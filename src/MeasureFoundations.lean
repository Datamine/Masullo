import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Integral.Regular
import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.MeasureTheory.Covering.DensityTheorem
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Topology.Algebra.ProperAction.CompactlyGenerated
import Mathlib.Topology.Covering.Quotient
import Mathlib.Topology.Metrizable.Urysohn
import Mathlib.MeasureTheory.Measure.Haar.Basic

open Set Filter MeasureTheory Topology

open scoped MeasureTheory
open scoped ENNReal

namespace Masullo

/-- Lemma 4.3.1.3. Haar measure on a second-countable locally compact
Hausdorff group is regular, inner regular, finite on compact sets and sigma-finite. -/
theorem haar_regular_radon_sigmaFinite {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (ν : Measure G) [ν.IsHaarMeasure] :
    ν.Regular ∧ ν.InnerRegular ∧ IsFiniteMeasureOnCompacts ν ∧ SigmaFinite ν :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

/-- A.5.1.3. Symmetric interval averages converge almost everywhere. -/
theorem lebesgue_differentiation_real {f : ℝ → ℂ} (hf : LocallyIntegrable f volume) :
    ∀ᵐ x ∂volume, Tendsto (fun r : ℝ =>
      (2 * r)⁻¹ • ∫ y in Icc (x - r) (x + r), f y) (𝓝[>] 0) (𝓝 (f x)) := by
  filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_average volume hf 1] with x hx
  have hmem : ∀ᶠ r : ℝ in 𝓝[>] 0, x ∈ Metric.closedBall x (1 * id r) := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    simpa using (Metric.mem_closedBall_self (mem_Ioi.mp hr).le (x := x))
  apply (hx _ id tendsto_id hmem).congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hr' : 0 < r := mem_Ioi.mp hr
  change (⨍ y in Metric.closedBall x r, f y) = _
  rw [Real.closedBall_eq_Icc, average_eq, measureReal_def, Measure.restrict_apply_univ,
    Real.volume_Icc]
  simp only [ENNReal.toReal_ofReal (by linarith : 0 ≤ x + r - (x - r))]
  ring_nf

/-- The difference between the average of the product and the average with
the multiplier evaluated at the center tends to zero. -/
theorem tendsto_average_mul_sub_const_mul
    {G : Type*} [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) {x : G} {U : ℕ → Set G} (hU : ∀ n, NullMeasurableSet (U n) μ)
    (hsmall : ∀ V ∈ 𝓝 x, ∀ᶠ n in atTop, U n ⊆ V)
    {f φ : G → ℂ} (hφ : Continuous φ) (hf : ∀ᶠ n in atTop, IntegrableOn f (U n) μ)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ᶠ n in atTop, (⨍ y in U n, ‖f y‖ ∂μ) ≤ C) :
    Tendsto (fun n => (⨍ y in U n, φ y * f y ∂μ) -
      φ x * (⨍ y in U n, f y ∂μ)) atTop (𝓝 0) := by
  let A (n : ℕ) := ⨍ y in U n, φ y * f y ∂μ
  let B (n : ℕ) := ⨍ y in U n, f y ∂μ
  change Tendsto (fun n => A n - φ x * B n) atTop (𝓝 0)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let δ := ε / (C + 1)
  have hδ : 0 < δ := div_pos hε (by linarith)
  have hsmall' := hsmall (φ ⁻¹' Metric.ball (φ x) δ)
    (hφ.continuousAt (Metric.ball_mem_nhds _ hδ))
  filter_upwards [hsmall', hf, hbound] with n hn hfn hbn
  let ν := μ.restrict (U n)
  have hnear : ∀ᵐ y ∂ν, ‖φ y - φ x‖ ≤ δ :=
    (ae_restrict_mem₀ (hU n)).mono fun y hy => (by
      simpa only [mem_preimage, Metric.mem_ball, dist_eq_norm] using hn hy : ‖φ y - φ x‖ < δ).le
  have hg : Integrable (fun y => (φ y - φ x) * f y) ν :=
    hfn.bdd_mul (hφ.measurable.sub measurable_const).aestronglyMeasurable hnear
  have hconst : Integrable (fun y => φ x * f y) ν := hfn.const_mul _
  have hprod : Integrable (fun y => φ y * f y) ν := by
    have heq : (fun y => (φ y - φ x) * f y) + (fun y => φ x * f y) =
        fun y => φ y * f y := by
      funext y
      simp only [Pi.add_apply, sub_mul, sub_add_cancel]
    exact heq ▸ hg.add hconst
  have he : A n - φ x * B n = (ν.real univ)⁻¹ •
      ∫ y, (φ y - φ x) * f y ∂ν := by
    simp only [A, B, average_eq, Complex.real_smul]
    simp only [sub_mul, integral_sub hprod hconst, integral_const_mul]
    dsimp [ν]
    ring
  have hle : ‖∫ y, (φ y - φ x) * f y ∂ν‖ ≤ δ * ∫ y, ‖f y‖ ∂ν := by
    rw [← integral_const_mul]
    exact norm_integral_le_of_norm_le (hfn.norm.const_mul _) (hnear.mono
      fun y hy => (norm_mul _ _).trans_le (mul_le_mul_of_nonneg_right hy (norm_nonneg _)))
  rw [dist_zero_right, he, norm_smul, Real.norm_of_nonneg (by positivity)]
  calc
    _ ≤ (ν.real univ)⁻¹ * (δ * ∫ y, ‖f y‖ ∂ν) :=
      mul_le_mul_of_nonneg_left hle (by positivity)
    _ = δ * (⨍ y in U n, ‖f y‖ ∂μ) := by rw [average_eq, smul_eq_mul]; ring
    _ ≤ δ * C := mul_le_mul_of_nonneg_left hbn hδ.le
    _ < ε := by
      change ε / (C + 1) * C < ε
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
      linarith

/-- Corrected A.5.4.3. At a point where the averages of `f` converge,
multiplication by a continuous function commutes with the limit when the
averages of `‖f‖` are eventually bounded. -/
theorem tendsto_average_mul_of_average_norm_bounded
    {G : Type*} [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) {x : G} {U : ℕ → Set G} (hU : ∀ n, NullMeasurableSet (U n) μ)
    (hsmall : ∀ V ∈ 𝓝 x, ∀ᶠ n in atTop, U n ⊆ V)
    {f φ : G → ℂ} (hφ : Continuous φ) (hf : ∀ᶠ n in atTop, IntegrableOn f (U n) μ)
    {a : ℂ} (ha : Tendsto (fun n => ⨍ y in U n, f y ∂μ) atTop (𝓝 a))
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ᶠ n in atTop, (⨍ y in U n, ‖f y‖ ∂μ) ≤ C) :
    Tendsto (fun n => ⨍ y in U n, φ y * f y ∂μ) atTop (𝓝 (φ x * a)) := by
  have hdiff := tendsto_average_mul_sub_const_mul μ hU hsmall hφ hf hC hbound
  have h := hdiff.add (tendsto_const_nhds.mul ha (f := fun _ : ℕ => φ x))
  simpa only [sub_add_cancel, zero_add] using h

/-- At a nonzero cutoff, convergence of the weighted means implies
convergence of the unweighted means under the absolute-mean bound. -/
theorem tendsto_average_of_tendsto_average_mul
    {G : Type*} [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) {x : G} {U : ℕ → Set G} (hU : ∀ n, NullMeasurableSet (U n) μ)
    (hsmall : ∀ V ∈ 𝓝 x, ∀ᶠ n in atTop, U n ⊆ V)
    {f φ : G → ℂ} (hφ : Continuous φ) (hφx : φ x ≠ 0)
    (hf : ∀ᶠ n in atTop, IntegrableOn f (U n) μ)
    {b : ℂ} (hb : Tendsto (fun n => ⨍ y in U n, φ y * f y ∂μ) atTop (𝓝 b))
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ᶠ n in atTop, (⨍ y in U n, ‖f y‖ ∂μ) ≤ C) :
    Tendsto (fun n => ⨍ y in U n, f y ∂μ) atTop (𝓝 ((φ x)⁻¹ * b)) := by
  have hdiff := tendsto_average_mul_sub_const_mul μ hU hsmall hφ hf hC hbound
  have hc := tendsto_const_nhds.mul (hb.sub hdiff) (f := fun _ : ℕ => (φ x)⁻¹)
  rw [sub_zero] at hc
  apply hc.congr
  intro n
  simp only [sub_sub_cancel, ← mul_assoc, inv_mul_cancel₀ hφx, one_mul]

/-- Theorem A.5.2.8 in the Borel measurable spaces of the two Polish spaces. -/
theorem borel_image_of_continuous_injOn {X Y : Type*}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (f : X → Y) (hf : Continuous f) (B : Set X) (hB : MeasurableSet B) (hinj : InjOn f B) :
    MeasurableSet (f '' B) :=
  hB.image_of_continuousOn_injOn hf.continuousOn hinj

/-- Extend a Borel partial section of a surjective local homeomorphism to a Borel transversal. -/
theorem borel_section_extend {X Y : Type*}
    [TopologicalSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] {f : X → Y}
    (hf : IsLocalHomeomorph f) (hsurj : Function.Surjective f)
    (E : Set X) (hE : MeasurableSet E) (hinj : InjOn f E) :
    ∃ B : Set X, MeasurableSet B ∧ E ⊆ B ∧ InjOn f B ∧ f '' B = univ := by
  classical
  by_cases hX : Nonempty X
  · letI := hX
    have hopen := hf.isOpenMap
    have hmeas := hf.continuous.measurable
    choose e he heq using hf
    have hcover : (univ : Set X) ⊆ ⋃ x, (e x).source := fun x _ => mem_iUnion.mpr ⟨x, he x⟩
    obtain ⟨k, hk⟩ := isLindelof_univ.indexed_countable_subcover _ (fun x => (e x).open_source) hcover
    let U (n : ℕ) := (e (k n)).source
    have hU (n : ℕ) : IsOpen (U n) := (e (k n)).open_source
    have hUcover (x : X) : ∃ n, x ∈ U n := mem_iUnion.mp (hk (mem_univ x))
    have hEmbed (n : ℕ) : IsOpenEmbedding ((U n).domRestrict f) :=
      heq (k n) ▸ (e (k n)).isOpenEmbedding_restrict
    have hEU (n : ℕ) : MeasurableSet (f '' (E ∩ U n)) := by
      have h := (hEmbed n).measurableEmbedding.measurableSet_image'
        (hE.preimage (measurable_subtype_coe : Measurable ((↑) : U n → X)))
      convert h using 1
      ext y
      constructor
      · rintro ⟨x, ⟨hx, hxU⟩, rfl⟩
        exact ⟨⟨x, hxU⟩, hx, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x, ⟨hx, x.property⟩, rfl⟩
    have hEI : MeasurableSet (f '' E) := by
      have heq : f '' E = ⋃ n, f '' (E ∩ U n) := by
        ext y
        constructor
        · rintro ⟨x, hx, rfl⟩
          obtain ⟨n, hn⟩ := hUcover x
          exact mem_iUnion.mpr ⟨n, x, ⟨hx, hn⟩, rfl⟩
        · intro hy
          obtain ⟨_, x, hx, rfl⟩ := mem_iUnion.mp hy
          exact ⟨x, hx.1, rfl⟩
      rw [heq]
      exact MeasurableSet.iUnion hEU
    let D (n : ℕ) := (f '' U n) \ ((f '' E) ∪ ⋃ j : {j : ℕ // j < n}, f '' U j)
    have hD (n : ℕ) : MeasurableSet (D n) :=
      (hopen _ (hU n)).measurableSet.diff
        (hEI.union (MeasurableSet.iUnion fun j => (hopen _ (hU j)).measurableSet))
    let B := E ∪ ⋃ n, U n ∩ f ⁻¹' D n
    refine ⟨B, hE.union (MeasurableSet.iUnion fun n => (hU n).measurableSet.inter
      ((hD n).preimage hmeas)), subset_union_left, ?_, ?_⟩
    · have hwithin (n : ℕ) {x y : X} (hx : x ∈ U n) (hy : y ∈ U n) (hxy : f x = f y) : x = y :=
        congrArg Subtype.val ((hEmbed n).injective (show (U n).domRestrict f ⟨x, hx⟩ =
          (U n).domRestrict f ⟨y, hy⟩ from hxy))
      have hout (n : ℕ) {x y : X} (he : x ∈ E) (hy : f y ∈ D n) (hxy : f x = f y) : False :=
        hy.2 (Or.inl ⟨x, he, hxy⟩)
      have hearlier {n m : ℕ} (hnm : n < m) {x y : X} (hx : x ∈ U n) (hy : f y ∈ D m)
          (hxy : f x = f y) : False :=
        hy.2 (Or.inr (mem_iUnion.mpr ⟨⟨n, hnm⟩, x, hx, hxy⟩))
      intro x hx y hy hxy
      rcases hx with hx | hx <;> rcases hy with hy | hy
      · exact hinj hx hy hxy
      · obtain ⟨n, _, hyD⟩ := mem_iUnion.mp hy
        exact (hout n hx hyD hxy).elim
      · obtain ⟨n, _, hxD⟩ := mem_iUnion.mp hx
        exact (hout n hy hxD hxy.symm).elim
      · obtain ⟨n, hxU, hxD⟩ := mem_iUnion.mp hx
        obtain ⟨m, hyU, hyD⟩ := mem_iUnion.mp hy
        rcases lt_trichotomy n m with hlt | rfl | hgt
        · exact (hearlier hlt hxU hyD hxy).elim
        · exact hwithin n hxU hyU hxy
        · exact (hearlier hgt hyU hxD hxy.symm).elim
    · apply eq_univ_of_forall
      intro y
      by_cases hy : y ∈ f '' E
      · exact image_mono subset_union_left hy
      · obtain ⟨x, rfl⟩ := hsurj y
        have hall : ∃ n, f x ∈ f '' U n := by
          obtain ⟨n, hn⟩ := hUcover x
          exact ⟨n, x, hn, rfl⟩
        obtain ⟨z, hz, hzx⟩ := Nat.find_spec hall
        refine ⟨z, Or.inr (mem_iUnion.mpr ⟨Nat.find hall, hz, ?_⟩), hzx⟩
        change f z ∈ D (Nat.find hall)
        rw [hzx]
        refine ⟨Nat.find_spec hall, ?_⟩
        rintro (hy' | hy')
        · exact hy hy'
        · obtain ⟨j, hj⟩ := mem_iUnion.mp hy'
          exact (Nat.not_lt_of_ge (Nat.find_min' hall hj)) j.property
  · refine ⟨E, hE, subset_rfl, hinj, eq_univ_of_forall fun y => ?_⟩
    obtain ⟨x, _⟩ := hsurj y
    exact (hX ⟨x⟩).elim

/-- Lemma A.5.2.10. A partial Borel transversal for a free proper discrete
action extends to a Borel transversal for the orbit quotient. -/
theorem borel_orbit_transversal_extend {G X : Type*} [Group G] [TopologicalSpace G]
    [DiscreteTopology G] [MulAction G X] [IsCancelSMul G X]
    [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
    [ContinuousConstSMul G X] [ProperSMul G X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableSpace (MulAction.orbitRel.Quotient G X)] [BorelSpace (MulAction.orbitRel.Quotient G X)]
    (E : Set X) (hE : MeasurableSet E) (hinj : InjOn (Quotient.mk (MulAction.orbitRel G X)) E) :
    ∃ B : Set X, MeasurableSet B ∧ E ⊆ B ∧ InjOn (Quotient.mk (MulAction.orbitRel G X)) B ∧
      Quotient.mk (MulAction.orbitRel G X) '' B = univ := by
  letI : ProperlyDiscontinuousSMul G X := properlyDiscontinuousSMul_iff_properSMul.mpr inferInstance
  exact borel_section_extend
    (isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul (G := G) (E := X)).isCoveringMap.isLocalHomeomorph
    Quotient.mk_surjective E hE hinj

/-- Lemma A.5.3.3. Local nullity in a second-countable space implies nullity
and measurability for the completed measure. -/
theorem nullMeasurableSet_of_locally_null {X : Type*} [TopologicalSpace X]
    [SecondCountableTopology X] [MeasurableSpace X] (μ : Measure X) (A : Set X)
    (h : ∀ x : X, ∃ U ∈ 𝓝 x, μ (A ∩ U) = 0) :
    μ A = 0 ∧ NullMeasurableSet A μ := by
  have hnull : μ A = 0 := measure_null_of_locally_null A fun x _ => by
    obtain ⟨U, hU, hU₀⟩ := h x
    exact ⟨A ∩ U, inter_mem (self_mem_nhdsWithin) (mem_nhdsWithin_of_mem_nhds hU), hU₀⟩
  exact ⟨hnull, NullMeasurableSet.of_null hnull⟩

/-- A set with null frontier has continuous envelopes with arbitrarily small integral gap. -/
theorem continuous_nullFrontier_envelopes {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [T2Space X] [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [μ.Regular]
    (U : Set X) (hfrontier : μ (frontier U) = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ f g : C(X, ℝ), (∀ x, f x ∈ Icc 0 1) ∧ (∀ x, g x ∈ Icc 0 1) ∧
      (∀ x, f x ≤ U.indicator 1 x ∧ U.indicator 1 x ≤ g x) ∧
      (∫ x, g x - f x ∂μ) < ε := by
  classical
  have hε₂ : ENNReal.ofReal (ε / 2) ≠ 0 := (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  obtain ⟨K, hKU, hK, hsmallK⟩ :=
    isOpen_interior.measurableSet.exists_isCompact_sdiff_lt (μ := μ) (by simp) hε₂
  obtain ⟨W, hUW, hW, _, hsmallW⟩ :=
    (isClosed_closure (s := U)).measurableSet.exists_isOpen_sdiff_lt (μ := μ) (by simp) hε₂
  obtain ⟨f, hfout, hfK, hfrange⟩ := exists_continuous_zero_one_of_isClosed
    isOpen_interior.isClosed_compl hK.isClosed (disjoint_compl_left_iff_subset.mpr hKU)
  obtain ⟨g, hgfout, hgU, hgrange⟩ := exists_continuous_zero_one_of_isClosed
    hW.isClosed_compl isClosed_closure (disjoint_compl_left_iff_subset.mpr hUW)
  refine ⟨f, g, hfrange, hgrange, ?_, ?_⟩
  · intro x
    by_cases hx : x ∈ U
    · rw [indicator_of_mem hx, hgU (subset_closure hx)]
      exact ⟨(hfrange x).2, le_rfl⟩
    · rw [indicator_of_notMem hx, hfout (fun h => hx (interior_subset h))]
      exact ⟨le_rfl, (hgrange x).1⟩
  let S := W \ K
  have hS : MeasurableSet S := hW.measurableSet.diff hK.measurableSet
  have hsub : S ⊆ (W \ closure U) ∪ frontier U ∪ (interior U \ K) := by
    intro x hx
    by_cases hc : x ∈ closure U
    · by_cases hu : x ∈ interior U
      · exact Or.inr ⟨hu, hx.2⟩
      · exact Or.inl (Or.inr ⟨hc, hu⟩)
    · exact Or.inl (Or.inl ⟨hx.1, hc⟩)
  have hμ : μ S ≤ μ (W \ closure U) + μ (interior U \ K) := by
    calc
      μ S ≤ μ ((W \ closure U) ∪ frontier U ∪ (interior U \ K)) := measure_mono hsub
      _ ≤ (μ (W \ closure U) + μ (frontier U)) + μ (interior U \ K) :=
        (measure_union_le _ _).trans (add_le_add_left (measure_union_le _ _) _)
      _ = _ := by rw [hfrontier, add_zero]
  have hb (x : X) : g x - f x ≤ S.indicator 1 x := by
    by_cases hx : x ∈ S
    · rw [indicator_of_mem hx, Pi.one_apply]
      linarith [(hgrange x).2, (hfrange x).1]
    · rw [indicator_of_notMem hx]
      by_cases hxK : x ∈ K
      · rw [hfK hxK, Pi.one_apply]
        linarith [(hgrange x).2]
      · rw [hgfout (fun hxW => hx ⟨hxW, hxK⟩), Pi.zero_apply]
        linarith [(hfrange x).1]
  have hgint : Integrable g μ :=
    g.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace g)
  have hfint : Integrable f μ :=
    f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)
  calc
    (∫ x, g x - f x ∂μ) ≤ ∫ x, S.indicator (fun _ => (1 : ℝ)) x ∂μ :=
      integral_mono (hgint.sub hfint) ((integrable_const (1 : ℝ)).indicator hS) hb
    _ = (μ S).toReal := integral_indicator_one hS
    _ < ε := by
      have hk' := (ENNReal.toReal_lt_toReal (measure_ne_top μ _) ENNReal.ofReal_ne_top).mpr hsmallK
      have hw' := (ENNReal.toReal_lt_toReal (measure_ne_top μ _) ENNReal.ofReal_ne_top).mpr hsmallW
      rw [ENNReal.toReal_ofReal (by positivity)] at hk' hw'
      have hmono := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨by simp, by simp⟩) hμ
      rw [ENNReal.toReal_add (by simp) (by simp)] at hmono
      linarith

/-- Lemma B.5.2.2. A Borel continuity set has continuous upper and lower
approximants with arbitrarily small integral gap. -/
theorem continuous_indicator_envelopes {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [T2Space X] [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [μ.Regular]
    (U : Set X) (_hU : IsOpen U) (hfrontier : μ (frontier U) = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ f g : C(X, ℝ), (∀ x, f x ∈ Icc 0 1) ∧ (∀ x, g x ∈ Icc 0 1) ∧
      (∀ x, f x ≤ U.indicator 1 x ∧ U.indicator 1 x ≤ g x) ∧
      (∫ x, g x - f x ∂μ) < ε :=
  continuous_nullFrontier_envelopes μ U hfrontier hε

end Masullo
