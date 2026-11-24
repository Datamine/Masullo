import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.Positive

open Filter MeasureTheory
open scoped ENNReal

namespace Masullo

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {r : X → ℂ} {C : ℝ}

theorem memLp_bounded_complex_mul {f : X → ℂ}
    (hr : AEStronglyMeasurable r μ) (hC : ∀ᵐ x ∂μ, ‖r x‖ ≤ C)
    (hf : MemLp f 2 μ) : MemLp (fun x => r x * f x) 2 μ := by
  have hnorm : MemLp (fun x => C * ‖f x‖) 2 μ := hf.norm.const_mul C
  refine hnorm.mono' (hr.mul hf.aestronglyMeasurable) ?_
  filter_upwards [hC] with x hx
  exact (norm_mul _ _).trans_le (mul_le_mul_of_nonneg_right hx (norm_nonneg _))

private noncomputable def lpTwoMultiplierFun (hr : AEStronglyMeasurable r μ) (hC : ∀ᵐ x ∂μ, ‖r x‖ ≤ C)
    (f : Lp ℂ 2 μ) : Lp ℂ 2 μ := (memLp_bounded_complex_mul hr hC (Lp.memLp f)).toLp _

private theorem lpTwoMultiplierFun_ae (hr : AEStronglyMeasurable r μ) (hC : ∀ᵐ x ∂μ, ‖r x‖ ≤ C) (f : Lp ℂ 2 μ) :
    (lpTwoMultiplierFun hr hC f : X → ℂ) =ᵐ[μ] fun x => r x * f x :=
  (memLp_bounded_complex_mul hr hC (Lp.memLp f)).coeFn_toLp

private theorem lpTwoMultiplierFun_norm_le (hr : AEStronglyMeasurable r μ) (hC : ∀ᵐ x ∂μ, ‖r x‖ ≤ C) (f : Lp ℂ 2 μ) :
    ‖lpTwoMultiplierFun hr hC f‖ ≤ C * ‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [lpTwoMultiplierFun_ae hr hC f, hC] with x hx hbound
  rw [hx, norm_mul]
  exact mul_le_mul_of_nonneg_right hbound (norm_nonneg _)

/-- Bounded measurable multiplication on complex L². -/
noncomputable def lpTwoComplexMultiplier (hr : AEStronglyMeasurable r μ) (hC : ∀ᵐ x ∂μ, ‖r x‖ ≤ C) :
    Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  let M := lpTwoMultiplierFun hr hC
  let T : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ :=
    { toFun := M
      map_add' := fun f g => Lp.ext (by
        filter_upwards [lpTwoMultiplierFun_ae hr hC (f + g), lpTwoMultiplierFun_ae hr hC f,
          lpTwoMultiplierFun_ae hr hC g, Lp.coeFn_add f g, Lp.coeFn_add (M f) (M g)]
          with x h₀ h₁ h₂ h₃ h₄
        change M (f + g) x = (M f + M g) x
        simp only [Pi.add_apply] at h₃ h₄
        rw [h₀, h₃, h₄, h₁, h₂, mul_add])
      map_smul' := fun c f => Lp.ext (by
        filter_upwards [lpTwoMultiplierFun_ae hr hC (c • f), lpTwoMultiplierFun_ae hr hC f,
          Lp.coeFn_smul c f, Lp.coeFn_smul c (M f)] with x h₀ h₁ h₂ h₃
        change M (c • f) x = (c • M f) x
        simp only [Pi.smul_apply, smul_eq_mul] at h₂ h₃
        rw [h₀, h₂, h₃, h₁]
        ring) }
  T.mkContinuous C (lpTwoMultiplierFun_norm_le hr hC)

theorem lpTwoComplexMultiplier_ae (hr : AEStronglyMeasurable r μ) (hC : ∀ᵐ x ∂μ, ‖r x‖ ≤ C) (f : Lp ℂ 2 μ) :
    (lpTwoComplexMultiplier hr hC f : X → ℂ) =ᵐ[μ] fun x => r x * f x :=
  lpTwoMultiplierFun_ae hr hC f

theorem lpTwoComplexMultiplier_norm_le (hr : AEStronglyMeasurable r μ) (hC : ∀ᵐ x ∂μ, ‖r x‖ ≤ C) (hC₀ : 0 ≤ C) :
    ‖lpTwoComplexMultiplier (μ := μ) hr hC‖ ≤ C :=
  ContinuousLinearMap.opNorm_le_bound _ hC₀ (lpTwoMultiplierFun_norm_le hr hC)

/-- Multiplication by an L∞ function uses its essential norm as a bound. -/
theorem ae_norm_le_essentialNorm (hr : MemLp r ⊤ μ) :
    ∀ᵐ x ∂μ, ‖r x‖ ≤ (eLpNorm r ⊤ μ).toReal := by
  filter_upwards [ae_le_eLpNormEssSup (f := r) (μ := μ)] with x hx
  rw [← eLpNorm_exponent_top] at hx
  simpa only [toReal_enorm] using ENNReal.toReal_mono hr.eLpNorm_lt_top.ne hx

/-- The measurable cutoff in Theorem 9.2.1.2(1). Multiplication by the
indicator gives a continuous projection onto its closed fixed-point space.
The specification follows original commit d99ce37 (Apache-2.0) and uses the
existing bounded multiplier construction. -/
theorem lpTwo_measurableCutoff {U : Set X} (hU : MeasurableSet U) :
    ∃ P : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ, IsClosed (Set.range P) ∧ ‖P‖ ≤ 1 ∧
      ∀ f, P (P f) = P f ∧ (P f : X → ℂ) =ᵐ[μ] U.indicator (f : X → ℂ) := by
  let r : X → ℂ := U.indicator (fun _ => 1)
  have hr : AEStronglyMeasurable r μ :=
    (measurable_const.indicator hU).aestronglyMeasurable
  have hb : ∀ᵐ x ∂μ, ‖r x‖ ≤ 1 := .of_forall fun x => by
    by_cases hx : x ∈ U <;> simp [r, hx]
  let P := lpTwoComplexMultiplier hr hb
  have hP (f : Lp ℂ 2 μ) : (P f : X → ℂ) =ᵐ[μ] U.indicator (f : X → ℂ) := by
    filter_upwards [lpTwoComplexMultiplier_ae hr hb f] with x hx
    rw [hx]
    by_cases h : x ∈ U <;> simp [r, h]
  have hidem (f : Lp ℂ 2 μ) : P (P f) = P f := by
    apply Lp.ext
    filter_upwards [hP (P f), hP f] with x h₁ h₂
    rw [h₁]
    by_cases hx : x ∈ U <;> simp [hx, h₂]
  refine ⟨P, ?_, lpTwoComplexMultiplier_norm_le hr hb zero_le_one,
    fun f => ⟨hidem f, hP f⟩⟩
  have he : Set.range P = {f | P f = f} := by
    ext f
    exact ⟨fun ⟨g, hg⟩ => hg ▸ hidem g, fun h => ⟨f, h⟩⟩
  rw [he]
  exact isClosed_eq P.continuous continuous_id

/-- Corrected Remark 9.3.3.4. The indicator of a measurable band gives a
positive orthogonal projection for every weighted L² measure. The symmetry
argument is adapted from original commit 469ebeb (Apache-2.0). -/
theorem lpTwo_cutoff_isStarProjection {U : Set X} (hU : MeasurableSet U) :
    ∃ P : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ,
      IsStarProjection P ∧ P.IsPositive ∧ IsClosed (Set.range P) ∧ ‖P‖ ≤ 1 ∧
      (∀ f, (P f : X → ℂ) =ᵐ[μ] U.indicator (f : X → ℂ)) ∧
      (P ≠ 0 → ‖P‖ = 1) ∧
      (μ Uᶜ = 0 → Function.Injective P) := by
  obtain ⟨P, hclosed, hnorm, hP⟩ := lpTwo_measurableCutoff (μ := μ) hU
  have hself : IsSelfAdjoint P := by
    apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.2
    intro u v
    rw [ContinuousLinearMap.coe_coe, L2.inner_def, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(hP u).2, (hP v).2] with x hu hv
    rw [hu, hv]
    by_cases hx : x ∈ U <;> simp [hx]
  have hproj : IsStarProjection P := ⟨ContinuousLinearMap.ext fun u => (hP u).1, hself⟩
  refine ⟨P, hproj, .of_isStarProjection hproj, hclosed, hnorm, fun f => (hP f).2, ?_, ?_⟩
  · intro hne
    have hex : ∃ f, P f ≠ 0 := by
      by_contra! hzero
      exact hne (ContinuousLinearMap.ext hzero)
    obtain ⟨f, hf⟩ := hex
    have hbound := P.le_opNorm (P f)
    rw [(hP f).1] at hbound
    exact le_antisymm hnorm ((le_mul_iff_one_le_left (norm_pos_iff.mpr hf)).mp hbound)
  · intro hnull u v huv
    have hUae : ∀ᵐ x ∂μ, x ∈ U := ae_iff.mpr hnull
    have hfix (f : Lp ℂ 2 μ) : P f = f := Lp.ext (by
      filter_upwards [hUae, (hP f).2] with x hx hf
      simpa only [Set.indicator_of_mem hx] using hf)
    simpa only [hfix] using huv

/-- A band cutoff annihilates any test supported outside the band. -/
theorem lpTwo_cutoff_eq_zero_of_supported_compl {U : Set X}
    {P : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ}
    (hP : ∀ f, (P f : X → ℂ) =ᵐ[μ] U.indicator (f : X → ℂ))
    {f : Lp ℂ 2 μ} (hf : ∀ᵐ x ∂μ, x ∈ U → f x = 0) : P f = 0 := by
  apply Lp.ext
  filter_upwards [hP f, hf, Lp.coeFn_zero ℂ 2 μ] with x hx hzero hz
  rw [hx, hz]
  by_cases h : x ∈ U <;> simp [h, hzero]

/-- An omitted measurable part of finite positive measure prevents injectivity. -/
theorem lpTwo_cutoff_not_injective {U V : Set X} (hV : MeasurableSet V)
    (hVU : V ⊆ Uᶜ) (hV₀ : μ V ≠ 0) (hVfin : μ V ≠ ∞)
    {P : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ}
    (hP : ∀ f, (P f : X → ℂ) =ᵐ[μ] U.indicator (f : X → ℂ)) : ¬ Function.Injective P := by
  let g : X → ℂ := V.indicator (fun _ => 1)
  let hg : MemLp g 2 μ := memLp_indicator_const _ hV _ (.inr hVfin)
  let f := hg.toLp g
  have hf : (f : X → ℂ) =ᵐ[μ] g := hg.coeFn_toLp
  have hPf : P f = 0 := lpTwo_cutoff_eq_zero_of_supported_compl hP (by
    filter_upwards [hf] with x hx hxU
    rw [hx]
    exact Set.indicator_of_notMem (fun hxV => hVU hxV hxU) _)
  intro h
  have he : f = 0 := h (hPf.trans P.map_zero.symm)
  have hzero : ∀ᵐ x ∂μ, x ∉ V := by
    filter_upwards [hf, Lp.coeFn_zero ℂ 2 μ] with x hx hz hxV
    have hxg : g x = 1 := Set.indicator_of_mem hxV _
    rw [he, hz, hxg] at hx
    exact zero_ne_one hx
  apply hV₀
  simpa using ae_iff.mp hzero

open Function Set in
/-- The supported L² row of Theorem 9.2.1.2(3) splits at logarithmic
coordinate zero, provided that the splitting level is null. The proof adapts
Apache-2.0 original commit 9433f29 and uses the local indicator projection. -/
theorem lpTwo_cutoff_exact {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (x : A → ℝ) (hx : Measurable x) (c : ℝ) (hc : c ≤ 0)
    (hzero : μ (x ⁻¹' {0}) = 0) :
    let E := Lp ℂ 2 μ
    let S := fun (U : Set ℝ) ↦ {f : E | (f : A → ℂ) =ᵐ[μ] (x ⁻¹' U).indicator (f : A → ℂ)}
    ∃ (L M R : Submodule ℂ E) (i : L →L[ℂ] M) (p : M →L[ℂ] R),
      (L : Set E) = S (Icc c 0) ∧ (M : Set E) = S (Ici c) ∧ (R : Set E) = S (Ici 0) ∧
      (∀ f, (i f).val = f.val) ∧
      (∀ f, ((p f).val : A → ℂ) =ᵐ[μ] (x ⁻¹' Ici 0).indicator (f.val : A → ℂ)) ∧
      Injective i ∧ IsClosed (range i) ∧ Exact i p ∧ Surjective p ∧ IsOpenMap p := by
  intro E S
  have supportedSubmodule (U : Set ℝ) (hU : MeasurableSet U) :
      ∃ K : Submodule ℂ (Lp ℂ 2 μ), IsClosed (K : Set (Lp ℂ 2 μ)) ∧
        ∀ f : Lp ℂ 2 μ, f ∈ K ↔ (f : A → ℂ) =ᵐ[μ] (x ⁻¹' U).indicator (f : A → ℂ) := by
    obtain ⟨P, -, -, hP⟩ := lpTwo_measurableCutoff (μ := μ) (hx hU)
    refine ⟨LinearMap.eqLocus (P : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ) LinearMap.id, ?_,
      fun f ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩⟩
    · exact isClosed_eq P.continuous continuous_id
    · have h' : P f = f := h
      have h2 := (hP f).2
      rw [h'] at h2
      exact h2
    · exact Lp.ext ((hP f).2.trans h.symm)
  obtain ⟨L, hLc, hL⟩ := supportedSubmodule (Icc c 0) measurableSet_Icc
  obtain ⟨M, -, hM⟩ := supportedSubmodule (Ici c) measurableSet_Ici
  obtain ⟨R, -, hR⟩ := supportedSubmodule (Ici 0) measurableSet_Ici
  obtain ⟨P, -, -, hP⟩ := lpTwo_measurableCutoff (μ := μ) (hx (measurableSet_Ici (a := (0 : ℝ))))
  have hnull : ∀ᵐ a ∂μ, a ∉ x ⁻¹' {0} := measure_eq_zero_iff_ae_notMem.1 hzero
  have hLM : ∀ f : L, f.val ∈ M := by
    intro f
    refine (hM _).2 ?_
    filter_upwards [(hL f.val).1 f.2] with a ha
    by_cases h : a ∈ x ⁻¹' Ici c
    · exact (Set.indicator_of_mem h _).symm
    · have h2 : a ∉ x ⁻¹' Icc c 0 := fun h' ↦ h (show c ≤ x a ∧ x a ≤ 0 from h').1
      exact ha.trans ((Set.indicator_of_notMem h2 _).trans (Set.indicator_of_notMem h _).symm)
  have hRM : ∀ r : R, r.val ∈ M := by
    intro r
    refine (hM _).2 ?_
    filter_upwards [(hR r.val).1 r.2] with a ha
    by_cases h : a ∈ x ⁻¹' Ici c
    · exact (Set.indicator_of_mem h _).symm
    · have h2 : a ∉ x ⁻¹' Ici 0 := fun h' ↦ h (hc.trans (show 0 ≤ x a from h'))
      exact ha.trans ((Set.indicator_of_notMem h2 _).trans (Set.indicator_of_notMem h _).symm)
  have hPR : ∀ f : M, P f.val ∈ R := by
    intro f
    refine (hR _).2 ?_
    have h1 := (hP (P f.val)).2
    rw [(hP f.val).1] at h1
    exact h1
  obtain ⟨i, hi⟩ : ∃ i : L →L[ℂ] M, ∀ f, (i f).val = f.val :=
    ⟨L.subtypeL.codRestrict M hLM, fun _ ↦ rfl⟩
  obtain ⟨p, hp⟩ : ∃ p : M →L[ℂ] R, ∀ f, (p f).val = P f.val :=
    ⟨(P.comp M.subtypeL).codRestrict R hPR, fun _ ↦ rfl⟩
  obtain ⟨j, hj⟩ : ∃ j : R →L[ℂ] M, ∀ r, (j r).val = r.val :=
    ⟨R.subtypeL.codRestrict M hRM, fun _ ↦ rfl⟩
  have hpj : ∀ r : R, p (j r) = r := fun r ↦ Subtype.ext ((hp _).trans
    ((congrArg (fun g ↦ P g) (hj r)).trans
      (Lp.ext ((hP r.val).2.trans ((hR r.val).1 r.2).symm))))
  have hinj : Injective i := fun f g h ↦
    Subtype.ext ((hi f).symm.trans ((congrArg (fun m : M ↦ (m : Lp ℂ 2 μ)) h).trans (hi g)))
  have hrange : IsClosed (range i) := by
    have hr : range i = (fun m : M ↦ (m : Lp ℂ 2 μ)) ⁻¹' (L : Set (Lp ℂ 2 μ)) := by
      ext m
      constructor
      · rintro ⟨f, rfl⟩
        have h1 : (i f).val ∈ L := by
          rw [hi]
          exact f.2
        exact h1
      · intro h
        exact ⟨⟨m.val, h⟩, Subtype.ext (hi _)⟩
    rw [hr]
    exact hLc.preimage continuous_subtype_val
  have hexact : Exact i p := by
    intro y
    constructor
    · intro h0
      have h0' : P y.val = 0 := (hp y).symm.trans (congrArg (fun r : R ↦ (r : Lp ℂ 2 μ)) h0)
      have hz : ((P y.val : Lp ℂ 2 μ) : A → ℂ) =ᵐ[μ] 0 := by
        rw [h0']
        exact Lp.coeFn_zero ℂ 2 μ
      have hyL : y.val ∈ L := by
        refine (hL _).2 ?_
        filter_upwards [(hM y.val).1 y.2, (hP y.val).2, hz] with a h1 h2 h3
        by_cases ha : a ∈ x ⁻¹' Icc c 0
        · exact (Set.indicator_of_mem ha _).symm
        · refine Eq.trans ?_ (Set.indicator_of_notMem ha _).symm
          by_cases hc' : a ∈ x ⁻¹' Ici c
          · have h0a : 0 ≤ x a := (le_total 0 (x a)).resolve_right
              fun hle ↦ ha (show x a ∈ Icc c 0 from ⟨hc', hle⟩)
            exact (Set.indicator_of_mem (show a ∈ x ⁻¹' Ici 0 from h0a) _).symm.trans
              (h2.symm.trans h3)
          · exact h1.trans (Set.indicator_of_notMem hc' _)
      exact ⟨⟨y.val, hyL⟩, Subtype.ext (hi _)⟩
    · rintro ⟨f, rfl⟩
      have hPf0 : P f.val = 0 := by
        refine Lp.ext ?_
        filter_upwards [(hL f.val).1 f.2, (hP f.val).2, hnull, Lp.coeFn_zero ℂ 2 μ]
          with a h1 h2 h3 h4
        refine h2.trans (Eq.trans ?_ h4.symm)
        by_cases ha : a ∈ x ⁻¹' Ici 0
        · have ha' : a ∉ x ⁻¹' Icc c 0 := fun h ↦
            h3 (show x a = 0 from le_antisymm (show c ≤ x a ∧ x a ≤ 0 from h).2 ha)
          exact (Set.indicator_of_mem ha _).trans (h1.trans (Set.indicator_of_notMem ha' _))
        · exact Set.indicator_of_notMem ha _
      exact Subtype.ext ((hp _).trans ((congrArg (fun g ↦ P g) (hi f)).trans hPf0))
  have hopen : IsOpenMap p := by
    refine IsOpenMap.of_sections fun m ↦ ⟨fun r ↦ m + j (r - p m), ?_, ?_, fun r ↦ ?_⟩
    · have hcontinuous : Continuous fun r : R ↦ m + j (r - p m) :=
        continuous_const.add (j.continuous.comp (continuous_id.sub continuous_const))
      exact hcontinuous.continuousAt
    · show m + j (p m - p m) = m
      rw [sub_self, map_zero, add_zero]
    · show p (m + j (r - p m)) = r
      rw [map_add, hpj, add_sub_cancel]
  exact ⟨L, M, R, i, p, Set.ext hL, Set.ext hM, Set.ext hR, hi,
    fun f ↦ (hp f).symm ▸ (hP f.val).2, hinj, hrange, hexact, fun r ↦ ⟨j r, hpj r⟩, hopen⟩

open Set Function in
/-- The support cutoff row inside a fixed admissible radial region. -/
theorem lpTwo_cutoff_exact_relative {G : Type*} [MeasurableSpace G] (W : Measure G)
    (radial : G → ℝ) (hm : Measurable radial) (c : ℝ) (hc : c ≤ 0)
    (hn : ∀ᵐ g ∂W, radial g ≠ 0)
    (R : Set ℝ) (hR : MeasurableSet R) :
    let E := Lp ℂ 2 W
    let S := fun (U : Set ℝ) =>
      {f : E | (f : G → ℂ) =ᵐ[W] (radial ⁻¹' (U ∩ R)).indicator (f : G → ℂ)}
    ∃ (L M Q : Submodule ℂ E) (i : L →L[ℂ] M) (p : M →L[ℂ] Q),
      (L : Set E) = S (Icc c 0) ∧ (M : Set E) = S (Ici c) ∧ (Q : Set E) = S (Ici 0) ∧
      (∀ f, (i f).val = f.val) ∧
      (∀ f, ((p f).val : G → ℂ) =ᵐ[W]
        (radial ⁻¹' (Ici 0 ∩ R)).indicator (f.val : G → ℂ)) ∧
      Injective i ∧ IsClosed (range i) ∧ Exact i p ∧ Surjective p ∧ IsOpenMap p := by
  classical
  let x (g : G) : ℝ := if radial g ∈ R then radial g else c - 1
  have hx : Measurable x := hm.ite (hm hR) measurable_const
  have hpre {U : Set ℝ} (hU : U ⊆ Ici c) :
      x ⁻¹' U = radial ⁻¹' (U ∩ R) := by
    ext g
    change x g ∈ U ↔ radial g ∈ U ∩ R
    by_cases hg : radial g ∈ R
    · simp [x, hg]
    · have hn : c - 1 ∉ U := fun h => (not_le_of_gt (by linarith : c - 1 < c)) (hU h)
      simp [x, hg, hn]
  have h0 : ({0} : Set ℝ) ⊆ Ici c := by
    intro z hz
    change c ≤ z
    rwa [mem_singleton_iff.mp hz]
  have hzero : W (x ⁻¹' {0}) = 0 := by
    rw [hpre h0]
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [hn] with g hg
    exact fun h => hg (mem_singleton_iff.mp h.1)
  have hL : Icc c 0 ⊆ Ici c := fun _ hg => hg.1
  have hM : Ici (0 : ℝ) ⊆ Ici c := Ici_subset_Ici.mpr hc
  simpa only [hpre hL, hpre (Subset.refl (Ici c)), hpre hM] using
    lpTwo_cutoff_exact W x hx c hc hzero


end Masullo
