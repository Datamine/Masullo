import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Measure.Haar.Quotient
import Mathlib.Topology.Covering.Quotient

open Set Filter Topology MeasureTheory
open scoped Pointwise ENNReal

namespace Masullo

private theorem localHomeomorph_measurableSet_image
    {X Y : Type*} [Nonempty X] [TopologicalSpace X] [TopologicalSpace Y] [SecondCountableTopology X]
    [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]
    {p : X → Y} (hp : IsLocalHomeomorph p) {A : Set X} (hA : MeasurableSet A) :
    MeasurableSet (p '' A) := by
  classical
  choose e he heq using hp
  have hcover : (univ : Set X) ⊆ ⋃ x, (e x).source :=
    fun x _ => mem_iUnion.mpr ⟨x, he x⟩
  obtain ⟨J, hJ⟩ := isLindelof_univ.indexed_countable_subcover _
    (fun x => (e x).open_source) hcover
  have hsplit : p '' A = ⋃ n, p '' (A ∩ (e (J n)).source) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨n, hn⟩ := mem_iUnion.mp (hJ (mem_univ x))
      exact mem_iUnion.mpr ⟨n, x, ⟨hx, hn⟩, rfl⟩
    · intro hy
      obtain ⟨_, x, hx, rfl⟩ := mem_iUnion.mp hy
      exact ⟨x, hx.1, rfl⟩
  rw [hsplit]
  apply MeasurableSet.iUnion
  intro n
  let U := (e (J n)).source
  have hE : IsOpenEmbedding (U.domRestrict p) :=
    heq (J n) ▸ (e (J n)).isOpenEmbedding_restrict
  have hm := hE.measurableEmbedding.measurableSet_image'
    (hA.preimage (measurable_subtype_coe : Measurable ((↑) : U → X)))
  convert hm using 1
  ext y
  constructor
  · rintro ⟨x, ⟨hx, hxU⟩, rfl⟩
    exact ⟨⟨x, hxU⟩, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, ⟨hx, x.property⟩, rfl⟩

section

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  (H : Subgroup G) [MeasurableSpace (G ⧸ H)] [BorelSpace (G ⧸ H)]

local notation "π" => @QuotientGroup.mk G _ H

private theorem quotient_transversal_embedding
    (hd : IsDiscrete (H : Set G)) {Δ : Set G}
    (hΔ : MeasurableSet Δ) (hb : BijOn π Δ univ) :
    MeasurableEmbedding (Δ.domRestrict π) where
  injective := hb.injOn.injective
  measurable := QuotientGroup.continuous_mk.measurable.comp measurable_subtype_coe
  measurableSet_image' s hs := by
    have he : (Δ.domRestrict π) '' s = π '' (Subtype.val '' s) :=
      (image_image π (Subtype.val : Δ → G) s).symm
    rw [he]
    exact localHomeomorph_measurableSet_image (H.isQuotientCoveringMap hd).isCoveringMap.isLocalHomeomorph
      ((MeasurableEmbedding.subtype_coe hΔ).measurableSet_image' hs)

omit [BorelSpace G] [SecondCountableTopology G] [MeasurableSpace (G ⧸ H)]
  [BorelSpace (G ⧸ H)] in
private theorem fundamentalDomain_of_bijective_quotient
    (hd : IsDiscrete (H : Set G)) (μ : Measure G) {Δ : Set G}
    (hΔ : MeasurableSet Δ) (hb : BijOn π Δ univ) :
    IsFundamentalDomain H.op Δ μ := by
  apply IsFundamentalDomain.mk' hΔ.nullMeasurableSet
  intro x
  obtain ⟨y, hy, he⟩ := hb.surjOn (mem_univ (π x))
  let hcover := H.isQuotientCoveringMap hd
  obtain ⟨g, rfl⟩ := hcover.apply_eq_iff_mem_orbit.mp he
  refine ⟨g, hy, fun k hk => ?_⟩
  have hkg : k • x = g • x := hb.injOn hk hy (hcover.map_smul k |>.trans (hcover.map_smul g).symm)
  exact hcover.isCancelSMul.right_cancel' k g x hkg

omit [MeasurableSpace (G ⧸ H)] [BorelSpace (G ⧸ H)] in
/-- D.1.2.5. Every Borel transversal gives the same restricted integral
of a function invariant along the subgroup cosets. -/
theorem integral_eq_on_quotient_transversals
    (hd : IsDiscrete (H : Set G)) (μ : Measure G) [μ.IsMulRightInvariant]
    {Δ Δ' : Set G} (hΔ : MeasurableSet Δ) (hΔ' : MeasurableSet Δ')
    (hb : BijOn π Δ univ) (hb' : BijOn π Δ' univ)
    {f : G → ℂ} (hf : ∀ (h : H) (g : G), f (g * h) = f g)
    (hi : IntegrableOn f Δ μ) :
    IntegrableOn f Δ' μ ∧ ∫ x in Δ, f x ∂μ = ∫ x in Δ', f x ∂μ := by
  haveI : DiscreteTopology H := isDiscrete_iff_discreteTopology.mp hd
  haveI : Countable H := countable_of_Lindelof_of_discrete
  haveI : Countable H.op := inferInstance
  have h₁ := fundamentalDomain_of_bijective_quotient H hd μ hΔ hb
  have h₂ := fundamentalDomain_of_bijective_quotient H hd μ hΔ' hb'
  have he (h : H.op) (g : G) : f (h • g) = f g := hf ⟨MulOpposite.unop h.val, h.property⟩ g
  exact ⟨(h₁.integrableOn_iff h₂ he).mp hi, h₁.setIntegral_eq h₂ he⟩

/-- Equality with the transversal pushforward for the quotient measure
normalized by the scalar Weil formula with counting measure on H. -/
theorem quotient_measure_eq_transversal_pushforward
    (hd : IsDiscrete (H : Set G)) (μ : Measure G) [SigmaFinite μ]
    (ν : Measure (G ⧸ H)) {Δ : Set G} (hΔ : MeasurableSet Δ) (hb : BijOn π Δ univ)
    (hWeil : ∀ f : G → ℂ, Measurable f → Integrable f μ → ∀ F : G ⧸ H → ℂ,
      (∀ g : G, F (π g) = ∑' h : H, f (g * h)) →
      Integrable F ν ∧ ∫ g, f g ∂μ = ∫ q, F q ∂ν) :
    ν = (μ.restrict Δ).map π := by
  classical
  have hmπ : Measurable π := QuotientGroup.continuous_mk.measurable
  apply Measure.ext
  intro A hA
  let T (n : ℕ) := (π ⁻¹' A ∩ Δ) ∩ spanningSets μ n
  let S (n : ℕ) := π '' T n
  have hT (n : ℕ) : MeasurableSet (T n) :=
    ((hA.preimage hmπ).inter hΔ).inter (measurableSet_spanningSets μ n)
  have hS (n : ℕ) : MeasurableSet (S n) :=
    localHomeomorph_measurableSet_image (H.isQuotientCoveringMap hd).isCoveringMap.isLocalHomeomorph (hT n)
  have hfin (n : ℕ) : μ (T n) < ∞ :=
    (measure_mono inter_subset_right).trans_lt (measure_spanningSets_lt_top μ n)
  have hnorm (n : ℕ) : ν (S n) = μ (T n) := by
    let f := (T n).indicator (fun _ => (1 : ℂ))
    let F := (S n).indicator (fun _ => (1 : ℂ))
    have hfi : Integrable f μ := (integrable_indicator_iff (hT n)).mpr
      (integrableOn_const (hfin n).ne)
    have he (g : G) : F (π g) = ∑' h : H, f (g * h) := by
      by_cases hg : π g ∈ S n
      · have hF : F (π g) = 1 := indicator_of_mem hg _
        obtain ⟨x, hx, hπx⟩ := hg
        have hh : g⁻¹ * x ∈ H := QuotientGroup.eq.mp hπx.symm
        let u : H := ⟨g⁻¹ * x, hh⟩
        have hxu : g * (u : G) = x := by simp [u]
        rw [tsum_eq_single u, hxu]
        · rw [hF, show f x = 1 from indicator_of_mem hx _]
        · intro h hne
          apply indicator_of_notMem
          intro hT'
          apply hne
          apply Subtype.ext
          apply mul_left_cancel (a := g)
          rw [hxu]
          exact hb.injOn hT'.1.2 hx.1.2 (by simpa using hπx.symm)
      · rw [show F (π g) = 0 from indicator_of_notMem hg _]
        have hz : (fun h : H => f (g * h)) = 0 := by
          funext h
          apply indicator_of_notMem
          intro hh
          exact hg ⟨g * h, hh, by simp⟩
        rw [hz]
        change 0 = ∑' _ : H, (0 : ℂ)
        simp
    obtain ⟨hi, hiEq⟩ := hWeil f (measurable_const.indicator (hT n)) hfi F he
    have hSn : ν (S n) ≠ ∞ := by
      have hi' : IntegrableOn (fun _ => (1 : ℂ)) (S n) ν :=
        (integrable_indicator_iff (hS n)).mp hi
      simpa [integrableOn_const_iff, lt_top_iff_ne_top] using hi'
    have hiEq' : ((μ (T n)).toReal : ℂ) = ((ν (S n)).toReal : ℂ) := by
      simpa [f, F, integral_indicator (hT n), integral_indicator (hS n), integral_const,
        MeasureTheory.measureReal_def, Measure.restrict_apply MeasurableSet.univ,
        Complex.real_smul] using hiEq
    exact (ENNReal.toReal_eq_toReal_iff' hSn (hfin n).ne).mp
      (Complex.ofReal_injective hiEq'.symm)
  have hTcov : ⋃ n, T n = π ⁻¹' A ∩ Δ := by
    simp only [T, ← inter_iUnion, iUnion_spanningSets, inter_univ]
  have hScov : ⋃ n, S n = A := by
    rw [← image_iUnion, hTcov]
    ext q
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx.1
    · intro hq
      obtain ⟨x, hx, rfl⟩ := hb.surjOn (mem_univ q)
      exact ⟨x, ⟨hq, hx⟩, rfl⟩
  have hTm : Monotone T := fun _ _ hij => inter_subset_inter_right _ (monotone_spanningSets μ hij)
  have hSm : Monotone S := fun _ _ hij => image_mono (hTm hij)
  rw [Measure.map_apply hmπ hA, Measure.restrict_apply (hA.preimage hmπ)]
  calc
    ν A = ⨆ n, ν (S n) := by rw [← hSm.measure_iUnion, hScov]
    _ = ⨆ n, μ (T n) := by simp only [hnorm]
    _ = μ (π ⁻¹' A ∩ Δ) := by rw [← hTm.measure_iUnion, hTcov]

/-- A Borel transversal identifies even the outer measure of an arbitrary
quotient subset with the outer measure of its representatives. -/
theorem transversal_pushforward_apply (hd : IsDiscrete (H : Set G)) (μ : Measure G)
    {E : Set G} (hE : MeasurableSet E) (hι : InjOn π E) (A : Set (G ⧸ H)) :
    ((μ.restrict E).map π) A = μ (π ⁻¹' A ∩ E) := by
  let q : E → G ⧸ H := fun x => π (x : G)
  have hq : Measurable q := QuotientGroup.continuous_mk.measurable.comp measurable_subtype_coe
  have hqe : MeasurableEmbedding q := by
    refine ⟨fun x y h => Subtype.ext (hι x.property y.property h), hq, fun S hS => ?_⟩
    have hmeas : MeasurableSet (Subtype.val '' S) := (MeasurableEmbedding.subtype_coe hE).measurableSet_image' hS
    have h := localHomeomorph_measurableSet_image (H.isQuotientCoveringMap hd).isCoveringMap.isLocalHomeomorph hmeas
    rwa [image_image] at h
  rw [← map_comap_subtype_coe hE μ, Measure.map_map QuotientGroup.continuous_mk.measurable
    measurable_subtype_coe]
  change ((Measure.comap ((↑) : E → G) μ).map q) A = _
  rw [hqe.map_apply, comap_subtype_coe_apply hE]
  congr 1
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨hy, y.property⟩
  · intro h
    exact ⟨⟨x, h.2⟩, h.1, rfl⟩

omit [MeasurableSpace (G ⧸ H)] [BorelSpace (G ⧸ H)] in
/-- D.1.2.4, the translates of a discrete transversal partition the
integral into an absolutely summable family. The opposite subgroup indexes
right translates, with the same counting measure as the subgroup. -/
theorem integral_tsum_of_transversal_translates
    (hd : IsDiscrete (H : Set G)) (μ : Measure G) [μ.IsMulRightInvariant]
    {Δ : Set G} (hΔ : MeasurableSet Δ) (hb : BijOn π Δ univ)
    {f : G → ℂ} (hf : Integrable f μ) :
    Summable (fun h : H.op => ‖∫ x in h • Δ, f x ∂μ‖) ∧
      (∫ x, f x ∂μ) = ∑' h : H.op, ∫ x in h • Δ, f x ∂μ := by
  haveI : DiscreteTopology H := isDiscrete_iff_discreteTopology.mp hd
  haveI : Countable H := countable_of_Lindelof_of_discrete
  haveI : Countable H.op := inferInstance
  have hF := fundamentalDomain_of_bijective_quotient H hd μ hΔ hb
  refine ⟨?_, hF.integral_eq_tsum f hf⟩
  have hi : Integrable f (Measure.sum fun h : H.op => μ.restrict (h • Δ)) := by
    rw [hF.sum_restrict_of_ac (show μ ≪ μ from by rfl)]
    exact hf
  exact hi.summable_integral.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun _ => norm_integral_le_integral_norm f)

omit [MeasurableSpace (G ⧸ H)] [BorelSpace (G ⧸ H)] in
/-- The summability assertion is integrability for counting measure. -/
theorem integrable_transversal_translates_count [T2Space G]
    (hd : IsDiscrete (H : Set G)) (μ : Measure G) [μ.IsMulRightInvariant]
    {Δ : Set G} (hΔ : MeasurableSet Δ) (hb : BijOn π Δ univ)
    {f : G → ℂ} (hf : Integrable f μ) :
    Integrable (fun h : H => ∫ x in (fun y : G => y * h) '' Δ, f x ∂μ) Measure.count := by
  let e : H ≃ H.op :=
    { toFun := fun h => ⟨MulOpposite.op h.val, h.property⟩
      invFun := fun h => ⟨MulOpposite.unop h.val, h.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  apply integrable_count_iff.mpr
  exact e.summable_iff.mpr (integral_tsum_of_transversal_translates H hd μ hΔ hb hf).1

/-- D.1.2.4, the measurability and integrability criteria and the
restricted-integral identity for the normalized quotient measure. -/
theorem quotient_transversal_integral_criteria
    (hd : IsDiscrete (H : Set G)) (μ : Measure G)
    (ν : Measure (G ⧸ H)) {Δ : Set G} (hΔ : MeasurableSet Δ) (hb : BijOn π Δ univ)
    (hnorm : ν = (μ.restrict Δ).map π) (f : G ⧸ H → ℂ) :
    (Measurable f ↔ Measurable (Δ.indicator (f ∘ π))) ∧
      (AEMeasurable f ν ↔ AEMeasurable (Δ.indicator (f ∘ π)) μ) ∧
      (Integrable f ν ↔ Integrable (Δ.indicator (f ∘ π)) μ) ∧
      (∫ q, f q ∂ν) = ∫ g in Δ, f (π g) ∂μ := by
  let P : Δ → (G ⧸ H) := Δ.domRestrict π
  have hP : MeasurableEmbedding P := quotient_transversal_embedding H hd hΔ hb
  have hPn : Function.Surjective P := fun q =>
    let ⟨x, hx, he⟩ := hb.surjOn (mem_univ q)
    ⟨⟨x, hx⟩, he⟩
  have hmπ : Measurable π := QuotientGroup.continuous_mk.measurable
  have he : (Δ.indicator (f ∘ π)) ∘ (Subtype.val : Δ → G) = f ∘ P :=
    funext fun x => indicator_of_mem x.property _
  have hμP : ν = (Measure.comap (Subtype.val : Δ → G) μ).map P := by
    rw [hnorm, ← map_comap_subtype_coe hΔ, Measure.map_map hmπ measurable_subtype_coe]
    rfl
  refine ⟨⟨fun hf => (hf.comp hmπ).indicator hΔ, ?_⟩, ?_, ?_, ?_⟩
  · intro hf B hB
    have hsB : MeasurableSet ((f ∘ P) ⁻¹' B) := by
      rw [← he]
      exact hB.preimage (hf.comp measurable_subtype_coe)
    have h := hP.measurableSet_image' hsB
    change MeasurableSet (P '' (P ⁻¹' (f ⁻¹' B))) at h
    rwa [hPn.image_preimage] at h
  · rw [hμP, hP.aemeasurable_map_iff, aemeasurable_indicator_iff hΔ]
    rw [← map_comap_subtype_coe hΔ, (MeasurableEmbedding.subtype_coe hΔ).aemeasurable_map_iff]
    rfl
  · rw [hμP, hP.integrable_map_iff, integrable_indicator_iff hΔ]
    change Integrable (f ∘ P) _ ↔ Integrable (f ∘ π) (μ.restrict Δ)
    rw [← map_comap_subtype_coe hΔ, (MeasurableEmbedding.subtype_coe hΔ).integrable_map_iff]
    rfl
  · rw [hμP, hP.integral_map]
    exact integral_subtype_comap hΔ (f ∘ π)

end

end Masullo
