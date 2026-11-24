import QuotientIndentation
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.MeasureTheory.Measure.Prod

open Filter Function MeasureTheory Set Topology
open scoped ENNReal

namespace Masullo

noncomputable section

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
variable (H : Subgroup G) (hH : IsClosed (H : Set G))

private abbrev qH := (QuotientGroup.mk : G → G ⧸ H)

private def restrictCutoff (u : C(G, ℝ)) (K : Subgroup G) : C(K, ℝ) :=
  u.comp ⟨Subtype.val, continuous_subtype_val⟩

private abbrev stageH (K : Subgroup G) := H.comap K.subtype

private abbrev stageQ (K : Subgroup G) :=
  (QuotientGroup.mk : K → K ⧸ stageH H K)

private def stageInclusion (K : Subgroup G) : stageH H K → H :=
  fun h => ⟨((h : K) : G), h.property⟩

omit [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [BorelSpace G] in
private theorem stageInclusion_measurable (K : Subgroup G) :
    Measurable (stageInclusion H K) :=
  (measurable_subtype_coe.comp measurable_subtype_coe).subtype_mk

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [BorelSpace G] in
omit [TopologicalSpace G] [MeasurableSpace G] in
private theorem stageInclusion_injective (K : Subgroup G) :
    Injective (stageInclusion H K) := fun _ _ h =>
  Subtype.ext (Subtype.ext (congrArg (fun a : H => (a : G)) h))

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [BorelSpace G] in
omit [TopologicalSpace G] [MeasurableSpace G] in
private theorem stageInclusion_range (K : Subgroup G) :
    range (stageInclusion H K) = {h : H | (h : G) ∈ K} := by
  ext h
  constructor
  · rintro ⟨a, rfl⟩
    exact (a : K).property
  · intro hh
    exact ⟨⟨⟨h, hh⟩, h.property⟩, rfl⟩

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
  [SecondCountableTopology G] in
private theorem stageInclusion_map_count (K : Subgroup G) (hK : IsClosed (K : Set G)) :
    Measure.count.map (stageInclusion H K) =
      (Measure.count : Measure H).restrict {h : H | (h : G) ∈ K} := by
  have hS : MeasurableSet {h : H | (h : G) ∈ K} :=
    (hK.preimage continuous_subtype_val).measurableSet
  have he := stageInclusion_measurable H K
  ext s hs
  rw [Measure.map_apply he hs, Measure.restrict_apply hs, Measure.count_apply (hs.preimage he),
    Measure.count_apply (hs.inter hS), ← (stageInclusion_injective H K).encard_image,
    image_preimage_eq_inter_range, stageInclusion_range]

include hH in
omit [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] in
private theorem restrictCutoff_proper (u : C(G, ℝ))
    (hp : ∀ L : Set (G ⧸ H), IsCompact L → IsCompact (tsupport u ∩ qH H ⁻¹' L))
    (K : Subgroup G) (hK : IsClosed (K : Set G)) (L : Set (K ⧸ stageH H K))
    (hL : IsCompact L) :
    IsCompact (tsupport (restrictCutoff u K) ∩ stageQ H K ⁻¹' L) := by
  let f : K ⧸ stageH H K → G ⧸ H := QuotientGroup.map (stageH H K) H K.subtype le_rfl
  have hf : Continuous f := by
    apply (QuotientGroup.isQuotientMap_mk (stageH H K)).continuous_iff.mpr
    exact QuotientGroup.continuous_mk.comp continuous_subtype_val
  have ht : tsupport (restrictCutoff u K) ⊆ Subtype.val ⁻¹' tsupport u := by
    apply closure_minimal _ ((isClosed_tsupport _).preimage continuous_subtype_val)
    intro x hx
    exact subset_tsupport _ hx
  letI : T1Space (K ⧸ stageH H K) :=
    QuotientGroup.t1Space_iff.mpr (hH.preimage continuous_subtype_val)
  apply (hK.isClosedEmbedding_subtypeVal.isCompact_preimage (hp (f '' L) (hL.image hf))).of_isClosed_subset
    ((isClosed_tsupport _).inter (hL.isClosed.preimage QuotientGroup.continuous_mk))
  intro x hx
  exact ⟨ht hx.1, ⟨stageQ H K x, hx.2, rfl⟩⟩

omit [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] in
private theorem restrictCutoff_count (u : C(G, ℝ)) (K : Subgroup G) (hK : IsClosed (K : Set G))
    (hsupp : tsupport u ⊆ K)
    (hu : ∀ x : G, Integrable (fun h : H => u ((h : G)⁻¹ * x)) Measure.count ∧
      (∫ h : H, u ((h : G)⁻¹ * x) ∂Measure.count) = 1) (x : K) :
    Integrable (fun h : stageH H K => restrictCutoff u K ((h : K)⁻¹ * x)) Measure.count ∧
    (∫ h : stageH H K, restrictCutoff u K ((h : K)⁻¹ * x) ∂Measure.count) = 1 := by
  let f (h : H) := u ((h : G)⁻¹ * (x : G))
  let e := stageInclusion H K
  have he : Measurable e := stageInclusion_measurable H K
  let S := {h : H | (h : G) ∈ K}
  have hS : MeasurableSet S := (hK.preimage continuous_subtype_val).measurableSet
  have hmap : Measure.count.map e = (Measure.count : Measure H).restrict S :=
    stageInclusion_map_count H K hK
  have hzero {h : H} (hh : h ∉ S) : f h = 0 := by
    change u ((h : G)⁻¹ * (x : G)) = 0
    apply image_eq_zero_of_notMem_tsupport
    intro hs
    have hm := hsupp hs
    apply hh
    change (h : G) ∈ K
    have hm' := K.mul_mem x.property (K.inv_mem hm)
    simpa only [mul_inv_rev, inv_inv, ← mul_assoc, mul_inv_cancel, one_mul] using hm'
  change Integrable (f ∘ e) Measure.count ∧ (∫ h, (f ∘ e) h ∂Measure.count) = 1
  have hfm : AEStronglyMeasurable f (Measure.count.map e) :=
    (u.continuous.comp (continuous_subtype_val.inv.mul continuous_const)).aestronglyMeasurable
  refine ⟨(integrable_map_measure hfm he.aemeasurable).mp ?_, ?_⟩
  · rw [hmap]
    exact (hu x).1.integrableOn
  · change (∫ h, f (e h) ∂Measure.count) = 1
    rw [← integral_map he.aemeasurable hfm, hmap, ← integral_indicator hS]
    convert (hu x).2 using 1
    apply integral_congr_ae
    exact .of_forall fun h => by
      by_cases hh : h ∈ S
      · exact indicator_of_mem hh _
      · rw [indicator_of_notMem hh]
        exact (hzero hh).symm


omit [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] in
theorem subgroup_count_isHaarMeasure [DiscreteTopology H] :
    (Measure.count : Measure H).IsHaarMeasure where
  lt_top_of_isCompact K hK := by
    rw [Measure.count_apply (isOpen_discrete K).measurableSet]
    exact_mod_cast hK.finite_of_discrete.encard_lt_top
  open_pos U hU hne := by
    rw [Measure.count_apply hU.measurableSet]
    exact_mod_cast hne.encard_pos.ne'

/-- The diagonal average of the product of two copies of an indentation. -/
def diagonalIndentation (u : C(G, ℝ)) (x y : G) : ℝ :=
  ∫ a : H, u ((a : G)⁻¹ * x) * u ((a : G)⁻¹ * y) ∂Measure.count

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [BorelSpace G] in
theorem diagonalIndentation_eq_zero (u : C(G, ℝ)) (K : Subgroup G)
    (hs : tsupport u ⊆ K) {x y : G} (hx : x ∈ K) (hy : y ∉ K) :
    diagonalIndentation H u x y = 0 := by
  unfold diagonalIndentation
  have hw (a : H) : u ((a : G)⁻¹ * x) * u ((a : G)⁻¹ * y) = 0 := by
    by_cases h : u ((a : G)⁻¹ * x) = 0
    · rw [h, zero_mul]
    have ham := K.mul_mem hx (K.inv_mem (hs (subset_tsupport _ h)))
    have ha : (a : G) ∈ K := by
      simpa only [mul_inv_rev, inv_inv, ← mul_assoc, mul_inv_cancel, one_mul] using ham
    have hb : (a : G)⁻¹ * y ∉ tsupport u := by
      intro h
      apply hy
      have hprod := K.mul_mem ha (hs h)
      simpa only [← mul_assoc, mul_inv_cancel, one_mul] using hprod
    rw [image_eq_zero_of_notMem_tsupport hb, mul_zero]
  simp [hw]

include hH in
/-- Proposition 12.2.2.4. An indentation supported in the first stage restricts
to each stage, and the truncated diagonal integral vanishes at every stage. -/
theorem filtered_quotientIndentation [DiscreteTopology H]
    (K : ℕ → Subgroup G) (hKo : ∀ k, IsOpen (K k : Set G)) (hKm : Monotone K)
    (hcover : ∀ x : G, ∃ a : H, (a : G)⁻¹ * x ∈ K 0)
    {D : Set G} (hD : D ⊆ K 0) (ν : Measure G) :
    ∃ u : C(G, ℝ), (∀ x, 0 ≤ u x) ∧ tsupport u ⊆ K 0 ∧
      (∀ L : Set (G ⧸ H), IsCompact L → IsCompact (tsupport u ∩ qH H ⁻¹' L)) ∧
      (∀ x : G, Integrable (fun h : H => u ((h : G)⁻¹ * x)) Measure.count ∧
        (∫ h : H, u ((h : G)⁻¹ * x) ∂Measure.count) = 1) ∧
      (∀ k,
        (∀ L : Set (K k ⧸ stageH H (K k)), IsCompact L →
          IsCompact (tsupport (restrictCutoff u (K k)) ∩ stageQ H (K k) ⁻¹' L)) ∧
        (∀ x : K k, 0 ≤ restrictCutoff u (K k) x) ∧
        (∀ x : K k,
          Integrable (fun h : stageH H (K k) => restrictCutoff u (K k) ((h : K k)⁻¹ * x))
            Measure.count ∧
          (∫ h : stageH H (K k), restrictCutoff u (K k) ((h : K k)⁻¹ * x) ∂Measure.count) = 1)) ∧
      ∀ w : (G ⧸ H) × (G ⧸ H) → ℂ, ∀ k,
        let f (x : G) (h : H) := ((K k : Set G)ᶜ).indicator
          (fun y => (diagonalIndentation H u x y : ℂ) * w (qH H x, qH H y))
          ((h : G)⁻¹ * x)
        Integrable (fun p : G × H => f p.1 p.2) ((ν.restrict D).prod Measure.count) ∧
          (∫ x in D, ∫ h : H, f x h ∂Measure.count ∂ν) = 0 ∧
          Tendsto (fun n : ℕ => ∫ x in D, ∫ h : H,
            ((K n : Set G)ᶜ).indicator
              (fun y => (diagonalIndentation H u x y : ℂ) * w (qH H x, qH H y))
              ((h : G)⁻¹ * x) ∂Measure.count ∂ν) atTop (𝓝 0) := by
  letI : (Measure.count : Measure H).IsHaarMeasure := subgroup_count_isHaarMeasure H
  have hqcover (q : G ⧸ H) : ∃ x ∈ K 0, qH H x = q := by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨a, ha⟩ := hcover x
    refine ⟨(a : G)⁻¹ * x, ha, ?_⟩
    change QuotientGroup.mk ((a : G)⁻¹ * x) = QuotientGroup.mk x
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, (QuotientGroup.eq_one_iff _).mpr a.property,
      inv_one, one_mul]
  obtain ⟨u, hn, hs, hp, hi⟩ :=
    exists_quotientIndentation_supported H hH Measure.count (hKo 0) hqcover
  have hstage (k : ℕ) : tsupport u ⊆ K k :=
    hs.trans (hKm (Nat.zero_le k))
  refine ⟨u, hn, hs, hp, hi, fun k => ?_, ?_⟩
  · have hc := (K k).isClosed_of_isOpen (hKo k)
    exact ⟨restrictCutoff_proper H hH u hp (K k) hc,
      fun x => hn (x : G), restrictCutoff_count H u (K k) hc (hstage k) hi⟩
  · intro w k
    let f (n : ℕ) (x : G) (h : H) := ((K n : Set G)ᶜ).indicator
      (fun y => (diagonalIndentation H u x y : ℂ) * w (qH H x, qH H y))
      ((h : G)⁻¹ * x)
    change Integrable (fun p : G × H => f k p.1 p.2) ((ν.restrict D).prod Measure.count) ∧
      (∫ x in D, ∫ h : H, f k x h ∂Measure.count ∂ν) = 0 ∧
      Tendsto (fun n => ∫ x in D, ∫ h : H, f n x h ∂Measure.count ∂ν) atTop (𝓝 0)
    have hz (n : ℕ) {x : G} (hx : x ∈ K 0) (h : H) : f n x h = 0 := by
      by_cases hy : (h : G)⁻¹ * x ∈ K n
      · exact indicator_of_notMem (show (h : G)⁻¹ * x ∉ (K n : Set G)ᶜ from not_not_intro hy) _
      · dsimp only [f]
        rw [indicator_of_mem (show (h : G)⁻¹ * x ∈ (K n : Set G)ᶜ from hy),
          diagonalIndentation_eq_zero H u (K n) (hstage n) (hKm (Nat.zero_le n) hx) hy,
          Complex.ofReal_zero, zero_mul]
    have hev : ∀ᵐ x ∂(ν.restrict D), x ∈ K 0 :=
      ae_restrict_of_ae_restrict_of_subset hD (ae_restrict_mem (hKo 0).measurableSet)
    have hint (n : ℕ) : (∫ x in D, ∫ h : H, f n x h ∂Measure.count ∂ν) = 0 := by
      calc
        _ = ∫ _ : G, (0 : ℂ) ∂(ν.restrict D) := ?_
        _ = _ := integral_zero _ _
      apply integral_congr_ae
      filter_upwards [hev] with x hx
      simp only [hz n hx, integral_zero]
    refine ⟨?_, hint k, ?_⟩
    · refine (integrable_zero _ _ _).congr ?_
      have hprod : ∀ᵐ p ∂((ν.restrict D).prod (Measure.count : Measure H)), p.1 ∈ K 0 :=
        Measure.quasiMeasurePreserving_fst.ae hev
      filter_upwards [hprod] with p hp
      exact (hz k hp p.2).symm
    · simpa only [hint] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0))

end
end Masullo
