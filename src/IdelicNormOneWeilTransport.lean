import IdelicWeilRestriction
import SLocalSplitRadialComparison

open Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped NumberField

namespace Masullo

noncomputable section

/-- Comapping along embeddings commutes with a change of coordinates in a commuting square. -/
theorem map_comap_of_square {A B C D : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C] [MeasurableSpace D]
    (e₁ : A ≃ᵐ B) (e₂ : C ≃ᵐ D) (i : A → C) (j : B → D)
    (hi : MeasurableEmbedding i) (hj : MeasurableEmbedding j)
    (h : ∀ a, e₂ (i a) = j (e₁ a)) (μ : Measure C) :
    Measure.map e₁ (μ.comap i) = (Measure.map e₂ μ).comap j := by
  ext s hs
  rw [Measure.map_apply e₁.measurable hs, hi.comap_apply,
    hj.comap_apply, Measure.map_apply e₂.measurable (hj.measurableSet_image.mpr hs)]
  congr 1
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨e₁ a, ha, (h a).symm⟩
  · rintro ⟨b, hb, he⟩
    let a := e₁.symm b
    have hab : e₁ a = b := e₁.apply_symm_apply b
    refine ⟨a, ?_, e₂.injective ?_⟩
    · show e₁ a ∈ s
      rwa [hab]
    · exact (h a).trans ((congrArg j hab).trans he)

variable (F : Type*) [Field F] [NumberField F]
  (S : Finset (HeightOneSpectrum (𝓞 F)))

private abbrev GlobalQuotient := NormOneIdeles F ⧸ (principalNormOne F).range
private abbrev LocalQuotient :=
  normOneIdeleBlock F S ⧸ (principalNormOne F).range.comap (normOneIdeleBlock F S).subtype

local instance : T2Space (Idele F) := ideles_hausdorff
local instance : LocallyCompactSpace (Idele F) := ideles_locallyCompact
local instance : MeasurableSpace (Idele F) := borel _
local instance : BorelSpace (Idele F) := ⟨rfl⟩
local instance : LocallyCompactSpace (NormOneIdeles F) :=
  (isClosed_singleton.preimage (ideleNorm_continuous F)).isClosedEmbedding_subtypeVal.locallyCompactSpace
local instance : MeasurableSpace (NormOneIdeles F) := borel _
local instance : BorelSpace (NormOneIdeles F) := ⟨rfl⟩
local instance : MeasurableSpace (GlobalQuotient F) := borel _
local instance : BorelSpace (GlobalQuotient F) := ⟨rfl⟩
local instance : MeasurableSpace (LocalQuotient F S) := borel _
local instance : BorelSpace (LocalQuotient F S) := ⟨rfl⟩
local instance : MeasurableSpace (normOneIdeleClass F) := borel _
local instance : BorelSpace (normOneIdeleClass F) := ⟨rfl⟩
local instance : MeasurableSpace (SIdeleClass F S) := borel _
local instance : BorelSpace (SIdeleClass F S) := ⟨rfl⟩
local instance : BorelSpace (sNormOneClass F S) := inferInstanceAs (BorelSpace (Subtype _))

set_option maxHeartbeats 2500000 in
/-- The Weil-restricted norm-one quotient measure, written in the actual
S-local class group, is the comap of the corresponding global class measure. -/
theorem normOneIdeleBlock_comap_transport (ν : Measure (GlobalQuotient F)) :
    let e₁ := normOneIdeleBlock_quotientEquiv F S
    let e₂ := normOneClass_quotientEquiv F
    let i : LocalQuotient F S →* GlobalQuotient F :=
      QuotientGroup.map _ (principalNormOne F).range (normOneIdeleBlock F S).subtype le_rfl
    Measure.map e₁ (ν.comap i) =
      (Measure.map e₂ ν).comap (sIdeleNormOneContinuousInclusion F S) := by
  dsimp only
  let e₁ := (normOneIdeleBlock_quotientEquiv F S).toHomeomorph.toMeasurableEquiv
  let e₂ := (normOneClass_quotientEquiv F).toHomeomorph.toMeasurableEquiv
  let H := (principalNormOne F).range
  let J := normOneIdeleBlock F S
  let i : LocalQuotient F S →* GlobalQuotient F :=
    QuotientGroup.map _ H J.subtype le_rfl
  let j := sIdeleNormOneContinuousInclusion F S
  have hi : MeasurableEmbedding i :=
    (openSubgroup_quotientMap_openEmbedding H J (normOneIdeleBlock_open F S) _ rfl).measurableEmbedding
  have h (a : LocalQuotient F S) : e₂ (i a) = j (e₁ a) := by
    apply Subtype.ext
    exact (normOneIdeleBlock_quotientEquiv_inclusion F S a).symm
  have hjEq : (j : sNormOneClass F S → normOneIdeleClass F) = e₂ ∘ i ∘ e₁.symm := by
    funext b
    change j b = e₂ (i (e₁.symm b))
    exact (congrArg j (e₁.apply_symm_apply b).symm).trans (h (e₁.symm b)).symm
  have hj : MeasurableEmbedding j := hjEq.symm ▸
    e₂.measurableEmbedding.comp (hi.comp e₁.symm.measurableEmbedding)
  exact map_comap_of_square e₁ e₂ i j hi hj h ν

end
end Masullo
