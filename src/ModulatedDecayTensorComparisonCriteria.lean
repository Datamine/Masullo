import ModulatedDecayTensorComparisonStages
import CompletedTensorFlip

open Bornology Function Set Topology UniformSpace
open scoped TensorProduct

namespace Masullo

noncomputable section

section

variable {H : Type*} [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H]
  [T2Space H] [LocallyCompactSpace H] [SecondCountableTopology H]

set_option maxHeartbeats 1000000 in
/-- Stage coverage and bounded lifting give a bijective comparison which
preserves and reflects bounded subsets. -/
theorem comparison_bijective_bounded_of_stageCoverage (I : Set ℝ)
    (hcov : InductiveDecayTensorStageCoverage I H) :
    let A := BruhatSchwartz H
    let R := PositiveRealExponentialDecay I
    letI : IsTopologicalAddGroup A := (PolynormableSpace.withSeminorms ℂ A).topologicalAddGroup
    letI : IsTopologicalAddGroup R := (PolynormableSpace.withSeminorms ℂ R).topologicalAddGroup
    let C := completedInductiveTensorComparison (E := A) (F := R)
    (∀ S : Set (projectiveTensorModuleStructure A R).Completed, IsVonNBounded ℂ S →
      ∃ B : Set (inductiveTensorModuleStructure A R).Completed, IsVonNBounded ℂ B ∧ C '' B = S) →
    Bijective C ∧ ∀ B : Set (inductiveTensorModuleStructure A R).Completed,
      IsVonNBounded ℂ (C '' B) ↔ IsVonNBounded ℂ B := by
  dsimp only
  let A := BruhatSchwartz H
  let R := PositiveRealExponentialDecay I
  letI : IsTopologicalAddGroup A := (PolynormableSpace.withSeminorms ℂ A).topologicalAddGroup
  letI : IsTopologicalAddGroup R := (PolynormableSpace.withSeminorms ℂ R).topologicalAddGroup
  let C := completedInductiveTensorComparison (E := A) (F := R)
  let P := projectiveTensorModuleStructure A R
  let X := A ⊗[ℂ] R
  letI : UniformSpace X := P.uniformSpace
  letI : IsUniformAddGroup X := P.uniformGroup
  letI : UniformContinuousConstSMul ℂ X := P.uniformConstSmul
  letI : PolynormableSpace ℂ X := projectiveTensor_withSeminorms.toPolynormableSpace
  letI : PolynormableSpace ℂ P.Completed := polynormableSpace_completion
  letI : ContinuousSMul ℂ P.Completed := (PolynormableSpace.withSeminorms ℂ P.Completed).continuousSMul
  intro hlift
  have hC : Injective C := comparison_injective_of_stageCoverage I hcov
  refine ⟨⟨hC, ?_⟩, ?_⟩
  · intro z
    have hB := hlift {z} (isVonNBounded_singleton (𝕜 := ℂ) z)
    have hz : z ∈ C '' hB.choose := by
      rw [hB.choose_spec.2]
      exact mem_singleton z
    exact ⟨hz.choose, hz.choose_spec.2⟩
  · intro B
    refine ⟨?_, fun h => h.image C⟩
    intro h
    let hB := hlift (C '' B) h
    have he : hB.choose = B := Set.image_injective.mpr hC hB.choose_spec.2
    exact he ▸ hB.choose_spec.1

end

section

variable {H : Type*} [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H]
  [T2Space H] [LocallyCompactSpace H]

set_option maxHeartbeats 1800000 in
/-- The bounded comparison with the radial factor first is obtained by
conjugating the comparison with the two canonical tensor flips. -/
theorem comparison_radialFirst_of_angularFirst (I : Set ℝ) :
    let A := BruhatSchwartz H
    let R := PositiveRealExponentialDecay I
    letI : IsTopologicalAddGroup A := (PolynormableSpace.withSeminorms ℂ A).topologicalAddGroup
    letI : IsTopologicalAddGroup R := (PolynormableSpace.withSeminorms ℂ R).topologicalAddGroup
    let C := completedInductiveTensorComparison (E := A) (F := R)
    let C' := completedInductiveTensorComparison (E := R) (F := A)
    (Bijective C ∧ ∀ B : Set (inductiveTensorModuleStructure A R).Completed,
      IsVonNBounded ℂ (C '' B) ↔ IsVonNBounded ℂ B) →
    Bijective C' ∧ ∀ B : Set (inductiveTensorModuleStructure R A).Completed,
      IsVonNBounded ℂ (C' '' B) ↔ IsVonNBounded ℂ B := by
  dsimp only
  let A := BruhatSchwartz H
  let R := PositiveRealExponentialDecay I
  letI : IsTopologicalAddGroup A := (PolynormableSpace.withSeminorms ℂ A).topologicalAddGroup
  letI : IsTopologicalAddGroup R := (PolynormableSpace.withSeminorms ℂ R).topologicalAddGroup
  let C := completedInductiveTensorComparison (E := A) (F := R)
  let C' := completedInductiveTensorComparison (E := R) (F := A)
  let D := inductiveTensorModuleStructure A R
  let Q := projectiveTensorModuleStructure R A
  let X := R ⊗[ℂ] A
  letI : UniformSpace X := Q.uniformSpace
  letI : IsUniformAddGroup X := Q.uniformGroup
  letI : T0Space Q.Completed := Completion.t0Space X
  intro h
  let exD := exists_completedInductiveTensorFlip (A := A) (R := R)
  let exQ := exists_completedProjectiveTensorFlip (A := A) (R := R)
  let U := exD.choose
  let V := exQ.choose
  have he : C'.comp U.toContinuousLinearMap = V.toContinuousLinearMap.comp C := by
    apply D.continuousLinearMap_ext_on_tmul
    intro a r
    change C' (U (D.incl (a ⊗ₜ[ℂ] r))) = V (C (D.incl (a ⊗ₜ[ℂ] r)))
    rw [exD.choose_spec, completedInductiveTensorComparison_incl,
      completedInductiveTensorComparison_incl, exQ.choose_spec]
  have hf : (C' : _ → _) = V ∘ C ∘ U.symm := by
    funext x
    have hx : C' (U (U.symm x)) = V (C (U.symm x)) :=
      DFunLike.congr_fun he (U.symm x)
    exact (congrArg C' (U.apply_symm_apply x)).symm.trans hx
  refine ⟨hf.symm ▸ V.bijective.comp (h.1.comp U.symm.bijective), ?_⟩
  intro B
  refine ⟨?_, fun hh => hh.image C'⟩
  intro hh
  have hpre : IsVonNBounded ℂ (V.symm '' (C' '' B)) := hh.image V.symm.toContinuousLinearMap
  have hcom : (V.symm : _ → _) ∘ C' = C ∘ U.symm := by
    rw [hf]
    funext x
    exact V.symm_apply_apply _
  rw [Set.image_image] at hpre
  change IsVonNBounded ℂ (((V.symm : _ → _) ∘ C') '' B) at hpre
  rw [hcom] at hpre
  have hpre' : IsVonNBounded ℂ (C '' (U.symm '' B)) := by
    simpa only [Set.image_image, Function.comp_def] using hpre
  have hb := (h.2 (U.symm '' B)).mp hpre'
  have ht : IsVonNBounded ℂ (U '' (U.symm '' B)) := hb.image U.toContinuousLinearMap
  simpa only [Set.image_image, U.apply_symm_apply, Set.image_id'] using ht


end

end
end Masullo
