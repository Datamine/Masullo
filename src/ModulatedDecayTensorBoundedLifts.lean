import ModulatedDecayTensorLocalization
import ModulatedDecayTensorComparisonStages
import ModulatedDecayProjectiveStageInclusion
import BruhatStageRetraction
import ExponentialDecayStructure

open Bornology Function Set Topology UniformSpace
open scoped TensorProduct

namespace Masullo

noncomputable section

variable {H : Type*} [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H]
  [T2Space H] [LocallyCompactSpace H] [SecondCountableTopology H]

private theorem boundedLift_through_factor
    {X Y Z : Type*} [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]
    [AddCommGroup Z] [Module ℂ Z] [TopologicalSpace Z]
    (C : Y →L[ℂ] Z) (J : X →L[ℂ] Y) (P : X →L[ℂ] Z)
    (h : C.comp J = P) (B : Set X) (hB : IsVonNBounded ℂ B) :
    ∃ L : Set Y, IsVonNBounded ℂ L ∧ C '' L = P '' B := by
  refine ⟨J '' B, hB.image J, ?_⟩
  rw [Set.image_image]
  exact congrArg (fun v : X →L[ℂ] Z => v '' B) h

set_option maxHeartbeats 3400000 in
/-- Every bounded set in the completed projective decay tensor has a bounded
lift through the canonical comparison. -/
theorem comparison_boundedLift [CompactSpace H] (I : Set ℝ)
    (hI : I.Nonempty) (hInt : OrdConnected I) :
    let A := BruhatSchwartz H
    let R := PositiveRealExponentialDecay I
    letI : IsTopologicalAddGroup A := (PolynormableSpace.withSeminorms ℂ A).topologicalAddGroup
    letI : IsTopologicalAddGroup R := (PolynormableSpace.withSeminorms ℂ R).topologicalAddGroup
    ∀ S : Set (projectiveTensorModuleStructure A R).Completed,
      IsVonNBounded ℂ S →
      ∃ B : Set (inductiveTensorModuleStructure A R).Completed,
        IsVonNBounded ℂ B ∧
          (completedInductiveTensorComparison (E := A) (F := R)) '' B = S := by
  dsimp only
  let A := BruhatSchwartz H
  let R := PositiveRealExponentialDecay I
  letI : IsTopologicalAddGroup A := (PolynormableSpace.withSeminorms ℂ A).topologicalAddGroup
  letI : IsTopologicalAddGroup R := (PolynormableSpace.withSeminorms ℂ R).topologicalAddGroup
  let C := completedInductiveTensorComparison (E := A) (F := R)
  intro S hS
  obtain ⟨p, B, hB, hBS⟩ := exists_projectiveStage_of_bounded_decayTensors I hI hInt S hS
  obtain ⟨J, hJ⟩ := exists_projectiveStageTensor_to_global p I hI hInt
  let P := completedProjectiveTensor_mapLeft (R := R) p.val.inclusionCLM
  have hc : C.comp J = P := comparison_comp_projectiveStageInclusion p I J hJ
  obtain ⟨L, hL, hCL⟩ := boundedLift_through_factor C J P hc B hB
  exact ⟨L, hL, hCL.trans hBS⟩

/-- The comparison reaches the entire completed projective decay tensor. -/
theorem comparison_surjective [CompactSpace H] (I : Set ℝ)
    (hI : I.Nonempty) (hInt : OrdConnected I) :
    let A := BruhatSchwartz H
    let R := PositiveRealExponentialDecay I
    letI : IsTopologicalAddGroup A := (PolynormableSpace.withSeminorms ℂ A).topologicalAddGroup
    letI : IsTopologicalAddGroup R := (PolynormableSpace.withSeminorms ℂ R).topologicalAddGroup
    Surjective (completedInductiveTensorComparison (E := A) (F := R)) := by
  dsimp only
  let A := BruhatSchwartz H
  let R := PositiveRealExponentialDecay I
  letI : IsTopologicalAddGroup A := (PolynormableSpace.withSeminorms ℂ A).topologicalAddGroup
  letI : IsTopologicalAddGroup R := (PolynormableSpace.withSeminorms ℂ R).topologicalAddGroup
  let P := projectiveTensorModuleStructure A R
  let C := completedInductiveTensorComparison (E := A) (F := R)
  let X := A ⊗[ℂ] R
  letI : UniformSpace X := P.uniformSpace
  letI : IsUniformAddGroup X := P.uniformGroup
  letI : UniformContinuousConstSMul ℂ X := P.uniformConstSmul
  letI : PolynormableSpace ℂ X := projectiveTensor_withSeminorms.toPolynormableSpace
  letI : PolynormableSpace ℂ P.Completed := polynormableSpace_completion
  letI : ContinuousSMul ℂ P.Completed := (PolynormableSpace.withSeminorms ℂ P.Completed).continuousSMul
  intro z
  obtain ⟨B, _, hB⟩ := comparison_boundedLift (H := H) I hI hInt {z} (isVonNBounded_singleton z)
  have hz : z ∈ C '' B := by rw [hB]; exact mem_singleton z
  obtain ⟨x, _, hx⟩ := hz
  exact ⟨x, hx⟩

end
end Masullo
