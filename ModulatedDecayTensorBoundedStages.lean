import CompletedProjectiveTensorSlices
import BruhatStageRetraction
import ExponentialDecayStructure

open Bornology Function Set Topology
open scoped TensorProduct

namespace Masullo

noncomputable section

variable {H : Type*} [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H]
  [T2Space H] [LocallyCompactSpace H] [SecondCountableTopology H]

/-- The angular slice of a completed decay tensor along a radial functional. -/
def decayTensor_angularSlice (I : Set ℝ) (φ : PositiveRealExponentialDecay I →L[ℂ] ℂ) :
    (projectiveTensorModuleStructure (BruhatSchwartz H) (PositiveRealExponentialDecay I)).Completed
      →L[ℂ] BruhatSchwartz H := by
  let A := BruhatSchwartz H
  letI : UniformSpace A := bruhatSchwartzUniformSpace
  letI : IsUniformAddGroup A := isUniformAddGroup_of_addCommGroup
  letI : CompleteSpace A := bruhatSchwartz_complete
  letI : ContinuousSMul ℂ A := (PolynormableSpace.withSeminorms ℂ A).continuousSMul
  letI : T2Space A := bruhatSchwartz_t2
  exact completedProjectiveTensor_slice φ

set_option maxHeartbeats 650000 in
/-- Slices of a bounded set of projective decay tensors lie in one angular
stage, uniformly over a family of radially bounded functionals. -/
theorem exists_angularStage_of_bounded_decaySlices [CompactSpace H] {J : Type*} [Nonempty J]
    (I : Set ℝ) (e : J → PositiveRealExponentialDecay I →L[ℂ] ℂ)
    (p : Seminorm ℂ (PositiveRealExponentialDecay I)) (hp : Continuous p)
    (he : ∀ j r, ‖e j r‖ ≤ p r)
    (S : Set (projectiveTensorModuleStructure (BruhatSchwartz H) (PositiveRealExponentialDecay I)).Completed)
    (hS : IsVonNBounded ℂ S) :
    ∃ q : WholeBruhatStage H, ∀ j z, z ∈ S → decayTensor_angularSlice I (e j) z ∈ range q.val.inclusionCLM := by
  let A := BruhatSchwartz H
  letI : UniformSpace A := bruhatSchwartzUniformSpace
  letI : IsUniformAddGroup A := isUniformAddGroup_of_addCommGroup
  letI : CompleteSpace A := bruhatSchwartz_complete
  letI : ContinuousSMul ℂ A := (PolynormableSpace.withSeminorms ℂ A).continuousSMul
  letI : T2Space A := bruhatSchwartz_t2
  let B : Set A := {a | ∃ j z, z ∈ S ∧ decayTensor_angularSlice I (e j) z = a}
  have hB : IsVonNBounded ℂ B := completedProjectiveTensor_slices_bounded e p hp he S hS
  obtain ⟨q, C, _, hC⟩ := (bruhatSchwartz_strict (G := H)).2.2 B hB
  obtain ⟨q', hq'⟩ := exists_wholeBruhatStage_refinement_of_compact q
  refine ⟨q', fun j z hz => ?_⟩
  have hm : decayTensor_angularSlice I (e j) z ∈ B := ⟨j, z, hz, rfl⟩
  obtain ⟨a, _, ha⟩ := hC.symm ▸ hm
  exact ⟨q.transition q'.val hq' a, (q.inclusion_transition q'.val hq' a).trans ha⟩

end
end Masullo
