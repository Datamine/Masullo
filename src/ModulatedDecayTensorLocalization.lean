import ModulatedDecayTensorBoundedStages
import CompletedProjectiveTensorSliceRetraction
import InjectiveTensorFlip
import BruhatStageRetraction
import ExponentialDecayStructure


open Bornology Function Set Topology
open scoped TensorProduct

namespace Masullo

noncomputable section

universe u

variable {H : Type u} [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H]
  [T2Space H] [LocallyCompactSpace H] [SecondCountableTopology H]

set_option maxHeartbeats 4200000 in
/-- Every bounded set in the completed projective decay tensor is the image
of a bounded set in a single angular stage. -/
theorem exists_projectiveStage_of_bounded_decayTensors [CompactSpace H]
    (I : Set ℝ) (hI : I.Nonempty) (hInt : OrdConnected I)
    (S : Set (projectiveTensorModuleStructure (BruhatSchwartz H) (PositiveRealExponentialDecay I)).Completed)
    (hS : IsVonNBounded ℂ S) :
    ∃ q : WholeBruhatStage H,
      ∃ B : Set (projectiveTensorModuleStructure q.val.Space (PositiveRealExponentialDecay I)).Completed,
        IsVonNBounded ℂ B ∧
          completedProjectiveTensor_mapLeft (R := PositiveRealExponentialDecay I)
            q.val.inclusionCLM '' B = S := by
  let A := BruhatSchwartz H
  let R := PositiveRealExponentialDecay I
  letI : UniformSpace A := bruhatSchwartzUniformSpace
  letI : IsUniformAddGroup A := isUniformAddGroup_of_addCommGroup
  letI : CompleteSpace A := bruhatSchwartz_complete
  letI : ContinuousSMul ℂ A := (PolynormableSpace.withSeminorms ℂ A).continuousSMul
  letI : T2Space A := bruhatSchwartz_t2
  letI : T2Space R := (positiveRealExponentialDecay_nuclear.{u} I hI).1
  have hf := positiveRealExponentialDecay_frechet I hInt hI
  let b : I := ⟨hI.choose, hI.choose_spec⟩
  let hrad := exists_bounded_radialEvaluations I b
  let p := hrad.choose
  let e := hrad.choose_spec.choose
  have hp := hrad.choose_spec.choose_spec.1
  have he := hrad.choose_spec.choose_spec.2.1
  have hsep := hrad.choose_spec.choose_spec.2.2
  let hst := exists_angularStage_of_bounded_decaySlices I e p hp he S hS
  let q := hst.choose
  have hq := hst.choose_spec
  let hret := exists_bruhatSchwartzStage_retraction q
  let L := hret.choose
  have hL := hret.choose_spec
  let i : q.val.Space →L[ℂ] A := q.val.inclusionCLM
  let D := projectiveTensorModuleStructure A R
  let J := completedProjectiveTensor_mapLeft (R := R) i
  let P := completedProjectiveTensor_mapLeft (R := R) L
  have hπ : projectiveTensorTopology A R = injectiveTensorTopology A R :=
    tensorTopologies_equal_of_flip ((positiveRealExponentialDecay_nuclear.{u} I hI).2.2 A)
  have hslices (z : D.Completed) (hz : z ∈ S) (j : ℝ) :
      completedProjectiveTensor_slice (A := A) (e j) z ∈ range i := by
    simpa only [decayTensor_angularSlice, i, q, A, R, D] using hq j z hz
  have hfix (z : D.Completed) (hz : z ∈ S) : J (P z) = z := by
    letI : IsTopologicalAddGroup R := hf.choose
    letI : UniformSpace R := IsTopologicalAddGroup.rightUniformSpace R
    letI : IsUniformAddGroup R := isUniformAddGroup_of_addCommGroup
    letI : CompleteSpace R := hf.choose_spec.2.2
    letI : ContinuousSMul ℂ R := (PolynormableSpace.withSeminorms ℂ R).continuousSMul
    exact completedProjectiveTensor_retract_of_slices (A := A) (B := q.val.Space) (R := R)
      e hsep hπ i L hL z (hslices z hz)
  refine ⟨q, P '' S, hS.image P, ?_⟩
  change J '' (P '' S) = S
  apply Set.Subset.antisymm
  · intro z
    rintro ⟨y, ⟨x, hx, hxy⟩, hyz⟩
    have he : J (P x) = z := (congrArg J hxy).trans hyz
    exact ((hfix x hx).symm.trans he) ▸ hx
  · intro z hz
    have hi : J (P z) ∈ J '' (P '' S) := Set.mem_image_of_mem J (Set.mem_image_of_mem P hz)
    exact hfix z hz ▸ hi

end
end Masullo
