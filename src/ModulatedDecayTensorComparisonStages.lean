import ModulatedDecayTensorBoundedStages
import ModulatedDecayProjectiveStageInclusion
import BruhatStageRetraction
import ExponentialDecayStructure

open Bornology Function Set Topology UniformSpace
open scoped TensorProduct

namespace Masullo

noncomputable section

variable {H : Type*} [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H]
  [T2Space H] [LocallyCompactSpace H] [SecondCountableTopology H]

omit [SecondCountableTopology H] in
set_option maxHeartbeats 1700000 in
/-- On a projective stage viewed in the inductive completion, the global
comparison is exactly the projective inclusion of that stage. -/
theorem comparison_comp_projectiveStageInclusion
    (p : WholeBruhatStage H) (I : Set ℝ)
    (J : (projectiveTensorModuleStructure p.val.Space (PositiveRealExponentialDecay I)).Completed
      →L[ℂ] (inductiveTensorModuleStructure (BruhatSchwartz H) (PositiveRealExponentialDecay I)).Completed)
    (hJ : ∀ (a : p.val.Space) (r : PositiveRealExponentialDecay I),
      J ((projectiveTensorModuleStructure p.val.Space (PositiveRealExponentialDecay I)).incl (a ⊗ₜ[ℂ] r)) =
        (inductiveTensorModuleStructure (BruhatSchwartz H) (PositiveRealExponentialDecay I)).incl
          (p.val.inclusionCLM a ⊗ₜ[ℂ] r)) :
    let A := BruhatSchwartz H
    let R := PositiveRealExponentialDecay I
    letI : IsTopologicalAddGroup A := (PolynormableSpace.withSeminorms ℂ A).topologicalAddGroup
    letI : IsTopologicalAddGroup R := (PolynormableSpace.withSeminorms ℂ R).topologicalAddGroup
    completedInductiveTensorComparison.comp J =
      completedProjectiveTensor_mapLeft (R := R) p.val.inclusionCLM := by
  dsimp only
  let A := BruhatSchwartz H
  let R := PositiveRealExponentialDecay I
  let P := projectiveTensorModuleStructure A R
  let D := inductiveTensorModuleStructure A R
  let X := A ⊗[ℂ] R
  letI : IsTopologicalAddGroup A := (PolynormableSpace.withSeminorms ℂ A).topologicalAddGroup
  letI : IsTopologicalAddGroup R := (PolynormableSpace.withSeminorms ℂ R).topologicalAddGroup
  let C := completedInductiveTensorComparison (E := A) (F := R)
  letI : UniformSpace X := P.uniformSpace
  letI : IsUniformAddGroup X := P.uniformGroup
  letI : IsUniformAddGroup P.Completed := Completion.isUniformAddGroup
  letI : T0Space P.Completed := Completion.t0Space X
  change C.comp J = _
  apply completedProjectiveTensor_ext
  intro a r
  have h : C (D.incl (p.val.inclusionCLM a ⊗ₜ[ℂ] r)) =
      P.incl (p.val.inclusionCLM a ⊗ₜ[ℂ] r) :=
    completedInductiveTensorComparison_incl (p.val.inclusionCLM a ⊗ₜ[ℂ] r)
  exact ((congrArg C (hJ a r)).trans h).trans
    (completedProjectiveTensor_mapLeft_tmul p.val.inclusionCLM a r).symm


/-- Every vector of the inductive completion is represented by a tensor in
a single angular stage, with the stage map agreeing with the algebraic inclusion. -/
def InductiveDecayTensorStageCoverage (I : Set ℝ) (H : Type*) [CommGroup H] [TopologicalSpace H]
    [IsTopologicalGroup H] [T2Space H] [LocallyCompactSpace H] : Prop :=
  ∀ w : (inductiveTensorModuleStructure (BruhatSchwartz H) (PositiveRealExponentialDecay I)).Completed,
    ∃ p : WholeBruhatStage H,
      ∃ J : (projectiveTensorModuleStructure p.val.Space (PositiveRealExponentialDecay I)).Completed
        →L[ℂ] (inductiveTensorModuleStructure (BruhatSchwartz H) (PositiveRealExponentialDecay I)).Completed,
        (∀ (a : p.val.Space) (r : PositiveRealExponentialDecay I),
          J ((projectiveTensorModuleStructure p.val.Space (PositiveRealExponentialDecay I)).incl
            (a ⊗ₜ[ℂ] r)) =
          (inductiveTensorModuleStructure (BruhatSchwartz H) (PositiveRealExponentialDecay I)).incl
            (p.val.inclusionCLM a ⊗ₜ[ℂ] r)) ∧ w ∈ range J

set_option maxHeartbeats 1700000 in
/-- Stage coverage and the complemented projective inclusions make the full
comparison injective. -/
theorem comparison_injective_of_stageCoverage (I : Set ℝ) (hcov : InductiveDecayTensorStageCoverage I H) :
    let A := BruhatSchwartz H
    let R := PositiveRealExponentialDecay I
    letI : IsTopologicalAddGroup A := (PolynormableSpace.withSeminorms ℂ A).topologicalAddGroup
    letI : IsTopologicalAddGroup R := (PolynormableSpace.withSeminorms ℂ R).topologicalAddGroup
    Injective (completedInductiveTensorComparison (E := A) (F := R)) := by
  dsimp only
  let A := BruhatSchwartz H
  let R := PositiveRealExponentialDecay I
  letI : IsTopologicalAddGroup A := (PolynormableSpace.withSeminorms ℂ A).topologicalAddGroup
  letI : IsTopologicalAddGroup R := (PolynormableSpace.withSeminorms ℂ R).topologicalAddGroup
  let C := completedInductiveTensorComparison (E := A) (F := R)
  change Injective C
  apply (injective_iff_map_eq_zero C).mpr
  intro w hw
  obtain ⟨q, J, hJ, z, hz⟩ := hcov w
  have hC : C.comp J = completedProjectiveTensor_mapLeft (R := R) q.val.inclusionCLM :=
    comparison_comp_projectiveStageInclusion q I J hJ
  have hzero : completedProjectiveTensor_mapLeft (R := R) q.val.inclusionCLM z = 0 :=
    (DFunLike.congr_fun hC z).symm.trans ((congrArg C hz).trans hw)
  obtain ⟨L, hL⟩ := exists_bruhatSchwartzStage_retraction q
  have hi : Injective (completedProjectiveTensor_mapLeft (R := R) q.val.inclusionCLM) :=
    (completedProjectiveTensor_mapLeft_leftInverse (R := R) q.val.inclusionCLM L hL).injective
  have he := hi (hzero.trans (map_zero (completedProjectiveTensor_mapLeft (R := R) q.val.inclusionCLM)).symm)
  exact hz.symm.trans ((congrArg J he).trans (map_zero J))

end
end Masullo
