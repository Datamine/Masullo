import ModulatedDecaySplitProducts
import InductiveTensorTopology

open Function Set Topology UniformSpace
open scoped TensorProduct

namespace Masullo

noncomputable section

private theorem exists_completedProjectiveLift
    {A R Y : Type*} [AddCommGroup A] [Module ℂ A] [TopologicalSpace A] [PolynormableSpace ℂ A]
    [AddCommGroup R] [Module ℂ R] [TopologicalSpace R] [PolynormableSpace ℂ R]
    [UniformSpace Y] [AddCommGroup Y] [Module ℂ Y] [IsUniformAddGroup Y] [CompleteSpace Y]
    [T2Space Y] [ContinuousConstSMul ℂ Y] [PolynormableSpace ℂ Y]
    (B : A →ₗ[ℂ] R →ₗ[ℂ] Y) (hB : Continuous (fun z : A × R => B z.1 z.2)) :
    ∃ F : (projectiveTensorModuleStructure A R).Completed →L[ℂ] Y,
      ∀ h f, F ((projectiveTensorModuleStructure A R).incl (h ⊗ₜ[ℂ] f)) = B h f := by
  let D := projectiveTensorModuleStructure A R
  letI : TopologicalSpace (A ⊗[ℂ] R) := D.topology
  let T : (A ⊗[ℂ] R) →L[ℂ] Y := ⟨TensorProduct.lift B, continuous_projectiveTensor_lift B hB⟩
  obtain ⟨F, hF⟩ := D.exists_continuousLinearMap_extend T
  exact ⟨F, fun h f => (hF (h ⊗ₜ[ℂ] f)).trans (TensorProduct.lift.tmul h f)⟩

variable {G H : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G]
  [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H] [LocallyCompactSpace H]
  (m : G →ₜ* Multiplicative ℝ)

set_option maxHeartbeats 4200000 in
/-- The forward map from the completed projective tensor product realizes
pointwise multiplication on elementary tensors at the prescribed stage. -/
theorem exists_splitStage_completedTensorMap (hm : IsProperMap m) (α : G →ₜ* H)
    (p : WholeBruhatStage H) (q : WholeBruhatStage G)
    (hker : q.val.1.kernel ≤ p.val.1.kernel.comap α.toMonoidHom)
    (I : Set ℝ) (hI : I.Nonempty) (hInt : OrdConnected I) :
    ∃ F : (projectiveTensorModuleStructure p.val.Space (PositiveRealExponentialDecay I)).Completed
        →L[ℂ] WholeBruhatDecayStage m I q,
      ∀ (h : p.val.Space) (f : PositiveRealExponentialDecay I) (g : G),
        (F ((projectiveTensorModuleStructure p.val.Space (PositiveRealExponentialDecay I)).incl
          (h ⊗ₜ[ℂ] f))).val g = p.val.realize h (α g) * f.val (m g).toAdd := by
  let A := p.val.Space
  let R := PositiveRealExponentialDecay I
  let Y := WholeBruhatDecayStage m I q
  have hExists : ∃ B : A →ₗ[ℂ] R →ₗ[ℂ] Y,
      (∀ h f g, (B h f).val g = p.val.realize h (α g) * f.val (m g).toAdd) ∧
      Continuous (fun z : A × R => B z.1 z.2) :=
    exists_splitStageJointlyContinuous m hm α p q hker I hI hInt
  obtain ⟨B, hB, hc⟩ := hExists
  letI : PolynormableSpace ℂ R := (positiveRealExponentialDecay_frechet I hInt hI).choose_spec.1
  letI : UniformSpace Y := IsTopologicalAddGroup.rightUniformSpace Y
  letI : IsUniformAddGroup Y := isUniformAddGroup_of_addCommGroup
  letI : CompleteSpace Y := WholeBruhatDecayStage.complete m I hI q
  letI : T2Space q.val.Space := @elementarySchwartz_t2
    q.val.2.realDim q.val.2.torusDim q.val.2.latticeRank q.val.2.finiteFactor
    q.val.2.finiteGroup q.val.2.finiteTopology q.val.2.finiteDiscrete (Finite.of_fintype _)
  letI : T2Space Y := (WholeBruhatDecayStage.twistTuple_isClosedEmbedding m I hI q).isEmbedding.t2Space
  letI : ContinuousSMul ℂ Y := (PolynormableSpace.withSeminorms ℂ Y).continuousSMul
  let D := projectiveTensorModuleStructure A R
  have hLift : ∃ F : D.Completed →L[ℂ] Y,
      ∀ (h : A) (f : R), F (D.incl (h ⊗ₜ[ℂ] f)) = B h f :=
    exists_completedProjectiveLift (A := A) (R := R) (Y := Y) B hc
  exact hLift.imp fun F hF h f g =>
    (congrArg (fun y : Y => y.val g) (hF h f)).trans (hB h f g)

end

end Masullo
