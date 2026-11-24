import StrictInductiveTensorStages
import CompletedTensorFlip

open Function Set Topology
open scoped TensorProduct

namespace Masullo

noncomputable section

section ToGlobal

variable {A B R : Type*}
  [AddCommGroup A] [Module ℂ A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [AddCommGroup B] [Module ℂ B] [TopologicalSpace B] [IsTopologicalAddGroup B]
  [AddCommGroup R] [Module ℂ R] [TopologicalSpace R] [IsTopologicalAddGroup R]

/-- A stage with equal tensor topologies can be mapped to the ambient
inductive tensor from its projective completion, with the same range. -/
theorem exists_projectiveStage_to_inductiveTensor
    (u : B →L[ℂ] A)
    (h : inductiveTensorTopology B R = projectiveTensorTopology B R) :
    let T := inductiveTensorModuleStructure A R
    let P := projectiveTensorModuleStructure B R
    let U := completedInductiveTensor_map u (ContinuousLinearMap.id ℂ R)
    ∃ J : P.Completed →L[ℂ] T.Completed,
      (∀ (x : B) (y : R), J (P.incl (x ⊗ₜ[ℂ] y)) = T.incl (u x ⊗ₜ[ℂ] y)) ∧
      range J = range U := by
  let D := inductiveTensorModuleStructure B R
  let P := projectiveTensorModuleStructure B R
  let T := inductiveTensorModuleStructure A R
  let U := completedInductiveTensor_map u (ContinuousLinearMap.id ℂ R)
  let V : D.Completed ≃L[ℂ] P.Completed := TopologicalModuleStructure.completionEquiv h
  let J := U.comp V.symm.toContinuousLinearMap
  refine ⟨J, ?_, ?_⟩
  · intro a r
    have he : V (D.incl (a ⊗ₜ[ℂ] r)) = P.incl (a ⊗ₜ[ℂ] r) :=
      TopologicalModuleStructure.completionEquiv_incl h _
    change U (V.symm (P.incl (a ⊗ₜ[ℂ] r))) = _
    rw [← he, V.symm_apply_apply]
    exact completedInductiveTensor_map_tmul u (ContinuousLinearMap.id ℂ R) a r
  · change range (U ∘ V.symm) = range U
    rw [range_comp, V.symm.surjective.range_eq, image_univ]

end ToGlobal

section Flip

variable {A R : Type*}
  [AddCommGroup A] [Module ℂ A] [TopologicalSpace A]
  [AddCommGroup R] [Module ℂ R] [TopologicalSpace R]

/-- Equal projective and inductive topologies identify the projective stage
with the completed inductive stage after interchanging its factors. -/
theorem exists_completedInductiveTensor_flip_toProjective
    (h : inductiveTensorTopology A R = projectiveTensorTopology A R) :
    let D := inductiveTensorModuleStructure R A
    let P := projectiveTensorModuleStructure A R
    ∃ V : D.Completed ≃L[ℂ] P.Completed,
      ∀ (r : R) (a : A), V (D.incl (r ⊗ₜ[ℂ] a)) = P.incl (a ⊗ₜ[ℂ] r) := by
  let D := inductiveTensorModuleStructure R A
  let T := inductiveTensorModuleStructure A R
  let P := projectiveTensorModuleStructure A R
  obtain ⟨U, hU⟩ := exists_completedInductiveTensorFlip (A := R) (R := A)
  let W : T.Completed ≃L[ℂ] P.Completed := TopologicalModuleStructure.completionEquiv h
  refine ⟨U.trans W, fun r a => ?_⟩
  have he : U (D.incl (r ⊗ₜ[ℂ] a)) = T.incl (a ⊗ₜ[ℂ] r) :=
    (hU _).trans (congrArg T.incl (TensorProduct.comm_tmul ℂ R A r a))
  exact (congrArg W he).trans (TopologicalModuleStructure.completionEquiv_incl h _)

end Flip

end
end Masullo
