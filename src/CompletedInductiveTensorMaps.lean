import InductiveTensorTopology

open Topology UniformSpace
open scoped TensorProduct

namespace Masullo

noncomputable section

variable {A B R S : Type*}
  [AddCommGroup A] [Module ℂ A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [AddCommGroup B] [Module ℂ B] [TopologicalSpace B] [IsTopologicalAddGroup B]
  [AddCommGroup R] [Module ℂ R] [TopologicalSpace R] [IsTopologicalAddGroup R]
  [AddCommGroup S] [Module ℂ S] [TopologicalSpace S] [IsTopologicalAddGroup S]

private def inductiveTensorMap (j : A →L[ℂ] B) (k : R →L[ℂ] S) :
    letI : TopologicalSpace (A ⊗[ℂ] R) := inductiveTensorTopology A R
    letI : TopologicalSpace (B ⊗[ℂ] S) := inductiveTensorTopology B S
    (A ⊗[ℂ] R) →L[ℂ] (B ⊗[ℂ] S) := by
  letI : TopologicalSpace (A ⊗[ℂ] R) := inductiveTensorTopology A R
  letI : TopologicalSpace (B ⊗[ℂ] S) := inductiveTensorTopology B S
  let W := inductiveTensor_withSeminorms (E := B) (F := S)
  letI : PolynormableSpace ℂ (B ⊗[ℂ] S) := W.toPolynormableSpace
  let L := (TensorProduct.mk ℂ B S).compl₁₂ j.toLinearMap k.toLinearMap
  have hj (s : S) : Continuous ((TensorProduct.mk ℂ B S).flip s) :=
    (W.continuous_iff_continuous_comp ((TensorProduct.mk ℂ B S).flip s)).mpr (fun q => q.first s)
  have hk (b : B) : Continuous (TensorProduct.mk ℂ B S b) :=
    (W.continuous_iff_continuous_comp (TensorProduct.mk ℂ B S b)).mpr (fun q => q.second b)
  refine ⟨TensorProduct.lift L, (continuous_inductiveTensor_lift_iff L).mpr ⟨?_, ?_⟩⟩
  · intro r
    exact (hj (k r)).comp j.continuous
  · intro a
    exact (hk (j a)).comp k.continuous

/-- Continuous linear maps of the factors act on the completed inductive tensors. -/
def completedInductiveTensor_map (j : A →L[ℂ] B) (k : R →L[ℂ] S) :
    (inductiveTensorModuleStructure A R).Completed →L[ℂ]
      (inductiveTensorModuleStructure B S).Completed := by
  let D := inductiveTensorModuleStructure A R
  let P := inductiveTensorModuleStructure B S
  letI : UniformSpace (A ⊗[ℂ] R) := D.uniformSpace
  letI : UniformSpace (B ⊗[ℂ] S) := P.uniformSpace
  letI : IsUniformAddGroup (A ⊗[ℂ] R) := D.uniformGroup
  letI : IsUniformAddGroup (B ⊗[ℂ] S) := P.uniformGroup
  letI : UniformContinuousConstSMul ℂ (A ⊗[ℂ] R) := D.uniformConstSmul
  letI : UniformContinuousConstSMul ℂ (B ⊗[ℂ] S) := P.uniformConstSmul
  exact (inductiveTensorMap j k).completion

@[simp]
theorem completedInductiveTensor_map_tmul (j : A →L[ℂ] B) (k : R →L[ℂ] S) (a : A) (r : R) :
    completedInductiveTensor_map j k
        ((inductiveTensorModuleStructure A R).incl (a ⊗ₜ[ℂ] r)) =
      (inductiveTensorModuleStructure B S).incl (j a ⊗ₜ[ℂ] k r) := by
  let D := inductiveTensorModuleStructure A R
  let P := inductiveTensorModuleStructure B S
  letI : UniformSpace (A ⊗[ℂ] R) := D.uniformSpace
  letI : UniformSpace (B ⊗[ℂ] S) := P.uniformSpace
  letI : IsUniformAddGroup (A ⊗[ℂ] R) := D.uniformGroup
  letI : IsUniformAddGroup (B ⊗[ℂ] S) := P.uniformGroup
  letI : UniformContinuousConstSMul ℂ (A ⊗[ℂ] R) := D.uniformConstSmul
  letI : UniformContinuousConstSMul ℂ (B ⊗[ℂ] S) := P.uniformConstSmul
  have h : inductiveTensorMap j k (a ⊗ₜ[ℂ] r) = j a ⊗ₜ[ℂ] k r :=
    TensorProduct.lift.tmul (f' := (TensorProduct.mk ℂ B S).compl₁₂ j.toLinearMap k.toLinearMap) a r
  exact ((inductiveTensorMap j k).completion_apply_coe (a ⊗ₜ[ℂ] r)).trans (congrArg P.incl h)

end
end Masullo
