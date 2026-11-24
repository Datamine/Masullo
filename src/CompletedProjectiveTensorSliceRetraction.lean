import CompletedProjectiveTensorSliceSeparation

open Function Set Topology UniformSpace
open scoped TensorProduct

namespace Masullo

noncomputable section

variable {A B R : Type*}
  [AddCommGroup A] [Module ℂ A] [UniformSpace A] [IsUniformAddGroup A]
  [ContinuousSMul ℂ A] [PolynormableSpace ℂ A] [CompleteSpace A] [T2Space A]
  [AddCommGroup B] [Module ℂ B] [TopologicalSpace B] [PolynormableSpace ℂ B]
  [AddCommGroup R] [Module ℂ R] [UniformSpace R] [IsUniformAddGroup R]
  [ContinuousSMul ℂ R] [PolynormableSpace ℂ R] [CompleteSpace R] [T2Space R]

/-- If every separating slice of a tensor belongs to a complemented subspace
of the first factor, the induced tensor projection fixes the tensor. -/
theorem completedProjectiveTensor_retract_of_slices {J : Type*}
    (e : J → R →L[ℂ] ℂ) (he : Injective (fun r j => e j r))
    (hπ : projectiveTensorTopology A R = injectiveTensorTopology A R)
    (i : B →L[ℂ] A) (r : A →L[ℂ] B) (hr : LeftInverse r i)
    (w : (projectiveTensorModuleStructure A R).Completed)
    (hw : ∀ j, completedProjectiveTensor_slice (e j) w ∈ range i) :
    completedProjectiveTensor_mapLeft (R := R) i
      (completedProjectiveTensor_mapLeft (R := R) r w) = w := by
  let D := projectiveTensorModuleStructure A R
  let X := A ⊗[ℂ] R
  letI : UniformSpace X := D.uniformSpace
  letI : IsUniformAddGroup X := D.uniformGroup
  letI : IsUniformAddGroup D.Completed := Completion.isUniformAddGroup
  letI : T0Space D.Completed := Completion.t0Space X
  let I := completedProjectiveTensor_mapLeft (R := R) i
  let P := completedProjectiveTensor_mapLeft (R := R) r
  let F := completedProjectiveTensor_mapLeft (R := R) (i.comp r)
  have hcomp : I.comp P = F := by
    apply completedProjectiveTensor_ext
    intro a b
    simp only [I, P, F, ContinuousLinearMap.comp_apply, completedProjectiveTensor_mapLeft_tmul]
  apply sub_eq_zero.mp
  apply completedProjectiveTensor_eq_zero_of_slices e he hπ
  intro j
  have hIP : I (P w) = F w := DFunLike.congr_fun hcomp w
  change completedProjectiveTensor_slice (e j) (I (P w) - w) = (0 : A)
  rw [hIP, map_sub, sub_eq_zero]
  have h := DFunLike.congr_fun (completedProjectiveTensor_slice_mapLeft (i.comp r) (e j)) w
  refine h.trans ?_
  obtain ⟨b, hb⟩ := hw j
  change i (r (completedProjectiveTensor_slice (e j) w)) = completedProjectiveTensor_slice (e j) w
  rw [← hb, hr b]

end
end Masullo
