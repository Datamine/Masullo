import InductiveTensorTopology

open Function Topology UniformSpace
open scoped TensorProduct

namespace Masullo

noncomputable section

/-- Continuous linear maps out of the completed projective tensor product
are determined by their values on elementary tensors. -/
theorem completedProjectiveTensor_ext
    {A R V : Type*} [AddCommGroup A] [Module ℂ A] [TopologicalSpace A]
    [AddCommGroup R] [Module ℂ R] [TopologicalSpace R]
    [AddCommGroup V] [Module ℂ V] [TopologicalSpace V] [T2Space V]
    {F G : (projectiveTensorModuleStructure A R).Completed →L[ℂ] V}
    (h : ∀ a r, F ((projectiveTensorModuleStructure A R).incl (a ⊗ₜ[ℂ] r)) =
      G ((projectiveTensorModuleStructure A R).incl (a ⊗ₜ[ℂ] r))) : F = G :=
  (projectiveTensorModuleStructure A R).continuousLinearMap_ext_on_tmul h

section FactorMaps

variable {A B R : Type*}
  [AddCommGroup A] [Module ℂ A] [TopologicalSpace A] [PolynormableSpace ℂ A]
  [AddCommGroup B] [Module ℂ B] [TopologicalSpace B] [PolynormableSpace ℂ B]
  [AddCommGroup R] [Module ℂ R] [TopologicalSpace R] [PolynormableSpace ℂ R]

/-- A change of the angular factor extends continuously to the projective completion. -/
def completedProjectiveTensor_mapLeft (j : A →L[ℂ] B) :
    (projectiveTensorModuleStructure A R).Completed →L[ℂ]
      (projectiveTensorModuleStructure B R).Completed := by
  let D := projectiveTensorModuleStructure A R
  let P := projectiveTensorModuleStructure B R
  let X := A ⊗[ℂ] R
  let Y := B ⊗[ℂ] R
  letI : UniformSpace X := D.uniformSpace
  letI : UniformSpace Y := P.uniformSpace
  letI : IsUniformAddGroup X := D.uniformGroup
  letI : IsUniformAddGroup Y := P.uniformGroup
  letI : UniformContinuousConstSMul ℂ X := D.uniformConstSmul
  letI : UniformContinuousConstSMul ℂ Y := P.uniformConstSmul
  exact (⟨TensorProduct.map j.toLinearMap LinearMap.id,
    projectiveTensor_map_continuous j (ContinuousLinearMap.id ℂ R)⟩ : X →L[ℂ] Y).completion

@[simp]
theorem completedProjectiveTensor_mapLeft_tmul (j : A →L[ℂ] B) (a : A) (r : R) :
    completedProjectiveTensor_mapLeft j
        ((projectiveTensorModuleStructure A R).incl (a ⊗ₜ[ℂ] r)) =
      (projectiveTensorModuleStructure B R).incl (j a ⊗ₜ[ℂ] r) := by
  let D := projectiveTensorModuleStructure A R
  let P := projectiveTensorModuleStructure B R
  let X := A ⊗[ℂ] R
  let Y := B ⊗[ℂ] R
  letI : UniformSpace X := D.uniformSpace
  letI : UniformSpace Y := P.uniformSpace
  letI : IsUniformAddGroup X := D.uniformGroup
  letI : IsUniformAddGroup Y := P.uniformGroup
  letI : UniformContinuousConstSMul ℂ X := D.uniformConstSmul
  letI : UniformContinuousConstSMul ℂ Y := P.uniformConstSmul
  let L : X →L[ℂ] Y := ⟨TensorProduct.map j.toLinearMap LinearMap.id,
    projectiveTensor_map_continuous j (ContinuousLinearMap.id ℂ R)⟩
  change L.completion (D.incl (a ⊗ₜ[ℂ] r)) = P.incl (j a ⊗ₜ[ℂ] r)
  exact (L.completion_apply_coe (a ⊗ₜ[ℂ] r)).trans
    (congrArg P.incl (TensorProduct.map_tmul j.toLinearMap LinearMap.id a r))

/-- A retraction of the left factor induces a retraction on the
completed projective tensor product. -/
theorem completedProjectiveTensor_mapLeft_leftInverse
    (j : A →L[ℂ] B) (r : B →L[ℂ] A) (hr : LeftInverse r j) :
    LeftInverse
      (completedProjectiveTensor_mapLeft (R := R) r)
      (completedProjectiveTensor_mapLeft (R := R) j) := by
  let X := A ⊗[ℂ] R
  let D := projectiveTensorModuleStructure A R
  letI : UniformSpace X := D.uniformSpace
  letI : IsUniformAddGroup X := D.uniformGroup
  letI : IsUniformAddGroup D.Completed := Completion.isUniformAddGroup
  letI : T0Space D.Completed := Completion.t0Space X
  let J := completedProjectiveTensor_mapLeft (R := R) j
  let P := completedProjectiveTensor_mapLeft (R := R) r
  have h : P.comp J = ContinuousLinearMap.id ℂ D.Completed := by
    apply D.continuousLinearMap_ext_on_tmul
    intro a b
    change P (J (D.incl (a ⊗ₜ[ℂ] b))) = D.incl (a ⊗ₜ[ℂ] b)
    dsimp only [P, J]
    rw [completedProjectiveTensor_mapLeft_tmul, completedProjectiveTensor_mapLeft_tmul, hr]
  exact DFunLike.congr_fun h

end FactorMaps

/-- The extended multiplication maps commute with an angular-factor map
whenever their scalar evaluations agree on elementary tensors. -/
theorem completedProjectiveTensor_mapLeft_natural
    {A B R Y Z G : Type*}
    [AddCommGroup A] [Module ℂ A] [TopologicalSpace A] [PolynormableSpace ℂ A]
    [AddCommGroup B] [Module ℂ B] [TopologicalSpace B] [PolynormableSpace ℂ B]
    [AddCommGroup R] [Module ℂ R] [TopologicalSpace R] [PolynormableSpace ℂ R]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]
    [AddCommGroup Z] [Module ℂ Z] [TopologicalSpace Z]
    (j : A →L[ℂ] B) (k : Y →L[ℂ] Z)
    (F : (projectiveTensorModuleStructure A R).Completed →L[ℂ] Y)
    (F' : (projectiveTensorModuleStructure B R).Completed →L[ℂ] Z)
    (e : G → Z →L[ℂ] ℂ) (he : Function.Injective (fun z g => e g z))
    (h : ∀ a r g, e g (k (F ((projectiveTensorModuleStructure A R).incl (a ⊗ₜ[ℂ] r)))) =
      e g (F' ((projectiveTensorModuleStructure B R).incl (j a ⊗ₜ[ℂ] r)))) :
    k.comp F = F'.comp (completedProjectiveTensor_mapLeft j) := by
  have hcomp (g : G) : (e g).comp (k.comp F) =
      (e g).comp (F'.comp (completedProjectiveTensor_mapLeft j)) := by
    apply completedProjectiveTensor_ext
    intro a r
    simp only [ContinuousLinearMap.comp_apply, completedProjectiveTensor_mapLeft_tmul]
    exact h a r g
  apply ContinuousLinearMap.ext
  intro z
  apply he
  funext g
  exact DFunLike.congr_fun (hcomp g) z

end
end Masullo
