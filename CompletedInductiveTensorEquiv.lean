import StrictInductiveTensorStages

open scoped TensorProduct

namespace Masullo
noncomputable section

variable {A B R S : Type*}
  [AddCommGroup A] [Module ℂ A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [AddCommGroup B] [Module ℂ B] [TopologicalSpace B] [IsTopologicalAddGroup B]
  [AddCommGroup R] [Module ℂ R] [TopologicalSpace R] [IsTopologicalAddGroup R]
  [AddCommGroup S] [Module ℂ S] [TopologicalSpace S] [IsTopologicalAddGroup S]

/-- Tensoring two continuous linear equivalences gives a continuous linear
equivalence on the completed inductive tensor products. -/
def completedInductiveTensor_congr (j : A ≃L[ℂ] B) (k : R ≃L[ℂ] S) :
    (inductiveTensorModuleStructure A R).Completed ≃L[ℂ]
      (inductiveTensorModuleStructure B S).Completed := by
  let f := completedInductiveTensor_map j.toContinuousLinearMap k.toContinuousLinearMap
  let g := completedInductiveTensor_map j.symm.toContinuousLinearMap k.symm.toContinuousLinearMap
  have hj : j.toContinuousLinearMap.comp j.symm.toContinuousLinearMap = .id ℂ B :=
    ContinuousLinearMap.ext j.apply_symm_apply
  have hk : k.toContinuousLinearMap.comp k.symm.toContinuousLinearMap = .id ℂ S :=
    ContinuousLinearMap.ext k.apply_symm_apply
  have hj' : j.symm.toContinuousLinearMap.comp j.toContinuousLinearMap = .id ℂ A :=
    ContinuousLinearMap.ext j.symm_apply_apply
  have hk' : k.symm.toContinuousLinearMap.comp k.toContinuousLinearMap = .id ℂ R :=
    ContinuousLinearMap.ext k.symm_apply_apply
  have h₁ : f.comp g = .id ℂ (inductiveTensorModuleStructure B S).Completed := by
    simp only [f, g, completedInductiveTensor_map_comp, hj, hk, completedInductiveTensor_map_id]
  have h₂ : g.comp f = .id ℂ (inductiveTensorModuleStructure A R).Completed := by
    simp only [f, g, completedInductiveTensor_map_comp, hj', hk', completedInductiveTensor_map_id]
  exact ContinuousLinearEquiv.equivOfInverse' f g h₁ h₂

@[simp]
theorem completedInductiveTensor_congr_tmul (j : A ≃L[ℂ] B) (k : R ≃L[ℂ] S) (a : A) (r : R) :
    completedInductiveTensor_congr j k ((inductiveTensorModuleStructure A R).incl (a ⊗ₜ[ℂ] r)) =
      (inductiveTensorModuleStructure B S).incl (j a ⊗ₜ[ℂ] k r) :=
  completedInductiveTensor_map_tmul j.toContinuousLinearMap k.toContinuousLinearMap a r

/-- A pair of scalar evaluations extends to a continuous evaluation on the
completed inductive tensor. -/
theorem exists_completedInductiveTensor_pair (j : A →L[ℂ] ℂ) (k : R →L[ℂ] ℂ) :
    ∃ E : (inductiveTensorModuleStructure A R).Completed →L[ℂ] ℂ,
      ∀ a r, E ((inductiveTensorModuleStructure A R).incl (a ⊗ₜ[ℂ] r)) = j a * k r := by
  let b : A →ₗ[ℂ] R →ₗ[ℂ] ℂ := (LinearMap.mul ℂ ℂ).compl₁₂ j.toLinearMap k.toLinearMap
  letI : TopologicalSpace (A ⊗[ℂ] R) := inductiveTensorTopology A R
  have hb : Continuous (TensorProduct.lift b) := by
    apply (continuous_inductiveTensor_lift_iff b).mpr
    exact ⟨fun r => j.continuous.mul_const (k r), fun a => k.continuous.const_mul (j a)⟩
  obtain ⟨E, hE⟩ := (inductiveTensorModuleStructure A R).exists_continuousLinearMap_extend
    (⟨TensorProduct.lift b, hb⟩ : A ⊗[ℂ] R →L[ℂ] ℂ)
  exact ⟨E, fun a r => (hE _).trans (TensorProduct.lift.tmul (f' := b) a r)⟩

end
end Masullo
