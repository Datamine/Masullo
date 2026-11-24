import InductiveTensorTopology

open Topology UniformSpace
open scoped TensorProduct

namespace Masullo

noncomputable section

variable {A R : Type*} [AddCommGroup A] [Module ℂ A] [TopologicalSpace A]
  [AddCommGroup R] [Module ℂ R] [TopologicalSpace R]

omit [TopologicalSpace A] [TopologicalSpace R] in
private theorem exists_completedTensorFlip
    (D : TopologicalModuleStructure (A ⊗[ℂ] R)) (P : TopologicalModuleStructure (R ⊗[ℂ] A))
    (hc : Continuous[D.topology, P.topology] (TensorProduct.comm ℂ A R))
    (hc' : Continuous[P.topology, D.topology] (TensorProduct.comm ℂ R A)) :
    ∃ F : D.Completed ≃L[ℂ] P.Completed,
      ∀ z, F (D.incl z) = P.incl (TensorProduct.comm ℂ A R z) := by
  let X := A ⊗[ℂ] R
  let Y := R ⊗[ℂ] A
  letI : UniformSpace X := D.uniformSpace
  letI : UniformSpace Y := P.uniformSpace
  letI : IsUniformAddGroup X := D.uniformGroup
  letI : IsUniformAddGroup Y := P.uniformGroup
  letI : UniformContinuousConstSMul ℂ X := D.uniformConstSmul
  letI : UniformContinuousConstSMul ℂ Y := P.uniformConstSmul
  letI : IsUniformAddGroup D.Completed := Completion.isUniformAddGroup
  letI : IsUniformAddGroup P.Completed := Completion.isUniformAddGroup
  letI : T0Space D.Completed := Completion.t0Space X
  letI : T0Space P.Completed := Completion.t0Space Y
  let f : X →L[ℂ] Y := ⟨(TensorProduct.comm ℂ A R).toLinearMap, hc⟩
  let g : Y →L[ℂ] X := ⟨(TensorProduct.comm ℂ R A).toLinearMap, hc'⟩
  let F := f.completion
  let G := g.completion
  have hf (z : X) : F (D.incl z) = P.incl (TensorProduct.comm ℂ A R z) := f.completion_apply_coe z
  have hg (z : Y) : G (P.incl z) = D.incl (TensorProduct.comm ℂ R A z) := g.completion_apply_coe z
  have hl : G.comp F = ContinuousLinearMap.id ℂ _ := by
    apply D.continuousLinearMap_ext_on_tmul
    intro a r
    change G (F (D.incl (a ⊗ₜ[ℂ] r))) = D.incl (a ⊗ₜ[ℂ] r)
    rw [hf, hg, TensorProduct.comm_tmul, TensorProduct.comm_tmul]
  have hr : F.comp G = ContinuousLinearMap.id ℂ _ := by
    apply P.continuousLinearMap_ext_on_tmul
    intro r a
    change F (G (P.incl (r ⊗ₜ[ℂ] a))) = P.incl (r ⊗ₜ[ℂ] a)
    rw [hg, hf, TensorProduct.comm_tmul, TensorProduct.comm_tmul]
  exact ⟨ContinuousLinearEquiv.equivOfInverse F G (DFunLike.congr_fun hl) (DFunLike.congr_fun hr), hf⟩

private theorem continuous_inductiveTensor_flip :
    Continuous[inductiveTensorTopology A R, inductiveTensorTopology R A]
      (TensorProduct.comm ℂ A R) := by
  letI : TopologicalSpace (A ⊗[ℂ] R) := inductiveTensorTopology A R
  letI : TopologicalSpace (R ⊗[ℂ] A) := inductiveTensorTopology R A
  let WA := inductiveTensor_withSeminorms (E := A) (F := R)
  let WR := inductiveTensor_withSeminorms (E := R) (F := A)
  letI : IsTopologicalAddGroup (A ⊗[ℂ] R) := WA.topologicalAddGroup
  apply (WR.continuous_iff_continuous_comp (TensorProduct.comm ℂ A R).toLinearMap).mpr
  intro q
  let Q : InductiveTensorTest A R :=
    { tensor := q.tensor.comp (TensorProduct.comm ℂ A R).toLinearMap
      first := fun r => (q.second r).congr (fun a => by simp)
      second := fun a => (q.first a).congr (fun r => by simp) }
  exact WA.continuous_seminorm Q

theorem continuous_projectiveTensor_flip :
    Continuous[projectiveTensorTopology A R, projectiveTensorTopology R A]
      (TensorProduct.comm ℂ A R) := by
  letI : TopologicalSpace (A ⊗[ℂ] R) := projectiveTensorTopology A R
  letI : TopologicalSpace (R ⊗[ℂ] A) := projectiveTensorTopology R A
  let WA := projectiveTensor_withSeminorms (E := A) (F := R)
  let WR := projectiveTensor_withSeminorms (E := R) (F := A)
  letI : IsTopologicalAddGroup (A ⊗[ℂ] R) := WA.topologicalAddGroup
  apply (WR.continuous_iff_continuous_comp (TensorProduct.comm ℂ A R).toLinearMap).mpr
  intro q
  let Q : ProjectiveTensorTest A R :=
    { tensor := q.tensor.comp (TensorProduct.comm ℂ A R).toLinearMap
      first := q.second
      second := q.first
      first_continuous := q.second_continuous
      second_continuous := q.first_continuous
      bound := fun a r => by simpa only [Seminorm.comp_apply, LinearEquiv.coe_coe,
        TensorProduct.comm_tmul, mul_comm] using q.bound r a }
  exact WA.continuous_seminorm Q

/-- Interchanging the two factors preserves the completed inductive tensor topology. -/
theorem exists_completedInductiveTensorFlip :
    ∃ F : (inductiveTensorModuleStructure A R).Completed ≃L[ℂ]
        (inductiveTensorModuleStructure R A).Completed,
      ∀ z, F ((inductiveTensorModuleStructure A R).incl z) =
        (inductiveTensorModuleStructure R A).incl (TensorProduct.comm ℂ A R z) :=
  exists_completedTensorFlip _ _ continuous_inductiveTensor_flip continuous_inductiveTensor_flip

/-- Interchanging the two factors preserves the completed projective tensor topology. -/
theorem exists_completedProjectiveTensorFlip :
    ∃ F : (projectiveTensorModuleStructure A R).Completed ≃L[ℂ]
        (projectiveTensorModuleStructure R A).Completed,
      ∀ z, F ((projectiveTensorModuleStructure A R).incl z) =
        (projectiveTensorModuleStructure R A).incl (TensorProduct.comm ℂ A R z) :=
  exists_completedTensorFlip _ _ continuous_projectiveTensor_flip continuous_projectiveTensor_flip

end
end Masullo
