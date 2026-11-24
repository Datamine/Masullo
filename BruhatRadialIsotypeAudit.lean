import RiemannMasullo.AppD_SchwartzBruhat.Sec2b

/-! Run with `lake env lean` in original revision
`cb3e092484c0e94d115634ce9f202433bdbd17be` on Lean 4.36.0. -/

open Function Set Topology UniformSpace

namespace Masullo

attribute [local instance] uniformContinuousConstSMul_of_continuousConstSMul

/-- The uniformity pulled back through a dense linear map to a complete Hausdorff
space realizes that space as the completion. -/
theorem completion_induced_linearEquiv
    {X Y : Type*} [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y] [UniformSpace Y] [IsUniformAddGroup Y]
    [ContinuousConstSMul ℂ Y] [T2Space Y] [CompleteSpace Y]
    (f : X →ₗ[ℂ] Y) (hd : DenseRange f) :
    let : UniformSpace X := UniformSpace.comap f inferInstance
    let : IsUniformAddGroup X := IsUniformAddGroup.comap f.toAddMonoidHom
    let : ContinuousConstSMul ℂ X := ⟨fun c =>
      continuous_induced_rng.mpr ((continuous_const_smul c).comp continuous_induced_dom |>.congr
        fun x => (f.map_smul c x).symm)⟩
    ∃ e : Completion X ≃L[ℂ] Y, ∀ x : X, e (x : Completion X) = f x := by
  let : UniformSpace X := UniformSpace.comap f inferInstance
  let : IsUniformAddGroup X := IsUniformAddGroup.comap f.toAddMonoidHom
  let : ContinuousConstSMul ℂ X := ⟨fun c =>
    continuous_induced_rng.mpr ((continuous_const_smul c).comp continuous_induced_dom |>.congr
      fun x => (f.map_smul c x).symm)⟩
  let F : X →L[ℂ] Y := ⟨f, continuous_induced_dom⟩
  have hu : IsUniformInducing F := ⟨rfl⟩
  have he : IsUniformInducing F.fromCompletion :=
    Completion.isUniformInducing_extension hu
  have hd' : DenseRange F.fromCompletion := hd.mono (by
    rintro _ ⟨x, rfl⟩
    exact ⟨(x : Completion X), F.fromCompletion_apply_coe x⟩)
  have hs : Surjective F.fromCompletion :=
    range_eq_univ.mp (he.isComplete_range.isClosed.closure_eq ▸ hd'.closure_range)
  let e := LinearEquiv.ofBijective F.fromCompletion.toLinearMap ⟨he.isInducing.injective, hs⟩
  exact ⟨{e with continuous_toFun := F.fromCompletion.continuous
                 continuous_invFun := he.isInducing.continuous_iff.mpr
                   (continuous_id.congr fun x ↦ (e.apply_symm_apply x).symm) },
         F.fromCompletion_apply_coe⟩

#print axioms completion_induced_linearEquiv
#print axioms RiemannMasullo.schwartzBruhat_modulation_tensor
#print axioms RiemannMasullo.schwartzBruhat_modulation_isotype_completion

end Masullo
