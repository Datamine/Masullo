import CompletedProjectiveTensorSlices

open Filter Function Set Topology UniformSpace
open scoped TensorProduct PointwiseConvergenceCLM

namespace Masullo

noncomputable section

variable {A R : Type*} [AddCommGroup A] [Module ℂ A] [UniformSpace A] [IsUniformAddGroup A]
  [ContinuousSMul ℂ A] [PolynormableSpace ℂ A] [CompleteSpace A] [T2Space A]
  [AddCommGroup R] [Module ℂ R] [UniformSpace R] [IsUniformAddGroup R]
  [ContinuousSMul ℂ R] [PolynormableSpace ℂ R] [CompleteSpace R] [T2Space R]

omit [IsUniformAddGroup A] [ContinuousSMul ℂ A] [CompleteSpace A] [T2Space A] in
/-- Contraction against a continuous angular functional. -/
private theorem exists_leftSlice (ψ : A →L[ℂ] ℂ) :
    ∃ L : (projectiveTensorModuleStructure A R).Completed →L[ℂ] R,
      ∀ a r, L ((projectiveTensorModuleStructure A R).incl (a ⊗ₜ[ℂ] r)) = ψ a • r := by
  let D := projectiveTensorModuleStructure A R
  let X := A ⊗[ℂ] R
  letI : TopologicalSpace X := D.topology
  let B := (LinearMap.lsmul ℂ R).compl₁₂ ψ.toLinearMap LinearMap.id
  have hc : Continuous (fun z : A × R => B z.1 z.2) :=
    (ψ.continuous.comp continuous_fst).smul continuous_snd
  let L : X →L[ℂ] R := ⟨TensorProduct.lift B, continuous_projectiveTensor_lift B hc⟩
  obtain ⟨F, hF⟩ := D.exists_continuousLinearMap_extend L
  exact ⟨F, fun a r => (hF (a ⊗ₜ[ℂ] r)).trans (TensorProduct.lift.tmul a r)⟩

/-- If the projective and injective topologies agree, contractions along
a separating family of radial functionals determine the completed tensor. -/
theorem completedProjectiveTensor_eq_zero_of_slices {J : Type*}
    (e : J → R →L[ℂ] ℂ) (he : Injective (fun r j => e j r))
    (hπ : projectiveTensorTopology A R = injectiveTensorTopology A R)
    (w : (projectiveTensorModuleStructure A R).Completed)
    (hw : ∀ j, completedProjectiveTensor_slice (e j) w = (0 : A)) : w = 0 := by
  let D := projectiveTensorModuleStructure A R
  let X := A ⊗[ℂ] R
  letI : UniformSpace X := D.uniformSpace
  letI : IsUniformAddGroup X := D.uniformGroup
  letI : UniformContinuousConstSMul ℂ X := D.uniformConstSmul
  have hW : WithSeminorms (injectiveTensorSeminorm (E := A) (F := R)) := by
    change @WithSeminorms ℂ X _ _ _ _ _ (projectiveTensorTopology A R)
    rw [hπ]
    exact InjectiveTensorTools.injectiveTensor_withSeminorms
  have scalar_zero (ψ : A →L[ℂ] ℂ) (φ : R →L[ℂ] ℂ) :
      ψ (completedProjectiveTensor_slice φ w) = 0 := by
    obtain ⟨L, hL⟩ := exists_leftSlice (R := R) ψ
    have commute (f : R →L[ℂ] ℂ) :
        ψ.comp (completedProjectiveTensor_slice f) = f.comp L := by
      apply completedProjectiveTensor_ext
      intro a r
      simp only [ContinuousLinearMap.comp_apply, completedProjectiveTensor_slice_tmul,
        hL, map_smul, smul_eq_mul, mul_comm]
    have hLw : L w = 0 := by
      apply he
      funext j
      change e j (L w) = e j 0
      have hj := DFunLike.congr_fun (commute (e j)) w
      simpa only [ContinuousLinearMap.comp_apply, hw, map_zero] using hj.symm
    rw [← ContinuousLinearMap.comp_apply, commute, ContinuousLinearMap.comp_apply, hLw, map_zero]
  apply completion_eq_zero_of_generatingSeminorms _ hW
  intro I
  letI : CompactSpace I.1.forms := isCompact_iff_compactSpace.mp I.1.compact
  letI : CompactSpace I.2.forms := isCompact_iff_compactSpace.mp I.2.compact
  let P := tensorPairEvaluation I.1.forms I.2.forms
  have hPnorm : Continuous (fun t : X => ‖P t‖) := hW.continuous_seminorm I
  have hP : Continuous P := by
    refine continuous_of_tendsto_nhds_zero (G := X) P.toAddMonoidHom ?_
    rw [Metric.tendsto_nhds]
    intro ε hε
    have ht := (hPnorm.tendsto' 0 0 (by simp)).eventually (Iio_mem_nhds hε)
    filter_upwards [ht] with t ht
    simpa only [show P.toAddMonoidHom t = P t from rfl, dist_zero_right] using ht
  obtain ⟨L, hL⟩ := D.exists_continuousLinearMap_extend ⟨P, hP⟩
  have hLw : L w = 0 := by
    ext x
    let ev : C(I.1.forms × I.2.forms, ℂ) →L[ℂ] ℂ := ContinuousMap.evalCLM ℂ x
    let ψ : A →L[ℂ] ℂ := x.1.val
    let φ : R →L[ℂ] ℂ := x.2.val
    have hEq : ev.comp L = ψ.comp (completedProjectiveTensor_slice φ) := by
      apply completedProjectiveTensor_ext
      intro a r
      have ht := completedProjectiveTensor_slice_tmul (A := A) φ a r
      change (L (D.incl (a ⊗ₜ[ℂ] r))) x = ψ (completedProjectiveTensor_slice φ (D.incl (a ⊗ₜ[ℂ] r)))
      calc
        _ = P (a ⊗ₜ[ℂ] r) x := congrArg (fun z : C(I.1.forms × I.2.forms, ℂ) => z x) (hL _)
        _ = ψ a * φ r := tensorPairEvaluation_tmul _ _ _ _ _
        _ = ψ (φ r • a) := by rw [map_smul, smul_eq_mul, mul_comm]
        _ = _ := (congrArg ψ ht).symm
    exact (DFunLike.congr_fun hEq w).trans (scalar_zero ψ φ)
  have hEq : completeSeminorm (injectiveTensorSeminorm I) (hW.continuous_seminorm I) w =
      ‖L w‖ := by
    refine Completion.denseRange_coe.induction_on w
      (isClosed_eq (completeSeminorm_continuous _ _) L.continuous.norm) ?_
    intro x
    change completeSeminorm (injectiveTensorSeminorm I) (hW.continuous_seminorm I) ↑x = ‖L (D.incl x)‖
    rw [completeSeminorm_apply_coe, hL]
    rfl
  rw [hEq, hLw, norm_zero]


end

section

variable {A R Y J K : Type*} [AddCommGroup A] [Module ℂ A] [UniformSpace A]
  [IsUniformAddGroup A] [ContinuousSMul ℂ A] [PolynormableSpace ℂ A] [CompleteSpace A] [T2Space A]
  [AddCommGroup R] [Module ℂ R] [UniformSpace R] [IsUniformAddGroup R]
  [ContinuousSMul ℂ R] [PolynormableSpace ℂ R] [CompleteSpace R] [T2Space R]
  [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]

/-- A linear map out of the completed projective tensor is injective if its
evaluations determine all slices of a separating family. -/
theorem completedProjectiveTensor_injective_of_sliceEvaluations
    (e : J → R →L[ℂ] ℂ) (he : Injective (fun r j => e j r))
    (a : K → A →L[ℂ] ℂ) (ha : Injective (fun x k => a k x))
    (hπ : projectiveTensorTopology A R = injectiveTensorTopology A R)
    (F : (projectiveTensorModuleStructure A R).Completed →L[ℂ] Y)
    (ev : J → K → Y →L[ℂ] ℂ)
    (hv : ∀ j k b r, e j r * a k b =
      ev j k (F ((projectiveTensorModuleStructure A R).incl (b ⊗ₜ[ℂ] r)))) :
    Injective F := by
  apply (injective_iff_map_eq_zero F).mpr
  intro z hz
  apply completedProjectiveTensor_eq_zero_of_slices e he hπ z
  intro j
  apply ha
  funext k
  have hcomp : (a k).comp (completedProjectiveTensor_slice (e j)) = (ev j k).comp F := by
    apply completedProjectiveTensor_ext
    intro b r
    change (a k) (completedProjectiveTensor_slice (e j)
      ((projectiveTensorModuleStructure A R).incl (b ⊗ₜ[ℂ] r))) =
      ev j k (F ((projectiveTensorModuleStructure A R).incl (b ⊗ₜ[ℂ] r)))
    rw [completedProjectiveTensor_slice_tmul, map_smul, smul_eq_mul]
    exact hv j k b r
  have h := DFunLike.congr_fun hcomp z
  exact h.trans ((congrArg (ev j k) hz).trans ((ev j k).map_zero.trans (map_zero (a k)).symm))

end
end Masullo
