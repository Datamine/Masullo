import CompletedProjectiveTensorMaps
import InjectiveTensorMaps

open Bornology Filter Function Set Topology UniformSpace
open scoped TensorProduct

namespace Masullo

noncomputable section

variable {A R : Type*} [AddCommGroup A] [Module ℂ A] [UniformSpace A] [IsUniformAddGroup A]
  [ContinuousSMul ℂ A] [PolynormableSpace ℂ A] [CompleteSpace A] [T2Space A]
  [AddCommGroup R] [Module ℂ R] [TopologicalSpace R] [PolynormableSpace ℂ R]

private def projectiveTensorSliceLinear (φ : R →L[ℂ] ℂ) : A ⊗[ℂ] R →ₗ[ℂ] A :=
  TensorProduct.lift ((LinearMap.lsmul ℂ A).flip.compl₁₂ LinearMap.id φ.toLinearMap)

omit [UniformSpace A] [IsUniformAddGroup A] [ContinuousSMul ℂ A] [PolynormableSpace ℂ A]
  [CompleteSpace A] [T2Space A] [PolynormableSpace ℂ R] in
@[simp] private theorem projectiveTensorSliceLinear_tmul
    (φ : R →L[ℂ] ℂ) (a : A) (r : R) :
    projectiveTensorSliceLinear φ (a ⊗ₜ[ℂ] r) = φ r • a := by
  exact TensorProduct.lift.tmul a r

private theorem exists_projectiveTensor_slice (φ : R →L[ℂ] ℂ) :
    ∃ L : (projectiveTensorModuleStructure A R).Completed →L[ℂ] A,
      ∀ w, L ((projectiveTensorModuleStructure A R).incl w) = projectiveTensorSliceLinear φ w := by
  let D := projectiveTensorModuleStructure A R
  let X := A ⊗[ℂ] R
  letI : TopologicalSpace X := D.topology
  let B := (LinearMap.lsmul ℂ A).flip.compl₁₂ LinearMap.id φ.toLinearMap
  have hc : Continuous (fun z : A × R => B z.1 z.2) :=
    (φ.continuous.comp continuous_snd).smul continuous_fst
  let L : X →L[ℂ] A := ⟨projectiveTensorSliceLinear φ, continuous_projectiveTensor_lift B hc⟩
  exact D.exists_continuousLinearMap_extend L

/-- Contraction against a continuous radial functional on the completed projective tensor product. -/
def completedProjectiveTensor_slice (φ : R →L[ℂ] ℂ) :
    (projectiveTensorModuleStructure A R).Completed →L[ℂ] A :=
  (exists_projectiveTensor_slice φ).choose

private theorem completedProjectiveTensor_slice_incl (φ : R →L[ℂ] ℂ) (w : A ⊗[ℂ] R) :
    completedProjectiveTensor_slice φ ((projectiveTensorModuleStructure A R).incl w) =
      projectiveTensorSliceLinear φ w :=
  (exists_projectiveTensor_slice φ).choose_spec w

@[simp] theorem completedProjectiveTensor_slice_tmul (φ : R →L[ℂ] ℂ) (a : A) (r : R) :
    completedProjectiveTensor_slice φ ((projectiveTensorModuleStructure A R).incl (a ⊗ₜ[ℂ] r)) =
      φ r • a :=
  (completedProjectiveTensor_slice_incl φ _).trans (projectiveTensorSliceLinear_tmul φ a r)

omit [UniformSpace A] [IsUniformAddGroup A] [ContinuousSMul ℂ A] [PolynormableSpace ℂ A]
  [CompleteSpace A] [T2Space A] [PolynormableSpace ℂ R] in
private theorem bddAbove_projectiveTensorSlice {J : Type*} (e : J → R →L[ℂ] ℂ)
    (p : Seminorm ℂ R) (he : ∀ j r, ‖e j r‖ ≤ p r)
    (q : Seminorm ℂ A) (w : A ⊗[ℂ] R) :
    BddAbove (range fun j => q (projectiveTensorSliceLinear (e j) w)) := by
  induction w using TensorProduct.induction_on with
  | zero =>
    refine ⟨0, ?_⟩
    rintro _ ⟨j, hj⟩
    rw [← hj]
    simp
  | tmul a r =>
    refine ⟨p r * q a, ?_⟩
    rintro _ ⟨j, hj⟩
    rw [← hj]
    change q (projectiveTensorSliceLinear (e j) (a ⊗ₜ[ℂ] r)) ≤ p r * q a
    rw [projectiveTensorSliceLinear_tmul, map_smul_eq_mul]
    exact mul_le_mul_of_nonneg_right (he j r) (apply_nonneg q a)
  | add w v hw hv =>
    obtain ⟨b, hb⟩ := hw
    obtain ⟨c, hc⟩ := hv
    refine ⟨b + c, ?_⟩
    rintro _ ⟨j, hj⟩
    rw [← hj]
    change q (projectiveTensorSliceLinear (e j) (w + v)) ≤ b + c
    rw [map_add]
    exact (map_add_le_add q _ _).trans (add_le_add (hb (mem_range_self j)) (hc (mem_range_self j)))

/-- A common bound on the radial functionals gives a uniform seminorm
bound for the corresponding slices on the completed projective tensor. -/
theorem exists_completedProjectiveTensor_slice_bound {J : Type*} [Nonempty J] (e : J → R →L[ℂ] ℂ)
    (p : Seminorm ℂ R) (hp : Continuous p) (he : ∀ j r, ‖e j r‖ ≤ p r)
    (q : Seminorm ℂ A) (hq : Continuous q) :
    ∃ Q : Seminorm ℂ (projectiveTensorModuleStructure A R).Completed,
      Continuous Q ∧ ∀ j w, q (completedProjectiveTensor_slice (e j) w) ≤ Q w := by
  let D := projectiveTensorModuleStructure A R
  let X := A ⊗[ℂ] R
  letI : UniformSpace X := D.uniformSpace
  letI : IsUniformAddGroup X := D.uniformGroup
  letI : UniformContinuousConstSMul ℂ X := D.uniformConstSmul
  let Q₀ : Seminorm ℂ X := ⨆ j, q.comp (projectiveTensorSliceLinear (e j))
  have hb (w : X) : BddAbove (range fun j => q (projectiveTensorSliceLinear (e j) w)) :=
    bddAbove_projectiveTensorSlice e p he q w
  have hQ (w : X) : Q₀ w = ⨆ j, q (projectiveTensorSliceLinear (e j) w) :=
    Seminorm.iSup_apply (Seminorm.bddAbove_range_iff.mpr hb)
  let P : ProjectiveTensorTest A R :=
    { tensor := Q₀
      first := q
      second := p
      first_continuous := hq
      second_continuous := hp
      bound a r := by
        rw [hQ]
        apply ciSup_le
        intro j
        rw [projectiveTensorSliceLinear_tmul, map_smul_eq_mul, mul_comm (q a)]
        exact mul_le_mul_of_nonneg_right (he j r) (apply_nonneg q a) }
  have hP : Continuous Q₀ := projectiveTensor_withSeminorms.continuous_seminorm P
  let Q := completeSeminorm Q₀ hP
  have hc : Continuous Q := completeSeminorm_continuous Q₀ hP
  refine ⟨Q, hc, fun j z => ?_⟩
  refine Completion.denseRange_coe.induction_on z
    (isClosed_le (hq.comp (completedProjectiveTensor_slice (e j)).continuous) hc) ?_
  intro w
  change q (completedProjectiveTensor_slice (e j) (D.incl w)) ≤ Q (D.incl w)
  have h₁ := completedProjectiveTensor_slice_incl (e j) w
  have h₂ : Q (D.incl w) = Q₀ w := completeSeminorm_apply_coe Q₀ hP w
  rw [h₁, h₂, hQ]
  exact le_ciSup (hb w) j

/-- A bounded set of projective tensors has a bounded set of slices
under any family of functionals controlled by one seminorm. -/
theorem completedProjectiveTensor_slices_bounded {J : Type*} [Nonempty J]
    (e : J → R →L[ℂ] ℂ) (p : Seminorm ℂ R) (hp : Continuous p)
    (he : ∀ j r, ‖e j r‖ ≤ p r)
    (S : Set (projectiveTensorModuleStructure A R).Completed) (hS : IsVonNBounded ℂ S) :
    IsVonNBounded ℂ {a : A | ∃ j z, z ∈ S ∧ completedProjectiveTensor_slice (e j) z = a} := by
  let X := A ⊗[ℂ] R
  let D := projectiveTensorModuleStructure A R
  let V := D.Completed
  letI : UniformSpace X := D.uniformSpace
  letI : IsUniformAddGroup X := D.uniformGroup
  letI : UniformContinuousConstSMul ℂ X := D.uniformConstSmul
  letI : PolynormableSpace ℂ X := projectiveTensor_withSeminorms.toPolynormableSpace
  letI : PolynormableSpace ℂ V := polynormableSpace_completion
  apply (PolynormableSpace.withSeminorms ℂ A).isVonNBounded_iff_seminorm_bounded.mpr
  intro q
  obtain ⟨Q, hQ, hq⟩ := exists_completedProjectiveTensor_slice_bound e p hp he q.val q.property
  obtain ⟨M, hM, hMS⟩ :=
    (PolynormableSpace.withSeminorms ℂ V).isVonNBounded_iff_seminorm_bounded.mp hS ⟨Q, hQ⟩
  refine ⟨M, hM, ?_⟩
  rintro a ⟨j, z, hz, rfl⟩
  exact (hq j z).trans_lt (hMS z hz)

end

noncomputable section

variable {A B R : Type*} [AddCommGroup A] [Module ℂ A] [UniformSpace A] [IsUniformAddGroup A]
  [ContinuousSMul ℂ A] [PolynormableSpace ℂ A] [CompleteSpace A] [T2Space A]
  [AddCommGroup B] [Module ℂ B] [UniformSpace B] [IsUniformAddGroup B]
  [ContinuousSMul ℂ B] [PolynormableSpace ℂ B] [CompleteSpace B] [T2Space B]
  [AddCommGroup R] [Module ℂ R] [TopologicalSpace R] [PolynormableSpace ℂ R]

/-- Tensor contraction commutes with applying a continuous map to the retained factor. -/
theorem completedProjectiveTensor_slice_mapLeft
    (f : A →L[ℂ] B) (φ : R →L[ℂ] ℂ) :
    (completedProjectiveTensor_slice φ).comp (completedProjectiveTensor_mapLeft (R := R) f) =
      f.comp (completedProjectiveTensor_slice φ) := by
  apply completedProjectiveTensor_ext
  intro a r
  simp only [ContinuousLinearMap.comp_apply, completedProjectiveTensor_mapLeft_tmul,
    completedProjectiveTensor_slice_tmul, map_smul]

end
end Masullo
