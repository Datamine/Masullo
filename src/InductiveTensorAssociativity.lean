import InductiveTensorTopology

open Topology
open scoped TensorProduct

namespace Masullo

noncomputable section

variable {A B C : Type*}
  [AddCommGroup A] [Module ℂ A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [AddCommGroup B] [Module ℂ B] [TopologicalSpace B] [IsTopologicalAddGroup B]
  [AddCommGroup C] [Module ℂ C] [TopologicalSpace C] [IsTopologicalAddGroup C]

theorem continuous_inductiveTensor_iff {D : Type*}
    [AddCommGroup D] [Module ℂ D] [TopologicalSpace D] [PolynormableSpace ℂ D]
    (L : A ⊗[ℂ] B →ₗ[ℂ] D) :
    Continuous[inductiveTensorTopology A B, inferInstance] L ↔
      (∀ b, Continuous fun a => L (a ⊗ₜ[ℂ] b)) ∧
      (∀ a, Continuous fun b => L (a ⊗ₜ[ℂ] b)) := by
  let e := TensorProduct.lift.equiv (RingHom.id ℂ) A B D
  have h := continuous_inductiveTensor_lift_iff (e.symm L)
  change Continuous[inductiveTensorTopology A B, inferInstance] (e (e.symm L)) ↔ _ at h
  rw [LinearEquiv.apply_symm_apply] at h
  exact h

omit [IsTopologicalAddGroup B] in
theorem continuous_inductiveTensor_tmul_left (b : B) :
    Continuous[inferInstance, inductiveTensorTopology A B] (fun a : A => a ⊗ₜ[ℂ] b) := by
  letI : TopologicalSpace (A ⊗[ℂ] B) := inductiveTensorTopology A B
  exact (inductiveTensor_withSeminorms.continuous_iff_continuous_comp
    ((TensorProduct.mk ℂ A B).flip b)).mpr fun p => p.first b

omit [IsTopologicalAddGroup A] in
theorem continuous_inductiveTensor_tmul_right (a : A) :
    Continuous[inferInstance, inductiveTensorTopology A B] (fun b : B => a ⊗ₜ[ℂ] b) := by
  letI : TopologicalSpace (A ⊗[ℂ] B) := inductiveTensorTopology A B
  exact (inductiveTensor_withSeminorms.continuous_iff_continuous_comp
    (TensorProduct.mk ℂ A B a)).mpr fun p => p.second a

/-- A linear homeomorphism of the left factor induces one of inductive tensors. -/
def inductiveTensor_rTensorEquiv (e : A ≃L[ℂ] B) :
    letI : TopologicalSpace (A ⊗[ℂ] C) := inductiveTensorTopology A C
    letI : TopologicalSpace (B ⊗[ℂ] C) := inductiveTensorTopology B C
    (A ⊗[ℂ] C) ≃L[ℂ] (B ⊗[ℂ] C) := by
  letI : TopologicalSpace (A ⊗[ℂ] C) := inductiveTensorTopology A C
  letI : TopologicalSpace (B ⊗[ℂ] C) := inductiveTensorTopology B C
  letI : PolynormableSpace ℂ (A ⊗[ℂ] C) := inductiveTensor_withSeminorms.toPolynormableSpace
  letI : PolynormableSpace ℂ (B ⊗[ℂ] C) := inductiveTensor_withSeminorms.toPolynormableSpace
  refine ⟨e.toLinearEquiv.rTensor C, (continuous_inductiveTensor_iff
    (e.toLinearEquiv.rTensor C).toLinearMap).mpr ⟨?_, ?_⟩,
    (continuous_inductiveTensor_iff (e.symm.toLinearEquiv.rTensor C).toLinearMap).mpr ⟨?_, ?_⟩⟩
  · intro c
    exact (continuous_inductiveTensor_tmul_left c).comp e.continuous
  · intro a
    exact continuous_inductiveTensor_tmul_right (e a)
  · intro c
    exact (continuous_inductiveTensor_tmul_left c).comp e.symm.continuous
  · intro b
    exact continuous_inductiveTensor_tmul_right (e.symm b)

set_option maxHeartbeats 800000 in
/-- The algebraic associator is a homeomorphism for the iterated inductive topologies. -/
def inductiveTensor_assoc :
    letI : TopologicalSpace (A ⊗[ℂ] B) := inductiveTensorTopology A B
    letI : TopologicalSpace (B ⊗[ℂ] C) := inductiveTensorTopology B C
    letI : TopologicalSpace ((A ⊗[ℂ] B) ⊗[ℂ] C) := inductiveTensorTopology (A ⊗[ℂ] B) C
    letI : TopologicalSpace (A ⊗[ℂ] (B ⊗[ℂ] C)) := inductiveTensorTopology A (B ⊗[ℂ] C)
    ((A ⊗[ℂ] B) ⊗[ℂ] C) ≃L[ℂ] (A ⊗[ℂ] (B ⊗[ℂ] C)) := by
  let U := A ⊗[ℂ] B
  let V := B ⊗[ℂ] C
  letI : TopologicalSpace U := inductiveTensorTopology A B
  letI : TopologicalSpace V := inductiveTensorTopology B C
  letI : IsTopologicalAddGroup U := (inductiveTensor_withSeminorms (E := A) (F := B)).topologicalAddGroup
  letI : IsTopologicalAddGroup V := (inductiveTensor_withSeminorms (E := B) (F := C)).topologicalAddGroup
  letI : TopologicalSpace (U ⊗[ℂ] C) := inductiveTensorTopology U C
  letI : TopologicalSpace (A ⊗[ℂ] V) := inductiveTensorTopology A V
  let W₁ := inductiveTensor_withSeminorms (E := U) (F := C)
  let W₂ := inductiveTensor_withSeminorms (E := A) (F := V)
  letI : PolynormableSpace ℂ (U ⊗[ℂ] C) := W₁.toPolynormableSpace
  letI : PolynormableSpace ℂ (A ⊗[ℂ] V) := W₂.toPolynormableSpace
  letI : IsTopologicalAddGroup (U ⊗[ℂ] C) := W₁.topologicalAddGroup
  letI : IsTopologicalAddGroup (A ⊗[ℂ] V) := W₂.topologicalAddGroup
  let e := TensorProduct.assoc ℂ A B C
  refine ⟨e, (continuous_inductiveTensor_iff e.toLinearMap).mpr ⟨?_, ?_⟩,
    (continuous_inductiveTensor_iff e.symm.toLinearMap).mpr ⟨?_, ?_⟩⟩
  · intro c
    apply (continuous_inductiveTensor_iff
      (e.toLinearMap.comp ((TensorProduct.mk ℂ U C).flip c))).mpr
    constructor
    · intro b
      simp only [LinearMap.comp_apply, LinearMap.flip_apply, LinearEquiv.coe_coe, e]
      exact continuous_inductiveTensor_tmul_left (b ⊗ₜ[ℂ] c)
    · intro a
      simp only [LinearMap.comp_apply, LinearMap.flip_apply, LinearEquiv.coe_coe, e]
      exact (continuous_inductiveTensor_tmul_right a).comp
        (continuous_inductiveTensor_tmul_left c)
  · intro u
    change Continuous (fun c => e (u ⊗ₜ[ℂ] c))
    induction u using TensorProduct.induction_on with
    | zero => simp only [TensorProduct.zero_tmul, map_zero]; exact continuous_const
    | tmul a b =>
      simp only [e, TensorProduct.assoc_tmul]
      exact (continuous_inductiveTensor_tmul_right a).comp (continuous_inductiveTensor_tmul_right b)
    | add u v hu hv => simpa only [TensorProduct.add_tmul, map_add, Pi.add_def] using hu.add hv
  · intro v
    change Continuous (fun a => e.symm (a ⊗ₜ[ℂ] v))
    induction v using TensorProduct.induction_on with
    | zero => simp only [TensorProduct.tmul_zero, map_zero]; exact continuous_const
    | tmul b c =>
      simp only [e, TensorProduct.assoc_symm_tmul]
      exact (continuous_inductiveTensor_tmul_left c).comp (continuous_inductiveTensor_tmul_left b)
    | add v w hv hw => simpa only [TensorProduct.tmul_add, map_add, Pi.add_def] using hv.add hw
  · intro a
    apply (continuous_inductiveTensor_iff
      (e.symm.toLinearMap.comp (TensorProduct.mk ℂ A V a))).mpr
    constructor
    · intro c
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, e]
      exact (continuous_inductiveTensor_tmul_left c).comp (continuous_inductiveTensor_tmul_right a)
    · intro b
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, e]
      exact continuous_inductiveTensor_tmul_right (a ⊗ₜ[ℂ] b)

end
end Masullo
