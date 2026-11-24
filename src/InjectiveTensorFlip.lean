import CompletedTensorFlip
import InjectiveTensorMaps

open Topology UniformSpace Masullo.InjectiveTensorTools
open scoped TensorProduct PointwiseConvergenceCLM

namespace Masullo

noncomputable section

variable {A R : Type*} [AddCommGroup A] [Module ℂ A] [TopologicalSpace A]
  [AddCommGroup R] [Module ℂ R] [TopologicalSpace R]

/-- The factor flip preserves the injective tensor topology. -/
theorem continuous_injectiveTensor_flip :
    Continuous[injectiveTensorTopology A R, injectiveTensorTopology R A]
      (TensorProduct.comm ℂ A R) := by
  letI : TopologicalSpace (A ⊗[ℂ] R) := injectiveTensorTopology A R
  letI : TopologicalSpace (R ⊗[ℂ] A) := injectiveTensorTopology R A
  let WA := injectiveTensor_withSeminorms (X := A) (Y := R)
  let WR := injectiveTensor_withSeminorms (X := R) (Y := A)
  letI : IsTopologicalAddGroup (A ⊗[ℂ] R) := WA.topologicalAddGroup
  let flip := (TensorProduct.comm ℂ A R).toLinearMap
  apply (WR.continuous_iff_continuous_comp flip).mpr
  rintro ⟨S, T⟩
  have hp (φ : R →Lₚₜ[ℂ] ℂ) (ψ : A →Lₚₜ[ℂ] ℂ) (w : A ⊗[ℂ] R) :
      dualPair φ ψ (flip w) = dualPair ψ φ w := by
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul a r =>
      change dualPair φ ψ (TensorProduct.comm ℂ A R (a ⊗ₜ[ℂ] r)) = _
      rw [TensorProduct.comm_tmul, dualPair_tmul, dualPair_tmul, mul_comm]
    | add x y hx hy => simp [hx, hy]
  refine Seminorm.continuous_of_le (WA.continuous_seminorm (T, S)) ?_
  intro w
  change injectiveTensorSeminorm (S, T) (flip w) ≤ injectiveTensorSeminorm (T, S) w
  refine injectiveTensorSeminorm_le S T (flip w) (apply_nonneg _ _) ?_
  intro φ hφ ψ hψ
  rw [hp]
  exact norm_dualPair_le T S w hψ hφ

/-- Equality of the projective and injective tensor topologies transports
through the factor flip. -/
theorem tensorTopologies_equal_of_flip [PolynormableSpace ℂ A] [PolynormableSpace ℂ R]
    (h : projectiveTensorTopology R A = injectiveTensorTopology R A) :
    projectiveTensorTopology A R = injectiveTensorTopology A R := by
  have hc : Continuous[injectiveTensorTopology A R, projectiveTensorTopology R A]
      (TensorProduct.comm ℂ A R) := by
    rw [h]
    exact continuous_injectiveTensor_flip
  have hb := @Continuous.comp _ _ _
    (injectiveTensorTopology A R) (projectiveTensorTopology R A)
    (projectiveTensorTopology A R) _ _
    (continuous_projectiveTensor_flip (A := R) (R := A)) hc
  have hid : Continuous[injectiveTensorTopology A R, projectiveTensorTopology A R]
      (id : A ⊗[ℂ] R → A ⊗[ℂ] R) := by
    change Continuous[injectiveTensorTopology A R, projectiveTensorTopology A R]
      (fun x : A ⊗[ℂ] R => x)
    simpa only [Function.comp_def, TensorProduct.comm_comm] using hb
  exact le_antisymm
    (continuous_id_iff_le.mp (projective_to_injective_continuous (E := A) (F := R)))
    (continuous_id_iff_le.mp hid)

end
end Masullo
