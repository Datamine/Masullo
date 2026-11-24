import IntegralBilinearForms
import ProjectiveTensorTopology

open Filter Function Set Topology
open scoped PointwiseConvergenceCLM TensorProduct

namespace Masullo

noncomputable section

variable {E F : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
variable [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
variable [PolynormableSpace ℂ E] [PolynormableSpace ℂ F]

omit [PolynormableSpace ℂ E] in
private theorem dualTest_pointwise_bounded (S : InjectiveDualTest E) (x : E) :
    BddAbove (range fun φ : S.forms => ‖φ.val x‖) :=
  (S.compact.image (PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) ℂ x).continuous.norm).bddAbove
    |>.mono (by rintro _ ⟨φ, rfl⟩; exact ⟨φ.val, φ.property, rfl⟩)

private def dualTestSeminorm (S : InjectiveDualTest E) : Seminorm ℂ E :=
  ⨆ φ : S.forms, (normSeminorm ℂ ℂ).comp φ.val.toLinearMap

omit [PolynormableSpace ℂ E] in
private theorem dualTestSeminorm_apply (S : InjectiveDualTest E) (x : E) :
    dualTestSeminorm S x = ⨆ φ : S.forms, ‖φ.val x‖ := by
  have hb : BddAbove (range fun φ : S.forms => (normSeminorm ℂ ℂ).comp φ.val.toLinearMap) :=
    Seminorm.bddAbove_range_iff.mpr (dualTest_pointwise_bounded S)
  exact Seminorm.iSup_apply hb

private theorem dualTestSeminorm_continuous (S : InjectiveDualTest E) :
    Continuous (dualTestSeminorm S) := by
  let hW := PolynormableSpace.withSeminorms ℂ E
  letI : IsTopologicalAddGroup E := hW.topologicalAddGroup
  letI : ContinuousSMul ℂ E := hW.continuousSMul
  apply Seminorm.continuous (r := 1)
  obtain h := S.equicontinuous (1 / 2) (by norm_num)
  filter_upwards [h] with x hx
  apply (dualTestSeminorm S).mem_ball_zero.mpr
  rw [dualTestSeminorm_apply]
  by_cases hne : Nonempty S.forms
  · exact (ciSup_le (fun φ : S.forms => hx φ.val φ.property)).trans_lt (by norm_num)
  · letI : IsEmpty S.forms := not_nonempty_iff.mp hne
    simp

omit [PolynormableSpace ℂ E] in
theorem dualTestSeminorm_dom (S : InjectiveDualTest E) (φ : S.forms) (x : E) :
    ‖φ.val x‖ ≤ dualTestSeminorm S x := by
  rw [dualTestSeminorm_apply]
  exact le_ciSup (dualTest_pointwise_bounded S x) φ

/-- Each injective tensor seminorm is a projective tensor seminorm test. -/
def injectiveAsProjectiveTest (I : InjectiveDualTest E × InjectiveDualTest F) :
    ProjectiveTensorTest E F where
  tensor := injectiveTensorSeminorm I
  first := dualTestSeminorm I.1
  second := dualTestSeminorm I.2
  first_continuous := dualTestSeminorm_continuous I.1
  second_continuous := dualTestSeminorm_continuous I.2
  bound x y := by
    letI : CompactSpace I.1.forms := isCompact_iff_compactSpace.mp I.1.compact
    letI : CompactSpace I.2.forms := isCompact_iff_compactSpace.mp I.2.compact
    change ‖tensorPairEvaluation I.1.forms I.2.forms (x ⊗ₜ[ℂ] y)‖ ≤ _
    apply (ContinuousMap.norm_le _ (by positivity)).mpr
    intro p
    rw [tensorPairEvaluation_tmul, norm_mul]
    exact mul_le_mul (dualTestSeminorm_dom I.1 p.1 x) (dualTestSeminorm_dom I.2 p.2 y)
      (norm_nonneg _) (apply_nonneg _ _)

/-- The identity from the projective tensor topology to the injective
tensor topology is continuous. -/
theorem projective_to_injective_continuous :
    Continuous[projectiveTensorTopology E F, injectiveTensorTopology E F] (id : E ⊗[ℂ] F → E ⊗[ℂ] F) := by
  have hW : @WithSeminorms ℂ (E ⊗[ℂ] F) _ _ _ _
      (injectiveTensorSeminorm (E := E) (F := F)) (injectiveTensorTopology E F) := by
    letI : TopologicalSpace (E ⊗[ℂ] F) := injectiveTensorTopology E F
    exact ⟨rfl⟩
  letI : TopologicalSpace (E ⊗[ℂ] F) := projectiveTensorTopology E F
  have hp := projectiveTensor_withSeminorms (E := E) (F := F)
  exact (@WithSeminorms.continuous_iff_continuous_comp ℂ ℂ (E ⊗[ℂ] F) (E ⊗[ℂ] F)
    _ _ _ _ _ _ _ (RingHom.id ℂ) _ _ (projectiveTensorTopology E F) hp.topologicalAddGroup
    (injectiveTensorTopology E F) hW LinearMap.id).mpr
      (fun I => hp.continuous_seminorm (injectiveAsProjectiveTest I))

end

end Masullo
