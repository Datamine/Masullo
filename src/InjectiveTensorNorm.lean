import InjectiveTensorMaps
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Topology.MetricSpace.Completion

open Filter Function Set Topology UniformSpace
open scoped NNReal PointwiseConvergenceCLM TensorProduct Uniformity

namespace Masullo

noncomputable section

open scoped Classical
open InjectiveTensorTools

set_option maxHeartbeats 1800000

section Normed

variable {E F E' F' : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
variable [NormedAddCommGroup E'] [NormedSpace ℂ E'] [NormedAddCommGroup F'] [NormedSpace ℂ F']

/-- A bounded functional viewed in its pointwise-convergence dual. -/
def asPointwise {V : Type*} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]
    (φ : V →L[ℂ] ℂ) : V →Lₚₜ[ℂ] ℂ := φ

@[simp] private theorem asPointwise_apply {V : Type*} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]
    (φ : V →L[ℂ] ℂ) (x : V) : asPointwise φ x = φ x := rfl

/-- The injective norm is the supremum of evaluations against the two dual unit balls. -/
def injectiveTensorNorm (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] : Seminorm ℂ (E ⊗[ℂ] F) :=
  injectiveTensorSeminorm
    (seminormPolarTest (normSeminorm ℂ E) continuous_norm, seminormPolarTest (normSeminorm ℂ F) continuous_norm)

private theorem dualPair_unit_le (z : E ⊗[ℂ] F) (φ : E →L[ℂ] ℂ) (ψ : F →L[ℂ] ℂ)
    (hφ : ‖φ‖ ≤ 1) (hψ : ‖ψ‖ ≤ 1) :
    ‖dualPair (asPointwise φ) (asPointwise ψ) z‖ ≤ injectiveTensorNorm E F z :=
  norm_dualPair_le _ _ z (fun x => by
    change ‖φ x‖ ≤ ‖x‖
    simpa only [one_mul] using φ.le_of_opNorm_le hφ x) (fun x => by
    change ‖ψ x‖ ≤ ‖x‖
    simpa only [one_mul] using ψ.le_of_opNorm_le hψ x)

/-- A uniform bound over the dual unit balls bounds the injective norm. -/
theorem injectiveTensorNorm_le_of_dualPairs (z : E ⊗[ℂ] F) {r : ℝ} (hr : 0 ≤ r)
    (H : ∀ (φ : E →L[ℂ] ℂ) (ψ : F →L[ℂ] ℂ), ‖φ‖ ≤ 1 → ‖ψ‖ ≤ 1 →
      ‖dualPair (asPointwise φ) (asPointwise ψ) z‖ ≤ r) :
    injectiveTensorNorm E F z ≤ r := by
  apply injectiveTensorSeminorm_le _ _ _ hr
  intro φ hφ ψ hψ
  exact H φ ψ
    (ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
      rw [one_mul]
      exact hφ x)
    (ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
      rw [one_mul]
      exact hψ x)

private theorem normed_eq_zero_of_dual_unit (x : E)
    (h : ∀ (φ : E →L[ℂ] ℂ), ‖φ‖ ≤ 1 → φ x = 0) : x = 0 := by
  obtain ⟨φ, hφ, hv⟩ := exists_dual_vector'' ℂ x
  exact norm_eq_zero.mp (Complex.ofReal_eq_zero.mp (hv.symm.trans (h φ hφ)))

theorem injectiveTensorNorm_eq_zero (z : E ⊗[ℂ] F) (hz : injectiveTensorNorm E F z = 0) :
    z = 0 := by
  let b := Module.Free.chooseBasis ℂ F
  let e := TensorProduct.equivFinsuppOfBasisRight (M := E) b
  have hpair (φ : E →L[ℂ] ℂ) (ψ : F →L[ℂ] ℂ) (hφ : ‖φ‖ ≤ 1) (hψ : ‖ψ‖ ≤ 1) :
      dualPair (asPointwise φ) (asPointwise ψ) z = 0 :=
    norm_le_zero_iff.mp ((dualPair_unit_le z φ ψ hφ hψ).trans_eq hz)
  let contract (φ : E →L[ℂ] ℂ) : E ⊗[ℂ] F →ₗ[ℂ] F :=
    (TensorProduct.lid ℂ F).toLinearMap.comp (TensorProduct.map φ.toLinearMap LinearMap.id)
  have hcontract (φ : E →L[ℂ] ℂ) (hφ : ‖φ‖ ≤ 1) : contract φ z = 0 := by
    apply normed_eq_zero_of_dual_unit
    intro ψ hψ
    have he : ψ.toLinearMap.comp (contract φ) = dualPair (asPointwise φ) (asPointwise ψ) := by
      apply TensorProduct.ext'
      intro x y
      change ψ ((TensorProduct.lid ℂ F) (TensorProduct.map φ.toLinearMap LinearMap.id (x ⊗ₜ[ℂ] y))) = _
      rw [TensorProduct.map_tmul, TensorProduct.lid_tmul, LinearMap.id_apply, map_smul, smul_eq_mul,
        dualPair_tmul]
      rfl
    exact (DFunLike.congr_fun he z).trans (hpair φ ψ hφ hψ)
  apply e.injective
  rw [map_zero]
  ext i
  change e z i = 0
  apply normed_eq_zero_of_dual_unit
  intro φ hφ
  have he (w : E ⊗[ℂ] F) : φ (e w i) = b.repr (contract φ w) i := by
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
      change φ ((TensorProduct.equivFinsuppOfBasisRight b) (x ⊗ₜ[ℂ] y) i) =
        b.repr ((TensorProduct.lid ℂ F) (TensorProduct.map φ.toLinearMap
          LinearMap.id (x ⊗ₜ[ℂ] y))) i
      rw [TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply,
        TensorProduct.map_tmul, TensorProduct.lid_tmul, LinearMap.id_apply, map_smul, map_smul,
        Finsupp.smul_apply, smul_eq_mul, smul_eq_mul, mul_comm]
      rfl
    | add u v hu hv => simp [map_add, hu, hv]
  rw [he, hcontract φ hφ, map_zero, Finsupp.zero_apply]

/-- The normed additive group defined by the injective norm. -/
abbrev injectiveTensorNormedGroup (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] : NormedAddCommGroup (E ⊗[ℂ] F) :=
  AddGroupNorm.toNormedAddCommGroup
    ⟨(injectiveTensorNorm E F).toAddGroupSeminorm, fun z hz => injectiveTensorNorm_eq_zero z hz⟩

/-- The tensor of linear isometries preserves the injective norm. -/
theorem injectiveTensor_map_norm_eq (f : E →ₗᵢ[ℂ] E') (g : F →ₗᵢ[ℂ] F')
    (z : E ⊗[ℂ] F) :
    injectiveTensorNorm E' F' (TensorProduct.map f.toLinearMap g.toLinearMap z) =
      injectiveTensorNorm E F z := by
  apply le_antisymm
  · apply injectiveTensorNorm_le_of_dualPairs _ (apply_nonneg _ _)
    intro φ ψ hφ hψ
    change ‖dualPair (asPointwise φ) (asPointwise ψ)
      (TensorProduct.map f.toContinuousLinearMap.toLinearMap g.toContinuousLinearMap.toLinearMap z)‖ ≤ _
    rw [dualPair_tensorMap f.toContinuousLinearMap g.toContinuousLinearMap]
    change ‖dualPair (asPointwise (φ.comp f.toContinuousLinearMap))
      (asPointwise (ψ.comp g.toContinuousLinearMap)) z‖ ≤ _
    exact dualPair_unit_le z _ _
      (ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
        change ‖φ (f x)‖ ≤ _
        simpa only [f.norm_map] using φ.le_of_opNorm_le hφ (f x))
      (ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
        change ‖ψ (g x)‖ ≤ _
        simpa only [g.norm_map] using ψ.le_of_opNorm_le hψ (g x))
  · apply injectiveTensorNorm_le_of_dualPairs _ (apply_nonneg _ _)
    intro φ ψ hφ hψ
    obtain ⟨φ', hφ', hφe⟩ := extend_form_with_bound f.toContinuousLinearMap f.injective
      (normSeminorm ℂ E') continuous_norm (asPointwise φ) (fun x => by
        change ‖φ x‖ ≤ ‖f x‖
        simpa only [one_mul, f.norm_map] using φ.le_of_opNorm_le hφ x)
    obtain ⟨ψ', hψ', hψe⟩ := extend_form_with_bound g.toContinuousLinearMap g.injective
      (normSeminorm ℂ F') continuous_norm (asPointwise ψ) (fun x => by
        change ‖ψ x‖ ≤ ‖g x‖
        simpa only [one_mul, g.norm_map] using ψ.le_of_opNorm_le hψ x)
    have he := dualPair_tensorMap f.toContinuousLinearMap g.toContinuousLinearMap φ' ψ' z
    rw [hφe, hψe] at he
    rw [← he]
    exact norm_dualPair_le _ _ _ hφ' hψ'

/-- The completed tensor map of linear isometries is an isometry for the
metric completions of the injective norms. -/
theorem completedInjectiveTensorMap_isometry (f : E →ₗᵢ[ℂ] E') (g : F →ₗᵢ[ℂ] F') :
    letI : NormedAddCommGroup (E ⊗[ℂ] F) := injectiveTensorNormedGroup E F
    letI : NormedAddCommGroup (E' ⊗[ℂ] F') := injectiveTensorNormedGroup E' F'
    Isometry (Completion.map (TensorProduct.map f.toLinearMap g.toLinearMap)) := by
  letI : NormedAddCommGroup (E ⊗[ℂ] F) := injectiveTensorNormedGroup E F
  letI : NormedAddCommGroup (E' ⊗[ℂ] F') := injectiveTensorNormedGroup E' F'
  exact (AddMonoidHomClass.isometry_of_norm (TensorProduct.map f.toLinearMap g.toLinearMap)
    (injectiveTensor_map_norm_eq f g)).completion_map

private theorem dualTest_unitScaling (S : InjectiveDualTest E) :
    ∃ a : ℝ, 0 < a ∧ ∀ φ ∈ S.forms, ∀ x, ‖φ x‖ ≤ a * ‖x‖ := by
  obtain ⟨r, hr, hS⟩ := Metric.mem_nhds_iff.mp (S.equicontinuous 1 zero_lt_one)
  let c : ℝ≥0 := ⟨r⁻¹, inv_nonneg.mpr hr.le⟩
  let q : Seminorm ℂ E := c • normSeminorm ℂ E
  refine ⟨r⁻¹, inv_pos.mpr hr, fun φ hφ => ?_⟩
  apply seminorm_bound_of_unitBall ((normSeminorm ℂ ℂ).comp φ.toLinearMap) q
  intro x hx
  apply hS _ φ hφ
  apply Metric.mem_ball.mpr
  rw [dist_zero_right]
  exact (inv_mul_lt_iff₀ hr).mp hx |>.trans_eq (mul_one _)

private theorem dualPair_scale (a b : ℂ) (φ : E →Lₚₜ[ℂ] ℂ) (ψ : F →Lₚₜ[ℂ] ℂ)
    (z : E ⊗[ℂ] F) : dualPair (a • φ) (b • ψ) z = (a * b) * dualPair φ ψ z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    rw [dualPair_tmul, dualPair_tmul]
    change (a * φ x) * (b * ψ y) = (a * b) * (φ x * ψ y)
    ring
  | add x y hx hy => rw [map_add, map_add, hx, hy, mul_add]

private theorem normalizedDualForm_bound {D : Type*} [NormedAddCommGroup D] [NormedSpace ℂ D]
    (c : ℝ) (hc : 0 < c) (ω : D →Lₚₜ[ℂ] ℂ) (h : ∀ x, ‖ω x‖ ≤ c * ‖x‖) (x : D) :
    ‖(((c : ℂ)⁻¹) • ω) x‖ ≤ ‖x‖ := by
  change ‖(c : ℂ)⁻¹ * ω x‖ ≤ ‖x‖
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hc.le, inv_mul_le_iff₀ hc]
  exact h x

/-- An elementary dual pairing is bounded by the product of the dual norms
times the injective tensor norm. -/
theorem norm_dualPair_le_injectiveTensorNorm (φ : StrongDual ℂ E) (ψ : StrongDual ℂ F)
    (z : E ⊗[ℂ] F) :
    ‖dualPair (asPointwise φ) (asPointwise ψ) z‖ ≤ (‖φ‖ * ‖ψ‖) * injectiveTensorNorm E F z := by
  by_cases hφ : φ = 0
  · subst φ
    have he : dualPair (asPointwise (0 : StrongDual ℂ E)) (asPointwise ψ) z = 0 := by
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul x y => simp [asPointwise_apply]
      | add x y hx hy => simp [hx, hy]
    simp [he]
  by_cases hψ : ψ = 0
  · subst ψ
    have he : dualPair (asPointwise φ) (asPointwise (0 : StrongDual ℂ F)) z = 0 := by
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul x y => simp [asPointwise_apply]
      | add x y hx hy => simp [hx, hy]
    simp [he]
  let a : ℝ := ‖φ‖
  let b : ℝ := ‖ψ‖
  have ha : 0 < a := norm_pos_iff.mpr hφ
  have hb : 0 < b := norm_pos_iff.mpr hψ
  let f := ((a : ℂ)⁻¹) • asPointwise φ
  let g := ((b : ℂ)⁻¹) • asPointwise ψ
  have hfg : ‖dualPair f g z‖ ≤ injectiveTensorNorm E F z :=
    norm_dualPair_le _ _ z (normalizedDualForm_bound a ha _ φ.le_opNorm)
      (normalizedDualForm_bound b hb _ ψ.le_opNorm)
  have hf : (a : ℂ) • f = asPointwise φ :=
    smul_inv_smul₀ (Complex.ofReal_ne_zero.mpr ha.ne') _
  have hg : (b : ℂ) • g = asPointwise ψ :=
    smul_inv_smul₀ (Complex.ofReal_ne_zero.mpr hb.ne') _
  rw [← hf, ← hg, dualPair_scale, norm_mul, norm_mul,
    Complex.norm_of_nonneg ha.le, Complex.norm_of_nonneg hb.le]
  exact mul_le_mul_of_nonneg_left hfg (mul_nonneg ha.le hb.le)

private theorem injectiveTensorNorm_dominates (S : InjectiveDualTest E) (T : InjectiveDualTest F) :
    ∃ c : ℝ≥0, ∀ z, injectiveTensorSeminorm (S, T) z ≤ c * injectiveTensorNorm E F z := by
  obtain ⟨a, ha, hS⟩ := dualTest_unitScaling S
  obtain ⟨b, hb, hT⟩ := dualTest_unitScaling T
  refine ⟨⟨a * b, mul_nonneg ha.le hb.le⟩, fun z => ?_⟩
  apply injectiveTensorSeminorm_le S T z (mul_nonneg (mul_nonneg ha.le hb.le) (apply_nonneg _ _))
  intro φ hφ ψ hψ
  let Φ : E →Lₚₜ[ℂ] ℂ := ((a : ℂ)⁻¹) • φ
  let Ψ : F →Lₚₜ[ℂ] ℂ := ((b : ℂ)⁻¹) • ψ
  have hbound : ‖dualPair Φ Ψ z‖ ≤ injectiveTensorNorm E F z :=
    norm_dualPair_le _ _ z (fun x => normalizedDualForm_bound a ha φ (hS φ hφ) x)
      (fun y => normalizedDualForm_bound b hb ψ (hT ψ hψ) y)
  have heφ : (a : ℂ) • Φ = φ :=
    smul_inv_smul₀ (Complex.ofReal_ne_zero.mpr ha.ne') _
  have heψ : (b : ℂ) • Ψ = ψ :=
    smul_inv_smul₀ (Complex.ofReal_ne_zero.mpr hb.ne') _
  rw [← heφ, ← heψ, dualPair_scale, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg ha.le, Real.norm_of_nonneg hb.le]
  exact mul_le_mul_of_nonneg_left hbound (mul_nonneg ha.le hb.le)

/-- The metric of the injective norm induces the injective uniform structure. -/
theorem injectiveTensor_uniformity_eq_norm (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] :
    (injectiveTensorStructure E F).uniformSpace =
      (injectiveTensorNormedGroup E F).toMetricSpace.toUniformSpace := by
  let D := injectiveTensorStructure E F
  letI : UniformSpace (E ⊗[ℂ] F) := D.uniformSpace
  letI : IsUniformAddGroup (E ⊗[ℂ] F) := D.uniformGroup
  letI : ContinuousConstSMul ℂ (E ⊗[ℂ] F) := D.constSmul
  let p := injectiveTensorNorm E F
  have hp : Continuous p := injectiveTensor_withSeminorms.continuous_seminorm _
  have he := Seminorm.uniformSpace_eq_of_hasBasis p injectiveTensor_withSeminorms.hasBasis_zero_ball
    ⟨1, mem_of_superset (Seminorm.ball_mem_nhds hp zero_lt_one) (Seminorm.ball_subset_closedBall _ _ _)⟩
    (by
      rintro ⟨I, r⟩ hr
      have hdom (i : InjectiveDualTest E × InjectiveDualTest F) :
          ∃ c : ℝ≥0, ∀ z, injectiveTensorSeminorm i z ≤ c * p z :=
        injectiveTensorNorm_dominates i.1 i.2
      choose c hc using hdom
      let C : ℝ≥0 := I.sup c
      refine ⟨r / ((C : ℝ) + 1), by positivity, ?_⟩
      intro z hz
      apply (I.sup (injectiveTensorSeminorm (E := E) (F := F))).mem_ball_zero.mpr
      apply Seminorm.finset_sup_apply_lt hr
      intro i hi
      obtain hC : (c i : ℝ) ≤ C := by exact_mod_cast Finset.le_sup (f := c) hi
      have hb : p z * ((C : ℝ) + 1) < r :=
        (lt_div_iff₀ (by positivity : 0 < (C : ℝ) + 1)).mp (p.mem_ball_zero.mp hz)
      exact (hc i z).trans_lt (lt_of_le_of_lt
        (by nlinarith only [mul_le_mul_of_nonneg_right hC (apply_nonneg p z), apply_nonneg p z])
        hb))
  exact he

end Normed

end

end Masullo
