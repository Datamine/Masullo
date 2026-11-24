import LocalBanachSpaces
import ProjectiveTensorTopology
import WeakDualFiniteRank
import WeakDualCompactness
import PettisBounds
import TensorTopologyComparison
import Mathlib.Analysis.LocallyConvex.PointwiseConvergence
import Mathlib.LinearAlgebra.TensorProduct.Associator

open Filter Function Set Topology
open scoped NNReal PointwiseConvergenceCLM TensorProduct

namespace Masullo

noncomputable section

variable {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]

/-- The actual local Banach space of any continuous weak-dual seminorm
is finite-dimensional. -/
theorem weakDual_localBanach_finiteDimensional
    (p : Seminorm ℂ (E →Lₚₜ[ℂ] ℂ)) (hp : Continuous p) :
    FiniteDimensional ℂ (LocalBanach p) :=
  weakDual_dense_banach_image_finiteDimensional
    (localBanachMap p hp) (localBanachDenseMap_dense p)

private theorem weakDual_seminorm_finite_projection
    (p : Seminorm ℂ (E →Lₚₜ[ℂ] ℂ)) (hp : Continuous p) :
    ∃ (n : ℕ) (v : Fin n → (E →Lₚₜ[ℂ] ℂ)) (c : Fin n → StrongDual ℂ (E →Lₚₜ[ℂ] ℂ)),
      ∀ x, p (x - ∑ i, c i x • v i) = 0 := by
  let L := localBanachMap p hp
  obtain ⟨s, hs⟩ := weakDual_map_finite_evaluations L
  let ev : (E →Lₚₜ[ℂ] ℂ) →ₗ[ℂ] (s → ℂ) :=
    { toFun := fun φ x => φ x.val
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let S := ev.range
  let e : (E →Lₚₜ[ℂ] ℂ) →L[ℂ] S :=
    ⟨ev.rangeRestrict, (continuous_pi fun i : s =>
      (PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) ℂ i.val).continuous).subtype_mk
      (fun φ => LinearMap.mem_range_self ev φ)⟩
  obtain ⟨s₀, hs₀⟩ := ev.rangeRestrict.exists_rightInverse_of_surjective ev.range_rangeRestrict
  let B := Module.finBasis ℂ S
  let v i := s₀ (B i)
  let c i := (LinearMap.toContinuousLinearMap (B.coord i)).comp e
  refine ⟨Module.finrank ℂ S, v, c, fun x => ?_⟩
  have hv : (∑ i, c i x • v i) = s₀ (e x) := by
    simp only [c, v, ContinuousLinearMap.comp_apply, ← map_smul, ← map_sum]
    change s₀ (∑ i, B.repr (e x) i • B i) = s₀ (e x)
    rw [B.sum_repr]
  rw [hv]
  have h0 : L (x - s₀ (e x)) = 0 := by
    apply hs
    intro y hy
    have he : (x - s₀ (e x)) y = ev (x - s₀ (e x)) ⟨y, hy⟩ := rfl
    have hs' : ev.rangeRestrict (s₀ (e x)) = e x :=
      DFunLike.congr_fun hs₀ (e x)
    have he' : ev (s₀ (e x)) = ev x := congrArg Subtype.val hs'
    rw [he, map_sub, he', sub_self]
    rfl
  have hn := congrArg norm h0
  change ‖localBanachDenseMap p (x - s₀ (e x))‖ = ‖(0 : LocalBanach p)‖ at hn
  simpa only [norm_localBanachDenseMap, norm_zero] using hn

variable {F : Type*} [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
variable [PolynormableSpace ℂ F]

def seminormPolarTest (q : Seminorm ℂ F) (hq : Continuous q) : InjectiveDualTest F := by
  let hW := PolynormableSpace.withSeminorms ℂ F
  letI : IsTopologicalAddGroup F := hW.topologicalAddGroup
  letI : ContinuousSMul ℂ F := hW.continuousSMul
  let S : Set (F →Lₚₜ[ℂ] ℂ) := {φ | ∀ x, ‖φ x‖ ≤ q x}
  have hc : IsClosed S := by
    have he : S = ⋂ x : F, {φ : F →Lₚₜ[ℂ] ℂ | ‖φ x‖ ≤ q x} := by ext; simp [S]
    rw [he]
    exact isClosed_iInter fun x =>
      isClosed_le (PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) ℂ x).continuous.norm continuous_const
  have he : EquicontinuousDualSet S := by
    intro ε hε
    filter_upwards [(hq.tendsto' 0 0 (map_zero q)).eventually (Iio_mem_nhds hε)] with x hx φ hφ
    exact (hφ x).trans (le_of_lt hx)
  exact ⟨S, hc.closure_eq ▸ equicontinuousDualSet_isCompact_closure he, he⟩

private def finiteDualTest {n : ℕ} (c : Fin n → E →Lₚₜ[ℂ] ℂ) : InjectiveDualTest E where
  forms := range c
  compact := (finite_range c).isCompact
  equicontinuous := by
    intro ε hε
    apply (finite_range c).eventually_all.mpr
    intro φ _
    let φs : E →L[ℂ] ℂ := φ
    have ht : Tendsto (fun x : E => ‖φs x‖) (𝓝 0) (𝓝 (0 : ℝ)) :=
      φs.continuous.norm.tendsto' 0 0 (by rw [map_zero φs, norm_zero])
    filter_upwards [ht.eventually (Iio_mem_nhds hε)] with x hx
    exact (show ‖φs x‖ < ε from hx).le

private def firstContraction (ℓ : E →ₗ[ℂ] ℂ) : (E ⊗[ℂ] F) →ₗ[ℂ] F :=
  (TensorProduct.lid ℂ F).toLinearMap.comp (TensorProduct.map ℓ LinearMap.id)

omit [TopologicalSpace E] [TopologicalSpace F] [PolynormableSpace ℂ F] in
@[simp] private theorem firstContraction_tmul (ℓ : E →ₗ[ℂ] ℂ) (x : E) (y : F) :
    firstContraction ℓ (x ⊗ₜ[ℂ] y) = ℓ x • y := by
  simp [firstContraction]

private theorem weakDual_projective_domination
    (P : ProjectiveTensorTest (E →Lₚₜ[ℂ] ℂ) F) :
    ∃ (I : InjectiveDualTest (E →Lₚₜ[ℂ] ℂ) × InjectiveDualTest F) (C : ℝ),
      0 ≤ C ∧ ∀ w, P.tensor w ≤ C * injectiveTensorSeminorm I w := by
  classical
  let X := E →Lₚₜ[ℂ] ℂ
  obtain ⟨n, v, c, h0⟩ := weakDual_seminorm_finite_projection P.first P.first_continuous
  let tests : Fin n → X →Lₚₜ[ℂ] ℂ := fun i => c i
  let I : InjectiveDualTest X × InjectiveDualTest F :=
    (finiteDualTest tests, seminormPolarTest P.second P.second_continuous)
  letI : CompactSpace I.1.forms := isCompact_iff_compactSpace.mp I.1.compact
  letI : CompactSpace I.2.forms := isCompact_iff_compactSpace.mp I.2.compact
  let C := ∑ i, P.first (v i)
  refine ⟨I, C, Finset.sum_nonneg fun _ _ => apply_nonneg _ _, fun w => ?_⟩
  let L : X →ₗ[ℂ] X := ∑ i, (c i).toLinearMap.smulRight (v i)
  let Q := TensorProduct.map L (LinearMap.id : F →ₗ[ℂ] F)
  let R : (X ⊗[ℂ] F) →ₗ[ℂ] X ⊗[ℂ] F := LinearMap.id - Q
  have hz (z : X ⊗[ℂ] F) : P.tensor (R z) = 0 := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
      have he : R (x ⊗ₜ[ℂ] y) = (x - L x) ⊗ₜ[ℂ] y := by
        simp [R, Q, TensorProduct.sub_tmul]
      have hv : P.first (x - L x) = 0 := by
        simpa [L, LinearMap.sum_apply, LinearMap.smulRight_apply] using h0 x
      rw [he]
      apply le_antisymm _ (apply_nonneg _ _)
      simpa only [hv, zero_mul] using P.bound (x - L x) y
    | add x y hx hy =>
      rw [map_add]
      apply le_antisymm _ (apply_nonneg _ _)
      simpa only [hx, hy, add_zero] using map_add_le_add P.tensor (R x) (R y)
  have hQ (z : X ⊗[ℂ] F) :
      Q z = ∑ i, v i ⊗ₜ[ℂ] firstContraction (c i).toLinearMap z := by
    induction z using TensorProduct.induction_on with
    | zero => simp [Q]
    | tmul x y =>
      simp only [Q, TensorProduct.map_tmul, LinearMap.id_apply, L, LinearMap.sum_apply,
        LinearMap.smulRight_apply, firstContraction_tmul, ContinuousLinearMap.coe_coe,
        TensorProduct.sum_tmul, TensorProduct.smul_tmul, TensorProduct.tmul_smul]
    | add x y hx hy =>
      rw [map_add, hx, hy, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [map_add, TensorProduct.tmul_add]
  have hq (i : Fin n) : P.second (firstContraction (c i).toLinearMap w) ≤ injectiveTensorSeminorm I w := by
    let hW := PolynormableSpace.withSeminorms ℂ F
    letI : IsTopologicalAddGroup F := hW.topologicalAddGroup
    letI : ContinuousSMul ℂ F := hW.continuousSMul
    obtain ⟨ψ, hψ, hdom⟩ := seminorm_support P.second P.second_continuous
      (firstContraction (c i).toLinearMap w)
    let p : I.1.forms × I.2.forms := (⟨tests i, mem_range_self i⟩, ⟨ψ, hdom⟩)
    have he : ψ (firstContraction (c i).toLinearMap w) =
        tensorPairEvaluation I.1.forms I.2.forms w p := by
      clear hψ
      induction w using TensorProduct.induction_on with
      | zero => simp
      | tmul x y =>
        simp only [firstContraction_tmul, map_smul, tensorPairEvaluation_tmul, smul_eq_mul]
        rfl
      | add x y hx hy => simp [map_add, hx, hy]
    rw [← hψ, he]
    exact (tensorPairEvaluation I.1.forms I.2.forms w).norm_coe_le_norm p
  have hsum (f : Fin n → X ⊗[ℂ] F) (s : Finset (Fin n)) :
      P.tensor (∑ i ∈ s, f i) ≤ ∑ i ∈ s, P.tensor (f i) := by
    induction s using Finset.induction_on with
    | empty => simp
    | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      exact (map_add_le_add P.tensor _ _).trans (add_le_add le_rfl ih)
  have hw : R w + Q w = w := by simp [R]
  calc
    P.tensor w = P.tensor (R w + Q w) := congrArg P.tensor hw.symm
    _ ≤ P.tensor (R w) + P.tensor (Q w) := map_add_le_add _ _ _
    _ = P.tensor (∑ i, v i ⊗ₜ[ℂ] firstContraction (c i).toLinearMap w) := by rw [hz, zero_add, hQ]
    _ ≤ ∑ i, P.tensor (v i ⊗ₜ[ℂ] firstContraction (c i).toLinearMap w) := hsum _ _
    _ ≤ ∑ i, P.first (v i) * injectiveTensorSeminorm I w :=
      Finset.sum_le_sum fun i _ => (P.bound _ _).trans
        (mul_le_mul_of_nonneg_left (hq i) (apply_nonneg _ _))
    _ = C * injectiveTensorSeminorm I w := (Finset.sum_mul _ _ _).symm

/-- Pointwise domination of each projective seminorm by one injective test
identifies the two tensor topologies. -/
theorem tensorTopologies_equal_of_domination
    {X : Type*} [AddCommGroup X] [Module ℂ X] [TopologicalSpace X] [PolynormableSpace ℂ X]
    (hdom : ∀ P : ProjectiveTensorTest X F,
      ∃ (I : InjectiveDualTest X × InjectiveDualTest F) (C : ℝ),
        0 ≤ C ∧ ∀ z, P.tensor z ≤ C * injectiveTensorSeminorm I z) :
    projectiveTensorTopology X F = injectiveTensorTopology X F := by
  letI : TopologicalSpace (X ⊗[ℂ] F) := injectiveTensorTopology X F
  have hW : WithSeminorms (injectiveTensorSeminorm (E := X) (F := F)) := ⟨rfl⟩
  letI : IsTopologicalAddGroup (X ⊗[ℂ] F) := hW.topologicalAddGroup
  letI : ContinuousSMul ℂ (X ⊗[ℂ] F) := hW.continuousSMul
  have hproj := projectiveTensor_withSeminorms (E := X) (F := F)
  have h : Continuous[injectiveTensorTopology X F, projectiveTensorTopology X F]
      (id : X ⊗[ℂ] F → X ⊗[ℂ] F) := by
    apply (@WithSeminorms.continuous_iff_continuous_comp ℂ ℂ (X ⊗[ℂ] F) (X ⊗[ℂ] F)
      _ _ _ _ _ _ _ (RingHom.id ℂ) _ _ (injectiveTensorTopology X F) hW.topologicalAddGroup
      (projectiveTensorTopology X F) hproj LinearMap.id).mpr
    intro P
    change Continuous P.tensor
    obtain ⟨I, C, hC, hb⟩ := hdom P
    apply Seminorm.continuous (r := 1)
    have hδ : 0 < (C + 1)⁻¹ := inv_pos.mpr (by positivity)
    have ht := ((hW.continuous_seminorm I).tendsto' 0 0 (map_zero _)).eventually
      (Iio_mem_nhds hδ)
    filter_upwards [ht] with z hz
    apply P.tensor.mem_ball_zero.mpr
    change injectiveTensorSeminorm I z < (C + 1)⁻¹ at hz
    have h' := mul_le_mul_of_nonneg_left hz.le hC
    have hlt : C * (C + 1)⁻¹ < 1 := by
      rw [← div_eq_mul_inv]
      exact (div_lt_one (by positivity)).mpr (by linarith)
    exact (hb z).trans_lt (h'.trans_lt hlt)
  exact le_antisymm (continuous_id_iff_le.mp (projective_to_injective_continuous (E := X) (F := F)))
    (continuous_id_iff_le.mp h)


/-- The projective and injective topologies agree when the first factor
is a weak dual. This is the tensor-topology definition of nuclearity. -/
theorem weakDual_tensorTopologies_equal :
    projectiveTensorTopology (E →Lₚₜ[ℂ] ℂ) F =
      injectiveTensorTopology (E →Lₚₜ[ℂ] ℂ) F := by
  let X := (E →Lₚₜ[ℂ] ℂ)
  letI : PolynormableSpace ℂ X :=
    (PointwiseConvergenceCLM.withSeminorms (σ := RingHom.id ℂ) (E := E) (F := ℂ)).toPolynormableSpace
  exact tensorTopologies_equal_of_domination weakDual_projective_domination

end

end Masullo
