import NuclearSignedSums
import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap

/-!
# Nuclearity of a strong dual from bounded series covers

The signed-sum argument adapts the Apache-2.0 original proof in
`RiemannMasullo/AppC_LCTVS/Sec2b.lean` at
`23cbb63d9a34c2ae8ab0ebd86074ea4c2a056978`.
-/

open Bornology Filter Function Set Topology
open scoped NNReal

namespace Masullo

noncomputable section

universe u v

variable {E : Type u} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
  [ContinuousSMul ℂ E]

private def dualEval (x : E) : StrongDual ℂ E →ₗ[ℂ] ℂ where
  toFun f := f x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Uniform seminorm on the strong dual obtained by testing on a bounded set. -/
def strongDualBoundedSeminorm (B : {B : Set E // IsVonNBounded ℂ B}) :
    Seminorm ℂ (StrongDual ℂ E) :=
  ⨆ x : B.val, (normSeminorm ℂ ℂ).comp (dualEval (x : E))

omit [ContinuousSMul ℂ E] in
private theorem dualBounded_bddAbove (B : {B : Set E // IsVonNBounded ℂ B})
    (f : StrongDual ℂ E) : BddAbove (range fun x : B.val ↦ ‖f x‖) := by
  obtain ⟨C, hC⟩ := (NormedSpace.isVonNBounded_iff' ℂ).mp (B.property.image f)
  exact ⟨C, forall_mem_range.mpr fun x ↦ hC _ ⟨x, x.property, rfl⟩⟩

omit [ContinuousSMul ℂ E] in
theorem strongDualBoundedSeminorm_apply (B : {B : Set E // IsVonNBounded ℂ B})
    (f : StrongDual ℂ E) :
    strongDualBoundedSeminorm B f = ⨆ x : B.val, ‖f x‖ := by
  unfold strongDualBoundedSeminorm
  apply Seminorm.iSup_apply
  exact Seminorm.bddAbove_range_iff.mpr (dualBounded_bddAbove B)

omit [ContinuousSMul ℂ E] in
theorem strongDualBoundedSeminorm_dom (B : {B : Set E // IsVonNBounded ℂ B})
    (f : StrongDual ℂ E) {x : E} (hx : x ∈ B.val) : ‖f x‖ ≤ strongDualBoundedSeminorm B f := by
  rw [strongDualBoundedSeminorm_apply]
  exact le_ciSup (dualBounded_bddAbove B f) (⟨x, hx⟩ : B.val)

omit [ContinuousSMul ℂ E] in
theorem strongDual_seminorm_test_bounded [PolynormableSpace ℂ E] (p : Seminorm ℂ E) (hp : Continuous p) :
    IsVonNBounded ℂ {f : StrongDual ℂ E | ∀ x, ‖f x‖ ≤ p x} := by
  apply ContinuousLinearMap.isVonNBounded_iff.mpr
  intro S hS
  obtain ⟨C, _, hC⟩ :=
    (PolynormableSpace.withSeminorms ℂ E).isVonNBounded_iff_seminorm_bounded.mp hS ⟨p, hp⟩
  apply (NormedSpace.isVonNBounded_iff' ℂ).mpr
  refine ⟨C, ?_⟩
  rintro _ ⟨f, hf, x, hx, rfl⟩
  exact (hf x).trans (hC x hx).le

omit [ContinuousSMul ℂ E] in
theorem strongDual_withBoundedSeminorms :
    WithSeminorms (strongDualBoundedSeminorm (E := E)) := by
  let p : SeminormFamily ℂ (StrongDual ℂ E) {B : Set E // IsVonNBounded ℂ B} :=
    strongDualBoundedSeminorm
  change WithSeminorms p
  rw [p.withSeminorms_iff_nhds_eq_iInf]
  refine le_antisymm (le_iInf fun B ↦ ?_) ?_
  · rw [((Metric.nhds_basis_ball (x := (0 : ℝ))).comap (p B)).ge_iff]
    intro r hr
    rw [← (p B).ball_zero_eq_preimage_ball]
    filter_upwards [ContinuousLinearMap.eventually_nhds_zero_mapsTo B.property
      (Metric.ball_mem_nhds (0 : ℂ) (half_pos hr))] with f hf
    apply (p B).mem_ball_zero.mpr
    rw [strongDualBoundedSeminorm_apply]
    exact (Real.iSup_le (fun x ↦ (mem_ball_zero_iff.mp (hf x.property)).le)
      (half_pos hr).le).trans_lt (half_lt_self hr)
  · rw [ContinuousLinearMap.nhds_zero_eq_of_basis (Metric.nhds_basis_ball (x := (0 : ℂ)))]
    simp only [le_iInf_iff, le_principal_iff]
    intro B hB r hr
    let b : {B : Set E // IsVonNBounded ℂ B} := ⟨B, hB⟩
    refine mem_of_superset (x := (p b).ball 0 r) ?_ ?_
    · rw [(p b).ball_zero_eq_preimage_ball]
      exact mem_iInf_of_mem b (preimage_mem_comap (Metric.ball_mem_nhds (0 : ℝ) hr))
    · intro f hf x hx
      apply mem_ball_zero_iff.mpr
      refine (le_ciSup (dualBounded_bddAbove b f) (⟨x, hx⟩ : b.val)).trans_lt ?_
      rw [← strongDualBoundedSeminorm_apply]
      exact (p b).mem_ball_zero.mp hf

/-- A series cover of each bounded set of the primal space gives absolute
summability bounds for the seminorms of its strong dual. -/
theorem strongDual_nuclear_of_bounded_series_cover
    (h : ∀ B : Set E, IsVonNBounded ℂ B →
      ∃ (c : ℕ → ℂ) (x : ℕ → E), Summable (fun k ↦ ‖c k‖) ∧ IsVonNBounded ℂ (range x) ∧
        ∀ y ∈ B, ∃ a : ℕ → ℂ, (∀ k, ‖a k‖ ≤ 1) ∧ HasSum (fun k ↦ (c k * a k) • x k) y) :
    NuclearLocallyConvex.{v, u} (StrongDual ℂ E) := by
  classical
  let D := StrongDual ℂ E
  let p := strongDualBoundedSeminorm (E := E)
  have hp := strongDual_withBoundedSeminorms (E := E)
  letI : PolynormableSpace ℂ D := hp.toPolynormableSpace
  apply nuclearLocallyConvex_of_signedSum_bound
  intro q hq
  obtain ⟨s, K, _, hK⟩ := Seminorm.bound_of_continuous hp q hq
  let B := ⋃ b ∈ s, b.val
  have hB : IsVonNBounded ℂ B := by
    exact (isVonNBounded_biUnion s.finite_toSet).mpr fun b _ ↦ b.property
  obtain ⟨c, x, hc, hx, hcover⟩ := h B hB
  let W : Set D := {f | MapsTo f (range x) (Metric.ball (0 : ℂ) 1)}
  have hW : W ∈ 𝓝 (0 : D) :=
    ContinuousLinearMap.eventually_nhds_zero_mapsTo hx (Metric.ball_mem_nhds _ one_pos)
  refine ⟨W, hW, (K : ℝ) * (∑' k, ‖c k‖), by positivity, fun n f hf ↦ ?_⟩
  have hsum (k : ℕ) : ∑ i, ‖f i (x k)‖ ≤ 1 := by
    choose a ha heq using fun i : Fin n ↦ Complex.exists_norm_mul_eq_self (f i (x k))
    have ha' (i : Fin n) : a i ≠ 0 := norm_ne_zero_iff.mp (by rw [ha i]; exact one_ne_zero)
    have hphase (i : Fin n) : (a i)⁻¹ * f i (x k) = (‖f i (x k)‖ : ℂ) := by
      calc
        _ = (a i)⁻¹ * (a i * (‖f i (x k)‖ : ℂ)) := congrArg ((a i)⁻¹ * ·) (heq i).symm
        _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ (ha' i), one_mul]
    have hz := hf (fun i ↦ (a i)⁻¹) (fun i ↦ by rw [norm_inv, ha, inv_one]) (mem_range_self k)
    change (∑ i, (a i)⁻¹ • f i) (x k) ∈ Metric.ball 0 1 at hz
    rw [Metric.mem_ball, dist_zero_right] at hz
    have heval : (∑ i, (a i)⁻¹ • f i) (x k) = ((∑ i, ‖f i (x k)‖ : ℝ) : ℂ) := by
      rw [Complex.ofReal_sum]
      simp only [sum_apply, smul_apply, smul_eq_mul, hphase]
    rw [heval, Complex.norm_of_nonneg (Finset.sum_nonneg fun i _ ↦ norm_nonneg (f i (x k)))] at hz
    exact hz.le
  have hmajorant (i : Fin n) : Summable (fun k ↦ ‖c k‖ * ‖f i (x k)‖) :=
    Summable.of_nonneg_of_le (fun _ ↦ by positivity) (fun k ↦
      mul_le_of_le_one_right (norm_nonneg _) ((Finset.single_le_sum
        (fun j _ ↦ norm_nonneg (f j (x k))) (Finset.mem_univ i)).trans (hsum k))) hc
  have heval (i : Fin n) (y : E) (hy : y ∈ B) :
      ‖f i y‖ ≤ ∑' k, ‖c k‖ * ‖f i (x k)‖ := by
    obtain ⟨a, ha, hseries⟩ := hcover y hy
    have hseries' : HasSum (fun k ↦ c k * a k * f i (x k)) (f i y) := by
      convert hseries.map (f i) (f i).continuous using 1
      funext k
      exact ((f i).map_smul (c k * a k) (x k)).symm
    have hterm (k : ℕ) : ‖c k * a k * f i (x k)‖ ≤ ‖c k‖ * ‖f i (x k)‖ := by
      rw [norm_mul, norm_mul]
      exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_right (norm_nonneg _) (ha k)) (norm_nonneg _)
    have hs' := Summable.of_nonneg_of_le (fun k ↦ norm_nonneg _) hterm (hmajorant i)
    rw [← hseries'.tsum_eq]
    exact (norm_tsum_le_tsum_norm hs').trans (hs'.tsum_le_tsum hterm (hmajorant i))
  have hdom (i : Fin n) : q (f i) ≤ (K : ℝ) * ∑' k, ‖c k‖ * ‖f i (x k)‖ := by
    have hr : 0 ≤ ∑' k, ‖c k‖ * ‖f i (x k)‖ := tsum_nonneg fun _ ↦ by positivity
    have hp' : ∀ b ∈ s, p b (f i) ≤ ∑' k, ‖c k‖ * ‖f i (x k)‖ := by
      intro b hb
      rw [strongDualBoundedSeminorm_apply]
      exact Real.iSup_le (fun y ↦ heval i y.val (mem_iUnion₂.mpr ⟨b, hb, y.property⟩)) hr
    have hs' := Seminorm.finset_sup_apply_le hr hp'
    exact (hK (f i)).trans (mul_le_mul_of_nonneg_left hs' K.coe_nonneg)
  calc
    ∑ i, q (f i) ≤ ∑ i, (K : ℝ) * ∑' k, ‖c k‖ * ‖f i (x k)‖ :=
      Finset.sum_le_sum fun i _ ↦ hdom i
    _ = (K : ℝ) * ∑' k, ∑ i, ‖c k‖ * ‖f i (x k)‖ := by
      rw [← Finset.mul_sum, Summable.tsum_finsetSum fun i _ ↦ hmajorant i]
    _ ≤ _ := by
      have hle (k : ℕ) : ∑ i, ‖c k‖ * ‖f i (x k)‖ ≤ ‖c k‖ := by
        rw [← Finset.mul_sum]
        exact mul_le_of_le_one_right (norm_nonneg _) (hsum k)
      have hs' := Summable.of_nonneg_of_le (fun k ↦ Finset.sum_nonneg fun _ _ ↦ by positivity) hle hc
      exact mul_le_mul_of_nonneg_left (hs'.tsum_le_tsum hle hc) K.coe_nonneg

end

end Masullo
