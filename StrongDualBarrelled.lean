import SchwartzReflexivity
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus

open Bornology Filter Function Set Topology
open scoped Pointwise

namespace Masullo

noncomputable section

variable {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
  [PolynormableSpace ℂ E]

/-- A set bounded under all continuous scalar forms is von Neumann bounded. -/
theorem isVonNBounded_of_dual_pointwise_bounded {S : Set E}
    (h : ∀ f : StrongDual ℂ E, ∃ M : ℝ, ∀ x ∈ S, ‖f x‖ ≤ M) :
    IsVonNBounded ℂ S := by
  let W := PolynormableSpace.withSeminorms ℂ E
  letI : IsTopologicalAddGroup E := W.topologicalAddGroup
  apply W.isVonNBounded_iff_seminorm_bounded.mpr
  rintro ⟨p, hp⟩
  let j := localBanachMap p hp
  let f (x : S) : StrongDual ℂ (LocalBanach p) →L[ℂ] ℂ :=
    ContinuousLinearMap.apply ℂ ℂ (j x)
  have hb (g : StrongDual ℂ (LocalBanach p)) : ∃ C, ∀ x, ‖f x g‖ ≤ C := by
    obtain ⟨C, hC⟩ := h (g.comp j)
    exact ⟨C, fun x ↦ hC x x.property⟩
  obtain ⟨M, hM⟩ := banach_steinhaus hb
  have hM' (x : E) (hx : x ∈ S) : p x ≤ M := by
    have he : ‖f ⟨x, hx⟩‖ = ‖j x‖ := by
      exact NormedSpace.inclusionInDoubleDualLi (E := LocalBanach p) ℂ |>.norm_map (j x)
    rw [show p x = ‖j x‖ from (norm_localBanachDenseMap p x).symm, ← he]
    exact hM ⟨x, hx⟩
  refine ⟨max 0 M + 1, by positivity, fun x hx ↦ ?_⟩
  exact (hM' x hx).trans_lt ((le_max_right 0 M).trans_lt (lt_add_one _))

/-- If the canonical evaluation onto the strong bidual is surjective, the
strong dual is barrelled. -/
theorem strongDual_barrelled_of_bidually_surjective [ContinuousSMul ℂ E]
    (h : Surjective (strongBidualEvaluation (E := E))) :
    BarrelledSpace ℂ (StrongDual ℂ E) := by
  let D := StrongDual ℂ E
  letI : ContinuousSMul ℂ D := strongDual_withBoundedSeminorms.continuousSMul
  letI : Module ℝ D := Module.restrictScalars ℝ ℂ D
  letI : IsScalarTower ℝ ℂ D := IsScalarTower.restrictScalars ℝ ℂ D
  letI : ContinuousSMul ℝ D := IsScalarTower.continuousSMul ℂ
  letI : LocallyConvexSpace ℝ D := strongDual_withBoundedSeminorms.toLocallyConvexSpace
  constructor
  intro q hq
  let C := q.closedBall 0 1
  let S : Set E := {x | ∀ f ∈ C, ‖f x‖ ≤ 1}
  have hC : IsClosed C := by
    rw [show C = q.closedBall 0 1 from rfl, Seminorm.closedBall_zero_eq]
    exact hq.isClosed_preimage 1
  have hC₀ : (0 : D) ∈ C := q.mem_closedBall_zero.mpr (by simp)
  have hS : IsVonNBounded ℂ S := by
    apply isVonNBounded_of_dual_pointwise_bounded
    intro f
    let M := q f + 1
    have hM : 0 < M := add_pos_of_nonneg_of_pos (apply_nonneg q f) one_pos
    refine ⟨M, fun x hx ↦ ?_⟩
    have htest : (M : ℂ)⁻¹ • f ∈ C := by
      apply q.mem_closedBall_zero.mpr
      rw [map_smul_eq_mul, norm_inv, Complex.norm_of_nonneg hM.le,
        inv_mul_le_iff₀ hM, mul_one]
      exact le_add_of_nonneg_right zero_le_one
    have hb := hx _ htest
    rw [smul_apply, norm_smul, norm_inv, Complex.norm_of_nonneg hM.le,
      inv_mul_le_iff₀ hM, mul_one] at hb
    exact hb
  let p := strongDualBoundedSeminorm ⟨S, hS⟩
  have hp : Continuous p := strongDual_withBoundedSeminorms.continuous_seminorm _
  apply Seminorm.continuous' (r := 1)
  refine mem_of_superset (p.ball_mem_nhds hp zero_lt_one) fun f hf ↦ ?_
  by_contra hfC
  obtain ⟨L, t, ht, hft⟩ :=
    RCLike.geometric_hahn_banach_closed_point (𝕜 := ℂ) (q.convex_closedBall 0 1) hC hfC
  have ht₀ : 0 < t := by simpa using ht 0 hC₀
  obtain ⟨x, hx⟩ := h L
  have hL (g : D) : L g = g x := (DFunLike.congr_fun hx g).symm
  let y := (t : ℂ)⁻¹ • x
  have hy : y ∈ S := by
    intro g hg
    obtain ⟨a, ha, he⟩ := Complex.exists_norm_mul_eq_self (g x)
    have ha₀ : a ≠ 0 := norm_ne_zero_iff.mp (ha ▸ one_ne_zero)
    have hgC : a⁻¹ • g ∈ C := by
      apply q.mem_closedBall_zero.mpr
      simpa only [map_smul_eq_mul, norm_inv, ha, inv_one, one_mul] using q.mem_closedBall_zero.mp hg
    have hb := ht _ hgC
    rw [hL, smul_apply, smul_eq_mul, ← show ((‖g x‖ : ℝ) : ℂ) = a⁻¹ * g x by
      rw [← inv_mul_cancel_left₀ ha₀ ((‖g x‖ : ℝ) : ℂ)]
      exact congrArg (a⁻¹ * ·) he] at hb
    change Complex.re ((‖g x‖ : ℝ) : ℂ) < t at hb
    rw [Complex.ofReal_re] at hb
    dsimp only [y]
    rw [map_smul, norm_smul, norm_inv, Complex.norm_of_nonneg ht₀.le, inv_mul_le_iff₀ ht₀, mul_one]
    exact hb.le
  have hfy := strongDualBoundedSeminorm_dom ⟨S, hS⟩ f hy
  have hle : ‖f x‖ ≤ t := by
    change ‖f ((t : ℂ)⁻¹ • x)‖ ≤ p f at hfy
    have hh := hfy.trans (p.mem_ball_zero.mp hf).le
    rw [map_smul, norm_smul, norm_inv, Complex.norm_of_nonneg ht₀.le, inv_mul_le_iff₀ ht₀, mul_one] at hh
    exact hh
  exact (not_lt_of_ge ((Complex.re_le_norm (L f)).trans ((hL f).symm ▸ hle))) hft

end

end Masullo
