import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

open Set Metric

namespace Masullo

/-- The open vertical strip with real parts in the specified interval. -/
def verticalStrip (a b : ℝ) : Set ℂ := Complex.re ⁻¹' Ioo a b

/-- The closed vertical strip with real parts in the specified interval. -/
def closedVerticalStrip (a b : ℝ) : Set ℂ := Complex.re ⁻¹' Icc a b

/-- D.3.1.1. Polynomially weighted bounds on interior closed substrips
persist under all complex derivatives. A fixed disk around each point
makes the estimate uniform in the imaginary direction. -/
theorem strip_weighted_iteratedDeriv_bound {a b : ℝ} (N : ℕ) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (verticalStrip a b))
    (hb : ∀ c d : ℝ, a < c → c ≤ d → d < b →
      ∃ M : ℝ, ∀ w ∈ closedVerticalStrip c d, ‖w ^ N * f w‖ ≤ M)
    (k : ℕ) (c d : ℝ) (hac : a < c) (hcd : c ≤ d) (hdb : d < b) :
    ∃ C : ℝ, ∀ z ∈ closedVerticalStrip c d, ‖z ^ N * iteratedDeriv k f z‖ ≤ C := by
  let R := min (c - a) (b - d) / 4
  have hR : 0 < R := div_pos (lt_min (sub_pos.mpr hac) (sub_pos.mpr hdb)) (by norm_num)
  have hL : a < c - 2 * R := by
    have h := min_le_left (c - a) (b - d)
    dsimp [R]
    linarith
  have hU : d + 2 * R < b := by
    have h := min_le_right (c - a) (b - d)
    dsimp [R]
    linarith
  let S := closedVerticalStrip (c - 2 * R) (d + 2 * R)
  have hS : S ⊆ verticalStrip a b := fun _ h => ⟨hL.trans_le h.1, h.2.trans_lt hU⟩
  obtain ⟨M, hM⟩ := hb _ _ hL (by linarith) hU
  have hK : IsCompact (closedBall (0 : ℂ) (3 * R) ∩ S) :=
    (isCompact_closedBall _ _).inter_right (isClosed_Icc.preimage Complex.continuous_re)
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn
    (hf.continuousOn.mono (inter_subset_right.trans hS))
  let A := max ((2 * R) ^ N * max 0 B) (2 ^ N * max 0 M)
  refine ⟨k.factorial * A / R ^ k, fun z hz => ?_⟩
  have hDisk : closedBall z R ⊆ S := by
    intro w hw
    have hr : |w.re - z.re| ≤ R := by
      have h := (Complex.abs_re_le_norm (w - z)).trans (mem_closedBall_iff_norm.mp hw)
      simpa only [Complex.sub_re] using h
    have hl := (abs_le.mp hr).1
    have hu := (abs_le.mp hr).2
    change c - 2 * R ≤ w.re ∧ w.re ≤ d + 2 * R
    exact ⟨by linarith [hz.1], by linarith [hz.2]⟩
  have hdiff : DiffContOnCl ℂ (fun w => z ^ N * f w) (ball z R) :=
    (hf.const_mul (z ^ N)).diffContOnCl_ball (hDisk.trans hS)
  have hnorm (w : ℂ) (hw : w ∈ sphere z R) : ‖z ^ N * f w‖ ≤ A := by
    have hwS := hDisk (sphere_subset_closedBall hw)
    have hwDist : ‖w - z‖ = R := mem_sphere_iff_norm.mp hw
    by_cases hzsmall : ‖z‖ ≤ 2 * R
    · have hwsmall : w ∈ closedBall (0 : ℂ) (3 * R) := by
        rw [mem_closedBall, dist_zero_right]
        have h := norm_add_le (w - z) z
        rw [sub_add_cancel, hwDist] at h
        linarith
      rw [norm_mul, norm_pow]
      apply le_trans _ (le_max_left _ _)
      exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hzsmall _)
        ((hB _ ⟨hwsmall, hwS⟩).trans (le_max_right _ _)) (norm_nonneg _)
        (pow_nonneg (by positivity) _)
    · have hzle : ‖z‖ ≤ 2 * ‖w‖ := by
        have h := norm_add_le (z - w) w
        rw [sub_add_cancel, norm_sub_rev, hwDist] at h
        linarith
      rw [norm_mul, norm_pow]
      calc
        ‖z‖ ^ N * ‖f w‖ ≤ (2 * ‖w‖) ^ N * ‖f w‖ :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hzle _) (norm_nonneg _)
        _ = 2 ^ N * ‖w ^ N * f w‖ := by rw [mul_pow, norm_mul, norm_pow, mul_assoc]
        _ ≤ 2 ^ N * max 0 M :=
          mul_le_mul_of_nonneg_left ((hM _ hwS).trans (le_max_right _ _)) (by positivity)
        _ ≤ A := le_max_right _ _
  have hh := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k hR hdiff hnorm
  rw [iteratedDeriv_const_mul_field] at hh
  exact hh

/-- A proper subinterval can share the boundary of the original strip.
The function `exp (-1/z)` is bounded on the whole right strip, whereas
its derivative is unbounded on the proper substrip with the same left edge. -/
theorem strip_derivative_shared_boundary_obstruction :
    let f : ℂ → ℂ := fun z => Complex.exp (-z⁻¹)
    DifferentiableOn ℂ f (verticalStrip 0 1) ∧
      (∀ z ∈ verticalStrip 0 1, ‖f z‖ ≤ 1) ∧
      ¬ ∃ M : ℝ, ∀ z ∈ verticalStrip 0 (1 / 2), ‖deriv f z‖ ≤ M := by
  let f : ℂ → ℂ := fun z => Complex.exp (-z⁻¹)
  change DifferentiableOn ℂ f (verticalStrip 0 1) ∧
      (∀ z ∈ verticalStrip 0 1, ‖f z‖ ≤ 1) ∧
      ¬ ∃ M : ℝ, ∀ z ∈ verticalStrip 0 (1 / 2), ‖deriv f z‖ ≤ M
  have hd {z : ℂ} (hz : z ≠ 0) : HasDerivAt f (f z * (z ^ 2)⁻¹) z := by
    simpa [f] using (hasDerivAt_inv hz).neg.cexp
  refine ⟨fun z hz => (hd (fun h => ?_)).differentiableAt.differentiableWithinAt, ?_, ?_⟩
  · exact (not_lt_of_ge (by simp [h])) hz.1
  · intro z hz
    change ‖Complex.exp (-z⁻¹)‖ ≤ 1
    rw [Complex.norm_exp, Complex.neg_re, ← Real.exp_zero]
    exact Real.exp_le_exp.mpr (neg_nonpos.mpr (by
      rw [Complex.inv_re]
      exact div_nonneg hz.1.le (Complex.normSq_nonneg _)))
  · rintro ⟨M, hM⟩
    let r := max 2 (M / Real.exp (-1) + 1)
    have hr : 2 ≤ r := le_max_left _ _
    let w := (1 : ℂ) + (r : ℂ) * Complex.I
    have hwre : w.re = 1 := by simp [w, Complex.mul_re]
    have hwim : w.im = r := by simp [w, Complex.mul_im]
    have hw : w ≠ 0 := by
      intro h
      simp [h] at hwre
    have hn : Complex.normSq w = 1 + r ^ 2 := by
      rw [Complex.normSq_apply, hwre, hwim]
      ring
    let z := w⁻¹
    have hz : z ∈ verticalStrip 0 (1 / 2) := by
      change 0 < z.re ∧ z.re < (1 / 2 : ℝ)
      rw [show z.re = 1 / (1 + r ^ 2) from by rw [Complex.inv_re, hwre, hn]]
      constructor
      · positivity
      · have hr2 : 2 < 1 + r ^ 2 := by nlinarith
        exact (div_lt_iff₀ (by positivity)).mpr (by linarith)
    have hderiv : ‖deriv f z‖ = Real.exp (-1) * (1 + r ^ 2) := by
      rw [(hd (inv_ne_zero hw)).deriv]
      change ‖Complex.exp (-(w⁻¹)⁻¹) * ((w⁻¹) ^ 2)⁻¹‖ = _
      rw [inv_inv, inv_pow, inv_inv, norm_mul, Complex.norm_exp, Complex.neg_re, hwre,
        norm_pow, ← Complex.normSq_eq_norm_sq, hn]
    have hrM : M / Real.exp (-1) < r := lt_of_lt_of_le (lt_add_one _) (le_max_right _ _)
    have hr' : r ≤ 1 + r ^ 2 := by nlinarith
    have hne := (div_lt_iff₀ (Real.exp_pos (-1))).mp (hrM.trans_le hr')
    have h := hM z hz
    rw [hderiv] at h
    exact (by simpa [mul_comm] using hne : M < Real.exp (-1) * (1 + r ^ 2)).not_ge h

end Masullo
