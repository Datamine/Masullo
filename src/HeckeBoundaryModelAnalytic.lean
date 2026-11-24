import OscillatoryLaplace
import HeckeBoundaryEulerLimit
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Calculus.MeanValue

open Complex Filter Function MeasureTheory Metric Set
open scoped Interval Topology

namespace Masullo

noncomputable section

private def logOscGrid (n : ℕ) : ℝ := Real.log (((n+2 : ℕ) : ℝ))

private theorem logOscGrid_pos (n : ℕ) : 0 < logOscGrid n :=
  Real.log_pos (by exact_mod_cast (show 1 < n+2 by omega))

private theorem logOscGrid_mono : Monotone logOscGrid := by
  intro n m h
  exact Real.log_le_log (by positivity) (by exact_mod_cast Nat.add_le_add_right h 2)

private theorem logOscGrid_gap_le (n : ℕ) : logOscGrid (n+1) - logOscGrid n ≤ (((n+2 : ℕ) : ℝ))⁻¹ := by
  let X : ℝ := ((n+2 : ℕ) : ℝ)
  have hX : 0 < X := by positivity
  have hb : logOscGrid (n+1) = Real.log (X+1) := by
    dsimp [logOscGrid, X]
    push_cast
    ring_nf
  rw [hb, show logOscGrid n = Real.log X from rfl, ← Real.log_div (by positivity) hX.ne']
  have h := Real.log_le_sub_one_of_pos (div_pos (by positivity : 0 < X+1) hX)
  exact h.trans_eq (by rw [add_div, div_self hX.ne', add_sub_cancel_left, one_div])

/-- The local error after replacing the exponential at the left endpoint
by its value at each point of the logarithmic interval. -/
private def logOscCorrection (n : ℕ) (z : ℂ) : ℂ :=
  ∫ u in logOscGrid n..logOscGrid (n+1),
    (Complex.exp (z * (logOscGrid n : ℂ)) - Complex.exp (z * u)) / (u : ℂ)^2

private theorem logOscCorrection_eq (n : ℕ) (w : ℂ) :
    logOscCorrection n w =
      Complex.exp (w * (logOscGrid n : ℂ)) *
        (∫ u : ℝ in logOscGrid n..logOscGrid (n+1), ((u : ℂ)^2)⁻¹) -
      (∫ u : ℝ in logOscGrid n..logOscGrid (n+1), Complex.exp (w*u) / (u : ℂ)^2) := by
  let a := logOscGrid n
  let b := logOscGrid (n+1)
  have ha : 0 < a := logOscGrid_pos n
  have hab : a ≤ b := logOscGrid_mono (Nat.le_succ _)
  have hi (w : ℂ) : IntervalIntegrable (fun u : ℝ ↦ Complex.exp (w*u) / (u : ℂ)^2) volume a b :=
    (continuousOn_exp_div_sq_Icc w ha).intervalIntegrable_of_Icc hab
  have h0 : IntervalIntegrable (fun u : ℝ ↦ ((u : ℂ)^2)⁻¹) volume a b := by
    simpa [one_div] using hi 0
  unfold logOscCorrection
  change (∫ u in a..b, (Complex.exp (w*a) - Complex.exp (w*u)) / (u : ℂ)^2) = _
  simp_rw [sub_div, div_eq_mul_inv]
  rw [intervalIntegral.integral_sub (h0.const_mul _) (by simpa [div_eq_mul_inv] using hi w),
    intervalIntegral.integral_const_mul]

private theorem analyticAt_logOscCorrection (n : ℕ) (z : ℂ) :
    AnalyticAt ℂ (logOscCorrection n) z := by
  rw [funext (logOscCorrection_eq n)]
  exact ((show AnalyticAt ℂ (fun w : ℂ ↦ Complex.exp (w*(logOscGrid n : ℂ))) z from by fun_prop).fun_mul
    analyticAt_const).fun_sub (analyticAt_integral_exp_div_sq_interval (logOscGrid_pos n)
      (logOscGrid_mono (Nat.le_succ _)) z)

private theorem norm_logOscCorrection_le (n : ℕ) {z : ℂ} (hz : z.re ≤ 1/2)
    {R : ℝ} (hR : ‖z‖ ≤ R) :
    ‖logOscCorrection n z‖ ≤
      (2 * R / Real.log 2 ^ 2) * (((n+2 : ℕ) : ℝ)) ^ (-(3/2 : ℝ)) := by
  let a := logOscGrid n
  let b := logOscGrid (n+1)
  let X : ℝ := ((n+2 : ℕ) : ℝ)
  have hX : (2 : ℝ) ≤ X := by dsimp [X]; exact_mod_cast (show 2 ≤ n+2 by omega)
  have hX₀ : 0 < X := by linarith
  have ha₀ : Real.log 2 ≤ a := Real.log_le_log (by norm_num) hX
  have ha : 0 < a := logOscGrid_pos n
  have hab : a ≤ b := logOscGrid_mono (Nat.le_succ _)
  have hc : 0 ≤ b-a := sub_nonneg.mpr hab
  have hgap : b-a ≤ X⁻¹ := logOscGrid_gap_le n
  have hl₂ : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hR₀ : 0 ≤ R := (norm_nonneg _).trans hR
  have hb : b = Real.log (X+1) := by dsimp [b, logOscGrid, X]; push_cast; ring
  have hExp (u : ℝ) (hu : u ∈ Icc a b) : ‖Complex.exp (z*u)‖ ≤ 2 * X ^ (1/2 : ℝ) := by
    have hu₀ : 0 ≤ u := ha.le.trans hu.1
    rw [norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    calc
      _ ≤ Real.exp (b * (1/2 : ℝ)) := Real.exp_le_exp.mpr (by
        nlinarith [mul_le_mul_of_nonneg_right hz hu₀, hu.2])
      _ = (X+1) ^ (1/2 : ℝ) := by rw [hb, Real.rpow_def_of_pos (by positivity)]
      _ ≤ 2 * X ^ (1/2 : ℝ) := by
        have he : X+1 ≤ 4 * X := by linarith
        refine (Real.rpow_le_rpow (by positivity) he (by norm_num)).trans_eq ?_
        rw [Real.mul_rpow (by norm_num) hX₀.le, ← Real.sqrt_eq_rpow]
        norm_num
  have hdiff (u : ℝ) (hu : u ∈ Icc a b) :
      ‖Complex.exp (z*a) - Complex.exp (z*u)‖ ≤ (R*(2 * X ^ (1/2 : ℝ))) * (b-a) := by
    have hder (v : ℝ) (_ : v ∈ Icc a b) :
        HasDerivWithinAt (fun t : ℝ ↦ Complex.exp (z*t)) (z * Complex.exp (z*v)) (Icc a b) v := by
      have hd := (((hasDerivAt_id' (v : ℂ)).const_mul z).cexp).comp_ofReal
      simpa [mul_comm] using hd.hasDerivWithinAt (s := Icc a b)
    rw [norm_sub_rev]
    refine ((convex_Icc a b).norm_image_sub_le_of_norm_hasDerivWithin_le hder
      (fun v hv ↦ by rw [norm_mul]; exact mul_le_mul hR (hExp v hv) (norm_nonneg _) hR₀)
      ⟨le_rfl, hab⟩ hu).trans ?_
    rw [Real.norm_of_nonneg (sub_nonneg.mpr hu.1)]
    exact mul_le_mul_of_nonneg_left (sub_le_sub_right hu.2 _) (by positivity)
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun u : ℝ ↦ (Complex.exp (z*a) - Complex.exp (z*u)) / (u : ℂ)^2)
    (a := a) (b := b) (C := (R * (2 * X ^ (1/2 : ℝ))) * (b-a) / Real.log 2 ^ 2) (by
      intro u hu
      rw [uIoc_of_le hab] at hu
      have hu' : u ∈ Icc a b := ⟨hu.1.le, hu.2⟩
      have hu₀ : 0 ≤ u := ha.le.trans hu'.1
      rw [norm_div, norm_pow, Complex.norm_real, Real.norm_of_nonneg hu₀]
      have hsq := pow_le_pow_left₀ hl₂.le (ha₀.trans hu'.1) 2
      exact (div_le_div_of_nonneg_left (norm_nonneg _) (pow_pos hl₂ _) hsq).trans
        (div_le_div_of_nonneg_right (hdiff u hu') (by positivity)))
  rw [abs_of_nonneg hc] at hi
  change ‖∫ u in a..b, (Complex.exp (z*a) - Complex.exp (z*u)) / (u : ℂ)^2‖ ≤ _
  refine hi.trans ?_
  calc
    _ ≤ (R * (2 * X ^ (1/2 : ℝ))) * X⁻¹ / Real.log 2 ^ 2 * X⁻¹ := by gcongr
    _ = (2 * R / Real.log 2 ^ 2) * (X ^ (1/2 : ℝ) * X ^ (-(2 : ℝ))) := by
      rw [Real.rpow_neg hX₀.le, Real.rpow_two, ← inv_pow]
      ring
    _ = _ := by
      change _ = (2 * R / Real.log 2 ^ 2) * X ^ (-(3/2 : ℝ))
      rw [← Real.rpow_add hX₀]
      norm_num

private theorem summable_logOscRpow (p : ℕ) :
    Summable (fun k : ℕ ↦ (((p+k+2 : ℕ) : ℝ)) ^ (-(3/2 : ℝ))) :=
  (Real.summable_nat_rpow.mpr (by norm_num : (-(3/2 : ℝ)) < -1)).comp_injective
    (show Injective (fun k : ℕ ↦ p+k+2) by
      intro n m h
      change p+n+2 = p+m+2 at h
      omega)

private theorem analyticAt_tsum_logOscCorrection (p : ℕ) {z : ℂ} (hz : z.re < 1/2) :
    AnalyticAt ℂ (fun w ↦ ∑' k : ℕ, logOscCorrection (p+k) w) z := by
  let R := ‖z‖ + 1
  let S : Set ℂ := {w | w.re < 1/2} ∩ {w | ‖w‖ < R}
  have hS : IsOpen S :=
    (isOpen_lt Complex.continuous_re continuous_const).inter (isOpen_lt continuous_norm continuous_const)
  have hzS : z ∈ S := ⟨hz, show ‖z‖ < R from lt_add_one _⟩
  refine (differentiableOn_tsum_of_summable_norm
    ((summable_logOscRpow p).mul_left (2 * R / Real.log 2 ^ 2))
    (fun k w _ ↦ (analyticAt_logOscCorrection (p+k) w).differentiableAt.differentiableWithinAt)
    hS (fun k w hw ↦ norm_logOscCorrection_le (p+k) hw.1.le hw.2.le)).analyticOnNhd hS z hzS

private theorem integral_inv_sq_interval {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ u : ℝ in a..b, ((u : ℂ)^2)⁻¹) = ((a⁻¹ - b⁻¹ : ℝ) : ℂ) := by
  have hn : (0 : ℝ) ∉ [[a, b]] := by rw [uIcc_of_le hab]; exact fun h ↦ ha.not_ge h.1
  have he := integral_rpow (a := a) (b := b) (r := -2) (.inr ⟨by norm_num, hn⟩)
  calc
    _ = ∫ u : ℝ in a..b, ((u ^ (-2 : ℝ) : ℝ) : ℂ) := by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [uIcc_of_le hab] at hu
      have hu₀ : 0 ≤ u := ha.le.trans hu.1
      change ((u : ℂ)^2)⁻¹ = ((u ^ (-2 : ℝ) : ℝ) : ℂ)
      rw [Real.rpow_neg hu₀, Real.rpow_two, Complex.ofReal_inv, Complex.ofReal_pow]
    _ = _ := by
      rw [intervalIntegral.integral_ofReal, he]
      norm_num only [show (-2 : ℝ) + 1 = -1 by norm_num, Real.rpow_neg_one]
      congr 1
      ring

private theorem integrableOn_exp_div_sq_Ioi_left {a : ℝ} (ha : 0 < a) {z : ℂ} (hz : z.re ≤ 0) :
    IntegrableOn (fun u : ℝ ↦ Complex.exp (z*u) / (u : ℂ)^2) (Ioi a) := by
  refine (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) ha).mono' (by
    apply Measurable.aestronglyMeasurable; fun_prop) ?_
  filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioi : MeasurableSet (Ioi a))] with u hu
  have hu₀ := ha.trans hu
  rw [norm_div, norm_pow, Complex.norm_real, Real.norm_of_nonneg hu₀.le,
    norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
    Real.rpow_neg hu₀.le, Real.rpow_two, ← one_div]
  exact div_le_div_of_nonneg_right (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg hz hu₀.le))
    (by positivity)

private theorem summable_weightedLogOscExp (p : ℕ) {z : ℂ} (hz : z.re ≤ 0) :
    Summable (fun k : ℕ ↦ (heckeBoundaryLogWeight (p+k) - heckeBoundaryLogWeight (p+k+1)) •
      Complex.exp (z * (logOscGrid (p+k) : ℂ))) := by
  obtain ⟨hw, _, hwl⟩ := abelReciprocalLogWeight
  refine (hasSum_antitone_weight_diff heckeBoundaryLogWeight hw hwl p).summable.of_norm_bounded fun k ↦ ?_
  have hn : 0 ≤ heckeBoundaryLogWeight (p+k) - heckeBoundaryLogWeight (p+k+1) :=
    sub_nonneg.mpr (hw (Nat.le_succ _))
  rw [norm_smul, Real.norm_of_nonneg hn]
  apply mul_le_of_le_one_right hn
  rw [norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg hz (logOscGrid_pos _).le)

private theorem weightedLogOscExp_eq_laplace (p : ℕ) {z : ℂ} (hz : z.re ≤ 0) :
    (∑' k : ℕ, (heckeBoundaryLogWeight (p+k) - heckeBoundaryLogWeight (p+k+1)) •
      Complex.exp (z * (logOscGrid (p+k) : ℂ))) =
        oscillatoryLaplaceTail (logOscGrid p) z + ∑' k : ℕ, logOscCorrection (p+k) z := by
  let a (k : ℕ) := logOscGrid (p+k)
  let F (u : ℝ) := Complex.exp (z*u) / (u : ℂ)^2
  let b (k : ℕ) := (heckeBoundaryLogWeight (p+k) - heckeBoundaryLogWeight (p+k+1)) •
    Complex.exp (z * (a k : ℂ))
  have hi (k : ℕ) : IntervalIntegrable F volume (a k) (a (k+1)) :=
    (continuousOn_exp_div_sq_Icc z (logOscGrid_pos (p+k))).intervalIntegrable_of_Icc
      (logOscGrid_mono (Nat.add_le_add_left (Nat.le_succ k) p))
  have hlocal (k : ℕ) : b k = (∫ u in a k..a (k+1), F u) + logOscCorrection (p+k) z := by
    rw [logOscCorrection_eq, integral_inv_sq_interval (logOscGrid_pos (p+k))
      (logOscGrid_mono (Nat.le_succ _))]
    simp only [b, a, F, heckeBoundaryLogWeight, logOscGrid, Complex.real_smul,
      Nat.succ_eq_add_one, Nat.add_assoc, show 1 + 2 = (3 : ℕ) by rfl]
    ring
  have hfinite (n : ℕ) : (∑ k ∈ Finset.range n, b k) =
      (∫ u in a 0..a n, F u) + ∑ k ∈ Finset.range n, logOscCorrection (p+k) z := by
    simp_rw [hlocal, Finset.sum_add_distrib, intervalIntegral.sum_integral_adjacent_intervals (fun k _ ↦ hi k)]
  have h_a : Tendsto a atTop atTop := Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop.comp
      ((tendsto_add_atTop_nat (p+2)).congr fun n ↦ by omega))
  have hF : IntegrableOn F (Ioi (a 0)) := integrableOn_exp_div_sq_Ioi_left (logOscGrid_pos _) hz
  have hCorr : Summable (fun k : ℕ ↦ logOscCorrection (p+k) z) :=
    ((summable_logOscRpow p).mul_left (2 * ‖z‖ / Real.log 2 ^ 2)).of_norm_bounded fun k ↦
      norm_logOscCorrection_le (p+k) (hz.trans (by norm_num)) le_rfl
  have h := (intervalIntegral_tendsto_integral_Ioi (a 0) hF h_a).add hCorr.tendsto_sum_tsum_nat
  rw [oscillatoryLaplaceTail_eq_integral (logOscGrid_pos p) hz]
  exact tendsto_nhds_unique (summable_weightedLogOscExp p hz).tendsto_sum_tsum_nat
    ((h.congr fun n ↦ (hfinite n).symm) |>.congr fun _ ↦ rfl)

/-- The exact oscillatory tail has a holomorphic extension from the
imaginary axis at every nonzero displacement. -/
theorem exists_analytic_perronBoundaryModel (p : ℕ) :
    ∃ G : ℂ → ℂ, (∀ z : ℂ, z.re < 1/2 → z.im ≠ 0 → AnalyticAt ℂ G z) ∧
      ∀ z : ℂ, z.re ≤ 0 → z ≠ 0 →
        G z = -(heckeBoundaryLogWeight p • perronExponentialDifference (((p+2 : ℕ) : ℝ)) z) +
          ∑' k : ℕ, (heckeBoundaryLogWeight (p+k) - heckeBoundaryLogWeight (p+k+1)) •
            perronExponentialDifference (((p+k+2 : ℕ) : ℝ)) z := by
  let w := heckeBoundaryLogWeight
  let P (z : ℂ) := -(w p • perronExponentialDifference (((p+2 : ℕ) : ℝ)) z)
  let H (z : ℂ) := oscillatoryLaplaceTail (logOscGrid p) z + ∑' k : ℕ, logOscCorrection (p+k) z
  let G (z : ℂ) := P z + (H z - (w p : ℂ)) / z
  refine ⟨G, ?_, ?_⟩
  · intro z hz hi
    have hz₀ : z ≠ 0 := fun h ↦ hi (by simp [h])
    have hP : AnalyticAt ℂ P z := by
      simpa only [P, Complex.real_smul] using
        (analyticAt_const.fun_mul (analyticAt_perronExponentialDifference (((p+2 : ℕ) : ℝ)) z)).fun_neg
    have hH : AnalyticAt ℂ H z :=
      (analyticAt_oscillatoryLaplaceTail (logOscGrid_pos p) hi).fun_add (analyticAt_tsum_logOscCorrection p hz)
    exact hP.fun_add ((hH.fun_sub analyticAt_const).fun_div analyticAt_id hz₀)
  · intro z hz hne
    let d (k : ℕ) := w (p+k) - w (p+k+1)
    let a (k : ℕ) := d k • Complex.exp (z * (logOscGrid (p+k) : ℂ))
    obtain ⟨hw, _, hwl⟩ := abelReciprocalLogWeight
    have hd : HasSum (fun k ↦ (d k : ℂ)) (w p : ℂ) := by
      exact (hasSum_antitone_weight_diff w hw hwl p).map Complex.ofRealHom.toAddMonoidHom
        Complex.continuous_ofReal
    have ha : Summable a := summable_weightedLogOscExp p hz
    have he (k : ℕ) :
        d k • perronExponentialDifference (((p+k+2 : ℕ) : ℝ)) z = (a k - (d k : ℂ)) * z⁻¹ := by
      rw [perronExponentialDifference, ite_eq_right hne]
      simp only [a, Complex.real_smul, logOscGrid, div_eq_mul_inv]
      ring
    change P z + (H z - (w p : ℂ)) / z = P z + ∑' k, d k •
      perronExponentialDifference (((p+k+2 : ℕ) : ℝ)) z
    simp_rw [he]
    rw [tsum_mul_right, ha.tsum_sub hd.summable, hd.tsum_eq,
      show (∑' k, a k) = H z from weightedLogOscExp_eq_laplace p hz, div_eq_mul_inv]

end

end Masullo
