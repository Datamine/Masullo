import RectangleResidue
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Truncated Perron inversion with the half weight at the cutoff. -/

noncomputable section

open Complex Filter MeasureTheory Set
open scoped Interval Topology

namespace Masullo

private def edgePoint (x y : ℝ) : ℂ := (x : ℂ) + (y : ℂ) * I

private def perronIntegrand (b : ℝ) (z : ℂ) : ℂ := Complex.exp ((b : ℂ) * z) / z

/-- The vertical Perron kernel, with the contour factor absorbed by its ordinate. -/
def truncatedPerron (b c T : ℝ) : ℂ :=
  (∫ y in -T..T, perronIntegrand b (edgePoint c y)) / (2 * (Real.pi : ℂ))

/-- Perron assigns half the coefficient to an index exactly at the cutoff. -/
def perronStep (b : ℝ) : ℝ := if 0 < b then 1 else if b = 0 then 1 / 2 else 0

private theorem edgePoint_re (x y : ℝ) : (edgePoint x y).re = x := by simp [edgePoint]

private theorem edgePoint_im (x y : ℝ) : (edgePoint x y).im = y := by simp [edgePoint]

private theorem edgePoint_ne_zero_re {x y : ℝ} (hx : x ≠ 0) : edgePoint x y ≠ 0 :=
  fun h ↦ hx (by simpa [edgePoint_re] using congrArg Complex.re h)

private theorem edgePoint_ne_zero_im {x y : ℝ} (hy : y ≠ 0) : edgePoint x y ≠ 0 :=
  fun h ↦ hy (by simpa [edgePoint_im] using congrArg Complex.im h)

private theorem norm_perronIntegrand (b x y : ℝ) :
    ‖perronIntegrand b (edgePoint x y)‖ = Real.exp (b * x) / ‖edgePoint x y‖ := by
  simp [perronIntegrand, Complex.norm_exp, Complex.mul_re, edgePoint_re]

private theorem perronHorizontal_bound (b l r y : ℝ) (hlr : l ≤ r) (hb : b ≠ 0)
    (hy : y ≠ 0) :
    ‖∫ x in l..r, perronIntegrand b (edgePoint x y)‖ ≤
      (Real.exp (b * r) - Real.exp (b * l)) / b / |y| := by
  have hcn : Continuous (fun x ↦ perronIntegrand b (edgePoint x y)) := by
    unfold perronIntegrand
    have hc : Continuous (fun x : ℝ ↦ edgePoint x y) := by unfold edgePoint; fun_prop
    exact (continuous_const.mul hc).cexp.div hc (fun _ ↦ edgePoint_ne_zero_im hy)
  have hExp : Continuous (fun x : ℝ ↦ Real.exp (b * x) / |y|) := by fun_prop
  calc
    _ ≤ ∫ x in l..r, ‖perronIntegrand b (edgePoint x y)‖ :=
      intervalIntegral.norm_integral_le_integral_norm hlr
    _ ≤ ∫ x in l..r, Real.exp (b * x) / |y| := by
      apply intervalIntegral.integral_mono_on hlr (hcn.norm.intervalIntegrable l r) (hExp.intervalIntegrable l r)
      intro x _
      rw [norm_perronIntegrand]
      exact div_le_div_of_nonneg_left (Real.exp_pos _).le (abs_pos.mpr hy)
        (by simpa only [edgePoint_im] using Complex.abs_im_le_norm (edgePoint x y))
    _ = _ := by
      rw [intervalIntegral.integral_div]
      have h := integral_exp_mul_complex (a := l) (b := r) (Complex.ofReal_ne_zero.mpr hb)
      apply congrArg (fun r : ℝ ↦ r / |y|)
      apply Complex.ofReal_injective
      rw [← intervalIntegral.integral_ofReal]
      simpa only [Complex.ofReal_exp, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_div] using h

private theorem perronVertical_bound (b c T : ℝ) (hT : 0 < T) (hc : c ≠ 0) :
    ‖∫ y in -T..T, perronIntegrand b (edgePoint c y)‖ ≤
      2 * T * (Real.exp (b * c) / |c|) := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := -T) (b := T) (C := Real.exp (b * c) / |c|)
    (f := fun y ↦ perronIntegrand b (edgePoint c y)) (fun y _ ↦ by
      rw [norm_perronIntegrand]
      exact div_le_div_of_nonneg_left (Real.exp_pos _).le (abs_pos.mpr hc)
        (by simpa only [edgePoint_re] using Complex.abs_re_le_norm (edgePoint c y)))
  rw [show |T - -T| = 2 * T by rw [abs_of_nonneg (by linarith)]; ring] at h
  simpa only [mul_comm] using h

private theorem perronRectangle_eq (b l r T : ℝ) (hT : 0 < T) (hl : l < 0) (hr : 0 < r) :
    rectIntegral (perronIntegrand b) l r (-T) T = 2 * Real.pi * I := by
  unfold perronIntegrand
  simpa using (rectIntegral_cauchy
    (f := fun z : ℂ ↦ Complex.exp ((b : ℂ) * z)) (p := 0) (n := 0)
    (by simpa using hl) (by simpa using hr) (by simp [hT]) (by simp [hT])
    (fun z _ ↦ analyticAt_cexp.comp (analyticAt_const.mul analyticAt_id)))

private theorem perronRectangle_zero (b l r T : ℝ) (hl : 0 < l) (hlr : l ≤ r) :
    rectIntegral (perronIntegrand b) l r (-T) T = 0 := by
  apply rectIntegral_eq_zero_of_differentiableOn
  intro z hz
  have hzr : 0 < z.re := hl.trans_le (by
    rw [Complex.mem_reProdIm, uIcc_of_le hlr] at hz
    exact hz.1.1)
  have hz0 : z ≠ 0 := fun he ↦ by simp [he] at hzr
  exact ((differentiableAt_const (b : ℂ)).mul differentiableAt_id).cexp.div differentiableAt_id hz0
    |>.differentiableWithinAt

private theorem perronPositive_bound {b c T : ℝ} (hb : 0 < b) (hc : 0 < c) (hT : 0 < T) :
    ‖truncatedPerron b c T - 1‖ ≤ Real.exp (b * c) / (Real.pi * T * b) := by
  let V (x : ℝ) := ∫ y in -T..T, perronIntegrand b (edgePoint x y)
  let D : ℂ := 2 * (Real.pi : ℂ)
  have hD : D ≠ 0 := mul_ne_zero (by norm_num) (ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hDnorm : ‖D‖ = 2 * Real.pi := by simp [D, Real.pi_pos.le]
  have hmain (x : ℝ) (hx : x ≤ -1) :
      ‖V c - D‖ ≤ 2 * (Real.exp (b * c) / b / T) + 2 * T * Real.exp (b * x) := by
    have hx0 : x < 0 := by linarith
    have hxc : x ≤ c := by linarith
    let H (y : ℝ) := ∫ r in x..c, perronIntegrand b (edgePoint r y)
    have hR := perronRectangle_eq b x c T hT hx0 hc
    rw [rectIntegral_eq_edges] at hR
    change H (-T) - H T + I * V c - I * V x = D * I at hR
    have he : I * (V c - D) = H T - H (-T) + I * V x := by linear_combination hR
    have hnorm : ‖V c - D‖ = ‖H T - H (-T) + I * V x‖ := by
      rw [← he, norm_mul, norm_I, one_mul]
    have hH (y : ℝ) (hy : |y| = T) : ‖H y‖ ≤ Real.exp (b * c) / b / T := by
      have hy0 : y ≠ 0 := by intro h; simp [h] at hy; linarith
      refine (perronHorizontal_bound b x c y hxc hb.ne' hy0).trans ?_
      rw [hy]
      exact div_le_div_of_nonneg_right
        (div_le_div_of_nonneg_right (sub_le_self _ (Real.exp_pos _).le) (by positivity)) hT.le
    have hV := perronVertical_bound b x T hT hx0.ne
    have hAbs : 1 ≤ |x| := by rw [abs_of_neg hx0]; linarith
    have hv : ‖V x‖ ≤ 2 * T * Real.exp (b * x) :=
      hV.trans (mul_le_mul_of_nonneg_left
        (div_le_self (Real.exp_pos _).le hAbs) (by positivity))
    rw [hnorm]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_I, one_mul]
    linarith [norm_sub_le (H T) (H (-T)), hH T (abs_of_pos hT), hH (-T) (by simp [hT.le])]
  have hxExp : Tendsto (fun x : ℝ ↦ Real.exp (b * x)) atBot (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atBot hb)
  have hlim : Tendsto (fun x : ℝ ↦ 2 * (Real.exp (b * c) / b / T) + 2 * T * Real.exp (b * x))
      atBot (𝓝 (2 * (Real.exp (b * c) / b / T))) := by
    simpa using tendsto_const_nhds.add (hxExp.const_mul (2 * T))
  have hbound : ‖V c - D‖ ≤ 2 * (Real.exp (b * c) / b / T) :=
    ge_of_tendsto hlim ((eventually_le_atBot (-1 : ℝ)).mono hmain)
  change ‖V c / D - 1‖ ≤ _
  rw [← div_self hD, ← sub_div, norm_div, hDnorm]
  calc
    _ ≤ (2 * (Real.exp (b * c) / b / T)) / (2 * Real.pi) :=
      div_le_div_of_nonneg_right hbound (by positivity)
    _ = _ := by ring

private theorem perronNegative_bound {b c T : ℝ} (hb : b < 0) (hc : 0 < c) (hT : 0 < T) :
    ‖truncatedPerron b c T‖ ≤ Real.exp (b * c) / (Real.pi * T * (-b)) := by
  let V (x : ℝ) := ∫ y in -T..T, perronIntegrand b (edgePoint x y)
  let D : ℂ := 2 * (Real.pi : ℂ)
  have hDnorm : ‖D‖ = 2 * Real.pi := by simp [D, Real.pi_pos.le]
  have hmain (x : ℝ) (hx : max c 1 ≤ x) :
      ‖V c‖ ≤ 2 * (Real.exp (b * c) / (-b) / T) + 2 * T * Real.exp (b * x) := by
    have hxc := (le_max_left c 1).trans hx
    have hx1 := (le_max_right c 1).trans hx
    have hx0 := zero_lt_one.trans_le hx1
    let H (y : ℝ) := ∫ r in c..x, perronIntegrand b (edgePoint r y)
    have hR := perronRectangle_zero b c x T hc hxc
    rw [rectIntegral_eq_edges] at hR
    change H (-T) - H T + I * V x - I * V c = 0 at hR
    have he : I * V c = H (-T) - H T + I * V x := by linear_combination -hR
    have hnorm : ‖V c‖ = ‖H (-T) - H T + I * V x‖ := by
      rw [← he, norm_mul, norm_I, one_mul]
    have hH (y : ℝ) (hy : |y| = T) : ‖H y‖ ≤ Real.exp (b * c) / (-b) / T := by
      have hy0 : y ≠ 0 := by intro h; simp [h] at hy; linarith
      refine (perronHorizontal_bound b c x y hxc hb.ne hy0).trans ?_
      rw [hy, ← neg_div_neg_eq (Real.exp (b * x) - Real.exp (b * c)) b, neg_sub]
      exact div_le_div_of_nonneg_right
        (div_le_div_of_nonneg_right (sub_le_self _ (Real.exp_pos _).le) (neg_nonneg.mpr hb.le)) hT.le
    have hV := perronVertical_bound b x T hT hx0.ne'
    have hv : ‖V x‖ ≤ 2 * T * Real.exp (b * x) :=
      hV.trans (mul_le_mul_of_nonneg_left
        (div_le_self (Real.exp_pos _).le (by rwa [abs_of_pos hx0])) (by positivity))
    rw [hnorm]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_I, one_mul]
    linarith [norm_sub_le (H (-T)) (H T), hH T (abs_of_pos hT), hH (-T) (by simp [hT.le])]
  have hxExp : Tendsto (fun x : ℝ ↦ Real.exp (b * x)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg hb)
  have hlim : Tendsto (fun x : ℝ ↦ 2 * (Real.exp (b * c) / (-b) / T) + 2 * T * Real.exp (b * x))
      atTop (𝓝 (2 * (Real.exp (b * c) / (-b) / T))) := by
    simpa using tendsto_const_nhds.add (hxExp.const_mul (2 * T))
  have hbound : ‖V c‖ ≤ 2 * (Real.exp (b * c) / (-b) / T) :=
    ge_of_tendsto hlim ((eventually_ge_atTop (max c 1)).mono hmain)
  change ‖V c / D‖ ≤ _
  rw [norm_div, hDnorm]
  calc
    _ ≤ (2 * (Real.exp (b * c) / (-b) / T)) / (2 * Real.pi) :=
      div_le_div_of_nonneg_right hbound (by positivity)
    _ = _ := by ring

/-- The two off-cutoff Perron bounds, uniform in the logarithmic ratio. -/
theorem truncatedPerron_error_of_ne_zero {b c T : ℝ} (hb : b ≠ 0) (hc : 0 < c) (hT : 0 < T) :
    ‖truncatedPerron b c T - (perronStep b : ℂ)‖ ≤
      Real.exp (b * c) / (Real.pi * T * |b|) := by
  rcases hb.lt_or_gt with hb | hb
  · simpa [perronStep, hb.not_gt, hb.ne, abs_of_neg hb] using perronNegative_bound hb hc hT
  · simpa [perronStep, hb, abs_of_pos hb] using perronPositive_bound hb hc hT

private theorem truncatedPerron_zero_eq {c T : ℝ} (hc : 0 < c) :
    truncatedPerron 0 c T = (Real.arctan (T / c) / Real.pi : ℝ) := by
  let V (y : ℝ) := (edgePoint c y)⁻¹
  have hV : Continuous V := by
    have h : Continuous (fun y ↦ edgePoint c y) := by unfold edgePoint; fun_prop
    exact h.inv₀ (fun _ ↦ edgePoint_ne_zero_re hc.ne')
  have hsym : ∫ y in -T..T, V (-y) = ∫ y in -T..T, V y := by
    rw [intervalIntegral.integral_comp_neg, neg_neg]
  have hsum (y : ℝ) : V y + V (-y) = ((2 * c / (c ^ 2 + y ^ 2) : ℝ) : ℂ) := by
    have hc' : (c : ℂ) + (y : ℂ) * I ≠ 0 := edgePoint_ne_zero_re hc.ne'
    have hc'' : (c : ℂ) - (y : ℂ) * I ≠ 0 := by
      simpa [edgePoint, sub_eq_add_neg] using (edgePoint_ne_zero_re (y := -y) hc.ne')
    simp only [V, edgePoint, Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_mul,
      Complex.ofReal_ofNat, Complex.ofReal_add, Complex.ofReal_pow, neg_mul, ← sub_eq_add_neg]
    have hden : (c : ℂ)^2 + (y : ℂ)^2 ≠ 0 := by
      exact_mod_cast (show c^2 + y^2 ≠ 0 by positivity)
    field_simp [hc', hc'', hden]
    linear_combination (2 * (c : ℂ) * (y : ℂ)^2) * Complex.I_sq
  have hi := intervalIntegral.integral_add (hV.intervalIntegrable (μ := volume) (-T) T)
    ((hV.comp continuous_neg).intervalIntegrable (μ := volume) (-T) T)
  change (∫ y in -T..T, V y + V (-y)) = _ at hi
  simp_rw [hsum] at hi
  simp only [Function.comp_apply] at hi
  rw [hsym, ← two_mul] at hi
  have hR : (∫ y : ℝ in -T..T, 2 * c / (c ^ 2 + y ^ 2)) = 4 * Real.arctan (T / c) := by
    have hder (y : ℝ) : HasDerivAt (fun y : ℝ ↦ 2 * Real.arctan (y / c))
        (2 * c / (c ^ 2 + y ^ 2)) y := by
      have hder := ((Real.hasDerivAt_arctan (y / c)).comp y ((hasDerivAt_id y).div_const c)).const_mul 2
      have hcoeff : 2 * ((1 / (1 + (y / c) ^ 2)) * (1 / c)) = 2 * c / (c ^ 2 + y ^ 2) := by
        field_simp
      change HasDerivAt _ (2 * ((1 / (1 + (y / c) ^ 2)) * (1 / c))) y at hder
      rw [hcoeff] at hder
      exact hder
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ ↦ hder y)]
    · rw [neg_div, Real.arctan_neg]
      ring
    · apply Continuous.intervalIntegrable
      apply continuous_const.div (by fun_prop)
      intro y
      positivity
  have H : (∫ y in -T..T, V y) = (2 * (Real.arctan (T / c) : ℂ)) := by
    rw [intervalIntegral.integral_ofReal, hR] at hi
    push_cast at hi
    linear_combination -(1 / 2 : ℂ) * hi
  have hk : (fun y ↦ perronIntegrand 0 (edgePoint c y)) = V := by
    funext y
    simp [perronIntegrand, V]
  rw [truncatedPerron, hk, H]
  push_cast
  ring

private theorem arctan_le_id_nonneg {x : ℝ} (hx : 0 ≤ x) : Real.arctan x ≤ x := by
  have h := intervalIntegral.integral_mono_on (μ := volume) hx
    ((show Continuous (fun y : ℝ ↦ 1 / (1 + y ^ 2)) by
      exact continuous_const.div (by fun_prop) (fun y ↦ by positivity)).intervalIntegrable 0 x)
    (intervalIntegrable_const (c := (1 : ℝ))) (fun y _ ↦
      div_le_one_of_le₀ (by nlinarith [sq_nonneg y]) (by positivity))
  simpa [integral_one_div_one_add_sq] using h

/-- At the cutoff the exact arctangent error is bounded by c/(π T). -/
theorem truncatedPerron_error_zero {c T : ℝ} (hc : 0 < c) (hT : 0 < T) :
    ‖truncatedPerron 0 c T - (perronStep 0 : ℂ)‖ ≤ c / (Real.pi * T) := by
  rw [truncatedPerron_zero_eq hc]
  have hrec := Real.arctan_inv_of_pos (div_pos hT hc)
  have hrecip : (T / c)⁻¹ = c / T := inv_div T c
  rw [hrecip] at hrec
  simp only [perronStep, lt_irrefl, ite_false, ite_true]
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have hpos : 0 ≤ Real.arctan (c / T) / Real.pi :=
    div_nonneg (Real.arctan_nonneg.mpr (div_nonneg hc.le hT.le)) Real.pi_pos.le
  have heq : Real.arctan (T / c) / Real.pi - 1 / 2 = -(Real.arctan (c / T) / Real.pi) := by
    rw [hrec]
    field_simp
    ring
  rw [heq, abs_neg, abs_of_nonneg hpos]
  calc
    _ ≤ (c / T) / Real.pi :=
      div_le_div_of_nonneg_right (arctan_le_id_nonneg (div_nonneg hc.le hT.le)) Real.pi_pos.le
    _ = _ := by ring

/-- The coefficient-wise bound on the truncated inversion error. -/
def perronError (b c T : ℝ) : ℝ :=
  if b = 0 then c / (Real.pi * T) else Real.exp (b * c) / (Real.pi * T * |b|)

theorem perronError_nonneg (b : ℝ) {c T : ℝ} (hc : 0 < c) (hT : 0 < T) :
    0 ≤ perronError b c T := by
  unfold perronError
  split <;> positivity

private theorem truncatedPerron_error (b : ℝ) {c T : ℝ} (hc : 0 < c) (hT : 0 < T) :
    ‖truncatedPerron b c T - (perronStep b : ℂ)‖ ≤ perronError b c T := by
  by_cases hb : b = 0
  · subst b
    simpa [perronError] using truncatedPerron_error_zero hc hT
  · simpa [perronError, hb] using truncatedPerron_error_of_ne_zero hb hc hT

private theorem lseriesTerm_realShift (a : ℕ → ℂ) (s w : ℂ) (n : ℕ) :
    LSeries.term a (s + w) n = LSeries.term a s n * Complex.exp (-w * Real.log n) := by
  by_cases hn : n = 0
  · simp [hn]
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hlog : Complex.log (n : ℂ) = (Real.log n : ℂ) := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg n)]
  simp only [LSeries.term_def, hn, ite_false, Complex.cpow_def_of_ne_zero hn', hlog,
    div_eq_mul_inv, ← Complex.exp_neg]
  rw [mul_assoc, ← Complex.exp_add]
  congr 2
  ring

private theorem lseriesPerronTerm_eq (a : ℕ → ℂ) (s w : ℂ) (x : ℝ) (n : ℕ) :
    LSeries.term a (s + w) n * perronIntegrand (Real.log x) w =
      LSeries.term a s n * perronIntegrand (Real.log x - Real.log n) w := by
  rw [lseriesTerm_realShift]
  unfold perronIntegrand
  rw [mul_assoc, ← mul_div_assoc, ← Complex.exp_add]
  congr 3
  push_cast
  ring

private theorem norm_lseriesShiftExponential (w : ℂ) (n : ℕ) :
    ‖Complex.exp (-w * (Real.log n : ℂ))‖ = Real.exp (-(w.re * Real.log n)) := by
  rw [Complex.norm_exp, Complex.mul_re, Complex.neg_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero, neg_mul]

private theorem norm_lseriesTerm_perron (a : ℕ → ℂ) (s : ℂ) (x c y : ℝ) (hc : 0 < c) (n : ℕ) :
    ‖LSeries.term a s n * perronIntegrand (Real.log x - Real.log n) (edgePoint c y)‖ ≤
      (Real.exp (Real.log x * c) / c) * ‖LSeries.term a (s + (c : ℂ)) n‖ := by
  rw [norm_mul, norm_perronIntegrand, lseriesTerm_realShift, norm_mul, norm_lseriesShiftExponential, Complex.ofReal_re]
  have he : Real.exp ((Real.log x - Real.log n) * c) =
      Real.exp (Real.log x * c) * Real.exp (-(c * Real.log n)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hden : c ≤ ‖edgePoint c y‖ := by
    simpa [edgePoint_re, abs_of_pos hc] using Complex.abs_re_le_norm (edgePoint c y)
  rw [he]
  calc
    _ ≤ ‖LSeries.term a s n‖ * ((Real.exp (Real.log x * c) * Real.exp (-(c * Real.log n))) / c) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left (by positivity) hc hden) (norm_nonneg _)
    _ = _ := by ring

private theorem lseriesPerronContour (a : ℕ → ℂ) (s : ℂ) (x c T : ℝ) (hc : 0 < c)
    (ha : Summable (fun n ↦ ‖LSeries.term a (s + (c : ℂ)) n‖)) :
    HasSum (fun n ↦ LSeries.term a s n * truncatedPerron (Real.log x - Real.log n) c T)
      ((∫ y in -T..T, LSeries a (s + edgePoint c y) *
        perronIntegrand (Real.log x) (edgePoint c y)) / (2 * (Real.pi : ℂ))) := by
  let F (n : ℕ) (y : ℝ) :=
    LSeries.term a s n * perronIntegrand (Real.log x - Real.log n) (edgePoint c y)
  let M (n : ℕ) := (Real.exp (Real.log x * c) / c) * ‖LSeries.term a (s + (c : ℂ)) n‖
  have hM : Summable M := ha.mul_left _
  have hF (n : ℕ) : Continuous (F n) := by
    have h : Continuous (fun y ↦ edgePoint c y) := by unfold edgePoint; fun_prop
    unfold F perronIntegrand
    exact continuous_const.mul ((continuous_const.mul h).cexp.div h
      (fun _ ↦ edgePoint_ne_zero_re hc.ne'))
  have hpoint (y : ℝ) :
      HasSum (F · y) (LSeries a (s + edgePoint c y) * perronIntegrand (Real.log x) (edgePoint c y)) := by
    have hsum : Summable (LSeries.term a (s + edgePoint c y)) := by
      refine ha.of_norm_bounded (fun n ↦ ?_)
      rw [lseriesTerm_realShift, lseriesTerm_realShift, norm_mul, norm_mul,
        norm_lseriesShiftExponential, norm_lseriesShiftExponential, edgePoint_re, Complex.ofReal_re]
    have hEq : (fun n ↦ F n y) =
        fun n ↦ LSeries.term a (s + edgePoint c y) n *
          perronIntegrand (Real.log x) (edgePoint c y) :=
      funext fun n ↦ (lseriesPerronTerm_eq a s (edgePoint c y) x n).symm
    rw [hEq]
    exact hsum.hasSum.mul_right _
  have hi := intervalIntegral.hasSum_integral_of_dominated_convergence
    (a := -T) (b := T) (μ := volume) (F := F)
    (fun n (_ : ℝ) ↦ M n) (fun n ↦ (hF n).aestronglyMeasurable)
    (fun n ↦ Eventually.of_forall fun y _ ↦ norm_lseriesTerm_perron a s x c y hc n)
    (Eventually.of_forall fun _ _ ↦ hM) intervalIntegrable_const
    (Eventually.of_forall fun y _ ↦ hpoint y)
  have heq : (fun n ↦ LSeries.term a s n * truncatedPerron (Real.log x - Real.log n) c T) =
      fun n ↦ (∫ y in -T..T, F n y) / (2 * (Real.pi : ℂ)) := by
    funext n
    simp only [truncatedPerron, F, intervalIntegral.integral_const_mul, mul_div_assoc]
  rw [heq]
  exact hi.div_const _

private theorem eventually_farPerronIndices (x : ℝ) :
    ∀ᶠ n : ℕ in atTop, Real.log x + 1 ≤ Real.log (n : ℝ) :=
  (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop _

/-- Comparison of logarithms recovers the strict cutoff and the half weight
at an integer. The zeroth L-series term is already zero. -/
theorem perronStep_log_cutoff {x : ℝ} (hx : 0 < x) {n : ℕ} (hn : 0 < n) :
    perronStep (Real.log x - Real.log (n : ℝ)) =
      if (n : ℝ) < x then 1 else if (n : ℝ) = x then 1 / 2 else 0 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hlt : 0 < Real.log x - Real.log (n : ℝ) ↔ (n : ℝ) < x :=
    sub_pos.trans (Real.log_lt_log_iff hn' hx)
  have he : Real.log x - Real.log (n : ℝ) = 0 ↔ (n : ℝ) = x := by
    rw [sub_eq_zero, (Real.strictMonoOn_log.injOn : Set.InjOn Real.log (Ioi 0)).eq_iff hx hn']
    exact eq_comm
  simp only [perronStep, hlt, he]

/-- Corrected B.7.1.1. The truncated vertical integral approximates the
half-weighted cutoff sum for every real cutoff. The absolutely summable
error is coefficient-wise, including an explicit bound at the diagonal. -/
theorem lseries_truncatedPerron (a : ℕ → ℂ) (s : ℂ) {x c T : ℝ} (hx : 0 < x)
    (hc : 0 < c) (hT : 0 < T) (ha : Summable (fun n ↦ ‖LSeries.term a (s + (c : ℂ)) n‖)) :
    let b := fun n : ℕ ↦ Real.log x - Real.log (n : ℝ)
    let E := fun n : ℕ ↦ ‖LSeries.term a s n‖ * perronError (b n) c T
    let step := fun n : ℕ ↦ LSeries.term a s n *
      (if (n : ℝ) < x then 1 else if (n : ℝ) = x then 1 / 2 else 0)
    Summable E ∧
      ‖((∫ y in -T..T, LSeries a (s + edgePoint c y) *
        perronIntegrand (Real.log x) (edgePoint c y)) / (2 * (Real.pi : ℂ))) - (∑' n, step n)‖
        ≤ ∑' n, E n := by
  intro b E step
  have heq (n : ℕ) : step n = LSeries.term a s n * (perronStep (b n) : ℂ) := by
    by_cases hn : n = 0
    · simp [step, hn]
    · rw [show perronStep (b n) = _ from perronStep_log_cutoff hx (Nat.pos_of_ne_zero hn)]
      dsimp only [step]
      apply congrArg (LSeries.term a s n * ·)
      split_ifs <;> norm_num
  have hE : Summable E := by
    refine (ha.mul_left (Real.exp (Real.log x * c) / (Real.pi * T))).of_norm_bounded_eventually_nat ?_
    filter_upwards [eventually_farPerronIndices x] with n hn
    have hb : b n < 0 := by dsimp [b]; linarith
    have hab : 1 ≤ |b n| := by rw [abs_of_neg hb]; dsimp [b]; linarith
    have hEn : 0 ≤ E n := mul_nonneg (norm_nonneg _) (perronError_nonneg _ hc hT)
    rw [Real.norm_of_nonneg hEn]
    change ‖LSeries.term a s n‖ * perronError _ c T ≤ _
    rw [perronError, ite_eq_right hb.ne, lseriesTerm_realShift, norm_mul,
      norm_lseriesShiftExponential, Complex.ofReal_re]
    have he : Real.exp (b n * c) = Real.exp (Real.log x * c) * Real.exp (-(c * Real.log n)) := by
      rw [← Real.exp_add]
      congr 1
      dsimp [b]
      ring
    rw [he]
    calc
      _ ≤ ‖LSeries.term a s n‖ *
          ((Real.exp (Real.log x * c) * Real.exp (-(c * Real.log n))) / (Real.pi * T)) := by
        refine mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left (by positivity) (by positivity) ?_)
          (norm_nonneg _)
        exact le_mul_of_one_le_right (by positivity) hab
      _ = _ := by ring
  have hstep : Summable step := by
    refine (summable_zero : Summable (fun _ : ℕ ↦ (0 : ℝ))).of_norm_bounded_eventually_nat ?_
    filter_upwards [eventually_farPerronIndices x] with n hn
    have hb : b n < 0 := by dsimp [b]; linarith
    simp [heq, perronStep, hb.not_gt, hb.ne]
  have hsum := (lseriesPerronContour a s x c T hc ha).sub hstep.hasSum
  refine ⟨hE, ?_⟩
  rw [← hsum.tsum_eq]
  have hdom (n : ℕ) :
      ‖LSeries.term a s n * truncatedPerron (b n) c T - step n‖ ≤ E n := by
    rw [heq, ← mul_sub, norm_mul]
    exact mul_le_mul_of_nonneg_left (truncatedPerron_error _ hc hT) (norm_nonneg _)
  have hn := hE.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hdom
  exact (norm_tsum_le_tsum_norm hn).trans (hn.tsum_le_tsum hdom hE)

/-- Outside the multiplicative factor-two neighbourhood, the logarithmic
denominator is at least log 2, uniformly in the cutoff and the index. -/
theorem perronLogRatio_far {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (h : y ≤ x / 2 ∨ 2 * x ≤ y) :
    Real.log 2 ≤ |Real.log x - Real.log y| := by
  have htwo : 0 < (2 : ℝ) := by norm_num
  rcases h with h | h
  · have hl := (Real.log_le_log_iff (mul_pos htwo hy) hx).mpr (by linarith : 2 * y ≤ x)
    rw [Real.log_mul htwo.ne' hy.ne'] at hl
    exact (show Real.log 2 ≤ Real.log x - Real.log y by linarith).trans (le_abs_self _)
  · have hl := (Real.log_le_log_iff (mul_pos htwo hx) hy).mpr h
    rw [Real.log_mul htwo.ne' hx.ne'] at hl
    exact (show Real.log 2 ≤ -(Real.log x - Real.log y) by linarith).trans (neg_le_abs _)

/-- The far part of the coefficient-wise error is controlled by the
absolute Dirichlet series on the shifted contour. -/
theorem tsum_perronError_far_le (a : ℕ → ℂ) (s : ℂ) {x c T : ℝ}
    (hx : 0 < x) (hc : 0 < c) (hT : 0 < T)
    (ha : Summable (fun n ↦ ‖LSeries.term a (s + (c : ℂ)) n‖)) :
    (∑' n : ℕ, if (n : ℝ) ≤ x / 2 ∨ 2 * x ≤ (n : ℝ) then
      ‖LSeries.term a s n‖ * perronError (Real.log x - Real.log (n : ℝ)) c T else 0) ≤
      (Real.exp (Real.log x * c) / (Real.pi * T * Real.log 2)) *
        ∑' n : ℕ, ‖LSeries.term a (s + (c : ℂ)) n‖ := by
  let M := Real.exp (Real.log x * c) / (Real.pi * T * Real.log 2)
  let E (n : ℕ) := if (n : ℝ) ≤ x / 2 ∨ 2 * x ≤ (n : ℝ) then
      ‖LSeries.term a s n‖ * perronError (Real.log x - Real.log (n : ℝ)) c T else 0
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hle (n : ℕ) : E n ≤ M * ‖LSeries.term a (s + (c : ℂ)) n‖ := by
    by_cases hn : n = 0
    · subst n
      simp [E]
    by_cases hfar : (n : ℝ) ≤ x / 2 ∨ 2 * x ≤ (n : ℝ)
    · let b := Real.log x - Real.log (n : ℝ)
      have hb : Real.log 2 ≤ |b| := perronLogRatio_far hx (by exact_mod_cast Nat.pos_of_ne_zero hn) hfar
      have hb₀ : b ≠ 0 := abs_pos.mp (hlog.trans_le hb)
      dsimp only [E]
      rw [ite_eq_left hfar]
      change ‖LSeries.term a s n‖ * perronError b c T ≤ _
      rw [perronError, ite_eq_right hb₀, lseriesTerm_realShift, norm_mul,
        norm_lseriesShiftExponential, Complex.ofReal_re]
      have hexp : Real.exp (b * c) = Real.exp (Real.log x * c) * Real.exp (-(c * Real.log n)) := by
        rw [← Real.exp_add]
        congr 1
        dsimp [b]
        ring
      rw [hexp]
      calc
        _ ≤ ‖LSeries.term a s n‖ *
            (Real.exp (Real.log x * c) * Real.exp (-(c * Real.log n)) /
              (Real.pi * T * Real.log 2)) := by
          gcongr
        _ = _ := by dsimp [M]; ring
    · dsimp only [E]
      rw [ite_eq_right hfar]
      exact mul_nonneg hM (norm_nonneg _)
  have hE : Summable E := (ha.mul_left M).of_nonneg_of_le (fun n ↦ by
    dsimp [E]
    split_ifs
    · exact mul_nonneg (norm_nonneg _) (perronError_nonneg _ hc hT)
    · exact le_rfl) hle
  exact (hE.tsum_le_tsum hle (ha.mul_left M)).trans_eq (ha.tsum_mul_left M)

/-- The reciprocal logarithmic ratio is controlled by the reciprocal
additive distance times the larger of the two positive numbers. -/
theorem perronLogRatio_near {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    |x - y| / max x y ≤ |Real.log x - Real.log y| := by
  have haux (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
      (a - b) / a ≤ Real.log a - Real.log b := by
    have h := Real.log_le_sub_one_of_pos (div_pos hb ha)
    rw [Real.log_div hb.ne' ha.ne'] at h
    rw [sub_div, div_self ha.ne']
    linarith
  rcases le_total y x with h | h
  · rw [max_eq_left h, abs_of_nonneg (sub_nonneg.mpr h)]
    exact (haux x y hx hy).trans (le_abs_self _)
  · rw [max_eq_right h, abs_of_nonpos (sub_nonpos.mpr h), neg_sub]
    exact (haux y x hy hx).trans (by simpa only [neg_sub] using neg_le_abs (Real.log x - Real.log y))

private theorem trivialPerronError_pos : 0 < ‖truncatedPerron (Real.log 2) 1 1 - 1‖ := by
  have h := perronVertical_bound (Real.log 2) 1 1 (by norm_num) (by norm_num)
  have hV : ‖∫ y : ℝ in (-1 : ℝ)..1, perronIntegrand (Real.log 2) (edgePoint 1 y)‖ ≤ 4 := by
    norm_num [Real.exp_log (by norm_num : 0 < (2 : ℝ))] at h ⊢
    exact h
  have hk : ‖truncatedPerron (Real.log 2) 1 1‖ < 1 := by
    rw [truncatedPerron, norm_div, show ‖2 * (Real.pi : ℂ)‖ = 2 * Real.pi by simp [Real.pi_pos.le] ]
    exact (div_lt_one (by positivity)).mpr (hV.trans_lt (by linarith [Real.pi_gt_three]))
  rw [norm_pos_iff, sub_ne_zero]
  intro he
  rw [he] at hk
  norm_num at hk

/-- The integer formula (B.7.1.5) cannot have constants independent of the
real part of s. For the series with only a₁=1 take x=2 and c=T=1. -/
theorem printedPerron_integer_uniform_false :
    ¬ ∃ C₁ C₂ C₃ : ℝ, ∀ σ > 0,
      ‖truncatedPerron (Real.log 2) 1 1 - 1‖ ≤
        C₁ * (2 / σ) + C₂ * (Real.exp ((1 - σ) * Real.log 2) * Real.log 2) +
          C₃ * Real.exp (-σ * Real.log 2) := by
  rintro ⟨C₁, C₂, C₃, h⟩
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpow : Tendsto (fun σ : ℝ ↦ Real.exp (-σ * Real.log 2)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp ((tendsto_id.const_mul_atTop_of_neg (neg_neg_of_pos hlog)).congr
      (fun σ ↦ by simp; ring))
  have hpow' : Tendsto (fun σ : ℝ ↦ Real.exp ((1 - σ) * Real.log 2)) atTop (𝓝 0) := by
    have ht := hpow.const_mul (2 : ℝ)
    simp only [mul_zero] at ht
    apply ht.congr
    intro σ
    calc
      2 * Real.exp (-σ * Real.log 2) =
          Real.exp (Real.log 2) * Real.exp (-σ * Real.log 2) := by
        rw [Real.exp_log (by norm_num : 0 < (2 : ℝ))]
      _ = _ := by
        rw [← Real.exp_add]
        congr 1
        ring
  have hinv : Tendsto (fun σ : ℝ ↦ (2 : ℝ) / σ) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using tendsto_inv_atTop_zero.const_mul (2 : ℝ)
  have hlim : Tendsto (fun σ : ℝ ↦
      C₁ * (2 / σ) + C₂ * (Real.exp ((1 - σ) * Real.log 2) * Real.log 2) +
        C₃ * Real.exp (-σ * Real.log 2)) atTop (𝓝 0) := by
    simpa only [zero_mul, mul_zero, add_zero] using
      ((hinv.const_mul C₁).add ((hpow'.mul_const (Real.log 2)).const_mul C₂)).add (hpow.const_mul C₃)
  exact trivialPerronError_pos.not_ge (ge_of_tendsto hlim ((eventually_gt_atTop (0 : ℝ)).mono h))

/-- The one-coefficient counterexample uses an actual absolutely convergent
Dirichlet series. Its contour integrand is independent of σ. -/
theorem oneCoefficientPerronSeries :
    ∃ a : ℕ → ℂ, (∀ s, Summable fun n ↦ ‖LSeries.term a s n‖) ∧
      (∀ s, LSeries a s = 1) ∧
      (∀ n, ‖a n‖ ≤ 1) ∧
      (∀ s, (∑' n, ‖LSeries.term a s n‖) = 1) := by
  let a (n : ℕ) : ℂ := if n = 1 then 1 else 0
  have hterm (s : ℂ) (n : ℕ) : LSeries.term a s n = a n := by
    by_cases hn : n = 1
    · subst n
      simp [a]
    · simp [a, LSeries.term_def, hn]
  refine ⟨a, fun s ↦ ?_, fun s ↦ ?_, fun n ↦ ?_, fun s ↦ ?_⟩
  · refine summable_of_ne_finset_zero (s := {1}) ?_
    intro n hn
    simp [hterm, a, show n ≠ 1 by simpa using hn]
  · rw [LSeries, tsum_eq_single 1 (fun n hn ↦ by simp [hterm, a, hn])]
    simp [a]
  · by_cases h : n = 1 <;> simp [a, h]
  · rw [tsum_eq_single 1 (fun n hn ↦ by simp [hterm, a, hn])]
    simp [a]

end Masullo
