import MellinJumps
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open Complex Filter Function MeasureTheory Set Topology
open scoped ContDiff

namespace Masullo

noncomputable section

/-- The indicator of the norm interval whose logarithmic interval is `(0,1]`. -/
def poissonJumpTest : ℝ → ℂ :=
  (Ioc (1 : ℝ) (Real.exp 1)).indicator fun _ => 1

private theorem poissonJumpTest_log (x : ℝ) :
    poissonJumpTest (Real.exp x) = (Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℂ)) x := by
  have he : Real.exp x ∈ Ioc 1 (Real.exp 1) ↔ x ∈ Ioc (0 : ℝ) 1 := by
    simp only [mem_Ioc, Real.exp_le_exp]
    rw [← Real.exp_zero, Real.exp_lt_exp]
  simp only [poissonJumpTest, indicator_apply, he]

private def stepLeft (x : ℝ) : ℂ :=
  if x = 1 then 1 else if x ∈ Ioo (0 : ℝ) 1 then 1 else 0

private def stepRight (x : ℝ) : ℂ :=
  if x = 0 then 1 else if x ∈ Ioo (0 : ℝ) 1 then 1 else 0

private theorem step_continuous_at {x : ℝ} (h0 : x ≠ 0) (h1 : x ≠ 1) :
    ContDiffAt ℝ ∞ (fun y => poissonJumpTest (Real.exp y)) x ∧
      HasDerivAt (fun y => poissonJumpTest (Real.exp y)) 0 x ∧
      poissonJumpTest (Real.exp x) = stepLeft x ∧
      poissonJumpTest (Real.exp x) = stepRight x := by
  have aux (c : ℂ) (h : ∀ᶠ y in 𝓝 x, poissonJumpTest (Real.exp y) = c)
      (hc₁ : stepLeft x = c) (hc₂ : stepRight x = c) :
      ContDiffAt ℝ ∞ (fun y => poissonJumpTest (Real.exp y)) x ∧
        HasDerivAt (fun y => poissonJumpTest (Real.exp y)) 0 x ∧
        poissonJumpTest (Real.exp x) = stepLeft x ∧
        poissonJumpTest (Real.exp x) = stepRight x := by
    have hval := mem_of_mem_nhds h
    exact ⟨contDiffAt_const.congr_of_eventuallyEq h,
      (hasDerivAt_const x c).congr_of_eventuallyEq h, hval.trans hc₁.symm, hval.trans hc₂.symm⟩
  rcases lt_or_gt_of_ne h0 with hx | hx
  · apply aux 0
    · filter_upwards [Iio_mem_nhds hx] with y hy
      rw [poissonJumpTest_log, indicator_of_notMem]
      exact fun h => (not_lt_of_ge hy.le) h.1
    · simp [stepLeft, h1, show x ∉ Ioo 0 1 from fun h => (not_lt_of_ge hx.le) h.1]
    · simp [stepRight, h0, show x ∉ Ioo 0 1 from fun h => (not_lt_of_ge hx.le) h.1]
  rcases lt_or_gt_of_ne h1 with hx' | hx'
  · apply aux 1
    · filter_upwards [Ioo_mem_nhds hx hx'] with y hy
      rw [poissonJumpTest_log, indicator_of_mem (show y ∈ Ioc (0 : ℝ) 1 from ⟨hy.1, hy.2.le⟩)]
    · simp [stepLeft, h1, show x ∈ Ioo 0 1 from ⟨hx, hx'⟩]
    · simp [stepRight, h0, show x ∈ Ioo 0 1 from ⟨hx, hx'⟩]
  · apply aux 0
    · filter_upwards [Ioi_mem_nhds hx'] with y hy
      rw [poissonJumpTest_log, indicator_of_notMem]
      exact fun h => (not_le_of_gt hy) h.2
    · simp [stepLeft, h1, show x ∉ Ioo 0 1 from fun h => (not_lt_of_ge hx'.le) h.2]
    · simp [stepRight, h0, show x ∉ Ioo 0 1 from fun h => (not_lt_of_ge hx'.le) h.2]

theorem poissonJumpTest_oneSided (x : ℝ) :
    Tendsto (fun y => poissonJumpTest (Real.exp y)) (𝓝[<] x) (𝓝 (stepLeft x)) ∧
    Tendsto (fun y => poissonJumpTest (Real.exp y)) (𝓝[>] x) (𝓝 (stepRight x)) := by
  rcases eq_or_ne x 0 with rfl | h0
  · have hl : (fun y => poissonJumpTest (Real.exp y)) =ᶠ[𝓝[<] (0 : ℝ)] fun _ => 0 := by
      filter_upwards [self_mem_nhdsWithin] with y hy
      rw [poissonJumpTest_log, indicator_of_notMem]
      exact fun h => (not_lt_of_ge hy.le) h.1
    have hr : (fun y => poissonJumpTest (Real.exp y)) =ᶠ[𝓝[>] (0 : ℝ)] fun _ => 1 := by
      filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with y hy
      rw [poissonJumpTest_log, indicator_of_mem (show y ∈ Ioc (0 : ℝ) 1 from ⟨hy.1, hy.2.le⟩)]
    refine ⟨?_, ?_⟩
    · simpa [stepLeft] using tendsto_const_nhds.congr' hl.symm
    · simpa [stepRight] using tendsto_const_nhds.congr' hr.symm
  rcases eq_or_ne x 1 with rfl | h1
  · have hl : (fun y => poissonJumpTest (Real.exp y)) =ᶠ[𝓝[<] (1 : ℝ)] fun _ => 1 := by
      filter_upwards [Ioc_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with y hy
      rw [poissonJumpTest_log, indicator_of_mem hy]
    have hr : (fun y => poissonJumpTest (Real.exp y)) =ᶠ[𝓝[>] (1 : ℝ)] fun _ => 0 := by
      filter_upwards [self_mem_nhdsWithin] with y hy
      rw [poissonJumpTest_log, indicator_of_notMem]
      exact fun h => (not_le_of_gt hy) h.2
    refine ⟨?_, ?_⟩
    · simpa [stepLeft] using tendsto_const_nhds.congr' hl.symm
    · simpa [stepRight] using tendsto_const_nhds.congr' hr.symm
  obtain ⟨_, hD, hL, hR⟩ := step_continuous_at h0 h1
  exact ⟨hL ▸ hD.continuousAt.continuousWithinAt, hR ▸ hD.continuousAt.continuousWithinAt⟩

/-- The orientation counterexample has the stipulated smoothness and
decay, with zero derivative outside the two jumps. -/
theorem poissonJumpTest_admissible :
    SuperExponentialLogDecay (fun x => poissonJumpTest (Real.exp x)) ∧
      SuperExponentialLogDecay (fun _ => (0 : ℂ)) ∧
      ∀ x : ℝ, x ≠ 0 → x ≠ 1 →
        ContDiffAt ℝ ∞ (fun y => poissonJumpTest (Real.exp y)) x ∧
        HasDerivAt (fun y => poissonJumpTest (Real.exp y)) 0 x := by
  constructor
  · constructor
    · refine ⟨1, fun x => ?_⟩
      change ‖poissonJumpTest (Real.exp x)‖ ≤ 1
      rw [poissonJumpTest_log]
      by_cases hx : x ∈ Ioc (0 : ℝ) 1 <;> simp [hx]
    · intro N
      refine ⟨1, 2, by norm_num, by norm_num, fun x hx => ?_⟩
      have hn : x ∉ Ioc (0 : ℝ) 1 := fun h =>
        (not_lt_of_ge (show |x| ≤ 2 by rw [abs_of_pos h.1]; linarith [h.2])) hx
      change ‖poissonJumpTest (Real.exp x)‖ ≤ _
      rw [poissonJumpTest_log, indicator_of_notMem hn, norm_zero]
      positivity
  · refine ⟨⟨⟨0, fun _ => norm_zero.le⟩, fun N => ⟨1, 1, by norm_num, by norm_num,
      fun x _ => by simp [Real.exp_nonneg]⟩⟩, fun x h0 h1 => ?_⟩
    exact ⟨(step_continuous_at h0 h1).1, (step_continuous_at h0 h1).2.1⟩

private theorem poissonJumpTest_mellin_integral (c : ℂ) :
    mellin poissonJumpTest c = ∫ x : ℝ in 0..1, Complex.exp (c * (x : ℂ)) := by
  classical
  rw [mellin_eq_log_integral, intervalIntegral.integral_of_le zero_le_one, ← integral_indicator
    measurableSet_Ioc]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [poissonJumpTest_log]
  by_cases hx : x ∈ Ioc (0 : ℝ) 1 <;> simp [hx]

private theorem poissonJumpTest_spectrum (m : ℤ) :
    mellin poissonJumpTest ((m : ℂ) * (2 * Real.pi * I)) = if m = 0 then 1 else 0 := by
  classical
  let c : ℂ := (m : ℂ) * (2 * Real.pi * I)
  change mellin poissonJumpTest c = _
  rw [poissonJumpTest_mellin_integral]
  split_ifs with hm
  · simp [c, hm]
  · have hc : c ≠ 0 := by
      unfold c
      exact mul_ne_zero (Int.cast_ne_zero.mpr hm)
        (mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero)
    rw [integral_exp_mul_complex hc]
    simp only [ofReal_one, mul_one, ofReal_zero, mul_zero, Complex.exp_zero]
    rw [Complex.exp_int_mul_two_pi_mul_I m]
    simp


/-- The absolute-convergence counterexample requested in footnote 12.
The generator with logarithm two gives harmonic-sized odd samples for
the indicator whose logarithmic support is the interval from zero to one. -/
theorem poissonJumpTest_spectrum_not_absolutely_summable :
    ¬ Summable (fun m : ℤ =>
      ‖mellin poissonJumpTest ((m : ℂ) * (2 * Real.pi * I) /
        (Real.log (Real.exp 2) : ℂ))‖) := by
  intro h
  let odd (n : ℕ) : ℤ := 2 * (n : ℤ) + 1
  have ho : Injective odd := by
    intro a b hab
    dsimp [odd] at hab
    omega
  have hsub := h.comp_injective ho
  simp only [Real.log_exp] at hsub
  have hsample (n : ℕ) :
      ‖mellin poissonJumpTest ((odd n : ℂ) * (2 * Real.pi * I) / ((2 : ℝ) : ℂ))‖ =
        2 / ((2 * (n : ℝ) + 1) * Real.pi) := by
    let c : ℂ := (odd n : ℂ) * (Real.pi * I)
    have hcpos : 0 < (2 * (n : ℝ) + 1) * Real.pi := by positivity
    have hn : ‖c‖ = (2 * (n : ℝ) + 1) * Real.pi := by
      simp only [c, odd, Int.cast_add, Int.cast_mul, Int.cast_natCast, Int.cast_ofNat,
        Int.cast_one, norm_mul, norm_I, mul_one]
      rw [show (2 : ℂ) * (n : ℂ) + 1 = ((2 * (n : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg (by positivity : 0 ≤ 2 * (n : ℝ) + 1),
        Real.norm_of_nonneg Real.pi_pos.le]
    have hc : c ≠ 0 := norm_ne_zero_iff.mp (hn.trans_ne hcpos.ne')
    have he : Complex.exp c = -1 := by
      have ha : c = (n : ℂ) * (2 * Real.pi * I) + Real.pi * I := by
        dsimp [c, odd]
        push_cast
        ring
      rw [ha, Complex.exp_add, ← Int.cast_natCast (R := ℂ), Complex.exp_int_mul_two_pi_mul_I,
        Complex.exp_pi_mul_I, one_mul]
    have harg : (odd n : ℂ) * (2 * Real.pi * I) / ((2 : ℝ) : ℂ) = c := by
      simp only [ofReal_ofNat]
      dsimp [c]
      ring
    rw [harg, poissonJumpTest_mellin_integral, integral_exp_mul_complex hc]
    simp only [ofReal_one, mul_one, ofReal_zero, mul_zero, Complex.exp_zero, he]
    rw [norm_div, hn]
    norm_num
  have hbound (n : ℕ) : ((n + 1 : ℕ) : ℝ)⁻¹ ≤
      Real.pi * ‖mellin poissonJumpTest ((odd n : ℂ) * (2 * Real.pi * I) / ((2 : ℝ) : ℂ))‖ := by
    rw [hsample, Nat.cast_add, Nat.cast_one]
    have hp : 0 < (2 * (n : ℝ) + 1) * Real.pi := by positivity
    rw [← mul_div_assoc]
    apply (le_div_iff₀ hp).mpr
    rw [inv_mul_eq_div]
    apply (div_le_iff₀ (by positivity : 0 < (n : ℝ) + 1)).mpr
    calc
      _ ≤ (2 * ((n : ℝ) + 1)) * Real.pi :=
        mul_le_mul_of_nonneg_right (by linarith) Real.pi_pos.le
      _ = _ := by ring
  exact Real.not_summable_natCast_inv ((summable_nat_add_iff 1).mp
    ((hsub.mul_left Real.pi).of_nonneg_of_le (fun n => by positivity) hbound))

theorem poissonJumpTest_orientation_failure :
    (Real.log (Real.exp (-1)) : ℂ) *
      (∑' m : ℤ, (stepLeft (m * Real.log (Real.exp (-1))) +
        stepRight (m * Real.log (Real.exp (-1)))) / 2) ≠
    ∑' m : ℤ, mellin poissonJumpTest ((m : ℂ) * (2 * Real.pi * I) /
      (Real.log (Real.exp (-1)) : ℂ)) := by
  classical
  simp only [Real.log_exp]
  have hs (m : ℤ) : (stepLeft ((m : ℝ) * (-1)) + stepRight ((m : ℝ) * (-1))) / 2 =
      if m = 0 ∨ m = -1 then (1 / 2 : ℂ) else 0 := by
    by_cases h0 : m = 0
    · subst m
      norm_num [stepLeft, stepRight]
    by_cases h1 : m = -1
    · subst m
      norm_num [stepLeft, stepRight]
    have hn0 : -(m : ℝ) ≠ 0 := by simpa using h0
    have hn1 : -(m : ℝ) ≠ 1 := by
      intro he
      apply h1
      exact_mod_cast (neg_eq_iff_eq_neg.mp he)
    have hn : -(m : ℝ) ∉ Ioo 0 1 := by
      rintro ⟨hL, hR⟩
      have hL' : (0 : ℤ) < -m := by exact_mod_cast hL
      have hR' : -m < (1 : ℤ) := by exact_mod_cast hR
      omega
    simp [stepLeft, stepRight, h0, h1, hn0, hn1, hn]
  have ha : (∑' m : ℤ, if m = 0 ∨ m = -1 then (1 / 2 : ℂ) else 0) = 1 := by
    rw [tsum_eq_sum (s := {0, -1})]
    · norm_num [Finset.sum_insert]
    · simp only [Finset.mem_insert, Finset.mem_singleton]
      intro m hm
      simp [hm]
  have hb (m : ℤ) :
      mellin poissonJumpTest ((m : ℂ) * (2 * Real.pi * I) / (-1 : ℂ)) =
        if m = 0 then 1 else (0 : ℂ) := by
    convert poissonJumpTest_spectrum (-m) using 1 <;> simp [div_neg]
  simp only [hs, ha, Complex.ofReal_neg, Complex.ofReal_one, mul_one]
  simp only [hb, tsum_ite_eq]
  norm_num

end
end Masullo
