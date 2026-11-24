import Mathlib.Analysis.Complex.Poisson

open Complex MeasureTheory Metric Set
open scoped Classical

namespace Masullo

noncomputable section

private theorem norm_one_sub_real_mul {z : ℂ} (hz : ‖z‖ = 1) (r : ℝ) :
    ‖1 - (r : ℂ) * z‖ = ‖z - (r : ℂ)‖ := by
  have hs : normSq z = 1 := by rw [normSq_eq_norm_sq, hz, one_pow]
  have h : normSq (1 - (r : ℂ) * z) = normSq (z - (r : ℂ)) := by
    rw [normSq_sub, normSq_sub, normSq_one, normSq_mul]
    simp only [hs, mul_one, normSq_ofReal, map_mul, conj_ofReal, mul_re, ofReal_re, ofReal_im,
      zero_mul, mul_zero, sub_zero, one_mul, conj_re, conj_im]
    ring
  rw [normSq_eq_norm_sq, normSq_eq_norm_sq] at h
  nlinarith [norm_nonneg (1 - (r : ℂ) * z), norm_nonneg (z - (r : ℂ))]

private theorem unitCircle_poisson_pow {a : ℝ} (ha₀ : 0 ≤ a) (ha : a < 1) (m : ℕ) :
    Real.circleAverage (fun z : ℂ => (‖z - (a : ℂ)‖ ^ 2)⁻¹ • z ^ m) 0 1 =
      ((a : ℂ) ^ m) / ((1 - a ^ 2 : ℝ) : ℂ) := by
  have hf : DiffContOnCl ℂ (fun z : ℂ => z ^ m) (ball 0 1) :=
    ⟨(differentiable_id.pow m).differentiableOn, (continuous_id.pow m).continuousOn⟩
  have hw : (a : ℂ) ∈ ball (0 : ℂ) 1 := by
    simpa only [mem_ball, dist_zero_right, norm_real, Real.norm_eq_abs, abs_of_nonneg ha₀] using ha
  have h := hf.circleAverage_poissonKernel_smul hw
  let G (z : ℂ) : ℂ := (‖z - (a : ℂ)‖ ^ 2)⁻¹ • z ^ m
  have he : Real.circleAverage (poissonKernel 0 (a : ℂ) • (fun z : ℂ => z ^ m)) 0 1 =
      Real.circleAverage ((1 - a ^ 2 : ℝ) • G) 0 1 := by
    apply Real.circleAverage_congr_sphere
    intro z hz
    have hz₁ : ‖z‖ = 1 := by simpa [mem_sphere, dist_zero_right] using hz
    change poissonKernel 0 (a : ℂ) z • z ^ m = (1 - a ^ 2 : ℝ) • G z
    simp only [poissonKernel_def, sub_zero, hz₁, one_pow, norm_real,
      Real.norm_eq_abs, abs_of_nonneg ha₀, G, smul_smul, div_eq_mul_inv]
  rw [he, Real.circleAverage_smul, Complex.real_smul] at h
  change Real.circleAverage G 0 1 = _
  have hne : ((1 - a ^ 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (show (1 - a ^ 2 : ℝ) ≠ 0 by nlinarith)
  exact (eq_div_iff hne).mpr ((mul_comm _ _).trans h)

/-- The weighted Poisson average on the unit circle, for all integral
angular characters. The exponent is the absolute value of the frequency. -/
theorem complexWeil_unitCircle_poisson_zpow {a : ℝ} (ha₀ : 0 ≤ a) (ha : a < 1) (m : ℤ) :
    Real.circleAverage (fun z : ℂ => (‖z - (a : ℂ)‖ ^ 2)⁻¹ • z ^ m) 0 1 =
      ((a : ℂ) ^ m.natAbs) / ((1 - a ^ 2 : ℝ) : ℂ) := by
  cases m with
  | ofNat m =>
      change Real.circleAverage (fun z : ℂ => (‖z - (a : ℂ)‖ ^ 2)⁻¹ • z ^ (m : ℤ)) 0 1 =
        ((a : ℂ) ^ m) / ((1 - a ^ 2 : ℝ) : ℂ)
      simpa only [zpow_natCast] using unitCircle_poisson_pow ha₀ ha m
  | negSucc m =>
      let G (z : ℂ) : ℂ := (‖z - (a : ℂ)‖ ^ 2)⁻¹ • z ^ (m + 1)
      have h : Real.circleAverage (fun z : ℂ => (‖z - (a : ℂ)‖ ^ 2)⁻¹ • z ^ (Int.negSucc m)) 0 1 =
          Real.circleAverage (G ·⁻¹) 0 1 := by
        apply Real.circleAverage_congr_sphere
        intro z hz
        have hz₁ : ‖z‖ = 1 := by simpa [mem_sphere, dist_zero_right] using hz
        have hz0 : z ≠ 0 := norm_ne_zero_iff.mp (hz₁.trans_ne one_ne_zero)
        have hnorm : ‖z⁻¹ - (a : ℂ)‖ = ‖z - (a : ℂ)‖ := by
          rw [show z⁻¹ - (a : ℂ) = z⁻¹ * (1 - (a : ℂ) * z) by field_simp,
            norm_mul, norm_inv, hz₁, inv_one, one_mul, norm_one_sub_real_mul hz₁]
        rw [show Int.negSucc m = -((m + 1 : ℕ) : ℤ) by omega]
        simp only [G, hnorm, zpow_neg, zpow_natCast, inv_pow]
      rw [h, Real.circleAverage_zero_one_congr_inv]
      exact unitCircle_poisson_pow ha₀ ha (m + 1)

/-- Exact angular average of the complex-place cutoff kernel off the
singular radius, including the frequency-dependent Poisson factor. -/
theorem complexWeil_angular_zpow {r : ℝ} (hr₀ : 0 < r) (hr : r ≠ 1) (m : ℤ) :
    Real.circleAverage (fun u : ℂ => (‖1 - u‖ ^ 2)⁻¹ • (u / (r : ℂ)) ^ m) 0 r =
      if r < 1 then ((r : ℂ) ^ m.natAbs) / ((1 - r ^ 2 : ℝ) : ℂ)
      else (((r⁻¹ : ℝ) : ℂ) ^ m.natAbs) / ((r ^ 2 - 1 : ℝ) : ℂ) := by
  rw [Real.circleAverage_eq_circleAverage_zero_one]
  have hrC : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr₀.ne'
  simp only [add_zero, mul_div_cancel_left₀ _ hrC]
  rcases lt_or_gt_of_ne hr with h | h
  · rw [ite_eq_left h]
    refine (Real.circleAverage_congr_sphere ?_).trans (complexWeil_unitCircle_poisson_zpow hr₀.le h m)
    intro z hz
    have hz₁ : ‖z‖ = 1 := by simpa [mem_sphere, dist_zero_right] using hz
    simp only [norm_one_sub_real_mul hz₁]
  · rw [ite_eq_right h.not_gt]
    have hi : r⁻¹ < 1 := inv_lt_one_of_one_lt₀ h
    have he :
        Real.circleAverage (fun z : ℂ => (‖1 - (r : ℂ) * z‖ ^ 2)⁻¹ • z ^ m) 0 1 =
          (r ^ 2)⁻¹ • Real.circleAverage
            (fun z : ℂ => (‖z - ((r⁻¹ : ℝ) : ℂ)‖ ^ 2)⁻¹ • z ^ m) 0 1 := by
      rw [← Real.circleAverage_smul]
      apply Real.circleAverage_congr_sphere
      intro z _
      have hn : ‖1 - (r : ℂ) * z‖ = r * ‖z - ((r⁻¹ : ℝ) : ℂ)‖ := by
        rw [norm_sub_rev, show (r : ℂ) * z - 1 = (r : ℂ) * (z - ((r⁻¹ : ℝ) : ℂ)) by
              rw [ofReal_inv, mul_sub, mul_inv_cancel₀ hrC],
            norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos hr₀]
      change (‖1 - (r : ℂ) * z‖ ^ 2)⁻¹ • z ^ m =
        (r ^ 2)⁻¹ • ((‖z - ((r⁻¹ : ℝ) : ℂ)‖ ^ 2)⁻¹ • z ^ m)
      rw [hn, mul_pow, mul_inv_rev, smul_smul, mul_comm]
    rw [he, complexWeil_unitCircle_poisson_zpow (inv_nonneg.mpr hr₀.le) hi, Complex.real_smul]
    have hne : r ^ 2 - 1 ≠ 0 := by nlinarith
    have hinv : 1 - (r⁻¹) ^ 2 ≠ 0 := by nlinarith [inv_nonneg.mpr hr₀.le]
    push_cast
    field_simp

/-- The mean over the two real signs, with the even or odd local character.
Together with the radial Jacobian, these are the two real gamma weights. -/
theorem realWeil_sign_average {r : ℝ} (hr₀ : 0 < r) (hr : r ≠ 1) (e : ℕ) (he : e < 2) :
    ((|1 - r|)⁻¹ + (-1 : ℝ) ^ e * (|1 + r|)⁻¹) / 2 =
      if r < 1 then r ^ e / (1 - r ^ 2) else r * (r⁻¹) ^ e / (r ^ 2 - 1) := by
  have hplus : 0 < 1 + r := by linarith
  rw [abs_of_pos hplus]
  rcases lt_or_gt_of_ne hr with h | h
  · have hminus : 0 < 1 - r := by linarith
    have hsq : 1 - r ^ 2 ≠ 0 := by nlinarith
    rw [ite_eq_left h, abs_of_pos hminus]
    have he' : e = 0 ∨ e = 1 := by omega
    rcases he' with rfl | rfl <;> simp only [pow_zero, pow_one, one_mul] <;> field_simp <;> ring
  · have hminus : 1 - r < 0 := by linarith
    have hsq : r ^ 2 - 1 ≠ 0 := by nlinarith
    have hdiff : -(1 - r) ≠ 0 := (neg_pos.mpr hminus).ne'
    rw [ite_eq_right h.not_gt, abs_of_neg hminus]
    have he' : e = 0 ∨ e = 1 := by omega
    rcases he' with rfl | rfl <;> simp only [pow_zero, pow_one, one_mul, mul_one] <;>
      field_simp <;> ring

/-- The positive and negative logarithmic shells give the same half-modulus
weight on the real sign component after reflecting the radius. -/
theorem realWeil_centeredSign_shells {r : ℝ} (hr₀ : 0 < r) (hr : r < 1)
    (e : ℕ) (he : e < 2) :
    (∀ s ∈ ({r, r⁻¹} : Set ℝ),
      s ^ (1 / 2 : ℝ) * (((|1 - s|)⁻¹ + (-1 : ℝ) ^ e * (|1 + s|)⁻¹) / 2) =
        r ^ (1 / 2 : ℝ) * r ^ e / (1 - r ^ 2)) := by
  intro s hs
  simp only [mem_insert_iff, mem_singleton_iff] at hs
  rcases hs with h | h <;> subst s
  · rw [realWeil_sign_average hr₀ hr.ne e he, ite_eq_left hr, mul_div_assoc]
  · have hi : 1 < r⁻¹ := one_lt_inv₀ hr₀ |>.mpr hr
    have hq : 1 - r ^ 2 ≠ 0 := by nlinarith
    have hiq : r⁻¹ ^ 2 - 1 ≠ 0 := by nlinarith
    have hpow : r ^ (1 / 2 : ℝ) * r ^ (1 / 2 : ℝ) = r := by
      rw [← Real.rpow_add hr₀, show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num, Real.rpow_one]
    rw [realWeil_sign_average (inv_pos.mpr hr₀) hi.ne' e he, ite_eq_right hi.not_gt,
      inv_inv, Real.inv_rpow hr₀.le]
    have hv : r ^ (1 / 2 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hr₀ _).ne'
    field_simp [hr₀.ne']
    rw [← pow_two] at hpow
    rw [hpow]

/-- The two complex valuation directions have the same centered radial
weight after integrating the angular character. -/
theorem complexWeil_centeredAngular_shells {r : ℝ} (hr₀ : 0 < r) (hr : r < 1) (m : ℤ) :
    (∀ s ∈ ({r, r⁻¹} : Set ℝ), (s : ℂ) *
      Real.circleAverage (fun u : ℂ => (‖1 - u‖ ^ 2)⁻¹ • (u / (s : ℂ)) ^ m) 0 s =
        ((r : ℂ) ^ (m.natAbs + 1)) / ((1 - r ^ 2 : ℝ) : ℂ)) := by
  intro s hs
  simp only [mem_insert_iff, mem_singleton_iff] at hs
  rcases hs with h | h <;> subst s
  · rw [complexWeil_angular_zpow hr₀ hr.ne, ite_eq_left hr, ← mul_div_assoc]
    exact congrArg (fun z : ℂ => z / ((1 - r ^ 2 : ℝ) : ℂ)) (pow_succ' (r : ℂ) m.natAbs).symm
  · have hi : 1 < r⁻¹ := one_lt_inv₀ hr₀ |>.mpr hr
    have hq : 1 - r ^ 2 ≠ 0 := by nlinarith
    have hiq : r⁻¹ ^ 2 - 1 ≠ 0 := by nlinarith
    rw [complexWeil_angular_zpow (inv_pos.mpr hr₀) hi.ne', ite_eq_right hi.not_gt, inv_inv]
    push_cast
    rw [pow_succ']
    field_simp [ofReal_ne_zero.mpr, hr₀.ne']
    ring

/-- The centered real amplitude becomes the real gamma denominator
when the radius is written as `exp (-t / 2)`. -/
theorem realWeil_radialWeight_log (t : ℝ) (e : ℕ) :
    let r := Real.exp (-t / 2)
    r ^ (1 / 2 : ℝ) * r ^ e / (1 - r ^ 2) =
      Real.exp (-((e : ℝ) + 1 / 2) * (t / 2)) / (1 - Real.exp (-t)) := by
  dsimp only
  have hden : Real.exp (-t / 2) ^ 2 = Real.exp (-t) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [hden, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp, ← Real.exp_nat_mul,
    ← Real.exp_add]
  apply congrArg (fun x : ℝ => x / (1 - Real.exp (-t)))
  apply congrArg Real.exp
  ring

/-- The centered complex amplitude becomes the complex gamma denominator
when the radius is written as `exp (-t / 2)`. -/
theorem complexWeil_radialWeight_log (t : ℝ) (m : ℤ) :
    let r := Real.exp (-t / 2)
    ((r : ℂ) ^ (m.natAbs + 1)) / ((1 - r ^ 2 : ℝ) : ℂ) =
      (Real.exp (-(((m.natAbs : ℝ) + 1) / 2) * t) : ℂ) /
        ((1 - Real.exp (-t) : ℝ) : ℂ) := by
  dsimp only
  have hden : Real.exp (-t / 2) ^ 2 = Real.exp (-t) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [hden, ← Complex.ofReal_pow, ← Real.exp_nat_mul]
  apply congrArg (fun x : ℝ => (x : ℂ) / ((1 - Real.exp (-t) : ℝ) : ℂ))
  apply congrArg Real.exp
  push_cast
  ring

end
end Masullo
