import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn

open Complex Filter Set
open scoped Topology

namespace Masullo

/-- The regularized reciprocal at the integer `m`. The index zero is
omitted by the inverse of zero convention. -/
noncomputable def regularizedReciprocal (m : ℤ) (z : ℂ) : ℂ :=
  z * (((z - (m : ℂ)) * (m : ℂ))⁻¹)

private theorem integer_difference_ne_zero {z : ℂ} (hz : z ∈ integerComplement) (m : ℤ) :
    z - (m : ℂ) ≠ 0 := by
  apply sub_ne_zero.mpr
  intro he
  exact (mem_integerComplement_iff.mp hz) ⟨m, he.symm⟩

theorem regularizedReciprocal_eq {z : ℂ} (hz : z ∈ integerComplement) {m : ℤ} (hm : m ≠ 0) :
    regularizedReciprocal m z = 1 / (z - (m : ℂ)) + 1 / (m : ℂ) := by
  have hn : (m : ℂ) ≠ 0 := by exact_mod_cast hm
  unfold regularizedReciprocal
  rw [← div_eq_mul_inv]
  field_simp [integer_difference_ne_zero hz m, hn]
  ring

@[simp] theorem regularizedReciprocal_zero (z : ℂ) : regularizedReciprocal 0 z = 0 := by
  simp [regularizedReciprocal]

theorem summable_regularizedReciprocal (z : ℂ) : Summable (fun m => regularizedReciprocal m z) := by
  simpa [regularizedReciprocal] using
    (EisensteinSeries.summable_linear_sub_mul_linear_add z 1 0).mul_left z

private theorem summable_inv_int_square : Summable (fun m : ℤ => ((m : ℝ) ^ 2)⁻¹) := by
  simpa [Real.rpow_neg (abs_nonneg _), Real.rpow_two, sq_abs] using
    (Real.summable_abs_int_rpow (b := (2 : ℝ)) (by norm_num))

/-- Absolute convergence and locally uniform convergence for the
regularized reciprocal series that occurs in B.4.1.9. -/
theorem regularizedReciprocal_summableLocallyUniformlyOn :
    SummableLocallyUniformlyOn regularizedReciprocal integerComplement := by
  apply SummableLocallyUniformlyOn.of_locally_bounded_eventually Complex.isClosed_range_intCast.isOpen_compl
  intro K _ hK
  obtain ⟨M, hM⟩ := hK.bddAbove_image continuous_norm.continuousOn
  let A := max 1 M
  have hA : 0 < A := zero_lt_one.trans_le (le_max_left _ _)
  have hZ (m : ℤ) : ‖(m : ℂ)‖ = ‖(m : ℝ)‖ := by
    rw [← Complex.ofReal_intCast, Complex.norm_real]
  have hmaj : Summable (fun m : ℤ => (‖(m : ℝ)‖ ^ 2)⁻¹) := by
    simpa only [Real.norm_eq_abs, sq_abs] using summable_inv_int_square
  refine ⟨fun m => (2 * A) * (‖(m : ℝ)‖ ^ 2)⁻¹, hmaj.mul_left _, ?_⟩
  have hlarge : ∀ᶠ m : ℤ in cofinite, 2 * A ≤ ‖(m : ℝ)‖ :=
    (tendsto_norm_comp_cofinite_atTop_of_isClosedEmbedding Int.isClosedEmbedding_coe_real).eventually
      (eventually_ge_atTop _)
  filter_upwards [hlarge] with m hm
  intro z hz
  have hzA : ‖z‖ ≤ A := (hM (mem_image_of_mem _ hz)).trans (le_max_right _ _)
  have hdiff : ‖(m : ℂ)‖ / 2 ≤ ‖z - (m : ℂ)‖ := by
    have htri := norm_sub_norm_le (m : ℂ) z
    rw [norm_sub_rev] at htri
    rw [← hZ m] at hm
    linarith
  rw [hZ m] at hdiff
  rw [regularizedReciprocal, norm_mul, norm_inv, norm_mul, hZ m]
  have hm' : 0 < ‖(m : ℝ)‖ := by linarith
  have hb : 0 < ‖z - (m : ℂ)‖ := (by positivity : 0 < ‖(m : ℝ)‖ / 2).trans_le hdiff
  rw [← div_eq_mul_inv, ← div_eq_mul_inv]
  calc
    ‖z‖ / (‖z - (m : ℂ)‖ * ‖(m : ℝ)‖) ≤
        A / ((‖(m : ℝ)‖ / 2) * ‖(m : ℝ)‖) :=
      div_le_div₀ hA.le hzA (by positivity)
        (mul_le_mul_of_nonneg_right hdiff (norm_nonneg _))
    _ = 2 * A / ‖(m : ℝ)‖ ^ 2 := by ring


theorem tsum_regularizedReciprocal_eq_cot {z : ℂ} (hz : z ∈ integerComplement) :
    (∑' m : ℤ, regularizedReciprocal m z) = Real.pi * cot (Real.pi * z) - 1 / z := by
  have hs := summable_regularizedReciprocal z
  obtain ⟨hp, hn⟩ := summable_int_iff_summable_nat_and_neg.mp hs
  have hpos : Summable (fun n : ℕ+ => regularizedReciprocal (n : ℕ) z) :=
    hp.comp_injective PNat.coe_injective
  have hneg : Summable (fun n : ℕ+ => regularizedReciprocal (-(n : ℕ) : ℤ) z) :=
    hn.comp_injective PNat.coe_injective
  rw [tsum_int_eq_zero_add_tsum_pnat hs, regularizedReciprocal_zero, zero_add, ← hpos.tsum_add hneg]
  have hcot := cot_series_rep hz
  have hpair (n : ℕ+) :
      regularizedReciprocal (n : ℕ) z + regularizedReciprocal (-(n : ℕ) : ℤ) z =
        1 / (z - (n : ℂ)) + 1 / (z + (n : ℂ)) := by
    have hn' : ((n : ℕ) : ℤ) ≠ 0 := by exact_mod_cast n.ne_zero
    rw [regularizedReciprocal_eq hz hn', regularizedReciprocal_eq hz (neg_ne_zero.mpr hn')]
    simp only [Int.cast_natCast, Int.cast_neg, sub_neg_eq_add, div_neg]
    ring
  rw [tsum_congr hpair, hcot]
  ring

/-- The expansion in equation (B.4.1.21), with absolute convergence at
every point away from the integer poles. -/
theorem geometric_pole_expansion {z : ℂ} (hz : z ∈ integerComplement) :
    (1 - Complex.exp (2 * Real.pi * I * z))⁻¹ =
      1 / 2 - 1 / (2 * Real.pi * I * z) -
      (1 / (2 * Real.pi * I)) * ∑' m : ℤ, regularizedReciprocal m z := by
  have hZ := integerComplement.ne_zero hz
  have hE : 1 - Complex.exp (2 * Real.pi * I * z) ≠ 0 := by
    intro he
    have he' : Complex.exp (2 * Real.pi * I * z) = 1 := (sub_eq_zero.mp he).symm
    obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.mp he'
    have heq : (2 * (Real.pi : ℂ) * I) * z = (2 * (Real.pi : ℂ) * I) * (m : ℂ) := by
      rw [hm, mul_comm]
    exact (mem_integerComplement_iff.mp hz)
      ⟨m, (mul_left_cancel₀ Complex.two_pi_I_ne_zero heq).symm⟩
  rw [tsum_regularizedReciprocal_eq_cot hz, Complex.cot_pi_eq_exp_ratio]
  have hP : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp [Complex.I_ne_zero, hP, hZ, hE]
  ring_nf
  simp
  ring


private theorem mem_integerComplement_of_im_ne_zero {z : ℂ} (hz : z.im ≠ 0) :
    z ∈ integerComplement := by
  rw [mem_integerComplement_iff]
  rintro ⟨m, hm⟩
  exact hz (by rw [← hm]; simp)

theorem tsum_regularizedReciprocal_horizontal_bound {a : ℝ} (ha : a ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, z.im = a →
      ‖∑' m : ℤ, regularizedReciprocal m z‖ ≤ C := by
  let q := Real.exp (-(2 * Real.pi * a))
  have hq : |1 - q| > 0 := by
    apply abs_pos.mpr
    intro h
    have h0 : -(2 * Real.pi * a) = 0 :=
      Real.exp_injective (by rw [Real.exp_zero]; exact (sub_eq_zero.mp h).symm)
    exact ha (by rcases mul_eq_zero.mp (neg_eq_zero.mp h0) with h' | h'
                 · exact (by positivity : 0 < 2 * Real.pi).ne' h' |>.elim
                 · exact h')
  refine ⟨1 + Real.pi * ((q + 1) / |1 - q|) + |a|⁻¹, by dsimp [q]; positivity, ?_⟩
  intro z hz
  have hn : ‖Complex.exp (2 * Real.pi * I * z)‖ = q := by
    rw [norm_exp]
    congr 1
    simp [Complex.mul_re, Complex.mul_im, hz]
  have hden : |1 - q| ≤ ‖1 - Complex.exp (2 * Real.pi * I * z)‖ := by
    simpa only [norm_one, hn] using abs_norm_sub_norm_le (1 : ℂ)
      (Complex.exp (2 * Real.pi * I * z))
  have hcot : ‖cot (Real.pi * z)‖ ≤ (q + 1) / |1 - q| := by
    rw [Complex.cot_pi_eq_exp_ratio, norm_div, norm_mul, norm_I, one_mul]
    apply div_le_div₀ (by dsimp [q]; positivity) _ hq hden
    simpa only [norm_one, hn] using norm_add_le (Complex.exp (2 * Real.pi * I * z)) (1 : ℂ)
  have hZ : |a| ≤ ‖z‖ := by simpa only [hz] using abs_im_le_norm z
  have hinv : ‖(1 : ℂ) / z‖ ≤ |a|⁻¹ := by
    rw [one_div, norm_inv]
    exact inv_anti₀ (abs_pos.mpr ha) hZ
  rw [tsum_regularizedReciprocal_eq_cot (mem_integerComplement_of_im_ne_zero (hz ▸ ha))]
  calc
    _ ≤ ‖(Real.pi : ℂ) * cot (Real.pi * z)‖ + ‖1 / z‖ := norm_sub_le _ _
    _ ≤ Real.pi * ((q + 1) / |1 - q|) + |a|⁻¹ := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
      exact add_le_add (mul_le_mul_of_nonneg_left hcot Real.pi_pos.le) hinv
    _ ≤ _ := by linarith

private theorem summable_inv_one_add_int_square :
    Summable (fun m : ℤ => (1 + (m : ℝ) ^ 2)⁻¹) := by
  apply summable_inv_int_square.of_norm_bounded_eventually
  have hE : ∀ᶠ m : ℤ in cofinite, m ≠ 0 := eventually_cofinite_ne _
  filter_upwards [hE] with m hm
  rw [Real.norm_of_nonneg (by positivity)]
  exact inv_anti₀ (sq_pos_of_ne_zero (by exact_mod_cast hm)) (by linarith)

private theorem tsum_inv_distance_sq_horizontal_bound {a : ℝ} (ha : a ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, z.im = a →
      Summable (fun m : ℤ => (‖z - (m : ℂ)‖ ^ 2)⁻¹) ∧
      (∑' m : ℤ, (‖z - (m : ℂ)‖ ^ 2)⁻¹) ≤ C := by
  let U := 3 / a ^ 2 + 2
  let v (m : ℤ) := U * (1 + (m : ℝ) ^ 2)⁻¹
  have hu : 0 ≤ U := by dsimp [U]; positivity
  have hv : Summable v := summable_inv_one_add_int_square.mul_left _
  refine ⟨∑' m, v m, tsum_nonneg (fun m => by dsimp [v]; positivity), ?_⟩
  intro z hz
  let k : ℤ := ⌊z.re⌋
  let w := z - (k : ℂ)
  have hw : 0 ≤ w.re ∧ w.re ≤ 1 := by
    simp only [w, sub_re, intCast_re]
    exact ⟨sub_nonneg.mpr (Int.floor_le _), by linarith [Int.lt_floor_add_one z.re]⟩
  have hwi : w.im = a := by simp [w, hz]
  have ht (m : ℤ) : (‖w - (m : ℂ)‖ ^ 2)⁻¹ ≤ v m := by
    have him : |a| ≤ ‖w - (m : ℂ)‖ := by
      simpa [hwi] using abs_im_le_norm (w - (m : ℂ))
    have hre : |w.re - (m : ℝ)| ≤ ‖w - (m : ℂ)‖ := by
      simpa using abs_re_le_norm (w - (m : ℂ))
    have hi : a ^ 2 ≤ ‖w - (m : ℂ)‖ ^ 2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) him 2
    have hr : (w.re - (m : ℝ)) ^ 2 ≤ ‖w - (m : ℂ)‖ ^ 2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hre 2
    have hw2 : w.re ^ 2 ≤ 1 := by nlinarith [mul_nonneg hw.1 (sub_nonneg.mpr hw.2)]
    have hm : 1 + (m : ℝ) ^ 2 ≤ 3 + 2 * ‖w - (m : ℂ)‖ ^ 2 := by
      nlinarith [sq_nonneg (2 * w.re - (m : ℝ))]
    have h1 : 3 ≤ (3 / a ^ 2) * ‖w - (m : ℂ)‖ ^ 2 := by
      calc
        _ = (3 / a ^ 2) * a ^ 2 := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left hi (by positivity)
    have hd : 0 < ‖w - (m : ℂ)‖ ^ 2 := (sq_pos_of_ne_zero ha).trans_le hi
    dsimp [v]
    rw [← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ hd (by positivity)]
    dsimp [U]
    linarith [show (3 / a ^ 2 + 2) * ‖w - (m : ℂ)‖ ^ 2 =
      (3 / a ^ 2) * ‖w - (m : ℂ)‖ ^ 2 + 2 * ‖w - (m : ℂ)‖ ^ 2 by ring]
  have hS : Summable (fun m : ℤ => (‖w - (m : ℂ)‖ ^ 2)⁻¹) :=
    hv.of_nonneg_of_le (fun _ => by positivity) ht
  have he (m : ℤ) :
      (‖w - (m : ℂ)‖ ^ 2)⁻¹ = (‖z - ((m + k : ℤ) : ℂ)‖ ^ 2)⁻¹ := by
    rw [Int.cast_add]
    congr 3
    dsimp [w]
    ring
  have ht' : Summable (fun m : ℤ => (‖z - (m : ℂ)‖ ^ 2)⁻¹) :=
    ((Equiv.addRight k).summable_iff.mp (hS.congr he))
  refine ⟨ht', ?_⟩
  rw [← (Equiv.addRight k).tsum_eq (f := fun m : ℤ => (‖z - (m : ℂ)‖ ^ 2)⁻¹)]
  exact (tsum_congr fun m => (he m).symm).trans_le (hS.tsum_le_tsum ht hv)

theorem tsum_norm_regularizedReciprocal_horizontal_bound {a : ℝ} (ha : a ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, z.im = a →
      (∑' m : ℤ, ‖regularizedReciprocal m z‖) ≤ C * ‖z‖ := by
  obtain ⟨B, hB, hBd⟩ := tsum_inv_distance_sq_horizontal_bound ha
  let T := ∑' m : ℤ, ((m : ℝ) ^ 2)⁻¹
  have hT : 0 ≤ T := tsum_nonneg fun _ => by positivity
  refine ⟨1 + (B + T) / 2, by positivity, ?_⟩
  intro z hz
  obtain ⟨hS, hSb⟩ := hBd z hz
  have hmajor := ((hS.add summable_inv_int_square).div_const 2).mul_left ‖z‖
  have hpoint (m : ℤ) :
      ‖regularizedReciprocal m z‖ ≤ ‖z‖ *
        (((‖z - (m : ℂ)‖ ^ 2)⁻¹ + ((m : ℝ) ^ 2)⁻¹) / 2) := by
    rw [regularizedReciprocal, norm_mul, norm_inv, norm_mul, mul_inv, ← Complex.ofReal_intCast,
      Complex.norm_real]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    rw [← inv_pow, ← inv_pow]
    have hfit : ‖(m : ℝ)‖ ^ 2 = (m : ℝ) ^ 2 := by rw [Real.norm_eq_abs, sq_abs]
    have h := sq_nonneg ((‖z - (m : ℂ)‖)⁻¹ - ‖(m : ℝ)‖⁻¹)
    have hi : ‖(m : ℝ)‖⁻¹ ^ 2 = ((m : ℝ)⁻¹) ^ 2 := by rw [inv_pow, inv_pow, hfit]
    rw [← hi, Complex.ofReal_intCast]
    nlinarith only [h]
  calc
    _ ≤ ∑' m : ℤ, ‖z‖ * (((‖z - (m : ℂ)‖ ^ 2)⁻¹ + ((m : ℝ) ^ 2)⁻¹) / 2) :=
      (summable_regularizedReciprocal z).norm.tsum_le_tsum hpoint hmajor
    _ = ‖z‖ * (((∑' m : ℤ, (‖z - (m : ℂ)‖ ^ 2)⁻¹) + T) / 2) := by
      simp only [tsum_mul_left, tsum_div_const, hS.tsum_add summable_inv_int_square, T]
    _ ≤ (1 + (B + T) / 2) * ‖z‖ := by
      rw [mul_comm ‖z‖]
      exact mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)


/-- The sum with the zero index omitted acquires a correction under a unit
translation. Restoring the omitted term makes the distance sum periodic. -/
theorem inv_distance_sq_omit_zero_shift {z : ℂ} (hz : z.im ≠ 0) :
    (∑' m : ℤ, if m = 0 then 0 else (‖z + 1 - (m : ℂ)‖ ^ 2)⁻¹) =
      (∑' m : ℤ, if m = 0 then 0 else (‖z - (m : ℂ)‖ ^ 2)⁻¹) +
        (‖z‖ ^ 2)⁻¹ - (‖z + 1‖ ^ 2)⁻¹ := by
  obtain ⟨C, -, hc⟩ := tsum_inv_distance_sq_horizontal_bound hz
  have hA := (hc z rfl).1.tsum_eq_add_tsum_ite 0
  have hB := (hc (z + 1) (by simp)).1.tsum_eq_add_tsum_ite 0
  have hp :
      (∑' m : ℤ, (‖z + 1 - (m : ℂ)‖ ^ 2)⁻¹) =
        ∑' m : ℤ, (‖z - (m : ℂ)‖ ^ 2)⁻¹ := by
    rw [← (Equiv.addRight (1 : ℤ)).tsum_eq (f := fun m : ℤ => (‖z + 1 - (m : ℂ)‖ ^ 2)⁻¹)]
    apply tsum_congr
    intro m
    simp only [Equiv.coe_addRight, Int.cast_add, Int.cast_one, add_sub_add_right_eq_sub]
  simp only [Int.cast_zero, sub_zero] at hA hB
  linarith only [hA, hB, hp]

end Masullo
