import ComplexLogFourier
import RealLogFourierGaussian
import SchwartzGaussian
import Mathlib.Analysis.Real.Pi.Bounds

open Filter Function MeasureTheory Set Topology
open scoped FourierTransform SchwartzMap

namespace Masullo

noncomputable section

local notation "π" => Real.pi
local notation "γ" => Real.eulerMascheroniConstant
local notation "Tests" => 𝓢(ℂ, ℂ)

private def complexGaussian : Tests := (exists_gaussian_schwartz (E := ℂ) 1 zero_lt_one).choose

private theorem complexGaussian_apply (z : ℂ) :
    complexGaussian z = (Real.exp (-(‖z‖ ^ 2)) : ℂ) := by
  unfold complexGaussian
  simpa only [neg_one_mul] using (exists_gaussian_schwartz (E := ℂ) 1 zero_lt_one).choose_spec z

private theorem complexGaussian_zero : complexGaussian 0 = 1 := by
  simp [complexGaussian_apply]

private theorem fourier_complexGaussian (z : ℂ) :
    (𝓕 complexGaussian) z = ((π * Real.exp (-(π ^ 2 * ‖z‖ ^ 2)) : ℝ) : ℂ) := by
  have hg : (complexGaussian : ℂ → ℂ) = fun z : ℂ ↦ Complex.exp (-(1 : ℂ) * (‖z‖ : ℂ) ^ 2) := by
    funext z
    rw [complexGaussian_apply, Complex.ofReal_exp]
    push_cast
    rw [neg_one_mul]
  rw [SchwartzMap.fourier_coe, hg, fourier_gaussian_innerProductSpace (by simp : 0 < (1 : ℂ).re),
    Complex.finrank_real_complex, show ((2 : ℕ) : ℂ) / 2 = 1 by norm_num,
    Complex.cpow_one, div_one, div_one]
  push_cast
  rw [neg_mul]

private theorem integral_complex_radial_sq (g : ℝ → ℝ) :
    (∫ z : ℂ, g (‖z‖ ^ 2)) = π * ∫ t in Ioi (0 : ℝ), g t := by
  rw [integral_complex_radial (fun r ↦ g (r ^ 2))]
  have h := integral_comp_rpow_Ioi_of_pos (g := g) (p := 2) (by norm_num)
  simp only [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, Real.rpow_two,
    smul_eq_mul, mul_assoc, integral_const_mul] at h
  rw [← h]
  ring

private theorem integral_scaled_log_gaussian {a : ℝ} (ha : 0 < a) :
    (∫ t in Ioi 0, Real.log t * Real.exp (-(a * t))) = a⁻¹ * (-γ - Real.log a) := by
  let g (u : ℝ) := (Real.log u - Real.log a) * Real.exp (-u)
  have hi : IntegrableOn (fun t : ℝ ↦ Real.log a * Real.exp (-t)) (Ioi 0) :=
    (integrableOn_exp_neg_Ioi 0).const_mul _
  calc
    _ = ∫ t in Ioi (0 : ℝ), g (a * t) := by
      refine setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ ?_
      have ht' : 0 < t := ht
      dsimp [g]
      rw [Real.log_mul ha.ne' ht'.ne', add_sub_cancel_left]
    _ = a⁻¹ * ∫ u in Ioi (0 : ℝ), g u := by
      simpa only [mul_zero, smul_eq_mul] using integral_comp_mul_left_Ioi g 0 ha
    _ = _ := by
      simp only [g, sub_mul, integral_sub log_exp_neg_integrableOn hi, integral_log_exp_neg_Ioi,
        integral_const_mul, integral_exp_neg_Ioi_zero, mul_one]

private theorem complexGaussian_logPairing :
    complexEuclideanLogFourierPairing complexGaussian = (-γ - 2 * Real.log π : ℝ) := by
  have hc (z : ℂ) : (2 * Real.log ‖z‖ : ℝ) • (𝓕 complexGaussian) z =
      ((Real.log (‖z‖ ^ 2) * (π * Real.exp (-(π ^ 2 * ‖z‖ ^ 2))) : ℝ) : ℂ) := by
    rw [fourier_complexGaussian, Complex.real_smul, ← Complex.ofReal_mul, Real.log_pow]
    norm_num
  unfold complexEuclideanLogFourierPairing
  simp_rw [hc]
  rw [integral_complex_ofReal, integral_complex_radial_sq (fun t ↦ Real.log t * (π * Real.exp (-(π ^ 2 * t))))]
  apply congrArg Complex.ofReal
  simp_rw [mul_left_comm (Real.log _), integral_const_mul]
  rw [integral_scaled_log_gaussian (sq_pos_of_pos Real.pi_pos), Real.log_pow]
  push_cast
  field_simp

private theorem complexGaussian_cutoff {ε : ℝ} (hε : 0 < ε) :
    complexLogCutoff complexGaussian ε =
      (2 * π * ((∫ t in Ioi ε, Real.exp (-t) * t⁻¹) + Real.log ε) : ℝ) := by
  have hc (z : ℂ) : (‖z‖ ^ 2)⁻¹ • complexGaussian z =
      ((Real.exp (-(‖z‖ ^ 2)) * (‖z‖ ^ 2)⁻¹) : ℝ) := by
    rw [complexGaussian_apply, Complex.real_smul, ← Complex.ofReal_mul, mul_comm]
  have hI : (∫ z in {z : ℂ | ε ≤ ‖z‖ ^ 2}, Real.exp (-(‖z‖ ^ 2)) * (‖z‖ ^ 2)⁻¹) =
      π * ∫ t in Ioi ε, Real.exp (-t) * t⁻¹ := by
    let q := (Ici ε).indicator (fun t : ℝ ↦ Real.exp (-t) * t⁻¹)
    have hQ : (∫ z in {z : ℂ | ε ≤ ‖z‖ ^ 2}, Real.exp (-(‖z‖ ^ 2)) * (‖z‖ ^ 2)⁻¹) =
        ∫ z : ℂ, q (‖z‖ ^ 2) := by
      have hm : MeasurableSet {z : ℂ | ε ≤ ‖z‖ ^ 2} :=
        (isClosed_le continuous_const (continuous_norm.pow 2)).measurableSet
      rw [← integral_indicator hm]
      refine integral_congr_ae (.of_forall fun z ↦ ?_)
      by_cases hz : ε ≤ ‖z‖ ^ 2 <;> simp [q, hz]
    rw [hQ, integral_complex_radial_sq, integral_indicator measurableSet_Ici,
      Measure.restrict_restrict measurableSet_Ici,
      inter_eq_left.mpr (show Ici ε ⊆ Ioi 0 from fun _ hx ↦ hε.trans_le hx),
      integral_Ici_eq_integral_Ioi]
  unfold complexLogCutoff
  simp_rw [hc]
  rw [integral_complex_ofReal, hI, complexGaussian_zero]
  simp only [Complex.real_smul, mul_one, ← Complex.ofReal_add, ← Complex.ofReal_mul]
  congr 1
  ring

private theorem complexGaussian_logRemainder :
    (∫ z : ℂ, complexLogCutoffRemainder complexGaussian z) = (-π * γ : ℝ) := by
  have he := Complex.continuous_ofReal.continuousAt.tendsto.comp
    (exponentialLog_cutoff_tendsto.const_mul (2 * π))
  have hh : Tendsto (complexLogCutoff complexGaussian) (𝓝[>] 0) (𝓝 (↑(2 * π * -γ) : ℂ)) := by
    apply he.congr'
    filter_upwards [show ∀ᶠ ε : ℝ in 𝓝[>] 0, ε ∈ Ioi 0 from self_mem_nhdsWithin] with ε hε
    exact (complexGaussian_cutoff hε).symm
  have h := tendsto_nhds_unique (complexLogCutoff_tendsto complexGaussian) hh
  simp only [Complex.real_smul] at h
  push_cast at h ⊢
  linear_combination h / 2

private theorem complexEuclideanLogFourierPairing_eq_finitePart (f : Tests) :
    complexEuclideanLogFourierPairing f =
      -π⁻¹ • (∫ z : ℂ, complexLogCutoffRemainder f z) - (2 * (γ + Real.log π)) • f 0 := by
  let g := complexGaussian
  let c := f 0
  let h := f - c • g
  have hh0 : h 0 = 0 := by simp [h, c, g, complexGaussian_zero]
  have hF : (fun z : ℂ ↦ (2 * Real.log ‖z‖ : ℝ) • (𝓕 h) z) = fun z : ℂ ↦
      (2 * Real.log ‖z‖ : ℝ) • (𝓕 f) z - c • ((2 * Real.log ‖z‖ : ℝ) • (𝓕 g) z) := by
    funext z
    rw [show (𝓕 h : Tests) = 𝓕 f - c • 𝓕 g by
      simp only [h, sub_eq_add_neg, FourierTransform.fourier_add,
        FourierTransform.fourier_neg, FourierTransform.fourier_smul]]
    simp only [sub_apply, smul_apply, smul_sub, smul_comm (2 * Real.log ‖z‖) c]
  have hP : complexEuclideanLogFourierPairing h =
      complexEuclideanLogFourierPairing f - c • complexEuclideanLogFourierPairing g := by
    unfold complexEuclideanLogFourierPairing
    have hi (a : Tests) : Integrable (fun z : ℂ ↦ (2 * Real.log ‖z‖ : ℝ) • (𝓕 a) z) := by
      simp_rw [mul_smul]
      exact (complexLogSchwartz_integrable (𝓕 a)).smul (2 : ℝ)
    have hg : Integrable (fun z : ℂ ↦ c • ((2 * Real.log ‖z‖ : ℝ) • (𝓕 g) z)) := (hi g).smul c
    rw [hF, integral_sub (hi f) hg, integral_smul]
  have hR (z : ℂ) : complexLogCutoffRemainder h z =
      complexLogCutoffRemainder f z - c • complexLogCutoffRemainder g z := by
    unfold complexLogCutoffRemainder
    simp only [h, sub_apply, smul_apply, indicator_sub, indicator_const_smul_apply,
      smul_sub, smul_comm ((‖z‖ ^ 2)⁻¹) c]
    abel
  have hS : (∫ z : ℂ, complexLogCutoffRemainder h z) =
      (∫ z : ℂ, complexLogCutoffRemainder f z) - c • ∫ z : ℂ, complexLogCutoffRemainder g z := by
    have hg : Integrable (fun z : ℂ ↦ c • complexLogCutoffRemainder g z) :=
      (complexLogCutoffRemainder_integrable g).smul c
    rw [integral_congr_ae (.of_forall hR),
      integral_sub (complexLogCutoffRemainder_integrable f) hg, integral_smul]
  have he := complexEuclideanLogFourierPairing_of_zero h hh0
  rw [hP, hS, complexGaussian_logPairing, complexGaussian_logRemainder] at he
  change complexEuclideanLogFourierPairing f = _ - _ • c
  simp only [Complex.real_smul, smul_eq_mul] at he ⊢
  push_cast at he ⊢
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp [hπ] at he ⊢
  linear_combination he

/-- The complex clause of B.4.3.2 with the trace character and self-dual measure. -/
theorem complexTraceLogFourierPairing_eq_finitePart (f : Tests) :
    complexTraceLogFourierPairing f =
      -π⁻¹ • (∫ z : ℂ, complexLogCutoffRemainder f z) - (2 * (γ + Real.log (2 * π))) • f 0 := by
  rw [complexTraceLogFourierPairing_eq_euclidean, complexEuclideanLogFourierPairing_eq_finitePart,
    Real.log_mul two_ne_zero Real.pi_ne_zero, ← sub_add_eq_sub_sub, ← add_smul]
  congr 2
  ring

/-- The corrected complex logarithmic Fourier formula with the squared-modulus cutoff. -/
theorem complexLogFourier_cutoff_corrected (f : Tests) :
    Tendsto (fun ε ↦ -((2 : ℝ) * π)⁻¹ • complexLogCutoff f ε -
      (2 * (γ + Real.log (2 * π))) • f 0)
      (𝓝[>] 0) (𝓝 (complexTraceLogFourierPairing f)) := by
  rw [complexTraceLogFourierPairing_eq_finitePart]
  have h := ((complexLogCutoff_tendsto f).const_smul (-((2 : ℝ) * π)⁻¹)).sub_const
    ((2 * (γ + Real.log (2 * π))) • f 0)
  rw [smul_smul, show -((2 : ℝ) * π)⁻¹ * 2 = -π⁻¹ by field_simp [Real.pi_ne_zero]] at h
  exact h

/-- The printed complex coefficients fail on the Gaussian test. -/
theorem complexLogFourier_cutoff_printed_false :
    ¬ ∀ f : Tests, Tendsto (fun ε ↦ -complexLogCutoff f ε -
      (4 * π * (γ + Real.log (2 * π))) • f 0)
      (𝓝[>] 0) (𝓝 (complexTraceLogFourierPairing f)) := by
  intro h
  have hh := ((complexLogCutoff_tendsto complexGaussian).neg.sub_const
    ((4 * π * (γ + Real.log (2 * π))) • complexGaussian 0))
  have he := tendsto_nhds_unique (h complexGaussian) hh
  rw [complexTraceLogFourierPairing_eq_euclidean, complexGaussian_logPairing, complexGaussian_zero,
    complexGaussian_logRemainder, Real.log_mul two_ne_zero Real.pi_ne_zero] at he
  simp only [Complex.real_smul, mul_one] at he
  push_cast at he
  have hr := congrArg Complex.re he
  norm_num [Complex.sub_re, Complex.neg_re, Complex.mul_re, Complex.add_re] at hr
  rw [show (Complex.log 2).re = Real.log 2 by rw [Complex.log_re]; norm_num] at hr
  have hγ : 0 < γ := (by norm_num : (0 : ℝ) < 1 / 2).trans Real.one_half_lt_eulerMascheroniConstant
  have hπ : 1 < π := (by norm_num : (1 : ℝ) < 3).trans Real.pi_gt_three
  have hlogπ : 0 < Real.log π := Real.log_pos hπ
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  nlinarith [mul_pos (show 0 < 2 * π - 1 by linarith)
    (show 0 < γ + 2 * (Real.log 2 + Real.log π) by linarith)]

end
end Masullo
