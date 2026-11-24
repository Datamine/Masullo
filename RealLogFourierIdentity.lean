import ArchimedeanLogGaussianKernel
import RealLogFourierGaussian

open Filter Function MeasureTheory Set Topology
open scoped FourierTransform SchwartzMap

namespace Masullo

noncomputable section

local notation "π" => Real.pi

private def realFourierGaussianWeight (t x : ℝ) : ℝ :=
  Real.sqrt (π / t) * Real.exp (-((π * x) ^ 2 / t))

private theorem integral_realFourierGaussianWeight {x : ℝ} (hx : x ≠ 0) :
    (∫ t in Ioi 0, t⁻¹ * realFourierGaussianWeight t x) = ‖x‖⁻¹ := by
  let a := (π * x) ^ 2
  have ha : 0 < a := sq_pos_of_ne_zero (mul_ne_zero Real.pi_ne_zero hx)
  let g (t : ℝ) := t ^ ((1 : ℝ) / 2 - 1) * Real.exp (-(a * t))
  have hsub := integral_comp_rpow_Ioi g (p := -1) (by norm_num)
  have he : (∫ t in Ioi 0, t⁻¹ * realFourierGaussianWeight t x) =
      Real.sqrt π * ∫ t in Ioi 0, g t := by
    rw [← hsub, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ ?_
    have ht0 : 0 < t := ht
    simp only [realFourierGaussianWeight, g, abs_neg, abs_one, one_mul, smul_eq_mul,
      show (-1 : ℝ) - 1 = -2 by norm_num, Real.rpow_neg ht0.le, Real.rpow_two, Real.rpow_one]
    rw [show (1 : ℝ) / 2 - 1 = -(1 / 2) by norm_num, Real.rpow_neg (inv_nonneg.mpr ht0.le),
      ← Real.sqrt_eq_rpow, Real.sqrt_inv, Real.sqrt_div Real.pi_pos.le, div_eq_mul_inv]
    change t⁻¹ * (√π * (√t)⁻¹ * Real.exp (-(a * t⁻¹))) =
      √π * ((t ^ 2)⁻¹ * (((√t)⁻¹)⁻¹ * Real.exp (-(a * t⁻¹))))
    have hs := Real.sq_sqrt ht0.le
    have hsn := (Real.sqrt_pos.2 ht0).ne'
    rw [inv_inv]
    field_simp
    rw [hs]
  rw [he]
  have hΓ : (∫ t in Ioi 0, g t) = (1 / a) ^ ((1 : ℝ) / 2) * Real.Gamma (1 / 2) :=
    Real.integral_rpow_mul_exp_neg_mul_Ioi (by norm_num) ha
  rw [hΓ, Real.Gamma_one_half_eq, ← Real.sqrt_eq_rpow, one_div, Real.sqrt_inv,
    show √a = ‖π * x‖ by rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs],
    norm_mul, Real.norm_of_nonneg Real.pi_pos.le, mul_inv]
  have hs := Real.sq_sqrt Real.pi_pos.le
  field_simp [Real.pi_ne_zero, norm_ne_zero_iff.mpr hx]
  nlinarith

private theorem realFourierGaussianWeight_integrable {x : ℝ} (hx : x ≠ 0) :
    IntegrableOn (fun t ↦ t⁻¹ * realFourierGaussianWeight t x) (Ioi 0) := by
  by_contra h
  have hh := integral_realFourierGaussianWeight hx
  rw [integral_undef h] at hh
  exact (inv_ne_zero (norm_ne_zero_iff.mpr hx)) hh.symm

private theorem realFourierGaussian_swap (f : 𝓢(ℝ, ℂ)) {t : ℝ} (ht : 0 < t) :
    (∫ x : ℝ, Real.exp (-(t * x ^ 2)) • (𝓕 f) x) =
      ∫ x : ℝ, realFourierGaussianWeight t x • f x := by
  let a := √(π / t)
  have ha : 0 < a := Real.sqrt_pos.2 (div_pos Real.pi_pos ht)
  have ha₂ : a ^ 2 = π / t := Real.sq_sqrt (div_nonneg Real.pi_pos.le ht.le)
  let g := realSchwartzDilate a ha realGaussianPi
  have hg (x : ℝ) : g x = (Real.exp (-(t * x ^ 2)) : ℂ) := by
    change realSchwartzDilate a ha realGaussianPi x = _
    rw [realSchwartzDilate_apply, realGaussianPi_apply, mul_pow, inv_pow, ha₂]
    have h : π * ((π / t)⁻¹ * x ^ 2) = t * x ^ 2 := by
      rw [inv_div]
      field_simp
    rw [h]
  have hgF (x : ℝ) : (𝓕 g) x = (realFourierGaussianWeight t x : ℂ) := by
    change (𝓕 (realSchwartzDilate a ha realGaussianPi)) x = _
    rw [realFourier_dilate, fourier_realGaussianPi, realGaussianPi_apply,
      Complex.real_smul, ← Complex.ofReal_mul, mul_pow, ha₂]
    have h : π * (π / t * x ^ 2) = (π * x) ^ 2 / t := by
      field_simp
    rw [h]
    rfl
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ ℝ)
    Real.continuous_fourierChar continuous_inner (f.integrable (μ := volume))
    (g.integrable (μ := volume))
  have hh : (∫ x : ℝ, (𝓕 f) x * g x) = ∫ x : ℝ, f x * (𝓕 g) x := by
    simpa using! h
  simpa only [hg, hgF, Complex.real_smul, mul_comm] using hh

private theorem ae_real_ne_zero : ∀ᵐ x : ℝ ∂volume, x ≠ 0 := ae_iff.mpr (by
  simpa only [not_not, ofPred_eq_eq_singleton] using measure_singleton (0 : ℝ) (μ := volume))

private theorem realLogCutoffRemainder_of_zero (f : 𝓢(ℝ, ℂ)) (hf : f 0 = 0) (x : ℝ) :
    realLogCutoffRemainder f x = ‖x‖⁻¹ • f x := by
  simp [realLogCutoffRemainder, hf]

private theorem integral_realFourierGaussian_smul (f : 𝓢(ℝ, ℂ)) (hf : f 0 = 0) :
    (∫ t in Ioi (0 : ℝ), t⁻¹ • ∫ x : ℝ, realFourierGaussianWeight t x • f x) =
      ∫ x : ℝ, ‖x‖⁻¹ • f x := by
  let F (x t : ℝ) := (t⁻¹ * realFourierGaussianWeight t x) • f x
  have hm : Measurable (Function.uncurry F) := by
    have ht : Measurable (Prod.snd : ℝ × ℝ → ℝ) := measurable_snd
    have hx : Measurable (Prod.fst : ℝ × ℝ → ℝ) := measurable_fst
    exact (ht.inv.mul ((Real.continuous_sqrt.measurable.comp
      (measurable_const.div ht)).mul (Real.measurable_exp.comp
      (((measurable_const.mul hx).pow_const 2).div ht).neg))).smul
      (f.continuous.measurable.comp hx)
  have hW (t x : ℝ) (ht : t ∈ Ioi (0 : ℝ)) :
      0 ≤ t⁻¹ * realFourierGaussianWeight t x := by
    exact mul_nonneg (inv_nonneg.mpr (mem_Ioi.mp ht).le)
      (mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le)
  have hnorm (x : ℝ) : (∫ t in Ioi (0 : ℝ), ‖F x t‖) =
      (∫ t in Ioi (0 : ℝ), t⁻¹ * realFourierGaussianWeight t x) * ‖f x‖ := by
    rw [← integral_mul_const]
    exact setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ by
      simp only [F, norm_smul, Real.norm_of_nonneg (hW t x ht)]
  have hiR : Integrable (fun x : ℝ ↦ ‖x‖⁻¹ • f x) := by
    exact (realLogCutoffRemainder_integrable f).congr (.of_forall (realLogCutoffRemainder_of_zero f hf))
  have hi : Integrable (Function.uncurry F) (volume.prod (volume.restrict (Ioi 0))) := by
    refine (integrable_prod_iff hm.aestronglyMeasurable).mpr ⟨?_, ?_⟩
    · filter_upwards [ae_real_ne_zero] with x hx
      exact (realFourierGaussianWeight_integrable hx).smul_const (f x)
    · refine hiR.norm.congr (ae_real_ne_zero.mono fun x hx ↦ ?_)
      change ‖‖x‖⁻¹ • f x‖ = ∫ t in Ioi (0 : ℝ), ‖F x t‖
      rw [hnorm, integral_realFourierGaussianWeight hx, norm_smul,
        Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg x))]
  calc
    _ = ∫ t in Ioi (0 : ℝ), ∫ x : ℝ, F x t := by
      simp only [← integral_smul, F, mul_smul]
    _ = ∫ x : ℝ, ∫ t in Ioi (0 : ℝ), F x t := (integral_integral_swap hi).symm
    _ = _ := integral_congr_ae (ae_real_ne_zero.mono fun x hx ↦ by
      simp only [F, integral_smul_const, integral_realFourierGaussianWeight hx])

private theorem realLogFourierPairing_of_zero (f : 𝓢(ℝ, ℂ)) (hf : f 0 = 0) :
    realLogFourierPairing f = -(2 : ℝ)⁻¹ • ∫ x : ℝ, ‖x‖⁻¹ • f x := by
  let g := (𝓕 f : 𝓢(ℝ, ℂ))
  have hG : (∫ x : ℝ, g x) = 0 := (integral_realSchwartz_fourier f).trans hf
  have hgI : Integrable (fun x : ℝ ↦ g x) := g.integrable
  have hF (t : ℝ) (ht : t ∈ Ioi (0 : ℝ)) :
      (∫ x : ℝ, gaussianLogKernel (‖x‖ ^ 2) t • g x) =
        -(t⁻¹ • ∫ x : ℝ, realFourierGaussianWeight t x • f x) := by
    have hI : Integrable (fun x : ℝ ↦ Real.exp (-(t * x ^ 2)) • g x) := by
      refine hgI.norm.mono' (by fun_prop) (.of_forall fun x ↦ ?_)
      rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
      apply mul_le_of_le_one_left (norm_nonneg (g x))
      exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg (mem_Ioi.mp ht).le (sq_nonneg x)))
    have h0 : (fun x : ℝ ↦ gaussianLogKernel (‖x‖ ^ 2) t • g x) = fun x : ℝ ↦ t⁻¹ •
        (Real.exp (-t) • g x - Real.exp (-(t * x ^ 2)) • g x) := by
      funext x
      rw [gaussianLogKernel, mul_smul, sub_smul, Real.norm_eq_abs, sq_abs, mul_comm (x ^ 2) t]
    have hE : Integrable (fun x : ℝ ↦ Real.exp (-t) • g x) :=
      hgI.smul (Real.exp (-t))
    rw [h0, integral_smul, integral_sub hE hI, integral_smul, hG,
      smul_zero, zero_sub, smul_neg]
    rw [realFourierGaussian_swap f (mem_Ioi.mp ht)]
  unfold realLogFourierPairing
  rw [integral_log_norm_smul_eq_gaussian ae_real_ne_zero g.continuous.measurable
    (realLogSchwartz_integrable g), setIntegral_congr_fun measurableSet_Ioi hF, integral_neg,
    smul_neg, ← neg_smul, integral_realFourierGaussian_smul f hf]

/-- The corrected real clause of B.4.3.2, with the subtracted unit cutoff. -/
theorem realLogFourierPairing_eq_finitePart (f : 𝓢(ℝ, ℂ)) :
    realLogFourierPairing f =
      -(2 : ℝ)⁻¹ • (∫ x : ℝ, realLogCutoffRemainder f x) -
        (Real.eulerMascheroniConstant + Real.log (2 * π)) • f 0 := by
  let g := realGaussianPi
  let c := f 0
  let h := f - c • g
  have hg0 : g 0 = 1 := by simp [g, realGaussianPi_apply]
  have hh0 : h 0 = 0 := by simp [h, hg0, c]
  have hF : (fun x : ℝ ↦ Real.log ‖x‖ • (𝓕 h) x) = fun x : ℝ ↦
      Real.log ‖x‖ • (𝓕 f) x - c • (Real.log ‖x‖ • (𝓕 g) x) := by
    funext x
    rw [show (𝓕 h : 𝓢(ℝ, ℂ)) = 𝓕 f - c • 𝓕 g by
      simp only [h, sub_eq_add_neg, FourierTransform.fourier_add,
        FourierTransform.fourier_neg, FourierTransform.fourier_smul]]
    simp only [sub_apply, smul_apply, smul_sub, smul_comm (Real.log ‖x‖) c]
  have hP : realLogFourierPairing h = realLogFourierPairing f - c • realLogFourierPairing g := by
    unfold realLogFourierPairing
    have hI : Integrable (fun x : ℝ ↦ c • (Real.log ‖x‖ • (𝓕 g) x)) :=
      (realLogSchwartz_integrable (𝓕 g)).smul c
    rw [hF, integral_sub (realLogSchwartz_integrable (𝓕 f)) hI, integral_smul]
  have hR (x : ℝ) : realLogCutoffRemainder h x =
      realLogCutoffRemainder f x - c • realLogCutoffRemainder g x := by
    unfold realLogCutoffRemainder
    simp only [h, sub_apply, smul_apply, indicator_sub,
      indicator_const_smul_apply, smul_sub, smul_comm (‖x‖⁻¹) c]
    abel
  have hS : (∫ x : ℝ, ‖x‖⁻¹ • h x) =
      (∫ x : ℝ, realLogCutoffRemainder f x) - c • ∫ x : ℝ, realLogCutoffRemainder g x := by
    have hG : Integrable (fun x : ℝ ↦ c • realLogCutoffRemainder g x) :=
      (realLogCutoffRemainder_integrable g).smul c
    calc
      _ = ∫ x : ℝ, realLogCutoffRemainder h x :=
        integral_congr_ae (.of_forall fun x ↦ (realLogCutoffRemainder_of_zero h hh0 x).symm)
      _ = _ := by
        rw [integral_congr_ae (.of_forall hR),
          integral_sub (realLogCutoffRemainder_integrable f) hG, integral_smul]
  have he := realLogFourierPairing_of_zero h hh0
  rw [hP, hS, realLogFourierPairing_gaussianPi, realGaussianPi_logRemainder] at he
  have hfour : Real.log (4 * π) = 2 * Real.log 2 + Real.log π := by
    rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) Real.pi_ne_zero,
      show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    norm_num
  rw [hfour] at he
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero]
  change realLogFourierPairing f = _ - _ • c
  simp only [Complex.real_smul, smul_eq_mul] at he ⊢
  push_cast at he ⊢
  linear_combination he

/-- The corrected real logarithmic Fourier formula in the manuscript's cutoff convention. -/
theorem realLogFourier_cutoff_corrected (f : 𝓢(ℝ, ℂ)) :
    Tendsto (fun ε ↦ -(2 : ℝ)⁻¹ • realLogCutoff f ε -
      (Real.eulerMascheroniConstant + Real.log (2 * π)) • f 0)
      (𝓝[>] 0) (𝓝 (realLogFourierPairing f)) := by
  rw [realLogFourierPairing_eq_finitePart]
  exact ((realLogCutoff_tendsto f).const_smul _).sub_const _

end
end Masullo
