import RealLogFourier
import SchwartzGaussian
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

open Filter Function MeasureTheory Set Topology
open scoped FourierTransform SchwartzMap

namespace Masullo

noncomputable section

set_option maxHeartbeats 1500000

local notation "γ" => Real.eulerMascheroniConstant
local notation "π" => Real.pi

private def gaussianSchwartzProfile : 𝓢(ℝ, ℂ) :=
  (exists_gaussian_schwartz (E := ℝ) 1 zero_lt_one).choose

@[simp] private theorem gaussianSchwartzProfile_apply (x : ℝ) :
    gaussianSchwartzProfile x = (Real.exp (-(x ^ 2)) : ℂ) := by
  unfold gaussianSchwartzProfile
  simpa only [neg_one_mul, Real.norm_eq_abs, sq_abs] using
    (exists_gaussian_schwartz (E := ℝ) 1 zero_lt_one).choose_spec x

private theorem gamma_logMoment {s : ℝ} (hs : 0 < s) :
    (((∫ t in Ioi (0 : ℝ), t ^ (s - 1) * (Real.log t * Real.exp (-t))) : ℝ) : ℂ) =
      deriv Complex.Gamma (s : ℂ) := by
  have hp : 0 < (s : ℂ).re := by simpa using hs
  have he : Complex.GammaIntegral =ᶠ[𝓝 (s : ℂ)] Complex.Gamma := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hp] with z hz
    exact (Complex.Gamma_eq_integral hz).symm
  have h := ((Complex.hasDerivAt_GammaIntegral hp).congr_of_eventuallyEq he.symm).deriv
  rw [h]
  rw [← integral_complex_ofReal]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  change ↑(t ^ (s - 1) * (Real.log t * Real.exp (-t))) =
    (t : ℂ) ^ ((s : ℂ) - 1) * ((Real.log t : ℂ) * (Real.exp (-t) : ℂ))
  rw [Complex.ofReal_mul, Complex.ofReal_mul, Complex.ofReal_cpow (le_of_lt ht),
    Complex.ofReal_sub, Complex.ofReal_one]

/-- The first exponential logarithmic moment is Euler's constant with a minus sign. -/
theorem integral_log_exp_neg_Ioi :
    (∫ t in Ioi (0 : ℝ), Real.log t * Real.exp (-t)) = -γ := by
  have h := gamma_logMoment (s := 1) zero_lt_one
  simp only [sub_self, Real.rpow_zero, one_mul, Complex.ofReal_one,
    Complex.hasDerivAt_Gamma_one.deriv] at h
  exact Complex.ofReal_injective (by simpa only [Complex.ofReal_neg] using h)

private theorem integral_log_exp_neg_half_Ioi :
    (∫ t in Ioi (0 : ℝ), t ^ ((1 / 2 : ℝ) - 1) * (Real.log t * Real.exp (-t))) =
      -Real.sqrt π * (γ + 2 * Real.log 2) := by
  have h := gamma_logMoment (s := 1 / 2) (by norm_num)
  rw [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat,
    Complex.hasDerivAt_Gamma_one_half.deriv] at h
  exact Complex.ofReal_injective (by
    simpa only [Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_add, Complex.ofReal_ofNat,
      Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)] using h)

theorem log_exp_neg_integrableOn : IntegrableOn (fun t : ℝ ↦ Real.log t * Real.exp (-t)) (Ioi 0) := by
  have hm : AEStronglyMeasurable (fun t : ℝ ↦ Real.log t * Real.exp (-t)) volume :=
    (Real.measurable_log.mul (Real.continuous_exp.comp continuous_neg).measurable).aestronglyMeasurable
  have hn : IntegrableOn (fun t : ℝ ↦ Real.log t * Real.exp (-t)) (Ioc 0 1) := by
    refine ((intervalIntegral.intervalIntegrable_log' (a := 0) (b := 1)).1.norm).mono'
      (hm.mono_measure Measure.restrict_le_self) ?_
    refine (ae_restrict_mem measurableSet_Ioc).mono fun x hx ↦ ?_
    rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le]
    exact mul_le_of_le_one_right (norm_nonneg _) (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hx.1.le))
  have hGamma : IntegrableOn (fun t : ℝ ↦ t * Real.exp (-t)) (Ioi 0) := by
    simpa only [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, mul_comm] using
      Real.GammaIntegral_convergent (s := 2) (by norm_num)
  have ht : IntegrableOn (fun t : ℝ ↦ Real.log t * Real.exp (-t)) (Ioi 1) := by
    refine ((hGamma.mono_set (Ioi_subset_Ioi (by norm_num))).norm).mono'
      (hm.mono_measure Measure.restrict_le_self) ?_
    refine (ae_restrict_mem measurableSet_Ioi).mono fun x hx ↦ ?_
    have h₁ : 1 < x := hx
    have hx₀ : 0 < x := zero_lt_one.trans h₁
    rw [norm_mul, norm_mul, Real.norm_of_nonneg (Real.log_nonneg h₁.le),
      Real.norm_of_nonneg hx₀.le]
    exact mul_le_mul_of_nonneg_right ((Real.log_le_sub_one_of_pos hx₀).trans (sub_le_self _ zero_le_one))
      (norm_nonneg _)
  rw [← Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1)]
  exact hn.union ht

private theorem integral_log_gaussian_Ioi :
    (∫ x in Ioi (0 : ℝ), Real.log x * Real.exp (-(x ^ 2))) =
      (-Real.sqrt π * (γ + 2 * Real.log 2)) / 4 := by
  let g (t : ℝ) := t ^ ((1 / 2 : ℝ) - 1) * (Real.log t * Real.exp (-t))
  have h := integral_comp_rpow_Ioi_of_pos (g := g) (p := 2) (by norm_num)
  have he : (∫ x in Ioi (0 : ℝ), (2 * x ^ ((2 : ℝ) - 1)) • g (x ^ (2 : ℝ))) =
      4 * ∫ x in Ioi (0 : ℝ), Real.log x * Real.exp (-(x ^ 2)) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    have hx' : 0 < x := hx
    have hpow : (x ^ (2 : ℝ)) ^ ((1 / 2 : ℝ) - 1) = x⁻¹ := by
      rw [← Real.rpow_mul hx'.le]
      norm_num
      rw [Real.rpow_neg_one]
    have hh : (x ^ (2 : ℕ)) ^ ((1 / 2 : ℝ) - 1) = x⁻¹ := by simpa only [Real.rpow_two] using hpow
    simp only [g, Real.rpow_two, hh, Real.log_pow, show (2 : ℝ) - 1 = 1 by norm_num,
      Real.rpow_one, smul_eq_mul, Nat.cast_ofNat]
    field_simp
    ring
  rw [he, show (∫ t in Ioi (0 : ℝ), g t) = _ from integral_log_exp_neg_half_Ioi] at h
  linarith

private theorem log_gaussian_integrable :
    Integrable (fun x : ℝ ↦ Real.log ‖x‖ * Real.exp (-(x ^ 2))) := by
  have hi := (realLogSchwartz_integrable gaussianSchwartzProfile).re
  convert hi using 1
  funext x
  change Real.log ‖x‖ * Real.exp (-(x ^ 2)) = (Real.log ‖x‖ • gaussianSchwartzProfile x).re
  rw [Complex.smul_re, gaussianSchwartzProfile_apply, Complex.ofReal_re, smul_eq_mul]

private theorem integral_log_gaussian :
    (∫ x : ℝ, Real.log ‖x‖ * Real.exp (-(x ^ 2))) =
      -Real.sqrt π * (γ + 2 * Real.log 2) / 2 := by
  let g (x : ℝ) := Real.log ‖x‖ * Real.exp (-(x ^ 2))
  have he (x : ℝ) : g (-x) = g x := by
    simp only [g, norm_neg, neg_sq]
  have h₁ : (∫ x in Ioi (0 : ℝ), g x) =
      (-Real.sqrt π * (γ + 2 * Real.log 2)) / 4 :=
    (setIntegral_congr_fun measurableSet_Ioi fun x hx ↦ by
      dsimp [g]
      rw [abs_of_nonneg (le_of_lt hx)]).trans integral_log_gaussian_Ioi
  have h₂ : (∫ x in (Ioi (0 : ℝ))ᶜ, g x) = ∫ x in Ioi (0 : ℝ), g x := by
    rw [compl_Ioi]
    simpa only [neg_zero, he] using (integral_comp_neg_Ioi 0 g).symm
  change (∫ x : ℝ, g x) = _
  rw [← integral_add_compl measurableSet_Ioi log_gaussian_integrable, h₂, h₁]
  ring

def realGaussianPi : 𝓢(ℝ, ℂ) :=
  realSchwartzDilate (Real.sqrt π)⁻¹ (inv_pos.mpr (Real.sqrt_pos_of_pos Real.pi_pos))
    gaussianSchwartzProfile

theorem realGaussianPi_apply (x : ℝ) :
    realGaussianPi x = (Real.exp (-(π * x ^ 2)) : ℂ) := by
  unfold realGaussianPi
  rw [realSchwartzDilate_apply, inv_inv, gaussianSchwartzProfile_apply,
    mul_pow, Real.sq_sqrt Real.pi_pos.le]

theorem fourier_realGaussianPi : (𝓕 realGaussianPi : 𝓢(ℝ, ℂ)) = realGaussianPi := by
  ext x
  have hf : (realGaussianPi : ℝ → ℂ) = fun x : ℝ ↦ Complex.exp (-(π : ℂ) * (x : ℂ) ^ 2) := by
    funext x
    rw [realGaussianPi_apply, Complex.ofReal_exp]
    push_cast
    rw [neg_mul]
  rw [SchwartzMap.fourier_coe, hf]
  have h := fourier_gaussian_pi (b := (1 : ℂ)) (by simp)
  simp only [mul_one, Complex.one_cpow, div_one, one_mul] at h
  exact congrFun h x

/-- The exact real logarithmic Fourier pairing on the self-dual Gaussian. -/
theorem realLogFourierPairing_gaussianPi :
    realLogFourierPairing realGaussianPi = (-(γ + Real.log (4 * π)) / 2 : ℝ) := by
  rw [realLogFourierPairing, fourier_realGaussianPi]
  have hc : (fun x : ℝ ↦ Real.log ‖x‖ • realGaussianPi x) =
      fun x : ℝ ↦ (↑(Real.log ‖x‖ * Real.exp (-(π * x ^ 2))) : ℂ) := by
    funext x
    rw [realGaussianPi_apply, Complex.real_smul, Complex.ofReal_mul]
  rw [hc, integral_complex_ofReal]
  apply congrArg Complex.ofReal
  let r := Real.sqrt π
  have hr : 0 < r := Real.sqrt_pos_of_pos Real.pi_pos
  have hr₂ : r ^ 2 = π := Real.sq_sqrt Real.pi_pos.le
  let g (y : ℝ) := Real.log ‖r⁻¹ * y‖ * Real.exp (-(y ^ 2))
  have hchange : (∫ x : ℝ, Real.log ‖x‖ * Real.exp (-(π * x ^ 2))) =
      r⁻¹ * ∫ y : ℝ, g y := by
    rw [← smul_eq_mul, ← abs_of_pos (inv_pos.mpr hr), ← Measure.integral_comp_mul_left g r]
    apply integral_congr_ae
    refine .of_forall fun x ↦ ?_
    change Real.log ‖x‖ * Real.exp (-(π * x ^ 2)) =
      Real.log ‖r⁻¹ * (r * x)‖ * Real.exp (-((r * x) ^ 2))
    rw [inv_mul_cancel_left₀ hr.ne', mul_pow, hr₂]
  have hlog : g =ᵐ[volume] fun y ↦
      Real.log ‖y‖ * Real.exp (-(y ^ 2)) - Real.log r * Real.exp (-(y ^ 2)) := by
    have hz : ∀ᵐ y : ℝ ∂volume, y ≠ 0 := ae_iff.mpr (by
      simpa only [not_not, ofPred_eq_eq_singleton] using measure_singleton (0 : ℝ) (μ := volume))
    filter_upwards [hz] with y hy
    dsimp only [g]
    rw [norm_mul, Real.norm_of_nonneg (inv_nonneg.mpr hr.le),
      Real.log_mul (inv_ne_zero hr.ne') (norm_ne_zero_iff.mpr hy), Real.log_inv,
      neg_add_eq_sub, sub_mul]
  have hi : Integrable (fun y : ℝ ↦ Real.log r * Real.exp (-(y ^ 2))) := by
    have h := (integrable_exp_neg_mul_sq (b := 1) zero_lt_one).const_mul (Real.log r)
    simpa only [neg_one_mul] using h
  have hg : (∫ y : ℝ, Real.exp (-(y ^ 2))) = r := by
    simpa only [neg_one_mul, div_one] using integral_gaussian 1
  rw [hchange, integral_congr_ae hlog, integral_sub log_gaussian_integrable hi,
    integral_const_mul, integral_log_gaussian, hg]
  have hrlog : Real.log r = Real.log π / 2 := by
    change Real.log (Real.sqrt π) = _
    rw [Real.log_sqrt Real.pi_pos.le]
  rw [hrlog, Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) Real.pi_pos.ne',
    show Real.log 4 = 2 * Real.log 2 from by
      rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
      norm_num]
  change r⁻¹ * (-r * (γ + 2 * Real.log 2) / 2 - Real.log π / 2 * r) =
    -(γ + (2 * Real.log 2 + Real.log π)) / 2
  field_simp
  ring

private theorem exponentialLog_boundary_atTop :
    Tendsto (fun t : ℝ ↦ Real.exp (-t) * Real.log t) atTop (𝓝 0) := by
  have ht := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
  refine squeeze_zero'
    ((eventually_ge_atTop (1 : ℝ)).mono fun x hx ↦
      mul_nonneg (Real.exp_pos _).le (Real.log_nonneg hx))
    ((eventually_ge_atTop (1 : ℝ)).mono fun x hx ↦ ?_) ht
  rw [pow_one, mul_comm x]
  exact mul_le_mul_of_nonneg_left
    ((Real.log_le_sub_one_of_pos (zero_lt_one.trans_le hx)).trans (sub_le_self _ zero_le_one))
    (Real.exp_pos _).le

private theorem exponentialLog_cutoff_eq {δ : ℝ} (hδ : 0 < δ) :
    (∫ t in Ioi δ, Real.exp (-t) * t⁻¹) + Real.log δ =
      (1 - Real.exp (-δ)) * Real.log δ + ∫ t in Ioi δ, Real.log t * Real.exp (-t) := by
  have hI : IntegrableOn (fun x : ℝ ↦ Real.exp (-x)) (Ioi δ) := by
    have h := Real.GammaIntegral_convergent (s := 1) zero_lt_one
    exact (by simpa only [sub_self, Real.rpow_zero, mul_one] using h :
      IntegrableOn (fun x : ℝ ↦ Real.exp (-x)) (Ioi 0)).mono_set (Ioi_subset_Ioi hδ.le)
  have hmul : IntegrableOn (fun x : ℝ ↦ Real.exp (-x) * x⁻¹) (Ioi δ) := by
    refine (hI.norm.const_mul δ⁻¹).mono'
      (((Real.continuous_exp.comp continuous_neg).measurable.mul measurable_inv).aestronglyMeasurable) ?_
    refine (ae_restrict_mem measurableSet_Ioi).mono fun x hx ↦ ?_
    have hx' : 0 < x := hδ.trans hx
    rw [norm_mul, Real.norm_of_nonneg (inv_pos.mpr hx').le, mul_comm δ⁻¹]
    exact mul_le_mul_of_nonneg_left (inv_anti₀ hδ hx.le) (norm_nonneg _)
  let e (x : ℝ) := Real.exp (-x)
  let w (x : ℝ) := Real.log x
  have he' (x : ℝ) (_ : x ∈ Ioi δ) : HasDerivAt e (- e x) x := by
    simpa only [e, Pi.neg_apply, id_eq, neg_one_mul, mul_neg, mul_one] using
      ((hasDerivAt_id x).neg.exp)
  have hw' (x : ℝ) (hx : x ∈ Ioi δ) : HasDerivAt w x⁻¹ x :=
    Real.hasDerivAt_log (hδ.trans hx).ne'
  have hmul' : IntegrableOn ((fun x : ℝ ↦ - e x) * w) (Ioi δ) := by
    have hi := (log_exp_neg_integrableOn.mono_set (Ioi_subset_Ioi hδ.le)).neg
    convert hi using 1
    funext x
    change -Real.exp (-x) * Real.log x = -(Real.log x * Real.exp (-x))
    ring
  have hc : ContinuousAt (fun x : ℝ ↦ e x * w x) δ :=
    ((Real.continuous_exp.comp continuous_neg).continuousAt).mul (Real.continuousAt_log hδ.ne')
  have hb : Tendsto (e * w) (𝓝[>] δ) (𝓝 (e δ * w δ)) :=
    hc.tendsto.mono_left nhdsWithin_le_nhds
  have hm : IntegrableOn (e * (fun x : ℝ ↦ x⁻¹)) (Ioi δ) := hmul
  have h := integral_Ioi_mul_deriv_eq_deriv_mul he' hw' hm hmul' hb exponentialLog_boundary_atTop
  change (∫ x in Ioi δ, e x * x⁻¹) = 0 - e δ * w δ - ∫ x in Ioi δ, -e x * w x at h
  rw [show (fun x : ℝ ↦ -e x * w x) = fun x ↦ -(Real.log x * Real.exp (-x)) from
    funext fun x ↦ by dsimp [e, w]; ring, integral_neg] at h
  change (∫ t in Ioi δ, e t * t⁻¹) + Real.log δ = _
  rw [h]
  dsimp [e, w]
  ring

theorem exponentialLog_cutoff_tendsto :
    Tendsto (fun δ : ℝ ↦ (∫ t in Ioi δ, Real.exp (-t) * t⁻¹) + Real.log δ)
      (𝓝[>] 0) (𝓝 (-γ)) := by
  have hpos : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < δ := self_mem_nhdsWithin
  have hb : Tendsto (fun t : ℝ ↦ (1 - Real.exp (-t)) * Real.log t) (𝓝[>] 0) (𝓝 0) := by
    refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
    have hzero : Tendsto (fun t : ℝ ↦ ‖t * Real.log t‖) (𝓝[>] 0) (𝓝 0) := by
      simpa only [zero_mul, norm_zero] using
        ((Real.continuous_mul_log.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds).norm
    refine squeeze_zero' (.of_forall fun _ ↦ norm_nonneg _) ?_ hzero
    filter_upwards [hpos] with t ht
    have he₀ : 0 ≤ 1 - Real.exp (-t) := sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht.le))
    have he₁ : 1 - Real.exp (-t) ≤ t := by linarith [Real.add_one_le_exp (-t)]
    rw [norm_mul, norm_mul, Real.norm_of_nonneg he₀, Real.norm_of_nonneg ht.le]
    exact mul_le_mul_of_nonneg_right he₁ (norm_nonneg _)
  let w := (Ioi (0 : ℝ)).indicator (fun x ↦ Real.log x * Real.exp (-x))
  have hw : Integrable w := (integrable_indicator_iff measurableSet_Ioi).mpr log_exp_neg_integrableOn
  have hW : (∫ x, w x) = -γ := by
    rw [show w = (Ioi (0 : ℝ)).indicator (fun x ↦ Real.log x * Real.exp (-x)) from rfl,
      integral_indicator measurableSet_Ioi, integral_log_exp_neg_Ioi]
  have ht : Tendsto (fun δ : ℝ ↦ ∫ x : ℝ, (Ioi δ).indicator w x) (𝓝[>] 0) (𝓝 (-γ)) := by
    rw [← hW]
    refine tendsto_integral_filter_of_dominated_convergence (fun x : ℝ ↦ ‖w x‖)
      (.of_forall fun δ ↦ hw.aestronglyMeasurable.indicator measurableSet_Ioi)
      (.of_forall fun δ ↦ .of_forall fun x ↦ ?_) hw.norm (.of_forall fun x ↦ ?_)
    · by_cases hx : x ∈ Ioi δ
      · rw [indicator_of_mem hx]
      · rw [indicator_of_notMem hx, norm_zero]
        exact norm_nonneg _
    · refine tendsto_const_nhds.congr' ?_
      by_cases hx : 0 < x
      · have he := (show ∀ᶠ δ : ℝ in 𝓝 (0 : ℝ), δ < x from Iio_mem_nhds hx).filter_mono
          (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
        filter_upwards [he] with δ hδ
        exact (indicator_of_mem (show x ∈ Ioi δ from hδ) w).symm
      · have he : w x = 0 := indicator_of_notMem hx _
        filter_upwards [hpos] with δ hδ
        rw [indicator_of_notMem (show x ∉ Ioi δ from fun hz ↦ hx (hδ.trans hz)), he]
  have ht' := hb.add ht
  rw [zero_add] at ht'
  apply ht'.congr'
  filter_upwards [hpos] with δ hδ
  have hI : (∫ x, (Ioi δ).indicator w x) = ∫ x in Ioi δ, Real.log x * Real.exp (-x) := by
    rw [integral_indicator measurableSet_Ioi]
    exact setIntegral_congr_fun measurableSet_Ioi fun x hx ↦
      indicator_of_mem (show x ∈ Ioi 0 from hδ.trans hx) _
  rw [hI, exponentialLog_cutoff_eq hδ]

private theorem gaussianLog_cutoff_eq {ε : ℝ} (hε : 0 < ε) :
    realLogCutoff gaussianSchwartzProfile ε =
      ((∫ t in Ioi (ε ^ 2), Real.exp (-t) * t⁻¹) + Real.log (ε ^ 2) : ℝ) := by
  let g (x : ℝ) := ‖x‖⁻¹ * Real.exp (-(x ^ 2))
  have hg (x : ℝ) : ‖x‖⁻¹ • gaussianSchwartzProfile x = (g x : ℂ) := by
    rw [gaussianSchwartzProfile_apply, Complex.real_smul]
    simp only [g, Complex.ofReal_mul]
  have hL : {x : ℝ | ε ≤ ‖x‖} = Ici ε ∪ Iic (-ε) := by
    ext x
    simp only [mem_ofPred_eq, mem_union, mem_Ici, mem_Iic, Real.norm_eq_abs, le_abs]
    exact or_congr Iff.rfl ⟨fun h ↦ by linarith, fun h ↦ by linarith⟩
  have hi : IntegrableOn g (Ici ε ∪ Iic (-ε)) := by
    have h := realLogCutoff_integrableOn gaussianSchwartzProfile hε
    rw [hL] at h
    refine h.re.congr (.of_forall fun x ↦ ?_)
    change (‖x‖⁻¹ • gaussianSchwartzProfile x).re = g x
    rw [hg, Complex.ofReal_re]
  have hdis : Disjoint (Ici ε) (Iic (-ε)) := Set.disjoint_left.mpr fun x hx hy ↦
    hε.not_ge ((show ε ≤ x from hx).trans (show x ≤ -ε from hy) |>.trans (neg_nonpos.mpr hε.le))
  have hneg : (∫ x in Iic (-ε), g x) = ∫ x in Ici ε, g x := by
    rw [integral_Ici_eq_integral_Ioi]
    simpa only [g, norm_neg, neg_sq] using (integral_comp_neg_Ioi ε g).symm
  have hsub : (∫ t in Ioi (ε ^ 2), Real.exp (-t) * t⁻¹) =
      2 * ∫ x in Ici ε, g x := by
    rw [integral_Ici_eq_integral_Ioi, ← integral_const_mul]
    have h := integral_comp_rpow_Ioi_of_pos' (p := 2) (c := ε ^ 2)
      (g := fun t : ℝ ↦ Real.exp (-t) * t⁻¹) (by norm_num) (sq_nonneg ε)
    rw [show (ε ^ 2 : ℝ) ^ (2 : ℝ)⁻¹ = ε by
      rw [inv_eq_one_div, ← Real.sqrt_eq_rpow, Real.sqrt_sq hε.le]] at h
    rw [← h]
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx ↦ ?_
    have hx' : 0 < x := hε.trans hx
    rw [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, Real.rpow_two,
      smul_eq_mul]
    simp only [g, Real.norm_of_nonneg hx'.le]
    field_simp
  have hzero : gaussianSchwartzProfile 0 = 1 := by simp
  unfold realLogCutoff
  simp_rw [hg]
  rw [integral_complex_ofReal, hL,
    setIntegral_union hdis measurableSet_Iic (hi.mono_set subset_union_left)
      (hi.mono_set subset_union_right), hneg, hsub, hzero, Complex.real_smul, mul_one,
    ← Complex.ofReal_add, Real.log_pow]
  norm_num
  ring

private theorem gaussianLog_remainder :
    (∫ x : ℝ, realLogCutoffRemainder gaussianSchwartzProfile x) = (-γ : ℝ) := by
  have hs : Tendsto (fun ε : ℝ ↦ ε ^ (2 : ℕ)) (𝓝[>] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, (show ∀ᶠ ε : ℝ in 𝓝[>] 0, ε ∈ Ioi 0 from self_mem_nhdsWithin).mono
      (fun ε hε ↦ mem_Ioi.mpr (pow_pos (mem_Ioi.mp hε) 2))⟩
    have hc : ContinuousAt (fun ε : ℝ ↦ ε ^ (2 : ℕ)) 0 := (continuous_id.pow 2).continuousAt
    simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using
      hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  have h := Complex.continuous_ofReal.continuousAt.tendsto.comp
    (exponentialLog_cutoff_tendsto.comp hs)
  apply tendsto_nhds_unique (realLogCutoff_tendsto gaussianSchwartzProfile)
  apply h.congr'
  filter_upwards [show ∀ᶠ ε : ℝ in 𝓝[>] 0, ε ∈ Ioi 0 from self_mem_nhdsWithin] with ε hε
  exact (gaussianLog_cutoff_eq hε).symm

theorem realGaussianPi_logRemainder :
    (∫ x : ℝ, realLogCutoffRemainder realGaussianPi x) = (-γ - Real.log π : ℝ) := by
  unfold realGaussianPi
  rw [realLogCutoffRemainder_dilate, gaussianLog_remainder]
  have hzero : gaussianSchwartzProfile 0 = 1 := by simp
  rw [hzero, Complex.real_smul, mul_one, Real.log_inv, Real.log_sqrt Real.pi_pos.le,
    ← Complex.ofReal_add]
  congr 1
  ring

/-- The constant at zero in a real logarithmic Fourier formula with unit cutoff. -/
theorem realLogFourier_cutoff_constant_unique (A B : ℂ)
    (h : ∀ f : 𝓢(ℝ, ℂ), realLogFourierPairing f =
      A * (∫ x : ℝ, realLogCutoffRemainder f x) + B * f 0) :
    B = (-(γ + Real.log (2 * π)) : ℝ) := by
  have hA := realLogFourier_cutoff_coefficient_unique A B h
  have he := h realGaussianPi
  have hzero : realGaussianPi 0 = 1 := by rw [realGaussianPi_apply]; simp
  rw [realLogFourierPairing_gaussianPi, hA, realGaussianPi_logRemainder, hzero, mul_one] at he
  have hfour : Real.log (4 * π) = 2 * Real.log 2 + Real.log π := by
    rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) Real.pi_pos.ne',
      show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    norm_num
  rw [hfour] at he
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) Real.pi_pos.ne']
  push_cast at he ⊢
  linear_combination -he

end
end Masullo
