import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.Prod

open Complex Filter MeasureTheory Metric Set
open scoped Topology

namespace Masullo

noncomputable section

private theorem integrableOn_linear_exp_neg {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun v : ℝ ↦ v * Real.exp (-(a * v))) (Ioi 0) := by
  have hdom := (integrableOn_exp_mul_Ioi (a := -(a/2)) (by linarith) 0).const_mul (2/a)
  refine hdom.mono' (by fun_prop) ?_
  filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioi : MeasurableSet (Ioi (0 : ℝ)))] with v hv
  have hv₀ : 0 ≤ v := hv.le
  have hvle : v ≤ (2/a) * Real.exp ((a/2) * v) := by
    have hh := Real.add_one_le_exp ((a/2) * v)
    rw [div_mul_eq_mul_div]
    exact (le_div_iff₀ ha).mpr (by linarith)
  rw [Real.norm_of_nonneg (by positivity)]
  calc
    _ ≤ ((2/a) * Real.exp ((a/2) * v)) * Real.exp (-(a*v)) :=
      mul_le_mul_of_nonneg_right hvle (Real.exp_pos _).le
    _ = _ := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring

private theorem integral_linear_exp_neg {a : ℝ} (ha : 0 < a) :
    (∫ v : ℝ in Ioi 0, v * Real.exp (-(a*v))) = a⁻¹ ^ 2 := by
  have hΓ : Real.Gamma (2 : ℝ) = 1 := by
    norm_num [show (2 : ℝ) = (1 : ℕ) + 1 by norm_num, Real.Gamma_nat_eq_factorial]
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (r := a) (by norm_num) ha
  simpa only [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, Real.rpow_two,
    hΓ, mul_one, one_div] using h

/-- Continuation of the inverse-square Laplace tail away from the real
spectral axis. -/
def oscillatoryLaplaceTail (a : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (z * (a : ℂ)) * ∫ v : ℝ in Ioi 0,
    ((v * Real.exp (-(a*v)) : ℝ) : ℂ) * ((v : ℂ) - z)⁻¹

theorem analyticAt_oscillatoryLaplaceTail {a : ℝ} (ha : 0 < a) {z : ℂ} (hz : z.im ≠ 0) :
    AnalyticAt ℂ (oscillatoryLaplaceTail a) z := by
  apply AnalyticAt.fun_mul (by fun_prop)
  let K (w : ℂ) (v : ℝ) := ((v * Real.exp (-(a*v)) : ℝ) : ℂ) * ((v : ℂ) - w)⁻¹
  let K' (w : ℂ) (v : ℝ) := ((v * Real.exp (-(a*v)) : ℝ) : ℂ) * (((v : ℂ) - w) ^ 2)⁻¹
  change AnalyticAt ℂ (fun w ↦ ∫ v : ℝ in Ioi 0, K w v) z
  have ho : IsOpen {w : ℂ | w.im ≠ 0} := isOpen_ne_fun Complex.continuous_im continuous_const
  apply DifferentiableOn.analyticOnNhd _ ho z hz
  intro w hw
  have hwi : w.im ≠ 0 := hw
  let r := |w.im| / 2
  have hr : 0 < r := half_pos (abs_pos.mpr hwi)
  have hdist (u : ℂ) (hu : u ∈ ball w r) (v : ℝ) : r ≤ ‖(v : ℂ) - u‖ := by
    have him : |u.im - w.im| ≤ ‖u-w‖ := by simpa [Complex.sub_im] using Complex.abs_im_le_norm (u-w)
    have huv : ‖u-w‖ < r := by simpa [dist_eq_norm] using hu
    have h := abs_sub_abs_le_abs_sub w.im u.im
    rw [abs_sub_comm] at h
    have h' : r ≤ |u.im| := by dsimp [r] at *; linarith
    exact h'.trans (by simpa [Complex.sub_im] using Complex.abs_im_le_norm ((v : ℂ)-u))
  have hmeas (u : ℂ) : AEStronglyMeasurable (K u) (volume.restrict (Ioi 0)) := by
    apply Measurable.aestronglyMeasurable
    dsimp [K]; fun_prop
  have hmeas' (u : ℂ) : AEStronglyMeasurable (K' u) (volume.restrict (Ioi 0)) := by
    apply Measurable.aestronglyMeasurable
    dsimp [K']; fun_prop
  have hI : IntegrableOn (K w) (Ioi 0) := by
    refine ((integrableOn_linear_exp_neg ha).mul_const r⁻¹).mono' (hmeas w) ?_
    filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioi : MeasurableSet (Ioi (0 : ℝ)))] with v hv
    have hv' : 0 ≤ v := hv.le
    dsimp only [K]
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity), norm_inv]
    exact mul_le_mul_of_nonneg_left (inv_anti₀ hr (hdist w (mem_ball_self hr) v)) (by positivity)
  have hbound : ∀ᵐ v ∂volume.restrict (Ioi 0), ∀ u ∈ ball w r,
      ‖K' u v‖ ≤ (v * Real.exp (-(a*v))) * (r ^ 2)⁻¹ := by
    filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioi : MeasurableSet (Ioi (0 : ℝ)))] with v hv u hu
    have hv' : 0 ≤ v := hv.le
    dsimp only [K']
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity), norm_inv, norm_pow]
    exact mul_le_mul_of_nonneg_left (inv_anti₀ (pow_pos hr _) (pow_le_pow_left₀ hr.le (hdist u hu v) _))
      (by positivity)
  have hder (v : ℝ) (u : ℂ) (hu : u ∈ ball w r) : HasDerivAt (K · v) (K' u v) u := by
    have hu₀ : (v : ℂ) - u ≠ 0 := norm_pos_iff.mp (hr.trans_le (hdist u hu v))
    have hd := (((hasDerivAt_id' u).const_sub (v : ℂ)).inv hu₀).const_mul
      (((v * Real.exp (-(a*v)) : ℝ)) : ℂ)
    simpa [K, K', one_div] using hd
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (ball_mem_nhds w hr)
    (Eventually.of_forall hmeas) hI (hmeas' w) hbound
    ((integrableOn_linear_exp_neg ha).mul_const (r ^ 2)⁻¹)
    (Eventually.of_forall hder)).2.differentiableAt.differentiableWithinAt

/-- Swapping the absolutely integrable Laplace integrals identifies the
continuation with the inverse-square tail on the closed left half-plane. -/
theorem oscillatoryLaplaceTail_eq_integral {a : ℝ} (ha : 0 < a) {z : ℂ} (hz : z.re ≤ 0) :
    oscillatoryLaplaceTail a z = ∫ u : ℝ in Ioi a, Complex.exp (z * u) / (u : ℂ) ^ 2 := by
  let μ := volume.restrict (Ioi a)
  let ν := volume.restrict (Ioi (0 : ℝ))
  let f (u v : ℝ) := (v : ℂ) * Complex.exp ((z - (v : ℂ)) * (u : ℂ))
  have hf : Continuous (Function.uncurry f) := by dsimp [Function.uncurry, f]; fun_prop
  have hfactor (u v : ℝ) : f u v = Complex.exp (z * u) * ((v * Real.exp (-(u*v)) : ℝ) : ℂ) := by
    dsimp only [f]
    rw [sub_mul, sub_eq_add_neg, Complex.exp_add, Complex.ofReal_mul, Complex.ofReal_exp]
    push_cast
    ring_nf
  have hrow (u : ℝ) (hu : u ∈ Ioi a) : Integrable (f u) ν := by
    rw [funext (hfactor u)]
    exact ((integrableOn_linear_exp_neg (ha.trans hu)).ofReal (𝕜 := ℂ)).const_mul _
  have hnrow (u : ℝ) (hu : u ∈ Ioi a) :
      (∫ v, ‖f u v‖ ∂ν) = Real.exp (z.re * u) * u⁻¹ ^ 2 := by
    calc
      _ = ∫ v, Real.exp (z.re * u) * (v * Real.exp (-(u*v))) ∂ν := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioi : MeasurableSet (Ioi (0 : ℝ)))] with v hv
        have hv' : 0 ≤ v := hv.le
        rw [hfactor, norm_mul, norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          mul_zero, sub_zero, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      _ = _ := by rw [integral_const_mul, integral_linear_exp_neg (ha.trans hu)]
  have hdom : Integrable (fun u : ℝ ↦ u⁻¹ ^ 2) μ := by
    refine (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) ha).congr_fun ?_ measurableSet_Ioi
    intro u hu
    change u ^ (-2 : ℝ) = u⁻¹ ^ 2
    rw [Real.rpow_neg (ha.trans hu).le, Real.rpow_two, inv_pow]
  have hprod : Integrable (Function.uncurry f) (μ.prod ν) := by
    refine (integrable_prod_iff hf.aestronglyMeasurable).mpr ⟨?_, ?_⟩
    · filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioi : MeasurableSet (Ioi a))] with u hu
      exact hrow u hu
    · refine hdom.mono' (hf.aestronglyMeasurable.norm.integral_prod_right') ?_
      filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioi : MeasurableSet (Ioi a))] with u hu
      change ‖∫ v, ‖f u v‖ ∂ν‖ ≤ _
      rw [hnrow u hu, Real.norm_of_nonneg (by positivity)]
      apply mul_le_of_le_one_left (by positivity)
      exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg hz (ha.trans hu).le)
  have hrowEq (u : ℝ) (hu : u ∈ Ioi a) :
      (∫ v, f u v ∂ν) = Complex.exp (z*u) / (u : ℂ)^2 := by
    simp_rw [hfactor u]
    rw [integral_const_mul, show (∫ v : ℝ, ((v * Real.exp (-(u*v)) : ℝ) : ℂ) ∂ν) =
      (((∫ v : ℝ, v * Real.exp (-(u*v)) ∂ν) : ℝ) : ℂ) from integral_ofReal (𝕜 := ℂ),
      integral_linear_exp_neg (ha.trans hu),
      Complex.ofReal_pow, Complex.ofReal_inv, inv_pow, div_eq_mul_inv]
  have hcolEq (v : ℝ) (hv : v ∈ Ioi 0) :
      (∫ u, f u v ∂μ) =
        Complex.exp (z*a) * (((v * Real.exp (-(a*v)) : ℝ) : ℂ) * ((v : ℂ)-z)⁻¹) := by
    have hv' : 0 < v := hv
    have hneg : (z - (v : ℂ)).re < 0 := by simp only [Complex.sub_re, Complex.ofReal_re]; linarith
    change (∫ u : ℝ in Ioi a, (v : ℂ) * Complex.exp ((z-(v : ℂ)) * u)) = _
    rw [integral_const_mul, integral_exp_mul_complex_Ioi hneg, sub_mul, sub_eq_add_neg, Complex.exp_add]
    push_cast
    rw [show z - (v : ℂ) = -((v : ℂ)-z) by ring, div_neg, neg_div, neg_neg]
    rw [mul_comm (v : ℂ) (a : ℂ), div_eq_mul_inv]
    ring
  calc
    _ = ∫ v, ∫ u, f u v ∂μ ∂ν := by
      rw [oscillatoryLaplaceTail, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioi : MeasurableSet (Ioi (0 : ℝ)))] with v hv
      exact (hcolEq v hv).symm
    _ = ∫ u, ∫ v, f u v ∂ν ∂μ := (integral_integral_swap hprod).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioi : MeasurableSet (Ioi a))] with u hu
      exact hrowEq u hu

theorem continuousOn_exp_div_sq_Icc (z : ℂ) {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (fun u : ℝ ↦ Complex.exp (z * u) / (u : ℂ)^2) (Icc a b) := by
  apply ContinuousOn.div (by fun_prop) (by fun_prop)
  intro u hu
  exact pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (ha.trans_le hu.1).ne')

/-- The integral over a positive finite interval is entire in the
Laplace parameter. -/
theorem analyticAt_integral_exp_div_sq_interval {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (z : ℂ) :
    AnalyticAt ℂ (fun w ↦ ∫ u : ℝ in a..b, Complex.exp (w*u) / (u : ℂ)^2) z := by
  simp_rw [intervalIntegral.integral_of_le hab]
  apply Differentiable.analyticAt
  intro w
  let F (y : ℂ) (u : ℝ) := Complex.exp (y*u) / (u : ℂ)^2
  let F' (y : ℂ) (u : ℝ) := (Complex.exp (y*u) * (u : ℂ)) / (u : ℂ)^2
  let S := closedBall w 1 ×ˢ Icc a b
  have hs : IsCompact S := (isCompact_closedBall w 1).prod isCompact_Icc
  have hCont : ContinuousOn (Function.uncurry F') S := by
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro p hp
    exact pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (ha.trans_le hp.2.1).ne')
  obtain ⟨C, hC⟩ := hs.exists_bound_of_continuousOn hCont
  let μ := volume.restrict (Ioc a b)
  have hm (y : ℂ) : AEStronglyMeasurable (F y) μ := by
    apply Measurable.aestronglyMeasurable
    dsimp [F]; fun_prop
  have hm' (y : ℂ) : AEStronglyMeasurable (F' y) μ := by
    apply Measurable.aestronglyMeasurable
    dsimp [F']; fun_prop
  have hi : Integrable (F w) μ :=
    ((continuousOn_exp_div_sq_Icc w ha).integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
  have hbound : ∀ᵐ u ∂μ, ∀ y ∈ ball w 1, ‖F' y u‖ ≤ C := by
    filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioc : MeasurableSet (Ioc a b))] with u hu y hy
    exact hC (y,u) ⟨ball_subset_closedBall hy, Ioc_subset_Icc_self hu⟩
  have hder : ∀ᵐ u ∂μ, ∀ y ∈ ball w 1, HasDerivAt (F · u) (F' y u) y := by
    filter_upwards with u y _
    have he := (((hasDerivAt_id' y).mul_const (u : ℂ)).cexp).div_const ((u : ℂ)^2)
    simpa [F, F'] using he
  have hCint : Integrable (fun _ : ℝ ↦ C) μ :=
    integrableOn_const (by simp)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (ball_mem_nhds _ one_pos)
    (Eventually.of_forall hm) hi (hm' w) hbound hCint hder).2.differentiableAt

end

end Masullo
