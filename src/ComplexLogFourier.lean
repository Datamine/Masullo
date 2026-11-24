import ArchimedeanLogGaussianKernel
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

open Filter Function MeasureTheory Set Topology
open scoped FourierTransform SchwartzMap

namespace Masullo

noncomputable section

local notation "π" => Real.pi
local notation "Tests" => 𝓢(ℂ, ℂ)

private theorem ae_complex_ne_zero : ∀ᵐ z : ℂ ∂volume, z ≠ 0 := ae_iff.mpr (by
  simpa only [not_not, ofPred_eq_eq_singleton] using measure_singleton (0 : ℂ) (μ := volume))

theorem integral_complex_radial (g : ℝ → ℝ) :
    (∫ z : ℂ, g ‖z‖) = 2 * π * ∫ r in Ioi (0 : ℝ), r * g r := by
  have hV : (volume : Measure ℂ).real (Metric.ball 0 1) = π := by
    rw [measureReal_def, Complex.volume_ball]
    simp
  simpa only [Complex.finrank_real_complex, hV, show (2 : ℕ) - 1 = 1 by norm_num,
    pow_one, nsmul_eq_mul, Nat.cast_ofNat, smul_eq_mul, mul_assoc] using
      integral_fun_norm_addHaar (volume : Measure ℂ) g

/-- The logarithm is integrable against each complex Schwartz test. -/
theorem complexLogSchwartz_integrable (f : Tests) :
    Integrable (fun z : ℂ ↦ Real.log ‖z‖ • f z) := by
  let S := Metric.ball (0 : ℂ) 1
  have hm : AEStronglyMeasurable (fun z : ℂ ↦ Real.log ‖z‖ • f z) :=
    ((Real.measurable_log.comp continuous_norm.measurable).smul f.continuous.measurable).aestronglyMeasurable
  have hlog : IntegrableOn (fun z : ℂ ↦ Real.log ‖z‖) S := by
    rw [integrableOn_fun_norm_addHaar (volume : Measure ℂ) (f := Real.log), Complex.finrank_real_complex]
    simpa only [show (2 : ℕ) - 1 = 1 by norm_num, pow_one, smul_eq_mul] using
      (Real.continuous_mul_log.continuousOn.integrableOn_Icc (a := 0) (b := 1)).mono_set Ioo_subset_Icc_self
  have hin : IntegrableOn (fun z : ℂ ↦ Real.log ‖z‖ • f z) S := by
    refine (hlog.norm.const_mul (SchwartzMap.seminorm ℂ 0 0 f)).mono'
      (hm.mono_measure Measure.restrict_le_self) (.of_forall fun z ↦ ?_)
    rw [norm_smul, mul_comm (SchwartzMap.seminorm ℂ 0 0 f)]
    exact mul_le_mul_of_nonneg_left (f.norm_le_seminorm ℂ z) (norm_nonneg _)
  have hout : IntegrableOn (fun z : ℂ ↦ Real.log ‖z‖ • f z) Sᶜ := by
    refine ((f.integrable_pow_mul volume 1).norm.integrableOn).mono'
      (hm.mono_measure Measure.restrict_le_self) ?_
    refine (ae_restrict_mem measurableSet_ball.compl).mono fun z hz ↦ ?_
    have hz' : 1 ≤ ‖z‖ := le_of_not_gt fun h ↦ hz (by simpa only [Metric.mem_ball, dist_zero_right] using h)
    rw [norm_smul, Real.norm_of_nonneg (Real.log_nonneg hz'), norm_mul, norm_norm, pow_one,
      Real.norm_of_nonneg (norm_nonneg z)]
    exact mul_le_mul_of_nonneg_right
      ((Real.log_le_sub_one_of_pos (zero_lt_one.trans_le hz')).trans (sub_le_self _ zero_le_one))
      (norm_nonneg _)
  simpa only [union_compl_self, integrableOn_univ] using hin.union hout

/-- The finite-part integrand for the squared-modulus cutoff in complex Lebesgue measure. -/
def complexLogCutoffRemainder (f : Tests) (z : ℂ) : ℂ :=
  (‖z‖ ^ 2)⁻¹ • (f z - {w : ℂ | ‖w‖ ≤ 1}.indicator (fun _ ↦ f 0) z)

theorem complexLogCutoffRemainder_integrable (f : Tests) :
    Integrable (complexLogCutoffRemainder f) := by
  let S := Metric.closedBall (0 : ℂ) 1
  let M := SchwartzMap.seminorm ℂ 0 1 f
  have hM : 0 ≤ M := apply_nonneg _ _
  let m := Real.toNNReal M
  have hM' : (m : ℝ) = M := Real.coe_toNNReal _ hM
  have hl : LipschitzWith m (f : ℂ → ℂ) := by
    apply lipschitzWith_of_nnnorm_fderiv_le (𝕜 := ℝ) f.differentiable
    intro z
    rw [← NNReal.coe_le_coe, coe_nnnorm, hM', ← norm_iteratedFDeriv_one]
    exact f.norm_iteratedFDeriv_le_seminorm ℂ 1 z
  have hS : S = {z : ℂ | ‖z‖ ≤ 1} := by ext; simp [S, Metric.mem_closedBall, dist_zero_right]
  have hSm : MeasurableSet {z : ℂ | ‖z‖ ≤ 1} := hS ▸ measurableSet_closedBall
  have hm : Measurable (complexLogCutoffRemainder f) :=
    (continuous_norm.measurable.pow_const 2).inv.smul
      (f.continuous.measurable.sub (measurable_const.indicator hSm))
  have hInv : IntegrableOn (fun z : ℂ ↦ ‖z‖⁻¹) S := by
    have hBall : IntegrableOn (fun z : ℂ ↦ ‖z‖⁻¹) (Metric.ball 0 2) := by
      rw [integrableOn_fun_norm_addHaar (volume : Measure ℂ) (f := fun r : ℝ ↦ r⁻¹),
        Complex.finrank_real_complex]
      refine (integrableOn_const (C := (1 : ℝ)) measure_Ioo_lt_top.ne).congr
        ((ae_restrict_mem measurableSet_Ioo).mono fun r hr ↦ ?_)
      have hp : 0 < r := hr.1
      change 1 = r ^ 1 • r⁻¹
      rw [pow_one, smul_eq_mul, mul_inv_cancel₀ hp.ne']
    exact hBall.mono_set fun z hz ↦ by
      rw [Metric.mem_ball, dist_zero_right]
      have hz' : z ∈ {z : ℂ | ‖z‖ ≤ 1} := hS ▸ hz
      exact hz'.trans_lt one_lt_two
  have hin : IntegrableOn (complexLogCutoffRemainder f) S := by
    refine (hInv.const_mul M).mono' hm.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_closedBall,
      ae_complex_ne_zero.filter_mono (Measure.absolutelyContinuous_of_le Measure.restrict_le_self).ae_le] with z hz hZ
    have hz' : z ∈ {w : ℂ | ‖w‖ ≤ 1} := hS ▸ hz
    have hp : 0 < ‖z‖ := norm_pos_iff.mpr hZ
    rw [complexLogCutoffRemainder, indicator_of_mem hz', norm_smul,
      Real.norm_of_nonneg (inv_nonneg.mpr (sq_nonneg ‖z‖))]
    have hd := hl.dist_le_mul z 0
    rw [dist_eq_norm, dist_zero_right, hM'] at hd
    apply (mul_le_mul_of_nonneg_left hd (inv_nonneg.mpr (sq_nonneg ‖z‖))).trans_eq
    field_simp
  have hout : IntegrableOn (complexLogCutoffRemainder f) Sᶜ := by
    refine f.integrable.norm.integrableOn.mono' hm.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_closedBall.compl] with z hz
    have hz' : z ∉ {w : ℂ | ‖w‖ ≤ 1} := hS ▸ hz
    rw [complexLogCutoffRemainder, indicator_of_notMem hz', sub_zero, norm_smul,
      Real.norm_of_nonneg (inv_nonneg.mpr (sq_nonneg ‖z‖))]
    exact mul_le_of_le_one_left (norm_nonneg _)
      (inv_le_one_of_one_le₀ (one_le_pow₀ (le_of_lt (lt_of_not_ge hz'))))
  simpa only [union_compl_self, integrableOn_univ] using hin.union hout

private def complexFourierGaussianWeight (t : ℝ) (z : ℂ) : ℝ :=
  (π / t) * Real.exp (-((π * ‖z‖) ^ 2 / t))

private theorem integral_complexFourierGaussianWeight {z : ℂ} (hz : z ≠ 0) :
    (∫ t in Ioi 0, t⁻¹ * complexFourierGaussianWeight t z) = (π * ‖z‖ ^ 2)⁻¹ := by
  let a := (π * ‖z‖) ^ 2
  have ha : 0 < a := sq_pos_of_ne_zero (mul_ne_zero Real.pi_ne_zero (norm_ne_zero_iff.mpr hz))
  have hsub := integral_comp_rpow_Ioi (fun t : ℝ ↦ Real.exp (-(a * t))) (p := -1) (by norm_num)
  have he : (∫ t in Ioi 0, t⁻¹ * complexFourierGaussianWeight t z) =
      π * ∫ t in Ioi (0 : ℝ), Real.exp (-(a * t)) := by
    rw [← hsub, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ ?_
    have hp : 0 < t := ht
    simp only [complexFourierGaussianWeight, abs_neg, abs_one, one_mul, smul_eq_mul,
      show (-1 : ℝ) - 1 = -2 by norm_num, Real.rpow_neg hp.le, Real.rpow_two, Real.rpow_one,
      div_eq_mul_inv]
    change t⁻¹ * (π * t⁻¹ * Real.exp (-(a * t⁻¹))) =
      π * ((t ^ 2)⁻¹ * Real.exp (-(a * t⁻¹)))
    rw [← inv_pow]
    ring
  rw [he]
  have hE := integral_exp_mul_Ioi (a := -a) (neg_neg_of_pos ha) 0
  simp only [← neg_mul]
  rw [hE]
  simp only [mul_zero, Real.exp_zero]
  dsimp [a]
  field_simp [Real.pi_ne_zero, norm_ne_zero_iff.mpr hz]

private theorem complexFourierGaussian_swap (f : Tests) {t : ℝ} (ht : 0 < t) :
    (∫ z : ℂ, Real.exp (-(t * ‖z‖ ^ 2)) • (𝓕 f) z) =
      ∫ z : ℂ, complexFourierGaussianWeight t z • f z := by
  let g : ℂ → ℂ := fun z ↦ Complex.exp (-(t : ℂ) * (‖z‖ : ℂ) ^ 2)
  have ht' : 0 < (t : ℂ).re := by simpa only [Complex.ofReal_re] using ht
  have hg : Integrable g := by
    simpa only [g, mul_zero, zero_mul, add_zero] using
      GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := ℂ) ht' 0 0
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ ℂ)
    Real.continuous_fourierChar continuous_inner (f.integrable (μ := volume)) hg
  have hSwap : (∫ z : ℂ, (𝓕 f) z * g z) = ∫ z : ℂ, f z * 𝓕 g z := by
    simpa using! h
  have hg0 (z : ℂ) : g z = (Real.exp (-(t * ‖z‖ ^ 2)) : ℂ) := by
    rw [Complex.ofReal_exp]
    push_cast
    simp only [g, neg_mul]
  have hgF (z : ℂ) : 𝓕 g z = (complexFourierGaussianWeight t z : ℂ) := by
    change 𝓕 (fun z : ℂ ↦ Complex.exp (-(t : ℂ) * (‖z‖ : ℂ) ^ 2)) z = _
    rw [fourier_gaussian_innerProductSpace ht', Complex.finrank_real_complex,
      show ((2 : ℕ) : ℂ) / 2 = 1 by norm_num, Complex.cpow_one]
    simp only [complexFourierGaussianWeight, Complex.ofReal_mul, Complex.ofReal_div,
      Complex.ofReal_exp, Complex.ofReal_neg, Complex.ofReal_pow]
    congr 2
    ring
  simpa only [hg0, hgF, Complex.real_smul, mul_comm] using hSwap

/-- The plane Fourier pairing uses the Euclidean character and Lebesgue measure. -/
def complexEuclideanLogFourierPairing (f : Tests) : ℂ :=
  ∫ z : ℂ, (2 * Real.log ‖z‖) • (𝓕 f) z

private theorem integral_complexSchwartz_fourier (f : Tests) : (∫ z : ℂ, (𝓕 f) z) = f 0 := by
  have h := congrArg (fun g : Tests ↦ g 0)
    (FourierTransform.fourierInv_fourier_eq (F := Tests) f)
  change (𝓕⁻ (𝓕 f)) 0 = f 0 at h
  rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq] at h
  simpa using h

theorem complexLogCutoffRemainder_of_zero (f : Tests) (hf : f 0 = 0) (z : ℂ) :
    complexLogCutoffRemainder f z = (‖z‖ ^ 2)⁻¹ • f z := by
  simp [complexLogCutoffRemainder, hf]

private theorem integral_complexFourierGaussian_smul (f : Tests) (hf : f 0 = 0) :
    (∫ t in Ioi (0 : ℝ), t⁻¹ • ∫ z : ℂ, complexFourierGaussianWeight t z • f z) =
      π⁻¹ • ∫ z : ℂ, (‖z‖ ^ 2)⁻¹ • f z := by
  let K (z : ℂ) (t : ℝ) := t⁻¹ * complexFourierGaussianWeight t z
  have hm : Measurable (Function.uncurry K) := by
    have ht : Measurable (Prod.snd : ℂ × ℝ → ℝ) := measurable_snd
    have hx : Measurable (fun p : ℂ × ℝ ↦ ‖p.1‖) := continuous_norm.measurable.comp measurable_fst
    exact (ht.inv.mul ((measurable_const.div ht).mul (Real.measurable_exp.comp
      (((measurable_const.mul hx).pow_const 2).div ht).neg)))
  have hK (z t) (ht : t ∈ Ioi (0 : ℝ)) : 0 ≤ K z t :=
    mul_nonneg (inv_nonneg.mpr (mem_Ioi.mp ht).le)
      (mul_nonneg (div_nonneg Real.pi_pos.le (mem_Ioi.mp ht).le) (Real.exp_pos _).le)
  have hh : ∀ᵐ z : ℂ ∂volume, (∫ t in Ioi (0 : ℝ), K z t) = (π * ‖z‖ ^ 2)⁻¹ ∧
      0 < (π * ‖z‖ ^ 2)⁻¹ := ae_complex_ne_zero.mono fun z hz ↦
    ⟨integral_complexFourierGaussianWeight hz,
      inv_pos.mpr (mul_pos Real.pi_pos (sq_pos_of_pos (norm_pos_iff.mpr hz)))⟩
  have hfI : Integrable (fun z : ℂ ↦ (‖z‖ ^ 2)⁻¹ • f z) :=
    (complexLogCutoffRemainder_integrable f).congr (.of_forall (complexLogCutoffRemainder_of_zero f hf))
  have hi : Integrable (fun z : ℂ ↦ (π * ‖z‖ ^ 2)⁻¹ • f z) := by
    simp_rw [mul_inv, mul_smul]
    exact hfI.smul π⁻¹
  have h := integral_gaussianWeight_smul hm f.continuous.measurable hK hh hi
  simpa only [K, mul_inv, mul_smul, integral_smul] using h

/-- The Euclidean complex logarithmic pairing on tests with value zero at the origin. -/
theorem complexEuclideanLogFourierPairing_of_zero (f : Tests) (hf : f 0 = 0) :
    complexEuclideanLogFourierPairing f =
      -π⁻¹ • ∫ z : ℂ, complexLogCutoffRemainder f z := by
  let g := (𝓕 f : Tests)
  have hG : (∫ z : ℂ, g z) = 0 := (integral_complexSchwartz_fourier f).trans hf
  have hgI : Integrable (fun z : ℂ ↦ g z) := g.integrable
  have hF (t : ℝ) (ht : t ∈ Ioi (0 : ℝ)) :
      (∫ z : ℂ, gaussianLogKernel (‖z‖ ^ 2) t • g z) =
        -(t⁻¹ • ∫ z : ℂ, complexFourierGaussianWeight t z • f z) := by
    have hI : Integrable (fun z : ℂ ↦ Real.exp (-(t * ‖z‖ ^ 2)) • g z) := by
      refine hgI.norm.mono' (by fun_prop) (.of_forall fun z ↦ ?_)
      rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
      apply mul_le_of_le_one_left (norm_nonneg (g z))
      exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg (mem_Ioi.mp ht).le (sq_nonneg ‖z‖)))
    have h0 : (fun z : ℂ ↦ gaussianLogKernel (‖z‖ ^ 2) t • g z) = fun z : ℂ ↦ t⁻¹ •
        (Real.exp (-t) • g z - Real.exp (-(t * ‖z‖ ^ 2)) • g z) := by
      funext z
      rw [gaussianLogKernel, mul_smul, sub_smul, mul_comm (‖z‖ ^ 2) t]
    have hE : Integrable (fun z : ℂ ↦ Real.exp (-t) • g z) := hgI.smul (Real.exp (-t))
    rw [h0, integral_smul, integral_sub hE hI, integral_smul, hG, smul_zero,
      zero_sub, smul_neg, complexFourierGaussian_swap f (mem_Ioi.mp ht)]
  change (∫ z : ℂ, (2 * Real.log ‖z‖) • g z) = _
  simp_rw [mul_smul]
  rw [integral_smul, integral_log_norm_smul_eq_gaussian ae_complex_ne_zero g.continuous.measurable
    (complexLogSchwartz_integrable g), smul_smul, mul_inv_cancel₀ (by norm_num : (2 : ℝ) ≠ 0),
    one_smul, setIntegral_congr_fun measurableSet_Ioi hF, integral_neg,
    integral_complexFourierGaussian_smul f hf, ← neg_smul]
  simp_rw [complexLogCutoffRemainder_of_zero f hf]

/-- The complex Fourier transform for the standard trace character and twice plane measure. -/
def complexTraceFourier (f : Tests) (z : ℂ) : ℂ :=
  (2 : ℝ) • (𝓕 f) ((2 : ℝ) • Complex.conjLIE z)

theorem complexTraceFourier_eq_integral (f : Tests) (z : ℂ) :
    complexTraceFourier f z = (2 : ℝ) • ∫ w : ℂ,
      Complex.exp (↑(-2 * π * (2 * (w * z).re)) * Complex.I) • f w := by
  rw [complexTraceFourier, SchwartzMap.fourier_coe, Real.fourier_eq']
  congr 1
  refine integral_congr_ae (.of_forall fun w ↦ ?_)
  have h : inner ℝ w ((2 : ℝ) • Complex.conjLIE z) = 2 * (w * z).re := by
    rw [inner_smul_right, Complex.inner, Complex.conjLIE_apply, ← map_mul, Complex.conj_re,
      mul_comm z w]
  simp only [h]

/-- The standard complex logarithmic pairing, with normalized absolute value `‖z‖²`. -/
def complexTraceLogFourierPairing (f : Tests) : ℂ :=
  (2 : ℝ) • ∫ z : ℂ, (2 * Real.log ‖z‖) • complexTraceFourier f z

/-- The other Fourier sign gives the same pairing with the even logarithm. -/
theorem complexTraceLogFourierPairing_eq_positive (f : Tests) :
    complexTraceLogFourierPairing f = (2 : ℝ) • ∫ z : ℂ,
      (2 * Real.log ‖z‖) • ((2 : ℝ) • ∫ w : ℂ,
        Complex.exp (↑(2 * π * (2 * (w * z).re)) * Complex.I) • f w) := by
  let g (z : ℂ) := (2 * Real.log ‖z‖ : ℝ) • complexTraceFourier f z
  change (2 : ℝ) • (∫ z : ℂ, g z) = _
  rw [← integral_neg_eq_self g volume]
  congr 1
  refine integral_congr_ae (.of_forall fun z ↦ ?_)
  change (2 * Real.log ‖-z‖ : ℝ) • complexTraceFourier f (-z) = _
  simp only [norm_neg, complexTraceFourier_eq_integral, mul_neg, Complex.neg_re, neg_mul, neg_neg]

private theorem complexTraceLogFourierPairing_comparison (f : Tests) :
    Integrable (fun z : ℂ ↦ (2 * Real.log ‖z‖ : ℝ) • complexTraceFourier f z) ∧
      complexTraceLogFourierPairing f = complexEuclideanLogFourierPairing f -
        (2 * Real.log 2 : ℝ) • f 0 := by
  let g := (𝓕 f : Tests)
  let J (z : ℂ) := (2 * Real.log ‖(2 : ℝ)⁻¹ • z‖ : ℝ) • g z
  have hJcomp (z : ℂ) : (2 * Real.log ‖z‖ : ℝ) • g ((2 : ℝ) • Complex.conjLIE z) =
      J ((2 : ℝ) • Complex.conjLIE z) := by
    simp only [J, smul_smul, inv_mul_cancel₀ (by norm_num : (2 : ℝ) ≠ 0), one_smul,
      Complex.conjLIE.norm_map]
  have hcomp : (∫ z : ℂ, (2 * Real.log ‖z‖) • g ((2 : ℝ) • Complex.conjLIE z)) =
      (∫ z : ℂ, J ((2 : ℝ) • z)) := by
    have h := Complex.conjLIE.measurePreserving.integral_comp
      Complex.conjLIE.toHomeomorph.measurableEmbedding (fun z : ℂ ↦ J ((2 : ℝ) • z))
    rw [← h]
    exact integral_congr_ae (.of_forall hJcomp)
  have hJ : J =ᵐ[volume] fun z ↦ (2 * Real.log ‖z‖ : ℝ) • g z -
      (2 * Real.log 2 : ℝ) • g z := by
    refine ae_complex_ne_zero.mono fun z hz ↦ ?_
    change (2 * Real.log ‖(2 : ℝ)⁻¹ • z‖ : ℝ) • g z =
      (2 * Real.log ‖z‖ : ℝ) • g z - (2 * Real.log 2 : ℝ) • g z
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (by norm_num)),
      Real.log_mul (by norm_num) (norm_ne_zero_iff.mpr hz), Real.log_inv]
    rw [neg_add_eq_sub, mul_sub, sub_smul]
  have hI : Integrable (fun z : ℂ ↦ (2 * Real.log ‖z‖ : ℝ) • g z) := by
    simp_rw [mul_smul]
    exact (complexLogSchwartz_integrable g).smul (2 : ℝ)
  have hG : Integrable (fun z : ℂ ↦ (2 * Real.log 2 : ℝ) • g z) :=
    (g.integrable (μ := volume)).smul (2 * Real.log 2 : ℝ)
  have ho : (fun z : ℂ ↦ (2 * Real.log ‖z‖ : ℝ) • complexTraceFourier f z) =
      fun z : ℂ ↦ (2 : ℝ) • ((2 * Real.log ‖z‖ : ℝ) • g ((2 : ℝ) • Complex.conjLIE z)) := by
    funext z
    exact smul_comm _ _ _
  constructor
  · have hjI : Integrable J := (hI.sub hG).congr hJ.symm
    have hjS : Integrable (fun z : ℂ ↦ J ((2 : ℝ) • z)) :=
      (integrable_comp_smul_iff volume J (by norm_num : (2 : ℝ) ≠ 0)).mpr hjI
    have hjC := (Complex.conjLIE.measurePreserving.integrable_comp_emb
      Complex.conjLIE.toHomeomorph.measurableEmbedding).mpr hjS
    rw [ho]
    exact (hjC.smul (2 : ℝ)).congr (.of_forall fun z ↦ congrArg (fun a : ℂ ↦ (2 : ℝ) • a) (hJcomp z).symm)
  · rw [complexTraceLogFourierPairing, ho, integral_smul, hcomp,
      Measure.integral_comp_smul_of_nonneg volume _ 2 (hR := by norm_num),
      Complex.finrank_real_complex, smul_smul, smul_smul,
      show (2 : ℝ) * 2 * (2 ^ (2 : ℕ))⁻¹ = 1 by norm_num, one_smul,
      integral_congr_ae hJ, integral_sub hI hG, integral_smul]
    rw [show (∫ z : ℂ, g z) = f 0 from integral_complexSchwartz_fourier f]
    rfl

theorem complexTraceLogFourierPairing_integrable (f : Tests) :
    Integrable (fun z : ℂ ↦ (2 * Real.log ‖z‖ : ℝ) • complexTraceFourier f z) :=
  (complexTraceLogFourierPairing_comparison f).1

theorem complexTraceLogFourierPairing_eq_euclidean (f : Tests) :
    complexTraceLogFourierPairing f = complexEuclideanLogFourierPairing f -
      (2 * Real.log 2 : ℝ) • f 0 :=
  (complexTraceLogFourierPairing_comparison f).2

private theorem complexLogCutoff_shell {ε : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1) :
    (∫ z in {z : ℂ | ε ≤ ‖z‖ ^ 2 ∧ ‖z‖ ≤ 1}, (‖z‖ ^ 2)⁻¹) = -π * Real.log ε := by
  let A := {r : ℝ | ε ≤ r ^ 2 ∧ r ≤ 1}
  let g := A.indicator (fun r : ℝ ↦ (r ^ 2)⁻¹)
  have hA : MeasurableSet A :=
    (isClosed_le continuous_const (continuous_id.pow 2)).measurableSet.inter measurableSet_Iic
  change (∫ z in (fun w : ℂ ↦ ‖w‖) ⁻¹' A, (‖z‖ ^ 2)⁻¹) = _
  have hG : (∫ z in (fun w : ℂ ↦ ‖w‖) ⁻¹' A, (‖z‖ ^ 2)⁻¹) = ∫ z : ℂ, g ‖z‖ := by
    rw [← integral_indicator (hA.preimage continuous_norm.measurable)]
    refine integral_congr_ae (.of_forall fun z ↦ ?_)
    by_cases hz : ‖z‖ ∈ A <;> simp [g, hz]
  rw [hG, integral_complex_radial]
  have hp : 0 < √ε := Real.sqrt_pos.mpr hε
  have hp₁ : √ε ≤ 1 := (Real.sqrt_le_iff.mpr ⟨zero_le_one, by simpa using hε₁⟩)
  have hsplit : (∫ r in Ioi (0 : ℝ), r * g r) = ∫ r in Icc (√ε) 1, r⁻¹ := by
    have hh : (∫ r in Ioi (0 : ℝ), (Icc (√ε) 1).indicator (fun r : ℝ ↦ r⁻¹) r) =
        ∫ r in Icc (√ε) 1, r⁻¹ := by
      rw [integral_indicator measurableSet_Icc, Measure.restrict_restrict measurableSet_Icc,
        inter_eq_left.mpr (show Icc (√ε) 1 ⊆ Ioi 0 from fun r hr ↦ hp.trans_le hr.1)]
    rw [← hh]
    refine setIntegral_congr_fun measurableSet_Ioi fun r hr ↦ ?_
    have hr0 : 0 < r := hr
    have hmem : r ∈ A ↔ r ∈ Icc (√ε) 1 := by
      change (ε ≤ r ^ 2 ∧ r ≤ 1) ↔ √ε ≤ r ∧ r ≤ 1
      rw [Real.sqrt_le_iff]
      simp only [hr0.le, true_and]
    by_cases h : r ∈ A
    · rw [show g r = (r ^ 2)⁻¹ from indicator_of_mem h _, indicator_of_mem (hmem.mp h)]
      field_simp
    · rw [show g r = 0 from indicator_of_notMem h _, indicator_of_notMem (mt hmem.mpr h), mul_zero]
  rw [hsplit, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hp₁]
  rw [integral_inv]
  · rw [one_div, Real.log_inv, Real.log_sqrt hε.le]
    ring
  · rw [uIcc_of_le hp₁]
    exact fun h ↦ hp.not_ge h.1

/-- The manuscript's squared-modulus cutoff with twice plane measure. -/
def complexLogCutoff (f : Tests) (ε : ℝ) : ℂ :=
  (2 : ℝ) • ((∫ z in {z : ℂ | ε ≤ ‖z‖ ^ 2}, (‖z‖ ^ 2)⁻¹ • f z) +
    (π * Real.log ε : ℝ) • f 0)

private theorem complexLogCutoff_eq_remainder (f : Tests) {ε : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1) :
    complexLogCutoff f ε = (2 : ℝ) • ∫ z in {z : ℂ | ε ≤ ‖z‖ ^ 2}, complexLogCutoffRemainder f z := by
  let L := {z : ℂ | ε ≤ ‖z‖ ^ 2}
  let S := {z : ℂ | ‖z‖ ≤ 1}
  have hm : MeasurableSet L := (isClosed_le continuous_const (continuous_norm.pow 2)).measurableSet
  have hS : MeasurableSet S := (isClosed_le continuous_norm continuous_const).measurableSet
  let g (z : ℂ) := (‖z‖ ^ 2)⁻¹ • f z
  let h (z : ℂ) := (‖z‖ ^ 2)⁻¹ • S.indicator (fun _ ↦ f 0) z
  have hg : IntegrableOn g L := by
    refine ((f.integrable (μ := volume)).norm.const_mul ε⁻¹).integrableOn.mono'
      ((continuous_norm.measurable.pow_const 2).inv.smul f.continuous.measurable).aestronglyMeasurable ?_
    refine (ae_restrict_mem hm).mono fun z hz ↦ ?_
    change ‖(‖z‖ ^ 2)⁻¹ • f z‖ ≤ ε⁻¹ * ‖f z‖
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_right (inv_anti₀ hε hz) (norm_nonneg _)
  have hd (z : ℂ) : complexLogCutoffRemainder f z = g z - h z := smul_sub ..
  have hh : IntegrableOn h L := by
    refine (hg.sub (complexLogCutoffRemainder_integrable f).integrableOn).congr (.of_forall fun z ↦ ?_)
    change g z - complexLogCutoffRemainder f z = h z
    rw [hd, sub_sub_cancel]
  have he : (∫ z in L, h z) = (-π * Real.log ε : ℝ) • f 0 := by
    calc
      _ = ∫ z in L ∩ S, (‖z‖ ^ 2)⁻¹ • f 0 := by
        change (∫ z in L, (‖z‖ ^ 2)⁻¹ • S.indicator (fun _ ↦ f 0) z) = _
        simp_rw [← indicator_smul, integral_indicator hS]
        rw [Measure.restrict_restrict hS, inter_comm]
      _ = _ := by
        rw [integral_smul_const]
        exact congrArg (fun r : ℝ ↦ r • f 0) (complexLogCutoff_shell hε hε₁)
  change (2 : ℝ) • ((∫ z in L, g z) + (π * Real.log ε) • f 0) = _
  rw [integral_congr_ae (.of_forall hd), integral_sub hg hh, he, neg_mul, neg_smul, sub_neg_eq_add]

/-- The complex squared-modulus cutoff converges on the full Schwartz space. -/
theorem complexLogCutoff_tendsto (f : Tests) :
    Tendsto (complexLogCutoff f) (𝓝[>] 0)
      (𝓝 ((2 : ℝ) • ∫ z : ℂ, complexLogCutoffRemainder f z)) := by
  let g := complexLogCutoffRemainder f
  let L (ε : ℝ) := {z : ℂ | ε ≤ ‖z‖ ^ 2}
  have hm (ε : ℝ) : MeasurableSet (L ε) :=
    (isClosed_le continuous_const (continuous_norm.pow 2)).measurableSet
  have hi : Integrable g := complexLogCutoffRemainder_integrable f
  have ht : Tendsto (fun ε : ℝ ↦ ∫ z : ℂ, (L ε).indicator g z) (𝓝[>] 0) (𝓝 (∫ z : ℂ, g z)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun z : ℂ ↦ ‖g z‖)
      (.of_forall fun ε ↦ hi.aestronglyMeasurable.indicator (hm ε))
      (.of_forall fun ε ↦ .of_forall fun z ↦ ?_) hi.norm ?_
    · by_cases hz : z ∈ L ε
      · rw [indicator_of_mem hz]
      · rw [indicator_of_notMem hz, norm_zero]
        exact norm_nonneg _
    · filter_upwards [ae_complex_ne_zero] with z hz
      refine tendsto_const_nhds.congr' ?_
      have he := (show ∀ᶠ ε : ℝ in 𝓝 0, ε < ‖z‖ ^ 2 from
        Iio_mem_nhds (sq_pos_of_pos (norm_pos_iff.mpr hz))).filter_mono
        (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
      filter_upwards [he] with ε hε
      exact (indicator_of_mem (show z ∈ L ε from le_of_lt hε) g).symm
  apply (ht.const_smul (2 : ℝ)).congr'
  have hlt : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε < 1 :=
    (show ∀ᶠ ε : ℝ in 𝓝 0, ε < 1 from Iio_mem_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hlt] with ε hε hε₁
  rw [integral_indicator (hm ε), complexLogCutoff_eq_remainder f hε hε₁.le]

end
end Masullo
