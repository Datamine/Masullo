import ScalarFractionalBoundary
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Covering.DensityTheorem
import Mathlib.MeasureTheory.Integral.Layercake

open Filter Function MeasureTheory Set Topology
open scoped ENNReal FourierTransform RealInnerProductSpace

namespace Masullo

noncomputable section

/-- Poisson kernel in the Fourier normalization with imaginary height
(2πy). Its multiplier on the physical line is (e^{-t|x|}). -/
def mellinPoissonKernel (t y : ℝ) : ℝ :=
  2 * t / (t ^ 2 + (2 * Real.pi * y) ^ 2)

private theorem integrable_exp_neg_abs_mul {t : ℝ} (ht : 0 < t) :
    Integrable (fun x : ℝ => Real.exp (-t * |x|)) := by
  have h₁ := integrableOn_exp_mul_Iic (a := t) ht 0
  have h₂ := integrableOn_exp_mul_Ioi (a := -t) (neg_neg_of_pos ht) 0
  have hleft : IntegrableOn (fun x : ℝ => Real.exp (-t * |x|)) (Iic 0) :=
    h₁.congr_fun (fun x hx => by simp [abs_of_nonpos (show x ≤ 0 from hx)]) measurableSet_Iic
  have hright : IntegrableOn (fun x : ℝ => Real.exp (-t * |x|)) (Ioi 0) :=
    h₂.congr_fun (fun x hx => by rw [abs_of_pos hx]) measurableSet_Ioi
  simpa only [← compl_Iic, union_compl_self, integrableOn_univ] using hleft.union hright

/-- The exact Fourier formula for the multiplier of the Poisson kernel. -/
theorem mellinPoissonKernel_eq_fourierInv {t : ℝ} (ht : 0 < t) (y : ℝ) :
    (mellinPoissonKernel t y : ℂ) =
      𝓕⁻ (fun x : ℝ => (Real.exp (-t * |x|) : ℂ)) y := by
  let v : ℝ := 2 * Real.pi * y
  let a : ℂ := (t : ℂ) + (v : ℂ) * Complex.I
  let b : ℂ := -(t : ℂ) + (v : ℂ) * Complex.I
  have ha : 0 < a.re := by simpa [a, Complex.mul_re] using ht
  have hb : b.re < 0 := by simpa [b, Complex.mul_re] using neg_neg_of_pos ht
  rw [Real.fourierInv_eq']
  simp only [real_inner_comm, Real.inner_apply, smul_eq_mul, Complex.ofReal_exp]
  let F (x : ℝ) := Complex.exp ((↑(2 * Real.pi * (y * x)) * Complex.I)) *
    Complex.exp (↑(-t * |x|))
  change (mellinPoissonKernel t y : ℂ) = ∫ x, F x
  have hF : Integrable F := by
    apply Integrable.mono' (integrable_exp_neg_abs_mul ht)
    · fun_prop
    · exact .of_forall fun x => by simp [F, Complex.norm_exp, Complex.mul_re]
  rw [← integral_add_compl measurableSet_Iic hF, compl_Iic]
  have hFa : (∫ x : ℝ in Iic 0, F x) = ∫ x : ℝ in Iic 0, Complex.exp (a * x) := by
    apply setIntegral_congr_fun measurableSet_Iic
    intro x hx
    simp only [F, a, v, abs_of_nonpos (show x ≤ 0 from hx), ← Complex.exp_add, Complex.ofReal_mul,
      Complex.ofReal_neg]
    congr 1
    ring
  have hFb : (∫ x : ℝ in Ioi 0, F x) = ∫ x : ℝ in Ioi 0, Complex.exp (b * x) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    simp only [F, b, v, abs_of_pos (show 0 < x from hx), ← Complex.exp_add, Complex.ofReal_mul,
      Complex.ofReal_neg]
    congr 1
    ring
  rw [hFa, hFb, integral_exp_mul_complex_Iic ha, integral_exp_mul_complex_Ioi hb]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  have ht' : t ≠ 0 := ht.ne'
  have ha' : a ≠ 0 := fun h => by simp [h] at ha
  have hb' : b ≠ 0 := fun h => by simp [h] at hb
  have hd : t ^ 2 + v ^ 2 ≠ 0 := by positivity
  rw [mellinPoissonKernel, ← show v = 2 * Real.pi * y from rfl]
  push_cast
  have hd' : ((t : ℂ) ^ 2 + (v : ℂ) ^ 2) ≠ 0 := by exact_mod_cast hd
  field_simp
  simp only [a, b]
  linear_combination (2 * (t : ℂ)) * (v : ℂ) ^ 2 * Complex.I_sq

theorem mellinPoissonKernel_nonneg {t : ℝ} (ht : 0 < t) (y : ℝ) :
    0 ≤ mellinPoissonKernel t y := by unfold mellinPoissonKernel; positivity

private theorem mellinPoissonKernel_rescale {t : ℝ} (ht : 0 < t) (y : ℝ) :
    mellinPoissonKernel t y = (2 / t) * (1 + ((2 * Real.pi / t) * y) ^ 2)⁻¹ := by
  unfold mellinPoissonKernel
  have h₁ : t ^ 2 + (2 * Real.pi * y) ^ 2 ≠ 0 := by positivity
  have h₂ : 1 + ((2 * Real.pi / t) * y) ^ 2 ≠ 0 := by positivity
  field_simp [ht.ne', h₁, h₂]

private theorem mellinPoissonKernel_continuous {t : ℝ} (ht : 0 < t) :
    Continuous (mellinPoissonKernel t) := by
  unfold mellinPoissonKernel
  exact continuous_const.div (by fun_prop) fun _ => by positivity

theorem mellinPoissonKernel_integrable {t : ℝ} (ht : 0 < t) :
    Integrable (mellinPoissonKernel t) := by
  have hc : 0 < 2 * Real.pi / t := by positivity
  exact ((integrable_inv_one_add_sq.comp_mul_left' hc.ne').const_mul (2 / t)).congr
    (.of_forall fun y => (mellinPoissonKernel_rescale ht y).symm)

theorem mellinPoissonKernel_integral {t : ℝ} (ht : 0 < t) :
    ∫ y, mellinPoissonKernel t y = 1 := by
  have hc : 0 < 2 * Real.pi / t := by positivity
  simp_rw [mellinPoissonKernel_rescale ht]
  rw [integral_const_mul, Measure.integral_comp_mul_left (fun x : ℝ => (1 + x ^ 2)⁻¹),
    integral_univ_inv_one_add_sq,
    abs_of_pos (inv_pos.mpr hc), smul_eq_mul]
  field_simp [ht.ne', Real.pi_ne_zero]

private theorem mellinPoissonKernel_superlevel {t c : ℝ} (ht : 0 < t) (hc : 0 < c) (y : ℝ) :
    ∃ r : ℝ, {x : ℝ | c < mellinPoissonKernel t (y - x)} = Metric.ball y r := by
  let A := 2 * t / c - t ^ 2
  refine ⟨Real.sqrt A / (2 * Real.pi), ?_⟩
  have hp : 0 < 2 * Real.pi := by positivity
  ext x
  simp only [Set.mem_ofPred_eq, Metric.mem_ball, Real.dist_eq]
  have hd : 0 < t ^ 2 + (2 * Real.pi * (y - x)) ^ 2 := by positivity
  have hrew : c < mellinPoissonKernel t (y - x) ↔ (2 * Real.pi * (y - x)) ^ 2 < A := by
    rw [mellinPoissonKernel, lt_div_iff₀ hd]
    dsimp [A]
    rw [lt_sub_iff_add_lt, add_comm, lt_div_iff₀ hc, mul_comm c]
  rw [hrew, lt_div_iff₀ hp, mul_comm |x - y|]
  have habs : 2 * Real.pi * |x - y| = |2 * Real.pi * (y - x)| := by
    rw [abs_mul, abs_of_pos hp, abs_sub_comm]
  rw [habs]
  by_cases hA : 0 ≤ A
  · calc
      _ ↔ (2 * Real.pi * (y - x)) ^ 2 < (Real.sqrt A) ^ 2 := by rw [Real.sq_sqrt hA]
      _ ↔ _ := by rw [sq_lt_sq, abs_of_nonneg (Real.sqrt_nonneg _)]
  · rw [Real.sqrt_eq_zero_of_nonpos (le_of_not_ge hA)]
    exact iff_of_false (not_lt_of_ge ((le_of_not_ge hA).trans (sq_nonneg _)))
      (not_lt_of_ge (abs_nonneg _))

/-- A nonnegative error with small integrals over all balls about a center
has small integral against every Poisson kernel at that center. -/
theorem mellinPoissonKernel_lintegral_le {h : ℝ → ℝ} (hm : AEMeasurable h volume)
    (y : ℝ) (ε : ℝ≥0∞) (hB : ∀ r : ℝ,
      (∫⁻ x in Metric.ball y r, ENNReal.ofReal (h x)) ≤ ε * volume (Metric.ball y r))
    {t : ℝ} (ht : 0 < t) :
    (∫⁻ x, ENNReal.ofReal (h x) * ENNReal.ofReal (mellinPoissonKernel t (y - x))) ≤
      ε * ∫⁻ x, ENNReal.ofReal (mellinPoissonKernel t (y - x)) := by
  let p (x : ℝ) := mellinPoissonKernel t (y - x)
  let ν := volume.withDensity (fun x => ENNReal.ofReal (h x))
  have hp : Measurable p := ((mellinPoissonKernel_continuous ht).comp
    (continuous_const.sub continuous_id)).measurable
  have hn : ∀ x, 0 ≤ p x := fun x => mellinPoissonKernel_nonneg ht _
  change (∫⁻ x, ENNReal.ofReal (h x) * ENNReal.ofReal (p x)) ≤
    ε * ∫⁻ x, ENNReal.ofReal (p x)
  have hν : (∫⁻ x, ENNReal.ofReal (p x) ∂ν) =
      ∫⁻ x, ENNReal.ofReal (h x) * ENNReal.ofReal (p x) :=
    lintegral_withDensity_eq_lintegral_mul₀ hm.ennreal_ofReal hp.ennreal_ofReal.aemeasurable
  rw [← hν]
  change (∫⁻ x, ENNReal.ofReal (p x) ∂ν) ≤ ε • (∫⁻ x, ENNReal.ofReal (p x))
  rw [← lintegral_smul_measure]
  rw [lintegral_eq_lintegral_meas_lt ν (.of_forall hn) hp.aemeasurable,
    lintegral_eq_lintegral_meas_lt (ε • (volume : Measure ℝ)) (.of_forall hn) hp.aemeasurable]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ioi] with c hc
  obtain ⟨r, hr⟩ := mellinPoissonKernel_superlevel ht (show 0 < c from hc) y
  change ν {x | c < mellinPoissonKernel t (y - x)} ≤
    (ε • (volume : Measure ℝ)) {x | c < mellinPoissonKernel t (y - x)}
  rw [hr, Measure.smul_apply, withDensity_apply _ Metric.isOpen_ball.measurableSet]
  exact hB r

private def mellinPoissonFourierTest (t y x : ℝ) : ℂ :=
  (Real.exp (-t * |x|) : ℂ) * Complex.exp (-(↑(2 * Real.pi * (y * x)) * Complex.I))

private theorem mellinPoissonFourierTest_norm (t y x : ℝ) :
    ‖mellinPoissonFourierTest t y x‖ = Real.exp (-t * |x|) := by
  simp [mellinPoissonFourierTest, Complex.norm_exp, Complex.mul_re]

private theorem mellinPoissonFourierTest_continuous (t y : ℝ) :
    Continuous (mellinPoissonFourierTest t y) := by
  unfold mellinPoissonFourierTest
  fun_prop

private theorem mellinPoissonFourierTest_integrable {t : ℝ} (ht : 0 < t) (y : ℝ) :
    Integrable (mellinPoissonFourierTest t y) :=
  (integrable_exp_neg_abs_mul ht).mono' (mellinPoissonFourierTest_continuous t y).aestronglyMeasurable
    (.of_forall fun x => (mellinPoissonFourierTest_norm t y x).le)

private theorem mellinPoissonFourierTest_memLp {t : ℝ} (ht : 0 < t) (y : ℝ) :
    MemLp (mellinPoissonFourierTest t y) 2 volume := by
  rw [memLp_two_iff_integrable_sq_norm (mellinPoissonFourierTest_continuous t y).aestronglyMeasurable]
  refine (integrable_exp_neg_abs_mul (show 0 < 2 * t by positivity)).congr (.of_forall fun x => ?_)
  change Real.exp (-(2 * t) * |x|) = ‖mellinPoissonFourierTest t y x‖ ^ 2
  rw [mellinPoissonFourierTest_norm, pow_two, ← Real.exp_add]
  congr 1
  ring

private theorem mellinPoissonFourierTest_fourierInv {t : ℝ} (ht : 0 < t) (y w : ℝ) :
    𝓕⁻ (mellinPoissonFourierTest t y) w = (mellinPoissonKernel t (y - w) : ℂ) := by
  have he : mellinPoissonKernel t (y - w) = mellinPoissonKernel t (w - y) := by
    unfold mellinPoissonKernel
    rw [show 2 * Real.pi * (y - w) = -(2 * Real.pi * (w - y)) by ring, neg_sq]
  rw [he, mellinPoissonKernel_eq_fourierInv ht]
  simp only [Real.fourierInv_eq', Real.inner_apply, smul_eq_mul, mellinPoissonFourierTest]
  apply integral_congr_ae
  refine .of_forall fun x => ?_
  dsimp only
  rw [mul_comm (↑(Real.exp (-t * |x|)) : ℂ), ← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- Inverse Fourier evaluation of an attenuated square integrable profile
equals convolution with the Poisson kernel of its boundary L² trace. -/
theorem mellinPoissonKernel_boundary_convolution {t : ℝ} (ht : 0 < t)
    (u : Lp ℂ 2 (volume : Measure ℝ)) (y : ℝ) :
    (∫ x : ℝ, Complex.exp (↑(2 * Real.pi * (y * x)) * Complex.I) *
        (Real.exp (-t * |x|) : ℂ) * u x) =
      ∫ w : ℝ, (mellinPoissonKernel t (y - w) : ℂ) * realFourierL2.symm u w := by
  let g := (mellinPoissonFourierTest_memLp ht y).toLp (mellinPoissonFourierTest t y)
  have hg : (g : ℝ → ℂ) =ᵐ[volume] mellinPoissonFourierTest t y :=
    (mellinPoissonFourierTest_memLp ht y).coeFn_toLp
  have hgI : Integrable (g : ℝ → ℂ) :=
    (mellinPoissonFourierTest_integrable ht y).congr hg.symm
  have hG : (realFourierL2.symm g : ℝ → ℂ) =ᵐ[volume]
      fun w => (mellinPoissonKernel t (y - w) : ℂ) := by
    refine (realFourierL2_symm_ae_eq_fourierInv g hgI).trans (.of_forall fun w => ?_)
    have he : 𝓕⁻ (g : ℝ → ℂ) w = 𝓕⁻ (mellinPoissonFourierTest t y) w := by
      rw [Real.fourierInv_eq', Real.fourierInv_eq']
      exact integral_congr_ae (hg.mono fun x hx => congrArg (_ • ·) hx)
    exact he.trans (mellinPoissonFourierTest_fourierInv ht y w)
  calc
    _ = inner ℂ g u := by
      rw [MeasureTheory.L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hg] with x hx
      rw [RCLike.inner_apply, hx]
      simp only [mellinPoissonFourierTest, ← Complex.exp_conj, map_mul, map_neg,
        Complex.conj_ofReal, Complex.conj_I, mul_neg, neg_neg]
      ring
    _ = inner ℂ (realFourierL2.symm g) (realFourierL2.symm u) :=
      (realFourierL2.symm.inner_map_map g u).symm
    _ = _ := by
      rw [MeasureTheory.L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hG] with w hw
      rw [RCLike.inner_apply, hw, Complex.conj_ofReal, mul_comm]

private theorem mellinPoissonKernel_memLp {t : ℝ} (ht : 0 < t) :
    MemLp (mellinPoissonKernel t) 2 volume := by
  rw [memLp_two_iff_integrable_sq_norm (mellinPoissonKernel_continuous ht).aestronglyMeasurable]
  apply ((mellinPoissonKernel_integrable ht).const_mul (2 / t)).mono'
    ((mellinPoissonKernel_continuous ht).norm.pow 2).aestronglyMeasurable
  refine .of_forall fun y => ?_
  change ‖‖mellinPoissonKernel t y‖ ^ 2‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), Real.norm_eq_abs,
    abs_of_nonneg (mellinPoissonKernel_nonneg ht y),
    sq]
  apply mul_le_mul_of_nonneg_right _ (mellinPoissonKernel_nonneg ht y)
  rw [mellinPoissonKernel_rescale ht]
  exact mul_le_of_le_one_right (by positivity) (inv_le_one_of_one_le₀ (le_add_of_nonneg_right (sq_nonneg _)))

private theorem mellinPoissonKernel_tail_le {t δ : ℝ} (ht : 0 < t) (hδ : 0 < δ)
    {x : ℝ} (hx : δ ≤ |x|) :
    mellinPoissonKernel t x ≤ t * (1 + ((2 * Real.pi * δ) ^ 2)⁻¹) * mellinPoissonKernel 1 x := by
  let B := (2 * Real.pi * δ) ^ 2
  let C := (2 * Real.pi * x) ^ 2
  have hB : 0 < B := by dsimp [B]; positivity
  have hBC : B ≤ C := by
    dsimp [B, C]
    rw [← sq_abs (2 * Real.pi * x), abs_mul,
      abs_of_pos (show 0 < 2 * Real.pi by positivity)]
    exact pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left hx (by positivity)) _
  have hC : 0 < C := hB.trans_le hBC
  have hrat : 1 + C ≤ (1 + B⁻¹) * (t ^ 2 + C) := by
    have hb := (le_div_iff₀ hB).2 (by simpa using hBC : 1 * B ≤ C)
    rw [div_eq_mul_inv, mul_comm C] at hb
    nlinarith [mul_nonneg (inv_nonneg.mpr hB.le) (sq_nonneg t)]
  change 2 * t / (t ^ 2 + C) ≤ t * (1 + B⁻¹) * (2 * (1 : ℝ) / (1 ^ 2 + C))
  norm_num only [one_pow, mul_one]
  have h₁ : 0 < t ^ 2 + C := by positivity
  have h₂ : 0 < 1 + C := by positivity
  apply (div_le_iff₀ h₁).2
  rw [mul_assoc _ (2 / (1 + C)), div_mul_eq_mul_div, ← mul_div_assoc]
  apply (le_div_iff₀ h₂).2
  convert mul_le_mul_of_nonneg_left hrat (show 0 ≤ 2 * t by positivity) using 1
  all_goals ring

private theorem mellinPoissonKernel_integral_sub_left {t : ℝ} (ht : 0 < t) (y : ℝ) :
    ∫ x, mellinPoissonKernel t (y - x) = 1 :=
  ((Measure.measurePreserving_sub_left volume y).integral_comp
    (MeasurableEquiv.subLeft y).measurableEmbedding (mellinPoissonKernel t)).trans
      (mellinPoissonKernel_integral ht)

/-- At Lebesgue points of an L² profile its Poisson integrals converge
as the positive parameter tends to zero. -/
theorem mellinPoissonKernel_tendsto_ae {f : ℝ → ℂ} (hf : MemLp f 2 volume) :
    ∀ᵐ y ∂volume, Tendsto (fun t => ∫ x, (mellinPoissonKernel t (y - x) : ℂ) * f x)
      (𝓝[>] 0) (𝓝 (f y)) := by
  filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub volume
    (hf.locallyIntegrable (by norm_num)) 1]
    with y hy
  let H (x : ℝ) := ‖f x - f y‖
  have hH : AEStronglyMeasurable H volume :=
    (hf.aestronglyMeasurable.sub aestronglyMeasurable_const).norm
  have hHloc : LocallyIntegrable H volume := by
    rw [← locallyIntegrableOn_univ]
    exact (((hf.locallyIntegrable (by norm_num)).sub
      (locallyIntegrable_const (f y))).locallyIntegrableOn univ).norm
  have hAve : Tendsto (fun r : ℝ => ⨍ x in Metric.closedBall y r, H x) (𝓝[>] 0) (𝓝 0) := by
    refine hy (fun _ : ℝ => y) id tendsto_id ?_
    filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
    exact Metric.mem_closedBall_self (by simpa using hr.le)
  have hweighted {t : ℝ} (ht : 0 < t) :
      Integrable (fun x => mellinPoissonKernel t (y - x) * H x) := by
    let p (x : ℝ) := mellinPoissonKernel t (y - x)
    have hpn : ∀ x, 0 ≤ p x := fun _ => mellinPoissonKernel_nonneg ht _
    have hpI : Integrable p := (mellinPoissonKernel_integrable ht).comp_sub_left y
    have hp₂ : MemLp p 2 volume :=
      (mellinPoissonKernel_memLp ht).comp_measurePreserving (Measure.measurePreserving_sub_left _ y)
    refine ((hp₂.integrable_mul hf.norm).add (hpI.mul_const ‖f y‖)).mono'
      (hpI.aestronglyMeasurable.mul hH) (.of_forall fun x => ?_)
    change ‖p x * H x‖ ≤ p x * ‖f x‖ + p x * ‖f y‖
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hpn x) (norm_nonneg _)), ← mul_add]
    exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) (hpn x)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ₀, hδ₀, hsmall⟩ := Metric.mem_nhdsWithin_iff.mp
    ((tendsto_order.mp hAve).2 _ (show 0 < ε / 3 by positivity))
  let δ := δ₀ / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  let D := Metric.ball y δ
  have hD : MeasurableSet D := Metric.isOpen_ball.measurableSet
  have hball (r : ℝ) (hr : 0 < r) (hrδ : r ≤ δ) :
      (∫⁻ x in Metric.ball y r, ENNReal.ofReal (H x)) ≤
        ENNReal.ofReal (ε / 3) * volume (Metric.ball y r) := by
    have hA : (⨍ x in Metric.closedBall y r, H x) < ε / 3 :=
      hsmall (show r ∈ Metric.ball 0 δ₀ ∩ Ioi (0 : ℝ) from
      ⟨by rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hr]; dsimp [δ] at hrδ; linarith, hr⟩)
    have hvol : (volume : Measure ℝ).real (Metric.closedBall y r) = 2 * r := by
      simp [Measure.real, Real.volume_closedBall, hr.le]
    have hI := hHloc.integrableOn_isCompact (isCompact_closedBall y r)
    rw [setAverage_eq, hvol, smul_eq_mul, ← div_eq_inv_mul] at hA
    refine (lintegral_mono_set Metric.ball_subset_closedBall).trans ?_
    rw [← ofReal_integral_eq_lintegral_ofReal hI (.of_forall fun _ => norm_nonneg _),
      Real.volume_ball, ← ENNReal.ofReal_mul (show 0 ≤ ε / 3 by positivity)]
    exact ENNReal.ofReal_le_ofReal ((div_lt_iff₀ (by positivity)).1 hA).le
  have hall (r : ℝ) :
      (∫⁻ x in Metric.ball y r, ENNReal.ofReal (D.indicator H x)) ≤
        ENNReal.ofReal (ε / 3) * volume (Metric.ball y r) := by
    have he : (fun x => ENNReal.ofReal (D.indicator H x)) =
        D.indicator (fun x => ENNReal.ofReal (H x)) := by
      funext x
      by_cases hx : x ∈ D <;> simp [hx]
    rw [he, setLIntegral_indicator hD]
    by_cases hr : 0 < r
    · by_cases hrδ : r ≤ δ
      · rw [inter_eq_right.mpr (Metric.ball_subset_ball hrδ)]
        exact hball r hr hrδ
      · have hsub : D ⊆ Metric.ball y r := Metric.ball_subset_ball (le_of_not_ge hrδ)
        rw [inter_eq_left.mpr hsub]
        exact (hball δ hδ le_rfl).trans (by gcongr)
    · simp [Metric.ball_eq_empty.mpr (le_of_not_gt hr)]
  let A := 1 + ((2 * Real.pi * δ) ^ 2)⁻¹
  let M := ∫ x, A * (mellinPoissonKernel 1 (y - x) * H x)
  have hMt : Tendsto (fun t : ℝ => t * M) (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous (fun t : ℝ => t * M) := by fun_prop
    simpa only [zero_mul] using (hc.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin,
    (tendsto_order.mp hMt).2 (ε / 3) (by positivity)]
    with t (ht : 0 < t) htM
  let p (x : ℝ) := mellinPoissonKernel t (y - x)
  have hpn (x : ℝ) : 0 ≤ p x := mellinPoissonKernel_nonneg ht _
  have hpI : Integrable p := (mellinPoissonKernel_integrable ht).comp_sub_left y
  have hDweighted : Integrable (fun x => D.indicator H x * p x) := by
    have he : (fun x => D.indicator H x * p x) = D.indicator (fun x => p x * H x) := by
      funext x
      by_cases hx : x ∈ D <;> simp [hx, mul_comm]
    rw [he]
    exact (hweighted ht).indicator hD
  have hHead : (∫ x, D.indicator H x * p x) ≤ ε / 3 := by
    have h := mellinPoissonKernel_lintegral_le (hH.indicator hD).aemeasurable y
      (ENNReal.ofReal (ε / 3)) hall ht
    change (∫⁻ x, ENNReal.ofReal (D.indicator H x) * ENNReal.ofReal (p x)) ≤
      ENNReal.ofReal (ε / 3) * (∫⁻ x, ENNReal.ofReal (p x)) at h
    have hn (x : ℝ) : 0 ≤ D.indicator H x := by
      by_cases hx : x ∈ D <;> simp [hx, H]
    have he : (∫⁻ x, ENNReal.ofReal (D.indicator H x * p x)) =
        ∫⁻ x, ENNReal.ofReal (D.indicator H x) * ENNReal.ofReal (p x) :=
      lintegral_congr fun x => ENNReal.ofReal_mul (hn x)
    rw [← he, ← ofReal_integral_eq_lintegral_ofReal hDweighted
      (.of_forall fun x => mul_nonneg (hn x) (hpn x)),
      ← ofReal_integral_eq_lintegral_ofReal hpI (.of_forall hpn),
      mellinPoissonKernel_integral_sub_left ht y, ENNReal.ofReal_one, mul_one] at h
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity : 0 ≤ ε / 3)).mp h
  have hTailI : Integrable (fun x => t * (A * (mellinPoissonKernel 1 (y - x) * H x))) :=
    ((hweighted one_pos).const_mul A).const_mul t
  have hError : (∫ x, p x * H x) ≤ ε / 3 + t * M := by
    have hpoint (x : ℝ) : p x * H x ≤
        D.indicator H x * p x + t * (A * (mellinPoissonKernel 1 (y - x) * H x)) := by
      by_cases hx : x ∈ D
      · rw [indicator_of_mem hx, mul_comm (H x)]
        exact le_add_of_nonneg_right (mul_nonneg ht.le
          (mul_nonneg (by dsimp [A]; positivity)
            (mul_nonneg (mellinPoissonKernel_nonneg one_pos _) (norm_nonneg _))))
      · rw [indicator_of_notMem hx, zero_mul, zero_add]
        have hdist : δ ≤ |y - x| := by
          simpa [D, Metric.mem_ball, Real.dist_eq, abs_sub_comm] using hx
        exact (mul_le_mul_of_nonneg_right (mellinPoissonKernel_tail_le ht hδ hdist)
          (norm_nonneg _)).trans_eq (by ring)
    have h := integral_mono (hweighted ht) (hDweighted.add hTailI) hpoint
    simp only [Pi.add_apply, integral_add hDweighted hTailI, integral_const_mul] at h
    have he : M = A * ∫ x, mellinPoissonKernel 1 (y - x) * H x :=
      integral_const_mul _ _
    rw [← he] at h
    exact h.trans (add_le_add_left hHead _)
  have hcomp : Integrable (fun x => (p x : ℂ) * f x) := by
    have hp₂ : MemLp (fun x => p x) 2 volume :=
      (mellinPoissonKernel_memLp ht).comp_measurePreserving (Measure.measurePreserving_sub_left _ y)
    have hpC : MemLp (fun x => (p x : ℂ)) 2 volume := hp₂.of_le
      (Complex.continuous_ofReal.comp_aestronglyMeasurable hpI.aestronglyMeasurable)
      (.of_forall fun x => by simp)
    exact hpC.integrable_mul hf
  have hc : Integrable (fun x => (p x : ℂ) * f y) := hpI.ofReal.mul_const _
  have heq : (∫ x, (p x : ℂ) * f x) - f y = ∫ x, (p x : ℂ) * (f x - f y) := by
    simp_rw [mul_sub]
    rw [integral_sub hcomp hc, integral_mul_const, integral_complex_ofReal,
      mellinPoissonKernel_integral_sub_left ht y, Complex.ofReal_one, one_mul]
  rw [dist_eq_norm, heq]
  apply (norm_integral_le_integral_norm _).trans_lt
  simp_rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hpn _)]
  exact hError.trans_lt (by change t * M < ε / 3 at htM; linarith)

private theorem scalarDampedMellin_boundary_ae {b s : ℝ} (hs : 0 ≤ s)
    (f : StripSobolev b b s) :
    ∀ᵐ y ∂volume, Tendsto (fun t : ℝ => ∫ x : ℝ,
        Complex.exp (↑(2 * Real.pi * (y * x)) * Complex.I) *
          (Real.exp (-t * |x|) : ℂ) * (Real.exp (b * x) • f x))
      (𝓝[>] 0) (𝓝 (mellinFrequencyValues hs (fractionalMellinLine b s f) y)) := by
  let g := mellinFrequencyValues hs (fractionalMellinLine b s f)
  let u := realFourierL2 g
  have hu : (u : ℝ → ℂ) =ᵐ[volume] fun x => Real.exp (b * x) • f x := by
    dsimp only [u, g]
    unfold mellinFrequencyValues
    rw [ContinuousLinearMap.comp_apply]
    change (realFourierL2 (realFourierL2.symm (lpTwoMeasureInclusion _ _)) : ℝ → ℂ) =ᵐ[volume] _
    rw [LinearIsometryEquiv.apply_symm_apply]
    exact (lpTwoMeasureInclusion_ae _ _).trans (fractionalMellinLine_ae b s f)
  filter_upwards [mellinPoissonKernel_tendsto_ae (Lp.memLp g)] with y hy
  refine hy.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
  rw [show g = realFourierL2.symm u from (realFourierL2.symm_apply_apply _).symm,
    ← mellinPoissonKernel_boundary_convolution ht u y]
  exact integral_congr_ae (hu.mono fun x hx =>
    congrArg (fun z : ℂ => Complex.exp (↑(2 * Real.pi * (y * x)) * Complex.I) *
      (Real.exp (-t * |x|) : ℂ) * z) hx)

private theorem scalarDampedIntegrand_eq {b d t x y : ℝ} (hx : (b + d) * x = b * x + -t * |x|)
    (v : ℂ) :
    Complex.exp (↑(2 * Real.pi * (y * x)) * Complex.I) *
        (Real.exp (-t * |x|) : ℂ) * (Real.exp (b * x) • v) =
      v * mellinEvaluationKernel 0 (⟨b + d, 2 * Real.pi * y⟩ : ℂ) x := by
  rw [mellinEvaluationKernel, pow_zero, mul_one, Complex.real_smul]
  simp only [Complex.ofReal_exp, ← mul_assoc, ← Complex.exp_add]
  rw [mul_comm v]
  congr 2
  apply Complex.ext
  · simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re,
      Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_zero, zero_add]
    linarith
  · simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re,
      Complex.ofReal_im, Complex.I_im, mul_zero, add_zero]
    ring

/-- The actual Mellin values have a full almost-everywhere boundary limit
from the right half-plane, identified with the endpoint Fourier trace. -/
theorem scalarRightHalfLineTrace_boundary_ae {b s : ℝ} (hs : 0 ≤ s)
    (f : StripSobolev b b s) (hf : ∀ᵐ x ∂volume, 0 < x → f x = 0) :
    ∀ᵐ y ∂volume, Tendsto
      (fun t : ℝ => scalarMellinMoment f 0 (⟨b + t, 2 * Real.pi * y⟩ : ℂ))
      (𝓝[>] 0) (𝓝 (mellinFrequencyValues hs (fractionalMellinLine b s f) y)) := by
  filter_upwards [scalarDampedMellin_boundary_ae hs f] with y hy
  refine hy.congr' (.of_forall fun t => ?_)
  apply integral_congr_ae
  filter_upwards [hf] with x hx
  by_cases hx' : 0 < x
  · simp [hx hx']
  · exact scalarDampedIntegrand_eq (b := b) (d := t) (t := t) (by
      rw [abs_of_nonpos (le_of_not_gt hx')]
      ring) (f x)

/-- The actual Mellin values have a full almost-everywhere boundary limit
from the left half-plane, identified with the endpoint Fourier trace. -/
theorem scalarLeftHalfLineTrace_boundary_ae {b s : ℝ} (hs : 0 ≤ s)
    (f : StripSobolev b b s) (hf : ∀ᵐ x ∂volume, x < 0 → f x = 0) :
    ∀ᵐ y ∂volume, Tendsto
      (fun t : ℝ => scalarMellinMoment f 0 (⟨b + -t, 2 * Real.pi * y⟩ : ℂ))
      (𝓝[>] 0) (𝓝 (mellinFrequencyValues hs (fractionalMellinLine b s f) y)) := by
  filter_upwards [scalarDampedMellin_boundary_ae hs f] with y hy
  refine hy.congr' (.of_forall fun t => ?_)
  apply integral_congr_ae
  filter_upwards [hf] with x hx
  by_cases hx' : x < 0
  · simp [hx hx']
  · exact scalarDampedIntegrand_eq (b := b) (d := -t) (t := t) (by
      rw [abs_of_nonneg (le_of_not_gt hx')]
      ring) (f x)

private theorem scalarMellinCompact_boundary_ae {a b e s d δ : ℝ}
    (hab : a ≤ b) (he : e ∈ Icc a b) (hs : 0 ≤ s) (f : StripSobolev a b s)
    (hd : d = 1 ∨ d = -1) (hδ : 0 < δ)
    (hI : ∀ t ∈ Ioc 0 δ, e + d * t ∈ Ioo a b) :
    ∀ᵐ y ∂volume, Tendsto
      (fun t : ℝ => scalarMellinMoment f 0 (⟨e + d * t, 2 * Real.pi * y⟩ : ℂ))
      (𝓝[>] 0) (𝓝 (mellinFrequencyValues hs (scalarFractionalTrace hab he s f) y)) := by
  let h := scalarInterval_lineMeasure_le hab he s
  let v := lpTwoMeasureInclusion h f
  have hv : (v : ℝ → ℂ) =ᵐ[volume] f :=
    (absolutelyContinuous_amplitudeMeasure volume _ (stripSobolevAmplitude_continuous e e s).measurable
      (stripSobolevAmplitude_pos e e s)).ae_le (lpTwoMeasureInclusion_ae h f)
  filter_upwards [scalarDampedMellin_boundary_ae hs v] with y hy
  let G (t x : ℝ) := f x * mellinEvaluationKernel 0 (⟨e + d * t, 2 * Real.pi * y⟩ : ℂ) x
  let H (t x : ℝ) := Complex.exp (↑(2 * Real.pi * (y * x)) * Complex.I) *
    (Real.exp (-t * |x|) : ℂ) * (Real.exp (e * x) • f x)
  let B (x : ℝ) := 2 * ‖f x‖ * Real.exp ((e + d * δ) * x)
  have hD : ∀ᶠ t : ℝ in 𝓝[>] 0, t ∈ Ioc 0 δ :=
    Ioc_mem_nhdsGT hδ
  have hvG : Tendsto (fun t => ∫ x, H t x) (𝓝[>] 0)
      (𝓝 (mellinFrequencyValues hs (scalarFractionalTrace hab he s f) y)) := by
    refine hy.congr' (.of_forall fun t => integral_congr_ae ?_)
    exact hv.mono fun x hx => congrArg (fun c : ℂ =>
      Complex.exp (↑(2 * Real.pi * (y * x)) * Complex.I) *
        (Real.exp (-t * |x|) : ℂ) * (Real.exp (e * x) • c)) hx
  have hnorm (t x : ℝ) : ‖G t x‖ = ‖f x‖ * Real.exp ((e + d * t) * x) := by
    simp [G, mellinEvaluationKernel_norm]
  have hnorm' (t x : ℝ) : ‖H t x‖ = ‖f x‖ * Real.exp (e * x + -t * |x|) := by
    simp only [H, norm_mul, Complex.norm_exp, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, Real.exp_zero,
      one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), norm_smul,
      Real.exp_add]
    ring
  have hBoundI : Integrable B := by
    have hm := (scalarMellinMoment_compact hs f 0
      (z := ⟨e + d * δ, 2 * Real.pi * y⟩) (hI δ ⟨hδ, le_rfl⟩)).1
    exact (hm.norm.const_mul 2).congr (.of_forall fun x => by
      change 2 * ‖G δ x‖ = B x
      rw [hnorm]
      unfold B
      ring)
  have hpoint (t : ℝ) (ht : t ∈ Ioc 0 δ) (x : ℝ) : ‖G t x - H t x‖ ≤ B x := by
    by_cases hx : d * x ≤ 0
    · have heq : d * x = -|x| := by
        rcases hd with rfl | rfl
        · simp only [one_mul] at hx ⊢
          rw [abs_of_nonpos hx, neg_neg]
        · simp only [neg_one_mul, neg_nonpos] at hx ⊢
          rw [abs_of_nonneg hx]
      have hEq : H t x = G t x :=
        scalarDampedIntegrand_eq (by linear_combination t * heq) (f x)
      rw [hEq, sub_self, norm_zero]
      exact mul_nonneg (mul_nonneg (by norm_num) (norm_nonneg _)) (Real.exp_pos _).le
    · have hp : 0 ≤ d * x := (le_of_not_ge hx)
      have hle₁ : (e + d * t) * x ≤ (e + d * δ) * x := by
        nlinarith [mul_le_mul_of_nonneg_left (show t ≤ δ from ht.2) hp]
      have hle₂ : e * x + -t * |x| ≤ (e + d * δ) * x := by
        nlinarith [mul_nonneg (abs_nonneg x) (show 0 ≤ t from ht.1.le), mul_nonneg hp hδ.le]
      refine (norm_sub_le _ _).trans ?_
      rw [hnorm, hnorm']
      exact (add_le_add
        (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hle₁) (norm_nonneg _))
        (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hle₂) (norm_nonneg _))).trans_eq (by
          unfold B
          ring)
  have hGmeas (t : ℝ) : AEStronglyMeasurable (G t) volume :=
    (Lp.stronglyMeasurable f).aestronglyMeasurable.mul
      (show Continuous (mellinEvaluationKernel 0 (⟨e + d * t, 2 * Real.pi * y⟩ : ℂ)) from by
        unfold mellinEvaluationKernel
        fun_prop).aestronglyMeasurable
  have hHmeas (t : ℝ) : AEStronglyMeasurable (H t) volume := by
    apply AEStronglyMeasurable.mul
    · exact (show Continuous (fun x : ℝ => Complex.exp (↑(2 * Real.pi * (y * x)) * Complex.I) *
        (Real.exp (-t * |x|) : ℂ)) from by fun_prop).aestronglyMeasurable
    · exact (show Continuous (fun x : ℝ => Real.exp (e * x)) from by fun_prop).aestronglyMeasurable.smul
        (Lp.stronglyMeasurable f).aestronglyMeasurable
  have hErr : Tendsto (fun t : ℝ => ∫ x, (G t x - H t x)) (𝓝[>] 0) (𝓝 0) := by
    have hC (x : ℝ) : Continuous (fun t => G t x - H t x) := by
      have hz (t : ℝ) : (⟨e + d * t, 2 * Real.pi * y⟩ : ℂ) =
          ((e + d * t : ℝ) : ℂ) + ((2 * Real.pi * y : ℝ) : ℂ) * Complex.I := by
        apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
      unfold G H mellinEvaluationKernel
      simp_rw [hz]
      fun_prop
    have htlim (x : ℝ) : Tendsto (fun t => G t x - H t x) (𝓝[>] 0) (𝓝 (0 : ℂ)) := by
      have hzero : G 0 x - H 0 x = 0 := by
        apply sub_eq_zero.mpr
        symm
        simpa only [G, H, mul_zero, add_zero] using
          scalarDampedIntegrand_eq (b := e) (d := 0) (t := 0) (x := x) (y := y) (by simp) (f x)
      rw [← hzero]
      exact (hC x).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    simpa using (tendsto_integral_filter_of_dominated_convergence (f := fun _ => (0 : ℂ))
      B (.of_forall fun t => (hGmeas t).sub (hHmeas t)) (hD.mono fun t ht => .of_forall (hpoint t ht))
      hBoundI (.of_forall htlim))
  have hTot := hvG.add hErr
  rw [add_zero] at hTot
  refine hTot.congr' (hD.mono fun t ht => ?_)
  have hGI : Integrable (G t) := (scalarMellinMoment_compact hs f 0 (hI t ht)).1
  have hEI : Integrable (fun x => G t x - H t x) :=
    hBoundI.mono' ((hGmeas t).sub (hHmeas t)) (.of_forall (hpoint t ht))
  have hHI : Integrable (H t) := (hGI.sub hEI).congr (.of_forall fun x => by
    change G t x - (G t x - H t x) = H t x
    abel)
  change (∫ x, H t x) + (∫ x, G t x - H t x) = ∫ x, G t x
  rw [integral_sub hGI hHI]
  abel

/-- At the lower endpoint of a nondegenerate compact base the actual scalar
Mellin integral has the full almost-everywhere vertical limit. -/
theorem scalarCompactTrace_lower_boundary_ae {a b s : ℝ} (hab : a < b)
    (hs : 0 ≤ s) (f : StripSobolev a b s) :
    ∀ᵐ y ∂volume, Tendsto
      (fun t : ℝ => scalarMellinMoment f 0 (⟨a + t, 2 * Real.pi * y⟩ : ℂ))
      (𝓝[>] 0) (𝓝 (mellinFrequencyValues hs
        (scalarFractionalTrace hab.le (left_mem_Icc.mpr hab.le) s f) y)) := by
  simpa only [one_mul] using scalarMellinCompact_boundary_ae hab.le (left_mem_Icc.mpr hab.le)
    hs f (d := 1) (δ := (b - a) / 2) (Or.inl rfl) (by positivity) (by
      intro t ht
      have h₁ : 0 < t := ht.1
      have h₂ : t ≤ (b - a) / 2 := ht.2
      simp only [one_mul]
      exact ⟨by linarith, by linarith⟩)

/-- At the upper endpoint of a nondegenerate compact base the actual scalar
Mellin integral has the full almost-everywhere vertical limit. -/
theorem scalarCompactTrace_upper_boundary_ae {a b s : ℝ} (hab : a < b)
    (hs : 0 ≤ s) (f : StripSobolev a b s) :
    ∀ᵐ y ∂volume, Tendsto
      (fun t : ℝ => scalarMellinMoment f 0 (⟨b + -t, 2 * Real.pi * y⟩ : ℂ))
      (𝓝[>] 0) (𝓝 (mellinFrequencyValues hs
        (scalarFractionalTrace hab.le (right_mem_Icc.mpr hab.le) s f) y)) := by
  simpa only [neg_one_mul] using scalarMellinCompact_boundary_ae hab.le (right_mem_Icc.mpr hab.le)
    hs f (d := -1) (δ := (b - a) / 2) (Or.inr rfl) (by positivity) (by
      intro t ht
      have h₁ : 0 < t := ht.1
      have h₂ : t ≤ (b - a) / 2 := ht.2
      simp only [neg_one_mul]
      exact ⟨by linarith, by linarith⟩)

end
end Masullo
