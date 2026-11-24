import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open Filter MeasureTheory Set Topology
open scoped ENat ContDiff

namespace Masullo

/-- The real-place density in x = log t, after subtracting a reference exponent.
The exponents a and b are 1/2 - z and 1/2 - z₀.
The negative real component uses exp x + 1 in the local denominator. -/
noncomputable def realPlaceDensity (negative : Bool) (a b : ℂ) (x : ℝ) : ℂ :=
  (Complex.exp (a * (x : ℂ)) - Complex.exp (b * (x : ℂ))) /
    ((Real.exp x + if negative then 1 else -1 : ℝ) : ℂ)

/-- Express the repaired density in the manuscript's norm coordinate t.
The outer inverse factor is the Haar measure dt/t. -/
theorem realPlaceIntegral_change_variables (negative : Bool) (a b : ℂ) (weight : ℝ → ℂ) :
    (∫ x in Ioi (0 : ℝ), weight x * realPlaceDensity negative a b x) =
      ∫ t : ℝ in Ioi 1, (t : ℂ)⁻¹ * (weight (Real.log t) *
        (((t : ℂ) ^ a - (t : ℂ) ^ b) / ((t + if negative then 1 else -1 : ℝ) : ℂ))) := by
  rw [← show Real.log 1 = 0 by simp]
  rw [← integral_comp_log_Ioi _ zero_lt_one]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  have htpos : 0 < t := zero_lt_one.trans ht
  have htne : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr htpos.ne'
  simp only [realPlaceDensity, Real.exp_log htpos, Complex.cpow_def_of_ne_zero htne,
    ← Complex.ofReal_log htpos.le, ← Complex.ofReal_inv, Complex.real_smul]
  rw [mul_comm a, mul_comm b]

noncomputable def realPlaceEnvelope (M δ x : ℝ) : ℝ :=
  (Ioc 0 1).indicator (fun _ => 2 * M * Real.exp M) x + 4 * Real.exp (-δ * x)

theorem realPlaceEnvelope_integrable {M δ : ℝ} (hδ : 0 < δ) :
    IntegrableOn (realPlaceEnvelope M δ) (Ioi 0) := by
  apply Integrable.add
  · apply Integrable.integrableOn
    exact (integrable_indicator_iff measurableSet_Ioc).mpr
      (integrableOn_const (by simp [Real.volume_Ioc]))
  · exact (integrableOn_exp_mul_Ioi (neg_neg_of_pos hδ) 0).const_mul _

/-- A single integrable bound works throughout any bounded family of exponents
with real parts uniformly below 1. -/
theorem norm_realPlaceDensity_le {negative : Bool} {a b : ℂ} {M δ x : ℝ}
    (ha : ‖a‖ ≤ M) (hb : ‖b‖ ≤ M) (har : a.re ≤ 1 - δ) (hbr : b.re ≤ 1 - δ)
    (hx : 0 < x) :
    ‖realPlaceDensity negative a b x‖ ≤ realPlaceEnvelope M δ x := by
  let d := Real.exp x + (if negative then 1 else -1)
  have hd : Real.exp x - 1 ≤ d := by
    cases negative
    · simp [d, sub_eq_add_neg]
    · simp [d]; linarith
  have hdx : x ≤ d := (by linarith [Real.add_one_le_exp x] : x ≤ Real.exp x - 1).trans hd
  have hdpos : 0 < d := hx.trans_le hdx
  have hn (c : ℂ) (hc : ‖c‖ ≤ M) (hx₁ : x ≤ 1) :
      ‖Complex.exp (c * (x : ℂ)) - 1‖ ≤ M * Real.exp M * x := by
    have hm : 0 ≤ M := (norm_nonneg c).trans hc
    have hcx : ‖c * (x : ℂ)‖ ≤ M := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx]
      exact mul_le_of_le_one_right hm hx₁ |>.trans' (mul_le_mul_of_nonneg_right hc hx.le)
    calc
      _ ≤ ‖c * (x : ℂ)‖ * Real.exp ‖c * (x : ℂ)‖ := by
        simpa using Complex.norm_exp_sub_sum_le_norm_mul_exp (c * (x : ℂ)) 1
      _ ≤ (M * x) * Real.exp M := by
        apply mul_le_mul _ (Real.exp_le_exp.mpr hcx) (Real.exp_pos _).le (by positivity)
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx]
        exact mul_le_mul_of_nonneg_right hc hx.le
      _ = _ := by ring
  unfold realPlaceDensity
  change ‖(Complex.exp (a * (x : ℂ)) - Complex.exp (b * (x : ℂ))) / (d : ℂ)‖ ≤ _
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hdpos]
  by_cases hx₁ : x ≤ 1
  · rw [realPlaceEnvelope, indicator_of_mem (show x ∈ Ioc (0 : ℝ) 1 from ⟨hx, hx₁⟩)]
    have hnum :
        ‖Complex.exp (a * (x : ℂ)) - Complex.exp (b * (x : ℂ))‖ ≤
          (2 * M * Real.exp M) * x := by
      calc
        _ ≤ ‖Complex.exp (a * (x : ℂ)) - 1‖ + ‖Complex.exp (b * (x : ℂ)) - 1‖ := by
          rw [← sub_sub_sub_cancel_right (Complex.exp (a * (x : ℂ)))
            (Complex.exp (b * (x : ℂ))) 1]
          exact norm_sub_le _ _
        _ ≤ _ := by linarith [hn a ha hx₁, hn b hb hx₁]
    have hM : 0 ≤ 2 * M * Real.exp M := by
      have := (norm_nonneg a).trans ha
      positivity
    refine ((div_le_iff₀ hdpos).mpr
      (hnum.trans (mul_le_mul_of_nonneg_left hdx hM))).trans ?_
    exact le_add_of_nonneg_right (by positivity)
  · rw [realPlaceEnvelope, indicator_of_notMem (show x ∉ Ioc (0 : ℝ) 1 from fun h => hx₁ h.2),
      zero_add]
    have hexp : Real.exp x / 2 ≤ d := by
      linarith [Real.add_one_le_exp x, lt_of_not_ge hx₁]
    have hterm (c : ℂ) (hc : c.re ≤ 1 - δ) :
        ‖Complex.exp (c * (x : ℂ))‖ ≤ Real.exp x * Real.exp (-δ * x) := by
      rw [Complex.norm_exp, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      nlinarith [mul_le_mul_of_nonneg_right hc hx.le]
    apply (div_le_iff₀ hdpos).mpr
    calc
      _ ≤ 2 * (Real.exp x * Real.exp (-δ * x)) := by
        linarith [norm_sub_le (Complex.exp (a * (x : ℂ))) (Complex.exp (b * (x : ℂ))),
          hterm a har, hterm b hbr]
      _ = (4 * Real.exp (-δ * x)) * (Real.exp x / 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hexp (by positivity)

/-- Smooth cutoffs that vanish near zero and beyond n + 1, and eventually
equal one at each point of the positive ray. -/
noncomputable def realPlaceCutoff (n : ℕ) (x : ℝ) : ℝ :=
  Real.smoothTransition (((n : ℝ) + 1) * x - 1) *
    Real.smoothTransition ((n : ℝ) + 1 - x)

theorem realPlaceCutoff_smooth (n : ℕ) : ContDiff ℝ ∞ (realPlaceCutoff n) := by
  unfold realPlaceCutoff
  have hLeft : ContDiff ℝ ∞ (fun x : ℝ => ((n : ℝ) + 1) * x - 1) := by fun_prop
  have hRight : ContDiff ℝ ∞ (fun x : ℝ => (n : ℝ) + 1 - x) := by fun_prop
  exact (Real.smoothTransition.contDiff.comp hLeft).mul
    (Real.smoothTransition.contDiff.comp hRight)

theorem realPlaceCutoff_support (n : ℕ) :
    tsupport (realPlaceCutoff n) ⊆ Icc (((n : ℝ) + 1)⁻¹) ((n : ℝ) + 1) := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  by_contra h
  apply hx
  unfold realPlaceCutoff
  rcases lt_or_ge x (((n : ℝ) + 1)⁻¹) with hlow | hlow
  · have hn : 0 < (n : ℝ) + 1 := by positivity
    have harg : ((n : ℝ) + 1) * x - 1 ≤ 0 := by
      rw [inv_eq_one_div, lt_div_iff₀ hn] at hlow
      nlinarith
    rw [Real.smoothTransition.zero_of_nonpos harg, zero_mul]
  · have hhigh : (n : ℝ) + 1 < x := lt_of_not_ge fun hx' => h ⟨hlow, hx'⟩
    rw [Real.smoothTransition.zero_of_nonpos (by linarith : (n : ℝ) + 1 - x ≤ 0), mul_zero]

theorem realPlaceCutoff_mem_Icc (n : ℕ) (x : ℝ) :
    realPlaceCutoff n x ∈ Icc (0 : ℝ) 1 := by
  unfold realPlaceCutoff
  exact ⟨mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _),
    mul_le_one₀ (Real.smoothTransition.le_one _) (Real.smoothTransition.nonneg _)
      (Real.smoothTransition.le_one _)⟩

theorem realPlaceCutoff_eventually_one {x : ℝ} (hx : 0 < x) :
    (fun n => realPlaceCutoff n x) =ᶠ[atTop] fun _ => 1 := by
  obtain ⟨N, hN⟩ := exists_nat_gt (max (2 / x) x)
  filter_upwards [eventually_ge_atTop N] with n hn
  have hNn : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hlow := (le_max_left (2 / x) x).trans (hN.le.trans hNn)
  have hhigh := (le_max_right (2 / x) x).trans (hN.le.trans hNn)
  have hl : 2 ≤ ((n : ℝ) + 1) * x := by
    have := (div_le_iff₀ hx).mp hlow
    linarith
  unfold realPlaceCutoff
  rw [Real.smoothTransition.one_of_one_le (by linarith),
    Real.smoothTransition.one_of_one_le (by linarith), one_mul]

/-- Removing the smooth cutoffs converges uniformly throughout the whole family
bounded by M and δ. The measurable unit-bounded factor allows local characters. -/
theorem realPlaceCutoff_integrals_uniform {M δ : ℝ} (hδ : 0 < δ)
    (weight : ℝ → ℂ) (hm : Measurable weight) (hw : ∀ x, ‖weight x‖ ≤ 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (negative : Bool) (a b : ℂ),
      ‖a‖ ≤ M → ‖b‖ ≤ M → a.re ≤ 1 - δ → b.re ≤ 1 - δ →
      ‖(∫ x in Ioi (0 : ℝ), (realPlaceCutoff n x : ℂ) * (weight x * realPlaceDensity negative a b x)) -
        (∫ x in Ioi (0 : ℝ), weight x * realPlaceDensity negative a b x)‖ < ε := by
  let μ := volume.restrict (Ioi (0 : ℝ))
  let envelope := realPlaceEnvelope M δ
  have hi : Integrable envelope μ := realPlaceEnvelope_integrable hδ
  let error (n : ℕ) (x : ℝ) : ℝ := (1 - realPlaceCutoff n x) * envelope x
  have hc (n : ℕ) : Measurable (realPlaceCutoff n) :=
    (realPlaceCutoff_smooth n).continuous.measurable
  have hemeas (n : ℕ) : AEStronglyMeasurable (error n) μ :=
    (measurable_const.sub (hc n)).aestronglyMeasurable.mul hi.1
  have hebound (n : ℕ) : ∀ᵐ x ∂μ, ‖error n x‖ ≤ ‖envelope x‖ :=
    Eventually.of_forall fun x => by
      have h := realPlaceCutoff_mem_Icc n x
      rw [show ‖error n x‖ = (1 - realPlaceCutoff n x) * ‖envelope x‖ by
        simp [error, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr h.2)]]
      exact mul_le_of_le_one_left (norm_nonneg _) (by linarith [h.1])
  have helim : ∀ᵐ x ∂μ, Tendsto (fun n => error n x) atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with x hx
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [realPlaceCutoff_eventually_one hx] with n hn
    simp [error, hn]
  have he : Tendsto (fun n => ∫ x, error n x ∂μ) atTop (𝓝 (0 : ℝ)) := by
    simpa only [integral_zero] using
      (tendsto_integral_of_dominated_convergence (f := fun _ : ℝ => (0 : ℝ)) (‖envelope ·‖)
        hemeas hi.norm hebound helim)
  filter_upwards [he.eventually (gt_mem_nhds hε)] with n hn negative a b ha hb har hbr
  let f (x : ℝ) := weight x * realPlaceDensity negative a b x
  let cutoff (x : ℝ) : ℂ := (realPlaceCutoff n x : ℂ)
  have hf : Measurable f := by
    unfold f realPlaceDensity
    fun_prop
  have hca : Measurable cutoff := Complex.continuous_ofReal.measurable.comp (hc n)
  have hbound : ∀ᵐ x ∂μ, ‖f x‖ ≤ envelope x := by
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with x hx
    rw [show ‖f x‖ = ‖weight x‖ * ‖realPlaceDensity negative a b x‖ by simp [f]]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hw x)).trans
      (norm_realPlaceDensity_le ha hb har hbr hx)
  have hcut : ∀ x, ‖cutoff x‖ ≤ 1 := fun x => by
    have h := realPlaceCutoff_mem_Icc n x
    simpa [cutoff, Real.norm_eq_abs, abs_of_nonneg h.1] using h.2
  have hfint : Integrable f μ := hi.mono' hf.aestronglyMeasurable hbound
  have hcint : Integrable (fun x => cutoff x * f x) μ := by
    apply hi.mono' (hca.mul hf).aestronglyMeasurable
    filter_upwards [hbound] with x hx
    change ‖cutoff x * f x‖ ≤ envelope x
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg (f x)) (hcut x)).trans hx
  have heint : Integrable (error n) μ := hi.norm.mono' (hemeas n) (hebound n)
  change ‖(∫ x, cutoff x * f x ∂μ) - ∫ x, f x ∂μ‖ < ε
  rw [← integral_sub hcint hfint]
  refine (norm_integral_le_of_norm_le heint ?_).trans_lt hn
  filter_upwards [hbound] with x hx
  have h := realPlaceCutoff_mem_Icc n x
  rw [← sub_one_mul, norm_mul, show cutoff x - 1 = ((realPlaceCutoff n x - 1 : ℝ) : ℂ) by
    simp [cutoff], Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr h.2)]
  rw [neg_sub]
  exact mul_le_mul_of_nonneg_left hx (sub_nonneg.mpr h.2)

/-- The repaired real-place integral is holomorphic for Re a < 1, with the
reference exponent b fixed and Re b < 1. -/
theorem differentiableOn_realPlaceIntegral (negative : Bool) {b : ℂ} (hb : b.re < 1)
    (weight : ℝ → ℂ) (hm : Measurable weight) (hw : ∀ x, ‖weight x‖ ≤ 1) :
    DifferentiableOn ℂ (fun a => ∫ x in Ioi (0 : ℝ), weight x * realPlaceDensity negative a b x)
      {a : ℂ | a.re < 1} := by
  intro a ha
  change a.re < 1 at ha
  let μ := volume.restrict (Ioi (0 : ℝ))
  let δ := (1 - a.re) / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  let s := {c : ℂ | c.re < 1 - δ}
  have hs : s ∈ 𝓝 a :=
    (isOpen_lt Complex.continuous_re continuous_const).mem_nhds (by
      change a.re < 1 - δ
      dsimp [δ]
      linarith)
  let d (x : ℝ) := Real.exp x + (if negative then 1 else -1)
  let F (c : ℂ) (x : ℝ) := weight x * realPlaceDensity negative c b x
  let F' (c : ℂ) (x : ℝ) :=
    weight x * ((Complex.exp (c * (x : ℂ)) * (x : ℂ)) / (d x : ℂ))
  let bound (x : ℝ) := (1 + 2 / δ) * Real.exp (-(δ / 2) * x)
  have hmeas (c : ℂ) : Measurable (F c) := by
    unfold F realPlaceDensity
    fun_prop
  have hint : Integrable (F a) μ := by
    let gap := min (1 - a.re) (1 - b.re)
    let M := max ‖a‖ ‖b‖
    have hg : 0 < gap := lt_min (by linarith) (by linarith)
    apply (realPlaceEnvelope_integrable (M := M) hg).mono' (hmeas a).aestronglyMeasurable
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with x hx
    unfold F
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hw x)).trans
      (norm_realPlaceDensity_le (le_max_left ..) (le_max_right ..)
        (by have := min_le_left (1 - a.re) (1 - b.re); dsimp [gap]; linarith)
        (by have := min_le_right (1 - a.re) (1 - b.re); dsimp [gap]; linarith) hx)
  have hF' : AEStronglyMeasurable (F' a) μ := by
    apply Measurable.aestronglyMeasurable
    unfold F' d
    fun_prop
  have hbound : Integrable bound μ :=
    (integrableOn_exp_mul_Ioi (by linarith : -(δ / 2) < 0) 0).const_mul _
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (F := F) (bound := bound)
    hs (Eventually.of_forall fun c => (hmeas c).aestronglyMeasurable) hint hF' ?_ hbound ?_).2.differentiableAt.differentiableWithinAt
  · filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with x hx c hc
    change 0 < x at hx
    change c.re < 1 - δ at hc
    have hd : Real.exp x - 1 ≤ d x := by cases negative <;> simp [d, sub_eq_add_neg]
    have hdpos : 0 < d x := by linarith [Real.add_one_le_exp x]
    have hratio : Real.exp x * x ≤ (1 + x) * d x := by
      calc
        _ ≤ (1 + x) * (Real.exp x - 1) := by nlinarith [Real.add_one_le_exp x]
        _ ≤ _ := mul_le_mul_of_nonneg_left hd (by positivity)
    have hexp : ‖Complex.exp (c * (x : ℂ))‖ ≤ Real.exp x * Real.exp (-δ * x) := by
      rw [Complex.norm_exp, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      nlinarith [mul_le_mul_of_nonneg_right hc.le hx.le]
    have hpoly : 1 + x ≤ (1 + 2 / δ) * Real.exp ((δ / 2) * x) := by
      have hsmall : 1 ≤ Real.exp ((δ / 2) * x) := Real.one_le_exp (by positivity)
      have hx' : x ≤ (2 / δ) * Real.exp ((δ / 2) * x) := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hδ]
        nlinarith [Real.add_one_le_exp ((δ / 2) * x)]
      linarith [show (1 + 2 / δ) * Real.exp ((δ / 2) * x) =
        Real.exp ((δ / 2) * x) + (2 / δ) * Real.exp ((δ / 2) * x) by ring]
    unfold F'
    rw [norm_mul, norm_div, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos hx, abs_of_pos hdpos]
    refine (mul_le_of_le_one_left (by positivity) (hw x)).trans ?_
    calc
      _ ≤ (1 + x) * Real.exp (-δ * x) := by
        apply (div_le_iff₀ hdpos).mpr
        calc
          _ ≤ (Real.exp x * Real.exp (-δ * x)) * x := mul_le_mul_of_nonneg_right hexp hx.le
          _ = (Real.exp x * x) * Real.exp (-δ * x) := by ring
          _ ≤ ((1 + x) * d x) * Real.exp (-δ * x) :=
            mul_le_mul_of_nonneg_right hratio (by positivity)
          _ = _ := by ring
      _ ≤ ((1 + 2 / δ) * Real.exp ((δ / 2) * x)) * Real.exp (-δ * x) :=
        mul_le_mul_of_nonneg_right hpoly (by positivity)
      _ = bound x := by
        change _ = (1 + 2 / δ) * Real.exp (-(δ / 2) * x)
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring
  · exact Eventually.of_forall fun x c _ => by
      unfold F F' realPlaceDensity d
      have h := ((hasDerivAt_id c).mul_const (x : ℂ)).cexp
      simpa only [id_eq, one_mul] using
        (((h.sub_const (Complex.exp (b * (x : ℂ)))).div_const
          ((Real.exp x + if negative then 1 else -1 : ℝ) : ℂ)).const_mul (weight x))

end Masullo
