import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

open Complex Filter Function MeasureTheory MeromorphicOn Metric Set
open scoped ContDiff Polynomial SchwartzMap

namespace Masullo

/-- The closed unit-height box used in Lemma 9.3.2.4. -/
def unitHeightBox (a b T : ℝ) : Set ℂ :=
  Complex.equivRealProdCLM.symm '' (Icc a b ×ˢ Icc T (T + 1))

/-- The disk center used for the Jensen estimate on a unit-height box. -/
noncomputable def unitHeightCenter (a b T : ℝ) : ℂ :=
  ((a + b) / 2 : ℝ) + (T + (1 / 2 : ℝ) : ℝ) * Complex.I

private theorem unitHeightBox_subset_disk {a b : ℝ} (hab : a ≤ b) (T : ℝ) :
    unitHeightBox a b T ⊆ closedBall (unitHeightCenter a b T) (b - a + 2) := by
  rintro z ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩
  rw [mem_closedBall, dist_eq_norm]
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  have hre :
      (Complex.equivRealProdCLM.symm (x, y) - unitHeightCenter a b T).re =
        x - (a + b) / 2 := by simp [unitHeightCenter]
  have him :
      (Complex.equivRealProdCLM.symm (x, y) - unitHeightCenter a b T).im =
        y - (T + 1 / 2) := by simp [unitHeightCenter]
  rw [hre, him]
  have h₁ : |x - (a + b) / 2| ≤ (b - a) / 2 :=
    abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have h₂ : |y - (T + 1 / 2)| ≤ 1 / 2 :=
    abs_le.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩
  linarith

/-- A replacement for the zero count of Lemma 9.3.2.4. The ratio of the
outer circle bound to the value at the moving center may grow polynomially.
Normalizing by the center value allows both quantities to decay rapidly. -/
theorem vertical_zero_count_of_relative_bound
    {a b M p : ℝ} (hab : a ≤ b) (hM : 1 ≤ M) (hp : 0 ≤ p)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f univ)
    (hcenter : ∀ T : ℝ, 2 ≤ |T| → f (unitHeightCenter a b T) ≠ 0)
    (hrelative : ∀ T : ℝ, 2 ≤ |T| → ∀ z ∈ sphere (unitHeightCenter a b T) (b - a + 3),
      ‖f z‖ ≤ M * |T| ^ p * ‖f (unitHeightCenter a b T)‖) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 2 ≤ |T| →
      ((∑ᶠ z, divisor f (unitHeightBox a b T) z : ℤ) : ℝ) ≤ C * Real.log |T| := by
  let r := b - a + 2
  let R := b - a + 3
  have hr : 0 < r := by dsimp [r]; linarith
  have hR : 0 < R := by dsimp [R]; linarith
  have hrR : r < R := by dsimp [r, R]; linarith
  have hlog : 0 < Real.log (R / r) := Real.log_pos ((one_lt_div hr).mpr hrR)
  let C := (Real.log M / Real.log 2 + p) / Real.log (R / r)
  have hlog₂ : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogM : 0 ≤ Real.log M := Real.log_nonneg hM
  refine ⟨C, by dsimp [C]; positivity, fun T hT => ?_⟩
  let c := unitHeightCenter a b T
  let B := unitHeightBox a b T
  let D := closedBall c |r|
  let g (z : ℂ) := (f c)⁻¹ * f z
  have hc := hcenter T hT
  have hgc : g c = 1 := inv_mul_cancel₀ hc
  have hg : AnalyticOnNhd ℂ g univ := analyticOnNhd_const.mul hf
  have hB : IsCompact B :=
    (isCompact_Icc.prod isCompact_Icc).image Complex.equivRealProdCLM.symm.continuous
  have h₂ : 0 < |T| := (by norm_num : (0 : ℝ) < 2).trans_le hT
  have hpos : 0 < ‖f c‖ := norm_pos_iff.mpr hc
  have htop (z : ℂ) (hz : z ∈ sphere c |R|) : ‖g z‖ ≤ M * |T| ^ p := by
    change ‖(f c)⁻¹ * f z‖ ≤ _
    rw [norm_mul, norm_inv, mul_comm, ← div_eq_mul_inv, div_le_iff₀ hpos]
    exact hrelative T hT z (by simpa only [abs_of_pos hR] using hz)
  have hbound : 1 ≤ M * |T| ^ p := by
    exact one_le_mul_of_one_le_of_one_le hM
      (Real.one_le_rpow ((by norm_num : (1 : ℝ) ≤ 2).trans hT) hp)
  have hj := AnalyticOnNhd.sum_divisor_le (c := c) (r := r) (R := R)
    (by simpa only [abs_of_pos hr] using hr)
    (by simpa only [abs_of_pos hr, abs_of_pos hR] using hrR) hbound
    (hg.mono (subset_univ _)) (by simp [hgc]) htop
  have hcount : (∑ᶠ z, divisor f B z) ≤ ∑ᶠ z, divisor g D z := by
    refine finsum_le_finsum' ((divisor f B).finiteSupport hB)
      ((divisor g D).finiteSupport (isCompact_closedBall _ _)) fun z => ?_
    by_cases hz : z ∈ B
    · have hz' : z ∈ D :=
        mem_closedBall.mpr ((mem_closedBall.mp (unitHeightBox_subset_disk hab T hz)).trans
          (le_abs_self r))
      rw [(hf.mono (subset_univ B)).meromorphicOn.divisor_apply hz,
        (hg.mono (subset_univ D)).meromorphicOn.divisor_apply hz']
      rw [show meromorphicOrderAt g z = meromorphicOrderAt f z from
        meromorphicOrderAt_mul_of_ne_zero analyticAt_const (inv_ne_zero hc)]
    · rw [(divisor f B).apply_eq_zero_of_notMem hz]
      exact (hg.mono (subset_univ D)).divisor_nonneg z
  calc
    _ ≤ ((∑ᶠ z, divisor g D z : ℤ) : ℝ) := by exact_mod_cast hcount
    _ ≤ Real.log (M * |T| ^ p / ‖g c‖) / Real.log (R / r) := hj
    _ = (Real.log M + p * Real.log |T|) / Real.log (R / r) := by
      rw [hgc, norm_one, div_one, Real.log_mul (zero_lt_one.trans_le hM).ne'
        (Real.rpow_pos_of_pos h₂ _).ne', Real.log_rpow h₂]
    _ ≤ C * Real.log |T| := by
      have hw : Real.log 2 ≤ Real.log |T| := Real.log_le_log (by norm_num) hT
      have hconst : Real.log M ≤ (Real.log M / Real.log 2) * Real.log |T| := by
        calc
          _ = (Real.log M / Real.log 2) * Real.log 2 := by field_simp
          _ ≤ _ := mul_le_mul_of_nonneg_left hw (by positivity)
      dsimp [C]
      rw [div_mul_eq_mul_div, add_mul]
      exact div_le_div_of_nonneg_right (add_le_add_left hconst _) hlog.le

private noncomputable def normalizedGaussian (b : ℂ) (x : ℝ) : ℂ :=
  ((Real.pi / -b) ^ (1 / 2 : ℂ))⁻¹ * Complex.exp (b * (x : ℂ) ^ 2)

private theorem gaussian_derivative_polynomial (b c : ℂ) (n : ℕ) :
    ∃ P : ℂ[X], ∀ x : ℝ,
      iteratedDeriv n (fun t : ℝ => Complex.exp (b * (t : ℂ) ^ 2 + c * t)) x =
        P.eval (x : ℂ) * Complex.exp (b * (x : ℂ) ^ 2 + c * x) := by
  induction n with
  | zero => exact ⟨1, fun x => by simp⟩
  | succ n ih =>
    obtain ⟨P, hP⟩ := ih
    refine ⟨P.derivative + P * (Polynomial.C (2 * b) * Polynomial.X + Polynomial.C c),
      fun x => ?_⟩
    rw [iteratedDeriv_succ, funext hP]
    have hQ : HasDerivAt (fun z : ℂ => b * z ^ 2 + c * z) (2 * b * (x : ℂ) + c) x := by
      have hpow : HasDerivAt (fun z : ℂ => z ^ 2) (2 * (x : ℂ)) x := by
        simpa using hasDerivAt_pow 2 (x : ℂ)
      have hlin : HasDerivAt (fun z : ℂ => c * z) c x := by
        simpa using (hasDerivAt_id (x : ℂ)).const_mul c
      rw [show 2 * b * (x : ℂ) + c = b * (2 * (x : ℂ)) + c by ring]
      exact (hpow.const_mul b).add hlin
    change deriv ((fun y : ℝ => P.eval (y : ℂ)) *
      fun y : ℝ => Complex.exp (b * (y : ℂ) ^ 2 + c * y)) x = _
    rw [((P.hasDerivAt (x : ℂ)).comp_ofReal.mul hQ.cexp.comp_ofReal).deriv]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    ring

private theorem gaussian_exp_bound {b c : ℂ} (hb : b.re < 0) :
    ∃ K : ℝ, ∀ x : ℝ,
      ‖Complex.exp (b * (x : ℂ) ^ 2 + c * x)‖ ≤ Real.exp K * Real.exp (-|x|) := by
  let R := (|c.re| + 1) / (-b.re)
  have hR : 0 < R := div_pos (by positivity) (neg_pos.mpr hb)
  refine ⟨(|c.re| + 1) * R, fun x => ?_⟩
  rw [Complex.norm_exp, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  simp only [Complex.add_re, ← Complex.ofReal_pow, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]
  have hx : c.re * x ≤ |c.re| * |x| := (le_abs_self _).trans_eq (abs_mul _ _)
  by_cases hxR : |x| ≤ R
  · have h := mul_le_mul_of_nonneg_left hxR (by positivity : 0 ≤ |c.re| + 1)
    nlinarith [mul_nonpos_of_nonpos_of_nonneg hb.le (sq_nonneg x)]
  · have hl := (div_le_iff₀ (neg_pos.mpr hb)).mp (show R ≤ |x| from le_of_not_ge hxR)
    have h := mul_le_mul_of_nonneg_right hl (abs_nonneg x)
    rw [mul_comm |x| (-b.re), mul_assoc, ← sq, sq_abs] at h
    have hK : 0 ≤ (|c.re| + 1) * R := by positivity
    linarith

private noncomputable def gaussianSchwartz (b c : ℂ) (hb : b.re < 0) : 𝓢(ℝ, ℂ) where
  toFun x := Complex.exp (b * (x : ℂ) ^ 2 + c * x)
  smooth' := by
    have hc : ContDiff ℝ ∞ (fun x : ℝ => (x : ℂ)) := Complex.ofRealCLM.contDiff
    fun_prop
  decay' k n := by
    obtain ⟨P, hP⟩ := gaussian_derivative_polynomial b c n
    obtain ⟨K, hK⟩ := gaussian_exp_bound (c := c) hb
    refine ⟨∑ i ∈ P.support, Real.exp K * ‖P.coeff i‖ * ((i + k).factorial : ℝ), fun x => ?_⟩
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, hP x, Real.norm_eq_abs, norm_mul]
    calc
      _ ≤ |x| ^ k * (‖P.eval (x : ℂ)‖ * (Real.exp K * Real.exp (-|x|))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hK x) (norm_nonneg _))
          (by positivity)
      _ ≤ |x| ^ k * ((∑ i ∈ P.support, ‖P.coeff i‖ * |x| ^ i) *
          (Real.exp K * Real.exp (-|x|))) := by
        gcongr
        rw [Polynomial.eval_eq_sum, Polynomial.sum]
        simpa only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs] using
          norm_sum_le P.support (fun i => P.coeff i * (x : ℂ) ^ i)
      _ = ∑ i ∈ P.support, Real.exp K * ‖P.coeff i‖ *
          (|x| ^ (i + k) * Real.exp (-|x|)) := by
        simp only [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [pow_add]
        ring
      _ ≤ _ := by
        refine Finset.sum_le_sum fun i _ => ?_
        have hi : |x| ^ (i + k) * Real.exp (-|x|) ≤ ((i + k).factorial : ℝ) := by
          rw [Real.exp_neg, ← div_eq_mul_inv]
          apply (div_le_iff₀ (Real.exp_pos _)).mpr
          rw [mul_comm]
          exact (div_le_iff₀ (by positivity)).mp (Real.pow_div_factorial_le_exp _ (abs_nonneg x) _)
        exact mul_le_mul_of_nonneg_left hi (by positivity)

private theorem gaussianBilateralLaplace {b : ℂ} (hb : b.re < 0) (s : ℂ) :
    Integrable (fun x : ℝ => Complex.exp (s * (x : ℂ)) * normalizedGaussian b x) ∧
      (∫ x : ℝ, Complex.exp (s * (x : ℂ)) * normalizedGaussian b x) =
        Complex.exp (-(s ^ 2 / (4 * b))) := by
  let K : ℂ := (Real.pi / -b) ^ (1 / 2 : ℂ)
  have hK : K ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl
    (div_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero)
      (neg_ne_zero.mpr (fun h => hb.ne (by simp [h])))))
  have he : (fun x : ℝ => Complex.exp (s * (x : ℂ)) * normalizedGaussian b x) =
      fun x : ℝ => K⁻¹ * Complex.exp (b * (x : ℂ) ^ 2 + s * (x : ℂ) + 0) := by
    funext x
    dsimp [normalizedGaussian, K]
    rw [add_zero, Complex.exp_add]
    ring
  rw [he]
  refine ⟨(integrable_cexp_quadratic' hb s 0).const_mul _, ?_⟩
  rw [integral_const_mul, integral_cexp_quadratic hb s 0, zero_sub]
  change K⁻¹ * (K * _) = _
  rw [← mul_assoc, inv_mul_cancel₀ hK, one_mul]

private noncomputable def gaussianPlus : ℂ := -(1 - Complex.I) / 8
private noncomputable def gaussianMinus : ℂ := -(1 + Complex.I) / 8

/-- The log-coordinate test giving the counterexample to the zero count. -/
noncomputable def zeroCountGaussianTest (x : ℝ) : ℂ :=
  (normalizedGaussian gaussianPlus x - normalizedGaussian gaussianMinus x) / (2 * Complex.I)

/-- Every exponential weight of the log-coordinate test is Schwartz. -/
theorem zeroCountGaussianTest_exponential_decay (σ : ℝ) :
    ∃ g : 𝓢(ℝ, ℂ), ⇑g = fun x => Real.exp (σ * x) • zeroCountGaussianTest x := by
  have hp : gaussianPlus.re < 0 := by norm_num [gaussianPlus, Complex.div_re, Complex.normSq_apply]
  have hm : gaussianMinus.re < 0 := by norm_num [gaussianMinus, Complex.div_re, Complex.normSq_apply]
  let KP : ℂ := ((Real.pi / -gaussianPlus) ^ (1 / 2 : ℂ))⁻¹
  let KM : ℂ := ((Real.pi / -gaussianMinus) ^ (1 / 2 : ℂ))⁻¹
  refine ⟨(2 * Complex.I : ℂ)⁻¹ •
    (KP • gaussianSchwartz gaussianPlus σ hp - KM • gaussianSchwartz gaussianMinus σ hm), ?_⟩
  funext x
  change (2 * Complex.I : ℂ)⁻¹ * (KP * Complex.exp (gaussianPlus * (x : ℂ) ^ 2 + σ * x) -
    KM * Complex.exp (gaussianMinus * (x : ℂ) ^ 2 + σ * x)) =
      Real.exp (σ * x) • ((KP * Complex.exp (gaussianPlus * (x : ℂ) ^ 2) -
        KM * Complex.exp (gaussianMinus * (x : ℂ) ^ 2)) / (2 * Complex.I))
  rw [Complex.real_smul, Complex.ofReal_exp, Complex.ofReal_mul, Complex.exp_add, Complex.exp_add]
  ring

/-- The bilateral Laplace transform of the test is the claimed entire
function. This is the Mellin transform after exponential change of variable. -/
theorem zeroCountGaussianTest_transform (s : ℂ) :
    (∫ x : ℝ, Complex.exp (s * (x : ℂ)) * zeroCountGaussianTest x) =
      Complex.exp (s ^ 2) * Complex.sin (s ^ 2) := by
  have hp : gaussianPlus.re < 0 := by norm_num [gaussianPlus, Complex.div_re, Complex.normSq_apply]
  have hm : gaussianMinus.re < 0 := by norm_num [gaussianMinus, Complex.div_re, Complex.normSq_apply]
  obtain ⟨hpI, hpE⟩ := gaussianBilateralLaplace hp s
  obtain ⟨hmI, hmE⟩ := gaussianBilateralLaplace hm s
  have hp' : (4 * gaussianPlus) * (1 + Complex.I) = -1 := by
    unfold gaussianPlus
    ring_nf
    norm_num [Complex.I_sq]
  have hm' : (4 * gaussianMinus) * (1 - Complex.I) = -1 := by
    unfold gaussianMinus
    ring_nf
    norm_num [Complex.I_sq]
  have power {b c : ℂ} (h : (4 * b) * c = -1) : -(s ^ 2 / (4 * b)) = c * s ^ 2 := by
    have hb : 4 * b ≠ 0 := fun hb => by simp [hb] at h
    rw [← neg_div]
    apply (div_eq_iff hb).mpr
    linear_combination -s ^ 2 * h
  simp only [zeroCountGaussianTest, ← mul_div_assoc, mul_sub]
  rw [integral_div, integral_sub hpI hmI, hpE, hmE, power hp', power hm', Complex.sin]
  have hp'' : (1 + Complex.I) * s ^ 2 = s ^ 2 + s ^ 2 * Complex.I := by ring
  have hm'' : (1 - Complex.I) * s ^ 2 = s ^ 2 + -(s ^ 2 * Complex.I) := by ring
  rw [hp'', hm'', Complex.exp_add, Complex.exp_add, ← mul_sub]
  simp only [div_eq_mul_inv, mul_inv_rev, Complex.inv_I]
  ring

/-- The counterexample has a zero at each positive square root of an
integer multiple of π on the imaginary axis. -/
theorem zeroCountGaussianTest_zero (n : ℕ) :
    (∫ x : ℝ, Complex.exp (((Real.sqrt (n * Real.pi) : ℝ) : ℂ) * Complex.I * (x : ℂ)) *
      zeroCountGaussianTest x) = 0 := by
  rw [zeroCountGaussianTest_transform, mul_pow, Complex.I_sq]
  have hs : (((Real.sqrt (↑n * Real.pi) : ℝ) : ℂ) ^ 2) = (n : ℂ) * Real.pi := by
    norm_cast
    exact Real.sq_sqrt (by positivity)
  rw [hs, mul_neg_one, Complex.sin_neg, Complex.sin_nat_mul_pi, neg_zero, mul_zero]

/-- In the positive-real coordinate, the same test has the displayed
Mellin transform with the manuscript's Haar normalization. -/
theorem zeroCountGaussianTest_mellin (s : ℂ) :
    mellin (fun t => zeroCountGaussianTest (Real.log t)) s =
      Complex.exp (s ^ 2) * Complex.sin (s ^ 2) := by
  calc
    _ = ∫ x : ℝ, Complex.exp (-s * (x : ℂ)) * zeroCountGaussianTest x := by
      rw [mellin_eq_fourier, Real.fourier_eq']
      apply integral_congr_ae
      filter_upwards [] with x
      have hp : (2 * Real.pi) ≠ 0 := by positivity
      have hcoef : -2 * Real.pi * x * (s.im / (2 * Real.pi)) = -(s.im * x) := by field_simp
      have he : ((↑(-(s.im * x)) : ℂ) * I) + ((-s.re * x : ℝ) : ℂ) = -s * (x : ℂ) := by
        conv_rhs => rw [← Complex.re_add_im s]
        push_cast
        ring
      have heven : zeroCountGaussianTest (-x) = zeroCountGaussianTest x := by
        simp [zeroCountGaussianTest, normalizedGaussian]
      simp only [Real.inner_apply, real_smul, ofReal_exp, smul_eq_mul, ← mul_assoc,
        ← Complex.exp_add, hcoef, he, Real.log_exp, heven]
    _ = _ := by simpa using zeroCountGaussianTest_transform (-s)

/-- The counterexample concerns an actual nonzero Mellin transform. -/
theorem zeroCountGaussianTest_mellin_ne_zero :
    mellin (fun t => zeroCountGaussianTest (Real.log t))
      ((Real.sqrt (Real.pi / 2) : ℝ) : ℂ) ≠ 0 := by
  rw [zeroCountGaussianTest_mellin]
  have hs : ((Real.sqrt (Real.pi / 2) : ℝ) : ℂ) ^ 2 = ((Real.pi / 2 : ℝ) : ℂ) := by
    norm_cast
    exact Real.sq_sqrt (by positivity)
  rw [hs, ← Complex.ofReal_sin, Real.sin_pi_div_two, Complex.ofReal_one, mul_one]
  exact Complex.exp_ne_zero _

/-- The explicit Mellin transform has a finite set of distinct zeros in
each positive unit-height box whose cardinality has a linear lower bound. -/
theorem zeroCountGaussianTest_linear_lower_bound {T : ℝ} (hT : 0 ≤ T) :
    ∃ S : Set ℂ, S.Finite ∧ S ⊆ unitHeightBox (-1) 1 T ∧
      (∀ z ∈ S, mellin (fun t => zeroCountGaussianTest (Real.log t)) z = 0) ∧
      (2 * T + 1) / Real.pi - 1 ≤ (S.ncard : ℝ) := by
  let l := T ^ 2 / Real.pi
  let u := (T + 1) ^ 2 / Real.pi
  let A : Set ℕ := Icc ⌈l⌉₊ ⌊u⌋₊
  let point (n : ℕ) : ℂ := (Real.sqrt (n * Real.pi) : ℝ) * Complex.I
  have hpoint : Injective point := by
    intro n m h
    have him : Real.sqrt (n * Real.pi) = Real.sqrt (m * Real.pi) := by
      simpa only [point, mul_I_im, ofReal_re] using congrArg Complex.im h
    have hsq := congrArg (fun t : ℝ => t ^ 2) him
    rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)] at hsq
    exact_mod_cast mul_right_cancel₀ Real.pi_ne_zero hsq
  have hA : A.Finite := finite_Icc _ _
  refine ⟨point '' A, hA.image _, ?_, ?_, ?_⟩
  · rintro _ ⟨n, hn, rfl⟩
    have hlo : l ≤ (n : ℝ) := (Nat.le_ceil _).trans (Nat.cast_le.mpr hn.1)
    have hup : (n : ℝ) ≤ u :=
      (Nat.cast_le.mpr hn.2).trans (Nat.floor_le (by dsimp [u]; positivity))
    have h₁ : T ≤ Real.sqrt ((n : ℝ) * Real.pi) :=
      (Real.le_sqrt hT (by positivity)).mpr ((div_le_iff₀ Real.pi_pos).mp hlo)
    have h₂ : Real.sqrt ((n : ℝ) * Real.pi) ≤ T + 1 :=
      (Real.sqrt_le_left (by positivity)).mpr ((le_div_iff₀ Real.pi_pos).mp hup)
    exact ⟨(0, Real.sqrt ((n : ℝ) * Real.pi)), ⟨by norm_num, ⟨h₁, h₂⟩⟩,
      by simp only [Complex.equivRealProdCLM_symm_apply, ofReal_zero, zero_add, point]⟩
  · rintro _ ⟨n, _, rfl⟩
    rw [zeroCountGaussianTest_mellin, ← zeroCountGaussianTest_transform (point n)]
    exact zeroCountGaussianTest_zero n
  · rw [Set.ncard_image_of_injective _ hpoint]
    have hlu : l ≤ u := by dsimp [l, u]; gcongr; linarith
    have hceil : (⌈l⌉₊ : ℝ) < l + 1 := Nat.ceil_lt_add_one (by dsimp [l]; positivity)
    have hfloor : u < (⌊u⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one u
    have hs : ⌈l⌉₊ ≤ ⌊u⌋₊ + 1 :=
      Nat.ceil_le.mpr (by push_cast; linarith)
    have hcard : A.ncard = ⌊u⌋₊ + 1 - ⌈l⌉₊ := by
      change (Icc ⌈l⌉₊ ⌊u⌋₊).ncard = _
      rw [Set.ncard_eq_toFinset_card', toFinset_Icc, Nat.card_Icc]
    rw [hcard, Nat.cast_sub hs, Nat.cast_add, Nat.cast_one]
    have hdiff : u - l = (2 * T + 1) / Real.pi := by
      dsimp [l, u]
      rw [← sub_div]
      congr 1
      ring
    linarith

/-- This Mellin transform violates every logarithmic upper bound on the
number of distinct zeros in the specified boxes. -/
theorem zeroCountGaussianTest_not_logarithmic (C T₀ : ℝ) :
    ∃ T ≥ T₀, ∃ S : Set ℂ, S.Finite ∧ S ⊆ unitHeightBox (-1) 1 T ∧
      (∀ z ∈ S, mellin (fun t => zeroCountGaussianTest (Real.log t)) z = 0) ∧
      C * Real.log T < (S.ncard : ℝ) := by
  have hconstant : 0 < 1 / (Real.pi * (|C| + 1)) := by positivity
  obtain ⟨T, hT, ht, hsmall⟩ := ((eventually_ge_atTop T₀).and
    ((eventually_ge_atTop (Real.pi + 1)).and
      (Real.isLittleO_log_id_atTop.bound hconstant))).exists
  have ht₀ : 0 ≤ T := by linarith [Real.pi_pos]
  have hlog : 0 ≤ Real.log T := Real.log_nonneg (by linarith [Real.pi_pos])
  obtain ⟨S, hs, hbox, hz, hcard⟩ := zeroCountGaussianTest_linear_lower_bound ht₀
  refine ⟨T, hT, S, hs, hbox, hz, ?_⟩
  have hv : |C| * Real.log T ≤ T / Real.pi := by
    change ‖Real.log T‖ ≤ _ * ‖T‖ at hsmall
    rw [Real.norm_of_nonneg hlog, Real.norm_of_nonneg ht₀] at hsmall
    have hmul := mul_le_mul_of_nonneg_left hsmall (show 0 ≤ |C| + 1 by positivity)
    have he : (|C| + 1) * (1 / (Real.pi * (|C| + 1)) * T) = T / Real.pi := by field_simp
    rw [he] at hmul
    nlinarith
  refine ((mul_le_mul_of_nonneg_right (le_abs_self C) hlog).trans hv).trans_lt ?_
  refine lt_of_lt_of_le ?_ hcard
  have hπ : 0 < Real.pi := Real.pi_pos
  have hlast := div_lt_div_of_pos_right (show T + Real.pi < 2 * T + 1 by linarith) hπ
  rw [add_div, div_self hπ.ne'] at hlast
  linarith

end Masullo
