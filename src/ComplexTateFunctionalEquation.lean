import ArchimedeanGammaTests
import ArchimedeanMultiplicativeHaar
import UnitHaarDensity
import MellinFourierCrossProduct
import Mathlib.Analysis.Complex.Isometry
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

open Filter Function MeasureTheory Set Topology FourierTransform
open scoped SchwartzMap ComplexConjugate RealInnerProductSpace LineDeriv ENNReal NNReal

namespace Masullo

noncomputable section

private abbrev E := 𝓢(ℂ, ℂ)

private def complexTateFrequency : ℂ ≃L[ℝ] ℂ :=
  Complex.conjCLE.trans
    (LinearEquiv.smulOfNeZero ℝ ℂ 2 (by norm_num)).toContinuousLinearEquiv

private theorem complexTateFrequency_inner (x y : ℂ) :
    inner ℝ x ((2 : ℝ) • conj y) = 2 * (x*y).re := by
  rw [real_inner_smul_right, real_inner_eq_re_inner ℂ, RCLike.inner_apply']
  change 2 * (conj x * conj y).re = _
  rw [← map_mul, Complex.conj_re]

/-- The positive Fourier transform for the complex trace pairing and
twice the Euclidean additive measure. -/
def complexTateFourier : E →L[ℂ] E :=
  (2 : ℂ) •
    ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ complexTateFrequency) ∘L
      fourierInvCLM ℂ E)

theorem complexTateFourier_apply (f : E) (y : ℂ) :
    complexTateFourier f y = 2 * (𝓕⁻ f) ((2 : ℝ) • conj y) := rfl

/-- The operator uses the symmetric bilinear trace kernel, with no
unrecorded scalar in the additive measure. -/
theorem complexTateFourier_eq_integral (f : E) (y : ℂ) :
    complexTateFourier f y =
      2 * ∫ x : ℂ, f x * Complex.exp (↑(2 * Real.pi * (2 * (x * y).re)) * Complex.I) := by
  rw [complexTateFourier_apply, SchwartzMap.fourierInv_coe, Real.fourierInv_eq']
  congr 1
  apply integral_congr_ae
  exact .of_forall fun x ↦ by
    change Complex.exp (↑(2 * Real.pi * inner ℝ x ((2 : ℝ) • conj y)) * Complex.I) * f x = _
    rw [complexTateFrequency_inner, mul_comm]

private theorem complexTateFourier_gaussian (f : E)
    (hf : ∀ x : ℂ, f x = (Real.pi : ℂ)⁻¹ *
      (Real.exp (-(2 * Real.pi) * ‖x‖ ^ 2) : ℂ)) : complexTateFourier f = f := by
  obtain ⟨g, hg⟩ := exists_gaussian_schwartz (E := ℂ) (2 * Real.pi) (by positivity)
  have he : f = (Real.pi : ℂ)⁻¹ • g := by
    ext x
    rw [hf, smul_apply, smul_eq_mul, hg]
  rw [he, map_smul]
  congr 1
  have h : (g : ℂ → ℂ) = fun x : ℂ ↦
      Complex.exp (-(2 * (Real.pi : ℂ)) * (‖x‖ : ℂ)^2) := by
    funext x
    rw [hg, Complex.ofReal_exp]
    push_cast
    rfl
  ext y
  rw [complexTateFourier_apply, SchwartzMap.fourierInv_coe, Real.fourierInv_eq_fourier_neg, h]
  have hb : 0 < (2 * (Real.pi : ℂ)).re := by
    rw [← Complex.ofReal_ofNat, ← Complex.ofReal_mul, Complex.ofReal_re]
    positivity
  rw [fourier_gaussian_innerProductSpace hb, Complex.finrank_real_complex,
    show ((2 : ℕ) : ℂ) / 2 = 1 by norm_num, Complex.cpow_one]
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hs : (Real.pi : ℂ) / (2 * (Real.pi : ℂ)) = (2 : ℂ)⁻¹ := by
    field_simp
  rw [hs, ← mul_assoc, mul_inv_cancel₀ (by norm_num : (2 : ℂ) ≠ 0), one_mul,
    norm_neg, norm_smul, Complex.norm_conj, show ‖(2 : ℝ)‖ = 2 by norm_num]
  change Complex.exp (-((Real.pi : ℂ)^2) * ((2 * ‖y‖ : ℝ) : ℂ)^2 /
    (2 * (Real.pi : ℂ))) = Complex.exp (-(2 * (Real.pi : ℂ)) * (‖y‖ : ℂ)^2)
  congr 1
  push_cast
  field_simp

private theorem complexTate_lineDeriv (f : E) (m y : ℂ) :
    complexTateFourier (∂_{m} f) y =
      (-(4 * Real.pi * Complex.I) * ((m * y).re : ℂ)) * complexTateFourier f y := by
  rw [complexTateFourier_apply, SchwartzMap.fourierInv_lineDerivOp_eq,
    smul_apply, smul_eq_mul, complexTateFourier_apply]
  let w : ℂ := (2 : ℝ) • conj y
  have ht : (inner ℝ · m).HasTemperateGrowth := by fun_prop
  rw [SchwartzMap.smulLeftCLM_apply_apply ht]
  rw [Complex.real_smul]
  change 2 * (-(2 * Real.pi * Complex.I) * (((inner ℝ w m : ℝ) : ℂ) * _ )) = _
  rw [real_inner_comm m w]
  dsimp only [w]
  rw [complexTateFrequency_inner, Complex.ofReal_mul, Complex.ofReal_ofNat]
  ring

private theorem complexGaussian_fderiv (g : E)
    (hg : ∀ x : ℂ, g x = (Real.pi : ℂ)⁻¹ *
      (Real.exp (-(2 * Real.pi) * ‖x‖ ^ 2) : ℂ)) (x m : ℂ) :
    fderiv ℝ (g : ℂ → ℂ) x m =
      (-(2 * Real.pi) : ℂ) * (m * conj x + x * conj m) * g x := by
  have he : (g : ℂ → ℂ) = fun z ↦ (Real.pi : ℂ)⁻¹ *
      Complex.exp ((-(2 * Real.pi) : ℂ) * (z * conj z)) := by
    funext z
    rw [hg, Complex.ofReal_exp, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    rfl
  have hd := (hasFDerivAt_id (𝕜 := ℝ) x).mul
    (Complex.conjCLE.toContinuousLinearMap.hasFDerivAt (x := x))
  have hD := ((hd.const_mul (-(2 * Real.pi) : ℂ)).cexp).const_mul (Real.pi : ℂ)⁻¹
  have hD' := hD.fderiv
  change fderiv ℝ (fun z : ℂ ↦ (Real.pi : ℂ)⁻¹ *
      Complex.exp ((-(2 * Real.pi) : ℂ) * (z * conj z))) x = _ at hD'
  rw [he, hD']
  change _ = _
  simp only [smul_apply, add_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply,
    smul_eq_mul, Pi.mul_apply, id_eq]
  ring

private theorem complexMonomialGaussian_fderiv (g : E)
    (hg : ∀ x : ℂ, g x = (Real.pi : ℂ)⁻¹ *
      (Real.exp (-(2 * Real.pi) * ‖x‖ ^ 2) : ℂ)) (p q : ℕ) (x m : ℂ) :
    fderiv ℝ (complexMellinMonomial p q g : ℂ → ℂ) x m =
      ((p : ℂ) * x^(p-1) * m * conj x^q +
        x^p * (q : ℂ) * conj x^(q-1) * conj m) * g x +
      (x^p * conj x^q) * ((-(2 * Real.pi) : ℂ) * (m * conj x + x * conj m) * g x) := by
  have h₁ : DifferentiableAt ℝ (fun z : ℂ ↦ z ^ p) x :=
    differentiableAt_fun_id.pow p
  have h₂ : DifferentiableAt ℝ (fun z : ℂ ↦ Complex.conjCLE z ^ q) x :=
    Complex.conjCLE.differentiable.differentiableAt.pow q
  have h₃ : DifferentiableAt ℝ (fun z : ℂ ↦ z^p * Complex.conjCLE z^q) x := h₁.mul h₂
  have he : (complexMellinMonomial p q g : ℂ → ℂ) =
      fun z ↦ (z^p * Complex.conjCLE z^q) * g z := funext fun z ↦ complexMellinMonomial_apply p q g z
  have hc : fderiv ℝ (⇑Complex.conjCLE) x = Complex.conjCLE.toContinuousLinearMap :=
    Complex.conjCLE.toContinuousLinearMap.fderiv
  rw [he, fderiv_fun_mul h₃ g.differentiableAt, add_apply,
    smul_apply, smul_apply, complexGaussian_fderiv g hg,
    fderiv_fun_mul h₁ h₂, add_apply,
    fderiv_fun_pow p differentiableAt_fun_id,
    fderiv_fun_pow q Complex.conjCLE.differentiable.differentiableAt,
    fderiv_fun_id, hc]
  simp only [smul_apply, smul_eq_mul, nsmul_eq_mul,
    ContinuousLinearMap.id_apply, ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply]
  ring

private theorem complexMonomialGaussian_z_step (g : E)
    (hg : ∀ x : ℂ, g x = (Real.pi : ℂ)⁻¹ *
      (Real.exp (-(2 * Real.pi) * ‖x‖ ^ 2) : ℂ)) (n : ℕ) :
    (∂_{(1 : ℂ)} (complexMellinMonomial n 0 g)) +
      Complex.I • (∂_{Complex.I} (complexMellinMonomial n 0 g)) =
      (-(4 * Real.pi) : ℂ) • complexMellinMonomial (n+1) 0 g := by
  ext x
  simp only [add_apply, smul_apply, smul_eq_mul, SchwartzMap.lineDerivOp_apply_eq_fderiv,
    complexMonomialGaussian_fderiv g hg, complexMellinMonomial_apply, pow_zero, Nat.cast_zero,
    map_one, Complex.conj_I, mul_zero, zero_mul, add_zero, mul_one, pow_succ]
  linear_combination ((n : ℂ) * x ^ (n - 1) * g x +
      x ^ n * (-(2 * Real.pi) : ℂ) * (conj x - x) * g x) * Complex.I_mul_I

private theorem complexMonomialGaussian_bar_step (g : E)
    (hg : ∀ x : ℂ, g x = (Real.pi : ℂ)⁻¹ *
      (Real.exp (-(2 * Real.pi) * ‖x‖ ^ 2) : ℂ)) (n : ℕ) :
    (∂_{(1 : ℂ)} (complexMellinMonomial 0 n g)) -
      Complex.I • (∂_{Complex.I} (complexMellinMonomial 0 n g)) =
      (-(4 * Real.pi) : ℂ) • complexMellinMonomial 0 (n+1) g := by
  ext x
  simp only [sub_apply, smul_apply, smul_eq_mul, SchwartzMap.lineDerivOp_apply_eq_fderiv,
    complexMonomialGaussian_fderiv g hg, complexMellinMonomial_apply, pow_zero, Nat.cast_zero,
    map_one, Complex.conj_I, zero_mul, zero_add, one_mul, pow_succ, Complex.star_def]
  linear_combination ((n : ℂ) * conj x ^ (n - 1) * g x -
      conj x ^ n * (-(2 * Real.pi) : ℂ) * (conj x - x) * g x) * Complex.I_mul_I

private theorem complexTateFourier_monomial (g : E)
    (hg : ∀ x : ℂ, g x = (Real.pi : ℂ)⁻¹ *
      (Real.exp (-(2 * Real.pi) * ‖x‖ ^ 2) : ℂ)) (n : ℕ) (y : ℂ) :
    (complexTateFourier (complexMellinMonomial n 0 g) y =
      Complex.I ^ n * (conj y ^ n * g y)) ∧
    (complexTateFourier (complexMellinMonomial 0 n g) y =
      Complex.I ^ n * (y ^ n * g y)) := by
  let c : ℂ := -(4 * Real.pi)
  have hc : c ≠ 0 := neg_ne_zero.mpr
    (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
  let L (m : ℂ) := -(4 * Real.pi * Complex.I) * ((m*y).re : ℂ)
  have hL (m : ℂ) (f : E) :
      complexTateFourier (∂_{m} f) y = L m * complexTateFourier f y :=
    complexTate_lineDeriv f m y
  have hY : (y.re : ℂ) + (y.im : ℂ) * Complex.I = y := Complex.re_add_im y
  have hY' : (y.re : ℂ) - (y.im : ℂ) * Complex.I = conj y := by
    apply Complex.ext <;> simp [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im]
  have hplus : L 1 + Complex.I * L Complex.I = c * (Complex.I * conj y) := by
    dsimp only [L, c]
    rw [one_mul, Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub,
      Complex.ofReal_neg, ← hY']
    ring
  have hminus : L 1 - Complex.I * L Complex.I = c * (Complex.I * y) := by
    dsimp only [L, c]
    rw [one_mul, Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub,
      Complex.ofReal_neg]
    conv_rhs => rw [← hY]
    ring
  induction n with
  | zero =>
    have h0 : complexMellinMonomial 0 0 g = g := by ext x; simp
    simp [h0, complexTateFourier_gaussian g hg]
  | succ n ih =>
    constructor
    · have h := congrArg (fun f : E ↦ complexTateFourier f y)
        (complexMonomialGaussian_z_step g hg n)
      change complexTateFourier (_ + _) y = complexTateFourier (c • _) y at h
      simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul, hL,
        ← mul_assoc (Complex.I), ← add_mul, hplus, mul_assoc c] at h
      have he := mul_left_cancel₀ hc h
      rw [← he, ih.1, pow_succ, pow_succ]
      ring
    · have h := congrArg (fun f : E ↦ complexTateFourier f y)
        (complexMonomialGaussian_bar_step g hg n)
      change complexTateFourier (_ - _) y = complexTateFourier (c • _) y at h
      simp only [map_sub, map_smul, sub_apply, smul_apply, smul_eq_mul, hL,
        ← mul_assoc (Complex.I), ← sub_mul, hminus, mul_assoc c] at h
      have he := mul_left_cancel₀ hc h
      rw [← he, ih.2, pow_succ, pow_succ]
      ring

/-- The normalized complex Euler reference test in angular mode `m`
transforms into the reference test in mode `-m` with phase `I ^ |m|`. -/
theorem exists_complexTateGammaTest_fourier (m : ℤ) :
    ∃ f g : E,
      (∀ c : ℂ, complexArchimedeanZetaContinued complexTamagawaAngularMeasure m f
        =ᶠ[𝓝[≠] c] fun z ↦ Complex.Gammaℂ (z + (m.natAbs : ℂ) / 2)) ∧
      (∀ c : ℂ, complexArchimedeanZetaContinued complexTamagawaAngularMeasure (-m) g
        =ᶠ[𝓝[≠] c] fun z ↦ Complex.Gammaℂ (z + (m.natAbs : ℂ) / 2)) ∧
      complexTateFourier f = Complex.I ^ m.natAbs • g := by
  obtain ⟨f, hf, hZf⟩ := exists_complexGammaTest_explicit m
  obtain ⟨h, hh, hZh⟩ := exists_complexGammaTest_explicit (-m)
  obtain ⟨G, hG⟩ := exists_gaussian_schwartz (E := ℂ) (2 * Real.pi) (by positivity)
  let b := (Real.pi : ℂ)⁻¹ • G
  have hb (x : ℂ) : b x = (Real.pi : ℂ)⁻¹ * (Real.exp (-(2 * Real.pi) * ‖x‖^2) : ℂ) := by
    change (Real.pi : ℂ)⁻¹ * G x = _
    rw [hG]
  have hf' : f = complexMellinMonomial (-m).toNat m.toNat b := by
    ext x
    rw [complexMellinMonomial_apply, hb, hf]
  have hh' : h = complexMellinMonomial m.toNat (-m).toNat b := by
    ext x
    rw [complexMellinMonomial_apply, hb, hh, neg_neg]
  refine ⟨f, h, hZf, (by simpa only [Int.natAbs_neg] using hZh), ?_⟩
  rw [hf', hh']
  ext y
  rcases le_or_gt 0 m with hm | hm
  · have h0 : (-m).toNat = 0 := by omega
    have h1 : m.toNat = m.natAbs := by omega
    rw [h0, h1, (complexTateFourier_monomial b hb m.natAbs y).2]
    simp only [smul_apply, smul_eq_mul, complexMellinMonomial_apply, pow_zero, mul_one]
  · have h0 : m.toNat = 0 := by omega
    have h1 : (-m).toNat = m.natAbs := by omega
    rw [h0, h1, (complexTateFourier_monomial b hb m.natAbs y).1]
    simp only [smul_apply, smul_eq_mul, complexMellinMonomial_apply, pow_zero, one_mul, Complex.star_def]

private theorem complexTate_fourier_pairing (t : ℂ) (f g : E) :
    (∫ x, f x * complexTateFourier g (t * x)) =
      ∫ x, g x * complexTateFourier f (t * x) := by
  let P (x y : ℂ) := Complex.exp (↑(2 * Real.pi * (2 * (y * (t*x)).re)) * Complex.I)
  let H (p : ℂ × ℂ) := f p.1 * g p.2 * P p.1 p.2
  have hc : Continuous H := by dsimp only [H, P]; fun_prop
  have hH : Integrable H (volume.prod volume) := by
    apply (f.integrable.norm.mul_prod g.integrable.norm).mono' hc.aestronglyMeasurable
    exact .of_forall fun p ↦ by
      change ‖f p.1 * g p.2 * P p.1 p.2‖ ≤ _
      have hp : ‖P p.1 p.2‖ = 1 := by simp [P, Complex.norm_exp, Complex.mul_re]
      rw [norm_mul, norm_mul, hp, mul_one]
  have he (x y : ℂ) : P x y = P y x := by
    unfold P
    rw [show y * (t*x) = x * (t*y) by ring]
  calc
    _ = 2 * ∫ x, ∫ y, H (x,y) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact .of_forall fun x ↦ by
        change f x * complexTateFourier g (t*x) = 2 * ∫ y, H (x,y)
        rw [complexTateFourier_eq_integral, mul_left_comm, ← integral_const_mul]
        congr 1
        apply integral_congr_ae
        exact .of_forall fun y ↦ (mul_assoc _ _ _).symm
    _ = 2 * ∫ y, ∫ x, H (x,y) := congrArg (2 * ·) (integral_integral_swap hH)
    _ = _ := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact .of_forall fun y ↦ by
        change (2 * ∫ x, H (x,y)) = g y * complexTateFourier f (t*y)
        rw [complexTateFourier_eq_integral]
        have h : (∫ x, H (x,y)) = g y * ∫ x, f x * P y x := by
          rw [← integral_const_mul]
          apply integral_congr_ae
          exact .of_forall fun x ↦ by
            change f x * g y * P x y = g y * (f x * P y x)
            rw [he, mul_comm (f x), mul_assoc]
        rw [h]
        ring

private def complexTateModulus : ℂˣ →* ℝ where
  toFun u := ‖u.val‖ ^ 2
  map_one' := by simp
  map_mul' a b := by rw [Units.val_mul, norm_mul, mul_pow]

private theorem complexTate_map_volume (u : ℂˣ) :
    Measure.map (fun x : ℂ ↦ u.val * x) volume =
      (ENNReal.ofReal (complexTateModulus u))⁻¹ • (volume : Measure ℂ) := by
  let r := ‖u.val‖
  have hr : 0 < r := norm_pos_iff.mpr u.ne_zero
  let a : Circle := ⟨u.val / (r : ℂ), by
    apply mem_sphere_zero_iff_norm.mpr
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hr.le, div_self hr.ne']⟩
  have he : (fun x : ℂ ↦ u.val * x) = (r • ·) ∘ rotation a := by
    funext x
    change u.val * x = (r : ℂ) * ((u.val / (r : ℂ)) * x)
    rw [← mul_assoc, mul_comm (r : ℂ), div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr hr.ne')]
  rw [he, ← Measure.map_map (measurable_const_smul r) (rotation a).continuous.measurable,
    (rotation a).measurePreserving.map_eq, Measure.map_addHaar_smul volume hr.ne',
    Complex.finrank_real_complex, abs_of_nonneg (inv_nonneg.mpr (sq_nonneg r)),
    ENNReal.ofReal_inv_of_pos (sq_pos_of_pos hr)]
  rfl

variable [MeasurableSpace ℂˣ] [BorelSpace ℂˣ]
attribute [local instance] complexZeta_circleMeasurable

private abbrev μ := (complexArchMultiplicativeHaar : Measure ℂˣ)
private abbrev Z := complexArchimedeanZetaContinued complexTamagawaAngularMeasure

private theorem complexTate_weightedHaar :
    ∃ c : ℝ≥0, c ≠ 0 ∧ Measure.map (Units.val : ℂˣ → ℂ)
      (μ.withDensity fun u ↦ ENNReal.ofReal (complexTateModulus u)) =
      c • (volume : Measure ℂ) := by
  let j : ℂˣ → ℂ := Units.val
  have hj : IsOpenEmbedding j := IsOpenUnits.isOpenEmbedding_unitsVal
  letI := hj.locallyCompactSpace
  letI := hj.isEmbedding.secondCountableTopology
  have hfull : ∀ᵐ x : ℂ ∂volume, x ∈ range j := by
    apply ae_iff.mpr
    have hs : {x | ¬ x ∈ range j} = ({0} : Set ℂ) := by
      ext x
      exact not_congr (show IsUnit x ↔ _ from isUnit_iff_ne_zero) |>.trans not_ne_iff
    rw [hs, measure_singleton]
  exact additiveMeasure_eq_weighted_unitHaar (volume : Measure ℂ)
    (fun h ↦ isOpen_univ.measure_ne_zero (volume : Measure ℂ) univ_nonempty (by simp [h]))
    μ hj hfull complexTateModulus (Units.continuous_val.norm.pow 2)
    (fun u ↦ sq_pos_of_pos (norm_pos_iff.mpr u.ne_zero)) complexTate_map_volume

private theorem complexTate_integral_weighted (c : ℝ≥0)
    (hc : Measure.map (Units.val : ℂˣ → ℂ)
        (μ.withDensity fun u ↦ ENNReal.ofReal (complexTateModulus u)) =
        c • (volume : Measure ℂ)) (h : ℂ → ℂ) (hh : Continuous h) :
    (∫ u, (complexTateModulus u : ℂ) * h u.val ∂μ) = c • ∫ x, h x := by
  rw [← integral_smul_nnreal_measure, ← hc,
    integral_map Units.continuous_val.measurable.aemeasurable hh.aestronglyMeasurable]
  let w (u : ℂˣ) : ℝ≥0 := ‖u.val‖₊ ^ 2
  have he : (fun u ↦ ENNReal.ofReal (complexTateModulus u)) =
      fun u ↦ (w u : ℝ≥0∞) := funext fun u ↦ by
    change ENNReal.ofReal (‖u.val‖ ^ 2) = _
    rw [← ENNReal.ofReal_coe_nnreal (p := w u)]
    simp only [w, NNReal.coe_pow, coe_nnnorm]
  have hw : Measurable w := ((continuous_nnnorm.comp Units.continuous_val).pow 2).measurable
  rw [he, integral_withDensity_eq_integral_smul hw]
  rfl

/-- Multiplying the complex Tamagawa Haar measure by the squared modulus
gives twice planar Lebesgue measure in the additive coordinate. -/
theorem complexArchHaar_weighted_map :
    Measure.map (Units.val : ℂˣ → ℂ)
      (μ.withDensity fun u ↦ ENNReal.ofReal (‖u.val‖ ^ 2)) = (2 : ℝ≥0) • volume := by
  obtain ⟨c, _, hc⟩ := complexTate_weightedHaar
  obtain ⟨g, hg⟩ := exists_gaussian_schwartz (E := ℂ) (2 * Real.pi) (by positivity)
  let h (z : ℂ) := Real.exp (-(2 * Real.pi) * ‖z‖ ^ 2)
  have hi : Integrable h := by
    have hRe := Complex.reCLM.integrable_comp (g.integrable (μ := volume))
    exact hRe.congr (.of_forall fun z ↦ by
      change (g z).re = h z
      rw [hg]
      rfl)
  have hI : (∫ z : ℂ, g z) ≠ 0 := by
    simp_rw [hg]
    rw [integral_complex_ofReal]
    exact Complex.ofReal_ne_zero.mpr (integral_exp_pos hi).ne'
  have hZ : (∫ u : ℂˣ, (complexTateModulus u : ℂ) * g u.val ∂μ) =
      (2 : ℝ≥0) • ∫ z : ℂ, g z := by
    calc
      _ = Z 0 g 1 := by
        simpa [complexTateModulus] using
          (complexArchimedeanZetaContinued_eq_unitIntegral 0 g (s := 1) (by simp)).2.symm
      _ = _ := by
        change complexArchimedeanZetaContinued complexTamagawaAngularMeasure 0 g 1 = _
        rw [(complexArchimedeanZetaContinued_eq_tamagawaIntegral 0 g (s := 1) (by simp)).2]
        let D (z : ℂ) := 2 / ‖z‖ ^ 2
        change (∫ z, ((‖z‖ ^ 2 : ℝ) : ℂ) ^ (1 : ℂ) * ((z / (‖z‖ : ℂ)) ^ (0 : ℤ) * g z)
          ∂volume.withDensity (fun z ↦ ENNReal.ofReal (D z))) = _
        have hm : Measurable D := by dsimp only [D]; fun_prop
        rw [integral_withDensity_eq_integral_toReal_smul hm.ennreal_ofReal
          (.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
        change _ = (2 : ℝ) • ∫ z : ℂ, g z
        rw [← integral_smul]
        apply integral_congr_ae
        have hne : ∀ᵐ z : ℂ ∂volume, z ≠ 0 := by rw [ae_iff]; simp
        filter_upwards [hne] with z hz
        have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
        simp only [D, ENNReal.toReal_ofReal (show 0 ≤ 2 / ‖z‖ ^ 2 by positivity),
          Complex.cpow_one, zpow_zero, one_mul, Complex.real_smul, Complex.ofReal_div,
          Complex.ofReal_ofNat, Complex.ofReal_pow]
        have hn' : (‖z‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hn
        field_simp
  have he := (complexTate_integral_weighted c hc g g.continuous).symm.trans hZ
  have hc₂ : c = 2 := by
    apply NNReal.eq
    apply Complex.ofReal_injective
    apply mul_right_cancel₀ hI
    simpa only [NNReal.smul_def, Complex.real_smul] using he
  rw [hc₂] at hc
  exact hc

private def complexTateAngle (u : ℂˣ) : ℂ := u.val / (‖u.val‖ : ℂ)

private def complexTateWeight (m : ℤ) (z : ℂ) : ℂˣ →* ℂ where
  toFun u := Complex.exp (z * (Real.log (complexTateModulus u) : ℂ)) * complexTateAngle u ^ m
  map_one' := by simp [complexTateAngle]
  map_mul' u v := by
    have hn (a : ℂˣ) : complexTateModulus a ≠ 0 :=
      pow_ne_zero 2 (norm_ne_zero_iff.mpr a.ne_zero)
    rw [map_mul, Real.log_mul (hn u) (hn v), Complex.ofReal_add, mul_add, Complex.exp_add]
    have h : complexTateAngle (u*v) = complexTateAngle u * complexTateAngle v := by
      unfold complexTateAngle
      rw [Units.val_mul, norm_mul, Complex.ofReal_mul, mul_div_mul_comm]
    rw [h, mul_zpow]
    ring

private theorem complexTate_weight_integral (m : ℤ) (z : ℂ) (hz : 0 < z.re) (f : E) :
    Integrable (fun u ↦ complexTateWeight m z u * f u.val) μ ∧
      Z m f z = ∫ u, complexTateWeight m z u * f u.val ∂μ := by
  have he (u : ℂˣ) : complexTateWeight m z u =
      ((‖u.val‖ ^ 2 : ℝ) : ℂ)^z * complexTateAngle u^m := by
    change Complex.exp (z * (Real.log (‖u.val‖ ^ 2) : ℂ)) * _ = _
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr
        (pow_ne_zero 2 (norm_ne_zero_iff.mpr u.ne_zero))),
      ← Complex.ofReal_log (sq_nonneg _), mul_comm (↑(Real.log (‖u.val‖ ^ 2)) : ℂ) z]
  simpa only [he, complexTateAngle] using complexArchimedeanZetaContinued_eq_unitIntegral m f hz

private theorem complexTate_cross (m : ℤ) (z : ℂ) (hz : 0 < z.re) (hr : z.re < 1)
    (f g : E) :
    Z m f z * Z (-m) (complexTateFourier g) (1-z) =
      Z m g z * Z (-m) (complexTateFourier f) (1-z) := by
  let j : ℂˣ → ℂ := Units.val
  have hj : IsOpenEmbedding j := IsOpenUnits.isOpenEmbedding_unitsVal
  letI := hj.locallyCompactSpace
  letI := hj.isEmbedding.secondCountableTopology
  let χ := (complexTateWeight (-m) (1-z)).toHomUnits
  let r (h : E) (u : ℂˣ) := (complexTateModulus u : ℂ) * h u.val
  let l (h : E) (u : ℂˣ) := complexTateFourier h u.val
  have hR (h : E) : (fun u ↦ ((χ u : ℂ)⁻¹) * r h u) =
      fun u ↦ complexTateWeight m z u * h u.val := by
    funext u
    let d := complexTateModulus u
    change (Complex.exp ((1-z) * (Real.log d : ℂ)) * complexTateAngle u ^ (-m))⁻¹ *
      ((d : ℂ) * h u.val) = (Complex.exp (z * (Real.log d : ℂ)) * complexTateAngle u ^ m) * h u.val
    have he : (d : ℂ) = Complex.exp (Real.log d : ℂ) := by
      have hd : 0 < d := sq_pos_of_pos (norm_pos_iff.mpr u.ne_zero)
      rw [← Complex.ofReal_exp, Real.exp_log hd]
    rw [he, mul_inv, zpow_neg, inv_inv, ← Complex.exp_neg]
    calc
      _ = (Complex.exp (-((1-z) * (Real.log d : ℂ))) *
          Complex.exp (Real.log d : ℂ)) * complexTateAngle u ^ m * h u.val := by ring
      _ = _ := by rw [← Complex.exp_add]; congr 3; ring
  have hs : 0 < (1-z).re := by simpa [Complex.sub_re, sub_pos] using hr
  obtain ⟨c, _, hc⟩ := complexTate_weightedHaar
  have hp (u : ℂˣ) (b d : E) :
      (∫ x, r b x * l d (u*x) ∂μ) = c • ∫ x, b x * complexTateFourier d (u.val*x) := by
    let H (x : ℂ) := b x * complexTateFourier d (u.val*x)
    have hH : Continuous H := b.continuous.mul ((complexTateFourier d).continuous.comp
      (continuous_const.mul continuous_id))
    calc
      _ = ∫ x, (complexTateModulus x : ℂ) * H x.val ∂μ :=
        integral_congr_ae (.of_forall fun _ ↦ mul_assoc _ _ _)
      _ = _ := complexTate_integral_weighted c hc H hH
  have hPair (u : ℂˣ) : (∫ x, r f x * l g (u*x) ∂μ) = ∫ x, r g x * l f (u*x) ∂μ := by
    rw [hp, hp, complexTate_fourier_pairing]
  have hf : Integrable (fun u ↦ ((χ u : ℂ)⁻¹) * r f u) μ := by
    rw [hR f]
    exact (complexTate_weight_integral m z hz f).1
  have hg : Integrable (fun u ↦ ((χ u : ℂ)⁻¹) * r g u) μ := by
    rw [hR g]
    exact (complexTate_weight_integral m z hz g).1
  have h := mellin_fourier_crossProduct μ χ (r f) (r g) (l f) (l g) hf hg
    (complexTate_weight_integral (-m) (1-z) hs (complexTateFourier f)).1
    (complexTate_weight_integral (-m) (1-z) hs (complexTateFourier g)).1 hPair
  rw [hR f, hR g, ← (complexTate_weight_integral m z hz f).2,
    ← (complexTate_weight_integral m z hz g).2] at h
  change Z m f z * (∫ u, complexTateWeight (-m) (1-z) u * complexTateFourier g u.val ∂μ) =
    Z m g z * (∫ u, complexTateWeight (-m) (1-z) u * complexTateFourier f u.val ∂μ) at h
  rw [← (complexTate_weight_integral (-m) (1-z) hs (complexTateFourier g)).2,
    ← (complexTate_weight_integral (-m) (1-z) hs (complexTateFourier f)).2] at h
  exact h

omit [MeasurableSpace ℂˣ] [BorelSpace ℂˣ] in
private theorem complexTate_gamma_ne_zero (m : ℤ) (z : ℂ) (hz : 0 < z.re) :
    Complex.Gammaℂ (z + (m.natAbs : ℂ) / 2) ≠ 0 := by
  rw [Complex.Gammaℂ_def]
  apply mul_ne_zero (mul_ne_zero (by norm_num) (Complex.cpow_ne_zero_iff.mpr
    (Or.inl (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)))))
  apply Complex.Gamma_ne_zero_of_re_pos
  rw [Complex.add_re, Complex.div_ofNat_re, Complex.natCast_re]
  positivity

/-- The normalized complex local Tate equation on the critical strip
with the adelic trace convention and the epsilon constant `(-I)^|m|`. -/
theorem complexTate_normalized_fourier (m : ℤ) (z : ℂ)
    (hz : 0 < z.re) (hr : z.re < 1) (f : E) :
    complexArchZetaDenominator m z * Z m f z =
      (-Complex.I) ^ m.natAbs *
        (complexArchZetaDenominator (-m) (1-z) * Z (-m) (complexTateFourier f) (1-z)) := by
  obtain ⟨g, g', hg, hg', hFg⟩ := exists_complexTateGammaTest_fourier m
  have hG (n : ℤ) (a : E)
      (h : ∀ c : ℂ, Z n a =ᶠ[𝓝[≠] c] fun w ↦ Complex.Gammaℂ (w + (n.natAbs : ℂ) / 2))
      (w : ℂ) (hw : 0 < w.re) : complexArchZetaDenominator n w * Z n a w = 1 := by
    let A (s : ℂ) := Complex.Gammaℂ (s + (n.natAbs : ℂ) / 2)
    have hA : A w ≠ 0 := complexTate_gamma_ne_zero n w hw
    have hAc : ContinuousAt A w := by
      have hh := (complexArchZetaDenominator_analytic n w).inv (inv_ne_zero hA)
      simpa only [complexArchZetaDenominator, Pi.inv_def, inv_inv, A] using hh.continuousAt
    have hZc : ContinuousAt (Z n a) w :=
      (complexArchimedeanZetaContinued_analyticAt complexTamagawaAngularMeasure n a (fun k hh ↦ by
        have hreal := congrArg Complex.re hh
        norm_num [Complex.add_re, Complex.mul_re] at hreal
        linarith [Nat.cast_nonneg (α := ℝ) k])).continuousAt
    have hEq : Z n a w = A w :=
      ((hZc.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE hAc).mp (h w)).eq_of_nhds
    change (A w)⁻¹ * Z n a w = 1
    rw [hEq, inv_mul_cancel₀ hA]
  let L (h : E) := complexArchZetaDenominator m z * Z m h z
  let R (h : E) := complexArchZetaDenominator (-m) (1-z) * Z (-m) (complexTateFourier h) (1-z)
  have hs : 0 < (1-z).re := by simpa [Complex.sub_re, sub_pos] using hr
  have hLg : L g = 1 := hG m g hg z hz
  have hRg : R g = Complex.I ^ m.natAbs := by
    change complexArchZetaDenominator (-m) (1-z) *
      complexArchimedeanZetaContinued complexTamagawaAngularMeasure (-m)
        (complexTateFourier g) (1-z) = _
    rw [hFg, ← complexArchimedeanZetaContinuedCLM_apply, map_smul, smul_eq_mul,
      complexArchimedeanZetaContinuedCLM_apply, mul_left_comm]
    change _ * (complexArchZetaDenominator (-m) (1-z) * Z (-m) g' (1-z)) = _
    rw [hG (-m) g' (by simpa only [Int.natAbs_neg] using hg') _ hs, mul_one]
  have hCross : L f * R g = L g * R f := by
    have h := complexTate_cross m z hz hr f g
    dsimp only [L, R]
    linear_combination (complexArchZetaDenominator m z * complexArchZetaDenominator (-m) (1-z)) * h
  change L f = (-Complex.I) ^ m.natAbs * R f
  rw [hLg, hRg, one_mul] at hCross
  calc
    _ = ((-Complex.I)^m.natAbs * Complex.I^m.natAbs) * L f := by
      rw [← mul_pow, neg_mul, Complex.I_mul_I, neg_neg, one_pow, one_mul]
    _ = _ := by rw [mul_assoc, mul_comm (Complex.I^m.natAbs), hCross]

/-- The complex local equation with the explicit Gamma ratio as a
meromorphic identity, including punctured germs at the poles. -/
theorem complexTate_fourier_meromorphic (m : ℤ) (f : E) (c : ℂ) :
    Z m f =ᶠ[𝓝[≠] c] fun z ↦ (-Complex.I) ^ m.natAbs *
      (complexArchZetaDenominator (-m) (1-z) / complexArchZetaDenominator m z) *
        Z (-m) (complexTateFourier f) (1-z) := by
  let ε : ℂ := (-Complex.I) ^ m.natAbs
  let D := complexArchZetaDenominator m
  let D' := complexArchZetaDenominator (-m)
  have hR : Meromorphic (fun z ↦ Z (-m) (complexTateFourier f) (1-z)) := fun z ↦
    (complexArchimedeanZetaContinued_meromorphic complexTamagawaAngularMeasure (-m)
      (complexTateFourier f) (1-z)).comp_analyticAt (analyticAt_const.fun_sub analyticAt_id)
  have hD : Meromorphic (fun z ↦ D' (1-z) / D z) := fun z ↦
    ((complexArchZetaDenominator_analytic (-m) (1-z)).comp
      (analyticAt_const.fun_sub analyticAt_id)).meromorphicAt.div
        (complexArchZetaDenominator_analytic m z).meromorphicAt
  refine boundedPoleMellinSpace_unique_germs (D := {z : ℂ | 0 < z.re ∧ z.re < 1})
    ((isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const))
    ⟨1 / 2, by change 0 < (1 / 2 : ℂ).re ∧ (1 / 2 : ℂ).re < 1
               norm_num [Complex.div_ofNat_re]⟩
    (complexArchimedeanZetaContinued_meromorphic complexTamagawaAngularMeasure m f)
    (fun z ↦ ((MeromorphicAt.const ε z).mul (hD z)).mul (hR z)) ?_ c
  intro z hz
  change Z m f z = ε * (D' (1-z) / D z) * Z (-m) (complexTateFourier f) (1-z)
  have hD₀ : D z ≠ 0 := inv_ne_zero (complexTate_gamma_ne_zero m z hz.1)
  apply mul_left_cancel₀ hD₀
  calc
    _ = ε * (D' (1-z) * Z (-m) (complexTateFourier f) (1-z)) :=
      complexTate_normalized_fourier m z hz.1 hz.2 f
    _ = _ := by field_simp

end

end Masullo
