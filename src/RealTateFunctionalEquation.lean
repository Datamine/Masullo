import ArchimedeanGammaTests
import ArchimedeanMultiplicativeHaar
import UnitHaarDensity
import MellinFourierCrossProduct
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

open Filter Function MeasureTheory Set Topology FourierTransform
open scoped SchwartzMap ENNReal NNReal

namespace Masullo

noncomputable section

private abbrev E := 𝓢(ℝ, ℂ)
private abbrev Z := realArchimedeanZetaContinued

private theorem realGaussian_fourier (g : E)
    (hg : ∀ x : ℝ, g x = (Real.exp (-Real.pi * ‖x‖ ^ 2) : ℂ)) : 𝓕 g = g := by
  have h : (g : ℝ → ℂ) = fun x : ℝ ↦ Complex.exp (-(Real.pi : ℂ) * (x : ℂ)^2) := by
    funext x
    rw [hg, Real.norm_eq_abs, sq_abs, Complex.ofReal_exp]
    push_cast
    rfl
  ext y
  rw [SchwartzMap.fourier_coe, h]
  have h' := congrFun (fourier_gaussian_pi (b := (1 : ℂ)) (by norm_num)) y
  simpa only [mul_one, Complex.one_cpow, div_one, one_mul, h] using h'

private theorem realGaussian_odd_fourier (g : E)
    (hg : ∀ x : ℝ, g x = (Real.exp (-Real.pi * ‖x‖ ^ 2) : ℂ)) :
    𝓕 (realMellinMonomial 1 g) = (-Complex.I) • realMellinMonomial 1 g := by
  let h := realMellinMonomial 1 g
  let c : ℂ := -2 * Real.pi
  have hd (x : ℝ) : deriv (g : ℝ → ℂ) x = c * h x := by
    have he : (g : ℝ → ℂ) = fun t : ℝ ↦ (Real.exp (-Real.pi * t ^ 2) : ℂ) := by
      funext t
      rw [hg, Real.norm_eq_abs, sq_abs]
    rw [he]
    have hfun := (((hasDerivAt_id x).pow 2).const_mul (-Real.pi)).exp.ofReal_comp
    simp only [Pi.pow_apply, id_eq] at hfun
    rw [hfun.deriv]
    rw [show h x = (x : ℂ) * g x by dsimp only [h]; rw [realMellinMonomial_apply, pow_one], hg,
      Real.norm_eq_abs, sq_abs]
    dsimp only [c]
    push_cast
    ring
  have he : deriv (g : ℝ → ℂ) = ((c • h : E) : ℝ → ℂ) := by
    funext x
    exact hd x
  have hF := Real.fourier_deriv g.integrable g.differentiable
    (he.symm ▸ (c • h).integrable)
  have hc : c ≠ 0 := by
    dsimp [c]
    exact mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  ext y
  have hF' := congrFun hF y
  rw [he, ← SchwartzMap.fourier_coe, ← SchwartzMap.fourier_coe,
    FourierTransform.fourier_smul, realGaussian_fourier g hg] at hF'
  change c * (𝓕 h) y = (2 * Real.pi * Complex.I * y) * g y at hF'
  change (𝓕 h) y = -Complex.I * h y
  apply mul_left_cancel₀ hc
  rw [hF', show h y = (y : ℂ) * g y by dsimp only [h]; rw [realMellinMonomial_apply, pow_one]]
  dsimp only [c]
  ring

/-- The Gaussian Euler reference test is an eigenvector for the positive
Fourier kernel used by the adelic convention. -/
theorem exists_realTateGammaTest_fourier (a : ℕ) :
    ∃ f : E,
      (∀ c : ℂ, Z a f =ᶠ[𝓝[≠] c]
        fun z ↦ Complex.Gammaℝ (z + ((a % 2 : ℕ) : ℂ))) ∧
      𝓕⁻ f = (Complex.I ^ (a % 2)) • f := by
  obtain ⟨f, hf, hZ⟩ := exists_realGammaTest_explicit a
  obtain ⟨g, hg⟩ := exists_gaussian_schwartz (E := ℝ) Real.pi Real.pi_pos
  refine ⟨f, hZ, ?_⟩
  have hn : a % 2 = 0 ∨ a % 2 = 1 := by omega
  rcases hn with hn | hn
  · have he : f = g := by ext x; rw [hf, hn, pow_zero, one_mul, hg]
    rw [he, hn, pow_zero, one_smul, SchwartzMap.fourierInv_apply_eq, realGaussian_fourier g hg]
    ext x
    change g (-x) = g x
    rw [hg, hg, norm_neg]
  · have he : f = realMellinMonomial 1 g := by
      ext x
      rw [hf, hn, realMellinMonomial_apply, hg]
    rw [he, hn, pow_one, SchwartzMap.fourierInv_apply_eq, realGaussian_odd_fourier g hg]
    ext x
    change (-Complex.I) * realMellinMonomial 1 g (-x) = Complex.I * realMellinMonomial 1 g x
    rw [realMellinMonomial_apply, realMellinMonomial_apply, hg, hg, norm_neg, Complex.ofReal_neg]
    ring

private theorem realTate_fourier_pairing (t : ℝ) (f g : E) :
    (∫ x, f x * (𝓕⁻ g) (t * x)) = ∫ x, g x * (𝓕⁻ f) (t * x) := by
  let P (x y : ℝ) := Complex.exp (↑(2 * Real.pi * (y * (t*x))) * Complex.I)
  let H (p : ℝ × ℝ) := f p.1 * g p.2 * P p.1 p.2
  have hc : Continuous H := by
    dsimp only [H, P]
    fun_prop
  have hH : Integrable H (volume.prod volume) := by
    apply (f.integrable.norm.mul_prod g.integrable.norm).mono' hc.aestronglyMeasurable
    exact .of_forall fun p ↦ by
      change ‖f p.1 * g p.2 * P p.1 p.2‖ ≤ _
      have hp : ‖P p.1 p.2‖ = 1 := by
        simp [P, Complex.norm_exp, Complex.mul_re]
      rw [norm_mul, norm_mul, hp, mul_one]
  have he (x y : ℝ) : P x y = P y x := by
    unfold P
    rw [show y * (t*x) = x * (t*y) by ring]
  have hF (h : E) (x : ℝ) : (𝓕⁻ h) (t*x) = ∫ y, h y * P x y := by
    rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq']
    apply integral_congr_ae
    exact .of_forall fun y ↦ by
      change Complex.exp (↑(2 * Real.pi * ((t*x) * y)) * Complex.I) * h y = h y * P x y
      dsimp only [P]
      rw [mul_comm (t*x) y, mul_comm]
  calc
    _ = ∫ x, ∫ y, H (x,y) := by
      apply integral_congr_ae
      exact .of_forall fun x ↦ by
        change f x * (𝓕⁻ g) (t * x) = ∫ y, H (x,y)
        rw [hF, ← integral_const_mul]
        apply integral_congr_ae
        exact .of_forall fun y ↦ (mul_assoc _ _ _).symm
    _ = ∫ y, ∫ x, H (x,y) := integral_integral_swap hH
    _ = _ := by
      apply integral_congr_ae
      exact .of_forall fun y ↦ by
        change (∫ x, H (x,y)) = g y * (𝓕⁻ f) (t * y)
        rw [hF, ← integral_const_mul]
        apply integral_congr_ae
        exact .of_forall fun x ↦ by
          change f x * g y * P x y = g y * (f x * P y x)
          rw [he, mul_comm (f x), mul_assoc]

variable [MeasurableSpace ℝˣ] [BorelSpace ℝˣ]

private abbrev μ := (realArchMultiplicativeHaar : Measure ℝˣ)

private theorem realTate_weightedHaar :
    ∃ c : ℝ≥0, c ≠ 0 ∧
      Measure.map (Units.val : ℝˣ → ℝ)
        (μ.withDensity fun u ↦ ENNReal.ofReal |u.val|) = c • (volume : Measure ℝ) := by
  let j : ℝˣ → ℝ := Units.val
  have hj : IsOpenEmbedding j := IsOpenUnits.isOpenEmbedding_unitsVal
  letI := hj.locallyCompactSpace
  letI := hj.isEmbedding.secondCountableTopology
  let d : ℝˣ →* ℝ := normHom.toMonoidHom.comp (Units.coeHom ℝ)
  have hfull : ∀ᵐ x : ℝ ∂volume, x ∈ range j := by
    apply ae_iff.mpr
    have hs : {x | ¬ x ∈ range j} = ({0} : Set ℝ) := by
      ext x
      exact not_congr (show IsUnit x ↔ _ from isUnit_iff_ne_zero) |>.trans not_ne_iff
    rw [hs, measure_singleton]
  refine additiveMeasure_eq_weighted_unitHaar (volume : Measure ℝ)
    (fun h ↦ isOpen_univ.measure_ne_zero (volume : Measure ℝ)
      univ_nonempty (by simp [h]))
    μ hj hfull d (continuous_norm.comp Units.continuous_val)
    (fun u ↦ norm_pos_iff.mpr u.ne_zero) ?_
  intro u
  rw [Real.map_volume_mul_left u.ne_zero, abs_inv,
    ENNReal.ofReal_inv_of_pos (abs_pos.mpr u.ne_zero)]
  change _ = (ENNReal.ofReal ‖u.val‖)⁻¹ • (volume : Measure ℝ)
  rw [Real.norm_eq_abs]

private theorem realTate_integral_weighted (c : ℝ≥0)
    (hc : Measure.map (Units.val : ℝˣ → ℝ)
        (μ.withDensity fun u ↦ ENNReal.ofReal |u.val|) = c • (volume : Measure ℝ))
    (h : ℝ → ℂ) (hh : Continuous h) :
    (∫ u, ((|u.val| : ℝ) : ℂ) * h u.val ∂μ) = c • ∫ x, h x := by
  rw [← integral_smul_nnreal_measure, ← hc,
    integral_map Units.continuous_val.measurable.aemeasurable hh.aestronglyMeasurable]
  have he : (fun u : ℝˣ ↦ ENNReal.ofReal |u.val|) =
      fun u ↦ (‖u.val‖₊ : ℝ≥0∞) := funext fun _ ↦ (Real.norm_eq_abs _ ▸ ofReal_norm _)
  rw [he, integral_withDensity_eq_integral_smul
    (f := fun u : ℝˣ ↦ ‖u.val‖₊) (continuous_nnnorm.comp Units.continuous_val).measurable]
  change (∫ u, ((|u.val| : ℝ) : ℂ) * h u.val ∂μ) = ∫ u, (‖u.val‖ : ℝ) • h u.val ∂μ
  simp only [Real.norm_eq_abs, Complex.real_smul]

/-- Multiplying the real Tamagawa Haar measure by the local modulus gives
exactly Lebesgue measure in the additive coordinate. -/
theorem realArchHaar_weighted_map :
    Measure.map (Units.val : ℝˣ → ℝ)
      (μ.withDensity fun u ↦ ENNReal.ofReal ‖u.val‖) = volume := by
  obtain ⟨c, _, hc⟩ := realTate_weightedHaar
  obtain ⟨g, hg⟩ := exists_gaussian_schwartz (E := ℝ) Real.pi Real.pi_pos
  have hI : (∫ x : ℝ, g x) = 1 := by
    simp_rw [hg, Real.norm_eq_abs, sq_abs]
    rw [integral_complex_ofReal, integral_gaussian, div_self Real.pi_ne_zero, Real.sqrt_one,
      Complex.ofReal_one]
  have hZ : (∫ u : ℝˣ, ((|u.val| : ℝ) : ℂ) * g u.val ∂μ) = ∫ x : ℝ, g x := by
    calc
      _ = realArchimedeanZetaContinued 0 g 1 := by
        simpa using (realArchimedeanZetaContinued_eq_unitIntegral 0 g (s := 1) (by simp)).2.symm
      _ = _ := by
        rw [(realArchimedeanZetaContinued_eq_integral 0 g (s := 1) (by simp)).2]
        simp [realArchimedeanZetaIntegral, realArchimedeanZetaIntegrand]
  have h := (realTate_integral_weighted c hc g g.continuous).symm.trans hZ
  rw [hI] at h
  have hc₁ : c = 1 := by
    apply NNReal.eq
    simpa only [NNReal.smul_def, NNReal.coe_one, Complex.real_smul, mul_one, Complex.ofReal_eq_one] using h
  simpa only [Real.norm_eq_abs, hc₁, one_smul] using hc

omit [MeasurableSpace ℝˣ] [BorelSpace ℝˣ] in
private def realTateSign : ℝˣ →* ℂ where
  toFun u := if u.val < 0 then -1 else 1
  map_one' := by norm_num
  map_mul' a b := by
    change (if a.val * b.val < 0 then (-1 : ℂ) else 1) = _
    rcases a.ne_zero.lt_or_gt with ha | ha <;> rcases b.ne_zero.lt_or_gt with hb | hb
    · simp [ha, hb, (mul_pos_of_neg_of_neg ha hb).not_gt]
    · simp [ha, hb.not_gt, mul_neg_of_neg_of_pos ha hb]
    · simp [ha.not_gt, hb, mul_neg_of_pos_of_neg ha hb]
    · simp [ha.not_gt, hb.not_gt, (mul_pos ha hb).not_gt]

omit [MeasurableSpace ℝˣ] [BorelSpace ℝˣ] in
private def realTateWeight (a : ℕ) (z : ℂ) : ℝˣ →* ℂ where
  toFun u := (realTateSign u)^a * Complex.exp (z * (Real.log |u.val| : ℂ))
  map_one' := by simp
  map_mul' u w := by
    rw [map_mul, mul_pow, Units.val_mul, abs_mul,
      Real.log_mul (abs_ne_zero.mpr u.ne_zero) (abs_ne_zero.mpr w.ne_zero),
      Complex.ofReal_add, mul_add, Complex.exp_add]
    ring

private theorem realTate_weight_integral (a : ℕ) (z : ℂ) (hz : 0 < z.re) (f : E) :
    Integrable (fun u ↦ realTateWeight a z u * f u.val) μ ∧
    Z a f z = ∫ u, realTateWeight a z u * f u.val ∂μ := by
  have he (u : ℝˣ) : realTateWeight a z u =
      ((|u.val| : ℝ) : ℂ)^z * (if u.val < 0 then (-1 : ℂ)^a else 1) := by
    change (realTateSign u)^a * _ = _
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (abs_ne_zero.mpr u.ne_zero)),
      ← Complex.ofReal_log (abs_nonneg _), mul_comm (↑(Real.log |u.val|) : ℂ) z]
    by_cases h : u.val < 0 <;> simp [realTateSign, h, mul_comm]
  simpa only [he] using realArchimedeanZetaContinued_eq_unitIntegral a f hz

private theorem realTate_cross (a : ℕ) (z : ℂ) (hz : 0 < z.re) (hr : z.re < 1)
    (f g : E) :
    Z a f z * Z a (𝓕⁻ g) (1 - z) = Z a g z * Z a (𝓕⁻ f) (1 - z) := by
  let j : ℝˣ → ℝ := Units.val
  have hj : IsOpenEmbedding j := IsOpenUnits.isOpenEmbedding_unitsVal
  letI := hj.locallyCompactSpace
  letI := hj.isEmbedding.secondCountableTopology
  let χ := (realTateWeight a (1 - z)).toHomUnits
  let r (h : E) (u : ℝˣ) := ((|u.val| : ℝ) : ℂ) * h u.val
  let l (h : E) (u : ℝˣ) := (𝓕⁻ h) u.val
  have hR (h : E) : (fun u ↦ ((χ u : ℂ)⁻¹) * r h u) =
      fun u ↦ realTateWeight a z u * h u.val := by
    funext u
    change ((realTateSign u)^a * Complex.exp ((1 - z) * (Real.log |u.val| : ℂ)))⁻¹ *
      (((|u.val| : ℝ) : ℂ) * h u.val) =
      ((realTateSign u)^a * Complex.exp (z * (Real.log |u.val| : ℂ))) * h u.val
    have hs : ((realTateSign u)^a : ℂ)⁻¹ = (realTateSign u)^a := by
      rw [← inv_pow]
      have he : (realTateSign u)⁻¹ = realTateSign u := by
        by_cases h : u.val < 0 <;> simp [realTateSign, h]
      rw [he]
    have he : ((|u.val| : ℝ) : ℂ) = Complex.exp (Real.log |u.val| : ℂ) := by
      rw [← Complex.ofReal_exp, Real.exp_log (abs_pos.mpr u.ne_zero)]
    rw [he, mul_inv, hs, ← Complex.exp_neg]
    calc
      _ = (realTateSign u)^a * (Complex.exp (-((1 - z) * (Real.log |u.val| : ℂ))) *
          Complex.exp (Real.log |u.val| : ℂ)) * h u.val := by ring
      _ = _ := by rw [← Complex.exp_add]; congr 3; ring
  have hs : 0 < (1 - z).re := by simpa [Complex.sub_re, sub_pos] using hr
  obtain ⟨c, _, hc⟩ := realTate_weightedHaar
  have hp (u : ℝˣ) (b d : E) :
      (∫ x, r b x * l d (u*x) ∂μ) =
        c • ∫ x, b x * (𝓕⁻ d) (u.val*x) := by
    let H (x : ℝ) := b x * (𝓕⁻ d) (u.val*x)
    have hH : Continuous H := b.continuous.mul ((𝓕⁻ d).continuous.comp
      (continuous_const.mul continuous_id))
    calc
      _ = ∫ x, ((|x.val| : ℝ) : ℂ) * H x.val ∂μ :=
        integral_congr_ae (.of_forall fun _ ↦ mul_assoc _ _ _)
      _ = _ := realTate_integral_weighted c hc H hH
  have hPair (u : ℝˣ) : (∫ x, r f x * l g (u*x) ∂μ) = ∫ x, r g x * l f (u*x) ∂μ := by
    rw [hp, hp, realTate_fourier_pairing]
  have hf : Integrable (fun u ↦ ((χ u : ℂ)⁻¹) * r f u) μ := by
    rw [hR f]
    exact (realTate_weight_integral a z hz f).1
  have hg : Integrable (fun u ↦ ((χ u : ℂ)⁻¹) * r g u) μ := by
    rw [hR g]
    exact (realTate_weight_integral a z hz g).1
  have h := mellin_fourier_crossProduct μ χ (r f) (r g) (l f) (l g) hf hg
    (realTate_weight_integral a (1-z) hs (𝓕⁻ f)).1
    (realTate_weight_integral a (1-z) hs (𝓕⁻ g)).1 hPair
  rw [hR f, hR g, ← (realTate_weight_integral a z hz f).2,
    ← (realTate_weight_integral a z hz g).2] at h
  change Z a f z * (∫ u, realTateWeight a (1-z) u * (𝓕⁻ g) u.val ∂μ) =
    Z a g z * (∫ u, realTateWeight a (1-z) u * (𝓕⁻ f) u.val ∂μ) at h
  rw [← (realTate_weight_integral a (1-z) hs (𝓕⁻ g)).2,
    ← (realTate_weight_integral a (1-z) hs (𝓕⁻ f)).2] at h
  exact h

/-- The real local Tate equation with the standard positive Fourier
kernel, normalized by the real Gamma factor. -/
theorem realTate_normalized_fourier (a : ℕ) (z : ℂ) (hz : 0 < z.re) (hr : z.re < 1) (f : E) :
    realArchZetaDenominator a z * Z a f z =
      (-Complex.I) ^ (a % 2) *
        (realArchZetaDenominator a (1-z) * Z a (𝓕⁻ f) (1-z)) := by
  obtain ⟨g, hg, hFg⟩ := exists_realTateGammaTest_fourier a
  let D := realArchZetaDenominator a
  let L (h : E) := D z * Z a h z
  let R (h : E) := D (1-z) * Z a (𝓕⁻ h) (1-z)
  have hG (w : ℂ) (hw : 0 < w.re) : D w * Z a g w = 1 := by
    let A (s : ℂ) := Complex.Gammaℝ (s + ((a % 2 : ℕ) : ℂ))
    have hA : A w ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos (by
      simp only [Complex.add_re, Complex.natCast_re]; positivity)
    have hAc : ContinuousAt A w := by
      have h := (realArchZetaDenominator_analytic a w).inv (inv_ne_zero hA)
      simpa only [realArchZetaDenominator, Pi.inv_def, inv_inv, A] using h.continuousAt
    have hZc : ContinuousAt (Z a g) w :=
      (realArchimedeanZetaContinued_analyticAt a g (fun k h ↦ by
        have hreal := congrArg Complex.re h
        simp only [Complex.add_re, Complex.natCast_re, Complex.zero_re] at hreal
        linarith [Nat.cast_nonneg (α := ℝ) k])).continuousAt
    have hEq : Z a g w = A w :=
      ((hZc.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE hAc).mp (hg w)).eq_of_nhds
    change (A w)⁻¹ * Z a g w = 1
    rw [hEq, inv_mul_cancel₀ hA]
  have hs : 0 < (1 - z).re := by simpa [Complex.sub_re, sub_pos] using hr
  have hLg : L g = 1 := hG z hz
  have hRg : R g = Complex.I ^ (a % 2) := by
    change D (1-z) * realArchimedeanZetaContinued a (𝓕⁻ g) (1-z) = _
    rw [hFg, ← realArchimedeanZetaContinuedCLM_apply, map_smul, smul_eq_mul,
      realArchimedeanZetaContinuedCLM_apply, mul_left_comm]
    change _ * (D (1-z) * Z a g (1-z)) = _
    rw [hG _ hs, mul_one]
  have hCross : L f * R g = L g * R f := by
    have h := realTate_cross a z hz hr f g
    dsimp only [L, R]
    linear_combination (D z * D (1-z)) * h
  change L f = (-Complex.I) ^ (a % 2) * R f
  rw [hLg, hRg, one_mul] at hCross
  calc
    _ = ((-Complex.I) ^ (a % 2) * Complex.I ^ (a % 2)) * L f := by
      rw [← mul_pow, neg_mul, Complex.I_mul_I, neg_neg, one_pow, one_mul]
    _ = _ := by rw [mul_assoc, mul_comm (Complex.I ^ (a % 2)), hCross]

omit [MeasurableSpace ℝˣ] [BorelSpace ℝˣ] in
/-- The unnormalized real factor is the parity epsilon constant times the
reflected real Gamma ratio. The identity extends as germs at every pole. -/
theorem realTate_fourier_meromorphic [MeasurableSpace ℝˣ] [BorelSpace ℝˣ]
    (a : ℕ) (f : E) (c : ℂ) :
    Z a f =ᶠ[𝓝[≠] c] fun z ↦ (-Complex.I) ^ (a % 2) *
      (realArchZetaDenominator a (1-z) / realArchZetaDenominator a z) *
        Z a (𝓕⁻ f) (1-z) := by
  let ε : ℂ := (-Complex.I) ^ (a % 2)
  let D := realArchZetaDenominator a
  have hR : Meromorphic (fun z ↦ Z a (𝓕⁻ f) (1 - z)) := fun z ↦
    (realArchimedeanZetaContinued_meromorphic a (𝓕⁻ f) (1-z)).comp_analyticAt
      (analyticAt_const.fun_sub analyticAt_id)
  have hD : Meromorphic (fun z ↦ D (1-z) / D z) := fun z ↦
    ((realArchZetaDenominator_analytic a (1-z)).comp
      (analyticAt_const.fun_sub analyticAt_id)).meromorphicAt.div
        (realArchZetaDenominator_analytic a z).meromorphicAt
  refine boundedPoleMellinSpace_unique_germs (D := {z : ℂ | 0 < z.re ∧ z.re < 1})
    ((isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const))
    ⟨1 / 2, by change 0 < (1 / 2 : ℂ).re ∧ (1 / 2 : ℂ).re < 1
               norm_num [Complex.div_ofNat_re]⟩
    (realArchimedeanZetaContinued_meromorphic a f)
    (fun z ↦ ((MeromorphicAt.const ε z).mul (hD z)).mul (hR z)) ?_ c
  intro z hz
  change Z a f z = ε * (D (1-z) / D z) * Z a (𝓕⁻ f) (1-z)
  have hD₀ : D z ≠ 0 := inv_ne_zero (Complex.Gammaℝ_ne_zero_of_re_pos (by
    simp only [Complex.add_re, Complex.natCast_re]; exact add_pos_of_pos_of_nonneg hz.1 (by positivity)))
  apply mul_left_cancel₀ hD₀
  calc
    _ = ε * (D (1-z) * Z a (𝓕⁻ f) (1-z)) := realTate_normalized_fourier a z hz.1 hz.2 f
    _ = _ := by field_simp

end

end Masullo
