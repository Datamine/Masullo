import ArchimedeanDigammaIntegral
import ExponentialDecayStructure
import MellinStrip
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne

/-! The local gamma contributions in the explicit formula (Masullo B.4.2.1).
The Fubini argument follows the original Masullo project and Neal Patel.
See External/PROVENANCE.md and the retained licence notices. -/

noncomputable section

open Complex Filter MeasureTheory Set
open scoped SchwartzMap Topology

namespace Masullo

private def ordinate (a y : ℝ) : ℂ := (a : ℂ) + (y : ℂ) * I

/-- Mellin inversion along a vertical line, with integrability of the trace. -/
theorem mellinVerticalTrace (f : ℝ → ℂ) (hw : ∀ a, MellinSchwartzAt f a) (a : ℝ)
    (hf : ∀ t > 0, ContinuousAt f t) :
    let W := fun y ↦ mellin f (ordinate a y)
    Continuous W ∧ Integrable (fun y ↦ ‖W y‖ * (1 + |y|)) ∧
      ∀ x : ℝ, (∫ y : ℝ, W y * exp (-ordinate a y * x)) / (2 * (Real.pi : ℂ)) =
        f (Real.exp x) := by
  intro W
  obtain ⟨g, hg⟩ := exists_mellinVerticalSchwartz (hw a)
  have hgw : (g : ℝ → ℂ) = W := by
    rw [hg]
    ext y
    congr 1
    apply Complex.ext <;> simp [ordinate]
  refine ⟨hgw ▸ g.continuous, ?_, fun x ↦ ?_⟩
  · rw [← hgw]
    apply (g.integrable.norm.add (g.integrable_pow_mul volume 1)).congr
    filter_upwards with y
    simp [Real.norm_eq_abs, add_mul, mul_comm]
  · have hgi : VerticalIntegrable (mellin f) a := by
      change Integrable W
      rw [← hgw]
      exact g.integrable
    have hx := Real.exp_pos x
    have hi := mellinInv_mellin_eq a f hx
      (mellinConvergent_of_schwartzAt (s := (a : ℂ)) (by simpa using hw a)) hgi (hf _ hx)
    have hpow (y : ℝ) : ((Real.exp x : ℝ) : ℂ) ^ (-ordinate a y) =
        exp (-ordinate a y * x) := by
      rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr hx.ne'),
        ← ofReal_log hx.le, Real.log_exp, mul_comm]
    simp only [mellinInv, Complex.real_smul, Complex.ofReal_div, Complex.ofReal_one,
      Complex.ofReal_mul, Complex.ofReal_ofNat, smul_eq_mul] at hi
    change 1 / (2 * (Real.pi : ℂ)) * (∫ y, ((Real.exp x : ℝ) : ℂ) ^ (-ordinate a y) * W y) =
      f (Real.exp x) at hi
    simpa only [hpow, mul_comm (exp _) _, div_eq_inv_mul, one_mul, mul_one] using hi

/-- Mellin inversion of the reflected trace on the right-hand line. -/
theorem mellinVerticalTrace_reflect (f : ℝ → ℂ) (hw : ∀ a, MellinSchwartzAt f a) (a : ℝ)
    (hf : ∀ t > 0, ContinuousAt f t) :
    let W := fun y ↦ mellin f (1 - ordinate a y)
    Continuous W ∧ Integrable (fun y ↦ ‖W y‖ * (1 + |y|)) ∧
      ∀ x : ℝ, (∫ y : ℝ, W y * exp (-ordinate a y * x)) / (2 * (Real.pi : ℂ)) =
        exp (-(x : ℂ)) * f (Real.exp (-x)) := by
  intro W
  let V := fun y ↦ mellin f (ordinate (1 - a) y)
  obtain ⟨hc, hm, hi⟩ := mellinVerticalTrace f hw (1 - a) hf
  have he (y : ℝ) : W y = V (-y) := by
    change mellin f (1 - ordinate a y) = mellin f (ordinate (1 - a) (-y))
    congr 1
    simp only [ordinate, ofReal_sub, ofReal_neg, ofReal_one]
    ring
  rw [funext he]
  refine ⟨hc.comp continuous_neg, ?_, fun x ↦ ?_⟩
  · refine ((Measure.measurePreserving_neg (volume : Measure ℝ)).integrable_comp_of_integrable hm).congr ?_
    filter_upwards with y
    change ‖V (-y)‖ * (1 + |-y|) = _
    rw [abs_neg]
  · rw [← hi (-x), ← mul_div_assoc, ← integral_const_mul]
    congr 1
    rw [← integral_neg_eq_self (fun y : ℝ ↦ V (-y) * exp (-ordinate a y * x))]
    apply integral_congr_ae
    filter_upwards with y
    rw [neg_neg, mul_left_comm, ← Complex.exp_add]
    congr 2
    simp only [ordinate, ofReal_sub, ofReal_one, ofReal_neg]
    ring

/-- The exponential prefactor of the local Euler gamma factor. -/
def scaledGamma (k P : ℝ) (b s : ℂ) : ℂ :=
  exp (-(Real.log P : ℂ) * ((k : ℂ) * (s + b))) * Gamma ((k : ℂ) * (s + b))

/-- The scaled gamma logarithmic derivative at any regular gamma argument. -/
theorem logDeriv_scaledGamma_of_regular (k P : ℝ) (b s : ℂ)
    (hreg : ∀ n : ℕ, (k : ℂ) * (s + b) ≠ -(n : ℂ)) :
    logDeriv (scaledGamma k P b) s =
      (k : ℂ) * (digamma ((k : ℂ) * (s + b)) - (Real.log P : ℂ)) := by
  let z (w : ℂ) := (k : ℂ) * (w + b)
  let E (w : ℂ) := exp (-(Real.log P : ℂ) * z w)
  have hz : HasDerivAt z (k : ℂ) s := by
    simpa using ((hasDerivAt_id s).add_const b).const_mul (k : ℂ)
  have hE := (hz.const_mul (-(Real.log P : ℂ))).cexp
  have hG := differentiableAt_Gamma (z s) hreg
  change logDeriv (fun w ↦ E w * Gamma (z w)) s = _
  rw [logDeriv_mul (f := E) (g := fun w ↦ Gamma (z w)) s
    (exp_ne_zero _) (Gamma_ne_zero hreg) hE.differentiableAt
    (hG.comp s hz.differentiableAt),
    show logDeriv (fun w ↦ Gamma (z w)) s = digamma (z s) * (k : ℂ) from
      (logDeriv_comp hG hz.differentiableAt).trans (by rw [hz.deriv, digamma_def])]
  rw [logDeriv_apply, show deriv E s = E s * (-(Real.log P : ℂ) * (k : ℂ)) from hE.deriv,
    mul_div_cancel_left₀ _ (show E s ≠ 0 from exp_ne_zero _)]
  dsimp [z]
  ring

private theorem logDeriv_scaledGamma (k P : ℝ) (b s : ℂ)
    (h : 0 < ((k : ℂ) * (s + b)).re) :
    logDeriv (scaledGamma k P b) s =
      (k : ℂ) * (digamma ((k : ℂ) * (s + b)) - (Real.log P : ℂ)) := by
  apply logDeriv_scaledGamma_of_regular
  intro n he
  have hr := congrArg Complex.re he
  simp at hr h
  linarith [Nat.cast_nonneg (α := ℝ) n]

/-- A scaled Euler gamma factor has a linearly bounded logarithmic
derivative whenever its argument is in the high portion of the strip. -/
theorem exists_norm_logDeriv_scaledGamma_le_high (k P : ℝ) (b : ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ,
      -1 ≤ ((k : ℂ) * (s + b)).re → 1 ≤ |((k : ℂ) * (s + b)).im| →
      ‖logDeriv (scaledGamma k P b) s‖ ≤ C * (1 + ‖s‖) := by
  obtain ⟨D, hD, hDigamma⟩ := exists_norm_digamma_le_high
  let C := |k| * (D * (1 + |k| * (1 + ‖b‖)) + |Real.log P|)
  refine ⟨C, by positivity, fun s hs hi => ?_⟩
  have hreg (n : ℕ) : (k : ℂ) * (s + b) ≠ -(n : ℂ) := by
    intro h
    rw [h] at hi
    norm_num at hi
  rw [logDeriv_scaledGamma_of_regular k P b s hreg, norm_mul, norm_real, Real.norm_eq_abs]
  dsimp only [C]
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  have harg : ‖(k : ℂ) * (s + b)‖ ≤ |k| * (‖s‖ + ‖b‖) := by
    rw [norm_mul, norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (abs_nonneg _)
  have hinner : 1 + |k| * (‖s‖ + ‖b‖) ≤ (1 + |k| * (1 + ‖b‖)) * (1 + ‖s‖) := by
    rw [add_mul, one_mul, mul_assoc]
    apply add_le_add (le_add_of_nonneg_right (norm_nonneg s))
    exact mul_le_mul_of_nonneg_left
      (by nlinarith [mul_nonneg (norm_nonneg b) (norm_nonneg s)]) (abs_nonneg _)
  calc
    _ ≤ ‖digamma ((k : ℂ) * (s + b))‖ + |Real.log P| := by
      simpa only [norm_real, Real.norm_eq_abs] using norm_sub_le
        (digamma ((k : ℂ) * (s + b))) (Real.log P : ℂ)
    _ ≤ D * ((1 + |k| * (1 + ‖b‖)) * (1 + ‖s‖)) + |Real.log P| :=
      add_le_add ((hDigamma _ hs hi).trans (mul_le_mul_of_nonneg_left
        ((add_le_add le_rfl harg).trans hinner) hD)) le_rfl
    _ ≤ _ := by
      have hp := mul_nonneg (abs_nonneg (Real.log P)) (norm_nonneg s)
      nlinarith

private def gammaSample (k : ℝ) (b : ℂ) (g : ℝ → ℂ) (t : ℝ) : ℂ :=
  (g 0 * exp (-(t : ℂ)) - exp (-b * ((k * t : ℝ) : ℂ)) * g (k * t)) /
    (1 - exp (-(t : ℂ)))

private theorem gammaContourLeg (k P a : ℝ) (hk : 0 < k) (b : ℂ) (hb : 0 < a + b.re)
    (W g : ℝ → ℂ) (hW : Continuous W) (hM : Integrable (fun y ↦ ‖W y‖ * (1 + |y|)))
    (hinv : ∀ x : ℝ, (∫ y : ℝ, W y * exp (-ordinate a y * x)) /
      (2 * (Real.pi : ℂ)) = g x) :
    let L := fun y ↦ W y * logDeriv (scaledGamma k P b) (ordinate a y)
    Integrable L ∧ IntegrableOn (gammaSample k b g) (Ioi 0) ∧
      (∫ y, L y) / (2 * (Real.pi : ℂ)) =
        (k : ℂ) * ((∫ t in Ioi 0, gammaSample k b g t) -
          ((Real.eulerMascheroniConstant : ℂ) + (Real.log P : ℂ)) * g 0) := by
  intro L
  let c : ℂ := 2 * Real.pi
  let A : ℂ := (Real.eulerMascheroniConstant : ℂ) + (Real.log P : ℂ)
  let D (y t : ℝ) := gaussDigammaDifference 1 ((k : ℂ) * (ordinate a y + b)) t
  have hJ : Integrable (fun p : ℝ × ℝ ↦ W p.1 * D p.1 p.2)
      ((volume : Measure ℝ).prod (volume.restrict (Ioi 0))) := by
    simpa only [D, ordinate, Complex.re_add_im] using
      integrable_mul_gaussDigammaDifference (τ := b.im) hb one_pos hk hW.measurable hM
  have hWi : Integrable W := hM.mono' hW.aestronglyMeasurable (Eventually.of_forall fun y ↦
    le_mul_of_one_le_right (norm_nonneg _) (by linarith [abs_nonneg y]))
  have hzero : (∫ y, W y) / c = g 0 := by simpa [c] using hinv 0
  have hslice (t : ℝ) : (∫ y, W y * D y t) / c = gammaSample k b g t := by
    let x := k * t
    have hExp (y : ℝ) : exp (-((k : ℂ) * (ordinate a y + b)) * t) =
        exp (-b * x) * exp (-ordinate a y * x) := by
      rw [← Complex.exp_add]
      congr 1
      dsimp [x]
      push_cast
      ring
    have hXi : Integrable (fun y ↦ W y * exp (-ordinate a y * x)) := by
      refine (hWi.norm.mul_const (Real.exp (-a * x))).mono'
        ((hW.mul (by unfold ordinate; fun_prop)).aestronglyMeasurable) (Eventually.of_forall fun y ↦ ?_)
      simp [Complex.norm_exp, ordinate, mul_re]
    have hpoint (y : ℝ) : W y * D y t = (W y * exp (-(t : ℂ)) -
        exp (-b * x) * (W y * exp (-ordinate a y * x))) / (1 - exp (-(t : ℂ))) := by
      simp only [D, gaussDigammaDifference, ofReal_one, neg_one_mul, hExp, div_eq_mul_inv]
      ring
    simp_rw [hpoint]
    rw [integral_div, integral_sub (hWi.mul_const _) (hXi.const_mul _), integral_mul_const,
      integral_const_mul]
    change _ = (g 0 * _ - _ * g x) / _
    rw [← hzero, ← hinv x]
    dsimp only [c]
    ring
  have hL (y : ℝ) : L y = (k : ℂ) * ((∫ t in Ioi 0, W y * D y t) - W y * A) := by
    have hz : 0 < ((k : ℂ) * (ordinate a y + b)).re := by
      simpa [ordinate, mul_re] using mul_pos hk hb
    have hψ := (integral_gaussDigammaDifference (d := 1) (w := (k : ℂ) * (ordinate a y + b))
      one_pos (by simpa using hz)).2
    simp only [ofReal_one, div_one, digamma_one] at hψ
    dsimp only [L]
    rw [logDeriv_scaledGamma k P b _ hz, integral_const_mul]
    change _ = _ * (W y * (∫ t in Ioi 0, D y t) - W y * A)
    rw [show (∫ t in Ioi 0, D y t) = _ from hψ]
    dsimp [A]
    ring
  have hLeft := hJ.integral_prod_left
  have hRight := hJ.integral_prod_right
  refine ⟨((hLeft.sub (hWi.mul_const A)).const_mul (k : ℂ)).congr
    (Eventually.of_forall fun y ↦ (hL y).symm),
    (hRight.div_const c).congr (Eventually.of_forall hslice), ?_⟩
  simp_rw [hL]
  rw [integral_const_mul, integral_sub hLeft (hWi.mul_const A), integral_mul_const,
    integral_integral_swap hJ]
  have hTotal := integral_congr_ae (μ := volume.restrict (Ioi (0 : ℝ)))
    (Eventually.of_forall hslice)
  rw [integral_div] at hTotal
  rw [← hTotal, ← hzero]
  ring

/-- The compensated kernel in logarithmic coordinates. Its contact term uses
the Euler constant outside the integral. -/
def localGammaExplicitKernel (k : ℝ) (b b' : ℂ) (f : ℝ → ℂ) (t : ℝ) : ℂ :=
  (k : ℂ) * ((2 * f 1 * exp (-(t : ℂ)) -
      exp (-b * ((k * t : ℝ) : ℂ)) * f (Real.exp (k * t)) -
      exp (-(b' + 1) * ((k * t : ℝ) : ℂ)) * f (Real.exp (-(k * t)))) /
    (1 - exp (-(t : ℂ))))

/-- Both local contours with the right abscissa and the dual local factor.
The two endpoint cancellations take place before the integral. -/
theorem localGamma_explicitContour (f : ℝ → ℂ) (hw : ∀ a, MellinSchwartzAt f a)
    (hf : ∀ t > 0, ContinuousAt f t) (k P a : ℝ) (hk : 0 < k) (b b' : ℂ)
    (hb : 0 < a + b.re) (hb' : 0 < a + b'.re) :
    let H := fun s ↦ mellin f s * logDeriv (scaledGamma k P b) s +
      mellin f (1 - s) * logDeriv (scaledGamma k P b') s
    let K := localGammaExplicitKernel k b b' f
    VerticalIntegrable H a ∧ IntegrableOn K (Ioi 0) ∧
      (∫ y : ℝ, H (ordinate a y)) / (2 * (Real.pi : ℂ)) =
        (∫ t in Ioi 0, K t) -
          (2 * (k : ℂ)) * ((Real.eulerMascheroniConstant : ℂ) + (Real.log P : ℂ)) * f 1 := by
  intro H K
  let g (x : ℝ) := f (Real.exp x)
  let g' (x : ℝ) := exp (-(x : ℂ)) * f (Real.exp (-x))
  have hg : g 0 = f 1 := by simp [g]
  have hg' : g' 0 = f 1 := by simp [g']
  obtain ⟨hd, hm, hi⟩ := mellinVerticalTrace f hw a hf
  obtain ⟨hd', hm', hi'⟩ := mellinVerticalTrace_reflect f hw a hf
  obtain ⟨hL, hK, hval⟩ := gammaContourLeg k P a hk b hb _ g hd hm hi
  obtain ⟨hL', hK', hval'⟩ := gammaContourLeg k P a hk b' hb' _ g' hd' hm' hi'
  have hsample (t : ℝ) : K t =
      (k : ℂ) * (gammaSample k b g t + gammaSample k b' g' t) := by
    have hphase : exp (-b' * ((k * t : ℝ) : ℂ)) * exp (-((k * t : ℝ) : ℂ)) =
        exp (-(b' + 1) * ((k * t : ℝ) : ℂ)) := by
      rw [← exp_add]
      congr 1
      ring
    simp only [K, localGammaExplicitKernel, gammaSample, hg, hg', g, g', ← mul_assoc, hphase]
    ring
  refine ⟨hL.add hL', ((hK.add hK').const_mul (k : ℂ)).congr
    (Eventually.of_forall fun t ↦ (hsample t).symm), ?_⟩
  dsimp only [H]
  simp_rw [hsample]
  rw [integral_add hL hL', add_div, hval, hval', integral_const_mul, integral_add hK hK', hg, hg']
  ring

theorem scaledGamma_real (b : ℂ) :
    scaledGamma (1 / 2) Real.pi b = fun s ↦ Gammaℝ (s + b) := by
  funext s
  rw [Gammaℝ_def, cpow_def_of_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero),
    ← ofReal_log Real.pi_nonneg]
  simp only [scaledGamma, ofReal_div, ofReal_one, ofReal_ofNat]
  congr 2 <;> ring

theorem scaledGamma_complex (b : ℂ) :
    scaledGamma 1 (2 * Real.pi) b = fun s ↦ Gammaℂ (s + b) / 2 := by
  have hP : 0 < 2 * Real.pi := by positivity
  funext s
  rw [Gammaℂ_def, show (2 : ℂ) * (Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; rfl,
    cpow_def_of_ne_zero (ofReal_ne_zero.mpr hP.ne'), ← ofReal_log hP.le]
  simp only [scaledGamma, ofReal_one, one_mul]
  rw [show (Real.log (2 * Real.pi) : ℂ) * -(s + b) =
    -(Real.log (2 * Real.pi) : ℂ) * (s + b) by ring]
  ring

/-- B.4.2.1 at a real place. Duality negates the radial exponent and preserves
the sign parity. The integral includes the real gamma prefactor. -/
theorem realGamma_explicitContour (f : ℝ → ℂ) (hw : ∀ a, MellinSchwartzAt f a)
    (hf : ∀ t > 0, ContinuousAt f t) {a : ℝ} (ha : 1 < a) {u : ℂ} (hu : u.re = 0)
    (parity : Fin 2) :
    let b : ℂ := u + (parity.val : ℂ)
    let b' : ℂ := -u + (parity.val : ℂ)
    let H := fun s ↦ mellin f s * logDeriv (fun z ↦ Gammaℝ (z + b)) s +
      mellin f (1 - s) * logDeriv (fun z ↦ Gammaℝ (z + b')) s
    let K := localGammaExplicitKernel (1 / 2) b b' f
    VerticalIntegrable H a ∧ IntegrableOn K (Ioi 0) ∧
      (I * ∫ y : ℝ, H ((a : ℂ) + (y : ℂ) * I)) / (2 * (Real.pi : ℂ) * I) =
        (∫ t in Ioi 0, K t) - ((Real.eulerMascheroniConstant : ℂ) + (Real.log Real.pi : ℂ)) * f 1 := by
  intro b b' H K
  have hb : 0 < a + b.re := by
    simp [b, hu]
    positivity
  have hb' : 0 < a + b'.re := by
    simp [b', hu]
    positivity
  have h := localGamma_explicitContour f hw hf (1 / 2) Real.pi a (by norm_num) b b' hb hb'
  dsimp only at h
  rw [scaledGamma_real, scaledGamma_real] at h
  rw [mul_comm (2 * (Real.pi : ℂ)) I, mul_div_mul_left _ _ I_ne_zero]
  norm_num [ordinate, H, K] at h ⊢
  exact h

/-- B.4.2.1 at a complex place. The angular shift is half its absolute
weight, and the gamma prefactor is half of Gammaℂ. -/
theorem complexGamma_explicitContour (f : ℝ → ℂ) (hw : ∀ a, MellinSchwartzAt f a)
    (hf : ∀ t > 0, ContinuousAt f t) {a : ℝ} (ha : 1 < a) {u : ℂ} (hu : u.re = 0)
    (angular : ℤ) :
    let b : ℂ := u + (angular.natAbs : ℂ) / 2
    let b' : ℂ := -u + (angular.natAbs : ℂ) / 2
    let H := fun s ↦ mellin f s * logDeriv (fun z ↦ Gammaℂ (z + b) / 2) s +
      mellin f (1 - s) * logDeriv (fun z ↦ Gammaℂ (z + b') / 2) s
    let K := localGammaExplicitKernel 1 b b' f
    VerticalIntegrable H a ∧ IntegrableOn K (Ioi 0) ∧
      (I * ∫ y : ℝ, H ((a : ℂ) + (y : ℂ) * I)) / (2 * (Real.pi : ℂ) * I) =
        (∫ t in Ioi 0, K t) -
          2 * ((Real.eulerMascheroniConstant : ℂ) + (Real.log (2 * Real.pi) : ℂ)) * f 1 := by
  intro b b' H K
  have hb : 0 < a + b.re := by
    simp [b, hu, Complex.div_ofNat_re]
    positivity
  have hb' : 0 < a + b'.re := by
    simp [b', hu, Complex.div_ofNat_re]
    positivity
  have h := localGamma_explicitContour f hw hf 1 (2 * Real.pi) a one_pos b b' hb hb'
  dsimp only at h
  rw [scaledGamma_complex, scaledGamma_complex] at h
  rw [mul_comm (2 * (Real.pi : ℂ)) I, mul_div_mul_left _ _ I_ne_zero]
  simpa [ordinate, H, K] using h

/-- The printed class of tests supplies the contour hypotheses under the
logarithmic coordinate on the positive reals. -/
theorem exponentialLogProfile_mellinHypotheses (g : PositiveRealExponentialDecay (univ : Set ℝ)) :
    (∀ a, MellinSchwartzAt (g.val ∘ Real.log) a) ∧
      (∀ t > 0, ContinuousAt (g.val ∘ Real.log) t) := by
  refine ⟨fun a ↦ (logExponentialDecay_mem_iff_mellinSchwartzAt _ _).mp g.property a (mem_univ _), ?_⟩
  obtain ⟨v, hv⟩ := ((logExponentialDecay_mem_iff_twoSided _).mp g.property).1
  have hg : Continuous g.val := by rw [← hv]; exact v.continuous
  exact fun t ht ↦ hg.continuousAt.comp (Real.continuousAt_log ht.ne')

/-- The right-hand kernel as printed in (B.4.2.15) at the real place
with the trivial character, in the logarithmic coordinate. -/
def printedRealGammaKernel (g : ℝ → ℂ) (t : ℝ) : ℂ :=
  g 0 / (t : ℂ) - (g t + g (-t)) * (Real.exp ((3 / 2 : ℝ) * t) : ℂ) /
    (1 - (Real.exp (-2 * t) : ℂ))

/-- The upper truncations of the real, trivial-character kernel in (B.4.2.15)
are exactly log R beyond one for a compact logarithmic bump. -/
theorem printedRealGammaKernel_upperTail :
    ∃ g : PositiveRealExponentialDecay (univ : Set ℝ), g.val 0 = 1 ∧
      ∀ R : ℝ, 1 ≤ R →
        (∫ t in Ioc 1 R, printedRealGammaKernel g.val t) = (Real.log R : ℂ) := by
  let ψ : ContDiffBump (0 : ℝ) := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩
  let p : ℝ → ℂ := fun t ↦ (ψ t : ℂ)
  let g : PositiveRealExponentialDecay (univ : Set ℝ) := ⟨p,
    mem_logExponentialDecaySubmodule_of_hasCompactSupport _
      (ψ.hasCompactSupport.comp_left Complex.ofReal_zero)
      (Complex.ofRealCLM.contDiff.comp ψ.contDiff)⟩
  have h0 : g.val 0 = 1 := by
    change (ψ 0 : ℂ) = 1
    rw [ψ.one_of_mem_closedBall (Metric.mem_closedBall_self ψ.rIn_pos.le), ofReal_one]
  have hzero (t : ℝ) (ht : 1 < |t|) : g.val t = 0 := by
    change (ψ t : ℂ) = 0
    rw [ψ.zero_of_le_dist, ofReal_zero]
    rw [Real.dist_eq, sub_zero]
    change 1 / 2 ≤ |t|
    linarith
  refine ⟨g, h0, fun R hR ↦ ?_⟩
  rw [setIntegral_congr_fun measurableSet_Ioc (g := fun t : ℝ ↦ ((t⁻¹ : ℝ) : ℂ))
    (fun t ht ↦ by
      have ht' : 1 < |t| := by rw [abs_of_pos (one_pos.trans ht.1)]; exact ht.1
      rw [printedRealGammaKernel, hzero t ht', hzero (-t) (by rwa [abs_neg]), h0]
      push_cast
      ring)]
  rw [integral_complex_ofReal, ← intervalIntegral.integral_of_le hR,
    integral_inv_of_pos one_pos (by linarith), div_one]

/-- The printed real kernel can have no finite improper integral at infinity. -/
theorem printedRealGammaKernel_diverges :
    ∃ g : PositiveRealExponentialDecay (univ : Set ℝ),
      ∀ L : ℂ, ¬ Tendsto (fun R : ℝ ↦ ∫ t in Ioc 1 R, printedRealGammaKernel g.val t)
        atTop (𝓝 L) := by
  obtain ⟨g, _, hlog⟩ := printedRealGammaKernel_upperTail
  refine ⟨g, fun L hL ↦ ?_⟩
  have hre := (continuous_re.tendsto L).comp hL
  refine not_tendsto_nhds_of_tendsto_atTop Real.tendsto_log_atTop _ (hre.congr' ?_)
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
  simp only [Function.comp_apply, hlog R hR, ofReal_re]

end Masullo
