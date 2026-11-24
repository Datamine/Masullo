import ArchimedeanExplicitContour
import HeckePrimePowerLimits
import ManuscriptHeckeCharacterChart
import AdelicHaarScaling
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open Complex Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped NumberField Topology

namespace Masullo

noncomputable section

private abbrev Place (F : Type*) [Field F] [NumberField F] := HeightOneSpectrum (𝓞 F)
private def ordinate (a y : ℝ) : ℂ := (a : ℂ) + (y : ℂ) * I

variable (F : Type*) [Field F] [NumberField F]

private abbrev powerNorm (j : Place F × ℕ) : ℝ := (heckePrimePowerIdeal F j).absNorm

private abbrev primeCoefficient (c : Place F → ℂ) (j : Place F × ℕ) : ℂ :=
  c j.1 ^ (j.2 + 1) * (Real.log (j.1.asIdeal.absNorm : ℝ) : ℂ)

private theorem powerNorm_pos (j : Place F × ℕ) : 0 < powerNorm F j := by
  simp only [powerNorm, heckePrimePowerIdeal, map_pow, Nat.cast_pow]
  exact pow_pos (by exact_mod_cast
    (zero_lt_one.trans (NumberField.HeightOneSpectrum.one_lt_absNorm j.1))) _

private theorem primePowerTerm_exp (c : Place F → ℂ) (s : ℂ) (j : Place F × ℕ) :
    heckePrimePowerTerm F c s j = primeCoefficient F c j *
      exp (-s * (Real.log (powerNorm F j) : ℂ)) := by
  have hq := powerNorm_pos F j
  unfold heckePrimePowerTerm
  rw [← Complex.ofReal_natCast, cpow_def_of_ne_zero (ofReal_ne_zero.mpr hq.ne'),
    ← ofReal_log hq.le, mul_comm (↑(Real.log (powerNorm F j)) : ℂ) (-s)]

/-- Termwise vertical-line integration of the finite Euler logarithmic
derivative. The inverse profile is sampled at log prime-power norm. -/
private theorem primeContourLeg (c : Place F → ℂ) (hc : ∀ v, ‖c v‖ ≤ 1)
    {a : ℝ} (ha : 1 < a) (W g : ℝ → ℂ) (hW : Continuous W) (hWi : Integrable W)
    (hinv : ∀ x : ℝ, (∫ y, W y * exp (-ordinate a y * x)) / (2 * (Real.pi : ℂ)) = g x) :
    let B := fun j : Place F × ℕ => primeCoefficient F c j * g (Real.log (powerNorm F j))
    let P := fun y => W y * logDeriv (fun z ↦ ∏' v, heckeEulerFactor F c v z) (ordinate a y)
    Integrable P ∧ Summable (fun j => ‖B j‖) ∧
      HasSum B (-(∫ y, P y) / (2 * (Real.pi : ℂ))) := by
  intro B P
  letI : Countable (Place F) := finitePlaces_countable F
  obtain ⟨M, hM, hBound⟩ := heckePrimePowerTerm_majorant F c hc ha
  let A (j : Place F × ℕ) (y : ℝ) := heckePrimePowerTerm F c (ordinate a y) j
  let J (j : Place F × ℕ) (y : ℝ) := W y * A j y
  have hre (y : ℝ) : (ordinate a y).re = a := by simp [ordinate, Complex.mul_re]
  have hA (j : Place F × ℕ) (y : ℝ) : ‖A j y‖ ≤ M j := hBound j _ ((hre y).ge)
  have hAc (j : Place F × ℕ) : Continuous (A j) := by
    simp only [A, primePowerTerm_exp]
    exact continuous_const.mul (Complex.continuous_exp.comp (by unfold ordinate; fun_prop))
  have hJ (j : Place F × ℕ) (y : ℝ) : ‖J j y‖ ≤ ‖W y‖ * M j := by
    rw [show J j y = W y * A j y from rfl, norm_mul]
    exact mul_le_mul_of_nonneg_left (hA j y) (norm_nonneg _)
  have hJi (j : Place F × ℕ) : Integrable (J j) :=
    (hWi.norm.mul_const (M j)).mono' (hW.mul (hAc j)).aestronglyMeasurable (.of_forall (hJ j))
  have hJn : Summable fun j => ∫ y, ‖J j y‖ := by
    apply (hM.mul_left (∫ y, ‖W y‖)).of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _)
    intro j
    rw [← integral_mul_const]
    exact integral_mono (hJi j).norm (hWi.norm.mul_const _) (hJ j)
  have hAsc : Continuous fun y => ∑' j, A j y := continuous_tsum hAc hM hA
  have hAsi : Integrable (fun y => W y * ∑' j, A j y) := by
    apply (hWi.norm.mul_const (∑' j, M j)).mono' (hW.mul hAsc).aestronglyMeasurable
    refine .of_forall fun y => ?_
    change ‖W y * (∑' j, A j y)‖ ≤ _
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    have hn := hM.of_nonneg_of_le (fun j => norm_nonneg (A j y)) (fun j => hA j y)
    exact (norm_tsum_le_tsum_norm hn).trans (hn.tsum_le_tsum (fun j => hA j y) hM)
  have hP (y : ℝ) : P y = -(W y * ∑' j, A j y) := by
    have hlog := neg_logDeriv_heckeEulerProduct F c hc (show 1 < (ordinate a y).re by rwa [hre])
    change W y * logDeriv _ _ = _
    rw [← show -logDeriv _ _ = (∑' j, A j y) from hlog, mul_neg, neg_neg]
  have hj (j : Place F × ℕ) : (∫ y, J j y) / (2 * (Real.pi : ℂ)) = B j := by
    have he (y : ℝ) : J j y = primeCoefficient F c j *
        (W y * exp (-ordinate a y * (Real.log (powerNorm F j) : ℂ))) := by
      simp only [J, A, primePowerTerm_exp]
      ring
    simp only [he, integral_const_mul, mul_div_assoc, hinv, B]
  refine ⟨hAsi.neg.congr (.of_forall fun y => (hP y).symm), ?_, ?_⟩
  · apply (hJn.mul_right ‖(2 * (Real.pi : ℂ))⁻¹‖).of_nonneg_of_le (fun _ => norm_nonneg _)
    intro j
    rw [← hj, div_eq_mul_inv, norm_mul]
    exact mul_le_mul_of_nonneg_right (norm_integral_le_integral_norm _) (norm_nonneg _)
  · have hsum := (hasSum_integral_of_summable_integral_norm hJi hJn).div_const (2 * (Real.pi : ℂ))
    simp only [hj] at hsum
    have hInt : (∫ y, ∑' j, J j y) = -(∫ y, P y) := by
      rw [← integral_neg]
      apply integral_congr_ae
      filter_upwards with y
      rw [hP, neg_neg]
      change (∑' j : Place F × ℕ, W y * A j y) = W y * ∑' j : Place F × ℕ, A j y
      exact tsum_mul_left
    simpa only [hInt] using hsum

/-- The two finite Euler-product legs in B.4.2.2, evaluated by Mellin
inversion in the original spectral parameter of the character. -/
theorem manuscriptFiniteHecke_explicitContour (χ : PontryaginDual (IdeleClass F))
    (f : ℝ → ℂ) (hw : ∀ a, MellinSchwartzAt f a) (hf : ∀ t > 0, ContinuousAt f t)
    {a : ℝ} (ha : 1 < a) :
    let c := heckeEulerCoefficient F χ (chosenFiniteUniformizer F)
    let c' := heckeEulerCoefficient F χ⁻¹ (chosenFiniteUniformizer F)
    let B := fun j : Place F × ℕ =>
      primeCoefficient F c j * f (powerNorm F j) +
        primeCoefficient F c' j * ((powerNorm F j : ℂ)⁻¹ * f (powerNorm F j)⁻¹)
    let H := fun s =>
      mellin f s * logDeriv (manuscriptFiniteHeckeEuler F χ) s +
        mellin f (1 - s) * logDeriv (manuscriptFiniteHeckeEuler F χ⁻¹) s
    VerticalIntegrable H a ∧ Summable (fun j => ‖B j‖) ∧
      HasSum B (-(∫ y : ℝ, H (ordinate a y)) / (2 * (Real.pi : ℂ))) := by
  intro c c' B H
  let W := fun y : ℝ => mellin f (ordinate a y)
  let V := fun y : ℝ => mellin f (1 - ordinate a y)
  obtain ⟨hW, hWn, hWinv⟩ := mellinVerticalTrace f hw a hf
  obtain ⟨hV, hVn, hVinv⟩ := mellinVerticalTrace_reflect f hw a hf
  have hWi : Integrable W := hWn.mono' hW.aestronglyMeasurable (.of_forall fun y => by
    change ‖W y‖ ≤ ‖W y‖ * (1 + |y|)
    exact le_mul_of_one_le_right (norm_nonneg _) (le_add_of_nonneg_right (abs_nonneg y)))
  have hVi : Integrable V := hVn.mono' hV.aestronglyMeasurable (.of_forall fun y => by
    change ‖V y‖ ≤ ‖V y‖ * (1 + |y|)
    exact le_mul_of_one_le_right (norm_nonneg _) (le_add_of_nonneg_right (abs_nonneg y)))
  obtain ⟨hi, hAbs, hSum⟩ := primeContourLeg F c (norm_heckeEulerCoefficient_le_one F χ _)
    ha W (fun x => f (Real.exp x)) hW hWi hWinv
  obtain ⟨hi', hAbs', hSum'⟩ := primeContourLeg F c'
    (norm_heckeEulerCoefficient_le_one F χ⁻¹ _) ha V
    (fun x => exp (-(x : ℂ)) * f (Real.exp (-x))) hV hVi hVinv
  have hSample (j : Place F × ℕ) :
      exp (-(Real.log (powerNorm F j) : ℂ)) * f (Real.exp (-Real.log (powerNorm F j))) =
        (powerNorm F j : ℂ)⁻¹ * f (powerNorm F j)⁻¹ := by
    rw [← ofReal_neg, ← ofReal_exp, Real.exp_neg, Real.exp_log (powerNorm_pos F j), ofReal_inv]
  have hB (j : Place F × ℕ) : B j =
      primeCoefficient F c j * f (Real.exp (Real.log (powerNorm F j))) +
        primeCoefficient F c' j *
          (exp (-(Real.log (powerNorm F j) : ℂ)) * f (Real.exp (-Real.log (powerNorm F j)))) := by
    rw [hSample, Real.exp_log (powerNorm_pos F j)]
  have hInt := hi.add hi'
  refine ⟨hInt, (hAbs.add hAbs').of_nonneg_of_le (fun _ => norm_nonneg _) (fun j => ?_), ?_⟩
  · rw [hB]
    exact norm_add_le _ _
  · have h := hSum.add hSum'
    rw [← funext hB] at h
    have hEq : (∫ y : ℝ, H (ordinate a y)) =
        (∫ y : ℝ, W y * logDeriv (manuscriptFiniteHeckeEuler F χ) (ordinate a y)) +
        (∫ y : ℝ, V y * logDeriv (manuscriptFiniteHeckeEuler F χ⁻¹) (ordinate a y)) :=
      integral_add hi hi'
    rw [hEq, neg_add, add_div]
    exact h

/-- The centered finite-prime term for the exponential-decay test class.
The two samples have the common prime-power weight of (B.4.2.17). -/
theorem manuscriptFiniteHecke_centeredExplicitContour
    (χ : PontryaginDual (IdeleClass F)) (g : PositiveRealExponentialDecay (univ : Set ℝ))
    {a : ℝ} (ha : 1 < a) :
    let c := heckeEulerCoefficient F χ (chosenFiniteUniformizer F)
    let c' := heckeEulerCoefficient F χ⁻¹ (chosenFiniteUniformizer F)
    let f := g.val ∘ Real.log
    let B := fun j : Place F × ℕ =>
      exp (-(Real.log (powerNorm F j) : ℂ) / 2) *
        (primeCoefficient F c j * g.val (Real.log (powerNorm F j)) +
          primeCoefficient F c' j * g.val (-Real.log (powerNorm F j)))
    let H := fun s =>
      mellin f (s - 1 / 2) * logDeriv (manuscriptFiniteHeckeEuler F χ) s +
        mellin f (1 / 2 - s) * logDeriv (manuscriptFiniteHeckeEuler F χ⁻¹) s
    VerticalIntegrable H a ∧ Summable (fun j => ‖B j‖) ∧
      HasSum B (-(∫ y : ℝ, H (ordinate a y)) / (2 * (Real.pi : ℂ))) := by
  intro c c' f B H
  obtain ⟨hfS, hfC⟩ := exponentialLogProfile_mellinHypotheses g
  let f₀ (u : ℝ) := exp (-(Real.log u : ℂ) / 2) * f u
  have hS (σ : ℝ) : MellinSchwartzAt f₀ σ := by
    obtain ⟨v, hv⟩ := mellinSchwartzAt_iff_positive_log.mp (hfS (σ - 1 / 2))
    refine mellinSchwartzAt_iff_positive_log.mpr ⟨v, funext fun x => ?_⟩
    rw [congrFun hv x]
    simp only [f₀, Real.log_exp, Complex.real_smul, ofReal_exp,
      ofReal_mul, ofReal_sub, ofReal_div, ofReal_one, ofReal_ofNat, ← mul_assoc, ← exp_add]
    congr 2
    ring
  have hC (u : ℝ) (hu : 0 < u) : ContinuousAt f₀ u := by
    have hc : ContinuousAt (fun t : ℝ => (Real.log t : ℂ)) u :=
      Complex.continuous_ofReal.continuousAt.comp (Real.continuousAt_log hu.ne')
    exact (Complex.continuous_exp.continuousAt.comp (hc.neg.div_const 2)).mul (hfC u hu)
  have hshift (s : ℂ) : mellin f₀ s = mellin f (s - 1 / 2) := by
    rw [mellin_eq_log_integral, mellin_eq_log_integral]
    apply integral_congr_ae
    filter_upwards with x
    simp only [f₀, Real.log_exp, ← mul_assoc, ← exp_add]
    congr 2
    ring
  obtain ⟨hI, hAbs, hSum⟩ := manuscriptFiniteHecke_explicitContour F χ f₀ hS hC ha
  have hH : (fun s =>
      mellin f₀ s * logDeriv (manuscriptFiniteHeckeEuler F χ) s +
        mellin f₀ (1 - s) * logDeriv (manuscriptFiniteHeckeEuler F χ⁻¹) s) = H := by
    funext s
    rw [hshift, hshift, show 1 - s - (1 / 2 : ℂ) = 1 / 2 - s by ring]
  have hB : (fun j : Place F × ℕ =>
      primeCoefficient F c j * f₀ (powerNorm F j) +
        primeCoefficient F c' j * ((powerNorm F j : ℂ)⁻¹ * f₀ (powerNorm F j)⁻¹)) = B := by
    funext j
    have hq := powerNorm_pos F j
    have hInv : (powerNorm F j : ℂ)⁻¹ = exp (-(Real.log (powerNorm F j) : ℂ)) := by
      rw [← ofReal_neg, ← ofReal_exp, Real.exp_neg, Real.exp_log hq, ofReal_inv]
    have hPhase :
        exp (-(Real.log (powerNorm F j) : ℂ)) * exp (-(-(Real.log (powerNorm F j) : ℂ)) / 2) =
          exp (-(Real.log (powerNorm F j) : ℂ) / 2) := by
      rw [← exp_add]
      congr 1
      ring
    dsimp only [f₀, f, B, Function.comp_apply]
    rw [Real.log_inv, Complex.ofReal_neg, hInv, ← mul_assoc (exp _) (exp _) (g.val _), hPhase]
    ring
  rw [hH] at hI
  refine ⟨hI, ?_, ?_⟩
  · change Summable (fun j => ‖(fun j : Place F × ℕ =>
      primeCoefficient F c j * f₀ (powerNorm F j) +
        primeCoefficient F c' j * ((powerNorm F j : ℂ)⁻¹ * f₀ (powerNorm F j)⁻¹)) j‖) at hAbs
    rwa [hB] at hAbs
  · change HasSum _ (-(∫ y, (fun s =>
      mellin f₀ s * logDeriv (manuscriptFiniteHeckeEuler F χ) s +
        mellin f₀ (1 - s) * logDeriv (manuscriptFiniteHeckeEuler F χ⁻¹) s) (ordinate a y)) /
      (2 * (Real.pi : ℂ))) at hSum
    rw [hH] at hSum
    change HasSum (fun j : Place F × ℕ =>
      primeCoefficient F c j * f₀ (powerNorm F j) +
        primeCoefficient F c' j * ((powerNorm F j : ℂ)⁻¹ * f₀ (powerNorm F j)⁻¹)) _ at hSum
    rwa [hB] at hSum

/-- The constant term against the reflected centered Mellin transform
evaluates at the identity under the same contour normalization. -/
theorem centeredMellin_reflected_constant_contour
    (g : PositiveRealExponentialDecay (univ : Set ℝ)) (a : ℝ) (k : ℂ) :
    let H := fun s => k * mellin (g.val ∘ Real.log) (1 / 2 - s)
    VerticalIntegrable H a ∧
      (∫ y : ℝ, H (ordinate a y)) / (2 * (Real.pi : ℂ)) = k * g.val 0 := by
  intro H
  let f := g.val ∘ Real.log
  let V := fun y : ℝ => mellin f (1 - ordinate (a + 1 / 2) y)
  obtain ⟨hfS, hfC⟩ := exponentialLogProfile_mellinHypotheses g
  obtain ⟨hV, hVn, hInv⟩ := mellinVerticalTrace_reflect f hfS (a + 1 / 2) hfC
  have hVi : Integrable V := hVn.mono' hV.aestronglyMeasurable (.of_forall fun y => by
    change ‖V y‖ ≤ ‖V y‖ * (1 + |y|)
    exact le_mul_of_one_le_right (norm_nonneg _) (le_add_of_nonneg_right (abs_nonneg y)))
  have hEq : (fun y => H (ordinate a y)) = fun y => k * V y := by
    funext y
    change k * mellin f (1 / 2 - ordinate a y) = k * mellin f (1 - ordinate (a + 1 / 2) y)
    congr 2
    simp only [ordinate, ofReal_add, ofReal_div, ofReal_one, ofReal_ofNat]
    ring
  have hZero : (∫ y, V y) / (2 * (Real.pi : ℂ)) = g.val 0 := by
    have hz := hInv 0
    change (∫ y, V y * exp (-ordinate (a + 1 / 2) y * (0 : ℂ))) / (2 * (Real.pi : ℂ)) =
      exp (-(0 : ℂ)) * f (Real.exp (-0)) at hz
    simpa [f] using hz
  change Integrable (fun y => H (ordinate a y)) ∧ _
  rw [hEq, integral_const_mul, mul_div_assoc, hZero]
  exact ⟨hVi.const_mul k, rfl⟩

end

end Masullo
