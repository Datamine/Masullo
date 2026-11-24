import FiniteWeilKernel

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped ENNReal NNReal NumberField Pointwise

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
local notation "K" => v.adicCompletion F
local notation "O" => v.adicCompletionIntegers F
local notation "π" => chosenFiniteUniformizer F v
local notation "q" => Ideal.absNorm v.asIdeal
local notation "d" => multiplicity v.asIdeal (differentIdeal ℤ (𝓞 F))
local notation "ψ" => finitePlaceTraceCharacter F v
local notation "Test" => locallyConstantTests K
local notation "φ" => finiteCompletionIntegerRingTest F v
local notation "φ₁" => locallyConstantTestTranslate K (chosenFiniteUniformizer F v) (finiteCompletionIntegerRingTest F v)

set_option maxHeartbeats 1500000

private def finiteTestTranslateAdd (a : K) (f : Test) : Test :=
  let e := Homeomorph.addRight a
  ⟨f.val ∘ e, f.property.1.comp_continuous e.continuous, f.property.2.comp_homeomorph e⟩

private theorem integerRingTest_unchanged_by_one (x : K) : (φ).val (1 + x) = (φ).val x := by
  change (O : Set K).indicator (fun _ ↦ (1 : ℂ)) (1 + x) =
    (O : Set K).indicator (fun _ ↦ (1 : ℂ)) x
  have h : 1 + x ∈ (O : Set K) ↔ x ∈ (O : Set K) := by
    change 1 + x ∈ (O).toSubring ↔ x ∈ (O).toSubring
    constructor
    · intro hx
      simpa only [add_sub_cancel_left] using (O).toSubring.sub_mem hx (O).toSubring.one_mem
    · exact (O).toSubring.add_mem (O).toSubring.one_mem
  classical
  simp only [indicator_apply, h]

private theorem finiteIntegerRingTest_one : (φ).val 1 = 1 := by
  change (O : Set K).indicator (fun _ ↦ (1 : ℂ)) (1 : K) = 1
  exact indicator_of_mem (O).one_mem _

private theorem finiteIntegerRingTest_zero : (φ).val 0 = 1 := by
  change (O : Set K).indicator (fun _ ↦ (1 : ℂ)) (0 : K) = 1
  exact indicator_of_mem (O).zero_mem _

private theorem contractedIntegerTest_zero : (φ₁).val 0 = 1 := by
  change (φ).val ((π)⁻¹.val * 0) = 1
  rw [mul_zero, finiteIntegerRingTest_zero]

private theorem contractedIntegerTest_one : (φ₁).val 1 = 0 := by
  have h := finitePrincipalValue_integerRing_apply F v π (chosenFiniteUniformizer_spec F v)
    (1 : Kˣ)
  change (φ).val 1 - (φ₁).val 1 = (if ‖(1 : K)‖ = 1 then 1 else 0) at h
  rw [finiteIntegerRingTest_one, norm_one, ite_eq_left rfl, sub_eq_self] at h
  exact h

/-- The translated unit test is the integer-ball indicator minus a
translate of the contracted ball indicator. -/
private theorem finiteWeilTest_unitTest :
    finiteWeilTest F v (finiteWeilUnitTest F v) =
      φ - finiteTestTranslateAdd F v 1 φ₁ := by
  classical
  apply Subtype.ext
  funext x
  have he : (φ - finiteTestTranslateAdd F v 1 φ₁ : Test).val x =
      (finitePrincipalValue π φ).val (1 + x) := by
    change (φ).val x - (φ₁).val (x + 1) = (φ).val (1 + x) - (φ₁).val (1 + x)
    rw [integerRingTest_unchanged_by_one F v, add_comm x 1]
  rw [he]
  by_cases hx : 1 + x = 0
  · have hx' : x = -1 := by linear_combination hx
    rw [hx', finiteWeilTest_neg_one, add_neg_cancel, finitePrincipalValue_eval_zero]
  let u := Units.mk0 (1 + x) hx
  have hu : u.val - 1 = x := by change 1 + x - 1 = x; ring
  rw [← show u.val = 1 + x from rfl, ← hu, finiteWeilTest_sub_one,
    finitePrincipalValue_integerRing_apply F v π (chosenFiniteUniformizer_spec F v)]
  change _ * (finitePlaceIntegralUnits F v).indicator (fun _ ↦ (1 : ℂ)) u = _
  have hc : u ∈ finitePlaceIntegralUnits F v ↔ ‖u.val‖ = 1 :=
    (localIntegralUnits_value F v u).trans (finiteCompletion_norm_eq_one_iff F v u).symm
  by_cases hn : ‖u.val‖ = 1
  · rw [indicator_of_mem (hc.mpr hn), ite_eq_left hn, hn, Real.one_rpow, Complex.ofReal_one, mul_one]
  · rw [indicator_of_notMem (mt hc.mp hn), ite_eq_right hn, mul_zero]

section Tamagawa

variable [∀ w : HeightOneSpectrum (𝓞 F), MeasurableSpace (w.adicCompletion F)]
  [∀ w : HeightOneSpectrum (𝓞 F), BorelSpace (w.adicCompletion F)]

local notation "ν" => additiveHaarDifferent F v
local notation "D" => finitePlaceIntegerAnnihilator F v
local notation "Fourier" => finitePlaceTraceFourier F v (additiveHaarDifferent F v)
local notation "J" => finiteLogFourierPairing F v (additiveHaarDifferent F v)

local instance : (ν).IsAddHaarMeasure := additiveHaarDifferent_isHaar F v

private theorem finiteLogFourierPairing_contractedTranslate_difference :
    J (φ₁ - finiteTestTranslateAdd F v 1 φ₁) = (d : ℂ) + 1 := by
  let b := finiteTestTranslateAdd F v 1 φ₁
  let δ : Test := φ₁ - b
  have htest0 : δ.val 0 = 1 := by
    change (φ₁).val 0 - (φ₁).val (0 + 1) = 1
    rw [zero_add, contractedIntegerTest_zero, contractedIntegerTest_one, sub_zero]
  have hdiff (y : K) : Fourier δ.val y =
      Fourier (φ₁).val y - Fourier (φ₁).val y * ((ψ (y * (-1))).toMul : ℂ) := by
    rw [finitePlaceTraceFourier_sub]
    have ht : Fourier b.val y = Fourier (φ₁).val y * ((ψ (y * (-1))).toMul : ℂ) := by
      change Fourier (fun t ↦ (φ₁).val (t + 1)) y = _
      simpa only [neg_neg] using finitePlaceTraceFourier_addTranslate F v ν (φ₁).val (-1) y
    rw [ht]
  have hq : 1 < (q : ℝ) := by
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hqp : 0 < (q : ℝ) := zero_lt_one.trans hq
  have hors (y : K) (h : Fourier δ.val y ≠ 0) :
      (q : ℝ) ^ d < ‖y‖ ∧ ‖y‖ ≤ (q : ℝ) ^ (d + 1) := by
    constructor
    · by_contra! hy
      have hyD : y ∈ D := by rw [finitePlaceIntegerAnnihilator_eq_differentBall]; exact hy
      have hψ : ψ y = 0 := by simpa only [one_mul] using hyD 1 (O).one_mem
      have hphase : ((ψ (y * (-1))).toMul : ℂ) = 1 := by
        rw [mul_neg, mul_one, map_neg, hψ, neg_zero]
        exact Circle.coe_one
      exact h (by rw [hdiff, hphase, mul_one, sub_self])
    · by_contra! hy
      have hπnorm : ‖(π).val‖ = (q : ℝ)⁻¹ :=
        norm_finiteUniformizer F v _ (chosenFiniteUniformizer_spec F v)
      have hyD : (π).val * y ∉ D := by
        rw [finitePlaceIntegerAnnihilator_eq_differentBall]
        intro he
        change ‖(π).val * y‖ ≤ (q : ℝ) ^ d at he
        rw [norm_mul, hπnorm, inv_mul_le_iff₀ hqp, ← pow_succ'] at he
        exact hy.not_ge he
      have hz : Fourier (φ₁).val y = 0 := by
        change Fourier (fun x ↦ (φ).val ((π)⁻¹.val * x)) y = 0
        rw [Units.val_inv_eq_inv_val, finitePlaceTraceFourier_dilate F v ν]
        have hφ : (φ).val = (O : Set K).indicator (fun _ ↦ (1 : ℂ)) := rfl
        rw [hφ, finitePlaceTraceFourier_integerRing F v ν]
        simp only [indicator_of_notMem hyD, mul_zero, smul_zero]
      exact h (by rw [hdiff, hz, zero_mul, sub_zero])
  have hs (y : K) (hy : Fourier δ.val y ≠ 0) :
      finiteNormalizedLog F v y = (d : ℝ) + 1 := by
    obtain ⟨hl, hr⟩ := hors y hy
    have hy₀ : y ≠ 0 := by
      exact norm_ne_zero_iff.mp ((pow_pos hqp _).trans hl).ne'
    obtain ⟨n, hn⟩ : ∃ n : ℤ, ‖y‖ = (q : ℝ) ^ (-n) :=
      iUnion_eq_univ_iff.mp (finiteZetaShell_iUnion F v) (Units.mk0 y hy₀)
    have hl' : (d : ℤ) < -n :=
      (zpow_lt_zpow_iff_right₀ hq).mp (by simpa only [zpow_natCast, ← hn] using hl)
    have hr' : -n ≤ (d : ℤ) + 1 :=
      (zpow_le_zpow_iff_right₀ hq).mp (by simpa only [← Int.natCast_succ, zpow_natCast, ← hn] using hr)
    have he : -n = (d : ℤ) + 1 := by omega
    unfold finiteNormalizedLog
    rw [hn, he, Real.log_zpow, mul_div_cancel_right₀ _ (Real.log_pos hq).ne']
    push_cast
    rfl
  change (∫ y, (finiteNormalizedLog F v y : ℂ) * Fourier δ.val y ∂ν) = _
  calc
    _ = ∫ y, ((d : ℂ) + 1) * Fourier δ.val y ∂ν := by
      apply integral_congr_ae
      refine .of_forall fun y ↦ ?_
      change (finiteNormalizedLog F v y : ℂ) * Fourier δ.val y =
        ((d : ℂ) + 1) * Fourier δ.val y
      by_cases hy : Fourier δ.val y = 0
      · rw [hy, mul_zero, mul_zero]
      · rw [hs y hy, Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_one]
    _ = _ := by
      rw [integral_const_mul, integral_finitePlaceTraceFourier F v ν δ
        (finitePlace_tamagawa_fourier_normalization F v), htest0, mul_one]

/-- The logarithmic Fourier pairing on the weighted Weil lift of the unit
indicator evaluates to the exponent of the local different. -/
theorem finiteWeil_unitTest_logFourier :
    J (finiteWeilTest F v (finiteWeilUnitTest F v)) = (d : ℂ) := by
  rw [finiteWeilTest_unitTest]
  have h : φ - finiteTestTranslateAdd F v 1 φ₁ =
      finitePrincipalValue π φ + (φ₁ - finiteTestTranslateAdd F v 1 φ₁) := by
    change φ - finiteTestTranslateAdd F v 1 φ₁ =
      (φ - φ₁) + (φ₁ - finiteTestTranslateAdd F v 1 φ₁)
    abel
  rw [h, map_add, finiteLogFourierPairing_integerUnits,
    finiteLogFourierPairing_contractedTranslate_difference]
  ring

/-- A generator of the local codifferent, with respect to the chosen uniformizer. -/
def finiteWeilCodifferentGenerator : Kˣ := π ^ (-(d : ℤ))

omit [∀ w : HeightOneSpectrum (𝓞 F), MeasurableSpace (w.adicCompletion F)]
  [∀ w : HeightOneSpectrum (𝓞 F), BorelSpace (w.adicCompletion F)] in
private theorem finiteWeilCodifferentGenerator_norm :
    ‖(finiteWeilCodifferentGenerator F v).val‖ = (q : ℝ) ^ d := by
  unfold finiteWeilCodifferentGenerator
  rw [finitePlaceUniformizer_norm_zpow F v, neg_neg, zpow_natCast]

omit [∀ w : HeightOneSpectrum (𝓞 F), MeasurableSpace (w.adicCompletion F)]
  [∀ w : HeightOneSpectrum (𝓞 F), BorelSpace (w.adicCompletion F)] in
/-- Its principal ball is the trace-dual lattice of the local integers. -/
theorem finiteWeilCodifferentGenerator_traceDual (y : K) :
    let r := v.under (𝓞 ℚ)
    letI := (finiteCompletionMap ℚ F v).toAlgebra
    (∀ x ∈ (O : Set K),
      Algebra.trace (r.adicCompletion ℚ) K (x * y) ∈ r.adicCompletionIntegers ℚ) ↔
      y ∈ finiteWeilCodifferentGenerator F v • (O : Set K) := by
  have h := finitePlace_localTraceDual_eq_differentBall F v y
  dsimp only at h ⊢
  rw [h]
  rw [mem_smul_set_iff_inv_smul_mem, ← finiteCompletion_closedBall F v]
  change ‖y‖ ≤ (q : ℝ) ^ d ↔ dist ((finiteWeilCodifferentGenerator F v)⁻¹.val * y) 0 ≤ 1
  rw [dist_zero_right, Units.val_inv_eq_inv_val, norm_mul, norm_inv,
    finiteWeilCodifferentGenerator_norm]
  have hq : 0 < (q : ℝ) := by
    exact_mod_cast zero_lt_one.trans (NumberField.HeightOneSpectrum.one_lt_absNorm v)
  rw [inv_mul_le_iff₀ (pow_pos hq _), mul_one]

omit [∀ w : HeightOneSpectrum (𝓞 F), MeasurableSpace (w.adicCompletion F)]
  [∀ w : HeightOneSpectrum (𝓞 F), BorelSpace (w.adicCompletion F)] in
private theorem finiteWeilTest_ext {f g : Test} (h₀ : f.val (-1) = g.val (-1))
    (h : ∀ u : Kˣ, f.val (u.val - 1) = g.val (u.val - 1)) : f = g := by
  apply Subtype.ext
  funext x
  by_cases hx : 1 + x = 0
  · have hx' : x = -1 := by linear_combination hx
    rw [hx']
    exact h₀
  let u := Units.mk0 (1 + x) hx
  have hu : u.val - 1 = x := by change 1 + x - 1 = x; ring
  simpa only [hu] using h u

/-- The weighted additive lift used in the Weil principal value is linear. -/
def finiteWeilTestLinear : locallyConstantTests Kˣ →ₗ[ℂ] Test where
  toFun := finiteWeilTest F v
  map_add' f g := by
    apply finiteWeilTest_ext F v
    · change (finiteWeilTest F v (f + g)).val (-1) =
        (finiteWeilTest F v f).val (-1) + (finiteWeilTest F v g).val (-1)
      simp
    · intro u
      change (finiteWeilTest F v (f + g)).val (u.val - 1) =
        (finiteWeilTest F v f).val (u.val - 1) + (finiteWeilTest F v g).val (u.val - 1)
      simp only [finiteWeilTest_sub_one, Submodule.coe_add, Pi.add_apply, mul_add]
  map_smul' c f := by
    apply finiteWeilTest_ext F v
    · change (finiteWeilTest F v (c • f)).val (-1) = c * (finiteWeilTest F v f).val (-1)
      simp
    · intro u
      change (finiteWeilTest F v (c • f)).val (u.val - 1) =
        c * (finiteWeilTest F v f).val (u.val - 1)
      simp only [finiteWeilTest_sub_one, Submodule.coe_smul_of_tower, Pi.smul_apply, smul_eq_mul,
        mul_left_comm]

variable [MeasurableSpace (v.adicCompletion F)ˣ] [BorelSpace (v.adicCompletion F)ˣ]
  (μ : Measure (v.adicCompletion F)ˣ) [μ.IsHaarMeasure]
  (hμ : μ (finitePlaceIntegralUnits F v) =
    additiveHaarDifferent F v (v.adicCompletionIntegers F : Set (v.adicCompletion F)))

local notation "U" => finitePlaceIntegralUnits F v
local notation "m" => μ.real (finitePlaceIntegralUnits F v)
local notation "c" => Real.log (Ideal.absNorm v.asIdeal : ℝ) / μ.real (finitePlaceIntegralUnits F v)

omit [BorelSpace Kˣ] [μ.IsHaarMeasure] in
/-- At one, the multiplicative Weil principal value is a scalar times the
linear additive Fourier pairing of the lifted test. -/
theorem finiteWeilPrincipalValue_apply_linear (f : locallyConstantTests Kˣ) :
    finiteWeilPrincipalValue F v μ 1 f =
      -(m : ℂ) * J (finiteWeilTestLinear F v f) := by
  unfold finiteWeilPrincipalValue finiteConnesPrincipalValue
  simp only [Units.val_one, norm_one, one_smul, one_mul]
  rfl

omit [BorelSpace Kˣ] [μ.IsHaarMeasure] in
/-- The unit-indicator principal value vanishes at an unramified place. -/
theorem finiteWeil_unitTest_principalValue_of_not_dvd_different
    (hv : ¬ v.asIdeal ∣ differentIdeal ℤ (𝓞 F)) :
    finiteWeilPrincipalValue F v μ 1 (finiteWeilUnitTest F v) = 0 := by
  rw [finiteWeilPrincipalValue_apply_linear]
  change -(m : ℂ) * J (finiteWeilTest F v (finiteWeilUnitTest F v)) = 0
  rw [finiteWeil_unitTest_logFourier, multiplicity_eq_zero.mpr hv, Nat.cast_zero, mul_zero]

/-- The ordinary integrals in Weil's cutoff normalization for a finite place. -/
def finiteWeilCanonicalPrincipalValue (f : locallyConstantTests Kˣ) : ℂ :=
  c • (∫ u in Uᶜ, finiteWeilOrdinaryIntegrand F v f u ∂μ) +
    c • (∫ u in U, (‖u.val‖ ^ (1 / 2 : ℝ) / ‖1 - u.val‖ : ℝ) • (f.val u - f.val 1) ∂μ)

omit [∀ w : HeightOneSpectrum (𝓞 F), MeasurableSpace (w.adicCompletion F)]
  [∀ w : HeightOneSpectrum (𝓞 F), BorelSpace (w.adicCompletion F)]
  [MeasurableSpace Kˣ] [BorelSpace Kˣ] in
private theorem finiteWeil_subtractUnit_integrands (f : locallyConstantTests Kˣ) :
    (∀ u ∈ (U : Set Kˣ)ᶜ,
      finiteWeilOrdinaryIntegrand F v (finiteWeilSubtractUnitTest F v f) u =
        finiteWeilOrdinaryIntegrand F v f u) ∧
    (∀ u ∈ U, finiteWeilOrdinaryIntegrand F v (finiteWeilSubtractUnitTest F v f) u =
      (‖u.val‖ ^ (1 / 2 : ℝ) / ‖1 - u.val‖ : ℝ) • (f.val u - f.val 1)) := by
  have he (u : Kˣ) : (finiteWeilSubtractUnitTest F v f).val u =
      f.val u - f.val 1 * (U).indicator (fun _ ↦ (1 : ℂ)) u := rfl
  constructor
  · intro u hu
    unfold finiteWeilOrdinaryIntegrand
    rw [he, indicator_of_notMem hu, mul_zero, sub_zero]
  · intro u hu
    unfold finiteWeilOrdinaryIntegrand
    rw [he, indicator_of_mem hu, mul_one]

omit [∀ w : HeightOneSpectrum (𝓞 F), MeasurableSpace (w.adicCompletion F)]
  [∀ w : HeightOneSpectrum (𝓞 F), BorelSpace (w.adicCompletion F)] in
/-- Each cutoff integral converges absolutely on every multiplicative test. -/
theorem finiteWeilCanonicalPrincipalValue_integrable (f : locallyConstantTests Kˣ) :
    IntegrableOn (finiteWeilOrdinaryIntegrand F v f) (U : Set Kˣ)ᶜ μ ∧
    IntegrableOn (fun u : Kˣ ↦ (‖u.val‖ ^ (1 / 2 : ℝ) / ‖1 - u.val‖ : ℝ) •
      (f.val u - f.val 1)) U μ := by
  have hU := (localIntegralUnits_open F v).measurableSet
  have hi := finiteWeilOrdinary_integrable F v μ _ (finiteWeilSubtractUnitTest_one F v f)
  exact ⟨hi.integrableOn.congr_fun (finiteWeil_subtractUnit_integrands F v f).1 hU.compl,
    hi.integrableOn.congr_fun (finiteWeil_subtractUnit_integrands F v f).2 hU⟩

omit [∀ w : HeightOneSpectrum (𝓞 F), MeasurableSpace (w.adicCompletion F)]
  [∀ w : HeightOneSpectrum (𝓞 F), BorelSpace (w.adicCompletion F)] in
private theorem finiteWeilCanonicalPrincipalValue_eq_subtract (f : locallyConstantTests Kˣ) :
    finiteWeilCanonicalPrincipalValue F v μ f =
      c • ∫ u, finiteWeilOrdinaryIntegrand F v (finiteWeilSubtractUnitTest F v f) u ∂μ := by
  let g := finiteWeilSubtractUnitTest F v f
  have hU := (localIntegralUnits_open F v).measurableSet
  have hi := finiteWeilOrdinary_integrable F v μ g (finiteWeilSubtractUnitTest_one F v f)
  unfold finiteWeilCanonicalPrincipalValue
  rw [← smul_add, ← setIntegral_congr_fun hU.compl (finiteWeil_subtractUnit_integrands F v f).1,
    ← setIntegral_congr_fun hU (finiteWeil_subtractUnit_integrands F v f).2,
    add_comm, integral_add_compl hU hi]

include hμ in
/-- Lemma B.4.4.5 on the full compact locally constant multiplicative test
space, with the finite-place codifferent correction. -/
theorem finiteWeilPrincipalValue_canonical (f : locallyConstantTests Kˣ) :
    c • finiteWeilPrincipalValue F v μ 1 f =
      finiteWeilCanonicalPrincipalValue F v μ f -
        (Real.log ‖(finiteWeilCodifferentGenerator F v).val‖ : ℝ) • f.val 1 := by
  let g := finiteWeilSubtractUnitTest F v f
  let A := finiteWeilTestLinear F v
  have hf : f = g + f.val 1 • finiteWeilUnitTest F v := (sub_add_cancel _ _).symm
  have hP : finiteWeilPrincipalValue F v μ 1 f =
      finiteWeilPrincipalValue F v μ 1 g - (m : ℂ) * ((d : ℂ) * f.val 1) := by
    rw [finiteWeilPrincipalValue_apply_linear F v μ f,
      finiteWeilPrincipalValue_apply_linear F v μ g]
    change -(m : ℂ) * J (A f) = -(m : ℂ) * J (A g) - (m : ℂ) * ((d : ℂ) * f.val 1)
    nth_rw 1 [hf]
    rw [map_add, map_smul, map_add, map_smul]
    have he : J (A (finiteWeilUnitTest F v)) = (d : ℂ) := finiteWeil_unitTest_logFourier F v
    rw [he, smul_eq_mul]
    ring
  have hm : m ≠ 0 := (finiteIntegralUnits_real_pos F v μ).ne'
  rw [hP, finiteWeilCanonicalPrincipalValue_eq_subtract, ← finiteWeilPrincipalValue_eq_ordinary
    F v μ hμ g (finiteWeilSubtractUnitTest_one F v f), finiteWeilCodifferentGenerator_norm,
    Real.log_pow, smul_sub, sub_right_inj]
  simp only [Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_natCast, Complex.ofReal_div]
  have hm' : (m : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hm
  field_simp

end Tamagawa

end
end Masullo
