import FiniteLogFourier
import WeilPrincipalValue

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped ENNReal NNReal NumberField Pointwise

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
local notation "K" => v.adicCompletion F
local notation "Test" => locallyConstantTests K
local notation "π" => chosenFiniteUniformizer F v
local notation "φ" => finiteCompletionIntegerRingTest F v
local notation "T" => locallyConstantTestTranslate K

set_option maxHeartbeats 1500000

private theorem finiteIntegerTest_zero : (φ).val 0 = 1 := by
  change (v.adicCompletionIntegers F : Set K).indicator (fun _ ↦ (1 : ℂ)) 0 = 1
  exact indicator_of_mem (show (0 : K) ∈ v.adicCompletionIntegers F from zero_mem _) _

private theorem finiteIntegerTest_unitInvariant (u : (principalIntegralUnits F v)) :
    T u.val φ = φ := by
  classical
  apply Subtype.ext
  funext x
  have hrad : ∀ x y : K, ‖x‖ = ‖y‖ → (φ).val x = (φ).val y := by
    intro x y h
    change (v.adicCompletionIntegers F : Set K).indicator (fun _ ↦ (1 : ℂ)) x =
      (v.adicCompletionIntegers F : Set K).indicator (fun _ ↦ (1 : ℂ)) y
    simp only [← finiteCompletion_closedBall F v, indicator_apply, Metric.mem_closedBall,
      dist_zero_right, h]
  apply hrad
  change ‖u.val⁻¹.val * x‖ = ‖x‖
  have hu : ‖u.val.val‖ = 1 := u.property
  rw [norm_mul, Units.val_inv_eq_inv_val, norm_inv, hu, inv_one, one_mul]

/-- Subtract the germ value on the integer ring before restricting to the
multiplicative group, so the subtracted test has compact support there. -/
private def finiteSubtractIntegerTest : Test →ₗ[ℂ] Test where
  toFun f := f - f.val 0 • φ
  map_add' f g := by
    change f + g - (f.val 0 + g.val 0) • φ = (f - f.val 0 • φ) + (g - g.val 0 • φ)
    rw [add_smul]
    abel
  map_smul' c f := by
    change c • f - (c * f.val 0) • φ = c • (f - f.val 0 • φ)
    rw [smul_sub, mul_smul]

@[simp] private theorem finiteSubtractIntegerTest_zero (f : Test) :
    (finiteSubtractIntegerTest F v f).val 0 = 0 := by
  change f.val 0 - f.val 0 * (φ).val 0 = 0
  rw [finiteIntegerTest_zero, mul_one, sub_self]

private theorem locallyConstantTest_integrable_units_of_zero [MeasurableSpace (v.adicCompletion F)ˣ]
    [BorelSpace (v.adicCompletion F)ˣ] (μ : Measure Kˣ) [IsFiniteMeasureOnCompacts μ]
    (f : Test) (hf : f.val 0 = 0) : Integrable (fun u : Kˣ ↦ f.val u.val) μ := by
  let C := tsupport f.val
  have hC : IsCompact C := f.property.2
  have hzero : (0 : K) ∉ C := by
    rw [notMem_tsupport_iff_eventuallyEq]
    change ∀ᶠ x in 𝓝 (0 : K), f.val x = 0
    simpa only [hf] using f.property.1.eventually_eq 0
  have he : (Units.val : Kˣ → K) '' ((Units.val : Kˣ → K) ⁻¹' C) = C := by
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact hu
    · intro hx
      have hx₀ : x ≠ 0 := fun h ↦ hzero (h ▸ hx)
      exact ⟨Units.mk0 x hx₀, hx, rfl⟩
  have hCompact : IsCompact ((Units.val : Kˣ → K) ⁻¹' C) :=
    Units.isEmbedding_val₀.isCompact_iff.mpr (he.symm ▸ hC)
  exact (f.property.1.continuous.comp Units.continuous_val).integrable_of_hasCompactSupport
    (HasCompactSupport.intro hCompact fun _ hx ↦ image_eq_zero_of_notMem_tsupport (f := f.val) hx)

section Haar

variable [MeasurableSpace (v.adicCompletion F)ˣ] [BorelSpace (v.adicCompletion F)ˣ]
  (μ : Measure (v.adicCompletion F)ˣ) [μ.IsHaarMeasure]

private def finiteHaarRestrictionExtension : Test →ₗ[ℂ] ℂ where
  toFun f := ∫ u : Kˣ, (finiteSubtractIntegerTest F v f).val u.val ∂μ
  map_add' f g := by
    rw [map_add]
    exact integral_add (locallyConstantTest_integrable_units_of_zero F v μ _
      (finiteSubtractIntegerTest_zero F v f)) (locallyConstantTest_integrable_units_of_zero F v μ _
      (finiteSubtractIntegerTest_zero F v g))
  map_smul' c f := by
    rw [map_smul]
    exact integral_smul c _

private theorem finiteHaarRestrictionExtension_of_zero (f : Test) (hf : f.val 0 = 0) :
    finiteHaarRestrictionExtension F v μ f = ∫ u : Kˣ, f.val u.val ∂μ := by
  change (∫ u : Kˣ, (f - f.val 0 • φ).val u.val ∂μ) = _
  rw [hf, zero_smul, sub_zero]

private theorem finiteHaarRestrictionExtension_unitInvariant
    (u : principalIntegralUnits F v) (f : Test) :
    finiteHaarRestrictionExtension F v μ (T u.val f) =
      finiteHaarRestrictionExtension F v μ f := by
  let r := finiteSubtractIntegerTest F v
  have h0 : (T u.val f).val 0 = f.val 0 := by change f.val (_ * 0) = _; rw [mul_zero]
  have h : r (T u.val f) = T u.val (r f) := by
    change T u.val f - (T u.val f).val 0 • φ = T u.val (f - f.val 0 • φ)
    rw [map_sub, map_smul, finiteIntegerTest_unitInvariant, h0]
  change (∫ x : Kˣ, (r (T u.val f)).val x.val ∂μ) = _
  rw [h]
  exact integral_mul_left_eq_self (μ := μ) (fun x : Kˣ ↦ (r f).val x.val) u.val⁻¹

private theorem finiteHaarRestrictionExtension_uniformizer (f : Test) :
    finiteHaarRestrictionExtension F v μ f - finiteHaarRestrictionExtension F v μ (T π f) =
      f.val 0 * (μ.real (finitePlaceIntegralUnits F v) : ℂ) := by
  classical
  let r := finiteSubtractIntegerTest F v
  let e := finitePrincipalValue π φ
  have h0 : (T π f).val 0 = f.val 0 := by change f.val (_ * 0) = _; rw [mul_zero]
  have h : r (T π f) = T π (r f) - f.val 0 • e := by
    change T π f - (T π f).val 0 • φ =
      T π (f - f.val 0 • φ) - f.val 0 • (φ - T π φ)
    rw [map_sub, map_smul, h0, smul_sub]
    abel
  have hr0 : (T π (r f)).val 0 = 0 := by
    change (r f).val (_ * 0) = 0
    rw [mul_zero]
    exact finiteSubtractIntegerTest_zero F v f
  have he0 : (f.val 0 • e).val 0 = 0 := by
    change f.val 0 * e.val 0 = 0
    rw [finitePrincipalValue_eval_zero, mul_zero]
  have he (x : Kˣ) : e.val x.val =
      (finitePlaceIntegralUnits F v).indicator (fun _ ↦ (1 : ℂ)) x := by
    rw [finitePrincipalValue_integerRing_apply F v π (chosenFiniteUniformizer_spec F v)]
    simp only [indicator_apply, localIntegralUnits_value, finiteCompletion_norm_eq_one_iff]
  change (∫ x : Kˣ, (r f).val x.val ∂μ) - (∫ x : Kˣ, (r (T π f)).val x.val ∂μ) = _
  rw [h]
  have hsub := integral_sub (locallyConstantTest_integrable_units_of_zero F v μ _ hr0)
    (locallyConstantTest_integrable_units_of_zero F v μ _ he0)
  change _ - (∫ x : Kˣ, (T π (r f)).val x.val - (f.val 0 • e).val x.val ∂μ) = _
  rw [hsub]
  change _ - ((∫ x : Kˣ, (r f).val ((π)⁻¹ * x).val ∂μ) -
    (∫ x : Kˣ, f.val 0 • e.val x.val ∂μ)) = _
  rw [integral_mul_left_eq_self (μ := μ) (fun x : Kˣ ↦ (r f).val x.val) (π)⁻¹,
    sub_sub_cancel, integral_smul, smul_eq_mul]
  simp_rw [he]
  rw [integral_indicator (localIntegralUnits_open F v).measurableSet, setIntegral_const]
  simp

end Haar

section Additive

variable [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]
  (ν : Measure (v.adicCompletion F)) [ν.IsAddHaarMeasure]

omit [ν.IsAddHaarMeasure] in
private theorem integrable_mul_finiteTest (b : K → ℝ)
    (hb : ∀ C : Set K, IsCompact C → IntegrableOn b C ν) (f : Test) :
    Integrable (fun x ↦ (b x : ℂ) * f.val x) ν := by
  let C := tsupport f.val
  have hC : IsCompact C := f.property.2
  obtain ⟨M, hM⟩ := (hC.image f.property.1.continuous.norm).bddAbove
  have hI : IntegrableOn (fun x ↦ (b x : ℂ) * f.val x) C ν := by
    refine ((hb C hC).norm.const_mul M).mono' ?_ ?_
    · exact ((Complex.continuous_ofReal.comp_aestronglyMeasurable (hb C hC).aestronglyMeasurable).mul
        f.property.1.continuous.measurable.aestronglyMeasurable)
    · refine (ae_restrict_mem hC.measurableSet).mono fun x hx ↦ ?_
      rw [norm_mul, Complex.norm_real, mul_comm]
      exact mul_le_mul_of_nonneg_right (hM ⟨x, hx, rfl⟩) (norm_nonneg _)
  refine ((integrable_indicator_iff hC.measurableSet).mpr hI).congr (.of_forall fun x ↦ ?_)
  by_cases hx : x ∈ C
  · exact indicator_of_mem hx _
  · rw [indicator_of_notMem hx]
    change 0 = (b x : ℂ) * f.val x
    rw [image_eq_zero_of_notMem_tsupport (f := f.val) hx, mul_zero]

private def finiteRealFourierPairing (b : K → ℝ)
    (hb : ∀ C : Set K, IsCompact C → IntegrableOn b C ν) : Test →ₗ[ℂ] ℂ where
  toFun f := ∫ y, (b y : ℂ) * finitePlaceTraceFourier F v ν f.val y ∂ν
  map_add' f g := by
    have h (y : K) : finitePlaceTraceFourier F v ν (f + g).val y =
        finitePlaceTraceFourier F v ν f.val y + finitePlaceTraceFourier F v ν g.val y := by
      unfold finitePlaceTraceFourier
      change (∫ x, (f.val x + g.val x) * _ ∂ν) = _
      simp only [add_mul]
      exact integral_add (finitePlace_integrable_mul_traceCharacter F v ν f y)
        (finitePlace_integrable_mul_traceCharacter F v ν g y)
    simp only [h, mul_add]
    exact integral_add (integrable_mul_finiteTest F v ν b hb (finitePlaceFourierTest F v ν f))
      (integrable_mul_finiteTest F v ν b hb (finitePlaceFourierTest F v ν g))
  map_smul' c f := by
    have h (y : K) : finitePlaceTraceFourier F v ν (c • f).val y =
        c * finitePlaceTraceFourier F v ν f.val y := by
      unfold finitePlaceTraceFourier
      change (∫ x, (c * f.val x) * _ ∂ν) = _
      simp only [mul_assoc, integral_const_mul]
    simp only [h, mul_left_comm _ c, integral_const_mul, smul_eq_mul, RingHom.id_apply]

/-- The Fourier transform of the normalized logarithm, evaluated on finite-place
Schwartz–Bruhat tests. -/
def finiteLogFourierPairing : Test →ₗ[ℂ] ℂ :=
  finiteRealFourierPairing F v ν (finiteNormalizedLog F v)
    (finiteNormalizedLog_integrableOn_compact F v ν)

/-- The logarithmic Fourier pairing is a tempered distribution on the
finite-place Schwartz–Bruhat test space. -/
theorem finiteLogFourierPairing_continuous :
    letI : TopologicalSpace Test := finestLocallyConvexTopology Test
    Continuous (finiteLogFourierPairing F v ν) := by
  letI : TopologicalSpace Test := finestLocallyConvexTopology Test
  exact finest_linear_continuous _

private theorem finiteLogFourierPairing_translate
    (hν : ν.real (v.adicCompletionIntegers F : Set K) *
      ν.real (finitePlaceIntegerAnnihilator F v) = 1) (a : Kˣ) (f : Test) :
    finiteLogFourierPairing F v ν (T a f) = finiteLogFourierPairing F v ν f -
      (finiteNormalizedLog F v a.val : ℂ) * f.val 0 := by
  change (∫ y, (finiteNormalizedLog F v y : ℂ) *
    finitePlaceTraceFourier F v ν (fun x ↦ f.val ((a⁻¹).val * x)) y ∂ν) = _
  simp only [Units.val_inv_eq_inv_val]
  exact finitePlace_logFourier_dilate F v ν hν a f

omit [MeasurableSpace K] [BorelSpace K] in
private theorem exists_compactOpen_finitePlace {W : Set K} {x : K} (hW : W ∈ 𝓝 x) :
    ∃ C : Set K, IsCompact C ∧ IsOpen C ∧ x ∈ C ∧ C ⊆ W := by
  let t := Homeomorph.addRight x
  have hWT : t ⁻¹' W ∈ 𝓝 (0 : K) := by
    apply t.continuous.continuousAt.tendsto
    simpa only [show t 0 = x from zero_add x] using hW
  obtain ⟨a, ha⟩ := exists_small_integral_dilate F v hWT
  let e := (Homeomorph.smul a).trans t
  let O₀ : Set K := v.adicCompletionIntegers F
  have h0 : e 0 = x := by change a.val * 0 + x = x; rw [mul_zero, zero_add]
  refine ⟨e '' O₀, (finitePlaceIntegral_compact F v).image e.continuous,
    e.isOpenMap _ (Valued.isOpen_valuationSubring K), ⟨0, zero_mem _, h0⟩, ?_⟩
  rintro y ⟨z, hz, rfl⟩
  exact ha (mem_smul_set.mpr ⟨z, hz, rfl⟩)

private theorem finiteTest_separates_off_zero (b : K → ℝ) (hb : ContinuousOn b ({0}ᶜ : Set K))
    (hi : ∀ C : Set K, IsCompact C → IntegrableOn b C ν)
    (hvanish : ∀ C : Set K, IsCompact C → IsOpen C → (∫ x in C, b x ∂ν) = 0) :
    ∀ x : K, x ≠ 0 → b x = 0 := by
  intro x hx
  by_contra hn
  let d := b x * b x / 2
  have hd : 0 < d := div_pos (mul_self_pos.mpr hn) two_pos
  have hcont : ContinuousAt b x :=
    (hb x hx).continuousAt (isClosed_singleton.isOpen_compl.mem_nhds hx)
  have hdx : d < b x * b x := by
    have hsq := mul_self_pos.mpr hn
    dsimp [d]
    linarith
  have hmem : {y : K | d < b y * b x} ∈ 𝓝 x :=
    ((hcont.mul continuousAt_const).tendsto.eventually (Ioi_mem_nhds hdx))
  obtain ⟨C, hC, hCo, hxC, hsub⟩ := exists_compactOpen_finitePlace F v hmem
  have hz : (∫ y in C, b y ∂ν) = 0 := hvanish C hC hCo
  have hmono : (∫ y in C, d ∂ν) ≤ ∫ y in C, b y * b x ∂ν := by
    haveI : IsFiniteMeasure ((ν).restrict C) := ⟨by simpa using hC.measure_lt_top (μ := ν)⟩
    exact integral_mono_ae (integrable_const _) ((hi C hC).mul_const _) <|
      (ae_restrict_mem hCo.measurableSet).mono fun y hy ↦ (hsub hy).le
  rw [integral_mul_const, hz, zero_mul, setIntegral_const, smul_eq_mul] at hmono
  have hpos : 0 < (ν).real C :=
    ENNReal.toReal_pos (hCo.measure_ne_zero ν ⟨x, hxC⟩) hC.measure_lt_top.ne
  exact (mul_pos hpos hd).not_ge hmono

omit [MeasurableSpace K] [BorelSpace K] in
private theorem finiteNormalizedLog_uniformizer : finiteNormalizedLog F v (π).val = -1 := by
  have hq : (1 : ℝ) < v.asIdeal.absNorm := by
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  unfold finiteNormalizedLog
  rw [norm_finiteUniformizer F v _ (chosenFiniteUniformizer_spec F v), Real.log_inv,
    neg_div, div_self (Real.log_pos hq).ne']

omit [MeasurableSpace K] [BorelSpace K] in
/-- The normalized logarithm is a distribution represented by a locally
integrable function. No choice of value at zero makes it a test function. -/
theorem finiteNormalizedLog_no_locallyConstant_extension (g : K → ℝ)
    (hg : ∀ x : K, x ≠ 0 → g x = finiteNormalizedLog F v x) :
    ¬ IsLocallyConstant g := by
  intro h
  let p : K := (π).val
  have hp : ‖p‖ < 1 := finiteCompletion_uniformizer_contracts F v π
    (chosenFiniteUniformizer_spec F v)
  have hval (n : ℕ) : finiteNormalizedLog F v (p ^ n) = -(n : ℝ) := by
    have hlog : Real.log ‖p‖ / Real.log (v.asIdeal.absNorm : ℝ) = -1 :=
      finiteNormalizedLog_uniformizer F v
    unfold finiteNormalizedLog
    rw [norm_pow, Real.log_pow, mul_div_assoc, hlog, mul_neg_one]
  obtain ⟨n, hn⟩ := eventually_atTop.mp <|
    (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hp).eventually (h.eventually_eq 0)
  have h₀ := hn n le_rfl
  have h₁ := hn (n + 1) (Nat.le_succ n)
  change g (p ^ n) = g 0 at h₀
  change g (p ^ (n + 1)) = g 0 at h₁
  rw [hg (p ^ n) (pow_ne_zero _ (π).ne_zero), hval] at h₀
  rw [hg (p ^ (n + 1)) (pow_ne_zero _ (π).ne_zero), hval] at h₁
  push_cast at h₁
  linarith

omit [MeasurableSpace K] [BorelSpace K] in
theorem finiteNormalizedLog_not_locallyConstant :
    ¬ IsLocallyConstant (finiteNormalizedLog F v) :=
  finiteNormalizedLog_no_locallyConstant_extension F v _ (fun _ _ ↦ rfl)

end Additive

section Tamagawa

variable [∀ w : HeightOneSpectrum (𝓞 F), MeasurableSpace (w.adicCompletion F)]
  [∀ w : HeightOneSpectrum (𝓞 F), BorelSpace (w.adicCompletion F)]
  [MeasurableSpace (v.adicCompletion F)ˣ] [BorelSpace (v.adicCompletion F)ˣ]
  (μ : Measure (v.adicCompletion F)ˣ) [μ.IsHaarMeasure]

local notation "ν" => additiveHaarDifferent F v
local instance : (ν).IsAddHaarMeasure := additiveHaarDifferent_isHaar F v

omit [MeasurableSpace (v.adicCompletion F)ˣ] [BorelSpace (v.adicCompletion F)ˣ] in
/-- Every finite local test has an exact preimage for the Tamagawa Fourier
transform. The inverse is Fourier transformation after reflection. -/
theorem finitePlaceFourierTest_tamagawa_surjective :
    Function.Surjective (finitePlaceFourierTest F v ν) := by
  intro f
  let e := Homeomorph.neg K
  let r : Test := ⟨f.val ∘ e, f.property.1.comp_continuous e.continuous,
    f.property.2.comp_homeomorph e⟩
  refine ⟨finitePlaceFourierTest F v ν r, Subtype.ext (funext fun x ↦ ?_)⟩
  rw [finitePlaceFourierTest_twice F v ν (finitePlace_tamagawa_fourier_normalization F v)]
  change f.val (- -x) = f.val x
  rw [neg_neg]

omit [MeasurableSpace Kˣ] [BorelSpace Kˣ] in
/-- The adjoint dilation identity of Proposition B.4.3.1 for the standard
local additive Tamagawa measure. -/
theorem finiteLogFourierPairing_tamagawa_translate (a : Kˣ) (f : Test) :
    finiteLogFourierPairing F v ν (T a f) = finiteLogFourierPairing F v ν f -
      (finiteNormalizedLog F v a.val : ℂ) * f.val 0 :=
  finiteLogFourierPairing_translate F v ν (finitePlace_tamagawa_fourier_normalization F v) a f

omit [MeasurableSpace Kˣ] [BorelSpace Kˣ] in
/-- The exact value of the logarithmic Fourier pairing on the unit shell. -/
theorem finiteLogFourierPairing_integerUnits :
    finiteLogFourierPairing F v ν (finitePrincipalValue π φ) = -1 := by
  let J := finiteLogFourierPairing F v ν
  change J (φ - T π φ) = -1
  rw [map_sub, show J (T π φ) = J φ - (finiteNormalizedLog F v (π).val : ℂ) * (φ).val 0
    from finiteLogFourierPairing_tamagawa_translate F v π φ,
    finiteNormalizedLog_uniformizer, finiteIntegerTest_zero, mul_one, sub_sub_cancel]
  simp

omit [∀ w : HeightOneSpectrum (𝓞 F), MeasurableSpace (w.adicCompletion F)]
  [∀ w : HeightOneSpectrum (𝓞 F), BorelSpace (w.adicCompletion F)] [BorelSpace Kˣ] in
theorem finiteIntegralUnits_real_pos :
    0 < μ.real (finitePlaceIntegralUnits F v) := by
  have hU : (finitePlaceIntegralUnits F v).Nonempty :=
    ⟨1, (v.adicCompletionIntegers F).toSubmonoid.units.one_mem⟩
  have hc : IsCompact (finitePlaceIntegralUnits F v) :=
    Submonoid.units_isCompact (S := (v.adicCompletionIntegers F).toSubmonoid)
      (finitePlaceIntegral_compact F v)
  exact ENNReal.toReal_pos ((localIntegralUnits_open F v).measure_ne_zero μ hU)
    hc.measure_lt_top.ne

/-- The punctured restriction of the logarithmic Fourier pairing is negative
multiplicative Haar integration divided by the mass of the integral units. -/
theorem finiteLogFourierPairing_eq_mulHaar_of_zero (f : Test) (hf : f.val 0 = 0) :
    finiteLogFourierPairing F v ν f =
      -(∫ u : Kˣ, f.val u.val ∂μ) / (μ.real (finitePlaceIntegralUnits F v) : ℂ) := by
  let J := finiteLogFourierPairing F v ν
  let H := finiteHaarRestrictionExtension F v μ
  let m : ℂ := μ.real (finitePlaceIntegralUnits F v)
  have hm : m ≠ 0 := Complex.ofReal_ne_zero.mpr (finiteIntegralUnits_real_pos F v μ).ne'
  let L : Test →ₗ[ℂ] ℂ := H + m • J
  have hn := finitePlace_tamagawa_fourier_normalization F v
  have hJ (a : Kˣ) (g : Test) : J (T a g) = J g - (finiteNormalizedLog F v a.val : ℂ) * g.val 0 :=
    finiteLogFourierPairing_translate F v ν hn a g
  have hU (u : principalIntegralUnits F v) (g : Test) : L (principalUnitAction F v u g) = L g := by
    have hu : ‖u.val.val‖ = 1 := u.property
    have hu₀ : finiteNormalizedLog F v u.val.val = 0 := by simp [finiteNormalizedLog, hu]
    change H (T u.val g) + m * J (T u.val g) = H g + m * J g
    rw [finiteHaarRestrictionExtension_unitInvariant, hJ, hu₀, Complex.ofReal_zero,
      zero_mul, sub_zero]
  have hπ (g : Test) : L (T π g) = L g := by
    have hh : H g - H (T π g) = g.val 0 * m :=
      finiteHaarRestrictionExtension_uniformizer F v μ g
    change H (T π g) + m * J (T π g) = H g + m * J g
    rw [hJ, finiteNormalizedLog_uniformizer, Complex.ofReal_neg, Complex.ofReal_one,
      sub_eq_iff_eq_add.mp hh]
    ring
  have hA (g : Test) : L (principalUnitAverage F v g) = L g := by
    rw [principalUnitAverage_apply]
    simp only [hU, integral_const, measureReal_def, principalUnitHaar_univ,
      ENNReal.toReal_one, one_smul]
  obtain ⟨g, rfl⟩ := (Set.ext_iff.mp (weilPrincipalValue_range F v) f).mpr hf
  have hL : L (weilPrincipalValue F v g) = 0 := by
    change L (g - T π (principalUnitAverage F v g)) = 0
    rw [map_sub, hπ, hA, sub_self]
  change H (weilPrincipalValue F v g) + m * J (weilPrincipalValue F v g) = 0 at hL
  change J (weilPrincipalValue F v g) = -_ / m
  apply (eq_div_iff hm).mpr
  rw [mul_comm, ← finiteHaarRestrictionExtension_of_zero F v μ _ hf]
  exact eq_neg_of_add_eq_zero_left (by simpa only [add_comm] using hL)

/-- At the standard character the principal value of an additive test
vanishing at the origin is its ordinary multiplicative Haar integral. -/
theorem finiteConnesPrincipalValue_eq_mulHaar_of_zero (f : Test) (hf : f.val 0 = 0) :
    finiteConnesPrincipalValue F v ν μ 1 f = ∫ u : Kˣ, f.val u.val ∂μ := by
  have hm : (μ.real (finitePlaceIntegralUnits F v) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (finiteIntegralUnits_real_pos F v μ).ne'
  unfold finiteConnesPrincipalValue
  simp only [Units.val_one, norm_one, one_smul, one_mul]
  change -(μ.real (finitePlaceIntegralUnits F v) : ℂ) * finiteLogFourierPairing F v ν f = _
  rw [finiteLogFourierPairing_eq_mulHaar_of_zero F v μ f hf, neg_div, neg_mul_neg,
    mul_div_left_comm, div_self hm, mul_one]

/-- The locally integrable real function whose Fourier pairing has the
prescribed punctured restriction is unique off zero when continuous there
and normalized at one. -/
theorem finiteNormalizedLog_unique (g : K → ℝ)
    (hg : ∀ C : Set K, IsCompact C → IntegrableOn g C ν)
    (hc : ContinuousOn g ({0}ᶜ : Set K)) (h₁ : g 1 = 0)
    (hrest : ∀ f : Test, f.val 0 = 0 →
      (∫ x, (g x : ℂ) * finitePlaceTraceFourier F v ν f.val x ∂ν) =
        -(∫ u : Kˣ, f.val u.val ∂μ) / (μ.real (finitePlaceIntegralUnits F v) : ℂ)) :
    ∀ x : K, x ≠ 0 → g x = finiteNormalizedLog F v x := by
  let J := finiteNormalizedLog F v
  let L := finiteRealFourierPairing F v ν g hg - finiteLogFourierPairing F v ν
  have hL (f : Test) (hf : f.val 0 = 0) : L f = 0 := by
    change (∫ x, (g x : ℂ) * finitePlaceTraceFourier F v ν f.val x ∂ν) -
      finiteLogFourierPairing F v ν f = 0
    rw [hrest f hf, finiteLogFourierPairing_eq_mulHaar_of_zero F v μ f hf, sub_self]
  have hL' (f : Test) : L f = f.val 0 * L φ := by
    have h := hL (finiteSubtractIntegerTest F v f) (finiteSubtractIntegerTest_zero F v f)
    change L (f - f.val 0 • φ) = 0 at h
    rwa [map_sub, map_smul, smul_eq_mul, sub_eq_zero] at h
  let c := (L φ).re
  let b (x : K) := g x - J x - c
  have hJ : ContinuousOn J ({0}ᶜ : Set K) := by
    intro x hx
    have hlog := (Real.continuousAt_log (norm_ne_zero_iff.mpr (show x ≠ 0 from hx))).comp
      (continuous_norm.continuousAt (x := x))
    exact (hlog.div_const _).continuousWithinAt
  have hb : ContinuousOn b ({0}ᶜ : Set K) := (hc.sub hJ).sub continuousOn_const
  have hbi (C : Set K) (hC : IsCompact C) : IntegrableOn b C ν := by
    haveI : IsFiniteMeasure ((ν).restrict C) := ⟨by simpa using hC.measure_lt_top (μ := ν)⟩
    exact ((hg C hC).sub (finiteNormalizedLog_integrableOn_compact F v ν C hC)).sub
      (integrable_const _)
  have hpair (f : Test) :
      (∫ x, (g x : ℂ) * f.val x ∂ν) - (∫ x, (J x : ℂ) * f.val x ∂ν) =
        (∫ x, f.val x ∂ν) * L φ := by
    obtain ⟨u, hu⟩ := finitePlaceFourierTest_tamagawa_surjective F v f
    have hn := finitePlace_tamagawa_fourier_normalization F v
    have hu0 : u.val 0 = ∫ x, f.val x ∂ν := by
      rw [← hu]
      exact (integral_finitePlaceTraceFourier F v ν u hn).symm
    have h := hL' u
    change (∫ x, (g x : ℂ) * (finitePlaceFourierTest F v ν u).val x ∂ν) -
      (∫ x, (J x : ℂ) * (finitePlaceFourierTest F v ν u).val x ∂ν) = u.val 0 * L φ at h
    rw [hu, hu0] at h
    exact h
  have hvanish (C : Set K) (hC : IsCompact C) (hCo : IsOpen C) : (∫ x in C, b x ∂ν) = 0 := by
    let f := compactOpenIndicator K ⟨C, hC, hCo⟩
    have hi (a : K → ℝ) :
        (∫ x, (a x : ℂ) * f.val x ∂ν) = ∫ x in C, (a x : ℂ) ∂ν := by
      rw [← integral_indicator hCo.measurableSet]
      apply integral_congr_ae
      refine .of_forall fun x ↦ ?_
      change (a x : ℂ) * C.indicator (fun _ ↦ (1 : ℂ)) x = C.indicator (fun y ↦ (a y : ℂ)) x
      by_cases hx : x ∈ C
      · rw [indicator_of_mem hx, indicator_of_mem hx, mul_one]
      · rw [indicator_of_notMem hx, indicator_of_notMem hx, mul_zero]
    have hz : (∫ x, f.val x ∂ν) = ((ν).real C : ℂ) := by
      change (∫ x, C.indicator (fun _ ↦ (1 : ℂ)) x ∂ν) = _
      rw [integral_indicator hCo.measurableSet, setIntegral_const]
      simp
    have h := hpair f
    rw [hi g, hi J, hz, integral_complex_ofReal, integral_complex_ofReal] at h
    have hr := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      zero_mul, sub_zero] at hr
    haveI : IsFiniteMeasure ((ν).restrict C) := ⟨by simpa using hC.measure_lt_top (μ := ν)⟩
    have hj : IntegrableOn J C ν := finiteNormalizedLog_integrableOn_compact F v ν C hC
    have hs : IntegrableOn (fun x : K ↦ g x - J x) C ν := (hg C hC).sub hj
    change (∫ x in C, (g x - J x) - c ∂ν) = 0
    rw [integral_sub hs (integrable_const c), integral_sub (hg C hC) hj, setIntegral_const,
      smul_eq_mul]
    exact sub_eq_zero.mpr hr
  have hz := finiteTest_separates_off_zero F v ν b hb hbi hvanish
  have hc₀ : c = 0 := by
    have h := hz 1 one_ne_zero
    change g 1 - J 1 - c = 0 at h
    simpa [h₁, J, finiteNormalizedLog] using h
  intro x hx
  have h := hz x hx
  change g x - J x - c = 0 at h
  simpa only [hc₀, sub_zero, sub_eq_zero] using h

end Tamagawa

end
end Masullo
