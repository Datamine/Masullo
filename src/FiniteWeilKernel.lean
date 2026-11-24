import FiniteLogFourierHaar

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped ENNReal NNReal NumberField Pointwise

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
local notation "K" => v.adicCompletion F
local notation "Tests" => locallyConstantTests Kˣ
local notation "U" => finitePlaceIntegralUnits F v

set_option maxHeartbeats 1500000

/-- Extend a function on nonzero elements by zero at the origin. -/
def finiteUnitExtension (g : Kˣ → ℂ) (x : K) : ℂ := by
  classical
  exact if h : x ≠ 0 then g (Units.mk0 x h) else 0

@[simp] theorem finiteUnitExtension_val (g : Kˣ → ℂ) (u : Kˣ) :
    finiteUnitExtension F v g u.val = g u := by
  unfold finiteUnitExtension
  rw [dite_eq_left u.ne_zero, Units.mk0_val]

private theorem finiteUnits_range : range (Units.val : Kˣ → K) = ({0}ᶜ : Set K) := by
  ext x
  refine ⟨?_, ?_⟩
  · rintro ⟨u, rfl⟩
    exact u.ne_zero
  · intro hx
    exact ⟨Units.mk0 x hx, rfl⟩

private theorem finiteUnitExtension_zero (g : Kˣ → ℂ) : finiteUnitExtension F v g 0 = 0 := by
  simp [finiteUnitExtension]

section Tamagawa

variable [∀ w : HeightOneSpectrum (𝓞 F), MeasurableSpace (w.adicCompletion F)]
  [∀ w : HeightOneSpectrum (𝓞 F), BorelSpace (w.adicCompletion F)]
  [MeasurableSpace (v.adicCompletion F)ˣ] [BorelSpace (v.adicCompletion F)ˣ]
  (μ : Measure (v.adicCompletion F)ˣ) [μ.IsHaarMeasure]

local notation "ν" => additiveHaarDifferent F v
local notation "q" => Ideal.absNorm v.asIdeal

local instance : (ν).IsAddHaarMeasure := additiveHaarDifferent_isHaar F v

omit [∀ w : HeightOneSpectrum (𝓞 F), MeasurableSpace (w.adicCompletion F)]
  [∀ w : HeightOneSpectrum (𝓞 F), BorelSpace (w.adicCompletion F)]
  [MeasurableSpace Kˣ] [BorelSpace Kˣ] in
/-- The real and measure-valued Tamagawa density coefficients coincide. -/
private theorem finitePlace_density_toReal :
    ((q : ℝ≥0∞) / (q - 1 : ℝ≥0∞)).toReal = (q : ℝ) / ((q : ℝ) - 1) := by
  have hq : (1 : ℝ≥0∞) ≤ q := by
    exact_mod_cast (NumberField.HeightOneSpectrum.one_lt_absNorm v).le
  rw [ENNReal.toReal_div, ENNReal.toReal_sub_of_le hq (ENNReal.natCast_ne_top _)]
  simp

private theorem finitePlace_unitEmbedding :
    MeasurableEmbedding (Units.val : Kˣ → K) :=
  IsOpenUnits.isOpenEmbedding_unitsVal.measurableEmbedding

private theorem finitePlace_map_unit_comap : ((ν).comap (Units.val : Kˣ → K)).map Units.val = ν := by
  rw [(finitePlace_unitEmbedding F v).map_comap, finiteUnits_range F v]
  apply Measure.restrict_eq_self_of_ae_mem
  rw [ae_iff]
  simpa only [mem_compl_iff, not_not, ofPred_mem_eq] using finitePlace_measure_singleton_zero F v ν

omit [∀ w : HeightOneSpectrum (𝓞 F), MeasurableSpace (w.adicCompletion F)]
  [∀ w : HeightOneSpectrum (𝓞 F), BorelSpace (w.adicCompletion F)]
  [MeasurableSpace Kˣ] [BorelSpace Kˣ] in
private theorem finitePlace_reciprocalWeight
    (u : Kˣ) : ((‖u.val‖₊ : ℝ≥0∞)⁻¹).toReal = ‖u.val‖⁻¹ := by
  rw [ENNReal.toReal_inv, ENNReal.coe_toReal, coe_nnnorm]

omit [∀ w : HeightOneSpectrum (𝓞 F), MeasurableSpace (w.adicCompletion F)]
  [∀ w : HeightOneSpectrum (𝓞 F), BorelSpace (w.adicCompletion F)] in
private theorem finitePlace_reciprocalWeight_measurable :
    Measurable (fun u : Kˣ ↦ (‖u.val‖₊ : ℝ≥0∞)⁻¹) :=
  (measurable_coe_nnreal_ennreal.comp (continuous_nnnorm.comp Units.continuous_val).measurable).inv

omit [∀ w : HeightOneSpectrum (𝓞 F), MeasurableSpace (w.adicCompletion F)]
  [∀ w : HeightOneSpectrum (𝓞 F), BorelSpace (w.adicCompletion F)]
  [MeasurableSpace Kˣ] [BorelSpace Kˣ] in
private theorem finitePlace_reciprocalWeight_finite (u : Kˣ) : (‖u.val‖₊ : ℝ≥0∞)⁻¹ < ∞ := by
  exact ENNReal.inv_lt_top.mpr (by exact_mod_cast u.nnnorm_pos)

variable (hμ : μ (finitePlaceIntegralUnits F v) =
  additiveHaarDifferent F v (v.adicCompletionIntegers F : Set (v.adicCompletion F)))

include hμ in
/-- Multiplicative Tamagawa integrals in additive coordinates. -/
theorem finitePlace_tamagawa_integral_units (g : K → ℂ) :
    (∫ u : Kˣ, g u.val ∂μ) =
      ((q : ℝ) / ((q : ℝ) - 1)) • ∫ x : K, ‖x‖⁻¹ • g x ∂ν := by
  rw [finitePlaceTamagawa_density F v ν μ hμ, integral_smul_measure,
    finitePlace_density_toReal F v]
  unfold finitePlaceUnitDensity
  rw [integral_withDensity_eq_integral_toReal_smul (finitePlace_reciprocalWeight_measurable F v)
    (.of_forall (finitePlace_reciprocalWeight_finite F v))]
  simp only [finitePlace_reciprocalWeight]
  congr 1
  have h := (finitePlace_unitEmbedding F v).integral_map
    (μ := (ν).comap Units.val) (fun x : K ↦ ‖x‖⁻¹ • g x)
  rw [finitePlace_map_unit_comap F v] at h
  exact h.symm

/-- The ordinary weighted integrand of (B.4.4.5). -/
def finiteWeilOrdinaryIntegrand (f : Tests) (u : Kˣ) : ℂ :=
  (‖u.val‖ ^ (1 / 2 : ℝ) / ‖1 - u.val‖ : ℝ) • f.val u

/-- The density prescribed for the distribution in (B.4.4.6) on tests
vanishing at one. -/
def finiteWeilDensityIntegral (f : Tests) : ℂ :=
  ((q : ℝ) / ((q : ℝ) - 1)) •
    ∫ x : K, ‖1 - x‖⁻¹ • finiteUnitExtension F v f.val x ∂ν

omit [MeasurableSpace Kˣ] [BorelSpace Kˣ] in
private theorem finiteWeil_translated_integrand_ae (f : Tests) :
    (fun y : K ↦ ‖y - 1‖⁻¹ • (finiteWeilTest F v f).val (y - 1)) =ᵐ[ν]
      (fun y : K ↦ ‖y‖⁻¹ • finiteUnitExtension F v (finiteWeilOrdinaryIntegrand F v f) y) := by
  have hzero : ∀ᵐ y : K ∂ν, y ≠ 0 := ae_iff.mpr (by
    simpa only [not_not, ofPred_eq_eq_singleton] using finitePlace_measure_singleton_zero F v ν)
  filter_upwards [hzero] with y hy
  let u := Units.mk0 y hy
  change ‖u.val - 1‖⁻¹ • (finiteWeilTest F v f).val (u.val - 1) =
    ‖u.val‖⁻¹ • finiteUnitExtension F v (finiteWeilOrdinaryIntegrand F v f) u.val
  rw [finiteWeilTest_sub_one, finiteUnitExtension_val, finiteWeilOrdinaryIntegrand, norm_sub_rev]
  rw [← Complex.real_smul, smul_smul, smul_smul]
  have hpow : ‖u.val‖ ^ (-1 / 2 : ℝ) * ‖u.val‖ = ‖u.val‖ ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_add_one (norm_ne_zero_iff.mpr u.ne_zero)]
    congr 1
    norm_num
  congr 1
  rw [← hpow]
  have hm : ‖u.val‖ ≠ 0 := norm_ne_zero_iff.mpr u.ne_zero
  let p : ℝ := ‖u.val‖ ^ (-1 / 2 : ℝ)
  change ‖1 - u.val‖⁻¹ * p = ‖u.val‖⁻¹ * (p * ‖u.val‖ / ‖1 - u.val‖)
  calc
    _ = ‖1 - u.val‖⁻¹ * p * (‖u.val‖⁻¹ * ‖u.val‖) := by rw [inv_mul_cancel₀ hm, mul_one]
    _ = _ := by simp only [div_eq_mul_inv]; ring

include hμ in
/-- The first formula of Lemma B.4.4.3, with its Weil principal value. -/
theorem finiteWeilPrincipalValue_eq_ordinary (f : Tests) (hf : f.val 1 = 0) :
    finiteWeilPrincipalValue F v μ 1 f = ∫ u, finiteWeilOrdinaryIntegrand F v f u ∂μ := by
  unfold finiteWeilPrincipalValue
  have ho := finitePlace_tamagawa_integral_units F v μ hμ
    (finiteUnitExtension F v (finiteWeilOrdinaryIntegrand F v f))
  simp only [finiteUnitExtension_val] at ho
  rw [finiteConnesPrincipalValue_eq_mulHaar_of_zero F v μ _ ((finiteWeilTest_zero F v f).trans hf),
    finitePlace_tamagawa_integral_units F v μ hμ, ho]
  congr 1
  let k (x : K) := ‖x‖⁻¹ • (finiteWeilTest F v f).val x
  have ht : (fun y : K ↦ k (y + -1)) =ᵐ[ν]
      (fun y : K ↦ ‖y‖⁻¹ • finiteUnitExtension F v (finiteWeilOrdinaryIntegrand F v f) y) := by
    simpa only [k, sub_eq_add_neg] using finiteWeil_translated_integrand_ae F v f
  calc
    _ = ∫ y : K, k (y + -1) ∂ν := (integral_add_right_eq_self (μ := ν) k (-1)).symm
    _ = _ := integral_congr_ae ht

omit [∀ w : HeightOneSpectrum (𝓞 F), MeasurableSpace (w.adicCompletion F)]
  [∀ w : HeightOneSpectrum (𝓞 F), BorelSpace (w.adicCompletion F)] in
private theorem finiteWeil_integrable_of_zero (w : Kˣ → ℝ) (hw : Continuous w)
    (f : Tests) (hf : f.val 1 = 0) :
    Integrable (fun u : Kˣ ↦ (w u / ‖1 - u.val‖ : ℝ) • f.val u) μ := by
  have hd : Continuous (fun u : Kˣ ↦ ‖1 - u.val‖) :=
    (continuous_const.sub Units.continuous_val).norm
  have hc : Continuous (fun u : Kˣ ↦ (w u / ‖1 - u.val‖ : ℝ) • f.val u) := by
    rw [continuous_iff_continuousAt]
    intro u
    by_cases hu : u = 1
    · subst u
      apply ContinuousAt.congr (f := fun _ : Kˣ ↦ (0 : ℂ)) continuousAt_const
      filter_upwards [f.property.1.eventually_eq 1] with z hz
      rw [hz, hf, smul_zero]
    · have he : ‖1 - u.val‖ ≠ 0 := by
        refine norm_ne_zero_iff.mpr (sub_ne_zero.mpr fun h ↦ hu ?_)
        exact Units.ext (show u.val = (1 : Kˣ).val from h.symm)
      exact (hw.continuousAt.div hd.continuousAt he).smul f.property.1.continuous.continuousAt
  exact hc.integrable_of_hasCompactSupport (HasCompactSupport.intro f.property.2 fun x hx ↦ by
    rw [image_eq_zero_of_notMem_tsupport (f := f.val) hx, smul_zero])

omit [∀ w : HeightOneSpectrum (𝓞 F), MeasurableSpace (w.adicCompletion F)]
  [∀ w : HeightOneSpectrum (𝓞 F), BorelSpace (w.adicCompletion F)] in
/-- The ordinary Weil integrand is integrable once the test vanishes at one. -/
theorem finiteWeilOrdinary_integrable (f : Tests) (hf : f.val 1 = 0) :
    Integrable (finiteWeilOrdinaryIntegrand F v f) μ := by
  apply finiteWeil_integrable_of_zero F v μ _ _ f hf
  exact (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 1 / 2)).comp
    (continuous_norm.comp Units.continuous_val)

/-- The compact-open integer-unit indicator fixes the normalization of the
singular distribution at identity. -/
def finiteWeilUnitTest : Tests :=
  compactOpenIndicator Kˣ ⟨U, localIntegralUnits_compact F v, localIntegralUnits_open F v⟩

omit [∀ w : HeightOneSpectrum (𝓞 F), MeasurableSpace (w.adicCompletion F)]
  [∀ w : HeightOneSpectrum (𝓞 F), BorelSpace (w.adicCompletion F)]
  [MeasurableSpace Kˣ] [BorelSpace Kˣ] in
@[simp] theorem finiteWeilUnitTest_one : (finiteWeilUnitTest F v).val 1 = 1 := by
  change (U).indicator (fun _ ↦ (1 : ℂ)) (1 : Kˣ) = 1
  exact indicator_of_mem (show (1 : Kˣ) ∈ U from (v.adicCompletionIntegers F).toSubmonoid.units.one_mem) _

def finiteWeilSubtractUnitTest : Tests →ₗ[ℂ] Tests where
  toFun g := g - g.val 1 • finiteWeilUnitTest F v
  map_add' f g := by
    change f + g - (f.val 1 + g.val 1) • finiteWeilUnitTest F v =
      (f - f.val 1 • finiteWeilUnitTest F v) + (g - g.val 1 • finiteWeilUnitTest F v)
    rw [add_smul]
    abel
  map_smul' c g := by
    change c • g - (c * g.val 1) • finiteWeilUnitTest F v =
      c • (g - g.val 1 • finiteWeilUnitTest F v)
    rw [smul_sub, mul_smul]

omit [∀ w : HeightOneSpectrum (𝓞 F), MeasurableSpace (w.adicCompletion F)]
  [∀ w : HeightOneSpectrum (𝓞 F), BorelSpace (w.adicCompletion F)]
  [MeasurableSpace Kˣ] [BorelSpace Kˣ] in
theorem finiteWeilSubtractUnitTest_one (g : Tests) :
    (finiteWeilSubtractUnitTest F v g).val 1 = 0 := by
  change g.val 1 - g.val 1 * (finiteWeilUnitTest F v).val 1 = 0
  rw [finiteWeilUnitTest_one, mul_one, sub_self]

/-- The distribution with density (q_v/(q_v-1),d\nu_v/|1-x|_v) off the
identity, normalized by its zero value on the integral-unit indicator. -/
def finiteWeilNormalizedDistribution : Tests →ₗ[ℂ] ℂ where
  toFun f :=
    ∫ u : Kˣ, (‖u.val‖ / ‖1 - u.val‖ : ℝ) • (finiteWeilSubtractUnitTest F v f).val u ∂μ
  map_add' f g := by
    rw [map_add]
    simp only [Submodule.coe_add, Pi.add_apply, smul_add]
    exact integral_add
      (finiteWeil_integrable_of_zero F v μ (fun u : Kˣ ↦ ‖u.val‖)
        (continuous_norm.comp Units.continuous_val) _ (finiteWeilSubtractUnitTest_one F v f))
      (finiteWeil_integrable_of_zero F v μ (fun u : Kˣ ↦ ‖u.val‖)
        (continuous_norm.comp Units.continuous_val) _ (finiteWeilSubtractUnitTest_one F v g))
  map_smul' c f := by
    rw [map_smul]
    simp only [Submodule.coe_smul_of_tower, Pi.smul_apply, smul_comm _ c, integral_smul,
      RingHom.id_apply]

@[simp] theorem finiteWeilNormalizedDistribution_unitTest :
    finiteWeilNormalizedDistribution F v μ (finiteWeilUnitTest F v) = 0 := by
  have h : finiteWeilSubtractUnitTest F v (finiteWeilUnitTest F v) = 0 := by
    change finiteWeilUnitTest F v - (finiteWeilUnitTest F v).val 1 • finiteWeilUnitTest F v = 0
    rw [finiteWeilUnitTest_one, one_smul, sub_self]
  change (∫ u : Kˣ, (‖u.val‖ / ‖1 - u.val‖ : ℝ) •
    (finiteWeilSubtractUnitTest F v (finiteWeilUnitTest F v)).val u ∂μ) = 0
  simp [h]

theorem finiteWeilNormalizedDistribution_continuous :
    letI : TopologicalSpace Tests := finestLocallyConvexTopology Tests
    Continuous (finiteWeilNormalizedDistribution F v μ) := by
  letI : TopologicalSpace Tests := finestLocallyConvexTopology Tests
  exact finest_linear_continuous _

private theorem finiteWeilNormalizedDistribution_eq_mulHaar_of_zero (g : Tests) (hg : g.val 1 = 0) :
    finiteWeilNormalizedDistribution F v μ g =
      ∫ u : Kˣ, (‖u.val‖ / ‖1 - u.val‖ : ℝ) • g.val u ∂μ := by
  change (∫ u : Kˣ, (‖u.val‖ / ‖1 - u.val‖ : ℝ) •
    (g - g.val 1 • finiteWeilUnitTest F v).val u ∂μ) = _
  rw [hg, zero_smul, sub_zero]

include hμ in
/-- The normalized distribution restricts to the printed positive density
on the hyperplane of tests vanishing at one. -/
theorem finiteWeilNormalizedDistribution_eq_density_of_zero (g : Tests) (hg : g.val 1 = 0) :
    finiteWeilNormalizedDistribution F v μ g = finiteWeilDensityIntegral F v g := by
  rw [finiteWeilNormalizedDistribution_eq_mulHaar_of_zero F v μ g hg]
  let G (u : Kˣ) := (‖u.val‖ / ‖1 - u.val‖ : ℝ) • g.val u
  have h := finitePlace_tamagawa_integral_units F v μ hμ (finiteUnitExtension F v G)
  simp only [finiteUnitExtension_val] at h
  change (∫ u : Kˣ, G u ∂μ) = _
  rw [h]
  congr 1
  apply integral_congr_ae
  refine .of_forall fun x ↦ ?_
  by_cases hx : x = 0
  · subst x
    simp only [finiteUnitExtension_zero, smul_zero]
  let u := Units.mk0 x hx
  change ‖u.val‖⁻¹ • finiteUnitExtension F v G u.val =
    ‖1 - u.val‖⁻¹ • finiteUnitExtension F v g.val u.val
  simp only [finiteUnitExtension_val, G, smul_smul]
  rw [div_eq_mul_inv, ← mul_assoc, inv_mul_cancel₀ (norm_ne_zero_iff.mpr u.ne_zero), one_mul]

include hμ in
theorem finiteWeilNormalizedDistribution_unique (T : Tests →ₗ[ℂ] ℂ)
    (hT : T (finiteWeilUnitTest F v) = 0)
    (h : ∀ f : Tests, f.val 1 = 0 → T f = finiteWeilDensityIntegral F v f) :
    T = finiteWeilNormalizedDistribution F v μ := by
  apply LinearMap.ext
  intro f
  let g := finiteWeilSubtractUnitTest F v f
  have hg := finiteWeilSubtractUnitTest_one F v f
  have he : f = g + f.val 1 • finiteWeilUnitTest F v := by
    change f = (f - f.val 1 • finiteWeilUnitTest F v) + f.val 1 • finiteWeilUnitTest F v
    exact (sub_add_cancel _ _).symm
  nth_rw 1 [he]
  rw [map_add, map_smul, hT, smul_zero, add_zero, h g hg,
    ← finiteWeilNormalizedDistribution_eq_density_of_zero F v μ hμ g hg]
  rw [show f = g + f.val 1 • finiteWeilUnitTest F v from he, map_add, map_smul,
    finiteWeilNormalizedDistribution_unitTest, smul_zero, add_zero]

/-- Multiplication by the inverse square root of the local norm preserves
the multiplicative test space. -/
def finiteWeilInverseSqrtTest (f : Tests) : Tests :=
  ⟨fun u ↦ (‖u.val‖ ^ (-1 / 2 : ℝ) : ℝ) • f.val u, by
    simp only [Complex.real_smul]
    change IsLocallyConstant (((fun r : ℝ ↦ (↑(r ^ (-1 / 2 : ℝ)) : ℂ)) ∘
      (fun u : Kˣ ↦ ‖u.val‖)) * f.val)
    exact ((finiteUnitNorm_locallyConstant F v).comp _).mul f.property.1,
    HasCompactSupport.intro f.property.2 (fun x hx ↦ by
      rw [image_eq_zero_of_notMem_tsupport (f := f.val) hx, smul_zero])⟩

include hμ in
/-- Corrected (B.4.4.6). The prescribed positive density has coefficient
one after the inverse-square-root weighting. -/
theorem finiteWeilPrincipalValue_eq_normalizedDistribution (f : Tests) (hf : f.val 1 = 0) :
    finiteWeilPrincipalValue F v μ 1 f =
      finiteWeilNormalizedDistribution F v μ (finiteWeilInverseSqrtTest F v f) := by
  have hg : (finiteWeilInverseSqrtTest F v f).val 1 = 0 := by
    change (‖(1 : Kˣ).val‖ ^ (-1 / 2 : ℝ) : ℝ) • f.val 1 = 0
    rw [hf, smul_zero]
  rw [finiteWeilPrincipalValue_eq_ordinary F v μ hμ f hf,
    finiteWeilNormalizedDistribution_eq_mulHaar_of_zero F v μ _ hg]
  apply integral_congr_ae
  refine .of_forall fun u ↦ ?_
  change (‖u.val‖ ^ (1 / 2 : ℝ) / ‖1 - u.val‖ : ℝ) • f.val u =
    (‖u.val‖ / ‖1 - u.val‖ : ℝ) • ((‖u.val‖ ^ (-1 / 2 : ℝ) : ℝ) • f.val u)
  have he : ‖u.val‖ ^ (1 / 2 : ℝ) = ‖u.val‖ ^ (-1 / 2 : ℝ) * ‖u.val‖ := by
    rw [← Real.rpow_add_one (norm_ne_zero_iff.mpr u.ne_zero)]
    congr 1
    norm_num
  rw [smul_smul, he]
  congr 1
  ring

include hμ in
/-- A test on one compact open shell gives positive real part on the left
of (B.4.4.6) and negative real part with its printed coefficient. -/
theorem finiteWeilPrincipalValue_printed_coefficient_counterexample :
    ∃ f : Tests, f.val 1 = 0 ∧
      0 < (finiteWeilPrincipalValue F v μ 1 f).re ∧
      (-(μ.real U : ℂ) *
        finiteWeilNormalizedDistribution F v μ (finiteWeilInverseSqrtTest F v f)).re < 0 := by
  let p := chosenFiniteUniformizer F v
  let e := Homeomorph.mulLeft p
  let C := e '' U
  have hC : IsCompact C := (localIntegralUnits_compact F v).image e.continuous
  have ho : IsOpen C := e.isOpenMap _ (localIntegralUnits_open F v)
  have hp : p ∈ C := ⟨1, (v.adicCompletionIntegers F).toSubmonoid.units.one_mem, mul_one p⟩
  have h1 : (1 : Kˣ) ∉ C := by
    rintro ⟨u, hu, he⟩
    have hn : ‖u.val‖ = 1 :=
      (finiteCompletion_norm_eq_one_iff F v u).mpr ((localIntegralUnits_value F v u).mp hu)
    have hsmall : ‖p.val‖ < 1 := finiteCompletion_uniformizer_contracts F v p
      (chosenFiniteUniformizer_spec F v)
    change p * u = 1 at he
    have h := congrArg (fun t : Kˣ ↦ ‖t.val‖) he
    simp only [Units.val_mul, Units.val_one, norm_mul, norm_one, hn, mul_one] at h
    exact hsmall.ne h
  let f := compactOpenIndicator Kˣ ⟨C, hC, ho⟩
  have hf : f.val 1 = 0 := by
    change C.indicator (fun _ ↦ (1 : ℂ)) (1 : Kˣ) = 0
    exact indicator_of_notMem h1 _
  have hpos : 0 < (finiteWeilPrincipalValue F v μ 1 f).re := by
    rw [finiteWeilPrincipalValue_eq_ordinary F v μ hμ f hf]
    change 0 < RCLike.re (∫ u, finiteWeilOrdinaryIntegrand F v f u ∂μ)
    rw [← integral_re (finiteWeilOrdinary_integrable F v μ f hf)]
    let k (u : Kˣ) := (finiteWeilOrdinaryIntegrand F v f u).re
    change 0 < ∫ u : Kˣ, k u ∂μ
    have he (u : Kˣ) : k u =
        (‖u.val‖ ^ (1 / 2 : ℝ) / ‖1 - u.val‖) *
          (C.indicator (fun _ ↦ (1 : ℂ)) u).re := by
      change ((‖u.val‖ ^ (1 / 2 : ℝ) / ‖1 - u.val‖ : ℝ) •
        C.indicator (fun _ ↦ (1 : ℂ)) u).re = _
      rw [Complex.smul_re, smul_eq_mul]
    have hnn : 0 ≤ k := by
      intro u
      rw [he]
      apply mul_nonneg (div_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (norm_nonneg _))
      by_cases hu : u ∈ C
      · simp [indicator_of_mem hu]
      · simp [indicator_of_notMem hu]
    have hi : Integrable k μ := (finiteWeilOrdinary_integrable F v μ f hf).re
    apply (integral_pos_iff_support_of_nonneg hnn hi).mpr
    have hsub : C ⊆ Function.support k := by
      intro u hu
      have hden : 0 < ‖1 - u.val‖ := by
        refine norm_pos_iff.mpr (sub_ne_zero.mpr fun he ↦ h1 ?_)
        exact (show u = (1 : Kˣ) from Units.ext he.symm) ▸ hu
      rw [Function.mem_support, he, indicator_of_mem hu, Complex.one_re, mul_one]
      exact (div_pos (Real.rpow_pos_of_pos (norm_pos_iff.mpr u.ne_zero) _) hden).ne'
    exact (pos_iff_ne_zero.mpr (ho.measure_ne_zero μ ⟨p, hp⟩)).trans_le (measure_mono hsub)
  refine ⟨f, hf, hpos, ?_⟩
  rw [← finiteWeilPrincipalValue_eq_normalizedDistribution F v μ hμ f hf,
    neg_mul, Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  exact neg_neg_of_pos (mul_pos (finiteIntegralUnits_real_pos F v μ) hpos)

end Tamagawa

end
end Masullo
