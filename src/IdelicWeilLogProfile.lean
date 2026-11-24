import IdelicWeilInfiniteDual
import IdelicHeckeZeroStrongDual
import BruhatIsotypeComparison
import MellinBergman
import IdelicCutoffKernel
import GlobalHeckeEulerComparison

open Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical ContDiff NumberField

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]
private abbrev K := normOneIdeleClass F

local instance : LocallyCompactSpace (IdeleClass F) := ideleClasses_locallyCompact
local instance : T2Space (IdeleClass F) := ideleClasses_hausdorff
local instance : SecondCountableTopology (IdeleClass F) := ideleClass_secondCountable F
local instance : CompactSpace (K F) := normOneIdeleClass_compact F
local instance : LocallyCompactSpace (K F) := inferInstance
local instance : SecondCountableTopology (K F) := IsInducing.subtypeVal.secondCountableTopology
local instance : MeasurableSpace (K F) := borel _
local instance : BorelSpace (K F) := ⟨rfl⟩
local instance : MeasurableSpace (IdeleClass F) := borel _
local instance : BorelSpace (IdeleClass F) := ⟨rfl⟩

private def idelicWeilRay : Multiplicative ℝ →ₜ* IdeleClass F :=
  ⟨ideleClassExpSection F, ideleClassExpSection_continuous F⟩

private theorem idelicWeilRay_proper :
    IsProperMap (fun t : ℝ => idelicWeilRay F (Multiplicative.ofAdd t)) := by
  let j (t : ℝ) := idelicWeilRay F (Multiplicative.ofAdd t)
  let l (g : IdeleClass F) := (ideleClassLogNorm F g).toAdd
  have hj : Continuous j := (idelicWeilRay F).continuous.comp continuous_ofAdd
  have hl : Continuous l := continuous_toAdd.comp (ideleClassLogNorm_continuous F)
  have he : l ∘ j = id := funext fun t =>
    congrArg Multiplicative.toAdd (ideleClassLogNorm_expSection F (Multiplicative.ofAdd t))
  exact isProperMap_of_comp_of_t2 hj hl (he.symm ▸ isProperMap_id)

variable (ν : Measure (K F)) [ν.IsHaarMeasure]

/-- The norm-one Fourier coefficient as a function of the logarithmic norm.
The weight uses the same character orientation as the spectral Mellin term. -/
def idelicWeilLogProfile (χ : PontryaginDual (K F))
    (f : BruhatCompactTest (IdeleClass F)) (t : ℝ) : ℂ :=
  ∫ k : K F, (χ k : ℂ) * f.val.val (k.val * idelicWeilRay F (Multiplicative.ofAdd t)) ∂ν

set_option maxHeartbeats 700000 in
/-- The norm-one coefficient of a compact Bruhat test is a compactly
supported smooth logarithmic profile, admissible for the characterwise formula. -/
theorem idelicWeilLogProfile_compact_smooth (χ : PontryaginDual (K F))
    (f : BruhatCompactTest (IdeleClass F)) :
    HasCompactSupport (idelicWeilLogProfile F ν χ f) ∧ ContDiff ℝ ∞ (idelicWeilLogProfile F ν χ f) := by
  letI : IsFiniteMeasure ν := ⟨isCompact_univ.measure_lt_top⟩
  letI : Measure.Regular ν := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure ν
  letI : ν.IsInvInvariant := Measure.IsHaarMeasure.isInvInvariant_of_regular ν
  obtain ⟨P, hP⟩ := exists_bruhatSchwartz_compactAverage (G := IdeleClass F) (normOneIdeleClass F) ν χ
  let b := P f.val
  have hEval (g : IdeleClass F) :
      b.val g = ∫ k : K F, (χ k : ℂ) * f.val.val (k.val * g) ∂ν := by
    let ev : BruhatSchwartz (IdeleClass F) →L[ℂ] ℂ :=
      ⟨(LinearMap.proj g).comp (bruhatSchwartzSubmodule (G := IdeleClass F)).subtype,
        bruhatSchwartz_continuous_eval g⟩
    have h := (hP f.val ev).2
    have hleft : b.val g =
        ∫ k : K F, (((χ k)⁻¹ : Circle) : ℂ) * f.val.val (k.val⁻¹ * g) ∂ν := by
      rw [show b.val g = ev (P f.val) from rfl, h]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun k => by
        change (((χ k)⁻¹ : Circle) : ℂ) * (bruhatSchwartz_translate k.val f.val).val g = _
        rw [bruhatSchwartz_translate_apply]
    exact hleft.trans (by
      simpa only [map_inv, Subgroup.coe_inv] using
        integral_inv_eq_self (fun k : K F => (χ k : ℂ) * f.val.val (k.val * g)) ν)
  let B : Set (IdeleClass F) :=
    (fun p : K F × IdeleClass F => p.1.val * p.2) '' (univ ×ˢ tsupport f.val.val)
  have hc₁ : Continuous (fun p : K F × IdeleClass F => p.1.val) :=
    continuous_subtype_val.comp continuous_fst
  have hc₂ : Continuous (Prod.snd : K F × IdeleClass F → IdeleClass F) := continuous_snd
  have hc : Continuous (fun p : K F × IdeleClass F => p.1.val * p.2) := hc₁.mul hc₂
  have hB : IsCompact B := (isCompact_univ.prod f.property).image hc
  have hb0 (g : IdeleClass F) (hg : g ∉ B) : b.val g = 0 := by
    rw [hEval]
    apply integral_eq_zero_of_ae
    exact Filter.Eventually.of_forall fun k => by
      change (χ k : ℂ) * f.val.val (k.val * g) = 0
      have hn : k.val * g ∉ tsupport f.val.val := by
        intro hk
        apply hg
        exact ⟨(k⁻¹, k.val * g), ⟨mem_univ _, hk⟩, inv_mul_cancel_left _ _⟩
      rw [image_eq_zero_of_notMem_tsupport hn, mul_zero]
  have hb : HasCompactSupport b.val := HasCompactSupport.intro hB hb0
  let u : BruhatCompactTest (IdeleClass F) := BruhatCompactTest.algebraicEquiv.symm ⟨b, hb⟩
  have he : idelicWeilLogProfile F ν χ f = fun t : ℝ => u.val.val (idelicWeilRay F (Multiplicative.ofAdd t)) :=
    funext fun t => (hEval _).symm
  rw [he]
  constructor
  · exact HasCompactSupport.intro ((idelicWeilRay_proper F).isCompact_preimage hB)
      fun t ht => hb0 _ ht
  · have heval : (fun t => u.val.val (1 * idelicWeilRay F (Multiplicative.ofAdd t))) =
      (fun t => u.val.val (idelicWeilRay F (Multiplicative.ofAdd t))) :=
      funext fun t => congrArg u.val.val
        (@one_mul (IdeleClass F) inferInstance (idelicWeilRay F (Multiplicative.ofAdd t)))
    rw [← heval]
    exact bruhatCompactTest_contDiff_vectorOrbit F u 1 (idelicWeilRay F)

/-- The actual norm-one coefficient is a valid centered test for B.4.2.2. -/
def idelicWeilCenteredTest (χ : PontryaginDual (K F))
    (f : BruhatCompactTest (IdeleClass F)) : PositiveRealExponentialDecay (univ : Set ℝ) :=
  ⟨idelicWeilLogProfile F ν χ f, mem_logExponentialDecaySubmodule_of_hasCompactSupport univ
    (idelicWeilLogProfile_compact_smooth F ν χ f).1
    (idelicWeilLogProfile_compact_smooth F ν χ f).2⟩

private theorem idelicWeil_logCoordinates_eval (p : ℝ × K F) :
    ideleClassLogCoordinates F p =
      p.2.val * idelicWeilRay F (Multiplicative.ofAdd p.1) := rfl

private theorem idelicWeil_character_logCoordinates (χ : PontryaginDual (K F))
    (p : ℝ × K F) : normOneEulerCharacter F χ (ideleClassLogCoordinates F p) = χ p.2 := by
  have he := (ideleClassSplitHomeomorph F).apply_symm_apply (p.2, Multiplicative.ofAdd p.1)
  exact congrArg (fun z : K F × Multiplicative ℝ => χ z.1) he

set_option maxHeartbeats 850000 in
/-- Mellin evaluation of a centered log profile equals the actual class
integral at the corresponding complex parameter. -/
theorem idelicWeilCenteredTest_mellin (χ : PontryaginDual (K F))
    (f : BruhatCompactTest (IdeleClass F)) (s : ℂ) :
    mellin ((idelicWeilCenteredTest F ν χ f).val ∘ Real.log) s =
      ∫ g, Complex.exp (s * ((ideleClassLogNorm F g).toAdd : ℂ)) *
        ((normOneEulerCharacter F χ g : ℂ) * f.val.val g) ∂globalClassMeasure F ν := by
  letI : IsFiniteMeasure ν := ⟨isCompact_univ.measure_lt_top⟩
  letI := globalClassMeasure_isHaar F ν
  let e := ideleClassLogCoordinates F
  let W (g : IdeleClass F) := Complex.exp (s * ((ideleClassLogNorm F g).toAdd : ℂ)) *
    ((normOneEulerCharacter F χ g : ℂ) * f.val.val g)
  have hc : Continuous W := by
    have he : Continuous (fun g : IdeleClass F => Complex.exp (s * ((ideleClassLogNorm F g).toAdd : ℂ))) :=
      Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
        (continuous_toAdd.comp (ideleClassLogNorm_continuous F))))
    have hχ : Continuous (fun g : IdeleClass F => (normOneEulerCharacter F χ g : ℂ)) :=
      continuous_subtype_val.comp (normOneEulerCharacter F χ).continuous
    exact he.mul (hχ.mul (bruhatSchwartz_continuous f.val))
  have hs : HasCompactSupport W := (f.property.mul_left (f := fun g => (normOneEulerCharacter F χ g : ℂ))).mul_left
  have hI : Integrable W (globalClassMeasure F ν) := hc.integrable_of_hasCompactSupport hs
  have hmp : MeasurePreserving e (volume.prod ν) (globalClassMeasure F ν) := ⟨e.continuous.measurable, rfl⟩
  have hprod := integral_prod (W ∘ e) (hmp.integrable_comp_of_integrable hI)
  rw [mellin_eq_log_integral]
  change (∫ t : ℝ, Complex.exp (s * (t : ℂ)) * idelicWeilLogProfile F ν χ f (Real.log (Real.exp t))) =
    ∫ g, W g ∂globalClassMeasure F ν
  rw [← hmp.integral_comp e.toMeasurableEquiv.measurableEmbedding W]
  change _ = ∫ p, (W ∘ e) p ∂volume.prod ν
  rw [hprod]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun t => by
    change Complex.exp (s * (t : ℂ)) * idelicWeilLogProfile F ν χ f (Real.log (Real.exp t)) =
      ∫ k : K F, W (e (t, k)) ∂ν
    rw [Real.log_exp, idelicWeilLogProfile, ← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun k => by
      have ht : (ideleClassLogNorm F (e (t, k))).toAdd = t := log_norm_coordinates F (t, k)
      change _ = Complex.exp (s * ((ideleClassLogNorm F (e (t, k))).toAdd : ℂ)) *
         ((normOneEulerCharacter F χ (e (t, k)) : ℂ) * f.val.val (e (t, k)))
      rw [ht, idelicWeil_character_logCoordinates, idelicWeil_logCoordinates_eval]

variable [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ] in
/-- A weighted completed-zero term is the centered Mellin sample for its
norm-one character, with the same zero order as in the spectral distribution. -/
theorem completedHeckeZeroDistribution_apply_centered
    (E : ∀ χ : PontryaginDual (K F), CompletedHeckeChart F χ)
    (p : CompletedHeckeZeros F E) (r : ℝ) (f : BruhatCompactTest (IdeleClass F)) :
    completedHeckeZeroDistribution F ν E r p f =
      (completedZeroMultiplicity F E p : ℂ) *
        mellin ((idelicWeilCenteredTest F ν p.1 f).val ∘ Real.log) (p.2.val + (r : ℂ)) := by
  rw [completedHeckeZeroDistribution_apply, idelicWeilCenteredTest_mellin]
  apply congrArg ((completedZeroMultiplicity F E p : ℂ) * ·)
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun g => by
    let a : ℂ := Real.exp ((p.2.val.re + r) * (ideleClassLogNorm F g).toAdd)
    let b : ℂ := completedZeroCharacter F E p g
    let c : ℂ := normOneEulerCharacter F p.1 g
    let d := Complex.exp ((p.2.val + (r : ℂ)) * ((ideleClassLogNorm F g).toAdd : ℂ))
    have hw : a * b = c * d := completedZero_mellin_weight F E p r g
    change f.val.val g * a * b = d * (c * f.val.val g)
    rw [mul_assoc, hw]
    ring

/-- The two normalized pole terms are the two endpoint Mellin samples of
the trivial norm-one coefficient. -/
theorem idelicWeilPolarDual_apply_centered (f : BruhatCompactTest (IdeleClass F)) :
    idelicWeilPolarDual F ν f = (ν.real univ : ℂ)⁻¹ *
      (mellin ((idelicWeilCenteredTest F ν 1 f).val ∘ Real.log) (-1 / 2) +
        mellin ((idelicWeilCenteredTest F ν 1 f).val ∘ Real.log) (1 / 2)) := by
  rw [idelicWeilPolarDual_apply, idelicWeilCenteredTest_mellin, idelicWeilCenteredTest_mellin]
  have he (a : ℝ) :
      (∫ g, (Real.exp (a * (ideleClassLogNorm F g).toAdd) : ℂ) * f.val.val g ∂globalClassMeasure F ν) =
      ∫ g, Complex.exp ((a : ℂ) * ((ideleClassLogNorm F g).toAdd : ℂ)) *
        ((normOneEulerCharacter F 1 g : ℂ) * f.val.val g) ∂globalClassMeasure F ν := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun g => by
      change (Real.exp (a * (ideleClassLogNorm F g).toAdd) : ℂ) * f.val.val g =
        Complex.exp ((a : ℂ) * ((ideleClassLogNorm F g).toAdd : ℂ)) *
          ((normOneEulerCharacter F 1 g : ℂ) * f.val.val g)
      have h : (normOneEulerCharacter F 1 g : ℂ) = 1 := rfl
      rw [h, one_mul, Complex.ofReal_exp, Complex.ofReal_mul]
  apply congrArg ((ν.real univ : ℂ)⁻¹ * ·)
  have hn : ((-1 / 2 : ℝ) : ℂ) = -1 / 2 := by (push_cast; norm_num)
  have hp : ((1 / 2 : ℝ) : ℂ) = 1 / 2 := by (push_cast; norm_num)
  have h₁ := he (-1 / 2)
  have h₂ := he (1 / 2)
  rw [hn] at h₁
  rw [hp] at h₂
  exact congrArg₂ (· + ·) h₁ h₂

end
end Masullo
