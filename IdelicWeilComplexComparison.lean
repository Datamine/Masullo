import ComplexWeilRadialCutoff
import IdelicWeilArchRadial
import IdelicWeilCharacterSynthesis

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical NumberField SchwartzMap

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

local instance weilComplexComparisonClassLC : LocallyCompactSpace (IdeleClass F) := ideleClasses_locallyCompact
local instance weilComplexComparisonClassT2 : T2Space (IdeleClass F) := ideleClasses_hausdorff

private abbrev ComplexPlace := {v : InfinitePlace F // v.IsComplex}

private def complexWeilIdelicShiftedTest (f : BruhatCompactTest (IdeleClass F))
    (v : ComplexPlace F) : 𝓢(ℂ, ℂ) :=
  archWeilShiftedTest 2 (f.val.val ∘ complexPlaceWeilInsertion F v.val v.property)
    (complexPlaceWeilTest_hasCompactSupport F f v.val v.property)
    (complexPlaceWeilTest_smooth F f v.val v.property)

private theorem complexWeilIdelicShiftedTest_zero (f : BruhatCompactTest (IdeleClass F))
    (v : ComplexPlace F) : complexWeilIdelicShiftedTest F f v 0 = f.val.val 1 := by
  simp [complexWeilIdelicShiftedTest]

private theorem complexWeilIdelicShiftedTest_radial (f : BruhatCompactTest (IdeleClass F))
    (v : ComplexPlace F) (r : ℝ) (hr : 0 < r) :
    complexWeilShiftedRadial (complexWeilIdelicShiftedTest F f v) r =
      idelicWeilComplexRadialSlice F f v r hr := by
  let h := complexWeilIdelicShiftedTest F f v
  let g (θ : ℝ) := complexWeilCircleKernel r θ •
    f.val.val (complexPlaceWeilInsertion F v.val v.property (complexWeilCircleUnit r hr θ))
  have he : (∫ θ in (0 : ℝ)..2 * Real.pi,
      (‖1 - circleMap 0 r θ‖ ^ 2)⁻¹ • h (1 - circleMap 0 r θ)) =
      r⁻¹ • ∫ θ in (0 : ℝ)..2 * Real.pi, g θ := by
    rw [← intervalIntegral.integral_smul]
    apply intervalIntegral.integral_congr
    intro θ _
    let u := complexWeilCircleUnit r hr θ
    have hext : archWeilZeroExtension
      (f.val.val ∘ complexPlaceWeilInsertion F v.val v.property) (circleMap 0 r θ) =
        f.val.val (complexPlaceWeilInsertion F v.val v.property u) :=
      archWeilZeroExtension_unit _ u
    change (‖1 - circleMap 0 r θ‖ ^ 2)⁻¹ • complexWeilIdelicShiftedTest F f v
      (1 - circleMap 0 r θ) = r⁻¹ • g θ
    unfold complexWeilIdelicShiftedTest
    rw [archWeilShiftedTest_apply, sub_sub_cancel, hext, norm_circleMap_zero, abs_of_pos hr]
    norm_num [Real.rpow_neg_one, g, complexWeilCircleKernel, smul_smul, mul_comm, u]
    ring
  change (r ^ 2 : ℝ) • ((2 * Real.pi)⁻¹ • ∫ θ in (0 : ℝ)..2 * Real.pi,
      (‖1 - circleMap 0 r θ‖ ^ 2)⁻¹ • h (1 - circleMap 0 r θ)) =
      (r : ℂ) * ((2 * Real.pi)⁻¹ • ∫ θ in (0 : ℝ)..2 * Real.pi, g θ)
  rw [he, ← Complex.real_smul, smul_smul, smul_smul, smul_smul]
  congr 1
  field_simp [hr.ne', Real.pi_ne_zero]

/-- The complex radial density before subtraction of the identity term. -/
def idelicWeilComplexRadialDensity (f : BruhatCompactTest (IdeleClass F))
    (v : ComplexPlace F) (t : ℝ) : ℂ :=
  idelicWeilComplexRadialSlice F f v (Real.exp (t / 2)) (Real.exp_pos _) +
    idelicWeilComplexRadialSlice F f v (Real.exp (-t / 2)) (Real.exp_pos _)

/-- The complex log-radius cutoff agrees with the shifted additive cutoff
after removing the complex gamma contact constant. -/
theorem complexPlaceIdelicWeil_radialCutoff_tendsto (f : BruhatCompactTest (IdeleClass F))
    (v : ComplexPlace F) :
    Tendsto (fun δ : ℝ => (∫ t in Ioi δ, idelicWeilComplexRadialDensity F f v t) +
      (2 * Real.log δ : ℝ) • f.val.val 1) (𝓝[>] 0)
      (𝓝 (complexPlaceIdelicWeilTerm F f v.val v.property -
        (2 * (Real.eulerMascheroniConstant + Real.log (2 * Real.pi))) • f.val.val 1)) := by
  let h := complexWeilIdelicShiftedTest F f v
  have hz : h 0 = f.val.val 1 := complexWeilIdelicShiftedTest_zero F f v
  have hc : HasCompactSupport (h : ℂ → ℂ) := archWeilShiftedTest_hasCompactSupport _ _ _ _
  have ht : complexPlaceIdelicWeilTerm F f v.val v.property =
      -complexTraceLogFourierDistribution h := rfl
  have hval : complexPlaceIdelicWeilTerm F f v.val v.property -
        (2 * (Real.eulerMascheroniConstant + Real.log (2 * Real.pi))) • f.val.val 1 =
      Real.pi⁻¹ • ∫ z, complexLogCutoffRemainder h z := by
    rw [ht, complexTraceLogFourierDistribution_apply, complexTraceLogFourierPairing_eq_finitePart,
      ← hz]
    simp only [neg_sub, neg_smul]
    abel
  rw [hval]
  apply (complexWeil_radialAreaCutoff_tendsto h).congr'
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  rw [complexWeil_radialAreaCutoff_eq_log h h.continuous hc hδ, hz]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _
  exact congrArg₂ (· + ·)
    (complexWeilIdelicShiftedTest_radial F f v _ (Real.exp_pos (t / 2)))
    (complexWeilIdelicShiftedTest_radial F f v _ (Real.exp_pos (-t / 2)))

/-- An integrable compensated complex radial density computes the local
Weil term with its finite gamma contact constant. -/
theorem complexPlaceIdelicWeilTerm_eq_radialIntegral (f : BruhatCompactTest (IdeleClass F))
    (v : ComplexPlace F)
    (hf : IntegrableOn (fun t : ℝ => idelicWeilComplexRadialDensity F f v t -
      (2 * Real.exp (-t) / (1 - Real.exp (-t))) • f.val.val 1) (Ioi 0)) :
    complexPlaceIdelicWeilTerm F f v.val v.property =
      (∫ t in Ioi (0 : ℝ), idelicWeilComplexRadialDensity F f v t -
        (2 * Real.exp (-t) / (1 - Real.exp (-t))) • f.val.val 1) +
      (2 * (Real.eulerMascheroniConstant + Real.log (2 * Real.pi))) • f.val.val 1 := by
  have he (t : ℝ) : (Real.exp (-t) / (1 - Real.exp (-t))) • ((2 : ℝ) • f.val.val 1) =
      (2 * Real.exp (-t) / (1 - Real.exp (-t))) • f.val.val 1 := by
    rw [smul_smul, mul_comm, mul_div_assoc]
  have hf' : IntegrableOn (fun t : ℝ => idelicWeilComplexRadialDensity F f v t -
      (Real.exp (-t) / (1 - Real.exp (-t))) • ((2 : ℝ) • f.val.val 1)) (Ioi 0) := by
    simpa only [he] using hf
  have ht := idelicWeil_radialFinitePart_tendsto _ _ hf'
  simp_rw [he, smul_smul, mul_comm (Real.log _) 2] at ht
  exact sub_eq_iff_eq_add.mp (tendsto_nhds_unique
    (complexPlaceIdelicWeil_radialCutoff_tendsto F f v) ht)

private abbrev K := normOneIdeleClass F
private abbrev Place := HeightOneSpectrum (𝓞 F)
private abbrev χ (w : PontryaginDual (K F)) := heckeOrdinateCharacter F w 0

local instance weilComplexComparisonNormOneMeasurable : MeasurableSpace (K F) := borel _
local instance weilComplexComparisonNormOneBorel : BorelSpace (K F) := ⟨rfl⟩

variable (ν : Measure (K F)) [ν.IsHaarMeasure]
  (E : ∀ w : PontryaginDual (K F), CompletedHeckeChart F w)
  (T : PontryaginDual (K F) → Finset (Place F))
  (hT : ∀ w, Surjective (sIdeleClassInclusion F (T w)))
  (huT : ∀ w, globalNormOneCharacter F (heckeNormOneRestriction F (χ F w)⁻¹) ∈
    (sUnramified F (T w) : Set (QuasiCharacter (IdeleClass F))))

private theorem complexForward_unramified (w : PontryaginDual (K F)) :
    globalNormOneCharacter F (heckeNormOneRestriction F (χ F w)) ∈
      (sUnramified F (E w).stage : Set (QuasiCharacter (IdeleClass F))) := by
  rw [heckeNormOneRestriction_ordinateCharacter]
  exact (E w).unramified

private abbrev b (v : ComplexPlace F) (w : PontryaginDual (K F)) :=
  manuscriptHeckeComplexGammaShift F (χ F w) (E w).stage (E w).surj
    (complexForward_unramified F E w) 0 v

private abbrev b' (v : ComplexPlace F) (w : PontryaginDual (K F)) :=
  manuscriptHeckeComplexGammaShift F (χ F w)⁻¹ (T w) (hT w) (huT w) 0 v

set_option maxHeartbeats 1200000 in
/-- A single complex character component contributes precisely its signed
centered gamma term, including the contact term. -/
theorem complexPlaceIdelicWeilTerm_characterComponent
    (f p : BruhatCompactTest (IdeleClass F)) (v : ComplexPlace F) (w : PontryaginDual (K F))
    (hp : ∀ x : IdeleClass F, p.val.val x =
      ((ν.real univ : ℂ)⁻¹ * idelicWeilLogProfile F ν w f (ideleClassLogNorm F x).toAdd) *
        (((normOneEulerCharacter F w x)⁻¹ : Circle) : ℂ)) :
    complexPlaceIdelicWeilTerm F p v.val v.property =
      -(ν.real univ : ℂ)⁻¹ * heckeCenteredGammaTerm (idelicWeilCenteredTest F ν w f)
        1 (2 * Real.pi) (b F E v w) (b' F T hT huT v w) := by
  let d (t : ℝ) := idelicWeilComplexRadialDensity F p v t -
    (2 * Real.exp (-t) / (1 - Real.exp (-t))) • p.val.val 1
  let L (ψ : PontryaginDual (K F)) (q : ℝ → ℂ) :=
    localGammaExplicitKernel 1 (b F E v ψ) (b' F T hT huT v ψ)
      (mellinWeight (q ∘ Real.log) (-(1 / 2)))
  let A := -(ν.real univ : ℂ)⁻¹
  let g := idelicWeilLogProfile F ν w f
  have hd (t : ℝ) (ht : 0 < t) : d t = A * L w g t := by
    have hs := idelicWeil_complexGammaKernel_hasSum F ν E T hT huT p v ht
    change HasSum (fun ψ => A * L ψ (idelicWeilLogProfile F ν ψ p) t) _ at hs
    have hs' : HasSum (fun ψ => if ψ = w then A * L w g t else 0) (d t) := by
      convert hs using 1
      · funext ψ
        have hq : idelicWeilLogProfile F ν ψ p = fun u => if ψ = w then g u else 0 :=
          funext fun u => idelicWeilLogProfile_characterComponent F ν f p w hp ψ u
        rw [hq]
        by_cases h : ψ = w
        · subst ψ
          simp
        · simp only [ite_eq_right h, L, localGammaExplicitKernel_centered_log, mul_zero, sub_zero,
            zero_mul, zero_div]
      · simp only [d, idelicWeilComplexRadialDensity, Complex.real_smul]
        push_cast
        ring
    exact hs'.unique (hasSum_ite_eq w (A * L w g t))
  have hi : IntegrableOn (L w g) (Ioi 0) :=
    heckeCenteredGammaKernel_integrable (idelicWeilCenteredTest F ν w f) 1
      zero_lt_one _ _
      (manuscriptHeckeComplexGammaShift_re_nonneg F (χ F w) _ _ _ 0 v)
      (manuscriptHeckeComplexGammaShift_re_nonneg F (χ F w)⁻¹ _ _ _ 0 v)
  have hscaled : IntegrableOn (fun t => A * L w g t) (Ioi 0) := hi.const_mul A
  have hdi : IntegrableOn d (Ioi 0) :=
    hscaled.congr_fun (fun t ht => (hd t ht).symm) measurableSet_Ioi
  have hc : p.val.val 1 = -A * g 0 := by
    rw [hp]
    simp [A, g]
  rw [complexPlaceIdelicWeilTerm_eq_radialIntegral F p v hdi]
  change (∫ t in Ioi (0 : ℝ), d t) +
    (2 * (Real.eulerMascheroniConstant + Real.log (2 * Real.pi))) • p.val.val 1 = _
  rw [setIntegral_congr_fun measurableSet_Ioi (fun t ht => hd t ht), integral_const_mul, hc]
  change A * (∫ t in Ioi (0 : ℝ), L w g t) +
    (2 * (Real.eulerMascheroniConstant + Real.log (2 * Real.pi))) • (-A * g 0) =
      A * ((∫ t in Ioi (0 : ℝ), L w g t) -
        2 * (1 : ℂ) * ((Real.eulerMascheroniConstant : ℂ) + (Real.log (2 * Real.pi) : ℂ)) * g 0)
  simp only [Complex.real_smul]
  push_cast
  ring

/-- The centered gamma contributions sum unconditionally to the signed
geometric complex-place term. -/
theorem idelicWeil_complexComparison_hasSum (f : BruhatCompactTest (IdeleClass F))
    (v : ComplexPlace F) :
    HasSum (fun w : PontryaginDual (K F) =>
      (ν.real univ : ℂ)⁻¹ * heckeCenteredGammaTerm (idelicWeilCenteredTest F ν w f)
        1 (2 * Real.pi) (b F E v w) (b' F T hT huT v w))
      (-complexPlaceIdelicWeilTerm F f v.val v.property) := by
  obtain ⟨P, hP, hsum, _⟩ := exists_idelicWeil_infinite_characterSynthesis F ν f
  have hs := (hsum v.val).neg
  simp only [infinitePlaceIdelicWeilDual_apply_complex F v.val v.property] at hs
  refine hs.congr_fun fun w => ?_
  rw [complexPlaceIdelicWeilTerm_characterComponent F ν E T hT huT f (P w) v w (hP w),
    neg_mul, neg_neg]

end
end Masullo
