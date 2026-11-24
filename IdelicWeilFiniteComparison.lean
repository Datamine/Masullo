import IdelicWeilCharacterFormula
import IdelicWeilConductor
import IdelicWeilPrimeCutoff
import IdelicWeilFiniteStrongDual

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical NumberField

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

private abbrev Place := HeightOneSpectrum (𝓞 F)
private abbrev K := normOneIdeleClass F

local instance weilFiniteComparisonClassLC : LocallyCompactSpace (IdeleClass F) :=
  ideleClasses_locallyCompact
local instance weilFiniteComparisonClassT2 : T2Space (IdeleClass F) := ideleClasses_hausdorff
local instance weilFiniteComparisonNormOneMeasurable : MeasurableSpace (K F) := borel _
local instance weilFiniteComparisonNormOneBorel : BorelSpace (K F) := ⟨rfl⟩

variable [∀ w : Place F, MeasurableSpace (w.adicCompletion F)]
  [∀ w : Place F, BorelSpace (w.adicCompletion F)]
  [∀ w : Place F, MeasurableSpace (w.adicCompletion F)ˣ]
  [∀ w : Place F, BorelSpace (w.adicCompletion F)ˣ]
  (μ : ∀ w : Place F, Measure (w.adicCompletion F)ˣ) [∀ w, (μ w).IsHaarMeasure]
  (ν : Measure (K F)) [ν.IsHaarMeasure]

set_option maxHeartbeats 1200000

/-- The complete finite-place comparison in the idelic explicit formula.
The characterwise conductor and prime powers reproduce the finite-place
principal values, including the discriminant and the geometric sign. -/
theorem idelicWeil_finiteComparison_hasSum
    (hμ : ∀ w, μ w (finitePlaceIntegralUnits F w) =
      additiveHaarDifferent F w (w.adicCompletionIntegers F : Set (w.adicCompletion F)))
    (f : BruhatCompactTest (IdeleClass F)) :
    HasSum (fun ω : PontryaginDual (K F) =>
      (ν.real univ : ℂ)⁻¹ *
        ((Real.log (heckeDiscriminantConductor F (heckeOrdinateCharacter F ω 0)) : ℂ) *
          (idelicWeilCenteredTest F ν ω f).val 0 -
          ∑' j, heckeCenteredPrimeTerm F (heckeOrdinateCharacter F ω 0)
            (idelicWeilCenteredTest F ν ω f) j))
      (-(∑' w : Place F, bruhatFiniteWeilTerm F μ w f)) := by
  let c (w : Place F) := Real.log (w.asIdeal.absNorm : ℝ) / (μ w).real (finitePlaceIntegralUnits F w)
  let g (w : Place F) := bruhatFiniteWeilPullback F w f
  let o (w : Place F) : ℂ := c w • ∫ u in (finitePlaceIntegralUnits F w)ᶜ,
    finiteWeilOrdinaryIntegrand F w (g w) u ∂μ w
  let p (w : Place F) : ℂ := c w • ∫ u in finitePlaceIntegralUnits F w,
    (‖u.val‖ ^ (1 / 2 : ℝ) / ‖1 - u.val‖ : ℝ) • ((g w).val u - (g w).val 1) ∂μ w
  let C (w : Place F) := finiteWeilCanonicalPrincipalValue F w (μ w) (g w)
  have hC : Summable C := summable_of_hasFiniteSupport ((finitePlaceIdelicWeilTerm_tsum F μ hμ
    f.val.val f.property (bruhatCompactTest_locallyConstantAtFinite F f)).2.1)
  have hp : Summable p := summable_of_hasFiniteSupport (idelicWeil_unitCutoff_hasFiniteSupport F μ f)
  have ho : Summable o := (hC.sub hp).congr fun w => by
    change o w + p w - p w = o w
    exact add_sub_cancel_right _ _
  have he : (∑' w, C w) = (∑' w, o w) + (∑' w, p w) := ho.tsum_add hp
  letI (w : Place F) : (additiveHaarDifferent F w).IsAddHaarMeasure :=
    additiveHaarDifferent_isHaar F w
  have h := ((idelicWeil_discriminantContact_hasSum F ν f).add
    (idelicWeil_conductorContact_hasSum F ν (additiveHaarDifferent F) μ hμ f)).sub
      (idelicWeil_primeTerms_hasSum F μ ν f)
  have hEval :
      (Real.log ((discr F).natAbs : ℝ) : ℂ) * f.val.val 1 + (-(∑' w, p w)) - (∑' w, o w) =
        -(∑' w : Place F, bruhatFiniteWeilTerm F μ w f) := by
    rw [bruhatFiniteWeilTerm_tsum_apply_canonical F μ hμ f]
    change _ = -((∑' w, C w) - (Real.log ((discr F).natAbs : ℝ) : ℂ) * f.val.val 1)
    rw [he]
    ring
  change HasSum _ ((Real.log ((discr F).natAbs : ℝ) : ℂ) * f.val.val 1 + (-(∑' w, p w)) -
    (∑' w, o w)) at h
  rw [hEval] at h
  refine h.congr_fun fun ω => ?_
  let χ := heckeOrdinateCharacter F ω 0
  have hc : (((∑' w : Place F, (heckeConductorExponent F χ w : ℝ) *
      Real.log (w.asIdeal.absNorm : ℝ)) : ℝ) : ℂ) =
        ∑' w : Place F, (heckeConductorExponent F χ w : ℂ) *
          (Real.log (w.asIdeal.absNorm : ℝ) : ℂ) := by
    let a (w : Place F) := (heckeConductorExponent F χ w : ℝ) * Real.log (w.asIdeal.absNorm : ℝ)
    have ha : Summable a := summable_of_hasFiniteSupport <|
      (heckeConductorExponent_finiteSupport F χ).subset fun w hw => by
        by_contra h
        have hzero := Function.notMem_support.mp h
        exact hw (by simp only [a, hzero, Nat.cast_zero, zero_mul])
    simpa only [a, Complex.ofRealCLM_apply, Complex.ofReal_mul, Complex.ofReal_natCast] using
      Complex.ofRealCLM.map_tsum ha
  change _ * ((Real.log (heckeDiscriminantConductor F χ) : ℂ) * _ - _) = _
  rw [heckeDiscriminantConductor_log_eq_local, Complex.ofReal_add, hc]
  ring

end
end Masullo
