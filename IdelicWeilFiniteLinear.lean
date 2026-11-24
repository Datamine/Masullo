import IdelicFiniteUnitInvariance

open IsDedekindDomain MeasureTheory NumberField
open scoped Classical NumberField

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]
local notation "Place" => HeightOneSpectrum (𝓞 F)
private abbrev LocalField (v : Place) := v.adicCompletion F

local instance : LocallyCompactSpace (IdeleClass F) := ideleClasses_locallyCompact
local instance : T2Space (IdeleClass F) := ideleClasses_hausdorff

variable [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)]
  [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)ˣ]
  (μ : ∀ v : HeightOneSpectrum (𝓞 F), Measure (v.adicCompletion F)ˣ)
  [∀ v : HeightOneSpectrum (𝓞 F), (μ v).IsHaarMeasure]

/-- Pull back an actual compact Bruhat test to a finite local test. -/
def bruhatFiniteWeilPullback (v : Place) :
    BruhatCompactTest (IdeleClass F) →ₗ[ℂ] locallyConstantTests (LocalField F v)ˣ where
  toFun f := finitePlaceIdelicTest F f.val.val f.property (bruhatCompactTest_locallyConstantAtFinite F f) v
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

def finiteWeilLocalLinear (v : Place) : locallyConstantTests (LocalField F v)ˣ →ₗ[ℂ] ℂ :=
  letI := additiveHaarDifferent_isHaar F v
  let c := Real.log (v.asIdeal.absNorm : ℝ) / (μ v).real (finitePlaceIntegralUnits F v)
  let m := (μ v).real (finitePlaceIntegralUnits F v)
  (c : ℂ) • -(m : ℂ) •
    ((finiteLogFourierPairing F v (additiveHaarDifferent F v)).comp (finiteWeilTestLinear F v))

/-- The normalized finite-place Weil summand as a linear functional on compact Bruhat tests. -/
def bruhatFiniteWeilLinear (v : Place) : BruhatCompactTest (IdeleClass F) →ₗ[ℂ] ℂ :=
  (finiteWeilLocalLinear F μ v).comp (bruhatFiniteWeilPullback F v)

omit [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)ˣ]
  [∀ v : HeightOneSpectrum (𝓞 F), (μ v).IsHaarMeasure] in
theorem bruhatFiniteWeilLinear_apply (v : Place) (f : BruhatCompactTest (IdeleClass F)) :
    bruhatFiniteWeilLinear F μ v f =
      finitePlaceIdelicWeilTerm F μ f.val.val f.property (bruhatCompactTest_locallyConstantAtFinite F f) v := by
  rw [finitePlaceIdelicWeilTerm, finiteWeilPrincipalValue_apply_linear]
  rfl

end
end Masullo
