import IdelicWeilFiniteStrongDual
import IdelicWeilInfiniteDual

open Filter IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical NumberField

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]
local notation "Place" => HeightOneSpectrum (𝓞 F)

local instance : LocallyCompactSpace (IdeleClass F) := ideleClasses_locallyCompact
local instance : T2Space (IdeleClass F) := ideleClasses_hausdorff
local instance : MeasurableSpace (normOneIdeleClass F) := borel _
local instance : BorelSpace (normOneIdeleClass F) := ⟨rfl⟩

variable [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)]
  [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)ˣ]
  (μ : ∀ v : HeightOneSpectrum (𝓞 F), Measure (v.adicCompletion F)ˣ)
  (ν : Measure (normOneIdeleClass F)) [ν.IsHaarMeasure]

/-- The geometric side of (B.4.4.16) with a finite set of finite places. -/
def idelicWeilGeometricPartial (S : Finset Place) :
    StrongDual ℂ (BruhatCompactTest (IdeleClass F)) :=
  idelicWeilPolarDual F ν - infinitePlaceIdelicWeilSum F - ∑ v ∈ S, bruhatFiniteWeilTerm F μ v

/-- The geometric side of (B.4.4.16) converges in the strong dual.
The limit gives the two normalized pole terms minus the infinite and finite
local terms, evaluated on the actual compact Bruhat test. -/
theorem idelicWeilGeometric_tendsto :
    ∃ D : StrongDual ℂ (BruhatCompactTest (IdeleClass F)),
      Tendsto (idelicWeilGeometricPartial F μ ν) atTop (𝓝 D) ∧
      ∀ f, D f = idelicWeilPolarDual F ν f -
        (∑ v : InfinitePlace F, infinitePlaceIdelicWeilDual F v f) -
        (∑' v : Place, finitePlaceIdelicWeilTerm F μ f.val.val f.property
          (bruhatCompactTest_locallyConstantAtFinite F f) v) := by
  obtain ⟨L, hL, hEval⟩ := bruhatFiniteWeilTerm_hasSum F μ
  refine ⟨idelicWeilPolarDual F ν - infinitePlaceIdelicWeilSum F - L, ?_, fun f => ?_⟩
  · exact tendsto_const_nhds.sub hL
  · simp only [sub_apply, infinitePlaceIdelicWeilSum_apply, hEval, bruhatFiniteWeilTerm_apply]

end
end Masullo
