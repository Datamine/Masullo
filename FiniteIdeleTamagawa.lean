import AdelicTamagawaProduct
import LocalMultiplicativeHaar

open IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped ENNReal NumberField

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

private abbrev Place := HeightOneSpectrum (𝓞 F)
private abbrev LocalField (v : Place F) := v.adicCompletion F

variable [∀ v : Place F, MeasurableSpace (LocalField F v)]
  [∀ v : Place F, BorelSpace (LocalField F v)]
  [∀ v : Place F, MeasurableSpace (LocalField F v)ˣ]
  [∀ v : Place F, BorelSpace (LocalField F v)ˣ]

private def localMultiplicativeDensity (v : Place F) : Measure (LocalField F v)ˣ :=
  finitePlaceUnitDensity F v (additiveHaarDifferent F v)

private theorem localMultiplicativeDensity_isHaar (v : Place F) :
    (localMultiplicativeDensity F v).IsHaarMeasure := by
  letI := additiveHaarDifferent_isHaar F v
  exact finitePlaceUnitDensity_haar F v (additiveHaarDifferent F v)

private theorem localMultiplicativeDensity_units_ne_zero (v : Place F) :
    localMultiplicativeDensity F v (finitePlaceIntegralUnits F v) ≠ 0 := by
  letI := localMultiplicativeDensity_isHaar F v
  exact (localIntegralUnits_open F v).measure_ne_zero (localMultiplicativeDensity F v)
    ⟨1, (v.adicCompletionIntegers F).toSubmonoid.units.one_mem⟩

private theorem localMultiplicativeDensity_units_ne_top (v : Place F) :
    localMultiplicativeDensity F v (finitePlaceIntegralUnits F v) ≠ ⊤ := by
  letI := localMultiplicativeDensity_isHaar F v
  exact (localIntegralUnits_compact F v).measure_ne_top

/-- The finite multiplicative Tamagawa factor with the prescribed
discriminant mass on the compact group of integral units. -/
def finitePlaceMultiplicativeTamagawa (v : Place F) : Measure (LocalField F v)ˣ :=
  (differentPrimeMass F v / localMultiplicativeDensity F v (finitePlaceIntegralUnits F v)) •
    localMultiplicativeDensity F v

theorem finitePlaceMultiplicativeTamagawa_units (v : Place F) :
    finitePlaceMultiplicativeTamagawa F v (finitePlaceIntegralUnits F v) =
      differentPrimeMass F v := by
  change (differentPrimeMass F v / localMultiplicativeDensity F v (finitePlaceIntegralUnits F v)) *
    localMultiplicativeDensity F v (finitePlaceIntegralUnits F v) = differentPrimeMass F v
  exact ENNReal.div_mul_cancel (localMultiplicativeDensity_units_ne_zero F v)
    (localMultiplicativeDensity_units_ne_top F v)

theorem finitePlaceMultiplicativeTamagawa_isHaar (v : Place F) :
    (finitePlaceMultiplicativeTamagawa F v).IsHaarMeasure := by
  letI := localMultiplicativeDensity_isHaar F v
  apply Measure.IsHaarMeasure.smul
  · exact ENNReal.div_ne_zero.mpr ⟨differentPrimeMass_ne_zero F v,
      localMultiplicativeDensity_units_ne_top F v⟩
  · exact ENNReal.div_ne_top (differentPrimeMass_ne_top F v)
      (localMultiplicativeDensity_units_ne_zero F v)

theorem finitePlaceMultiplicativeTamagawa_eq_density (v : Place F) :
    finitePlaceMultiplicativeTamagawa F v =
      ((Ideal.absNorm v.asIdeal : ℝ≥0∞) / (Ideal.absNorm v.asIdeal - 1 : ℝ≥0∞)) •
        finitePlaceUnitDensity F v (additiveHaarDifferent F v) := by
  letI := additiveHaarDifferent_isHaar F v
  letI := finitePlaceMultiplicativeTamagawa_isHaar F v
  apply finitePlaceTamagawa_density
  rw [finitePlaceMultiplicativeTamagawa_units, additiveHaarDifferent_integers]

/-- Only finitely many finite factors have integral-unit mass different from one. -/
theorem finitePlaceMultiplicativeTamagawa_units_finite :
    (fun v : Place F => finitePlaceMultiplicativeTamagawa F v (finitePlaceIntegralUnits F v)).HasFiniteMulSupport := by
  simp_rw [finitePlaceMultiplicativeTamagawa_units]
  exact differentPrimeMass_finite F

/-- The product of the finite integral-unit masses is the inverse square
root of the absolute global discriminant. -/
theorem finitePlaceMultiplicativeTamagawa_units_finprod :
    (∏ᶠ v : Place F, finitePlaceMultiplicativeTamagawa F v (finitePlaceIntegralUnits F v)) =
      (NNReal.sqrt ‖discr F‖₊ : ℝ≥0∞)⁻¹ := by
  simp_rw [finitePlaceMultiplicativeTamagawa_units]
  exact differentPrimeMass_finprod F

end
end Masullo
