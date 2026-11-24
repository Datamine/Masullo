import ArchimedeanFundamentalDomain
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

open Function MeasureTheory NumberField NumberField.Units.dirichletUnitTheorem Set Topology
open scoped ENNReal NNReal Classical

namespace Masullo
noncomputable section

variable (F : Type*) [Field F] [NumberField F]

/-- Dropping the distinguished log coordinate on the norm-one archimedean
ideles pushes Haar measure to a positive multiple of Lebesgue measure. -/
theorem archRegulatorLog_map_haar
    [MeasurableSpace (archNormOne F)] [BorelSpace (archNormOne F)]
    (μ : Measure (archNormOne F)) [μ.IsHaarMeasure] :
    ∃ c : ℝ≥0, 0 < c ∧
      μ.map (fun x => (archRegulatorLog F x).toAdd) = c • (Measure.pi (fun _ : {v : InfinitePlace F // v ≠ w₀} => (volume : Measure ℝ))) := by
  let q (x : archNormOne F) := (archRegulatorLog F x).toAdd
  have hc : Continuous q := continuous_toAdd.comp (archRegulatorLog_continuous F)
  have hs : Surjective q := Multiplicative.toAdd.surjective.comp (archRegulatorLog_surjective F)
  let e := archNormOnePolar F
  have hproj : (archRegulatorLog F : archNormOne F → Multiplicative (logSpace F)) = Prod.fst ∘ e.symm := rfl
  let a : Multiplicative (logSpace F) ≃ₜ logSpace F :=
    ⟨⟨Multiplicative.toAdd, Multiplicative.ofAdd, fun _ => rfl, fun _ => rfl⟩,
      continuous_toAdd, continuous_ofAdd⟩
  have hp : IsProperMap q := by
    change IsProperMap (a ∘ (archRegulatorLog F : archNormOne F → Multiplicative (logSpace F)))
    rw [hproj]
    exact a.isProperMap.comp (isProperMap_fst_of_compactSpace.comp e.symm.toHomeomorph.isProperMap)
  let η := μ.map q
  letI : η.IsAddHaarMeasure :=
    { lt_top_of_isCompact := fun {_} h => by
        rw [show η = μ.map q from rfl, Measure.map_apply hc.measurable h.measurableSet]
        exact (hp.isCompact_preimage h).measure_lt_top
      map_add_left_eq_self := fun t => by
        obtain ⟨g, hg⟩ := hs t
        change Measure.map (t + ·) (Measure.map q μ) = Measure.map q μ
        have ht : Measurable (fun x : logSpace F => t + x) := measurable_const.add measurable_id
        rw [Measure.map_map ht hc.measurable]
        have he : (t + ·) ∘ q = q ∘ (g * ·) := by
          funext x
          exact (congrArg (· + q x) hg).symm.trans (congrArg Multiplicative.toAdd (map_mul (archRegulatorLog F) g x)).symm
        have hg' : Measurable (fun x : archNormOne F => g * x) :=
          (continuous_const.mul continuous_id).measurable
        rw [he, ← Measure.map_map hc.measurable hg', map_mul_left_eq_self]
      open_pos := (hc.isOpenPosMeasure_map hs).open_pos }
  let ρ : Measure (logSpace F) := Measure.pi (fun _ : {v : InfinitePlace F // v ≠ w₀} => (volume : Measure ℝ))
  letI : ρ.IsAddHaarMeasure := isAddHaarMeasure_volume_pi {v : InfinitePlace F // v ≠ w₀}
  exact ⟨Measure.addHaarScalarFactor η ρ, Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure η ρ,
    Measure.isAddLeftInvariant_eq_smul η ρ⟩


end
end Masullo
