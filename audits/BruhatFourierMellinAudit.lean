import RiemannMasullo.AppD_SchwartzBruhat.Sec3a_part2
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! Run with `lake env lean` in original revision
`553ef728d88838327946035310ffdef2589e3844` on Lean 4.36.0. -/

open MeasureTheory RiemannMasullo
open scoped NNReal ENNReal

namespace Masullo

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]

/-- The Fourier–Mellin integral for any Haar measure is a positive scalar
multiple of the one for the canonical Haar measure. -/
theorem bruhat_fourierMellin_haar_scaling
    (m : G →ₜ* ℝ≥0ˣ) (I : Set ℝ) (hm : IsModulation m)
    (μ : Measure G) [μ.IsHaarMeasure] :
    ∃ a : ℝ, 0 < a ∧ ∀ (f : G → ℂ) (c : QuasiCharacter G),
      modulatedFourierMellin m I hm μ f c =
        a • modulatedFourierMellin m I hm (canonicalModulatedHaar m hm) f c := by
  let ν := canonicalModulatedHaar m hm
  let : ν.IsHaarMeasure := (Classical.choose_spec (existsUnique_canonicalModulatedHaar m hm).exists).1
  let k := Measure.haarScalarFactor μ ν
  have hμ : μ = k • ν := Measure.isMulLeftInvariant_eq_smul μ ν
  refine ⟨(k : ℝ), Measure.haarScalarFactor_pos_of_isHaarMeasure μ ν, ?_⟩
  intro f c
  unfold modulatedFourierMellin
  by_cases hc : c ∈ relativeVerticalStrip m.toMonoidHom hm.1 hm.2 I
  · rw [Set.indicator_of_mem hc, Set.indicator_of_mem hc, hμ]
    exact integral_smul_measure _ (k : ℝ≥0∞)
  · rw [Set.indicator_of_notMem hc, Set.indicator_of_notMem hc, smul_zero]

#print axioms RiemannMasullo.modulatedExponentialDecay_tensor_equiv
#print axioms RiemannMasullo.modulatedExponentialDecay_tensor_equivariant
#print axioms RiemannMasullo.modulatedExponentialDecay_tensor_stage
#print axioms RiemannMasullo.modulatedExponentialDecay_stage_tensor_comparison
#print axioms RiemannMasullo.modulatedExponentialDecay_bounded_image_stage
#print axioms RiemannMasullo.modulatedExponentialDecay_strictLF
#print axioms RiemannMasullo.modulatedExponentialDecay_complete
#print axioms RiemannMasullo.modulatedExponentialDecay_nuclear
#print axioms RiemannMasullo.modulatedExponentialDecay_montel
#print axioms RiemannMasullo.modulatedExponentialDecay_bornological
#print axioms RiemannMasullo.modulatedExponentialDecay_frechet
#print axioms RiemannMasullo.modulatedExponentialDecay_strongDual_complete
#print axioms RiemannMasullo.modulatedExponentialDecay_strongDual_nuclear
#print axioms RiemannMasullo.modulatedExponentialDecay_strongDual_montel
#print axioms RiemannMasullo.modulatedExponentialDecay_continuous_inclusion
#print axioms RiemannMasullo.modulatedExponentialDecay_compact_projective_topology
#print axioms RiemannMasullo.modulatedExponentialDecay_tensor_comparison_bounded
#print axioms RiemannMasullo.modulatedExponentialDecay_stage_tensor_equiv_swap
#print axioms RiemannMasullo.modulatedExponentialDecayStage_frechet
#print axioms RiemannMasullo.modulatedExponentialDecayStage_nuclear
#print axioms RiemannMasullo.modulatedExponentialDecayStage_separable
#print axioms RiemannMasullo.modulatedExponentialDecay_bounded_separable_metrizable
#print axioms RiemannMasullo.modulatedExponentialDecay_twists_continuous
#print axioms RiemannMasullo.modulatedExponentialDecay_bounded_iff_projective
#print axioms RiemannMasullo.modulatedExponentialDecay_bounded_iff_twists
#print axioms RiemannMasullo.modulatedExponentialDecay_bounded_iff_countable_twists
#print axioms bruhat_fourierMellin_haar_scaling
#print axioms RiemannMasullo.modulatedFourierMellin_integrable
#print axioms RiemannMasullo.modulatedFourierMellin_holomorphic
#print axioms RiemannMasullo.modulatedFourierMellin_linear
#print axioms RiemannMasullo.modulatedFourierMellin_equivariant
#print axioms RiemannMasullo.modulatedFourierMellin_injective
#print axioms RiemannMasullo.modulatedFourierMellin_tensor
#print axioms RiemannMasullo.IsModulation.exists_section
#print axioms RiemannMasullo.canonicalModulatedHaar_eq_map_prod

end Masullo
