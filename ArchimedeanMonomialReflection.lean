import RealTateFunctionalEquation
import ComplexTateFunctionalEquation

open Filter MeasureTheory Topology FourierTransform
open scoped SchwartzMap

namespace Masullo

noncomputable section

private theorem translateSpectralGerm (c a : ℂ) :
    Tendsto (fun z : ℂ ↦ z + a) (𝓝[≠] c) (𝓝[≠] (c + a)) := by
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨(continuous_id.add continuous_const).continuousAt.tendsto.mono_left nhdsWithin_le_nhds, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact fun he ↦ hz (add_right_cancel (Set.mem_singleton_iff.mp he))

/-- Corrected (5.3.3.29) for the positive real Fourier kernel. -/
theorem realMellinMonomial_fourier_reflection [MeasurableSpace ℝˣ] [BorelSpace ℝˣ]
    (a n : ℕ) (f : 𝓢(ℝ, ℂ)) (c : ℂ) :
    realArchimedeanZetaContinued a (realMellinMonomial n f) =ᶠ[𝓝[≠] c]
      fun z ↦
        let w := z + (n : ℂ)
        (-Complex.I) ^ ((a + n) % 2) *
          (realArchZetaDenominator (a + n) (1 - w) / realArchZetaDenominator (a + n) w) *
          realArchimedeanZetaContinued (a + n) (𝓕⁻ f) (1 - w) := by
  exact (realMellinMonomial_shift a n f c).trans
    ((realTate_fourier_meromorphic (a + n) f (c + n)).comp_tendsto
      (translateSpectralGerm c n))

attribute [local instance] complexZeta_circleMeasurable
local instance : MeasurableSpace ℂˣ := borel _
local instance : BorelSpace ℂˣ := ⟨rfl⟩

/-- Corrected (5.3.3.31) for the positive complex trace Fourier kernel. -/
theorem complexMellinMonomial_fourier_reflection (n : ℤ) (p q : ℕ) (f : 𝓢(ℂ, ℂ)) (c : ℂ) :
    complexArchimedeanZetaContinued complexTamagawaAngularMeasure n (complexMellinMonomial p q f)
      =ᶠ[𝓝[≠] c] fun z ↦
        let m := n + (p : ℤ) - q
        let w := z + ((p : ℂ) + q) / 2
        (-Complex.I) ^ m.natAbs *
          (complexArchZetaDenominator (-m) (1 - w) / complexArchZetaDenominator m w) *
          complexArchimedeanZetaContinued complexTamagawaAngularMeasure (-m)
            (complexTateFourier f) (1 - w) := by
  exact (complexMellinMonomial_shift complexTamagawaAngularMeasure n p q f c).trans
    ((complexTate_fourier_meromorphic (n + (p : ℤ) - q) f
      (c + ((p : ℂ) + q) / 2)).comp_tendsto (translateSpectralGerm c (((p : ℂ) + q) / 2)))

end
end Masullo
