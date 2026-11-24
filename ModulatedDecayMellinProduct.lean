import ModulatedDecayMellin
import ModulatedDecaySplitCoordinates
import MellinStrip

open Filter Function MeasureTheory Set Topology

namespace Masullo
noncomputable section

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  (m : G →ₜ* Multiplicative ℝ) (τ : Multiplicative ℝ →ₜ* G) (hτ : RightInverse τ m)

local notation "K" => m.toMonoidHom.ker

include hτ in
/-- Separated decay tests have the Fourier–Mellin product formula for the
split Haar measure. The angular factor is written with the positive character. -/
theorem decayMellin_integral_of_product (ν : Measure K) [IsFiniteMeasure ν]
    {I : Set ℝ} (f : ModulatedExponentialInductive m I)
    (u : K → ℂ) (r : ℝ → ℂ) (ω : PontryaginDual K) (z : ℂ) (hI : I.Nonempty)
    (hf : ∀ g, f.val g = u (modulatedKernelProjection m τ hτ g) * r (modulatedLog m g)) :
    (∫ g, decayMellinIntegrand m (ω.comp (modulatedKernelProjection m τ hτ)) f z g
      ∂modulatedLogMeasure m τ hτ ν) =
      (∫ k, u k * (ω k : ℂ) ∂ν) * (∫ t, r t * Complex.exp (z * (t : ℂ))) := by
  let α := modulatedKernelProjection m τ hτ
  let e := modulatedLogSplit m τ hτ
  let χ : PontryaginDual G := ω.comp α
  let v := decayMellinIntegrand m χ f z
  have hvc : Continuous v := continuous_decayMellinIntegrand m χ f z hI
  have hi : (∫ g, v g ∂modulatedLogMeasure m τ hτ ν) = ∫ p, v (e p) ∂volume.prod ν :=
    integral_map e.continuous.measurable.aemeasurable hvc.aestronglyMeasurable
  rw [hi, mul_comm]
  have he (p : ℝ × K) : v (e p) =
      (r p.1 * Complex.exp (z * (p.1 : ℂ))) * (u p.2 * (ω p.2 : ℂ)) := by
    have hα : α (e p) = p.2 := by
      change α (τ (Multiplicative.ofAdd p.1) * p.2.val) = p.2
      exact modulatedKernelProjection_split m τ hτ p.2 p.1
    have hlog : modulatedLog m (e p) = p.1 := by
      change (m (τ (Multiplicative.ofAdd p.1) * p.2.val)).toAdd = p.1
      rw [map_mul, hτ, show m p.2.val = 1 from p.2.property, mul_one]
      rfl
    change f.val (e p) * (ω (α (e p)) : ℂ) * Complex.exp (z * (modulatedLog m (e p) : ℂ)) = _
    rw [hf]
    change (u (α (e p)) * r (modulatedLog m (e p))) * (ω (α (e p)) : ℂ) *
      Complex.exp (z * (modulatedLog m (e p) : ℂ)) = _
    rw [hα, hlog]
    ring
  simp only [he]
  exact integral_prod_mul (μ := volume) (ν := ν)
    (fun t : ℝ => r t * Complex.exp (z * (t : ℂ))) (fun k : K => u k * (ω k : ℂ))

include hτ in
/-- On a pure tensor, the angular Haar integral is the Fourier transform at
 the inverted dual character and the radial factor is the usual Mellin integral. -/
theorem decayMellin_fourier_mul_mellin (ν : Measure K) [IsFiniteMeasure ν]
    {I : Set ℝ} (f : ModulatedExponentialInductive m I)
    (u : K → ℂ) (r : ℝ → ℂ) (ω : PontryaginDual K) (z : ℂ) (hI : I.Nonempty)
    (hf : ∀ g, f.val g = u (modulatedKernelProjection m τ hτ g) * r (modulatedLog m g)) :
    (∫ g, decayMellinIntegrand m (ω.comp (modulatedKernelProjection m τ hτ)) f z g
      ∂modulatedLogMeasure m τ hτ ν) =
      lcaFourier ν u ω⁻¹ * mellin (fun t => r (Real.log t)) z := by
  rw [decayMellin_integral_of_product m τ hτ ν f u r ω z hI hf, mellin_eq_log_integral]
  have hinv (k : K) : star (ω⁻¹ k : ℂ) = (ω k : ℂ) := by
    change star (((ω k)⁻¹ : Circle) : ℂ) = _
    rw [Circle.coe_inv_eq_conj, ← Complex.star_def, star_star]
  simp only [lcaFourier, hinv, Real.log_exp]
  congr 1
  exact integral_congr_ae (.of_forall fun _ => mul_comm _ _)

include hτ in
/-- The Haar normalization rescales every separated transform by the same
positive constant. -/
theorem decayMellin_fourier_mul_mellin_haar [SecondCountableTopology G]
    (μ : Measure G) [μ.IsHaarMeasure] (ν : Measure K) [ν.IsHaarMeasure] [IsFiniteMeasure ν] :
    ∃ c : ℝ, 0 < c ∧
      ∀ {I : Set ℝ} (f : ModulatedExponentialInductive m I)
        (u : K → ℂ) (r : ℝ → ℂ) (ω : PontryaginDual K) (z : ℂ),
        I.Nonempty →
        (∀ g, f.val g = u (modulatedKernelProjection m τ hτ g) * r (modulatedLog m g)) →
        (∫ g, decayMellinIntegrand m (ω.comp (modulatedKernelProjection m τ hτ)) f z g ∂μ) =
          c • (lcaFourier ν u ω⁻¹ * mellin (fun t => r (Real.log t)) z) := by
  let ρ := modulatedLogMeasure m τ hτ ν
  letI : ρ.IsHaarMeasure := modulatedLogMeasure_isHaar m τ hτ ν
  let k := Measure.haarScalarFactor μ ρ
  have hk : 0 < (k : ℝ) := by exact_mod_cast Measure.haarScalarFactor_pos_of_isHaarMeasure μ ρ
  have hμ : μ = k • ρ := Measure.isMulLeftInvariant_eq_smul μ ρ
  refine ⟨k, hk, ?_⟩
  intro I f u r ω z hI hf
  rw [hμ, integral_smul_nnreal_measure,
    decayMellin_fourier_mul_mellin m τ hτ ν f u r ω z hI hf]
  rfl

end
end Masullo
