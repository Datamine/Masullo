import ModulatedDecayMellin
import ModulatedSobolevQuasiCharacters
import ModulationSection

open Function MeasureTheory Set Topology

namespace Masullo

noncomputable section

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  (m : G →ₜ* Multiplicative ℝ)

omit [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] in
private theorem modulatedLogQuasiCharacter_globalCoordinates
    (τ : Multiplicative ℝ →ₜ* G) (hτ : RightInverse τ m)
    (q : G →ₜ* ℂ) (χ : PontryaginDual m.toMonoidHom.ker) (z : ℂ)
    (h : ∀ (x : ℝ) (k : m.toMonoidHom.ker),
      q (τ (Multiplicative.ofAdd x) * k.val) = (χ k : ℂ) * Complex.exp (z * (x : ℂ)))
    (g : G) :
    q g = (χ (modulatedKernelProjection m τ hτ g) : ℂ) *
      Complex.exp (z * (modulatedLog m g : ℂ)) := by
  let k := modulatedKernelProjection m τ hτ g
  have he : τ (m g) * k.val = g := by
    change τ (m g) * (g / τ (m g)) = g
    rw [← mul_div_assoc, mul_div_cancel_left]
  have hg := h (modulatedLog m g) k
  change q (τ (m g) * k.val) = _ at hg
  exact (congrArg q he).symm.trans hg

/-- The Haar integral in Theorem D.3.3.13 applies to every continuous
quasi-character in the relative strip. Left translation multiplies by
the original quasi-character, with the same Haar normalization. -/
theorem decayMellin_integrable_and_translate_of_quasiCharacter
    (hm : IsProperMap m) (hms : Surjective m)
    (μ : Measure G) [μ.IsHaarMeasure] (I : Set ℝ) (q : G →ₜ* ℂ) :
    ∃ a : ℝ, (∀ g, ‖q g‖ = Real.exp (a * modulatedLog m g)) ∧
      (a ∈ I → ∀ f : ModulatedExponentialInductive m I,
        Integrable (fun g ↦ f.val g * q g) μ ∧
        ∀ y : G, (∫ g, (ModulatedExponentialInductive.translate m I y f).val g * q g ∂μ) =
          q y * ∫ g, f.val g * q g ∂μ) := by
  obtain ⟨τ,hτ⟩ := exists_realModulation_section m hm hms
  letI : CompactSpace m.toMonoidHom.ker := compactSpace_realModulation_ker m hm
  obtain ⟨⟨χ,z⟩, ⟨hcoord,hnorm⟩, _⟩ := modulatedLogQuasiCharacter_coordinates m τ hτ q
  refine ⟨z.re,hnorm,fun hz f ↦ ?_⟩
  let α := modulatedKernelProjection m τ hτ
  let ξ := χ.comp α
  have heq (g : G) :
      q g = (ξ g : ℂ) * Complex.exp (z * (modulatedLog m g : ℂ)) :=
    modulatedLogQuasiCharacter_globalCoordinates m τ hτ q χ z hcoord g
  have he (u : ModulatedExponentialInductive m I) (g : G) :
      u.val g * q g = decayMellinIntegrand m ξ u z g := by
    rw [heq g]
    exact (mul_assoc _ _ _).symm
  constructor
  · exact (decayMellinIntegrand_integrable μ m ξ f hz).congr
      (.of_forall fun g ↦ (he f g).symm)
  · intro y
    simp only [he]
    have hy := decayMellinEvaluation_translate μ m ξ hz f y
    change (∫ g, decayMellinIntegrand m ξ (ModulatedExponentialInductive.translate m I y f) z g ∂μ) =
      ((ξ y : ℂ) * Complex.exp (z * (modulatedLog m y : ℂ))) *
        ∫ g, decayMellinIntegrand m ξ f z g ∂μ at hy
    rw [← heq y] at hy
    exact hy

/-- In the charts supplied by a real modulation, the actual Fourier–Mellin
integral is holomorphic on each open relative strip. -/
theorem decayMellin_holomorphic_in_character_charts [SecondCountableTopology G]
    (hm : IsProperMap m) (hms : Surjective m)
    (μ : Measure G) [μ.IsHaarMeasure] (I : Set ℝ) (hI : IsOpen I) :
    ∃ (τ : Multiplicative ℝ →ₜ* G) (hτ : RightInverse τ m),
      ∀ (χ : PontryaginDual m.toMonoidHom.ker) (f : ModulatedExponentialInductive m I),
        DifferentiableOn ℂ (fun z ↦ ∫ g,
          decayMellinIntegrand m (χ.comp (modulatedKernelProjection m τ hτ)) f z g ∂μ)
          (Complex.re ⁻¹' I) := by
  obtain ⟨τ,hτ⟩ := exists_realModulation_section m hm hms
  refine ⟨τ,hτ,fun χ f z hz ↦ ?_⟩
  have hz' : z.re ∈ interior I := hI.interior_eq.symm ▸ hz
  exact (decayMellin_hasDerivAt μ m hm hms
    (χ.comp (modulatedKernelProjection m τ hτ)) f hz').differentiableAt.differentiableWithinAt

end
end Masullo
