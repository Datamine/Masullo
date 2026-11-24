import ModulatedDecayMellin
import ModulatedDecaySplitCoordinates
import ModulatedSobolevQuasiCharacters

open Function MeasureTheory Set Topology

namespace Masullo
noncomputable section

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  (m : G →ₜ* Multiplicative ℝ) (τ : Multiplicative ℝ →ₜ* G) (hτ : RightInverse τ m)

local notation "K" => m.toMonoidHom.ker

include hτ in
omit [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] in
/-- Each continuous quasi-character has unique compact-character and complex
exponent coordinates, with the formula on the original group. -/
theorem modulatedMellin_existsUnique_quasiCharacter_formula (hm : IsProperMap m) (q : G →ₜ* ℂ) :
    ∃! p : PontryaginDual K × ℂ, ∀ g,
      q g = (p.1 (modulatedKernelProjection m τ hτ g) : ℂ) *
        Complex.exp (p.2 * (modulatedLog m g : ℂ)) := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp
    (hm.isCompact_preimage (isCompact_singleton (x := (1 : Multiplicative ℝ))))
  let α := modulatedKernelProjection m τ hτ
  obtain ⟨p, hp, huv⟩ := modulatedLogQuasiCharacter_coordinates m τ hτ q
  refine ⟨p, fun g => ?_, fun r hr => ?_⟩
  · have hg : τ (m g) * (α g).val = g := by
      change τ (m g) * (g / τ (m g)) = g
      rw [mul_comm, div_mul_cancel]
    have h := hp.1 (modulatedLog m g) (α g)
    change q (τ (m g) * (α g).val) = _ at h
    exact (congrArg q hg).symm.trans h
  · apply huv
    refine ⟨?_, ?_⟩
    · intro x k
      let g := τ (Multiplicative.ofAdd x) * k.val
      have hlog : modulatedLog m g = x := by
        change (m (τ (Multiplicative.ofAdd x) * k.val)).toAdd = x
        rw [map_mul, hτ, show m k.val = 1 from k.property, mul_one]
        rfl
      exact (hr g).trans (congrArg₂ (· * ·)
        (congrArg (fun u : K => (r.1 u : ℂ)) (modulatedKernelProjection_split m τ hτ k x))
        (congrArg (fun t : ℝ => Complex.exp (r.2 * (t : ℂ))) hlog))
    · intro g
      rw [hr g, norm_mul, Circle.norm_coe, one_mul, Complex.norm_exp, Complex.mul_re]
      simp [modulatedLog]

/-- On its relative strip, the chart evaluation is the absolutely convergent
Haar integral of the original quasi-character. -/
theorem decayMellinEvaluation_eq_quasiCharacter_integral
    (μ : Measure G) [μ.IsHaarMeasure] {I : Set ℝ} (f : ModulatedExponentialInductive m I)
    (q : G →ₜ* ℂ) (ω : PontryaginDual K) (z : ℂ) (hz : z.re ∈ I)
    (hq : ∀ g, q g = (ω (modulatedKernelProjection m τ hτ g) : ℂ) *
      Complex.exp (z * (modulatedLog m g : ℂ))) :
    Integrable (fun g => f.val g * q g) μ ∧
      decayMellinEvaluation μ m (ω.comp (modulatedKernelProjection m τ hτ)) z hz f =
        ∫ g, f.val g * q g ∂μ := by
  let χ := ω.comp (modulatedKernelProjection m τ hτ)
  have he (g : G) : decayMellinIntegrand m χ f z g = f.val g * q g := by
    rw [hq]
    exact mul_assoc _ _ _
  exact ⟨(decayMellinIntegrand_integrable μ m χ f hz).congr (.of_forall he),
    integral_congr_ae (.of_forall he)⟩


end
end Masullo
