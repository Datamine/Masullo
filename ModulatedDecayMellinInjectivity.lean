import ModulatedDecayMellinEvaluation
import ModulatedDecaySplitCoordinates
import ModulatedSobolevQuasiCharacters
import Mathlib.Topology.Metrizable.Urysohn

open Function MeasureTheory Set Topology

namespace Masullo
noncomputable section

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
  (m : G →ₜ* Multiplicative ℝ) (τ : Multiplicative ℝ →ₜ* G) (hτ : RightInverse τ m)

local notation "K" => m.toMonoidHom.ker

/-- The Fourier–Mellin transform is already injective on the vertical line
at any single abscissa in the decay interval, using all compact characters. -/
theorem decayMellinEvaluation_eq_zero_of_verticalLine
    (hm : IsProperMap m) (μ : Measure G) [μ.IsHaarMeasure] {I : Set ℝ} (a : I)
    (f : ModulatedExponentialInductive m I)
    (hf : ∀ (ω : PontryaginDual K) (t : ℝ),
      decayMellinEvaluation μ m (ω.comp (modulatedKernelProjection m τ hτ))
        (⟨a.val, t⟩ : ℂ) a.property f = 0) : f = 0 := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp
    (hm.isCompact_preimage (isCompact_singleton (x := (1 : Multiplicative ℝ))))
  let α := modulatedKernelProjection m τ hτ
  let A := modulatedDecayTwistCLM m I a f
  have hFour (η : PontryaginDual G) : lcaFourier μ A.val η = 0 := by
    let q : G →ₜ* ℂ :=
      ⟨Circle.coeHom.comp (η⁻¹).toMonoidHom, continuous_subtype_val.comp (η⁻¹).continuous⟩
    obtain ⟨⟨ω, c⟩, ⟨hcoord, hnorm⟩, _⟩ := modulatedLogQuasiCharacter_coordinates m τ hτ q
    have hc : c.re = 0 := by
      have h := hnorm (τ (Multiplicative.ofAdd (1 : ℝ)))
      change ‖((η⁻¹) (τ (Multiplicative.ofAdd (1 : ℝ))) : ℂ)‖ = _ at h
      rw [Circle.norm_coe, hτ] at h
      change 1 = Real.exp (c.re * 1) at h
      apply Real.exp_injective
      simpa only [mul_one, Real.exp_zero] using h.symm
    have hq (g : G) : q g = (ω (α g) : ℂ) * Complex.exp (c * (modulatedLog m g : ℂ)) := by
      have hg : τ (m g) * (α g).val = g := by
        change τ (m g) * (g / τ (m g)) = g
        rw [mul_comm, div_mul_cancel]
      have h := hcoord (modulatedLog m g) (α g)
      change q (τ (m g) * (α g).val) = _ at h
      exact (congrArg q hg).symm.trans h
    let z : ℂ := ⟨a.val, c.im⟩
    have hz : z = (a.val : ℂ) + c := by
      apply Complex.ext <;> simp [z, hc]
    have he : lcaFourier μ A.val η = decayMellinEvaluation μ m (ω.comp α) z a.property f := by
      change (∫ g, A.val g * star (η g : ℂ) ∂μ) =
        ∫ g, decayMellinIntegrand m (ω.comp α) f z g ∂μ
      apply integral_congr_ae
      exact .of_forall fun g => by
        have hqstar : star (η g : ℂ) = q g := by
          change star (η g : ℂ) = (((η g)⁻¹ : Circle) : ℂ)
          rw [Circle.coe_inv_eq_conj, Complex.star_def]
        change A.val g * star (η g : ℂ) = decayMellinIntegrand m (ω.comp α) f z g
        rw [hqstar, hq]
        change ((Real.exp (a.val * modulatedLog m g) : ℂ) * f.val g) *
            ((ω (α g) : ℂ) * Complex.exp (c * (modulatedLog m g : ℂ))) =
          f.val g * (ω (α g) : ℂ) * Complex.exp (z * (modulatedLog m g : ℂ))
        rw [hz, add_mul, Complex.exp_add, ← Complex.ofReal_mul, ← Complex.ofReal_exp]
        ring
    exact he.trans (hf ω c.im)
  have hA := ae_eq_zero_of_lcaFourier_eq_zero μ (bruhatSchwartz_integrable μ A) hFour
  have hzero : A.val = 0 := Measure.eq_of_ae_eq hA (bruhatSchwartz_continuous A) continuous_const
  apply Subtype.ext
  funext g
  have hz := congrFun hzero g
  change (Real.exp (a.val * modulatedLog m g) : ℂ) * f.val g = 0 at hz
  exact (mul_eq_zero.mp hz).resolve_left (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _))


end
end Masullo
