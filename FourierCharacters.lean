import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace Masullo

open MeasureTheory Set Filter
open scoped FourierTransform

/-- The directional derivative in the manuscript is the ordinary real
derivative of the restriction to a translate of the one-parameter group. -/
noncomputable def characterDirection {G : Type*} [Monoid G] (a : ℝ → G)
    (χ : G →* ℂ) (g : G) : ℂ :=
  deriv (fun t : ℝ => χ (g * a t)) 0

/-- D.1.6.15. With the manuscript's exponential normalization at
frequency `σ`, the first-order symbol is `2πiσ`. The formula is also
proved for evaluation at points other than the identity. -/
theorem characterDirection_eq_frequency {G : Type*} [Monoid G]
    (a : Multiplicative ℝ →* G) (χ : G →* ℂ) (σ : ℝ)
    (hσ : ∀ t : ℝ, χ (a (Multiplicative.ofAdd t)) =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (σ : ℂ) * (t : ℂ))) :
    (∀ g, characterDirection (fun t => a (Multiplicative.ofAdd t)) χ g =
      (2 * (Real.pi : ℂ) * Complex.I * (σ : ℂ)) * χ g) ∧
    characterDirection (fun t => a (Multiplicative.ofAdd t)) χ 1 =
      2 * (Real.pi : ℂ) * Complex.I * (σ : ℂ) := by
  let c := 2 * (Real.pi : ℂ) * Complex.I * (σ : ℂ)
  have h (g : G) : characterDirection (fun t => a (Multiplicative.ofAdd t)) χ g =
      c * χ g := by
    have hfun : (fun t : ℝ => χ (g * a (Multiplicative.ofAdd t))) =
        fun t : ℝ => χ g * Complex.exp (c * (t : ℂ)) := by
      funext t
      rw [map_mul, hσ t]
    have hz : HasDerivAt (fun z : ℂ => Complex.exp (c * z)) c 0 := by
      simpa using ((hasDerivAt_id' (0 : ℂ)).const_mul c).cexp
    rw [characterDirection, hfun, (hz.comp_ofReal.const_mul (χ g)).deriv, mul_comm]
  exact ⟨h, by simpa only [map_one, mul_one] using h 1⟩

private theorem realSingletonIndicator_ae_zero :
    (fun x : ℝ ↦ if x = 0 then (1 : ℂ) else 0) =ᵐ[volume] (0 : ℝ → ℂ) := by
  have hn : ∀ᵐ x : ℝ ∂volume, x ≠ 0 := ae_iff.mpr (by simp)
  filter_upwards [hn] with x hx
  simp [hx]

private theorem realSingletonIndicator_fourier_zero :
    𝓕 (fun x : ℝ ↦ if x = 0 then (1 : ℂ) else 0) = 0 := by
  funext t
  rw [Real.fourier_congr_ae realSingletonIndicator_ae_zero]
  simp [Real.fourier_eq]

/-- D.1.1.2(5) fails for an arbitrary pointwise representative. Changing
an integrable function at one point leaves its Fourier transform unchanged. -/
theorem fourier_pointwise_representative_obstruction :
    let f : ℝ → ℂ := fun x => if x = 0 then 1 else 0
    Integrable f ∧ Integrable (𝓕 f) ∧ ¬ Continuous f ∧
      (𝓕 (𝓕 f)) 0 ≠ f 0 := by
  let f : ℝ → ℂ := fun x => if x = 0 then 1 else 0
  change Integrable f ∧ Integrable (𝓕 f) ∧ ¬ Continuous f ∧ (𝓕 (𝓕 f)) 0 ≠ f 0
  have ha : f =ᵐ[volume] (0 : ℝ → ℂ) := realSingletonIndicator_ae_zero
  have hF : 𝓕 f = 0 := realSingletonIndicator_fourier_zero
  have hz : Integrable (0 : ℝ → ℂ) volume := integrable_zero ℝ ℂ volume
  refine ⟨hz.congr ha.symm, hF.symm ▸ hz, ?_, ?_⟩
  · intro hc
    have he : f = (0 : ℝ → ℂ) :=
      Continuous.ext_on (dense_compl_singleton (0 : ℝ)) hc continuous_const (by
        intro x hx
        simp [f, show x ≠ 0 from hx])
    simpa [f] using congrFun he 0
  · simp [hF, Real.fourier_eq, f]

/-- The singleton indicator has zero Fourier transform but fails translation
invariance as a pointwise function. This is the obstruction in D.1.5.2(3). -/
theorem fourier_pointwise_invariance_obstruction :
    let f : ℝ → ℂ := fun x ↦ if x = 0 then 1 else 0
    Integrable f ∧ 𝓕 f = 0 ∧ f (1 + 0) ≠ f 0 := by
  exact ⟨(integrable_zero ℝ ℂ volume).congr realSingletonIndicator_ae_zero.symm,
    realSingletonIndicator_fourier_zero, by norm_num⟩

end Masullo
