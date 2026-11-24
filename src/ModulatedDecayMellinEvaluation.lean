import ModulatedDecayMellin
import BruhatFourierTransform

open MeasureTheory Set Topology

namespace Masullo
noncomputable section

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  (m : G →ₜ* Multiplicative ℝ) (μ : Measure G) [μ.IsHaarMeasure] {I : Set ℝ}

/-- The unitary part of the spectral parameter acts through the logarithmic modulus. -/
def decayMellinPhase (t : ℝ) : PontryaginDual G :=
  ⟨{ toFun := fun g => Circle.exp (t * modulatedLog m g)
     map_one' := by simp [modulatedLog]
     map_mul' := by intro x y; simp only [modulatedLog, map_mul, toAdd_mul, mul_add, Circle.exp_add] },
   Circle.exp.continuous.comp (continuous_const.mul (continuous_toAdd.comp m.continuous))⟩

/-- A Fourier–Mellin evaluation is an ordinary Fourier evaluation of the
Schwartz–Bruhat twist at the real part of its parameter. -/
theorem decayMellinEvaluation_eq_lcaFourier (χ : PontryaginDual G) (z : ℂ) (hz : z.re ∈ I)
    (f : ModulatedExponentialInductive m I) :
    decayMellinEvaluation μ m χ z hz f =
      lcaFourier μ (modulatedDecayTwistCLM m I ⟨z.re, hz⟩ f).val (χ * decayMellinPhase m z.im)⁻¹ := by
  change (∫ g, decayMellinIntegrand m χ f z g ∂μ) = _
  rw [lcaFourier]
  apply integral_congr_ae
  exact .of_forall fun g => by
    let x := modulatedLog m g
    have hinv : star (((χ * decayMellinPhase m z.im)⁻¹ g : Circle) : ℂ) =
        ((χ * decayMellinPhase m z.im) g : ℂ) := by
      change star ((((χ * decayMellinPhase m z.im) g)⁻¹ : Circle) : ℂ) = _
      rw [Circle.coe_inv_eq_conj, ← Complex.star_def, star_star]
    have hzexp : Complex.exp (z * (x : ℂ)) =
        (Real.exp (z.re * x) : ℂ) * (Circle.exp (z.im * x) : ℂ) := by
      rw [Complex.ofReal_exp, Circle.coe_exp, ← Complex.exp_add]
      congr 1
      conv_lhs => rw [← Complex.re_add_im z]
      push_cast
      ring
    change decayMellinIntegrand m χ f z g =
      (modulatedDecayTwistCLM m I ⟨z.re, hz⟩ f).val g * star (((χ * decayMellinPhase m z.im)⁻¹ g : Circle) : ℂ)
    rw [hinv]
    change f.val g * (χ g : ℂ) * Complex.exp (z * (x : ℂ)) =
      ((Real.exp (z.re * x) : ℂ) * f.val g) * ((χ g : ℂ) * (Circle.exp (z.im * x) : ℂ))
    rw [hzexp]
    ring

/-- For a fixed character and spectral parameter, Haar Mellin evaluation is
continuous in the actual inductive topology of the decay space. -/
theorem continuous_decayMellinEvaluation (χ : PontryaginDual G) (z : ℂ) (hz : z.re ∈ I) :
    Continuous (decayMellinEvaluation μ m χ z hz) := by
  let k := (χ * decayMellinPhase m z.im)⁻¹
  let A := modulatedDecayTwistCLM m I ⟨z.re, hz⟩
  exact ((bruhatFourier_evaluation_continuous μ k).comp A.continuous).congr
    (fun f => (decayMellinEvaluation_eq_lcaFourier m μ χ z hz f).symm)

end
end Masullo
