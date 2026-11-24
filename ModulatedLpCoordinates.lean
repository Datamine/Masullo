import ModulatedJumpPoisson
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Integral.Prod

open Function MeasureTheory Set
open scoped ENNReal

namespace Masullo

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G]

/-- In split Haar coordinates the finite Lᵖ norm is the manuscript's
iterated integral. Lebesgue measure on the log coordinate is the radial Haar
normalization, and the second measure is the given norm-one normalization. -/
theorem lpNorm_modulatedLogMeasure
    (m : G →ₜ* Multiplicative ℝ) (τ : Multiplicative ℝ →ₜ* G) (hτ : RightInverse τ m)
    (ν : Measure m.toMonoidHom.ker) [SFinite ν]
    {p : ℝ≥0∞} (hp₀ : p ≠ 0) (hp : p ≠ ⊤)
    {f : G → ℂ} (hf : Continuous f) (hfp : MemLp f p (modulatedLogMeasure m τ hτ ν)) :
    lpNorm f p (modulatedLogMeasure m τ hτ ν) =
      (∫ x : ℝ, ∫ k, ‖f (τ (Multiplicative.ofAdd x) * k.val)‖ ^ p.toReal ∂ν) ^
        (1 / p.toReal) := by
  let e := modulatedLogSplit m τ hτ
  let F (g : G) := ‖f g‖ ^ p.toReal
  have hF : Measurable F := hf.norm.measurable.pow_const _
  have he : Measurable e := e.continuous.measurable
  have hFi : Integrable F (modulatedLogMeasure m τ hτ ν) :=
    (integrable_norm_rpow_iff hf.aestronglyMeasurable hp₀ hp).mpr hfp
  have hprod : Integrable (F ∘ e) (volume.prod ν) :=
    (integrable_map_measure hF.aestronglyMeasurable he.aemeasurable).mp hFi
  rw [lpNorm_eq_integral_norm_rpow_toReal hp₀ hp hf.aestronglyMeasurable, ← one_div]
  change (∫ g, F g ∂Measure.map e (volume.prod ν)) ^ (1 / p.toReal) = _
  rw [integral_map he.aemeasurable hF.aestronglyMeasurable]
  exact congrArg (fun y : ℝ => y ^ (1 / p.toReal)) (integral_prod (F ∘ e) hprod)

private theorem integral_logCoordinates (F : ℝ → ℝ) :
    (∫ x, F x) = ∫ t in Ioi (0 : ℝ), t⁻¹ * F (Real.log t) := by
  have h := integral_image_eq_integral_abs_deriv_smul (s := univ) (f := Real.exp)
    MeasurableSet.univ (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
    Real.exp_injective.injOn (fun t => t⁻¹ * F (Real.log t))
  rw [image_univ, Real.range_exp, Measure.restrict_univ] at h
  rw [h]
  apply integral_congr_ae
  refine ae_of_all _ fun x => ?_
  dsimp only
  rw [abs_of_pos (Real.exp_pos x), smul_eq_mul, Real.log_exp, ← mul_assoc,
    mul_inv_cancel₀ (Real.exp_ne_zero x), one_mul]

/-- The finite norm in a chosen modulus section with the radial integration
written against `dt/t`, as in (D.1.10.17) and (D.1.10.20). -/
theorem lpNorm_modulatedLogMeasure_positiveRadial
    (m : G →ₜ* Multiplicative ℝ) (τ : Multiplicative ℝ →ₜ* G) (hτ : RightInverse τ m)
    (ν : Measure m.toMonoidHom.ker) [SFinite ν]
    {p : ℝ≥0∞} (hp₀ : p ≠ 0) (hp : p ≠ ⊤)
    {f : G → ℂ} (hf : Continuous f) (hfp : MemLp f p (modulatedLogMeasure m τ hτ ν)) :
    lpNorm f p (modulatedLogMeasure m τ hτ ν) =
      (∫ t in Ioi (0 : ℝ), t⁻¹ *
        (∫ k, ‖f (τ (Multiplicative.ofAdd (Real.log t)) * k.val)‖ ^ p.toReal ∂ν)) ^
        (1 / p.toReal) := by
  rw [lpNorm_modulatedLogMeasure m τ hτ ν hp₀ hp hf hfp]
  exact congrArg (fun y : ℝ => y ^ (1 / p.toReal)) (integral_logCoordinates _)

end Masullo
