import AdelicHaarScaling
import Mathlib.Analysis.Complex.Circle

open Function MeasureTheory NumberField Set Topology
open scoped ENNReal NumberField Pointwise

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]
  [MeasurableSpace (Adeles F)] [BorelSpace (Adeles F)]

/-- The additive Fourier integral with the manuscript's positive
character convention, at a chosen Haar normalization. -/
def adelicFourierIntegral (μ : Measure (Adeles F)) (ψ : Adeles F →+ Additive Circle)
    (f : Adeles F → ℂ) (ξ : Adeles F) : ℂ :=
  ∫ a, f a * ((ψ (a * ξ)).toMul : ℂ) ∂μ

private theorem adelicHaar_map_mul (μ : Measure (Adeles F)) [μ.IsAddHaarMeasure]
    (g : Idele F) :
    μ.map (fun a => g.val * a) = ENNReal.ofReal ((ideleNorm F g)⁻¹) • μ := by
  ext T hT
  have hsm : Measurable (fun a : Adeles F => g.val * a) :=
    (continuous_const.mul continuous_id).measurable
  rw [Measure.map_apply hsm hT, Measure.smul_apply, smul_eq_mul]
  have hpre : (fun a : Adeles F => g.val * a) ⁻¹' T = g⁻¹ • T := by
    ext a
    rw [mem_smul_set_iff_inv_smul_mem, inv_inv]
    rfl
  rw [hpre, adelicHaar_smul F g⁻¹ μ T, map_inv (ideleNorm F) g]

/-- Under multiplication of the argument by an idele, the Fourier
argument is multiplied by its inverse and the integral by the inverse
modulus. This uses the normalized idelic norm for arbitrary additive Haar. -/
theorem adelicFourier_mul_argument (μ : Measure (Adeles F)) [μ.IsAddHaarMeasure]
    (ψ : Adeles F →+ Additive Circle) (hψ : Continuous ψ)
    (f : Adeles F → ℂ) (hf : Measurable f) (g : Idele F) (ξ : Adeles F) :
    adelicFourierIntegral F μ ψ (fun a => f (g.val * a)) ξ =
      (ideleNorm F g)⁻¹ • adelicFourierIntegral F μ ψ f (g.inv * ξ) := by
  let k (a : Adeles F) := f a * ((ψ (a * (g.inv * ξ))).toMul : ℂ)
  have hφ : Continuous (fun a : Adeles F => ((ψ (a * (g.inv * ξ))).toMul : ℂ)) :=
    continuous_subtype_val.comp (continuous_toMul.comp
      (hψ.comp (continuous_id.mul continuous_const)))
  have hk : Measurable k := hf.mul hφ.measurable
  have hg : Measurable (fun a : Adeles F => g.val * a) :=
    (continuous_const.mul continuous_id).measurable
  have he : (∫ a, k (g.val * a) ∂μ) =
      adelicFourierIntegral F μ ψ (fun a => f (g.val * a)) ξ := by
    unfold adelicFourierIntegral
    apply integral_congr_ae
    filter_upwards [] with a
    have h : (g.val * a) * (g.inv * ξ) = a * ξ := by
      calc
        _ = (g.val * g.inv) * (a * ξ) := by ac_rfl
        _ = _ := by rw [g.val_inv, one_mul]
    exact congrArg (fun b : Adeles F => f (g.val * a) * ((ψ b).toMul : ℂ)) h
  rw [← he, ← integral_map hg.aemeasurable hk.aestronglyMeasurable,
    adelicHaar_map_mul F μ g, integral_smul_measure,
    ENNReal.toReal_ofReal (inv_nonneg.mpr (ideleNorm_pos F g).le)]
  rfl

end

end Masullo
