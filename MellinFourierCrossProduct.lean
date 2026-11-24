import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Complex.Basic

open Filter Function MeasureTheory Set

namespace Masullo

noncomputable section

variable {G : Type*} [CommGroup G] [MeasurableSpace G] [MeasurableMul₂ G]
  [MeasurableInv G] (μ : Measure G) [SFinite μ] [μ.IsMulLeftInvariant]

/-- The multiplicative shear separates the two spectral weights in a
weighted correlation. This is the Fubini step in Tate's local equation. -/
theorem mellin_weighted_correlation
    (χ : G →* ℂˣ) (a b : G → ℂ)
    (ha : Integrable (fun x ↦ ((χ x : ℂ)⁻¹) * a x) μ)
    (hb : Integrable (fun x ↦ (χ x : ℂ) * b x) μ) :
    (∫ y, (χ y : ℂ) * (∫ x, a x * b (y * x) ∂μ) ∂μ) =
      (∫ x, ((χ x : ℂ)⁻¹) * a x ∂μ) * (∫ x, (χ x : ℂ) * b x ∂μ) := by
  let A (x : G) : ℂ := (χ x : ℂ)⁻¹ * a x
  let B (x : G) : ℂ := (χ x : ℂ) * b x
  let F (z : G × G) : ℂ := A z.1 * B z.2
  let H (z : G × G) : ℂ := (χ z.2 : ℂ) * (a z.1 * b (z.2 * z.1))
  let e : G × G ≃ᵐ G × G := MeasurableEquiv.shearMulRight G
  have he : MeasurePreserving e (μ.prod μ) (μ.prod μ) :=
    measurePreserving_prod_mul μ μ
  have hFH : F ∘ e = H := by
    funext z
    change ((χ z.1 : ℂ)⁻¹ * a z.1) * ((χ (z.1 * z.2) : ℂ) * b (z.1 * z.2)) = _
    rw [map_mul, Units.val_mul]
    have hx : (χ z.1 : ℂ) ≠ 0 := (χ z.1).ne_zero
    calc
      _ = ((χ z.1 : ℂ)⁻¹ * (χ z.1 : ℂ)) *
          ((χ z.2 : ℂ) * (a z.1 * b (z.1 * z.2))) := by ring
      _ = _ := by rw [inv_mul_cancel₀ hx, one_mul, mul_comm z.1 z.2]
  have hF : Integrable F (μ.prod μ) := ha.mul_prod hb
  have hH : Integrable H (μ.prod μ) := hFH ▸ (he.integrable_comp_emb e.measurableEmbedding).mpr hF
  calc
    _ = ∫ y, ∫ x, H (x,y) ∂μ ∂μ := by
      congr 1
      funext y
      simp only [H, integral_const_mul]
    _ = ∫ z, H z ∂μ.prod μ := (integral_prod_symm H hH).symm
    _ = ∫ z, F z ∂μ.prod μ := by
      rw [← hFH]
      exact he.integral_comp e.measurableEmbedding F
    _ = _ := integral_prod_mul A B

/-- Symmetry of the additive Fourier pairing gives a cross-product identity
for opposite multiplicative weights. The density is included in the
untransformed tests. -/
theorem mellin_fourier_crossProduct
    (χ : G →* ℂˣ) (f g φ ψ : G → ℂ)
    (hf : Integrable (fun x ↦ ((χ x : ℂ)⁻¹) * f x) μ)
    (hg : Integrable (fun x ↦ ((χ x : ℂ)⁻¹) * g x) μ)
    (hφ : Integrable (fun x ↦ (χ x : ℂ) * φ x) μ)
    (hψ : Integrable (fun x ↦ (χ x : ℂ) * ψ x) μ)
    (hPair : ∀ y : G, (∫ x, f x * ψ (y*x) ∂μ) = ∫ x, g x * φ (y*x) ∂μ) :
    (∫ x, ((χ x : ℂ)⁻¹) * f x ∂μ) * (∫ x, (χ x : ℂ) * ψ x ∂μ) =
      (∫ x, ((χ x : ℂ)⁻¹) * g x ∂μ) * (∫ x, (χ x : ℂ) * φ x ∂μ) := by
  rw [← mellin_weighted_correlation μ χ f ψ hf hψ,
    ← mellin_weighted_correlation μ χ g φ hg hφ]
  simp_rw [hPair]

end

end Masullo
