import HilbertSchmidtKernels
import CompactSingularExpansion
import SchattenConvergence

open InnerProductSpace
open scoped ENNReal InnerProductSpace

namespace Masullo

noncomputable section

universe u v

variable {E F : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace E] [CompleteSpace F]
  {ι : Type v}

private theorem ofReal_tsum_ne_top_iff {I : Type*} {f : I → ℝ} (hf : ∀ i, 0 ≤ f i) :
    (∑' i, ENNReal.ofReal (f i)) ≠ ⊤ ↔ Summable f := by
  refine ⟨fun h => ?_, Summable.tsum_ofReal_ne_top⟩
  have h' := ENNReal.summable_toNNReal_of_tsum_ne_top h
  rw [← NNReal.summable_coe] at h'
  simpa only [Function.comp_apply, ← ENNReal.ofNNReal_toNNReal, ENNReal.toNNReal_coe, Real.coe_toNNReal _ (hf _)] using h'

/-- For a compact operator, the extended squared basis energy is the sum of
the squares of the approximation numbers. Inspired by original a6e9e5c. -/
theorem hilbertSchmidt_basisEnergy (b : HilbertBasis ι ℂ E)
    (T : E →L[ℂ] F) (hT : IsCompactOperator T) :
    (∑' i, ‖T (b i)‖ₑ ^ (2 : ℝ)) =
      ∑' n, ENNReal.ofReal (approximationNumber n T ^ 2) := by
  obtain ⟨c, e, f, h⟩ := (isCompactOperator_iff_singularExpansion T).mp hT
  simp_rw [h.approximationNumber_eq, h.image_energy]
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro n
  rw [ENNReal.tsum_mul_left, tsum_enorm_basis_inner_sq]
  by_cases hn : 0 < c n
  · have hu : ‖e n‖ = 1 := h.sourceOrthonormal.norm_eq_one ⟨n, hn⟩
    rw [← ofReal_norm, hu, ENNReal.ofReal_one, ENNReal.one_rpow, mul_one]
  · have hz := le_antisymm (le_of_not_gt hn) (h.nonnegative n)
    simp [hz]

/-- The Schatten-two criterion is equivalent to square summability on any
Hilbert basis. The basis condition itself implies compactness. -/
theorem isSchatten_two_iff_summable_basis (b : HilbertBasis ι ℂ E) (T : E →L[ℂ] F) :
    IsSchatten 2 T ↔ Summable (fun i => ‖T (b i)‖ ^ 2) := by
  have hEnergy :
      (∑' i, ‖T (b i)‖ₑ ^ (2 : ℝ)) ≠ ⊤ ↔ Summable (fun i => ‖T (b i)‖ ^ 2) := by
    simpa only [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, ENNReal.rpow_two] using
      (ofReal_tsum_ne_top_iff (f := fun i => ‖T (b i)‖ ^ 2) (fun _ => sq_nonneg _))
  have hSchatten (hT : IsCompactOperator T) :
      Summable (fun n => approximationNumber n T ^ (2 : ℝ)) ↔
        Summable (fun i => ‖T (b i)‖ ^ 2) := by
    rw [← hEnergy, hilbertSchmidt_basisEnergy b T hT]
    simpa only [Real.rpow_two] using
      (ofReal_tsum_ne_top_iff (f := fun n => approximationNumber n T ^ 2)
        (fun _ => sq_nonneg _)).symm
  exact ⟨fun h => (hSchatten h.1).mp h.2, fun h => by
    have hT := isCompactOperator_of_basisEnergy b T (hEnergy.mpr h)
    exact ⟨hT, (hSchatten hT).mpr h⟩⟩

/-- The Schatten-two norm is the square root of the basis energy. -/
theorem schattenNorm_two_eq_basisEnergy (b : HilbertBasis ι ℂ E) {T : E →L[ℂ] F}
    (hT : IsSchatten 2 T) : schattenNorm 2 T = Real.sqrt (∑' i, ‖T (b i)‖ ^ 2) := by
  have hbasis := (isSchatten_two_iff_summable_basis b T).mp hT
  have happrox : Summable (fun n => approximationNumber n T ^ 2) := by
    simpa only [Real.rpow_two] using hT.2
  have h := hilbertSchmidt_basisEnergy b T hT.1
  simp only [ENNReal.rpow_two, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)] at h
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) hbasis,
    ← ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) happrox] at h
  have heq := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_ofReal (tsum_nonneg (fun _ => sq_nonneg _)),
    ENNReal.toReal_ofReal (tsum_nonneg (fun _ => sq_nonneg _))] at heq
  rw [schattenNorm, show ((2 : ℝ)⁻¹) = 1 / 2 by ring, ← Real.sqrt_eq_rpow]
  simp only [Real.rpow_two, heq]

end
end Masullo
