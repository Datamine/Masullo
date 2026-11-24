import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.l2Space
import AbsolutelySummingFactorization
import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# Nuclear series for a composite of three absolutely summing operators

Adapted from the Apache-2.0 original formalization at
`23cbb63d9a34c2ae8ab0ebd86074ea4c2a056978`, in
`RiemannMasullo/ForMathlib/Analysis/Normed/Operator/AbsolutelySumming/Composition.lean`.
-/

noncomputable section
open Set Filter Topology

namespace Masullo
namespace AbsolutelySumming
universe w

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
  [NormedAddCommGroup Y] [NormedSpace ℂ Y]
variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Precomposing a 2-summing map with a Hilbert-space operator sends Hilbert bases
to square-summable families. -/
private theorem summable_basis {ι : Type*} (b : HilbertBasis ι ℂ H)
    (T : X →L[ℂ] Y) (d : H →L[ℂ] X) {C : ℝ}
    (h : HasQuadraticBound T C) : Summable (fun i ↦ ‖T (d (b i))‖ ^ 2) := by
  classical
  apply summable_of_sum_le (c := C * ‖d‖ ^ 2) (fun i ↦ sq_nonneg _)
  intro s
  let e := Fintype.equivFin ↥s
  have hweak (φ : StrongDual ℂ X) (hφ : ‖φ‖ ≤ 1) :
      ∑ i ∈ s, ‖φ (d (b i))‖ ^ 2 ≤ ‖d‖ ^ 2 := by
    let y := (InnerProductSpace.toDual ℂ H).symm (φ.comp d)
    have hy : ‖y‖ ≤ ‖d‖ := ((InnerProductSpace.toDual ℂ H).symm.norm_map _).trans_le
      ((φ.opNorm_comp_le d).trans (mul_le_of_le_one_left (norm_nonneg _) hφ))
    have heq (i : ι) : ‖φ (d (b i))‖ = ‖inner ℂ (b i) y‖ := by
      change ‖(φ.comp d) (b i)‖ = _
      rw [← InnerProductSpace.toDual_symm_apply, norm_inner_symm]
    simp only [heq]
    exact (b.orthonormal.sum_inner_products_le y).trans ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hy)
  have hf (f : ι → ℝ) : ∑ i, f (e.symm i) = ∑ i ∈ s, f i :=
    (e.symm.sum_comp (fun i : s ↦ f i)).trans (Finset.sum_subtype s (fun _ ↦ Iff.rfl) f).symm
  have h' := h _ (fun i ↦ d (b (e.symm i))) _ (sq_nonneg ‖d‖)
    (fun φ hφ ↦ (hf (fun i ↦ ‖φ (d (b i))‖ ^ 2)).trans_le (hweak φ hφ))
  rwa [hf (fun i ↦ ‖T (d (b i))‖ ^ 2)] at h'

/-- Parseval and Bessel transfer the square-summability bound to the adjoint. -/
private theorem summable_adjoint_basis {ι κ : Type*} (b : HilbertBasis ι ℂ H)
    (c : HilbertBasis κ ℂ K) (T : H →L[ℂ] K) (h : Summable (fun j ↦ ‖T (b j)‖ ^ 2)) :
    Summable (fun i ↦ ‖T.adjoint (c i)‖ ^ 2) := by
  classical
  let a (i : κ) (j : ι) := ‖inner ℂ (b j) (T.adjoint (c i))‖ ^ 2
  have row (i : κ) : HasSum (a i) (‖T.adjoint (c i)‖ ^ 2) := by
    have h := lp.hasSum_norm (p := 2) (by norm_num) (b.repr (T.adjoint (c i)))
    simpa [a, b.repr_apply_apply] using h
  apply summable_of_sum_le (c := ∑' j, ‖T (b j)‖ ^ 2) (fun i ↦ sq_nonneg _)
  intro s
  have hs := hasSum_sum (s := s) (fun i _ ↦ row i)
  rw [← hs.tsum_eq]
  apply hs.summable.tsum_le_tsum _ h
  intro j
  simpa only [a, T.adjoint_inner_right, norm_inner_symm (T (b j))] using
    (c.orthonormal.sum_inner_products_le (s := s) (T (b j)))

/-- The composite of three absolutely summing Banach-space maps admits a nuclear
series of rank-one operators with summable norms. -/
theorem exists_rankOne_comp_three {X₂ : Type w} {X₃ : Type*}
    [NormedAddCommGroup X₂] [NormedSpace ℂ X₂] [CompleteSpace X₂]
    [NormedAddCommGroup X₃] [NormedSpace ℂ X₃] [CompleteSpace X] [CompleteSpace Y]
    (T₁ : X →L[ℂ] Y) (T₂ : X₂ →L[ℂ] X) (T₃ : X₃ →L[ℂ] X₂)
    (s₁ : ∃ C, 0 ≤ C ∧ HasBound T₁ C) (s₂ : ∃ C, 0 ≤ C ∧ HasBound T₂ C)
    (s₃ : ∃ C, 0 ≤ C ∧ HasBound T₃ C) :
    ∃ (ι : Type w) (φ : ι → StrongDual ℂ X₃) (y : ι → Y),
      Summable (fun i ↦ ‖φ i‖ * ‖y i‖) ∧
        HasSum (fun i ↦ (φ i).smulRight (y i)) (T₁.comp (T₂.comp T₃)) := by
  obtain ⟨C₁, hC₁, h₁⟩ := s₁
  obtain ⟨C₂, hC₂, h₂⟩ := s₂
  obtain ⟨C₃, hC₃, h₃⟩ := s₃
  obtain ⟨H₂, _, _, _, a₂, d₂, hd₂, ha₂⟩ := factor T₂ hC₂ h₂
  obtain ⟨H₃, _, _, _, a₃, d₃, hd₃, _⟩ := factor T₃ hC₃ h₃
  obtain ⟨ι, b, _⟩ := exists_hilbertBasis (𝕜 := ℂ) (E := H₂)
  obtain ⟨κ, c, _⟩ := exists_hilbertBasis (𝕜 := ℂ) (E := H₃)
  let U := a₂.comp d₃
  let V := T₁.comp d₂
  have hU : Summable (fun j ↦ ‖U (c j)‖ ^ 2) :=
    summable_basis c a₂ d₃ (C := 1) fun n x M _ hx ↦ (ha₂ n x M hx).trans_eq (one_mul M).symm
  have hV : Summable (fun i ↦ ‖V (b i)‖ ^ 2) :=
    summable_basis b T₁ d₂ (C := C₁ ^ 2) fun _ x _ ↦ sum_sq_le T₁ hC₁ h₁ x
  let φ (i : ι) := (innerSL ℂ (U.adjoint (b i))).comp a₃
  have hφ (i : ι) : ‖φ i‖ ≤ ‖U.adjoint (b i)‖ * ‖a₃‖ := by
    simpa only [innerSL_apply_norm] using (innerSL ℂ (U.adjoint (b i))).opNorm_comp_le a₃
  let y (i : ι) := V (b i)
  have hn : Summable (fun i ↦ ‖φ i‖ * ‖y i‖) := by
    have hA := summable_adjoint_basis c b U hU
    refine ((hA.add hV).mul_right ‖a₃‖).of_nonneg_of_le (fun i ↦ by positivity) fun i ↦ ?_
    refine (mul_le_mul_of_nonneg_right (hφ i) (norm_nonneg _)).trans ?_
    have hsq := sq_nonneg (‖U.adjoint (b i)‖ - ‖V (b i)‖)
    have hprod := mul_nonneg (norm_nonneg (U.adjoint (b i))) (norm_nonneg (V (b i)))
    calc
      _ = (‖U.adjoint (b i)‖ * ‖V (b i)‖) * ‖a₃‖ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by nlinarith only [hsq, hprod]) (norm_nonneg _)
  refine ⟨ι, φ, y, hn, ?_⟩
  have hop : Summable (fun i ↦ (φ i).smulRight (y i)) :=
    hn.of_norm_bounded fun i ↦ ((φ i).norm_smulRight_apply (y i)).le
  suffices he : (∑' i, (φ i).smulRight (y i)) = T₁.comp (T₂.comp T₃) by
    exact he ▸ hop.hasSum
  ext x
  have hx := (ContinuousLinearMap.apply ℂ Y x).hasSum hop.hasSum
  have hb : HasSum (fun i ↦ φ i x • y i) (T₁ (T₂ (T₃ x))) := by
    have heq : V (U (a₃ x)) = T₁ (T₂ (T₃ x)) := by
      change T₁ (d₂ (a₂ (d₃ (a₃ x)))) = _
      rw [hd₂, hd₃]
    rw [← heq]
    refine (V.hasSum (b.hasSum_repr (U (a₃ x)))).congr_fun fun i ↦ ?_
    rw [map_smul, b.repr_apply_apply]
    change inner ℂ (U.adjoint (b i)) (a₃ x) • _ = _
    rw [U.adjoint_inner_left]
  apply hx.unique
  simpa only [ContinuousLinearMap.apply_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.comp_apply] using hb

end AbsolutelySumming
end Masullo
