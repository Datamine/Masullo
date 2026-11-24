import FinestLocallyConvex
import WeakDualNuclear

open Function Module Set Topology
open scoped TensorProduct

namespace Masullo

noncomputable section

variable {I E F : Type*}
variable [AddCommGroup E] [Module ℂ E]
variable [AddCommGroup F] [Module ℂ F]

private def coordinateContraction (c : E →ₗ[ℂ] ℂ) : (E ⊗[ℂ] F) →ₗ[ℂ] F :=
  (TensorProduct.lid ℂ F).toLinearMap.comp (TensorProduct.map c LinearMap.id)

@[simp] private theorem coordinateContraction_tmul (c : E →ₗ[ℂ] ℂ) (x : E) (y : F) :
    coordinateContraction c (x ⊗ₜ[ℂ] y) = c x • y := by
  simp [coordinateContraction]

private theorem tensor_basis_expansion (b : Basis I ℂ E) (z : E ⊗[ℂ] F) :
    ∃ s : Finset I, ∀ t : Finset I, s ⊆ t →
      z = ∑ i ∈ t, b i ⊗ₜ[ℂ] coordinateContraction (b.coord i) z := by
  classical
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨∅, fun t _ => by simp⟩
  | tmul x y =>
    refine ⟨(b.repr x).support, fun t ht => ?_⟩
    simp only [coordinateContraction_tmul, ← TensorProduct.smul_tmul, ← TensorProduct.sum_tmul]
    have hsum : ∑ i ∈ t, (b.coord i x) • b i = x := by
      calc
        _ = ∑ i ∈ (b.repr x).support, (b.coord i x) • b i := by
          symm
          exact Finset.sum_subset ht fun i _ hi => by
            rw [b.coord_apply, Finsupp.notMem_support_iff.mp hi, zero_smul]
        _ = _ := b.linearCombination_repr x
    rw [hsum]
  | add x y hx hy =>
    obtain ⟨s, hs⟩ := hx
    obtain ⟨r, hr⟩ := hy
    refine ⟨s ∪ r, fun t ht => ?_⟩
    simp only [map_add, TensorProduct.tmul_add, Finset.sum_add_distrib]
    exact congrArg₂ (· + ·) (hs t (Finset.subset_union_left.trans ht))
      (hr t (Finset.subset_union_right.trans ht))

variable [TopologicalSpace F] [PolynormableSpace ℂ F]

/-- A countable basis allows each projective test to be bounded by a
single injective test, with an absolutely summable geometric bound. -/
theorem finest_projective_domination (b : Basis I ℂ E) (j : I ↪ ℕ) :
    letI : TopologicalSpace E := finestLocallyConvexTopology E
    ∀ P : ProjectiveTensorTest E F,
      ∃ A : InjectiveDualTest E × InjectiveDualTest F,
        ∀ z, P.tensor z ≤ 2 * injectiveTensorSeminorm A z := by
  classical
  letI : TopologicalSpace E := finestLocallyConvexTopology E
  let W := finest_withSeminorms E
  letI : IsTopologicalAddGroup E := W.topologicalAddGroup
  letI : ContinuousSMul ℂ E := W.continuousSMul
  letI : PolynormableSpace ℂ E := W.toPolynormableSpace
  let WF := PolynormableSpace.withSeminorms ℂ F
  letI : IsTopologicalAddGroup F := WF.topologicalAddGroup
  letI : ContinuousSMul ℂ F := WF.continuousSMul
  intro P
  let d (i : I) : ℝ := (1 / 2 : ℝ) ^ j i
  have hd (i : I) : 0 < d i := by dsimp [d]; positivity
  let w (i : I) : ℂ := ↑((P.first (b i) + 1) / d i)

  let p := (weightedLoneSeminorm w).comp b.repr.toLinearMap
  let A := (seminormPolarTest p (W.continuous_seminorm p),
    seminormPolarTest P.second P.second_continuous)
  letI : CompactSpace A.1.forms := isCompact_iff_compactSpace.mp A.1.compact
  letI : CompactSpace A.2.forms := isCompact_iff_compactSpace.mp A.2.compact
  let c (i : I) : E →L[ℂ] ℂ := ⟨w i • b.coord i, finest_linear_continuous _⟩
  have hc (i : I) : (c i : E →Lₚₜ[ℂ] ℂ) ∈ A.1.forms := by
    intro x
    change ‖weightedLone w (b.repr x) i‖ ≤ ‖weightedLone w (b.repr x)‖
    exact lp.norm_apply_le_norm (by simp) _ _
  refine ⟨A, fun z => ?_⟩
  obtain ⟨s, hs⟩ := tensor_basis_expansion b z
  let M := injectiveTensorSeminorm A z
  have hM : 0 ≤ M := apply_nonneg _ _
  have hcoord (i : I) : ‖w i‖ * P.second (coordinateContraction (b.coord i) z) ≤ M := by
    let y := coordinateContraction (b.coord i) z
    obtain ⟨ψ, hψ, hdom⟩ := seminorm_support P.second P.second_continuous y
    let t : A.1.forms × A.2.forms := (⟨c i, hc i⟩, ⟨ψ, hdom⟩)
    have he : tensorPairEvaluation A.1.forms A.2.forms z t = w i * ψ y := by
      dsimp only [y]
      clear hψ hM hs
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul x f =>
        simp only [tensorPairEvaluation_tmul, coordinateContraction_tmul, map_smul, smul_eq_mul]
        rw [show t.1.val x = w i * b.coord i x from rfl, show t.2.val f = ψ f from rfl]
        ring
      | add x y hx hy => simp [map_add, hx, hy, mul_add]
    have hle := (tensorPairEvaluation A.1.forms A.2.forms z).norm_coe_le_norm t
    change ‖tensorPairEvaluation A.1.forms A.2.forms z t‖ ≤ M at hle
    rwa [he, norm_mul, hψ] at hle
  have hterm (i : I) :
      P.tensor (b i ⊗ₜ[ℂ] coordinateContraction (b.coord i) z) ≤ d i * M := by
    have hwd : d i * ‖w i‖ = P.first (b i) + 1 := by
      have hp : 0 ≤ (P.first (b i) + 1) / d i :=
        div_nonneg (by have := apply_nonneg P.first (b i); linarith) (hd i).le
      change d i * ‖((↑((P.first (b i) + 1) / d i) : ℂ))‖ = _
      rw [Complex.norm_real, Real.norm_of_nonneg hp]
      field_simp [(hd i).ne']
    refine (P.bound _ _).trans ?_
    calc
      _ ≤ (P.first (b i) + 1) * P.second (coordinateContraction (b.coord i) z) :=
        mul_le_mul_of_nonneg_right (by linarith) (apply_nonneg _ _)
      _ = d i * (‖w i‖ * P.second (coordinateContraction (b.coord i) z)) := by rw [← mul_assoc, hwd]
      _ ≤ d i * M := mul_le_mul_of_nonneg_left (hcoord i) (hd i).le
  have hsum (t : Finset I) :
      P.tensor (∑ i ∈ t, b i ⊗ₜ[ℂ] coordinateContraction (b.coord i) z) ≤
        ∑ i ∈ t, d i * M := by
    induction t using Finset.induction_on with
    | empty => simp
    | insert i t hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      exact (map_add_le_add P.tensor _ _).trans (add_le_add (hterm i) ih)
  have hgeo : (∑ i ∈ s, d i) ≤ 2 := by
    have hs' : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ n) :=
      summable_geometric_of_lt_one (by norm_num) (by norm_num)
    rw [show (∑ i ∈ s, d i) = ∑ n ∈ s.map j, (1 / 2 : ℝ) ^ n by simp [d]]
    calc
      _ ≤ ∑' n : ℕ, (1 / 2 : ℝ) ^ n := hs'.sum_le_tsum _ (fun n _ => by positivity)
      _ = 2 := by rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]; norm_num
  calc
    P.tensor z = P.tensor (∑ i ∈ s, b i ⊗ₜ[ℂ] coordinateContraction (b.coord i) z) :=
      congrArg P.tensor (hs s Subset.rfl)
    _ ≤ ∑ i ∈ s, d i * M := hsum s
    _ = (∑ i ∈ s, d i) * M := (Finset.sum_mul _ _ _).symm
    _ ≤ 2 * M := mul_le_mul_of_nonneg_right hgeo hM

theorem finest_tensorTopologies_equal (b : Basis I ℂ E) (j : I ↪ ℕ) :
    letI : TopologicalSpace E := finestLocallyConvexTopology E
    projectiveTensorTopology E F = injectiveTensorTopology E F := by
  letI : TopologicalSpace E := finestLocallyConvexTopology E
  letI : PolynormableSpace ℂ E := (finest_withSeminorms E).toPolynormableSpace
  exact tensorTopologies_equal_of_domination fun P =>
    let ⟨A, hA⟩ := finest_projective_domination b j P
    ⟨A, 2, by norm_num, hA⟩

end
end Masullo
