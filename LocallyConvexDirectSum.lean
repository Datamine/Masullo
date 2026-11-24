import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Data.DFinsupp.Module

open Filter Function Set
open scoped NNReal Pointwise Topology

namespace Masullo

noncomputable section

variable {E : ℕ → Type*} [∀ n, NormedAddCommGroup (E n)] [∀ n, NormedSpace ℂ (E n)]

local instance (n : ℕ) (x : E n) : Decidable (x ≠ 0) := Classical.propDecidable _

abbrev NormedSum (E : ℕ → Type*) [∀ n, Zero (E n)] := Π₀ n, E n

private def weightedSum (w : ℕ → ℝ≥0) (x : NormedSum E) : ℝ := by
  classical
  exact ∑ i ∈ x.support, (w i : ℝ) * ‖x i‖

omit [∀ n, NormedSpace ℂ (E n)] in
private theorem weightedSum_sum_of_support_subset (w : ℕ → ℝ≥0) (x : NormedSum E)
    (I : Finset ℕ) (hI : x.support ⊆ I) :
    weightedSum w x = ∑ i ∈ I, (w i : ℝ) * ‖x i‖ := by
  classical
  unfold weightedSum
  exact Finset.sum_subset hI fun i _ h => by
    have hx := DFinsupp.notMem_support_iff.mp h
    simp [hx]

/-- Weighted sums of the coordinate norms are the continuous seminorms
used to present the locally convex direct sum. -/
def directSumWeight (w : ℕ → ℝ≥0) : Seminorm ℂ (NormedSum E) := by
  classical
  refine Seminorm.of (weightedSum w) (fun x y => ?_) (fun a x => ?_)
  · let I := x.support ∪ y.support
    rw [weightedSum_sum_of_support_subset w (x + y) I DFinsupp.support_add,
      weightedSum_sum_of_support_subset w x I Finset.subset_union_left,
      weightedSum_sum_of_support_subset w y I Finset.subset_union_right, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun i _ => by
      rw [DFinsupp.add_apply, ← mul_add]
      exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (w i).coe_nonneg
  · rw [weightedSum_sum_of_support_subset w (a • x) x.support (DFinsupp.support_smul a x),
      weightedSum_sum_of_support_subset w x x.support (Finset.Subset.refl _),
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [DFinsupp.smul_apply, norm_smul]
    ring

theorem directSumWeight_apply (w : ℕ → ℝ≥0) (x : NormedSum E) :
    directSumWeight w x = weightedSum w x := rfl

instance directSumTopology (E : ℕ → Type*) [∀ n, NormedAddCommGroup (E n)]
    [∀ n, NormedSpace ℂ (E n)] : TopologicalSpace (NormedSum E) :=
  (SeminormFamily.moduleFilterBasis (directSumWeight (E := E))).topology

theorem directSum_withSeminorms :
    WithSeminorms (directSumWeight (E := E)) := ⟨rfl⟩

instance (E : ℕ → Type*) [∀ n, NormedAddCommGroup (E n)] [∀ n, NormedSpace ℂ (E n)] :
    IsTopologicalAddGroup (NormedSum E) := directSum_withSeminorms.topologicalAddGroup

instance (E : ℕ → Type*) [∀ n, NormedAddCommGroup (E n)] [∀ n, NormedSpace ℂ (E n)] :
    ContinuousSMul ℂ (NormedSum E) := directSum_withSeminorms.continuousSMul

instance (E : ℕ → Type*) [∀ n, NormedAddCommGroup (E n)] [∀ n, NormedSpace ℂ (E n)] :
    PolynormableSpace ℂ (NormedSum E) := directSum_withSeminorms.toPolynormableSpace

theorem directSumWeight_mono {w v : ℕ → ℝ≥0} (h : ∀ i, w i ≤ v i) :
    directSumWeight (E := E) w ≤ directSumWeight v := by
  classical
  intro x
  change weightedSum w x ≤ weightedSum v x
  unfold weightedSum
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (h i) (norm_nonneg _)

theorem directSumWeight_smul_weight (c : ℝ≥0) (w : ℕ → ℝ≥0) (x : NormedSum E) :
    directSumWeight (fun i => c * w i) x = (c : ℝ) * directSumWeight w x := by
  classical
  change weightedSum _ x = _ * weightedSum w x
  simp only [weightedSum, NNReal.coe_mul, Finset.mul_sum, mul_assoc]

theorem directSumWeight_single (w : ℕ → ℝ≥0) (n : ℕ) (x : E n) :
    directSumWeight w (DFinsupp.single n x) = (w n : ℝ) * ‖x‖ := by
  classical
  change weightedSum w (DFinsupp.single n x) = _
  rw [weightedSum_sum_of_support_subset _ _ {n} DFinsupp.support_single_subset,
    Finset.sum_singleton, DFinsupp.single_eq_same]

theorem directSum_single_continuous (n : ℕ) :
    Continuous (DFinsupp.lsingle n : E n →ₗ[ℂ] NormedSum E) := by
  apply WithSeminorms.continuous_normedSpace_dom (E n) directSum_withSeminorms
  intro w
  refine ⟨w n, fun x => ?_⟩
  change directSumWeight w (DFinsupp.single n x) ≤ (w n : ℝ) * ‖x‖
  rw [directSumWeight_single]

theorem directSum_coordinate_continuous (n : ℕ) :
    Continuous (DFinsupp.lapply n : NormedSum E →ₗ[ℂ] E n) := by
  classical
  let w : ℕ → ℝ≥0 := fun _ => 1
  apply WithSeminorms.continuous_normedSpace_rng (E n) directSum_withSeminorms
  refine ⟨{w}, 1, fun x => ?_⟩
  simp only [Finset.sup_singleton, one_smul]
  change ‖x n‖ ≤ weightedSum w x
  by_cases h : n ∈ x.support
  · unfold weightedSum
    simpa only [w, NNReal.coe_one, one_mul] using
      Finset.single_le_sum (f := fun i => ‖x i‖) (fun i _ => norm_nonneg (x i)) h
  · rw [DFinsupp.notMem_support_iff.mp h, norm_zero]
    exact apply_nonneg (directSumWeight w) x

instance (E : ℕ → Type*) [∀ n, NormedAddCommGroup (E n)] [∀ n, NormedSpace ℂ (E n)] :
    T2Space (NormedSum E) :=
  T2Space.of_injective_continuous (f := fun x i => x i)
    (fun _ _ h => DFinsupp.ext (congrFun h))
    (continuous_pi directSum_coordinate_continuous)


private theorem directSum_seminorm_dominated (q : Seminorm ℂ (NormedSum E))
    (hq : ∀ n, Continuous (q.comp (DFinsupp.lsingle n))) :
    ∃ w, q ≤ directSumWeight w := by
  classical
  have h (n : ℕ) : ∃ C : ℝ≥0, ∀ x : E n, q (DFinsupp.single n x) ≤ (C : ℝ) * ‖x‖ := by
    obtain ⟨s, C, _, hs⟩ := Seminorm.bound_of_continuous (norm_withSeminorms ℂ (E n))
      (q.comp (DFinsupp.lsingle n)) (hq n)
    refine ⟨C, fun x => (hs x).trans ?_⟩
    have hsup : s.sup (fun _ => normSeminorm ℂ (E n)) ≤ normSeminorm ℂ (E n) :=
      Finset.sup_le fun _ _ => le_rfl
    exact mul_le_mul_of_nonneg_left (hsup x) C.coe_nonneg
  choose w hw using h
  refine ⟨w, fun x => ?_⟩
  change q x ≤ weightedSum w x
  have hx : ∑ i ∈ x.support, DFinsupp.single i (x i) = x := DFinsupp.sum_single
  have hsum (s : Finset ℕ) : q (∑ i ∈ s, DFinsupp.single i (x i)) ≤
      ∑ i ∈ s, (w i : ℝ) * ‖x i‖ := by
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact (map_add_le_add q _ _).trans (add_le_add (hw a _) ih)
  calc
    q x = q (∑ i ∈ x.support, DFinsupp.single i (x i)) := congrArg q hx.symm
    _ ≤ _ := hsum x.support

/-- The weighted-seminorm construction is the locally convex direct sum.
A linear map out of it is continuous exactly when each coordinate
inclusion followed by the map is continuous. -/
theorem directSum_continuous_iff {F : Type*} [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
    [PolynormableSpace ℂ F] (L : NormedSum E →ₗ[ℂ] F) :
    Continuous L ↔ ∀ n, Continuous (L.comp (DFinsupp.lsingle n)) := by
  constructor
  · intro h n
    exact h.comp (directSum_single_continuous n)
  · intro h
    apply WithSeminorms.continuous_of_continuous_comp (PolynormableSpace.withSeminorms ℂ F)
    intro q
    obtain ⟨w, hw⟩ := directSum_seminorm_dominated (q.val.comp L)
      (fun n => q.property.comp (h n))
    exact Seminorm.continuous_of_le (directSum_withSeminorms.continuous_seminorm w) hw


theorem normedSum_nhds_contains_weight_ball {V : Set (NormedSum E)} (hV : V ∈ 𝓝 0) :
    ∃ w : ℕ → ℝ≥0, (directSumWeight w).ball 0 1 ⊆ V := by
  classical
  obtain ⟨⟨I, ε⟩, hε, hI⟩ :=
    (directSum_withSeminorms (E := E)).hasBasis_zero_ball.mem_iff.mp hV
  let c : ℝ≥0 := ⟨ε⁻¹, inv_nonneg.mpr hε.le⟩
  let w (n : ℕ) := I.sup fun v => v n
  have hc : I.sup (directSumWeight (E := E)) ≤ directSumWeight w :=
    Finset.sup_le fun v hv => directSumWeight_mono (fun n => Finset.le_sup (f := fun v => v n) hv)
  refine ⟨fun i => c * w i, fun x hx => hI ?_⟩
  rw [Seminorm.mem_ball_zero] at hx ⊢
  rw [directSumWeight_smul_weight] at hx
  change ε⁻¹ * directSumWeight w x < 1 at hx
  have h := (inv_mul_lt_iff₀ hε).mp hx
  exact (hc x).trans_lt (by simpa using h)

/-- Proposition C.1.5.1 for the locally convex direct sum of normed spaces.
A diagonal choice of positive real dilations leaves a common zero neighborhood. -/
theorem countable_directSum_neighborhood_dilations (V : ℕ → Set (NormedSum E))
    (hV : ∀ n, V n ∈ 𝓝 0) :
    ∃ ρ : ℕ → ℝ, (∀ n, 0 < ρ n) ∧ (⋂ n, ((ρ n : ℂ) • V n)) ∈ 𝓝 (0 : NormedSum E) := by
  classical
  choose w hw using fun n => normedSum_nhds_contains_weight_ball (hV n)
  let r (n : ℕ) : ℝ≥0 := 1 + (Finset.range (n + 1)).sup (w n)
  have hr (n : ℕ) : 0 < r n := by dsimp [r]; positivity
  let b (k : ℕ) : ℝ≥0 := 1 + ∑ n ∈ Finset.range k, w n k / r n
  have hb (n k : ℕ) : w n k / r n ≤ b k := by
    by_cases hk : k ≤ n
    · have hh : w n k ≤ r n := (Finset.le_sup
        (f := w n) (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))).trans (le_add_of_nonneg_left zero_le_one)
      exact ((div_le_iff₀ (hr n)).mpr (by simpa using hh)).trans
        (le_add_of_nonneg_right (by positivity))
    · have hnk := Nat.lt_of_not_ge hk
      have hh := Finset.single_le_sum (f := fun i => w i k / r i)
        (fun _ _ => by positivity) (Finset.mem_range.mpr hnk)
      exact hh.trans (le_add_of_nonneg_left zero_le_one)
  refine ⟨fun n => (r n : ℝ), fun n => by exact_mod_cast hr n, mem_of_superset (x := (directSumWeight (E := E) b).ball 0 1) ?_ ?_⟩
  · simpa only [Finset.sup_singleton] using (directSum_withSeminorms (E := E)).hasBasis_zero_ball.mem_of_mem
      (i := ({b}, 1)) zero_lt_one
  · intro x hx
    apply mem_iInter.mpr
    intro n
    let c : ℂ := ↑(r n : ℝ)
    have hreal : 0 < (r n : ℝ) := by exact_mod_cast hr n
    have hc : c ≠ 0 := Complex.ofReal_ne_zero.mpr hreal.ne'
    let y := c⁻¹ • x
    have hy : y ∈ (directSumWeight (w n)).ball 0 1 := by
      rw [Seminorm.mem_ball_zero] at hx ⊢
      have hweight : directSumWeight (fun k => (r n)⁻¹ * w n k) x =
          directSumWeight (w n) y := by
        rw [directSumWeight_smul_weight]
        change _ = directSumWeight (w n) (c⁻¹ • x)
        rw [map_smul_eq_mul]
        simp [c, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hreal]
      rw [← hweight]
      exact (directSumWeight_mono (fun k => by simpa [div_eq_mul_inv, mul_comm] using hb n k) x).trans_lt hx
    exact ⟨y, hw n hy, by change c • (c⁻¹ • x) = x; rw [smul_smul, mul_inv_cancel₀ hc, one_smul]⟩

end

end Masullo
