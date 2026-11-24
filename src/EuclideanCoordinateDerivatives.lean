import IteratedDirectionalDerivatives
import Mathlib.Analysis.InnerProductSpace.PiL2

open scoped BigOperators ContDiff
open Set

namespace Masullo

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- On a Euclidean space the multilinear operator norm and the finite family
of coordinate entries control each other. -/
theorem euclideanMultilinear_norm_bounds {d n : ℕ}
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin n => EuclideanSpace ℝ (Fin d)) V) :
    (∀ j : Fin n → Fin d, ‖T (fun i => EuclideanSpace.basisFun (Fin d) ℝ (j i))‖ ≤ ‖T‖) ∧
      ∀ M : ℝ, 0 ≤ M →
        (∀ j : Fin n → Fin d, ‖T (fun i => EuclideanSpace.basisFun (Fin d) ℝ (j i))‖ ≤ M) →
        ‖T‖ ≤ (d : ℝ) ^ n * M := by
  classical
  let b := EuclideanSpace.basisFun (Fin d) ℝ
  have hb (i : Fin d) : ‖b i‖ = 1 := b.orthonormal.norm_eq_one i
  refine ⟨fun j => ?_, fun M hM hEntry => ?_⟩
  · simpa only [hb, Finset.prod_const_one, mul_one] using T.le_opNorm (fun i => b (j i))
  · apply ContinuousMultilinearMap.opNorm_le_bound (mul_nonneg (by positivity) hM)
    intro v
    have hv (i : Fin n) : (∑ j, (v i) j • b j) = v i := by
      simpa only [b, EuclideanSpace.basisFun_repr] using b.sum_repr (v i)
    calc
      ‖T v‖ = ‖∑ j : Fin n → Fin d,
        (∏ i, (v i) (j i)) • T (fun i => b (j i))‖ := by
        congr 1
        conv_lhs => rw [show v = (fun i => ∑ j, (v i) j • b j) from (funext hv).symm]
        change T.toMultilinearMap _ = _
        rw [T.toMultilinearMap.map_sum]
        exact Finset.sum_congr rfl fun j _ => T.toMultilinearMap.map_smul_univ _ _
      _ ≤ ∑ j : Fin n → Fin d, ‖(∏ i, (v i) (j i)) • T (fun i => b (j i))‖ :=
        norm_sum_le _ _
      _ ≤ ∑ _j : Fin n → Fin d, (∏ i, ‖v i‖) * M := by
        apply Finset.sum_le_sum
        intro j _
        rw [norm_smul, norm_prod]
        exact mul_le_mul
          (Finset.prod_le_prod (fun i _ => norm_nonneg ((v i) (j i)))
            (fun i _ => PiLp.norm_apply_le (v i) (j i)))
          (hEntry j) (norm_nonneg _) (by positivity)
      _ = (d : ℝ) ^ n * M * ∏ i, ‖v i‖ := by
        simp [mul_assoc, mul_left_comm, mul_comm]

/-- An ordered list of repeated coordinate differentiations with index in `Fin d`. -/
noncomputable def euclideanCoordinateDerivative {d : ℕ} :
    (n : ℕ) → (Fin n → Fin d) → (EuclideanSpace ℝ (Fin d) → V) →
      EuclideanSpace ℝ (Fin d) → V
  | 0, _, f => f
  | n + 1, j, f => fun x =>
      fderiv ℝ (euclideanCoordinateDerivative n (Fin.tail j) f) x
        (EuclideanSpace.basisFun (Fin d) ℝ (j 0))

/-- The usual repeated coordinate derivative is an entry of the iterated Fréchet derivative. -/
theorem euclideanCoordinateDerivative_eq {d : ℕ}
    {f : EuclideanSpace ℝ (Fin d) → V} (hf : ContDiff ℝ ∞ f) (n : ℕ)
    (j : Fin n → Fin d) (x : EuclideanSpace ℝ (Fin d)) :
    euclideanCoordinateDerivative n j f x =
      iteratedFDeriv ℝ n f x (fun i => EuclideanSpace.basisFun (Fin d) ℝ (j i)) := by
  induction n generalizing x with
  | zero => exact (iteratedFDeriv_zero_apply _).symm
  | succ n ih =>
    change fderiv ℝ (euclideanCoordinateDerivative n (Fin.tail j) f) x
      (EuclideanSpace.basisFun (Fin d) ℝ (j 0)) = _
    rw [show euclideanCoordinateDerivative n (Fin.tail j) f =
      fun y => iteratedFDeriv ℝ n f y (fun i => EuclideanSpace.basisFun (Fin d) ℝ (j i.succ))
      from funext (ih (Fin.tail j))]
    exact ((hf.differentiable_iteratedFDeriv
      (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top n)) x).iteratedFDeriv_succ_apply_left'
        (m := fun i => EuclideanSpace.basisFun (Fin d) ℝ (j i))).symm

/-- A smooth coordinate derivative depends only on the multiplicity of
each basis direction. In particular the derivatives may be grouped by coordinate. -/
theorem euclideanCoordinateDerivative_eq_of_count {d n : ℕ}
    {f : EuclideanSpace ℝ (Fin d) → V} (hf : ContDiff ℝ ∞ f)
    (j j' : Fin n → Fin d)
    (h : ∀ i : Fin d, (List.ofFn j).count i = (List.ofFn j').count i) :
    euclideanCoordinateDerivative n j f = euclideanCoordinateDerivative n j' f := by
  let b := EuclideanSpace.basisFun (Fin d) ℝ
  have hp := (List.perm_iff_count.mpr h).map b
  rw [List.map_ofFn, List.map_ofFn] at hp
  funext x
  rw [euclideanCoordinateDerivative_eq hf, euclideanCoordinateDerivative_eq hf,
    ← iteratedDirectionalDerivative_ofFn hf, ← iteratedDirectionalDerivative_ofFn hf]
  exact congrFun (iteratedDirectionalDerivative_perm hp hf) x

/-- A norm-power weight is controlled by the constant and pure coordinate monomials. -/
theorem euclidean_normPow_mul_le_of_coordinatePow_bounds {d : ℕ}
    (x : EuclideanSpace ℝ (Fin d)) (k : ℕ) {A M : ℝ} (hA : 0 ≤ A) (hAM : A ≤ M)
    (hcoord : ∀ i, ‖x i‖ ^ k * A ≤ M) : ‖x‖ ^ k * A ≤ ((d : ℝ) + 1) ^ k * M := by
  cases d with
  | zero =>
    have hx : x = 0 := Subsingleton.elim _ _
    rw [hx, norm_zero]
    simpa using (mul_le_mul_of_nonneg_right (zero_pow_le_one (n := k)) hA).trans
      (by simpa only [one_mul] using hAM)
  | succ d =>
    classical
    obtain ⟨i, -, hi⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin (d + 1)))
      (fun i => ‖x i‖) Finset.univ_nonempty
    have hsq : ‖x‖ ^ 2 ≤ ((d + 1 : ℕ) : ℝ) * ‖x i‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      calc
        _ ≤ ∑ _j : Fin (d + 1), ‖x i‖ ^ 2 := Finset.sum_le_sum fun j hj =>
          pow_le_pow_left₀ (norm_nonneg _) (hi j hj) _
        _ = _ := by simp
    have hd : ((d + 1 : ℕ) : ℝ) ≤ (((d + 1 : ℕ) : ℝ) + 1) ^ 2 := by
      nlinarith [sq_nonneg (((d + 1 : ℕ) : ℝ)), Nat.cast_nonneg (α := ℝ) (d + 1)]
    have hn : ‖x‖ ≤ (((d + 1 : ℕ) : ℝ) + 1) * ‖x i‖ := by
      apply le_of_pow_le_pow_left₀ (n := 2) (by decide) (by positivity)
      rw [mul_pow]
      exact hsq.trans (mul_le_mul_of_nonneg_right hd (sq_nonneg _))
    calc
      _ ≤ ((((d + 1 : ℕ) : ℝ) + 1) * ‖x i‖) ^ k * A :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hn _) hA
      _ = (((d + 1 : ℕ) : ℝ) + 1) ^ k * (‖x i‖ ^ k * A) := by rw [mul_pow, mul_assoc]
      _ ≤ _ := mul_le_mul_of_nonneg_left (hcoord i) (by positivity)

/-- A product of coordinate absolute values times one coordinate derivative
is bounded by the corresponding radial weight times the full derivative norm. -/
theorem euclidean_monomial_coordinateDerivative_le {d k n : ℕ}
    {f : EuclideanSpace ℝ (Fin d) → V} (hf : ContDiff ℝ ∞ f)
    (x : EuclideanSpace ℝ (Fin d)) (a : Fin k → Fin d) (j : Fin n → Fin d) :
    (∏ t, ‖x (a t)‖) * ‖euclideanCoordinateDerivative n j f x‖ ≤
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ := by
  rw [euclideanCoordinateDerivative_eq hf]
  apply mul_le_mul
  · calc
      _ ≤ ∏ _ : Fin k, ‖x‖ :=
        Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun t _ => PiLp.norm_apply_le x (a t))
      _ = _ := by simp
  · exact (euclideanMultilinear_norm_bounds (iteratedFDeriv ℝ n f x)).1 j
  · exact norm_nonneg _
  · positivity

/-- The constant and pure coordinate monomials, tested on the finitely many
order-`n` coordinate derivatives, also control the radial Schwartz bound. -/
theorem euclidean_weighted_iteratedFDeriv_le_of_coordinate_bounds {d k n : ℕ}
    {f : EuclideanSpace ℝ (Fin d) → V} (hf : ContDiff ℝ ∞ f)
    (x : EuclideanSpace ℝ (Fin d)) {M : ℝ} (hM : 0 ≤ M)
    (hconst : ∀ j : Fin n → Fin d, ‖euclideanCoordinateDerivative n j f x‖ ≤ M)
    (hpow : ∀ (i : Fin d) (j : Fin n → Fin d),
      ‖x i‖ ^ k * ‖euclideanCoordinateDerivative n j f x‖ ≤ M) :
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ (d : ℝ) ^ n * (((d : ℝ) + 1) ^ k * M) := by
  let T := ‖x‖ ^ k • iteratedFDeriv ℝ n f x
  have hnorm : ‖T‖ = ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ := by
    rw [show T = ‖x‖ ^ k • iteratedFDeriv ℝ n f x from rfl, norm_smul,
      Real.norm_of_nonneg (by positivity)]
  rw [← hnorm]
  apply (euclideanMultilinear_norm_bounds T).2 _ (by positivity)
  intro j
  change ‖(‖x‖ ^ k • iteratedFDeriv ℝ n f x) (fun i => EuclideanSpace.basisFun (Fin d) ℝ (j i))‖ ≤ _
  rw [smul_apply, norm_smul, Real.norm_of_nonneg (by positivity),
    ← euclideanCoordinateDerivative_eq hf]
  exact euclidean_normPow_mul_le_of_coordinatePow_bounds x k (norm_nonneg _) (hconst j) (fun i => hpow i j)


end Masullo
