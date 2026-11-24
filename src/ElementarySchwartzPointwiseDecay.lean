import ElementarySchwartz

open Filter Topology
open scoped ENNReal

namespace Masullo

/-- The global supremum in (D.1.3.33) cannot satisfy the stated inverse
weight at every point, already for the single real weight of degree one. -/
theorem not_uniform_supremum_le_inverseWeight (M C : ℝ) (hM : 0 < M) :
    ¬ ∀ x : ℝ, M ≤ C / (1 + |x|) := by
  intro h
  let x := max (C / M) 0
  have hx : 0 ≤ x := le_max_right _ _
  have hC : C ≤ x * M := (div_le_iff₀ hM).mp (le_max_left _ _)
  have hbound := h x
  rw [abs_of_nonneg hx] at hbound
  have hb : M * (1 + x) ≤ C := (le_div_iff₀ (by positivity : 0 < 1 + x)).mp hbound
  nlinarith

private theorem one_add_pow_mul_le (r : ℝ) (hr : 0 ≤ r) (j k : ℕ) :
    (1 + r ^ j) * (1 + r ^ k) ≤ 4 * (1 + r ^ (j + k)) := by
  by_cases h : r ≤ 1
  · have hj : r ^ j ≤ 1 := pow_le_one₀ hr h
    have hk : r ^ k ≤ 1 := pow_le_one₀ hr h
    have hp : (1 + r ^ j) * (1 + r ^ k) ≤ 2 * 2 :=
      mul_le_mul (by linarith) (by linarith) (by positivity) (by norm_num)
    exact hp.trans (by nlinarith [pow_nonneg hr (j+k)])
  · have hj : 1 ≤ r ^ j := one_le_pow₀ (le_of_not_ge h)
    have hk : 1 ≤ r ^ k := one_le_pow₀ (le_of_not_ge h)
    have hp : (1 + r ^ j) * (1 + r ^ k) ≤ (2 * r ^ j) * (2 * r ^ k) :=
      mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
    rw [pow_add]
    linarith

noncomputable section

variable {m n r : ℕ} {F : Type*} [AddCommGroup F] [TopologicalSpace F]
  [DiscreteTopology F] [Finite F]

/-- The pointwise replacement for (D.1.3.33). The inverse weight controls
the mixed derivative at the evaluation point through a larger seminorm. -/
theorem elementarySchwartz_pointwise_decay_P1
    (h : ElementarySchwartz m n r F) (p q p' q' : ℕ)
    (β : Fin m → ℕ) (γ : Fin n → ℕ)
    (xt : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n))
    (a : Fin r → ℤ) (b : F) :
    let aVec : EuclideanSpace ℝ (Fin r) := WithLp.toLp 2 (fun k => (a k : ℝ))
    (1 + ‖xt.1‖ ^ p) * (1 + ‖aVec‖ ^ p') * ‖elementaryPartial h β γ xt a b‖ ≤
      (16 * elementarySchwartz_withSeminorms_P1.choose (p+q, p'+q', β, γ) h) /
        ((1 + ‖xt.1‖ ^ q) * (1 + ‖aVec‖ ^ q')) := by
  dsimp only
  let x := ‖xt.1‖
  let y := ‖(WithLp.toLp 2 (fun k => (a k : ℝ)) : EuclideanSpace ℝ (Fin r))‖
  let v := ‖elementaryPartial h β γ xt a b‖
  let s := elementarySchwartz_withSeminorms_P1.choose (p+q, p'+q', β, γ) h
  have hs : (1 + x ^ (p+q)) * (1 + y ^ (p'+q')) * v ≤ s := by
    apply (ENNReal.ofReal_le_ofReal_iff (apply_nonneg _ _)).mp
    dsimp only [s]
    rw [elementarySchwartz_withSeminorms_P1.choose_spec.2]
    exact le_iSup_of_le xt (le_iSup_of_le a (le_iSup_of_le b le_rfl))
  have hh := mul_le_mul (one_add_pow_mul_le x (norm_nonneg _) p q)
    (one_add_pow_mul_le y (norm_nonneg _) p' q') (by dsimp [y]; positivity) (by dsimp [x]; positivity)
  change (1 + x ^ p) * (1 + y ^ p') * v ≤
    (16 * s) / ((1 + x ^ q) * (1 + y ^ q'))
  apply (le_div_iff₀ (by dsimp [x, y]; positivity)).mpr
  calc
    _ = ((1 + x^p) * (1 + x^q)) * ((1 + y^p') * (1 + y^q')) * v := by ring
    _ ≤ (4 * (1 + x^(p+q))) * (4 * (1 + y^(p'+q'))) * v :=
      mul_le_mul_of_nonneg_right hh (norm_nonneg _)
    _ = 16 * ((1 + x ^ (p+q)) * (1 + y ^ (p'+q')) * v) := by ring
    _ ≤ 16 * s := mul_le_mul_of_nonneg_left hs (by norm_num)

end
end Masullo
