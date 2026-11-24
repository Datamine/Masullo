import ArchimedeanFlatMellin

open Set
open scoped SchwartzMap

namespace Masullo

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem schwartz_norm_jet_le_on_closedBall_of_vanishing_jets (f : 𝓢(E, ℂ)) (y : E)
    {r C : ℝ} (hr : 0 ≤ r) (m n : ℕ)
    (hy : ∀ k : ℕ, n ≤ k → k < n + m → iteratedFDeriv ℝ k f y = 0)
    (hbound : ∀ z ∈ Metric.closedBall y r, ‖iteratedFDeriv ℝ (n + m) f z‖ ≤ C) :
    ∀ z ∈ Metric.closedBall y r, ‖iteratedFDeriv ℝ n f z‖ ≤ C * r ^ m := by
  induction m generalizing n with
  | zero => simpa using hbound
  | succ m ih =>
    intro z hz
    let g := iteratedFDeriv ℝ n f.toFun
    have hg : Differentiable ℝ g :=
      f.smooth'.differentiable_iteratedFDeriv (by exact_mod_cast WithTop.coe_lt_top n)
    have hD (w : E) (hw : w ∈ Metric.closedBall y r) : ‖fderiv ℝ g w‖ ≤ C * r ^ m := by
      rw [norm_fderiv_iteratedFDeriv]
      refine ih (n+1) (fun k hk hkm ↦ hy k (by omega) (by omega)) ?_ w hw
      rw [show n + 1 + m = n + (m + 1) by omega]
      exact hbound
    have hb := (convex_closedBall y r).norm_image_sub_le_of_norm_fderiv_le
      (fun w _ ↦ hg w) hD (Metric.mem_closedBall_self hr) hz
    have hzero : g y = 0 := hy n le_rfl (by omega)
    have hC : 0 ≤ C := (norm_nonneg _).trans (hbound y (Metric.mem_closedBall_self hr))
    rw [hzero, sub_zero] at hb
    calc
      ‖g z‖ ≤ C * r ^ m * ‖z - y‖ := hb
      _ ≤ C * r ^ m * r := mul_le_mul_of_nonneg_left (by
        simpa only [Metric.mem_closedBall, dist_eq_norm] using hz) (by positivity)
      _ = C * r ^ (m + 1) := by rw [pow_succ, mul_assoc]

/-- If all jets vanish at the center, a Schwartz jet at a point within
distance one is bounded to any order in the distance. The global Schwartz
weight is retained, with a uniform bound in two ordinary seminorms. -/
theorem schwartzFlat_norm_pow_mul_norm_jet_le (f : 𝓢(E, ℂ)) (x y : E)
    (hy : ∀ n : ℕ, iteratedFDeriv ℝ n f y = 0)
    (hxy : ‖x - y‖ ≤ 1) (k n m : ℕ) :
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤
      3 ^ k * max (SchwartzMap.seminorm ℂ 0 (n + m) f)
        (SchwartzMap.seminorm ℂ k (n + m) f) * ‖x - y‖ ^ m := by
  let r := ‖x - y‖
  let C := max (SchwartzMap.seminorm ℂ 0 (n + m) f)
    (SchwartzMap.seminorm ℂ k (n + m) f)
  have hCS : ∀ z ∈ Metric.closedBall y r,
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ (n + m) f z‖ ≤ 3 ^ k * C := by
    intro z hz
    have hzr : ‖z - y‖ ≤ r := by
      simpa only [Metric.mem_closedBall, dist_eq_norm] using hz
    have hdist : ‖x - z‖ ≤ 2 := calc
      ‖x - z‖ ≤ ‖x - y‖ + ‖z - y‖ := by
        simpa only [← dist_eq_norm] using dist_triangle_right x z y
      _ ≤ 2 := by dsimp [r] at hzr; linarith
    have hx : ‖x‖ ≤ ‖z‖ + 2 := calc
      ‖x‖ = ‖x - z + z‖ := by rw [sub_add_cancel]
      _ ≤ ‖x - z‖ + ‖z‖ := norm_add_le _ _
      _ ≤ ‖z‖ + 2 := by linarith
    by_cases h : ‖z‖ ≤ 1
    · have hx3 : ‖x‖ ≤ 3 := by linarith
      exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hx3 _)
        ((SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ f _ z).trans (le_max_left _ _))
        (norm_nonneg _) (by positivity)
    · have hx3 : ‖x‖ ≤ 3 * ‖z‖ := by linarith
      calc
        _ ≤ (3 * ‖z‖) ^ k * ‖iteratedFDeriv ℝ (n+m) f z‖ :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hx3 _) (norm_nonneg _)
        _ ≤ 3 ^ k * C := by
          rw [mul_pow, mul_assoc]
          exact mul_le_mul_of_nonneg_left
            ((SchwartzMap.le_seminorm ℂ k (n+m) f z).trans (le_max_right _ _)) (by positivity)
  by_cases hx0 : ‖x‖ ^ k = 0
  · rw [hx0, zero_mul]
    positivity
  have hpos : 0 < ‖x‖ ^ k := lt_of_le_of_ne (by positivity) (Ne.symm hx0)
  have hb (z : E) (hz : z ∈ Metric.closedBall y r) :
      ‖iteratedFDeriv ℝ (n+m) f z‖ ≤ (3 ^ k * C) / ‖x‖ ^ k :=
    (le_div_iff₀ hpos).mpr (by rw [mul_comm]; exact hCS z hz)
  have hxball : x ∈ Metric.closedBall y r := by
    rw [Metric.mem_closedBall, dist_eq_norm]
  have he := schwartz_norm_jet_le_on_closedBall_of_vanishing_jets f y (norm_nonneg _) m n
    (fun j _ _ ↦ hy j) hb x hxball
  calc
    _ ≤ ‖x‖ ^ k * ((3 ^ k * C) / ‖x‖ ^ k * r ^ m) :=
      mul_le_mul_of_nonneg_left he hpos.le
    _ = 3 ^ k * C * r ^ m := by field_simp

/-- Near a coordinate hyperplane, flat Schwartz jets decay to every
order in the size of that coordinate, uniformly in the other coordinates. -/
theorem schwartzFlat_norm_pow_mul_norm_jet_le_of_coordinate
    {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    (p : E →L[ℝ] D) (i : D →L[ℝ] E) (hpi : Function.LeftInverse p i)
    (hi : ∀ d, ‖i d‖ ≤ ‖d‖) (f : 𝓢(E, ℂ))
    (hf : f ∈ schwartzFlatSubspace {x | p x = 0}) (x : E) (hx : ‖p x‖ ≤ 1) (k n m : ℕ) :
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤
      3 ^ k * max (SchwartzMap.seminorm ℂ 0 (n + m) f)
        (SchwartzMap.seminorm ℂ k (n + m) f) * ‖p x‖ ^ m := by
  let y := x - i (p x)
  have hy : p y = 0 := by
    change p (x - i (p x)) = 0
    rw [map_sub, hpi _, sub_self]
  have hd : ‖x - y‖ ≤ ‖p x‖ := by
    change ‖x - (x - i (p x))‖ ≤ ‖p x‖
    rw [sub_sub_cancel]
    exact hi _
  have hJ := (mem_schwartzFlatSubspace _ _).mp hf y hy
  refine (schwartzFlat_norm_pow_mul_norm_jet_le f x y hJ (hd.trans hx) k n m).trans ?_
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hd _) (by positivity)

/-- A bound valid both near and far from a coordinate hyperplane. It keeps
the rapid decay at infinity and every prescribed order of vanishing. -/
theorem schwartzFlat_weighted_jet_le_of_coordinate
    {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    (p : E →L[ℝ] D) (i : D →L[ℝ] E) (hpi : Function.LeftInverse p i)
    (hi : ∀ d, ‖i d‖ ≤ ‖d‖) (f : 𝓢(E, ℂ))
    (hf : f ∈ schwartzFlatSubspace {x | p x = 0}) (x : E) (k n m : ℕ) :
    max 1 ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤
      3 ^ k * max (max (SchwartzMap.seminorm ℂ 0 n f) (SchwartzMap.seminorm ℂ k n f))
        (max (SchwartzMap.seminorm ℂ 0 (n + m) f) (SchwartzMap.seminorm ℂ k (n + m) f)) *
        min 1 ‖p x‖ ^ m := by
  let C := max (max (SchwartzMap.seminorm ℂ 0 n f) (SchwartzMap.seminorm ℂ k n f))
    (max (SchwartzMap.seminorm ℂ 0 (n + m) f) (SchwartzMap.seminorm ℂ k (n + m) f))
  have hC : 0 ≤ C := (apply_nonneg _ _).trans ((le_max_left _ _).trans (le_max_left _ _))
  have h3 : 1 ≤ (3 : ℝ) ^ k := one_le_pow₀ (by norm_num)
  change max 1 ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ 3 ^ k * C * min 1 ‖p x‖ ^ m
  rcases le_total ‖p x‖ 1 with hp | hp
  · rw [min_eq_right hp]
    rcases le_total ‖x‖ 1 with hx | hx
    · rw [max_eq_left hx, one_pow, one_mul]
      have h := schwartzFlat_norm_pow_mul_norm_jet_le_of_coordinate p i hpi hi f hf x hp 0 n m
      simp only [pow_zero, one_mul, max_self] at h
      refine h.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
      exact ((le_max_left _ _).trans (le_max_right _ _)).trans (le_mul_of_one_le_left hC h3)
    · rw [max_eq_right hx]
      refine (schwartzFlat_norm_pow_mul_norm_jet_le_of_coordinate p i hpi hi f hf x hp k n m).trans ?_
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (le_max_right _ _) (by positivity))
        (by positivity)
  · rw [min_eq_left hp, one_pow, mul_one]
    refine le_trans ?_ (le_mul_of_one_le_left hC h3)
    rcases le_total ‖x‖ 1 with hx | hx
    · rw [max_eq_left hx, one_pow, one_mul]
      exact (SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ f _ x).trans
        ((le_max_left _ _).trans (le_max_left _ _))
    · rw [max_eq_right hx]
      exact (SchwartzMap.le_seminorm ℂ _ _ f x).trans ((le_max_right _ _).trans (le_max_left _ _))

end Masullo
