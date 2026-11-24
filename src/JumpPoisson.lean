import DirichletKernel
import JumpPeriodization

open Complex Filter Function MeasureTheory Set Topology

namespace Masullo

noncomputable section

/-- The exponential weights for the integer frequencies of a period-one test. -/
def poissonPhase (m : ℤ) (x : ℝ) : ℂ :=
  Complex.exp ((m : ℂ) * (2 * Real.pi * I) * (x : ℂ))

private theorem poissonPhase_continuous (m : ℤ) : Continuous (poissonPhase m) := by
  unfold poissonPhase
  fun_prop

private theorem poissonPhase_norm (m : ℤ) (x : ℝ) : ‖poissonPhase m x‖ = 1 := by
  rw [poissonPhase, norm_exp]
  simp [Complex.mul_re, Complex.mul_im]

private theorem poissonPhase_add_int (m n : ℤ) (x : ℝ) :
    poissonPhase m ((n : ℝ) + x) = poissonPhase m x := by
  unfold poissonPhase
  push_cast
  rw [mul_add, Complex.exp_add]
  have h : ((m : ℂ) * (2 * Real.pi * I) * (n : ℂ)) =
      ((m * n : ℤ) : ℂ) * (2 * Real.pi * I) := by push_cast; ring
  rw [h, Complex.exp_int_mul_two_pi_mul_I, one_mul]

private theorem sum_poissonPhase (n : ℕ) (x : ℝ) :
    (∑ m ∈ Finset.Icc (-(n : ℤ)) n, poissonPhase m x) = symmetricDirichletKernel n x := by
  induction n with
  | zero => simp [symmetricDirichletKernel, poissonPhase]
  | succ n ih =>
    have hi : Finset.Icc (-((n + 1 : ℕ) : ℤ)) ((n + 1 : ℕ) : ℤ) =
        insert ((n + 1 : ℕ) : ℤ)
          (insert (-((n + 1 : ℕ) : ℤ)) (Finset.Icc (-(n : ℤ)) n)) := by
      ext m
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have hleft : -((n + 1 : ℕ) : ℤ) ∉ Finset.Icc (-(n : ℤ)) n := by
      simp only [Finset.mem_Icc]
      omega
    have hright : ((n + 1 : ℕ) : ℤ) ∉
        insert (-((n + 1 : ℕ) : ℤ)) (Finset.Icc (-(n : ℤ)) n) := by
      simp only [Finset.mem_insert, Finset.mem_Icc]
      omega
    rw [hi, Finset.sum_insert hright, Finset.sum_insert hleft, ih]
    have hpos : poissonPhase ((n + 1 : ℕ) : ℤ) x =
        Complex.exp ((2 * Real.pi * (n + 1) * x : ℝ) * I) := by
      unfold poissonPhase
      congr 1
      push_cast
      ring
    have hneg : poissonPhase (-((n + 1 : ℕ) : ℤ)) x =
        Complex.exp (-((2 * Real.pi * (n + 1) * x : ℝ) : ℂ) * I) := by
      unfold poissonPhase
      congr 1
      push_cast
      ring
    simp only [symmetricDirichletKernel, Finset.sum_range_succ, Complex.ofReal_add,
      Complex.ofReal_one, Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_sum,
      Complex.ofReal_cos, Complex.ofReal_natCast]
    rw [hpos, hneg]
    unfold Complex.cos
    push_cast
    ring

private theorem periodized_coefficient {u : ℝ → ℂ} (hmu : Measurable u) (hui : Integrable u)
    (A : ℤ → ℝ) (hA : Summable A) (hbound : ∀ x (n : ℤ), |x| ≤ 1 / 2 → ‖u ((n : ℝ) + x)‖ ≤ A n)
    (m : ℤ) :
    (∫ x in (-(1 / 2) : ℝ)..(1 / 2 : ℝ), poissonPhase m x * ∑' n : ℤ, u ((n : ℝ) + x)) =
      ∫ x, poissonPhase m x * u x := by
  let a : ℝ := -(1 / 2)
  let b : ℝ := 1 / 2
  let C := Ioc a b
  let f (x : ℝ) := poissonPhase m x * u x
  have hfi : Integrable f :=
    hui.bdd_mul ((poissonPhase_continuous m).measurable.aestronglyMeasurable)
      (Eventually.of_forall fun x => (poissonPhase_norm m x).le)
  let g (n : ℤ) (x : ℝ) := poissonPhase m x * u ((n : ℝ) + x)
  have hgn (n : ℤ) (x : ℝ) (hx : x ∈ C) : ‖g n x‖ ≤ A n := by
    dsimp only [g]
    rw [norm_mul, poissonPhase_norm, one_mul]
    exact hbound x n (abs_le.mpr ⟨hx.1.le, hx.2⟩)
  have hgm (n : ℤ) : Measurable (g n) :=
    (poissonPhase_continuous m).measurable.mul (hmu.comp (measurable_const.add measurable_id))
  have hG (n : ℤ) : Integrable (g n) (volume.restrict C) :=
    (integrableOn_const (C := A n) (measure_Ioc_lt_top.ne)).mono' (hgm n).aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall (hgn n)))
  have hAi (n : ℤ) : (∫ x in C, ‖g n x‖) ≤ A n := by
    have h := integral_mono_ae (hG n).norm (integrable_const (A n))
      ((ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall (hgn n)))
    norm_num [C, a, b, Measure.real] at h ⊢
    exact h
  have hsum : Summable (fun n : ℤ => ∫ x in C, ‖g n x‖) :=
    hA.of_nonneg_of_le (fun n => integral_nonneg fun x => norm_nonneg _) hAi
  have hcong (n : ℤ) :
      (∫ x in C, g n x) = ∫ y in a + n..a + n + 1, f y := by
    rw [← intervalIntegral.integral_of_le (show a ≤ b by dsimp [a,b]; norm_num)]
    have hEq : g n = fun x : ℝ => f (x + n) := by
      funext x
      dsimp [g, f]
      rw [add_comm x, poissonPhase_add_int]
    rw [hEq, intervalIntegral.integral_comp_add_right]
    congr 1
    dsimp [a, b]
    ring
  change (∫ x in a..b, poissonPhase m x * ∑' n : ℤ, u ((n : ℝ) + x)) = ∫ x, f x
  rw [intervalIntegral.integral_of_le (show a ≤ b by dsimp [a,b]; norm_num)]
  calc
    _ = ∫ x in C, (∑' n : ℤ, g n x) := by simp only [C, g, tsum_mul_left]
    _ = ∑' n : ℤ, ∫ x in C, g n x := (integral_tsum_of_summable_integral_norm hG hsum).symm
    _ = _ := by simp only [hcong]; exact (hfi.hasSum_intervalIntegral a).tsum_eq

/-- Symmetric period-one Poisson summation for piecewise smooth data.
The two one-sided sample sums are absolutely convergent. -/
theorem jumpPoisson_period_one
    {u v left right : ℝ → ℂ} (S : Finset ℝ)
    (hu : SuperExponentialLogDecay u) (hv : SuperExponentialLogDecay v)
    (hmu : Measurable u) (hmv : Measurable v) (hui : Integrable u)
    (hderiv : ∀ x ∉ S, HasDerivAt u (v x) x)
    (hleft : ∀ x, Tendsto u (𝓝[<] x) (𝓝 (left x)))
    (hright : ∀ x, Tendsto u (𝓝[>] x) (𝓝 (right x))) :
    (Summable fun n : ℤ => ‖(left n + right n) / 2‖) ∧
      Tendsto (fun N : ℕ => ∑ m ∈ Finset.Icc (-(N : ℤ)) N,
        ∫ x, poissonPhase m x * u x) atTop (𝓝 (∑' n : ℤ, (left n + right n) / 2)) := by
  let β := fun x : ℝ => ∑' n : ℤ, u ((n : ℝ) + x)
  let L := (∑' n : ℤ, left n) + ∑' n : ℤ, right n
  obtain ⟨hsl, hsr, K, hK, hKbd⟩ :=
    jumpPeriodization_midpoint_bound S hu hv hmv hderiv hleft hright
  have hsum : Summable (fun n : ℤ => ‖(left n + right n) / 2‖) := by
    simp only [norm_div]
    apply Summable.div_const
    exact (hsl.add hsr).of_nonneg_of_le (fun n => norm_nonneg _) fun n => norm_add_le _ _
  refine ⟨hsum, ?_⟩
  have hmuβ : Measurable β := Measurable.tsum fun n =>
    hmu.comp (measurable_const.add measurable_id)
  have hpaired : Measurable (fun x : ℝ => β x + β (-x)) := hmuβ.add (hmuβ.comp measurable_neg)
  have hlim := tendsto_symmetricDirichlet_midpoint (fun x => β x + β (-x))
    hpaired L K hK hKbd
  have hL : L / 2 = ∑' n : ℤ, (left n + right n) / 2 := by
    rw [tsum_div_const, hsl.of_norm.tsum_add hsr.of_norm]
  rw [hL] at hlim
  convert hlim using 1
  funext N
  obtain ⟨A, hA, _, hbd⟩ := integerTranslate_summable_majorant hu
  have hbi : IntervalIntegrable β volume (-(1 / 2)) (1 / 2) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (-(1 / 2) : ℝ) ≤ 1 / 2)]
    let M := ∑' n : ℤ, A n
    apply (integrableOn_const (C := M) (measure_Ioc_lt_top.ne)).mono'
      hmuβ.aestronglyMeasurable
    apply (ae_restrict_iff' measurableSet_Ioc).mpr
    exact Eventually.of_forall fun x hx => by
      have hb (n : ℤ) := hbd x n (abs_le.mpr ⟨hx.1.le, hx.2⟩)
      have hs := hA.of_nonneg_of_le (fun n => norm_nonneg _) hb
      exact (norm_tsum_le_tsum_norm hs).trans (hs.tsum_le_tsum hb hA)
  let D (x : ℝ) : ℂ := symmetricDirichletKernel N x
  have hD : Continuous D := by unfold D symmetricDirichletKernel; fun_prop
  have hDi : IntervalIntegrable (fun x => D x * β x) volume (-(1 / 2)) (1 / 2) :=
    hbi.continuousOn_mul hD.continuousOn
  have hDj : IntervalIntegrable (fun x => D x * β x) volume (-(1 / 2)) 0 :=
    hDi.mono_set (by
      rw [uIcc_of_le (by norm_num : (-(1 / 2) : ℝ) ≤ 0),
        uIcc_of_le (by norm_num : (-(1 / 2) : ℝ) ≤ 1 / 2)]
      exact Icc_subset_Icc_right (by norm_num))
  have hDk : IntervalIntegrable (fun x => D x * β x) volume 0 (1 / 2) :=
    hDi.mono_set (by
      rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2),
        uIcc_of_le (by norm_num : (-(1 / 2) : ℝ) ≤ 1 / 2)]
      exact Icc_subset_Icc_left (by norm_num))
  calc
    _ = ∑ m ∈ Finset.Icc (-(N : ℤ)) N,
        ∫ x in (-(1 / 2) : ℝ)..(1 / 2 : ℝ), poissonPhase m x * β x := by
      exact Finset.sum_congr rfl fun m _ => (periodized_coefficient hmu hui A hA hbd m).symm
    _ = ∫ x in (-(1 / 2) : ℝ)..(1 / 2 : ℝ), D x * β x := by
      rw [← intervalIntegral.integral_finsetSum fun m _ =>
        hbi.continuousOn_mul (poissonPhase_continuous m).continuousOn]
      simp only [← Finset.sum_mul, sum_poissonPhase]
      rfl
    _ = (∫ x in (-(1 / 2) : ℝ)..0, D x * β x) +
        (∫ x in (0 : ℝ)..(1 / 2 : ℝ), D x * β x) :=
      (intervalIntegral.integral_add_adjacent_intervals hDj hDk).symm
    _ = (∫ x in (0 : ℝ)..(1 / 2 : ℝ), D x * β (-x)) +
        (∫ x in (0 : ℝ)..(1 / 2 : ℝ), D x * β x) := by
      have h := intervalIntegral.integral_comp_neg (f := fun x => D x * β x)
        (a := (0 : ℝ)) (b := 1 / 2)
      simpa only [D, symmetricDirichletKernel_even, neg_zero, neg_neg] using
        congrArg (fun z => z + ∫ x in (0 : ℝ)..(1 / 2 : ℝ), D x * β x) h.symm
    _ = _ := by
      have hi : IntervalIntegrable (fun x => D x * β (-x)) volume 0 (1 / 2) := by
        simpa only [D, symmetricDirichletKernel_even, neg_zero, neg_neg] using
          (IntervalIntegrable.iff_comp_neg (f := fun x => D x * β x) (a := (0 : ℝ))
            (b := -(1 / 2))).mp hDj.symm
      rw [← intervalIntegral.integral_add hi hDk]
      apply intervalIntegral.integral_congr
      intro x _
      change D x * β (-x) + D x * β x = D x * (β x + β (-x))
      ring


end
end Masullo
