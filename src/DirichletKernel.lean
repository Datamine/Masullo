import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

open Complex Filter MeasureTheory Set Topology
open scoped FourierTransform

namespace Masullo

noncomputable section

/-- The symmetric Fourier kernel on a period of length one. -/
def symmetricDirichletKernel (n : ℕ) (x : ℝ) : ℝ :=
  1 + 2 * ∑ k ∈ Finset.range n, Real.cos (2 * Real.pi * (k + 1) * x)

theorem symmetricDirichletKernel_even (n : ℕ) (x : ℝ) :
    symmetricDirichletKernel n (-x) = symmetricDirichletKernel n x := by
  simp [symmetricDirichletKernel, mul_neg, Real.cos_neg]

theorem symmetricDirichletKernel_mul_sin (n : ℕ) (x : ℝ) :
    symmetricDirichletKernel n x * Real.sin (Real.pi * x) =
      Real.sin ((2 * n + 1) * (Real.pi * x)) := by
  induction n with
  | zero => simp [symmetricDirichletKernel]
  | succ n ih =>
    have hn : symmetricDirichletKernel (n + 1) x =
        symmetricDirichletKernel n x + 2 * Real.cos (2 * Real.pi * (n + 1) * x) := by
      rw [symmetricDirichletKernel, Finset.sum_range_succ, symmetricDirichletKernel]
      ring
    rw [hn, add_mul, ih]
    push_cast
    have he : (2 * ((n : ℝ) + 1) + 1) * (Real.pi * x) =
        2 * Real.pi * ((n : ℝ) + 1) * x + Real.pi * x := by ring
    have hf : (2 * (n : ℝ) + 1) * (Real.pi * x) =
        2 * Real.pi * ((n : ℝ) + 1) * x - Real.pi * x := by ring
    rw [he, hf, Real.sin_add, Real.sin_sub]
    ring

private theorem symmetricDirichletKernel_continuous (n : ℕ) :
    Continuous (symmetricDirichletKernel n) := by
  unfold symmetricDirichletKernel
  fun_prop

private theorem integral_symmetricDirichletKernel (n : ℕ) :
    (∫ x in (0 : ℝ)..(1 / 2 : ℝ), (symmetricDirichletKernel n x : ℂ)) = 1 / 2 := by
  have h (k : ℕ) : (∫ x in (0 : ℝ)..(1 / 2 : ℝ),
      (Real.cos (2 * Real.pi * (k + 1) * x) : ℂ)) = 0 := by
    let c : ℂ := 2 * Real.pi * (k + 1)
    have hc : c ≠ 0 := by
      dsimp [c]
      exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
        (by exact_mod_cast Nat.succ_ne_zero k)
    simp only [Complex.ofReal_cos, Complex.ofReal_mul, Complex.ofReal_add,
      Complex.ofReal_natCast, Complex.ofReal_one, Complex.ofReal_ofNat]
    change (∫ x in (0 : ℝ)..(1 / 2 : ℝ), Complex.cos (c * (x : ℂ))) = 0
    rw [integral_cos_mul_complex hc]
    have he : c * ((1 / 2 : ℝ) : ℂ) = ((k + 1 : ℕ) : ℂ) * Real.pi := by
      dsimp [c]
      push_cast
      ring
    rw [he, Complex.sin_nat_mul_pi]
    simp
  have hi (k : ℕ) :
      IntervalIntegrable (fun x : ℝ => (Real.cos (2 * Real.pi * (k + 1) * x) : ℂ))
        volume 0 (1 / 2) := (by fun_prop : Continuous _).intervalIntegrable _ _
  simp only [symmetricDirichletKernel, Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_mul,
    Complex.ofReal_ofNat, Complex.ofReal_sum]
  have hS : IntervalIntegrable (fun x : ℝ => ∑ k ∈ Finset.range n,
      (Real.cos (2 * Real.pi * (k + 1) * x) : ℂ)) volume 0 (1 / 2) := by
    apply Continuous.intervalIntegrable
    fun_prop
  have h2 : IntervalIntegrable (fun x : ℝ => (2 : ℂ) * ∑ k ∈ Finset.range n,
      (Real.cos (2 * Real.pi * (k + 1) * x) : ℂ)) volume 0 (1 / 2) := hS.const_mul _
  rw [intervalIntegral.integral_add intervalIntegrable_const h2, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_finsetSum (fun k _ => hi k)]
  rw [Finset.sum_eq_zero fun k _ => h k]
  norm_num

private theorem tendsto_integral_sine_frequency (g : ℝ → ℂ) (hg : Integrable g) :
    Tendsto (fun n : ℕ => ∫ x : ℝ, (Real.sin ((2 * n + 1) * (Real.pi * x)) : ℂ) * g x)
      atTop (𝓝 0) := by
  let a (n : ℕ) : ℝ := n + 1 / 2
  have ha : Tendsto a atTop atTop := tendsto_atTop_mono
    (fun n => show (n : ℝ) ≤ (n : ℝ) + 1 / 2 by linarith) tendsto_natCast_atTop_atTop
  have hp := (Real.zero_at_infty_fourier g).comp (ha.mono_right atTop_le_cocompact)
  have hm := (Real.zero_at_infty_fourier g).comp
    ((tendsto_neg_atTop_atBot.comp ha).mono_right atBot_le_cocompact)
  have h := (hm.sub hp).div_const (2 * I)
  refine h.congr' ?_ |> (fun ht => by simpa using ht)
  filter_upwards [] with n
  simp only [Function.comp_apply]
  rw [Real.fourier_eq', Real.fourier_eq']
  simp only [Real.inner_apply]
  have hI (w : ℝ) : Integrable (fun x : ℝ => Complex.exp ((-2 * Real.pi * (x * w) : ℝ) * I) • g x) :=
    hg.bdd_mul (c := 1) ((by fun_prop : Continuous (fun x : ℝ =>
      Complex.exp ((-2 * Real.pi * (x * w) : ℝ) * I))).aestronglyMeasurable)
      (Eventually.of_forall fun x => by simp [Complex.norm_exp, Complex.mul_re])
  rw [← integral_sub (hI (-(a n))) (hI (a n)), ← integral_div]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [smul_eq_mul]
  let y : ℝ := (2 * (n : ℝ) + 1) * (Real.pi * x)
  have he : ((-2 * Real.pi * (x * -(a n)) : ℝ) : ℂ) = (y : ℂ) := by
    congr 1
    dsimp [a, y]
    ring
  have hf : ((-2 * Real.pi * (x * a n) : ℝ) : ℂ) = -(y : ℂ) := by
    rw [← Complex.ofReal_neg]
    congr 1
    dsimp [a, y]
    ring
  rw [he, hf]
  have hcast : (y : ℂ) = (2 * (n : ℂ) + 1) * ((Real.pi : ℂ) * (x : ℂ)) := by
    dsimp [y]
    push_cast
    rfl
  rw [← hcast]
  change (Complex.exp ((y : ℂ) * I) * g x - Complex.exp (-(y : ℂ) * I) * g x) / (2 * I) =
    Complex.sin (y : ℂ) * g x
  rw [Complex.sin, div_eq_mul_inv, mul_inv_rev, Complex.inv_I]
  ring


/-- Symmetric Fourier averages converge to the midpoint of the two
one-sided values when their paired error is bounded by a constant times
the distance to zero. The function `u` is the paired value. -/
theorem tendsto_symmetricDirichlet_midpoint (u : ℝ → ℂ)
    (hu : Measurable u) (L : ℂ) (C : ℝ) (hC : 0 ≤ C)
    (herror : ∀ x ∈ Ioc (0 : ℝ) (1 / 2), ‖u x - L‖ ≤ C * x) :
    Tendsto (fun n : ℕ => ∫ x in (0 : ℝ)..(1 / 2 : ℝ),
      (symmetricDirichletKernel n x : ℂ) * u x) atTop (𝓝 (L / 2)) := by
  let A := Ioc (0 : ℝ) (1 / 2)
  let q (x : ℝ) := (u x - L) / (Real.sin (Real.pi * x) : ℂ)
  let g := A.indicator q
  have hq : Measurable q := (hu.sub measurable_const).div
    (by fun_prop : Continuous (fun x : ℝ => (Real.sin (Real.pi * x) : ℂ))).measurable
  have hU (x : ℝ) (hx : x ∈ A) : 2 * x ≤ Real.sin (Real.pi * x) := by
    have h := Real.le_sin_mul (x := 2 * x) (by linarith [hx.1]) (by linarith [hx.2])
    convert h using 2
    ring
  have hp (x : ℝ) (hx : x ∈ A) : 0 < Real.sin (Real.pi * x) :=
    (by linarith [hx.1] : 0 < 2 * x).trans_le (hU x hx)
  have hqle (x : ℝ) (hx : x ∈ A) : ‖q x‖ ≤ C / 2 := by
    dsimp only [q]
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (hp x hx).le]
    apply (div_le_iff₀ (hp x hx)).mpr
    exact (herror x hx).trans ((show C * x = C / 2 * (2 * x) by ring).le.trans
      (mul_le_mul_of_nonneg_left (hU x hx) (by positivity)))
  have hqi : IntegrableOn q A := by
    apply (integrableOn_const (C := C / 2) (measure_Ioc_lt_top.ne)).mono'
      hq.aestronglyMeasurable
    exact (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall hqle)
  have hg : Integrable g := hqi.integrable_indicator measurableSet_Ioc
  have hui : IntervalIntegrable u volume 0 (1 / 2) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    apply (integrableOn_const (C := C * (1 / 2) + ‖L‖) (measure_Ioc_lt_top.ne)).mono'
      hu.aestronglyMeasurable
    apply (ae_restrict_iff' measurableSet_Ioc).mpr
    exact Eventually.of_forall fun x hx => calc
      ‖u x‖ = ‖u x - L + L‖ := by rw [sub_add_cancel]
      _ ≤ ‖u x - L‖ + ‖L‖ := norm_add_le _ _
      _ ≤ _ := add_le_add ((herror x hx).trans
        (mul_le_mul_of_nonneg_left hx.2 hC)) le_rfl
  have he (n : ℕ) :
      (∫ x : ℝ, (Real.sin ((2 * n + 1) * (Real.pi * x)) : ℂ) * g x) =
        (∫ x in (0 : ℝ)..(1 / 2 : ℝ), (symmetricDirichletKernel n x : ℂ) * u x) - L / 2 := by
    let D (x : ℝ) : ℂ := symmetricDirichletKernel n x
    have hD : Continuous D := Complex.continuous_ofReal.comp (symmetricDirichletKernel_continuous n)
    have hq (x : ℝ) (hx : x ∈ A) :
        (Real.sin ((2 * n + 1) * (Real.pi * x)) : ℂ) * q x = D x * (u x - L) := by
      have hs := congrArg (fun t : ℝ => (t : ℂ)) (symmetricDirichletKernel_mul_sin n x)
      rw [← hs, Complex.ofReal_mul]
      dsimp only [q, D]
      let y : ℂ := Real.sin (Real.pi * x)
      have hy : y ≠ 0 := Complex.ofReal_ne_zero.mpr (hp x hx).ne'
      change (symmetricDirichletKernel n x : ℂ) * y * ((u x - L) / y) = _
      rw [mul_assoc, mul_comm y, div_mul_cancel₀ _ hy]
    calc
      _ = ∫ x in A, (Real.sin ((2 * n + 1) * (Real.pi * x)) : ℂ) * q x := by
        rw [← integral_indicator measurableSet_Ioc]
        apply integral_congr_ae
        filter_upwards [] with x
        by_cases hx : x ∈ A
        · rw [show g = A.indicator q from rfl, indicator_of_mem hx, indicator_of_mem hx]
        · rw [show g = A.indicator q from rfl, indicator_of_notMem hx, indicator_of_notMem hx, mul_zero]
      _ = ∫ x in A, D x * (u x - L) := setIntegral_congr_fun measurableSet_Ioc hq
      _ = _ := by
        rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)]
        simp_rw [mul_sub]
        have hDC : Continuous (fun x => D x * L) := hD.mul continuous_const
        rw [intervalIntegral.integral_sub (hui.continuousOn_mul hD.continuousOn)
          (hDC.intervalIntegrable _ _), intervalIntegral.integral_mul_const]
        change _ - (∫ x in (0 : ℝ)..(1 / 2 : ℝ), (symmetricDirichletKernel n x : ℂ)) * L = _
        rw [integral_symmetricDirichletKernel]
        ring
  have ht := (tendsto_integral_sine_frequency g hg).add_const (L / 2)
  simpa only [he, sub_add_cancel, zero_add] using ht


end
end Masullo
