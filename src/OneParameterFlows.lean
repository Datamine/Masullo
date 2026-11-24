import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Instances.Real.Lemmas

open Filter MeasureTheory Set Topology
open scoped ContDiff

namespace Masullo

/-- A continuous homomorphism from the additive real line to the units of
a real normed field is smooth. The result includes its derivative as
multiplication by a fixed element of the field. -/
theorem continuous_oneParameter_smooth {K : Type*} [NormedField K] [NormedAlgebra ℝ K]
    [CompleteSpace K] (γ : Multiplicative ℝ →* Kˣ)
    (hγ : Continuous (fun t : ℝ => ((γ (Multiplicative.ofAdd t) : Kˣ) : K))) :
    let g (t : ℝ) := ((γ (Multiplicative.ofAdd t) : Kˣ) : K)
    ContDiff ℝ ∞ g ∧ ∃ c : K, ∀ t : ℝ, HasDerivAt g (g t * c) t := by
  dsimp only
  let g (t : ℝ) := ((γ (Multiplicative.ofAdd t) : Kˣ) : K)
  have g₀ : g 0 = 1 := by simp [g]
  have hmul (t u : ℝ) : g (t + u) = g t * g u := by
    change ((γ (Multiplicative.ofAdd t * Multiplicative.ofAdd u) : Kˣ) : K) = _
    rw [map_mul]
    rfl
  let B (t : ℝ) := ∫ y in (0 : ℝ)..t, g y
  have hB (t : ℝ) : HasDerivAt B (g t) t :=
    intervalIntegral.integral_hasDerivAt_right (hγ.intervalIntegrable _ _)
      (hγ.stronglyMeasurableAtFilter volume (𝓝 t)) hγ.continuousAt
  have hB₀ : B 0 = 0 := intervalIntegral.integral_same
  have hslope := (hB 0).tendsto_slope
  rw [g₀] at hslope
  obtain ⟨a, ha⟩ := (hslope.eventually_ne one_ne_zero).exists
  have hBa : B a ≠ 0 := by
    intro h
    exact ha (by simp [slope, hB₀, h])
  have he (t : ℝ) : B (t + a) - B t = g t * B a := by
    calc
      _ = ∫ y in t..t + a, g y := by
        apply sub_eq_of_eq_add'
        exact (intervalIntegral.integral_add_adjacent_intervals
          (hγ.intervalIntegrable 0 t) (hγ.intervalIntegrable t (t + a))).symm
      _ = ∫ y in (0 : ℝ)..a, g (y + t) := by
        rw [intervalIntegral.integral_comp_add_right, zero_add, add_comm a t]
      _ = _ := by
        simp_rw [add_comm _ t, hmul]
        exact intervalIntegral.integral_const_mul _ _
  have heq : (fun t => (B (t + a) - B t) * (B a)⁻¹) = g := by
    funext t
    rw [he, mul_assoc, mul_inv_cancel₀ hBa, mul_one]
  let c := (g a - 1) * (B a)⁻¹
  have hd (t : ℝ) : HasDerivAt g (g t * c) t := by
    have h := (((hB (t + a)).comp_add_const t a).sub (hB t)).mul_const (B a)⁻¹
    change HasDerivAt (fun y => (B (y + a) - B y) * (B a)⁻¹)
      ((g (t + a) - g t) * (B a)⁻¹) t at h
    rw [heq] at h
    have hcoeff : g (t + a) - g t = g t * (g a - 1) := by rw [hmul, mul_sub, mul_one]
    simpa only [hcoeff, mul_assoc, c] using h
  have hsmooth : ∀ n : ℕ, ContDiff ℝ n g := by
    intro n
    induction n with
    | zero => exact contDiff_zero.mpr hγ
    | succ n ih =>
      rw [Nat.cast_succ, contDiff_succ_iff_deriv]
      refine ⟨fun t => (hd t).differentiableAt, by simp, ?_⟩
      rw [show deriv g = fun t => g t * c from funext fun t => (hd t).deriv]
      exact ih.mul contDiff_const
  exact ⟨contDiff_infty.mpr hsmooth, c, hd⟩

/-- In a complex coordinate the homomorphism has a unique exponential
parameter. This includes the phase, which the norm does not determine. -/
theorem complex_oneParameter_exp (γ : Multiplicative ℝ →* ℂˣ)
    (hγ : Continuous (fun t : ℝ => ((γ (Multiplicative.ofAdd t) : ℂˣ) : ℂ))) :
    ∃! c : ℂ, ∀ t : ℝ,
      (γ (Multiplicative.ofAdd t) : ℂ) = Complex.exp (c * (t : ℂ)) := by
  let g (t : ℝ) := ((γ (Multiplicative.ofAdd t) : ℂˣ) : ℂ)
  obtain ⟨_, c, hc⟩ := continuous_oneParameter_smooth γ hγ
  have hzero : g 0 = 1 := by simp [g]
  have hExp (a : ℂ) (t : ℝ) :
      HasDerivAt (fun x : ℝ => Complex.exp (a * (x : ℂ)))
        (a * Complex.exp (a * (t : ℂ))) t := by
    have h : HasDerivAt (fun z : ℂ => Complex.exp (a * z))
        (a * Complex.exp (a * (t : ℂ))) (t : ℂ) := by
      simpa [mul_comm] using ((hasDerivAt_id' (t : ℂ)).const_mul a).cexp
    exact h.comp_ofReal
  have hz (t : ℝ) :
      HasDerivAt (fun x : ℝ => g x * Complex.exp (-c * (x : ℂ))) 0 t := by
    have h := (hc t).mul (hExp (-c) t)
    change HasDerivAt (fun x : ℝ => g x * Complex.exp (-c * (x : ℂ)))
      ((g t * c) * Complex.exp (-c * (t : ℂ)) +
        g t * (-c * Complex.exp (-c * (t : ℂ)))) t at h
    convert h using 1
    ring
  have hg (t : ℝ) : g t = Complex.exp (c * (t : ℂ)) := by
    have hconst := is_const_of_deriv_eq_zero (fun t => (hz t).differentiableAt)
      (fun t => (hz t).deriv) t 0
    change g t * Complex.exp (-c * (t : ℂ)) = g 0 * Complex.exp (-c * (0 : ℝ)) at hconst
    rw [hzero, Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one,
      neg_mul, Complex.exp_neg] at hconst
    exact (mul_inv_eq_iff_eq_mul₀ (Complex.exp_ne_zero _)).mp hconst |>.trans (one_mul _)
  refine ⟨c, hg, fun a ha => ?_⟩
  have h₁ : deriv g 0 = a := by
    rw [show g = fun t : ℝ => Complex.exp (a * (t : ℂ)) from funext ha, (hExp a 0).deriv]
    simp
  have h₂ : deriv g 0 = c := by simpa [hzero] using (hc 0).deriv
  exact h₁.symm.trans h₂

end Masullo
