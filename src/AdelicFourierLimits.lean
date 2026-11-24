import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.Deriv.Inv

open Filter Topology

namespace Masullo

/-- At the zero frequency, the inverse action fixes the input but the
inverse modulus differentiates to minus the modulus exponent. -/
theorem scaled_fourier_at_zero_hasDerivAt (α : ℝ) (z : ℂ) :
    HasDerivAt (fun t : ℝ => (t ^ (-α : ℝ)) • z) ((-α) • z) 1 := by
  have h : HasDerivAt (fun t : ℝ => t ^ (-α : ℝ)) (-α) 1 := by
    simpa only [Real.one_rpow, mul_one] using
      (Real.hasDerivAt_rpow_const (x := 1) (p := -α) (Or.inl one_ne_zero))
  exact h.smul_const z

theorem scaled_fourier_at_zero_nonzero (α : ℝ) (z : ℂ)
    (hα : α ≠ 0) (hz : z ≠ 0) :
    deriv (fun t : ℝ => (t ^ (-α : ℝ)) • z) 1 ≠ 0 := by
  rw [(scaled_fourier_at_zero_hasDerivAt α z).deriv]
  exact smul_ne_zero (neg_ne_zero.mpr hα) hz

/-- For the positive exponential convention, reciprocating the parameter
changes the sign of the phase derivative. -/
theorem reciprocal_fourier_phase_hasDerivAt (ω : ℝ) :
    HasDerivAt (fun t : ℝ => Complex.exp ((ω * t⁻¹ : ℝ) * Complex.I))
      (Complex.exp ((ω : ℂ) * Complex.I) * (-((ω : ℂ) * Complex.I))) 1 := by
  have hi : HasDerivAt (fun t : ℝ => t⁻¹) (-1) 1 := by
    simpa using hasDerivAt_inv (one_ne_zero (α := ℝ))
  have harg : HasDerivAt (fun t : ℝ => ((ω * t⁻¹ : ℝ) : ℂ) * Complex.I)
      (-((ω : ℂ) * Complex.I)) 1 := by
    simpa [Complex.ofReal_mul, Complex.ofReal_neg, mul_neg, neg_mul] using
      (((hi.const_mul ω).ofReal_comp).mul_const Complex.I)
  have hx := (Complex.hasDerivAt_exp (((ω * (1 : ℝ)⁻¹ : ℝ) : ℂ) * Complex.I)).complexToReal_fderiv
  have h := hx.comp_hasDerivAt 1 harg
  simpa [Function.comp_def, smul_eq_mul] using h

theorem reciprocal_fourier_phase_sign_obstruction (ω : ℝ) (hω : ω ≠ 0) :
    deriv (fun t : ℝ => Complex.exp ((ω * t⁻¹ : ℝ) * Complex.I)) 1 ≠
      Complex.exp ((ω : ℂ) * Complex.I) * ((ω : ℂ) * Complex.I) := by
  rw [(reciprocal_fourier_phase_hasDerivAt ω).deriv]
  intro h
  have hc : (ω : ℂ) * Complex.I ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr hω) Complex.I_ne_zero
  have hn := mul_left_cancel₀ (Complex.exp_ne_zero _) h
  have ht : (2 : ℂ) * ((ω : ℂ) * Complex.I) = 0 := by linear_combination -hn
  exact (mul_ne_zero (by norm_num) hc) ht

end Masullo
