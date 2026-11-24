import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Analysis.Normed.Group.Tannery

open Filter Topology
open scoped ArithmeticFunction.vonMangoldt

namespace Masullo

/-- Prime-power coefficients for the finite-place sum over ℚ. -/
noncomputable def finiteCoefficient {q : ℕ} (χ : DirichletCharacter ℂ q) (n : ℕ) : ℂ :=
  χ n * (ArithmeticFunction.vonMangoldt n : ℂ)

/-- The subtracted finite-place limit over ℚ. The Euler sum with positive
prime-power coefficients is the difference of negative logarithmic derivatives. -/
theorem finitePlaceCutoff_tendsto {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s r : ℂ} (hs : 1 < s.re) (hr : 1 < r.re)
    (cutoff : ℕ → ℕ → ℝ)
    (hcut : ∀ k n, cutoff k n ∈ Set.Icc (0 : ℝ) 1)
    (hlim : ∀ n > 1, Tendsto (fun k => cutoff k n) atTop (𝓝 1)) :
    Tendsto (fun k => ∑' n, (cutoff k n : ℂ) *
      (LSeries.term (finiteCoefficient χ) s n - LSeries.term (finiteCoefficient χ) r n))
      atTop (𝓝 ((-deriv χ.LFunction s / χ.LFunction s) -
        (-deriv χ.LFunction r / χ.LFunction r))) := by
  let f := finiteCoefficient χ
  have hsum (v : ℂ) (hv : 1 < v.re) : Summable (fun n => ‖LSeries.term f v n‖) :=
    (DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ hv).norm
  have hdom : Summable (fun n => ‖LSeries.term f s n‖ + ‖LSeries.term f r n‖) :=
    (hsum s hs).add (hsum r hr)
  have hterms := tendsto_tsum_of_dominated_convergence hdom
    (g := fun n => LSeries.term f s n - LSeries.term f r n)
    (f := fun k n => (cutoff k n : ℂ) * (LSeries.term f s n - LSeries.term f r n))
    (fun n => by
      by_cases hn : 1 < n
      · have h : Tendsto (fun k => (cutoff k n : ℂ)) atTop (𝓝 (1 : ℂ)) := by
          simpa only [Complex.ofReal_one] using (hlim n hn).ofReal
        simpa only [one_mul] using h.mul_const (LSeries.term f s n - LSeries.term f r n)
      · have hn' : n = 0 ∨ n = 1 := by omega
        rcases hn' with rfl | rfl
        · simp [LSeries.term_zero]
        · simp [f, finiteCoefficient])
    (Eventually.of_forall fun k n => by
      have h := hcut k n
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h.1]
      exact (mul_le_of_le_one_left (norm_nonneg _) h.2).trans (norm_sub_le _ _))
  have hEval (v : ℂ) (hv : 1 < v.re) :
      (∑' n, LSeries.term f v n) = -deriv χ.LFunction v / χ.LFunction v := by
    change LSeries (fun n => χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) v = _
    have h := DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hv
    rw [← χ.deriv_LFunction_eq_deriv_LSeries hv, ← χ.LFunction_eq_LSeries hv] at h
    exact h
  rw [((hsum s hs).of_norm).tsum_sub ((hsum r hr).of_norm), hEval s hs, hEval r hr] at hterms
  exact hterms

end Masullo
