import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace Masullo

open scoped ContDiff

/-- The Euler derivative acts on the original positive variable. -/
noncomputable def eulerDerivative (f : ℝ → ℂ) (t : ℝ) : ℂ := t • deriv f t

private theorem eulerDerivative_comp_exp (f : ℝ → ℂ) (h : DifferentiableOn ℝ f (Set.Ioi 0)) :
    eulerDerivative f ∘ Real.exp = deriv (f ∘ Real.exp) := by
  funext x
  have hd := (h (Real.exp x) (Real.exp_pos x)).differentiableAt
    (isOpen_Ioi.mem_nhds (Real.exp_pos x))
  exact (hd.hasDerivAt.scomp x (Real.hasDerivAt_exp x)).deriv.symm

/-- Lemma B.2.1.6. The Euler derivative becomes ordinary differentiation
in the logarithmic coordinate, including after any finite number of iterations. -/
theorem eulerDerivative_iterate_comp_exp (f : ℝ → ℂ) (hf : ContDiffOn ℝ ∞ f (Set.Ioi 0)) (n : ℕ) :
    (eulerDerivative^[n] f) ∘ Real.exp = iteratedDeriv n (f ∘ Real.exp) := by
  have hSmooth (k : ℕ) : ContDiffOn ℝ ∞ (eulerDerivative^[k] f) (Set.Ioi 0) := by
    induction k with
    | zero => exact hf
    | succ k hk =>
      rw [Function.iterate_succ_apply']
      exact contDiff_id.contDiffOn.smul (hk.deriv_of_isOpen isOpen_Ioi (by simp))
  induction n with
  | zero => simp
  | succ n hn =>
    rw [Function.iterate_succ_apply', eulerDerivative_comp_exp _ ((hSmooth n).differentiableOn (by simp)),
      hn, iteratedDeriv_succ]

end Masullo
