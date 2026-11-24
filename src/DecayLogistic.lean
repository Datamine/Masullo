import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

open Function Set
open scoped ContDiff

namespace Masullo

noncomputable section

/-- The ratio of one endpoint exponential weight to the sum of the two. -/
def decayLogistic (c x : ℝ) : ℝ := (1 + Real.exp (c*x))⁻¹

theorem decayLogistic_smooth (c : ℝ) : ContDiff ℝ ∞ (decayLogistic c) := by
  unfold decayLogistic
  exact (contDiff_const.add (contDiff_const.mul contDiff_id).exp).inv
    (fun x => ne_of_gt (by positivity))

theorem decayLogistic_hasDerivAt (c x : ℝ) :
    HasDerivAt (decayLogistic c) (c * decayLogistic c x * (decayLogistic c x - 1)) x := by
  let d (t : ℝ) := 1 + Real.exp (c*t)
  have hd : HasDerivAt d (Real.exp (c*x)*c) x := by
    have h := ((Real.hasDerivAt_exp (c*x)).comp x ((hasDerivAt_id x).const_mul c)).const_add 1
    rw [mul_one] at h
    exact h
  have hn : d x ≠ 0 := ne_of_gt (by dsimp [d]; positivity)
  have hr : c * decayLogistic c x * (decayLogistic c x - 1) =
      -(d x ^ 2)⁻¹ * (Real.exp (c*x)*c) := by
    change c * (d x)⁻¹ * ((d x)⁻¹ - 1) = _
    have he : Real.exp (c*x) = d x - 1 := by dsimp [d]; ring
    rw [he]
    field_simp
    <;> ring
  rw [hr]
  exact (hasDerivAt_inv hn).comp x hd

theorem decayLogistic_mem_Icc (c x : ℝ) : decayLogistic c x ∈ Icc (0 : ℝ) 1 := by
  unfold decayLogistic
  exact ⟨by positivity, (inv_le_one₀ (by positivity)).mpr
    (le_add_of_nonneg_right (Real.exp_nonneg _))⟩

private theorem exists_iteratedDeriv_decayLogistic_polynomial (c : ℝ) (n : ℕ) :
    ∃ p : Polynomial ℝ, iteratedDeriv n (decayLogistic c) = fun x => p.eval (decayLogistic c x) := by
  induction n with
  | zero =>
      exact ⟨Polynomial.X, by simp⟩
  | succ n ih =>
      obtain ⟨p,hp⟩ := ih
      refine ⟨p.derivative * Polynomial.C c * Polynomial.X * (Polynomial.X - 1),?_⟩
      rw [iteratedDeriv_succ, hp]
      funext x
      have h := ((p.hasDerivAt (decayLogistic c x)).comp x (decayLogistic_hasDerivAt c x)).deriv
      change deriv ((fun y => p.eval y) ∘ decayLogistic c) x = _
      rw [h]
      simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_sub,
        Polynomial.eval_one]
      ring

/-- Every derivative of the logistic endpoint multiplier is bounded. -/
theorem decayLogistic_iteratedDeriv_bounded (c : ℝ) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖iteratedDeriv n (decayLogistic c) x‖ ≤ C := by
  obtain ⟨p,hp⟩ := exists_iteratedDeriv_decayLogistic_polynomial c n
  have hcont : Continuous (fun x : ℝ => p.eval x) :=
    continuous_iff_continuousAt.mpr fun x => (p.hasDerivAt x).continuousAt
  obtain ⟨C,hC⟩ := isCompact_Icc.bddAbove_image
    (f := fun x : ℝ => ‖p.eval x‖) hcont.norm.continuousOn
  have hBound (x : ℝ) : ‖iteratedDeriv n (decayLogistic c) x‖ ≤ C := by
    rw [hp]
    exact hC (mem_image_of_mem _ (decayLogistic_mem_Icc c x))
  exact ⟨C,(norm_nonneg _).trans (hBound 0),hBound⟩

end

end Masullo
