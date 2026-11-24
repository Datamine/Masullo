import ComplexSchwartzPointJets
import Mathlib.Analysis.Calculus.FDeriv.Pow

open Filter Function Set Topology
open scoped ContDiff SchwartzMap

namespace Masullo

noncomputable section

private abbrev S := 𝓢(ℂ, ℂ)

private def monomial (a b : ℕ) (z : ℂ) : ℂ := z ^ a * Complex.conjCLE z ^ b

private theorem monomial_smooth (a b : ℕ) : ContDiff ℝ ∞ (monomial a b) :=
  (contDiff_id.pow a).mul (Complex.conjCLE.contDiff.pow b)

private theorem fderiv_monomial_scaled (c : ℂ) (a b : ℕ) (x v : ℂ) :
    fderiv ℝ (fun z ↦ c * monomial a b z) x v =
      c * ((a : ℂ) * monomial (a-1) b x * v +
        (b : ℂ) * monomial a (b-1) x * Complex.conjCLE v) := by
  have h₁ : DifferentiableAt ℝ (fun z : ℂ ↦ z ^ a) x :=
    differentiableAt_fun_id.pow a
  have h₂ : DifferentiableAt ℝ (fun z : ℂ ↦ Complex.conjCLE z ^ b) x :=
    Complex.conjCLE.differentiable.differentiableAt.pow b
  have h₃ : DifferentiableAt ℝ (monomial a b) x := h₁.mul h₂
  have hc : fderiv ℝ (⇑Complex.conjCLE) x = Complex.conjCLE.toContinuousLinearMap :=
    Complex.conjCLE.toContinuousLinearMap.fderiv
  rw [fderiv_const_mul h₃, smul_apply]
  change c * fderiv ℝ (fun z : ℂ ↦ z ^ a * Complex.conjCLE z ^ b) x v = _
  rw [fderiv_fun_mul h₁ h₂, add_apply, smul_apply, smul_apply,
    fderiv_fun_pow a differentiableAt_fun_id,
    fderiv_fun_pow b Complex.conjCLE.differentiable.differentiableAt,
    fderiv_fun_id, hc]
  simp only [smul_apply, smul_eq_mul, nsmul_eq_mul, ContinuousLinearMap.id_apply,
    ContinuousLinearEquiv.coe_coe, monomial]
  ring

/-- Evaluation formula for the Schwartz Wirtinger derivative in z. -/
theorem complexWirtingerZ_apply (f : S) (z : ℂ) :
    complexWirtingerZ f z =
      (1 / 2 : ℂ) * (fderiv ℝ (f : ℂ → ℂ) z 1 -
        Complex.I * fderiv ℝ (f : ℂ → ℂ) z Complex.I) := rfl

/-- Evaluation formula for the Schwartz Wirtinger derivative in conjugate z. -/
theorem complexWirtingerBar_apply (f : S) (z : ℂ) :
    complexWirtingerBar f z =
      (1 / 2 : ℂ) * (fderiv ℝ (f : ℂ → ℂ) z 1 +
        Complex.I * fderiv ℝ (f : ℂ → ℂ) z Complex.I) := rfl

private theorem wirtingerZ_monomial_germ (f : S) (c : ℂ) (a b : ℕ)
    (hf : (f : ℂ → ℂ) =ᶠ[𝓝 0] fun z ↦ c * monomial a b z) :
    (complexWirtingerZ f : ℂ → ℂ) =ᶠ[𝓝 0] fun z ↦ (c * a) * monomial (a-1) b z := by
  filter_upwards [hf.fderiv (𝕜 := ℝ)] with z hz
  rw [complexWirtingerZ_apply, hz, fderiv_monomial_scaled, fderiv_monomial_scaled,
    Complex.conjCLE_apply, Complex.conjCLE_apply, map_one, Complex.conj_I]
  linear_combination (c * ((a : ℂ) * monomial (a - 1) b z -
    (b : ℂ) * monomial a (b - 1) z) / (-2)) * Complex.I_mul_I

private theorem wirtingerBar_monomial_germ (f : S) (c : ℂ) (a b : ℕ)
    (hf : (f : ℂ → ℂ) =ᶠ[𝓝 0] fun z ↦ c * monomial a b z) :
    (complexWirtingerBar f : ℂ → ℂ) =ᶠ[𝓝 0] fun z ↦ (c * b) * monomial a (b-1) z := by
  filter_upwards [hf.fderiv (𝕜 := ℝ)] with z hz
  rw [complexWirtingerBar_apply, hz, fderiv_monomial_scaled, fderiv_monomial_scaled,
    Complex.conjCLE_apply, Complex.conjCLE_apply, map_one, Complex.conj_I]
  linear_combination (c * ((a : ℂ) * monomial (a - 1) b z -
    (b : ℂ) * monomial a (b - 1) z) / 2) * Complex.I_mul_I

private theorem wirtingerBar_pow_monomial_germ (f : S) (a b : ℕ)
    (hf : (f : ℂ → ℂ) =ᶠ[𝓝 0] fun z ↦ 1 * monomial a b z) (k : ℕ) :
    ((((complexWirtingerBar ^ k) f : S)) : ℂ → ℂ) =ᶠ[𝓝 0]
      fun z ↦ (b.descFactorial k : ℂ) * monomial a (b-k) z := by
  induction k with
  | zero => simpa using hf
  | succ k ih =>
    rw [pow_succ']
    change (complexWirtingerBar ((complexWirtingerBar ^ k) f) : ℂ → ℂ) =ᶠ[𝓝 0] _
    have h := wirtingerBar_monomial_germ ((complexWirtingerBar ^ k) f)
      (b.descFactorial k) a (b-k) ih
    rw [Nat.descFactorial_succ, Nat.cast_mul, show b - (k+1) = b-k-1 by omega, mul_comm]
    exact h

private theorem wirtingerZ_pow_monomial_germ (f : S) (c : ℂ) (a b : ℕ)
    (hf : (f : ℂ → ℂ) =ᶠ[𝓝 0] fun z ↦ c * monomial a b z) (k : ℕ) :
    (((complexWirtingerZ ^ k) f : S) : ℂ → ℂ) =ᶠ[𝓝 0]
      fun z ↦ (c * (a.descFactorial k : ℂ)) * monomial (a-k) b z := by
  induction k with
  | zero => simpa using hf
  | succ k ih =>
    rw [pow_succ']
    change (complexWirtingerZ ((complexWirtingerZ ^ k) f) : ℂ → ℂ) =ᶠ[𝓝 0] _
    rw [Nat.descFactorial_succ, Nat.cast_mul, show a - (k+1) = a-k-1 by omega]
    convert wirtingerZ_monomial_germ ((complexWirtingerZ ^ k) f)
      (c * a.descFactorial k) (a-k) b ih using 2
    ring

/-- Cutoff complex monomials interpolate the individual Wirtinger
coordinates at zero. The factorial normalization makes the interpolation
diagonal with ones on the diagonal. -/
theorem exists_complexSchwartz_single_pointJet (a b : ℕ) :
    ∃ f : S, ∀ k l, complexSchwartzPointJet k l f = if k = a ∧ l = b then 1 else 0 := by
  let χ : ContDiffBump (0 : ℂ) := ⟨1/2, 1, by norm_num, by norm_num⟩
  let p : ℂ → ℂ := fun z ↦ (χ z : ℂ) * monomial a b z
  have hs : tsupport p ⊆ Metric.closedBall 0 1 :=
    tsupport_mul_subset_left.trans
      ((tsupport_comp_subset Complex.ofReal_zero χ).trans (by rw [χ.tsupport_eq]))
  have hcompact : HasCompactSupport p :=
    (isCompact_closedBall 0 1).of_isClosed_subset (isClosed_tsupport _) hs
  let φ := hcompact.toSchwartzMap ((Complex.ofRealCLM.contDiff.comp χ.contDiff).mul
    (monomial_smooth a b))
  have hloc : (φ : ℂ → ℂ) =ᶠ[𝓝 0] fun z ↦ 1 * monomial a b z := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1/2)] with z hz
    change (χ z : ℂ) * monomial a b z = 1 * monomial a b z
    rw [χ.one_of_mem_closedBall (Metric.ball_subset_closedBall hz), Complex.ofReal_one]
  have he (k l : ℕ) : complexSchwartzPointJet k l φ =
      (b.descFactorial l : ℂ) * (a.descFactorial k : ℂ) * monomial (a-k) (b-l) 0 := by
    exact (wirtingerZ_pow_monomial_germ ((complexWirtingerBar ^ l) φ)
      (b.descFactorial l) a (b-l) (wirtingerBar_pow_monomial_germ φ a b hloc l) k).eq_of_nhds
  refine ⟨(((a.factorial : ℂ) * (b.factorial : ℂ))⁻¹) • φ, fun k l ↦ ?_⟩
  rw [map_smul, smul_eq_mul, he]
  by_cases ha : k = a
  · subst k
    by_cases hb : l = b
    · subst l
      simp only [true_and, Nat.descFactorial_self, Nat.sub_self, monomial, pow_zero, mul_one]
      rw [mul_comm (b.factorial : ℂ) (a.factorial : ℂ)]
      exact inv_mul_cancel₀ (mul_ne_zero (by exact_mod_cast Nat.factorial_ne_zero a)
        (by exact_mod_cast Nat.factorial_ne_zero b))
    · rcases lt_or_gt_of_ne hb with hl | hl
      · have hpos : b-l ≠ 0 := by omega
        simp [hb, monomial, zero_pow hpos]
      · simp [hb, Nat.descFactorial_of_lt hl]
  · rcases lt_or_gt_of_ne ha with hk | hk
    · have hpos : a-k ≠ 0 := by omega
      simp [ha, monomial, zero_pow hpos]
    · simp [ha, Nat.descFactorial_of_lt hk]

end
end Masullo
