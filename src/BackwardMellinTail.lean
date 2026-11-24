import MellinStrip

open Complex Filter Function Set Topology
open scoped SchwartzMap ContDiff Nat

namespace Masullo

noncomputable section

/-- On the positive ray this test decays at zero at every power and
has a nonzero tail of order `t⁻¹` at infinity. -/
def backwardMellinTail (t : ℝ) : ℂ :=
  ↑(t⁻¹ * Real.exp (-t⁻¹))

private def logGammaTail (r x : ℝ) : ℂ :=
  ↑(Real.exp (-r * x - Real.exp (-x)))

private theorem logGammaTail_smooth (r : ℝ) : ContDiff ℝ ∞ (logGammaTail r) := by
  have h : ContDiff ℝ ∞ (fun x : ℝ => Real.exp (-r * x - Real.exp (-x))) := by fun_prop
  exact Complex.ofRealCLM.contDiff.comp h

private theorem logGammaTail_deriv (r : ℝ) :
    deriv (logGammaTail r) = fun x => (-r : ℂ) * logGammaTail r x + logGammaTail (r + 1) x := by
  funext x
  have h₁ : HasDerivAt (fun y : ℝ => -r * y) (-r) x :=
    ((hasDerivAt_id x).const_mul (-r)).congr_deriv (mul_one _)
  have h₂ : HasDerivAt (fun y : ℝ => Real.exp (-y)) (-Real.exp (-x)) x := by
    simpa only [id_eq, Pi.neg_apply, mul_neg_one] using ((hasDerivAt_id x).neg.exp)
  have he : HasDerivAt (fun y : ℝ => -r * y - Real.exp (-y)) (-r + Real.exp (-x)) x := by
    have hh := h₁.sub h₂
    change HasDerivAt (fun y : ℝ => -r * y - Real.exp (-y)) (-r - -Real.exp (-x)) x at hh
    rwa [sub_neg_eq_add] at hh
  have h := he.exp.ofReal_comp.deriv
  unfold logGammaTail
  rw [h]
  rw [show -(r + 1) * x - Real.exp (-x) =
      (-r * x - Real.exp (-x)) + -x by ring, Real.exp_add, Complex.ofReal_mul]
  push_cast
  ring

private theorem logGammaTail_exp_bound {r : ℝ} (x : ℝ) :
    ‖logGammaTail r x‖ ≤ Real.exp (2 * r ^ 2) * Real.exp (-r * |x|) := by
  rw [logGammaTail, Complex.norm_real, Real.norm_of_nonneg (Real.exp_nonneg _), ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx]
    linarith [sq_nonneg r, Real.exp_nonneg (-x)]
  · rw [abs_of_neg (lt_of_not_ge hx)]
    have h := Real.pow_div_factorial_le_exp (x := -x) (by linarith) 2
    norm_num at h
    nlinarith [sq_nonneg ((-x) - 2 * r)]

private theorem logGammaTail_power_bound {r : ℝ} (hr : 0 < r) (k : ℕ) (x : ℝ) :
    ‖x‖ ^ k * ‖logGammaTail r x‖ ≤ Real.exp (2 * r ^ 2) * (k ! : ℝ) / r ^ k := by
  have h := Real.pow_div_factorial_le_exp (x := r * |x|) (by positivity) k
  have h₂ : |x| ^ k ≤ (k ! : ℝ) * Real.exp (r * |x|) / r ^ k := by
    have hk : 0 < (k ! : ℝ) := by exact_mod_cast Nat.factorial_pos k
    rw [mul_pow, div_le_iff₀ hk] at h
    apply (le_div_iff₀ (by positivity : 0 < r ^ k)).mpr
    simpa only [mul_comm] using h
  rw [Real.norm_eq_abs]
  refine (mul_le_mul h₂ (logGammaTail_exp_bound (r := r) x) (norm_nonneg _) (by positivity)).trans_eq ?_
  rw [show -r * |x| = -(r * |x|) by ring, Real.exp_neg]
  field_simp

private theorem logGammaTail_schwartz_decay (k n : ℕ) :
    ∀ r : ℝ, 0 < r → ∃ B : ℝ, ∀ x, ‖x‖ ^ k * ‖iteratedDeriv n (logGammaTail r) x‖ ≤ B := by
  induction n with
  | zero =>
    intro r hr
    exact ⟨_, fun x => by simpa only [iteratedDeriv_zero] using logGammaTail_power_bound hr k x⟩
  | succ n ih =>
    intro r hr
    obtain ⟨B, hB⟩ := ih r hr
    obtain ⟨C, hC⟩ := ih (r + 1) (by positivity)
    refine ⟨‖(-r : ℂ)‖ * B + C, fun x => ?_⟩
    rw [iteratedDeriv_succ', logGammaTail_deriv]
    have hleft : ContDiffAt ℝ n (fun x => (-r : ℂ) * logGammaTail r x) x := by
      exact ((contDiff_infty.mp (contDiff_const.mul (logGammaTail_smooth r))) n).contDiffAt
    have hright : ContDiffAt ℝ n (logGammaTail (r + 1)) x :=
      (contDiff_infty.mp (logGammaTail_smooth (r + 1)) n).contDiffAt
    change ‖x‖ ^ k * ‖iteratedDeriv n
      ((fun y => (-r : ℂ) * logGammaTail r y) + logGammaTail (r + 1)) x‖ ≤ _
    rw [iteratedDeriv_add hleft hright, iteratedDeriv_const_mul_field]
    refine (mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)).trans ?_
    rw [mul_add, norm_mul, mul_left_comm (‖x‖ ^ k)]
    exact add_le_add (mul_le_mul_of_nonneg_left (hB x) (norm_nonneg _)) (hC x)

private def logGammaTailSchwartz (r : ℝ) (hr : 0 < r) : 𝓢(ℝ, ℂ) where
  toFun := logGammaTail r
  smooth' := logGammaTail_smooth r
  decay' k n := by
    simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv] using
      logGammaTail_schwartz_decay k n r hr

/-- The counterexample belongs to every backward Mellin weight. -/
theorem backwardMellinTail_weight {s : ℝ} (hs : s ≤ 0) :
    MellinSchwartzAt backwardMellinTail s := by
  have hr : 0 < 1 - s := by linarith
  apply mellinSchwartzAt_iff_positive_log.mpr
  refine ⟨logGammaTailSchwartz (1 - s) hr, funext fun x => ?_⟩
  change logGammaTail (1 - s) x = Real.exp (s * x) • backwardMellinTail (Real.exp x)
  rw [logGammaTail, backwardMellinTail, ← Real.exp_neg, ← Real.exp_add,
    Complex.real_smul, ← Complex.ofReal_mul, ← Real.exp_add]
  congr 2
  ring

/-- For this counterexample to B.2.1.4(1), agreement on the positive ray
is already incompatible with Euclidean Schwartz decay for this backward test. -/
theorem backwardMellinTail_not_euclideanSchwartz :
    ¬ ∃ f : 𝓢(ℝ, ℂ), ∀ t > 0, f t = backwardMellinTail t := by
  rintro ⟨f, hf⟩
  obtain ⟨C, hC⟩ := f.decay' 2 0
  let t : ℝ := 2 + |C| * Real.exp 1
  have ht : 1 ≤ t := by dsimp [t]; linarith [mul_nonneg (abs_nonneg C) (Real.exp_nonneg 1)]
  have ht₀ : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have h := hC t
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_zero] at h
  change ‖t‖ ^ 2 * ‖f t‖ ≤ C at h
  rw [hf t ht₀,
    backwardMellinTail, Real.norm_eq_abs, abs_of_pos ht₀, Complex.norm_real,
    Real.norm_of_nonneg (by positivity), ← mul_assoc] at h
  have hmul : t ^ 2 * t⁻¹ = t := by field_simp
  rw [hmul] at h
  have he : Real.exp (-1) ≤ Real.exp (-t⁻¹) := by
    apply Real.exp_le_exp.mpr
    exact neg_le_neg ((inv_le_one₀ ht₀).mpr ht)
  have hbound := (mul_le_mul_of_nonneg_left he ht₀.le).trans h
  have hpow : t * Real.exp (-1) = 2 * Real.exp (-1) + |C| := by
    dsimp [t]
    rw [add_mul, mul_assoc, ← Real.exp_add]
    norm_num
  linarith [Real.exp_pos (-1), le_abs_self C]

end
end Masullo
