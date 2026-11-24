import MellinCoordinates
import MellinStrip
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv

open Complex Filter Function Set Topology
open scoped SchwartzMap ContDiff

namespace Masullo

noncomputable section

/-- Reflection on the Schwartz space in logarithmic coordinates. -/
def logarithmicSchwartzReflection : 𝓢(ℝ, ℂ) ≃L[ℂ] 𝓢(ℝ, ℂ) := by
  let e := (LinearIsometryEquiv.neg ℝ : ℝ ≃ₗᵢ[ℝ] ℝ).toContinuousLinearEquiv
  let r := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e (F := ℂ)
  have h : Involutive r := by
    intro f
    ext x
    simp [r, e, SchwartzMap.compCLMOfContinuousLinearEquiv_apply]
  exact ⟨LinearEquiv.ofInvolutive r.toLinearMap h, r.continuous, r.continuous⟩

@[simp] theorem logarithmicSchwartzReflection_apply (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    logarithmicSchwartzReflection f x = f (-x) := rfl

theorem logarithmicSchwartzReflection_involutive : Involutive logarithmicSchwartzReflection := by
  intro f
  ext x
  simp

theorem mellinSchwartzAt_reflect_iff (f : ℝ → ℂ) (s : ℝ) :
    MellinSchwartzAt (mellinReflect f) s ↔ MellinSchwartzAt f (-s) := by
  constructor
  · intro h
    have hh := mellinSchwartzAt_reflect (σ := -s) (by simpa using h)
    have he : mellinReflect (mellinReflect f) = f := funext fun t => by simp [mellinReflect]
    rwa [he] at hh
  · exact mellinSchwartzAt_reflect

theorem logarithmicSchwartzReflection_norm_apply (f : 𝓢(ℝ, ℂ)) (t : ℝ) :
    logarithmicSchwartzReflection f (Real.log t) = mellinReflect (f ∘ Real.log) t := by
  simp [mellinReflect, Real.log_inv]

theorem mellinSchwartzAt_reflection_classes (f : ℝ → ℂ) :
    ((∀ s : ℝ, MellinSchwartzAt (mellinReflect f) s) ↔ ∀ s : ℝ, MellinSchwartzAt f s) ∧
    ((∀ s ≤ 0, MellinSchwartzAt (mellinReflect f) s) ↔ ∀ s ≥ 0, MellinSchwartzAt f s) := by
  constructor
  · constructor
    · intro h s
      simpa using (mellinSchwartzAt_reflect_iff f (-s)).mp (h (-s))
    · intro h s
      exact (mellinSchwartzAt_reflect_iff f s).mpr (h (-s))
  · constructor
    · intro h s hs
      simpa using (mellinSchwartzAt_reflect_iff f (-s)).mp (h (-s) (by linarith))
    · intro h s hs
      exact (mellinSchwartzAt_reflect_iff f s).mpr (h (-s) (by linarith))


private theorem mellinSchwartzAt_congr {f g : ℝ → ℂ} (h : EqOn f g (Ioi 0)) (s : ℝ) :
    MellinSchwartzAt f s ↔ MellinSchwartzAt g s := by
  have he (x : ℝ) : f (Real.exp x) = g (Real.exp x) := h (Real.exp_pos x)
  rw [mellinSchwartzAt_iff_positive_log, mellinSchwartzAt_iff_positive_log]
  simp only [he]

private theorem mellinSchwartzAt_zero_contDiffOn {f : ℝ → ℂ} (h : MellinSchwartzAt f 0) :
    ContDiffOn ℝ ∞ f (Ioi 0) := by
  obtain ⟨g, hg⟩ := mellinSchwartzAt_iff_positive_log.mp h
  have hlog : ContDiffOn ℝ ∞ Real.log (Ioi 0) := fun x hx =>
    (Real.contDiffAt_log.mpr hx.ne').contDiffWithinAt
  apply (g.smooth'.comp_contDiffOn hlog).congr
  intro t ht
  have h := congrFun hg (Real.log t)
  change f t = g (Real.log t)
  simpa only [Function.comp_apply, zero_mul, Real.exp_zero, one_smul, Real.exp_log ht] using h.symm

/-- The Euler derivative preserves every logarithmic Schwartz weight.
The derivative of the weight contributes the subtraction of the constant
multiple of the weighted test. -/
theorem mellinSchwartzAt_eulerDerivative {f : ℝ → ℂ} {s : ℝ}
    (h : MellinSchwartzAt f s) (hf : ContDiffOn ℝ ∞ f (Ioi 0)) :
    MellinSchwartzAt (eulerDerivative f) s := by
  obtain ⟨g, hg⟩ := mellinSchwartzAt_iff_positive_log.mp h
  apply mellinSchwartzAt_iff_positive_log.mpr
  refine ⟨SchwartzMap.derivCLM ℂ ℂ g - (s : ℂ) • g, funext fun x => ?_⟩
  have hsx : HasDerivAt (fun y : ℝ => Real.exp (s * y)) (Real.exp (s * x) * s) x := by
    simpa only [id_eq, mul_one] using (((hasDerivAt_id x).const_mul s).exp)
  have hx : Real.exp x ∈ Ioi (0 : ℝ) := Real.exp_pos x
  have hfx := ((hf.differentiableOn (by simp) (Real.exp x) hx).differentiableAt
    (isOpen_Ioi.mem_nhds hx)).hasDerivAt.scomp x (Real.hasDerivAt_exp x)
  have hd := (hsx.smul hfx).deriv
  have hge : deriv g x =
      (Real.exp (s * x) * s : ℝ) • f (Real.exp x) +
        Real.exp (s * x) • (Real.exp x • deriv f (Real.exp x)) := by
    rw [hg]
    change deriv (fun y : ℝ => Real.exp (s * y) • f (Real.exp y)) x =
      Real.exp (s * x) • (Real.exp x • deriv f (Real.exp x)) +
        (Real.exp (s * x) * s : ℝ) • f (Real.exp x) at hd
    exact hd.trans (add_comm _ _)
  simp only [sub_apply, smul_apply, SchwartzMap.derivCLM_apply, hge,
    congrFun hg x, eulerDerivative, Complex.real_smul, smul_eq_mul, Complex.ofReal_mul]
  ring

/-- The same Euler operator preserves the forward, backward and two-sided
classes without any choice of weighted representative. -/
theorem mellinEuler_preserves_weight_class {f : ℝ → ℂ} (S : Set ℝ) (h0 : 0 ∈ S)
    (h : ∀ s ∈ S, MellinSchwartzAt f s) :
    ∀ s ∈ S, MellinSchwartzAt (eulerDerivative f) s :=
  fun s hs => mellinSchwartzAt_eulerDerivative (h s hs)
    (mellinSchwartzAt_zero_contDiffOn (h 0 h0))


private theorem mellinSchwartzAt_deriv {f : ℝ → ℂ} {s : ℝ} (h : MellinSchwartzAt f (s - 1))
    (hf : ContDiffOn ℝ ∞ f (Ioi 0)) : MellinSchwartzAt (deriv f) s := by
  have hD := mellinSchwartzAt_eulerDerivative h hf
  have hw := mellinSchwartzAt_weight (f := eulerDerivative f) (c := -1) (σ := s)
    (by simpa [sub_eq_add_neg] using hD)
  apply (mellinSchwartzAt_congr (f := mellinWeight (eulerDerivative f) (-1))
    (g := deriv f) ?_ s).mp hw
  intro t ht
  have h₀ : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  simp only [mellinWeight, eulerDerivative, Complex.ofReal_neg, Complex.ofReal_one, Complex.cpow_neg_one,
    Complex.real_smul, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ h₀, one_mul]

private theorem mellinSchwartzAt_iteratedDeriv_nonpos {f : ℝ → ℂ}
    (h : ∀ s ≤ 0, MellinSchwartzAt f s) (n : ℕ) :
    ∀ s ≤ 0, MellinSchwartzAt (iteratedDeriv n f) s := by
  induction n with
  | zero => simpa only [iteratedDeriv_zero] using h
  | succ n ih =>
    intro s hs
    rw [iteratedDeriv_succ]
    exact mellinSchwartzAt_deriv (ih (s - 1) (by linarith))
      (mellinSchwartzAt_zero_contDiffOn (ih 0 le_rfl))

private theorem mellinSchwartzAt_iteratedDeriv_all {f : ℝ → ℂ}
    (h : ∀ s, MellinSchwartzAt f s) (n : ℕ) : ∀ s, MellinSchwartzAt (iteratedDeriv n f) s := by
  induction n with
  | zero => simpa only [iteratedDeriv_zero] using h
  | succ n ih =>
    intro s
    rw [iteratedDeriv_succ]
    exact mellinSchwartzAt_deriv (ih (s - 1)) (mellinSchwartzAt_zero_contDiffOn (ih 0))

/-- Extension by zero on the nonpositive real half-line. -/
def positiveZeroExtension (f : ℝ → ℂ) : ℝ → ℂ :=
  (Ioi (0 : ℝ)).indicator f

private theorem mellinSchwartzAt_power_bound {f : ℝ → ℂ} {s : ℝ}
    (h : MellinSchwartzAt f s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t > 0, t ^ s * ‖f t‖ ≤ C := by
  obtain ⟨g, hg⟩ := mellinSchwartzAt_iff_positive_log.mp h
  refine ⟨SchwartzMap.seminorm ℂ 0 0 g, apply_nonneg _ _, fun t ht => ?_⟩
  have hd := SchwartzMap.le_seminorm ℂ 0 0 g (Real.log t)
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_zero, pow_zero, one_mul,
    congrFun hg (Real.log t), Real.exp_log ht, norm_smul,
    Real.norm_of_nonneg (Real.exp_nonneg _), mul_comm s (Real.log t), ← Real.rpow_def_of_pos ht] at hd
  exact hd

private theorem positiveZeroExtension_hasDerivAt {f : ℝ → ℂ}
    (hf : ContDiffOn ℝ ∞ f (Ioi 0)) (h : MellinSchwartzAt f (-2)) (t : ℝ) :
    HasDerivAt (positiveZeroExtension f) (positiveZeroExtension (deriv f) t) t := by
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · have ht' : positiveZeroExtension (deriv f) t = 0 :=
      indicator_of_notMem (show t ∉ Ioi (0 : ℝ) from not_lt_of_ge ht.le) _
    rw [ht']
    apply (hasDerivAt_const t (0 : ℂ)).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds ht] with x hx
    exact indicator_of_notMem (show x ∉ Ioi (0 : ℝ) from not_lt_of_ge (le_of_lt (show x < 0 from hx))) _
  · have hzero (g : ℝ → ℂ) : positiveZeroExtension g 0 = 0 := by
      exact indicator_of_notMem (show (0 : ℝ) ∉ Ioi 0 by simp) g
    rw [hzero, hasDerivAt_iff_tendsto]
    simp only [sub_zero, hzero, smul_zero]
    obtain ⟨C, hC, hbd⟩ := mellinSchwartzAt_power_bound h
    have hlim : Tendsto (fun x : ℝ => C * ‖x‖) (𝓝 0) (𝓝 0) := by
      simpa only [norm_zero, mul_zero] using (continuous_norm.continuousAt.tendsto.const_mul C :
        Tendsto (fun x : ℝ => C * ‖x‖) (𝓝 0) (𝓝 (C * ‖(0 : ℝ)‖)))
    apply squeeze_zero (fun x => mul_nonneg (inv_nonneg.mpr (norm_nonneg x)) (norm_nonneg _)) ?_ hlim
    intro x
    by_cases hx : 0 < x
    · have hxt : x ∈ Ioi (0 : ℝ) := hx
      have hX := hbd x hx
      rw [show (-2 : ℝ) = -(2 : ℝ) by rfl, Real.rpow_neg hx.le] at hX
      rw [show x ^ (2 : ℝ) = x ^ (2 : ℕ) from Real.rpow_natCast x 2] at hX
      have hb : ‖f x‖ ≤ C * x ^ 2 := by
        simpa only [mul_comm] using (inv_mul_le_iff₀ (sq_pos_of_pos hx)).mp hX
      rw [positiveZeroExtension, indicator_of_mem hxt, Real.norm_eq_abs, abs_of_pos hx]
      exact (mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hx.le)).trans_eq (by field_simp)
    · rw [positiveZeroExtension, indicator_of_notMem (show x ∉ Ioi (0 : ℝ) from hx),
        norm_zero, mul_zero]
      positivity
  · have ht' : positiveZeroExtension (deriv f) t = deriv f t := indicator_of_mem ht _
    rw [ht']
    have hd := (hf.differentiableOn (by simp) t ht).differentiableAt (Ioi_mem_nhds ht)
    apply hd.hasDerivAt.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds ht] with x hx
    exact indicator_of_mem hx _

private theorem positiveZeroExtension_iteratedDeriv
    {f : ℝ → ℂ} (h : ∀ s ≤ 0, MellinSchwartzAt f s) (n : ℕ) :
    iteratedDeriv n (positiveZeroExtension f) = positiveZeroExtension (iteratedDeriv n f) := by
  induction n with
  | zero => simp only [iteratedDeriv_zero]
  | succ n ih =>
    rw [iteratedDeriv_succ, ih, iteratedDeriv_succ]
    funext x
    have H := mellinSchwartzAt_iteratedDeriv_nonpos h n
    exact (positiveZeroExtension_hasDerivAt
      (mellinSchwartzAt_zero_contDiffOn (H 0 le_rfl)) (H (-2) (by norm_num)) x).deriv

/-- A backward Mellin-Schwartz test extends smoothly by zero at the
origin. The backward weights give vanishing of every ordinary derivative. -/
theorem backwardMellinSchwartz_zeroExtension_smooth {f : ℝ → ℂ}
    (h : ∀ s ≤ 0, MellinSchwartzAt f s) :
    ContDiff ℝ ∞ (positiveZeroExtension f) ∧
      ∀ n : ℕ, iteratedDeriv n (positiveZeroExtension f) 0 = 0 := by
  have hD (n : ℕ) (x : ℝ) :
      HasDerivAt (positiveZeroExtension (iteratedDeriv n f))
        (positiveZeroExtension (deriv (iteratedDeriv n f)) x) x :=
    positiveZeroExtension_hasDerivAt
      (mellinSchwartzAt_zero_contDiffOn (mellinSchwartzAt_iteratedDeriv_nonpos h n 0 le_rfl))
      (mellinSchwartzAt_iteratedDeriv_nonpos h n (-2) (by norm_num)) x
  have hC (k : ℕ) : ∀ n, ContDiff ℝ k (positiveZeroExtension (iteratedDeriv n f)) := by
    induction k with
    | zero =>
      intro n
      exact contDiff_zero.mpr (continuous_iff_continuousAt.mpr fun x => (hD n x).continuousAt)
    | succ k ih =>
      intro n
      rw [Nat.cast_succ]
      refine contDiff_succ_iff_deriv.mpr ⟨fun x => (hD n x).differentiableAt, by simp, ?_⟩
      have he : deriv (positiveZeroExtension (iteratedDeriv n f)) =
          positiveZeroExtension (iteratedDeriv (n + 1) f) := by
        rw [iteratedDeriv_succ]
        exact funext fun x => (hD n x).deriv
      rw [he]
      exact ih (n + 1)
  refine ⟨contDiff_infty.mpr fun k => by simpa only [iteratedDeriv_zero] using hC k 0, fun n => ?_⟩
  rw [positiveZeroExtension_iteratedDeriv h n, positiveZeroExtension,
    indicator_of_notMem (show (0 : ℝ) ∉ Ioi 0 by simp)]

/-- With two-sided exponential decay in the logarithmic coordinate, the
smooth extension by zero is a Euclidean Schwartz function. -/
def twoSidedMellinSchwartz_zeroExtension {f : ℝ → ℂ}
    (h : ∀ s, MellinSchwartzAt f s) : 𝓢(ℝ, ℂ) where
  toFun := positiveZeroExtension f
  smooth' := (backwardMellinSchwartz_zeroExtension_smooth (fun s _ => h s)).1
  decay' k n := by
    obtain ⟨C, hC, hbd⟩ := mellinSchwartzAt_power_bound
      (mellinSchwartzAt_iteratedDeriv_all h n k)
    refine ⟨C, fun t => ?_⟩
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,
      positiveZeroExtension_iteratedDeriv (fun s _ => h s) n]
    by_cases ht : 0 < t
    · rw [positiveZeroExtension, indicator_of_mem (show t ∈ Ioi (0 : ℝ) from ht),
        Real.norm_eq_abs, abs_of_pos ht]
      simpa only [Real.rpow_natCast] using hbd t ht
    · rw [positiveZeroExtension, indicator_of_notMem (show t ∉ Ioi (0 : ℝ) from ht),
        norm_zero, mul_zero]
      exact hC

@[simp] theorem twoSidedMellinSchwartz_zeroExtension_apply {f : ℝ → ℂ}
    (h : ∀ s, MellinSchwartzAt f s) (t : ℝ) :
    twoSidedMellinSchwartz_zeroExtension h t = positiveZeroExtension f t := rfl


end
end Masullo
