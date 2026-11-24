import HardySobolevInverse
import HardySobolevDecomposition
import Mathlib.Analysis.Calculus.FDeriv.Analytic

open Filter Function MeasureTheory Set Topology
open scoped ENNReal

namespace Masullo

noncomputable section

local notation "planePoint" => (fun (r y : ℝ) => (r : ℂ) + (y : ℂ) * Complex.I)
local notation "ZeroProfile" b => supportedSobolevCompletion b b 0 (Ioi 0)

private theorem inverse_derivative_profile_ae {b : ℝ} (k : ℕ) (u v : ZeroProfile b)
    (h : ∀ z : ℂ, z.re < b → cutoffMellinIntegral v.val 0 z = cutoffMellinIntegral u.val k z) :
    (v.val : ℝ → ℂ) =ᵐ[volume] fun x => u.val x * (x : ℂ) ^ k := by
  let r := b - 1
  have hr : r < b := by dsimp [r]; linarith
  let P (j : ℕ) (w : ZeroProfile b) (x : ℝ) :=
    w.val x * mellinEvaluationKernel j (r : ℂ) x
  let f (x : ℝ) := P 0 v x - P k u x
  have hP (j : ℕ) (w : ZeroProfile b) : Integrable (P j w) :=
    cutoffSobolev_mellinMoment_integrable le_rfl le_rfl w (z := (r : ℂ)) hr j
  have hf : Integrable f := (hP 0 v).sub (hP k u)
  have hEval (y : ℝ) (j : ℕ) (w : ZeroProfile b) :
      (∫ t : ℝ, Complex.exp ((y : ℂ) * Complex.I * (t : ℂ)) * P j w t) =
        cutoffMellinIntegral w.val j (planePoint r y) := by
    unfold cutoffMellinIntegral
    apply integral_congr_ae
    refine .of_forall fun x => ?_
    change Complex.exp ((y : ℂ) * Complex.I * (x : ℂ)) *
      (w.val x * mellinEvaluationKernel j (r : ℂ) x) = _
    simp only [mellinEvaluationKernel, add_mul, Complex.exp_add]
    ring
  have hEq : f =ᵐ[volume] 0 := by
    apply integrable_logFourier_ae_zero hf
    intro y
    let q (x : ℝ) := Complex.exp ((y : ℂ) * Complex.I * (x : ℂ))
    have hq : Continuous q := by dsimp [q]; fun_prop
    have hq1 : ∀ x : ℝ, ‖q x‖ ≤ 1 := fun x => by
      simp [q, Complex.norm_exp, Complex.mul_re, Complex.mul_im]
    have hi (j : ℕ) (w : ZeroProfile b) : Integrable (fun x => q x * P j w x) :=
      (hP j w).bdd_mul hq.aestronglyMeasurable (.of_forall hq1)
    change (∫ x : ℝ, q x * (P 0 v x - P k u x)) = 0
    simp_rw [mul_sub]
    rw [integral_sub (hi 0 v) (hi k u), hEval y 0 v, hEval y k u, h]
    · exact sub_self _
    · simpa [Complex.mul_re] using hr
  filter_upwards [hEq] with x hx
  have hcancel : v.val x * Complex.exp ((r : ℂ) * (x : ℂ)) =
      (u.val x * (x : ℂ) ^ k) * Complex.exp ((r : ℂ) * (x : ℂ)) := by
    change P 0 v x - P k u x = 0 at hx
    have he := sub_eq_zero.mp hx
    simpa only [P, mellinEvaluationKernel, pow_zero, mul_one, mul_assoc, mul_comm ((x : ℂ) ^ k)]
      using he
  exact mul_right_cancel₀ (Complex.exp_ne_zero _) hcancel

private theorem promote_zeroProfile {b : ℝ} (N : ℕ) (u v : ZeroProfile b)
    (hv : (v.val : ℝ → ℂ) =ᵐ[volume] fun x => u.val x * (x : ℂ) ^ N) :
    ∃ w : supportedSobolevCompletion b b (2 * (N : ℝ)) (Ioi 0),
      (w.val : ℝ → ℂ) =ᵐ[volume] (u.val : ℝ → ℂ) := by
  let q (s x : ℝ) := stripSobolevAmplitude b b s x
  let s := 2 * (N : ℝ)
  have hq (s : ℝ) : Measurable (q s) := (stripSobolevAmplitude_continuous b b s).measurable
  have hu0 (w : ZeroProfile b) : AEStronglyMeasurable (w.val : ℝ → ℂ) volume :=
    (Lp.aestronglyMeasurable w.val).mono_ac
      (absolutelyContinuous_amplitudeMeasure volume (q 0) (hq 0) (stripSobolevAmplitude_pos b b 0))
  have hL (w : ZeroProfile b) : MemLp (fun x => q 0 x • w.val x) 2 volume :=
    (memLp_amplitudeMeasure_iff volume (q 0) (hq 0) (hu0 w)).mp (Lp.memLp w.val)
  have hM : AEStronglyMeasurable (fun x => q s x • u.val x) volume :=
    (hq s).aestronglyMeasurable.smul (hu0 u)
  have hI (w : ZeroProfile b) : Integrable (fun x => ‖q 0 x • w.val x‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm (hL w).aestronglyMeasurable).mp (hL w)
  have hpow (x : ℝ) : (1 + x ^ 2) ^ N ≤ (2 : ℝ) ^ N * (1 + (x ^ 2) ^ N) := by
    let M := max 1 (x ^ 2)
    have hM₁ : 1 ≤ M := le_max_left _ _
    have hM₂ : x ^ 2 ≤ M := le_max_right _ _
    have hM : M ^ N ≤ 1 + (x ^ 2) ^ N := by
      by_cases hx : x ^ 2 ≤ 1
      · simp [M, max_eq_left hx]
        positivity
      · simp [M, max_eq_right (le_of_not_ge hx)]
    calc
      _ ≤ (2 * M) ^ N := pow_le_pow_left₀ (by positivity) (by linarith) _
      _ = (2 : ℝ) ^ N * M ^ N := mul_pow ..
      _ ≤ _ := mul_le_mul_of_nonneg_left hM (by positivity)
  have hqs (x : ℝ) : q s x ^ 2 = q 0 x ^ 2 * (1 + x ^ 2) ^ N := by
    simp only [q, stripSobolevAmplitude_sq le_rfl, hardySobolevWeight, max_self,
      zero_div, Real.rpow_zero, mul_one]
    rw [show s / 2 = (N : ℝ) by dsimp [s]; ring, Real.rpow_natCast]
  have hweighted : MemLp (u.val : ℝ → ℂ) 2 (stripMeasure b b s) := by
    apply (memLp_amplitudeMeasure_iff volume (q s) (hq s) (hu0 u)).mpr
    apply (memLp_two_iff_integrable_sq_norm hM).mpr
    apply (((hI u).add (hI v)).const_mul ((2 : ℝ) ^ N)).mono' (hM.norm.pow 2)
    filter_upwards [hv] with x hx
    change v.val x = u.val x * (x : ℂ) ^ N at hx
    have hn : (‖(x : ℂ)‖ ^ N) ^ 2 = (x ^ 2) ^ N := by
      rw [← pow_mul, Nat.mul_comm, pow_mul, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    change ‖‖q s x • u.val x‖ ^ 2‖ ≤
      (2 : ℝ) ^ N * (‖q 0 x • u.val x‖ ^ 2 + ‖q 0 x • v.val x‖ ^ 2)
    simp only [Real.norm_of_nonneg (sq_nonneg _), norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
      hqs, hx, norm_mul, norm_pow, hn, abs_of_nonneg (show 0 ≤ 1 + x ^ 2 by positivity)]
    calc
      _ = (q 0 x ^ 2 * ‖u.val x‖ ^ 2) * (1 + x ^ 2) ^ N := by ring
      _ ≤ (q 0 x ^ 2 * ‖u.val x‖ ^ 2) * ((2 : ℝ) ^ N * (1 + (x ^ 2) ^ N)) :=
        mul_le_mul_of_nonneg_left (hpow x) (by positivity)
      _ = _ := by ring
  let W := hweighted.toLp (u.val : ℝ → ℂ)
  have hW : (W : ℝ → ℂ) =ᵐ[volume] (u.val : ℝ → ℂ) :=
    (absolutelyContinuous_amplitudeMeasure volume (q s) (hq s)
      (stripSobolevAmplitude_pos b b s)).ae_le hweighted.coeFn_toLp
  refine ⟨⟨W, (mem_supportedSobolevCompletion_iff b b s isOpen_Ioi W).mpr ?_⟩, hW⟩
  filter_upwards [hW, (mem_supportedSobolevCompletion_iff b b 0 isOpen_Ioi u.val).mp u.property]
    with x h₁ h₂ hx
  rw [h₁, h₂ hx]

/-- Surjectivity of the scalar left-half-plane Hardy–Sobolev Mellin transform
in every degree (2N), with the usual uniform bounds on all derivatives. -/
theorem exists_cutoffMellinIntegral_of_leftHardySobolev {F : ℂ → ℂ} {b : ℝ} {N : ℕ}
    (hF : DifferentiableOn ℂ F (Complex.re ⁻¹' Iio b))
    (hL : UniformMellinLineBound (Iio b) N F) :
    ∃ u : supportedSobolevCompletion b b (2 * (N : ℝ)) (Ioi 0),
      ∀ z : ℂ, z.re < b → F z = cutoffMellinIntegral u.val 0 z := by
  have hb : IsOpen (Complex.re ⁻¹' Iio b) := isOpen_Iio.preimage Complex.continuous_re
  have hm (k : ℕ) (hk : k ≤ N) :
      ∃ v : ZeroProfile b, ∀ z : ℂ, z.re < b →
        iteratedDeriv k F z = cutoffMellinIntegral v.val 0 z := by
    obtain ⟨C, hC⟩ := hL k hk
    have hdiff : DifferentiableOn ℂ (iteratedDeriv k F) (Complex.re ⁻¹' Iio b) := by
      rw [iteratedDeriv_eq_iterate]
      exact ((hF.analyticOnNhd hb).iterated_deriv k).differentiableOn
    apply exists_cutoffMellinIntegral_of_uniform_leftL2 hdiff (A := C)
    intro r hr
    have he (y : ℝ) : planePoint r y = (⟨r, y⟩ : ℂ) := by
      apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
    simpa only [he] using hC r hr
  obtain ⟨u, hu⟩ := hm 0 (Nat.zero_le N)
  obtain ⟨v, hv⟩ := hm N le_rfl
  have he (z : ℂ) (hz : z.re < b) : cutoffMellinIntegral v.val 0 z =
      cutoffMellinIntegral u.val N z := by
    have hfg : F =ᶠ[𝓝 z] cutoffMellinIntegral u.val 0 :=
      (show ∀ᶠ w in 𝓝 z, w ∈ Complex.re ⁻¹' Iio b from hb.mem_nhds hz).mono
        fun w hw => hu w hw
    rw [← hv z hz, hfg.iteratedDeriv_eq, iteratedDeriv_cutoffMellinIntegral le_rfl le_rfl u N hz]
  obtain ⟨w, hw⟩ := promote_zeroProfile N u v (inverse_derivative_profile_ae N u v he)
  refine ⟨w, fun z hz => (hu z hz).trans ?_⟩
  unfold cutoffMellinIntegral
  exact integral_congr_ae (hw.symm.mono fun x hx => congrArg (fun c : ℂ => c * mellinEvaluationKernel 0 z x) hx)

end
end Masullo
