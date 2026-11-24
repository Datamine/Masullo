import CompactExponentialSchwartz
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

open Filter Function Set Topology
open scoped ContDiff FourierTransform SchwartzMap

namespace Masullo

noncomputable section

private def truncationBump : ContDiffBump (0 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩

private def truncationProfile (x : ℝ) : ℂ := truncationBump x

private theorem truncationProfile_smooth : ContDiff ℝ ∞ truncationProfile :=
  Complex.ofRealCLM.contDiff.comp truncationBump.contDiff

private theorem truncationProfile_compact : HasCompactSupport truncationProfile := by
  apply truncationBump.hasCompactSupport.comp_left
  simp

private def truncationScale (N : ℕ) : ℝ := ((N : ℝ) + 1)⁻¹

private theorem truncationScale_pos (N : ℕ) : 0 < truncationScale N := by
  unfold truncationScale
  positivity

def truncationMultiplier (N : ℕ) (x : ℝ) : ℂ := truncationProfile (truncationScale N * x)

theorem truncationMultiplier_growth (N : ℕ) : (truncationMultiplier N).HasTemperateGrowth :=
  (truncationProfile_compact.hasTemperateGrowth truncationProfile_smooth).comp (by
    fun_prop)

/-- A smooth spatial truncation on the real Schwartz space. -/
def truncateSchwartz (N : ℕ) : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (truncationMultiplier N)

private theorem truncateSchwartz_apply (N : ℕ) (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    truncateSchwartz N f x = truncationMultiplier N x * f x := by
  rw [truncateSchwartz, SchwartzMap.smulLeftCLM_apply_apply (truncationMultiplier_growth N), smul_eq_mul]

theorem truncationMultiplier_one (N : ℕ) {x : ℝ} (hx : |x| < (N : ℝ) + 1) :
    truncationMultiplier N x = 1 := by
  unfold truncationMultiplier truncationProfile
  suffices hb : truncationScale N * x ∈ Metric.closedBall 0 truncationBump.rIn by
    rw [truncationBump.one_of_mem_closedBall hb]
    simp
  change dist (truncationScale N * x) 0 ≤ 1
  rw [Real.dist_eq, sub_zero, abs_mul, abs_of_pos (truncationScale_pos N)]
  unfold truncationScale
  rw [← div_eq_inv_mul]
  exact (div_le_one (by positivity)).2 hx.le

theorem truncateSchwartz_apply_zero (N : ℕ) (f : 𝓢(ℝ, ℂ)) :
    truncateSchwartz N f 0 = f 0 := by
  rw [truncateSchwartz_apply, truncationMultiplier_one N (by simp; positivity), one_mul]

theorem truncationMultiplier_zero (N : ℕ) {x : ℝ} (hx : 2 * ((N : ℝ) + 1) < |x|) :
    truncationMultiplier N x = 0 := by
  unfold truncationMultiplier truncationProfile
  rw [truncationBump.zero_of_le_dist]
  · simp
  · change 2 ≤ dist (truncationScale N * x) 0
    rw [Real.dist_eq, sub_zero, abs_mul, abs_of_pos (truncationScale_pos N)]
    unfold truncationScale
    rw [← div_eq_inv_mul]
    exact (le_div_iff₀ (by positivity)).2 hx.le

private def truncationError (x : ℝ) : ℂ := truncationProfile x - 1

private theorem truncationError_smooth : ContDiff ℝ ∞ truncationError :=
  truncationProfile_smooth.sub contDiff_const

private theorem truncationError_bound (i : ℕ) :
    ∃ A ≥ 0, ∀ x, ‖iteratedDeriv i truncationError x‖ ≤ A := by
  let g x := ‖iteratedFDeriv ℝ i truncationProfile x‖
  have hg : Continuous g := (truncationProfile_smooth.continuous_iteratedFDeriv (mod_cast le_top)).norm
  obtain ⟨y, hy⟩ := hg.exists_forall_ge_of_hasCompactSupport ((truncationProfile_compact.iteratedFDeriv _).norm)
  refine ⟨g y + ‖iteratedDeriv i (fun _ : ℝ => (1 : ℂ)) 0‖, by positivity, fun x => ?_⟩
  have hC : ContDiff ℝ i truncationProfile := truncationProfile_smooth.of_le (mod_cast le_top)
  unfold truncationError
  rw [iteratedDeriv_fun_sub hC.contDiffAt contDiffAt_const]
  refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
  · simpa [g, norm_iteratedFDeriv_eq_norm_iteratedDeriv] using hy x
  · cases i <;> simp [iteratedDeriv_const]

theorem truncationError_scaled_bound (i : ℕ) :
    ∃ A ≥ 0, ∀ N x, ‖iteratedDeriv i (fun v => truncationMultiplier N v - 1) x‖ ≤ A := by
  obtain ⟨A, hA, hb⟩ := truncationError_bound i
  refine ⟨A, hA, fun N x => ?_⟩
  change ‖iteratedDeriv i (fun v => truncationError (truncationScale N * v)) x‖ ≤ A
  have hC : ContDiff ℝ i truncationError := truncationError_smooth.of_le (mod_cast le_top)
  rw [iteratedDeriv_comp_const_smul hC, norm_smul, Real.norm_eq_abs, abs_pow,
    abs_of_pos (truncationScale_pos N)]
  have hS : truncationScale N ≤ 1 := by
    unfold truncationScale
    apply (inv_le_one₀ (by positivity)).2
    linarith [Nat.cast_nonneg (α := ℝ) N]
  refine (mul_le_mul_of_nonneg_left (hb _) (pow_nonneg (truncationScale_pos N).le _)).trans ?_
  exact mul_le_of_le_one_left hA (pow_le_one₀ (truncationScale_pos N).le hS)

theorem truncateSchwartz_tendsto (f : 𝓢(ℝ, ℂ)) :
    Tendsto (fun N : ℕ => truncateSchwartz N f) atTop (𝓝 f) := by
  rw [(schwartz_withSeminorms ℂ ℝ ℂ).tendsto_nhds]
  rintro ⟨k, n⟩ ε hε
  choose A hA hb using truncationError_scaled_bound
  let C := ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * A i *
    SchwartzMap.seminorm ℂ (k + 1) (n - i) f
  have hC : 0 ≤ C := Finset.sum_nonneg fun i _ =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hA i)) (apply_nonneg _ _)
  have hlimR : Tendsto (fun N : ℕ => (N : ℝ) + 1) atTop atTop :=
    (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
  have hlim : Tendsto (fun N : ℕ => C / ((N : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hlimR
  filter_upwards [hlim (Iio_mem_nhds hε)] with N hN
  refine lt_of_le_of_lt (SchwartzMap.seminorm_le_bound ℂ k n _ (by positivity) fun x => ?_) hN
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  have he : (⇑(truncateSchwartz N f - f) : ℝ → ℂ) =
      (fun v => truncationMultiplier N v - 1) * (f : ℝ → ℂ) := by
    funext x
    change truncateSchwartz N f x - f x = _
    rw [truncateSchwartz_apply]
    simp [sub_mul]
  rw [he]
  by_cases hx : |x| < (N : ℝ) + 1
  · have heq : ((fun v => truncationMultiplier N v - 1) * (f : ℝ → ℂ)) =ᶠ[𝓝 x] (fun _ => 0) := by
      filter_upwards [(continuous_abs.continuousAt : ContinuousAt (fun v : ℝ => |v|) x)
        (Iio_mem_nhds hx)] with y hy
      simp [truncationMultiplier_one N hy]
    rw [heq.iteratedDeriv_eq n]
    simpa [iteratedDeriv_const] using div_nonneg hC (show 0 ≤ (N : ℝ) + 1 by positivity)
  have hmul := iteratedDeriv_mul
    (((truncationMultiplier_growth N).1.sub (contDiff_const (c := (1 : ℂ)))).of_le
      (mod_cast le_top)).contDiffAt
    ((f.smooth n).contDiffAt (x := x))
  rw [hmul]
  push Not at hx
  have hp : 0 < (N : ℝ) + 1 := by positivity
  apply (le_div_iff₀ hp).2
  have hle : ‖x‖ ^ k * ‖∑ i ∈ Finset.range (n + 1),
      (n.choose i : ℂ) * iteratedDeriv i (fun v => truncationMultiplier N v - 1) x *
        iteratedDeriv (n - i) (f : ℝ → ℂ) x‖ * ((N : ℝ) + 1) ≤
      ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * A i *
        (‖x‖ ^ (k + 1) * ‖iteratedDeriv (n - i) (f : ℝ → ℂ) x‖) := by
    rw [mul_comm _ ((N : ℝ) + 1), ← mul_assoc, pow_succ, mul_comm (‖x‖ ^ k)]
    refine (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)).trans ?_
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    rw [norm_mul, norm_mul, Complex.norm_natCast]
    have h₁ : ((N : ℝ) + 1) * ‖x‖ ^ k ≤ ‖x‖ * ‖x‖ ^ k :=
      mul_le_mul_of_nonneg_right (by rwa [Real.norm_eq_abs]) (by positivity)
    have h₂ := mul_le_mul_of_nonneg_left (hb i N x) (Nat.cast_nonneg (n.choose i))
    have h₃ := mul_le_mul h₁ h₂ (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _))
      (mul_nonneg (norm_nonneg _) (pow_nonneg (norm_nonneg _) _))
    calc
      _ ≤ (‖x‖ * ‖x‖ ^ k * ((n.choose i : ℝ) * A i)) *
          ‖iteratedDeriv (n - i) (f : ℝ → ℂ) x‖ := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right h₃ (norm_nonneg _)
      _ = _ := by ring
  refine hle.trans (Finset.sum_le_sum fun i _ => ?_)
  rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  exact mul_le_mul_of_nonneg_left (SchwartzMap.le_seminorm ℂ (k + 1) (n - i) f x)
    (mul_nonneg (Nat.cast_nonneg _) (hA i))

/-- Cut off every logarithmic weight using the same smooth compactly
supported multiplier. -/
def truncateExpSchwartz (N : ℕ) (f : ExpSchwartz) : ExpSchwartz :=
  ⟨fun s => truncateSchwartz N (expSchwartzEvaluation s f), fun s x => by
    change truncateSchwartz N (expSchwartzEvaluation s f) x =
      (Real.exp (s * x) : ℂ) * truncateSchwartz N (expSchwartzEvaluation 0 f) x
    rw [truncateSchwartz_apply, truncateSchwartz_apply]
    change truncationMultiplier N x * f.val s x = _ * (truncationMultiplier N x * f.val 0 x)
    rw [f.property s x]
    ring⟩

theorem truncateSchwartz_hasCompactSupport (N : ℕ) (f : 𝓢(ℝ, ℂ)) :
    HasCompactSupport (truncateSchwartz N f) := by
  refine HasCompactSupport.intro (K := Icc (-2 * ((N : ℝ) + 1)) (2 * ((N : ℝ) + 1))) isCompact_Icc ?_
  intro x hx
  rw [truncateSchwartz_apply, truncationMultiplier_zero N]
  · simp
  · by_contra! h
    exact hx ⟨by linarith [(abs_le.mp h).1], (abs_le.mp h).2⟩

/-- Smoothly truncate the frequency spectrum of a real Schwartz function. -/
abbrev fourierWindow (f : 𝓢(ℝ, ℂ)) (n : ℕ) : 𝓢(ℝ, ℂ) :=
  𝓕⁻ (truncateSchwartz n (𝓕 f))

theorem fourierWindow_tendsto (f : 𝓢(ℝ, ℂ)) : Tendsto (fourierWindow f) atTop (𝓝 f) := by
  have h := (FourierTransform.fourierInvCLM ℂ (𝓢(ℝ, ℂ))).continuous.continuousAt.tendsto.comp
    (truncateSchwartz_tendsto (𝓕 f))
  simpa only [Function.comp_def, FourierTransform.fourierInvCLM_apply, FourierTransform.fourierInv_fourier_eq] using h

theorem fourierWindow_hasCompactSpectrum (f : 𝓢(ℝ, ℂ)) (n : ℕ) :
    HasCompactSupport ((𝓕 (fourierWindow f n) : 𝓢(ℝ, ℂ)) : ℝ → ℂ) := by
  rw [fourierWindow, FourierTransform.fourier_fourierInv_eq]
  exact truncateSchwartz_hasCompactSupport n (𝓕 f)

theorem truncateExpSchwartz_hasCompactSupport (N : ℕ) (f : ExpSchwartz) :
    HasCompactSupport (expSchwartzEvaluation 0 (truncateExpSchwartz N f)) :=
  truncateSchwartz_hasCompactSupport N (expSchwartzEvaluation 0 f)

theorem truncateExpSchwartz_tendsto (f : ExpSchwartz) :
    Tendsto (fun N : ℕ => truncateExpSchwartz N f) atTop (𝓝 f) := by
  apply tendsto_subtype_rng.mpr
  rw [tendsto_pi_nhds]
  exact fun r => truncateSchwartz_tendsto (expSchwartzEvaluation r f)

end
end Masullo
