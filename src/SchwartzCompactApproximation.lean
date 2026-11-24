import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

open Filter Function Set Topology
open scoped ContDiff SchwartzMap

set_option maxHeartbeats 600000

namespace Masullo

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

private def compactCutoffBump : ContDiffBump (0 : V) := ⟨1, 2, by norm_num, by norm_num⟩

private def compactCutoffProfile (x : V) : ℂ := ((compactCutoffBump (V := V)) x : ℝ)

private theorem compactCutoffProfile_smooth :
    ContDiff ℝ ∞ (compactCutoffProfile : V → ℂ) :=
  Complex.ofRealCLM.contDiff.comp compactCutoffBump.contDiff

private theorem compactCutoffProfile_compact :
    HasCompactSupport (compactCutoffProfile : V → ℂ) :=
  compactCutoffBump.hasCompactSupport.comp_left Complex.ofReal_zero

private def compactCutoffScale (n : ℕ) : ℝ := ((n : ℝ) + 1)⁻¹

private theorem compactCutoffScale_pos (n : ℕ) : 0 < compactCutoffScale n := by
  unfold compactCutoffScale
  positivity

private theorem compactCutoffScale_le_one (n : ℕ) : compactCutoffScale n ≤ 1 := by
  unfold compactCutoffScale
  exact inv_le_one_of_one_le₀ (by linarith [Nat.cast_nonneg (α := ℝ) n])

private def compactCutoffMultiplier (n : ℕ) (x : V) : ℂ :=
  compactCutoffProfile (compactCutoffScale n • x)

private theorem compactCutoffMultiplier_growth (n : ℕ) :
    (compactCutoffMultiplier n : V → ℂ).HasTemperateGrowth :=
  (compactCutoffProfile_compact.hasTemperateGrowth compactCutoffProfile_smooth).comp (by
    fun_prop)

private theorem compactCutoffMultiplier_one (n : ℕ) {x : V} (hx : ‖x‖ < (n : ℝ) + 1) :
    compactCutoffMultiplier n x = 1 := by
  unfold compactCutoffMultiplier compactCutoffProfile
  suffices hb : (compactCutoffScale n • x) ∈ Metric.closedBall 0 (compactCutoffBump (V := V)).rIn by
    rw [compactCutoffBump.one_of_mem_closedBall hb]
    norm_num
  change dist (compactCutoffScale n • x) 0 ≤ 1
  rw [dist_zero_right, norm_smul, Real.norm_of_nonneg (compactCutoffScale_pos n).le]
  unfold compactCutoffScale
  rw [← div_eq_inv_mul]
  exact (div_le_one (by positivity)).mpr hx.le

private theorem compactCutoffMultiplier_compact (n : ℕ) :
    HasCompactSupport (compactCutoffMultiplier n : V → ℂ) :=
  compactCutoffProfile_compact.comp_homeomorph
    (Homeomorph.smulOfNeZero (compactCutoffScale n) (compactCutoffScale_pos n).ne')

private theorem compactCutoffError_bound (i : ℕ) :
    ∃ A ≥ 0, ∀ n (x : V),
      ‖iteratedFDeriv ℝ i (fun v : V ↦ compactCutoffMultiplier n v - 1) x‖ ≤ A := by
  let p : 𝓢(V, ℂ) := compactCutoffProfile_compact.toSchwartzMap compactCutoffProfile_smooth
  let h (x : V) := compactCutoffProfile x - 1
  have hdiff : ContDiff ℝ i h :=
    (compactCutoffProfile_smooth.sub contDiff_const).of_le (mod_cast le_top)
  let A := SchwartzMap.seminorm ℂ 0 i p + 1
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hb (x : V) : ‖iteratedFDeriv ℝ i h x‖ ≤ A := by
    have hp : ‖iteratedFDeriv ℝ i compactCutoffProfile x‖ ≤ SchwartzMap.seminorm ℂ 0 i p := by
      change ‖iteratedFDeriv ℝ i (p : V → ℂ) x‖ ≤ _
      simpa only [pow_zero, one_mul] using SchwartzMap.le_seminorm ℂ 0 i p x
    have h1 : ‖iteratedFDeriv ℝ i (fun _ : V ↦ (1 : ℂ)) x‖ ≤ 1 := by
      cases i with
      | zero => simp [norm_iteratedFDeriv_zero]
      | succ j => simp [iteratedFDeriv_succ_const]
    change ‖iteratedFDeriv ℝ i (fun v : V ↦ compactCutoffProfile v - 1) x‖ ≤ A
    change ‖iteratedFDeriv ℝ i ((compactCutoffProfile : V → ℂ) - (fun _ ↦ 1)) x‖ ≤ A
    rw [iteratedFDeriv_sub_apply (compactCutoffProfile_smooth.of_le (mod_cast le_top)).contDiffAt
      contDiffAt_const]
    exact (norm_sub_le _ _).trans (add_le_add hp h1)
  refine ⟨A, hA, fun n x ↦ ?_⟩
  change ‖iteratedFDeriv ℝ i (fun v ↦ h (compactCutoffScale n • v)) x‖ ≤ A
  rw [iteratedFDeriv_comp_const_smul _ hdiff, norm_smul,
    Real.norm_of_nonneg (pow_nonneg (compactCutoffScale_pos n).le _)]
  exact ((mul_le_mul_of_nonneg_left (hb _) (pow_nonneg (compactCutoffScale_pos n).le _))).trans
    (mul_le_of_le_one_left hA (pow_le_one₀ (compactCutoffScale_pos n).le (compactCutoffScale_le_one n)))

/-- Approximate a finite-dimensional Schwartz function by compactly
supported Schwartz functions in its full Schwartz topology. -/
theorem exists_schwartz_compactSupport_sequence_subset (f : 𝓢(V, ℂ)) :
    ∃ g : ℕ → 𝓢(V, ℂ), (∀ n, HasCompactSupport (g n) ∧ tsupport (g n) ⊆ tsupport f) ∧
      Tendsto g atTop (𝓝 f) := by
  let g (n : ℕ) := SchwartzMap.smulLeftCLM ℂ (compactCutoffMultiplier n) f
  have hg (n : ℕ) (x : V) : g n x = compactCutoffMultiplier n x * f x := by
    exact SchwartzMap.smulLeftCLM_apply_apply (compactCutoffMultiplier_growth n) f x
  refine ⟨g, fun n ↦ ?_, ?_⟩
  · exact ⟨(compactCutoffMultiplier_compact n).of_isClosed_subset isClosed_closure
      ((SchwartzMap.tsupport_smulLeftCLM_subset _ _).trans inter_subset_right),
      (SchwartzMap.tsupport_smulLeftCLM_subset _ _).trans inter_subset_left⟩
  · rw [(schwartz_withSeminorms ℂ V ℂ).tendsto_nhds]
    rintro ⟨k, m⟩ ε hε
    choose A hA hb using (compactCutoffError_bound (V := V))
    let C := ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * A i *
      SchwartzMap.seminorm ℂ (k + 1) (m - i) f
    have hC : 0 ≤ C := Finset.sum_nonneg fun i _ ↦
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hA i)) (apply_nonneg _ _)
    have hlimR : Tendsto (fun n : ℕ ↦ (n : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    have hlim : Tendsto (fun n : ℕ ↦ C / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hlimR
    filter_upwards [hlim (Iio_mem_nhds hε)] with n hn
    have hpos : 0 < (n : ℝ) + 1 := by positivity
    refine (SchwartzMap.seminorm_le_bound ℂ k m _ (div_nonneg hC hpos.le) fun x ↦ ?_).trans_lt hn
    have he : (⇑(g n - f) : V → ℂ) = fun y ↦ (compactCutoffMultiplier n y - 1) * f y := by
      funext y
      change g n y - f y = _
      rw [hg, sub_mul, one_mul]
    rw [he]
    by_cases hx : ‖x‖ < (n : ℝ) + 1
    · have heq : (fun y ↦ (compactCutoffMultiplier n y - 1) * f y) =ᶠ[𝓝 x] (fun _ ↦ 0) := by
        filter_upwards [continuous_norm.continuousAt (Iio_mem_nhds hx)] with y hy
        simp [compactCutoffMultiplier_one n hy]
      rw [(heq.iteratedFDeriv (𝕜 := ℝ) m).eq_of_nhds]
      simp [div_nonneg hC hpos.le]
    · have hdiff : ContDiff ℝ ∞ (fun y : V ↦ compactCutoffMultiplier n y - 1) :=
        (compactCutoffMultiplier_growth (V := V) n).1.sub
          (contDiff_const (c := (1 : ℂ)))
      have hD := norm_iteratedFDeriv_mul_le hdiff (f.smooth ⊤) x (n := m) (mod_cast le_top)
      apply (le_div_iff₀ hpos).mpr
      calc
        _ ≤ (‖x‖ ^ k * ∑ i ∈ Finset.range (m + 1),
            (m.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun y ↦ compactCutoffMultiplier n y - 1) x‖ *
              ‖iteratedFDeriv ℝ (m - i) f x‖) * ((n : ℝ) + 1) := by
          gcongr
        _ = ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) *
            ‖iteratedFDeriv ℝ i (fun y ↦ compactCutoffMultiplier n y - 1) x‖ *
              (((n : ℝ) + 1) * ‖x‖ ^ k * ‖iteratedFDeriv ℝ (m - i) f x‖) := by
          rw [Finset.mul_sum, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ ≤ C := by
          apply Finset.sum_le_sum
          intro i hi
          have hw : ((n : ℝ) + 1) * ‖x‖ ^ k ≤ ‖x‖ ^ (k + 1) := by
            rw [pow_succ']
            exact mul_le_mul_of_nonneg_right (le_of_not_gt hx) (pow_nonneg (norm_nonneg _) _)
          exact mul_le_mul
            (mul_le_mul_of_nonneg_left (hb i n x) (Nat.cast_nonneg _))
            ((mul_le_mul_of_nonneg_right hw (norm_nonneg _)).trans
              (SchwartzMap.le_seminorm ℂ (k + 1) (m - i) f x))
            (by positivity) (mul_nonneg (Nat.cast_nonneg _) (hA i))

/-- Approximate a Schwartz test by compactly supported Schwartz tests. -/
theorem exists_schwartz_compactSupport_sequence (f : 𝓢(V, ℂ)) :
    ∃ g : ℕ → 𝓢(V, ℂ), (∀ n, HasCompactSupport (g n)) ∧ Tendsto g atTop (𝓝 f) := by
  obtain ⟨g, hg, hf⟩ := exists_schwartz_compactSupport_sequence_subset f
  exact ⟨g, fun j ↦ (hg j).1, hf⟩

end

end Masullo
