import CompactGroupAveraging
import SchwartzCompactApproximation
import SchwartzComplete

open Filter Function MeasureTheory Set Topology
open scoped ContDiff SchwartzMap

namespace Masullo

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [ProperSpace V]

/-- Translates of a fixed test vary continuously in the Schwartz topology. -/
theorem continuous_schwartz_compSubConst (f : 𝓢(V, ℂ)) :
    Continuous (fun a : V => SchwartzMap.compSubConstCLM ℂ a f) := by
  let F (a : V) := SchwartzMap.compSubConstCLM ℂ a f
  apply continuous_iff_continuousAt.mpr
  intro a₀
  change Tendsto F (𝓝 a₀) (𝓝 (F a₀))
  apply ((schwartz_withSeminorms ℂ V ℂ).tendsto_nhds _ _).mpr
  rintro ⟨k, n⟩ ε hε
  let K := ‖a₀‖ + 1
  let C := (2 : ℝ) ^ k * SchwartzMap.seminorm ℂ (k+1) n f
  let M := 2*K + 1 + 4*C/ε
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hnear : ∀ᶠ a in 𝓝 a₀, ‖a‖ < ‖a₀‖ + 1 :=
    continuous_norm.continuousAt.eventually_lt continuousAt_const (lt_add_one _)
  have hD (a x : V) : iteratedFDeriv ℝ n (F a : V → ℂ) x =
      iteratedFDeriv ℝ n f (x - a) := by
    change iteratedFDeriv ℝ n (fun y => f (y - a)) x = _
    simpa only [sub_eq_add_neg] using iteratedFDeriv_comp_add_right n (-a) x
  have hn : (n : ℕ∞ω) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
  have hdiff (a x : V) :
      iteratedFDeriv ℝ n ((F a - F a₀ : 𝓢(V, ℂ)) : V → ℂ) x =
        iteratedFDeriv ℝ n f (x - a) - iteratedFDeriv ℝ n f (x - a₀) := by
    change iteratedFDeriv ℝ n ((F a : V → ℂ) - (F a₀ : V → ℂ)) x = _
    have he : iteratedFDeriv ℝ n ((F a : V → ℂ) - (F a₀ : V → ℂ)) x =
        iteratedFDeriv ℝ n (F a : V → ℂ) x - iteratedFDeriv ℝ n (F a₀ : V → ℂ) x :=
      iteratedFDeriv_sub_apply ((F a).smooth'.of_le hn).contDiffAt
        ((F a₀).smooth'.of_le hn).contDiffAt
    rw [he, hD, hD]
  let g (p : V × V) := ‖p.2‖ ^ k *
    ‖iteratedFDeriv ℝ n ((F p.1 - F a₀ : 𝓢(V, ℂ)) : V → ℂ) p.2‖
  have hg : Continuous g := by
    simp only [g, hdiff]
    have hd := f.smooth'.continuous_iteratedFDeriv hn
    exact (continuous_snd.norm.pow k).mul
      ((hd.comp (continuous_snd.sub continuous_fst)).sub
        (hd.comp (continuous_snd.sub continuous_const))).norm
  have hsmall : ∀ᶠ a in 𝓝 a₀, ∀ x ∈ Metric.closedBall (0 : V) M, g (a, x) < ε / 2 := by
    apply (isCompact_closedBall (0 : V) M).eventually_forall_of_forall_eventually
    intro x _
    have hx : g (a₀, x) < ε / 2 := by simp [g, hε]
    exact hg.continuousAt.eventually_lt continuousAt_const hx
  have htail (a x : V) (ha : ‖a‖ ≤ K) (hx : M < ‖x‖) :
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f (x - a)‖ ≤ ε / 4 := by
    have htri := norm_add_le (x-a) a
    rw [sub_add_cancel] at htri
    have hεC : 0 ≤ 4*C/ε := by positivity
    have hy : 0 < ‖x-a‖ := by
      dsimp [M, K] at hx ha
      linarith [norm_nonneg a₀]
    have hy' : K ≤ ‖x-a‖ := by dsimp [M] at hx; linarith
    have hx₂ : ‖x‖ ≤ 2 * ‖x-a‖ := by linarith
    have hbound := SchwartzMap.le_seminorm ℂ (k+1) n f (x-a)
    have hscale : C ≤ (ε/4) * ‖x-a‖ := by
      have hR : 4*C/ε ≤ ‖x-a‖ := by
        dsimp only [M] at hx
        linarith [show 0 ≤ K by dsimp [K]; positivity]
      have hR' := (div_le_iff₀ hε).mp hR
      linarith
    apply (le_of_mul_le_mul_right _ hy)
    calc
      _ ≤ (2 * ‖x-a‖)^k * ‖iteratedFDeriv ℝ n f (x-a)‖ * ‖x-a‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (norm_nonneg _) hx₂ _) (norm_nonneg _)) (norm_nonneg _)
      _ = (2:ℝ)^k * (‖x-a‖^(k+1) * ‖iteratedFDeriv ℝ n f (x-a)‖) := by
        rw [mul_pow, pow_succ]
        ring
      _ ≤ C := mul_le_mul_of_nonneg_left hbound (by positivity)
      _ ≤ _ := hscale
  filter_upwards [hnear, hsmall] with a ha hsmall'
  change SchwartzMap.seminorm ℂ k n (F a - F a₀) < ε
  refine (SchwartzMap.seminorm_le_bound ℂ k n _ (half_pos hε).le fun x => ?_).trans_lt
    (half_lt_self hε)
  by_cases hx : x ∈ Metric.closedBall (0 : V) M
  · exact (hsmall' x hx).le
  · have hMx : M < ‖x‖ := lt_of_not_ge (fun h => hx (mem_closedBall_zero_iff.mpr h))
    rw [hdiff]
    calc
      _ ≤ ‖x‖^k * (‖iteratedFDeriv ℝ n f (x-a)‖ +
          ‖iteratedFDeriv ℝ n f (x-a₀)‖) :=
        mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by positivity)
      _ ≤ ε/2 := by
        rw [mul_add]
        linarith [htail a x ha.le hMx, htail a₀ x (le_add_of_nonneg_right zero_le_one) hMx]

/-- Compactly supported Schwartz tests give the same continuous orbits. -/
theorem continuous_schwartz_compSubConst_of_hasCompactSupport
    (f : 𝓢(V, ℂ)) (_hf : HasCompactSupport f) :
    Continuous (fun a : V => SchwartzMap.compSubConstCLM ℂ a f) :=
  continuous_schwartz_compSubConst f

/-- Convolution of two compact Schwartz tests can be paired with a
continuous functional by integrating translates of either test. -/
theorem exists_schwartz_compactConvolution [MeasurableSpace V] [BorelSpace V]
    (μ : Measure V) [IsFiniteMeasureOnCompacts μ] [μ.IsAddLeftInvariant] [μ.IsNegInvariant]
    (f g : 𝓢(V, ℂ)) (hf : HasCompactSupport f) (hg : HasCompactSupport g) :
    ∃ h : 𝓢(V, ℂ), ∀ T : StrongDual ℂ 𝓢(V, ℂ),
      T h = (∫ x, f x * T (SchwartzMap.compSubConstCLM ℂ x g) ∂μ) ∧
      T h = (∫ x, g x * T (SchwartzMap.compSubConstCLM ℂ x f) ∂μ) := by
  letI : CompleteSpace 𝓢(V, ℂ) := completeSpace_schwartzMap
  let A (x : V) := f x • SchwartzMap.compSubConstCLM ℂ x g
  let B (x : V) := g x • SchwartzMap.compSubConstCLM ℂ x f
  obtain ⟨p, hp⟩ := exists_positivePettisIntegral_of_hasCompactSupport μ
    (f.continuous.smul (continuous_schwartz_compSubConst_of_hasCompactSupport g hg)) hf.smul_right
  obtain ⟨q, hq⟩ := exists_positivePettisIntegral_of_hasCompactSupport μ
    (g.continuous.smul (continuous_schwartz_compSubConst_of_hasCompactSupport f hf)) hg.smul_right
  change HasPositivePettisIntegral μ A p at hp
  change HasPositivePettisIntegral μ B q at hq
  have he : p = q := by
    ext y
    let ε := (BoundedContinuousFunction.evalCLM ℂ y).comp
      (SchwartzMap.toBoundedContinuousFunctionCLM ℂ V ℂ)
    change ε p = ε q
    rw [(hp ε).2, (hq ε).2]
    change (∫ x, f x * g (y - x) ∂μ) = ∫ x, g x * f (y - x) ∂μ
    calc
      _ = ∫ x, g (y - x) * f (y - (y - x)) ∂μ := by
        simp only [sub_sub_cancel, mul_comm]
      _ = _ := integral_sub_left_eq_self (fun x => g x * f (y - x)) μ y
  refine ⟨p, fun T => ⟨?_, ?_⟩⟩
  · simpa only [A, map_smul, smul_eq_mul] using (hp T).2
  · simpa only [he, B, map_smul, smul_eq_mul] using (hq T).2

end
end Masullo
