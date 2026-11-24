import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension

open Filter Function Set Topology
open scoped ContDiff SchwartzMap

namespace Masullo

noncomputable section

variable {V P : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [ProperSpace V]
  [TopologicalSpace P]

/-- Pullback of a fixed Schwartz function varies continuously in a family
of real linear coordinates with continuous forward and inverse operators. -/
theorem continuous_schwartz_linearPullback (A : P → V ≃L[ℝ] V)
    (hA : Continuous (fun p ↦ (A p).toContinuousLinearMap))
    (hAi : Continuous (fun p ↦ (A p).symm.toContinuousLinearMap))
    (f : 𝓢(V, ℂ)) :
    Continuous (fun p ↦ SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (A p) f) := by
  let F (p : P) := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (A p) f
  apply continuous_iff_continuousAt.mpr
  intro p₀
  change Tendsto F (𝓝 p₀) (𝓝 (F p₀))
  apply ((schwartz_withSeminorms ℂ V ℂ).tendsto_nhds _ _).mpr
  rintro ⟨k, n⟩ ε hε
  let M := 1 + ‖(A p₀).toContinuousLinearMap‖ + ‖(A p₀).symm.toContinuousLinearMap‖
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hA₀ : ‖(A p₀).toContinuousLinearMap‖ < M := by
    dsimp [M]
    linarith [norm_nonneg (A p₀).symm.toContinuousLinearMap]
  have hAi₀ : ‖(A p₀).symm.toContinuousLinearMap‖ < M := by
    dsimp [M]
    linarith [norm_nonneg (A p₀).toContinuousLinearMap]
  have hnear : ∀ᶠ p in 𝓝 p₀,
      ‖(A p).toContinuousLinearMap‖ < M ∧ ‖(A p).symm.toContinuousLinearMap‖ < M :=
    (hA.norm.continuousAt.eventually_lt continuousAt_const hA₀).and
      (hAi.norm.continuousAt.eventually_lt continuousAt_const hAi₀)
  have hD (p : P) (x : V) :
      iteratedFDeriv ℝ n (F p : V → ℂ) x =
        (iteratedFDeriv ℝ n f (A p x)).compContinuousLinearMap
          (fun _ ↦ (A p).toContinuousLinearMap) :=
    (A p).toContinuousLinearMap.iteratedFDeriv_comp_right f.smooth' x
      (WithTop.coe_le_coe.mpr le_top)
  let C := (M ^ (k + 1) * M ^ n) * SchwartzMap.seminorm ℂ (k + 1) n f
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have htail (p : P) (hp : ‖(A p).toContinuousLinearMap‖ ≤ M)
      (hpi : ‖(A p).symm.toContinuousLinearMap‖ ≤ M) (x : V) :
      ‖x‖ ^ (k + 1) * ‖iteratedFDeriv ℝ n (F p : V → ℂ) x‖ ≤ C := by
    have hx : ‖x‖ ≤ M * ‖A p x‖ := by
      have h := (A p).symm.toContinuousLinearMap.le_opNorm (A p x)
      change ‖(A p).symm (A p x)‖ ≤ _ at h
      rw [ContinuousLinearEquiv.symm_apply_apply] at h
      exact h.trans (mul_le_mul_of_nonneg_right hpi (norm_nonneg _))
    rw [hD]
    have hder := (iteratedFDeriv ℝ n f (A p x)).norm_compContinuousLinearMap_le
      (fun _ ↦ (A p).toContinuousLinearMap)
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hder
    calc
      _ ≤ (M * ‖A p x‖) ^ (k + 1) *
            (‖iteratedFDeriv ℝ n f (A p x)‖ * M ^ n) :=
        mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hx _) (hder.trans
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hp _) (norm_nonneg _)))
          (norm_nonneg _) (by positivity)
      _ = (M ^ (k + 1) * M ^ n) *
            (‖A p x‖ ^ (k + 1) * ‖iteratedFDeriv ℝ n f (A p x)‖) := by rw [mul_pow]; ring
      _ ≤ C := mul_le_mul_of_nonneg_left (SchwartzMap.le_seminorm ℂ _ _ f _) (by positivity)
  let R := 1 + (2 * C) / (ε / 2)
  have hR : 0 < R := by
    dsimp [R]
    positivity
  have hcD : Continuous (fun z : P × V ↦ iteratedFDeriv ℝ n (F z.1 : V → ℂ) z.2) := by
    simp only [hD]
    let L := ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear
      ℝ (fun _ : Fin n ↦ V) (fun _ : Fin n ↦ V) ℂ
    have hL : Continuous (fun z : P × V ↦ L (fun _ ↦ (A z.1).toContinuousLinearMap)) :=
      L.cont.comp (continuous_pi fun _ ↦ hA.comp continuous_fst)
    have hfx : Continuous (fun z : P × V ↦ iteratedFDeriv ℝ n f (A z.1 z.2)) := by
      apply (f.smooth'.continuous_iteratedFDeriv (WithTop.coe_le_coe.mpr le_top)).comp
      exact (hA.comp continuous_fst).clm_apply continuous_snd
    exact hL.clm_apply hfx
  have hdiff (p : P) (x : V) :
      iteratedFDeriv ℝ n ((F p - F p₀ : 𝓢(V, ℂ)) : V → ℂ) x =
        iteratedFDeriv ℝ n (F p : V → ℂ) x - iteratedFDeriv ℝ n (F p₀ : V → ℂ) x := by
    have hn : (n : ℕ∞ω) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
    exact iteratedFDeriv_sub_apply ((F p).smooth'.of_le hn).contDiffAt
      ((F p₀).smooth'.of_le hn).contDiffAt
  let g (z : P × V) :=
    ‖z.2‖ ^ k * ‖iteratedFDeriv ℝ n ((F z.1 - F p₀ : 𝓢(V, ℂ)) : V → ℂ) z.2‖
  have hg : Continuous g := by
    simp only [g, hdiff]
    exact (continuous_snd.norm.pow k).mul ((hcD.sub
      (hcD.comp (continuous_const.prodMk continuous_snd))).norm)
  have hsmall : ∀ᶠ p in 𝓝 p₀, ∀ x ∈ Metric.closedBall (0 : V) R, g (p, x) < ε / 2 := by
    apply (isCompact_closedBall (0 : V) R).eventually_forall_of_forall_eventually
    intro x _
    have hx : g (p₀, x) < ε / 2 := by simp [g, hε]
    exact hg.continuousAt.eventually_lt continuousAt_const hx
  filter_upwards [hnear, hsmall] with p hp hsmall'
  change SchwartzMap.seminorm ℂ k n (F p - F p₀) < ε
  refine (SchwartzMap.seminorm_le_bound ℂ k n _ (half_pos hε).le fun x ↦ ?_).trans_lt
    (half_lt_self hε)
  by_cases hx : x ∈ Metric.closedBall (0 : V) R
  · exact (hsmall' x hx).le
  · have hRx : R < ‖x‖ := lt_of_not_ge (fun h ↦ hx (mem_closedBall_zero_iff.mpr h))
    have hpos : 0 < ‖x‖ := hR.trans hRx
    apply le_of_mul_le_mul_right (?_ : _ * ‖x‖ ≤ (ε / 2) * ‖x‖) hpos
    rw [hdiff, mul_right_comm, ← pow_succ]
    refine (mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by positivity)).trans ?_
    rw [mul_add]
    have ht := add_le_add (htail p hp.1.le hp.2.le x) (htail p₀ hA₀.le hAi₀.le x)
    refine ht.trans ?_
    have hRε : 2 * C ≤ (ε / 2) * R := by
      dsimp [R]
      rw [mul_add, mul_one, mul_div_cancel₀ _ (half_pos hε).ne']
      linarith
    exact (by linarith : C + C ≤ (ε / 2) * R).trans
      (mul_le_mul_of_nonneg_left hRx.le (half_pos hε).le)

end

end Masullo
