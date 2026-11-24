import HardySobolevHalfline

open Filter Function MeasureTheory Set Topology
open scoped ENNReal ContDiff

namespace Masullo

noncomputable section

set_option maxHeartbeats 600000 in
/-- On the compact base [-1,0], convergence on every interior Mellin line
can hold while the interval norm remains a nonzero constant. This already
occurs for degree zero and smooth compactly supported logarithmic tests. -/
theorem mellin_interiorSampling_strictly_weaker :
    ∃ (f : ℕ → PositiveRealExponentialDecay univ) (d : ℝ),
      0 < d ∧ (∀ n, HasCompactSupport (f n).val) ∧
      (∀ n, (hardySobolevIntervalENorm volume id (Icc (-1 : ℝ) 0) 0 (f n).val).toReal = d) ∧
      ∀ σ ∈ Ioo (-1 : ℝ) 0, Tendsto (fun n => mellinLineEnergy (f n) 0 σ) atTop (𝓝 0) := by
  let b : ContDiffBump (1 : ℝ) := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩
  let g (x : ℝ) : ℂ := b x
  have hg : HasCompactSupport g := b.hasCompactSupport.comp_left Complex.ofReal_zero
  have hgSmooth : ContDiff ℝ ∞ g := Complex.ofRealCLM.contDiff.comp b.contDiff
  let shift (n : ℕ) := Homeomorph.addRight (-(n : ℝ))
  let gₙ (n : ℕ) (x : ℝ) := g (shift n x)
  have hgₙ (n : ℕ) : HasCompactSupport (gₙ n) := hg.comp_homeomorph (shift n)
  have hgₙSmooth (n : ℕ) : ContDiff ℝ ∞ (gₙ n) := by
    exact hgSmooth.comp (by change ContDiff ℝ ∞ (fun x : ℝ => x + -(n : ℝ)); fun_prop)
  let f (n : ℕ) : PositiveRealExponentialDecay univ :=
    ⟨gₙ n, mem_logExponentialDecaySubmodule_of_hasCompactSupport univ (hgₙ n) (hgₙSmooth n)⟩
  have hpos (n : ℕ) (x : ℝ) (hx : gₙ n x ≠ 0) : (n : ℝ) ≤ x := by
    have hx' : x + -(n : ℝ) ∈ support b := by
      change b (x + -(n : ℝ)) ≠ 0
      intro h
      exact hx (by simp [gₙ, g, shift, h])
    rw [b.support_eq, Metric.mem_ball, Real.dist_eq] at hx'
    have hlo : -(1 / 2 : ℝ) < x + -(n : ℝ) - 1 := by
      simpa [b] using (abs_lt.mp hx').1
    linarith
  let e := ∫ x : ℝ, ‖g x‖ ^ 2
  have hE : 0 < e := by
    have hc : Continuous (fun x => ‖g x‖ ^ 2) := hgSmooth.continuous.norm.pow 2
    have hs : HasCompactSupport (fun x => ‖g x‖ ^ 2) :=
      hg.comp_left (g := fun y : ℂ => ‖y‖ ^ 2) (by simp)
    have hb : b 1 = 1 := b.one_of_mem_closedBall (Metric.mem_closedBall_self (by norm_num [b]))
    exact integral_pos_of_integrable_nonneg_nonzero (x := (1 : ℝ)) hc (hc.integrable_of_hasCompactSupport hs)
      (fun x => sq_nonneg ‖g x‖) (by simp [g, hb])
  have hEq (n : ℕ) : (∫ x : ℝ, ‖gₙ n x‖ ^ 2) = e :=
    (measurePreserving_add_right (volume : Measure ℝ) (-(n : ℝ))).integral_comp
      (shift n).measurableEmbedding (fun x => ‖g x‖ ^ 2)
  refine ⟨f, Real.sqrt e, Real.sqrt_pos_of_pos hE, hgₙ, ?_, ?_⟩
  · intro n
    rw [(stripSobolevTest_energy univ ⟨-1, mem_univ _⟩ ⟨0, mem_univ _⟩
        (by norm_num) 0 (f n)).2, ENNReal.toReal_ofReal (Real.sqrt_nonneg _)]
    congr 1
    rw [← hEq n]
    apply integral_congr_ae
    filter_upwards with x
    change ‖gₙ n x‖ ^ 2 * hardySobolevWeight (-1) 0 0 x = ‖gₙ n x‖ ^ 2
    by_cases hx : gₙ n x = 0
    · simp [hx]
    · have hx0 : 0 ≤ x := (Nat.cast_nonneg n).trans (hpos n x hx)
      have hb : Real.exp (2 * (-1 : ℝ) * x) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      have hw : hardySobolevWeight (-1) 0 0 x = 1 := by
        unfold hardySobolevWeight
        rw [show Real.exp (2 * (0 : ℝ) * x) = 1 by simp, max_eq_right hb]
        simp
      rw [hw, mul_one]
  · intro σ hσ
    have hs : σ < 0 := hσ.2
    have hI (n : ℕ) : Integrable (fun x : ℝ => ‖gₙ n x‖ ^ 2) := by
      have he : (fun y : ℂ => ‖y‖ ^ (2 : ℕ)) 0 = 0 := by simp
      have hcompact : HasCompactSupport (fun x : ℝ => ‖gₙ n x‖ ^ 2) := (hgₙ n).comp_left (g := fun y : ℂ => ‖y‖ ^ (2 : ℕ)) he
      exact ((hgₙSmooth n).continuous.norm.pow 2).integrable_of_hasCompactSupport hcompact
    have hb (n : ℕ) : mellinLineEnergy (f n) 0 σ ≤
        (2 * Real.pi) * (Real.exp (2 * σ * n) * e) := by
      have hLine := (mellin_iteratedDeriv_line_energy (f n) 0 σ).2
      change mellinLineEnergy (f n) 0 σ = _ at hLine
      rw [hLine]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [← hEq n, ← integral_const_mul]
      apply integral_mono_of_nonneg
        (.of_forall fun x : ℝ => by positivity) ((hI n).const_mul (Real.exp (2 * σ * n)))
      refine .of_forall fun x => ?_
      change ‖gₙ n x‖ ^ 2 * (Real.exp (2 * σ * x) * (x ^ 2) ^ (0 : ℕ)) ≤
        Real.exp (2 * σ * n) * ‖gₙ n x‖ ^ 2
      by_cases hx : gₙ n x = 0
      · simp [hx]
      · rw [pow_zero, mul_one, mul_comm]
        exact mul_le_mul_of_nonneg_right
          (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left (hpos n x hx) (by linarith))) (sq_nonneg _)
    apply squeeze_zero (fun n => mellinLineEnergy_nonneg (f n) 0 σ) hb
    have ht : Tendsto (fun n : ℕ => 2 * σ * n) atTop atBot :=
      tendsto_natCast_atTop_atTop.const_mul_atTop_of_neg (by linarith)
    simpa using ((Real.tendsto_exp_atBot.comp ht).mul_const e).const_mul (2 * Real.pi)

end
end Masullo
