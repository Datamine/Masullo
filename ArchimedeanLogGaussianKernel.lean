import Mathlib.Analysis.SpecialFunctions.FrullaniIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Prod

open Filter MeasureTheory Set Topology

namespace Masullo

noncomputable section

/-- The exponential difference in the Gaussian representation of a logarithm. -/
def gaussianLogKernel (b t : ℝ) : ℝ :=
  t⁻¹ * (Real.exp (-t) - Real.exp (-(b * t)))

theorem gaussianLogKernel_integrableOn {b : ℝ} (hb : 0 < b) :
    IntegrableOn (gaussianLogKernel b) (Ioi 0) := by
  have hm : Measurable (gaussianLogKernel b) := by
    unfold gaussianLogKernel
    exact measurable_inv.mul (Real.continuous_exp.measurable.comp measurable_neg |>.sub
      (Real.continuous_exp.comp (continuous_const.mul continuous_id).neg).measurable)
  have hsmall : IntegrableOn (gaussianLogKernel b) (Ioc 0 1) := by
    refine (integrableOn_const (C := 1 + b) measure_Ioc_lt_top.ne).mono'
      hm.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have ht0 : 0 < t := ht.1
    have he (x : ℝ) (hx : 0 ≤ x) : |1 - Real.exp (-x)| ≤ x := by
      rw [abs_of_nonneg (sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hx)))]
      linarith [Real.add_one_le_exp (-x)]
    have hd : |Real.exp (-t) - Real.exp (-(b * t))| ≤ (1 + b) * t := by
      rw [show Real.exp (-t) - Real.exp (-(b * t)) =
        (1 - Real.exp (-(b * t))) - (1 - Real.exp (-t)) by ring]
      calc
        _ ≤ |1 - Real.exp (-(b * t))| + |1 - Real.exp (-t)| := abs_sub _ _
        _ ≤ b * t + t := add_le_add (he _ (mul_nonneg hb.le ht0.le)) (he _ ht0.le)
        _ = _ := by ring
    dsimp [gaussianLogKernel]
    rw [abs_mul, abs_of_pos (inv_pos.mpr ht0)]
    exact (mul_le_mul_of_nonneg_left hd (inv_nonneg.mpr ht0.le)).trans_eq (by
      field_simp)
  have hlarge : IntegrableOn (gaussianLogKernel b) (Ioi 1) := by
    have he : IntegrableOn (fun t : ℝ ↦ Real.exp (-(b * t))) (Ioi 1) := by
      simpa only [neg_mul] using integrableOn_exp_mul_Ioi (neg_neg_of_pos hb) 1
    refine ((integrableOn_exp_neg_Ioi 1).add he).mono' hm.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht1 : 1 ≤ t := ht.le
    have ht0 : 0 < t := zero_lt_one.trans_le ht1
    dsimp [gaussianLogKernel]
    rw [abs_mul, abs_of_pos (inv_pos.mpr ht0)]
    calc
      _ ≤ 1 * |Real.exp (-t) - Real.exp (-(b * t))| :=
        mul_le_mul_of_nonneg_right ((inv_le_one₀ ht0).mpr ht1) (abs_nonneg _)
      _ ≤ Real.exp (-t) + Real.exp (-(b * t)) := by
        simpa only [one_mul, abs_of_pos (Real.exp_pos _)] using
          abs_sub (Real.exp (-t)) (Real.exp (-(b * t)))
  rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num)]
  exact hsmall.union hlarge

/-- Frullani's formula for the exponential Gaussian kernel. -/
theorem integral_gaussianLogKernel {b : ℝ} (hb : 0 < b) :
    (∫ t in Ioi 0, gaussianLogKernel b t) = Real.log b := by
  have hc : Continuous (fun t : ℝ ↦ Real.exp (-t)) := Real.continuous_exp.comp continuous_neg
  have hz : Tendsto (fun t : ℝ ↦ Real.exp (-t)) (𝓝[>] 0) (𝓝 1) := by
    simpa only [neg_zero, Real.exp_zero] using hc.continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds (a := (0 : ℝ)) (s := Ioi 0))
  have ht : Tendsto (fun t : ℝ ↦ Real.exp (-t)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
  have hi : IntegrableOn
      (fun t : ℝ ↦ t⁻¹ • (Real.exp (-(1 * t)) - Real.exp (-(b * t)))) (Ioi 0) := by
    simp only [one_mul, smul_eq_mul]
    change IntegrableOn (gaussianLogKernel b) (Ioi 0)
    exact gaussianLogKernel_integrableOn hb
  simpa only [gaussianLogKernel, one_mul, div_one, sub_zero, smul_eq_mul, mul_one] using
    Frullani.integral_Ioi_eq (hc.locallyIntegrable.locallyIntegrableOn (Ioi 0)) zero_lt_one hb hz ht hi

/-- The absolute mass of the Gaussian kernel is the absolute logarithm. -/
theorem integral_norm_gaussianLogKernel {b : ℝ} (hb : 0 < b) :
    (∫ t in Ioi 0, ‖gaussianLogKernel b t‖) = ‖Real.log b‖ := by
  rcases le_total 1 b with h | h
  · rw [Real.norm_of_nonneg (Real.log_nonneg h)]
    calc
      _ = ∫ t in Ioi 0, gaussianLogKernel b t := by
        refine setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ Real.norm_of_nonneg ?_
        have ht0 : 0 < t := ht
        exact mul_nonneg (inv_nonneg.mpr ht0.le)
          (sub_nonneg.mpr (Real.exp_le_exp.mpr (neg_le_neg (le_mul_of_one_le_left ht0.le h))))
      _ = _ := integral_gaussianLogKernel hb
  · rw [Real.norm_of_nonpos (Real.log_nonpos hb.le h), ← integral_gaussianLogKernel hb, ← integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ Real.norm_of_nonpos ?_
    have ht0 : 0 < t := ht
    exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr ht0.le)
      (sub_nonpos.mpr (Real.exp_le_exp.mpr (neg_le_neg (mul_le_of_le_one_left ht0.le h))))

/-- A log-integrable test can be paired with the Gaussian difference by Fubini. -/
theorem integral_log_norm_smul_eq_gaussian {V : Type*} [NormedAddCommGroup V]
    [MeasurableSpace V] [BorelSpace V] {μ : Measure V} [SFinite μ]
    (h0 : ∀ᵐ x ∂μ, x ≠ 0) {g : V → ℂ} (hg : Measurable g)
    (hi : Integrable (fun x ↦ Real.log ‖x‖ • g x) μ) :
    (∫ x, Real.log ‖x‖ • g x ∂μ) = (2 : ℝ)⁻¹ •
      ∫ t in Ioi 0, ∫ x, gaussianLogKernel (‖x‖ ^ 2) t • g x ∂μ := by
  let F (x : V) (t : ℝ) := gaussianLogKernel (‖x‖ ^ 2) t • g x
  have hm : Measurable (Function.uncurry F) := by
    have ht : Measurable (Prod.snd : V × ℝ → ℝ) := measurable_snd
    have hn : Measurable (fun p : V × ℝ ↦ ‖p.1‖ ^ 2) :=
      (continuous_norm.measurable.comp measurable_fst).pow_const _
    exact (ht.inv.mul ((Real.measurable_exp.comp ht.neg).sub
      (Real.measurable_exp.comp (hn.mul ht).neg))).smul (hg.comp measurable_fst)
  have hf : Integrable (Function.uncurry F) (μ.prod (volume.restrict (Ioi 0))) := by
    refine (integrable_prod_iff hm.aestronglyMeasurable).mpr ⟨?_, ?_⟩
    · filter_upwards [h0] with x hx
      exact (gaussianLogKernel_integrableOn (sq_pos_of_pos (norm_pos_iff.mpr hx))).smul_const (g x)
    · refine (hi.norm.const_mul 2).congr ?_
      filter_upwards [h0] with x hx
      change 2 * ‖Real.log ‖x‖ • g x‖ = ∫ t in Ioi 0, ‖F x t‖
      simp only [F, norm_smul, integral_mul_const,
        integral_norm_gaussianLogKernel (sq_pos_of_pos (norm_pos_iff.mpr hx)), Real.log_pow,
        Nat.cast_ofNat, norm_mul, Real.norm_ofNat]
      ring
  rw [← integral_integral_swap hf, ← integral_smul]
  refine integral_congr_ae (h0.mono fun x hx ↦ ?_)
  change Real.log ‖x‖ • g x = (2 : ℝ)⁻¹ • ∫ t in Ioi 0, gaussianLogKernel (‖x‖ ^ 2) t • g x
  rw [integral_smul_const, integral_gaussianLogKernel (sq_pos_of_pos (norm_pos_iff.mpr hx)),
    Real.log_pow, Nat.cast_ofNat, smul_smul]
  congr 1
  ring

/-- Integrate a nonnegative kernel against a test using its known mass. -/
theorem integral_gaussianWeight_smul {V : Type*} [MeasurableSpace V]
    {μ : Measure V} [SFinite μ] {K : V → ℝ → ℝ} {g : V → ℂ} {m : V → ℝ}
    (hK : Measurable (Function.uncurry K)) (hg : Measurable g)
    (hpos : ∀ x t, t ∈ Ioi (0 : ℝ) → 0 ≤ K x t)
    (hm : ∀ᵐ x ∂μ, (∫ t in Ioi (0 : ℝ), K x t) = m x ∧ 0 < m x)
    (hgI : Integrable (fun x ↦ m x • g x) μ) :
    (∫ t in Ioi (0 : ℝ), ∫ x, K x t • g x ∂μ) = ∫ x, m x • g x ∂μ := by
  let F (x : V) (t : ℝ) := K x t • g x
  have hM : Measurable (Function.uncurry F) := hK.smul (hg.comp measurable_fst)
  have hI : Integrable (Function.uncurry F) (μ.prod (volume.restrict (Ioi 0))) := by
    refine (integrable_prod_iff hM.aestronglyMeasurable).mpr ⟨?_, ?_⟩
    · filter_upwards [hm] with x hx
      have hKx : IntegrableOn (K x) (Ioi (0 : ℝ)) := by
        by_contra h
        rw [integral_undef h] at hx
        exact hx.2.ne' hx.1.symm
      exact hKx.smul_const (g x)
    · refine hgI.norm.congr (hm.mono fun x hx ↦ ?_)
      change ‖m x • g x‖ = ∫ t in Ioi (0 : ℝ), ‖F x t‖
      rw [norm_smul, Real.norm_of_nonneg hx.2.le, ← hx.1, ← integral_mul_const]
      exact setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ by
        simp only [F, norm_smul, Real.norm_of_nonneg (hpos x t ht)]
  rw [← integral_integral_swap hI]
  exact integral_congr_ae (hm.mono fun x hx ↦ by
    change (∫ t in Ioi (0 : ℝ), K x t • g x) = m x • g x
    rw [integral_smul_const, hx.1])

end
end Masullo
