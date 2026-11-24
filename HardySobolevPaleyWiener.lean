import HardySobolevLine

open Filter Function MeasureTheory Metric Set Topology
open scoped ENNReal

namespace Masullo

noncomputable section

local notation "realMeasure" => (volume : Measure ℝ)

private theorem stripSobolev_memLp_restrict_compact (a b s : ℝ) (u : StripSobolev a b s)
    {K : Set ℝ} (hK : IsCompact K) : MemLp (u : ℝ → ℂ) 2 ((realMeasure).restrict K) := by
  let r := stripSobolevAmplitude a b s
  have hr := stripSobolevAmplitude_continuous a b s
  have hpos := stripSobolevAmplitude_pos a b s
  let V := amplitudeL2Iso realMeasure r hr.measurable hpos
  let f := V u
  have hac := absolutelyContinuous_amplitudeMeasure realMeasure r hr.measurable hpos
  have huf : (u : ℝ → ℂ) =ᵐ[realMeasure] fun x => (r x)⁻¹ • f x := by
    have h := hac.ae_le (amplitudeL2Iso_symm_ae realMeasure r hr.measurable hpos f)
    rwa [V.symm_apply_apply] at h
  have hri : Continuous (fun x => (r x)⁻¹) := hr.inv₀ fun x => (hpos x).ne'
  obtain ⟨C, hC⟩ := hK.bddAbove_image hri.continuousOn
  let D := max C 0
  have hd : 0 ≤ D := le_max_right _ _
  apply (((Lp.memLp f).norm.restrict K).const_mul D).mono'
    ((Lp.aestronglyMeasurable u).mono_ac hac).restrict
  filter_upwards [ae_restrict_mem hK.measurableSet, ae_restrict_of_ae huf] with x hx hu
  rw [hu, norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (hpos x).le)]
  exact mul_le_mul_of_nonneg_right ((hC (mem_image_of_mem _ hx)).trans (le_max_left _ _)) (norm_nonneg _)

def compactMellinKernel (u : ℝ → ℂ) (z : ℂ) (x : ℝ) : ℂ :=
  u x * Complex.exp (z * (x : ℂ))

set_option maxHeartbeats 1200000 in
/-- The Mellin transform of a bounded logarithmic interval is entire and
satisfies the Cauchy–Schwarz growth bound at every complex point. The integral
form of the growth factor also covers the line of real part zero. -/
theorem boundedStripSobolev_mellin_entire_bound (a b s c : ℝ)
    (u : supportedSobolevCompletion a b s (Ioo c 0)) :
    let F := fun z : ℂ => ∫ x, compactMellinKernel u.val z x
    (∀ z, Integrable (compactMellinKernel u.val z)) ∧ Differentiable ℂ F ∧
      ∀ z, ‖F z‖ ≤ Real.sqrt (∫ x in Icc c 0, ‖u.val x‖ ^ 2) *
        Real.sqrt (∫ x in Icc c 0, Real.exp (2 * z.re * x)) := by
  let K := Icc c (0 : ℝ)
  let μ := (realMeasure).restrict K
  have hK : IsCompact K := isCompact_Icc
  have hmem := stripSobolev_memLp_restrict_compact a b s u.val hK
  letI : IsFiniteMeasure μ := ⟨by
    rw [Measure.restrict_apply_univ]
    exact hK.measure_lt_top⟩
  have hI : Integrable (u.val : ℝ → ℂ) μ := by
    rw [← memLp_one_iff_integrable]
    exact hmem.mono_exponent (by norm_num)
  have hsmul (F : ℝ → ℂ) (hF : Continuous F) :
      Integrable (fun x => u.val x * F x) μ :=
    (show IntegrableOn (u.val : ℝ → ℂ) K realMeasure from hI).mul_continuousOn hF.continuousOn hK
  have hC (z : ℂ) : Continuous (fun x : ℝ => Complex.exp (z * (x : ℂ))) := by fun_prop
  have hlocal (z : ℂ) : Integrable (compactMellinKernel u.val z) μ := hsmul _ (hC z)
  have hz : ∀ᵐ x ∂realMeasure, x ∉ K → u.val x = 0 := by
    filter_upwards [(mem_supportedSobolevCompletion_iff a b s isOpen_Ioo u.val).mp u.property] with x hx h
    exact hx fun hin => h (Ioo_subset_Icc_self hin)
  have hind (z : ℂ) :
      K.indicator (compactMellinKernel u.val z) =ᵐ[realMeasure] compactMellinKernel u.val z := by
    filter_upwards [hz] with x hx
    by_cases h : x ∈ K
    · rw [indicator_of_mem h]
    · rw [indicator_of_notMem h, compactMellinKernel, hx h, zero_mul]
  have hEq (z : ℂ) : (∫ x, compactMellinKernel u.val z x) =
      ∫ x, compactMellinKernel u.val z x ∂μ := by
    rw [← integral_indicator hK.measurableSet]
    exact integral_congr_ae (hind z).symm
  refine ⟨fun z => ((integrable_indicator_iff hK.measurableSet).mpr (hlocal z)).congr (hind z), ?_, ?_⟩
  · simp_rw [hEq]
    intro z
    have hcont : Continuous (fun p : ℂ × ℝ => ‖Complex.exp (p.1 * (p.2 : ℂ)) * (p.2 : ℂ)‖) := by
      fun_prop
    obtain ⟨C, hC'⟩ := ((isCompact_closedBall z 1).prod hK).bddAbove_image hcont.continuousOn
    let D := max C 0
    have hDer (w : ℂ) (x : ℝ) :
        HasDerivAt (fun v => compactMellinKernel u.val v x)
          (u.val x * (Complex.exp (w * (x : ℂ)) * (x : ℂ))) w := by
      simpa [compactMellinKernel, mul_comm (x : ℂ)] using
        (((hasDerivAt_id' w).mul_const (x : ℂ)).cexp).const_mul (u.val x)
    have hMeas (w : ℂ) : AEStronglyMeasurable (compactMellinKernel u.val w) μ :=
      (hlocal w).aestronglyMeasurable
    have hMeas' : AEStronglyMeasurable
        (fun x : ℝ => u.val x * (Complex.exp (z * (x : ℂ)) * (x : ℂ))) μ := by
      exact hI.aestronglyMeasurable.mul (((hC z).mul Complex.continuous_ofReal).aestronglyMeasurable)
    have hbound : ∀ᵐ x ∂μ, ∀ w ∈ ball z 1,
        ‖u.val x * (Complex.exp (w * (x : ℂ)) * (x : ℂ))‖ ≤ ‖u.val x‖ * D := by
      filter_upwards [ae_restrict_mem hK.measurableSet] with x hx w hw
      rw [norm_mul]
      have hpair : (w, x) ∈ closedBall z 1 ×ˢ K := ⟨ball_subset_closedBall hw, hx⟩
      have he : ‖Complex.exp (w * (x : ℂ)) * (x : ℂ)‖ ≤ C :=
        hC' (mem_image_of_mem _ hpair)
      exact mul_le_mul_of_nonneg_left (he.trans (le_max_left C 0)) (norm_nonneg _)
    exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (ball_mem_nhds z one_pos)
      (.of_forall hMeas) (hlocal z) hMeas' hbound (hI.norm.mul_const D)
      (.of_forall fun x w _ => hDer w x)).2.differentiableAt
  · intro z
    dsimp only
    rw [hEq]
    let q (x : ℝ) := Real.exp (z.re * x)
    have hqc : Continuous q := by dsimp [q]; fun_prop
    have hq : MemLp q 2 μ :=
      (memLp_two_iff_integrable_sq_norm hqc.aestronglyMeasurable).mpr
        (hqc.norm.pow 2).continuousOn.integrableOn_Icc
    have hh : (2 : ℝ).HolderConjugate 2 := Real.HolderConjugate.two_two
    have hH := integral_mul_norm_le_Lp_mul_Lq (μ := μ) (f := fun x => ‖u.val x‖) (g := q) hh
      (by simpa using hmem.norm) (by simpa using hq)
    calc
      _ ≤ ∫ x, ‖compactMellinKernel u.val z x‖ ∂μ := norm_integral_le_integral_norm _
      _ = ∫ x, ‖‖u.val x‖‖ * ‖q x‖ ∂μ := by
        apply integral_congr_ae
        exact .of_forall fun x => by
          simp [compactMellinKernel, q, Complex.norm_exp, Complex.mul_re, mul_comm]
      _ ≤ _ := by
        have hn (x : ℝ) : ‖q x‖ ^ (2 : ℝ) = Real.exp (2 * z.re * x) := by
          rw [Real.norm_of_nonneg (Real.exp_pos _).le, show (2 : ℝ) = (2 : ℕ) by norm_num,
            Real.rpow_natCast, ← Real.exp_nat_mul]
          push_cast
          ring_nf
        have hu (x : ℝ) : ‖‖u.val x‖‖ = ‖u.val x‖ :=
          Real.norm_of_nonneg (norm_nonneg _)
        have h2 (x : ℝ) : x ^ (2 : ℝ) = x ^ (2 : ℕ) := Real.rpow_natCast x 2
        simpa only [Real.sqrt_eq_rpow, hu, hn, h2] using hH


/-- The square of the Paley–Wiener growth factor in logarithmic coordinates. -/
theorem paleyWiener_interval_factor {c : ℝ} (hc : c ≤ 0) (r : ℝ) :
    (∫ x in Icc c 0, Real.exp (2 * r * x)) =
      if r = 0 then -c else (1 - Real.exp (2 * r * c)) / (2 * r) := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hc]
  by_cases h : r = 0
  · simp [h]
  · rw [ite_eq_right h]
    have hn : 2 * r ≠ 0 := mul_ne_zero two_ne_zero h
    have hd (x : ℝ) : HasDerivAt (fun y : ℝ => Real.exp (2 * r * y) / (2 * r))
        (Real.exp (2 * r * x)) x := by
      have h' := (((hasDerivAt_id' x).const_mul (2 * r)).exp).div_const (2 * r)
      simpa only [mul_one, mul_div_cancel_right₀ _ hn] using h'
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)]
    · rw [mul_zero, Real.exp_zero, sub_div]
    · exact (by fun_prop : Continuous (fun x : ℝ => Real.exp (2 * r * x))).intervalIntegrable _ _

end
end Masullo
