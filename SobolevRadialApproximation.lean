import ExponentialSchwartzCutoffs

open Filter Function MeasureTheory Set Topology
open scoped ContDiff ENNReal FourierTransform SchwartzMap

namespace Masullo

noncomputable section

/-- The radial weight controlling the translation norm and the error term
in a singleton Hardy–Sobolev strip after untwisting its abscissa. -/
def radialSobolevTailWeight (s x : ℝ) : ℝ := (1 + |x|) ^ (s / 2) + 1

private def radialMajorant (s x : ℝ) : ℝ := (1 + ‖x‖ ^ 2) ^ (s / 2)

private theorem radialMajorant_growth (s : ℝ) :
    (fun x => (radialMajorant s x : ℂ)).HasTemperateGrowth :=
  Complex.ofRealCLM.hasTemperateGrowth.comp
    (Function.hasTemperateGrowth_one_add_norm_sq_rpow ℝ (s / 2))

private def radialMajorantLp (s : ℝ) : 𝓢(ℝ, ℂ) →L[ℂ] Lp ℂ 1 (volume : Measure ℝ) :=
  (SchwartzMap.toLpCLM ℂ ℂ 1 volume).comp
    (SchwartzMap.smulLeftCLM ℂ (fun x => (radialMajorant s x : ℂ)))

private theorem radialMajorant_nonneg (s x : ℝ) : 0 ≤ radialMajorant s x :=
  Real.rpow_nonneg (by positivity) _

private theorem norm_radialMajorantSchwartz (s : ℝ) (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    ‖SchwartzMap.smulLeftCLM ℂ (fun y => (radialMajorant s y : ℂ)) f x‖ =
      ‖f x‖ * radialMajorant s x := by
  rw [SchwartzMap.smulLeftCLM_apply_apply (radialMajorant_growth s), smul_eq_mul,
    norm_mul, Complex.norm_real, Real.norm_of_nonneg (radialMajorant_nonneg s x), mul_comm]

private theorem integrable_radialMajorant (s : ℝ) (f : 𝓢(ℝ, ℂ)) :
    Integrable (fun x => ‖f x‖ * radialMajorant s x) volume :=
  ((SchwartzMap.smulLeftCLM ℂ (fun x => (radialMajorant s x : ℂ)) f).integrable
    (μ := volume)).norm.congr (.of_forall (norm_radialMajorantSchwartz s f))

private theorem radialMajorantLp_norm (s : ℝ) (f : 𝓢(ℝ, ℂ)) :
    ‖radialMajorantLp s f‖ = ∫ x, ‖f x‖ * radialMajorant s x := by
  change ‖(SchwartzMap.smulLeftCLM ℂ (fun x => (radialMajorant s x : ℂ)) f).toLp 1 volume‖ = _
  rw [SchwartzMap.norm_toLp_one]
  exact integral_congr_ae (.of_forall (norm_radialMajorantSchwartz s f))

private theorem radialSobolevTailWeight_bound (s : ℝ) (hs : 0 ≤ s) (x : ℝ) :
    radialSobolevTailWeight s x ≤ ((2 : ℝ) ^ (s / 2) + 1) * radialMajorant s x := by
  have hx : 1 + |x| ≤ 2 * (1 + ‖x‖ ^ 2) := by
    rw [Real.norm_eq_abs, sq_abs]
    nlinarith [sq_nonneg (|x| - 1), sq_abs x, abs_nonneg x]
  have hbase : 0 ≤ 1 + ‖x‖ ^ 2 := by positivity
  have hr := Real.rpow_le_rpow (show 0 ≤ 1 + |x| by positivity) hx
    (div_nonneg hs (by norm_num : (0 : ℝ) ≤ 2))
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hbase] at hr
  have hb : 1 ≤ radialMajorant s x :=
    Real.one_le_rpow (by nlinarith [sq_nonneg ‖x‖]) (div_nonneg hs (by norm_num))
  unfold radialSobolevTailWeight
  rw [add_mul, one_mul]
  exact add_le_add hr hb

/-- Real Schwartz profiles have integrable weighted absolute value at every
nonnegative Sobolev order. -/
theorem integrable_radialSobolevTailWeight (s : ℝ) (hs : 0 ≤ s) (f : 𝓢(ℝ, ℂ)) :
    Integrable (fun x => ‖f x‖ * radialSobolevTailWeight s x) volume := by
  let C := (2 : ℝ) ^ (s / 2) + 1
  have hi := integrable_radialMajorant s f
  have hc : Continuous (radialSobolevTailWeight s) := by
    have hbase : Continuous (fun x : ℝ => (1 : ℝ) + |x|) := continuous_const.add continuous_abs
    exact (hbase.rpow_const (fun x => Or.inl (show 1 + |x| ≠ 0 by positivity))).add continuous_const
  apply (hi.const_mul C).mono' (f.continuous.norm.mul hc).aestronglyMeasurable
  refine .of_forall fun x => ?_
  have hnonneg : 0 ≤ radialSobolevTailWeight s x := by unfold radialSobolevTailWeight; positivity
  change ‖‖f x‖ * radialSobolevTailWeight s x‖ ≤ C * (‖f x‖ * radialMajorant s x)
  rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) hnonneg), mul_left_comm C]
  exact mul_le_mul_of_nonneg_left (radialSobolevTailWeight_bound s hs x) (norm_nonneg _)

private theorem radialSobolevTailWeight_integral_le (s : ℝ) (hs : 0 ≤ s) (f : 𝓢(ℝ, ℂ)) :
    (∫ x, ‖f x‖ * radialSobolevTailWeight s x) ≤
      ((2 : ℝ) ^ (s / 2) + 1) * ‖radialMajorantLp s f‖ := by
  rw [radialMajorantLp_norm, ← integral_const_mul]
  apply integral_mono_of_nonneg
  · exact .of_forall fun x => mul_nonneg (norm_nonneg _) (by unfold radialSobolevTailWeight; positivity)
  · exact (integrable_radialMajorant s f).const_mul _
  · exact .of_forall fun x => by
      change ‖f x‖ * radialSobolevTailWeight s x ≤ ((2 : ℝ) ^ (s / 2) + 1) * (‖f x‖ * radialMajorant s x)
      rw [mul_left_comm ((2 : ℝ) ^ (s / 2) + 1)]
      exact mul_le_mul_of_nonneg_left (radialSobolevTailWeight_bound s hs x) (norm_nonneg _)

private theorem exists_fourierWindow_weighted_error_lt (s : ℝ) (hs : 0 ≤ s) (f : 𝓢(ℝ, ℂ))
    {ε : ℝ} (hε : 0 < ε) : ∃ n : ℕ,
    (∫ x, ‖fourierWindow f n x - f x‖ * radialSobolevTailWeight s x) < ε := by
  have ht := ((radialMajorantLp s).continuous.tendsto f).comp (fourierWindow_tendsto f)
  rw [Metric.tendsto_nhds] at ht
  let C := (2 : ℝ) ^ (s / 2) + 1
  have hC : 0 < C := by dsimp [C]; positivity
  obtain ⟨n, hn⟩ := (ht (ε / C) (div_pos hε hC)).exists
  rw [Function.comp_apply, dist_eq_norm, ← map_sub] at hn
  refine ⟨n, (radialSobolevTailWeight_integral_le s hs (fourierWindow f n - f)).trans_lt ?_⟩
  rwa [mul_comm, ← lt_div_iff₀ hC]

private theorem fourierWindow_integral (f : 𝓢(ℝ, ℂ)) (n : ℕ) :
    (∫ x, fourierWindow f n x) = ∫ x, f x := by
  have hzero (p : 𝓢(ℝ, ℂ)) : (𝓕 p) 0 = ∫ x, p x := by
    rw [SchwartzMap.fourier_coe, Real.fourier_real_eq_integral_exp_smul]
    simp
  rw [← hzero (fourierWindow f n), ← hzero f, fourierWindow,
    FourierTransform.fourier_fourierInv_eq, truncateSchwartz_apply_zero]

private theorem exists_radialSchwartz_mollifier {δ : ℝ} (hδ : 0 < δ) :
    ∃ f : 𝓢(ℝ, ℂ), support (f : ℝ → ℂ) ⊆ Metric.ball 0 δ ∧
      (∫ x, f x) = 1 ∧ (∫ x, ‖f x‖) = 1 := by
  let bump : ContDiffBump (0 : ℝ) := ⟨δ / 2, δ, by positivity, by linarith⟩
  let p : 𝓢(ℝ, ℂ) := (bump.hasCompactSupport.comp_left Complex.ofReal_zero).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp bump.contDiff)
  have hp (x : ℝ) : p x = (bump x : ℂ) := rfl
  have hb : bump 0 = 1 := bump.one_of_mem_closedBall (Metric.mem_closedBall_self bump.rIn_pos.le)
  let a := ∫ x, bump x
  have ha : 0 < a := bump.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    bump.hasCompactSupport (fun _ => bump.nonneg) (by rw [hb]; norm_num)
  let f : 𝓢(ℝ, ℂ) := (a⁻¹ : ℝ) • p
  have hf (x : ℝ) : f x = ((a⁻¹ * bump x : ℝ) : ℂ) := by
    change (a⁻¹ : ℝ) • p x = _
    rw [hp, Complex.real_smul, Complex.ofReal_mul]
  have hi : (∫ x, a⁻¹ * bump x) = 1 := by
    rw [integral_const_mul, inv_mul_cancel₀ ha.ne']
  refine ⟨f, ?_, ?_, ?_⟩
  · intro x hx
    rw [← bump.support_eq]
    intro h
    exact hx (by rw [hf, h, mul_zero, Complex.ofReal_zero])
  · simp_rw [hf, integral_complex_ofReal, hi, Complex.ofReal_one]
  · simpa only [hf, Complex.norm_real, Real.norm_of_nonneg (mul_nonneg (inv_nonneg.mpr ha.le) bump.nonneg)] using hi

/-- Real log-coordinate kernels with exact mass one, compact Fourier
spectrum, nearly unit L¹ mass, and arbitrarily small weighted tails
outside a prescribed neighborhood of the identity. -/
theorem exists_bandlimited_radialSobolev_kernel (s : ℝ) (hs : 0 ≤ s) {δ ε : ℝ}
    (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ φ : 𝓢(ℝ, ℂ), HasCompactSupport ((𝓕 φ : 𝓢(ℝ, ℂ)) : ℝ → ℂ) ∧
      (∫ x, φ x) = 1 ∧ (∫ x, ‖φ x‖) < 1 + ε ∧
      (∫ x in (Metric.ball (0 : ℝ) δ)ᶜ, ‖φ x‖ * radialSobolevTailWeight s x) < ε := by
  obtain ⟨f, hf, hm, hn⟩ := exists_radialSchwartz_mollifier hδ
  obtain ⟨n, he⟩ := exists_fourierWindow_weighted_error_lt s hs f hε
  let φ := fourierWindow f n
  let d := φ - f
  let D (x : ℝ) := ‖d x‖ * radialSobolevTailWeight s x
  have hD : Integrable D volume := integrable_radialSobolevTailWeight s hs d
  have hD0 (x : ℝ) : 0 ≤ D x := by dsimp [D, radialSobolevTailWeight]; positivity
  have herr : (∫ x, D x) < ε := he
  refine ⟨φ, fourierWindow_hasCompactSpectrum f n, (fourierWindow_integral f n).trans hm, ?_, ?_⟩
  · calc
      (∫ x, ‖φ x‖) ≤ ∫ x, D x + ‖f x‖ := by
        apply integral_mono φ.integrable.norm (hD.add f.integrable.norm)
        intro x
        have h1 : 1 ≤ radialSobolevTailWeight s x := by
          unfold radialSobolevTailWeight
          exact le_add_of_nonneg_left (Real.rpow_nonneg (by positivity) _)
        have hle : ‖φ x - f x‖ ≤ D x := by
          rw [show ‖φ x - f x‖ = ‖d x‖ from rfl]
          exact le_mul_of_one_le_right (norm_nonneg _) h1
        calc
          ‖φ x‖ = ‖(φ x - f x) + f x‖ := by rw [sub_add_cancel]
          _ ≤ _ := (norm_add_le _ _).trans (add_le_add_left hle _)
      _ = (∫ x, D x) + 1 := by rw [integral_add hD f.integrable.norm, hn]
      _ < 1 + ε := by linarith
  · let U := Metric.ball (0 : ℝ) δ
    have hEq : (fun x => ‖φ x‖ * radialSobolevTailWeight s x) =ᵐ[volume.restrict Uᶜ] D := by
      filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet.compl] with x hx
      have hz : f x = 0 := by by_contra h; exact hx (hf h)
      change _ = ‖φ x - f x‖ * radialSobolevTailWeight s x
      rw [hz, sub_zero]
    exact ((integral_congr_ae hEq).trans_le (setIntegral_le_integral hD (.of_forall hD0))).trans_lt herr

end

end Masullo
