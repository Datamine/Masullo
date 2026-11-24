import RealLogFourierIdentity
import ComplexLogFourierNormalization
import Mathlib.Analysis.Distribution.TemperedDistribution

open Filter Function MeasureTheory Set Topology
open scoped FourierTransform SchwartzMap

namespace Masullo

noncomputable section

section LogDistribution

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [Nontrivial V] [MeasureSpace V] [BorelSpace V]
  [(volume : Measure V).IsAddHaarMeasure]

private theorem logNorm_integrableOn_unitBall :
    IntegrableOn (fun x : V ↦ Real.log ‖x‖) (Metric.ball 0 1) := by
  rw [integrableOn_fun_norm_addHaar (volume : Measure V) (f := Real.log)]
  have hl : IntegrableOn Real.log (Ioo (0 : ℝ) 1) := by
    exact ((intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mp
      intervalIntegral.intervalIntegrable_log').mono_set Ioo_subset_Icc_self
  refine hl.norm.mono' (by
    exact ((continuous_id.pow _).aestronglyMeasurable.smul Real.measurable_log.aestronglyMeasurable)) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
  rw [norm_smul, Real.norm_of_nonneg (pow_nonneg hr.1.le _)]
  exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ hr.1.le hr.2.le)

/-- Integration against the real logarithm of the norm is continuous on Schwartz space. -/
def archimedeanLogCLM (hI : ∀ f : 𝓢(V, ℂ), Integrable (fun x : V ↦ Real.log ‖x‖ • f x)) :
    𝓢(V, ℂ) →L[ℂ] ℂ := by
  classical
  refine SchwartzMap.mkCLMtoNormedSpace (fun f ↦ ∫ x : V, Real.log ‖x‖ • f x) ?_ ?_ ?_
  · intro f g
    simp only [add_apply, smul_add, integral_add (hI f) (hI g)]
  · intro c f
    simp only [smul_apply, RingHom.id_apply, smul_comm (Real.log _ : ℝ) c, integral_smul]
  · let B := Metric.ball (0 : V) 1
    let l := (volume : Measure V).integrablePower
    let w (x : V) := (1 + ‖x‖) ^ (-(l : ℝ))
    let W (x : V) := B.indicator (fun y : V ↦ ‖Real.log ‖y‖‖) x + (2 ^ l * 2 : ℝ) * w x
    have hw : Integrable w := Measure.integrable_pow_neg_integrablePower volume
    have hW : Integrable W :=
      ((integrable_indicator_iff measurableSet_ball).2 (logNorm_integrableOn_unitBall (V := V)).norm).add
        (hw.const_mul _)
    have hW0 (x : V) : 0 ≤ W x :=
      add_nonneg (indicator_nonneg (fun _ _ ↦ norm_nonneg _) _) (by unfold w; positivity)
    let s : Finset (ℕ × ℕ) := {(0, 0), (1 + l, 0)}
    refine ⟨s, ∫ x : V, W x, integral_nonneg hW0, fun f ↦ ?_⟩
    let M := s.sup (schwartzSeminormFamily ℂ V ℂ) f
    have hbound (k : ℕ) (hk : (k, 0) ∈ s) : SchwartzMap.seminorm ℂ k 0 f ≤ M :=
      Seminorm.le_def.mp (Finset.le_sup (f := schwartzSeminormFamily ℂ V ℂ) hk) f
    have h₀ (x : V) : ‖f x‖ ≤ M :=
      (f.norm_le_seminorm ℂ x).trans (hbound 0 (by simp [s]))
    have h₁ (x : V) : ‖x‖ ^ (1 + l) * ‖f x‖ ≤ M := by
      refine le_trans ?_ (hbound (1 + l) (by simp [s]))
      simpa only [norm_iteratedFDeriv_zero] using SchwartzMap.le_seminorm ℂ (1 + l) 0 f x
    have hM : 0 ≤ M := (norm_nonneg _).trans (h₀ 0)
    have hpoint (x : V) : ‖Real.log ‖x‖ • f x‖ ≤ W x * M := by
      rw [norm_smul]
      by_cases hx : x ∈ B
      · change ‖Real.log ‖x‖‖ * ‖f x‖ ≤
          (B.indicator (fun y : V ↦ ‖Real.log ‖y‖‖) x + (2 ^ l * 2 : ℝ) * w x) * M
        rw [indicator_of_mem hx]
        have hw0 : 0 ≤ (2 ^ l * 2 : ℝ) * w x := by unfold w; positivity
        exact (mul_le_mul_of_nonneg_left (h₀ x) (norm_nonneg _)).trans
          (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hw0) hM)
      · have hx₁ : 1 ≤ ‖x‖ := le_of_not_gt fun he ↦ hx (by simpa [B, Metric.mem_ball, dist_zero_right] using he)
        rw [Real.norm_of_nonneg (Real.log_nonneg hx₁)]
        have hlog : Real.log ‖x‖ ≤ ‖x‖ :=
          (Real.log_le_sub_one_of_pos (zero_lt_one.trans_le hx₁)).trans (sub_le_self _ zero_le_one)
        have hp := pow_mul_le_of_le_of_pow_mul_le (k := 1) (l := l)
          (norm_nonneg x) (norm_nonneg (f x)) (h₀ x) (h₁ x)
        calc
          _ ≤ ‖x‖ * ‖f x‖ := mul_le_mul_of_nonneg_right hlog (norm_nonneg _)
          _ ≤ (2 ^ l : ℝ) * (M + M) * w x := by simpa only [pow_one, w] using hp
          _ = W x * M := by
            dsimp only [W]
            rw [indicator_of_notMem hx, zero_add]
            ring
    calc
      _ ≤ ∫ x : V, ‖Real.log ‖x‖ • f x‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ x : V, W x * M := integral_mono (hI f).norm (hW.mul_const M) hpoint
      _ = _ := integral_mul_const M W

end LogDistribution

/-- The real logarithmic Fourier pairing is a tempered distribution. -/
def realLogFourierDistribution : 𝓢'(ℝ, ℂ) :=
  ContinuousLinearMap.toPointwiseConvergenceCLM _ _ _ _
    ((archimedeanLogCLM realLogSchwartz_integrable).comp
      (FourierTransform.fourierCLM ℂ 𝓢(ℝ, ℂ)))

theorem realLogFourierDistribution_apply (f : 𝓢(ℝ, ℂ)) :
    realLogFourierDistribution f = realLogFourierPairing f := rfl

/-- The logarithmic Fourier pairing for the complex trace character is tempered. -/
def complexTraceLogFourierDistribution : 𝓢'(ℂ, ℂ) :=
  ContinuousLinearMap.toPointwiseConvergenceCLM _ _ _ _
    ((2 : ℂ) • (archimedeanLogCLM complexLogSchwartz_integrable).comp
      (FourierTransform.fourierCLM ℂ 𝓢(ℂ, ℂ)) -
        ((2 * Real.log 2 : ℝ) : ℂ) • (BoundedContinuousFunction.evalCLM ℂ (0 : ℂ)).comp
          (SchwartzMap.toBoundedContinuousFunctionCLM ℂ ℂ ℂ))

theorem complexTraceLogFourierDistribution_apply (f : 𝓢(ℂ, ℂ)) :
    complexTraceLogFourierDistribution f = complexTraceLogFourierPairing f := by
  rw [complexTraceLogFourierPairing_eq_euclidean, complexEuclideanLogFourierPairing]
  change _ - (((2 * Real.log 2 : ℝ) : ℂ) * f 0) = _
  rw [Complex.real_smul]
  congr 1
  simp_rw [mul_smul, integral_smul, Complex.real_smul, Complex.ofReal_ofNat]
  rfl

/-- Corrected Proposition B.4.3.2, p. 619, including both cutoff normalizations. -/
theorem archimedeanLogFourier_cutoff_corrected :
    (∀ f : 𝓢(ℝ, ℂ),
      Tendsto (fun ε ↦ -(2 : ℝ)⁻¹ • realLogCutoff f ε -
        (Real.eulerMascheroniConstant + Real.log (2 * Real.pi)) • f 0)
        (𝓝[>] 0) (𝓝 (realLogFourierDistribution f))) ∧
    (∀ f : 𝓢(ℂ, ℂ),
      Tendsto (fun ε ↦ -((2 : ℝ) * Real.pi)⁻¹ • complexLogCutoff f ε -
        (2 * (Real.eulerMascheroniConstant + Real.log (2 * Real.pi))) • f 0)
        (𝓝[>] 0) (𝓝 (complexTraceLogFourierDistribution f))) := by
  constructor
  · intro f
    rw [realLogFourierDistribution_apply]
    exact realLogFourier_cutoff_corrected f
  · intro f
    rw [complexTraceLogFourierDistribution_apply]
    exact complexLogFourier_cutoff_corrected f

end
end Masullo
