import PeriodicFourierBasis
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Fourier.PoissonSummation

open AddCircle Filter Function MeasureTheory Set Topology
open scoped ContDiff FourierTransform SchwartzMap

namespace Masullo

noncomputable section

variable (d : ℝ) [Fact (0 < d)]

private theorem schwartzPeriod_pos : 0 < d := Fact.out

private def scaleSchwartz : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 d (schwartzPeriod_pos d).ne'))

private theorem scaleSchwartz_apply (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    scaleSchwartz d f x = f (d * x) := by
  simp [scaleSchwartz, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, mul_comm]

private theorem fourierMode_unit (m : ℤ) (x : ℝ) :
    (periodicFourierMode d m).val x = fourier m ((x / d : ℝ) : AddCircle (1 : ℝ)) := by
  rw [periodicFourierMode_apply, fourier_coe_apply]
  congr 1
  unfold periodicFrequency
  push_cast
  ring

private theorem schwartzPeriodization_fourier (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    integerPeriodization d f x =
      ∑' m : ℤ, (𝓕 (scaleSchwartz d f)) m * (periodicFourierMode d m).val x := by
  rw [integerPeriodization]
  have hs := (scaleSchwartz d f).tsum_eq_tsum_fourier (x / d)
  simp_rw [scaleSchwartz_apply] at hs
  have he (m : ℤ) : d * (x / d + m) = x + d * m := by
    field_simp [(schwartzPeriod_pos d).ne']
  simpa only [he, fourierMode_unit] using hs

private def sampledDerivative (k : ℕ) : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) :=
  (SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => (2 * Real.pi * Complex.I * (x : ℂ) / d) ^ k)).comp
    ((SchwartzMap.fourierTransformCLM ℂ).comp (scaleSchwartz d))

private theorem sampledDerivative_apply (k : ℕ) (f : 𝓢(ℝ, ℂ)) (m : ℤ) :
    sampledDerivative d k f m = periodicFrequency d m ^ k * (𝓕 (scaleSchwartz d f)) m := by
  have h : (fun x : ℝ => (2 * Real.pi * Complex.I * (x : ℂ) / d) ^ k).HasTemperateGrowth := by
    simp only [div_eq_mul_inv]
    fun_prop
  simp [sampledDerivative, SchwartzMap.smulLeftCLM_apply_apply h, smul_eq_mul, periodicFrequency]

private def samplingWeight (m : ℤ) : ℝ := (if m = 0 then 1 else 0) + 1 / (m : ℝ) ^ 2

private theorem samplingWeight_summable : Summable samplingWeight := by
  apply Summable.add
  · exact (hasSum_ite_eq (0 : ℤ) (1 : ℝ)).summable
  · exact Real.summable_one_div_int_pow.mpr (by decide : 1 < (2 : ℕ))

private theorem schwartzIntegerSample_bound (f : 𝓢(ℝ, ℂ)) (m : ℤ) :
    ‖f m‖ ≤ (SchwartzMap.seminorm ℂ 0 0 f + SchwartzMap.seminorm ℂ 2 0 f) * samplingWeight m := by
  have h₀ := SchwartzMap.norm_le_seminorm ℂ f (m : ℝ)
  have h₂ := SchwartzMap.norm_pow_mul_le_seminorm ℂ f 2 (m : ℝ)
  by_cases hm : m = 0
  · subst m
    simpa [samplingWeight] using h₀.trans (le_add_of_nonneg_right (apply_nonneg _ _))
  · simp only [samplingWeight, if_neg hm, zero_add, mul_one_div]
    have hp : 0 < (m : ℝ) ^ 2 := sq_pos_of_ne_zero (Int.cast_ne_zero.mpr hm)
    apply (le_div_iff₀ hp).2
    rw [Real.norm_eq_abs, sq_abs] at h₂
    exact (by simpa [mul_comm] using h₂ : ‖f (m : ℝ)‖ * (m : ℝ) ^ 2 ≤ _).trans
      (le_add_of_nonneg_left (apply_nonneg _ _))

private def fourierPeriodizationTerm (f : 𝓢(ℝ, ℂ)) (m : ℤ) (x : ℝ) : ℂ :=
  (𝓕 (scaleSchwartz d f)) m * (periodicFourierMode d m).val x

private theorem fourierPeriodizationTerm_smooth (f : 𝓢(ℝ, ℂ)) (m : ℤ) :
    ContDiff ℝ ∞ (fourierPeriodizationTerm d f m) :=
  contDiff_const.mul (periodicFourierMode d m).property.1

private theorem fourierPeriodizationTerm_iterated (f : 𝓢(ℝ, ℂ)) (m : ℤ) (k : ℕ) (x : ℝ) :
    iteratedDeriv k (fourierPeriodizationTerm d f m) x =
      sampledDerivative d k f m * (periodicFourierMode d m).val x := by
  unfold fourierPeriodizationTerm
  rw [iteratedDeriv_const_mul_field, periodicFourierMode_iteratedDeriv,
    sampledDerivative_apply, mul_left_comm, ← mul_assoc]

private theorem fourierPeriodizationTerm_bound (f : 𝓢(ℝ, ℂ)) (k : ℕ) (m : ℤ) (x : ℝ) :
    ‖iteratedFDeriv ℝ k (fourierPeriodizationTerm d f m) x‖ ≤ ‖sampledDerivative d k f m‖ := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, fourierPeriodizationTerm_iterated,
    norm_mul, periodicFourierMode_circle, fourier_apply, Circle.norm_coe, mul_one]

private theorem sampledDerivative_summable (f : 𝓢(ℝ, ℂ)) (k : ℕ) :
    Summable fun m : ℤ => ‖sampledDerivative d k f m‖ :=
  (samplingWeight_summable.mul_left _).of_nonneg_of_le (fun _ => norm_nonneg _)
    (schwartzIntegerSample_bound (sampledDerivative d k f))

/-- Schwartz periodization is smooth, by Poisson summation and uniform
summability of the differentiated Fourier series. -/
theorem schwartzIntegerPeriodization_smooth (f : 𝓢(ℝ, ℂ)) :
    ContDiff ℝ ∞ (integerPeriodization d f) := by
  rw [show integerPeriodization d f = (fun x => ∑' m, fourierPeriodizationTerm d f m x) from
    funext (schwartzPeriodization_fourier d f)]
  exact contDiff_tsum (fourierPeriodizationTerm_smooth d f)
    (fun k _ => sampledDerivative_summable d f k)
    (fun k m x _ => fourierPeriodizationTerm_bound d f k m x)

theorem schwartzIntegerTranslate_summable (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    Summable (fun m : ℤ => f (x + d * m)) := by
  let g := scaleSchwartz d (f.compSubConstCLM ℂ (-x))
  have hs : Summable fun m : ℤ => ‖g m‖ :=
    (samplingWeight_summable.mul_left _).of_nonneg_of_le (fun _ => norm_nonneg _)
      (schwartzIntegerSample_bound g)
  apply (hs.of_norm).congr
  intro m
  simp [g, scaleSchwartz_apply, add_comm]

private def schwartzPeriodizationLM : 𝓢(ℝ, ℂ) →ₗ[ℂ] SmoothPeriodic d where
  toFun f := ⟨integerPeriodization d f, schwartzIntegerPeriodization_smooth d f,
    integerPeriodization_periodic d f⟩
  map_add' f g := by
    apply Subtype.ext
    funext x
    exact (schwartzIntegerTranslate_summable d f x).tsum_add
      (schwartzIntegerTranslate_summable d g x)
  map_smul' c f := by
    apply Subtype.ext
    funext x
    exact tsum_mul_left

private theorem schwartzPeriodization_derivativeBound (f : 𝓢(ℝ, ℂ)) (k : ℕ) :
    ‖periodicDerivativeLM d k (schwartzPeriodizationLM d f)‖ ≤
      (SchwartzMap.seminorm ℂ 0 0 (sampledDerivative d k f) +
        SchwartzMap.seminorm ℂ 2 0 (sampledDerivative d k f)) * ∑' m, samplingWeight m := by
  let g := sampledDerivative d k f
  let C := (SchwartzMap.seminorm ℂ 0 0 g + SchwartzMap.seminorm ℂ 2 0 g)
  have hs := (samplingWeight_summable.mul_left C)
  have hm : Summable fun m : ℤ => ‖g m‖ := sampledDerivative_summable d f k
  have hC : 0 ≤ C * ∑' m, samplingWeight m := by
    apply mul_nonneg (add_nonneg (apply_nonneg _ _) (apply_nonneg _ _))
    apply tsum_nonneg
    intro m
    unfold samplingWeight
    split <;> positivity
  apply (ContinuousMap.norm_le _ hC).mpr
  intro x
  change ‖iteratedDeriv k (integerPeriodization d f) x‖ ≤ _
  rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  rw [show integerPeriodization d f = (fun x => ∑' m, fourierPeriodizationTerm d f m x) from
    funext (schwartzPeriodization_fourier d f)]
  rw [iteratedFDeriv_tsum_apply (f := fourierPeriodizationTerm d f)
    (v := fun k m => ‖sampledDerivative d k f m‖)
    (fourierPeriodizationTerm_smooth d f)
    (fun k _ => sampledDerivative_summable d f k)
    (fun k m x _ => fourierPeriodizationTerm_bound d f k m x) (by simp)]
  refine (norm_tsum_le_tsum_norm (hm.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun m => fourierPeriodizationTerm_bound d f k m x))).trans ?_
  rw [← tsum_mul_left]
  exact (hm.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun m => fourierPeriodizationTerm_bound d f k m x)).tsum_le_tsum
    (fun m => (fourierPeriodizationTerm_bound d f k m x).trans (schwartzIntegerSample_bound g m)) hs

/-- The ordinary Schwartz orbit sum is continuous for the smooth topology of
all uniform derivatives on a fundamental interval. -/
def schwartzPeriodizationCLM : 𝓢(ℝ, ℂ) →L[ℂ] SmoothPeriodic d where
  toLinearMap := schwartzPeriodizationLM d
  cont := by
    have hW := smoothPeriodic_withDerivativeSeminorms d
    letI : IsTopologicalAddGroup (SmoothPeriodic d) := hW.topologicalAddGroup
    apply continuous_of_continuousAt_zero (schwartzPeriodizationLM d)
    change Tendsto (schwartzPeriodizationLM d) (𝓝 0) (𝓝 ((schwartzPeriodizationLM d) 0))
    rw [map_zero, hW.tendsto_nhds]
    intro i ε hε
    have h₀ := (schwartz_withSeminorms ℂ ℝ ℂ).continuous_seminorm (0, 0)
    have h₂ := (schwartz_withSeminorms ℂ ℝ ℂ).continuous_seminorm (2, 0)
    have h := (((h₀.add h₂).comp (sampledDerivative d i.1).continuous).mul_const
      (∑' m, samplingWeight m)).continuousAt (x := (0 : 𝓢(ℝ, ℂ)))
    have hz : Tendsto (fun f => (SchwartzMap.seminorm ℂ 0 0 (sampledDerivative d i.1 f) +
      SchwartzMap.seminorm ℂ 2 0 (sampledDerivative d i.1 f)) * ∑' m, samplingWeight m)
      (𝓝 0) (𝓝 0) := by simpa [ContinuousAt, Function.comp_def] using h
    filter_upwards [hz (Iio_mem_nhds hε)] with f hf
    rw [sub_zero]
    exact (schwartzPeriodization_derivativeBound d f i.1).trans_lt hf

@[simp] theorem schwartzPeriodizationCLM_apply (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    (schwartzPeriodizationCLM d f).val x = ∑' m : ℤ, f (x + d * m) := rfl

private def continuousCircleFourierCoeff (m : ℤ) : C(AddCircle d, ℂ) →L[ℂ] ℂ := by
  let L : C(AddCircle d, ℂ) →ₗ[ℂ] ℂ :=
    { toFun f := fourierCoeff f m
      map_add' f g := congrFun
        (fourierCoeff.add (f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f))
          (g.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace g))) m
      map_smul' c f := fourierCoeff.const_smul f c m }
  refine L.mkContinuous 1 (fun f => ?_)
  rw [one_mul]
  change ‖∫ z, fourier (-m) z • f z ∂(haarAddCircle (T := d))‖ ≤ _
  have h := norm_integral_le_of_norm_le_const (μ := haarAddCircle (T := d))
    (f := fun x => fourier (-m) x • f x)
    (C := ‖f‖) (Eventually.of_forall fun z => ?_)
  · simpa using h
  · rw [norm_smul, fourier_apply, Circle.norm_coe, one_mul]
    exact f.norm_coe_le_norm z

/-- The Fourier coefficient of an orbit sum is a sample of the line Fourier
transform, with scaling by the length of a period. -/
theorem schwartzPeriodization_coefficient (f : 𝓢(ℝ, ℂ)) (m : ℤ) :
    periodicFourierCoefficient d (schwartzPeriodizationCLM d f) m =
      d⁻¹ • (𝓕 f) ((m : ℝ) / d) := by
  let a (n : ℤ) : ℂ := (𝓕 (scaleSchwartz d f)) n
  let h (n : ℤ) : C(AddCircle d, ℂ) := a n • fourier n
  have hA : Summable (fun n : ℤ => ‖a n‖) := by
    simpa [a, sampledDerivative_apply] using sampledDerivative_summable d f 0
  have hh : Summable h := by
    apply Summable.of_norm
    refine hA.of_nonneg_of_le (fun _ => norm_nonneg _) ?_
    intro n
    change ‖a n • fourier (T := d) n‖ ≤ ‖a n‖
    rw [norm_smul]
    exact mul_le_of_le_one_right (norm_nonneg _) ((ContinuousMap.norm_le _ zero_le_one).mpr
      (fun z => by rw [fourier_apply, Circle.norm_coe]))
  have hsum : ∑' n, h n = periodicCircleFunction d (schwartzPeriodizationCLM d f) := by
    apply ContinuousMap.ext
    intro z
    obtain ⟨x, rfl⟩ := Quotient.exists_rep z
    change (∑' n, h n) (x : AddCircle d) = _
    rw [← ContinuousMap.tsum_apply hh, periodicCircleFunction_coe,
      schwartzPeriodizationCLM_apply]
    change _ = integerPeriodization d f x
    rw [schwartzPeriodization_fourier]
    apply tsum_congr
    intro n
    change a n * fourier n (x : AddCircle d) = _
    rw [periodicFourierMode_circle]
  have hf (n : ℤ) : continuousCircleFourierCoeff d m (h n) =
      a n * Pi.single (M := fun _ : ℤ => ℂ) n 1 m := by
    change fourierCoeff (fun x => a n * fourier n x) m = _
    rw [fourierCoeff.const_mul, fourierCoeff_fourier]
  have hδ : HasSum (fun n => continuousCircleFourierCoeff d m (h n)) (a m) := by
    have hz (n : ℤ) (hn : n ≠ m) : continuousCircleFourierCoeff d m (h n) = 0 := by
      simp [hf, Pi.single_eq_of_ne (Ne.symm hn)]
    simpa only [hf m, Pi.single_eq_same, mul_one] using hasSum_single m hz
  change continuousCircleFourierCoeff d m (periodicCircleFunction d (schwartzPeriodizationCLM d f)) = _
  rw [← hsum, (continuousCircleFourierCoeff d m).map_tsum hh, hδ.tsum_eq]
  unfold a
  simp only [SchwartzMap.fourier_coe, Real.fourier_real_eq_integral_exp_smul, scaleSchwartz_apply]
  let u (x : ℝ) : ℂ := Complex.exp (↑(-2 * Real.pi * (x * (m / d))) * Complex.I) • f x
  have hscale := Measure.integral_comp_mul_left u d
  rw [abs_of_pos (inv_pos.mpr (schwartzPeriod_pos d))] at hscale
  calc
    _ = (∫ x : ℝ, u (d * x)) := by
      apply integral_congr_ae
      filter_upwards with x
      dsimp only [u]
      congr 2
      push_cast
      field_simp [(schwartzPeriod_pos d).ne'] <;> ring
    _ = _ := by simpa only [u, ← mul_assoc] using hscale

end
end Masullo
