import ScalarFractionalInterval
import ModulatedIntervalEvaluation
import Mathlib.Algebra.Group.PUnit
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

open Filter Function MeasureTheory Set Topology
open scoped ENNReal

namespace Masullo

noncomputable section

local notation "dx" => (volume : Measure ℝ)
private def unitMeasure : Measure PUnit.{1} := Measure.dirac PUnit.unit

local notation "ν₁" => unitMeasure

private instance : IsProbabilityMeasure unitMeasure := inferInstanceAs
  (IsProbabilityMeasure (Measure.dirac (PUnit.unit : PUnit.{1})))

private theorem unitChart_preserving (ρ : Measure ℝ) [SFinite ρ] :
    MeasurePreserving (MeasurableEquiv.punitProd (α := ℝ)) ((ν₁).prod ρ) ρ := by
  refine ⟨measurable_snd, ?_⟩
  change Measure.map Prod.snd ((ν₁).prod ρ) = ρ
  rw [unitMeasure, Measure.dirac_prod, Measure.map_map measurable_snd measurable_prodMk_left]
  exact Measure.map_id

private def liftUnit (ρ : Measure ℝ) [SFinite ρ] :
    Lp ℂ 2 ρ →ₗᵢ[ℂ] Lp ℂ 2 ((ν₁).prod ρ) :=
  Lp.compMeasurePreservingₗᵢ ℂ (MeasurableEquiv.punitProd (α := ℝ)) (unitChart_preserving ρ)

private def sliceUnit (ρ : Measure ℝ) [SFinite ρ] :
    Lp ℂ 2 ((ν₁).prod ρ) →ₗᵢ[ℂ] Lp ℂ 2 ρ :=
  Lp.compMeasurePreservingₗᵢ ℂ (MeasurableEquiv.punitProd (α := ℝ)).symm
    ((unitChart_preserving ρ).symm MeasurableEquiv.punitProd)

private def sliceFractionalTensor (s : ℝ) :
    FractionalMellinTensor ν₁ s →ₗᵢ[ℂ] MellinFrequencySobolev s :=
  (sliceUnit (stripMeasure 0 0 s)).comp completedLpTwoTensorEquiv.toLinearIsometry

private theorem scalarFractionalTrace_eq_slice {a b t : ℝ} (hab : a ≤ b) (ht : t ∈ Icc a b)
    (s : ℝ) (f : StripSobolev a b s) :
    scalarFractionalTrace hab ht s f =
      sliceFractionalTensor s
        (fractionalIntervalTrace ν₁ hab s ht (liftUnit (stripMeasure a b s) f)) := by
  let u := liftUnit (stripMeasure a b s) f
  let v := completedLpTwoTensorEquiv (fractionalIntervalTrace ν₁ hab s ht u)
  have h₁ : (u : PUnit.{1} × ℝ → ℂ) =ᵐ[(ν₁).prod dx] fun p => f p.2 :=
    (Measure.AbsolutelyContinuous.rfl.prod (absolutelyContinuous_amplitudeMeasure dx _
      (stripSobolevAmplitude_continuous a b s).measurable (stripSobolevAmplitude_pos a b s))).ae_le
      (Lp.coeFn_compMeasurePreserving f (unitChart_preserving (stripMeasure a b s)))
  have h₂ : (v : PUnit.{1} × ℝ → ℂ) =ᵐ[(ν₁).prod dx] fun p => Real.exp (t * p.2) • f p.2 :=
    (fractionalIntervalTrace_coordinates_ae ν₁ hab s ht u).trans
      (h₁.mono fun p hp => congrArg (Real.exp (t * p.2) • ·) hp)
  let e := MeasurableEquiv.punitProd (α := ℝ)
  have h₃ := ((unitChart_preserving dx).symm e).quasiMeasurePreserving.ae h₂
  have h₄ : (sliceUnit (stripMeasure 0 0 s) v : ℝ → ℂ) =ᵐ[dx] v ∘ e.symm :=
    (absolutelyContinuous_amplitudeMeasure dx _ (stripSobolevAmplitude_continuous 0 0 s).measurable
      (stripSobolevAmplitude_pos 0 0 s)).ae_le
      (Lp.coeFn_compMeasurePreserving v ((unitChart_preserving (stripMeasure 0 0 s)).symm e))
  apply Lp.ext
  apply (amplitudeMeasure_absolutelyContinuous dx (stripSobolevAmplitude 0 0 s)).ae_le
  filter_upwards [scalarFractionalTrace_ae hab ht s f, h₃, h₄] with x hx hy hz
  exact hx.trans (hy.symm.trans hz.symm)

/-- As the abscissa approaches a finite boundary of a compact base, the
scalar Mellin trace converges in the full fractional Sobolev norm. -/
theorem scalarFractionalTrace_continuous {a b : ℝ} (hab : a ≤ b) (s : ℝ)
    (f : StripSobolev a b s) :
    Continuous (fun t : Icc a b => scalarFractionalTrace hab t.property s f) := by
  exact ((sliceFractionalTensor s).continuous.comp
    (fractionalIntervalTrace_continuous ν₁ hab s (liftUnit (stripMeasure a b s) f))).congr
      (fun t => (scalarFractionalTrace_eq_slice hab t.property s f).symm)

/-- Uniform control on any set of scalar interior samples accumulating at
both ends bounds the full weighted norm. Each sample is contractive. -/
theorem scalarFractional_uniformSamples_bound {a b : ℝ} (hab : a ≤ b) (s : ℝ)
    (A : Set ℝ) (hAI : A ⊆ Icc a b) (ha : a ∈ closure A) (hb : b ∈ closure A)
    (f : StripSobolev a b s) (C : ℝ)
    (hC : ∀ t (ht : t ∈ A), ‖scalarFractionalTrace hab (hAI ht) s f‖ ^ 2 ≤ C) :
    ‖f‖ ^ 2 ≤ 2 * C := by
  have h := fractionalInterval_uniformSamples_bound ν₁ hab s A hAI ha hb
    (liftUnit (stripMeasure a b s) f) C (by
      intro t ht
      have he := hC t ht
      rw [scalarFractionalTrace_eq_slice hab (hAI ht) s f, LinearIsometry.norm_map] at he
      exact he)
  simpa only [LinearIsometry.norm_map] using h


/-- Every sampling set whose closure contains both endpoints gives the same
uniform sampling topology as the weighted compact-interval norm. -/
theorem scalarFractional_uniformSamples_tendsto_iff {a b : ℝ} (hab : a ≤ b) (s : ℝ)
    (A : Set ℝ) (hAI : A ⊆ Icc a b) (ha : a ∈ closure A) (hb : b ∈ closure A)
    {ι : Type*} {l : Filter ι} (f : ι → StripSobolev a b s) (g : StripSobolev a b s) :
    Tendsto f l (𝓝 g) ↔ ∀ ε > 0, ∀ᶠ i in l, ∀ t (ht : t ∈ A),
      ‖scalarFractionalTrace hab (hAI ht) s (f i - g)‖ < ε := by
  rw [Metric.tendsto_nhds]
  constructor
  · intro h ε hε
    filter_upwards [h ε hε] with i hi
    intro t ht
    exact (scalarFractionalTrace_norm_le hab (hAI ht) s _).trans_lt
      (by simpa only [dist_eq_norm] using hi)
  · intro h ε hε
    filter_upwards [h (ε / 2) (half_pos hε)] with i hi
    have hbnd := scalarFractional_uniformSamples_bound hab s A hAI ha hb (f i - g)
      ((ε / 2) ^ 2) (fun t ht => pow_le_pow_left₀ (norm_nonneg _) (hi t ht).le 2)
    rw [dist_eq_norm]
    nlinarith [norm_nonneg (f i - g)]

private theorem liftUnit_vanishes (a b s : ℝ) (f : StripSobolev a b s) {P : ℝ → Prop}
    (hf : ∀ᵐ x ∂dx, P x → f x = 0) :
    ∀ᵐ p ∂(ν₁).prod (stripMeasure a b s),
      P p.2 → liftUnit (stripMeasure a b s) f p = 0 := by
  have h := (amplitudeMeasure_absolutelyContinuous dx (stripSobolevAmplitude a b s)).ae_le hf
  have he := (unitChart_preserving (stripMeasure a b s)).quasiMeasurePreserving.ae h
  filter_upwards [he, Lp.coeFn_compMeasurePreserving f (unitChart_preserving (stripMeasure a b s))]
    with p hp he hn
  exact he.trans (hp hn)

/-- Scalar vertical traces on the positive abscissa ray. The finite-norm
domain in the inverse Fourier variable is supported on the nonpositive ray. -/
def scalarRightHalfLineTrace (b s : ℝ) (f : StripSobolev b b s)
    (hf : ∀ᵐ x ∂dx, 0 < x → f x = 0) (t : Ici b) : MellinFrequencySobolev s :=
  sliceFractionalTensor s (fractionalRightHalfLineTrace ν₁ b s
    (liftUnit (stripMeasure b b s) f) (liftUnit_vanishes b b s f hf) t)

/-- Scalar vertical traces on the negative abscissa ray. The finite-norm
domain in the inverse Fourier variable is supported on the nonnegative ray. -/
def scalarLeftHalfLineTrace (b s : ℝ) (f : StripSobolev b b s)
    (hf : ∀ᵐ x ∂dx, x < 0 → f x = 0) (t : Iic b) : MellinFrequencySobolev s :=
  sliceFractionalTensor s (fractionalLeftHalfLineTrace ν₁ b s
    (liftUnit (stripMeasure b b s) f) (liftUnit_vanishes b b s f hf) t)

theorem scalarRightHalfLineTrace_continuousAt (b s : ℝ) (f : StripSobolev b b s)
    (hf : ∀ᵐ x ∂dx, 0 < x → f x = 0) :
    ContinuousAt (scalarRightHalfLineTrace b s f hf) (⟨b, self_mem_Ici⟩ : Ici b) :=
  (sliceFractionalTensor s).continuous.continuousAt.comp
    (fractionalRightHalfLineTrace_continuousAt ν₁ b s
      (liftUnit (stripMeasure b b s) f) (liftUnit_vanishes b b s f hf))

theorem scalarLeftHalfLineTrace_continuousAt (b s : ℝ) (f : StripSobolev b b s)
    (hf : ∀ᵐ x ∂dx, x < 0 → f x = 0) :
    ContinuousAt (scalarLeftHalfLineTrace b s f hf) (⟨b, self_mem_Iic⟩ : Iic b) :=
  (sliceFractionalTensor s).continuous.continuousAt.comp
    (fractionalLeftHalfLineTrace_continuousAt ν₁ b s
      (liftUnit (stripMeasure b b s) f) (liftUnit_vanishes b b s f hf))

private theorem scalarSingletonTrace_eq (b s : ℝ) (f : StripSobolev b b s) :
    scalarFractionalTrace (a := b) (b := b) le_rfl ⟨le_rfl, le_rfl⟩ s f =
      fractionalMellinLine b s f := by
  change fractionalMellinLine b s (lpTwoMeasureInclusion _ f) = fractionalMellinLine b s f
  apply congrArg (fractionalMellinLine b s)
  exact Lp.ext (lpTwoMeasureInclusion_ae _ _)

private theorem scalarSingletonTrace_tensor (b s : ℝ) (f : StripSobolev b b s) :
    fractionalIntervalTrace ν₁ (a := b) (b := b) le_rfl s ⟨le_rfl, le_rfl⟩
        (liftUnit (stripMeasure b b s) f) =
      fractionalMellinTensor ν₁ b s (liftUnit (stripMeasure b b s) f) := by
  change fractionalMellinTensor ν₁ b s (lpTwoMeasureInclusion _ _) = _
  apply congrArg (fractionalMellinTensor ν₁ b s)
  exact Lp.ext (lpTwoMeasureInclusion_ae _ _)

theorem scalarRightHalfLineTrace_endpoint (b s : ℝ) (f : StripSobolev b b s)
    (hf : ∀ᵐ x ∂dx, 0 < x → f x = 0) :
    scalarRightHalfLineTrace b s f hf ⟨b, self_mem_Ici⟩ = fractionalMellinLine b s f := by
  unfold scalarRightHalfLineTrace
  rw [fractionalRightHalfLineTrace_endpoint, ← scalarSingletonTrace_tensor]
  exact (scalarFractionalTrace_eq_slice le_rfl (show b ∈ Icc b b from ⟨le_rfl, le_rfl⟩) s f).symm.trans
    (scalarSingletonTrace_eq b s f)

theorem scalarLeftHalfLineTrace_endpoint (b s : ℝ) (f : StripSobolev b b s)
    (hf : ∀ᵐ x ∂dx, x < 0 → f x = 0) :
    scalarLeftHalfLineTrace b s f hf ⟨b, self_mem_Iic⟩ = fractionalMellinLine b s f := by
  unfold scalarLeftHalfLineTrace
  rw [fractionalLeftHalfLineTrace_endpoint, ← scalarSingletonTrace_tensor]
  exact (scalarFractionalTrace_eq_slice le_rfl (show b ∈ Icc b b from ⟨le_rfl, le_rfl⟩) s f).symm.trans
    (scalarSingletonTrace_eq b s f)

theorem scalarRightHalfLineTrace_norm_le (b s : ℝ) (f : StripSobolev b b s)
    (hf : ∀ᵐ x ∂dx, 0 < x → f x = 0) (t : Ici b) :
    ‖scalarRightHalfLineTrace b s f hf t‖ ≤ ‖f‖ := by
  simpa only [scalarRightHalfLineTrace, LinearIsometry.norm_map] using
    fractionalRightHalfLineTrace_norm_le ν₁ b s (liftUnit (stripMeasure b b s) f)
      (liftUnit_vanishes b b s f hf) t

theorem scalarLeftHalfLineTrace_norm_le (b s : ℝ) (f : StripSobolev b b s)
    (hf : ∀ᵐ x ∂dx, x < 0 → f x = 0) (t : Iic b) :
    ‖scalarLeftHalfLineTrace b s f hf t‖ ≤ ‖f‖ := by
  simpa only [scalarLeftHalfLineTrace, LinearIsometry.norm_map] using
    fractionalLeftHalfLineTrace_norm_le ν₁ b s (liftUnit (stripMeasure b b s) f)
      (liftUnit_vanishes b b s f hf) t

theorem scalarRightHalfLine_uniformSamples_bound (b s : ℝ) (f : StripSobolev b b s)
    (hf : ∀ᵐ x ∂dx, 0 < x → f x = 0) (t : ℕ → Ici b)
    (ht : Tendsto t atTop (𝓝 (⟨b, self_mem_Ici⟩ : Ici b))) (C : ℝ)
    (hC : ∀ n, ‖scalarRightHalfLineTrace b s f hf (t n)‖ ≤ C) :
    ‖f‖ ≤ C := by
  have h := ((scalarRightHalfLineTrace_continuousAt b s f hf).tendsto.comp ht).norm
  rw [scalarRightHalfLineTrace_endpoint, LinearIsometryEquiv.norm_map] at h
  exact le_of_tendsto h (.of_forall hC)

theorem scalarLeftHalfLine_uniformSamples_bound (b s : ℝ) (f : StripSobolev b b s)
    (hf : ∀ᵐ x ∂dx, x < 0 → f x = 0) (t : ℕ → Iic b)
    (ht : Tendsto t atTop (𝓝 (⟨b, self_mem_Iic⟩ : Iic b))) (C : ℝ)
    (hC : ∀ n, ‖scalarLeftHalfLineTrace b s f hf (t n)‖ ≤ C) :
    ‖f‖ ≤ C := by
  have h := ((scalarLeftHalfLineTrace_continuousAt b s f hf).tendsto.comp ht).norm
  rw [scalarLeftHalfLineTrace_endpoint, LinearIsometryEquiv.norm_map] at h
  exact le_of_tendsto h (.of_forall hC)

private instance : BorelSpace PUnit.{1} where
  measurable_eq := borel_eq_top_of_discrete.symm

/-- Scalar Mellin moments in the logarithmic variable. -/
def scalarMellinMoment {a b s : ℝ} (f : StripSobolev a b s) (k : ℕ) (z : ℂ) : ℂ :=
  ∫ x, f x * mellinEvaluationKernel k z x ∂dx

/-- On every open range of absolutely integrable supported kernels, the actual
scalar Mellin transform is holomorphic and its derivatives are Mellin moments. -/
theorem scalarMellinMoment_analyticOnAbscissae {a b s : ℝ} {U J : Set ℝ}
    (hU : IsOpen U) (hJ : IsOpen J) (f : StripSobolev a b s)
    (hf : ∀ᵐ x ∂dx, x ∉ U → f x = 0)
    (hKer : ∀ w : ℂ, w.re ∈ J → ∀ k : ℕ,
      MemLp (U.indicator (mellinEvaluationKernel k w)) 2 (stripMeasure (-a) (-b) (-s)))
    (k : ℕ) {z : ℂ} (hz : z.re ∈ J) :
    Integrable (fun x => f x * mellinEvaluationKernel k z x) dx ∧
      AnalyticAt ℂ (scalarMellinMoment f 0) z ∧
      iteratedDeriv k (scalarMellinMoment f 0) z = scalarMellinMoment f k z := by
  let u : lpTwoRadialSupport ν₁ (stripMeasure a b s) U :=
    ⟨liftUnit (stripMeasure a b s) f, liftUnit_vanishes a b s f hf⟩
  let χ : PontryaginDual PUnit.{1} := 1
  have hcoe : (u.val : PUnit.{1} × ℝ → ℂ) =ᵐ[(ν₁).prod dx] fun p => f p.2 :=
    (Measure.AbsolutelyContinuous.rfl.prod (absolutelyContinuous_amplitudeMeasure dx _
      (stripSobolevAmplitude_continuous a b s).measurable (stripSobolevAmplitude_pos a b s))).ae_le
      (Lp.coeFn_compMeasurePreserving f (unitChart_preserving (stripMeasure a b s)))
  let e := MeasurableEquiv.punitProd (α := ℝ)
  have hAE (n : ℕ) (w : ℂ) :
      (fun p : PUnit.{1} × ℝ => (χ p.1 : ℂ) * u.val p * mellinEvaluationKernel n w p.2)
        =ᵐ[(ν₁).prod dx] (fun x => f x * mellinEvaluationKernel n w x) ∘ e :=
    hcoe.mono fun p hp => by
      change (χ p.1 : ℂ) * u.val p * mellinEvaluationKernel n w p.2 =
        f p.2 * mellinEvaluationKernel n w p.2
      simp [χ, hp]
  have hm (n : ℕ) : modulatedIntervalMoment ν₁ a b s χ u n = scalarMellinMoment f n := by
    funext w
    exact (integral_congr_ae (hAE n w)).trans
      ((unitChart_preserving dx).integral_comp e.measurableEmbedding
        (fun x => f x * mellinEvaluationKernel n w x))
  obtain ⟨L, hL, _⟩ := modulatedInterval_mellinMoment_of_kernel ν₁ a b s hU χ k z (hKer z hz k)
  refine ⟨((unitChart_preserving dx).integrable_comp_emb e.measurableEmbedding).mp
    ((hL u).1.congr (hAE k z)), ?_⟩
  simpa only [hm 0, hm k] using
    modulatedIntervalMoment_analyticOnAbscissae ν₁ a b s hU χ u hJ hKer k hz

theorem scalarMellinMoment_compact {a b s : ℝ} (hs : 0 ≤ s) (f : StripSobolev a b s)
    (k : ℕ) {z : ℂ} (hz : z.re ∈ Ioo a b) :
    Integrable (fun x => f x * mellinEvaluationKernel k z x) dx ∧
      AnalyticAt ℂ (scalarMellinMoment f 0) z ∧
      iteratedDeriv k (scalarMellinMoment f 0) z = scalarMellinMoment f k z := by
  refine scalarMellinMoment_analyticOnAbscissae isOpen_univ isOpen_Ioo f (by simp) ?_ k hz
  intro w hw n
  rw [indicator_univ]
  exact (mellinEvaluationKernel_memLp_iff hw.1.le hw.2.le hs n).mpr (Or.inl hw)

theorem scalarMellinMoment_rightHalfLine {b s : ℝ} (hs : 0 ≤ s) (f : StripSobolev b b s)
    (hf : ∀ᵐ x ∂dx, 0 < x → f x = 0) (k : ℕ) {z : ℂ} (hz : b < z.re) :
    Integrable (fun x => f x * mellinEvaluationKernel k z x) dx ∧
      AnalyticAt ℂ (scalarMellinMoment f 0) z ∧
      iteratedDeriv k (scalarMellinMoment f 0) z = scalarMellinMoment f k z := by
  refine scalarMellinMoment_analyticOnAbscissae (U := Iio 0) isOpen_Iio isOpen_Ioi f ?_ ?_ k hz
  · filter_upwards [hf, (dx).ae_ne (0 : ℝ)] with x hx hzero h
    exact hx (lt_of_le_of_ne (le_of_not_gt h) hzero.symm)
  · intro w (hw : b < w.re) n
    exact (supportedMellinEvaluation_memLp_iff b b s isOpen_Iio n w).mp
      ((hardySobolev_right_mellinEvaluation_exists_iff hw.le hs n).mpr (Or.inl hw))

theorem scalarMellinMoment_leftHalfLine {b s : ℝ} (hs : 0 ≤ s) (f : StripSobolev b b s)
    (hf : ∀ᵐ x ∂dx, x < 0 → f x = 0) (k : ℕ) {z : ℂ} (hz : z.re < b) :
    Integrable (fun x => f x * mellinEvaluationKernel k z x) dx ∧
      AnalyticAt ℂ (scalarMellinMoment f 0) z ∧
      iteratedDeriv k (scalarMellinMoment f 0) z = scalarMellinMoment f k z := by
  refine scalarMellinMoment_analyticOnAbscissae (U := Ioi 0) isOpen_Ioi isOpen_Iio f ?_ ?_ k hz
  · filter_upwards [hf, (dx).ae_ne (0 : ℝ)] with x hx hzero h
    exact hx (lt_of_le_of_ne (le_of_not_gt h) hzero)
  · intro w (hw : w.re < b) n
    exact (supportedMellinEvaluation_memLp_iff b b s isOpen_Ioi n w).mp
      ((hardySobolev_left_mellinEvaluation_exists_iff hw.le hs n).mpr (Or.inl hw))

private theorem integrable_exp_smul_of_real_moment {a b s t : ℝ}
    (f : StripSobolev a b s)
    (h : Integrable (fun x => f x * mellinEvaluationKernel 0 (t : ℂ) x) dx) :
    Integrable (fun x : ℝ => Real.exp (t * x) • f x) dx := by
  refine h.congr (.of_forall fun x => ?_)
  simp only [mellinEvaluationKernel, pow_zero, mul_one, Complex.real_smul,
    Complex.ofReal_exp, Complex.ofReal_mul, mul_comm (f x)]

/-- On the open strip the vertical profiles of completed classes are the
actual scalar Mellin integrals. -/
theorem scalarFractionalTrace_interior_values {a b s t : ℝ} (hs : 0 ≤ s) (ht : t ∈ Ioo a b)
    (f : StripSobolev a b s) :
    (mellinFrequencyValues hs
      (scalarFractionalTrace (ht.1.trans ht.2).le (Ioo_subset_Icc_self ht) s f) : ℝ → ℂ) =ᵐ[dx]
      fun y => scalarMellinMoment f 0 (⟨t, 2 * Real.pi * y⟩ : ℂ) := by
  let h := scalarInterval_lineMeasure_le (ht.1.trans ht.2).le (Ioo_subset_Icc_self ht) s
  let v := lpTwoMeasureInclusion h f
  have hv : (v : ℝ → ℂ) =ᵐ[dx] f :=
    (absolutelyContinuous_amplitudeMeasure dx _ (stripSobolevAmplitude_continuous t t s).measurable
      (stripSobolevAmplitude_pos t t s)).ae_le (lpTwoMeasureInclusion_ae h f)
  have hi := integrable_exp_smul_of_real_moment f
    (scalarMellinMoment_compact hs f 0 (z := (t : ℂ)) (by simpa using ht)).1
  refine (fractionalMellinLine_values_ae t hs v (hi.congr (hv.symm.mono fun x hx =>
    congrArg (Real.exp (t * x) • ·) hx))).trans (.of_forall fun y => ?_)
  exact integral_congr_ae (hv.mono fun x hx =>
    congrArg (fun c : ℂ => c * mellinEvaluationKernel 0 (⟨t, 2 * Real.pi * y⟩ : ℂ) x) hx)

private theorem sliceFractionalTensor_values {s : ℝ} (hs : 0 ≤ s)
    (v : FractionalMellinTensor ν₁ s) :
    mellinFrequencyValues hs (sliceFractionalTensor s v) =
      fractionalMellinTensorValues ν₁ hs (1 : PontryaginDual PUnit.{1}) v := by
  let u := completedLpTwoTensorEquiv v
  apply congrArg (mellinFrequencyValues hs)
  apply Lp.ext
  have h := Lp.coeFn_compMeasurePreserving u
    ((unitChart_preserving (stripMeasure 0 0 s)).symm (MeasurableEquiv.punitProd (α := ℝ)))
  filter_upwards [h, lpTwoCharacterCoefficient_ae (1 : PontryaginDual PUnit.{1}) u]
    with x hx hc
  change sliceFractionalTensor s v x = u (PUnit.unit, x) at hx
  change sliceFractionalTensor s v x = lpTwoCharacterCoefficient (1 : PontryaginDual PUnit.{1}) u x
  rw [hx, hc.2]
  change u (PUnit.unit, x) =
    ∫ j, ((1 : PontryaginDual PUnit.{1}) j : ℂ) * u (j, x) ∂Measure.dirac PUnit.unit
  rw [integral_dirac]
  simp

private theorem unitMellinIntegral_eq {a b s : ℝ} (f : StripSobolev a b s) (z : ℂ) :
    (∫ p : PUnit.{1} × ℝ, liftUnit (stripMeasure a b s) f p *
        mellinEvaluationKernel 0 z p.2 ∂(ν₁).prod dx) = scalarMellinMoment f 0 z := by
  let e := MeasurableEquiv.punitProd (α := ℝ)
  have h : (liftUnit (stripMeasure a b s) f : PUnit.{1} × ℝ → ℂ) =ᵐ[(ν₁).prod dx]
      fun p => f p.2 :=
    (Measure.AbsolutelyContinuous.rfl.prod (absolutelyContinuous_amplitudeMeasure dx _
      (stripSobolevAmplitude_continuous a b s).measurable (stripSobolevAmplitude_pos a b s))).ae_le
      (Lp.coeFn_compMeasurePreserving f (unitChart_preserving (stripMeasure a b s)))
  have he : (fun p => liftUnit (stripMeasure a b s) f p * mellinEvaluationKernel 0 z p.2)
      =ᵐ[(ν₁).prod dx] (fun x => f x * mellinEvaluationKernel 0 z x) ∘ e :=
    h.mono fun p hp => congrArg (· * mellinEvaluationKernel 0 z p.2) hp
  exact (integral_congr_ae he).trans
    ((unitChart_preserving dx).integral_comp e.measurableEmbedding
      (fun x => f x * mellinEvaluationKernel 0 z x))

/-- Interior vertical profiles on the right half-plane represent the actual
scalar Mellin integral almost everywhere. -/
theorem scalarRightHalfLineTrace_interior_values {b s : ℝ} (hs : 0 ≤ s)
    (f : StripSobolev b b s) (hf : ∀ᵐ x ∂dx, 0 < x → f x = 0)
    (t : Ici b) (ht : b < (t : ℝ)) :
    (mellinFrequencyValues hs (scalarRightHalfLineTrace b s f hf t) : ℝ → ℂ) =ᵐ[dx]
      fun y => scalarMellinMoment f 0 (⟨(t : ℝ), 2 * Real.pi * y⟩ : ℂ) := by
  rw [scalarRightHalfLineTrace, sliceFractionalTensor_values]
  refine (fractionalRightHalfLineTrace_values_ae ν₁ b hs (liftUnit (stripMeasure b b s) f)
    (liftUnit_vanishes b b s f hf) t ht (1 : PontryaginDual PUnit.{1})).trans
      (.of_forall fun y => ?_)
  simpa using unitMellinIntegral_eq f (⟨(t : ℝ), 2 * Real.pi * y⟩ : ℂ)

/-- Interior vertical profiles on the left half-plane represent the actual
scalar Mellin integral almost everywhere. -/
theorem scalarLeftHalfLineTrace_interior_values {b s : ℝ} (hs : 0 ≤ s)
    (f : StripSobolev b b s) (hf : ∀ᵐ x ∂dx, x < 0 → f x = 0)
    (t : Iic b) (ht : (t : ℝ) < b) :
    (mellinFrequencyValues hs (scalarLeftHalfLineTrace b s f hf t) : ℝ → ℂ) =ᵐ[dx]
      fun y => scalarMellinMoment f 0 (⟨(t : ℝ), 2 * Real.pi * y⟩ : ℂ) := by
  rw [scalarLeftHalfLineTrace, sliceFractionalTensor_values]
  refine (fractionalLeftHalfLineTrace_values_ae ν₁ b hs (liftUnit (stripMeasure b b s) f)
    (liftUnit_vanishes b b s f hf) t ht (1 : PontryaginDual PUnit.{1})).trans
      (.of_forall fun y => ?_)
  simpa using unitMellinIntegral_eq f (⟨(t : ℝ), 2 * Real.pi * y⟩ : ℂ)

/-- For actual vertical profiles, fractional boundary convergence gives an
almost-everywhere convergent subsequence along any chosen sequence of lines. -/
theorem scalarMellinProfiles_subsequence {s : ℝ} (hs : 0 ≤ s)
    {T : ℕ → MellinFrequencySobolev s} {B : MellinFrequencySobolev s}
    (hT : Tendsto T atTop (𝓝 B)) (g : ℕ → ℝ → ℂ)
    (hg : ∀ n, (mellinFrequencyValues hs (T n) : ℝ → ℂ) =ᵐ[dx] g n) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ y ∂dx,
      Tendsto (fun n => g (ns n) y) atTop (𝓝 (mellinFrequencyValues hs B y)) := by
  have hv : Tendsto (fun n => mellinFrequencyValues hs (T n)) atTop
      (𝓝 (mellinFrequencyValues hs B)) :=
    ((mellinFrequencyValues hs).continuous.tendsto B).comp hT
  obtain ⟨ns, hns, hlim⟩ := (tendstoInMeasure_of_tendsto_Lp hv).exists_seq_tendsto_ae
  refine ⟨ns, hns, ?_⟩
  filter_upwards [hlim, ae_all_iff.2 hg] with x h hx
  simpa only [← hx] using h

/-- Any sequence of interior lines tending to a point of the closed
interval admits a subsequence of actual Mellin values with the correct
almost-everywhere limit. -/
theorem scalarFractionalTrace_interior_subsequence {a b s : ℝ} (hab : a ≤ b) (hs : 0 ≤ s)
    (f : StripSobolev a b s) (t : ℕ → Ioo a b) (e : Icc a b)
    (ht : Tendsto (fun n => (⟨(t n : ℝ), Ioo_subset_Icc_self (t n).property⟩ : Icc a b))
      atTop (𝓝 e)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ y ∂dx,
      Tendsto (fun n => scalarMellinMoment f 0 (⟨(t (ns n) : ℝ), 2 * Real.pi * y⟩ : ℂ))
        atTop (𝓝 (mellinFrequencyValues hs (scalarFractionalTrace hab e.property s f) y)) := by
  exact scalarMellinProfiles_subsequence hs
    (((scalarFractionalTrace_continuous hab s f).continuousAt (x := e)).tendsto.comp ht)
    (fun n y => scalarMellinMoment f 0 (⟨(t n : ℝ), 2 * Real.pi * y⟩ : ℂ))
    (fun n => scalarFractionalTrace_interior_values hs (t n).property f)

theorem scalarLeftHalfLineTrace_interior_subsequence {b s : ℝ} (hs : 0 ≤ s)
    (f : StripSobolev b b s) (hf : ∀ᵐ x ∂dx, x < 0 → f x = 0)
    (t : ℕ → Iic b) (hI : ∀ n, (t n : ℝ) < b)
    (ht : Tendsto t atTop (𝓝 (⟨b, self_mem_Iic⟩ : Iic b))) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ y ∂dx,
      Tendsto (fun n => scalarMellinMoment f 0 (⟨(t (ns n) : ℝ), 2 * Real.pi * y⟩ : ℂ))
        atTop (𝓝 (mellinFrequencyValues hs (fractionalMellinLine b s f) y)) := by
  simpa only [scalarLeftHalfLineTrace_endpoint] using
    scalarMellinProfiles_subsequence hs
      ((scalarLeftHalfLineTrace_continuousAt b s f hf).tendsto.comp ht)
      (fun n y => scalarMellinMoment f 0 (⟨(t n : ℝ), 2 * Real.pi * y⟩ : ℂ))
      (fun n => scalarLeftHalfLineTrace_interior_values hs f hf (t n) (hI n))

theorem scalarRightHalfLineTrace_interior_subsequence {b s : ℝ} (hs : 0 ≤ s)
    (f : StripSobolev b b s) (hf : ∀ᵐ x ∂dx, 0 < x → f x = 0)
    (t : ℕ → Ici b) (hI : ∀ n, b < (t n : ℝ))
    (ht : Tendsto t atTop (𝓝 (⟨b, self_mem_Ici⟩ : Ici b))) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ y ∂dx,
      Tendsto (fun n => scalarMellinMoment f 0 (⟨(t (ns n) : ℝ), 2 * Real.pi * y⟩ : ℂ))
        atTop (𝓝 (mellinFrequencyValues hs (fractionalMellinLine b s f) y)) := by
  simpa only [scalarRightHalfLineTrace_endpoint] using
    scalarMellinProfiles_subsequence hs
      ((scalarRightHalfLineTrace_continuousAt b s f hf).tendsto.comp ht)
      (fun n y => scalarMellinMoment f 0 (⟨(t n : ℝ), 2 * Real.pi * y⟩ : ℂ))
      (fun n => scalarRightHalfLineTrace_interior_values hs f hf (t n) (hI n))

/-- At an even degree the fractional trace and the completed derivative
line model are isometric through their common weighted profile. -/
def scalarEvenDegreeTraceEquiv (b : ℝ) (N : ℕ) :
    MellinFrequencySobolev (2 * (N : ℝ)) ≃ₗᵢ[ℂ] MellinLineCompletion b N :=
  (fractionalMellinLine b (2 * (N : ℝ))).symm.trans (mellinLineEquiv b N)

theorem scalarEvenDegreeTraceEquiv_apply (b : ℝ) (N : ℕ)
    (f : StripSobolev b b (2 * (N : ℝ))) :
    scalarEvenDegreeTraceEquiv b N (fractionalMellinLine b (2 * (N : ℝ)) f) =
      mellinLineEquiv b N f := by
  simp [scalarEvenDegreeTraceEquiv]

end
end Masullo
