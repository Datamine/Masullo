import ModulatedIntervalTraces
import RealFourierPlancherel

open Filter Function MeasureTheory Set Topology UniformSpace
open scoped ENNReal FourierTransform TensorProduct

namespace Masullo

noncomputable section

local notation "dx" => (volume : Measure ℝ)
local notation "L²" => Lp ℂ 2 dx

/-- The Hilbert space of vertical Sobolev traces in inverse Fourier
coordinates. The trace itself is read by `mellinFrequencyValues`. -/
abbrev MellinFrequencySobolev (s : ℝ) := StripSobolev 0 0 s

private def stripLineAmplitudeIso (b s : ℝ) : StripSobolev b b s ≃ₗᵢ[ℂ] L² :=
  amplitudeL2Iso dx _ (stripSobolevAmplitude_continuous b b s).measurable
    (stripSobolevAmplitude_pos b b s)

/-- The normalized vertical line lift at every real order. Its coordinate
function in the inverse Fourier variable is the exponentially twisted input. -/
def fractionalMellinLine (b s : ℝ) : StripSobolev b b s ≃ₗᵢ[ℂ] MellinFrequencySobolev s :=
  (stripLineAmplitudeIso b s).trans (stripLineAmplitudeIso 0 s).symm

theorem fractionalMellinLine_ae (b s : ℝ) (f : StripSobolev b b s) :
    (fractionalMellinLine b s f : ℝ → ℂ) =ᵐ[dx] fun x => Real.exp (b * x) • f x := by
  let r := stripSobolevAmplitude 0 0 s
  let A := stripLineAmplitudeIso b s
  have hr := (stripSobolevAmplitude_continuous 0 0 s).measurable
  have hp := stripSobolevAmplitude_pos 0 0 s
  have h := (absolutelyContinuous_amplitudeMeasure dx r hr hp).ae_le
    (amplitudeL2Iso_symm_ae dx r hr hp (A f))
  filter_upwards [h, amplitudeL2Iso_ae dx (stripSobolevAmplitude b b s)
    (stripSobolevAmplitude_continuous b b s).measurable (stripSobolevAmplitude_pos b b s) f]
    with x hx hA
  change fractionalMellinLine b s f x = (r x)⁻¹ • A f x at hx
  change A f x = _ at hA
  rw [hx, hA, smul_smul]
  have he : stripSobolevAmplitude b b s x = Real.exp (b * x) * r x := by
    simp [stripSobolevAmplitude, r]
  rw [he, mul_left_comm, inv_mul_cancel₀ (hp x).ne', mul_one]

private theorem volume_le_zeroStrip {s : ℝ} (hs : 0 ≤ s) :
    dx ≤ stripMeasure 0 0 s := by
  rw [stripMeasure_eq 0 0 s le_rfl]
  unfold hardySobolevMeasure
  refine ((withDensity_one (μ := dx)).symm.le).trans (withDensity_mono ?_)
  refine .of_forall fun x => ?_
  change (1 : ℝ≥0∞) ≤ ENNReal.ofReal (hardySobolevWeight 0 0 s x)
  rw [← ENNReal.ofReal_one]
  apply ENNReal.ofReal_le_ofReal
  simp only [hardySobolevWeight, mul_zero, zero_mul, Real.exp_zero, max_self, one_mul]
  exact Real.one_le_rpow (le_add_of_nonneg_right (sq_nonneg x)) (div_nonneg hs (by norm_num))

/-- Actual vertical trace values, with the frequency variable scaled so
that its imaginary height is `2 * π * y`. -/
def mellinFrequencyValues {s : ℝ} (hs : 0 ≤ s) : MellinFrequencySobolev s →L[ℂ] L² :=
  realFourierL2.symm.toLinearIsometry.toContinuousLinearMap.comp
    (lpTwoMeasureInclusion (volume_le_zeroStrip hs))

theorem mellinFrequencyValues_injective {s : ℝ} (hs : 0 ≤ s) :
    Injective (mellinFrequencyValues hs) := by
  intro f g hfg
  let inc := lpTwoMeasureInclusion (volume_le_zeroStrip hs)
  have h : inc f = inc g := realFourierL2.symm.injective hfg
  have hf := lpTwoMeasureInclusion_ae (volume_le_zeroStrip hs) f
  rw [show lpTwoMeasureInclusion (volume_le_zeroStrip hs) f = inc g from h] at hf
  exact Lp.ext <| (amplitudeMeasure_absolutelyContinuous dx (stripSobolevAmplitude 0 0 s)).ae_le
    (hf.symm.trans (lpTwoMeasureInclusion_ae (volume_le_zeroStrip hs) g))

/-- On each integrable exponential profile the fractional trace is the actual
Mellin integral, in the Fourier normalization of the vertical variable. -/
theorem fractionalMellinLine_values_ae (b : ℝ) {s : ℝ} (hs : 0 ≤ s) (f : StripSobolev b b s)
    (hf : Integrable (fun x : ℝ => Real.exp (b * x) • f x) dx) :
    (mellinFrequencyValues hs (fractionalMellinLine b s f) : ℝ → ℂ) =ᵐ[dx]
      fun y => ∫ x, f x * mellinEvaluationKernel 0 (⟨b, 2 * Real.pi * y⟩ : ℂ) x := by
  let u := lpTwoMeasureInclusion (volume_le_zeroStrip hs) (fractionalMellinLine b s f)
  have hu : (u : ℝ → ℂ) =ᵐ[dx] fun x => Real.exp (b * x) • f x :=
    (lpTwoMeasureInclusion_ae (volume_le_zeroStrip hs) _).trans (fractionalMellinLine_ae b s f)
  refine (realFourierL2_symm_ae_eq_fourierInv u (hf.congr hu.symm)).trans (.of_forall fun y => ?_)
  rw [Real.fourierInv_eq']
  apply integral_congr_ae
  filter_upwards [hu] with x hx
  rw [hx, mellinEvaluationKernel, pow_zero, mul_one, Complex.real_smul, smul_eq_mul]
  rw [mul_comm (f x), Complex.ofReal_exp, ← mul_assoc, ← Complex.exp_add]
  congr 2
  apply Complex.ext
  · simp [Complex.mul_re]
  · simp [Complex.mul_im]
    ring


section Product

variable {K : Type*} [MeasurableSpace K] (μ : Measure K) [SFinite μ]

/-- The fractional vertical Sobolev tensor with the compact angular factor.
Its radial factor carries the inverse Fourier Sobolev norm. -/
abbrev FractionalMellinTensor (s : ℝ) :=
  Completion (Lp ℂ 2 μ ⊗[ℂ] MellinFrequencySobolev s)

/-- Fractional Mellin transformation in the radial coordinate leaves the
angular Hilbert factor unchanged. -/
def fractionalMellinTensor (b s : ℝ) :
    Lp ℂ 2 (μ.prod (stripMeasure b b s)) ≃ₗᵢ[ℂ] FractionalMellinTensor μ s :=
  completedLpTwoTensorEquiv.symm.trans
    (completionCongrIsometry (TensorProduct.congrIsometry (.refl ℂ _) (fractionalMellinLine b s)))

/-- Restrict to a vertical line in a compact base, then take its fractional
Mellin transform. -/
def fractionalIntervalTrace {a b : ℝ} (hab : a ≤ b) (s : ℝ) {t : ℝ} (ht : t ∈ Icc a b) :
    Lp ℂ 2 (μ.prod (stripMeasure a b s)) →L[ℂ] FractionalMellinTensor μ s :=
  (fractionalMellinTensor μ t s).toLinearIsometry.toContinuousLinearMap.comp
    (lpTwoMeasureInclusion (by
      rw [modulatedInterval_prod_weightedMeasure μ (a := t) le_rfl,
        modulatedInterval_prod_weightedMeasure μ hab]
      apply withDensity_mono
      exact .of_forall fun p => ENNReal.ofReal_le_ofReal
        (hardySobolevWeight_mono_interval ht.1 ht.2 ht.1 ht.2 s p.2)))

theorem fractionalIntervalTrace_norm_le {a b : ℝ} (hab : a ≤ b) (s : ℝ) {t : ℝ}
    (ht : t ∈ Icc a b) (f : Lp ℂ 2 (μ.prod (stripMeasure a b s))) :
    ‖fractionalIntervalTrace μ hab s ht f‖ ≤ ‖f‖ := by
  unfold fractionalIntervalTrace
  rw [ContinuousLinearMap.comp_apply]
  change ‖fractionalMellinTensor μ t s _‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  exact lpTwoMeasureInclusion_norm_le _ f

/-- The two fractional endpoint traces determine the compact interval
completion topology, and compatible pairs form a closed subspace. -/
theorem fractionalIntervalEndpoints_closedEmbedding {a b : ℝ} (hab : a ≤ b) (s : ℝ) :
    let A := fractionalIntervalTrace μ hab s (left_mem_Icc.mpr hab)
    let B := fractionalIntervalTrace μ hab s (right_mem_Icc.mpr hab)
    IsClosedEmbedding (A.prod B) ∧
      ∀ f, ‖A.prod B f‖ ≤ ‖f‖ ∧ ‖f‖ ^ 2 ≤ ‖A f‖ ^ 2 + ‖B f‖ ^ 2 := by
  intro A B
  obtain ⟨ha, hb, hW⟩ := modulatedInterval_endpointMeasures μ hab s
  have hsq (f : Lp ℂ 2 (μ.prod (stripMeasure a b s))) : ‖f‖ ^ 2 ≤ ‖A f‖ ^ 2 + ‖B f‖ ^ 2 := by
    change ‖f‖ ^ 2 ≤ ‖fractionalMellinTensor μ a s (lpTwoMeasureInclusion ha f)‖ ^ 2 +
      ‖fractionalMellinTensor μ b s (lpTwoMeasureInclusion hb f)‖ ^ 2
    simp only [LinearIsometryEquiv.norm_map]
    exact lpTwo_norm_sq_le_endpoints ha hb hW f
  have hlow (f : Lp ℂ 2 (μ.prod (stripMeasure a b s))) : ‖f‖ ≤ 2 * ‖A.prod B f‖ := by
    have hA : ‖A f‖ ≤ ‖A.prod B f‖ := le_max_left _ _
    have hB : ‖B f‖ ≤ ‖A.prod B f‖ := le_max_right _ _
    nlinarith [hsq f, pow_le_pow_left₀ (norm_nonneg _) hA 2, pow_le_pow_left₀ (norm_nonneg _) hB 2,
      norm_nonneg f, norm_nonneg (A.prod B f)]
  have hJ : AntilipschitzWith 2 (A.prod B) := AntilipschitzWith.of_le_mul_dist fun f g => by
    simpa only [dist_eq_norm, map_sub, NNReal.coe_ofNat] using hlow (f - g)
  refine ⟨hJ.isClosedEmbedding (A.prod B).uniformContinuous, fun f => ⟨?_, hsq f⟩⟩
  exact max_le (fractionalIntervalTrace_norm_le μ hab s _ f) (fractionalIntervalTrace_norm_le μ hab s _ f)



/-- Compatible pairs of fractional Mellin endpoint traces. -/
def fractionalIntervalEndpointSpace {a b : ℝ} (hab : a ≤ b) (s : ℝ) :
    Submodule ℂ (FractionalMellinTensor μ s × FractionalMellinTensor μ s) :=
  ((fractionalIntervalTrace μ hab s (left_mem_Icc.mpr hab)).prod
    (fractionalIntervalTrace μ hab s (right_mem_Icc.mpr hab))).toLinearMap.range

/-- Fractional Mellin transformation realizes the compact interval completion
as the closed space of compatible pairs of its fractional line traces. -/
def fractionalIntervalEndpointEquiv {a b : ℝ} (hab : a ≤ b) (s : ℝ) :
    Lp ℂ 2 (μ.prod (stripMeasure a b s)) ≃L[ℂ] fractionalIntervalEndpointSpace μ hab s := by
  let J := (fractionalIntervalTrace μ hab s (left_mem_Icc.mpr hab)).prod
    (fractionalIntervalTrace μ hab s (right_mem_Icc.mpr hab))
  have hJ : IsClosedEmbedding J := (fractionalIntervalEndpoints_closedEmbedding μ hab s).1
  let e := LinearEquiv.ofInjective J.toLinearMap hJ.injective
  refine ⟨e, J.continuous.subtype_mk _, ?_⟩
  apply hJ.isEmbedding.isInducing.continuous_iff.mpr
  have hcomp : (fun x => J (e.symm x)) = Subtype.val :=
    funext fun x => congrArg Subtype.val (e.apply_symm_apply x)
  change Continuous (fun x => J (e.symm x))
  rw [hcomp]
  exact continuous_subtype_val


theorem fractionalIntervalTrace_energy {a b : ℝ} (hab : a ≤ b) (s : ℝ)
    {t : ℝ} (ht : t ∈ Icc a b) (f : Lp ℂ 2 (μ.prod (stripMeasure a b s))) :
    ‖fractionalIntervalTrace μ hab s ht f‖ ^ 2 = intervalWeightedLineEnergy μ a b s f t := by
  unfold fractionalIntervalTrace
  rw [ContinuousLinearMap.comp_apply]
  change ‖fractionalMellinTensor μ t s (lpTwoMeasureInclusion _ f)‖ ^ 2 = _
  rw [LinearIsometryEquiv.norm_map, lpTwoMeasureInclusion_sq,
    modulatedInterval_prod_weightedMeasure μ (a := t) le_rfl]
  let W := hardySobolevWeight t t s
  have hW : Measurable (fun p : K × ℝ => ENNReal.ofReal (W p.2)) :=
    ((continuous_hardySobolevWeight t t s).measurable.comp measurable_snd).ennreal_ofReal
  change (∫ p : K × ℝ, ‖f p‖ ^ 2 ∂(μ.prod volume).withDensity (fun p => ENNReal.ofReal (W p.2))) = _
  rw [integral_withDensity_eq_integral_toReal_smul hW (.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [intervalWeightedLineEnergy, ENNReal.toReal_ofReal (hardySobolevWeight_nonneg ..),
    W, smul_eq_mul]

/-- Sample sets approaching both endpoints recover the real-order interval
norm when the sampled trace norms are controlled uniformly. -/
theorem fractionalInterval_uniformSamples_bound {a b : ℝ} (hab : a ≤ b) (s : ℝ)
    (A : Set ℝ) (hAI : A ⊆ Icc a b) (ha : a ∈ closure A) (hb : b ∈ closure A)
    (f : Lp ℂ 2 (μ.prod (stripMeasure a b s))) (C : ℝ)
    (hC : ∀ t (ht : t ∈ A), ‖fractionalIntervalTrace μ hab s (hAI ht) f‖ ^ 2 ≤ C) :
    ‖f‖ ^ 2 ≤ 2 * C := by
  let E := intervalWeightedLineEnergy μ a b s f
  have hClosed : IsClosed {x ∈ Icc a b | E x ≤ C} :=
    (isClosed_Icc : IsClosed (Icc a b)).isClosed_le
      (intervalWeightedLineEnergy_continuousOn μ hab s f) continuousOn_const
  have he : closure A ⊆ {x ∈ Icc a b | E x ≤ C} := closure_minimal (fun x hx => by
    refine ⟨hAI hx, ?_⟩
    rw [show E x = _ from (fractionalIntervalTrace_energy μ hab s (hAI hx) f).symm]
    exact hC x hx) hClosed
  have h := ((fractionalIntervalEndpoints_closedEmbedding μ hab s).2 f).2
  rw [fractionalIntervalTrace_energy, fractionalIntervalTrace_energy] at h
  exact h.trans (by simpa only [two_mul] using add_le_add (he ha).2 (he hb).2)

section Character

variable [TopologicalSpace K] [BorelSpace K] [CommGroup K] [IsFiniteMeasure μ]

/-- Evaluation of a vertical tensor at an angular character and all
imaginary heights, as an ordinary L² trace. -/
def fractionalMellinTensorValues {s : ℝ} (hs : 0 ≤ s) (χ : PontryaginDual K) :
    FractionalMellinTensor μ s →L[ℂ] L² :=
  (mellinFrequencyValues hs).comp
    ((lpTwoCharacterCoefficient χ).comp
      completedLpTwoTensorEquiv.toLinearIsometry.toContinuousLinearMap)

private theorem coefficient_lpTwoProduct (b s : ℝ) (χ : PontryaginDual K)
    (u : Lp ℂ 2 μ) (v : StripSobolev b b s) :
    lpTwoCharacterCoefficient χ (lpTwoProduct u v) = (∫ k, (χ k : ℂ) * u k ∂μ) • v := by
  apply Lp.ext
  let c := ∫ k, (χ k : ℂ) * u k ∂μ
  have hswap : ∀ᵐ p : ℝ × K ∂(stripMeasure b b s).prod μ,
      lpTwoProduct u v (p.2, p.1) = u p.2 * v p.1 :=
    Measure.measurePreserving_swap.quasiMeasurePreserving.ae (lpTwoProduct_ae u v)
  filter_upwards [lpTwoCharacterCoefficient_ae χ (lpTwoProduct u v),
    Measure.ae_ae_of_ae_prod hswap, Lp.coeFn_smul c v] with x h hx hs
  change lpTwoCharacterCoefficient χ (lpTwoProduct u v) x = (c • v) x
  rw [h.2, hs, Pi.smul_apply, smul_eq_mul]
  have he : (fun k => (χ k : ℂ) * lpTwoProduct u v (k, x)) =ᵐ[μ]
      fun k => ((χ k : ℂ) * u k) * v x :=
    hx.mono fun k hk => (congrArg ((χ k : ℂ) * ·) hk).trans (mul_assoc _ _ _).symm
  exact (integral_congr_ae he).trans (integral_mul_const _ _)

/-- Character extraction on a separated weighted product acts on its
compact factor and preserves its radial factor. -/
theorem lpTwoCharacterCoefficient_product (b s : ℝ) (χ : PontryaginDual K)
    (u : Lp ℂ 2 μ) (v : StripSobolev b b s) :
    lpTwoCharacterCoefficient χ (lpTwoProduct u v) = (∫ k, (χ k : ℂ) * u k ∂μ) • v :=
  coefficient_lpTwoProduct μ b s χ u v

set_option maxHeartbeats 1300000 in
private theorem fractionalTensor_coefficient (b s : ℝ) (χ : PontryaginDual K)
    (f : Lp ℂ 2 (μ.prod (stripMeasure b b s))) :
    lpTwoCharacterCoefficient χ (completedLpTwoTensorEquiv (fractionalMellinTensor μ b s f)) =
      fractionalMellinLine b s (lpTwoCharacterCoefficient χ f) := by
  let E := Lp ℂ 2 μ ⊗[ℂ] StripSobolev b b s
  let T : Completion E ≃ₗᵢ[ℂ] Lp ℂ 2 (μ.prod (stripMeasure b b s)) :=
    completedLpTwoTensorEquiv
  let A := TensorProduct.congrIsometry
    (.refl ℂ (Lp ℂ 2 μ)) (fractionalMellinLine b s)
  let L : FractionalMellinTensor μ s →L[ℂ] MellinFrequencySobolev s :=
    (lpTwoCharacterCoefficient χ).comp completedLpTwoTensorEquiv.toLinearIsometry.toContinuousLinearMap
  let R : Lp ℂ 2 (μ.prod (stripMeasure b b s)) →L[ℂ] MellinFrequencySobolev s :=
    (fractionalMellinLine b s).toLinearIsometry.toContinuousLinearMap.comp (lpTwoCharacterCoefficient χ)
  obtain ⟨h, rfl⟩ := T.surjective f
  change L (completionCongrIsometry A (T.symm (T h))) = R (T h)
  rw [LinearIsometryEquiv.symm_apply_apply]
  refine Completion.denseRange_coe.induction_on h
    (isClosed_eq (L.continuous.comp (completionCongrIsometry A).continuous)
      (R.continuous.comp T.continuous)) ?_
  intro x
  let J := L.toLinearMap.comp (Completion.toComplₗᵢ.toLinearMap.comp A.toLinearMap)
  let F := R.toLinearMap.comp (T.toLinearMap.comp Completion.toComplₗᵢ.toLinearMap)
  rw [completionCongrIsometry_coe]
  change J x = F x
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul u v =>
    let v' := fractionalMellinLine b s v
    let C : FractionalMellinTensor μ s ≃ₗᵢ[ℂ] Lp ℂ 2 (μ.prod (stripMeasure 0 0 s)) :=
      completedLpTwoTensorEquiv
    have hC : C (A (u ⊗ₜ[ℂ] v) : FractionalMellinTensor μ s) = lpTwoProduct u v' :=
      completedLpTwoTensorEquiv_tmul u v'
    have hT : T ((u ⊗ₜ[ℂ] v : E) : Completion E) = lpTwoProduct u v :=
      completedLpTwoTensorEquiv_tmul u v
    change lpTwoCharacterCoefficient χ (C (A (u ⊗ₜ[ℂ] v) : FractionalMellinTensor μ s)) =
      fractionalMellinLine b s (lpTwoCharacterCoefficient χ (T ((u ⊗ₜ[ℂ] v : E) : Completion E)))
    rw [hC, hT, coefficient_lpTwoProduct μ 0 s χ, coefficient_lpTwoProduct μ b s χ, map_smul]

/-- The character coordinates of the completed fractional transform agree
with applying the scalar fractional transform to the angular coefficient. -/
theorem fractionalMellinTensorValues_eq (b : ℝ) {s : ℝ} (hs : 0 ≤ s)
    (χ : PontryaginDual K) (f : Lp ℂ 2 (μ.prod (stripMeasure b b s))) :
    fractionalMellinTensorValues μ hs χ (fractionalMellinTensor μ b s f) =
      mellinFrequencyValues hs (fractionalMellinLine b s (lpTwoCharacterCoefficient χ f)) := by
  exact congrArg (mellinFrequencyValues hs) (fractionalTensor_coefficient μ b s χ f)


/-- At an abscissa where the group integrals exist, the characters of the
fractional tensor are the actual Mellin integrals almost everywhere in height. -/
theorem fractionalMellinTensor_values_ae (b : ℝ) {s : ℝ} (hs : 0 ≤ s)
    (χ : PontryaginDual K) (f : Lp ℂ 2 (μ.prod (stripMeasure b b s)))
    (hf : ∀ y : ℝ, Integrable (fun p : K × ℝ =>
      (χ p.1 : ℂ) * f p * mellinEvaluationKernel 0 (⟨b, 2 * Real.pi * y⟩ : ℂ) p.2)
      (μ.prod dx)) :
    (fractionalMellinTensorValues μ hs χ (fractionalMellinTensor μ b s f) : ℝ → ℂ) =ᵐ[dx]
      fun y => ∫ p : K × ℝ,
        (χ p.1 : ℂ) * f p * mellinEvaluationKernel 0 (⟨b, 2 * Real.pi * y⟩ : ℂ) p.2
          ∂μ.prod dx := by
  let g := lpTwoCharacterCoefficient χ f
  let z (y : ℝ) : ℂ := ⟨b, 2 * Real.pi * y⟩
  let F (y : ℝ) (p : K × ℝ) := (χ p.1 : ℂ) * f p * mellinEvaluationKernel 0 (z y) p.2
  have hg : ∀ᵐ x ∂dx, g x = ∫ k, (χ k : ℂ) * f (k, x) ∂μ :=
    (absolutelyContinuous_amplitudeMeasure dx _ (stripSobolevAmplitude_continuous b b s).measurable
      (stripSobolevAmplitude_pos b b s)).ae_le
        ((lpTwoCharacterCoefficient_ae χ f).mono fun _ hx => hx.2)
  have hF (y : ℝ) : (fun x : ℝ => ∫ k, F y (k, x) ∂μ) =ᵐ[dx]
      fun x => g x * mellinEvaluationKernel 0 (z y) x := by
    filter_upwards [hg] with x hx
    change (∫ k, ((χ k : ℂ) * f (k, x)) * mellinEvaluationKernel 0 (z y) x ∂μ) = _
    rw [integral_mul_const, hx]
  have hz : z 0 = (b : ℂ) := by apply Complex.ext <;> simp [z]
  have hgInt : Integrable (fun x : ℝ => Real.exp (b * x) • g x) dx := by
    refine (hf 0).integral_prod_right.congr ((hF 0).trans (.of_forall fun x => ?_))
    change g x * mellinEvaluationKernel 0 (z 0) x = Real.exp (b * x) • g x
    rw [hz, mellinEvaluationKernel, pow_zero, mul_one, ← Complex.ofReal_mul,
      ← Complex.ofReal_exp, Complex.real_smul, mul_comm]
  rw [fractionalMellinTensorValues_eq μ b hs χ f]
  refine (fractionalMellinLine_values_ae b hs g hgInt).trans (.of_forall fun y => ?_)
  change (∫ x, g x * mellinEvaluationKernel 0 (z y) x) = ∫ p, F y p ∂μ.prod dx
  rw [integral_prod_symm (F y) (hf y)]
  exact integral_congr_ae (hF y).symm

/-- On every interior line, the compact-strip trace agrees almost everywhere
with the actual absolutely convergent character Mellin integral. -/
theorem fractionalIntervalTrace_values_ae {a b s : ℝ} (hab : a ≤ b) (hs : 0 ≤ s)
    {t : ℝ} (ht : t ∈ Ioo a b) (χ : PontryaginDual K)
    (f : Lp ℂ 2 (μ.prod (stripMeasure a b s))) :
    (fractionalMellinTensorValues μ hs χ (fractionalIntervalTrace μ hab s
      (Ioo_subset_Icc_self ht) f) : ℝ → ℂ) =ᵐ[dx]
      fun y => ∫ p : K × ℝ,
        (χ p.1 : ℂ) * f p * mellinEvaluationKernel 0 (⟨t, 2 * Real.pi * y⟩ : ℂ) p.2
          ∂μ.prod dx := by
  let z (y : ℝ) : ℂ := ⟨t, 2 * Real.pi * y⟩
  have hm : μ.prod (stripMeasure t t s) ≤ μ.prod (stripMeasure a b s) := by
    rw [modulatedInterval_prod_weightedMeasure μ (a := t) le_rfl,
      modulatedInterval_prod_weightedMeasure μ hab]
    apply withDensity_mono
    exact .of_forall fun p => ENNReal.ofReal_le_ofReal
      (hardySobolevWeight_mono_interval ht.1.le ht.2.le ht.1.le ht.2.le s p.2)
  let g := lpTwoMeasureInclusion hm f
  have hAC : μ.prod dx ≪ μ.prod (stripMeasure t t s) :=
    Measure.AbsolutelyContinuous.rfl.prod (absolutelyContinuous_amplitudeMeasure dx _
      (stripSobolevAmplitude_continuous t t s).measurable (stripSobolevAmplitude_pos t t s))
  have hgf : (g : K × ℝ → ℂ) =ᵐ[μ.prod dx] f := hAC.ae_le (lpTwoMeasureInclusion_ae hm f)
  let u : lpTwoRadialSupport μ (stripMeasure a b s) univ :=
    ⟨f, by change ∀ᵐ p ∂μ.prod (stripMeasure a b s), p.2 ∉ univ → f p = 0; simp⟩
  have hF (y : ℝ) : (fun p : K × ℝ =>
      (χ p.1 : ℂ) * g p * mellinEvaluationKernel 0 (z y) p.2) =ᵐ[μ.prod dx]
      fun p => (χ p.1 : ℂ) * f p * mellinEvaluationKernel 0 (z y) p.2 :=
    hgf.mono fun p hp => congrArg
      (fun q : ℂ => (χ p.1 : ℂ) * q * mellinEvaluationKernel 0 (z y) p.2) hp
  have hi (y : ℝ) : Integrable (fun p : K × ℝ =>
      (χ p.1 : ℂ) * g p * mellinEvaluationKernel 0 (z y) p.2) (μ.prod dx) := by
    have hk : MemLp ((univ : Set ℝ).indicator (mellinEvaluationKernel 0 (z y))) 2
        (stripMeasure (-a) (-b) (-s)) := by
      rw [indicator_univ]
      exact (mellinEvaluationKernel_memLp_iff ht.1.le ht.2.le hs 0).mpr (Or.inl ht)
    obtain ⟨_, hΛ, _⟩ := modulatedInterval_mellinMoment_of_kernel μ a b s isOpen_univ χ 0 (z y) hk
    exact (hΛ u).1.congr (hF y).symm
  change (fractionalMellinTensorValues μ hs χ (fractionalMellinTensor μ t s g) : ℝ → ℂ) =ᵐ[dx] _
  exact (fractionalMellinTensor_values_ae μ t hs χ g hi).trans
    (.of_forall fun y => integral_congr_ae (hF y))

end Character

end Product

end
end Masullo
