import FractionalMellinBoundary
import HardySobolevHolomorphic

open Filter Function MeasureTheory Set Topology

namespace Masullo

noncomputable section

local notation "dx" => (volume : Measure ℝ)

/-- Restriction of the scalar weighted interval class to an abscissa. -/
theorem scalarInterval_lineMeasure_le {a b t : ℝ} (hab : a ≤ b) (ht : t ∈ Icc a b) (s : ℝ) :
    stripMeasure t t s ≤ stripMeasure a b s := by
  rw [stripMeasure_eq _ _ _ le_rfl, stripMeasure_eq _ _ _ hab]
  exact withDensity_mono (.of_forall fun x => ENNReal.ofReal_le_ofReal
    (hardySobolevWeight_mono_interval ht.1 ht.2 ht.1 ht.2 s x))

private theorem scalarInterval_endpoint_sum {a b : ℝ} (hab : a ≤ b) (s : ℝ) :
    stripMeasure a b s ≤ stripMeasure a a s + stripMeasure b b s := by
  rw [stripMeasure_eq a b s hab, stripMeasure_eq a a s le_rfl, stripMeasure_eq b b s le_rfl]
  exact (hardySobolevMeasure_endpoint_comparison dx measurable_id hab s).2.2

/-- Scalar fractional Mellin trace, with its Sobolev norm and Fourier
evaluation as in the general trace model. -/
def scalarFractionalTrace {a b t : ℝ} (hab : a ≤ b) (ht : t ∈ Icc a b) (s : ℝ) :
    StripSobolev a b s →L[ℂ] MellinFrequencySobolev s :=
  (fractionalMellinLine t s).toLinearIsometry.toContinuousLinearMap.comp
    (lpTwoMeasureInclusion (scalarInterval_lineMeasure_le hab ht s))

theorem scalarFractionalTrace_ae {a b t : ℝ} (hab : a ≤ b) (ht : t ∈ Icc a b)
    (s : ℝ) (f : StripSobolev a b s) :
    (scalarFractionalTrace hab ht s f : ℝ → ℂ) =ᵐ[dx] fun x => Real.exp (t * x) • f x := by
  let q := scalarInterval_lineMeasure_le hab ht s
  have hf : (lpTwoMeasureInclusion q f : ℝ → ℂ) =ᵐ[dx] f :=
    (absolutelyContinuous_amplitudeMeasure dx _ (stripSobolevAmplitude_continuous t t s).measurable
      (stripSobolevAmplitude_pos t t s)).ae_le (lpTwoMeasureInclusion_ae q f)
  exact (fractionalMellinLine_ae t s (lpTwoMeasureInclusion q f)).trans
    (hf.mono fun x hx => congrArg (Real.exp (t * x) • ·) hx)

theorem scalarFractionalTrace_norm_le {a b t : ℝ} (hab : a ≤ b) (ht : t ∈ Icc a b)
    (s : ℝ) (f : StripSobolev a b s) :
    ‖scalarFractionalTrace hab ht s f‖ ≤ ‖f‖ := by
  change ‖fractionalMellinLine t s (lpTwoMeasureInclusion _ f)‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  exact lpTwoMeasureInclusion_norm_le _ f

def scalarFractionalEndpointPair {a b : ℝ} (hab : a ≤ b) (s : ℝ) :
    StripSobolev a b s →L[ℂ] MellinFrequencySobolev s × MellinFrequencySobolev s :=
  (scalarFractionalTrace hab (left_mem_Icc.mpr hab) s).prod
    (scalarFractionalTrace hab (right_mem_Icc.mpr hab) s)

theorem scalarFractionalEndpointPair_closedEmbedding {a b : ℝ} (hab : a ≤ b) (s : ℝ) :
    IsClosedEmbedding (scalarFractionalEndpointPair hab s) := by
  let L := scalarFractionalTrace hab (left_mem_Icc.mpr hab) s
  let R := scalarFractionalTrace hab (right_mem_Icc.mpr hab) s
  let M := scalarFractionalEndpointPair hab s
  have h (f : StripSobolev a b s) : ‖f‖ ^ 2 ≤ ‖L f‖ ^ 2 + ‖R f‖ ^ 2 := by
    change ‖f‖ ^ 2 ≤ ‖fractionalMellinLine a s (lpTwoMeasureInclusion _ f)‖ ^ 2 +
      ‖fractionalMellinLine b s (lpTwoMeasureInclusion _ f)‖ ^ 2
    simp only [LinearIsometryEquiv.norm_map]
    exact lpTwo_norm_sq_le_endpoints _ _ (scalarInterval_endpoint_sum hab s) f
  have hbound (f : StripSobolev a b s) : ‖f‖ ≤ 2 * ‖M f‖ := by
    have hL : ‖L f‖ ≤ ‖M f‖ := le_max_left _ _
    have hR : ‖R f‖ ≤ ‖M f‖ := le_max_right _ _
    nlinarith [h f, pow_le_pow_left₀ (norm_nonneg _) hL 2,
      pow_le_pow_left₀ (norm_nonneg _) hR 2, norm_nonneg f, norm_nonneg (M f)]
  have hM : AntilipschitzWith 2 M := AntilipschitzWith.of_le_mul_dist fun f g => by
    simpa only [dist_eq_norm, map_sub, NNReal.coe_ofNat] using hbound (f - g)
  exact hM.isClosedEmbedding M.uniformContinuous

/-- The analytic compact scalar model consists of compatible fractional
endpoint traces. A singleton base is represented by a repeated line. -/
def scalarFractionalInterval (a b : ℝ) (hab : a ≤ b) (s : ℝ) :
    Submodule ℂ (MellinFrequencySobolev s × MellinFrequencySobolev s) :=
  (scalarFractionalEndpointPair hab s).toLinearMap.range

def scalarFractionalIntervalEquiv {a b : ℝ} (hab : a ≤ b) (s : ℝ) :
    StripSobolev a b s ≃L[ℂ] scalarFractionalInterval a b hab s := by
  let M := scalarFractionalEndpointPair hab s
  have hM : IsClosedEmbedding M := scalarFractionalEndpointPair_closedEmbedding hab s
  let e := LinearEquiv.ofInjective M.toLinearMap hM.injective
  refine ⟨e, M.continuous.subtype_mk _, ?_⟩
  apply hM.isEmbedding.isInducing.continuous_iff.mpr
  have hcomp : (fun x => M (e.symm x)) = Subtype.val :=
    funext fun x => congrArg Subtype.val (e.apply_symm_apply x)
  change Continuous (fun x => M (e.symm x))
  rw [hcomp]
  exact continuous_subtype_val

/-- The zeroth Fourier coordinate of the trace of a scalar exponential test
is the genuine scalar Mellin integral, at the $2π$ normalization of height. -/
theorem scalarFractionalTrace_onTest {J : Set ℝ} (a b t : J) (hab : (a : ℝ) ≤ b)
    (ht : (t : ℝ) ∈ Icc (a : ℝ) b) {s : ℝ} (hs : 0 ≤ s) (f : PositiveRealExponentialDecay J) :
    (mellinFrequencyValues hs
      (scalarFractionalTrace hab ht s (stripSobolevTest J a b s f)) : ℝ → ℂ) =ᵐ[dx]
      fun y => cutoffMellinIntegral f.val 0 (⟨(t : ℝ), 2 * Real.pi * y⟩ : ℂ) := by
  let u := stripSobolevTest J a b s f
  let h := scalarInterval_lineMeasure_le hab ht s
  let v := lpTwoMeasureInclusion h u
  have hv : (v : ℝ → ℂ) =ᵐ[dx] f.val :=
    (absolutelyContinuous_amplitudeMeasure dx _ (stripSobolevAmplitude_continuous t t s).measurable
      (stripSobolevAmplitude_pos t t s)).ae_le
      ((lpTwoMeasureInclusion_ae h u).trans (h.absolutelyContinuous.ae_le (stripSobolevTest_ae J a b s f)))
  have hg : Integrable (fun x : ℝ => Real.exp ((t : ℝ) * x) • f.val x) dx := by
    exact (logExponentialDecayTwist J t f).integrable.congr
      (.of_forall fun x => (logExponentialDecayTwist_apply J t f x).trans Complex.real_smul.symm)
  refine (fractionalMellinLine_values_ae t hs v (hg.congr (hv.symm.mono fun x hx =>
    congrArg (Real.exp ((t : ℝ) * x) • ·) hx))).trans (.of_forall fun y => ?_)
  exact integral_congr_ae (hv.mono fun x hx =>
    congrArg (fun z : ℂ => z * mellinEvaluationKernel 0 (⟨(t : ℝ), 2 * Real.pi * y⟩ : ℂ) x) hx)


theorem scalarFractionalTrace_onTest_mellin {J : Set ℝ} (a b t : J) (hab : (a : ℝ) ≤ b)
    (ht : (t : ℝ) ∈ Icc (a : ℝ) b) {s : ℝ} (hs : 0 ≤ s) (f : PositiveRealExponentialDecay J) :
    (mellinFrequencyValues hs
      (scalarFractionalTrace hab ht s (stripSobolevTest J a b s f)) : ℝ → ℂ) =ᵐ[dx]
      fun y => mellin (fun r => f.val (Real.log r)) (⟨(t : ℝ), 2 * Real.pi * y⟩ : ℂ) := by
  refine (scalarFractionalTrace_onTest a b t hab ht hs f).trans (.of_forall fun y => ?_)
  simp only [cutoffMellinIntegral, mellin_eq_log_integral, Real.log_exp, mellinEvaluationKernel,
    pow_zero, mul_one]
  exact integral_congr_ae (.of_forall fun _ => mul_comm _ _)

end
end Masullo
