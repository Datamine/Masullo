import ModulatedDerivativeTraces
import ModulatedExponentialRadial

open Filter Function MeasureTheory Set Topology UniformSpace
open scoped ENNReal TensorProduct

namespace Masullo

noncomputable section

variable {A : Type*} [NormedAddCommGroup A] [InnerProductSpace ℂ A]

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  (m : G →ₜ* Multiplicative ℝ) [CompactSpace m.toMonoidHom.ker]
  (τ : Multiplicative ℝ →ₜ* G) (hτ : RightInverse τ m)
  (ν : Measure m.toMonoidHom.ker) [ν.IsHaarMeasure] [IsProbabilityMeasure ν]

local notation "K₀" => m.toMonoidHom.ker
local notation "E₀" => ModulatedExponentialInductive m (univ : Set ℝ)

set_option maxHeartbeats 1300000 in
private theorem bruhatMellinMoment_eq_radialTest
    (χ : PontryaginDual K₀) (f : E₀) (g : PositiveRealExponentialDecay (univ : Set ℝ))
    (hg : ∀ x : ℝ, g.val x = ∫ j : K₀, (χ j : ℂ) * f.val ((intervalGroupChart m τ hτ) (j, x)) ∂ν)
    (k : ℕ) (z : ℂ) :
    (∫ x, g.val x * mellinEvaluationKernel k z x) =
      bruhatGroupMellinMoment m τ hτ ν χ f.val k z := by
  let b := z.re
  let e := intervalGroupChart m τ hτ
  have hprof (s : ℝ) :
      (bruhatIntervalEndpointInclusion m τ hτ ν ⟨b, mem_univ b⟩ s f : K₀ × ℝ → ℂ) =ᵐ[ν.prod volume]
        f.val ∘ e :=
    (Measure.AbsolutelyContinuous.rfl.prod (absolutelyContinuous_amplitudeMeasure volume _
      (stripSobolevAmplitude_continuous b b s).measurable (stripSobolevAmplitude_pos b b s))).ae_le
      (bruhatIntervalEndpointInclusion_ae m τ hτ ν ⟨b, mem_univ b⟩ s f)
  let r : ℝ := 2 * (k : ℝ) + 2
  let V := bruhatIntervalEndpointInclusion m τ hτ ν ⟨b, mem_univ b⟩ r f
  let v : lpTwoRadialSupport ν (stripMeasure b b r) univ :=
    ⟨V, by change ∀ᵐ p ∂ν.prod (stripMeasure b b r), p.2 ∉ univ → V p = 0; simp⟩
  have hk : MemLp ((univ : Set ℝ).indicator (mellinEvaluationKernel k z)) 2
      (stripMeasure (-b) (-b) (-r)) := by
    rw [indicator_univ]
    exact (mellinEvaluationKernel_memLp_iff (z := z) le_rfl le_rfl (by dsimp [r]; positivity) k).mpr
      (Or.inr (by dsimp [r]; linarith))
  obtain ⟨_, hL, _⟩ := modulatedInterval_mellinMoment_of_kernel ν b b r isOpen_univ χ k z hk
  let F (p : K₀ × ℝ) := (χ p.1 : ℂ) * f.val (e p) * mellinEvaluationKernel k z p.2
  have hF : Integrable F (ν.prod volume) := (hL v).1.congr <|
    (hprof r).mono fun p hp =>
      congrArg (fun c : ℂ => (χ p.1 : ℂ) * c * mellinEvaluationKernel k z p.2) hp
  change (∫ x, g.val x * mellinEvaluationKernel k z x) =
    bruhatGroupMellinMoment m τ hτ ν χ f.val k z
  have hMP : MeasurePreserving e (ν.prod volume) (modulatedLogMeasure m τ hτ ν) :=
    intervalGroupChart_preserving m τ hτ ν volume
  rw [bruhatGroupMellinMoment, ← hMP.integral_comp e.toMeasurableEquiv.measurableEmbedding]
  calc
    _ = ∫ p, F p ∂ν.prod volume := by
      rw [integral_prod_symm F hF]
      apply integral_congr_ae
      refine .of_forall fun x => ?_
      change g.val x * mellinEvaluationKernel k z x = ∫ j, F (j, x) ∂ν
      rw [hg, ← integral_mul_const]
    _ = _ := by
      apply integral_congr_ae
      refine .of_forall fun p => ?_
      have he : e.symm (e p) = p := e.symm_apply_apply p
      have hlog : modulatedLog m (e p) = p.2 := intervalGroupChart_log m τ hτ p
      change F p = (χ (e.symm (e p)).1 : ℂ) * f.val (e p) *
        mellinEvaluationKernel k z (modulatedLog m (e p))
      rw [he, hlog]

set_option maxHeartbeats 2600000 in
/-- Every original entire-decay Bruhat test gives its actual group Mellin
moment in each of the normalized derivative coordinates. -/
theorem bruhatDerivativeTensor_onTest (hm : IsProperMap m)
    (U : Lp ℂ 2 ν ≃ₗᵢ[ℂ] A) (χ : PontryaginDual K₀) (L : A →L[ℂ] ℂ)
    (hc : ∀ u : Lp ℂ 2 ν, L (U u) = ∫ k, (χ k : ℂ) * u k ∂ν)
    (b : ℝ) (N : ℕ) (k : Fin (N + 1)) (f : E₀) :
    (mellinDerivativeAngularEval L (mellinDerivativeTensor ν U b N
      (modulatedMellinLineEquiv ν b N (bruhatIntervalEndpointInclusion m τ hτ ν
        ⟨b, mem_univ b⟩ (2 * (N : ℝ)) f)) k) : ℝ → ℂ) =ᵐ[volume]
      fun y => (Real.sqrt ((N.choose (k : ℕ) : ℝ) / (2 * Real.pi)) : ℂ) *
        iteratedDeriv (k : ℕ) (bruhatGroupMellinMoment m τ hτ ν χ f.val 0) (⟨b, y⟩ : ℂ) := by
  let e := intervalGroupChart m τ hτ
  let fχ := modulatedDecayRadialRestriction m τ hτ univ (univ_nonempty : (univ : Set ℝ).Nonempty)
    (modulatedDecay_kernelAverage m ν χ univ hm (Function.RightInverse.surjective hτ)
      univ_nonempty f)
  have hfχ (x : ℝ) : fχ.val x = ∫ j : K₀, (χ j : ℂ) * f.val (e (j, x)) ∂ν := by
    dsimp only [fχ]
    rw [modulatedDecayRadialRestriction_apply, modulatedDecay_kernelAverage_apply]
    unfold modulatedKernelAverage
    rw [← integral_inv_eq_self]
    apply integral_congr_ae
    refine .of_forall fun j => ?_
    change (((χ j⁻¹)⁻¹ : Circle) : ℂ) * f.val ((j⁻¹ : K₀).val⁻¹ * τ (Multiplicative.ofAdd x)) =
      (χ j : ℂ) * f.val (τ (Multiplicative.ofAdd x) * j.val)
    have hj : (j⁻¹ : K₀).val = j.val⁻¹ := rfl
    have hχ : χ j⁻¹ = (χ j)⁻¹ := map_inv χ j
    rw [hj, hχ, inv_inv, inv_inv, mul_comm j.val]
  have hprof (s : ℝ) :
      (bruhatIntervalEndpointInclusion m τ hτ ν ⟨b, mem_univ b⟩ s f : K₀ × ℝ → ℂ) =ᵐ[ν.prod volume]
        f.val ∘ e :=
    (Measure.AbsolutelyContinuous.rfl.prod (absolutelyContinuous_amplitudeMeasure volume _
      (stripSobolevAmplitude_continuous b b s).measurable (stripSobolevAmplitude_pos b b s))).ae_le
      (bruhatIntervalEndpointInclusion_ae m τ hτ ν ⟨b, mem_univ b⟩ s f)
  let s := 2 * (N : ℝ)
  let W := bruhatIntervalEndpointInclusion m τ hτ ν ⟨b, mem_univ b⟩ s f
  have hcoeff : lpTwoCharacterCoefficient χ W = weightedLineTest b N fχ := by
    apply Lp.ext
    apply (amplitudeMeasure_absolutelyContinuous volume (stripSobolevAmplitude b b s)).ae_le
    have hAC := absolutelyContinuous_amplitudeMeasure volume _
      (stripSobolevAmplitude_continuous b b s).measurable (stripSobolevAmplitude_pos b b s)
    have hpair := Measure.ae_ae_of_ae_prod
      (Measure.measurePreserving_swap.quasiMeasurePreserving.ae (hprof s))
    filter_upwards [hAC.ae_le (lpTwoCharacterCoefficient_ae χ W), hpair,
      hAC.ae_le (stripSobolevTest_ae univ ⟨b, mem_univ b⟩ ⟨b, mem_univ b⟩ s fχ)]
      with x hx hpair htest
    change weightedLineTest b N fχ x = fχ.val x at htest
    rw [hx.2, htest, hfχ]
    exact integral_congr_ae (hpair.mono fun j hj => congrArg ((χ j : ℂ) * ·) hj)
  change (mellinDerivativeAngularEval L
    (mellinDerivativeTensor ν U b N (modulatedMellinLineEquiv ν b N W) k) : ℝ → ℂ) =ᵐ[volume] _
  rw [modulatedDerivativeTensor_character ν U L χ hc, hcoeff]
  have htest := mellinLineEquiv_onTest_derivative_ae b N fχ k
  rw [mellinLineEquiv_onTest] at htest
  rw [mellinLineIsometry_onTest]
  have hfun : (fun w => mellin (fun t => fχ.val (Real.log t)) w) =
      bruhatGroupMellinMoment m τ hτ ν χ f.val 0 := by
    funext w
    have hh := mellinEvaluation_test_integral fχ 0 w
    rw [iteratedDeriv_zero] at hh
    exact hh.trans (bruhatMellinMoment_eq_radialTest m τ hτ ν χ f fχ hfχ 0 w)
  simpa only [hfun] using htest

/-- The compact angular Plancherel transform gives the actual full family
of group Mellin derivatives. The inverse character converts the usual
conjugated Fourier convention to the manuscript's Mellin convention. -/
theorem bruhatDerivativeTensor_angularPlancherel (hm : IsProperMap m) [ν.WeaklyRegular] :
    ∃ U : Lp ℂ 2 ν ≃ₗᵢ[ℂ] lp (fun _ : PontryaginDual K₀ => ℂ) 2,
      (∀ u χ, U u χ = ∫ j, star (χ j : ℂ) * u j ∂ν) ∧
      ∀ (b : ℝ) (N : ℕ) (k : Fin (N + 1)) (χ : PontryaginDual K₀) (f : E₀),
        (mellinDerivativeAngularEval (lp.evalCLM ℂ (fun _ : PontryaginDual K₀ => ℂ) 2 χ⁻¹) (mellinDerivativeTensor ν U b N
          (modulatedMellinLineEquiv ν b N (bruhatIntervalEndpointInclusion m τ hτ ν
            ⟨b, mem_univ b⟩ (2 * (N : ℝ)) f)) k) : ℝ → ℂ) =ᵐ[volume]
          fun y => (Real.sqrt ((N.choose (k : ℕ) : ℝ) / (2 * Real.pi)) : ℂ) *
            iteratedDeriv (k : ℕ) (bruhatGroupMellinMoment m τ hτ ν χ f.val 0) (⟨b, y⟩ : ℂ) := by
  obtain ⟨U, hU⟩ := exists_compactCharacterPlancherel ν
  refine ⟨U, hU, fun b N k χ f => bruhatDerivativeTensor_onTest m τ hτ ν hm U χ
    (lp.evalCLM ℂ (fun _ : PontryaginDual K₀ => ℂ) 2 χ⁻¹) ?_ b N k f⟩
  intro u
  change U u χ⁻¹ = _
  rw [hU]
  apply integral_congr_ae
  refine .of_forall fun j => ?_
  have hχ : (χ⁻¹) j = (χ j)⁻¹ := rfl
  change star (((χ⁻¹) j : Circle) : ℂ) * u j = (χ j : ℂ) * u j
  rw [hχ, Circle.coe_inv_eq_conj]
  simp


omit [ν.IsHaarMeasure] in
private theorem bruhatEndpointClasses_ae (b t s : ℝ) (f : E₀) :
    (bruhatIntervalEndpointInclusion m τ hτ ν ⟨b, mem_univ b⟩ s f : K₀ × ℝ → ℂ)
      =ᵐ[ν.prod (stripMeasure t t s)] bruhatIntervalEndpointInclusion m τ hτ ν ⟨t, mem_univ t⟩ s f := by
  have hprof (a : ℝ) :
      (bruhatIntervalEndpointInclusion m τ hτ ν ⟨a, mem_univ a⟩ s f : K₀ × ℝ → ℂ)
        =ᵐ[ν.prod volume] f.val ∘ intervalGroupChart m τ hτ :=
    (Measure.AbsolutelyContinuous.rfl.prod (absolutelyContinuous_amplitudeMeasure volume _
      (stripSobolevAmplitude_continuous a a s).measurable (stripSobolevAmplitude_pos a a s))).ae_le
        (bruhatIntervalEndpointInclusion_ae m τ hτ ν ⟨a, mem_univ a⟩ s f)
  exact (Measure.AbsolutelyContinuous.rfl.prod (amplitudeMeasure_absolutelyContinuous volume
    (stripSobolevAmplitude t t s))).ae_le ((hprof b).trans (hprof t).symm)

/-- The completed right-half-line sample of an original finite-norm test
is its original endpoint inclusion at the sampled abscissa. -/
theorem bruhatRightDerivativeSample_onTest (b s : ℝ) (f : E₀)
    (hf : ∀ᵐ p ∂ν.prod (stripMeasure b b s), 0 < p.2 →
      bruhatIntervalEndpointInclusion m τ hτ ν ⟨b, mem_univ b⟩ s f p = 0)
    (t : Ici b) :
    fractionalRightHalfLineTrace ν b s (bruhatIntervalEndpointInclusion m τ hτ ν
      ⟨b, mem_univ b⟩ s f) hf t =
      fractionalMellinTensor ν t s (bruhatIntervalEndpointInclusion m τ hτ ν
        ⟨(t : ℝ), mem_univ _⟩ s f) := by
  unfold fractionalRightHalfLineTrace
  apply congrArg (fractionalMellinTensor ν t s)
  apply Lp.ext
  exact (MemLp.coeFn_toLp _).trans (bruhatEndpointClasses_ae m τ hτ ν b t s f)

/-- The completed left-half-line sample of an original finite-norm test
is its original endpoint inclusion at the sampled abscissa. -/
theorem bruhatLeftDerivativeSample_onTest (b s : ℝ) (f : E₀)
    (hf : ∀ᵐ p ∂ν.prod (stripMeasure b b s), p.2 < 0 →
      bruhatIntervalEndpointInclusion m τ hτ ν ⟨b, mem_univ b⟩ s f p = 0)
    (t : Iic b) :
    fractionalLeftHalfLineTrace ν b s (bruhatIntervalEndpointInclusion m τ hτ ν
      ⟨b, mem_univ b⟩ s f) hf t =
      fractionalMellinTensor ν t s (bruhatIntervalEndpointInclusion m τ hτ ν
        ⟨(t : ℝ), mem_univ _⟩ s f) := by
  unfold fractionalLeftHalfLineTrace
  apply congrArg (fractionalMellinTensor ν t s)
  apply Lp.ext
  exact (MemLp.coeFn_toLp _).trans (bruhatEndpointClasses_ae m τ hτ ν b t s f)

end
end Masullo
