import ModulatedSobolevMain

open Filter Function MeasureTheory Set Topology
open scoped ENNReal NNReal SchwartzMap

namespace Masullo

noncomputable section

variable {K : Type*} [TopologicalSpace K] [CompactSpace K] [T2Space K]
  [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [IsFiniteMeasure μ]

omit [T2Space K] in
private theorem schwartzEvaluate_memLp (F : 𝓢(ℝ, C(K, ℂ))) :
    MemLp (fun p : K × ℝ => F p.2 p.1) 2 (μ.prod (volume : Measure ℝ)) := by
  have hc : Continuous (fun p : K × ℝ => F p.2 p.1) :=
    (F.continuous.comp continuous_snd).eval continuous_fst
  apply (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mpr
  have hI := (memLp_two_iff_integrable_sq_norm (F.memLp 2 volume).aestronglyMeasurable).mp
    (F.memLp 2 volume)
  have hD : Integrable (fun p : K × ℝ => ‖F p.2‖ ^ 2) (μ.prod (volume : Measure ℝ)) := by
    simpa only [one_mul] using (integrable_const (1 : ℝ)).mul_prod hI (μ := μ)
  apply hD.mono' (hc.norm.pow 2).aestronglyMeasurable
  refine Eventually.of_forall fun p => ?_
  change ‖‖F p.2 p.1‖ ^ 2‖ ≤ ‖F p.2‖ ^ 2
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _) ((F p.2).norm_coe_le_norm p.1) 2

private def schwartzEvaluateLinear : 𝓢(ℝ, C(K, ℂ)) →ₗ[ℂ] Lp ℂ 2 (μ.prod (volume : Measure ℝ)) where
  toFun F := (schwartzEvaluate_memLp μ F).toLp _
  map_add' F H := by
    apply Lp.ext
    filter_upwards [(schwartzEvaluate_memLp μ (F + H)).coeFn_toLp,
      (schwartzEvaluate_memLp μ F).coeFn_toLp, (schwartzEvaluate_memLp μ H).coeFn_toLp,
      Lp.coeFn_add ((schwartzEvaluate_memLp μ F).toLp _) ((schwartzEvaluate_memLp μ H).toLp _)]
      with p h hF hH hsum
    exact h.trans (hsum.trans (congrArg₂ (· + ·) hF hH)).symm
  map_smul' c F := by
    apply Lp.ext
    filter_upwards [(schwartzEvaluate_memLp μ (c • F)).coeFn_toLp,
      (schwartzEvaluate_memLp μ F).coeFn_toLp, Lp.coeFn_smul c ((schwartzEvaluate_memLp μ F).toLp _)]
      with p h hF hs
    exact h.trans (hs.trans (congrArg (c • ·) hF)).symm

omit [T2Space K] [MeasurableSpace K] [BorelSpace K] in
private theorem schwartz_l2_norm_sq (F : 𝓢(ℝ, C(K, ℂ))) :
    ‖F.toLp 2 (volume : Measure ℝ)‖ ^ 2 = ∫ x : ℝ, ‖F x‖ ^ 2 := by
  have hf := F.memLp 2 (volume : Measure ℝ)
  change ‖hf.toLp F‖ ^ 2 = _
  rw [Lp.norm_toLp, toReal_eLpNorm hf.aestronglyMeasurable,
    lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num) hf.aestronglyMeasurable]
  have hn : 0 ≤ ∫ x : ℝ, ‖F x‖ ^ 2 := integral_nonneg (fun x => sq_nonneg ‖F x‖)
  simp only [ENNReal.toReal_ofNat]
  rw [show ((2 : ℝ)⁻¹) = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow]
  simpa only [Real.rpow_two] using Real.sq_sqrt hn

omit [T2Space K] in
private theorem schwartzEvaluateLinear_norm (F : 𝓢(ℝ, C(K, ℂ))) :
    ‖schwartzEvaluateLinear μ F‖ ≤ Real.sqrt (μ.real univ) * ‖F.toLp 2 volume‖ := by
  have hsq : ‖schwartzEvaluateLinear μ F‖ ^ 2 ≤
      (Real.sqrt (μ.real univ) * ‖F.toLp 2 volume‖) ^ 2 := by
    change ‖(schwartzEvaluate_memLp μ F).toLp _‖ ^ 2 ≤ _
    rw [norm_sq_toLp_two, mul_pow, Real.sq_sqrt measureReal_nonneg, schwartz_l2_norm_sq]
    have hmass : (∫ _ : K, (1 : ℝ) ∂μ) = μ.real univ := by simp
    rw [← hmass, ← integral_prod_mul]
    exact integral_mono
      ((memLp_two_iff_integrable_sq_norm (schwartzEvaluate_memLp μ F).aestronglyMeasurable).mp
        (schwartzEvaluate_memLp μ F))
      ((integrable_const (μ := μ) (1 : ℝ)).mul_prod
        ((memLp_two_iff_integrable_sq_norm (F.memLp 2 volume).aestronglyMeasurable).mp
          (F.memLp 2 volume)))
      (fun p => by
        simp only [one_mul]
        exact pow_le_pow_left₀ (norm_nonneg _) ((F p.2).norm_coe_le_norm p.1) 2)
  nlinarith [norm_nonneg (schwartzEvaluateLinear μ F),
    mul_nonneg (Real.sqrt_nonneg (μ.real univ)) (norm_nonneg (F.toLp 2 volume))]

/-- Evaluation in the compact angular variable is continuous from the
sup-norm-valued radial Schwartz space into product L². -/
def schwartzEvaluateCLM : 𝓢(ℝ, C(K, ℂ)) →L[ℂ] Lp ℂ 2 (μ.prod (volume : Measure ℝ)) := by
  let L := schwartzEvaluateLinear μ
  refine ⟨L, ?_⟩
  let T := SchwartzMap.toLpCLM ℂ (C(K, ℂ)) 2 (volume : Measure ℝ)
  let p := (normSeminorm ℂ _).comp L
  let q := (normSeminorm ℂ _).comp T.toLinearMap
  have hq : Continuous q := T.continuous.norm
  have hP : Continuous p :=
    Seminorm.continuous_of_le (q := Real.toNNReal (Real.sqrt (μ.real univ)) • q)
      (by
        change Continuous (fun x => (Real.toNNReal (Real.sqrt (μ.real univ)) : ℝ) * q x)
        exact continuous_const.mul hq)
      (fun x => by
        change ‖L x‖ ≤ (Real.toNNReal (Real.sqrt (μ.real univ)) : ℝ) * ‖T x‖
        rw [Real.coe_toNNReal _ (Real.sqrt_nonneg _)]
        exact schwartzEvaluateLinear_norm μ x)
  apply continuous_of_continuousAt_zero L
  rw [ContinuousAt, map_zero, tendsto_zero_iff_norm_tendsto_zero]
  exact hP.tendsto' _ _ (map_zero p)

omit [T2Space K] in
theorem schwartzEvaluateCLM_ae (F : 𝓢(ℝ, C(K, ℂ))) :
    (schwartzEvaluateCLM μ F : K × ℝ → ℂ) =ᵐ[μ.prod (volume : Measure ℝ)]
      fun p => F p.2 p.1 :=
  (schwartzEvaluate_memLp μ F).coeFn_toLp

/-- The chosen Schwartz representative of the logarithmic twist. -/
def modulatedProfileTwist (b : ℝ) (f : modulatedExponentialProfiles (K := K)) :
    𝓢(ℝ, C(K, ℂ)) := (f.property b).choose

omit [T2Space K] [MeasurableSpace K] [BorelSpace K] in
private theorem modulatedProfileTwist_apply (b : ℝ) (f : modulatedExponentialProfiles (K := K)) (x : ℝ) :
    modulatedProfileTwist b f x = (Real.exp (b * x) : ℂ) • f.val x :=
  (f.property b).choose_spec x

/-- The weighted test inclusion is continuous for any topology on the source
for which its radial Schwartz twist at the chosen abscissa is continuous. -/
theorem modulatedExponentialProfile_inclusion_continuous {A : Type*} [TopologicalSpace A]
    (b : ℝ) (N : ℕ) (f : A → modulatedExponentialProfiles (K := K))
    (hf : Continuous (fun a => modulatedProfileTwist b (f a))) :
    Continuous (fun a => modulatedExponentialProfile_inclusion μ b N (f a)) := by
  let s : ℝ := 2 * (N : ℝ)
  let r (x : K × ℝ) := stripSobolevAmplitude b b s x.2
  let W := μ.prod (stripMeasure b b s)
  let U := μ.prod (volume : Measure ℝ)
  have hr : Measurable r := (stripSobolevAmplitude_continuous b b s).measurable.comp measurable_snd
  have hp (x : K × ℝ) : 0 < r x := stripSobolevAmplitude_pos ..
  have he : W = amplitudeMeasure U r := by
    unfold W U stripMeasure amplitudeMeasure
    exact prod_withDensity_right (μ := μ) (ν := (volume : Measure ℝ))
      (g := fun x => ENNReal.ofReal (stripSobolevAmplitude b b s x ^ 2))
      (((stripSobolevAmplitude_continuous b b s).pow 2).measurable.ennreal_ofReal)
  have hid : MeasurePreserving (id : K × ℝ → K × ℝ) (amplitudeMeasure U r) W :=
    ⟨measurable_id, by simpa using he.symm⟩
  let I : Lp ℂ 2 W →ₗᵢ[ℂ] Lp ℂ 2 (amplitudeMeasure U r) :=
    Lp.compMeasurePreservingₗᵢ ℂ id hid
  let J := (amplitudeL2Iso U r hr hp).toLinearIsometry.comp I
  let P (x : ℝ) : ℂ := ((1 + x ^ 2) ^ (s / 4) : ℝ)
  have hP : P.HasTemperateGrowth := Complex.hasTemperateGrowth_ofReal.comp (by
    simpa only [Real.norm_eq_abs, sq_abs] using
      Function.hasTemperateGrowth_one_add_norm_sq_rpow ℝ (s / 4))
  let A := SchwartzMap.smulLeftCLM C(K, ℂ) P
  have hc : Continuous (fun a => schwartzEvaluateCLM μ (A (modulatedProfileTwist b (f a)))) :=
    (schwartzEvaluateCLM μ).continuous.comp (A.continuous.comp hf)
  apply J.isometry.isEmbedding.isInducing.continuous_iff.mpr
  convert hc using 1
  funext a
  apply Lp.ext
  let w := modulatedExponentialProfile_toLp μ b N (f a)
  let F := A (modulatedProfileTwist b (f a))
  change (J w : K × ℝ → ℂ) =ᵐ[U] schwartzEvaluateCLM μ F
  have hW : U ≪ W := he.symm ▸ absolutelyContinuous_amplitudeMeasure U r hr hp
  have hI : (I w : K × ℝ → ℂ) =ᵐ[amplitudeMeasure U r] w :=
    Lp.coeFn_compMeasurePreserving w hid
  filter_upwards [amplitudeL2Iso_ae U r hr hp (I w),
    (absolutelyContinuous_amplitudeMeasure U r hr hp).ae_le hI,
    hW.ae_le (modulatedExponentialProfile_toLp_ae μ b N (f a)),
    (schwartzEvaluate_memLp μ F).coeFn_toLp] with x hx hIw hw hF
  change (J w) x = r x • (I w) x at hx
  change schwartzEvaluateCLM μ F x = F x.2 x.1 at hF
  rw [hx, hIw, hw, hF, show F x.2 = _ from SchwartzMap.smulLeftCLM_apply_apply hP _ _,
    modulatedProfileTwist_apply, ContinuousMap.smul_apply, ContinuousMap.smul_apply, smul_smul]
  simp only [r, P, stripSobolevAmplitude, ite_self, Complex.real_smul, smul_eq_mul,
    Complex.ofReal_mul]
  ring

end
end Masullo
