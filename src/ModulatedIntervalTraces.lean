import ModulatedIntervalGroupEvaluation
import ModulatedSobolevMellin
import ModulatedSobolevNorm

open Filter Function MeasureTheory Set Topology UniformSpace
open scoped ENNReal TensorProduct

namespace Masullo

noncomputable section

variable {X : Type*} [MeasurableSpace X]

/-- Restriction of an L² class to a dominated measure is contractive. -/
def lpTwoMeasureInclusion {μ ν : Measure X} (h : ν ≤ μ) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 ν := by
  let I (f : Lp ℂ 2 μ) := ((Lp.memLp f).mono_measure h).toLp (f : X → ℂ)
  let J : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 ν :=
    { toFun := I
      map_add' := fun f g => Lp.ext (by
        filter_upwards [((Lp.memLp (f + g)).mono_measure h).coeFn_toLp,
          ((Lp.memLp f).mono_measure h).coeFn_toLp, ((Lp.memLp g).mono_measure h).coeFn_toLp,
          h.absolutelyContinuous.ae_le (Lp.coeFn_add f g), Lp.coeFn_add (I f) (I g)]
          with x hfg hf hg h₁ h₂
        exact hfg.trans (h₁.trans (h₂.trans (congrArg₂ (· + ·) hf hg)).symm))
      map_smul' := fun c f => Lp.ext (by
        filter_upwards [((Lp.memLp (c • f)).mono_measure h).coeFn_toLp,
          ((Lp.memLp f).mono_measure h).coeFn_toLp,
          h.absolutelyContinuous.ae_le (Lp.coeFn_smul c f), Lp.coeFn_smul c (I f)]
          with x hcf hf h₁ h₂
        exact hcf.trans (h₁.trans (h₂.trans (congrArg (c • ·) hf)).symm)) }
  refine J.mkContinuous 1 (fun f => ?_)
  change ‖I f‖ ≤ 1 * ‖f‖
  rw [one_mul, show I f = _ from rfl, Lp.norm_toLp, Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.memLp f).eLpNorm_lt_top.ne (eLpNorm_mono_measure _ h)

theorem lpTwoMeasureInclusion_ae {μ ν : Measure X} (h : ν ≤ μ) (f : Lp ℂ 2 μ) :
    (lpTwoMeasureInclusion h f : X → ℂ) =ᵐ[ν] f :=
  ((Lp.memLp f).mono_measure h).coeFn_toLp

theorem lpTwoMeasureInclusion_norm_le {μ ν : Measure X} (h : ν ≤ μ) (f : Lp ℂ 2 μ) :
    ‖lpTwoMeasureInclusion h f‖ ≤ ‖f‖ := by
  change ‖((Lp.memLp f).mono_measure h).toLp (f : X → ℂ)‖ ≤ _
  rw [Lp.norm_toLp, Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.memLp f).eLpNorm_lt_top.ne (eLpNorm_mono_measure _ h)

theorem lpTwoMeasureInclusion_sq {μ ν : Measure X} (h : ν ≤ μ) (f : Lp ℂ 2 μ) :
    ‖lpTwoMeasureInclusion h f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂ν :=
  norm_sq_toLp_two ((Lp.memLp f).mono_measure h)

theorem lpTwo_norm_sq_le_endpoints {A B W : Measure X} (ha : A ≤ W) (hb : B ≤ W)
    (hW : W ≤ A + B) (f : Lp ℂ 2 W) :
    ‖f‖ ^ 2 ≤ ‖lpTwoMeasureInclusion ha f‖ ^ 2 + ‖lpTwoMeasureInclusion hb f‖ ^ 2 := by
  have ha' := (Lp.memLp f).mono_measure ha
  have hb' := (Lp.memLp f).mono_measure hb
  have hiA := (memLp_two_iff_integrable_sq_norm ha'.aestronglyMeasurable).mp ha'
  have hiB := (memLp_two_iff_integrable_sq_norm hb'.aestronglyMeasurable).mp hb'
  have hw := norm_sq_toLp_two (Lp.memLp f)
  rw [Lp.toLp_coeFn] at hw
  rw [hw, lpTwoMeasureInclusion_sq ha, lpTwoMeasureInclusion_sq hb, ← integral_add_measure hiA hiB]
  exact integral_mono_measure hW (.of_forall fun x => sq_nonneg ‖f x‖) (hiA.add_measure hiB)

private theorem hardySobolevWeight_le_endpoint_sum (a b s x : ℝ) :
    hardySobolevWeight a b s x ≤ hardySobolevWeight a a s x + hardySobolevWeight b b s x := by
  unfold hardySobolevWeight
  simp only [max_self, ← add_mul]
  exact mul_le_mul_of_nonneg_right
    (max_le (le_add_of_nonneg_right (Real.exp_nonneg _)) (le_add_of_nonneg_left (Real.exp_nonneg _)))
    (Real.rpow_nonneg (by positivity) _)

/-- The interval weight is between each endpoint weight and their sum. -/
theorem hardySobolevMeasure_endpoint_comparison (μ : Measure X) {ℓ : X → ℝ}
    (hℓ : Measurable ℓ) {a b : ℝ} (hab : a ≤ b) (s : ℝ) :
    hardySobolevMeasure μ ℓ a a s ≤ hardySobolevMeasure μ ℓ a b s ∧
    hardySobolevMeasure μ ℓ b b s ≤ hardySobolevMeasure μ ℓ a b s ∧
    hardySobolevMeasure μ ℓ a b s ≤
      hardySobolevMeasure μ ℓ a a s + hardySobolevMeasure μ ℓ b b s := by
  unfold hardySobolevMeasure
  refine ⟨withDensity_mono (.of_forall fun x => ENNReal.ofReal_le_ofReal
    (hardySobolevWeight_mono_interval le_rfl hab le_rfl hab s (ℓ x))),
    withDensity_mono (.of_forall fun x => ENNReal.ofReal_le_ofReal
      (hardySobolevWeight_mono_interval hab le_rfl hab le_rfl s (ℓ x))), ?_⟩
  rw [← withDensity_add_left (show Measurable (fun x => ENNReal.ofReal (hardySobolevWeight a a s (ℓ x))) from
    ((continuous_hardySobolevWeight a a s).measurable.comp hℓ).ennreal_ofReal)]
  exact withDensity_mono (.of_forall fun x =>
    (ENNReal.ofReal_le_ofReal (hardySobolevWeight_le_endpoint_sum a b s (ℓ x))).trans
      ENNReal.ofReal_add_le)

section Product

variable {K : Type*} [MeasurableSpace K] (μ : Measure K)

theorem modulatedInterval_endpointMeasures {a b : ℝ} (hab : a ≤ b) (s : ℝ) :
    μ.prod (stripMeasure a a s) ≤ μ.prod (stripMeasure a b s) ∧
    μ.prod (stripMeasure b b s) ≤ μ.prod (stripMeasure a b s) ∧
    μ.prod (stripMeasure a b s) ≤ μ.prod (stripMeasure a a s) + μ.prod (stripMeasure b b s) := by
  rw [modulatedInterval_prod_weightedMeasure μ hab,
    modulatedInterval_prod_weightedMeasure μ (a := a) le_rfl,
    modulatedInterval_prod_weightedMeasure μ (a := b) le_rfl]
  exact hardySobolevMeasure_endpoint_comparison (μ.prod volume) measurable_snd hab s

variable [SFinite μ]

local notation "LineTensor[" t "," n "]" =>
  Completion (Lp ℂ 2 μ ⊗[ℂ] MellinLineCompletion t n)

/-- Each completed Mellin endpoint is the actual line isometry after
restricting the interval class to the endpoint measure. -/
def modulatedIntervalMellinLine {a b : ℝ} (hab : a ≤ b) (N : ℕ) {t : ℝ} (ht : t ∈ Icc a b) :
    Lp ℂ 2 (μ.prod (stripMeasure a b (2 * (N : ℝ)))) →L[ℂ] LineTensor[t, N] :=
  (modulatedMellinLineEquiv μ t N).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (lpTwoMeasureInclusion (by
      rw [modulatedInterval_prod_weightedMeasure μ (a := t) le_rfl,
        modulatedInterval_prod_weightedMeasure μ hab]
      apply withDensity_mono
      exact .of_forall fun p => ENNReal.ofReal_le_ofReal
        (hardySobolevWeight_mono_interval ht.1 ht.2 ht.1 ht.2 _ p.2)))

theorem modulatedIntervalMellinLine_norm_le {a b : ℝ} (hab : a ≤ b) (N : ℕ)
    {t : ℝ} (ht : t ∈ Icc a b) (f : Lp ℂ 2 (μ.prod (stripMeasure a b (2 * (N : ℝ))))) :
    ‖modulatedIntervalMellinLine μ hab N ht f‖ ≤ ‖f‖ := by
  unfold modulatedIntervalMellinLine
  rw [ContinuousLinearMap.comp_apply]
  change ‖modulatedMellinLineEquiv μ t N _‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  exact lpTwoMeasureInclusion_norm_le _ f

/-- The two endpoint traces form a closed embedding with a bounded inverse
on their range. The squared endpoint energies dominate the interval energy. -/
theorem modulatedIntervalMellin_endpoints (a b : ℝ) (hab : a ≤ b) (N : ℕ) :
    let Mₐ := modulatedIntervalMellinLine μ hab N (left_mem_Icc.mpr hab)
    let Mᵦ := modulatedIntervalMellinLine μ hab N (right_mem_Icc.mpr hab)
    let J := Mₐ.prod Mᵦ
    IsClosedEmbedding J ∧ (∀ f, ‖J f‖ ≤ ‖f‖) ∧
      ∀ f, ‖f‖ ^ 2 ≤ ‖Mₐ f‖ ^ 2 + ‖Mᵦ f‖ ^ 2 := by
  intro Mₐ Mᵦ J
  have hlow (f : Lp ℂ 2 (μ.prod (stripMeasure a b (2 * (N : ℝ))))) :
      ‖f‖ ^ 2 ≤ ‖Mₐ f‖ ^ 2 + ‖Mᵦ f‖ ^ 2 := by
    obtain ⟨ha, hb, hW⟩ := modulatedInterval_endpointMeasures μ hab (2 * (N : ℝ))
    change ‖f‖ ^ 2 ≤ ‖modulatedMellinLineEquiv μ a N (lpTwoMeasureInclusion ha f)‖ ^ 2 +
      ‖modulatedMellinLineEquiv μ b N (lpTwoMeasureInclusion hb f)‖ ^ 2
    simp only [LinearIsometryEquiv.norm_map]
    exact lpTwo_norm_sq_le_endpoints ha hb hW f
  have hmax (f : Lp ℂ 2 (μ.prod (stripMeasure a b (2 * (N : ℝ))))) : ‖f‖ ≤ 2 * ‖J f‖ := by
    have ha : ‖Mₐ f‖ ≤ ‖J f‖ := le_max_left _ _
    have hb : ‖Mᵦ f‖ ≤ ‖J f‖ := le_max_right _ _
    nlinarith [hlow f,
      pow_le_pow_left₀ (norm_nonneg _) ha 2, pow_le_pow_left₀ (norm_nonneg _) hb 2,
      norm_nonneg f, norm_nonneg (J f)]
  have hJ : AntilipschitzWith 2 J := AntilipschitzWith.of_le_mul_dist fun x y => by
    simpa only [dist_eq_norm, map_sub, NNReal.coe_ofNat] using hmax (x - y)
  refine ⟨hJ.isClosedEmbedding J.uniformContinuous, ?_, hlow⟩
  intro f
  exact max_le (modulatedIntervalMellinLine_norm_le μ hab N _ f)
    (modulatedIntervalMellinLine_norm_le μ hab N _ f)


/-- The closed space of compatible pairs of completed endpoint traces. -/
def modulatedIntervalEndpointSpace (a b : ℝ) (hab : a ≤ b) (N : ℕ) :
    Submodule ℂ (LineTensor[a, N] × LineTensor[b, N]) :=
  ((modulatedIntervalMellinLine μ hab N (left_mem_Icc.mpr hab)).prod
    (modulatedIntervalMellinLine μ hab N (right_mem_Icc.mpr hab))).toLinearMap.range

/-- Mellin transformation on both endpoint lines is a topological isomorphism
onto the compatible trace pairs. -/
def modulatedIntervalEndpointEquiv (a b : ℝ) (hab : a ≤ b) (N : ℕ) :
    Lp ℂ 2 (μ.prod (stripMeasure a b (2 * (N : ℝ)))) ≃L[ℂ]
      modulatedIntervalEndpointSpace μ a b hab N := by
  let J := (modulatedIntervalMellinLine μ hab N (left_mem_Icc.mpr hab)).prod
    (modulatedIntervalMellinLine μ hab N (right_mem_Icc.mpr hab))
  have hJ : IsClosedEmbedding J := (modulatedIntervalMellin_endpoints μ a b hab N).1
  let e := LinearEquiv.ofInjective J.toLinearMap hJ.injective
  refine ⟨e, J.continuous.subtype_mk _, ?_⟩
  apply hJ.isEmbedding.isInducing.continuous_iff.mpr
  have hcomp : (fun x => J (e.symm x)) = Subtype.val :=
    funext fun x => congrArg Subtype.val (e.apply_symm_apply x)
  change Continuous (fun x => J (e.symm x))
  rw [hcomp]
  exact continuous_subtype_val

theorem modulatedIntervalEndpointSpace_closed (a b : ℝ) (hab : a ≤ b) (N : ℕ) :
    IsClosed (modulatedIntervalEndpointSpace μ a b hab N :
      Set (LineTensor[a, N] × LineTensor[b, N])) :=
  ((modulatedIntervalMellin_endpoints μ a b hab N).1).isClosed_range

/-- The squared weighted energy on a vertical line of an interval class. -/
def intervalWeightedLineEnergy (a b s : ℝ)
    (f : Lp ℂ 2 (μ.prod (stripMeasure a b s))) (t : ℝ) : ℝ :=
  ∫ p : K × ℝ, hardySobolevWeight t t s p.2 * ‖f p‖ ^ 2 ∂μ.prod volume

/-- The same line energy at even Sobolev order. -/
abbrev modulatedIntervalLineEnergy (a b : ℝ) (N : ℕ) :=
  intervalWeightedLineEnergy μ a b (2 * (N : ℝ))

theorem modulatedIntervalLineEnergy_eq_norm_sq {a b : ℝ} (hab : a ≤ b) (N : ℕ)
    {t : ℝ} (ht : t ∈ Icc a b) (f : Lp ℂ 2 (μ.prod (stripMeasure a b (2 * (N : ℝ))))) :
    modulatedIntervalLineEnergy μ a b N f t = ‖modulatedIntervalMellinLine μ hab N ht f‖ ^ 2 := by
  unfold modulatedIntervalMellinLine
  rw [ContinuousLinearMap.comp_apply]
  change _ = ‖modulatedMellinLineEquiv μ t N (lpTwoMeasureInclusion _ f)‖ ^ 2
  rw [LinearIsometryEquiv.norm_map, lpTwoMeasureInclusion_sq]
  let W := hardySobolevWeight t t (2 * (N : ℝ))
  have hW : Measurable (fun p : K × ℝ => ENNReal.ofReal (W p.2)) :=
    ((continuous_hardySobolevWeight t t _).measurable.comp measurable_snd).ennreal_ofReal
  rw [modulatedInterval_prod_weightedMeasure μ (a := t) le_rfl]
  change _ = ∫ p : K × ℝ, ‖f p‖ ^ 2 ∂(μ.prod volume).withDensity (fun p => ENNReal.ofReal (W p.2))
  rw [integral_withDensity_eq_integral_toReal_smul hW (.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [modulatedIntervalLineEnergy, intervalWeightedLineEnergy, ENNReal.toReal_ofReal (hardySobolevWeight_nonneg ..),
    W, smul_eq_mul]

omit [SFinite μ] in
theorem intervalWeightedLineEnergy_continuousOn {a b : ℝ} (hab : a ≤ b) (s : ℝ)
    (f : Lp ℂ 2 (μ.prod (stripMeasure a b s))) :
    ContinuousOn (intervalWeightedLineEnergy μ a b s f) (Icc a b) := by
  let H (p : K × ℝ) := hardySobolevWeight a b s p.2 * ‖f p‖ ^ 2
  have hI : Integrable H (μ.prod volume) := by
    let v : K × ℝ → ℂ := f
    have h : MemLp v 2 (μ.prod (stripMeasure a b s)) := Lp.memLp f
    rw [modulatedInterval_prod_weightedMeasure μ hab] at h
    exact (integrable_hardySobolev_sq_iff (μ.prod volume) measurable_snd a b s v).mp
      ((memLp_two_iff_integrable_sq_norm h.aestronglyMeasurable).mp h)
  have hfae : AEStronglyMeasurable (f : K × ℝ → ℂ) (μ.prod volume) :=
    (Lp.aestronglyMeasurable f).mono_ac
      (Measure.AbsolutelyContinuous.rfl.prod
        (absolutelyContinuous_amplitudeMeasure volume _
          (stripSobolevAmplitude_continuous a b s).measurable (stripSobolevAmplitude_pos a b s)))
  intro t ht
  refine tendsto_integral_filter_of_dominated_convergence H ?_ ?_ hI ?_
  · refine .of_forall fun v => ?_
    have hw : AEStronglyMeasurable (fun p : K × ℝ => hardySobolevWeight v v s p.2)
        (μ.prod volume) :=
      ((continuous_hardySobolevWeight v v s).measurable.comp measurable_snd).aestronglyMeasurable
    exact hw.mul (hfae.norm.pow 2)
  · filter_upwards [self_mem_nhdsWithin] with v hv
    refine .of_forall fun p => ?_
    rw [Real.norm_of_nonneg (mul_nonneg (hardySobolevWeight_nonneg ..) (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_right
      (hardySobolevWeight_mono_interval hv.1 hv.2 hv.1 hv.2 s p.2) (sq_nonneg _)
  · refine .of_forall fun p => ?_
    have hc : Continuous (fun t : ℝ => Real.exp (2 * t * p.2) *
        ((1 + p.2 ^ 2) ^ (s / 2)) * ‖f p‖ ^ 2) := by fun_prop
    simpa only [hardySobolevWeight, max_self] using
      (show Tendsto (fun v : ℝ => Real.exp (2 * v * p.2) *
          ((1 + p.2 ^ 2) ^ (s / 2)) * ‖f p‖ ^ 2) (𝓝[Icc a b] t) (𝓝 _) from
        hc.continuousAt.continuousWithinAt)

omit [SFinite μ] in
theorem modulatedIntervalLineEnergy_continuousOn {a b : ℝ} (hab : a ≤ b) (N : ℕ)
    (f : Lp ℂ 2 (μ.prod (stripMeasure a b (2 * (N : ℝ))))) :
    ContinuousOn (modulatedIntervalLineEnergy μ a b N f) (Icc a b) :=
  intervalWeightedLineEnergy_continuousOn μ hab _ f

/-- Approaching the endpoints suffices when the sampled energies are
controlled uniformly. Each sampled trace is also bounded by the interval norm. -/
theorem modulatedInterval_uniformSamples_bound {a b : ℝ} (hab : a ≤ b)
    (A : Set ℝ) (hAI : A ⊆ Icc a b) (ha : a ∈ closure A) (hb : b ∈ closure A)
    (N : ℕ) (f : Lp ℂ 2 (μ.prod (stripMeasure a b (2 * (N : ℝ))))) (C : ℝ)
    (hC : ∀ t ∈ A, modulatedIntervalLineEnergy μ a b N f t ≤ C) :
    ‖f‖ ^ 2 ≤ 2 * C := by
  let E := modulatedIntervalLineEnergy μ a b N f
  have hClosed : IsClosed {x ∈ Icc a b | E x ≤ C} := (isClosed_Icc : IsClosed (Icc a b)).isClosed_le
    (modulatedIntervalLineEnergy_continuousOn μ hab N f) continuousOn_const
  have he : closure A ⊆ {x ∈ Icc a b | E x ≤ C} :=
    closure_minimal (fun x hx => ⟨hAI hx, hC x hx⟩) hClosed
  obtain ⟨_, _, h⟩ := modulatedIntervalMellin_endpoints μ a b hab N
  have h' := h f
  rw [← modulatedIntervalLineEnergy_eq_norm_sq μ hab N (left_mem_Icc.mpr hab),
    ← modulatedIntervalLineEnergy_eq_norm_sq μ hab N (right_mem_Icc.mpr hab)] at h'
  exact h'.trans (by simpa only [two_mul] using add_le_add (he ha).2 (he hb).2)

/-- Uniform control of the sampled line energies measures precisely
convergence in the compact interval norm. -/
theorem modulatedInterval_uniformSamples_tendsto_iff {a b : ℝ} (hab : a ≤ b)
    (A : Set ℝ) (hAI : A ⊆ Icc a b) (ha : a ∈ closure A) (hb : b ∈ closure A)
    (N : ℕ) {ι : Type*} {l : Filter ι}
    (f : ι → Lp ℂ 2 (μ.prod (stripMeasure a b (2 * (N : ℝ))))) :
    Tendsto (fun i => ‖f i‖) l (𝓝 0) ↔
      Tendsto (fun i => sSup (modulatedIntervalLineEnergy μ a b N (f i) '' A)) l (𝓝 0) := by
  have hne : A.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty.mp h, closure_empty] at ha
    exact ha
  let E i := modulatedIntervalLineEnergy μ a b N (f i)
  have hu i (t : ℝ) (ht : t ∈ A) : E i t ≤ ‖f i‖ ^ 2 := by
    dsimp only [E]
    rw [modulatedIntervalLineEnergy_eq_norm_sq μ hab N (hAI ht)]
    exact pow_le_pow_left₀ (norm_nonneg _) (modulatedIntervalMellinLine_norm_le μ hab N (hAI ht) _) 2
  have hbd i : BddAbove (E i '' A) := ⟨‖f i‖ ^ 2, by
    rintro _ ⟨t, ht, rfl⟩
    exact hu i t ht⟩
  have hlo i : 0 ≤ sSup (E i '' A) := by
    obtain ⟨t, ht⟩ := hne
    refine le_trans ?_ (le_csSup (hbd i) (mem_image_of_mem _ ht))
    dsimp only [E]
    rw [modulatedIntervalLineEnergy_eq_norm_sq μ hab N (hAI ht)]
    positivity
  constructor
  · intro hf
    exact squeeze_zero hlo (fun i => csSup_le (hne.image (E i)) (by
      rintro _ ⟨t, ht, rfl⟩
      exact hu i t ht)) (by simpa using hf.pow 2)
  · intro h
    have ht : Tendsto (fun i => Real.sqrt (2 * sSup (E i '' A))) l (𝓝 0) := by
      simpa using (h.const_mul 2).sqrt
    refine squeeze_zero (fun i => norm_nonneg _) (fun i => ?_) ht
    apply (Real.le_sqrt (norm_nonneg _) (mul_nonneg (by norm_num) (hlo i))).mpr
    exact modulatedInterval_uniformSamples_bound μ hab A hAI ha hb N (f i) _
      (fun t ht => le_csSup (hbd i) (mem_image_of_mem _ ht))

end Product
end
end Masullo
