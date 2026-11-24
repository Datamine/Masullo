import CutoffTraceAsymptotic
import CutoffConvolutionKernel
import ModulatedIntervalGroupEvaluation

open Filter Function MeasureTheory Set Topology
open scoped ENNReal Pointwise InnerProductSpace

namespace Masullo

noncomputable section

/-- At a continuity point, averages over positive finite windows shrinking
to that point converge to the pointwise value. -/
theorem cutoff_setAverage_tendsto_at_continuity {X ι : Type*} [TopologicalSpace X]
    [MeasurableSpace X] (μ : Measure X) {l : Filter ι} {x : X} {f : X → ℂ}
    (hf : ContinuousAt f x) (hfm : AEStronglyMeasurable f μ) (V : ι → Set X)
    (hV : ∀ᶠ n in l, μ (V n) ≠ 0 ∧ μ (V n) ≠ ∞ ∧ MeasurableSet (V n))
    (hsmall : ∀ W ∈ 𝓝 x, ∀ᶠ n in l, V n ⊆ W) :
    Tendsto (fun n => ⨍ y in V n, f y ∂μ) l (𝓝 (f x)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hB : {y | dist (f y) (f x) < ε / 2} ∈ 𝓝 x :=
    hf.tendsto (Metric.ball_mem_nhds _ (half_pos hε))
  filter_upwards [hV, hsmall _ hB] with n hn hs
  have hb (y : X) (hy : y ∈ V n) : ‖f y - f x‖ ≤ ε / 2 := by
    rw [← dist_eq_norm]
    exact (show dist (f y) (f x) < ε / 2 from hs hy).le
  have hm : 0 < μ.real (V n) := ENNReal.toReal_pos hn.1 hn.2.1
  letI : IsFiniteMeasure (μ.restrict (V n)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.mpr hn.2.1⟩
  have hdiff : IntegrableOn (fun y => f y - f x) (V n) μ := by
    refine (integrable_const (ε / 2)).mono' (hfm.restrict.sub aestronglyMeasurable_const) ?_
    exact (ae_restrict_mem hn.2.2).mono hb
  have hi : IntegrableOn f (V n) μ := by
    refine (hdiff.add (integrable_const (f x))).congr (.of_forall fun y => ?_)
    exact sub_add_cancel (f y) (f x)
  have hnorm : ‖∫ y in V n, f y - f x ∂μ‖ ≤ (ε / 2) * μ.real (V n) :=
    norm_setIntegral_le_of_norm_le_const (lt_top_iff_ne_top.mpr hn.2.1) hb
  have he : (⨍ y in V n, f y ∂μ) - f x =
      (μ.real (V n))⁻¹ • ∫ y in V n, f y - f x ∂μ := by
    rw [setAverage_eq, integral_sub hi (integrable_const (f x)), setIntegral_const,
      smul_sub, smul_smul, inv_mul_cancel₀ hm.ne', one_smul]
  rw [dist_eq_norm, he, norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hm.le)]
  refine (mul_le_mul_of_nonneg_left hnorm (inv_nonneg.mpr hm.le)).trans_lt ?_
  field_simp [hm.ne']
  linarith

/-- A Hilbert–Schmidt factorization supplies an explicit nuclear series,
by expanding the intermediate Hilbert space in its orthonormal basis. -/
theorem exists_cutoffTraceSeries_of_hilbertSchmidt_factors
    {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    {ι : Type*} (b : HilbertBasis ι ℂ E) (A : E →L[ℂ] H) (B : H →L[ℂ] E)
    (hA : Summable (fun i => ‖A (b i)‖ ^ 2)) (hB : Summable (fun i => ‖B.adjoint (b i)‖ ^ 2)) :
    ∃ T : RankOneSeries ι H, T.operator = A.comp B := by
  have hsum : Summable (fun i => ‖A (b i)‖ * ‖B.adjoint (b i)‖) := by
    refine (hA.add hB).of_nonneg_of_le
      (fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)) ?_
    intro i
    nlinarith [sq_nonneg (‖A (b i)‖ - ‖B.adjoint (b i)‖), norm_nonneg (A (b i)),
      norm_nonneg (B.adjoint (b i))]
  let T : RankOneSeries ι H := ⟨fun i => A (b i), fun i => B.adjoint (b i), hsum⟩
  refine ⟨T, ?_⟩
  ext x
  rw [RankOneSeries.operator_apply]
  have h := (b.hasSum_repr (B x)).mapL A
  change (∑' i, inner ℂ (B.adjoint (b i)) x • A (b i)) = A (B x)
  convert h.tsum_eq using 1
  apply tsum_congr
  intro i
  rw [B.adjoint_inner_left, b.repr_apply_apply, map_smul]

section WeightedCutoff

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]

omit [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] in
private theorem cutoffKernel_continuousAt_diagonal {w : G → ℝ} (hw : Continuous w)
    (hpos : ∀ x, 0 < w x) {ρ φ : G → ℂ} (hφ : ContinuousAt φ 1)
    {x : G} (hρ : ContinuousAt ρ x) :
    ContinuousAt (cutoffConvolutionKernel w ρ φ) (x, x) := by
  have hd : ContinuousAt (fun p : G × G => φ (p.1 * p.2⁻¹)) (x, x) := by
    let g (p : G × G) := p.1 * p.2⁻¹
    have h : Continuous g := continuous_fst.mul continuous_snd.inv
    have he : g (x, x) = (1 : G) := mul_inv_cancel x
    have hh : ContinuousAt φ (g (x, x)) := he ▸ hφ
    exact hh.comp (h.continuousAt (x := (x, x)))
  have hnum := (hρ.comp continuous_fst.continuousAt).mul hd
  exact hnum.div
    ((Complex.continuous_ofReal.comp (hw.comp continuous_snd)).continuousAt)
    (Complex.ofReal_ne_zero.mpr (hpos x).ne')

omit [T2Space G] in
/-- Continuity of the symbol at the identity gives the actual diagonal
of the weighted cutoff kernel under Haar window smoothing. -/
theorem cutoffConvolutionKernel_smoothed_diagonal
    {w : G → ℝ} (hw : Continuous w) (hpos : ∀ x, 0 < w x)
    {ρ φ : G → ℂ} (hρm : Measurable ρ) (hφm : AEMeasurable φ μ)
    (hφ : ContinuousAt φ 1) {x : G} (hρ : ContinuousAt ρ x)
    {U : ℕ → Set G} (hU : DoublingSequence μ U) (hcof : CofinalAtOne U) :
    Tendsto (fun n => translatedAverage (μ.prod μ) (U n ×ˢ U n)
      (cutoffConvolutionKernel w ρ φ) (x, x)) atTop
      (𝓝 (ρ x * φ 1 / (w x : ℂ))) := by
  let k := cutoffConvolutionKernel w ρ φ
  let V (n : ℕ) := (x, x) • (U n ×ˢ U n)
  have hd : AEMeasurable (fun p : G × G => φ (p.1 * p.2⁻¹)) (μ.prod μ) := by
    have h := hφm.comp_quasiMeasurePreserving (quasiMeasurePreserving_div μ μ)
    change AEMeasurable (fun p : G × G => φ (p.1 / p.2)) (μ.prod μ) at h
    simpa only [div_eq_mul_inv] using h
  have hm : AEStronglyMeasurable k (μ.prod μ) :=
    AEMeasurable.aestronglyMeasurable (((hρm.comp measurable_fst).aemeasurable.mul hd).div
      (Complex.continuous_ofReal.measurable.comp (hw.measurable.comp measurable_snd)).aemeasurable)
  letI : SigmaFinite μ := inferInstance
  have hUU := doublingSequence_measure_prod hU hU
  have hVV : CofinalAtOne (fun n => U n ×ˢ U n) :=
    doublingSequence_prod_properties.1 hU.decreasing hU.decreasing hcof hcof
  have hV : ∀ᶠ n : ℕ in atTop, (μ.prod μ) (V n) ≠ 0 ∧ (μ.prod μ) (V n) ≠ ∞ ∧
      MeasurableSet (V n) := .of_forall fun n => by
    refine ⟨?_, ?_, (hUU.measurable n).const_smul _⟩
    · change (μ.prod μ) ((x, x) • (U n ×ˢ U n)) ≠ _
      rw [measure_smul]
      exact (hUU.positive n).ne'
    · change (μ.prod μ) ((x, x) • (U n ×ˢ U n)) ≠ _
      rw [measure_smul]
      exact (hUU.finite n).ne
  have hsmall (W : Set (G × G)) (hW : W ∈ 𝓝 (x, x)) :
      ∀ᶠ n : ℕ in atTop, V n ⊆ W := by
    have ht : Tendsto (fun p : G × G => (x, x) * p) (𝓝 1) (𝓝 (x, x)) := by
      have hc : Continuous (fun p : G × G => (x, x) * p) := continuous_const.mul continuous_id
      simpa only [mul_one] using (hc.continuousAt (x := (1 : G × G))).tendsto
    obtain ⟨N, hN⟩ := hVV _ (ht hW)
    filter_upwards [eventually_ge_atTop N] with n hn z hz
    obtain ⟨p, hp, rfl⟩ := hz
    exact hN (hUU.decreasing hn hp)
  have hc : ContinuousAt k (x, x) := cutoffKernel_continuousAt_diagonal hw hpos hφ hρ
  have h := cutoff_setAverage_tendsto_at_continuity (μ.prod μ) hc hm V hV hsmall
  simpa only [V, translatedAverage_eq_average, k, cutoffConvolutionKernel, mul_inv_cancel] using h

omit [T2Space G] in
/-- If the cutoff is continuous at Haar-almost every point, then the
smoothed diagonal exists almost everywhere and its Haar-weighted integral
is the symbol at the identity times the cutoff mass. -/
theorem cutoffConvolutionKernel_smoothed_diagonal_integral
    {w : G → ℝ} (hw : Continuous w) (hpos : ∀ x, 0 < w x)
    {ρ φ : G → ℂ} (hρm : Measurable ρ) (hρI : Integrable ρ μ)
    (hρ : ∀ᵐ x ∂μ, ContinuousAt ρ x) (hφm : AEMeasurable φ μ) (hφ : ContinuousAt φ 1)
    {U : ℕ → Set G} (hU : DoublingSequence μ U) (hcof : CofinalAtOne U) :
    let d (x : G) := ρ x * φ 1 / (w x : ℂ)
    (∀ᵐ x ∂μ, Tendsto (fun n => translatedAverage (μ.prod μ) (U n ×ˢ U n)
      (cutoffConvolutionKernel w ρ φ) (x, x)) atTop (𝓝 (d x))) ∧
      Integrable (fun x => d x * (w x : ℂ)) μ ∧
      (∫ x, d x * (w x : ℂ) ∂μ) = (∫ x, ρ x ∂μ) * φ 1 := by
  intro d
  refine ⟨hρ.mono (fun x hx =>
    cutoffConvolutionKernel_smoothed_diagonal μ hw hpos hρm hφm hφ hx hU hcof), ?_⟩
  have hd (x : G) : d x * (w x : ℂ) = ρ x * φ 1 :=
    div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr (hpos x).ne')
  simp only [hd]
  exact ⟨hρI.mul_const _, integral_mul_const _ _⟩

/-- The corrected bounded-symbol clause allows measurable cutoffs with
jumps on a Haar-null set. Continuity of the symbol at the identity supplies
the integrable smoothed diagonal; the Hilbert–Schmidt conclusion uses only
measurability and compact support. -/
theorem cutoffConvolutionKernel_hilbertSchmidt_and_diagonal
    {w : G → ℝ} (hw : Continuous w) (hpos : ∀ x, 0 < w x)
    {ρ φ : G → ℂ} (hρm : Measurable ρ) (hρb : ∃ C : ℝ, ∀ x, ‖ρ x‖ ≤ C)
    (hφm : AEMeasurable φ μ) (hφb : ∃ C : ℝ, ∀ x, ‖φ x‖ ≤ C)
    (hρc : HasCompactSupport ρ) (hφc : HasCompactSupport φ)
    (hρ : ∀ᵐ x ∂μ, ContinuousAt ρ x) (hφ : ContinuousAt φ 1)
    {U : ℕ → Set G} (hU : DoublingSequence μ U) (hcof : CofinalAtOne U) :
    let ν := μ.withDensity (fun x => ENNReal.ofReal (w x))
    letI : IsLocallyFiniteMeasure ν := IsLocallyFiniteMeasure.withDensity_ofReal hw
    let k := cutoffConvolutionKernel w ρ φ
    let d (x : G) := ρ x * φ 1 / (w x : ℂ)
    ∃ hk : MemLp k 2 (ν.prod ν),
      (∀ f : Lp ℂ 2 ν, ∀ᵐ x ∂μ, kernelIntegralOperator (hk.toLp k) f x =
        ρ x * ∫ y, φ y * f (y⁻¹ * x) ∂μ) ∧
      (∃ (I : Set (Lp ℂ 2 ν)) (_ : I.Countable) (b : HilbertBasis I ℂ (Lp ℂ 2 ν)),
        Summable (fun i => ‖kernelIntegralOperator (hk.toLp k) (b i)‖ ^ 2) ∧
          (∑' i, ‖kernelIntegralOperator (hk.toLp k) (b i)‖ ^ 2) = ‖hk.toLp k‖ ^ 2) ∧
      (∀ᵐ x ∂μ, Tendsto (fun n => translatedAverage (μ.prod μ) (U n ×ˢ U n) k (x, x))
        atTop (𝓝 (d x))) ∧ Integrable (fun x => d x * (w x : ℂ)) μ ∧
      (∫ x, d x * (w x : ℂ) ∂μ) = (∫ x, ρ x ∂μ) * φ 1 := by
  intro ν k d
  letI : IsLocallyFiniteMeasure ν := IsLocallyFiniteMeasure.withDensity_ofReal hw
  let hk := cutoffConvolutionKernel_memLp_of_measurable_cutoff μ hw hpos hρm hφm hρb hφb hρc hφc
  refine ⟨hk, cutoffConvolutionKernel_apply_of_measurable_cutoff μ hw hpos hρm hφm hρb hφb hρc hφc,
    (radonKernel_hilbertSchmidt ν (hk.toLp k)).2, ?_⟩
  obtain ⟨C, hC⟩ := hρb
  have hi : Integrable ρ μ := memLp_one_iff_integrable.mp
    (hρc.memLp_of_bound hρm.aestronglyMeasurable C (.of_forall hC))
  exact cutoffConvolutionKernel_smoothed_diagonal_integral μ hw hpos hρm hi hρ hφm hφ hU hcof

/-- Changing the symbol at the identity alone has no effect on the kernel
in nonatomic Haar measure, but changes the pointwise diagonal formula. -/
theorem cutoffConvolution_identity_value_obstruction [NullSingletonClass μ]
    (w : G → ℝ) (ρ : G → ℂ) :
    ∃ φ : G → ℂ, Measurable φ ∧ HasCompactSupport φ ∧ (∀ v, ‖φ v‖ ≤ 1) ∧ φ 1 = 1 ∧
      (cutoffConvolutionKernel w ρ φ =ᵐ[μ.prod μ] (0 : G × G → ℂ)) ∧
      ∀ (U : Set (G × G)) (x : G × G),
        translatedAverage (μ.prod μ) U (cutoffConvolutionKernel w ρ φ) x = 0 := by
  let φ : G → ℂ := ({1} : Set G).indicator (fun _ => (1 : ℂ))
  have hφ : φ =ᵐ[μ] (0 : G → ℂ) := by
    filter_upwards [μ.ae_ne (1 : G)] with x hx
    simp [φ, hx]
  have hk : cutoffConvolutionKernel w ρ φ =ᵐ[μ.prod μ] (0 : G × G → ℂ) := by
    have hae := (quasiMeasurePreserving_div μ μ).ae hφ
    filter_upwards [hae] with p hp
    change φ (p.1 / p.2) = 0 at hp
    simp only [cutoffConvolutionKernel, ← div_eq_mul_inv, hp, mul_zero, zero_div, Pi.zero_apply]
  refine ⟨φ, measurable_const.indicator (measurableSet_singleton _), ?_, ?_, by simp [φ], hk, ?_⟩
  · exact HasCompactSupport.intro (isCompact_singleton (x := (1 : G))) (fun x hx => indicator_of_notMem hx _)
  · intro v
    by_cases hv : v = 1 <;> simp [φ, hv]
  · intro U x
    rw [translatedAverage_congr_ae (μ.prod μ) U hk]
    simp [translatedAverage]

omit [T2Space G] in
/-- A trace-class representation of the weighted cutoff convolution has
the trace given by the Haar cutoff mass and the symbol at the identity. -/
theorem cutoffConvolutionKernel_trace_of_series
    {w : G → ℝ} (hw : Continuous w) (hpos : ∀ x, 0 < w x)
    {ρ φ : G → ℂ} (hρ : Continuous ρ) (hρc : HasCompactSupport ρ) (hφ : ContinuousAt φ 1)
    (T : RankOneSeries ℕ (Lp ℂ 2 (μ.withDensity (fun x => ENNReal.ofReal (w x)))))
    (hk : MemLp (cutoffConvolutionKernel w ρ φ) 2
      ((μ.withDensity (fun x => ENNReal.ofReal (w x))).prod
        (μ.withDensity (fun x => ENNReal.ofReal (w x)))))
    (hT : kernelIntegralOperator (hk.toLp (cutoffConvolutionKernel w ρ φ)) = T.operator) :
    T.trace = (∫ x, ρ x ∂μ) * φ 1 := by
  let ν := μ.withDensity (fun x => ENNReal.ofReal (w x))
  letI : IsLocallyFiniteMeasure ν := IsLocallyFiniteMeasure.withDensity_ofReal hw
  have hd := (RankOneSeries.continuous_kernel_diagonal_trace ν T hk hT
    (.of_forall fun x => cutoffKernel_continuousAt_diagonal hw hpos hφ hρ.continuousAt)).2
  have he := (cutoffConvolutionKernel_integrable_densityDiagonal μ hpos (φ := φ) hρ hρc).2
  rw [← hd]
  rw [integral_withDensity_eq_integral_toReal_smul hw.measurable.ennreal_ofReal
    (.of_forall fun _ => ENNReal.ofReal_lt_top)]
  exact (integral_congr_ae (.of_forall fun x => by
    rw [ENNReal.toReal_ofReal (hpos x).le, Complex.real_smul, mul_comm])).trans he

omit [T2Space G] in
/-- A verified factorization through two Hilbert–Schmidt operators gives
trace class and the diagonal trace formula for the actual cutoff kernel. -/
theorem cutoffConvolutionKernel_traceClass_of_hilbertSchmidt_factors
    {w : G → ℝ} (hw : Continuous w) (hpos : ∀ x, 0 < w x)
    {ρ φ : G → ℂ} (hρ : Continuous ρ) (hρc : HasCompactSupport ρ) (hφ : ContinuousAt φ 1)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (b : HilbertBasis ℕ ℂ E) :
    let ν := μ.withDensity (fun x => ENNReal.ofReal (w x))
    letI : IsLocallyFiniteMeasure ν := IsLocallyFiniteMeasure.withDensity_ofReal hw
    let k := cutoffConvolutionKernel w ρ φ
    ∀ (hk : MemLp k 2 (ν.prod ν)) (A : E →L[ℂ] Lp ℂ 2 ν) (B : Lp ℂ 2 ν →L[ℂ] E),
      (Summable fun i => ‖A (b i)‖ ^ 2) → (Summable fun i => ‖B.adjoint (b i)‖ ^ 2) →
      kernelIntegralOperator (hk.toLp k) = A.comp B →
      ∃ T : TraceClass (Lp ℂ 2 ν),
        T.toOperator = kernelIntegralOperator (hk.toLp k) ∧ T.traceValue = (∫ x, ρ x ∂μ) * φ 1 := by
  intro ν k hk A B hA hB he
  obtain ⟨T, hT⟩ := exists_cutoffTraceSeries_of_hilbertSchmidt_factors b A B hA hB
  refine ⟨TraceClass.ofSeries T, hT.trans he.symm, ?_⟩
  rw [TraceClass.traceValue_ofSeries]
  exact cutoffConvolutionKernel_trace_of_series μ hw hpos hρ hρc hφ T hk (he.trans hT.symm)

end WeightedCutoff

section ModulatedCutoff

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  (m : G →ₜ* Multiplicative ℝ) (τ : Multiplicative ℝ →ₜ* G) (hτ : RightInverse τ m)
  (ν : Measure m.toMonoidHom.ker) [IsFiniteMeasure ν]

omit [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] in
/-- For every complex symbol, the weighted diagonal integral of the cutoff
kernel has the logarithmic asymptotic in split Haar coordinates. This also
computes the trace whenever the operator has a nuclear representation and
the symbol is continuous at the identity. -/
theorem modulatedCutoff_densityDiagonal_asymptotic {ι : Type*} {l : Filter ι}
    {Λ ε : ι → ℝ} (hΛ : Tendsto Λ l atTop) (hε : Tendsto (fun i => ε i * Λ i) l (𝓝 0))
    (ρ : ι → G → ℝ) (φ : G → ℂ) {w : G → ℝ} (hw : ∀ x, 0 < w x)
    (hdata : ∀ᶠ i in l, 0 ≤ ε i ∧ (Λ i)⁻¹ + ε i ≤ Λ i - ε i ∧
      Integrable (ρ i) (modulatedLogMeasure m τ hτ ν) ∧
      (∀ x, 0 ≤ ρ i x ∧ ρ i x ≤ 1) ∧
      (∀ x, modulatedLog m x ∉ Icc (-Real.log (Λ i)) (Real.log (Λ i)) → ρ i x = 0) ∧
      (∀ x, modulatedLog m x ∈ Icc (Real.log ((Λ i)⁻¹ + ε i)) (Real.log (Λ i - ε i)) → ρ i x = 1)) :
    Tendsto (fun i =>
      (∫ x, cutoffConvolutionKernel w (fun g => (ρ i g : ℂ)) φ (x, x) * (w x : ℂ)
        ∂modulatedLogMeasure m τ hτ ν) -
        (((2 * Real.log (Λ i)) * ν.real univ : ℝ) : ℂ) * φ 1) l (𝓝 0) := by
  let e := modulatedLogSplit m τ hτ
  have he : MeasurePreserving e ((volume : Measure ℝ).prod ν) (modulatedLogMeasure m τ hτ ν) :=
    ⟨e.continuous.measurable, rfl⟩
  have hlog (p : ℝ × m.toMonoidHom.ker) : modulatedLog m (e p) = p.1 := by
    exact intervalGroupChart_log m τ hτ (p.2, p.1)
  have ht := cutoffLogBand_mass_asymptotic ν hΛ hε (fun i => ρ i ∘ e) (hdata.mono fun i hi => by
    obtain ⟨hεi, hgap, hI, hR, hzero, hone⟩ := hi
    refine ⟨hεi, hgap, he.integrable_comp_of_integrable hI, fun p => hR (e p), ?_, ?_⟩
    · exact fun p hp => hzero (e p) (by rwa [hlog])
    · exact fun p hp => hone (e p) (by rwa [hlog]))
  have h := (Complex.continuous_ofReal.continuousAt.tendsto.comp ht).mul_const (φ 1)
  have h' : Tendsto (fun i => (((∫ p, ρ i (e p) ∂(volume : Measure ℝ).prod ν) -
      (2 * Real.log (Λ i)) * ν.real univ : ℝ) : ℂ) * φ 1) l (𝓝 0) := by
    simpa only [Function.comp_apply, Complex.ofReal_zero, zero_mul] using h
  refine h'.congr' (.of_forall fun i => ?_)
  rw [he.integral_comp e.toMeasurableEquiv.measurableEmbedding (ρ i), Complex.ofReal_sub, sub_mul]
  congr 1
  rw [← integral_complex_ofReal, ← integral_mul_const]
  apply integral_congr_ae
  refine .of_forall fun x => ?_
  change (ρ i x : ℂ) * φ 1 = cutoffConvolutionKernel w (fun g => (ρ i g : ℂ)) φ (x, x) * (w x : ℂ)
  rw [cutoffConvolutionKernel, mul_inv_cancel,
    div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr (hw x).ne')]

omit [T2Space G] in
/-- Once the weighted cutoff operators are trace class, their trace values
have the claimed leading term and a vanishing remainder. -/
theorem modulatedCutoff_traceClass_asymptotic [ν.IsHaarMeasure] {ι : Type*} {l : Filter ι}
    {Λ ε : ι → ℝ} (hΛ : Tendsto Λ l atTop) (hε : Tendsto (fun i => ε i * Λ i) l (𝓝 0))
    (ρ : ι → G → ℝ) {φ : G → ℂ} (hφ : ContinuousAt φ 1)
    {w : G → ℝ} (hw : Continuous w) (hpos : ∀ x, 0 < w x)
    (hρ : ∀ i, Continuous (ρ i)) (hρc : ∀ i, HasCompactSupport (ρ i))
    (hdata : ∀ᶠ i in l, 0 ≤ ε i ∧ (Λ i)⁻¹ + ε i ≤ Λ i - ε i ∧
      (∀ x, 0 ≤ ρ i x ∧ ρ i x ≤ 1) ∧
      (∀ x, modulatedLog m x ∉ Icc (-Real.log (Λ i)) (Real.log (Λ i)) → ρ i x = 0) ∧
      (∀ x, modulatedLog m x ∈ Icc (Real.log ((Λ i)⁻¹ + ε i)) (Real.log (Λ i - ε i)) → ρ i x = 1)) :
    let μ := modulatedLogMeasure m τ hτ ν
    letI : μ.IsHaarMeasure := modulatedLogMeasure_isHaar m τ hτ ν
    let μw := μ.withDensity (fun x => ENNReal.ofReal (w x))
    letI : IsLocallyFiniteMeasure μw := IsLocallyFiniteMeasure.withDensity_ofReal hw
    let k i := cutoffConvolutionKernel w (fun g => (ρ i g : ℂ)) φ
    ∀ (T : ι → TraceClass (Lp ℂ 2 μw)) (hk : ∀ i, MemLp (k i) 2 (μw.prod μw)),
      (∀ i, kernelIntegralOperator ((hk i).toLp (k i)) = (T i).toOperator) →
      Tendsto (fun i => (T i).traceValue - (((2 * Real.log (Λ i)) * ν.real univ : ℝ) : ℂ) * φ 1)
        l (𝓝 0) := by
  intro μ μw k T hk hT
  letI : (modulatedLogMeasure m τ hτ ν).IsHaarMeasure := modulatedLogMeasure_isHaar m τ hτ ν
  have hs := modulatedCutoff_densityDiagonal_asymptotic m τ hτ ν hΛ hε ρ φ hpos
    (hdata.mono fun i hi => ⟨hi.1, hi.2.1, (hρ i).integrable_of_hasCompactSupport (hρc i), hi.2.2⟩)
  refine hs.congr' (.of_forall fun i => ?_)
  apply congrArg (· - (((2 * Real.log (Λ i)) * ν.real univ : ℝ) : ℂ) * φ 1)
  obtain ⟨S, hS⟩ := (T i).toOperator_mem
  have hρC : Continuous (fun g => (ρ i g : ℂ)) := Complex.continuous_ofReal.comp (hρ i)
  have hρcC : HasCompactSupport (fun g => (ρ i g : ℂ)) :=
    (hρc i).comp_left (g := Complex.ofReal) Complex.ofReal_zero
  have hVal := cutoffConvolutionKernel_trace_of_series μ hw hpos hρC hρcC hφ S (hk i)
    ((hT i).trans hS.symm)
  exact ((cutoffConvolutionKernel_integrable_densityDiagonal μ hpos (φ := φ) hρC hρcC).2.trans hVal.symm).trans
    (TraceClass.traceValue_eq_of_operator (T i) S hS).symm

end ModulatedCutoff

end
end Masullo
