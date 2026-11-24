import NuclearKernelDiagonal
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/- The coordinate construction and graph-support comparison are adapted from
the parallel RiemannMasullo development, commit cd84b23, under Apache-2.0.
See External/PROVENANCE.md for the corresponding source files. -/

open Filter MeasureTheory Set TopologicalSpace
open scoped ENNReal InnerProductSpace Topology

namespace Masullo

noncomputable section

/-- The diagonal can carry product mass for a Radon measure with atoms. -/
theorem printed_diagonal_nullity_fails :
    ((Measure.dirac (0 : ℕ)).prod (Measure.dirac (0 : ℕ))) {p | p.1 = p.2} = 1 := by
  rw [Measure.dirac_prod_dirac, Measure.dirac_apply' _ (measurableSet_eq_fun measurable_fst measurable_snd)]
  simp

/-- The pairing used to smooth a kernel is an absolutely convergent convolution
over the counting measure on its coordinate index. -/
theorem lp_pairing_eq_countingConvolution (a b : lp (fun _ : ℕ => ℂ) 2) :
    Integrable (fun i => a i * star (b i)) Measure.count ∧
      (∫ i, a i * star (b i) ∂Measure.count) = ⟪b, a⟫_ℂ := by
  have hi : Integrable (fun i => a i * star (b i)) Measure.count := by
    apply integrable_count_iff.mpr
    have hc : (2 : ℝ≥0∞).toReal.HolderConjugate (2 : ℝ≥0∞).toReal := by
      simpa only [ENNReal.toReal_ofNat] using Real.HolderConjugate.two_two
    simpa only [norm_mul, norm_star] using lp.summable_mul hc a b
  refine ⟨hi, ?_⟩
  rw [integral_countable hi, lp.inner_eq_tsum]
  simp only [count_real_singleton, one_smul, RCLike.inner_apply, starRingEnd_apply]

/-- The integral of the squared pointwise norm is the square of the L² norm. -/
private theorem integral_sq_norm {X E 𝕜 : Type*} [MeasurableSpace X] {μ : Measure X}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (f : Lp E 2 μ) :
    (∫ x, ‖f x‖ ^ 2 ∂μ) = ‖f‖ ^ 2 := by
  rw [norm_sq_eq_re_inner (𝕜 := 𝕜), L2.inner_def]
  change _ = RCLike.reCLM (∫ x, inner 𝕜 (f x) (f x) ∂μ)
  rw [← RCLike.reCLM.integral_comp_comm (L2.integrable_inner (𝕜 := 𝕜) f f)]
  simp [inner_self_eq_norm_sq_to_K]

/-- A sequence of scalar L² functions with summable squared L² norms is the coordinate
family of a single square-integrable function with values in ℓ². -/
private theorem exists_memLp_coordinates {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (u : ℕ → Lp ℂ 2 μ) (hu : Summable fun n ↦ ‖u n‖ ^ 2) :
    ∃ a : X → lp (fun _ : ℕ ↦ ℂ) 2, MemLp a 2 μ ∧
      ∀ᵐ x ∂μ, ∀ n, a x n = u n x := by
  classical
  have he (n : ℕ) : ∫⁻ x, ENNReal.ofReal (‖u n x‖ ^ 2) ∂μ =
      ENNReal.ofReal (‖u n‖ ^ 2) := by
    rw [← ofReal_integral_eq_lintegral_ofReal
      ((Lp.memLp (u n)).integrable_norm_pow (by decide : 2 ≠ 0))
      (Eventually.of_forall fun _ ↦ sq_nonneg _), integral_sq_norm (𝕜 := ℂ)]
  have hmeas (n : ℕ) : AEMeasurable (fun x ↦ ENNReal.ofReal (‖u n x‖ ^ 2)) μ :=
    ((Lp.aestronglyMeasurable (u n)).norm.aemeasurable.pow_const _).ennreal_ofReal
  have henergy : ∫⁻ x, ∑' n, ENNReal.ofReal (‖u n x‖ ^ 2) ∂μ =
      ENNReal.ofReal (∑' n, ‖u n‖ ^ 2) := by
    rw [lintegral_tsum hmeas, ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ sq_nonneg _) hu]
    simp only [he]
  have hs : ∀ᵐ x ∂μ, Summable fun n ↦ ‖u n x‖ ^ 2 := by
    have hfinite := ae_lt_top' (AEMeasurable.tsum hmeas) (by rw [henergy]; simp)
    filter_upwards [hfinite] with x hx
    have hnorm (n : ℕ) : ENNReal.ofReal (‖u n x‖ ^ 2) = ‖(‖u n x‖ ^ 2 : ℝ)‖ₑ :=
      by rw [← ofReal_norm, Real.norm_of_nonneg (sq_nonneg _)]
    simp_rw [hnorm] at hx
    simpa only [Real.norm_of_nonneg (sq_nonneg _)] using
      (tsum_enorm_ne_top_iff_summable_norm.mp hx.ne)
  let a (x : X) : lp (fun _ : ℕ ↦ ℂ) 2 :=
    if h : Summable (fun n ↦ ‖u n x‖ ^ 2) then
      ⟨fun n ↦ u n x, memℓp_gen (by simpa using h)⟩ else 0
  have hcoords : ∀ᵐ x ∂μ, ∀ n, a x n = u n x := by
    filter_upwards [hs] with x hx n
    simp [a, hx]
  have ha : AEStronglyMeasurable a μ := by
    apply aestronglyMeasurable_of_tendsto_ae atTop
      (f := fun (m : ℕ) x ↦ ∑ n ∈ Finset.range m, lp.single 2 n (u n x))
    · intro m
      apply Finset.aestronglyMeasurable_fun_sum
      intro n _
      exact (lp.singleContinuousLinearMap ℂ _ 2 n).continuous.comp_aestronglyMeasurable
        (Lp.aestronglyMeasurable (u n))
    · filter_upwards [hcoords] with x hx
      simpa only [hx] using (lp.hasSum_single (by simp) (a x)).tendsto_sum_nat
  refine ⟨a, (memLp_two_iff_integrable_sq_norm ha).mpr
    ⟨ha.norm.pow _, ?_⟩, hcoords⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun _ ↦ sq_nonneg _)]
  calc
    (∫⁻ x, ENNReal.ofReal (‖a x‖ ^ 2) ∂μ) =
        ∫⁻ x, ∑' n, ENNReal.ofReal (‖u n x‖ ^ 2) ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [hs, hcoords] with x hx hc
      have hn : ‖a x‖ ^ 2 = ∑' n, ‖u n x‖ ^ 2 := by
        simpa [hc] using lp.norm_rpow_eq_tsum (p := 2) (by simp) (a x)
      rw [hn, ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ sq_nonneg _) hx]
    _ < ∞ := by rw [henergy]; simp

/-- If a kernel agrees product-almost everywhere with a continuous function of
two separately measurable parameters, then the agreement holds almost everywhere on the
diagonal at which the kernel is jointly continuous. -/
private theorem ae_diagonal_eq_of_ae_eq_comp_prod
    {X Y Z W : Type*}
    [TopologicalSpace X] [SecondCountableTopology X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [TopologicalSpace Y] [SecondCountableTopology Y] [MeasurableSpace Y] [OpensMeasurableSpace Y]
    [TopologicalSpace Z] [SecondCountableTopology Z] [MeasurableSpace Z] [OpensMeasurableSpace Z]
    [TopologicalSpace W] [T2Space W]
    {μ : Measure X} [SFinite μ] {a : X → Y} {b : X → Z} {φ : Y × Z → W} {k : X × X → W}
    (ha : AEMeasurable a μ) (hb : AEMeasurable b μ) (hφ : Continuous φ)
    (hk : k =ᵐ[μ.prod μ] fun p ↦ φ (a p.1, b p.2))
    (hcont : ∀ᵐ x ∂μ, ContinuousAt k (x, x)) :
    (fun x ↦ k (x, x)) =ᵐ[μ] fun x ↦ φ (a x, b x) := by
  let A (x : X) : X × Y := (x, a x)
  let B (x : X) : X × Z := (x, b x)
  have hA : AEMeasurable A μ := aemeasurable_id.prodMk ha
  have hB : AEMeasurable B μ := aemeasurable_id.prodMk hb
  filter_upwards [hcont, ae_of_ae_map hA (Measure.support_mem_ae (μ := μ.map A)),
    ae_of_ae_map hB (Measure.support_mem_ae (μ := μ.map B))] with x hx hxA hxB
  by_contra hne
  let f (p : (X × Y) × (X × Z)) := k (p.1.1, p.2.1)
  let g (p : (X × Y) × (X × Z)) := φ (p.1.2, p.2.2)
  have hf : ContinuousAt f (A x, B x) := by
    let coords (p : (X × Y) × (X × Z)) : X × X := (p.1.1, p.2.1)
    have hcoords : Continuous coords := continuous_fst.fst.prodMk continuous_snd.fst
    exact (show ContinuousAt k (coords (A x, B x)) from hx).comp hcoords.continuousAt
  have hg : ContinuousAt g (A x, B x) :=
    (hφ.comp (continuous_fst.snd.prodMk continuous_snd.snd)).continuousAt
  have hsep : {p | f p ≠ g p} ∈ 𝓝 (A x, B x) :=
    (hf.ne_iff_eventually_ne hg).mp hne
  obtain ⟨U, V, hU, hxU, hV, hxV, hUV⟩ := mem_nhds_prod_iff'.mp hsep
  have hμU : 0 < μ (A ⁻¹' U) := by
    rw [← Measure.map_apply_of_aemeasurable hA hU.measurableSet]
    exact (Measure.mem_support_iff_forall _).mp hxA U (hU.mem_nhds hxU)
  have hμV : 0 < μ (B ⁻¹' V) := by
    rw [← Measure.map_apply_of_aemeasurable hB hV.measurableSet]
    exact (Measure.mem_support_iff_forall _).mp hxB V (hV.mem_nhds hxV)
  have hpos : 0 < μ.prod μ ((A ⁻¹' U) ×ˢ (B ⁻¹' V)) := by
    rw [Measure.prod_prod]
    exact pos_iff_ne_zero.mpr (mul_ne_zero hμU.ne' hμV.ne')
  apply hpos.ne'
  apply measure_mono_null _ (ae_iff.mp hk)
  exact fun p hp ↦ hUV (show (A p.1, B p.2) ∈ U ×ˢ V from hp)

/-- A countable `lp` sum of separable spaces is separable for finite exponent. -/
private theorem lp_separableSpace {ι : Type*} [Countable ι] {E : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, SeparableSpace (E i)]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞) :
    SeparableSpace (lp E p) := by
  classical
  let embed (s : Finset ι) (x : ∀ i : s, E i) : lp E p :=
    ∑ i : s, lp.single p i (x i)
  have hc (s : Finset ι) : Continuous (embed s) := by
    apply continuous_finsetSum
    intro i _
    exact (lp.isometry_single (E := E) (p := p) (i : ι)).continuous.comp (continuous_apply i)
  have hsep : IsSeparable (⋃ s, range (embed s)) :=
    IsSeparable.iUnion fun s ↦ isSeparable_range (hc s)
  have hd : Dense (⋃ s, range (embed s)) := by
    intro x
    apply mem_closure_of_tendsto (lp.hasSum_single hp x)
    apply Eventually.of_forall
    intro s
    refine mem_iUnion.2 ⟨s, ⟨fun i ↦ x i, ?_⟩⟩
    exact Finset.sum_coe_sort s (fun i ↦ lp.single p i (x i))
  have he : closure (⋃ s, range (embed s)) = univ := hd.closure_eq
  rw [← isSeparable_univ_iff, ← he]
  exact hsep.closure

/-- Rescale each nonzero rank-one term so the squared norms of the two vectors
are both equal to the original product of norms. -/
private theorem RankOneSeries.exists_balanced {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (T : RankOneSeries ℕ H) :
    ∃ S : RankOneSeries ℕ H, S.operator = T.operator ∧
      Summable (fun i => ‖S.image i‖ ^ 2) ∧ Summable (fun i => ‖S.functional i‖ ^ 2) := by
  classical
  let d (i : ℕ) := Real.sqrt (‖T.functional i‖ / ‖T.image i‖)
  let nonzero (i : ℕ) := T.image i ≠ 0 ∧ T.functional i ≠ 0
  let u (i : ℕ) : H := if nonzero i then (d i : ℂ) • T.image i else 0
  let v (i : ℕ) : H := if nonzero i then ((d i)⁻¹ : ℂ) • T.functional i else 0
  have hpos {i : ℕ} (hi : nonzero i) : 0 < d i :=
    Real.sqrt_pos.mpr (div_pos (norm_pos_iff.mpr hi.2) (norm_pos_iff.mpr hi.1))
  have hsq (i : ℕ) : d i ^ 2 = ‖T.functional i‖ / ‖T.image i‖ :=
    Real.sq_sqrt (div_nonneg (norm_nonneg _) (norm_nonneg _))
  have henergy (i : ℕ) : ‖u i‖ ^ 2 = ‖T.image i‖ * ‖T.functional i‖ ∧
      ‖v i‖ ^ 2 = ‖T.image i‖ * ‖T.functional i‖ := by
    by_cases hi : nonzero i
    · have hU := norm_pos_iff.mpr hi.1
      have hV := norm_pos_iff.mpr hi.2
      have hd := hpos hi
      simp only [u, v, ite_eq_left hi, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hd, mul_pow, inv_pow, hsq]
      constructor <;> field_simp
    · have hz : T.image i = 0 ∨ T.functional i = 0 := by
        by_contra! hn
        exact hi hn
      rcases hz with hz | hz <;> simp [u, v, hi, hz]
  let S : RankOneSeries ℕ H :=
    { image := u
      functional := v
      summableNorm := by
        apply T.summableNorm.congr
        intro i
        have he : ‖u i‖ = ‖v i‖ :=
          (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ((henergy i).1.trans (henergy i).2.symm)
        rw [← he, ← pow_two, (henergy i).1] }
  refine ⟨S, ?_, T.summableNorm.congr (fun i => (henergy i).1.symm),
    T.summableNorm.congr (fun i => (henergy i).2.symm)⟩
  ext f : 1
  rw [S.operator_apply, T.operator_apply]
  apply tsum_congr
  intro i
  change ⟪v i, f⟫_ℂ • u i = _
  by_cases hi : nonzero i
  · simp only [u, v, ite_eq_left hi, inner_smul_left, map_inv₀, Complex.conj_ofReal, smul_smul]
    rw [mul_right_comm, inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (hpos hi).ne'), one_mul]
  · have hz : T.image i = 0 ∨ T.functional i = 0 := by
        by_contra! hn
        exact hi hn
    rcases hz with hz | hz <;> simp [u, v, hi, hz]

variable {X : Type*} [TopologicalSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [SFinite μ]

/-- C.3.7.1(1). The operator is compact, and the squares of its norms on a Hilbert
basis sum to the squared kernel norm. -/
theorem radonKernel_hilbertSchmidt (k : (X × X) →₂[μ.prod μ] ℂ) :
    IsCompactOperator (kernelIntegralOperator k) ∧
      ∃ (s : Set (X →₂[μ] ℂ)) (_ : s.Countable) (b : HilbertBasis s ℂ (X →₂[μ] ℂ)),
        Summable (fun i => ‖kernelIntegralOperator k (b i)‖ ^ 2) ∧
          (∑' i, ‖kernelIntegralOperator k (b i)‖ ^ 2) = ‖k‖ ^ 2 := by
  obtain ⟨s, hs, ⟨b⟩⟩ := exists_countable_hilbertBasis_L2 (ν := μ)
  letI : Countable s := hs.to_subtype
  have he := kernelIntegralOperator_hilbertSchmidt_sq b k
  have hf : (∑' i, ‖kernelIntegralOperator k (b i)‖ₑ ^ (2 : ℝ)) ≠ ⊤ :=
    he.trans_ne (ENNReal.rpow_lt_top_of_nonneg (by norm_num) enorm_ne_top).ne
  refine ⟨isCompactOperator_of_basisEnergy b (kernelIntegralOperator k) hf, s, hs, b, ?_, ?_⟩
  · simpa only [ENNReal.rpow_two, ENNReal.toReal_pow, toReal_enorm] using ENNReal.summable_toReal hf
  · have he' := congrArg ENNReal.toReal he
    rw [ENNReal.tsum_toReal_eq (f := fun i : s => ‖kernelIntegralOperator k (b i)‖ₑ ^ (2 : ℝ)) (fun _ =>
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) enorm_ne_top).ne)] at he'
    simpa only [ENNReal.rpow_two, ENNReal.toReal_pow, toReal_enorm] using he'

/-- C.3.7.1(2)(b). Two square-integrable vector fields give a representative
by pairing their values. Its diagonal computes the trace. -/
theorem RankOneSeries.kernel_trace_smoothing
    (T : RankOneSeries ℕ (X →₂[μ] ℂ)) {k : X × X → ℂ} (hk : MemLp k 2 (μ.prod μ))
    (hoperator : kernelIntegralOperator (hk.toLp k) = T.operator) :
    ∃ a b : X → lp (fun _ : ℕ => ℂ) 2, MemLp a 2 μ ∧ MemLp b 2 μ ∧
      (k =ᵐ[μ.prod μ] fun p => ⟪b p.2, a p.1⟫_ℂ) ∧
      Integrable (fun x => ⟪b x, a x⟫_ℂ) μ ∧ (∫ x, ⟪b x, a x⟫_ℂ ∂μ) = T.trace := by
  obtain ⟨S, hS, hu, hv⟩ := T.exists_balanced
  obtain ⟨a, ha, hcoordsA⟩ := exists_memLp_coordinates S.image hu
  obtain ⟨b, hb, hcoordsB⟩ := exists_memLp_coordinates S.functional hv
  have hinner (x y : X) (hx : ∀ i, a x i = S.image i x) (hy : ∀ i, b y i = S.functional i y) :
      ⟪b y, a x⟫_ℂ = ∑' i, S.image i x * star (S.functional i y) := by
    simp only [lp.inner_eq_tsum, hx, hy, RCLike.inner_apply, starRingEnd_apply]
  have hkernel := S.kernel_ae_eq μ hk (hoperator.trans hS.symm)
  have hfactor : k =ᵐ[μ.prod μ] fun p => ⟪b p.2, a p.1⟫_ℂ := by
    filter_upwards [hkernel, Measure.quasiMeasurePreserving_fst.ae hcoordsA,
      Measure.quasiMeasurePreserving_snd.ae hcoordsB] with p hp hpa hpb
    exact hp.trans (hinner p.1 p.2 hpa hpb).symm
  have he : (fun x => ⟪b x, a x⟫_ℂ) =ᵐ[μ] fun x => ∑' i, S.image i x * star (S.functional i x) := by
    filter_upwards [hcoordsA, hcoordsB] with x hxa hxb
    exact hinner x x hxa hxb
  exact ⟨a, b, ha, hb, hfactor, (S.diagonal_series_trace μ).1.congr he.symm,
    (integral_congr_ae he).trans ((S.diagonal_series_trace μ).2.trans
      (RankOneSeries.trace_eq_of_operator_eq hS))⟩

/-- C.3.7.1(2)(a). Almost-everywhere continuity on the diagonal identifies the
pointwise values with the integrable nuclear trace density. -/
theorem RankOneSeries.continuous_kernel_diagonal_trace
    (T : RankOneSeries ℕ (X →₂[μ] ℂ)) {k : X × X → ℂ} (hk : MemLp k 2 (μ.prod μ))
    (hoperator : kernelIntegralOperator (hk.toLp k) = T.operator)
    (hcont : ∀ᵐ x ∂μ, ContinuousAt k (x, x)) :
    Integrable (fun x => k (x, x)) μ ∧ (∫ x, k (x, x) ∂μ) = T.trace := by
  obtain ⟨a, b, ha, hb, hfactor, hInt, htrace⟩ := T.kernel_trace_smoothing μ hk hoperator
  let V := lp (fun _ : ℕ => ℂ) 2
  letI : SeparableSpace V := lp_separableSpace (by simp)
  letI : MeasurableSpace V := borel V
  letI : BorelSpace V := ⟨rfl⟩
  have hφ : Continuous (fun p : V × V => ⟪p.2, p.1⟫_ℂ) := continuous_snd.inner continuous_fst
  have he := ae_diagonal_eq_of_ae_eq_comp_prod ha.aestronglyMeasurable.aemeasurable
    hb.aestronglyMeasurable.aemeasurable hφ hfactor hcont
  exact ⟨hInt.congr he.symm, (integral_congr_ae he).trans htrace⟩

end

end Masullo
