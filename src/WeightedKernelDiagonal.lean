import KernelMultipliers
import SpectralKernelNorm
import SpectralSchattenOne
import MeasureFoundations
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology Pointwise

namespace Masullo

noncomputable section

variable {X : Type*} [MeasurableSpace X]

private theorem restrict_le_scaled_density (μ : Measure X) {w : X → ℝ} (hw : Measurable w)
    {K : Set X} (hK : MeasurableSet K) {c : ℝ} (hc : 0 < c) (hmin : ∀ x ∈ K, c ≤ w x) :
    μ.restrict K ≤ (ENNReal.ofReal c)⁻¹ • μ.withDensity (fun x => ENNReal.ofReal (w x)) := by
  rw [← withDensity_smul _ hw.ennreal_ofReal, ← withDensity_one (μ := μ.restrict K),
    ← withDensity_indicator hK]
  apply withDensity_mono
  apply Eventually.of_forall
  intro x
  by_cases hx : x ∈ K
  · rw [indicator_of_mem hx, Pi.one_apply, Pi.smul_apply, smul_eq_mul]
    exact (ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr hc).ne' ENNReal.ofReal_ne_top).symm.le.trans
      (mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal (hmin x hx)))
  · simp [indicator_of_notMem hx]

private theorem memLp_density_cutoff (μ : Measure X) {w : X → ℝ} (hw : Measurable w)
    {K : Set X} (hK : MeasurableSet K) {c : ℝ} (hc : 0 < c) (hmin : ∀ x ∈ K, c ≤ w x)
    {f : X → ℂ} (hf : MemLp f 2 (μ.withDensity (fun x => ENNReal.ofReal (w x)))) :
    MemLp (K.indicator f) 2 μ ∧
      eLpNorm (K.indicator f) 2 μ ≤
        ((ENNReal.ofReal c)⁻¹) ^ (1 / 2 : ℝ) *
          eLpNorm f 2 (μ.withDensity (fun x => ENNReal.ofReal (w x))) := by
  have hm := restrict_le_scaled_density μ hw hK hc hmin
  have hscaled : MemLp f 2 ((ENNReal.ofReal c)⁻¹ • μ.withDensity (fun x => ENNReal.ofReal (w x))) :=
    hf.smul_measure (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr hc).ne')
  refine ⟨(memLp_indicator_iff_restrict hK).mpr (hscaled.mono_measure hm), ?_⟩
  rw [eLpNorm_indicator_eq_eLpNorm_restrict hK]
  refine (eLpNorm_mono_measure f hm).trans_eq ?_
  rw [eLpNorm_smul_measure_of_ne_top (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)]
  simp only [smul_eq_mul, ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat]

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure] [SigmaFinite μ]
  (w : G → ℝ)

private abbrev weighted (μ : Measure G) (w : G → ℝ) : Measure G :=
  μ.withDensity (fun x => ENNReal.ofReal (w x))

/-- The Haar window averages of a weighted nuclear kernel recover the weighted
rank-one trace density. The argument localizes to compact sets, where the
continuous positive weight has a positive minimum. -/
private theorem RankOneSeries.weighted_kernel_diagonal_behavior_compact
    (hw : Continuous w) (hpos : ∀ x, 0 < w x) {U : ℕ → Set G}
    (hU : DoublingSequence μ U) (hcof : CofinalAtOne U) (hUc : IsCompact (closure (U 0)))
    {C : ℝ≥0} (hC : 0 < C) (hDiff : ∀ n, μ (U n * (U n)⁻¹) < C * μ (U n))
    (T : RankOneSeries ℕ (G →₂[weighted μ w] ℂ))
    {k : G × G → ℂ} (hk : MemLp k 2 ((weighted μ w).prod (weighted μ w)))
    (hoperator : kernelIntegralOperator (hk.toLp k) = T.operator) :
    ∀ᵐ x ∂μ, (Tendsto (fun n => translatedAverage (μ.prod μ) (U n ×ˢ U n) k (x, x)) atTop
      (𝓝 (∑' i, T.image i x * star (T.functional i x)))) ∧
      ∃ B : ℝ≥0∞, B < ⊤ ∧ ∀ n,
        (∫⁻ z in (x, x) • (U n ×ˢ U n), ‖k z‖ₑ ∂μ.prod μ) / (μ (U n) * μ (U n)) ≤ B := by
  let ν := weighted μ w
  letI : IsLocallyFiniteMeasure ν := IsLocallyFiniteMeasure.withDensity_ofReal hw
  letI : Measure.Regular μ := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _
  have hac : μ ≪ ν := withDensity_absolutelyContinuous' hw.measurable.ennreal_ofReal.aemeasurable
    (Eventually.of_forall fun x => (ENNReal.ofReal_pos.mpr (hpos x)).ne')
  have hseries := (hac.prod hac).ae_le (T.kernel_ae_eq ν hk hoperator)
  have hmass : (∑' i, eLpNorm (T.image i) 2 ν * eLpNorm (T.functional i) 2 ν) < ⊤ := by
    have h := ENNReal.ofReal_tsum_of_nonneg (fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
      T.summableNorm
    simp only [ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm, Lp.enorm_def] at h
    rw [← h]
    exact ENNReal.ofReal_lt_top
  have hlocal (j : ℕ) : ∀ᵐ x ∂μ, x ∈ compactCovering G j →
      (Tendsto (fun n => translatedAverage (μ.prod μ) (U n ×ˢ U n) k (x, x)) atTop
        (𝓝 (∑' i, T.image i x * star (T.functional i x)))) ∧
        ∃ B : ℝ≥0∞, B < ⊤ ∧ ∀ n,
          (∫⁻ z in (x, x) • (U n ×ˢ U n), ‖k z‖ₑ ∂μ.prod μ) / (μ (U n) * μ (U n)) ≤ B := by
    let K := insert 1 (compactCovering G j)
    let V := K * closure (U 0)
    have hV : IsCompact V := ((isCompact_compactCovering G j).insert 1).mul hUc
    have hone : (1 : G) ∈ closure (U 0) := subset_closure (hU.one_mem 0)
    have hV₁ : (1 : G) ∈ V := ⟨1, mem_insert 1 _, 1, hone, one_mul 1⟩
    obtain ⟨y, _, hmin⟩ := hV.exists_isMinOn ⟨1, hV₁⟩ hw.continuousOn
    let D := ((ENNReal.ofReal (w y))⁻¹) ^ (1 / 2 : ℝ)
    have hD : D < ⊤ := ENNReal.rpow_lt_top_of_nonneg (by norm_num)
      (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr (hpos y)).ne')
    let u (i : ℕ) := V.indicator (T.image i : G → ℂ)
    let v (i : ℕ) := V.indicator (T.functional i : G → ℂ)
    let f := (V ×ˢ V).indicator k
    have hu (i : ℕ) := memLp_density_cutoff μ hw.measurable hV.measurableSet (hpos y)
      (fun x hx => hmin hx)
      (Lp.memLp (T.image i))
    have hv (i : ℕ) := memLp_density_cutoff μ hw.measurable hV.measurableSet (hpos y)
      (fun x hx => hmin hx) (Lp.memLp (T.functional i))
    have hmassV : (∑' i, eLpNorm (u i) 2 μ * eLpNorm (v i) 2 μ) < ⊤ := by
      refine (ENNReal.tsum_le_tsum (fun i => mul_le_mul' (hu i).2 (hv i).2)).trans_lt ?_
      change (∑' i, (D * eLpNorm (T.image i) 2 ν) * (D * eLpNorm (T.functional i) 2 ν)) < ⊤
      simp_rw [mul_mul_mul_comm D _ D]
      rw [ENNReal.tsum_mul_left]
      exact ENNReal.mul_lt_top (ENNReal.mul_lt_top hD hD) hmass
    have hf : f =ᵐ[μ.prod μ] fun z => ∑' i, u i z.1 * star (v i z.2) := by
      filter_upwards [hseries] with z hz
      by_cases h₁ : z.1 ∈ V <;> by_cases h₂ : z.2 ∈ V <;>
        simp [f, u, v, mem_prod, h₁, h₂, hz]
    have hgev (i : ℕ) : Measurable (u i) :=
      (Lp.stronglyMeasurable (T.image i)).measurable.indicator hV.measurableSet
    have hgev' (i : ℕ) : Measurable (v i) :=
      (Lp.stronglyMeasurable (T.functional i)).measurable.indicator hV.measurableSet
    filter_upwards [rankOneKernel_diagonal_ae μ hU hcof hUc hC hDiff u v hgev hgev'
      (fun i => (hu i).1) (fun i => (hv i).1) hmassV hf,
      rankOneKernel_enorm_windowBound μ hU hUc hC hDiff u v hgev hgev'
        (fun i => (hu i).1) (fun i => (hv i).1) hmassV hf] with x hx hbound hxK
    have hxV : x ∈ V := ⟨x, mem_insert_of_mem 1 hxK, 1, hone, mul_one x⟩
    have hwindow (n : ℕ) : (x, x) • (U n ×ˢ U n) ⊆ V ×ˢ V := by
      rintro _ ⟨z, hz, rfl⟩
      exact ⟨⟨x, mem_insert_of_mem 1 hxK, z.1, subset_closure (hU.decreasing (Nat.zero_le n) hz.1), rfl⟩,
        ⟨x, mem_insert_of_mem 1 hxK, z.2, subset_closure (hU.decreasing (Nat.zero_le n) hz.2), rfl⟩⟩
    have hmeas (n : ℕ) : MeasurableSet ((x, x) • (U n ×ˢ U n)) :=
      ((hU.measurable n).prod (hU.measurable n)).const_smul (x, x)
    simp only [u, v, indicator_of_mem hxV] at hx
    refine ⟨hx.congr (fun n => ?_), ?_⟩
    · unfold translatedAverage
      congr 1
      exact setIntegral_congr_fun (hmeas n) (fun z hz => indicator_of_mem (hwindow n hz) k)
    · obtain ⟨B, hB, hBn⟩ := hbound
      refine ⟨B, hB, fun n => ?_⟩
      have he : (∫⁻ z in (x, x) • (U n ×ˢ U n), ‖f z‖ₑ ∂μ.prod μ) =
          ∫⁻ z in (x, x) • (U n ×ˢ U n), ‖k z‖ₑ ∂μ.prod μ := by
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_mem (hmeas n)] with z hz
        rw [show f z = k z from indicator_of_mem (hwindow n hz) k]
      rw [← he]
      exact hBn n
  filter_upwards [ae_all_iff.mpr hlocal] with x hx
  obtain ⟨j, hj⟩ := exists_mem_compactCovering x
  exact hx j hj

/-- The Haar window averages of a weighted nuclear kernel recover its diagonal
series. Cofinality allows the proof to start at a window with compact closure. -/
theorem RankOneSeries.weighted_kernel_diagonal_tendsto_series
    (hw : Continuous w) (hpos : ∀ x, 0 < w x) {U : ℕ → Set G}
    (hU : DoublingSequence μ U) (hcof : CofinalAtOne U)
    {C : ℝ≥0} (hC : 0 < C) (hDiff : ∀ n, μ (U n * (U n)⁻¹) < C * μ (U n))
    (T : RankOneSeries ℕ (G →₂[weighted μ w] ℂ))
    {k : G × G → ℂ} (hk : MemLp k 2 ((weighted μ w).prod (weighted μ w)))
    (hoperator : kernelIntegralOperator (hk.toLp k) = T.operator) :
    ∀ᵐ x ∂μ, Tendsto (fun n => translatedAverage (μ.prod μ) (U n ×ˢ U n) k (x, x)) atTop
      (𝓝 (∑' i, T.image i x * star (T.functional i x))) := by
  obtain ⟨m, hm, hmcof, hmC⟩ := exists_compact_doublingTail hU hcof
  have ht := T.weighted_kernel_diagonal_behavior_compact μ w hw hpos hm hmcof
    (by simpa only [zero_add] using hmC) hC (fun n => hDiff (n + m)) hk hoperator
  exact ht.mono fun _ hx => (tendsto_add_atTop_iff_nat m).mp hx.1

omit [IsTopologicalGroup G] in
private theorem weighted_kernel_locallyIntegrable
    (hw : Continuous w) (hpos : ∀ x, 0 < w x)
    {k : G × G → ℂ} (hk : MemLp k 2 ((weighted μ w).prod (weighted μ w))) :
    LocallyIntegrable k (μ.prod μ) := by
  let F (z : G × G) := w z.1 * w z.2
  have hF : Continuous F := (hw.comp continuous_fst).mul (hw.comp continuous_snd)
  have hFpos (z : G × G) : 0 < F z := mul_pos (hpos _) (hpos _)
  have hp : (weighted μ w).prod (weighted μ w) = (μ.prod μ).withDensity
      (fun z => ENNReal.ofReal (F z)) := by
    rw [weighted, prod_withDensity hw.measurable.ennreal_ofReal hw.measurable.ennreal_ofReal]
    congr 1
    funext z
    exact (ENNReal.ofReal_mul (hpos z.1).le).symm
  rw [hp] at hk
  refine locallyIntegrable_iff.mpr fun K hK => ?_
  by_cases hne : K.Nonempty
  · obtain ⟨z, _, hz⟩ := hK.exists_isMinOn hne hF.continuousOn
    have h := (memLp_density_cutoff (μ.prod μ) hF.measurable hK.measurableSet
      (hFpos z) (fun x hx => hz hx) hk).1
    have hlocal := (memLp_indicator_iff_restrict hK.measurableSet).mp h
    letI : IsFiniteMeasure ((μ.prod μ).restrict K) := ⟨by
      rw [Measure.restrict_apply_univ]
      exact hK.measure_lt_top⟩
    exact memLp_one_iff_integrable.mp (hlocal.mono_exponent (by norm_num : (1 : ℝ≥0∞) ≤ 2))
  · simp [Set.not_nonempty_iff_eq_empty.mp hne]

/-- Theorem 12.1.1.2(1) for a continuous positive density. The original and
smoothed kernels agree in the weighted product measure, and the smoothed
diagonal is regular Haar-almost everywhere and integrates to the trace. -/
theorem RankOneSeries.weighted_kernel_diagonal_trace
    (hw : Continuous w) (hpos : ∀ x, 0 < w x) {U : ℕ → Set G}
    (hU : DoublingSequence μ U) (hcof : CofinalAtOne U)
    {C : ℝ≥0} (hC : 0 < C) (hDiff : ∀ n, μ (U n * (U n)⁻¹) < C * μ (U n))
    (T : RankOneSeries ℕ (G →₂[weighted μ w] ℂ))
    {k : G × G → ℂ} (hk : MemLp k 2 ((weighted μ w).prod (weighted μ w)))
    (hoperator : kernelIntegralOperator (hk.toLp k) = T.operator) :
    let smooth := regularizedLimit (fun n => translatedAverage (μ.prod μ) (U n ×ˢ U n) k)
    (smooth =ᵐ[(weighted μ w).prod (weighted μ w)] k) ∧
      (∀ᵐ x ∂μ, ∃ a, Tendsto
        (fun n => translatedAverage (μ.prod μ) (U n ×ˢ U n) k (x, x)) atTop (𝓝 a)) ∧
      Integrable (fun x => smooth (x, x)) (weighted μ w) ∧
      (∫ x, smooth (x, x) ∂weighted μ w) = T.trace := by
  let ν := weighted μ w
  have hac : ν ≪ μ := withDensity_absolutelyContinuous _ _
  have ht := T.weighted_kernel_diagonal_tendsto_series μ w hw hpos hU hcof hC hDiff hk hoperator
  have hdiag : (fun x => regularizedLimit (fun n => translatedAverage (μ.prod μ) (U n ×ˢ U n) k) (x, x))
      =ᵐ[ν] fun x => ∑' i, T.image i x * star (T.functional i x) :=
    hac.ae_le (ht.mono fun _ hx => regularizedLimit_tendsto hx)
  have hprod : regularizedLimit (fun n => translatedAverage (μ.prod μ) (U n ×ˢ U n) k)
      =ᵐ[ν.prod ν] k := by
    obtain ⟨m, hm, hmcof, hmC⟩ := exists_compact_doublingTail hU hcof
    have hs := doubleWindowSmoothing_ae_eq_of_locallyIntegrable μ hm hmcof
      (by simpa only [zero_add] using hmC) hC (fun n => hDiff (n + m))
      (weighted_kernel_locallyIntegrable μ w hw hpos hk)
    have he := regularizedLimit_nat_add (fun n => translatedAverage (μ.prod μ) (U n ×ˢ U n) k) m
    exact (hac.prod hac).ae_le (he ▸ hs)
  exact ⟨hprod, ht.mono (fun _ hx => ⟨_, hx⟩), (T.diagonal_series_trace ν).1.congr hdiag.symm,
    (integral_congr_ae hdiag).trans (T.diagonal_series_trace ν).2⟩

/-- Multiplication and trace for 12.1.1.2(2) in the weighted space.
The smoothed product identity holds almost everywhere for the product measure
and on the diagonal for Haar measure. -/
theorem RankOneSeries.weighted_kernel_multiplier_trace
    (hw : Continuous w) (hpos : ∀ x, 0 < w x) {U : ℕ → Set G}
    (hU : DoublingSequence μ U) (hcof : CofinalAtOne U)
    {C : ℝ≥0} (hC : 0 < C) (hDiff : ∀ n, μ (U n * (U n)⁻¹) < C * μ (U n))
    (T : RankOneSeries ℕ (G →₂[weighted μ w] ℂ))
    {k : G × G → ℂ} (hk : MemLp k 2 ((weighted μ w).prod (weighted μ w)))
    (hop : kernelIntegralOperator (hk.toLp k) = T.operator)
    {ρ : G → ℂ} (hρ : MemLp ρ ⊤ (weighted μ w)) :
    let ν := weighted μ w
    let M := lpTwoComplexMultiplier hρ.aestronglyMeasurable (ae_norm_le_essentialNorm hρ)
    let m (z : G × G) := ρ z.1 * k z
    let smooth (f : G × G → ℂ) :=
      regularizedLimit (fun n => translatedAverage (μ.prod μ) (U n ×ˢ U n) f)
    ∃ hm : MemLp m 2 (ν.prod ν),
      kernelIntegralOperator (hm.toLp m) = M.comp T.operator ∧
      (smooth m =ᵐ[ν.prod ν] fun z => ρ z.1 * smooth k z) ∧
      ((fun x => smooth m (x, x)) =ᵐ[μ] fun x => ρ x * smooth k (x, x)) ∧
      Integrable (fun x => ρ x * smooth k (x, x)) ν ∧
      (∫ x, ρ x * smooth k (x, x) ∂ν) = (T.leftComp M).trace := by
  let ν := weighted μ w
  let hB := ae_norm_le_essentialNorm hρ
  let M := lpTwoComplexMultiplier hρ.aestronglyMeasurable hB
  let S := T.leftComp M
  let m (z : G × G) := ρ z.1 * k z
  let smooth (f : G × G → ℂ) :=
    regularizedLimit (fun n => translatedAverage (μ.prod μ) (U n ×ˢ U n) f)
  letI : IsLocallyFiniteMeasure ν := IsLocallyFiniteMeasure.withDensity_ofReal hw
  have hμν : μ ≪ ν := withDensity_absolutelyContinuous' hw.measurable.ennreal_ofReal.aemeasurable
    (Eventually.of_forall fun x => (ENNReal.ofReal_pos.mpr (hpos x)).ne')
  have hνμ : ν ≪ μ := withDensity_absolutelyContinuous _ _
  obtain ⟨hm, hM⟩ := kernelIntegralOperator_mul_left hρ.aestronglyMeasurable hB hk
  have hopM : kernelIntegralOperator (hm.toLp m) = S.operator :=
    hM.trans ((congrArg (M.comp ·) hop).trans (T.operator_leftComp M).symm)
  have hkTrace := T.weighted_kernel_diagonal_trace μ w hw hpos hU hcof hC hDiff hk hop
  have hmTrace := S.weighted_kernel_diagonal_trace μ w hw hpos hU hcof hC hDiff hm hopM
  have hprod : smooth m =ᵐ[ν.prod ν] fun z => ρ z.1 * smooth k z := by
    filter_upwards [hmTrace.1, hkTrace.1] with z hz hkz
    change smooth m z = ρ z.1 * k z at hz
    change smooth k z = k z at hkz
    rw [hz, hkz]
  have hdiag : (fun x => smooth m (x, x)) =ᵐ[μ] fun x => ρ x * smooth k (x, x) := by
    filter_upwards [T.weighted_kernel_diagonal_tendsto_series μ w hw hpos hU hcof hC hDiff hk hop,
      S.weighted_kernel_diagonal_tendsto_series μ w hw hpos hU hcof hC hDiff hm hopM,
      hμν.ae_le (T.diagonal_series_left_multiplier_ae hρ.aestronglyMeasurable hB)]
      with x hx hs he
    calc
      smooth m (x, x) = ∑' i, S.image i x * star (S.functional i x) := regularizedLimit_tendsto hs
      _ = ρ x * (∑' i, T.image i x * star (T.functional i x)) := he
      _ = ρ x * smooth k (x, x) := congrArg (ρ x * ·) (regularizedLimit_tendsto hx).symm
  have hd : (fun x => smooth m (x, x)) =ᵐ[ν] fun x => ρ x * smooth k (x, x) :=
    hνμ.ae_le hdiag
  exact ⟨hm, hopM.trans (T.operator_leftComp M), hprod, hdiag,
    hmTrace.2.2.1.congr hd, (integral_congr_ae hd.symm).trans hmTrace.2.2.2⟩

omit [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [BorelSpace G]
  [μ.IsHaarMeasure] [SigmaFinite μ] in
private theorem doubleWindow_subsets_eventually {U : ℕ → Set G}
    (hU : DoublingSequence μ U) (hcof : CofinalAtOne U) (p : G × G) :
    ∀ A ∈ 𝓝 p, ∀ᶠ n in atTop, p • (U n ×ˢ U n) ⊆ A := by
  let W (n : ℕ) := U n ×ˢ U n
  let V (n : ℕ) := p • W n
  have hcofW : CofinalAtOne W :=
    doublingSequence_prod_properties.1 hU.decreasing hU.decreasing hcof hcof
  have hW : Antitone W := fun _ _ hh => Set.prod_mono (hU.decreasing hh) (hU.decreasing hh)
  intro A hA
  have ht : ContinuousAt (fun z : G × G => p * z) 1 := (continuous_const.mul continuous_id).continuousAt
  have hpre : (fun z : G × G => p * z) ⁻¹' A ∈ 𝓝 (1 : G × G) :=
    ht (by simpa only [mul_one] using hA)
  obtain ⟨m, hm⟩ := hcofW _ hpre
  filter_upwards [eventually_ge_atTop m] with n hn
  rintro _ ⟨z, hz, rfl⟩
  exact hm (hW hn hz)

private theorem weighted_kernel_pointwise_mul_tendsto_at
    (hw : Continuous w) (hpos : ∀ x, 0 < w x) {U : ℕ → Set G}
    (hU : DoublingSequence μ U) (hcof : CofinalAtOne U)
    {k : G × G → ℂ} (hk : MemLp k 2 ((weighted μ w).prod (weighted μ w)))
    {ρ : G × G → ℂ} (hρ : Continuous ρ) (p : G × G) {a : ℂ}
    (ha : Tendsto (fun n => translatedAverage (μ.prod μ) (U n ×ˢ U n) k p) atTop (𝓝 a))
    {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ᶠ n in atTop, (⨍ z in p • (U n ×ˢ U n), ‖k z‖ ∂μ.prod μ) ≤ B) :
    Tendsto (fun n => translatedAverage (μ.prod μ) (U n ×ˢ U n) (fun z => ρ z * k z) p)
      atTop (𝓝 (ρ p * a)) := by
  let V (n : ℕ) := p • (U n ×ˢ U n)
  have hsmall := doubleWindow_subsets_eventually μ hU hcof p
  obtain ⟨A, hA, hInt⟩ := weighted_kernel_locallyIntegrable μ w hw hpos hk p
  have hlocal : ∀ᶠ n in atTop, IntegrableOn k (V n) (μ.prod μ) :=
    (hsmall A hA).mono fun _ hsub => hInt.mono_set hsub
  have hmeas (n : ℕ) : NullMeasurableSet (V n) (μ.prod μ) :=
    ((hU.measurable n).prod (hU.measurable n) |>.const_smul p).nullMeasurableSet
  simp only [translatedAverage_eq_average] at ha ⊢
  exact tendsto_average_mul_of_average_norm_bounded (μ.prod μ) hmeas hsmall
    hρ hlocal ha hB hbound

/-- At a fixed regular point, a continuous multiplier commutes with smoothing
when the absolute local means of the kernel are eventually bounded. -/
theorem weighted_kernel_multiplier_tendsto_at
    (hw : Continuous w) (hpos : ∀ x, 0 < w x) {U : ℕ → Set G}
    (hU : DoublingSequence μ U) (hcof : CofinalAtOne U)
    {k : G × G → ℂ} (hk : MemLp k 2 ((weighted μ w).prod (weighted μ w)))
    {ρ : G → ℂ} (hρ : Continuous ρ) (p : G × G) {a : ℂ}
    (ha : Tendsto (fun n => translatedAverage (μ.prod μ) (U n ×ˢ U n) k p) atTop (𝓝 a))
    {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ᶠ n in atTop, (⨍ z in p • (U n ×ˢ U n), ‖k z‖ ∂μ.prod μ) ≤ B) :
    Tendsto (fun n => translatedAverage (μ.prod μ) (U n ×ˢ U n) (fun z => ρ z.1 * k z) p)
      atTop (𝓝 (ρ p.1 * a)) :=
  weighted_kernel_pointwise_mul_tendsto_at μ w hw hpos hU hcof hk
    (hρ.comp continuous_fst) p ha hB hbound

/-- The weighted nuclear kernel satisfies the absolute-mean hypothesis on
almost every Haar diagonal point. -/
theorem RankOneSeries.weighted_kernel_abs_means_ae
    (hw : Continuous w) (hpos : ∀ x, 0 < w x) {U : ℕ → Set G}
    (hU : DoublingSequence μ U) (hcof : CofinalAtOne U)
    {C : ℝ≥0} (hC : 0 < C) (hDiff : ∀ n, μ (U n * (U n)⁻¹) < C * μ (U n))
    (T : RankOneSeries ℕ (G →₂[weighted μ w] ℂ))
    {k : G × G → ℂ} (hk : MemLp k 2 ((weighted μ w).prod (weighted μ w)))
    (hop : kernelIntegralOperator (hk.toLp k) = T.operator) :
    ∀ᵐ x ∂μ, ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ n in atTop,
      (⨍ z in (x, x) • (U n ×ˢ U n), ‖k z‖ ∂μ.prod μ) ≤ B := by
  obtain ⟨m, hm, hmcof, hmC⟩ := exists_compact_doublingTail hU hcof
  have htail := T.weighted_kernel_diagonal_behavior_compact μ w hw hpos hm hmcof
    (by simpa only [zero_add] using hmC) hC (fun n => hDiff (n + m)) hk hop
  filter_upwards [htail] with x hx
  obtain ⟨B, hB, hwindow⟩ := hx.2
  refine ⟨B.toReal, ENNReal.toReal_nonneg, ?_⟩
  obtain ⟨A, hA, hInt⟩ := weighted_kernel_locallyIntegrable μ w hw hpos hk (x, x)
  have hs := doubleWindow_subsets_eventually μ hU hcof (x, x) A hA
  filter_upwards [hs, eventually_ge_atTop m] with n hn hnm
  let V := (x, x) • (U n ×ˢ U n)
  have h := ofReal_average (hInt.mono_set hn).norm (Eventually.of_forall fun _ => norm_nonneg _)
  change ENNReal.ofReal (⨍ z in V, ‖k z‖ ∂μ.prod μ) =
    (∫⁻ z in V, ENNReal.ofReal ‖k z‖ ∂μ.prod μ) / ((μ.prod μ).restrict V) univ at h
  rw [Measure.restrict_apply_univ, show V = (x, x) • (U n ×ˢ U n) from rfl,
    measure_smul, Measure.prod_prod] at h
  apply (ENNReal.ofReal_le_iff_le_toReal hB.ne).mp
  rw [h]
  simpa only [ofReal_norm, Nat.sub_add_cancel hnm] using hwindow (n - m)

omit [Group G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [μ.IsHaarMeasure] in
/-- The same integral operator, written with the kernel against ordinary Haar
measure as in (10.4.3.28). -/
theorem kernelIntegralOperator_haarDensity_apply
    (hw : Continuous w) (hpos : ∀ x, 0 < w x)
    {k : G × G → ℂ} (hk : MemLp k 2 ((weighted μ w).prod (weighted μ w)))
    (f : G →₂[weighted μ w] ℂ) :
    ∀ᵐ x ∂μ, Integrable (fun y => (w y : ℂ) * k (x, y) * f y) μ ∧
      kernelIntegralOperator (hk.toLp k) f x =
        ∫ y, (w y : ℂ) * k (x, y) * f y ∂μ := by
  let ν := weighted μ w
  have hac : μ ≪ ν := withDensity_absolutelyContinuous' hw.measurable.ennreal_ofReal.aemeasurable
    (Eventually.of_forall fun x => (ENNReal.ofReal_pos.mpr (hpos x)).ne')
  have hfinite : ∀ᵐ x ∂μ, ENNReal.ofReal (w x) < ⊤ :=
    Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  filter_upwards [hac.ae_le (kernelIntegralOperator_apply_of_memLp hk f)] with x hx
  have he : (fun y => (ENNReal.ofReal (w y)).toReal • (k (x, y) * f y)) =
      fun y => (w y : ℂ) * k (x, y) * f y := by
    funext y
    rw [ENNReal.toReal_ofReal (hpos y).le, Complex.real_smul, mul_assoc]
  refine ⟨he ▸ (integrable_withDensity_iff_integrable_smul'
    hw.measurable.ennreal_ofReal hfinite).mp hx.1, hx.2.trans ?_⟩
  rw [integral_withDensity_eq_integral_toReal_smul hw.measurable.ennreal_ofReal hfinite, he]

/-- Restoring the source-variable density before smoothing gives the trace
formula with unweighted Haar integration on the diagonal. -/
theorem RankOneSeries.haarDensity_kernel_diagonal_trace
    (hw : Continuous w) (hpos : ∀ x, 0 < w x) {U : ℕ → Set G}
    (hU : DoublingSequence μ U) (hcof : CofinalAtOne U)
    {C : ℝ≥0} (hC : 0 < C) (hDiff : ∀ n, μ (U n * (U n)⁻¹) < C * μ (U n))
    (T : RankOneSeries ℕ (G →₂[weighted μ w] ℂ))
    {k : G × G → ℂ} (hk : MemLp k 2 ((weighted μ w).prod (weighted μ w)))
    (hop : kernelIntegralOperator (hk.toLp k) = T.operator) :
    let raw (z : G × G) := (w z.2 : ℂ) * k z
    let smooth (f : G × G → ℂ) :=
      regularizedLimit (fun n => translatedAverage (μ.prod μ) (U n ×ˢ U n) f)
    (∀ᵐ x ∂μ, ∃ b, Tendsto (fun n =>
      translatedAverage (μ.prod μ) (U n ×ˢ U n) raw (x, x)) atTop (𝓝 b)) ∧
    ((fun x => smooth raw (x, x)) =ᵐ[μ] fun x => (w x : ℂ) * smooth k (x, x)) ∧
    Integrable (fun x => smooth raw (x, x)) μ ∧ (∫ x, smooth raw (x, x) ∂μ) = T.trace := by
  let raw (z : G × G) := (w z.2 : ℂ) * k z
  let smooth (f : G × G → ℂ) :=
    regularizedLimit (fun n => translatedAverage (μ.prod μ) (U n ×ˢ U n) f)
  have htrace := T.weighted_kernel_diagonal_trace μ w hw hpos hU hcof hC hDiff hk hop
  have hlim : ∀ᵐ x ∂μ, Tendsto (fun n =>
      translatedAverage (μ.prod μ) (U n ×ˢ U n) raw (x, x)) atTop
      (𝓝 ((w x : ℂ) * smooth k (x, x))) := by
    filter_upwards [htrace.2.1, T.weighted_kernel_abs_means_ae μ w hw hpos hU hcof hC hDiff hk hop]
      with x hx hbx
    obtain ⟨a, ha⟩ := hx
    obtain ⟨B, hB, hb⟩ := hbx
    have hd : smooth k (x, x) = a := regularizedLimit_tendsto ha
    rw [hd]
    exact weighted_kernel_pointwise_mul_tendsto_at μ w hw hpos hU hcof hk
      (Complex.continuous_ofReal.comp (hw.comp continuous_snd)) (x, x) ha hB hb
  have he : (fun x => smooth raw (x, x)) =ᵐ[μ] fun x => (w x : ℂ) * smooth k (x, x) :=
    hlim.mono fun _ hx => regularizedLimit_tendsto hx
  have hfinite : ∀ᵐ x ∂μ, ENNReal.ofReal (w x) < ⊤ :=
    Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  have heq : (fun x => (ENNReal.ofReal (w x)).toReal • smooth k (x, x)) =
      fun x => (w x : ℂ) * smooth k (x, x) := by
    funext x
    rw [ENNReal.toReal_ofReal (hpos x).le, Complex.real_smul]
  refine ⟨hlim.mono (fun _ hx => ⟨_, hx⟩), he, ?_, ?_⟩
  · exact (heq ▸ (integrable_withDensity_iff_integrable_smul'
      hw.measurable.ennreal_ofReal hfinite).mp htrace.2.2.1).congr he.symm
  · refine (integral_congr_ae he).trans ?_
    have hx := htrace.2.2.2
    rw [integral_withDensity_eq_integral_toReal_smul hw.measurable.ennreal_ofReal hfinite, heq] at hx
    exact hx

/-- The two ambient L² limits and the bounded-test diagonal limit in
12.1.1.2(3) under the manuscript's two Schatten convergence hypotheses. -/
theorem tendsto_weighted_kernel_smoothings
    (hw : Continuous w) (hpos : ∀ x, 0 < w x) {U : ℕ → Set G}
    (hU : DoublingSequence μ U) (hcof : CofinalAtOne U)
    {C : ℝ≥0} (hC : 0 < C) (hDiff : ∀ n, μ (U n * (U n)⁻¹) < C * μ (U n))
    {ι : Type*} {l : Filter ι}
    {T : ι → RankOneSeries ℕ (G →₂[weighted μ w] ℂ)}
    {T₀ : RankOneSeries ℕ (G →₂[weighted μ w] ℂ)}
    {k : ι → G × G → ℂ} {k₀ : G × G → ℂ}
    (hk : ∀ i, MemLp (k i) 2 ((weighted μ w).prod (weighted μ w)))
    (hk₀ : MemLp k₀ 2 ((weighted μ w).prod (weighted μ w)))
    (hop : ∀ i, kernelIntegralOperator ((hk i).toLp (k i)) = (T i).operator)
    (hop₀ : kernelIntegralOperator (hk₀.toLp k₀) = T₀.operator)
    (h₁ : Tendsto (fun i => schattenNorm 1 ((T i).operator - T₀.operator)) l (𝓝 0))
    (h₂ : Tendsto (fun i => schattenNorm 2 ((T i).operator - T₀.operator)) l (𝓝 0)) :
    let ν := weighted μ w
    let smooth (f : G × G → ℂ) :=
      regularizedLimit (fun n => translatedAverage (μ.prod μ) (U n ×ˢ U n) f)
    (Tendsto (fun i => (hk i).toLp (k i)) l (𝓝 (hk₀.toLp k₀))) ∧
    (∃ (hs : ∀ i, MemLp (smooth (k i)) 2 (ν.prod ν)) (hs₀ : MemLp (smooth k₀) 2 (ν.prod ν)),
      Tendsto (fun i => (hs i).toLp (smooth (k i))) l (𝓝 (hs₀.toLp (smooth k₀)))) ∧
    (∀ ρ : G → ℂ, MemLp ρ ⊤ ν →
      Tendsto (fun i => ∫ x, ρ x * smooth (k i) (x, x) ∂ν) l
        (𝓝 (∫ x, ρ x * smooth k₀ (x, x) ∂ν))) := by
  let ν := weighted μ w
  letI : IsLocallyFiniteMeasure ν := IsLocallyFiniteMeasure.withDensity_ofReal hw
  let smooth (f : G × G → ℂ) :=
    regularizedLimit (fun n => translatedAverage (μ.prod μ) (U n ×ˢ U n) f)
  have htrace : Tendsto (fun i => TraceClass.ofSeries (T i)) l (𝓝 (TraceClass.ofSeries T₀)) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    simp only [TraceClass.dist_eq_schattenNorm_one]
    exact h₁
  have ht : Tendsto (fun i => (hk i).toLp (k i)) l (𝓝 (hk₀.toLp k₀)) := by
    apply tendsto_kernel_of_schatten_two ν
    simp only [hop, hop₀]
    exact h₂
  have he (S : RankOneSeries ℕ (G →₂[ν] ℂ)) {f : G × G → ℂ}
      (hf : MemLp f 2 (ν.prod ν)) (hS : kernelIntegralOperator (hf.toLp f) = S.operator) :
      smooth f =ᵐ[ν.prod ν] f :=
    (S.weighted_kernel_diagonal_trace μ w hw hpos hU hcof hC hDiff hf hS).1
  have hs (i : ι) : MemLp (smooth (k i)) 2 (ν.prod ν) :=
    (hk i).ae_eq (he (T i) (hk i) (hop i)).symm
  have hs₀ : MemLp (smooth k₀) 2 (ν.prod ν) := hk₀.ae_eq (he T₀ hk₀ hop₀).symm
  refine ⟨ht, ⟨hs, hs₀, ?_⟩, ?_⟩
  · rw [(MemLp.toLp_eq_toLp_iff hs₀ hk₀).mpr (he T₀ hk₀ hop₀)]
    exact ht.congr fun i => ((MemLp.toLp_eq_toLp_iff (hs i) (hk i)).mpr
      (he (T i) (hk i) (hop i))).symm
  · intro ρ hρ
    have hm (S : RankOneSeries ℕ (G →₂[ν] ℂ)) {f : G × G → ℂ}
        (hf : MemLp f 2 (ν.prod ν)) (hS : kernelIntegralOperator (hf.toLp f) = S.operator) :
        (∫ x, ρ x * smooth f (x, x) ∂ν) = traceClassMultiplierTest hρ (TraceClass.ofSeries S) := by
      rw [traceClassMultiplierTest_ofSeries]
      obtain ⟨_, _, _, _, _, htρ⟩ :=
        S.weighted_kernel_multiplier_trace μ w hw hpos hU hcof hC hDiff hf hS hρ
      exact htρ
    change Tendsto (fun i => ∫ x, ρ x * smooth (k i) (x, x) ∂ν) l
      (𝓝 (∫ x, ρ x * smooth k₀ (x, x) ∂ν))
    rw [hm T₀ hk₀ hop₀]
    exact (((traceClassMultiplierTest hρ).continuous.tendsto _).comp htrace).congr fun i =>
      (hm (T i) (hk i) (hop i)).symm

end

end Masullo
