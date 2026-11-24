import MaximalAverages
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Analysis.Normed.Group.Bounded

open Set Filter Topology MeasureTheory
open scoped ENNReal NNReal Pointwise

namespace Masullo

noncomputable section

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
variable (μ : Measure G) [μ.IsMulLeftInvariant]

omit [T2Space G] in
theorem continuous_translateIntegral_of_integrable [μ.Regular]
    {U : Set G} (hU : μ U < ⊤) {f : G → ℂ} (hf : Integrable f μ) :
    Continuous (fun x : G => ∫ y in x • U, f y ∂μ) := by
  let A (f : G → ℂ) (x : G) := ∫ y in x • U, f y ∂μ
  apply continuous_iff_continuousAt.mpr
  intro x₀
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨g, hgC, herr, hgc, hg⟩ := hf.exists_hasCompactSupport_integral_sub_le
    (show 0 < ε / 3 by positivity)
  have hgcont : ContinuousAt (A g) x₀ := by
    have he (x : G) : A g x = ∫ y in U, g (x * y) ∂μ :=
      (measurePreserving_smul x μ).setIntegral_image_emb (measurableEmbedding_const_smul x) g U
    rw [show A g = (fun x => ∫ y in U, g (x * y) ∂μ) from funext he]
    letI : IsFiniteMeasure (μ.restrict U) := ⟨by rwa [Measure.restrict_apply_univ]⟩
    obtain ⟨M, hM⟩ := hgc.norm.bddAbove_range_of_hasCompactSupport hgC.norm
    apply continuousAt_of_dominated (bound := fun _ => M)
    · exact Eventually.of_forall fun x => (hgc.comp (continuous_const.mul continuous_id)).aestronglyMeasurable
    · exact Eventually.of_forall fun x => Eventually.of_forall fun y => hM ⟨x * y, rfl⟩
    · exact integrable_const M
    · exact Eventually.of_forall fun y => (hgc.comp (continuous_id.mul continuous_const)).continuousAt
  have he (x : G) : dist (A f x) (A g x) ≤ ε / 3 := by
    rw [dist_eq_norm]
    change ‖(∫ y in x • U, f y ∂μ) - ∫ y in x • U, g y ∂μ‖ ≤ _
    rw [← integral_sub hf.integrableOn hg.integrableOn]
    calc
      _ ≤ ∫ y in x • U, ‖f y - g y‖ ∂μ := norm_integral_le_integral_norm _
      _ ≤ ∫ y, ‖f y - g y‖ ∂μ := integral_mono_measure Measure.restrict_le_self
        (Eventually.of_forall fun _ => norm_nonneg _) (hf.sub hg).norm
      _ ≤ _ := herr
  filter_upwards [(Metric.tendsto_nhds.mp hgcont) (ε / 3) (by positivity)] with x hx
  change dist (A f x) (A f x₀) < ε
  have h₁ := dist_triangle (A f x) (A g x) (A f x₀)
  have h₂ := dist_triangle (A g x) (A g x₀) (A f x₀)
  linarith [he x, he x₀, dist_comm (A g x₀) (A f x₀)]

/-- Corrected A.5.4.1(1). Local integrability is sufficient for continuity of
a relatively compact translated average. Uniform continuity on compact
subsets follows for any compatible uniform structure. -/
theorem continuous_translateIntegral_of_locallyIntegrable [μ.Regular]
    {U : Set G} (hmU : MeasurableSet U) (hU : IsCompact (closure U))
    {f : G → ℂ} (hf : LocallyIntegrable f μ) :
    Continuous (fun x : G => ∫ y in x • U, f y ∂μ) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  obtain ⟨K, hKc, hK⟩ := exists_compact_mem_nhds x
  let T : Set G := K * closure U
  have hTc : IsCompact T := hKc.mul hU
  have hT : MeasurableSet T := hTc.measurableSet
  let g := T.indicator f
  have hg : Integrable g μ := (integrable_indicator_iff hT).mpr (hf.integrableOn_isCompact hTc)
  have hc : ContinuousAt (fun x : G => ∫ y in x • U, g y ∂μ) x :=
    (continuous_translateIntegral_of_integrable μ
      ((measure_mono subset_closure).trans_lt hU.measure_lt_top) hg).continuousAt
  apply hc.congr
  filter_upwards [hK] with z hz
  apply setIntegral_congr_fun (hmU.const_smul z)
  rintro y ⟨w, hw, rfl⟩
  have hzw : z * w ∈ T := ⟨z, hz, w, subset_closure hw, rfl⟩
  exact Set.indicator_of_mem hzw f

theorem continuous_normalized_translateAverage [μ.Regular]
    {U : Set G} (hmU : MeasurableSet U) (hU : IsCompact (closure U))
    {f : G → ℂ} (hf : LocallyIntegrable f μ) :
    Continuous (fun x : G => (μ.real U)⁻¹ • ∫ y in x • U, f y ∂μ) := by
  show Continuous ((fun _ : G => (μ.real U)⁻¹) • (fun x : G => ∫ y in x • U, f y ∂μ))
  exact continuous_const.smul (continuous_translateIntegral_of_locallyIntegrable μ hmU hU hf)


/-- The normalized translated integral appearing in A.5.4.1. -/
def translatedAverage (U : Set G) (f : G → ℂ) (x : G) : ℂ :=
  (μ.real U)⁻¹ • ∫ y in x • U, f y ∂μ

omit [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [LocallyCompactSpace G] [SecondCountableTopology G] [BorelSpace G] in
theorem translatedAverage_eq_average (U : Set G) (f : G → ℂ) (x : G) :
    translatedAverage μ U f x = ⨍ y in x • U, f y ∂μ := by
  rw [translatedAverage, average_eq, measureReal_def, measureReal_def,
    Measure.restrict_apply_univ, measure_smul]

omit [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [BorelSpace G] [μ.IsMulLeftInvariant] in
theorem translatedAverage_congr_ae (U : Set G) {f g : G → ℂ}
    (h : f =ᵐ[μ] g) : translatedAverage μ U f = translatedAverage μ U g := by
  funext x
  unfold translatedAverage
  rw [integral_congr_ae (ae_restrict_of_ae h)]

variable {U : ℕ → Set G}

omit [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [BorelSpace G] [μ.IsMulLeftInvariant] in
private theorem real_measure_pos_of_stage (hU : DoublingSequence μ U) (n : ℕ) :
    0 < μ.real (U n) := ENNReal.toReal_pos (hU.positive n).ne' (hU.finite n).ne

omit [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [μ.IsMulLeftInvariant] in
private theorem translatedAverage_error_bound (hU : DoublingSequence μ U)
    (f : G → ℂ) (x : G) (n : ℕ) :
    ‖translatedAverage μ (U n) f x‖ₑ ≤
      (μ.withDensity fun y => ‖f y‖ₑ) (x • U n) / μ (U n) := by
  rw [translatedAverage, enorm_smul, Real.enorm_of_nonneg (inv_nonneg.mpr (measureReal_nonneg)),
    ENNReal.ofReal_inv_of_pos (real_measure_pos_of_stage μ hU n), measureReal_def,
    ENNReal.ofReal_toReal (hU.finite n).ne, withDensity_apply _ ((hU.measurable n).const_smul x)]
  rw [div_eq_mul_inv, mul_comm]
  exact mul_le_mul_of_nonneg_right (enorm_integral_le_lintegral_enorm (μ := μ.restrict (x • U n)) f) zero_le

omit [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [BorelSpace G] in
/-- Cofinality of the stages alone gives differentiation at each point of
continuity, when the indicated local integrals exist. -/
theorem translatedAverage_tendsto_of_continuous
    (hU : DoublingSequence μ U) (hcof : CofinalAtOne U)
    {f : G → ℂ} (hfc : Continuous f)
    (hint : ∀ (x : G) (n : ℕ), IntegrableOn f (x • U n) μ) (x : G) :
    Tendsto (fun n => translatedAverage μ (U n) f x) atTop (𝓝 (f x)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have ho : (fun y : G => x * y) ⁻¹' {y | dist (f y) (f x) < ε / 2} ∈ 𝓝 (1 : G) := by
    apply IsOpen.mem_nhds
    · exact (isOpen_lt (continuous_dist.comp (hfc.prodMk continuous_const)) continuous_const).preimage
        (continuous_const.mul continuous_id)
    · simp [show 0 < ε / 2 by positivity]
  obtain ⟨N, hN⟩ := hcof _ ho
  filter_upwards [eventually_ge_atTop N] with n hn
  have hclose (y : G) (hy : y ∈ x • U n) : ‖f y - f x‖ ≤ ε / 2 := by
    obtain ⟨z, hz, rfl⟩ := hy
    have H := (hN (hU.decreasing hn hz))
    rw [← dist_eq_norm]
    exact (show dist (f (x * z)) (f x) < ε / 2 from H).le
  rw [dist_eq_norm]
  have hnorm : ‖∫ y in x • U n, f y - f x ∂μ‖ ≤ (ε / 2) * μ.real (U n) := by
    have hm : μ (x • U n) < ⊤ := by rw [measure_smul]; exact hU.finite n
    have h := norm_setIntegral_le_of_norm_le_const hm hclose
    simpa only [measureReal_def, measure_smul] using h
  have hpos := real_measure_pos_of_stage μ hU n
  have hconst : (∫ _ in x • U n, f x ∂μ) = μ.real (U n) • f x := by
    rw [setIntegral_const, measureReal_def, measure_smul, measureReal_def]
  have hid : translatedAverage μ (U n) f x - f x =
      (μ.real (U n))⁻¹ • (∫ y in x • U n, f y - f x ∂μ) := by
    letI : IsFiniteMeasure (μ.restrict (x • U n)) :=
      ⟨by rw [Measure.restrict_apply_univ, measure_smul]; exact hU.finite n⟩
    rw [integral_sub (hint x n) (integrable_const (f x)), hconst, smul_sub, smul_smul,
      inv_mul_cancel₀ hpos.ne', one_smul]
    rfl
  rw [hid, norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hpos.le)]
  refine (mul_le_mul_of_nonneg_left hnorm (inv_nonneg.mpr hpos.le)).trans_lt ?_
  field_simp [hpos.ne']
  linarith


omit [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [BorelSpace G] [μ.IsMulLeftInvariant] in
private theorem translatedAverage_sub (f g : G → ℂ) {U : Set G} (x : G)
    (hf : IntegrableOn f (x • U) μ) (hg : IntegrableOn g (x • U) μ) :
    translatedAverage μ U (fun y => f y - g y) x =
      translatedAverage μ U f x - translatedAverage μ U g x := by
  simp only [translatedAverage, integral_sub hf hg, smul_sub]

omit [T2Space G] in
/-- The weak estimate controls Lebesgue differentiation errors for globally integrable functions. -/
theorem translatedAverage_ae_of_integrable_of_subset_compact [μ.Regular] (hU : DoublingSequence μ U)
    (hcof : CofinalAtOne U) {K : Set G} (hK : IsCompact K) (hU₀ : U 0 ⊆ K) {C : ℝ≥0}
    (hC : 0 < C) (hDiff : ∀ k, μ (U k * (U k)⁻¹) < C * μ (U k))
    {f : G → ℂ} (hf : Integrable f μ) :
    ∀ᵐ x ∂μ, Tendsto (fun n => translatedAverage μ (U n) f x) atTop (𝓝 (f x)) := by
  let Bad (a : ℝ) := {x | ¬ ∀ᶠ n in atTop, ‖translatedAverage μ (U n) f x - f x‖ < a}
  have hBad (a : ℝ) (ha : 0 < a) : μ (Bad a) = 0 := by
    apply le_antisymm ?_ zero_le
    by_contra! hab
    obtain ⟨ε, -, hε, hεlt⟩ := ENNReal.lt_iff_exists_real_btwn.mp hab
    have hε0 : 0 < ε := ENNReal.ofReal_pos.mp hε
    let d := a / 4
    let η := ε * d / ((C : ℝ) + 1)
    have hd : 0 < d := by dsimp [d]; positivity
    have hη : 0 < η := by dsimp [η]; positivity
    obtain ⟨g, -, hfg, hgc, hg⟩ := hf.exists_hasCompactSupport_integral_sub_le hη
    let e : G → ℝ≥0∞ := fun x => ‖f x - g x‖ₑ
    let Z := {x | ENNReal.ofReal d < densityMaximal μ U e x}
    let P := {x | ENNReal.ofReal d ≤ e x}
    have hE : (∫⁻ x, e x ∂μ) ≤ ENNReal.ofReal η := by
      change (∫⁻ x, ‖(f - g) x‖ₑ ∂μ) ≤ _
      rw [← ofReal_integral_norm_eq_lintegral_enorm (hf.sub hg)]
      exact ENNReal.ofReal_le_ofReal hfg
    have hZ : μ Z ≤ ENNReal.ofReal ((C : ℝ) * η / d) := by
      have h := densityMaximal_global_weak_of_subset_compact μ hU hK hU₀ hC hDiff e
        (ENNReal.ofReal_pos.mpr hd) ENNReal.ofReal_ne_top
      refine h.trans ((mul_le_mul_of_nonneg_left hE zero_le).trans_eq ?_)
      rw [ENNReal.ofReal_div_of_pos hd, ENNReal.ofReal_mul C.coe_nonneg,
        ENNReal.ofReal_coe_nnreal]
      simp only [div_eq_mul_inv]
      ac_rfl
    have hP : μ P ≤ ENNReal.ofReal (η / d) := by
      have hmeas : AEMeasurable e μ := (hf.sub hg).aestronglyMeasurable.enorm
      have h := meas_ge_le_lintegral_div hmeas (ENNReal.ofReal_pos.mpr hd).ne'
        ENNReal.ofReal_ne_top
      rw [ENNReal.ofReal_div_of_pos hd]
      exact h.trans (ENNReal.div_le_div_right hE _)
    have hsubset : Bad a ⊆ Z ∪ P := by
      intro x hx
      by_contra! he
      have hZM : densityMaximal μ U e x ≤ ENNReal.ofReal d := le_of_not_gt (fun h => he (Or.inl h))
      have hPP : e x < ENNReal.ofReal d := lt_of_not_ge (fun h => he (Or.inr h))
      have hpp : ‖f x - g x‖ < d := by
        rw [show e x = ENNReal.ofReal ‖f x - g x‖ from (ofReal_norm _).symm] at hPP
        exact (ENNReal.ofReal_lt_ofReal_iff hd).mp hPP
      have hda : ENNReal.ofReal d < ENNReal.ofReal (a / 3) :=
        (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr (by dsimp [d]; linarith)
      have hb₂ : ∀ᶠ n in atTop,
          (μ.withDensity e) (x • U n) / μ (U n) < ENNReal.ofReal (a / 3) :=
        eventually_lt_of_limsup_lt (hZM.trans_lt hda)
      have hb₃ : ∀ᶠ n in atTop, ‖translatedAverage μ (U n) g x - g x‖ < a / 3 :=
        (Metric.tendsto_nhds.mp
          (translatedAverage_tendsto_of_continuous μ hU hcof hgc (fun _ _ => hg.integrableOn) x))
          (a / 3) (by positivity) |>.mono (fun _ h => by simpa only [dist_eq_norm] using h)
      apply hx
      filter_upwards [hb₂, hb₃] with n hn₂ hn₃
      have heq := translatedAverage_sub μ f g (U := U n) x hf.integrableOn hg.integrableOn
      have h₁ : ‖translatedAverage μ (U n) f x - translatedAverage μ (U n) g x‖ < a / 3 := by
        rw [← heq]
        apply (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mp
        rw [ofReal_norm]
        exact (translatedAverage_error_bound μ hU (fun y => f y - g y) x n).trans_lt hn₂
      have ht₁ := dist_triangle (translatedAverage μ (U n) f x)
        (translatedAverage μ (U n) g x) (f x)
      have ht₂ := dist_triangle (translatedAverage μ (U n) g x) (g x) (f x)
      simp only [dist_eq_norm, norm_sub_rev (g x) (f x)] at ht₁ ht₂
      dsimp [d] at hpp
      linarith
    have hC0 : 0 ≤ (C : ℝ) * η / d := by positivity
    have hs : ENNReal.ofReal ((C : ℝ) * η / d) + ENNReal.ofReal (η / d) = ENNReal.ofReal ε := by
      rw [← ENNReal.ofReal_add hC0 (by positivity)]
      congr 1
      dsimp [η]
      have hn : (C : ℝ) + 1 ≠ 0 := by positivity
      field_simp [hn, hd.ne']
    exact hεlt.not_ge ((measure_mono hsubset).trans ((measure_union_le Z P).trans
      ((add_le_add hZ hP).trans_eq hs)))
  have hcount : ∀ᵐ x ∂μ, ∀ m : ℕ, x ∉ Bad (1 / ((m : ℝ) + 1)) := by
    apply ae_all_iff.mpr
    intro m
    exact ae_iff.mpr (by simpa using hBad (1 / ((m : ℝ) + 1)) (by positivity))
  filter_upwards [hcount] with x hx
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hsmall : ∀ᶠ m : ℕ in atTop, 1 / ((m : ℝ) + 1) < ε :=
    tendsto_one_div_add_atTop_nhds_zero_nat.eventually (gt_mem_nhds hε)
  obtain ⟨m, hm⟩ := hsmall.exists
  have hb : ∀ᶠ n in atTop, ‖translatedAverage μ (U n) f x - f x‖ < 1 / ((m : ℝ) + 1) :=
    not_not.mp (hx m)
  exact hb.mono fun n hn => by rw [dist_eq_norm]; exact hn.trans hm

omit [T2Space G] in
theorem translatedAverage_ae_of_integrable [μ.Regular] (hU : DoublingSequence μ U)
    (hcof : CofinalAtOne U) (hU₀ : IsCompact (U 0)) {C : ℝ≥0}
    (hC : 0 < C) (hDiff : ∀ k, μ (U k * (U k)⁻¹) < C * μ (U k))
    {f : G → ℂ} (hf : Integrable f μ) :
    ∀ᵐ x ∂μ, Tendsto (fun n => translatedAverage μ (U n) f x) atTop (𝓝 (f x)) :=
  translatedAverage_ae_of_integrable_of_subset_compact μ hU hcof hU₀ Subset.rfl hC hDiff hf

/-- Corrected Theorem A.5.4.1. Relatively compact stages give continuous averages,
and the cofinal same-stage covering hypothesis gives a.e. recovery. -/
theorem translatedAverage_ae_of_locallyIntegrable_of_isCompact_closure
    [μ.Regular] (hU : DoublingSequence μ U)
    (hcof : CofinalAtOne U) (hU₀ : IsCompact (closure (U 0))) {C : ℝ≥0}
    (hC : 0 < C) (hDiff : ∀ k, μ (U k * (U k)⁻¹) < C * μ (U k))
    {f : G → ℂ} (hf : LocallyIntegrable f μ) :
    (∀ n, Continuous (translatedAverage μ (U n) f)) ∧
    (∀ᵐ x ∂μ, Tendsto (fun n => translatedAverage μ (U n) f x) atTop (𝓝 (f x))) := by
  refine ⟨fun n => continuous_normalized_translateAverage μ (hU.measurable n)
    (hU₀.of_isClosed_subset isClosed_closure
      (closure_mono (hU.decreasing (Nat.zero_le n)))) hf, ?_⟩
  have hk : ∀ m : ℕ, ∀ᵐ x ∂μ, x ∈ compactCovering G m →
      Tendsto (fun n => translatedAverage μ (U n) f x) atTop (𝓝 (f x)) := by
    intro m
    let T := compactCovering G m * closure (U 0)
    have hT : IsCompact T := (isCompact_compactCovering G m).mul hU₀
    let g := T.indicator f
    have hg : Integrable g μ := (integrable_indicator_iff hT.measurableSet).mpr
      (hf.integrableOn_isCompact hT)
    filter_upwards [translatedAverage_ae_of_integrable_of_subset_compact
      μ hU hcof hU₀ subset_closure hC hDiff hg] with x hx hxm
    have hxT : x ∈ T := ⟨x, hxm, 1, subset_closure (hU.one_mem 0), mul_one x⟩
    have hgf : g x = f x := Set.indicator_of_mem hxT f
    rw [hgf] at hx
    apply hx.congr
    intro n
    unfold translatedAverage
    congr 1
    apply setIntegral_congr_fun ((hU.measurable n).const_smul x)
    rintro _ ⟨y, hy, rfl⟩
    have hxy : x * y ∈ T := ⟨x, hxm, y, subset_closure (hU.decreasing (Nat.zero_le n) hy), rfl⟩
    exact Set.indicator_of_mem hxy f
  filter_upwards [ae_all_iff.mpr hk] with x hx
  obtain ⟨m, hm⟩ := exists_mem_compactCovering x
  exact hx m hm

theorem translatedAverage_ae_of_locallyIntegrable [μ.Regular] (hU : DoublingSequence μ U)
    (hcof : CofinalAtOne U) (hU₀ : IsCompact (U 0)) {C : ℝ≥0}
    (hC : 0 < C) (hDiff : ∀ k, μ (U k * (U k)⁻¹) < C * μ (U k))
    {f : G → ℂ} (hf : LocallyIntegrable f μ) :
    (∀ n, Continuous (translatedAverage μ (U n) f)) ∧
    (∀ᵐ x ∂μ, Tendsto (fun n => translatedAverage μ (U n) f x) atTop (𝓝 (f x))) :=
  translatedAverage_ae_of_locallyIntegrable_of_isCompact_closure μ hU hcof hU₀.closure hC hDiff hf


/-- The complement of the regular points is negligible, and the regular
limit agrees with the original function almost everywhere there. -/
theorem translatedAverage_regular_points [μ.Regular]
    (hU : DoublingSequence μ U) (hcof : CofinalAtOne U) (hU₀ : IsCompact (U 0)) {C : ℝ≥0}
    (hC : 0 < C) (hDiff : ∀ k, μ (U k * (U k)⁻¹) < C * μ (U k))
    {f : G → ℂ} (hf : LocallyIntegrable f μ) :
    let Reg : Set G := {x | ∃ z : ℂ, Tendsto (fun n => translatedAverage μ (U n) f x) atTop (𝓝 z)}
    μ Regᶜ = 0 ∧
    (∀ᵐ x ∂μ.restrict Reg, Tendsto (fun n => translatedAverage μ (U n) f x) atTop (𝓝 (f x))) := by
  have h := (translatedAverage_ae_of_locallyIntegrable μ hU hcof hU₀ hC hDiff hf).2
  refine ⟨?_, ae_restrict_of_ae h⟩
  exact ae_iff.mp (h.mono fun x hx => show ∃ z : ℂ, _ from ⟨f x, hx⟩)

section Sequence

variable {X : Type*}

/-- Choose the limit at regular points and use zero off the convergence set. -/
def regularizedLimit (a : ℕ → X → ℂ) (x : X) : ℂ := by
  classical
  exact if h : ∃ z : ℂ, Tendsto (fun n => a n x) atTop (𝓝 z) then h.choose else 0

theorem regularizedLimit_tendsto {a : ℕ → X → ℂ} {x : X} {z : ℂ}
    (h : Tendsto (fun n => a n x) atTop (𝓝 z)) : regularizedLimit a x = z := by
  have he : ∃ z : ℂ, Tendsto (fun n => a n x) atTop (𝓝 z) := ⟨z, h⟩
  rw [regularizedLimit, dite_eq_left he]
  exact tendsto_nhds_unique he.choose_spec h

theorem tendsto_regularizedLimit {a : ℕ → X → ℂ} {x : X}
    (h : ∃ z : ℂ, Tendsto (fun n => a n x) atTop (𝓝 z)) :
    Tendsto (fun n => a n x) atTop (𝓝 (regularizedLimit a x)) := by
  obtain ⟨z, hz⟩ := h
  rwa [regularizedLimit_tendsto hz]

/-- Discarding finitely many averaging windows preserves the regularized limit. -/
theorem regularizedLimit_nat_add (a : ℕ → X → ℂ) (m : ℕ) :
    regularizedLimit (fun n => a (n + m)) = regularizedLimit a := by
  funext x
  by_cases h : ∃ z, Tendsto (fun n => a n x) atTop (𝓝 z)
  · obtain ⟨z, hz⟩ := h
    rw [regularizedLimit_tendsto hz, regularizedLimit_tendsto ((tendsto_add_atTop_iff_nat m).mpr hz)]
  · have ht : ¬ ∃ z, Tendsto (fun n => a (n + m) x) atTop (𝓝 z) := by
      rintro ⟨z, hz⟩
      exact h ⟨z, (tendsto_add_atTop_iff_nat m).mp hz⟩
    simp [regularizedLimit, ht, h]

theorem regularizedLimit_measurable [MeasurableSpace X] {a : ℕ → X → ℂ}
    (hm : ∀ n, Measurable (a n)) : Measurable (regularizedLimit a) := by
  let E := {x | ∃ z : ℂ, Tendsto (fun n => a n x) atTop (𝓝 z)}
  have hE : MeasurableSet E := measurableSet_exists_tendsto hm
  have h0 : Eᶜ.domRestrict (regularizedLimit a) = fun _ => 0 := by
    funext x
    change regularizedLimit a x.val = 0
    exact dite_eq_right x.property
  refine measurable_of_restrict_of_restrict_compl hE ?_ (h0 ▸ measurable_const)
  refine measurable_of_tendsto_metrizable' atTop
    (fun n => (hm n).comp measurable_subtype_coe) (tendsto_pi_nhds.mpr fun p => ?_)
  have hp := p.property
  change Tendsto (fun n => a n p.val) atTop (𝓝 (regularizedLimit a p.val))
  rw [regularizedLimit_tendsto hp.choose_spec]
  exact hp.choose_spec

end Sequence

omit [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [BorelSpace G] [μ.IsMulLeftInvariant] in
/-- Two almost everywhere equal representatives have identical smoothed
values everywhere, including at points of a product-null diagonal. -/
theorem regularizedLimit_translatedAverage_congr_ae (U : ℕ → Set G)
    {f g : G → ℂ} (h : f =ᵐ[μ] g) :
    regularizedLimit (fun n => translatedAverage μ (U n) f) =
      regularizedLimit (fun n => translatedAverage μ (U n) g) :=
  congrArg regularizedLimit (funext fun n => translatedAverage_congr_ae μ (U n) h)

end

end Masullo
