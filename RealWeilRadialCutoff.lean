import IdelicWeilGammaKernel
import RealLogFourierIdentity

open Filter Function MeasureTheory Metric Set Topology
open scoped Classical SchwartzMap

namespace Masullo

noncomputable section

/-- The reciprocal shell cutoff in the shifted additive real coordinate. -/
def realWeilReciprocalDomain (a : ℝ) : Set ℝ :=
  {y | |1 - y| ≤ a ∨ a⁻¹ ≤ |1 - y|}

private theorem realWeilReciprocalDomain_measurable (a : ℝ) :
    MeasurableSet (realWeilReciprocalDomain a) :=
  ((isClosed_le (continuous_const.sub continuous_id).abs continuous_const).union
    (isClosed_le continuous_const (continuous_const.sub continuous_id).abs)).measurableSet

private theorem realWeil_positive_reference {a : ℝ} (ha : 0 < a) (ha₁ : a ≤ 1) :
    IntegrableOn (fun y : ℝ => ‖y‖⁻¹) (Icc a 1) ∧
      (∫ y in Icc a 1, ‖y‖⁻¹) = -Real.log a := by
  refine ⟨ContinuousOn.integrableOn_Icc (continuous_norm.continuousOn.inv₀
    fun y hy => norm_ne_zero_iff.mpr (ha.trans_le hy.1).ne'), ?_⟩
  calc
    _ = ∫ y in Icc a 1, y⁻¹ := setIntegral_congr_fun measurableSet_Icc fun y hy => by
      rw [Real.norm_of_nonneg (ha.le.trans hy.1)]
    _ = ∫ y in a..1, y⁻¹ := by
      rw [intervalIntegral.integral_of_le ha₁, integral_Icc_eq_integral_Ioc]
    _ = _ := by
      rw [integral_inv, one_div, Real.log_inv]
      rw [uIcc_of_le ha₁]
      exact fun hy => ha.not_ge hy.1

private theorem realWeil_negative_reference {a : ℝ} (ha : 0 < a) (ha₁ : a ≤ 1) :
    IntegrableOn (fun y : ℝ => ‖y‖⁻¹) (Icc (-1 : ℝ) (-a)) ∧
      (∫ y in Icc (-1 : ℝ) (-a), ‖y‖⁻¹) = -Real.log a := by
  refine ⟨ContinuousOn.integrableOn_Icc (continuous_norm.continuousOn.inv₀
    fun y hy => norm_ne_zero_iff.mpr (hy.2.trans_lt (neg_lt_zero.mpr ha)).ne), ?_⟩
  calc
    _ = ∫ y in Icc (-1 : ℝ) (-a), -y⁻¹ := setIntegral_congr_fun measurableSet_Icc fun y hy => by
      rw [Real.norm_of_nonpos (hy.2.trans (neg_nonpos.mpr ha.le)), inv_neg]
    _ = ∫ y in (-1 : ℝ)..(-a), -y⁻¹ := by
      rw [intervalIntegral.integral_of_le (neg_le_neg ha₁), integral_Icc_eq_integral_Ioc]
    _ = _ := by
      rw [intervalIntegral.integral_neg, integral_inv, neg_div_neg_eq]
      norm_num
      rw [uIcc_of_le (neg_le_neg ha₁)]
      exact fun hy => (neg_lt_zero.mpr ha).not_ge hy.2

private theorem realWeil_reciprocal_reference {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 2) :
    let D := realWeilReciprocalDomain (1 - ε) ∩ {y : ℝ | ‖y‖ ≤ 1}
    IntegrableOn (fun y : ℝ => ‖y‖⁻¹) D ∧
      (∫ y in D, ‖y‖⁻¹) = -2 * Real.log ε + Real.log (1 - ε) := by
  let a := 1 - ε
  let b := a⁻¹ - 1
  have ha : 0 < a := by dsimp only [a]; linarith
  have ha₁ : a < 1 := by dsimp only [a]; linarith
  have hhalf : 1 / 2 < a := by dsimp only [a]; linarith
  have hb : 0 < b := sub_pos.mpr ((one_lt_inv₀ ha).mpr ha₁)
  have hb₁ : b ≤ 1 := by
    dsimp only [b]
    have hle : a⁻¹ ≤ 2 := (inv_le_iff_one_le_mul₀ ha).mpr (by linarith)
    linarith
  have he : realWeilReciprocalDomain a ∩ {y : ℝ | ‖y‖ ≤ 1} =
      Icc (-1 : ℝ) (-b) ∪ Icc ε 1 := by
    ext y
    change ((|1 - y| ≤ a ∨ a⁻¹ ≤ |1 - y|) ∧ |y| ≤ 1) ↔
      (-1 ≤ y ∧ y ≤ -b) ∨ (ε ≤ y ∧ y ≤ 1)
    constructor
    · rintro ⟨h, hy⟩
      obtain ⟨hy₁, hy₂⟩ := abs_le.mp hy
      rw [abs_of_nonneg (sub_nonneg.mpr hy₂)] at h
      rcases h with h | h
      · exact Or.inr ⟨by dsimp only [a] at h; linarith, hy₂⟩
      · exact Or.inl ⟨hy₁, by dsimp only [b]; linarith⟩
    · rintro (⟨hy₁, hy₂⟩ | ⟨hy₁, hy₂⟩)
      · have hy : y ≤ 1 := by linarith
        rw [abs_of_nonneg (sub_nonneg.mpr hy)]
        exact ⟨Or.inr (by dsimp only [b] at hy₂; linarith), abs_le.mpr ⟨hy₁, hy⟩⟩
      · rw [abs_of_nonneg (sub_nonneg.mpr hy₂)]
        exact ⟨Or.inl (by dsimp only [a]; linarith), abs_le.mpr ⟨by linarith, hy₂⟩⟩
  have hd : Disjoint (Icc (-1 : ℝ) (-b)) (Icc ε 1) := by
    rw [Set.disjoint_left]
    intro y hy hz
    exact (hε.trans_le hz.1).not_ge (hy.2.trans (neg_nonpos.mpr hb.le))
  obtain ⟨hP, hp⟩ := realWeil_positive_reference hε (by linarith)
  obtain ⟨hN, hn⟩ := realWeil_negative_reference hb hb₁
  have hb' : b = ε / (1 - ε) := by
    dsimp only [b, a]
    field_simp [show 1 - ε ≠ 0 by linarith]
    ring
  change IntegrableOn _ (realWeilReciprocalDomain a ∩ {y : ℝ | ‖y‖ ≤ 1}) ∧
    (∫ y in realWeilReciprocalDomain a ∩ {y : ℝ | ‖y‖ ≤ 1}, ‖y‖⁻¹) = _
  rw [he]
  refine ⟨hN.union hP, ?_⟩
  rw [setIntegral_union hd measurableSet_Icc hN hP, hp, hn, hb',
    Real.log_div hε.ne' ha.ne']
  ring

private theorem realWeil_reciprocal_remainder_tendsto (h : 𝓢(ℝ, ℂ)) :
    Tendsto (fun ε : ℝ => ∫ y in realWeilReciprocalDomain (1 - ε), realLogCutoffRemainder h y)
      (𝓝[>] 0) (𝓝 (∫ y, realLogCutoffRemainder h y)) := by
  let g := realLogCutoffRemainder h
  let D (ε : ℝ) := realWeilReciprocalDomain (1 - ε)
  have hg := realLogCutoffRemainder_integrable h
  have hmeas (ε : ℝ) := realWeilReciprocalDomain_measurable (1 - ε)
  have hbad : ∀ᵐ y : ℝ ∂volume, |1 - y| ≠ 1 := by
    rw [ae_iff]
    have hsub : {y : ℝ | ¬ |1 - y| ≠ 1} ⊆ ({0, 2} : Set ℝ) := by
      intro y hy
      have hy' : |1 - y| = 1 := not_not.mp hy
      rw [abs_eq (by norm_num : (0 : ℝ) ≤ 1)] at hy'
      simp only [mem_insert_iff, mem_singleton_iff]
      rcases hy' with h | h
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
    exact measure_mono_null hsub ((by simp : ({0, 2} : Set ℝ).Finite).measure_zero _)
  have ha : Tendsto (fun ε : ℝ => 1 - ε) (𝓝[>] 0) (𝓝 1) := by
    have h : ContinuousAt (fun ε : ℝ => 1 - ε) 0 :=
      (continuous_const.sub continuous_id).continuousAt
    simpa only [sub_zero] using h.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  have hi : Tendsto (fun ε : ℝ => (1 - ε)⁻¹) (𝓝[>] 0) (𝓝 1) := by
    simpa only [inv_one] using ha.inv₀ one_ne_zero
  have hlim : Tendsto (fun ε : ℝ => ∫ y, (D ε).indicator g y) (𝓝[>] 0) (𝓝 (∫ y, g y)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun y => ‖g y‖)
      (.of_forall fun ε => hg.aestronglyMeasurable.indicator (hmeas ε))
      (.of_forall fun ε => .of_forall fun y => ?_) hg.norm ?_
    · by_cases hy : y ∈ D ε
      · rw [indicator_of_mem hy]
      · rw [indicator_of_notMem hy, norm_zero]
        exact norm_nonneg _
    · filter_upwards [hbad] with y hy
      apply tendsto_const_nhds.congr'
      have hm : ∀ᶠ ε : ℝ in 𝓝[>] 0, y ∈ D ε := by
        rcases lt_or_gt_of_ne hy with h | h
        · exact (ha.eventually (eventually_gt_nhds h)).mono fun ε hε => Or.inl hε.le
        · exact (hi.eventually (eventually_lt_nhds h)).mono fun ε hε => Or.inr hε.le
      exact hm.mono fun ε hε => (indicator_of_mem hε g).symm
  exact hlim.congr' (.of_forall fun ε => integral_indicator (hmeas ε))

/-- The reciprocal real cutoff has the same finite part as the
distance cutoff after the substitution to shifted additive coordinates. -/
theorem realWeil_reciprocalCutoff_tendsto (h : 𝓢(ℝ, ℂ)) :
    Tendsto (fun ε : ℝ =>
      (∫ y in realWeilReciprocalDomain (1 - ε), ‖y‖⁻¹ • h y) + (2 * Real.log ε : ℝ) • h 0)
      (𝓝[>] 0) (𝓝 (∫ y, realLogCutoffRemainder h y)) := by
  have hlog : Tendsto (fun ε : ℝ => Real.log (1 - ε)) (𝓝[>] 0) (𝓝 0) := by
    have h : ContinuousAt (fun ε : ℝ => 1 - ε) 0 :=
      (continuous_const.sub continuous_id).continuousAt
    have ht : Tendsto (fun ε : ℝ => 1 - ε) (𝓝[>] 0) (𝓝 1) := by
      simpa only [sub_zero] using h.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa only [Function.comp_def, Real.log_one] using
      (Real.continuousAt_log (x := 1) one_ne_zero).tendsto.comp ht
  have hh := (realWeil_reciprocal_remainder_tendsto h).add (hlog.smul_const (h 0))
  rw [zero_smul, add_zero] at hh
  refine hh.congr' ?_
  have hsmall : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε < 1 / 2 :=
    (show ∀ᶠ ε : ℝ in 𝓝 0, ε < 1 / 2 from Iio_mem_nhds (by norm_num)).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hsmall] with ε hε hsmall
  have hε' : 0 < ε := hε
  let D := realWeilReciprocalDomain (1 - ε)
  let S := {y : ℝ | ‖y‖ ≤ 1}
  have hS : MeasurableSet S := (isClosed_le continuous_norm continuous_const).measurableSet
  obtain ⟨hi, hv⟩ := realWeil_reciprocal_reference hε' hsmall
  have hq : IntegrableOn (fun y : ℝ => S.indicator (fun y => ‖y‖⁻¹ • h 0) y) D := by
    change Integrable _ (volume.restrict D)
    rw [integrable_indicator_iff hS]
    change Integrable _ ((volume.restrict D).restrict S)
    rw [Measure.restrict_restrict hS, inter_comm]
    exact Integrable.smul_const hi (h 0)
  have hg := (realLogCutoffRemainder_integrable h).integrableOn (s := D)
  have hpw (y : ℝ) : realLogCutoffRemainder h y +
      S.indicator (fun z : ℝ => ‖z‖⁻¹ • h 0) y = ‖y‖⁻¹ • h y := by
    change ‖y‖⁻¹ • (h y - S.indicator (fun _ => h 0) y) + _ = _
    by_cases hy : y ∈ S
    · rw [indicator_of_mem hy, indicator_of_mem hy, smul_sub, sub_add_cancel]
    · rw [indicator_of_notMem hy, indicator_of_notMem hy, sub_zero, add_zero]
  have he : (∫ y in D, ‖y‖⁻¹ • h y) =
      (∫ y in D, realLogCutoffRemainder h y) + (-2 * Real.log ε + Real.log (1 - ε)) • h 0 := by
    simp_rw [← hpw]
    rw [integral_add hg hq, setIntegral_indicator hS, integral_smul_const, hv]
  change (∫ y in D, realLogCutoffRemainder h y) + Real.log (1 - ε) • h 0 =
    (∫ y in D, ‖y‖⁻¹ • h y) + (2 * Real.log ε : ℝ) • h 0
  rw [he, add_smul, neg_mul, neg_smul]
  abel

private theorem realWeil_reciprocal_integrable (h : 𝓢(ℝ, ℂ))
    {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 2) :
    IntegrableOn (fun y : ℝ => ‖y‖⁻¹ • h y) (realWeilReciprocalDomain (1 - ε)) := by
  let D := realWeilReciprocalDomain (1 - ε)
  let S := {y : ℝ | ‖y‖ ≤ 1}
  have hS : MeasurableSet S := (isClosed_le continuous_norm continuous_const).measurableSet
  have hi := (realWeil_reciprocal_reference hε hε').1
  have hq : IntegrableOn (S.indicator (fun y : ℝ => ‖y‖⁻¹ • h 0)) D := by
    change Integrable _ (volume.restrict D)
    rw [integrable_indicator_iff hS]
    change Integrable _ ((volume.restrict D).restrict S)
    rw [Measure.restrict_restrict hS, inter_comm]
    exact Integrable.smul_const hi (h 0)
  have hg := (realLogCutoffRemainder_integrable h).integrableOn (s := D)
  exact (hg.add hq).congr_fun (fun y _ => by
    change ‖y‖⁻¹ • (h y - S.indicator (fun _ => h 0) y) +
      S.indicator (fun y => ‖y‖⁻¹ • h 0) y = _
    by_cases hy : y ∈ S
    · rw [indicator_of_mem hy, indicator_of_mem hy, smul_sub, sub_add_cancel]
    · rw [indicator_of_notMem hy, indicator_of_notMem hy, sub_zero, add_zero])
    (realWeilReciprocalDomain_measurable _)

private theorem realWeil_reciprocal_fold {a : ℝ} (ha : 0 < a)
    (g : ℝ → ℂ) (hg : IntegrableOn g (realWeilReciprocalDomain a)) :
    let R := Ioc 0 a ∪ Ici a⁻¹
    IntegrableOn (fun r : ℝ => g (1 - r) + g (1 + r)) R ∧
      (∫ y in realWeilReciprocalDomain a, g y) =
        ∫ r in R, g (1 - r) + g (1 + r) := by
  let R := Ioc 0 a ∪ Ici a⁻¹
  let D := realWeilReciprocalDomain a
  let M := (fun r : ℝ => 1 - r) '' R
  let P := (fun r : ℝ => 1 + r) '' R
  have hr (r : ℝ) : r ∈ R ↔ 0 < r ∧ (r ≤ a ∨ a⁻¹ ≤ r) := by
    have hi : 0 < a⁻¹ := inv_pos.mpr ha
    change (0 < r ∧ r ≤ a) ∨ a⁻¹ ≤ r ↔ _
    constructor
    · rintro (h | h)
      · exact ⟨h.1, Or.inl h.2⟩
      · exact ⟨hi.trans_le h, Or.inr h⟩
    · rintro ⟨h, h' | h'⟩
      · exact Or.inl ⟨h, h'⟩
      · exact Or.inr h'
  have hM : M = D ∩ Iio 1 := by
    ext y
    constructor
    · rintro ⟨r, hr', rfl⟩
      obtain ⟨hpos, h⟩ := (hr r).mp hr'
      refine ⟨?_, show 1 - r < 1 from sub_lt_self 1 hpos⟩
      change |1 - (1 - r)| ≤ a ∨ a⁻¹ ≤ |1 - (1 - r)|
      rw [sub_sub_cancel, abs_of_pos hpos]
      exact h
    · rintro ⟨hy, hy'⟩
      have hpos : 0 < 1 - y := sub_pos.mpr hy'
      refine ⟨1 - y, (hr _).mpr ⟨hpos, ?_⟩, sub_sub_cancel ..⟩
      change |1 - y| ≤ a ∨ a⁻¹ ≤ |1 - y| at hy
      rwa [abs_of_pos hpos] at hy
  have hP : P = D ∩ Ioi 1 := by
    ext y
    constructor
    · rintro ⟨r, hr', rfl⟩
      obtain ⟨hpos, h⟩ := (hr r).mp hr'
      refine ⟨?_, show 1 < 1 + r from lt_add_of_pos_right 1 hpos⟩
      change |1 - (1 + r)| ≤ a ∨ a⁻¹ ≤ |1 - (1 + r)|
      rw [show 1 - (1 + r) = -r by ring, abs_neg, abs_of_pos hpos]
      exact h
    · rintro ⟨hy, hy'⟩
      have hpos : 0 < y - 1 := sub_pos.mpr hy'
      refine ⟨y - 1, (hr _).mpr ⟨hpos, ?_⟩, by ring⟩
      change |1 - y| ≤ a ∨ a⁻¹ ≤ |1 - y| at hy
      rwa [abs_sub_comm, abs_of_pos hpos] at hy
  have hm : M ⊆ D := hM ▸ inter_subset_left
  have hp : P ⊆ D := hP ▸ inter_subset_left
  have hd : Disjoint M P := by
    rw [hM, hP, Set.disjoint_left]
    intro y hy hz
    exact (show y < 1 from hy.2).not_gt (show 1 < y from hz.2)
  have hPmeas : MeasurableSet P := hP ▸ (realWeilReciprocalDomain_measurable a).inter measurableSet_Ioi
  have hAE : (M ∪ P : Set ℝ) =ᵐ[(volume : Measure ℝ)] D := by
    have hne : ∀ᵐ y : ℝ ∂volume, y ≠ 1 := by
      rw [ae_iff]
      simpa only [not_not, ofPred_eq_eq_singleton] using measure_singleton (1 : ℝ)
    filter_upwards [hne] with y hy
    apply propext
    change y ∈ M ∪ P ↔ y ∈ D
    simp only [hM, hP, mem_union, mem_inter_iff, mem_Iio, mem_Ioi]
    rcases lt_or_gt_of_ne hy with h | h
    · simp [h, h.not_gt]
    · simp [h, h.not_gt]
  let u := MeasurableEquiv.subLeft (1 : ℝ)
  let v := MeasurableEquiv.addLeft (1 : ℝ)
  have h₁ := Measure.measurePreserving_sub_left volume (1 : ℝ)
  have h₂ := measurePreserving_add_left volume (1 : ℝ)
  have hminus : IntegrableOn (fun r : ℝ => g (1 - r)) R :=
    ((h₁.restrict_image_emb u.measurableEmbedding R).integrable_comp_emb u.measurableEmbedding).2
      (hg.mono_set hm)
  have hplus : IntegrableOn (fun r : ℝ => g (1 + r)) R :=
    ((h₂.restrict_image_emb v.measurableEmbedding R).integrable_comp_emb v.measurableEmbedding).2
      (hg.mono_set hp)
  refine ⟨hminus.add hplus, ?_⟩
  change (∫ y in D, g y) = _
  rw [← Measure.restrict_congr_set hAE, setIntegral_union hd hPmeas (hg.mono_set hm) (hg.mono_set hp),
    h₁.setIntegral_image_emb u.measurableEmbedding, h₂.setIntegral_image_emb v.measurableEmbedding,
    ← integral_add hminus hplus]

/-- Exponential substitution on a positive or negative logarithmic ray. -/
theorem weilRadialExp_change (c δ : ℝ) (hc : c ≠ 0)
    (g : ℝ → ℂ) (hg : IntegrableOn g ((fun t : ℝ => Real.exp (c * t)) '' Ici δ)) :
    IntegrableOn (fun t : ℝ => (|c| * Real.exp (c * t)) • g (Real.exp (c * t))) (Ici δ) ∧
      (∫ r in (fun t : ℝ => Real.exp (c * t)) '' Ici δ, g r) =
      ∫ t in Ici δ, (|c| * Real.exp (c * t)) • g (Real.exp (c * t)) := by
  have hd (t : ℝ) (_ : t ∈ Ici δ) :
      HasDerivWithinAt (fun t : ℝ => Real.exp (c * t)) (Real.exp (c * t) * c) (Ici δ) t :=
    ((Real.hasDerivAt_exp (c * t)).comp t (hasDerivAt_const_mul c)).hasDerivWithinAt
  have hi : InjOn (fun t : ℝ => Real.exp (c * t)) (Ici δ) := by
    intro x hx y hy h
    exact mul_left_cancel₀ hc (Real.exp_injective h)
  have he (t : ℝ) : |Real.exp (c * t) * c| = |c| * Real.exp (c * t) := by
    rw [abs_mul, abs_of_pos (Real.exp_pos _), mul_comm]
  exact ⟨by
    simpa only [he] using (integrableOn_image_iff_integrableOn_abs_deriv_smul
      measurableSet_Ici hd hi g).mp hg, by
    simpa only [he] using integral_image_eq_integral_abs_deriv_smul measurableSet_Ici hd hi g⟩

/-- Solving for the reciprocal shell parameter converts the shifted additive
integral into the two half-modulus logarithmic radial integrals. -/
theorem realWeil_reciprocalCutoff_eq_radial (g : ℝ → ℂ) {a : ℝ} (ha : 0 < a) (ha₁ : a < 1)
    (hg : IntegrableOn g (realWeilReciprocalDomain a)) :
    let δ := -2 * Real.log a
    let G (r : ℝ) := g (1 - r) + g (1 + r)
    (∫ y in realWeilReciprocalDomain a, g y) =
      ∫ t in Ioi δ,
        ((Real.exp (t / 2) / 2 : ℝ) • G (Real.exp (t / 2))) +
        ((Real.exp (-t / 2) / 2 : ℝ) • G (Real.exp (-t / 2))) := by
  let δ := -2 * Real.log a
  let G (r : ℝ) := g (1 - r) + g (1 + r)
  obtain ⟨hG, he⟩ := realWeil_reciprocal_fold ha g hg
  have hinner : (fun t : ℝ => Real.exp (-(1 / 2 : ℝ) * t)) '' Ici δ = Ioc 0 a := by
    have heq : -(1 / 2 : ℝ) * δ = Real.log a := by dsimp only [δ]; ring
    ext r
    constructor
    · rintro ⟨t, ht, rfl⟩
      refine ⟨Real.exp_pos _, ?_⟩
      rw [← Real.exp_log ha, Real.exp_le_exp, ← heq]
      exact mul_le_mul_of_nonpos_left ht (by norm_num)
    · rintro ⟨hr₀, hr⟩
      refine ⟨-2 * Real.log r, ?_, ?_⟩
      · change δ ≤ -2 * Real.log r
        exact mul_le_mul_of_nonpos_left (Real.log_le_log hr₀ hr) (by norm_num)
      · change Real.exp (-(1 / 2 : ℝ) * (-2 * Real.log r)) = r
        rw [show -(1 / 2 : ℝ) * (-2 * Real.log r) = Real.log r by ring, Real.exp_log hr₀]
  have houter : (fun t : ℝ => Real.exp ((1 / 2 : ℝ) * t)) '' Ici δ = Ici a⁻¹ := by
    have heq : (1 / 2 : ℝ) * δ = Real.log a⁻¹ := by
      dsimp only [δ]
      rw [Real.log_inv]
      ring
    have hai : 0 < a⁻¹ := inv_pos.mpr ha
    ext r
    constructor
    · rintro ⟨t, ht, rfl⟩
      change a⁻¹ ≤ Real.exp ((1 / 2 : ℝ) * t)
      rw [← Real.exp_log hai, Real.exp_le_exp, ← heq]
      exact mul_le_mul_of_nonneg_left ht (by norm_num)
    · intro hr
      have hr₀ : 0 < r := hai.trans_le hr
      refine ⟨2 * Real.log r, ?_, ?_⟩
      · change δ ≤ 2 * Real.log r
        have hle := Real.log_le_log hai hr
        rw [← heq] at hle
        linarith
      · change Real.exp ((1 / 2 : ℝ) * (2 * Real.log r)) = r
        rw [show (1 / 2 : ℝ) * (2 * Real.log r) = Real.log r by ring, Real.exp_log hr₀]
  have hdis : Disjoint (Ioc 0 a) (Ici a⁻¹) := by
    rw [Set.disjoint_left]
    intro x hx hy
    have h₁ : x ≤ a := hx.2
    have h₂ : a⁻¹ ≤ x := hy
    linarith [(one_lt_inv₀ ha).mpr ha₁]
  have hGI : IntegrableOn G (Ioc 0 a) := hG.mono_set subset_union_left
  have hGO : IntegrableOn G (Ici a⁻¹) := hG.mono_set subset_union_right
  obtain ⟨hi, hi'⟩ := weilRadialExp_change (-(1 / 2 : ℝ)) δ (by norm_num) G (hinner ▸ hGI)
  obtain ⟨ho, ho'⟩ := weilRadialExp_change (1 / 2) δ (by norm_num) G (houter ▸ hGO)
  rw [hinner] at hi'
  rw [houter] at ho'
  change (∫ y in realWeilReciprocalDomain a, g y) = _
  rw [← integral_Ici_eq_integral_Ioi]
  rw [he, setIntegral_union hdis measurableSet_Ici hGI hGO, hi', ho', add_comm, ← integral_add ho hi]
  apply setIntegral_congr_fun measurableSet_Ici
  intro t _
  have h₁ : (1 / 2 : ℝ) * t = t / 2 := by ring
  have h₂ : -(1 / 2 : ℝ) * t = -t / 2 := by ring
  simp only [h₁, h₂, abs_neg, abs_of_nonneg (by norm_num : 0 ≤ (1 / 2 : ℝ))]
  rw [show (1 / 2 : ℝ) * Real.exp (t / 2) = Real.exp (t / 2) / 2 by ring,
    show (1 / 2 : ℝ) * Real.exp (-t / 2) = Real.exp (-t / 2) / 2 by ring]

/-- The two real sign contributions on the reciprocal radial shells. -/
def realWeilShiftedRadial (h : 𝓢(ℝ, ℂ)) (t : ℝ) : ℂ :=
  let G (r : ℝ) := ‖1 - r‖⁻¹ • h (1 - r) + ‖1 + r‖⁻¹ • h (1 + r)
  (Real.exp (t / 2) / 2 : ℝ) • G (Real.exp (t / 2)) +
    (Real.exp (-t / 2) / 2 : ℝ) • G (Real.exp (-t / 2))

/-- The real radial finite part differs from the additive one by the cutoff scale. -/
theorem realWeil_radialCutoff_tendsto (h : 𝓢(ℝ, ℂ)) :
    Tendsto (fun δ : ℝ =>
      (2 : ℝ)⁻¹ • (∫ t in Ioi δ, realWeilShiftedRadial h t) + Real.log δ • h 0)
      (𝓝[>] 0)
      (𝓝 ((2 : ℝ)⁻¹ • (∫ y, realLogCutoffRemainder h y) + Real.log 2 • h 0)) := by
  let ε (δ : ℝ) := 1 - Real.exp (-(δ / 2))
  have hδ : ∀ᶠ δ : ℝ in 𝓝[>] 0, 0 < δ := self_mem_nhdsWithin
  have hεp : ∀ᶠ δ : ℝ in 𝓝[>] 0, 0 < ε δ := hδ.mono fun δ hp =>
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos (half_pos hp)))
  have hεC : Continuous ε := continuous_const.sub (Real.continuous_exp.comp
    (continuous_id.div_const 2).neg)
  have hε0 : ε 0 = 0 := by simp [ε]
  have hεN : Tendsto ε (𝓝[>] 0) (𝓝 0) := by
    have ht : Tendsto ε (𝓝[>] 0) (𝓝 (ε 0)) :=
      hεC.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    simpa only [hε0] using ht
  have hε : Tendsto ε (𝓝[>] 0) (𝓝[>] 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within ε hεN hεp
  have hεsmall : ∀ᶠ δ : ℝ in 𝓝[>] 0, ε δ < 1 / 2 :=
    hεN.eventually (Iio_mem_nhds (by norm_num))
  have hhalf : Tendsto (fun δ : ℝ => δ / 2) (𝓝[>] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have hc : ContinuousAt (fun δ : ℝ => δ / 2) 0 :=
        (continuous_id.div_const (2 : ℝ)).continuousAt
      simpa only [zero_div] using hc.tendsto.mono_left nhdsWithin_le_nhds
    · exact hδ.mono fun δ hp => half_pos hp
  have hlog := tendsto_const_nhds.sub (idelicWeil_radialCounterterm_logLimit.comp hhalf)
    (a := Real.log 2)
  rw [sub_zero] at hlog
  have hlog' : Tendsto (fun δ : ℝ => Real.log δ - Real.log (ε δ)) (𝓝[>] 0)
      (𝓝 (Real.log 2)) := by
    apply hlog.congr'
    filter_upwards [hδ] with δ hp
    change Real.log 2 - (Real.log (ε δ) - Real.log (δ / 2)) = _
    rw [Real.log_div hp.ne' (by norm_num)]
    ring
  refine ((((realWeil_reciprocalCutoff_tendsto h).comp hε).const_smul ((2 : ℝ)⁻¹)).add
    (hlog'.smul_const (h 0))).congr' ?_
  filter_upwards [hεp, hεsmall] with δ hp hs
  have ha : 0 < 1 - ε δ := by linarith
  have ha' : 1 - ε δ < 1 := by linarith
  have hc := realWeil_reciprocalCutoff_eq_radial (fun y => ‖y‖⁻¹ • h y) ha ha'
    (realWeil_reciprocal_integrable h hp hs)
  have hscale : -2 * Real.log (1 - ε δ) = δ := by
    rw [show 1 - ε δ = Real.exp (-(δ / 2)) by simp [ε], Real.log_exp]
    ring
  change (∫ y in realWeilReciprocalDomain (1 - ε δ), ‖y‖⁻¹ • h y) =
      ∫ t in Ioi (-2 * Real.log (1 - ε δ)), realWeilShiftedRadial h t at hc
  rw [hscale] at hc
  change (2 : ℝ)⁻¹ • ((∫ y in realWeilReciprocalDomain (1 - ε δ), ‖y‖⁻¹ • h y) +
    (2 * Real.log (ε δ) : ℝ) • h 0) + (Real.log δ - Real.log (ε δ)) • h 0 = _
  rw [hc, smul_add, smul_smul, inv_mul_cancel_left₀ (by norm_num : (2 : ℝ) ≠ 0)]
  simp only [sub_smul]
  abel

end
end Masullo
