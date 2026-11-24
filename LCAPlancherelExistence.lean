/-
Adapted from the Apache-2.0 RiemannMasullo project at
3b4b2cd6915a243a5299a26001ca6b1c1a2ed037, AppD_SchwartzBruhat/Sec1a.lean
and the ForMathlib modules ProdRegular, ContinuousMapDense and RegularDomination.
See External/PROVENANCE.md and External/RiemannMasullo.LICENSE.
-/
import LCAPlancherel
import LCAConvolution
import PontryaginSeparation
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Continuous
import Mathlib.Topology.TietzeExtension

noncomputable section

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal Pointwise ZeroAtInfty

namespace Masullo

/-- A finite regular measure is carried by a countable union of compact sets. -/
private theorem exists_isSigmaCompact_ae_mem
    {X : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
    (ν : Measure X) [IsFiniteMeasure ν] [ν.Regular] :
    ∃ S : Set X, IsSigmaCompact S ∧ ∀ᵐ x ∂ν, x ∈ S := by
  obtain ⟨ε, -, hε, hlim⟩ := exists_seq_strictAnti_tendsto' (zero_lt_one : (0 : ℝ≥0∞) < 1)
  choose K _ hK hSmall using fun n ↦ MeasurableSet.univ.exists_isCompact_sdiff_lt
    (μ := ν) (measure_ne_top ν univ) (hε n).1.ne'
  let S := ⋃ n, K n
  refine ⟨S, ⟨K, hK, rfl⟩, ?_⟩
  rw [ae_iff]
  change ν Sᶜ = 0
  by_contra h
  have ht : ∀ᶠ n in atTop, ε n < ν Sᶜ := hlim (Iio_mem_nhds (pos_iff_ne_zero.mpr h))
  obtain ⟨n, hn⟩ := ht.exists
  have hs : ν Sᶜ ≤ ν (univ \ K n) := measure_mono <|
    fun x hx ↦ ⟨mem_univ x, fun hk ↦ hx (mem_iUnion.mpr ⟨n, hk⟩)⟩
  exact (hs.trans_lt (hSmall n)).not_gt hn

/-- A continuous kernel on a product, set to zero outside a product of σ-compact sets, is
measurable for the product σ-algebra. -/
private theorem measurable_indicator_prod_of_isSigmaCompact
    {X Y E : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [T2Space Y] [MeasurableSpace Y] [BorelSpace Y]
    [TopologicalSpace E] [TopologicalSpace.PseudoMetrizableSpace E] [Zero E] [MeasurableSpace E] [BorelSpace E]
    {k : X × Y → E} (hk : Continuous k) {S : Set X} {T : Set Y}
    (hS : IsSigmaCompact S) (hT : IsSigmaCompact T) :
    Measurable ((S ×ˢ T).indicator k) := by
  classical
  obtain ⟨K, hK, rfl⟩ := hS
  obtain ⟨L, hL, rfl⟩ := hT
  have hRect (n m : ℕ) (U : Set E) (hU : MeasurableSet U) :
      MeasurableSet ((K n ×ˢ L m) ∩ k ⁻¹' U) := by
    let e : K n × L m → X × Y := Prod.map Subtype.val Subtype.val
    have he : MeasurableEmbedding e :=
      (MeasurableEmbedding.subtype_coe (hK n).isClosed.measurableSet).prodMap
        (MeasurableEmbedding.subtype_coe (hL m).isClosed.measurableSet)
    let : CompactSpace (K n) := isCompact_iff_compactSpace.mp (hK n)
    let : CompactSpace (L m) := isCompact_iff_compactSpace.mp (hL m)
    have hc : Continuous (k ∘ e) :=
      hk.comp ((continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd))
    have hm : Measurable (k ∘ e) := (HasCompactSupport.of_compactSpace _).measurable_of_prod hc
    have hr : range e = K n ×ˢ L m := by
      ext ⟨x, y⟩
      constructor
      · rintro ⟨⟨a, b⟩, heq⟩
        rw [← heq]
        exact ⟨a.property, b.property⟩
      · intro h
        exact ⟨(⟨x, h.1⟩, ⟨y, h.2⟩), rfl⟩
    have heq : e '' ((k ∘ e) ⁻¹' U) = (K n ×ˢ L m) ∩ k ⁻¹' U := by
      rw [preimage_comp, image_preimage_eq_inter_range, hr, inter_comm]
    rw [← heq]
    exact he.measurableSet_image' (hm hU)
  let R := (⋃ n, K n) ×ˢ (⋃ m, L m)
  have hR : MeasurableSet R := (MeasurableSet.iUnion fun n ↦ (hK n).isClosed.measurableSet).prod
    (MeasurableSet.iUnion fun m ↦ (hL m).isClosed.measurableSet)
  intro U hU
  have hOn : MeasurableSet (R ∩ k ⁻¹' U) := by
    have heq : R ∩ k ⁻¹' U = ⋃ n, ⋃ m, ((K n ×ˢ L m) ∩ k ⁻¹' U) := by
      simp only [R, ← iUnion_prod, iUnion_inter, iUnion_prod']
    rw [heq]
    exact MeasurableSet.iUnion fun n ↦ MeasurableSet.iUnion fun m ↦ hRect n m U hU
  by_cases h : (0 : E) ∈ U
  · convert hOn.union hR.compl using 1
    ext p
    by_cases hp : p ∈ R <;> change ((R.indicator k p ∈ U) ↔ _)
    all_goals simp [hp, h]
  · convert hOn using 1
    ext p
    by_cases hp : p ∈ R <;> change ((R.indicator k p ∈ U) ↔ _)
    all_goals simp [hp, h]

/-- A measure dominated by a finite regular measure on a Hausdorff Borel space is regular. -/
private theorem regular_of_le_finite_regular {X : Type*} [TopologicalSpace X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X] (μ ν : Measure X) [IsFiniteMeasure ν]
    [ν.Regular] (h : μ ≤ ν) : μ.Regular := by
  have : IsFiniteMeasure μ := isFiniteMeasure_of_le ν h
  have : μ.InnerRegularCompactLTTop := by
    constructor
    intro A hA r hr
    have he : μ A - r ≠ 0 := ne_of_gt (tsub_pos_of_lt hr)
    obtain ⟨K, hKA, hK, hsmall⟩ :=
      hA.1.exists_isCompact_sdiff_lt (μ := ν) (measure_ne_top ν A) he
    refine ⟨K, hKA, hK, ?_⟩
    have hd : μ (A \ K) < μ A - r := lt_of_le_of_lt (h (A \ K)) hsmall
    have hsum : μ A = μ K + μ (A \ K) := by
      simpa [union_eq_right.mpr hKA] using
        (measure_add_sdiff (μ := μ) hK.measurableSet.nullMeasurableSet A).symm
    rw [lt_tsub_iff_right] at hd
    rw [hsum] at hd
    exact (ENNReal.add_lt_add_iff_right (measure_ne_top μ (A \ K))).mp
      (by simpa [add_comm] using hd)
  infer_instance


section CompactTests

open scoped CompactlySupported ENNReal NNReal

variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [MeasurableSpace X] [BorelSpace X]

/-- A bounded density with a σ-compact carrier over a regular measure is inner regular. -/
private theorem innerRegular_withDensity_of_le_of_isSigmaCompact
    (η : Measure X) [η.Regular] {w : X → ℝ≥0∞} {C : ℝ≥0}
    (hBound : ∀ x, w x ≤ C) {S : Set X} (hS : IsSigmaCompact S)
    (hW : Function.support w ⊆ S) : (η.withDensity w).InnerRegular := by
  let ν := η.withDensity w
  obtain ⟨K, hK, rfl⟩ := hS
  let L := accumulate K
  have hL (n : ℕ) : IsCompact (L n) := isCompact_accumulate hK n
  have hLm (n : ℕ) : MeasurableSet (L n) := (hL n).isClosed.measurableSet
  have hUnion : (⋃ n, L n) = ⋃ n, K n := iUnion_accumulate
  have hSm : MeasurableSet (⋃ n, L n) := MeasurableSet.iUnion hLm
  have hSupp : ∀ᵐ x ∂ν, x ∈ ⋃ n, L n := by
    rw [ae_iff]
    change ν (⋃ n, L n)ᶜ = 0
    rw [withDensity_apply _ hSm.compl]
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    filter_upwards [ae_restrict_mem hSm.compl] with x hx
    by_contra hn
    exact hx (hUnion ▸ hW hn)
  have hRestr (n : ℕ) : (ν.restrict (L n)).InnerRegular := by
    let : Fact (η (L n) < ∞) := ⟨(hL n).measure_lt_top⟩
    let : (η.restrict (L n)).Regular :=
      Measure.Regular.restrict_of_measure_ne_top (hL n).measure_lt_top.ne
    let Cη := C • η.restrict (L n)
    let : Cη.Regular := inferInstanceAs (C • η.restrict (L n)).Regular
    have hDom : ν.restrict (L n) ≤ Cη := by
      rw [show ν = η.withDensity w from rfl, restrict_withDensity (hLm n),
        show Cη = (C : ℝ≥0∞) • η.restrict (L n) from rfl, ← withDensity_const]
      exact withDensity_mono (.of_forall hBound)
    let : IsFiniteMeasure (ν.restrict (L n)) := isFiniteMeasure_of_le Cη hDom
    let := regular_of_le_finite_regular _ Cη hDom
    infer_instance
  constructor
  intro s hs r hr
  have hEq : ν s = ⨆ n, ν (s ∩ L n) := by
    conv_lhs => rw [← Measure.restrict_eq_self_of_ae_mem hSupp, Measure.restrict_apply hs]
    rw [inter_iUnion, (monotone_const.inter monotone_accumulate).measure_iUnion]
  rw [hEq] at hr
  obtain ⟨n, hn⟩ := lt_iSup_iff.mp hr
  let := hRestr n
  rw [← Measure.restrict_apply hs] at hn
  obtain ⟨A, hA, hAc, hAn⟩ := hs.exists_lt_isCompact hn
  exact ⟨A, hA, hAc, hAn.trans_le (Measure.restrict_apply_le _ _)⟩

/-- Nonnegative compactly supported continuous tests determine inner regular measures
when one of the two measures is locally finite. -/
private theorem measure_eq_of_lintegral_eq_on_compactlySupported_nnreal
    (μ ν : Measure X) [μ.InnerRegular] [ν.InnerRegular] [IsLocallyFiniteMeasure ν]
    (h : ∀ f : C_c(X, ℝ≥0), (∫⁻ x, (f x : ℝ≥0∞) ∂μ) = ∫⁻ x, (f x : ℝ≥0∞) ∂ν) :
    μ = ν := by
  have hle (m n : Measure X) [n.InnerRegular] [IsLocallyFiniteMeasure n]
      (h' : ∀ f : C_c(X, ℝ≥0), (∫⁻ x, (f x : ℝ≥0∞) ∂m) ≤
        ∫⁻ x, (f x : ℝ≥0∞) ∂n)
      {K : Set X} (hK : IsCompact K) : m K ≤ n K := by
    by_contra! hLt
    obtain ⟨V, hKV, hV, hVn⟩ := hK.exists_isOpen_lt_of_lt (μ := n) (m K) hLt
    obtain ⟨f, hf, hfc, hfs, h01⟩ :=
      exists_continuousMap_one_of_isCompact_subset_isOpen hK hV hKV
    let u := (⟨f, hfc⟩ : C_c(X, ℝ)).nnrealPart
    have huK (x : X) (hx : x ∈ K) : (u x : ℝ≥0∞) = 1 := by
      change ENNReal.ofReal (f x) = 1
      exact ENNReal.ofReal_eq_one.mpr (hf hx)
    have huV (x : X) : (u x : ℝ≥0∞) ≤ V.indicator (fun _ ↦ (1 : ℝ≥0∞)) x := by
      by_cases hx : x ∈ V
      · rw [indicator_of_mem hx]
        change ENNReal.ofReal (f x) ≤ 1
        exact ENNReal.ofReal_le_one.mpr (h01 x).2
      · have hz := image_eq_zero_of_notMem_tsupport (fun hx' ↦ hx (hfs hx'))
        rw [indicator_of_notMem hx]
        change ENNReal.ofReal (f x) ≤ 0
        simp [hz]
    have hLow : m K ≤ ∫⁻ x, (u x : ℝ≥0∞) ∂m := by
      rw [← setLIntegral_one]
      refine (setLIntegral_congr_fun hK.isClosed.measurableSet
        (fun x hx ↦ (huK x hx).symm)).le.trans (setLIntegral_le_lintegral _ _)
    have hHigh : (∫⁻ x, (u x : ℝ≥0∞) ∂n) ≤ n V :=
      (lintegral_mono huV).trans_eq (by simpa using lintegral_indicator_const (μ := n) hV.measurableSet 1)
    exact hVn.not_ge (hLow.trans ((h' u).trans hHigh))
  have hμν {K : Set X} (hK : IsCompact K) : μ K ≤ ν K := hle μ ν (fun f ↦ (h f).le) hK
  let : IsFiniteMeasureOnCompacts μ :=
    ⟨fun K hK ↦ (hμν hK).trans_lt hK.measure_lt_top⟩
  have hνμ {K : Set X} (hK : IsCompact K) : ν K ≤ μ K := hle ν μ (fun f ↦ (h f).ge) hK
  ext1 s hs
  rw [hs.measure_eq_iSup_isCompact μ, hs.measure_eq_iSup_isCompact ν]
  exact iSup_congr fun K ↦ iSup_congr fun _ ↦ iSup_congr fun hK ↦
    le_antisymm (hμν hK) (hνμ hK)

end CompactTests

/-- Haar averaging of a translated nonnegative weight can be computed by integrating
over Haar first. A σ-compact carrier for the weight suffices for Tonelli. -/
private theorem lintegral_lintegral_mul_translate
    {H : Type*} [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]
    [LocallyCompactSpace H] [MeasurableSpace H] [BorelSpace H]
    (η τ : Measure H) [η.IsHaarMeasure] [IsFiniteMeasure τ] [τ.Regular]
    {w v : H → ℝ≥0} (hw : Continuous w) (hv : Continuous v)
    {U : Set H} (hU : IsSigmaCompact U) (hW : Function.support w ⊆ U) :
    (∫⁻ a, ∫⁻ b, (w (a * b) : ℝ≥0∞) * (v b : ℝ≥0∞) ∂τ ∂η) =
      (∫⁻ a, (w a : ℝ≥0∞) ∂η) * (∫⁻ b, (v b : ℝ≥0∞) ∂τ) := by
  obtain ⟨S, hS, hτ⟩ := exists_isSigmaCompact_ae_mem τ
  obtain ⟨K, hK, rfl⟩ := hU
  obtain ⟨L, hL, rfl⟩ := hS
  let T : Set H := ⋃ p : ℕ × ℕ, K p.1 * (L p.2)⁻¹
  have hC (p : ℕ × ℕ) : IsCompact (K p.1 * (L p.2)⁻¹) := (hK p.1).mul (hL p.2).inv
  have hTm : MeasurableSet T := MeasurableSet.iUnion fun p ↦ (hC p).isClosed.measurableSet
  obtain ⟨B, hB, hBT⟩ := isSigmaCompact_iUnion_of_isCompact _ hC
  let : SigmaFinite (η.restrict T) := by
    refine ⟨⟨⟨fun n ↦ B n ∪ Tᶜ, fun _ ↦ trivial, fun n ↦ ?_, ?_⟩⟩⟩
    · rw [Measure.restrict_apply ((hB n).isClosed.measurableSet.union hTm.compl),
        union_inter_distrib_right, compl_inter_self, union_empty]
      exact (measure_mono inter_subset_left).trans_lt (hB n).measure_lt_top
    · rw [← iUnion_union, hBT]
      exact union_compl_self T
  have hzero (a b : H) (ha : a ∉ T) (hb : b ∈ ⋃ n, L n) : w (a * b) = 0 := by
    by_contra hne
    obtain ⟨n, hn⟩ := mem_iUnion.mp (hW hne)
    obtain ⟨m, hm⟩ := mem_iUnion.mp hb
    exact ha (mem_iUnion.mpr ⟨(n, m), a * b, hn, b⁻¹, by simpa, mul_inv_cancel_right a b⟩)
  let k (p : H × H) : ℝ≥0∞ := ((w (p.1 * p.2) * v p.2 : ℝ≥0) : ℝ≥0∞)
  have hk : Continuous k := ENNReal.continuous_coe.comp
    ((hw.comp (continuous_fst.mul continuous_snd)).mul (hv.comp continuous_snd))
  let q := (T ×ˢ (⋃ n, L n)).indicator k
  have hq : Measurable q :=
    measurable_indicator_prod_of_isSigmaCompact hk ⟨B, hB, hBT⟩ ⟨L, hL, rfl⟩
  have hrow (a : H) (ha : a ∈ T) :
      (∫⁻ b, q (a, b) ∂τ) = ∫⁻ b, (w (a * b) : ℝ≥0∞) * (v b : ℝ≥0∞) ∂τ := by
    apply lintegral_congr_ae
    filter_upwards [hτ] with b hb
    simpa only [q, k, ENNReal.coe_mul] using
      (indicator_of_mem (s := T ×ˢ (⋃ n, L n)) (a := (a, b)) ⟨ha, hb⟩ k)
  have hcol (b : H) (hb : b ∈ ⋃ n, L n) :
      (∫⁻ a in T, q (a, b) ∂η) = ∫⁻ a, (w (a * b) : ℝ≥0∞) * (v b : ℝ≥0∞) ∂η := by
    rw [← setLIntegral_eq_of_support_subset (s := T)
      (f := fun a ↦ (w (a * b) : ℝ≥0∞) * (v b : ℝ≥0∞)) (fun a ha ↦ by
        by_contra h
        exact ha (by simp [hzero a b h hb]))]
    apply setLIntegral_congr_fun hTm
    intro a ha
    simpa only [q, k, ENNReal.coe_mul] using
      (indicator_of_mem (s := T ×ˢ (⋃ n, L n)) (a := (a, b)) ⟨ha, hb⟩ k)
  calc
    _ = ∫⁻ a in T, ∫⁻ b, (w (a * b) : ℝ≥0∞) * (v b : ℝ≥0∞) ∂τ ∂η := by
      symm
      apply setLIntegral_eq_of_support_subset
      intro a ha
      by_contra h
      exact ha ((lintegral_congr_ae (hτ.mono fun b hb ↦ by simp [hzero a b h hb])).trans
        (lintegral_zero))
    _ = ∫⁻ a in T, ∫⁻ b, q (a, b) ∂τ ∂η :=
      setLIntegral_congr_fun hTm fun a ha ↦ (hrow a ha).symm
    _ = ∫⁻ b, ∫⁻ a in T, q (a, b) ∂η ∂τ :=
      lintegral_lintegral_swap hq.aemeasurable
    _ = ∫⁻ b, ∫⁻ a, (w (a * b) : ℝ≥0∞) * (v b : ℝ≥0∞) ∂η ∂τ :=
      lintegral_congr_ae (hτ.mono hcol)
    _ = _ := by
      have hm : Measurable (fun a : H ↦ (w a : ℝ≥0∞)) :=
        (ENNReal.continuous_coe.comp hw).measurable
      have hinner (b : H) : (∫⁻ a, (w (a * b) : ℝ≥0∞) * (v b : ℝ≥0∞) ∂η) =
          (∫⁻ a, (w a : ℝ≥0∞) ∂η) * (v b : ℝ≥0∞) := by
        have hmb : Measurable (fun a : H ↦ (w (a * b) : ℝ≥0∞)) :=
          hm.comp (continuous_id.mul continuous_const).measurable
        rw [lintegral_mul_const _ hmb]
        rw [lintegral_mul_right_eq_self (fun a ↦ (w a : ℝ≥0∞)) b]
      simp_rw [hinner]
      exact lintegral_const_mul _ (ENNReal.continuous_coe.comp hv).measurable


section CompactSupportApproximation

open Filter MeasureTheory Set Topology TopologicalSpace
open scoped ENNReal


/-- Approximate the indicator of a finite-measure set by a continuous cutoff with compact
support. The error is bounded by a constant on a measurable set of arbitrarily small mass. -/
private theorem exists_continuous_indicator_error_bound
    {X E : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [MeasurableSpace X] [BorelSpace X] {ν : Measure X} [ν.Regular]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (c : E) {s : Set X}
    (hs : MeasurableSet s) (hsfin : ν s < ∞) {η : ℝ≥0∞} (hη : η ≠ 0) :
    ∃ (v : X → E) (t : Set X), Continuous v ∧ HasCompactSupport v ∧ AEStronglyMeasurable v ν ∧
      MeasurableSet t ∧ ν t ≤ η ∧ ∀ x, ‖(s.indicator (fun _ ↦ c) - v) x‖ ≤
        ‖t.indicator (fun _ ↦ ‖c‖ + ‖c‖) x‖ := by
  have he := (ENNReal.half_pos hη).ne'
  obtain ⟨K, hKs, hK, hsmallK⟩ := hs.exists_isCompact_sdiff_lt hsfin.ne he
  obtain ⟨V, hsV, hV, -, hsmallV⟩ := hs.exists_isOpen_sdiff_lt hsfin.ne he
  obtain ⟨b, hbK, hbV, hbc, hbr⟩ := exists_continuous_one_zero_of_isCompact hK
    hV.isClosed_compl (disjoint_compl_right_iff_subset.mpr (hKs.trans hsV))
  let v (x : X) := b x • c
  refine ⟨v, V \ K, b.continuous.smul continuous_const, hbc.smul_right (f' := fun _ ↦ c),
    b.continuous.aestronglyMeasurable.smul aestronglyMeasurable_const,
    hV.measurableSet.diff hK.isClosed.measurableSet, ?_, ?_⟩
  · calc
      _ ≤ ν ((V \ s) ∪ (s \ K)) := measure_mono (by grind)
      _ ≤ ν (V \ s) + ν (s \ K) := measure_union_le _ _
      _ ≤ η := (add_le_add hsmallV.le hsmallK.le).trans_eq (ENNReal.add_halves _)
  · intro x
    by_cases hx : x ∈ K
    · simp [v, hx, hKs hx, hbK hx]
    by_cases hxV : x ∈ V
    · rw [indicator_of_mem (show x ∈ V \ K from ⟨hxV, hx⟩)]
      refine (norm_sub_le _ _).trans ?_
      rw [Real.norm_of_nonneg (by positivity)]
      exact add_le_add (by simp [indicator]; split <;> simp) (by
        simpa [v, norm_smul, abs_of_nonneg (hbr x).1] using
          mul_le_mul_of_nonneg_right (hbr x).2 (norm_nonneg c))
    · have hxs : x ∉ s := fun h ↦ hxV (hsV h)
      simp [v, hxV, hxs, hbV hxV]

section Approximation

variable {X E : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [MeasurableSpace X] [BorelSpace X] {ν : Measure X} [ν.Regular]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [SecondCountableTopology E]

/-- Compactly supported continuous functions approximate a function simultaneously in
`Lᵖ` and `Lᑫ` for finite exponents at least one. -/
private theorem exists_hasCompactSupport_eLpNorm_sub_le_two
    {p q : ℝ≥0∞} (hp : 1 ≤ p) (hq : 1 ≤ q) (hp' : p ≠ ∞) (hq' : q ≠ ∞)
    {u : X → E} (hup : MemLp u p ν) (huq : MemLp u q ν) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ v : X → E, Continuous v ∧ HasCompactSupport v ∧
      eLpNorm (u - v) p ν ≤ ε ∧ eLpNorm (u - v) q ν ≤ ε := by
  classical
  borelize E
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  have he := (ENNReal.half_pos hε).ne'
  have approxSimple (f : SimpleFunc X E) (hf : MemLp f p ν) :
      ∀ δ : ℝ≥0∞, δ ≠ 0 → ∃ v : X → E, Continuous v ∧ HasCompactSupport v ∧
        eLpNorm (⇑f - v) p ν ≤ δ ∧ eLpNorm (⇑f - v) q ν ≤ δ := by
    induction f using SimpleFunc.induction with
    | const c hs =>
      intro δ hδ
      rename_i s
      have hcoe : (⇑(SimpleFunc.piecewise s hs (SimpleFunc.const X c)
          (SimpleFunc.const X 0)) : X → E) = s.indicator (fun _ ↦ c) := by
        rw [SimpleFunc.coe_piecewise, SimpleFunc.coe_const, SimpleFunc.coe_const]
        rfl
      rw [hcoe]
      by_cases hc : c = 0
      · subst c
        exact ⟨0, continuous_const, HasCompactSupport.zero, by simp, by simp⟩
      have hsfin := SimpleFunc.measure_lt_top_of_memLp_indicator hp0 hp' hc hs hf
      obtain ⟨ηp, hηp, hboundp⟩ := exists_eLpNorm_indicator_le (μ := ν) hp' (‖c‖ + ‖c‖) hδ
      obtain ⟨ηq, hηq, hboundq⟩ := exists_eLpNorm_indicator_le (μ := ν) hq' (‖c‖ + ‖c‖) hδ
      obtain ⟨v, t, hv, hvK, hvm, ht, hνt, hbound⟩ :=
        exists_continuous_indicator_error_bound c hs hsfin
          (ENNReal.coe_ne_zero.mpr (lt_min hηp hηq).ne')
      exact ⟨v, hv, hvK,
        (eLpNorm_mono hbound).trans (hboundp t (hνt.trans (by exact_mod_cast min_le_left ..))),
        (eLpNorm_mono hbound).trans (hboundq t (hνt.trans (by exact_mod_cast min_le_right ..)))⟩
    | add hdisj ihf ihg =>
      rename_i f g
      intro δ hδ
      rw [SimpleFunc.coe_add, memLp_add_of_disjoint hdisj f.stronglyMeasurable g.stronglyMeasurable] at hf
      obtain ⟨v, hv, hvK, hvp, hvq⟩ := ihf hf.1 (δ / 2) (ENNReal.half_pos hδ).ne'
      obtain ⟨w, hw, hwK, hwp, hwq⟩ := ihg hf.2 (δ / 2) (ENNReal.half_pos hδ).ne'
      have hm₁ := f.aestronglyMeasurable.sub (μ := ν) hv.aestronglyMeasurable
      have hm₂ := g.aestronglyMeasurable.sub (μ := ν) hw.aestronglyMeasurable
      refine ⟨v + w, hv.add hw, hvK.add hwK, ?_, ?_⟩ <;>
        rw [SimpleFunc.coe_add, add_sub_add_comm]
      · exact (eLpNorm_add_le hm₁ hm₂ hp).trans ((add_le_add hvp hwp).trans_eq (ENNReal.add_halves _))
      · exact (eLpNorm_add_le hm₁ hm₂ hq).trans ((add_le_add hvq hwq).trans_eq (ENNReal.add_halves _))
  -- The same sequence of simple functions converges in both norms.
  let u' := hup.aestronglyMeasurable.mk u
  have hueq : u =ᵐ[ν] u' := hup.aestronglyMeasurable.ae_eq_mk
  have hum := hup.aestronglyMeasurable.measurable_mk
  let : SeparableSpace (range u' ∪ {0} : Set E) :=
    StronglyMeasurable.separableSpace_range_union_singleton hup.aestronglyMeasurable.stronglyMeasurable_mk
  let a n := SimpleFunc.approxOn u' hum (range u' ∪ {0}) 0 (by simp) n
  have hlim {r : ℝ≥0∞} (hr : r ≠ ∞) (hu : MemLp u r ν) :
      Tendsto (fun n ↦ eLpNorm (⇑(a n) - u') r ν) atTop (𝓝 0) :=
    SimpleFunc.tendsto_approxOn_range_Lp_eLpNorm hr hum (hu.ae_eq hueq).eLpNorm_lt_top
  obtain ⟨n, hpδ, hqδ⟩ := (((hlim hp' hup).eventually (gt_mem_nhds he.bot_lt)).and
    ((hlim hq' huq).eventually (gt_mem_nhds he.bot_lt))).exists
  obtain ⟨v, hv, hvK, hvp, hvq⟩ := approxSimple (a n)
    (SimpleFunc.memLp_approxOn_range hum (hup.ae_eq hueq) n) (ε / 2) he
  have heq : (u - v) =ᵐ[ν] (u' - v) := hueq.sub EventuallyEq.rfl
  have hm₁ : AEStronglyMeasurable (u' - ⇑(a n)) ν :=
    (hup.aestronglyMeasurable.congr hueq).sub (a n).aestronglyMeasurable
  have hm₂ : AEStronglyMeasurable (⇑(a n) - v) ν :=
    (a n).aestronglyMeasurable.sub hv.aestronglyMeasurable
  refine ⟨v, hv, hvK, ?_, ?_⟩ <;>
    rw [eLpNorm_congr_ae heq, show u' - v = u' - ⇑(a n) + (⇑(a n) - v) by abel]
  · exact (eLpNorm_add_le hm₁ hm₂ hp).trans
      ((add_le_add ((eLpNorm_sub_comm _ _ _ _).le.trans hpδ.le) hvp).trans_eq (ENNReal.add_halves _))
  · exact (eLpNorm_add_le hm₁ hm₂ hq).trans
      ((add_le_add ((eLpNorm_sub_comm _ _ _ _).le.trans hqδ.le) hvq).trans_eq (ENNReal.add_halves _))

end Approximation
end CompactSupportApproximation

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [MeasurableSpace (PontryaginDual G)] [BorelSpace (PontryaginDual G)]
  (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]

private theorem continuous_pontryaginDual_evaluation (x : G) :
    Continuous (fun χ : PontryaginDual G ↦ χ x) :=
  (continuous_eval_const (F := C(G, Circle)) x).comp
    (ContinuousMonoidHom.isInducing_toContinuousMap G Circle).continuous

/-- A Fourier norm identity for compactly supported continuous functions extends to
integrable square-integrable functions by approximation in both norms. -/
private theorem isLCAPlancherelMeasure_of_compactSupport
    (ν : Measure (PontryaginDual G)) [ν.IsHaarMeasure] [ν.Regular]
    (h : ∀ (f : G → ℂ), Continuous f → HasCompactSupport f →
      eLpNorm (lcaFourier μ f) 2 ν = eLpNorm f 2 μ) :
    IsLCAPlancherelMeasure μ ν := by
  have hp : 1 ≤ (2 : ℝ≥0∞) := by norm_num
  have hsub {f g : G → ℂ} (hf : Integrable f μ) (hg : Integrable g μ) :
      lcaFourier μ (f - g) = lcaFourier μ f - lcaFourier μ g := by
    funext χ
    simp only [lcaFourier, Pi.sub_apply, sub_mul]
    exact integral_sub (integrable_fourierIntegrand μ hf χ) (integrable_fourierIntegrand μ hg χ)
  have hApprox (f : G → ℂ) (hf₁ : Integrable f μ) (hf₂ : MemLp f 2 μ) :
      ∃ (g : ℕ → G → ℂ), (∀ n, Continuous (g n) ∧ HasCompactSupport (g n)) ∧
        Tendsto (fun n ↦ eLpNorm (g n - f) 2 μ) atTop (𝓝 0) ∧
        ∀ χ, Tendsto (fun n ↦ lcaFourier μ (g n) χ) atTop (𝓝 (lcaFourier μ f χ)) := by
    let ε (n : ℕ) : ℝ≥0∞ := ((n : ℝ≥0∞) + 1)⁻¹
    have hε : Tendsto ε atTop (𝓝 0) := by
      simpa only [ε, Function.comp_def, Nat.cast_add, Nat.cast_one] using
        ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)
    choose g hgC hgK hg₁ hg₂ using fun n : ℕ ↦
      exists_hasCompactSupport_eLpNorm_sub_le_two le_rfl hp ENNReal.one_ne_top
        (by simp) (memLp_one_iff_integrable.mpr hf₁) hf₂ (ε := ε n) (by simp [ε])
    have hlim (p : ℝ≥0∞) (hg : ∀ n, eLpNorm (f - g n) p μ ≤ ε n) :
        Tendsto (fun n ↦ eLpNorm (g n - f) p μ) atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hε (fun _ ↦ bot_le)
        (fun n ↦ (eLpNorm_sub_comm _ _ _ _).le.trans (hg n))
    refine ⟨g, fun n ↦ ⟨hgC n, hgK n⟩, hlim 2 hg₂, fun χ ↦ ?_⟩
    have hmem (n : ℕ) := ((hgC n).integrable_of_hasCompactSupport (μ := μ) (hgK n)).sub hf₁
    refine tendsto_iff_norm_sub_tendsto_zero.mpr ?_
    have hlim' := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (hlim 1 hg₁)
    simp only [ENNReal.toReal_zero, Function.comp_def] at hlim'
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim'
      (fun _ ↦ norm_nonneg _) (fun n ↦ ?_)
    have hEq : (eLpNorm (g n - f) 1 μ).toReal = ∫ x, ‖(g n - f) x‖ ∂μ := by
      rw [eLpNorm_one_eq_lintegral_enorm,
        ← ofReal_integral_norm_eq_lintegral_enorm (hmem n),
        ENNReal.toReal_ofReal (integral_nonneg fun _ ↦ norm_nonneg _)]
    rw [hEq, ← Pi.sub_apply, ← hsub
      ((hgC n).integrable_of_hasCompactSupport (hgK n)) hf₁]
    exact norm_lcaFourier_le_integral_norm μ _ χ
  -- Pointwise convergence of the transforms and Fatou give the bound for arbitrary inputs.
  have hupper (f : G → ℂ) (hf₁ : Integrable f μ) (hf₂ : MemLp f 2 μ) :
      eLpNorm (lcaFourier μ f) 2 ν ≤ eLpNorm f 2 μ := by
    obtain ⟨g, hg, hlim₂, hlimF⟩ := hApprox f hf₁ hf₂
    have hg₁ (n : ℕ) : Integrable (g n) μ :=
      (hg n).1.integrable_of_hasCompactSupport (hg n).2
    have hg₂ (n : ℕ) : MemLp (g n) 2 μ := (hg n).1.memLp_of_hasCompactSupport (hg n).2
    have hnorm : Tendsto (fun n ↦ eLpNorm (g n) 2 μ) atTop (𝓝 (eLpNorm f 2 μ)) := by
      have ht := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' g hg₂ f hf₂).mpr hlim₂
      simpa only [Function.comp_def, Lp.enorm_toLp] using (continuous_enorm.tendsto _).comp ht
    calc
      eLpNorm (lcaFourier μ f) 2 ν ≤ liminf (fun n ↦ eLpNorm (lcaFourier μ (g n)) 2 ν) atTop :=
        Lp.eLpNorm_lim_le_liminf_eLpNorm
          (fun n ↦ (continuous_lcaFourier μ (hg₁ n)).aestronglyMeasurable)
          _ (.of_forall hlimF)
      _ = eLpNorm f 2 μ := by
        simp_rw [h _ (hg _).1 (hg _).2]
        exact hnorm.liminf_eq
  refine ⟨inferInstance, inferInstance, fun f hf₁ hf₂ ↦ ?_⟩
  have hfF : MemLp (lcaFourier μ f) 2 ν :=
    ⟨(continuous_lcaFourier μ hf₁).aestronglyMeasurable,
      (hupper f hf₁ hf₂).trans_lt hf₂.eLpNorm_lt_top⟩
  obtain ⟨g, hg, hlim₂, -⟩ := hApprox f hf₁ hf₂
  have hg₁ (n : ℕ) : Integrable (g n) μ :=
    (hg n).1.integrable_of_hasCompactSupport (hg n).2
  have hg₂ (n : ℕ) : MemLp (g n) 2 μ := (hg n).1.memLp_of_hasCompactSupport (hg n).2
  have hgF (n : ℕ) : MemLp (lcaFourier μ (g n)) 2 ν :=
    ⟨(continuous_lcaFourier μ (hg₁ n)).aestronglyMeasurable,
      (h (g n) (hg n).1 (hg n).2).trans_lt (hg₂ n).eLpNorm_lt_top⟩
  -- The bound applied to differences gives convergence of the transformed sequence in L².
  have hlimF : Tendsto (fun n ↦ eLpNorm (lcaFourier μ (g n) - lcaFourier μ f) 2 ν)
      atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim₂
      (fun _ ↦ bot_le) (fun n ↦ ?_)
    rw [← hsub (hg₁ n) hf₁]
    exact hupper _ ((hg₁ n).sub hf₁) ((hg₂ n).sub hf₂)
  have ht := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' g hg₂ f hf₂).mpr hlim₂
  have htF := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ hgF _ hfF).mpr hlimF
  refine ⟨hfF, tendsto_nhds_unique (l := atTop)
    (f := fun n ↦ eLpNorm (lcaFourier μ (g n)) 2 ν) ?_ ?_⟩
  · simpa only [Function.comp_def, Lp.enorm_toLp] using (continuous_enorm.tendsto _).comp htF
  · simp_rw [h _ (hg _).1 (hg _).2]
    simpa only [Function.comp_def, Lp.enorm_toLp] using (continuous_enorm.tendsto _).comp ht

open scoped CompactlySupported in
/-- The autocorrelation of a continuous compactly supported function is the
Fourier–Stieltjes transform of a finite regular positive measure on the dual.
This is the autocorrelation case of Bochner's theorem. -/
theorem exists_lcaAutocorrelation_measure (f : C_c(G, ℂ)) :
    ∃ ρ : Measure (PontryaginDual G), IsFiniteMeasure ρ ∧ ρ.Regular ∧
      ∀ x : G, (∫ χ, (χ x : ℂ) ∂ρ) =
        lcaConvolution μ f (fun y ↦ star (f y⁻¹)) x := by
  obtain ⟨ρ, hFinite, hRegular, hρ⟩ := exists_haar_autocorrelation_measure μ (f := (f : G → ℂ))
    (f.continuous.memLp_of_hasCompactSupport (p := 2) f.hasCompactSupport)
  exact ⟨ρ, hFinite, hRegular, fun x ↦ by
    simpa only [lcaConvolution, mul_inv_rev, inv_inv] using hρ x⟩

open scoped CompactlySupported Pointwise in
/-- The autocorrelation has compact support, and its Fourier integral is the
squared modulus of the Fourier integral of the original function. -/
private theorem lcaFourier_autocorrelation (f : C_c(G, ℂ)) :
    HasCompactSupport (lcaConvolution μ f (fun y ↦ star (f y⁻¹))) ∧
    ∀ χ, lcaFourier μ (lcaConvolution μ f (fun y ↦ star (f y⁻¹))) χ =
      (‖lcaFourier μ f χ‖ ^ 2 : ℝ) := by
  let K := tsupport f
  have hK : IsCompact K := f.hasCompactSupport
  have hout (x y : G) (hx : x ∉ K * K⁻¹) : f y * star (f (x⁻¹ * y)) = 0 := by
    by_contra h
    have hy : y ∈ K := subset_tsupport f fun hy ↦ h (by simp [hy])
    have hz : x⁻¹ * y ∈ K := subset_tsupport f fun hz ↦ h (by simp [hz])
    apply hx
    refine ⟨y, hy, (x⁻¹ * y)⁻¹, by simpa, ?_⟩
    simp [mul_inv_rev]
  constructor
  · refine HasCompactSupport.intro (hK.mul hK.inv) fun x hx ↦ ?_
    simp only [lcaConvolution, mul_inv_rev, inv_inv, hout x _ hx, integral_zero]
  intro χ
  let k (x y : G) := f y * star (f (x⁻¹ * y)) * star (χ x : ℂ)
  have hk : Continuous (Function.uncurry k) :=
    ((f.continuous.comp continuous_snd).mul
      (f.continuous.comp (continuous_fst.inv.mul continuous_snd)).star).mul
      ((continuous_subtype_val.comp χ.continuous).comp continuous_fst).star
  have hkK : HasCompactSupport (Function.uncurry k) := by
    refine HasCompactSupport.intro ((hK.mul hK.inv).prod hK) ?_
    rintro ⟨x, y⟩ h
    change f y * star (f (x⁻¹ * y)) * star (χ x : ℂ) = 0
    by_cases hx : x ∈ K * K⁻¹
    · rw [image_eq_zero_of_notMem_tsupport (fun hy ↦ h ⟨hx, hy⟩), zero_mul, zero_mul]
    · rw [hout x y hx, zero_mul]
  have hrow (x : G) : lcaConvolution μ f (fun y ↦ star (f y⁻¹)) x *
      star (χ x : ℂ) = ∫ y, k x y ∂μ := by
    simp only [k, lcaConvolution, mul_inv_rev, inv_inv, integral_mul_const]
  have hcol (y : G) : (∫ x, k x y ∂μ) =
      f y * star (χ y : ℂ) * star (lcaFourier μ f χ) := by
    calc
      _ = ∫ z, k (y * z⁻¹) y ∂μ := by
        rw [integral_inv_eq_self (fun z ↦ k (y * z) y) μ,
          integral_mul_left_eq_self (fun z ↦ k z y) y]
      _ = ∫ z, (f y * star (χ y : ℂ)) * star (f z * star (χ z : ℂ)) ∂μ := by
        apply integral_congr_ae
        exact .of_forall fun z ↦ by
          have hχ : (χ (y * z⁻¹) : ℂ) = (χ y : ℂ) * star (χ z : ℂ) := by
            simp only [map_mul, Circle.coe_mul, map_inv, Circle.coe_inv_eq_conj, Complex.star_def]
          simp only [k, hχ, mul_inv_rev, inv_inv, inv_mul_cancel_right, star_mul, star_star]
          ring
      _ = _ := (integral_const_mul _ _).trans
        (congrArg (fun z : ℂ ↦ (f y * star (χ y : ℂ)) * z)
          (integral_conj (f := fun z ↦ f z * star (χ z : ℂ))))
  calc
    _ = ∫ x, ∫ y, k x y ∂μ ∂μ := by simp only [lcaFourier, hrow]
    _ = ∫ y, ∫ x, k x y ∂μ ∂μ := integral_integral_swap_of_hasCompactSupport hk hkK
    _ = _ := by
      simp only [hcol, integral_mul_const]
      change lcaFourier μ f χ * star (lcaFourier μ f χ) = _
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- A Fourier density under a finite regular spectral measure corresponds to
convolution with the Fourier–Stieltjes transform of that measure. -/
private theorem integral_lcaFourier_mul_char
    (τ : Measure (PontryaginDual G)) [IsFiniteMeasure τ] [τ.Regular]
    {u : G → ℂ} (hu : Continuous u) (huK : HasCompactSupport u) (x : G) :
    (∫ χ, lcaFourier μ u χ * (χ x : ℂ) ∂τ) =
      lcaConvolution μ u (fun z ↦ ∫ χ, (χ z : ℂ) ∂τ) x := by
  obtain ⟨S, hS, hτ⟩ := exists_isSigmaCompact_ae_mem τ
  let K := tsupport u
  have hK : IsCompact K := huK
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  let : Fact (μ K < ⊤) := ⟨hK.measure_lt_top⟩
  let k (p : G × PontryaginDual G) := u p.1 * (p.2 (p.1⁻¹ * x) : ℂ)
  have he : Continuous (fun p : G × PontryaginDual G ↦ p.2 (p.1⁻¹ * x)) :=
    (continuous_eval (F := C(G, Circle))).comp
      (((ContinuousMonoidHom.isInducing_toContinuousMap G Circle).continuous.comp
        continuous_snd).prodMk (continuous_fst.inv.mul continuous_const))
  have hk : Continuous k := (hu.comp continuous_fst).mul (continuous_subtype_val.comp he)
  let q := (K ×ˢ S).indicator k
  have hq : Measurable q := measurable_indicator_prod_of_isSigmaCompact hk hK.isSigmaCompact hS
  obtain ⟨C, hC⟩ : ∃ C, ∀ y, ‖u y‖ ≤ C := hu.bounded_above_of_compact_support huK
  have hInt : Integrable q ((μ.restrict K).prod τ) := by
    apply Integrable.of_bound hq.aestronglyMeasurable C
    exact .of_forall fun p ↦ by
      by_cases hp : p ∈ K ×ˢ S
      · simpa [q, hp, k, norm_mul, Circle.norm_coe] using hC p.1
      · simpa [q, hp] using (norm_nonneg (u p.1)).trans (hC p.1)
  have hrow : ∀ᵐ y ∂μ.restrict K, (∫ χ, q (y, χ) ∂τ) =
      u y * ∫ χ, (χ (y⁻¹ * x) : ℂ) ∂τ := by
    filter_upwards [ae_restrict_mem hKm] with y hy
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [hτ] with χ hχ
    exact indicator_of_mem (s := K ×ˢ S) (a := (y, χ)) ⟨hy, hχ⟩ k
  have hcol : ∀ᵐ χ ∂τ, (∫ y in K, q (y, χ) ∂μ) = lcaFourier μ u χ * (χ x : ℂ) := by
    filter_upwards [hτ] with χ hχ
    let r (y : G) := u y * star (χ y : ℂ) * (χ x : ℂ)
    calc
      _ = ∫ y in K, r y ∂μ := by
        refine setIntegral_congr_fun hKm fun y hy ↦ ?_
        rw [show q (y, χ) = k (y, χ) from
          indicator_of_mem (s := K ×ˢ S) (a := (y, χ)) ⟨hy, hχ⟩ k]
        simp only [k, r, map_mul, Circle.coe_mul, map_inv, Circle.coe_inv_eq_conj,
          Complex.star_def, mul_assoc]
      _ = ∫ y, r y ∂μ := setIntegral_eq_integral_of_forall_compl_eq_zero <| fun y hy ↦ by
        have hz : u y = 0 := image_eq_zero_of_notMem_tsupport hy
        simp only [r, hz, zero_mul]
      _ = _ := integral_mul_const _ _
  calc
    _ = ∫ χ, ∫ y in K, q (y, χ) ∂μ ∂τ := integral_congr_ae (hcol.mono fun _ h ↦ h.symm)
    _ = ∫ y in K, ∫ χ, q (y, χ) ∂τ ∂μ :=
      (integral_integral_swap (f := fun y χ ↦ q (y, χ)) hInt).symm
    _ = _ := (integral_congr_ae hrow).trans
      (setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun y hy ↦ by simp [image_eq_zero_of_notMem_tsupport hy]))

/-- A finite regular measure on the dual is determined by its integrals against
the evaluation characters. -/
private theorem lcaSpectral_measure_ext
    (τ₁ τ₂ : Measure (PontryaginDual G)) [IsFiniteMeasure τ₁] [τ₁.Regular]
    [IsFiniteMeasure τ₂] [τ₂.Regular]
    (h : ∀ x : G, (∫ χ, (χ x : ℂ) ∂τ₁) = ∫ χ, (χ x : ℂ) ∂τ₂) : τ₁ = τ₂ := by
  let τ := τ₁ + τ₂
  let h₁ : τ₁ ≪ τ := Measure.AbsolutelyContinuous.rfl.add_right _
  let h₂ : τ₂ ≪ τ := Measure.AbsolutelyContinuous.rfl.add_right' _
  let : τ.InnerRegular := inferInstanceAs (τ₁ + τ₂).InnerRegular
  let : τ.Regular := inferInstance
  let d₁ (χ : PontryaginDual G) : ℂ := (τ₁.rnDeriv τ χ).toReal
  let d₂ (χ : PontryaginDual G) : ℂ := (τ₂.rnDeriv τ χ).toReal
  have hInt₁ : Integrable d₁ τ := by
    simpa only [d₁, Complex.real_smul, mul_one] using
      (integrable_rnDeriv_smul_iff (f := fun _ ↦ (1 : ℂ)) h₁).2 (integrable_const _)
  have hInt₂ : Integrable d₂ τ := by
    simpa only [d₂, Complex.real_smul, mul_one] using
      (integrable_rnDeriv_smul_iff (f := fun _ ↦ (1 : ℂ)) h₂).2 (integrable_const _)
  have hc (x : G) : Continuous (fun χ : PontryaginDual G ↦ (χ x : ℂ)) :=
    continuous_subtype_val.comp (continuous_pontryaginDual_evaluation x)
  have hEq : (d₁ - d₂) =ᵐ[τ] 0 := by
    refine ae_eq_zero_of_integral_mul_circle_eq_zero
      (fun χ : PontryaginDual G ↦ χ.toMonoidHom)
      (fun x ↦ continuous_pontryaginDual_evaluation x)
      (fun χ ψ heq ↦ PontryaginDual.ext fun x ↦ congrArg (fun e : G →* Circle ↦ e x) heq)
      (hInt₁.sub hInt₂) fun x ↦ ?_
    change (∫ χ, (d₁ χ - d₂ χ) * (χ x : ℂ) ∂τ) = 0
    simp only [sub_mul]
    rw [integral_sub
      (hInt₁.mul_bdd (hc x).aestronglyMeasurable (.of_forall fun χ ↦ (Circle.norm_coe _).le))
      (hInt₂.mul_bdd (hc x).aestronglyMeasurable (.of_forall fun χ ↦ (Circle.norm_coe _).le))]
    simp only [d₁, d₂, ← Complex.real_smul, integral_rnDeriv_smul, h₁, h₂, h,
      sub_self]
  rw [← Measure.withDensity_rnDeriv_eq τ₁ τ h₁, ← Measure.withDensity_rnDeriv_eq τ₂ τ h₂]
  apply withDensity_congr_ae
  filter_upwards [hEq, Measure.rnDeriv_lt_top τ₁ τ, Measure.rnDeriv_lt_top τ₂ τ] with χ he ht₁ ht₂
  have hr := Complex.ofReal_injective (sub_eq_zero.mp he)
  rw [← ENNReal.ofReal_toReal ht₁.ne, ← ENNReal.ofReal_toReal ht₂.ne, hr]

open scoped CompactlySupported in
/-- The translate of one spectral measure and the other spectral measure agree after
weighting each by the squared Fourier magnitude of the other function. -/
private theorem lcaAutocorrelation_weighted_translate
    (f g : C_c(G, ℂ)) (ρ σ : Measure (PontryaginDual G))
    [IsFiniteMeasure ρ] [ρ.Regular] [IsFiniteMeasure σ] [σ.Regular]
    (hρ : ∀ x : G, (∫ χ, (χ x : ℂ) ∂ρ) =
      lcaConvolution μ f (fun y ↦ star (f y⁻¹)) x)
    (hσ : ∀ x : G, (∫ χ, (χ x : ℂ) ∂σ) =
      lcaConvolution μ g (fun y ↦ star (g y⁻¹)) x)
    (a : PontryaginDual G) :
    (ρ.map (a * ·)).withDensity (fun χ ↦ ‖lcaFourier μ g χ‖ₑ ^ 2) =
      σ.withDensity (fun χ ↦ ‖lcaFourier μ f (a⁻¹ * χ)‖ₑ ^ 2) := by
  let A (h : C_c(G, ℂ)) := lcaConvolution μ h (fun y ↦ star (h y⁻¹))
  have hAc (h : C_c(G, ℂ)) : Continuous (A h) := by
    apply continuous_lcaConvolution_L2 μ (h.continuous.memLp_of_hasCompactSupport h.hasCompactSupport)
    exact (h.continuous.comp continuous_inv).star.memLp_of_hasCompactSupport
      ((h.hasCompactSupport.comp_homeomorph (Homeomorph.inv G)).comp_left (star_zero ℂ))
  let u (x : G) := (a x : ℂ) * A f x
  have huc : Continuous u := (continuous_subtype_val.comp a.continuous).mul (hAc f)
  have huK : HasCompactSupport u := (lcaFourier_autocorrelation μ f).1.mul_left
  let e := Homeomorph.mulLeft a
  let τ := ρ.map e
  let : IsFiniteMeasure τ := ρ.isFiniteMeasure_map e
  let : τ.Regular := Measure.Regular.map e
  have hτ (x : G) : (∫ χ, (χ x : ℂ) ∂τ) = u x := by
    rw [show τ = Measure.map e.toMeasurableEquiv ρ from rfl,
      integral_map_equiv]
    change (∫ χ, ((a x * χ x : Circle) : ℂ) ∂ρ) = u x
    simp only [Circle.coe_mul, integral_const_mul, hρ, u, A]
  have hF (χ : PontryaginDual G) : lcaFourier μ u χ =
      (‖lcaFourier μ f (a⁻¹ * χ)‖ ^ 2 : ℝ) := by
    rw [← (lcaFourier_autocorrelation μ f).2 (a⁻¹ * χ)]
    apply integral_congr_ae
    exact .of_forall fun y ↦ by
      change (a y : ℂ) * A f y * star (χ y : ℂ) =
        A f y * star ((a⁻¹ * χ) y : ℂ)
      have hinv : ((a⁻¹ * χ) y : ℂ) = star (a y : ℂ) * (χ y : ℂ) := by
        change (((a y)⁻¹ * χ y : Circle) : ℂ) = _
        rw [Circle.coe_mul, Circle.coe_inv_eq_conj, Complex.star_def]
      rw [hinv, star_mul, star_star]
      ring
  let w (h : C_c(G, ℂ)) (χ : PontryaginDual G) : ℝ≥0 := ‖lcaFourier μ h χ‖₊ ^ 2
  have hw (h : C_c(G, ℂ)) : Continuous (w h) :=
    (continuous_lcaFourier μ h.integrable).nnnorm.pow 2
  have hw' : Continuous (fun χ ↦ w f (a⁻¹ * χ)) :=
    (hw f).comp (continuous_const.mul continuous_id)
  have hBound (h : C_c(G, ℂ)) (χ : PontryaginDual G) :
      (w h χ : ℝ≥0∞) ≤ ENNReal.ofReal ((∫ x, ‖h x‖ ∂μ) ^ 2) := by
    rw [← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal
      (pow_le_pow_left₀ (norm_nonneg _) (norm_lcaFourier_le_integral_norm μ h χ) 2)
  have hReg (v : Measure (PontryaginDual G)) [IsFiniteMeasure v] [v.Regular]
      (p : PontryaginDual G → ℝ≥0∞) (C : ℝ) (hp : ∀ χ, p χ ≤ ENNReal.ofReal C) :
      IsFiniteMeasure (v.withDensity p) ∧ (v.withDensity p).Regular := by
    let c := Real.toNNReal C
    let cv := c • v
    have hle : v.withDensity p ≤ cv := by
      change _ ≤ (ENNReal.ofReal C) • v
      rw [← withDensity_const]
      exact withDensity_mono (.of_forall hp)
    let : IsFiniteMeasure cv := inferInstanceAs (IsFiniteMeasure (c • v))
    let : cv.Regular := inferInstanceAs (c • v).Regular
    exact ⟨isFiniteMeasure_of_le cv hle, regular_of_le_finite_regular _ cv hle⟩
  obtain ⟨h₁fin, h₁reg⟩ := hReg τ (fun χ ↦ (w g χ : ℝ≥0∞)) _ (hBound g)
  obtain ⟨h₂fin, h₂reg⟩ := hReg σ (fun χ ↦ (w f (a⁻¹ * χ) : ℝ≥0∞)) _
    (fun χ ↦ hBound f (a⁻¹ * χ))
  let := h₁fin
  let := h₁reg
  let := h₂fin
  let := h₂reg
  suffices heq : τ.withDensity (fun χ ↦ (w g χ : ℝ≥0∞)) =
      σ.withDensity (fun χ ↦ (w f (a⁻¹ * χ) : ℝ≥0∞)) by
    have he : (e : PontryaginDual G → PontryaginDual G) = (a * ·) := rfl
    simpa only [τ, he, w, ENNReal.coe_pow, enorm_eq_nnnorm] using heq
  apply lcaSpectral_measure_ext
  intro x
  rw [integral_withDensity_eq_integral_smul (hw g).measurable,
    integral_withDensity_eq_integral_smul hw'.measurable]
  have hl (χ : PontryaginDual G) :
      w g χ • (χ x : ℂ) = lcaFourier μ (A g) χ * (χ x : ℂ) := by
    rw [(lcaFourier_autocorrelation μ g).2 χ]
    simp [w, NNReal.smul_def, Complex.real_smul]
  have hr (χ : PontryaginDual G) :
      w f (a⁻¹ * χ) • (χ x : ℂ) = lcaFourier μ u χ * (χ x : ℂ) := by
    rw [hF]
    simp [w, NNReal.smul_def, Complex.real_smul]
  simp_rw [hl, hr]
  rw [integral_lcaFourier_mul_char μ τ (hAc g) (lcaFourier_autocorrelation μ g).1,
    integral_lcaFourier_mul_char μ σ huc huK, funext hτ, funext hσ]
  let q (y : G) := A g y * u (y⁻¹ * x)
  have hcomm (y : G) : q (x * y⁻¹) = u y * A g (y⁻¹ * x) := by
    simp only [q, mul_inv_rev, inv_inv, inv_mul_cancel_right]
    rw [mul_comm x y⁻¹, mul_comm]
  change (∫ y, q y ∂μ) = ∫ y, u y * A g (y⁻¹ * x) ∂μ
  rw [← integral_mul_left_eq_self q x]
  calc
    (∫ y, q (x * y) ∂μ) = ∫ y, q (x * y⁻¹) ∂μ :=
      (integral_inv_eq_self (fun y ↦ q (x * y)) μ).symm
    _ = _ := integral_congr_ae (.of_forall hcomm)

open scoped CompactlySupported in
/-- Averaging the weighted spectral measures of two autocorrelations over dual
translations gives this identity on each measurable set. For a dual character `a`,
the spectral measure of `f` modulated by `a` is the translate of its spectral
measure by `a`. Weight that translate by the squared Fourier magnitude of `g`,
or weight the spectral measure of `g` by the shifted squared Fourier magnitude
of `f`. The two measures have the same Fourier–Stieltjes transform by
commutativity of convolution. Integrate the resulting identity over `a`
against the fixed Haar measure `η`. -/
theorem lcaAutocorrelation_measure_mul_lintegral
    (η : Measure (PontryaginDual G)) [η.IsHaarMeasure] [η.Regular]
    (f g : C_c(G, ℂ)) (ρ σ : Measure (PontryaginDual G))
    [IsFiniteMeasure ρ] [ρ.Regular] [IsFiniteMeasure σ] [σ.Regular]
    (hρ : ∀ x : G, (∫ χ, (χ x : ℂ) ∂ρ) =
      lcaConvolution μ f (fun y ↦ star (f y⁻¹)) x)
    (hσ : ∀ x : G, (∫ χ, (χ x : ℂ) ∂σ) =
      lcaConvolution μ g (fun y ↦ star (g y⁻¹)) x)
    {s : Set (PontryaginDual G)} (hs : MeasurableSet s) :
    (∫⁻ χ, ‖lcaFourier μ f χ‖ₑ ^ 2 ∂η) * σ s =
      ρ univ * (∫⁻ χ in s, ‖lcaFourier μ g χ‖ₑ ^ 2 ∂η) := by
  let w (h : C_c(G, ℂ)) (χ : PontryaginDual G) : ℝ≥0 := ‖lcaFourier μ h χ‖₊ ^ 2
  have hw (h : C_c(G, ℂ)) : Continuous (w h) :=
    (continuous_lcaFourier μ h.integrable).nnnorm.pow 2
  have hwMeas (h : C_c(G, ℂ)) : Measurable (fun χ ↦ (w h χ : ℝ≥0∞)) :=
    (ENNReal.continuous_coe.comp (hw h)).measurable
  have hCarrier (h : C_c(G, ℂ)) :
      ∃ S : Set (PontryaginDual G), IsSigmaCompact S ∧ Function.support (w h) ⊆ S := by
    obtain ⟨F, hF⟩ := lcaFourier_zeroAtInfty μ h.integrable
    have hlim : Tendsto (w h) (cocompact (PontryaginDual G)) (𝓝 0) := by
      simpa only [w, ← hF, nnnorm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)] using
        (zero_at_infty F).nnnorm.pow 2
    obtain ⟨ε, -, hε, hεlim⟩ := exists_seq_strictAnti_tendsto' (zero_lt_one : (0 : ℝ≥0) < 1)
    let K (n : ℕ) := {χ | ε n ≤ w h χ}
    have hK (n : ℕ) : IsCompact (K n) := by
      obtain ⟨L, hL, hLK⟩ := mem_cocompact.mp (hlim (Iio_mem_nhds (hε n).1))
      exact hL.of_isClosed_subset (isClosed_le continuous_const (hw h)) (by
        intro χ hχ
        by_contra hn
        exact (not_lt_of_ge (show ε n ≤ w h χ from hχ)) (show w h χ < ε n from hLK hn))
    refine ⟨⋃ n, K n, ⟨K, hK, rfl⟩, fun χ hχ ↦ ?_⟩
    have hh : ∀ᶠ n in atTop, ε n < w h χ :=
      hεlim (Iio_mem_nhds (pos_iff_ne_zero.mpr hχ))
    obtain ⟨n, hn⟩ := hh.exists
    exact mem_iUnion.mpr ⟨n, le_of_lt hn⟩
  obtain ⟨S, hS, hfS⟩ := hCarrier f
  obtain ⟨T, hT, hgT⟩ := hCarrier g
  let I := ∫⁻ χ, (w f χ : ℝ≥0∞) ∂η
  let ν₁ := I • σ
  let ν₂ := ρ univ • η.withDensity (fun χ ↦ (w g χ : ℝ≥0∞))
  -- Average the translated identity against each compactly supported continuous test.
  have hTests (p : C_c(PontryaginDual G, ℝ≥0)) :
      (∫⁻ χ, (p χ : ℝ≥0∞) ∂ν₁) = ∫⁻ χ, (p χ : ℝ≥0∞) ∂ν₂ := by
    let v (χ : PontryaginDual G) := w g χ * p χ
    have hv : Continuous v := (hw g).mul p.continuous
    have hvT : Function.support v ⊆ T := fun χ hχ ↦ hgT (mul_ne_zero_iff.mp hχ).1
    have hp : Measurable (fun χ ↦ (p χ : ℝ≥0∞)) :=
      (ENNReal.continuous_coe.comp p.continuous).measurable
    have hpoint (a : PontryaginDual G) :
        (∫⁻ χ, (w f (a⁻¹ * χ) : ℝ≥0∞) * (p χ : ℝ≥0∞) ∂σ) =
          ∫⁻ χ, (v (a * χ) : ℝ≥0∞) ∂ρ := by
      have h := congrArg (fun m : Measure (PontryaginDual G) ↦ ∫⁻ χ, (p χ : ℝ≥0∞) ∂m)
        (lcaAutocorrelation_weighted_translate μ f g ρ σ hρ hσ a).symm
      simp only [enorm_eq_nnnorm, ← ENNReal.coe_pow] at h
      change (∫⁻ χ, (p χ : ℝ≥0∞) ∂σ.withDensity (fun χ ↦ (w f (a⁻¹ * χ) : ℝ≥0∞))) =
        ∫⁻ χ, (p χ : ℝ≥0∞) ∂(ρ.map (a * ·)).withDensity (fun χ ↦ (w g χ : ℝ≥0∞)) at h
      have hshift : Measurable (fun χ ↦ (w f (a⁻¹ * χ) : ℝ≥0∞)) :=
        (hwMeas f).comp (continuous_const.mul continuous_id).measurable
      rw [lintegral_withDensity_eq_lintegral_mul _ hshift hp,
        lintegral_withDensity_eq_lintegral_mul _ (hwMeas g) hp] at h
      have hm : Measurable (fun χ ↦ (v χ : ℝ≥0∞)) :=
        (ENNReal.continuous_coe.comp hv).measurable
      calc
        _ = ∫⁻ χ, (v χ : ℝ≥0∞) ∂(ρ.map (a * ·)) := by
          simpa only [Pi.mul_apply, v, ENNReal.coe_mul] using h
        _ = _ := lintegral_map hm (continuous_const.mul continuous_id).measurable
    rw [lintegral_smul_measure, lintegral_smul_measure, smul_eq_mul, smul_eq_mul,
      lintegral_withDensity_eq_lintegral_mul _ (hwMeas g) hp]
    calc
      I * (∫⁻ χ, (p χ : ℝ≥0∞) ∂σ) =
          ∫⁻ a, ∫⁻ χ, (w f (a * χ) : ℝ≥0∞) * (p χ : ℝ≥0∞) ∂σ ∂η :=
        (lintegral_lintegral_mul_translate η σ (hw f) p.continuous hS hfS).symm
      _ = ∫⁻ a, ∫⁻ χ, (w f (a⁻¹ * χ) : ℝ≥0∞) * (p χ : ℝ≥0∞) ∂σ ∂η :=
        (lintegral_inv_eq_self (fun a ↦ ∫⁻ χ, (w f (a * χ) : ℝ≥0∞) *
          (p χ : ℝ≥0∞) ∂σ)).symm
      _ = ∫⁻ a, ∫⁻ χ, (v (a * χ) : ℝ≥0∞) ∂ρ ∂η := lintegral_congr hpoint
      _ = ρ univ * ∫⁻ χ, (w g χ : ℝ≥0∞) * (p χ : ℝ≥0∞) ∂η := by
        simpa only [ENNReal.coe_one, mul_one, lintegral_const, one_mul, v, ENNReal.coe_mul] using
          (lintegral_lintegral_mul_translate η ρ hv
            (v := fun _ ↦ (1 : ℝ≥0)) continuous_const hT hvT).trans (mul_comm _ _)
  let C := Real.toNNReal ((∫ x, ‖g x‖ ∂μ) ^ 2)
  have hBound (χ : PontryaginDual G) : (w g χ : ℝ≥0∞) ≤ C := by
    rw [← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal
      (pow_le_pow_left₀ (norm_nonneg _) (norm_lcaFourier_le_integral_norm μ g χ) 2)
  let ν := η.withDensity (fun χ ↦ (w g χ : ℝ≥0∞))
  have hνle : ν ≤ C • η := by
    change _ ≤ (C : ℝ≥0∞) • η
    rw [← withDensity_const]
    exact withDensity_mono (.of_forall hBound)
  let : IsFiniteMeasureOnCompacts ν := ⟨fun K hK ↦ (hνle K).trans_lt
    (hK.measure_lt_top (μ := C • η))⟩
  let : ν.InnerRegular := innerRegular_withDensity_of_le_of_isSigmaCompact η hBound hT
    (fun χ hχ ↦ hgT (by simpa using hχ))
  let : ν₂.InnerRegular := inferInstanceAs (ρ univ • ν).InnerRegular
  let : IsFiniteMeasureOnCompacts ν₂ := .smul ν (measure_ne_top ρ univ)
  let : σ.InnerRegular := inferInstance
  let : ν₁.InnerRegular := inferInstanceAs (I • σ).InnerRegular
  -- Local finiteness of the weighted Haar measure suffices to identify both measures.
  have hEq := congrArg (fun m : Measure (PontryaginDual G) ↦ m s)
    (measure_eq_of_lintegral_eq_on_compactlySupported_nnreal ν₁ ν₂ hTests)
  change (I • σ) s = (ρ univ • ν) s at hEq
  rw [Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul,
    show ν = η.withDensity (fun χ ↦ (w g χ : ℝ≥0∞)) from rfl,
    withDensity_apply _ hs] at hEq
  simpa only [I, w, ENNReal.coe_pow, enorm_eq_nnnorm] using hEq

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [μ.Regular] in
open scoped CompactlySupported in
/-- Evaluating the Fourier–Stieltjes representation at the identity identifies
the total mass with the integral of the squared source norm. -/
private theorem lcaAutocorrelation_measure_univ (f : C_c(G, ℂ))
    (ρ : Measure (PontryaginDual G)) [IsFiniteMeasure ρ]
    (hρ : ∀ x : G, (∫ χ, (χ x : ℂ) ∂ρ) =
      lcaConvolution μ f (fun y ↦ star (f y⁻¹)) x) :
    ρ univ = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ := by
  have hSqC : Continuous (fun x ↦ ‖f x‖ ^ 2) := f.continuous.norm.pow 2
  have hSqK : HasCompactSupport (fun x ↦ ‖f x‖ ^ 2) :=
    f.hasCompactSupport.norm.comp_left (g := fun t : ℝ ↦ t ^ 2) (by simp)
  have hAuto : lcaConvolution μ f (fun y ↦ star (f y⁻¹)) 1 =
      ((∫ x, ‖f x‖ ^ 2 ∂μ : ℝ) : ℂ) := by
    rw [lcaConvolution, ← integral_complex_ofReal]
    apply integral_congr_ae
    exact .of_forall fun x ↦ by
      simp [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have h := congrArg Complex.re (hρ 1)
  simp only [map_one, Circle.coe_one, integral_const, Complex.real_smul, mul_one,
    Complex.ofReal_re, hAuto] at h
  rw [← ENNReal.ofReal_toReal (measure_ne_top ρ univ)]
  change ENNReal.ofReal (ρ.real univ) = _
  rw [h, ofReal_integral_eq_lintegral_ofReal (hSqC.integrable_of_hasCompactSupport hSqK)
    (.of_forall fun x ↦ sq_nonneg _)]
  exact lintegral_congr fun x ↦ by rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

open scoped CompactlySupported in
/-- A nonnegative compactly supported bump fixes the normalization of Haar measure
on the dual. Its spectral measure gives positive mass to a compact set, so the
averaging identity on that set ensures its squared Fourier integral is finite. -/
private theorem exists_lcaFourier_weighted_haar
    (ρ : C_c(G, ℂ) → Measure (PontryaginDual G))
    (hρ : ∀ f, IsFiniteMeasure (ρ f) ∧ (ρ f).Regular ∧
      ∀ x : G, (∫ χ, (χ x : ℂ) ∂(ρ f)) =
        lcaConvolution μ f (fun y ↦ star (f y⁻¹)) x) :
    ∃ ν : Measure (PontryaginDual G), ν.IsHaarMeasure ∧ ν.Regular ∧
      ∀ f : C_c(G, ℂ), ν.withDensity (fun χ ↦ ‖lcaFourier μ f χ‖ₑ ^ 2) = ρ f := by
  let η : Measure (PontryaginDual G) := MeasureTheory.Measure.haar
  let (g : C_c(G, ℂ)) : IsFiniteMeasure (ρ g) := (hρ g).1
  let (g : C_c(G, ℂ)) : (ρ g).Regular := (hρ g).2.1
  obtain ⟨b, hbK, hb₀, hb₁⟩ := exists_continuous_nonneg_pos (1 : G)
  let f : C_c(G, ℂ) := ⟨⟨fun x ↦ (b x : ℂ), Complex.continuous_ofReal.comp b.continuous⟩,
    hbK.comp_left Complex.ofReal_zero⟩
  let w (g : C_c(G, ℂ)) (χ : PontryaginDual G) := ‖lcaFourier μ g χ‖ₑ ^ 2
  have hf₁ : f 1 ≠ 0 := Complex.ofReal_ne_zero.mpr hb₁
  have hw (g : C_c(G, ℂ)) : Continuous (w g) :=
    ENNReal.continuous_coe.comp ((continuous_lcaFourier μ g.integrable).nnnorm.pow 2)
  have hfSq : Continuous (fun x ↦ ‖f x‖ₑ ^ 2) :=
    ENNReal.continuous_coe.comp (f.continuous.nnnorm.pow 2)
  have hM : ρ f univ ≠ 0 := by
    rw [lcaAutocorrelation_measure_univ μ f (ρ f) (hρ f).2.2]
    apply ne_of_gt
    apply (lintegral_pos_iff_support hfSq.measurable).2
    exact (isOpen_ne_fun hfSq continuous_const).measure_pos μ
      ⟨1, show ‖f 1‖ₑ ^ 2 ≠ 0 by simpa using hf₁⟩
  have hF₁ : lcaFourier μ f 1 ≠ 0 := by
    simp only [lcaFourier, PontryaginDual.one_apply, Circle.coe_one, star_one, mul_one]
    change (∫ x, (b x : ℂ) ∂μ) ≠ 0
    rw [integral_complex_ofReal]
    exact Complex.ofReal_ne_zero.mpr
      (b.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero hbK hb₀ hb₁).ne'
  let I : ℝ≥0∞ := ∫⁻ χ, w f χ ∂η
  have hI₀ : I ≠ 0 := by
    apply ne_of_gt
    apply (lintegral_pos_iff_support (hw f).measurable).2
    exact (isOpen_ne_fun (hw f) continuous_const).measure_pos η
      ⟨1, show w f 1 ≠ 0 by simpa [w] using hF₁⟩
  obtain ⟨K, -, hK, hKpos⟩ := MeasurableSet.univ.exists_lt_isCompact (pos_iff_ne_zero.mpr hM)
  have hI_top : I ≠ ⊤ := by
    intro h
    have hAvg := lcaAutocorrelation_measure_mul_lintegral μ η f f (ρ f) (ρ f)
      (hρ f).2.2 (hρ f).2.2 hK.isClosed.measurableSet
    change I * ρ f K = ρ f univ * (∫⁻ χ in K, w f χ ∂η) at hAvg
    rw [h, ENNReal.top_mul hKpos.ne'] at hAvg
    have hBound (χ : PontryaginDual G) : w f χ ≤ ENNReal.ofReal (∫ x, ‖f x‖ ∂μ) ^ 2 := by
      change ‖lcaFourier μ f χ‖ₑ ^ 2 ≤ _
      rw [← ofReal_norm]
      exact pow_le_pow_left' (ENNReal.ofReal_le_ofReal
        (norm_lcaFourier_le_integral_norm μ f χ)) _
    have hFinite : (∫⁻ χ in K, w f χ ∂η) < ⊤ := by
      refine (lintegral_mono hBound).trans_lt ?_
      rw [setLIntegral_const]
      exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top) hK.measure_lt_top
    exact (ENNReal.mul_lt_top (measure_lt_top (ρ f) univ) hFinite).ne hAvg.symm
  let c := ρ f univ * I⁻¹
  have hc₀ : c ≠ 0 := mul_ne_zero hM (ENNReal.inv_ne_zero.mpr hI_top)
  have hc_top : c ≠ ⊤ :=
    ENNReal.mul_ne_top (measure_ne_top (ρ f) univ) (ENNReal.inv_ne_top.mpr hI₀)
  refine ⟨c • η, Measure.IsHaarMeasure.smul η hc₀ hc_top, Measure.Regular.smul hc_top, ?_⟩
  intro g
  ext1 s hs
  have hAvg := lcaAutocorrelation_measure_mul_lintegral μ η f g (ρ f) (ρ g)
    (hρ f).2.2 (hρ g).2.2 hs
  change I * ρ g s = ρ f univ * (∫⁻ χ in s, w g χ ∂η) at hAvg
  change (c • η).withDensity (w g) s = _
  rw [withDensity_apply _ hs, setLIntegral_smul_measure, smul_eq_mul]
  calc
    c * (∫⁻ χ in s, w g χ ∂η) = I⁻¹ * (ρ f univ * (∫⁻ χ in s, w g χ ∂η)) := by
      dsimp [c]
      ac_rfl
    _ = ρ g s := by rw [← hAvg, ← mul_assoc, ENNReal.inv_mul_cancel hI₀ hI_top, one_mul]

open scoped CompactlySupported in
/-- There is a regular Haar measure on the dual for which the Fourier transform
preserves the L² norm of every continuous compactly supported function. It suffices
to construct this measure by Fourier inversion at the identity for autocorrelations
of such functions. -/
theorem exists_lcaFourier_eLpNorm_eq_of_hasCompactSupport :
    ∃ ν : Measure (PontryaginDual G), ν.IsHaarMeasure ∧ ν.Regular ∧
      ∀ (f : G → ℂ), Continuous f → HasCompactSupport f →
        eLpNorm (lcaFourier μ f) 2 ν = eLpNorm f 2 μ := by
  choose ρ hρ using exists_lcaAutocorrelation_measure μ
  obtain ⟨ν, hHaar, hRegular, hDensity⟩ := exists_lcaFourier_weighted_haar μ ρ hρ
  refine ⟨ν, hHaar, hRegular, fun f hf hs ↦ ?_⟩
  let g : C_c(G, ℂ) := ⟨⟨f, hf⟩, hs⟩
  let : IsFiniteMeasure (ρ g) := (hρ g).1
  have hMass : ρ g univ = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ :=
    lcaAutocorrelation_measure_univ μ g (ρ g) (hρ g).2.2
  have hSqEq : (∫⁻ χ, ‖lcaFourier μ f χ‖ₑ ^ 2 ∂ν) = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ := by
    have h := congrArg (fun m : Measure (PontryaginDual G) ↦ m univ) (hDensity g)
    change (ν.withDensity (fun χ ↦ ‖lcaFourier μ f χ‖ₑ ^ 2)) univ = ρ g univ at h
    rwa [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hMass] at h
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top,
    eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_ofNat]
  rw [hSqEq]

/-- Paper: Lemma D.1.1.2(4), p. 747. There is exactly one Plancherel measure. -/
theorem lcaPlancherelMeasure_existsUnique :
    ∃! ν : Measure (PontryaginDual G), IsLCAPlancherelMeasure μ ν := by
  obtain ⟨ν, hHaar, hReg, hNorm⟩ := exists_lcaFourier_eLpNorm_eq_of_hasCompactSupport μ
  let := hHaar
  let := hReg
  have hν := isLCAPlancherelMeasure_of_compactSupport μ ν hNorm
  exact ⟨ν, hν, fun ν' hν' ↦ isLCAPlancherelMeasure_unique μ hν' hν⟩

end Masullo
