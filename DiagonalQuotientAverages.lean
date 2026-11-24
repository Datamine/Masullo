import DiagonalQuotientTrace
import QuotientLiftedL1
import TranslationAverages

open Filter Function MeasureTheory Set Topology
open scoped ENNReal NNReal Pointwise

namespace Masullo

noncomputable section

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
variable (H : Subgroup G) (hH : IsClosed (H : Set G)) [DiscreteTopology H]

local instance : MeasurableSpace (G ⧸ H) := borel _
local instance : BorelSpace (G ⧸ H) := ⟨rfl⟩
private abbrev q := (QuotientGroup.mk : G → G ⧸ H)

omit [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] in
private theorem translate_product (p : G × G) (A B : Set G) :
    p • (A ×ˢ B) = (p.1 • A) ×ˢ (p.2 • B) := by
  ext z
  simp only [mem_smul_set, mem_prod]
  constructor
  · rintro ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩
    exact ⟨⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩⟩
  · rintro ⟨⟨a, ha, hxa⟩, ⟨b, hb, hxb⟩⟩
    exact ⟨(a, b), ⟨ha, hb⟩, Prod.ext hxa hxb⟩

omit [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [DiscreteTopology H] in
private theorem quotient_image_translate (x : G) (U : Set G) :
    q H '' (x • U) = q H x • (q H '' U) :=
  Set.image_smul_distrib (QuotientGroup.mk' H) x U

omit [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [DiscreteTopology H] in
private theorem translate_injOn (x : G) {U : Set G} (h : InjOn (q H) U) :
    InjOn (q H) (x • U) := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hab
  change QuotientGroup.mk (x * a) = QuotientGroup.mk (x * b) at hab
  rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul] at hab
  exact congrArg (fun y => x * y) (h ha hb (mul_left_cancel hab))

private theorem eventually_bound_absolute_means {X : Type*} [Group X] [MeasurableSpace X]
    (μ : Measure X) [μ.IsMulLeftInvariant] (W : ℕ → Set X) (g : X → ℂ) (x : X)
    (h : Tendsto (fun n => translatedAverage μ (W n) (fun y => (‖g y‖ : ℂ)) x)
      atTop (𝓝 (‖g x‖ : ℂ))) :
    ∀ᶠ n in atTop, (⨍ y in x • W n, ‖g y‖ ∂μ) ≤ ‖g x‖ + 1 := by
  have he (n : ℕ) : (translatedAverage μ (W n) (fun y => (‖g y‖ : ℂ)) x).re =
      ⨍ y in x • W n, ‖g y‖ ∂μ := by
    rw [translatedAverage_eq_average, average_eq, average_eq, integral_complex_ofReal,
      Complex.smul_re, Complex.ofReal_re, smul_eq_mul]
  have ht := Complex.continuous_re.continuousAt.tendsto.comp h
  change Tendsto (fun n => (translatedAverage μ (W n) (fun y => (‖g y‖ : ℂ)) x).re)
    atTop (𝓝 (‖g x‖ : ℂ).re) at ht
  simp only [he, Complex.ofReal_re] at ht
  exact ht.eventually (Iic_mem_nhds (lt_add_one ‖g x‖))

include hH in
/-- Proposition 12.2.2.2(4), with the a.e. limit made explicit. The
quotient and ambient averaging measures use the same counting-fibre
normalization. Compact closure, rather than closedness, suffices. -/
theorem diagonalIndentation_ae_average
    (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular] [SigmaFinite μ]
    (ν : Measure (G ⧸ H)) [ν.IsHaarMeasure] [SigmaFinite ν]
    (hν : IsWeilQuotientMeasure H μ Measure.count ν)
    (u : C(G, ℝ))
    (hp : ∀ L : Set (G ⧸ H), IsCompact L → IsCompact (tsupport u ∩ q H ⁻¹' L))
    (hn : ∀ x, 0 ≤ u x)
    (U : ℕ → Set G) (hUone : ∀ n, 1 ∈ U n) (hUd : Antitone U) (hUo : ∀ n, IsOpen (U n)) (hUi : ∀ n, InjOn (q H) (U n))
    (hUc : IsCompact (closure (U 0))) (hUcof : CofinalAtOne U)
    (f : (G ⧸ H) × (G ⧸ H) → ℂ) (hf : LocallyIntegrable f (ν.prod ν))
    (V : ℕ → Set (G ⧸ H)) (hV : ∀ n, V n = q H '' U n)
    (hVd : DoublingSequence ν V) {C : ℝ≥0} (hC : 0 < C)
    (hDiff : ∀ n, ν (V n * (V n)⁻¹) < C * ν (V n)) :
    let Q := Prod.map (q H) (q H)
    let W n := V n ×ˢ V n
    let φ (z : G × G) := (diagonalIndentation H u z.1 z.2 : ℂ)
    let fReg := regularizedLimit (fun n => translatedAverage (ν.prod ν) (W n) f)
    let g (z : G × G) := φ z * f (Q z)
    LocallyIntegrable g (μ.prod μ) ∧ Measurable fReg ∧
      (∀ᵐ p ∂μ.prod μ,
        Tendsto (fun n => translatedAverage (ν.prod ν) (W n) f (Q p)) atTop (𝓝 (fReg (Q p))) ∧
        Tendsto (fun n => translatedAverage (μ.prod μ) (U n ×ˢ U n) g p)
          atTop (𝓝 (φ p * fReg (Q p)))) := by
  intro Q W φ fReg g
  letI : T1Space (G ⧸ H) := QuotientGroup.t1Space_iff.mpr hH
  letI : (Measure.count : Measure H).IsHaarMeasure := subgroup_count_isHaarMeasure H
  letI : LocallyCompactSpace H := hH.locallyCompactSpace
  letI : SecondCountableTopology H := TopologicalSpace.Subtype.secondCountableTopology (H : Set G)
  letI : Measure.Regular (Measure.count : Measure H) :=
    Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _
  have hL := weilQuotientMeasure_lift_eq H hH μ ν hν
  letI : SigmaFinite (quotientLiftedMeasure H Measure.count ν) := hL ▸ inferInstance
  letI : Measure.Regular (ν.prod ν) :=
    Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _
  have hq : Measure.QuasiMeasurePreserving (q H) μ ν := by
    rw [← hL]
    exact quotientLiftedMeasure_quasiMeasurePreserving H hH Measure.count ν
  have hQ : Measure.QuasiMeasurePreserving Q (μ.prod μ) (ν.prod ν) :=
    QuasiMeasurePreserving.prodMap hq hq
  have hφ : Continuous φ :=
    Complex.continuous_ofReal.comp (diagonalIndentation_continuous H hH u hp hn).2.1
  have hVcof : CofinalAtOne V := by
    intro N hN
    obtain ⟨k, hk⟩ := hUcof ((q H) ⁻¹' N)
      (QuotientGroup.continuous_mk.continuousAt.preimage_mem_nhds
        (show N ∈ 𝓝 (q H 1) by simpa using hN))
    exact ⟨k, (hV k).symm ▸ image_subset_iff.mpr hk⟩
  have hv₀ : IsCompact (closure (V 0)) := by
    have hqi : IsCompact (q H '' closure (U 0)) := hUc.image QuotientGroup.continuous_mk
    exact hqi.of_isClosed_subset isClosed_closure
      (closure_minimal (by rw [hV]; exact image_mono subset_closure) hqi.isClosed)
  have hWc : IsCompact (closure (W 0)) := by
    rw [show W 0 = V 0 ×ˢ V 0 from rfl, closure_prod_eq]
    exact hv₀.prod hv₀
  have hWd : DoublingSequence (ν.prod ν) W := doublingSequence_measure_prod hVd hVd
  have hWcof : CofinalAtOne W :=
    doublingSequence_prod_properties.1 hVd.decreasing hVd.decreasing hVcof hVcof
  have hdiff (n : ℕ) : (ν.prod ν) (W n * (W n)⁻¹) < (↑(C * C) : ℝ≥0∞) * (ν.prod ν) (W n) := by
    simp only [W, Set.inv_prod, Set.prod_mul_prod_comm, Measure.prod_prod, ENNReal.coe_mul]
    simpa only [mul_mul_mul_comm] using ENNReal.mul_lt_mul (hDiff n) (hDiff n)
  obtain ⟨hcont, hlim⟩ := translatedAverage_ae_of_locallyIntegrable_of_isCompact_closure
    (ν.prod ν) hWd hWcof hWc (mul_pos hC hC) hdiff hf
  have hfN : LocallyIntegrable (fun x => (‖f x‖ : ℂ)) (ν.prod ν) := by
    intro z
    obtain ⟨s, hs, hi⟩ := hf z
    exact ⟨s, hs, hi.norm.ofReal⟩
  have hlimN := (translatedAverage_ae_of_locallyIntegrable_of_isCompact_closure
    (ν.prod ν) hWd hWcof hWc (mul_pos hC hC) hdiff hfN).2
  have hVcn (n : ℕ) : IsCompact (closure (V n)) :=
    hv₀.of_isClosed_subset isClosed_closure (closure_mono (hVd.decreasing (Nat.zero_le n)))
  have hfi (p : G × G) (n : ℕ) : IntegrableOn f
      ((q H '' (p.1 • U n)) ×ˢ (q H '' (p.2 • U n))) (ν.prod ν) := by
    rw [quotient_image_translate, quotient_image_translate, ← hV]
    have hc₁ : Continuous (fun z : G ⧸ H => q H p.1 * z) := by fun_prop
    have hc₂ : Continuous (fun z : G ⧸ H => q H p.2 * z) := by fun_prop
    apply (hf.integrableOn_isCompact
      (((hVcn n).image hc₁).prod ((hVcn n).image hc₂))).mono_set
    exact Set.prod_mono (image_mono subset_closure) (image_mono subset_closure)
  have hloc : LocallyIntegrable g (μ.prod μ) := by
    intro p
    let J := (p.1 • U 0) ×ˢ (p.2 • U 0)
    have hJ : IsOpen J := ((hUo 0).smul p.1).prod ((hUo 0).smul p.2)
    have hpJ : p ∈ J := by
      exact ⟨⟨1, hUone 0, mul_one p.1⟩, ⟨1, hUone 0, mul_one p.2⟩⟩
    refine ⟨J, hJ.mem_nhds hpJ, ?_⟩
    have hpres := quotientLiftedMeasure_preserving_productSlices H hH ν
      ((hUo 0).smul p.1) ((hUo 0).smul p.2) (translate_injOn H p.1 (hUi 0))
      (translate_injOn H p.2 (hUi 0))
    rw [hL] at hpres
    have hi : Integrable (f ∘ Q) ((μ.prod μ).restrict J) :=
      hpres.integrable_comp_of_integrable (hfi p 0)
    let K := (p.1 • closure (U 0)) ×ˢ (p.2 • closure (U 0))
    have hK : IsCompact K := (hUc.image (continuous_const.mul continuous_id)).prod
      (hUc.image (continuous_const.mul continuous_id))
    obtain ⟨a, ha⟩ := (hK.image hφ.norm).bddAbove
    exact hi.bdd_mul hφ.aestronglyMeasurable (by
      filter_upwards [ae_restrict_mem hJ.measurableSet] with z hz
      exact ha ⟨z, Set.prod_mono (image_mono subset_closure) (image_mono subset_closure) hz, rfl⟩)
  refine ⟨hloc, regularizedLimit_measurable (fun n => (hcont n).measurable), ?_⟩
  filter_upwards [hQ.ae hlim, hQ.ae hlimN] with p hp1 hp2
  refine ⟨?_, ?_⟩
  · rw [show fReg (Q p) = f (Q p) from regularizedLimit_tendsto hp1]
    exact hp1
  have hm (n : ℕ) : (q H '' (p.1 • U n)) ×ˢ (q H '' (p.2 • U n)) = Q p • W n := by
    rw [quotient_image_translate, quotient_image_translate, ← hV, translate_product]
    rfl
  have hnmb := eventually_bound_absolute_means (ν.prod ν) W f (Q p) hp2
  have hsmall : ∀ N ∈ 𝓝 p, ∀ᶠ n in atTop, (p.1 • U n) ×ˢ (p.2 • U n) ⊆ N := by
    intro N hN
    have hp' : 𝓝 p = 𝓝 p.1 ×ˢ 𝓝 p.2 := nhds_prod_eq
    rw [hp'] at hN
    obtain ⟨A, hA, B, hB, hAB⟩ := Filter.mem_prod_iff.mp hN
    have ht₁ : Continuous (fun z : G => p.1 * z) := by fun_prop
    have ht₂ : Continuous (fun z : G => p.2 * z) := by fun_prop
    obtain ⟨i, hi⟩ := hUcof ((fun z : G => p.1 * z) ⁻¹' A)
      (ht₁.continuousAt.preimage_mem_nhds (by simpa using hA))
    obtain ⟨j, hj⟩ := hUcof ((fun z : G => p.2 * z) ⁻¹' B)
      (ht₂.continuousAt.preimage_mem_nhds (by simpa using hB))
    filter_upwards [eventually_ge_atTop (max i j)] with n h
    refine (Set.prod_mono ?_ ?_).trans hAB
    · rintro _ ⟨y, hy, rfl⟩
      exact hi (hUd ((le_max_left i j).trans h) hy)
    · rintro _ ⟨y, hy, rfl⟩
      exact hj (hUd ((le_max_right i j).trans h) hy)
  have hfa : Tendsto (fun n => ⨍ z in (q H '' (p.1 • U n)) ×ˢ (q H '' (p.2 • U n)), f z ∂ν.prod ν)
      atTop (𝓝 (f (Q p))) := by
    simpa only [translatedAverage_eq_average, hm] using hp1
  have hfb : ∀ᶠ n in atTop,
      (⨍ z in (q H '' (p.1 • U n)) ×ˢ (q H '' (p.2 • U n)), ‖f z‖ ∂ν.prod ν) ≤ ‖f (Q p)‖ + 1 := by
    simpa only [hm] using hnmb
  have h := diagonalIndentation_average_limit H hH u hp hn ν p (fun n => p.1 • U n)
    (fun n => p.2 • U n) (fun n => (hUo n).smul p.1) (fun n => (hUo n).smul p.2)
    (fun n => translate_injOn H p.1 (hUi n)) (fun n => translate_injOn H p.2 (hUi n))
    hsmall f (hfi p) (f (Q p)) hfa (‖f (Q p)‖ + 1) (by positivity) hfb
  rw [show fReg (Q p) = f (Q p) from regularizedLimit_tendsto hp1]
  simp only [translatedAverage_eq_average, translate_product, g, Q, φ]
  have ht : ∀ z : G × G, Prod.map (q H) (q H) z = (q H z.1, q H z.2) := fun _ => rfl
  simpa only [Q, ht, hL] using h

include hH in
/-- The counting lift of a quotient measure assigns at least the measure
of the image to an open set. Equality holds if the open set is a slice. -/
theorem quotientLiftedMeasure_open_image_le (ν : Measure (G ⧸ H))
    {A : Set G} (hA : IsOpen A) :
    ν (q H '' A) ≤ (quotientLiftedMeasure H Measure.count ν) A := by
  letI : (Measure.count : Measure H).IsHaarMeasure := subgroup_count_isHaarMeasure H
  letI : LocallyCompactSpace H := hH.locallyCompactSpace
  letI : SecondCountableTopology H := TopologicalSpace.Subtype.secondCountableTopology (H : Set G)
  letI : Measure.Regular (Measure.count : Measure H) :=
    Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _
  have hi : MeasurableSet (q H '' A) := (QuotientGroup.isOpenMap_coe _ hA).measurableSet
  rw [← lintegral_indicator_one hi, quotientLiftedMeasure,
    Measure.bind_apply hA.measurableSet
      (quotientCosetMeasure_measurable H hH (Measure.count : Measure H)).aemeasurable]
  apply lintegral_mono
  intro c
  by_cases hc : c ∈ q H '' A
  · obtain ⟨a, ha, hac⟩ := hc
    let b : H := ⟨c.out⁻¹ * a, QuotientGroup.eq.mp ((Quotient.out_eq' c).trans hac.symm)⟩
    let t : H → G := fun k => c.out * (k : G)
    have ht : Measurable t := (continuous_const.mul continuous_subtype_val).measurable
    have hb : t b ∈ A := by convert ha using 1; simp [t, b]
    rw [indicator_of_mem (show c ∈ q H '' A from ⟨a, ha, hac⟩)]
    change 1 ≤ (Measure.count.map t) A
    rw [Measure.map_apply ht hA.measurableSet]
    simpa using (measure_mono (Set.singleton_subset_iff.mpr hb) :
      (Measure.count : Measure H) {b} ≤ Measure.count (t ⁻¹' A))
  · rw [indicator_of_notMem hc]
    exact zero_le

include hH in
/-- The quotient images of the ambient open slice windows obey the same
adjacent-stage and same-stage upper bounds. -/
theorem weilQuotientMeasure_doublingSequence (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]
    [SigmaFinite μ] (ν : Measure (G ⧸ H)) (hν : IsWeilQuotientMeasure H μ Measure.count ν)
    (U : ℕ → Set G) (hU : DoublingSequence μ U)
    (hUo : ∀ n, IsOpen (U n)) (hUi : ∀ n, InjOn (q H) (U n))
    {C : ℝ≥0} (hDiff : ∀ n, μ (U n * (U n)⁻¹) < C * μ (U n)) :
    let V (n : ℕ) := q H '' U n
    DoublingSequence ν V ∧ (∀ n, ν (V n * (V n)⁻¹) < C * ν (V n)) := by
  intro V
  have hL := weilQuotientMeasure_lift_eq H hH μ ν hν
  have hVo (n : ℕ) : IsOpen (V n) := QuotientGroup.isOpenMap_coe _ (hUo n)
  have hV1 (n : ℕ) : 1 ∈ V n := ⟨1, hU.one_mem n, map_one (QuotientGroup.mk' H)⟩
  have he (n : ℕ) : ν (V n) = μ (U n) := by
    have hm := congrArg (fun m : Measure (G ⧸ H) => m univ)
      (quotientLiftedMeasure_injective_slice H hH ν (hUo n).measurableSet (hVo n).measurableSet (hUi n))
    rw [hL, Measure.map_apply QuotientGroup.continuous_mk.measurable MeasurableSet.univ,
      preimage_univ, Measure.restrict_apply_univ, Measure.restrict_apply_univ] at hm
    exact hm.symm
  refine ⟨⟨hV1, fun n => (hVo n).measurableSet, fun n => (he n).symm ▸ hU.positive n,
    fun n => (he n).symm ▸ hU.finite n, fun _ _ h => image_mono (hU.decreasing h), ?_⟩, ?_⟩
  · obtain ⟨C', hC', hbound⟩ := hU.doubling
    refine ⟨C', hC', fun n => ⟨?_, ?_⟩⟩
    · exact ((he (n + 1)).symm ▸ hU.positive (n + 1)).trans_le
        (measure_mono fun x hx => ⟨x, hx, 1, hV1 n, mul_one x⟩)
    · calc
        ν (V (n + 1) * V n) = ν (q H '' (U (n + 1) * U n)) := by
          change ν ((q H '' U (n + 1)) * (q H '' U n)) = _
          exact congrArg (fun S => ν S) ((Set.image_mul (QuotientGroup.mk' H)
            (s := U (n + 1)) (t := U n)).symm)
        _ ≤ μ (U (n + 1) * U n) := by
          rw [← hL]
          exact quotientLiftedMeasure_open_image_le H hH ν ((hUo (n + 1)).mul_right)
        _ < _ := by rw [he]; exact (hbound n).2
  · intro n
    calc
      ν (V n * (V n)⁻¹) = ν (q H '' (U n * (U n)⁻¹)) := by
        change ν ((q H '' U n) * (q H '' U n)⁻¹) = _
        let qhom := QuotientGroup.mk' H
        change ν ((qhom '' U n) * (qhom '' U n)⁻¹) = ν (qhom '' (U n * (U n)⁻¹))
        rw [Set.image_mul qhom, Set.image_inv qhom]
      _ ≤ μ (U n * (U n)⁻¹) := by
        rw [← hL]
        exact quotientLiftedMeasure_open_image_le H hH ν ((hUo n).mul_right)
      _ < _ := by rw [he]; exact hDiff n

/-- The diagonal cutoff lift of a function on the product quotient. -/
def diagonalIndentationLift (u : C(G, ℝ)) (f : (G ⧸ H) × (G ⧸ H) → ℂ)
    (p : G × G) : ℂ :=
  (diagonalIndentation H u p.1 p.2 : ℂ) * f (q H p.1, q H p.2)

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [BorelSpace G] [DiscreteTopology H] in
/-- Multiplying by a quotient function commutes with the cutoff lift. -/
theorem diagonalIndentationLift_mul (u : C(G, ℝ)) (r f : (G ⧸ H) × (G ⧸ H) → ℂ)
    (p : G × G) :
    diagonalIndentationLift H u (r * f) p =
      r (q H p.1, q H p.2) * diagonalIndentationLift H u f p := by
  simp only [diagonalIndentationLift, Pi.mul_apply]
  ring

include hH in
/-- The four trace integrals of Proposition 12.2.2.2 agree on a Borel
transversal. The quotient function may be the measurable smoothing of a
locally integrable input, with integrable diagonal trace. -/
theorem diagonalIndentationLift_trace
    (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular] [SigmaFinite μ]
    (ν : Measure (G ⧸ H)) (hν : IsWeilQuotientMeasure H μ Measure.count ν)
    {D : Set G} (hD : MeasurableSet D) (hDt : BijOn (q H) D univ)
    (u : C(G, ℝ))
    (hp : ∀ L : Set (G ⧸ H), IsCompact L → IsCompact (tsupport u ∩ q H ⁻¹' L))
    (hpos : ∀ x, 0 ≤ u x)
    (hn : ∀ x : G, (∫ h : H, u ((h : G)⁻¹ * x) ∂Measure.count) = 1)
    (f : (G ⧸ H) × (G ⧸ H) → ℂ) (hf : Measurable f)
    (htrace : Integrable (fun c => f (c, c)) ν) :
    let L (p : G × H) := diagonalIndentationLift H u f ((p.2 : G)⁻¹ * p.1, p.1)
    let R (p : G × H) := diagonalIndentationLift H u f (p.1, (p.2 : G)⁻¹ * p.1)
    Measurable L ∧ Measurable R ∧ Integrable L ((μ.restrict D).prod Measure.count) ∧
      Integrable R ((μ.restrict D).prod Measure.count) ∧
      (∫ x in D, ∫ h, L (x, h) ∂Measure.count ∂μ) = ∫ c, f (c, c) ∂ν ∧
      (∫ h, ∫ x in D, L (x, h) ∂μ ∂Measure.count) = ∫ c, f (c, c) ∂ν ∧
      (∫ x in D, ∫ h, R (x, h) ∂Measure.count ∂μ) = ∫ c, f (c, c) ∂ν ∧
      (∫ h, ∫ x in D, R (x, h) ∂μ ∂Measure.count) = ∫ c, f (c, c) ∂ν := by
  intro L R
  have hq : Measurable (q H) := QuotientGroup.continuous_mk.measurable
  have hc : Continuous (fun z : G × G => (diagonalIndentation H u z.1 z.2 : ℂ)) :=
    Complex.continuous_ofReal.comp (diagonalIndentation_continuous H hH u hp hpos).2.1
  have hmeas : Measurable (diagonalIndentationLift H u f) :=
    hc.measurable.mul (hf.comp (hq.prodMap hq))
  have heq : L = R := by
    funext p
    have hπ : q H ((p.2 : G)⁻¹ * p.1) = q H p.1 := by
      change QuotientGroup.mk ((p.2 : G)⁻¹ * p.1) = _
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv,
        (QuotientGroup.eq_one_iff _).mpr p.2.property, inv_one, one_mul]
    simp only [L, R, diagonalIndentationLift, hπ]
    congr 2
    unfold diagonalIndentation
    exact integral_congr_ae (.of_forall fun _ => mul_comm _ _)
  have hR : Measurable R := hmeas.comp ((continuous_fst.prodMk
    (((continuous_subtype_val.comp continuous_snd).inv).mul continuous_fst)).measurable)
  obtain ⟨h1, h2, h3⟩ := diagonalIndentation_trace_integral H hH u hp hpos hn (μ.restrict D)
    ν (weilQuotientMeasure_transversal H hH μ ν hν hD hDt) _ htrace
  have hr : R = fun p => (diagonalIndentation H u p.1 ((p.2 : G)⁻¹ * p.1) : ℂ) *
      f (q H p.1, q H p.1) := by
    funext p
    have hπ : q H ((p.2 : G)⁻¹ * p.1) = q H p.1 := by
      change QuotientGroup.mk ((p.2 : G)⁻¹ * p.1) = _
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv,
        (QuotientGroup.eq_one_iff _).mpr p.2.property, inv_one, one_mul]
    change (diagonalIndentation H u p.1 ((p.2 : G)⁻¹ * p.1) : ℂ) *
      f (q H p.1, q H ((p.2 : G)⁻¹ * p.1)) = _
    rw [hπ]
  rw [heq]
  refine ⟨hR, hR, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [hr]
  · exact h1
  · exact h1
  · exact h2
  · exact h3
  · exact h2
  · exact h3

omit [T2Space G] [LocallyCompactSpace G] [DiscreteTopology H] in
/-- An ambient open slice containing the identity extends to a Borel
transversal. This makes the trace integrals available without a
measurability assumption on an initially specified choice of representatives. -/
theorem quotient_borel_transversal_of_open_slice {U : Set G}
    (ho : IsOpen U) (h1 : 1 ∈ U) (hi : InjOn (q H) U) :
    ∃ D : Set G, MeasurableSet D ∧ U ⊆ D ∧ BijOn (q H) D univ := by
  have hlocal : IsLocalHomeomorph (q H) := by
    apply isLocalHomeomorph_iff_isOpenEmbedding_restrict.mpr
    intro x
    have hx : x ∈ x • U := ⟨1, h1, mul_one x⟩
    have hopen := ho.smul x
    refine ⟨x • U, hopen.mem_nhds hx, .of_continuous_injective_isOpenMap
      (QuotientGroup.continuous_mk.comp continuous_subtype_val) ?_ ?_⟩
    · intro a b hab
      exact Subtype.ext (translate_injOn H x hi a.property b.property hab)
    · exact QuotientGroup.isOpenMap_coe.comp hopen.isOpenEmbedding_subtypeVal.isOpenMap
  obtain ⟨D, hD, hUD, hiD, hs⟩ := borel_section_extend hlocal
    QuotientGroup.mk_surjective U ho.measurableSet hi
  exact ⟨D, hD, hUD, mapsTo_univ _ _, hiD, hs.superset⟩

omit [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [BorelSpace G] in
private theorem doublingSequence_self_difference_bound (μ : Measure G)
    [IsFiniteMeasureOnCompacts μ] (U : ℕ → Set G) (hU : DoublingSequence μ U)
    (hS : ∀ n, (U n)⁻¹ = U n) (hUc : IsCompact (closure (U 0))) :
    ∃ C : ℝ≥0, 0 < C ∧ ∀ n, μ (U n * (U n)⁻¹) < C * μ (U n) := by
  obtain ⟨B, hB, hbd⟩ := hU.doubling
  have hfin : μ (U 0 * (U 0)⁻¹) < ⊤ := by
    rw [hS]
    exact (measure_mono (Set.mul_subset_mul subset_closure subset_closure)).trans_lt
      (hUc.mul hUc).measure_lt_top
  let R := μ (U 0 * (U 0)⁻¹) / μ (U 0)
  have hR : R < ⊤ := ENNReal.div_lt_top hfin.ne (hU.positive 0).ne'
  let C := B + R.toNNReal + 1
  have hCB : B ≤ C :=
    (le_add_of_nonneg_right (zero_le : 0 ≤ R.toNNReal)).trans (le_add_of_nonneg_right zero_le)
  refine ⟨C, hB.trans_le hCB, fun n => ?_⟩
  cases n with
  | zero =>
    apply (ENNReal.div_lt_iff (.inl (hU.positive 0).ne') (.inl (hU.finite 0).ne)).mp
    change R < (C : ℝ≥0∞)
    rw [← ENNReal.coe_toNNReal hR.ne]
    exact_mod_cast (show R.toNNReal < C from by
      change R.toNNReal < B + R.toNNReal + 1
      exact (le_add_of_nonneg_left (zero_le : 0 ≤ B)).trans_lt (lt_add_one _))
  | succ n =>
    rw [hS]
    exact ((measure_mono (Set.mul_subset_mul Subset.rfl (hU.decreasing (Nat.le_succ n)))).trans_lt
      (hbd n).2).trans_le (mul_le_mul_of_nonneg_right (by exact_mod_cast hCB) zero_le)

include hH in
set_option maxHeartbeats 800000 in
/-- The smoothed cutoff identity in 12.2.2.2(4) for the ambient window
sequence. Both the quotient and ambient points are regular almost
everywhere for ambient product Haar measure. -/
theorem diagonalIndentation_regularized_average
    (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular] [SigmaFinite μ]
    (ν : Measure (G ⧸ H)) [ν.IsHaarMeasure] [SigmaFinite ν]
    (hν : IsWeilQuotientMeasure H μ Measure.count ν)
    (u : C(G, ℝ))
    (hp : ∀ L : Set (G ⧸ H), IsCompact L → IsCompact (tsupport u ∩ q H ⁻¹' L))
    (hn : ∀ x, 0 ≤ u x)
    (U : ℕ → Set G) (hU : DoublingSequence μ U)
    (hUo : ∀ n, IsOpen (U n)) (hUi : ∀ n, InjOn (q H) (U n))
    (hUc : IsCompact (closure (U 0))) (hUcof : CofinalAtOne U)
    (hS : ∀ n, (U n)⁻¹ = U n)
    (f : (G ⧸ H) × (G ⧸ H) → ℂ) (hf : LocallyIntegrable f (ν.prod ν)) :
    let V n := (q H '' U n) ×ˢ (q H '' U n)
    let F n := translatedAverage (ν.prod ν) (V n) f
    let g := diagonalIndentationLift H u f
    let Gavg n := translatedAverage (μ.prod μ) (U n ×ˢ U n) g
    LocallyIntegrable g (μ.prod μ) ∧ Measurable (regularizedLimit F) ∧
    Measurable (fun c => regularizedLimit F (c, c)) ∧
    Measurable (regularizedLimit Gavg) ∧
    (∀ᵐ p ∂μ.prod μ,
      Tendsto (fun n => F n (q H p.1, q H p.2)) atTop
        (𝓝 (regularizedLimit F (q H p.1, q H p.2))) ∧
      Tendsto (fun n => Gavg n p) atTop
        (𝓝 (diagonalIndentationLift H u (regularizedLimit F) p)) ∧
      regularizedLimit Gavg p = diagonalIndentationLift H u (regularizedLimit F) p) := by
  intro V F g Gavg
  obtain ⟨C, hC, hDiff⟩ := doublingSequence_self_difference_bound μ U hU hS hUc
  obtain ⟨hV, hVdiff⟩ := weilQuotientMeasure_doublingSequence H hH μ ν hν U hU hUo hUi hDiff
  obtain ⟨hGloc, hFmeas, hlim⟩ := diagonalIndentation_ae_average H hH μ ν hν u hp hn U
    hU.one_mem hU.decreasing hUo hUi hUc hUcof f hf _ (fun _ => rfl) hV hC hVdiff
  have hGmeas (n : ℕ) : Measurable (Gavg n) := by
    letI : (μ.prod μ).Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _
    have hu : IsCompact (closure (U n)) :=
      hUc.of_isClosed_subset isClosed_closure (closure_mono (hU.decreasing (Nat.zero_le n)))
    have hc : IsCompact (closure (U n ×ˢ U n)) := by rw [closure_prod_eq]; exact hu.prod hu
    exact (continuous_normalized_translateAverage (μ.prod μ)
      ((hUo n).prod (hUo n)).measurableSet hc hGloc).measurable
  refine ⟨hGloc, hFmeas, hFmeas.comp (measurable_id.prodMk measurable_id),
    regularizedLimit_measurable hGmeas, ?_⟩
  filter_upwards [hlim] with p hp'
  exact ⟨hp'.1, hp'.2, regularizedLimit_tendsto hp'.2⟩

end
end Masullo
