import DiagonalQuotientCutoff
import QuotientLiftedMeasure
import MeasureFoundations

open Filter Function MeasureTheory Set Topology
open scoped ENNReal Pointwise

namespace Masullo

noncomputable section

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
variable (H : Subgroup G) (hH : IsClosed (H : Set G)) [DiscreteTopology H]

local instance : MeasurableSpace (G ⧸ H) := borel _
local instance : BorelSpace (G ⧸ H) := ⟨rfl⟩

private abbrev q := (QuotientGroup.mk : G → G ⧸ H)

include hH in
/-- On a measurable slice where the quotient map is injective, the counting
fibres give exactly the restricted quotient measure. -/
theorem quotientLiftedMeasure_injective_slice (ν : Measure (G ⧸ H))
    {D : Set G} (hD : MeasurableSet D) (hImage : MeasurableSet (q H '' D))
    (hi : InjOn (q H) D) :
    ((quotientLiftedMeasure H Measure.count ν).restrict D).map (q H) =
      ν.restrict (q H '' D) := by
  letI : (Measure.count : Measure H).IsHaarMeasure := subgroup_count_isHaarMeasure H
  letI : LocallyCompactSpace H := hH.locallyCompactSpace
  letI : SecondCountableTopology H := TopologicalSpace.Subtype.secondCountableTopology (H : Set G)
  letI : Measure.Regular (Measure.count : Measure H) :=
    Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _
  have hq : Measurable (q H) := QuotientGroup.continuous_mk.measurable
  have hk := quotientCosetMeasure_measurable H hH (Measure.count : Measure H)
  ext A hA
  rw [Measure.map_apply hq hA, Measure.restrict_apply (hA.preimage hq),
    quotientLiftedMeasure, Measure.bind_apply ((hA.preimage hq).inter hD) hk.aemeasurable,
    Measure.restrict_apply hA, ← lintegral_indicator_one (hA.inter hImage)]
  apply lintegral_congr
  intro c
  let t : H → G := fun a => c.out * (a : G)
  have ht : Measurable t := (continuous_const.mul continuous_subtype_val).measurable
  have htc (a : H) : q H (t a) = c := by
    change QuotientGroup.mk (c.out * (a : G)) = c
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).mpr a.property, mul_one]
    exact Quotient.out_eq' c
  change Measure.count.map t (q H ⁻¹' A ∩ D) = (A ∩ q H '' D).indicator 1 c
  rw [Measure.map_apply ht ((hA.preimage hq).inter hD)]
  by_cases hc : c ∈ A ∩ q H '' D
  · obtain ⟨d, hd, hdc⟩ := hc.2
    have hmem : c.out⁻¹ * d ∈ H := QuotientGroup.eq.mp ((Quotient.out_eq' c).trans hdc.symm)
    let a : H := ⟨c.out⁻¹ * d, hmem⟩
    have ha : t a = d := by simp [t, a]
    have hsing : t ⁻¹' (q H ⁻¹' A ∩ D) = {a} := by
      ext b
      constructor
      · intro hb'
        apply mem_singleton_iff.mpr
        apply Subtype.ext
        have htb : t b = t a := hi hb'.2 (ha.symm ▸ hd) ((htc b).trans (htc a).symm)
        exact mul_left_cancel htb
      · intro hba
        subst b
        refine ⟨?_, ha.symm ▸ hd⟩
        change q H (t a) ∈ A
        rw [htc a]
        exact hc.1
    simp [hsing, hc]
  · have hnull : t ⁻¹' (q H ⁻¹' A ∩ D) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro a ha
      apply hc
      refine ⟨?_, ⟨t a, ha.2, htc a⟩⟩
      exact (htc a) ▸ ha.1
    simp [hnull, hc]

include hH in
/-- A Borel transversal carries the full quotient measure via restriction
of the lift whose fibre measures are counting measures. -/
theorem quotientLiftedMeasure_transversal (ν : Measure (G ⧸ H))
    {D : Set G} (hD : MeasurableSet D) (hb : BijOn (q H) D univ) :
    ((quotientLiftedMeasure H Measure.count ν).restrict D).map (q H) = ν := by
  have hi : MeasurableSet (q H '' D) := hb.image_eq.symm ▸ MeasurableSet.univ
  rw [quotientLiftedMeasure_injective_slice H hH ν hD hi hb.injOn, hb.image_eq, Measure.restrict_univ]

include hH in
/-- The counting-fibre lift of the Haar quotient measure recovers Haar
measure upstairs with its original normalization. -/
theorem weilQuotientMeasure_lift_eq (μG : Measure G) [μG.IsHaarMeasure] [μG.Regular]
    [SigmaFinite μG] (ν : Measure (G ⧸ H))
    (hν : IsWeilQuotientMeasure H μG Measure.count ν) :
    quotientLiftedMeasure H Measure.count ν = μG := by
  letI : (Measure.count : Measure H).IsHaarMeasure := subgroup_count_isHaarMeasure H
  letI : LocallyCompactSpace H := hH.locallyCompactSpace
  letI : SecondCountableTopology H := TopologicalSpace.Subtype.secondCountableTopology (H : Set G)
  letI : Measure.Regular (Measure.count : Measure H) :=
    Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _
  exact (weilMeasure_eq_bind H hH μG Measure.count ν hν).2

include hH in
/-- The transversal identity with the Haar normalization in the manuscript. -/
theorem weilQuotientMeasure_transversal (μG : Measure G) [μG.IsHaarMeasure] [μG.Regular]
    [SigmaFinite μG] (ν : Measure (G ⧸ H))
    (hν : IsWeilQuotientMeasure H μG Measure.count ν)
    {D : Set G} (hD : MeasurableSet D) (hb : BijOn (q H) D univ) :
    (μG.restrict D).map (q H) = ν := by
  rw [← weilQuotientMeasure_lift_eq H hH μG ν hν]
  exact quotientLiftedMeasure_transversal H hH ν hD hb

include hH in
/-- The quotient map on a product of injective open slices preserves the two
restricted product measures, so the unweighted local averages transport exactly. -/
theorem quotientLiftedMeasure_preserving_productSlices (ν : Measure (G ⧸ H))
    [SigmaFinite (quotientLiftedMeasure H Measure.count ν)]
    [SigmaFinite ν] {A B : Set G} (hAo : IsOpen A) (hBo : IsOpen B)
    (hAi : InjOn (q H) A) (hBi : InjOn (q H) B) :
    let ρ := quotientLiftedMeasure H Measure.count ν
    MeasurePreserving (Prod.map (q H) (q H))
      ((ρ.prod ρ).restrict (A ×ˢ B))
      ((ν.prod ν).restrict ((q H '' A) ×ˢ (q H '' B))) := by
  intro ρ
  have hq : Measurable (q H) := QuotientGroup.continuous_mk.measurable
  have hA := quotientLiftedMeasure_injective_slice H hH ν hAo.measurableSet
    (QuotientGroup.isOpenMap_coe _ hAo).measurableSet hAi
  have hB := quotientLiftedMeasure_injective_slice H hH ν hBo.measurableSet
    (QuotientGroup.isOpenMap_coe _ hBo).measurableSet hBi
  refine ⟨hq.prodMap hq, ?_⟩
  rw [← Measure.prod_restrict, ← Measure.prod_restrict, ← Measure.map_prod_map _ _ hq hq, hA, hB]

include hH in
/-- The diagonal trace integral is unchanged by the normalized diagonal
indentation. The formula holds on any transversal carrying the quotient
measure, for every integrable representative of the diagonal trace. -/
theorem diagonalIndentation_trace_integral (u : C(G, ℝ))
    (hp : ∀ L : Set (G ⧸ H), IsCompact L → IsCompact (tsupport u ∩ q H ⁻¹' L))
    (hpos : ∀ x, 0 ≤ u x)
    (hn : ∀ x : G, (∫ h : H, u ((h : G)⁻¹ * x) ∂Measure.count) = 1)
    (η : Measure G) [SigmaFinite η] (ν : Measure (G ⧸ H))
    (he : η.map (q H) = ν) (w : G ⧸ H → ℂ) (hw : Integrable w ν) :
    let f (x : G) (h : H) :=
      (diagonalIndentation H u x ((h : G)⁻¹ * x) : ℂ) * w (q H x)
    Integrable (uncurry f) (η.prod Measure.count) ∧
      (∫ x, ∫ h : H, f x h ∂Measure.count ∂η) = ∫ c, w c ∂ν ∧
      (∫ h : H, ∫ x, f x h ∂η ∂Measure.count) = ∫ c, w c ∂ν := by
  intro f
  letI : SecondCountableTopology H := TopologicalSpace.Subtype.secondCountableTopology (H : Set G)
  letI : Countable H := countable_of_Lindelof_of_discrete
  have hdiag := diagonalIndentation_continuous H hH u hp hpos
  have hq : Measurable (q H) := QuotientGroup.continuous_mk.measurable
  have hwq : Integrable (w ∘ q H) η := by
    apply (integrable_map_measure (μ := η) ?_ hq.aemeasurable).mp
    · exact he.symm ▸ hw
    · exact he.symm ▸ hw.aestronglyMeasurable
  have hfn (x : G) : Integrable (f x) Measure.count :=
    (diagonalIndentation_integral H hH u hp hn x x).1.ofReal.mul_const _
  have hnm (x : G) : (∫ h : H, ‖f x h‖ ∂Measure.count) = ‖w (q H x)‖ := by
    have hp' (h : H) : ‖f x h‖ =
        diagonalIndentation H u x ((h : G)⁻¹ * x) * ‖w (q H x)‖ := by
      dsimp [f]
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hdiag.2.2.1 _ _)]
    simp_rw [hp']
    rw [integral_mul_const, (diagonalIndentation_integral H hH u hp hn x x).2, one_mul]
  have hfm : AEStronglyMeasurable (uncurry f) (η.prod Measure.count) := by
    apply AEStronglyMeasurable.mul _ (hwq.aestronglyMeasurable.comp_quasiMeasurePreserving
      Measure.quasiMeasurePreserving_fst)
    exact (Complex.continuous_ofReal.comp (hdiag.2.1.comp
      (continuous_fst.prodMk ((continuous_subtype_val.comp continuous_snd).inv.mul
        continuous_fst)))).aestronglyMeasurable
  have hfi : Integrable (uncurry f) (η.prod Measure.count) :=
    (integrable_prod_iff hfm).mpr ⟨.of_forall hfn, hwq.norm.congr (.of_forall fun x => (hnm x).symm)⟩
  have hv (x : G) : (∫ h : H, f x h ∂Measure.count) = w (q H x) := by
    dsimp [f]
    rw [integral_mul_const, integral_complex_ofReal,
      (diagonalIndentation_integral H hH u hp hn x x).2, Complex.ofReal_one, one_mul]
  have hfirst : (∫ x, ∫ h : H, f x h ∂Measure.count ∂η) = ∫ c, w c ∂ν := by
    simp_rw [hv]
    rw [← he]
    exact (integral_map hq.aemeasurable (he.symm ▸ hw.aestronglyMeasurable)).symm
  exact ⟨hfi, hfirst, (integral_integral_swap hfi).symm.trans hfirst⟩


private theorem average_comp_measurePreserving {X Y E : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m : Measure X} {n : Measure Y} {t : X → Y} (h : MeasurePreserving t m n)
    (w : Y → E) (hw : AEStronglyMeasurable w n) :
    (⨍ z, w (t z) ∂m) = ⨍ z, w z ∂n := by
  have hm : m.real univ = n.real univ := by
    rw [← h.map_eq, measureReal_def, measureReal_def, Measure.map_apply h.measurable
      MeasurableSet.univ, preimage_univ]
  rw [average_eq, average_eq, hm]
  congr 1
  rw [← h.map_eq]
  exact (integral_map h.measurable.aemeasurable (h.map_eq.symm ▸ hw)).symm

include hH in
/-- The local average formula with the diagonal cutoff. The absolute means
are used to control variation of the cutoff on the shrinking slices. -/
theorem diagonalIndentation_average_limit (u : C(G, ℝ))
    (hp : ∀ L : Set (G ⧸ H), IsCompact L → IsCompact (tsupport u ∩ q H ⁻¹' L))
    (hn : ∀ x, 0 ≤ u x)
    (ν : Measure (G ⧸ H)) [SigmaFinite (quotientLiftedMeasure H Measure.count ν)] [SigmaFinite ν]
    (p : G × G) (A B : ℕ → Set G) (hAo : ∀ n, IsOpen (A n)) (hBo : ∀ n, IsOpen (B n))
    (hAi : ∀ n, InjOn (q H) (A n)) (hBi : ∀ n, InjOn (q H) (B n))
    (hsmall : ∀ V ∈ 𝓝 p, ∀ᶠ n in atTop, A n ×ˢ B n ⊆ V)
    (f : (G ⧸ H) × (G ⧸ H) → ℂ)
    (hI : ∀ n, IntegrableOn f ((q H '' A n) ×ˢ (q H '' B n)) (ν.prod ν))
    (a : ℂ)
    (ha : Tendsto (fun n => ⨍ z in (q H '' A n) ×ˢ (q H '' B n), f z ∂ν.prod ν)
      atTop (𝓝 a))
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ᶠ n in atTop,
      (⨍ z in (q H '' A n) ×ˢ (q H '' B n), ‖f z‖ ∂ν.prod ν) ≤ C) :
    let ρ := quotientLiftedMeasure H Measure.count ν
    Tendsto (fun n => ⨍ z in A n ×ˢ B n,
      (diagonalIndentation H u z.1 z.2 : ℂ) * f (q H z.1, q H z.2) ∂ρ.prod ρ)
      atTop (𝓝 ((diagonalIndentation H u p.1 p.2 : ℂ) * a)) := by
  intro ρ
  let t (z : G × G) := (q H z.1, q H z.2)
  let g := f ∘ t
  let φ (z : G × G) : ℂ := diagonalIndentation H u z.1 z.2
  have hφ : Continuous φ :=
    Complex.continuous_ofReal.comp (diagonalIndentation_continuous H hH u hp hn).2.1
  have hpres (n : ℕ) :
      MeasurePreserving t ((ρ.prod ρ).restrict (A n ×ˢ B n))
        ((ν.prod ν).restrict ((q H '' A n) ×ˢ (q H '' B n))) :=
    quotientLiftedMeasure_preserving_productSlices H hH ν (hAo n) (hBo n) (hAi n) (hBi n)
  have hAvg {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
      (w : (G ⧸ H) × (G ⧸ H) → E) (n : ℕ)
      (hw : AEStronglyMeasurable w ((ν.prod ν).restrict ((q H '' A n) ×ˢ (q H '' B n)))) :
      (⨍ z in A n ×ˢ B n, w (t z) ∂ρ.prod ρ) =
        ⨍ z in (q H '' A n) ×ˢ (q H '' B n), w z ∂ν.prod ν := by
    exact average_comp_measurePreserving (hpres n) w hw
  have hi (n : ℕ) : IntegrableOn g (A n ×ˢ B n) (ρ.prod ρ) :=
    (hpres n).integrable_comp_of_integrable (hI n)
  have hag : Tendsto (fun n => ⨍ z in A n ×ˢ B n, g z ∂ρ.prod ρ) atTop (𝓝 a) :=
    ha.congr fun n => (hAvg f n (hI n).aestronglyMeasurable).symm
  have hbg : ∀ᶠ n in atTop, (⨍ z in A n ×ˢ B n, ‖g z‖ ∂ρ.prod ρ) ≤ C := by
    filter_upwards [hbound] with n hn'
    change (⨍ z in A n ×ˢ B n, ‖f (t z)‖ ∂ρ.prod ρ) ≤ C
    rw [hAvg (fun q => ‖f q‖) n (hI n).norm.aestronglyMeasurable]
    exact hn'
  exact tendsto_average_mul_of_average_norm_bounded (ρ.prod ρ)
    (fun n => ((hAo n).measurableSet.prod (hBo n).measurableSet).nullMeasurableSet)
    hsmall hφ (.of_forall hi) hag hC hbg

include hH in
/-- Where the cutoff is nonzero, regularity of the lifted averages implies
regularity of the quotient averages under bounded absolute means. -/
theorem diagonalIndentation_average_converse (u : C(G, ℝ))
    (hp : ∀ L : Set (G ⧸ H), IsCompact L → IsCompact (tsupport u ∩ q H ⁻¹' L))
    (hn : ∀ (x : G), 0 ≤ u x)
    (ν : Measure (G ⧸ H)) [SigmaFinite (quotientLiftedMeasure H Measure.count ν)] [SigmaFinite ν]
    (p : G × G) (hpos : diagonalIndentation H u p.1 p.2 ≠ 0)
    (A B : ℕ → Set G) (hAo : ∀ n, IsOpen (A n)) (hBo : ∀ n, IsOpen (B n))
    (hAi : ∀ n, InjOn (q H) (A n)) (hBi : ∀ n, InjOn (q H) (B n))
    (hsmall : ∀ V ∈ 𝓝 p, ∀ᶠ n in atTop, A n ×ˢ B n ⊆ V)
    (f : (G ⧸ H) × (G ⧸ H) → ℂ)
    (hI : ∀ n, IntegrableOn f ((q H '' A n) ×ˢ (q H '' B n)) (ν.prod ν))
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ᶠ n in atTop,
      (⨍ z in (q H '' A n) ×ˢ (q H '' B n), ‖f z‖ ∂ν.prod ν) ≤ C)
    (b : ℂ)
    (hb : let ρ := quotientLiftedMeasure H Measure.count ν
      Tendsto (fun n => ⨍ z in A n ×ˢ B n,
        (diagonalIndentation H u z.1 z.2 : ℂ) * f (q H z.1, q H z.2) ∂ρ.prod ρ) atTop (𝓝 b)) :
    Tendsto (fun n => ⨍ z in (q H '' A n) ×ˢ (q H '' B n), f z ∂ν.prod ν)
      atTop (𝓝 ((diagonalIndentation H u p.1 p.2 : ℂ)⁻¹ * b)) := by
  let ρ := quotientLiftedMeasure H Measure.count ν
  let t (z : G × G) := (q H z.1, q H z.2)
  let g := f ∘ t
  let φ (z : G × G) : ℂ := diagonalIndentation H u z.1 z.2
  have hφ : Continuous φ :=
    Complex.continuous_ofReal.comp (diagonalIndentation_continuous H hH u hp hn).2.1
  have hpres (n : ℕ) :
      MeasurePreserving t ((ρ.prod ρ).restrict (A n ×ˢ B n))
        ((ν.prod ν).restrict ((q H '' A n) ×ˢ (q H '' B n))) :=
    quotientLiftedMeasure_preserving_productSlices H hH ν (hAo n) (hBo n) (hAi n) (hBi n)
  have hi (n : ℕ) : IntegrableOn g (A n ×ˢ B n) (ρ.prod ρ) :=
    (hpres n).integrable_comp_of_integrable (hI n)
  have hbg : ∀ᶠ n in atTop, (⨍ z in A n ×ˢ B n, ‖g z‖ ∂ρ.prod ρ) ≤ C := by
    filter_upwards [hbound] with n hn'
    change (⨍ z in A n ×ˢ B n, ‖f (t z)‖ ∂ρ.prod ρ) ≤ C
    rw [average_comp_measurePreserving (hpres n) (fun z => ‖f z‖)
      (hI n).norm.aestronglyMeasurable]
    exact hn'
  have hp' : φ p ≠ 0 := Complex.ofReal_ne_zero.mpr hpos
  have ht := tendsto_average_of_tendsto_average_mul (ρ.prod ρ)
    (fun n => ((hAo n).measurableSet.prod (hBo n).measurableSet).nullMeasurableSet)
    hsmall hφ hp' (.of_forall hi) hb hC hbg
  exact ht.congr fun n => average_comp_measurePreserving (hpres n) f (hI n).aestronglyMeasurable

end
end Masullo
