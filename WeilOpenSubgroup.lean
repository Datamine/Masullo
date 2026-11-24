import WeilSigmaCompactLocalization
import Mathlib.Topology.Algebra.Support
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Maps.Proper.CompactlyGenerated

open Filter Function MeasureTheory Set Topology

namespace Masullo

noncomputable section

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]

variable (H J : Subgroup G)

private abbrev smallFiber := H.comap J.subtype

private def smallFiberInclusion : smallFiber H J →* H :=
  { toFun := fun x => ⟨x.val.val, x.property⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }

private theorem smallFiberInclusion_range :
    range (smallFiberInclusion H J) = (Subtype.val : H → G) ⁻¹' (J : Set G) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact y.val.property
  · intro hx
    exact ⟨⟨⟨x.val, hx⟩, x.property⟩, rfl⟩

private theorem smallFiberInclusion_openEmbedding (hJ : IsOpen (J : Set G)) :
    IsOpenEmbedding (smallFiberInclusion H J) := by
  have he : IsEmbedding (smallFiberInclusion H J) := by
    apply (IsEmbedding.subtypeVal (p := fun x : G => x ∈ H)).of_comp_iff.mp
    change IsEmbedding (fun x : smallFiber H J => x.val.val)
    exact IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal
  refine ⟨he, ?_⟩
  rw [smallFiberInclusion_range]
  exact hJ.preimage continuous_subtype_val

private def smallQuotientInclusion : (J ⧸ smallFiber H J) →* (G ⧸ H) :=
  QuotientGroup.map _ _ J.subtype (le_refl _)

private theorem smallQuotientInclusion_openEmbedding (hJ : IsOpen (J : Set G)) :
    IsOpenEmbedding (smallQuotientInclusion H J) := by
  let i := smallQuotientInclusion H J
  have hc : Continuous i := QuotientGroup.isOpenQuotientMap_mk.continuous_comp_iff.mp
    (QuotientGroup.continuous_mk.comp continuous_subtype_val)
  have ho : IsOpenMap i := IsOpenMap.of_comp QuotientGroup.continuous_mk
    QuotientGroup.mk_surjective (QuotientGroup.isOpenQuotientMap_mk.isOpenMap.comp
      hJ.isOpenEmbedding_subtypeVal.isOpenMap)
  have hi : Injective i := by
    rw [injective_iff_map_eq_one]
    intro x hx
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    apply (QuotientGroup.eq_one_iff (N := smallFiber H J) g).mpr
    exact (QuotientGroup.eq_one_iff (N := H) g.val).mp hx
  exact IsOpenEmbedding.of_continuous_injective_isOpenMap hc hi ho

private theorem mem_smallQuotientInclusion_iff (q : G ⧸ H) :
    q ∈ range (smallQuotientInclusion H J) ↔ ∃ x : J, QuotientGroup.mk x.val = q := by
  constructor
  · rintro ⟨j, rfl⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective j
    exact ⟨x, rfl⟩
  · rintro ⟨x, rfl⟩
    exact ⟨QuotientGroup.mk x, rfl⟩

variable (hH : IsClosed (H : Set G))

include hH in
private theorem smallFiber_closed : IsClosed (smallFiber H J : Set J) :=
  hH.preimage continuous_subtype_val

private lemma comap_integrable_iff {X Y E : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [NormedAddCommGroup E] {i : X → Y} {μ : Measure Y} (hi : MeasurableEmbedding i) {f : Y → E} :
    Integrable (f ∘ i) (μ.comap i) ↔ IntegrableOn f (range i) μ := by
  rw [IntegrableOn, ← hi.map_comap]
  exact hi.integrable_map_iff.symm

private lemma comap_integral {X Y E : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {i : X → Y} {μ : Measure Y}
    (hi : MeasurableEmbedding i) (f : Y → E) :
    (∫ x, f (i x) ∂μ.comap i) = ∫ y in range i, f y ∂μ := by
  rw [← hi.map_comap, hi.integral_map]

private lemma integrableOn_iff_of_zero_outside {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] {μ : Measure X} {S : Set X} (hS : MeasurableSet S) {f : X → E}
    (hf : ∀ x ∉ S, f x = 0) : IntegrableOn f S μ ↔ Integrable f μ := by
  have he : S.indicator f = f := by
    ext x
    by_cases hx : x ∈ S <;> simp [hx, hf]
  rw [← integrable_indicator_iff hS, he]

private lemma integral_eq_setIntegral_of_zero_outside {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {μ : Measure X} {S : Set X}
    (hS : MeasurableSet S) {f : X → E} (hf : ∀ x ∉ S, f x = 0) :
    (∫ x, f x ∂μ) = ∫ x in S, f x ∂μ := by
  have he : S.indicator f = f := by
    ext x
    by_cases hx : x ∈ S <;> simp [hx, hf]
  rw [← integral_indicator hS, he]

local instance : MeasurableSpace (G ⧸ H) := borel _
local instance : MeasurableSpace (J ⧸ smallFiber H J) := borel _

private theorem lcaCosetIntegral_zero_outside_smallQuotient
    {f : G → ℂ} (hf : ∀ x ∉ (J : Set G), f x = 0)
    (q : G ⧸ H) (hq : q ∉ range (smallQuotientInclusion H J)) :
    (fun h : H => f (q.out * (h : G))) = 0 := by
  funext h
  apply hf
  intro hm
  apply hq
  apply (mem_smallQuotientInclusion_iff H J q).mpr
  refine ⟨⟨q.out * (h : G), hm⟩, ?_⟩
  change (QuotientGroup.mk' H) (q.out * (h : G)) = q
  have he : (QuotientGroup.mk' H) (h : G) = 1 :=
    (QuotientGroup.eq_one_iff (N := H) h.val).mpr h.property
  rw [map_mul, he, mul_one]
  exact Quotient.out_eq' q

private theorem smallFiber_vanishes {f : G → ℂ} (hf : ∀ x ∉ (J : Set G), f x = 0)
    (x : J) (h : H) (hh : h ∉ range (smallFiberInclusion H J)) :
    f (x.val * h.val) = 0 := by
  apply hf
  intro hm
  apply hh
  rw [smallFiberInclusion_range]
  exact (J.mul_mem_cancel_left x.property).mp hm

private theorem lcaCosetIntegral_smallQuotient (hJ : IsOpen (J : Set G))
    (μH : Measure H) [μH.IsHaarMeasure] {f : G → ℂ} (hf : ∀ x ∉ (J : Set G), f x = 0)
    (q : J ⧸ smallFiber H J) :
    lcaCosetIntegral (smallFiber H J) (μH.comap (smallFiberInclusion H J)) (f ∘ J.subtype) q =
      lcaCosetIntegral H μH f (smallQuotientInclusion H J q) := by
  letI : LocallyCompactSpace J := hJ.locallyCompactSpace
  letI := Measure.IsHaarMeasure.comap (mH := inferInstance) μH (smallFiberInclusion_openEmbedding H J hJ)
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  change lcaCosetIntegral _ _ _ (QuotientGroup.mk x) =
    lcaCosetIntegral _ _ _ (QuotientGroup.mk x.val)
  rw [lcaCosetIntegral_mk, lcaCosetIntegral_mk]
  let hi := (smallFiberInclusion_openEmbedding H J hJ).measurableEmbedding
  calc
    (∫ h : smallFiber H J, (f ∘ J.subtype) (x * (h : J)) ∂μH.comap (smallFiberInclusion H J)) =
        ∫ h in range (smallFiberInclusion H J), f (x.val * (h : H).val) ∂μH :=
      comap_integral hi (fun y : H => f (x.val * y.val))
    _ = ∫ h : H, f (x.val * h.val) ∂μH :=
      (integral_eq_setIntegral_of_zero_outside hi.measurableSet_range
        (smallFiber_vanishes H J hf x)).symm

private theorem lcaCosetIntegrable_smallQuotient (hJ : IsOpen (J : Set G))
    (μH : Measure H) [μH.IsHaarMeasure] {f : G → ℂ} (hf : ∀ x ∉ (J : Set G), f x = 0)
    (q : J ⧸ smallFiber H J) :
    Integrable (fun h : smallFiber H J => f ((q.out * (h : J) : J) : G))
        (μH.comap (smallFiberInclusion H J)) ↔
      Integrable (fun h : H => f ((smallQuotientInclusion H J q).out * (h : G))) μH := by
  letI : LocallyCompactSpace J := hJ.locallyCompactSpace
  letI := Measure.IsHaarMeasure.comap (mH := inferInstance) μH (smallFiberInclusion_openEmbedding H J hJ)
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  change Integrable (fun h : smallFiber H J => (f ∘ J.subtype)
      ((QuotientGroup.mk x : J ⧸ smallFiber H J).out * (h : J))) _ ↔
    Integrable (fun h : H => f ((QuotientGroup.mk x.val : G ⧸ H).out * (h : G))) μH
  rw [lcaCosetIntegrable_mk, lcaCosetIntegrable_mk]
  let hi := (smallFiberInclusion_openEmbedding H J hJ).measurableEmbedding
  change Integrable ((fun h : H => f (x.val * h.val)) ∘ smallFiberInclusion H J) _ ↔ _
  rw [comap_integrable_iff hi]
  exact integrableOn_iff_of_zero_outside hi.measurableSet_range (smallFiber_vanishes H J hf x)

private theorem smallWeilMeasure (hJ : IsOpen (J : Set G)) (μ : Measure G)
    (μH : Measure H) [μH.IsHaarMeasure] (ν : Measure (G ⧸ H))
    (hν : IsWeilQuotientMeasure H μ μH ν) :
    IsWeilQuotientMeasure (smallFiber H J) (μ.comap J.subtype)
      (μH.comap (smallFiberInclusion H J)) (ν.comap (smallQuotientInclusion H J)) := by
  letI : BorelSpace (G ⧸ H) := ⟨rfl⟩
  letI : BorelSpace (J ⧸ smallFiber H J) := ⟨rfl⟩
  letI := hν.1
  letI := hν.2.1
  let hi := smallQuotientInclusion_openEmbedding H J hJ
  refine ⟨Measure.IsHaarMeasure.comap (mH := inferInstance) ν hi, Measure.Regular.comap' ν hi, ?_⟩
  intro f hf
  let g : C(G, ℂ) := ⟨Function.extend (Subtype.val : J → G) f 0,
    HasCompactSupport.continuous_extend_zero hJ f.continuous hf⟩
  have hg : HasCompactSupport g := hf.extend_zero continuous_subtype_val
  have hgJ : ∀ x ∉ (J : Set G), g x = 0 := by
    intro x hx
    change Function.extend (Subtype.val : J → G) f 0 x = 0
    exact Function.extend_apply' _ _ _ (fun ⟨y, hy⟩ => hx (hy ▸ y.property))
  have he : (g : G → ℂ) ∘ J.subtype = f := funext fun x =>
    Function.Injective.extend_apply Subtype.val_injective _ _ x
  have hleft : (∫ x : J, f x ∂μ.comap J.subtype) = ∫ x, g x ∂μ := by
    calc
      _ = ∫ x : J, g (J.subtype x) ∂μ.comap J.subtype := by
        simp only [show (fun x : J => g (J.subtype x)) = f from he]
      _ = ∫ x in (J : Set G), g x ∂μ := integral_subtype_comap hJ.measurableSet g
      _ = _ := (integral_eq_setIntegral_of_zero_outside hJ.measurableSet hgJ).symm
  rw [hleft, hν.2.2 g hg]
  have hfib (q : J ⧸ smallFiber H J) :
      lcaCosetIntegral (smallFiber H J) (μH.comap (smallFiberInclusion H J)) (f : J → ℂ) q =
        lcaCosetIntegral H μH g (smallQuotientInclusion H J q) := by
    rw [← he]
    exact lcaCosetIntegral_smallQuotient H J hJ μH hgJ q
  simp_rw [hfib]
  rw [comap_integral hi.measurableEmbedding (lcaCosetIntegral H μH g)]
  apply integral_eq_setIntegral_of_zero_outside hi.measurableEmbedding.measurableSet_range
  intro q hq
  rw [lcaCosetIntegral, lcaCosetIntegral_zero_outside_smallQuotient H J hgJ q hq]
  exact integral_zero _ _

/-- The quotient of an open subgroup by its intersection with the fibres
embeds as an open subgroup of the full quotient. -/
theorem openSubgroup_quotientMap_openEmbedding (hJ : IsOpen (J : Set G))
    (K : Subgroup J) (hK : K = H.comap J.subtype) :
    IsOpenEmbedding (QuotientGroup.map K H J.subtype hK.le) := by
  subst K
  exact smallQuotientInclusion_openEmbedding H J hJ

/-- The Weil normalization restricts to the open subgroup quotient if the
ambient and fibre Haar measures are restricted along the inclusions. -/
theorem isWeilQuotientMeasure_comap_openSubgroup
    (hJ : IsOpen (J : Set G)) (μ : Measure G)
    (μH : Measure H) [μH.IsHaarMeasure] (ν : Measure (G ⧸ H))
    (hν : IsWeilQuotientMeasure H μ μH ν) :
    IsWeilQuotientMeasure (H.comap J.subtype) (μ.comap J.subtype)
      (μH.comap (fun x : H.comap J.subtype => (⟨x.val.val, x.property⟩ : H)))
      (ν.comap (QuotientGroup.map (H.comap J.subtype) H J.subtype le_rfl)) :=
  smallWeilMeasure H J hJ μ μH ν hν

/-- If the fibre Haar normalization is counting measure, its restriction
still counts every element once. The smaller quotient can be presented
using any equal subgroup of the open ambient subgroup. -/
theorem isWeilQuotientMeasure_count_comap_openSubgroup
    (hJ : IsOpen (J : Set G)) (K : Subgroup J) (hK : K = H.comap J.subtype)
    (μ : Measure G) [(Measure.count : Measure H).IsHaarMeasure] (ν : Measure (G ⧸ H))
    (hν : IsWeilQuotientMeasure H μ Measure.count ν) :
    IsWeilQuotientMeasure K (μ.comap J.subtype) Measure.count
      (ν.comap (QuotientGroup.map K H J.subtype hK.le)) := by
  subst K
  have hi := (smallFiberInclusion_openEmbedding H J hJ).measurableEmbedding
  have hcount : (Measure.count : Measure H).comap (smallFiberInclusion H J) =
      (Measure.count : Measure (smallFiber H J)) := by
    ext s hms
    rw [Measure.comap_apply _ hi.injective
      (fun _ ht => hi.measurableSet_image.mpr ht) _ hms, Measure.count_apply hms,
      Measure.count_apply (hi.measurableSet_image.mpr hms), hi.injective.encard_image]
  have h := smallWeilMeasure H J hJ μ Measure.count ν hν
  rw [hcount] at h
  exact h


include hH in
/-- Weil's formula for integrable functions on an arbitrary locally compact
Hausdorff abelian group with regular Haar measure. -/
theorem weilQuotientIntegral_L1 (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]
    (μH : Measure H) [μH.IsHaarMeasure] [μH.Regular] (ν : Measure (G ⧸ H))
    (hν : IsWeilQuotientMeasure H μ μH ν) {f : G → ℂ} (hf : Integrable f μ) :
    (∀ᵐ q ∂ν, Integrable (fun h : H => f (q.out * (h : G))) μH) ∧
      Integrable (lcaCosetIntegral H μH f) ν ∧
      (∫ x, f x ∂μ) = ∫ q, lcaCosetIntegral H μH f q ∂ν := by
  obtain ⟨J, hJ, hJσ, hJf⟩ := exists_open_sigmaCompact_subgroup_of_integrable μ hf
  have hfzero : ∀ x ∉ (J : Set G), f x = 0 := by
    intro x hx
    by_contra hn
    exact hx (hJf hn)
  letI : BorelSpace (G ⧸ H) := ⟨rfl⟩
  letI : BorelSpace (J ⧸ smallFiber H J) := ⟨rfl⟩
  letI : LocallyCompactSpace J := hJ.locallyCompactSpace
  letI : SigmaCompactSpace J := isSigmaCompact_iff_sigmaCompactSpace.mp hJσ
  let hji := hJ.isOpenEmbedding_subtypeVal
  let hhi := smallFiberInclusion_openEmbedding H J hJ
  let hqi := smallQuotientInclusion_openEmbedding H J hJ
  let μJ := μ.comap J.subtype
  let μHJ := μH.comap (smallFiberInclusion H J)
  let νJ := ν.comap (smallQuotientInclusion H J)
  letI : μJ.IsHaarMeasure := Measure.IsHaarMeasure.comap (mH := inferInstance) μ hji
  letI : μJ.Regular := Measure.Regular.comap' μ hji
  letI : μHJ.IsHaarMeasure := Measure.IsHaarMeasure.comap (mH := inferInstance) μH hhi
  letI : μHJ.Regular := Measure.Regular.comap' μH hhi
  letI : SigmaFinite μJ := inferInstance
  have hfJ : Integrable (f ∘ J.subtype) μJ :=
    (comap_integrable_iff hji.measurableEmbedding).mpr (hf.integrableOn)
  obtain ⟨hae, hint, he⟩ := weilQuotientIntegral_L1_sigmaFinite (smallFiber H J)
    (smallFiber_closed H J hH) μJ μHJ νJ (smallWeilMeasure H J hJ μ μH ν hν) hfJ
  have hinJ (q : J ⧸ smallFiber H J) :=
    lcaCosetIntegral_smallQuotient H J hJ μH hfzero q
  have hout (q : G ⧸ H) (hq : q ∉ range (smallQuotientInclusion H J)) :
      lcaCosetIntegral H μH f q = 0 := by
    rw [lcaCosetIntegral, lcaCosetIntegral_zero_outside_smallQuotient H J hfzero q hq]
    exact integral_zero _ _
  have hintComp : Integrable (lcaCosetIntegral H μH f ∘ smallQuotientInclusion H J) νJ := by
    rw [← show lcaCosetIntegral _ _ _ = lcaCosetIntegral H μH f ∘
      smallQuotientInclusion H J from funext hinJ]
    exact hint
  have haeq : ∀ᵐ q ∂νJ,
      Integrable (fun h : H => f ((smallQuotientInclusion H J q).out * (h : G))) μH := by
    filter_upwards [hae] with q hq
    exact (lcaCosetIntegrable_smallQuotient H J hJ μH hfzero q).mp hq
  let hme := hqi.measurableEmbedding
  refine ⟨?_, (integrableOn_iff_of_zero_outside hme.measurableSet_range hout).mp
    ((comap_integrable_iff hme).mp hintComp), ?_⟩
  · have haer := (hme.ae_map_iff (μ := νJ) (p := fun q : G ⧸ H =>
      Integrable (fun h : H => f (q.out * (h : G))) μH)).mpr haeq
    rw [show νJ = ν.comap (smallQuotientInclusion H J) from rfl, hme.map_comap] at haer
    filter_upwards [(ae_restrict_iff' hme.measurableSet_range).mp haer] with q hq
    by_cases hm : q ∈ range (smallQuotientInclusion H J)
    · exact hq hm
    · rw [lcaCosetIntegral_zero_outside_smallQuotient H J hfzero q hm]
      exact integrable_zero H ℂ μH
  · calc
      (∫ x, f x ∂μ) = ∫ x in (J : Set G), f x ∂μ :=
        integral_eq_setIntegral_of_zero_outside hJ.measurableSet hfzero
      _ = ∫ x, (f ∘ J.subtype) x ∂μJ := (integral_subtype_comap hJ.measurableSet f).symm
      _ = ∫ q : J ⧸ smallFiber H J, lcaCosetIntegral H μH f (smallQuotientInclusion H J q) ∂νJ := by
        rw [he]
        exact integral_congr_ae (Filter.Eventually.of_forall hinJ)
      _ = ∫ q in range (smallQuotientInclusion H J), lcaCosetIntegral H μH f q ∂ν :=
        comap_integral hme (lcaCosetIntegral H μH f)
      _ = _ := (integral_eq_setIntegral_of_zero_outside hme.measurableSet_range hout).symm


include hH in
/-- Corrected scalar Weil theorem, C.4.4.3 and D.1.2.1. The normalization
is fixed on continuous compactly supported tests, and the fibre assertion
for integrable functions uses the quotient measure. -/
theorem weilQuotientMeasure_existsUnique_L1 (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]
    (μH : Measure H) [μH.IsHaarMeasure] [μH.Regular] :
    ∃! ν : Measure (G ⧸ H), IsWeilQuotientMeasure H μ μH ν ∧
      ∀ f : G → ℂ, Integrable f μ →
        (∀ᵐ q ∂ν, Integrable (fun h : H => f (q.out * (h : G))) μH) ∧
        Integrable (lcaCosetIntegral H μH f) ν ∧
        (∫ x, f x ∂μ) = ∫ q, lcaCosetIntegral H μH f q ∂ν := by
  obtain ⟨ν, hν, hu⟩ := weilQuotientMeasure_existsUnique H hH μ μH
  refine ⟨ν, ⟨hν, fun _ hf => weilQuotientIntegral_L1 H hH μ μH ν hν hf⟩, ?_⟩
  intro ρ hρ
  exact hu ρ hρ.1

set_option maxHeartbeats 900000 in
/-- Haar integration over a closed subgroup, for a test supported on an open
subgroup and pulled back through a proper map of that open subgroup.
The image fibre carries the pushforward of Haar restricted to the intersection. -/
theorem exists_haar_imageFiber_integral {A : Type*} [CommGroup A] [TopologicalSpace A]
    [IsTopologicalGroup A] [T2Space A] [LocallyCompactSpace A] [MeasurableSpace A] [BorelSpace A]
    (hH : IsClosed (H : Set G)) (hJ : IsOpen (J : Set G)) (π : J →ₜ* A)
    (hπ : IsProperMap π) (μH : Measure H) [μH.IsHaarMeasure]
    (L : Subgroup A) (hL : L = (H.comap J.subtype).map π.toMonoidHom) :
    ∃ ν : Measure L, ν.IsHaarMeasure ∧ IsClosed (L : Set A) ∧
      ∀ {f : G → ℂ} {g : A → ℂ}, Continuous g →
        (∀ x ∉ (J : Set G), f x = 0) → (∀ x : J, f x.val = g (π x)) →
        ∀ x : J,
          (Integrable (fun h : H => f (x.val * h.val)) μH ↔
            Integrable (fun z : L => g (π x * z.val)) ν) ∧
          (∫ h : H, f (x.val * h.val) ∂μH) = ∫ z : L, g (π x * z.val) ∂ν := by
  subst L
  let L := (H.comap J.subtype).map π.toMonoidHom
  let I := H.comap J.subtype
  have hi : IsClosed (I : Set J) := hH.preimage continuous_subtype_val
  have hL : IsClosed (L : Set A) := hπ.isClosedMap _ hi
  letI : LocallyCompactSpace L := hL.isClosedEmbedding_subtypeVal.locallyCompactSpace
  let j : I →* H := smallFiberInclusion H J
  have he : IsOpenEmbedding j := smallFiberInclusion_openEmbedding H J hJ
  let w := μH.comap j
  letI : w.IsHaarMeasure :=
    Measure.IsHaarMeasure.comap (mH := ContinuousMul.measurableMul) μH he
  let ρ : I →* L := (π.toMonoidHom.comp I.subtype).codRestrict L
    (fun x => ⟨x.val, x.property, rfl⟩)
  have hc : Continuous ρ := (π.continuous.comp continuous_subtype_val).subtype_mk _
  have hs : Surjective ρ := by
    rintro ⟨_, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  have hp : IsProperMap ρ := by
    refine isProperMap_iff_isCompact_preimage.mpr ⟨hc, fun S hS => ?_⟩
    have hk := (hπ.comp hi.isClosedEmbedding_subtypeVal.isProperMap).isCompact_preimage
      (hS.image continuous_subtype_val)
    suffices heq : ((π ∘ (Subtype.val : I → J)) ⁻¹' (Subtype.val '' S)) = ρ ⁻¹' S from heq ▸ hk
    ext x
    constructor
    · rintro ⟨y, hy, hxy⟩
      change ρ x ∈ S
      rwa [← (Subtype.ext hxy : y = ρ x)]
    · intro hx
      exact ⟨ρ x, hx, rfl⟩
  let ν := w.map ρ
  letI : LocallyCompactSpace H := hH.isClosedEmbedding_subtypeVal.locallyCompactSpace
  letI : LocallyCompactSpace I := he.locallyCompactSpace
  have hν : ν.IsHaarMeasure := Measure.isHaarMeasure_map w ρ hc hs
    (isProperMap_iff_tendsto_cocompact.mp hp).2
  refine ⟨ν, hν, hL, fun {f g} hg hf hfπ x => ?_⟩
  let F (h : H) := f (x.val * h.val)
  let T (z : L) := g (π x * z.val)
  have hT : Continuous T := hg.comp (continuous_const.mul continuous_subtype_val)
  have hzero (h : H) (hh : h ∉ range j) : F h = 0 :=
    smallFiber_vanishes H J hf x h hh
  have hcomp : F ∘ j = T ∘ ρ := by
    funext z
    change f (x * z.val : J).val = g (π x * π z.val)
    rw [hfπ, map_mul]
  constructor
  · change Integrable F μH ↔ Integrable T (w.map ρ)
    rw [integrable_map_measure hT.aestronglyMeasurable hc.aemeasurable, ← hcomp,
      comap_integrable_iff he.measurableEmbedding]
    exact (integrableOn_iff_of_zero_outside he.measurableEmbedding.measurableSet_range hzero).symm
  · calc
      _ = ∫ h in range j, F h ∂μH :=
        (setIntegral_eq_integral_of_forall_compl_eq_zero hzero).symm
      _ = ∫ z : I, F (j z) ∂w := (comap_integral he.measurableEmbedding F).symm
      _ = ∫ z : I, T (ρ z) ∂w := congrArg (fun u : I → ℂ => ∫ z, u z ∂w) hcomp
      _ = _ := (integral_map hc.aemeasurable hT.aestronglyMeasurable).symm

end
end Masullo
