import GlobalIdeleTamagawa
import IdelicNormOneWeilTransport
import SLocalZetaUnfolding
import Mathlib.Topology.Maps.Proper.CompactlyGenerated

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology TopologicalSpace
open scoped Classical ENNReal NNReal NumberField

namespace Masullo

noncomputable section

private theorem compact_covered_by_compact_image
    {X Y : Type*} [TopologicalSpace X] [LocallyCompactSpace X] [TopologicalSpace Y]
    {p : X → Y} (hp : IsOpenQuotientMap p) {K : Set Y} (hK : IsCompact K) :
    ∃ L : Set X, IsCompact L ∧ K ⊆ p '' L := by
  choose C hC hx using fun x : X => exists_compact_mem_nhds x
  have hcov : K ⊆ ⋃ x, p '' interior (C x) := by
    intro y _
    obtain ⟨x, rfl⟩ := hp.surjective y
    exact mem_iUnion.mpr ⟨x, x, mem_interior_iff_mem_nhds.mpr (hx x), rfl⟩
  obtain ⟨T, hT⟩ := hK.elim_finite_subcover (fun x => p '' interior (C x))
    (fun x => hp.isOpenMap _ isOpen_interior) hcov
  refine ⟨⋃ x ∈ T, C x, T.finite_toSet.isCompact_biUnion (fun x _ => hC x), ?_⟩
  intro y hy
  obtain ⟨x, hxT, z, hz, rfl⟩ := mem_iUnion₂.mp (hT hy)
  exact ⟨z, mem_iUnion₂.mpr ⟨x, hxT, interior_subset hz⟩, rfl⟩

variable (F : Type*) [Field F] [NumberField F]

private abbrev Place := HeightOneSpectrum (𝓞 F)
private abbrev Arch := (InfiniteAdeleRing F)ˣ
private abbrev Q := IdeleClass F
private abbrev K := normOneIdeleClass F
private abbrev B (S : Finset (Place F)) := sIdeleBlock F S
private abbrev U (S : Finset (Place F)) := (SAdeles F S)ˣ
private abbrev T (S : Finset (Place F)) := (SIntegralTail F S)ˣ
private abbrev H (S : Finset (Place F)) := (sPrincipal F S).range
private abbrev D (S : Finset (Place F)) := sUnitImage F S

variable (S : Finset (Place F))

local instance tamCompareAdelesSC : SecondCountableTopology (Adeles F) := adeles_secondCountable F
local instance tamCompareAdelesOppSC : SecondCountableTopology (Adeles F)ᵐᵒᵖ :=
  MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
local instance tamCompareIdeleSC : SecondCountableTopology (Idele F) :=
  Units.isEmbedding_embedProduct.secondCountableTopology
local instance tamCompareIdeleLC : LocallyCompactSpace (Idele F) := ideles_locallyCompact
local instance tamCompareIdeleT2 : T2Space (Idele F) := ideles_hausdorff
local instance tamCompareIdeleMeas : MeasurableSpace (Idele F) := borel _
local instance tamCompareIdeleBorel : BorelSpace (Idele F) := ⟨rfl⟩
local instance tamCompareClassMeas : MeasurableSpace (Q F) := borel _
local instance tamCompareClassBorel : BorelSpace (Q F) := ⟨rfl⟩
local instance tamCompareClassT2 : T2Space (Q F) := ideleClasses_hausdorff
local instance tamCompareKMeas : MeasurableSpace (K F) := borel _
local instance tamCompareKBorel : BorelSpace (K F) := ⟨rfl⟩
local instance tamCompareArchMeas : MeasurableSpace (Arch F) := borel _
local instance tamCompareArchBorel : BorelSpace (Arch F) := ⟨rfl⟩
local instance tamCompareCompletionMeas (v : Place F) : MeasurableSpace (v.adicCompletion F) := borel _
local instance tamCompareCompletionBorel (v : Place F) : BorelSpace (v.adicCompletion F) := ⟨rfl⟩
local instance tamCompareLocalMeas (v : Place F) : MeasurableSpace (v.adicCompletion F)ˣ := borel _
local instance tamCompareLocalBorel (v : Place F) : BorelSpace (v.adicCompletion F)ˣ := ⟨rfl⟩
local instance tamCompareBlockBorel : BorelSpace (B F S) :=
  inferInstanceAs (BorelSpace (Subtype _))
local instance tamCompareBlockLC : LocallyCompactSpace (B F S) :=
  (sIdeleBlock_open F S).locallyCompactSpace
local instance tamCompareBlockSC : SecondCountableTopology (B F S) :=
  (sIdeleBlock_open F S).isOpenEmbedding_subtypeVal.isEmbedding.secondCountableTopology
local instance tamCompareSelectedLC : LocallyCompactSpace (U F S) := sLocalIdeles_locallyCompact F S
local instance tamCompareSelectedSC : SecondCountableTopology (U F S) := sLocalIdeles_secondCountable F S
local instance tamCompareSelectedMeas : MeasurableSpace (U F S) := borel _
local instance tamCompareSelectedBorel : BorelSpace (U F S) := ⟨rfl⟩
local instance tamCompareTailCompact : CompactSpace (T F S) := tailUnits_compact F S
local instance tamCompareTailMeas : MeasurableSpace (T F S) := borel _
local instance tamCompareTailBorel : BorelSpace (T F S) := ⟨rfl⟩
local instance tamCompareProductSC : SecondCountableTopology (U F S × T F S) :=
  (sBlockUnitProduct F S).symm.toHomeomorph.isEmbedding.secondCountableTopology
local instance tamCompareTailSC : SecondCountableTopology (T F S) :=
  (isEmbedding_prodMkRight (Y := T F S) (1 : U F S)).secondCountableTopology
local instance tamCompareBlockClassMeas : MeasurableSpace (SIdeleClass F S) := borel _
local instance tamCompareBlockClassBorel : BorelSpace (SIdeleClass F S) := ⟨rfl⟩
local instance tamCompareBlockClassLC : LocallyCompactSpace (SIdeleClass F S) :=
  (sIdeleClassInclusion_openEmbedding F S).locallyCompactSpace
local instance tamCompareBlockClassT2 : T2Space (SIdeleClass F S) :=
  (sIdeleClassInclusion_openEmbedding F S).isEmbedding.t2Space
local instance tamCompareBlockClassSC : SecondCountableTopology (SIdeleClass F S) :=
  (sIdeleClassInclusion_openEmbedding F S).isEmbedding.secondCountableTopology
local instance tamCompareLocalClassMeas : MeasurableSpace (SIdeleQuotient F S) := borel _
local instance tamCompareLocalClassBorel : BorelSpace (SIdeleQuotient F S) := ⟨rfl⟩
local instance tamCompareLocalClassLC : LocallyCompactSpace (SIdeleQuotient F S) :=
  QuotientGroup.isOpenQuotientMap_mk.locallyCompactSpace
local instance tamCompareLocalClassSC : SecondCountableTopology (SIdeleQuotient F S) :=
  TopologicalSpace.Quotient.secondCountableTopology (QuotientGroup.isOpenMap_coe (N := D F S))
local instance tamCompareLocalClassT2 : T2Space (SIdeleQuotient F S) := by
  letI : T1Space (SIdeleQuotient F S) := QuotientGroup.t1Space_iff.mpr (sUnitImage_closed F S)
  exact inferInstance
local instance tamCompareSelectedT2 : T2Space (U F S) :=
  ((sBlockUnitProduct F S).symm.toHomeomorph.isEmbedding.comp
    (isEmbedding_prodMkLeft (X := U F S) (1 : T F S))).t2Space

private abbrev project : B F S →* U F S :=
  (MonoidHom.fst _ _).comp (sBlockUnitProduct F S).toMonoidHom

private theorem preimage_image_localQuotient (L : Set (U F S)) :
    (sIdeleClassToLocal F S) ⁻¹' ((QuotientGroup.mk : U F S → SIdeleQuotient F S) '' L) =
      (fun p : U F S × T F S => (QuotientGroup.mk ((sBlockUnitProduct F S).symm p) :
        SIdeleClass F S)) '' (L ×ˢ univ) := by
  let e := sBlockUnitProduct F S
  ext q
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
  constructor
  · rintro ⟨x, hx, he⟩
    have he' : QuotientGroup.mk x = (QuotientGroup.mk (project F S a) : SIdeleQuotient F S) := he
    have hh : x⁻¹ * project F S a ∈ D F S := QuotientGroup.eq.mp he'
    obtain ⟨u, hu⟩ := hh
    change project F S (sPrincipal F S u) = x⁻¹ * project F S a at hu
    let b := a * (sPrincipal F S u)⁻¹
    have hb : (e b).1 = x := by
      change project F S b = x
      rw [show b = a * (sPrincipal F S u)⁻¹ from rfl, map_mul, map_inv, hu, mul_inv_rev, inv_inv]
      group
    refine ⟨e b, ⟨hb ▸ hx, mem_univ _⟩, ?_⟩
    change QuotientGroup.mk (e.symm (e b)) = _
    rw [e.symm_apply_apply]
    apply QuotientGroup.eq.mpr
    change b⁻¹ * a ∈ H F S
    rw [show b⁻¹ * a = sPrincipal F S u by dsimp [b]; group]
    exact ⟨u, rfl⟩
  · rintro ⟨p, hp, hpa⟩
    refine ⟨p.1, hp.1, ?_⟩
    rw [← hpa, sIdeleClassToLocal_mk]
    change QuotientGroup.mk p.1 = QuotientGroup.mk (e (e.symm p)).1
    rw [e.apply_symm_apply]

/-- Discarding the integral tail is proper on the actual idele class quotient. -/
theorem sIdeleClassToLocal_isProperMap : IsProperMap (sIdeleClassToLocal F S) := by
  apply isProperMap_iff_isCompact_preimage.mpr
  refine ⟨(sIdeleClassToLocal_isOpenQuotientMap F S).continuous, fun C hC => ?_⟩
  obtain ⟨L, hL, hLC⟩ := compact_covered_by_compact_image
    (QuotientGroup.isOpenQuotientMap_mk (N := D F S)) hC
  have hBig : IsCompact ((sIdeleClassToLocal F S) ⁻¹'
      ((QuotientGroup.mk : U F S → SIdeleQuotient F S) '' L)) := by
    rw [preimage_image_localQuotient F S]
    exact (hL.prod isCompact_univ).image
      (QuotientGroup.continuous_mk.comp (sBlockUnitProduct F S).symm.continuous)
  exact hBig.of_isClosed_subset (hC.isClosed.preimage
    (sIdeleClassToLocal_isOpenQuotientMap F S).continuous) (preimage_mono hLC)

private def principalProject : H F S →* D F S :=
  ((project F S).comp (H F S).subtype).codRestrict _ (by
    intro a
    obtain ⟨u, hu⟩ := a.property
    exact ⟨u, congrArg (project F S) hu⟩)

private theorem principalProject_bijective : Bijective (principalProject F S) := by
  constructor
  · intro a b hab
    obtain ⟨u, hu⟩ := a.property
    obtain ⟨v, hv⟩ := b.property
    have he := congrArg (fun x : D F S => (x.val : SAdeles F S)) hab
    change (project F S a.val).val = (project F S b.val).val at he
    rw [← hu, ← hv] at he
    change sAdelesDiagonal F S ((sUnitToField F S u : Fˣ) : F) =
      sAdelesDiagonal F S ((sUnitToField F S v : Fˣ) : F) at he
    have huv : u = v := Units.ext (Subtype.ext ((sAdelesDiagonal_injective F S) he))
    subst v
    exact Subtype.ext (hu.symm.trans hv)
  · intro b
    obtain ⟨u, hu⟩ := b.property
    exact ⟨⟨sPrincipal F S u, u, rfl⟩, Subtype.ext hu⟩

private theorem blockPrincipal_discrete : DiscreteTopology (H F S) := by
  letI : DiscreteTopology (principalIdeles F) := principalIdeles_discrete
  let j : H F S → principalIdeles F := fun x =>
    ⟨x.val.val, by
      obtain ⟨u, hu⟩ := x.property
      exact ⟨sUnitToField F S u, congrArg Subtype.val hu⟩⟩
  have hi : IsEmbedding j := by
    have hval : IsEmbedding (Subtype.val : principalIdeles F → Idele F) := IsEmbedding.subtypeVal
    apply (hval.of_comp_iff (f := j)).mp
    change IsEmbedding ((Subtype.val : B F S → Idele F) ∘ (Subtype.val : H F S → B F S))
    exact IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal
  exact hi.discreteTopology

local instance tamComparePrincipalDiscrete : DiscreteTopology (H F S) := blockPrincipal_discrete F S
local instance tamCompareLocalPrincipalDiscrete : DiscreteTopology (D F S) := sThetaUnitImage_discrete F S
local instance tamComparePrincipalMeasDiscrete : DiscreteMeasurableSpace (H F S) :=
  ⟨fun U => (isOpen_discrete U).measurableSet⟩
local instance tamCompareLocalPrincipalMeasDiscrete : DiscreteMeasurableSpace (D F S) :=
  ⟨fun U => (isOpen_discrete U).measurableSet⟩

set_option maxHeartbeats 1000000 in
local instance tamComparePrincipalHaar : (Measure.count : Measure (H F S)).IsHaarMeasure :=
  subgroup_count_isHaarMeasure (H F S)

set_option maxHeartbeats 1000000 in
local instance tamCompareLocalPrincipalHaar : (Measure.count : Measure (D F S)).IsHaarMeasure :=
  subgroup_count_isHaarMeasure (D F S)

private theorem principalProject_preservesCount :
    MeasurePreserving (principalProject F S) Measure.count Measure.count := by
  have hm : Measurable (⇑(principalProject F S)) := Measurable.of_discrete
  refine ⟨hm, ?_⟩
  ext A hA
  rw [Measure.map_apply hm hA, Measure.count_apply (hm hA), Measure.count_apply hA,
    encard_preimage_of_bijective (principalProject_bijective F S)]

private theorem localCosetIntegral_project (f : U F S → ℂ) (q : SIdeleClass F S) :
    lcaCosetIntegral (H F S) Measure.count (f ∘ project F S) q =
      lcaCosetIntegral (D F S) Measure.count f (sIdeleClassToLocal F S q) := by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
  rw [sIdeleClassToLocal_mk, lcaCosetIntegral_mk, lcaCosetIntegral_mk]
  let e := Equiv.ofBijective (principalProject F S) (principalProject_bijective F S)
  let b : H F S ≃ᵐ D F S := ⟨e, Measurable.of_discrete, Measurable.of_discrete⟩
  have hi : (∫ h : H F S, f (project F S a * (b h).val) ∂Measure.count) =
        ∫ h : D F S, f (project F S a * h.val) ∂Measure.count := by
    calc
      _ = ∫ h : D F S, f (project F S a * h.val) ∂(Measure.count : Measure (H F S)).map b :=
        (b.measurableEmbedding.integral_map _).symm
      _ = _ := by
        exact congrArg (fun m : Measure (D F S) => ∫ h, f (project F S a * h.val) ∂m)
          (principalProject_preservesCount F S).map_eq
  have hb (h : H F S) : (b h).val = project F S h.val := rfl
  simp only [hb] at hi
  change (∫ h : H F S, f (project F S (a * h.val)) ∂Measure.count) =
    ∫ h : D F S, f (project F S a * h.val) ∂Measure.count
  simpa only [map_mul] using hi

theorem integralIdeleTailMass_ne_zero : integralIdeleTailMass F S ≠ 0 := by
  have h := differentPrimeMass_split F S
  change (∏ v : S, differentPrimeMass F v.val) * integralIdeleTailMass F S =
    (NNReal.sqrt ‖discr F‖₊ : ℝ≥0∞)⁻¹ at h
  intro he
  rw [he, mul_zero] at h
  exact (ENNReal.inv_ne_zero.mpr ENNReal.coe_ne_top) h.symm

theorem integralIdeleTailMass_ne_top : integralIdeleTailMass F S ≠ ⊤ := by
  have h := differentPrimeMass_split F S
  change (∏ v : S, differentPrimeMass F v.val) * integralIdeleTailMass F S =
    (NNReal.sqrt ‖discr F‖₊ : ℝ≥0∞)⁻¹ at h
  have hprod : (∏ v : S, differentPrimeMass F v.val) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun v _ => differentPrimeMass_ne_zero F v.val
  intro he
  rw [he, ENNReal.mul_top hprod] at h
  exact (ENNReal.inv_ne_top.mpr (by simpa using discr_ne_zero F)) h.symm

/-- Integrate out the integral tail in the global Weil quotient. The
projected local quotient uses the selected Haar measure scaled by the
mass of the omitted factors. -/
theorem globalIdeleTamagawa_map_localQuotient_isWeil (ν : Measure (Q F))
    (hν : IsWeilQuotientMeasure (principalIdeles F) (globalIdeleTamagawa F) Measure.count ν) :
    IsWeilQuotientMeasure (D F S)
      (integralIdeleTailMass F S • sLocalMultiplicativeTamagawa F S) Measure.count
      ((ν.comap (sIdeleClassInclusion F S)).map (sIdeleClassToLocal F S)) := by
  let η := globalIdeleTamagawa F
  let ρ := ν.comap (sIdeleClassInclusion F S)
  let φ := sIdeleClassToLocal F S
  let m := integralIdeleTailMass F S
  let μ := sLocalMultiplicativeTamagawa F S
  let κ := integralIdeleTailProbability F S
  letI : μ.IsHaarMeasure := sLocalMultiplicativeTamagawa_isHaar F S
  letI : IsProbabilityMeasure κ := ⟨integralIdeleTailProbability_univ F S⟩
  let e := (sBlockUnitProduct F S).toHomeomorph.toMeasurableEquiv
  let ηS := η.comap (sIdeleBlock F S).subtype
  have hr := sIdeleClass_isWeilQuotientMeasure_comap F S η ν hν
  letI : ρ.IsHaarMeasure := hr.1
  have hφ := sIdeleClassToLocal_isProperMap F S
  letI : (ρ.map φ).IsHaarMeasure := Measure.isHaarMeasure_map ρ φ hφ.continuous
    (sIdeleClassToLocal_isOpenQuotientMap F S).surjective (isProperMap_iff_tendsto_cocompact.mp hφ).2
  letI : (ρ.map φ).Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _
  refine ⟨inferInstance, inferInstance, fun f hf => ?_⟩
  let fp : C(B F S, ℂ) := ⟨f ∘ project F S, f.continuous.comp
    (continuous_fst.comp (sBlockUnitProduct F S).continuous)⟩
  have hp : IsProperMap (project F S) :=
    isProperMap_fst_of_compactSpace.comp (sBlockUnitProduct F S).toHomeomorph.isProperMap
  have hfp : HasCompactSupport fp :=
    HasCompactSupport.intro (hp.isCompact_preimage hf) fun a ha =>
      notMem_support.mp (fun hn => ha (subset_tsupport f hn))
  have hcoset (q : SIdeleClass F S) : lcaCosetIntegral (H F S) Measure.count fp q =
      lcaCosetIntegral (D F S) Measure.count f (φ q) := localCosetIntegral_project F S f q
  have hme : Measurable (lcaCosetIntegral (D F S) Measure.count f) := by
    let ses := TopologicalGroup.IsSES.ofClosedSubgroup (D F S) (sUnitImage_closed F S)
    let fc : CompactlySupportedContinuousMap (U F S) ℂ := ⟨f, hf⟩
    have he : lcaCosetIntegral (D F S) Measure.count f = ses.pushforward Measure.count fc := by
      funext q
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
      change _ = ses.pushforward Measure.count fc ((QuotientGroup.mk' (D F S)) a)
      rw [ses.pushforward_apply_apply, lcaCosetIntegral_mk]
      rfl
    rw [he]
    exact (ses.pushforward Measure.count fc).continuous.measurable
  change (∫ u, f u ∂m • μ) = ∫ q, lcaCosetIntegral (D F S) Measure.count f q ∂ρ.map φ
  rw [integral_map hφ.continuous.measurable.aemeasurable hme.aestronglyMeasurable]
  rw [show (fun q => lcaCosetIntegral (D F S) Measure.count f (φ q)) =
    lcaCosetIntegral (H F S) Measure.count fp from (funext hcoset).symm]
  have hWeil : (∫ a, fp a ∂ηS) =
      ∫ q, lcaCosetIntegral (H F S) Measure.count fp q ∂ρ := hr.2.2 fp hfp
  rw [← hWeil]
  have hc : (ηS.map e) = m • (μ.prod κ) := globalIdeleTamagawa_block F S
  change (∫ u, f u ∂m • μ) = ∫ a, f (e a).1 ∂ηS
  rw [← e.measurableEmbedding.integral_map (fun p => f p.1), hc, integral_smul_measure,
    integral_smul_measure, integral_fun_fst, measureReal_def,
    integralIdeleTailProbability_univ, ENNReal.toReal_one, one_smul]

/-- The pushed global quotient measure is exactly the local Tamagawa quotient
times the omitted integral-unit mass. -/
theorem globalIdeleTamagawa_map_localQuotient (ν : Measure (Q F))
    (hν : IsWeilQuotientMeasure (principalIdeles F) (globalIdeleTamagawa F) Measure.count ν)
    (ρ : Measure (SIdeleQuotient F S))
    (hρ : IsWeilQuotientMeasure (D F S) (sLocalMultiplicativeTamagawa F S) Measure.count ρ) :
    (ν.comap (sIdeleClassInclusion F S)).map (sIdeleClassToLocal F S) =
      integralIdeleTailMass F S • ρ := by
  let m := integralIdeleTailMass F S
  let μ := sLocalMultiplicativeTamagawa F S
  letI : μ.IsHaarMeasure := sLocalMultiplicativeTamagawa_isHaar F S
  letI : (m • μ).IsHaarMeasure :=
    Measure.IsHaarMeasure.smul μ (integralIdeleTailMass_ne_zero F S) (integralIdeleTailMass_ne_top F S)
  letI : (m • μ).Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _
  letI : (Measure.count : Measure (D F S)).Regular := by
    letI : LocallyCompactSpace (D F S) := (sUnitImage_closed F S).locallyCompactSpace
    exact Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _
  have hs : IsWeilQuotientMeasure (D F S) (m • μ) Measure.count (m • ρ) := by
    letI : ρ.IsHaarMeasure := hρ.1
    letI : (m • ρ).IsHaarMeasure :=
      Measure.IsHaarMeasure.smul ρ (integralIdeleTailMass_ne_zero F S) (integralIdeleTailMass_ne_top F S)
    refine ⟨inferInstance, Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _, ?_⟩
    intro f hf
    simp only [integral_smul_measure]
    exact congrArg (m.toReal • ·) (hρ.2.2 f hf)
  obtain ⟨τ, _, hu⟩ := weilQuotientMeasure_existsUnique (D F S) (sUnitImage_closed F S)
    (m • μ) Measure.count
  exact (hu _ (globalIdeleTamagawa_map_localQuotient_isWeil F S ν hν)).trans (hu _ hs).symm

local instance tamCompareBlockNormOneBorel : BorelSpace (sNormOneClass F S) :=
  inferInstanceAs (BorelSpace (Subtype _))
local instance tamCompareLocalNormOneBorel : BorelSpace (SLocalThetaNormOne F S) :=
  inferInstanceAs (BorelSpace (Subtype _))

/-- Discard the integral tail on the norm-one subgroup of the S-block classes. -/
def sIdeleNormOneToLocal : sNormOneClass F S →ₜ* SLocalThetaNormOne F S :=
  { toMonoidHom :=
      ((sIdeleClassToLocal F S).comp (sNormOneClass F S).subtype).codRestrict
        (SLocalThetaNormOne F S) (fun k => by
          change sQuotientNorm F S (sIdeleClassToLocal F S k.val) = 1
          rw [sQuotientNorm_toLocal]
          exact Units.ext (NNReal.eq k.property))
    continuous_toFun :=
      ((sIdeleClassToLocal_isOpenQuotientMap F S).continuous.comp continuous_subtype_val).subtype_mk _ }

theorem sIdeleNormOneToLocal_surjective : Surjective (sIdeleNormOneToLocal F S) := by
  intro y
  obtain ⟨x, hx⟩ := (sIdeleClassToLocal_isOpenQuotientMap F S).surjective y.val
  have h := sQuotientNorm_toLocal F S x
  rw [hx, show sQuotientNorm F S y.val = 1 from y.property] at h
  have hk : x ∈ sNormOneClass F S := congrArg (fun n : ℝ≥0ˣ => (n.val : ℝ)) h.symm
  exact ⟨⟨x, hk⟩, Subtype.ext hx⟩

private theorem sIdeleNormOneInclusion_openEmbedding :
    IsOpenEmbedding (sIdeleNormOneContinuousInclusion F S) := by
  let i := sIdeleClassInclusion F S
  let j := sIdeleNormOneContinuousInclusion F S
  have hr : range j = (Subtype.val : K F → Q F) ⁻¹' range i := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x.val, rfl⟩
    · rintro ⟨x, hx⟩
      have hk : x ∈ sNormOneClass F S := by
        change ideleClassNorm F (i x) = 1
        rw [hx]
        exact y.property
      exact ⟨⟨x, hk⟩, Subtype.ext hx⟩
  refine ⟨?_, hr ▸ (sIdeleClassInclusion_openEmbedding F S).isOpen_range.preimage continuous_subtype_val⟩
  apply (IsEmbedding.subtypeVal (p := fun x : Q F => x ∈ normOneIdeleClass F)).of_comp_iff.mp
  exact (sIdeleClassInclusion_openEmbedding F S).isEmbedding.comp IsEmbedding.subtypeVal

private def sBlockClassRay (t : Multiplicative ℝ) : SIdeleClass F S :=
  QuotientGroup.mk (⟨ideleExpSection F t, by
    apply (sIdeleBlock_mem_iff F S _).mpr
    intro v _
    apply (ideleOrder_eq_zero_iff F _ v).mpr
    rw [(ideleExpSection_components F t).2]
    exact map_one _⟩ : B F S)

private def sBlockClassLogMap (p : ℝ × sNormOneClass F S) : SIdeleClass F S :=
  sBlockClassRay F S (Multiplicative.ofAdd p.1) * p.2.val

private theorem sBlockClassLogMap_global (p : ℝ × sNormOneClass F S) :
    sIdeleClassInclusion F S (sBlockClassLogMap F S p) =
      ideleClassLogCoordinates F (p.1, sIdeleNormOneContinuousInclusion F S p.2) := by
  unfold sBlockClassLogMap
  rw [map_mul]
  exact mul_comm (ideleClassExpSection F (Multiplicative.ofAdd p.1))
    (sIdeleClassInclusion F S p.2.val)

private theorem sBlockClassLogMap_local (p : ℝ × sNormOneClass F S) :
    sIdeleClassToLocal F S (sBlockClassLogMap F S p) =
      sLocalZetaSplit F S (p.1, sIdeleNormOneToLocal F S p.2) := by
  unfold sBlockClassLogMap
  rw [map_mul]
  rfl

/-- Logarithmic modulus and norm-one coordinates on the open S-block quotient. -/
def sBlockClassLogCoordinates : ℝ × sNormOneClass F S ≃ₜ SIdeleClass F S := by
  have hi := (sIdeleClassInclusion_openEmbedding F S).isEmbedding
  have he : IsEmbedding (sBlockClassLogMap F S) := by
    apply hi.of_comp_iff.mp
    rw [show (sIdeleClassInclusion F S) ∘ sBlockClassLogMap F S =
      (ideleClassLogCoordinates F) ∘ Prod.map id (sIdeleNormOneContinuousInclusion F S) from
      funext (sBlockClassLogMap_global F S)]
    exact (ideleClassLogCoordinates F).isEmbedding.comp
      (IsEmbedding.id.prodMap (sIdeleNormOneInclusion_openEmbedding F S).isEmbedding)
  refine he.toHomeomorphOfSurjective fun x => ?_
  let i := sIdeleClassInclusion F S
  let t := ideleClassLogNorm F (i x)
  let r := sBlockClassRay F S t
  have hk : x / r ∈ sNormOneClass F S := by
    change ideleClassNorm F (i (x / r)) = 1
    rw [map_div, map_div, div_eq_one_iff_eq (ideleClassNorm_pos F (i r)).ne']
    change ideleClassNorm F (i x) = ideleClassNorm F (ideleClassExpSection F t)
    rw [ideleClassNorm_expSection]
    exact (Real.exp_log (ideleClassNorm_pos F (i x))).symm
  exact ⟨(t.toAdd, ⟨x / r, hk⟩), mul_div_cancel r x⟩

private theorem globalClassMeasure_comap_block (ν : Measure (K F)) [IsFiniteMeasure ν] :
    (globalClassMeasure F ν).comap (sIdeleClassInclusion F S) =
      (volume.prod (ν.comap (sIdeleNormOneContinuousInclusion F S))).map
        (sBlockClassLogCoordinates F S) := by
  let j := sIdeleNormOneContinuousInclusion F S
  let i := sIdeleClassInclusion F S
  let J := Prod.map (@id ℝ) j
  let b := (sBlockClassLogCoordinates F S).toMeasurableEquiv
  let e := (ideleClassLogCoordinates F).toMeasurableEquiv
  have hj := (sIdeleNormOneInclusion_openEmbedding F S).measurableEmbedding
  have hJ : MeasurableEmbedding J := MeasurableEmbedding.id.prodMap hj
  have hprod : (volume.prod ν).comap J = volume.prod (ν.comap j) := by
    letI : IsFiniteMeasure (ν.comap j) := ⟨by rw [hj.comap_apply ν univ]; exact measure_lt_top _ _⟩
    symm
    refine Measure.prod_eq fun s t _ _ => ?_
    rw [hJ.comap_apply (volume.prod ν) (s ×ˢ t), hj.comap_apply ν t]
    change (volume.prod ν) ((fun a : ℝ × sNormOneClass F S => (id a.1, j a.2)) '' (s ×ˢ t)) =
      volume s * ν (j '' t)
    rw [← Set.prod_image_image_eq, Set.image_id, Measure.prod_prod]
  change (Measure.map e (volume.prod ν)).comap i = Measure.map b (volume.prod (ν.comap j))
  rw [← hprod]
  exact map_comap_of_square b e J i hJ
    (sIdeleClassInclusion_openEmbedding F S).measurableEmbedding
    (fun p => (sBlockClassLogMap_global F S p).symm) (volume.prod ν) |>.symm

/-- With Lebesgue measure in the common logarithmic coordinate, the local
norm-one Weil measure differs from the pushed global restriction by precisely
the integral-unit mass of the discarded finite places. -/
theorem globalIdeleTamagawa_map_localNormOne (ν : Measure (K F)) [ν.IsHaarMeasure]
    (hν : IsWeilQuotientMeasure (principalIdeles F) (globalIdeleTamagawa F)
      Measure.count (globalClassMeasure F ν))
    (ρ : Measure (SLocalThetaNormOne F S)) [ρ.IsHaarMeasure]
    (hρ : IsWeilQuotientMeasure (D F S) (sLocalMultiplicativeTamagawa F S)
      Measure.count (sLocalClassHaar F S ρ)) :
    (ν.comap (sIdeleNormOneContinuousInclusion F S)).map (sIdeleNormOneToLocal F S) =
      integralIdeleTailMass F S • ρ := by
  let j := sIdeleNormOneContinuousInclusion F S
  let p := sIdeleNormOneToLocal F S
  let m := integralIdeleTailMass F S
  let v := ν.comap j
  letI : CompactSpace (K F) := normOneIdeleClass_compact F
  letI : IsFiniteMeasure ν := ⟨isCompact_univ.measure_lt_top⟩
  letI : CompactSpace (SLocalThetaNormOne F S) := sLocalThetaNormOne_compact F S
  letI : IsFiniteMeasure ρ := ⟨isCompact_univ.measure_lt_top⟩
  letI : IsFiniteMeasure v := ⟨by
    rw [show v = ν.comap j from rfl,
      (sIdeleNormOneInclusion_openEmbedding F S).measurableEmbedding.comap_apply ν univ]
    exact measure_lt_top _ _⟩
  have h := globalIdeleTamagawa_map_localQuotient F S (globalClassMeasure F ν)
    hν (sLocalClassHaar F S ρ) hρ
  rw [globalClassMeasure_comap_block F S ν] at h
  have he : (sIdeleClassToLocal F S) ∘ (sBlockClassLogCoordinates F S) =
      (sLocalZetaSplit F S) ∘ Prod.map id p := funext (sBlockClassLogMap_local F S)
  change ((volume.prod v).map (sBlockClassLogCoordinates F S)).map
    (sIdeleClassToLocal F S) = m • sLocalClassHaar F S ρ at h
  have hp : Measurable (p : sNormOneClass F S → SLocalThetaNormOne F S) :=
    p.continuous.measurable
  rw [Measure.map_map (sIdeleClassToLocal_isOpenQuotientMap F S).continuous.measurable
    (sBlockClassLogCoordinates F S).continuous.measurable, he,
    ← Measure.map_map (sLocalZetaSplit F S).continuous.measurable (measurable_id.prodMap hp),
    ← Measure.map_prod_map volume v measurable_id hp, Measure.map_id] at h
  unfold sLocalClassHaar at h
  rw [← Measure.map_smul, ← Measure.prod_smul_right] at h
  have hprod := (sLocalZetaSplit F S).toMeasurableEquiv.map_measurableEquiv_injective h
  ext A _
  have hmass := congrArg (fun μ : Measure (ℝ × SLocalThetaNormOne F S) =>
    μ (Icc (0 : ℝ) 1 ×ˢ A)) hprod
  simpa [Measure.prod_prod, Real.volume_Icc] using hmass

/-- Once S contains the support of the different, the omitted unit groups
all have Tamagawa mass one. -/
theorem integralIdeleTailMass_eq_one_of_support_subset
    (hS : Function.mulSupport (differentPrimeMass F) ⊆ (S : Set (Place F))) :
    integralIdeleTailMass F S = 1 := by
  unfold integralIdeleTailMass
  apply finprod_eq_one_of_forall_eq_one
  intro v
  by_contra h
  exact v.property (hS h)

/-- A finite threshold ensures both surjectivity onto the global class group
and unit mass for the discarded integral tail at every larger stage. -/
theorem globalIdeleTamagawa_eventually_noTailScale :
    ∃ S₀ : Finset (Place F), ∀ S : Finset (Place F), S₀ ⊆ S →
      Surjective (sIdeleClassInclusion F S) ∧ integralIdeleTailMass F S = 1 := by
  obtain ⟨R, hR⟩ := sIdeleClass_eventually_surjective F
  let D := (differentPrimeMass_finite F).toFinset
  refine ⟨R ∪ D, fun S hS => ⟨hR S (Finset.subset_union_left.trans hS), ?_⟩⟩
  apply integralIdeleTailMass_eq_one_of_support_subset F S
  intro v hv
  exact hS (Finset.mem_union_right R ((Set.Finite.mem_toFinset _).mpr hv))

/-- For functions pulled back from the finite-coordinate norm-one quotient,
integration against the restricted global measure introduces exactly the
discarded integral-unit mass. This applies to each radial seminorm profile. -/
theorem globalIdeleTamagawa_localNormOne_integral (ν : Measure (K F)) [ν.IsHaarMeasure]
    (hν : IsWeilQuotientMeasure (principalIdeles F) (globalIdeleTamagawa F)
      Measure.count (globalClassMeasure F ν))
    (ρ : Measure (SLocalThetaNormOne F S)) [ρ.IsHaarMeasure]
    (hρ : IsWeilQuotientMeasure (D F S) (sLocalMultiplicativeTamagawa F S)
      Measure.count (sLocalClassHaar F S ρ))
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : SLocalThetaNormOne F S → E) (hf : StronglyMeasurable f) :
    (∫ k, f (sIdeleNormOneToLocal F S k) ∂ν.comap (sIdeleNormOneContinuousInclusion F S)) =
      (integralIdeleTailMass F S).toReal • ∫ k, f k ∂ρ := by
  have hp : Measurable (sIdeleNormOneToLocal F S : sNormOneClass F S → SLocalThetaNormOne F S) :=
    (sIdeleNormOneToLocal F S).continuous.measurable
  rw [← integral_map hp.aemeasurable hf.aestronglyMeasurable,
    globalIdeleTamagawa_map_localNormOne F S ν hν ρ hρ, integral_smul_measure]

/-- For Bruhat tests that descend through the integral tail, the radial
seminorm picks up exactly the omitted unit mass to the power `1 / p`. -/
theorem globalIdeleTamagawa_splitRadialNorm (ν : Measure (K F)) [ν.IsHaarMeasure]
    (hν : IsWeilQuotientMeasure (principalIdeles F) (globalIdeleTamagawa F)
      Measure.count (globalClassMeasure F ν))
    (ρ : Measure (SLocalThetaNormOne F S)) [ρ.IsHaarMeasure]
    (hρ : IsWeilQuotientMeasure (D F S) (sLocalMultiplicativeTamagawa F S)
      Measure.count (sLocalClassHaar F S ρ))
    (σ : Multiplicative ℝ →ₜ* SIdeleClass F S)
    (τ : Multiplicative ℝ →ₜ* SIdeleQuotient F S)
    (hστ : ∀ t, sIdeleClassToLocal F S (σ t) = τ t)
    (p : ℝ≥0∞) (P : Polynomial ℂ)
    (u : BruhatSchwartz (SIdeleClass F S)) (w : BruhatSchwartz (SIdeleQuotient F S))
    (hu : ∀ x, u.val x = w.val (sIdeleClassToLocal F S x)) :
    bruhatSplitRadialNorm σ (ν.comap (sIdeleNormOneContinuousInclusion F S)) p P u =
      (integralIdeleTailMass F S).toReal ^ (1 / p.toReal) * bruhatSplitRadialNorm τ ρ p P w := by
  let m := (integralIdeleTailMass F S).toReal
  let g (t : ℝ) (k : SLocalThetaNormOne F S) :=
    ‖P.eval (↑|Real.log t| : ℂ) * w.val (τ (Multiplicative.ofAdd (Real.log t)) * k.val)‖ ^ p.toReal
  have hg (t : ℝ) : Continuous (g t) :=
    (Real.continuous_rpow_const ENNReal.toReal_nonneg).comp
      (continuous_const.mul
        ((bruhatSchwartz_continuous w).comp (continuous_const.mul continuous_subtype_val))).norm
  have hinner (t : ℝ) :
      (∫ k, ‖P.eval (↑|Real.log t| : ℂ) *
        u.val (σ (Multiplicative.ofAdd (Real.log t)) * k.val)‖ ^ p.toReal
        ∂ν.comap (sIdeleNormOneContinuousInclusion F S)) = m * ∫ k, g t k ∂ρ := by
    have he (k : sNormOneClass F S) :
        sIdeleClassToLocal F S (σ (Multiplicative.ofAdd (Real.log t)) * k.val) =
          τ (Multiplicative.ofAdd (Real.log t)) * (sIdeleNormOneToLocal F S k).val := by
      rw [map_mul, hστ]
      rfl
    simp only [hu, he]
    exact globalIdeleTamagawa_localNormOne_integral F S ν hν ρ hρ (g t)
      ((hg t).stronglyMeasurable)
  unfold bruhatSplitRadialNorm
  simp_rw [hinner]
  change (∫ t in Ioi (0 : ℝ), t⁻¹ * (m * ∫ k, g t k ∂ρ)) ^ (1 / p.toReal) =
    m ^ (1 / p.toReal) * (∫ t in Ioi (0 : ℝ), t⁻¹ * ∫ k, g t k ∂ρ) ^ (1 / p.toReal)
  simp_rw [mul_left_comm _ m, integral_const_mul]
  refine Real.mul_rpow ENNReal.toReal_nonneg (setIntegral_nonneg measurableSet_Ioi fun t ht => ?_)
  exact mul_nonneg (inv_nonneg.mpr ht.le) (integral_nonneg fun k => Real.rpow_nonneg (norm_nonneg _) _)

end
end Masullo
