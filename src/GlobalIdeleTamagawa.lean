import SLocalMultiplicativeTamagawa
import SLocalCharacterRestriction
import GlobalMellinPadding
import GlobalHeckeGaussianReference
import GlobalHeckeResidues
import Mathlib.Probability.ProductMeasure

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology TopologicalSpace
open scoped Classical ENNReal NumberField SchwartzMap

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

private abbrev Place := HeightOneSpectrum (𝓞 F)
private abbrev Arch := (InfiniteAdeleRing F)ˣ
private abbrev Local (v : Place F) := (v.adicCompletion F)ˣ
private abbrev Selected (S : Finset (Place F)) := (SAdeles F S)ˣ
private abbrev Tail (S : Finset (Place F)) := (SIntegralTail F S)ˣ

local instance tamAdelesSC : SecondCountableTopology (Adeles F) := adeles_secondCountable F
local instance tamAdelesOppSC : SecondCountableTopology (Adeles F)ᵐᵒᵖ :=
  MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
local instance tamIdeleSC : SecondCountableTopology (Idele F) :=
  Units.isEmbedding_embedProduct.secondCountableTopology
local instance tamIdeleLC : LocallyCompactSpace (Idele F) := ideles_locallyCompact
local instance tamIdeleT2 : T2Space (Idele F) := ideles_hausdorff
local instance tamIdeleMeas : MeasurableSpace (Idele F) := borel _
local instance tamIdeleBorel : BorelSpace (Idele F) := ⟨rfl⟩
local instance tamNormOneMeas : MeasurableSpace (normOneIdeleClass F) := borel _
local instance tamNormOneBorel : BorelSpace (normOneIdeleClass F) := ⟨rfl⟩
local instance tamInfiniteT2 : T2Space (InfiniteAdeleRing F) :=
  (infiniteAdeleMixedHomeomorph F).isEmbedding.t2Space
local instance tamArchMeas : MeasurableSpace (Arch F) := borel _
local instance tamArchBorel : BorelSpace (Arch F) := ⟨rfl⟩
local instance tamCompletionMeas (v : Place F) : MeasurableSpace (v.adicCompletion F) := borel _
local instance tamCompletionBorel (v : Place F) : BorelSpace (v.adicCompletion F) := ⟨rfl⟩
local instance tamCompletionSC (v : Place F) : SecondCountableTopology (v.adicCompletion F) :=
  finitePlace_secondCountable F v
local instance tamCompletionLC (v : Place F) : LocallyCompactSpace (v.adicCompletion F) :=
  finitePlace_locallyCompact F v
local instance tamLocalLC (v : Place F) : LocallyCompactSpace (Local F v) :=
  IsOpenUnits.isOpenEmbedding_unitsVal.locallyCompactSpace
local instance tamLocalSC (v : Place F) : SecondCountableTopology (Local F v) :=
  Units.isEmbedding_val₀.secondCountableTopology
local instance tamLocalMeas (v : Place F) : MeasurableSpace (Local F v) := borel _
local instance tamLocalBorel (v : Place F) : BorelSpace (Local F v) := ⟨rfl⟩
local instance tamFiniteHaar (v : Place F) :
    (finitePlaceMultiplicativeTamagawa F v).IsHaarMeasure :=
  finitePlaceMultiplicativeTamagawa_isHaar F v
local instance tamFiniteSigma (v : Place F) : SigmaFinite (finitePlaceMultiplicativeTamagawa F v) :=
  inferInstance
local instance tamBlockLC (S : Finset (Place F)) : LocallyCompactSpace (sIdeleBlock F S) :=
  (sIdeleBlock_open F S).locallyCompactSpace
local instance tamBlockSC (S : Finset (Place F)) : SecondCountableTopology (sIdeleBlock F S) :=
  (sIdeleBlock_open F S).isOpenEmbedding_subtypeVal.isEmbedding.secondCountableTopology
local instance tamSelectedLC (S : Finset (Place F)) : LocallyCompactSpace (Selected F S) :=
  sLocalIdeles_locallyCompact F S
local instance tamSelectedSC (S : Finset (Place F)) : SecondCountableTopology (Selected F S) :=
  sLocalIdeles_secondCountable F S
local instance tamSelectedMeas (S : Finset (Place F)) : MeasurableSpace (Selected F S) := borel _
local instance tamSelectedBorel (S : Finset (Place F)) : BorelSpace (Selected F S) := ⟨rfl⟩
local instance tamTailCompact (S : Finset (Place F)) : CompactSpace (Tail F S) :=
  tailUnits_compact F S
local instance tamTailMeas (S : Finset (Place F)) : MeasurableSpace (Tail F S) := borel _
local instance tamTailBorel (S : Finset (Place F)) : BorelSpace (Tail F S) := ⟨rfl⟩
local instance tamProductSC (S : Finset (Place F)) :
    SecondCountableTopology (Selected F S × Tail F S) :=
  (sBlockUnitProduct F S).symm.toHomeomorph.isEmbedding.secondCountableTopology
local instance tamProductT2 (S : Finset (Place F)) :
    T2Space (Selected F S × Tail F S) :=
  (sBlockUnitProduct F S).symm.toHomeomorph.isEmbedding.t2Space
local instance tamTailSC (S : Finset (Place F)) : SecondCountableTopology (Tail F S) :=
  (isEmbedding_prodMkRight (Y := Tail F S) (1 : Selected F S)).secondCountableTopology
local instance tamBlockBorel (S : Finset (Place F)) : BorelSpace (sIdeleBlock F S) :=
  inferInstanceAs (BorelSpace (Subtype _))

/-- Product of the original local Tamagawa masses of the omitted integral unit groups. -/
def integralIdeleTailMass (S : Finset (Place F)) : ℝ≥0∞ :=
  ∏ᶠ v : {v : Place F // v ∉ S}, differentPrimeMass F v.val

/-- Probability Haar measure on the product of the integral units outside S. -/
def integralIdeleTailProbability (S : Finset (Place F)) : Measure (Tail F S) :=
  Measure.haarMeasure ⊤

theorem integralIdeleTailProbability_univ (S : Finset (Place F)) :
    integralIdeleTailProbability F S univ = 1 := Measure.haarMeasure_self (K₀ := ⊤)

local instance tamTailProb (S : Finset (Place F)) :
    IsProbabilityMeasure (integralIdeleTailProbability F S) := ⟨integralIdeleTailProbability_univ F S⟩
local instance tamTailHaar (S : Finset (Place F)) :
    (integralIdeleTailProbability F S).IsHaarMeasure := by
  unfold integralIdeleTailProbability
  infer_instance
local instance tamSelectedHaar (S : Finset (Place F)) :
    (sLocalMultiplicativeTamagawa F S).IsHaarMeasure := sLocalMultiplicativeTamagawa_isHaar F S

private abbrev TailIndex (S : Finset (Place F)) := {v : Place F // v ∉ S}
private abbrev TailFactor (v : Place F) := (v.adicCompletionIntegers F)ˣ

local instance tamFinitePlaceCountable : Countable (Place F) := finitePlaces_countable F
local instance tamIntegerCompact (v : Place F) : CompactSpace (v.adicCompletionIntegers F) :=
  compactSpace_adicIntegers v
local instance tamFactorCompact (v : Place F) : CompactSpace (TailFactor F v) :=
  compactSpace_units_of_compactSpace _
local instance tamFactorSC (v : Place F) : SecondCountableTopology (TailFactor F v) := by
  letI : SecondCountableTopology (v.adicCompletionIntegers F) :=
    IsEmbedding.subtypeVal.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology
local instance tamFactorMeas (v : Place F) : MeasurableSpace (TailFactor F v) := borel _
local instance tamFactorBorel (v : Place F) : BorelSpace (TailFactor F v) := ⟨rfl⟩

/-- Probability Haar on an individual finite integral unit group. -/
def finiteIntegralIdeleProbability (v : Place F) : Measure (TailFactor F v) :=
  Measure.haarMeasure ⊤

local instance tamFactorProb (v : Place F) : IsProbabilityMeasure (finiteIntegralIdeleProbability F v) :=
  ⟨Measure.haarMeasure_self (K₀ := ⊤)⟩
local instance tamFactorHaar (v : Place F) : (finiteIntegralIdeleProbability F v).IsHaarMeasure := by
  unfold finiteIntegralIdeleProbability
  infer_instance

private def finiteIntegralUnitInclusion (v : Place F) : TailFactor F v →* Local F v :=
  Units.map (v.adicCompletionIntegers F).subtype

private theorem finiteIntegralUnitInclusion_range (v : Place F) :
    range (finiteIntegralUnitInclusion F v) = finitePlaceIntegralUnits F v := by
  ext u
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x.val.property, x.inv.property⟩
  · intro hu
    refine ⟨⟨⟨u.val, hu.1⟩, ⟨u.inv, hu.2⟩, Subtype.ext u.val_inv,
      Subtype.ext u.inv_val⟩, ?_⟩
    exact Units.ext rfl

/-- On each omitted place the probability factor is the normalized
restriction of its original multiplicative Tamagawa measure. -/
theorem finiteIntegralIdeleProbability_map (v : Place F) :
    (finiteIntegralIdeleProbability F v).map (finiteIntegralUnitInclusion F v) =
      (differentPrimeMass F v)⁻¹ •
        (finitePlaceMultiplicativeTamagawa F v).restrict (finitePlaceIntegralUnits F v) := by
  let j := finiteIntegralUnitInclusion F v
  let μ := finitePlaceMultiplicativeTamagawa F v
  let ν := finiteIntegralIdeleProbability F v
  have hj : Continuous j := Units.continuous_iff.mpr
    ⟨continuous_subtype_val.comp Units.continuous_val,
      continuous_subtype_val.comp Units.continuous_coe_inv⟩
  have hi : Injective j := fun a b hab => Units.ext
    (Subtype.ext (congrArg Units.val hab))
  have he : IsOpenEmbedding j :=
    ⟨(hj.isClosedEmbedding hi).isEmbedding,
      by rw [finiteIntegralUnitInclusion_range]; exact localIntegralUnits_open F v⟩
  let ρ := μ.comap j
  letI : ρ.IsHaarMeasure := Measure.IsHaarMeasure.comap (mH := inferInstance) μ he
  let c := Measure.haarScalarFactor ρ ν
  have hρ : ρ = c • ν := Measure.isMulLeftInvariant_eq_smul _ _
  have hc := congrArg (fun m : Measure (TailFactor F v) => m univ) hρ
  have hm : MeasurableEmbedding (⇑j) := he.measurableEmbedding
  change (μ.comap j) univ = (c • ν) univ at hc
  rw [hm.comap_apply, image_univ, finiteIntegralUnitInclusion_range,
    finitePlaceMultiplicativeTamagawa_units, Measure.coe_nnreal_smul_apply, measure_univ, mul_one] at hc
  have hrestrict : ρ.map j = μ.restrict (finitePlaceIntegralUnits F v) := by
    rw [← finiteIntegralUnitInclusion_range]
    exact hm.map_comap μ
  rw [hρ, Measure.map_smul] at hrestrict
  change ν.map j = (differentPrimeMass F v)⁻¹ • _
  rw [← hrestrict]
  change ν.map j = (differentPrimeMass F v)⁻¹ • ((c : ℝ≥0∞) • ν.map j)
  rw [smul_smul, ← hc, ENNReal.inv_mul_cancel (differentPrimeMass_ne_zero F v)
    (differentPrimeMass_ne_top F v), one_smul]

/-- The normalized Haar measure of the integral tail is the infinite
product of the normalized local unit measures. -/
theorem integralIdeleTailProbability_eq_product (S : Finset (Place F)) :
    (integralIdeleTailProbability F S).map
      (ContinuousMulEquiv.piUnits :
        Tail F S ≃ₜ* (∀ v : TailIndex F S, TailFactor F v.val)) =
      Measure.infinitePi (fun v : TailIndex F S => finiteIntegralIdeleProbability F v.val) := by
  let e : Tail F S ≃ₜ* (∀ v : TailIndex F S, TailFactor F v.val) := ContinuousMulEquiv.piUnits
  let α (v : TailIndex F S) := finiteIntegralIdeleProbability F v.val
  let ν := (integralIdeleTailProbability F S).map e
  let μ := Measure.infinitePi α
  letI : ν.IsHaarMeasure := e.toMulEquiv.isHaarMeasure_map _ e.continuous e.symm.continuous
  letI : IsProbabilityMeasure μ := inferInstance
  letI : μ.IsMulLeftInvariant := ⟨fun a => by
    change (Measure.infinitePi α).map (fun x i => a i * x i) = _
    rw [Measure.infinitePi_map_pi _ (fun i => measurable_const_mul (a i))]
    congr 1
    funext i
    exact (measurePreserving_mul_left (α i) (a i)).map_eq⟩
  let c := Measure.haarScalarFactor μ ν
  have he : μ = c • ν := Measure.isMulLeftInvariant_eq_smul _ _
  have hν : ν univ = 1 :=
    (Measure.map_apply e.continuous.measurable MeasurableSet.univ).trans
      (by rw [preimage_univ, integralIdeleTailProbability_univ])
  have hc := congrArg (fun m : Measure (∀ v : TailIndex F S, TailFactor F v.val) => m univ) he
  change μ univ = (c • ν) univ at hc
  rw [measure_univ, Measure.coe_nnreal_smul_apply, hν, mul_one] at hc
  have hc' : c = 1 := ENNReal.coe_inj.mp (hc.symm.trans ENNReal.coe_one.symm)
  change ν = μ
  rw [he, hc', one_smul]

private def allIntegralReference (A : PositiveCompacts (Arch F)) : Set (Idele F) :=
  {a | a ∈ sIdeleBlock F ∅ ∧ (Homeomorph.prodUnits a).1 ∈ (A : Set (Arch F))}

private def selectedReference (A : PositiveCompacts (Arch F)) (S : Finset (Place F)) :
    Set (Selected F S) :=
  (sLocalZetaIdeleCoordinates F S) ⁻¹'
    ((A : Set (Arch F)) ×ˢ Set.pi univ (fun v : S => finitePlaceIntegralUnits F v.val))

private theorem reference_image (A : PositiveCompacts (Arch F)) (S : Finset (Place F)) :
    (Subtype.val : sIdeleBlock F S → Idele F) ''
        ((sBlockUnitProduct F S) ⁻¹' (selectedReference F A S ×ˢ univ)) =
      allIntegralReference F A := by
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    change ((a.val ∈ sIdeleBlock F ∅) ∧ _)
    refine ⟨⟨?_, ?_⟩, ha.1.1⟩
    · intro v _
      by_cases hv : v ∈ S
      · exact (ha.1.2 ⟨v, hv⟩ (mem_univ _)).1
      · exact a.property.1 v hv
    · intro v _
      by_cases hv : v ∈ S
      · exact (ha.1.2 ⟨v, hv⟩ (mem_univ _)).2
      · exact a.property.2 v hv
  · rintro ⟨hx, hA⟩
    have hxS : x ∈ sIdeleBlock F S :=
      ⟨fun v _ => hx.1 v (Finset.notMem_empty v), fun v _ => hx.2 v (Finset.notMem_empty v)⟩
    exact ⟨⟨x, hxS⟩, ⟨⟨hA, fun v _ => ⟨hx.1 v.val (Finset.notMem_empty _),
      hx.2 v.val (Finset.notMem_empty _)⟩⟩, mem_univ _⟩, rfl⟩

private theorem selectedReference_isCompact (A : PositiveCompacts (Arch F)) (S : Finset (Place F)) :
    IsCompact (selectedReference F A S) :=
  (sLocalZetaIdeleCoordinates F S).toHomeomorph.isCompact_preimage.mpr
    (A.isCompact.prod (isCompact_univ_pi fun v : S => localIntegralUnits_compact F v.val))

private theorem allIntegralReference_isCompact (A : PositiveCompacts (Arch F)) :
    IsCompact (allIntegralReference F A) := by
  rw [← reference_image F A ∅]
  exact ((sBlockUnitProduct F ∅).toHomeomorph.isCompact_preimage.mpr
    ((selectedReference_isCompact F A ∅).prod isCompact_univ)).image continuous_subtype_val

private theorem allIntegralReference_interior (A : PositiveCompacts (Arch F)) :
    (interior (allIntegralReference F A)).Nonempty := by
  let e := sBlockUnitProduct F (∅ : Finset (Place F))
  let j := sLocalZetaIdeleCoordinates F (∅ : Finset (Place F))
  let U : Set (Selected F ∅) := j ⁻¹' (interior (A : Set (Arch F)) ×ˢ
    Set.pi univ (fun v : (∅ : Finset (Place F)) => finitePlaceIntegralUnits F v.val))
  have hu : IsOpen U :=
    (isOpen_interior.prod (isOpen_set_pi finite_univ fun v _ => localIntegralUnits_open F v.val)).preimage
      j.continuous
  let W := (Subtype.val : sIdeleBlock F ∅ → Idele F) '' (e ⁻¹' (U ×ˢ univ))
  have hw : IsOpen W :=
    (sIdeleBlock_open F ∅).isOpenEmbedding_subtypeVal.isOpenMap
      _ ((hu.prod isOpen_univ).preimage e.continuous)
  have hn : W.Nonempty := by
    obtain ⟨y, hy⟩ := A.interior_nonempty
    let k := j.symm (y, 1)
    have hk : k ∈ U := by
      change j (j.symm (y, 1)) ∈ interior (A : Set (Arch F)) ×ˢ
        Set.pi univ (fun v : (∅ : Finset (Place F)) => finitePlaceIntegralUnits F v.val)
      rw [j.apply_symm_apply]
      exact ⟨hy, fun v _ => False.elim (Finset.notMem_empty _ v.property)⟩
    refine ⟨(e.symm (k, 1)).val, ⟨e.symm (k, 1), ?_, rfl⟩⟩
    change e (e.symm (k, 1)) ∈ U ×ˢ univ
    rw [e.apply_symm_apply]
    exact ⟨hk, mem_univ _⟩
  apply hn.mono
  rw [← hw.interior_eq]
  apply interior_mono
  rw [← reference_image F A ∅]
  exact image_mono (preimage_mono (Set.prod_mono (preimage_mono
    (Set.prod_mono interior_subset Subset.rfl)) Subset.rfl))

private def allIntegralPositiveCompact (A : PositiveCompacts (Arch F)) :
    PositiveCompacts (Idele F) :=
  ⟨⟨allIntegralReference F A, allIntegralReference_isCompact F A⟩,
    allIntegralReference_interior F A⟩

private abbrev discriminantMass : ℝ≥0∞ := (NNReal.sqrt ‖discr F‖₊ : ℝ≥0∞)⁻¹

private theorem discriminantMass_pos : discriminantMass F ≠ 0 :=
  ENNReal.inv_ne_zero.mpr ENNReal.coe_ne_top

private theorem discriminantMass_finite : discriminantMass F ≠ ⊤ := by
  apply ENNReal.inv_ne_top.mpr
  simpa using discr_ne_zero F

private theorem archReference_pos (A : PositiveCompacts (Arch F)) :
    archimedeanMultiplicativeHaar F A ≠ 0 :=
  fun hA => (isOpen_interior.measure_ne_zero _ A.interior_nonempty)
    (measure_mono_null interior_subset hA)

/-- Global Haar measure normalized by an archimedean compact and all
finite integral unit groups. The block formula shows independence of
the reference compact. -/
def globalIdeleProductHaar (A : PositiveCompacts (Arch F)) : Measure (Idele F) :=
  ((archimedeanMultiplicativeHaar F) (A : Set (Arch F)) * discriminantMass F) •
    Measure.haarMeasure (allIntegralPositiveCompact F A)

theorem globalIdeleProductHaar_isHaar (A : PositiveCompacts (Arch F)) :
    (globalIdeleProductHaar F A).IsHaarMeasure := by
  unfold globalIdeleProductHaar
  apply Measure.IsHaarMeasure.smul
  · exact mul_ne_zero (archReference_pos F A) (discriminantMass_pos F)
  · exact ENNReal.mul_ne_top A.isCompact.measure_ne_top (discriminantMass_finite F)

private theorem globalIdeleProductHaar_reference (A : PositiveCompacts (Arch F)) :
    globalIdeleProductHaar F A (allIntegralReference F A) =
      archimedeanMultiplicativeHaar F A * discriminantMass F := by
  rw [globalIdeleProductHaar, Measure.smul_apply, smul_eq_mul]
  change _ * Measure.haarMeasure (allIntegralPositiveCompact F A) (allIntegralPositiveCompact F A) = _
  rw [Measure.haarMeasure_self, mul_one]

private theorem selectedReference_mass (A : PositiveCompacts (Arch F)) (S : Finset (Place F)) :
    sLocalMultiplicativeTamagawa F S (selectedReference F A S) =
      archimedeanMultiplicativeHaar F A * ∏ v : S, differentPrimeMass F v.val := by
  let j := sLocalZetaIdeleCoordinates F S
  let B := Set.pi univ (fun v : S => finitePlaceIntegralUnits F v.val)
  have hm : MeasurableSet B :=
    MeasurableSet.pi countable_univ fun v _ => (localIntegralUnits_open F v.val).measurableSet
  have hA : MeasurableSet (A : Set (Arch F)) := A.isCompact.measurableSet
  unfold sLocalMultiplicativeTamagawa sLocalZetaProductMeasure
  change ((archimedeanMultiplicativeHaar F).prod
    (Measure.pi (fun v : S => finitePlaceMultiplicativeTamagawa F v.val))).map j.symm
      (j ⁻¹' ((A : Set (Arch F)) ×ˢ B)) = _
  have hme : Measurable (⇑j.symm) := j.symm.continuous.measurable
  have hset : MeasurableSet (j ⁻¹' ((A : Set (Arch F)) ×ˢ B)) :=
    j.continuous.measurable (hA.prod hm)
  rw [Measure.map_apply hme hset]
  have he : j.symm ⁻¹' (j ⁻¹' ((A : Set (Arch F)) ×ˢ B)) = (A : Set (Arch F)) ×ˢ B := by
    ext a
    simp
  rw [he, Measure.prod_prod, Measure.pi_pi]
  simp only [finitePlaceMultiplicativeTamagawa_units]

/-- On every open idele block, the global Haar measure is the product
of the selected local Tamagawa measures and normalized Haar on the
integral tail, scaled by the omitted local integral-unit masses. -/
theorem globalIdeleProductHaar_block (A : PositiveCompacts (Arch F)) (S : Finset (Place F)) :
    ((globalIdeleProductHaar F A).comap (Subtype.val : sIdeleBlock F S → Idele F)).map
      (sBlockUnitProduct F S) =
    integralIdeleTailMass F S •
      ((sLocalMultiplicativeTamagawa F S).prod (integralIdeleTailProbability F S)) := by
  let η := globalIdeleProductHaar F A
  letI : η.IsHaarMeasure := globalIdeleProductHaar_isHaar F A
  let e := sBlockUnitProduct F S
  let ρ := η.comap (sIdeleBlock F S).subtype
  let μ := (sLocalMultiplicativeTamagawa F S).prod (integralIdeleTailProbability F S)
  let K := selectedReference F A S ×ˢ (univ : Set (Tail F S))
  letI : ρ.IsHaarMeasure :=
    Measure.IsHaarMeasure.comap (mH := inferInstance) η
      (sIdeleBlock_open F S).isOpenEmbedding_subtypeVal
  letI : (ρ.map e).IsHaarMeasure :=
    e.toMulEquiv.isHaarMeasure_map ρ e.continuous e.symm.continuous
  letI : μ.IsHaarMeasure := Measure.prod.instIsHaarMeasure _ _
  let c := Measure.haarScalarFactor (ρ.map e) μ
  have he : ρ.map e = c • μ := Measure.isMulLeftInvariant_eq_smul _ _
  have hK : IsCompact K := (selectedReference_isCompact F A S).prod isCompact_univ
  have hKmass : μ K = archimedeanMultiplicativeHaar F A * ∏ v : S, differentPrimeMass F v.val := by
    change (((sLocalMultiplicativeTamagawa F S).prod (integralIdeleTailProbability F S))
      (selectedReference F A S ×ˢ univ)) = _
    rw [Measure.prod_prod, integralIdeleTailProbability_univ, mul_one, selectedReference_mass]
  have hμ0 : μ K ≠ 0 := by
    rw [hKmass]
    exact mul_ne_zero (archReference_pos F A)
      (Finset.prod_ne_zero_iff.mpr fun v _ => differentPrimeMass_ne_zero F v.val)
  have hm := congrArg (fun ζ : Measure (Selected F S × Tail F S) => ζ K) he
  change (ρ.map e) K = (c • μ) K at hm
  have hme : Measurable (⇑e) := e.continuous.measurable
  rw [Measure.map_apply hme hK.measurableSet] at hm
  have hMe : MeasurableEmbedding (Subtype.val : sIdeleBlock F S → Idele F) :=
    Topology.IsOpenEmbedding.measurableEmbedding
      (f := (Subtype.val : sIdeleBlock F S → Idele F))
      (sIdeleBlock_open F S).isOpenEmbedding_subtypeVal
  change (η.comap (Subtype.val : sIdeleBlock F S → Idele F)) (e ⁻¹' K) = _ at hm
  rw [hMe.comap_apply η (e ⁻¹' K), reference_image F A S, Measure.coe_nnreal_smul_apply,
    globalIdeleProductHaar_reference] at hm
  have hscale : (c : ℝ≥0∞) = integralIdeleTailMass F S := by
    apply (ENNReal.mul_left_inj hμ0 hK.measure_ne_top).mp
    rw [← hm, hKmass, mul_left_comm, ← mul_assoc]
    rw [mul_assoc, mul_comm (integralIdeleTailMass F S), integralIdeleTailMass,
      differentPrimeMass_split]
  change ρ.map e = integralIdeleTailMass F S • μ
  rw [he, ← hscale]
  rfl

/-- The global measure of any measurable set in an open block can be read
in its selected coordinates and integral tail. -/
theorem globalIdeleProductHaar_block_apply (A : PositiveCompacts (Arch F)) (S : Finset (Place F))
    (B : Set (Selected F S × Tail F S)) (hB : MeasurableSet B) :
    globalIdeleProductHaar F A
      ((Subtype.val : sIdeleBlock F S → Idele F) '' ((sBlockUnitProduct F S) ⁻¹' B)) =
      integralIdeleTailMass F S *
        ((sLocalMultiplicativeTamagawa F S).prod (integralIdeleTailProbability F S)) B := by
  have hi : MeasurableEmbedding (Subtype.val : sIdeleBlock F S → Idele F) :=
    Topology.IsOpenEmbedding.measurableEmbedding
      (f := (Subtype.val : sIdeleBlock F S → Idele F))
      (sIdeleBlock_open F S).isOpenEmbedding_subtypeVal
  have he : Measurable (⇑(sBlockUnitProduct F S)) := (sBlockUnitProduct F S).continuous.measurable
  have h := congrArg (fun ζ : Measure (Selected F S × Tail F S) => ζ B)
    (globalIdeleProductHaar_block F A S)
  rw [Measure.map_apply he hB, hi.comap_apply, Measure.smul_apply, smul_eq_mul] at h
  exact h

/-- Haar uniqueness makes the restricted product independent of the
archimedean compact used to fix its normalization. -/
theorem globalIdeleProductHaar_independent (A B : PositiveCompacts (Arch F)) :
    globalIdeleProductHaar F A = globalIdeleProductHaar F B := by
  let μ := globalIdeleProductHaar F A
  let ν := globalIdeleProductHaar F B
  letI : μ.IsHaarMeasure := globalIdeleProductHaar_isHaar F A
  letI : ν.IsHaarMeasure := globalIdeleProductHaar_isHaar F B
  let D := allIntegralReference F A
  let C := selectedReference F A ∅ ×ˢ (univ : Set (Tail F ∅))
  have hC : MeasurableSet C := ((selectedReference_isCompact F A ∅).prod isCompact_univ).measurableSet
  have hD : μ D = ν D := by
    have hA := globalIdeleProductHaar_block_apply F A ∅ C hC
    have hB := globalIdeleProductHaar_block_apply F B ∅ C hC
    change μ (allIntegralReference F A) = ν (allIntegralReference F A)
    rw [← reference_image F A ∅]
    exact hA.trans hB.symm
  let c := Measure.haarScalarFactor μ ν
  have he : μ = c • ν := Measure.isMulLeftInvariant_eq_smul _ _
  have hd₀ : ν D ≠ 0 := by
    rw [← hD]
    exact (isOpen_interior.measure_ne_zero _ (allIntegralReference_interior F A))
      ∘ measure_mono_null interior_subset
  have h1 : (c : ℝ≥0∞) = 1 := by
    apply (ENNReal.mul_left_inj hd₀ (allIntegralReference_isCompact F A).measure_ne_top).mp
    rw [one_mul, ← Measure.coe_nnreal_smul_apply, ← he, hD]
  have hc : c = 1 := ENNReal.coe_inj.mp (h1.trans ENNReal.coe_one.symm)
  change μ = ν
  rw [he, hc, one_smul]

/-- For a test depending only on the selected coordinates inside an open
block, integrating the omitted unit groups produces exactly their total mass. -/
theorem globalIdeleProductHaar_block_integral (A : PositiveCompacts (Arch F))
    (S : Finset (Place F)) (f : Idele F → ℂ) (g : Selected F S → ℂ)
    (h : ∀ a : sIdeleBlock F S, f a.val = g ((sBlockUnitProduct F S a).1)) :
    (∫ a in (sIdeleBlock F S : Set (Idele F)), f a ∂globalIdeleProductHaar F A) =
      (integralIdeleTailMass F S).toReal • (∫ b, g b ∂sLocalMultiplicativeTamagawa F S) := by
  let η := globalIdeleProductHaar F A
  let e := sBlockUnitProduct F S
  let ρ := η.comap (Subtype.val : sIdeleBlock F S → Idele F)
  have hi : MeasurableEmbedding (Subtype.val : sIdeleBlock F S → Idele F) :=
    Topology.IsOpenEmbedding.measurableEmbedding
      (f := (Subtype.val : sIdeleBlock F S → Idele F))
      (sIdeleBlock_open F S).isOpenEmbedding_subtypeVal
  have he : MeasurableEmbedding (⇑e) := e.toHomeomorph.toMeasurableEquiv.measurableEmbedding
  have hmap : ρ.map Subtype.val = η.restrict (sIdeleBlock F S) := by
    rw [show (sIdeleBlock F S : Set (Idele F)) =
      range (Subtype.val : sIdeleBlock F S → Idele F) from Subtype.range_coe.symm]
    exact hi.map_comap η
  change (∫ a, f a ∂η.restrict (sIdeleBlock F S)) = _
  rw [← hmap, hi.integral_map]
  change (∫ a : sIdeleBlock F S, f a.val ∂ρ) = _
  simp_rw [h]
  have hblock := globalIdeleProductHaar_block F A S
  change ρ.map e = _ at hblock
  rw [← he.integral_map (fun p : Selected F S × Tail F S => g p.1), hblock,
    integral_smul_measure, integral_fun_fst, measureReal_def,
    integralIdeleTailProbability_univ, ENNReal.toReal_one, one_smul]

/-- Finite open blocks exhaust the global integral of an integrable test. -/
theorem globalIdeleProductHaar_integral_tendsto_blocks (A : PositiveCompacts (Arch F))
    {f : Idele F → ℂ} (hf : Integrable f (globalIdeleProductHaar F A)) :
    Tendsto (fun S : Finset (Place F) => ∫ a in (sIdeleBlock F S : Set (Idele F)),
      f a ∂globalIdeleProductHaar F A) atTop (𝓝 (∫ a, f a ∂globalIdeleProductHaar F A)) := by
  let μ := globalIdeleProductHaar F A
  let D (S : Finset (Place F)) : Set (Idele F) := sIdeleBlock F S
  have hm (S : Finset (Place F)) : MeasurableSet (D S) := (sIdeleBlock_open F S).measurableSet
  have ht : Tendsto (fun S : Finset (Place F) => ∫ a, (D S).indicator f a ∂μ)
      atTop (𝓝 (∫ a, f a ∂μ)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun a => ‖f a‖)
      (.of_forall fun S => hf.aestronglyMeasurable.indicator (hm S))
      (.of_forall fun S => .of_forall fun a => ?_) hf.norm ?_
    · by_cases ha : a ∈ D S
      · rw [indicator_of_mem ha]
      · rw [indicator_of_notMem ha, norm_zero]
        exact norm_nonneg _
    · exact Eventually.of_forall fun a => by
        obtain ⟨S, ha⟩ := sIdeleBlock_cover F a
        apply tendsto_const_nhds.congr'
        filter_upwards [eventually_ge_atTop S] with T hT
        exact (indicator_of_mem (show a ∈ D T from sIdeleBlock_mono F hT ha) f).symm
  exact ht.congr' (.of_forall fun S => integral_indicator (hm S))

private abbrev integerEulerTest (S : Finset (Place F))
    (φ : 𝓢(mixedEmbedding.mixedSpace F, ℂ)) :=
  sLocalBruhatPure F S φ (locallyConstantTestPiProduct
    fun v : S => finiteCompletionIntegerRingTest F v.val)

private theorem integerEulerTest_independent (S T : Finset (Place F))
    (φ : 𝓢(mixedEmbedding.mixedSpace F, ℂ)) :
    (integerEulerTest F S φ).val = (integerEulerTest F T φ).val := by
  have h (U : Finset (Place F)) (x : Adeles F) :
      GlobalBruhat.evaluation F x (integerEulerTest F U φ).val =
        φ (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1) *
          (if ∀ v : Place F, x.2 v ∈ v.adicCompletionIntegers F then 1 else 0) := by
    rw [sLocalBruhatRestriction_reconstruct, sLocalBruhatPure_restrict,
      locallyConstantTestPiProduct_apply, mul_assoc]
    have hx (v : U) :
        (finiteCompletionIntegerRingTest F v.val).val ((sAdelesProjection F U x).2 v) =
          if x.2 v.val ∈ v.val.adicCompletionIntegers F then (1 : ℂ) else 0 := rfl
    simp_rw [hx]
    by_cases hs : ∀ v : U, x.2 v.val ∈ v.val.adicCompletionIntegers F
    · have hp : (∏ v : U, if x.2 v.val ∈ v.val.adicCompletionIntegers F then (1 : ℂ) else 0) = 1 :=
        Finset.prod_eq_one (fun v _ => ite_eq_left (hs v))
      have he : (∀ v ∉ U, x.2 v ∈ v.adicCompletionIntegers F) ↔
          ∀ v : Place F, x.2 v ∈ v.adicCompletionIntegers F := by
        refine ⟨fun h v => ?_, fun h v _ => h v⟩
        by_cases hv : v ∈ U
        · exact hs ⟨v, hv⟩
        · exact h v hv
      rw [hp, he, one_mul]
      rfl
    · push Not at hs
      obtain ⟨v, hv⟩ := hs
      rw [Finset.prod_eq_zero (Finset.mem_univ v) (ite_eq_right hv), zero_mul,
        ite_eq_right (fun h => hv (h v.val)), mul_zero, mul_zero]
  apply (GlobalBruhat.algebraicEquiv F).injective
  apply Subtype.ext
  funext x
  exact (h S x).trans (h T x).symm

private theorem localTrivialEulerFactor (S : Finset (Place F)) (v : S) {z : ℂ} (hz : 0 < z.re) :
    finiteZetaIntegral F v.val (finitePlaceMultiplicativeTamagawa F v.val)
        (sLocalFiniteZetaPhases F S 1 v) (finiteCompletionIntegerRingTest F v.val) z =
      (differentPrimeMass F v.val).toReal *
        (1 - (v.val.asIdeal.absNorm : ℂ) ^ (-z))⁻¹ := by
  have he (u : Local F v.val) : sLocalFiniteZetaPhases F S 1 v u = 1 := by
    apply Circle.coe_injective
    change sLocalZetaWeight F S 1 0 (QuotientGroup.mk (sLocalFiniteZetaInsert F S v u)) = 1
    simp [sLocalZetaWeight]
  rw [finiteZetaIntegral_integerRing_unramified F v.val _ _ (fun u _ => he u) z hz,
    finiteZetaRatio, he, Circle.coe_one, one_mul, measureReal_def, finitePlaceMultiplicativeTamagawa_units]
  congr 3
  have hp : (0 : ℝ) < v.val.asIdeal.absNorm := by
    exact_mod_cast (NumberField.HeightOneSpectrum.one_lt_absNorm v.val).trans' Nat.zero_lt_one
  rw [← Complex.ofReal_natCast,
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hp.ne'),
    ← Complex.ofReal_log hp.le, mul_comm]

private theorem trivialArchZeta_independent (S T : Finset (Place F))
    (φ : 𝓢(mixedEmbedding.mixedSpace F, ℂ)) (z : ℂ) :
    sLocalArchZetaIntegral F S (archimedeanMultiplicativeHaar F) 1 φ z =
      sLocalArchZetaIntegral F T (archimedeanMultiplicativeHaar F) 1 φ z := by
  have hn (U : Finset (Place F)) (a : Arch F) :
      sLocalZetaWeight F U 1 z (QuotientGroup.mk (sLocalArchZetaInsert F U a)) =
        Complex.exp (z * (Real.log (∏ v : InfinitePlace F, ‖a.val v‖ ^ v.mult) : ℂ)) := by
    let q : SIdeleQuotient F U := QuotientGroup.mk (sLocalArchZetaInsert F U a)
    let p := (sLocalZetaSplit F U).symm q
    have h := sLocalZetaSplit_logModulus F U p
    rw [(sLocalZetaSplit F U).apply_symm_apply q] at h
    have hm : sLocalClassModulus F U q = ∏ v : InfinitePlace F, ‖a.val v‖ ^ v.mult := by
      change sLocalIdeleNorm F U (sLocalArchZetaInsert F U a) = _
      unfold sLocalArchZetaInsert
      rw [sLocalZetaIdeleCoordinates_norm]
      simp
    change Complex.exp (z * (p.1 : ℂ)) * ((1 : PontryaginDual _) p.2 : ℂ) = _
    rw [← h, hm, PontryaginDual.one_apply, Circle.coe_one, mul_one]
  unfold sLocalArchZetaIntegral
  simp_rw [hn]

/-- The integer-ring test at all finite places gives the Dedekind Euler
product on the half-plane of absolute convergence, with the exact global
discriminant scale from the Tamagawa factors. -/
theorem globalIdeleProductHaar_trivialEuler (A : PositiveCompacts (Arch F))
    (φ : 𝓢(mixedEmbedding.mixedSpace F, ℂ)) {z : ℂ} (hz : 1 < z.re) :
    idelicZetaIntegral F (globalIdeleProductHaar F A)
      (GlobalBruhat.algebraicEquiv F (integerEulerTest F ∅ φ).val).val
      (compactIdeleClassCharacter F 1) z =
    (discriminantMass F).toReal *
      (sLocalArchZetaIntegral F ∅ (archimedeanMultiplicativeHaar F) 1 φ z * dedekindZeta F z) := by
  let η := globalIdeleProductHaar F A
  letI : η.IsHaarMeasure := globalIdeleProductHaar_isHaar F A
  let f := (integerEulerTest F ∅ φ).val
  let g := globalMellinIntegrand F 1 f z
  obtain ⟨ν, hν, hweil⟩ := globalClassMeasure_exists_weil F η
  letI := hν
  have hg : Integrable g η := (idelicZeta_integrable_eq_theta F η ν hweil f
    (compactIdeleClassCharacter F 1) (compactIdeleClassCharacter_unitary F 1) z hz).1
  have hL := globalIdeleProductHaar_integral_tendsto_blocks F A hg
  let C := (discriminantMass F).toReal *
    sLocalArchZetaIntegral F ∅ (archimedeanMultiplicativeHaar F) 1 φ z
  let P (v : Place F) := (1 - (v.asIdeal.absNorm : ℂ) ^ (-z))⁻¹
  have hprod : Tendsto (fun S : Finset (Place F) => ∏ v ∈ S, P v) atTop (𝓝 (dedekindZeta F z)) :=
    dedekindZeta_hasProd F hz
  have hR := hprod.const_mul C
  have htarget : Tendsto (fun S : Finset (Place F) =>
      ∫ a in (sIdeleBlock F S : Set (Idele F)), g a ∂η) atTop (𝓝 (C * dedekindZeta F z)) := by
    apply hR.congr'
    obtain ⟨S₀, hS₀⟩ := sIdeleClass_eventually_surjective F
    filter_upwards [eventually_ge_atTop S₀] with S hS
    have hs := hS₀ S hS
    have hu : globalNormOneCharacter F 1 ∈
        (sUnramified F S : Set (QuasiCharacter (IdeleClass F))) := by
      change (globalNormOneCharacter F 1).comp (classOfTail F S) = 1
      ext a
      change ((1 : PontryaginDual (normOneIdeleClass F))
        (ideleClassNormOnePart F (classOfTail F S a)) : ℂ) = 1
      rw [PontryaginDual.one_apply, Circle.coe_one]
    let q := integerEulerTest F S φ
    have hq : q.val = f := integerEulerTest_independent F S ∅ φ
    have hw (a : sIdeleBlock F S) :
        g a.val = sLocalIdelicZetaIntegrand F S 1 z q (sBlockUnitProduct F S a).1 := by
      rw [← sLocalNormOneCharacterOfGlobal_trivial F S hs hu]
      change globalMellinIntegrand F 1 f z a.val = _
      rw [← hq]
      exact globalMellinIntegrand_on_block F 1 S hs hu q z a
    change C * (∏ v ∈ S, P v) = _
    rw [globalIdeleProductHaar_block_integral F A S g _ hw]
    change _ = (integralIdeleTailMass F S).toReal •
      sLocalIdelicZetaIntegral F S (sLocalMultiplicativeTamagawa F S) 1 q z
    unfold sLocalMultiplicativeTamagawa
    rw [sLocalIdelicZetaIntegral_pure_product _ _ _ _ _ _ _ _ (zero_lt_one.trans hz)]
    simp_rw [localTrivialEulerFactor F S (hz := zero_lt_one.trans hz), Finset.prod_mul_distrib]
    rw [trivialArchZeta_independent F S ∅]
    have hm : ((integralIdeleTailMass F S).toReal : ℂ) *
        ∏ v : S, ((differentPrimeMass F v.val).toReal : ℂ) = (discriminantMass F).toReal := by
      rw [← Complex.ofReal_prod, ← Complex.ofReal_mul, ← ENNReal.toReal_prod, ← ENNReal.toReal_mul,
        mul_comm, integralIdeleTailMass, differentPrimeMass_split]
    have hp : (∏ v : S, P v.val) = ∏ v ∈ S, P v := (Finset.prod_subtype S (fun _ => Iff.rfl) P).symm
    change _ = _ • (_ * ((∏ v : S, ((differentPrimeMass F v.val).toReal : ℂ)) *
      ∏ v : S, P v.val))
    rw [hp, Complex.real_smul]
    dsimp only [C]
    rw [← hm]
    ring
  change (∫ a, g a ∂η) = _
  simpa only [C, mul_assoc] using tendsto_nhds_unique hL htarget

/-- The restricted product gives the class-number-formula mass on the
norm-one classes with counting on the principal ideles and log Lebesgue
measure on the norm coordinate. -/
theorem globalIdeleProductHaar_normOne_mass (A : PositiveCompacts (Arch F))
    (ν : Measure (normOneIdeleClass F)) [ν.IsHaarMeasure]
    (hweil : IsWeilQuotientMeasure (principalIdeles F) (globalIdeleProductHaar F A)
      Measure.count (globalClassMeasure F ν)) :
    ν.real univ = dedekindZeta_residue F := by
  let η := globalIdeleProductHaar F A
  letI : η.IsHaarMeasure := globalIdeleProductHaar_isHaar F A
  obtain ⟨φ, hφ, hI, _, hΓ⟩ := exists_trivialArchGamma_reference_exact F ∅
  let r := (integerEulerTest F ∅ φ).val
  let d : ℂ := (discriminantMass F).toReal
  have hd : d ≠ 0 := Complex.ofReal_ne_zero.mpr
    (ENNReal.toReal_ne_zero.mpr ⟨discriminantMass_pos F, discriminantMass_finite F⟩)
  apply normOneHaar_mass_of_trivialEuler_reference F η ν hweil r d hd
  · change GlobalBruhat.evaluation F 0
      (GlobalBruhat.fourier F (integerEulerTest F ∅ φ).val) = _
    rw [trivialEuler_reference_fourier_origin F ∅ φ, hI, hφ]
  · intro t ht
    have ht' : 1 < (t : ℂ).re := by simpa only [Complex.ofReal_re] using ht
    rw [globalIdeleProductHaar_trivialEuler F A φ ht',
      ← archimedeanNumberFieldZeta_eq_sLocalArchZetaIntegral F ∅ 1 φ (zero_lt_one.trans ht'),
      hΓ _ (zero_lt_one.trans ht')]

/-- Lemma A.3.2.4. The Haar measure specified by the numerical norm-one
volume of (A.3.2.1) equals the restricted product in (A.3.2.5). -/
theorem globalIdeleTamagawa_eq_restrictedProduct_on_reference (A : PositiveCompacts (Arch F))
    (η : Measure (Idele F)) [η.IsHaarMeasure]
    (ν : Measure (normOneIdeleClass F)) [ν.IsHaarMeasure]
    (hweil : IsWeilQuotientMeasure (principalIdeles F) η Measure.count (globalClassMeasure F ν))
    (hmass : ν.real univ = dedekindZeta_residue F) :
    η = globalIdeleProductHaar F A := by
  let η₀ := globalIdeleProductHaar F A
  letI : η₀.IsHaarMeasure := globalIdeleProductHaar_isHaar F A
  obtain ⟨ν₀, hν₀, hweil₀⟩ := globalClassMeasure_exists_weil F η₀
  letI := hν₀
  have hmass₀ := globalIdeleProductHaar_normOne_mass F A ν₀ hweil₀
  letI : CompactSpace (normOneIdeleClass F) := normOneIdeleClass_compact F
  letI : SecondCountableTopology (IdeleClass F) :=
    TopologicalSpace.Quotient.secondCountableTopology
      (QuotientGroup.isOpenMap_coe (N := principalIdeles F))
  letI : SecondCountableTopology (normOneIdeleClass F) :=
    IsEmbedding.subtypeVal.secondCountableTopology
  letI : T2Space (IdeleClass F) := ideleClasses_hausdorff
  have hmass' : ν univ = ν₀ univ :=
    (ENNReal.toReal_eq_toReal_iff' isCompact_univ.measure_ne_top isCompact_univ.measure_ne_top).mp
      (hmass.trans hmass₀.symm)
  let c := Measure.haarScalarFactor ν ν₀
  have he : ν = c • ν₀ := Measure.isMulLeftInvariant_eq_smul _ _
  have hne : ν₀ univ ≠ 0 := isOpen_univ.measure_ne_zero ν₀ univ_nonempty
  have hcE : (c : ℝ≥0∞) = 1 := by
    apply (ENNReal.mul_left_inj hne isCompact_univ.measure_ne_top).mp
    rw [one_mul, ← Measure.coe_nnreal_smul_apply, ← he, hmass']
  have hc : c = 1 := ENNReal.coe_inj.mp (hcE.trans ENNReal.coe_one.symm)
  have hν : ν = ν₀ := by rw [he, hc, one_smul]
  rw [hν] at hweil
  letI : η.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _
  letI : η₀.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _
  change η = η₀
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  let fc : C(Idele F, ℂ) := ⟨fun a => (f a : ℂ), Complex.continuous_ofReal.comp f.continuous⟩
  have hfc : HasCompactSupport fc := f.hasCompactSupport.comp_left Complex.ofReal_zero
  apply Complex.ofReal_injective
  simpa only [fc, ContinuousMap.coe_mk, integral_complex_ofReal] using
    (hweil.2.2 fc hfc).trans (hweil₀.2.2 fc hfc).symm

private def ideleTamagawaReference : PositiveCompacts (Arch F) := by
  letI : LocallyCompactSpace ℝˣ := IsOpenUnits.isOpenEmbedding_unitsVal.locallyCompactSpace
  letI : LocallyCompactSpace ℂˣ := IsOpenUnits.isOpenEmbedding_unitsVal.locallyCompactSpace
  letI : LocallyCompactSpace (Arch F) :=
    (infiniteAdeleUnitsCoordinates F).toHomeomorph.isOpenEmbedding.locallyCompactSpace
  exact Classical.choice (inferInstance : Nonempty (PositiveCompacts (Arch F)))

/-- The restricted product of the local multiplicative Tamagawa measures,
using the global different for the finite integral-unit masses. -/
def globalIdeleTamagawa : Measure (Idele F) :=
  globalIdeleProductHaar F (ideleTamagawaReference F)

theorem globalIdeleTamagawa_isHaar : (globalIdeleTamagawa F).IsHaarMeasure :=
  globalIdeleProductHaar_isHaar F _

/-- The product measure admits the Weil quotient with the prescribed mass. -/
theorem globalIdeleTamagawa_exists_weil :
    ∃ (ν : Measure (normOneIdeleClass F)) (_ : ν.IsHaarMeasure),
      IsWeilQuotientMeasure (principalIdeles F) (globalIdeleTamagawa F)
        Measure.count (globalClassMeasure F ν) ∧
      ν.real univ = dedekindZeta_residue F := by
  letI : (globalIdeleTamagawa F).IsHaarMeasure := globalIdeleTamagawa_isHaar F
  obtain ⟨ν, hν, hweil⟩ := globalClassMeasure_exists_weil F (globalIdeleTamagawa F)
  letI := hν
  exact ⟨ν, hν, hweil, globalIdeleProductHaar_normOne_mass F _ ν hweil⟩

theorem globalIdeleTamagawa_block (S : Finset (Place F)) :
    ((globalIdeleTamagawa F).comap (Subtype.val : sIdeleBlock F S → Idele F)).map
      (sBlockUnitProduct F S) =
    integralIdeleTailMass F S •
      ((sLocalMultiplicativeTamagawa F S).prod (integralIdeleTailProbability F S)) :=
  globalIdeleProductHaar_block F _ S

/-- Integration of a selected-coordinate test on a block with the canonical
Tamagawa normalization. -/
theorem globalIdeleTamagawa_block_integral (S : Finset (Place F))
    (f : Idele F → ℂ) (g : Selected F S → ℂ)
    (h : ∀ a : sIdeleBlock F S, f a.val = g ((sBlockUnitProduct F S a).1)) :
    (∫ a in (sIdeleBlock F S : Set (Idele F)), f a ∂globalIdeleTamagawa F) =
      (integralIdeleTailMass F S).toReal • (∫ b, g b ∂sLocalMultiplicativeTamagawa F S) :=
  globalIdeleProductHaar_block_integral F _ S f g h

/-- The open blocks exhaust the canonical Tamagawa integral of an
integrable function. -/
theorem globalIdeleTamagawa_integral_tendsto_blocks {f : Idele F → ℂ}
    (hf : Integrable f (globalIdeleTamagawa F)) :
    Tendsto (fun S : Finset (Place F) => ∫ a in (sIdeleBlock F S : Set (Idele F)),
      f a ∂globalIdeleTamagawa F) atTop (𝓝 (∫ a, f a ∂globalIdeleTamagawa F)) :=
  globalIdeleProductHaar_integral_tendsto_blocks F _ hf

/-- Lemma A.3.2.4 with the finite masses read from the global different.
The norm-one quotient mass uniquely fixes the restricted product. -/
theorem globalIdeleTamagawa_eq_restrictedProduct
    (η : Measure (Idele F)) [η.IsHaarMeasure]
    (ν : Measure (normOneIdeleClass F)) [ν.IsHaarMeasure]
    (hweil : IsWeilQuotientMeasure (principalIdeles F) η Measure.count (globalClassMeasure F ν))
    (hmass : ν.real univ = dedekindZeta_residue F) :
    η = globalIdeleTamagawa F :=
  globalIdeleTamagawa_eq_restrictedProduct_on_reference F _ η ν hweil hmass

end
end Masullo
