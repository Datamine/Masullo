import WeilOpenSubgroup
import FilteredQuotientIndentation
import SLocalIdelic
import SUnitRank
import NormOneExact

open Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped NumberField

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

local instance : LocallyCompactSpace (Idele F) := ideles_locallyCompact
local instance : T2Space (Idele F) := ideles_hausdorff
local instance : MeasurableSpace (Idele F) := borel _
local instance : BorelSpace (Idele F) := ⟨rfl⟩
local instance : MeasurableSpace (IdeleClass F) := borel _

/-- The intersection of global principal ideles with an S-block consists
exactly of the S-principal ideles. -/
theorem sPrincipal_range_eq_principal_comap (S : Finset (HeightOneSpectrum (𝓞 F))) :
    (sPrincipal F S).range = (principalIdeles F).comap (sIdeleBlock F S).subtype := by
  ext x
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨sUnitToField F S u, rfl⟩
  · rintro ⟨t, ht⟩
    have hmem : principalIdele F t ∈ sIdeleBlock F S := ht.symm ▸ x.property
    let u : (sIntegerRing F S)ˣ :=
      ⟨⟨t.val, hmem.1⟩, ⟨t.inv, hmem.2⟩, Subtype.ext t.val_inv, Subtype.ext t.inv_val⟩
    have hu : sUnitToField F S u = t := Units.ext rfl
    refine ⟨u, Subtype.ext ?_⟩
    change principalIdele F (sUnitToField F S u) = x.val
    rw [hu]
    exact ht

local instance (S : Finset (HeightOneSpectrum (𝓞 F))) :
    MeasurableSpace (SIdeleClass F S) := borel _

/-- Restricting global idelic Haar to the S-block and retaining counting
measure on principal ideles gives exactly the restriction of the global
Weil quotient measure to the S-local idele class group. -/
theorem sIdeleClass_isWeilQuotientMeasure_comap
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (μ : Measure (Idele F)) (ν : Measure (IdeleClass F))
    (hν : IsWeilQuotientMeasure (principalIdeles F) μ Measure.count ν) :
    IsWeilQuotientMeasure (sPrincipal F S).range (μ.comap (sIdeleBlock F S).subtype)
      Measure.count (ν.comap (sIdeleClassInclusion F S)) := by
  letI := principalIdeles_discrete (F := F)
  letI : (Measure.count : Measure (principalIdeles F)).IsHaarMeasure :=
    subgroup_count_isHaarMeasure (principalIdeles F)
  let J := sIdeleBlock F S
  let K := (sPrincipal F S).range
  have hK : K = (principalIdeles F).comap J.subtype := sPrincipal_range_eq_principal_comap F S
  have hi : QuotientGroup.map K (principalIdeles F) J.subtype hK.le =
      sIdeleClassInclusion F S := by
    apply MonoidHom.ext
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    rfl
  have h := isWeilQuotientMeasure_count_comap_openSubgroup (principalIdeles F) J
    (sIdeleBlock_open F S) K hK μ ν hν
  rw [hi] at h
  exact h

/-- Norm-one ideles lying in the S-block form an open subgroup. -/
abbrev normOneIdeleBlock (S : Finset (HeightOneSpectrum (𝓞 F))) : Subgroup (NormOneIdeles F) :=
  (sIdeleBlock F S).comap (ideleNorm F).ker.subtype

theorem normOneIdeleBlock_open (S : Finset (HeightOneSpectrum (𝓞 F))) :
    IsOpen (normOneIdeleBlock F S : Set (NormOneIdeles F)) :=
  (sIdeleBlock_open F S).preimage continuous_subtype_val

local instance : LocallyCompactSpace (NormOneIdeles F) :=
  (show IsClosed ((ideleNorm F).ker : Set (Idele F)) from
    isClosed_singleton.preimage (ideleNorm_continuous F)).isClosedEmbedding_subtypeVal.locallyCompactSpace
local instance : MeasurableSpace (NormOneIdeles F) := borel _
local instance : BorelSpace (NormOneIdeles F) := ⟨rfl⟩
local instance : MeasurableSpace (NormOneIdeles F ⧸ (principalNormOne F).range) := borel _
local instance (S : Finset (HeightOneSpectrum (𝓞 F))) : MeasurableSpace
    (normOneIdeleBlock F S ⧸ (principalNormOne F).range.comap (normOneIdeleBlock F S).subtype) := borel _

/-- At norm one the same restriction preserves Weil normalization,
including the counting measure on the intersection with the principal fibre. -/
theorem normOneIdeleBlock_isWeilQuotientMeasure_comap
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (μ : Measure (NormOneIdeles F))
    (ν : Measure (NormOneIdeles F ⧸ (principalNormOne F).range))
    (hν : IsWeilQuotientMeasure (principalNormOne F).range μ Measure.count ν) :
    let J := normOneIdeleBlock F S
    let H := (principalNormOne F).range
    let K := H.comap J.subtype
    IsWeilQuotientMeasure K (μ.comap J.subtype) Measure.count
      (ν.comap (QuotientGroup.map K H J.subtype le_rfl)) := by
  dsimp only
  let H := (principalNormOne F).range
  let J := normOneIdeleBlock F S
  letI : DiscreteTopology H := (principalNormOne_closed_discrete F).2
  letI : (Measure.count : Measure H).IsHaarMeasure := subgroup_count_isHaarMeasure H
  exact isWeilQuotientMeasure_count_comap_openSubgroup H J (normOneIdeleBlock_open F S)
    (H.comap J.subtype) rfl μ ν hν

section NormOneComparison

variable (S : Finset (HeightOneSpectrum (𝓞 F)))

/-- The quotient map on the norm-one part of the S-block. -/
def normOneIdeleBlockToClasses : normOneIdeleBlock F S →* sNormOneClass F S :=
  { toFun := fun x => ⟨QuotientGroup.mk ⟨x.val.val, x.property⟩, x.val.property⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }

theorem normOneIdeleBlockToClasses_openQuotient :
    IsOpenQuotientMap (normOneIdeleBlockToClasses F S) := by
  let q := QuotientGroup.mk' (sPrincipal F S).range
  let P := (sNormOneClass F S).comap q
  let e : normOneIdeleBlock F S ≃ₜ* P :=
    { toFun := fun x => ⟨⟨x.val.val, x.property⟩, x.val.property⟩
      invFun := fun x => ⟨⟨x.val.val, x.property⟩, x.val.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      continuous_toFun := ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _).subtype_mk _
      continuous_invFun := ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _).subtype_mk _ }
  have hq : IsOpenQuotientMap q := QuotientGroup.isOpenQuotientMap_mk
  exact (hq.restrictPreimage (sNormOneClass F S : Set (SIdeleClass F S))).comp
    e.toHomeomorph.isOpenQuotientMap

theorem normOneIdeleBlockToClasses_ker :
    (normOneIdeleBlockToClasses F S).ker =
      (principalNormOne F).range.comap (normOneIdeleBlock F S).subtype := by
  ext x
  let y : sIdeleBlock F S := ⟨x.val.val, x.property⟩
  change normOneIdeleBlockToClasses F S x = 1 ↔
    x.val ∈ (principalNormOne F).range
  have hx : normOneIdeleBlockToClasses F S x = 1 ↔
      y ∈ (sPrincipal F S).range :=
    (show normOneIdeleBlockToClasses F S x = 1 ↔
      (QuotientGroup.mk y : SIdeleClass F S) = 1 from Subtype.ext_iff).trans
      (QuotientGroup.eq_one_iff y)
  rw [hx, sPrincipal_range_eq_principal_comap, ← normOneIdelesToClasses_ker]
  change x.val.val ∈ principalIdeles F ↔ normOneIdelesToClasses F x.val = 1
  rw [← QuotientGroup.eq_one_iff (N := principalIdeles F)]
  change ideleClassMap F x.val.val = (1 : IdeleClass F) ↔ normOneIdelesToClasses F x.val = 1
  constructor
  · intro h
    apply Subtype.ext
    exact h
  · intro h
    exact congrArg (fun c : normOneIdeleClass F => c.val) h

set_option maxHeartbeats 2500000 in
/-- The local norm-one class group is the quotient of the norm-one S-block
by the intersection with the principal norm-one ideles. -/
def normOneIdeleBlock_quotientEquiv :
    (normOneIdeleBlock F S ⧸ (principalNormOne F).range.comap (normOneIdeleBlock F S).subtype)
      ≃ₜ* sNormOneClass F S := by
  let m := normOneIdeleBlockToClasses F S
  let K := (principalNormOne F).range.comap (normOneIdeleBlock F S).subtype
  let q := QuotientGroup.mk' K
  have hm := normOneIdeleBlockToClasses_openQuotient F S
  let e := (QuotientGroup.quotientMulEquivOfEq (normOneIdeleBlockToClasses_ker F S).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective m hm.surjective)
  have he : e ∘ q = m := funext fun a => by
    change QuotientGroup.quotientKerEquivOfSurjective m hm.surjective
      (QuotientGroup.quotientMulEquivOfEq (normOneIdeleBlockToClasses_ker F S).symm
        (QuotientGroup.mk a)) = _
    rw [QuotientGroup.quotientMulEquivOfEq_mk]
    rfl
  have hc : Continuous e := QuotientGroup.isOpenQuotientMap_mk.continuous_comp_iff.mp
    (he.symm ▸ hm.continuous)
  have ho : IsOpenMap e := IsOpenMap.of_comp QuotientGroup.continuous_mk
    QuotientGroup.mk_surjective (he.symm ▸ hm.isOpenMap)
  exact ⟨e, hc, (e.toEquiv.toHomeomorphOfContinuousOpen hc ho).continuous_invFun⟩

@[simp] theorem normOneIdeleBlock_quotientEquiv_mk (a : normOneIdeleBlock F S) :
    normOneIdeleBlock_quotientEquiv F S (QuotientGroup.mk a) = normOneIdeleBlockToClasses F S a := by
  change QuotientGroup.quotientKerEquivOfSurjective (normOneIdeleBlockToClasses F S)
    (normOneIdeleBlockToClasses_openQuotient F S).surjective
    (QuotientGroup.quotientMulEquivOfEq (normOneIdeleBlockToClasses_ker F S).symm
      (QuotientGroup.mk a)) = _
  rw [QuotientGroup.quotientMulEquivOfEq_mk]
  rfl

@[simp] theorem normOneClass_quotientEquiv_mk (a : NormOneIdeles F) :
    normOneClass_quotientEquiv F (QuotientGroup.mk a) = normOneIdelesToClasses F a := by
  change QuotientGroup.quotientKerEquivOfSurjective (normOneIdelesToClasses F)
    (normOneIdelesToClasses_openQuotient F).surjective
    (QuotientGroup.quotientMulEquivOfEq (normOneIdelesToClasses_ker F).symm
      (QuotientGroup.mk a)) = _
  rw [QuotientGroup.quotientMulEquivOfEq_mk]
  rfl

/-- The quotient comparison is the norm-one restriction of the actual
S-local inclusion into global idele classes. -/
theorem normOneIdeleBlock_quotientEquiv_inclusion
    (q : normOneIdeleBlock F S ⧸ (principalNormOne F).range.comap (normOneIdeleBlock F S).subtype) :
    sIdeleClassInclusion F S (normOneIdeleBlock_quotientEquiv F S q).val =
      (normOneClass_quotientEquiv F
        (QuotientGroup.map _ (principalNormOne F).range (normOneIdeleBlock F S).subtype le_rfl q)).val := by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
  rw [normOneIdeleBlock_quotientEquiv_mk, QuotientGroup.map_mk, normOneClass_quotientEquiv_mk]
  rfl

end NormOneComparison

end
end Masullo
