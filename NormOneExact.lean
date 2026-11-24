import IdelicFundamentalDomain
import Mathlib.Topology.LocalAtTarget

open Function IsDedekindDomain NumberField Set Topology
open scoped Classical NumberField

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

/-- The canonical map between the two norm-one groups. -/
def normOneIdelesToClasses : NormOneIdeles F →* normOneIdeleClass F :=
  ((ideleClassMap F).comp (ideleNorm F).ker.subtype).codRestrict (normOneIdeleClass F)
    (fun a => a.property)

theorem normOneIdelesToClasses_openQuotient :
    IsOpenQuotientMap (normOneIdelesToClasses F) := by
  have h : IsOpenQuotientMap (ideleClassMap F) := QuotientGroup.isOpenQuotientMap_mk
  exact h.restrictPreimage (normOneIdeleClass F : Set (IdeleClass F))

theorem normOneIdelesToClasses_ker :
    (normOneIdelesToClasses F).ker = (principalNormOne F).range := by
  ext a
  change normOneIdelesToClasses F a = 1 ↔ _
  have he : normOneIdelesToClasses F a = 1 ↔ ideleClassMap F a.val = 1 := by
    constructor
    · exact fun h => congrArg (fun c : normOneIdeleClass F => c.val) h
    · intro h
      apply Subtype.ext
      exact h
  rw [he]
  change QuotientGroup.mk a.val = (1 : IdeleClass F) ↔ _
  rw [QuotientGroup.eq_one_iff]
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨t, Subtype.ext ht⟩
  · rintro ⟨t, ht⟩
    exact ⟨t, congrArg Subtype.val ht⟩

instance principalNormOne_range_normal : (principalNormOne F).range.Normal := by
  rw [← normOneIdelesToClasses_ker]
  infer_instance

theorem principalNormOne_closed_discrete :
    IsClosed ((principalNormOne F).range : Set (NormOneIdeles F)) ∧
      DiscreteTopology ((principalNormOne F).range) := by
  have hr : ((principalNormOne F).range : Set (NormOneIdeles F)) =
      Subtype.val ⁻¹' (principalIdeles F : Set (Idele F)) := by
    ext a
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨t, rfl⟩
    · rintro ⟨t, ht⟩
      exact ⟨t, Subtype.ext ht⟩
  have h : IsClosed ((principalNormOne F).range : Set (NormOneIdeles F)) :=
    hr ▸ (principalIdeles_closed (F := F)).preimage continuous_subtype_val
  letI := principalIdeles_discrete (F := F)
  let i (a : (principalNormOne F).range) : principalIdeles F :=
    ⟨a.val.val, show a.val ∈ Subtype.val ⁻¹' (principalIdeles F : Set (Idele F)) from hr ▸ a.property⟩
  have hi : Continuous i := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  exact ⟨h, DiscreteTopology.of_continuous_injective hi
      (fun _ _ e => Subtype.ext (Subtype.ext (congrArg (fun p : principalIdeles F => p.val) e)))⟩

/-- The strict exact sequence at norm one, with the actual topological quotient. -/
def normOneClass_quotientEquiv :
    (NormOneIdeles F ⧸ (principalNormOne F).range) ≃ₜ* normOneIdeleClass F := by
  let m := normOneIdelesToClasses F
  let q := QuotientGroup.mk' (principalNormOne F).range
  let h := normOneIdelesToClasses_openQuotient F
  let e := (QuotientGroup.quotientMulEquivOfEq (normOneIdelesToClasses_ker F).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective m h.surjective)
  have he : e ∘ q = m := funext fun a => by
    change QuotientGroup.quotientKerEquivOfSurjective m h.surjective
      (QuotientGroup.quotientMulEquivOfEq (normOneIdelesToClasses_ker F).symm (QuotientGroup.mk a)) = _
    rw [QuotientGroup.quotientMulEquivOfEq_mk]
    rfl
  have hc : Continuous e := QuotientGroup.isOpenQuotientMap_mk.continuous_comp_iff.mp (he.symm ▸ h.continuous)
  have ho : IsOpenMap e := IsOpenMap.of_comp QuotientGroup.continuous_mk
    QuotientGroup.mk_surjective (he.symm ▸ h.isOpenMap)
  exact
    { toMulEquiv := e
      continuous_toFun := hc
      continuous_invFun := (e.toEquiv.toHomeomorphOfContinuousOpen hc ho).continuous_invFun }

theorem principalNormOne_injective : Injective (principalNormOne F) :=
  fun _ _ h => principalIdele_injective F (congrArg Subtype.val h)

end

end Masullo
