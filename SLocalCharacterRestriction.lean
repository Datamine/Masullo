/-
Adapted from the Apache-2.0 RiemannMasullo project, commit
cd84b23dd5e4f741037cf31aee06bc90161c6514.
See External/PROVENANCE.md and External/RiemannMasullo.LICENSE.
-/
import NormTwistCharts
import SLocalFundamentalDomain
import Mathlib.Algebra.Category.Grp.Injective
import Mathlib.Analysis.Complex.Polynomial.Basic

open Function IsDedekindDomain NumberField Set Topology
open scoped Classical ContDiff Manifold NNReal NumberField RestrictedProduct

namespace Masullo

noncomputable section

/-- A continuous complex character on an open subgroup of an abelian topological group
extends to the full group. Algebraically the complex units are divisible, and continuity
on the open subgroup gives continuity at the identity. -/
theorem exists_complexCharacter_extension_of_isOpenEmbedding {G H : Type*}
    [CommGroup G] [CommGroup H] [TopologicalSpace G] [TopologicalSpace H] [IsTopologicalGroup H]
    (i : G →* H) (hi : IsOpenEmbedding i) (c : G →ₜ* ℂ) :
    ∃ C : H →ₜ* ℂ, ∀ g, C (i g) = c g := by
  let : DivisibleBy (Additive ℂˣ) ℕ := divisibleByOfSMulRightSurj _ _ fun {n} hn u ↦ by
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (u.toMul : ℂ) (Nat.pos_of_ne_zero hn)
    have hz₀ : z ≠ 0 := fun h ↦ u.toMul.ne_zero (by simpa [h, zero_pow hn] using hz.symm)
    exact ⟨Additive.ofMul (Units.mk0 z hz₀), congrArg Additive.ofMul (Units.ext hz)⟩
  let := AddGroup.divisibleByIntOfDivisibleByNat (Additive ℂˣ)
  let q := c.toMonoidHom.toHomUnits
  obtain ⟨L, hL⟩ := (Module.Baer.of_divisible (Additive ℂˣ)).extension_property_addMonoidHom
    i.toAdditive hi.injective q.toAdditive
  let C : H →* ℂˣ := MonoidHom.toAdditive.symm L
  have hC (g : G) : C (i g) = q g := DFunLike.congr_fun hL (Additive.ofMul g)
  have hcont : Continuous C := by
    apply continuous_of_continuousAt_one
    rw [← i.map_one, ← hi.continuousAt_iff]
    rw [show (C ∘ i) = q from funext hC]
    have hq : Continuous q := Units.isEmbedding_val₀.continuous_iff.mpr c.continuous
    exact hq.continuousAt
  exact ⟨⟨(Units.coeHom ℂ).comp C, Units.continuous_val.comp hcont⟩, fun g ↦
    congrArg Units.val (hC g)⟩


/-- The units of a compact Hausdorff topological monoid form a compact space. -/
theorem compactSpace_units_of_compactSpace (M : Type*) [Monoid M]
    [TopologicalSpace M] [T2Space M] [ContinuousMul M] [CompactSpace M] :
    CompactSpace Mˣ := by
  refine IsClosedEmbedding.compactSpace ⟨Units.isEmbedding_embedProduct, ?_⟩
  have hrange : Set.range (Units.embedProduct M) =
      {p | p.1 * MulOpposite.unop p.2 = 1} ∩ {p | MulOpposite.unop p.2 * p.1 = 1} := by
    ext p
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨u.val_inv, u.inv_val⟩
    · rintro ⟨h, h'⟩
      exact ⟨⟨p.1, MulOpposite.unop p.2, h, h'⟩, by cases p; rfl⟩
  rw [hrange]
  exact (isClosed_eq (continuous_fst.mul (MulOpposite.continuous_unop.comp continuous_snd))
    continuous_const).inter (isClosed_eq
      ((MulOpposite.continuous_unop.comp continuous_snd).mul continuous_fst) continuous_const)

/-- If a monoid embeds with closed image, the induced map on units also has closed image.
Both a unit and its inverse must lift to the original monoid. -/
theorem isClosed_range_unitsMap {M N : Type*} [Monoid M] [Monoid N] [TopologicalSpace N]
    (f : M →* N) (hf : Function.Injective f) (hc : IsClosed (Set.range f)) :
    IsClosed (Set.range (Units.map f)) := by
  have h : Set.range (Units.map f) = (Units.val ⁻¹' Set.range f) ∩
      (fun u : Nˣ ↦ (u⁻¹ : Nˣ).val) ⁻¹' Set.range f := by
    ext u
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨⟨a.val, rfl⟩, ⟨a.inv, rfl⟩⟩
    · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
      have hab : a * b = 1 := hf (by rw [map_mul, ha, hb, map_one]; exact u.val_inv)
      have hba : b * a = 1 := hf (by rw [map_mul, hb, ha, map_one]; exact u.inv_val)
      exact ⟨⟨a, b, hab, hba⟩, Units.ext ha⟩
  rw [h]
  exact (hc.preimage Units.continuous_val).inter (hc.preimage Units.continuous_coe_inv)

variable (F : Type*) [Field F] [NumberField F]

private abbrev Place := HeightOneSpectrum (𝓞 F)

variable (S : Finset (Place F))

private def projectS : sIdeleBlock F S →* (SAdeles F S)ˣ :=
  (MonoidHom.fst _ _).comp (sBlockUnitProduct F S).toMonoidHom

private theorem project_sectionS (a : (SAdeles F S)ˣ) :
    projectS F S (sLocalEmbed F S a) = a := by
  change (sBlockUnitProduct F S ((sBlockUnitProduct F S).symm (a, 1))).1 = a
  rw [ContinuousMulEquiv.apply_symm_apply]

private theorem block_factor (a : sIdeleBlock F S) :
    a = sLocalEmbed F S (projectS F S a) * sTailEmbed F S (sBlockUnitProduct F S a).2 := by
  change a = (sBlockUnitProduct F S).symm ((sBlockUnitProduct F S a).1, 1) *
    (sBlockUnitProduct F S).symm (1, (sBlockUnitProduct F S a).2)
  rw [← map_mul]
  simp

private theorem project_tailS (b : (SIntegralTail F S)ˣ) :
    projectS F S (sTailEmbed F S b) = 1 := by
  change (sBlockUnitProduct F S ((sBlockUnitProduct F S).symm (1, b))).1 = 1
  rw [ContinuousMulEquiv.apply_symm_apply]

def sUnitImage : Subgroup (SAdeles F S)ˣ :=
  ((projectS F S).comp (sPrincipal F S)).range

/-- The S-local group of the manuscript discards the integral tail. -/
abbrev SIdeleQuotient := (SAdeles F S)ˣ ⧸ sUnitImage F S

private def forgetTail : SIdeleClass F S →* SIdeleQuotient F S :=
  QuotientGroup.map _ _ (projectS F S) (by
    rintro x ⟨u, rfl⟩
    exact ⟨u, rfl⟩)

private theorem forgetTail_continuous : Continuous (forgetTail F S) :=
  QuotientGroup.isOpenQuotientMap_mk.continuous_comp_iff.mp
    (QuotientGroup.continuous_mk.comp
      (continuous_fst.comp (sBlockUnitProduct F S).continuous))

private theorem forgetTail_surjective : Surjective (forgetTail F S) := by
  intro x
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
  refine ⟨QuotientGroup.mk (sLocalEmbed F S a), ?_⟩
  change QuotientGroup.mk (projectS F S (sLocalEmbed F S a)) = QuotientGroup.mk a
  rw [project_sectionS]


private theorem forgetTail_isOpenQuotientMap : IsOpenQuotientMap (forgetTail F S) := by
  refine ⟨forgetTail_surjective F S, forgetTail_continuous F S, ?_⟩
  apply IsOpenMap.of_comp QuotientGroup.continuous_mk QuotientGroup.mk_surjective
  exact QuotientGroup.isOpenQuotientMap_mk.isOpenMap.comp
    (isOpenMap_fst.comp (sBlockUnitProduct F S).toHomeomorph.isOpenMap)

/-- The quotient from the open block of global idele classes to S-local classes. -/
def sIdeleClassToLocal : SIdeleClass F S →* SIdeleQuotient F S := forgetTail F S

@[simp] theorem sIdeleClassToLocal_mk (a : sIdeleBlock F S) :
    sIdeleClassToLocal F S (QuotientGroup.mk a) =
      QuotientGroup.mk (sBlockUnitProduct F S a).1 := rfl

theorem sIdeleClassToLocal_isOpenQuotientMap :
    IsOpenQuotientMap (sIdeleClassToLocal F S) :=
  forgetTail_isOpenQuotientMap F S

theorem sUnitImage_closed : IsClosed (sUnitImage F S : Set (SAdeles F S)ˣ) := by
  let d := (sAdelesDiagonal F S).comp (sIntegerRing F S).subtype
  change IsClosed (Set.range (Units.map d.toMonoidHom))
  exact isClosed_range_unitsMap _ ((sAdelesDiagonal_injective F S).comp Subtype.val_injective)
    (principalSAdeles_closed F S)

private def sNormOnRepresentatives : (SAdeles F S)ˣ →* ℝ≥0ˣ :=
  (globalNormUnits F).comp
    ((ideleClassMap F).comp ((sIdeleBlock F S).subtype.comp (sLocalEmbed F S)))

private theorem sNormOnRepresentatives_project (a : sIdeleBlock F S) :
    sNormOnRepresentatives F S (projectS F S a) =
      globalNormUnits F (sIdeleClassInclusion F S (QuotientGroup.mk a)) := by
  apply Units.ext
  apply NNReal.eq
  change ideleClassNorm F (ideleClassMap F (sLocalEmbed F S (projectS F S a)).val) =
    ideleClassNorm F (ideleClassMap F a.val)
  rw [ideleClassNorm_mk, ideleClassNorm_mk]
  exact sBlock_norm_eq F S a

/-- The S-local norm coincides with the global norm on idele classes with integral tail. -/
def sQuotientNorm : SIdeleQuotient F S →* ℝ≥0ˣ :=
  QuotientGroup.lift _ (sNormOnRepresentatives F S) (by
    rintro x ⟨u, rfl⟩
    rw [MonoidHom.comp_apply, MonoidHom.mem_ker, sNormOnRepresentatives_project]
    have he : (QuotientGroup.mk (sPrincipal F S u) : SIdeleClass F S) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr ⟨u, rfl⟩
    rw [he, map_one, map_one])

private theorem sQuotientNorm_forgetTail (c : SIdeleClass F S) :
    sQuotientNorm F S (forgetTail F S c) = globalNormUnits F (sIdeleClassInclusion F S c) := by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective c
  exact sNormOnRepresentatives_project F S a

/-- Forgetting the integral tail preserves the idele class modulus. -/
theorem sQuotientNorm_toLocal (c : SIdeleClass F S) :
    sQuotientNorm F S (sIdeleClassToLocal F S c) =
      globalNormUnits F (sIdeleClassInclusion F S c) :=
  sQuotientNorm_forgetTail F S c

theorem sQuotientNorm_proper : IsProperMap (sQuotientNorm F S) := by
  letI := ideleClasses_hausdorff (F := F)
  have hi := sIdeleClassInclusion_openEmbedding F S
  have hclosed : IsClosed (Set.range (sIdeleClassInclusion F S)) :=
    (sIdeleClassInclusion F S).range.isClosed_of_isOpen hi.isOpen_range
  have hcomp : IsProperMap (sQuotientNorm F S ∘ forgetTail F S) := by
    rw [show sQuotientNorm F S ∘ forgetTail F S =
      globalNormUnits F ∘ sIdeleClassInclusion F S from funext (sQuotientNorm_forgetTail F S)]
    exact (globalNormUnits_proper F).comp (IsClosedEmbedding.isProperMap ⟨hi.isEmbedding, hclosed⟩)
  exact isProperMap_of_comp_of_surj (forgetTail_continuous F S)
    ((forgetTail_isOpenQuotientMap F S).continuous_comp_iff.mp hcomp.continuous)
    hcomp (forgetTail_surjective F S)

theorem sQuotient_hasNormTwistCharts : HasNormTwistCharts (G := SIdeleQuotient F S) (sQuotientNorm F S) := by
  letI := ideleClasses_locallyCompact (F := F)
  letI : LocallyCompactSpace (SIdeleClass F S) :=
    (sIdeleClassInclusion_openEmbedding F S).locallyCompactSpace
  letI := (forgetTail_isOpenQuotientMap F S).locallyCompactSpace
  letI := sUnitImage_closed F S
  apply hasNormTwistCharts_of_proper _ (sQuotientNorm_proper F S)
  let a := ideleExpSection F (Multiplicative.ofAdd 1)
  have ha : a ∈ sIdeleBlock F S := by
    apply (sIdeleBlock_mem_iff F S a).mpr
    intro v _
    apply (ideleOrder_eq_zero_iff F a v).mpr
    rw [(ideleExpSection_components F _).2]
    change Valued.v (1 : v.adicCompletion F) = 1
    exact map_one _
  refine ⟨forgetTail F S (QuotientGroup.mk (⟨a, ha⟩ : sIdeleBlock F S)), ?_⟩
  rw [sQuotientNorm_forgetTail]
  intro h
  have he := congrArg (fun u : ℝ≥0ˣ => ((u : ℝ≥0) : ℝ)) h
  change ideleClassNorm F (ideleClassMap F a) = 1 at he
  rw [ideleClassNorm_mk, ideleNorm_expSection] at he
  exact (Real.one_lt_exp_iff.mpr zero_lt_one).ne' he


def classOfTail : (SIntegralTail F S)ˣ →ₜ* IdeleClass F :=
  ⟨(ideleClassMap F).comp ((sIdeleBlock F S).subtype.comp (sTailEmbed F S)),
    (ideleClassMap_continuous F).comp (continuous_subtype_val.comp
      ((sBlockUnitProduct F S).symm.continuous.comp (continuous_const.prodMk continuous_id)))⟩

theorem tailUnits_compact : CompactSpace (SIntegralTail F S)ˣ := by
  letI (v : {v : Place F // v ∉ S}) : CompactSpace (v.val.adicCompletionIntegers F) :=
    compactSpace_adicIntegers v.val
  exact compactSpace_units_of_compactSpace _

/-- A character unramified outside S is trivial on the product of the integral units off S. -/
def sUnramified : TopologicalSpace.Opens (QuasiCharacter (IdeleClass F)) := by
  letI := tailUnits_compact F S
  exact ⟨(fun c => c.comp (classOfTail F S)) ⁻¹' {1},
    isOpen_singleton_one_complex.preimage (classOfTail F S).continuous_comp_left⟩

private def classOfSection : (SAdeles F S)ˣ →ₜ* IdeleClass F :=
  ⟨(ideleClassMap F).comp ((sIdeleBlock F S).subtype.comp (sLocalEmbed F S)),
    (ideleClassMap_continuous F).comp (continuous_subtype_val.comp
      ((sBlockUnitProduct F S).symm.continuous.comp (continuous_id.prodMk continuous_const)))⟩

private theorem sUnramified_tail_value (c : sUnramified F S) (b : (SIntegralTail F S)ˣ) :
    c.val (classOfTail F S b) = 1 :=
  DFunLike.congr_fun (Set.mem_singleton_iff.mp c.property) b

theorem classOfTail_mulSingle (v : {v : Place F // v ∉ S})
    (u : (v.val.adicCompletionIntegers F)ˣ) :
    classOfTail F S (ContinuousMulEquiv.piUnits.symm (Pi.mulSingle v u)) =
      ideleClassMap F (singleFiniteIdele F v.val
        (Units.map (v.val.adicCompletionIntegers F).subtype.toMonoidHom u)) := by
  classical
  let b : (SIntegralTail F S)ˣ := ContinuousMulEquiv.piUnits.symm (Pi.mulSingle v u)
  have he := (sBlockUnitProduct F S).apply_symm_apply ((1 : (SAdeles F S)ˣ), b)
  apply congrArg (ideleClassMap F)
  apply Units.ext
  apply Prod.ext
  · exact congrArg (fun p : (SAdeles F S)ˣ × (SIntegralTail F S)ˣ => p.1.val.1) he
  · apply DFunLike.ext
    intro w
    change (sTailEmbed F S b).val.val.2 w =
      Function.update (fun j : Place F => (1 : j.adicCompletion F)) v.val
        (u.val : v.val.adicCompletion F) w
    by_cases hw : w ∈ S
    · have h := congrArg (fun p : (SAdeles F S)ˣ × (SIntegralTail F S)ˣ => p.1.val.2 ⟨w, hw⟩) he
      have hne : w ≠ v.val := fun e => v.property (e ▸ hw)
      rw [Function.update_of_ne hne]
      exact h
    · have h := congrArg (fun p : (SAdeles F S)ˣ × (SIntegralTail F S)ˣ =>
          ((p.2.val ⟨w, hw⟩).val : w.adicCompletion F)) he
      change (sTailEmbed F S b).val.val.2 w = ((Pi.mulSingle (M := fun j : {v : Place F // v ∉ S} =>
        (j.val.adicCompletionIntegers F)ˣ) v u ⟨w, hw⟩).val : w.adicCompletion F) at h
      rw [h]
      by_cases hwv : w = v.val
      · subst w
        rw [Function.update_self]
        change (((Pi.mulSingle (M := fun j : {v : Place F // v ∉ S} =>
          (j.val.adicCompletionIntegers F)ˣ) v u v).val).val : v.val.adicCompletion F) = _
        rw [Pi.mulSingle_eq_same]
      · rw [Function.update_of_ne hwv,
          Pi.mulSingle_eq_of_ne (fun e => hwv (congrArg Subtype.val e))]; rfl

/-- Triviality on the integral tail is exactly unramifiedness at each place off S. -/
theorem mem_sUnramified_iff (c : QuasiCharacter (IdeleClass F)) :
    c ∈ (sUnramified F S : Set (QuasiCharacter (IdeleClass F))) ↔
      ∀ v : Place F, v ∉ S → ∀ u : (v.adicCompletionIntegers F)ˣ,
        c (ideleClassMap F (singleFiniteIdele F v
          (Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom u))) = 1 := by
  classical
  constructor
  · intro hc v hv u
    rw [← classOfTail_mulSingle F S ⟨v, hv⟩ u]
    exact sUnramified_tail_value F S ⟨c, hc⟩ _
  · intro hc
    change c.comp (classOfTail F S) = 1
    ext1 b
    let e : (∀ v : {v : Place F // v ∉ S}, (v.val.adicCompletionIntegers F)ˣ) ≃ₜ*
        (SIntegralTail F S)ˣ := ContinuousMulEquiv.piUnits.symm
    let a := e.symm b
    have hp : HasProd (fun v => Pi.mulSingle v (a v)) a := by
      refine Pi.hasProd.mpr fun w => ?_
      convert hasProd_ite_eq w (a w) using 1
      funext v
      rcases eq_or_ne v w with rfl | hv
      · simp
      · simp [hv, Ne.symm hv]
    let d := (c.comp (classOfTail F S)).comp ⟨e.toMonoidHom, e.continuous⟩
    have hd (v : {v : Place F // v ∉ S}) : d (Pi.mulSingle v (a v)) = 1 := by
      change c (classOfTail F S (e (Pi.mulSingle v (a v)))) = 1
      rw [classOfTail_mulSingle]
      exact hc v.val v.property (a v)
    have hm := hp.map d d.continuous
    have hv := hm.unique (hasProd_one.congr_fun hd)
    change c (classOfTail F S (e (e.symm b))) = 1 at hv
    rwa [ContinuousMulEquiv.apply_symm_apply] at hv

/-- Every global quasi-character is unramified away from finitely many places. -/
theorem exists_sUnramified (c : QuasiCharacter (IdeleClass F)) :
    ∃ S : Finset (Place F), c ∈ (sUnramified F S : Set (QuasiCharacter (IdeleClass F))) := by
  classical
  let ι := {v : Place F // v ∉ (∅ : Finset (Place F))}
  let M (v : ι) := (v.val.adicCompletionIntegers F)ˣ
  letI (v : ι) : CompactSpace (v.val.adicCompletionIntegers F) := compactSpace_adicIntegers v.val
  letI (v : ι) : CompactSpace (M v) := compactSpace_units_of_compactSpace _
  let e : (∀ v : ι, M v) ≃ₜ* (SIntegralTail F ∅)ˣ := ContinuousMulEquiv.piUnits.symm
  let d := (c.comp (classOfTail F ∅)).comp ⟨e.toMonoidHom, e.continuous⟩
  obtain ⟨T, hT⟩ := exists_finset_complexCharacter_eq_one d
  refine ⟨T.image Subtype.val, (mem_sUnramified_iff F _ c).mpr ?_⟩
  intro v hv u
  let w : ι := ⟨v, Finset.notMem_empty _⟩
  rw [← classOfTail_mulSingle F ∅ w u]
  change d (Pi.mulSingle w u) = 1
  apply hT
  intro j hj
  have hne : j ≠ w := by
    rintro rfl
    exact hv (Finset.mem_image.mpr ⟨w, hj, rfl⟩)
  exact Pi.mulSingle_eq_of_ne hne _

private theorem sUnramified_block_value (c : sUnramified F S) (a : sIdeleBlock F S) :
    c.val (classOfSection F S (projectS F S a)) =
      c.val (ideleClassMap F a.val) := by
  conv_rhs => rw [block_factor F S a]
  rw [Subgroup.coe_mul, map_mul, map_mul]
  change _ = _ * c.val (classOfTail F S (sBlockUnitProduct F S a).2)
  rw [sUnramified_tail_value, mul_one]
  rfl

/-- Restriction of a global character unramified off S to the S-local idele quotient. -/
def sCharacterRestriction (c : sUnramified F S) : QuasiCharacter (SIdeleQuotient F S) :=
  ⟨QuotientGroup.lift _ (c.val.toMonoidHom.comp (classOfSection F S).toMonoidHom) (by
    rintro a ⟨u, rfl⟩
    change c.val (classOfSection F S (projectS F S (sPrincipal F S u))) = 1
    rw [sUnramified_block_value]
    change c.val (ideleClassMap F (principalIdele F (sUnitToField F S u))) = 1
    have he : ideleClassMap F (principalIdele F (sUnitToField F S u)) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr ⟨_, rfl⟩
    rw [he, map_one]),
   QuotientGroup.isOpenQuotientMap_mk.continuous_comp_iff.mp
     (c.val.continuous.comp (classOfSection F S).continuous)⟩

@[simp] theorem sCharacterRestriction_mk (c : sUnramified F S) (a : (SAdeles F S)ˣ) :
    sCharacterRestriction F S c (QuotientGroup.mk a) = c.val (classOfSection F S a) :=
  rfl

/-- The S-local character agrees with the original character on the open block. -/
theorem sCharacterRestriction_block (c : sUnramified F S) (b : SIdeleClass F S) :
    sCharacterRestriction F S c (sIdeleClassToLocal F S b) =
      c.val (sIdeleClassInclusion F S b) := by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective b
  exact sUnramified_block_value F S c a

theorem sCharacterRestriction_surjective : Surjective (sCharacterRestriction F S) := by
  intro c
  let π : SIdeleClass F S →ₜ* SIdeleQuotient F S := ⟨forgetTail F S, forgetTail_continuous F S⟩
  obtain ⟨χ, hχ⟩ := exists_complexCharacter_extension_of_isOpenEmbedding
    (G := SIdeleClass F S) (H := IdeleClass F)
    (sIdeleClassInclusion F S) (sIdeleClassInclusion_openEmbedding F S)
    (c.comp π)
  have hval (a : sIdeleBlock F S) :
      χ (ideleClassMap F a.val) = c (QuotientGroup.mk (projectS F S a)) :=
    hχ (QuotientGroup.mk a)
  have htail : χ ∈ (sUnramified F S : Set (QuasiCharacter (IdeleClass F))) := by
    change χ.comp (classOfTail F S) = 1
    ext1 b
    change χ (ideleClassMap F (sTailEmbed F S b).val) = 1
    rw [hval, project_tailS, QuotientGroup.mk_one, map_one]
  refine ⟨⟨χ, htail⟩, ?_⟩
  ext1 x
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
  rw [sCharacterRestriction_mk]
  change χ (ideleClassMap F (sLocalEmbed F S a).val) = c (QuotientGroup.mk a)
  rw [hval, project_sectionS]


set_option maxHeartbeats 1000000 in
/-- Lemma 3.1.2.2. Restriction is a local complex analytic isomorphism
for the open unramified locus with its inherited charts. -/
theorem sCharacterRestriction_isLocalDiffeomorph :
    letI := quasiCharacterChartedSpace _ (globalNorm_hasNormTwistCharts F)
    letI := quasiCharacterChartedSpace _ (sQuotient_hasNormTwistCharts F S)
    IsLocalDiffeomorph 𝓘(ℂ) 𝓘(ℂ) ω (sCharacterRestriction F S) := by
  let n := sQuotientNorm F S
  let m := globalNormUnits F
  let hG := globalNorm_hasNormTwistCharts F
  let hH := sQuotient_hasNormTwistCharts F S
  letI := quasiCharacterChartedSpace (G := IdeleClass F) m hG
  letI := quasiCharacterChartedSpace (G := SIdeleQuotient F S) n hH
  letI := quasiCharacter_isManifold (G := IdeleClass F) m hG
  letI := quasiCharacter_isManifold (G := SIdeleQuotient F S) n hH
  apply isLocalDiffeomorph_of_chartAt 𝓘(ℂ) ω
  · intro c
    let d := sCharacterRestriction F S c
    change (hG c.val).choose c.val ∈ (hH d).choose.target
    rw [(hG c.val).choose_spec.2.1.trans (hH d).choose_spec.2.1.symm]
    exact (hH d).choose.map_source (hH d).choose_spec.1
  · intro c y hy hz
    let d := sCharacterRestriction F S c
    let a := (hG c.val).choose
    let b := (hH d).choose
    have hy' : y.val ∈ a.source := hy.2
    change a y.val ∈ b.target at hz
    change sCharacterRestriction F S y = b.symm (a y.val)
    ext1 x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    rw [sCharacterRestriction_mk, (hH d).choose_spec.2.2 _ hz]
    change y.val (classOfSection F S g) = c.val (classOfSection F S g) *
      (((n (QuotientGroup.mk g) : ℝ≥0) : ℝ) : ℂ) ^ (a y.val)
    change y.val (classOfSection F S g) = c.val (classOfSection F S g) *
      (((m (classOfSection F S g) : ℝ≥0) : ℝ) : ℂ) ^ (a y.val)
    exact (congrArg (fun q : QuasiCharacter (IdeleClass F) => q (classOfSection F S g))
      (a.left_inv hy')).symm.trans
      ((hG c.val).choose_spec.2.2 _ (a.map_source hy') (classOfSection F S g))

end
end Masullo
