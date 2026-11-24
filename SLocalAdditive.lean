import AdelicHaarScaling
import SLocalObstruction

open Filter Function IsDedekindDomain NumberField Set Topology
open scoped Classical NumberField RestrictedProduct

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

private abbrev Place := HeightOneSpectrum (𝓞 F)
private abbrev FinAdeles := FiniteAdeleRing (𝓞 F) F

/-- The number field elements integral outside the selected finite places. -/
def sIntegerRing (S : Finset (Place F)) : Subring F where
  carrier := {a | ∀ v ∉ S, algebraMap F (v.adicCompletion F) a ∈ v.adicCompletionIntegers F}
  zero_mem' := fun v _ => by rw [map_zero]; exact zero_mem _
  one_mem' := fun v _ => by rw [map_one]; exact one_mem _
  add_mem' ha hb v hv := by rw [map_add]; exact add_mem (ha v hv) (hb v hv)
  mul_mem' ha hb v hv := by rw [map_mul]; exact mul_mem (ha v hv) (hb v hv)
  neg_mem' ha v hv := by rw [map_neg]; exact neg_mem (ha v hv)

/-- S-adeles, with all Archimedean places and the finite places in S. -/
abbrev SAdeles (S : Finset (Place F)) := InfiniteAdeleRing F × ((v : S) → v.val.adicCompletion F)

/-- Project the full adeles to the finite list of selected places. -/
def sAdelesProjection (S : Finset (Place F)) : Adeles F →+* SAdeles F S where
  toFun a := (a.1, fun v => a.2 v.val)
  map_one' := rfl
  map_zero' := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

theorem sAdelesProjection_continuous (S : Finset (Place F)) :
    Continuous (sAdelesProjection F S) := by
  apply Continuous.prodMk continuous_fst
  exact continuous_pi fun v => (RestrictedProduct.continuous_eval v.val).comp continuous_snd

/-- The diagonal field map and its restriction to the S-integers. -/
def sAdelesDiagonal (S : Finset (Place F)) : F →+* SAdeles F S :=
  (sAdelesProjection F S).comp (algebraMap F (Adeles F))

theorem sAdelesDiagonal_injective (S : Finset (Place F)) :
    Injective (sAdelesDiagonal F S) :=
  (sAdelesDiagonal F S).injective

def sIntegerDiagonal (S : Finset (Place F)) : sIntegerRing F S →+ SAdeles F S :=
  (sAdelesDiagonal F S).toAddMonoidHom.comp (sIntegerRing F S).subtype.toAddMonoidHom

def principalSAdeles (S : Finset (Place F)) : AddSubgroup (SAdeles F S) :=
  (sIntegerDiagonal F S).range

/-- The S-adelic fundamental domain, with the same signed compact
lattice cube as the corrected global domain. -/
def signedSAdelicDomain (S : Finset (Place F)) : Set (SAdeles F S) :=
  {a | infiniteAdeleMixedHomeomorph F a.1 ∈ signedMixedDomain F ∧
    ∀ v : S, a.2 v ∈ v.val.adicCompletionIntegers F}

theorem signedSAdelicDomain_compactClosure (S : Finset (Place F)) :
    IsCompact (closure (signedSAdelicDomain F S)) := by
  letI : T2Space (InfiniteAdeleRing F) :=
    inferInstanceAs (T2Space ((v : InfinitePlace F) → v.Completion))
  let I : Set (SAdeles F S) :=
    ((infiniteAdeleMixedHomeomorph F).symm '' closure (signedMixedDomain F)) ×ˢ
      Set.pi univ (fun v : S => (v.val.adicCompletionIntegers F : Set (v.val.adicCompletion F)))
  have hArch : IsCompact (closure (signedMixedDomain F)) :=
    (ZSpan.fundamentalDomain_isBounded (mixedEmbedding.latticeBasis F)).isCompact_closure
  have hI : IsCompact I :=
    hArch.image (infiniteAdeleMixedHomeomorph F).symm.continuous
      |>.prod (isCompact_univ_pi (fun v => finitePlaceIntegral_compact F v.val))
  apply hI.closure_of_subset
  intro a ha
  refine ⟨⟨infiniteAdeleMixedHomeomorph F a.1, subset_closure ha.1, Homeomorph.symm_apply_apply _ _⟩, ?_⟩
  exact Set.mem_univ_pi.mpr ha.2

private theorem finiteCoordinateSplit_pad_apply (S : Finset (Place F))
    (x : (v : S) → v.val.adicCompletion F) (v : Place F) :
    (finiteCoordinateSplit F S (x, 0)) v =
      if h : v ∈ S then x ⟨v, h⟩ else 0 := by
  rw [finiteCoordinateSplit_apply]
  by_cases h : v ∈ S
  · rw [dite_eq_left h, dite_eq_left h]
  · rw [dite_eq_right h, dite_eq_right h]
    rfl

/-- The padded adele reduces to the signed domain by an S-integer. -/
theorem signedSAdelicDomain_covers (S : Finset (Place F)) (a : SAdeles F S) :
    ∃ q : sIntegerRing F S, a - sIntegerDiagonal F S q ∈ signedSAdelicDomain F S := by
  let b : Adeles F := (a.1, finiteCoordinateSplit F S (a.2, 0))
  obtain ⟨q, hq, _⟩ := signedAdelicDomain_existsUnique b
  have hqS : q ∈ sIntegerRing F S := by
    intro v hv
    have h := hq.2 v
    change (finiteCoordinateSplit F S (a.2, 0)) v -
      algebraMap F (v.adicCompletion F) q ∈ v.adicCompletionIntegers F at h
    rw [finiteCoordinateSplit_pad_apply F S, dite_eq_right hv, zero_sub] at h
    exact neg_mem_iff.mp h
  refine ⟨⟨q, hqS⟩, hq.1, ?_⟩
  intro v
  have h := hq.2 v.val
  change (finiteCoordinateSplit F S (a.2, 0)) v.val -
    algebraMap F (v.val.adicCompletion F) q ∈ v.val.adicCompletionIntegers F at h
  rwa [finiteCoordinateSplit_pad_apply F S, dite_eq_left v.property] at h

theorem signedSAdelicDomain_existsUnique (S : Finset (Place F)) (a : SAdeles F S) :
    ∃! q : sIntegerRing F S, a - sIntegerDiagonal F S q ∈ signedSAdelicDomain F S := by
  let b : Adeles F := (a.1, finiteCoordinateSplit F S (a.2, 0))
  have lifts (q : sIntegerRing F S) (hq : a - sIntegerDiagonal F S q ∈ signedSAdelicDomain F S) :
      b - algebraMap F (Adeles F) q.val ∈ signedAdelicDomain := by
    refine ⟨hq.1, fun v => ?_⟩
    change (finiteCoordinateSplit F S (a.2, 0)) v -
      algebraMap F (v.adicCompletion F) q.val ∈ v.adicCompletionIntegers F
    rw [finiteCoordinateSplit_pad_apply]
    by_cases hv : v ∈ S
    · rw [dite_eq_left hv]
      exact hq.2 ⟨v, hv⟩
    · rw [dite_eq_right hv, zero_sub]
      exact neg_mem (q.property v hv)
  obtain ⟨p, hp, hu⟩ := signedAdelicDomain_existsUnique b
  obtain ⟨q, hq⟩ := signedSAdelicDomain_covers F S a
  exact ⟨q, hq, fun r hr => Subtype.ext ((hu r.val (lifts r hr)).trans
    (hu q.val (lifts q hq)).symm)⟩

def globalIntegralBlock (S : Finset (Place F)) : AddSubgroup (Adeles F) where
  carrier := {a | ∀ v ∉ S, a.2 v ∈ v.adicCompletionIntegers F}
  zero_mem' := fun _ _ => zero_mem _
  add_mem' ha hb v hv := add_mem (ha v hv) (hb v hv)
  neg_mem' ha v hv := neg_mem (ha v hv)

theorem principalSAdeles_discrete (S : Finset (Place F)) :
    DiscreteTopology (principalSAdeles F S) := by
  let I := NumberField.mixedEmbedding.integerLattice F
  obtain ⟨V, hV, hI⟩ := isOpen_induced_iff.mp (isOpen_discrete ({0} : Set I))
  have hV₀ : (0 : NumberField.mixedEmbedding.mixedSpace F) ∈ V := by
    have h : (0 : I) ∈ ({0} : Set I) := mem_singleton _
    rwa [← hI] at h
  let U : Set (SAdeles F S) :=
    {a | infiniteAdeleMixedHomeomorph F a.1 ∈ V ∧ ∀ v : S, a.2 v ∈ v.val.adicCompletionIntegers F}
  have hU₂ : IsOpen {a : SAdeles F S | ∀ v : S, a.2 v ∈ v.val.adicCompletionIntegers F} := by
    have h := (isOpen_set_pi (finite_univ (α := S))
      (fun (v : S) _ => Valued.isOpen_valuationSubring (v.val.adicCompletion F))).preimage
        (continuous_snd : Continuous (Prod.snd : SAdeles F S → _))
    convert h using 1
    ext a
    exact Set.mem_univ_pi.symm
  have hU : IsOpen U := (hV.preimage ((infiniteAdeleMixedHomeomorph F).continuous.comp continuous_fst)).inter hU₂
  have he : (Subtype.val : principalSAdeles F S → SAdeles F S) ⁻¹' U = {0} := by
    ext a
    constructor
    · intro ha
      obtain ⟨q, hq⟩ := a.property
      have hqS : ∀ v : Place F, algebraMap F (v.adicCompletion F) q.val ∈ v.adicCompletionIntegers F := by
        intro v
        by_cases hv : v ∈ S
        · have h := (congrArg (fun x : SAdeles F S => x.2 ⟨v, hv⟩) hq)
          change algebraMap F (v.adicCompletion F) q.val = a.val.2 ⟨v, hv⟩ at h
          rw [h]
          exact ha.2 ⟨v, hv⟩
        · exact q.property v hv
      obtain ⟨r, hr⟩ := (diagonal_finiteAdeles_integral_iff q.val).mp hqS
      let y : I := ⟨NumberField.mixedEmbedding F q.val, ⟨r, congrArg (NumberField.mixedEmbedding F) hr⟩⟩
      have hy : y.val ∈ V := by
        have h := congrArg (fun a : SAdeles F S => infiniteAdeleMixedHomeomorph F a.1) hq
        change (InfiniteAdeleRing.ringEquiv_mixedSpace F)
          (algebraMap F (InfiniteAdeleRing F) q.val) = infiniteAdeleMixedHomeomorph F a.val.1 at h
        have h' : mixedEmbedding F q.val = infiniteAdeleMixedHomeomorph F a.val.1 :=
          (InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp (x := q.val)).trans h
        change mixedEmbedding F q.val ∈ V
        rw [h']
        exact ha.1
      have hz : y = 0 := mem_singleton_iff.mp (hI ▸ hy)
      have hq₀ : q.val = 0 := (mixedEmbedding_injective F)
        ((congrArg Subtype.val hz).trans (map_zero (NumberField.mixedEmbedding F)).symm)
      apply mem_singleton_iff.mpr
      apply Subtype.ext
      change a.val = 0
      rw [← hq, show q = 0 from Subtype.ext hq₀, map_zero]
    · rintro rfl
      have ha : infiniteAdeleMixedHomeomorph F (0 : InfiniteAdeleRing F) = 0 :=
        (InfiniteAdeleRing.ringEquiv_mixedSpace F).map_zero
      exact ⟨ha.symm ▸ hV₀, fun v => zero_mem _⟩
  apply discreteTopology_of_isOpen_singleton_zero
  rw [← he]
  exact hU.preimage continuous_subtype_val


theorem principalSAdeles_closed (S : Finset (Place F)) :
    IsClosed (principalSAdeles F S : Set (SAdeles F S)) := by
  letI : T2Space (InfiniteAdeleRing F) :=
    inferInstanceAs (T2Space ((v : InfinitePlace F) → v.Completion))
  letI : DiscreteTopology (principalSAdeles F S) := principalSAdeles_discrete F S
  exact AddSubgroup.isClosed_of_discrete

/-- Lemma A.2.4.2 with the signed domain. Only finitely many
S-integer translates of its closure meet a compact subset. -/
theorem signedSAdelicDomain_finite_translates (S : Finset (Place F))
    {K : Set (SAdeles F S)} (hK : IsCompact K) :
    {q : sIntegerRing F S | ∃ a ∈ K, a - sIntegerDiagonal F S q ∈
      closure (signedSAdelicDomain F S)}.Finite := by
  let P := principalSAdeles F S
  let D := closure (signedSAdelicDomain F S)
  let C := (fun p : SAdeles F S × SAdeles F S => p.1 - p.2) '' (K ×ˢ D)
  have hC : IsCompact C := (hK.prod (signedSAdelicDomain_compactClosure F S)).image
    (continuous_fst.sub continuous_snd)
  letI : DiscreteTopology P := principalSAdeles_discrete F S
  have hfinite : ((↑) ⁻¹' C : Set P).Finite :=
    ((principalSAdeles_closed F S).isClosedEmbedding_subtypeVal.isCompact_preimage hC).finite_of_discrete
  let j (q : sIntegerRing F S) : P := ⟨sIntegerDiagonal F S q, ⟨q, rfl⟩⟩
  have hj : Injective j := fun x y h => Subtype.ext
    (sAdelesDiagonal_injective F S (congrArg Subtype.val h))
  refine (hfinite.preimage hj.injOn).subset ?_
  rintro q ⟨x, hx, hq⟩
  exact ⟨(x, x - sIntegerDiagonal F S q), ⟨hx, hq⟩, sub_sub_cancel _ _⟩

abbrev SAdelicClass (S : Finset (Place F)) := SAdeles F S ⧸ principalSAdeles F S

theorem sAdelicClass_compact (S : Finset (Place F)) : CompactSpace (SAdelicClass F S) := by
  let π := QuotientAddGroup.mk' (principalSAdeles F S)
  have h : π '' closure (signedSAdelicDomain F S) = univ := by
    apply eq_univ_of_forall
    intro y
    obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective y
    obtain ⟨q, hq⟩ := signedSAdelicDomain_covers F S a
    have hz : π (sIntegerDiagonal F S q) = 0 :=
      (QuotientAddGroup.eq_zero_iff (sIntegerDiagonal F S q)).mpr ⟨q, rfl⟩
    refine ⟨a - sIntegerDiagonal F S q, subset_closure hq, ?_⟩
    rw [map_sub, hz, sub_zero]
    rfl
  exact ⟨h ▸ (signedSAdelicDomain_compactClosure F S).image QuotientAddGroup.continuous_mk⟩

theorem sAdelicClass_hausdorff (S : Finset (Place F)) : T2Space (SAdelicClass F S) := by
  letI : T2Space (InfiniteAdeleRing F) := inferInstanceAs (T2Space ((v : InfinitePlace F) → v.Completion))
  letI := principalSAdeles_closed F S
  infer_instance

theorem sAdelicClass_divisible (S : Finset (Place F)) (n : ℕ) (hn : n ≠ 0) :
    Surjective (fun x : SAdelicClass F S => n • x) := by
  letI : Algebra ℚ (InfiniteAdeleRing F) :=
    (algebraMap F (InfiniteAdeleRing F)).comp (algebraMap ℚ F) |>.toAlgebra
  letI (v : S) : Algebra ℚ (v.val.adicCompletion F) :=
    (algebraMap F (v.val.adicCompletion F)).comp (algebraMap ℚ F) |>.toAlgebra
  exact quotient_rationalVectorSpace_divisible _ n hn


theorem principalSAdeles_strict_exact (S : Finset (Place F))
    [TopologicalSpace (sIntegerRing F S)] [DiscreteTopology (sIntegerRing F S)] :
    IsClosedEmbedding (sIntegerDiagonal F S) ∧
      IsOpenQuotientMap (QuotientAddGroup.mk' (principalSAdeles F S)) ∧
      (QuotientAddGroup.mk' (principalSAdeles F S)).ker = (sIntegerDiagonal F S).range := by
  let P := principalSAdeles F S
  letI : DiscreteTopology P := principalSAdeles_discrete F S
  let j (q : sIntegerRing F S) : P := ⟨sIntegerDiagonal F S q, ⟨q, rfl⟩⟩
  have hj : Injective j := fun _ _ h => Subtype.ext
    (sAdelesDiagonal_injective F S (congrArg Subtype.val h))
  have hje : IsEmbedding j :=
    (IsOpenEmbedding.of_continuous_injective_isOpenMap continuous_of_discreteTopology hj
      (fun _ _ => isOpen_discrete _)).isEmbedding
  refine ⟨⟨IsEmbedding.subtypeVal.comp hje, principalSAdeles_closed F S⟩,
    QuotientAddGroup.isOpenQuotientMap_mk, ?_⟩
  ext a
  exact QuotientAddGroup.eq_zero_iff a

theorem globalIntegralBlock_open (S : Finset (Place F)) :
    IsOpen (globalIntegralBlock F S : Set (Adeles F)) := by
  have h : IsOpen {x : FinAdeles F | ∀ v, v ∉ S → x v ∈ v.adicCompletionIntegers F} :=
    RestrictedProduct.isOpen_forall_imp_mem
      (fun v : Place F => Valued.isOpen_valuationSubring (v.adicCompletion F))
  exact h.preimage (continuous_snd : Continuous (Prod.snd : Adeles F → FinAdeles F))

def sIntegersGlobal (S : Finset (Place F)) : sIntegerRing F S →+ globalIntegralBlock F S :=
  ((algebraMap F (Adeles F)).toAddMonoidHom.comp (sIntegerRing F S).subtype.toAddMonoidHom).codRestrict _
    (fun u => u.property)

abbrev SBlockClass (S : Finset (Place F)) :=
  (globalIntegralBlock F S) ⧸ (sIntegersGlobal F S).range

abbrev GlobalAddClass :=
  Adeles F ⧸ NumberField.AdeleRing.principalSubgroup (𝓞 F) F

private def sBlockToGlobal (S : Finset (Place F)) : globalIntegralBlock F S →+ GlobalAddClass F :=
  (QuotientAddGroup.mk' _).comp (globalIntegralBlock F S).subtype

private theorem sBlockToGlobal_open (S : Finset (Place F)) : IsOpenMap (sBlockToGlobal F S) :=
  QuotientAddGroup.isOpenQuotientMap_mk.isOpenMap.comp
    (globalIntegralBlock_open F S).isOpenEmbedding_subtypeVal.isOpenMap

private theorem sBlockToGlobal_continuous (S : Finset (Place F)) : Continuous (sBlockToGlobal F S) :=
  QuotientAddGroup.continuous_mk.comp continuous_subtype_val

private theorem sBlockToGlobal_surjective (S : Finset (Place F)) : Surjective (sBlockToGlobal F S) := by
  intro y
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective y
  obtain ⟨q, hq, _⟩ := signedAdelicDomain_existsUnique a
  let π := QuotientAddGroup.mk' (NumberField.AdeleRing.principalSubgroup (𝓞 F) F)
  have hp : π (algebraMap F (Adeles F) q) = 0 :=
    (QuotientAddGroup.eq_zero_iff _).mpr ⟨q, rfl⟩
  refine ⟨⟨a - algebraMap F (Adeles F) q, fun v _ => hq.2 v⟩, ?_⟩
  change π (a - algebraMap F (Adeles F) q) = π a
  rw [map_sub, hp, sub_zero]

private theorem sBlockToGlobal_ker (S : Finset (Place F)) :
    (sBlockToGlobal F S).ker = (sIntegersGlobal F S).range := by
  ext a
  change QuotientAddGroup.mk a.val = (0 : GlobalAddClass F) ↔ _
  rw [QuotientAddGroup.eq_zero_iff]
  constructor
  · rintro ⟨q, hq⟩
    have h : q ∈ sIntegerRing F S := by
      have hI : a.val ∈ globalIntegralBlock F S := a.property
      rwa [← hq] at hI
    exact ⟨⟨q, h⟩, Subtype.ext hq⟩
  · rintro ⟨q, hq⟩
    exact ⟨q.val, congrArg Subtype.val hq⟩

/-- The S-local block with the integral tail gives the same adelic
classes as the full adelic ring. -/
def sBlockClass_homeomorph (S : Finset (Place F)) : SBlockClass F S ≃ₜ+ GlobalAddClass F := by
  let p := sBlockToGlobal F S
  let f : SBlockClass F S →+ GlobalAddClass F := QuotientAddGroup.lift _ p
    (sBlockToGlobal_ker F S).ge
  have hf₀ : f ∘ (QuotientAddGroup.mk' (sIntegersGlobal F S).range) = p := rfl
  have hf₁ : Continuous f := QuotientAddGroup.isOpenQuotientMap_mk.continuous_comp_iff.mp
    (hf₀.symm ▸ sBlockToGlobal_continuous F S)
  have hf₂ : IsOpenMap f := IsOpenMap.of_comp QuotientAddGroup.continuous_mk
    QuotientAddGroup.mk_surjective (hf₀.symm ▸ sBlockToGlobal_open F S)
  have hfinj : Injective f := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective x
    apply (QuotientAddGroup.eq_zero_iff a).mpr
    rw [← sBlockToGlobal_ker F S]
    exact hx
  have hfs : Surjective f := by
    intro y
    obtain ⟨a, ha⟩ := sBlockToGlobal_surjective F S y
    exact ⟨QuotientAddGroup.mk a, ha⟩
  let e := AddEquiv.ofBijective f ⟨hfinj, hfs⟩
  exact { toAddEquiv := e
          continuous_toFun := hf₁
          continuous_invFun := (e.toEquiv.continuous_symm_iff).mpr hf₂ }

private theorem sAdelesProjection_open (S : Finset (Place F)) :
    IsOpenMap (sAdelesProjection F S) := by
  let e := (Homeomorph.refl (InfiniteAdeleRing F)).prodCongr (finiteCoordinateSplit F S).toHomeomorph
  have h : (sAdelesProjection F S) ∘ e =
      Prod.map id Prod.fst := by
    funext a
    apply Prod.ext
    · rfl
    · funext v
      change finiteCoordinateSplit F S a.2 v.val = a.2.1 v
      rw [finiteCoordinateSplit_apply, dite_eq_left v.property]
  exact IsOpenMap.of_comp (f := e) e.continuous e.surjective
    (h.symm ▸ IsOpenMap.id.prodMap isOpenMap_fst)

private def sBlockProject (S : Finset (Place F)) : globalIntegralBlock F S →+ SAdeles F S :=
  (sAdelesProjection F S).toAddMonoidHom.comp (globalIntegralBlock F S).subtype

private theorem sBlockProject_surjective (S : Finset (Place F)) :
    Surjective (sBlockProject F S) := by
  intro a
  let b : Adeles F := (a.1, finiteCoordinateSplit F S (a.2, 0))
  have hb : b ∈ globalIntegralBlock F S := by
    intro v hv
    change (finiteCoordinateSplit F S (a.2, 0)) v ∈ v.adicCompletionIntegers F
    rw [finiteCoordinateSplit_pad_apply, dite_eq_right hv]
    exact zero_mem _
  refine ⟨⟨b, hb⟩, Prod.ext rfl ?_⟩
  funext v
  change (finiteCoordinateSplit F S (a.2, 0)) v.val = a.2 v
  rw [finiteCoordinateSplit_pad_apply, dite_eq_left v.property]

/-- Projection from the adelic block modulo S-integers to the
S-local additive class group. -/
def sBlockClass_projection (S : Finset (Place F)) : SBlockClass F S →+ SAdelicClass F S :=
  QuotientAddGroup.lift _
    ((QuotientAddGroup.mk' (principalSAdeles F S)).comp (sBlockProject F S)) (by
      rintro _ ⟨q, rfl⟩
      exact (QuotientAddGroup.eq_zero_iff (sIntegerDiagonal F S q)).mpr ⟨q, rfl⟩)

theorem sBlockClass_projection_properQuotient (S : Finset (Place F)) :
    IsProperMap (sBlockClass_projection F S) ∧ IsOpenQuotientMap (sBlockClass_projection F S) := by
  let p := sBlockClass_projection F S
  let q := QuotientAddGroup.mk' (sIntegersGlobal F S).range
  let t := QuotientAddGroup.mk' (principalSAdeles F S)
  have he : p ∘ q = t ∘ (sAdelesProjection F S) ∘ Subtype.val := rfl
  have hc : Continuous p := QuotientAddGroup.isOpenQuotientMap_mk.continuous_comp_iff.mp
    (he.symm ▸ (QuotientAddGroup.continuous_mk.comp
      ((sAdelesProjection_continuous F S).comp continuous_subtype_val)))
  have ho : IsOpenMap p := IsOpenMap.of_comp QuotientAddGroup.continuous_mk
    QuotientAddGroup.mk_surjective (he.symm ▸
      QuotientAddGroup.isOpenQuotientMap_mk.isOpenMap.comp ((sAdelesProjection_open F S).comp
        (globalIntegralBlock_open F S).isOpenEmbedding_subtypeVal.isOpenMap))
  have hs : Surjective p := by
    intro y
    obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective y
    obtain ⟨b, hb⟩ := sBlockProject_surjective F S a
    exact ⟨q b, congrArg t hb⟩
  letI : CompactSpace (GlobalAddClass F) := principalAdeles_quotient_compact
  letI : CompactSpace (SBlockClass F S) := (sBlockClass_homeomorph F S).toHomeomorph.symm.compactSpace
  letI : T2Space (SAdelicClass F S) := sAdelicClass_hausdorff F S
  exact ⟨hc.isProperMap, ⟨hs, hc, ho⟩⟩


/-- The integral tail is precisely the product of the local integer rings. -/
abbrev SIntegralTail (S : Finset (Place F)) :=
  (v : {v : Place F // v ∉ S}) → v.val.adicCompletionIntegers F

private def insertIntegralTail (S : Finset (Place F)) (a : SIntegralTail F S) :
    Πʳ v : {v : Place F // v ∉ S}, [v.val.adicCompletion F, (v.val.adicCompletionIntegers F).toSubring] :=
  RestrictedProduct.inclusion _ _ le_top (RestrictedProduct.homeoTop a)

private theorem insertIntegralTail_continuous (S : Finset (Place F)) :
    Continuous (insertIntegralTail F S) :=
  (RestrictedProduct.continuous_inclusion le_top).comp RestrictedProduct.homeoTop.continuous

/-- The open subgroup of adeles integral outside S is the product of
the S-adele ring and the full integral tail used in (A.1.5.4). -/
def globalIntegralBlockHomeomorph (S : Finset (Place F)) :
    globalIntegralBlock F S ≃ₜ+ SAdeles F S × SIntegralTail F S where
  toFun a := (sAdelesProjection F S a.val, fun v => ⟨a.val.2 v.val, a.property v.val v.property⟩)
  invFun p := ⟨(p.1.1, finiteCoordinateSplit F S (p.1.2, insertIntegralTail F S p.2)), by
    intro v hv
    change finiteCoordinateSplit F S (p.1.2, insertIntegralTail F S p.2) v ∈
      v.adicCompletionIntegers F
    rw [finiteCoordinateSplit_apply, dite_eq_right hv]
    exact (p.2 ⟨v, hv⟩).property⟩
  left_inv a := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply RestrictedProduct.ext
      intro v
      change finiteCoordinateSplit F S _ v = a.val.2 v
      rw [finiteCoordinateSplit_apply]
      by_cases hv : v ∈ S <;> simp only [hv, dite_true, dite_false] <;> rfl
  right_inv p := by
    apply Prod.ext
    · apply Prod.ext
      · rfl
      · funext v
        change finiteCoordinateSplit F S _ v.val = p.1.2 v
        rw [finiteCoordinateSplit_apply, dite_eq_left v.property]
    · funext v
      apply Subtype.ext
      change finiteCoordinateSplit F S _ v.val = (p.2 v).val
      rw [finiteCoordinateSplit_apply, dite_eq_right v.property]
      rfl
  map_add' a b := by
    apply Prod.ext
    · exact map_add (sAdelesProjection F S) a.val b.val
    · funext v
      apply Subtype.ext
      rfl
  continuous_toFun := by
    let val : globalIntegralBlock F S → Adeles F := Subtype.val
    have hv : Continuous val := continuous_subtype_val
    refine ((sAdelesProjection_continuous F S).comp hv).prodMk (continuous_pi fun v => ?_)
    exact ((RestrictedProduct.continuous_eval v.val).comp (continuous_snd.comp hv)).subtype_mk _
  continuous_invFun := by
    have h : Continuous (fun p : SAdeles F S × SIntegralTail F S =>
        (p.1.1, finiteCoordinateSplit F S (p.1.2, insertIntegralTail F S p.2))) :=
      (continuous_fst.comp continuous_fst).prodMk ((finiteCoordinateSplit F S).continuous.comp
        ((continuous_snd.comp continuous_fst).prodMk
          ((insertIntegralTail_continuous F S).comp continuous_snd)))
    exact h.subtype_mk _

end

end Masullo
