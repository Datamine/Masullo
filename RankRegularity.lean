import RankBoundedSpaces
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers

open Cardinal CategoryTheory CategoryTheory.Limits Function Order Set Topology
open scoped Cardinal Ordinal

namespace Masullo

universe u

section

variable {α : Ordinal.{u}} {ν : Cardinal.{u}}
variable (hα : IsSuccLimit α) (hcard : preBeth α = α.card) (hν : ℵ₀ ≤ ν) (hc : ν < α.cof)

local notation "U" => rankSpaceInclusion α

include hα hcard hν hc in
theorem rankSpace_finite_limits :
    HasFiniteLimits (RankSpace α) ∧ PreservesFiniteLimits U := by
  refine ⟨⟨?_⟩, ⟨?_⟩⟩
  · intro J _ _
    exact (rankSpace_countable_shape_closure hα hcard hν hc J).1
  · intro J _ _
    exact (rankSpace_countable_shape_closure hα hcard hν hc J).2.2.1

include hα hcard hν hc in
theorem rankSpace_finite_colimits :
    HasFiniteColimits (RankSpace α) ∧ PreservesFiniteColimits U := by
  refine ⟨⟨?_⟩, ⟨?_⟩⟩
  · intro J _ _
    exact (rankSpace_countable_shape_closure hα hcard hν hc J).2.1
  · intro J _ _
    exact (rankSpace_countable_shape_closure hα hcard hν hc J).2.2.2

private theorem collapse_carrier_card_lt (Y : RankSpace α) (S : Set Y.space.obj)
    (hS : IsClosed S) (hω : ℵ₀ < preBeth α) :
    #((CGWH.pointedCollapseObject Y.space S hS).obj : Type u) < preBeth α := by
  refine (mk_le_of_surjective (f := CGWH.pointedCollapseMap Y.space S) (fun y => Quotient.exists_rep y)).trans_lt ?_
  change #(ULift.{u} Unit ⊕ (Y.space.obj : Type u)) < preBeth α
  simp only [mk_sum, lift_id]
  exact add_lt_of_lt hω.le (mk_le_aleph0.trans_lt hω) Y.carrier_lt

private theorem eval_eq {X Y : CGWH.{u}} {f g : X ⟶ Y} (e : f = g)
    (x : X.obj) : f.hom x = g.hom x :=
  ConcreteCategory.congr_hom (congrArg InducedCategory.Hom.hom e) x

include hα hcard hν hc in
theorem rankSpace_mono_iff {X Y : RankSpace α} (f : X ⟶ Y) :
    Mono f ↔ Injective ((U).map f).hom := by
  constructor
  · intro hf x y e
    letI := hf
    have hω := (rank_cardinal_properties hα hcard hν hc).2.1
    obtain ⟨P, ⟨hp⟩⟩ := rankSpace_representative hcard CGWH.basepointObject
      (show #(ULift.{u} Unit) < preBeth α from mk_le_aleph0.trans_lt hω)
    let i := cgwhIsoOfHomeo hp
    let a : P ⟶ X := (U).preimage (i.hom ≫ CGWH.point X.space x)
    let b : P ⟶ X := (U).preimage (i.hom ≫ CGWH.point X.space y)
    have he : a ≫ f = b ≫ f := by
      apply (U).map_injective
      simp only [(U).map_comp, a, b, Functor.map_preimage]
      exact cgwhForget.map_injective (ConcreteCategory.hom_ext _ _ (fun _ => e))
    have hab : a = b := (cancel_mono f).mp he
    have hh := congrArg (U).map hab
    simp only [a, b, Functor.map_preimage] at hh
    exact eval_eq hh (hp.symm ⟨()⟩)
  · intro hf
    letI := (CGWH.mono_iff_injective ((U).map f)).mpr hf
    exact Functor.mono_of_mono_map U inferInstance

include hα hcard hν hc in
theorem rankSpace_epi_iff {X Y : RankSpace α} (f : X ⟶ Y) :
    Epi f ↔ DenseRange ((U).map f).hom := by
  constructor
  · intro hf
    letI := hf
    let S := closure (range ((U).map f).hom)
    let Q := CGWH.pointedCollapseObject Y.space S isClosed_closure
    let a := CGWH.pointedCollapseInclusionMorphism Y.space S isClosed_closure
    let b := CGWH.pointedCollapseConstantMorphism Y.space S isClosed_closure
    have hω := (rank_cardinal_properties hα hcard hν hc).2.1
    obtain ⟨P, ⟨hp⟩⟩ := rankSpace_representative hcard Q
      (collapse_carrier_card_lt Y S isClosed_closure hω)
    let i := cgwhIsoOfHomeo hp
    let a' : Y ⟶ P := (U).preimage (a ≫ i.inv)
    let b' : Y ⟶ P := (U).preimage (b ≫ i.inv)
    have hmem (y : Y.space.obj) : a.hom y = b.hom y ↔ y ∈ S :=
      Set.ext_iff.mp (CGWH.pointedCollapseInclusion_preimage Y.space S) y
    have he : f ≫ a' = f ≫ b' := by
      apply (U).map_injective
      simp only [(U).map_comp, a', b', Functor.map_preimage]
      apply cgwhForget.map_injective
      exact ConcreteCategory.hom_ext _ _ (fun x =>
        congrArg i.inv.hom ((hmem (((U).map f).hom x)).mpr (subset_closure (mem_range_self x))))
    have hab := congrArg (U).map ((cancel_epi f).mp he)
    simp only [a', b', Functor.map_preimage] at hab
    exact fun y => (hmem y).mp (eval_eq ((cancel_mono i.inv).mp hab) y)
  · intro hf
    letI := (CGWH.epi_iff_denseRange ((U).map f)).mpr hf
    exact Functor.epi_of_epi_map U inferInstance

include hα hcard hν hc in
theorem rankSpace_regularMono_iff {X Y : RankSpace α} (f : X ⟶ Y) :
    IsRegularMono f ↔ IsClosedEmbedding ((U).map f).hom := by
  letI := (rankSpace_finite_limits hα hcard hν hc).2
  constructor
  · rintro ⟨⟨h⟩⟩
    apply (CGWH.regularMono_iff_closedEmbedding ((U).map f)).mp
    refine ⟨⟨⟨_, (U).map h.left, (U).map h.right, ?_, isLimitForkMapOfIsLimit U h.w h.isLimit⟩⟩⟩
    simp only [← (U).map_comp, h.w]
  · intro hf
    let S := range ((U).map f).hom
    let Q := CGWH.pointedCollapseObject Y.space S hf.isClosed_range
    let a := CGWH.pointedCollapseInclusionMorphism Y.space S hf.isClosed_range
    let b := CGWH.pointedCollapseConstantMorphism Y.space S hf.isClosed_range
    have hω := (rank_cardinal_properties hα hcard hν hc).2.1
    obtain ⟨P, ⟨hp⟩⟩ := rankSpace_representative hcard Q
      (collapse_carrier_card_lt Y S hf.isClosed_range hω)
    let i := cgwhIsoOfHomeo hp
    let a' : Y ⟶ P := (U).preimage (a ≫ i.inv)
    let b' : Y ⟶ P := (U).preimage (b ≫ i.inv)
    obtain ⟨w, ⟨h⟩⟩ := CGWH.closedEmbedding_collapseEqualizer hf
    have wa : (U).map f ≫ a = (U).map f ≫ b := w
    have wc : f ≫ a' = f ≫ b' := by
      apply (U).map_injective
      simp only [(U).map_comp, a', b', Functor.map_preimage, ← Category.assoc, wa]
    refine ⟨⟨⟨P, a', b', wc, isLimitOfIsLimitForkMap U wc ?_⟩⟩⟩
    have ea : (U).map a' = a ≫ i.inv := Functor.map_preimage U _
    have eb : (U).map b' = b ≫ i.inv := Functor.map_preimage U _
    have mapCondition (c : Fork ((U).map a') ((U).map b')) : c.ι ≫ a = c.ι ≫ b := by
      apply (cancel_mono i.inv).mp
      rw [Category.assoc, Category.assoc, ← ea, ← eb]
      exact c.condition
    let lift (c : Fork ((U).map a') ((U).map b')) :=
      h.lift (Fork.ofι c.ι (mapCondition c))
    refine Fork.IsLimit.mk _ lift (fun c => Fork.IsLimit.lift_ι h) ?_
    intro c m hm
    exact Fork.IsLimit.hom_ext h (hm.trans (Fork.IsLimit.lift_ι (t := Fork.ofι c.ι (mapCondition c)) h).symm)

include hα hcard hν hc in
theorem rankSpace_regularEpi_iff {X Y : RankSpace α} (f : X ⟶ Y) :
    IsRegularEpi f ↔ IsQuotientMap ((U).map f).hom := by
  letI := (rankSpace_finite_colimits hα hcard hν hc).2
  letI := (rankSpace_finite_limits hα hcard hν hc).1
  letI := (rankSpace_finite_limits hα hcard hν hc).2
  constructor
  · rintro ⟨⟨h⟩⟩
    apply (CGWH.regularEpi_iff_quotient ((U).map f)).mp
    refine ⟨⟨⟨_, (U).map h.left, (U).map h.right, ?_, isColimitCoforkMapOfIsColimit U h.w h.isColimit⟩⟩⟩
    simp only [← (U).map_comp, h.w]
  · intro hf
    letI := (CGWH.effectiveEpi_iff_quotient ((U).map f)).mpr hf
    refine ⟨⟨regularEpiOfKernelPair _ (isColimitOfIsColimitCoforkMap U pullback.condition ?_)⟩⟩
    let p := (U).map_isPullback (IsPullback.of_hasPullback f f)
    exact isColimitCoforkOfEffectiveEpi _ _ p.isLimit

include hα hcard hν hc in
theorem rankSpace_regular : Regular (RankSpace α) where
  toHasFiniteLimits := (rankSpace_finite_limits hα hcard hν hc).1
  hasCoequalizer_of_isKernelPair _ := by
    letI := (rankSpace_finite_colimits hα hcard hν hc).1
    infer_instance
  regularEpiIsStableUnderBaseChange := by
    letI := (rankSpace_finite_limits hα hcard hν hc).2
    exact ⟨fun sq hg => (rankSpace_regularEpi_iff hα hcard hν hc _).mpr
      (CGWH.quotient_of_isPullback ((U).map_isPullback sq)
        ((rankSpace_regularEpi_iff hα hcard hν hc _).mp hg))⟩

include hα hcard hν hc in
theorem rankSpace_effectiveEpi_iff {X Y : RankSpace α} (f : X ⟶ Y) :
    EffectiveEpi f ↔ IsQuotientMap ((U).map f).hom := by
  letI := (rankSpace_finite_limits hα hcard hν hc).1
  constructor
  · intro h
    letI := h
    exact (rankSpace_regularEpi_iff hα hcard hν hc f).mp inferInstance
  · intro h
    letI := (rankSpace_regularEpi_iff hα hcard hν hc f).mpr h
    infer_instance

include hα hcard hν hc in
theorem rankSpace_effectiveMono_iff {X Y : RankSpace α} (f : X ⟶ Y)
    [HasPushouts (RankSpace α)] :
    Nonempty (IsLimit (Fork.ofι f (pushout.condition (f := f) (g := f)))) ↔
      IsClosedEmbedding ((U).map f).hom :=
  (CGWH.effectiveMono_iff_regularMono f).trans (rankSpace_regularMono_iff hα hcard hν hc f)

include hα hcard hν hc in
theorem rankSpace_universallyEffectiveEpi_iff {X Y : RankSpace α} (f : X ⟶ Y) :
    (EffectiveEpi f ∧
      ∀ {A B : RankSpace α} {g : A ⟶ Y} {p : B ⟶ X} {q : B ⟶ A}, IsPullback p q f g →
        EffectiveEpi q) ↔ IsQuotientMap ((U).map f).hom := by
  constructor
  · exact fun h => (rankSpace_effectiveEpi_iff hα hcard hν hc f).mp h.1
  · intro h
    letI := (rankSpace_finite_limits hα hcard hν hc).2
    refine ⟨(rankSpace_effectiveEpi_iff hα hcard hν hc f).mpr h, ?_⟩
    intro A B g p q sq
    exact (rankSpace_effectiveEpi_iff hα hcard hν hc q).mpr
      (CGWH.quotient_of_isPullback ((U).map_isPullback sq) h)

theorem rankSpace_isIso_iff {X Y : RankSpace α} (f : X ⟶ Y) :
    IsIso f ↔ IsHomeomorph ((U).map f).hom := by
  constructor
  · intro h
    letI := h
    exact (CGWH.isIso_iff_isHomeomorph _).mp inferInstance
  · intro h
    letI := (CGWH.isIso_iff_isHomeomorph _).mpr h
    exact isIso_of_reflects_iso f U

include hα hcard hν hc in
theorem rankSpace_composition {X Y Z : RankSpace α} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (Mono f → Mono g → Mono (f ≫ g)) ∧ (Epi f → Epi g → Epi (f ≫ g)) ∧
    (IsRegularMono f → IsRegularMono g → IsRegularMono (f ≫ g)) ∧
    (IsRegularEpi f → IsRegularEpi g → IsRegularEpi (f ≫ g)) := by
  simp only [rankSpace_mono_iff hα hcard hν hc, rankSpace_epi_iff hα hcard hν hc,
    rankSpace_regularMono_iff hα hcard hν hc, rankSpace_regularEpi_iff hα hcard hν hc,
    Functor.map_comp, ← CGWH.mono_iff_injective, ← CGWH.epi_iff_denseRange,
    ← CGWH.regularMono_iff_closedEmbedding, ← CGWH.regularEpi_iff_quotient]
  exact CGWH.regularity_composition _ _

include hα hcard hν hc in
theorem rankSpace_factorisation {X Y : RankSpace α} (f : X ⟶ Y) :
    ∃ (Z : RankSpace α) (e : X ⟶ Z) (m : Z ⟶ Y),
      IsRegularEpi e ∧ Mono m ∧ e ≫ m = f := by
  letI := rankSpace_regular hα hcard hν hc
  let F := Regular.strongEpiMonoFactorisation f
  exact ⟨F.I, F.e, F.m, inferInstance, inferInstance, F.fac⟩

include hα hcard hν hc in
theorem rankSpace_factorisation_baseChange {X Y Z A B : RankSpace α}
    {e : X ⟶ Z} {m : Z ⟶ Y} {g : A ⟶ Y} {p : B ⟶ X} {q : B ⟶ A}
    (he : IsRegularEpi e) (hm : Mono m) (sq : IsPullback p q (e ≫ m) g) :
    ∃ (W : RankSpace α) (e' : B ⟶ W) (m' : W ⟶ A) (r : W ⟶ Z),
      IsPullback m' r g m ∧ IsPullback e' p r e ∧
        IsRegularEpi e' ∧ Mono m' ∧ e' ≫ m' = q := by
  letI := rankSpace_regular hα hcard hν hc
  let t := IsPullback.of_hasPullback g m
  have sf := sq.flip
  let e' := t.lift q (p ≫ e) (by rw [sf.w, Category.assoc])
  have w := sf.of_right' t
  exact ⟨_, e', _, _, t, w, Regular.regularEpiIsStableUnderBaseChange.of_isPullback w.flip he,
    t.mono_fst_of_mono hm, t.lift_fst _ _ _⟩


private theorem rankSpace_product_comparison {I : Type u} {X Y : I → RankSpace α}
    [HasProduct X] [HasProduct Y] [PreservesLimit (Discrete.functor X) U]
    [PreservesLimit (Discrete.functor Y) U] (f : ∀ i, X i ⟶ Y i) :
    ∃ (ex : (U).obj (∏ᶜ X) ≅ (CGWH.piFan (fun i => (U).obj (X i))).pt)
      (ey : (U).obj (∏ᶜ Y) ≅ (CGWH.piFan (fun i => (U).obj (Y i))).pt),
      (U).map (CategoryTheory.Limits.Pi.map f) = ex.hom ≫ CGWH.piFamilyMap (fun i => (U).map (f i)) ≫ ey.inv := by
  let lx := isLimitFanMkObjOfIsLimit U X (CategoryTheory.Limits.Pi.π X) (productIsProduct X)
  let ly := isLimitFanMkObjOfIsLimit U Y (CategoryTheory.Limits.Pi.π Y) (productIsProduct Y)
  let px := CGWH.piFan_isLimit (fun i => (U).obj (X i))
  let py := CGWH.piFan_isLimit (fun i => (U).obj (Y i))
  let ex := lx.conePointUniqueUpToIso px
  let ey := ly.conePointUniqueUpToIso py
  refine ⟨ex, ey, ?_⟩
  apply ly.hom_ext
  rintro ⟨i⟩
  change (U).map (CategoryTheory.Limits.Pi.map f) ≫ (U).map (CategoryTheory.Limits.Pi.π Y i) =
    (ex.hom ≫ CGWH.piFamilyMap (fun i => (U).map (f i)) ≫ ey.inv) ≫ (U).map (CategoryTheory.Limits.Pi.π Y i)
  have hx := lx.conePointUniqueUpToIso_hom_comp px (Discrete.mk i)
  have hy := ly.conePointUniqueUpToIso_inv_comp py (Discrete.mk i)
  change ex.hom ≫ (CGWH.piFan (fun i => (U).obj (X i))).proj i = (U).map (CategoryTheory.Limits.Pi.π X i) at hx
  change ey.inv ≫ (U).map (CategoryTheory.Limits.Pi.π Y i) = (CGWH.piFan (fun i => (U).obj (Y i))).proj i at hy
  rw [← (U).map_comp, CategoryTheory.Limits.Pi.map_π, (U).map_comp, Category.assoc, Category.assoc, hy,
    CGWH.piFamilyMap_projection, ← Category.assoc, hx]

private theorem rankSpace_coproduct_comparison {I : Type u} {X Y : I → RankSpace α}
    [HasCoproduct X] [HasCoproduct Y] [PreservesColimit (Discrete.functor X) U]
    [PreservesColimit (Discrete.functor Y) U] (f : ∀ i, X i ⟶ Y i) :
    ∃ (ex : (U).obj (∐ X) ≅ (CGWH.coproductCofan (fun i => (U).obj (X i))).pt)
      (ey : (U).obj (∐ Y) ≅ (CGWH.coproductCofan (fun i => (U).obj (Y i))).pt),
      (U).map (CategoryTheory.Limits.Sigma.map f) = ex.hom ≫ CGWH.coproductFamilyMap (fun i => (U).map (f i)) ≫ ey.inv := by
  let lx := isColimitCofanMkObjOfIsColimit U X (CategoryTheory.Limits.Sigma.ι X) (coproductIsCoproduct X)
  let ly := isColimitCofanMkObjOfIsColimit U Y (CategoryTheory.Limits.Sigma.ι Y) (coproductIsCoproduct Y)
  let px := CGWH.coproductCofan_isColimit (fun i => (U).obj (X i))
  let py := CGWH.coproductCofan_isColimit (fun i => (U).obj (Y i))
  let ex := lx.coconePointUniqueUpToIso px
  let ey := ly.coconePointUniqueUpToIso py
  refine ⟨ex, ey, ?_⟩
  apply lx.hom_ext
  rintro ⟨i⟩
  change (U).map (CategoryTheory.Limits.Sigma.ι X i) ≫ (U).map (CategoryTheory.Limits.Sigma.map f) =
    (U).map (CategoryTheory.Limits.Sigma.ι X i) ≫ (ex.hom ≫ CGWH.coproductFamilyMap (fun i => (U).map (f i)) ≫ ey.inv)
  have hx := lx.comp_coconePointUniqueUpToIso_hom px (Discrete.mk i)
  have hy := ly.comp_coconePointUniqueUpToIso_inv py (Discrete.mk i)
  change (U).map (CategoryTheory.Limits.Sigma.ι X i) ≫ ex.hom = (CGWH.coproductCofan (fun i => (U).obj (X i))).inj i at hx
  change (CGWH.coproductCofan (fun i => (U).obj (Y i))).inj i ≫ ey.inv = (U).map (CategoryTheory.Limits.Sigma.ι Y i) at hy
  rw [← (U).map_comp, CategoryTheory.Limits.Sigma.ι_map, (U).map_comp, ← Category.assoc, hx, ← Category.assoc,
    CGWH.coproductFamilyMap_inclusion, Category.assoc, hy]

include hα hcard hν hc in
theorem rankSpace_product_map {I : Type u} {X Y : I → RankSpace α}
    [HasProduct X] [HasProduct Y] [PreservesLimit (Discrete.functor X) U]
    [PreservesLimit (Discrete.functor Y) U] (f : ∀ i, X i ⟶ Y i) :
    ((∀ i, Mono (f i)) → Mono (CategoryTheory.Limits.Pi.map f)) ∧
      ((∀ i, IsRegularMono (f i)) → IsRegularMono (CategoryTheory.Limits.Pi.map f)) ∧
      (Finite I → ((∀ i, Epi (f i)) → Epi (CategoryTheory.Limits.Pi.map f)) ∧
        ((∀ i, IsRegularEpi (f i)) → IsRegularEpi (CategoryTheory.Limits.Pi.map f))) := by
  simp only [rankSpace_mono_iff hα hcard hν hc, rankSpace_epi_iff hα hcard hν hc,
    rankSpace_regularMono_iff hα hcard hν hc, rankSpace_regularEpi_iff hα hcard hν hc,
    ← CGWH.mono_iff_injective, ← CGWH.epi_iff_denseRange,
    ← CGWH.regularMono_iff_closedEmbedding, ← CGWH.regularEpi_iff_quotient]
  obtain ⟨ex, ey, h⟩ := rankSpace_product_comparison f
  rw [h]
  let g := fun i => (U).map (f i)
  refine ⟨fun hf => ?_, fun hf => ?_, fun hI => ⟨fun hf => ?_, fun hf => ?_⟩⟩
  · exact (CGWH.regularity_composition _ _).1 inferInstance
      ((CGWH.regularity_composition _ _).1 (CGWH.piFamilyMap_mono g hf) inferInstance)
  · exact (CGWH.regularity_composition _ _).2.2.1 inferInstance
      ((CGWH.regularity_composition _ _).2.2.1 (CGWH.piFamilyMap_regularMono g hf) inferInstance)
  · letI := hI
    exact (CGWH.regularity_composition _ _).2.1 inferInstance
      ((CGWH.regularity_composition _ _).2.1 (CGWH.piFamilyMap_epi g hf) inferInstance)
  · letI := hI
    exact (CGWH.regularity_composition _ _).2.2.2 inferInstance
      ((CGWH.regularity_composition _ _).2.2.2 (CGWH.piFamilyMap_regularEpi g hf) inferInstance)

include hα hcard hν hc in
theorem rankSpace_coproduct_map {I : Type u} {X Y : I → RankSpace α}
    [HasCoproduct X] [HasCoproduct Y] [PreservesColimit (Discrete.functor X) U]
    [PreservesColimit (Discrete.functor Y) U] (f : ∀ i, X i ⟶ Y i) :
    ((∀ i, Mono (f i)) → Mono (CategoryTheory.Limits.Sigma.map f)) ∧
      ((∀ i, IsRegularMono (f i)) → IsRegularMono (CategoryTheory.Limits.Sigma.map f)) ∧
      ((∀ i, Epi (f i)) → Epi (CategoryTheory.Limits.Sigma.map f)) ∧
      ((∀ i, IsRegularEpi (f i)) → IsRegularEpi (CategoryTheory.Limits.Sigma.map f)) := by
  simp only [rankSpace_mono_iff hα hcard hν hc, rankSpace_epi_iff hα hcard hν hc,
    rankSpace_regularMono_iff hα hcard hν hc, rankSpace_regularEpi_iff hα hcard hν hc,
    ← CGWH.mono_iff_injective, ← CGWH.epi_iff_denseRange,
    ← CGWH.regularMono_iff_closedEmbedding, ← CGWH.regularEpi_iff_quotient]
  obtain ⟨ex, ey, h⟩ := rankSpace_coproduct_comparison f
  rw [h]
  let g := fun i => (U).map (f i)
  refine ⟨fun hf => ?_, fun hf => ?_, fun hf => ?_, fun hf => ?_⟩
  · exact (CGWH.regularity_composition _ _).1 inferInstance
      ((CGWH.regularity_composition _ _).1 (CGWH.coproductFamilyMap_mono g hf) inferInstance)
  · exact (CGWH.regularity_composition _ _).2.2.1 inferInstance
      ((CGWH.regularity_composition _ _).2.2.1 (CGWH.coproductFamilyMap_regularMono g hf) inferInstance)
  · exact (CGWH.regularity_composition _ _).2.1 inferInstance
      ((CGWH.regularity_composition _ _).2.1 (CGWH.coproductFamilyMap_epi g hf) inferInstance)
  · exact (CGWH.regularity_composition _ _).2.2.2 inferInstance
      ((CGWH.regularity_composition _ _).2.2.2 (CGWH.coproductFamilyMap_regularEpi g hf) inferInstance)

end

end Masullo
