import FiberedGrothendieck
import StrictFiberedProducts
import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete

open CategoryTheory CategoryTheory.Functor Opposite
open scoped Bicategory Pseudofunctor.StrongTrans CategoryTheory.BasedFunctor

namespace Masullo.SplitFibered

open CategoryTheory.Pseudofunctor.CoGrothendieck

universe u

variable {D : Type u} [SmallCategory D]

abbrev Diagram := Dᵒᵖ ⥤ Cat.{u, u}

private theorem eqToHom_comp_id {C : Type*} [Category C] {a b : C} (h k : a = b) :
    eqToHom h = eqToHom k ≫ 𝟙 b :=
  (Category.comp_id (eqToHom k)).symm

private theorem eqToHom_comp_id_comp {C : Type*} [Category C] {a b c : C}
    (h : a = c) (k : a = b) (l : b = c) :
    eqToHom h = eqToHom k ≫ 𝟙 b ≫ eqToHom l := by
  subst b
  subst c
  simp

set_option backward.isDefEq.respectTransparency false in
/-- Ordinary natural transformations of strict diagrams act on the split
Grothendieck categories by their equality-valued naturality constraints. -/
def strongOfNatural {F G : Diagram (D := D)} (t : F ⟶ G) :
    F.toPseudofunctor' ⟶ G.toPseudofunctor' where
  app X := t.app X.as
  naturality f := eqToIso (t.naturality f.as)
  naturality_naturality η := by
    obtain rfl := LocallyDiscrete.eq_of_hom η
    have e : η = 𝟙 _ := Subsingleton.elim _ _
    subst η
    simp
  naturality_id X := by
    rw [Bicategory.Strict.leftUnitor_eqToIso, Bicategory.Strict.rightUnitor_eqToIso]
    simp [Functor.toPseudofunctor'_mapId]
    exact eqToHom_comp_id _ _
  naturality_comp f g := by
    simp [Functor.toPseudofunctor'_mapComp, Bicategory.Strict.associator_eqToIso]
    exact eqToHom_comp_id_comp _ _ _

abbrev total (F : Diagram (D := D)) := Pseudofunctor.CoGrothendieck F.toPseudofunctor'

abbrev projection (F : Diagram (D := D)) : total F ⥤ D := forget F.toPseudofunctor'

abbrev based (F : Diagram (D := D)) : BasedCategory.{u, u} D :=
  BasedCategory.ofFunctor (projection F)

def mapBased {F G : Diagram (D := D)} (t : F ⟶ G) : based F ⥤ᵇ based G where
  toFunctor := Pseudofunctor.CoGrothendieck.map (strongOfNatural t)
  w := rfl

@[simp] theorem mapBased_obj_base {F G : Diagram (D := D)} (t : F ⟶ G) (x : total F) :
    ((mapBased t).obj x : total G).base = x.base := rfl

@[simp] theorem mapBased_obj_fiber {F G : Diagram (D := D)} (t : F ⟶ G) (x : total F) :
    ((mapBased t).obj x : total G).fiber = (t.app (op x.base)).toFunctor.obj x.fiber := rfl

/-- The compatibility square in a strict split diagram gives a literal
equality after changing base. -/
theorem mapBased_cartesianDomain_eq {F G : Diagram (D := D)} (t : F ⟶ G)
    {R S : D} (x : F.obj (op S)) (f : R ⟶ S) :
    (mapBased t).obj (domainCartesianLift (F := F.toPseudofunctor') x f) =
      domainCartesianLift (F := G.toPseudofunctor') ((t.app (op S)).toFunctor.obj x) f := by
  apply congrArg (fun y => Pseudofunctor.CoGrothendieck.mk R y)
  exact congrArg (fun k : F.obj (op S) ⟶ G.obj (op R) => k.toFunctor.obj x)
    (t.naturality f.op)

theorem cat_eqToHom_app {C D : Cat.{u,u}} {f g : C ⟶ D} (h : f = g) (x : C) :
    (eqToHom h).toNatTrans.app x = eqToHom (congrArg (fun k : C ⟶ D => k.toFunctor.obj x) h) := by
  cases h
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem cartesianLift_transport {F : Diagram (D := D)} {R S : D}
    (f : R ⟶ S) (y : F.obj (op S)) {x : F.obj (op R)}
    (h : x = ((F.map f.op).toFunctor.obj y)) :
    (⟨f, eqToHom h⟩ : (⟨R, x⟩ : total F) ⟶ ⟨S, y⟩) =
      eqToHom (congrArg (fun z => Pseudofunctor.CoGrothendieck.mk R z) h) ≫
        cartesianLift (F := F.toPseudofunctor') y f := by
  subst x
  simp
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem mapBased_cartesian_eq {F G : Diagram (D := D)} (t : F ⟶ G)
    {R S : D} (x : F.obj (op S)) (f : R ⟶ S) :
    (mapBased t).map (cartesianLift (F := F.toPseudofunctor') x f) =
      eqToHom (mapBased_cartesianDomain_eq t x f) ≫
        cartesianLift (F := G.toPseudofunctor') ((t.app (op S)).toFunctor.obj x) f := by
  let h : (t.app (op R)).toFunctor.obj ((F.map f.op).toFunctor.obj x) =
      (G.map f.op).toFunctor.obj ((t.app (op S)).toFunctor.obj x) :=
    congrArg (fun k : F.obj (op S) ⟶ G.obj (op R) => k.toFunctor.obj x)
      (t.naturality f.op)
  refine Eq.trans ?_ (cartesianLift_transport f _ h)
  refine Hom.ext _ _ (show f = f from rfl) ?_
  simp only [eqToHom_refl, Category.comp_id, mapBased,
    Pseudofunctor.CoGrothendieck.map_map_fiber]
  change (t.app (op R)).toFunctor.map (𝟙 _) ≫
    (eqToHom (t.naturality f.op)).toNatTrans.app x = eqToHom h
  rw [CategoryTheory.Functor.map_id, Category.id_comp]
  exact cat_eqToHom_app _ _


open VerticalIsoComma in
set_option backward.isDefEq.respectTransparency false in
theorem mapBased_preserves {F G : Diagram (D := D)} (t : F ⟶ G) :
    PreservesCartesian (mapBased t) := by
  apply preserves_of_lifts
  rintro ⟨U, x⟩ R f
  change R ⟶ U at f
  refine ⟨domainCartesianLift x f, cartesianLift x f,
    isStronglyCartesian_homCartesianLift x f, ?_⟩
  rw [mapBased_cartesian_eq]
  have h := mapBased_cartesianDomain_eq t x f
  have h₁ : (projection G).IsHomLift (𝟙 R) (eqToHom h) := by
    apply IsHomLift.of_fac' _ _ _ rfl rfl
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id, eqToHom_map]
    rfl
  letI := h₁
  haveI : (projection G).IsStronglyCartesian (𝟙 R) (eqToHom h) :=
    IsStronglyCartesian.of_isIso _ _ _
  haveI := isStronglyCartesian_homCartesianLift (F := G.toPseudofunctor')
    ((t.app (op U)).toFunctor.obj x) f
  have he : (projection G).IsStronglyCartesian (𝟙 R ≫ f)
      (eqToHom h ≫ cartesianLift (F := G.toPseudofunctor')
        ((t.app (op U)).toFunctor.obj x) f) := IsStronglyCartesian.comp (projection G)
  rw [Category.id_comp] at he
  exact he

set_option backward.isDefEq.respectTransparency false in
private theorem cartesianLift_naturality {F : Diagram (D := D)} {R S : D}
    (f : R ⟶ S) {x y : F.obj (op S)} (h : x = y) :
    cartesianLift (F := F.toPseudofunctor') x f ≫
        eqToHom (congrArg (fun z => Pseudofunctor.CoGrothendieck.mk S z) h) =
      eqToHom (congrArg (fun z => domainCartesianLift (F := F.toPseudofunctor') z f) h) ≫
        cartesianLift (F := F.toPseudofunctor') y f := by
  cases h
  simp

open VerticalIsoComma in
set_option backward.isDefEq.respectTransparency false in
theorem split_hasComponentLifts {F G H : Diagram (D := D)} (t : F ⟶ H) (s : G ⟶ H) :
    HasComponentLifts (mapBased t) (mapBased s) := by
  rintro ⟨⟨⟨U, x⟩, ⟨V, y⟩, e, he⟩, ⟨h, heq⟩⟩ R f
  have hb : U = V := congrArg Pseudofunctor.CoGrothendieck.base h
  subst V
  change (⟨U, (t.app (op U)).toFunctor.obj x⟩ : total H) =
    ⟨U, (s.app (op U)).toFunctor.obj y⟩ at h
  have hxy : (t.app (op U)).toFunctor.obj x = (s.app (op U)).toFunctor.obj y := by
    have he := (Pseudofunctor.CoGrothendieck.mk.inj h).2
    exact eq_of_heq he
  let l := domainCartesianLift (F := F.toPseudofunctor') x f
  let r := domainCartesianLift (F := G.toPseudofunctor') y f
  let el := mapBased_cartesianDomain_eq t x f
  let er := mapBased_cartesianDomain_eq s y f
  let ec := congrArg (fun z => domainCartesianLift (F := H.toPseudofunctor') z f) hxy
  let h' : (mapBased t).obj l = (mapBased s).obj r := el.trans (ec.trans er.symm)
  let b : Obj (mapBased t) (mapBased s) := ⟨l, r, eqToIso h', by
    dsimp
    have hh := congrArg (fun z : total H => z.base) h'
    have hb : ((projection H).map (eqToHom h')) = 𝟙 R := by
      rw [eqToHom_map]
      rfl
    apply IsHomLift.of_fac' _ _ _ rfl rfl
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    exact hb⟩
  let m := cartesianLift (F := F.toPseudofunctor') x f
  let n := cartesianLift (F := G.toPseudofunctor') y f
  have ht : e.hom = eqToHom
      (congrArg (fun z => Pseudofunctor.CoGrothendieck.mk U z) hxy) := heq
  have hstep := cartesianLift_naturality f (F := H) hxy
  have hchain : eqToHom el ≫ eqToHom ec = eqToHom h' ≫ eqToHom er := by
    simp only [eqToHom_trans]
  have hsq : (mapBased t).map m ≫ e.hom = b.iso.hom ≫ (mapBased s).map n := by
    calc
      _ = eqToHom el ≫ (cartesianLift (F := H.toPseudofunctor')
         ((t.app (op U)).toFunctor.obj x) f ≫
           eqToHom (congrArg (fun z => Pseudofunctor.CoGrothendieck.mk U z) hxy)) := by
        rw [ht, mapBased_cartesian_eq, Category.assoc]
      _ = (eqToHom el ≫ eqToHom ec) ≫ cartesianLift (F := H.toPseudofunctor')
          ((s.app (op U)).toFunctor.obj y) f := by
        rw [hstep, Category.assoc]
      _ = _ := by
        rw [hchain, Category.assoc]
        exact congrArg (eqToHom h' ≫ ·) (mapBased_cartesian_eq s y f).symm
  have hn : (based G).p.IsHomLift ((based F).p.map m) n :=
    isHomLift_cartesianLift y f
  exact ⟨⟨b, ⟨h', rfl⟩⟩, ⟨⟨m, n, hn, hsq⟩⟩,
    isStronglyCartesian_homCartesianLift x f, isStronglyCartesian_homCartesianLift y f⟩


open VerticalIsoComma in
/-- A strict pullback of split Grothendieck categories has the strict
universal property among fibered categories and Cartesian functors. -/
theorem split_strict_universal {F G H : Diagram (D := D)} (t : F ⟶ H) (s : G ⟶ H)
    {T : BasedCategory.{u, u} D}
    (A : T ⥤ᵇ based F) (B : T ⥤ᵇ based G)
    (h : A ⋙ mapBased t = B ⋙ mapBased s)
    (hA : PreservesCartesian A) (hB : PreservesCartesian B) :
    ∃! L : T ⥤ᵇ strictBased (mapBased t) (mapBased s),
      L ⋙ strictFst (mapBased t) (mapBased s) = A ∧
      L ⋙ strictSnd (mapBased t) (mapBased s) = B ∧ PreservesCartesian L := by
  let J := strictLift (mapBased t) (mapBased s) A B h
  have hJ := strictLift_projections (mapBased t) (mapBased s) A B h
  have hu := strictLift_unique (mapBased t) (mapBased s) A B h
  exact ⟨J, ⟨hJ.1, hJ.2, strictLift_preserves _ _ (mapBased_preserves s) A B h hA hB⟩,
    fun L hL => hu.unique ⟨hL.1, hL.2.1⟩ hJ⟩

private theorem split_vertical_isIso (F : Diagram (D := D))
    (hF : ∀ (U : D) (a b : F.obj (op U)) (m : a ⟶ b), IsIso m)
    (U : D) {a b : total F} (m : a ⟶ b) (hm : (projection F).IsHomLift (𝟙 U) m) :
    IsIso m := by
  letI := hm
  let x : Fiber (projection F) U := ⟨a, IsHomLift.domain_eq (projection F) (𝟙 U) m⟩
  let y : Fiber (projection F) U := ⟨b, IsHomLift.codomain_eq (projection F) (𝟙 U) m⟩
  let n : x ⟶ y := ⟨m, hm⟩
  letI := FiberedGrothendieck.fiber_all_isIso_of_groupoid F.toPseudofunctor' hF U n
  exact (inferInstance : IsIso ((Fiber.fiberInclusion (p := projection F) (S := U)).map n))

open VerticalIsoComma in
/-- When the two source diagrams take values in groupoids, the strict
Grothendieck pullback is fibered in groupoids, with Cartesian projections. -/
theorem split_strict_fibered_in_groupoids {F G H : Diagram (D := D)}
    (t : F ⟶ H) (s : G ⟶ H)
    (hF : ∀ (U : D) (a b : F.obj (op U)) (m : a ⟶ b), IsIso m)
    (hG : ∀ (U : D) (a b : G.obj (op U)) (m : a ⟶ b), IsIso m) :
    let P := strictBased (mapBased t) (mapBased s)
    P.p.IsFibered ∧
      PreservesCartesian (strictFst (mapBased t) (mapBased s)) ∧
      PreservesCartesian (strictSnd (mapBased t) (mapBased s)) ∧
      ∀ (U : D) (a b : Fiber P.p U) (m : a ⟶ b), IsIso m := by
  intro P
  haveI : (based F).p.IsFibered := FiberedGrothendieck.fibered _
  haveI : (based G).p.IsFibered := FiberedGrothendieck.fibered _
  obtain ⟨hp, -, hl, hr⟩ := strictFibered_projections (mapBased t) (mapBased s)
    (mapBased_preserves t) (mapBased_preserves s) (split_hasComponentLifts t s)
  exact ⟨hp, hl, hr, fun U _ _ m =>
    strictFiber_isGroupoid (mapBased t) (mapBased s)
      (fun V {_ _} m hm => split_vertical_isIso F hF V m hm)
      (fun V {_ _} m hm => split_vertical_isIso G hG V m hm) U m⟩


end Masullo.SplitFibered
