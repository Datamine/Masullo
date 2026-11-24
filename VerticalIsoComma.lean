import Mathlib.CategoryTheory.FiberedCategory.BasedCategory
import Mathlib.CategoryTheory.SingleObj
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.Group.TypeTags.Basic

open CategoryTheory CategoryTheory.Functor CategoryTheory.IsHomLift
open scoped CategoryTheory.BasedFunctor

namespace Masullo

universe u

namespace VerticalIsoComma

variable {D : Type u} [SmallCategory D]
  {X Y S : BasedCategory.{u, u} D} (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S)

/-- The comparison isomorphism in the two-fiber product over a base
lifts an identity of the base. -/
structure Obj where
  left : X.obj
  right : Y.obj
  iso : F.obj left ≅ G.obj right
  vertical : S.p.IsHomLift (𝟙 (X.p.obj left)) iso.hom

variable {F G}

instance (a : Obj F G) : S.p.IsHomLift (𝟙 (X.p.obj a.left)) a.iso.hom :=
  a.vertical

theorem base_eq (a : Obj F G) : Y.p.obj a.right = X.p.obj a.left :=
  (G.w_obj a.right).symm.trans (codomain_eq S.p (𝟙 (X.p.obj a.left)) a.iso.hom)

@[ext]
structure Arrow (a b : Obj F G) where
  left : a.left ⟶ b.left
  right : a.right ⟶ b.right
  over : Y.p.IsHomLift (X.p.map left) right
  square : F.map left ≫ b.iso.hom = a.iso.hom ≫ G.map right

instance {a b : Obj F G} (f : Arrow a b) : Y.p.IsHomLift (X.p.map f.left) f.right :=
  f.over

instance : SmallCategory (Obj F G) where
  Hom := Arrow
  id a := ⟨𝟙 _, 𝟙 _, by
    rw [CategoryTheory.Functor.map_id]
    exact IsHomLift.id (base_eq a), by simp⟩
  comp f g := ⟨f.left ≫ g.left, f.right ≫ g.right, by
    rw [CategoryTheory.Functor.map_comp]
    infer_instance, by
    simp only [CategoryTheory.Functor.map_comp, Category.assoc]
    rw [g.square, ← Category.assoc, f.square, Category.assoc]⟩
  id_comp f := Arrow.ext (Category.id_comp _) (Category.id_comp _)
  comp_id f := Arrow.ext (Category.comp_id _) (Category.comp_id _)
  assoc f g h := Arrow.ext (Category.assoc _ _ _) (Category.assoc _ _ _)

theorem sameBase {a b : Obj F G} {U V : D}
    (f : U ⟶ V) (α : a.left ⟶ b.left) (β : a.right ⟶ b.right)
    [ha : X.p.IsHomLift f α] [hb : Y.p.IsHomLift f β] :
    Y.p.IsHomLift (X.p.map α) β := by
  apply IsHomLift.of_fac' Y.p _ _ (base_eq a) (base_eq b)
  rw [IsHomLift.fac' Y.p f β, IsHomLift.fac' X.p f α]
  simp [Category.assoc]

variable (F G)

/-- The comma category with its projection to the base. -/
def based : BasedCategory.{u, u} D :=
  BasedCategory.ofFunctor
    ({ obj := fun a : Obj F G => X.p.obj a.left
       map := fun f => X.p.map f.left
       map_id := fun a => X.p.map_id a.left
       map_comp := fun f g => X.p.map_comp f.left g.left } : Obj F G ⥤ D)

def fst : based F G ⥤ᵇ X where
  toFunctor := { obj := Obj.left, map := Arrow.left, map_id := fun _ => rfl, map_comp := fun _ _ => rfl }
  w := rfl

def snd : based F G ⥤ᵇ Y where
  toFunctor := { obj := Obj.right, map := Arrow.right, map_id := fun _ => rfl, map_comp := fun _ _ => rfl }
  w := by
    refine CategoryTheory.Functor.ext (fun a => base_eq a) ?_
    intro a b f
    exact @IsHomLift.fac' _ _ _ _ Y.p _ _ _ _ (X.p.map f.left) f.right f.over

def comparison : (fst F G ⋙ F) ≅ (snd F G ⋙ G) :=
  BasedNatIso.mkNatIso
    (NatIso.ofComponents (fun a => a.iso) (fun f => f.square))
    (fun a => a.vertical)

variable {T : BasedCategory.{u, u} D}

private def liftObj (A : T ⥤ᵇ X) (B : T ⥤ᵇ Y) (i : (A ⋙ F) ≅ (B ⋙ G))
    (a : T.obj) : Obj F G :=
  ⟨A.obj a, B.obj a, (BasedNatTrans.forgetful T S).mapIso i |>.app a,
    i.hom.isHomLift (A.w_obj a).symm⟩

/-- The functor induced by any pair of based functors and a vertical
isomorphism between their composites. -/
def lift (A : T ⥤ᵇ X) (B : T ⥤ᵇ Y) (i : (A ⋙ F) ≅ (B ⋙ G)) :
    T ⥤ᵇ based F G where
  toFunctor := {
    obj := liftObj F G A B i
    map {a b} f := ⟨A.map f, B.map f,
      by
        have hA : X.p.IsHomLift (T.p.map f) (A.map f) :=
          BasedFunctor.preserves_isHomLift A (T.p.map f) f
        have hB : Y.p.IsHomLift (T.p.map f) (B.map f) :=
          BasedFunctor.preserves_isHomLift B (T.p.map f) f
        exact sameBase (a := liftObj F G A B i a) (b := liftObj F G A B i b)
          (T.p.map f) (A.map f) (B.map f) (ha := hA) (hb := hB),
      i.hom.toNatTrans.naturality f⟩
    map_id a := Arrow.ext (A.map_id a) (B.map_id a)
    map_comp f g := Arrow.ext (A.map_comp f g) (B.map_comp f g) }
  w := A.w

theorem lift_fst (A : T ⥤ᵇ X) (B : T ⥤ᵇ Y) (i : (A ⋙ F) ≅ (B ⋙ G)) :
    lift F G A B i ⋙ fst F G = A := by
  cases A
  rfl

theorem lift_snd (A : T ⥤ᵇ X) (B : T ⥤ᵇ Y) (i : (A ⋙ F) ≅ (B ⋙ G)) :
    lift F G A B i ⋙ snd F G = B := by
  cases B
  rfl

theorem lift_comparison (A : T ⥤ᵇ X) (B : T ⥤ᵇ Y) (i : (A ⋙ F) ≅ (B ⋙ G))
    (a : T.obj) : ((lift F G A B i).obj a).iso.hom = i.hom.toNatTrans.app a := rfl

variable {F G}

/-- A commuting pair of vertical isomorphisms gives an isomorphism in
the two-fiber product. -/
def objectIso {a b : Obj F G}
    (α : a.left ≅ b.left) (β : a.right ≅ b.right)
    (ha : X.p.IsHomLift (𝟙 (X.p.obj a.left)) α.hom)
    (hb : Y.p.IsHomLift (𝟙 (X.p.obj a.left)) β.hom)
    (hc : F.map α.hom ≫ b.iso.hom = a.iso.hom ≫ G.map β.hom) : a ≅ b where
  hom := ⟨α.hom, β.hom, sameBase (𝟙 (X.p.obj a.left)) α.hom β.hom, hc⟩
  inv := ⟨α.inv, β.inv, by
    haveI : Y.p.IsHomLift (𝟙 (X.p.obj a.left)) β.inv :=
      IsHomLift.lift_id_inv Y.p (X.p.obj a.left) β
    haveI : X.p.IsHomLift (𝟙 (X.p.obj a.left)) α.inv :=
      IsHomLift.lift_id_inv X.p (X.p.obj a.left) α
    exact sameBase (𝟙 (X.p.obj a.left)) α.inv β.inv, by
    apply (cancel_mono (G.map β.hom)).mp
    rw [Category.assoc, Category.assoc, ← CategoryTheory.Functor.map_comp, β.inv_hom_id, CategoryTheory.Functor.map_id,
      Category.comp_id, ← hc, ← Category.assoc, ← CategoryTheory.Functor.map_comp,
      α.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]⟩
  hom_inv_id := Arrow.ext α.hom_inv_id β.hom_inv_id
  inv_hom_id := Arrow.ext α.inv_hom_id β.inv_hom_id

/-- The universal lifting property on isomorphisms. The projected
isomorphisms determine the lifted isomorphism uniquely. -/
theorem uniqueIsoLift (A B : T ⥤ᵇ based F G)
    (α : (A ⋙ fst F G) ≅ (B ⋙ fst F G))
    (β : (A ⋙ snd F G) ≅ (B ⋙ snd F G))
    (h : ∀ a : T.obj, F.map (α.hom.toNatTrans.app a) ≫ (B.obj a).iso.hom =
      (A.obj a).iso.hom ≫ G.map (β.hom.toNatTrans.app a)) :
    ∃! i : A ≅ B, ∀ a : T.obj,
      (i.hom.toNatTrans.app a).left = α.hom.toNatTrans.app a ∧
      (i.hom.toNatTrans.app a).right = β.hom.toNatTrans.app a := by
  let α' (a : T.obj) := ((BasedNatTrans.forgetful T X).mapIso α).app a
  let β' (a : T.obj) := ((BasedNatTrans.forgetful T Y).mapIso β).app a
  have hbase (a : T.obj) : X.p.obj (A.obj a).left = T.p.obj a := A.w_obj a
  let I (a : T.obj) := objectIso (α' a) (β' a)
    (α.hom.isHomLift (hbase a).symm) (β.hom.isHomLift (hbase a).symm) (h a)
  let i : A ≅ B := BasedNatIso.mkNatIso (NatIso.ofComponents I (fun f => by
    apply Arrow.ext
    · exact α.hom.toNatTrans.naturality f
    · exact β.hom.toNatTrans.naturality f))
    (fun a => by
      apply IsHomLift.of_fac' _ _ _ (A.w_obj a) (B.w_obj a)
      change X.p.map (α' a).hom = _
      haveI : X.p.IsHomLift (𝟙 (T.p.obj a)) (α' a).hom :=
        α.hom.isHomLift rfl
      exact IsHomLift.fac' X.p (𝟙 (T.p.obj a)) (α' a).hom)
  refine ⟨i, fun a => ⟨rfl, rfl⟩, ?_⟩
  intro j hj
  apply Iso.ext
  apply BasedNatTrans.ext
  apply NatTrans.ext
  funext a
  exact Arrow.ext (hj a).1 (hj a).2


/-- The unrestricted comma object formula admits a nonvertical
comparison arrow even when all three categories are the base itself. -/
theorem unrestrictedComparison_not_vertical :
    let D := SingleObj (Multiplicative ℤ)
    let x := SingleObj.star (Multiplicative ℤ)
    let f : x ⟶ x := Multiplicative.ofAdd (1 : ℤ)
    ∃ i : x ≅ x, i.hom = f ∧ ¬ (CategoryTheory.Functor.id D).IsHomLift (𝟙 x) i.hom := by
  dsimp only
  let x := SingleObj.star (Multiplicative ℤ)
  let f : x ⟶ x := Multiplicative.ofAdd (1 : ℤ)
  refine ⟨asIso f, rfl, ?_⟩
  intro h
  have he := @IsHomLift.eq_of_isHomLift _ _ _ _
    (CategoryTheory.Functor.id (SingleObj (Multiplicative ℤ))) x x (𝟙 x) f h
  have hz : (0 : ℤ) = 1 := congrArg Multiplicative.toAdd he
  omega

end VerticalIsoComma

end Masullo
