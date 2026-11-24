import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Bicategory.InducedBicategory
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.Whiskering

open CategoryTheory Function Set

namespace Masullo

universe u

/-- A small category described by sets of objects and arrows. Composition
uses categorical order, with the first arrow followed by the second. -/
structure EffectiveCategory where
  Obj : Type u
  Arrow : Type u
  source : Arrow → Obj
  target : Arrow → Obj
  unit : Obj → Arrow
  compose : (a b : Arrow) → target a = source b → Arrow
  source_unit : ∀ x, source (unit x) = x
  target_unit : ∀ x, target (unit x) = x
  source_compose : ∀ a b h, source (compose a b h) = source a
  target_compose : ∀ a b h, target (compose a b h) = target b
  unit_compose : ∀ a, compose (unit (source a)) a (target_unit _) = a
  compose_unit : ∀ a, compose a (unit (target a)) (source_unit _).symm = a
  assoc : ∀ a b c hab hbc,
    compose (compose a b hab) c ((target_compose a b hab).trans hbc) =
      compose a (compose b c hbc) (hab.trans (source_compose b c hbc).symm)

namespace EffectiveCategory

abbrev ArrowBetween (C : EffectiveCategory.{u}) (x y : C.Obj) :=
  {a : C.Arrow // C.source a = x ∧ C.target a = y}

instance instObjectCategory (C : EffectiveCategory.{u}) : SmallCategory C.Obj where
  Hom := C.ArrowBetween
  id x := ⟨C.unit x, C.source_unit x, C.target_unit x⟩
  comp a b := ⟨C.compose a.val b.val (a.property.2.trans b.property.1.symm),
    (C.source_compose _ _ _).trans a.property.1, (C.target_compose _ _ _).trans b.property.2⟩
  id_comp := by
    rintro x y ⟨a, hx, hy⟩
    subst x
    exact Subtype.ext (C.unit_compose a)
  comp_id := by
    rintro x y ⟨a, hx, hy⟩
    subst y
    exact Subtype.ext (C.compose_unit a)
  assoc a b c := Subtype.ext (C.assoc a.val b.val c.val
    (a.property.2.trans b.property.1.symm) (b.property.2.trans c.property.1.symm))

@[simp] theorem id_val (C : EffectiveCategory.{u}) (x : C.Obj) :
    (𝟙 x : x ⟶ x).val = C.unit x := rfl

@[simp] theorem comp_val (C : EffectiveCategory.{u}) {x y z : C.Obj} (a : x ⟶ y) (b : y ⟶ z) :
    (a ≫ b).val = C.compose a.val b.val (a.property.2.trans b.property.1.symm) := rfl

@[ext]
structure Hom (C D : EffectiveCategory.{u}) where
  obj : C.Obj → D.Obj
  arrow : C.Arrow → D.Arrow
  source_arrow : ∀ a, D.source (arrow a) = obj (C.source a)
  target_arrow : ∀ a, D.target (arrow a) = obj (C.target a)
  map_unit : ∀ x, arrow (C.unit x) = D.unit (obj x)
  map_compose : ∀ a b h, arrow (C.compose a b h) = D.compose (arrow a) (arrow b)
    ((target_arrow a).trans ((congrArg obj h).trans (source_arrow b).symm))

instance : Category EffectiveCategory.{u} where
  Hom := Hom
  id C := ⟨id, id, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ _ _ => rfl⟩
  comp f g :=
    { obj := g.obj ∘ f.obj
      arrow := g.arrow ∘ f.arrow
      source_arrow := fun x => (g.source_arrow (f.arrow x)).trans (congrArg g.obj (f.source_arrow x))
      target_arrow := fun x => (g.target_arrow (f.arrow x)).trans (congrArg g.obj (f.target_arrow x))
      map_unit := fun x => (congrArg g.arrow (f.map_unit x)).trans (g.map_unit _)
      map_compose := fun a b h => (congrArg g.arrow (f.map_compose a b h)).trans (g.map_compose _ _ _) }

def Hom.toFunctor {C D : EffectiveCategory.{u}} (f : Hom C D) : C.Obj ⥤ D.Obj where
  obj := f.obj
  map a := ⟨f.arrow a.val, (f.source_arrow _).trans (congrArg f.obj a.property.1),
    (f.target_arrow _).trans (congrArg f.obj a.property.2)⟩
  map_id x := Subtype.ext (f.map_unit x)
  map_comp a b := Subtype.ext (f.map_compose a.val b.val _)

/-- Lemma E.5.4.2. The dependent hom types are the fibres of the source
and target maps, and the assignments on objects and arrows are functorial. -/
def toCat : EffectiveCategory.{u} ⥤ Cat.{u, u} where
  obj C := Cat.of C.Obj
  map f := (Hom.toFunctor f).toCatHom

private def functorArrow {C D : EffectiveCategory.{u}} (F : C.Obj ⥤ D.Obj) (a : C.Arrow) : D.Arrow :=
  (F.map (show C.source a ⟶ C.target a from ⟨a, rfl, rfl⟩)).val

private theorem functorArrow_eq {C D : EffectiveCategory.{u}} (F : C.Obj ⥤ D.Obj)
    {x y : C.Obj} (a : x ⟶ y) : functorArrow F a.val = (F.map a).val := by
  obtain ⟨a, hx, hy⟩ := a
  subst x
  subst y
  rfl

private theorem compose_congr (D : EffectiveCategory.{u}) {a b c d : D.Arrow}
    (h₁ : a = c) (h₂ : b = d) (hab : D.target a = D.source b) (hcd : D.target c = D.source d) :
    D.compose a b hab = D.compose c d hcd := by
  subst c
  subst d
  rfl

private def fromFunctor {C D : EffectiveCategory.{u}} (F : C.Obj ⥤ D.Obj) : Hom C D where
  obj := F.obj
  arrow := functorArrow F
  source_arrow a := (F.map (show C.source a ⟶ C.target a from ⟨a, rfl, rfl⟩)).property.1
  target_arrow a := (F.map (show C.source a ⟶ C.target a from ⟨a, rfl, rfl⟩)).property.2
  map_unit x := (functorArrow_eq F (𝟙 x)).trans (congrArg Subtype.val (F.map_id x))
  map_compose a b h := by
    let a' : C.source a ⟶ C.target a := ⟨a, rfl, rfl⟩
    let b' : C.target a ⟶ C.target b := ⟨b, h.symm, rfl⟩
    change functorArrow F (a' ≫ b').val = D.compose (functorArrow F a) (functorArrow F b) _
    rw [functorArrow_eq F (a' ≫ b')]
    have hmap := congrArg Subtype.val (F.map_comp a' b')
    change (F.map (a' ≫ b')).val = D.compose (F.map a').val (F.map b').val _ at hmap
    exact hmap.trans (compose_congr D (functorArrow_eq F a').symm (functorArrow_eq F b').symm _ _)

private theorem fromFunctor_toFunctor {C D : EffectiveCategory.{u}} (f : Hom C D) :
    fromFunctor f.toFunctor = f := by
  ext <;> rfl

set_option backward.isDefEq.respectTransparency false in
private theorem toFunctor_fromFunctor {C D : EffectiveCategory.{u}} (F : C.Obj ⥤ D.Obj) :
    (fromFunctor F).toFunctor = F := by
  refine Functor.ext (F := (fromFunctor F).toFunctor) (G := F) (fun _ => rfl) ?_
  intro x y a
  have h : (fromFunctor F).toFunctor.map a = F.map a := Subtype.ext (functorArrow_eq F a)
  change _ = eqToHom (rfl : F.obj x = F.obj x) ≫ F.map a ≫ eqToHom (rfl : F.obj y = F.obj y)
  simpa only [eqToHom_refl, Category.comp_id, Category.id_comp] using h

instance : toCat.{u}.Full where
  map_surjective F := ⟨fromFunctor F.toFunctor, Cat.ext (toFunctor_fromFunctor F.toFunctor)⟩

instance : toCat.{u}.Faithful where
  map_injective h := by
    have h' := congrArg Cat.Hom.toFunctor h
    change Hom.toFunctor _ = Hom.toFunctor _ at h'
    simpa only [fromFunctor_toFunctor] using congrArg fromFunctor h'

/-- Every small category admits a single total arrow set by tagging each
arrow with its endpoints. -/
def ofCat (C : Cat.{u, u}) : EffectiveCategory.{u} where
  Obj := C
  Arrow := Σ x y : C, x ⟶ y
  source a := a.1
  target a := a.2.1
  unit x := ⟨x, x, 𝟙 x⟩
  compose a b h := ⟨a.1, b.2.1, a.2.2 ≫ eqToHom h ≫ b.2.2⟩
  source_unit _ := rfl
  target_unit _ := rfl
  source_compose _ _ _ := rfl
  target_compose _ _ _ := rfl
  unit_compose := by
    rintro ⟨x, y, a⟩
    simp
  compose_unit := by
    rintro ⟨x, y, a⟩
    simp
  assoc := by
    rintro ⟨x, y, a⟩ ⟨y', z, b⟩ ⟨z', w, c⟩ hab hbc
    change y = y' at hab
    change z = z' at hbc
    subst y'
    subst z'
    simp [Category.assoc]

private def untag {C : Cat.{u, u}} {x y : C} (a : (ofCat C).ArrowBetween x y) : x ⟶ y :=
  eqToHom a.property.1.symm ≫ a.val.2.2 ≫ eqToHom a.property.2

@[simp] private theorem untag_mk {C : Cat.{u, u}} {x y : C} (a : x ⟶ y) :
    untag (C := C) (x := x) (y := y) ⟨⟨x, y, a⟩, rfl, rfl⟩ = a := by
  change eqToHom (rfl : x = x) ≫ a ≫ eqToHom (rfl : y = y) = a
  simp

set_option backward.isDefEq.respectTransparency false in
private def untagFunctor (C : Cat.{u, u}) : (ofCat C).Obj ⥤ C where
  obj := id
  map := untag
  map_id x := untag_mk (C := C) (𝟙 (show C from x))
  map_comp := by
    rintro x y z ⟨⟨x', y', f⟩, hx : x' = x, hy : y' = y⟩ ⟨⟨y'', z', g⟩, hy' : y'' = y, hz : z' = z⟩
    subst x'
    subst y'
    subst y''
    subst z'
    change untag (C := C) (x := x) (y := z) ⟨⟨x, z, f ≫ eqToHom (rfl : y = y) ≫ g⟩, rfl, rfl⟩ =
      untag (C := C) (x := x) (y := y) ⟨⟨x, y, f⟩, rfl, rfl⟩ ≫
        untag (C := C) (x := y) (y := z) ⟨⟨y, z, g⟩, rfl, rfl⟩
    simp only [untag_mk, eqToHom_refl, Category.id_comp]

private def tagFunctor (C : Cat.{u, u}) : C ⥤ (ofCat C).Obj where
  obj := id
  map f := ⟨⟨_, _, f⟩, rfl, rfl⟩
  map_id x := rfl
  map_comp {x y z} f g := Subtype.ext (by
    change (⟨x, z, f ≫ g⟩ : (ofCat C).Arrow) = ⟨x, z, f ≫ eqToHom (rfl : y = y) ≫ g⟩
    simp)

set_option backward.isDefEq.respectTransparency false in
private def ofCatIso (C : Cat.{u, u}) : toCat.obj (ofCat C) ≅ C where
  hom := (untagFunctor C).toCatHom
  inv := (tagFunctor C).toCatHom
  hom_inv_id := by
    apply Cat.ext
    change untagFunctor C ⋙ tagFunctor C = 𝟭 (ofCat C).Obj
    refine Functor.ext (F := untagFunctor C ⋙ tagFunctor C) (G := 𝟭 (ofCat C).Obj) (fun _ => rfl) ?_
    rintro x y ⟨⟨x', y', a⟩, hx : x' = x, hy : y' = y⟩
    subst x'
    subst y'
    have hmap : (untagFunctor C ⋙ tagFunctor C).map (⟨⟨x, y, a⟩, rfl, rfl⟩ : x ⟶ y) =
        ⟨⟨x, y, a⟩, rfl, rfl⟩ := by
      apply Subtype.ext
      change (⟨x, y, untag (C := C) ⟨⟨x, y, a⟩, rfl, rfl⟩⟩ : (ofCat C).Arrow) = ⟨x, y, a⟩
      rw [untag_mk]
    change _ = eqToHom (rfl : x = x) ≫
      (⟨⟨x, y, a⟩, rfl, rfl⟩ : x ⟶ y) ≫ eqToHom (rfl : y = y)
    simpa only [Functor.id_map, eqToHom_refl, Category.id_comp, Category.comp_id] using hmap
  inv_hom_id := by
    apply Cat.ext
    change tagFunctor C ⋙ untagFunctor C = 𝟭 C
    refine Functor.ext (F := tagFunctor C ⋙ untagFunctor C) (G := 𝟭 C) (fun _ => rfl) ?_
    intro x y f
    have hmap : (tagFunctor C ⋙ untagFunctor C).map f = f := untag_mk (C := C) f
    change _ = eqToHom (rfl : x = x) ≫ f ≫ eqToHom (rfl : y = y)
    simpa only [Functor.id_map, eqToHom_refl, Category.id_comp, Category.comp_id] using hmap

instance : toCat.{u}.EssSurj where
  mem_essImage C := ⟨ofCat C, ⟨ofCatIso C⟩⟩

/-- Corrected Lemma E.5.4.3. The comparison is an equivalence of categories. -/
noncomputable def comparisonEquivalence : EffectiveCategory.{u} ≌ Cat.{u, u} :=
  letI : toCat.{u}.IsEquivalence := ⟨inferInstance, inferInstance, inferInstance⟩
  toCat.asEquivalence

/-- Two distinct identity hom sets may reuse the same raw label. Such a
family cannot be the literal fibres of a single source-target map. -/
theorem overlapping_identity_labels_obstruction :
    ¬ ∃ s t : Unit → Bool, ∀ x y, {a | s a = x ∧ t a = y} = if x = y then univ else ∅ := by
  rintro ⟨s, t, h⟩
  have h₀ : s () = false := by
    have hm : () ∈ {a | s a = false ∧ t a = false} := by rw [h]; simp
    exact hm.1
  have h₁ : s () = true := by
    have hm : () ∈ {a | s a = true ∧ t a = true} := by rw [h]; simp
    exact hm.1
  exact Bool.false_ne_true (h₀.symm.trans h₁)

/-- Natural transformations on the single arrow set. -/
@[ext]
structure Transformation {C D : EffectiveCategory.{u}} (F G : Hom C D) where
  app : C.Obj → D.Arrow
  source_app : ∀ x, D.source (app x) = F.obj x
  target_app : ∀ x, D.target (app x) = G.obj x
  naturality : ∀ a, D.compose (F.arrow a) (app (C.target a))
      ((F.target_arrow a).trans (source_app _).symm) =
    D.compose (app (C.source a)) (G.arrow a) ((target_app _).trans (G.source_arrow a).symm)

def Transformation.toNatTrans {C D : EffectiveCategory.{u}} {F G : Hom C D}
    (T : Transformation F G) : F.toFunctor ⟶ G.toFunctor where
  app x := ⟨T.app x, T.source_app x, T.target_app x⟩
  naturality := by
    rintro x y ⟨a, hx, hy⟩
    subst x
    subst y
    exact Subtype.ext (T.naturality a)

def Transformation.ofNatTrans {C D : EffectiveCategory.{u}} {F G : Hom C D}
    (T : F.toFunctor ⟶ G.toFunctor) : Transformation F G where
  app x := (T.app x).val
  source_app x := (T.app x).property.1
  target_app x := (T.app x).property.2
  naturality a := congrArg Subtype.val (T.naturality (show C.source a ⟶ C.target a from ⟨a, rfl, rfl⟩))

def transformationEquiv {C D : EffectiveCategory.{u}} (F G : Hom C D) :
    Transformation F G ≃ (F.toFunctor ⟶ G.toFunctor) where
  toFun := Transformation.toNatTrans
  invFun := Transformation.ofNatTrans
  left_inv T := by ext; rfl
  right_inv T := by ext; rfl

namespace Transformation

set_option backward.isDefEq.respectTransparency false

open CategoryTheory.Functor

variable {A B C D : EffectiveCategory.{u}}

@[simp] theorem toNatTrans_ofNatTrans {F G : Hom A B} (T : F.toFunctor ⟶ G.toFunctor) :
    (ofNatTrans T).toNatTrans = T :=
  (transformationEquiv F G).right_inv T

theorem toNatTrans_injective {F G : Hom A B} :
    Injective (toNatTrans (F := F) (G := G)) :=
  (transformationEquiv F G).injective

def identity (F : Hom A B) : Transformation F F := ofNatTrans (𝟙 F.toFunctor)

def vertical {F G H : Hom A B} (T : Transformation F G) (S : Transformation G H) :
    Transformation F H := ofNatTrans (T.toNatTrans ≫ S.toNatTrans)

@[simp] theorem identity_toNatTrans (F : Hom A B) :
    (identity F).toNatTrans = 𝟙 F.toFunctor :=
  toNatTrans_ofNatTrans _

@[simp] theorem vertical_toNatTrans {F G H : Hom A B} (T : Transformation F G)
    (S : Transformation G H) : (vertical T S).toNatTrans = T.toNatTrans ≫ S.toNatTrans :=
  toNatTrans_ofNatTrans _

@[simp] theorem vertical_id_left {F G : Hom A B} (T : Transformation F G) :
    vertical (identity F) T = T := toNatTrans_injective (by simp)

@[simp] theorem vertical_id_right {F G : Hom A B} (T : Transformation F G) :
    vertical T (identity G) = T := toNatTrans_injective (by simp)

/-- The hom category uses the source's transformations on the total arrow set. -/
instance homCategory : SmallCategory (Hom A B) where
  Hom := Transformation
  id := identity
  comp := vertical
  id_comp := vertical_id_left
  comp_id := vertical_id_right
  assoc _ _ _ := toNatTrans_injective (by simp)

@[simp] theorem id_app (F : Hom A B) (x : A.Obj) :
    (identity F).app x = B.unit (F.obj x) := rfl

theorem vertical_app {F G H : Hom A B} (T : Transformation F G)
    (S : Transformation G H) (x : A.Obj) :
    (vertical T S).app x =
      B.compose (T.app x) (S.app x) ((T.target_app x).trans (S.source_app x).symm) := rfl

/-- Horizontal composition in the total arrow set, with categorical order. -/
def horizontal {F F' : Hom A B} {G G' : Hom B C} (T : Transformation F F')
    (S : Transformation G G') : Transformation (F ≫ G : A ⟶ C) (F' ≫ G' : A ⟶ C) :=
  ofNatTrans (T.toNatTrans ◫ S.toNatTrans)

@[simp] theorem horizontal_toNatTrans {F F' : Hom A B} {G G' : Hom B C}
    (T : Transformation F F') (S : Transformation G G') :
    (horizontal T S).toNatTrans = T.toNatTrans ◫ S.toNatTrans :=
  toNatTrans_ofNatTrans _

theorem horizontal_app {F F' : Hom A B} {G G' : Hom B C}
    (T : Transformation F F') (S : Transformation G G') (x : A.Obj) :
    (horizontal T S).app x =
      C.compose (S.app (F.obj x)) (G'.arrow (T.app x))
        ((S.target_app (F.obj x)).trans ((G'.source_arrow (T.app x)).trans
          (congrArg G'.obj (T.source_app x))).symm) := rfl

theorem horizontal_identity (F : Hom A B) (G : Hom B C) :
    horizontal (identity F) (identity G) = identity (F ≫ G : A ⟶ C) := by
  apply toNatTrans_injective
  ext x
  simp
  rfl

theorem horizontal_vertical {F F' F'' : Hom A B} {G G' G'' : Hom B C}
    (T : Transformation F F') (T' : Transformation F' F'') (S : Transformation G G')
    (S' : Transformation G' G'') :
    horizontal (vertical T T') (vertical S S') = vertical (horizontal T S) (horizontal T' S') := by
  apply toNatTrans_injective
  simp only [horizontal_toNatTrans, vertical_toNatTrans]
  ext x
  simp only [NatTrans.hcomp_app, NatTrans.comp_app, Functor.map_comp, Category.assoc]
  rw [S'.toNatTrans.naturality_assoc]

theorem horizontal_pre_whisker_comp {F : Hom A B} {G G' G'' : Hom B C}
    (S : Transformation G G') (S' : Transformation G' G'') :
    vertical (horizontal (identity F) S) (horizontal (identity F) S') =
      horizontal (identity F) (vertical S S') := by
  simpa using (horizontal_vertical (identity F) (identity F) S S').symm

theorem horizontal_post_whisker_comp {F F' F'' : Hom A B} {G : Hom B C}
    (T : Transformation F F') (T' : Transformation F' F'') :
    vertical (horizontal T (identity G)) (horizontal T' (identity G)) =
      horizontal (vertical T T') (identity G) := by
  simpa using (horizontal_vertical T T' (identity G) (identity G)).symm

theorem horizontal_two_whiskerings {F F' : Hom A B} {G G' : Hom B C}
    (T : Transformation F F') (S : Transformation G G') :
    vertical (horizontal (identity F) S) (horizontal T (identity G')) =
      vertical (horizontal T (identity G)) (horizontal (identity F') S) := by
  calc
    _ = horizontal (vertical (identity F) T) (vertical S (identity G')) :=
      (horizontal_vertical _ _ _ _).symm
    _ = horizontal (vertical T (identity F')) (vertical (identity G) S) := by simp
    _ = _ := horizontal_vertical _ _ _ _

/-- The units agree on every raw arrow component. The whiskering indices
are the domain identity on the left and the codomain identity on the right. -/
theorem horizontal_units_app {F F' : Hom A B} (T : Transformation F F') (x : A.Obj) :
    (horizontal (identity (𝟙 A : A ⟶ A)) T).app x = T.app x ∧
    (horizontal T (identity (𝟙 B : B ⟶ B))).app x = T.app x := by
  constructor
  · simp only [horizontal_app, id_app, Hom.map_unit]
    change B.compose (T.app x) (B.unit (F'.obj x)) _ = T.app x
    exact (compose_congr B rfl (congrArg B.unit (T.target_app x)).symm _ _).trans (B.compose_unit _)
  · simp only [horizontal_app, id_app]
    change B.compose (B.unit (F.obj x)) (T.app x) _ = T.app x
    exact (compose_congr B (congrArg B.unit (T.source_app x)).symm rfl _ _).trans (B.unit_compose _)

theorem horizontal_assoc_app {F F' : Hom A B} {G G' : Hom B C} {H H' : Hom C D}
    (T : Transformation F F') (S : Transformation G G') (R : Transformation H H')
    (x : A.Obj) :
    (horizontal (horizontal T S) R).app x = (horizontal T (horizontal S R)).app x := by
  change (((T.toNatTrans ◫ S.toNatTrans) ◫ R.toNatTrans).app x).val =
    ((T.toNatTrans ◫ (S.toNatTrans ◫ R.toNatTrans)).app x).val
  simp only [NatTrans.hcomp_app, Functor.comp_map, Functor.map_comp, Category.assoc]
  rfl

/-- The mixed whiskering associativity law (E.5.1.34) on the total arrow set. -/
theorem horizontal_mixed_whiskering_app (F : Hom A B) {G G' : Hom B C}
    (S : Transformation G G') (H : Hom C D) (x : A.Obj) :
    (horizontal (horizontal (identity F) S) (identity H)).app x =
      (horizontal (identity F) (horizontal S (identity H))).app x :=
  horizontal_assoc_app _ _ _ _

/-- Lemma E.5.1.19. Composition is a functor on effective hom categories,
with unit and associativity laws as in `horizontal_units_app` and `horizontal_assoc_app`. -/
def compositionBifunctor : (Hom A B × Hom B C) ⥤ Hom A C where
  obj p := (p.1 ≫ p.2 : A ⟶ C)
  map {p q} T := by
    change Transformation (p.1 ≫ p.2 : A ⟶ C) (q.1 ≫ q.2 : A ⟶ C)
    exact horizontal T.1 T.2
  map_id p := horizontal_identity p.1 p.2
  map_comp p q := horizontal_vertical p.1 q.1 p.2 q.2

theorem compositionBifunctor_object_laws (F : Hom A B) (G : Hom B C) (H : Hom C D) :
    (compositionBifunctor (A := A) (B := A) (C := B)).obj (𝟙 A, F) = F ∧
    (compositionBifunctor (A := A) (B := B) (C := B)).obj (F, 𝟙 B) = F ∧
    (compositionBifunctor (A := A) (B := C) (C := D)).obj
        ((compositionBifunctor (A := A) (B := B) (C := C)).obj (F, G), H) =
      (compositionBifunctor (A := A) (B := B) (C := D)).obj
        (F, (compositionBifunctor (A := B) (B := C) (C := D)).obj (G, H)) :=
  ⟨rfl, rfl, rfl⟩

end Transformation

/-- The strict bicategory on effective categories, using the dependent
hom types to represent the single-arrow-set functors and transformations. -/
abbrev EffectiveCategory₂ := Bicategory.InducedBicategory Cat.{u, u} toCat.obj

def comparison₂ : StrictPseudofunctor EffectiveCategory₂.{u} Cat.{u, u} :=
  Bicategory.InducedBicategory.forget

def comparison₂HomInverse (X Y : EffectiveCategory₂.{u}) :
    (comparison₂.obj X ⟶ comparison₂.obj Y) ⥤ (X ⟶ Y) where
  obj := fun f => Bicategory.InducedBicategory.mkHom f
  map := fun T => Bicategory.InducedBicategory.mkHom₂ T

/-- Corrected Lemma E.5.4.5. The comparison is a strict pseudofunctor
with isomorphisms on hom categories, and every target object is isomorphic
to one in its image. -/
theorem comparison₂_locally_iso_and_essSurj :
    (∀ X Y : EffectiveCategory₂.{u},
      comparison₂.mapFunctor X Y ⋙ comparison₂HomInverse X Y = 𝟭 (X ⟶ Y) ∧
      comparison₂HomInverse X Y ⋙ comparison₂.mapFunctor X Y =
        𝟭 (comparison₂.obj X ⟶ comparison₂.obj Y)) ∧
    (∀ C : Cat.{u, u}, ∃ X : EffectiveCategory₂.{u}, Nonempty (comparison₂.obj X ≅ C)) :=
  ⟨fun _ _ => ⟨rfl, rfl⟩, fun C => ⟨ofCat C, ⟨ofCatIso C⟩⟩⟩

end EffectiveCategory

end Masullo
