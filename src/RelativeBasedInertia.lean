import BasedInertia
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.FiberedCategory.Fiber

open CategoryTheory CategoryTheory.Functor CategoryTheory.IsHomLift
open scoped CategoryTheory.BasedFunctor

namespace Masullo.RelativeBasedInertia

open VerticalIsoComma

universe u
variable {D : Type u} [SmallCategory D]
  {Y X : BasedCategory.{u,u} D} (x : Y ⥤ᵇ X)

/-- The objects of relative inertia are a point of the domain and a
vertical automorphism of its image. -/
structure Obj where
  point : Y.obj
  loop : x.obj point ≅ x.obj point
  vertical : X.p.IsHomLift (𝟙 (Y.p.obj point)) loop.hom

variable {x}

@[ext]
structure Arrow (a b : Obj x) where
  hom : a.point ⟶ b.point
  square : x.map hom ≫ b.loop.hom = a.loop.hom ≫ x.map hom

instance : SmallCategory (Obj x) where
  Hom := Arrow
  id a := ⟨𝟙 a.point, by simp⟩
  comp f g := ⟨f.hom ≫ g.hom, by
    simp only [Functor.map_comp, Category.assoc]
    rw [g.square, ← Category.assoc, f.square, Category.assoc]⟩
  id_comp f := Arrow.ext (Category.id_comp _)
  comp_id f := Arrow.ext (Category.comp_id _)
  assoc f g h := Arrow.ext (Category.assoc _ _ _)

variable (x)

def forget : Obj x ⥤ Y.obj where
  obj a := a.point
  map f := f.hom

abbrev relative := BasedCategory.ofFunctor (forget x ⋙ Y.p)

def toDomain : relative x ⥤ᵇ Y where
  toFunctor := forget x
  w := rfl

abbrev pullback := VerticalIsoComma.based x (BasedInertia.forgetBased X)
private abbrev PullbackObj := VerticalIsoComma.Obj x (BasedInertia.forgetBased X)

set_option backward.isDefEq.respectTransparency false in
private def comparisonObj (a : Obj x) : PullbackObj x where
  left := a.point
  right := ⟨x.obj a.point, a.loop, x.w_obj a.point ▸ a.vertical⟩
  iso := Iso.refl _
  vertical := IsHomLift.id (x.w_obj a.point)

set_option backward.isDefEq.respectTransparency false in
/-- The relative automorphism maps to the corresponding absolute
automorphism, with identity comparison at the marked point. -/
def comparison : relative x ⥤ᵇ pullback x where
  toFunctor := {
    obj := comparisonObj x
    map {a b} f := {
      left := f.hom
      right := ⟨x.map f.hom, f.square⟩
      over := by
        let q : (comparisonObj x a).right ⟶ (comparisonObj x b).right :=
          ⟨x.map f.hom, f.square⟩
        haveI : X.p.IsHomLift (Y.p.map f.hom) ((BasedInertia.forgetBased X).map q) :=
          x.preserves_isHomLift (Y.p.map f.hom) f.hom
        exact (BasedInertia.forgetBased X).isHomLift_map (Y.p.map f.hom) q
      square := (Category.comp_id _).trans (Category.id_comp _).symm }
    map_id a := VerticalIsoComma.Arrow.ext rfl (BasedInertia.Arrow.ext (x.map_id _))
    map_comp f g := VerticalIsoComma.Arrow.ext rfl (BasedInertia.Arrow.ext (x.map_comp _ _)) }
  w := rfl

set_option backward.isDefEq.respectTransparency false in
private def inverseObj (a : PullbackObj x) : Obj x where
  point := a.left
  loop := a.iso ≪≫ a.right.loop ≪≫ a.iso.symm
  vertical := by
    haveI := a.vertical
    haveI : X.p.IsHomLift (𝟙 (Y.p.obj a.left)) a.right.loop.hom := by
      have he : X.p.obj a.right.point = Y.p.obj a.left :=
        codomain_eq X.p (𝟙 (Y.p.obj a.left)) a.iso.hom
      exact he ▸ a.right.vertical
    haveI := lift_id_inv X.p (Y.p.obj a.left) a.iso
    change X.p.IsHomLift (𝟙 (Y.p.obj a.left))
      (a.iso.hom ≫ a.right.loop.hom ≫ a.iso.inv)
    haveI : X.p.IsHomLift (𝟙 (Y.p.obj a.left)) (a.right.loop.hom ≫ a.iso.inv) :=
      comp_lift_id_right' X.p (𝟙 (Y.p.obj a.left)) a.right.loop.hom
        (Y.p.obj a.left) a.iso.inv
    exact comp_lift_id_right' X.p (𝟙 (Y.p.obj a.left)) a.iso.hom
      (Y.p.obj a.left) (a.right.loop.hom ≫ a.iso.inv)

set_option backward.isDefEq.respectTransparency false in
def inverseComparison : pullback x ⥤ᵇ relative x where
  toFunctor := {
    obj := inverseObj x
    map {a b} f := ⟨f.left, by
      have h₁ : x.map f.left ≫ b.iso.hom = a.iso.hom ≫ f.right.hom := f.square
      have h₂ := f.right.square
      change x.map f.left ≫ (b.iso.hom ≫ b.right.loop.hom ≫ b.iso.inv) =
        (a.iso.hom ≫ a.right.loop.hom ≫ a.iso.inv) ≫ x.map f.left
      apply (cancel_mono b.iso.hom).mp
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      rw [h₁, Iso.inv_hom_id_assoc, ← Category.assoc (x.map f.left), h₁,
        Category.assoc, h₂]⟩
    map_id a := Arrow.ext rfl
    map_comp f g := Arrow.ext rfl }
  w := rfl

set_option backward.isDefEq.respectTransparency false in
private def unitComponent (a : Obj x) : a ≅ inverseObj x (comparisonObj x a) where
  hom := ⟨𝟙 a.point, by
    change x.map (𝟙 a.point) ≫ (𝟙 _ ≫ a.loop.hom ≫ 𝟙 _) =
      a.loop.hom ≫ x.map (𝟙 a.point)
    simp only [x.map_id, Category.comp_id, Category.id_comp]⟩
  inv := ⟨𝟙 a.point, by
    change x.map (𝟙 a.point) ≫ a.loop.hom =
      (𝟙 _ ≫ a.loop.hom ≫ 𝟙 _) ≫ x.map (𝟙 a.point)
    simp only [x.map_id, Category.comp_id, Category.id_comp]⟩
  hom_inv_id := Arrow.ext (Category.id_comp _)
  inv_hom_id := Arrow.ext (Category.id_comp _)

set_option backward.isDefEq.respectTransparency false in
def unitIso : BasedFunctor.id (relative x) ≅ comparison x ⋙ inverseComparison x :=
  BasedNatIso.mkNatIso
    (NatIso.ofComponents (unitComponent x) (fun m => by
      apply Arrow.ext
      exact (Category.comp_id _).trans (Category.id_comp _).symm))
    (fun a => by
      apply IsHomLift.of_fac' _ _ _ rfl rfl
      simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
      exact Y.p.map_id a.point)

set_option backward.isDefEq.respectTransparency false in
private def conjugationIso (a : PullbackObj x) :
    (comparisonObj x (inverseObj x a)).right ≅ a.right where
  hom := ⟨a.iso.hom, by
    change a.iso.hom ≫ a.right.loop.hom =
      (a.iso.hom ≫ a.right.loop.hom ≫ a.iso.inv) ≫ a.iso.hom
    simp [Category.assoc]⟩
  inv := ⟨a.iso.inv, by
    change a.iso.inv ≫ (a.iso.hom ≫ a.right.loop.hom ≫ a.iso.inv) =
      a.right.loop.hom ≫ a.iso.inv
    simp⟩
  hom_inv_id := BasedInertia.Arrow.ext a.iso.hom_inv_id
  inv_hom_id := BasedInertia.Arrow.ext a.iso.inv_hom_id

set_option backward.isDefEq.respectTransparency false in
private def counitComponent (a : PullbackObj x) :
    comparisonObj x (inverseObj x a) ≅ a :=
  objectIso (Iso.refl a.left) (conjugationIso x a) (IsHomLift.id rfl)
    (by
      haveI : X.p.IsHomLift (𝟙 (Y.p.obj a.left))
          ((BasedInertia.forgetBased X).map (conjugationIso x a).hom) := a.vertical
      exact (BasedInertia.forgetBased X).isHomLift_map (𝟙 (Y.p.obj a.left))
        (conjugationIso x a).hom) (by
      change x.map (𝟙 a.left) ≫ a.iso.hom = 𝟙 _ ≫ a.iso.hom
      rw [x.map_id])

set_option backward.isDefEq.respectTransparency false in
/-- Conjugation gives the inverse comparison, with vertical unit and
counit. This verifies the relative inertia square as a two-pullback. -/
def counitIso : inverseComparison x ⋙ comparison x ≅ BasedFunctor.id (pullback x) :=
  BasedNatIso.mkNatIso
    (NatIso.ofComponents (counitComponent x) (fun m => by
      apply VerticalIsoComma.Arrow.ext
      · exact (Category.comp_id _).trans (Category.id_comp _).symm
      · apply BasedInertia.Arrow.ext
        exact m.square))
    (fun a => by
      apply IsHomLift.of_fac' _ _ _ rfl rfl
      simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
      exact Y.p.map_id a.left)


/-- The map to absolute inertia sends a relative automorphism to the
same automorphism of the image object. -/
abbrev toAbsolute : relative x ⥤ᵇ BasedInertia.based X :=
  comparison x ⋙ snd x (BasedInertia.forgetBased X)

theorem comparison_fst : comparison x ⋙ fst x (BasedInertia.forgetBased X) = toDomain x := rfl

theorem inertia_square : toDomain x ⋙ x = toAbsolute x ⋙ BasedInertia.forgetBased X := by
  cases x
  rfl

/-- The category over the base associated to the presheaf represented by T. -/
abbrev representable (T : D) : BasedCategory.{u,u} D :=
  BasedCategory.ofFunctor (Over.forget T)

/-- Sections of relative inertia over U are arrows to T equipped with
a vertical automorphism of the marked object over U. -/
abbrev markedSections {T : D} (x : representable T ⥤ᵇ X) (U : D) :=
  Σ f : U ⟶ T, {i : x.obj (Over.mk f) ≅ x.obj (Over.mk f) // X.p.IsHomLift (𝟙 U) i.hom}

set_option backward.isDefEq.respectTransparency false in
def markedSectionsEquiv {T : D} (x : representable T ⥤ᵇ X) (U : D) :
    markedSections x U ≃ Fiber (relative x).p U where
  toFun f := ⟨⟨Over.mk f.1, f.2.val, f.2.property⟩, rfl⟩
  invFun a := by
    rcases a with ⟨⟨A, i, hi⟩, hA⟩
    change A.left = U at hA
    subst U
    exact ⟨A.hom, ⟨i, hi⟩⟩
  left_inv := by
    rintro ⟨f, i, hi⟩
    rfl
  right_inv := by
    rintro ⟨⟨A, i, hi⟩, hA⟩
    change A.left = U at hA
    subst U
    rfl

/-- For Cartesian x between fibered categories, the two-pullback that
computes relative inertia is fibered over the original base. -/
theorem pullback_fibered [Y.p.IsFibered] [X.p.IsFibered] (hx : PreservesCartesian x) :
    (pullback x).p.IsFibered := by
  haveI : (BasedInertia.based X).p.IsFibered := BasedInertia.isFibered X
  exact VerticalIsoComma.isFibered hx (BasedInertia.forget_preserves X)

end Masullo.RelativeBasedInertia
