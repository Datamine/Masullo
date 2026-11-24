import Mathlib.CategoryTheory.Bicategory.Basic

open CategoryTheory
open scoped Bicategory

namespace Masullo

universe w v u

namespace TwoCommutativeDiagram

variable {𝒞 : Type u} [Bicategory.{w, v} 𝒞]
variable {A B C : 𝒞}

/-- A two-commutative cone on a cospan in a bicategory. -/
structure Diagram (f : B ⟶ A) (g : C ⟶ A) where
  vertex : 𝒞
  left : vertex ⟶ B
  right : vertex ⟶ C
  square : left ≫ f ≅ right ≫ g

variable {f : B ⟶ A} {g : C ⟶ A}

/-- The triangular comparison isomorphisms are part of a map of cones. -/
structure ConeMap (X Y : Diagram f g) where
  vertexMap : X.vertex ⟶ Y.vertex
  leftIso : X.left ≅ vertexMap ≫ Y.left
  rightIso : X.right ≅ vertexMap ≫ Y.right
  comm : X.square.hom ≫ rightIso.hom ▷ g ≫ (α_ vertexMap Y.right g).hom =
    leftIso.hom ▷ f ≫ (α_ vertexMap Y.left f).hom ≫ vertexMap ◁ Y.square.hom

variable {X Y : Diagram f g}

/-- A cell between cone maps satisfies the two triangular equations of
Construction E.5.5.2. -/
@[ext]
structure Cell (a b : ConeMap X Y) where
  cell : a.vertexMap ⟶ b.vertexMap
  left_comm : a.leftIso.hom ≫ cell ▷ Y.left = b.leftIso.hom
  right_comm : a.rightIso.hom ≫ cell ▷ Y.right = b.rightIso.hom

/-- Lemma E.5.5.3. The hom between two diagrams is a category with inherited
vertical composition, and its objects and arrows lie in the hom universes. -/
instance coneMapCategory : Category.{w} (ConeMap X Y) where
  Hom := Cell
  id a := ⟨𝟙 a.vertexMap, by simp, by simp⟩
  comp a b :=
    ⟨a.cell ≫ b.cell,
      by rw [Bicategory.comp_whiskerRight, ← Category.assoc, a.left_comm, b.left_comm],
      by rw [Bicategory.comp_whiskerRight, ← Category.assoc, a.right_comm, b.right_comm]⟩
  id_comp a := Cell.ext (Category.id_comp a.cell)
  comp_id a := Cell.ext (Category.comp_id a.cell)
  assoc a b c := Cell.ext (Category.assoc a.cell b.cell c.cell)

@[simp] theorem cell_id (a : ConeMap X Y) :
    (𝟙 a : a ⟶ a).cell = 𝟙 a.vertexMap := rfl

@[simp] theorem cell_comp {a b c : ConeMap X Y} (α : a ⟶ b) (β : b ⟶ c) :
    (α ≫ β : a ⟶ c).cell = α.cell ≫ β.cell := rfl

end TwoCommutativeDiagram

end Masullo
