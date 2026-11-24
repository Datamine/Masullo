import DiagramCategories
import Mathlib.Tactic.CategoryTheory.Bicategory.Basic
import Mathlib.CategoryTheory.Bicategory.Strict.Basic

open CategoryTheory CategoryTheory.Bicategory
open scoped Bicategory

namespace Masullo.TwoCommutativeDiagram

universe w v u

variable {𝒞 : Type u} [Bicategory.{w, v} 𝒞]
variable {A B C : 𝒞} {f : B ⟶ A} {g : C ⟶ A}
variable {X Y Z W : Diagram f g}

@[reassoc] private theorem unitor_paste {P Q R : 𝒞} (k : P ⟶ Q) (l : Q ⟶ R) :
    (λ_ k).inv ▷ l ≫ (α_ (𝟙 P) k l).hom = (λ_ (k ≫ l)).inv := by
  bicategory

def coneId (X : Diagram f g) : ConeMap X X where
  vertexMap := 𝟙 X.vertex
  leftIso := (λ_ X.left).symm
  rightIso := (λ_ X.right).symm
  comm := by
    simp only [Iso.symm_hom]
    rw [unitor_paste, unitor_paste_assoc]
    exact leftUnitor_inv_naturality X.square.hom

def coneComp (a : ConeMap X Y) (b : ConeMap Y Z) : ConeMap X Z where
  vertexMap := a.vertexMap ≫ b.vertexMap
  leftIso := a.leftIso ≪≫ whiskerLeftIso a.vertexMap b.leftIso ≪≫ (α_ a.vertexMap b.vertexMap Z.left).symm
  rightIso := a.rightIso ≪≫ whiskerLeftIso a.vertexMap b.rightIso ≪≫ (α_ a.vertexMap b.vertexMap Z.right).symm
  comm := by
    simp only [Iso.trans_hom, Iso.symm_hom, whiskerLeftIso_hom]
    calc
      _ = (X.square.hom ≫ a.rightIso.hom ▷ g ≫ (α_ a.vertexMap Y.right g).hom) ≫
          a.vertexMap ◁ (b.rightIso.hom ▷ g ≫ (α_ b.vertexMap Z.right g).hom) ≫
            (α_ a.vertexMap b.vertexMap (Z.right ≫ g)).inv := by bicategory
      _ = (a.leftIso.hom ▷ f ≫ (α_ a.vertexMap Y.left f).hom) ≫
          a.vertexMap ◁ (Y.square.hom ≫ b.rightIso.hom ▷ g ≫ (α_ b.vertexMap Z.right g).hom) ≫
            (α_ a.vertexMap b.vertexMap (Z.right ≫ g)).inv := by
        rw [a.comm]
        bicategory
      _ = _ := by
        rw [b.comm]
        bicategory

instance : CategoryStruct (Diagram f g) where
  Hom := ConeMap
  id := coneId
  comp := coneComp

instance diagramHomCategory (X Y : Diagram f g) : Category.{w} (X ⟶ Y) :=
  coneMapCategory

@[simp] theorem vertexMap_id (X : Diagram f g) :
    (𝟙 X : ConeMap X X).vertexMap = 𝟙 X.vertex := rfl

@[simp] theorem vertexMap_comp (a : X ⟶ Y) (b : Y ⟶ Z) :
    (a ≫ b : X ⟶ Z).vertexMap = a.vertexMap ≫ b.vertexMap := rfl

def coneWhiskerLeft (a : ConeMap X Y) {b b' : ConeMap Y Z} (η : Cell b b') :
    Cell (coneComp a b) (coneComp a b') where
  cell := a.vertexMap ◁ η.cell
  left_comm := by
    simp only [coneComp, Iso.trans_hom, Iso.symm_hom, whiskerLeftIso_hom]
    calc
      _ = a.leftIso.hom ≫ a.vertexMap ◁ (b.leftIso.hom ≫ η.cell ▷ Z.left) ≫
          (α_ a.vertexMap b'.vertexMap Z.left).inv := by bicategory
      _ = _ := by rw [η.left_comm]
  right_comm := by
    simp only [coneComp, Iso.trans_hom, Iso.symm_hom, whiskerLeftIso_hom]
    calc
      _ = a.rightIso.hom ≫ a.vertexMap ◁ (b.rightIso.hom ≫ η.cell ▷ Z.right) ≫
          (α_ a.vertexMap b'.vertexMap Z.right).inv := by bicategory
      _ = _ := by rw [η.right_comm]

def coneWhiskerRight {a a' : ConeMap X Y} (η : Cell a a') (b : ConeMap Y Z) :
    Cell (coneComp a b) (coneComp a' b) where
  cell := η.cell ▷ b.vertexMap
  left_comm := by
    simp only [coneComp, Iso.trans_hom, Iso.symm_hom, whiskerLeftIso_hom]
    calc
      _ = a.leftIso.hom ≫ (a.vertexMap ◁ b.leftIso.hom ≫ η.cell ▷ (b.vertexMap ≫ Z.left)) ≫
          (α_ a'.vertexMap b.vertexMap Z.left).inv := by bicategory
      _ = (a.leftIso.hom ≫ η.cell ▷ Y.left) ≫ a'.vertexMap ◁ b.leftIso.hom ≫
          (α_ a'.vertexMap b.vertexMap Z.left).inv := by
        rw [whisker_exchange]
        bicategory
      _ = _ := by rw [η.left_comm]
  right_comm := by
    simp only [coneComp, Iso.trans_hom, Iso.symm_hom, whiskerLeftIso_hom]
    calc
      _ = a.rightIso.hom ≫ (a.vertexMap ◁ b.rightIso.hom ≫ η.cell ▷ (b.vertexMap ≫ Z.right)) ≫
          (α_ a'.vertexMap b.vertexMap Z.right).inv := by bicategory
      _ = (a.rightIso.hom ≫ η.cell ▷ Y.right) ≫ a'.vertexMap ◁ b.rightIso.hom ≫
          (α_ a'.vertexMap b.vertexMap Z.right).inv := by
        rw [whisker_exchange]
        bicategory
      _ = _ := by rw [η.right_comm]

def coneAssociator (a : ConeMap X Y) (b : ConeMap Y Z) (c : ConeMap Z W) :
    coneComp (coneComp a b) c ≅ coneComp a (coneComp b c) where
  hom :=
    { cell := (α_ a.vertexMap b.vertexMap c.vertexMap).hom
      left_comm := by simp only [coneComp, Iso.trans_hom, Iso.symm_hom, whiskerLeftIso_hom]; bicategory
      right_comm := by simp only [coneComp, Iso.trans_hom, Iso.symm_hom, whiskerLeftIso_hom]; bicategory }
  inv :=
    { cell := (α_ a.vertexMap b.vertexMap c.vertexMap).inv
      left_comm := by simp only [coneComp, Iso.trans_hom, Iso.symm_hom, whiskerLeftIso_hom]; bicategory
      right_comm := by simp only [coneComp, Iso.trans_hom, Iso.symm_hom, whiskerLeftIso_hom]; bicategory }
  hom_inv_id := Cell.ext (Iso.hom_inv_id _)
  inv_hom_id := Cell.ext (Iso.inv_hom_id _)

def coneLeftUnitor (a : ConeMap X Y) : coneComp (coneId X) a ≅ a where
  hom :=
    { cell := (λ_ a.vertexMap).hom
      left_comm := by simp only [coneComp, coneId, Iso.trans_hom, Iso.symm_hom, whiskerLeftIso_hom]; bicategory
      right_comm := by simp only [coneComp, coneId, Iso.trans_hom, Iso.symm_hom, whiskerLeftIso_hom]; bicategory }
  inv :=
    { cell := (λ_ a.vertexMap).inv
      left_comm := by simp only [coneComp, coneId, Iso.trans_hom, Iso.symm_hom, whiskerLeftIso_hom]; bicategory
      right_comm := by simp only [coneComp, coneId, Iso.trans_hom, Iso.symm_hom, whiskerLeftIso_hom]; bicategory }
  hom_inv_id := Cell.ext (Iso.hom_inv_id _)
  inv_hom_id := Cell.ext (Iso.inv_hom_id _)

def coneRightUnitor (a : ConeMap X Y) : coneComp a (coneId Y) ≅ a where
  hom :=
    { cell := (ρ_ a.vertexMap).hom
      left_comm := by simp only [coneComp, coneId, Iso.trans_hom, Iso.symm_hom, whiskerLeftIso_hom]; bicategory
      right_comm := by simp only [coneComp, coneId, Iso.trans_hom, Iso.symm_hom, whiskerLeftIso_hom]; bicategory }
  inv :=
    { cell := (ρ_ a.vertexMap).inv
      left_comm := by simp only [coneComp, coneId, Iso.trans_hom, Iso.symm_hom, whiskerLeftIso_hom]; bicategory
      right_comm := by simp only [coneComp, coneId, Iso.trans_hom, Iso.symm_hom, whiskerLeftIso_hom]; bicategory }
  hom_inv_id := Cell.ext (Iso.hom_inv_id _)
  inv_hom_id := Cell.ext (Iso.inv_hom_id _)

set_option backward.isDefEq.respectTransparency false in
/-- The hom categories of two-commutative diagrams assemble into a
bicategory, with the horizontal composites given by pasting. -/
instance diagramBicategory : Bicategory.{w, max w v} (Diagram f g) where
  toCategoryStruct := inferInstance
  homCategory := diagramHomCategory
  whiskerLeft := coneWhiskerLeft
  whiskerRight := coneWhiskerRight
  associator := coneAssociator
  leftUnitor := coneLeftUnitor
  rightUnitor := coneRightUnitor
  whiskerLeft_id a b := Cell.ext (Bicategory.whiskerLeft_id a.vertexMap b.vertexMap)
  whiskerLeft_comp a := by
    intro b c d α β
    exact Cell.ext (Bicategory.whiskerLeft_comp a.vertexMap α.cell β.cell)
  id_whiskerLeft α := Cell.ext (Bicategory.id_whiskerLeft α.cell)
  comp_whiskerLeft a b := by
    intro c d α
    exact Cell.ext (Bicategory.comp_whiskerLeft a.vertexMap b.vertexMap α.cell)
  id_whiskerRight a b := Cell.ext (Bicategory.id_whiskerRight a.vertexMap b.vertexMap)
  comp_whiskerRight α β c := Cell.ext (Bicategory.comp_whiskerRight α.cell β.cell c.vertexMap)
  whiskerRight_id α := Cell.ext (Bicategory.whiskerRight_id α.cell)
  whiskerRight_comp α b c := Cell.ext (Bicategory.whiskerRight_comp α.cell b.vertexMap c.vertexMap)
  whisker_assoc a := by
    intro b c α d
    exact Cell.ext (Bicategory.whisker_assoc a.vertexMap α.cell d.vertexMap)
  whisker_exchange α β := Cell.ext (Bicategory.whisker_exchange α.cell β.cell)
  pentagon a b c d := Cell.ext (Bicategory.pentagon a.vertexMap b.vertexMap c.vertexMap d.vertexMap)
  triangle a b := Cell.ext (Bicategory.triangle a.vertexMap b.vertexMap)

private theorem coneMap_eq_of_eqToHom {a b : ConeMap X Y} (η : Cell a b)
    (hv : a.vertexMap = b.vertexMap) (hη : η.cell = eqToHom hv) : a = b := by
  cases a with
  | mk av al ar ac =>
    cases b with
    | mk bv bl br bc =>
      change av = bv at hv
      subst bv
      have hl := η.left_comm
      have hr := η.right_comm
      simp only [hη, eqToHom_refl, id_whiskerRight, Category.comp_id] at hl hr
      obtain rfl : al = bl := Iso.ext hl
      obtain rfl : ar = br := Iso.ext hr
      rfl

private theorem coneEqToHom_cell {a b : ConeMap X Y} (h : a = b) :
    (eqToHom h : Cell a b).cell = eqToHom (congrArg ConeMap.vertexMap h) := by
  subst b
  rfl

section Strict

variable [Bicategory.Strict 𝒞]

private theorem strictDiagram_id_comp (a : ConeMap X Y) : coneComp (coneId X) a = a :=
  coneMap_eq_of_eqToHom (coneLeftUnitor a).hom (Bicategory.Strict.id_comp a.vertexMap) (by
    change (λ_ a.vertexMap).hom = _
    rw [Bicategory.Strict.leftUnitor_eqToIso]
    rfl)

private theorem strictDiagram_comp_id (a : ConeMap X Y) : coneComp a (coneId Y) = a :=
  coneMap_eq_of_eqToHom (coneRightUnitor a).hom (Bicategory.Strict.comp_id a.vertexMap) (by
    change (ρ_ a.vertexMap).hom = _
    rw [Bicategory.Strict.rightUnitor_eqToIso]
    rfl)

private theorem strictDiagram_assoc (a : ConeMap X Y) (b : ConeMap Y Z) (c : ConeMap Z W) :
    coneComp (coneComp a b) c = coneComp a (coneComp b c) :=
  coneMap_eq_of_eqToHom (coneAssociator a b c).hom (Bicategory.Strict.assoc _ _ _) (by
    change (α_ a.vertexMap b.vertexMap c.vertexMap).hom = _
    rw [Bicategory.Strict.associator_eqToIso]
    rfl)

set_option backward.isDefEq.respectTransparency false in
/-- E.5.5.4. The diagram bicategory is strict whenever the ambient
bicategory is strict. -/
instance diagramBicategory_strict : Bicategory.Strict (Diagram f g) where
  id_comp := strictDiagram_id_comp
  comp_id := strictDiagram_comp_id
  assoc := strictDiagram_assoc
  leftUnitor_eqToIso a := by
    apply Iso.ext
    apply Cell.ext
    change (λ_ a.vertexMap).hom = (eqToHom (strictDiagram_id_comp a) : Cell _ _).cell
    rw [Bicategory.Strict.leftUnitor_eqToIso, coneEqToHom_cell]
    rfl
  rightUnitor_eqToIso a := by
    apply Iso.ext
    apply Cell.ext
    change (ρ_ a.vertexMap).hom = (eqToHom (strictDiagram_comp_id a) : Cell _ _).cell
    rw [Bicategory.Strict.rightUnitor_eqToIso, coneEqToHom_cell]
    rfl
  associator_eqToIso a b c := by
    apply Iso.ext
    apply Cell.ext
    change (α_ a.vertexMap b.vertexMap c.vertexMap).hom =
      (eqToHom (strictDiagram_assoc a b c) : Cell _ _).cell
    rw [Bicategory.Strict.associator_eqToIso, coneEqToHom_cell]
    rfl

end Strict

end Masullo.TwoCommutativeDiagram
