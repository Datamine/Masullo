import TopologicalGroupoid
import CategoryFoundations
import Mathlib.CategoryTheory.Bicategory.LocallyGroupoid

open CategoryTheory Function Set Topology TopologicalSpace
open scoped Bicategory

namespace Masullo.TopologicalGroupoid

universe u

/-- The objects of an internal groupoid, considered as a category in sets. -/
def Underlying (G : TopologicalGroupoid.{u}) := G.objects.obj

abbrev UnderlyingArrow (G : TopologicalGroupoid.{u}) (x y : G.Underlying) :=
  {a : G.arrows.obj // G.source a = x ∧ G.target a = y}

instance (G : TopologicalGroupoid.{u}) : Groupoid G.Underlying where
  Hom := G.UnderlyingArrow
  id x := ⟨G.unit x, G.source_unit x, G.target_unit x⟩
  comp a b :=
    let p : ComposableArrows G.source G.target :=
      ⟨(a.val, b.val), a.property.2.trans b.property.1.symm⟩
    ⟨G.comp p, (G.source_comp p).trans a.property.1, (G.target_comp p).trans b.property.2⟩
  id_comp {x y} a := by
    rcases a with ⟨a, hx, hy⟩
    subst x
    exact Subtype.ext (G.unit_comp a)
  comp_id {x y} a := by
    rcases a with ⟨a, hx, hy⟩
    subst y
    exact Subtype.ext (G.comp_unit a)
  assoc a b c := Subtype.ext (G.assoc a.val b.val c.val _ _)
  inv a := ⟨G.inverse a.val, (G.source_inv a.val).trans a.property.2,
    (G.target_inv a.val).trans a.property.1⟩
  inv_comp a := by
    apply Subtype.ext
    exact (G.inv_comp a.val).trans (congrArg G.unit a.property.2)
  comp_inv a := by
    apply Subtype.ext
    exact (G.comp_inv a.val).trans (congrArg G.unit a.property.1)

def underlyingFunctor {G H : TopologicalGroupoid.{u}} (F : G ⟶ H) :
    G.Underlying ⥤ H.Underlying where
  obj x := F.objectMap x
  map a := ⟨F.arrowMap a.val, (F.mapSource _).trans (congrArg F.objectMap a.property.1),
    (F.mapTarget _).trans (congrArg F.objectMap a.property.2)⟩
  map_id x := Subtype.ext (F.mapUnit x)
  map_comp a b := Subtype.ext (F.mapComp a.val b.val _)

theorem underlyingFunctor_injective {G H : TopologicalGroupoid.{u}} :
    Injective (underlyingFunctor : (G ⟶ H) → G.Underlying ⥤ H.Underlying) := by
  intro F K h
  have hobj (x : G.Underlying) : F.objectMap x = K.objectMap x :=
    congrArg (fun f : G.Underlying ⥤ H.Underlying => f.obj x) h
  apply Hom.ext
  · exact ContinuousMap.ext hobj
  · apply ContinuousMap.ext
    intro a
    let t : G.UnderlyingArrow (G.source a) (G.target a) := ⟨a, rfl, rfl⟩
    let hmap (f : G.Underlying ⥤ H.Underlying) : H.arrows.obj := (f.map t).val
    have e := congrArg hmap h
    simpa [hmap, underlyingFunctor, t] using e

/-- A natural transformation whose component arrow varies continuously. -/
def ContinuousTransformation {G H : TopologicalGroupoid.{u}} (F K : G ⟶ H) :=
  {α : underlyingFunctor F ⟶ underlyingFunctor K // Continuous (fun x => (α.app x).val)}

private theorem continuous_components_comp {G H : TopologicalGroupoid.{u}} {F K L : G ⟶ H}
    (α : ContinuousTransformation F K) (β : ContinuousTransformation K L) :
    Continuous (fun x => ((α.val ≫ β.val).app x).val) := by
  letI : CompactlyGeneratedSpace G.Underlying := inferInstanceAs (CompactlyGeneratedSpace G.objects.obj)
  have hc : Continuous (fun x => ((α.val.app x).val, (β.val.app x).val)) :=
    α.property.prodMk β.property
  let h : G.Underlying → ComposableArrows H.source H.target :=
    fun x => ⟨((α.val.app x).val, (β.val.app x).val),
      (α.val.app x).property.2.trans (β.val.app x).property.1.symm⟩
  have hh : Continuous h := (continuous_to_Kelley hc).subtype_mk _
  exact H.comp.continuous.comp hh

private def verticalComp {G H : TopologicalGroupoid.{u}} {F K L : G ⟶ H}
    (α : ContinuousTransformation F K) (β : ContinuousTransformation K L) :
    ContinuousTransformation F L :=
  ⟨α.val ≫ β.val, continuous_components_comp α β⟩

instance homCategory (G H : TopologicalGroupoid.{u}) : Category (G ⟶ H) where
  Hom := ContinuousTransformation
  id F := ⟨𝟙 (underlyingFunctor F), H.unit.continuous.comp F.objectMap.continuous⟩
  comp := verticalComp
  id_comp α := Subtype.ext (Category.id_comp α.val)
  comp_id α := Subtype.ext (Category.comp_id α.val)
  assoc α β δ := Subtype.ext (Category.assoc α.val β.val δ.val)

private def whiskerL {A B C : TopologicalGroupoid.{u}} (F : A ⟶ B) {K L : B ⟶ C}
    (α : ContinuousTransformation K L) : ContinuousTransformation (F ≫ K) (F ≫ L) :=
  ⟨Functor.whiskerLeft (underlyingFunctor F) α.val, α.property.comp F.objectMap.continuous⟩

private def whiskerR {A B C : TopologicalGroupoid.{u}} {F K : A ⟶ B}
    (α : ContinuousTransformation F K) (L : B ⟶ C) : ContinuousTransformation (F ≫ L) (K ≫ L) :=
  ⟨Functor.whiskerRight α.val (underlyingFunctor L), L.arrowMap.continuous.comp α.property⟩

private theorem whiskerL_id {A B C : TopologicalGroupoid.{u}} (F : A ⟶ B) (K : B ⟶ C) :
    whiskerL F (𝟙 K) = 𝟙 (F ≫ K) := by
  apply Subtype.ext
  rfl

private theorem whiskerR_id {A B C : TopologicalGroupoid.{u}} (F : A ⟶ B) (K : B ⟶ C) :
    whiskerR (𝟙 F) K = 𝟙 (F ≫ K) := by
  apply Subtype.ext
  ext x
  exact (underlyingFunctor K).map_id _

private theorem continuous_whisker_exchange {A B C : TopologicalGroupoid.{u}}
    {F F' : A ⟶ B} {K K' : B ⟶ C}
    (α : ContinuousTransformation F F') (β : ContinuousTransformation K K') :
    verticalComp (whiskerL F β) (whiskerR α K') = verticalComp (whiskerR α K) (whiskerL F' β) := by
  apply Subtype.ext
  ext x
  exact (β.val.naturality (α.val.app x)).symm

set_option backward.isDefEq.respectTransparency false in
/-- The strict two-category uses continuous transformations as 2-morphisms. -/
instance topologicalBicategory : Bicategory TopologicalGroupoid.{u} where
  toCategoryStruct := (inferInstance : Category TopologicalGroupoid.{u}).toCategoryStruct
  homCategory := homCategory
  whiskerLeft := whiskerL
  whiskerRight := whiskerR
  associator _ _ _ := eqToIso rfl
  leftUnitor _ := eqToIso rfl
  rightUnitor _ := eqToIso rfl
  whiskerLeft_id := whiskerL_id
  whiskerLeft_comp F := by
    intro K L M α β
    rfl
  id_whiskerLeft α := by
    simp only [eqToIso_refl, Iso.refl_hom, Iso.refl_inv, Category.id_comp]
    apply Subtype.ext
    ext x
    exact (Category.comp_id _).symm
  comp_whiskerLeft F K := by
    intro L L' α
    simp only [eqToIso_refl, Iso.refl_hom, Iso.refl_inv, Category.id_comp]
    apply Subtype.ext
    ext x
    exact (Category.comp_id _).symm
  id_whiskerRight := whiskerR_id
  comp_whiskerRight α β F := by
    apply Subtype.ext
    ext x
    exact (underlyingFunctor F).map_comp (α.val.app x) (β.val.app x)
  whiskerRight_id α := by
    simp only [eqToIso_refl, Iso.refl_hom, Iso.refl_inv, Category.id_comp]
    apply Subtype.ext
    ext x
    exact (Category.comp_id _).symm
  whiskerRight_comp β _ _ := by
    simp only [eqToIso_refl, Iso.refl_hom, Iso.refl_inv, Category.comp_id]
    apply Subtype.ext
    ext x
    exact (Category.id_comp _).symm
  whisker_assoc F := by
    intro K K' α L
    simp only [eqToIso_refl, Iso.refl_hom, Iso.refl_inv, Category.id_comp]
    apply Subtype.ext
    ext x
    exact (Category.comp_id _).symm
  whisker_exchange := continuous_whisker_exchange
  pentagon F K L M := by
    simp only [eqToIso_refl, Iso.refl_hom, whiskerL_id, whiskerR_id, Category.id_comp]
    rfl
  triangle F K := by
    simp only [eqToIso_refl, Iso.refl_hom, whiskerL_id, whiskerR_id, Category.id_comp]
    rfl

instance : Bicategory.Strict TopologicalGroupoid.{u} where
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl
  leftUnitor_eqToIso _ := rfl
  rightUnitor_eqToIso _ := rfl
  associator_eqToIso _ _ _ := rfl

/-- Continuous transformations between functors of topological groupoids
have continuous inverses. -/
theorem continuousTransformation_isIso {G H : TopologicalGroupoid.{u}} {F K : G ⟶ H}
    (α : F ⟶ K) : IsIso α := by
  letI : IsIso α.val := naturalTransformation_isIso_of_groupoid α.val
  let β := inv α.val
  have hInv (x : G.Underlying) : β.app x = Groupoid.inv (α.val.app x) := by
    have h := congrArg (fun t : underlyingFunctor F ⟶ underlyingFunctor F => t.app x)
      (IsIso.hom_inv_id α.val)
    change α.val.app x ≫ β.app x = 𝟙 _ at h
    calc
      β.app x = (𝟙 _) ≫ β.app x := (Category.id_comp _).symm
      _ = (Groupoid.inv (α.val.app x) ≫ α.val.app x) ≫ β.app x := by rw [Groupoid.inv_comp]
      _ = Groupoid.inv (α.val.app x) := by rw [Category.assoc, h, Category.comp_id]
  let β' : ContinuousTransformation K F := ⟨β, by
    have eq : (fun x => (β.app x).val) = fun x => H.inverse ((α.val.app x).val) := by
      funext x
      rw [hInv]
      rfl
    rw [eq]
    exact H.inverse.continuous.comp α.property⟩
  refine ⟨⟨β', ?_, ?_⟩⟩
  · exact Subtype.ext (IsIso.hom_inv_id α.val)
  · exact Subtype.ext (IsIso.inv_hom_id α.val)

abbrev underlyingGroupoid (G : TopologicalGroupoid.{u}) : SmallGroupoid₂.{u} :=
  Grpd.of G.Underlying

set_option backward.isDefEq.respectTransparency false in
/-- E.5.4.10. Forgetting continuity is strict on objects, functors,
transformations, and their compositions. -/
def forgetToGroupoids : StrictPseudofunctor TopologicalGroupoid.{u} SmallGroupoid₂.{u} :=
  StrictPseudofunctor.mk'' {
    obj := underlyingGroupoid
    map := fun F => Bicategory.InducedBicategory.mkHom (Cat.Hom.ofFunctor (underlyingFunctor F))
    map₂ := fun α => Bicategory.InducedBicategory.mkHom₂ (Cat.Hom₂.ofNatTrans α.val)
    map_id := fun _ => rfl
    map_comp := fun _ _ => rfl
    map₂_id := fun _ => rfl
    map₂_comp := fun _ _ => rfl
    map₂_whisker_left := by intros; simp only [eqToHom_refl, Category.id_comp, Category.comp_id]; rfl
    map₂_whisker_right := by intros; simp only [eqToHom_refl, Category.id_comp, Category.comp_id]; rfl }

theorem forgetToGroupoids_injective_on_functors
    (G H : TopologicalGroupoid.{u}) :
    Injective (fun F : G ⟶ H => (forgetToGroupoids.{u}).map F) := by
  intro F K h
  apply underlyingFunctor_injective
  exact congrArg (fun f => f.hom.toFunctor) h

instance forgetToGroupoids_faithful_on_transformations (G H : TopologicalGroupoid.{u}) :
    (forgetToGroupoids.toPseudofunctor.toPrelaxFunctor.mapFunctor G H).Faithful where
  map_injective := by
    intro F K α β h
    exact Subtype.ext (congrArg (fun η => η.hom.toNatTrans) h)

end Masullo.TopologicalGroupoid
