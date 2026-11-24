import VerticalIsoCommaFibered
import Mathlib.CategoryTheory.Sites.Grothendieck

open CategoryTheory CategoryTheory.Functor CategoryTheory.IsHomLift
open scoped CategoryTheory.BasedFunctor

namespace Masullo.VerticalIsoComma

universe u

variable {D : Type u} [SmallCategory D]

/-- A section over a diagram in the base, taking its arrows to Cartesian arrows.
Its morphisms are vertical natural transformations. -/
structure CartesianSection (T X : BasedCategory.{u, u} D) where
  functor : T ⥤ᵇ X
  cartesian : ∀ {a b : T.obj} (f : a ⟶ b), X.p.IsStronglyCartesian (T.p.map f) (functor.map f)

namespace CartesianSection

variable {T K X Y Z : BasedCategory.{u, u} D}

instance : Category (CartesianSection T X) where
  Hom A B := A.functor ⟶ B.functor
  id A := 𝟙 A.functor
  comp f g := f ≫ g
  id_comp f := Category.id_comp f
  comp_id f := Category.comp_id f
  assoc f g h := Category.assoc f g h

def precompose (i : K ⥤ᵇ T) (X : BasedCategory.{u, u} D) :
    CartesianSection T X ⥤ CartesianSection K X where
  obj A := ⟨i ⋙ A.functor, fun f ↦ by
    have h := A.cartesian (i.map f)
    change X.p.IsStronglyCartesian (K.p.map f) (A.functor.map (i.map f))
    rw [← i.w]
    exact h⟩
  map {A B} n := BasedCategory.whiskerLeft i n
  map_id _ := rfl
  map_comp _ _ := rfl

def postcompose (F : X ⥤ᵇ Y) (hF : PreservesCartesian F) (T : BasedCategory.{u, u} D) :
    CartesianSection T X ⥤ CartesianSection T Y where
  obj A := ⟨A.functor ⋙ F, fun f ↦ hF _ _ (A.cartesian f)⟩
  map {A B} n := BasedCategory.whiskerRight n F
  map_id A := by
    apply BasedNatTrans.ext
    ext a
    exact F.map_id _
  map_comp n m := by
    apply BasedNatTrans.ext
    ext a
    exact F.map_comp _ _

@[ext]
theorem hom_ext {A B : CartesianSection T X} {n m : A ⟶ B}
    (h : ∀ a, n.toNatTrans.app a = m.toNatTrans.app a) : n = m := by
  apply BasedNatTrans.ext
  exact NatTrans.ext (funext h)

def fstSection {F : X ⥤ᵇ Z} {G : Y ⥤ᵇ Z}
    [X.p.IsFibered] [Y.p.IsFibered] (hF : PreservesCartesian F) (hG : PreservesCartesian G) :
    CartesianSection T (based F G) ⥤ CartesianSection T X :=
  postcompose (fst F G) (preserves_projections hF hG).1 T

def sndSection {F : X ⥤ᵇ Z} {G : Y ⥤ᵇ Z}
    [X.p.IsFibered] [Y.p.IsFibered] (hF : PreservesCartesian F) (hG : PreservesCartesian G) :
    CartesianSection T (based F G) ⥤ CartesianSection T Y :=
  postcompose (snd F G) (preserves_projections hF hG).2 T

def comparisonIso {F : X ⥤ᵇ Z} {G : Y ⥤ᵇ Z}
    [X.p.IsFibered] [Y.p.IsFibered] (hF : PreservesCartesian F) (hG : PreservesCartesian G)
    (A : CartesianSection T (based F G)) :
    (postcompose F hF T).obj ((fstSection hF hG).obj A) ≅
      (postcompose G hG T).obj ((sndSection hF hG).obj A) := by
  let e : ((A.functor ⋙ fst F G) ⋙ F) ≅ ((A.functor ⋙ snd F G) ⋙ G) := BasedNatIso.mkNatIso
    (isoWhiskerLeft A.functor.toFunctor ((BasedNatTrans.forgetful (based F G) Z).mapIso
      (comparison F G)))
    (fun a ↦ (comparison F G).hom.isHomLift (A.functor.w_obj a))
  exact ⟨e.hom, e.inv, e.hom_inv_id, e.inv_hom_id⟩

section Pullback

variable {F : X ⥤ᵇ Z} {G : Y ⥤ᵇ Z} (i : K ⥤ᵇ T)
  [X.p.IsFibered] [Y.p.IsFibered] (hF : PreservesCartesian F) (hG : PreservesCartesian G)

private def pairSection (A : CartesianSection T X) (B : CartesianSection T Y)
    (e : (postcompose F hF T).obj A ≅ (postcompose G hG T).obj B) :
    CartesianSection T (based F G) where
  functor := lift F G A.functor B.functor ⟨e.hom, e.inv, e.hom_inv_id, e.inv_hom_id⟩
  cartesian f := strong_of_components hG _ _ (A.cartesian f) (B.cartesian f)

private def pairHom {A B : CartesianSection T (based F G)}
    (a : (fstSection hF hG).obj A ⟶ (fstSection hF hG).obj B)
    (b : (sndSection hF hG).obj A ⟶ (sndSection hF hG).obj B)
    (h : (postcompose F hF T).map a ≫ (comparisonIso hF hG B).hom =
      (comparisonIso hF hG A).hom ≫ (postcompose G hG T).map b) : A ⟶ B where
  app t := ⟨a.toNatTrans.app t, b.toNatTrans.app t,
    sameBase (𝟙 (T.p.obj t)) _ _ (ha := a.isHomLift rfl) (hb := b.isHomLift rfl),
    congrArg (fun n => n.toNatTrans.app t) h⟩
  naturality {x y} f := by
    apply Arrow.ext
    · exact a.toNatTrans.naturality f
    · exact b.toNatTrans.naturality f
  isHomLift' t := by
    exact @BasedFunctor.isHomLift_map D _ (based F G) X (fst F G) _ _ _ _
      (𝟙 (T.p.obj t)) _ (a.isHomLift rfl)

/-- Compatible morphisms between two pairs with comparison isomorphisms
descend when the component restrictions are fully faithful and the
target restriction is faithful. -/
noncomputable def precomposePullbackFullyFaithful
    (hX : (precompose i X).FullyFaithful)
    (hY : (precompose i Y).FullyFaithful)
    (hZ : (precompose i Z).Faithful) :
    (precompose i (based F G)).FullyFaithful where
  preimage {A B} n := by
    let a : (fstSection hF hG).obj A ⟶ (fstSection hF hG).obj B :=
      hX.preimage ((fstSection hF hG).map n)
    let b : (sndSection hF hG).obj A ⟶ (sndSection hF hG).obj B :=
      hY.preimage ((sndSection hF hG).map n)
    refine pairHom hF hG a b ?_
    apply (precompose i Z).map_injective
    have ha := hX.map_preimage (X := (fstSection hF hG).obj A)
      (Y := (fstSection hF hG).obj B) ((fstSection hF hG).map n)
    have hb := hY.map_preimage (X := (sndSection hF hG).obj A)
      (Y := (sndSection hF hG).obj B) ((sndSection hF hG).map n)
    exact hom_ext (fun t ↦ by
      change F.map (a.toNatTrans.app (i.obj t)) ≫ (B.functor.obj (i.obj t)).iso.hom =
        (A.functor.obj (i.obj t)).iso.hom ≫ G.map (b.toNatTrans.app (i.obj t))
      rw [show a.toNatTrans.app (i.obj t) = (n.toNatTrans.app t).left from
        congrArg (fun m => m.toNatTrans.app t) ha,
        show b.toNatTrans.app (i.obj t) = (n.toNatTrans.app t).right from
        congrArg (fun m => m.toNatTrans.app t) hb]
      exact (n.toNatTrans.app t).square)
  map_preimage {A B} n := by
    apply hom_ext
    intro t
    apply Arrow.ext
    · exact congrArg (fun m => m.toNatTrans.app t)
        (hX.map_preimage (X := (fstSection hF hG).obj A)
          (Y := (fstSection hF hG).obj B) ((fstSection hF hG).map n))
    · exact congrArg (fun m => m.toNatTrans.app t)
        (hY.map_preimage (X := (sndSection hF hG).obj A)
          (Y := (sndSection hF hG).obj B) ((sndSection hF hG).map n))
  preimage_map {A B} n := by
    apply hom_ext
    intro t
    apply Arrow.ext
    · exact congrArg (fun m => m.toNatTrans.app t)
        (hX.preimage_map ((fstSection hF hG).map n))
    · exact congrArg (fun m => m.toNatTrans.app t)
        (hY.preimage_map ((sndSection hF hG).map n))

include hF hG in
/-- A local pair is effective whenever the two objects descend and their
comparison can be lifted uniquely in the common target. -/
theorem precomposePullbackEssSurj
    (hX : (precompose i X).EssSurj)
    (hY : (precompose i Y).EssSurj)
    (hZ : (precompose i Z).FullyFaithful) :
    (precompose i (based F G)).EssSurj := by
  constructor
  intro L
  obtain ⟨A, ⟨a⟩⟩ := hX.mem_essImage ((fstSection hF hG).obj L)
  obtain ⟨B, ⟨b⟩⟩ := hY.mem_essImage ((sndSection hF hG).obj L)
  let localIso : (precompose i Z).obj ((postcompose F hF T).obj A) ≅
      (precompose i Z).obj ((postcompose G hG T).obj B) :=
    (postcompose F hF K).mapIso a ≪≫ comparisonIso hF hG L ≪≫
      ((postcompose G hG K).mapIso b).symm
  let e := hZ.preimageIso localIso
  let P := pairSection hF hG A B e
  have he := hZ.map_preimage localIso.hom
  have hs (t : K.obj) : F.map (a.hom.toNatTrans.app t) ≫ (L.functor.obj t).iso.hom =
      ((P.functor.obj (i.obj t)).iso.hom) ≫ G.map (b.hom.toNatTrans.app t) := by
    have ht := congrArg (fun n => n.toNatTrans.app t) he
    change (P.functor.obj (i.obj t)).iso.hom =
      F.map (a.hom.toNatTrans.app t) ≫ (L.functor.obj t).iso.hom ≫ G.map (b.inv.toNatTrans.app t) at ht
    have hb : G.map (b.inv.toNatTrans.app t) ≫ G.map (b.hom.toNatTrans.app t) = 𝟙 _ := by
      rw [← G.map_comp]
      exact (congrArg (fun n => G.map (n.toNatTrans.app t)) b.inv_hom_id).trans (G.map_id _)
    rw [ht]
    exact ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·)
      ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hb).trans (Category.comp_id _))))).symm
  let a' : ((i ⋙ P.functor) ⋙ fst F G) ≅ (L.functor ⋙ fst F G) :=
    ⟨a.hom, a.inv, a.hom_inv_id, a.inv_hom_id⟩
  let b' : ((i ⋙ P.functor) ⋙ snd F G) ≅ (L.functor ⋙ snd F G) :=
    ⟨b.hom, b.inv, b.hom_inv_id, b.inv_hom_id⟩
  obtain ⟨j, _, _⟩ := uniqueIsoLift (i ⋙ P.functor) L.functor a' b' hs
  exact ⟨P, ⟨⟨j.hom, j.inv, j.hom_inv_id, j.inv_hom_id⟩⟩⟩

end Pullback

end CartesianSection

/-- The arrow categories of a sieve and the entire slice carry their domain
projections to the base. The inclusion restricts sections to the sieve. -/
def sieveInclusion {U : D} (R : Sieve U) :
    BasedCategory.ofFunctor R.arrows.diagram ⥤ᵇ BasedCategory.ofFunctor (Over.forget U) where
  toFunctor := ObjectProperty.ι _
  w := rfl

/-- A category fibred in groupoids is a stack when Cartesian sections over
a slice restrict by an equivalence to Cartesian sections on every covering
sieve. The section morphisms are vertical natural transformations. -/
structure StackInGroupoids (J : GrothendieckTopology D) (X : BasedCategory.{u, u} D) : Prop where
  fibered : X.p.IsFibered
  verticalIsIso : ∀ (U : D) {a b : X.obj} (m : a ⟶ b), X.p.IsHomLift (𝟙 U) m → IsIso m
  descent : ∀ (U : D) (R : Sieve U), R ∈ J U →
    (CartesianSection.precompose (sieveInclusion R) X).IsEquivalence

set_option backward.isDefEq.respectTransparency false in
/-- All 2-morphisms between Cartesian functors into a stack in groupoids
are invertible. Their components are vertical morphisms. -/
theorem StackInGroupoids.natTrans_isIso {J : GrothendieckTopology D}
    {T X : BasedCategory.{u, u} D} (hX : StackInGroupoids J X)
    {A B : T ⥤ᵇ X} (n : A ⟶ B) : IsIso n := by
  haveI (t : T.obj) : IsIso (n.toNatTrans.app t) :=
    hX.verticalIsIso (T.p.obj t) _ (n.isHomLift rfl)
  letI : IsIso (X := A.toFunctor) n.toNatTrans := NatIso.isIso_of_isIso_app _
  exact BasedNatIso.isIso_of_toNatTrans_isIso n

/-- Stacks in groupoids on a fixed site, with Cartesian functors as
one-morphisms and all vertical natural transformations as two-morphisms. -/
structure Stacks (J : GrothendieckTopology D) where
  basedCategory : BasedCategory.{u, u} D
  isStack : StackInGroupoids J basedCategory

namespace Stacks

variable {J : GrothendieckTopology D}

abbrev Hom (A B : Stacks J) :=
  {F : A.basedCategory ⥤ᵇ B.basedCategory // PreservesCartesian F}

instance {A B : Stacks J} : Category (Hom A B) where
  Hom F G := F.val ⟶ G.val
  id F := 𝟙 F.val
  comp n m := n ≫ m
  id_comp n := Category.id_comp n
  comp_id n := Category.comp_id n
  assoc n m k := Category.assoc n m k

private def reflIso {A B : Stacks J} {F G : Hom A B} (h : F.val = G.val) : F ≅ G :=
  eqToIso (Subtype.ext h)

open scoped Bicategory in
instance bicategory : Bicategory (Stacks J) where
  Hom := Hom
  id A := ⟨BasedFunctor.id A.basedCategory, fun _ _ h ↦ h⟩
  comp F G := ⟨F.val ⋙ G.val, fun f m h ↦ G.property f _ (F.property f m h)⟩
  homCategory _ _ := inferInstance
  whiskerLeft {_ _ _} F {_ _} n := BasedCategory.whiskerLeft F.val n
  whiskerRight {_ _ _} {_ _} n G := BasedCategory.whiskerRight n G.val
  associator F G H := reflIso (BasedFunctor.comp_assoc F.val G.val H.val)
  leftUnitor F := reflIso (BasedFunctor.id_comp F.val)
  rightUnitor F := reflIso (BasedFunctor.comp_id F.val)
  whiskerLeft_id _ _ := rfl
  whiskerLeft_comp {_ _ _} _ {_ _ _} _ _ := rfl
  id_whiskerLeft n := Bicategory.id_whiskerLeft (B := BasedCategory D) n
  comp_whiskerLeft {_ _ _ _} F G {_ _} n :=
    Bicategory.comp_whiskerLeft (B := BasedCategory.{u, u} D) F.val G.val n
  id_whiskerRight F G := Bicategory.id_whiskerRight (B := BasedCategory D) F.val G.val
  comp_whiskerRight n m G := Bicategory.comp_whiskerRight (B := BasedCategory D) n m G.val
  whiskerRight_id n := Bicategory.whiskerRight_id (B := BasedCategory D) n
  whiskerRight_comp n G H := Bicategory.whiskerRight_comp (B := BasedCategory D) n G.val H.val
  whisker_assoc {_ _ _ _} F {_ _} n G :=
    Bicategory.whisker_assoc (B := BasedCategory.{u, u} D) F.val n G.val
  whisker_exchange n m := Bicategory.whisker_exchange (B := BasedCategory D) n m
  pentagon F G H I := Bicategory.pentagon (B := BasedCategory.{u, u} D) F.val G.val H.val I.val
  triangle F G := Bicategory.triangle (B := BasedCategory.{u, u} D) F.val G.val

instance : Bicategory.Strict (Stacks J) where
  id_comp F := Subtype.ext (BasedFunctor.id_comp F.val)
  comp_id F := Subtype.ext (BasedFunctor.comp_id F.val)
  assoc F G H := Subtype.ext (BasedFunctor.comp_assoc F.val G.val H.val)
  leftUnitor_eqToIso _ := rfl
  rightUnitor_eqToIso _ := rfl
  associator_eqToIso _ _ _ := rfl

instance (A B : Stacks J) : IsGroupoid (A ⟶ B) where
  all_isIso n := by
    obtain ⟨⟨m, hm, hn⟩⟩ := B.isStack.natTrans_isIso n
    exact ⟨⟨m, hm, hn⟩⟩

end Stacks

/-- E.5.7.13. The two-fibre product computed among categories fibred in
groupoids is already a stack. Thus the identity gives its associated stack.
The projections preserve Cartesian arrows, so the same based universal
property gives the two-fibre product among stacks. -/
theorem stackTwoPullback {J : GrothendieckTopology D}
    {X Y Z : BasedCategory.{u, u} D} {F : X ⥤ᵇ Z} {G : Y ⥤ᵇ Z}
    (hX : StackInGroupoids J X) (hY : StackInGroupoids J Y) (hZ : StackInGroupoids J Z)
    (hF : PreservesCartesian F) (hG : PreservesCartesian G) :
    StackInGroupoids J (based F G) ∧ PreservesCartesian (fst F G) ∧ PreservesCartesian (snd F G) := by
  letI := hX.fibered
  letI := hY.fibered
  refine ⟨⟨isFibered hF hG, ?_, ?_⟩, preserves_projections hF hG⟩
  · intro U a b m hm
    exact vertical_arrow_isIso hX.verticalIsIso hY.verticalIsIso m hm
  · intro U R hR
    let i := sieveInclusion R
    letI := hX.descent U R hR
    letI := hY.descent U R hR
    letI := hZ.descent U R hR
    let ff := CartesianSection.precomposePullbackFullyFaithful i hF hG
      (.ofFullyFaithful (CartesianSection.precompose i X))
      (.ofFullyFaithful (CartesianSection.precompose i Y)) inferInstance
    haveI := ff.full
    haveI := ff.faithful
    haveI := CartesianSection.precomposePullbackEssSurj i hF hG inferInstance inferInstance
      (.ofFullyFaithful (CartesianSection.precompose i Z))
    exact {}

/-- A cone of Cartesian functors into the components induces a Cartesian
functor to the two-pullback stack, with the specified projections and comparison. -/
theorem stackTwoPullbackLift {X Y Z T : BasedCategory.{u, u} D}
    {F : X ⥤ᵇ Z} {G : Y ⥤ᵇ Z} (hG : PreservesCartesian G)
    (A : T ⥤ᵇ X) (B : T ⥤ᵇ Y) (e : (A ⋙ F) ≅ (B ⋙ G))
    (hA : PreservesCartesian A) (hB : PreservesCartesian B) :
    let H := lift F G A B e
    PreservesCartesian H ∧ H ⋙ fst F G = A ∧ H ⋙ snd F G = B ∧
      ∀ t, (H.obj t).iso.hom = e.hom.toNatTrans.app t := by
  exact ⟨preserves_lift hG A B e hA hB,
    lift_fst F G A B e, lift_snd F G A B e, lift_comparison F G A B e⟩

end Masullo.VerticalIsoComma
