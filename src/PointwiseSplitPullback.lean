import SplitFiberedPullback
import StrictCatPullback

open CategoryTheory CategoryTheory.Functor Opposite
open scoped Bicategory CategoryTheory.BasedFunctor

namespace Masullo.SplitFibered

open CategoryTheory.Pseudofunctor.CoGrothendieck

universe u
variable {D : Type u} [SmallCategory D]
variable {F G H : Diagram (D := D)} (t : F ⟶ H) (s : G ⟶ H)

namespace Pointwise
open StrictCatPullback

abbrev Obj (U : Dᵒᵖ) := StrictCatPullback.Obj (t.app U).toFunctor (s.app U).toFunctor

private def left {U V : Dᵒᵖ} (f : U ⟶ V) : Obj t s U ⥤ F.obj V :=
  fst _ _ ⋙ (F.map f).toFunctor

private def right {U V : Dᵒᵖ} (f : U ⟶ V) : Obj t s U ⥤ G.obj V :=
  snd _ _ ⋙ (G.map f).toFunctor

private theorem compatible {U V : Dᵒᵖ} (f : U ⟶ V) :
    left t s f ⋙ (t.app V).toFunctor = right t s f ⋙ (s.app V).toFunctor := by
  change fst _ _ ⋙ (F.map f).toFunctor ⋙ (t.app V).toFunctor =
    snd _ _ ⋙ (G.map f).toFunctor ⋙ (s.app V).toFunctor
  have ht := congrArg Cat.Hom.toFunctor (t.naturality f)
  have hs := congrArg Cat.Hom.toFunctor (s.naturality f)
  simp only [Cat.Hom.comp_toFunctor] at ht hs
  rw [ht, hs]
  exact congrArg (· ⋙ (H.map f).toFunctor) (condition (t.app U).toFunctor (s.app U).toFunctor)

/-- The strict pullback of the original diagrams, formed in each fiber. -/
def diagram : Diagram (D := D) where
  obj U := Cat.of (Obj t s U)
  map f := (lift (left t s f) (right t s f) (compatible t s f)).toCatHom
  map_id U := by
    apply Cat.Hom.ext
    apply functor_ext
    · change left t s (𝟙 U) = fst (t.app U).toFunctor (s.app U).toFunctor
      simp [left]
      rfl
    · change right t s (𝟙 U) = snd (t.app U).toFunctor (s.app U).toFunctor
      simp [right]
      rfl
  map_comp f g := by
    apply Cat.Hom.ext
    apply functor_ext
    · change left t s (f ≫ g) = lift (left t s f) (right t s f) (compatible t s f) ⋙ left t s g
      change fst _ _ ⋙ (F.map (f ≫ g)).toFunctor =
        (lift (left t s f) (right t s f) (compatible t s f) ⋙ fst _ _) ⋙ (F.map g).toFunctor
      rw [lift_fst, F.map_comp, Cat.Hom.comp_toFunctor]
      rfl
    · change right t s (f ≫ g) = lift (left t s f) (right t s f) (compatible t s f) ⋙ right t s g
      change snd _ _ ⋙ (G.map (f ≫ g)).toFunctor =
        (lift (left t s f) (right t s f) (compatible t s f) ⋙ snd _ _) ⋙ (G.map g).toFunctor
      rw [lift_snd, G.map_comp, Cat.Hom.comp_toFunctor]
      rfl

def fstNat : diagram t s ⟶ F where
  app U := (fst (t.app U).toFunctor (s.app U).toFunctor).toCatHom
  naturality _ _ _ := rfl

def sndNat : diagram t s ⟶ G where
  app U := (snd (t.app U).toFunctor (s.app U).toFunctor).toCatHom
  naturality _ _ _ := rfl

theorem conditionNat : fstNat t s ≫ t = sndNat t s ≫ s := by
  apply NatTrans.ext
  funext U
  exact Cat.Hom.ext (condition (t.app U).toFunctor (s.app U).toFunctor)


abbrev Strict := VerticalIsoComma.strictBased (mapBased t) (mapBased s)

private def leftTotal := mapBased (fstNat t s)
private def rightTotal := mapBased (sndNat t s)

private theorem matchTotal (a : total (diagram t s)) :
    (mapBased t).obj ((leftTotal t s).obj a) =
      (mapBased s).obj ((rightTotal t s).obj a) :=
  congrArg (fun z => Pseudofunctor.CoGrothendieck.mk a.base z) a.fiber.matchObj

set_option backward.isDefEq.respectTransparency false in
private def toStrictObj (a : total (diagram t s)) : (Strict t s).obj where
  obj := {
    left := (leftTotal t s).obj a
    right := (rightTotal t s).obj a
    iso := eqToIso (matchTotal t s a)
    vertical := by
      apply IsHomLift.of_fac' _ _ _ rfl rfl
      simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
      change (projection H).map (eqToHom (matchTotal t s a)) = 𝟙 a.base
      rw [eqToHom_map]
      rfl }
  property := ⟨matchTotal t s a, rfl⟩

set_option backward.isDefEq.respectTransparency false in
private theorem leftTotal_map_fiber {a b : total (diagram t s)} (m : a ⟶ b) :
    ((leftTotal t s).map m : (leftTotal t s).obj a ⟶ (leftTotal t s).obj b).fiber =
      m.fiber.left := by
  simp [leftTotal, mapBased, strongOfNatural, fstNat, StrictCatPullback.fst]

set_option backward.isDefEq.respectTransparency false in
private theorem rightTotal_map_fiber {a b : total (diagram t s)} (m : a ⟶ b) :
    ((rightTotal t s).map m : (rightTotal t s).obj a ⟶ (rightTotal t s).obj b).fiber =
      m.fiber.right := by
  simp [rightTotal, mapBased, strongOfNatural, sndNat, StrictCatPullback.snd]

set_option backward.isDefEq.respectTransparency false in
private theorem comp_transport {K : Diagram (D := D)} {U V : D}
    {x : K.obj (op U)} {y z : K.obj (op V)}
    (m : (⟨U, x⟩ : total K) ⟶ ⟨V, y⟩) (h : y = z) :
    m ≫ eqToHom (congrArg (fun w => Pseudofunctor.CoGrothendieck.mk V w) h) =
      (⟨m.base, m.fiber ≫ (K.map m.base.op).toFunctor.map (eqToHom h)⟩ :
        (⟨U, x⟩ : total K) ⟶ ⟨V, z⟩) := by
  subst z
  cases m
  simp
  congr 1
  exact (Category.comp_id _).symm

set_option backward.isDefEq.respectTransparency false in
private theorem transport_comp {K : Diagram (D := D)} {U V : D}
    {x y : K.obj (op U)} {z : K.obj (op V)}
    (h : x = y) (m : (⟨U, y⟩ : total K) ⟶ ⟨V, z⟩) :
    eqToHom (congrArg (fun w => Pseudofunctor.CoGrothendieck.mk U w) h) ≫ m =
      (⟨m.base, eqToHom h ≫ m.fiber⟩ : (⟨U, x⟩ : total K) ⟶ ⟨V, z⟩) := by
  subst x
  cases m
  simp

set_option backward.isDefEq.respectTransparency false in
private theorem square_iff {a b : total (diagram t s)} (f : a.base ⟶ b.base)
    (l : a.fiber.left ⟶ ((F.map f.op).toFunctor.obj b.fiber.left))
    (r : a.fiber.right ⟶ ((G.map f.op).toFunctor.obj b.fiber.right)) :
    let L : (leftTotal t s).obj a ⟶ (leftTotal t s).obj b := ⟨f, l⟩
    let R : (rightTotal t s).obj a ⟶ (rightTotal t s).obj b := ⟨f, r⟩
    ((mapBased t).map L ≫ eqToHom (matchTotal t s b) =
      eqToHom (matchTotal t s a) ≫ (mapBased s).map R) ↔
      ((t.app (op a.base)).toFunctor.map l ≫
        eqToHom (((diagram t s).map f.op).toFunctor.obj b.fiber).matchObj =
      eqToHom a.fiber.matchObj ≫ (s.app (op a.base)).toFunctor.map r) := by
  intro L R
  rw [comp_transport (K := H) ((mapBased t).map L) b.fiber.matchObj,
    transport_comp (K := H) a.fiber.matchObj ((mapBased s).map R)]
  have hT : ((mapBased t).map L).fiber =
      (t.app (op a.base)).toFunctor.map l ≫
        eqToHom (congrArg (fun k : F.obj (op b.base) ⟶ H.obj (op a.base) =>
          k.toFunctor.obj b.fiber.left) (t.naturality f.op)) := by
    simp only [mapBased, Pseudofunctor.CoGrothendieck.map_map_fiber, strongOfNatural]
    exact congrArg ((t.app (op a.base)).toFunctor.map l ≫ ·) (cat_eqToHom_app (t.naturality f.op) b.fiber.left)
  have hS : ((mapBased s).map R).fiber =
      (s.app (op a.base)).toFunctor.map r ≫
        eqToHom (congrArg (fun k : G.obj (op b.base) ⟶ H.obj (op a.base) =>
          k.toFunctor.obj b.fiber.right) (s.naturality f.op)) := by
    simp only [mapBased, Pseudofunctor.CoGrothendieck.map_map_fiber, strongOfNatural]
    exact congrArg ((s.app (op a.base)).toFunctor.map r ≫ ·) (cat_eqToHom_app (s.naturality f.op) b.fiber.right)
  have hEq (p q : (t.app (op a.base)).toFunctor.obj a.fiber.left ⟶
      (H.map f.op).toFunctor.obj ((s.app (op b.base)).toFunctor.obj b.fiber.right)) :
      (⟨f, p⟩ : (mapBased t).obj ((leftTotal t s).obj a) ⟶
        (mapBased s).obj ((rightTotal t s).obj b)) = ⟨f, q⟩ ↔ p = q := by
    constructor
    · intro h
      simpa using (Pseudofunctor.CoGrothendieck.Hom.congr h)
    · rintro rfl
      rfl
  change (⟨f, ((mapBased t).map L).fiber ≫ (H.map f.op).toFunctor.map
      (eqToHom b.fiber.matchObj)⟩ :
        (mapBased t).obj ((leftTotal t s).obj a) ⟶
          (mapBased s).obj ((rightTotal t s).obj b)) =
        ⟨f, eqToHom a.fiber.matchObj ≫ ((mapBased s).map R).fiber⟩ ↔ _
  rw [hEq, hT, hS]
  have htransport : eqToHom (congrArg (fun k : F.obj (op b.base) ⟶ H.obj (op a.base) =>
        k.toFunctor.obj b.fiber.left) (t.naturality f.op)) ≫
      (H.map f.op).toFunctor.map (eqToHom b.fiber.matchObj) =
      eqToHom (((diagram t s).map f.op).toFunctor.obj b.fiber).matchObj ≫
        eqToHom (congrArg (fun k : G.obj (op b.base) ⟶ H.obj (op a.base) =>
          k.toFunctor.obj b.fiber.right) (s.naturality f.op)) := by
    rw [eqToHom_map, eqToHom_trans, eqToHom_trans]
  rw [Category.assoc, htransport, ← Category.assoc, ← Category.assoc]
  exact cancel_mono _


set_option backward.isDefEq.respectTransparency false in
/-- The total category of the pointwise diagram maps to the strict pullback
over the base by taking the two components of each object and arrow. -/
def comparison : based (diagram t s) ⥤ᵇ Strict t s where
  toFunctor := {
    obj := toStrictObj t s
    map := fun m => ⟨{
      left := (leftTotal t s).map m
      right := (rightTotal t s).map m
      over := by
        apply IsHomLift.of_fac' _ _ _ rfl rfl
        simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
        rfl
      square := by
        have h := (square_iff t s m.base m.fiber.left m.fiber.right).2 m.fiber.matchHom
        have hl : (leftTotal t s).map m = ⟨m.base, m.fiber.left⟩ :=
          Hom.ext _ _ rfl (by simpa using leftTotal_map_fiber t s m)
        have hr : (rightTotal t s).map m = ⟨m.base, m.fiber.right⟩ :=
          Hom.ext _ _ rfl (by simpa using rightTotal_map_fiber t s m)
        simpa only [toStrictObj, hl, hr, eqToIso.hom] using h }⟩
    map_id := fun a => ObjectProperty.hom_ext _
      (VerticalIsoComma.Arrow.ext ((leftTotal t s).map_id a) ((rightTotal t s).map_id a))
    map_comp := fun f g => ObjectProperty.hom_ext _
      (VerticalIsoComma.Arrow.ext ((leftTotal t s).map_comp f g) ((rightTotal t s).map_comp f g)) }
  w := rfl

@[simp] theorem comparison_fst :
    comparison t s ⋙ VerticalIsoComma.strictFst (mapBased t) (mapBased s) =
      mapBased (fstNat t s) := rfl

@[simp] theorem comparison_snd :
    comparison t s ⋙ VerticalIsoComma.strictSnd (mapBased t) (mapBased s) =
      mapBased (sndNat t s) := rfl

set_option backward.isDefEq.respectTransparency false in
theorem comparison_obj_bijective : Function.Bijective (comparison t s).obj := by
  constructor
  · rintro ⟨U, x⟩ ⟨V, y⟩ h
    have hL := congrArg (fun a : (Strict t s).obj => a.obj.left) h
    have hR := congrArg (fun a : (Strict t s).obj => a.obj.right) h
    have hbase : U = V := congrArg Pseudofunctor.CoGrothendieck.base hL
    subst V
    have hx : x.left = y.left := eq_of_heq (Pseudofunctor.CoGrothendieck.mk.inj hL).2
    have hy : x.right = y.right := eq_of_heq (Pseudofunctor.CoGrothendieck.mk.inj hR).2
    exact congrArg (fun w => Pseudofunctor.CoGrothendieck.mk U w) (StrictCatPullback.Obj.ext hx hy)
  · rintro ⟨⟨⟨U, x⟩, ⟨V, y⟩, e, _⟩, ⟨h, _⟩⟩
    have hbase : U = V := congrArg Pseudofunctor.CoGrothendieck.base h
    subst V
    have hxy : (t.app (op U)).toFunctor.obj x = (s.app (op U)).toFunctor.obj y :=
      eq_of_heq (Pseudofunctor.CoGrothendieck.mk.inj h).2
    exact ⟨⟨U, ⟨x, y, hxy⟩⟩, VerticalIsoComma.strictObj_ext _ _ rfl rfl⟩

set_option backward.isDefEq.respectTransparency false in
private theorem alignBase {K : Diagram (D := D)} {a b : total K}
    (r : a ⟶ b) (f : a.base ⟶ b.base) (h : r.base = f) :
    (⟨f, h ▸ r.fiber⟩ : a ⟶ b) = r := by
  subst f
  cases r
  rfl

set_option backward.isDefEq.respectTransparency false in
private def comparisonPreimage {a b : total (diagram t s)}
    (m : (comparison t s).obj a ⟶ (comparison t s).obj b) :
    {n : a ⟶ b // (comparison t s).map n = m} := by
  let l := m.hom.left
  let r := m.hom.right
  haveI : (projection G).IsHomLift l.base r := m.hom.over
  have hb : r.base = l.base := by
    have h := IsHomLift.fac' (projection G) l.base r
    simpa using h
  let r' : (rightTotal t s).obj a ⟶ (rightTotal t s).obj b := ⟨l.base, hb ▸ r.fiber⟩
  have hr : r' = r := alignBase r l.base hb
  have hs := m.hom.square
  change (mapBased t).map l ≫ eqToHom (matchTotal t s b) =
    eqToHom (matchTotal t s a) ≫ (mapBased s).map r at hs
  rw [← hr] at hs
  let n : a ⟶ b := ⟨l.base, ⟨l.fiber, r'.fiber, (square_iff t s l.base l.fiber r'.fiber).1 hs⟩⟩
  refine ⟨n, ObjectProperty.hom_ext _ (VerticalIsoComma.Arrow.ext ?_ ?_)⟩
  · change (leftTotal t s).map n = l
    refine Hom.ext ((leftTotal t s).map n) l rfl ?_
    simpa only [eqToHom_refl, Category.comp_id] using leftTotal_map_fiber t s n
  · change (rightTotal t s).map n = r
    refine Eq.trans (b := r') ?_ hr
    refine Hom.ext ((rightTotal t s).map n) r' rfl ?_
    simpa only [eqToHom_refl, Category.comp_id] using rightTotal_map_fiber t s n

set_option backward.isDefEq.respectTransparency false in
def comparison_fullyFaithful : (comparison t s).toFunctor.FullyFaithful where
  preimage m := (comparisonPreimage t s m).val
  map_preimage m := (comparisonPreimage t s m).property
  preimage_map {a b} m := by
    let n := (comparisonPreimage t s ((comparison t s).map m)).val
    have h := (comparisonPreimage t s ((comparison t s).map m)).property
    have hl : (leftTotal t s).map n = (leftTotal t s).map m :=
      congrArg (fun f => f.hom.left) h
    have hr : (rightTotal t s).map n = (rightTotal t s).map m :=
      congrArg (fun f => f.hom.right) h
    have hb : n.base = m.base := congrArg (fun f => f.base) hl
    apply Hom.ext _ _ hb
    apply StrictCatPullback.Hom.ext
    · have h₁ := Pseudofunctor.CoGrothendieck.Hom.congr hl
      rw [leftTotal_map_fiber, leftTotal_map_fiber] at h₁
      simpa [StrictCatPullback.fst, eqToHom_map] using h₁
    · have h₂ := Pseudofunctor.CoGrothendieck.Hom.congr hr
      rw [rightTotal_map_fiber, rightTotal_map_fiber] at h₂
      simpa [StrictCatPullback.snd, eqToHom_map] using h₂


/-- The canonical comparison is an isomorphism of the total categories. -/
noncomputable def comparisonIso :
    Cat.of (total (diagram t s)) ≅ Cat.of (Strict t s).obj :=
  StrictCatPullback.isoOfFullyFaithfulBijective (comparison t s).toFunctor.toCatHom
    (comparison_fullyFaithful t s) (comparison_obj_bijective t s)

set_option backward.isDefEq.respectTransparency false in
/-- The inverse of the canonical comparison is also a functor over the base. -/
noncomputable def comparisonInverse : Strict t s ⥤ᵇ based (diagram t s) where
  toFunctor := (comparisonIso t s).inv.toFunctor
  w := by
    have h := congrArg Cat.Hom.toFunctor (comparisonIso t s).inv_hom_id
    change (comparisonIso t s).inv.toFunctor ⋙ (comparison t s).toFunctor = Functor.id (Strict t s).obj at h
    have hw := (comparison t s).w
    change (comparison t s).toFunctor ⋙ (Strict t s).p = projection (diagram t s) at hw
    change (comparisonIso t s).inv.toFunctor ⋙ projection (diagram t s) = (Strict t s).p
    rw [← hw, ← Functor.assoc, h]
    rfl

private theorem basedFunctor_ext {X Y : BasedCategory.{u, u} D} {I J : X ⥤ᵇ Y}
    (h : I.toFunctor = J.toFunctor) : I = J := by
  cases I
  cases J
  cases h
  rfl

/-- The comparison and its inverse are strictly inverse over the base. -/
theorem comparison_inverse :
    comparison t s ⋙ comparisonInverse t s = BasedFunctor.id (based (diagram t s)) ∧
      comparisonInverse t s ⋙ comparison t s = BasedFunctor.id (Strict t s) := by
  constructor
  · apply basedFunctor_ext
    exact congrArg Cat.Hom.toFunctor (comparisonIso t s).hom_inv_id
  · apply basedFunctor_ext
    exact congrArg Cat.Hom.toFunctor (comparisonIso t s).inv_hom_id

end Pointwise

end Masullo.SplitFibered
