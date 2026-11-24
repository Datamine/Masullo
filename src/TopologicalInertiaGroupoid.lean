import TopologicalGroupoidTwoCategory
import BasedInertia
import StrictCatPullback

open CategoryTheory CategoryTheory.Limits Function Set Topology

namespace Masullo.TopologicalGroupoid

universe u
variable (G : TopologicalGroupoid.{u})

private instance : CompactlyGeneratedSpace G.Inertia :=
  closed_compactlyGenerated G.inertia_isClosed

/-- The loop space as an object of CGWH. -/
abbrev loopSpace : CGWH.{u} := G.inertiaFork.pt

/-- The base-point map of a continuous family of loops. -/
def loopBase : C(G.Inertia, G.objects.obj) := G.source.comp ⟨Subtype.val, continuous_subtype_val⟩

private abbrev arrowSource : G.arrows ⟶ G.objects := CGWH.map G.source
private abbrev loopSource : G.loopSpace ⟶ G.objects := CGWH.map G.loopBase

/-- The arrows of the conjugation groupoid form the internal pullback
of the source map and the base-point map of a loop. -/
abbrev InertiaArrow := CGWH.FibreSubspace G.arrowSource G.loopSource

instance : CompactlyGeneratedSpace G.InertiaArrow :=
  closed_compactlyGenerated (CGWH.fibreSubspace_isClosed G.arrowSource G.loopSource)

abbrev inertiaArrowSpace : CGWH.{u} :=
  CGWH.of (X := G.InertiaArrow)
    (CGWH.fibreSubspace_weaklyHausdorff G.arrowSource G.loopSource)

/-- The arrow space, with its two coordinate projections, computes the
pullback in CGWH. -/
def inertiaArrowPullback : LimitCone (cospan G.arrowSource G.loopSource) :=
  CGWH.fibreSubspaceLimit G.arrowSource G.loopSource

private def transportArrow : C(G.InertiaArrow, G.arrows.obj) :=
  ⟨fun p => p.val.1, continuous_fst.comp (continuous_Kelley_forget.comp continuous_subtype_val)⟩

private def sourceLoop : C(G.InertiaArrow, G.Inertia) :=
  ⟨fun p => p.val.2, continuous_snd.comp (continuous_Kelley_forget.comp continuous_subtype_val)⟩

private def loopArrow : C(G.InertiaArrow, G.arrows.obj) :=
  ⟨fun p => p.val.2.val, continuous_subtype_val.comp (G.sourceLoop.continuous)⟩

/-- Compose continuous families of composable arrows. -/
def composeMaps {T : Type u} [TopologicalSpace T] [CompactlyGeneratedSpace T]
    (f g : C(T, G.arrows.obj)) (h : ∀ t, G.target (f t) = G.source (g t)) :
    C(T, G.arrows.obj) :=
  G.comp.comp ⟨fun t => ⟨(f t, g t), h t⟩, (kelleyPair f g).continuous.subtype_mk _⟩

private def firstComposite : C(G.InertiaArrow, G.arrows.obj) :=
  G.composeMaps G.loopArrow G.transportArrow (fun p => p.val.2.property.symm.trans p.property.symm)

private theorem firstComposite_source (p : G.InertiaArrow) :
    G.source (G.firstComposite p) = G.source p.val.2.val :=
  G.source_comp ⟨(p.val.2.val, p.val.1), p.val.2.property.symm.trans p.property.symm⟩

private def conjugatedArrow : C(G.InertiaArrow, G.arrows.obj) :=
  G.composeMaps (G.inverse.comp G.transportArrow) G.firstComposite
    (fun p => (G.target_inv p.val.1).trans (p.property.trans (G.firstComposite_source p).symm))

private theorem conjugated_source (p : G.InertiaArrow) :
    G.source (G.conjugatedArrow p) = G.target p.val.1 :=
  (G.source_comp _).trans (G.source_inv _)

private theorem conjugated_target (p : G.InertiaArrow) :
    G.target (G.conjugatedArrow p) = G.target p.val.1 :=
  (G.target_comp _).trans (G.target_comp _)

private def targetLoop : C(G.InertiaArrow, G.Inertia) :=
  ⟨fun p => ⟨G.conjugatedArrow p, (G.conjugated_source p).trans (G.conjugated_target p).symm⟩,
    G.conjugatedArrow.continuous.subtype_mk _⟩

private def unitArrow : C(G.Inertia, G.InertiaArrow) :=
  ⟨fun g => ⟨(G.unit (G.source g.val), g), G.source_unit _⟩,
    (kelleyPair (G.unit.comp G.loopBase) (ContinuousMap.id _)).continuous.subtype_mk _⟩

private def reverseArrow : C(G.InertiaArrow, G.InertiaArrow) :=
  ⟨fun p => ⟨(G.inverse p.val.1, G.targetLoop p),
      (G.source_inv _).trans (G.conjugated_source p).symm⟩,
    (kelleyPair (G.inverse.comp G.transportArrow) G.targetLoop).continuous.subtype_mk _⟩

private abbrev Pairs := ComposableArrows (G.sourceLoop.toFun) (G.targetLoop.toFun)

private theorem pairs_closed :
    IsClosed {p : Kelley (G.InertiaArrow × G.InertiaArrow) | G.targetLoop p.1 = G.sourceLoop p.2} :=
  CGWH.fibreSubspace_isClosed (CGWH.map (X := G.inertiaArrowSpace) (Y := G.loopSpace) G.targetLoop)
    (CGWH.map (X := G.inertiaArrowSpace) (Y := G.loopSpace) G.sourceLoop)

private instance : CompactlyGeneratedSpace G.Pairs := closed_compactlyGenerated G.pairs_closed

private def first (p : G.Pairs) : G.InertiaArrow := p.val.1
private def second (p : G.Pairs) : G.InertiaArrow := p.val.2
private def firstMap : C(G.Pairs, G.InertiaArrow) :=
  ⟨G.first, continuous_fst.comp (continuous_Kelley_forget.comp continuous_subtype_val)⟩
private def secondMap : C(G.Pairs, G.InertiaArrow) :=
  ⟨G.second, continuous_snd.comp (continuous_Kelley_forget.comp continuous_subtype_val)⟩

private theorem transport_composable (p : G.Pairs) :
    G.target (G.first p).val.1 = G.source (G.second p).val.1 :=
  (G.conjugated_source (G.first p)).symm.trans
    ((congrArg (fun a : G.Inertia => G.source a.val) p.property).trans (G.second p).property.symm)

private def compositeTransport : C(G.Pairs, G.arrows.obj) :=
  G.composeMaps (G.transportArrow.comp G.firstMap) (G.transportArrow.comp G.secondMap)
    G.transport_composable

private def compositeArrow : C(G.Pairs, G.InertiaArrow) :=
  ⟨fun p => ⟨(G.compositeTransport p, G.sourceLoop (G.first p)),
      (G.source_comp _).trans (G.first p).property⟩,
    (kelleyPair G.compositeTransport (G.sourceLoop.comp G.firstMap)).continuous.subtype_mk _⟩


private def loopOf {x : G.Underlying} (g : x ⟶ x) : G.Inertia :=
  ⟨g.val, g.property.1.trans g.property.2.symm⟩

private def pairOf {x y : G.Underlying} (r : x ⟶ y) (g : x ⟶ x) : G.InertiaArrow :=
  ⟨(r.val, G.loopOf g), r.property.1.trans g.property.1.symm⟩

private def conjugate {x y : G.Underlying} (r : x ⟶ y) (g : x ⟶ x) : y ⟶ y :=
  Groupoid.inv r ≫ g ≫ r

private theorem conjugate_id {x : G.Underlying} (g : x ⟶ x) :
    G.conjugate (𝟙 x) g = g := by simp [conjugate]

private theorem conjugate_comp {x y z : G.Underlying} (r : x ⟶ y) (s : y ⟶ z) (g : x ⟶ x) :
    G.conjugate (r ≫ s) g = G.conjugate s (G.conjugate r g) := by
  simp [conjugate, Groupoid.inv_eq_inv, Category.assoc]

private theorem conjugate_inverse {x y : G.Underlying} (r : x ⟶ y) (g : x ⟶ x) :
    G.conjugate (Groupoid.inv r) (G.conjugate r g) = g := by
  rw [← conjugate_comp, Groupoid.comp_inv, conjugate_id]

private theorem target_pair {x y : G.Underlying} (r : x ⟶ y) (g : x ⟶ x) :
    G.targetLoop (G.pairOf r g) = G.loopOf (G.conjugate r g) := rfl

private theorem reverse_pair {x y : G.Underlying} (r : x ⟶ y) (g : x ⟶ x) :
    G.reverseArrow (G.pairOf r g) = G.pairOf (Groupoid.inv r) (G.conjugate r g) := rfl

private theorem unit_pair {x : G.Underlying} (g : x ⟶ x) :
    G.unitArrow (G.loopOf g) = G.pairOf (𝟙 x) g := by
  have h : G.source g.val = x := g.property.1
  exact Subtype.ext (Prod.ext (congrArg G.unit h) rfl)

private theorem composite_pair {x y z : G.Underlying} (r : x ⟶ y) (s : y ⟶ z)
    (g : x ⟶ x) (k : y ⟶ y)
    (h : G.targetLoop (G.pairOf r g) = G.sourceLoop (G.pairOf s k)) :
    G.compositeArrow ⟨(G.pairOf r g, G.pairOf s k), h⟩ = G.pairOf (r ≫ s) g := rfl

private theorem pair_surjective (p : G.InertiaArrow) :
    ∃ (x y : G.Underlying) (r : x ⟶ y) (g : x ⟶ x), G.pairOf r g = p := by
  refine ⟨G.source p.val.1, G.target p.val.1, ⟨p.val.1, rfl, rfl⟩,
    ⟨p.val.2.val, p.property.symm, p.val.2.property.symm.trans p.property.symm⟩, ?_⟩
  exact Subtype.ext (Prod.ext rfl (Subtype.ext rfl))


private theorem unit_target (g : G.Inertia) : G.targetLoop (G.unitArrow g) = g := by
  let x : G.Underlying := G.source g.val
  let l : x ⟶ x := ⟨g.val, rfl, g.property.symm⟩
  have h : G.loopOf l = g := rfl
  rw [← h, G.unit_pair l, G.target_pair, G.conjugate_id]

private theorem inverse_target (a : G.InertiaArrow) :
    G.targetLoop (G.reverseArrow a) = G.sourceLoop a := by
  obtain ⟨x, y, r, g, rfl⟩ := G.pair_surjective a
  rw [G.reverse_pair, G.target_pair, G.conjugate_inverse]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem comp_target (p : G.Pairs) :
    G.targetLoop (G.compositeArrow p) = G.targetLoop p.val.2 := by
  rcases p with ⟨⟨a, b⟩, h⟩
  obtain ⟨x, y, r, g, rfl⟩ := G.pair_surjective a
  let c := G.conjugate r g
  have hb : G.loopOf c = b.val.2 := (G.target_pair r g).symm.trans h
  have hby : G.source b.val.1 = y := b.property.trans
    ((congrArg (fun k : G.Inertia => G.source k.val) hb).symm.trans c.property.1)
  let z : G.Underlying := G.target b.val.1
  let s : y ⟶ z := ⟨b.val.1, hby, rfl⟩
  have hpair : G.pairOf s c = b := Subtype.ext (Prod.ext rfl hb)
  let q : G.Pairs := ⟨(G.pairOf r g, G.pairOf s c), G.target_pair r g⟩
  have hp : q = (⟨(G.pairOf r g, b), h⟩ : G.Pairs) :=
    Subtype.ext (Prod.ext rfl hpair)
  rw [← hp]
  change G.targetLoop (G.compositeArrow ⟨(G.pairOf r g, G.pairOf s c), _⟩) =
    G.targetLoop (G.pairOf s c)
  rw [G.composite_pair, G.target_pair, G.target_pair, G.conjugate_comp]

private theorem inertiaArrow_ext {a b : G.InertiaArrow}
    (hr : a.val.1 = b.val.1) (hg : a.val.2 = b.val.2) : a = b :=
  Subtype.ext (Prod.ext hr hg)

/-- The corrected topological inertia groupoid of E.6.3.6. In categorical
composition order the composite retains the loop at the first source. -/
def inertiaGroupoid : TopologicalGroupoid.{u} where
  objects := G.loopSpace
  arrows := G.inertiaArrowSpace
  source := G.sourceLoop
  target := G.targetLoop
  unit := G.unitArrow
  inverse := G.reverseArrow
  comp := G.compositeArrow
  source_unit _ := rfl
  target_unit := G.unit_target
  source_inv _ := rfl
  target_inv := G.inverse_target
  source_comp _ := rfl
  target_comp := G.comp_target
  unit_comp a := by
    refine G.inertiaArrow_ext ?_ rfl
    change G.comp ⟨(G.unit (G.source a.val.2.val), a.val.1), _⟩ = a.val.1
    trans G.comp ⟨(G.unit (G.source a.val.1), a.val.1), G.target_unit _⟩
    · exact congrArg G.comp (Subtype.ext (Prod.ext (congrArg G.unit a.property.symm) rfl))
    · exact G.unit_comp _
  comp_unit a := by
    refine G.inertiaArrow_ext ?_ rfl
    change G.comp ⟨(a.val.1, G.unit (G.source (G.targetLoop a).val)), _⟩ = a.val.1
    trans G.comp ⟨(a.val.1, G.unit (G.target a.val.1)), (G.source_unit _).symm⟩
    · exact congrArg G.comp (Subtype.ext (Prod.ext rfl (congrArg G.unit (G.conjugated_source a))))
    · exact G.comp_unit _
  inv_comp a := by
    refine G.inertiaArrow_ext ?_ rfl
    change G.comp ⟨(G.inverse a.val.1, a.val.1), _⟩ = G.unit (G.source (G.targetLoop a).val)
    exact (G.inv_comp _).trans (congrArg G.unit (G.conjugated_source a).symm)
  comp_inv a := by
    refine G.inertiaArrow_ext ?_ rfl
    change G.comp ⟨(a.val.1, G.inverse a.val.1), _⟩ = G.unit (G.source a.val.2.val)
    exact (G.comp_inv _).trans (congrArg G.unit a.property)
  assoc a b c hab hbc := by
    refine G.inertiaArrow_ext ?_ rfl
    exact G.assoc a.val.1 b.val.1 c.val.1
      (G.transport_composable ⟨(a, b), hab⟩)
      (G.transport_composable ⟨(b, c), hbc⟩)


/-- An arrow intertwines two loops precisely when the second loop is the
conjugate of the first by the transport arrow. -/
theorem targetLoop_eq_iff (p : G.InertiaArrow) (k : G.Inertia)
    (h : G.target p.val.1 = G.source k.val) :
    G.targetLoop p = k ↔
      G.firstComposite p = G.comp ⟨(p.val.1, k.val), h⟩ := by
  let x : G.Underlying := G.source p.val.1
  let y : G.Underlying := G.target p.val.1
  let r : x ⟶ y := ⟨p.val.1, rfl, rfl⟩
  let l : x ⟶ x := ⟨p.val.2.val, p.property.symm, p.val.2.property.symm.trans p.property.symm⟩
  let m : y ⟶ y := ⟨k.val, h.symm, k.property.symm.trans h.symm⟩
  change G.loopOf (G.conjugate r l) = G.loopOf m ↔ (l ≫ r).val = (r ≫ m).val
  constructor
  · intro he
    have hc : G.conjugate r l = m := Subtype.ext (congrArg (fun k : G.Inertia => k.val) he)
    have heq : l ≫ r = r ≫ m := by
      rw [← hc, conjugate, Groupoid.inv_eq_inv, IsIso.hom_inv_id_assoc]
    exact congrArg Subtype.val heq
  · intro he
    have heq : l ≫ r = r ≫ m := Subtype.ext he
    have hc : G.conjugate r l = m := by
      change Groupoid.inv r ≫ l ≫ r = m
      rw [heq, Groupoid.inv_eq_inv, IsIso.inv_hom_id_assoc]
    exact congrArg (G.loopOf) hc


/-- Continuous test-space points of a topological groupoid. -/
def Points (T : CGWH.{u}) := C(T.obj, G.objects.obj)

instance (T : CGWH.{u}) : CoeFun (G.Points T) (fun _ => T.obj → G.objects.obj) :=
  ⟨fun a => (show C(T.obj, G.objects.obj) from a)⟩

/-- A morphism of continuous points is a continuous family of arrows. -/
abbrev PointArrow {T : CGWH.{u}} (a b : G.Points T) :=
  {f : C(T.obj, G.arrows.obj) // (∀ t, G.source (f t) = a t) ∧ (∀ t, G.target (f t) = b t)}

set_option backward.isDefEq.respectTransparency false in
instance (T : CGWH.{u}) : Groupoid (G.Points T) where
  Hom := G.PointArrow
  id a := ⟨G.unit.comp a, fun t => G.source_unit _, fun t => G.target_unit _⟩
  comp f g := ⟨G.composeMaps f.val g.val (fun t => (f.property.2 t).trans (g.property.1 t).symm),
    fun t => (G.source_comp _).trans (f.property.1 t),
    fun t => (G.target_comp _).trans (g.property.2 t)⟩
  id_comp {a b} f := Subtype.ext (ContinuousMap.ext fun t => by
    trans G.comp ⟨(G.unit (G.source (f.val t)), f.val t), G.target_unit _⟩
    · exact congrArg G.comp (Subtype.ext (Prod.ext (congrArg G.unit (f.property.1 t).symm) rfl))
    · exact G.unit_comp _)
  comp_id {a b} f := Subtype.ext (ContinuousMap.ext fun t => by
    trans G.comp ⟨(f.val t, G.unit (G.target (f.val t))), (G.source_unit _).symm⟩
    · exact congrArg G.comp (Subtype.ext (Prod.ext rfl (congrArg G.unit (f.property.2 t).symm)))
    · exact G.comp_unit _)
  assoc f g h := Subtype.ext (ContinuousMap.ext fun t =>
    G.assoc (f.val t) (g.val t) (h.val t) _ _)
  inv f := ⟨G.inverse.comp f.val, fun t => (G.source_inv _).trans (f.property.2 t),
    fun t => (G.target_inv _).trans (f.property.1 t)⟩
  inv_comp f := Subtype.ext (ContinuousMap.ext fun t =>
    (G.inv_comp (f.val t)).trans (congrArg G.unit (f.property.2 t)))
  comp_inv f := Subtype.ext (ContinuousMap.ext fun t =>
    (G.comp_inv (f.val t)).trans (congrArg G.unit (f.property.1 t)))

private abbrev pointBase := Discrete (PUnit.{u+1})

/-- Regard the groupoid of points as based over a terminal category. -/
abbrev pointsBased (T : CGWH.{u}) : BasedCategory.{u,u} pointBase :=
  BasedCategory.ofFunctor ((Functor.const (G.Points T)).obj (Discrete.mk PUnit.unit))

private def pointedBase {T : CGWH.{u}} (a : G.inertiaGroupoid.Points T) : G.Points T :=
  G.loopBase.comp a

private def pointedLoop {T : CGWH.{u}} (a : G.inertiaGroupoid.Points T) :
    G.pointedBase a ⟶ G.pointedBase a :=
  (show G.PointArrow (G.pointedBase a) (G.pointedBase a) from ⟨(⟨Subtype.val, continuous_subtype_val⟩ : C(G.Inertia, G.arrows.obj)).comp a,
    fun _ => rfl, fun t => (a t).property.symm⟩)

set_option backward.isDefEq.respectTransparency false in
private noncomputable def intoPointInertia {T : CGWH.{u}} (a : G.inertiaGroupoid.Points T) :
    BasedInertia.Obj (G.pointsBased T) where
  point := G.pointedBase a
  loop := {
    hom := G.pointedLoop a
    inv := @Groupoid.inv (G.Points T) (inferInstance : Groupoid (G.Points T)) _ _ (G.pointedLoop a)
    hom_inv_id := @Groupoid.comp_inv (G.Points T) (inferInstance : Groupoid (G.Points T)) _ _ _
    inv_hom_id := @Groupoid.inv_comp (G.Points T) (inferInstance : Groupoid (G.Points T)) _ _ _ }
  vertical := IsHomLift.of_fac' _ _ _ rfl rfl
    (Subsingleton.elim _ _)

private def outOfPointInertia {T : CGWH.{u}} (a : BasedInertia.Obj (G.pointsBased T)) :
    G.inertiaGroupoid.Points T :=
  let l : G.PointArrow a.point a.point := a.loop.hom
  ⟨fun t => ⟨l.val t, (l.property.1 t).trans (l.property.2 t).symm⟩,
    l.val.continuous.subtype_mk _⟩

set_option backward.isDefEq.respectTransparency false in
private def pointTransport {T : CGWH.{u}} {a b : G.inertiaGroupoid.Points T}
    (r : G.inertiaGroupoid.PointArrow a b) :
    G.pointedBase a ⟶ G.pointedBase b :=
  (show G.PointArrow (G.pointedBase a) (G.pointedBase b) from ⟨G.transportArrow.comp r.val, fun t =>
    (r.val t).property.trans (congrArg (fun k : G.Inertia => G.source k.val) (r.property.1 t)),
    fun t => (G.conjugated_source (r.val t)).symm.trans
      (congrArg (fun k : G.Inertia => G.source k.val) (r.property.2 t))⟩)

set_option backward.isDefEq.respectTransparency false in
private theorem pointInertia_comp (T : CGWH.{u}) (a b : G.inertiaGroupoid.Points T)
    (r : G.inertiaGroupoid.PointArrow a b) :
    (G.pointedLoop a : G.pointedBase a ⟶ G.pointedBase a) ≫ G.pointTransport r =
      G.pointTransport r ≫ G.pointedLoop b := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro t
  let p := r.val t
  have h₁ : G.sourceLoop p = a t := r.property.1 t
  have h₂ : G.targetLoop p = b t := r.property.2 t
  have ht : G.target p.val.1 = G.source (b t).val :=
    (G.conjugated_source p).symm.trans
      (congrArg (fun k : G.Inertia => G.source k.val) h₂)
  have h := (G.targetLoop_eq_iff p (b t) ht).mp h₂
  change G.comp ⟨((a t).val, p.val.1), _⟩ = G.comp ⟨(p.val.1, (b t).val), ht⟩
  refine Eq.trans ?_ h
  exact congrArg G.comp (Subtype.ext (Prod.ext
    (congrArg Subtype.val h₁.symm) rfl))

set_option backward.isDefEq.respectTransparency false in
/-- At each test space, taking points of the conjugation groupoid gives
the inertia category of the groupoid of continuous points. -/
noncomputable def inertiaPointsComparison (T : CGWH.{u}) :
    G.inertiaGroupoid.Points T ⥤ BasedInertia.Obj (G.pointsBased T) where
  obj := G.intoPointInertia
  map {a b} r := ⟨G.pointTransport r, (G.pointInertia_comp T a b r).symm⟩
  map_id _ := BasedInertia.Arrow.ext rfl
  map_comp _ _ := BasedInertia.Arrow.ext rfl


private def pointInertiaLoopMap {T : CGWH.{u}} (a : BasedInertia.Obj (G.pointsBased T)) :
    C(T.obj, G.arrows.obj) :=
  (show G.PointArrow a.point a.point from a.loop.hom).val

set_option backward.isDefEq.respectTransparency false in
private theorem pointInertiaObj_ext {T : CGWH.{u}} {a b : BasedInertia.Obj (G.pointsBased T)}
    (hp : a.point = b.point) (hl : G.pointInertiaLoopMap a = G.pointInertiaLoopMap b) : a = b := by
  rcases a with ⟨a, ar, ha⟩
  rcases b with ⟨b, br, hb⟩
  change a = b at hp
  subst b
  have he : ar = br := Iso.ext (Subtype.ext hl)
  subst br
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem inertiaPointsComparison_bijective (T : CGWH.{u}) :
    Function.Bijective (G.inertiaPointsComparison T).obj := by
  have hinv (a : G.inertiaGroupoid.Points T) : G.outOfPointInertia (G.intoPointInertia a) = a := by
    apply ContinuousMap.ext
    intro t
    exact Subtype.ext rfl
  refine ⟨fun a b h => (hinv a).symm.trans ((congrArg (G.outOfPointInertia) h).trans (hinv b)), ?_⟩
  intro a
  refine ⟨G.outOfPointInertia a, G.pointInertiaObj_ext ?_ rfl⟩
  change (G.pointedBase (G.outOfPointInertia a) : C(T.obj, G.objects.obj)) = a.point
  apply ContinuousMap.ext
  exact (show G.PointArrow a.point a.point from a.loop.hom).property.1

set_option backward.isDefEq.respectTransparency false in
private def pointInertiaPreimage {T : CGWH.{u}} {a b : G.inertiaGroupoid.Points T}
    (r : G.intoPointInertia a ⟶ G.intoPointInertia b) : a ⟶ b := by
  let m : G.PointArrow (G.pointedBase a) (G.pointedBase b) := r.hom
  let aa : C(T.obj, G.Inertia) := a
  let p : C(T.obj, G.InertiaArrow) :=
    ⟨fun t => ⟨(m.val t, a t), m.property.1 t⟩,
      (kelleyPair m.val aa).continuous.subtype_mk _⟩
  refine (show G.inertiaGroupoid.PointArrow a b from ⟨p, fun _ => rfl, ?_⟩)
  intro t
  apply (G.targetLoop_eq_iff (p t) (b t) (m.property.2 t)).mpr
  have hs := congrArg (fun n : G.PointArrow (G.pointedBase a) (G.pointedBase b) => n.val t)
    r.square.symm
  exact hs

set_option backward.isDefEq.respectTransparency false in
def inertiaPointsComparison_fullyFaithful (T : CGWH.{u}) :
    (G.inertiaPointsComparison T).FullyFaithful where
  preimage r := G.pointInertiaPreimage r
  map_preimage r := BasedInertia.Arrow.ext (Subtype.ext rfl)
  preimage_map {a b} r := by
    apply Subtype.ext
    apply ContinuousMap.ext
    intro t
    exact G.inertiaArrow_ext rfl (r.property.1 t).symm

/-- The comparison on each test space is a strict isomorphism of categories. -/
noncomputable def inertiaPointsIso (T : CGWH.{u}) :
    Cat.of (G.inertiaGroupoid.Points T) ≅ Cat.of (BasedInertia.Obj (G.pointsBased T)) :=
  StrictCatPullback.isoOfFullyFaithfulBijective (G.inertiaPointsComparison T).toCatHom
    (G.inertiaPointsComparison_fullyFaithful T) (G.inertiaPointsComparison_bijective T)


set_option backward.isDefEq.respectTransparency false in
/-- The pullback of a point or a continuous family of arrows is composition
with the map of test spaces. -/
def restrictPoints {S T : CGWH.{u}} (f : C(S.obj, T.obj)) : G.Points T ⥤ G.Points S where
  obj a := (show C(T.obj, G.objects.obj) from a).comp f
  map {a b} r :=
    (show G.PointArrow ((show C(T.obj, G.objects.obj) from a).comp f)
        ((show C(T.obj, G.objects.obj) from b).comp f) from
      ⟨r.val.comp f, fun t => r.property.1 (f t), fun t => r.property.2 (f t)⟩)
  map_id _ := Subtype.ext rfl
  map_comp _ _ := Subtype.ext rfl

set_option backward.isDefEq.respectTransparency false in
/-- Restriction of inertia points pulls back the object and its
automorphism together. -/
def restrictInertiaPoints {S T : CGWH.{u}} (f : C(S.obj, T.obj)) :
    BasedInertia.Obj (G.pointsBased T) ⥤ BasedInertia.Obj (G.pointsBased S) where
  obj a := {
    point := (G.restrictPoints f).obj a.point
    loop := (G.restrictPoints f).mapIso a.loop
    vertical := IsHomLift.of_fac' _ _ _ rfl rfl (Subsingleton.elim _ _) }
  map {a b} r := ⟨(G.restrictPoints f).map r.hom, by
    change (G.restrictPoints f).map r.hom ≫ (G.restrictPoints f).map b.loop.hom =
      (G.restrictPoints f).map a.loop.hom ≫ (G.restrictPoints f).map r.hom
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
    exact congrArg (G.restrictPoints f).map r.square⟩
  map_id _ := BasedInertia.Arrow.ext ((G.restrictPoints f).map_id _)
  map_comp _ _ := BasedInertia.Arrow.ext ((G.restrictPoints f).map_comp _ _)

set_option backward.isDefEq.respectTransparency false in
/-- The test-space comparison commutes with every restriction map. -/
theorem inertiaPointsComparison_natural {S T : CGWH.{u}} (f : C(S.obj, T.obj)) :
    G.inertiaGroupoid.restrictPoints f ⋙ G.inertiaPointsComparison S =
      G.inertiaPointsComparison T ⋙ G.restrictInertiaPoints f := by
  have ho (a : G.inertiaGroupoid.Points T) :
      (G.inertiaPointsComparison S).obj ((G.inertiaGroupoid.restrictPoints f).obj a) =
        (G.restrictInertiaPoints f).obj ((G.inertiaPointsComparison T).obj a) :=
    G.pointInertiaObj_ext rfl rfl
  refine CategoryTheory.Functor.ext ho ?_
  intro a b r
  apply BasedInertia.Arrow.ext
  have ha : congrArg BasedInertia.Obj.point (ho a) = rfl := Subsingleton.elim _ _
  have hb : congrArg BasedInertia.Obj.point (ho b).symm = rfl := Subsingleton.elim _ _
  change ((G.inertiaPointsComparison S).map ((G.inertiaGroupoid.restrictPoints f).map r)).hom =
    (BasedInertia.forget (G.pointsBased S)).map
      (eqToHom (ho a) ≫ (G.restrictInertiaPoints f).map ((G.inertiaPointsComparison T).map r) ≫
        eqToHom (ho b).symm)
  simp only [CategoryTheory.Functor.map_comp, eqToHom_map]
  change _ = eqToHom (congrArg BasedInertia.Obj.point (ho a)) ≫ _ ≫
    eqToHom (congrArg BasedInertia.Obj.point (ho b).symm)
  rw [ha, hb]
  change _ = (𝟙 _) ≫ ((G.restrictPoints f).map (G.pointTransport r)) ≫ (𝟙 _)
  simp only [Category.id_comp, Category.comp_id]
  rfl


/-- Forget the loop and retain its base point and the transport arrow. -/
def inertiaProjection : G.inertiaGroupoid ⟶ G where
  objectMap := G.loopBase
  arrowMap := G.transportArrow
  mapSource p := p.property
  mapTarget p := (G.conjugated_source p).symm
  mapUnit _ := rfl
  mapInverse _ := rfl
  mapComp _ _ _ := rfl

private def identityLoop : C(G.objects.obj, G.Inertia) :=
  ⟨fun x => ⟨G.unit x, (G.source_unit x).trans (G.target_unit x).symm⟩,
    G.unit.continuous.subtype_mk _⟩

private def identityTransport : C(G.arrows.obj, G.InertiaArrow) :=
  ⟨fun r => ⟨(r, G.identityLoop (G.source r)), (G.source_unit _).symm⟩,
    (kelleyPair (ContinuousMap.id _) (G.identityLoop.comp G.source)).continuous.subtype_mk _⟩

private theorem uniqueLoop (h : Injective (fun a => (G.source a, G.target a)))
    (g : G.Inertia) (x : G.objects.obj) (hx : G.source g.val = x) : G.identityLoop x = g := by
  apply Subtype.ext
  apply h
  exact Prod.ext ((G.source_unit x).trans hx.symm)
    ((G.target_unit x).trans (g.property.symm.trans hx).symm)

set_option backward.isDefEq.respectTransparency false in
/-- If the source and target determine the arrow, the topological inertia
groupoid is canonically isomorphic to the original groupoid. -/
def inertiaIsoOfInjectiveEndpoints (h : Injective (fun a => (G.source a, G.target a))) :
    G.inertiaGroupoid ≅ G where
  hom := G.inertiaProjection
  inv := {
    objectMap := G.identityLoop
    arrowMap := G.identityTransport
    mapSource _ := rfl
    mapTarget a := (G.uniqueLoop h _ _ (G.conjugated_source (G.identityTransport a))).symm
    mapUnit x := G.inertiaArrow_ext (congrArg G.unit (G.source_unit x).symm)
      (congrArg G.identityLoop (G.source_unit x))
    mapInverse a := G.inertiaArrow_ext rfl
      (G.uniqueLoop h _ _ ((G.conjugated_source (G.identityTransport a)).trans (G.source_inv a).symm))
    mapComp a b hab := G.inertiaArrow_ext rfl (congrArg G.identityLoop (G.source_comp ⟨(a,b), hab⟩)) }
  hom_inv_id := by
    apply Hom.ext
    · exact ContinuousMap.ext fun x => G.uniqueLoop h x _ rfl
    · apply ContinuousMap.ext
      intro p
      exact G.inertiaArrow_ext rfl (G.uniqueLoop h p.val.2 _ p.property.symm)
  inv_hom_id := by
    apply Hom.ext
    · exact ContinuousMap.ext fun x => G.source_unit x
    · rfl

end Masullo.TopologicalGroupoid
