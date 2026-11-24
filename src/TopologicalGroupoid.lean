import CompactlyGenerated
import Mathlib.Algebra.Group.MinimalAxioms
import Mathlib.Topology.Compactness.LocallyCompact

open CategoryTheory CategoryTheory.Limits Function Set Topology TopologicalSpace

namespace Masullo

universe u

/-- Pairs of composable arrows, with the topology inherited from the Kelley product. -/
abbrev ComposableArrows {X R : Type u} [TopologicalSpace R] (s t : R → X) :=
  {p : Kelley (R × R) // t p.1 = s p.2}

/-- A groupoid internal to CGWH. Composition follows categorical left-to-right order. -/
structure TopologicalGroupoid where
  objects : CGWH.{u}
  arrows : CGWH.{u}
  source : C(arrows.obj, objects.obj)
  target : C(arrows.obj, objects.obj)
  unit : C(objects.obj, arrows.obj)
  inverse : C(arrows.obj, arrows.obj)
  comp : C(ComposableArrows source.toFun target.toFun, arrows.obj)
  source_unit : ∀ x, source (unit x) = x
  target_unit : ∀ x, target (unit x) = x
  source_inv : ∀ a, source (inverse a) = target a
  target_inv : ∀ a, target (inverse a) = source a
  source_comp : ∀ p : ComposableArrows source.toFun target.toFun,
    source (comp p) = source p.val.1
  target_comp : ∀ p : ComposableArrows source.toFun target.toFun,
    target (comp p) = target p.val.2
  unit_comp : ∀ a, comp ⟨(unit (source a), a), target_unit _⟩ = a
  comp_unit : ∀ a, comp ⟨(a, unit (target a)), (source_unit _).symm⟩ = a
  inv_comp : ∀ a, comp ⟨(inverse a, a), target_inv _⟩ = unit (target a)
  comp_inv : ∀ a, comp ⟨(a, inverse a), (source_inv _).symm⟩ = unit (source a)
  assoc : ∀ (a b c : arrows.obj) (hab : target a = source b) (hbc : target b = source c),
    comp ⟨(comp ⟨(a, b), hab⟩, c), (target_comp ⟨(a, b), hab⟩).trans hbc⟩ =
      comp ⟨(a, comp ⟨(b, c), hbc⟩), hab.trans (source_comp ⟨(b, c), hbc⟩).symm⟩

namespace TopologicalGroupoid

/-- Lemma E.4.2.5. The continuous identity map splits both structure maps. -/
theorem unit_closed_and_projections_quotient (G : TopologicalGroupoid.{u}) :
    IsClosedEmbedding G.unit ∧ IsQuotientMap G.source ∧ IsQuotientMap G.target := by
  have hs := cgwh_section_closed_and_quotient G.arrows.property G.source G.unit G.source_unit
  have ht := cgwh_section_closed_and_quotient G.arrows.property G.target G.unit G.target_unit
  exact ⟨hs.1, hs.2, ht.2⟩

/-- Lemma E.4.2.6. The space of composable arrows is a closed CGWH subspace. -/
theorem composable_closed_cgwh (G : TopologicalGroupoid.{u}) :
    IsClosed {p : Kelley (G.arrows.obj × G.arrows.obj) | G.target p.1 = G.source p.2} ∧
    CompactlyGeneratedSpace (ComposableArrows G.source G.target) ∧
    WeaklyHausdorff (ComposableArrows G.source G.target) := by
  have hc := CGWH.fibreSubspace_isClosed (CGWH.map (X := G.arrows) (Y := G.objects) G.target)
    (CGWH.map (X := G.arrows) (Y := G.objects) G.source)
  exact ⟨hc, closed_compactlyGenerated hc, CGWH.fibreSubspace_weaklyHausdorff
    (CGWH.map (X := G.arrows) (Y := G.objects) G.target)
    (CGWH.map (X := G.arrows) (Y := G.objects) G.source)⟩

def composablePullback (G : TopologicalGroupoid.{u}) : LimitCone (cospan
    (CGWH.map (X := G.arrows) (Y := G.objects) G.target) (CGWH.map G.source)) :=
  CGWH.fibreSubspaceLimit _ _

/-- Arrows whose source and target both equal the specified object. -/
abbrev Isotropy (G : TopologicalGroupoid.{u}) (x : G.objects.obj) :=
  {a : G.arrows.obj // G.source a = x ∧ G.target a = x}

theorem isotropy_isClosed (G : TopologicalGroupoid.{u}) (x : G.objects.obj) :
    IsClosed {a : G.arrows.obj | G.source a = x ∧ G.target a = x} :=
  ((weaklyHausdorff_closed_singleton G.objects.property x).preimage G.source.continuous).inter
    ((weaklyHausdorff_closed_singleton G.objects.property x).preimage G.target.continuous)

instance (G : TopologicalGroupoid.{u}) (x : G.objects.obj) :
    CompactlyGeneratedSpace (G.Isotropy x) := closed_compactlyGenerated (G.isotropy_isClosed x)

theorem isotropy_weaklyHausdorff (G : TopologicalGroupoid.{u}) (x : G.objects.obj) :
    WeaklyHausdorff (G.Isotropy x) := weaklyHausdorff_subspace G.arrows.property _

instance (G : TopologicalGroupoid.{u}) (x : G.objects.obj) : One (G.Isotropy x) :=
  ⟨⟨G.unit x, G.source_unit x, G.target_unit x⟩⟩

instance (G : TopologicalGroupoid.{u}) (x : G.objects.obj) : Mul (G.Isotropy x) where
  mul a b := ⟨G.comp ⟨(a, b), a.property.2.trans b.property.1.symm⟩,
    (G.source_comp _).trans a.property.1, (G.target_comp _).trans b.property.2⟩

instance (G : TopologicalGroupoid.{u}) (x : G.objects.obj) : Inv (G.Isotropy x) where
  inv a := ⟨G.inverse a, (G.source_inv _).trans a.property.2, (G.target_inv _).trans a.property.1⟩

instance (G : TopologicalGroupoid.{u}) (x : G.objects.obj) : Group (G.Isotropy x) :=
  Group.ofLeftAxioms
    (fun a b c => Subtype.ext (G.assoc a b c
      (a.property.2.trans b.property.1.symm) (b.property.2.trans c.property.1.symm)))
    (fun a => Subtype.ext (show G.comp ⟨(G.unit x, a.val),
      (G.target_unit x).trans a.property.1.symm⟩ = a.val from by
        simpa only [a.property.1] using G.unit_comp a.val))
    (fun a => Subtype.ext (show G.comp ⟨(G.inverse a.val, a.val), G.target_inv a.val⟩ =
      G.unit x from by simpa only [a.property.2] using G.inv_comp a.val))

instance (G : TopologicalGroupoid.{u}) (x : G.objects.obj) : ContinuousInv (G.Isotropy x) where
  continuous_inv := (G.inverse.continuous.comp continuous_subtype_val).subtype_mk _

theorem continuous_isotropy_mul_of_product (G : TopologicalGroupoid.{u}) (x : G.objects.obj)
    [CompactlyGeneratedSpace (G.Isotropy x × G.Isotropy x)] :
    Continuous (fun p : G.Isotropy x × G.Isotropy x => p.1 * p.2) := by
  have hp : Continuous (fun p : G.Isotropy x × G.Isotropy x =>
      (p.1.val, p.2.val)) := continuous_subtype_val.prodMap continuous_subtype_val
  have hk := continuous_to_Kelley (Y := G.arrows.obj × G.arrows.obj) hp
  exact (G.comp.continuous.comp (hk.subtype_mk _)).subtype_mk _

/-- Isotropy multiplication is continuous on the internal product in CGWH. -/
theorem continuous_isotropy_kelley_mul (G : TopologicalGroupoid.{u}) (x : G.objects.obj) :
    Continuous (fun p : Kelley (G.Isotropy x × G.Isotropy x) => p.1 * p.2) := by
  have hp : Continuous (fun p : Kelley (G.Isotropy x × G.Isotropy x) => (p.1.val, p.2.val)) :=
    (continuous_subtype_val.prodMap continuous_subtype_val).comp
      (continuous_Kelley_forget (X := G.Isotropy x × G.Isotropy x))
  have hk := continuous_to_Kelley (Y := G.arrows.obj × G.arrows.obj) hp
  exact (G.comp.continuous.comp (hk.subtype_mk _)).subtype_mk _

/-- Corrected Lemmas E.4.2.7 and E.6.3.9. The isotropy group is a
closed CGWH subspace, with its group operations continuous in CGWH.
The ordinary topological group conclusion holds when its square is compactly generated. -/
theorem isotropy_group_topology (G : TopologicalGroupoid.{u}) (x : G.objects.obj) :
    IsClosed {a : G.arrows.obj | G.source a = x ∧ G.target a = x} ∧
    CompactlyGeneratedSpace (G.Isotropy x) ∧ WeaklyHausdorff (G.Isotropy x) ∧
    Continuous (Inv.inv : G.Isotropy x → G.Isotropy x) ∧
    Continuous (fun p : Kelley (G.Isotropy x × G.Isotropy x) => p.1 * p.2) ∧
    (CompactlyGeneratedSpace (G.Isotropy x × G.Isotropy x) → IsTopologicalGroup (G.Isotropy x)) := by
  refine ⟨G.isotropy_isClosed x, inferInstance, G.isotropy_weaklyHausdorff x, continuous_inv,
    G.continuous_isotropy_kelley_mul x, fun h => ?_⟩
  letI := h
  exact { continuous_mul := G.continuous_isotropy_mul_of_product x }

/-- Lemma E.6.3.10. With locally compact Hausdorff arrow space, the
isotropy groups are locally compact Hausdorff topological groups. -/
theorem locallyCompact_isotropy (G : TopologicalGroupoid.{u}) (x : G.objects.obj)
    [LocallyCompactSpace G.arrows.obj] [T2Space G.arrows.obj] :
    LocallyCompactSpace (G.Isotropy x) ∧ T2Space (G.Isotropy x) ∧ IsTopologicalGroup (G.Isotropy x) := by
  letI : LocallyCompactSpace (G.Isotropy x) :=
    (G.isotropy_isClosed x).isClosedEmbedding_subtypeVal.locallyCompactSpace
  letI : CompactlyGeneratedSpace (G.Isotropy x × G.Isotropy x) :=
    (locallyCompact_compactlyGenerated_and_prod (X := G.Isotropy x) (Y := G.Isotropy x)).2
  exact ⟨inferInstance, inferInstance, { continuous_mul := G.continuous_isotropy_mul_of_product x }⟩

/-- The relative inertia space is the ordinary topological equalizer. -/
abbrev Inertia (G : TopologicalGroupoid.{u}) := {a : G.arrows.obj // G.source a = G.target a}

theorem inertia_isClosed (G : TopologicalGroupoid.{u}) :
    IsClosed {a : G.arrows.obj | G.source a = G.target a} :=
  cgwh_isClosed_equalizer G.objects.property G.source G.target

private abbrev inertiaObject (G : TopologicalGroupoid.{u}) : CGWH.{u} := by
  letI : CompactlyGeneratedSpace G.Inertia := closed_compactlyGenerated G.inertia_isClosed
  exact CGWH.of (X := G.Inertia)
    (weaklyHausdorff_subspace G.arrows.property {a | G.source a = G.target a})

private theorem cgwh_ext {X Y : CGWH.{u}} {f g : X ⟶ Y} (h : ∀ x, f.hom x = g.hom x) : f = g :=
  cgwhForget.map_injective (ConcreteCategory.hom_ext _ _ h)

/-- Lemma E.6.3.5. The closed inertia subspace already computes the equalizer
in both CGWH and ordinary spaces. -/
abbrev inertiaFork (G : TopologicalGroupoid.{u}) :
    Fork (CGWH.map (X := G.arrows) (Y := G.objects) G.source) (CGWH.map G.target) :=
  Fork.ofι (CGWH.map (X := G.inertiaObject) (Y := G.arrows)
    (⟨Subtype.val, continuous_subtype_val⟩ : C(G.Inertia, G.arrows.obj)))
    (cgwh_ext fun x => show G.source x.val = G.target x.val from x.property)

def inertiaFork_isLimit (G : TopologicalGroupoid.{u}) : IsLimit G.inertiaFork := by
  refine Fork.IsLimit.mk' _ fun c => ?_
  have h (x : c.pt.obj) : G.source (c.ι.hom x) = G.target (c.ι.hom x) :=
    ConcreteCategory.congr_hom (congrArg InducedCategory.Hom.hom c.condition) x
  let l : c.pt ⟶ G.inertiaObject := CGWH.map ⟨fun x => ⟨c.ι.hom x, h x⟩,
    c.ι.hom.hom.hom.continuous.subtype_mk _⟩
  refine ⟨l, cgwh_ext (fun _ => rfl), ?_⟩
  intro m hm
  apply cgwh_ext
  intro x
  apply Subtype.ext
  have hx := ConcreteCategory.congr_hom (congrArg InducedCategory.Hom.hom hm) x
  exact hx

def topologicalInertiaFork (G : TopologicalGroupoid.{u}) :
    Fork (TopCat.ofHom G.source) (TopCat.ofHom G.target) :=
  Fork.ofι (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ : C(G.Inertia, G.arrows.obj)))
    (ConcreteCategory.hom_ext _ _ fun x => x.property)

def topologicalInertiaFork_isLimit (G : TopologicalGroupoid.{u}) :
    IsLimit G.topologicalInertiaFork := by
  refine Fork.IsLimit.mk' _ fun c => ?_
  have h (x : c.pt) : G.source (c.ι x) = G.target (c.ι x) :=
    ConcreteCategory.congr_hom c.condition x
  let l : c.pt ⟶ TopCat.of G.Inertia := TopCat.ofHom ⟨fun x => ⟨c.ι x, h x⟩,
    c.ι.hom.continuous.subtype_mk _⟩
  exact ⟨l, ConcreteCategory.hom_ext _ _ fun _ => rfl,
    fun hm => ConcreteCategory.hom_ext _ _ fun x => Subtype.ext (ConcreteCategory.congr_hom hm x)⟩

/-- The equalizer agrees with the pullback of the diagonal in ordinary spaces. -/
def inertiaTopologicalPullbackHomeomorph (G : TopologicalGroupoid.{u}) : G.Inertia ≃ₜ
    {p : G.objects.obj × G.arrows.obj // (p.1, p.1) = (G.source p.2, G.target p.2)} where
  toFun a := ⟨(G.source a, a), Prod.ext rfl a.property⟩
  invFun p := ⟨p.val.2, (congrArg Prod.fst p.property).symm.trans (congrArg Prod.snd p.property)⟩
  left_inv _ := rfl
  right_inv p := Subtype.ext (Prod.ext (congrArg Prod.fst p.property).symm rfl)
  continuous_toFun := (((G.source.continuous.comp continuous_subtype_val).prodMk
    continuous_subtype_val).subtype_mk _)
  continuous_invFun := (continuous_snd.comp continuous_subtype_val).subtype_mk _

/-- A continuous functor between internal groupoids. -/
@[ext]
structure Hom (G H : TopologicalGroupoid.{u}) where
  objectMap : C(G.objects.obj, H.objects.obj)
  arrowMap : C(G.arrows.obj, H.arrows.obj)
  mapSource : ∀ a, H.source (arrowMap a) = objectMap (G.source a)
  mapTarget : ∀ a, H.target (arrowMap a) = objectMap (G.target a)
  mapUnit : ∀ x, arrowMap (G.unit x) = H.unit (objectMap x)
  mapInverse : ∀ a, arrowMap (G.inverse a) = H.inverse (arrowMap a)
  mapComp : ∀ (a b : G.arrows.obj) (h : G.target a = G.source b),
    arrowMap (G.comp ⟨(a, b), h⟩) = H.comp ⟨(arrowMap a, arrowMap b),
      (mapTarget a).trans ((congrArg objectMap h).trans (mapSource b).symm)⟩

private def identity (G : TopologicalGroupoid.{u}) : Hom G G where
  objectMap := ContinuousMap.id _
  arrowMap := ContinuousMap.id _
  mapSource _ := rfl
  mapTarget _ := rfl
  mapUnit _ := rfl
  mapInverse _ := rfl
  mapComp _ _ _ := rfl

private def composition {A B C' : TopologicalGroupoid.{u}} (f : Hom A B) (g : Hom B C') : Hom A C' where
  objectMap := g.objectMap.comp f.objectMap
  arrowMap := g.arrowMap.comp f.arrowMap
  mapSource a := (g.mapSource _).trans (congrArg g.objectMap (f.mapSource a))
  mapTarget a := (g.mapTarget _).trans (congrArg g.objectMap (f.mapTarget a))
  mapUnit a := (congrArg g.arrowMap (f.mapUnit a)).trans (g.mapUnit _)
  mapInverse a := (congrArg g.arrowMap (f.mapInverse a)).trans (g.mapInverse _)
  mapComp a b h := (congrArg g.arrowMap (f.mapComp a b h)).trans (g.mapComp _ _ _)

instance : Category TopologicalGroupoid.{u} where
  Hom := Hom
  id := identity
  comp := composition

/-- The constant groupoid uses the object space itself to represent its diagonal. -/
abbrev constant (X : CGWH.{u}) : TopologicalGroupoid.{u} where
  objects := X
  arrows := X
  source := ContinuousMap.id _
  target := ContinuousMap.id _
  inverse := ContinuousMap.id _
  unit := ContinuousMap.id _
  comp := ⟨fun p => p.val.1, continuous_fst.comp
    ((continuous_Kelley_forget (X := X.obj × X.obj)).comp continuous_subtype_val)⟩
  source_unit _ := rfl
  target_unit _ := rfl
  source_inv _ := rfl
  target_inv _ := rfl
  source_comp _ := rfl
  target_comp p := p.property
  unit_comp _ := rfl
  comp_unit _ := rfl
  inv_comp _ := rfl
  comp_inv _ := rfl
  assoc _ _ _ _ _ := rfl

/-- The functor of Lemma E.4.2.11. -/
def constantFunctor : CGWH.{u} ⥤ TopologicalGroupoid.{u} where
  obj := constant
  map {X Y} f := {
    objectMap := f.hom.hom.hom
    arrowMap := f.hom.hom.hom
    mapSource := fun _ => rfl
    mapTarget := fun _ => rfl
    mapUnit := fun _ => rfl
    mapInverse := fun _ => rfl
    mapComp := fun _ _ _ => rfl }

def constantFunctor_fullyFaithful : constantFunctor.{u}.FullyFaithful where
  preimage f := CGWH.map f.objectMap
  map_preimage f := by
    apply Hom.ext
    · rfl
    · exact ContinuousMap.ext (fun x => (f.mapUnit x).symm)
  preimage_map _ := rfl

end TopologicalGroupoid

end Masullo
