import ActionGroupoid
import TopologicalGroupoidTwoCategory

open CategoryTheory Function Set Topology TopologicalSpace

namespace Masullo.TopologicalGroupoid

universe u

private def objectSquare (X : CGWH.{u}) : CGWH.{u} :=
  CGWH.of (X := Kelley (X.obj × X.obj)) (weaklyHausdorff_kelleyProduct X.property X.property)

private def endpoints (G : TopologicalGroupoid.{u}) : G.arrows ⟶ objectSquare G.objects :=
  CGWH.map (kelleyPair G.source G.target)

private def squareMap {W X : CGWH.{u}} (q : C(W.obj, X.obj)) : objectSquare W ⟶ objectSquare X :=
  CGWH.map (kelleyPair
    ⟨fun p ↦ q p.1, q.continuous.comp (continuous_fst.comp continuous_Kelley_forget)⟩
    ⟨fun p ↦ q p.2, q.continuous.comp (continuous_snd.comp continuous_Kelley_forget)⟩)

private abbrev endpointMap {G H : TopologicalGroupoid.{u}} (f : G ⟶ H) :=
  squareMap f.objectMap

/-- The pullback defining full faithfulness of a continuous groupoid functor. -/
abbrev ArrowComparisonSpace {G H : TopologicalGroupoid.{u}} (f : G ⟶ H) :=
  CGWH.FibreSubspace (endpointMap f) (endpoints H)

/-- The endpoint pullback as a test space. -/
def arrowComparisonObject {G H : TopologicalGroupoid.{u}} (f : G ⟶ H) : CGWH.{u} :=
  CGWH.of (X := ArrowComparisonSpace f) (CGWH.fibreSubspace_weaklyHausdorff _ _)

/-- Send a source arrow to its two endpoints and its image. -/
def arrowComparison {G H : TopologicalGroupoid.{u}} (f : G ⟶ H) :
    C(G.arrows.obj, ArrowComparisonSpace f) :=
  ⟨fun a ↦ ⟨((G.source a, G.target a), f.arrowMap a),
    Prod.ext (f.mapSource a).symm (f.mapTarget a).symm⟩,
    (kelleyPair (kelleyPair G.source G.target) f.arrowMap).continuous.subtype_mk _⟩

/-- Standard Morita equivalences use the source-to-pullback comparison and
the manuscript's quotient-map meaning of submersion. -/
def IsStandardMorita {G H : TopologicalGroupoid.{u}} (f : G ⟶ H) : Prop :=
  IsQuotientMap f.objectMap ∧
    ∃ e : G.arrows.obj ≃ₜ ArrowComparisonSpace f, ∀ a, e a = arrowComparison f a

section ChangeOfObjects

variable {G : TopologicalGroupoid.{u}} {W : CGWH.{u}} (q : C(W.obj, G.objects.obj))

/-- A refined arrow consists of lifted endpoints and an arrow with their images as its endpoints. -/
abbrev RefinedArrow := CGWH.FibreSubspace (squareMap q) (endpoints G)

private instance : CompactlyGeneratedSpace (RefinedArrow q) :=
  closed_compactlyGenerated (CGWH.fibreSubspace_isClosed (squareMap q) (endpoints G))

private def refinedArrowSpace : CGWH.{u} :=
  CGWH.of (X := RefinedArrow q) (CGWH.fibreSubspace_weaklyHausdorff (squareMap q) (endpoints G))

private def refinedEnds : C(RefinedArrow q, (objectSquare W).obj) :=
  ⟨fun a ↦ a.val.1, continuous_fst.comp (continuous_Kelley_forget.comp continuous_subtype_val)⟩

private def refinedUnderlying : C(RefinedArrow q, G.arrows.obj) :=
  ⟨fun a ↦ a.val.2, continuous_snd.comp (continuous_Kelley_forget.comp continuous_subtype_val)⟩

private def refinedSource : C(RefinedArrow q, W.obj) :=
  ⟨fun a ↦ a.val.1.1, continuous_fst.comp (continuous_Kelley_forget.comp (refinedEnds q).continuous)⟩

private def refinedTarget : C(RefinedArrow q, W.obj) :=
  ⟨fun a ↦ a.val.1.2, continuous_snd.comp (continuous_Kelley_forget.comp (refinedEnds q).continuous)⟩

private theorem refined_source (a : RefinedArrow q) : q a.val.1.1 = G.source a.val.2 :=
  congrArg Prod.fst a.property

private theorem refined_target (a : RefinedArrow q) : q a.val.1.2 = G.target a.val.2 :=
  congrArg Prod.snd a.property

private def refinedUnit : C(W.obj, RefinedArrow q) :=
  ⟨fun x ↦ ⟨((x, x), G.unit (q x)), Prod.ext (G.source_unit _).symm (G.target_unit _).symm⟩,
    (kelleyPair (kelleyPair (ContinuousMap.id _) (ContinuousMap.id _)) (G.unit.comp q)).continuous.subtype_mk _⟩

private def refinedInverse : C(RefinedArrow q, RefinedArrow q) :=
  ⟨fun a ↦ ⟨((a.val.1.2, a.val.1.1), G.inverse a.val.2),
      Prod.ext ((refined_target q a).trans (G.source_inv _).symm)
        ((refined_source q a).trans (G.target_inv _).symm)⟩,
    (kelleyPair (kelleyPair (refinedTarget q) (refinedSource q))
      (G.inverse.comp (refinedUnderlying q))).continuous.subtype_mk _⟩

private abbrev RefinedPairs := ComposableArrows (refinedSource q) (refinedTarget q)

private instance : CompactlyGeneratedSpace (RefinedPairs q) :=
  closed_compactlyGenerated (CGWH.fibreSubspace_isClosed
    (CGWH.map (X := refinedArrowSpace q) (Y := W) (refinedTarget q))
    (CGWH.map (X := refinedArrowSpace q) (Y := W) (refinedSource q)))

private def refinedFirst : C(RefinedPairs q, RefinedArrow q) :=
  ⟨fun p ↦ p.val.1, continuous_fst.comp (continuous_Kelley_forget.comp continuous_subtype_val)⟩

private def refinedSecond : C(RefinedPairs q, RefinedArrow q) :=
  ⟨fun p ↦ p.val.2, continuous_snd.comp (continuous_Kelley_forget.comp continuous_subtype_val)⟩

private theorem refined_composable (a b : RefinedArrow q) (h : a.val.1.2 = b.val.1.1) :
    G.target a.val.2 = G.source b.val.2 :=
  (refined_target q a).symm.trans ((congrArg q h).trans (refined_source q b))

private def refinedComp : C(RefinedPairs q, RefinedArrow q) := by
  let pair : C(RefinedPairs q, ComposableArrows G.source G.target) :=
    ⟨fun p ↦ ⟨(p.val.1.val.2, p.val.2.val.2), refined_composable q p.val.1 p.val.2 p.property⟩,
      (kelleyPair ((refinedUnderlying q).comp (refinedFirst q))
        ((refinedUnderlying q).comp (refinedSecond q))).continuous.subtype_mk _⟩
  exact ⟨fun p ↦ ⟨((p.val.1.val.1.1, p.val.2.val.1.2), G.comp (pair p)),
    Prod.ext ((refined_source q p.val.1).trans (G.source_comp (pair p)).symm)
      ((refined_target q p.val.2).trans (G.target_comp (pair p)).symm)⟩,
    (kelleyPair (kelleyPair ((refinedSource q).comp (refinedFirst q))
      ((refinedTarget q).comp (refinedSecond q))) (G.comp.comp pair)).continuous.subtype_mk _⟩

/-- Pull the arrow space back along the two copies of the object map. -/
def refineObjects : TopologicalGroupoid.{u} where
  objects := W
  arrows := refinedArrowSpace q
  source := refinedSource q
  target := refinedTarget q
  unit := refinedUnit q
  inverse := refinedInverse q
  comp := refinedComp q
  source_unit _ := rfl
  target_unit _ := rfl
  source_inv _ := rfl
  target_inv _ := rfl
  source_comp _ := rfl
  target_comp _ := rfl
  unit_comp a := Subtype.ext (Prod.ext rfl (by
    change G.comp ⟨(G.unit (q a.val.1.1), a.val.2), _⟩ = a.val.2
    calc
      _ = G.comp ⟨(G.unit (G.source a.val.2), a.val.2), G.target_unit _⟩ := by
        apply congrArg (fun r : ComposableArrows G.source G.target ↦ G.comp r)
        exact Subtype.ext (Prod.ext (congrArg G.unit (refined_source q a)) rfl)
      _ = _ := G.unit_comp a.val.2))
  comp_unit a := Subtype.ext (Prod.ext rfl (by
    change G.comp ⟨(a.val.2, G.unit (q a.val.1.2)), _⟩ = a.val.2
    calc
      _ = G.comp ⟨(a.val.2, G.unit (G.target a.val.2)), (G.source_unit _).symm⟩ := by
        apply congrArg (fun r : ComposableArrows G.source G.target ↦ G.comp r)
        exact Subtype.ext (Prod.ext rfl (congrArg G.unit (refined_target q a)))
      _ = _ := G.comp_unit a.val.2))
  inv_comp a := Subtype.ext (Prod.ext rfl ((G.inv_comp a.val.2).trans
    (congrArg G.unit (refined_target q a).symm)))
  comp_inv a := Subtype.ext (Prod.ext rfl ((G.comp_inv a.val.2).trans
    (congrArg G.unit (refined_source q a).symm)))
  assoc a b c hab hbc := Subtype.ext (Prod.ext rfl
    (G.assoc a.val.2 b.val.2 c.val.2 (refined_composable q a b hab) (refined_composable q b c hbc)))

/-- The continuous projection from a groupoid refined on its objects. -/
def refineObjectsProjection : refineObjects q ⟶ G where
  objectMap := q
  arrowMap := refinedUnderlying q
  mapSource a := (refined_source q a).symm
  mapTarget a := (refined_target q a).symm
  mapUnit _ := rfl
  mapInverse _ := rfl
  mapComp _ _ _ := rfl

/-- A quotient cover of the objects yields a standard Morita equivalence. -/
theorem refineObjectsProjection_standardMorita (hq : IsQuotientMap q) :
    IsStandardMorita (refineObjectsProjection q) := by
  refine ⟨hq, ?_⟩
  let e : (refineObjects q).arrows.obj ≃ₜ ArrowComparisonSpace (refineObjectsProjection q) :=
    Homeomorph.refl _
  exact ⟨e, fun a ↦ Subtype.ext rfl⟩

end ChangeOfObjects

private theorem standardMorita_id (G : TopologicalGroupoid.{u}) :
    IsStandardMorita (𝟙 G) := by
  refine ⟨IsQuotientMap.id, ?_⟩
  refine ⟨{ toFun := arrowComparison (𝟙 G)
            invFun := fun p ↦ p.val.2
            left_inv := fun _ ↦ rfl
            right_inv := ?_
            continuous_toFun := (arrowComparison (𝟙 G)).continuous
            continuous_invFun := continuous_snd.comp
              (continuous_Kelley_forget.comp continuous_subtype_val) }, fun _ ↦ rfl⟩
  intro p
  exact Subtype.ext (Prod.ext p.property.symm rfl)

/-- The map on object spaces of a strictly commuting refinement must
already be a quotient map if both legs are quotient maps. -/
theorem strictRefinement_object_quotient {G H U : TopologicalGroupoid.{u}}
    (f : G ⟶ H) (g : U ⟶ G) (h : U ⟶ H) (he : g ≫ f = h)
    (hg : IsQuotientMap g.objectMap) (hh : IsQuotientMap h.objectMap) :
    IsQuotientMap f.objectMap := by
  have hcomp : IsQuotientMap (f.objectMap ∘ g.objectMap) := by
    change IsQuotientMap ((g ≫ f).objectMap : U.objects.obj → H.objects.obj)
    rw [he]
    exact hh
  exact IsQuotientMap.of_comp hg.continuous f.objectMap.continuous hcomp

theorem arrowComparison_eq {G H : TopologicalGroupoid.{u}} (f : G ⟶ H)
    (p : ArrowComparisonSpace f) (a : G.arrows.obj)
    (hs : G.source a = p.val.1.1) (ht : G.target a = p.val.1.2)
    (ha : f.arrowMap a = p.val.2) : arrowComparison f a = p :=
  Subtype.ext (Prod.ext (Prod.ext hs ht) ha)

private theorem arrowComparison_covered_bijective {G H U : TopologicalGroupoid.{u}}
    (f : G ⟶ H) (g : U ⟶ G) (h : U ⟶ H) (he : g ≫ f = h)
    (hg : Surjective g.objectMap) (eg : Bijective (arrowComparison g))
    (eh : Bijective (arrowComparison h)) : Bijective (arrowComparison f) := by
  have ho (x : U.objects.obj) : h.objectMap x = f.objectMap (g.objectMap x) := by
    rw [← he]
    rfl
  have ha (a : U.arrows.obj) : f.arrowMap (g.arrowMap a) = h.arrowMap a := by
    rw [← he]
    rfl
  constructor
  · intro a b hab
    have hs : G.source a = G.source b := congrArg (fun p : ArrowComparisonSpace f ↦ p.val.1.1) hab
    have ht : G.target a = G.target b := congrArg (fun p : ArrowComparisonSpace f ↦ p.val.1.2) hab
    obtain ⟨x, hx⟩ := hg (G.source a)
    obtain ⟨y, hy⟩ := hg (G.target a)
    let pa : ArrowComparisonSpace g := ⟨((x, y), a), Prod.ext hx hy⟩
    let pb : ArrowComparisonSpace g := ⟨((x, y), b), Prod.ext (hx.trans hs) (hy.trans ht)⟩
    obtain ⟨a', ha'⟩ := eg.2 pa
    obtain ⟨b', hb'⟩ := eg.2 pb
    have heq : arrowComparison h a' = arrowComparison h b' := by
      apply Subtype.ext
      apply Prod.ext
      · exact (congrArg (fun p : ArrowComparisonSpace g ↦ p.val.1) ha').trans
          (congrArg (fun p : ArrowComparisonSpace g ↦ p.val.1) hb').symm
      · change h.arrowMap a' = h.arrowMap b'
        rw [← ha, ← ha b']
        exact congrArg f.arrowMap (congrArg (fun p : ArrowComparisonSpace g ↦ p.val.2) ha') |>.trans
          ((congrArg (fun p : ArrowComparisonSpace f ↦ p.val.2) hab).trans
            (congrArg f.arrowMap (congrArg (fun p : ArrowComparisonSpace g ↦ p.val.2) hb')).symm)
    exact (congrArg (fun p : ArrowComparisonSpace g ↦ p.val.2) ha').symm.trans
      ((congrArg g.arrowMap (eh.1 heq)).trans
        (congrArg (fun p : ArrowComparisonSpace g ↦ p.val.2) hb'))
  · intro p
    obtain ⟨x, hx⟩ := hg p.val.1.1
    obtain ⟨y, hy⟩ := hg p.val.1.2
    let q : ArrowComparisonSpace h := ⟨((x,y), p.val.2), by
      change (h.objectMap x, h.objectMap y) = (H.source p.val.2, H.target p.val.2)
      rw [ho, ho, hx, hy]
      exact p.property⟩
    obtain ⟨a, hq⟩ := eh.2 q
    refine ⟨g.arrowMap a, arrowComparison_eq f p _ ?_ ?_ ?_⟩
    · rw [g.mapSource]
      exact (congrArg g.objectMap (congrArg (fun p : ArrowComparisonSpace h ↦ p.val.1.1) hq)).trans hx
    · rw [g.mapTarget]
      exact (congrArg g.objectMap (congrArg (fun p : ArrowComparisonSpace h ↦ p.val.1.2) hq)).trans hy
    · rw [ha]
      exact congrArg (fun p : ArrowComparisonSpace h ↦ p.val.2) hq

private def comparisonEndpoints {G H : TopologicalGroupoid.{u}} (f : G ⟶ H) :
    arrowComparisonObject f ⟶ objectSquare G.objects :=
  CGWH.map ⟨fun p ↦ p.val.1, continuous_fst.comp
    (continuous_Kelley_forget.comp continuous_subtype_val)⟩

set_option maxHeartbeats 800000 in
private theorem arrowComparison_covered_homeomorph {G H U : TopologicalGroupoid.{u}}
    (f : G ⟶ H) (g : U ⟶ G) (h : U ⟶ H) (he : g ≫ f = h)
    (hg : IsQuotientMap g.objectMap)
    (eg : U.arrows.obj ≃ₜ ArrowComparisonSpace g) (heg : ∀ a, eg a = arrowComparison g a)
    (eh : U.arrows.obj ≃ₜ ArrowComparisonSpace h) (heh : ∀ a, eh a = arrowComparison h a) :
    ∃ e : G.arrows.obj ≃ₜ ArrowComparisonSpace f, ∀ a, e a = arrowComparison f a := by
  classical
  have hgb : Bijective (arrowComparison g) := (show (eg : U.arrows.obj → _) = arrowComparison g from
    funext heg) ▸ eg.bijective
  have hhb : Bijective (arrowComparison h) := (show (eh : U.arrows.obj → _) = arrowComparison h from
    funext heh) ▸ eh.bijective
  let e := Equiv.ofBijective (arrowComparison f) (arrowComparison_covered_bijective f g h he
    hg.surjective hgb hhb)
  let P := CGWH.FibreSubspace (endpointMap g) (comparisonEndpoints f)
  let p : C(P, ArrowComparisonSpace f) := ⟨fun x ↦ x.val.2, continuous_snd.comp
    (continuous_Kelley_forget.comp continuous_subtype_val)⟩
  let u : C(P, Kelley (U.objects.obj × U.objects.obj)) := ⟨fun x ↦ x.val.1, continuous_fst.comp
    (continuous_Kelley_forget.comp continuous_subtype_val)⟩
  have hp : IsQuotientMap p := CGWH.quotient_baseChange (endpointMap g) (comparisonEndpoints f)
    (kelleyProduct_quotient hg hg)
  have ho (x : U.objects.obj) : h.objectMap x = f.objectMap (g.objectMap x) := by
    rw [← he]
    rfl
  let b : C(ArrowComparisonSpace f, H.arrows.obj) := ⟨fun x ↦ x.val.2, continuous_snd.comp
    (continuous_Kelley_forget.comp continuous_subtype_val)⟩
  have hr (x : P) : (endpointMap h).hom (u x) = (endpoints H).hom (b (p x)) := by
    have hx : (g.objectMap (u x).1, g.objectMap (u x).2) = (p x).val.1 := x.property
    have hs : g.objectMap (u x).1 = (p x).val.1.1 := congrArg Prod.fst hx
    have ht : g.objectMap (u x).2 = (p x).val.1.2 := congrArg Prod.snd hx
    change (h.objectMap (u x).1, h.objectMap (u x).2) =
      (H.source (b (p x)), H.target (b (p x)))
    rw [ho, ho, hs, ht]
    exact (p x).property
  let r : C(P, ArrowComparisonSpace h) := ⟨fun x ↦ ⟨(u x, b (p x)), hr x⟩,
    (kelleyPair u (b.comp p)).continuous.subtype_mk hr⟩
  have hLift (x : P) : arrowComparison f (g.arrowMap (eh.symm (r x))) = p x := by
    have hx : arrowComparison h (eh.symm (r x)) = r x :=
      (heh _).symm.trans (eh.apply_symm_apply _)
    have heq : (g.objectMap (u x).1, g.objectMap (u x).2) = (p x).val.1 := x.property
    apply arrowComparison_eq
    · rw [g.mapSource]
      exact (congrArg g.objectMap (congrArg (fun p : ArrowComparisonSpace h ↦ p.val.1.1) hx)).trans
        (congrArg Prod.fst heq)
    · rw [g.mapTarget]
      exact (congrArg g.objectMap (congrArg (fun p : ArrowComparisonSpace h ↦ p.val.1.2) hx)).trans
        (congrArg Prod.snd heq)
    · change (g ≫ f).arrowMap (eh.symm (r x)) = _
      rw [he]
      exact congrArg (fun p : ArrowComparisonSpace h ↦ p.val.2) hx
  have hc : Continuous e.symm := hp.continuous_iff.mpr (by
    have hfun : e.symm ∘ p = fun x ↦ g.arrowMap (eh.symm (r x)) := by
      funext x
      apply e.injective
      exact (e.apply_symm_apply (p x)).trans (hLift x).symm
    rw [hfun]
    exact g.arrowMap.continuous.comp (eh.symm.continuous.comp r.continuous))
  exact ⟨⟨e, (arrowComparison f).continuous, hc⟩, fun _ ↦ rfl⟩

/-- Exact correction of E.6.4.5. A strict common refinement with two
standard Morita legs exists exactly when the given functor itself is
standard Morita. -/
theorem strictMoritaRefinement_iff {G H : TopologicalGroupoid.{u}} (f : G ⟶ H) :
    (∃ (U : TopologicalGroupoid.{u}) (g : U ⟶ G) (h : U ⟶ H),
      IsStandardMorita g ∧ IsStandardMorita h ∧ g ≫ f = h) ↔ IsStandardMorita f := by
  constructor
  · rintro ⟨U, g, h, ⟨hg, eg, hEg⟩, ⟨hh, eh, hEh⟩, he⟩
    exact ⟨strictRefinement_object_quotient f g h he hg hh,
      arrowComparison_covered_homeomorph f g h he hg eg hEg eh hEh⟩
  · intro hf
    exact ⟨G, 𝟙 G, f, standardMorita_id G, hf, Category.id_comp f⟩

private def objectMapMorphism {G H : TopologicalGroupoid.{u}} (f : G ⟶ H) :
    G.objects ⟶ H.objects := CGWH.map f.objectMap

private def targetMorphism (H : TopologicalGroupoid.{u}) : H.arrows ⟶ H.objects :=
  CGWH.map H.target

/-- Pairs of a source object and an arrow ending at its image. -/
abbrev MoritaAnchorSpace {G H : TopologicalGroupoid.{u}} (f : G ⟶ H) :=
  CGWH.FibreSubspace (objectMapMorphism f) (targetMorphism H)

/-- The coverage map in E.6.4.2(2)(b). -/
def moritaAnchor {G H : TopologicalGroupoid.{u}} (f : G ⟶ H) :
    C(MoritaAnchorSpace f, H.objects.obj) :=
  ⟨fun p ↦ H.source p.val.2, H.source.continuous.comp
    (continuous_snd.comp (continuous_Kelley_forget.comp continuous_subtype_val))⟩

/-- The submersion check used in the proof of E.6.4.4. -/
theorem moritaAnchor_quotient_of_object_quotient {G H : TopologicalGroupoid.{u}}
    (f : G ⟶ H) (hf : IsQuotientMap f.objectMap) : IsQuotientMap (moritaAnchor f) :=
  H.unit_closed_and_projections_quotient.2.1.comp
    (CGWH.quotient_baseChange (objectMapMorphism f) (targetMorphism H) hf)

/-- A continuous quasi-inverse with continuous counit supplies a global
section of the coverage map. -/
theorem moritaAnchor_quotient_of_continuous_counit {G H : TopologicalGroupoid.{u}}
    (f : G ⟶ H) (k : H ⟶ G)
    (α : ContinuousTransformation (k ≫ f) (𝟙 H)) : IsQuotientMap (moritaAnchor f) := by
  let A : C(H.objects.obj, H.arrows.obj) :=
    ⟨fun x ↦ (α.val.app x).val, α.property⟩
  let B := H.inverse.comp A
  have ht (x : H.objects.obj) : f.objectMap (k.objectMap x) = H.target (B x) :=
    ((H.target_inv (A x)).trans (α.val.app x).property.1).symm
  let j : C(H.objects.obj, MoritaAnchorSpace f) := ⟨fun x ↦ ⟨(k.objectMap x, B x), ht x⟩,
    (kelleyPair k.objectMap B).continuous.subtype_mk ht⟩
  exact IsQuotientMap.of_inverse j.continuous (moritaAnchor f).continuous fun x ↦
    (H.source_inv (A x)).trans (α.val.app x).property.2

private def singletonGroupoid : TopologicalGroupoid.{0} :=
  constant (CGWH.of (X := PUnit) (fun _ f ↦ (isCompact_range f.continuous).isClosed))

private def twoPointPairGroupoid : TopologicalGroupoid.{0} :=
  pairGroupoid (CGWH.of (X := Bool) (fun _ f ↦ (isCompact_range f.continuous).isClosed))

private def includePoint : singletonGroupoid ⟶ twoPointPairGroupoid where
  objectMap := ContinuousMap.const _ false
  arrowMap := ContinuousMap.const _ (false, false)
  mapSource _ := rfl
  mapTarget _ := rfl
  mapUnit _ := rfl
  mapInverse _ := rfl
  mapComp _ _ _ := rfl

private def collapsePair : twoPointPairGroupoid ⟶ singletonGroupoid where
  objectMap := ContinuousMap.const _ PUnit.unit
  arrowMap := ContinuousMap.const _ PUnit.unit
  mapSource _ := rfl
  mapTarget _ := rfl
  mapUnit _ := rfl
  mapInverse _ := rfl
  mapComp _ _ _ := rfl

private def pairCounit :
    ContinuousTransformation (collapsePair ≫ includePoint) (𝟙 twoPointPairGroupoid) := by
  refine ⟨{app := fun x ↦ ⟨(false, x), rfl, rfl⟩, naturality := ?_}, ?_⟩
  · intro x y a
    apply Subtype.ext
    change (false, y) = (false, (a.val : Bool × Bool).2)
    exact Prod.ext rfl a.property.2.symm
  · letI : DiscreteTopology twoPointPairGroupoid.Underlying := inferInstanceAs (DiscreteTopology Bool)
    exact continuous_of_discreteTopology

/-- A topological equivalence, with a continuous quasi-inverse and continuous
comparison transformations, need not have a strictly commuting standard
Morita refinement. This refutes the strict conclusion of E.6.4.5. -/
theorem strictMoritaRefinement_counterexample :
    ∃ (G H : TopologicalGroupoid.{0}) (f : G ⟶ H) (k : H ⟶ G),
      Nonempty ((f ≫ k) ≅ 𝟙 G) ∧ Nonempty ((k ≫ f) ≅ 𝟙 H) ∧
      ¬ ∃ (U : TopologicalGroupoid.{0}) (g : U ⟶ G) (h : U ⟶ H),
        IsStandardMorita g ∧ IsStandardMorita h ∧ g ≫ f = h := by
  let α : (collapsePair ≫ includePoint) ⟶ (𝟙 twoPointPairGroupoid) := pairCounit
  letI : IsIso α := continuousTransformation_isIso α
  refine ⟨singletonGroupoid, twoPointPairGroupoid, includePoint, collapsePair, ?_,
    ⟨asIso α⟩, ?_⟩
  · have he : includePoint ≫ collapsePair = 𝟙 singletonGroupoid :=
      Hom.ext (ContinuousMap.ext fun x ↦ by change PUnit.unit = x; cases x; rfl)
        (ContinuousMap.ext fun x ↦ by change PUnit.unit = x; cases x; rfl)
    exact ⟨eqToIso he⟩
  · rintro ⟨U, g, h, hg, hh, he⟩
    obtain ⟨x, hx⟩ := (strictRefinement_object_quotient includePoint g h he hg.1 hh.1).surjective true
    exact Bool.noConfusion hx

end Masullo.TopologicalGroupoid
