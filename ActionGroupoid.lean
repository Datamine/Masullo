import TopologicalGroupoid

open CategoryTheory Function Set Topology TopologicalSpace

namespace Masullo.TopologicalGroupoid

universe u

section Action

variable {X : CGWH.{u}} {G : Type u} [Group G] [TopologicalSpace G] [MulAction G X.obj]

private def actionArrows (hG : WeaklyHausdorff G) : CGWH.{u} :=
  CGWH.of (X := Kelley (G × X.obj)) (weaklyHausdorff_kelleyProduct hG X.property)

private def actionSource : C(Kelley (G × X.obj), X.obj) :=
  ⟨Prod.snd, continuous_snd.comp continuous_Kelley_forget⟩

private def actionTarget (ha : Continuous (fun p : Kelley (G × X.obj) => p.1 • p.2)) :
    C(Kelley (G × X.obj), X.obj) := ⟨fun p => p.1 • p.2, ha⟩

private theorem actionComposable_closed
    (hG : WeaklyHausdorff G) (ha : Continuous (fun p : Kelley (G × X.obj) => p.1 • p.2)) :
    IsClosed {p : Kelley (Kelley (G × X.obj) × Kelley (G × X.obj)) |
      actionTarget ha p.1 = actionSource p.2} :=
  CGWH.fibreSubspace_isClosed (CGWH.map (X := actionArrows hG) (Y := X) (actionTarget ha))
    (CGWH.map (X := actionArrows hG) (Y := X) actionSource)

/-- Construction E.4.2.12, using the Kelley product in the arrow space.
For the successive arrows `(g,x)` and `(h,g • x)`, the composite is `(h*g,x)`. -/
def action (hG : WeaklyHausdorff G)
    (hm : Continuous (fun p : Kelley (G × G) => p.1 * p.2)) (hi : Continuous (Inv.inv : G → G))
    (ha : Continuous (fun p : Kelley (G × X.obj) => p.1 • p.2)) : TopologicalGroupoid.{u} := by
  let A := actionArrows (X := X) hG
  let s := actionSource (X := X) (G := G)
  let t := actionTarget ha
  letI : CompactlyGeneratedSpace (ComposableArrows s.toFun t.toFun) :=
    closed_compactlyGenerated (actionComposable_closed hG ha)
  let fst : C(Kelley (G × X.obj), G) := ⟨Prod.fst, continuous_fst.comp continuous_Kelley_forget⟩
  let p : C(ComposableArrows s t, Kelley (G × X.obj)) :=
    ⟨fun z => z.val.1, continuous_fst.comp (continuous_Kelley_forget.comp continuous_subtype_val)⟩
  let q : C(ComposableArrows s t, Kelley (G × X.obj)) :=
    ⟨fun z => z.val.2, continuous_snd.comp (continuous_Kelley_forget.comp continuous_subtype_val)⟩
  let mul : C(Kelley (G × G), G) := ⟨fun z => z.1 * z.2, hm⟩
  let cm : C(ComposableArrows s t, Kelley (G × X.obj)) :=
    kelleyPair (T := ComposableArrows s.toFun t.toFun)
      (mul.comp (kelleyPair (T := ComposableArrows s.toFun t.toFun) (fst.comp q) (fst.comp p))) (s.comp p)
  refine {
    objects := X
    arrows := A
    source := s
    target := t
    unit := kelleyPair (ContinuousMap.const _ 1) (ContinuousMap.id _)
    inverse := kelleyPair ((⟨Inv.inv, hi⟩ : C(G, G)).comp fst) t
    comp := cm
    source_unit := fun _ => rfl
    target_unit := one_smul G
    source_inv := fun _ => rfl
    target_inv := fun z => inv_smul_smul z.1 z.2
    source_comp := fun _ => rfl
    target_comp := ?_
    unit_comp := ?_
    comp_unit := ?_
    inv_comp := ?_
    comp_inv := ?_
    assoc := ?_ }
  · intro z
    change (z.val.2.1 * z.val.1.1) • z.val.1.2 = z.val.2.1 • z.val.2.2
    rw [mul_smul]
    exact congrArg (z.val.2.1 • ·) z.property
  · intro z
    exact Prod.ext (mul_one z.1) rfl
  · intro z
    exact Prod.ext (one_mul z.1) rfl
  · intro z
    exact Prod.ext (mul_inv_cancel z.1) rfl
  · intro z
    exact Prod.ext (inv_mul_cancel z.1) rfl
  · intro a b c hab hbc
    exact Prod.ext (mul_assoc c.1 b.1 a.1).symm rfl

end Action

/-- The pair groupoid, with one arrow from each object to each object. -/
def pairGroupoid (X : CGWH.{u}) : TopologicalGroupoid.{u} := by
  let A : CGWH.{u} := CGWH.of (X := Kelley (X.obj × X.obj))
    (weaklyHausdorff_kelleyProduct X.property X.property)
  let s : C(Kelley (X.obj × X.obj), X.obj) := ⟨Prod.fst, continuous_fst.comp continuous_Kelley_forget⟩
  let t : C(Kelley (X.obj × X.obj), X.obj) := ⟨Prod.snd, continuous_snd.comp continuous_Kelley_forget⟩
  have hc := CGWH.fibreSubspace_isClosed (CGWH.map (X := A) (Y := X) t)
    (CGWH.map (X := A) (Y := X) s)
  letI : CompactlyGeneratedSpace (ComposableArrows s.toFun t.toFun) := closed_compactlyGenerated hc
  let p : C(ComposableArrows s.toFun t.toFun, Kelley (X.obj × X.obj)) :=
    ⟨fun a => a.val.1, continuous_fst.comp (continuous_Kelley_forget.comp continuous_subtype_val)⟩
  let q : C(ComposableArrows s.toFun t.toFun, Kelley (X.obj × X.obj)) :=
    ⟨fun a => a.val.2, continuous_snd.comp (continuous_Kelley_forget.comp continuous_subtype_val)⟩
  let cm : C(ComposableArrows s.toFun t.toFun, Kelley (X.obj × X.obj)) :=
    kelleyPair (T := ComposableArrows s.toFun t.toFun) (s.comp p) (t.comp q)
  exact {
    objects := X
    arrows := A
    source := s
    target := t
    unit := kelleyPair (ContinuousMap.id _) (ContinuousMap.id _)
    inverse := kelleyPair t s
    comp := cm
    source_unit := fun _ => rfl
    target_unit := fun _ => rfl
    source_inv := fun _ => rfl
    target_inv := fun _ => rfl
    source_comp := fun _ => rfl
    target_comp := fun _ => rfl
    unit_comp := fun _ => rfl
    comp_unit := fun _ => rfl
    inv_comp := fun _ => rfl
    comp_inv := fun _ => rfl
    assoc := fun _ _ _ _ _ => rfl }

/-- Conjugation arrows sit over an arrow and a loop based at that arrow's source. -/
abbrev ConjugationArrow (G : TopologicalGroupoid.{u}) :=
  {p : G.arrows.obj × G.Inertia // G.source p.1 = G.source p.2.val}

private def boolPairGroupoid : TopologicalGroupoid.{0} :=
  pairGroupoid (CGWH.of (X := Bool) (fun _ f => (isCompact_range f.continuous).isClosed))

/-- In the printed order of E.6.3.6(3), the first loop can be based at a
different object from the source of the composite. The pair groupoid on two
points gives a concrete example. -/
theorem inertia_printed_composite_preserves_wrong_loop :
    ∃ (G : TopologicalGroupoid.{0}) (first second : ConjugationArrow G)
      (h : G.target first.val.1 = G.source second.val.1),
      G.source (G.comp ⟨(first.val.1, second.val.1), h⟩) ≠ G.source second.val.2.val := by
  let G := boolPairGroupoid
  let first : ConjugationArrow G := ⟨((false, true), ⟨(false, false), rfl⟩), rfl⟩
  let second : ConjugationArrow G := ⟨((true, false), ⟨(true, true), rfl⟩), rfl⟩
  exact ⟨G, first, second, rfl, Bool.noConfusion⟩

end Masullo.TopologicalGroupoid
