import RankCocycleStack

open CategoryTheory Opposite Function Topology
open scoped Bicategory

namespace Masullo.TopologicalGroupoid

open QuotientCocycle

noncomputable section

universe u

variable {α : Ordinal.{u}} {G : TopologicalGroupoid.{u}} {X : RankSpace α} {S : Sieve X}

private abbrev RankDescent (G : TopologicalGroupoid.{u}) (S : Sieve X) :=
  (rankCocyclePseudofunctor G α).DescentData (fun i : S.arrows.category ↦ i.obj.hom)

private abbrev localObj (D : RankDescent G S) (i : S.arrows.category) : QuotientCocycle G i.obj.left.space :=
  D.obj i

private abbrev U := rankSpaceInclusion α

/-- Two factorizations of the same arrow through two domains in a sieve. -/
private abbrev OverlapSpan (i j : S.arrows.category) (W : RankSpace α) :=
  {p : (W ⟶ i.obj.left) × (W ⟶ j.obj.left) // p.1 ≫ i.obj.hom = p.2 ≫ j.obj.hom}

private def OverlapSpan.refine {i j : S.arrows.category} {V W : RankSpace α}
    (p : OverlapSpan i j W) (d : V ⟶ W) : OverlapSpan i j V :=
  ⟨(d ≫ p.val.1,d ≫ p.val.2),by simp only [Category.assoc,p.property]⟩

private abbrev spanHom (D : RankDescent G S) {i j : S.arrows.category} {W : RankSpace α}
    (p : OverlapSpan i j W) :
    (localObj D i).pullback (U.map p.val.1) ⟶ (localObj D j).pullback (U.map p.val.2) :=
  D.hom (p.val.1 ≫ i.obj.hom) p.val.1 p.val.2 rfl p.property.symm

private def spanValue (D : RankDescent G S) {i j : S.arrows.category} {W : RankSpace α}
    (p : OverlapSpan i j W) (w : W.space.obj)
    (x : (localObj D i).coverSpace.obj) (y : (localObj D j).coverSpace.obj)
    (hx : (localObj D i).cover.hom x = (U.map p.val.1).hom w)
    (hy : (localObj D j).cover.hom y = (U.map p.val.2).hom w) :
    G.UnderlyingArrow ((localObj D i).point x) ((localObj D j).point y) :=
  homValue (spanHom D p) ⟨(x,w),hx⟩ ⟨(y,w),hy⟩ rfl

private theorem spanValue_refine (D : RankDescent G S) {i j : S.arrows.category} {V W : RankSpace α}
    (p : OverlapSpan i j W) (d : V ⟶ W) (v : V.space.obj)
    (x : (localObj D i).coverSpace.obj) (y : (localObj D j).coverSpace.obj)
    (hx : (localObj D i).cover.hom x = (U.map (p.refine d).val.1).hom v)
    (hy : (localObj D j).cover.hom y = (U.map (p.refine d).val.2).hom v) :
    spanValue D (p.refine d) v x y hx hy = spanValue D p ((U.map d).hom v) x y hx hy := by
  have h := D.pullHom_hom d (p.val.1 ≫ i.obj.hom) ((d ≫ p.val.1) ≫ i.obj.hom)
    (Category.assoc d p.val.1 i.obj.hom).symm p.val.1 p.val.2 rfl p.property.symm
    (d ≫ p.val.1) (d ≫ p.val.2) rfl rfl
  have e := (rankCocyclePullHom_eq G p.val.1 p.val.2 d (spanHom D p)).symm.trans h
  let q : CGWH.FibreSubspace ((localObj D i).pullback (U.map (d ≫ p.val.1))).cover
      ((localObj D j).pullback (U.map (d ≫ p.val.2))).cover :=
    ⟨(⟨(x,v),hx⟩,⟨(y,v),hy⟩),rfl⟩
  apply Subtype.ext
  exact (congrArg (fun a : (localObj D i).pullback (U.map (d ≫ p.val.1)) ⟶
    (localObj D j).pullback (U.map (d ≫ p.val.2)) ↦ a.val.val q) e).symm.trans
    (pullbackRebracketHom_apply (U.map p.val.1) (U.map p.val.2) (spanHom D p) (U.map d) q)

private noncomputable def constMap (V W : RankSpace α) (w : W.space.obj) : V ⟶ W :=
  U.preimage (CGWH.map (ContinuousMap.const _ w))

private theorem constMap_apply (V W : RankSpace α) (w : W.space.obj) (v : V.space.obj) :
    (U.map (constMap V W w)).hom v = w := by
  unfold constMap
  rw [Functor.map_preimage]
  rfl

private theorem spanValue_independent (D : RankDescent G S) {i j : S.arrows.category}
    {V W : RankSpace α} (p : OverlapSpan i j V) (q : OverlapSpan i j W)
    (v : V.space.obj) (w : W.space.obj) (x : (localObj D i).coverSpace.obj)
    (y : (localObj D j).coverSpace.obj)
    (hx : (localObj D i).cover.hom x = (U.map p.val.1).hom v)
    (hy : (localObj D j).cover.hom y = (U.map p.val.2).hom v)
    (hx' : (localObj D i).cover.hom x = (U.map q.val.1).hom w)
    (hy' : (localObj D j).cover.hom y = (U.map q.val.2).hom w) :
    spanValue D p v x y hx hy = spanValue D q w x y hx' hy' := by
  let a := constMap V V v
  let b := constMap V W w
  have pa : (U.map a).hom v = v := constMap_apply V V v v
  have pb : (U.map b).hom v = w := constMap_apply V W w v
  have ea : (localObj D i).cover.hom x = (U.map (p.refine a).val.1).hom v :=
    hx.trans (congrArg (U.map p.val.1).hom pa).symm
  have eb : (localObj D j).cover.hom y = (U.map (p.refine a).val.2).hom v :=
    hy.trans (congrArg (U.map p.val.2).hom pa).symm
  have ec : (localObj D i).cover.hom x = (U.map (q.refine b).val.1).hom v :=
    hx'.trans (congrArg (U.map q.val.1).hom pb).symm
  have ed : (localObj D j).cover.hom y = (U.map (q.refine b).val.2).hom v :=
    hy'.trans (congrArg (U.map q.val.2).hom pb).symm
  have ep : p.refine a = q.refine b := by
    apply Subtype.ext
    apply Prod.ext
    · apply U.map_injective
      apply CGWH.ext_hom
      intro v'
      exact (congrArg (U.map p.val.1).hom (constMap_apply V V v v')).trans
        (hx.symm.trans (hx'.trans (congrArg (U.map q.val.1).hom (constMap_apply V W w v')).symm))
    · apply U.map_injective
      apply CGWH.ext_hom
      intro v'
      exact (congrArg (U.map p.val.2).hom (constMap_apply V V v v')).trans
        (hy.symm.trans (hy'.trans (congrArg (U.map q.val.2).hom (constMap_apply V W w v')).symm))
  have ecg (c d : OverlapSpan i j V) (h : c = d)
      (hx₁ : (localObj D i).cover.hom x = (U.map c.val.1).hom v)
      (hy₁ : (localObj D j).cover.hom y = (U.map c.val.2).hom v)
      (hx₂ : (localObj D i).cover.hom x = (U.map d.val.1).hom v)
      (hy₂ : (localObj D j).cover.hom y = (U.map d.val.2).hom v) :
      spanValue D c v x y hx₁ hy₁ = spanValue D d v x y hx₂ hy₂ := by subst d; rfl
  have el := spanValue_refine D p a v x y ea eb
  have er := spanValue_refine D q b v x y ec ed
  simp only [pa] at el
  simp only [pb] at er
  exact el.symm.trans ((ecg _ _ ep ea eb ec ed).trans er)

private abbrev sieveIndex (i : S.arrows.category) : RankSieveArrows S :=
  ⟨i.obj.left,i.obj.hom,i.property⟩

private abbrev overlapTest (i j : S.arrows.category)
    (hα : Cardinal.preBeth α = α.card) (hω : Cardinal.aleph0 < Cardinal.preBeth α) :=
  rankSieveOverlapTest (sieveIndex i) (sieveIndex j) hα hω

private def overlapTestSpan {i j : S.arrows.category} (t : RankSieveOverlapTest (sieveIndex i) (sieveIndex j)) :
    OverlapSpan i j t.mid.1 :=
  ⟨(t.left.hom,t.right.hom),t.left.comm.trans t.right.comm.symm⟩

private def descentOverlapHom (D : RankDescent G S) (hα : Cardinal.preBeth α = α.card)
    (hω : Cardinal.aleph0 < Cardinal.preBeth α) (i j : S.arrows.category) :
    (localObj D i).PairOverlapHom (localObj D j) (U.map i.obj.hom) (U.map j.obj.hom) :=
  let t := overlapTest i j hα hω
  pairOverlapHomOfHomeomorphicTest (localObj D i) (localObj D j) (U.map i.obj.hom) (U.map j.obj.hom)
    t.homeomorph (U.map t.left.hom) (U.map t.right.hom) t.left_apply t.right_apply
    (spanHom D (overlapTestSpan t))

private theorem descentOverlapHom_value (D : RankDescent G S) (hα : Cardinal.preBeth α = α.card)
    (hω : Cardinal.aleph0 < Cardinal.preBeth α) {i j : S.arrows.category} {W : RankSpace α}
    (p : OverlapSpan i j W) (v : W.space.obj) (x : (localObj D i).coverSpace.obj)
    (y : (localObj D j).coverSpace.obj)
    (hx : (localObj D i).cover.hom x = (U.map p.val.1).hom v)
    (hy : (localObj D j).cover.hom y = (U.map p.val.2).hom v)
    (h : ((localObj D i).cover ≫ U.map i.obj.hom).hom x =
      ((localObj D j).cover ≫ U.map j.obj.hom).hom y) :
    pairOverlapValue (localObj D i) (localObj D j) (U.map i.obj.hom) (U.map j.obj.hom)
      (descentOverlapHom D hα hω i j) x y h = spanValue D p v x y hx hy := by
  let t := overlapTest i j hα hω
  let q : CGWH.FibreSubspace (U.map i.obj.hom) (U.map j.obj.hom) :=
    ⟨((localObj D i).cover.hom x,(localObj D j).cover.hom y),h⟩
  let w := t.homeomorph.symm q
  have he := t.homeomorph.apply_symm_apply q
  have hx₀ : (localObj D i).cover.hom x = (U.map t.left.hom).hom w :=
    (congrArg (fun p ↦ p.val.1) he).symm.trans (t.left_apply w)
  have hy₀ : (localObj D j).cover.hom y = (U.map t.right.hom).hom w :=
    (congrArg (fun p ↦ p.val.2) he).symm.trans (t.right_apply w)
  refine Eq.trans ?_ (spanValue_independent D (overlapTestSpan t) p w v x y hx₀ hy₀ hx hy)
  apply Subtype.ext
  exact pairOverlapHomOfHomeomorphicTest_apply (localObj D i) (localObj D j)
    (U.map i.obj.hom) (U.map j.obj.hom) t.homeomorph (U.map t.left.hom)
    (U.map t.right.hom) t.left_apply t.right_apply (spanHom D (overlapTestSpan t)) w x y hx₀ hy₀ h

private def constSpan {i j : S.arrows.category} (W : RankSpace α) (x : i.obj.left.space.obj)
    (y : j.obj.left.space.obj) (h : (U.map i.obj.hom).hom x = (U.map j.obj.hom).hom y) :
    OverlapSpan i j W := by
  refine ⟨(constMap W i.obj.left x,constMap W j.obj.left y),?_⟩
  apply U.map_injective
  apply CGWH.ext_hom
  intro w
  exact (congrArg (U.map i.obj.hom).hom (constMap_apply W i.obj.left x w)).trans
    (h.trans (congrArg (U.map j.obj.hom).hom (constMap_apply W j.obj.left y w)).symm)

private theorem spanHom_eq (D : RankDescent G S) {i j : S.arrows.category} {W : RankSpace α}
    (p : OverlapSpan i j W) (q : W ⟶ X) (ha : p.val.1 ≫ i.obj.hom = q)
    (hb : p.val.2 ≫ j.obj.hom = q) :
    spanHom D p = D.hom q p.val.1 p.val.2 ha hb := by
  subst q
  rfl

private theorem descentOverlapHom_cocycle (D : RankDescent G S)
    (hα : Cardinal.preBeth α = α.card) (hω : Cardinal.aleph0 < Cardinal.preBeth α) :
    PairwiseOverlapCocycle (descentOverlapHom D hα hω) := by
  constructor
  · intro i x
    let v := (localObj D i).cover.hom x
    let p : OverlapSpan i i i.obj.left := constSpan i.obj.left v v rfl
    have hx : (localObj D i).cover.hom x = (U.map p.val.1).hom v := (constMap_apply _ _ v v).symm
    refine (descentOverlapHom_value D hα hω p v x x hx hx rfl).trans ?_
    have e : spanHom D p = 𝟙 _ := D.hom_self (p.val.1 ≫ i.obj.hom) p.val.1 rfl
    apply Subtype.ext
    let C := (localObj D i).pullback (U.map p.val.1)
    exact (congrArg (fun a : C ⟶ C ↦ a.val.val ⟨(⟨(x,v),hx⟩,⟨(x,v),hx⟩),rfl⟩) e).trans
      ((localObj D i).transitionUnit x)
  · intro i j k x y z hxy hyz
    let v := (localObj D i).cover.hom x
    let w := (localObj D j).cover.hom y
    let t := (localObj D k).cover.hom z
    let p : OverlapSpan i j i.obj.left := constSpan i.obj.left v w hxy
    let q : OverlapSpan j k i.obj.left := constSpan i.obj.left w t hyz
    let r : OverlapSpan i k i.obj.left := constSpan i.obj.left v t (hxy.trans hyz)
    have hx : (localObj D i).cover.hom x = (U.map p.val.1).hom v := (constMap_apply _ _ v v).symm
    have hy : (localObj D j).cover.hom y = (U.map p.val.2).hom v := (constMap_apply _ _ w v).symm
    have hz : (localObj D k).cover.hom z = (U.map q.val.2).hom v := (constMap_apply _ _ t v).symm
    have hp := descentOverlapHom_value D hα hω p v x y hx hy hxy
    have hq := descentOverlapHom_value D hα hω q v y z hy hz hyz
    have hr := descentOverlapHom_value D hα hω r v x z hx hz (hxy.trans hyz)
    refine Eq.trans (congrArg₂ (@CategoryStruct.comp G.Underlying _ _ _ _) hp hq) (Eq.trans ?_ hr.symm)
    let b := p.val.1 ≫ i.obj.hom
    have hb₂ : p.val.2 ≫ j.obj.hom = b := p.property.symm
    have hb₃ : q.val.2 ≫ k.obj.hom = b := q.property.symm.trans hb₂
    have he : spanHom D p ≫ spanHom D q = spanHom D r := by
      rw [spanHom_eq D p b rfl hb₂, spanHom_eq D q b hb₂ hb₃, spanHom_eq D r b rfl hb₃]
      exact D.hom_comp b p.val.1 p.val.2 q.val.2 rfl hb₂ hb₃
    let x' : ((localObj D i).pullback (U.map p.val.1)).coverSpace.obj := ⟨(x,v),hx⟩
    let y' : ((localObj D j).pullback (U.map p.val.2)).coverSpace.obj := ⟨(y,v),hy⟩
    let z' : ((localObj D k).pullback (U.map q.val.2)).coverSpace.obj := ⟨(z,v),hz⟩
    apply Subtype.ext
    exact (comp_apply (spanHom D p) (spanHom D q) x' y' z' rfl rfl).symm.trans
      (congrArg (fun a : (localObj D i).pullback (U.map p.val.1) ⟶
        (localObj D k).pullback (U.map q.val.2) ↦ a.val.val ⟨(x',z'),rfl⟩) he)

private abbrev comparisonAt {Y W : RankSpace α} (g : Y ⟶ X) (a : W ⟶ Y) (q : W ⟶ X)
    (h : a ≫ g = q) (A : QuotientCocycle G X.space) :
    A.pullback (U.map q) ≅ (A.pullback (U.map g)).pullback (U.map a) :=
  (Cat.Hom.toNatIso ((rankCocyclePseudofunctor G α).mapComp' g.op.toLoc a.op.toLoc q.op.toLoc
    (congrArg (fun f : W ⟶ X ↦ f.op.toLoc) h))).app A

private theorem comparisonAt_comp {Y W : RankSpace α} (g : Y ⟶ X) (a : W ⟶ Y)
    (A : QuotientCocycle G X.space) :
    comparisonAt g a (a ≫ g) rfl A = pullbackCompIso A (U.map g) (U.map a) := by
  unfold comparisonAt
  have h : (rankCocyclePseudofunctor G α).mapComp' g.op.toLoc a.op.toLoc (a ≫ g).op.toLoc rfl =
      (rankCocyclePseudofunctor G α).mapComp g.op.toLoc a.op.toLoc :=
    Pseudofunctor.mapComp'_eq_mapComp _ _ _
  rw [h]
  rfl

private theorem comparisonAt_hom_value {Y W : RankSpace α} (g : Y ⟶ X) (a : W ⟶ Y)
    (q : W ⟶ X) (h : a ≫ g = q) (A : QuotientCocycle G X.space)
    (p : CGWH.FibreSubspace (A.pullback (U.map q)).cover ((A.pullback (U.map g)).pullback (U.map a)).cover) :
    (comparisonAt g a q h A).hom.val.val p = A.transition ⟨(p.val.1.val.1,p.val.2.val.1.val.1),by
      subst q
      exact p.val.1.property.trans ((congrArg (U.map (a ≫ g)).hom p.property).trans
        ((congrArg (U.map g).hom p.val.2.property).symm.trans p.val.2.val.1.property.symm))⟩ := by
  subst q
  rw [comparisonAt_comp]
  rfl

private theorem comparisonAt_inv_value {Y W : RankSpace α} (g : Y ⟶ X) (a : W ⟶ Y)
    (q : W ⟶ X) (h : a ≫ g = q) (A : QuotientCocycle G X.space)
    (p : CGWH.FibreSubspace ((A.pullback (U.map g)).pullback (U.map a)).cover (A.pullback (U.map q)).cover) :
    (comparisonAt g a q h A).inv.val.val p = A.transition ⟨(p.val.1.val.1.val.1,p.val.2.val.1),by
      subst q
      exact p.val.1.val.1.property.trans ((congrArg (U.map g).hom p.val.1.property).trans
        ((congrArg (U.map (a ≫ g)).hom p.property).trans p.val.2.property.symm))⟩ := by
  subst q
  rw [comparisonAt_comp]
  exact pullbackCompIso_inv_apply A (U.map g) (U.map a) p

/-- The change of domain for descent data induced by a global object
uses that object's original transition on the two presenting points. -/
private theorem globalDescent_hom_value (A : QuotientCocycle G X.space) {Y Z W : RankSpace α}
    (g : Y ⟶ X) (h : Z ⟶ X) (q : W ⟶ X) (a : W ⟶ Y) (b : W ⟶ Z)
    (ha : a ≫ g = q) (hb : b ≫ h = q)
    (p : CGWH.FibreSubspace ((A.pullback (U.map g)).pullback (U.map a)).cover
      ((A.pullback (U.map h)).pullback (U.map b)).cover) :
    ((comparisonAt g a q ha A).inv ≫ (comparisonAt h b q hb A).hom).val.val p =
      A.transition ⟨(p.val.1.val.1.val.1,p.val.2.val.1.val.1),by
        have hg : A.cover.hom p.val.1.val.1.val.1 = (U.map q).hom p.val.1.val.2 := by
          rw [← ha]
          exact p.val.1.val.1.property.trans (congrArg (U.map g).hom p.val.1.property)
        have hh : A.cover.hom p.val.2.val.1.val.1 = (U.map q).hom p.val.2.val.2 := by
          rw [← hb]
          exact p.val.2.val.1.property.trans (congrArg (U.map h).hom p.val.2.property)
        exact hg.trans ((congrArg (U.map q).hom p.property).trans hh.symm)⟩ := by
  let x := p.val.1
  let y := p.val.2
  have hx : A.cover.hom x.val.1.val.1 = (U.map q).hom x.val.2 := by
    rw [← ha]
    exact x.val.1.property.trans (congrArg (U.map g).hom x.property)
  let m : (A.pullback (U.map q)).coverSpace.obj := ⟨(x.val.1.val.1,x.val.2),hx⟩
  exact (comp_apply_left_unit (comparisonAt g a q ha A).inv (comparisonAt h b q hb A).hom
    x m y rfl p.property ((comparisonAt_inv_value g a q ha A ⟨(x,m),rfl⟩).trans
      (A.transitionUnit x.val.1.val.1))).trans
    (comparisonAt_hom_value h b q hb A ⟨(m,y),p.property⟩)

private abbrev descentFamily (D : RankDescent G S) (hα : Cardinal.preBeth α = α.card)
    (hω : Cardinal.aleph0 < Cardinal.preBeth α) :=
  FamilyOverlap.ofPairwise (descentOverlapHom D hα hω) (descentOverlapHom_cocycle D hα hω)

private abbrev DescendedCover (S : Sieve X) :=
  IsQuotientMap (sumDesc (fun i : S.arrows.category ↦ U.map i.obj.hom)).hom

private theorem descentCover (S : Sieve X) (hα : Cardinal.preBeth α = α.card)
    (hω : Cardinal.aleph0 < Cardinal.preBeth α)
    (hS : S ∈ Sheaf.canonicalTopology (RankSpace α) X) : DescendedCover S := by
  let k : (Σ i : RankSieveArrows S, i.1.space.obj) →
      (Σ i : S.arrows.category, i.obj.left.space.obj) :=
    fun x ↦ ⟨S.arrows.categoryMk x.1.2.val x.1.2.property,x.2⟩
  have hk : Continuous k := continuous_sigma fun i ↦
    @continuous_sigmaMk S.arrows.category (fun j ↦ j.obj.left.space.obj) _
      (S.arrows.categoryMk i.2.val i.2.property)
  apply IsQuotientMap.of_comp hk (sumDesc (fun i : S.arrows.category ↦ U.map i.obj.hom)).hom.hom.hom.continuous
  exact (rankCanonicalTopology_iff S hα hω).mp hS

set_option maxHeartbeats 700000 in
/-- The comparison with the assembled cocycle is an isomorphism of
descent data, including every overlap arrow. -/
private def descentIso (D : RankDescent G S) (hα : Cardinal.preBeth α = α.card)
    (hω : Cardinal.aleph0 < Cardinal.preBeth α) (hc : DescendedCover S) :
    D ≅ ((rankCocyclePseudofunctor G α).toDescentData (fun i : S.arrows.category ↦ i.obj.hom)).obj
      ((descentFamily D hα hω).descend hc) := by
  let d := descentFamily D hα hω
  let A := d.descend hc
  let e := d.descendRestrictIso hc
  refine Pseudofunctor.DescentData.isoMk e ?_
  intro W q i j a b ha hb
  let g := U.map i.obj.hom
  let h := U.map j.obj.hom
  let a' := U.map a
  let b' := U.map b
  let s := pullbackHom (e i).hom a'
  let t := (comparisonAt i.obj.hom a q ha A).inv ≫ (comparisonAt j.obj.hom b q hb A).hom
  let n := D.hom q a b ha hb
  let u := pullbackHom (e j).hom b'
  change s ≫ t = n ≫ u
  apply hom_ext
  intro p
  rcases p with ⟨⟨l,r⟩,hbase⟩
  rcases l with ⟨⟨x,v⟩,hx⟩
  rcases r with ⟨⟨r,v'⟩,hw⟩
  change v = v' at hbase
  subst v'
  rcases r with ⟨⟨z,w⟩,hzw⟩
  rcases z with ⟨k,z⟩
  change (localObj D i).cover.hom x = a'.hom v at hx
  change w = b'.hom v at hw
  change ((localObj D k).cover ≫ U.map k.obj.hom).hom z = h.hom w at hzw
  obtain ⟨y,hy⟩ := (localObj D j).isCover.surjective w
  have hy' : (localObj D j).cover.hom y = b'.hom v := hy.trans hw
  have hxy : ((localObj D i).cover ≫ g).hom x = ((localObj D j).cover ≫ h).hom y := by
    have he : U.map a ≫ U.map i.obj.hom = U.map b ≫ U.map j.obj.hom :=
      congrArg U.map (ha.trans hb.symm)
    exact (congrArg g.hom hx).trans ((congrArg (fun f : W.space ⟶ X.space ↦ f.hom v) he).trans
      (congrArg h.hom hy').symm)
  have hyz : ((localObj D j).cover ≫ h).hom y = ((localObj D k).cover ≫ U.map k.obj.hom).hom z :=
    (congrArg h.hom hy).trans hzw.symm
  let x' : ((localObj D i).pullback a').coverSpace.obj := ⟨(x,v),hx⟩
  let y' : ((localObj D j).pullback b').coverSpace.obj := ⟨(y,v),hy'⟩
  let z' : ((A.pullback h).pullback b').coverSpace.obj := ⟨(⟨(⟨k,z⟩,w),hzw⟩,v),hw⟩
  let m : ((A.pullback g).pullback a').coverSpace.obj :=
    ⟨(⟨(⟨k,z⟩,(localObj D i).cover.hom x),(hxy.trans hyz).symm⟩,v),hx⟩
  have hl : (s ≫ t).val.val ⟨(x',z'),rfl⟩ = d.arrow i k ⟨(x,z),hxy.trans hyz⟩ :=
    (comp_apply_right_unit s t x' m z' rfl rfl
      ((globalDescent_hom_value A i.obj.hom j.obj.hom q a b ha hb ⟨(m,z'),rfl⟩).trans
        (A.transitionUnit ⟨k,z⟩))).trans
      (d.descendRestrictIso_apply hc i k x z (hxy.trans hyz).symm)
  have he₁ : n.val.val ⟨(x',y'),rfl⟩ = d.arrow i j ⟨(x,y),hxy⟩ := by
    let p : OverlapSpan i j W := ⟨(a,b),ha.trans hb.symm⟩
    have he := (descentOverlapHom_value D hα hω p v x y hx hy' hxy).symm
    exact (congrArg (fun f : (localObj D i).pullback a' ⟶ (localObj D j).pullback b' ↦
      f.val.val ⟨(x',y'),rfl⟩) (spanHom_eq D p q ha hb)).symm.trans (congrArg Subtype.val he)
  have he₂ : u.val.val ⟨(y',z'),rfl⟩ = d.arrow j k ⟨(y,z),hyz⟩ := by
    let w' : (A.pullback h).coverSpace.obj := ⟨(⟨k,z⟩,(localObj D j).cover.hom y),hyz.symm⟩
    have he : w' = z'.val.1 := Subtype.ext (Prod.ext rfl hy)
    have ep : (⟨(y,w'),rfl⟩ : CGWH.FibreSubspace (localObj D j).cover (A.pullback h).cover) =
        mixedPullback (localObj D j) (A.pullback h) b' ⟨(y',z'),rfl⟩ :=
      Subtype.ext (Prod.ext rfl he)
    exact (congrArg (e j).hom.val.val ep).symm.trans (d.descendRestrictIso_apply hc j k y z hyz.symm)
  change (s ≫ t).val.val ⟨(x',z'),rfl⟩ = (n ≫ u).val.val ⟨(x',z'),rfl⟩
  refine hl.trans (Eq.symm ((comp_apply n u x' y' z' rfl rfl).trans ?_))
  refine Eq.trans ?_ (d.comp i j k x y z hxy hyz)
  apply congrArg G.comp
  exact Subtype.ext (Prod.ext he₁ he₂)

/-- Quotient cocycles form a stack on the canonical rank site. -/
theorem rankCocycle_isStack (G : TopologicalGroupoid.{u}) (hα : Cardinal.preBeth α = α.card)
    (hω : Cardinal.aleph0 < Cardinal.preBeth α) :
    (rankCocyclePseudofunctor G α).IsStack (Sheaf.canonicalTopology (RankSpace α)) where
  toIsPrestack := rankCocycle_isPrestack G hα hω
  essSurj_of_sieve S hS :=
    ⟨fun D ↦
      let hc := descentCover S hα hω hS
      ⟨(descentFamily D hα hω).descend hc,⟨(descentIso D hα hω hc).symm⟩⟩⟩

end

end Masullo.TopologicalGroupoid
