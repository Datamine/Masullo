import RankCocycleDescent
import Mathlib.CategoryTheory.Category.ULift

open CategoryTheory Opposite Topology
open scoped Bicategory Pseudofunctor.StrongTrans

namespace Masullo.TopologicalGroupoid

open QuotientCocycle
attribute [local instance] uliftCategory

universe u

noncomputable section

variable {G : TopologicalGroupoid.{u}} {T : CGWH.{u}}

/-- The identity-cover presentation of continuous points and arrows. -/
def pointPresentation (G : TopologicalGroupoid.{u}) (T : CGWH.{u}) :
    G.Points T ⥤ QuotientCocycle G T where
  obj := ofPoint
  map {a b} r := pointHomEquiv a b r
  map_id _ := hom_ext fun _ ↦ rfl
  map_comp {a b c} r s := by
    apply hom_ext
    intro p
    exact (comp_apply (pointHomEquiv a b r) (pointHomEquiv b c s)
      p.val.1 p.val.1 p.val.2 rfl p.property).symm

def pointPresentation_fullyFaithful (G : TopologicalGroupoid.{u}) (T : CGWH.{u}) :
    (pointPresentation G T).FullyFaithful where
  preimage {a b} := (pointHomEquiv a b).symm
  map_preimage {a b} := (pointHomEquiv a b).apply_symm_apply
  preimage_map {a b} := (pointHomEquiv a b).symm_apply_apply

private def pointRestrictionIso {S : CGWH.{u}} (g : S ⟶ T) (a : G.Points T) :
    ofPoint ((G.restrictPoints g.hom.hom.hom).obj a) ≅ (ofPoint a).pullback g := by
  let C := ofPoint ((G.restrictPoints g.hom.hom.hom).obj a)
  let B := (ofPoint a).pullback g
  let k : C(C.coverSpace.obj,B.coverSpace.obj) :=
    ⟨fun x ↦ ⟨(g.hom x,x),rfl⟩,(kelleyPair g.hom.hom.hom (ContinuousMap.id _)).continuous.subtype_mk _⟩
  exact isoOfCoverMap B C k (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ _ ↦ rfl)

private theorem pointRestrictionIso_apply {S : CGWH.{u}} (g : S ⟶ T) (a : G.Points T)
    (p : CGWH.FibreSubspace (ofPoint ((G.restrictPoints g.hom.hom.hom).obj a)).cover
      ((ofPoint a).pullback g).cover) :
    (pointRestrictionIso g a).hom.val.val p = G.unit (a (g.hom p.val.1)) := rfl

/-- The point presentation commutes with restriction up to a natural
isomorphism on the corresponding presenting covers. -/
def pointPresentationPullbackIso {S : CGWH.{u}} (g : S ⟶ T) :
    G.restrictPoints g.hom.hom.hom ⋙ pointPresentation G S ≅
      pointPresentation G T ⋙ pullbackFunctor g := by
  refine NatIso.ofComponents (pointRestrictionIso g) ?_
  intro a b r
  let L := pointPresentation G S
  let P := pointPresentation G T
  let I := G.restrictPoints g.hom.hom.hom
  change L.map (I.map r) ≫ (pointRestrictionIso g b).hom =
    (pointRestrictionIso g a).hom ≫ pullbackHom (P.map r) g
  apply hom_ext
  intro p
  let x := p.val.1
  let y := p.val.2
  let m : (ofPoint (I.obj b)).coverSpace.obj := x
  let n : ((ofPoint a).pullback g).coverSpace.obj := ⟨(g.hom x,x),rfl⟩
  exact (comp_apply_right_unit (L.map (I.map r)) (pointRestrictionIso g b).hom x m y rfl p.property
    (pointRestrictionIso_apply g b ⟨(m,y),p.property⟩)).trans
    (comp_apply_left_unit (pointRestrictionIso g a).hom (pullbackHom (P.map r) g) x n y rfl p.property
      (pointRestrictionIso_apply g a ⟨(x,n),rfl⟩)).symm

theorem pointRestrictionIso_comp {R S : CGWH.{u}} (g : S ⟶ T) (h : R ⟶ S) (a : G.Points T) :
    (pointRestrictionIso (h ≫ g) a).hom ≫ (pullbackCompIso (ofPoint a) g h).hom =
      (pointRestrictionIso h ((G.restrictPoints g.hom.hom.hom).obj a)).hom ≫
        pullbackHom (pointRestrictionIso g a).hom h := by
  apply hom_ext
  intro p
  let x := p.val.1
  let y := p.val.2
  let m : ((ofPoint a).pullback (h ≫ g)).coverSpace.obj := ⟨((h ≫ g).hom x,x),rfl⟩
  let n : ((ofPoint ((G.restrictPoints g.hom.hom.hom).obj a)).pullback h).coverSpace.obj :=
    ⟨(h.hom x,x),rfl⟩
  exact (comp_apply_left_unit (pointRestrictionIso (h ≫ g) a).hom (pullbackCompIso (ofPoint a) g h).hom
    x m y rfl p.property (pointRestrictionIso_apply (h ≫ g) a ⟨(x,m),rfl⟩)).trans
    (comp_apply_left_unit (pointRestrictionIso h ((G.restrictPoints g.hom.hom.hom).obj a)).hom
      (pullbackHom (pointRestrictionIso g a).hom h) x n y rfl p.property
      (pointRestrictionIso_apply h ((G.restrictPoints g.hom.hom.hom).obj a) ⟨(x,n),rfl⟩)).symm

private theorem pointRestrictionIso_id (a : G.Points T) :
    (pointRestrictionIso (𝟙 T) a).hom ≫ (pullbackIdIso (ofPoint a)).hom = 𝟙 (ofPoint a) := by
  apply hom_ext
  intro p
  let x := p.val.1
  let m : ((ofPoint a).pullback (𝟙 T)).coverSpace.obj := ⟨(x,x),rfl⟩
  exact comp_apply_left_unit (pointRestrictionIso (𝟙 T) a).hom (pullbackIdIso (ofPoint a)).hom
    x m p.val.2 rfl p.property (pointRestrictionIso_apply (𝟙 T) a ⟨(x,m),rfl⟩)

variable {α : Ordinal.{u}}

/-- The manuscript's functor of continuous points on the rank site. The
object lift places it in the same category universe as the cocycles. -/
def rankPointDiagram (G : TopologicalGroupoid.{u}) (α : Ordinal.{u}) :
    (RankSpace α)ᵒᵖ ⥤ Cat.{u,u+1} where
  obj X := Cat.of (ULift.{u+1} (G.Points X.unop.space))
  map f := (ULift.downFunctor ⋙
    G.restrictPoints ((rankSpaceInclusion α).map f.unop).hom.hom.hom ⋙ ULift.upFunctor).toCatHom
  map_id _ := rfl
  map_comp _ _ := rfl

set_option maxHeartbeats 650000 in
/-- Identity-cover presentations give a coherent comparison from the
point diagram to the quotient cocycle stack. -/
def rankPointInclusion (G : TopologicalGroupoid.{u}) (α : Ordinal.{u}) :
    (rankPointDiagram G α).toPseudofunctor' ⟶ rankCocyclePseudofunctor G α where
  app X := (ULift.downFunctor ⋙ pointPresentation G X.as.unop.space).toCatHom
  naturality f := Cat.Hom.isoMk (Functor.isoWhiskerLeft ULift.downFunctor
    (pointPresentationPullbackIso (G := G) ((rankSpaceInclusion α).map f.as.unop)))
  naturality_naturality η := by
    obtain rfl := LocallyDiscrete.eq_of_hom η
    have e : η = 𝟙 _ := Subsingleton.elim _ _
    subst η
    simp only [PrelaxFunctor.map₂_id]
    apply Cat.Hom₂.ext
    ext a
    change 𝟙 _ ≫ _ = _ ≫ 𝟙 _
    exact (Category.id_comp _).trans (Category.comp_id _).symm
  naturality_id X := by
    apply Cat.Hom₂.ext
    ext a
    change ULift.{u+1} (G.Points X.as.unop.space) at a
    change (pointRestrictionIso (𝟙 X.as.unop.space) a.down).hom ≫
      (pullbackIdIso (ofPoint a.down)).hom = 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _
    exact (pointRestrictionIso_id a.down).trans ((Category.id_comp _).trans (Category.id_comp _)).symm
  naturality_comp {X Y Z} f g := by
    apply Cat.Hom₂.ext
    ext a
    change ULift.{u+1} (G.Points X.as.unop.space) at a
    let l := (rankSpaceInclusion α).map f.as.unop
    let m := (rankSpaceInclusion α).map g.as.unop
    let b := (G.restrictPoints l.hom.hom.hom).obj a.down
    change (pointRestrictionIso (m ≫ l) a.down).hom ≫
      (pullbackCompIso (ofPoint a.down) l m).hom =
      𝟙 _ ≫ 𝟙 _ ≫ (pointRestrictionIso m b).hom ≫ 𝟙 _ ≫
        pullbackHom (pointRestrictionIso l a.down).hom m ≫ 𝟙 _
    exact (pointRestrictionIso_comp l m a.down).trans (by
      simp [b]
      rfl)

/-- The total category map from continuous points to their cocycle presentations. -/
def rankPointTotalMap (G : TopologicalGroupoid.{u}) (α : Ordinal.{u}) :
    Pseudofunctor.CoGrothendieck ((rankPointDiagram G α).toPseudofunctor') ⥤ RankCocycleTotal G α :=
  Pseudofunctor.CoGrothendieck.map (rankPointInclusion G α)

theorem rankPointTotalMap_over (G : TopologicalGroupoid.{u}) (α : Ordinal.{u}) :
    rankPointTotalMap G α ⋙ rankCocycleProjection G α =
      Pseudofunctor.CoGrothendieck.forget ((rankPointDiagram G α).toPseudofunctor') := rfl

/-- Each global cocycle is isomorphic to a point on a single canonical
cover in the same rank. -/
theorem rankCocycle_locallyPoint {X : RankSpace α} (A : QuotientCocycle G X.space)
    (hα : Cardinal.preBeth α = α.card) (hω : Cardinal.aleph0 < Cardinal.preBeth α)
    (hκ : (Cardinal.preBeth α).IsStrongLimit) :
    ∃ (W : RankSpace α) (q : W ⟶ X) (a : G.Points W.space),
      Sieve.generate (Presieve.singleton q) ∈ Sheaf.canonicalTopology (RankSpace α) X ∧
        Nonempty (A.pullback ((rankSpaceInclusion α).map q) ≅ ofPoint a) := by
  let U := rankSpaceInclusion α
  obtain ⟨W,l,hl⟩ := rankQuotientMap_refinement A.cover A.isCover hα hω hκ
  let B := A.refinePresentation l hl
  let q : W ⟶ X := U.preimage B.cover
  have hq : U.map q = B.cover := U.map_preimage _
  have hw : IsQuotientMap (U.map q).hom := hq.symm ▸ hl
  obtain ⟨e⟩ := A.refinePresentation_iso l hl
  obtain ⟨i⟩ := B.pullback_cover_locally_point
  have b : Nonempty (B.pullback (U.map q) ≅ ofPoint B.point) := hq.symm ▸ ⟨i⟩
  obtain ⟨j⟩ := b
  exact ⟨W,q,B.point,(rankSingleton_canonical_iff_quotient q hα hω).mpr hw,
    ⟨(pullbackFunctor (U.map q)).mapIso e.symm ≪≫ j⟩⟩

/-- The comparison with the continuous point diagram is fully faithful
in each fibre. -/
def rankPointInclusion_fullyFaithful (G : TopologicalGroupoid.{u}) (X : RankSpace α) :
    ((rankPointInclusion G α).app ⟨op X⟩).toFunctor.FullyFaithful where
  preimage {a b} := (pointHomEquiv a.down b.down).symm
  map_preimage {a b} := (pointHomEquiv a.down b.down).apply_symm_apply
  preimage_map {a b} := (pointHomEquiv a.down b.down).symm_apply_apply

/-- The comparison of the total point and cocycle categories is fully faithful. -/
def rankPointTotalMap_fullyFaithful (G : TopologicalGroupoid.{u}) (α : Ordinal.{u}) :
    (rankPointTotalMap G α).FullyFaithful :=
  FiberedGrothendieck.mapFullyFaithful (rankPointInclusion G α) (rankPointInclusion_fullyFaithful G)

/-- The comparison from points preserves Cartesian arrows over the rank site. -/
theorem rankPointTotalMap_cartesian (G : TopologicalGroupoid.{u})
    {a b : Pseudofunctor.CoGrothendieck ((rankPointDiagram G α).toPseudofunctor')} (r : a ⟶ b) :
    (rankCocycleProjection G α).IsStronglyCartesian r.base ((rankPointTotalMap G α).map r) := by
  let s := (rankPointTotalMap G α).map r
  letI : IsIso s.fiber := @IsIso.of_groupoid (QuotientCocycle G a.base.space) _ _ _ s.fiber
  exact FiberedGrothendieck.isStronglyCartesian_of_fiber_isIso s

/-- The point comparison is locally essentially surjective for the
canonical rank topology. A single canonical cover suffices. -/
theorem rankPointInclusion_locallyEssentiallySurjective (G : TopologicalGroupoid.{u})
    (hα : Cardinal.preBeth α = α.card) (hω : Cardinal.aleph0 < Cardinal.preBeth α)
    (hκ : (Cardinal.preBeth α).IsStrongLimit) {X : RankSpace α}
    (A : (rankCocyclePseudofunctor G α).obj ⟨op X⟩) :
    ∃ (W : RankSpace α) (q : W ⟶ X)
      (a : (rankPointDiagram G α).toPseudofunctor'.obj ⟨op W⟩),
      Sieve.generate (Presieve.singleton q) ∈ Sheaf.canonicalTopology (RankSpace α) X ∧
      Nonempty (((rankCocyclePseudofunctor G α).map q.op.toLoc).toFunctor.obj A ≅
        ((rankPointInclusion G α).app ⟨op W⟩).toFunctor.obj a) := by
  obtain ⟨W,q,a,hq,e⟩ := rankCocycle_locallyPoint A hα hω hκ
  exact ⟨W,q,⟨a⟩,hq,e⟩

end

end Masullo.TopologicalGroupoid
