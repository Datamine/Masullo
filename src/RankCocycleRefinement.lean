import RankCocycleMorita

open CategoryTheory Opposite Function Cardinal Topology
open scoped Bicategory Pseudofunctor.StrongTrans Cardinal

namespace Masullo.TopologicalGroupoid

open QuotientCocycle

universe u

noncomputable section

variable {G H : TopologicalGroupoid.{u}} {α : Ordinal.{u}}

/-- Naturality of a stack morphism supplies its comparison with restriction
for a cocycle and every map of rank-site test spaces. -/
def rankStackMorphismPullbackIso
    (τ : rankCocyclePseudofunctor G α ⟶ rankCocyclePseudofunctor H α)
    {U V : RankSpace α} (f : U ⟶ V) (A : QuotientCocycle G V.space) :
    (τ.app ⟨op U⟩).toFunctor.obj (A.pullback ((rankSpaceInclusion α).map f)) ≅
      ((τ.app ⟨op V⟩).toFunctor.obj A).pullback ((rankSpaceInclusion α).map f) :=
  ((Cat.Hom.toNatIso (τ.naturality f.op.toLoc))).app A

/-- The restriction comparisons for a stack morphism agree along
composable maps, with the cocycle comparison for iterated pullback. -/
theorem rankStackMorphismPullbackIso_comp
    (τ : rankCocyclePseudofunctor G α ⟶ rankCocyclePseudofunctor H α)
    {R U V : RankSpace α} (f : R ⟶ U) (g : U ⟶ V) (A : QuotientCocycle G V.space) :
    let q := (rankSpaceInclusion α).map g
    let p := (rankSpaceInclusion α).map f
    let B := (τ.app ⟨op V⟩).toFunctor.obj A
    (rankStackMorphismPullbackIso τ (f ≫ g) A).hom ≫ (pullbackCompIso B q p).hom =
      (τ.app ⟨op R⟩).toFunctor.map (pullbackCompIso A q p).hom ≫
        (rankStackMorphismPullbackIso τ f (A.pullback q)).hom ≫
        pullbackHom (rankStackMorphismPullbackIso τ g A).hom p := by
  let q := (rankSpaceInclusion α).map g
  let p := (rankSpaceInclusion α).map f
  let B := (τ.app ⟨op V⟩).toFunctor.obj A
  let c := (rankStackMorphismPullbackIso τ (f ≫ g) A).hom
  let d := (pullbackCompIso B q p).hom
  let l := (τ.app ⟨op R⟩).toFunctor.map (pullbackCompIso A q p).hom
  let m := (rankStackMorphismPullbackIso τ f (A.pullback q)).hom
  let n := pullbackHom (rankStackMorphismPullbackIso τ g A).hom p
  have h := congrArg (fun t ↦ t.toNatTrans.app A) (τ.naturality_comp g.op.toLoc f.op.toLoc)
  change c ≫ d = l ≫ 𝟙 _ ≫ m ≫ 𝟙 _ ≫ n ≫ 𝟙 _ at h
  change c ≫ d = l ≫ m ≫ n
  exact h.trans (congrArg (l ≫ ·) ((Category.id_comp _).trans
    (congrArg (m ≫ ·) ((Category.id_comp _).trans (Category.comp_id _)))))

/-- Data obtained by restricting a morphism of quotient cocycle stacks to
the source's universal chart and choosing a presenting cover of its image. -/
structure RankChartRefinement
    (τ : rankCocyclePseudofunctor G α ⟶ rankCocyclePseudofunctor H α)
    {X : RankSpace α} (x : X.space.obj ≃ₜ G.objects.obj) where
  cover : RankSpace α
  map : cover ⟶ X
  isQuotient : IsQuotientMap ((rankSpaceInclusion α).map map).hom
  point : H.Points cover.space
  comparison :
    ((τ.app ⟨op X⟩).toFunctor.obj
      (ofPoint (⟨x, x.continuous⟩ : G.Points X.space))).pullback
        ((rankSpaceInclusion α).map map) ≅ ofPoint point

/-- A rank-site quotient cover admits a base change along every rank-site
map, with the pullback represented in the same rank. -/
theorem rankQuotientCover_baseChange {T U W : RankSpace α} (q : W ⟶ T) (f : U ⟶ T)
    (hα : preBeth α = α.card) (hω : ℵ₀ < preBeth α)
    (hq : IsQuotientMap ((rankSpaceInclusion α).map q).hom) :
    ∃ (V : RankSpace α) (p : V ⟶ U) (k : V ⟶ W),
      p ≫ f = k ≫ q ∧ IsQuotientMap ((rankSpaceInclusion α).map p).hom := by
  let I := rankSpaceInclusion α
  obtain ⟨V, ⟨e⟩⟩ := rankPairOverlap_representative q f hα hω
  let X := pairOverlap (I.map q) (I.map f)
  let l : V.space ⟶ X := CGWH.map ⟨e, e.continuous⟩
  let a := pairOverlapFirst (I.map q) (I.map f)
  let b := pairOverlapSecond (I.map q) (I.map f)
  let p := I.preimage (l ≫ b)
  let k := I.preimage (l ≫ a)
  have hp : I.map p = l ≫ b := I.map_preimage _
  have hk : I.map k = l ≫ a := I.map_preimage _
  refine ⟨V, p, k, I.map_injective ?_, ?_⟩
  · simp only [I.map_comp, hp, hk, Category.assoc]
    exact congrArg (l ≫ ·) (pairOverlap_comm (I.map q) (I.map f)).symm
  · rw [hp]
    exact (CGWH.quotient_baseChange (I.map q) (I.map f) hq).comp e.isQuotientMap

namespace RankChartRefinement

variable {τ : rankCocyclePseudofunctor G α ⟶ rankCocyclePseudofunctor H α}
  {X : RankSpace α} {x : X.space.obj ≃ₜ G.objects.obj}

def objectMap (r : RankChartRefinement τ x) : C(r.cover.space.obj, G.objects.obj) :=
  (⟨x, x.continuous⟩ : C(X.space.obj, G.objects.obj)).comp
    ((rankSpaceInclusion α).map r.map).hom.hom.hom

/-- The chosen trivialization identifies the image of the refined chart
point with an actual continuous point of the target groupoid. -/
def chartComparison (r : RankChartRefinement τ x) :
    (τ.app ⟨op r.cover⟩).toFunctor.obj (ofPoint (r.objectMap : G.Points r.cover.space)) ≅ ofPoint r.point :=
  ((τ.app ⟨op r.cover⟩).toFunctor.mapIso
    ((pointPresentationPullbackIso ((rankSpaceInclusion α).map r.map)).app
      (⟨x, x.continuous⟩ : G.Points X.space))) ≪≫
    rankStackMorphismPullbackIso τ r.map (ofPoint (⟨x, x.continuous⟩ : G.Points X.space)) ≪≫
    r.comparison

def sourcePoint (r : RankChartRefinement τ x) {T : RankSpace α} (f : T ⟶ r.cover) : G.Points T.space :=
  r.objectMap.comp ((rankSpaceInclusion α).map f).hom.hom.hom

def targetPoint (r : RankChartRefinement τ x) {T : RankSpace α} (f : T ⟶ r.cover) : H.Points T.space :=
  r.point.comp ((rankSpaceInclusion α).map f).hom.hom.hom

/-- Restriction to any test over the refined chart gives the corresponding
comparison between the images of the two chart points. -/
def comparisonOn (r : RankChartRefinement τ x) {T : RankSpace α} (f : T ⟶ r.cover) :
    (τ.app ⟨op T⟩).toFunctor.obj
      (ofPoint (r.sourcePoint f)) ≅
      ofPoint (r.targetPoint f) := by
  let q := (rankSpaceInclusion α).map f
  let a : G.Points r.cover.space := r.objectMap
  exact ((τ.app ⟨op T⟩).toFunctor.mapIso ((pointPresentationPullbackIso q).app a)) ≪≫
    rankStackMorphismPullbackIso τ f (ofPoint a) ≪≫
    (pullbackFunctor q).mapIso r.chartComparison ≪≫
    ((pointPresentationPullbackIso q).app r.point).symm

set_option maxHeartbeats 750000 in
theorem comparisonOn_comp (r : RankChartRefinement τ x) {S T : RankSpace α}
    (f : S ⟶ T) (g : T ⟶ r.cover) :
    let p := (rankSpaceInclusion α).map f
    (r.comparisonOn (f ≫ g)).hom ≫ ((pointPresentationPullbackIso p).app (r.targetPoint g)).hom =
      (τ.app ⟨op S⟩).toFunctor.map ((pointPresentationPullbackIso p).app (r.sourcePoint g)).hom ≫
        (rankStackMorphismPullbackIso τ f (ofPoint (r.sourcePoint g))).hom ≫
        pullbackHom (r.comparisonOn g).hom p := by
  let p : S.space ⟶ T.space := (rankSpaceInclusion α).map f
  let q : T.space ⟶ r.cover.space := (rankSpaceInclusion α).map g
  let P : QuotientCocycle G T.space ⥤ QuotientCocycle G S.space := pullbackFunctor p
  let Q : QuotientCocycle H T.space ⥤ QuotientCocycle H S.space := pullbackFunctor p
  let F : QuotientCocycle G S.space ⥤ QuotientCocycle H S.space := (τ.app ⟨op S⟩).toFunctor
  let E : QuotientCocycle G T.space ⥤ QuotientCocycle H T.space := (τ.app ⟨op T⟩).toFunctor
  let K : QuotientCocycle G r.cover.space ⥤ QuotientCocycle H r.cover.space := (τ.app ⟨op r.cover⟩).toFunctor
  let a : G.Points r.cover.space := r.objectMap
  let b := r.point
  let A := ofPoint a
  let B := ofPoint b
  let c : K.obj A ≅ B := r.chartComparison
  let l : ofPoint (r.sourcePoint g) ≅ A.pullback q := (pointPresentationPullbackIso q).app a
  let m : ofPoint (r.targetPoint g) ≅ B.pullback q := (pointPresentationPullbackIso q).app b
  let l₁ : ofPoint (r.sourcePoint (f ≫ g)) ≅ P.obj (ofPoint (r.sourcePoint g)) :=
    (pointPresentationPullbackIso p).app (r.sourcePoint g)
  let m₁ : ofPoint (r.targetPoint (f ≫ g)) ≅ Q.obj (ofPoint (r.targetPoint g)) :=
    (pointPresentationPullbackIso p).app (r.targetPoint g)
  let l₂ : ofPoint (r.sourcePoint (f ≫ g)) ≅ A.pullback (p ≫ q) :=
    (pointPresentationPullbackIso (p ≫ q)).app a
  let m₂ : ofPoint (r.targetPoint (f ≫ g)) ≅ B.pullback (p ≫ q) :=
    (pointPresentationPullbackIso (p ≫ q)).app b
  let L : A.pullback (p ≫ q) ≅ P.obj (A.pullback q) := pullbackCompIso A q p
  let M : (K.obj A).pullback (p ≫ q) ≅ Q.obj ((K.obj A).pullback q) := pullbackCompIso (K.obj A) q p
  let N : B.pullback (p ≫ q) ≅ Q.obj (B.pullback q) := pullbackCompIso B q p
  let n : F.obj (P.obj (ofPoint (r.sourcePoint g))) ≅ Q.obj (E.obj (ofPoint (r.sourcePoint g))) :=
    rankStackMorphismPullbackIso τ f _
  let n' : F.obj (P.obj (A.pullback q)) ≅ Q.obj (E.obj (A.pullback q)) :=
    rankStackMorphismPullbackIso τ f _
  let h : E.obj (A.pullback q) ≅ (K.obj A).pullback q := rankStackMorphismPullbackIso τ g A
  let h' : F.obj (A.pullback (p ≫ q)) ≅ (K.obj A).pullback (p ≫ q) :=
    rankStackMorphismPullbackIso τ (f ≫ g) A
  have hl : l₂.hom ≫ L.hom = l₁.hom ≫ P.map l.hom := pointRestrictionIso_comp q p a
  have hm : m₂.hom ≫ N.hom = m₁.hom ≫ Q.map m.hom := pointRestrictionIso_comp q p b
  have hc : pullbackHom c.hom (p ≫ q) ≫ N.hom =
      M.hom ≫ Q.map (pullbackHom c.hom q) :=
    (pullbackCompNatIso q p).hom.naturality c.hom
  have hn : F.map (P.map l.hom) ≫ n'.hom = n.hom ≫ Q.map (E.map l.hom) :=
    (Cat.Hom.toNatIso (τ.naturality f.op.toLoc)).hom.naturality l.hom
  have hh : h'.hom ≫ M.hom = F.map L.hom ≫ n'.hom ≫ Q.map h.hom :=
    rankStackMorphismPullbackIso_comp τ f g A
  change (F.map l₂.hom ≫ h'.hom ≫ pullbackHom c.hom (p ≫ q) ≫ m₂.inv) ≫ m₁.hom =
    F.map l₁.hom ≫ n.hom ≫ Q.map (E.map l.hom ≫ h.hom ≫ pullbackHom c.hom q ≫ m.inv)
  apply (cancel_mono (Q.map m.hom)).mp
  have cancel : Q.map m.inv ≫ Q.map m.hom = 𝟙 _ := by rw [← Q.map_comp, m.inv_hom_id, Q.map_id]
  simp only [Category.assoc, Q.map_comp, cancel, Category.comp_id]
  rw [← hm, Iso.inv_hom_id_assoc, hc, reassoc_of% hh]
  rw [← F.map_comp_assoc, hl, F.map_comp, Category.assoc, reassoc_of% hn]

def groupoid (r : RankChartRefinement τ x) : TopologicalGroupoid.{u} :=
  refineObjects r.objectMap

def projection (r : RankChartRefinement τ x) : r.groupoid ⟶ G :=
  refineObjectsProjection r.objectMap

/-- Transport the image of a continuous family of arrows by the two local
chart trivializations, then recover its unique continuous target family. -/
def compareArrow (r : RankChartRefinement τ x) {T : RankSpace α} (f g : T ⟶ r.cover)
    (a : r.sourcePoint f ⟶ r.sourcePoint g) : r.targetPoint f ⟶ r.targetPoint g :=
  (pointPresentation_fullyFaithful H T.space).preimage
    ((r.comparisonOn f).inv ≫ (τ.app ⟨op T⟩).toFunctor.map ((pointPresentation G T.space).map a) ≫
      (r.comparisonOn g).hom)

theorem compareArrow_square (r : RankChartRefinement τ x) {T : RankSpace α}
    (f g : T ⟶ r.cover) (a : r.sourcePoint f ⟶ r.sourcePoint g) :
    (τ.app ⟨op T⟩).toFunctor.map ((pointPresentation G T.space).map a) ≫ (r.comparisonOn g).hom =
      (r.comparisonOn f).hom ≫ (pointPresentation H T.space).map (r.compareArrow f g a) := by
  let P := pointPresentation H T.space
  let ff := pointPresentation_fullyFaithful H T.space
  let F : QuotientCocycle G T.space ⥤ QuotientCocycle H T.space := (τ.app ⟨op T⟩).toFunctor
  let A : F.obj (ofPoint (r.sourcePoint f)) ≅ ofPoint (r.targetPoint f) := r.comparisonOn f
  let B : F.obj (ofPoint (r.sourcePoint g)) ≅ ofPoint (r.targetPoint g) := r.comparisonOn g
  let v : F.obj (ofPoint (r.sourcePoint f)) ⟶ F.obj (ofPoint (r.sourcePoint g)) :=
    F.map ((pointPresentation G T.space).map a)
  change v ≫ B.hom = A.hom ≫ P.map (ff.preimage (A.inv ≫ v ≫ B.hom))
  rw [ff.map_preimage]
  exact (A.hom_inv_id_assoc _).symm

set_option maxHeartbeats 750000 in
/-- Applying the comparison to an arrow commutes with restriction of its
continuous family to any smaller test space. -/
theorem compareArrow_restrict (r : RankChartRefinement τ x) {S T : RankSpace α}
    (p : S ⟶ T) (f g : T ⟶ r.cover) (a : r.sourcePoint f ⟶ r.sourcePoint g) :
    r.compareArrow (p ≫ f) (p ≫ g)
      ((G.restrictPoints ((rankSpaceInclusion α).map p).hom.hom.hom).map a) =
      (H.restrictPoints ((rankSpaceInclusion α).map p).hom.hom.hom).map (r.compareArrow f g a) := by
  let q : S.space ⟶ T.space := (rankSpaceInclusion α).map p
  let P : QuotientCocycle G T.space ⥤ QuotientCocycle G S.space := pullbackFunctor q
  let Q : QuotientCocycle H T.space ⥤ QuotientCocycle H S.space := pullbackFunctor q
  let F : QuotientCocycle G S.space ⥤ QuotientCocycle H S.space := (τ.app ⟨op S⟩).toFunctor
  let E : QuotientCocycle G T.space ⥤ QuotientCocycle H T.space := (τ.app ⟨op T⟩).toFunctor
  let l : ofPoint (r.sourcePoint (p ≫ f)) ≅ P.obj (ofPoint (r.sourcePoint f)) :=
    (pointPresentationPullbackIso q).app (r.sourcePoint f)
  let m : ofPoint (r.sourcePoint (p ≫ g)) ≅ P.obj (ofPoint (r.sourcePoint g)) :=
    (pointPresentationPullbackIso q).app (r.sourcePoint g)
  let l' : ofPoint (r.targetPoint (p ≫ f)) ≅ Q.obj (ofPoint (r.targetPoint f)) :=
    (pointPresentationPullbackIso q).app (r.targetPoint f)
  let m' : ofPoint (r.targetPoint (p ≫ g)) ≅ Q.obj (ofPoint (r.targetPoint g)) :=
    (pointPresentationPullbackIso q).app (r.targetPoint g)
  let c : F.obj (ofPoint (r.sourcePoint (p ≫ f))) ≅ ofPoint (r.targetPoint (p ≫ f)) :=
    r.comparisonOn (p ≫ f)
  let d : F.obj (ofPoint (r.sourcePoint (p ≫ g))) ≅ ofPoint (r.targetPoint (p ≫ g)) :=
    r.comparisonOn (p ≫ g)
  let c' : E.obj (ofPoint (r.sourcePoint f)) ≅ ofPoint (r.targetPoint f) := r.comparisonOn f
  let d' : E.obj (ofPoint (r.sourcePoint g)) ≅ ofPoint (r.targetPoint g) := r.comparisonOn g
  let n : F.obj (P.obj (ofPoint (r.sourcePoint f))) ≅ Q.obj (E.obj (ofPoint (r.sourcePoint f))) :=
    rankStackMorphismPullbackIso τ p _
  let k : F.obj (P.obj (ofPoint (r.sourcePoint g))) ≅ Q.obj (E.obj (ofPoint (r.sourcePoint g))) :=
    rankStackMorphismPullbackIso τ p _
  let a' := (G.restrictPoints q.hom.hom.hom).map a
  let b := r.compareArrow f g a
  let b' := (H.restrictPoints q.hom.hom.hom).map b
  let a₀ : ofPoint (r.sourcePoint f) ⟶ ofPoint (r.sourcePoint g) :=
    (pointPresentation G T.space).map a
  let a₁ : ofPoint (r.sourcePoint (p ≫ f)) ⟶ ofPoint (r.sourcePoint (p ≫ g)) :=
    (pointPresentation G S.space).map a'
  let b₀ : ofPoint (r.targetPoint f) ⟶ ofPoint (r.targetPoint g) :=
    (pointPresentation H T.space).map b
  let b₁ : ofPoint (r.targetPoint (p ≫ f)) ⟶ ofPoint (r.targetPoint (p ≫ g)) :=
    (pointPresentation H S.space).map b'
  let b₂ : ofPoint (r.targetPoint (p ≫ f)) ⟶ ofPoint (r.targetPoint (p ≫ g)) :=
    (pointPresentation H S.space).map (r.compareArrow (p ≫ f) (p ≫ g) a')
  have hl : a₁ ≫ m.hom = l.hom ≫ P.map a₀ := (pointPresentationPullbackIso q).hom.naturality a
  have hm : b₁ ≫ m'.hom = l'.hom ≫ Q.map b₀ := (pointPresentationPullbackIso q).hom.naturality b
  have hc : c.hom ≫ l'.hom = F.map l.hom ≫ n.hom ≫ Q.map c'.hom := r.comparisonOn_comp p f
  have hd : d.hom ≫ m'.hom = F.map m.hom ≫ k.hom ≫ Q.map d'.hom := r.comparisonOn_comp p g
  have hn : F.map (P.map a₀) ≫ k.hom = n.hom ≫ Q.map (E.map a₀) :=
    (Cat.Hom.toNatIso (τ.naturality p.op.toLoc)).hom.naturality a₀
  have hb : E.map a₀ ≫ d'.hom = c'.hom ≫ b₀ := r.compareArrow_square f g a
  have hs : F.map a₁ ≫ d.hom = c.hom ≫ b₂ := r.compareArrow_square (p ≫ f) (p ≫ g) a'
  apply (pointPresentation_fullyFaithful H S.space).map_injective
  change b₂ = b₁
  apply (cancel_mono m'.hom).mp
  apply (cancel_epi c.hom).mp
  rw [← Category.assoc, ← hs, Category.assoc, hd, hm, reassoc_of% hc]
  rw [← F.map_comp_assoc, hl, F.map_comp, Category.assoc, reassoc_of% hn]
  rw [← Q.map_comp, hb, Q.map_comp]

theorem compareArrow_id (r : RankChartRefinement τ x) {T : RankSpace α} (f : T ⟶ r.cover) :
    r.compareArrow f f (𝟙 (r.sourcePoint f)) = 𝟙 (r.targetPoint f) := by
  let P := pointPresentation H T.space
  let F : QuotientCocycle G T.space ⥤ QuotientCocycle H T.space := (τ.app ⟨op T⟩).toFunctor
  let ff := pointPresentation_fullyFaithful H T.space
  apply ff.map_injective
  change P.map (ff.preimage _) = P.map (𝟙 _)
  rw [ff.map_preimage, P.map_id, (pointPresentation G T.space).map_id]
  let e := r.comparisonOn f
  change e.inv ≫ F.map (𝟙 (ofPoint (r.sourcePoint f))) ≫ e.hom = 𝟙 _
  exact (congrArg (fun k => e.inv ≫ k ≫ e.hom) (F.map_id _)).trans
    ((congrArg (e.inv ≫ ·) (Category.id_comp _)).trans e.inv_hom_id)

theorem compareArrow_comp (r : RankChartRefinement τ x) {T : RankSpace α}
    (f g h : T ⟶ r.cover)
    (a : r.sourcePoint f ⟶ r.sourcePoint g) (b : r.sourcePoint g ⟶ r.sourcePoint h) :
    r.compareArrow f h (a ≫ b) = (r.compareArrow f g a : r.targetPoint f ⟶ r.targetPoint g) ≫
      r.compareArrow g h b := by
  let P := pointPresentation H T.space
  let F : QuotientCocycle G T.space ⥤ QuotientCocycle H T.space := (τ.app ⟨op T⟩).toFunctor
  let ff := pointPresentation_fullyFaithful H T.space
  apply ff.map_injective
  change P.map (ff.preimage _) = P.map (ff.preimage _ ≫ ff.preimage _)
  rw [ff.map_preimage, P.map_comp, ff.map_preimage, ff.map_preimage,
    (pointPresentation G T.space).map_comp]
  let A : ofPoint (r.targetPoint f) ⟶ F.obj (ofPoint (r.sourcePoint f)) := (r.comparisonOn f).inv
  let E : F.obj (ofPoint (r.sourcePoint g)) ≅ ofPoint (r.targetPoint g) := r.comparisonOn g
  let B : F.obj (ofPoint (r.sourcePoint h)) ⟶ ofPoint (r.targetPoint h) := (r.comparisonOn h).hom
  let u : ofPoint (r.sourcePoint f) ⟶ ofPoint (r.sourcePoint g) := (pointPresentation G T.space).map a
  let v : ofPoint (r.sourcePoint g) ⟶ ofPoint (r.sourcePoint h) := (pointPresentation G T.space).map b
  change A ≫ F.map (u ≫ v) ≫ B = (A ≫ F.map u ≫ E.hom) ≫ E.inv ≫ F.map v ≫ B
  rw [F.map_comp]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

private def rankPointMap (r : RankChartRefinement τ x) {T : RankSpace α}
    (a : r.groupoid.Points T.space) : T ⟶ r.cover :=
  (rankSpaceInclusion α).preimage (CGWH.map a)

private theorem rankPointMap_apply (r : RankChartRefinement τ x) {T : RankSpace α}
    (a : r.groupoid.Points T.space) (t : T.space.obj) :
    ((rankSpaceInclusion α).map (r.rankPointMap a)).hom t = a t :=
  congrArg (fun g : T.space ⟶ r.cover.space ↦ g.hom t)
    ((rankSpaceInclusion α).map_preimage _)

private def projectTestArrow (r : RankChartRefinement τ x) {T : RankSpace α}
    {a b : r.groupoid.Points T.space} (v : a ⟶ b) :
    r.sourcePoint (r.rankPointMap a) ⟶ r.sourcePoint (r.rankPointMap b) := by
  let w := (mapPoints r.projection T.space).map v
  exact ⟨w.val,
    fun t ↦ (w.property.1 t).trans (congrArg r.objectMap (r.rankPointMap_apply a t).symm),
    fun t ↦ (w.property.2 t).trans (congrArg r.objectMap (r.rankPointMap_apply b t).symm)⟩

private theorem projectTestArrow_id (r : RankChartRefinement τ x) {T : RankSpace α}
    (a : r.groupoid.Points T.space) :
    r.projectTestArrow (𝟙 a) = 𝟙 (r.sourcePoint (r.rankPointMap a)) := by
  apply Subtype.ext
  exact ContinuousMap.ext (fun t ↦ (r.projection.mapUnit (a t)).trans
    (congrArg (fun z ↦ G.unit (r.objectMap z)) (r.rankPointMap_apply a t).symm))

private theorem projectTestArrow_comp (r : RankChartRefinement τ x) {T : RankSpace α}
    {a b c : r.groupoid.Points T.space} (v : a ⟶ b) (w : b ⟶ c) :
    r.projectTestArrow (v ≫ w) = r.projectTestArrow v ≫ r.projectTestArrow w := by
  apply Subtype.ext
  exact ContinuousMap.ext (fun t ↦ r.projection.mapComp (v.val t) (w.val t) _)

private def projectTestFunctor (r : RankChartRefinement τ x) (T : RankSpace α) :
    r.groupoid.Points T.space ⥤ G.Points T.space where
  obj a := r.sourcePoint (r.rankPointMap a)
  map v := r.projectTestArrow v
  map_id := r.projectTestArrow_id
  map_comp := r.projectTestArrow_comp

/-- Over each test space the chart trivializations conjugate the image
of the refined point groupoid into the target point groupoid. -/
def testFunctor (r : RankChartRefinement τ x) (T : RankSpace α) :
    r.groupoid.Points T.space ⥤ H.Points T.space where
  obj a := r.targetPoint (r.rankPointMap a)
  map {a b} v := r.compareArrow (r.rankPointMap a) (r.rankPointMap b) (r.projectTestArrow v)
  map_id a :=
    (congrArg (r.compareArrow (r.rankPointMap a) (r.rankPointMap a)) (r.projectTestArrow_id a)).trans
      (r.compareArrow_id (r.rankPointMap a))
  map_comp {a b c} v w :=
    (congrArg (r.compareArrow (r.rankPointMap a) (r.rankPointMap c)) (r.projectTestArrow_comp v w)).trans
      (r.compareArrow_comp (r.rankPointMap a) (r.rankPointMap b) (r.rankPointMap c)
        (r.projectTestArrow v) (r.projectTestArrow w))

private theorem compareArrow_congr_apply (r : RankChartRefinement τ x) {T : RankSpace α}
    {f f' g g' : T ⟶ r.cover} (hf : f = f') (hg : g = g')
    (a : r.sourcePoint f ⟶ r.sourcePoint g) (b : r.sourcePoint f' ⟶ r.sourcePoint g')
    (h : a.val = b.val) (t : T.space.obj) :
    (r.compareArrow f g a).val t = (r.compareArrow f' g' b).val t := by
  subst f' g'
  exact congrArg (fun v : r.sourcePoint f ⟶ r.sourcePoint g ↦ (r.compareArrow f g v).val t)
    (Subtype.ext h)

private theorem rankPointMap_restrict (r : RankChartRefinement τ x) {S T : RankSpace α}
    (p : S ⟶ T) (a : r.groupoid.Points T.space) :
    r.rankPointMap ((r.groupoid.restrictPoints ((rankSpaceInclusion α).map p).hom.hom.hom).obj a) =
      p ≫ r.rankPointMap a := by
  let I := rankSpaceInclusion α
  apply I.map_injective
  rw [I.map_comp]
  apply cgwhForget.map_injective
  apply ConcreteCategory.hom_ext
  intro t
  exact (r.rankPointMap_apply _ t).trans (r.rankPointMap_apply a ((I.map p).hom t)).symm

/-- Evaluations of the conjugated functor commute with every restriction
of a continuous family. -/
theorem testFunctor_restrict_apply (r : RankChartRefinement τ x) {S T : RankSpace α}
    (p : S ⟶ T) {a b : r.groupoid.Points T.space} (v : a ⟶ b) (s : S.space.obj) :
    ((r.testFunctor S).map
      ((r.groupoid.restrictPoints ((rankSpaceInclusion α).map p).hom.hom.hom).map v)).val s =
    ((r.testFunctor T).map v).val (((rankSpaceInclusion α).map p).hom s) := by
  let q := ((rankSpaceInclusion α).map p).hom.hom.hom
  let R := r.groupoid.restrictPoints q
  let w := r.projectTestArrow v
  let w' := (G.restrictPoints q).map w
  let s₀ := r.rankPointMap a
  let s₁ := r.rankPointMap b
  change (r.compareArrow (r.rankPointMap (R.obj a)) (r.rankPointMap (R.obj b))
    (r.projectTestArrow (R.map v))).val s = (r.compareArrow s₀ s₁ w).val (q s)
  exact (r.compareArrow_congr_apply (r.rankPointMap_restrict p a) (r.rankPointMap_restrict p b)
    (r.projectTestArrow (R.map v)) w' rfl s).trans
    (congrArg (fun u : r.targetPoint (p ≫ s₀) ⟶ r.targetPoint (p ≫ s₁) ↦ u.val s)
      (r.compareArrow_restrict p s₀ s₁ w))

private def universalSource (r : RankChartRefinement τ x) {Z : RankSpace α}
    (e : Z.space.obj ≃ₜ r.groupoid.arrows.obj) : r.groupoid.Points Z.space :=
  r.groupoid.source.comp ⟨e, e.continuous⟩

private def universalTarget (r : RankChartRefinement τ x) {Z : RankSpace α}
    (e : Z.space.obj ≃ₜ r.groupoid.arrows.obj) : r.groupoid.Points Z.space :=
  r.groupoid.target.comp ⟨e, e.continuous⟩

private def universalArrow (r : RankChartRefinement τ x) {Z : RankSpace α}
    (e : Z.space.obj ≃ₜ r.groupoid.arrows.obj) : r.universalSource e ⟶ r.universalTarget e :=
  ⟨⟨e, e.continuous⟩, fun _ ↦ rfl, fun _ ↦ rfl⟩

/-- Evaluate on a rank representative of the universal refined arrow to
obtain a continuous candidate for the arrow map of the second leg. -/
def arrowMap (r : RankChartRefinement τ x) {Z : RankSpace α}
    (e : Z.space.obj ≃ₜ r.groupoid.arrows.obj) :
    C(r.groupoid.arrows.obj, H.arrows.obj) :=
  ((r.testFunctor Z).map (r.universalArrow e)).val.comp ⟨e.symm, e.symm.continuous⟩

private theorem testFunctor_congr_apply (r : RankChartRefinement τ x) {T : RankSpace α}
    {a b a' b' : r.groupoid.Points T.space} (ha : a = a') (hb : b = b')
    (v : a ⟶ b) (w : a' ⟶ b') (h : v.val = w.val) (t : T.space.obj) :
    ((r.testFunctor T).map v).val t = ((r.testFunctor T).map w).val t := by
  subst a' b'
  exact congrArg (fun v : a ⟶ b ↦ ((r.testFunctor T).map v).val t) (Subtype.ext h)

/-- The continuous arrow map realizes every restriction of the universal
family, and every continuous family factors through that universal one. -/
theorem arrowMap_testFunctor_apply (r : RankChartRefinement τ x) {Z T : RankSpace α}
    (e : Z.space.obj ≃ₜ r.groupoid.arrows.obj) {a b : r.groupoid.Points T.space}
    (v : a ⟶ b) (t : T.space.obj) :
    r.arrowMap e (v.val t) = ((r.testFunctor T).map v).val t := by
  let I := rankSpaceInclusion α
  let k : T.space ⟶ Z.space :=
    CGWH.map ((⟨e.symm, e.symm.continuous⟩ : C(r.groupoid.arrows.obj, Z.space.obj)).comp v.val)
  let p := I.preimage k
  let P := r.groupoid.restrictPoints (I.map p).hom.hom.hom
  have hp (s : T.space.obj) : (I.map p).hom s = e.symm (v.val s) :=
    congrArg (fun g : T.space ⟶ Z.space ↦ g.hom s) (I.map_preimage k)
  have he (s : T.space.obj) : e ((I.map p).hom s) = v.val s :=
    (congrArg e (hp s)).trans (e.apply_symm_apply _)
  have ha : P.obj (r.universalSource e) = a :=
    ContinuousMap.ext fun s ↦ (congrArg r.groupoid.source (he s)).trans (v.property.1 s)
  have hb : P.obj (r.universalTarget e) = b :=
    ContinuousMap.ext fun s ↦ (congrArg r.groupoid.target (he s)).trans (v.property.2 s)
  have hv : (P.map (r.universalArrow e)).val = v.val := ContinuousMap.ext he
  calc
    _ = ((r.testFunctor Z).map (r.universalArrow e)).val ((I.map p).hom t) :=
      congrArg ((r.testFunctor Z).map (r.universalArrow e)).val (hp t).symm
    _ = ((r.testFunctor T).map (P.map (r.universalArrow e))).val t :=
      (r.testFunctor_restrict_apply p (r.universalArrow e) t).symm
    _ = _ := r.testFunctor_congr_apply ha hb (P.map (r.universalArrow e)) v hv t

theorem arrowMap_source (r : RankChartRefinement τ x) {Z : RankSpace α}
    (e : Z.space.obj ≃ₜ r.groupoid.arrows.obj) (a : r.groupoid.arrows.obj) :
    H.source (r.arrowMap e a) = r.point (r.groupoid.source a) := by
  let b := (r.testFunctor Z).map (r.universalArrow e)
  exact (b.property.1 (e.symm a)).trans
    (congrArg r.point ((r.rankPointMap_apply (r.universalSource e) (e.symm a)).trans
      (congrArg r.groupoid.source (e.apply_symm_apply a))))

theorem arrowMap_target (r : RankChartRefinement τ x) {Z : RankSpace α}
    (e : Z.space.obj ≃ₜ r.groupoid.arrows.obj) (a : r.groupoid.arrows.obj) :
    H.target (r.arrowMap e a) = r.point (r.groupoid.target a) := by
  let b := (r.testFunctor Z).map (r.universalArrow e)
  exact (b.property.2 (e.symm a)).trans
    (congrArg r.point ((r.rankPointMap_apply (r.universalTarget e) (e.symm a)).trans
      (congrArg r.groupoid.target (e.apply_symm_apply a))))

theorem testFunctor_obj_apply (r : RankChartRefinement τ x) {T : RankSpace α}
    (a : r.groupoid.Points T.space) (t : T.space.obj) :
    (r.testFunctor T).obj a t = r.point (a t) :=
  congrArg r.point (r.rankPointMap_apply a t)

private def constantPoint (r : RankChartRefinement τ x) (T : RankSpace α) (a : r.groupoid.objects.obj) :
    r.groupoid.Points T.space :=
  ContinuousMap.const _ a

private def constantArrow (r : RankChartRefinement τ x) (T : RankSpace α) (a : r.groupoid.arrows.obj) :
    r.constantPoint T (r.groupoid.source a) ⟶ r.constantPoint T (r.groupoid.target a) :=
  ⟨ContinuousMap.const _ a, fun _ ↦ rfl, fun _ ↦ rfl⟩

private def targetLegAt (r : RankChartRefinement τ x) {Z T : RankSpace α}
    (e : Z.space.obj ≃ₜ r.groupoid.arrows.obj) (t : T.space.obj) : r.groupoid ⟶ H where
  objectMap := r.point
  arrowMap := r.arrowMap e
  mapSource := r.arrowMap_source e
  mapTarget := r.arrowMap_target e
  mapUnit a := by
    let A := r.constantPoint T a
    let F := r.testFunctor T
    exact (r.arrowMap_testFunctor_apply e (𝟙 A) t).trans
      ((congrArg (fun v : F.obj A ⟶ F.obj A ↦ v.val t) (F.map_id A)).trans
        (congrArg H.unit (r.testFunctor_obj_apply A t)))
  mapInverse a := by
    let v := r.constantArrow T a
    let F := r.testFunctor T
    have hv : F.map (Groupoid.inv v) = Groupoid.inv (F.map v) := by
      rw [Groupoid.inv_eq_inv, Groupoid.inv_eq_inv, F.map_inv]
    exact (r.arrowMap_testFunctor_apply e (Groupoid.inv v) t).trans
      ((congrArg (fun w : F.obj (r.constantPoint T (r.groupoid.target a)) ⟶
          F.obj (r.constantPoint T (r.groupoid.source a)) ↦ w.val t) hv).trans
        (congrArg H.inverse (r.arrowMap_testFunctor_apply e v t).symm))
  mapComp a b hab := by
    let A := r.constantPoint T (r.groupoid.source a)
    let B := r.constantPoint T (r.groupoid.target a)
    let C := r.constantPoint T (r.groupoid.target b)
    let v : A ⟶ B := r.constantArrow T a
    let w : B ⟶ C := ⟨ContinuousMap.const _ b, fun _ ↦ hab.symm, fun _ ↦ rfl⟩
    let F := r.testFunctor T
    have he := congrArg (fun m : F.obj A ⟶ F.obj C ↦ m.val t) (F.map_comp v w)
    refine (r.arrowMap_testFunctor_apply e (v ≫ w) t).trans (he.trans ?_)
    apply congrArg (fun p : ComposableArrows H.source H.target ↦ H.comp p)
    exact Subtype.ext (Prod.ext (r.arrowMap_testFunctor_apply e v t).symm
      (r.arrowMap_testFunctor_apply e w t).symm)

/-- The continuous map of universal arrows preserves the groupoid laws,
as seen by evaluating functoriality on constant families. -/
def targetLeg (r : RankChartRefinement τ x) {Z : RankSpace α}
    (e : Z.space.obj ≃ₜ r.groupoid.arrows.obj)
    (hα : preBeth α = α.card) (hω : ℵ₀ < preBeth α) : r.groupoid ⟶ H :=
  let h := rankSpace_representative hα CGWH.basepointObject
    (show #(ULift.{u} Unit) < preBeth α from mk_le_aleph0.trans_lt hω)
  r.targetLegAt e (h.choose_spec.some.symm ⟨()⟩)

private theorem pointArrow_eqToHom_naturality {K : TopologicalGroupoid.{u}} {T : CGWH.{u}}
    {a a' b b' : K.Points T} (ha : a = a') (hb : b = b')
    (v : a ⟶ b) (w : a' ⟶ b') (h : v.val = w.val) :
    v ≫ eqToHom hb = eqToHom ha ≫ w := by
  subst a' b'
  have hv : v = w := Subtype.ext h
  simp [hv]

private def pointFunctorIsoOfVal {K : TopologicalGroupoid.{u}} {T : CGWH.{u}}
    {C : Type u} [Category.{u} C] (F L : C ⥤ K.Points T)
    (ho : ∀ a, F.obj a = L.obj a)
    (hm : ∀ ⦃a b : C⦄ (v : a ⟶ b), (F.map v).val = (L.map v).val) : F ≅ L :=
  NatIso.ofComponents (fun a ↦ eqToIso (ho a))
    (fun {a b} v ↦ pointArrow_eqToHom_naturality (ho a) (ho b) _ _ (hm v))

private def projectTestFunctorIso (r : RankChartRefinement τ x) (T : RankSpace α) :
    r.projectTestFunctor T ≅ mapPoints r.projection T.space :=
  pointFunctorIsoOfVal _ _
    (fun a ↦ ContinuousMap.ext fun t ↦ congrArg r.objectMap (r.rankPointMap_apply a t))
    (fun {_ _} _ ↦ rfl)

private def targetLegTestFunctorIso (r : RankChartRefinement τ x) (T : RankSpace α) {Z : RankSpace α}
    (e : Z.space.obj ≃ₜ r.groupoid.arrows.obj)
    (hα : preBeth α = α.card) (hω : ℵ₀ < preBeth α) :
    r.testFunctor T ≅ mapPoints (r.targetLeg e hα hω) T.space :=
  pointFunctorIsoOfVal _ _
    (fun a ↦ ContinuousMap.ext fun t ↦ r.testFunctor_obj_apply a t)
    (fun {_ _} v ↦ ContinuousMap.ext fun t ↦ (r.arrowMap_testFunctor_apply e v t).symm)

private def comparisonTransport (r : RankChartRefinement τ x) {T : RankSpace α}
    (f : T ⟶ r.cover) {a : G.Points T.space} {b : H.Points T.space}
    (ha : r.sourcePoint f = a) (hb : r.targetPoint f = b) :
    (τ.app ⟨op T⟩).toFunctor.obj (ofPoint a) ≅ ofPoint b :=
  (eqToIso (congrArg (fun y ↦ (τ.app ⟨op T⟩).toFunctor.obj (ofPoint y)) ha.symm)) ≪≫
    r.comparisonOn f ≪≫ eqToIso (congrArg ofPoint hb)

private theorem comparisonTransport_self (r : RankChartRefinement τ x) {T : RankSpace α}
    (f : T ⟶ r.cover) : r.comparisonTransport f rfl rfl = r.comparisonOn f := by
  apply Iso.ext
  exact (Category.id_comp _).trans (Category.comp_id _)

set_option maxHeartbeats 650000 in
private theorem comparisonTransport_restrict (r : RankChartRefinement τ x) {S T : RankSpace α}
    (p : S ⟶ T) (f : T ⟶ r.cover) {a : G.Points T.space} {b : H.Points T.space}
    (ha : r.sourcePoint f = a) (hb : r.targetPoint f = b) :
    let q := (rankSpaceInclusion α).map p
    let L := G.restrictPoints q.hom.hom.hom
    let R := H.restrictPoints q.hom.hom.hom
    (r.comparisonTransport (p ≫ f) (congrArg L.obj ha) (congrArg R.obj hb)).hom ≫
        ((pointPresentationPullbackIso q).app b).hom =
      (τ.app ⟨op S⟩).toFunctor.map ((pointPresentationPullbackIso q).app a).hom ≫
        (rankStackMorphismPullbackIso τ p (ofPoint a)).hom ≫
        pullbackHom (r.comparisonTransport f ha hb).hom q := by
  subst a b
  let q : S.space ⟶ T.space := (rankSpaceInclusion α).map p
  let F : QuotientCocycle G S.space ⥤ QuotientCocycle H S.space := (τ.app ⟨op S⟩).toFunctor
  let E : QuotientCocycle G T.space ⥤ QuotientCocycle H T.space := (τ.app ⟨op T⟩).toFunctor
  let tl : ofPoint (r.targetPoint (p ≫ f)) ≅ (ofPoint (r.targetPoint f)).pullback q :=
    (pointPresentationPullbackIso q).app (r.targetPoint f)
  let sl : ofPoint (r.sourcePoint (p ≫ f)) ≅ (ofPoint (r.sourcePoint f)).pullback q :=
    (pointPresentationPullbackIso q).app (r.sourcePoint f)
  let n : F.obj ((ofPoint (r.sourcePoint f)).pullback q) ≅
      (E.obj (ofPoint (r.sourcePoint f))).pullback q := rankStackMorphismPullbackIso τ p _
  let c : F.obj (ofPoint (r.sourcePoint (p ≫ f))) ≅ ofPoint (r.targetPoint (p ≫ f)) :=
    r.comparisonTransport (p ≫ f) rfl rfl
  let d : E.obj (ofPoint (r.sourcePoint f)) ≅ ofPoint (r.targetPoint f) :=
    r.comparisonTransport f rfl rfl
  change c.hom ≫ tl.hom = F.map sl.hom ≫ n.hom ≫ pullbackHom d.hom q
  have hc : c = r.comparisonOn (p ≫ f) := r.comparisonTransport_self _
  have hd : d = r.comparisonOn f := r.comparisonTransport_self _
  rw [hc, hd]
  exact r.comparisonOn_comp p f

private theorem comparisonTransport_congr (r : RankChartRefinement τ x) {T : RankSpace α}
    {f g : T ⟶ r.cover} (h : f = g) {a : G.Points T.space} {b : H.Points T.space}
    (hf : r.sourcePoint f = a) (hg : r.sourcePoint g = a)
    (kf : r.targetPoint f = b) (kg : r.targetPoint g = b) :
    r.comparisonTransport f hf kf = r.comparisonTransport g hg kg := by
  subst g
  rfl

private def chartObjectComparison (r : RankChartRefinement τ x) {T : RankSpace α} {Z : RankSpace α}
    (e : Z.space.obj ≃ₜ r.groupoid.arrows.obj)
    (hα : preBeth α = α.card) (hω : ℵ₀ < preBeth α) (a : r.groupoid.Points T.space) :
    (τ.app ⟨op T⟩).toFunctor.obj (ofPoint ((mapPoints r.projection T.space).obj a)) ≅
      ofPoint ((mapPoints (r.targetLeg e hα hω) T.space).obj a) :=
  r.comparisonTransport (r.rankPointMap a)
    (ContinuousMap.ext fun t ↦ congrArg r.objectMap (r.rankPointMap_apply a t))
    (ContinuousMap.ext fun t ↦ r.testFunctor_obj_apply a t)

set_option maxHeartbeats 750000 in
private theorem chartObjectComparison_restrict (r : RankChartRefinement τ x)
    {S T Z : RankSpace α} (e : Z.space.obj ≃ₜ r.groupoid.arrows.obj)
    (hα : preBeth α = α.card) (hω : ℵ₀ < preBeth α) (p : S ⟶ T) (a : r.groupoid.Points T.space) :
    let q := (rankSpaceInclusion α).map p
    let b := (r.groupoid.restrictPoints q.hom.hom.hom).obj a
    let s := (mapPoints r.projection T.space).obj a
    let t := (mapPoints (r.targetLeg e hα hω) T.space).obj a
    (r.chartObjectComparison e hα hω b).hom ≫ ((pointPresentationPullbackIso q).app t).hom =
      (τ.app ⟨op S⟩).toFunctor.map ((pointPresentationPullbackIso q).app s).hom ≫
      (rankStackMorphismPullbackIso τ p (ofPoint s)).hom ≫
      pullbackHom (r.chartObjectComparison e hα hω a).hom q := by
  let q : S.space ⟶ T.space := (rankSpaceInclusion α).map p
  let b := (r.groupoid.restrictPoints q.hom.hom.hom).obj a
  let s := (mapPoints r.projection T.space).obj a
  let t := (mapPoints (r.targetLeg e hα hω) T.space).obj a
  let L := G.restrictPoints q.hom.hom.hom
  let R := H.restrictPoints q.hom.hom.hom
  let hs : r.sourcePoint (r.rankPointMap a) = s :=
    ContinuousMap.ext fun v ↦ congrArg r.objectMap (r.rankPointMap_apply a v)
  let ht : r.targetPoint (r.rankPointMap a) = t :=
    ContinuousMap.ext fun v ↦ r.testFunctor_obj_apply a v
  let hs' : r.sourcePoint (r.rankPointMap b) = L.obj s :=
    ContinuousMap.ext fun v ↦ congrArg r.objectMap (r.rankPointMap_apply b v)
  let ht' : r.targetPoint (r.rankPointMap b) = R.obj t :=
    ContinuousMap.ext fun v ↦ r.testFunctor_obj_apply b v
  let F : QuotientCocycle G S.space ⥤ QuotientCocycle H S.space := (τ.app ⟨op S⟩).toFunctor
  let E : QuotientCocycle G T.space ⥤ QuotientCocycle H T.space := (τ.app ⟨op T⟩).toFunctor
  let a₁ : F.obj (ofPoint (L.obj s)) ≅ ofPoint (R.obj t) := r.chartObjectComparison e hα hω b
  let a₂ : F.obj (ofPoint (L.obj s)) ≅ ofPoint (R.obj t) :=
    r.comparisonTransport (p ≫ r.rankPointMap a) (congrArg L.obj hs) (congrArg R.obj ht)
  let a₃ : E.obj (ofPoint s) ≅ ofPoint t := r.chartObjectComparison e hα hω a
  let m : ofPoint (R.obj t) ⟶ (ofPoint t).pullback q := ((pointPresentationPullbackIso q).app t).hom
  let l : ofPoint (L.obj s) ⟶ (ofPoint s).pullback q := ((pointPresentationPullbackIso q).app s).hom
  let n : F.obj ((ofPoint s).pullback q) ≅ (E.obj (ofPoint s)).pullback q :=
    rankStackMorphismPullbackIso τ p (ofPoint s)
  have h : a₁ = a₂ := r.comparisonTransport_congr (r.rankPointMap_restrict p a) hs' (congrArg L.obj hs)
    ht' (congrArg R.obj ht)
  change a₁.hom ≫ m = F.map l ≫ n.hom ≫ pullbackHom a₃.hom q
  rw [h]
  exact r.comparisonTransport_restrict p _ hs ht

private def chartTestComparison (r : RankChartRefinement τ x) (T : RankSpace α) :
    (r.projectTestFunctor T ⋙ pointPresentation G T.space) ⋙ (τ.app ⟨op T⟩).toFunctor ≅
      r.testFunctor T ⋙ pointPresentation H T.space :=
  NatIso.ofComponents (fun a ↦ r.comparisonOn (r.rankPointMap a))
    (fun v ↦ r.compareArrow_square _ _ (r.projectTestArrow v))

/-- On every fibre the constructed target leg gives the original stack
morphism after the Morita leg, on the full subcategory of continuous points. -/
def pointFactorization (r : RankChartRefinement τ x) (T : RankSpace α) {Z : RankSpace α}
    (e : Z.space.obj ≃ₜ r.groupoid.arrows.obj)
    (hα : preBeth α = α.card) (hω : ℵ₀ < preBeth α) :
    (pointPresentation r.groupoid T.space ⋙ mapCocycles r.projection) ⋙ (τ.app ⟨op T⟩).toFunctor ≅
      pointPresentation r.groupoid T.space ⋙ mapCocycles (r.targetLeg e hα hω) :=
  Functor.isoWhiskerRight (pointPresentationPushforwardIso r.projection).symm _ ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerRight (r.projectTestFunctorIso T).symm (pointPresentation G T.space))
      (τ.app ⟨op T⟩).toFunctor ≪≫
    r.chartTestComparison T ≪≫
    Functor.isoWhiskerRight (r.targetLegTestFunctorIso T e hα hω) _ ≪≫
    pointPresentationPushforwardIso (r.targetLeg e hα hω)

set_option maxHeartbeats 750000 in
private theorem pointFactorization_app (r : RankChartRefinement τ x) (T : RankSpace α) {Z : RankSpace α}
    (e : Z.space.obj ≃ₜ r.groupoid.arrows.obj)
    (hα : preBeth α = α.card) (hω : ℵ₀ < preBeth α) (a : r.groupoid.Points T.space) :
    (r.pointFactorization T e hα hω).hom.app a =
      (τ.app ⟨op T⟩).toFunctor.map (pointImageIso r.projection a).inv ≫
        (r.chartObjectComparison e hα hω a).hom ≫
        (pointImageIso (r.targetLeg e hα hω) a).hom := by
  let f := r.rankPointMap a
  let s := (mapPoints r.projection T.space).obj a
  let t := (mapPoints (r.targetLeg e hα hω) T.space).obj a
  let hs : r.sourcePoint f = s :=
    ContinuousMap.ext fun v ↦ congrArg r.objectMap (r.rankPointMap_apply a v)
  let ht : r.targetPoint f = t :=
    ContinuousMap.ext fun v ↦ r.testFunctor_obj_apply a v
  let F : QuotientCocycle G T.space ⥤ QuotientCocycle H T.space := (τ.app ⟨op T⟩).toFunctor
  let P := pointPresentation G T.space
  let Q := pointPresentation H T.space
  let A : ofPoint s ≅ (ofPoint a).map r.projection := pointImageIso r.projection a
  let B : ofPoint t ≅ (ofPoint a).map (r.targetLeg e hα hω) := pointImageIso (r.targetLeg e hα hω) a
  let C : F.obj (ofPoint (r.sourcePoint f)) ≅ ofPoint (r.targetPoint f) := r.comparisonOn f
  let V : F.obj (ofPoint s) ≅ ofPoint t := r.chartObjectComparison e hα hω a
  change F.map A.inv ≫ F.map (P.map (eqToHom hs.symm)) ≫ C.hom ≫ Q.map (eqToHom ht) ≫ B.hom =
    F.map A.inv ≫ V.hom ≫ B.hom
  have hv : V.hom = eqToHom (congrArg (fun y ↦ F.obj (ofPoint y)) hs.symm) ≫
      C.hom ≫ eqToHom (congrArg ofPoint ht) := rfl
  have hsMap := eqToHom_map (P ⋙ F) hs.symm
  have htMap := eqToHom_map Q ht
  let a₀ := F.map A.inv
  let c₀ := C.hom
  let b₀ := B.hom
  exact (congrArg (fun (k : F.obj (ofPoint s) ⟶ F.obj (ofPoint (r.sourcePoint f))) ↦
    a₀ ≫ k ≫ c₀ ≫ Q.map (eqToHom ht) ≫ b₀) hsMap).trans
    ((congrArg (fun (k : ofPoint (r.targetPoint f) ⟶ ofPoint t) ↦
      a₀ ≫ eqToHom (congrArg (fun y ↦ F.obj (ofPoint y)) hs.symm) ≫ c₀ ≫ k ≫ b₀) htMap).trans
      (by rw [hv]; simp only [Category.assoc]; rfl))

set_option maxHeartbeats 900000 in
/-- The factorization isomorphisms on points respect Cartesian pullback. -/
theorem pointFactorization_restrict (r : RankChartRefinement τ x) {S T Z : RankSpace α}
    (e : Z.space.obj ≃ₜ r.groupoid.arrows.obj)
    (hα : preBeth α = α.card) (hω : ℵ₀ < preBeth α) (p : S ⟶ T) (a : r.groupoid.Points T.space) :
    let q := (rankSpaceInclusion α).map p
    let b := (r.groupoid.restrictPoints q.hom.hom.hom).obj a
    let l := ((pointPresentationPullbackIso q).app a).hom
    (r.pointFactorization S e hα hω).hom.app b ≫ mapHom (r.targetLeg e hα hω) l =
      (τ.app ⟨op S⟩).toFunctor.map (mapHom r.projection l) ≫
        (rankStackMorphismPullbackIso τ p ((ofPoint a).map r.projection)).hom ≫
        pullbackHom ((r.pointFactorization T e hα hω).hom.app a) q := by
  let q : S.space ⟶ T.space := (rankSpaceInclusion α).map p
  let b := (r.groupoid.restrictPoints q.hom.hom.hom).obj a
  let g := r.projection
  let h := r.targetLeg e hα hω
  let s := (mapPoints g T.space).obj a
  let t := (mapPoints h T.space).obj a
  let s' := (mapPoints g S.space).obj b
  let t' := (mapPoints h S.space).obj b
  let P : QuotientCocycle G T.space ⥤ QuotientCocycle G S.space := pullbackFunctor q
  let Q : QuotientCocycle H T.space ⥤ QuotientCocycle H S.space := pullbackFunctor q
  let F : QuotientCocycle G S.space ⥤ QuotientCocycle H S.space := (τ.app ⟨op S⟩).toFunctor
  let E : QuotientCocycle G T.space ⥤ QuotientCocycle H T.space := (τ.app ⟨op T⟩).toFunctor
  let L : ofPoint b ⟶ (ofPoint a).pullback q := ((pointPresentationPullbackIso q).app a).hom
  let l : ofPoint s' ⟶ P.obj (ofPoint s) := ((pointPresentationPullbackIso q).app s).hom
  let m : ofPoint t' ⟶ Q.obj (ofPoint t) := ((pointPresentationPullbackIso q).app t).hom
  let Lg : (ofPoint b).map g ⟶ P.obj ((ofPoint a).map g) := mapHom g L
  let Lh : (ofPoint b).map h ⟶ Q.obj ((ofPoint a).map h) := mapHom h L
  let A : ofPoint s ≅ (ofPoint a).map g := pointImageIso g a
  let A' : ofPoint s' ≅ (ofPoint b).map g := pointImageIso g b
  let B : ofPoint t ≅ (ofPoint a).map h := pointImageIso h a
  let B' : ofPoint t' ≅ (ofPoint b).map h := pointImageIso h b
  let C : E.obj (ofPoint s) ≅ ofPoint t := r.chartObjectComparison e hα hω a
  let C' : F.obj (ofPoint s') ≅ ofPoint t' := r.chartObjectComparison e hα hω b
  let N : F.obj (P.obj ((ofPoint a).map g)) ≅ Q.obj (E.obj ((ofPoint a).map g)) :=
    rankStackMorphismPullbackIso τ p _
  let M : F.obj (P.obj (ofPoint s)) ≅ Q.obj (E.obj (ofPoint s)) :=
    rankStackMorphismPullbackIso τ p _
  let θ : E.obj ((ofPoint a).map g) ⟶ (ofPoint a).map h := (r.pointFactorization T e hα hω).hom.app a
  let θ' : F.obj ((ofPoint b).map g) ⟶ (ofPoint b).map h := (r.pointFactorization S e hα hω).hom.app b
  have ha : l ≫ P.map A.hom = A'.hom ≫ Lg := pointPresentationPushforwardIso_pullback g q a
  have hb : m ≫ Q.map B.hom = B'.hom ≫ Lh := pointPresentationPushforwardIso_pullback h q a
  have hc : C'.hom ≫ m = F.map l ≫ M.hom ≫ Q.map C.hom :=
    r.chartObjectComparison_restrict e hα hω p a
  have hn : F.map (P.map A.hom) ≫ N.hom = M.hom ≫ Q.map (E.map A.hom) :=
    (Cat.Hom.toNatIso (τ.naturality p.op.toLoc)).hom.naturality A.hom
  have ht : θ = E.map A.inv ≫ C.hom ≫ B.hom := r.pointFactorization_app T e hα hω a
  have ht' : θ' = F.map A'.inv ≫ C'.hom ≫ B'.hom := r.pointFactorization_app S e hα hω b
  let j := F.mapIso A'
  change θ' ≫ Lh = F.map Lg ≫ N.hom ≫ Q.map θ
  apply (cancel_epi j.hom).mp
  rw [ht, ht']
  change j.hom ≫ (j.inv ≫ C'.hom ≫ B'.hom) ≫ Lh = j.hom ≫ F.map Lg ≫ N.hom ≫
    Q.map (E.map A.inv ≫ C.hom ≫ B.hom)
  simp only [Category.assoc, j.hom_inv_id_assoc, Q.map_comp]
  rw [← hb, reassoc_of% hc]
  change _ = F.map A'.hom ≫ F.map Lg ≫ N.hom ≫ _
  rw [← F.map_comp_assoc, ← ha, F.map_comp, Category.assoc, reassoc_of% hn]
  have hcancel : Q.map (E.map A.hom) ≫ Q.map (E.map A.inv) = 𝟙 _ := by
    rw [← Q.map_comp, ← E.map_comp, A.hom_inv_id, E.map_id, Q.map_id]
  rw [reassoc_of% hcancel]

/-- Transport the factorization along an isomorphism from a cocycle to a
continuous point presentation over the same base. -/
def factorizationAtPresentation (r : RankChartRefinement τ x) {T Z : RankSpace α}
    (e : Z.space.obj ≃ₜ r.groupoid.arrows.obj)
    (hα : preBeth α = α.card) (hω : ℵ₀ < preBeth α)
    {A : QuotientCocycle r.groupoid T.space} {a : r.groupoid.Points T.space}
    (i : A ≅ ofPoint a) :
    (τ.app ⟨op T⟩).toFunctor.obj (A.map r.projection) ≅ A.map (r.targetLeg e hα hω) :=
  ((mapCocycles r.projection ⋙ (τ.app ⟨op T⟩).toFunctor).mapIso i) ≪≫
    (r.pointFactorization T e hα hω).app a ≪≫
    ((mapCocycles (r.targetLeg e hα hω)).mapIso i.symm)

set_option maxHeartbeats 650000 in
/-- The transported comparison is natural for arbitrary morphisms between
cocycles with point presentations, including changes of the presentation. -/
theorem factorizationAtPresentation_natural (r : RankChartRefinement τ x) {T Z : RankSpace α}
    (e : Z.space.obj ≃ₜ r.groupoid.arrows.obj)
    (hα : preBeth α = α.card) (hω : ℵ₀ < preBeth α)
    {A B : QuotientCocycle r.groupoid T.space} {a b : r.groupoid.Points T.space}
    (i : A ≅ ofPoint a) (j : B ≅ ofPoint b) (v : A ⟶ B) :
    (τ.app ⟨op T⟩).toFunctor.map (mapHom r.projection v) ≫
      (r.factorizationAtPresentation e hα hω j).hom =
        (r.factorizationAtPresentation e hα hω i).hom ≫ mapHom (r.targetLeg e hα hω) v := by
  let I := pointPresentation r.groupoid T.space
  let ff := pointPresentation_fullyFaithful r.groupoid T.space
  let C : QuotientCocycle G T.space ⥤ QuotientCocycle H T.space := (τ.app ⟨op T⟩).toFunctor
  let F : QuotientCocycle r.groupoid T.space ⥤ QuotientCocycle H T.space := mapCocycles r.projection ⋙ C
  let L : QuotientCocycle r.groupoid T.space ⥤ QuotientCocycle H T.space :=
    mapCocycles (r.targetLeg e hα hω)
  let η := r.pointFactorization T e hα hω
  let ea : F.obj (ofPoint a) ⟶ L.obj (ofPoint a) := η.hom.app a
  let eb : F.obj (ofPoint b) ⟶ L.obj (ofPoint b) := η.hom.app b
  let w : a ⟶ b := ff.preimage (i.inv ≫ v ≫ j.hom)
  let u : ofPoint a ⟶ ofPoint b := I.map w
  let lj := L.mapIso j
  let li := L.mapIso i
  have hw : u = i.inv ≫ v ≫ j.hom := ff.map_preimage _
  have hu : v ≫ j.hom = i.hom ≫ u := by rw [hw, i.hom_inv_id_assoc]
  have hv : i.inv ≫ v ≫ j.hom = u := hw.symm
  have hn : F.map u ≫ eb = ea ≫ L.map u := η.hom.naturality w
  change F.map v ≫ (F.map j.hom ≫ eb ≫ lj.inv) =
    (F.map i.hom ≫ ea ≫ li.inv) ≫ L.map v
  apply (cancel_mono lj.hom).mp
  simp only [Category.assoc, lj.inv_hom_id, Category.comp_id]
  rw [← F.map_comp_assoc, hu, F.map_comp, Category.assoc, hn]
  change F.map i.hom ≫ ea ≫ L.map u = F.map i.hom ≫ ea ≫ L.map i.inv ≫ L.map v ≫ L.map j.hom
  rw [← L.map_comp, ← L.map_comp, hv]

set_option maxHeartbeats 800000 in
/-- A presentation and its restricted presentation give compatible local
factorizations, with the strong morphism's comparison inserted. -/
theorem factorizationAtPresentation_restrict (r : RankChartRefinement τ x) {S T Z : RankSpace α}
    (e : Z.space.obj ≃ₜ r.groupoid.arrows.obj)
    (hα : preBeth α = α.card) (hω : ℵ₀ < preBeth α) (p : S ⟶ T)
    {A : QuotientCocycle r.groupoid T.space} {a : r.groupoid.Points T.space}
    (i : A ≅ ofPoint a) :
    let q := (rankSpaceInclusion α).map p
    let i' := (pullbackFunctor q).mapIso i ≪≫ ((pointPresentationPullbackIso q).app a).symm
    (r.factorizationAtPresentation e hα hω i').hom =
      (rankStackMorphismPullbackIso τ p (A.map r.projection)).hom ≫
        pullbackHom (r.factorizationAtPresentation e hα hω i).hom q := by
  let q : S.space ⟶ T.space := (rankSpaceInclusion α).map p
  let g := r.projection
  let h := r.targetLeg e hα hω
  let P : QuotientCocycle r.groupoid T.space ⥤ QuotientCocycle r.groupoid S.space := pullbackFunctor q
  let Q : QuotientCocycle H T.space ⥤ QuotientCocycle H S.space := pullbackFunctor q
  let F : QuotientCocycle G S.space ⥤ QuotientCocycle H S.space := (τ.app ⟨op S⟩).toFunctor
  let E : QuotientCocycle G T.space ⥤ QuotientCocycle H T.space := (τ.app ⟨op T⟩).toFunctor
  let M : QuotientCocycle r.groupoid S.space ⥤ QuotientCocycle H S.space := mapCocycles g ⋙ F
  let M₀ : QuotientCocycle r.groupoid T.space ⥤ QuotientCocycle H T.space := mapCocycles g ⋙ E
  let N : QuotientCocycle r.groupoid S.space ⥤ QuotientCocycle H S.space := mapCocycles h
  let N₀ : QuotientCocycle r.groupoid T.space ⥤ QuotientCocycle H T.space := mapCocycles h
  let b := (r.groupoid.restrictPoints q.hom.hom.hom).obj a
  let l : ofPoint b ≅ P.obj (ofPoint a) := (pointPresentationPullbackIso q).app a
  let Y : M.obj (P.obj A) ≅ Q.obj (M₀.obj A) := rankStackMorphismPullbackIso τ p (A.map g)
  let Y' : M.obj (P.obj (ofPoint a)) ≅ Q.obj (M₀.obj (ofPoint a)) :=
    rankStackMorphismPullbackIso τ p ((ofPoint a).map g)
  let θ : M₀.obj (ofPoint a) ⟶ N₀.obj (ofPoint a) := (r.pointFactorization T e hα hω).hom.app a
  let θ' : M.obj (ofPoint b) ⟶ N.obj (ofPoint b) := (r.pointFactorization S e hα hω).hom.app b
  let d := M.mapIso l
  have hi : θ' ≫ N.map l.hom = d.hom ≫ Y'.hom ≫ Q.map θ :=
    r.pointFactorization_restrict e hα hω p a
  have hn : M.map (P.map i.hom) ≫ Y'.hom = Y.hom ≫ Q.map (M₀.map i.hom) :=
    (Cat.Hom.toNatIso (τ.naturality p.op.toLoc)).hom.naturality (mapHom g i.hom)
  change M.map (P.map i.hom ≫ l.inv) ≫ θ' ≫ N.map (l.hom ≫ P.map i.inv) =
    Y.hom ≫ Q.map (M₀.map i.hom ≫ θ ≫ N₀.map i.inv)
  simp only [M.map_comp, N.map_comp, Category.assoc]
  rw [reassoc_of% hi]
  change M.map (P.map i.hom) ≫ d.inv ≫ (d.hom ≫ Y'.hom ≫ Q.map θ) ≫ Q.map (N₀.map i.inv) =
    Y.hom ≫ Q.map (M₀.map i.hom ≫ θ ≫ N₀.map i.inv)
  simp only [Q.map_comp, Category.assoc, d.inv_hom_id_assoc]
  rw [reassoc_of% hn]

/-- A cocycle with two point presentations receives the same comparison
from either one. -/
theorem factorizationAtPresentation_independent (r : RankChartRefinement τ x) {T Z : RankSpace α}
    (e : Z.space.obj ≃ₜ r.groupoid.arrows.obj)
    (hα : preBeth α = α.card) (hω : ℵ₀ < preBeth α)
    {A : QuotientCocycle r.groupoid T.space} {a b : r.groupoid.Points T.space}
    (i : A ≅ ofPoint a) (j : A ≅ ofPoint b) :
    r.factorizationAtPresentation e hα hω i = r.factorizationAtPresentation e hα hω j := by
  let F : QuotientCocycle r.groupoid T.space ⥤ QuotientCocycle H T.space :=
    mapCocycles r.projection ⋙ (τ.app ⟨op T⟩).toFunctor
  let P : QuotientCocycle r.groupoid T.space ⥤ QuotientCocycle H T.space :=
    mapCocycles (r.targetLeg e hα hω)
  let l : F.obj A ⟶ P.obj A := (r.factorizationAtPresentation e hα hω i).hom
  let m : F.obj A ⟶ P.obj A := (r.factorizationAtPresentation e hα hω j).hom
  have h : F.map (𝟙 A) ≫ m = l ≫ P.map (𝟙 A) :=
    r.factorizationAtPresentation_natural e hα hω i j (𝟙 A)
  apply Iso.ext
  change l = m
  rw [F.map_id, P.map_id, Category.id_comp, Category.comp_id] at h
  exact h.symm

/-- Express the local comparison as an isomorphism between the
restrictions of the two global images of the cocycle. -/
def factorizationOnCover (r : RankChartRefinement τ x) {T W Z : RankSpace α}
    (e : Z.space.obj ≃ₜ r.groupoid.arrows.obj)
    (hα : preBeth α = α.card) (hω : ℵ₀ < preBeth α) (q : W ⟶ T)
    {A : QuotientCocycle r.groupoid T.space} {a : r.groupoid.Points W.space}
    (i : A.pullback ((rankSpaceInclusion α).map q) ≅ ofPoint a) :
    ((τ.app ⟨op T⟩).toFunctor.obj (A.map r.projection)).pullback ((rankSpaceInclusion α).map q) ≅
      (A.map (r.targetLeg e hα hω)).pullback ((rankSpaceInclusion α).map q) :=
  (rankStackMorphismPullbackIso τ q (A.map r.projection)).symm ≪≫
    r.factorizationAtPresentation e hα hω i

set_option maxHeartbeats 900000 in
/-- Pullback of the local factorization, expressed on the composite
cover, is the factorization given by the induced point presentation. -/
theorem factorizationOnCover_rebracket (r : RankChartRefinement τ x) {T W V Z : RankSpace α}
    (e : Z.space.obj ≃ₜ r.groupoid.arrows.obj)
    (hα : preBeth α = α.card) (hω : ℵ₀ < preBeth α) (q : W ⟶ T) (p : V ⟶ W)
    {A : QuotientCocycle r.groupoid T.space} {a : r.groupoid.Points W.space}
    (i : A.pullback ((rankSpaceInclusion α).map q) ≅ ofPoint a) :
    let k := (rankSpaceInclusion α).map q
    let m := (rankSpaceInclusion α).map p
    let j := pullbackCompIso A k m ≪≫ (pullbackFunctor m).mapIso i ≪≫
      ((pointPresentationPullbackIso m).app a).symm
    pullbackRebracketHom k k (r.factorizationOnCover e hα hω q i).hom m =
      (r.factorizationOnCover e hα hω (p ≫ q) j).hom := by
  let k : W.space ⟶ T.space := (rankSpaceInclusion α).map q
  let m : V.space ⟶ W.space := (rankSpaceInclusion α).map p
  let g := r.projection
  let h := r.targetLeg e hα hω
  let B : QuotientCocycle H T.space := (τ.app ⟨op T⟩).toFunctor.obj (A.map g)
  let C := A.map h
  let P : QuotientCocycle r.groupoid W.space ⥤ QuotientCocycle r.groupoid V.space := pullbackFunctor m
  let Q : QuotientCocycle H W.space ⥤ QuotientCocycle H V.space := pullbackFunctor m
  let L : QuotientCocycle r.groupoid V.space ⥤ QuotientCocycle H V.space := mapCocycles h
  let F : QuotientCocycle G V.space ⥤ QuotientCocycle H V.space := (τ.app ⟨op V⟩).toFunctor
  let E : QuotientCocycle G W.space ⥤ QuotientCocycle H W.space := (τ.app ⟨op W⟩).toFunctor
  let δ := pullbackCompIso A k m
  let d : B.pullback (m ≫ k) ≅ Q.obj (B.pullback k) := pullbackCompIso B k m
  let d' : C.pullback (m ≫ k) ≅ Q.obj (C.pullback k) := pullbackCompIso C k m
  let j₀ := P.mapIso i ≪≫ ((pointPresentationPullbackIso m).app a).symm
  let j := δ ≪≫ j₀
  let n : E.obj ((A.map g).pullback k) ≅ B.pullback k := rankStackMorphismPullbackIso τ q _
  let n' : F.obj (((A.map g).pullback k).pullback m) ≅ Q.obj (E.obj ((A.map g).pullback k)) :=
    rankStackMorphismPullbackIso τ p _
  let n₀ : F.obj ((A.map g).pullback (m ≫ k)) ≅ B.pullback (m ≫ k) :=
    rankStackMorphismPullbackIso τ (p ≫ q) _
  let θ : E.obj ((A.map g).pullback k) ⟶ C.pullback k :=
    (r.factorizationAtPresentation e hα hω i).hom
  let u : F.obj (((A.map g).pullback k).pullback m) ⟶ Q.obj (C.pullback k) :=
    (r.factorizationAtPresentation e hα hω j₀).hom
  let v : F.obj ((A.map g).pullback (m ≫ k)) ⟶ C.pullback (m ≫ k) :=
    (r.factorizationAtPresentation e hα hω j).hom
  let D : (A.map g).pullback (m ≫ k) ⟶ ((A.map g).pullback k).pullback m := mapHom g δ.hom
  have hv : F.map D ≫ u = v ≫ d'.hom :=
    r.factorizationAtPresentation_natural e hα hω j j₀ δ.hom
  have hu : u = n'.hom ≫ Q.map θ := r.factorizationAtPresentation_restrict e hα hω p i
  have hn : n₀.hom ≫ d.hom = F.map D ≫ n'.hom ≫ Q.map n.hom :=
    rankStackMorphismPullbackIso_comp τ p q (A.map g)
  change d.hom ≫ Q.map (n.inv ≫ θ) ≫ d'.inv = n₀.inv ≫ v
  apply (cancel_mono d'.hom).mp
  apply (cancel_epi n₀.hom).mp
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id, Category.comp_id, Q.map_comp]
  rw [← hv, hu, reassoc_of% hn]
  have hc : Q.map n.hom ≫ Q.map n.inv = 𝟙 _ := by
    rw [← Q.map_comp, n.hom_inv_id, Q.map_id]
  simp only [reassoc_of% hc]

private def samplePullbackHom {T V : CGWH.{u}} {B C : QuotientCocycle H T}
    (k : V ⟶ T) (v : B.pullback k ⟶ C.pullback k)
    (y : CGWH.FibreSubspace B.cover C.cover) (t : V.obj)
    (ht : k.hom t = (baseOfMixed B C).hom y) : H.arrows.obj :=
  v.val.val (mixedPullbackLift B C k ⟨(t, y), ht⟩)

private theorem sampleRebracketHom {T W V : CGWH.{u}} {B C : QuotientCocycle H T}
    (k : W ⟶ T) (m : V ⟶ W) (v : B.pullback k ⟶ C.pullback k)
    (y : CGWH.FibreSubspace (B.pullback k).cover (C.pullback k).cover) (t : V.obj)
    (ht : m.hom t = y.val.1.val.2) :
    samplePullbackHom (m ≫ k) (pullbackRebracketHom k k v m) (mixedPullback B C k y) t
      ((congrArg k.hom ht).trans y.val.1.property.symm) = v.val.val y := by
  unfold samplePullbackHom
  rw [pullbackRebracketHom_apply]
  apply congrArg v.val.val
  apply Subtype.ext
  exact Prod.ext (Subtype.ext (Prod.ext rfl ht))
    (Subtype.ext (Prod.ext rfl (ht.trans y.property)))

private theorem factorizationCoverSample_eq (r : RankChartRefinement τ x) {T V Z : RankSpace α}
    (e : Z.space.obj ≃ₜ r.groupoid.arrows.obj)
    (hα : preBeth α = α.card) (hω : ℵ₀ < preBeth α) {f g : V ⟶ T} (hfg : f = g)
    {A : QuotientCocycle r.groupoid T.space} {a b : r.groupoid.Points V.space}
    (i : A.pullback ((rankSpaceInclusion α).map f) ≅ ofPoint a)
    (j : A.pullback ((rankSpaceInclusion α).map g) ≅ ofPoint b)
    (y y' : CGWH.FibreSubspace
      ((τ.app ⟨op T⟩).toFunctor.obj (A.map r.projection)).cover
      (A.map (r.targetLeg e hα hω)).cover) (hy : y = y') (t : V.space.obj)
    (hp : ((rankSpaceInclusion α).map f).hom t =
      (baseOfMixed ((τ.app ⟨op T⟩).toFunctor.obj (A.map r.projection))
        (A.map (r.targetLeg e hα hω))).hom y)
    (hq : ((rankSpaceInclusion α).map g).hom t =
      (baseOfMixed ((τ.app ⟨op T⟩).toFunctor.obj (A.map r.projection))
        (A.map (r.targetLeg e hα hω))).hom y') :
    samplePullbackHom ((rankSpaceInclusion α).map f) (r.factorizationOnCover e hα hω f i).hom y t hp =
      samplePullbackHom ((rankSpaceInclusion α).map g) (r.factorizationOnCover e hα hω g j).hom y' t hq := by
  subst g y'
  have hi := r.factorizationAtPresentation_independent e hα hω i j
  exact congrArg (fun η ↦ samplePullbackHom ((rankSpaceInclusion α).map f)
    ((rankStackMorphismPullbackIso τ f (A.map r.projection)).symm ≪≫ η).hom y t hp) hi

set_option maxHeartbeats 1200000 in
/-- The local comparison descends across a quotient cover. One-point
probes detect equality of values on each overlap of the lifted common cover. -/
theorem factorizationOnCover_descends (r : RankChartRefinement τ x) {T W Z : RankSpace α}
    (e : Z.space.obj ≃ₜ r.groupoid.arrows.obj)
    (hα : preBeth α = α.card) (hω : ℵ₀ < preBeth α) (q : W ⟶ T)
    (hq : IsQuotientMap ((rankSpaceInclusion α).map q).hom)
    {A : QuotientCocycle r.groupoid T.space} {a : r.groupoid.Points W.space}
    (i : A.pullback ((rankSpaceInclusion α).map q) ≅ ofPoint a) :
    ∃! θ : (τ.app ⟨op T⟩).toFunctor.obj (A.map r.projection) ⟶ A.map (r.targetLeg e hα hω),
      pullbackHom θ ((rankSpaceInclusion α).map q) = (r.factorizationOnCover e hα hω q i).hom := by
  let I := rankSpaceInclusion α
  let k : W.space ⟶ T.space := I.map q
  let B : QuotientCocycle H T.space := (τ.app ⟨op T⟩).toFunctor.obj (A.map r.projection)
  let C := A.map (r.targetLeg e hα hω)
  let w : B.pullback k ⟶ C.pullback k := (r.factorizationOnCover e hα hω q i).hom
  apply existsUnique_pullbackHom_of_overlap k hq w
  intro y y' hy
  obtain ⟨V, ⟨homeo⟩⟩ := rankSpace_representative hα CGWH.basepointObject
    (show #(ULift.{u} Unit) < preBeth α from mk_le_aleph0.trans_lt hω)
  let t := homeo.symm ⟨()⟩
  let p (z : W.space.obj) : V ⟶ W := I.preimage (CGWH.map (ContinuousMap.const _ z))
  have hp (z : W.space.obj) (v : V.space.obj) : (I.map (p z)).hom v = z :=
    congrArg (fun f : V.space ⟶ W.space ↦ f.hom v) (I.map_preimage _)
  let z := y.val.1.val.2
  let z' := y'.val.1.val.2
  have he : k.hom z = k.hom z' := y.val.1.property.symm.trans
    ((congrArg (fun u ↦ (baseOfMixed B C).hom u) hy).trans y'.val.1.property)
  have hpp : p z ≫ q = p z' ≫ q := by
    apply I.map_injective
    rw [I.map_comp, I.map_comp]
    apply cgwhForget.map_injective
    apply ConcreteCategory.hom_ext
    intro v
    exact (congrArg k.hom (hp z v)).trans (he.trans (congrArg k.hom (hp z' v)).symm)
  let j (v : W.space.obj) := pullbackCompIso A k (I.map (p v)) ≪≫
    (pullbackFunctor (I.map (p v))).mapIso i ≪≫
      ((pointPresentationPullbackIso (I.map (p v))).app a).symm
  let hy₁ := (congrArg k.hom (hp z t)).trans y.val.1.property.symm
  let hy₂ := (congrArg k.hom (hp z' t)).trans y'.val.1.property.symm
  have h₁ := sampleRebracketHom k (I.map (p z)) w y t (hp z t)
  have h₂ := sampleRebracketHom k (I.map (p z')) w y' t (hp z' t)
  have hj₁ := r.factorizationOnCover_rebracket e hα hω q (p z) i
  have hj₂ := r.factorizationOnCover_rebracket e hα hω q (p z') i
  have h := r.factorizationCoverSample_eq e hα hω hpp (j z) (j z')
    (mixedPullback B C k y) (mixedPullback B C k y') hy t hy₁ hy₂
  exact h₁.symm.trans ((congrArg (fun v ↦ samplePullbackHom (I.map (p z ≫ q)) v
    (mixedPullback B C k y) t hy₁) hj₁).trans (h.trans
      ((congrArg (fun v ↦ samplePullbackHom (I.map (p z' ≫ q)) v
        (mixedPullback B C k y') t hy₂) hj₂).symm.trans h₂)))

/-- Every cocycle admits a comparison over its base obtained by
descending the local factorization on a quotient presentation. -/
theorem factorizationOfCocycle_exists (r : RankChartRefinement τ x) {T Z : RankSpace α}
    (e : Z.space.obj ≃ₜ r.groupoid.arrows.obj)
    (hα : preBeth α = α.card) (hω : ℵ₀ < preBeth α) (hκ : (preBeth α).IsStrongLimit)
    (A : QuotientCocycle r.groupoid T.space) :
    ∃ (W : RankSpace α) (q : W ⟶ T) (a : r.groupoid.Points W.space)
      (i : A.pullback ((rankSpaceInclusion α).map q) ≅ ofPoint a)
      (θ : (τ.app ⟨op T⟩).toFunctor.obj (A.map r.projection) ≅ A.map (r.targetLeg e hα hω)),
      IsQuotientMap ((rankSpaceInclusion α).map q).hom ∧
        pullbackHom θ.hom ((rankSpaceInclusion α).map q) =
          (r.factorizationOnCover e hα hω q i).hom := by
  obtain ⟨W, q, a, hq, ⟨i⟩⟩ := rankCocycle_locallyPoint A hα hω hκ
  have hk := (rankSingleton_canonical_iff_quotient q hα hω).mp hq
  obtain ⟨θ, hθ, _⟩ := r.factorizationOnCover_descends e hα hω q hk i
  letI : IsIso θ := @IsIso.of_groupoid (QuotientCocycle H T.space) _ _ _ θ
  exact ⟨W, q, a, i, asIso θ, hk, hθ⟩

theorem projection_standardMorita (r : RankChartRefinement τ x) :
    IsStandardMorita r.projection :=
  refineObjectsProjection_standardMorita _ (x.isQuotientMap.comp r.isQuotient)

theorem equivalenceOver (r : RankChartRefinement τ x) :
    IsRankCocycleEquivalenceOver r.projection α :=
  rankCocycleEquivalenceOver_of_standardMorita r.projection r.projection_standardMorita

theorem arrows_bounded (r : RankChartRefinement τ x)
    (hω : ℵ₀ < preBeth α) (hG : #(G.arrows.obj : Type u) < preBeth α) :
    #(r.groupoid.arrows.obj : Type u) < preBeth α :=
  arrowComparison_carrier_lt r.projection hω r.cover.carrier_lt hG

theorem arrows_rankRepresentative (r : RankChartRefinement τ x)
    (hα : preBeth α = α.card) (hω : ℵ₀ < preBeth α) (hG : #(G.arrows.obj : Type u) < preBeth α) :
    ∃ Z : RankSpace α, Nonempty (Z.space.obj ≃ₜ r.groupoid.arrows.obj) :=
  rankSpace_representative hα r.groupoid.arrows (r.arrows_bounded hω hG)

end RankChartRefinement

/-- Every morphism of the explicit rank-site quotient stacks has a
rank-bounded chart refinement that trivializes the image of the chart. -/
theorem rankChartRefinement_exists
    (τ : rankCocyclePseudofunctor G α ⟶ rankCocyclePseudofunctor H α)
    {X : RankSpace α} (x : X.space.obj ≃ₜ G.objects.obj)
    (hα : preBeth α = α.card) (hω : ℵ₀ < preBeth α) (hκ : (preBeth α).IsStrongLimit) :
    Nonempty (RankChartRefinement τ x) := by
  let a : G.Points X.space := ⟨x, x.continuous⟩
  let A : QuotientCocycle H X.space := (τ.app ⟨op X⟩).toFunctor.obj (ofPoint a)
  obtain ⟨W, q, b, hq, ⟨i⟩⟩ := rankCocycle_locallyPoint A hα hω hκ
  exact ⟨⟨W, q, (rankSingleton_canonical_iff_quotient q hα hω).mp hq, b, i⟩⟩


/-- Any morphism of the explicit quotient stacks admits both continuous
groupoid legs of a refinement, with the desired comparison on points in
every rank-site fibre. The source leg is standard Morita. -/
theorem rankChartFactorizationOnPoints
    (τ : rankCocyclePseudofunctor G α ⟶ rankCocyclePseudofunctor H α)
    (hα : preBeth α = α.card) (hω : ℵ₀ < preBeth α) (hκ : (preBeth α).IsStrongLimit)
    (hG₀ : #(G.objects.obj : Type u) < preBeth α) (hG₁ : #(G.arrows.obj : Type u) < preBeth α) :
    ∃ (K : TopologicalGroupoid.{u}) (g : K ⟶ G) (h : K ⟶ H),
      #(K.objects.obj : Type u) < preBeth α ∧ #(K.arrows.obj : Type u) < preBeth α ∧
      IsStandardMorita g ∧
        ∀ T : RankSpace α, Nonempty (
          (pointPresentation K T.space ⋙ mapCocycles g) ⋙ (τ.app ⟨op T⟩).toFunctor ≅
          pointPresentation K T.space ⋙ mapCocycles h) := by
  obtain ⟨X, ⟨x⟩⟩ := rankSpace_representative hα G.objects hG₀
  obtain ⟨r⟩ := rankChartRefinement_exists τ x hα hω hκ
  obtain ⟨Z, ⟨e⟩⟩ := r.arrows_rankRepresentative hα hω hG₁
  exact ⟨r.groupoid, r.projection, r.targetLeg e hα hω, r.cover.carrier_lt,
    r.arrows_bounded hω hG₁, r.projection_standardMorita, fun T ↦ ⟨r.pointFactorization T e hα hω⟩⟩

end

end Masullo.TopologicalGroupoid
