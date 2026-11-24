import RankCocycleRefinement

open CategoryTheory.Pseudofunctor.CoGrothendieck

open CategoryTheory Opposite Function Cardinal Topology
open scoped Bicategory Pseudofunctor.StrongTrans Cardinal

namespace Masullo.TopologicalGroupoid

open QuotientCocycle

universe u

noncomputable section

variable {G H : TopologicalGroupoid.{u}} {α : Ordinal.{u}}

private theorem pullbackRebracketHom_global {T W V : CGWH.{u}} {B C : QuotientCocycle H T}
    (θ : B ⟶ C) (k : W ⟶ T) (m : V ⟶ W) :
    pullbackRebracketHom k k (pullbackHom θ k) m = pullbackHom θ (m ≫ k) := by
  let e := pullbackCompIso C k m
  let d := pullbackCompIso B k m
  have h : pullbackHom θ (m ≫ k) ≫ e.hom = d.hom ≫ pullbackHom (pullbackHom θ k) m :=
    (pullbackCompNatIso k m).hom.naturality θ
  change d.hom ≫ pullbackHom (pullbackHom θ k) m ≫ e.inv = _
  apply (cancel_mono e.hom).mp
  simp only [Category.assoc, e.inv_hom_id, Category.comp_id]
  exact h.symm

namespace RankChartRefinement

variable {τ : rankCocyclePseudofunctor G α ⟶ rankCocyclePseudofunctor H α}
  {X : RankSpace α} {x : X.space.obj ≃ₜ G.objects.obj}

private theorem factorizationOnCover_eq_of_base (r : RankChartRefinement τ x) {T V Z : RankSpace α}
    (e : Z.space.obj ≃ₜ r.groupoid.arrows.obj)
    (hα : preBeth α = α.card) (hω : ℵ₀ < preBeth α)
    {f g : V ⟶ T} (hfg : f = g)
    {A : QuotientCocycle r.groupoid T.space} {a b : r.groupoid.Points V.space}
    (i : A.pullback ((rankSpaceInclusion α).map f) ≅ ofPoint a)
    (j : A.pullback ((rankSpaceInclusion α).map g) ≅ ofPoint b) :
    HEq (r.factorizationOnCover e hα hω f i).hom (r.factorizationOnCover e hα hω g j).hom := by
  subst g
  apply heq_of_eq
  have h := r.factorizationAtPresentation_independent e hα hω i j
  exact congrArg (fun η ↦ ((rankStackMorphismPullbackIso τ f (A.map r.projection)).symm ≪≫ η).hom) h

set_option maxHeartbeats 1000000 in
/-- A global comparison descended from one quotient presentation restricts
to the local comparison at any point presentation. -/
theorem factorization_agrees (r : RankChartRefinement τ x) {T W S Z : RankSpace α}
    (e : Z.space.obj ≃ₜ r.groupoid.arrows.obj)
    (hα : preBeth α = α.card) (hω : ℵ₀ < preBeth α)
    (q : W ⟶ T) (f : S ⟶ T) (hq : IsQuotientMap ((rankSpaceInclusion α).map q).hom)
    {A : QuotientCocycle r.groupoid T.space} {a : r.groupoid.Points W.space} {b : r.groupoid.Points S.space}
    (i : A.pullback ((rankSpaceInclusion α).map q) ≅ ofPoint a)
    (j : A.pullback ((rankSpaceInclusion α).map f) ≅ ofPoint b)
    (θ : (τ.app ⟨op T⟩).toFunctor.obj (A.map r.projection) ⟶ A.map (r.targetLeg e hα hω))
    (hθ : pullbackHom θ ((rankSpaceInclusion α).map q) = (r.factorizationOnCover e hα hω q i).hom) :
    pullbackHom θ ((rankSpaceInclusion α).map f) = (r.factorizationOnCover e hα hω f j).hom := by
  obtain ⟨V, p, k, hbase, hp⟩ := rankQuotientCover_baseChange q f hα hω hq
  let I := rankSpaceInclusion α
  let ff : S.space ⟶ T.space := I.map f
  let qq : W.space ⟶ T.space := I.map q
  let pp : V.space ⟶ S.space := I.map p
  let kk : V.space ⟶ W.space := I.map k
  let B : QuotientCocycle H T.space := (τ.app ⟨op T⟩).toFunctor.obj (A.map r.projection)
  let C := A.map (r.targetLeg e hα hω)
  let u : B.pullback ff ⟶ C.pullback ff := pullbackHom θ ff
  let v : B.pullback ff ⟶ C.pullback ff := (r.factorizationOnCover e hα hω f j).hom
  let i' := pullbackCompIso A qq kk ≪≫ (pullbackFunctor kk).mapIso i ≪≫
    ((pointPresentationPullbackIso kk).app a).symm
  let j' := pullbackCompIso A ff pp ≪≫ (pullbackFunctor pp).mapIso j ≪≫
    ((pointPresentationPullbackIso pp).app b).symm
  have hl : pullbackRebracketHom ff ff u pp = pullbackHom θ (I.map (p ≫ f)) :=
    pullbackRebracketHom_global θ ff pp
  have hr : pullbackRebracketHom ff ff v pp =
      (r.factorizationOnCover e hα hω (p ≫ f) j').hom := r.factorizationOnCover_rebracket e hα hω f p j
  have hh : pullbackHom θ (I.map (k ≫ q)) = (r.factorizationOnCover e hα hω (k ≫ q) i').hom :=
    (pullbackRebracketHom_global θ qq kk).symm.trans
      ((congrArg (fun z ↦ pullbackRebracketHom qq qq z kk) hθ).trans
        (r.factorizationOnCover_rebracket e hα hω q k i))
  have he : HEq (pullbackHom θ (I.map (p ≫ f))) (pullbackHom θ (I.map (k ≫ q))) := by
    rw [hbase]
  have hout := (he.trans (heq_of_eq hh)).trans
    (r.factorizationOnCover_eq_of_base e hα hω hbase.symm i' j')
  have hb : pullbackRebracketHom ff ff u pp = pullbackRebracketHom ff ff v pp :=
    hl.trans ((eq_of_heq hout).trans hr.symm)
  let d := pullbackCompIso B ff pp
  let d' := pullbackCompIso C ff pp
  apply (pullbackFunctor_faithful_of_quotient pp hp).map_injective
  change pullbackHom u pp = pullbackHom v pp
  apply (cancel_mono d'.inv).mp
  apply (cancel_epi d.hom).mp
  exact hb

/-- The descended comparison agrees with every pullback presentation. -/
theorem factorizationGlobal_exists (r : RankChartRefinement τ x) {T Z : RankSpace α}
    (e : Z.space.obj ≃ₜ r.groupoid.arrows.obj)
    (hα : preBeth α = α.card) (hω : ℵ₀ < preBeth α) (hκ : (preBeth α).IsStrongLimit)
    (A : QuotientCocycle r.groupoid T.space) :
    ∃ θ : (τ.app ⟨op T⟩).toFunctor.obj (A.map r.projection) ≅ A.map (r.targetLeg e hα hω),
      ∀ {S : RankSpace α} (f : S ⟶ T) (a : r.groupoid.Points S.space)
        (i : A.pullback ((rankSpaceInclusion α).map f) ≅ ofPoint a),
        pullbackHom θ.hom ((rankSpaceInclusion α).map f) = (r.factorizationOnCover e hα hω f i).hom := by
  obtain ⟨W, q, a, i, θ, hq, hθ⟩ := r.factorizationOfCocycle_exists e hα hω hκ A
  exact ⟨θ, fun f b j ↦ r.factorization_agrees e hα hω q f hq i j θ.hom hθ⟩

def factorizationGlobal (r : RankChartRefinement τ x) {T Z : RankSpace α}
    (e : Z.space.obj ≃ₜ r.groupoid.arrows.obj)
    (hα : preBeth α = α.card) (hω : ℵ₀ < preBeth α) (hκ : (preBeth α).IsStrongLimit)
    (A : QuotientCocycle r.groupoid T.space) :
    (τ.app ⟨op T⟩).toFunctor.obj (A.map r.projection) ≅ A.map (r.targetLeg e hα hω) :=
  (r.factorizationGlobal_exists e hα hω hκ A).choose

theorem factorizationGlobal_pullback (r : RankChartRefinement τ x) {T S Z : RankSpace α}
    (e : Z.space.obj ≃ₜ r.groupoid.arrows.obj)
    (hα : preBeth α = α.card) (hω : ℵ₀ < preBeth α) (hκ : (preBeth α).IsStrongLimit)
    {A : QuotientCocycle r.groupoid T.space} (f : S ⟶ T) {a : r.groupoid.Points S.space}
    (i : A.pullback ((rankSpaceInclusion α).map f) ≅ ofPoint a) :
    pullbackHom (r.factorizationGlobal e hα hω hκ A).hom ((rankSpaceInclusion α).map f) =
      (r.factorizationOnCover e hα hω f i).hom :=
  (r.factorizationGlobal_exists e hα hω hκ A).choose_spec f a i

set_option maxHeartbeats 1000000 in
/-- The descended comparison is natural in all quotient cocycles over a
fixed test space. A common quotient cover detects the equality. -/
theorem factorizationGlobal_natural (r : RankChartRefinement τ x) {T Z : RankSpace α}
    (e : Z.space.obj ≃ₜ r.groupoid.arrows.obj)
    (hα : preBeth α = α.card) (hω : ℵ₀ < preBeth α) (hκ : (preBeth α).IsStrongLimit)
    {A B : QuotientCocycle r.groupoid T.space} (v : A ⟶ B) :
    (τ.app ⟨op T⟩).toFunctor.map (mapHom r.projection v) ≫ (r.factorizationGlobal e hα hω hκ B).hom =
      (r.factorizationGlobal e hα hω hκ A).hom ≫ mapHom (r.targetLeg e hα hω) v := by
  obtain ⟨W, q, a, hq, ⟨i⟩⟩ := rankCocycle_locallyPoint A hα hω hκ
  obtain ⟨W', q', b, hq', ⟨j⟩⟩ := rankCocycle_locallyPoint B hα hω hκ
  have hQ := (rankSingleton_canonical_iff_quotient q hα hω).mp hq
  have hQ' := (rankSingleton_canonical_iff_quotient q' hα hω).mp hq'
  obtain ⟨V, p, p', hbase, hp⟩ := rankQuotientCover_baseChange q' q hα hω hQ'
  let I := rankSpaceInclusion α
  let f := p ≫ q
  let k : V.space ⟶ T.space := I.map f
  have hk : IsQuotientMap k.hom := hQ.comp hp
  let i₀ := pullbackCompIso A (I.map q) (I.map p) ≪≫
    (pullbackFunctor (I.map p)).mapIso i ≪≫ ((pointPresentationPullbackIso (I.map p)).app a).symm
  let j₀ := pullbackCompIso B (I.map q') (I.map p') ≪≫
    (pullbackFunctor (I.map p')).mapIso j ≪≫ ((pointPresentationPullbackIso (I.map p')).app b).symm
  let i' : A.pullback k ≅ ofPoint ((r.groupoid.restrictPoints (I.map p).hom.hom.hom).obj a) := i₀
  let j' : B.pullback k ≅ ofPoint ((r.groupoid.restrictPoints (I.map p').hom.hom.hom).obj b) :=
    eqToIso (congrArg B.pullback (congrArg I.map hbase)) ≪≫ j₀
  let g := r.projection
  let h := r.targetLeg e hα hω
  let F : QuotientCocycle G T.space ⥤ QuotientCocycle H T.space := (τ.app ⟨op T⟩).toFunctor
  let E : QuotientCocycle G V.space ⥤ QuotientCocycle H V.space := (τ.app ⟨op V⟩).toFunctor
  let P : QuotientCocycle r.groupoid T.space ⥤ QuotientCocycle r.groupoid V.space := pullbackFunctor k
  let Q : QuotientCocycle H T.space ⥤ QuotientCocycle H V.space := pullbackFunctor k
  let M : QuotientCocycle r.groupoid V.space ⥤ QuotientCocycle H V.space := mapCocycles g ⋙ E
  let N : QuotientCocycle r.groupoid V.space ⥤ QuotientCocycle H V.space := mapCocycles h
  let n : M.obj (P.obj A) ≅ Q.obj (F.obj (A.map g)) := rankStackMorphismPullbackIso τ f (A.map g)
  let m : M.obj (P.obj B) ≅ Q.obj (F.obj (B.map g)) := rankStackMorphismPullbackIso τ f (B.map g)
  let A₀ : M.obj (P.obj A) ⟶ Q.obj (A.map h) := (r.factorizationAtPresentation e hα hω i').hom
  let B₀ : M.obj (P.obj B) ⟶ Q.obj (B.map h) := (r.factorizationAtPresentation e hα hω j').hom
  let θ : F.obj (A.map g) ⟶ A.map h := (r.factorizationGlobal e hα hω hκ A).hom
  let θ' : F.obj (B.map g) ⟶ B.map h := (r.factorizationGlobal e hα hω hκ B).hom
  let v₀ : A.map g ⟶ B.map g := mapHom g v
  let v₁ : A.map h ⟶ B.map h := mapHom h v
  have hA : Q.map θ = n.inv ≫ A₀ := r.factorizationGlobal_pullback e hα hω hκ f i'
  have hB : Q.map θ' = m.inv ≫ B₀ := r.factorizationGlobal_pullback e hα hω hκ f j'
  have hn : M.map (P.map v) ≫ m.hom = n.hom ≫ Q.map (F.map v₀) :=
    (Cat.Hom.toNatIso (τ.naturality f.op.toLoc)).hom.naturality v₀
  have hl : M.map (P.map v) ≫ B₀ = A₀ ≫ Q.map v₁ :=
    r.factorizationAtPresentation_natural e hα hω i' j' (P.map v)
  change F.map v₀ ≫ θ' = θ ≫ v₁
  apply (pullbackFunctor_faithful_of_quotient k hk).map_injective
  change Q.map (F.map v₀ ≫ θ') = Q.map (θ ≫ v₁)
  rw [Q.map_comp, Q.map_comp, hA, hB]
  apply (cancel_epi n.hom).mp
  rw [Category.assoc, ← reassoc_of% hn, m.hom_inv_id_assoc, n.hom_inv_id_assoc]
  exact hl

set_option maxHeartbeats 1200000 in
/-- The comparison between the two images of an arbitrary quotient
cocycle commutes with restriction along every base arrow. -/
theorem factorizationGlobal_restrict (r : RankChartRefinement τ x) {S T Z : RankSpace α}
    (e : Z.space.obj ≃ₜ r.groupoid.arrows.obj)
    (hα : preBeth α = α.card) (hω : ℵ₀ < preBeth α) (hκ : (preBeth α).IsStrongLimit)
    (p : S ⟶ T) (A : QuotientCocycle r.groupoid T.space) :
    let k := (rankSpaceInclusion α).map p
    (r.factorizationGlobal e hα hω hκ (A.pullback k)).hom =
      (rankStackMorphismPullbackIso τ p (A.map r.projection)).hom ≫
        pullbackHom (r.factorizationGlobal e hα hω hκ A).hom k := by
  let I := rankSpaceInclusion α
  let k : S.space ⟶ T.space := I.map p
  let A' := A.pullback k
  obtain ⟨W, q, a, hq, ⟨i⟩⟩ := rankCocycle_locallyPoint A' hα hω hκ
  let m : W.space ⟶ S.space := I.map q
  have hM := (rankSingleton_canonical_iff_quotient q hα hω).mp hq
  let g := r.projection
  let h := r.targetLeg e hα hω
  let F : QuotientCocycle G W.space ⥤ QuotientCocycle H W.space := (τ.app ⟨op W⟩).toFunctor
  let E : QuotientCocycle G S.space ⥤ QuotientCocycle H S.space := (τ.app ⟨op S⟩).toFunctor
  let J : QuotientCocycle G T.space ⥤ QuotientCocycle H T.space := (τ.app ⟨op T⟩).toFunctor
  let Q : QuotientCocycle H S.space ⥤ QuotientCocycle H W.space := pullbackFunctor m
  let B := J.obj (A.map g)
  let C := A.map h
  let δ : A.pullback (m ≫ k) ≅ A'.pullback m := pullbackCompIso A k m
  let db : B.pullback (m ≫ k) ≅ Q.obj (B.pullback k) := pullbackCompIso B k m
  let dc : C.pullback (m ≫ k) ≅ Q.obj (C.pullback k) := pullbackCompIso C k m
  let j : A.pullback (m ≫ k) ≅ ofPoint a := δ ≪≫ i
  let n : E.obj (A'.map g) ≅ B.pullback k := rankStackMorphismPullbackIso τ p (A.map g)
  let n' : F.obj ((A'.pullback m).map g) ≅ Q.obj (E.obj (A'.map g)) :=
    rankStackMorphismPullbackIso τ q (A'.map g)
  let n₀ : F.obj ((A.pullback (m ≫ k)).map g) ≅ B.pullback (m ≫ k) :=
    rankStackMorphismPullbackIso τ (q ≫ p) (A.map g)
  let u : F.obj ((A'.pullback m).map g) ⟶ Q.obj (C.pullback k) :=
    (r.factorizationAtPresentation e hα hω i).hom
  let v : F.obj ((A.pullback (m ≫ k)).map g) ⟶ C.pullback (m ≫ k) :=
    (r.factorizationAtPresentation e hα hω j).hom
  let d : F.obj ((A.pullback (m ≫ k)).map g) ≅ F.obj ((A'.pullback m).map g) :=
    (mapCocycles g ⋙ F).mapIso δ
  let θ : B ⟶ C := (r.factorizationGlobal e hα hω hκ A).hom
  let θ' : E.obj (A'.map g) ⟶ C.pullback k := (r.factorizationGlobal e hα hω hκ A').hom
  have hθ : Q.map θ' = n'.inv ≫ u := r.factorizationGlobal_pullback e hα hω hκ q i
  have hθ' : pullbackHom θ (m ≫ k) = n₀.inv ≫ v :=
    r.factorizationGlobal_pullback e hα hω hκ (q ≫ p) j
  have hu : d.hom ≫ u = v ≫ dc.hom :=
    r.factorizationAtPresentation_natural e hα hω j i δ.hom
  have hn : n₀.hom ≫ db.hom = d.hom ≫ n'.hom ≫ Q.map n.hom :=
    rankStackMorphismPullbackIso_comp τ q p (A.map g)
  have hb : pullbackHom θ (m ≫ k) ≫ dc.hom = db.hom ≫ Q.map (pullbackHom θ k) :=
    (pullbackCompNatIso k m).hom.naturality θ
  change θ' = n.hom ≫ pullbackHom θ k
  apply (pullbackFunctor_faithful_of_quotient m hM).map_injective
  change Q.map θ' = Q.map (n.hom ≫ pullbackHom θ k)
  rw [hθ, Q.map_comp]
  apply (cancel_epi (d.hom ≫ n'.hom)).mp
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [hu, ← reassoc_of% hn, ← hb, hθ']
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

set_option maxHeartbeats 1200000 in
/-- The two stack functors following the refinement are isomorphic on
their total categories, with components in the fibres over the rank site. -/
def factorizationTotalIso (r : RankChartRefinement τ x) {Z : RankSpace α}
    (e : Z.space.obj ≃ₜ r.groupoid.arrows.obj)
    (hα : preBeth α = α.card) (hω : ℵ₀ < preBeth α) (hκ : (preBeth α).IsStrongLimit) :
    rankCocyclePushforwardTotal r.projection α ⋙ Pseudofunctor.CoGrothendieck.map τ ≅
      rankCocyclePushforwardTotal (r.targetLeg e hα hω) α := by
  let g := r.projection
  let h := r.targetLeg e hα hω
  let K := rankCocyclePseudofunctor H α
  let L := rankCocyclePushforwardTotal g α ⋙ Pseudofunctor.CoGrothendieck.map τ
  let R := rankCocyclePushforwardTotal h α
  let θ (a : RankCocycleTotal r.groupoid α) : L.obj a ≅ R.obj a :=
    (ι K a.base).mapIso (r.factorizationGlobal e hα hω hκ a.fiber)
  refine NatIso.ofComponents θ ?_
  intro a b f
  let s : (L.obj a).fiber ⟶ (R.obj a).fiber := (r.factorizationGlobal e hα hω hκ a.fiber).hom
  let t : (L.obj b).fiber ⟶ (R.obj b).fiber := (r.factorizationGlobal e hα hω hκ b.fiber).hom
  have h₁ := FiberedGrothendieck.comp_vertical_between (L.map f) t
  have h₂ := FiberedGrothendieck.vertical_comp_between (R.map f) s
  refine h₁.trans (Eq.trans ?_ h₂.symm)
  change (⟨f.base, (L.map f).fiber ≫ (K.map f.base.op.toLoc).toFunctor.map t⟩ :
    L.obj a ⟶ R.obj b) = ⟨f.base, s ≫ (R.map f).fiber⟩
  apply congrArg (fun v ↦ (⟨f.base, v⟩ : L.obj a ⟶ R.obj b))
  let q : a.base.space ⟶ b.base.space := (rankSpaceInclusion α).map f.base
  let E : QuotientCocycle G a.base.space ⥤ QuotientCocycle H a.base.space := (τ.app ⟨op a.base⟩).toFunctor
  let A : QuotientCocycle r.groupoid a.base.space := a.fiber
  let B : QuotientCocycle r.groupoid b.base.space := b.fiber
  let v : A ⟶ B.pullback q := f.fiber
  let u : A.map g ⟶ (B.map g).pullback q := mapHom g v
  let w : A.map h ⟶ (B.map h).pullback q := mapHom h v
  let J : QuotientCocycle G b.base.space ⥤ QuotientCocycle H b.base.space := (τ.app ⟨op b.base⟩).toFunctor
  let n : E.obj ((B.map g).pullback q) ⟶ (J.obj (B.map g)).pullback q :=
    (rankStackMorphismPullbackIso τ f.base (B.map g)).hom
  have hL : (L.map f).fiber = E.map u ≫ n := by
    change E.map (u ≫ 𝟙 _) ≫ n = E.map u ≫ n
    rw [Category.comp_id]
  have hR : (R.map f).fiber = w := Category.comp_id _
  change (L.map f).fiber ≫ pullbackHom (r.factorizationGlobal e hα hω hκ B).hom q =
    (r.factorizationGlobal e hα hω hκ A).hom ≫ (R.map f).fiber
  rw [hL, hR]
  let z : (J.obj (B.map g)).pullback q ⟶ (B.map h).pullback q :=
    pullbackHom (r.factorizationGlobal e hα hω hκ B).hom q
  have hn : (r.factorizationGlobal e hα hω hκ (B.pullback q)).hom = n ≫ z :=
    r.factorizationGlobal_restrict e hα hω hκ f.base B
  exact (Category.assoc (E.map u) n z).trans
    ((congrArg (E.map u ≫ ·) hn.symm).trans (r.factorizationGlobal_natural e hα hω hκ v))

theorem factorizationTotalIso_vertical (r : RankChartRefinement τ x) {Z : RankSpace α}
    (e : Z.space.obj ≃ₜ r.groupoid.arrows.obj)
    (hα : preBeth α = α.card) (hω : ℵ₀ < preBeth α) (hκ : (preBeth α).IsStrongLimit)
    (a : RankCocycleTotal r.groupoid α) :
    (rankCocycleProjection H α).IsHomLift (𝟙 a.base)
      ((r.factorizationTotalIso e hα hω hκ).hom.app a) := by
  let p := rankCocycleProjection H α
  let v := (ι (rankCocyclePseudofunctor H α) a.base).map
    (r.factorizationGlobal e hα hω hκ a.fiber).hom
  change p.IsHomLift (𝟙 a.base) v
  exact Functor.IsHomLift.map (p := p) v

end RankChartRefinement

/-- Corrected E.6.4.6 for the explicit quotient cocycle stacks. Every
stack morphism factors through a standard Morita refinement and a
continuous groupoid functor, with a vertical natural isomorphism comparing
the two induced maps of stacks. -/
theorem rankCocycleFactorization
    (τ : rankCocyclePseudofunctor G α ⟶ rankCocyclePseudofunctor H α)
    (hα : preBeth α = α.card) (hω : ℵ₀ < preBeth α) (hκ : (preBeth α).IsStrongLimit)
    (hG₀ : #(G.objects.obj : Type u) < preBeth α) (hG₁ : #(G.arrows.obj : Type u) < preBeth α) :
    ∃ (K : TopologicalGroupoid.{u}) (g : K ⟶ G) (h : K ⟶ H),
      #(K.objects.obj : Type u) < preBeth α ∧ #(K.arrows.obj : Type u) < preBeth α ∧
      IsStandardMorita g ∧ IsRankCocycleEquivalenceOver g α ∧
      ∃ η : rankCocyclePushforwardTotal g α ⋙ Pseudofunctor.CoGrothendieck.map τ ≅
          rankCocyclePushforwardTotal h α,
        ∀ a : RankCocycleTotal K α,
          (rankCocycleProjection H α).IsHomLift (𝟙 a.base) (η.hom.app a) := by
  obtain ⟨X, ⟨x⟩⟩ := rankSpace_representative hα G.objects hG₀
  obtain ⟨r⟩ := rankChartRefinement_exists τ x hα hω hκ
  obtain ⟨Z, ⟨e⟩⟩ := r.arrows_rankRepresentative hα hω hG₁
  exact ⟨r.groupoid, r.projection, r.targetLeg e hα hω, r.cover.carrier_lt,
    r.arrows_bounded hω hG₁, r.projection_standardMorita, r.equivalenceOver,
    r.factorizationTotalIso e hα hω hκ, r.factorizationTotalIso_vertical e hα hω hκ⟩

end

end Masullo.TopologicalGroupoid
