import RankCocyclePresentation

open CategoryTheory Opposite Function Cardinal Topology
open scoped Bicategory Pseudofunctor.StrongTrans Cardinal

namespace Masullo.TopologicalGroupoid

open QuotientCocycle

universe u

noncomputable section

variable {G H : TopologicalGroupoid.{u}} {α : Ordinal.{u}}

def pointImageIso {T : CGWH.{u}} (f : G ⟶ H) (a : G.Points T) :
    ofPoint ((mapPoints f T).obj a) ≅ (ofPoint a).map f :=
  isoOfCoverMap _ _ (ContinuousMap.id _) (fun _ ↦ rfl) (fun _ ↦ rfl)
    (fun x _ _ ↦ (f.mapUnit (a x)).symm)

/-- Cocycle pushforward agrees with the underlying point map on identity
presentations, including the continuous arrows. -/
def pointPresentationPushforwardIso {T : CGWH.{u}} (f : G ⟶ H) :
    mapPoints f T ⋙ pointPresentation H T ≅ pointPresentation G T ⋙ mapCocycles f := by
  refine NatIso.ofComponents (pointImageIso f) ?_
  intro a b r
  let p := pointPresentation H T
  let u := (p.map ((mapPoints f T).map r))
  let v := mapHom f ((pointPresentation G T).map r)
  change u ≫ (pointImageIso f b).hom = (pointImageIso f a).hom ≫ v
  apply hom_ext
  intro x
  exact (comp_apply_right_unit u (pointImageIso f b).hom x.val.1 x.val.1 x.val.2 rfl x.property
    (f.mapUnit (b x.val.1))).trans
    (comp_apply_left_unit (pointImageIso f a).hom v x.val.1 x.val.1 x.val.2 rfl x.property
      (f.mapUnit (a x.val.1))).symm

/-- The identification with pushforward of points is compatible with the
two restriction comparisons. -/
theorem pointPresentationPushforwardIso_pullback {T S : CGWH.{u}} (f : G ⟶ H)
    (g : S ⟶ T) (a : G.Points T) :
    (pointPresentationPullbackIso (G := H) g).hom.app ((mapPoints f T).obj a) ≫
      pullbackHom (pointImageIso f a).hom g =
    (pointImageIso f ((G.restrictPoints g.hom.hom.hom).obj a)).hom ≫
      mapHom f ((pointPresentationPullbackIso (G := G) g).hom.app a) := by
  apply hom_ext
  intro p
  let x := p.val.1
  let y := p.val.2
  let b := (mapPoints f T).obj a
  let c := (G.restrictPoints g.hom.hom.hom).obj a
  let q : ((ofPoint b).pullback g).coverSpace.obj := ⟨(g.hom x,x),rfl⟩
  let r : ((ofPoint c).map f).coverSpace.obj := x
  exact (comp_apply_left_unit ((pointPresentationPullbackIso (G := H) g).hom.app b)
    (pullbackHom (pointImageIso f a).hom g) x q y rfl p.property rfl).trans
    (comp_apply_left_unit (pointImageIso f c).hom (mapHom f ((pointPresentationPullbackIso (G := G) g).hom.app a))
      x r y rfl p.property (f.mapUnit (c x))).symm

private theorem comparison_identities {C : Type*} [Category C] {a b : C} (r : a ⟶ b) :
    𝟙 a ≫ r = r ≫ 𝟙 b ≫ 𝟙 b := by simp

private theorem comparison_identities_comp {C : Type*} [Category C] {a b : C} (r : a ⟶ b)
    (s : b ⟶ b) (h : s = 𝟙 b) :
    𝟙 a ≫ r = r ≫ 𝟙 b ≫ 𝟙 b ≫ 𝟙 b ≫ s ≫ 𝟙 b := by simp [h]

set_option maxHeartbeats 600000 in
/-- Pushforward by a continuous groupoid functor on the quotient cocycle
stacks. It commutes with pullback of the presenting cover. -/
def rankCocyclePushforward (f : G ⟶ H) (α : Ordinal.{u}) :
    rankCocyclePseudofunctor G α ⟶ rankCocyclePseudofunctor H α where
  app X := (mapCocycles (T := X.as.unop.space) f).toCatHom
  naturality _ := eqToIso rfl
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
    change QuotientCocycle G X.as.unop.space at a
    change 𝟙 _ ≫ (pullbackIdIso (a.map f)).hom =
      mapHom f (pullbackIdIso a).hom ≫ 𝟙 _ ≫ 𝟙 _
    exact comparison_identities (pullbackIdIso (a.map f)).hom
  naturality_comp {X Y Z} g h := by
    apply Cat.Hom₂.ext
    ext a
    change QuotientCocycle G X.as.unop.space at a
    let l := (rankSpaceInclusion α).map g.as.unop
    let m := (rankSpaceInclusion α).map h.as.unop
    let A := (a.map f).pullback (m ≫ l)
    let B := ((a.map f).pullback l).pullback m
    let c : A ⟶ B := (pullbackCompIso (a.map f) l m).hom
    let d : B ⟶ B := pullbackHom (𝟙 ((a.map f).pullback l)) m
    change 𝟙 A ≫ c = c ≫ 𝟙 B ≫ 𝟙 B ≫ 𝟙 B ≫ d ≫ 𝟙 B
    have hi : d = 𝟙 B :=
      (pullbackFunctor m).map_id _
    exact comparison_identities_comp c d hi

/-- The induced map of total categories of the two cocycle stacks. -/
def rankCocyclePushforwardTotal (f : G ⟶ H) (α : Ordinal.{u}) :
    RankCocycleTotal G α ⥤ RankCocycleTotal H α :=
  Pseudofunctor.CoGrothendieck.map (rankCocyclePushforward f α)

theorem rankCocyclePushforwardTotal_over (f : G ⟶ H) (α : Ordinal.{u}) :
    rankCocyclePushforwardTotal f α ⋙ rankCocycleProjection H α = rankCocycleProjection G α := rfl

/-- The induced map preserves Cartesian arrows over the same base arrow. -/
theorem rankCocyclePushforwardTotal_cartesian (f : G ⟶ H) {a b : RankCocycleTotal G α} (r : a ⟶ b) :
    (rankCocycleProjection H α).IsStronglyCartesian r.base ((rankCocyclePushforwardTotal f α).map r) := by
  let s := (rankCocyclePushforwardTotal f α).map r
  letI : IsIso s.fiber := @IsIso.of_groupoid (QuotientCocycle H a.base.space) _ _ _ s.fiber
  exact FiberedGrothendieck.isStronglyCartesian_of_fiber_isIso s

/-- E.6.4.1 for the cocycle stack on the canonical rank site. -/
theorem rankCocyclePushforwardTotal_fullyFaithful_iff (f : G ⟶ H)
    (hα : preBeth α = α.card) (hω : ℵ₀ < preBeth α)
    (hG : #(G.objects.obj : Type u) < preBeth α) (hH : #(H.arrows.obj : Type u) < preBeth α) :
    Nonempty (rankCocyclePushforwardTotal f α).FullyFaithful ↔
      ∃ e : G.arrows.obj ≃ₜ ArrowComparisonSpace f, ∀ a, e a = arrowComparison f a := by
  refine (FiberedGrothendieck.map_fullyFaithful_iff (rankCocyclePushforward f α)).trans ⟨?_,?_⟩
  · intro h
    apply (arrowComparison_homeomorph_iff_rankCocycles f hα hω hG hH).mpr
    intro T A B _ _
    exact (Functor.FullyFaithful.nonempty_iff_map_bijective (mapCocycles f)).mp (h T) A B
  · intro h T
    exact (arrowComparison_homeomorph_iff_mapCocycles f).mp h T.space

private theorem moritaAnchor_quotient_of_rankComponents (f : G ⟶ H)
    (hα : preBeth α = α.card) (hH : #(H.objects.obj : Type u) < preBeth α)
    (h : ∀ W : RankSpace α, (mapCocycles (T := W.space) f).EssSurj) : IsQuotientMap (moritaAnchor f) := by
  obtain ⟨W,⟨e⟩⟩ := rankSpace_representative hα H.objects hH
  let b : H.Points W.space := ⟨e,e.continuous⟩
  obtain ⟨V,q,hq,a,⟨r⟩⟩ := localPoint_of_cocycle_essSurj f b (h W)
  let a₀ : C(V.obj,G.objects.obj) := a
  have ht (x : V.obj) : f.objectMap (a₀ x) = H.target (r.val x) := (r.property.2 x).symm
  let k : C(V.obj,MoritaAnchorSpace f) :=
    ⟨fun x ↦ ⟨(a₀ x,r.val x),ht x⟩,(kelleyPair a₀ r.val).continuous.subtype_mk ht⟩
  apply IsQuotientMap.of_comp k.continuous (moritaAnchor f).continuous
  have he : moritaAnchor f ∘ k = e ∘ q.hom := funext fun x ↦ r.property.1 x
  rw [he]
  exact e.isQuotientMap.comp hq

/-- E.6.4.2 for the cocycle stack on the canonical rank site. -/
theorem rankCocyclePushforwardTotal_isEquivalence_iff (f : G ⟶ H)
    (hα : preBeth α = α.card) (hω : ℵ₀ < preBeth α)
    (hG : #(G.objects.obj : Type u) < preBeth α) (hH : #(H.arrows.obj : Type u) < preBeth α)
    (hH₀ : #(H.objects.obj : Type u) < preBeth α) :
    (rankCocyclePushforwardTotal f α).IsEquivalence ↔
      (∃ e : G.arrows.obj ≃ₜ ArrowComparisonSpace f, ∀ a, e a = arrowComparison f a) ∧
      IsQuotientMap (moritaAnchor f) := by
  let τ := rankCocyclePushforward f α
  let L := rankCocyclePushforwardTotal f α
  constructor
  · intro h
    letI : L.IsEquivalence := h
    refine ⟨(rankCocyclePushforwardTotal_fullyFaithful_iff f hα hω hG hH).mp
      ⟨Functor.FullyFaithful.ofFullyFaithful L⟩,?_⟩
    exact moritaAnchor_quotient_of_rankComponents f hα hH₀ fun X ↦
      FiberedGrothendieck.component_essSurj_of_map τ (inferInstance : L.EssSurj)
        (fun Y _ _ r ↦ @IsIso.of_groupoid (QuotientCocycle H Y.space) _ _ _ r) X
  · rintro ⟨he,hq⟩
    let ff := FiberedGrothendieck.mapFullyFaithful τ fun X ↦
      ((arrowComparison_homeomorph_iff_mapCocycles f).mp he X.space).some
    letI : L.Faithful := ff.faithful
    letI : L.Full := ff.full
    letI : L.EssSurj := FiberedGrothendieck.map_essSurj_of_components τ fun _ ↦
      cocycle_essSurj_of_morita f he hq
    exact ({} : L.IsEquivalence)

/-- E.6.4.4. Standard Morita equivalences induce equivalences of the
total categories of quotient cocycle stacks over the same rank site. -/
theorem rankCocyclePushforwardTotal_isEquivalence_of_standardMorita (f : G ⟶ H)
    (hf : IsStandardMorita f) : (rankCocyclePushforwardTotal f α).IsEquivalence := by
  let τ := rankCocyclePushforward f α
  let L := rankCocyclePushforwardTotal f α
  let ff := FiberedGrothendieck.mapFullyFaithful τ fun X ↦
    ((arrowComparison_homeomorph_iff_mapCocycles f).mp hf.2 X.space).some
  letI : L.Faithful := ff.faithful
  letI : L.Full := ff.full
  letI : L.EssSurj := FiberedGrothendieck.map_essSurj_of_components τ fun _ ↦
    cocycle_essSurj_of_morita f hf.2 (moritaAnchor_quotient_of_object_quotient f hf.1)
  exact ({} : L.IsEquivalence)

/-- An equivalence induced by pushforward, with inverse over the rank site
and unit and counit over identities. -/
def IsRankCocycleEquivalenceOver (f : G ⟶ H) (α : Ordinal.{u}) : Prop :=
  ∃ e : RankCocycleTotal G α ≌ RankCocycleTotal H α,
    e.functor = rankCocyclePushforwardTotal f α ∧
    e.inverse ⋙ rankCocycleProjection G α = rankCocycleProjection H α ∧
    (∀ a, (rankCocycleProjection G α).IsHomLift (𝟙 a.base) (e.unitIso.hom.app a)) ∧
    ∀ b, (rankCocycleProjection H α).IsHomLift (𝟙 b.base) (e.counitIso.hom.app b)

theorem rankCocycleEquivalenceOver_iff (f : G ⟶ H) :
    IsRankCocycleEquivalenceOver f α ↔ (rankCocyclePushforwardTotal f α).IsEquivalence := by
  constructor
  · rintro ⟨e,he,_⟩
    exact he ▸ e.isEquivalence_functor
  · intro hf
    let τ := rankCocyclePushforward f α
    let L := rankCocyclePushforwardTotal f α
    letI : L.IsEquivalence := hf
    have hff := (FiberedGrothendieck.map_fullyFaithful_iff τ).mp ⟨Functor.FullyFaithful.ofFullyFaithful L⟩
    apply FiberedGrothendieck.equivalence_over_of_components τ (fun X ↦ (hff X).some)
    intro X
    exact FiberedGrothendieck.component_essSurj_of_map τ (inferInstance : L.EssSurj)
      (fun Y _ _ r ↦ @IsIso.of_groupoid (QuotientCocycle H Y.space) _ _ _ r) X

/-- The Morita criterion gives an equivalence over the base, not only an
equivalence of the underlying categories. -/
theorem rankCocycleEquivalenceOver_iff_morita (f : G ⟶ H)
    (hα : preBeth α = α.card) (hω : ℵ₀ < preBeth α)
    (hG : #(G.objects.obj : Type u) < preBeth α) (hH : #(H.arrows.obj : Type u) < preBeth α)
    (hH₀ : #(H.objects.obj : Type u) < preBeth α) :
    IsRankCocycleEquivalenceOver f α ↔
      (∃ e : G.arrows.obj ≃ₜ ArrowComparisonSpace f, ∀ a, e a = arrowComparison f a) ∧
      IsQuotientMap (moritaAnchor f) :=
  (rankCocycleEquivalenceOver_iff f).trans (rankCocyclePushforwardTotal_isEquivalence_iff f hα hω hG hH hH₀)

/-- Standard Morita equivalences induce equivalences over the rank site. -/
theorem rankCocycleEquivalenceOver_of_standardMorita (f : G ⟶ H) (hf : IsStandardMorita f) :
    IsRankCocycleEquivalenceOver f α :=
  (rankCocycleEquivalenceOver_iff f).mpr (rankCocyclePushforwardTotal_isEquivalence_of_standardMorita f hf)

end

end Masullo.TopologicalGroupoid
