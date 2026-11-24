import RankSieveRefinement
import CocycleCoproduct

open Cardinal CategoryTheory Function Set Topology TopologicalSpace
open scoped Cardinal Ordinal

namespace Masullo.TopologicalGroupoid

universe u

variable {α : Ordinal.{u}}

/-- On the manuscript's rank site a single map generates a canonical cover
exactly when its underlying map is quotient. -/
theorem rankSingleton_canonical_iff_quotient {X Y : RankSpace α} (q : Y ⟶ X)
    (hα : preBeth α = α.card) (hω : ℵ₀ < preBeth α) :
    Sieve.generate (Presieve.singleton q) ∈ Sheaf.canonicalTopology (RankSpace α) X ↔
      IsQuotientMap ((rankSpaceInclusion α).map q).hom := by
  classical
  let S : Sieve X := Sieve.generate (Presieve.singleton q)
  rw [rankCanonicalTopology_iff S hα hω]
  let U := rankSpaceInclusion α
  constructor
  · intro hS
    have hfac (i : RankSieveArrows S) : ∃ r : i.1 ⟶ Y, r ≫ q = i.2.val := by
      obtain ⟨W,r,w,hw,he⟩ := i.2.property
      cases hw
      exact ⟨r,he⟩
    let r (i : RankSieveArrows S) := (hfac i).choose
    let d : (Σ i : RankSieveArrows S, i.1.space.obj) → Y.space.obj :=
      fun p ↦ (U.map (r p.1)).hom p.2
    have hd : Continuous d := continuous_sigma fun i ↦ (U.map (r i)).hom.hom.hom.continuous
    apply IsQuotientMap.of_comp hd (U.map q).hom.hom.hom.continuous
    have hdq : (U.map q).hom ∘ d = rankSieveMap S := by
      funext p
      exact congrArg (fun a : p.1.1 ⟶ X ↦ (U.map a).hom p.2) ((hfac p.1).choose_spec)
    change IsQuotientMap ((U.map q).hom ∘ d)
    rwa [hdq]
  · intro hq
    let i : RankSieveArrows S := ⟨Y, q, ⟨Y, 𝟙 Y, q, Presieve.singleton_self q, Category.id_comp q⟩⟩
    apply IsQuotientMap.of_comp (continuous_sigmaMk (i := i)) (rankSieveMap_continuous S)
    exact hq

theorem arrowComparison_carrier_lt {G H : TopologicalGroupoid.{u}} (f : G ⟶ H)
    (hω : ℵ₀ < preBeth α) (hG : #(G.objects.obj : Type u) < preBeth α)
    (hH : #(H.arrows.obj : Type u) < preBeth α) :
    #(ArrowComparisonSpace f) < preBeth α := by
  have hGG : #(G.objects.obj × G.objects.obj) < preBeth α := by
    simp only [mk_prod, lift_id]
    exact mul_lt_of_lt hω.le hG hG
  have hW : #((G.objects.obj × G.objects.obj) × H.arrows.obj) < preBeth α := by
    simp only [mk_prod, lift_id]
    exact mul_lt_of_lt hω.le hGG hH
  exact (mk_le_of_injective (f := fun p : ArrowComparisonSpace f ↦
    show (G.objects.obj × G.objects.obj) × H.arrows.obj from p.val) Subtype.val_injective).trans_lt hW

/-- E.6.4.1 on cocycle presentations using rank-bounded test spaces and
rank-bounded covers. A rank representative of the endpoint pullback is
already enough to detect the backward implication. -/
theorem arrowComparison_homeomorph_iff_rankCocycles {G H : TopologicalGroupoid.{u}} (f : G ⟶ H)
    (hα : preBeth α = α.card) (hω : ℵ₀ < preBeth α)
    (hG : #(G.objects.obj : Type u) < preBeth α) (hH : #(H.arrows.obj : Type u) < preBeth α) :
    (∃ e : G.arrows.obj ≃ₜ ArrowComparisonSpace f, ∀ a, e a = arrowComparison f a) ↔
    ∀ (T : RankSpace α) (A B : QuotientCocycle G T.space),
      #(A.coverSpace.obj : Type u) < preBeth α → #(B.coverSpace.obj : Type u) < preBeth α →
      Bijective (QuotientCocycle.mapHom f (A := A) (B := B)) := by
  constructor
  · intro h _ A B _ _
    exact QuotientCocycle.mapHom_bijective_of_arrowComparison f h A B
  · intro h
    obtain ⟨T, ⟨e⟩⟩ := rankSpace_representative hα (arrowComparisonObject f)
      (arrowComparison_carrier_lt f hω hG hH)
    apply arrowComparison_homeomorph_of_test f (T := T.space) e
    apply QuotientCocycle.mapPoints_fullyFaithful_of_identityCovers
    intro a b
    exact h T (QuotientCocycle.ofPoint a) (QuotientCocycle.ofPoint b) T.carrier_lt T.carrier_lt

/-- Restricting a rank-bounded cocycle along a rank-site arrow still gives a
cocycle whose cover admits a representative in the same rank. -/
theorem rankCocycle_pullback_cover_representative {G : TopologicalGroupoid.{u}}
    {X Y : RankSpace α} (g : X ⟶ Y) (A : QuotientCocycle G Y.space)
    (hα : preBeth α = α.card) (hω : ℵ₀ < preBeth α)
    (hA : #(A.coverSpace.obj : Type u) < preBeth α) :
    ∃ W : RankSpace α,
      Nonempty (W.space.obj ≃ₜ (A.pullback ((rankSpaceInclusion α).map g)).coverSpace.obj) := by
  let f := (rankSpaceInclusion α).map g
  apply rankSpace_representative hα
  change #(CGWH.FibreSubspace A.cover f) < preBeth α
  have hp : #(A.coverSpace.obj × X.space.obj) < preBeth α := by
    simp only [mk_prod, lift_id]
    exact mul_lt_of_lt hω.le hA X.carrier_lt
  exact (mk_le_of_injective (f := fun p : CGWH.FibreSubspace A.cover f ↦
    show A.coverSpace.obj × X.space.obj from p.val) Subtype.val_injective).trans_lt hp

/-- A bounded cocycle has an isomorphic presentation by an actual single
canonical cover of the rank site. -/
theorem rankCocycle_exists_canonical_presentation {G : TopologicalGroupoid.{u}}
    {X : RankSpace α} (A : QuotientCocycle G X.space)
    (hα : preBeth α = α.card) (hω : ℵ₀ < preBeth α)
    (hA : #(A.coverSpace.obj : Type u) < preBeth α) :
    ∃ (W : RankSpace α) (q : W ⟶ X) (B : QuotientCocycle G X.space),
      (Sieve.generate (Presieve.singleton q) ∈ Sheaf.canonicalTopology (RankSpace α) X) ∧
      (∃ h : B.coverSpace = W.space,
        cast (congrArg (fun Z : CGWH.{u} ↦ Z ⟶ X.space) h) B.cover = (rankSpaceInclusion α).map q) ∧
      Nonempty (B ≅ A) := by
  obtain ⟨W, ⟨e⟩⟩ := rankSpace_representative hα A.coverSpace hA
  let U := rankSpaceInclusion α
  let r : W.space ⟶ A.coverSpace := CGWH.map ⟨e,e.continuous⟩
  have hr : IsQuotientMap r.hom := e.isQuotientMap
  let B := A.refineCover r hr
  let q : W ⟶ X := U.preimage (r ≫ A.cover)
  have hq : U.map q = r ≫ A.cover := U.map_preimage _
  have hCov : IsQuotientMap (U.map q).hom := by
    rw [hq]
    exact A.isCover.comp hr
  exact ⟨W,q,B,(rankSingleton_canonical_iff_quotient q hα hω).mpr hCov,
    ⟨rfl, hq.symm⟩, A.refineCover_iso r hr⟩

/-- Object descent along a single rank-site quotient cover gives a global
presentation using an actual canonical cover in the same rank. -/
theorem rankCocycle_effective_singleton_descent {G : TopologicalGroupoid.{u}}
    {X Y : RankSpace α} (q : Y ⟶ X)
    (hα : preBeth α = α.card) (hω : ℵ₀ < preBeth α)
    (hq : Sieve.generate (Presieve.singleton q) ∈ Sheaf.canonicalTopology (RankSpace α) X)
    (A : QuotientCocycle G Y.space) (hA : #(A.coverSpace.obj : Type u) < preBeth α)
    (r : A.OverlapHom ((rankSpaceInclusion α).map q))
    (hr : A.OverlapDescent ((rankSpaceInclusion α).map q) r) :
    ∃ (W : RankSpace α) (g : W ⟶ X) (B : QuotientCocycle G X.space),
      (Sieve.generate (Presieve.singleton g) ∈ Sheaf.canonicalTopology (RankSpace α) X) ∧
      (∃ h : B.coverSpace = W.space,
        cast (congrArg (fun Z : CGWH.{u} ↦ Z ⟶ X.space) h) B.cover = (rankSpaceInclusion α).map g) ∧
      Nonempty (A ≅ B.pullback ((rankSpaceInclusion α).map q)) := by
  let f := (rankSpaceInclusion α).map q
  have hf : IsQuotientMap f.hom := (rankSingleton_canonical_iff_quotient q hα hω).mp hq
  let B₀ := A.descendObject f hf r hr
  obtain ⟨W,g,B,hg,hB,⟨e⟩⟩ := rankCocycle_exists_canonical_presentation B₀ hα hω hA
  obtain ⟨i⟩ := A.descendObject_pullback_iso f hf r hr
  exact ⟨W,g,B,hg,hB,⟨i ≪≫ (QuotientCocycle.pullbackFunctor (G := G) f).mapIso e.symm⟩⟩


private def rankBoundedCocycle (α : Ordinal.{u}) (G : TopologicalGroupoid.{u}) (T : CGWH.{u}) :
    ObjectProperty (QuotientCocycle G T) :=
  fun A ↦ #(A.coverSpace.obj : Type u) < preBeth α

private def rankBoundedLoopedCocycle (α : Ordinal.{u}) (G : TopologicalGroupoid.{u}) (T : CGWH.{u}) :
    ObjectProperty (QuotientCocycle.LoopedCocycle G T) :=
  fun A ↦ #(A.point.coverSpace.obj : Type u) < preBeth α

/-- The inertia comparison does not change the covering carrier, so it
restricts to the actual rank-bounded cocycle categories. -/
noncomputable def rankCocycleInertiaComparison (α : Ordinal.{u}) (G : TopologicalGroupoid.{u})
    (X : RankSpace α) :
    (rankBoundedLoopedCocycle α G X.space).FullSubcategory ⥤
      (rankBoundedCocycle α G.inertiaGroupoid X.space).FullSubcategory :=
  (rankBoundedCocycle α G.inertiaGroupoid X.space).lift
    ((rankBoundedLoopedCocycle α G X.space).ι ⋙ QuotientCocycle.descendedInertiaComparison G X.space)
    (fun A ↦ A.property)

/-- Every inertia cocycle in the same rank comes from a looped quotient
cocycle in that rank. -/
theorem rankCocycleInertiaComparison_isEquivalence (α : Ordinal.{u})
    (G : TopologicalGroupoid.{u}) (X : RankSpace α) :
    (rankCocycleInertiaComparison α G X).IsEquivalence := by
  let F := QuotientCocycle.descendedInertiaComparison G X.space
  letI : F.IsEquivalence := QuotientCocycle.descendedInertiaComparison_isEquivalence G X.space
  let P := rankBoundedLoopedCocycle α G X.space
  let Q := rankBoundedCocycle α G.inertiaGroupoid X.space
  let K := Q.lift (P.ι ⋙ F) (fun A ↦ A.property)
  letI : K.Faithful := ⟨by
    intro A B x y h
    apply P.ι.map_injective
    apply F.map_injective
    exact congrArg Q.ι.map h⟩
  letI : K.Full := ⟨by
    intro A B h
    refine ⟨ObjectProperty.homMk (F.preimage (Q.ι.map h)), ?_⟩
    apply Q.ι.map_injective
    exact F.map_preimage (Q.ι.map h)⟩
  letI : K.EssSurj := ⟨fun B ↦ by
    obtain ⟨r,hr⟩ := QuotientCocycle.exists_ofAutomorphism_eq B.obj
    let A : P.FullSubcategory := ⟨⟨B.obj.map G.inertiaProjection,r⟩,B.property⟩
    have he : (K.obj A).obj = B.obj := hr
    exact ⟨A,⟨Q.isoMk (eqToIso he)⟩⟩⟩
  change K.IsEquivalence
  exact {}


/-- Every cocycle on a rank-site object has a presentation by a single
canonical cover in that rank, even if its initial cover had a larger
carrier. -/
theorem rankCocycle_exists_bounded_presentation {G : TopologicalGroupoid.{u}}
    {X : RankSpace α} (A : QuotientCocycle G X.space)
    (hα : preBeth α = α.card) (hω : ℵ₀ < preBeth α) (hκ : (preBeth α).IsStrongLimit) :
    ∃ (W : RankSpace α) (q : W ⟶ X) (B : QuotientCocycle G X.space),
      (Sieve.generate (Presieve.singleton q) ∈ Sheaf.canonicalTopology (RankSpace α) X) ∧
      (∃ h : B.coverSpace = W.space,
        cast (congrArg (fun Z : CGWH.{u} ↦ Z ⟶ X.space) h) B.cover =
          (rankSpaceInclusion α).map q) ∧ Nonempty (B ≅ A) := by
  obtain ⟨W,g,hg⟩ := rankQuotientMap_refinement A.cover A.isCover hα hω hκ
  let B := A.refinePresentation g hg
  let U := rankSpaceInclusion α
  let q := U.preimage (g ≫ A.cover)
  have hq : U.map q = g ≫ A.cover := U.map_preimage _
  have hq' : IsQuotientMap (U.map q).hom := hq.symm ▸ hg
  exact ⟨W,q,B,(rankSingleton_canonical_iff_quotient q hα hω).mpr hq',
    ⟨rfl,hq.symm⟩,A.refinePresentation_iso g hg⟩

/-- The full subcategory of rank-bounded presentations gives the entire
cocycle groupoid over a rank test. -/
theorem rankBoundedCocycle_inclusion_isEquivalence (G : TopologicalGroupoid.{u})
    (X : RankSpace α) (hα : preBeth α = α.card) (hω : ℵ₀ < preBeth α)
    (hκ : (preBeth α).IsStrongLimit) :
    (rankBoundedCocycle α G X.space).ι.IsEquivalence := by
  let P := rankBoundedCocycle α G X.space
  letI : P.ι.EssSurj := ⟨fun A ↦ by
    obtain ⟨W,_,B,_,⟨h, _⟩,e⟩ := rankCocycle_exists_bounded_presentation A hα hω hκ
    exact ⟨⟨B, by change #(B.coverSpace.obj : Type u) < preBeth α; rw [h]; exact W.carrier_lt⟩,e⟩⟩
  exact {}

/-- On a jointly quotient family inside a canonical sieve, the cocycles on
the individual domains assemble into a rank-bounded cocycle on the rank-site
coproduct. Its restriction to each summand recovers the given cocycle. -/
theorem rankCanonicalSieve_assembleCocycleObjects {G : TopologicalGroupoid.{u}}
    {X : RankSpace α} (S : Sieve X)
    (hα : preBeth α = α.card) (hω : ℵ₀ < preBeth α) (hκ : (preBeth α).IsStrongLimit)
    (hS : S ∈ Sheaf.canonicalTopology (RankSpace α) X)
    (A : ∀ ⦃Y : RankSpace α⦄ (f : Y ⟶ X), S f → QuotientCocycle G Y.space) :
    ∃ (I : Type u) (Y : I → RankSpace α) (W : RankSpace α) (q : W ⟶ X)
      (j : ∀ i, Y i ⟶ W) (B : QuotientCocycle G W.space),
        IsQuotientMap ((rankSpaceInclusion α).map q).hom ∧
        #(B.coverSpace.obj : Type u) < preBeth α ∧
        ∃ hm : ∀ i, S (j i ≫ q), ∀ i,
          Nonempty (A (j i ≫ q) (hm i) ≅ B.pullback ((rankSpaceInclusion α).map (j i))) := by
  obtain ⟨I,Y,W,q,e,j,hq,hm,he⟩ := rankCanonicalSieve_quotientCoproduct S hα hω hκ hS
  let T (i : I) := (Y i).space
  let A₀ (i : I) := A (j i ≫ q) (hm i)
  let C := QuotientCocycle.assembleCocycles A₀
  let l : W.space ⟶ QuotientCocycle.sumSpace T := CGWH.map ⟨e,e.continuous⟩
  let B₀ := C.pullback l
  obtain ⟨V,_,B,_,⟨hB,_⟩,⟨eB⟩⟩ := rankCocycle_exists_bounded_presentation B₀ hα hω hκ
  refine ⟨I,Y,W,q,j,B,hq,?_,hm,?_⟩
  · rw [hB]
    exact V.carrier_lt
  · intro i
    let k := (rankSpaceInclusion α).map (j i)
    have hc : k ≫ l = QuotientCocycle.sumInclusion T i := by
      apply CGWH.ext_hom
      intro x
      exact he i x
    obtain ⟨a⟩ := QuotientCocycle.assembleCocycles_restrict_iso A₀ i
    obtain ⟨b⟩ := QuotientCocycle.pullback_comp_obj_iso C l k
    rw [hc] at b
    exact ⟨a ≪≫ b.symm ≪≫ (QuotientCocycle.pullbackFunctor (G := G) k).mapIso eB.symm⟩

/-- Compatible continuous overlap data on the presenting covers of a
canonical sieve give a global rank-bounded cocycle on its target, whose
restrictions recover the local objects on a jointly quotient subfamily. -/
theorem rankCanonicalSieve_descendCocycleObjects {G : TopologicalGroupoid.{u}}
    {X : RankSpace α} (S : Sieve X)
    (hα : preBeth α = α.card) (hω : ℵ₀ < preBeth α) (hκ : (preBeth α).IsStrongLimit)
    (hS : S ∈ Sheaf.canonicalTopology (RankSpace α) X)
    (A : ∀ ⦃Y : RankSpace α⦄ (g : Y ⟶ X), S g → QuotientCocycle G Y.space)
    (overlap : ∀ {I : Type u} {Y : I → RankSpace α} (g : ∀ i, Y i ⟶ X) (hg : ∀ i, S (g i)),
      QuotientCocycle.FamilyOverlap (fun i ↦ (rankSpaceInclusion α).map (g i))
        (fun i ↦ A (g i) (hg i))) :
    ∃ (I : Type u) (Y : I → RankSpace α) (g : ∀ i, Y i ⟶ X) (B : QuotientCocycle G X.space),
      IsQuotientMap (QuotientCocycle.sumDesc (fun i ↦ (rankSpaceInclusion α).map (g i))).hom ∧
      #(B.coverSpace.obj : Type u) < preBeth α ∧
      ∃ hg : ∀ i, S (g i), ∀ i,
        Nonempty (A (g i) (hg i) ≅ B.pullback ((rankSpaceInclusion α).map (g i))) := by
  obtain ⟨I,Y,g,hg,_,hq⟩ := rankCanonicalSieve_boundedFamily S hα hω hκ hS
  let r := overlap g hg
  let B₀ := r.descend hq
  obtain ⟨V,_,B,_,⟨hB,_⟩,⟨eB⟩⟩ := rankCocycle_exists_bounded_presentation B₀ hα hω hκ
  refine ⟨I,Y,g,B,hq,?_,hg,?_⟩
  · rw [hB]
    exact V.carrier_lt
  · intro i
    obtain ⟨a⟩ := r.descend_restrict_iso hq i
    let F := QuotientCocycle.pullbackFunctor (G := G) ((rankSpaceInclusion α).map (g i))
    exact ⟨a ≪≫ F.mapIso eB.symm⟩

/-- A family of morphisms between two globally defined cocycles, with one
morphism between their restrictions for each arrow of a sieve. -/
abbrev RankSieveCocycleHoms {G : TopologicalGroupoid.{u}} {X : RankSpace α}
    (S : Sieve X) (A B : QuotientCocycle G X.space) :=
  ∀ ⦃Y : RankSpace α⦄ (g : Y ⟶ X), S g →
    (A.pullback ((rankSpaceInclusion α).map g) ⟶ B.pullback ((rankSpaceInclusion α).map g))

open QuotientCocycle in
/-- Morphisms between the restrictions of two global objects extend
uniquely from an arbitrary canonical sieve when their evaluations agree
at the same pair of global presenting points. -/
theorem rankCanonicalSieve_pullbackHom_descends_iff {G : TopologicalGroupoid.{u}}
    {X : RankSpace α} (S : Sieve X)
    (hα : preBeth α = α.card) (hω : ℵ₀ < preBeth α)
    (hS : S ∈ Sheaf.canonicalTopology (RankSpace α) X)
    (A B : QuotientCocycle G X.space)
    (r : RankSieveCocycleHoms S A B) :
    (∃! a : A ⟶ B, ∀ ⦃Y : RankSpace α⦄ (g : Y ⟶ X) (hg : S g),
      pullbackHom a ((rankSpaceInclusion α).map g) = r g hg) ↔
    ∀ ⦃Y Y' : RankSpace α⦄ (g : Y ⟶ X) (g' : Y' ⟶ X) (hg : S g) (hg' : S g')
      (p : CGWH.FibreSubspace (A.pullback ((rankSpaceInclusion α).map g)).cover
        (B.pullback ((rankSpaceInclusion α).map g)).cover)
      (q : CGWH.FibreSubspace (A.pullback ((rankSpaceInclusion α).map g')).cover
        (B.pullback ((rankSpaceInclusion α).map g')).cover),
      mixedPullback A B ((rankSpaceInclusion α).map g) p =
        mixedPullback A B ((rankSpaceInclusion α).map g') q →
          (r g hg).val.val p = (r g' hg').val.val q := by
  constructor
  · rintro ⟨a,ha,_⟩ Y Y' g g' hg hg' p q h
    rw [← ha g hg, ← ha g' hg']
    exact congrArg a.val.val h
  · intro hr
    let k (i : RankSieveArrows S) := (rankSpaceInclusion α).map i.2.val
    let s (i : RankSieveArrows S) := r i.2.val i.2.property
    have hq : IsQuotientMap (sumDesc k).hom := (rankCanonicalTopology_iff S hα hω).mp hS
    obtain ⟨a,ha,hu⟩ := (familyPullbackHom_descends_iff k A B hq s).mpr
      (fun i j p q h ↦ hr i.2.val j.2.val i.2.property j.2.property p q h)
    exact ⟨a,fun _ g hg ↦ ha ⟨_,g,hg⟩,fun b hb ↦ hu b (fun i ↦ hb i.2.val i.2.property)⟩

open QuotientCocycle in
/-- Restriction compatibility on a sieve, expressed on the pair of global
presenting points and a point of the refining test space. -/
def rankSieveCocycleHomsCompatible {G : TopologicalGroupoid.{u}} {X : RankSpace α}
    {S : Sieve X} {A B : QuotientCocycle G X.space} (r : RankSieveCocycleHoms S A B) : Prop :=
  let U := rankSpaceInclusion α
  ∀ ⦃Y V : RankSpace α⦄ (g : Y ⟶ X) (hg : S g) (h : V ⟶ Y)
    (p : CGWH.FibreSubspace A.cover B.cover) (v : V.space.obj)
    (hv : (U.map h ≫ U.map g).hom v = (baseOfMixed A B).hom p),
    (r g hg).val.val (mixedPullbackLift A B (U.map g) ⟨((U.map h).hom v,p),hv⟩) =
      (r (h ≫ g) (S.downward_closed hg h)).val.val
        (mixedPullbackLift A B (U.map (h ≫ g)) ⟨(v,p),by rw [U.map_comp]; exact hv⟩)

open QuotientCocycle in
/-- A morphism between two global quotient cocycles satisfies the sheaf
condition on every canonical sieve in the manuscript's rank site. -/
theorem rankCanonicalSieve_pullbackHom_descends_iff_restriction {G : TopologicalGroupoid.{u}}
    {X : RankSpace α} (S : Sieve X)
    (hα : preBeth α = α.card) (hω : ℵ₀ < preBeth α)
    (hS : S ∈ Sheaf.canonicalTopology (RankSpace α) X)
    (A B : QuotientCocycle G X.space) (r : RankSieveCocycleHoms S A B) :
    (∃! a : A ⟶ B, ∀ ⦃Y : RankSpace α⦄ (g : Y ⟶ X) (hg : S g),
      pullbackHom a ((rankSpaceInclusion α).map g) = r g hg) ↔
      rankSieveCocycleHomsCompatible r := by
  let U := rankSpaceInclusion α
  constructor
  · rintro ⟨a,ha,_⟩ Y V g hg h p v hv
    rw [← ha g hg, ← ha (h ≫ g) (S.downward_closed hg h)]
    have hv' : (U.map (h ≫ g)).hom v = (baseOfMixed A B).hom p := by
      rw [U.map_comp]
      exact hv
    exact congrArg a.val.val ((mixedPullback_lift A B (U.map g) ⟨((U.map h).hom v,p),hv⟩).trans
      (mixedPullback_lift A B (U.map (h ≫ g)) ⟨(v,p),hv'⟩).symm)
  · intro hr
    apply (rankCanonicalSieve_pullbackHom_descends_iff S hα hω hS A B r).mpr
    intro Y Y' g g' hg hg' p q hpq
    let m := mixedPullback A B (U.map g) p
    let y := p.val.1.val.2
    let z := q.val.1.val.2
    have hy : (U.map g).hom y = (baseOfMixed A B).hom m := p.val.1.property.symm
    have hz : (U.map g').hom z = (baseOfMixed A B).hom m :=
      q.val.1.property.symm.trans (congrArg (baseOfMixed A B).hom hpq).symm
    let h : Y ⟶ Y := U.preimage (CGWH.map (ContinuousMap.const _ y))
    let h' : Y ⟶ Y' := U.preimage (CGWH.map (ContinuousMap.const _ z))
    have hl : U.map h = CGWH.map (ContinuousMap.const _ y) := U.map_preimage _
    have hr' : U.map h' = CGWH.map (ContinuousMap.const _ z) := U.map_preimage _
    have he : h ≫ g = h' ≫ g' := by
      apply U.map_injective
      rw [U.map_comp, U.map_comp, hl, hr']
      apply CGWH.ext_hom
      intro _
      exact hy.trans hz.symm
    have hyl : (U.map h ≫ U.map g).hom y = (baseOfMixed A B).hom m := by
      rw [hl]
      exact hy
    have hzl : (U.map h' ≫ U.map g').hom y = (baseOfMixed A B).hom m := by
      rw [hr']
      exact hz
    have hy' : (U.map h).hom y = y := by rw [hl]; rfl
    have hz' : (U.map h').hom y = z := by rw [hr']; rfl
    have ep : mixedPullbackLift A B (U.map g) ⟨((U.map h).hom y,m),hyl⟩ = p := by
      rw [← mixedPullbackLift_recovers A B (U.map g) p]
      apply congrArg (mixedPullbackLift A B (U.map g))
      exact Subtype.ext (Prod.ext hy' rfl)
    have eq : mixedPullbackLift A B (U.map g') ⟨((U.map h').hom y,m),hzl⟩ = q := by
      rw [← mixedPullbackLift_recovers A B (U.map g') q]
      apply congrArg (mixedPullbackLift A B (U.map g'))
      exact Subtype.ext (Prod.ext hz' hpq)
    have hp := hr g hg h m y hyl
    have hq := hr g' hg' h' m y hzl
    rw [ep] at hp
    rw [eq] at hq
    refine hp.trans (Eq.trans ?_ hq.symm)
    let V := {k : Y ⟶ X // S k ∧ (U.map k).hom y = (baseOfMixed A B).hom m}
    let value (k : V) := (r k.val k.property.1).val.val
      (mixedPullbackLift A B (U.map k.val) ⟨(y,m),k.property.2⟩)
    have hk₁ : (U.map (h ≫ g)).hom y = (baseOfMixed A B).hom m := by
      rw [U.map_comp]
      exact hyl
    have hk₂ : (U.map (h' ≫ g')).hom y = (baseOfMixed A B).hom m := by
      rw [U.map_comp]
      exact hzl
    have he' : (⟨h ≫ g, S.downward_closed hg h,hk₁⟩ : V) =
        ⟨h' ≫ g', S.downward_closed hg' h',hk₂⟩ := Subtype.ext he
    exact congrArg value he'

open QuotientCocycle in
/-- The pairwise overlap of rank-site arrows admits a homeomorphic test
space in the same rank. -/
theorem rankPairOverlap_representative {X Y V : RankSpace α} (g : Y ⟶ X) (h : V ⟶ X)
    (hα : preBeth α = α.card) (hω : ℵ₀ < preBeth α) :
    ∃ W : RankSpace α, Nonempty (W.space.obj ≃ₜ
      (pairOverlap ((rankSpaceInclusion α).map g) ((rankSpaceInclusion α).map h)).obj) := by
  apply rankSpace_representative hα
  change #(CGWH.FibreSubspace ((rankSpaceInclusion α).map g) ((rankSpaceInclusion α).map h)) < preBeth α
  have hsize : #(Y.space.obj × V.space.obj) < preBeth α := by
    simp only [mk_prod,lift_id]
    exact mul_lt_of_lt hω.le Y.carrier_lt V.carrier_lt
  exact (mk_le_of_injective (f := fun p : CGWH.FibreSubspace ((rankSpaceInclusion α).map g)
    ((rankSpaceInclusion α).map h) ↦ show Y.space.obj × V.space.obj from p.val)
    Subtype.val_injective).trans_lt hsize

/-- An object on every arrow of the sieve. -/
abbrev RankSieveCocycleObjects {G : TopologicalGroupoid.{u}} {X : RankSpace α} (S : Sieve X) :=
  ∀ ⦃Y : RankSpace α⦄ (g : Y ⟶ X), S g → QuotientCocycle G Y.space

/-- The restriction arrows of local cocycle objects, directed from the
object assigned to the refining domain to the restricted object. -/
abbrev RankSieveCocycleRestrictions {G : TopologicalGroupoid.{u}} {X : RankSpace α} {S : Sieve X}
    (A : RankSieveCocycleObjects (G := G) S) :=
  ∀ ⦃Y W : RankSpace α⦄ (g : Y ⟶ X) (hg : S g) (a : W ⟶ Y),
    A (a ≫ g) (S.downward_closed hg a) ⟶ (A g hg).pullback ((rankSpaceInclusion α).map a)

namespace RankSieveCocycleObjects

abbrev onArrow {G : TopologicalGroupoid.{u}} {X : RankSpace α} {S : Sieve X}
    (A : RankSieveCocycleObjects (G := G) S) (i : RankSieveArrows S) := A i.2.val i.2.property

end RankSieveCocycleObjects

/-- A map between two domains of a sieve commuting with their maps to
the target. -/
structure RankSieveRefinementArrow {X : RankSpace α} {S : Sieve X} (i j : RankSieveArrows S) where
  hom : i.1 ⟶ j.1
  comm : hom ≫ j.2.val = i.2.val

namespace RankSieveRefinementArrow

variable {X : RankSpace α} {S : Sieve X} {i j k : RankSieveArrows S}

def comp (a : RankSieveRefinementArrow i j) (b : RankSieveRefinementArrow j k) :
    RankSieveRefinementArrow i k := ⟨a.hom ≫ b.hom,by rw [Category.assoc,b.comm,a.comm]⟩

theorem ext_hom {a b : RankSieveRefinementArrow i j} (h : a.hom = b.hom) : a = b := by
  cases a
  cases b
  cases h
  rfl

end RankSieveRefinementArrow

/-- The restriction arrow with its source indexed by an explicit sieve
refinement, rather than a chosen expression for the composite. -/
noncomputable def rankSieveRestrictionHom {G : TopologicalGroupoid.{u}} {X : RankSpace α}
    {S : Sieve X} {A : RankSieveCocycleObjects (G := G) S}
    (r : RankSieveCocycleRestrictions A) {i j : RankSieveArrows S} (a : RankSieveRefinementArrow i j) :
    A.onArrow i ⟶ (A.onArrow j).pullback ((rankSpaceInclusion α).map a.hom) := by
  have h : A.onArrow i = A (a.hom ≫ j.2.val) (S.downward_closed j.2.property a.hom) :=
    congrArg (fun t : {k : i.1 ⟶ X // S k} ↦ A t.val t.property)
      (show i.2 = ⟨a.hom ≫ j.2.val,S.downward_closed j.2.property a.hom⟩ from Subtype.ext a.comm.symm)
  exact eqToHom h ≫ r j.2.val j.2.property a.hom

/-- Evaluate a sieve restriction at one presenting point of each object. -/
noncomputable def rankSieveRestrictionValue {G : TopologicalGroupoid.{u}} {X : RankSpace α}
    {S : Sieve X} {A : RankSieveCocycleObjects (G := G) S}
    (r : RankSieveCocycleRestrictions A) {i j : RankSieveArrows S} (a : RankSieveRefinementArrow i j)
    (x : (A.onArrow i).coverSpace.obj) (y : (A.onArrow j).coverSpace.obj)
    (h : (A.onArrow j).cover.hom y = ((rankSpaceInclusion α).map a.hom).hom ((A.onArrow i).cover.hom x)) :
    G.UnderlyingArrow ((A.onArrow i).point x) ((A.onArrow j).point y) :=
  QuotientCocycle.homValue (rankSieveRestrictionHom r a) x ⟨(y,(A.onArrow i).cover.hom x),h⟩ rfl

/-- Composition coherence for restriction arrows, evaluated using the
canonical rebracketing of pulled-back presenting points. -/
structure RankSieveRestrictionsCoherent {G : TopologicalGroupoid.{u}} {X : RankSpace α}
    {S : Sieve X} {A : RankSieveCocycleObjects (G := G) S} (r : RankSieveCocycleRestrictions A) : Prop where
  comp : ∀ {i j k : RankSieveArrows S} (a : RankSieveRefinementArrow i j) (b : RankSieveRefinementArrow j k)
    (x : (A.onArrow i).coverSpace.obj) (y : (A.onArrow j).coverSpace.obj) (z : (A.onArrow k).coverSpace.obj)
    (hy : (A.onArrow j).cover.hom y = ((rankSpaceInclusion α).map a.hom).hom ((A.onArrow i).cover.hom x))
    (hz : (A.onArrow k).cover.hom z = ((rankSpaceInclusion α).map b.hom).hom ((A.onArrow j).cover.hom y)),
    @CategoryStruct.comp G.Underlying _ _ _ _ (rankSieveRestrictionValue r a x y hy)
      (rankSieveRestrictionValue r b y z hz) = rankSieveRestrictionValue r (a.comp b) x z (by
        change _ = ((rankSpaceInclusion α).map (a.hom ≫ b.hom)).hom _
        rw [Functor.map_comp]
        exact hz.trans (congrArg ((rankSpaceInclusion α).map b.hom).hom hy))

open QuotientCocycle in
/-- A rank-site test for the pairwise overlap, with both projections
viewed as refinements in the sieve. -/
structure RankSieveOverlapTest {X : RankSpace α} {S : Sieve X} (i j : RankSieveArrows S) where
  mid : RankSieveArrows S
  homeomorph : mid.1.space.obj ≃ₜ
    (pairOverlap ((rankSpaceInclusion α).map i.2.val) ((rankSpaceInclusion α).map j.2.val)).obj
  left : RankSieveRefinementArrow mid i
  right : RankSieveRefinementArrow mid j
  left_apply : ∀ x, (homeomorph x).val.1 = ((rankSpaceInclusion α).map left.hom).hom x
  right_apply : ∀ x, (homeomorph x).val.2 = ((rankSpaceInclusion α).map right.hom).hom x

open QuotientCocycle in
/-- Choose a rank representative of the overlap, together with its
projections over the target of the sieve. -/
noncomputable def rankSieveOverlapTest {X : RankSpace α} {S : Sieve X} (i j : RankSieveArrows S)
    (hα : preBeth α = α.card) (hω : ℵ₀ < preBeth α) : RankSieveOverlapTest i j := by
  let U := rankSpaceInclusion α
  let g := i.2.val
  let h := j.2.val
  let w := rankPairOverlap_representative g h hα hω
  let W := w.choose
  let e := Classical.choice w.choose_spec
  let l : W.space ⟶ pairOverlap (U.map g) (U.map h) := CGWH.map ⟨e,e.continuous⟩
  let a : W ⟶ i.1 := U.preimage (l ≫ pairOverlapFirst (U.map g) (U.map h))
  let b : W ⟶ j.1 := U.preimage (l ≫ pairOverlapSecond (U.map g) (U.map h))
  have ha : U.map a = l ≫ pairOverlapFirst (U.map g) (U.map h) := U.map_preimage _
  have hb : U.map b = l ≫ pairOverlapSecond (U.map g) (U.map h) := U.map_preimage _
  have he : b ≫ h = a ≫ g := by
    apply U.map_injective
    simp only [U.map_comp, ha, hb, Category.assoc, pairOverlap_comm]
  exact ⟨⟨W,a ≫ g,S.downward_closed i.2.property a⟩,e,⟨a,rfl⟩,⟨b,he⟩,
    fun x ↦ (congrArg (fun z : W.space ⟶ i.1.space ↦ z.hom x) ha).symm,
    fun x ↦ (congrArg (fun z : W.space ⟶ j.1.space ↦ z.hom x) hb).symm⟩

open QuotientCocycle in
/-- Compose the inverse of the first restriction with the second one on
the rank representative of a pairwise overlap. -/
noncomputable def RankSieveOverlapTest.overlapHom {G : TopologicalGroupoid.{u}} {X : RankSpace α}
    {S : Sieve X} {A : RankSieveCocycleObjects (G := G) S} (r : RankSieveCocycleRestrictions A)
    {i j : RankSieveArrows S} (t : RankSieveOverlapTest i j) :
    (A.onArrow i).PairOverlapHom (A.onArrow j) ((rankSpaceInclusion α).map i.2.val)
      ((rankSpaceInclusion α).map j.2.val) :=
  let U := rankSpaceInclusion α
  pairOverlapHomOfHomeomorphicTest (A.onArrow i) (A.onArrow j) (U.map i.2.val) (U.map j.2.val)
    t.homeomorph (U.map t.left.hom) (U.map t.right.hom) t.left_apply t.right_apply
    (Groupoid.inv (rankSieveRestrictionHom r t.left) ≫ rankSieveRestrictionHom r t.right)

open QuotientCocycle in
/-- Restriction arrows on a sieve give an arrow on each pairwise overlap.
The two restrictions share the object assigned to the composite from a
rank representative of the overlap. -/
noncomputable def rankSievePairOverlapHom {G : TopologicalGroupoid.{u}} {X Y V : RankSpace α}
    {S : Sieve X} {A : RankSieveCocycleObjects (G := G) S}
    (r : RankSieveCocycleRestrictions A) (g : Y ⟶ X) (h : V ⟶ X) (hg : S g) (hh : S h)
    (hα : preBeth α = α.card) (hω : ℵ₀ < preBeth α) :
    (A g hg).PairOverlapHom (A h hh) ((rankSpaceInclusion α).map g) ((rankSpaceInclusion α).map h) :=
  (rankSieveOverlapTest ⟨Y,g,hg⟩ ⟨V,h,hh⟩ hα hω).overlapHom r

open QuotientCocycle in
/-- Evaluate an overlap arrow by factoring both local arrows through one
presenting point of the overlap test. -/
theorem RankSieveOverlapTest.overlapHom_value {G : TopologicalGroupoid.{u}} {X : RankSpace α}
    {S : Sieve X} {A : RankSieveCocycleObjects (G := G) S} (r : RankSieveCocycleRestrictions A)
    {i j : RankSieveArrows S} (t : RankSieveOverlapTest i j)
    (x : (A.onArrow i).coverSpace.obj) (y : (A.onArrow j).coverSpace.obj)
    (z : (A.onArrow t.mid).coverSpace.obj)
    (hx : (A.onArrow i).cover.hom x =
      ((rankSpaceInclusion α).map t.left.hom).hom ((A.onArrow t.mid).cover.hom z))
    (hy : (A.onArrow j).cover.hom y =
      ((rankSpaceInclusion α).map t.right.hom).hom ((A.onArrow t.mid).cover.hom z))
    (h : ((A.onArrow i).cover ≫ (rankSpaceInclusion α).map i.2.val).hom x =
      ((A.onArrow j).cover ≫ (rankSpaceInclusion α).map j.2.val).hom y) :
    pairOverlapValue (A.onArrow i) (A.onArrow j) ((rankSpaceInclusion α).map i.2.val)
      ((rankSpaceInclusion α).map j.2.val) (t.overlapHom r) x y h =
      @CategoryStruct.comp G.Underlying _ _ _ _
        (@Groupoid.inv G.Underlying _ _ _ (rankSieveRestrictionValue r t.left z x hx))
        (rankSieveRestrictionValue r t.right z y hy) := by
  let U := rankSpaceInclusion α
  let l := rankSieveRestrictionHom r t.left
  let s := rankSieveRestrictionHom r t.right
  let w : t.mid.1.space.obj := (A.onArrow t.mid).cover.hom z
  let x' : ((A.onArrow i).pullback (U.map t.left.hom)).coverSpace.obj := ⟨(x,w),hx⟩
  let y' : ((A.onArrow j).pullback (U.map t.right.hom)).coverSpace.obj := ⟨(y,w),hy⟩
  apply Subtype.ext
  exact (pairOverlapHomOfHomeomorphicTest_apply (A.onArrow i) (A.onArrow j) (U.map i.2.val)
    (U.map j.2.val) t.homeomorph (U.map t.left.hom) (U.map t.right.hom)
    t.left_apply t.right_apply (Groupoid.inv l ≫ s) w x y hx hy h).trans
    (congrArg Subtype.val (homValue_inv_comp l s x' y' z rfl rfl))

/-- A constant map into a sieve domain is a refinement when its value
lies over the constant value of the source arrow. -/
noncomputable def RankSieveRefinementArrow.constant {X : RankSpace α} {S : Sieve X}
    (i j : RankSieveArrows S) (y : j.1.space.obj)
    (hy : ∀ v, ((rankSpaceInclusion α).map i.2.val).hom v = ((rankSpaceInclusion α).map j.2.val).hom y) :
    RankSieveRefinementArrow i j := by
  let U := rankSpaceInclusion α
  let a : i.1 ⟶ j.1 := U.preimage (CGWH.map (ContinuousMap.const _ y))
  refine ⟨a,U.map_injective ?_⟩
  rw [U.map_comp, U.map_preimage]
  exact CGWH.ext_hom fun v ↦ (hy v).symm

theorem RankSieveRefinementArrow.constant_apply {X : RankSpace α} {S : Sieve X}
    (i j : RankSieveArrows S) (y : j.1.space.obj)
    (hy : ∀ v, ((rankSpaceInclusion α).map i.2.val).hom v = ((rankSpaceInclusion α).map j.2.val).hom y)
    (v : i.1.space.obj) :
    ((rankSpaceInclusion α).map (RankSieveRefinementArrow.constant i j y hy).hom).hom v = y := by
  change ((rankSpaceInclusion α).map ((rankSpaceInclusion α).preimage (CGWH.map
    (ContinuousMap.const _ y)))).hom v = y
  rw [Functor.map_preimage]
  rfl

private noncomputable def rankSieveConstantRestrictionValue {G : TopologicalGroupoid.{u}} {X : RankSpace α}
    {S : Sieve X} {A : RankSieveCocycleObjects (G := G) S} (r : RankSieveCocycleRestrictions A)
    {i j : RankSieveArrows S} (x : (A.onArrow i).coverSpace.obj) (y : (A.onArrow j).coverSpace.obj)
    (hy : ∀ v, ((rankSpaceInclusion α).map i.2.val).hom v =
      ((rankSpaceInclusion α).map j.2.val).hom ((A.onArrow j).cover.hom y)) :
    G.UnderlyingArrow ((A.onArrow i).point x) ((A.onArrow j).point y) :=
  rankSieveRestrictionValue r (RankSieveRefinementArrow.constant i j ((A.onArrow j).cover.hom y) hy)
    x y (RankSieveRefinementArrow.constant_apply i j ((A.onArrow j).cover.hom y) hy
      ((A.onArrow i).cover.hom x)).symm

private theorem rankSieveRestrictionValue_congr {G : TopologicalGroupoid.{u}} {X : RankSpace α}
    {S : Sieve X} {A : RankSieveCocycleObjects (G := G) S} (r : RankSieveCocycleRestrictions A)
    {i j : RankSieveArrows S} {a b : RankSieveRefinementArrow i j} (h : a = b)
    (x : (A.onArrow i).coverSpace.obj) (y : (A.onArrow j).coverSpace.obj)
    (ha : (A.onArrow j).cover.hom y = ((rankSpaceInclusion α).map a.hom).hom ((A.onArrow i).cover.hom x))
    (hb : (A.onArrow j).cover.hom y = ((rankSpaceInclusion α).map b.hom).hom ((A.onArrow i).cover.hom x)) :
    rankSieveRestrictionValue r a x y ha = rankSieveRestrictionValue r b x y hb := by
  subst b
  rfl

private theorem cancel_shared_prefix {C : Type*} [Groupoid C] {a b c d : C}
    (v : a ⟶ b) (s : b ⟶ c) (u : b ⟶ d) :
    Groupoid.inv s ≫ u = Groupoid.inv (v ≫ s) ≫ (v ≫ u) := by
  simp [IsIso.inv_comp,Category.assoc]

private theorem compose_spans {C : Type*} [Groupoid C] {a b c d : C}
    (s : a ⟶ b) (t : a ⟶ c) (u : a ⟶ d) :
    (Groupoid.inv s ≫ t) ≫ Groupoid.inv t ≫ u = Groupoid.inv s ≫ u := by
  simp [Category.assoc]

open QuotientCocycle in
private theorem rankSieveOverlap_value_common {G : TopologicalGroupoid.{u}} {X : RankSpace α}
    {S : Sieve X} {A : RankSieveCocycleObjects (G := G) S} {r : RankSieveCocycleRestrictions A}
    (hr : RankSieveRestrictionsCoherent r) {i j c : RankSieveArrows S} (t : RankSieveOverlapTest i j)
    (x : (A.onArrow i).coverSpace.obj) (y : (A.onArrow j).coverSpace.obj)
    (h : ((A.onArrow i).cover ≫ (rankSpaceInclusion α).map i.2.val).hom x =
      ((A.onArrow j).cover ≫ (rankSpaceInclusion α).map j.2.val).hom y)
    (z : (A.onArrow c).coverSpace.obj)
    (hc : ∀ v, ((rankSpaceInclusion α).map c.2.val).hom v =
      ((A.onArrow i).cover ≫ (rankSpaceInclusion α).map i.2.val).hom x) :
    pairOverlapValue (A.onArrow i) (A.onArrow j) ((rankSpaceInclusion α).map i.2.val)
      ((rankSpaceInclusion α).map j.2.val) (t.overlapHom r) x y h =
      @CategoryStruct.comp G.Underlying _ _ _ _
        (@Groupoid.inv G.Underlying _ _ _ (rankSieveConstantRestrictionValue r z x hc))
        (rankSieveConstantRestrictionValue r z y (fun v ↦ (hc v).trans h)) := by
  let U := rankSpaceInclusion α
  let p : CGWH.FibreSubspace (U.map i.2.val) (U.map j.2.val) :=
    ⟨((A.onArrow i).cover.hom x,(A.onArrow j).cover.hom y),h⟩
  let w := t.homeomorph.symm p
  have ex : (U.map t.left.hom).hom w = (A.onArrow i).cover.hom x :=
    (t.left_apply w).symm.trans (congrArg (fun p ↦ p.val.1) (t.homeomorph.apply_symm_apply p))
  have ey : (U.map t.right.hom).hom w = (A.onArrow j).cover.hom y :=
    (t.right_apply w).symm.trans (congrArg (fun p ↦ p.val.2) (t.homeomorph.apply_symm_apply p))
  have ew : (U.map t.mid.2.val).hom w = ((A.onArrow i).cover ≫ U.map i.2.val).hom x := by
    rw [← t.left.comm, U.map_comp]
    exact congrArg (U.map i.2.val).hom ex
  let d := RankSieveRefinementArrow.constant c t.mid w (fun v ↦ (hc v).trans ew.symm)
  obtain ⟨z',hz⟩ := (A.onArrow t.mid).isCover.surjective w
  have hd : (A.onArrow t.mid).cover.hom z' = (U.map d.hom).hom ((A.onArrow c).cover.hom z) :=
    hz.trans (RankSieveRefinementArrow.constant_apply c t.mid w _ _).symm
  have hx : (A.onArrow i).cover.hom x = (U.map t.left.hom).hom ((A.onArrow t.mid).cover.hom z') :=
    ex.symm.trans (congrArg (U.map t.left.hom).hom hz).symm
  have hy : (A.onArrow j).cover.hom y = (U.map t.right.hom).hom ((A.onArrow t.mid).cover.hom z') :=
    ey.symm.trans (congrArg (U.map t.right.hom).hom hz).symm
  let a := RankSieveRefinementArrow.constant c i ((A.onArrow i).cover.hom x) hc
  let b := RankSieveRefinementArrow.constant c j ((A.onArrow j).cover.hom y) (fun v ↦ (hc v).trans h)
  have ha : d.comp t.left = a := by
    apply RankSieveRefinementArrow.ext_hom
    apply U.map_injective
    change U.map (d.hom ≫ t.left.hom) = U.map a.hom
    rw [U.map_comp]
    apply CGWH.ext_hom
    intro v
    exact ((congrArg (U.map t.left.hom).hom (RankSieveRefinementArrow.constant_apply c t.mid w _ v)).trans ex).trans
      (RankSieveRefinementArrow.constant_apply c i ((A.onArrow i).cover.hom x) hc v).symm
  have hb : d.comp t.right = b := by
    apply RankSieveRefinementArrow.ext_hom
    apply U.map_injective
    change U.map (d.hom ≫ t.right.hom) = U.map b.hom
    rw [U.map_comp]
    apply CGWH.ext_hom
    intro v
    exact ((congrArg (U.map t.right.hom).hom (RankSieveRefinementArrow.constant_apply c t.mid w _ v)).trans ey).trans
      (RankSieveRefinementArrow.constant_apply c j ((A.onArrow j).cover.hom y) _ v).symm
  let v : @Quiver.Hom G.Underlying _ ((A.onArrow c).point z) ((A.onArrow t.mid).point z') :=
    rankSieveRestrictionValue r d z z' hd
  let s : @Quiver.Hom G.Underlying _ ((A.onArrow t.mid).point z') ((A.onArrow i).point x) :=
    rankSieveRestrictionValue r t.left z' x hx
  let u : @Quiver.Hom G.Underlying _ ((A.onArrow t.mid).point z') ((A.onArrow j).point y) :=
    rankSieveRestrictionValue r t.right z' y hy
  have hs : v ≫ s = rankSieveConstantRestrictionValue r z x hc :=
    (hr.comp d t.left z z' x hd hx).trans (rankSieveRestrictionValue_congr r ha z x _ _)
  have hu : v ≫ u = rankSieveConstantRestrictionValue r z y (fun v ↦ (hc v).trans h) :=
    (hr.comp d t.right z z' y hd hy).trans (rankSieveRestrictionValue_congr r hb z y _ _)
  refine (t.overlapHom_value r x y z' hx hy h).trans ?_
  change Groupoid.inv s ≫ u =
    (@Groupoid.inv G.Underlying _ _ _ (rankSieveConstantRestrictionValue r z x hc)) ≫ _
  rw [← hs, ← hu]
  exact @cancel_shared_prefix G.Underlying _ _ _ _ _ v s u

private theorem rankSieve_exists_constant_presentingPoint {G : TopologicalGroupoid.{u}} {X : RankSpace α}
    {S : Sieve X} (A : RankSieveCocycleObjects (G := G) S) (i : RankSieveArrows S)
    (y : i.1.space.obj) : ∃ c : RankSieveArrows S, Nonempty (A.onArrow c).coverSpace.obj ∧
      ∀ v, ((rankSpaceInclusion α).map c.2.val).hom v = ((rankSpaceInclusion α).map i.2.val).hom y := by
  let U := rankSpaceInclusion α
  let a : i.1 ⟶ i.1 := U.preimage (CGWH.map (ContinuousMap.const _ y))
  let c : RankSieveArrows S := ⟨i.1,a ≫ i.2.val,S.downward_closed i.2.property a⟩
  obtain ⟨z,_⟩ := (A.onArrow c).isCover.surjective y
  refine ⟨c,⟨z⟩,?_⟩
  intro v
  change (U.map (a ≫ i.2.val)).hom v = _
  rw [U.map_comp, U.map_preimage]
  rfl

open QuotientCocycle in
/-- Composition coherence of the restriction arrows implies both overlap
identities. The unit and triple identities are checked using one common
constant refinement of the presenting points over the target. -/
theorem rankSievePairOverlap_cocycle {G : TopologicalGroupoid.{u}} {X : RankSpace α}
    {S : Sieve X} {A : RankSieveCocycleObjects (G := G) S} (r : RankSieveCocycleRestrictions A)
    (hr : RankSieveRestrictionsCoherent r) (hα : preBeth α = α.card) (hω : ℵ₀ < preBeth α) :
    PairwiseOverlapCocycle (fun i j : RankSieveArrows S ↦
      rankSievePairOverlapHom r i.2.val j.2.val i.2.property j.2.property hα hω) := by
  constructor
  · intro i x
    obtain ⟨c,⟨z⟩,hc⟩ := rankSieve_exists_constant_presentingPoint A i ((A.onArrow i).cover.hom x)
    refine (rankSieveOverlap_value_common hr (rankSieveOverlapTest i i hα hω) x x rfl z hc).trans ?_
    exact @Groupoid.inv_comp G.Underlying _ _ _ (rankSieveConstantRestrictionValue r z x hc)
  · intro i j k x y z hxy hyz
    obtain ⟨c,⟨w⟩,hc⟩ := rankSieve_exists_constant_presentingPoint A i ((A.onArrow i).cover.hom x)
    let a : @Quiver.Hom G.Underlying _ ((A.onArrow c).point w) ((A.onArrow i).point x) :=
      rankSieveConstantRestrictionValue r w x hc
    let b : @Quiver.Hom G.Underlying _ ((A.onArrow c).point w) ((A.onArrow j).point y) :=
      rankSieveConstantRestrictionValue r w y (fun v ↦ (hc v).trans hxy)
    let d : @Quiver.Hom G.Underlying _ ((A.onArrow c).point w) ((A.onArrow k).point z) :=
      rankSieveConstantRestrictionValue r w z (fun v ↦ (hc v).trans (hxy.trans hyz))
    have exy := rankSieveOverlap_value_common hr (rankSieveOverlapTest i j hα hω) x y hxy w hc
    have eyz := rankSieveOverlap_value_common hr (rankSieveOverlapTest j k hα hω) y z hyz w
      (fun v ↦ (hc v).trans hxy)
    have exz := rankSieveOverlap_value_common hr (rankSieveOverlapTest i k hα hω) x z (hxy.trans hyz) w hc
    refine Eq.trans (congrArg₂ (@CategoryStruct.comp G.Underlying _ _ _ _) exy eyz) (Eq.trans ?_ exz.symm)
    exact @compose_spans G.Underlying _ _ _ _ _ a b d

private theorem cancel_prefix {C : Type*} [Groupoid C] {a b c : C}
    (s : a ⟶ b) (t : b ⟶ c) : Groupoid.inv s ≫ (s ≫ t) = t := by simp

open QuotientCocycle in
/-- On a refinement between two sieve domains the overlap arrow agrees
pointwise with the original restriction arrow. -/
theorem RankSieveOverlapTest.overlapHom_value_of_refinement {G : TopologicalGroupoid.{u}} {X : RankSpace α}
    {S : Sieve X} {A : RankSieveCocycleObjects (G := G) S} {r : RankSieveCocycleRestrictions A}
    (hr : RankSieveRestrictionsCoherent r) {i j : RankSieveArrows S} (t : RankSieveOverlapTest i j)
    (a : RankSieveRefinementArrow i j) (x : (A.onArrow i).coverSpace.obj) (y : (A.onArrow j).coverSpace.obj)
    (hy : (A.onArrow j).cover.hom y = ((rankSpaceInclusion α).map a.hom).hom ((A.onArrow i).cover.hom x))
    (h : ((A.onArrow i).cover ≫ (rankSpaceInclusion α).map i.2.val).hom x =
      ((A.onArrow j).cover ≫ (rankSpaceInclusion α).map j.2.val).hom y) :
    pairOverlapValue (A.onArrow i) (A.onArrow j) ((rankSpaceInclusion α).map i.2.val)
      ((rankSpaceInclusion α).map j.2.val) (t.overlapHom r) x y h = rankSieveRestrictionValue r a x y hy := by
  let U := rankSpaceInclusion α
  let p := (A.onArrow i).cover.hom x
  let q := (A.onArrow j).cover.hom y
  obtain ⟨c,⟨z⟩,hc⟩ := rankSieve_exists_constant_presentingPoint A i p
  let b := RankSieveRefinementArrow.constant c i p hc
  let d := RankSieveRefinementArrow.constant c j q (fun v ↦ (hc v).trans h)
  have hb := (RankSieveRefinementArrow.constant_apply c i p hc ((A.onArrow c).cover.hom z)).symm
  have he : b.comp a = d := by
    apply RankSieveRefinementArrow.ext_hom
    apply U.map_injective
    change U.map (b.hom ≫ a.hom) = U.map d.hom
    rw [U.map_comp]
    apply CGWH.ext_hom
    intro v
    exact ((congrArg (U.map a.hom).hom (RankSieveRefinementArrow.constant_apply c i p hc v)).trans hy.symm).trans
      (RankSieveRefinementArrow.constant_apply c j q _ v).symm
  let s : @Quiver.Hom G.Underlying _ ((A.onArrow c).point z) ((A.onArrow i).point x) :=
    rankSieveConstantRestrictionValue r z x hc
  let u : @Quiver.Hom G.Underlying _ ((A.onArrow i).point x) ((A.onArrow j).point y) :=
    rankSieveRestrictionValue r a x y hy
  have hu : s ≫ u = rankSieveConstantRestrictionValue r z y (fun v ↦ (hc v).trans h) :=
    (hr.comp b a z x y hb hy).trans (rankSieveRestrictionValue_congr r he z y _ _)
  refine (rankSieveOverlap_value_common hr t x y h z hc).trans ?_
  change Groupoid.inv s ≫ rankSieveConstantRestrictionValue r z y (fun v ↦ (hc v).trans h) = u
  rw [← hu]
  exact @cancel_prefix G.Underlying _ _ _ _ s u

open QuotientCocycle in
/-- The presenting-cover overlap data of coherent objects on a sieve. -/
noncomputable def rankSieveCoherentOverlap {G : TopologicalGroupoid.{u}} {X : RankSpace α}
    {S : Sieve X} {A : RankSieveCocycleObjects (G := G) S} {r : RankSieveCocycleRestrictions A}
    (hr : RankSieveRestrictionsCoherent r) (hα : preBeth α = α.card) (hω : ℵ₀ < preBeth α) :
    FamilyOverlap (fun i : RankSieveArrows S ↦ (rankSpaceInclusion α).map i.2.val) A.onArrow :=
  FamilyOverlap.ofPairwise (fun i j ↦ rankSievePairOverlapHom r i.2.val j.2.val i.2.property j.2.property hα hω)
    (rankSievePairOverlap_cocycle r hr hα hω)

open QuotientCocycle in
/-- The transitions of the presenting-cover overlap data recover the
given restriction arrows on every refinement sample. -/
theorem rankSieveCoherentOverlap_arrow_of_refinement {G : TopologicalGroupoid.{u}} {X : RankSpace α}
    {S : Sieve X} {A : RankSieveCocycleObjects (G := G) S} {r : RankSieveCocycleRestrictions A}
    (hr : RankSieveRestrictionsCoherent r) (hα : preBeth α = α.card) (hω : ℵ₀ < preBeth α)
    {i j : RankSieveArrows S} (a : RankSieveRefinementArrow i j)
    (x : (A.onArrow i).coverSpace.obj) (y : (A.onArrow j).coverSpace.obj)
    (hy : (A.onArrow j).cover.hom y = ((rankSpaceInclusion α).map a.hom).hom ((A.onArrow i).cover.hom x))
    (h : ((A.onArrow i).cover ≫ (rankSpaceInclusion α).map i.2.val).hom x =
      ((A.onArrow j).cover ≫ (rankSpaceInclusion α).map j.2.val).hom y) :
    (rankSieveCoherentOverlap hr hα hω).arrow i j ⟨(x,y),h⟩ = (rankSieveRestrictionValue r a x y hy).val :=
  congrArg Subtype.val ((rankSieveOverlapTest i j hα hω).overlapHom_value_of_refinement hr a x y hy h)

open QuotientCocycle in
/-- The local objects on a canonical sieve descend to a rank-bounded
global object when their pairwise restriction arrows satisfy the unit and
triple-overlap identities. This recovers every object of the sieve. -/
theorem rankCanonicalSieve_descendPairwiseObjects {G : TopologicalGroupoid.{u}} {X : RankSpace α}
    (S : Sieve X) (hα : preBeth α = α.card) (hω : ℵ₀ < preBeth α) (hκ : (preBeth α).IsStrongLimit)
    (hS : S ∈ Sheaf.canonicalTopology (RankSpace α) X)
    (A : RankSieveCocycleObjects (G := G) S) (r : RankSieveCocycleRestrictions A)
    (hr : PairwiseOverlapCocycle (fun i j : RankSieveArrows S ↦
      rankSievePairOverlapHom r i.2.val j.2.val i.2.property j.2.property hα hω)) :
    ∃ B : QuotientCocycle G X.space, #(B.coverSpace.obj : Type u) < preBeth α ∧
      ∀ ⦃Y : RankSpace α⦄ (g : Y ⟶ X) (hg : S g),
        Nonempty (A g hg ≅ B.pullback ((rankSpaceInclusion α).map g)) := by
  let k (i : RankSieveArrows S) := (rankSpaceInclusion α).map i.2.val
  let s (i j : RankSieveArrows S) := rankSievePairOverlapHom r i.2.val j.2.val i.2.property j.2.property hα hω
  have hq : IsQuotientMap (sumDesc k).hom := (rankCanonicalTopology_iff S hα hω).mp hS
  let data := FamilyOverlap.ofPairwise s hr
  let B₀ := data.descend hq
  obtain ⟨V,_,B,_,⟨hB,_⟩,⟨eB⟩⟩ := rankCocycle_exists_bounded_presentation B₀ hα hω hκ
  refine ⟨B,?_,?_⟩
  · rw [hB]
    exact V.carrier_lt
  · intro Y g hg
    let i : RankSieveArrows S := ⟨Y,g,hg⟩
    obtain ⟨a⟩ := data.descend_restrict_iso hq i
    let F := pullbackFunctor (G := G) (k i)
    exact ⟨a ≪≫ F.mapIso eB.symm⟩

/-- Coherent restrictions of cocycle objects on an arbitrary canonical
sieve have a global rank-bounded presentation. -/
theorem rankCanonicalSieve_descendCoherentObjects {G : TopologicalGroupoid.{u}} {X : RankSpace α}
    (S : Sieve X) (hα : preBeth α = α.card) (hω : ℵ₀ < preBeth α) (hκ : (preBeth α).IsStrongLimit)
    (hS : S ∈ Sheaf.canonicalTopology (RankSpace α) X)
    (A : RankSieveCocycleObjects (G := G) S) (r : RankSieveCocycleRestrictions A)
    (hr : RankSieveRestrictionsCoherent r) :
    ∃ B : QuotientCocycle G X.space, #(B.coverSpace.obj : Type u) < preBeth α ∧
      ∀ ⦃Y : RankSpace α⦄ (g : Y ⟶ X) (hg : S g),
        Nonempty (A g hg ≅ B.pullback ((rankSpaceInclusion α).map g)) :=
  rankCanonicalSieve_descendPairwiseObjects S hα hω hκ hS A r (rankSievePairOverlap_cocycle r hr hα hω)

end Masullo.TopologicalGroupoid
