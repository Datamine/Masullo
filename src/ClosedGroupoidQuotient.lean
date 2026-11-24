import RankQuotientCocycles
import Mathlib.CategoryTheory.Discrete.Basic

/-! A topological groupoid with a closed embedding of arrows into the
ordinary object square presents its orbit space. -/

open CategoryTheory Function Set Topology TopologicalSpace
open Cardinal
open scoped Cardinal Ordinal

noncomputable section

namespace Masullo.TopologicalGroupoid

universe u

/-- Two objects lie in the same orbit if there is an arrow between them. -/
def orbitSetoid (G : TopologicalGroupoid.{u}) : Setoid G.objects.obj where
  r x y := ∃ a : G.arrows.obj, G.source a = x ∧ G.target a = y
  iseqv := {
    refl x := ⟨G.unit x, G.source_unit x, G.target_unit x⟩
    symm := by
      rintro x y ⟨a,ha,hb⟩
      exact ⟨G.inverse a, (G.source_inv a).trans hb, (G.target_inv a).trans ha⟩
    trans := by
      rintro x y z ⟨a,ha,hay⟩ ⟨b,hby,hb⟩
      let p : ComposableArrows G.source.toFun G.target.toFun := ⟨(a,b), hay.trans hby.symm⟩
      exact ⟨G.comp p, (G.source_comp p).trans ha, (G.target_comp p).trans hb⟩ }

def ordinaryEndpoints (G : TopologicalGroupoid.{u}) :
    G.arrows.obj → G.objects.obj × G.objects.obj :=
  fun a ↦ (G.source a, G.target a)

/-- Closedness in the ordinary square implies closedness in the Kelley
square, so the ordinary topological quotient already belongs to CGWH. -/
def closedOrbitSpace (G : TopologicalGroupoid.{u})
    (hG : IsClosedEmbedding (ordinaryEndpoints G)) : CGWH.{u} := by
  let Q := Quotient (orbitSetoid G)
  refine CGWH.of (X := Q) ((weaklyHausdorff_quotient_iff_closed_relation _ _).mpr ?_)
  have he : {p : Kelley (G.objects.obj × G.objects.obj) | orbitSetoid G p.1 p.2} =
      (fun p : Kelley (G.objects.obj × G.objects.obj) ↦
        (p : G.objects.obj × G.objects.obj)) ⁻¹' range (ordinaryEndpoints G) := by
    ext p
    exact exists_congr fun a ↦ (Prod.mk.injEq _ _ _ _).to_iff.symm

  rw [he]
  exact hG.isClosed_range.preimage continuous_Kelley_forget

/-- The canonical map to the orbit space. -/
def closedOrbitMap (G : TopologicalGroupoid.{u})
    (hG : IsClosedEmbedding (ordinaryEndpoints G)) : G.objects ⟶ closedOrbitSpace G hG :=
  CGWH.map ⟨@Quotient.mk' G.objects.obj (orbitSetoid G), continuous_quotient_mk'⟩

theorem closedOrbitMap_isQuotientMap (G : TopologicalGroupoid.{u})
    (hG : IsClosedEmbedding (ordinaryEndpoints G)) :
    IsQuotientMap (closedOrbitMap G hG).hom :=
  @isQuotientMap_quotient_mk' G.objects.obj _ (orbitSetoid G)

private theorem orbitMap_eq_iff (G : TopologicalGroupoid.{u})
    (hG : IsClosedEmbedding (ordinaryEndpoints G)) (x y : G.objects.obj) :
    (closedOrbitMap G hG).hom x = (closedOrbitMap G hG).hom y ↔
      ∃ a : G.arrows.obj, G.source a = x ∧ G.target a = y :=
  @Quotient.eq'' G.objects.obj (orbitSetoid G) x y

/-- The orbit projection as a functor to the unit groupoid of the quotient. -/
def closedOrbitFunctor (G : TopologicalGroupoid.{u})
    (hG : IsClosedEmbedding (ordinaryEndpoints G)) : G ⟶ constant (closedOrbitSpace G hG) where
  objectMap := (closedOrbitMap G hG).hom.hom.hom
  arrowMap := (closedOrbitMap G hG).hom.hom.hom.comp G.source
  mapSource _ := rfl
  mapTarget a := (orbitMap_eq_iff G hG _ _).mpr ⟨a,rfl,rfl⟩
  mapUnit x := congrArg (closedOrbitMap G hG).hom (G.source_unit x)
  mapInverse a := (congrArg (closedOrbitMap G hG).hom (G.source_inv a)).trans
    ((orbitMap_eq_iff G hG _ _).mpr ⟨a,rfl,rfl⟩).symm
  mapComp a b hab := congrArg (closedOrbitMap G hG).hom (G.source_comp ⟨(a,b),hab⟩)

/-- The arrow comparison of the quotient projection is a homeomorphism.
Its inverse is continuous by the given ordinary embedding. -/
theorem closedOrbitFunctor_isStandardMorita (G : TopologicalGroupoid.{u})
    (hG : IsClosedEmbedding (ordinaryEndpoints G)) :
    IsStandardMorita (closedOrbitFunctor G hG) := by
  let f := closedOrbitFunctor G hG
  refine ⟨closedOrbitMap_isQuotientMap G hG, ?_⟩
  have hex (p : ArrowComparisonSpace f) :
      ∃ a : G.arrows.obj, G.source a = p.val.1.1 ∧ G.target a = p.val.1.2 := by
    have e : (closedOrbitMap G hG).hom p.val.1.1 = p.val.2 :=
      congrArg Prod.fst p.property
    have e' : (closedOrbitMap G hG).hom p.val.1.2 = p.val.2 :=
      congrArg Prod.snd p.property
    exact (orbitMap_eq_iff G hG _ _).mp (e.trans e'.symm)
  let inv (p : ArrowComparisonSpace f) : G.arrows.obj := (hex p).choose
  have hInv (p : ArrowComparisonSpace f) :
      ordinaryEndpoints G (inv p) = (p.val.1.1, p.val.1.2) :=
    Prod.ext (hex p).choose_spec.1 (hex p).choose_spec.2
  have hFirst : Continuous (fun p : ArrowComparisonSpace f ↦
      (p.val.1 : Kelley (G.objects.obj × G.objects.obj))) :=
    continuous_fst.comp (continuous_Kelley_forget.comp continuous_subtype_val)
  have hp : Continuous (fun p : ArrowComparisonSpace f ↦
      (p.val.1.1, p.val.1.2)) :=
    (continuous_Kelley_forget (X := G.objects.obj × G.objects.obj)).comp hFirst
  have hinv : Continuous inv := by
    apply hG.isEmbedding.isInducing.continuous_iff.mpr
    exact hp.congr (fun p ↦ (hInv p).symm)
  have hright (p : ArrowComparisonSpace f) : arrowComparison f (inv p) = p := by
    refine arrowComparison_eq f p (inv p) (hex p).choose_spec.1 (hex p).choose_spec.2 ?_
    exact (congrArg (closedOrbitMap G hG).hom (hex p).choose_spec.1).trans
      (congrArg Prod.fst p.property)
  exact ⟨{
    toFun := arrowComparison f
    invFun := inv
    left_inv := fun a ↦ hG.isEmbedding.injective (hInv (arrowComparison f a))
    right_inv := hright
    continuous_toFun := (arrowComparison f).continuous
    continuous_invFun := hinv }, fun _ ↦ rfl⟩


namespace QuotientCocycle

variable {Q T : CGWH.{u}}

/-- A cocycle in the unit groupoid descends to an ordinary continuous map. -/
def unitDescendedMap (A : QuotientCocycle (constant Q) T) : C(T.obj, Q.obj) := by
  let d (t : T.obj) := A.point ((A.isCover.surjective t).choose)
  have hd (x : A.coverSpace.obj) : d (A.cover.hom x) = A.point x := by
    let p : CGWH.FibreSubspace A.cover A.cover :=
      ⟨((A.isCover.surjective (A.cover.hom x)).choose, x),
        (A.isCover.surjective (A.cover.hom x)).choose_spec⟩
    exact (A.transitionSource p).symm.trans (A.transitionTarget p)
  exact ⟨d, A.isCover.continuous_iff.mpr ((A.point.continuous).congr (fun x ↦ (hd x).symm))⟩

theorem unitDescendedMap_cover (A : QuotientCocycle (constant Q) T) (x : A.coverSpace.obj) :
    A.unitDescendedMap (A.cover.hom x) = A.point x := by
  let p : CGWH.FibreSubspace A.cover A.cover :=
    ⟨((A.isCover.surjective (A.cover.hom x)).choose, x),
      (A.isCover.surjective (A.cover.hom x)).choose_spec⟩
  exact (A.transitionSource p).symm.trans (A.transitionTarget p)

private theorem unitDescendedMap_hom {A B : QuotientCocycle (constant Q) T} (r : A ⟶ B) :
    A.unitDescendedMap = B.unitDescendedMap := by
  ext t
  obtain ⟨x,hx⟩ := A.isCover.surjective t
  obtain ⟨y,hy⟩ := B.isCover.surjective t
  let p : CGWH.FibreSubspace A.cover B.cover := ⟨(x,y),hx.trans hy.symm⟩
  exact ((congrArg A.unitDescendedMap hx).symm.trans
    (A.unitDescendedMap_cover x)).trans ((r.val.property.1 p).symm.trans
      ((r.val.property.2 p).trans ((B.unitDescendedMap_cover y).symm.trans
        (congrArg B.unitDescendedMap hy))))

private theorem unitHom_subsingleton (A B : QuotientCocycle (constant Q) T) :
    Subsingleton (A ⟶ B) := by
  refine ⟨fun r s ↦ Subtype.ext (Subtype.ext (ContinuousMap.ext fun p ↦ ?_))⟩
  exact (r.val.property.1 p).trans (s.val.property.1 p).symm

private def unitHomOfEq {A B : QuotientCocycle (constant Q) T}
    (h : A.unitDescendedMap = B.unitDescendedMap) : A ⟶ B := by
  let p₁ : C(CGWH.FibreSubspace A.cover B.cover, A.coverSpace.obj) :=
    ⟨fun p ↦ p.val.1, continuous_fst.comp (continuous_Kelley_forget.comp continuous_subtype_val)⟩
  have hp (p : CGWH.FibreSubspace A.cover B.cover) : A.point p.val.1 = B.point p.val.2 := by
    rw [← A.unitDescendedMap_cover p.val.1, ← B.unitDescendedMap_cover p.val.2, h, p.property]
  refine ⟨⟨A.point.comp p₁, fun _ ↦ rfl, hp⟩, ?_⟩
  intro p q hp hq
  have hthin (x y : (constant Q).Underlying) : Subsingleton ((constant Q).UnderlyingArrow x y) :=
    ⟨fun a b ↦ Subtype.ext (a.property.1.trans b.property.1.symm)⟩
  exact (hthin (A.point p.val.1) (B.point q.val.2)).elim _ _

/-- The unit-groupoid cocycle category represents the functor of points. -/
def unitDescendedFunctor (Q T : CGWH.{u}) :
    QuotientCocycle (constant Q) T ⥤ Discrete C(T.obj, Q.obj) where
  obj A := Discrete.mk A.unitDescendedMap
  map r := Discrete.eqToHom' (unitDescendedMap_hom r)
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

theorem unitDescendedFunctor_fullyFaithful (Q T : CGWH.{u}) :
    Nonempty (unitDescendedFunctor Q T).FullyFaithful := by
  refine (Functor.FullyFaithful.nonempty_iff_map_bijective _).mpr fun A B ↦ ⟨?_, ?_⟩
  · intro a b _
    exact (unitHom_subsingleton A B).elim a b
  · intro r
    exact ⟨unitHomOfEq (Discrete.eq_of_hom r), Subsingleton.elim _ _⟩

theorem unitDescendedMap_ofPoint (a : C(T.obj, Q.obj)) :
    (ofPoint (G := constant Q) (T := T) a).unitDescendedMap = a :=
  ContinuousMap.ext fun t ↦ unitDescendedMap_cover (ofPoint (G := constant Q) (T := T) a) t

private theorem unitDescendedFunctor_isEquivalence (Q T : CGWH.{u}) :
    (unitDescendedFunctor Q T).IsEquivalence := by
  obtain ⟨h⟩ := unitDescendedFunctor_fullyFaithful Q T
  letI := h.full
  letI := h.faithful
  letI : (unitDescendedFunctor Q T).EssSurj := ⟨fun a ↦
    ⟨ofPoint (G := constant Q) (T := T) a.as,
      ⟨eqToIso (congrArg Discrete.mk (unitDescendedMap_ofPoint a.as))⟩⟩⟩
  exact {}

end QuotientCocycle

/-- The quotient projection represents cocycles by maps to the ordinary
orbit space, with no choice of orbit representatives in the target. -/
def closedOrbitRepresentation (G : TopologicalGroupoid.{u})
    (hG : IsClosedEmbedding (ordinaryEndpoints G)) (T : CGWH.{u}) :
    QuotientCocycle G T ⥤ Discrete C(T.obj, (closedOrbitSpace G hG).obj) :=
  QuotientCocycle.mapCocycles (closedOrbitFunctor G hG) ⋙
    QuotientCocycle.unitDescendedFunctor (closedOrbitSpace G hG) T

/-- E.6.3.8 on all CGWH test spaces. -/
theorem closedOrbitRepresentation_isEquivalence (G : TopologicalGroupoid.{u})
    (hG : IsClosedEmbedding (ordinaryEndpoints G)) (T : CGWH.{u}) :
    (closedOrbitRepresentation G hG T).IsEquivalence := by
  letI := QuotientCocycle.mapCocycles_isEquivalence_of_standardMorita (T := T)
    (closedOrbitFunctor G hG) (closedOrbitFunctor_isStandardMorita G hG)
  letI := QuotientCocycle.unitDescendedFunctor_isEquivalence (closedOrbitSpace G hG) T
  unfold closedOrbitRepresentation
  infer_instance

/-- The representing maps commute with arbitrary change of the test space. -/
theorem closedOrbitRepresentation_pullback (G : TopologicalGroupoid.{u})
    (hG : IsClosedEmbedding (ordinaryEndpoints G)) {S T : CGWH.{u}}
    (g : S ⟶ T) (A : QuotientCocycle G T) :
    ((closedOrbitRepresentation G hG S).obj (A.pullback g)).as =
      ((closedOrbitRepresentation G hG T).obj A).as.comp g.hom.hom.hom := by
  apply ContinuousMap.ext
  intro s
  obtain ⟨x,hx⟩ := A.isCover.surjective (g.hom s)
  let p : CGWH.FibreSubspace A.cover g := ⟨(x,s),hx⟩
  change (QuotientCocycle.map (closedOrbitFunctor G hG) (A.pullback g)).unitDescendedMap
      ((A.pullback g).cover.hom p) =
    (QuotientCocycle.map (closedOrbitFunctor G hG) A).unitDescendedMap (g.hom s)
  let U := QuotientCocycle.map (closedOrbitFunctor G hG) (A.pullback g)
  let V := QuotientCocycle.map (closedOrbitFunctor G hG) A
  exact (QuotientCocycle.unitDescendedMap_cover U p).trans
    ((QuotientCocycle.unitDescendedMap_cover V x).symm.trans (congrArg V.unitDescendedMap hx))


/-- The orbit space has a representative on the same rank site as the
object space. -/
theorem closedOrbitSpace_rankRepresentative {α : Ordinal.{u}} (G : TopologicalGroupoid.{u})
    (hG : IsClosedEmbedding (ordinaryEndpoints G)) (hα : preBeth α = α.card)
    (hX : #(G.objects.obj : Type u) < preBeth α) :
    ∃ Q : RankSpace α, Nonempty (Q.space.obj ≃ₜ (closedOrbitSpace G hG).obj) :=
  rankSpace_representative hα _ ((mk_le_of_surjective
    (closedOrbitMap_isQuotientMap G hG).surjective).trans_lt hX)

/-- A map into the orbit space lifts to a cocycle on a quotient cover whose
carrier has the same cardinal bound as the rank site. -/
theorem closedOrbitRepresentation_boundedLift {α : Ordinal.{u}} (G : TopologicalGroupoid.{u})
    (hG : IsClosedEmbedding (ordinaryEndpoints G)) (hω : ℵ₀ < preBeth α)
    (hX : #(G.objects.obj : Type u) < preBeth α) {T : CGWH.{u}}
    (hT : #(T.obj : Type u) < preBeth α) (a : C(T.obj, (closedOrbitSpace G hG).obj)) :
    ∃ B : QuotientCocycle G T, #(B.coverSpace.obj : Type u) < preBeth α ∧
      ((closedOrbitRepresentation G hG T).obj B).as = a := by
  let Q := closedOrbitSpace G hG
  let q := closedOrbitMap G hG
  let f := closedOrbitFunctor G hG
  let g : T ⟶ Q := CGWH.map a
  let V := CGWH.FibreSubspace q g
  let W : CGWH.{u} := CGWH.of (X := V) (CGWH.fibreSubspace_weaklyHausdorff q g)
  let r : W ⟶ T := CGWH.map
    ⟨fun p : V ↦ p.val.2, continuous_snd.comp (continuous_Kelley_forget.comp continuous_subtype_val)⟩
  let l : G.Points W :=
    ⟨fun p : V ↦ p.val.1, continuous_fst.comp (continuous_Kelley_forget.comp continuous_subtype_val)⟩
  have hr : IsQuotientMap r.hom := CGWH.quotient_baseChange q g (closedOrbitMap_isQuotientMap G hG)
  let A := (QuotientCocycle.ofPoint (G := constant Q) (T := T) a).refineCover r hr
  obtain ⟨e,he⟩ := (closedOrbitFunctor_isStandardMorita G hG).2
  obtain ⟨B,hB⟩ := QuotientCocycle.liftCocycle_of_point (A := A) f e he l
    (fun p ↦ p.property)
  have hBW : B.coverSpace = W := congrArg QuotientCocycle.coverSpace hB
  have hV : #V < preBeth α := by
    refine (mk_le_of_injective (f := fun p : V ↦
      (show G.objects.obj × T.obj from (p.val.1,p.val.2))) ?_).trans_lt ?_
    · intro p p' h
      exact Subtype.ext h
    · simp only [mk_prod, lift_id]
      exact mul_lt_of_lt hω.le hX hT
  refine ⟨B, by rw [hBW]; exact hV, ?_⟩
  change (B.map f).unitDescendedMap = a
  rw [hB]
  apply ContinuousMap.ext
  intro t
  obtain ⟨p,hp⟩ := hr.surjective t
  rw [← hp]
  exact QuotientCocycle.unitDescendedMap_cover A p

/-- The full category of cocycles whose covers satisfy the rank bound. -/
def boundedOrbitCocycles (α : Ordinal.{u}) (G : TopologicalGroupoid.{u}) (T : CGWH.{u}) :
    ObjectProperty (QuotientCocycle G T) :=
  fun A ↦ #(A.coverSpace.obj : Type u) < preBeth α

/-- The corrected proof of E.6.3.8 on the manuscript's rank site. The
equivalence is induced by the orbit map on the actual bounded cocycles. -/
theorem closedOrbitRepresentation_boundedEquivalence {α : Ordinal.{u}} (G : TopologicalGroupoid.{u})
    (hG : IsClosedEmbedding (ordinaryEndpoints G)) (hω : ℵ₀ < preBeth α)
    (hX : #(G.objects.obj : Type u) < preBeth α) (T : RankSpace α) :
    ((boundedOrbitCocycles α G T.space).ι ⋙ closedOrbitRepresentation G hG T.space).IsEquivalence := by
  let P := boundedOrbitCocycles α G T.space
  let F := closedOrbitRepresentation G hG T.space
  letI := closedOrbitRepresentation_isEquivalence G hG T.space
  letI : (P.ι ⋙ F).EssSurj := ⟨fun a ↦ by
    obtain ⟨B,hB,he⟩ := closedOrbitRepresentation_boundedLift G hG hω hX T.carrier_lt a.as
    exact ⟨⟨B,hB⟩, ⟨eqToIso (congrArg Discrete.mk he)⟩⟩⟩
  change (P.ι ⋙ F).IsEquivalence
  exact {}

/-- Each map to the quotient has a presentation on an actual canonical
singleton cover, even when the fibre-product carrier was initially abstract. -/
theorem closedOrbitRepresentation_canonicalLift {α : Ordinal.{u}} (G : TopologicalGroupoid.{u})
    (hG : IsClosedEmbedding (ordinaryEndpoints G)) (hα : preBeth α = α.card)
    (hω : ℵ₀ < preBeth α) (hX : #(G.objects.obj : Type u) < preBeth α)
    (T : RankSpace α) (a : C(T.space.obj, (closedOrbitSpace G hG).obj)) :
    ∃ (W : RankSpace α) (q : W ⟶ T) (B : QuotientCocycle G T.space),
      Sieve.generate (Presieve.singleton q) ∈ Sheaf.canonicalTopology (RankSpace α) T ∧
      (∃ h : B.coverSpace = W.space,
        cast (congrArg (fun Z : CGWH.{u} ↦ Z ⟶ T.space) h) B.cover =
          (rankSpaceInclusion α).map q) ∧
      ((closedOrbitRepresentation G hG T.space).obj B).as = a := by
  obtain ⟨A,hA,ha⟩ := closedOrbitRepresentation_boundedLift G hG hω hX T.carrier_lt a
  obtain ⟨W,q,B,hq,hB,⟨i⟩⟩ := rankCocycle_exists_canonical_presentation A hα hω hA
  let F := closedOrbitRepresentation G hG T.space
  exact ⟨W,q,B,hq,hB,(Discrete.eq_of_hom (F.map i.hom)).trans ha⟩


/-- Isomorphism classes of quotient cocycles. For a groupoid with embedded
endpoints the morphisms within each class are unique. -/
def cocycleIsoSetoid (G : TopologicalGroupoid.{u}) (T : CGWH.{u}) :
    Setoid (QuotientCocycle G T) where
  r A B := Nonempty (A ≅ B)
  iseqv := {
    refl A := ⟨Iso.refl A⟩
    symm := fun ⟨e⟩ ↦ ⟨e.symm⟩
    trans := fun ⟨e⟩ ⟨f⟩ ↦ ⟨e ≪≫ f⟩ }

/-- The class presheaf records pullback of actual cocycles. -/
def rankCocycleClasses (α : Ordinal.{u}) (G : TopologicalGroupoid.{u}) :
    (RankSpace α)ᵒᵖ ⥤ Type (u + 1) where
  obj X := Quotient (cocycleIsoSetoid G X.unop.space)
  map {X _} f := TypeCat.ofHom (Quotient.map'
    (fun A : QuotientCocycle G X.unop.space ↦ A.pullback ((rankSpaceInclusion α).map f.unop))
    (fun _ _ ⟨e⟩ ↦ ⟨(QuotientCocycle.pullbackFunctor ((rankSpaceInclusion α).map f.unop)).mapIso e⟩))
  map_id X := by
    apply ConcreteCategory.hom_ext
    intro a
    refine Quotient.inductionOn a fun A ↦ ?_
    change Quotient.mk'' (A.pullback ((rankSpaceInclusion α).map (𝟙 X.unop))) = Quotient.mk'' A
    rw [(rankSpaceInclusion α).map_id]
    exact Quotient.sound (QuotientCocycle.pullback_id_obj_iso A)
  map_comp {X Y Z} f g := by
    apply ConcreteCategory.hom_ext
    intro a
    refine Quotient.inductionOn a fun A ↦ ?_
    change Quotient.mk'' (A.pullback ((rankSpaceInclusion α).map (g.unop ≫ f.unop))) =
      Quotient.mk'' ((A.pullback ((rankSpaceInclusion α).map f.unop)).pullback
        ((rankSpaceInclusion α).map g.unop))
    rw [(rankSpaceInclusion α).map_comp]
    obtain ⟨e⟩ := QuotientCocycle.pullback_comp_obj_iso A
      ((rankSpaceInclusion α).map f.unop) ((rankSpaceInclusion α).map g.unop)
    exact Quotient.sound ⟨e.symm⟩

private def rankCocycleClassEquiv {α : Ordinal.{u}} (G : TopologicalGroupoid.{u})
    (hG : IsClosedEmbedding (ordinaryEndpoints G)) (T R : RankSpace α)
    (e : R.space ≅ closedOrbitSpace G hG) :
    Quotient (cocycleIsoSetoid G T.space) ≃ (T ⟶ R) := by
  let F := closedOrbitRepresentation G hG T.space
  let U := rankSpaceInclusion α
  let d (A : QuotientCocycle G T.space) : T ⟶ R :=
    U.preimage (CGWH.map (F.obj A).as ≫ e.inv)
  let k : Quotient (cocycleIsoSetoid G T.space) → (T ⟶ R) :=
    Quotient.lift d (fun A B ⟨i⟩ ↦ by
      have h := Discrete.eq_of_hom (F.map i.hom)
      dsimp [d]
      rw [h])
  refine Equiv.ofBijective k ⟨?_, ?_⟩
  · intro a b
    refine Quotient.inductionOn₂ a b fun A B h ↦ ?_
    change d A = d B at h
    have hm : CGWH.map (F.obj A).as ≫ e.inv = CGWH.map (F.obj B).as ≫ e.inv := by
      simpa only [d, Functor.map_preimage] using congrArg U.map h
    have hF : F.obj A = F.obj B := by
      apply Discrete.ext
      have hmap := (cancel_mono e.inv).mp hm
      apply ContinuousMap.ext
      intro x
      exact congrArg (fun f : T.space ⟶ closedOrbitSpace G hG ↦ f.hom x) hmap
    letI := closedOrbitRepresentation_isEquivalence G hG T.space
    exact Quotient.sound ⟨F.preimageIso (eqToIso hF)⟩
  · intro q
    let a : C(T.space.obj, (closedOrbitSpace G hG).obj) :=
      (U.map q ≫ e.hom).hom.hom.hom
    letI := closedOrbitRepresentation_isEquivalence G hG T.space
    obtain ⟨A, ⟨i⟩⟩ := Functor.EssSurj.mem_essImage F (Discrete.mk a)
    have h := Discrete.eq_of_hom i.hom
    refine ⟨Quotient.mk'' A, ?_⟩
    change d A = q
    apply U.map_injective
    rw [show U.map (d A) = CGWH.map (F.obj A).as ≫ e.inv from U.map_preimage _, h]
    change (U.map q ≫ e.hom) ≫ e.inv = _
    simp

/-- On the canonical rank site the cocycle classes identify naturally with
the represented presheaf of the orbit space. -/
def rankCocycleClassesYoneda {α : Ordinal.{u}} (G : TopologicalGroupoid.{u})
    (hG : IsClosedEmbedding (ordinaryEndpoints G)) (R : RankSpace α)
    (e : R.space ≅ closedOrbitSpace G hG) :
    rankCocycleClasses α G ≅ yoneda.obj R ⋙ uliftFunctor.{u + 1, u} := by
  refine NatIso.ofComponents (fun T ↦ Equiv.toIso
    ((rankCocycleClassEquiv G hG T.unop R e).trans Equiv.ulift.symm)) ?_
  intro X Y f
  apply ConcreteCategory.hom_ext
  intro a
  apply ULift.ext
  refine Quotient.inductionOn a fun A ↦ ?_
  apply (rankSpaceInclusion α).map_injective
  change (rankSpaceInclusion α).map ((rankCocycleClassEquiv G hG Y.unop R e)
      (Quotient.mk'' (A.pullback ((rankSpaceInclusion α).map f.unop)))) =
    (rankSpaceInclusion α).map (f.unop ≫ (rankCocycleClassEquiv G hG X.unop R e) (Quotient.mk'' A))
  let U := rankSpaceInclusion α
  let k := U.map f.unop
  change U.map (U.preimage (CGWH.map ((closedOrbitRepresentation G hG Y.unop.space).obj
      (A.pullback k)).as ≫ e.inv)) =
    U.map (f.unop ≫ U.preimage (CGWH.map ((closedOrbitRepresentation G hG X.unop.space).obj A).as ≫ e.inv))
  rw [U.map_comp, U.map_preimage, U.map_preimage, closedOrbitRepresentation_pullback]
  exact Category.assoc k (CGWH.map ((closedOrbitRepresentation G hG X.unop.space).obj A).as) e.inv


/-- The cocycle classes glue uniquely for every canonical covering sieve.
Together with uniqueness of each cocycle arrow with fixed endpoints, this
gives descent of the represented quotient groupoids. -/
theorem rankCocycleClasses_isSheaf {α : Ordinal.{u}} (G : TopologicalGroupoid.{u})
    (hG : IsClosedEmbedding (ordinaryEndpoints G)) (hα : preBeth α = α.card)
    (hX : #(G.objects.obj : Type u) < preBeth α) :
    Presieve.IsSheaf (Sheaf.canonicalTopology (RankSpace α)) (rankCocycleClasses α G) := by
  obtain ⟨R,⟨e⟩⟩ := closedOrbitSpace_rankRepresentative G hG hα hX
  exact Presieve.isSheaf_iso _ (rankCocycleClassesYoneda G hG R (cgwhIsoOfHomeo e)).symm
    (Presieve.isSheaf_comp_uliftFunctor _ (Sheaf.isSheaf_yoneda_obj R))

/-- Every two cocycle morphisms with the same endpoints coincide for a
closed endpoint embedding. -/
theorem closedOrbitCocycle_homSubsingleton (G : TopologicalGroupoid.{u})
    (hG : IsClosedEmbedding (ordinaryEndpoints G)) {T : CGWH.{u}}
    (A B : QuotientCocycle G T) : Subsingleton (A ⟶ B) := by
  let F := closedOrbitRepresentation G hG T
  letI : F.IsEquivalence := closedOrbitRepresentation_isEquivalence G hG T
  exact ⟨fun r s ↦ F.map_injective (Subsingleton.elim _ _)⟩

/-- Object descent for arbitrary canonical covering sieves in the closed
endpoint case. The gluing and all its arrows over the sieve are unique up
to the unique compatible isomorphism. -/
theorem closedOrbitCocycle_effectiveDescent {α : Ordinal.{u}} (G : TopologicalGroupoid.{u})
    (hG : IsClosedEmbedding (ordinaryEndpoints G)) (hα : preBeth α = α.card)
    (hω : ℵ₀ < preBeth α) (hX : #(G.objects.obj : Type u) < preBeth α)
    {T : RankSpace α} (S : Sieve T) (hS : S ∈ Sheaf.canonicalTopology (RankSpace α) T)
    (A : ∀ ⦃Y : RankSpace α⦄ (g : Y ⟶ T), S g → QuotientCocycle G Y.space)
    (hA : ∀ ⦃Y Z W : RankSpace α⦄ (f : Y ⟶ T) (g : Z ⟶ T) (hf : S f) (hg : S g)
      (a : W ⟶ Y) (b : W ⟶ Z), a ≫ f = b ≫ g →
      Nonempty ((A f hf).pullback ((rankSpaceInclusion α).map a) ≅
        (A g hg).pullback ((rankSpaceInclusion α).map b))) :
    ∃ B : QuotientCocycle G T.space, #(B.coverSpace.obj : Type u) < preBeth α ∧
      (∀ ⦃Y : RankSpace α⦄ (g : Y ⟶ T) (hg : S g),
        Nonempty (B.pullback ((rankSpaceInclusion α).map g) ≅ A g hg)) ∧
      (∀ C : QuotientCocycle G T.space,
        (∀ ⦃Y : RankSpace α⦄ (g : Y ⟶ T) (hg : S g),
          Nonempty (C.pullback ((rankSpaceInclusion α).map g) ≅ A g hg)) →
        Nonempty (C ≅ B)) := by
  let P := rankCocycleClasses α G
  let x : (S : Presieve T).FamilyOfElements P := fun _ g hg ↦ Quotient.mk'' (A g hg)
  have hx : x.Compatible := by
    intro Y Z W a b f g hf hg hab
    exact Quotient.sound (hA f g hf hg a b hab)
  obtain ⟨t,ht,huniq⟩ := rankCocycleClasses_isSheaf G hG hα hX S hS x hx
  obtain ⟨D,hD⟩ := Quotient.exists_rep t
  let F := closedOrbitRepresentation G hG T.space
  obtain ⟨B,hB,hBF⟩ := closedOrbitRepresentation_boundedLift G hG hω hX T.carrier_lt (F.obj D).as
  letI : F.IsEquivalence := closedOrbitRepresentation_isEquivalence G hG T.space
  have hBD : Quotient.mk'' B = t := (Quotient.sound
    (s := cocycleIsoSetoid G T.space) ⟨F.preimageIso (eqToIso (Discrete.ext hBF))⟩).trans hD
  have htB : x.IsAmalgamation (Quotient.mk'' B) := hBD ▸ ht
  refine ⟨B,hB,fun Y g hg ↦ Quotient.exact (htB g hg), ?_⟩
  intro C hC
  have htC : x.IsAmalgamation (Quotient.mk'' C) := fun Y g hg ↦ Quotient.sound (hC g hg)
  exact Quotient.exact ((huniq _ htC).trans hBD.symm)

/-- A family of arrows on a canonical covering sieve descends uniquely.
All overlap equations are automatic because the cocycle groupoids are thin. -/
theorem closedOrbitCocycle_morphismDescent {α : Ordinal.{u}} (G : TopologicalGroupoid.{u})
    (hG : IsClosedEmbedding (ordinaryEndpoints G)) (hα : preBeth α = α.card)
    (hX : #(G.objects.obj : Type u) < preBeth α)
    {T : RankSpace α} (S : Sieve T) (hS : S ∈ Sheaf.canonicalTopology (RankSpace α) T)
    (A B : QuotientCocycle G T.space)
    (r : ∀ ⦃Y : RankSpace α⦄ (g : Y ⟶ T), S g →
      (A.pullback ((rankSpaceInclusion α).map g) ⟶ B.pullback ((rankSpaceInclusion α).map g))) :
    ∃! f : A ⟶ B, ∀ ⦃Y : RankSpace α⦄ (g : Y ⟶ T) (hg : S g),
      QuotientCocycle.pullbackHom f ((rankSpaceInclusion α).map g) = r g hg := by
  let P := rankCocycleClasses α G
  let x : (S : Presieve T).FamilyOfElements P :=
    fun _ g _ ↦ P.map g.op (Quotient.mk'' A)
  have hA : x.IsAmalgamation (Quotient.mk'' A) := fun _ _ _ ↦ rfl
  have hB : x.IsAmalgamation (Quotient.mk'' B) := by
    intro Y g hg
    exact Quotient.sound (s := cocycleIsoSetoid G Y.space) ⟨(asIso (r g hg)).symm⟩
  have hx := Presieve.is_compatible_of_exists_amalgamation x ⟨_,hA⟩
  obtain ⟨z,_,hz⟩ := rankCocycleClasses_isSheaf G hG hα hX S hS x hx
  have he : Quotient.mk'' A = Quotient.mk'' B := (hz _ hA).trans (hz _ hB).symm
  obtain ⟨i⟩ := Quotient.exact he
  refine ⟨i.hom, fun Y g hg ↦ (closedOrbitCocycle_homSubsingleton G hG _ _).elim _ _, ?_⟩
  exact fun f _ ↦ (closedOrbitCocycle_homSubsingleton G hG A B).elim _ _

/-- The continuous points of the original groupoid compare fully
faithfully with those of the orbit space. -/
theorem closedOrbitPoints_fullyFaithful (G : TopologicalGroupoid.{u})
    (hG : IsClosedEmbedding (ordinaryEndpoints G)) (T : CGWH.{u}) :
    Nonempty (mapPoints (closedOrbitFunctor G hG) T).FullyFaithful :=
  (arrowComparison_homeomorph_iff_mapPoints (closedOrbitFunctor G hG)).mp
    (closedOrbitFunctor_isStandardMorita G hG).2 T

private theorem castCover_eqToHom {X Y T : CGWH.{u}} (h : X = Y) (q : X ⟶ T) :
    cast (congrArg (fun Z : CGWH.{u} ↦ Z ⟶ T) h) q = eqToHom h.symm ≫ q := by
  subst Y
  simp

/-- A point of the representing object lifts locally to an actual point of
the original groupoid over a canonical rank cover. -/
theorem closedOrbitPoints_canonicalLift {α : Ordinal.{u}} (G : TopologicalGroupoid.{u})
    (hG : IsClosedEmbedding (ordinaryEndpoints G)) (hα : preBeth α = α.card)
    (hω : ℵ₀ < preBeth α) (hX : #(G.objects.obj : Type u) < preBeth α)
    (T : RankSpace α) (a : C(T.space.obj, (closedOrbitSpace G hG).obj)) :
    ∃ (W : RankSpace α) (q : W ⟶ T) (b : G.Points W.space),
      Sieve.generate (Presieve.singleton q) ∈ Sheaf.canonicalTopology (RankSpace α) T ∧
      ∀ w, (closedOrbitMap G hG).hom (b w) = a (((rankSpaceInclusion α).map q).hom w) := by
  obtain ⟨W,q,B,hq,⟨hB,hcover⟩,ha⟩ := closedOrbitRepresentation_canonicalLift G hG hα hω hX T a
  let b : G.Points W.space := B.point.comp (eqToHom hB.symm).hom.hom.hom
  refine ⟨W,q,b,hq,?_⟩
  have hc : (eqToHom hB.symm : W.space ⟶ B.coverSpace) ≫ B.cover =
      (rankSpaceInclusion α).map q :=
    (castCover_eqToHom hB B.cover).symm.trans hcover
  intro w
  let v := (eqToHom hB.symm : W.space ⟶ B.coverSpace).hom w
  have hv : B.cover.hom v = ((rankSpaceInclusion α).map q).hom w :=
    congrArg (fun f : W.space ⟶ T.space ↦ f.hom w) hc
  let M := B.map (closedOrbitFunctor G hG)
  have he : M.unitDescendedMap = a := ha
  exact (M.unitDescendedMap_cover v).symm.trans ((congrArg M.unitDescendedMap hv).trans
    (congrArg (fun f : C(T.space.obj, (closedOrbitSpace G hG).obj) ↦
      f (((rankSpaceInclusion α).map q).hom w)) he))

end Masullo.TopologicalGroupoid
