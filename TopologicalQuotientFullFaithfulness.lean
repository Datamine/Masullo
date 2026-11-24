import TopologicalMoritaRefinement
import TopologicalInertiaGroupoid
import Mathlib.CategoryTheory.Functor.FullyFaithful

open CategoryTheory Function Set Topology TopologicalSpace

namespace Masullo.TopologicalGroupoid

universe u

set_option backward.isDefEq.respectTransparency false in
/-- Postcomposition of a continuous family of objects and arrows. -/
def mapPoints {G H : TopologicalGroupoid.{u}} (f : G ⟶ H) (T : CGWH.{u}) :
    G.Points T ⥤ H.Points T where
  obj a := f.objectMap.comp a
  map {_a _b} r := ⟨f.arrowMap.comp r.val,
    fun x ↦ (f.mapSource _).trans (congrArg f.objectMap (r.property.1 x)),
    fun x ↦ (f.mapTarget _).trans (congrArg f.objectMap (r.property.2 x))⟩
  map_id _ := Subtype.ext (ContinuousMap.ext fun _ ↦ f.mapUnit _)
  map_comp _ _ := Subtype.ext (ContinuousMap.ext fun _ ↦ f.mapComp _ _ _)

/-- A single test space homeomorphic to the endpoint pullback detects
the arrow comparison. -/
theorem arrowComparison_homeomorph_of_test {G H : TopologicalGroupoid.{u}}
    (f : G ⟶ H) {T : CGWH.{u}} (e : T.obj ≃ₜ ArrowComparisonSpace f)
    (hf : Nonempty (mapPoints f T).FullyFaithful) :
    ∃ E : G.arrows.obj ≃ₜ ArrowComparisonSpace f, ∀ a, E a = arrowComparison f a := by
  let L : C(ArrowComparisonSpace f, G.objects.obj) := ⟨fun p ↦ p.val.1.1,
    continuous_fst.comp (continuous_Kelley_forget.comp (continuous_fst.comp
      (continuous_Kelley_forget.comp continuous_subtype_val)))⟩
  let R : C(ArrowComparisonSpace f, G.objects.obj) := ⟨fun p ↦ p.val.1.2,
    continuous_snd.comp (continuous_Kelley_forget.comp (continuous_fst.comp
      (continuous_Kelley_forget.comp continuous_subtype_val)))⟩
  let A : C(ArrowComparisonSpace f, H.arrows.obj) := ⟨fun p ↦ p.val.2,
    continuous_snd.comp (continuous_Kelley_forget.comp continuous_subtype_val)⟩
  let E : C(T.obj, ArrowComparisonSpace f) := ⟨e,e.continuous⟩
  let a : G.Points T := L.comp E
  let b : G.Points T := R.comp E
  let r : (mapPoints f T).obj a ⟶ (mapPoints f T).obj b :=
    ⟨A.comp E, fun p ↦ (congrArg Prod.fst (e p).property).symm,
      fun p ↦ (congrArg Prod.snd (e p).property).symm⟩
  let hw := (Functor.FullyFaithful.nonempty_iff_map_bijective (mapPoints f T)).mp hf
  obtain ⟨q, hq⟩ := (hw a b).surjective r
  have hright : RightInverse (q.val ∘ e.symm) (arrowComparison f) := by
    intro p
    have h : arrowComparison f (q.val (e.symm p)) = e (e.symm p) :=
      arrowComparison_eq f _ _ (q.property.1 _) (q.property.2 _)
        (congrArg (fun z : (mapPoints f T).obj a ⟶ (mapPoints f T).obj b ↦ z.val (e.symm p)) hq)
    exact h.trans (e.apply_symm_apply p)
  have hinj : Injective (arrowComparison f) := by
    intro x y hxy
    let A : G.Points T := ContinuousMap.const _ (G.source x)
    let B : G.Points T := ContinuousMap.const _ (G.target x)
    have h1 : G.source x = G.source y := congrArg (fun p : ArrowComparisonSpace f ↦ p.val.1.1) hxy
    have h2 : G.target x = G.target y := congrArg (fun p : ArrowComparisonSpace f ↦ p.val.1.2) hxy
    let r1 : A ⟶ B := ⟨ContinuousMap.const _ x, fun _ ↦ rfl, fun _ ↦ rfl⟩
    let r2 : A ⟶ B := ⟨ContinuousMap.const _ y, fun _ ↦ h1.symm, fun _ ↦ h2.symm⟩
    have hr : (mapPoints f T).map r1 = (mapPoints f T).map r2 :=
      Subtype.ext (ContinuousMap.ext fun _ ↦ congrArg (fun p : ArrowComparisonSpace f ↦ p.val.2) hxy)
    exact congrArg (fun z : A ⟶ B ↦ z.val (e.symm (arrowComparison f x))) ((hw A B).injective hr)
  exact ⟨{
    toFun := arrowComparison f
    invFun := q.val ∘ e.symm
    left_inv := fun x ↦ hinj (hright _)
    right_inv := hright
    continuous_toFun := (arrowComparison f).continuous
    continuous_invFun := q.val.continuous.comp e.symm.continuous }, fun _ ↦ rfl⟩

/-- Topological full faithfulness can be checked on all continuous test families. -/
theorem arrowComparison_homeomorph_iff_mapPoints {G H : TopologicalGroupoid.{u}} (f : G ⟶ H) :
    (∃ e : G.arrows.obj ≃ₜ ArrowComparisonSpace f, ∀ a, e a = arrowComparison f a) ↔
      ∀ T : CGWH.{u}, Nonempty (mapPoints f T).FullyFaithful := by
  classical
  constructor
  · rintro ⟨e, he⟩ T
    apply (Functor.FullyFaithful.nonempty_iff_map_bijective (mapPoints f T)).mpr
    intro a b
    constructor
    · intro r s hrs
      apply Subtype.ext
      ext x
      apply e.injective
      rw [he, he]
      apply arrowComparison_eq
      · exact (r.property.1 x).trans (s.property.1 x).symm
      · exact (r.property.2 x).trans (s.property.2 x).symm
      · exact congrArg (fun v : (mapPoints f T).obj a ⟶ (mapPoints f T).obj b ↦ v.val x) hrs
    · intro r
      let A : C(T.obj, G.objects.obj) := a
      let B : C(T.obj, G.objects.obj) := b
      have hr (x : T.obj) : (f.objectMap (A x), f.objectMap (B x)) =
          (H.source (r.val x), H.target (r.val x)) :=
        Prod.ext (r.property.1 x).symm (r.property.2 x).symm
      let p : C(T.obj, ArrowComparisonSpace f) :=
        ⟨fun x ↦ ⟨((A x, B x), r.val x), hr x⟩,
          (kelleyPair (kelleyPair A B) r.val).continuous.subtype_mk hr⟩
      let inv : C(ArrowComparisonSpace f, G.arrows.obj) := ⟨e.symm, e.symm.continuous⟩
      let q := inv.comp p
      have hq (x : T.obj) : arrowComparison f (q x) = p x :=
        (he _).symm.trans (e.apply_symm_apply _)
      refine ⟨⟨q, fun x ↦ congrArg (fun z : ArrowComparisonSpace f ↦ z.val.1.1) (hq x),
        fun x ↦ congrArg (fun z : ArrowComparisonSpace f ↦ z.val.1.2) (hq x)⟩, ?_⟩
      exact Subtype.ext (ContinuousMap.ext fun x ↦
        congrArg (fun z : ArrowComparisonSpace f ↦ z.val.2) (hq x))
  · intro h
    exact arrowComparison_homeomorph_of_test f (T := arrowComparisonObject f)
      (Homeomorph.refl _) (h _)

/-- Local representatives in the continuous groupoids are equivalent to the
quotient-map coverage condition of E.6.4.2. -/
theorem moritaAnchor_quotient_iff_localPoints {G H : TopologicalGroupoid.{u}} (f : G ⟶ H) :
    IsQuotientMap (moritaAnchor f) ↔
      ∀ (T : CGWH.{u}) (b : H.Points T),
        ∃ (V : CGWH.{u}) (q : V ⟶ T) (_ : IsQuotientMap q.hom) (a : G.Points V),
          Nonempty ((H.restrictPoints q.hom.hom.hom).obj b ⟶ (mapPoints f V).obj a) := by
  constructor
  · intro h T b
    let Z : CGWH.{u} := CGWH.of (X := MoritaAnchorSpace f)
      (CGWH.fibreSubspace_weaklyHausdorff _ _)
    let k : Z ⟶ H.objects := CGWH.map (moritaAnchor f)
    let j : T ⟶ H.objects := CGWH.map (show C(T.obj, H.objects.obj) from b)
    let P := CGWH.FibreSubspace k j
    letI : CompactlyGeneratedSpace P := closed_compactlyGenerated (CGWH.fibreSubspace_isClosed k j)
    let V : CGWH.{u} := CGWH.of (X := P) (CGWH.fibreSubspace_weaklyHausdorff _ _)
    let q : C(P, T.obj) := ⟨fun p ↦ p.val.2,
      continuous_snd.comp (continuous_Kelley_forget.comp continuous_subtype_val)⟩
    let d : C(P, Z.obj) := ⟨fun p ↦ p.val.1,
      continuous_fst.comp (continuous_Kelley_forget.comp continuous_subtype_val)⟩
    let a₀ : C(Z.obj, G.objects.obj) := ⟨fun p ↦ p.val.1,
      continuous_fst.comp (continuous_Kelley_forget.comp continuous_subtype_val)⟩
    let r₀ : C(Z.obj, H.arrows.obj) := ⟨fun p ↦ p.val.2,
      continuous_snd.comp (continuous_Kelley_forget.comp continuous_subtype_val)⟩
    exact ⟨V, CGWH.map (X := V) q, CGWH.quotient_baseChange k j h, a₀.comp d,
      ⟨⟨r₀.comp d, fun p ↦ p.property, fun p ↦ (d p).property.symm⟩⟩⟩
  · intro h
    obtain ⟨V, q, hq, a, ⟨r⟩⟩ := h H.objects (ContinuousMap.id _)
    let a₀ : C(V.obj, G.objects.obj) := a
    have ht (x : V.obj) : f.objectMap (a₀ x) = H.target (r.val x) := (r.property.2 x).symm
    let k : C(V.obj, MoritaAnchorSpace f) :=
      ⟨fun x ↦ ⟨(a₀ x, r.val x), ht x⟩, (kelleyPair a₀ r.val).continuous.subtype_mk ht⟩
    apply IsQuotientMap.of_comp k.continuous (moritaAnchor f).continuous
    have he : moritaAnchor f ∘ k = q.hom := funext fun x ↦ r.property.1 x
    rwa [he]

/-- A presentation of a quotient-stack object by a point on a CGWH cover
and a continuous cocycle on its kernel pair. -/
structure QuotientCocycle (G : TopologicalGroupoid.{u}) (T : CGWH.{u}) where
  coverSpace : CGWH.{u}
  cover : coverSpace ⟶ T
  isCover : IsQuotientMap cover.hom
  point : C(coverSpace.obj, G.objects.obj)
  transition : C(CGWH.FibreSubspace cover cover, G.arrows.obj)
  transitionSource : ∀ p, G.source (transition p) = point p.val.1
  transitionTarget : ∀ p, G.target (transition p) = point p.val.2
  transitionUnit : ∀ x, transition ⟨(x,x), rfl⟩ = G.unit (point x)
  transitionComp : ∀ x y z (hxy : cover.hom x = cover.hom y) (hyz : cover.hom y = cover.hom z),
    G.comp ⟨(transition ⟨(x,y), hxy⟩, transition ⟨(y,z), hyz⟩),
      (transitionTarget ⟨(x,y), hxy⟩).trans (transitionSource ⟨(y,z), hyz⟩).symm⟩ =
      transition ⟨(x,z), hxy.trans hyz⟩

namespace QuotientCocycle

variable {G H : TopologicalGroupoid.{u}} {T : CGWH.{u}}

private def step (A : QuotientCocycle G T) (x y : A.coverSpace.obj)
    (h : A.cover.hom x = A.cover.hom y) : G.UnderlyingArrow (A.point x) (A.point y) :=
  ⟨A.transition ⟨(x,y), h⟩, A.transitionSource _, A.transitionTarget _⟩

/-- Push a cover and its cocycle forward through a continuous groupoid functor. -/
def map (f : G ⟶ H) (A : QuotientCocycle G T) : QuotientCocycle H T where
  coverSpace := A.coverSpace
  cover := A.cover
  isCover := A.isCover
  point := f.objectMap.comp A.point
  transition := f.arrowMap.comp A.transition
  transitionSource x := (f.mapSource _).trans (congrArg f.objectMap (A.transitionSource x))
  transitionTarget x := (f.mapTarget _).trans (congrArg f.objectMap (A.transitionTarget x))
  transitionUnit x := (congrArg f.arrowMap (A.transitionUnit x)).trans (f.mapUnit _)
  transitionComp x y z hxy hyz :=
    (f.mapComp _ _ _).symm.trans (congrArg f.arrowMap (A.transitionComp x y z hxy hyz))

private def fibreOne (A B : QuotientCocycle G T) : C(CGWH.FibreSubspace A.cover B.cover, A.coverSpace.obj) :=
  ⟨fun p ↦ p.val.1, continuous_fst.comp (continuous_Kelley_forget.comp continuous_subtype_val)⟩

private def fibreTwo (A B : QuotientCocycle G T) : C(CGWH.FibreSubspace A.cover B.cover, B.coverSpace.obj) :=
  ⟨fun p ↦ p.val.2, continuous_snd.comp (continuous_Kelley_forget.comp continuous_subtype_val)⟩

/-- The common presenting cover of two cocycles as a CGWH space. -/
abbrev mixedTest (A B : QuotientCocycle G T) : CGWH.{u} :=
  CGWH.of (X := CGWH.FibreSubspace A.cover B.cover) (CGWH.fibreSubspace_weaklyHausdorff _ _)

private def firstPoint (A B : QuotientCocycle G T) : G.Points (mixedTest A B) :=
  A.point.comp (fibreOne A B)

private def secondPoint (A B : QuotientCocycle G T) : G.Points (mixedTest A B) :=
  B.point.comp (fibreTwo A B)

private def arrowAt {A B : QuotientCocycle G T}
    (a : firstPoint A B ⟶ secondPoint A B) (p : CGWH.FibreSubspace A.cover B.cover) :
    G.UnderlyingArrow (A.point p.val.1) (B.point p.val.2) :=
  ⟨a.val p, a.property.1 p, a.property.2 p⟩

/-- A morphism of the descended objects is a continuous arrow on the
common refinement commuting with both cocycles. -/
abbrev Hom (A B : QuotientCocycle G T) :=
  {a : firstPoint A B ⟶ secondPoint A B //
    ∀ (p q : CGWH.FibreSubspace A.cover B.cover)
      (hp : A.cover.hom p.val.1 = A.cover.hom q.val.1)
      (hq : B.cover.hom p.val.2 = B.cover.hom q.val.2),
      @CategoryStruct.comp G.Underlying _ _ _ _ (A.step p.val.1 q.val.1 hp) (arrowAt (A := A) (B := B) a q) =
        @CategoryStruct.comp G.Underlying _ _ _ _ (arrowAt (A := A) (B := B) a p) (B.step p.val.2 q.val.2 hq)}

private theorem step_unit (A : QuotientCocycle G T) (x : A.coverSpace.obj) :
    A.step x x rfl = @CategoryStruct.id G.Underlying _ (A.point x) :=
  Subtype.ext (A.transitionUnit x)

private theorem step_comp (A : QuotientCocycle G T)
    (x y z : A.coverSpace.obj)
    (hxy : A.cover.hom x = A.cover.hom y) (hyz : A.cover.hom y = A.cover.hom z) :
    @CategoryStruct.comp G.Underlying _ _ _ _ (A.step x y hxy) (A.step y z hyz) =
      A.step x z (hxy.trans hyz) :=
  Subtype.ext (A.transitionComp x y z hxy hyz)

/-- The transition cocycle supplies the identity arrow on its presentation. -/
def identityHom (A : QuotientCocycle G T) : A.Hom A := by
  refine ⟨⟨A.transition, A.transitionSource, A.transitionTarget⟩, ?_⟩
  intro p q hp hq
  exact (step_comp A p.val.1 q.val.1 q.val.2 hp q.property).trans
    (step_comp A p.val.1 p.val.2 q.val.2 p.property hq).symm

/-- The map from the common presenting cover to the base. -/
def baseOfMixed (A C : QuotientCocycle G T) : mixedTest A C ⟶ T :=
  CGWH.map ((A.cover.hom.hom.hom).comp (fibreOne A C))

private abbrev Triple (A B C : QuotientCocycle G T) :=
  CGWH.FibreSubspace B.cover (baseOfMixed A C)

local instance (A B C : QuotientCocycle G T) : CompactlyGeneratedSpace (Triple A B C) :=
  closed_compactlyGenerated (CGWH.fibreSubspace_isClosed B.cover (baseOfMixed A C))

private def tripleEndpoints (A B C : QuotientCocycle G T) :
    C(Triple A B C, CGWH.FibreSubspace A.cover C.cover) :=
  ⟨fun p ↦ p.val.2, continuous_snd.comp (continuous_Kelley_forget.comp continuous_subtype_val)⟩

private def tripleMiddle (A B C : QuotientCocycle G T) : C(Triple A B C, B.coverSpace.obj) :=
  ⟨fun p ↦ p.val.1, continuous_fst.comp (continuous_Kelley_forget.comp continuous_subtype_val)⟩

private def tripleLeft (A B C : QuotientCocycle G T) :
    C(Triple A B C, CGWH.FibreSubspace A.cover B.cover) := by
  let a := (fibreOne A C).comp (tripleEndpoints A B C)
  let b := tripleMiddle A B C
  have h (p : Triple A B C) : A.cover.hom (a p) = B.cover.hom (b p) := p.property.symm
  exact ⟨fun p ↦ ⟨(a p,b p), h p⟩, (kelleyPair a b).continuous.subtype_mk h⟩

private def tripleRight (A B C : QuotientCocycle G T) :
    C(Triple A B C, CGWH.FibreSubspace B.cover C.cover) := by
  let b := tripleMiddle A B C
  let c := (fibreTwo A C).comp (tripleEndpoints A B C)
  have h (p : Triple A B C) : B.cover.hom (b p) = C.cover.hom (c p) :=
    p.property.trans p.val.2.property
  exact ⟨fun p ↦ ⟨(b p,c p), h p⟩, (kelleyPair b c).continuous.subtype_mk h⟩

private def tripleComposite {A B C : QuotientCocycle G T} (r : A.Hom B) (s : B.Hom C) :
    C(Triple A B C, G.arrows.obj) := by
  let R := r.val.val.comp (tripleLeft A B C)
  let S := s.val.val.comp (tripleRight A B C)
  have h (p : Triple A B C) : G.target (R p) = G.source (S p) := by
    have hr : G.target (R p) = B.point (tripleMiddle A B C p) := r.val.property.2 (tripleLeft A B C p)
    have hs : G.source (S p) = B.point (tripleMiddle A B C p) := s.val.property.1 (tripleRight A B C p)
    exact hr.trans hs.symm
  exact G.comp.comp ⟨fun p ↦ ⟨(R p,S p), h p⟩, (kelleyPair R S).continuous.subtype_mk h⟩

private theorem tripleComposite_eq_on_fibres {A B C : QuotientCocycle G T}
    (r : A.Hom B) (s : B.Hom C) {p q : Triple A B C}
    (h : tripleEndpoints A B C p = tripleEndpoints A B C q) :
    tripleComposite r s p = tripleComposite r s q := by
  rcases p with ⟨⟨y, xz⟩, hy⟩
  rcases q with ⟨⟨y', xz'⟩, hy'⟩
  change xz = xz' at h
  subst xz'
  let p : Triple A B C := ⟨(y,xz),hy⟩
  let q : Triple A B C := ⟨(y',xz),hy'⟩
  have hyy : B.cover.hom y = B.cover.hom y' := hy.trans hy'.symm
  let r₀ := arrowAt (A := A) (B := B) r.val (tripleLeft A B C p)
  let r₁ := arrowAt (A := A) (B := B) r.val (tripleLeft A B C q)
  let s₀ := arrowAt (A := B) (B := C) s.val (tripleRight A B C p)
  let s₁ := arrowAt (A := B) (B := C) s.val (tripleRight A B C q)
  let j := B.step y y' hyy
  have h₁ : r₁ = @CategoryStruct.comp G.Underlying _ _ _ _ r₀ j := by
    have he := r.property (tripleLeft A B C p) (tripleLeft A B C q) rfl hyy
    exact (@Category.id_comp G.Underlying _ _ _ r₁).symm.trans
      ((congrArg (fun v ↦ @CategoryStruct.comp G.Underlying _ _ _ _ v r₁)
        (step_unit A xz.val.1).symm).trans he)
  have h₂ : @CategoryStruct.comp G.Underlying _ _ _ _ j s₁ = s₀ := by
    have he := s.property (tripleRight A B C p) (tripleRight A B C q) hyy rfl
    exact he.trans ((congrArg (fun v ↦ @CategoryStruct.comp G.Underlying _ _ _ _ s₀ v)
      (step_unit C xz.val.2)).trans (@Category.comp_id G.Underlying _ _ _ s₀))
  have he : @CategoryStruct.comp G.Underlying _ _ _ _ r₀ s₀ =
      @CategoryStruct.comp G.Underlying _ _ _ _ r₁ s₁ :=
    (congrArg (fun v ↦ @CategoryStruct.comp G.Underlying _ _ _ _ r₀ v) h₂.symm).trans
      ((@Category.assoc G.Underlying _ _ _ _ _ r₀ j s₁).symm.trans
        (congrArg (fun v ↦ @CategoryStruct.comp G.Underlying _ _ _ _ v s₁) h₁.symm))
  exact congrArg Subtype.val he

/-- Composition of compatible arrows descends continuously through the
middle cover. Its value can be calculated using any lift to that cover. -/
theorem exists_continuousComposite {A B C : QuotientCocycle G T}
    (r : A.Hom B) (s : B.Hom C) :
    ∃ d : C(CGWH.FibreSubspace A.cover C.cover, G.arrows.obj),
      ∀ p : Triple A B C, d (tripleEndpoints A B C p) = tripleComposite r s p := by
  classical
  let e := tripleEndpoints A B C
  have he : IsQuotientMap e := CGWH.quotient_baseChange B.cover (baseOfMixed A C) B.isCover
  let σ (x : CGWH.FibreSubspace A.cover C.cover) : Triple A B C := (he.surjective x).choose
  have hσ (x : CGWH.FibreSubspace A.cover C.cover) : e (σ x) = x := (he.surjective x).choose_spec
  let d (x : CGWH.FibreSubspace A.cover C.cover) := tripleComposite r s (σ x)
  have hD (p : Triple A B C) : d (e p) = tripleComposite r s p :=
    tripleComposite_eq_on_fibres r s (hσ (e p))
  have hc : Continuous d := he.continuous_iff.mpr
    ((tripleComposite r s).continuous.congr (fun x ↦ (hD x).symm))
  exact ⟨⟨d,hc⟩, hD⟩

private theorem tripleArrows_comp {A B C : QuotientCocycle G T}
    (r : A.Hom B) (s : B.Hom C) (p : Triple A B C) :
    tripleComposite r s p =
      (@CategoryStruct.comp G.Underlying _ _ _ _
        (arrowAt (A := A) (B := B) r.val (tripleLeft A B C p))
        (arrowAt (A := B) (B := C) s.val (tripleRight A B C p))).val := rfl

/-- Compose descent arrows by composing after lifting to the middle cover. -/
noncomputable def composeHom {A B C : QuotientCocycle G T} (r : A.Hom B) (s : B.Hom C) :
    A.Hom C := by
  let e := tripleEndpoints A B C
  let hd := exists_continuousComposite r s
  let d := hd.choose
  have hd' := hd.choose_spec
  have hsur : Surjective e :=
    (CGWH.quotient_baseChange B.cover (baseOfMixed A C) B.isCover).surjective
  have hs (p : CGWH.FibreSubspace A.cover C.cover) : G.source (d p) = A.point p.val.1 := by
    obtain ⟨x, rfl⟩ := hsur p
    have h := hd' x
    change G.source (d (e x)) = _
    rw [h]
    exact (G.source_comp _).trans (r.val.property.1 (tripleLeft A B C x))
  have ht (p : CGWH.FibreSubspace A.cover C.cover) : G.target (d p) = C.point p.val.2 := by
    obtain ⟨x, rfl⟩ := hsur p
    have h := hd' x
    change G.target (d (e x)) = _
    rw [h]
    exact (G.target_comp _).trans (s.val.property.2 (tripleRight A B C x))
  let D : firstPoint A C ⟶ secondPoint A C := ⟨d, hs, ht⟩
  have hD (x : Triple A B C) : arrowAt (A := A) (B := C) D (e x) =
      @CategoryStruct.comp G.Underlying _ _ _ _
        (arrowAt (A := A) (B := B) r.val (tripleLeft A B C x))
        (arrowAt (A := B) (B := C) s.val (tripleRight A B C x)) :=
    Subtype.ext ((hd' x).trans (tripleArrows_comp r s x))
  refine ⟨D, ?_⟩
  intro p q hp hq
  obtain ⟨x, rfl⟩ := hsur p
  obtain ⟨y, rfl⟩ := hsur q
  have hm : B.cover.hom (tripleMiddle A B C x) = B.cover.hom (tripleMiddle A B C y) :=
    x.property.trans (hp.trans y.property.symm)
  let a := A.step (e x).val.1 (e y).val.1 hp
  let b := B.step (tripleMiddle A B C x) (tripleMiddle A B C y) hm
  let c := C.step (e x).val.2 (e y).val.2 hq
  let r₀ := arrowAt (A := A) (B := B) r.val (tripleLeft A B C x)
  let r₁ := arrowAt (A := A) (B := B) r.val (tripleLeft A B C y)
  let s₀ := arrowAt (A := B) (B := C) s.val (tripleRight A B C x)
  let s₁ := arrowAt (A := B) (B := C) s.val (tripleRight A B C y)
  have hr : @CategoryStruct.comp G.Underlying _ _ _ _ a r₁ =
      @CategoryStruct.comp G.Underlying _ _ _ _ r₀ b :=
    r.property (tripleLeft A B C x) (tripleLeft A B C y) hp hm
  have hs' : @CategoryStruct.comp G.Underlying _ _ _ _ b s₁ =
      @CategoryStruct.comp G.Underlying _ _ _ _ s₀ c :=
    s.property (tripleRight A B C x) (tripleRight A B C y) hm hq
  exact (congrArg (fun v ↦ @CategoryStruct.comp G.Underlying _ _ _ _ a v) (hD y)).trans
    ((@Category.assoc G.Underlying _ _ _ _ _ a r₁ s₁).symm.trans
      ((congrArg (fun v ↦ @CategoryStruct.comp G.Underlying _ _ _ _ v s₁) hr).trans
        ((@Category.assoc G.Underlying _ _ _ _ _ r₀ b s₁).trans
          ((congrArg (fun v ↦ @CategoryStruct.comp G.Underlying _ _ _ _ r₀ v) hs').trans
            ((@Category.assoc G.Underlying _ _ _ _ _ r₀ s₀ c).symm.trans
              (congrArg (fun v ↦ @CategoryStruct.comp G.Underlying _ _ _ _ v c) (hD x).symm))))))

private theorem composeHom_eval {A B C : QuotientCocycle G T} (r : A.Hom B) (s : B.Hom C)
    (p : Triple A B C) :
    arrowAt (A := A) (B := C) (composeHom r s).val (tripleEndpoints A B C p) =
      @CategoryStruct.comp G.Underlying _ _ _ _
        (arrowAt (A := A) (B := B) r.val (tripleLeft A B C p))
        (arrowAt (A := B) (B := C) s.val (tripleRight A B C p)) := by
  apply Subtype.ext
  exact ((exists_continuousComposite r s).choose_spec p).trans (tripleArrows_comp r s p)

private theorem identity_composeHom {A B : QuotientCocycle G T} (r : A.Hom B) :
    composeHom (identityHom A) r = r := by
  apply Subtype.ext
  apply Subtype.ext
  apply ContinuousMap.ext
  intro p
  let q : Triple A A B := ⟨(p.val.1,p), rfl⟩
  have he := composeHom_eval (identityHom A) r q
  let a := arrowAt (A := A) (B := B) r.val p
  have h : arrowAt (A := A) (B := B) (composeHom (identityHom A) r).val p = a :=
    he.trans ((congrArg (fun v ↦ @CategoryStruct.comp G.Underlying _ _ _ _ v a)
      (step_unit A p.val.1)).trans (@Category.id_comp G.Underlying _ _ _ a))
  exact congrArg Subtype.val h

private theorem composeHom_identity {A B : QuotientCocycle G T} (r : A.Hom B) :
    composeHom r (identityHom B) = r := by
  apply Subtype.ext
  apply Subtype.ext
  apply ContinuousMap.ext
  intro p
  let q : Triple A B B := ⟨(p.val.2,p), p.property.symm⟩
  have he := composeHom_eval r (identityHom B) q
  let a := arrowAt (A := A) (B := B) r.val p
  have h : arrowAt (A := A) (B := B) (composeHom r (identityHom B)).val p = a :=
    he.trans ((congrArg (fun v ↦ @CategoryStruct.comp G.Underlying _ _ _ _ a v)
      (step_unit B p.val.2)).trans (@Category.comp_id G.Underlying _ _ _ a))
  exact congrArg Subtype.val h

private theorem composeHom_assoc {A B C D : QuotientCocycle G T}
    (r : A.Hom B) (s : B.Hom C) (t : C.Hom D) :
    composeHom (composeHom r s) t = composeHom r (composeHom s t) := by
  apply Subtype.ext
  apply Subtype.ext
  apply ContinuousMap.ext
  intro p
  obtain ⟨b,hb⟩ := B.isCover.surjective (A.cover.hom p.val.1)
  obtain ⟨c,hc⟩ := C.isCover.surjective (A.cover.hom p.val.1)
  let pac : CGWH.FibreSubspace A.cover C.cover := ⟨(p.val.1,c),hc.symm⟩
  let pbd : CGWH.FibreSubspace B.cover D.cover := ⟨(b,p.val.2),hb.trans p.property⟩
  let x₀ : Triple A C D := ⟨(c,p),hc⟩
  let x₁ : Triple A B C := ⟨(b,pac),hb⟩
  let y₀ : Triple A B D := ⟨(b,p),hb⟩
  let y₁ : Triple B C D := ⟨(c,pbd),hc.trans hb.symm⟩
  let r₀ := arrowAt (A := A) (B := B) r.val (tripleLeft A B C x₁)
  let s₀ := arrowAt (A := B) (B := C) s.val (tripleRight A B C x₁)
  let t₀ := arrowAt (A := C) (B := D) t.val (tripleRight A C D x₀)
  have he := (composeHom_eval (composeHom r s) t x₀).trans
    (congrArg (fun v ↦ @CategoryStruct.comp G.Underlying _ _ _ _ v t₀) (composeHom_eval r s x₁))
  have hf := (composeHom_eval r (composeHom s t) y₀).trans
    (congrArg (fun v ↦ @CategoryStruct.comp G.Underlying _ _ _ _ r₀ v) (composeHom_eval s t y₁))
  exact congrArg Subtype.val (he.trans ((@Category.assoc G.Underlying _ _ _ _ _ r₀ s₀ t₀).trans hf.symm))

/-- The quotient cocycles form a category with composition computed on common covers. -/
noncomputable instance : Category (QuotientCocycle G T) where
  Hom := Hom
  id := identityHom
  comp := composeHom
  id_comp := identity_composeHom
  comp_id := composeHom_identity
  assoc := composeHom_assoc

private def swappedFibre (A B : QuotientCocycle G T) :
    C(CGWH.FibreSubspace B.cover A.cover, CGWH.FibreSubspace A.cover B.cover) :=
  ⟨fun p ↦ ⟨(p.val.2,p.val.1),p.property.symm⟩,
    (kelleyPair (fibreTwo B A) (fibreOne B A)).continuous.subtype_mk (fun p ↦ p.property.symm)⟩

/-- The inverse family on the reversed common refinement is again compatible. -/
def inverseHom {A B : QuotientCocycle G T} (r : A.Hom B) : B.Hom A := by
  let R : firstPoint B A ⟶ secondPoint B A := ⟨(G.inverse.comp r.val.val).comp (swappedFibre A B),
    fun p ↦ (G.source_inv _).trans (r.val.property.2 (swappedFibre A B p)),
    fun p ↦ (G.target_inv _).trans (r.val.property.1 (swappedFibre A B p))⟩
  refine ⟨R, ?_⟩
  intro p q hp hq
  let r₀ := arrowAt (A := A) (B := B) r.val (swappedFibre A B p)
  let r₁ := arrowAt (A := A) (B := B) r.val (swappedFibre A B q)
  letI iso_r₀ : @IsIso G.Underlying _ _ _ r₀ := @IsIso.of_groupoid G.Underlying _ _ _ r₀
  letI iso_r₁ : @IsIso G.Underlying _ _ _ r₁ := @IsIso.of_groupoid G.Underlying _ _ _ r₁
  let a := A.step p.val.2 q.val.2 hq
  let b := B.step p.val.1 q.val.1 hp
  have hp' : arrowAt (A := B) (B := A) R p = @CategoryTheory.inv G.Underlying _ _ _ r₀ iso_r₀ :=
    @Groupoid.inv_eq_inv G.Underlying _ _ _ r₀
  have hq' : arrowAt (A := B) (B := A) R q = @CategoryTheory.inv G.Underlying _ _ _ r₁ iso_r₁ :=
    @Groupoid.inv_eq_inv G.Underlying _ _ _ r₁
  have hn : @CategoryStruct.comp G.Underlying _ _ _ _ a r₁ =
      @CategoryStruct.comp G.Underlying _ _ _ _ r₀ b :=
    r.property (swappedFibre A B p) (swappedFibre A B q) hq hp
  have h : @CategoryStruct.comp G.Underlying _ _ _ _ b (@CategoryTheory.inv G.Underlying _ _ _ r₁ iso_r₁) =
      @CategoryStruct.comp G.Underlying _ _ _ _ (@CategoryTheory.inv G.Underlying _ _ _ r₀ iso_r₀) a :=
    (@IsIso.comp_inv_eq G.Underlying _ _ _ _ r₁ iso_r₁ _ _).mpr (((@IsIso.eq_inv_comp G.Underlying _ _ _ _ r₀ iso_r₀ _ _).mpr hn.symm).trans
      (@Category.assoc G.Underlying _ _ _ _ _ (@CategoryTheory.inv G.Underlying _ _ _ r₀ iso_r₀) a r₁).symm)
  exact (congrArg (fun v ↦ @CategoryStruct.comp G.Underlying _ _ _ _ b v) hq').trans
    (h.trans (congrArg (fun v ↦ @CategoryStruct.comp G.Underlying _ _ _ _ v a) hp'.symm))

private theorem inverse_composeHom {A B : QuotientCocycle G T} (r : A.Hom B) :
    composeHom (inverseHom r) r = identityHom B := by
  apply Subtype.ext
  apply Subtype.ext
  apply ContinuousMap.ext
  intro p
  obtain ⟨x,hx⟩ := A.isCover.surjective (B.cover.hom p.val.1)
  let q : Triple B A B := ⟨(x,p),hx⟩
  let b := B.step p.val.1 p.val.2 p.property
  let u := arrowAt (A := A) (B := B) r.val (swappedFibre A B (tripleLeft B A B q))
  let v := arrowAt (A := A) (B := B) r.val (tripleRight B A B q)
  have hn := r.property (swappedFibre A B (tripleLeft B A B q)) (tripleRight B A B q) rfl p.property
  have hv : v = @CategoryStruct.comp G.Underlying _ _ _ _ u b :=
    (@Category.id_comp G.Underlying _ _ _ v).symm.trans
      ((congrArg (fun z ↦ @CategoryStruct.comp G.Underlying _ _ _ _ z v) (step_unit A x).symm).trans hn)
  letI iso_u : @IsIso G.Underlying _ _ _ u := @IsIso.of_groupoid G.Underlying _ _ _ u
  have hI : arrowAt (A := B) (B := A) (inverseHom r).val (tripleLeft B A B q) =
      @CategoryTheory.inv G.Underlying _ _ _ u iso_u := @Groupoid.inv_eq_inv G.Underlying _ _ _ u
  have he := (composeHom_eval (inverseHom r) r q).trans
    ((congrArg (fun z ↦ @CategoryStruct.comp G.Underlying _ _ _ _ z v) hI).trans
      ((@IsIso.inv_comp_eq G.Underlying _ _ _ _ u iso_u _ _).mpr hv))
  exact congrArg Subtype.val he

private theorem composeHom_inverse {A B : QuotientCocycle G T} (r : A.Hom B) :
    composeHom r (inverseHom r) = identityHom A := by
  apply Subtype.ext
  apply Subtype.ext
  apply ContinuousMap.ext
  intro p
  obtain ⟨y,hy⟩ := B.isCover.surjective (A.cover.hom p.val.1)
  let q : Triple A B A := ⟨(y,p),hy⟩
  let a := A.step p.val.1 p.val.2 p.property
  let u := arrowAt (A := A) (B := B) r.val (tripleLeft A B A q)
  let v := arrowAt (A := A) (B := B) r.val (swappedFibre A B (tripleRight A B A q))
  have hn := r.property (tripleLeft A B A q) (swappedFibre A B (tripleRight A B A q)) p.property rfl
  have hu : u = @CategoryStruct.comp G.Underlying _ _ _ _ a v :=
    (@Category.comp_id G.Underlying _ _ _ u).symm.trans
      ((congrArg (fun z ↦ @CategoryStruct.comp G.Underlying _ _ _ _ u z) (step_unit B y).symm).trans
        hn.symm)
  letI iso_v : @IsIso G.Underlying _ _ _ v := @IsIso.of_groupoid G.Underlying _ _ _ v
  have hI : arrowAt (A := B) (B := A) (inverseHom r).val (tripleRight A B A q) =
      @CategoryTheory.inv G.Underlying _ _ _ v iso_v := @Groupoid.inv_eq_inv G.Underlying _ _ _ v
  have he := (composeHom_eval r (inverseHom r) q).trans
    ((congrArg (fun z ↦ @CategoryStruct.comp G.Underlying _ _ _ _ u z) hI).trans
      ((@IsIso.comp_inv_eq G.Underlying _ _ _ _ v iso_v _ _).mpr hu))
  exact congrArg Subtype.val he

/-- Every compatible arrow of quotient cocycles is invertible. -/
noncomputable instance : Groupoid (QuotientCocycle G T) where
  toCategory := inferInstance
  inv := inverseHom
  inv_comp := inverse_composeHom
  comp_inv := composeHom_inverse

/-- On a common refinement, evaluate a composition by choosing any lift
in the middle cover of the same base point. -/
theorem comp_apply {A B C : QuotientCocycle G T} (r : A ⟶ B) (s : B ⟶ C)
    (x : A.coverSpace.obj) (y : B.coverSpace.obj) (z : C.coverSpace.obj)
    (hxy : A.cover.hom x = B.cover.hom y) (hyz : B.cover.hom y = C.cover.hom z) :
    (r ≫ s).val.val ⟨(x,z),hxy.trans hyz⟩ =
      G.comp ⟨(r.val.val ⟨(x,y),hxy⟩, s.val.val ⟨(y,z),hyz⟩),
        (r.val.property.2 ⟨(x,y),hxy⟩).trans (s.val.property.1 ⟨(y,z),hyz⟩).symm⟩ :=
  congrArg Subtype.val (composeHom_eval r s
    (⟨(y,⟨(x,z),hxy.trans hyz⟩),hxy.symm⟩ : Triple A B C))

/-- A morphism evaluated at two points of its presenting covers. -/
def homValue {A B : QuotientCocycle G T} (r : A ⟶ B)
    (x : A.coverSpace.obj) (y : B.coverSpace.obj) (h : A.cover.hom x = B.cover.hom y) :
    G.UnderlyingArrow (A.point x) (B.point y) :=
  arrowAt r.val ⟨(x,y),h⟩

/-- A span of cocycle arrows evaluates to the corresponding span of
groupoid arrows on any lift to the middle cover. -/
theorem homValue_inv_comp {A B C : QuotientCocycle G T} (r : C ⟶ A) (s : C ⟶ B)
    (x : A.coverSpace.obj) (y : B.coverSpace.obj) (z : C.coverSpace.obj)
    (hx : C.cover.hom z = A.cover.hom x) (hy : C.cover.hom z = B.cover.hom y) :
    homValue (Groupoid.inv r ≫ s) x y (hx.symm.trans hy) =
      @CategoryStruct.comp G.Underlying _ _ _ _
        (@Groupoid.inv G.Underlying _ _ _ (homValue r z x hx)) (homValue s z y hy) := by
  apply Subtype.ext
  exact comp_apply (Groupoid.inv r) s x z y hx.symm hy

/-- A morphism is determined by its values on the common presenting cover. -/
theorem hom_ext {A B : QuotientCocycle G T} {r s : A ⟶ B}
    (h : ∀ p : CGWH.FibreSubspace A.cover B.cover, r.val.val p = s.val.val p) : r = s :=
  Subtype.ext (Subtype.ext (ContinuousMap.ext h))

/-- A composition on a common presenting point with an identity first leg
has the value of its second leg. -/
theorem comp_apply_left_unit {A B C : QuotientCocycle G T} (r : A ⟶ B) (s : B ⟶ C)
    (x : A.coverSpace.obj) (y : B.coverSpace.obj) (z : C.coverSpace.obj)
    (hxy : A.cover.hom x = B.cover.hom y) (hyz : B.cover.hom y = C.cover.hom z)
    (hr : r.val.val ⟨(x,y),hxy⟩ = G.unit (B.point y)) :
    (r ≫ s).val.val ⟨(x,z),hxy.trans hyz⟩ = s.val.val ⟨(y,z),hyz⟩ := by
  let v := s.val.val ⟨(y,z),hyz⟩
  have he : r.val.val ⟨(x,y),hxy⟩ = G.unit (G.source v) :=
    hr.trans (congrArg G.unit (s.val.property.1 ⟨(y,z),hyz⟩).symm)
  refine (comp_apply r s x y z hxy hyz).trans (Eq.trans ?_ (G.unit_comp v))
  apply congrArg G.comp
  exact Subtype.ext (Prod.ext he rfl)

/-- A composition on a common presenting point with an identity second leg
has the value of its first leg. -/
theorem comp_apply_right_unit {A B C : QuotientCocycle G T} (r : A ⟶ B) (s : B ⟶ C)
    (x : A.coverSpace.obj) (y : B.coverSpace.obj) (z : C.coverSpace.obj)
    (hxy : A.cover.hom x = B.cover.hom y) (hyz : B.cover.hom y = C.cover.hom z)
    (hs : s.val.val ⟨(y,z),hyz⟩ = G.unit (B.point y)) :
    (r ≫ s).val.val ⟨(x,z),hxy.trans hyz⟩ = r.val.val ⟨(x,y),hxy⟩ := by
  let v := r.val.val ⟨(x,y),hxy⟩
  have he : s.val.val ⟨(y,z),hyz⟩ = G.unit (G.target v) :=
    hs.trans (congrArg G.unit (r.val.property.2 ⟨(x,y),hxy⟩).symm)
  refine (comp_apply r s x y z hxy hyz).trans (Eq.trans ?_ (G.comp_unit v))
  apply congrArg G.comp
  exact Subtype.ext (Prod.ext rfl he)

/-- The map on compatible arrows after pushing forward a cocycle. -/
def mapHom (f : G ⟶ H) {A B : QuotientCocycle G T} :
    A.Hom B → (A.map f).Hom (B.map f) := by
  intro a
  refine ⟨(mapPoints f (mixedTest A B)).map a.val, ?_⟩
  intro p q hp hq
  let u := underlyingFunctor f
  let l := A.step p.val.1 q.val.1 hp
  let r := B.step p.val.2 q.val.2 hq
  let x := arrowAt (A := A) (B := B) a.val p
  let y := arrowAt (A := A) (B := B) a.val q
  calc
    _ = u.map (@CategoryStruct.comp G.Underlying _ _ _ _ l y) := (u.map_comp l y).symm
    _ = u.map (@CategoryStruct.comp G.Underlying _ _ _ _ x r) :=
      congrArg u.map (a.property p q hp hq)
    _ = _ := u.map_comp x r

private theorem underlying_map_injective_of_arrowComparison (f : G ⟶ H)
    (hf : Injective (arrowComparison f)) {x y : G.Underlying} :
    Injective ((underlyingFunctor f).map : (x ⟶ y) → _) := by
  intro a b h
  apply Subtype.ext
  apply hf
  apply arrowComparison_eq
  · exact a.property.1.trans b.property.1.symm
  · exact a.property.2.trans b.property.2.symm
  · exact congrArg Subtype.val h

/-- The continuous functor induces a functor between the categories of cocycle presentations. -/
noncomputable def mapCocycles (f : G ⟶ H) : QuotientCocycle G T ⥤ QuotientCocycle H T where
  obj := map f
  map := mapHom f
  map_id A := by
    change mapHom f (identityHom A) = identityHom (A.map f)
    apply Subtype.ext
    apply Subtype.ext
    exact ContinuousMap.ext fun _ ↦ rfl
  map_comp {A B C} r s := by
    change mapHom f (composeHom r s) = composeHom (mapHom f r) (mapHom f s)
    apply Subtype.ext
    apply Subtype.ext
    apply ContinuousMap.ext
    intro p
    obtain ⟨b,hb⟩ := B.isCover.surjective (A.cover.hom p.val.1)
    let x : Triple A B C := ⟨(b,p),hb⟩
    let y : Triple (A.map f) (B.map f) (C.map f) := ⟨(b,p),hb⟩
    have hl := congrArg (fun a ↦ f.arrowMap a.val) (composeHom_eval r s x)
    have hr := congrArg Subtype.val (composeHom_eval (mapHom f r) (mapHom f s) y)
    exact hl.trans ((f.mapComp _ _ _).trans hr.symm)

/-- The arrow pullback induces a bijection on the morphisms of any pair of
quotient-stack objects presented by continuous cocycles. -/
theorem mapHom_bijective_of_arrowComparison (f : G ⟶ H)
    (hf : ∃ e : G.arrows.obj ≃ₜ ArrowComparisonSpace f, ∀ a, e a = arrowComparison f a)
    (A B : QuotientCocycle G T) : Bijective (mapHom f (A := A) (B := B)) := by
  have h := (arrowComparison_homeomorph_iff_mapPoints f).mp hf (mixedTest A B)
  let hf' := (Functor.FullyFaithful.nonempty_iff_map_bijective (mapPoints f (mixedTest A B))).mp
    h (firstPoint A B) (secondPoint A B)
  constructor
  · intro a b hab
    apply Subtype.ext
    apply hf'.1
    apply Subtype.ext
    apply ContinuousMap.ext
    intro p
    exact congrArg (fun t : (A.map f).Hom (B.map f) ↦ t.val.val p) hab
  · intro a
    obtain ⟨r, hr⟩ := hf'.2 a.val
    have hi : Injective (arrowComparison f) := by
      obtain ⟨e, he⟩ := hf
      intro a b hab
      apply e.injective
      rwa [he, he]
    have hc : r ∈ {r : firstPoint A B ⟶ secondPoint A B |
        ∀ (p q : CGWH.FibreSubspace A.cover B.cover)
          (hp : A.cover.hom p.val.1 = A.cover.hom q.val.1)
          (hq : B.cover.hom p.val.2 = B.cover.hom q.val.2),
          @CategoryStruct.comp G.Underlying _ _ _ _ (A.step p.val.1 q.val.1 hp) (arrowAt (A := A) (B := B) r q) =
            @CategoryStruct.comp G.Underlying _ _ _ _ (arrowAt (A := A) (B := B) r p) (B.step p.val.2 q.val.2 hq)} := by
      intro p q hp hq
      apply underlying_map_injective_of_arrowComparison f hi
      let u := underlyingFunctor f
      let l := A.step p.val.1 q.val.1 hp
      let b := B.step p.val.2 q.val.2 hq
      let x := arrowAt (A := A) (B := B) r p
      let y := arrowAt (A := A) (B := B) r q
      have h₁ : u.map x = arrowAt (A := A.map f) (B := B.map f) a.val p :=
        congrArg (fun t ↦ arrowAt (A := A.map f) (B := B.map f) t p) hr
      have h₂ : u.map y = arrowAt (A := A.map f) (B := B.map f) a.val q :=
        congrArg (fun t ↦ arrowAt (A := A.map f) (B := B.map f) t q) hr
      have hl := congrArg (fun v ↦ @CategoryStruct.comp H.Underlying _ _ _ _ (u.map l) v) h₂
      have hb := congrArg (fun v ↦ @CategoryStruct.comp H.Underlying _ _ _ _ v (u.map b)) h₁.symm
      exact (u.map_comp l y).trans (hl.trans ((a.property p q hp hq).trans
        (hb.trans (u.map_comp x b).symm)))
    refine ⟨⟨r, hc⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    apply ContinuousMap.ext
    intro p
    exact congrArg (fun t : (mapPoints f (mixedTest A B)).obj (firstPoint A B) ⟶
      (mapPoints f (mixedTest A B)).obj (secondPoint A B) ↦ t.val p) hr

/-- A global point gives a cocycle on the identity cover. -/
def ofPoint (a : G.Points T) : QuotientCocycle G T where
  coverSpace := T
  cover := 𝟙 T
  isCover := IsQuotientMap.id
  point := a
  transition := G.unit.comp ((show C(T.obj, G.objects.obj) from a).comp
    ⟨fun p ↦ p.val.1, continuous_fst.comp (continuous_Kelley_forget.comp continuous_subtype_val)⟩)
  transitionSource p := G.source_unit _
  transitionTarget p := (G.target_unit _).trans (congrArg a p.property)
  transitionUnit _ := rfl
  transitionComp x y z hxy hyz := by
    change x = y at hxy
    subst y
    have ho := G.unit_comp (G.unit (a x))
    change G.comp ⟨(G.unit (a x), G.unit (a x)), _⟩ = G.unit (a x)
    simpa only [G.source_unit] using ho

private def diagonal : C(T.obj, CGWH.FibreSubspace (𝟙 T) (𝟙 T)) :=
  ⟨fun x ↦ ⟨(x,x), rfl⟩,
    (kelleyPair (ContinuousMap.id _) (ContinuousMap.id _)).continuous.subtype_mk (fun _ ↦ rfl)⟩

private def pointToHom {a b : G.Points T} (f : a ⟶ b) : (ofPoint a).Hom (ofPoint b) := by
  refine ⟨⟨f.val.comp (fibreOne (ofPoint a) (ofPoint b)),
    fun p ↦ f.property.1 p.val.1, fun p ↦ (f.property.2 p.val.1).trans (congrArg b p.property)⟩, ?_⟩
  intro p q hp hq
  have he : p = q := Subtype.ext (Prod.ext hp hq)
  subst q
  let c := arrowAt (A := ofPoint a) (B := ofPoint b)
    ⟨f.val.comp (fibreOne (ofPoint a) (ofPoint b)), fun z ↦ f.property.1 z.val.1,
      fun z ↦ (f.property.2 z.val.1).trans (congrArg b z.property)⟩ p
  exact (@Category.id_comp G.Underlying _ _ _ c).trans (@Category.comp_id G.Underlying _ _ _ c).symm

private def homToPoint {a b : G.Points T} (f : (ofPoint a).Hom (ofPoint b)) : a ⟶ b :=
  ⟨f.val.val.comp diagonal, fun x ↦ f.val.property.1 (diagonal x),
    fun x ↦ f.val.property.2 (diagonal x)⟩

/-- The identity-cover presentations recover the actual arrows of continuous points. -/
def pointHomEquiv (a b : G.Points T) : (a ⟶ b) ≃ (ofPoint a).Hom (ofPoint b) where
  toFun := pointToHom
  invFun := homToPoint
  left_inv r := Subtype.ext (ContinuousMap.ext fun _ ↦ rfl)
  right_inv r := by
    apply Subtype.ext
    apply Subtype.ext
    ext p
    change r.val.val (diagonal p.val.1) = r.val.val p
    exact congrArg r.val.val (Subtype.ext (Prod.ext rfl p.property))

private def mappedPointHom (f : G ⟶ H) {a b : G.Points T}
    (r : (mapPoints f T).obj a ⟶ (mapPoints f T).obj b) :
    ((ofPoint a).map f).Hom ((ofPoint b).map f) := by
  refine ⟨⟨r.val.comp (fibreOne ((ofPoint a).map f) ((ofPoint b).map f)),
    fun p ↦ r.property.1 p.val.1, fun p ↦ (r.property.2 p.val.1).trans
      (congrArg ((mapPoints f T).obj b) p.property)⟩, ?_⟩
  intro p q hp hq
  have he : p = q := Subtype.ext (Prod.ext hp hq)
  subst q
  let c := arrowAt (A := (ofPoint a).map f) (B := (ofPoint b).map f)
    ⟨r.val.comp (fibreOne ((ofPoint a).map f) ((ofPoint b).map f)),
      fun z ↦ r.property.1 z.val.1,
      fun z ↦ (r.property.2 z.val.1).trans (congrArg ((mapPoints f T).obj b) z.property)⟩ p
  have ha := f.mapUnit (a p.val.1)
  have hb := f.mapUnit (b p.val.2)
  have hl : ((ofPoint a).map f).step p.val.1 p.val.1 hp =
      @CategoryStruct.id H.Underlying _ (f.objectMap (a p.val.1)) := Subtype.ext ha
  have hr : ((ofPoint b).map f).step p.val.2 p.val.2 hq =
      @CategoryStruct.id H.Underlying _ (f.objectMap (b p.val.2)) := Subtype.ext hb
  exact (congrArg (fun v ↦ @CategoryStruct.comp H.Underlying _ _ _ _ v c) hl).trans
    ((@Category.id_comp H.Underlying _ _ _ c).trans
      ((@Category.comp_id H.Underlying _ _ _ c).symm.trans
        (congrArg (fun v ↦ @CategoryStruct.comp H.Underlying _ _ _ _ c v) hr).symm))

/-- Identity covers recover full faithfulness of the original point functor. -/
theorem mapPoints_fullyFaithful_of_identityCovers (f : G ⟶ H)
    (h : ∀ a b : G.Points T, Bijective (mapHom f (A := ofPoint a) (B := ofPoint b))) :
    Nonempty (mapPoints f T).FullyFaithful := by
  apply (Functor.FullyFaithful.nonempty_iff_map_bijective (mapPoints f T)).mpr
  intro a b
  have h' := h a b
  have hm (r : a ⟶ b) : mapHom f (pointToHom r) = mappedPointHom f ((mapPoints f T).map r) := by
    apply Subtype.ext
    apply Subtype.ext
    apply ContinuousMap.ext
    intro p
    change f.arrowMap (r.val p.val.1) = f.arrowMap (r.val p.val.1)
    rfl
  constructor
  · intro r s hrs
    apply (pointHomEquiv a b).injective
    apply h'.1
    rw [show (pointHomEquiv a b) r = pointToHom r from rfl,
      show (pointHomEquiv a b) s = pointToHom s from rfl, hm, hm, hrs]
  · intro r
    obtain ⟨w, hw⟩ := h'.2 (mappedPointHom f r)
    refine ⟨homToPoint w, ?_⟩
    apply Subtype.ext
    apply ContinuousMap.ext
    intro x
    exact congrArg
      (fun z : ((ofPoint a).map f).Hom ((ofPoint b).map f) ↦ z.val.val (diagonal x)) hw

/-- The endpoint pullback criterion on continuous descent data and arrows. -/
theorem arrowComparison_homeomorph_iff_mapHom (f : G ⟶ H) :
    (∃ e : G.arrows.obj ≃ₜ ArrowComparisonSpace f, ∀ a, e a = arrowComparison f a) ↔
    ∀ (T : CGWH.{u}) (A B : QuotientCocycle G T), Bijective (mapHom f (A := A) (B := B)) :=
  ⟨fun h _ A B ↦ mapHom_bijective_of_arrowComparison f h A B, fun h ↦
    (arrowComparison_homeomorph_iff_mapPoints f).mpr (fun T ↦
      mapPoints_fullyFaithful_of_identityCovers f (fun a b ↦ h T (ofPoint a) (ofPoint b)))⟩

/-- Lemma E.6.4.1 on the category of quotient cocycles. -/
theorem arrowComparison_homeomorph_iff_mapCocycles (f : G ⟶ H) :
    (∃ e : G.arrows.obj ≃ₜ ArrowComparisonSpace f, ∀ a, e a = arrowComparison f a) ↔
      ∀ T : CGWH.{u}, Nonempty (mapCocycles (T := T) f).FullyFaithful := by
  rw [arrowComparison_homeomorph_iff_mapHom]
  exact forall_congr' fun T ↦ (Functor.FullyFaithful.nonempty_iff_map_bijective (mapCocycles (T := T) f)).symm

/-- An identity-cover point in the essential image lifts on the presenting
cover of a preimage cocycle. -/
theorem localPoint_of_cocycle_essSurj (f : G ⟶ H) (b : H.Points T)
    (h : (mapCocycles (T := T) f).EssSurj) :
    ∃ (V : CGWH.{u}) (q : V ⟶ T) (_ : IsQuotientMap q.hom) (a : G.Points V),
      Nonempty ((H.restrictPoints q.hom.hom.hom).obj b ⟶ (mapPoints f V).obj a) := by
  let P := ofPoint b
  let F := mapCocycles (T := T) f
  letI : F.EssSurj := h
  let A := F.objPreimage P
  let B := A.map f
  let e := F.objObjPreimageIso P
  let r : P.Hom B := e.inv
  let q := A.cover
  let z : C(A.coverSpace.obj, CGWH.FibreSubspace P.cover B.cover) :=
    ⟨fun x ↦ ⟨(q.hom x,x),rfl⟩,
      (kelleyPair q.hom.hom.hom (ContinuousMap.id _)).continuous.subtype_mk (fun _ ↦ rfl)⟩
  exact ⟨A.coverSpace, q, A.isCover, A.point,
    ⟨⟨r.val.val.comp z, fun x ↦ r.val.property.1 (z x), fun x ↦ r.val.property.2 (z x)⟩⟩⟩

/-- Essential surjectivity on cocycle categories implies the quotient-map
coverage condition. -/
theorem moritaAnchor_quotient_of_cocycle_essSurj (f : G ⟶ H)
    (h : ∀ T : CGWH.{u}, (mapCocycles (T := T) f).EssSurj) :
    IsQuotientMap (moritaAnchor f) :=
  (moritaAnchor_quotient_iff_localPoints f).mpr (fun T b ↦ localPoint_of_cocycle_essSurj f b (h T))

section Restriction

variable {S : CGWH.{u}}

private abbrev CoverPullback (A : QuotientCocycle G T) (g : S ⟶ T) :=
  CGWH.FibreSubspace A.cover g

private def coverPullbackObject (A : QuotientCocycle G T) (g : S ⟶ T) : CGWH.{u} :=
  CGWH.of (X := CoverPullback A g) (CGWH.fibreSubspace_weaklyHausdorff A.cover g)

private def coverPullbackLeft (A : QuotientCocycle G T) (g : S ⟶ T) :
    C(CoverPullback A g, A.coverSpace.obj) :=
  ⟨fun p ↦ p.val.1, continuous_fst.comp (continuous_Kelley_forget.comp continuous_subtype_val)⟩

private def coverPullbackRight (A : QuotientCocycle G T) (g : S ⟶ T) :
    coverPullbackObject A g ⟶ S :=
  CGWH.map ⟨fun (p : CoverPullback A g) ↦ p.val.2,
    continuous_snd.comp (continuous_Kelley_forget.comp continuous_subtype_val)⟩

/-- Restrict cocycle objects by base change of their covers. -/
def pullback (A : QuotientCocycle G T) (g : S ⟶ T) : QuotientCocycle G S := by
  let V := coverPullbackObject A g
  let l := coverPullbackLeft A g
  let r := coverPullbackRight A g
  let P := CGWH.FibreSubspace r r
  letI : CompactlyGeneratedSpace P := closed_compactlyGenerated (CGWH.fibreSubspace_isClosed r r)
  let a : C(P, V.obj) := ⟨fun p ↦ p.val.1,
    continuous_fst.comp (continuous_Kelley_forget.comp continuous_subtype_val)⟩
  let b : C(P, V.obj) := ⟨fun p ↦ p.val.2,
    continuous_snd.comp (continuous_Kelley_forget.comp continuous_subtype_val)⟩
  have h (p : P) : A.cover.hom (l (a p)) = A.cover.hom (l (b p)) :=
    (a p).property.trans ((congrArg g.hom p.property).trans (b p).property.symm)
  let d : C(P, CGWH.FibreSubspace A.cover A.cover) :=
    ⟨fun p ↦ ⟨(l (a p),l (b p)),h p⟩, (kelleyPair (l.comp a) (l.comp b)).continuous.subtype_mk h⟩
  exact {
    coverSpace := V
    cover := r
    isCover := CGWH.quotient_baseChange A.cover g A.isCover
    point := A.point.comp l
    transition := A.transition.comp d
    transitionSource := fun p ↦ A.transitionSource (d p)
    transitionTarget := fun p ↦ A.transitionTarget (d p)
    transitionUnit := fun x ↦ A.transitionUnit (l x)
    transitionComp := fun x y z _ _ ↦ A.transitionComp (l x) (l y) (l z) _ _ }

/-- Forget the base-change point in the common cover of two pullbacks. -/
def mixedPullback (A B : QuotientCocycle G T) (g : S ⟶ T) :
    C(CGWH.FibreSubspace (A.pullback g).cover (B.pullback g).cover,
      CGWH.FibreSubspace A.cover B.cover) := by
  let P := CGWH.FibreSubspace (A.pullback g).cover (B.pullback g).cover
  let a := (coverPullbackLeft A g).comp (fibreOne (A.pullback g) (B.pullback g))
  let b := (coverPullbackLeft B g).comp (fibreTwo (A.pullback g) (B.pullback g))
  have h (p : P) : A.cover.hom (a p) = B.cover.hom (b p) :=
    (p.val.1).property.trans ((congrArg g.hom p.property).trans (p.val.2).property.symm)
  exact ⟨fun p ↦ ⟨(a p,b p),h p⟩, (kelleyPair a b).continuous.subtype_mk h⟩

/-- Compatible arrows restrict by pulling back their common refinement. -/
def pullbackHom {A B : QuotientCocycle G T} (r : A.Hom B) (g : S ⟶ T) :
    (A.pullback g).Hom (B.pullback g) := by
  let d := mixedPullback A B g
  refine ⟨⟨r.val.val.comp d, fun p ↦ r.val.property.1 (d p),
    fun p ↦ r.val.property.2 (d p)⟩, ?_⟩
  intro p q hp hq
  have h₁ : A.cover.hom (d p).val.1 = A.cover.hom (d q).val.1 :=
    (p.val.1).property.trans ((congrArg g.hom hp).trans (q.val.1).property.symm)
  have h₂ : B.cover.hom (d p).val.2 = B.cover.hom (d q).val.2 :=
    (p.val.2).property.trans ((congrArg g.hom hq).trans (q.val.2).property.symm)
  exact r.property (d p) (d q) h₁ h₂

/-- Base change is functorial on each category of cocycle presentations. -/
noncomputable def pullbackFunctor (g : S ⟶ T) : QuotientCocycle G T ⥤ QuotientCocycle G S where
  obj A := A.pullback g
  map r := pullbackHom r g
  map_id A := by
    change pullbackHom (identityHom A) g = identityHom (A.pullback g)
    apply Subtype.ext
    apply Subtype.ext
    exact ContinuousMap.ext fun _ ↦ rfl
  map_comp {A B C} r s := by
    change pullbackHom (composeHom r s) g = composeHom (pullbackHom r g) (pullbackHom s g)
    apply Subtype.ext
    apply Subtype.ext
    apply ContinuousMap.ext
    intro p
    let e := mixedPullback A C g
    obtain ⟨b,hb⟩ := (B.pullback g).isCover.surjective ((A.pullback g).cover.hom p.val.1)
    let y : Triple (A.pullback g) (B.pullback g) (C.pullback g) := ⟨(b,p),hb⟩
    let b₀ := coverPullbackLeft B g b
    have h₀ : B.cover.hom b₀ = A.cover.hom (e p).val.1 :=
      b.property.trans ((congrArg g.hom hb).trans p.val.1.property.symm)
    let x : Triple A B C := ⟨(b₀,e p),h₀⟩
    have hl := congrArg Subtype.val (composeHom_eval r s x)
    have hr := congrArg Subtype.val (composeHom_eval (pullbackHom r g) (pullbackHom s g) y)
    exact hl.trans hr.symm

/-- After restriction to its presenting cover, a cocycle object is
isomorphic to the point from which it was constructed. -/
theorem pullback_cover_locally_point (A : QuotientCocycle G T) :
    Nonempty (A.pullback A.cover ≅ ofPoint (T := A.coverSpace) A.point) := by
  let B := A.pullback A.cover
  let C := ofPoint (T := A.coverSpace) (G := G) A.point
  let x : C(CGWH.FibreSubspace B.cover C.cover, A.coverSpace.obj) :=
    (coverPullbackLeft A A.cover).comp (fibreOne B C)
  let y : C(CGWH.FibreSubspace B.cover C.cover, A.coverSpace.obj) := fibreTwo B C
  have hp (p : CGWH.FibreSubspace B.cover C.cover) : A.cover.hom (x p) = A.cover.hom (y p) :=
    (p.val.1).property.trans (congrArg A.cover.hom p.property)
  let W : C(CGWH.FibreSubspace B.cover C.cover, CGWH.FibreSubspace A.cover A.cover) :=
    ⟨fun p ↦ ⟨(x p,y p),hp p⟩, (kelleyPair x y).continuous.subtype_mk hp⟩
  let r : firstPoint B C ⟶ secondPoint B C := ⟨A.transition.comp W,
    fun p ↦ A.transitionSource (W p), fun p ↦ A.transitionTarget (W p)⟩
  have hr : r ∈ {r : firstPoint B C ⟶ secondPoint B C |
      ∀ (p q : CGWH.FibreSubspace B.cover C.cover)
        (hpq : B.cover.hom p.val.1 = B.cover.hom q.val.1)
        (hqp : C.cover.hom p.val.2 = C.cover.hom q.val.2),
        @CategoryStruct.comp G.Underlying _ _ _ _ (B.step p.val.1 q.val.1 hpq)
          (arrowAt (A := B) (B := C) r q) =
        @CategoryStruct.comp G.Underlying _ _ _ _ (arrowAt (A := B) (B := C) r p)
          (C.step p.val.2 q.val.2 hqp)} := by
    intro p q hl hz
    have he : y p = y q := hz
    have hd : A.cover.hom (x p) = A.cover.hom (x q) :=
      (hp p).trans ((congrArg A.cover.hom he).trans (hp q).symm)
    have h₁ := step_comp A (x p) (x q) (y q) hd (hp q)
    have h₂ := step_comp A (x p) (y p) (y q) (hp p) (congrArg A.cover.hom he)
    exact h₁.trans (h₂.symm.trans (congrArg
      (fun a ↦ @CategoryStruct.comp G.Underlying _ _ _ _ (A.step (x p) (y p) (hp p)) a)
      (by
        apply Subtype.ext
        change A.transition ⟨(y p,y q),congrArg A.cover.hom he⟩ = G.unit (A.point (y p))
        have hpair : (⟨(y p,y q),congrArg A.cover.hom he⟩ : CGWH.FibreSubspace A.cover A.cover) =
            ⟨(y p,y p),rfl⟩ := Subtype.ext (Prod.ext rfl he.symm)
        exact (congrArg A.transition hpair).trans (A.transitionUnit _))))
  let a : B ⟶ C := ⟨r,hr⟩
  exact ⟨asIso a⟩

end Restriction

section Refinement

variable {W : CGWH.{u}}

/-- Replace the presenting cover by a composite which is still a quotient map. -/
def refinePresentation (A : QuotientCocycle G T) (g : W ⟶ A.coverSpace)
    (hg : IsQuotientMap (g ≫ A.cover).hom) : QuotientCocycle G T := by
  let P := CGWH.FibreSubspace (g ≫ A.cover) (g ≫ A.cover)
  letI : CompactlyGeneratedSpace P :=
    closed_compactlyGenerated (CGWH.fibreSubspace_isClosed (g ≫ A.cover) (g ≫ A.cover))
  let L : C(P, A.coverSpace.obj) := ⟨fun p ↦ g.hom p.val.1,
    g.hom.hom.hom.continuous.comp (continuous_fst.comp
      (continuous_Kelley_forget.comp continuous_subtype_val))⟩
  let R : C(P, A.coverSpace.obj) := ⟨fun p ↦ g.hom p.val.2,
    g.hom.hom.hom.continuous.comp (continuous_snd.comp
      (continuous_Kelley_forget.comp continuous_subtype_val))⟩
  have h (p : P) : A.cover.hom (L p) = A.cover.hom (R p) := p.property
  let d : C(P, CGWH.FibreSubspace A.cover A.cover) :=
    ⟨fun p ↦ ⟨(L p,R p),h p⟩, (kelleyPair L R).continuous.subtype_mk h⟩
  exact {
    coverSpace := W
    cover := g ≫ A.cover
    isCover := hg
    point := A.point.comp g.hom.hom.hom
    transition := A.transition.comp d
    transitionSource := fun p ↦ A.transitionSource (d p)
    transitionTarget := fun p ↦ A.transitionTarget (d p)
    transitionUnit := fun x ↦ A.transitionUnit (g.hom x)
    transitionComp := fun x y z _ _ ↦ A.transitionComp (g.hom x) (g.hom y) (g.hom z) _ _ }

/-- The transition arrows identify the refined presentation with the
original whenever the new map to the base is quotient. -/
theorem refinePresentation_iso (A : QuotientCocycle G T) (g : W ⟶ A.coverSpace)
    (hg : IsQuotientMap (g ≫ A.cover).hom) : Nonempty (A.refinePresentation g hg ≅ A) := by
  let B := A.refinePresentation g hg
  let x := g.hom.hom.hom.comp (fibreOne B A)
  let y := fibreTwo B A
  have h (p : CGWH.FibreSubspace B.cover A.cover) : A.cover.hom (x p) = A.cover.hom (y p) := p.property
  let E : C(CGWH.FibreSubspace B.cover A.cover, CGWH.FibreSubspace A.cover A.cover) :=
    ⟨fun p ↦ ⟨(x p,y p),h p⟩, (kelleyPair x y).continuous.subtype_mk h⟩
  let r : B.Hom A := ⟨⟨A.transition.comp E,
    fun p ↦ A.transitionSource (E p), fun p ↦ A.transitionTarget (E p)⟩, by
    intro p q hp hq
    exact (step_comp A (x p) (x q) (y q) hp (h q)).trans
      (step_comp A (x p) (y p) (y q) (h p) hq).symm⟩
  let r' : B ⟶ A := r
  exact ⟨asIso r'⟩

/-- Replace the presenting cover by its composite with another quotient map. -/
def refineCover (A : QuotientCocycle G T) (g : W ⟶ A.coverSpace)
    (hg : IsQuotientMap g.hom) : QuotientCocycle G T :=
  A.refinePresentation g (A.isCover.comp hg)

/-- A quotient refinement is isomorphic to the original presentation. -/
theorem refineCover_iso (A : QuotientCocycle G T) (g : W ⟶ A.coverSpace)
    (hg : IsQuotientMap g.hom) : Nonempty (A.refineCover g hg ≅ A) :=
  A.refinePresentation_iso g (A.isCover.comp hg)

end Refinement

section ChangeOfPoint

private theorem conjugation_comp {C : Type*} [Category C] {x y z a b c : C}
    (i : x ≅ a) (j : y ≅ b) (k : z ≅ c) (v : a ⟶ b) (w : b ⟶ c) :
    (i.hom ≫ v ≫ j.inv) ≫ j.hom ≫ w ≫ k.inv = i.hom ≫ (v ≫ w) ≫ k.inv := by
  simp [Category.assoc]

private theorem conjugation_unit {C : Type*} [Category C] {x a : C} (i : x ≅ a) :
    i.hom ≫ 𝟙 a ≫ i.inv = 𝟙 x := by simp

private theorem conjugation_compat {C : Type*} [Category C] {x x' a b c d : C}
    (i : x ≅ a) (j : x' ≅ b) (v : a ⟶ b) (w : b ⟶ d) (p : a ⟶ c) (q : c ⟶ d)
    (h : v ≫ w = p ≫ q) :
    (i.hom ≫ v ≫ j.inv) ≫ j.hom ≫ w = (i.hom ≫ p) ≫ q := by
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  exact congrArg (i.hom ≫ ·) h

private def pointIsoAt {V : CGWH.{u}} {a b : G.Points V} (r : a ⟶ b) (x : V.obj) :
    @Iso G.Underlying _ (a x) (b x) := by
  let u : G.UnderlyingArrow (a x) (b x) := ⟨r.val x, r.property.1 x, r.property.2 x⟩
  exact ⟨u, @Groupoid.inv G.Underlying _ _ _ u, @Groupoid.comp_inv G.Underlying _ _ _ u,
    @Groupoid.inv_comp G.Underlying _ _ _ u⟩

/-- Change the local point on a fixed cover by conjugating the cocycle
through a continuous family of isomorphisms. -/
def changePoint (A : QuotientCocycle G T) (a : G.Points A.coverSpace) (r : a ⟶ A.point) :
    QuotientCocycle G T := by
  let P := CGWH.FibreSubspace A.cover A.cover
  letI : CompactlyGeneratedSpace P :=
    closed_compactlyGenerated (CGWH.fibreSubspace_isClosed A.cover A.cover)
  let l := r.val.comp (fibreOne A A)
  let j := (G.inverse.comp r.val).comp (fibreTwo A A)
  let v := G.composeMaps A.transition j (fun p ↦
    (A.transitionTarget p).trans ((G.source_inv _).trans (r.property.2 p.val.2)).symm)
  let w := G.composeMaps l v (fun p ↦
    (r.property.2 p.val.1).trans ((G.source_comp _).trans (A.transitionSource p)).symm)
  have hs (p : P) : G.source (w p) = a p.val.1 :=
    (G.source_comp _).trans (r.property.1 p.val.1)
  have ht (p : P) : G.target (w p) = a p.val.2 :=
    (G.target_comp _).trans ((G.target_comp _).trans ((G.target_inv _).trans (r.property.1 p.val.2)))
  have hval (x y : A.coverSpace.obj) (h : A.cover.hom x = A.cover.hom y) :
      w ⟨(x,y),h⟩ = (@CategoryStruct.comp G.Underlying _ _ _ _ (pointIsoAt r x).hom
        (@CategoryStruct.comp G.Underlying _ _ _ _ (A.step x y h) (pointIsoAt r y).inv)).val := rfl
  refine { A with
    point := a
    transition := w
    transitionSource := hs
    transitionTarget := ht
    transitionUnit := ?_
    transitionComp := ?_ }
  · intro x
    refine (hval x x rfl).trans ?_
    have he := @conjugation_unit G.Underlying _ _ _ (pointIsoAt r x)
    exact (congrArg (fun v : G.UnderlyingArrow (A.point x) (A.point x) ↦
      (@CategoryStruct.comp G.Underlying _ _ _ _ (pointIsoAt r x).hom
        (@CategoryStruct.comp G.Underlying _ _ _ _ v (pointIsoAt r x).inv)).val) (step_unit A x)).trans
        (congrArg Subtype.val he)
  · intro x y z hxy hyz
    let L : G.UnderlyingArrow (a x) (a y) := ⟨w ⟨(x,y),hxy⟩, hs _, ht _⟩
    let R : G.UnderlyingArrow (a y) (a z) := ⟨w ⟨(y,z),hyz⟩, hs _, ht _⟩
    have hl : L = @CategoryStruct.comp G.Underlying _ _ _ _ (pointIsoAt r x).hom
        (@CategoryStruct.comp G.Underlying _ _ _ _ (A.step x y hxy) (pointIsoAt r y).inv) :=
      Subtype.ext (hval x y hxy)
    have hr : R = @CategoryStruct.comp G.Underlying _ _ _ _ (pointIsoAt r y).hom
        (@CategoryStruct.comp G.Underlying _ _ _ _ (A.step y z hyz) (pointIsoAt r z).inv) :=
      Subtype.ext (hval y z hyz)
    have he := @conjugation_comp G.Underlying _ _ _ _ _ _ _
      (pointIsoAt r x) (pointIsoAt r y) (pointIsoAt r z) (A.step x y hxy) (A.step y z hyz)
    exact (congrArg₂ (fun l r ↦ (@CategoryStruct.comp G.Underlying _ _ _ _ l r).val) hl hr).trans
      ((congrArg Subtype.val he).trans ((congrArg (fun t : G.UnderlyingArrow (A.point x) (A.point z) ↦
        (@CategoryStruct.comp G.Underlying _ _ _ _ (pointIsoAt r x).hom
          (@CategoryStruct.comp G.Underlying _ _ _ _ t (pointIsoAt r z).inv)).val)
        (step_comp A x y z hxy hyz)).trans (hval x z (hxy.trans hyz)).symm))

private theorem changePoint_step (A : QuotientCocycle G T) (a : G.Points A.coverSpace)
    (r : a ⟶ A.point) (x y : A.coverSpace.obj) (h : A.cover.hom x = A.cover.hom y) :
    (A.changePoint a r).step x y h =
      @CategoryStruct.comp G.Underlying _ _ _ _ (pointIsoAt r x).hom
        (@CategoryStruct.comp G.Underlying _ _ _ _ (A.step x y h) (pointIsoAt r y).inv) := rfl

theorem changePoint_iso (A : QuotientCocycle G T) (a : G.Points A.coverSpace) (r : a ⟶ A.point) :
    Nonempty (A.changePoint a r ≅ A) := by
  let B := A.changePoint a r
  let P := CGWH.FibreSubspace B.cover A.cover
  letI : CompactlyGeneratedSpace P := closed_compactlyGenerated (CGWH.fibreSubspace_isClosed B.cover A.cover)
  let l : C(P, G.arrows.obj) := r.val.comp (fibreOne B A)
  let m : C(P, G.arrows.obj) := A.transition
  let w := G.composeMaps l m (fun p ↦ (r.property.2 p.val.1).trans (A.transitionSource p).symm)
  let W : firstPoint B A ⟶ secondPoint B A := ⟨w, fun p ↦
    (G.source_comp _).trans (r.property.1 p.val.1), fun p ↦
      (G.target_comp _).trans (A.transitionTarget p)⟩
  have hw (p : P) : arrowAt (A := B) (B := A) W p =
      @CategoryStruct.comp G.Underlying _ _ _ _ (pointIsoAt r p.val.1).hom
        (A.step p.val.1 p.val.2 p.property) := rfl
  let k : B ⟶ A := ⟨W, by
    intro p q hp hq
    have he := changePoint_step A a r p.val.1 q.val.1 hp
    have h₁ := step_comp A p.val.1 q.val.1 q.val.2 hp q.property
    have h₂ := step_comp A p.val.1 p.val.2 q.val.2 p.property hq
    have h := @conjugation_compat G.Underlying _ _ _ _ _ _ _
      (pointIsoAt r p.val.1) (pointIsoAt r q.val.1) (A.step p.val.1 q.val.1 hp)
      (A.step q.val.1 q.val.2 q.property) (A.step p.val.1 p.val.2 p.property)
      (A.step p.val.2 q.val.2 hq) (h₁.trans h₂.symm)
    exact (congrArg₂ (fun x y ↦ @CategoryStruct.comp G.Underlying _ _ _ _ x y) he (hw q)).trans
      (h.trans (congrArg (fun x ↦ @CategoryStruct.comp G.Underlying _ _ _ _ x
        (A.step p.val.2 q.val.2 hq)) (hw p).symm))⟩
  exact ⟨asIso k⟩

end ChangeOfPoint

private theorem cocycle_eq_of_fields {A B : QuotientCocycle G T}
    (hS : A.coverSpace = B.coverSpace) (hcover : HEq A.cover B.cover)
    (hpoint : HEq A.point B.point) (htransition : HEq A.transition B.transition) :
    A = B := by
  cases A
  cases B
  cases hS
  cases hcover
  cases hpoint
  cases htransition
  rfl

/-- The arrow pullback lifts a cocycle once its presenting point has been
lifted. All of its cocycle laws are reflected by faithfulness. -/
theorem liftCocycle_of_point {A : QuotientCocycle H T} (f : G ⟶ H)
    (e : G.arrows.obj ≃ₜ ArrowComparisonSpace f) (he : ∀ x, e x = arrowComparison f x)
    (a : G.Points A.coverSpace) (ha : ∀ x, f.objectMap (a x) = A.point x) :
    ∃ B : QuotientCocycle G T, B.map f = A := by
  let P := CGWH.FibreSubspace A.cover A.cover
  letI : CompactlyGeneratedSpace P :=
    closed_compactlyGenerated (CGWH.fibreSubspace_isClosed A.cover A.cover)
  let a₀ : C(A.coverSpace.obj, G.objects.obj) := a
  let l := a₀.comp (fibreOne A A)
  let r := a₀.comp (fibreTwo A A)
  have hx (p : P) : (f.objectMap (l p), f.objectMap (r p)) =
      (H.source (A.transition p), H.target (A.transition p)) :=
    Prod.ext ((ha p.val.1).trans (A.transitionSource p).symm)
      ((ha p.val.2).trans (A.transitionTarget p).symm)
  let j : C(P, ArrowComparisonSpace f) :=
    ⟨fun p ↦ ⟨((l p,r p),A.transition p),hx p⟩,
      (kelleyPair (kelleyPair l r) A.transition).continuous.subtype_mk hx⟩
  let inv : C(ArrowComparisonSpace f, G.arrows.obj) := ⟨e.symm,e.symm.continuous⟩
  let K := inv.comp j
  have hK (p : P) : arrowComparison f (K p) = j p :=
    (he _).symm.trans (e.apply_symm_apply _)
  have hs (p : P) : G.source (K p) = a p.val.1 :=
    congrArg (fun p : ArrowComparisonSpace f ↦ p.val.1.1) (hK p)
  have ht (p : P) : G.target (K p) = a p.val.2 :=
    congrArg (fun p : ArrowComparisonSpace f ↦ p.val.1.2) (hK p)
  have hmap (p : P) : f.arrowMap (K p) = A.transition p :=
    congrArg (fun p : ArrowComparisonSpace f ↦ p.val.2) (hK p)
  have hi : Injective (arrowComparison f) := by
    intro x y h
    apply e.injective
    exact (he x).trans (h.trans (he y).symm)
  let U (x y : A.coverSpace.obj) (h : A.cover.hom x = A.cover.hom y) :
      G.UnderlyingArrow (a x) (a y) :=
    ⟨K ⟨(x,y),h⟩, hs _, ht _⟩
  have hUnit (x : A.coverSpace.obj) : K ⟨(x,x),rfl⟩ = G.unit (a x) := by
    have hu : U x x rfl = @CategoryStruct.id G.Underlying _ (a x) := by
      apply underlying_map_injective_of_arrowComparison f hi
      apply Subtype.ext
      change f.arrowMap (K ⟨(x,x),rfl⟩) = f.arrowMap (G.unit (a x))
      exact (hmap _).trans ((A.transitionUnit x).trans
        ((congrArg H.unit (ha x).symm).trans (f.mapUnit (a x)).symm))
    exact congrArg Subtype.val hu
  have hComp (x y z : A.coverSpace.obj)
      (hxy : A.cover.hom x = A.cover.hom y) (hyz : A.cover.hom y = A.cover.hom z) :
      @CategoryStruct.comp G.Underlying _ _ _ _ (U x y hxy) (U y z hyz) = U x z (hxy.trans hyz) := by
    apply underlying_map_injective_of_arrowComparison f hi
    apply Subtype.ext
    change f.arrowMap (G.comp ⟨(K ⟨(x,y),hxy⟩,K ⟨(y,z),hyz⟩), _⟩) =
      f.arrowMap (K ⟨(x,z),hxy.trans hyz⟩)
    refine (f.mapComp _ _ _).trans ?_
    exact (congrArg H.comp (Subtype.ext (Prod.ext (hmap _) (hmap _)))).trans
      ((A.transitionComp x y z hxy hyz).trans (hmap _).symm)
  let B : QuotientCocycle G T := {
    coverSpace := A.coverSpace
    cover := A.cover
    isCover := A.isCover
    point := a₀
    transition := K
    transitionSource := hs
    transitionTarget := ht
    transitionUnit := hUnit
    transitionComp := fun x y z hxy hyz ↦ congrArg Subtype.val (hComp x y z hxy hyz) }
  refine ⟨B, cocycle_eq_of_fields rfl (HEq.rfl) ?_ ?_⟩
  · exact heq_of_eq (ContinuousMap.ext ha)
  · exact heq_of_eq (ContinuousMap.ext hmap)

/-- The two Morita conditions suffice for essential surjectivity on the
actual cocycle groupoids. -/
theorem cocycle_essSurj_of_morita (f : G ⟶ H)
    (hf : ∃ e : G.arrows.obj ≃ₜ ArrowComparisonSpace f, ∀ a, e a = arrowComparison f a)
    (hq : IsQuotientMap (moritaAnchor f)) : (mapCocycles (T := T) f).EssSurj where
  mem_essImage A := by
    obtain ⟨e,he⟩ := hf
    obtain ⟨V,q,hq',a,⟨r⟩⟩ := (moritaAnchor_quotient_iff_localPoints f).mp hq A.coverSpace A.point
    let B := A.refineCover q hq'
    let aH : H.Points B.coverSpace := (mapPoints f V).obj a
    let r' : aH ⟶ B.point := @Groupoid.inv (H.Points V) _ _ _ r
    let C := B.changePoint aH r'
    obtain ⟨D,hD⟩ := liftCocycle_of_point (A := C) f e he a (fun _ ↦ rfl)
    obtain ⟨I⟩ := B.changePoint_iso aH r'
    obtain ⟨J⟩ := A.refineCover_iso q hq'
    exact ⟨D, ⟨(eqToIso hD) ≪≫ I ≪≫ J⟩⟩

/-- The complete Morita criterion for the cocycle groupoids. -/
theorem mapCocycles_isEquivalence_iff_morita (f : G ⟶ H) :
    (∀ T : CGWH.{u}, (mapCocycles (T := T) f).IsEquivalence) ↔
    (∃ e : G.arrows.obj ≃ₜ ArrowComparisonSpace f, ∀ a, e a = arrowComparison f a) ∧
      IsQuotientMap (moritaAnchor f) := by
  constructor
  · intro h
    refine ⟨(arrowComparison_homeomorph_iff_mapCocycles f).mpr ?_, ?_⟩
    · intro T
      letI : (mapCocycles (T := T) f).IsEquivalence := h T
      exact ⟨Functor.FullyFaithful.ofFullyFaithful _⟩
    · apply moritaAnchor_quotient_of_cocycle_essSurj
      intro T
      letI : (mapCocycles (T := T) f).IsEquivalence := h T
      infer_instance
  · rintro ⟨he,hq⟩ T
    obtain ⟨hff⟩ := (arrowComparison_homeomorph_iff_mapCocycles f).mp he T
    letI : (mapCocycles (T := T) f).Full := hff.full
    letI : (mapCocycles (T := T) f).Faithful := hff.faithful
    letI : (mapCocycles (T := T) f).EssSurj := cocycle_essSurj_of_morita f he hq
    exact {}

/-- A standard Morita functor gives equivalences on all cocycle groupoids. -/
theorem mapCocycles_isEquivalence_of_standardMorita (f : G ⟶ H)
    (hf : IsStandardMorita f) : (mapCocycles (T := T) f).IsEquivalence :=
  (mapCocycles_isEquivalence_iff_morita f).mpr
    ⟨hf.2, moritaAnchor_quotient_of_object_quotient f hf.1⟩ T

/-- A change of presenting cover preserving points and transitions gives
an isomorphism of the presented cocycles. -/
noncomputable def isoOfCoverMap (A B : QuotientCocycle G T)
    (k : C(B.coverSpace.obj, A.coverSpace.obj))
    (hk : ∀ x, A.cover.hom (k x) = B.cover.hom x)
    (hp : ∀ x, A.point (k x) = B.point x)
    (ht : ∀ x y (h : B.cover.hom x = B.cover.hom y),
      B.transition ⟨(x,y),h⟩ = A.transition ⟨(k x,k y),(hk x).trans (h.trans (hk y).symm)⟩) :
    B ≅ A := by
  let P := CGWH.FibreSubspace B.cover A.cover
  let x := k.comp (fibreOne B A)
  let y := fibreTwo B A
  have h (p : P) : A.cover.hom (x p) = A.cover.hom (y p) :=
    (hk p.val.1).trans p.property
  let K : C(P, CGWH.FibreSubspace A.cover A.cover) :=
    ⟨fun p ↦ ⟨(x p,y p),h p⟩, (kelleyPair x y).continuous.subtype_mk h⟩
  let R : firstPoint B A ⟶ secondPoint B A :=
    ⟨A.transition.comp K, fun p ↦ (A.transitionSource (K p)).trans (hp p.val.1),
      fun p ↦ A.transitionTarget (K p)⟩
  let r : B ⟶ A := ⟨R, by
    intro p q hpq hq
    let e := (hk p.val.1).trans (hpq.trans (hk q.val.1).symm)
    have ha := A.transitionComp (x p) (x q) (y q) e (h q)
    have hb := A.transitionComp (x p) (y p) (y q) (h p) hq
    have hL : G.target (B.transition ⟨(p.val.1,q.val.1),hpq⟩) =
        G.source (A.transition ⟨(x q,y q),h q⟩) :=
      (B.transitionTarget ⟨(p.val.1,q.val.1),hpq⟩).trans ((hp q.val.1).symm.trans
        (A.transitionSource ⟨(x q,y q),h q⟩).symm)
    have hR : G.target (A.transition ⟨(x p,x q),e⟩) =
        G.source (A.transition ⟨(x q,y q),h q⟩) :=
      (A.transitionTarget ⟨(x p,x q),e⟩).trans (A.transitionSource ⟨(x q,y q),h q⟩).symm
    have hcomp : G.comp ⟨(B.transition ⟨(p.val.1,q.val.1),hpq⟩,
          A.transition ⟨(x q,y q),h q⟩),hL⟩ =
        G.comp ⟨(A.transition ⟨(x p,x q),e⟩, A.transition ⟨(x q,y q),h q⟩),hR⟩ :=
      congrArg G.comp (Subtype.ext (Prod.ext (ht p.val.1 q.val.1 hpq) rfl))
    apply Subtype.ext
    exact hcomp.trans (ha.trans hb.symm)⟩
  exact asIso r

theorem iso_of_cover_map (A B : QuotientCocycle G T)
    (k : C(B.coverSpace.obj, A.coverSpace.obj))
    (hk : ∀ x, A.cover.hom (k x) = B.cover.hom x)
    (hp : ∀ x, A.point (k x) = B.point x)
    (ht : ∀ x y (h : B.cover.hom x = B.cover.hom y),
      B.transition ⟨(x,y),h⟩ = A.transition ⟨(k x,k y),(hk x).trans (h.trans (hk y).symm)⟩) :
    Nonempty (B ≅ A) := ⟨isoOfCoverMap A B k hk hp ht⟩

/-- The canonical cover comparison evaluates to the target transition
from the image of the first presenting point. -/
theorem isoOfCoverMap_hom_apply (A B : QuotientCocycle G T)
    (k : C(B.coverSpace.obj, A.coverSpace.obj))
    (hk : ∀ x, A.cover.hom (k x) = B.cover.hom x)
    (hp : ∀ x, A.point (k x) = B.point x)
    (ht : ∀ x y (h : B.cover.hom x = B.cover.hom y),
      B.transition ⟨(x,y),h⟩ = A.transition ⟨(k x,k y),(hk x).trans (h.trans (hk y).symm)⟩)
    (p : CGWH.FibreSubspace B.cover A.cover) :
    (isoOfCoverMap A B k hk hp ht).hom.val.val p = A.transition ⟨(k p.val.1,p.val.2),
      (hk p.val.1).trans p.property⟩ := rfl

/-- The pullback of a presentation along the identity is canonically
isomorphic to the original presentation. -/
noncomputable def pullbackIdIso (A : QuotientCocycle G T) : A.pullback (𝟙 T) ≅ A :=
  isoOfCoverMap A (A.pullback (𝟙 T)) (coverPullbackLeft A (𝟙 T))
    (fun x ↦ x.property) (fun _ ↦ rfl) (fun _ _ _ ↦ rfl)

theorem pullback_id_obj_iso (A : QuotientCocycle G T) :
    Nonempty (A.pullback (𝟙 T) ≅ A) := ⟨pullbackIdIso A⟩

/-- The identity comparison uses the transition on the original cover. -/
theorem pullbackIdIso_hom_apply (A : QuotientCocycle G T)
    (p : CGWH.FibreSubspace (A.pullback (𝟙 T)).cover A.cover) :
    (pullbackIdIso A).hom.val.val p =
      A.transition ⟨(p.val.1.val.1,p.val.2),p.val.1.property.trans p.property⟩ := rfl

private def pullbackCompLift (A : QuotientCocycle G T) {R S : CGWH.{u}} (g : S ⟶ T) (h : R ⟶ S) :
    C((A.pullback (h ≫ g)).coverSpace.obj,((A.pullback g).pullback h).coverSpace.obj) := by
  let B := A.pullback (h ≫ g)
  let V := A.pullback g
  let a := coverPullbackLeft A (h ≫ g)
  let r : C(B.coverSpace.obj,R.obj) := B.cover.hom.hom.hom
  let s := h.hom.hom.hom.comp r
  let v : C(B.coverSpace.obj,V.coverSpace.obj) :=
    ⟨fun p ↦ ⟨(a p,s p),p.property⟩,(kelleyPair a s).continuous.subtype_mk _⟩
  exact ⟨fun p ↦ ⟨(v p,r p),rfl⟩,(kelleyPair v r).continuous.subtype_mk _⟩

/-- Comparing one pullback along a composite with the two successive
pullbacks preserves the original presenting point. -/
noncomputable def pullbackCompIso (A : QuotientCocycle G T) {R S : CGWH.{u}} (g : S ⟶ T) (h : R ⟶ S) :
    A.pullback (h ≫ g) ≅ (A.pullback g).pullback h :=
  isoOfCoverMap _ _ (pullbackCompLift A g h) (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ _ ↦ rfl)

/-- The composition comparison uses the transition on the original cover. -/
theorem pullbackCompIso_hom_apply (A : QuotientCocycle G T) {R S : CGWH.{u}} (g : S ⟶ T) (h : R ⟶ S)
    (p : CGWH.FibreSubspace (A.pullback (h ≫ g)).cover ((A.pullback g).pullback h).cover) :
    (pullbackCompIso A g h).hom.val.val p = A.transition ⟨(p.val.1.val.1,p.val.2.val.1.val.1),
      p.val.1.property.trans ((congrArg (fun z ↦ (h ≫ g).hom z) p.property).trans
        ((congrArg g.hom p.val.2.property).symm.trans p.val.2.val.1.property.symm))⟩ := rfl

/-- The canonical rebracketing of iterated pullbacks identifies their
cocycle objects. -/
theorem pullback_comp_obj_iso (A : QuotientCocycle G T) {R S : CGWH.{u}} (g : S ⟶ T) (h : R ⟶ S) :
    Nonempty (((A.pullback g).pullback h) ≅ A.pullback (h ≫ g)) := ⟨(pullbackCompIso A g h).symm⟩

private theorem pullbackIdIso_natural {A B : QuotientCocycle G T} (r : A ⟶ B) :
    pullbackHom r (𝟙 T) ≫ (pullbackIdIso B).hom = (pullbackIdIso A).hom ≫ r := by
  apply hom_ext
  intro p
  let x := p.val.1
  let y := p.val.2
  let y' : (B.pullback (𝟙 T)).coverSpace.obj := ⟨(y,B.cover.hom y),rfl⟩
  have hx : (A.pullback (𝟙 T)).cover.hom x = A.cover.hom x.val.1 := x.property.symm
  have hp : (A.pullback (𝟙 T)).cover.hom x = (B.pullback (𝟙 T)).cover.hom y' := p.property
  exact (comp_apply_right_unit (pullbackHom r (𝟙 T)) (pullbackIdIso B).hom x y' y hp rfl
    (B.transitionUnit y)).trans
    (comp_apply_left_unit (pullbackIdIso A).hom r x x.val.1 y hx (hx.symm.trans p.property)
      (A.transitionUnit x.val.1)).symm

private theorem pullbackCompIso_natural {A B : QuotientCocycle G T} (r : A ⟶ B)
    {R S : CGWH.{u}} (g : S ⟶ T) (h : R ⟶ S) :
    pullbackHom r (h ≫ g) ≫ (pullbackCompIso B g h).hom =
      (pullbackCompIso A g h).hom ≫ pullbackHom (pullbackHom r g) h := by
  apply hom_ext
  intro p
  let x := p.val.1
  let y := p.val.2
  have hy : B.cover.hom y.val.1.val.1 = (h ≫ g).hom y.val.2 :=
    y.val.1.property.trans (congrArg g.hom y.property)
  let y' : (B.pullback (h ≫ g)).coverSpace.obj := ⟨(y.val.1.val.1,y.val.2),hy⟩
  let x' := pullbackCompLift A g h x
  have hp : (A.pullback (h ≫ g)).cover.hom x = ((B.pullback g).pullback h).cover.hom y := p.property
  exact (comp_apply_right_unit (pullbackHom r (h ≫ g)) (pullbackCompIso B g h).hom x y' y hp rfl
    (B.transitionUnit y.val.1.val.1)).trans
    (comp_apply_left_unit (pullbackCompIso A g h).hom (pullbackHom (pullbackHom r g) h) x x' y rfl hp
      (A.transitionUnit x.val.1)).symm

/-- Restriction along the identity is naturally isomorphic to the identity functor. -/
noncomputable def pullbackIdNatIso : pullbackFunctor (G := G) (𝟙 T) ≅ 𝟭 (QuotientCocycle G T) :=
  NatIso.ofComponents pullbackIdIso pullbackIdIso_natural

/-- Restriction along a composite is naturally isomorphic to successive restriction. -/
noncomputable def pullbackCompNatIso {R S : CGWH.{u}} (g : S ⟶ T) (h : R ⟶ S) :
    pullbackFunctor (G := G) (h ≫ g) ≅ pullbackFunctor g ⋙ pullbackFunctor h :=
  NatIso.ofComponents (fun A ↦ pullbackCompIso A g h) (fun r ↦ pullbackCompIso_natural r g h)

/-- The identity comparison cancels rebracketing on the first pullback. -/
theorem pullbackCompIso_left_unit (A : QuotientCocycle G T) {S : CGWH.{u}} (g : S ⟶ T) :
    (pullbackCompIso A (𝟙 T) g).hom ≫ pullbackHom (pullbackIdIso A).hom g = 𝟙 (A.pullback g) := by
  apply hom_ext
  intro p
  let x := p.val.1
  let y := p.val.2
  let m := pullbackCompLift A (𝟙 T) g x
  exact comp_apply_left_unit (pullbackCompIso A (𝟙 T) g).hom (pullbackHom (pullbackIdIso A).hom g)
    x m y rfl p.property (A.transitionUnit x.val.1)

theorem pullbackCompIso_left_unit_with_identity (A : QuotientCocycle G T) {S : CGWH.{u}} (g : S ⟶ T) :
    (pullbackCompIso A (𝟙 T) g).hom ≫ pullbackHom (pullbackIdIso A).hom g ≫ 𝟙 (A.pullback g) =
      𝟙 (A.pullback g) := by
  have h := congrArg ((pullbackCompIso A (𝟙 T) g).hom ≫ ·)
    (Category.comp_id (pullbackHom (pullbackIdIso A).hom g))
  exact h.trans (pullbackCompIso_left_unit A g)

/-- The identity comparison cancels rebracketing on the second pullback. -/
theorem pullbackCompIso_right_unit (A : QuotientCocycle G T) {S : CGWH.{u}} (g : S ⟶ T) :
    (pullbackCompIso A g (𝟙 S)).hom ≫ (pullbackIdIso (A.pullback g)).hom = 𝟙 (A.pullback g) := by
  apply hom_ext
  intro p
  let x := p.val.1
  let y := p.val.2
  let m := pullbackCompLift A g (𝟙 S) x
  exact comp_apply_left_unit (pullbackCompIso A g (𝟙 S)).hom (pullbackIdIso (A.pullback g)).hom
    x m y rfl p.property (A.transitionUnit x.val.1)

/-- The two rebracketings of a threefold pullback agree. -/
theorem pullbackCompIso_assoc (A : QuotientCocycle G T) {Q R S : CGWH.{u}}
    (g : S ⟶ T) (h : R ⟶ S) (k : Q ⟶ R) :
    (pullbackCompIso A (h ≫ g) k).hom ≫ pullbackHom (pullbackCompIso A g h).hom k =
      (pullbackCompIso A g (k ≫ h)).hom ≫ (pullbackCompIso (A.pullback g) h k).hom := by
  apply hom_ext
  intro p
  let x := p.val.1
  let y := p.val.2
  let m := pullbackCompLift A (h ≫ g) k x
  let n := pullbackCompLift A g (k ≫ h) x
  exact (comp_apply_left_unit (pullbackCompIso A (h ≫ g) k).hom (pullbackHom (pullbackCompIso A g h).hom k)
    x m y rfl p.property (A.transitionUnit x.val.1)).trans
    (comp_apply_left_unit (pullbackCompIso A g (k ≫ h)).hom (pullbackCompIso (A.pullback g) h k).hom
      x n y rfl p.property (A.transitionUnit x.val.1)).symm

/-- The inverse rebracketing comparison also evaluates to the transition
on the original cover. -/
theorem pullbackCompIso_inv_apply (A : QuotientCocycle G T) {R S : CGWH.{u}} (g : S ⟶ T) (h : R ⟶ S)
    (p : CGWH.FibreSubspace ((A.pullback g).pullback h).cover (A.pullback (h ≫ g)).cover) :
    (pullbackCompIso A g h).inv.val.val p = A.transition ⟨(p.val.1.val.1.val.1,p.val.2.val.1),
      p.val.1.val.1.property.trans ((congrArg g.hom p.val.1.property).trans
        ((congrArg (h ≫ g).hom p.property).trans p.val.2.property.symm))⟩ := by
  let e := pullbackCompIso A g h
  let y := p.val.1
  let z := p.val.2
  let x : (A.pullback (h ≫ g)).coverSpace.obj := ⟨(y.val.1.val.1,y.val.2),
    y.val.1.property.trans (congrArg g.hom y.property)⟩
  let q : CGWH.FibreSubspace (A.pullback (h ≫ g)).cover (A.pullback (h ≫ g)).cover := ⟨(x,z),p.property⟩
  exact (comp_apply_left_unit e.hom e.inv x y z rfl p.property
    (A.transitionUnit x.val.1)).symm.trans
    (congrArg (fun r : A.pullback (h ≫ g) ⟶ A.pullback (h ≫ g) ↦ r.val.val q) e.hom_inv_id)

/-- Rebracketed pullback of a morphism between two pullbacks. -/
noncomputable def pullbackRebracketHom {T' R S : CGWH.{u}} {A : QuotientCocycle G T} {B : QuotientCocycle G T'}
    (g : S ⟶ T) (h : S ⟶ T') (r : A.pullback g ⟶ B.pullback h) (k : R ⟶ S) :
    A.pullback (k ≫ g) ⟶ B.pullback (k ≫ h) :=
  (pullbackCompIso A g k).hom ≫ pullbackHom r k ≫ (pullbackCompIso B h k).inv

/-- Rebracketing a pulled-back morphism changes only its base point. -/
theorem pullbackRebracketHom_apply {T' R S : CGWH.{u}} {A : QuotientCocycle G T} {B : QuotientCocycle G T'}
    (g : S ⟶ T) (h : S ⟶ T') (r : A.pullback g ⟶ B.pullback h) (k : R ⟶ S)
    (p : CGWH.FibreSubspace (A.pullback (k ≫ g)).cover (B.pullback (k ≫ h)).cover) :
    (pullbackRebracketHom g h r k).val.val p =
      r.val.val ⟨(⟨(p.val.1.val.1,k.hom p.val.1.val.2),p.val.1.property⟩,
        ⟨(p.val.2.val.1,k.hom p.val.2.val.2),p.val.2.property⟩),congrArg k.hom p.property⟩ := by
  let x := p.val.1
  let y := p.val.2
  let x' := pullbackCompLift A g k x
  let y' := pullbackCompLift B h k y
  let r' := pullbackHom r k
  let e := pullbackCompIso B h k
  exact (comp_apply_left_unit (pullbackCompIso A g k).hom (r' ≫ e.inv) x x' y rfl p.property
    (A.transitionUnit x.val.1)).trans
    (comp_apply_right_unit r' e.inv x' y' y p.property rfl
      ((pullbackCompIso_inv_apply B h k ⟨(y',y),rfl⟩).trans (B.transitionUnit y.val.1)))

section MorphismDescent

variable {S : CGWH.{u}}

/-- A point of the base change of the common cover gives a point of the
common cover of the two pulled-back presentations. -/
def mixedPullbackLift (A B : QuotientCocycle G T) (g : S ⟶ T) :
    C(CGWH.FibreSubspace g (baseOfMixed A B),
      CGWH.FibreSubspace (A.pullback g).cover (B.pullback g).cover) := by
  let W := CGWH.FibreSubspace g (baseOfMixed A B)
  letI : CompactlyGeneratedSpace W := closed_compactlyGenerated (CGWH.fibreSubspace_isClosed g (baseOfMixed A B))
  let s : C(W,S.obj) := ⟨fun w ↦ w.val.1, continuous_fst.comp
    (continuous_Kelley_forget.comp continuous_subtype_val)⟩
  let p : C(W,CGWH.FibreSubspace A.cover B.cover) := ⟨fun w ↦ w.val.2, continuous_snd.comp
    (continuous_Kelley_forget.comp continuous_subtype_val)⟩
  let l := (fibreOne A B).comp p
  let r := (fibreTwo A B).comp p
  have hl (w : W) : A.cover.hom (l w) = g.hom (s w) := w.property.symm
  have hr (w : W) : B.cover.hom (r w) = g.hom (s w) :=
    (p w).property.symm.trans (hl w)
  let L : C(W,(A.pullback g).coverSpace.obj) :=
    ⟨fun w ↦ ⟨(l w,s w),hl w⟩, (kelleyPair l s).continuous.subtype_mk hl⟩
  let R : C(W,(B.pullback g).coverSpace.obj) :=
    ⟨fun w ↦ ⟨(r w,s w),hr w⟩, (kelleyPair r s).continuous.subtype_mk hr⟩
  exact ⟨fun w ↦ ⟨(L w,R w),rfl⟩, (kelleyPair L R).continuous.subtype_mk (fun _ ↦ rfl)⟩

/-- The lifted pair forgets back to the original pair of presenting points. -/
theorem mixedPullback_lift (A B : QuotientCocycle G T) (g : S ⟶ T)
    (w : CGWH.FibreSubspace g (baseOfMixed A B)) :
    mixedPullback A B g (mixedPullbackLift A B g w) = w.val.2 := Subtype.ext rfl

/-- A pair on the local common cover is recovered from its two global
presenting points and its common base-change point. -/
theorem mixedPullbackLift_recovers (A B : QuotientCocycle G T) (g : S ⟶ T)
    (p : CGWH.FibreSubspace (A.pullback g).cover (B.pullback g).cover) :
    mixedPullbackLift A B g ⟨(p.val.1.val.2,mixedPullback A B g p),p.val.1.property.symm⟩ = p := by
  apply Subtype.ext
  exact Prod.ext (Subtype.ext rfl) (Subtype.ext (Prod.ext rfl p.property))

private theorem mixedPullback_quotient (A B : QuotientCocycle G T) (g : S ⟶ T)
    (hg : IsQuotientMap g.hom) : IsQuotientMap (mixedPullback A B g) := by
  apply IsQuotientMap.of_comp (mixedPullbackLift A B g).continuous (mixedPullback A B g).continuous
  have he : mixedPullback A B g ∘ mixedPullbackLift A B g = fun w ↦ w.val.2 :=
    funext (mixedPullback_lift A B g)
  have hq := CGWH.quotient_baseChange g (baseOfMixed A B) hg
  rwa [he]

/-- A quotient cover detects equality of cocycle morphisms. -/
theorem pullbackFunctor_faithful_of_quotient (g : S ⟶ T) (hg : IsQuotientMap g.hom) :
    (pullbackFunctor (G := G) g).Faithful where
  map_injective {A B} {r s} h := by
    apply Subtype.ext
    apply Subtype.ext
    apply ContinuousMap.ext
    intro x
    obtain ⟨y, rfl⟩ := (mixedPullback_quotient A B g hg).surjective x
    exact congrArg (fun w : (A.pullback g).Hom (B.pullback g) ↦ w.val.val y) h

/-- A compatible arrow over a quotient cover descends uniquely when its
underlying arrow family agrees on overlaps. -/
theorem existsUnique_pullbackHom_of_overlap {A B : QuotientCocycle G T}
    (g : S ⟶ T) (hg : IsQuotientMap g.hom) (r : (A.pullback g).Hom (B.pullback g))
    (hr : ∀ p q, mixedPullback A B g p = mixedPullback A B g q → r.val.val p = r.val.val q) :
    ∃! u : A.Hom B, pullbackHom u g = r := by
  classical
  let k := mixedPullback A B g
  have hk : IsQuotientMap k := mixedPullback_quotient A B g hg
  let j (p : CGWH.FibreSubspace A.cover B.cover) := (hk.surjective p).choose
  have hj (p : CGWH.FibreSubspace A.cover B.cover) : k (j p) = p := (hk.surjective p).choose_spec
  let d (p : CGWH.FibreSubspace A.cover B.cover) := r.val.val (j p)
  have he (x : CGWH.FibreSubspace (A.pullback g).cover (B.pullback g).cover) :
      d (k x) = r.val.val x := hr _ _ (hj (k x))
  have hd : Continuous d := hk.continuous_iff.mpr (r.val.val.continuous.congr (fun x ↦ (he x).symm))
  have hs (p : CGWH.FibreSubspace A.cover B.cover) : G.source (d p) = A.point p.val.1 := by
    obtain ⟨x,rfl⟩ := hk.surjective p
    exact (congrArg G.source (he x)).trans (r.val.property.1 x)
  have ht (p : CGWH.FibreSubspace A.cover B.cover) : G.target (d p) = B.point p.val.2 := by
    obtain ⟨x,rfl⟩ := hk.surjective p
    exact (congrArg G.target (he x)).trans (r.val.property.2 x)
  let D : firstPoint A B ⟶ secondPoint A B := ⟨⟨d,hd⟩, hs, ht⟩
  have hArrow (x : CGWH.FibreSubspace (A.pullback g).cover (B.pullback g).cover) :
      arrowAt (A := A) (B := B) D (k x) =
        arrowAt (A := A.pullback g) (B := B.pullback g) r.val x :=
    Subtype.ext (he x)
  let u : A.Hom B := ⟨D, by
    intro p q hp hq
    obtain ⟨s,hs⟩ := hg.surjective (A.cover.hom p.val.1)
    let p' : CGWH.FibreSubspace (A.pullback g).cover (B.pullback g).cover :=
      ⟨(⟨(p.val.1,s),hs.symm⟩,⟨(p.val.2,s),p.property.symm.trans hs.symm⟩),rfl⟩
    let q' : CGWH.FibreSubspace (A.pullback g).cover (B.pullback g).cover :=
      ⟨(⟨(q.val.1,s),hp.symm.trans hs.symm⟩,
        ⟨(q.val.2,s),hq.symm.trans (p.property.symm.trans hs.symm)⟩),rfl⟩
    let a := A.step p.val.1 q.val.1 hp
    let b := B.step p.val.2 q.val.2 hq
    exact (congrArg (fun v ↦ @CategoryStruct.comp G.Underlying _ _ _ _ a v) (hArrow q')).trans
      ((r.property p' q' rfl rfl).trans
        (congrArg (fun v ↦ @CategoryStruct.comp G.Underlying _ _ _ _ v b) (hArrow p').symm))⟩
  have hu : pullbackHom u g = r := by
    apply Subtype.ext
    apply Subtype.ext
    exact ContinuousMap.ext he
  refine ⟨u,hu,?_⟩
  intro v hv
  exact (pullbackFunctor_faithful_of_quotient (G := G) g hg).map_injective (hv.trans hu.symm)

/-- The exact overlap criterion for descent of cocycle morphisms. -/
theorem pullbackHom_descends_iff_overlap {A B : QuotientCocycle G T}
    (g : S ⟶ T) (hg : IsQuotientMap g.hom) (r : (A.pullback g).Hom (B.pullback g)) :
    (∃! u : A.Hom B, pullbackHom u g = r) ↔
      ∀ p q, mixedPullback A B g p = mixedPullback A B g q → r.val.val p = r.val.val q := by
  refine ⟨?_, existsUnique_pullbackHom_of_overlap g hg r⟩
  rintro ⟨u,rfl,_⟩ p q hpq
  exact congrArg u.val.val hpq

end MorphismDescent

section PairOverlap

variable {Y Y' : CGWH.{u}}

/-- The CGWH overlap of two maps to a common base. -/
def pairOverlap (f : Y ⟶ T) (g : Y' ⟶ T) : CGWH.{u} :=
  CGWH.of (X := CGWH.FibreSubspace f g) (CGWH.fibreSubspace_weaklyHausdorff f g)

/-- The first projection of the CGWH overlap. -/
def pairOverlapFirst (f : Y ⟶ T) (g : Y' ⟶ T) : pairOverlap f g ⟶ Y :=
  CGWH.map ⟨fun (p : CGWH.FibreSubspace f g) ↦ p.val.1,
    continuous_fst.comp (continuous_Kelley_forget.comp continuous_subtype_val)⟩

/-- The second projection of the CGWH overlap. -/
def pairOverlapSecond (f : Y ⟶ T) (g : Y' ⟶ T) : pairOverlap f g ⟶ Y' :=
  CGWH.map ⟨fun (p : CGWH.FibreSubspace f g) ↦ p.val.2,
    continuous_snd.comp (continuous_Kelley_forget.comp continuous_subtype_val)⟩

theorem pairOverlap_comm (f : Y ⟶ T) (g : Y' ⟶ T) :
    pairOverlapFirst f g ≫ f = pairOverlapSecond f g ≫ g := by
  apply CGWH.ext_hom
  exact fun p ↦ p.property

/-- An arrow between the two local cocycles restricted to the overlap. -/
abbrev PairOverlapHom (A : QuotientCocycle G Y) (B : QuotientCocycle G Y')
    (f : Y ⟶ T) (g : Y' ⟶ T) :=
  (A.pullback (pairOverlapFirst f g)).Hom (B.pullback (pairOverlapSecond f g))

/-- The common presenting cover over the overlap, evaluated at two original
presenting points whose images in the base agree. -/
def pairOverlapSample (A : QuotientCocycle G Y) (B : QuotientCocycle G Y')
    (f : Y ⟶ T) (g : Y' ⟶ T)
    (x : A.coverSpace.obj) (y : B.coverSpace.obj)
    (h : (A.cover ≫ f).hom x = (B.cover ≫ g).hom y) :
    CGWH.FibreSubspace (A.pullback (pairOverlapFirst f g)).cover
      (B.pullback (pairOverlapSecond f g)).cover :=
  let z : CGWH.FibreSubspace f g := ⟨(A.cover.hom x,B.cover.hom y),h⟩
  ⟨(⟨(x,z),rfl⟩,⟨(y,z),rfl⟩),rfl⟩

/-- Evaluation of a pairwise overlap arrow on the original presenting points. -/
def pairOverlapValue (A : QuotientCocycle G Y) (B : QuotientCocycle G Y')
    (f : Y ⟶ T) (g : Y' ⟶ T) (r : A.PairOverlapHom B f g)
    (x : A.coverSpace.obj) (y : B.coverSpace.obj)
    (h : (A.cover ≫ f).hom x = (B.cover ≫ g).hom y) :
    G.UnderlyingArrow (A.point x) (B.point y) :=
  arrowAt (A := A.pullback (pairOverlapFirst f g)) (B := B.pullback (pairOverlapSecond f g))
    r.val (pairOverlapSample A B f g x y h)

/-- The pairwise overlap sample depends continuously on both presenting points. -/
def continuousPairOverlapSample (A : QuotientCocycle G Y) (B : QuotientCocycle G Y')
    (f : Y ⟶ T) (g : Y' ⟶ T) :
    C(CGWH.FibreSubspace (A.cover ≫ f) (B.cover ≫ g),
      CGWH.FibreSubspace (A.pullback (pairOverlapFirst f g)).cover
        (B.pullback (pairOverlapSecond f g)).cover) := by
  let P := CGWH.FibreSubspace (A.cover ≫ f) (B.cover ≫ g)
  letI : CompactlyGeneratedSpace P :=
    closed_compactlyGenerated (CGWH.fibreSubspace_isClosed (A.cover ≫ f) (B.cover ≫ g))
  let x : C(P,A.coverSpace.obj) := ⟨fun p ↦ p.val.1,
    continuous_fst.comp (continuous_Kelley_forget.comp continuous_subtype_val)⟩
  let y : C(P,B.coverSpace.obj) := ⟨fun p ↦ p.val.2,
    continuous_snd.comp (continuous_Kelley_forget.comp continuous_subtype_val)⟩
  let l := A.cover.hom.hom.hom.comp x
  let r := B.cover.hom.hom.hom.comp y
  have h (p : P) : f.hom (l p) = g.hom (r p) := p.property
  let z : C(P,CGWH.FibreSubspace f g) := ⟨fun p ↦ ⟨(l p,r p),h p⟩,
    (kelleyPair l r).continuous.subtype_mk h⟩
  let s : C(P,(A.pullback (pairOverlapFirst f g)).coverSpace.obj) :=
    ⟨fun p ↦ ⟨(x p,z p),rfl⟩, (kelleyPair x z).continuous.subtype_mk (fun _ ↦ rfl)⟩
  let t : C(P,(B.pullback (pairOverlapSecond f g)).coverSpace.obj) :=
    ⟨fun p ↦ ⟨(y p,z p),rfl⟩, (kelleyPair y z).continuous.subtype_mk (fun _ ↦ rfl)⟩
  exact ⟨fun p ↦ ⟨(s p,t p),rfl⟩,
    (kelleyPair s t).continuous.subtype_mk (fun _ ↦ rfl)⟩

/-- Every presenting point over the overlap comes from a unique compatible
pair of the original presenting points. -/
theorem continuousPairOverlapSample_bijective (A : QuotientCocycle G Y) (B : QuotientCocycle G Y')
    (f : Y ⟶ T) (g : Y' ⟶ T) : Bijective (continuousPairOverlapSample A B f g) := by
  constructor
  · intro p q h
    apply Subtype.ext
    exact Prod.ext (congrArg (fun w ↦ w.val.1.val.1) h) (congrArg (fun w ↦ w.val.2.val.1) h)
  · intro p
    let z := p.val.1.val.2
    have hl : A.cover.hom p.val.1.val.1 = z.val.1 := p.val.1.property
    have hr : B.cover.hom p.val.2.val.1 = z.val.2 :=
      p.val.2.property.trans (congrArg (fun w : CGWH.FibreSubspace f g ↦ w.val.2) p.property).symm
    have h : (A.cover ≫ f).hom p.val.1.val.1 = (B.cover ≫ g).hom p.val.2.val.1 :=
      (congrArg f.hom hl).trans (z.property.trans (congrArg g.hom hr).symm)
    refine ⟨⟨(p.val.1.val.1,p.val.2.val.1),h⟩,?_⟩
    have hz : (⟨(A.cover.hom p.val.1.val.1,B.cover.hom p.val.2.val.1),h⟩ :
        CGWH.FibreSubspace f g) = z := Subtype.ext (Prod.ext hl hr)
    exact Subtype.ext (Prod.ext (Subtype.ext (Prod.ext rfl hz))
      (Subtype.ext (Prod.ext rfl (hz.trans p.property))))

/-- The overlap arrows are determined by their evaluations on the two
original presenting covers. -/
theorem pairOverlapHom_ext {A : QuotientCocycle G Y} {B : QuotientCocycle G Y'}
    {f : Y ⟶ T} {g : Y' ⟶ T} {r s : A.PairOverlapHom B f g}
    (h : ∀ (p : CGWH.FibreSubspace (A.cover ≫ f) (B.cover ≫ g)),
      pairOverlapValue A B f g r p.val.1 p.val.2 p.property =
        pairOverlapValue A B f g s p.val.1 p.val.2 p.property) : r = s := by
  apply Subtype.ext
  apply Subtype.ext
  apply ContinuousMap.ext
  intro p
  obtain ⟨q,rfl⟩ := (continuousPairOverlapSample_bijective A B f g).2 p
  exact congrArg Subtype.val (h q)

private def coverMapOfHomeomorphicTest {S W : CGWH.{u}} (A : QuotientCocycle G Y)
    (d : S ⟶ Y) (a : W ⟶ Y) (e : W.obj ≃ₜ S.obj) (he : ∀ w, d.hom (e w) = a.hom w) :
    C((A.pullback d).coverSpace.obj,(A.pullback a).coverSpace.obj) := by
  let l := coverPullbackLeft A d
  let s : C((A.pullback d).coverSpace.obj,W.obj) :=
    (show C(S.obj,W.obj) from ⟨e.symm,e.symm.continuous⟩).comp (A.pullback d).cover.hom.hom.hom
  have hs (p : (A.pullback d).coverSpace.obj) : A.cover.hom (l p) = a.hom (s p) :=
    p.property.trans ((congrArg d.hom (e.apply_symm_apply p.val.2)).symm.trans (he (s p)))
  exact ⟨fun p ↦ ⟨(l p,s p),hs p⟩,(kelleyPair l s).continuous.subtype_mk _⟩

/-- A morphism over a homeomorphic test for a pairwise overlap gives an
actual overlap morphism. This allows the test for the overlap to be an
object of a chosen small site. -/
def pairOverlapHomOfHomeomorphicTest {W : CGWH.{u}} (A : QuotientCocycle G Y)
    (B : QuotientCocycle G Y') (f : Y ⟶ T) (g : Y' ⟶ T)
    (e : W.obj ≃ₜ (pairOverlap f g).obj) (a : W ⟶ Y) (b : W ⟶ Y')
    (ha : ∀ w, (e w).val.1 = a.hom w) (hb : ∀ w, (e w).val.2 = b.hom w)
    (r : A.pullback a ⟶ B.pullback b) : A.PairOverlapHom B f g := by
  let L := A.pullback (pairOverlapFirst f g)
  let R := B.pullback (pairOverlapSecond f g)
  let l := (coverMapOfHomeomorphicTest A (pairOverlapFirst f g) a e ha).comp (fibreOne L R)
  let s := (coverMapOfHomeomorphicTest B (pairOverlapSecond f g) b e hb).comp (fibreTwo L R)
  have hs (p : CGWH.FibreSubspace L.cover R.cover) :
      (A.pullback a).cover.hom (l p) = (B.pullback b).cover.hom (s p) :=
    congrArg e.symm p.property
  let k : C(CGWH.FibreSubspace L.cover R.cover,
      CGWH.FibreSubspace (A.pullback a).cover (B.pullback b).cover) :=
    ⟨fun p ↦ ⟨(l p,s p),hs p⟩,(kelleyPair l s).continuous.subtype_mk hs⟩
  refine ⟨⟨r.val.val.comp k,fun p ↦ r.val.property.1 (k p),fun p ↦ r.val.property.2 (k p)⟩,?_⟩
  intro p q hp hq
  exact r.property (k p) (k q) (congrArg e.symm hp) (congrArg e.symm hq)

/-- Evaluation after changing the test space uses the same original
presenting points and the corresponding point of the new test. -/
theorem pairOverlapHomOfHomeomorphicTest_apply {W : CGWH.{u}} (A : QuotientCocycle G Y)
    (B : QuotientCocycle G Y') (f : Y ⟶ T) (g : Y' ⟶ T)
    (e : W.obj ≃ₜ (pairOverlap f g).obj) (a : W ⟶ Y) (b : W ⟶ Y')
    (ha : ∀ w, (e w).val.1 = a.hom w) (hb : ∀ w, (e w).val.2 = b.hom w)
    (r : A.pullback a ⟶ B.pullback b) (w : W.obj) (x : A.coverSpace.obj) (y : B.coverSpace.obj)
    (hx : A.cover.hom x = a.hom w) (hy : B.cover.hom y = b.hom w)
    (h : (A.cover ≫ f).hom x = (B.cover ≫ g).hom y) :
    (pairOverlapValue A B f g (pairOverlapHomOfHomeomorphicTest A B f g e a b ha hb r) x y h).val =
      r.val.val ⟨(⟨(x,w),hx⟩,⟨(y,w),hy⟩),rfl⟩ := by
  let p : CGWH.FibreSubspace f g := ⟨(A.cover.hom x,B.cover.hom y),h⟩
  have he : e w = p := Subtype.ext (Prod.ext ((ha w).trans hx.symm) ((hb w).trans hy.symm))
  have hwp : e.symm p = w := (congrArg e.symm he).symm.trans (e.symm_apply_apply w)
  apply congrArg r.val.val
  apply Subtype.ext
  exact Prod.ext (Subtype.ext (Prod.ext rfl hwp)) (Subtype.ext (Prod.ext rfl hwp))

end PairOverlap

section ObjectDescent

variable {Y : CGWH.{u}}

private abbrev coverOverlap (q : Y ⟶ T) := pairOverlap q q
private abbrev coverOverlapFirst (q : Y ⟶ T) := pairOverlapFirst q q
private abbrev coverOverlapSecond (q : Y ⟶ T) := pairOverlapSecond q q

/-- An overlap arrow between the two copies of a presentation pulled back
from the cover. All such arrows are isomorphisms. -/
abbrev OverlapHom (A : QuotientCocycle G Y) (q : Y ⟶ T) := A.PairOverlapHom A q q

private abbrev overlapSample (A : QuotientCocycle G Y) (q : Y ⟶ T) :=
  pairOverlapSample A A q q

/-- Evaluate the overlap arrow using two points of the presenting cover. -/
abbrev overlapValue (A : QuotientCocycle G Y) (q : Y ⟶ T) (r : A.OverlapHom q) :=
  pairOverlapValue A A q q r

private abbrev continuousOverlapSample (A : QuotientCocycle G Y) (q : Y ⟶ T) :=
  continuousPairOverlapSample A A q q

/-- Normalization and the triple-overlap condition, evaluated on points of
the presenting cover. -/
structure OverlapDescent (A : QuotientCocycle G Y) (q : Y ⟶ T)
    (r : A.OverlapHom q) : Prop where
  unit : ∀ x : A.coverSpace.obj, overlapValue A q r x x rfl =
    @CategoryStruct.id G.Underlying _ (A.point x)
  comp : ∀ (x y z : A.coverSpace.obj)
      (hxy : (A.cover ≫ q).hom x = (A.cover ≫ q).hom y)
      (hyz : (A.cover ≫ q).hom y = (A.cover ≫ q).hom z),
    @CategoryStruct.comp G.Underlying _ _ _ _ (overlapValue A q r x y hxy)
      (overlapValue A q r y z hyz) = overlapValue A q r x z (hxy.trans hyz)

private theorem overlapValue_eq_original_step (A : QuotientCocycle G Y) (q : Y ⟶ T)
    (r : A.OverlapHom q) (hr : OverlapDescent A q r) (x y : A.coverSpace.obj)
    (h : A.cover.hom x = A.cover.hom y) :
    overlapValue A q r x y (congrArg q.hom h) = A.step x y h := by
  let p := overlapSample A q x x rfl
  let p' := overlapSample A q x y (congrArg q.hom h)
  have hbase : (A.pullback (coverOverlapSecond q)).cover.hom p.val.2 =
      (A.pullback (coverOverlapSecond q)).cover.hom p'.val.2 :=
    Subtype.ext (Prod.ext rfl h)
  have hleft : (A.pullback (coverOverlapFirst q)).step p.val.1 p'.val.1
      (show (A.pullback (coverOverlapFirst q)).cover.hom p.val.1 =
        (A.pullback (coverOverlapFirst q)).cover.hom p'.val.1 from hbase) =
      @CategoryStruct.id G.Underlying _ (A.point x) :=
    step_unit A x
  have hcompat := r.property p p' hbase hbase
  let v := overlapValue A q r x y (congrArg q.hom h)
  let u := overlapValue A q r x x rfl
  let w := A.step x y h
  have hcomp : @CategoryStruct.comp G.Underlying _ _ _ _
      ((A.pullback (coverOverlapFirst q)).step p.val.1 p'.val.1 hbase) v =
      @CategoryStruct.comp G.Underlying _ _ _ _ u w := hcompat
  exact (@Category.id_comp G.Underlying _ _ _ v).symm.trans
    ((congrArg (fun j ↦ @CategoryStruct.comp G.Underlying _ _ _ _ j v) hleft.symm).trans
      (hcomp.trans ((congrArg (fun j ↦ @CategoryStruct.comp G.Underlying _ _ _ _ j w) (hr.unit x)).trans
        (@Category.id_comp G.Underlying _ _ _ w))))

/-- On one domain the overlap arrow gives back the local transition. -/
theorem overlapValue_eq_transition (A : QuotientCocycle G Y) (q : Y ⟶ T)
    (r : A.OverlapHom q) (hr : OverlapDescent A q r) (x y : A.coverSpace.obj)
    (h : A.cover.hom x = A.cover.hom y) :
    (overlapValue A q r x y (congrArg q.hom h)).val = A.transition ⟨(x,y),h⟩ :=
  congrArg Subtype.val (overlapValue_eq_original_step A q r hr x y h)

/-- Reconstruct a cocycle on the composite cover from the overlap
isomorphism of a cocycle presentation. -/
def descendObject (A : QuotientCocycle G Y) (q : Y ⟶ T) (hq : IsQuotientMap q.hom)
    (r : A.OverlapHom q) (hr : OverlapDescent A q r) : QuotientCocycle G T where
  coverSpace := A.coverSpace
  cover := A.cover ≫ q
  isCover := hq.comp A.isCover
  point := A.point
  transition := r.val.val.comp (continuousOverlapSample A q)
  transitionSource p := (overlapValue A q r p.val.1 p.val.2 p.property).property.1
  transitionTarget p := (overlapValue A q r p.val.1 p.val.2 p.property).property.2
  transitionUnit x := congrArg Subtype.val (hr.unit x)
  transitionComp x y z hxy hyz := congrArg Subtype.val (hr.comp x y z hxy hyz)

/-- The reconstructed transitions recover the entire overlap arrow. -/
theorem descendObject_recovers_overlap (A : QuotientCocycle G Y) (q : Y ⟶ T)
    (hq : IsQuotientMap q.hom) (r : A.OverlapHom q) (hr : OverlapDescent A q r)
    (p : CGWH.FibreSubspace (A.pullback (coverOverlapFirst q)).cover
      (A.pullback (coverOverlapSecond q)).cover) :
    ∃ h : (A.cover ≫ q).hom p.val.1.val.1 = (A.cover ≫ q).hom p.val.2.val.1,
      (A.descendObject q hq r hr).transition ⟨(p.val.1.val.1,p.val.2.val.1),h⟩ =
        r.val.val p := by
  let x := p.val.1.val.1
  let y := p.val.2.val.1
  let z := p.val.1.val.2
  have h₁ : A.cover.hom x = z.val.1 := p.val.1.property
  have hz : z = p.val.2.val.2 := p.property
  have h₂ : A.cover.hom y = z.val.2 :=
    p.val.2.property.trans (congrArg (fun w : CGWH.FibreSubspace q q ↦ w.val.2) hz).symm
  have h : (A.cover ≫ q).hom x = (A.cover ≫ q).hom y :=
    (congrArg q.hom h₁).trans (z.property.trans (congrArg q.hom h₂).symm)
  have hs : overlapSample A q x y h = p := by
    have ht : (⟨(A.cover.hom x,A.cover.hom y),h⟩ : CGWH.FibreSubspace q q) = z :=
      Subtype.ext (Prod.ext h₁ h₂)
    exact Subtype.ext (Prod.ext (Subtype.ext (Prod.ext rfl ht))
      (Subtype.ext (Prod.ext rfl (ht.trans hz))))
  exact ⟨h,congrArg r.val.val hs⟩

/-- Effective descent of a cocycle object along a single quotient cover.
The reconstruction restricts to the original local object. -/
theorem descendObject_pullback_iso (A : QuotientCocycle G Y)
    (q : Y ⟶ T) (hq : IsQuotientMap q.hom) (r : A.OverlapHom q) (hr : OverlapDescent A q r) :
    Nonempty (A ≅ (A.descendObject q hq r hr).pullback q) := by
  let B := A.descendObject q hq r hr
  let C := B.pullback q
  let k : C(A.coverSpace.obj,C.coverSpace.obj) :=
    ⟨fun x ↦ ⟨(x,A.cover.hom x),rfl⟩,
      (kelleyPair (ContinuousMap.id _) A.cover.hom.hom.hom).continuous.subtype_mk (fun _ ↦ rfl)⟩
  refine iso_of_cover_map C A k (fun _ ↦ rfl) (fun _ ↦ rfl) ?_
  intro x y h
  exact (congrArg Subtype.val (overlapValue_eq_original_step A q r hr x y h)).symm

/-- A global cocycle supplies a canonical overlap arrow after restriction. -/
def overlapOfGlobal (B : QuotientCocycle G T) (q : Y ⟶ T) : (B.pullback q).OverlapHom q := by
  let A := B.pullback q
  let L := A.pullback (coverOverlapFirst q)
  let R := A.pullback (coverOverlapSecond q)
  let P := CGWH.FibreSubspace L.cover R.cover
  let l := (coverPullbackLeft B q).comp ((coverPullbackLeft A (coverOverlapFirst q)).comp (fibreOne L R))
  let r := (coverPullbackLeft B q).comp ((coverPullbackLeft A (coverOverlapSecond q)).comp (fibreTwo L R))
  have hl (p : P) : B.cover.hom (l p) = q.hom p.val.1.val.2.val.1 :=
    p.val.1.val.1.property.trans (congrArg q.hom p.val.1.property)
  have hr (p : P) : B.cover.hom (r p) = q.hom p.val.1.val.2.val.2 := by
    have hx : p.val.1.val.2 = p.val.2.val.2 := p.property
    exact (p.val.2.val.1.property.trans (congrArg q.hom p.val.2.property)).trans
      (congrArg (fun z : CGWH.FibreSubspace q q ↦ q.hom z.val.2) hx).symm
  have h (p : P) : B.cover.hom (l p) = B.cover.hom (r p) :=
    (hl p).trans (p.val.1.val.2.property.trans (hr p).symm)
  let M : C(P,CGWH.FibreSubspace B.cover B.cover) :=
    ⟨fun p ↦ ⟨(l p,r p),h p⟩, (kelleyPair l r).continuous.subtype_mk h⟩
  refine ⟨⟨B.transition.comp M, fun p ↦ B.transitionSource (M p),
    fun p ↦ B.transitionTarget (M p)⟩, ?_⟩
  intro p p' hl' hr'
  have hL : B.cover.hom (l p) = B.cover.hom (l p') :=
    (hl p).trans ((congrArg (fun z : CGWH.FibreSubspace q q ↦ q.hom z.val.1) hl').trans
      (hl p').symm)
  have hR : B.cover.hom (r p) = B.cover.hom (r p') := by
    have hx : p.val.1.val.2 = p'.val.1.val.2 := hl'
    exact (hr p).trans ((congrArg (fun z : CGWH.FibreSubspace q q ↦ q.hom z.val.2) hx).trans
      (hr p').symm)
  exact (step_comp B (l p) (l p') (r p') hL (h p')).trans
    (step_comp B (l p) (r p) (r p') (h p) hR).symm

/-- The canonical overlap arrow of a restriction satisfies unit and
triple-overlap compatibility. -/
theorem overlapOfGlobal_descent (B : QuotientCocycle G T) (q : Y ⟶ T) :
    OverlapDescent (B.pullback q) q (B.overlapOfGlobal q) where
  unit x := step_unit B x.val.1
  comp x y z hxy hyz :=
    step_comp B x.val.1 y.val.1 z.val.1
      (x.property.trans (hxy.trans y.property.symm))
      (y.property.trans (hyz.trans z.property.symm))

/-- Reconstruction from the canonical descent datum is isomorphic to the
global object that supplied it. -/
theorem descendObject_of_global_iso (B : QuotientCocycle G T) (q : Y ⟶ T)
    (hq : IsQuotientMap q.hom) :
    Nonempty ((B.pullback q).descendObject q hq (B.overlapOfGlobal q)
      (B.overlapOfGlobal_descent q) ≅ B) :=
  iso_of_cover_map B _ (coverPullbackLeft B q) (fun x ↦ x.property)
    (fun _ ↦ rfl) (fun _ _ _ ↦ rfl)

/-- A local morphism commutes with the descent isomorphisms when its
values commute with the two overlap arrows. -/
def OverlapHomCompatible {A B : QuotientCocycle G Y} (q : Y ⟶ T)
    (r : A.OverlapHom q) (s : B.OverlapHom q) (a : A.Hom B) : Prop :=
  ∀ (p p' : CGWH.FibreSubspace A.cover B.cover)
    (h : (A.cover ≫ q).hom p.val.1 = (A.cover ≫ q).hom p'.val.1),
    @CategoryStruct.comp G.Underlying _ _ _ _
      (overlapValue A q r p.val.1 p'.val.1 h) (arrowAt (A := A) (B := B) a.val p') =
      @CategoryStruct.comp G.Underlying _ _ _ _ (arrowAt (A := A) (B := B) a.val p)
        (overlapValue B q s p.val.2 p'.val.2
          ((congrArg q.hom p.property).symm.trans (h.trans (congrArg q.hom p'.property))))

/-- A morphism respecting the overlap arrows extends to the reconstructed
objects. Its values on the original common cover are preserved. -/
theorem descendHom_exists {A B : QuotientCocycle G Y} (q : Y ⟶ T) (hq : IsQuotientMap q.hom)
    (r : A.OverlapHom q) (s : B.OverlapHom q) (hr : OverlapDescent A q r) (hs : OverlapDescent B q s)
    (a : A.Hom B) (ha : OverlapHomCompatible q r s a) :
    ∃ u : (A.descendObject q hq r hr).Hom (B.descendObject q hq s hs),
      ∀ p : CGWH.FibreSubspace A.cover B.cover,
        u.val.val ⟨p.val,congrArg q.hom p.property⟩ = a.val.val p := by
  classical
  let D := A.descendObject q hq r hr
  let E := B.descendObject q hq s hs
  let P := CGWH.FibreSubspace D.cover E.cover
  let J := mixedTest D E
  let b : J ⟶ Y := CGWH.map (A.cover.hom.hom.hom.comp (fibreOne D E))
  let W := CGWH.FibreSubspace B.cover b
  letI : CompactlyGeneratedSpace W :=
    closed_compactlyGenerated (CGWH.fibreSubspace_isClosed B.cover b)
  let p : C(W,P) := ⟨fun w ↦ w.val.2,
    continuous_snd.comp (continuous_Kelley_forget.comp continuous_subtype_val)⟩
  let m : C(W,B.coverSpace.obj) := ⟨fun w ↦ w.val.1,
    continuous_fst.comp (continuous_Kelley_forget.comp continuous_subtype_val)⟩
  let L := (fibreOne D E).comp p
  let R := (fibreTwo D E).comp p
  have hl (w : W) : A.cover.hom (L w) = B.cover.hom (m w) := w.property.symm
  have ht (w : W) : E.cover.hom (m w) = E.cover.hom (R w) :=
    (congrArg q.hom w.property).trans (p w).property
  let l : C(W,CGWH.FibreSubspace A.cover B.cover) :=
    ⟨fun w ↦ ⟨(L w,m w),hl w⟩, (kelleyPair L m).continuous.subtype_mk hl⟩
  let v : C(W,CGWH.FibreSubspace E.cover E.cover) :=
    ⟨fun w ↦ ⟨(m w,R w),ht w⟩, (kelleyPair m R).continuous.subtype_mk ht⟩
  let C := G.composeMaps (a.val.val.comp l) (E.transition.comp v) (fun w ↦
    (a.val.property.2 (l w)).trans (E.transitionSource (v w)).symm)
  have hp : IsQuotientMap p := CGWH.quotient_baseChange B.cover b B.isCover
  have hC (w w' : W) (he : p w = p w') : C w = C w' := by
    rcases w with ⟨⟨y,z⟩,h₁⟩
    rcases w' with ⟨⟨y',z'⟩,h₂⟩
    change z = z' at he
    subst z'
    let w : W := ⟨(y,z),h₁⟩
    let w' : W := ⟨(y',z),h₂⟩
    have hyy : B.cover.hom y = B.cover.hom y' := h₁.trans h₂.symm
    let a₀ := arrowAt (A := A) (B := B) a.val (l w)
    let a₁ := arrowAt (A := A) (B := B) a.val (l w')
    let j := B.step y y' hyy
    let e₀ := E.step y z.val.2 (ht w)
    let e₁ := E.step y' z.val.2 (ht w')
    have ha' : a₁ = @CategoryStruct.comp G.Underlying _ _ _ _ a₀ j := by
      have h := a.property (l w) (l w') rfl hyy
      exact (@Category.id_comp G.Underlying _ _ _ a₁).symm.trans
        ((congrArg (fun v ↦ @CategoryStruct.comp G.Underlying _ _ _ _ v a₁)
          (step_unit A z.val.1).symm).trans h)
    have hj : E.step y y' (congrArg q.hom hyy) = j := overlapValue_eq_original_step B q s hs y y' hyy
    have hh : @CategoryStruct.comp G.Underlying _ _ _ _ j e₁ = e₀ :=
      (congrArg (fun v ↦ @CategoryStruct.comp G.Underlying _ _ _ _ v e₁) hj.symm).trans
        (step_comp E y y' z.val.2 (congrArg q.hom hyy) (ht w'))
    have eq : @CategoryStruct.comp G.Underlying _ _ _ _ a₀ e₀ =
        @CategoryStruct.comp G.Underlying _ _ _ _ a₁ e₁ :=
      (congrArg (fun v ↦ @CategoryStruct.comp G.Underlying _ _ _ _ a₀ v) hh.symm).trans
        ((@Category.assoc G.Underlying _ _ _ _ _ a₀ j e₁).symm.trans
          (congrArg (fun v ↦ @CategoryStruct.comp G.Underlying _ _ _ _ v e₁) ha'.symm))
    exact congrArg Subtype.val eq
  let pick (x : P) : W := (hp.surjective x).choose
  have hpick (x : P) : p (pick x) = x := (hp.surjective x).choose_spec
  let d (x : P) := C (pick x)
  have hd (w : W) : d (p w) = C w := hC _ _ (hpick _)
  have hcont : Continuous d := hp.continuous_iff.mpr (C.continuous.congr (fun w ↦ (hd w).symm))
  have hsrc (x : P) : G.source (d x) = D.point x.val.1 := by
    obtain ⟨w,rfl⟩ := hp.surjective x
    exact (congrArg G.source (hd w)).trans ((G.source_comp _).trans (a.val.property.1 (l w)))
  have htgt (x : P) : G.target (d x) = E.point x.val.2 := by
    obtain ⟨w,rfl⟩ := hp.surjective x
    exact (congrArg G.target (hd w)).trans ((G.target_comp _).trans (E.transitionTarget (v w)))
  let F : firstPoint D E ⟶ secondPoint D E := ⟨⟨d,hcont⟩,hsrc,htgt⟩
  have hF (w : W) : arrowAt (A := D) (B := E) F (p w) =
      @CategoryStruct.comp G.Underlying _ _ _ _
        (arrowAt (A := A) (B := B) a.val (l w)) (E.step (m w) (R w) (ht w)) :=
    Subtype.ext (hd w)
  refine ⟨⟨F,?_⟩,?_⟩
  · intro z z' hz hz'
    obtain ⟨w,rfl⟩ := hp.surjective z
    obtain ⟨w',rfl⟩ := hp.surjective z'
    let i := D.step (L w) (L w') hz
    let j := E.step (R w) (R w') hz'
    let k := E.step (m w) (m w')
      ((congrArg q.hom (hl w)).symm.trans (hz.trans (congrArg q.hom (hl w'))))
    let a₀ := arrowAt (A := A) (B := B) a.val (l w)
    let a₁ := arrowAt (A := A) (B := B) a.val (l w')
    let e₀ := E.step (m w) (R w) (ht w)
    let e₁ := E.step (m w') (R w') (ht w')
    have h₁ : @CategoryStruct.comp G.Underlying _ _ _ _ i a₁ =
        @CategoryStruct.comp G.Underlying _ _ _ _ a₀ k := ha (l w) (l w') hz
    have h₂ : @CategoryStruct.comp G.Underlying _ _ _ _ k e₁ =
        @CategoryStruct.comp G.Underlying _ _ _ _ e₀ j :=
      (step_comp E (m w) (m w') (R w') _ _).trans (step_comp E (m w) (R w) (R w') _ _).symm
    exact (congrArg (fun x ↦ @CategoryStruct.comp G.Underlying _ _ _ _ i x) (hF w')).trans
      ((@Category.assoc G.Underlying _ _ _ _ _ i a₁ e₁).symm.trans
        ((congrArg (fun x ↦ @CategoryStruct.comp G.Underlying _ _ _ _ x e₁) h₁).trans
          ((@Category.assoc G.Underlying _ _ _ _ _ a₀ k e₁).trans
            ((congrArg (fun x ↦ @CategoryStruct.comp G.Underlying _ _ _ _ a₀ x) h₂).trans
              ((@Category.assoc G.Underlying _ _ _ _ _ a₀ e₀ j).symm.trans
                (congrArg (fun x ↦ @CategoryStruct.comp G.Underlying _ _ _ _ x j) (hF w).symm))))))
  · intro z
    let w : W := ⟨(z.val.2,⟨z.val,congrArg q.hom z.property⟩),z.property.symm⟩
    have hh := hF w
    let a₀ := arrowAt (A := A) (B := B) a.val z
    exact congrArg Subtype.val (hh.trans
      ((congrArg (fun x ↦ @CategoryStruct.comp G.Underlying _ _ _ _ a₀ x)
        (step_unit E z.val.2)).trans (@Category.comp_id G.Underlying _ _ _ a₀)))

/-- The extension of a compatible local morphism is unique. -/
theorem descendHom_existsUnique {A B : QuotientCocycle G Y} (q : Y ⟶ T) (hq : IsQuotientMap q.hom)
    (r : A.OverlapHom q) (s : B.OverlapHom q) (hr : OverlapDescent A q r) (hs : OverlapDescent B q s)
    (a : A.Hom B) (ha : OverlapHomCompatible q r s a) :
    ∃! u : (A.descendObject q hq r hr).Hom (B.descendObject q hq s hs),
      ∀ p : CGWH.FibreSubspace A.cover B.cover,
        u.val.val ⟨p.val,congrArg q.hom p.property⟩ = a.val.val p := by
  obtain ⟨u,hu⟩ := descendHom_exists q hq r s hr hs a ha
  refine ⟨u,hu,?_⟩
  intro v hv
  apply Subtype.ext
  apply Subtype.ext
  apply ContinuousMap.ext
  intro p
  let D := A.descendObject q hq r hr
  let E := B.descendObject q hq s hs
  obtain ⟨y,hy⟩ := B.isCover.surjective (A.cover.hom p.val.1)
  let b : CGWH.FibreSubspace A.cover B.cover := ⟨(p.val.1,y),hy.symm⟩
  let c : CGWH.FibreSubspace D.cover E.cover := ⟨b.val,congrArg q.hom b.property⟩
  have h : E.cover.hom c.val.2 = E.cover.hom p.val.2 :=
    (congrArg q.hom hy).trans p.property
  let j := E.step c.val.2 p.val.2 h
  have hc (f : D.Hom E) : arrowAt (A := D) (B := E) f.val p =
      @CategoryStruct.comp G.Underlying _ _ _ _ (arrowAt (A := D) (B := E) f.val c) j :=
    (@Category.id_comp G.Underlying _ _ _ _).symm.trans
      ((congrArg (fun x ↦ @CategoryStruct.comp G.Underlying _ _ _ _ x _)
        (step_unit D p.val.1).symm).trans (f.property c p rfl h))
  have hcv : arrowAt (A := D) (B := E) v.val c = arrowAt (A := D) (B := E) u.val c :=
    Subtype.ext ((hv b).trans (hu b).symm)
  exact congrArg Subtype.val ((hc v).trans ((congrArg
    (fun x ↦ @CategoryStruct.comp G.Underlying _ _ _ _ x j) hcv).trans (hc u).symm))

end ObjectDescent


section InertiaComparison

private def coverDiagonal (A : QuotientCocycle G T) :
    C(A.coverSpace.obj, CGWH.FibreSubspace A.cover A.cover) :=
  ⟨fun x ↦ ⟨(x,x),rfl⟩,
    (kelleyPair (ContinuousMap.id _) (ContinuousMap.id _)).continuous.subtype_mk _⟩

private def loopAt {A : QuotientCocycle G T} (r : A ⟶ A) (x : A.coverSpace.obj) :
    G.UnderlyingArrow (A.point x) (A.point x) :=
  arrowAt r.val (A.coverDiagonal x)

private theorem loop_offDiagonal {A : QuotientCocycle G T} (r : A ⟶ A)
    (p : CGWH.FibreSubspace A.cover A.cover) :
    arrowAt r.val p =
      @CategoryStruct.comp G.Underlying _ _ _ _ (loopAt r p.val.1)
        (A.step p.val.1 p.val.2 p.property) := by
  have h := r.property (A.coverDiagonal p.val.1) p rfl p.property
  change @CategoryStruct.comp G.Underlying _ _ _ _
      (A.step p.val.1 p.val.1 rfl) (arrowAt r.val p) = _ at h
  rw [step_unit] at h
  exact (@Category.id_comp G.Underlying _ _ _ (arrowAt r.val p)).symm.trans h

private theorem loop_commutes_transition {A : QuotientCocycle G T} (r : A ⟶ A)
    (p : CGWH.FibreSubspace A.cover A.cover) :
    @CategoryStruct.comp G.Underlying _ _ _ _
      (A.step p.val.1 p.val.2 p.property) (loopAt r p.val.2) =
    @CategoryStruct.comp G.Underlying _ _ _ _
      (loopAt r p.val.1) (A.step p.val.1 p.val.2 p.property) := by
  have h := r.property p (A.coverDiagonal p.val.2) p.property rfl
  change _ = @CategoryStruct.comp G.Underlying _ _ _ _
      (arrowAt r.val p) (A.step p.val.2 p.val.2 rfl) at h
  rw [step_unit] at h
  exact h.trans ((@Category.comp_id G.Underlying _ _ _ (arrowAt r.val p)).trans (loop_offDiagonal r p))

private def presentingLoops {A : QuotientCocycle G T} (r : A ⟶ A) :
    C(A.coverSpace.obj, G.Inertia) :=
  ⟨fun x ↦ ⟨(loopAt r x).val, (loopAt r x).property.1.trans (loopAt r x).property.2.symm⟩,
    (r.val.val.continuous.comp A.coverDiagonal.continuous).subtype_mk _⟩

private def presentingInertiaTransitions {A : QuotientCocycle G T} (r : A ⟶ A) :
    C(CGWH.FibreSubspace A.cover A.cover, G.InertiaArrow) := by
  let p := (presentingLoops r).comp (fibreOne A A)
  letI : CompactlyGeneratedSpace (CGWH.FibreSubspace A.cover A.cover) :=
    closed_compactlyGenerated (CGWH.fibreSubspace_isClosed A.cover A.cover)
  exact ⟨fun x ↦ ⟨(A.transition x, p x),
    (A.transitionSource x).trans (loopAt r x.val.1).property.1.symm⟩,
    (kelleyPair A.transition p).continuous.subtype_mk _⟩

private theorem presentingInertiaTransitions_target {A : QuotientCocycle G T} (r : A ⟶ A)
    (p : CGWH.FibreSubspace A.cover A.cover) :
    G.inertiaGroupoid.target (presentingInertiaTransitions r p) = presentingLoops r p.val.2 := by
  apply (G.targetLoop_eq_iff _ _ ((A.transitionTarget p).trans
    (loopAt r p.val.2).property.1.symm)).mpr
  exact congrArg Subtype.val (loop_commutes_transition r p).symm

/-- A cocycle and a global automorphism give an actual cocycle in the
topological conjugation groupoid on the identical covering space. -/
def ofAutomorphism (A : QuotientCocycle G T) (r : A ≅ A) :
    QuotientCocycle G.inertiaGroupoid T where
  coverSpace := A.coverSpace
  cover := A.cover
  isCover := A.isCover
  point := presentingLoops r.hom
  transition := presentingInertiaTransitions r.hom
  transitionSource _ := rfl
  transitionTarget := presentingInertiaTransitions_target r.hom
  transitionUnit x := by
    apply Subtype.ext
    apply Prod.ext
    · change A.transition ⟨(x,x),rfl⟩ = G.unit (G.source (loopAt r.hom x).val)
      exact (A.transitionUnit x).trans (congrArg G.unit (loopAt r.hom x).property.1.symm)
    · rfl
  transitionComp x y z hxy hyz := Subtype.ext (Prod.ext (A.transitionComp x y z hxy hyz) rfl)

/-- The new inertia presentation projects to the given cocycle. -/
theorem ofAutomorphism_projects (A : QuotientCocycle G T) (r : A ≅ A) :
    (ofAutomorphism A r).map G.inertiaProjection = A := by
  refine cocycle_eq_of_fields (A := (ofAutomorphism A r).map G.inertiaProjection)
    (B := A) rfl (HEq.rfl) ?_ ?_
  · exact heq_of_eq (ContinuousMap.ext fun x ↦ (loopAt r.hom x).property.1)
  · exact heq_of_eq (ContinuousMap.ext fun _ ↦ rfl)


/-- A continuous family of loops on the presenting cover with the
conjugation law along transition arrows. -/
structure CoverLoop (A : QuotientCocycle G T) where
  arrows : C(A.coverSpace.obj, G.arrows.obj)
  source_eq : ∀ x, G.source (arrows x) = A.point x
  target_eq : ∀ x, G.target (arrows x) = A.point x
  commute (p : CGWH.FibreSubspace A.cover A.cover) :
    @CategoryStruct.comp G.Underlying _ _ _ _ (A.step p.val.1 p.val.2 p.property)
      (⟨arrows p.val.2, source_eq _, target_eq _⟩ :
        G.UnderlyingArrow (A.point p.val.2) (A.point p.val.2)) =
    @CategoryStruct.comp G.Underlying _ _ _ _
      (⟨arrows p.val.1, source_eq _, target_eq _⟩ :
        G.UnderlyingArrow (A.point p.val.1) (A.point p.val.1)) (A.step p.val.1 p.val.2 p.property)

private theorem CoverLoop.arrow_ext {A : QuotientCocycle G T} {r s : CoverLoop A}
    (h : r.arrows = s.arrows) : r = s := by
  cases r
  cases s
  cases h
  rfl

private def CoverLoop.atPoint {A : QuotientCocycle G T} (l : CoverLoop A) (x : A.coverSpace.obj) :
    G.UnderlyingArrow (A.point x) (A.point x) :=
  ⟨l.arrows x, l.source_eq x, l.target_eq x⟩

/-- An automorphism of a cocycle records its loop on the diagonal
of the cover. -/
def coverLoopOfHom {A : QuotientCocycle G T} (r : A ⟶ A) : CoverLoop A where
  arrows := r.val.val.comp A.coverDiagonal
  source_eq x := (loopAt r x).property.1
  target_eq x := (loopAt r x).property.2
  commute := loop_commutes_transition r

private def CoverLoop.toArrowFamily {A : QuotientCocycle G T} (l : CoverLoop A) :
    firstPoint A A ⟶ secondPoint A A := by
  let u := l.arrows.comp (fibreOne A A)
  let v := A.transition
  have hu (p : CGWH.FibreSubspace A.cover A.cover) : G.target (u p) = G.source (v p) :=
    (l.target_eq p.val.1).trans (A.transitionSource p).symm
  exact ⟨G.composeMaps u v hu,
    fun p ↦ (G.source_comp _).trans (l.source_eq p.val.1),
    fun p ↦ (G.target_comp _).trans (A.transitionTarget p)⟩

private theorem CoverLoop.toArrowFamily_at {A : QuotientCocycle G T} (l : CoverLoop A)
    (p : CGWH.FibreSubspace A.cover A.cover) :
    arrowAt l.toArrowFamily p =
      @CategoryStruct.comp G.Underlying _ _ _ _ (l.atPoint p.val.1)
        (A.step p.val.1 p.val.2 p.property) :=
  Subtype.ext rfl

/-- The conjugation law descends a continuous family of loops to an
automorphism of the quotient cocycle. -/
def CoverLoop.toHom {A : QuotientCocycle G T} (l : CoverLoop A) : A ⟶ A := by
  refine ⟨l.toArrowFamily, ?_⟩
  intro p q hp hq
  let a := A.step p.val.1 q.val.1 hp
  let b := A.step q.val.1 q.val.2 q.property
  let c := A.step p.val.1 p.val.2 p.property
  let d := A.step p.val.2 q.val.2 hq
  let x := l.atPoint p.val.1
  let y := l.atPoint q.val.1
  have hab : @CategoryStruct.comp G.Underlying _ _ _ _ a b =
      @CategoryStruct.comp G.Underlying _ _ _ _ c d :=
    (A.step_comp _ _ _ hp q.property).trans (A.step_comp _ _ _ p.property hq).symm
  have hc : @CategoryStruct.comp G.Underlying _ _ _ _ a y =
      @CategoryStruct.comp G.Underlying _ _ _ _ x a :=
    l.commute ⟨(p.val.1,q.val.1),hp⟩
  rw [l.toArrowFamily_at, l.toArrowFamily_at]
  change @CategoryStruct.comp G.Underlying _ _ _ _ a
      (@CategoryStruct.comp G.Underlying _ _ _ _ y b) =
    @CategoryStruct.comp G.Underlying _ _ _ _
      (@CategoryStruct.comp G.Underlying _ _ _ _ x c) d
  rw [← @Category.assoc G.Underlying _ _ _ _ _ a y b, hc,
    @Category.assoc G.Underlying _ _ _ _ _ x a b, hab,
    @Category.assoc G.Underlying _ _ _ _ _ x c d]

/-- Restriction to the diagonal and descent from the cover are inverse
operations on continuous loops. -/
def coverLoopEquiv (A : QuotientCocycle G T) : (A ⟶ A) ≃ CoverLoop A where
  toFun := coverLoopOfHom
  invFun := CoverLoop.toHom
  left_inv r := by
    apply Subtype.ext
    apply Subtype.ext
    apply ContinuousMap.ext
    intro p
    exact congrArg Subtype.val (((coverLoopOfHom r).toArrowFamily_at p).trans
      (loop_offDiagonal r p).symm)
  right_inv l := by
    apply CoverLoop.arrow_ext
    apply ContinuousMap.ext
    intro x
    have he := ((l.toArrowFamily_at (A.coverDiagonal x)).trans
      (congrArg (fun s ↦ @CategoryStruct.comp G.Underlying _ _ _ _ (l.atPoint x) s)
        (A.step_unit x))).trans (@Category.comp_id G.Underlying _ _ _ (l.atPoint x))
    exact congrArg Subtype.val he


private def projectedCoverLoop (B : QuotientCocycle G.inertiaGroupoid T) :
    CoverLoop (B.map G.inertiaProjection) where
  arrows := ⟨fun x ↦ (B.point x).val, continuous_subtype_val.comp B.point.continuous⟩
  source_eq _ := rfl
  target_eq x := (B.point x).property.symm
  commute p := by
    let w := B.transition p
    have hsource : w.val.2 = B.point p.val.1 := B.transitionSource p
    have htarget : G.inertiaGroupoid.target w = B.point p.val.2 := B.transitionTarget p
    have h : G.target w.val.1 = G.source (B.point p.val.2).val :=
      (G.inertiaProjection.mapTarget w).trans (congrArg G.loopBase htarget)
    have he := (G.targetLoop_eq_iff w (B.point p.val.2) h).mp htarget
    apply Subtype.ext
    refine he.symm.trans ?_
    exact congrArg G.comp (Subtype.ext (Prod.ext
      (congrArg Subtype.val hsource) rfl))

/-- The vertical automorphism read from a cocycle of the conjugation groupoid. -/
noncomputable def projectedCocycleAutomorphism (B : QuotientCocycle G.inertiaGroupoid T) :
    (B.map G.inertiaProjection) ≅ (B.map G.inertiaProjection) :=
  asIso (projectedCoverLoop B).toHom

private theorem projectedCocycleAutomorphism_diagonal (B : QuotientCocycle G.inertiaGroupoid T)
    (x : B.coverSpace.obj) : (loopAt (projectedCocycleAutomorphism B).hom x).val = (B.point x).val :=
  congrArg (fun l : CoverLoop (B.map G.inertiaProjection) ↦ l.arrows x)
    ((coverLoopEquiv _).apply_symm_apply (projectedCoverLoop B))

/-- Restriction of the projected automorphism agrees with restricting the
conjugation cocycle before projecting. -/
theorem projectedCocycleAutomorphism_pullback {S : CGWH.{u}} (B : QuotientCocycle G.inertiaGroupoid T)
    (g : S ⟶ T) : pullbackHom (projectedCocycleAutomorphism B).hom g =
      (projectedCocycleAutomorphism (B.pullback g)).hom :=
  hom_ext fun _ ↦ rfl

/-- The canonical projected automorphism recovers the original conjugation cocycle. -/
theorem ofProjectedCocycleAutomorphism (B : QuotientCocycle G.inertiaGroupoid T) :
    ofAutomorphism (B.map G.inertiaProjection) (projectedCocycleAutomorphism B) = B := by
  have hpt (x : B.coverSpace.obj) : presentingLoops (projectedCocycleAutomorphism B).hom x = B.point x :=
    Subtype.ext (projectedCocycleAutomorphism_diagonal B x)
  refine cocycle_eq_of_fields rfl HEq.rfl (heq_of_eq (ContinuousMap.ext hpt)) ?_
  apply heq_of_eq
  apply ContinuousMap.ext
  intro p
  exact Subtype.ext (Prod.ext rfl ((hpt p.val.1).trans (B.transitionSource p).symm))

/-- Each conjugation cocycle is recovered from its projected cocycle and automorphism. -/
theorem exists_ofAutomorphism_eq (B : QuotientCocycle G.inertiaGroupoid T) :
    ∃ r : (B.map G.inertiaProjection) ≅ (B.map G.inertiaProjection),
      ofAutomorphism (B.map G.inertiaProjection) r = B :=
  ⟨projectedCocycleAutomorphism B,ofProjectedCocycleAutomorphism B⟩

private theorem loopSquare_iff {A B : QuotientCocycle G T}
    (a : A ⟶ A) (b : B ⟶ B) (f : A ⟶ B) :
    f ≫ b = a ≫ f ↔
      ∀ p : CGWH.FibreSubspace A.cover B.cover,
        @CategoryStruct.comp G.Underlying _ _ _ _ (arrowAt f.val p) (loopAt b p.val.2) =
        @CategoryStruct.comp G.Underlying _ _ _ _ (loopAt a p.val.1) (arrowAt f.val p) := by
  have hl (p : CGWH.FibreSubspace A.cover B.cover) :
      arrowAt (f ≫ b).val p =
        @CategoryStruct.comp G.Underlying _ _ _ _ (arrowAt f.val p) (loopAt b p.val.2) :=
    composeHom_eval f b (⟨(p.val.2,p),p.property.symm⟩ : Triple A B B)
  have hr (p : CGWH.FibreSubspace A.cover B.cover) :
      arrowAt (a ≫ f).val p =
        @CategoryStruct.comp G.Underlying _ _ _ _ (loopAt a p.val.1) (arrowAt f.val p) :=
    composeHom_eval a f (⟨(p.val.1,p),rfl⟩ : Triple A A B)
  constructor
  · intro h p
    exact (hl p).symm.trans ((congrArg (fun k : A ⟶ B ↦ arrowAt k.val p) h).trans (hr p))
  · intro h
    apply Subtype.ext
    apply Subtype.ext
    apply ContinuousMap.ext
    intro p
    exact congrArg Subtype.val ((hl p).trans ((h p).trans (hr p).symm))

private def presentingInertiaArrow {A B : QuotientCocycle G T}
    (a : A ⟶ A) (f : A ⟶ B) :
    C(CGWH.FibreSubspace A.cover B.cover, G.InertiaArrow) := by
  let l := (presentingLoops a).comp (fibreOne A B)
  letI : CompactlyGeneratedSpace (CGWH.FibreSubspace A.cover B.cover) :=
    closed_compactlyGenerated (CGWH.fibreSubspace_isClosed A.cover B.cover)
  exact ⟨fun p ↦ ⟨(f.val.val p,l p), (f.val.property.1 p).trans
    (loopAt a p.val.1).property.1.symm⟩, (kelleyPair f.val.val l).continuous.subtype_mk _⟩

/-- An arrow intertwining two global cocycle automorphisms lifts
continuously to the conjugation groupoid. -/
def liftInertiaHom {A B : QuotientCocycle G T} (a : A ≅ A) (b : B ≅ B) (f : A ⟶ B)
    (hf : f ≫ b.hom = a.hom ≫ f) : ofAutomorphism A a ⟶ ofAutomorphism B b := by
  let k := presentingInertiaArrow a.hom f
  have ht (p : CGWH.FibreSubspace A.cover B.cover) :
      G.inertiaGroupoid.target (k p) = presentingLoops b.hom p.val.2 := by
    apply (G.targetLoop_eq_iff _ _ ((f.val.property.2 p).trans
      (loopAt b.hom p.val.2).property.1.symm)).mpr
    exact congrArg Subtype.val ((loopSquare_iff a.hom b.hom f).mp hf p).symm
  refine ⟨⟨k,fun _ ↦ rfl,ht⟩,?_⟩
  intro p q hp hq
  apply Subtype.ext
  exact Subtype.ext (Prod.ext (congrArg Subtype.val (f.property p q hp hq)) rfl)

/-- The first coordinate of the lifted morphism is the original arrow
on the common refinement. -/
theorem liftInertiaHom_transport {A B : QuotientCocycle G T} (a : A ≅ A) (b : B ≅ B) (f : A ⟶ B)
    (hf : f ≫ b.hom = a.hom ≫ f) (p : CGWH.FibreSubspace A.cover B.cover) :
    (liftInertiaHom a b f hf).val.val p |>.val.1 = f.val.val p := rfl



private theorem inertiaHom_ext {A B : QuotientCocycle G.inertiaGroupoid T} (r s : A ⟶ B)
    (h : ∀ p : CGWH.FibreSubspace A.cover B.cover,
      (r.val.val p).val.1 = (s.val.val p).val.1) : r = s := by
  apply Subtype.ext
  apply Subtype.ext
  apply ContinuousMap.ext
  intro p
  exact Subtype.ext (Prod.ext (h p) ((r.val.property.1 p).trans (s.val.property.1 p).symm))

/-- The cocycle functor induced by the inertia projection is faithful. -/
theorem inertiaProjection_mapCocycles_faithful :
    (mapCocycles (T := T) G.inertiaProjection).Faithful where
  map_injective {A B} {r s} h := by
    apply inertiaHom_ext r s
    intro p
    exact congrArg (fun a : A.map G.inertiaProjection ⟶ B.map G.inertiaProjection ↦ a.val.val p) h

/-- Projection of an arrow of conjugation cocycles intertwines the two
automorphisms specified by the point loops. -/
theorem inertiaProjection_mapHom_commutes {B C : QuotientCocycle G.inertiaGroupoid T} (r : B ⟶ C) :
    mapHom G.inertiaProjection r ≫ (projectedCocycleAutomorphism C).hom =
      (projectedCocycleAutomorphism B).hom ≫ mapHom G.inertiaProjection r := by
  apply (loopSquare_iff _ _ _).mpr
  intro p
  let w := r.val.val p
  have hs : w.val.2 = B.point p.val.1 := r.val.property.1 p
  have ht : G.inertiaGroupoid.target w = C.point p.val.2 := r.val.property.2 p
  have h : G.target w.val.1 = G.source (C.point p.val.2).val :=
    (G.inertiaProjection.mapTarget w).trans (congrArg G.loopBase ht)
  have he := (G.targetLoop_eq_iff _ _ h).mp ht
  apply Subtype.ext
  refine Eq.trans ?_ (Eq.trans he.symm ?_)
  · apply congrArg G.comp
    exact Subtype.ext (Prod.ext rfl (projectedCocycleAutomorphism_diagonal C p.val.2))
  · apply congrArg G.comp
    exact Subtype.ext (Prod.ext ((congrArg Subtype.val hs).trans
      (projectedCocycleAutomorphism_diagonal B p.val.1).symm) rfl)

/-- An intertwining arrow lifts between the actual conjugation cocycles. -/
def liftProjectedInertiaHom {B C : QuotientCocycle G.inertiaGroupoid T}
    (r : B.map G.inertiaProjection ⟶ C.map G.inertiaProjection)
    (hr : r ≫ (projectedCocycleAutomorphism C).hom = (projectedCocycleAutomorphism B).hom ≫ r) : B ⟶ C := by
  let P := CGWH.FibreSubspace B.cover C.cover
  letI : CompactlyGeneratedSpace P := closed_compactlyGenerated (CGWH.fibreSubspace_isClosed B.cover C.cover)
  let l := B.point.comp (fibreOne B C)
  have hl (p : P) : G.source (r.val.val p) = G.source (l p).val := r.val.property.1 p
  let k : C(P,G.InertiaArrow) := ⟨fun p ↦ ⟨(r.val.val p,l p),hl p⟩,
    (kelleyPair r.val.val l).continuous.subtype_mk _⟩
  have ht (p : P) : G.inertiaGroupoid.target (k p) = C.point p.val.2 := by
    apply (G.targetLoop_eq_iff _ _ (r.val.property.2 p)).mpr
    have he := congrArg Subtype.val ((loopSquare_iff _ _ _).mp hr p).symm
    refine Eq.trans ?_ (Eq.trans he ?_)
    · apply congrArg G.comp
      exact Subtype.ext (Prod.ext (projectedCocycleAutomorphism_diagonal B p.val.1).symm rfl)
    · apply congrArg G.comp
      exact Subtype.ext (Prod.ext rfl (projectedCocycleAutomorphism_diagonal C p.val.2))
  refine ⟨⟨k,fun _ ↦ rfl,ht⟩,?_⟩
  intro p q hp hq
  exact Subtype.ext (Subtype.ext (Prod.ext (congrArg Subtype.val (r.property p q hp hq))
    (B.transitionSource ⟨(p.val.1,q.val.1),hp⟩)))

theorem mapHom_liftProjectedInertiaHom {B C : QuotientCocycle G.inertiaGroupoid T}
    (r : B.map G.inertiaProjection ⟶ C.map G.inertiaProjection)
    (hr : r ≫ (projectedCocycleAutomorphism C).hom = (projectedCocycleAutomorphism B).hom ≫ r) :
    mapHom G.inertiaProjection (liftProjectedInertiaHom (B := B) (C := C) r hr) = r := by
  apply hom_ext
  intro p
  rfl

/-- Starting with an automorphism and then reading it back from its
conjugation cocycle gives an isomorphic pair. -/
theorem projectedCocycleAutomorphism_ofAutomorphism (A : QuotientCocycle G T) (r : A ≅ A) :
    ∃ e : (ofAutomorphism A r).map G.inertiaProjection ≅ A,
      e.hom ≫ r.hom = (projectedCocycleAutomorphism (ofAutomorphism A r)).hom ≫ e.hom := by
  let B := ofAutomorphism A r
  let A' := B.map G.inertiaProjection
  let e : A' ≅ A := isoOfCoverMap A A' (ContinuousMap.id _)
    (fun _ ↦ rfl) (fun x ↦ (loopAt r.hom x).property.1.symm) (fun _ _ _ ↦ rfl)
  refine ⟨e,(loopSquare_iff _ _ _).mpr ?_⟩
  intro p
  have h := congrArg Subtype.val (loop_commutes_transition r.hom p)
  apply Subtype.ext
  refine Eq.trans h ?_
  apply congrArg G.comp
  exact Subtype.ext (Prod.ext (projectedCocycleAutomorphism_diagonal B p.val.1).symm rfl)

private def transportInertiaHom {A B : QuotientCocycle G T} (a : A ≅ A) (b : B ≅ B)
    (r : ofAutomorphism A a ⟶ ofAutomorphism B b) : A ⟶ B := by
  let k := G.inertiaProjection.arrowMap.comp r.val.val
  have hs (p : CGWH.FibreSubspace A.cover B.cover) : G.source (k p) = A.point p.val.1 :=
    (G.inertiaProjection.mapSource (r.val.val p)).trans
      ((congrArg G.loopBase (r.val.property.1 p)).trans (loopAt a.hom p.val.1).property.1)
  have ht (p : CGWH.FibreSubspace A.cover B.cover) : G.target (k p) = B.point p.val.2 :=
    (G.inertiaProjection.mapTarget (r.val.val p)).trans
      ((congrArg G.loopBase (r.val.property.2 p)).trans (loopAt b.hom p.val.2).property.1)
  refine ⟨⟨k,hs,ht⟩,?_⟩
  intro p q hp hq
  apply Subtype.ext
  exact congrArg (fun z : G.InertiaArrow ↦ z.val.1)
    (congrArg Subtype.val (r.property p q hp hq))

private theorem transportInertiaHom_square {A B : QuotientCocycle G T} (a : A ≅ A) (b : B ≅ B)
    (r : ofAutomorphism A a ⟶ ofAutomorphism B b) :
    transportInertiaHom a b r ≫ b.hom = a.hom ≫ transportInertiaHom a b r := by
  apply (loopSquare_iff a.hom b.hom _).mpr
  intro p
  have hs : (r.val.val p).val.2 = presentingLoops a.hom p.val.1 := r.val.property.1 p
  have ht : G.inertiaGroupoid.target (r.val.val p) = presentingLoops b.hom p.val.2 :=
    r.val.property.2 p
  have h : G.target (r.val.val p).val.1 = G.source (loopAt b.hom p.val.2).val :=
    (G.inertiaProjection.mapTarget _).trans (congrArg G.loopBase ht)
  have he := (G.targetLoop_eq_iff _ _ h).mp ht
  apply Subtype.ext
  change G.comp ⟨((r.val.val p).val.1, (loopAt b.hom p.val.2).val), h⟩ =
    G.comp ⟨((loopAt a.hom p.val.1).val, (r.val.val p).val.1), _⟩
  refine he.symm.trans ?_
  exact congrArg G.comp (Subtype.ext (Prod.ext (congrArg Subtype.val hs) rfl))

/-- Objects of inertia of a quotient cocycle category. -/
structure LoopedCocycle (G : TopologicalGroupoid.{u}) (T : CGWH.{u}) where
  point : QuotientCocycle G T
  loop : point ≅ point

/-- An arrow in inertia intertwines the designated automorphisms. -/
@[ext] structure LoopedHom {G : TopologicalGroupoid.{u}} {T : CGWH.{u}}
    (a b : LoopedCocycle G T) where
  hom : a.point ⟶ b.point
  square : hom ≫ b.loop.hom = a.loop.hom ≫ hom

noncomputable instance : Category (LoopedCocycle G T) where
  Hom := LoopedHom
  id a := ⟨𝟙 a.point, by simp⟩
  comp f g := ⟨f.hom ≫ g.hom, by
    rw [Category.assoc, g.square, ← Category.assoc, f.square, Category.assoc]⟩
  id_comp f := LoopedHom.ext (Category.id_comp _)
  comp_id f := LoopedHom.ext (Category.comp_id _)
  assoc f g h := LoopedHom.ext (Category.assoc _ _ _)

set_option maxHeartbeats 900000 in
/-- The descent version of the comparison with the topological conjugation
groupoid, including all cocycle objects and all compatible arrows. -/
def descendedInertiaComparison (G : TopologicalGroupoid.{u}) (T : CGWH.{u}) :
    LoopedCocycle G T ⥤ QuotientCocycle G.inertiaGroupoid T where
  obj a := ofAutomorphism a.point a.loop
  map {a b} r := liftInertiaHom a.loop b.loop r.hom r.square
  map_id a := by
    apply inertiaHom_ext
    intro p
    rfl
  map_comp {a b c} r s := by
    apply inertiaHom_ext
    intro p
    obtain ⟨y,hy⟩ := b.point.isCover.surjective (a.point.cover.hom p.val.1)
    let z : Triple a.point b.point c.point := ⟨(y,p),hy⟩
    let z' : Triple (ofAutomorphism a.point a.loop) (ofAutomorphism b.point b.loop)
        (ofAutomorphism c.point c.loop) := ⟨(y,p),hy⟩
    have h₁ := congrArg Subtype.val (composeHom_eval r.hom s.hom z)
    have h₂ := congrArg (fun v : G.InertiaArrow ↦ v.val.1)
      (congrArg Subtype.val (composeHom_eval (liftInertiaHom a.loop b.loop r.hom r.square)
        (liftInertiaHom b.loop c.loop s.hom s.square) z'))
    exact h₁.trans h₂.symm

/-- A categorical equivalence on the actual cocycle groupoids, before
any further passage to stackification. -/
theorem descendedInertiaComparison_isEquivalence (G : TopologicalGroupoid.{u}) (T : CGWH.{u}) :
    (descendedInertiaComparison G T).IsEquivalence := by
  let F := descendedInertiaComparison G T
  obtain ⟨hff⟩ : Nonempty F.FullyFaithful := by
    apply (Functor.FullyFaithful.nonempty_iff_map_bijective _).mpr
    intro a b
    constructor
    · intro r s h
      apply LoopedHom.ext
      apply Subtype.ext
      apply Subtype.ext
      apply ContinuousMap.ext
      intro p
      exact congrArg (fun v : F.obj a ⟶ F.obj b ↦ (v.val.val p).val.1) h
    · intro r
      let f := transportInertiaHom a.loop b.loop r
      let s : a ⟶ b := ⟨f,transportInertiaHom_square a.loop b.loop r⟩
      exact ⟨s,inertiaHom_ext _ _ (fun _ ↦ rfl)⟩
  letI := hff.full
  letI := hff.faithful
  letI : F.EssSurj := ⟨fun B ↦ by
    obtain ⟨r,hr⟩ := exists_ofAutomorphism_eq B
    exact ⟨⟨B.map G.inertiaProjection,r⟩,⟨eqToIso hr⟩⟩⟩
  exact {}

/-- Restriction of the descended conjugation cocycle uses exactly the
pullback of the automorphism on the original quotient cocycle. -/
theorem ofAutomorphism_pullback {S : CGWH.{u}} (g : S ⟶ T)
    (A : QuotientCocycle G T) (r : A ≅ A) :
    ofAutomorphism (A.pullback g) ((pullbackFunctor g).mapIso r) =
      (ofAutomorphism A r).pullback g := by
  refine cocycle_eq_of_fields rfl HEq.rfl ?_ ?_
  · exact heq_of_eq (ContinuousMap.ext fun _ ↦ rfl)
  · exact heq_of_eq (ContinuousMap.ext fun _ ↦ rfl)


/-- Restriction also preserves the actual continuous arrow on the common
refinement. The two values are compared on their identical pullback cover. -/
theorem liftInertiaHom_pullback_apply {S : CGWH.{u}} (g : S ⟶ T)
    {A B : QuotientCocycle G T} (a : A ≅ A) (b : B ≅ B) (f : A ⟶ B)
    (hf : f ≫ b.hom = a.hom ≫ f)
    (hfg : (pullbackFunctor g).map f ≫ ((pullbackFunctor g).mapIso b).hom =
      ((pullbackFunctor g).mapIso a).hom ≫ (pullbackFunctor g).map f)
    (p : CGWH.FibreSubspace (A.pullback g).cover (B.pullback g).cover) :
    (liftInertiaHom ((pullbackFunctor g).mapIso a) ((pullbackFunctor g).mapIso b)
      ((pullbackFunctor g).map f) hfg).val.val p =
      (pullbackHom (liftInertiaHom a b f hf) g).val.val p :=
  Subtype.ext (Prod.ext rfl rfl)

end InertiaComparison

end QuotientCocycle

end Masullo.TopologicalGroupoid
