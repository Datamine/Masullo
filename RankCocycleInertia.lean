import BasedInertia
import RankCocycleMorita

open CategoryTheory CategoryTheory.Functor CategoryTheory.Pseudofunctor.CoGrothendieck Opposite Cardinal
open scoped Bicategory Pseudofunctor.StrongTrans Cardinal

namespace Masullo.TopologicalGroupoid

open QuotientCocycle

universe u

noncomputable section

variable {G : TopologicalGroupoid.{u}} {α : Ordinal.{u}}

/-- Forming the conjugation groupoid preserves the manuscript's rank bound. -/
theorem rankInertiaGroupoid_bounded (G : TopologicalGroupoid.{u})
    (hω : ℵ₀ < preBeth α) (hG : #(G.arrows.obj : Type u) < preBeth α) :
    #(G.inertiaGroupoid.objects.obj : Type u) < preBeth α ∧
      #(G.inertiaGroupoid.arrows.obj : Type u) < preBeth α := by
  have hl : #G.Inertia < preBeth α := (mk_le_of_injective
    (f := fun x : G.Inertia ↦ x.val) Subtype.val_injective).trans_lt hG
  have hp : #(G.arrows.obj × G.Inertia) < preBeth α := by
    simp only [mk_prod,lift_id]
    exact mul_lt_of_lt hω.le hG hl
  exact ⟨hl,(mk_le_of_injective (f := fun x : G.InertiaArrow ↦
    show G.arrows.obj × G.Inertia from x.val) Subtype.val_injective).trans_lt hp⟩

/-- The inertia category of the total rank-site cocycle stack. Its objects
carry automorphisms lying over identity maps of rank tests. -/
abbrev RankCocycleInertiaTotal (G : TopologicalGroupoid.{u}) (α : Ordinal.{u}) :=
  BasedInertia.Obj (BasedCategory.ofFunctor (rankCocycleProjection G α))

abbrev rankCocycleInertiaProjection (G : TopologicalGroupoid.{u}) (α : Ordinal.{u}) :
    RankCocycleInertiaTotal G α ⥤ RankSpace α :=
  (BasedInertia.based (BasedCategory.ofFunctor (rankCocycleProjection G α))).p

private abbrev project (G : TopologicalGroupoid.{u}) (α : Ordinal.{u}) :=
  rankCocyclePushforwardTotal G.inertiaProjection α

private def verticalLoop (a : RankCocycleTotal G.inertiaGroupoid α) :
    (project G α).obj a ≅ (project G α).obj a :=
  (ι (rankCocyclePseudofunctor G α) a.base).mapIso (projectedCocycleAutomorphism a.fiber)

private theorem project_map_fiber {a b : RankCocycleTotal G.inertiaGroupoid α} (r : a ⟶ b) :
    ((project G α).map r).fiber = mapHom G.inertiaProjection r.fiber := by
  let g := (rankSpaceInclusion α).map r.base
  let f : a.fiber.map G.inertiaProjection ⟶ (b.fiber.map G.inertiaProjection).pullback g :=
    mapHom G.inertiaProjection r.fiber
  change f ≫ 𝟙 _ = f
  exact Category.comp_id _

private theorem square_iff {a b : RankCocycleTotal G.inertiaGroupoid α}
    (r : (project G α).obj a ⟶ (project G α).obj b) :
    r ≫ (verticalLoop b).hom = (verticalLoop a).hom ≫ r ↔
      r.fiber ≫ (projectedCocycleAutomorphism
        (b.fiber.pullback ((rankSpaceInclusion α).map r.base))).hom =
      (projectedCocycleAutomorphism a.fiber).hom ≫ r.fiber := by
  refine (FiberedGrothendieck.verticalSquare_iff r
    (projectedCocycleAutomorphism a.fiber).hom (projectedCocycleAutomorphism b.fiber).hom).trans ?_
  have h := projectedCocycleAutomorphism_pullback b.fiber ((rankSpaceInclusion α).map r.base)
  refine ⟨fun e ↦ ?_,fun e ↦ ?_⟩
  · exact (congrArg (fun t ↦ r.fiber ≫ t) h).symm.trans e
  · exact (congrArg (fun t ↦ r.fiber ≫ t) h).trans e

/-- The conjugation groupoid stack maps to the actual inertia of the
quotient cocycle stack. The automorphism is read from its local loops. -/
def rankInertiaStackComparison (G : TopologicalGroupoid.{u}) (α : Ordinal.{u}) :
    RankCocycleTotal G.inertiaGroupoid α ⥤ RankCocycleInertiaTotal G α where
  obj a := ⟨(project G α).obj a,verticalLoop a,IsHomLift.map _ (verticalLoop a).hom⟩
  map {a b} r := ⟨(project G α).map r,(square_iff ((project G α).map r)).mpr (by
    rw [project_map_fiber]
    exact inertiaProjection_mapHom_commutes r.fiber)⟩
  map_id a := BasedInertia.Arrow.ext ((project G α).map_id a)
  map_comp r s := BasedInertia.Arrow.ext ((project G α).map_comp r s)

theorem rankInertiaStackComparison_over (G : TopologicalGroupoid.{u}) (α : Ordinal.{u}) :
    rankInertiaStackComparison G α ⋙ rankCocycleInertiaProjection G α =
      rankCocycleProjection G.inertiaGroupoid α := rfl

theorem rankInertiaStackComparison_forget (G : TopologicalGroupoid.{u}) (α : Ordinal.{u}) :
    rankInertiaStackComparison G α ⋙ BasedInertia.forget (BasedCategory.ofFunctor (rankCocycleProjection G α)) =
      rankCocyclePushforwardTotal G.inertiaProjection α := rfl

/-- The comparison is fully faithful on all arrows, including arrows
over a nonidentity base map. -/
theorem rankInertiaStackComparison_fullyFaithful (G : TopologicalGroupoid.{u}) (α : Ordinal.{u}) :
    Nonempty (rankInertiaStackComparison G α).FullyFaithful := by
  apply (Functor.FullyFaithful.nonempty_iff_map_bijective _).mpr
  intro a b
  constructor
  · intro r s h
    have he := congrArg BasedInertia.Arrow.hom h
    obtain ⟨q,r⟩ := r
    obtain ⟨q',s⟩ := s
    have hq : q = q' := congrArg Hom.base he
    subst q'
    let m : a ⟶ b := ⟨q,r⟩
    let n : a ⟶ b := ⟨q,s⟩
    have hf : ((project G α).map m).fiber = ((project G α).map n).fiber :=
      (Hom.congr he).trans (Category.comp_id _)
    have hr : mapHom G.inertiaProjection r = mapHom G.inertiaProjection s :=
      (project_map_fiber m).symm.trans (hf.trans (project_map_fiber n))
    let K := mapCocycles (T := a.base.space) G.inertiaProjection
    letI : K.Faithful := inertiaProjection_mapCocycles_faithful
    exact congrArg (fun x ↦ (⟨q,x⟩ : a ⟶ b)) (K.map_injective hr)
  · intro r
    let q := r.hom.base
    let g := (rankSpaceInclusion α).map q
    have hr := (square_iff r.hom).mp r.square
    let t := liftProjectedInertiaHom (B := a.fiber) (C := b.fiber.pullback g) r.hom.fiber hr
    let s : a ⟶ b := ⟨q,t⟩
    refine ⟨s,BasedInertia.Arrow.ext ?_⟩
    refine Pseudofunctor.CoGrothendieck.Hom.ext ((project G α).map s) r.hom (by rfl) ?_
    exact (project_map_fiber s).trans ((mapHom_liftProjectedInertiaHom (B := a.fiber)
      (C := b.fiber.pullback g) r.hom.fiber hr).trans
      (Category.comp_id _).symm)

private def inertiaIso {a b : RankCocycleInertiaTotal G α} (e : a.point ≅ b.point)
    (h : e.hom ≫ b.loop.hom = a.loop.hom ≫ e.hom) : a ≅ b where
  hom := ⟨e.hom,h⟩
  inv := ⟨e.inv,by
    have h' := congrArg (fun t ↦ e.inv ≫ t ≫ e.inv) h
    simpa [Category.assoc] using h'.symm⟩
  hom_inv_id := BasedInertia.Arrow.ext e.hom_inv_id
  inv_hom_id := BasedInertia.Arrow.ext e.inv_hom_id

private theorem inertiaVerticalCover (b : RankCocycleInertiaTotal G α) :
    ∃ A : QuotientCocycle G.inertiaGroupoid b.point.base.space,
      ∃ e : (rankInertiaStackComparison G α).obj ⟨b.point.base,A⟩ ≅ b,
        (rankCocycleInertiaProjection G α).IsHomLift (𝟙 b.point.base) e.hom := by
  let F := rankCocyclePseudofunctor G α
  let X := b.point.base
  obtain ⟨t,ht⟩ := FiberedGrothendieck.exists_verticalHom b.loop.hom b.vertical
  letI : IsIso t := @IsIso.of_groupoid (QuotientCocycle G X.space) _ _ _ t
  let u := asIso t
  have hu : (ι F X).mapIso u = b.loop := Iso.ext ht
  obtain ⟨e,he⟩ := projectedCocycleAutomorphism_ofAutomorphism b.point.fiber u
  let A := ofAutomorphism b.point.fiber u
  let a : RankCocycleTotal G.inertiaGroupoid α := ⟨X,A⟩
  let c := (rankInertiaStackComparison G α).obj a
  let q : c.point ≅ b.point := (ι F X).mapIso e
  have h : q.hom ≫ b.loop.hom = c.loop.hom ≫ q.hom := by
    rw [← hu]
    change ((ι F X).map e.hom) ≫ ((ι F X).map u.hom) =
      ((ι F X).map (projectedCocycleAutomorphism A).hom) ≫ ((ι F X).map e.hom)
    exact ((ι F X).map_comp e.hom u.hom).symm.trans
      (((ι F X).congr_map he).trans ((ι F X).map_comp (projectedCocycleAutomorphism A).hom e.hom))
  exact ⟨A,inertiaIso q h,IsHomLift.map _ (inertiaIso q h).hom⟩

/-- Every inertia object has a conjugation-cocycle representative on its
own test space. -/
theorem rankInertiaStackComparison_isEquivalence (G : TopologicalGroupoid.{u}) (α : Ordinal.{u}) :
    (rankInertiaStackComparison G α).IsEquivalence := by
  let L := rankInertiaStackComparison G α
  let ff := (rankInertiaStackComparison_fullyFaithful G α).some
  letI : L.Full := ff.full
  letI : L.Faithful := ff.faithful
  letI : L.EssSurj := ⟨fun b ↦ by
    obtain ⟨A,e,_⟩ := inertiaVerticalCover b
    exact ⟨⟨b.point.base,A⟩,⟨e⟩⟩⟩
  exact ({} : L.IsEquivalence)

set_option backward.isDefEq.respectTransparency false in
/-- Corrected E.6.3.6. In the explicit quotient-cocycle models the
conjugation groupoid presents the inertia of the quotient stack over the
rank site, with an inverse over the site and vertical unit and counit. -/
theorem rankInertiaStackEquivalence_over (G : TopologicalGroupoid.{u}) (α : Ordinal.{u}) :
    ∃ e : RankCocycleTotal G.inertiaGroupoid α ≌ RankCocycleInertiaTotal G α,
      e.functor = rankInertiaStackComparison G α ∧
      e.inverse ⋙ rankCocycleProjection G.inertiaGroupoid α = rankCocycleInertiaProjection G α ∧
      (∀ a, (rankCocycleProjection G.inertiaGroupoid α).IsHomLift (𝟙 a.base) (e.unitIso.hom.app a)) ∧
      ∀ b, (rankCocycleInertiaProjection G α).IsHomLift (𝟙 b.point.base) (e.counitIso.hom.app b) := by
  let L := rankInertiaStackComparison G α
  let ff := (rankInertiaStackComparison_fullyFaithful G α).some
  let p := rankCocycleProjection G.inertiaGroupoid α
  let q := rankCocycleInertiaProjection G α
  let pick (b : RankCocycleInertiaTotal G α) := inertiaVerticalCover b
  let obj (b : RankCocycleInertiaTotal G α) : RankCocycleTotal G.inertiaGroupoid α :=
    ⟨b.point.base,(pick b).choose⟩
  let v (b : RankCocycleInertiaTotal G α) : L.obj (obj b) ≅ b := (pick b).choose_spec.choose
  have hv (b : RankCocycleInertiaTotal G α) : q.IsHomLift (𝟙 b.point.base) (v b).hom := (pick b).choose_spec.choose_spec
  have hvh (b : RankCocycleInertiaTotal G α) : q.map (v b).hom = 𝟙 b.point.base := by
    letI := hv b
    simpa using (IsHomLift.fac q (𝟙 b.point.base) (v b).hom).symm
  have hvi (b : RankCocycleInertiaTotal G α) : q.map (v b).inv = 𝟙 b.point.base := by
    have h := q.congr_map (v b).hom_inv_id
    rw [q.map_comp,hvh,q.map_id] at h
    exact (Category.id_comp (q.map (v b).inv)).symm.trans h
  let I : RankCocycleInertiaTotal G α ⥤ RankCocycleTotal G.inertiaGroupoid α := {
    obj := obj
    map {a b} r := ff.preimage ((v a).hom ≫ r ≫ (v b).inv)
    map_id a := ff.map_injective (by simp)
    map_comp r s := ff.map_injective (by simp [ff.map_preimage,Category.assoc]) }
  have hpre {a b : RankCocycleTotal G.inertiaGroupoid α} (r : L.obj a ⟶ L.obj b) :
      L.map (ff.preimage r) = r := ff.map_preimage r
  have hmap {a b} (r : a ⟶ b) : L.map (I.map r) = (v a).hom ≫ r ≫ (v b).inv := ff.map_preimage _
  let η : 𝟭 _ ≅ L ⋙ I := NatIso.ofComponents (fun a ↦ (ff.preimageIso (v (L.obj a))).symm)
    (fun r ↦ ff.map_injective (by
      change L.map (r ≫ ff.preimage (v (L.obj _)).inv) = L.map (ff.preimage (v (L.obj _)).inv ≫ I.map (L.map r))
      rw [L.map_comp,L.map_comp,hpre,hpre,hmap]
      simp))
  let ε : I ⋙ L ≅ 𝟭 _ := NatIso.ofComponents v (by
    intro a b r
    change L.map (I.map r) ≫ (v b).hom = (v a).hom ≫ r
    rw [hmap]
    simp [Category.assoc])
  let e : RankCocycleTotal G.inertiaGroupoid α ≌ RankCocycleInertiaTotal G α := {
    functor := L
    inverse := I
    unitIso := η
    counitIso := ε
    functor_unitIso_comp a := by
      change L.map (ff.preimage (v (L.obj a)).inv) ≫ (v (L.obj a)).hom = 𝟙 _
      rw [hpre,Iso.inv_hom_id] }
  refine ⟨e,rfl,?_,?_,hv⟩
  · refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
    intro a b r
    simp only [eqToHom_refl,Category.id_comp,Category.comp_id]
    change q.map (L.map (I.map r)) = q.map r
    rw [hmap,q.map_comp,q.map_comp,hvh,hvi]
    exact (Category.id_comp (q.map r ≫ 𝟙 _)).trans (Category.comp_id (q.map r))
  · intro a
    apply IsHomLift.of_fac' p (𝟙 a.base) (e.unitIso.hom.app a) rfl rfl
    change q.map (L.map (ff.preimage (v (L.obj a)).inv)) = _
    rw [hpre,hvi]
    simp only [eqToHom_refl,Category.comp_id]
    rfl

private theorem inertiaHomLift_iff {a b : RankCocycleInertiaTotal G α} (r : a ⟶ b)
    {X Y : RankSpace α} (f : X ⟶ Y) :
    (rankCocycleInertiaProjection G α).IsHomLift f r ↔ (rankCocycleProjection G α).IsHomLift f r.hom := by
  let q := rankCocycleInertiaProjection G α
  let p := rankCocycleProjection G α
  constructor
  · intro h
    cases h
    exact IsHomLift.map p r.hom
  · intro h
    cases h
    exact IsHomLift.map q r

set_option backward.isDefEq.respectTransparency false in
/-- Every arrow of the inertia category of these groupoid fibres is
Cartesian. Cancellation along the underlying Cartesian arrow verifies
that the lifted arrow still intertwines the vertical automorphisms. -/
theorem rankCocycleInertiaArrow_cartesian {a b : RankCocycleInertiaTotal G α} (r : a ⟶ b) :
    (rankCocycleInertiaProjection G α).IsStronglyCartesian r.hom.base r := by
  let p := rankCocycleProjection G α
  let q := rankCocycleInertiaProjection G α
  let f := r.hom.base
  letI : IsIso r.hom.fiber := @IsIso.of_groupoid (QuotientCocycle G a.point.base.space) _ _ _ r.hom.fiber
  letI : p.IsStronglyCartesian f r.hom := FiberedGrothendieck.isStronglyCartesian_of_fiber_isIso r.hom
  letI : p.IsHomLift f r.hom := IsHomLift.map p r.hom
  refine { toIsHomLift := IsHomLift.map q r, universal_property' := ?_ }
  intro c g s hs
  letI : p.IsHomLift (g ≫ f) s.hom := (inertiaHomLift_iff s _).mp hs
  obtain ⟨t,⟨ht,htr⟩,hu⟩ := IsStronglyCartesian.universal_property p f r.hom g (g ≫ f) rfl s.hom
  letI := ht
  letI : p.IsHomLift (𝟙 a.point.base) a.loop.hom := a.vertical
  letI : p.IsHomLift (𝟙 c.point.base) c.loop.hom := c.vertical
  have hta : p.IsHomLift g (t ≫ a.loop.hom) := by
    simpa only [Category.comp_id] using (IsHomLift.comp p g (𝟙 a.point.base) t a.loop.hom)
  have hct : p.IsHomLift g (c.loop.hom ≫ t) := by
    simpa only [Category.id_comp] using (IsHomLift.comp p (𝟙 c.point.base) g c.loop.hom t)
  letI := hta
  letI := hct
  have hsq : t ≫ a.loop.hom = c.loop.hom ≫ t := by
    apply IsStronglyCartesian.ext p f r.hom g
    rw [Category.assoc,← r.square,← Category.assoc,htr,s.square,Category.assoc,htr]
  let u : c ⟶ a := ⟨t,hsq⟩
  refine ⟨u,⟨(inertiaHomLift_iff u g).mpr ht,BasedInertia.Arrow.ext htr⟩,?_⟩
  intro v hv
  exact BasedInertia.Arrow.ext (hu v.hom ⟨(inertiaHomLift_iff v g).mp hv.1,congrArg BasedInertia.Arrow.hom hv.2⟩)

/-- The stack comparison preserves Cartesian arrows over the rank site. -/
theorem rankInertiaStackComparison_cartesian {a b : RankCocycleTotal G.inertiaGroupoid α} (r : a ⟶ b) :
    (rankCocycleInertiaProjection G α).IsStronglyCartesian r.base ((rankInertiaStackComparison G α).map r) :=
  rankCocycleInertiaArrow_cartesian ((rankInertiaStackComparison G α).map r)

/-- Inertia is fibred over the rank site. -/
theorem rankCocycleInertiaProjection_isFibered (G : TopologicalGroupoid.{u}) (α : Ordinal.{u}) :
    (rankCocycleInertiaProjection G α).IsFibered := by
  apply Functor.IsFibered.of_exists_isStronglyCartesian
  intro b X f
  let a : RankCocycleTotal G α := ⟨X,b.point.fiber.pullback ((rankSpaceInclusion α).map f)⟩
  let r : a ⟶ b.point := ⟨f,𝟙 _⟩
  let F := rankCocyclePseudofunctor G α
  obtain ⟨s,hs⟩ := FiberedGrothendieck.exists_verticalHom b.loop.hom b.vertical
  let A : QuotientCocycle G b.point.base.space := b.point.fiber
  let v : A ⟶ A := s
  let e : A ≅ A := @asIso (QuotientCocycle G b.point.base.space) _ A A v
    (@IsIso.of_groupoid (QuotientCocycle G b.point.base.space) _ A A v)
  let t := (pullbackFunctor ((rankSpaceInclusion α).map f)).mapIso e
  let c : RankCocycleInertiaTotal G α := ⟨a,(ι F X).mapIso t,IsHomLift.map _ ((ι F X).mapIso t).hom⟩
  let u : c ⟶ b := ⟨r,by
    rw [← hs]
    apply (FiberedGrothendieck.verticalSquare_iff _ _ _).mpr
    let g := (rankSpaceInclusion α).map f
    let m : A.pullback g ⟶ A.pullback g := pullbackHom v g
    change 𝟙 (A.pullback g) ≫ m = m ≫ 𝟙 (A.pullback g)
    exact (Category.id_comp m).trans (Category.comp_id m).symm⟩
  exact ⟨c,u,rankCocycleInertiaArrow_cartesian u⟩

end

end Masullo.TopologicalGroupoid
