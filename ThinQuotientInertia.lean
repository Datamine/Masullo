import ClosedGroupoidQuotient
import Mathlib.CategoryTheory.Sites.LocallyInjective
import Mathlib.CategoryTheory.Sites.LocallySurjective
import Mathlib.CategoryTheory.Elements

/-! A topological groupoid whose endpoints determine its arrows has a
discrete stackification, so the inertia projection is an equivalence. -/

open Cardinal CategoryTheory Function Set Topology TopologicalSpace
open scoped Cardinal Ordinal CategoryTheory.BasedFunctor

noncomputable section

namespace Masullo.TopologicalGroupoid

universe u

variable {α : Ordinal.{u}} (G : TopologicalGroupoid.{u})

/-- Injectivity of the endpoint map makes every category of continuous
points thin, independently of the topology induced on the endpoint image. -/
theorem pointHom_subsingleton (hG : Injective (ordinaryEndpoints G))
    {T : CGWH.{u}} (a b : G.Points T) : Subsingleton (a ⟶ b) := by
  refine ⟨fun r s ↦ Subtype.ext (ContinuousMap.ext fun x ↦ ?_)⟩
  apply hG
  exact Prod.ext ((r.property.1 x).trans (s.property.1 x).symm)
    ((r.property.2 x).trans (s.property.2 x).symm)

/-- Arrows between continuous points glue along any canonical sieve when
endpoints determine an arrow. Compatibility holds pointwise on the disjoint
union and continuity descends along its quotient map. -/
theorem pointIso_of_rankLocalIso (hG : Injective (ordinaryEndpoints G))
    (hα : preBeth α = α.card) (hω : ℵ₀ < preBeth α)
    {T : RankSpace α} (S : Sieve T) (hS : S ∈ Sheaf.canonicalTopology (RankSpace α) T)
    (a b : G.Points T.space)
    (h : ∀ i : RankSieveArrows S,
      Nonempty ((G.restrictPoints ((rankSpaceInclusion α).map i.2.val).hom.hom.hom).obj a ≅
        (G.restrictPoints ((rankSpaceInclusion α).map i.2.val).hom.hom.hom).obj b)) :
    Nonempty (a ≅ b) := by
  let q := rankSieveMap S
  have hq : IsQuotientMap q := (rankCanonicalTopology_iff S hα hω).mp hS
  let r (i : RankSieveArrows S) := (h i).some.hom
  let k : (Σ i : RankSieveArrows S, i.1.space.obj) → G.arrows.obj :=
    fun p ↦ (r p.1).val p.2
  have hk : Continuous k := continuous_sigma fun i ↦ (r i).val.continuous
  have hs (p) : G.source (k p) = a (q p) := (r p.1).property.1 p.2
  have ht (p) : G.target (k p) = b (q p) := (r p.1).property.2 p.2
  let K (x : T.space.obj) : G.arrows.obj := k ((hq.surjective x).choose)
  have hK (x : T.space.obj) : ordinaryEndpoints G (K x) = (a x, b x) := by
    let p := (hq.surjective x).choose
    have hp : q p = x := (hq.surjective x).choose_spec
    exact Prod.ext ((hs p).trans (congrArg a hp)) ((ht p).trans (congrArg b hp))
  have hcomp (p) : K (q p) = k p := hG ((hK (q p)).trans (Prod.ext (hs p) (ht p)).symm)
  have hKc : Continuous K := hq.continuous_iff.mpr (hk.congr fun p ↦ (hcomp p).symm)
  let f : a ⟶ b := ⟨⟨K,hKc⟩, fun x ↦ congrArg Prod.fst (hK x),
    fun x ↦ congrArg Prod.snd (hK x)⟩
  exact ⟨asIso f⟩

/-- Isomorphism of continuous points is the equivalence relation underlying
their presheaf of classes. -/
def pointIsoSetoid (T : CGWH.{u}) : Setoid (G.Points T) where
  r a b := Nonempty (a ≅ b)
  iseqv := {
    refl a := ⟨Iso.refl a⟩
    symm := fun ⟨i⟩ ↦ ⟨i.symm⟩
    trans := fun ⟨i⟩ ⟨j⟩ ↦ ⟨i ≪≫ j⟩ }

private theorem rankPoint_pullback_id (T : RankSpace α) (a : G.Points T.space) :
    (G.restrictPoints ((rankSpaceInclusion α).map (𝟙 T)).hom.hom.hom).obj a = a := by
  rw [(rankSpaceInclusion α).map_id]
  exact ContinuousMap.ext fun _ ↦ rfl

private theorem rankPoint_pullback_comp {R S T : RankSpace α}
    (f : S ⟶ T) (g : R ⟶ S) (a : G.Points T.space) :
    (G.restrictPoints ((rankSpaceInclusion α).map (g ≫ f)).hom.hom.hom).obj a =
    (G.restrictPoints ((rankSpaceInclusion α).map g).hom.hom.hom).obj
      ((G.restrictPoints ((rankSpaceInclusion α).map f).hom.hom.hom).obj a) := by
  rw [(rankSpaceInclusion α).map_comp]
  exact ContinuousMap.ext fun _ ↦ rfl

/-- Isomorphism classes of actual continuous points over the rank site. -/
def rankPointClasses (α : Ordinal.{u}) : (RankSpace α)ᵒᵖ ⥤ Type u where
  obj X := Quotient (G.pointIsoSetoid X.unop.space)
  map {X Y} f := TypeCat.ofHom (Quotient.map'
    ((G.restrictPoints ((rankSpaceInclusion α).map f.unop).hom.hom.hom).obj)
    (fun _ _ ⟨i⟩ ↦ ⟨(G.restrictPoints ((rankSpaceInclusion α).map f.unop).hom.hom.hom).mapIso i⟩))
  map_id X := by
    apply ConcreteCategory.hom_ext
    intro a
    refine Quotient.inductionOn a (fun A ↦ ?_)
    exact congrArg Quotient.mk'' (rankPoint_pullback_id G X.unop A)
  map_comp {X Y Z} f g := by
    apply ConcreteCategory.hom_ext
    intro a
    refine Quotient.inductionOn a (fun A ↦ ?_)
    exact congrArg Quotient.mk'' (rankPoint_pullback_comp G f.unop g.unop A)

local notation "J" => Sheaf.canonicalTopology (RankSpace α)
local notation "P" => rankPointClasses G α

/-- The sheaf of local continuous-point classes. Its discrete groupoids give
the thin quotient-stack model. -/
abbrev thinQuotientSheaf (α : Ordinal.{u}) : (RankSpace α)ᵒᵖ ⥤ Type u :=
  (Sheaf.canonicalTopology (RankSpace α)).sheafify (rankPointClasses G α)

private abbrev pointClass (T : RankSpace α) (a : G.Points T.space) : (P).obj (Opposite.op T) :=
  Quotient.mk'' a

/-- The comparison from actual points to local point classes. -/
def thinQuotientSection (α : Ordinal.{u}) (T : RankSpace α) (a : G.Points T.space) :
    (thinQuotientSheaf G α).obj (Opposite.op T) :=
  ((Sheaf.canonicalTopology (RankSpace α)).toSheafify (rankPointClasses G α)).app
    (Opposite.op T) (pointClass G T a)

/-- Two presenting points have the same image precisely when they have a
continuous arrow. Local equality in sheafification suffices by descent of
the arrow over the whole canonical sieve. -/
theorem thinQuotientSection_eq_iff (hG : Injective (ordinaryEndpoints G))
    (hα : preBeth α = α.card) (hω : ℵ₀ < preBeth α)
    (T : RankSpace α) (a b : G.Points T.space) :
    thinQuotientSection G α T a = thinQuotientSection G α T b ↔ Nonempty (a ≅ b) := by
  constructor
  · intro hab
    letI := Presheaf.isLocallyInjective_toSheafify (J) (P)
    let S := Presheaf.equalizerSieve (F := P) (X := Opposite.op T)
      (pointClass G T a) (pointClass G T b)
    have hS : S ∈ J T := Presheaf.equalizerSieve_mem J ((J).toSheafify (P)) _ _ hab
    apply pointIso_of_rankLocalIso G hG hα hω S hS a b
    intro i
    exact Quotient.exact i.2.property
  · rintro ⟨i⟩
    exact congrArg (fun x ↦ ((J).toSheafify (P)).app (Opposite.op T) (x))
      (Quotient.sound (s := G.pointIsoSetoid T.space) ⟨i⟩)

/-- Every sheafified section has actual presenting points on a canonical
cover. This permits arbitrary sieve covers, including those without a
single rank-bounded covering object. -/
theorem thinQuotientSection_localLift (T : RankSpace α)
    (x : (thinQuotientSheaf G α).obj (Opposite.op T)) :
    ∃ S : Sieve T, S ∈ J T ∧
      ∀ ⦃Y : RankSpace α⦄ (f : Y ⟶ T), S f →
        ∃ a : G.Points Y.space, thinQuotientSection G α Y a = (thinQuotientSheaf G α).map f.op x := by
  let φ := (J).toSheafify (P)
  letI : Presheaf.IsLocallySurjective J φ := Presheaf.isLocallySurjective_toSheafify (J) (P)
  refine ⟨Presheaf.imageSieve φ x, Presheaf.imageSieve_mem J φ x, ?_⟩
  intro Y f hf
  obtain ⟨p,hp⟩ := hf
  obtain ⟨a,ha⟩ := Quotient.exists_rep p
  refine ⟨a, ?_⟩
  have he : pointClass G Y a = p := ha
  change φ.app _ (pointClass G Y a) = _
  rw [he]
  exact hp

end Masullo.TopologicalGroupoid

namespace Masullo.BasedInertia

open CategoryTheory.Functor CategoryTheory.IsHomLift

universe v

variable {D : Type v} [SmallCategory D] (X : BasedCategory.{v,v} D)

/-- Insert the identity automorphism into the based inertia. -/
def identitySection : X ⥤ᵇ based X where
  toFunctor := {
    obj a := ⟨a, Iso.refl a, IsHomLift.id rfl⟩
    map f := ⟨f, by simp⟩
    map_id _ := rfl
    map_comp _ _ := rfl }
  w := rfl

private theorem loop_hom_eq_id_of_faithful [X.p.Faithful] (a : Obj X) :
    a.loop.hom = 𝟙 a.point := by
  letI := a.vertical
  apply X.p.map_injective
  rw [X.p.map_id]
  simpa using (fac' X.p (𝟙 (X.p.obj a.point)) a.loop.hom)

private def identitySectionComponent [X.p.Faithful] (a : Obj X) :
    a ≅ (identitySection X).obj a.point where
  hom := ⟨𝟙 a.point, by
    change 𝟙 a.point ≫ 𝟙 a.point = a.loop.hom ≫ 𝟙 a.point
    rw [loop_hom_eq_id_of_faithful X a]⟩
  inv := ⟨𝟙 a.point, by
    change 𝟙 a.point ≫ a.loop.hom = 𝟙 a.point ≫ 𝟙 a.point
    rw [loop_hom_eq_id_of_faithful X a]⟩
  hom_inv_id := Arrow.ext (Category.id_comp _)
  inv_hom_id := Arrow.ext (Category.id_comp _)

/-- Inertia of a category with faithful projection has the identity section
as a quasi-inverse over the base. -/
def forgetUnitOfFaithful [X.p.Faithful] :
    BasedFunctor.id (based X) ≅ forgetBased X ⋙ identitySection X :=
  BasedNatIso.mkNatIso
    (NatIso.ofComponents (identitySectionComponent X) (fun m ↦ by
      apply Arrow.ext
      exact (Category.comp_id _).trans (Category.id_comp _).symm))
    (fun a ↦ by
      apply IsHomLift.of_fac' _ _ _ rfl rfl
      simp only [eqToHom_refl, Category.id_comp]
      change X.p.map (𝟙 a.point) = 𝟙 (X.p.obj a.point) ≫ 𝟙 (X.p.obj a.point)
      rw [Category.id_comp, X.p.map_id])

/-- The other composite of the inertia projection and the identity section
is the identity, with the comparison lying over the base identity. -/
def forgetCounit :
    identitySection X ⋙ forgetBased X ≅ BasedFunctor.id X :=
  BasedNatIso.mkNatIso
    (NatIso.ofComponents (fun a ↦ Iso.refl a) (fun m ↦ by
      change m ≫ 𝟙 _ = 𝟙 _ ≫ m
      simp))
    (fun a ↦ by
      apply IsHomLift.of_fac' _ _ _ rfl rfl
      simp only [eqToHom_refl, Category.id_comp]
      change X.p.map (𝟙 a) = 𝟙 (X.p.obj a) ≫ 𝟙 (X.p.obj a)
      rw [Category.id_comp, X.p.map_id])

/-- Inserting the identity preserves Cartesian arrows when every vertical
automorphism is the identity. -/
theorem identitySection_preserves [X.p.Faithful] :
    Masullo.VerticalIsoComma.PreservesCartesian (identitySection X) := by
  intro R S a b f m hm
  letI := hm
  let I := identitySection X
  let U := forgetBased X
  refine { toIsHomLift := I.preserves_isHomLift f m, universal_property' := ?_ }
  intro c g n hn
  letI := hn
  let n₀ : c.point ⟶ b := n.hom
  haveI : X.p.IsHomLift (g ≫ f) n₀ := U.preserves_isHomLift (g ≫ f) n
  obtain ⟨r,⟨hr,he⟩,hu⟩ := IsStronglyCartesian.universal_property X.p f m
    (a' := c.point) g (g ≫ f) rfl n₀
  let k : c ⟶ I.obj a := ⟨r, by
    change r ≫ 𝟙 a = c.loop.hom ≫ r
    rw [loop_hom_eq_id_of_faithful X c, Category.comp_id, Category.id_comp]⟩
  haveI : X.p.IsHomLift g (U.map k) := hr
  refine ⟨k,⟨U.isHomLift_map g k,Arrow.ext he⟩,?_⟩
  rintro l ⟨hl,hle⟩
  letI := hl
  apply Arrow.ext
  exact hu l.hom ⟨U.preserves_isHomLift g l, congrArg Arrow.hom hle⟩

end Masullo.BasedInertia

namespace Masullo.TopologicalGroupoid

universe u
variable {α : Ordinal.{u}} (G : TopologicalGroupoid.{u})

/-- The discrete fibres are a sheaf, so their descent works for every
canonical covering sieve. -/
theorem thinQuotientSheaf_isSheaf :
    Presheaf.IsSheaf (Sheaf.canonicalTopology (RankSpace α)) (thinQuotientSheaf G α) :=
  (Sheaf.canonicalTopology (RankSpace α)).sheafify_isSheaf _

/-- The comparison into each discrete stack fibre. -/
def thinQuotientPoints (T : RankSpace α) :
    G.Points T.space ⥤ Discrete ((thinQuotientSheaf G α).obj (Opposite.op T)) where
  obj a := Discrete.mk (thinQuotientSection G α T a)
  map f := Discrete.eqToHom'
    (congrArg (fun x ↦ ((Sheaf.canonicalTopology (RankSpace α)).toSheafify
      (rankPointClasses G α)).app (Opposite.op T) (x))
      (Quotient.sound (s := G.pointIsoSetoid T.space) ⟨asIso f⟩))
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

theorem thinQuotientPoints_fullyFaithful (hG : Injective (ordinaryEndpoints G))
    (hα : preBeth α = α.card) (hω : ℵ₀ < preBeth α) (T : RankSpace α) :
    Nonempty (thinQuotientPoints G T).FullyFaithful := by
  apply (Functor.FullyFaithful.nonempty_iff_map_bijective _).mpr
  intro a b
  refine ⟨fun r s _ ↦ (pointHom_subsingleton G hG a b).elim r s, ?_⟩
  intro f
  obtain ⟨e⟩ := (thinQuotientSection_eq_iff G hG hα hω T a b).mp (Discrete.eq_of_hom f)
  exact ⟨e.hom, Subsingleton.elim _ _⟩

/-- The fibrewise comparison respects change of the rank test space. -/
theorem thinQuotientSection_natural {S T : RankSpace α} (f : S ⟶ T) (a : G.Points T.space) :
    thinQuotientSection G α S
      ((G.restrictPoints ((rankSpaceInclusion α).map f).hom.hom.hom).obj a) =
    (thinQuotientSheaf G α).map f.op (thinQuotientSection G α T a) :=
  (NatTrans.naturality_apply
    ((Sheaf.canonicalTopology (RankSpace α)).toSheafify (rankPointClasses G α))
    f.op (pointClass G T a))

/-- Pullback and the presentation comparison commute as functors of
groupoids. The comparison isomorphisms are unique on each object. -/
def thinQuotientPoints_pullbackIso {S T : RankSpace α} (f : S ⟶ T) :
    G.restrictPoints ((rankSpaceInclusion α).map f).hom.hom.hom ⋙ thinQuotientPoints G S ≅
      thinQuotientPoints G T ⋙ Discrete.functor
        (fun x ↦ Discrete.mk ((thinQuotientSheaf G α).map f.op x)) :=
  NatIso.ofComponents
    (fun a ↦ eqToIso (congrArg Discrete.mk (thinQuotientSection_natural G f a)))
    (fun _ ↦ Subsingleton.elim _ _)

/-- Based category of the thin quotient stack, with the objects and
arrows of its discrete fibres. -/
def thinQuotientBased (α : Ordinal.{u}) : BasedCategory.{u,u} (RankSpace α) :=
  BasedCategory.ofFunctor ((CategoryOfElements.π (thinQuotientSheaf G α)).op ⋙ unopUnop _)

theorem thinQuotientBased_faithful (α : Ordinal.{u}) : (thinQuotientBased G α).p.Faithful := by
  unfold thinQuotientBased
  change ((CategoryOfElements.π (thinQuotientSheaf G α)).op ⋙ unopUnop _).Faithful
  infer_instance

/-- The stack of local classes is fibred. Pullback is restriction of a
section, with the actual arrows of the category of elements. -/
theorem thinQuotientBased_isFibered (α : Ordinal.{u}) : (thinQuotientBased G α).p.IsFibered := by
  let F := thinQuotientSheaf G α
  let X := thinQuotientBased G α
  let p := X.p
  letI : p.Faithful := thinQuotientBased_faithful G α
  apply CategoryTheory.Functor.IsFibered.of_exists_isStronglyCartesian
  intro a R f
  let A : F.Elements := a.unop
  let B : F.Elements := F.elementsMk (Opposite.op R) (F.map f.op A.snd)
  let b : X.obj := Opposite.op B
  let φ : b ⟶ a := (CategoryOfElements.homMk A B f.op rfl).op
  refine ⟨b,φ,?_⟩
  have hφ : p.IsHomLift f φ := CategoryTheory.IsHomLift.of_fac' p f φ rfl rfl (by simp; rfl)
  refine { toIsHomLift := hφ, universal_property' := ?_ }
  intro a' g φ' hφ'
  have hh : p.map φ' = g ≫ f := by
    simpa using (CategoryTheory.IsHomLift.fac' p (g ≫ f) φ')
  let A' : F.Elements := a'.unop
  have hA' : φ'.unop.val = f.op ≫ g.op :=
    congrArg Quiver.Hom.op hh
  have hcond : F.map g.op B.snd = A'.snd := by
    have he := congrArg (fun k : F.obj A.fst ⟶ F.obj A'.fst ↦ k A.snd) (F.map_comp f.op g.op)
    exact he.symm.trans ((congrArg (fun k : A.fst ⟶ A'.fst ↦ F.map k A.snd) hA'.symm).trans
      φ'.unop.property)
  let χ : a' ⟶ b := (CategoryOfElements.homMk B A' g.op hcond).op
  refine ⟨χ,⟨CategoryTheory.IsHomLift.of_fac' p g χ rfl rfl (by simp; rfl), ?_⟩, ?_⟩
  · apply p.map_injective
    rw [p.map_comp, hh]
    rfl
  · rintro ψ ⟨hψ, _⟩
    apply p.map_injective
    change p.map ψ = g
    have hs := CategoryTheory.IsHomLift.fac' p g ψ
    change p.map ψ = eqToHom (show p.obj a' = p.obj a' from rfl) ≫ g ≫
      eqToHom (show R = R from rfl) at hs
    simpa only [eqToHom_refl, Category.comp_id, Category.id_comp] using hs

/-- E.6.3.7. The actual inertia projection for the discrete quotient-stack
model has a quasi-inverse and both comparison isomorphisms over the base. -/
def thinQuotientInertiaEquivalence (α : Ordinal.{u}) :
    BasedInertia.Obj (thinQuotientBased G α) ≌ (thinQuotientBased G α).obj := by
  let X := thinQuotientBased G α
  letI : X.p.Faithful := thinQuotientBased_faithful G α
  exact CategoryTheory.Equivalence.mk (BasedInertia.forgetBased X).toFunctor
    (BasedInertia.identitySection X).toFunctor
    ((BasedNatTrans.forgetful (BasedInertia.based X) (BasedInertia.based X)).mapIso
      (BasedInertia.forgetUnitOfFaithful X))
    ((BasedNatTrans.forgetful X X).mapIso (BasedInertia.forgetCounit X))


/-- With injective endpoints the quotient presentation is fully faithful
on every rank test, and its inertia projection is a Cartesian equivalence. -/
theorem quotientInertia_of_injectiveEndpoints
    (hG : Injective (ordinaryEndpoints G)) (hα : preBeth α = α.card)
    (hω : ℵ₀ < preBeth α) :
    (∀ T : RankSpace α, Nonempty (thinQuotientPoints G T).FullyFaithful) ∧
      (BasedInertia.forget (thinQuotientBased G α)).IsEquivalence ∧
      Masullo.VerticalIsoComma.PreservesCartesian (BasedInertia.forgetBased (thinQuotientBased G α)) ∧
      Masullo.VerticalIsoComma.PreservesCartesian (BasedInertia.identitySection (thinQuotientBased G α)) := by
  let X := thinQuotientBased G α
  letI : X.p.Faithful := thinQuotientBased_faithful G α
  letI : X.p.IsFibered := thinQuotientBased_isFibered G α
  exact ⟨thinQuotientPoints_fullyFaithful G hG hα hω,
    (thinQuotientInertiaEquivalence G α).isEquivalence_functor,
    BasedInertia.forget_preserves X, BasedInertia.identitySection_preserves X⟩

end Masullo.TopologicalGroupoid
