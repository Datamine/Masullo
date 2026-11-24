import RankQuotientCocycles
import FiberedGrothendieck
import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
import Mathlib.CategoryTheory.Sites.Descent.IsStack

open CategoryTheory Opposite
open scoped Bicategory

namespace Masullo.TopologicalGroupoid

open QuotientCocycle

universe u

noncomputable section

variable {α : Ordinal.{u}} (G : TopologicalGroupoid.{u})

private abbrev rankCocycleCategory (X : (RankSpace α)ᵒᵖ) : Cat.{u,u+1} :=
  Cat.of (QuotientCocycle G X.unop.space)

private abbrev rankCocycleMap {X Y : (RankSpace α)ᵒᵖ} (f : X ⟶ Y) :
    rankCocycleCategory G X ⟶ rankCocycleCategory G Y :=
  (pullbackFunctor (G := G) ((rankSpaceInclusion α).map f.unop)).toCatHom

private abbrev rankCocycleMapId (X : (RankSpace α)ᵒᵖ) :
    rankCocycleMap G (𝟙 X) ≅ 𝟙 (rankCocycleCategory G X) :=
  Cat.Hom.isoMk pullbackIdNatIso

private abbrev rankCocycleMapComp {X Y Z : (RankSpace α)ᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) :
    rankCocycleMap G (f ≫ g) ≅ rankCocycleMap G f ≫ rankCocycleMap G g :=
  Cat.Hom.isoMk (pullbackCompNatIso ((rankSpaceInclusion α).map f.unop)
    ((rankSpaceInclusion α).map g.unop))

private theorem comparison_closed_path {C : Type*} [Category C] {a b c d : C}
    (f : a ⟶ b) (g : b ⟶ d) (h : a ≅ c) (k : c ≅ d)
    (e : f ≫ g = h.hom ≫ k.hom) : f ≫ g ≫ k.inv ≫ h.inv = 𝟙 a := by
  rw [← Category.assoc, e]
  simp [Category.assoc]

set_option maxHeartbeats 600000 in
/-- The cocycle categories and their restrictions form a pseudofunctor on
the manuscript's rank site. -/
def rankCocyclePseudofunctor (α : Ordinal.{u}) :
    LocallyDiscrete (RankSpace α)ᵒᵖ ⥤ᵖ Cat.{u,u+1} :=
  LocallyDiscrete.mkPseudofunctor (rankCocycleCategory G) (rankCocycleMap G)
    (rankCocycleMapId G) (rankCocycleMapComp G)
    (by
      intro X Y Z W f g h
      apply Cat.Hom₂.ext
      ext A
      change QuotientCocycle G X.unop.space at A
      let l := (rankSpaceInclusion α).map f.unop
      let m := (rankSpaceInclusion α).map g.unop
      let n := (rankSpaceInclusion α).map h.unop
      change (pullbackCompIso A (m ≫ l) n).hom ≫
        pullbackHom (pullbackCompIso A l m).hom n ≫ 𝟙 _ ≫
        (pullbackCompIso (A.pullback l) m n).inv ≫ (pullbackCompIso A l (n ≫ m)).inv = 𝟙 _
      rw [Category.id_comp]
      exact comparison_closed_path _ _ _ _ (pullbackCompIso_assoc A l m n))
    (by
      intro X Y f
      apply Cat.Hom₂.ext
      ext A
      change QuotientCocycle G X.unop.space at A
      let l := (rankSpaceInclusion α).map f.unop
      change (pullbackCompIso A (𝟙 X.unop.space) l).hom ≫
        pullbackHom (pullbackIdIso A).hom l ≫ 𝟙 _ = 𝟙 _
      exact pullbackCompIso_left_unit_with_identity A l)
    (by
      intro X Y f
      apply Cat.Hom₂.ext
      ext A
      change QuotientCocycle G X.unop.space at A
      let l := (rankSpaceInclusion α).map f.unop
      change (pullbackCompIso A l (𝟙 Y.unop.space)).hom ≫
        (pullbackIdIso (A.pullback l)).hom ≫ 𝟙 _ = 𝟙 _
      rw [Category.comp_id]
      exact pullbackCompIso_right_unit A l)

/-- The total category of quotient cocycles over the rank site. -/
abbrev RankCocycleTotal (α : Ordinal.{u}) :=
  Pseudofunctor.CoGrothendieck (rankCocyclePseudofunctor G α)

/-- The projection of the total category to the rank site. -/
abbrev rankCocycleProjection (α : Ordinal.{u}) : RankCocycleTotal G α ⥤ RankSpace α :=
  Pseudofunctor.CoGrothendieck.forget (rankCocyclePseudofunctor G α)

theorem rankCocycleProjection_isFibered (α : Ordinal.{u}) :
    (rankCocycleProjection G α).IsFibered := inferInstance

/-- The actual fibre of the total category is the quotient cocycle category. -/
def rankCocycleFiberEquivalence (X : RankSpace α) :
    QuotientCocycle G X.space ≌ Functor.Fiber (rankCocycleProjection G α) X :=
  FiberedGrothendieck.fiberModelEquivalence (rankCocyclePseudofunctor G α) X

/-- Every arrow in an actual fibre of the projection is invertible. -/
theorem rankCocycleFiber_isIso (X : RankSpace α) {A B : Functor.Fiber (rankCocycleProjection G α) X}
    (r : A ⟶ B) : IsIso r :=
  FiberedGrothendieck.fiber_all_isIso_of_groupoid (rankCocyclePseudofunctor G α)
    (fun U _ _ r ↦ @IsIso.of_groupoid (QuotientCocycle G U.space) _ _ _ r) X r

open Pseudofunctor.LocallyDiscreteOpToCat in
/-- Mathlib's restriction of a morphism between pullbacks is computed by
rebracketing the two presenting covers. -/
theorem rankCocyclePullHom_eq {X Y U V : RankSpace α} (f : U ⟶ X) (g : U ⟶ Y) (h : V ⟶ U)
    {A : QuotientCocycle G X.space} {B : QuotientCocycle G Y.space}
    (r : A.pullback ((rankSpaceInclusion α).map f) ⟶ B.pullback ((rankSpaceInclusion α).map g)) :
    pullHom (F := rankCocyclePseudofunctor G α) (M₁ := A) (M₂ := B) (f₁ := f) (f₂ := g)
      r h (h ≫ f) (h ≫ g) rfl rfl =
      pullbackRebracketHom ((rankSpaceInclusion α).map f) ((rankSpaceInclusion α).map g)
        r ((rankSpaceInclusion α).map h) := by
  unfold pullHom
  let F := rankCocyclePseudofunctor G α
  have hf : F.mapComp' f.op.toLoc h.op.toLoc (h ≫ f).op.toLoc rfl =
      F.mapComp f.op.toLoc h.op.toLoc := F.mapComp'_eq_mapComp _ _
  have hg : F.mapComp' g.op.toLoc h.op.toLoc (h ≫ g).op.toLoc rfl =
      F.mapComp g.op.toLoc h.op.toLoc := F.mapComp'_eq_mapComp _ _
  rw [hf, hg]
  rfl

open Pseudofunctor.LocallyDiscreteOpToCat in
private theorem rankCocycleDescentHom_unique {X : RankSpace α} (S : Sieve X)
    (hα : Cardinal.preBeth α = α.card) (hω : Cardinal.aleph0 < Cardinal.preBeth α)
    (hS : S ∈ Sheaf.canonicalTopology (RankSpace α) X)
    (A B : QuotientCocycle G X.space)
    (r : ((rankCocyclePseudofunctor G α).toDescentData (fun i : S.arrows.category ↦ i.obj.hom)).obj A ⟶
      ((rankCocyclePseudofunctor G α).toDescentData (fun i : S.arrows.category ↦ i.obj.hom)).obj B) :
    ∃! u : A ⟶ B, ((rankCocyclePseudofunctor G α).toDescentData
      (fun i : S.arrows.category ↦ i.obj.hom)).map u = r := by
  let F := rankCocyclePseudofunctor G α
  let f (i : S.arrows.category) := i.obj.hom
  let D := F.toDescentData f
  let U := rankSpaceInclusion α
  let s : RankSieveCocycleHoms S A B := fun _ g hg ↦ r.hom (S.arrows.categoryMk g hg)
  have hc : rankSieveCocycleHomsCompatible s := by
    intro Y V g hg h p v hv
    let i := S.arrows.categoryMk g hg
    let j := S.arrows.categoryMk (h ≫ g) (S.downward_closed hg h)
    let t : Over.mk (h ≫ g) ⟶ Over.mk g := Over.homMk h
    let w := (Pseudofunctor.DescentData.subtypeCompatibleHomEquiv F f).symm r
    have hcomm : t ≫ (Over.homMk g (by simp) : Over.mk g ⟶ Over.mk (𝟙 X)) =
        𝟙 (Over.mk (h ≫ g)) ≫ (Over.homMk (h ≫ g) (by simp) : Over.mk (h ≫ g) ⟶ Over.mk (𝟙 X)) := by
      ext
      change h ≫ g = 𝟙 V ≫ (h ≫ g)
      exact (Category.id_comp _).symm
    have e := w.property i j (Over.mk (h ≫ g)) t (𝟙 _) hcomm
    have hid := (F.presheafHom A B).map_id (op (Over.mk (h ≫ g)))
    rw [op_id, hid] at e
    have ev : pullHom (F := F) (M₁ := A) (M₂ := B) (f₁ := g) (f₂ := g)
        (s g hg) h (h ≫ g) (h ≫ g) rfl rfl = s (h ≫ g) (S.downward_closed hg h) := e
    have hval : (U.map (h ≫ g)).hom v = (baseOfMixed A B).hom p := hv
    let q := mixedPullbackLift A B (U.map (h ≫ g)) ⟨(v,p),hval⟩
    have hEval := pullbackRebracketHom_apply (U.map g) (U.map g) (s g hg) (U.map h) q
    have he' := (rankCocyclePullHom_eq G g g h (s g hg)).symm.trans ev
    exact hEval.symm.trans (congrArg (fun m : A.pullback (U.map (h ≫ g)) ⟶
      B.pullback (U.map (h ≫ g)) ↦ m.val.val q) he')
  obtain ⟨u,hu,huniq⟩ := (rankCanonicalSieve_pullbackHom_descends_iff_restriction S hα hω hS A B s).mpr hc
  refine ⟨u,?_,?_⟩
  · apply Pseudofunctor.DescentData.hom_ext
    intro i
    exact hu i.obj.hom i.property
  · intro v hv
    apply huniq
    intro Y g hg
    exact congrArg (fun r : D.obj A ⟶ D.obj B ↦ r.hom (S.arrows.categoryMk g hg)) hv

/-- The quotient-cocycle pseudofunctor is a prestack on the canonical rank site. -/
theorem rankCocycle_isPrestack (hα : Cardinal.preBeth α = α.card)
    (hω : Cardinal.aleph0 < Cardinal.preBeth α) :
    (rankCocyclePseudofunctor G α).IsPrestack (Sheaf.canonicalTopology (RankSpace α)) := by
  apply Pseudofunctor.IsPrestack.of_isPrestackFor
  intro X S hS
  constructor
  apply (Functor.FullyFaithful.nonempty_iff_map_bijective _).mpr
  intro A B
  constructor
  · intro a b e
    obtain ⟨u,hu,unique⟩ := rankCocycleDescentHom_unique G S hα hω hS A B
      (((rankCocyclePseudofunctor G α).toDescentData (fun i : S.arrows.category ↦ i.obj.hom)).map b)
    exact (unique a e).trans (unique b rfl).symm
  · intro r
    obtain ⟨u,hu,_⟩ := rankCocycleDescentHom_unique G S hα hω hS A B r
    exact ⟨u,hu⟩

end

end Masullo.TopologicalGroupoid
