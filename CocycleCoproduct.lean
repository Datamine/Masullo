import TopologicalQuotientFullFaithfulness
import Mathlib.CategoryTheory.Pi.Basic

/-! Quotient cocycles on disjoint unions of test spaces. -/

open CategoryTheory CategoryTheory.Limits Function Set Topology TopologicalSpace

noncomputable section

namespace Masullo.TopologicalGroupoid.QuotientCocycle

universe u

variable {I : Type u}

abbrev sumSpace (X : I → CGWH.{u}) : CGWH.{u} := (CGWH.coproductCofan X).pt

abbrev sumInclusion (X : I → CGWH.{u}) (i : I) : X i ⟶ sumSpace X :=
  (CGWH.coproductCofan X).inj i

private abbrev sumMk (X : I → CGWH.{u}) (i : I) :
    (X i).obj → (sumSpace X).obj :=
  @Sigma.mk I (fun j ↦ ((X j).obj : Type u)) i

private theorem sumMk_inj (X : I → CGWH.{u}) (i : I) : Injective (sumMk X i) :=
  sigma_mk_injective

/-- A family of maps into the corresponding summands. -/
def sumMap {X Y : I → CGWH.{u}} (f : ∀ i, X i ⟶ Y i) : sumSpace X ⟶ sumSpace Y :=
  CGWH.map ⟨fun p : Σ i, (X i).obj ↦ ⟨p.1,(f p.1).hom p.2⟩, continuous_sigma fun i ↦
    continuous_sigmaMk.comp (f i).hom.hom.hom.continuous⟩

theorem sumMap_quotient {X Y : I → CGWH.{u}} (f : ∀ i, X i ⟶ Y i)
    (h : ∀ i, IsQuotientMap (f i).hom) : IsQuotientMap (sumMap f).hom := by
  refine ⟨IsCoinducing.of_isOpen_preimage_iff_isOpen fun s ↦ ⟨?_,?_⟩,?_⟩
  · intro hs
    apply isOpen_sigma_iff.mpr
    intro i
    exact (h i).isOpen_preimage.mp (isOpen_sigma_iff.mp hs i)
  · exact fun hs ↦ hs.preimage (sumMap f).hom.hom.hom.continuous
  · rintro ⟨i,y⟩
    obtain ⟨x,hx⟩ := (h i).surjective y
    exact ⟨⟨i,x⟩,congrArg (Sigma.mk i) hx⟩

private abbrev SumFibre {X Y Z : I → CGWH.{u}} (f : ∀ i, X i ⟶ Z i) (g : ∀ i, Y i ⟶ Z i) :=
  CGWH.FibreSubspace (sumMap f) (sumMap g)

private def pairInclusion {X Y Z : I → CGWH.{u}}
    (f : ∀ i, X i ⟶ Z i) (g : ∀ i, Y i ⟶ Z i) (i : I) :
    C(CGWH.FibreSubspace (f i) (g i), SumFibre f g) := by
  letI : CompactlyGeneratedSpace (CGWH.FibreSubspace (f i) (g i)) :=
    closed_compactlyGenerated (CGWH.fibreSubspace_isClosed (f i) (g i))
  let a : C(CGWH.FibreSubspace (f i) (g i), (sumSpace X).obj) := ⟨fun p ↦ ⟨i,p.val.1⟩,
    continuous_sigmaMk.comp (continuous_fst.comp (continuous_Kelley_forget.comp continuous_subtype_val))⟩
  let b : C(CGWH.FibreSubspace (f i) (g i), (sumSpace Y).obj) := ⟨fun p ↦ ⟨i,p.val.2⟩,
    continuous_sigmaMk.comp (continuous_snd.comp (continuous_Kelley_forget.comp continuous_subtype_val))⟩
  exact ⟨fun p ↦ ⟨(a p,b p),congrArg (Sigma.mk i) p.property⟩,
    (kelleyPair a b).continuous.subtype_mk _⟩

private theorem pairInclusion_bijective {X Y Z : I → CGWH.{u}}
    (f : ∀ i, X i ⟶ Z i) (g : ∀ i, Y i ⟶ Z i) :
    Bijective (fun p : Σ i, CGWH.FibreSubspace (f i) (g i) ↦ pairInclusion f g p.1 p.2) := by
  constructor
  · rintro ⟨i,p⟩ ⟨j,q⟩ h
    have h₁ := congrArg (fun r : SumFibre f g ↦ r.val.1) h
    have h₂ := congrArg (fun r : SumFibre f g ↦ r.val.2) h
    have hij : i = j := congrArg Sigma.fst h₁
    subst j
    exact congrArg (Sigma.mk i) (Subtype.ext (Prod.ext (sumMk_inj X i h₁) (sumMk_inj Y i h₂)))
  · rintro ⟨⟨⟨i,x⟩,⟨j,y⟩⟩,h⟩
    have hij : i = j := congrArg Sigma.fst h
    subst j
    exact ⟨⟨i,⟨(x,y),sumMk_inj Z i h⟩⟩,rfl⟩

private def fibreSummand {X Y Z : I → CGWH.{u}}
    (f : ∀ i, X i ⟶ Z i) (g : ∀ i, Y i ⟶ Z i) (i : I) : Set (SumFibre f g) :=
  {p | p.val.1 ∈ range (sumMk X i)}

private theorem fibreSummand_isOpen {X Y Z : I → CGWH.{u}}
    (f : ∀ i, X i ⟶ Z i) (g : ∀ i, Y i ⟶ Z i) (i : I) :
    IsOpen (fibreSummand f g i) :=
  (show IsOpen (range (sumMk X i)) from isOpen_range_sigmaMk).preimage
    (continuous_fst.comp (continuous_Kelley_forget.comp continuous_subtype_val))

private theorem fibreSummand_isClosed {X Y Z : I → CGWH.{u}}
    (f : ∀ i, X i ⟶ Z i) (g : ∀ i, Y i ⟶ Z i) (i : I) :
    IsClosed (fibreSummand f g i) :=
  (show IsClosed (range (sumMk X i)) from isClosed_range_sigmaMk).preimage
    (continuous_fst.comp (continuous_Kelley_forget.comp continuous_subtype_val))

private def pairOnSummand {X Y Z : I → CGWH.{u}}
    (f : ∀ i, X i ⟶ Z i) (g : ∀ i, Y i ⟶ Z i) (i : I) :
    C(fibreSummand f g i, CGWH.FibreSubspace (f i) (g i)) := by
  let T := SumFibre f g
  let S := fibreSummand f g i
  letI : CompactlyGeneratedSpace T := closed_compactlyGenerated (CGWH.fibreSubspace_isClosed _ _)
  letI : CompactlyGeneratedSpace S := closed_compactlyGenerated (fibreSummand_isClosed f g i)
  let ex := (IsEmbedding.sigmaMk (i := i) (σ := fun i ↦ ((X i).obj : Type u))).toHomeomorph
  let ey := (IsEmbedding.sigmaMk (i := i) (σ := fun i ↦ ((Y i).obj : Type u))).toHomeomorph
  have hr (p : S) : p.val.val.2 ∈ range (sumMk Y i) := by
    obtain ⟨x,hx⟩ := p.property
    rcases hp : p.val.val.2 with ⟨j,y⟩
    have he : i = j := (congrArg Sigma.fst hx).trans
      ((congrArg Sigma.fst p.val.property).trans (congrArg Sigma.fst hp))
    subst j
    exact ⟨y,rfl⟩
  let x₀ : C(S, range (sumMk X i)) :=
    ⟨fun p ↦ ⟨p.val.val.1,p.property⟩, (continuous_fst.comp
      (continuous_Kelley_forget.comp (continuous_subtype_val.comp continuous_subtype_val))).subtype_mk _⟩
  let y₀ : C(S, range (sumMk Y i)) :=
    ⟨fun p ↦ ⟨p.val.val.2,hr p⟩, (continuous_snd.comp
      (continuous_Kelley_forget.comp (continuous_subtype_val.comp continuous_subtype_val))).subtype_mk _⟩
  let x : C(S,(X i).obj) := ⟨fun p ↦ ex.symm (x₀ p),ex.symm.continuous.comp x₀.continuous⟩
  let y : C(S,(Y i).obj) := ⟨fun p ↦ ey.symm (y₀ p),ey.symm.continuous.comp y₀.continuous⟩
  have hx (p : S) : sumMk X i (x p) = p.val.val.1 := congrArg Subtype.val (ex.apply_symm_apply (x₀ p))
  have hy (p : S) : sumMk Y i (y p) = p.val.val.2 := congrArg Subtype.val (ey.apply_symm_apply (y₀ p))
  have h (p : S) : (f i).hom (x p) = (g i).hom (y p) :=
    sumMk_inj Z i (((congrArg (sumMap f).hom (hx p)).trans p.val.property).trans
      (congrArg (sumMap g).hom (hy p)).symm)
  exact ⟨fun p ↦ ⟨(x p,y p),h p⟩, (kelleyPair x y).continuous.subtype_mk _⟩

private theorem pairOnSummand_inv {X Y Z : I → CGWH.{u}}
    (f : ∀ i, X i ⟶ Z i) (g : ∀ i, Y i ⟶ Z i) (i : I) (p : fibreSummand f g i) :
    pairInclusion f g i (pairOnSummand f g i p) = p.val := by
  apply Subtype.ext
  exact Prod.ext
    (congrArg Subtype.val ((IsEmbedding.sigmaMk (i := i)
      (σ := fun j ↦ ((X j).obj : Type u))).toHomeomorph.apply_symm_apply ⟨p.val.val.1,p.property⟩))
    (congrArg Subtype.val ((IsEmbedding.sigmaMk (i := i)
      (σ := fun j ↦ ((Y j).obj : Type u))).toHomeomorph.apply_symm_apply ⟨p.val.val.2,_⟩))

/-- Fibre products of maps between corresponding disjoint summands are
the ordinary disjoint unions of their CGWH fibre products. -/
def coproductFibreHomeomorph {X Y Z : I → CGWH.{u}}
    (f : ∀ i, X i ⟶ Z i) (g : ∀ i, Y i ⟶ Z i) :
    (Σ i, CGWH.FibreSubspace (f i) (g i)) ≃ₜ SumFibre f g := by
  let E := Equiv.ofBijective _ (pairInclusion_bijective f g)
  refine ⟨E,continuous_sigma fun i ↦ (pairInclusion f g i).continuous,?_⟩
  apply continuous_iff_continuousAt.mpr
  intro p
  let i := p.val.1.1
  have hp : p ∈ fibreSummand f g i := ⟨p.val.1.2,rfl⟩
  have he (q : fibreSummand f g i) : E.symm q.val = ⟨i,pairOnSummand f g i q⟩ :=
    E.symm_apply_eq.mpr (pairOnSummand_inv f g i q).symm
  apply (show ContinuousOn E.symm (fibreSummand f g i) from
    (continuousOn_iff_continuous_domRestrict).mpr ?_).continuousAt
    ((fibreSummand_isOpen f g i).mem_nhds hp)
  have hι : Continuous (@Sigma.mk I (fun j ↦ CGWH.FibreSubspace (f j) (g j)) i) := continuous_sigmaMk
  exact (hι.comp (pairOnSummand f g i).continuous).congr (fun q ↦ (he q).symm)

/-- The map out of the disjoint union specified by the maps on its summands. -/
def sumDesc {X : I → CGWH.{u}} {Z : CGWH.{u}} (f : ∀ i, X i ⟶ Z) : sumSpace X ⟶ Z :=
  CGWH.map ⟨fun p : Σ i, (X i).obj ↦ (f p.1).hom p.2,
    continuous_sigma fun i ↦ (f i).hom.hom.hom.continuous⟩

section CrossFibre

variable {J : Type u} {X : I → CGWH.{u}} {Y : J → CGWH.{u}} {Z : CGWH.{u}}
  (f : ∀ i, X i ⟶ Z) (g : ∀ j, Y j ⟶ Z)

/-- The overlap of two individual summands maps into the overlap of the
two disjoint unions over their common target. -/
def crossPairInclusion (i : I) (j : J) :
    C(CGWH.FibreSubspace (f i) (g j), CGWH.FibreSubspace (sumDesc f) (sumDesc g)) := by
  letI : CompactlyGeneratedSpace (CGWH.FibreSubspace (f i) (g j)) :=
    closed_compactlyGenerated (CGWH.fibreSubspace_isClosed (f i) (g j))
  let a : C(CGWH.FibreSubspace (f i) (g j), (sumSpace X).obj) := ⟨fun p ↦ ⟨i,p.val.1⟩,
    continuous_sigmaMk.comp (continuous_fst.comp (continuous_Kelley_forget.comp continuous_subtype_val))⟩
  let b : C(CGWH.FibreSubspace (f i) (g j), (sumSpace Y).obj) := ⟨fun p ↦ ⟨j,p.val.2⟩,
    continuous_sigmaMk.comp (continuous_snd.comp (continuous_Kelley_forget.comp continuous_subtype_val))⟩
  exact ⟨fun p ↦ ⟨(a p,b p),p.property⟩,(kelleyPair a b).continuous.subtype_mk _⟩

private theorem crossPairInclusion_bijective :
    Bijective (fun p : Σ k : I × J, CGWH.FibreSubspace (f k.1) (g k.2) ↦
      crossPairInclusion f g p.1.1 p.1.2 p.2) := by
  constructor
  · rintro ⟨⟨i,j⟩,p⟩ ⟨⟨i',j'⟩,q⟩ h
    have h₁ := congrArg (fun r : CGWH.FibreSubspace (sumDesc f) (sumDesc g) ↦ r.val.1) h
    have h₂ := congrArg (fun r : CGWH.FibreSubspace (sumDesc f) (sumDesc g) ↦ r.val.2) h
    have hi : i = i' := congrArg Sigma.fst h₁
    have hj : j = j' := congrArg Sigma.fst h₂
    subst i'
    subst j'
    exact congrArg (Sigma.mk (i,j)) (Subtype.ext (Prod.ext (sumMk_inj X i h₁) (sumMk_inj Y j h₂)))
  · rintro ⟨⟨⟨i,x⟩,⟨j,y⟩⟩,h⟩
    exact ⟨⟨(i,j),⟨(x,y),h⟩⟩,rfl⟩

private def crossFibreSummand (i : I) (j : J) : Set (CGWH.FibreSubspace (sumDesc f) (sumDesc g)) :=
  {p | p.val.1 ∈ range (sumMk X i) ∧ p.val.2 ∈ range (sumMk Y j)}

private theorem crossFibreSummand_isClopen (i : I) (j : J) :
    IsClopen (crossFibreSummand f g i j) := by
  have h₁ : Continuous (fun p : CGWH.FibreSubspace (sumDesc f) (sumDesc g) ↦ p.val.1) :=
    continuous_fst.comp (continuous_Kelley_forget.comp continuous_subtype_val)
  have h₂ : Continuous (fun p : CGWH.FibreSubspace (sumDesc f) (sumDesc g) ↦ p.val.2) :=
    continuous_snd.comp (continuous_Kelley_forget.comp continuous_subtype_val)
  exact ⟨(isClosed_range_sigmaMk.preimage h₁).inter (isClosed_range_sigmaMk.preimage h₂),
    (isOpen_range_sigmaMk.preimage h₁).inter (isOpen_range_sigmaMk.preimage h₂)⟩

private def crossPairOnSummand (i : I) (j : J) :
    C(crossFibreSummand f g i j, CGWH.FibreSubspace (f i) (g j)) := by
  let T := CGWH.FibreSubspace (sumDesc f) (sumDesc g)
  let S := crossFibreSummand f g i j
  letI : CompactlyGeneratedSpace T := closed_compactlyGenerated (CGWH.fibreSubspace_isClosed _ _)
  letI : CompactlyGeneratedSpace S := closed_compactlyGenerated (crossFibreSummand_isClopen f g i j).1
  let ex := (IsEmbedding.sigmaMk (i := i) (σ := fun i ↦ ((X i).obj : Type u))).toHomeomorph
  let ey := (IsEmbedding.sigmaMk (i := j) (σ := fun j ↦ ((Y j).obj : Type u))).toHomeomorph
  let x₀ : C(S, range (sumMk X i)) :=
    ⟨fun p ↦ ⟨p.val.val.1,p.property.1⟩, (continuous_fst.comp
      (continuous_Kelley_forget.comp (continuous_subtype_val.comp continuous_subtype_val))).subtype_mk _⟩
  let y₀ : C(S, range (sumMk Y j)) :=
    ⟨fun p ↦ ⟨p.val.val.2,p.property.2⟩, (continuous_snd.comp
      (continuous_Kelley_forget.comp (continuous_subtype_val.comp continuous_subtype_val))).subtype_mk _⟩
  let x : C(S,(X i).obj) := ⟨fun p ↦ ex.symm (x₀ p),ex.symm.continuous.comp x₀.continuous⟩
  let y : C(S,(Y j).obj) := ⟨fun p ↦ ey.symm (y₀ p),ey.symm.continuous.comp y₀.continuous⟩
  have hx (p : S) : sumMk X i (x p) = p.val.val.1 := congrArg Subtype.val (ex.apply_symm_apply (x₀ p))
  have hy (p : S) : sumMk Y j (y p) = p.val.val.2 := congrArg Subtype.val (ey.apply_symm_apply (y₀ p))
  have h (p : S) : (f i).hom (x p) = (g j).hom (y p) :=
    ((congrArg (sumDesc f).hom (hx p)).trans p.val.property).trans (congrArg (sumDesc g).hom (hy p)).symm
  exact ⟨fun p ↦ ⟨(x p,y p),h p⟩,(kelleyPair x y).continuous.subtype_mk _⟩

/-- Overlaps of maps out of disjoint unions decompose into the disjoint
union of every pairwise CGWH overlap, including distinct summands. -/
def crossCoproductFibreHomeomorph : (Σ k : I × J, CGWH.FibreSubspace (f k.1) (g k.2)) ≃ₜ
    CGWH.FibreSubspace (sumDesc f) (sumDesc g) := by
  let E := Equiv.ofBijective _ (crossPairInclusion_bijective f g)
  refine ⟨E, continuous_sigma fun k ↦ (crossPairInclusion f g k.1 k.2).continuous,?_⟩
  apply continuous_iff_continuousAt.mpr
  intro p
  let i := p.val.1.1
  let j := p.val.2.1
  have hp : p ∈ crossFibreSummand f g i j := ⟨⟨p.val.1.2,rfl⟩,⟨p.val.2.2,rfl⟩⟩
  have he (q : crossFibreSummand f g i j) : E.symm q.val = ⟨(i,j),crossPairOnSummand f g i j q⟩ := by
    apply E.symm_apply_eq.mpr
    symm
    apply Subtype.ext
    exact Prod.ext
      (congrArg Subtype.val ((IsEmbedding.sigmaMk (i := i)
        (σ := fun i ↦ ((X i).obj : Type u))).toHomeomorph.apply_symm_apply ⟨q.val.val.1,q.property.1⟩))
      (congrArg Subtype.val ((IsEmbedding.sigmaMk (i := j)
        (σ := fun j ↦ ((Y j).obj : Type u))).toHomeomorph.apply_symm_apply ⟨q.val.val.2,q.property.2⟩))
  apply (show ContinuousOn E.symm (crossFibreSummand f g i j) from
    (continuousOn_iff_continuous_domRestrict).mpr ?_).continuousAt
    ((crossFibreSummand_isClopen f g i j).2.mem_nhds hp)
  have hι : Continuous (@Sigma.mk (I × J) (fun k ↦ CGWH.FibreSubspace (f k.1) (g k.2)) (i,j)) :=
    continuous_sigmaMk
  exact (hι.comp (crossPairOnSummand f g i j).continuous).congr (fun q ↦ (he q).symm)

/-- The overlap homeomorphism uses the given inclusions on each pair of summands. -/
theorem crossCoproductFibreHomeomorph_apply (i : I) (j : J) (p : CGWH.FibreSubspace (f i) (g j)) :
    crossCoproductFibreHomeomorph f g ⟨(i,j),p⟩ = crossPairInclusion f g i j p := rfl

end CrossFibre

section FamilyMorphismDescent

variable {G : TopologicalGroupoid.{u}} {T : I → CGWH.{u}} {Z : CGWH.{u}}
  (f : ∀ i, T i ⟶ Z) (A B : QuotientCocycle G Z)

/-- Forget the choice of domain in a jointly quotient family from the
common cover of the restricted cocycles. -/
def familyMixedPullback :
    C((Σ i, CGWH.FibreSubspace (A.pullback (f i)).cover (B.pullback (f i)).cover),
      CGWH.FibreSubspace A.cover B.cover) :=
  ⟨fun p ↦ mixedPullback A B (f p.1) p.2,
    continuous_sigma fun i ↦ (mixedPullback A B (f i)).continuous⟩

/-- The common cover is a quotient of the disjoint union of the common
covers over a jointly quotient family. Neither local map needs to be
individually surjective for this argument. -/
theorem familyMixedPullback_quotient (hf : IsQuotientMap (sumDesc f).hom) :
    IsQuotientMap (familyMixedPullback f A B) := by
  let M := mixedTest A B
  let Y : PUnit.{u+1} → CGWH.{u} := fun _ ↦ M
  let g (j : PUnit.{u+1}) : Y j ⟶ Z := baseOfMixed A B
  let r : sumSpace Y ⟶ M := sumDesc (fun _ ↦ 𝟙 M)
  have hr : IsQuotientMap r.hom := by
    apply IsQuotientMap.of_comp (sumInclusion Y PUnit.unit).hom.hom.hom.continuous
      r.hom.hom.hom.continuous
    exact IsQuotientMap.id
  let e := crossCoproductFibreHomeomorph f g
  let v : C(CGWH.FibreSubspace (sumDesc f) (sumDesc g), (sumSpace Y).obj) :=
    ⟨fun p ↦ p.val.2,continuous_snd.comp (continuous_Kelley_forget.comp continuous_subtype_val)⟩
  have hv : IsQuotientMap v := CGWH.quotient_baseChange (sumDesc f) (sumDesc g) hf
  let k : C((Σ s : I × PUnit.{u+1}, CGWH.FibreSubspace (f s.1) (g s.2)),
      (Σ i, CGWH.FibreSubspace (A.pullback (f i)).cover (B.pullback (f i)).cover)) :=
    ⟨fun p ↦ ⟨p.1.1,mixedPullbackLift A B (f p.1.1) p.2⟩,
      continuous_sigma fun s ↦ (continuous_sigmaMk (i := s.1)).comp
        (mixedPullbackLift A B (f s.1)).continuous⟩
  apply IsQuotientMap.of_comp k.continuous (familyMixedPullback f A B).continuous
  have he : (familyMixedPullback f A B) ∘ k = r.hom ∘ v ∘ e := by
    funext p
    rcases p with ⟨⟨i,j⟩,p⟩
    exact mixedPullback_lift A B (f i) p
  rw [he]
  exact hr.comp (hv.comp e.isQuotientMap)

/-- Arrows between the restrictions of two global cocycles descend through
a jointly quotient family exactly when their values agree at common
presenting points. The global arrow is unique. -/
theorem familyPullbackHom_descends_iff (hf : IsQuotientMap (sumDesc f).hom)
    (r : ∀ i, A.pullback (f i) ⟶ B.pullback (f i)) :
    (∃! a : A ⟶ B, ∀ i, pullbackHom a (f i) = r i) ↔
      ∀ (i j : I) (p : CGWH.FibreSubspace (A.pullback (f i)).cover (B.pullback (f i)).cover)
        (q : CGWH.FibreSubspace (A.pullback (f j)).cover (B.pullback (f j)).cover),
        mixedPullback A B (f i) p = mixedPullback A B (f j) q →
          (r i).val.val p = (r j).val.val q := by
  classical
  constructor
  · rintro ⟨a,ha,_⟩ i j p q h
    rw [← ha i, ← ha j]
    exact congrArg a.val.val h
  · intro hr
    let k := familyMixedPullback f A B
    have hk : IsQuotientMap k := familyMixedPullback_quotient f A B hf
    let l : C((Σ i, CGWH.FibreSubspace (A.pullback (f i)).cover (B.pullback (f i)).cover),
        G.arrows.obj) := ⟨fun p ↦ (r p.1).val.val p.2, continuous_sigma fun i ↦ (r i).val.val.continuous⟩
    let j (p : CGWH.FibreSubspace A.cover B.cover) := (hk.surjective p).choose
    have hj (p : CGWH.FibreSubspace A.cover B.cover) : k (j p) = p := (hk.surjective p).choose_spec
    let d (p : CGWH.FibreSubspace A.cover B.cover) := l (j p)
    have hd (p : _) : d (k p) = l p := hr (j (k p)).1 p.1 (j (k p)).2 p.2 (hj (k p))
    have hcont : Continuous d := hk.continuous_iff.mpr (l.continuous.congr (fun p ↦ (hd p).symm))
    have hsrc (p : CGWH.FibreSubspace A.cover B.cover) : G.source (d p) = A.point p.val.1 := by
      obtain ⟨⟨i,q⟩,rfl⟩ := hk.surjective p
      exact (congrArg G.source (hd ⟨i,q⟩)).trans ((r i).val.property.1 q)
    have htgt (p : CGWH.FibreSubspace A.cover B.cover) : G.target (d p) = B.point p.val.2 := by
      obtain ⟨⟨i,q⟩,rfl⟩ := hk.surjective p
      exact (congrArg G.target (hd ⟨i,q⟩)).trans ((r i).val.property.2 q)
    let a : A ⟶ B := ⟨⟨⟨d,hcont⟩,hsrc,htgt⟩,by
      intro p q hp hq
      obtain ⟨⟨i,t⟩,ht⟩ := hf.surjective (A.cover.hom p.val.1)
      have ht' : (f i).hom t = A.cover.hom p.val.1 := ht
      let p' : CGWH.FibreSubspace (A.pullback (f i)).cover (B.pullback (f i)).cover :=
        mixedPullbackLift A B (f i) ⟨(t,p),ht'⟩
      let q' : CGWH.FibreSubspace (A.pullback (f i)).cover (B.pullback (f i)).cover :=
        mixedPullbackLift A B (f i) ⟨(t,q),ht'.trans hp⟩
      have ep : d p = (r i).val.val p' := hd ⟨i,p'⟩
      have eq : d q = (r i).val.val q' := hd ⟨i,q'⟩
      have h := congrArg Subtype.val ((r i).property p' q' rfl rfl)
      apply Subtype.ext
      refine Eq.trans ?_ (h.trans ?_)
      · apply congrArg G.comp
        exact Subtype.ext (Prod.ext rfl eq)
      · apply congrArg G.comp
        exact Subtype.ext (Prod.ext ep.symm rfl)⟩
    have ha (i : I) : pullbackHom a (f i) = r i := by
      apply Subtype.ext
      apply Subtype.ext
      exact ContinuousMap.ext fun p ↦ hd ⟨i,p⟩
    refine ⟨a,ha,?_⟩
    intro v hv
    apply Subtype.ext
    apply Subtype.ext
    apply ContinuousMap.ext
    intro p
    obtain ⟨⟨i,q⟩,rfl⟩ := hk.surjective p
    exact congrArg (fun a : A.pullback (f i) ⟶ B.pullback (f i) ↦ a.val.val q)
      ((hv i).trans (ha i).symm)

end FamilyMorphismDescent


section Assemble

variable {G : TopologicalGroupoid.{u}} {T : I → CGWH.{u}}

private abbrev localCoverSpaces (A : ∀ i, QuotientCocycle G (T i)) (i : I) := (A i).coverSpace

private def sumPoint (A : ∀ i, QuotientCocycle G (T i)) :
    C((sumSpace (localCoverSpaces A)).obj,G.objects.obj) :=
  ⟨fun p : Σ i, (A i).coverSpace.obj ↦ (A p.1).point p.2,
    continuous_sigma fun i ↦ (A i).point.continuous⟩

private def sumTransition (A : ∀ i, QuotientCocycle G (T i)) :
    C(SumFibre (fun i ↦ (A i).cover) (fun i ↦ (A i).cover), G.arrows.obj) := by
  let f := fun i ↦ (A i).cover
  let e := coproductFibreHomeomorph f f
  let tr : C((Σ i, CGWH.FibreSubspace (f i) (f i)),G.arrows.obj) :=
    ⟨fun p ↦ (A p.1).transition p.2, continuous_sigma fun i ↦ (A i).transition.continuous⟩
  exact tr.comp ⟨e.symm,e.symm.continuous⟩

private theorem sumTransition_pair (A : ∀ i, QuotientCocycle G (T i)) (i : I)
    (p : CGWH.FibreSubspace (A i).cover (A i).cover) :
    sumTransition A (pairInclusion (fun i ↦ (A i).cover) (fun i ↦ (A i).cover) i p) =
      (A i).transition p := by
  let f := fun i ↦ (A i).cover
  let e := coproductFibreHomeomorph f f
  have he : e.symm (pairInclusion f f i p) = ⟨i,p⟩ := e.symm_apply_apply ⟨i,p⟩
  change (A (e.symm (pairInclusion f f i p)).1).transition
    (e.symm (pairInclusion f f i p)).2 = _
  rw [he]

/-- Families of cocycles on disjoint summands assemble into a single
cocycle on their test-space coproduct. -/
def assembleCocycles (A : ∀ i, QuotientCocycle G (T i)) :
    QuotientCocycle G (sumSpace T) where
  coverSpace := sumSpace (localCoverSpaces A)
  cover := sumMap (fun i ↦ (A i).cover)
  isCover := sumMap_quotient _ (fun i ↦ (A i).isCover)
  point := sumPoint A
  transition := sumTransition A
  transitionSource p := by
    obtain ⟨⟨i,q⟩,rfl⟩ := (pairInclusion_bijective (fun i ↦ (A i).cover) (fun i ↦ (A i).cover)).2 p
    rw [sumTransition_pair]
    exact (A i).transitionSource q
  transitionTarget p := by
    obtain ⟨⟨i,q⟩,rfl⟩ := (pairInclusion_bijective (fun i ↦ (A i).cover) (fun i ↦ (A i).cover)).2 p
    rw [sumTransition_pair]
    exact (A i).transitionTarget q
  transitionUnit := by
    rintro ⟨i,x⟩
    change sumTransition A (pairInclusion (fun i ↦ (A i).cover) (fun i ↦ (A i).cover)
      i ⟨(x,x),rfl⟩) = G.unit ((A i).point x)
    rw [sumTransition_pair]
    exact (A i).transitionUnit x
  transitionComp := by
    rintro ⟨i,x⟩ ⟨j,y⟩ ⟨k,z⟩ hxy hyz
    have hij : i = j := congrArg Sigma.fst hxy
    have hjk : j = k := congrArg Sigma.fst hyz
    subst j
    subst k
    let f := fun i ↦ (A i).cover
    have h₁ : (A i).cover.hom x = (A i).cover.hom y := sumMk_inj T i hxy
    have h₂ : (A i).cover.hom y = (A i).cover.hom z := sumMk_inj T i hyz
    let p := pairInclusion f f i ⟨(x,y),h₁⟩
    let q := pairInclusion f f i ⟨(y,z),h₂⟩
    let r := pairInclusion f f i ⟨(x,z),h₁.trans h₂⟩
    change G.comp ⟨(sumTransition A p,sumTransition A q),_⟩ = sumTransition A r
    have he₁ : sumTransition A p = (A i).transition ⟨(x,y),h₁⟩ := sumTransition_pair A i _
    have he₂ : sumTransition A q = (A i).transition ⟨(y,z),h₂⟩ := sumTransition_pair A i _
    have he₃ : sumTransition A r = (A i).transition ⟨(x,z),h₁.trans h₂⟩ :=
      sumTransition_pair A i _
    exact (congrArg G.comp (Subtype.ext (Prod.ext he₁ he₂))).trans
      (((A i).transitionComp x y z h₁ h₂).trans he₃.symm)

/-- Restriction of the assembled cocycle to a summand recovers the
given cocycle up to the canonical refinement isomorphism. -/
theorem assembleCocycles_restrict_iso (A : ∀ i, QuotientCocycle G (T i)) (i : I) :
    Nonempty ((A i) ≅ (assembleCocycles A).pullback (sumInclusion T i)) := by
  let B := assembleCocycles A
  let g := sumInclusion T i
  let x : C((A i).coverSpace.obj,B.coverSpace.obj) :=
    ⟨sumMk (localCoverSpaces A) i,continuous_sigmaMk⟩
  let y : C((A i).coverSpace.obj,(T i).obj) := (A i).cover.hom.hom.hom
  let k : C((A i).coverSpace.obj, CGWH.FibreSubspace B.cover g) :=
    ⟨fun p ↦ ⟨(x p,y p),rfl⟩,(kelleyPair x y).continuous.subtype_mk _⟩
  refine iso_of_cover_map (B.pullback g) (A i) k (fun _ ↦ rfl) (fun _ ↦ rfl) ?_
  intro x y h
  exact (sumTransition_pair A i ⟨(x,y),h⟩).symm

/-- Overlap transitions on the actual presenting covers of a family of
local cocycles. The equality of the two images is taken in the common
base, so these transitions include overlaps of distinct summands. -/
structure FamilyOverlap {Z : CGWH.{u}} (f : ∀ i, T i ⟶ Z)
    (A : ∀ i, QuotientCocycle G (T i)) where
  arrow : ∀ i j, C(CGWH.FibreSubspace ((A i).cover ≫ f i) ((A j).cover ≫ f j),G.arrows.obj)
  source : ∀ i j p, G.source (arrow i j p) = (A i).point p.val.1
  target : ∀ i j p, G.target (arrow i j p) = (A j).point p.val.2
  agrees : ∀ i (x y : (A i).coverSpace.obj) (h : (A i).cover.hom x = (A i).cover.hom y),
    arrow i i ⟨(x,y),congrArg (f i).hom h⟩ = (A i).transition ⟨(x,y),h⟩
  comp : ∀ i j k (x : (A i).coverSpace.obj) (y : (A j).coverSpace.obj)
      (z : (A k).coverSpace.obj)
      (hxy : ((A i).cover ≫ f i).hom x = ((A j).cover ≫ f j).hom y)
      (hyz : ((A j).cover ≫ f j).hom y = ((A k).cover ≫ f k).hom z),
    G.comp ⟨(arrow i j ⟨(x,y),hxy⟩,arrow j k ⟨(y,z),hyz⟩),
      (target i j ⟨(x,y),hxy⟩).trans (source j k ⟨(y,z),hyz⟩).symm⟩ =
        arrow i k ⟨(x,z),hxy.trans hyz⟩

variable {Z : CGWH.{u}} {f : ∀ i, T i ⟶ Z} {A : ∀ i, QuotientCocycle G (T i)}

/-- The unit and triple-overlap identities for pairwise restriction arrows,
evaluated on the actual presenting points. -/
structure PairwiseOverlapCocycle (r : ∀ i j, (A i).PairOverlapHom (A j) (f i) (f j)) : Prop where
  unit : ∀ i (x : (A i).coverSpace.obj),
      pairOverlapValue (A i) (A i) (f i) (f i) (r i i) x x rfl =
        @CategoryStruct.id G.Underlying _ ((A i).point x)
  comp : ∀ i j k (x : (A i).coverSpace.obj) (y : (A j).coverSpace.obj)
        (z : (A k).coverSpace.obj)
        (hxy : ((A i).cover ≫ f i).hom x = ((A j).cover ≫ f j).hom y)
        (hyz : ((A j).cover ≫ f j).hom y = ((A k).cover ≫ f k).hom z),
      @CategoryStruct.comp G.Underlying _ _ _ _
        (pairOverlapValue (A i) (A j) (f i) (f j) (r i j) x y hxy)
        (pairOverlapValue (A j) (A k) (f j) (f k) (r j k) y z hyz) =
          pairOverlapValue (A i) (A k) (f i) (f k) (r i k) x z (hxy.trans hyz)

/-- Pairwise restriction arrows satisfying the cocycle identities supply
continuous transition data for effective family descent. -/
def FamilyOverlap.ofPairwise (r : ∀ i j, (A i).PairOverlapHom (A j) (f i) (f j))
    (hr : PairwiseOverlapCocycle r) : FamilyOverlap f A where
  arrow i j := (r i j).val.val.comp (continuousPairOverlapSample (A i) (A j) (f i) (f j))
  source i j p := (pairOverlapValue (A i) (A j) (f i) (f j) (r i j) p.val.1 p.val.2 p.property).property.1
  target i j p := (pairOverlapValue (A i) (A j) (f i) (f j) (r i j) p.val.1 p.val.2 p.property).property.2
  agrees i x y h := overlapValue_eq_transition (A i) (f i) (r i i)
    ⟨hr.unit i,hr.comp i i i⟩ x y h
  comp i j k x y z hxy hyz := congrArg Subtype.val (hr.comp i j k x y z hxy hyz)

private abbrev coverToBase (f : ∀ i, T i ⟶ Z) (A : ∀ i, QuotientCocycle G (T i)) (i : I) :=
  (A i).cover ≫ f i

private def FamilyOverlap.transition (r : FamilyOverlap f A) :
    C(CGWH.FibreSubspace (sumDesc (coverToBase f A)) (sumDesc (coverToBase f A)),G.arrows.obj) := by
  let d := coverToBase f A
  let e := crossCoproductFibreHomeomorph d d
  let t : C((Σ ij : I × I, CGWH.FibreSubspace (d ij.1) (d ij.2)),G.arrows.obj) :=
    ⟨fun p ↦ r.arrow p.1.1 p.1.2 p.2, continuous_sigma fun ij ↦ (r.arrow ij.1 ij.2).continuous⟩
  exact t.comp ⟨e.symm,e.symm.continuous⟩

private theorem FamilyOverlap.transition_pair (r : FamilyOverlap f A) (i j : I)
    (p : CGWH.FibreSubspace (coverToBase f A i) (coverToBase f A j)) :
    r.transition (crossPairInclusion (coverToBase f A) (coverToBase f A) i j p) = r.arrow i j p := by
  let d := coverToBase f A
  let e := crossCoproductFibreHomeomorph d d
  have he : e.symm (crossPairInclusion d d i j p) = ⟨(i,j),p⟩ := e.symm_apply_apply ⟨(i,j),p⟩
  change r.arrow (e.symm (crossPairInclusion d d i j p)).1.1
    (e.symm (crossPairInclusion d d i j p)).1.2 (e.symm (crossPairInclusion d d i j p)).2 = _
  rw [he]

/-- Effective object descent on a jointly quotient family, expressed on
its local presenting covers. The descended presentation uses the disjoint
union of those covers, with every pairwise transition recovered exactly. -/
def FamilyOverlap.descend (r : FamilyOverlap f A) (hf : IsQuotientMap (sumDesc f).hom) :
    QuotientCocycle G Z where
  coverSpace := sumSpace (localCoverSpaces A)
  cover := sumDesc (coverToBase f A)
  isCover := by
    have h : sumDesc (coverToBase f A) = sumMap (fun i ↦ (A i).cover) ≫ sumDesc f := by
      apply CGWH.ext_hom
      rintro ⟨i,x⟩
      rfl
    rw [h]
    exact hf.comp (sumMap_quotient _ (fun i ↦ (A i).isCover))
  point := sumPoint A
  transition := r.transition
  transitionSource p := by
    let d := coverToBase f A
    obtain ⟨⟨⟨i,j⟩,q⟩,rfl⟩ := (crossPairInclusion_bijective d d).2 p
    rw [r.transition_pair]
    exact r.source i j q
  transitionTarget p := by
    let d := coverToBase f A
    obtain ⟨⟨⟨i,j⟩,q⟩,rfl⟩ := (crossPairInclusion_bijective d d).2 p
    rw [r.transition_pair]
    exact r.target i j q
  transitionUnit := by
    rintro ⟨i,x⟩
    let d := coverToBase f A
    change r.transition (crossPairInclusion d d i i ⟨(x,x),rfl⟩) = G.unit ((A i).point x)
    rw [r.transition_pair, r.agrees i x x rfl]
    exact (A i).transitionUnit x
  transitionComp := by
    rintro ⟨i,x⟩ ⟨j,y⟩ ⟨k,z⟩ hxy hyz
    let d := coverToBase f A
    let p := crossPairInclusion d d i j ⟨(x,y),hxy⟩
    let q := crossPairInclusion d d j k ⟨(y,z),hyz⟩
    let s := crossPairInclusion d d i k ⟨(x,z),hxy.trans hyz⟩
    change G.comp ⟨(r.transition p,r.transition q),_⟩ = r.transition s
    have h₁ : r.transition p = r.arrow i j ⟨(x,y),hxy⟩ := r.transition_pair i j _
    have h₂ : r.transition q = r.arrow j k ⟨(y,z),hyz⟩ := r.transition_pair j k _
    have h₃ : r.transition s = r.arrow i k ⟨(x,z),hxy.trans hyz⟩ := r.transition_pair i k _
    exact (congrArg G.comp (Subtype.ext (Prod.ext h₁ h₂))).trans
      ((r.comp i j k x y z hxy hyz).trans h₃.symm)

/-- The global transition restricts to the given arrow on every overlap. -/
theorem FamilyOverlap.descend_transition (r : FamilyOverlap f A) (hf : IsQuotientMap (sumDesc f).hom)
    (i j : I) (p : CGWH.FibreSubspace ((A i).cover ≫ f i) ((A j).cover ≫ f j)) :
    (r.descend hf).transition
      (crossPairInclusion (fun k ↦ (A k).cover ≫ f k) (fun k ↦ (A k).cover ≫ f k) i j p) =
      r.arrow i j p := r.transition_pair i j p

/-- The canonical identification of the descended cocycle on one domain
with the original local cocycle. -/
def FamilyOverlap.descendRestrictIso (r : FamilyOverlap f A) (hf : IsQuotientMap (sumDesc f).hom)
    (i : I) : A i ≅ (r.descend hf).pullback (f i) := by
  let B := r.descend hf
  let x : C((A i).coverSpace.obj,B.coverSpace.obj) :=
    ⟨sumMk (localCoverSpaces A) i,continuous_sigmaMk⟩
  let y : C((A i).coverSpace.obj,(T i).obj) := (A i).cover.hom.hom.hom
  let k : C((A i).coverSpace.obj, CGWH.FibreSubspace B.cover (f i)) :=
    ⟨fun p ↦ ⟨(x p,y p),rfl⟩,(kelleyPair x y).continuous.subtype_mk _⟩
  refine isoOfCoverMap (B.pullback (f i)) (A i) k (fun _ ↦ rfl) (fun _ ↦ rfl) ?_
  intro x y h
  exact ((r.descend_transition hf i i ⟨(x,y),congrArg (f i).hom h⟩).trans (r.agrees i x y h)).symm

/-- Evaluation of the restriction identification is the relevant
pairwise overlap arrow, including on different summands. -/
theorem FamilyOverlap.descendRestrictIso_apply (r : FamilyOverlap f A) (hf : IsQuotientMap (sumDesc f).hom)
    (i j : I) (x : (A i).coverSpace.obj) (y : (A j).coverSpace.obj)
    (h : ((A j).cover ≫ f j).hom y = (f i).hom ((A i).cover.hom x)) :
    (r.descendRestrictIso hf i).hom.val.val ⟨(x,⟨(⟨j,y⟩,(A i).cover.hom x),h⟩),rfl⟩ =
      r.arrow i j ⟨(x,y),h.symm⟩ :=
  r.descend_transition hf i j ⟨(x,y),h.symm⟩

/-- The two restriction comparisons agree after transport along a
pairwise overlap, on every presenting point of the descended object. -/
theorem FamilyOverlap.descendRestrictIso_comp (r : FamilyOverlap f A) (hf : IsQuotientMap (sumDesc f).hom)
    (i j k : I) (x : (A i).coverSpace.obj) (y : (A j).coverSpace.obj) (z : (A k).coverSpace.obj)
    (hxy : ((A i).cover ≫ f i).hom x = ((A j).cover ≫ f j).hom y)
    (hyz : ((A j).cover ≫ f j).hom y = ((A k).cover ≫ f k).hom z) :
    let p : CGWH.FibreSubspace (A j).cover ((r.descend hf).pullback (f j)).cover :=
      ⟨(y,⟨(⟨k,z⟩,(A j).cover.hom y),hyz.symm⟩),rfl⟩
    let q : CGWH.FibreSubspace (A i).cover ((r.descend hf).pullback (f i)).cover :=
      ⟨(x,⟨(⟨k,z⟩,(A i).cover.hom x),(hxy.trans hyz).symm⟩),rfl⟩
    G.comp ⟨(r.arrow i j ⟨(x,y),hxy⟩,(r.descendRestrictIso hf j).hom.val.val p),
      (r.target i j ⟨(x,y),hxy⟩).trans ((r.descendRestrictIso hf j).hom.val.property.1 p).symm⟩ =
        (r.descendRestrictIso hf i).hom.val.val q := by
  dsimp only
  refine Eq.trans ?_ (Eq.trans (r.comp i j k x y z hxy hyz) ?_)
  · apply congrArg G.comp
    exact Subtype.ext (Prod.ext rfl (r.descendRestrictIso_apply hf j k y z hyz.symm))
  · exact (r.descendRestrictIso_apply hf i k x z (hxy.trans hyz).symm).symm

/-- The descended cocycle restricts to the given cocycle on each domain. -/
theorem FamilyOverlap.descend_restrict_iso (r : FamilyOverlap f A) (hf : IsQuotientMap (sumDesc f).hom)
    (i : I) : Nonempty (A i ≅ (r.descend hf).pullback (f i)) := ⟨r.descendRestrictIso hf i⟩

private def sumArrowFamily {A B : ∀ i, QuotientCocycle G (T i)}
    (r : ∀ i, (A i) ⟶ (B i)) :
    C(SumFibre (fun i ↦ (A i).cover) (fun i ↦ (B i).cover), G.arrows.obj) := by
  let f := fun i ↦ (A i).cover
  let g := fun i ↦ (B i).cover
  let e := coproductFibreHomeomorph f g
  let t : C((Σ i, CGWH.FibreSubspace (f i) (g i)),G.arrows.obj) :=
    ⟨fun p ↦ (r p.1).val.val p.2, continuous_sigma fun i ↦ (r i).val.val.continuous⟩
  exact t.comp ⟨e.symm,e.symm.continuous⟩

private theorem sumArrowFamily_pair {A B : ∀ i, QuotientCocycle G (T i)}
    (r : ∀ i, (A i) ⟶ (B i)) (i : I)
    (p : CGWH.FibreSubspace (A i).cover (B i).cover) :
    sumArrowFamily r (pairInclusion (fun i ↦ (A i).cover) (fun i ↦ (B i).cover) i p) =
      (r i).val.val p := by
  let f := fun i ↦ (A i).cover
  let g := fun i ↦ (B i).cover
  let e := coproductFibreHomeomorph f g
  have he : e.symm (pairInclusion f g i p) = ⟨i,p⟩ := e.symm_apply_apply ⟨i,p⟩
  change (r (e.symm (pairInclusion f g i p)).1).val.val
    (e.symm (pairInclusion f g i p)).2 = _
  rw [he]

/-- Arrows on the summands assemble into a compatible arrow on the
disjoint union, with the exact given continuous representative on each
summand of the common refinement. -/
def assembleCocycleHom {A B : ∀ i, QuotientCocycle G (T i)}
    (r : ∀ i, (A i) ⟶ (B i)) :
    assembleCocycles A ⟶ assembleCocycles B := by
  let f := fun i ↦ (A i).cover
  let g := fun i ↦ (B i).cover
  have hs (p : SumFibre f g) : G.source (sumArrowFamily r p) = sumPoint A p.val.1 := by
    obtain ⟨⟨i,q⟩,rfl⟩ := (pairInclusion_bijective f g).2 p
    rw [sumArrowFamily_pair]
    exact (r i).val.property.1 q
  have ht (p : SumFibre f g) : G.target (sumArrowFamily r p) = sumPoint B p.val.2 := by
    obtain ⟨⟨i,q⟩,rfl⟩ := (pairInclusion_bijective f g).2 p
    rw [sumArrowFamily_pair]
    exact (r i).val.property.2 q
  refine ⟨⟨sumArrowFamily r,hs,ht⟩,?_⟩
  intro p q hp hq
  obtain ⟨⟨i,p₀⟩,rfl⟩ := (pairInclusion_bijective f g).2 p
  obtain ⟨⟨j,q₀⟩,rfl⟩ := (pairInclusion_bijective f g).2 q
  have hij : i = j := congrArg Sigma.fst hp
  subst j
  have hp' : (f i).hom p₀.val.1 = (f i).hom q₀.val.1 := sumMk_inj T i hp
  have hq' : (g i).hom p₀.val.2 = (g i).hom q₀.val.2 := sumMk_inj T i hq
  apply Subtype.ext
  let u := pairInclusion f f i ⟨(p₀.val.1,q₀.val.1),hp'⟩
  let v := pairInclusion g g i ⟨(p₀.val.2,q₀.val.2),hq'⟩
  change G.comp ⟨(sumTransition A u,sumArrowFamily r (pairInclusion f g i q₀)),_⟩ =
    G.comp ⟨(sumArrowFamily r (pairInclusion f g i p₀),sumTransition B v),_⟩
  exact (congrArg G.comp (Subtype.ext (Prod.ext (sumTransition_pair A i _)
    (sumArrowFamily_pair r i q₀)))).trans
    ((congrArg Subtype.val ((r i).property p₀ q₀ hp' hq')).trans
      (congrArg G.comp (Subtype.ext (Prod.ext (sumArrowFamily_pair r i p₀)
        (sumTransition_pair B i _)))).symm)

/-- The assembled arrow has the given value on each summand. -/
theorem assembleCocycleHom_apply {A B : ∀ i, QuotientCocycle G (T i)}
    (r : ∀ i, (A i) ⟶ (B i)) (i : I)
    (p : CGWH.FibreSubspace (A i).cover (B i).cover) :
    (assembleCocycleHom r).val.val
      (pairInclusion (fun i ↦ (A i).cover) (fun i ↦ (B i).cover) i p) =
        (r i).val.val p :=
  sumArrowFamily_pair r i p

private def restrictAssembledHom {A B : ∀ i, QuotientCocycle G (T i)}
    (r : assembleCocycles A ⟶ assembleCocycles B) (i : I) : A i ⟶ B i := by
  let f := fun i ↦ (A i).cover
  let g := fun i ↦ (B i).cover
  let e := pairInclusion f g i
  refine ⟨⟨r.val.val.comp e,fun p ↦ r.val.property.1 (e p),fun p ↦ r.val.property.2 (e p)⟩,?_⟩
  intro p q hp hq
  have hp' : (sumMap f).hom (e p).val.1 = (sumMap f).hom (e q).val.1 := congrArg (sumMk T i) hp
  have hq' : (sumMap g).hom (e p).val.2 = (sumMap g).hom (e q).val.2 := congrArg (sumMk T i) hq
  have he := congrArg Subtype.val (r.property (e p) (e q) hp' hq')
  apply Subtype.ext
  let u := pairInclusion f f i ⟨(p.val.1,q.val.1),hp⟩
  let v := pairInclusion g g i ⟨(p.val.2,q.val.2),hq⟩
  change G.comp ⟨(sumTransition A u, r.val.val (e q)),_⟩ =
    G.comp ⟨(r.val.val (e p),sumTransition B v),_⟩ at he
  change G.comp ⟨((A i).transition ⟨(p.val.1,q.val.1),hp⟩, r.val.val (e q)),_⟩ =
    G.comp ⟨(r.val.val (e p),(B i).transition ⟨(p.val.2,q.val.2),hq⟩),_⟩
  have hA : sumTransition A u = (A i).transition ⟨(p.val.1,q.val.1),hp⟩ :=
    sumTransition_pair A i _
  have hB : sumTransition B v = (B i).transition ⟨(p.val.2,q.val.2),hq⟩ :=
    sumTransition_pair B i _
  refine Eq.trans ?_ (he.trans ?_)
  · apply congrArg G.comp
    exact Subtype.ext (Prod.ext hA.symm rfl)
  · apply congrArg G.comp
    exact Subtype.ext (Prod.ext rfl hB)

private theorem assembleCocycleHom_bijective (A B : ∀ i, QuotientCocycle G (T i)) :
    Bijective (fun r : ∀ i, A i ⟶ B i ↦ assembleCocycleHom r) := by
  constructor
  · intro r s h
    funext i
    apply Subtype.ext
    apply Subtype.ext
    apply ContinuousMap.ext
    intro p
    have h₁ := congrArg (fun v : assembleCocycles A ⟶ assembleCocycles B ↦ v.val.val
      (pairInclusion (fun i ↦ (A i).cover) (fun i ↦ (B i).cover) i p)) h
    exact (assembleCocycleHom_apply r i p).symm.trans (h₁.trans (assembleCocycleHom_apply s i p))
  · intro r
    let s := restrictAssembledHom r
    refine ⟨s,?_⟩
    apply Subtype.ext
    apply Subtype.ext
    apply ContinuousMap.ext
    intro p
    obtain ⟨⟨i,q⟩,rfl⟩ := (pairInclusion_bijective (fun i ↦ (A i).cover) (fun i ↦ (B i).cover)).2 p
    refine (assembleCocycleHom_apply s i q).trans ?_
    change r.val.val (pairInclusion (fun j ↦ (A j).cover) (fun j ↦ (B j).cover) i q) = _
    rfl

/-- Assembly respects identities and compositions of the local arrows. -/
def assembleCocyclesFunctor : (∀ i, QuotientCocycle G (T i)) ⥤ QuotientCocycle G (sumSpace T) where
  obj := assembleCocycles
  map r := assembleCocycleHom r
  map_id A := by
    apply Subtype.ext
    apply Subtype.ext
    apply ContinuousMap.ext
    intro p
    obtain ⟨⟨i,q⟩,rfl⟩ := (pairInclusion_bijective (fun i ↦ (A i).cover) (fun i ↦ (A i).cover)).2 p
    exact (assembleCocycleHom_apply (fun j ↦ 𝟙 (A j)) i q).trans (sumTransition_pair A i q).symm
  map_comp {A B C} r s := by
    apply Subtype.ext
    apply Subtype.ext
    apply ContinuousMap.ext
    intro p
    let f := fun i ↦ (A i).cover
    let g := fun i ↦ (B i).cover
    let h := fun i ↦ (C i).cover
    obtain ⟨⟨i,q⟩,rfl⟩ := (pairInclusion_bijective f h).2 p
    obtain ⟨y,hy⟩ := (B i).isCover.surjective ((A i).cover.hom q.val.1)
    have hz : (B i).cover.hom y = (C i).cover.hom q.val.2 := hy.trans q.property
    have h₁ := comp_apply (assembleCocycleHom r) (assembleCocycleHom s)
      (sumMk (localCoverSpaces A) i q.val.1) (sumMk (localCoverSpaces B) i y)
      (sumMk (localCoverSpaces C) i q.val.2)
      (congrArg (sumMk T i) hy.symm) (congrArg (sumMk T i) hz)
    have h₂ := comp_apply (r i) (s i) q.val.1 y q.val.2 hy.symm hz
    refine (assembleCocycleHom_apply (fun i ↦ r i ≫ s i) i q).trans
      (h₂.trans (?_ : _ = _))
    apply Eq.trans _ h₁.symm
    apply congrArg G.comp
    apply Subtype.ext
    exact Prod.ext (assembleCocycleHom_apply r i ⟨(q.val.1,y),hy.symm⟩).symm
      (assembleCocycleHom_apply s i ⟨(y,q.val.2),hz⟩).symm

/-- Pullback to all summands and reassembly recovers the original object
through the map that forgets the summand of a presenting point. -/
theorem assembleCocycles_of_restrictions (A : QuotientCocycle G (sumSpace T)) :
    Nonempty (assembleCocycles (fun i ↦ A.pullback (sumInclusion T i)) ≅ A) := by
  let R := fun i ↦ A.pullback (sumInclusion T i)
  let B := assembleCocycles R
  let k : C(B.coverSpace.obj,A.coverSpace.obj) := ⟨fun p : (Σ i, (R i).coverSpace.obj) ↦ p.2.val.1,
    continuous_sigma fun _ ↦ continuous_fst.comp (continuous_Kelley_forget.comp continuous_subtype_val)⟩
  have hk (p : B.coverSpace.obj) : A.cover.hom (k p) = B.cover.hom p := p.2.property
  refine iso_of_cover_map A B k hk (fun _ ↦ rfl) ?_
  intro x y h
  let p : CGWH.FibreSubspace B.cover B.cover := ⟨(x,y),h⟩
  obtain ⟨⟨i,q⟩,he⟩ := (pairInclusion_bijective (fun i ↦ (R i).cover) (fun i ↦ (R i).cover)).2 p
  have eq : B.transition p = (R i).transition q := he ▸ sumTransition_pair R i q
  refine eq.trans ?_
  apply congrArg A.transition
  apply Subtype.ext
  exact Prod.ext (congrArg (fun p : CGWH.FibreSubspace B.cover B.cover ↦ k p.val.1) he)
    (congrArg (fun p : CGWH.FibreSubspace B.cover B.cover ↦ k p.val.2) he)

/-- The quotient cocycle groupoid on a disjoint union is equivalent to
the product of the quotient cocycle groupoids on its summands. -/
theorem assembleCocyclesFunctor_isEquivalence :
    (assembleCocyclesFunctor (G := G) (T := T)).IsEquivalence := by
  let F := assembleCocyclesFunctor (G := G) (T := T)
  obtain ⟨ff⟩ : Nonempty F.FullyFaithful :=
    (Functor.FullyFaithful.nonempty_iff_map_bijective _).mpr assembleCocycleHom_bijective
  letI := ff.full
  letI := ff.faithful
  letI : F.EssSurj := ⟨fun A ↦ ⟨fun i ↦ A.pullback (sumInclusion T i),assembleCocycles_of_restrictions A⟩⟩
  exact {}

end Assemble

end Masullo.TopologicalGroupoid.QuotientCocycle
