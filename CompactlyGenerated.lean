import Mathlib.Topology.Category.CompactlyGenerated
import Mathlib.Topology.Category.TopCat.Limits.Basic
import Mathlib.Topology.Category.TopCat.Limits.Pullbacks
import Mathlib.Topology.Category.TopCat.Limits.Products
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Convenient.HomSpace
import Mathlib.Topology.LocallyClosed
import Mathlib.Topology.Separation.Regular
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Limits.Shapes.KernelPair
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import Mathlib.CategoryTheory.RegularCategory.Basic

open CategoryTheory CategoryTheory.Limits Function Set Topology TopologicalSpace

namespace Masullo

universe u
universe v

section Kelleyfication

/-- The same underlying set with the compactly generated topology. -/
def Kelley (X : Type u) := X

instance (X : Type u) [TopologicalSpace X] : TopologicalSpace (Kelley X) :=
  TopologicalSpace.compactlyGenerated.{u} X

/-- The evaluation map is continuous from a compact Hausdorff test space
into the Kelleyfication. -/
theorem continuous_test_to_Kelley {X : Type u} [TopologicalSpace X] (K : CompHaus.{u})
    (g : C(K, X)) : Continuous (show K → Kelley X from g) := by
  let i : (S : CompHaus.{u}) × C(S, X) := ⟨K, g⟩
  let j : K → (Σ (i : (S : CompHaus.{u}) × C(S, X)), i.fst) := fun x => ⟨i, x⟩
  have hj : Continuous j := by
    change Continuous (Sigma.mk (β := fun i : (S : CompHaus.{u}) × C(S, X) => i.fst) i)
    exact continuous_sigmaMk
  let e : (Σ (i : (S : CompHaus.{u}) × C(S, X)), i.fst) → Kelley X := fun p => p.1.2 p.2
  have hEval : Continuous e := continuous_coinduced_rng
  exact hEval.comp hj

instance (X : Type u) [TopologicalSpace X] : CompactlyGeneratedSpace (Kelley X) := by
  apply compactlyGeneratedSpace_of_continuous_maps
  intro Y _ f hf
  apply continuous_from_compactlyGenerated (X := X) f
  intro K g
  exact hf K g (continuous_test_to_Kelley K g)

theorem continuous_Kelley_forget {X : Type u} [TopologicalSpace X] :
    Continuous (show Kelley X → X from id) := by
  change Continuous[TopologicalSpace.compactlyGenerated.{u} X, inferInstanceAs (TopologicalSpace X)]
    (id : X → X)
  exact continuous_from_compactlyGenerated _ fun _ g => g.continuous

theorem continuous_to_Kelley {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactlyGeneratedSpace X] {f : X → Y} (hf : Continuous f) :
    Continuous (show X → Kelley Y from f) := by
  apply continuous_from_uCompactlyGeneratedSpace
  intro K g
  exact continuous_test_to_Kelley K ⟨f ∘ g, hf.comp g.continuous⟩

/-- Kelleyfication is functorial on topological spaces. -/
def kelleyFunctor : TopCat.{u} ⥤ CompactlyGenerated.{u, u} where
  obj X := ⟨TopCat.of (Kelley X)⟩
  map {X Y} f := ConcreteCategory.ofHom
    (⟨f.hom, continuous_to_Kelley (f.hom.continuous.comp continuous_Kelley_forget)⟩ : C(Kelley X, Kelley Y))
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The adjunction in Lemma E.1.2.1. -/
def kelleyAdjunction : CompactlyGenerated.compactlyGeneratedToTop.{u, u} ⊣ kelleyFunctor.{u} := by
  apply Adjunction.mkOfHomEquiv
  refine {
    homEquiv := fun X Y => {
      toFun := fun f => ConcreteCategory.ofHom (⟨f.hom, continuous_to_Kelley f.hom.continuous⟩ : C(X, Kelley Y))
      invFun := fun f => ConcreteCategory.ofHom
        (⟨f.hom.hom, continuous_Kelley_forget.comp f.hom.hom.continuous⟩ : C(X, Y))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
    homEquiv_naturality_left_symm := by intros; rfl
    homEquiv_naturality_right := by intros; rfl }

instance kelleyAdjunction_unit_isIso : IsIso (kelleyAdjunction.{u}).unit := by
  haveI (X : CompactlyGenerated.{u, u}) : IsIso ((kelleyAdjunction.{u}).unit.app X) := by
    let g : (kelleyFunctor.obj X.toTop) ⟶ X :=
      ConcreteCategory.ofHom (⟨id, continuous_Kelley_forget⟩ : C(Kelley X, X))
    refine ⟨⟨g, ?_, ?_⟩⟩
    · rfl
    · rfl
  exact NatIso.isIso_of_isIso_app _

local notation "UCG" => CompactlyGenerated.compactlyGeneratedToTop

private def kelleyUnitIso : 𝟭 CompactlyGenerated.{u, u} ≅ UCG ⋙ kelleyFunctor :=
  NatIso.ofComponents (fun X => {
    hom := kelleyAdjunction.unit.app X
    inv := ConcreteCategory.ofHom (⟨id, continuous_Kelley_forget⟩ : C(Kelley X, X))
    hom_inv_id := rfl
    inv_hom_id := rfl }) (fun f => kelleyAdjunction.unit.naturality f)

/-- The limiting cone in Lemma E.1.2.2(1) is the Kelleyfication of the
topological limiting cone. -/
noncomputable def kelleyLimit {J : Type v} [SmallCategory J]
    (P : J ⥤ CompactlyGenerated.{u, u}) [HasLimit (P ⋙ UCG)] : LimitCone P := by
  letI : PreservesLimitsOfSize.{v, v} kelleyFunctor := kelleyAdjunction.rightAdjoint_preservesLimits
  let Q := P ⋙ UCG
  let e : P ≅ Q ⋙ kelleyFunctor :=
    (Functor.rightUnitor P).symm ≪≫
      Functor.isoWhiskerLeft P kelleyUnitIso ≪≫
      (Functor.associator P UCG kelleyFunctor).symm
  let c := kelleyFunctor.mapCone (limit.cone Q)
  exact ⟨(Cone.postcompose e.inv).obj c,
    (IsLimit.postcomposeInvEquiv e c).symm (isLimitOfPreserves kelleyFunctor (limit.isLimit Q))⟩

/-- The topological colimit of a diagram of compactly generated spaces is
compactly generated. This uses the final topology of the colimit. -/
theorem compactlyGenerated_topological_colimit {J : Type u} [SmallCategory J]
    (P : J ⥤ CompactlyGenerated.{u, u}) :
    CompactlyGeneratedSpace ((colimit (P ⋙ UCG) : TopCat.{u}) : Type u) := by
  apply uCompactlyGeneratedSpace_of_continuous_maps
  intro Y _ f hf
  apply (TopCat.continuous_iff_of_isColimit _ (colimit.isColimit (P ⋙ UCG)) f).mpr
  intro j
  letI : UCompactlyGeneratedSpace.{u} ((P ⋙ UCG).obj j : TopCat.{u}) := (P.obj j).is_compactly_generated
  apply continuous_from_uCompactlyGeneratedSpace
  intro K g
  exact hf K ⟨_, (colimit.ι (P ⋙ UCG) j).hom.continuous.comp g.continuous⟩

/-- The colimit in Lemma E.1.2.2(2) is computed in topological spaces. -/
noncomputable def kelleyColimit {J : Type u} [SmallCategory J]
    (P : J ⥤ CompactlyGenerated.{u, u}) : ColimitCocone P := by
  letI := compactlyGenerated_topological_colimit P
  let c : Cocone P := {
    pt := ⟨colimit (P ⋙ UCG)⟩
    ι := {
      app := fun j => ConcreteCategory.ofHom (colimit.ι (P ⋙ UCG) j).hom
      naturality := by
        intro i j f
        apply (UCG).map_injective
        change (P ⋙ UCG).map f ≫ colimit.ι (P ⋙ UCG) j = colimit.ι (P ⋙ UCG) i
        exact colimit.w (P ⋙ UCG) f } }
  exact ⟨c, isColimitOfReflects UCG (colimit.isColimit (P ⋙ UCG))⟩

theorem kelley_forget_reflects_colimits :
    ReflectsColimitsOfSize.{u, u} CompactlyGenerated.compactlyGeneratedToTop.{u, u} := inferInstance

theorem kelley_forget_preserves_colimits :
    PreservesColimitsOfSize.{u, u} CompactlyGenerated.compactlyGeneratedToTop.{u, u} :=
  kelleyAdjunction.leftAdjoint_preservesColimits

/-- A weakly Hausdorff space has closed images of compact Hausdorff test spaces. -/
def WeaklyHausdorff (X : Type u) [TopologicalSpace X] : Prop :=
  ∀ (K : CompHaus.{u}) (g : C(K, X)), IsClosed (range g)

/-- Lemma E.2.1.5. Kelleyfication preserves the weak Hausdorff property. -/
theorem weaklyHausdorff_Kelley {X : Type u} [TopologicalSpace X] (hX : WeaklyHausdorff X) :
    WeaklyHausdorff (Kelley X) := by
  intro K f
  let g : C(K, X) := ⟨f, continuous_Kelley_forget.comp f.continuous⟩
  exact (hX K g).preimage continuous_Kelley_forget

theorem weaklyHausdorff_closed_singleton {X : Type u} [TopologicalSpace X]
    (hX : WeaklyHausdorff X) (x : X) : IsClosed ({x} : Set X) := by
  let K := CompHaus.of (ULift.{u} Unit)
  have h := hX K (ContinuousMap.const K x)
  have heq : range (ContinuousMap.const K x) = {x} := by
    ext y
    constructor
    · rintro ⟨_, rfl⟩
      exact mem_singleton x
    · rintro hy
      exact ⟨⟨()⟩, (mem_singleton_iff.mp hy).symm⟩
  rwa [heq] at h

/-- Lemma E.2.1.4. A weakly Hausdorff continuous image of a compact
Hausdorff space is Hausdorff. -/
theorem weaklyHausdorff_compact_surjection {X : Type u} [TopologicalSpace X]
    (hX : WeaklyHausdorff X) (K : CompHaus.{u}) (q : C(K, X)) (hq : Surjective q) :
    T2Space X := by
  have hclosed : IsClosedMap q := by
    intro S hS
    haveI : CompactSpace S := isCompact_iff_compactSpace.mp hS.isCompact
    let L := CompHaus.of S
    have he : range (fun s : L => q s.val) = q '' S := by ext y; simp [L]
    rw [← he]
    exact hX L ⟨fun s => q s.val, q.continuous.comp continuous_subtype_val⟩
  refine ⟨fun x y hxy => ?_⟩
  have hsx := (weaklyHausdorff_closed_singleton hX x).preimage q.continuous
  have hsy := (weaklyHausdorff_closed_singleton hX y).preimage q.continuous
  have hdis : Disjoint (q ⁻¹' {x}) (q ⁻¹' {y}) := by
    rw [Set.disjoint_left]
    intro p hx hy
    exact hxy ((Set.mem_singleton_iff.mp hx).symm.trans (Set.mem_singleton_iff.mp hy))
  obtain ⟨U, V, hU, hV, hxU, hyV, hd⟩ := normal_separation hsx hsy hdis
  refine ⟨(q '' Uᶜ)ᶜ, (q '' Vᶜ)ᶜ, (hclosed _ hU.isClosed_compl).isOpen_compl,
    (hclosed _ hV.isClosed_compl).isOpen_compl, ?_, ?_, ?_⟩
  · rintro ⟨p, hp, hpx⟩
    exact hp (hxU (Set.mem_singleton_iff.mpr hpx))
  · rintro ⟨p, hp, hpy⟩
    exact hp (hyV (Set.mem_singleton_iff.mpr hpy))
  · rw [Set.disjoint_left]
    intro z hzU hzV
    obtain ⟨p, rfl⟩ := hq z
    exact Set.disjoint_left.mp hd
      (by by_contra h; exact hzU ⟨p, h, rfl⟩)
      (by by_contra h; exact hzV ⟨p, h, rfl⟩)

theorem weaklyHausdorff_subspace {X : Type u} [TopologicalSpace X]
    (hX : WeaklyHausdorff X) (S : Set X) : WeaklyHausdorff S := by
  intro K f
  let g : C(K, X) := ⟨fun x => (f x).val, continuous_subtype_val.comp f.continuous⟩
  have heq : range f = (Subtype.val : S → X) ⁻¹' range g := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, rfl⟩
    · rintro ⟨x, hx⟩
      exact ⟨x, Subtype.ext hx⟩
  rw [heq]
  exact (hX K g).preimage continuous_subtype_val

/-- The diagonal is closed after pullback along every compact Hausdorff test map. -/
def KelleyClosedDiagonal (X : Type u) [TopologicalSpace X] : Prop :=
  ∀ (K : CompHaus.{u}) (f : C(K, X × X)), IsClosed {k | (f k).1 = (f k).2}

/-- The closed self-fibre-product test in Lemma E.2.1.6. -/
def ClosedCompactSelfPullbacks (X : Type u) [TopologicalSpace X] : Prop :=
  ∀ (K : CompHaus.{u}) (f : C(K, X)), IsClosed {p : K × K | f p.1 = f p.2}

theorem weaklyHausdorff_kelleyClosedDiagonal {X : Type u} [TopologicalSpace X]
    (hX : WeaklyHausdorff X) : KelleyClosedDiagonal X := by
  intro K f
  let L := CompHaus.of (K ⊕ K)
  let g : C(L, X) := ⟨Sum.elim (fun k => (f k).1) (fun k => (f k).2),
    (continuous_fst.comp f.continuous).sumElim (continuous_snd.comp f.continuous)⟩
  let g' : C(L, range g) := ⟨rangeFactorization g,
    continuous_rangeFactorization_iff.mpr g.continuous⟩
  haveI := weaklyHausdorff_compact_surjection (weaklyHausdorff_subspace hX _) L g'
    (rangeFactorization_surjective (f := g))
  convert isClosed_eq (g'.continuous.comp continuous_inl) (g'.continuous.comp continuous_inr) using 1
  ext k
  change (f k).1 = (f k).2 ↔ g' (Sum.inl k) = g' (Sum.inr k)
  constructor
  · intro h
    apply Subtype.ext
    exact h
  · intro h
    exact congrArg Subtype.val h

theorem kelleyClosedDiagonal_iff_compactSelfPullbacks (X : Type u) [TopologicalSpace X] :
    KelleyClosedDiagonal X ↔ ClosedCompactSelfPullbacks X := by
  constructor
  · intro h K f
    exact h (CompHaus.of (K × K)) ⟨fun p => (f p.1, f p.2),
      (f.continuous.comp continuous_fst).prodMk (f.continuous.comp continuous_snd)⟩
  · intro h K f
    let L := CompHaus.of (K ⊕ K)
    let g : C(L, X) := ⟨Sum.elim (fun k => (f k).1) (fun k => (f k).2),
      (continuous_fst.comp f.continuous).sumElim (continuous_snd.comp f.continuous)⟩
    exact (h L g).preimage (continuous_inl.prodMk continuous_inr)

theorem weaklyHausdorff_iff_kelleyClosedDiagonal (X : Type u) [TopologicalSpace X]
    [CompactlyGeneratedSpace X] : WeaklyHausdorff X ↔ KelleyClosedDiagonal X := by
  refine ⟨weaklyHausdorff_kelleyClosedDiagonal, fun h K f => ?_⟩
  apply CompactlyGeneratedSpace.isClosed'
  intro L _ _ _ g hg
  let S : Set (L × K) := {p | g p.1 = f p.2}
  have hS : IsClosed S := h (CompHaus.of (L × K))
    ⟨fun p : L × K => (g p.1, f p.2),
      (hg.comp continuous_fst).prodMk (f.continuous.comp continuous_snd)⟩
  have heq : g ⁻¹' range f = Prod.fst '' S := by
    ext x
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨(x, k), hk.symm, rfl⟩
    · rintro ⟨⟨y, k⟩, hy, rfl⟩
      exact ⟨k, hy.symm⟩
  rw [heq]
  exact (hS.isCompact.image continuous_fst).isClosed

end Kelleyfication

/-- The test-map criterion for compact generation. -/
def KelleyTestMaps (X : Type u) [TopologicalSpace X] : Prop :=
  ∀ (Y : Type u) [TopologicalSpace Y] (f : X → Y),
    Continuous f ↔ ∀ (K : CompHaus.{u}) (g : C(K, X)), Continuous (f ∘ g)

/-- The criterion using a specified set of test spaces. -/
def KelleyTestFamily (X : Type u) [TopologicalSpace X] : Prop :=
  ∃ S : Set (CompHaus.{u}), ∀ (Y : Type u) [TopologicalSpace Y] (f : X → Y),
    Continuous f ↔ ∀ K ∈ S, ∀ (g : C(K, X)), Continuous (f ∘ g)

/-- The open-set test for compact generation. -/
def KelleyTestOpen (X : Type u) [TopologicalSpace X] : Prop :=
  ∀ U : Set X, IsOpen U ↔ ∀ (K : CompHaus.{u}) (g : C(K, X)), IsOpen (g ⁻¹' U)

/-- The quotient-of-coproducts criterion. The index set is allowed to live
in the next universe so it can index the family of all small test maps. -/
def KelleyTestQuotient (X : Type u) [TopologicalSpace X] : Prop :=
  ∃ (I : Type (u + 1)) (K : I → CompHaus.{u}) (q : (Σ i, K i) → X), IsQuotientMap q

/-- All four descriptions of compact generation in Lemma E.1.1.3. -/
theorem kelley_criteria (X : Type u) [t : TopologicalSpace X] :
    (KelleyTestMaps X ↔ CompactlyGeneratedSpace X) ∧
    (KelleyTestFamily X ↔ CompactlyGeneratedSpace X) ∧
    (KelleyTestOpen X ↔ CompactlyGeneratedSpace X) ∧
    (KelleyTestQuotient X ↔ CompactlyGeneratedSpace X) := by
  have hm : KelleyTestMaps X ↔ CompactlyGeneratedSpace X := by
    constructor
    · intro h
      exact uCompactlyGeneratedSpace_of_continuous_maps fun f hf => (h _ f).mpr hf
    · intro h
      exact fun _ _ f => ⟨fun hf _ g => hf.comp g.continuous,
        continuous_from_uCompactlyGeneratedSpace f⟩
  refine ⟨hm, ?_, ?_, ?_⟩
  · constructor
    · rintro ⟨S, hS⟩
      exact hm.mp fun Y _ f => ⟨fun hf _ g => hf.comp g.continuous,
        fun hf => (hS Y f).mpr (fun K _ => hf K)⟩
    · intro h
      refine ⟨univ, fun Y _ f => ?_⟩
      simpa using hm.mpr h Y f
  · constructor
    · intro h
      apply compactlyGeneratedSpace_of_isOpen
      intro U hU
      exact (h U).mpr fun K g => hU K g g.continuous
    · intro h U
      exact ⟨fun hU _ g => hU.preimage g.continuous,
        fun hU => UCompactlyGeneratedSpace.isOpen hU⟩
  · constructor
    · rintro ⟨I, K, q, hq⟩
      apply hm.mp
      intro Y _ f
      refine ⟨fun hf _ g => hf.comp g.continuous, fun hf => hq.continuous_iff.mpr ?_⟩
      apply continuous_sigma_iff.mpr
      intro i
      let j : K i → (Σ i, K i) := fun x => ⟨i, x⟩
      have hj : Continuous j := by
        change Continuous (Sigma.mk (β := fun i => (K i : Type u)) i)
        exact continuous_sigmaMk
      exact hf (K i) ⟨q ∘ j, hq.continuous.comp hj⟩
    · intro h
      refine ⟨(K : CompHaus.{u}) × C(K, X), Sigma.fst, fun x => x.1.2 x.2, ?_⟩
      refine ⟨⟨eq_compactlyGenerated⟩, ?_⟩
      intro x
      let K := CompHaus.of (ULift.{u} Unit)
      exact ⟨⟨⟨K, ContinuousMap.const K x⟩, ⟨()⟩⟩, rfl⟩

/-- Both clauses of Proposition E.1.2.19. A product with a locally compact
Hausdorff factor already has the compactly generated topology. -/
theorem locallyCompact_compactlyGenerated_and_prod {X Y : Type u} [TopologicalSpace X]
    [TopologicalSpace Y] [CompactlyGeneratedSpace X] [LocallyCompactSpace Y] [T2Space Y] :
    CompactlyGeneratedSpace Y ∧ CompactlyGeneratedSpace (X × Y) := by
  refine ⟨inferInstance, ?_⟩
  apply compactlyGeneratedSpace_of_continuous_maps
  intro Z _ f h
  let g (x : X) : C(Y, Z) :=
    ⟨fun y => f (x, y), continuous_from_compactlyGeneratedSpace _ (fun S _ _ _ l hl =>
      h S (fun s => (x, l s)) (continuous_const.prodMk hl))⟩
  -- Joint continuity on a compact test space times Y follows by testing once more
  -- against compact spaces, since that product is itself locally compact Hausdorff.
  have hg : Continuous g := by
    apply continuous_from_compactlyGeneratedSpace
    intro K _ _ _ k hk
    apply ContinuousMap.continuous_of_continuous_uncurry
    have hf : Continuous (fun p : K × Y => f (k p.1, p.2)) := by
      apply continuous_from_compactlyGeneratedSpace
      intro S _ _ _ l hl
      exact h S _ ((hk.comp continuous_fst).prodMk continuous_snd |>.comp hl)
    exact hf
  exact ContinuousMap.continuous_uncurry_of_continuous ⟨g, hg⟩

/-- Proposition E.1.2.21. -/
theorem sequential_compactlyGenerated (X : Type u) [TopologicalSpace X] [SequentialSpace X] :
    CompactlyGeneratedSpace X := inferInstance

theorem firstCountable_prod_compactlyGenerated (X Y : Type u) [TopologicalSpace X]
    [TopologicalSpace Y] [FirstCountableTopology X] [FirstCountableTopology Y] :
    CompactlyGeneratedSpace (X × Y) := inferInstance

/-- Lemma E.1.2.25. Open, closed, and locally closed subspaces preserve compact generation. -/
theorem closed_compactlyGenerated {X : Type u} [TopologicalSpace X]
    [CompactlyGeneratedSpace X] {S : Set X} (hS : IsClosed S) : CompactlyGeneratedSpace S := by
  apply compactlyGeneratedSpace_of_isClosed
  intro A hA
  apply hS.isClosedEmbedding_subtypeVal.isClosed_iff_image_isClosed.mpr
  apply CompactlyGeneratedSpace.isClosed'
  intro K _ _ _ f hf
  let V := f ⁻¹' S
  have hV : IsClosed V := hS.preimage hf
  letI : CompactSpace V := isCompact_iff_compactSpace.mp hV.isCompact
  let g : V → S := fun v => ⟨f v, v.property⟩
  have hg : Continuous g := (hf.comp continuous_subtype_val).subtype_mk _
  have heq : f ⁻¹' (Subtype.val '' A) = (Subtype.val : V → K) '' (g ⁻¹' A) := by
    ext x
    constructor
    · rintro ⟨a, ha, hax⟩
      have hx : x ∈ V := by change f x ∈ S; rw [← hax]; exact a.property
      refine ⟨⟨x, hx⟩, ?_, rfl⟩
      change g ⟨x, hx⟩ ∈ A
      rwa [show g ⟨x, hx⟩ = a from Subtype.ext hax.symm]
    · rintro ⟨v, hv, rfl⟩
      exact ⟨g v, hv, rfl⟩
  rw [heq]
  exact hV.isClosedMap_subtype_val _ (hA V g (by exact hg))

theorem open_compactlyGenerated {X : Type u} [TopologicalSpace X]
    [CompactlyGeneratedSpace X] {S : Set X} (hS : IsOpen S) : CompactlyGeneratedSpace S := by
  apply compactlyGeneratedSpace_of_isOpen
  intro A hA
  apply hS.isOpenEmbedding_subtypeVal.isOpen_iff_image_isOpen.mpr
  apply CompactlyGeneratedSpace.isOpen'
  intro K _ _ _ f hf
  let V := f ⁻¹' S
  have hV : IsOpen V := hS.preimage hf
  letI : LocallyCompactSpace V := hV.locallyCompactSpace
  let g : V → S := fun v => ⟨f v, v.property⟩
  have hg : Continuous g := (hf.comp continuous_subtype_val).subtype_mk _
  have heq : f ⁻¹' (Subtype.val '' A) = (Subtype.val : V → K) '' (g ⁻¹' A) := by
    ext x
    constructor
    · rintro ⟨a, ha, hax⟩
      have hx : x ∈ V := by change f x ∈ S; rw [← hax]; exact a.property
      refine ⟨⟨x, hx⟩, ?_, rfl⟩
      change g ⟨x, hx⟩ ∈ A
      rwa [show g ⟨x, hx⟩ = a from Subtype.ext hax.symm]
    · rintro ⟨v, hv, rfl⟩
      exact ⟨g v, hv, rfl⟩
  rw [heq]
  apply hV.isOpenMap_subtype_val
  apply CompactlyGeneratedSpace.isOpen'
  intro L _ _ _ l hl
  exact hA L (g ∘ l) (hg.comp hl)

theorem locallyClosed_compactlyGenerated {X : Type u} [TopologicalSpace X]
    [CompactlyGeneratedSpace X] {S : Set X} (hS : IsLocallyClosed S) : CompactlyGeneratedSpace S := by
  obtain ⟨U, Z, hU, hZ, rfl⟩ := hS
  letI := open_compactlyGenerated hU
  let W : Set U := Subtype.val ⁻¹' Z
  letI : CompactlyGeneratedSpace W := closed_compactlyGenerated
    (hZ.preimage continuous_subtype_val)
  let e : W ≃ₜ ↥(U ∩ Z) := {
    toFun x := ⟨x.val.val, x.val.property, x.property⟩
    invFun x := ⟨⟨x.val, x.property.1⟩, x.property.2⟩
    left_inv _ := rfl
    right_inv _ := rfl
    continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
    continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _ }
  exact compactlyGeneratedSpace_of_coinduced e.continuous e.isQuotientMap.eq_coinduced

/-- Both clauses of Proposition E.2.3.1. -/
theorem locallyCompact_cgwh_and_prod {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactlyGeneratedSpace X] [LocallyCompactSpace Y] [T2Space Y] (hX : WeaklyHausdorff X) :
    (CompactlyGeneratedSpace Y ∧ WeaklyHausdorff Y) ∧
    (CompactlyGeneratedSpace (X × Y) ∧ WeaklyHausdorff (X × Y)) := by
  obtain ⟨hY, hXY⟩ := locallyCompact_compactlyGenerated_and_prod (X := X) (Y := Y)
  refine ⟨⟨hY, fun K f => (isCompact_range f.continuous).isClosed⟩, hXY, ?_⟩
  apply (weaklyHausdorff_iff_kelleyClosedDiagonal (X × Y)).mpr
  intro K f
  let h : C(K, X × X) := ⟨fun k => ((f k).1.1, (f k).2.1),
    (continuous_fst.comp (continuous_fst.comp f.continuous)).prodMk
      (continuous_fst.comp (continuous_snd.comp f.continuous))⟩
  have h₁ := weaklyHausdorff_kelleyClosedDiagonal hX K h
  have h₂ := isClosed_eq (continuous_snd.comp (continuous_fst.comp f.continuous))
    (continuous_snd.comp (continuous_snd.comp f.continuous))
  have heq : {k | (f k).1 = (f k).2} = {k | (h k).1 = (h k).2} ∩
      {k | (f k).1.2 = (f k).2.2} := by
    ext k
    exact Prod.ext_iff
  rw [heq]
  exact h₁.inter h₂

/-- An equalizer into a weakly Hausdorff space is closed on a compactly
generated source. Its subspace thus computes the equalizer in CGWH. -/
theorem cgwh_isClosed_equalizer {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactlyGeneratedSpace X] (hY : WeaklyHausdorff Y) (f g : C(X, Y)) :
    IsClosed {x | f x = g x} := by
  apply UCompactlyGeneratedSpace.isClosed
  intro K k
  exact weaklyHausdorff_kelleyClosedDiagonal hY K
    ⟨fun x => (f (k x), g (k x)), (f.continuous.comp k.continuous).prodMk (g.continuous.comp k.continuous)⟩

/-- Lemma E.2.3.4. A continuous section into a compactly generated weakly
Hausdorff space is a closed embedding, and the split map is a quotient. -/
theorem cgwh_section_closed_and_quotient {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactlyGeneratedSpace X] (hX : WeaklyHausdorff X) (g : C(X, Y)) (f : C(Y, X))
    (hs : RightInverse f g) : IsClosedEmbedding f ∧ IsQuotientMap g := by
  have hQ : IsQuotientMap g := by
    apply isQuotientMap_iff_isClosed.mpr
    refine ⟨hs.surjective, fun S => ⟨fun hS => hS.preimage g.continuous, ?_⟩⟩
    intro hS
    have h := hS.preimage f.continuous
    rwa [← preimage_comp, hs.comp_eq_id, preimage_id] at h
  refine ⟨⟨hs.isEmbedding g.continuous f.continuous, ?_⟩, hQ⟩
  convert cgwh_isClosed_equalizer hX (f.comp g) (ContinuousMap.id X) using 1
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact congrArg f (hs y)
  · intro hx
    exact ⟨g x, hx⟩

/-- The preimage of the composite's range is where the first map is split. -/
private theorem cgwh_range_closed_in_composite_preimage {X Y Z : Type u}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] [CompactlyGeneratedSpace Y]
    (hY : WeaklyHausdorff Y) (f : C(X, Y)) (g : C(Y, Z)) (h : IsEmbedding (g ∘ f))
    (hS : IsLocallyClosed (g ⁻¹' range (g ∘ f))) :
    IsClosed (Subtype.val ⁻¹' range f : Set (g ⁻¹' range (g ∘ f))) := by
  let S := g ⁻¹' range (g ∘ f)
  letI : CompactlyGeneratedSpace S := locallyClosed_compactlyGenerated hS
  let f' : C(X, S) := ⟨fun x => ⟨f x, mem_range_self x⟩, f.continuous.subtype_mk _⟩
  let g' : C(S, range (g ∘ f)) := ⟨fun y => ⟨g y, y.property⟩,
    (g.continuous.comp continuous_subtype_val).subtype_mk _⟩
  let r : C(S, X) := ⟨fun y => h.toHomeomorph.symm (g' y),
    h.toHomeomorph.symm.continuous.comp g'.continuous⟩
  have hr : RightInverse f' r := by
    intro x
    exact h.toHomeomorph.symm_apply_apply x
  have hc := (cgwh_section_closed_and_quotient (weaklyHausdorff_subspace hY S) r f' hr).1.isClosed_range
  convert hc using 1
  ext y
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, Subtype.ext hx⟩
  · rintro ⟨x, rfl⟩
    exact mem_range_self x

/-- All three clauses of Lemma E.2.3.5. -/
theorem cgwh_embeddings_of_composite {X Y Z : Type u}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] [CompactlyGeneratedSpace Y]
    (hY : WeaklyHausdorff Y) (f : C(X, Y)) (g : C(Y, Z)) :
    (IsEmbedding (g ∘ f) → IsEmbedding f) ∧
    (IsClosedEmbedding (g ∘ f) → IsClosedEmbedding f) ∧
    (IsOpenEmbedding (g ∘ f) → IsEmbedding f ∧ IsLocallyClosed (range f)) := by
  have hImage : Subtype.val '' (Subtype.val ⁻¹' range f : Set (g ⁻¹' range (g ∘ f))) =
      range f := image_preimage_eq_of_subset (by
        rw [Subtype.range_coe]
        rintro _ ⟨x, rfl⟩
        exact mem_range_self x)
  refine ⟨IsEmbedding.of_comp f.continuous g.continuous, ?_, ?_⟩
  · intro h
    have hS := h.isClosed_range.preimage g.continuous
    have hc := cgwh_range_closed_in_composite_preimage hY f g h.isEmbedding hS.isLocallyClosed
    refine ⟨IsEmbedding.of_comp f.continuous g.continuous h.isEmbedding, ?_⟩
    exact hImage ▸ hS.isClosedMap_subtype_val _ hc
  · intro h
    have hS := h.isOpen_range.preimage g.continuous
    have hc := cgwh_range_closed_in_composite_preimage hY f g h.isEmbedding hS.isLocallyClosed
    refine ⟨IsEmbedding.of_comp f.continuous g.continuous h.isEmbedding, ?_⟩
    exact hImage ▸ IsLocallyClosed.image hc.isLocallyClosed IsInducing.subtypeVal
      (by rw [Subtype.range_coe]; exact hS.isLocallyClosed)

section Quotients

private abbrev TestSpaces (K : CompHaus.{u}) := (K : Type u)

private theorem continuous_from_Kelley_iff {X Y : Type u} [TopologicalSpace X]
    [TopologicalSpace Y] (f : X → Y) :
    Continuous (show Kelley X → Y from f) ↔ ContinuousGeneratedBy TestSpaces.{u} f :=
  ⟨fun h K k => h.comp (continuous_test_to_Kelley K k),
    fun h => continuous_from_compactlyGenerated f fun _ k => h k⟩

private theorem continuous_kelleyProductMap {X Y X' Y' : Type u} [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace X'] [TopologicalSpace Y']
    {f : X → X'} {g : Y → Y'} (hf : Continuous f) (hg : Continuous g) :
    Continuous (show Kelley (X × Y) → Kelley (X' × Y') from Prod.map f g) :=
  continuous_to_Kelley ((hf.prodMap hg).comp continuous_Kelley_forget)

/-- Currying with respect to the manuscript's compact Hausdorff tests. -/
private theorem continuous_kelleyProduct_iff_curried {X Y Z : Type u} [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace Z]
    (h : X × Y → Z)
    (hc : ∀ x, ContinuousGeneratedBy TestSpaces.{u} (fun y => h (x, y))) :
    Continuous (show Kelley (X × Y) → Z from h) ↔
      ContinuousGeneratedBy TestSpaces.{u}
        (fun x => (⟨fun y => h (x, y), hc x⟩ : ContinuousMapGeneratedBy TestSpaces.{u} Y Z)) := by
  rw [continuous_from_Kelley_iff]
  constructor
  · intro hh K k
    apply ContinuousMapGeneratedBy.continuous_iff.mpr
    intro L l
    have hkl := hh (i := CompHaus.of (K × L)) ⟨_, k.continuous.prodMap l.continuous⟩
    exact (ContinuousMap.curry ⟨_, hkl⟩).continuous
  · intro hh K k
    let k₁ : C(K, X) := ContinuousMap.fst.comp k
    let k₂ : C(K, Y) := ContinuousMap.snd.comp k
    have hkk := ContinuousMapGeneratedBy.continuous_iff.mp (hh k₁) K k₂
    have hu := ContinuousMap.continuous_uncurry_of_continuous ⟨_, hkk⟩
    exact hu.comp (continuous_id.prodMk continuous_id)

private theorem kelleyProduct_quotient_left {X X' Y : Type u} [TopologicalSpace X]
    [TopologicalSpace X'] [TopologicalSpace Y] [CompactlyGeneratedSpace X]
    {f : X → X'} (hf : IsQuotientMap f) :
    IsQuotientMap (show Kelley (X × Y) → Kelley (X' × Y) from Prod.map f id) := by
  let q : Kelley (X × Y) → Kelley (X' × Y) := Prod.map f id
  have hq : Continuous q := continuous_kelleyProductMap hf.continuous continuous_id
  refine ⟨⟨le_antisymm ?_ ((continuous_iff_coinduced_le (f := q)).mp hq)⟩, ?_⟩
  · let Z := Kelley (X' × Y)
    letI : TopologicalSpace Z := coinduced q inferInstance
    have hcont : Continuous (show Kelley (X × Y) → Z from q) := continuous_coinduced_rng
    have hc (x : X') : ContinuousGeneratedBy TestSpaces.{u} (fun y : Y => (show Z from (x, y))) := by
      obtain ⟨a, rfl⟩ := hf.surjective x
      intro K k
      exact hcont.comp (continuous_test_to_Kelley K ⟨fun z => (a, k z),
        continuous_const.prodMk k.continuous⟩)
    let h : X' → ContinuousMapGeneratedBy TestSpaces.{u} Y Z := fun x => ⟨_, hc x⟩
    have hh₀ : ContinuousGeneratedBy TestSpaces.{u} (h ∘ f) :=
      (continuous_kelleyProduct_iff_curried (Z := Z) (fun p : X × Y => (f p.1, p.2))
        (fun x => hc (f x))).mp hcont
    have hh₁ : Continuous (h ∘ f) :=
      continuous_from_uCompactlyGeneratedSpace _ fun _ k => hh₀ k
    have hh : Continuous h := hf.continuous_iff.mpr hh₁
    have hid := (continuous_kelleyProduct_iff_curried (Z := Z) (fun p : X' × Y => p) hc).mpr
      hh.continuousGeneratedBy
    exact (continuous_iff_coinduced_le (f := (id : Kelley (X' × Y) → Z))
      (t₁ := instTopologicalSpaceKelley (X' × Y)) (t₂ := inferInstanceAs (TopologicalSpace Z))).mp hid
  · intro p
    obtain ⟨x, hx⟩ := hf.surjective p.1
    exact ⟨(x, p.2), Prod.ext hx rfl⟩

private def kelleySwap (X Y : Type u) [TopologicalSpace X] [TopologicalSpace Y] :
    Kelley (X × Y) ≃ₜ Kelley (Y × X) where
  toEquiv := Equiv.prodComm X Y
  continuous_toFun := continuous_to_Kelley (X := Kelley (X × Y)) (Y := Y × X)
    ((continuous_swap : Continuous (Prod.swap : X × Y → Y × X)).comp
      (continuous_Kelley_forget (X := X × Y)))
  continuous_invFun := continuous_to_Kelley (X := Kelley (Y × X)) (Y := X × Y)
    ((continuous_swap : Continuous (Prod.swap : Y × X → X × Y)).comp
      (continuous_Kelley_forget (X := Y × X)))

/-- Lemma E.1.2.17. The categorical product preserves quotient maps. -/
theorem kelleyProduct_quotient {X X' Y Y' : Type u} [TopologicalSpace X] [TopologicalSpace X']
    [TopologicalSpace Y] [TopologicalSpace Y'] [CompactlyGeneratedSpace X] [CompactlyGeneratedSpace Y]
    [CompactlyGeneratedSpace X'] [CompactlyGeneratedSpace Y'] {f : X → X'} {g : Y → Y'}
    (hf : IsQuotientMap f) (hg : IsQuotientMap g) :
    IsQuotientMap (show Kelley (X × Y) → Kelley (X' × Y') from Prod.map f g) :=
  ((kelleySwap Y' X').isQuotientMap.comp ((kelleyProduct_quotient_left (Y := X') hg).comp
    (kelleySwap X' Y).isQuotientMap)).comp (kelleyProduct_quotient_left (Y := Y) hf)

/-- Lemma E.1.2.26. Products of closed embeddings are closed embeddings
for the compactly generated product topologies. -/
theorem kelleyProduct_closedEmbedding {X X' Y Y' : Type u} [TopologicalSpace X]
    [TopologicalSpace X'] [TopologicalSpace Y] [TopologicalSpace Y']
    {f : X → X'} {g : Y → Y'} (hf : IsClosedEmbedding f) (hg : IsClosedEmbedding g) :
    IsClosedEmbedding (show Kelley (X × Y) → Kelley (X' × Y') from Prod.map f g) := by
  let p : Kelley (X × Y) → Kelley (X' × Y') := Prod.map f g
  have hp : Continuous p := continuous_kelleyProductMap hf.continuous hg.continuous
  let S : Set (Kelley (X' × Y')) := range p
  have he := hf.prodMap hg
  have hS : IsClosed S := he.isClosed_range.preimage (continuous_Kelley_forget (X := X' × Y'))
  letI : CompactlyGeneratedSpace S := closed_compactlyGenerated hS
  let e := he.isEmbedding.toHomeomorph
  let c : Kelley (X × Y) → S := fun x => ⟨p x, mem_range_self x⟩
  let b : S → range (Prod.map f g) := fun x => ⟨Subtype.val x, x.property⟩
  have hb : Continuous b :=
    ((continuous_Kelley_forget (X := X' × Y')).comp continuous_subtype_val).subtype_mk _
  let r : S → Kelley (X × Y) := fun x => e.symm (b x)
  have hr : Continuous r := continuous_to_Kelley (X := S) (Y := X × Y) (e.symm.continuous.comp hb)
  have hrc : RightInverse c r := fun x => e.symm_apply_apply x
  exact ⟨IsEmbedding.subtypeVal.comp (hrc.isEmbedding hr (hp.subtype_mk _)), hS⟩

private theorem isClosed_kelleyDiagonal_iff (X : Type u) [TopologicalSpace X] :
    IsClosed {p : Kelley (X × X) | p.1 = p.2} ↔ KelleyClosedDiagonal X := by
  constructor
  · intro h K k
    exact h.preimage (continuous_test_to_Kelley K k)
  · intro h
    apply UCompactlyGeneratedSpace.isClosed
    intro K k
    exact h K ⟨k, continuous_Kelley_forget.comp k.continuous⟩

/-- Lemma E.2.1.11. The quotient is weakly Hausdorff precisely when the
relation is closed in the compactly generated product. -/
theorem weaklyHausdorff_quotient_iff_closed_relation (X : Type u) [TopologicalSpace X]
    [CompactlyGeneratedSpace X] (s : Setoid X) :
    WeaklyHausdorff (Quotient s) ↔ IsClosed {p : Kelley (X × X) | s p.1 p.2} := by
  let q : X → Quotient s := Quotient.mk'
  have hq : IsQuotientMap q := isQuotientMap_quotient_mk'
  rw [weaklyHausdorff_iff_kelleyClosedDiagonal, ← isClosed_kelleyDiagonal_iff,
    ← (kelleyProduct_quotient hq hq).isClosed_preimage]
  have heq : (Prod.map q q : Kelley (X × X) → Kelley (Quotient s × Quotient s)) ⁻¹'
      {p | p.1 = p.2} = {p | s p.1 p.2} := by
    ext p
    exact Quotient.eq''
  exact heq ▸ Iff.rfl

private theorem closed_kelleyKernel {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (hY : WeaklyHausdorff Y) (f : C(X, Y)) :
    IsClosed {p : Kelley (X × X) | f p.1 = f p.2} :=
  ((isClosed_kelleyDiagonal_iff Y).mpr (weaklyHausdorff_kelleyClosedDiagonal hY)).preimage
    (continuous_kelleyProductMap f.continuous f.continuous)

/-- The least closed equivalence relation containing the given pairs.
With no prescribed pairs, its quotient is the weak Hausdorff reflection. -/
def closedKelleyRelation {X : Type u} [TopologicalSpace X] (pairs : Set (X × X)) : Setoid X where
  r x y := ∀ s : Setoid X, IsClosed {p : Kelley (X × X) | s p.1 p.2} →
    (∀ p ∈ pairs, s p.1 p.2) → s x y
  iseqv := ⟨fun x s _ _ => s.refl x, fun h s hs hp => s.symm (h s hs hp),
    fun h₁ h₂ s hs hp => s.trans (h₁ s hs hp) (h₂ s hs hp)⟩

theorem closedKelleyRelation_isClosed {X : Type u} [TopologicalSpace X] (pairs : Set (X × X)) :
    IsClosed {p : Kelley (X × X) | closedKelleyRelation pairs p.1 p.2} := by
  let I := {s : Setoid X // IsClosed {p : Kelley (X × X) | s p.1 p.2} ∧
    ∀ p ∈ pairs, s p.1 p.2}
  have heq : {p : Kelley (X × X) | closedKelleyRelation pairs p.1 p.2} =
      ⋂ s : I, {p : Kelley (X × X) | s.val p.1 p.2} := by
    ext p
    simp only [mem_iInter, mem_ofPred_eq]
    exact ⟨fun h s => h s.val s.property.1 s.property.2,
      fun h s hs hp => h ⟨s, hs, hp⟩⟩
  rw [heq]
  exact isClosed_iInter fun s => s.property.1

theorem weaklyHausdorff_closedKelleyQuotient {X : Type u} [TopologicalSpace X]
    [CompactlyGeneratedSpace X] (pairs : Set (X × X)) :
    WeaklyHausdorff (Quotient (closedKelleyRelation pairs)) :=
  (weaklyHausdorff_quotient_iff_closed_relation X _).mpr (closedKelleyRelation_isClosed pairs)

/-- Continuous maps into weakly Hausdorff spaces descend through the least
closed relation whenever they identify the specified pairs. -/
def closedKelleyLift {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (pairs : Set (X × X)) (hY : WeaklyHausdorff Y) (f : C(X, Y))
    (hf : ∀ p ∈ pairs, f p.1 = f p.2) : C(Quotient (closedKelleyRelation pairs), Y) := by
  have h (a b : X) (hab : closedKelleyRelation pairs a b) : f a = f b :=
    hab (Setoid.ker f) (closed_kelleyKernel hY f) hf
  exact ⟨Quotient.lift f h, f.continuous.quotient_lift h⟩

end Quotients

/-- The full subcategory of weakly Hausdorff objects in CG. -/
def cgwhProperty : ObjectProperty CompactlyGenerated.{u, u} := fun X => WeaklyHausdorff X

abbrev CGWH := cgwhProperty.{u}.FullSubcategory

abbrev cgwhForget : CGWH.{u} ⥤ CompactlyGenerated.{u, u} := cgwhProperty.ι

private abbrev weakHausdorffObject (X : CompactlyGenerated.{u, u}) : CGWH.{u} :=
  ⟨CompactlyGenerated.of (Quotient (closedKelleyRelation (∅ : Set (X × X)))),
    weaklyHausdorff_closedKelleyQuotient _⟩

private def weakHausdorffUnit (X : CompactlyGenerated.{u, u}) :
    X ⟶ cgwhForget.obj (weakHausdorffObject X) :=
  ConcreteCategory.ofHom (⟨@Quotient.mk' X (closedKelleyRelation ∅), continuous_quotient_mk'⟩ :
    C(X, Quotient (closedKelleyRelation ∅)))

private def weakHausdorffHomEquiv (X : CompactlyGenerated.{u, u}) (Y : CGWH.{u}) :
    (weakHausdorffObject X ⟶ Y) ≃ (X ⟶ cgwhForget.obj Y) where
  toFun f := weakHausdorffUnit X ≫ f.hom
  invFun f := ObjectProperty.homMk (ConcreteCategory.ofHom
    (closedKelleyLift ∅ Y.property f.hom.hom (by simp)))
  left_inv f := by
    apply ObjectProperty.hom_ext
    ext q
    obtain ⟨x, rfl⟩ := Quotient.exists_rep q
    rfl
  right_inv f := by ext x; rfl

/-- The weak Hausdorff reflection of Lemma E.2.2.4. -/
def weakHausdorffFunctor : CompactlyGenerated.{u, u} ⥤ CGWH.{u} where
  obj := weakHausdorffObject
  map {X Y} f := (weakHausdorffHomEquiv X (weakHausdorffObject Y)).symm (f ≫ weakHausdorffUnit Y)
  map_id X := by
    apply (weakHausdorffHomEquiv X _).injective
    rw [Equiv.apply_symm_apply]
    exact (Category.comp_id _).symm
  map_comp {X Y Z} f g := by
    apply (weakHausdorffHomEquiv X _).injective
    rw [Equiv.apply_symm_apply]
    have hy := (weakHausdorffHomEquiv Y (weakHausdorffObject Z)).apply_symm_apply
      (g ≫ weakHausdorffUnit Z)
    have hx := (weakHausdorffHomEquiv X (weakHausdorffObject Y)).apply_symm_apply
      (f ≫ weakHausdorffUnit Y)
    change weakHausdorffUnit Y ≫ _ = _ at hy
    change weakHausdorffUnit X ≫ _ = _ at hx
    change (f ≫ g) ≫ _ = weakHausdorffUnit X ≫ _ ≫ _
    rw [← Category.assoc, hx]
    simp only [Category.assoc, hy]

def weakHausdorffAdjunction : weakHausdorffFunctor.{u} ⊣ cgwhForget.{u} := by
  apply Adjunction.mkOfHomEquiv
  refine { homEquiv := weakHausdorffHomEquiv
           homEquiv_naturality_left_symm := ?_
           homEquiv_naturality_right := ?_ }
  · intro X Y Z f g
    apply (weakHausdorffHomEquiv X _).injective
    change (weakHausdorffHomEquiv X Z) ((weakHausdorffHomEquiv X Z).symm (f ≫ g)) =
      (weakHausdorffHomEquiv X Z)
        ((weakHausdorffHomEquiv X (weakHausdorffObject Y)).symm (f ≫ weakHausdorffUnit Y) ≫
          (weakHausdorffHomEquiv Y Z).symm g)
    rw [Equiv.apply_symm_apply]
    have hf := (weakHausdorffHomEquiv X (weakHausdorffObject Y)).apply_symm_apply
      (f ≫ weakHausdorffUnit Y)
    have hg := (weakHausdorffHomEquiv Y Z).apply_symm_apply g
    change weakHausdorffUnit X ≫ _ = _ at hf
    change weakHausdorffUnit Y ≫ _ = _ at hg
    change _ = weakHausdorffUnit X ≫ _ ≫ _
    rw [← Category.assoc, hf, Category.assoc, hg]
  · intro X Y Y' f g
    change weakHausdorffUnit X ≫ f.hom ≫ g.hom = (weakHausdorffUnit X ≫ f.hom) ≫ g.hom
    exact (Category.assoc _ _ _).symm

theorem weakHausdorffUnit_isQuotientMap (X : CompactlyGenerated.{u, u}) :
    IsQuotientMap ((weakHausdorffAdjunction.{u}).unit.app X) := isQuotientMap_quotient_mk'

theorem weakHausdorffUnit_isIso_of_weaklyHausdorff (X : CompactlyGenerated.{u, u})
    (hX : WeaklyHausdorff X) : IsIso ((weakHausdorffAdjunction.{u}).unit.app X) :=
  weakHausdorffAdjunction.isIso_unit_app_of_iso (X := (⟨X, hX⟩ : CGWH.{u})) (Iso.refl X)

theorem weakHausdorff_map_unit_isIso (X : CompactlyGenerated.{u, u}) :
    IsIso (weakHausdorffFunctor.{u}.map ((weakHausdorffAdjunction.{u}).unit.app X)) := by
  have he := IsIso.eq_inv_of_inv_hom_id (weakHausdorffAdjunction.left_triangle_components X)
  rw [he]
  infer_instance

private theorem weaklyHausdorff_of_jointly_injective {I X : Type u} {Y : I → Type u}
    [TopologicalSpace X] [CompactlyGeneratedSpace X] [∀ i, TopologicalSpace (Y i)]
    (p : ∀ i, C(X, Y i)) (hY : ∀ i, WeaklyHausdorff (Y i))
    (hinj : ∀ x y, (∀ i, p i x = p i y) → x = y) : WeaklyHausdorff X := by
  apply (weaklyHausdorff_iff_kelleyClosedDiagonal X).mpr
  intro K k
  have heq : {z | (k z).1 = (k z).2} = ⋂ i, {z | p i (k z).1 = p i (k z).2} := by
    ext z
    simp only [mem_ofPred_eq, mem_iInter]
    exact ⟨fun h i => congrArg (p i) h, hinj _ _⟩
  rw [heq]
  exact isClosed_iInter fun i => weaklyHausdorff_kelleyClosedDiagonal (hY i) K
    ⟨_, ((p i).continuous.prodMap (p i).continuous).comp k.continuous⟩

theorem topologicalLimit_jointly_injective {J : Type u} [SmallCategory J]
    (P : J ⥤ TopCat.{u}) (x y : ((limit P : TopCat.{u}) : Type u))
    (h : ∀ j, limit.π P j x = limit.π P j y) : x = y := by
  let hc := isLimitOfPreserves (forget TopCat) (limit.isLimit P)
  let c (z : ((limit P : TopCat.{u}) : Type u)) : (PUnit : Type u) ⟶ (forget TopCat).obj (limit P) :=
    TypeCat.ofHom (fun _ => z)
  have he : c x = c y := hc.hom_ext (fun j => ConcreteCategory.hom_ext _ _ (fun _ => h j))
  exact ConcreteCategory.congr_hom he PUnit.unit

/-- The Kelley product of two weakly Hausdorff spaces is weakly Hausdorff. -/
theorem weaklyHausdorff_kelleyProduct {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (hX : WeaklyHausdorff X) (hY : WeaklyHausdorff Y) : WeaklyHausdorff (Kelley (X × Y)) := by
  apply (weaklyHausdorff_iff_kelleyClosedDiagonal _).mpr
  intro K k
  let p : C(Kelley (X × Y), X) := ⟨Prod.fst, continuous_fst.comp continuous_Kelley_forget⟩
  let q : C(Kelley (X × Y), Y) := ⟨Prod.snd, continuous_snd.comp continuous_Kelley_forget⟩
  have hx := weaklyHausdorff_kelleyClosedDiagonal hX K
    ⟨_, (p.continuous.prodMap p.continuous).comp k.continuous⟩
  have hy := weaklyHausdorff_kelleyClosedDiagonal hY K
    ⟨_, (q.continuous.prodMap q.continuous).comp k.continuous⟩
  convert hx.inter hy using 1
  ext z
  exact Prod.ext_iff

/-- Pair two continuous maps into a Kelley product from a compactly generated space. -/
def kelleyPair {T X Y : Type u} [TopologicalSpace T] [TopologicalSpace X] [TopologicalSpace Y]
    [CompactlyGeneratedSpace T] (f : C(T, X)) (g : C(T, Y)) : C(T, Kelley (X × Y)) :=
  ⟨fun t => (f t, g t), continuous_to_Kelley (X := T) (Y := X × Y)
    (f.continuous.prodMk g.continuous)⟩

/-- Lemma E.2.2.5(1). Limits in CGWH are computed in CG. -/
noncomputable def cgwhLimit {J : Type u} [SmallCategory J] (P : J ⥤ CGWH.{u}) : LimitCone P := by
  let c := kelleyLimit (P ⋙ cgwhForget)
  have hp : WeaklyHausdorff c.cone.pt := by
    exact weaklyHausdorff_of_jointly_injective (X := (c.cone.pt : Type u))
      (Y := fun j => ((P.obj j).obj : Type u)) (fun j => (c.cone.π.app j).hom.hom)
      (fun j => (P.obj j).property) (fun x y h =>
        topologicalLimit_jointly_injective
          ((P ⋙ cgwhForget) ⋙ CompactlyGenerated.compactlyGeneratedToTop) x y h)
  let d : Cone P := {
    pt := ⟨c.cone.pt, hp⟩
    π := {
      app := fun j => ObjectProperty.homMk (c.cone.π.app j)
      naturality := fun i j f => cgwhForget.map_injective (c.cone.π.naturality f) } }
  exact ⟨d, isLimitOfReflects cgwhForget c.isLimit⟩

/-- Lemma E.2.2.5(2). Colimits in CGWH are weak Hausdorff reflections
of the corresponding colimits in CG. -/
noncomputable def cgwhColimit {J : Type u} [SmallCategory J] (P : J ⥤ CGWH.{u}) : ColimitCocone P := by
  letI : PreservesColimitsOfSize.{u, u} weakHausdorffFunctor :=
    weakHausdorffAdjunction.leftAdjoint_preservesColimits
  let c := kelleyColimit (P ⋙ cgwhForget)
  let e : (P ⋙ cgwhForget) ⋙ weakHausdorffFunctor ≅ P :=
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft P (asIso weakHausdorffAdjunction.counit) ≪≫
      Functor.rightUnitor P
  exact ⟨(Cocone.precompose e.inv).obj (weakHausdorffFunctor.mapCocone c.cocone),
    (IsColimit.precomposeInvEquiv e _).symm (isColimitOfPreserves weakHausdorffFunctor c.isColimit)⟩

theorem cgwhForget_preserves_limits : PreservesLimitsOfSize.{u, u} cgwhForget.{u} :=
  weakHausdorffAdjunction.rightAdjoint_preservesLimits

theorem cgwhForget_reflects_limits : ReflectsLimitsOfSize.{u, u} cgwhForget.{u} := inferInstance

private theorem regularEpi_iff_comparison_iso {C : Type*} [Category C] {X Y : C} (f : X ⟶ Y) :
    (∃ (R : C) (s t : R ⟶ X) (c : Cofork s t), Nonempty (IsColimit c) ∧
      ∃ e : c.pt ≅ Y, c.π ≫ e.hom = f) ↔ Nonempty (RegularEpi f) := by
  constructor
  · rintro ⟨R, s, t, c, ⟨hc⟩, e, he⟩
    have hf : s ≫ f = t ≫ f := by rw [← he, ← Category.assoc, c.condition, Category.assoc]
    let d := Cofork.ofπ f hf
    have hd : IsColimit d := hc.ofIsoColimit (Cofork.ext e he)
    exact ⟨{ W := R, left := s, right := t, w := hf, isColimit := hd }⟩
  · rintro ⟨h⟩
    exact ⟨h.W, h.left, h.right, Cofork.ofπ f h.w, ⟨h.isColimit⟩, Iso.refl _, Category.comp_id _⟩

namespace CGWH

abbrev of {X : Type u} [TopologicalSpace X] [CompactlyGeneratedSpace X]
    (hX : WeaklyHausdorff X) : CGWH.{u} := ⟨CompactlyGenerated.of X, hX⟩

abbrev map {X Y : CGWH.{u}} (f : C(X.obj, Y.obj)) : X ⟶ Y :=
  ObjectProperty.homMk (ConcreteCategory.ofHom f)

theorem ext_hom {X Y : CGWH.{u}} {f g : X ⟶ Y}
    (h : ∀ x, f.hom x = g.hom x) : f = g :=
  cgwhForget.map_injective (ConcreteCategory.hom_ext _ _ h)

private theorem weaklyHausdorff_sigma {I : Type u} {X : I → Type u}
    [∀ i, TopologicalSpace (X i)] (hX : ∀ i, WeaklyHausdorff (X i)) :
    WeaklyHausdorff (Σ i, X i) := by
  intro K k
  apply isClosed_sigma_iff.mpr
  intro i
  let e := (IsEmbedding.sigmaMk (i := i) (σ := X)).toHomeomorph
  let S := k ⁻¹' range (Sigma.mk i : X i → Σ i, X i)
  have hS : IsClosed S := isClosed_range_sigmaMk.preimage k.continuous
  letI : CompactSpace S := isCompact_iff_compactSpace.mp hS.isCompact
  let b : C(S, range (Sigma.mk i : X i → Σ i, X i)) := ⟨fun x => ⟨k x, x.property⟩,
    (k.continuous.comp continuous_subtype_val).subtype_mk _⟩
  let l : C(S, X i) := ⟨fun x => e.symm (b x), e.symm.continuous.comp b.continuous⟩
  have he (x : S) : Sigma.mk i (l x) = k x := by
    exact congrArg Subtype.val (e.apply_symm_apply (b x))
  have hset : Sigma.mk i ⁻¹' range k = range l := by
    ext x
    constructor
    · rintro ⟨z, hz⟩
      let a : S := ⟨z, ⟨x, hz.symm⟩⟩
      exact ⟨a, sigma_mk_injective ((he a).trans hz)⟩
    · rintro ⟨z, rfl⟩
      exact ⟨z, (he z).symm⟩
  rw [hset]
  exact hX i (CompHaus.of S) l

/-- Corollary E.2.2.9(1): products are computed in CG. -/
noncomputable def productCone {I : Type u} (X : I → CGWH.{u}) :
    LimitCone (Discrete.functor X) := cgwhLimit (Discrete.functor X)

/-- Corollary E.2.2.9(2): the ordinary topological disjoint union is the coproduct. -/
abbrev coproductCofan {I : Type u} (X : I → CGWH.{u}) : Cofan X :=
  let Z := of (X := Σ i, (X i).obj) (weaklyHausdorff_sigma fun i => (X i).property)
  Cofan.mk Z (fun i => map (X := X i) (Y := Z)
    ({ toFun := @Sigma.mk I (fun i => ((X i).obj : Type u)) i
       continuous_toFun := continuous_sigmaMk } : C((X i).obj, (Σ i, (X i).obj))))

def coproductCofan_isColimit {I : Type u} (X : I → CGWH.{u}) : IsColimit (coproductCofan X) := by
  let d (s : Cofan X) : C((Σ i, (X i).obj), s.pt.obj) :=
    ⟨fun x => (s.inj x.1).hom x.2, continuous_sigma fun i => (s.inj i).hom.hom.hom.continuous⟩
  refine Cofan.IsColimit.mk _ (fun s => ?_) ?_ ?_
  · apply map
    exact d s
  · exact fun _ _ => ext_hom fun _ => rfl
  · intro s m h
    apply ext_hom
    intro z
    change (Σ i, (X i).obj) at z
    rcases z with ⟨i, x⟩
    exact ConcreteCategory.congr_hom (congrArg InducedCategory.Hom.hom (h i)) x

private def coequalizerPairs {R X : CGWH.{u}} (s t : R ⟶ X) : Set (X.obj × X.obj) :=
  range fun x => (s.hom x, t.hom x)

private def quotientCofork {R X : CGWH.{u}} (s t : R ⟶ X) : Cofork s t := by
  let pairs := coequalizerPairs s t
  let Z := of (weaklyHausdorff_closedKelleyQuotient pairs)
  let q : X ⟶ Z := map ⟨@Quotient.mk' X.obj (closedKelleyRelation pairs), continuous_quotient_mk'⟩
  refine Cofork.ofπ q (ext_hom fun x => ?_)
  exact Quotient.sound (fun r _ hr => hr (s.hom x, t.hom x) (mem_range_self x))

private theorem quotientCofork_isQuotientMap {R X : CGWH.{u}} (s t : R ⟶ X) :
    IsQuotientMap (quotientCofork s t).π.hom := isQuotientMap_quotient_mk'

private def quotientCofork_isColimit {R X : CGWH.{u}} (s t : R ⟶ X) :
    IsColimit (quotientCofork s t) := by
  refine Cofork.IsColimit.mk' _ fun c => ?_
  have hc : ∀ p ∈ coequalizerPairs s t, c.π.hom p.1 = c.π.hom p.2 := by
    rintro _ ⟨x, rfl⟩
    exact ConcreteCategory.congr_hom (congrArg InducedCategory.Hom.hom c.condition) x
  let l : (quotientCofork s t).pt ⟶ c.pt := map
    (closedKelleyLift _ c.pt.property c.π.hom.hom.hom hc)
  refine ⟨l, ext_hom (fun _ => rfl), ?_⟩
  intro m hm
  apply ext_hom
  intro z
  obtain ⟨x, rfl⟩ := (quotientCofork_isQuotientMap s t).surjective z
  exact ConcreteCategory.congr_hom (congrArg InducedCategory.Hom.hom hm) x

private theorem isQuotientMap_of_regularEpi {X Y : CGWH.{u}} {f : X ⟶ Y}
    (hf : RegularEpi f) : IsQuotientMap f.hom := by
  let e : (quotientCofork hf.left hf.right).pt ≅ Y :=
    (quotientCofork_isColimit hf.left hf.right).coconePointUniqueUpToIso hf.isColimit
  have he := IsColimit.comp_coconePointUniqueUpToIso_hom
    (quotientCofork_isColimit hf.left hf.right) hf.isColimit WalkingParallelPair.one
  have hq := (CompactlyGenerated.homeoOfIso (cgwhForget.mapIso e)).isQuotientMap.comp
    (quotientCofork_isQuotientMap hf.left hf.right)
  have hfe : (quotientCofork hf.left hf.right).π ≫ e.hom = f := he
  have hfun := congrArg (fun g : X ⟶ Y => (g.hom : X.obj → Y.obj)) hfe
  exact hfun ▸ hq

private abbrev KernelPoints {X Y : CGWH.{u}} (f : X ⟶ Y) :=
  {p : X.obj × X.obj // f.hom p.1 = f.hom p.2}

private def kernelProjection {X Y : CGWH.{u}} (f : X ⟶ Y) (b : ULift.{u} Bool) :
    C(Kelley (KernelPoints f), X.obj) :=
  if b.down then ⟨fun p => p.val.1,
    (continuous_fst.comp continuous_subtype_val).comp
      (continuous_Kelley_forget (X := KernelPoints f))⟩
  else ⟨fun p => p.val.2,
    (continuous_snd.comp continuous_subtype_val).comp
      (continuous_Kelley_forget (X := KernelPoints f))⟩

private def kernelObject {X Y : CGWH.{u}} (f : X ⟶ Y) : CGWH.{u} :=
  of (weaklyHausdorff_of_jointly_injective (kernelProjection f) (fun _ => X.property)
    (fun _ _ h => Subtype.ext (Prod.ext (h ⟨true⟩) (h ⟨false⟩))))

private abbrev kernelFirst {X Y : CGWH.{u}} (f : X ⟶ Y) : kernelObject f ⟶ X :=
  map (kernelProjection f ⟨true⟩)

private abbrev kernelSecond {X Y : CGWH.{u}} (f : X ⟶ Y) : kernelObject f ⟶ X :=
  map (kernelProjection f ⟨false⟩)

private theorem kernelPair {X Y : CGWH.{u}} (f : X ⟶ Y) :
    IsKernelPair f (kernelFirst f) (kernelSecond f) := by
  have h : kernelFirst f ≫ f = kernelSecond f ≫ f := ext_hom fun p => p.property
  refine ⟨⟨h⟩, ⟨PullbackCone.IsLimit.mk _ ?_ ?_ ?_ ?_⟩⟩
  · intro c
    have eq (x : c.pt.obj) : f.hom (c.fst.hom x) = f.hom (c.snd.hom x) :=
      ConcreteCategory.congr_hom (congrArg InducedCategory.Hom.hom c.condition) x
    exact map ⟨fun x => ⟨(c.fst.hom x, c.snd.hom x), eq x⟩, continuous_to_Kelley
      ((c.fst.hom.hom.hom.continuous.prodMk c.snd.hom.hom.hom.continuous).subtype_mk eq)⟩
  · intro c
    exact ext_hom fun _ => rfl
  · intro c
    exact ext_hom fun _ => rfl
  · intro c m h₁ h₂
    apply ext_hom
    intro x
    apply Subtype.ext
    apply Prod.ext
    · have hx := ConcreteCategory.congr_hom (congrArg InducedCategory.Hom.hom h₁) x
      exact hx
    · have hx := ConcreteCategory.congr_hom (congrArg InducedCategory.Hom.hom h₂) x
      exact hx

private noncomputable def kernelCoequalizerOfQuotient {X Y : CGWH.{u}} (f : X ⟶ Y)
    (hf : IsQuotientMap f.hom) : IsColimit (Cofork.ofπ f (kernelPair f).w) := by
  refine Cofork.IsColimit.mk' _ fun c => ?_
  have hc (a b : X.obj) (hab : f.hom a = f.hom b) : c.π.hom a = c.π.hom b :=
    ConcreteCategory.congr_hom (congrArg InducedCategory.Hom.hom c.condition)
      (⟨(a, b), hab⟩ : KernelPoints f)
  let d := hf.lift c.π.hom.hom.hom hc
  have hd := hf.lift_comp c.π.hom.hom.hom hc
  refine ⟨map d, ext_hom (fun x => DFunLike.congr_fun hd x), ?_⟩
  intro m hm
  apply ext_hom
  intro y
  obtain ⟨x, rfl⟩ := hf.surjective y
  exact (ConcreteCategory.congr_hom (congrArg InducedCategory.Hom.hom hm) x).trans
    (DFunLike.congr_fun hd x).symm

/-- Corrected Lemma E.2.3.8. The first clause identifies the codomain with
the coequalizer, via the isomorphism implicit in `RegularEpi`. -/
theorem quotient_iff_coequalizer {X Y : CGWH.{u}} (f : X ⟶ Y) :
    (Nonempty (RegularEpi f) ↔ IsQuotientMap f.hom) ∧
    (Nonempty (IsColimit (Cofork.ofπ f (kernelPair f).w)) ↔ IsQuotientMap f.hom) := by
  refine ⟨⟨fun ⟨h⟩ => isQuotientMap_of_regularEpi h, ?_⟩,
    ⟨fun ⟨h⟩ => isQuotientMap_of_regularEpi (Cofork.IsColimit.regularEpi h),
      fun h => ⟨kernelCoequalizerOfQuotient f h⟩⟩⟩
  intro h
  exact ⟨Cofork.IsColimit.regularEpi (kernelCoequalizerOfQuotient f h)⟩

/-- The codomain identification in the repaired first clause is an isomorphism. -/
theorem quotient_iff_comparison_iso {X Y : CGWH.{u}} (f : X ⟶ Y) :
    (∃ (R : CGWH.{u}) (s t : R ⟶ X) (c : Cofork s t), Nonempty (IsColimit c) ∧
      ∃ e : c.pt ≅ Y, c.π ≫ e.hom = f) ↔ IsQuotientMap f.hom :=
  (regularEpi_iff_comparison_iso f).trans (quotient_iff_coequalizer f).1

/-- The unchanged printed comparison condition holds for a nonsurjective map. -/
theorem continuous_coequalizer_comparison_counterexample :
    ∃ (X Y : CGWH.{0}) (f : X ⟶ Y), ¬ IsQuotientMap f.hom ∧
      ∃ (R : CGWH.{0}) (s t : R ⟶ X) (c : Cofork s t), Nonempty (IsColimit c) ∧
        ∃ g : c.pt ⟶ Y, c.π ≫ g = f := by
  let X := of (X := PUnit) (fun _ k => (isCompact_range k.continuous).isClosed)
  let Y := of (X := Bool) (fun _ k => (isCompact_range k.continuous).isClosed)
  let f : X ⟶ Y := map ⟨fun _ => false, continuous_const⟩
  refine ⟨X, Y, f, ?_, X, 𝟙 X, 𝟙 X, idCofork rfl, ⟨isColimitIdCofork rfl⟩, f, ?_⟩
  · intro h
    obtain ⟨x, hx⟩ := h.surjective true
    exact Bool.noConfusion hx
  · exact Category.id_comp f

end CGWH

section CGCoequalizers

local notation "UCG" => CompactlyGenerated.compactlyGeneratedToTop

private noncomputable abbrev cgHasKernelPair {X Y : CompactlyGenerated.{u, u}} (f : X ⟶ Y) :
    HasPullback f f := HasLimit.mk (kelleyLimit (cospan f f))

private theorem cg_equal_on_fibres {X Y Z : CompactlyGenerated.{u, u}} (f : X ⟶ Y) (g : X ⟶ Z)
    (h : ∀ ⦃T : CompactlyGenerated.{u, u}⦄ (a b : T ⟶ X),
      a ≫ f = b ≫ f → a ≫ g = b ≫ g) : ∀ x y, f x = f y → g x = g y := by
  intro x y hxy
  let T := CompactlyGenerated.of (PUnit : Type u)
  let a : T ⟶ X := ConcreteCategory.ofHom ⟨fun _ => x, continuous_const⟩
  let b : T ⟶ X := ConcreteCategory.ofHom ⟨fun _ => y, continuous_const⟩
  exact ConcreteCategory.congr_hom (h a b (ConcreteCategory.hom_ext _ _ fun _ => hxy)) PUnit.unit

private noncomputable def cgEffectiveEpi {X Y : CompactlyGenerated.{u, u}} (f : X ⟶ Y)
    (hf : IsQuotientMap f) : EffectiveEpiStruct f where
  desc g h := ConcreteCategory.ofHom (hf.lift g.hom.hom (cg_equal_on_fibres f g @h))
  fac {W} g h := by
    apply ConcreteCategory.hom_ext
    intro x
    exact congrArg (fun k : C(X, W) => k x)
      (hf.lift_comp g.hom.hom (cg_equal_on_fibres f g @h))
  uniq g h m hm := by
    apply ConcreteCategory.hom_ext
    intro y
    obtain ⟨x, rfl⟩ := hf.surjective y
    exact (ConcreteCategory.congr_hom hm x).trans
      (DFunLike.congr_fun (hf.lift_comp g.hom.hom (cg_equal_on_fibres f g @h)) x).symm

private theorem cg_regularEpi_isQuotientMap {X Y : CompactlyGenerated.{u, u}} {f : X ⟶ Y}
    (h : RegularEpi f) : IsQuotientMap f := by
  let U : CompactlyGenerated.{u, u} ⥤ TopCat.{u} := UCG
  letI : PreservesColimitsOfSize.{0, 0} U := kelleyAdjunction.leftAdjoint_preservesColimits
  exact TopCat.isQuotientMap_of_isColimit_cofork _ (isColimitCoforkMapOfIsColimit U _ h.isColimit)

/-- Lemma E.1.2.14. Quotient maps are precisely the regular epimorphisms,
and precisely the coequalizers of their kernel pairs. -/
theorem cg_quotient_iff_coequalizer {X Y : CompactlyGenerated.{u, u}} (f : X ⟶ Y) :
    letI := cgHasKernelPair f
    (Nonempty (RegularEpi f) ↔ IsQuotientMap f) ∧
    (Nonempty (IsColimit (Cofork.ofπ f (pullback.condition (f := f) (g := f)))) ↔ IsQuotientMap f) := by
  letI := cgHasKernelPair f
  refine ⟨⟨fun ⟨h⟩ => cg_regularEpi_isQuotientMap h, ?_⟩,
    ⟨fun ⟨h⟩ => cg_regularEpi_isQuotientMap (Cofork.IsColimit.regularEpi h), ?_⟩⟩
  · intro h
    letI : EffectiveEpi f := ⟨⟨cgEffectiveEpi f h⟩⟩
    exact ⟨regularEpiOfEffectiveEpi f⟩
  · intro h
    letI : EffectiveEpi f := ⟨⟨cgEffectiveEpi f h⟩⟩
    exact ⟨(regularEpiOfEffectiveEpi f).isColimit⟩

theorem cg_quotient_iff_comparison_iso {X Y : CompactlyGenerated.{u, u}} (f : X ⟶ Y) :
    (∃ (R : CompactlyGenerated.{u, u}) (s t : R ⟶ X) (c : Cofork s t), Nonempty (IsColimit c) ∧
      ∃ e : c.pt ≅ Y, c.π ≫ e.hom = f) ↔ IsQuotientMap f :=
  (regularEpi_iff_comparison_iso f).trans (cg_quotient_iff_coequalizer f).1

end CGCoequalizers

namespace CGWH

/-- The ordinary topological pullback, with its subspace topology. -/
abbrev FibrePoints {X Y Z : CGWH.{u}} (f : X ⟶ Y) (g : Z ⟶ Y) :=
  {p : X.obj × Z.obj // f.hom p.1 = g.hom p.2}

private theorem fibreSnd_isClosedEmbedding {X Y Z : CGWH.{u}} (f : X ⟶ Y) (g : Z ⟶ Y)
    (hf : IsClosedEmbedding f.hom) :
    IsClosedEmbedding (fun p : FibrePoints f g => p.val.2) := by
  let e := TopCat.pullbackHomeoPreimage g.hom g.hom.hom.hom.continuous f.hom hf.isEmbedding
  let swap : FibrePoints f g ≃ₜ {p : Z.obj × X.obj // g.hom p.1 = f.hom p.2} := {
    toFun := fun p => ⟨p.val.swap, p.property.symm⟩
    invFun := fun p => ⟨p.val.swap, p.property.symm⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    continuous_toFun := (continuous_swap.comp continuous_subtype_val).subtype_mk _
    continuous_invFun := (continuous_swap.comp continuous_subtype_val).subtype_mk _ }
  exact ((hf.isClosed_range.preimage g.hom.hom.hom.continuous).isClosedEmbedding_subtypeVal.comp
    e.isClosedEmbedding).comp swap.isClosedEmbedding

/-- Lemma E.2.3.9. If the ordinary pullback projects by a closed embedding,
it already represents the pullback in CGWH. -/
noncomputable def topologicalPullbackOfClosedProjection {X Y Z : CGWH.{u}}
    (f : X ⟶ Y) (g : Z ⟶ Y) (h : IsClosedEmbedding (fun p : FibrePoints f g => p.val.2)) :
    LimitCone (cospan f g) := by
  let e := h.isEmbedding.toHomeomorph
  letI := closed_compactlyGenerated h.isClosed_range
  letI : CompactlyGeneratedSpace (FibrePoints f g) :=
    compactlyGeneratedSpace_of_coinduced e.symm.continuous e.symm.isQuotientMap.eq_coinduced
  let A := of (X := FibrePoints f g) (by
    intro K k
    have hk := Z.property K ⟨fun x => (k x).val.2, h.continuous.comp k.continuous⟩
    have heq : range k = (fun p : FibrePoints f g => p.val.2) ⁻¹'
        range (fun x => (k x).val.2) := by
      ext p
      exact ⟨fun ⟨x, hx⟩ => ⟨x, congrArg (fun q : FibrePoints f g => q.val.2) hx⟩,
        fun ⟨x, hx⟩ => ⟨x, h.injective hx⟩⟩
    rw [heq]
    exact hk.preimage h.continuous)
  let p : A ⟶ X := map ⟨fun x => x.val.1, continuous_fst.comp continuous_subtype_val⟩
  let q : A ⟶ Z := map ⟨fun x => x.val.2, continuous_snd.comp continuous_subtype_val⟩
  have hpq : p ≫ f = q ≫ g := ext_hom fun x => x.property
  refine ⟨PullbackCone.mk p q hpq, PullbackCone.IsLimit.mk hpq ?_ ?_ ?_ ?_⟩
  · intro c
    have eq (x : c.pt.obj) : f.hom (c.fst.hom x) = g.hom (c.snd.hom x) :=
      ConcreteCategory.congr_hom (congrArg InducedCategory.Hom.hom c.condition) x
    exact map ⟨fun x => ⟨(c.fst.hom x, c.snd.hom x), eq x⟩,
      (c.fst.hom.hom.hom.continuous.prodMk c.snd.hom.hom.hom.continuous).subtype_mk eq⟩
  · exact fun _ => ext_hom fun _ => rfl
  · exact fun _ => ext_hom fun _ => rfl
  · intro c m h₁ h₂
    apply ext_hom
    intro x
    apply Subtype.ext
    apply Prod.ext
    · have hx := ConcreteCategory.congr_hom (congrArg InducedCategory.Hom.hom h₁) x
      exact hx
    · have hx := ConcreteCategory.congr_hom (congrArg InducedCategory.Hom.hom h₂) x
      exact hx

/-- In particular the ordinary pullback along a closed embedding computes
the CGWH pullback. -/
noncomputable def topologicalPullbackOfClosedEmbedding {X Y Z : CGWH.{u}}
    (f : X ⟶ Y) (g : Z ⟶ Y) (hf : IsClosedEmbedding f.hom) : LimitCone (cospan f g) :=
  topologicalPullbackOfClosedProjection f g (fibreSnd_isClosedEmbedding f g hf)

private theorem quotient_restrict_closed {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    {q : X → Y} (hq : IsQuotientMap q) {S : Set Y} (hS : IsClosed S) :
    IsQuotientMap (S.restrictPreimage q) := by
  apply isQuotientMap_iff_isClosed.mpr
  refine ⟨hq.surjective.restrictPreimage _, fun A => ?_⟩
  rw [hS.isClosedEmbedding_subtypeVal.isClosed_iff_image_isClosed,
    (hS.preimage hq.continuous).isClosedEmbedding_subtypeVal.isClosed_iff_image_isClosed,
    image_val_preimage_restrictPreimage, hq.isClosed_preimage]

/-- The CGWH fibre product as a closed subspace of the Kelley product. -/
abbrev FibreSubspace {X Y Z : CGWH.{u}} (f : X ⟶ Y) (g : Z ⟶ Y) :=
  {p : Kelley (X.obj × Z.obj) // f.hom p.1 = g.hom p.2}

theorem fibreSubspace_isClosed {X Y Z : CGWH.{u}} (f : X ⟶ Y) (g : Z ⟶ Y) :
    IsClosed {p : Kelley (X.obj × Z.obj) | f.hom p.1 = g.hom p.2} := by
  let k := continuous_Kelley_forget (X := X.obj × Z.obj)
  let a : C(Kelley (X.obj × Z.obj), Y.obj) :=
    ⟨fun p => f.hom p.1, f.hom.hom.hom.continuous.comp (continuous_fst.comp k)⟩
  let b : C(Kelley (X.obj × Z.obj), Y.obj) :=
    ⟨fun p => g.hom p.2, g.hom.hom.hom.continuous.comp (continuous_snd.comp k)⟩
  exact cgwh_isClosed_equalizer Y.property a b

private def fibreFst {X Y Z : CGWH.{u}} (f : X ⟶ Y) (g : Z ⟶ Y) : C(FibreSubspace f g, X.obj) :=
  ⟨fun p => p.val.1, continuous_fst.comp (continuous_Kelley_forget.comp continuous_subtype_val)⟩

private def fibreSnd {X Y Z : CGWH.{u}} (f : X ⟶ Y) (g : Z ⟶ Y) : C(FibreSubspace f g, Z.obj) :=
  ⟨fun p => p.val.2, continuous_snd.comp (continuous_Kelley_forget.comp continuous_subtype_val)⟩

private instance fibreSubspace_compactlyGenerated {X Y Z : CGWH.{u}} (f : X ⟶ Y) (g : Z ⟶ Y) :
    CompactlyGeneratedSpace (FibreSubspace f g) := closed_compactlyGenerated (fibreSubspace_isClosed f g)

theorem fibreSubspace_weaklyHausdorff {X Y Z : CGWH.{u}} (f : X ⟶ Y) (g : Z ⟶ Y) :
    WeaklyHausdorff (FibreSubspace f g) := by
  apply (weaklyHausdorff_iff_kelleyClosedDiagonal _).mpr
  intro K k
  have h₁ := weaklyHausdorff_kelleyClosedDiagonal X.property K
    ⟨_, ((fibreFst f g).continuous.prodMap (fibreFst f g).continuous).comp k.continuous⟩
  have h₂ := weaklyHausdorff_kelleyClosedDiagonal Z.property K
    ⟨_, ((fibreSnd f g).continuous.prodMap (fibreSnd f g).continuous).comp k.continuous⟩
  convert h₁.inter h₂ using 1
  ext z
  exact Subtype.ext_iff.trans Prod.ext_iff

/-- The subtype of the Kelley product computes the CGWH pullback. -/
def fibreSubspaceLimit {X Y Z : CGWH.{u}} (f : X ⟶ Y) (g : Z ⟶ Y) : LimitCone (cospan f g) := by
  let T := of (X := FibreSubspace f g) (fibreSubspace_weaklyHausdorff f g)
  let p : T ⟶ X := map (fibreFst f g)
  let q : T ⟶ Z := map (fibreSnd f g)
  have hpq : p ≫ f = q ≫ g := ext_hom fun w => w.property
  refine ⟨PullbackCone.mk p q hpq, PullbackCone.IsLimit.mk hpq ?_ ?_ ?_ ?_⟩
  · intro c
    let a := c.fst.hom.hom.hom
    let b := c.snd.hom.hom.hom
    have eq (x : c.pt.obj) : f.hom (a x) = g.hom (b x) :=
      ConcreteCategory.congr_hom (congrArg InducedCategory.Hom.hom c.condition) x
    have ha : Continuous (fun x : c.pt.obj => (a x, b x)) := a.continuous.prodMk b.continuous
    exact map ⟨fun x => ⟨(a x, b x), eq x⟩,
      (continuous_to_Kelley (Y := X.obj × Z.obj) ha).subtype_mk _⟩
  · exact fun _ => ext_hom fun _ => rfl
  · exact fun _ => ext_hom fun _ => rfl
  · intro c m h₁ h₂
    apply ext_hom
    intro x
    apply Subtype.ext
    apply Prod.ext
    · have hx := ConcreteCategory.congr_hom (congrArg InducedCategory.Hom.hom h₁) x
      exact hx
    · have hx := ConcreteCategory.congr_hom (congrArg InducedCategory.Hom.hom h₂) x
      exact hx

/-- Stability of submersions under base change, the last base-change
assertion of Lemma E.2.3.6. -/
theorem quotient_baseChange {X Y Z : CGWH.{u}} (f : X ⟶ Y) (g : Z ⟶ Y)
    (hf : IsQuotientMap f.hom) : IsQuotientMap (fun p : FibreSubspace f g => p.val.2) := by
  let G : Set (Kelley (Y.obj × Z.obj)) := {p | p.1 = g.hom p.2}
  let q : Kelley (X.obj × Z.obj) → Kelley (Y.obj × Z.obj) :=
    Prod.map f.hom (id : Z.obj → Z.obj)
  have hq : IsQuotientMap q := kelleyProduct_quotient hf IsQuotientMap.id
  have hG : IsClosed G := fibreSubspace_isClosed (𝟙 Y) g
  let a : Z.obj → G := fun z => ⟨(g.hom z, z), rfl⟩
  let b : G → Z.obj := fun p => p.val.2
  have ha : Continuous a := by
    apply Continuous.subtype_mk
    exact continuous_to_Kelley (X := Z.obj) (Y := Y.obj × Z.obj)
      (g.hom.hom.hom.continuous.prodMk continuous_id)
  have hb : Continuous b := (continuous_snd.comp (continuous_Kelley_forget (X := Y.obj × Z.obj))).comp
    continuous_subtype_val
  have hab : RightInverse a b := fun _ => rfl
  have hq' := quotient_restrict_closed hq hG
  exact (IsQuotientMap.of_inverse ha hb hab).comp hq'

/-- Submersions descend along submersions, as in Lemma E.2.3.7(6). -/
theorem quotient_descends {X Y Z : CGWH.{u}} (f : X ⟶ Y) (g : Z ⟶ Y)
    (hg : IsQuotientMap g.hom) (h : IsQuotientMap (fun p : FibreSubspace f g => p.val.2)) :
    IsQuotientMap f.hom := by
  apply IsQuotientMap.of_comp (fibreFst f g).continuous f.hom.hom.hom.continuous
  have he : f.hom ∘ fibreFst f g = g.hom ∘ fibreSnd f g := funext fun p => p.property
  exact he.symm ▸ hg.comp h

/-- The disjoint union with a point before collapsing a closed subspace. -/
abbrev WithBasepoint (X : Type u) := ULift.{u} Unit ⊕ X

theorem weaklyHausdorff_sum {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (hX : WeaklyHausdorff X) (hY : WeaklyHausdorff Y) : WeaklyHausdorff (X ⊕ Y) := by
  intro K f
  apply isClosed_sum_iff.mpr
  have aux {Z : Type u} [TopologicalSpace Z] (hZ : WeaklyHausdorff Z) (i : Z → X ⊕ Y)
      (hi : IsClosedEmbedding i) : IsClosed (i ⁻¹' range f) := by
    let S := f ⁻¹' range i
    have hS : IsClosed S := hi.isClosed_range.preimage f.continuous
    letI : CompactSpace S := isCompact_iff_compactSpace.mp hS.isCompact
    let f' : C(S, range i) :=
      ⟨fun x => ⟨f x, x.property⟩, (f.continuous.comp continuous_subtype_val).subtype_mk _⟩
    let e := hi.isEmbedding.toHomeomorph
    let g : C(S, Z) := ⟨e.symm ∘ f', e.symm.continuous.comp f'.continuous⟩
    have hg (x : S) : i (g x) = f x := congrArg Subtype.val (e.apply_symm_apply (f' x))
    have hset : i ⁻¹' range f = range g := by
      ext x
      constructor
      · rintro ⟨a, ha⟩
        let b : S := ⟨a, x, ha.symm⟩
        exact ⟨b, hi.injective ((hg b).trans ha)⟩
      · rintro ⟨a, rfl⟩
        exact ⟨a, (hg a).symm⟩
    exact hset ▸ hZ (CompHaus.of S) g
  exact ⟨aux hX Sum.inl IsClosedEmbedding.inl, aux hY Sum.inr IsClosedEmbedding.inr⟩

private def collapseSetoid {X : Type u} (S : Set X) : Setoid X where
  r x y := x = y ∨ x ∈ S ∧ y ∈ S
  iseqv := ⟨fun x => Or.inl rfl, fun h => h.elim (Or.inl ∘ Eq.symm) (Or.inr ∘ And.symm),
    by
      intro a b c hab hbc
      rcases hab with rfl | ⟨ha, hb⟩
      · exact hbc
      rcases hbc with rfl | ⟨_, hc⟩
      · exact Or.inr ⟨ha, hb⟩
      · exact Or.inr ⟨ha, hc⟩⟩

private theorem collapse_weaklyHausdorff {X : Type u} [TopologicalSpace X]
    [CompactlyGeneratedSpace X] (hX : WeaklyHausdorff X) {S : Set X} (hS : IsClosed S) :
    WeaklyHausdorff (Quotient (collapseSetoid S)) := by
  apply (weaklyHausdorff_quotient_iff_closed_relation X _).mpr
  have hdiag := (isClosed_kelleyDiagonal_iff X).mpr (weaklyHausdorff_kelleyClosedDiagonal hX)
  have hpair : IsClosed {p : Kelley (X × X) | p.1 ∈ S ∧ p.2 ∈ S} :=
    ((hS.preimage continuous_fst).inter (hS.preimage continuous_snd)).preimage
      (continuous_Kelley_forget (X := X × X))
  exact hdiag.union hpair

private theorem collapse_isClosedMap {X : Type u} [TopologicalSpace X] {S : Set X}
    (hS : IsClosed S) : IsClosedMap (@Quotient.mk' X (collapseSetoid S)) := by
  let q := @Quotient.mk' X (collapseSetoid S)
  have hq : IsQuotientMap q := isQuotientMap_quotient_mk'
  intro C hC
  apply hq.isClosed_preimage.mp
  by_cases h : (S ∩ C).Nonempty
  · obtain ⟨x, hxS, hxC⟩ := h
    have he : q ⁻¹' (q '' C) = C ∪ S := by
      ext y
      constructor
      · rintro ⟨z, hz, he⟩
        rcases Quotient.exact' he with (rfl | ⟨_, hy⟩)
        · exact Or.inl hz
        · exact Or.inr hy
      · rintro (hy | hy)
        · exact ⟨y, hy, rfl⟩
        · exact ⟨x, hxC, Quotient.sound' (Or.inr ⟨hxS, hy⟩)⟩
    rw [he]
    exact hC.union hS
  · have he : q ⁻¹' (q '' C) = C := by
      ext y
      constructor
      · rintro ⟨z, hz, he⟩
        rcases Quotient.exact' he with (rfl | ⟨hzS, _⟩)
        · exact hz
        · exact (h ⟨z, hzS, hz⟩).elim
      · intro hy
        exact ⟨y, hy, rfl⟩
    rwa [he]

section PointedCollapse

variable (X : CGWH.{u}) (S : Set X.obj)

/-- The closed subset to collapse includes the disjoint base point. -/
def pointedCollapseSubset : Set (WithBasepoint X.obj) :=
  {z | z.elim (fun _ => True) (· ∈ S)}

theorem pointedCollapseSubset_isClosed (hS : IsClosed S) :
    IsClosed (pointedCollapseSubset X S) :=
  isClosed_sum_iff.mpr ⟨isClosed_univ, hS⟩

abbrev PointedCollapse := Quotient (collapseSetoid (pointedCollapseSubset X S))

private abbrev PointedSource := WithBasepoint X.obj

private theorem pointedSource_weaklyHausdorff : WeaklyHausdorff (PointedSource X) :=
  weaklyHausdorff_sum (fun _ f => (isCompact_range f.continuous).isClosed) X.property

/-- The collapsed subspace has exactly the disjoint-union topology. -/
noncomputable def pointedCollapseSubsetHomeomorph (hS : IsClosed S) :
    WithBasepoint S ≃ₜ pointedCollapseSubset X S := by
  let f : WithBasepoint S → PointedSource X := Sum.map id Subtype.val
  have hf : IsClosedEmbedding f := IsClosedEmbedding.of_continuous_injective_isClosedMap
    (continuous_sumMap.mpr ⟨continuous_id, continuous_subtype_val⟩)
    (Sum.map_injective.mpr ⟨Function.injective_id, Subtype.val_injective⟩)
    (IsClosedMap.id.sumMap hS.isClosedEmbedding_subtypeVal.isClosedMap)
  have he : range f = pointedCollapseSubset X S := by
    ext z
    cases z with
    | inl x => exact ⟨fun _ => trivial, fun _ => ⟨Sum.inl x, rfl⟩⟩
    | inr x =>
      change Sum.inr x ∈ range f ↔ x ∈ S
      constructor
      · rintro ⟨a, ha⟩
        cases a with
        | inl y =>
          change Sum.inl y = Sum.inr x at ha
          cases ha
        | inr y => exact (Sum.inr.inj ha) ▸ y.property
      · intro hx
        exact ⟨Sum.inr ⟨x, hx⟩, rfl⟩
  exact hf.isEmbedding.toHomeomorph.trans (Homeomorph.setCongr he)

/-- The topological quotient identifying the points of the closed set with the base point. -/
abbrev pointedCollapseObject (hS : IsClosed S) : CGWH.{u} :=
  of (collapse_weaklyHausdorff (pointedSource_weaklyHausdorff X)
    (pointedCollapseSubset_isClosed X S hS))

abbrev pointedCollapseMap : PointedSource X → PointedCollapse X S :=
  @Quotient.mk' _ (collapseSetoid (pointedCollapseSubset X S))

abbrev pointedCollapsePoint : PointedCollapse X S :=
  pointedCollapseMap X S (Sum.inl ⟨()⟩)

abbrev pointedCollapseInclusion : X.obj → PointedCollapse X S :=
  pointedCollapseMap X S ∘ Sum.inr

theorem pointedCollapseMap_preimage :
    pointedCollapseMap X S ⁻¹' {pointedCollapsePoint X S} = pointedCollapseSubset X S := by
  ext z
  change pointedCollapseMap X S z = pointedCollapsePoint X S ↔ z ∈ pointedCollapseSubset X S
  constructor
  · intro h
    rcases Quotient.exact' h with h | ⟨h, _⟩
    · subst z
      trivial
    · exact h
  · intro h
    exact Quotient.sound' (Or.inr ⟨h, trivial⟩)

theorem pointedCollapseInclusion_preimage :
    pointedCollapseInclusion X S ⁻¹' {pointedCollapsePoint X S} = S := by
  change Sum.inr ⁻¹' (pointedCollapseMap X S ⁻¹' {pointedCollapsePoint X S}) = S
  rw [pointedCollapseMap_preimage]
  rfl

theorem pointedCollapseInclusion_closed_quotient (hS : IsClosed S) (hne : S.Nonempty) :
    IsClosedMap (pointedCollapseInclusion X S) ∧ IsQuotientMap (pointedCollapseInclusion X S) := by
  let b := pointedCollapseMap X S
  let q := pointedCollapseInclusion X S
  have hb : IsQuotientMap b := isQuotientMap_quotient_mk'
  have hclosed : IsClosedMap q := (collapse_isClosedMap
    (pointedCollapseSubset_isClosed X S hS)).comp IsClosedEmbedding.inr.isClosedMap
  refine ⟨hclosed, (hclosed.isQuotientMap (hb.continuous.comp continuous_inr)) ?_⟩
  intro y
  obtain ⟨z, rfl⟩ := hb.surjective y
  cases z with
  | inr x => exact ⟨x, rfl⟩
  | inl i =>
    obtain ⟨x, hx⟩ := hne
    exact ⟨x, Quotient.sound' (Or.inr ⟨hx, trivial⟩)⟩

end PointedCollapse

private def collapseLift {Y : Type u} [TopologicalSpace Y] {X : CGWH.{u}} {S : Set X.obj}
    (g : C(PointedSource X, Y)) (y : Y) (hg : ∀ z ∈ pointedCollapseSubset X S, g z = y) :
    C(PointedCollapse X S, Y) := by
  have h : ∀ a b, collapseSetoid (pointedCollapseSubset X S) a b → g a = g b := by
    intro a b hab
    rcases hab with rfl | ⟨ha, hb⟩
    · rfl
    · exact (hg a ha).trans (hg b hb).symm
  exact ⟨Quotient.lift g h, g.continuous.quotient_lift h⟩

private abbrev pointedSourceObject (X : CGWH.{u}) : CGWH.{u} :=
  of (pointedSource_weaklyHausdorff X)

abbrev basepointObject : CGWH.{u} :=
  of (X := ULift.{u} Unit) (fun _ f => (isCompact_range f.continuous).isClosed)

private abbrev pointedCollapseSubsetObject (X : CGWH.{u}) (S : Set X.obj) (hS : IsClosed S) :
    CGWH.{u} :=
  letI := closed_compactlyGenerated (pointedCollapseSubset_isClosed X S hS)
  of (weaklyHausdorff_subspace (pointedSource_weaklyHausdorff X) (pointedCollapseSubset X S))

/-- The pushout square of Construction E.2.3.16, with the collapsed component
represented by its closed inclusion in the disjoint union. -/
def pointedCollapseTopPushout (X : CGWH.{u}) (S : Set X.obj) :
    ColimitCocone (span
      (C := TopCat.{u})
      (TopCat.ofHom (ContinuousMap.const (pointedCollapseSubset X S) (⟨()⟩ : ULift.{u} Unit)))
      (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ :
        C(pointedCollapseSubset X S, PointedSource X)))) := by
  let A := TopCat.of (pointedCollapseSubset X S)
  let B := TopCat.of (ULift.{u} Unit)
  let D := TopCat.of (PointedSource X)
  let Q := TopCat.of (PointedCollapse X S)
  let a : A ⟶ B := ConcreteCategory.ofHom (ContinuousMap.const _ ⟨()⟩)
  let i : A ⟶ D := ConcreteCategory.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  let x : B ⟶ Q := ConcreteCategory.ofHom (ContinuousMap.const _ (pointedCollapsePoint X S))
  let b : D ⟶ Q := ConcreteCategory.ofHom
    (⟨pointedCollapseMap X S, continuous_quotient_mk'⟩ : C(PointedSource X, PointedCollapse X S))
  have he (z : PointedSource X) (hz : z ∈ pointedCollapseSubset X S) :
      b z = pointedCollapsePoint X S := by
    change z ∈ pointedCollapseMap X S ⁻¹' {pointedCollapsePoint X S}
    rwa [pointedCollapseMap_preimage]
  have hw : a ≫ x = i ≫ b := by
    apply ConcreteCategory.hom_ext
    exact fun z => (he z z.property).symm
  let lift (c : PushoutCocone a i) : Q ⟶ c.pt :=
    ConcreteCategory.ofHom (collapseLift (X := X) (S := S) c.inr.hom (c.inl ⟨()⟩)
      (fun z hz => (ConcreteCategory.congr_hom c.condition ⟨z, hz⟩).symm))
  refine ⟨PushoutCocone.mk x b hw, PushoutCocone.IsColimit.mk hw lift ?_ ?_ ?_⟩
  · intro c
    apply ConcreteCategory.hom_ext
    intro j
    have e : j = (⟨()⟩ : ULift.{u} Unit) := Subsingleton.elim _ _
    rw [e]
    exact (ConcreteCategory.congr_hom c.condition ⟨Sum.inl ⟨()⟩, trivial⟩).symm
  · exact fun c => ConcreteCategory.hom_ext _ _ fun _ => rfl
  · intro c m h₁ h₂
    apply ConcreteCategory.hom_ext
    intro y
    obtain ⟨z, rfl⟩ := Quotient.exists_rep y
    exact ConcreteCategory.congr_hom h₂ z

private def pointedCollapseBasepointMorphism (X : CGWH.{u}) (S : Set X.obj) (hS : IsClosed S) :
    basepointObject ⟶ pointedCollapseObject X S hS :=
  map (ContinuousMap.const _ (pointedCollapsePoint X S))

private def pointedCollapseMorphism (X : CGWH.{u}) (S : Set X.obj) (hS : IsClosed S) :
    pointedSourceObject X ⟶ pointedCollapseObject X S hS :=
  map ⟨pointedCollapseMap X S, continuous_quotient_mk'⟩

def pointedCollapseInclusionMorphism (X : CGWH.{u}) (S : Set X.obj) (hS : IsClosed S) :
    X ⟶ pointedCollapseObject X S hS :=
  map ⟨pointedCollapseInclusion X S, continuous_quotient_mk'.comp continuous_inr⟩

def pointedCollapseConstantMorphism (X : CGWH.{u}) (S : Set X.obj) (hS : IsClosed S) :
    X ⟶ pointedCollapseObject X S hS :=
  map (ContinuousMap.const _ (pointedCollapsePoint X S))

/-- The same topological pushout, with its objects in CGWH. -/
def pointedCollapsePushout (X : CGWH.{u}) (S : Set X.obj) (hS : IsClosed S) :
    ColimitCocone (span
      (map (X := pointedCollapseSubsetObject X S hS) (Y := basepointObject)
        (ContinuousMap.const _ ⟨()⟩))
      (map (X := pointedCollapseSubsetObject X S hS) (Y := pointedSourceObject X)
        ⟨Subtype.val, continuous_subtype_val⟩)) := by
  let x := pointedCollapseBasepointMorphism X S hS
  let b := pointedCollapseMorphism X S hS
  let a : pointedCollapseSubsetObject X S hS ⟶ basepointObject :=
    map (ContinuousMap.const _ ⟨()⟩)
  let i : pointedCollapseSubsetObject X S hS ⟶ pointedSourceObject X :=
    map ⟨Subtype.val, continuous_subtype_val⟩
  have hw : a ≫ x = i ≫ b := by
    apply ext_hom
    intro z
    exact Quotient.sound' (Or.inr ⟨trivial, z.property⟩)
  let lift (c : PushoutCocone a i) : pointedCollapseObject X S hS ⟶ c.pt :=
    map (collapseLift (X := X) (S := S) c.inr.hom.hom.hom (c.inl.hom ⟨()⟩) (fun z hz =>
      (ConcreteCategory.congr_hom (congrArg InducedCategory.Hom.hom c.condition) ⟨z, hz⟩).symm))
  refine ⟨PushoutCocone.mk x b hw, PushoutCocone.IsColimit.mk hw lift ?_ ?_ ?_⟩
  · intro c
    apply ext_hom
    intro j
    have e : j = (⟨()⟩ : ULift.{u} Unit) := Subsingleton.elim _ _
    rw [e]
    exact (ConcreteCategory.congr_hom (congrArg InducedCategory.Hom.hom c.condition)
      ⟨Sum.inl ⟨()⟩, trivial⟩).symm
  · exact fun c => ext_hom fun _ => rfl
  · intro c m h₁ h₂
    apply ext_hom
    intro y
    obtain ⟨z, rfl⟩ := Quotient.exists_rep y
    exact ConcreteCategory.congr_hom (congrArg InducedCategory.Hom.hom h₂) z

private theorem pointedCollapseBasepoint_isClosedEmbedding (X : CGWH.{u}) (S : Set X.obj)
    (hS : IsClosed S) : IsClosedEmbedding (pointedCollapseBasepointMorphism X S hS).hom := by
  let f := pointedCollapseBasepointMorphism X S hS
  apply IsClosedEmbedding.of_continuous_injective_isClosedMap
  · exact f.hom.hom.hom.continuous
  · exact fun _ _ _ => Subsingleton.elim _ _
  · intro U _
    by_cases hU : U.Nonempty
    · obtain ⟨x, hx⟩ := hU
      have eq : f.hom '' U = {pointedCollapsePoint X S} := by
        ext y
        exact ⟨fun ⟨z, _, hz⟩ => hz.symm, fun hy => ⟨x, hx, hy.symm⟩⟩
      rw [eq]
      exact weaklyHausdorff_closed_singleton (pointedCollapseObject X S hS).property _
    · rw [not_nonempty_iff_eq_empty.mp hU, image_empty]
      exact isClosed_empty

private def basepointFibreHomeomorph {Y Z : CGWH.{u}} (x : basepointObject ⟶ Y) (g : Z ⟶ Y) :
    FibrePoints x g ≃ₜ {z : Z.obj // g.hom z = x.hom ⟨()⟩} where
  toFun p := ⟨p.val.2, p.property.symm.trans (congrArg x.hom (Subsingleton.elim _ _))⟩
  invFun z := ⟨(⟨()⟩, z.val), z.property.symm⟩
  left_inv _ := Subtype.ext (Prod.ext (Subsingleton.elim _ _) rfl)
  right_inv _ := rfl
  continuous_toFun := (continuous_snd.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_const.prodMk continuous_subtype_val).subtype_mk _

/-- Lemma E.2.3.17(2)–(4). All three ordinary topological fibers also compute
the corresponding CGWH pullbacks. -/
noncomputable def pointedCollapseFibres (X : CGWH.{u}) (S : Set X.obj) (hS : IsClosed S) :
    (FibrePoints (pointedCollapseBasepointMorphism X S hS) (pointedCollapseMorphism X S hS)
      ≃ₜ pointedCollapseSubset X S) ×
    (FibrePoints (pointedCollapseBasepointMorphism X S hS) (pointedCollapseInclusionMorphism X S hS)
      ≃ₜ S) ×
    (FibrePoints (pointedCollapseBasepointMorphism X S hS) (pointedCollapseConstantMorphism X S hS)
      ≃ₜ X.obj) := by
  let a {Z : CGWH.{u}} := @basepointFibreHomeomorph _ Z (pointedCollapseBasepointMorphism X S hS)
  have h₁ : {z : PointedSource X | pointedCollapseMap X S z = pointedCollapsePoint X S} =
      pointedCollapseSubset X S := pointedCollapseMap_preimage X S
  have h₂ : {z : X.obj | pointedCollapseInclusion X S z = pointedCollapsePoint X S} =
      S := pointedCollapseInclusion_preimage X S
  have h₃ : {z : X.obj | (pointedCollapseConstantMorphism X S hS).hom z =
      (pointedCollapseBasepointMorphism X S hS).hom ⟨()⟩} = univ := by
    ext z
    exact ⟨fun _ => trivial, fun _ => rfl⟩
  exact ⟨(a _).trans (Homeomorph.setCongr h₁), (a _).trans (Homeomorph.setCongr h₂),
    (a _).trans ((Homeomorph.setCongr h₃).trans (Homeomorph.Set.univ X.obj))⟩

theorem pointedCollapseConstant_preimage (X : CGWH.{u}) (S : Set X.obj) (hS : IsClosed S) :
    (pointedCollapseConstantMorphism X S hS).hom ⁻¹' {pointedCollapsePoint X S} = univ :=
  preimage_const_of_mem (mem_singleton _)

noncomputable def pointedCollapseFibreLimits (X : CGWH.{u}) (S : Set X.obj) (hS : IsClosed S) :
    LimitCone (cospan (pointedCollapseBasepointMorphism X S hS) (pointedCollapseMorphism X S hS)) ×
    LimitCone (cospan (pointedCollapseBasepointMorphism X S hS) (pointedCollapseInclusionMorphism X S hS)) ×
    LimitCone (cospan (pointedCollapseBasepointMorphism X S hS) (pointedCollapseConstantMorphism X S hS)) :=
  ⟨topologicalPullbackOfClosedEmbedding _ _ (pointedCollapseBasepoint_isClosedEmbedding X S hS),
    topologicalPullbackOfClosedEmbedding _ _ (pointedCollapseBasepoint_isClosedEmbedding X S hS),
    topologicalPullbackOfClosedEmbedding _ _ (pointedCollapseBasepoint_isClosedEmbedding X S hS)⟩

section Regularity

local instance cgwhLimits : HasLimitsOfSize.{u, u} CGWH.{u} where
  has_limits_of_shape _ := ⟨fun P => ⟨⟨cgwhLimit P⟩⟩⟩

local instance cgwhColimits : HasColimitsOfSize.{u, u} CGWH.{u} where
  has_colimits_of_shape _ := ⟨fun P => ⟨⟨cgwhColimit P⟩⟩⟩

local instance cgwhSmallLimits : HasLimitsOfSize.{0, 0} CGWH.{u} where
  has_limits_of_shape J := HasLimitsOfShape.of_small.{u, u} CGWH.{u} J

local instance cgwhSmallColimits : HasColimitsOfSize.{0, 0} CGWH.{u} where
  has_colimits_of_shape J := HasColimitsOfShape.of_small.{u, u} CGWH.{u} J

def point (X : CGWH.{u}) (x : X.obj) : basepointObject ⟶ X :=
  map (ContinuousMap.const _ x)

theorem mono_iff_injective {X Y : CGWH.{u}} (f : X ⟶ Y) :
    Mono f ↔ Injective f.hom := by
  constructor
  · intro hf x y h
    letI := hf
    have e : point X x ≫ f = point X y ≫ f := ext_hom fun _ => h
    have p := (cancel_mono f).mp e
    exact ConcreteCategory.congr_hom (congrArg InducedCategory.Hom.hom p) ⟨()⟩
  · intro hf
    exact ⟨fun _ _ e => ext_hom fun x =>
      hf (ConcreteCategory.congr_hom (congrArg InducedCategory.Hom.hom e) x)⟩

theorem epi_iff_denseRange {X Y : CGWH.{u}} (f : X ⟶ Y) :
    Epi f ↔ DenseRange f.hom := by
  constructor
  · intro he
    letI := he
    let S := closure (range f.hom)
    let a := pointedCollapseInclusionMorphism Y S isClosed_closure
    let b := pointedCollapseConstantMorphism Y S isClosed_closure
    have hm (y : Y.obj) : a.hom y = b.hom y ↔ y ∈ S :=
      Set.ext_iff.mp (pointedCollapseInclusion_preimage Y S) y
    have hn : a = b := (cancel_epi f).mp (ext_hom fun x =>
      (hm (f.hom x)).mpr (subset_closure (mem_range_self x)))
    exact fun y => (hm y).mp (ConcreteCategory.congr_hom (congrArg InducedCategory.Hom.hom hn) y)
  · intro hd
    constructor
    intro Z a b h
    let E := {y : Y.obj | a.hom y = b.hom y}
    have he : IsClosed E :=
      cgwh_isClosed_equalizer Z.property a.hom.hom.hom b.hom.hom.hom
    have hr : range f.hom ⊆ E := by
      rintro _ ⟨x, rfl⟩
      exact ConcreteCategory.congr_hom (congrArg InducedCategory.Hom.hom h) x
    exact ext_hom fun y => closure_minimal hr he (hd y)

theorem isIso_iff_isHomeomorph {X Y : CGWH.{u}} (f : X ⟶ Y) :
    IsIso f ↔ IsHomeomorph f.hom := by
  constructor
  · intro hf
    letI := hf
    let e : X.obj ≃ₜ Y.obj :=
      { toFun := f.hom
        invFun := (inv f).hom
        left_inv := fun x =>
          ConcreteCategory.congr_hom (congrArg InducedCategory.Hom.hom (IsIso.hom_inv_id f)) x
        right_inv := fun y =>
          ConcreteCategory.congr_hom (congrArg InducedCategory.Hom.hom (IsIso.inv_hom_id f)) y
        continuous_toFun := f.hom.hom.hom.continuous
        continuous_invFun := (inv f).hom.hom.hom.continuous }
    exact e.isHomeomorph
  · intro hf
    let e := hf.homeomorph
    exact ⟨⟨map ⟨e.symm, e.symm.continuous⟩,
      ext_hom (fun x => e.symm_apply_apply x), ext_hom (fun y => e.apply_symm_apply y)⟩⟩

private def closedSubtypeObj (X : CGWH.{u}) (S : Set X.obj) (hS : IsClosed S) : CGWH.{u} :=
  letI := closed_compactlyGenerated hS
  of (weaklyHausdorff_subspace X.property S)

private def closedEqualizer {X Y : CGWH.{u}} (a b : X ⟶ Y) :
    Limits.LimitCone (parallelPair a b) := by
  let S : Set X.obj := {x | a.hom x = b.hom x}
  have hS : IsClosed S := cgwh_isClosed_equalizer Y.property a.hom.hom.hom b.hom.hom.hom
  let Z := closedSubtypeObj X S hS
  let i : Z ⟶ X := map ⟨Subtype.val, continuous_subtype_val⟩
  have w : i ≫ a = i ≫ b := ext_hom fun z => z.property
  refine ⟨Fork.ofι i w, Fork.IsLimit.mk (Fork.ofι i w) ?_ ?_ ?_⟩
  · intro c
    have hc (x : c.pt.obj) : c.ι.hom x ∈ S := by
      change a.hom (c.ι.hom x) = b.hom (c.ι.hom x)
      exact ConcreteCategory.congr_hom (congrArg InducedCategory.Hom.hom c.condition) x
    exact map (X := c.pt) (Y := Z) ⟨fun x => ⟨c.ι.hom x, hc x⟩,
      c.ι.hom.hom.hom.continuous.subtype_mk _⟩
  · intro c
    exact ext_hom fun _ => rfl
  · intro c m hm
    apply ext_hom
    intro x
    apply Subtype.ext
    have h := ConcreteCategory.congr_hom (congrArg InducedCategory.Hom.hom hm) x
    exact h

/-- A closed embedding is the equalizer of the collapse and constant maps. -/
theorem closedEmbedding_collapseEqualizer {X Y : CGWH.{u}} {f : X ⟶ Y}
    (hf : IsClosedEmbedding f.hom) :
    let a := pointedCollapseInclusionMorphism Y (range f.hom) hf.isClosed_range
    let b := pointedCollapseConstantMorphism Y (range f.hom) hf.isClosed_range
    ∃ w : f ≫ a = f ≫ b, Nonempty (IsLimit (Fork.ofι f w)) := by
  let a := pointedCollapseInclusionMorphism Y (range f.hom) hf.isClosed_range
  let b := pointedCollapseConstantMorphism Y (range f.hom) hf.isClosed_range
  have he (y : Y.obj) : a.hom y = b.hom y ↔ y ∈ range f.hom :=
    Set.ext_iff.mp (pointedCollapseInclusion_preimage Y (range f.hom)) y
  have w : f ≫ a = f ≫ b := ext_hom fun x => (he _).mpr (mem_range_self x)
  let e := hf.isEmbedding.toHomeomorph
  let lift (c : Fork a b) : c.pt ⟶ X :=
    map ⟨fun x => e.symm ⟨c.ι.hom x, (he _).mp
        (ConcreteCategory.congr_hom (congrArg InducedCategory.Hom.hom c.condition) x)⟩,
      e.symm.continuous.comp (c.ι.hom.hom.hom.continuous.subtype_mk _)⟩
  have hl (c : Fork a b) : lift c ≫ f = c.ι := ext_hom fun x =>
    congrArg Subtype.val (e.apply_symm_apply ⟨c.ι.hom x, (he _).mp
      (ConcreteCategory.congr_hom (congrArg InducedCategory.Hom.hom c.condition) x)⟩)
  refine ⟨w, ⟨Fork.IsLimit.mk (Fork.ofι f w) lift hl ?_⟩⟩
  intro c m hm
  exact ext_hom fun x => hf.injective (ConcreteCategory.congr_hom
    (congrArg InducedCategory.Hom.hom (hm.trans (hl c).symm)) x)


theorem regularMono_iff_closedEmbedding {X Y : CGWH.{u}} (f : X ⟶ Y) :
    IsRegularMono f ↔ IsClosedEmbedding f.hom := by
  constructor
  · rintro ⟨⟨h⟩⟩
    let l := closedEqualizer h.left h.right
    let e := h.isLimit.conePointUniqueUpToIso l.isLimit
    have ehome : IsHomeomorph e.hom.hom := (isIso_iff_isHomeomorph _).mp inferInstance
    have he : e.hom ≫ l.cone.π.app WalkingParallelPair.zero = f :=
      h.isLimit.conePointUniqueUpToIso_hom_comp l.isLimit _
    have hS : IsClosed {y : Y.obj | h.left.hom y = h.right.hom y} :=
      cgwh_isClosed_equalizer h.Z.property h.left.hom.hom.hom h.right.hom.hom.hom
    have hclosed : IsClosedEmbedding (l.cone.π.app WalkingParallelPair.zero).hom :=
      hS.isClosedEmbedding_subtypeVal
    rw [← he]
    exact hclosed.comp ehome.isClosedEmbedding
  · intro hf
    obtain ⟨w, ⟨h⟩⟩ := closedEmbedding_collapseEqualizer hf
    exact ⟨⟨⟨_, _, _, w, h⟩⟩⟩

theorem effectiveMono_iff_regularMono {C : Type u} [Category.{v} C] [HasPushouts C]
    {X Y : C} (f : X ⟶ Y) :
    Nonempty (IsLimit (Fork.ofι f (pushout.condition (f := f) (g := f)))) ↔ IsRegularMono f := by
  constructor
  · rintro ⟨h⟩
    exact ⟨⟨⟨_, _, _, pushout.condition, h⟩⟩⟩
  · rintro ⟨⟨h⟩⟩
    let q := pushout.desc h.left h.right h.w
    have hq (c : Fork (pushout.inl f f) (pushout.inr f f)) :
        c.ι ≫ h.left = c.ι ≫ h.right := by
      calc
        _ = (c.ι ≫ pushout.inl f f) ≫ q := by
          rw [Category.assoc]
          exact congrArg (c.ι ≫ ·) (pushout.inl_desc h.left h.right h.w).symm
        _ = (c.ι ≫ pushout.inr f f) ≫ q := by rw [c.condition]
        _ = _ := by
          rw [Category.assoc]
          exact congrArg (c.ι ≫ ·) (pushout.inr_desc h.left h.right h.w)
    let I (c : Fork (pushout.inl f f) (pushout.inr f f)) := Fork.ofι c.ι (hq c)
    exact ⟨Fork.IsLimit.mk _ (fun c => h.isLimit.lift (I c))
      (fun c => Fork.IsLimit.lift_ι (t := I c) h.isLimit)
      (fun c m hm => Fork.IsLimit.hom_ext h.isLimit
        (hm.trans (Fork.IsLimit.lift_ι (t := I c) h.isLimit).symm))⟩

theorem effectiveMono_iff_closedEmbedding {X Y : CGWH.{u}} (f : X ⟶ Y) :
    Nonempty (IsLimit (Fork.ofι f (pushout.condition (f := f) (g := f)))) ↔
      IsClosedEmbedding f.hom :=
  (effectiveMono_iff_regularMono f).trans (regularMono_iff_closedEmbedding f)

theorem regularEpi_iff_quotient {X Y : CGWH.{u}} (f : X ⟶ Y) :
    IsRegularEpi f ↔ IsQuotientMap f.hom :=
  ⟨fun h => (quotient_iff_coequalizer f).1.mp h.regularEpi,
    fun h => ⟨(quotient_iff_coequalizer f).1.mpr h⟩⟩

theorem quotient_of_isPullback {X Y Y' S : CGWH.{u}}
    {f : X ⟶ S} {g : Y ⟶ S} {f' : Y' ⟶ Y} {g' : Y' ⟶ X}
    (sq : IsPullback f' g' g f) (hg : IsQuotientMap g.hom) : IsQuotientMap g'.hom := by
  let L := fibreSubspaceLimit g f
  let e := sq.isLimit.conePointUniqueUpToIso L.isLimit
  have he : e.hom ≫ L.cone.π.app WalkingCospan.right = g' :=
    sq.isLimit.conePointUniqueUpToIso_hom_comp L.isLimit _
  have hx : IsQuotientMap e.hom.hom :=
    ((isIso_iff_isHomeomorph e.hom).mp inferInstance).homeomorph.isQuotientMap
  rw [← he]
  exact (quotient_baseChange g f hg).comp hx

instance : Regular CGWH.{u} where
  toHasFiniteLimits := inferInstance
  hasCoequalizer_of_isKernelPair _ := inferInstance
  regularEpiIsStableUnderBaseChange :=
    ⟨fun sq hg => (regularEpi_iff_quotient _).mpr
      (quotient_of_isPullback sq ((regularEpi_iff_quotient _).mp hg))⟩

theorem effectiveEpi_iff_quotient {X Y : CGWH.{u}} (f : X ⟶ Y) :
    EffectiveEpi f ↔ IsQuotientMap f.hom := by
  constructor
  · intro h
    letI := h
    exact (regularEpi_iff_quotient f).mp inferInstance
  · intro h
    letI := (regularEpi_iff_quotient f).mpr h
    infer_instance

theorem universallyEffectiveEpi_iff_quotient {X Y : CGWH.{u}} (f : X ⟶ Y) :
    (Nonempty (IsColimit (Cofork.ofπ f (pullback.condition (f := f) (g := f)))) ∧
      ∀ {A B : CGWH.{u}} {g : A ⟶ Y} {p : B ⟶ X} {q : B ⟶ A},
        IsPullback p q f g →
        Nonempty (IsColimit (Cofork.ofπ q (pullback.condition (f := q) (g := q))))) ↔
      IsQuotientMap f.hom := by
  constructor
  · rintro ⟨h, _⟩
    exact (regularEpi_iff_quotient f).mp ⟨⟨Cofork.IsColimit.regularEpi h.some⟩⟩
  · intro h
    have hf : IsRegularEpi f := (regularEpi_iff_quotient f).mpr h
    letI := hf
    refine ⟨⟨(regularEpiOfEffectiveEpi f).isColimit⟩, ?_⟩
    intro A B g p q sq
    letI : IsRegularEpi q := (regularEpi_iff_quotient q).mpr (quotient_of_isPullback sq h)
    exact ⟨(regularEpiOfEffectiveEpi q).isColimit⟩

theorem regularEpi_mono_factorisation {X Y : CGWH.{u}} (f : X ⟶ Y) :
    ∃ (Z : CGWH.{u}) (e : X ⟶ Z) (m : Z ⟶ Y),
      IsRegularEpi e ∧ Mono m ∧ e ≫ m = f := by
  let F := Regular.strongEpiMonoFactorisation f
  exact ⟨F.I, F.e, F.m, inferInstance, inferInstance, F.fac⟩

theorem regularEpi_mono_factorisation_baseChange {X Y Z A B : CGWH.{u}}
    {e : X ⟶ Z} {m : Z ⟶ Y} {g : A ⟶ Y} {p : B ⟶ X} {q : B ⟶ A}
    (he : IsRegularEpi e) (hm : Mono m) (sq : IsPullback p q (e ≫ m) g) :
    ∃ (W : CGWH.{u}) (e' : B ⟶ W) (m' : W ⟶ A) (r : W ⟶ Z),
      IsPullback m' r g m ∧ IsPullback e' p r e ∧
        IsRegularEpi e' ∧ Mono m' ∧ e' ≫ m' = q := by
  let t := IsPullback.of_hasPullback g m
  have sf := sq.flip
  let e' := t.lift q (p ≫ e) (by rw [sf.w, Category.assoc])
  have w := sf.of_right' t
  exact ⟨_, e', _, _, t, w, (regularEpi_iff_quotient _).mpr
    (quotient_of_isPullback w.flip ((regularEpi_iff_quotient _).mp he)),
    t.mono_fst_of_mono hm, t.lift_fst _ _ _⟩

theorem regularity_composition {X Y Z : CGWH.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (Mono f → Mono g → Mono (f ≫ g)) ∧ (Epi f → Epi g → Epi (f ≫ g)) ∧
    (IsRegularMono f → IsRegularMono g → IsRegularMono (f ≫ g)) ∧
    (IsRegularEpi f → IsRegularEpi g → IsRegularEpi (f ≫ g)) := by
  refine ⟨fun h k => ?_, fun h k => ?_, fun h k => ?_, fun h k => ?_⟩
  · letI := h
    letI := k
    infer_instance
  · letI := h
    letI := k
    infer_instance
  · exact (regularMono_iff_closedEmbedding _).mpr
      (((regularMono_iff_closedEmbedding _).mp k).comp ((regularMono_iff_closedEmbedding _).mp h))
  · exact (regularEpi_iff_quotient _).mpr
      (((regularEpi_iff_quotient _).mp k).comp ((regularEpi_iff_quotient _).mp h))

private def kelleyHomeomorph {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) :
    Kelley X ≃ₜ Kelley Y where
  toEquiv := e.toEquiv
  continuous_toFun := continuous_to_Kelley (X := Kelley X) (Y := Y)
    (e.continuous.comp (continuous_Kelley_forget (X := X)))
  continuous_invFun := continuous_to_Kelley (X := Kelley Y) (Y := X)
    (e.symm.continuous.comp (continuous_Kelley_forget (X := Y)))

private theorem kelley_closedEmbedding {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : IsClosedEmbedding f) :
    IsClosedEmbedding (show Kelley X → Kelley Y from f) := by
  let p : Kelley X → Kelley Y := f
  have hp : Continuous p := continuous_to_Kelley (hf.continuous.comp continuous_Kelley_forget)
  let S : Set (Kelley Y) := range p
  have hS : IsClosed S := hf.isClosed_range.preimage (continuous_Kelley_forget (X := Y))
  letI : CompactlyGeneratedSpace S := closed_compactlyGenerated hS
  let e := hf.isEmbedding.toHomeomorph
  let c : Kelley X → S := fun x => ⟨p x, mem_range_self x⟩
  let b : S → range f := fun x => ⟨Subtype.val x, x.property⟩
  have hb : Continuous b :=
    ((continuous_Kelley_forget (X := Y)).comp continuous_subtype_val).subtype_mk _
  let r : S → Kelley X := fun x => e.symm (b x)
  have hr : Continuous r := continuous_to_Kelley (e.symm.continuous.comp hb)
  have hrc : RightInverse c r := fun x => e.symm_apply_apply x
  exact ⟨IsEmbedding.subtypeVal.comp (hrc.isEmbedding hr (hp.subtype_mk _)), hS⟩

private def kelleyOptionPi {I : Type u} (X : Option I → Type u) [∀ i, TopologicalSpace (X i)] :
    Kelley ((i : Option I) → X i) ≃ₜ Kelley (X none × Kelley ((i : I) → X (some i))) where
  toEquiv := Equiv.piOptionEquivProd
  continuous_toFun := by
    have h₁ : Continuous (fun x : Kelley (∀ i : Option I, X i) => x none) :=
      (continuous_apply (A := X) none).comp
        (continuous_Kelley_forget (X := ∀ i : Option I, X i))
    have h₂ : Continuous (fun x : Kelley (∀ i : Option I, X i) =>
        (show Kelley (∀ i : I, X (some i)) from fun i => x (some i))) :=
      continuous_to_Kelley (X := Kelley (∀ i : Option I, X i)) (Y := ∀ i : I, X (some i))
        (continuous_pi fun i => (continuous_apply (A := X) (some i)).comp
          (continuous_Kelley_forget (X := ∀ i : Option I, X i)))
    exact continuous_to_Kelley (X := Kelley (∀ i : Option I, X i))
      (Y := X none × Kelley (∀ i : I, X (some i)))
      (Continuous.prodMk (X := X none) (Y := Kelley (∀ i : I, X (some i)))
        (Z := Kelley (∀ i : Option I, X i)) h₁ h₂)
  continuous_invFun := by
    apply continuous_to_Kelley (X := Kelley (X none × Kelley (∀ i : I, X (some i))))
      (Y := ∀ i : Option I, X i)
    apply continuous_pi
    intro i
    cases i with
    | none => exact continuous_fst.comp (continuous_Kelley_forget (X := X none × Kelley (∀ i : I, X (some i))))
    | some i =>
      exact (continuous_apply i).comp ((continuous_Kelley_forget (X := ∀ i : I, X (some i))).comp
        (continuous_snd.comp (continuous_Kelley_forget (X := X none × Kelley (∀ i : I, X (some i))))))

private theorem kelleyPi_quotient {I : Type u} [Finite I] (X Y : I → Type u)
    [∀ i, TopologicalSpace (X i)] [∀ i, TopologicalSpace (Y i)]
    [∀ i, CompactlyGeneratedSpace (X i)] [∀ i, CompactlyGeneratedSpace (Y i)]
    (f : ∀ i, X i → Y i) (hf : ∀ i, IsQuotientMap (f i)) :
    IsQuotientMap (show Kelley ((i : I) → X i) → Kelley ((i : I) → Y i) from fun x i => f i (x i)) := by
  revert X Y
  refine Finite.induction_empty_option (P := fun I =>
    ∀ (X Y : I → Type u) [∀ i, TopologicalSpace (X i)] [∀ i, TopologicalSpace (Y i)]
      [∀ i, CompactlyGeneratedSpace (X i)] [∀ i, CompactlyGeneratedSpace (Y i)]
      (f : ∀ i, X i → Y i), (∀ i, IsQuotientMap (f i)) →
      IsQuotientMap (show Kelley ((i : I) → X i) → Kelley ((i : I) → Y i) from fun x i => f i (x i))) ?_ ?_ ?_ I
  · intro I J e he X Y _ _ _ _ f hf
    let A : Kelley (∀ i : I, X (e i)) ≃ₜ Kelley (∀ i : J, X i) :=
      kelleyHomeomorph (Homeomorph.piCongrLeft (Y := X) e)
    let B : Kelley (∀ i : I, Y (e i)) ≃ₜ Kelley (∀ i : J, Y i) :=
      kelleyHomeomorph (Homeomorph.piCongrLeft (Y := Y) e)
    have h :
        (show Kelley (∀ i : J, X i) → Kelley (∀ i : J, Y i) from fun x i => f i (x i)) =
          B ∘ (fun x : Kelley (∀ i : I, X (e i)) => fun i => f (e i) (x i)) ∘ A.symm := by
      funext x i
      obtain ⟨j, rfl⟩ := e.surjective i
      change f (e j) (x (e j)) =
        Homeomorph.piCongrLeft (Y := Y) e (fun i => f (e i) (x (e i))) (e j)
      exact (Homeomorph.piCongrLeft_apply_apply (Y := Y) e (fun i => f (e i) (x (e i))) j).symm
    rw [h]
    exact B.isQuotientMap.comp ((he _ _ _ (fun i => hf _)).comp A.symm.isQuotientMap)
  · intro X Y _ _ _ _ f hf
    letI : Unique (Kelley (∀ i : PEmpty, X i)) :=
      ⟨⟨fun i => nomatch i⟩, fun x => funext fun i => nomatch i⟩
    letI : Unique (Kelley (∀ i : PEmpty, Y i)) :=
      ⟨⟨fun i => nomatch i⟩, fun x => funext fun i => nomatch i⟩
    let e : Kelley (∀ i : PEmpty, X i) ≃ₜ Kelley (∀ i : PEmpty, Y i) :=
      { toEquiv := Equiv.ofUnique _ _
        continuous_toFun := by
          convert (continuous_const : Continuous
            (fun _ : Kelley (∀ i : PEmpty, X i) => (default : Kelley (∀ i : PEmpty, Y i)))) using 1
          exact funext (fun _ => Subsingleton.elim _ _)
        continuous_invFun := by
          convert (continuous_const : Continuous
            (fun _ : Kelley (∀ i : PEmpty, Y i) => (default : Kelley (∀ i : PEmpty, X i)))) using 1
          exact funext (fun _ => Subsingleton.elim _ _) }
    have h : (show Kelley (∀ i : PEmpty, X i) → Kelley (∀ i : PEmpty, Y i)
        from fun x i => f i (x i)) = e := funext fun _ => Subsingleton.elim _ _
    rw [h]
    exact e.isQuotientMap
  · intro I _ hi X Y _ _ _ _ f hf
    let A := kelleyOptionPi X
    let B := kelleyOptionPi Y
    let p : Kelley (X none × Kelley (∀ i : I, X (some i))) →
        Kelley (Y none × Kelley (∀ i : I, Y (some i))) :=
      Prod.map (f none) (fun x i => f (some i) (x i))
    have hp : IsQuotientMap p := kelleyProduct_quotient (hf none) (hi _ _ _ fun i => hf (some i))
    have h : (show Kelley (∀ i : Option I, X i) → Kelley (∀ i : Option I, Y i)
        from fun x i => f i (x i)) = B.symm ∘ p ∘ A := by
      funext x i
      cases i <;> rfl
    rw [h]
    exact B.symm.isQuotientMap.comp (hp.comp A.isQuotientMap)

private theorem kelleyPi_denseRange {I : Type u} [Finite I] {X Y : I → Type u}
    [∀ i, TopologicalSpace (Y i)] [∀ i, CompactlyGeneratedSpace (Y i)]
    (f : ∀ i, X i → Y i) (hf : ∀ i, DenseRange (f i)) :
    DenseRange (show ((i : I) → X i) → Kelley ((i : I) → Y i) from fun x i => f i (x i)) := by
  classical
  letI : Fintype I := Fintype.ofFinite _
  let p : ((i : I) → X i) → Kelley ((i : I) → Y i) := fun x i => f i (x i)
  have h (s : Finset I) (y : Kelley ((i : I) → Y i))
      (hy : ∀ i ∉ s, y i ∈ range (f i)) : y ∈ closure (range p) := by
    induction s using Finset.induction_on generalizing y with
    | empty =>
      choose x hx using fun i => hy i (Finset.notMem_empty i)
      exact subset_closure ⟨x, funext hx⟩
    | @insert j s hjs ih =>
      let y' : (i : I) → Y i := y
      let k : Y j → Kelley ((i : I) → Y i) := fun z => Function.update y' j z
      have hk : Continuous k := continuous_to_Kelley (continuous_pi fun i => by
        by_cases e : i = j
        · subst i
          change Continuous (fun z : Y j => Function.update y' j z j)
          have hfun : (fun z : Y j => Function.update y' j z j) = id :=
            funext fun z => Function.update_self j z y'
          rw [hfun]
          exact continuous_id
        · change Continuous (fun z : Y j => Function.update y' j z i)
          simpa only [Function.update_of_ne e] using (continuous_const : Continuous (fun _ : Y j => y' i)))
      have hs : range (f j) ⊆ k ⁻¹' closure (range p) := by
        rintro _ ⟨x, rfl⟩
        apply ih (k (f j x))
        intro i hi
        by_cases h : i = j
        · subst i
          change Function.update y' j (f j x) j ∈ _
          rw [Function.update_self]
          exact mem_range_self x
        · change Function.update y' j (f j x) i ∈ _
          rw [Function.update_of_ne h]
          exact hy i (by simp [h, hi])
      have hcl : y j ∈ k ⁻¹' closure (range p) :=
        closure_minimal hs (isClosed_closure.preimage hk) (hf j (y j))
      have e : k (y j) = y := Function.update_eq_self j y'
      exact e ▸ hcl
  exact fun y => h Finset.univ y (by simp)

private def piObject {I : Type u} (X : I → CGWH.{u}) : CGWH.{u} :=
  of (X := Kelley ((i : I) → (X i).obj))
    (weaklyHausdorff_of_jointly_injective
      (fun i => ⟨fun x => x i, (continuous_apply i).comp continuous_Kelley_forget⟩)
      (fun i => (X i).property) (fun _ _ h => funext h))

/-- The Kelleyfication of the ordinary product, with its actual projections. -/
abbrev piFan {I : Type u} (X : I → CGWH.{u}) : Fan X :=
  Fan.mk (piObject X) fun i =>
    map ⟨fun x => x i, (continuous_apply i).comp continuous_Kelley_forget⟩

def piFan_isLimit {I : Type u} (X : I → CGWH.{u}) : IsLimit (piFan X) :=
  Fan.IsLimit.mk _ (fun s => map ⟨fun x i => (s.proj i).hom x, continuous_to_Kelley
      (continuous_pi fun i => (s.proj i).hom.hom.hom.continuous)⟩)
    (fun _ _ => ext_hom fun _ => rfl) (fun _ _ h => ext_hom fun x => funext fun i =>
      ConcreteCategory.congr_hom (congrArg InducedCategory.Hom.hom (h i)) x)

def piFamilyMap {I : Type u} {X Y : I → CGWH.{u}} (f : ∀ i, X i ⟶ Y i) :
    (piFan X).pt ⟶ (piFan Y).pt :=
  map ⟨fun x i => (f i).hom (x i), continuous_to_Kelley
    (continuous_pi fun i => (f i).hom.hom.hom.continuous.comp
      ((continuous_apply i).comp continuous_Kelley_forget))⟩

theorem piFamilyMap_projection {I : Type u} {X Y : I → CGWH.{u}} (f : ∀ i, X i ⟶ Y i)
    (i : I) : piFamilyMap f ≫ (piFan Y).proj i = (piFan X).proj i ≫ f i :=
  ext_hom fun _ => rfl

theorem piFamilyMap_mono {I : Type u} {X Y : I → CGWH.{u}} (f : ∀ i, X i ⟶ Y i)
    (hf : ∀ i, Mono (f i)) : Mono (piFamilyMap f) :=
  (mono_iff_injective _).mpr (fun _ _ h => funext fun i =>
    ((mono_iff_injective _).mp (hf i)) (congrFun h i))

theorem piFamilyMap_regularMono {I : Type u} {X Y : I → CGWH.{u}} (f : ∀ i, X i ⟶ Y i)
    (hf : ∀ i, IsRegularMono (f i)) : IsRegularMono (piFamilyMap f) :=
  (regularMono_iff_closedEmbedding _).mpr
    (kelley_closedEmbedding
      (X := ∀ i, ((X i).obj : Type u)) (Y := ∀ i, ((Y i).obj : Type u))
      (IsClosedEmbedding.piMap fun i => (regularMono_iff_closedEmbedding (f i)).mp (hf i)))

theorem piFamilyMap_epi {I : Type u} [Finite I] {X Y : I → CGWH.{u}} (f : ∀ i, X i ⟶ Y i)
    (hf : ∀ i, Epi (f i)) : Epi (piFamilyMap f) :=
  (epi_iff_denseRange _).mpr (kelleyPi_denseRange (fun i => (f i).hom)
    (fun i => (epi_iff_denseRange _).mp (hf i)))

theorem piFamilyMap_regularEpi {I : Type u} [Finite I] {X Y : I → CGWH.{u}} (f : ∀ i, X i ⟶ Y i)
    (hf : ∀ i, IsRegularEpi (f i)) : IsRegularEpi (piFamilyMap f) :=
  (regularEpi_iff_quotient _).mpr (kelleyPi_quotient _ _ (fun i => (f i).hom)
    (fun i => (regularEpi_iff_quotient _).mp (hf i)))

def coproductFamilyMap {I : Type u} {X Y : I → CGWH.{u}} (f : ∀ i, X i ⟶ Y i) :
    (coproductCofan X).pt ⟶ (coproductCofan Y).pt :=
  map ⟨fun x => ⟨x.1, (f x.1).hom x.2⟩,
    continuous_sigma fun i => continuous_sigmaMk.comp (f i).hom.hom.hom.continuous⟩

theorem coproductFamilyMap_inclusion {I : Type u} {X Y : I → CGWH.{u}} (f : ∀ i, X i ⟶ Y i)
    (i : I) : (coproductCofan X).inj i ≫ coproductFamilyMap f = f i ≫ (coproductCofan Y).inj i :=
  ext_hom fun _ => rfl

private theorem coproductFamilyMap_injective {I : Type u} {X Y : I → CGWH.{u}} (f : ∀ i, X i ⟶ Y i)
    (hf : ∀ i, Injective (f i).hom) : Injective (coproductFamilyMap f).hom := by
  rintro ⟨i, x⟩ ⟨j, y⟩ h
  have he : i = j := congrArg (fun p : Σ i, (Y i).obj => p.1) h
  subst j
  change (⟨i, (f i).hom x⟩ : Σ i, (Y i).obj) = ⟨i, (f i).hom y⟩ at h
  exact congrArg (@Sigma.mk I (fun i => ((X i).obj : Type u)) i)
    (hf i ((sigma_mk_injective (β := fun i => ((Y i).obj : Type u))) h))

theorem coproductFamilyMap_mono {I : Type u} {X Y : I → CGWH.{u}} (f : ∀ i, X i ⟶ Y i)
    (hf : ∀ i, Mono (f i)) : Mono (coproductFamilyMap f) :=
  (mono_iff_injective _).mpr (coproductFamilyMap_injective f (fun i => (mono_iff_injective _).mp (hf i)))

theorem coproductFamilyMap_regularMono {I : Type u} {X Y : I → CGWH.{u}} (f : ∀ i, X i ⟶ Y i)
    (hf : ∀ i, IsRegularMono (f i)) : IsRegularMono (coproductFamilyMap f) := by
  have he (i : I) := (regularMono_iff_closedEmbedding (f i)).mp (hf i)
  let p := coproductFamilyMap f
  apply (regularMono_iff_closedEmbedding p).mpr
  refine IsClosedEmbedding.of_continuous_injective_isClosedMap p.hom.hom.hom.continuous
    (coproductFamilyMap_injective f (fun i => (he i).injective)) ?_
  intro A hA
  apply isClosed_sigma_iff.mpr
  intro i
  have h : (@Sigma.mk I (fun i => ((Y i).obj : Type u)) i) ⁻¹' (p.hom '' A) =
      (f i).hom '' ((@Sigma.mk I (fun i => ((X i).obj : Type u)) i) ⁻¹' A) := by
    ext y
    constructor
    · rintro ⟨⟨j, x⟩, hx, hx'⟩
      change (⟨j, (f j).hom x⟩ : Σ i, (Y i).obj) = ⟨i, y⟩ at hx'
      have e : j = i := congrArg Sigma.fst hx'
      subst j
      exact ⟨x, hx, (sigma_mk_injective (β := fun i => ((Y i).obj : Type u))) hx'⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨i, x⟩, hx, rfl⟩
  rw [h]
  exact (he i).isClosedMap _ (hA.preimage continuous_sigmaMk)

theorem coproductFamilyMap_epi {I : Type u} {X Y : I → CGWH.{u}} (f : ∀ i, X i ⟶ Y i)
    (hf : ∀ i, Epi (f i)) : Epi (coproductFamilyMap f) := by
  constructor
  intro Z g h he
  apply (coproductCofan_isColimit Y).hom_ext
  rintro ⟨i⟩
  change (coproductCofan Y).inj i ≫ g = (coproductCofan Y).inj i ≫ h
  letI := hf i
  apply (cancel_epi (f i)).mp
  have e := congrArg ((coproductCofan X).inj i ≫ ·) he
  simpa only [← Category.assoc, coproductFamilyMap_inclusion] using e

theorem coproductFamilyMap_regularEpi {I : Type u} {X Y : I → CGWH.{u}} (f : ∀ i, X i ⟶ Y i)
    (hf : ∀ i, IsRegularEpi (f i)) : IsRegularEpi (coproductFamilyMap f) := by
  have he (i : I) := (regularEpi_iff_quotient (f i)).mp (hf i)
  let p := coproductFamilyMap f
  apply (regularEpi_iff_quotient p).mpr
  refine ⟨IsCoinducing.of_isOpen_preimage_iff_isOpen fun A => ?_, ?_⟩
  · rw [isOpen_sigma_iff, isOpen_sigma_iff]
    apply forall_congr'
    intro i
    let k : (Y i).obj → Σ j, (Y j).obj := @Sigma.mk I (fun i => ((Y i).obj : Type u)) i
    change IsOpen ((f i).hom ⁻¹' (k ⁻¹' A)) ↔ IsOpen (k ⁻¹' A)
    exact (he i).isOpen_preimage
  · rintro ⟨i, y⟩
    obtain ⟨x, rfl⟩ := (he i).surjective y
    exact ⟨⟨i, x⟩, rfl⟩

end Regularity

end CGWH

end Masullo
