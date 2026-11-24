import Mathlib.SetTheory.ZFC.VonNeumann
import CompactlyGenerated
import Mathlib.Analysis.Complex.Cardinality
import Mathlib.Analysis.Complex.Tietze
import Mathlib.CategoryTheory.IsoCat
import Mathlib.SetTheory.Cardinal.Arithmetic

open Cardinal CategoryTheory Filter Function Set Topology TopologicalSpace
open scoped Cardinal

namespace Masullo

universe u

/-- E.3.1.2. All types of cardinality at most `κ` have representatives
among the subsets of one fixed type of cardinality `κ`. -/
theorem bounded_type_representatives (κ : Cardinal.{u}) :
    (∀ s : Set κ.out, #s ≤ κ) ∧
    ∀ X : Type u, #X ≤ κ → ∃ s : Set κ.out, Nonempty (X ≃ s) := by
  refine ⟨fun s => (mk_set_le s).trans_eq (mk_out κ), ?_⟩
  intro X hX
  obtain ⟨e⟩ := (Cardinal.le_def X κ.out).mp (hX.trans_eq (mk_out κ).symm)
  exact ⟨range e, ⟨Equiv.ofInjective e e.injective⟩⟩

/-- Compact Hausdorff subspaces in the definition of the size of a space. -/
def CompactHausdorffSubspace (X : Type u) [TopologicalSpace X] :=
  {s : Set X // IsCompact s ∧ T2Space s}

/-- The size of a space as defined in E.3.1.1. -/
noncomputable def topologicalSize (X : Type u) [TopologicalSpace X] : Cardinal.{u} :=
  max ℵ₀ (max #(CompactHausdorffSubspace X) (⨆ K : CompactHausdorffSubspace X, #C(K.1, ℂ)))

private theorem contMap_card_le_functions {X : Type u} [TopologicalSpace X] :
    #C(X, ℂ) ≤ Cardinal.lift.{u} (#ℂ) ^ #X := by
  calc
    #C(X, ℂ) ≤ #(X → ℂ) := mk_le_of_injective DFunLike.coe_injective
    _ = _ := by simp only [Cardinal.mk_arrow, Cardinal.lift_uzero]

private theorem complexCard_ne_zero : (Cardinal.lift.{u} (#ℂ)) ≠ 0 :=
  fun h => Cardinal.mk_ne_zero ℂ (Cardinal.lift_eq_zero.mp h)

private theorem topologicalSize_le_iff {X : Type u} [TopologicalSpace X] {κ : Cardinal.{u}} :
    topologicalSize X ≤ κ ↔ ℵ₀ ≤ κ ∧ #(CompactHausdorffSubspace X) ≤ κ ∧
      ∀ K : CompactHausdorffSubspace X, #C(K.1, ℂ) ≤ κ := by
  have hB : BddAbove (range fun K : CompactHausdorffSubspace X => #C(K.1, ℂ)) := by
    refine ⟨Cardinal.lift.{u} (#ℂ) ^ #X, forall_mem_range.mpr fun K => ?_⟩
    exact contMap_card_le_functions.trans (power_le_power_left complexCard_ne_zero (mk_set_le K.1))
  simp only [topologicalSize, max_le_iff, ciSup_le_iff' hB]

private def whole_space_subspace {X : Type u} [TopologicalSpace X] [CompactSpace X]
    [T2Space X] : CompactHausdorffSubspace X :=
  ⟨univ, isCompact_univ, inferInstance⟩

private theorem contMap_card_le_size {X : Type u} [TopologicalSpace X] [CompactSpace X]
    [T2Space X] : #C(X, ℂ) ≤ topologicalSize X := by
  have h := (topologicalSize_le_iff.mp (le_rfl : topologicalSize X ≤ topologicalSize X)).2.2
    (whole_space_subspace (X := X))
  let e : (univ : Set X) ≃ₜ X := Homeomorph.Set.univ X
  exact (mk_le_of_injective (f := fun f : C(X, ℂ) => f.comp (⟨e, e.continuous⟩ : C((univ : Set X), X)))
    (fun f g hfg => by
      ext x
      obtain ⟨y, rfl⟩ := e.surjective x
      exact congrArg (fun h : C((univ : Set X), ℂ) => h y) hfg)).trans h

private def singletonCompactSubspace {X : Type u} [TopologicalSpace X] (x : X) :
    CompactHausdorffSubspace X :=
  ⟨{x}, isCompact_singleton, by
    letI : Subsingleton ({x} : Set X) := ⟨fun y z => Subtype.ext
      ((mem_singleton_iff.mp y.2).trans (mem_singleton_iff.mp z.2).symm)⟩
    infer_instance⟩

theorem carrier_card_le_size (X : Type u) [TopologicalSpace X] : #X ≤ topologicalSize X := by
  have hf : Injective (singletonCompactSubspace (X := X)) := by
    intro x y h
    exact singleton_injective (congrArg Subtype.val h)
  exact (mk_le_of_injective hf).trans ((le_max_left _ _).trans (le_max_right _ _))

theorem topologicalSize_le_of_embedding {X Y : Type u}
    [TopologicalSpace X] [TopologicalSpace Y] {e : X → Y} (he : IsEmbedding e) :
    topologicalSize X ≤ topologicalSize Y := by
  obtain ⟨hω, hK, hF⟩ := (topologicalSize_le_iff (X := Y)).mp le_rfl
  let E' (K : CompactHausdorffSubspace X) := e '' K.1
  let Em (K : CompactHausdorffSubspace X) : K.1 ≃ₜ E' K := by
    have hr : range (fun x : K.1 => e x.val) = E' K := by
      ext y
      simp [E']
    exact (he.comp IsEmbedding.subtypeVal).toHomeomorph.trans (Homeomorph.setCongr hr)
  let E (K : CompactHausdorffSubspace X) : CompactHausdorffSubspace Y :=
    ⟨E' K, K.2.1.image he.continuous, by
      letI : T2Space K.1 := K.2.2
      exact (Em K).t2Space⟩
  have hE : Injective E := fun _ _ h => Subtype.ext
    (he.injective.image_injective (congrArg Subtype.val h))
  refine topologicalSize_le_iff.mpr ⟨hω, (mk_le_of_injective hE).trans hK, ?_⟩
  intro K
  let eK : K.1 ≃ₜ (E K).1 := Em K
  exact (mk_le_of_injective (f := fun g : C(K.1, ℂ) =>
    g.comp (⟨eK.symm, eK.symm.continuous⟩ : C((E K).1, K.1))) (fun f g h => by
      ext x
      obtain ⟨y, rfl⟩ := eK.symm.surjective x
      exact congrArg (fun w : C((E K).1, ℂ) => w y) h)).trans (hF (E K))

private theorem topologicalSize_homeomorph {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) : topologicalSize X = topologicalSize Y :=
  le_antisymm (topologicalSize_le_of_embedding e.isEmbedding)
    (topologicalSize_le_of_embedding e.symm.isEmbedding)

/-- E.3.1.5. The unit cube with `κ` coordinates contains a closed copy
of every compact Hausdorff space of size at most `κ`. -/
theorem compactHausdorff_closedEmbedding_cube {X : Type u} [TopologicalSpace X]
    [CompactSpace X] [T2Space X] {κ : Cardinal.{u}} (hX : topologicalSize X ≤ κ) :
    ∃ f : X → (κ.out → (Icc (0 : ℝ) 1)), IsClosedEmbedding f := by
  classical
  let J := C(X, Icc (0 : ℝ) 1)
  let castMap : C(Icc (0 : ℝ) 1, ℂ) :=
    ⟨fun x => (x.val : ℂ), Complex.continuous_ofReal.comp continuous_subtype_val⟩
  have hJ : #J ≤ #C(X, ℂ) := by
    apply mk_le_of_injective (f := fun g : J => castMap.comp g)
    intro f g h
    ext x
    apply Complex.ofReal_injective
    exact congrArg (fun k : C(X, ℂ) => k x) h
  obtain ⟨i⟩ := (Cardinal.le_def J κ.out).mp
    ((hJ.trans ((contMap_card_le_size (X := X)).trans hX)).trans_eq (mk_out κ).symm)
  let zeroI : Icc (0 : ℝ) 1 := ⟨0, by norm_num⟩
  let E : X → κ.out → Icc (0 : ℝ) 1 := fun x j =>
    if h : j ∈ range i then Classical.choose h x else zeroI
  have hE (x : X) (g : J) : E x (i g) = g x := by
    have h : i g ∈ range i := mem_range_self _
    exact (dite_eq_left h).trans (congrArg (fun k : J => k x) (i.injective (Classical.choose_spec h)))
  have hc : Continuous E := by
    apply continuous_pi
    intro j
    by_cases h : j ∈ range i
    · simpa only [E, dite_eq_left h] using (Classical.choose h : J).continuous
    · simpa only [E, dite_eq_right h] using (continuous_const : Continuous (fun _ : X => zeroI))
  have hinj : Injective E := by
    intro x y heq
    by_contra hn
    obtain ⟨f, hx, hy, h⟩ := exists_continuous_zero_one_of_isClosed
      (isClosed_singleton (x := x)) (isClosed_singleton (x := y)) (by simpa using hn)
    let g : J := ⟨fun z => ⟨f z, h z⟩, f.continuous.subtype_mk h⟩
    have hh := congrFun heq (i g)
    rw [hE, hE] at hh
    exact zero_ne_one ((hx (mem_singleton x)).symm.trans
      ((congrArg Subtype.val hh).trans (hy (mem_singleton y))))
  exact ⟨E, hc.isClosedEmbedding hinj⟩

/-- E.3.1.6. A small family of compact Hausdorff representatives of
size at most `κ`, obtained as closed subspaces of a single cube. -/
theorem compactHausdorff_bounded_representatives (κ : Cardinal.{u}) :
    ∃ (I : Type u) (X : I → Type u) (t : ∀ i, TopologicalSpace (X i)),
      (∀ i, @CompactSpace (X i) (t i) ∧ @T2Space (X i) (t i) ∧
        @topologicalSize (X i) (t i) ≤ κ) ∧
      ∀ (Y : Type u) [TopologicalSpace Y] [CompactSpace Y] [T2Space Y],
        topologicalSize Y ≤ κ → ∃ i, Nonempty (@Homeomorph (X i) Y (t i) inferInstance) := by
  let Cube := κ.out → Icc (0 : ℝ) 1
  let I := {S : Set Cube // IsClosed S ∧ topologicalSize S ≤ κ}
  refine ⟨I, fun i => i.1, fun _ => inferInstance, ?_, ?_⟩
  · intro i
    exact ⟨isCompact_iff_compactSpace.mp i.2.1.isCompact, inferInstance, i.2.2⟩
  · intro Y _ _ _ hY
    obtain ⟨f, hf⟩ := compactHausdorff_closedEmbedding_cube hY
    let e := hf.isEmbedding.toHomeomorph
    exact ⟨⟨range f, hf.isClosed_range, (topologicalSize_homeomorph e.symm).trans_le hY⟩, ⟨e.symm⟩⟩

/-- A topology on a subset of a fixed cardinal representative is
specified by data in the same universe as that representative. -/
structure BoundedTopology (κ : Cardinal.{u}) where
  carrier : Set κ.out
  topology : TopologicalSpace carrier

/-- E.3.1.7. Small representatives for compactly generated weakly
Hausdorff spaces. The singleton subspaces already bound the cardinality
of the underlying set. -/
theorem cgwh_bounded_representatives (κ : Cardinal.{u}) :
    ∃ (I : Type u) (X : I → Type u) (t : ∀ i, TopologicalSpace (X i)),
      (∀ i, @CompactlyGeneratedSpace (X i) (t i) ∧ @WeaklyHausdorff (X i) (t i) ∧
        @topologicalSize (X i) (t i) ≤ κ) ∧
      ∀ (Y : Type u) [TopologicalSpace Y] [CompactlyGeneratedSpace Y], WeaklyHausdorff Y →
        topologicalSize Y ≤ κ → ∃ i, Nonempty (@Homeomorph (X i) Y (t i) inferInstance) := by
  let I := {c : BoundedTopology κ //
    @CompactlyGeneratedSpace c.carrier c.topology ∧ @WeaklyHausdorff c.carrier c.topology ∧
    @topologicalSize c.carrier c.topology ≤ κ}
  refine ⟨I, fun i => i.1.carrier, fun i => i.1.topology, fun i => i.2, ?_⟩
  intro Y _ _ hY hκ
  obtain ⟨S, ⟨e⟩⟩ := (bounded_type_representatives κ).2 Y ((carrier_card_le_size Y).trans hκ)
  let t : TopologicalSpace S := TopologicalSpace.induced e.symm inferInstance
  letI : TopologicalSpace S := t
  let h : S ≃ₜ Y := e.symm.toHomeomorphOfIsInducing ⟨rfl⟩
  have hcg : CompactlyGeneratedSpace S :=
    compactlyGeneratedSpace_of_coinduced h.symm.continuous h.symm.isQuotientMap.eq_coinduced
  have hwh : WeaklyHausdorff S := by
    intro K f
    let g : C(K, Y) := ⟨h ∘ f, h.continuous.comp f.continuous⟩
    have he : range f = h ⁻¹' range g := by
      ext x
      simp [g, Function.comp_def, h.injective.eq_iff]
    rw [he]
    exact (hY K g).preimage h.continuous
  exact ⟨⟨⟨S, t⟩, hcg, hwh, (topologicalSize_homeomorph h).trans_le hκ⟩, ⟨h⟩⟩


private theorem compactSubspaces_card_le_power {X : Type u} [TopologicalSpace X] :
    #(CompactHausdorffSubspace X) ≤ 2 ^ #X :=
  (mk_le_of_injective Subtype.val_injective).trans_eq Cardinal.mk_set

/-- E.3.3.1. The size bound for a compact Hausdorff space. Tietze
extension bounds the number of functions on each compact subspace. -/
theorem topologicalSize_compactHausdorff {X : Type u} [TopologicalSpace X] [CompactSpace X]
    [T2Space X] : topologicalSize X ≤ max ℵ₀ (2 ^ #C(X, ℂ)) := by
  let Z (K : CompactHausdorffSubspace X) : Set C(X, ℂ) :=
    {g | ∀ x ∈ K.1, g x = 0}
  have hZ (K : CompactHausdorffSubspace X) (x : X) :
      x ∈ K.1 ↔ ∀ f ∈ Z K, f x = 0 := by
    constructor
    · exact fun hx f hf => hf x hx
    · intro hx
      by_contra hxK
      obtain ⟨g, hg, hx1, _⟩ := exists_continuous_zero_one_of_isClosed K.2.1.isClosed
        isClosed_singleton (Set.disjoint_left.mpr fun y hy hyx =>
          hxK (by simpa [show y = x from mem_singleton_iff.mp hyx] using hy))
      let G : C(X, ℂ) := ⟨fun y => (g y : ℂ), Complex.continuous_ofReal.comp g.continuous⟩
      have hG : G ∈ Z K := by
        intro y hy
        change (g y : ℂ) = 0
        exact_mod_cast hg hy
      have h := hx G hG
      change (g x : ℂ) = 0 at h
      have hxg : g x = 1 := hx1 (mem_singleton x)
      simp [hxg] at h
  have hZinj : Injective Z := by
    intro S T he
    apply Subtype.ext
    ext x
    rw [hZ, hZ, he]
  apply topologicalSize_le_iff.mpr
  refine ⟨le_max_left _ _, (mk_le_of_injective hZinj).trans (Cardinal.mk_set ▸ le_max_right _ _), ?_⟩
  · intro K
    have hK : IsClosed K.1 := K.2.1.isClosed
    exact (mk_le_of_surjective (f := fun g : C(X, ℂ) => g.restrict K.1)
      (fun g => g.exists_restrict_eq hK)).trans
      ((le_of_lt (Cardinal.cantor _)).trans (le_max_right _ _))

private theorem pi_card_le_power {I : Type u} {X : I → Type u} {κ : Cardinal.{u}}
    (hX : ∀ i : I, #(X i) ≤ κ) : #(∀ i, X i) ≤ κ ^ #I := by
  classical
  let e (i : I) : X i ↪ κ.out :=
    ((Cardinal.le_def (X i) κ.out).mp ((hX i).trans_eq (mk_out κ).symm)).some
  calc
    #(∀ i, X i) ≤ #(I → κ.out) :=
      mk_le_of_injective (f := fun a i => e i (a i)) (fun a b h => funext fun i =>
        (e i).injective (congrFun h i))
    _ = κ ^ #I := by rw [Cardinal.mk_arrow, Cardinal.lift_id, Cardinal.lift_id, mk_out]

private theorem compactSubspace_closed {X : Type u} [TopologicalSpace X]
    (hX : WeaklyHausdorff X) (K : CompactHausdorffSubspace X) : IsClosed K.1 := by
  letI : CompactSpace K.1 := isCompact_iff_compactSpace.mp K.2.1
  letI : T2Space K.1 := K.2.2
  have h := hX (CompHaus.of K.1) ⟨Subtype.val, continuous_subtype_val⟩
  change IsClosed (range (Subtype.val : K.1 → X)) at h
  rwa [Subtype.range_coe] at h

/-- E.3.3.2. A compact Hausdorff cover bounds both the number of
compact subspaces and the functions on each such subspace. -/
theorem topologicalSize_of_compact_cover {X I : Type u} [TopologicalSpace X]
    (hX : WeaklyHausdorff X) (K : I → CompactHausdorffSubspace X)
    (hcover : ∀ x : X, ∃ i : I, x ∈ (K i).1) :
    topologicalSize X ≤ max ℵ₀ ((⨆ i : I, topologicalSize (K i).1) ^ #I) := by
  let κ := ⨆ i : I, topologicalSize (K i).1
  have hSup (i : I) : topologicalSize (K i).1 ≤ κ :=
    le_ciSup (f := fun i : I => topologicalSize (K i).1)
      ⟨topologicalSize X, forall_mem_range.mpr fun i =>
        topologicalSize_le_of_embedding (e := ((↑) : (K i).1 → X)) IsEmbedding.subtypeVal⟩ i
  let inter (S : CompactHausdorffSubspace X) (i : I) : CompactHausdorffSubspace (K i).1 := by
    letI : CompactSpace (K i).1 := isCompact_iff_compactSpace.mp (K i).2.1
    letI : T2Space (K i).1 := (K i).2.2
    exact ⟨Subtype.val ⁻¹' S.1, ((compactSubspace_closed hX S).preimage continuous_subtype_val).isCompact,
      inferInstance⟩
  have hκ (i : I) := topologicalSize_le_iff.mp (hSup i)
  apply topologicalSize_le_iff.mpr
  refine ⟨le_max_left _ _, ?_, ?_⟩
  · have hinj : Injective inter := by
      intro S T he
      apply Subtype.ext
      ext x
      obtain ⟨i, hi⟩ := hcover x
      exact Set.ext_iff.mp (congrArg (fun s : CompactHausdorffSubspace (K i).1 => s.1)
        (congrFun he i)) ⟨x, hi⟩
    exact ((mk_le_of_injective hinj).trans (pi_card_le_power (fun i => (hκ i).2.1))).trans
      (le_max_right _ _)
  · intro S
    let r (i : I) : C((inter S i).1, S.1) :=
      ⟨fun x => ⟨x.val.val, x.property⟩,
       (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩
    let B : C(S.1, ℂ) → ∀ i : I, C((inter S i).1, ℂ) := fun g i => g.comp (r i)
    have hB : Injective B := by
      intro f g h
      ext x
      obtain ⟨i, hi⟩ := hcover x.val
      exact congrArg (fun t : C((inter S i).1, ℂ) => t ⟨⟨x.val, hi⟩, x.property⟩) (congrFun h i)
    exact ((mk_le_of_injective hB).trans (pi_card_le_power (fun i => (hκ i).2.2 (inter S i)))).trans
      (le_max_right _ _)


/-- The cardinal function in Definition E.3.1.1. -/
noncomputable def smallSpaceBound (κ : Cardinal.{u}) : Cardinal.{u} :=
  max (κ ^ ℵ₀) (max ((2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ κ)) (κ ^ κ))

theorem topologicalSize_le_two_power_of_carrier {X : Type u} [TopologicalSpace X]
    {κ : Cardinal.{u}} (hω : ℵ₀ ≤ κ) (hX : #X ≤ κ) : topologicalSize X ≤ 2 ^ κ := by
  have hn : (2 : Cardinal.{u}) ≠ 0 := by simp
  apply topologicalSize_le_iff.mpr
  refine ⟨hω.trans (le_of_lt (Cardinal.cantor _)), compactSubspaces_card_le_power.trans
    (power_le_power_left hn hX), ?_⟩
  intro K
  have hC : Cardinal.lift.{u} (#ℂ) ≤ 2 ^ κ := by
    rw [Cardinal.mk_complex, Cardinal.continuum, lift_power, lift_ofNat, lift_aleph0]
    exact power_le_power_left hn hω
  calc
    #C(K.1, ℂ) ≤ Cardinal.lift.{u} (#ℂ) ^ #K.1 := contMap_card_le_functions
    _ ≤ (2 ^ κ) ^ κ :=
      (power_le_power_right hC).trans (power_le_power_left (power_ne_zero _ hn) ((mk_set_le _).trans hX))
    _ = 2 ^ κ := by rw [← power_mul, mul_eq_max hω hω, max_self]

/-- E.3.3.3. The bound holds for the subtype of the Kelley product
that computes the pullback in CGWH. -/
theorem topologicalSize_cgwh_pullback {X Y Z : CGWH.{u}} (f : X ⟶ Y) (g : Z ⟶ Y) :
    topologicalSize (CGWH.FibreSubspace f g) ≤
      max (smallSpaceBound (topologicalSize X.obj)) (smallSpaceBound (topologicalSize Z.obj)) := by
  let κ := max (topologicalSize X.obj) (topologicalSize Z.obj)
  have hω : ℵ₀ ≤ κ := (le_max_left _ _).trans (le_max_left _ _)
  have hcard : #(CGWH.FibreSubspace f g) ≤ κ := by
    change #({p : Kelley (X.obj × Z.obj) | f.hom p.1 = g.hom p.2} : Set _) ≤ κ
    refine (mk_set_le _).trans ?_
    change #(X.obj × Z.obj) ≤ κ
    rw [Cardinal.mk_prod, Cardinal.lift_id, Cardinal.lift_id]
    calc
      _ ≤ κ * κ := mul_le_mul' ((carrier_card_le_size X.obj).trans (le_max_left _ _))
        ((carrier_card_le_size Z.obj).trans (le_max_right _ _))
      _ = κ := by rw [mul_eq_max hω hω, max_self]
  refine (topologicalSize_le_two_power_of_carrier hω hcard).trans ?_
  unfold smallSpaceBound
  rcases le_total (topologicalSize X.obj) (topologicalSize Z.obj) with h | h
  · have hκ : κ = topologicalSize Z.obj := max_eq_right h
    rw [hκ, ← power_self_eq (hκ ▸ hω)]
    exact (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  · have hκ : κ = topologicalSize X.obj := max_eq_left h
    rw [hκ, ← power_self_eq (hκ ▸ hω)]
    exact (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_left _ _))


/-- A category represented by subsets of a single fixed carrier. The
operations and laws are data in the same universe as that carrier. -/
structure BoundedCategoryCode (κ : Cardinal.{u}) where
  objects : Set κ.out
  arrows : objects → objects → Set κ.out
  id (x : objects) : arrows x x
  comp {x y z : objects} : arrows x y → arrows y z → arrows x z
  id_comp {x y : objects} (f : arrows x y) : comp (id x) f = f
  comp_id {x y : objects} (f : arrows x y) : comp f (id y) = f
  assoc {w x y z : objects} (f : arrows w x) (g : arrows x y) (h : arrows y z) :
    comp (comp f g) h = comp f (comp g h)

instance boundedCategoryCodeSmallCategory (κ : Cardinal.{u}) (C : BoundedCategoryCode κ) : SmallCategory C.objects where
  Hom x y := C.arrows x y
  id := C.id
  comp := C.comp
  id_comp := C.id_comp
  comp_id := C.comp_id
  assoc := C.assoc

/-- E.3.1.4. A small family of representatives for bounded categories.
The conclusion is a strict isomorphism of categories. -/
theorem bounded_category_representatives (κ : Cardinal.{u}) :
    (∀ D : BoundedCategoryCode κ, #(D.objects : Type u) ≤ κ ∧
      ∀ x y : D.objects, #(x ⟶ y) ≤ κ) ∧
    ∀ (C : Type u) [SmallCategory C], #C ≤ κ →
      (∀ x y : C, #(x ⟶ y) ≤ κ) → ∃ D : BoundedCategoryCode κ,
      Nonempty (IsoCat D.objects C) := by
  classical
  refine ⟨fun D => ⟨(bounded_type_representatives κ).1 D.objects,
    fun x y => (bounded_type_representatives κ).1 (D.arrows x y)⟩, ?_⟩
  intro C _ hC hHom
  obtain ⟨O, ⟨e⟩⟩ := (bounded_type_representatives κ).2 C hC
  have ha (x y : O) : ∃ S : Set κ.out, Nonempty ((e.symm x ⟶ e.symm y) ≃ S) :=
    (bounded_type_representatives κ).2 _ (hHom (e.symm x) (e.symm y))
  let A (x y : O) := (ha x y).choose
  let h (x y : O) : (e.symm x ⟶ e.symm y) ≃ A x y := (ha x y).choose_spec.some
  let D : BoundedCategoryCode κ :=
    { objects := O
      arrows := A
      id := fun x => h x x (𝟙 (e.symm x))
      comp := fun {x y z} f g => h x z ((h x y).symm f ≫ (h y z).symm g)
      id_comp := fun f => by simp
      comp_id := fun f => by simp
      assoc := fun f g k => by simp [Category.assoc] }
  letI : SmallCategory D.objects := boundedCategoryCodeSmallCategory κ D
  let F : D.objects ⥤ C :=
    { obj := e.symm
      map := fun {x y} f => (h x y).symm f
      map_id := fun x => (h x x).symm_apply_apply _
      map_comp := fun {x y z} _ _ => (h x z).symm_apply_apply _ }
  have hF : F.FullyFaithful :=
    { preimage := fun {x y} f => h x y f
      map_preimage := fun f => Equiv.symm_apply_apply _ f
      preimage_map := fun f => Equiv.apply_symm_apply _ f }
  letI : F.IsIso := ⟨hF.faithful, hF.full, e.symm.bijective⟩
  exact ⟨D, ⟨F.asIsomorphism⟩⟩


/-- The indexing set of closed compact Hausdorff subspaces of a space. -/
def ClosedCompactHausdorffSubspace (X : Type u) [TopologicalSpace X] :=
  {s : CompactHausdorffSubspace X // IsClosed s.1}

private abbrev closedCHSet {X : Type u} [TopologicalSpace X]
    (K : ClosedCompactHausdorffSubspace X) : Set X := K.1.1

/-- The canonical map from the coproduct of a collection of subspaces. -/
def compactSubspaceCoproductMap {X : Type u} [TopologicalSpace X]
    (S : Set (ClosedCompactHausdorffSubspace X))
    (x : Σ K : S, (closedCHSet K.val : Type u)) : X := x.2.val

private theorem isClosed_sigma_prod_iff {I Y : Type u} [TopologicalSpace Y]
    {A : I → Type u} [∀ i, TopologicalSpace (A i)] {S : Set ((Σ i, A i) × Y)} :
    IsClosed S ↔ ∀ i : I, IsClosed ((fun p : A i × Y => (⟨i, p.1⟩, p.2)) ⁻¹' S) := by
  rw [← (Homeomorph.sigmaProdDistrib (X := A) (Y := Y)).symm.isClosed_preimage,
    isClosed_sigma_iff]
  rfl

private theorem isClosed_coproduct_kernel {X : Type u} [TopologicalSpace X]
    (S : Set (ClosedCompactHausdorffSubspace X)) :
    IsClosed {p : (Σ K : S, (closedCHSet K.val : Type u)) ×
        (Σ K : S, (closedCHSet K.val : Type u)) |
      compactSubspaceCoproductMap S p.1 = compactSubspaceCoproductMap S p.2} := by
  apply isClosed_sigma_prod_iff.mpr
  intro i
  apply (Homeomorph.prodComm _ _).isClosed_preimage.mp
  apply isClosed_sigma_prod_iff.mpr
  intro j
  let D : Set (closedCHSet j.val) := Subtype.val ⁻¹' closedCHSet i.val
  have hD : IsClosed D := i.val.property.preimage continuous_subtype_val
  letI : CompactSpace (closedCHSet j.val) := isCompact_iff_compactSpace.mp j.val.val.property.1
  letI : T2Space (closedCHSet i.val) := i.val.val.property.2
  letI : T2Space (closedCHSet j.val) := j.val.val.property.2
  letI : CompactSpace D := isCompact_iff_compactSpace.mp hD.isCompact
  let e (x : D) : (closedCHSet j.val) × (closedCHSet i.val) :=
    (x.val, ⟨x.val.val, x.property⟩)
  have he : Continuous e := continuous_subtype_val.prodMk
    ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)
  have hR : range e = {p : (closedCHSet j.val) × (closedCHSet i.val) | p.2.val = p.1.val} := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      rfl
    · intro h
      have h' : x.1.val ∈ closedCHSet i.val := by rw [← h]; exact x.2.property
      refine ⟨⟨x.1, h'⟩, Prod.ext rfl (Subtype.ext h.symm)⟩
  change IsClosed {p : (closedCHSet j.val) × (closedCHSet i.val) | p.2.val = p.1.val}
  rw [← hR]
  exact (isCompact_range he).isClosed

/-- E.2.1.13. A compactly generated space is weakly Hausdorff exactly
when it is a quotient of a coproduct of its closed compact Hausdorff
subspaces. In the forward direction one may take all such subspaces. -/
theorem weaklyHausdorff_iff_compactSubspace_quotient {X : Type u} [TopologicalSpace X]
    [CompactlyGeneratedSpace X] :
    WeaklyHausdorff X ↔ ∃ S : Set (ClosedCompactHausdorffSubspace X),
      IsQuotientMap (compactSubspaceCoproductMap S) := by
  constructor
  · intro hX
    let S : Set (ClosedCompactHausdorffSubspace X) := univ
    let q := compactSubspaceCoproductMap S
    have hc : Continuous q := continuous_sigma_iff.mpr fun _ => continuous_subtype_val
    refine ⟨S, isQuotientMap_iff_isClosed.mpr ⟨?_, fun U => ⟨fun hu => hu.preimage hc, ?_⟩⟩⟩
    · intro x
      let K : ClosedCompactHausdorffSubspace X :=
        ⟨singletonCompactSubspace x, weaklyHausdorff_closed_singleton hX x⟩
      exact ⟨⟨⟨K, mem_univ _⟩, ⟨x, mem_singleton _⟩⟩, rfl⟩
    · intro hu
      apply UCompactlyGeneratedSpace.isClosed
      intro K g
      have hclose := hX K g
      let R := range g
      let g' : C(K, R) := ⟨Set.rangeFactorization g, g.continuous.rangeFactorization⟩
      have hT2 : T2Space R := weaklyHausdorff_compact_surjection
        (weaklyHausdorff_subspace hX R) K g' (rangeFactorization_surjective)
      let i : S := ⟨⟨⟨R, isCompact_range g.continuous, hT2⟩, hclose⟩, mem_univ _⟩
      let lift : K → Σ i : S, (closedCHSet i.val : Type u) := fun k => ⟨i, g' k⟩
      have hlift : Continuous lift := continuous_sigmaMk.comp g'.continuous
      exact hu.preimage hlift
  · rintro ⟨S, hq⟩
    let W := Σ i : S, (closedCHSet i.val : Type u)
    letI (i : S) : CompactSpace (closedCHSet i.val) :=
      isCompact_iff_compactSpace.mp i.val.val.property.1
    letI (i : S) : T2Space (closedCHSet i.val) := i.val.val.property.2
    haveI : CompactlyGeneratedSpace W := inferInstance
    let q : W → X := compactSubspaceCoproductMap S
    let Q : Kelley (W × W) → Kelley (X × X) := Prod.map q q
    have hQ : IsQuotientMap Q := kelleyProduct_quotient hq hq
    have hD : IsClosed {p : Kelley (X × X) | p.1 = p.2} := by
      apply ((isQuotientMap_iff_isClosed.mp hQ).2 _).mpr
      exact (isClosed_coproduct_kernel S).preimage continuous_Kelley_forget
    apply (weaklyHausdorff_iff_kelleyClosedDiagonal X).mpr
    intro K g
    exact hD.preimage (continuous_to_Kelley g.continuous)


/-- E.2.1.15. In a sequential final presentation by T₁ spaces with
finite fibres, every compact set lies in one of the stages. -/
theorem compact_subset_sequential_final_stage {X : Type u} [TopologicalSpace X]
    {Y : ℕ → Type u} [∀ n, TopologicalSpace (Y n)] [∀ n, T1Space (Y n)]
    (f : ∀ n, Y n → X)
    (hcover : ∀ x : X, ∃ n, x ∈ range (f n))
    (hmono : Monotone (fun n => range (f n)))
    (hfinal : ∀ S : Set X, IsClosed S ↔ ∀ n, IsClosed (f n ⁻¹' S))
    (hfinite : ∀ n x, Set.Finite (f n ⁻¹' {x}))
    {K : Set X} (hK : IsCompact K) :
    ∃ n, K ⊆ range (f n) := by
  classical
  by_contra hneg
  have hex (n : ℕ) : ∃ x ∈ K, x ∉ range (f n) := by
    exact not_subset.mp (fun h => hneg ⟨n, h⟩)
  choose x hxK hx using hex
  let F := range x
  have hclosed (B : Set X) (hB : B ⊆ F) : IsClosed B := by
    apply (hfinal B).mpr
    intro n
    have hfin : (f n ⁻¹' B).Finite := by
      have hsmall : (x '' Iio n).Finite := (Set.finite_lt_nat n).image x
      refine (hsmall.biUnion fun b _ => hfinite n b).subset ?_
      intro y hy
      obtain ⟨i, he⟩ := hB hy
      have hi : i < n := by
        by_contra! hni
        exact hx i (he ▸ hmono hni (mem_range_self y))
      exact mem_biUnion ⟨i, hi, he⟩ (by simp)
    exact hfin.isClosed
  have hF : IsCompact F := hK.of_isClosed_subset (hclosed F Subset.rfl)
    (fun _ hx' => by obtain ⟨i, rfl⟩ := hx'; exact hxK i)
  have hdisc : IsDiscrete F := by
    rw [isDiscrete_iff_discreteTopology, discreteTopology_iff_isOpen_singleton]
    intro y
    have hcl : IsClosed (F \ {y.val}) := hclosed _ sdiff_subset
    have he : ({y} : Set F) = Subtype.val ⁻¹' (F \ {y.val})ᶜ := by
      ext z
      simp [Subtype.ext_iff]
    rw [he]
    exact hcl.isOpen_compl.preimage continuous_subtype_val
  have hFfin := hF.finite hdisc
  let N (y : X) := (hcover y).choose
  obtain ⟨n, hn⟩ : BddAbove (N '' F) := (hFfin.image N).bddAbove
  have hi : N (x n) ≤ n := hn (mem_image_of_mem _ (mem_range_self n))
  exact hx n (hmono hi (hcover (x n)).choose_spec)

/-- The manuscript's hemicompactness condition. -/
def HasCofinalCompactSequence (X : Type u) [TopologicalSpace X] : Prop :=
  ∃ K : ℕ → Set X, (∀ n, IsCompact (K n)) ∧ ∀ S : Set X, IsCompact S → ∃ n, S ⊆ K n

private theorem compact_stage_mem_nhds {X : Type u} [TopologicalSpace X]
    [FirstCountableTopology X] {K : ℕ → Set X}
    (hcover : ∀ S : Set X, IsCompact S → ∃ n, S ⊆ K n) (a : X) :
    ∃ n, K n ∈ nhds a := by
  obtain ⟨U, hU⟩ := (nhds a).exists_antitone_basis
  by_contra h
  have hnot (n : ℕ) : ¬ U n ⊆ K n := fun hn =>
    h ⟨n, mem_of_superset (hU.toHasBasis.mem_of_mem (by trivial : True)) hn⟩
  choose x hxU hxK using fun n => not_subset.mp (hnot n)
  have ht : Tendsto x atTop (nhds a) := by
    apply hU.toHasBasis.tendsto_right_iff.mpr
    intro n _
    filter_upwards [eventually_ge_atTop n] with i hi
    exact hU.antitone hi (hxU i)
  obtain ⟨n, hn⟩ := hcover (insert a (range x)) ht.isCompact_insert_range
  exact hxK n (hn (mem_insert_of_mem _ (mem_range_self n)))

/-- E.2.1.16. A first-countable hemicompact space has a compact
neighbourhood at every point. -/
theorem weaklyLocallyCompact_of_hemicompact {X : Type u} [TopologicalSpace X]
    [FirstCountableTopology X] (hX : HasCofinalCompactSequence X) :
    WeaklyLocallyCompactSpace X where
  exists_compact_mem_nhds a := by
    obtain ⟨K, hK, hcover⟩ := hX
    obtain ⟨n, hn⟩ := compact_stage_mem_nhds hcover a
    exact ⟨K n, hK n, hn⟩


/-- E.2.1.17. In a first-countable weakly Hausdorff space whose topology
is final for a countable covering family of compact Hausdorff probes,
each point has a basis of compact neighbourhoods. -/
theorem locallyCompact_of_countable_compactHausdorff_tests {X : Type u} [TopologicalSpace X]
    [FirstCountableTopology X] (hX : WeaklyHausdorff X)
    (K : ℕ → CompHaus.{u}) (f : ∀ i, C(K i, X))
    (hcover : ∀ x : X, ∃ i, x ∈ range (f i))
    (hfinal : ∀ S : Set X, IsClosed S ↔ ∀ i, IsClosed (f i ⁻¹' S)) :
    LocallyCompactSpace X := by
  let S (n : ℕ) : Set X := ⋃ i ∈ Iic n, range (f i)
  have hMono : Monotone S := by
    intro i j hij x hx
    obtain ⟨k, hk, h⟩ := mem_iUnion₂.mp hx
    exact mem_iUnion₂.mpr ⟨k, (show k ≤ i from hk).trans hij, h⟩
  have hSH (n : ℕ) : IsCompact (S n) ∧ T2Space (S n) := by
    let W := Σ i : Fin (n + 1), K i.val
    let e : C(W, S n) :=
      ⟨fun p => ⟨f p.1.val p.2, mem_iUnion₂.mpr
          ⟨p.1.val, Nat.le_of_lt_succ p.1.isLt, mem_range_self _⟩⟩,
        continuous_sigma_iff.mpr fun i => (f i.val).continuous.subtype_mk _⟩
    have he : Surjective e := by
      intro x
      obtain ⟨i, hi, z, hz⟩ := mem_iUnion₂.mp x.property
      exact ⟨⟨⟨i, Nat.lt_succ_of_le hi⟩, z⟩, Subtype.ext hz⟩
    have hT := weaklyHausdorff_compact_surjection (weaklyHausdorff_subspace hX (S n))
      (CompHaus.of W) e he
    have hc : IsCompact (range (fun w : W => (e w).val)) :=
      isCompact_range (continuous_subtype_val.comp e.continuous)
    have hRange : range (fun w : W => (e w).val) = S n := by
      change range (Subtype.val ∘ (e : W → S n)) = S n
      rw [range_comp, he.range_eq, image_univ, Subtype.range_coe]
    exact ⟨hRange ▸ hc, hT⟩
  letI : T1Space X := ⟨weaklyHausdorff_closed_singleton hX⟩
  have hScover (x : X) : ∃ n, x ∈ S n := by
    obtain ⟨i, hi⟩ := hcover x
    exact ⟨i, mem_iUnion₂.mpr ⟨i, mem_Iic.mpr le_rfl, hi⟩⟩
  let e (n : ℕ) : S n → X := Subtype.val
  have he (n : ℕ) : range (e n) = S n := Subtype.range_coe
  have hTop (A : Set X) : IsClosed A ↔ ∀ n, IsClosed ((e n) ⁻¹' A) := by
    refine ⟨fun h n => h.preimage continuous_subtype_val, fun h => (hfinal A).mpr ?_⟩
    intro n
    let g : K n → S n := fun p => ⟨f n p, mem_iUnion₂.mpr ⟨n, mem_Iic.mpr le_rfl, mem_range_self p⟩⟩
    exact (h n).preimage ((f n).continuous.subtype_mk _ : Continuous g)
  have hCofinal (A : Set X) (hA : IsCompact A) : ∃ n, A ⊆ S n := by
    have h := compact_subset_sequential_final_stage e
      (fun x => by simpa only [he] using hScover x)
      (by simpa only [he] using hMono) hTop
      (fun n x => (Set.finite_singleton x).preimage Subtype.val_injective.injOn) hA
    simpa only [he] using h
  refine ⟨fun x U hU => ?_⟩
  obtain ⟨n, hn⟩ := compact_stage_mem_nhds hCofinal x
  letI : CompactSpace (S n) := isCompact_iff_compactSpace.mp (hSH n).1
  letI : T2Space (S n) := (hSH n).2
  let x' : S n := ⟨x, mem_of_mem_nhds hn⟩
  have hU' : Subtype.val ⁻¹' U ∈ nhds x' := continuous_subtype_val.continuousAt hU
  obtain ⟨V, hV, hVs, hVc⟩ := local_compact_nhds hU'
  refine ⟨Subtype.val '' V, ?_, image_subset_iff.mpr hVs, hVc.image continuous_subtype_val⟩
  have hVm : Subtype.val '' V ∈ map Subtype.val (nhds x') := by
    exact Filter.mem_map.mpr (mem_of_superset hV (subset_preimage_image _ _))
  rwa [map_nhds_subtype_val, nhdsWithin_eq_nhds.mpr hn] at hVm


/-- E.3.3.4. In any family of CGWH spaces with the closure property of
E.3.2.3(2), the stated bounds on a compact Hausdorff cover put its
target in the family up to homeomorphism. -/
theorem bounded_compact_cover_has_representative {P : CGWH.{u} → Prop}
    (hP : ∀ A B : CGWH.{u}, P A →
      topologicalSize B.obj ≤ smallSpaceBound (topologicalSize A.obj) →
      ∃ B' : CGWH.{u}, P B' ∧ Nonempty (B'.obj ≃ₜ B.obj))
    {A B : CGWH.{u}} (hA : P A)
    {I : Type u} (K : I → CompactHausdorffSubspace B.obj)
    (hq : IsQuotientMap (fun p : Σ i, (K i).1 => p.2.val))
    (hs : ∀ i, topologicalSize (K i).1 ≤ topologicalSize A.obj)
    (hi : #I ≤ topologicalSize A.obj) :
    ∃ B' : CGWH.{u}, P B' ∧ Nonempty (B'.obj ≃ₜ B.obj) := by
  let κ := topologicalSize A.obj
  have hω : ℵ₀ ≤ κ := le_max_left _ _
  have hκ : κ ≠ 0 := (aleph0_pos.trans_le hω).ne'
  have hsup : (⨆ i, topologicalSize (K i).1) ≤ κ := ciSup_le' hs
  have hc : ∀ x : B.obj, ∃ i, x ∈ (K i).1 := by
    intro x
    obtain ⟨⟨i, w⟩, rfl⟩ := hq.surjective x
    exact ⟨i, w.property⟩
  apply hP A B hA
  refine (topologicalSize_of_compact_cover B.property K hc).trans ?_
  have hb : κ ^ κ ≤ smallSpaceBound κ := (le_max_right _ _).trans (le_max_right _ _)
  exact max_le ((hω.trans (le_of_lt (Cardinal.cantor _))).trans (by
    rw [← power_self_eq hω]; exact hb))
    (((power_le_power_right hsup).trans (power_le_power_left hκ hi)).trans hb)


/-- The fundamental covering families of E.3.5.2, with index sets
chosen as subsets of a fixed carrier as in E.3.1.2. -/
structure FundamentalCoverFamily {A : Type u} (basic : A → CGWH.{u}) (ν : Cardinal.{u}) where
  target : A
  indices : Set ν.out
  member : indices → CompactHausdorffSubspace (basic target).obj

/-- The code in E.3.5.3 is in the universe of the given small families.
It specifies all members and therefore also every inclusion map. -/
def fundamentalCoverFamily_code {A : Type u} (basic : A → CGWH.{u}) (ν : Cardinal.{u}) :
    FundamentalCoverFamily basic ν ≃
      (Σ a : A × Set ν.out, a.2 → CompactHausdorffSubspace (basic a.1).obj) where
  toFun U := ⟨(U.target, U.indices), U.member⟩
  invFun U := ⟨U.1.1, U.1.2, U.2⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

theorem fundamentalCoverFamily_members_closed {A : Type u} {basic : A → CGWH.{u}}
    {ν : Cardinal.{u}} (U : FundamentalCoverFamily basic ν) (i : U.indices) :
    IsClosedEmbedding (Subtype.val : (U.member i).val → (basic U.target).obj) :=
  (compactSubspace_closed (basic U.target).property (U.member i)).isClosedEmbedding_subtypeVal

theorem fundamentalCoverFamily_bounded {A : Type u} (basic : A → CGWH.{u}) (ν : Cardinal.{u}) :
    (∀ U : FundamentalCoverFamily basic ν, #U.indices ≤ ν) ∧
      ∀ (a : A) (I : Type u), #I ≤ ν → ∀ K : I → CompactHausdorffSubspace (basic a).obj,
        ∃ (U : FundamentalCoverFamily basic ν) (_h : U.target = a) (e : I ≃ U.indices),
          ∀ i, HEq (U.member (e i)) (K i) := by
  constructor
  · exact fun U => (bounded_type_representatives ν).1 U.indices
  · intro a I hI K
    obtain ⟨J, ⟨e⟩⟩ := (bounded_type_representatives ν).2 I hI
    refine ⟨⟨a, J, K ∘ e.symm⟩, rfl, e, fun i => ?_⟩
    exact heq_of_eq (congrArg K (e.symm_apply_apply i))

/-- The proposed family `V_(ακ + 1)` in the proof of E.3.1.2 need
not consist of sets of cardinality at most `κ`. For `κ = 3`,
the element `V₃` has four elements and belongs to `V₄`. -/
theorem vonNeumann_three_exceeds_printed_bound :
    ZFSet.vonNeumann (3 : Ordinal.{u}) ∈ ZFSet.vonNeumann (4 : Ordinal.{u}) ∧
      (3 : Cardinal.{u}) < ZFSet.card (ZFSet.vonNeumann (3 : Ordinal.{u})) := by
  refine ⟨ZFSet.vonNeumann_mem_of_lt (by exact_mod_cast (show (3 : ℕ) < 4 by decide)), ?_⟩
  conv_rhs =>
    rw [show (3 : Ordinal.{u}) = ((0 + 1) + 1) + 1 by norm_num]
  simp only [ZFSet.vonNeumann_add_one, ZFSet.vonNeumann_zero, ZFSet.card_powerset,
    ZFSet.card_empty]
  rw [show (2 : Cardinal.{u}) ^ (0 : Cardinal.{u}) = 1 by simp,
    show (2 : Cardinal.{u}) ^ (1 : Cardinal.{u}) = 2 by simp,
    show (2 : Cardinal.{u}) ^ (2 : Cardinal.{u}) = 4 by
      rw [show (2 : Cardinal.{u}) = ((2 : ℕ) : Cardinal.{u}) by rfl,
        Cardinal.power_natCast]
      exact_mod_cast (show (2 : ℕ) ^ 2 = 4 by decide)]
  exact_mod_cast (show (3 : ℕ) < 4 by decide)

end Masullo
