import CompactlyGenerated
import FunctionSpaces
import Mathlib.Analysis.Real.Cardinality
import Mathlib.Topology.DiscreteSubset
import Mathlib.Topology.LocalAtTarget

open Function Set Topology TopologicalSpace

namespace Masullo.EmbeddingObstruction

/-- The extra point `none` is discrete in the source. -/
def Point := Option ℝ

instance : TopologicalSpace Point := ⊥
instance : DiscreteTopology Point := ⟨rfl⟩
instance : Inhabited Point := ⟨none⟩

abbrev Coordinate := {s : Set ℝ // s.Countable}
abbrev Cube := Coordinate → Bool

/-- Countable subsets give Boolean coordinates; `none` maps to the zero vector. -/
noncomputable def encode (p : Point) (i : Coordinate) : Bool := by
  classical
  exact match p with
  | none => false
  | some x => decide (x ∈ i.val)

private theorem encode_true (p : Point) (i : Coordinate) :
    encode p i = true ↔ ∃ x ∈ i.val, p = Option.some x := by
  classical
  cases p with
  | none => simp [encode]
  | some y =>
    simp only [encode, decide_eq_true_eq]
    exact ⟨fun h => ⟨y, h, rfl⟩, fun ⟨_, h, eq⟩ => (Option.some.inj eq).symm ▸ h⟩

private theorem encode_singleton (p : Point) (x : ℝ) :
    encode p ⟨{x}, countable_singleton x⟩ = true ↔ p = Option.some x := by
  rw [encode_true]
  simp

theorem encode_injective : Injective encode := by
  intro a b hab
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some y =>
      have hy := (encode_singleton (Option.some y) y).mpr rfl
      rw [← hab] at hy
      exact Bool.noConfusion hy
  | some x =>
    have hx := (encode_singleton (Option.some x) x).mpr rfl
    rw [hab] at hx
    exact ((encode_singleton b x).mp hx).symm

theorem encode_not_embedding : ¬ IsEmbedding encode := by
  classical
  intro h
  obtain ⟨V, hV, heq⟩ := h.isInducing.isOpen_iff.mp
    (isOpen_discrete ({Option.none} : Set Point))
  have hzero : encode (Option.none : Point) ∈ V := by
    change (Option.none : Point) ∈ encode ⁻¹' V
    rw [heq]
    exact mem_singleton _
  obtain ⟨I, U, hU, hbox⟩ := isOpen_pi_iff.mp hV _ hzero
  let S : Set ℝ := ⋃ i : (I : Set Coordinate), i.val.val
  have hS : S.Countable := countable_iUnion fun i => i.val.property
  have hnonempty : ∃ x, x ∉ S := by
    by_contra! h
    exact Cardinal.not_countable_real ((eq_univ_of_forall h) ▸ hS)
  obtain ⟨x, hx⟩ := hnonempty
  have hVx : encode (Option.some x) ∈ V := hbox fun i hi => by
    have hxi : x ∉ i.val := fun hmem => hx (mem_iUnion.mpr ⟨⟨i, hi⟩, hmem⟩)
    have he : encode (Option.some x) i = encode (Option.none : Point) i := by
      simp [encode, hxi]
    rw [he]
    exact (hU i hi).2
  have hp : (Option.some x : Point) ∈ ({Option.none} : Set Point) := heq ▸ hVx
  have he : (Option.some x : Point) = (Option.none : Point) := mem_singleton_iff.mp hp
  change Option.some x = (Option.none : Option ℝ) at he
  cases he

private theorem finite_compact_image {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (h : K → Point) (hc : Continuous (encode ∘ h)) : (range (encode ∘ h)).Finite := by
  classical
  let A : Set ℝ := Option.some ⁻¹' range h
  have hA : A.Finite := by
    by_contra hinf
    obtain ⟨S, hSA, hSc, hSi⟩ := Set.Infinite.exists_subset_countable_infinite hinf
    let j : Coordinate := ⟨S, hSc⟩
    let B : Set Cube := range (encode ∘ h) ∩ {p | p j = true}
    have hBc : IsCompact B := (isCompact_range hc).inter_right
      (isClosed_singleton.preimage (continuous_apply j))
    have hBd : IsDiscrete B := isDiscrete_iff_forall_mem_exists_isOpen.mpr (by
      rintro _ ⟨⟨k, rfl⟩, hk⟩
      obtain ⟨x, hx, hkx⟩ := (encode_true (h k) j).mp hk
      let i : Coordinate := ⟨{x}, countable_singleton x⟩
      have ho : IsOpen ((fun p : Cube => p i) ⁻¹' ({true} : Set Bool)) :=
        (isOpen_discrete ({true} : Set Bool)).preimage (continuous_apply i)
      refine ⟨{p | p i = true}, ho, ?_⟩
      ext y
      constructor
      · rintro ⟨hy, ⟨⟨l, rfl⟩, _⟩⟩
        exact mem_singleton_iff.mpr (congrArg encode (((encode_singleton (h l) x).mp hy).trans hkx.symm))
      · rintro hy
        subst y
        exact ⟨(encode_singleton (h k) x).mpr hkx, ⟨mem_range_self k, hk⟩⟩)
    have hSf : S.Finite := (hBc.finite hBd).preimage (f := encode ∘ Option.some)
      (encode_injective.comp (Option.some_injective ℝ)).injOn |>.subset (by
        intro x hx
        obtain ⟨k, hk⟩ := hSA hx
        exact ⟨⟨k, congrArg encode hk⟩, (encode_true (Option.some x) j).mpr ⟨x, hx, rfl⟩⟩)
    exact hSi hSf
  have hr : (range h).Finite := ((hA.image Option.some).insert Option.none).subset (by
    intro p hp
    cases p with
    | none => exact mem_insert _ _
    | some x => exact mem_insert_of_mem _ ⟨x, hp, rfl⟩)
  simpa only [range_comp] using hr.image encode

/-- The continuity tests in E.1.2.27 and E.2.3.3 all hold for `encode`,
even though its image has a strictly coarser subspace topology. -/
theorem encode_detects_continuity {T : Type*} [TopologicalSpace T]
    [UCompactlyGeneratedSpace.{0} T] (g : T → Point) : Continuous (encode ∘ g) ↔ Continuous g := by
  refine ⟨fun h => ?_, fun h => continuous_of_discreteTopology.comp h⟩
  apply continuous_from_uCompactlyGeneratedSpace
  intro K k
  let a := g ∘ k
  have ha : Continuous (encode ∘ a) := h.comp k.continuous
  let R := range (encode ∘ a)
  haveI : DiscreteTopology R := isDiscrete_iff_discreteTopology.mp (finite_compact_image a ha).isDiscrete
  let l : R → Point := fun r => invFun encode r.val
  let b : K → R := fun x => ⟨encode (a x), mem_range_self x⟩
  have hb : Continuous b := ha.subtype_mk _
  have he : l ∘ b = a := by
    funext x
    exact leftInverse_invFun encode_injective (a x)
  change Continuous a
  rw [← he]
  exact continuous_of_discreteTopology.comp hb

/-- Both spaces meet the separation and generation hypotheses of the printed lemmas. -/
theorem immersion_criteria_counterexample :
    (CompactlyGeneratedSpace Point ∧ WeaklyHausdorff Point) ∧
    (CompactlyGeneratedSpace Cube ∧ WeaklyHausdorff Cube) ∧
    Continuous encode ∧ Injective encode ∧ ¬ IsEmbedding encode ∧
    (∀ (T : Type) [TopologicalSpace T] [CompactlyGeneratedSpace T],
      ∀ g : T → Point, Continuous (encode ∘ g) ↔ Continuous g) := by
  have hWH (Z : Type) [TopologicalSpace Z] [T2Space Z] : WeaklyHausdorff Z :=
    fun _ k => (isCompact_range k.continuous).isClosed
  exact ⟨⟨inferInstance, hWH Point⟩, ⟨inferInstance, hWH Cube⟩,
    continuous_of_discreteTopology, encode_injective, encode_not_embedding,
    fun _ _ _ g => encode_detects_continuity g⟩

end Masullo.EmbeddingObstruction

namespace Masullo

universe u

/-- The image map with the compactly generated refinement of the subspace topology. -/
def kelleyImageMap {X Y : Type u} [TopologicalSpace Y] (f : X → Y) : X → Kelley (range f) :=
  fun x => ⟨f x, mem_range_self x⟩

private theorem kelleyImageMap_detects {X Y T : Type u}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace T] [CompactlyGeneratedSpace T]
    {f : X → Y} (hf : Continuous f) (h : IsHomeomorph (kelleyImageMap f)) (g : T → X) :
    Continuous (f ∘ g) ↔ Continuous g := by
  refine ⟨fun hg => h.isEmbedding.isInducing.continuous_iff.mpr ?_, fun hg => hf.comp hg⟩
  exact continuous_to_Kelley (X := T) (Y := range f) (hg.subtype_mk fun t => mem_range_self (g t))

private theorem kelleyImageMap_isHomeomorph_of_test {X Y : Type u}
    [TopologicalSpace X] [TopologicalSpace Y] [CompactlyGeneratedSpace X]
    {f : X → Y} (hf : Continuous f) (hi : Injective f)
    (ht : ∀ g : Kelley (range f) → X, Continuous (f ∘ g) → Continuous g) :
    IsHomeomorph (kelleyImageMap f) := by
  let e : X ≃ Kelley (range f) := Equiv.ofInjective f hi
  change IsHomeomorph e
  apply (Equiv.isHomeomorph_iff e).mpr
  refine ⟨continuous_to_Kelley (Y := range f) (hf.subtype_mk mem_range_self), ht e.symm ?_⟩
  have he : f ∘ e.symm = fun x : Kelley (range f) => x.val := by
    funext x
    exact congrArg Subtype.val (e.apply_symm_apply x)
  rw [he]
  exact continuous_subtype_val.comp (continuous_Kelley_forget (X := range f))

/-- Corrected Lemma E.1.2.27. Compactly generated tests recover the
compactly generated image topology. -/
theorem cg_kelleyImage_criterion {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactlyGeneratedSpace X] {f : X → Y} (hf : Continuous f) (hi : Injective f) :
    IsHomeomorph (kelleyImageMap f) ↔ ∀ (T : Type u) [TopologicalSpace T] [CompactlyGeneratedSpace T],
      ∀ g : T → X, Continuous (f ∘ g) ↔ Continuous g := by
  refine ⟨fun h _ _ _ g => kelleyImageMap_detects hf h g, fun h => ?_⟩
  exact kelleyImageMap_isHomeomorph_of_test hf hi (fun g => (h _ g).mp)

/-- Corrected Lemma E.2.3.3. Weakly Hausdorff compactly generated tests
suffice because the compactly generated image is weakly Hausdorff. -/
theorem cgwh_kelleyImage_criterion {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactlyGeneratedSpace X] (hY : WeaklyHausdorff Y) {f : X → Y}
    (hf : Continuous f) (hi : Injective f) :
    IsHomeomorph (kelleyImageMap f) ↔ ∀ (T : Type u) [TopologicalSpace T] [CompactlyGeneratedSpace T],
      WeaklyHausdorff T → ∀ g : T → X, Continuous (f ∘ g) ↔ Continuous g := by
  refine ⟨fun h _ _ _ _ g => kelleyImageMap_detects hf h g, fun h => ?_⟩
  apply kelleyImageMap_isHomeomorph_of_test hf hi
  exact fun g => (h _ (weaklyHausdorff_Kelley (weaklyHausdorff_subspace hY (range f))) g).mp

/-- The original conclusion holds when the subspace image is compactly generated. -/
theorem isEmbedding_of_kelleyImage {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} [CompactlyGeneratedSpace (range f)] (h : IsHomeomorph (kelleyImageMap f)) :
    IsEmbedding f := by
  let e : Kelley (range f) ≃ range f := Equiv.refl (range f)
  have hId : IsHomeomorph e := (Equiv.isHomeomorph_iff e).mpr
    ⟨continuous_Kelley_forget (X := range f),
      continuous_to_Kelley (X := range f) (Y := range f) continuous_id⟩
  exact IsEmbedding.subtypeVal.comp (hId.isEmbedding.comp h.isEmbedding)

/-- Corrected Lemma E.1.2.28. Postcomposition along an embedding
recovers the Kelley topology on its image, and a closed embedding gives
an ordinary closed embedding of mapping spaces. -/
theorem kelleyMap_postcompose_embedding {X Y Z : Type u}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    {i : C(Z, Y)} (hi : IsEmbedding i) :
    let post := KelleyMap.map (ContinuousMap.id X) i
    IsHomeomorph (kelleyImageMap post) ∧
      (CompactlyGeneratedSpace (range post) → IsEmbedding post) ∧
      (IsClosedEmbedding i → IsClosedEmbedding post) := by
  let post := KelleyMap.map (ContinuousMap.id X) i
  have hc : Continuous post := KelleyMap.continuous_map (ContinuousMap.id X) i
  have hinj : Injective post := by
    intro f g h
    exact KelleyMap.ext fun x => hi.injective (congrArg (fun k : KelleyMap X Y => k x) h)
  have ht := (cg_kelleyImage_criterion hc hinj).mpr (by
    intro T _ _ g
    refine ⟨fun hg => ?_, hc.comp⟩
    apply (KelleyMap.continuous_uncurry_iff g).mp
    apply hi.isInducing.continuous_iff.mpr
    exact (KelleyMap.continuous_uncurry_iff (post ∘ g)).mpr hg)
  refine ⟨ht, fun h => @isEmbedding_of_kelleyImage _ _ _ _ _ h ht, fun h => ?_⟩
  have hr : range post = ⋂ x : X, {f : KelleyMap X Y | f x ∈ range i} := by
    ext f
    simp only [mem_iInter, mem_range, mem_ofPred_eq]
    constructor
    · rintro ⟨g, rfl⟩ x
      exact ⟨g x, rfl⟩
    · intro hf
      let e := hi.toHomeomorph
      let g : C(X, Z) := ⟨fun x => e.symm ⟨f x, hf x⟩,
        e.symm.continuous.comp (f.map_continuous.subtype_mk _)⟩
      refine ⟨(show KelleyMap X Z from g), KelleyMap.ext fun x => ?_⟩
      exact congrArg Subtype.val (e.apply_symm_apply ⟨f x, hf x⟩)
  have hclosed : IsClosed (range post) := hr ▸ isClosed_iInter fun x =>
    h.isClosed_range.preimage (KelleyMap.continuous_eval_const x)
  letI : CompactlyGeneratedSpace (range post) := closed_compactlyGenerated hclosed
  exact ⟨isEmbedding_of_kelleyImage ht, hclosed⟩

namespace CGWH

open CategoryTheory

private theorem continuous_into_fibre {W : Type u} [TopologicalSpace W] [CompactlyGeneratedSpace W]
    {X Y T : CGWH.{u}} {f : X ⟶ Y} {g : T ⟶ Y} {k : W → FibreSubspace f g}
    (ha : Continuous fun w => (k w).val.1) (hb : Continuous fun w => (k w).val.2) : Continuous k := by
  apply IsEmbedding.subtypeVal.isInducing.continuous_iff.mpr
  exact continuous_to_Kelley (Y := X.obj × T.obj) (ha.prodMk hb)

private theorem fibre_snd_range {X Y T : CGWH.{u}} (f : X ⟶ Y) (g : T ⟶ Y) :
    range (fun p : FibreSubspace f g => p.val.2) = g.hom ⁻¹' range f.hom := by
  ext t
  constructor
  · rintro ⟨⟨⟨x, t'⟩, h⟩, rfl⟩
    exact ⟨x, h⟩
  · rintro ⟨x, h⟩
    exact ⟨⟨(x, t), h⟩, rfl⟩

private theorem kelleyImage_of_embedding {A B : Type u} [TopologicalSpace A] [TopologicalSpace B]
    [CompactlyGeneratedSpace A] {f : A → B} (h : IsEmbedding f) :
    IsHomeomorph (kelleyImageMap f) :=
  (cg_kelleyImage_criterion h.continuous h.injective).mpr fun _ _ _ _ =>
    h.isInducing.continuous_iff.symm

/-- The six composition clauses of Lemma E.2.3.6. -/
theorem properties_compose {X Y Z : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] [CompactlyGeneratedSpace X] {f : X → Y} {g : Y → Z}
    (hf : Continuous f) (hg : Continuous g) :
    (Injective f → Injective g → Injective (g ∘ f)) ∧
    (Surjective f → Surjective g → Surjective (g ∘ f)) ∧
    (IsHomeomorph (kelleyImageMap f) → IsHomeomorph (kelleyImageMap g) →
      IsHomeomorph (kelleyImageMap (g ∘ f))) ∧
    (IsClosedEmbedding f → IsClosedEmbedding g → IsClosedEmbedding (g ∘ f)) ∧
    (IsOpenEmbedding f → IsOpenEmbedding g → IsOpenEmbedding (g ∘ f)) ∧
    (IsQuotientMap f → IsQuotientMap g → IsQuotientMap (g ∘ f)) := by
  refine ⟨fun h k => k.comp h, fun h k => k.comp h, ?_,
    fun h k => k.comp h, fun h k => k.comp h, fun h k => k.comp h⟩
  intro h k
  have hi : Injective f := fun a b hab => h.isEmbedding.injective (Subtype.ext hab)
  have hj : Injective g := fun a b hab => k.isEmbedding.injective (Subtype.ext hab)
  exact (cg_kelleyImage_criterion (hg.comp hf) (hj.comp hi)).mpr fun _ _ _ a =>
    (kelleyImageMap_detects hg k (f ∘ a)).trans (kelleyImageMap_detects hf h a)

/-- The six base-change clauses of Lemma E.2.3.6. -/
theorem fibre_properties_baseChange {X Y T : CGWH.{u}} (f : X ⟶ Y) (g : T ⟶ Y) :
    let p : FibreSubspace f g → T.obj := fun z => z.val.2
    (Injective f.hom → Injective p) ∧ (Surjective f.hom → Surjective p) ∧
    (IsHomeomorph (kelleyImageMap f.hom) → IsHomeomorph (kelleyImageMap p)) ∧
    (IsClosedEmbedding f.hom → IsClosedEmbedding p) ∧
    (IsOpenEmbedding f.hom → IsOpenEmbedding p) ∧
    (IsQuotientMap f.hom → IsQuotientMap p) := by
  let p : FibreSubspace f g → T.obj := fun z => z.val.2
  letI : CompactlyGeneratedSpace (FibreSubspace f g) :=
    closed_compactlyGenerated (fibreSubspace_isClosed f g)
  have hp : Continuous p := continuous_snd.comp (continuous_Kelley_forget.comp continuous_subtype_val)
  have hf := f.hom.hom.hom.continuous
  have hg := g.hom.hom.hom.continuous
  have hInject (hi : Injective f.hom) : Injective p := by
    intro a b hab
    exact Subtype.ext (Prod.ext (hi (a.property.trans ((congrArg g.hom hab).trans b.property.symm))) hab)
  have hImage (h : IsHomeomorph (kelleyImageMap f.hom)) : IsHomeomorph (kelleyImageMap p) := by
    have hi := hInject fun a b hab => h.isEmbedding.injective (Subtype.ext hab)
    apply (cg_kelleyImage_criterion hp hi).mpr
    intro W _ _ a
    refine ⟨fun ha => ?_, fun ha => hp.comp ha⟩
    have heq : (f.hom ∘ fun w => (a w).val.1) = g.hom ∘ (p ∘ a) :=
      funext fun w => (a w).property
    have hfst := (kelleyImageMap_detects hf h (fun w => (a w).val.1)).mp
      (heq.symm ▸ hg.comp ha)
    exact continuous_into_fibre hfst ha
  refine ⟨hInject, ?_, hImage, ?_, ?_, quotient_baseChange f g⟩
  · intro h t
    obtain ⟨x, hx⟩ := h (g.hom t)
    exact ⟨⟨(x, t), hx⟩, rfl⟩
  · intro h
    have hc : IsClosed (range p) := (fibre_snd_range f g).symm ▸ h.isClosed_range.preimage hg
    letI := closed_compactlyGenerated hc
    exact ⟨isEmbedding_of_kelleyImage (hImage (kelleyImage_of_embedding h.isEmbedding)), hc⟩
  · intro h
    have ho : IsOpen (range p) := (fibre_snd_range f g).symm ▸ h.isOpen_range.preimage hg
    letI := open_compactlyGenerated ho
    exact ⟨isEmbedding_of_kelleyImage (hImage (kelleyImage_of_embedding h.isEmbedding)), ho⟩

/-- The target-local clauses of Lemma E.2.3.6 for an arbitrary open cover. -/
theorem properties_of_openCover {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactlyGeneratedSpace X] {f : X → Y} (hf : Continuous f) {ι : Type*}
    {U : ι → Opens Y} (hU : IsOpenCover U) :
    (let fᵢ (i : ι) := (U i).1.restrictPreimage f
     ((∀ i, Injective (fᵢ i)) → Injective f) ∧
     ((∀ i, Surjective (fᵢ i)) → Surjective f) ∧
     ((∀ i, IsHomeomorph (kelleyImageMap (fᵢ i))) → IsHomeomorph (kelleyImageMap f)) ∧
     ((∀ i, IsClosedEmbedding (fᵢ i)) → IsClosedEmbedding f) ∧
     ((∀ i, IsOpenEmbedding (fᵢ i)) → IsOpenEmbedding f) ∧
     ((∀ i, IsQuotientMap (fᵢ i)) → IsQuotientMap f)) := by
  have hInject := (injective_iff_injective_of_iUnion_eq_univ (f := f) hU.iSup_set_eq_univ).mpr
  have hSurject := (surjective_iff_surjective_of_iUnion_eq_univ (f := f) hU.iSup_set_eq_univ).mpr
  refine ⟨hInject, hSurject, ?_, (hU.isClosedEmbedding_iff_restrictPreimage hf).mpr,
    (hU.isOpenEmbedding_iff_restrictPreimage hf).mpr, ?_⟩
  · intro h
    have hi : Injective f := hInject fun i a b hab => (h i).isEmbedding.injective (Subtype.ext hab)
    refine (cg_kelleyImage_criterion hf hi).mpr fun W _ _ a => ⟨fun ha => ?_, fun ha => hf.comp ha⟩
    let V (i : ι) : Set W := (f ∘ a) ⁻¹' (U i).1
    have hV (i : ι) : IsOpen (V i) := (U i).isOpen.preimage ha
    refine continuous_of_continuousOn_iUnion_of_isOpen (s := V) ?_ hV ?_
    · intro i
      letI := open_compactlyGenerated (hV i)
      let aᵢ : V i → f ⁻¹' (U i).1 := fun w => ⟨a w, w.property⟩
      have hcomp : Continuous ((U i).1.restrictPreimage f ∘ aᵢ) :=
        (ha.comp continuous_subtype_val).subtype_mk fun w => w.property
      have htest := (kelleyImageMap_detects (hf.restrictPreimage (s := (U i).1)) (h i) aᵢ).mp hcomp
      exact continuousOn_iff_continuous_domRestrict.mpr (continuous_subtype_val.comp htest)
    · rw [show (⋃ i, V i) = (f ∘ a) ⁻¹' (⋃ i, (U i : Set Y)) from preimage_iUnion.symm,
        hU.iSup_set_eq_univ, preimage_univ]
  · intro h
    refine ⟨.of_isOpen_preimage_iff_isOpen (fun s => ⟨fun hs => ?_, fun hs => hs.preimage hf⟩),
      hSurject fun i => (h i).surjective⟩
    apply hU.isOpen_iff_coe_preimage.mpr
    intro i
    exact (h i).isCoinducing.isOpen_preimage.mp (hs.preimage continuous_subtype_val)

/-- Corrected Lemma E.2.3.7. All six properties descend along a quotient
map, with the Kelley image topology in the general immersion clause. -/
theorem fibre_properties_descend {X Y T : CGWH.{u}} (f : X ⟶ Y) (g : T ⟶ Y)
    (hg : IsQuotientMap g.hom) :
    let p : FibreSubspace f g → T.obj := fun z => z.val.2
    (Injective p → Injective f.hom) ∧ (Surjective p → Surjective f.hom) ∧
    (IsHomeomorph (kelleyImageMap p) → IsHomeomorph (kelleyImageMap f.hom)) ∧
    (IsClosedEmbedding p → IsClosedEmbedding f.hom) ∧
    (IsOpenEmbedding p → IsOpenEmbedding f.hom) ∧
    (IsQuotientMap p → IsQuotientMap f.hom) := by
  let p : FibreSubspace f g → T.obj := fun z => z.val.2
  have hp : Continuous p := continuous_snd.comp (continuous_Kelley_forget.comp continuous_subtype_val)
  have hf := f.hom.hom.hom.continuous
  have hInject (hi : Injective p) : Injective f.hom := by
    intro x x' h
    obtain ⟨t, ht⟩ := hg.surjective (f.hom x)
    let z : FibreSubspace f g := ⟨(x, t), ht.symm⟩
    let z' : FibreSubspace f g := ⟨(x', t), h.symm.trans ht.symm⟩
    exact congrArg (fun v : FibreSubspace f g => v.val.1) (hi (show p z = p z' from rfl))
  have hSurject (hs : Surjective p) : Surjective f.hom := by
    intro y
    obtain ⟨t, ht⟩ := hg.surjective y
    obtain ⟨z, hz⟩ := hs t
    exact ⟨z.val.1, z.property.trans ((congrArg g.hom hz).trans ht)⟩
  have hImage (h : IsHomeomorph (kelleyImageMap p)) : IsHomeomorph (kelleyImageMap f.hom) := by
    have hi := hInject fun a b hab => h.isEmbedding.injective (Subtype.ext hab)
    apply (cgwh_kelleyImage_criterion Y.property hf hi).mpr
    intro W _ _ hW a
    refine ⟨fun ha => ?_, fun ha => hf.comp ha⟩
    let B := CGWH.of hW
    let b : B ⟶ Y := CGWH.map ⟨f.hom ∘ a, ha⟩
    let k : FibreSubspace g b → FibreSubspace f g := fun z =>
      ⟨(a z.val.2, z.val.1), z.property.symm⟩
    have hk : Continuous (p ∘ k) :=
      continuous_fst.comp (continuous_Kelley_forget.comp continuous_subtype_val)
    letI : CompactlyGeneratedSpace (FibreSubspace g b) :=
      closed_compactlyGenerated (fibreSubspace_isClosed g b)
    have hfst : Continuous (fun z : FibreSubspace f g => z.val.1) :=
      continuous_fst.comp (continuous_Kelley_forget.comp continuous_subtype_val)
    exact (quotient_baseChange g b hg).continuous_iff.mpr
      (hfst.comp ((kelleyImageMap_detects hp h k).mp hk))
  have hOrdinary (h : IsEmbedding p) [CompactlyGeneratedSpace (range f.hom)] : IsEmbedding f.hom := by
    apply isEmbedding_of_kelleyImage (hImage ((cg_kelleyImage_criterion hp h.injective).mpr ?_))
    exact fun _ _ _ k => h.isInducing.continuous_iff.symm
  refine ⟨hInject, hSurject, hImage, fun h => ?_, fun h => ?_, quotient_descends f g hg⟩
  · have hc : IsClosed (range f.hom) := hg.isCoinducing.isClosed_preimage.mp
      ((fibre_snd_range f g) ▸ h.isClosed_range)
    letI := closed_compactlyGenerated hc
    exact ⟨hOrdinary h.isEmbedding, hc⟩
  · have ho : IsOpen (range f.hom) := hg.isCoinducing.isOpen_preimage.mp
      ((fibre_snd_range f g) ▸ h.isOpen_range)
    letI := open_compactlyGenerated ho
    exact ⟨hOrdinary h.isEmbedding, ho⟩

end CGWH

end Masullo
