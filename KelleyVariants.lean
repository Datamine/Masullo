import CompactlyGenerated
import Mathlib.Analysis.Real.Cardinality
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.DiscreteSubset
import Mathlib.Topology.Instances.RatLemmas

open CategoryTheory Function Set Topology TopologicalSpace

namespace Masullo

universe u

/-- The compact-subspace test in Definition E.2.4.1(1). -/
def KelleySubspaceGenerated (X : Type u) [TopologicalSpace X] : Prop :=
  ∀ U : Set X, (∀ K : Set X, IsCompact K → IsOpen (Subtype.val ⁻¹' U : Set K)) → IsOpen U

/-- The compact Hausdorff subspace test in Definition E.2.4.1(2). -/
def SteenrodGenerated (X : Type u) [TopologicalSpace X] : Prop :=
  ∀ U : Set X, (∀ K : Set X, IsCompact K → T2Space K → IsOpen (Subtype.val ⁻¹' U : Set K)) →
    IsOpen U

private theorem preimage_open_of_compact_range {X K : Type*} [TopologicalSpace X]
    [TopologicalSpace K] [CompactSpace K] {g : K → X} (hg : Continuous g) {U : Set X}
    (h : IsOpen (Subtype.val ⁻¹' U : Set (range g))) : IsOpen (g ⁻¹' U) :=
  h.preimage (hg.subtype_mk mem_range_self)

/-- The four equivalent criteria in Lemma E.2.4.2. -/
theorem kelleySubspaceGenerated_criteria (X : Type u) [TopologicalSpace X] :
    let maps := ∀ (Y : Type u) [TopologicalSpace Y] (f : X → Y),
      Continuous f ↔ ∀ K : Set X, IsCompact K → Continuous (f ∘ (Subtype.val : K → X))
    let opens := ∀ U : Set X, IsOpen U ↔ ∀ (K : Type u) [TopologicalSpace K] [CompactSpace K]
      (g : K → X), Continuous g → IsOpen (g ⁻¹' U)
    let quotient := ∃ (I : Type u) (K : I → TopCat.{u}),
      (∀ i, CompactSpace (K i)) ∧ ∃ q : (Σ i, K i) → X, IsQuotientMap q
    (KelleySubspaceGenerated X ↔ maps) ∧ (KelleySubspaceGenerated X ↔ opens) ∧
      (KelleySubspaceGenerated X ↔ quotient) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro h Y _ f
    refine ⟨fun hf _ _ => hf.comp continuous_subtype_val, fun hK => continuous_def.mpr ?_⟩
    exact fun U hU => h (f ⁻¹' U) fun K hKc => hU.preimage (hK K hKc)
  · intro h U hU
    let f (x : X) : ULift.{u} Prop := ⟨x ∈ U⟩
    have hf : Continuous f := (h _ f).mpr fun K hK =>
      continuous_uliftUp.comp (isOpen_iff_continuous_mem.mp (hU K hK))
    exact isOpen_iff_continuous_mem.mpr (continuous_uliftDown.comp hf)
  · intro h U
    refine ⟨fun ho _ _ _ _ hg => ho.preimage hg, fun hK => h U fun K hKc => ?_⟩
    letI : CompactSpace K := isCompact_iff_compactSpace.mp hKc
    exact hK K Subtype.val continuous_subtype_val
  · intro h U hU
    refine (h U).mpr fun K _ _ g hg => preimage_open_of_compact_range hg ?_
    exact hU (range g) (isCompact_range hg)
  · intro h
    let I := {K : Set X // IsCompact K}
    let K (i : I) := TopCat.of i.val
    let q (p : Σ i, K i) : X := p.2.val
    refine ⟨I, K, fun i => isCompact_iff_compactSpace.mp i.property, q, ?_⟩
    refine ⟨.of_isOpen_preimage_iff_isOpen fun U => ?_, fun x => ?_⟩
    · refine ⟨fun hq => h U fun s hs => ?_, fun hU => ?_⟩
      · exact isOpen_sigma_iff.mp hq ⟨s, hs⟩
      · exact isOpen_sigma_iff.mpr fun i => hU.preimage continuous_subtype_val
    · exact ⟨⟨⟨{x}, isCompact_singleton⟩, ⟨x, mem_singleton x⟩⟩, rfl⟩
  · rintro ⟨I, K, hK, q, hq⟩ U hU
    apply hq.isCoinducing.isOpen_preimage.mp
    apply isOpen_sigma_iff.mpr
    intro i
    letI := hK i
    let g : K i → X := fun k => q ⟨i, k⟩
    have hg : Continuous g := hq.continuous.comp continuous_sigmaMk
    exact preimage_open_of_compact_range hg (hU (range g) (isCompact_range hg))

/-- The comparison implications of Lemma E.2.4.3. -/
theorem compact_generation_implications (X : Type u) [TopologicalSpace X] :
    (SteenrodGenerated X → CompactlyGeneratedSpace X) ∧
    (CompactlyGeneratedSpace X → KelleySubspaceGenerated X) := by
  refine ⟨fun h => compactlyGeneratedSpace_of_isOpen fun U hU => h U fun K hK hT => ?_,
    fun h U hU => ?_⟩
  · letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
    exact hU K Subtype.val continuous_subtype_val
  · apply UCompactlyGeneratedSpace.isOpen
    intro K g
    exact preimage_open_of_compact_range g.continuous (hU _ (isCompact_range g.continuous))

/-- Lemma E.2.4.8. The three compact-generation tests agree on a Hausdorff space. -/
theorem compact_generation_equiv_of_t2 (X : Type u) [TopologicalSpace X] [T2Space X] :
    (KelleySubspaceGenerated X ↔ CompactlyGeneratedSpace X) ∧
    (CompactlyGeneratedSpace X ↔ SteenrodGenerated X) := by
  have h : KelleySubspaceGenerated X → SteenrodGenerated X :=
    fun h U hU => h U fun K hK => hU K hK inferInstance
  obtain ⟨h₁, h₂⟩ := compact_generation_implications X
  exact ⟨⟨fun H => h₁ (h H), h₂⟩, ⟨fun H => h (h₂ H), h₁⟩⟩

/-- Lemma E.2.4.7. The Sierpinski topology on propositions separates the tests. -/
theorem sierpinski_compactlyGenerated_not_steenrod :
    CompactlyGeneratedSpace Prop ∧ ¬ SteenrodGenerated Prop := by
  classical
  constructor
  · letI : FirstCountableTopology Prop := ⟨fun p => by
      by_cases hp : p
      · rw [eq_true hp, nhds_true]
        infer_instance
      · rw [eq_false hp, nhds_false]
        infer_instance⟩
    infer_instance
  · intro h
    have hn : ¬ IsOpen ({False} : Set Prop) := by
      intro ho
      have hm := ho.mem_nhds (mem_singleton False)
      simp [nhds_false] at hm
    apply hn (h _ fun K _ _ => ?_)
    by_cases hF : False ∈ K
    · have hT : True ∉ K := by
        intro ht
        have hs : True ⤳ False := specializes_iff_nhds.mpr (nhds_false ▸ le_top)
        have hs' := (subtype_specializes_iff (⟨True, ht⟩ : K) ⟨False, hF⟩).mpr hs
        exact of_eq_false (congrArg Subtype.val hs'.eq) trivial
      have hAll : (Subtype.val ⁻¹' ({False} : Set Prop) : Set K) = univ := by
        ext ⟨p, hp⟩
        have hnp : ¬ p := fun h' => hT (eq_true h' ▸ hp)
        simp [eq_false hnp]
      rw [hAll]
      exact isOpen_univ
    · have hNone : (Subtype.val ⁻¹' ({False} : Set Prop) : Set K) = ∅ := by
        ext ⟨p, hp⟩
        exact ⟨fun h' => hF ((mem_singleton_iff.mp h') ▸ hp), False.elim⟩
      rw [hNone]
      exact isOpen_empty

/-- The real set with its cocountable topology. -/
def CocountableReal := ℝ

instance : TopologicalSpace CocountableReal where
  IsOpen s := s = ∅ ∨ sᶜ.Countable
  isOpen_univ := Or.inr (by simp)
  isOpen_inter s t hs ht := by
    rcases hs with rfl | hs
    · exact Or.inl (empty_inter t)
    rcases ht with rfl | ht
    · exact Or.inl (inter_empty s)
    · exact Or.inr (by simpa only [compl_inter] using hs.union ht)
  isOpen_sUnion S hS := by
    by_cases h : ⋃₀ S = ∅
    · exact Or.inl h
    · obtain ⟨x, s, hs, hxs⟩ := nonempty_iff_ne_empty.mpr h
      exact Or.inr (((hS s hs).resolve_left (nonempty_iff_ne_empty.mp ⟨x, hxs⟩)).mono
        (compl_subset_compl.mpr (subset_sUnion_of_mem hs)))

private theorem cocountable_closed {s : Set CocountableReal} (hs : s.Countable) : IsClosed s :=
  ⟨Or.inr (by simpa only [compl_compl] using hs)⟩

instance : T1Space CocountableReal := ⟨fun x => cocountable_closed (countable_singleton x)⟩

private theorem cocountable_compact_finite {s : Set CocountableReal} (hs : IsCompact s) : s.Finite := by
  by_contra h
  obtain ⟨t, hts, htc, hti⟩ := Infinite.exists_subset_countable_infinite h
  have htk := hs.of_isClosed_subset (cocountable_closed htc) hts
  apply hti
  refine htk.finite (isDiscrete_iff_forall_mem_exists_isOpen.mpr fun x hx => ?_)
  refine ⟨(t \ {x})ᶜ, (cocountable_closed (htc.mono sdiff_subset)).isOpen_compl, ?_⟩
  aesop

private theorem cocountable_not_kelley : ¬ KelleySubspaceGenerated CocountableReal := by
  intro h
  let x : CocountableReal := (0 : ℝ)
  have ho : IsOpen ({x} : Set CocountableReal) := by
    apply h
    intro K hK
    letI : Finite K := (cocountable_compact_finite hK).to_subtype
    haveI : DiscreteTopology K := Finite.instDiscreteTopology
    exact isOpen_discrete _
  change ({x} : Set CocountableReal) = ∅ ∨ ({x} : Set CocountableReal)ᶜ.Countable at ho
  have hx := ho.resolve_left (singleton_ne_empty x)
  have huniv : (univ : Set ℝ).Countable := by
    change (univ : Set CocountableReal).Countable
    simpa only [union_compl_self] using (countable_singleton x).union hx
  exact not_countable_univ huniv

private theorem kelley_of_compact {X : Type u} [TopologicalSpace X] [CompactSpace X] :
    KelleySubspaceGenerated X := by
  intro U hU
  obtain ⟨V, hV, he⟩ := isOpen_induced_iff.mp (hU univ isCompact_univ)
  have hval : Surjective (Subtype.val : (↑(univ : Set X) : Type u) → X) :=
    fun x => ⟨⟨x, mem_univ _⟩, rfl⟩
  exact (hval.preimage_injective he) ▸ hV

private theorem kelley_of_homeomorph {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (hX : KelleySubspaceGenerated X) : KelleySubspaceGenerated Y := by
  apply (kelleySubspaceGenerated_criteria Y).2.1.mpr
  intro U
  refine ⟨fun hU _ _ _ _ hg => hU.preimage hg, fun hU => ?_⟩
  have he : IsOpen (e ⁻¹' U) := ((kelleySubspaceGenerated_criteria X).2.1.mp hX _).mpr
    fun K _ _ g hg => hU K (e ∘ g) (e.continuous.comp hg)
  simpa only [image_preimage_eq _ e.surjective] using e.isOpenMap _ he

/-- Lemma E.2.4.12. The open cocountable subspace fails the compact-subspace test. -/
theorem kelleySubspaceGenerated_open_subspace_obstruction :
    let U := range ((↑) : CocountableReal → OnePoint CocountableReal)
    KelleySubspaceGenerated (OnePoint CocountableReal) ∧ IsOpen U ∧ ¬KelleySubspaceGenerated U := by
  refine ⟨kelley_of_compact, OnePoint.isOpen_range_coe, fun h => cocountable_not_kelley ?_⟩
  exact kelley_of_homeomorph OnePoint.isOpenEmbedding_coe.isEmbedding.toHomeomorph.symm h

/-- Lemma E.2.4.11. A compact space can fail compact Hausdorff generation. -/
theorem kelleySubspaceGenerated_not_compactlyGenerated :
    KelleySubspaceGenerated (OnePoint CocountableReal) ∧
      ¬CompactlyGeneratedSpace (OnePoint CocountableReal) := by
  obtain ⟨hk, hu, hnu⟩ := kelleySubspaceGenerated_open_subspace_obstruction
  exact ⟨hk, fun h => hnu ((compact_generation_implications _).2 (open_compactlyGenerated hu))⟩

section OnePointRational

open Filter OnePoint

private theorem onePoint_sequential {X : Type u} [TopologicalSpace X] [MetrizableSpace X] :
    SequentialSpace (OnePoint X) := by
  refine ⟨fun S hS => ?_⟩
  let inc : X → OnePoint X := OnePoint.some
  let A : Set X := inc ⁻¹' S
  have hA : IsClosed A := by
    apply isSeqClosed_iff_isClosed.mp
    intro x a hseq hlim
    exact hS hseq (OnePoint.continuous_coe.continuousAt.tendsto.comp hlim)
  by_cases hi : (∞ : OnePoint X) ∈ S
  · exact (OnePoint.isClosed_iff_of_mem hi).mpr hA
  refine (OnePoint.isClosed_iff_of_notMem hi).mpr ⟨hA, IsSeqCompact.isCompact ?_⟩
  intro x hx
  by_contra hsub
  have hescape (K : Set X) (hK : IsCompact K) : ∀ᶠ n in atTop, x n ∉ K := by
    by_contra h
    have hfreq : ∃ᶠ n in atTop, x n ∈ K := h
    obtain ⟨φ, hφ, hmem⟩ := extraction_of_frequently_atTop hfreq
    obtain ⟨y, _, ψ, hψ, hlim⟩ := hK.isSeqCompact hmem
    exact hsub ⟨y, hA.mem_of_tendsto hlim (.of_forall fun n => hx (φ (ψ n))),
      φ ∘ ψ, hφ.comp hψ, hlim⟩
  have hco : Tendsto x atTop (coclosedCompact X) :=
    hasBasis_coclosedCompact.tendsto_right_iff.mpr fun K hK => hescape K hK.2
  exact hi (hS hx (OnePoint.tendsto_coe_infty.comp hco))

private theorem onePoint_weaklyHausdorff {X : Type u} [TopologicalSpace X] [T2Space X]
    [FirstCountableTopology X] : WeaklyHausdorff (OnePoint X) := by
  intro K f
  let inc : X → OnePoint X := OnePoint.some
  have he : IsEmbedding inc := OnePoint.isOpenEmbedding_coe.isEmbedding
  have hpreCompact {S : Set (OnePoint X)} (hS : IsCompact S) (hr : S ⊆ range inc) :
      IsCompact (inc ⁻¹' S) :=
    he.isCompact_iff.mpr ((image_preimage_eq_of_subset hr).symm ▸ hS)
  by_cases hi : (∞ : OnePoint X) ∈ range f
  · apply (OnePoint.isClosed_iff_of_mem hi).mpr
    apply isSeqClosed_iff_isClosed.mp
    intro x a hx ha
    let C := insert a (range x)
    let W := f ⁻¹' (inc '' C)
    have hC : IsCompact C := ha.isCompact_insert_range
    have hW : IsCompact W := ((OnePoint.isClosed_image_coe.mpr ⟨hC.isClosed, hC⟩).preimage
      f.continuous).isCompact
    have hr : f '' W ⊆ range inc := fun _ ⟨k, hk, heq⟩ =>
      heq ▸ (image_subset_range inc C hk : f k ∈ range inc)
    have hc : IsClosed (inc ⁻¹' (f '' W)) := (hpreCompact (hW.image f.continuous) hr).isClosed
    have hseq (n : ℕ) : x n ∈ inc ⁻¹' (f '' W) := by
      obtain ⟨k, hk⟩ := hx n
      exact ⟨k, by rw [mem_preimage, hk]; exact mem_image_of_mem inc (Or.inr (mem_range_self n)), hk⟩
    exact image_subset_range f W (hc.mem_of_tendsto ha (.of_forall hseq))
  · have hr : range f ⊆ range inc := fun z hz =>
      (OnePoint.ne_infty_iff_exists.mp fun hz' => hi (hz' ▸ hz))
    have hc := hpreCompact (isCompact_range f.continuous) hr
    exact (OnePoint.isClosed_iff_of_notMem hi).mpr ⟨hc.isClosed, hc⟩

/-- Lemma E.2.4.5. The one-point compactification of the rationals has
the three stated properties and is not Hausdorff. -/
theorem rational_onePoint_compactlyGenerated_weaklyHausdorff :
    CompactSpace (OnePoint ℚ) ∧ CompactlyGeneratedSpace (OnePoint ℚ) ∧
      WeaklyHausdorff (OnePoint ℚ) ∧ ¬T2Space (OnePoint ℚ) := by
  letI : SequentialSpace (OnePoint ℚ) := onePoint_sequential
  refine ⟨inferInstance, inferInstance, onePoint_weaklyHausdorff, fun h => ?_⟩
  obtain ⟨U, V, hU, hV, h0, hi, hd⟩ := t2_separation (OnePoint.coe_ne_infty (0 : ℚ))
  let C : Set ℚ := (OnePoint.some : ℚ → OnePoint ℚ) ⁻¹' Vᶜ
  have hC : IsCompact C := (OnePoint.isOpen_iff_of_mem hi).mp hV |>.2
  have h0C : (0 : ℚ) ∈ interior C := mem_interior_iff_mem_nhds.mpr <|
    mem_of_superset ((hU.preimage OnePoint.continuous_coe).mem_nhds h0) fun x hx hy =>
      (Set.disjoint_left.mp hd) hx hy
  rw [Rat.interior_compact_eq_empty hC] at h0C
  exact h0C

/-- Lemma E.2.4.9. The ordinary square of this space fails compact generation. -/
theorem rational_onePoint_product_not_compactlyGenerated :
    CompactSpace (OnePoint ℚ) ∧ CompactlyGeneratedSpace (OnePoint ℚ) ∧
      WeaklyHausdorff (OnePoint ℚ) ∧ ¬T2Space (OnePoint ℚ) ∧
      ¬CompactlyGeneratedSpace (OnePoint ℚ × OnePoint ℚ) := by
  obtain ⟨hK, hCG, hWH, hT⟩ := rational_onePoint_compactlyGenerated_weaklyHausdorff
  exact ⟨hK, hCG, hWH, hT, fun h => hT (t2_iff_isClosed_diagonal.mpr
    (UCompactlyGeneratedSpace.isClosed (weaklyHausdorff_kelleyClosedDiagonal hWH)))⟩

end OnePointRational

end Masullo
