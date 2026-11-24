import CompactlyGenerated
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Instances.Real.Lemmas

open Function Set Topology OnePoint
open scoped Topology

universe u

namespace Masullo

variable {X : Type u} [TopologicalSpace X]

private theorem open_of_avoids_point {x : X}
    (hx : ∀ A : Set X, x ∈ A → IsClosed A) {U : Set X} (hU : x ∉ U) :
    IsOpen U := by
  simpa using (hx Uᶜ hU).isOpen_compl

/-- The two-point hypothesis of E.1.1.4 forces all singletons to be open. -/
theorem discrete_of_two_closed_superset_points {x y : X} (hxy : x ≠ y)
    (hx : ∀ A : Set X, x ∈ A → IsClosed A)
    (hy : ∀ A : Set X, y ∈ A → IsClosed A) :
    DiscreteTopology X ∧ KelleyTestMaps X ∧ KelleyTestFamily X ∧
      KelleyTestOpen X ∧ KelleyTestQuotient X := by
  have hd : DiscreteTopology X := discreteTopology_iff_isOpen_singleton.mpr fun z => by
    by_cases h : z = x
    · subst z
      exact open_of_avoids_point hy (by simpa using hxy.symm)
    · exact open_of_avoids_point hx (by simpa using Ne.symm h)
  letI : DiscreteTopology X := hd
  obtain ⟨hm, hf, ho, hq⟩ := kelley_criteria X
  exact ⟨hd, hm.mpr inferInstance, hf.mpr inferInstance, ho.mpr inferInstance, hq.mpr inferInstance⟩

private theorem isolated_subspace_of_closed_supersets {x : X}
    (hx : ∀ A : Set X, x ∈ A → IsClosed A) :
    IsOpen ({x}ᶜ : Set X) ∧ DiscreteTopology ({x}ᶜ : Set X) := by
  refine ⟨(hx {x} (mem_singleton x)).isOpen_compl, discreteTopology_iff_isOpen_singleton.mpr ?_⟩
  intro z
  have hz : IsOpen ({z.1} : Set X) := open_of_avoids_point hx (by
    have h : z.1 ≠ x := z.property
    simpa using Ne.symm h)
  have he : Subtype.val ⁻¹' ({z.1} : Set X) = ({z} : Set ({x}ᶜ : Set X)) := by
    ext w
    exact Subtype.ext_iff.symm
  rw [← he]
  exact hz.preimage continuous_subtype_val

private theorem closed_singleton_of_not_mem_component {x y : X}
    (hx : ∀ A : Set X, x ∈ A → IsClosed A) (hy : y ∉ connectedComponent x) :
    IsClosed ({y} : Set X) := by
  have hnot : x ∉ closure ({y} : Set X) := by
    intro h
    exact hy (isPreconnected_singleton.closure.subset_connectedComponent h (subset_closure (mem_singleton y)))
  have hsub : closure ({y} : Set X) ⊆ {y} := by
    have hbound : closure ({y} : Set X) ⊆ {x, y} :=
      closure_minimal (by simp) (hx _ (by simp))
    intro z hz
    rcases mem_insert_iff.mp (hbound hz) with rfl | h
    · exact (hnot hz).elim
    · exact h
  rw [← closure_eq_iff_isClosed]
  exact Subset.antisymm hsub subset_closure

private abbrev ComponentRemainder (x : X) := closure ((connectedComponent x)ᶜ)

private theorem componentRemainder_subset {x : X}
    (hx : ∀ A : Set X, x ∈ A → IsClosed A) :
    ComponentRemainder x ⊆ insert x (connectedComponent x)ᶜ :=
  closure_minimal (subset_insert x _) (hx _ (mem_insert x _))

private theorem componentRemainder_t2 {x : X} (hx : ∀ A : Set X, x ∈ A → IsClosed A) :
    T2Space (ComponentRemainder x) := by
  apply t2Space_iff_disjoint_nhds.mpr
  intro p q hpq
  have hcl (z : ComponentRemainder x) (hz : z.1 ≠ x) : IsClopen ({z} : Set (ComponentRemainder x)) := by
    have hz' : z.1 ∉ connectedComponent x :=
      (mem_insert_iff.mp (componentRemainder_subset hx z.property)).resolve_left hz
    have he : Subtype.val ⁻¹' ({z.1} : Set X) = ({z} : Set (ComponentRemainder x)) := by
      ext w
      exact Subtype.ext_iff.symm
    rw [← he]
    exact ⟨(closed_singleton_of_not_mem_component hx hz').preimage continuous_subtype_val,
      (open_of_avoids_point hx (by simpa using Ne.symm hz)).preimage continuous_subtype_val⟩
  have sep (a b : ComponentRemainder x) (hab : a ≠ b) (ha : a.1 ≠ x) :
      Disjoint (nhds a) (nhds b) := by
    have h := hcl a ha
    exact Filter.disjoint_of_disjoint_of_mem disjoint_compl_right
      (h.2.mem_nhds (mem_singleton a)) (h.1.isOpen_compl.mem_nhds (by simpa using hab.symm))
  by_cases hp : p.1 = x
  · have hq : q.1 ≠ x := fun hq => hpq (Subtype.ext (hp.trans hq.symm))
    exact (sep q p hpq.symm hq).symm
  · exact sep p q hpq hp

private def componentAndRemainderMap (x : X) :
    connectedComponent x ⊕ ComponentRemainder x → X :=
  Sum.elim Subtype.val Subtype.val

private theorem componentAndRemainderMap_quotient {x : X} :
    IsQuotientMap (componentAndRemainderMap x) := by
  have hcover : connectedComponent x ∪ ComponentRemainder x = univ := by
    apply eq_univ_of_forall
    intro y
    by_cases hy : y ∈ connectedComponent x
    · exact Or.inl hy
    · exact Or.inr (subset_closure hy)
  apply isQuotientMap_iff_isClosed.mpr
  refine ⟨?_, fun A => ⟨?_, ?_⟩⟩
  · intro y
    rcases (show y ∈ connectedComponent x ∪ ComponentRemainder x by rw [hcover]; trivial) with hy | hy
    · exact ⟨Sum.inl ⟨y, hy⟩, rfl⟩
    · exact ⟨Sum.inr ⟨y, hy⟩, rfl⟩
  · intro hA
    exact isClosed_sum_iff.mpr ⟨hA.preimage continuous_subtype_val, hA.preimage continuous_subtype_val⟩
  · intro h
    obtain ⟨h₁, h₂⟩ := isClosed_sum_iff.mp h
    have hc₁ := isClosed_connectedComponent.isClosedEmbedding_subtypeVal.isClosedMap _ h₁
    have hc₂ := isClosed_closure.isClosedEmbedding_subtypeVal.isClosedMap _ h₂
    convert hc₁.union hc₂ using 1
    ext y
    simp only [mem_union, mem_image, mem_preimage]
    constructor
    · intro hy
      rcases (show y ∈ connectedComponent x ∪ ComponentRemainder x by rw [hcover]; trivial) with hyZ | hyV
      · exact Or.inl ⟨⟨y, hyZ⟩, hy, rfl⟩
      · exact Or.inr ⟨⟨y, hyV⟩, hy, rfl⟩
    · rintro (⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩) <;> exact hz


private abbrev componentCenter (x : X) : connectedComponent x := ⟨x, mem_connectedComponent⟩

private abbrev componentPunctures (x : X) := {z : connectedComponent x // z ≠ componentCenter x}

private def componentCompactMap (x : X) :
    OnePoint (Σ _ : componentPunctures x, ℝ) → connectedComponent x
  | .infty => componentCenter x
  | .some p => p.1.1

private theorem componentCompactMap_quotient {x : X}
    (hx : ∀ A : Set X, x ∈ A → IsClosed A) :
    IsQuotientMap (componentCompactMap x) := by
  classical
  let c := componentCenter x
  let q := componentCompactMap x
  have hinfty : q ∞ = c := rfl
  have hclosed {A : Set (connectedComponent x)} (hA : c ∈ A) : IsClosed A := by
    have hA' : x ∈ Subtype.val '' A := ⟨c, hA, rfl⟩
    have h := (hx (Subtype.val '' A) hA').preimage
      (continuous_subtype_val : Continuous (Subtype.val : connectedComponent x → X))
    simpa [preimage_image_eq _ Subtype.val_injective] using h
  letI : PreconnectedSpace (connectedComponent x) :=
    isPreconnected_iff_preconnectedSpace.mp isPreconnected_connectedComponent
  have hcont : Continuous q := by
    rw [continuous_def]
    intro A hA
    by_cases h : c ∈ A
    · have ht : A = univ := (show IsClopen A from ⟨hclosed h, hA⟩).eq_univ ⟨c, h⟩
      rw [ht, preimage_univ]
      exact isOpen_univ
    · apply (OnePoint.isOpen_iff_of_notMem (show ∞ ∉ q ⁻¹' A from h)).mpr
      apply isOpen_sigma_iff.mpr
      intro i
      have he : Sigma.mk i ⁻¹' (OnePoint.some ⁻¹' (q ⁻¹' A)) =
          (fun _ : ℝ => i.1) ⁻¹' A := rfl
      rw [he]
      exact hA.preimage continuous_const
  apply isQuotientMap_iff_isClosed.mpr
  refine ⟨?_, fun A => ⟨fun h => h.preimage hcont, ?_⟩⟩
  · intro z
    by_cases hz : z = c
    · exact ⟨∞, hinfty.trans hz.symm⟩
    · exact ⟨OnePoint.some ⟨⟨z, hz⟩, 0⟩, rfl⟩
  · intro hA
    by_cases hc : c ∈ A
    · exact hclosed hc
    · have hcompact := ((OnePoint.isClosed_iff_of_notMem (show ∞ ∉ q ⁻¹' A from hc)).mp hA).2
      have hempty : A = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro y hy
        have hyc : y ≠ c := fun he => hc (he ▸ hy)
        let i : componentPunctures x := ⟨y, hyc⟩
        let v : ℝ → (Σ _ : componentPunctures x, ℝ) := fun t => ⟨i, t⟩
        have hv : IsClosedEmbedding v := IsClosedEmbedding.sigmaMk (σ := fun _ : componentPunctures x => ℝ)
        have hu : v ⁻¹' (OnePoint.some ⁻¹' (q ⁻¹' A)) = univ := eq_univ_of_forall fun _ => hy
        have hk := hv.isCompact_preimage hcompact
        rw [hu] at hk
        exact (not_compactSpace_iff.mpr (inferInstance : NoncompactSpace ℝ)) (isCompact_univ_iff.mp hk)
      rw [hempty]
      exact isClosed_empty

private theorem componentRemainder_compactImage {x : X}
    (hx : ∀ A : Set X, x ∈ A → IsClosed A) (K : CompHaus.{u}) (g : C(K, ComponentRemainder x)) :
    IsClosed (range g) ∧ CompactSpace (range g) ∧ T2Space (range g) ∧
      IsQuotientMap (rangeFactorization g) := by
  letI : T2Space (ComponentRemainder x) := componentRemainder_t2 hx
  have h := isCompact_range g.continuous
  letI : CompactSpace (range g) := isCompact_iff_compactSpace.mp h
  exact ⟨h.isClosed, inferInstance, inferInstance,
    IsQuotientMap.of_surjective_continuous Set.rangeFactorization_surjective
      (g.continuous.subtype_mk _)⟩

/-- Lemma E.1.1.4(2). The connected component is a quotient of a compact
Hausdorff space, and the closed remainder is Hausdorff. -/
theorem closed_superset_point_bouquet {x : X} (hx : ∀ A : Set X, x ∈ A → IsClosed A) :
    (IsOpen ({x}ᶜ : Set X) ∧ DiscreteTopology ({x}ᶜ : Set X)) ∧
    IsQuotientMap (componentAndRemainderMap x) ∧
    (∀ (K : CompHaus.{u}) (g : C(K, ComponentRemainder x)),
      IsClosed (range g) ∧ CompactSpace (range g) ∧ T2Space (range g) ∧
        IsQuotientMap (rangeFactorization g)) ∧
    (∃ (K : CompHaus.{u}) (q : K → connectedComponent x), IsQuotientMap q) ∧
    (KelleyTestMaps X → KelleyTestFamily X) := by
  refine ⟨isolated_subspace_of_closed_supersets hx, componentAndRemainderMap_quotient,
    componentRemainder_compactImage hx, ?_, fun h => (kelley_criteria X).2.1.mpr
      ((kelley_criteria X).1.mp h)⟩
  let D := Σ _ : componentPunctures x, ℝ
  letI : WeaklyLocallyCompactSpace D := ⟨fun p => by
    obtain ⟨K, hK, hmem⟩ := exists_compact_mem_nhds p.2
    let v : ℝ → D := fun t => ⟨p.1, t⟩
    have hv : IsOpenEmbedding v := IsOpenEmbedding.sigmaMk (σ := fun _ : componentPunctures x => ℝ)
    exact ⟨v '' K, hK.image hv.continuous, hv.map_nhds_eq p.2 ▸ Filter.image_mem_map hmem⟩⟩
  exact ⟨CompHaus.of (OnePoint D), componentCompactMap x, componentCompactMap_quotient hx⟩

end Masullo
