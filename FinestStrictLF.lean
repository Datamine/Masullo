import FinestSubspaces
import FinestTensor

open Bornology Filter Function Module Set Topology

namespace Masullo

noncomputable section

variable {I E : Type*} [AddCommGroup E] [Module ℂ E]

private def basisStage (b : Basis I ℂ E) (j : I ↪ ℕ) (n : ℕ) : Submodule ℂ E :=
  Submodule.span ℂ (b '' {i | j i < n})

private theorem stage_indices_finite (j : I ↪ ℕ) (n : ℕ) :
    {i | j i < n}.Finite :=
  (Set.finite_Iio n).preimage_embedding j

private theorem basisStage_finite (b : Basis I ℂ E) (j : I ↪ ℕ) (n : ℕ) :
    FiniteDimensional ℂ (basisStage b j n) :=
  FiniteDimensional.span_of_finite ℂ ((stage_indices_finite j n).image b)

private theorem basisStage_mono (b : Basis I ℂ E) (j : I ↪ ℕ) :
    Monotone (basisStage b j) :=
  fun _ _ h => Submodule.span_mono (Set.image_mono (fun _ hi => lt_of_lt_of_le hi h))

private theorem finite_indices_one_stage (j : I ↪ ℕ) {S : Set I} (hS : S.Finite) :
    ∃ n : ℕ, S ⊆ {i | j i < n} := by
  obtain ⟨m, hm⟩ := (hS.image j).bddAbove
  exact ⟨m + 1, fun i hi => Nat.lt_succ_of_le (hm (mem_image_of_mem j hi))⟩

private theorem basisStage_exhaust (b : Basis I ℂ E) (j : I ↪ ℕ) (x : E) :
    ∃ n, x ∈ basisStage b j n := by
  obtain ⟨n, hn⟩ := finite_indices_one_stage j (b.repr x).support.finite_toSet
  exact ⟨n, b.mem_span_image.mpr hn⟩

/-- An increasing sequence of finite-dimensional closed subspaces presents
the finest topology as a strict locally convex inductive limit. -/
theorem finest_strictLF (b : Basis I ℂ E) (j : I ↪ ℕ) :
    letI : TopologicalSpace E := finestLocallyConvexTopology E
    ∃ P : ℕ → Submodule ℂ E, Monotone P ∧ (∀ x : E, ∃ n, x ∈ P n) ∧
      (∀ n, FiniteDimensional ℂ (P n)) ∧
      (∀ n, IsClosed (P n : Set E) ∧ IsEmbedding ((P n).subtype : P n → E)) ∧
      (∀ (m n : ℕ) (_h : m ≤ n) (h' : P m ≤ P n),
        IsClosedEmbedding (Submodule.inclusion h' : P m → P n)) ∧
      locallyConvexFinalTopology (fun n => (P n).subtype) = finestLocallyConvexTopology E := by
  letI : TopologicalSpace E := finestLocallyConvexTopology E
  let P := basisStage b j
  refine ⟨P, basisStage_mono b j, basisStage_exhaust b j, basisStage_finite b j, ?_, ?_,
    finest_submodule_family_final P⟩
  · exact fun n => ⟨(finest_submodule_quotient (P n)).2.1, IsEmbedding.subtypeVal⟩
  · intro m n _ h
    have hclosed : IsClosed (P m : Set E) := (finest_submodule_quotient (P m)).2.1
    have he : IsEmbedding (Submodule.inclusion h : P m → P n) :=
      (IsEmbedding.of_comp_iff (g := (Subtype.val : P n → E)) IsEmbedding.subtypeVal).mp
        IsEmbedding.subtypeVal
    refine ⟨he, ?_⟩
    have hr : range (Submodule.inclusion h : P m → P n) = (Subtype.val : P n → E) ⁻¹' P m := by
      ext x
      constructor
      · rintro ⟨y, rfl⟩
        exact y.property
      · intro hx
        exact ⟨⟨x.val, hx⟩, Subtype.ext rfl⟩
    rw [hr]
    exact hclosed.preimage continuous_subtype_val

private theorem finest_bounded_one_basisStage (b : Basis I ℂ E) (j : I ↪ ℕ) {B : Set E} :
    letI : TopologicalSpace E := finestLocallyConvexTopology E
    IsVonNBounded ℂ B → ∃ n, B ⊆ basisStage b j n := by
  letI : TopologicalSpace E := finestLocallyConvexTopology E
  let W := finest_withSeminorms E
  letI : IsTopologicalAddGroup E := W.topologicalAddGroup
  letI : ContinuousSMul ℂ E := W.continuousSMul
  letI : TopologicalSpace (I →₀ ℂ) := finestLocallyConvexTopology _
  letI : PolynormableSpace ℂ (I →₀ ℂ) := (finest_withSeminorms _).toPolynormableSpace
  intro hB
  let L : E →L[ℂ] (I →₀ ℂ) := ⟨b.repr.toLinearMap, finest_linear_continuous _⟩
  have hf : {i | ∃ x ∈ L '' B, x i ≠ 0}.Finite :=
    finest_finsupp_bounded_support (hB.image L)
  obtain ⟨n, hn⟩ := finite_indices_one_stage j hf
  refine ⟨n, fun x hx => b.mem_span_image.mpr (fun i hi => hn ?_)⟩
  exact ⟨L x, mem_image_of_mem L hx, Finsupp.mem_support_iff.mp hi⟩

/-- For infinite countable dimension, the finest topology is never
first-countable. The putative countable base would produce a convergent
sequence that escapes every finite stage, contradicting boundedness. -/
theorem finest_not_firstCountable (b : Basis I ℂ E) (j : I ↪ ℕ) [Infinite I] :
    ¬ @FirstCountableTopology E (finestLocallyConvexTopology E) := by
  letI : TopologicalSpace E := finestLocallyConvexTopology E
  let W := finest_withSeminorms E
  letI : IsTopologicalAddGroup E := W.topologicalAddGroup
  letI : ContinuousSMul ℂ E := W.continuousSMul
  intro h
  letI : FirstCountableTopology E := h
  let P := basisStage b j
  have hproper (n : ℕ) : P n ≠ ⊤ := by
    intro hP
    obtain ⟨i, hi⟩ := (stage_indices_finite j n).exists_notMem
    have hb : b i ∈ P n := by simp [hP]
    have he := b.mem_span_image.mp hb
    exact hi (he (by simp))
  obtain ⟨U, hU⟩ := (𝓝 (0 : E)).exists_antitone_basis
  have hex (n : ℕ) : ∃ x ∈ U n, x ∉ P n := by
    by_contra! hsub
    have hP : (P n : Set E) ∈ 𝓝 (0 : E) :=
      mem_of_superset (hU.1.mem_of_mem trivial) hsub
    exact hproper n ((P n).eq_top_of_nonempty_interior'
      ⟨0, mem_interior_iff_mem_nhds.mpr hP⟩)
  choose x hx hnot using hex
  have hlim : Tendsto x atTop (𝓝 (0 : E)) := hU.tendsto hx
  obtain ⟨n, hn⟩ := finest_bounded_one_basisStage b j (hlim.isVonNBounded_range ℂ)
  exact hnot n (hn (mem_range_self n))

end
end Masullo
