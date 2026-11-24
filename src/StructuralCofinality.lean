/-
The compact exhaustion and shrinking-kernel argument adapts the Apache-2.0
RiemannMasullo project at 3b4b2cd6915a243a5299a26001ca6b1c1a2ed037.
See External/PROVENANCE.md and External/RiemannMasullo.LICENSE.
-/
import StructuralPairs

open Filter Set Topology

namespace Masullo

noncomputable section

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]

/-- The structural pairs of a second-countable LCA group admit a monotone
cofinal sequence. A compact exhaustion controls the upper subgroups. Shrinking
identity neighborhoods control the kernels through the elementary quotients. -/
theorem lcaStructuralPairs_cofinalSequence :
    ∃ b : ℕ → LCAStructuralPair G, Monotone b ∧ ∀ a, ∃ n, a ≤ b n := by
  classical
  let C := CompactExhaustion.choice G
  obtain ⟨U, hU⟩ := (𝓝 (1 : G)).exists_antitone_basis
  choose H hH using fun n ↦ exists_openCompactlyGeneratedSubgroup_contains (C.isCompact n)
  choose A hA using fun n ↦ exists_lcaDualAnnihilator_subset_nhds
    (inter_mem (hU.mem n) ((H n).property.1.mem_nhds (H n).val.one_mem))
  let K (n : ℕ) := lcaDualAnnihilator (A n).val
  let b (n : ℕ) : LCAStructuralPair G :=
    LCAStructuralPair.ofDual (H n) (A n) (fun _ hx ↦ (hA n hx).2)
  have hCofinal (a : LCAStructuralPair G) : ∃ n, a ≤ b n := by
    obtain ⟨D, _, hDc, hDgen⟩ := a.upper.property.2
    obtain ⟨m, hm⟩ := C.exists_superset_of_isCompact (hDc.image continuous_subtype_val)
    let J := a.upper.val
    let K₀ := a.kernel.comap J.subtype
    let Q := J ⧸ K₀
    letI : LocallyCompactSpace J := a.upper.property.1.locallyCompactSpace
    letI : T1Space Q :=
      QuotientGroup.t1Space_iff.mpr (a.kernel_closed.preimage continuous_subtype_val)
    letI : LocallyCompactSpace Q :=
      (QuotientGroup.isOpenQuotientMap_mk (N := K₀)).locallyCompactSpace
    have hE : IsLocallyEuclidean Q := (lca_elementary_iff.mpr a.quotient_elementary).2
    obtain ⟨W, hW, hPow⟩ := exists_nhds_one_of_isLocallyEuclidean hE
    let π : J →* Q := QuotientGroup.mk' K₀
    have hPre : π ⁻¹' W ∈ 𝓝 (1 : J) :=
      (QuotientGroup.continuous_mk (N := K₀) : Continuous π).continuousAt.preimage_mem_nhds
        (by change W ∈ 𝓝 (π 1); rwa [map_one])
    have hImage : Subtype.val '' (π ⁻¹' W) ∈ 𝓝 (1 : G) :=
      a.upper.property.1.isOpenEmbedding_subtypeVal.isOpenMap.image_mem_nhds hPre
    obtain ⟨l, _, hl⟩ := hU.1.mem_iff.mp hImage
    let n := max m l
    refine ⟨n, ?_, ?_⟩
    · have hD : D ⊆ ((H n).val.comap J.subtype : Set J) :=
        fun x hx ↦ hH n (C.subset (le_max_left m l) (hm ⟨x, hx, rfl⟩))
      have htop : ⊤ ≤ (H n).val.comap J.subtype :=
        hDgen ▸ (Subgroup.closure_le _).mpr hD
      exact fun x hx ↦ htop (Subgroup.mem_top ⟨x, hx⟩)
    · have hSmall : (K n : Set G) ⊆ Subtype.val '' (π ⁻¹' W) :=
        fun _ hx ↦ hl (hU.2 (le_max_right m l) (hA n hx).1)
      intro x hx
      obtain ⟨y, _, rfl⟩ := hSmall hx
      change y ∈ K₀
      apply (QuotientGroup.eq_one_iff y).mp
      change π y = 1
      apply hPow
      intro k
      rw [← map_pow]
      obtain ⟨z, hz, hzy⟩ := hSmall ((K n).pow_mem hx k)
      exact (Subtype.ext hzy : z = y ^ k) ▸ hz
  letI := (lcaStructuralPairs_filtered (G := G)).2
  choose upper hleft hright using (exists_ge_ge (α := LCAStructuralPair G))
  let chain : ℕ → LCAStructuralPair G :=
    Nat.rec (b 0) fun n prev ↦ upper prev (b (n + 1))
  have hdom (n : ℕ) : b n ≤ chain n := by
    cases n with
    | zero => exact le_rfl
    | succ n => exact hright (chain n) (b (n + 1))
  exact ⟨chain, monotone_nat_of_le_succ fun n ↦ hleft (chain n) (b (n + 1)), fun a ↦ by
    obtain ⟨n, hn⟩ := hCofinal a
    exact ⟨n, hn.trans (hdom n)⟩⟩

end
end Masullo
