/-
Adapted from RiemannMasullo/AppD_SchwartzBruhat/Sec1b.lean at
db376192baf52253727c46e2b211619d4e6a3941 (Apache-2.0).
See External/PROVENANCE.md and External/RiemannMasullo.LICENSE.
-/
import PontryaginAnnihilators
import PontryaginBidual
import Mathlib.Topology.Connected.Clopen

open Filter Function Set Topology
open scoped Pointwise

namespace Masullo

/-- Compact generation by a compact neighborhood of the identity. -/
def IsCompactlyGeneratedGroup (G : Type*) [Group G] [TopologicalSpace G] : Prop :=
  ∃ K : Set G, K ∈ 𝓝 1 ∧ IsCompact K ∧ Subgroup.closure K = ⊤

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G]

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] in
/-- Open compactly generated subgroups, ordered by inclusion. -/
abbrev OpenCompactlyGeneratedSubgroups (G : Type*) [CommGroup G] [TopologicalSpace G] :=
  {H : Subgroup G // IsOpen (H : Set G) ∧ IsCompactlyGeneratedGroup H}

omit [T2Space G] in
/-- Paper: (D.1.4.3), p. 758. The open compactly generated subgroups are filtered
and cover the group. The topology is final for their open inclusions. -/
theorem openCompactlyGeneratedSubgroups_colimit :
    IsDirectedOrder (OpenCompactlyGeneratedSubgroups G) ∧
      (∀ x : G, ∃ H : OpenCompactlyGeneratedSubgroups G, x ∈ H.val) ∧
      (∀ U : Set G, IsOpen U ↔
        ∀ H : OpenCompactlyGeneratedSubgroups G, IsOpen (Subtype.val ⁻¹' U : Set H.val)) := by
  let ofCompactNeighborhood (K : Set G) (hK : IsCompact K) (hKnhds : K ∈ 𝓝 (1 : G)) :
      OpenCompactlyGeneratedSubgroups G := by
    let H := Subgroup.closure K
    have hH : IsOpen (H : Set G) := H.isOpen_of_mem_nhds
      (mem_of_superset hKnhds Subgroup.subset_closure)
    exact ⟨H, hH, Subtype.val ⁻¹' K,
      continuous_subtype_val.continuousAt.preimage_mem_nhds hKnhds,
      (H.isClosed_of_isOpen hH).isClosedEmbedding_subtypeVal.isCompact_preimage hK,
      Subgroup.closure_preimage_eq_top K⟩
  have hCover (x : G) : ∃ H : OpenCompactlyGeneratedSubgroups G, x ∈ H.val := by
    obtain ⟨K, hK, hKnhds⟩ := exists_compact_mem_nhds (1 : G)
    exact ⟨ofCompactNeighborhood (insert x K) (hK.insert x)
      (mem_of_superset hKnhds (subset_insert x K)), Subgroup.subset_closure (mem_insert x K)⟩
  refine ⟨⟨?_⟩, hCover, ?_⟩
  · intro H J
    obtain ⟨A, hAnhds, hA, hAgen⟩ := H.property.2
    obtain ⟨B, _, hB, hBgen⟩ := J.property.2
    have hAnhds' : H.val.subtype '' A ∈ 𝓝 (1 : G) :=
      H.property.1.isOpenEmbedding_subtypeVal.isOpenMap.image_mem_nhds hAnhds
    let L := ofCompactNeighborhood (H.val.subtype '' A ∪ J.val.subtype '' B)
      ((hA.image continuous_subtype_val).union (hB.image continuous_subtype_val))
      (mem_of_superset hAnhds' subset_union_left)
    have hL : L.val = H.val ⊔ J.val := by
      change Subgroup.closure (H.val.subtype '' A ∪ J.val.subtype '' B) = _
      rw [Subgroup.closure_union, ← MonoidHom.map_closure, ← MonoidHom.map_closure,
        hAgen, hBgen]
      congr 1 <;> ext x <;> simp
    exact ⟨L, le_sup_left.trans hL.ge, le_sup_right.trans hL.ge⟩
  · intro U
    refine ⟨fun hU H ↦ hU.preimage continuous_subtype_val, ?_⟩
    intro hU
    refine isOpen_iff_mem_nhds.mpr fun x hx ↦ ?_
    obtain ⟨H, hxH⟩ := hCover x
    have hImage := H.property.1.isOpenEmbedding_subtypeVal.isOpenMap _ (hU H)
    exact mem_of_superset (hImage.mem_nhds ⟨⟨x, hxH⟩, hx, rfl⟩)
      (fun _ ⟨_, hy, hEq⟩ ↦ hEq ▸ hy)

omit [T2Space G] in
/-- Every compact set is contained in an open compactly generated subgroup. -/
theorem exists_openCompactlyGeneratedSubgroup_contains {K : Set G} (hK : IsCompact K) :
    ∃ H : OpenCompactlyGeneratedSubgroups G, K ⊆ (H.val : Set G) := by
  obtain ⟨U, hU, hU₁⟩ := exists_compact_mem_nhds (1 : G)
  let H := Subgroup.closure (U ∪ K)
  have hSubset : U ∪ K ⊆ (H : Set G) := Subgroup.subset_closure
  have hOpen : IsOpen (H : Set G) :=
    H.isOpen_of_mem_nhds (mem_of_superset hU₁ (subset_union_left.trans hSubset))
  refine ⟨⟨H, hOpen, ⟨Subtype.val ⁻¹' (U ∪ K), ?_, ?_, ?_⟩⟩,
    subset_union_right.trans hSubset⟩
  · exact continuous_subtype_val.continuousAt.preimage_mem_nhds
      (mem_of_superset hU₁ subset_union_left)
  · exact IsEmbedding.subtypeVal.isInducing.isCompact_preimage' (hU.union hK)
      (Subtype.range_coe.symm ▸ hSubset)
  · exact Subgroup.closure_preimage_eq_top _

omit [T2Space G] in
/-- Characters on the open compactly generated subgroups glue to a character
on the whole group, and the restrictions recover the compact-open topology. -/
theorem pontryaginDual_openSubgroups_inverseLimit :
    let I := OpenCompactlyGeneratedSubgroups G
    ∃ r : PontryaginDual G →ₜ* ((H : I) → PontryaginDual H.val),
      (∀ ψ H (x : H.val), r ψ H x = ψ x.val) ∧ IsEmbedding r ∧
        range r = {a | ∀ (H J : I) (h : H ≤ J) (x : H.val),
          a H x = a J (Subgroup.inclusion h x)} := by
  classical
  let I := OpenCompactlyGeneratedSubgroups G
  letI : IsDirectedOrder I := (openCompactlyGeneratedSubgroups_colimit (G := G)).1
  have hCover := (openCompactlyGeneratedSubgroups_colimit (G := G)).2.1
  let restrict (H : I) : PontryaginDual G →ₜ* PontryaginDual H.val :=
    PontryaginDual.map ⟨H.val.subtype, continuous_subtype_val⟩
  let r : PontryaginDual G →ₜ* ((H : I) → PontryaginDual H.val) :=
    { toFun ψ H := restrict H ψ
      map_one' := funext fun H => map_one (restrict H)
      map_mul' ψ η := funext fun H => map_mul (restrict H) ψ η
      continuous_toFun := continuous_pi fun H => (restrict H).continuous }
  have hEval (ψ : PontryaginDual G) (H : I) (x : H.val) : r ψ H x = ψ x.val := rfl
  refine ⟨r, hEval, ⟨?_, ?_⟩, ?_⟩
  · rw [isInducing_iff_nhds]
    intro ψ
    apply le_antisymm (r.continuous.tendsto ψ).le_comap
    have h := (ContinuousMonoidHom.isInducing_toContinuousMap G Circle).nhds_eq_comap ψ
    refine le_trans ?_ h.ge
    change Tendsto id (Filter.comap (fun η : PontryaginDual G => r η) (𝓝 (r ψ)))
      (Filter.comap ContinuousMonoidHom.toContinuousMap (𝓝 ψ.toContinuousMap))
    apply Filter.tendsto_comap_iff.mpr
    apply ContinuousMap.tendsto_nhds_compactOpen.mpr
    intro K hK U hU hψ
    obtain ⟨H, hH⟩ := exists_openCompactlyGeneratedSubgroup_contains hK
    have hKH : IsCompact (Subtype.val ⁻¹' K : Set H.val) :=
      IsEmbedding.subtypeVal.isInducing.isCompact_preimage' hK (Subtype.range_coe.symm ▸ hH)
    let V : Set (PontryaginDual H.val) := {η | MapsTo η (Subtype.val ⁻¹' K) U}
    have hV : IsOpen V := (ContinuousMap.isOpen_setOfPred_mapsTo hKH hU).preimage
      (ContinuousMonoidHom.isInducing_toContinuousMap H.val Circle).continuous
    have hVr : r ψ H ∈ V := fun x hx => hψ hx
    have ht : Tendsto (fun η => r η H) (Filter.comap r (𝓝 (r ψ))) (𝓝 (r ψ H)) :=
      (continuous_apply H).continuousAt.tendsto.comp Filter.tendsto_comap
    filter_upwards [ht (hV.mem_nhds hVr)] with η hη
    exact fun x hx => hη (show (⟨x, hH hx⟩ : H.val) ∈ Subtype.val ⁻¹' K from hx)
  · intro ψ η h
    apply PontryaginDual.ext
    intro x
    obtain ⟨H, hH⟩ := hCover x
    exact congrArg (fun a => a H ⟨x, hH⟩) h
  · ext a
    constructor
    · rintro ⟨ψ, rfl⟩ H J h x
      rfl
    · intro ha
      change ∀ (H J : I) (h : H ≤ J) (x : H.val),
        a H x = a J (Subgroup.inclusion h x) at ha
      choose H hH using hCover
      let f (x : G) := a (H x) ⟨x, hH x⟩
      have hf (J : I) (x : J.val) : f x.val = a J x := by
        obtain ⟨L, h₁, h₂⟩ := exists_ge_ge (H x.val) J
        exact (ha _ _ h₁ _).trans (ha _ _ h₂ x).symm
      let ψ : PontryaginDual G :=
        { toFun := f
          map_one' := (hf (H 1) 1).trans (map_one (a (H 1)))
          map_mul' x y := by
            obtain ⟨L, hx, hy⟩ := exists_ge_ge (H x) (H y)
            let xL : L.val := ⟨x, hx (hH x)⟩
            let yL : L.val := ⟨y, hy (hH y)⟩
            exact (hf L (xL * yL)).trans
              ((map_mul (a L) xL yL).trans (congrArg₂ (· * ·) (hf L xL).symm (hf L yL).symm))
          continuous_toFun := by
            rw [continuous_iff_continuousAt]
            intro x
            let J := H x
            have hComp : f ∘ (Subtype.val : J.val → G) = a J := funext (hf J)
            exact J.property.1.isOpenEmbedding_subtypeVal.continuousAt_iff.mp
              (hComp.symm ▸ (a J).continuous.continuousAt (x := (⟨x, hH x⟩ : J.val))) }
      exact ⟨ψ, funext fun J => PontryaginDual.ext (hf J)⟩

/-- The evaluation map in D.1.4.4 is an embedding into the inverse limit
of duals. Surjectivity is equivalent to surjectivity of the bidual evaluation. -/
theorem lca_dualSubgroups_inverseLimit_iff_bidual :
    let I := OpenCompactlyGeneratedSubgroups (PontryaginDual G)
    ∃ γ : G →ₜ* ((H : I) → PontryaginDual H.val),
      (∀ x H (χ : H.val), γ x H χ = χ.val x) ∧ IsEmbedding γ ∧
      (range γ = {a | ∀ (H J : I) (h : H ≤ J) (χ : H.val),
        a H χ = a J (Subgroup.inclusion h χ)} ↔
        Surjective (pontryaginBidualEval (G := G))) := by
  obtain ⟨r, hEval, hEmb, hRange⟩ := pontryaginDual_openSubgroups_inverseLimit
    (G := PontryaginDual G)
  refine ⟨r.comp pontryaginBidualEval, fun x H χ => hEval _ H χ,
    hEmb.comp pontryaginBidualEval_isClosedEmbedding.isEmbedding, ?_⟩
  rw [← hRange]
  exact ⟨fun h ψ => by
    obtain ⟨x, hx⟩ := h.symm ▸ mem_range_self (f := r) ψ
    exact ⟨x, hEmb.injective hx⟩, fun h => h.range_comp r⟩

/-- Paper: After (D.1.4.10), p. 759. Every identity neighborhood contains
one of the compact annihilators.
Deviation: The small subgroups are the kernels Kᵢ, as stated on p. 760. -/
theorem exists_lcaDualAnnihilator_subset_nhds {U : Set G} (hU : U ∈ 𝓝 (1 : G)) :
    ∃ H : OpenCompactlyGeneratedSubgroups (PontryaginDual G),
      (lcaDualAnnihilator H.val : Set G) ⊆ U := by
  obtain ⟨K, hK, hTest⟩ := exists_compact_pontryaginDual_test hU
  obtain ⟨H, hKH⟩ := exists_openCompactlyGeneratedSubgroup_contains hK
  refine ⟨H, fun x hx ↦ hTest x ?_⟩
  intro χ hχ
  have hχx := (mem_lcaDualAnnihilator_iff H.val x).mp hx ⟨χ, hKH hχ⟩
  change χ x = 1 at hχx
  rw [hχx, dist_self]
  norm_num

/-- An open subgroup of the dual has compact annihilator in the original group. -/
theorem isCompact_lcaDualAnnihilator_of_isOpen (H : Subgroup (PontryaginDual G))
    (hH : IsOpen (H : Set (PontryaginDual G))) : IsCompact (lcaDualAnnihilator H : Set G) := by
  have hPreimage : (lcaDualAnnihilator H : Set G) =
      pontryaginBidualEval ⁻¹' (lcaAnnihilator H : Set (PontryaginDual (PontryaginDual G))) := by
    ext x
    exact (mem_lcaDualAnnihilator_iff H x).trans
      (mem_lcaAnnihilator_iff H (pontryaginBidualEval x)).symm
  rw [hPreimage]
  exact pontryaginBidualEval_isClosedEmbedding.isCompact_preimage (isCompact_lcaAnnihilator H hH)

/-- The canonical quotient maps from an open compactly generated subgroup identify
it with the compatible families in the product of quotients by small annihilators. -/
theorem lca_openSubgroup_inverseLimit (J : OpenCompactlyGeneratedSubgroups G) :
    let I := {H : OpenCompactlyGeneratedSubgroups (PontryaginDual G) //
      lcaDualAnnihilator H.val ≤ J.val}
    let K : I → Subgroup J.val := fun H ↦ (lcaDualAnnihilator H.val.val).comap J.val.subtype
    let δ : J.val → ((H : I) → J.val ⧸ K H) := fun x _ ↦ QuotientGroup.mk x
    Nonempty I ∧ IsDirectedOrder I ∧
      IsEmbedding δ ∧ range δ = {a | ∀ (H H' : I), H ≤ H' →
      ∃ x : J.val, δ x H = a H ∧ δ x H' = a H'} := by
  let I := {H : OpenCompactlyGeneratedSubgroups (PontryaginDual G) //
    lcaDualAnnihilator H.val ≤ J.val}
  let K (H : I) : Subgroup J.val := (lcaDualAnnihilator H.val.val).comap J.val.subtype
  let δ : J.val →ₜ* ((H : I) → J.val ⧸ K H) :=
    { toFun := fun x H ↦ QuotientGroup.mk x
      map_one' := funext fun H ↦ QuotientGroup.mk_one (N := K H)
      map_mul' := fun x y ↦ funext fun H ↦ QuotientGroup.mk_mul (K H) x y
      continuous_toFun := continuous_pi fun H ↦ QuotientGroup.continuous_mk }
  change Nonempty I ∧ IsDirectedOrder I ∧ IsEmbedding δ ∧
    range δ = {a | ∀ (H H' : I), H ≤ H' → ∃ x : J.val, δ x H = a H ∧ δ x H' = a H'}
  have hSmall {V : Set J.val} (hV : V ∈ 𝓝 (1 : J.val)) :
      ∃ H : I, (K H : Set J.val) ⊆ V := by
    obtain ⟨H, hH⟩ := exists_lcaDualAnnihilator_subset_nhds
      (J.property.1.isOpenEmbedding_subtypeVal.isOpenMap.image_mem_nhds hV)
    refine ⟨⟨H, fun x hx ↦ ?_⟩, ?_⟩
    · obtain ⟨y, _, rfl⟩ := hH hx
      exact y.property
    · intro x hx
      obtain ⟨y, hy, hyx⟩ := hH (Subgroup.mem_comap.mp hx)
      exact (Subtype.ext hyx : y = x) ▸ hy
  let : Nonempty I := ⟨(hSmall Filter.univ_mem).choose⟩
  let : IsDirectedOrder (OpenCompactlyGeneratedSubgroups (PontryaginDual G)) :=
    (openCompactlyGeneratedSubgroups_colimit (G := PontryaginDual G)).1
  have hAnti : Antitone (fun H : OpenCompactlyGeneratedSubgroups (PontryaginDual G) ↦
      lcaDualAnnihilator H.val) := by
    intro H H' h x hx
    exact (mem_lcaDualAnnihilator_iff H.val x).mpr fun χ ↦
      (mem_lcaDualAnnihilator_iff H'.val x).mp hx (Subgroup.inclusion h χ)
  let : IsDirectedOrder I := ⟨fun H H' ↦ by
    obtain ⟨L, hHL, hH'L⟩ := exists_ge_ge H.val H'.val
    exact ⟨⟨L, (hAnti hHL).trans H.property⟩, hHL, hH'L⟩⟩
  -- A neighborhood can be tested in a quotient whose kernel lies in a smaller neighborhood.
  have hInducing : IsInducing δ := by
    rw [IsTopologicalGroup.isInducing_iff_nhds_one]
    refine le_antisymm ?_ ?_
    · have h : Tendsto δ (𝓝 1) (𝓝 (δ 1)) := δ.continuous.tendsto 1
      rw [map_one] at h
      exact h.le_comap
    · intro U hU
      obtain ⟨V, hV, h1V, hVV⟩ := exists_open_nhds_one_mul_subset hU
      obtain ⟨H, hH⟩ := hSmall (hV.mem_nhds h1V)
      let q : J.val → J.val ⧸ K H := QuotientGroup.mk
      have hqV : q '' V ∈ 𝓝 (1 : J.val ⧸ K H) :=
        (QuotientGroup.isOpenMap_coe (N := K H)).image_mem_nhds (hV.mem_nhds h1V)
      refine Filter.mem_comap.mpr ⟨(fun a ↦ a H) ⁻¹' (q '' V),
        (continuous_apply H).continuousAt.preimage_mem_nhds hqV, ?_⟩
      intro x hx
      obtain ⟨y, hy, hyx⟩ : q x ∈ q '' V := hx
      have hDiff : y⁻¹ * x ∈ K H := QuotientGroup.eq.mp hyx
      exact hVV ⟨y, hy, y⁻¹ * x, hH hDiff, mul_inv_cancel_left y x⟩
  refine ⟨inferInstance, inferInstance, ⟨hInducing, hInducing.injective⟩, ?_⟩
  ext a
  constructor
  · rintro ⟨x, rfl⟩ H H' _
    exact ⟨x, rfl, rfl⟩
  · intro ha
    change ∀ (H H' : I), H ≤ H' → ∃ x : J.val, δ x H = a H ∧ δ x H' = a H' at ha
    let F (H : I) : Set J.val := {x | δ x H = a H}
    have hNonempty (H : I) : (F H).Nonempty := by
      obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (a H)
      exact ⟨x, hx⟩
    have hCompact (H : I) : IsCompact (K H : Set J.val) :=
      (J.val.isClosed_of_isOpen J.property.1).isClosedEmbedding_subtypeVal.isCompact_preimage
        (isCompact_lcaDualAnnihilator_of_isOpen H.val.val H.val.property.1)
    -- The fibers are translates of compact kernels and decrease along the index order.
    have hFiberCompact (H : I) : IsCompact (F H) := by
      obtain ⟨y, hy⟩ := hNonempty H
      have hFiber : F H = (fun z : J.val ↦ y * z) '' (K H : Set J.val) := by
        ext x
        constructor
        · intro hx
          exact ⟨y⁻¹ * x, QuotientGroup.eq.mp (hy.trans hx.symm), mul_inv_cancel_left y x⟩
        · rintro ⟨z, hz, rfl⟩
          change (QuotientGroup.mk (y * z) : J.val ⧸ K H) = a H
          rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff z).mpr hz, mul_one]
          exact hy
      rw [hFiber]
      exact (hCompact H).image (continuous_const.mul continuous_id)
    have hFiberAnti : Antitone F := by
      intro H H' h x hx
      obtain ⟨y, hy, hy'⟩ := ha H H' h
      have hDiff : x⁻¹ * y ∈ K H' := QuotientGroup.eq.mp (hx.trans hy'.symm)
      have hK : K H' ≤ K H := Subgroup.comap_mono (hAnti (show H.val ≤ H'.val from h))
      exact (QuotientGroup.eq.mpr (hK hDiff)).trans hy
    obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
      F (directed_of_isDirected_le hFiberAnti) hNonempty hFiberCompact
      (fun H ↦ (hFiberCompact H).isClosed)
    exact ⟨x, funext (mem_iInter.mp hx)⟩

/-- In the system for the discrete integers there is a quotient by the trivial
annihilator. This quotient has infinitely many connected components. -/
theorem integer_annihilator_quotient_infinite_components :
    ∃ H : OpenCompactlyGeneratedSubgroups (PontryaginDual (Multiplicative ℤ)),
      Infinite (ConnectedComponents (Multiplicative ℤ ⧸ lcaDualAnnihilator H.val)) := by
  have hN : ({1} : Set (Multiplicative ℤ)) ∈ 𝓝 (1 : Multiplicative ℤ) :=
    (isOpen_discrete _).mem_nhds (mem_singleton _)
  obtain ⟨H, hH⟩ := exists_lcaDualAnnihilator_subset_nhds hN
  let K := lcaDualAnnihilator H.val
  have hK : K = ⊥ := le_antisymm (fun _ hx => Subgroup.mem_bot.mpr (hH hx)) bot_le
  refine ⟨H, ?_⟩
  let q : Multiplicative ℤ → Multiplicative ℤ ⧸ K := QuotientGroup.mk
  letI : DiscreteTopology (Multiplicative ℤ ⧸ K) := discreteTopology_iff_forall_isOpen.mpr fun U =>
    (QuotientGroup.isQuotientMap_mk K).isCoinducing.isOpen_preimage.mp (isOpen_discrete (q ⁻¹' U))
  let f : Multiplicative ℤ → ConnectedComponents (Multiplicative ℤ ⧸ K) :=
    ConnectedComponents.mk ∘ q
  apply Infinite.of_injective f
  intro x y hxy
  have hq : q x = q y := by
    change (q x : ConnectedComponents (Multiplicative ℤ ⧸ K)) = q y at hxy
    simpa only [connectedComponent_eq_singleton, mem_singleton_iff] using
      ConnectedComponents.coe_eq_coe'.mp hxy
  have h : x⁻¹ * y ∈ K := QuotientGroup.eq.mp hq
  have hOne : x⁻¹ * y = 1 := Subgroup.mem_bot.mp (hK ▸ h)
  exact inv_mul_eq_one.mp hOne

end Masullo
