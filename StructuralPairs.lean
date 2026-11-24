import ElementaryLCAStructure
import StructuralPairFourier

open Filter Function MeasureTheory Set Topology
open scoped ZeroAtInfty

namespace Masullo

noncomputable section

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G]

/-- The reverse double-annihilator identity follows from the canonical
bidual isomorphism and the double-annihilator theorem on the dual. -/
theorem lcaAnnihilator_dualAnnihilator (H : Subgroup (PontryaginDual G))
    (hH : IsClosed (H : Set (PontryaginDual G))) :
    lcaAnnihilator (lcaDualAnnihilator H) = H := by
  ext χ
  constructor
  · intro hχ
    rw [← lcaDualAnnihilator_annihilator H hH]
    apply (mem_lcaDualAnnihilator_iff (lcaAnnihilator H) χ).mpr
    intro η
    obtain ⟨x, hx⟩ := pontryaginBidualEval_surjective (G := G) η.val
    have hxK : x ∈ lcaDualAnnihilator H := by
      apply (mem_lcaDualAnnihilator_iff H x).mpr
      intro ψ
      exact (DFunLike.congr_fun hx ψ.val).trans
        ((mem_lcaAnnihilator_iff H η.val).mp η.property ψ)
    exact (DFunLike.congr_fun hx χ).symm.trans
      ((mem_lcaAnnihilator_iff (lcaDualAnnihilator H) χ).mp hχ ⟨x, hxK⟩)
  · intro hχ
    exact (mem_lcaAnnihilator_iff (lcaDualAnnihilator H) χ).mpr fun x ↦
      (mem_lcaDualAnnihilator_iff H x.val).mp x.property ⟨χ, hχ⟩

private theorem isClosed_lcaDualAnnihilator_direct (H : Subgroup (PontryaginDual G)) :
    IsClosed (lcaDualAnnihilator H : Set G) := by
  rw [show (lcaDualAnnihilator H : Set G) = ⋂ χ : H, {x | χ.val x = 1} by
    ext x
    rw [mem_iInter]
    exact mem_lcaDualAnnihilator_iff H x]
  exact isClosed_iInter fun χ ↦ isClosed_eq χ.val.continuous continuous_const

/-- A structural pair has an open compactly generated upper subgroup and
a closed kernel whose annihilator is open and compactly generated. -/
structure LCAStructuralPair (G : Type*) [CommGroup G] [TopologicalSpace G] where
  upper : OpenCompactlyGeneratedSubgroups G
  kernel : Subgroup G
  kernel_closed : IsClosed (kernel : Set G)
  annihilator_open : IsOpen (lcaAnnihilator kernel : Set (PontryaginDual G))
  annihilator_compactlyGenerated : IsCompactlyGeneratedGroup (lcaAnnihilator kernel)
  kernel_le : kernel ≤ upper.val

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] in
@[ext] theorem LCAStructuralPair.ext' {P Q : LCAStructuralPair G}
    (hu : P.upper = Q.upper) (hk : P.kernel = Q.kernel) : P = Q := by
  cases P
  cases Q
  cases hu
  cases hk
  rfl

instance : PartialOrder (LCAStructuralPair G) :=
  PartialOrder.lift
    (fun P : LCAStructuralPair G ↦ (P.upper.val, OrderDual.toDual P.kernel))
    (fun _ _ h ↦ LCAStructuralPair.ext' (Subtype.ext (congrArg Prod.fst h))
      (congrArg (fun a : Subgroup G × OrderDual (Subgroup G) ↦ OrderDual.ofDual a.2) h))

/-- Open compactly generated primal and dual subgroups give a structural
pair whenever the dual annihilator is contained in the primal subgroup. -/
def LCAStructuralPair.ofDual
    (J : OpenCompactlyGeneratedSubgroups G)
    (H : OpenCompactlyGeneratedSubgroups (PontryaginDual G))
    (h : lcaDualAnnihilator H.val ≤ J.val) : LCAStructuralPair G where
  upper := J
  kernel := lcaDualAnnihilator H.val
  kernel_closed := isClosed_lcaDualAnnihilator_direct H.val
  annihilator_open := by
    rw [lcaAnnihilator_dualAnnihilator H.val (H.val.isClosed_of_isOpen H.property.1)]
    exact H.property.1
  annihilator_compactlyGenerated := by
    rw [lcaAnnihilator_dualAnnihilator H.val (H.val.isClosed_of_isOpen H.property.1)]
    exact H.property.2
  kernel_le := h

/-- The order enlarges the upper subgroup and shrinks the kernel. -/
theorem lcaStructuralPairs_filtered : Nonempty (LCAStructuralPair G) ∧
    IsDirectedOrder (LCAStructuralPair G) := by
  letI := (openCompactlyGeneratedSubgroups_colimit (G := G)).1
  letI := (openCompactlyGeneratedSubgroups_colimit (G := PontryaginDual G)).1
  constructor
  · obtain ⟨J, _⟩ := (openCompactlyGeneratedSubgroups_colimit (G := G)).2.1 1
    obtain ⟨H, hH⟩ := exists_lcaDualAnnihilator_subset_nhds
      (J.property.1.mem_nhds J.val.one_mem)
    exact ⟨LCAStructuralPair.ofDual J H hH⟩
  · constructor
    intro P Q
    obtain ⟨J, hPJ, hQJ⟩ := exists_ge_ge P.upper Q.upper
    let P' : OpenCompactlyGeneratedSubgroups (PontryaginDual G) :=
      ⟨lcaAnnihilator P.kernel, P.annihilator_open, P.annihilator_compactlyGenerated⟩
    let Q' : OpenCompactlyGeneratedSubgroups (PontryaginDual G) :=
      ⟨lcaAnnihilator Q.kernel, Q.annihilator_open, Q.annihilator_compactlyGenerated⟩
    obtain ⟨H, hPH, hQH⟩ := exists_ge_ge P' Q'
    have hP : lcaDualAnnihilator H.val ≤ P.kernel := by
      intro x hx
      rw [← lcaDualAnnihilator_annihilator P.kernel P.kernel_closed]
      exact (mem_lcaDualAnnihilator_iff _ x).mpr fun ψ ↦
        (mem_lcaDualAnnihilator_iff _ x).mp hx (Subgroup.inclusion hPH ψ)
    have hQ : lcaDualAnnihilator H.val ≤ Q.kernel := by
      intro x hx
      rw [← lcaDualAnnihilator_annihilator Q.kernel Q.kernel_closed]
      exact (mem_lcaDualAnnihilator_iff _ x).mpr fun ψ ↦
        (mem_lcaDualAnnihilator_iff _ x).mp hx (Subgroup.inclusion hQH ψ)
    exact ⟨LCAStructuralPair.ofDual J H (hP.trans (P.kernel_le.trans hPJ)),
      ⟨hPJ, hP⟩, ⟨hQJ, hQ⟩⟩

/-- The quotient of any structural pair is an elementary abelian Lie group. -/
theorem LCAStructuralPair.quotient_elementary (P : LCAStructuralPair G) :
    Nonempty (ElementaryLCAPresentation
      (P.upper.val ⧸ P.kernel.comap P.upper.val.subtype)) := by
  let H : OpenCompactlyGeneratedSubgroups (PontryaginDual G) :=
    ⟨lcaAnnihilator P.kernel, P.annihilator_open, P.annihilator_compactlyGenerated⟩
  obtain ⟨p⟩ := lca_openSubgroup_quotient_elementary P.upper H
  have hk := congrArg (fun K : Subgroup G ↦ K.comap P.upper.val.subtype)
    (lcaDualAnnihilator_annihilator P.kernel P.kernel_closed)
  let e₀ := QuotientGroup.quotientMulEquivOfEq hk.symm
  let e := e₀.toContinuousMulEquiv fun U ↦ by
    exact (QuotientGroup.isQuotientMap_mk _).isCoinducing.isOpen_preimage.symm.trans
      (QuotientGroup.isQuotientMap_mk _).isCoinducing.isOpen_preimage
  exact ⟨{
    realDim := p.realDim
    torusDim := p.torusDim
    latticeRank := p.latticeRank
    finiteFactor := p.finiteFactor
    finiteGroup := p.finiteGroup
    finiteFintype := p.finiteFintype
    finiteTopology := p.finiteTopology
    finiteDiscrete := p.finiteDiscrete
    equiv := e.trans p.equiv }⟩

/-- A topological group isomorphism preserves compact generation. -/
theorem compactGeneration_transport {A B : Type*}
    [CommGroup A] [TopologicalSpace A] [CommGroup B] [TopologicalSpace B]
    (e : A ≃ₜ* B) (ha : IsCompactlyGeneratedGroup A) : IsCompactlyGeneratedGroup B := by
  obtain ⟨U, hU, hUc, hGen⟩ := ha
  refine ⟨e '' U, ?_, hUc.image e.continuous, ?_⟩
  · have h := e.toHomeomorph.isOpenMap.image_mem_nhds hU
    change e '' U ∈ 𝓝 (e 1) at h
    rwa [map_one] at h
  · change Subgroup.closure (e.toMulEquiv.toMonoidHom '' U) = ⊤
    rw [← MonoidHom.map_closure, hGen,
      Subgroup.map_top_of_surjective _ e.surjective]

/-- Taking annihilators exchanges the upper subgroup and the kernel. -/
def LCAStructuralPair.dual (P : LCAStructuralPair G) : LCAStructuralPair (PontryaginDual G) := by
  let D := lcaAnnihilator (lcaAnnihilator P.upper.val)
  let b := pontryaginBidualEval (G := G)
  have hPred : b ⁻¹' (D : Set (PontryaginDual (PontryaginDual G))) =
      (P.upper.val : Set G) := by
    ext x
    change b x ∈ D ↔ x ∈ P.upper.val
    rw [← lcaDualAnnihilator_annihilator P.upper.val (P.upper.val.isClosed_of_isOpen P.upper.property.1)]
    exact (mem_lcaAnnihilator_iff (lcaAnnihilator P.upper.val) (b x)).trans
      (mem_lcaDualAnnihilator_iff (lcaAnnihilator P.upper.val) x).symm
  have hb := pontryaginBidualEval_isClosedEmbedding (G := G)
  have hSurj := pontryaginBidualEval_surjective (G := G)
  have hbOpen := hb.isInducing.isOpenMap (hSurj.range_eq ▸ isOpen_univ)
  have hD : IsOpen (D : Set (PontryaginDual (PontryaginDual G))) := by
    have h := hbOpen _ (hPred.symm ▸ P.upper.property.1)
    rw [image_preimage_eq _ hSurj] at h
    exact h
  let r : P.upper.val →* D :=
    (b.toMonoidHom.comp P.upper.val.subtype).codRestrict D (fun x ↦
      show x.val ∈ b ⁻¹' (D : Set _) from hPred.symm ▸ x.property)
  have hrOpen : IsOpenMap r :=
    (hbOpen.comp P.upper.property.1.isOpenEmbedding_subtypeVal.isOpenMap).codRestrict _
  have hrCont : Continuous r := (b.continuous.comp continuous_subtype_val).subtype_mk _
  have hrSurj : Surjective r := by
    intro η
    obtain ⟨x, hx⟩ := hSurj η.val
    have hx' : x ∈ b ⁻¹' (D : Set _) := show b x ∈ D from hx.symm ▸ η.property
    have hJ : x ∈ (P.upper.val : Set G) := by rw [← hPred]; exact hx'
    exact ⟨⟨x, hJ⟩, Subtype.ext hx⟩
  let e := (MulEquiv.ofBijective r ⟨fun _ _ h ↦
    Subtype.ext (hb.injective (congrArg (fun z : D ↦ z.val) h)), hrSurj⟩).toContinuousMulEquiv
    (fun _ ↦ (hrOpen.isQuotientMap hrCont hrSurj).isCoinducing.isOpen_preimage)
  refine ⟨⟨lcaAnnihilator P.kernel, P.annihilator_open, P.annihilator_compactlyGenerated⟩,
    lcaAnnihilator P.upper.val, ?_, hD, compactGeneration_transport e P.upper.property.2, ?_⟩
  · exact isClosed_eq (PontryaginDual.map
      (⟨P.upper.val.subtype, continuous_subtype_val⟩ : P.upper.val →ₜ* G)).continuous continuous_const
  · intro χ hχ
    exact (mem_lcaAnnihilator_iff P.kernel χ).mpr fun x ↦
      (mem_lcaAnnihilator_iff P.upper.val χ).mp hχ ⟨x.val, P.kernel_le x.property⟩

/-- On the unique continuous representative, structural support and invariance
are exchanged by the Fourier transform. -/
theorem LCAStructuralPair.fourier_iff
    [MeasurableSpace G] [BorelSpace G] [MeasurableSpace (PontryaginDual G)]
    [BorelSpace (PontryaginDual G)] (P : LCAStructuralPair G)
    (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular] (ν : Measure (PontryaginDual G))
    (hν : IsLCAPlancherelMeasure μ ν) {f : G → ℂ}
    (hf : Integrable f μ) (hF : Integrable (lcaFourier μ f) ν) :
    ∃ F : C₀(G, ℂ), (F : G → ℂ) =ᵐ[μ] f ∧
      ((Function.support F ⊆ P.upper.val ∧ ∀ k : P.kernel, ∀ x, F (k.val * x) = F x) ↔
        (∀ ψ : P.dual.kernel, ∀ χ, lcaFourier μ f (ψ.val * χ) = lcaFourier μ f χ) ∧
        Function.support (lcaFourier μ f) ⊆ P.dual.upper.val) := by
  obtain ⟨F, hEq, _, hK, hΓ, _⟩ := lcaFourier_structural_representative μ ν hν hf hF
  refine ⟨F, hEq, ?_⟩
  exact and_congr (hΓ P.upper.val (P.upper.val.isClosed_of_isOpen P.upper.property.1)).symm
    (hK P.kernel).symm

end
end Masullo
