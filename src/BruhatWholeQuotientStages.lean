import ModulatedExponentialInductive

open Function Set Topology

namespace Masullo

noncomputable section

set_option maxHeartbeats 1200000

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G]

namespace WholeBruhatStage

variable (P : WholeBruhatStage G)

private def upperEquiv : G ≃ₜ* P.val.1.upper.val :=
  { toFun := fun x ↦ ⟨x, P.property.symm ▸ Subgroup.mem_top x⟩
    invFun := Subtype.val
    left_inv := fun _ ↦ rfl
    right_inv := fun _ ↦ Subtype.ext rfl
    map_mul' := fun _ _ ↦ Subtype.ext rfl
    continuous_toFun := continuous_id.subtype_mk _
    continuous_invFun := continuous_subtype_val }

/-- Coordinates on the elementary quotient of a stage whose upper subgroup
is the whole group. -/
def coordinates : G →ₜ* Multiplicative (ElementaryLCAModel P.val.2.realDim P.val.2.torusDim
    P.val.2.latticeRank P.val.2.finiteFactor) :=
  (P.val.1.stageCoordinates P.val.2).comp
    ⟨(upperEquiv P).toMonoidHom, (upperEquiv P).continuous⟩

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] in
theorem coordinates_surjective : Surjective P.coordinates :=
  (P.val.2.equiv.surjective.comp QuotientGroup.mk_surjective).comp (upperEquiv P).surjective

omit [T2Space G] [LocallyCompactSpace G] in
theorem coordinates_isOpenMap : IsOpenMap P.coordinates :=
  (P.val.2.equiv.toHomeomorph.isOpenMap.comp QuotientGroup.isOpenMap_coe).comp
    (upperEquiv P).toHomeomorph.isOpenMap

@[simp] theorem realize_eq_coordinates (f : P.val.Space) (x : G) :
    P.val.realize f x = f (P.coordinates x).toAdd :=
  P.val.1.realizeSchwartz_apply_of_mem P.val.2 f (upperEquiv P x)

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] in
@[simp] theorem coordinates_ker : P.coordinates.toMonoidHom.ker = P.val.1.kernel := by
  ext x
  change P.val.2.equiv (QuotientGroup.mk (upperEquiv P x)) = 1 ↔ x ∈ P.val.1.kernel
  rw [← map_one P.val.2.equiv, P.val.2.equiv.injective.eq_iff, QuotientGroup.eq_one_iff]
  rfl

variable {Y : Type*} [CommGroup Y] [TopologicalSpace Y] [IsTopologicalGroup Y]
  [T2Space Y] [LocallyCompactSpace Y]

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
  [IsTopologicalGroup Y] [T2Space Y] [LocallyCompactSpace Y] in
private theorem coordinateMap_condition (Q : WholeBruhatStage Y) (q : G →ₜ* Y)
    (hq : P.val.1.kernel ≤ Q.val.1.kernel.comap q.toMonoidHom) (k : P.val.1.kernel) :
    (Q.coordinates.comp q) k.val = 1 := by
  have hk := hq k.property
  change q k.val ∈ Q.val.1.kernel at hk
  rw [← Q.coordinates_ker] at hk
  exact hk

/-- A map respecting two whole-group structural kernels induces a
continuous map in the elementary coordinates. -/
def coordinateMap (Q : WholeBruhatStage Y) (q : G →ₜ* Y)
    (hq : P.val.1.kernel ≤ Q.val.1.kernel.comap q.toMonoidHom) :
    Multiplicative (ElementaryLCAModel P.val.2.realDim P.val.2.torusDim P.val.2.latticeRank
      P.val.2.finiteFactor) →ₜ* Multiplicative (ElementaryLCAModel Q.val.2.realDim
      Q.val.2.torusDim Q.val.2.latticeRank Q.val.2.finiteFactor) :=
  (P.val.1.descendHom (Q.coordinates.comp q) (P.coordinateMap_condition Q q hq)).comp
    P.val.2.equiv.symm

omit [IsTopologicalGroup Y] [T2Space Y] [LocallyCompactSpace Y] in
@[simp] theorem coordinateMap_coordinates (Q : WholeBruhatStage Y) (q : G →ₜ* Y)
    (hq : P.val.1.kernel ≤ Q.val.1.kernel.comap q.toMonoidHom) (x : G) :
    P.coordinateMap Q q hq (P.coordinates x) = Q.coordinates (q x) := by
  change (P.val.1.descendHom (Q.coordinates.comp q) (P.coordinateMap_condition Q q hq))
    (P.val.2.equiv.symm (P.val.2.equiv (QuotientGroup.mk (upperEquiv P x)))) = _
  rw [P.val.2.equiv.symm_apply_apply, LCAStructuralPair.descendHom_mk]
  rfl

omit [IsTopologicalGroup Y] [T2Space Y] [LocallyCompactSpace Y] in
theorem coordinateMap_surjective (Q : WholeBruhatStage Y) (q : G →ₜ* Y)
    (hq : P.val.1.kernel ≤ Q.val.1.kernel.comap q.toMonoidHom) (hs : Surjective q) :
    Surjective (P.coordinateMap Q q hq) := by
  intro z
  obtain ⟨x, hx⟩ := Q.coordinates_surjective.comp hs z
  exact ⟨P.coordinates x, (P.coordinateMap_coordinates Q q hq x).trans hx⟩

omit [T2Space Y] [LocallyCompactSpace Y] in
theorem coordinateMap_isOpenMap (Q : WholeBruhatStage Y) (q : G →ₜ* Y)
    (hq : P.val.1.kernel ≤ Q.val.1.kernel.comap q.toMonoidHom) (ho : IsOpenMap q) :
    IsOpenMap (P.coordinateMap Q q hq) := by
  intro U hU
  have he : P.coordinateMap Q q hq '' U =
      (Q.coordinates ∘ q) '' (P.coordinates ⁻¹' U) := by
    ext y
    constructor
    · rintro ⟨u, hu, rfl⟩
      obtain ⟨x, rfl⟩ := P.coordinates_surjective u
      exact ⟨x, hu, (P.coordinateMap_coordinates Q q hq x).symm⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨P.coordinates x, hx, P.coordinateMap_coordinates Q q hq x⟩
  rw [he]
  exact (Q.coordinates_isOpenMap.comp ho) _ (hU.preimage P.coordinates.continuous)

/-- Descend the logarithmic modulation to a whole-group elementary chart. -/
def logCoordinate (m : G →ₜ* Multiplicative ℝ) :
    ElementaryLCAModel P.val.2.realDim P.val.2.torusDim P.val.2.latticeRank P.val.2.finiteFactor →+ ℝ :=
  let A := ElementaryLCAModel P.val.2.realDim P.val.2.torusDim P.val.2.latticeRank P.val.2.finiteFactor
  let e : Multiplicative A →ₜ* P.val.1.StageQuotient := P.val.2.equiv.symm
  ((P.val.1.descendHom m (P.val.1.modulation_eq_one_on_kernel m)).comp e).toMonoidHom.toAdditive

theorem logCoordinate_isProperMap (m : G →ₜ* Multiplicative ℝ) (hm : IsProperMap m) :
    IsProperMap (P.logCoordinate m) :=
  (P.val.1.descendModulation_isProperMap m hm).comp P.val.2.equiv.symm.toHomeomorph.isProperMap

@[simp] theorem logCoordinate_coordinates (m : G →ₜ* Multiplicative ℝ) (x : G) :
    P.logCoordinate m (P.coordinates x).toAdd = (m x).toAdd := by
  change ((P.val.1.descendHom m (P.val.1.modulation_eq_one_on_kernel m))
    (P.val.2.equiv.symm (P.val.2.equiv (QuotientGroup.mk (upperEquiv P x))))).toAdd = _
  rw [P.val.2.equiv.symm_apply_apply, LCAStructuralPair.descendHom_mk]
  rfl

end WholeBruhatStage

section Image

variable (H : Subgroup G) [T2Space (G ⧸ H)] [LocallyCompactSpace (G ⧸ H)]

/-- On a compact quotient, the image of a whole-group structural stage
again gives a whole-group structural stage. The dual proof adapts
mccorvie/riemann-masullo, §D.1.7 (Apache-2.0). -/
theorem exists_wholeBruhatStage_quotient_image [CompactSpace (G ⧸ H)]
    (hH : IsClosed (H : Set G)) (P : WholeBruhatStage G) :
    ∃ Q : WholeBruhatStage (G ⧸ H),
      Q.val.1.kernel = P.val.1.kernel.map (QuotientGroup.mk' H) := by
  let q := QuotientGroup.mk' H
  let K := P.val.1.kernel
  have hK : IsCompact (K : Set G) := by
    change IsCompact (P.val.1.kernel : Set G)
    rw [← lcaDualAnnihilator_annihilator P.val.1.kernel P.val.1.kernel_closed]
    exact isCompact_lcaDualAnnihilator_of_isOpen _ P.val.1.annihilator_open
  have hKq : IsCompact (K.map q : Set (G ⧸ H)) := by
    rw [Subgroup.coe_map]
    exact hK.image QuotientGroup.continuous_mk
  let eTop : (⊤ : Subgroup (G ⧸ H)) ≃ₜ* (G ⧸ H) :=
    ⟨Subgroup.topEquiv, continuous_subtype_val, continuous_id.subtype_mk _⟩
  have hcg : IsCompactlyGeneratedGroup (G ⧸ H) := by
    exact ⟨univ, Filter.univ_mem, isCompact_univ, Subgroup.closure_univ⟩
  let J : OpenCompactlyGeneratedSubgroups (G ⧸ H) :=
    ⟨⊤, isOpen_univ, compactGeneration_transport eTop.symm hcg⟩
  have hAnn : IsCompactlyGeneratedGroup (lcaAnnihilator (K.map q)) := by
    obtain ⟨e, he⟩ := lcaQuotientDual_equiv_annihilator H hH
    let M : Subgroup (lcaAnnihilator K) := (lcaAnnihilator H).comap (lcaAnnihilator K).subtype
    have hLoc : LocallyCompactSpace (lcaAnnihilator K) :=
      P.val.1.annihilator_open.isOpenEmbedding_subtypeVal.locallyCompactSpace
    have hClosed : IsClosed (lcaAnnihilator H : Set (PontryaginDual G)) := by
      let R : H →ₜ* G := ⟨H.subtype, continuous_subtype_val⟩
      change IsClosed ((PontryaginDual.map R) ⁻¹' {1})
      exact isClosed_singleton.preimage (PontryaginDual.map R).continuous
    have hGen := isCompactlyGeneratedGroup_closedSubgroup P.val.1.annihilator_compactlyGenerated
      M (hClosed.preimage continuous_subtype_val)
    have hto (ψ : M) : e.symm ⟨ψ.val.val, ψ.property⟩ ∈ lcaAnnihilator (K.map q) := by
      rw [mem_lcaAnnihilator_iff]
      rintro ⟨_, x, hx, rfl⟩
      have h := he (e.symm ⟨ψ.val.val, ψ.property⟩) x
      rw [e.apply_symm_apply] at h
      exact h.symm.trans ((mem_lcaAnnihilator_iff K _).1 ψ.val.property ⟨x, hx⟩)
    have hfrom (χ : lcaAnnihilator (K.map q)) : (e χ.val).val ∈ lcaAnnihilator K := by
      rw [mem_lcaAnnihilator_iff]
      intro x
      rw [he]
      exact (mem_lcaAnnihilator_iff _ _).1 χ.property ⟨q x.val, x.val, x.property, rfl⟩
    let E : M ≃ₜ* lcaAnnihilator (K.map q) :=
      { toFun := fun ψ ↦ ⟨e.symm ⟨ψ.val.val, ψ.property⟩, hto ψ⟩
        invFun := fun χ ↦ ⟨⟨(e χ.val).val, hfrom χ⟩, (e χ.val).property⟩
        left_inv := fun ψ ↦ by
          apply Subtype.ext
          apply Subtype.ext
          change (e (e.symm ⟨ψ.val.val, ψ.property⟩)).val = ψ.val.val
          rw [e.apply_symm_apply]
        right_inv := fun χ ↦ by
          apply Subtype.ext
          change e.symm ⟨(e χ.val).val, (e χ.val).property⟩ = χ.val
          exact e.symm_apply_apply χ.val
        map_mul' := fun ψ ω ↦ by
          apply Subtype.ext
          exact e.symm.map_mul ⟨ψ.val.val, ψ.property⟩ ⟨ω.val.val, ω.property⟩
        continuous_toFun := (e.symm.continuous.comp
          ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)).subtype_mk _
        continuous_invFun := ((continuous_subtype_val.comp
          (e.continuous.comp continuous_subtype_val)).subtype_mk _).subtype_mk _ }
    exact compactGeneration_transport E hGen
  let B : LCAStructuralPair (G ⧸ H) :=
    ⟨J, K.map q, hKq.isClosed, isOpen_lcaAnnihilator _ hKq, hAnn, le_top⟩
  obtain ⟨b⟩ := B.quotient_elementary
  exact ⟨⟨⟨B, b⟩, rfl⟩, rfl⟩

/-- Every stage on a compact group refines to a whole-group stage. -/
theorem exists_wholeBruhatStage_refinement_of_compact {Y : Type*} [CommGroup Y]
    [TopologicalSpace Y] [IsTopologicalGroup Y] [T2Space Y] [LocallyCompactSpace Y]
    [CompactSpace Y] (Q : BruhatSchwartzStage Y) :
    ∃ R : WholeBruhatStage Y, Q.1 ≤ R.val.1 := by
  let eTop : (⊤ : Subgroup Y) ≃ₜ* Y :=
    ⟨Subgroup.topEquiv, continuous_subtype_val, continuous_id.subtype_mk _⟩
  have hcg : IsCompactlyGeneratedGroup Y :=
    ⟨univ, Filter.univ_mem, isCompact_univ, Subgroup.closure_univ⟩
  let J : OpenCompactlyGeneratedSubgroups Y :=
    ⟨⊤, isOpen_univ, compactGeneration_transport eTop.symm hcg⟩
  let B : LCAStructuralPair Y :=
    ⟨J, Q.1.kernel, Q.1.kernel_closed, Q.1.annihilator_open, Q.1.annihilator_compactlyGenerated, le_top⟩
  obtain ⟨b⟩ := B.quotient_elementary
  exact ⟨⟨⟨B, b⟩, rfl⟩, le_top, le_rfl⟩

/-- A target stage admits a source stage whose kernel maps into its
structural kernel, when the source has proper surjective modulation. -/
theorem exists_wholeBruhatStage_quotient_pullback (hH : IsClosed (H : Set G))
    (m : G →ₜ* Multiplicative ℝ) (hm : IsProperMap m) (hms : Surjective m)
    (Q : WholeBruhatStage (G ⧸ H)) :
    ∃ P : WholeBruhatStage G, P.val.1.kernel ≤ Q.val.1.kernel.comap (QuotientGroup.mk' H) := by
  let K := Q.val.1.kernel
  obtain ⟨e, he⟩ := lcaQuotientDual_equiv_annihilator H hH
  let B : lcaAnnihilator K →* PontryaginDual G :=
    (lcaAnnihilator H).subtype.comp (e.toMonoidHom.comp (lcaAnnihilator K).subtype)
  have hB : Continuous B :=
    continuous_subtype_val.comp (e.continuous.comp continuous_subtype_val)
  obtain ⟨C, _, hC, hgen⟩ := Q.val.1.annihilator_compactlyGenerated
  obtain ⟨D, hD⟩ := exists_openCompactlyGeneratedSubgroup_contains (hC.image hB)
  have hmap : Subgroup.map B ⊤ ≤ D.val := by
    rw [← hgen, MonoidHom.map_closure]
    exact (Subgroup.closure_le _).mpr hD
  obtain ⟨J, hJ⟩ := exists_modulatedBruhat_upper_eq_top m hm hms
  let P := LCAStructuralPair.ofDual J D (hJ ▸ le_top)
  obtain ⟨p⟩ := P.quotient_elementary
  refine ⟨⟨⟨P, p⟩, hJ⟩, fun x hx ↦ ?_⟩
  change (QuotientGroup.mk x : G ⧸ H) ∈ K
  rw [← lcaDualAnnihilator_annihilator K Q.val.1.kernel_closed]
  apply (mem_lcaDualAnnihilator_iff _ _).mpr
  intro χ
  have hχ : B χ ∈ D.val := hmap ⟨χ, Subgroup.mem_top _, rfl⟩
  have hz := (mem_lcaDualAnnihilator_iff _ _).mp hx ⟨B χ, hχ⟩
  change (B χ) x = 1 at hz
  exact (he χ.val x).symm.trans hz

end Image

end

end Masullo
