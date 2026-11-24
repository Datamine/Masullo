/-
The structural quotient and fibre-measure arguments adapt RiemannMasullo
AppD_SchwartzBruhat/Sec1c.lean at a1d61084d11ef14e3119178113488c654be4da80
(Apache-2.0). See External/PROVENANCE.md and External/RiemannMasullo.LICENSE.
-/
import BruhatFourierTransform
import TorusLocalCharts
import WeilFourier

open Filter Function MeasureTheory Set Topology

namespace Masullo

noncomputable section

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G]
  (K : Subgroup G) (hK : IsClosed (K : Set G))

private def closedQuotientMap : G →ₜ* G ⧸ K :=
  ⟨QuotientGroup.mk' K, QuotientGroup.continuous_mk⟩

/-- Properness of an ambient quotient is equivalent to compactness of
the subgroup. Structural quotients use compact kernels even when the
ambient subgroup in distributional Poisson summation is noncompact. -/
theorem lcaQuotient_isProper_iff :
    IsProperMap (QuotientGroup.mk' K) ↔ IsCompact (K : Set G) := by
  constructor
  · intro h
    have hc := h.isCompact_preimage (isCompact_singleton (x := (1 : G ⧸ K)))
    rwa [show (QuotientGroup.mk' K) ⁻¹' {1} = (K : Set G) from QuotientGroup.preimage_mk_one K] at hc
  · intro h
    exact LCAStructuralPair.proper_of_open_surjective_compact_kernel (closedQuotientMap K)
      (QuotientGroup.mk'_surjective K) QuotientGroup.isOpenMap_coe (by
        change IsCompact ((QuotientGroup.mk' K).ker : Set G)
        rwa [QuotientGroup.ker_mk'])

include hK

/-- Annihilating the image of a subgroup in a closed quotient is equivalent
to annihilating both original subgroups. -/
private theorem quotientImage_annihilatorEquiv (C : Subgroup G) :
    Nonempty (lcaAnnihilator (C.map (closedQuotientMap K).toMonoidHom) ≃ₜ*
      (lcaAnnihilator K).comap (lcaAnnihilator C).subtype) := by
  letI : IsClosed (K : Set G) := hK
  obtain ⟨e, he⟩ := lcaQuotientDual_equiv_annihilator K hK
  let M := (lcaAnnihilator K).comap (lcaAnnihilator C).subtype
  let N := lcaAnnihilator (C.map (closedQuotientMap K).toMonoidHom)
  have hN (χ : N) : (e χ.val).val ∈ lcaAnnihilator C := by
    apply (mem_lcaAnnihilator_iff C _).mpr
    intro c
    rw [he]
    exact (mem_lcaAnnihilator_iff _ _).mp χ.property
      ⟨(closedQuotientMap K) c.val, ⟨c.val, c.property, rfl⟩⟩
  have hM (χ : M) : e.symm ⟨χ.val.val, χ.property⟩ ∈ N := by
    apply (mem_lcaAnnihilator_iff _ _).mpr
    rintro ⟨_, c, hc, rfl⟩
    have h := he (e.symm ⟨χ.val.val, χ.property⟩) c
    rw [e.apply_symm_apply] at h
    change χ.val.val c = e.symm ⟨χ.val.val, χ.property⟩ (QuotientGroup.mk c) at h
    exact h.symm.trans ((mem_lcaAnnihilator_iff C _).mp χ.val.property ⟨c, hc⟩)
  refine ⟨{
    toFun := fun χ => ⟨⟨(e χ.val).val, hN χ⟩, (e χ.val).property⟩
    invFun := fun χ => ⟨e.symm ⟨χ.val.val, χ.property⟩, hM χ⟩
    left_inv := fun χ => Subtype.ext (e.symm_apply_apply χ.val)
    right_inv := ?_
    map_mul' := ?_
    continuous_toFun := ?_
    continuous_invFun := ?_ }⟩
  · intro χ
    apply Subtype.ext
    apply Subtype.ext
    change (e (e.symm ⟨χ.val.val, χ.property⟩)).val = χ.val.val
    rw [e.apply_symm_apply]
  · intro χ ψ
    apply Subtype.ext
    apply Subtype.ext
    change (e (χ.val * ψ.val)).val = (e χ.val).val * (e ψ.val).val
    rw [map_mul]
    rfl
  · exact ((continuous_subtype_val.comp
      (e.continuous.comp continuous_subtype_val)).subtype_mk hN).subtype_mk _
  · exact (e.symm.continuous.comp
      ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)).subtype_mk hM

set_option maxHeartbeats 1100000 in
/-- Images of both subgroups of a structural pair form a structural pair in
the quotient by any closed subgroup. The compact kernel remains compact. -/
theorem LCAStructuralPair.exists_quotientPair (P : LCAStructuralPair G) :
    ∃ Q : LCAStructuralPair (G ⧸ K),
      Q.upper.val = P.upper.val.map (QuotientGroup.mk' K) ∧
      Q.kernel = P.kernel.map (QuotientGroup.mk' K) := by
  letI : IsClosed (K : Set G) := hK
  let q := closedQuotientMap K
  let J := P.upper.val
  let C := P.kernel
  let J' := J.map q.toMonoidHom
  let C' := C.map q.toMonoidHom
  have ho : IsOpen (J' : Set (G ⧸ K)) :=
    QuotientGroup.isOpenMap_coe _ P.upper.property.1
  have hc : IsCompact (C : Set G) := by
    rw [← lcaDualAnnihilator_annihilator C P.kernel_closed]
    exact isCompact_lcaDualAnnihilator_of_isOpen _ P.annihilator_open
  have hc' : IsCompact (C' : Set (G ⧸ K)) := hc.image q.continuous
  have hJ' : IsCompactlyGeneratedGroup J' := by
    let j := q.toMonoidHom.subgroupMap J
    have hj : Continuous j := (q.continuous.comp continuous_subtype_val).subtype_mk _
    have hjo : IsOpenMap j := by
      intro U hU
      have hO : IsOpen (q '' (Subtype.val '' U)) :=
        QuotientGroup.isOpenMap_coe _ (P.upper.property.1.isOpenEmbedding_subtypeVal.isOpenMap _ hU)
      have he : j '' U = Subtype.val ⁻¹' (q '' (Subtype.val '' U)) := by
        ext y
        constructor
        · rintro ⟨x, hx, rfl⟩
          exact ⟨x.val, ⟨x, hx, rfl⟩, rfl⟩
        · rintro ⟨_, ⟨x, hx, rfl⟩, hy⟩
          exact ⟨x, hx, Subtype.ext hy⟩
      rw [he]
      exact hO.preimage continuous_subtype_val
    obtain ⟨U, hU, hUc, hGen⟩ := P.upper.property.2
    refine ⟨j '' U, ?_, hUc.image hj, ?_⟩
    · have h := hjo.image_mem_nhds hU
      simpa only [map_one] using h
    · change Subgroup.closure (j '' U) = ⊤
      rw [← MonoidHom.map_closure, hGen,
        Subgroup.map_top_of_surjective _ (q.toMonoidHom.subgroupMap_surjective J)]
  have hKclosed : IsClosed (lcaAnnihilator K : Set (PontryaginDual G)) := by
    let r := PontryaginDual.map (⟨K.subtype, continuous_subtype_val⟩ : K →ₜ* G)
    change IsClosed (r ⁻¹' {1})
    exact isClosed_singleton.preimage r.continuous
  letI : LocallyCompactSpace (lcaAnnihilator C) :=
    P.annihilator_open.isOpenEmbedding_subtypeVal.locallyCompactSpace
  have hgen := isCompactlyGeneratedGroup_closedSubgroup P.annihilator_compactlyGenerated
    ((lcaAnnihilator K).comap (lcaAnnihilator C).subtype)
    (hKclosed.preimage continuous_subtype_val)
  obtain ⟨e⟩ := quotientImage_annihilatorEquiv K hK C
  exact ⟨⟨⟨J', ho, hJ'⟩, C', hc'.isClosed, isOpen_lcaAnnihilator C' hc',
    compactGeneration_transport e.symm hgen, Subgroup.map_mono P.kernel_le⟩, rfl, rfl⟩

omit hK

omit [T2Space G] [LocallyCompactSpace G] in
set_option maxHeartbeats 1300000 in
/-- The map on elementary structural quotients is continuous, open and
surjective. Its kernel is the image of the intersection with the ambient
closed subgroup under the physical stage quotient. -/
theorem LCAStructuralPair.exists_quotientStageMap (P : LCAStructuralPair G)
    (Q : LCAStructuralPair (G ⧸ K))
    (hJ : Q.upper.val = P.upper.val.map (QuotientGroup.mk' K))
    (hC : Q.kernel = P.kernel.map (QuotientGroup.mk' K)) :
    ∃ a : P.StageQuotient →ₜ* Q.StageQuotient,
      IsOpenMap a ∧ Surjective a ∧
      a.toMonoidHom.ker = (K.comap P.upper.val.subtype).map
        (QuotientGroup.mk' (P.kernel.comap P.upper.val.subtype)) ∧
      ∀ (x : P.upper.val) (hx : QuotientGroup.mk x.val ∈ Q.upper.val),
        a (QuotientGroup.mk x) = QuotientGroup.mk ⟨QuotientGroup.mk x.val, hx⟩ := by
  let J := P.upper.val
  let C := P.kernel
  let N := C.comap J.subtype
  let N' := Q.kernel.comap Q.upper.val.subtype
  let q := closedQuotientMap K
  let qJ : J →* Q.upper.val :=
    (q.toMonoidHom.comp J.subtype).codRestrict Q.upper.val (fun x => by
      rw [hJ]
      exact ⟨x.val, x.property, rfl⟩)
  have hqJ (x : J) : (qJ x).val = QuotientGroup.mk x.val := rfl
  have hc : Continuous qJ := (q.continuous.comp continuous_subtype_val).subtype_mk _
  have ho : IsOpenMap qJ := by
    intro U hU
    have hO : IsOpen (q '' (Subtype.val '' U)) :=
      QuotientGroup.isOpenMap_coe _ (P.upper.property.1.isOpenEmbedding_subtypeVal.isOpenMap _ hU)
    have hEq : qJ '' U = (Subtype.val : Q.upper.val → G ⧸ K) ⁻¹' (q '' (Subtype.val '' U)) := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x.val, ⟨x, hx, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨x, hx, rfl⟩, hy⟩
        exact ⟨x, hx, Subtype.ext hy⟩
    rw [hEq]
    exact hO.preimage continuous_subtype_val
  have hs : Surjective qJ := by
    rintro ⟨y, hy⟩
    rw [hJ] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨⟨x, hx⟩, rfl⟩
  let f := (QuotientGroup.mk' N').comp qJ
  have hN : N ≤ f.ker := by
    intro x hx
    change QuotientGroup.mk (qJ x) = 1
    apply (QuotientGroup.eq_one_iff _).mpr
    change (qJ x).val ∈ Q.kernel
    rw [hqJ, hC]
    exact ⟨x.val, hx, rfl⟩
  let a := QuotientGroup.lift N f hN
  have ha (x : J) : a (QuotientGroup.mk x) = QuotientGroup.mk (qJ x) := rfl
  have hacomp : (a ∘ (QuotientGroup.mk : J → P.StageQuotient)) =
      (QuotientGroup.mk' N') ∘ qJ := funext ha
  have hac : Continuous a := by
    apply (QuotientGroup.isQuotientMap_mk N).continuous_iff.mpr
    rw [hacomp]
    exact QuotientGroup.continuous_mk.comp hc
  refine ⟨⟨a, hac⟩, ?_, ?_, ?_, ?_⟩
  · intro U hU
    have he : a '' U = ((QuotientGroup.mk' N') ∘ qJ) ''
        ((QuotientGroup.mk : J → P.StageQuotient) ⁻¹' U) := by
      rw [← hacomp, image_comp, image_preimage_eq _ QuotientGroup.mk_surjective]
    change IsOpen (a '' U)
    rw [he, image_comp]
    exact QuotientGroup.isOpenMap_coe _ (ho _ (hU.preimage QuotientGroup.continuous_mk))
  · intro z
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective z
    obtain ⟨x, rfl⟩ := hs y
    exact ⟨QuotientGroup.mk x, rfl⟩
  · ext y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    change a (QuotientGroup.mk x) = 1 ↔
      QuotientGroup.mk x ∈ (K.comap J.subtype).map (QuotientGroup.mk' N)
    rw [ha, QuotientGroup.eq_one_iff]
    change (qJ x).val ∈ Q.kernel ↔ _
    rw [hqJ, hC]
    constructor
    · rintro ⟨c, hc, he⟩
      have hk : c⁻¹ * x.val ∈ K := QuotientGroup.eq.mp he
      have hj : c⁻¹ * x.val ∈ J := J.mul_mem (J.inv_mem (P.kernel_le hc)) x.property
      refine ⟨⟨c⁻¹ * x.val, hj⟩, hk, ?_⟩
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq]
      change (c⁻¹ * x.val)⁻¹ * x.val ∈ C
      simpa using hc
    · rintro ⟨k, hk, h⟩
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq] at h
      refine ⟨(k⁻¹ * x).val, h, ?_⟩
      change (QuotientGroup.mk ((k⁻¹ * x : J) : G) : G ⧸ K) = QuotientGroup.mk x.val
      rw [QuotientGroup.eq]
      have he : ((k⁻¹ * x : J) : G)⁻¹ * x.val = k.val := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, inv_inv]
        rw [mul_assoc, mul_comm (k : G), inv_mul_cancel_left]
      rwa [he]
  · intro x hx
    exact ha x

include hK

set_option maxHeartbeats 1400000 in
/-- Images of source structural pairs are cofinal among structural pairs of
the quotient. The compact kernel can be chosen inside the pullback of a
neighborhood with no nontrivial cyclic subgroups in the target stage. -/
theorem LCAStructuralPair.exists_cofinal_quotientPair (B : LCAStructuralPair (G ⧸ K)) :
    ∃ P : LCAStructuralPair G, ∃ Q : LCAStructuralPair (G ⧸ K),
      Q.upper.val = P.upper.val.map (QuotientGroup.mk' K) ∧
      Q.kernel = P.kernel.map (QuotientGroup.mk' K) ∧ B ≤ Q := by
  letI : IsClosed (K : Set G) := hK
  let q := closedQuotientMap K
  have hq : IsOpenQuotientMap q := QuotientGroup.isOpenQuotientMap_mk
  let J := B.upper.val
  let N := B.kernel.comap J.subtype
  letI : LocallyCompactSpace J := B.upper.property.1.locallyCompactSpace
  letI : IsClosed (N : Set J) := B.kernel_closed.preimage continuous_subtype_val
  letI : LocallyCompactSpace B.StageQuotient :=
    (QuotientGroup.isOpenQuotientMap_mk (N := N)).locallyCompactSpace
  have hE : IsLocallyEuclidean B.StageQuotient :=
    (lca_elementary_iff.mpr B.quotient_elementary).2
  obtain ⟨W, hW, hPow⟩ := exists_nhds_one_of_isLocallyEuclidean hE
  let π : J →* B.StageQuotient := QuotientGroup.mk' N
  have hPre : π ⁻¹' W ∈ 𝓝 (1 : J) :=
    (QuotientGroup.continuous_mk (N := N) : Continuous π).continuousAt.preimage_mem_nhds
      (by change W ∈ 𝓝 (π 1); rwa [map_one])
  have hImage : Subtype.val '' (π ⁻¹' W) ∈ 𝓝 (1 : G ⧸ K) :=
    B.upper.property.1.isOpenEmbedding_subtypeVal.isOpenMap.image_mem_nhds hPre
  obtain ⟨A, hA⟩ := exists_lcaDualAnnihilator_subset_nhds
    (q.continuous.continuousAt.preimage_mem_nhds (show _ ∈ 𝓝 (q 1) by
      rw [map_one]; exact hImage))
  let C := lcaDualAnnihilator A.val
  have hsmall : C.map q.toMonoidHom ≤ B.kernel := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, _, hy⟩ := hA hx
    change y.val = q x at hy
    change q x ∈ B.kernel
    rw [← hy]
    change y ∈ N
    apply (QuotientGroup.eq_one_iff y).mp
    change π y = 1
    apply hPow
    intro n
    rw [← map_pow]
    obtain ⟨z, hz, hzy⟩ := hA (C.pow_mem hx n)
    change z.val = q (x ^ n) at hzy
    exact (Subtype.ext (by simpa only [map_pow, Subgroup.coe_pow, hy] using hzy) :
      z = y ^ n) ▸ hz
  obtain ⟨D, _, hDc, hDgen⟩ := B.upper.property.2
  let I := OpenCompactlyGeneratedSubgroups G
  letI : IsDirectedOrder I := (openCompactlyGeneratedSubgroups_colimit (G := G)).1
  letI : Nonempty I :=
    ⟨((openCompactlyGeneratedSubgroups_colimit (G := G)).2.1 1).choose⟩
  let V (i : I) := q '' (i.val : Set G)
  have hcover : Subtype.val '' D ⊆ ⋃ i, V i := by
    rintro _ ⟨x, _, rfl⟩
    obtain ⟨g, hg⟩ := hq.surjective x.val
    obtain ⟨i, hi⟩ := (openCompactlyGeneratedSubgroups_colimit (G := G)).2.1 g
    exact mem_iUnion.mpr ⟨i, g, hi, hg⟩
  obtain ⟨i, hi⟩ := (hDc.image continuous_subtype_val).elim_directed_cover V
    (fun j ↦ hq.isOpenMap _ j.property.1) hcover
    (directed_of_isDirected_le (fun _ _ h ↦ image_mono h))
  have hD : D ⊆ ((i.val.map q.toMonoidHom).comap J.subtype : Set J) :=
    fun x hx ↦ hi ⟨x, hx, rfl⟩
  have htop : ⊤ ≤ (i.val.map q.toMonoidHom).comap J.subtype :=
    hDgen ▸ (Subgroup.closure_le _).mpr hD
  obtain ⟨L, hL⟩ := exists_openCompactlyGeneratedSubgroup_contains
    (isCompact_lcaDualAnnihilator_of_isOpen A.val A.property.1)
  obtain ⟨M, hiM, hLM⟩ := exists_ge_ge i L
  let P : LCAStructuralPair G := .ofDual M A (hL.trans hLM)
  obtain ⟨Q, hJ, hC⟩ := P.exists_quotientPair K hK
  refine ⟨P, Q, hJ, hC, ?_, ?_⟩
  · change J ≤ Q.upper.val
    rw [hJ]
    have hJi : J ≤ i.val.map q.toMonoidHom :=
      fun x hx ↦ htop (Subgroup.mem_top (⟨x, hx⟩ : J))
    exact hJi.trans (Subgroup.map_mono hiM)
  · change Q.kernel ≤ B.kernel
    rwa [hC]

end
end Masullo
