import BruhatSchwartzStrict
import ElementarySchwartzTranslationContinuity

open Filter Function Set Topology

namespace Masullo

noncomputable section

set_option maxHeartbeats 1500000

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G]

/-- A translate on the upper subgroup is realized by translating in its
elementary quotient. The same identity holds outside the upper subgroup
by extension by zero. -/
theorem BruhatSchwartzStage.realize_translate (p : BruhatSchwartzStage G)
    (g : p.1.upper.val) (f : p.Space) :
    p.realize (elementarySchwartz_translate (p.1.stageCoordinates p.2 g).toAdd f) =
      fun x ↦ p.realize f (x * g.val) := by
  funext x
  by_cases hx : x ∈ p.1.upper.val
  · let y : p.1.upper.val := ⟨x, hx⟩
    change p.realize _ y.val = p.realize f (y * g).val
    rw [p.1.realizeSchwartz_apply_of_mem, p.1.realizeSchwartz_apply_of_mem,
      elementarySchwartz_translate_apply, map_mul]
    rfl
  · have hnot : x * g.val ∉ p.1.upper.val := by
      intro h
      exact hx (by simpa using p.1.upper.val.mul_mem h (p.1.upper.val.inv_mem g.property))
    rw [p.1.realizeSchwartz_apply_of_not_mem p.2 _ x hx,
      p.1.realizeSchwartz_apply_of_not_mem p.2 _ _ hnot]

/-- Any stage can be refined to an upper subgroup containing the translator. -/
private theorem exists_stage_refinement_containing
    (p : BruhatSchwartzStage G) (g : G) :
    ∃ q : BruhatSchwartzStage G, p.1 ≤ q.1 ∧ g ∈ q.1.upper.val := by
  obtain ⟨P, hP, hg⟩ := p.1.exists_same_kernel_contains g
  letI := (openCompactlyGeneratedSubgroups_colimit (G := G)).1
  obtain ⟨J, hpJ, hPJ⟩ := exists_ge_ge p.1.upper P.upper
  let Q : LCAStructuralPair G :=
    ⟨J, p.1.kernel, p.1.kernel_closed, p.1.annihilator_open,
      p.1.annihilator_compactlyGenerated, p.1.kernel_le.trans hpJ⟩
  obtain ⟨e⟩ := Q.quotient_elementary
  exact ⟨⟨Q, e⟩, ⟨hpJ, le_rfl⟩, hPJ hg⟩

/-- A compact set of translators can be placed in the upper subgroup of one
refined stage. This uses the open upper subgroups and a finite subcover. -/
theorem exists_stage_refinement_containing_compact (p : BruhatSchwartzStage G)
    {K : Set G} (hK : IsCompact K) :
    ∃ q : BruhatSchwartzStage G, p.1 ≤ q.1 ∧ K ⊆ q.1.upper.val := by
  classical
  choose q hp hq using exists_stage_refinement_containing p
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover
    (fun g ↦ (q g).1.upper.val : G → Set G)
    (fun g ↦ (q g).1.upper.property.1)
    (fun g _ ↦ mem_iUnion.mpr ⟨g, hq g⟩)
  letI := (openCompactlyGeneratedSubgroups_colimit (G := G)).1
  have hupper (t : Finset G) :
      ∃ J : OpenCompactlyGeneratedSubgroups G, p.1.upper ≤ J ∧ ∀ g ∈ t, (q g).1.upper ≤ J := by
    induction t using Finset.induction_on with
    | empty => exact ⟨p.1.upper, le_rfl, by simp⟩
    | @insert g t _ ih =>
      obtain ⟨J, hpJ, htJ⟩ := ih
      obtain ⟨L, hJL, hgL⟩ := exists_ge_ge J (q g).1.upper
      refine ⟨L, hpJ.trans hJL, fun x hx ↦ ?_⟩
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hgL
      · exact (htJ x hx).trans hJL
  obtain ⟨J, hpJ, hqJ⟩ := hupper s
  let P : LCAStructuralPair G :=
    ⟨J, p.1.kernel, p.1.kernel_closed, p.1.annihilator_open,
      p.1.annihilator_compactlyGenerated, p.1.kernel_le.trans hpJ⟩
  obtain ⟨e⟩ := P.quotient_elementary
  refine ⟨⟨P, e⟩, ⟨hpJ, le_rfl⟩, fun x hx ↦ ?_⟩
  obtain ⟨g, hg⟩ := mem_iUnion.mp (hs hx)
  obtain ⟨hgs, hxg⟩ := mem_iUnion.mp hg
  exact hqJ g hgs hxg

private theorem bruhatSchwartz_translate_mem
    (g : G) (f : BruhatSchwartz G) :
    (fun x ↦ f.val (x * g)) ∈ bruhatSchwartzSubmodule (G := G) := by
  obtain ⟨p, u, hu⟩ := f.property
  obtain ⟨q, hpq, hqg⟩ := exists_stage_refinement_containing p g
  let z : q.1.upper.val := ⟨g, hqg⟩
  let v := BruhatSchwartzStage.transition p q hpq u
  refine ⟨q, elementarySchwartz_translate (q.1.stageCoordinates q.2 z).toAdd v, ?_⟩
  rw [q.realize_translate z v]
  have hv : q.realize v = p.realize u :=
    congrArg Subtype.val (BruhatSchwartzStage.inclusion_transition p q hpq u)
  rw [hv, hu]

/-- Each fixed left translation is continuous on the full Schwartz–Bruhat
space with its final locally convex topology. -/
def bruhatSchwartz_translate (g : G) : BruhatSchwartz G →L[ℂ] BruhatSchwartz G := by
  let L : BruhatSchwartz G →ₗ[ℂ] BruhatSchwartz G :=
    { toFun := fun f ↦ ⟨fun x ↦ f.val (x * g⁻¹), bruhatSchwartz_translate_mem g⁻¹ f⟩
      map_add' _ _ := Subtype.ext rfl
      map_smul' _ _ := Subtype.ext rfl }
  refine ⟨L, ?_⟩
  apply (locallyConvexFinal_continuous_iff (fun p : BruhatSchwartzStage G ↦ p.inclusion) L).mpr
  intro p
  obtain ⟨q, hpq, hqg⟩ := exists_stage_refinement_containing p g⁻¹
  let z : q.1.upper.val := ⟨g⁻¹, hqg⟩
  let T := elementarySchwartz_translate (q.1.stageCoordinates q.2 z).toAdd
  let M := (q.inclusionCLM.comp T).comp (BruhatSchwartzStage.transition p q hpq)
  have hM : (L.comp p.inclusion : p.Space → BruhatSchwartz G) = M := by
    funext f
    apply Subtype.ext
    change (fun x ↦ p.realize f (x * g⁻¹)) =
      q.realize (T (BruhatSchwartzStage.transition p q hpq f))
    rw [q.realize_translate z]
    have hv : q.realize (BruhatSchwartzStage.transition p q hpq f) = p.realize f :=
      congrArg Subtype.val (BruhatSchwartzStage.inclusion_transition p q hpq f)
    rw [hv]
  rw [hM]
  exact M.continuous

@[simp] theorem bruhatSchwartz_translate_apply (g : G) (f : BruhatSchwartz G) (x : G) :
    (bruhatSchwartz_translate g f).val x = f.val (g⁻¹ * x) := by
  change f.val (x * g⁻¹) = f.val (g⁻¹ * x)
  rw [mul_comm]

set_option maxHeartbeats 1800000 in
/-- Left translation is jointly continuous on the full Schwartz–Bruhat
space. Around any translating element, each source stage refines into an
open upper subgroup containing that element. -/
theorem continuous_bruhatSchwartz_translate :
    Continuous (fun z : G × BruhatSchwartz G => bruhatSchwartz_translate z.1 z.2) := by
  let L (g : G) := (bruhatSchwartz_translate g).toLinearMap
  apply locallyConvexFinal_continuous_family (fun p : BruhatSchwartzStage G => p.inclusion) L
  · intro f
    obtain ⟨p, u, hu⟩ := f.property
    exact ⟨p, u, Subtype.ext hu⟩
  · intro p
    apply continuous_iff_continuousAt.mpr
    rintro ⟨g, u⟩
    obtain ⟨q, hpq, hg⟩ := exists_stage_refinement_containing p g⁻¹
    let U : Set (G × p.Space) := {z | z.1 ∈ q.1.upper.val}
    have hU : IsOpen U := q.1.upper.property.1.preimage continuous_fst
    have hgU : (g, u) ∈ U := by
      change g ∈ q.1.upper.val
      simpa only [inv_inv] using q.1.upper.val.inv_mem hg
    have hC : ContinuousOn (fun z : G × p.Space => L z.1 (p.inclusion z.2)) U := by
      apply continuousOn_iff_continuous_domRestrict.mpr
      let T (z : U) : q.1.upper.val := ⟨z.val.1⁻¹, q.1.upper.val.inv_mem z.property⟩
      have hT : Continuous T :=
        ((continuous_fst.comp continuous_subtype_val).inv).subtype_mk _
      let R := p.transition q hpq
      have ht : Continuous (fun z : U => (q.1.stageCoordinates q.2 (T z)).toAdd) :=
        continuous_toAdd.comp ((q.1.stageCoordinates q.2).continuous.comp hT)
      have hr : Continuous (fun z : U => R z.val.2) :=
        R.continuous.comp (continuous_snd.comp continuous_subtype_val)
      have hc : Continuous (fun z : U =>
          q.inclusionCLM (elementarySchwartz_translate (q.1.stageCoordinates q.2 (T z)).toAdd
            (R z.val.2))) :=
        q.inclusionCLM.continuous.comp
          ((@continuous_elementarySchwartz_translate q.2.realDim q.2.torusDim q.2.latticeRank
            q.2.finiteFactor q.2.finiteGroup q.2.finiteTopology q.2.finiteDiscrete (Finite.of_fintype _)).comp
            (ht.prodMk hr))
      apply hc.congr
      intro z
      apply Subtype.ext
      have he := q.realize_translate (T z) (R z.val.2)
      have hr₀ : q.realize (R z.val.2) = p.realize z.val.2 :=
        congrArg Subtype.val (p.inclusion_transition q hpq z.val.2)
      rw [hr₀] at he
      exact he
    exact (hC (g, u) hgU).continuousAt (hU.mem_nhds hgU)

set_option maxHeartbeats 800000 in
/-- Proposition D.1.9.2. On a compact set of shifts, one neighborhood of
zero suffices for every translate. -/
theorem bruhatSchwartz_translate_uniform_compact {K : Set G} (hK : IsCompact K)
    {U : Set (BruhatSchwartz G)} (hU : U ∈ 𝓝 (0 : BruhatSchwartz G)) :
    ∃ V ∈ 𝓝 (0 : BruhatSchwartz G), ∀ g ∈ K, ∀ f ∈ V, bruhatSchwartz_translate g f ∈ U := by
  obtain ⟨W, hWU, hWo, hW₀⟩ := mem_nhds_iff.mp hU
  let V₀ := (fun z : G × BruhatSchwartz G => bruhatSchwartz_translate z.1 z.2) ⁻¹' W
  have hV : IsOpen V₀ := hWo.preimage continuous_bruhatSchwartz_translate
  have hsub : K ×ˢ ({0} : Set (BruhatSchwartz G)) ⊆ V₀ := by
    rintro ⟨g, f⟩ ⟨_, hf⟩
    change f = 0 at hf
    change bruhatSchwartz_translate g f ∈ W
    simpa only [hf, map_zero] using hW₀
  obtain ⟨O, V, _, hVo, hKO, hV₀, hOV⟩ :=
    generalized_tube_lemma hK isCompact_singleton hV hsub
  refine ⟨V, hVo.mem_nhds (hV₀ (mem_singleton 0)), fun g hg f hf => ?_⟩
  exact hWU (hOV (show (g,f) ∈ O ×ˢ V from ⟨hKO hg, hf⟩))

end

end Masullo
