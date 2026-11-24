import BruhatSchwartzStrict

open Filter Function Set Topology

namespace Masullo

noncomputable section

set_option maxHeartbeats 1500000

/-- The complement of distributional support consists of points with an
open neighborhood on which all supported test functions are annihilated. -/
def distributionVanishingLocus {X V : Type*} [TopologicalSpace X]
    (test : V → X → ℂ) (T : V → ℂ) : Set X :=
  {x | ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
    ∀ f : V, tsupport (test f) ⊆ U → T f = 0}

theorem isOpen_distributionVanishingLocus {X V : Type*} [TopologicalSpace X]
    (test : V → X → ℂ) (T : V → ℂ) :
    IsOpen (distributionVanishingLocus test T) := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  obtain ⟨U, hU, hxU, hT⟩ := hx
  exact mem_of_superset (hU.mem_nhds hxU) fun y hy ↦ ⟨U, hU, hy, hT⟩

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G]

namespace BruhatSchwartzStage

/-- Read a stage test as a function on the actual structural quotient. -/
def quotientTest (p : BruhatSchwartzStage G) (f : p.Space) (y : p.1.StageQuotient) : ℂ :=
  f (p.2.equiv y).toAdd

/-- The extension by zero has support inside the image of the pullback of
the quotient support. The upper subgroup is closed as well as open. -/
theorem realize_tsupport_subset (p : BruhatSchwartzStage G) (f : p.Space) :
    tsupport (p.realize f) ⊆ (Subtype.val : p.1.upper.val → G) ''
      ((QuotientGroup.mk : p.1.upper.val → p.1.StageQuotient) ⁻¹' tsupport (p.quotientTest f)) := by
  have hclosed : IsClosed (p.1.upper.val : Set G) :=
    p.1.upper.val.isClosed_of_isOpen p.1.upper.property.1
  apply closure_minimal _ (hclosed.isClosedMap_subtype_val _
    (isClosed_closure.preimage QuotientGroup.continuous_mk))
  intro x hx
  have hx' : x ∈ p.1.upper.val := by
    by_contra h
    exact hx (p.1.realizeSchwartz_apply_of_not_mem p.2 f x h)
  let y : p.1.upper.val := ⟨x, hx'⟩
  refine ⟨y, subset_tsupport _ ?_, rfl⟩
  change f (p.1.stageCoordinates p.2 y).toAdd ≠ 0
  rw [← p.1.realizeSchwartz_apply_of_mem p.2 f y]
  exact hx

end BruhatSchwartzStage

/-- A neighborhood of a point contains a neighborhood pulled back from
some elementary structural quotient of an open upper subgroup. -/
theorem exists_structuralQuotient_neighborhood {x : G} {U : Set G}
    (hU : U ∈ 𝓝 x) :
    ∃ (P : LCAStructuralPair G) (y : P.upper.val) (V : Set P.StageQuotient),
      y.val = x ∧ IsOpen V ∧ QuotientGroup.mk y ∈ V ∧
      (Subtype.val : P.upper.val → G) '' ((QuotientGroup.mk : P.upper.val → P.StageQuotient) ⁻¹' V)
        ⊆ U := by
  obtain ⟨J, hxJ⟩ := (openCompactlyGeneratedSubgroups_colimit (G := G)).2.1 x
  have hpre : (fun g : G ↦ g * x) ⁻¹' U ∈ 𝓝 (1 : G) := by
    have hc : ContinuousAt (fun g : G ↦ g * x) (1 : G) := continuousAt_id.mul continuousAt_const
    exact hc (by simpa only [one_mul] using hU)
  have hJ : (J.val : Set G) ∈ 𝓝 (1 : G) := J.property.1.mem_nhds J.val.one_mem
  obtain ⟨W, hW, hWone, hWW⟩ := exists_open_nhds_one_mul_subset (inter_mem hpre hJ)
  have hWsub : W ⊆ (fun g : G ↦ g * x) ⁻¹' U ∩ (J.val : Set G) := fun g hg ↦
    hWW (Set.mem_mul.mpr ⟨g, hg, 1, hWone, mul_one g⟩)
  obtain ⟨H, hH⟩ := exists_lcaDualAnnihilator_subset_nhds (hW.mem_nhds hWone)
  let P := LCAStructuralPair.ofDual J H (fun g hg ↦ (hWsub (hH hg)).2)
  let y : P.upper.val := ⟨x, hxJ⟩
  let B : Set P.upper.val := (fun t : P.upper.val ↦ t.val / x) ⁻¹' W
  let q : P.upper.val → P.StageQuotient := QuotientGroup.mk
  let V : Set P.StageQuotient := q '' B
  have hB : IsOpen B := hW.preimage (continuous_subtype_val.div_const x)
  have hy : y ∈ B := by simpa [B, y] using hWone
  refine ⟨P, y, V, rfl, QuotientGroup.isOpenMap_coe _ hB, mem_image_of_mem q hy, ?_⟩
  rintro _ ⟨t, ⟨s, hs, hst⟩, rfl⟩
  have hts : t / s ∈ P.kernel.comap P.upper.val.subtype :=
    QuotientGroup.eq_iff_div_mem.mp hst.symm
  have hk : t.val / s.val ∈ W := hH hts
  have hs' : s.val / x ∈ W := hs
  have ht : t.val / x ∈ (fun g : G ↦ g * x) ⁻¹' U ∩ (J.val : Set G) := by
    apply hWW
    exact Set.mem_mul.mpr ⟨t.val / s.val, hk, s.val / x, hs', div_mul_div_cancel _ _ _⟩
  exact (by simpa only [mem_preimage, div_mul_cancel] using ht.1)

/-- D.1.8.4. Every point outside the support of a Schwartz–Bruhat
distribution is detected outside the support of one elementary stage
restriction. -/
theorem bruhatDistribution_vanishingLocus_subset_stage
    (T : BruhatSchwartz G →L[ℂ] ℂ) :
    distributionVanishingLocus (fun f : BruhatSchwartz G ↦ f.val) T ⊆
      {x | ∃ (p : BruhatSchwartzStage G) (y : p.1.upper.val), y.val = x ∧
        (QuotientGroup.mk y : p.1.StageQuotient) ∈
          distributionVanishingLocus p.quotientTest (T.comp p.inclusionCLM)} := by
  intro x hx
  obtain ⟨U, hU, hxU, hT⟩ := hx
  obtain ⟨P, y, V, hy, hV, hyV, hsub⟩ :=
    exists_structuralQuotient_neighborhood (hU.mem_nhds hxU)
  obtain ⟨e⟩ := P.quotient_elementary
  let p : BruhatSchwartzStage G := ⟨P, e⟩
  refine ⟨p, y, hy, V, hV, hyV, fun f hf ↦ ?_⟩
  exact hT (p.inclusionCLM f) ((p.realize_tsupport_subset f).trans
    ((image_mono (preimage_mono hf)).trans hsub))

end

end Masullo
