import BruhatSchwartzStrict
import StrictLimitCompleteness
import NuclearApproximation
import ElementarySchwartzStructure
import Mathlib.Analysis.LocallyConvex.Montel
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Analysis.LocallyConvex.ContinuousOfBounded

open Bornology Function Set Topology
open scoped Uniformity

namespace Masullo

noncomputable section

universe u

set_option maxHeartbeats 1500000

variable {G : Type u} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G]

/-- The barrelledness assertion of D.1.5.7. Lower semicontinuous seminorms
are continuous on each Fréchet stage, hence on the final topology. -/
theorem bruhatSchwartz_barrelled : BarrelledSpace ℂ (BruhatSchwartz G) := by
  constructor
  intro q hq
  apply locallyConvexFinal_seminorm_continuous (fun p : BruhatSchwartzStage G ↦ p.inclusion)
  intro p
  let X := p.Space
  obtain ⟨_, hp, hm, hc⟩ := elementarySchwartz_isFrechet
    (m := p.2.realDim) (n := p.2.torusDim) (r := p.2.latticeRank) (F := p.2.finiteFactor)
  let W := elementarySchwartz_withSeminorms
    (m := p.2.realDim) (n := p.2.torusDim) (r := p.2.latticeRank) (F := p.2.finiteFactor)
  letI : PolynormableSpace ℂ X := hp
  letI : TopologicalSpace.MetrizableSpace X := hm
  letI : CompleteSpace X := hc
  letI : ContinuousSMul ℂ X := W.continuousSMul
  haveI : (𝓤 X).IsCountablyGenerated := by
    rw [uniformity_eq_comap_nhds_zero X]
    infer_instance
  letI : BaireSpace X := BaireSpace.of_completelyPseudoMetrizable
  letI : BarrelledSpace ℂ X := inferInstance
  exact (q.comp p.inclusion).continuous_of_lowerSemicontinuous (hq.comp p.inclusionCLM.continuous)

/-- The bornologicality assertion of D.1.5.7 in the bounded linear map
form. Each Fréchet stage is first countable. -/
theorem bruhatSchwartz_linear_continuous_of_bounded
    {Y : Type*} [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y] [PolynormableSpace ℂ Y]
    (L : BruhatSchwartz G →ₗ[ℂ] Y)
    (hL : ∀ B : Set (BruhatSchwartz G), IsVonNBounded ℂ B → IsVonNBounded ℂ (L '' B)) :
    Continuous L := by
  letI : IsTopologicalAddGroup Y := (PolynormableSpace.withSeminorms ℂ Y).topologicalAddGroup
  apply (locallyConvexFinal_continuous_iff (fun p : BruhatSchwartzStage G ↦ p.inclusion) L).mpr
  intro p
  letI : TopologicalSpace.MetrizableSpace p.Space := (elementarySchwartz_isFrechet
    (m := p.2.realDim) (n := p.2.torusDim) (r := p.2.latticeRank) (F := p.2.finiteFactor)).2.2.1
  letI : ContinuousSMul ℂ p.Space := (PolynormableSpace.withSeminorms ℂ p.Space).continuousSMul
  apply LinearMap.continuous_of_locally_bounded
  intro C hC
  change IsVonNBounded ℂ ((fun x : p.Space ↦ L (p.inclusion x)) '' C)
  exact Set.image_image (⇑L) (⇑p.inclusion) C ▸ hL _ (hC.image p.inclusionCLM)

/-- Uniformity of the final locally convex Schwartz–Bruhat topology. -/
abbrev bruhatSchwartzUniformSpace : UniformSpace (BruhatSchwartz G) :=
  letI : IsTopologicalAddGroup (BruhatSchwartz G) :=
    (PolynormableSpace.withSeminorms ℂ (BruhatSchwartz G)).topologicalAddGroup
  IsTopologicalAddGroup.rightUniformSpace _

/-- Completeness in D.1.5.7, for the additive uniformity of the full
Schwartz–Bruhat topology. The cofinal strict stages are complete. -/
theorem bruhatSchwartz_complete [SecondCountableTopology G] :
    @CompleteSpace (BruhatSchwartz G) bruhatSchwartzUniformSpace := by
  obtain ⟨P, hP, hCov⟩ := lcaStructuralPairs_cofinalSequence (G := G)
  let b (n : ℕ) : BruhatSchwartzStage G := ⟨P n, Classical.choice (P n).quotient_elementary⟩
  let D := bruhatSchwartz_countablePresentation b hP hCov
  have hEmb (n : ℕ) : IsEmbedding (D.incl n) := (bruhatSchwartz_strict (G := G)).2.1 (b n)
  exact D.complete_of_strict
    (fun n ↦ (elementarySchwartz_isFrechet (m := (b n).2.realDim)
      (n := (b n).2.torusDim) (r := (b n).2.latticeRank) (F := (b n).2.finiteFactor)).2.2.2)
    hEmb (bruhatSchwartz_seminorm_continuous_of_cofinal b hCov)

/-- Every closed bounded subset of the second-countable Schwartz–Bruhat
space is complete. The intrinsic stage topology and the bounded set
comparison are the two clauses of D.1.5.6 used here. -/
theorem bruhatSchwartz_quasiComplete [SecondCountableTopology G] :
    @QuasiCompleteSpace ℂ (BruhatSchwartz G) _ bruhatSchwartzUniformSpace _ _ := by
  letI : UniformSpace (BruhatSchwartz G) := bruhatSchwartzUniformSpace
  letI : IsUniformAddGroup (BruhatSchwartz G) := isUniformAddGroup_of_addCommGroup
  obtain ⟨_, hEmb, hbound⟩ := bruhatSchwartz_strict (G := G)
  constructor
  intro B hB hclosed
  obtain ⟨p, C, _, hC⟩ := hbound B hB
  have hpre : p.inclusionCLM ⁻¹' B = C := by
    rw [← hC]
    exact preimage_image_eq _ (hEmb p).injective
  have hcClosed : IsClosed C := hpre ▸ hclosed.preimage p.inclusionCLM.continuous
  letI : CompleteSpace p.Space := completeSpace_elementarySchwartz
  have hcComplete := hcClosed.isComplete
  have hUni := AddMonoidHom.isUniformInducing_of_isInducing
    (f := p.inclusionCLM.toLinearMap.toAddMonoidHom) (hEmb p).isInducing
  rw [← hC]
  exact hUni.isComplete_iff.mpr hcComplete

private theorem bruhatSchwartz_bounded_subset_of_cofinal [SecondCountableTopology G]
    (b : ℕ → BruhatSchwartzStage G)
    (hCov : ∀ p : LCAStructuralPair G, ∃ n, p ≤ (b n).1)
    (B : Set (BruhatSchwartz G)) (hB : IsVonNBounded ℂ B) :
    ∃ (n : ℕ) (C : Set ((b n).Space)), IsVonNBounded ℂ C ∧
      B ⊆ (b n).inclusionCLM '' C := by
  obtain ⟨p, C, hC, hBC⟩ := (bruhatSchwartz_strict (G := G)).2.2 B hB
  obtain ⟨n, h⟩ := hCov p.1
  let L := BruhatSchwartzStage.transition p (b n) h
  refine ⟨n, L '' C, hC.image L, ?_⟩
  rw [← hBC]
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨L x, ⟨x, hx, rfl⟩, BruhatSchwartzStage.inclusion_transition p (b n) h x⟩

/-- Nuclearity of the elementary stages passes to the full structural limit. -/
theorem bruhatSchwartz_nuclear_of_stages [SecondCountableTopology G]
    (hN : ∀ p : BruhatSchwartzStage G, NuclearLocallyConvex.{u, 0} p.Space) :
    NuclearLocallyConvex.{u, u} (BruhatSchwartz G) := by
  obtain ⟨P, hP, hCov⟩ := lcaStructuralPairs_cofinalSequence (G := G)
  let b (n : ℕ) : BruhatSchwartzStage G := ⟨P n, Classical.choice (P n).quotient_elementary⟩
  letI : T2Space (BruhatSchwartz G) := bruhatSchwartz_t2
  exact (bruhatSchwartz_countablePresentation b hP hCov).nuclear_of_stages
    (fun n ↦ hN (b n)) (bruhatSchwartz_seminorm_continuous_of_cofinal b hCov)

/-- The primal nuclearity assertion of D.1.5.7 for the actual locally
convex Schwartz–Bruhat topology. -/
theorem bruhatSchwartz_nuclear [SecondCountableTopology G] :
    NuclearLocallyConvex.{u, u} (BruhatSchwartz G) :=
  bruhatSchwartz_nuclear_of_stages fun _ ↦ elementarySchwartz_nuclear

/-- Nuclearity of the elementary strong duals passes to the full strong dual
via the topology of compatible stage restrictions. -/
theorem bruhatSchwartz_strongDual_nuclear_of_stages [SecondCountableTopology G]
    (hN : ∀ p : BruhatSchwartzStage G, NuclearLocallyConvex.{u, 0} (StrongDual ℂ p.Space)) :
    NuclearLocallyConvex.{u, u} (StrongDual ℂ (BruhatSchwartz G)) := by
  obtain ⟨P, hP, hCov⟩ := lcaStructuralPairs_cofinalSequence (G := G)
  let b (n : ℕ) : BruhatSchwartzStage G := ⟨P n, Classical.choice (P n).quotient_elementary⟩
  let D := bruhatSchwartz_countablePresentation b hP hCov
  let e := D.strongDualRestriction (bruhatSchwartz_bounded_subset_of_cofinal b hCov)
  exact nuclearLocallyConvex_of_equiv e.symm
    (nuclearLocallyConvex_submodule (nuclearLocallyConvex_pi (fun n ↦ hN (b n))) D.CompatibleDual)

/-- The strong Schwartz–Bruhat dual is nuclear in the topology of bounded convergence. -/
theorem bruhatSchwartz_strongDual_nuclear [SecondCountableTopology G] :
    NuclearLocallyConvex.{u, u} (StrongDual ℂ (BruhatSchwartz G)) := by
  apply bruhatSchwartz_strongDual_nuclear_of_stages
  intro p
  exact elementarySchwartz_strongDual_nuclear (m := p.2.realDim) (n := p.2.torusDim)
    (r := p.2.latticeRank) (F := p.2.finiteFactor)

/-- The strong Schwartz–Bruhat dual is complete. The limit topology on
the dual is the closed subspace of compatible stage restrictions. -/
theorem bruhatSchwartz_strongDual_complete [SecondCountableTopology G] :
    CompleteSpace (StrongDual ℂ (BruhatSchwartz G)) := by
  obtain ⟨P, hp, hCov⟩ := lcaStructuralPairs_cofinalSequence (G := G)
  let b (n : ℕ) : BruhatSchwartzStage G := ⟨P n, Classical.choice (P n).quotient_elementary⟩
  let D := bruhatSchwartz_countablePresentation b hp hCov
  let e := D.strongDualRestriction (bruhatSchwartz_bounded_subset_of_cofinal b hCov)
  letI (n : ℕ) : ContinuousSMul ℂ (b n).Space :=
    (PolynormableSpace.withSeminorms ℂ (b n).Space).continuousSMul
  letI (n : ℕ) : TopologicalSpace.MetrizableSpace (b n).Space :=
    (elementarySchwartz_isFrechet (m := (b n).2.realDim) (n := (b n).2.torusDim)
      (r := (b n).2.latticeRank) (F := (b n).2.finiteFactor)).2.2.1
  letI (n : ℕ) : CompleteSpace (StrongDual ℂ (b n).Space) := inferInstance
  have hclosed : IsClosed (D.CompatibleDual : Set (∀ n, StrongDual ℂ (b n).Space)) := by
    have heq : (D.CompatibleDual : Set (∀ n, StrongDual ℂ (b n).Space)) =
        ⋂ m : ℕ, ⋂ n : ℕ, ⋂ h : m ≤ n, ⋂ x : (b m).Space,
          {g : ∀ n, StrongDual ℂ (b n).Space | g n (D.transition h x) = g m x} := by
      ext g
      simp only [mem_iInter, mem_ofPred_eq]
      rfl
    rw [heq]
    refine isClosed_iInter fun m ↦ isClosed_iInter fun n ↦ isClosed_iInter fun h ↦
      isClosed_iInter fun x ↦ isClosed_eq ?_ ?_
    · exact (continuous_eval_const (D.transition h x)).comp (continuous_apply n)
    · exact (continuous_eval_const x).comp (continuous_apply m)
  let L : StrongDual ℂ (BruhatSchwartz G) →+ (∀ n, StrongDual ℂ (b n).Space) :=
    (D.CompatibleDual.subtype.comp e.toLinearEquiv.toLinearMap).toAddMonoidHom
  have he : IsUniformInducing L :=
    AddMonoidHom.isUniformInducing_of_isInducing
      ((show IsInducing (Subtype.val : D.CompatibleDual → _) from ⟨rfl⟩).comp
        e.toHomeomorph.isInducing)
  apply he.completeSpace
  have hRange : range L = (D.CompatibleDual : Set (∀ n, StrongDual ℂ (b n).Space)) := by
    ext g
    constructor
    · rintro ⟨x, rfl⟩
      exact (e x).property
    · intro hg
      obtain ⟨x, hx⟩ := e.surjective ⟨g, hg⟩
      exact ⟨x, congrArg Subtype.val hx⟩
  exact hRange.symm ▸ hclosed.isComplete


/-- The Heine–Borel clause of D.1.5.7 follows from nuclearity and completeness. -/
theorem bruhatSchwartz_montel_of_nuclear [SecondCountableTopology G]
    (hN : NuclearLocallyConvex.{u, u} (BruhatSchwartz G)) :
    MontelSpace ℂ (BruhatSchwartz G) := by
  letI : UniformSpace (BruhatSchwartz G) := bruhatSchwartzUniformSpace
  letI : IsUniformAddGroup (BruhatSchwartz G) := isUniformAddGroup_of_addCommGroup
  letI : CompleteSpace (BruhatSchwartz G) := bruhatSchwartz_complete
  exact ⟨fun _ hs hB ↦ (nuclearLocallyConvex_totallyBounded hN hB).isCompact_of_isClosed hs⟩

/-- Every closed bounded subset of the full Schwartz–Bruhat space is compact. -/
theorem bruhatSchwartz_montel [SecondCountableTopology G] : MontelSpace ℂ (BruhatSchwartz G) :=
  bruhatSchwartz_montel_of_nuclear bruhatSchwartz_nuclear

/-- Closed bounded subsets of the strong dual are compact once the dual is nuclear. -/
theorem bruhatSchwartz_strongDual_montel_of_nuclear [SecondCountableTopology G]
    (hN : NuclearLocallyConvex.{u, u} (StrongDual ℂ (BruhatSchwartz G))) :
    MontelSpace ℂ (StrongDual ℂ (BruhatSchwartz G)) := by
  letI : CompleteSpace (StrongDual ℂ (BruhatSchwartz G)) := bruhatSchwartz_strongDual_complete
  constructor
  intro S hs hB
  have ht : TotallyBounded S :=
    nuclearLocallyConvex_totallyBounded (E := StrongDual ℂ (BruhatSchwartz G)) hN hB
  exact ht.isCompact_of_isClosed hs

/-- Every closed bounded set in the strong Schwartz–Bruhat dual is compact. -/
theorem bruhatSchwartz_strongDual_montel [SecondCountableTopology G] :
    MontelSpace ℂ (StrongDual ℂ (BruhatSchwartz G)) :=
  bruhatSchwartz_strongDual_montel_of_nuclear bruhatSchwartz_strongDual_nuclear

end

end Masullo
