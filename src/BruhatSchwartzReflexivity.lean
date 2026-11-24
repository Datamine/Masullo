import BruhatSchwartzStructure
import StrongDualBarrelled

open Bornology Filter Function Set Topology

namespace Masullo

noncomputable section

universe u

set_option maxSynthPendingDepth 8

variable {G : Type u} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]

local instance : ContinuousSMul ℂ (BruhatSchwartz G) :=
  (PolynormableSpace.withSeminorms ℂ (BruhatSchwartz G)).continuousSMul

omit [SecondCountableTopology G] in
/-- The bornological assertion in the manuscript's seminorm formulation. -/
theorem bruhatSchwartz_bornological (p : Seminorm ℂ (BruhatSchwartz G))
    (hp : ∀ B : Set (BruhatSchwartz G), IsVonNBounded ℂ B → ∃ M : ℝ, ∀ x ∈ B, p x ≤ M) :
    Continuous p := by
  let j : BruhatSchwartz G →ₗ[ℂ] SeminormCarrier p := LinearMap.id
  letI : PolynormableSpace ℂ (SeminormCarrier p) :=
    (norm_withSeminorms ℂ (SeminormCarrier p)).toPolynormableSpace
  have hj : Continuous j := by
    apply bruhatSchwartz_linear_continuous_of_bounded j
    intro B hB
    obtain ⟨M, hM⟩ := hp B hB
    apply (NormedSpace.isVonNBounded_iff' ℂ).mpr
    refine ⟨M, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact hM x hx
  exact hj.norm

/-- Evaluation gives the strong reflexivity of the full Schwartz–Bruhat space. -/
theorem bruhatSchwartz_reflexive :
    ∃ e : BruhatSchwartz G ≃L[ℂ] StrongDual ℂ (StrongDual ℂ (BruhatSchwartz G)),
      ∀ x f, e x f = f x := by
  let E := BruhatSchwartz G
  letI : UniformSpace E := bruhatSchwartzUniformSpace
  letI : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  letI : BarrelledSpace ℂ E := bruhatSchwartz_barrelled
  letI : CompleteSpace E := bruhatSchwartz_complete
  letI : T2Space E := bruhatSchwartz_t2
  exact strongBidual_equiv_of_nuclear (E := E) bruhatSchwartz_nuclear

theorem bruhatSchwartz_strongDual_barrelled : BarrelledSpace ℂ (StrongDual ℂ (BruhatSchwartz G)) := by
  apply strongDual_barrelled_of_bidually_surjective
  obtain ⟨e, he⟩ := bruhatSchwartz_reflexive (G := G)
  intro f
  obtain ⟨x, hx⟩ := e.surjective f
  exact ⟨x, ContinuousLinearMap.ext fun l ↦ (he x l).symm.trans (DFunLike.congr_fun hx l)⟩

/-- Evaluation gives the strong reflexivity of the distribution space. -/
theorem bruhatSchwartz_strongDual_reflexive :
    let D := StrongDual ℂ (BruhatSchwartz G)
    ∃ e : D ≃L[ℂ] StrongDual ℂ (StrongDual ℂ D), ∀ x f, e x f = f x := by
  let D := StrongDual ℂ (BruhatSchwartz G)
  let h := bruhatSchwartz_strongDual_nuclear (G := G)
  letI : T2Space D := h.1
  letI : PolynormableSpace ℂ D := h.2.1
  letI : BarrelledSpace ℂ D := bruhatSchwartz_strongDual_barrelled
  letI : CompleteSpace D := bruhatSchwartz_strongDual_complete
  exact strongBidual_equiv_of_nuclear (E := D) h

end

end Masullo
