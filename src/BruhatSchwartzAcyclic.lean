import BruhatSchwartzStrict
import StrictInductiveTelescope

open Function Set Topology
open scoped DirectSum

namespace Masullo

noncomputable section

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G]

/-- The canonical sequence of the structural stages, with the locally
convex direct sum on both copies, is topologically exact. -/
def BruhatSchwartzStructuralExact
    (b : ℕ → BruhatSchwartzStage G)
    (hb : Monotone (fun n ↦ (b n).1))
    (hCov : ∀ p : LCAStructuralPair G, ∃ n, p ≤ (b n).1) : Prop :=
  let X := fun n ↦ (b n).Space
  letI : TopologicalSpace (⨁ n, X n) := locallyConvexSumTopology X
  let D := bruhatSchwartz_countablePresentation b hb hCov
  let σ := directSumDifference (fun n ↦ D.transition (Nat.le_succ n))
  let q := DirectSum.toModule ℂ ℕ (BruhatSchwartz G) (fun n ↦ (D.incl n).toLinearMap)
  IsClosedEmbedding σ ∧ LinearMap.range σ = LinearMap.ker q ∧ IsOpenQuotientMap q

/-- Theorem D.1.5.10. Every increasing cofinal structural sequence gives
the paper's topologically exact difference sequence. -/
theorem bruhatSchwartz_structural_topologicallyExact
    (b : ℕ → BruhatSchwartzStage G)
    (hb : Monotone (fun n ↦ (b n).1))
    (hCov : ∀ p : LCAStructuralPair G, ∃ n, p ≤ (b n).1) :
    BruhatSchwartzStructuralExact b hb hCov := by
  letI : T2Space (BruhatSchwartz G) := bruhatSchwartz_t2
  exact (bruhatSchwartz_countablePresentation b hb hCov).topologicallyExact_difference
    (fun n ↦ (BruhatSchwartzStage.transition_isClosedEmbedding
      (b n) (b (n + 1)) (hb (Nat.le_succ n))).isEmbedding)
    (bruhatSchwartz_seminorm_continuous_of_cofinal b hCov)

/-- Proposition D.1.5.9. In the second-countable case the full
Schwartz–Bruhat space has an acyclic countable structural presentation. -/
theorem bruhatSchwartz_acyclic [SecondCountableTopology G] :
    ∃ (b : ℕ → BruhatSchwartzStage G)
      (hb : Monotone (fun n ↦ (b n).1))
      (hCov : ∀ p : LCAStructuralPair G, ∃ n, p ≤ (b n).1),
      BruhatSchwartzStructuralExact b hb hCov := by
  obtain ⟨P, hP, hCov⟩ := lcaStructuralPairs_cofinalSequence (G := G)
  let b (n : ℕ) : BruhatSchwartzStage G := ⟨P n, Classical.choice (P n).quotient_elementary⟩
  exact ⟨b, hP, hCov, bruhatSchwartz_structural_topologicallyExact b hP hCov⟩

end

end Masullo
