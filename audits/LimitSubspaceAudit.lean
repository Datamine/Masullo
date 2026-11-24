import RiemannMasullo.AppC_LCTVS.Sec2b

/-! Run with `lake env lean` in original revision
`cb3e092484c0e94d115634ce9f202433bdbd17be` on Lean 4.36.0. -/

open Bornology Set

namespace Masullo

open RiemannMasullo

variable {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] [T2Space E]
  {X : ℕ → Type*} [∀ n, AddCommGroup (X n)] [∀ n, Module ℂ (X n)]
  [∀ n, TopologicalSpace (X n)]
  {j : ∀ n, X n →L[ℂ] X (n + 1)} {i : ∀ n, X n →L[ℂ] E}

/-- Theorem C.1.5.11, p. 668, with the quotient lifting condition written out. -/
theorem strictNuclear_limitSubspace_iff_boundedLift
    (h : IsInjectiveLCLimit j i) (hj : ∀ n, Topology.IsEmbedding (j n))
    (hFrechet : ∀ n, IsFrechetTVS (X n)) (hNuclear : ∀ n, IsNuclearTVS (X n))
    (F : Submodule ℂ E) (hF : IsClosed (F : Set E)) :
    (inferInstance : TopologicalSpace F) = limitSubspaceTopology i F ↔
      ∀ B : Set (E ⧸ F), IsVonNBounded ℂ B →
        ∃ A : Set E, IsVonNBounded ℂ A ∧ B ⊆ F.mkQL '' A := by
  change (inferInstance : TopologicalSpace F) = limitSubspaceTopology i F ↔
    LiftsBoundedSets F.mkQL
  exact (and_iff_right hF).symm.trans
    (isLimitSubspace_iff_liftsBoundedSets_of_nuclear h hj hFrechet hNuclear F hF)

#print axioms strictNuclear_limitSubspace_iff_boundedLift
#print axioms RiemannMasullo.limitSubspaceTopology_eq_iff_liftsBoundedSets

end Masullo
