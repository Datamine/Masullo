import FixedFactorStrictTensor
import ElementarySchwartzNuclear
import BruhatSchwartzStructure
import ModulatedDecayTensorComparisonStages

set_option Elab.async false

open Function Set Topology
open scoped TensorProduct

namespace Masullo
noncomputable section

variable {H : Type*} [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H]
  [T2Space H] [LocallyCompactSpace H] [SecondCountableTopology H]

variable {R : Type*} [AddCommGroup R] [Module ℂ R] [TopologicalSpace R]
  [IsTopologicalAddGroup R] [PolynormableSpace ℂ R] [T2Space R]

set_option maxHeartbeats 1200000 in
/-- A cofinal sequence of Bruhat stages covers the completed inductive tensor
of the Schwartz–Bruhat space with a fixed Fréchet factor. -/
theorem completedInductiveBruhatTensor_exists_stage_of_cofinal
    (p : ℕ → BruhatSchwartzStage H) (hp : Monotone (fun n => (p n).1))
    (hCov : ∀ Q : LCAStructuralPair H, ∃ n, Q ≤ (p n).1)
    (hR : IsFrechetTVS R)
    (w : (inductiveTensorModuleStructure (BruhatSchwartz H) R).Completed) :
    ∃ n : ℕ, w ∈ range
      (completedInductiveTensor_map (p n).inclusionCLM (ContinuousLinearMap.id ℂ R)) := by
  let A := BruhatSchwartz H
  let X (n : ℕ) := (p n).Space
  letI : ∀ n : ℕ, IsTopologicalAddGroup (X n) := fun n =>
    (elementarySchwartz_frechet : IsFrechetTVS (X n)).1
  let B : LinearInductivePresentation A X := bruhatSchwartz_countablePresentation p hp hCov
  let u (n : ℕ) : X n →L[ℂ] A := B.incl n
  let t (n k : ℕ) (h : n ≤ k) : X n →L[ℂ] X k := B.transition h
  have hcompat (n k : ℕ) (h : n ≤ k) : (u k).comp (t n k h) = u n :=
    ContinuousLinearMap.ext (B.incl_transition h)
  have hfinal : (inferInstance : TopologicalSpace A) =
      locallyConvexFinalTopology (fun n => (u n).toLinearMap) :=
    locallyConvexFinalTopology_eq_of_seminormTests (P := X) u
      (fun s hs => bruhatSchwartz_seminorm_continuous_of_cofinal p hCov s hs)
  have ht (n : ℕ) : inductiveTensorTopology (X n) R =
      injectiveTensorTopology (X n) R :=
    nuclearFrechet_inductiveTensorTopology_eq_injective elementarySchwartz_frechet hR
      elementarySchwartz_nuclear
  have hEmb (n : ℕ) : IsEmbedding (u n) := bruhatSchwartz_strict.2.1 (p n)
  exact completedInductiveTensor_exists_stage_of_strict_left
    (X := X) u t hcompat B.exhaust hfinal hEmb ht w

section CompactAngularFactor

variable [CompactSpace H]

omit [SecondCountableTopology H] in
private theorem exists_wholeBruhatStage_same_kernel (Q : BruhatSchwartzStage H) :
    ∃ R : WholeBruhatStage H, R.val.1.kernel = Q.1.kernel := by
  let eTop : (⊤ : Subgroup H) ≃ₜ* H :=
    ⟨Subgroup.topEquiv, continuous_subtype_val, continuous_id.subtype_mk _⟩
  have hcg : IsCompactlyGeneratedGroup H :=
    ⟨univ, Filter.univ_mem, isCompact_univ, Subgroup.closure_univ⟩
  let J : OpenCompactlyGeneratedSubgroups H :=
    ⟨⊤, isOpen_univ, compactGeneration_transport eTop.symm hcg⟩
  let B : LCAStructuralPair H :=
    ⟨J, Q.1.kernel, Q.1.kernel_closed, Q.1.annihilator_open, Q.1.annihilator_compactlyGenerated, le_top⟩
  obtain ⟨b⟩ := B.quotient_elementary
  exact ⟨⟨⟨B, b⟩, rfl⟩, rfl⟩

theorem exists_wholeBruhatStage_compact_cofinal :
    ∃ p : ℕ → WholeBruhatStage H, Monotone (fun n => (p n).val.1) ∧
      ∀ Q : LCAStructuralPair H, ∃ n, Q ≤ (p n).val.1 := by
  obtain ⟨b, hb, hc⟩ := lcaStructuralPairs_cofinalSequence (G := H)
  let B (n : ℕ) : BruhatSchwartzStage H := ⟨b n, Classical.choice (b n).quotient_elementary⟩
  choose p hp using fun n => exists_wholeBruhatStage_same_kernel (B n)
  refine ⟨p, ?_, ?_⟩
  · intro i j hij
    refine ⟨?_, ?_⟩
    · change (p i).val.1.upper.val ≤ (p j).val.1.upper.val
      rw [(p j).property]
      exact le_top
    · change (p j).val.1.kernel ≤ (p i).val.1.kernel
      rw [hp j, hp i]
      exact (hb hij).2
  · intro Q
    obtain ⟨n, hn⟩ := hc Q
    refine ⟨n, ?_, ?_⟩
    · change Q.upper.val ≤ (p n).val.1.upper.val
      rw [(p n).property]
      exact le_top
    · change (p n).val.1.kernel ≤ Q.kernel
      rw [hp n]
      exact hn.2


end CompactAngularFactor

end
end Masullo
