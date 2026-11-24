import BruhatInductiveTensorCoverage
import CompletedTensorStageBridge
import ModulatedDecayStageTensorComparison

set_option Elab.async false

open Function Set Topology
open scoped TensorProduct

namespace Masullo
noncomputable section

variable {H : Type*} [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H]
  [T2Space H] [LocallyCompactSpace H] [CompactSpace H] [SecondCountableTopology H]

set_option maxHeartbeats 1200000 in
/-- A compact angular factor and a Fréchet radial factor give coverage of the
inductive decay tensor by the completed projective stage maps. -/
theorem inductiveDecayTensorStageCoverage_of_strict (I : Set ℝ)
    (hI : I.Nonempty) (hInt : OrdConnected I) : InductiveDecayTensorStageCoverage I H := by
  let A := BruhatSchwartz H
  let R := PositiveRealExponentialDecay I
  let D := inductiveTensorModuleStructure A R
  let hf := positiveRealExponentialDecay_frechet I hInt hI
  letI : IsTopologicalAddGroup A := (PolynormableSpace.withSeminorms ℂ A).topologicalAddGroup
  letI : IsTopologicalAddGroup R := (PolynormableSpace.withSeminorms ℂ R).topologicalAddGroup
  letI : T2Space R := (positiveRealExponentialDecay_isEmbedding I hI).t2Space
  intro w
  let data := exists_wholeBruhatStage_compact_cofinal (H := H)
  let p₀ : ℕ → WholeBruhatStage H := data.choose
  let b (n : ℕ) : BruhatSchwartzStage H := (p₀ n).val
  have hb : Monotone (fun n => (b n).1) := data.choose_spec.1
  have hCov : ∀ Q : LCAStructuralPair H, ∃ n, Q ≤ (b n).1 := data.choose_spec.2
  let ex := completedInductiveBruhatTensor_exists_stage_of_cofinal (H := H) (R := R) b hb hCov hf w
  let p := p₀ ex.choose
  let B := p.val.Space
  letI : IsTopologicalAddGroup B := (PolynormableSpace.withSeminorms ℂ B).topologicalAddGroup
  let j : B →L[ℂ] A := p.val.inclusionCLM
  have heq : inductiveTensorTopology B R = projectiveTensorTopology B R :=
    frechet_inductiveTensorTopology_eq_projective elementarySchwartz_frechet hf
  have h :
      ∃ J : (projectiveTensorModuleStructure B R).Completed →L[ℂ] D.Completed,
        (∀ (a : B) (r : R), J ((projectiveTensorModuleStructure B R).incl
          (a ⊗ₜ[ℂ] r)) = D.incl (j a ⊗ₜ[ℂ] r)) ∧
        range J = range (completedInductiveTensor_map j (ContinuousLinearMap.id ℂ R)) :=
    exists_projectiveStage_to_inductiveTensor (R := R) j heq
  let J := h.choose
  have hmem : w ∈ range J := h.choose_spec.2.symm ▸ ex.choose_spec
  exact ⟨p, J, h.choose_spec.1, hmem⟩


end
end Masullo
