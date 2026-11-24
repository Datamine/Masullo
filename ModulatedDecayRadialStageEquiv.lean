import ModulatedDecayStageTensorComparison
import CompletedTensorStageBridge

set_option Elab.async false
set_option maxHeartbeats 1000000

open Function Set Topology
open scoped TensorProduct

namespace Masullo

noncomputable section

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G]
  (m : G →ₜ* Multiplicative ℝ)

local notation "K" => m.toMonoidHom.ker


/-- The fixed-stage projective multiplication equivalence induces the
radial-first inductive multiplication equivalence in (D.3.3.7). -/
theorem exists_decayStage_radialFirst_equiv_of_projective
    (α : G →ₜ* K) (p : WholeBruhatStage K) (q : WholeBruhatStage G)
    (I : Set ℝ) (hI : I.Nonempty) (hInt : OrdConnected I)
    (F : (projectiveTensorModuleStructure p.val.Space (PositiveRealExponentialDecay I)).Completed
      ≃L[ℂ] WholeBruhatDecayStage m I q)
    (hF : ∀ (a : p.val.Space) (r : PositiveRealExponentialDecay I) (g : G),
      (F ((projectiveTensorModuleStructure p.val.Space (PositiveRealExponentialDecay I)).incl
        (a ⊗ₜ[ℂ] r))).val g = p.val.realize a (α g) * r.val (m g).toAdd) :
    ∃ L : (inductiveTensorModuleStructure (PositiveRealExponentialDecay I) p.val.Space).Completed
          ≃L[ℂ] WholeBruhatDecayStage m I q,
      ∀ (r : PositiveRealExponentialDecay I) (a : p.val.Space) (g : G),
        (L ((inductiveTensorModuleStructure (PositiveRealExponentialDecay I) p.val.Space).incl
          (r ⊗ₜ[ℂ] a))).val g = r.val (m g).toAdd * p.val.realize a (α g) := by
  let A := p.val.Space
  let R := PositiveRealExponentialDecay I
  have hEq : inductiveTensorTopology A R = projectiveTensorTopology A R :=
    frechet_inductiveTensorTopology_eq_projective elementarySchwartz_frechet
      (positiveRealExponentialDecay_frechet I hInt hI)
  let P := projectiveTensorModuleStructure A R
  let D := inductiveTensorModuleStructure R A
  have hbridge : ∃ V : D.Completed ≃L[ℂ] P.Completed,
      ∀ (r : R) (a : A), V (D.incl (r ⊗ₜ[ℂ] a)) = P.incl (a ⊗ₜ[ℂ] r) :=
    exists_completedInductiveTensor_flip_toProjective (A := A) (R := R) hEq
  let V := hbridge.choose
  let L : D.Completed ≃L[ℂ] WholeBruhatDecayStage m I q := V.trans F
  refine ⟨L, fun r a g => ?_⟩
  change (F (V (D.incl (r ⊗ₜ[ℂ] a)))).val g = _
  have he := hbridge.choose_spec r a
  exact (congrArg (fun z : P.Completed => (F z).val g) he).trans
    ((hF a r g).trans (mul_comm _ _))


end
end Masullo
