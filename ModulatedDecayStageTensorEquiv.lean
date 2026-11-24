import ModulatedDecayStageTensorComparison

open Set
open scoped TensorProduct

namespace Masullo
noncomputable section

variable {G H : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [CommGroup H] [TopologicalSpace H]
  [IsTopologicalGroup H] [T2Space H] [LocallyCompactSpace H]

set_option maxHeartbeats 1400000 in
/-- On a fixed quotient stage, the projective multiplication equivalence induces
 the angular-first inductive multiplication equivalence of (D.3.3.4). -/
theorem exists_decayStage_angularFirst_equiv_of_projective
    (m : G →ₜ* Multiplicative ℝ) (α : G →ₜ* H)
    (p : WholeBruhatStage H) (q : WholeBruhatStage G)
    (I : Set ℝ) (hI : I.Nonempty) (hInt : OrdConnected I)
    (F : (projectiveTensorModuleStructure p.val.Space (PositiveRealExponentialDecay I)).Completed
      ≃L[ℂ] WholeBruhatDecayStage m I q)
    (hF : ∀ (a : p.val.Space) (r : PositiveRealExponentialDecay I) (g : G),
      (F ((projectiveTensorModuleStructure p.val.Space (PositiveRealExponentialDecay I)).incl
        (a ⊗ₜ[ℂ] r))).val g = p.val.realize a (α g) * r.val (m g).toAdd) :
    ∃ L : (inductiveTensorModuleStructure p.val.Space (PositiveRealExponentialDecay I)).Completed
          ≃L[ℂ] WholeBruhatDecayStage m I q,
      ∀ (a : p.val.Space) (r : PositiveRealExponentialDecay I) (g : G),
        (L ((inductiveTensorModuleStructure p.val.Space (PositiveRealExponentialDecay I)).incl
          (a ⊗ₜ[ℂ] r))).val g = p.val.realize a (α g) * r.val (m g).toAdd := by
  let A := p.val.Space
  let R := PositiveRealExponentialDecay I
  let D := inductiveTensorModuleStructure A R
  let P := projectiveTensorModuleStructure A R
  let h := exists_decayStage_completedTensorComparison p I hInt hI
  let E : D.Completed ≃L[ℂ] P.Completed := h.choose
  refine ⟨E.trans F, fun a r g => ?_⟩
  change (F (E (D.incl (a ⊗ₜ[ℂ] r)))).val g = _
  exact (congrArg (fun z : P.Completed => (F z).val g)
    (h.choose_spec (a ⊗ₜ[ℂ] r))).trans (hF a r g)

end
end Masullo
