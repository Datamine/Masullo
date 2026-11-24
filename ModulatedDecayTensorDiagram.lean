import ModulatedDecayGlobalTensorEquiv
import ModulatedDecayStageTensorEquiv

set_option Elab.async false
set_option maxHeartbeats 3500000

open Function Set Topology
open scoped TensorProduct

namespace Masullo
noncomputable section

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  (m : G →ₜ* Multiplicative ℝ) (τ : Multiplicative ℝ →ₜ* G) (hτ : RightInverse τ m)

local notation "K" => m.toMonoidHom.ker

variable [LocallyCompactSpace m.toMonoidHom.ker]

/-- The split multiplication equivalence of (D.3.3.3), with the translation law
and the commuting square of multiplication equivalences in (D.3.3.4). -/
theorem exists_splitGlobal_completedTensorEquiv_with_diagram_of_stages
    (hm : IsProperMap m) (I : Set ℝ) (hI : I.Nonempty) (hInt : OrdConnected I)
    (hLoc : ∀ (p : WholeBruhatStage K) (q : WholeBruhatStage G),
      q.val.1.kernel = p.val.1.kernel.map m.toMonoidHom.ker.subtype →
      ∃ L : (projectiveTensorModuleStructure p.val.Space (PositiveRealExponentialDecay I)).Completed
          ≃L[ℂ] WholeBruhatDecayStage m I q,
        ∀ (a : p.val.Space) (r : PositiveRealExponentialDecay I) (g : G),
          (L ((projectiveTensorModuleStructure p.val.Space (PositiveRealExponentialDecay I)).incl
            (a ⊗ₜ[ℂ] r))).val g =
            p.val.realize a (modulatedKernelProjection m τ hτ g) * r.val (m g).toAdd) :
    let A := BruhatSchwartz K
    let R := PositiveRealExponentialDecay I
    let D := inductiveTensorModuleStructure A R
    let α := modulatedKernelProjection m τ hτ
    letI : IsTopologicalAddGroup A := (PolynormableSpace.withSeminorms ℂ A).topologicalAddGroup
    letI : IsTopologicalAddGroup R := (PolynormableSpace.withSeminorms ℂ R).topologicalAddGroup
    ∃ L : D.Completed ≃L[ℂ] ModulatedExponentialInductive m I,
      (∀ (a : A) (r : R) (x : G), (L (D.incl (a ⊗ₜ[ℂ] r))).val x =
        a.val (α x) * r.val (m x).toAdd) ∧
      (∀ (g : G) (z : D.Completed),
        L (completedInductiveTensor_map (bruhatSchwartz_translate (α g))
          (logExponentialDecayTranslation I hI (-(m g).toAdd)) z) =
        ModulatedExponentialInductive.translate m I g (L z)) ∧
      ∀ (p : WholeBruhatStage K) (q : WholeBruhatStage G),
        q.val.1.kernel = p.val.1.kernel.map m.toMonoidHom.ker.subtype →
        let B := p.val.Space
        letI : IsTopologicalAddGroup B := (PolynormableSpace.withSeminorms ℂ B).topologicalAddGroup
        let P := inductiveTensorModuleStructure B R
        ∃ L₀ : P.Completed ≃L[ℂ] WholeBruhatDecayStage m I q,
          (∀ (b : B) (r : R) (x : G), (L₀ (P.incl (b ⊗ₜ[ℂ] r))).val x =
            p.val.realize b (α x) * r.val (m x).toAdd) ∧
          ∀ z, ModulatedExponentialInductive.stageMap q (L₀ z) =
            L (completedInductiveTensor_map p.val.inclusionCLM (ContinuousLinearMap.id ℂ R) z) := by
  dsimp only
  let α := modulatedKernelProjection m τ hτ
  let hex := exists_splitGlobal_completedTensorEquiv_of_stages m τ hτ hm I hI hInt hLoc
  let L := hex.choose
  have hL := hex.choose_spec
  refine ⟨L, hL, ?_, ?_⟩
  · intro g
    exact splitGlobal_completedTensorMap_translate m hm hτ.surjective α I hI g L.toContinuousLinearMap hL
  · intro p q hker
    let hp := hLoc p q hker
    let h₀ := exists_decayStage_angularFirst_equiv_of_projective m α p q I hI hInt hp.choose hp.choose_spec
    let L₀ := h₀.choose
    have hL₀ := h₀.choose_spec
    exact ⟨L₀, hL₀, splitStage_completedInductiveTensor_to_global m α I hI p q
      L₀.toContinuousLinearMap L.toContinuousLinearMap hL₀ hL⟩


end
end Masullo
