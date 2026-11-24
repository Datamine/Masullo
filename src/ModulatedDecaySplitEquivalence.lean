import ModulatedDecaySplitTensor
import ModulatedDecaySplitTensorInverseBridge
import ModulatedDecayFixedTensorInjectivity
import ModulatedDecayTensorDiagram
import ModulatedDecayRadialStageEquiv

set_option Elab.async false
set_option maxHeartbeats 350000

open Function MeasureTheory Set Topology
open scoped TensorProduct

namespace Masullo

noncomputable section

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  (m : G →ₜ* Multiplicative ℝ) (τ : Multiplicative ℝ →ₜ* G) (hτ : RightInverse τ m)

local notation "K" => m.toMonoidHom.ker

variable [LocallyCompactSpace m.toMonoidHom.ker] [MeasurableSpace m.toMonoidHom.ker] [BorelSpace m.toMonoidHom.ker]

include hτ in
omit [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [LocallyCompactSpace m.toMonoidHom.ker] [MeasurableSpace m.toMonoidHom.ker]
  [BorelSpace m.toMonoidHom.ker] in
private theorem splitStage_kernel_le_projection (p : WholeBruhatStage K) (q : WholeBruhatStage G)
    (hq : q.val.1.kernel = p.val.1.kernel.map m.toMonoidHom.ker.subtype) :
    q.val.1.kernel ≤ p.val.1.kernel.comap (modulatedKernelProjection m τ hτ).toMonoidHom := by
  rw [hq]
  rintro _ ⟨k,hk,rfl⟩
  change modulatedKernelProjection m τ hτ k.val ∈ p.val.1.kernel
  have hp : modulatedKernelProjection m τ hτ k.val = k := by
    have he := modulatedKernelProjection_split m τ hτ k 0
    change modulatedKernelProjection m τ hτ (τ 1 * k.val) = k at he
    rwa [map_one τ, one_mul] at he
  rwa [hp]

/-- On each matched quotient stage, multiplication of angular and radial
tests gives the completed projective tensor isomorphism. -/
theorem exists_splitStage_completedTensorEquiv
    (hm : IsProperMap m) (I : Set ℝ) (hI : I.Nonempty) (hInt : OrdConnected I)
    (p : WholeBruhatStage K) (q : WholeBruhatStage G)
    (hq : q.val.1.kernel = p.val.1.kernel.map m.toMonoidHom.ker.subtype) :
    ∃ E : (projectiveTensorModuleStructure p.val.Space (PositiveRealExponentialDecay I)).Completed
        ≃L[ℂ] WholeBruhatDecayStage m I q,
      SplitStageTensorFormula m p q I (modulatedKernelProjection m τ hτ) E.toContinuousLinearMap := by
  letI compactKernel : CompactSpace K := isCompact_iff_compactSpace.mp
    (hm.isCompact_preimage (isCompact_singleton (x := (1 : Multiplicative ℝ))))
  let ν : Measure K := Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts K)
  letI haar : ν.IsHaarMeasure := inferInstanceAs
    (Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts K)).IsHaarMeasure
  letI probability : IsProbabilityMeasure ν := ⟨by
    simpa only [ν, TopologicalSpace.PositiveCompacts.coe_top] using
      (Measure.haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts K)))⟩
  let t : I := ⟨hI.choose,hI.choose_spec⟩
  let α : G →ₜ* K := modulatedKernelProjection m τ hτ
  have hker : q.val.1.kernel ≤ p.val.1.kernel.comap α.toMonoidHom :=
    splitStage_kernel_le_projection m τ hτ p q hq
  have hex : ∃ F : (projectiveTensorModuleStructure p.val.Space
        (PositiveRealExponentialDecay I)).Completed →L[ℂ] WholeBruhatDecayStage m I q,
      SplitStageTensorFormula m p q I α F :=
    exists_splitStage_completedTensorMap (G := G) (H := K) m hm α p q hker I hI hInt
  let F := hex.choose
  have hF' : SplitStageTensorFormula m p q I (modulatedKernelProjection m τ hτ) F := hex.choose_spec
  let D := projectiveTensorModuleStructure p.val.Space (PositiveRealExponentialDecay I)
  let Y := WholeBruhatDecayStage m I q
  let hInv := splitStage_multiplication_hasContinuousRightInverse m τ hτ ν p q hq hm I t F hF'
  let S := hInv.choose
  have hS := hInv.choose_spec
  have hr (y : Y) : F (S y) = y := by
    with_reducible_and_instances
      exact congrArg (fun L : Y →L[ℂ] Y ↦ L y) hS
  have hi : Injective F := splitStage_multiplication_injective (G := G) m τ hτ p q I t hInt F hF'
  have hl : LeftInverse S F := fun x ↦ hi (hr (F x))
  let E : D.Completed ≃L[ℂ] Y := ContinuousLinearEquiv.equivOfInverse F S hl hr
  refine ⟨E, ?_⟩
  change SplitStageTensorFormula m p q I (modulatedKernelProjection m τ hτ) F
  exact hF'

/-- The split multiplication equivalence of (D.3.3.3), with the translation law
and the commuting square of multiplication equivalences in (D.3.3.4). -/
theorem exists_splitGlobal_completedTensorEquiv_with_diagram
    (hm : IsProperMap m) (I : Set ℝ) (hI : I.Nonempty) (hInt : OrdConnected I) :
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
  refine exists_splitGlobal_completedTensorEquiv_with_diagram_of_stages m τ hτ hm I hI hInt ?_
  intro p q hq
  obtain ⟨E,hE⟩ := exists_splitStage_completedTensorEquiv m τ hτ hm I hI hInt p q hq
  exact ⟨E,hE⟩

/-- The radial-first fixed-stage multiplication in (D.3.3.7). -/
theorem exists_splitStage_radialFirst_equiv
    (hm : IsProperMap m) (I : Set ℝ) (hI : I.Nonempty) (hInt : OrdConnected I)
    (p : WholeBruhatStage K) (q : WholeBruhatStage G)
    (hq : q.val.1.kernel = p.val.1.kernel.map m.toMonoidHom.ker.subtype) :
    let R := PositiveRealExponentialDecay I
    let D := inductiveTensorModuleStructure R p.val.Space
    ∃ E : D.Completed ≃L[ℂ] WholeBruhatDecayStage m I q,
      ∀ (r : R) (a : p.val.Space) (g : G),
        (E (D.incl (r ⊗ₜ[ℂ] a))).val g =
          r.val (m g).toAdd * p.val.realize a (modulatedKernelProjection m τ hτ g) := by
  obtain ⟨F,hF⟩ := exists_splitStage_completedTensorEquiv m τ hτ hm I hI hInt p q hq
  exact exists_decayStage_radialFirst_equiv_of_projective m (modulatedKernelProjection m τ hτ)
    p q I hI hInt F hF

end
end Masullo
