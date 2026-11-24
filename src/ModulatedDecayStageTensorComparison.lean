import ModulatedDecaySplitTensor

open Set Topology
open scoped TensorProduct

namespace Masullo

noncomputable section

variable {K : Type*} [CommGroup K] [TopologicalSpace K]

/-- The canonical comparison on completions follows from the Fréchet
hypotheses on the two factors. -/
private theorem exists_frechet_completedTensorComparison
    {A R : Type*} [AddCommGroup A] [Module ℂ A] [TopologicalSpace A]
    [AddCommGroup R] [Module ℂ R] [TopologicalSpace R]
    (hA : IsFrechetTVS A) (hR : IsFrechetTVS R) :
    ∃ E : (inductiveTensorModuleStructure A R).Completed
        ≃L[ℂ] (projectiveTensorModuleStructure A R).Completed,
      ∀ w : A ⊗[ℂ] R,
        E ((inductiveTensorModuleStructure A R).incl w) =
          (projectiveTensorModuleStructure A R).incl w := by
  obtain ⟨haddA, hpolyA, hmetricA, hcompleteA⟩ := hA
  obtain ⟨haddR, hpolyR, hmetricR, _⟩ := hR
  letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A
  haveI : IsUniformAddGroup A := isUniformAddGroup_of_addCommGroup
  haveI : ContinuousSMul ℂ A := (PolynormableSpace.withSeminorms ℂ A).continuousSMul
  haveI : (uniformity A).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  haveI : BaireSpace A := BaireSpace.of_completelyPseudoMetrizable
  have h : inductiveTensorTopology A R = projectiveTensorTopology A R :=
    frechet_inductive_projective_tensor_equal
  exact ⟨TopologicalModuleStructure.completionEquiv h,
    TopologicalModuleStructure.completionEquiv_incl h⟩

set_option maxHeartbeats 800000 in
/-- The canonical comparison of the completed inductive and projective
tensor products on a fixed angular stage and the radial decay space. -/
theorem exists_decayStage_completedTensorComparison
    (p : WholeBruhatStage K) (I : Set ℝ) (hInt : OrdConnected I) (hI : I.Nonempty) :
    ∃ E : (inductiveTensorModuleStructure p.val.Space (PositiveRealExponentialDecay I)).Completed
        ≃L[ℂ]
        (projectiveTensorModuleStructure p.val.Space (PositiveRealExponentialDecay I)).Completed,
      ∀ w : p.val.Space ⊗[ℂ] PositiveRealExponentialDecay I,
        E ((inductiveTensorModuleStructure p.val.Space (PositiveRealExponentialDecay I)).incl w) =
          (projectiveTensorModuleStructure p.val.Space (PositiveRealExponentialDecay I)).incl w := by
  have hA : IsFrechetTVS p.val.Space := @elementarySchwartz_frechet
    p.val.2.realDim p.val.2.torusDim p.val.2.latticeRank p.val.2.finiteFactor
    p.val.2.finiteGroup p.val.2.finiteTopology p.val.2.finiteDiscrete (Finite.of_fintype _)
  exact exists_frechet_completedTensorComparison hA (positiveRealExponentialDecay_frechet I hInt hI)

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G]
  [IsTopologicalGroup K] [T2Space K] [LocallyCompactSpace K]

set_option maxHeartbeats 1000000 in
/-- The canonical map from the completed inductive tensor product to
a compatible decay stage is continuous and realizes multiplication. -/
theorem exists_splitStage_completedInductiveTensorMap
    (m : G →ₜ* Multiplicative ℝ) (hm : IsProperMap m) (α : G →ₜ* K)
    (p : WholeBruhatStage K) (q : WholeBruhatStage G)
    (hker : q.val.1.kernel ≤ p.val.1.kernel.comap α.toMonoidHom)
    (I : Set ℝ) (hI : I.Nonempty) (hInt : OrdConnected I) :
    ∃ F : (inductiveTensorModuleStructure p.val.Space (PositiveRealExponentialDecay I)).Completed
        →L[ℂ] WholeBruhatDecayStage m I q,
      ∀ (a : p.val.Space) (r : PositiveRealExponentialDecay I) (g : G),
        (F ((inductiveTensorModuleStructure p.val.Space (PositiveRealExponentialDecay I)).incl
          (a ⊗ₜ[ℂ] r))).val g = p.val.realize a (α g) * r.val (m g).toAdd := by
  let A := p.val.Space
  let R := PositiveRealExponentialDecay I
  let D := inductiveTensorModuleStructure A R
  let P := projectiveTensorModuleStructure A R
  let Y := WholeBruhatDecayStage m I q
  have hComparison : ∃ E : D.Completed ≃L[ℂ] P.Completed,
      ∀ w : A ⊗[ℂ] R, E (D.incl w) = P.incl w :=
    exists_decayStage_completedTensorComparison (K := K) p I hInt hI
  have hForward : ∃ F : P.Completed →L[ℂ] Y,
      ∀ (a : A) (r : R) (g : G),
        (F (P.incl (a ⊗ₜ[ℂ] r))).val g = p.val.realize a (α g) * r.val (m g).toAdd :=
    exists_splitStage_completedTensorMap (G := G) (H := K) m hm α p q hker I hI hInt
  let E := hComparison.choose
  let F := hForward.choose
  refine ⟨F.comp E.toContinuousLinearMap, fun a r g => ?_⟩
  change (F (E (D.incl (a ⊗ₜ[ℂ] r)))).val g = _
  exact (congrArg (fun z : P.Completed => (F z).val g)
    (hComparison.choose_spec (a ⊗ₜ[ℂ] r))).trans (hForward.choose_spec a r g)

end
end Masullo
