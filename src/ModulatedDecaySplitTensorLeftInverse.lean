import ModulatedDecaySplitTensorFormula
import CompactBruhatStageFourierReconstruction

open Function MeasureTheory Set Topology
open scoped TensorProduct

namespace Masullo

noncomputable section

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  (m : G →ₜ* Multiplicative ℝ) (τ : Multiplicative ℝ →ₜ* G) (hτ : RightInverse τ m)

local notation "K" => m.toMonoidHom.ker

variable [MeasurableSpace m.toMonoidHom.ker] [BorelSpace m.toMonoidHom.ker]
  (ν : Measure m.toMonoidHom.ker) [ν.IsHaarMeasure] [IsProbabilityMeasure ν]
  [LocallyCompactSpace m.toMonoidHom.ker] [CompactSpace m.toMonoidHom.ker]

include hτ in
set_option maxHeartbeats 3800000 in
/-- The specified Fourier synthesis map is a left inverse of the split
product map on the completed projective tensors. -/
theorem splitStageSynthesis_leftInverse_of_coefficients
    (p : WholeBruhatStage K) (q : WholeBruhatStage G) (hm : IsProperMap m)
    (I : Set ℝ) (hI : I.Nonempty)
    (F : (projectiveTensorModuleStructure p.val.Space (PositiveRealExponentialDecay I)).Completed
      →L[ℂ] WholeBruhatDecayStage m I q)
    (S : WholeBruhatDecayStage m I q →L[ℂ]
      (projectiveTensorModuleStructure p.val.Space (PositiveRealExponentialDecay I)).Completed)
    (hS : ∀ f, HasSum (splitStageFourierTensor m τ hτ ν p hm I hI
      (ModulatedExponentialInductive.stageMap q f)) (S f))
    (hc : ∀ (x : p.val.Space) (r : PositiveRealExponentialDecay I) (χ : PontryaginDual K),
      modulatedDecayAngularCoefficient m τ hτ ν χ I hI hm
        (ModulatedExponentialInductive.stageMap q
          (F ((projectiveTensorModuleStructure p.val.Space (PositiveRealExponentialDecay I)).incl
            (x ⊗ₜ[ℂ] r)))) = compactBruhatFourierCoeff ν χ (p.val.inclusion x) • r) :
    S.comp F = ContinuousLinearMap.id ℂ _ := by
  let A := p.val.Space
  let R := PositiveRealExponentialDecay I
  let D := projectiveTensorModuleStructure A R
  let Ω := PontryaginDual (Multiplicative p.CoordinateModel)
  let a (θ : Ω) : A := splitStageInverseCharacter m p θ
  let c (x : A) (θ : Ω) := compactBruhatFourierCoeff ν (θ.comp p.coordinates) (p.val.inclusion x)
  letI : CompactSpace p.CoordinateModel := (Multiplicative.toAdd.surjective.comp p.coordinates_surjective).compactSpace
    (continuous_toAdd.comp p.coordinates.continuous)
  have hA (x : A) : HasSum (fun θ => c x θ • a θ) x :=
    hasSum_compactBruhatStage_elementaryFourier ν p x
  letI : IsTopologicalAddGroup A := (PolynormableSpace.withSeminorms ℂ A).topologicalAddGroup
  letI : IsTopologicalAddGroup R := (PolynormableSpace.withSeminorms ℂ R).topologicalAddGroup
  refine @completedProjectiveTensor_leftInverse_of_angularSeries
    A R (WholeBruhatDecayStage m I q) Ω _ _ _ _ _ _ _ _ _ _ _ F S a c hA ?_
  intro x r
  let f := F (D.incl (x ⊗ₜ[ℂ] r))
  have hs : HasSum (splitStageFourierTensor m τ hτ ν p hm I hI
      (ModulatedExponentialInductive.stageMap q f)) (S f) := hS f
  refine hs.congr_fun fun θ => ?_
  have hc : modulatedDecayAngularCoefficient m τ hτ ν (θ.comp p.coordinates) I hI hm
      (ModulatedExponentialInductive.stageMap q f) = c x θ • r :=
    hc x r (θ.comp p.coordinates)
  exact congrArg (fun z : R => D.incl (a θ ⊗ₜ[ℂ] z)) hc.symm


include hτ in
set_option maxHeartbeats 1500000 in
/-- The angular synthesis is a left inverse to multiplication on the
completed projective tensor of a fixed stage. -/
theorem splitStageSynthesis_leftInverse
    (p : WholeBruhatStage K) (q : WholeBruhatStage G) (hm : IsProperMap m)
    (I : Set ℝ) (hI : I.Nonempty)
    (F : (projectiveTensorModuleStructure p.val.Space (PositiveRealExponentialDecay I)).Completed
      →L[ℂ] WholeBruhatDecayStage m I q)
    (S : WholeBruhatDecayStage m I q →L[ℂ]
      (projectiveTensorModuleStructure p.val.Space (PositiveRealExponentialDecay I)).Completed)
    (hF : SplitStageTensorFormula m p q I (modulatedKernelProjection m τ hτ) F)
    (hS : SplitStageSynthesisFormula m τ hτ ν p q I hI hm S) :
    S.comp F = ContinuousLinearMap.id ℂ _ :=
  splitStageSynthesis_leftInverse_of_coefficients m τ hτ ν p q hm I hI F S hS
    (splitStageTensorFormula_coefficient m τ hτ ν p q hm I hI F hF)

end
end Masullo
