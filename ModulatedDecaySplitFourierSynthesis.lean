import ModulatedDecayStageFourierTensors

open Function MeasureTheory Set Topology UniformSpace
open scoped TensorProduct

namespace Masullo

noncomputable section

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  (m : G →ₜ* Multiplicative ℝ) (τ : Multiplicative ℝ →ₜ* G) (hτ : RightInverse τ m)

local notation "K" => m.toMonoidHom.ker

variable [MeasurableSpace m.toMonoidHom.ker] [BorelSpace m.toMonoidHom.ker]
  (ν : Measure m.toMonoidHom.ker) [ν.IsHaarMeasure]
  [LocallyCompactSpace m.toMonoidHom.ker] [CompactSpace m.toMonoidHom.ker]

include hτ in
set_option maxHeartbeats 3500000 in
/-- Fourier synthesis into the completed tensor product is continuous on a decay stage. -/
theorem exists_splitStageFourierSynthesis
    (p : WholeBruhatStage K) (q : WholeBruhatStage G)
    (hm : IsProperMap m) (I : Set ℝ) (hI : I.Nonempty) :
    ∃ R : WholeBruhatDecayStage m I q →L[ℂ]
      (projectiveTensorModuleStructure p.val.Space (PositiveRealExponentialDecay I)).Completed,
      ∀ f, HasSum (splitStageFourierTensor m τ hτ ν p hm I hI
        (ModulatedExponentialInductive.stageMap q f)) (R f) := by
  let Y := WholeBruhatDecayStage m I q
  letI : UniformSpace Y := IsTopologicalAddGroup.rightUniformSpace Y
  letI : IsUniformAddGroup Y := isUniformAddGroup_of_addCommGroup
  letI : ContinuousSMul ℂ Y := (PolynormableSpace.withSeminorms ℂ Y).continuousSMul
  letI : BarrelledSpace ℂ Y :=
    isFrechetTVS_barrelled (wholeBruhatDecayStage_separableNuclearFrechet m hI q).2.2
  let s : Y →L[ℂ] ModulatedExponentialInductive m I :=
    ⟨ModulatedExponentialInductive.stageMap q, ModulatedExponentialInductive.stageMap_continuous q⟩
  letI : CompactSpace p.CoordinateModel := (Multiplicative.toAdd.surjective.comp p.coordinates_surjective).compactSpace
    (continuous_toAdd.comp p.coordinates.continuous)
  let c := p.val.2
  exact @exists_completed_splitAngularFourierSynthesis c.realDim c.torusDim c.latticeRank c.finiteFactor
    c.finiteGroup c.finiteTopology c.finiteDiscrete (Finite.of_fintype _)
    G _ _ _ _ _ _ m _ τ hτ _ _ ν _ Y _ _ _ _ _ _ _ _
    p.coordinates p.coordinates_surjective hm I hI s

end

end Masullo
