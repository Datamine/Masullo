import ModulatedDecaySplitTensorRightInverse
import ModulatedDecaySplitTensorFormula

set_option Elab.async false

open Function MeasureTheory Set Topology

namespace Masullo
noncomputable section

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  (m : G →ₜ* Multiplicative ℝ) (τ : Multiplicative ℝ →ₜ* G) (hτ : RightInverse τ m)

local notation "K" => m.toMonoidHom.ker

variable [LocallyCompactSpace m.toMonoidHom.ker]
  [CompactSpace m.toMonoidHom.ker] [MeasurableSpace m.toMonoidHom.ker] [BorelSpace m.toMonoidHom.ker]

set_option maxHeartbeats 1200000 in
/-- The stage multiplication map has a continuous right inverse. -/
theorem splitStage_multiplication_hasContinuousRightInverse
    (ν : Measure K) [ν.IsHaarMeasure] [IsProbabilityMeasure ν]
    (p : WholeBruhatStage K) (q : WholeBruhatStage G)
    (hq : q.val.1.kernel = p.val.1.kernel.map m.toMonoidHom.ker.subtype)
    (hm : IsProperMap m) (I : Set ℝ) (t : I)
    (F : (projectiveTensorModuleStructure p.val.Space (PositiveRealExponentialDecay I)).Completed
      →L[ℂ] WholeBruhatDecayStage m I q)
    (hF : SplitStageTensorFormula m p q I (modulatedKernelProjection m τ hτ) F) :
    ∃ S : WholeBruhatDecayStage m I q →L[ℂ]
        (projectiveTensorModuleStructure p.val.Space (PositiveRealExponentialDecay I)).Completed,
      F.comp S = ContinuousLinearMap.id ℂ (WholeBruhatDecayStage m I q) := by
  let es := exists_splitStageFourierSynthesis m τ hτ ν p q hm I ⟨t, t.property⟩
  exact ⟨es.choose, splitStageSynthesis_rightInverse m τ hτ ν p q hq hm I t F hF es.choose es.choose_spec⟩


end
end Masullo
