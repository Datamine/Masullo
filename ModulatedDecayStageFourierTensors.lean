import ModulatedDecayTensorSummability
import ModulatedDecaySplitCoordinates

open Function MeasureTheory Set Topology
open scoped TensorProduct

namespace Masullo

noncomputable section

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  (m : G →ₜ* Multiplicative ℝ) (τ : Multiplicative ℝ →ₜ* G) (hτ : RightInverse τ m)

local notation "K" => m.toMonoidHom.ker

variable [MeasurableSpace m.toMonoidHom.ker] [BorelSpace m.toMonoidHom.ker]
  (ν : Measure m.toMonoidHom.ker) [ν.IsHaarMeasure]

/-- The inverse character of the angular quotient as a test in its stage. -/
def splitStageInverseCharacter [CompactSpace K] (p : WholeBruhatStage K)
    (θ : PontryaginDual (Multiplicative p.CoordinateModel)) : p.val.Space := by
  letI : CompactSpace p.CoordinateModel := (Multiplicative.toAdd.surjective.comp p.coordinates_surjective).compactSpace
    (continuous_toAdd.comp p.coordinates.continuous)
  exact compactElementaryInverseCharacterTest θ

omit [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace m.toMonoidHom.ker] [BorelSpace m.toMonoidHom.ker] in
theorem splitStageInverseCharacter_realize [CompactSpace K] (p : WholeBruhatStage K)
    (θ : PontryaginDual (Multiplicative p.CoordinateModel)) (u : K) :
    p.val.realize (splitStageInverseCharacter m p θ) u = ((θ⁻¹) (p.coordinates u) : ℂ) :=
  p.realize_eq_coordinates _ _

variable [LocallyCompactSpace m.toMonoidHom.ker] [CompactSpace m.toMonoidHom.ker]

include hτ in
/-- The elementary tensor formed from one angular character and its radial coefficient. -/
def splitStageFourierTensor
    (p : WholeBruhatStage K) (hm : IsProperMap m) (I : Set ℝ) (hI : I.Nonempty)
    (f : ModulatedExponentialInductive m I) (θ : PontryaginDual (Multiplicative p.CoordinateModel)) :
    (projectiveTensorModuleStructure p.val.Space (PositiveRealExponentialDecay I)).Completed :=
  (projectiveTensorModuleStructure p.val.Space (PositiveRealExponentialDecay I)).incl
    (splitStageInverseCharacter m p θ ⊗ₜ[ℂ]
      modulatedDecayAngularCoefficient m τ hτ ν (θ.comp p.coordinates) I hI hm f)

include hτ in
set_option maxHeartbeats 1500000 in
/-- The Fourier tensors are summable in the completion of the prescribed angular stage. -/
theorem summable_splitStageFourierTensor
    (p : WholeBruhatStage K) (hm : IsProperMap m) (I : Set ℝ) (hI : I.Nonempty)
    (f : ModulatedExponentialInductive m I) :
    Summable (splitStageFourierTensor m τ hτ ν p hm I hI f) := by
  rcases p with ⟨⟨P, c⟩, hP⟩
  rcases c with @⟨d, n, r, T, gT, fT, tT, dT, e⟩
  letI : AddCommGroup T := gT
  letI : Fintype T := fT
  letI : TopologicalSpace T := tT
  letI : DiscreteTopology T := dT
  let p : WholeBruhatStage K := ⟨⟨P, ⟨d, n, r, T, e⟩⟩, hP⟩
  letI : CompactSpace (ElementaryLCAModel d n r T) :=
    (Multiplicative.toAdd.surjective.comp p.coordinates_surjective).compactSpace
      (continuous_toAdd.comp p.coordinates.continuous)
  exact @summable_completed_splitAngularFourier d n r T gT tT dT (Finite.of_fintype _)
    G _ _ _ _ _ _ m _ τ hτ _ _ ν _ _ _ p.coordinates p.coordinates_surjective hm I hI f

end
end Masullo
