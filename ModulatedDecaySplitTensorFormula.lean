import ModulatedDecayStageFourierTensors

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

/-- The scalar formula specifying the forward map on elementary tensors. -/
def SplitStageTensorFormula (p : WholeBruhatStage K) (q : WholeBruhatStage G) (I : Set ℝ)
    (α : G →ₜ* K)
    (F : (projectiveTensorModuleStructure p.val.Space (PositiveRealExponentialDecay I)).Completed
      →L[ℂ] WholeBruhatDecayStage m I q) : Prop :=
  ∀ (a : p.val.Space) (r : PositiveRealExponentialDecay I) (g : G),
    (F ((projectiveTensorModuleStructure p.val.Space (PositiveRealExponentialDecay I)).incl
      (a ⊗ₜ[ℂ] r))).val g = p.val.realize a (α g) * r.val (m g).toAdd

include hτ in
/-- The series formula specifying the synthesis map on the decay stage. -/
def SplitStageSynthesisFormula (p : WholeBruhatStage K) (q : WholeBruhatStage G) (I : Set ℝ)
    (hI : I.Nonempty) (hm : IsProperMap m)
    (S : WholeBruhatDecayStage m I q →L[ℂ]
      (projectiveTensorModuleStructure p.val.Space (PositiveRealExponentialDecay I)).Completed) : Prop :=
  ∀ f, HasSum (splitStageFourierTensor m τ hτ ν p hm I hI
    (ModulatedExponentialInductive.stageMap q f)) (S f)

include hτ in
omit [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace K] [BorelSpace K] [LocallyCompactSpace K] [CompactSpace K] in
private theorem split_product_values (f : G → ℂ) (a : K → ℂ) (r : ℝ → ℂ)
    (hF : ∀ g, f g = a (modulatedKernelProjection m τ hτ g) * r (m g).toAdd) :
    ∀ x (k : K), f (τ (Multiplicative.ofAdd x) * k.val) = a k * r x := by
  intro x k
  let g := τ (Multiplicative.ofAdd x) * k.val
  have hg : (m g).toAdd = x := by
    change (m (τ (Multiplicative.ofAdd x) * k.val)).toAdd = x
    rw [map_mul, hτ, show m k.val = 1 from k.property, mul_one]
    rfl
  exact (hF g).trans (congrArg₂ (· * ·)
    (congrArg a (modulatedKernelProjection_split m τ hτ k x)) (congrArg r hg))

include hτ in
set_option maxHeartbeats 40000 in
/-- On a separated tensor, angular coefficient extraction acts on the angular
factor and preserves the radial factor up to that scalar. -/
theorem splitStageTensorFormula_coefficient (p : WholeBruhatStage K) (q : WholeBruhatStage G)
    (hm : IsProperMap m) (I : Set ℝ) (hI : I.Nonempty)
    (F : (projectiveTensorModuleStructure p.val.Space (PositiveRealExponentialDecay I)).Completed
      →L[ℂ] WholeBruhatDecayStage m I q)
    (hF : SplitStageTensorFormula m p q I (modulatedKernelProjection m τ hτ) F)
    (a : p.val.Space) (r : PositiveRealExponentialDecay I) (χ : PontryaginDual K) :
    modulatedDecayAngularCoefficient m τ hτ ν χ I hI hm
      (ModulatedExponentialInductive.stageMap q
        (F ((projectiveTensorModuleStructure p.val.Space (PositiveRealExponentialDecay I)).incl
          (a ⊗ₜ[ℂ] r)))) = compactBruhatFourierCoeff ν χ (p.val.inclusion a) • r := by
  let D := projectiveTensorModuleStructure p.val.Space (PositiveRealExponentialDecay I)
  let f : ModulatedExponentialInductive m I := ModulatedExponentialInductive.stageMap q
    (F (D.incl (a ⊗ₜ[ℂ] r)))
  let u : BruhatSchwartz K := p.val.inclusion a
  have hprod : ∀ g : G, f.val g = u.val (modulatedKernelProjection m τ hτ g) * r.val (m g).toAdd :=
    hF a r
  have hsep : ∀ x (k : K), f.val (τ (Multiplicative.ofAdd x) * k.val) = u.val k * r.val x :=
    split_product_values m τ hτ f.val u.val r.val hprod
  exact @modulatedDecayAngularCoefficient_of_product G _ _ _ _ _ _ m τ hτ _ _ ν _ χ I hI hm
    _ _ _ u r f hsep


end
end Masullo
