import ModulatedDecaySplitFourierSynthesis
import ModulatedDecayAngularInversion

set_option Elab.async false

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

private def splitStageScalarEvaluation (q : WholeBruhatStage G) (I : Set ℝ) (hI : I.Nonempty)
    (g : G) : WholeBruhatDecayStage m I q →L[ℂ] ℂ :=
  (ModulatedExponentialInductive.evaluation m I hI g).comp
    ⟨ModulatedExponentialInductive.stageMap q, ModulatedExponentialInductive.stageMap_continuous q⟩

include hτ in
set_option maxHeartbeats 600000 in
private theorem hasSum_splitStageTensorFormula_values
    (p : WholeBruhatStage K) (q : WholeBruhatStage G)
    (hq : q.val.1.kernel = p.val.1.kernel.map m.toMonoidHom.ker.subtype)
    (hm : IsProperMap m) (I : Set ℝ) (b : I)
    (F : (projectiveTensorModuleStructure p.val.Space (PositiveRealExponentialDecay I)).Completed
      →L[ℂ] WholeBruhatDecayStage m I q)
    (hF : ∀ (a : p.val.Space) (r : PositiveRealExponentialDecay I) (g : G),
      (F ((projectiveTensorModuleStructure p.val.Space (PositiveRealExponentialDecay I)).incl
        (a ⊗ₜ[ℂ] r))).val g =
        p.val.realize a (modulatedKernelProjection m τ hτ g) * r.val (m g).toAdd)
    (f : WholeBruhatDecayStage m I q) (g : G) :
    HasSum (fun θ => (F (splitStageFourierTensor m τ hτ ν p hm I ⟨b,b.property⟩
      (ModulatedExponentialInductive.stageMap q f) θ)).val g) (f.val g) := by
  let u : K := modulatedKernelProjection m τ hτ g
  let x := (m g).toAdd
  have hu : τ (Multiplicative.ofAdd x) * u.val = g := by
    change τ (m g) * (g / τ (m g)) = g
    rw [mul_comm, div_mul_cancel]
  let Ω := PontryaginDual (Multiplicative p.CoordinateModel)
  let r (θ : Ω) := modulatedDecayAngularCoefficient m τ hτ ν (θ.comp p.coordinates) I
    ⟨b,b.property⟩ hm (ModulatedExponentialInductive.stageMap q f)
  let s (θ : Ω) := (r θ).val x * ((θ⁻¹) (p.coordinates u) : ℂ)
  have hs : HasSum s (f.val (τ (Multiplicative.ofAdd x) * u.val)) :=
    hasSum_splitStage_elementaryAngularFourier m τ hτ ν hm p q hq I b f x u
  have hv : HasSum s (f.val g) := by
    rw [← hu]
    exact hs
  refine hv.congr_fun fun θ => ?_
  let a : p.val.Space := splitStageInverseCharacter m p θ
  have ha : p.val.realize a u = ((θ⁻¹) (p.coordinates u) : ℂ) :=
    splitStageInverseCharacter_realize m p θ u
  have hfwd : (F ((projectiveTensorModuleStructure p.val.Space (PositiveRealExponentialDecay I)).incl
      (a ⊗ₜ[ℂ] r θ))).val g = p.val.realize a u * (r θ).val x := hF a (r θ) g
  change (F ((projectiveTensorModuleStructure p.val.Space (PositiveRealExponentialDecay I)).incl
    (a ⊗ₜ[ℂ] r θ))).val g = s θ
  exact hfwd.trans ((congrArg (fun z : ℂ => z * (r θ).val x) ha).trans (mul_comm _ _))


include hτ in
set_option maxHeartbeats 1100000 in
/-- The Fourier synthesis map is a right inverse to fixed-stage multiplication. -/
theorem splitStageSynthesis_rightInverse
    (p : WholeBruhatStage K) (q : WholeBruhatStage G)
    (hq : q.val.1.kernel = p.val.1.kernel.map m.toMonoidHom.ker.subtype)
    (hm : IsProperMap m) (I : Set ℝ) (b : I)
    (F : (projectiveTensorModuleStructure p.val.Space (PositiveRealExponentialDecay I)).Completed
      →L[ℂ] WholeBruhatDecayStage m I q)
    (hF : ∀ (a : p.val.Space) (r : PositiveRealExponentialDecay I) (g : G),
      (F ((projectiveTensorModuleStructure p.val.Space (PositiveRealExponentialDecay I)).incl
        (a ⊗ₜ[ℂ] r))).val g =
        p.val.realize a (modulatedKernelProjection m τ hτ g) * r.val (m g).toAdd)
    (S : WholeBruhatDecayStage m I q →L[ℂ]
      (projectiveTensorModuleStructure p.val.Space (PositiveRealExponentialDecay I)).Completed)
    (hS : ∀ f, HasSum (splitStageFourierTensor m τ hτ ν p hm I ⟨b, b.property⟩
      (ModulatedExponentialInductive.stageMap q f)) (S f)) :
    F.comp S = ContinuousLinearMap.id ℂ _ := by
  let Y := WholeBruhatDecayStage m I q
  let ev := splitStageScalarEvaluation m q I ⟨b, b.property⟩
  have hinj : Injective (fun y : Y => fun g : G => ev g y) :=
    fun _ _ he => WholeBruhatDecayStage.algebraicEquiv.injective (Subtype.ext he)
  let t (f : Y) := splitStageFourierTensor m τ hτ ν p hm I ⟨b, b.property⟩
    (ModulatedExponentialInductive.stageMap q f)
  have hv (f : Y) (g : G) : HasSum (fun θ => ev g (F (t f θ))) (ev g f) :=
    hasSum_splitStageTensorFormula_values m τ hτ ν p q hq hm I b F hF f g
  exact continuousLinearMap_comp_eq_id_of_scalar_sums F S ev hinj t hS hv

end
end Masullo
