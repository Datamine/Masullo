import ModulatedDecayStageEvaluations
import ModulatedDecaySplitTensorFormula
import CompletedProjectiveTensorSliceSeparation
import InjectiveTensorFlip

open Function Set Topology UniformSpace
open scoped TensorProduct

namespace Masullo

noncomputable section

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G]
  (m : G →ₜ* Multiplicative ℝ) (τ : Multiplicative ℝ →ₜ* G) (hτ : RightInverse τ m)

local notation "K" => m.toMonoidHom.ker

variable [LocallyCompactSpace m.toMonoidHom.ker]

include hτ in
set_option maxHeartbeats 1500000 in
/-- The fixed-stage multiplication map is injective because point evaluations
determine all the slices. -/
theorem splitStage_multiplication_injective
    (p : WholeBruhatStage K) (q : WholeBruhatStage G) (I : Set ℝ) (b : I)
    (hInt : OrdConnected I)
    (F : (projectiveTensorModuleStructure p.val.Space (PositiveRealExponentialDecay I)).Completed
      →L[ℂ] WholeBruhatDecayStage m I q)
    (hF : SplitStageTensorFormula m p q I (modulatedKernelProjection m τ hτ) F) :
    Injective F := by
  let A := p.val.Space
  let R := PositiveRealExponentialDecay I
  let D := projectiveTensorModuleStructure A R
  let Y := WholeBruhatDecayStage m I q
  letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A
  letI : IsUniformAddGroup A := isUniformAddGroup_of_addCommGroup
  letI : ContinuousSMul ℂ A := (PolynormableSpace.withSeminorms ℂ A).continuousSMul
  letI : CompleteSpace A := completeSpace_elementarySchwartz
  letI : T2Space A := elementarySchwartz_t2
  let hI : I.Nonempty := ⟨b, b.property⟩
  let hfrechet := positiveRealExponentialDecay_frechet I hInt hI
  letI : IsTopologicalAddGroup R := hfrechet.choose
  letI : UniformSpace R := IsTopologicalAddGroup.rightUniformSpace R
  letI : IsUniformAddGroup R := isUniformAddGroup_of_addCommGroup
  letI : CompleteSpace R := hfrechet.choose_spec.2.2
  letI : ContinuousSMul ℂ R := (PolynormableSpace.withSeminorms ℂ R).continuousSMul
  letI : T2Space R := (positiveRealExponentialDecay_isEmbedding I hI).t2Space
  let e (x : ℝ) : R →L[ℂ] ℂ := radialDecayEvaluation I b x
  let a (k : K) : A →L[ℂ] ℂ :=
    ⟨(LinearMap.proj k).comp p.val.realize,
      (bruhatSchwartz_continuous_eval k).comp p.val.inclusionCLM.continuous⟩
  let g (x : ℝ) (k : K) := τ (Multiplicative.ofAdd x) * k.val
  let v (x : ℝ) (k : K) : Y →L[ℂ] ℂ := splitDecayStageEvaluation m q I hI (g x k)
  have he : Injective (fun r : R => fun x : ℝ => e x r) := by
    intro r s hrs
    apply Subtype.ext
    funext x
    exact (radialDecayEvaluation_apply I b x r).symm.trans
      ((congrFun hrs x).trans (radialDecayEvaluation_apply I b x s))
  have ha : Injective (fun c : A => fun k : K => a k c) :=
    p.val.1.realizeSchwartz_injective p.val.2
  have hπ : projectiveTensorTopology A R = injectiveTensorTopology A R :=
    tensorTopologies_equal_of_flip ((positiveRealExponentialDecay_nuclear.{0} I hI).2.2 A)
  apply completedProjectiveTensor_injective_of_sliceEvaluations e he a ha hπ F v
  intro x k c r
  have hx : (m (g x k)).toAdd = x := by
    change (m (τ (Multiplicative.ofAdd x) * k.val)).toAdd = x
    rw [map_mul, hτ, show m k.val = 1 from k.property, mul_one]
    rfl
  have hv : v x k (F (D.incl (c ⊗ₜ[ℂ] r))) =
      (F (D.incl (c ⊗ₜ[ℂ] r))).val (g x k) :=
    splitDecayStageEvaluation_apply m q I hI (g x k) _
  have hprod : (F (D.incl (c ⊗ₜ[ℂ] r))).val (g x k) =
      p.val.realize c k * r.val x :=
    (hF c r (g x k)).trans (congrArg₂ (· * ·)
      (congrArg (p.val.realize c) (modulatedKernelProjection_split m τ hτ k x)) (congrArg r.val hx))
  exact (congrArg (fun z : ℂ => z * p.val.realize c k) (radialDecayEvaluation_apply I b x r)).trans
    ((mul_comm _ _).trans (hprod.symm.trans hv.symm))

end
end Masullo
