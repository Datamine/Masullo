import ModulatedDecaySplitTensor

open Function Set Topology UniformSpace
open scoped SchwartzMap TensorProduct

namespace Masullo

noncomputable section

private def radialWeightedEvaluation (I : Set ℝ) (b : I) (x : ℝ) :
    PositiveRealExponentialDecay I →L[ℂ] ℂ := by
  let R := PositiveRealExponentialDecay I
  let T : R →ₗ[ℂ] 𝓢(ℝ, ℂ) := logExponentialDecayTwist I b
  have hT : Continuous T := (continuous_apply b).comp
    (positiveRealExponentialDecay_isEmbedding I ⟨b, b.property⟩).continuous
  exact ⟨{ toFun := fun f => T f x
           map_add' := fun f g => by rw [T.map_add]; rfl
           map_smul' := fun c f => by rw [T.map_smul]; rfl },
    ((BoundedContinuousFunction.lipschitz_eval_const x).continuous.comp
      (SchwartzMap.toBoundedContinuousFunctionCLM ℂ ℝ ℂ).continuous).comp hT⟩

/-- Continuous point evaluation on the radial decay test space. -/
def radialDecayEvaluation (I : Set ℝ) (b : I) (x : ℝ) :
    PositiveRealExponentialDecay I →L[ℂ] ℂ :=
  ((Real.exp ((b : ℝ) * x) : ℂ)⁻¹) • radialWeightedEvaluation I b x

@[simp] theorem radialDecayEvaluation_apply (I : Set ℝ) (b : I) (x : ℝ)
    (f : PositiveRealExponentialDecay I) : radialDecayEvaluation I b x f = f.val x := by
  change (Real.exp ((b : ℝ) * x) : ℂ)⁻¹ * (logExponentialDecayTwist I b f) x = f.val x
  let c : ℂ := Real.exp ((b : ℝ) * x)
  have hc : c ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)
  exact (congrArg (fun w : ℂ => c⁻¹ * w) (logExponentialDecayTwist_apply I b f x)).trans
    (by rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul])

universe u

variable {G : Type u} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G]
  (m : G →ₜ* Multiplicative ℝ)


/-- The value at a point of a decay stage, as a continuous linear map. -/
def splitDecayStageEvaluation (q : WholeBruhatStage G) (I : Set ℝ) (hI : I.Nonempty)
    (g : G) : WholeBruhatDecayStage m I q →L[ℂ] ℂ :=
  (ModulatedExponentialInductive.evaluation m I hI g).comp
    ⟨ModulatedExponentialInductive.stageMap q, ModulatedExponentialInductive.stageMap_continuous q⟩



@[simp] theorem splitDecayStageEvaluation_apply (q : WholeBruhatStage G)
    (I : Set ℝ) (hI : I.Nonempty) (g : G) (f : WholeBruhatDecayStage m I q) :
    splitDecayStageEvaluation m q I hI g f = f.val g := rfl

end
end Masullo
