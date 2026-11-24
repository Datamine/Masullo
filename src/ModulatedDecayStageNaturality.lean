import CompletedProjectiveTensorMaps
import ModulatedDecayStructure
import ModulatedDecaySplitTensor

open Function Set Topology
open scoped TensorProduct

namespace Masullo

noncomputable section

variable {G H : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G]
  [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]
  [LocallyCompactSpace H]

set_option maxHeartbeats 1200000 in
/-- The canonical completed projective multiplication maps commute with
simultaneous refinements of their angular and whole-group stages. -/
theorem splitStage_completedTensorMap_natural
    (m : G →ₜ* Multiplicative ℝ) (α : G →ₜ* H)
    (I : Set ℝ) (hI : I.Nonempty) (p p' : WholeBruhatStage H) (q q' : WholeBruhatStage G)
    (hp : p.val.1 ≤ p'.val.1) (hq : q.val.1 ≤ q'.val.1)
    (F : (projectiveTensorModuleStructure p.val.Space (PositiveRealExponentialDecay I)).Completed
        →L[ℂ] WholeBruhatDecayStage m I q)
    (F' : (projectiveTensorModuleStructure p'.val.Space (PositiveRealExponentialDecay I)).Completed
        →L[ℂ] WholeBruhatDecayStage m I q')
    (hF : ∀ (a : p.val.Space) (r : PositiveRealExponentialDecay I) (g : G),
      (F ((projectiveTensorModuleStructure p.val.Space (PositiveRealExponentialDecay I)).incl
        (a ⊗ₜ[ℂ] r))).val g = p.val.realize a (α g) * r.val (m g).toAdd)
    (hF' : ∀ (a : p'.val.Space) (r : PositiveRealExponentialDecay I) (g : G),
      (F' ((projectiveTensorModuleStructure p'.val.Space (PositiveRealExponentialDecay I)).incl
        (a ⊗ₜ[ℂ] r))).val g = p'.val.realize a (α g) * r.val (m g).toAdd) :
    (wholeBruhatDecayStageTransition m I q q' hq).comp F =
      F'.comp (completedProjectiveTensor_mapLeft (p.val.transition p'.val hp)) := by
  let Y := WholeBruhatDecayStage m I q
  let Z := WholeBruhatDecayStage m I q'
  let R := PositiveRealExponentialDecay I
  let D := projectiveTensorModuleStructure p.val.Space R
  let P := projectiveTensorModuleStructure p'.val.Space R
  let j : p.val.Space →L[ℂ] p'.val.Space := p.val.transition p'.val hp
  let k : Y →L[ℂ] Z := wholeBruhatDecayStageTransition m I q q' hq
  let e (g : G) : Z →L[ℂ] ℂ :=
    (ModulatedExponentialInductive.evaluation m I hI g).comp
      ⟨ModulatedExponentialInductive.stageMap q', ModulatedExponentialInductive.stageMap_continuous q'⟩
  have he : Injective (fun z : Z => fun g : G => e g z) :=
    fun _ _ h => WholeBruhatDecayStage.algebraicEquiv.injective (Subtype.ext h)
  apply completedProjectiveTensor_mapLeft_natural
    (A := p.val.Space) (B := p'.val.Space) (R := R) (Y := Y) (Z := Z) j k F F' e he
  intro a r g
  change (k (F (D.incl (a ⊗ₜ[ℂ] r)))).val g =
    (F' (P.incl (j a ⊗ₜ[ℂ] r))).val g
  have hk : (k (F (D.incl (a ⊗ₜ[ℂ] r)))).val g =
      (F (D.incl (a ⊗ₜ[ℂ] r))).val g :=
    congrFun (wholeBruhatDecayStageTransition_val m I q q' hq
      (F (D.incl (a ⊗ₜ[ℂ] r)))) g
  have hj : p'.val.realize (j a) (α g) = p.val.realize a (α g) :=
    congrArg (fun f : BruhatSchwartz H => f.val (α g))
      (BruhatSchwartzStage.inclusion_transition p.val p'.val hp a)
  exact hk.trans ((hF a r g).trans
    ((congrArg (fun z : ℂ => z * r.val (m g).toAdd) hj.symm).trans (hF' (j a) r g).symm))

end
end Masullo
