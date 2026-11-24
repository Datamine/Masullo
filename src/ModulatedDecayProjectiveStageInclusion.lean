import ModulatedDecayGlobalTensor
import ModulatedDecayStageTensorComparison
import CompletedProjectiveTensorMaps
import CompletedInductiveTensorMaps

open Function Set Topology UniformSpace
open scoped TensorProduct

namespace Masullo

noncomputable section

variable {H : Type*} [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H]
  [T2Space H] [LocallyCompactSpace H]

set_option maxHeartbeats 800000 in
/-- A fixed projective stage maps continuously into the full inductive
tensor product by angular inclusion and the identity on the radial factor. -/
theorem exists_projectiveStageTensor_to_global
    (p : WholeBruhatStage H) (I : Set ℝ) (hI : I.Nonempty) (hInt : OrdConnected I) :
    ∃ J : (projectiveTensorModuleStructure p.val.Space (PositiveRealExponentialDecay I)).Completed
        →L[ℂ] (inductiveTensorModuleStructure (BruhatSchwartz H) (PositiveRealExponentialDecay I)).Completed,
      ∀ (a : p.val.Space) (r : PositiveRealExponentialDecay I),
        J ((projectiveTensorModuleStructure p.val.Space (PositiveRealExponentialDecay I)).incl
          (a ⊗ₜ[ℂ] r)) =
        (inductiveTensorModuleStructure (BruhatSchwartz H) (PositiveRealExponentialDecay I)).incl
          (p.val.inclusionCLM a ⊗ₜ[ℂ] r) := by
  let A := p.val.Space
  let B := BruhatSchwartz H
  let R := PositiveRealExponentialDecay I
  let D := inductiveTensorModuleStructure A R
  let P := projectiveTensorModuleStructure A R
  let T := inductiveTensorModuleStructure B R
  letI : IsTopologicalAddGroup A := (PolynormableSpace.withSeminorms ℂ A).topologicalAddGroup
  letI : IsTopologicalAddGroup B := (PolynormableSpace.withSeminorms ℂ B).topologicalAddGroup
  letI : IsTopologicalAddGroup R := (PolynormableSpace.withSeminorms ℂ R).topologicalAddGroup
  have hComparison : ∃ e : D.Completed ≃L[ℂ] P.Completed,
      ∀ w : A ⊗[ℂ] R, e (D.incl w) = P.incl w :=
    exists_decayStage_completedTensorComparison (K := H) p I hInt hI
  let e := hComparison.choose
  let j : A →L[ℂ] B := p.val.inclusionCLM
  let U : D.Completed →L[ℂ] T.Completed :=
    completedInductiveTensor_map j (ContinuousLinearMap.id ℂ R)
  refine ⟨U.comp e.symm.toContinuousLinearMap, fun a r => ?_⟩
  have he : e.symm (P.incl (a ⊗ₜ[ℂ] r)) = D.incl (a ⊗ₜ[ℂ] r) :=
    e.symm_apply_eq.mpr (hComparison.choose_spec (a ⊗ₜ[ℂ] r)).symm
  have hu : U (D.incl (a ⊗ₜ[ℂ] r)) = T.incl (j a ⊗ₜ[ℂ] r) :=
    @completedInductiveTensor_map_tmul A B R R _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      j (ContinuousLinearMap.id ℂ R) a r
  exact (congrArg U he).trans hu

set_option maxHeartbeats 950000 in
/-- The inclusions into the full tensor completion agree under angular refinement. -/
theorem projectiveStageTensor_to_global_refinement
    (p p' : WholeBruhatStage H) (hp : p.val.1 ≤ p'.val.1) (I : Set ℝ)
    (J : (projectiveTensorModuleStructure p.val.Space (PositiveRealExponentialDecay I)).Completed
      →L[ℂ] (inductiveTensorModuleStructure (BruhatSchwartz H) (PositiveRealExponentialDecay I)).Completed)
    (J' : (projectiveTensorModuleStructure p'.val.Space (PositiveRealExponentialDecay I)).Completed
      →L[ℂ] (inductiveTensorModuleStructure (BruhatSchwartz H) (PositiveRealExponentialDecay I)).Completed)
    (hJ : ∀ (a : p.val.Space) (r : PositiveRealExponentialDecay I),
      J ((projectiveTensorModuleStructure p.val.Space (PositiveRealExponentialDecay I)).incl (a ⊗ₜ[ℂ] r)) =
        (inductiveTensorModuleStructure (BruhatSchwartz H) (PositiveRealExponentialDecay I)).incl
          (p.val.inclusionCLM a ⊗ₜ[ℂ] r))
    (hJ' : ∀ (a : p'.val.Space) (r : PositiveRealExponentialDecay I),
      J' ((projectiveTensorModuleStructure p'.val.Space (PositiveRealExponentialDecay I)).incl (a ⊗ₜ[ℂ] r)) =
        (inductiveTensorModuleStructure (BruhatSchwartz H) (PositiveRealExponentialDecay I)).incl
          (p'.val.inclusionCLM a ⊗ₜ[ℂ] r)) :
    J'.comp (completedProjectiveTensor_mapLeft (p.val.transition p'.val hp)) = J := by
  let A := p.val.Space
  let B := p'.val.Space
  let R := PositiveRealExponentialDecay I
  let V := BruhatSchwartz H
  let X := V ⊗[ℂ] R
  let D := projectiveTensorModuleStructure A R
  let P := projectiveTensorModuleStructure B R
  let T := inductiveTensorModuleStructure V R
  let j : A →L[ℂ] B := p.val.transition p'.val hp
  letI : UniformSpace X := T.uniformSpace
  letI : IsUniformAddGroup X := T.uniformGroup
  letI : IsUniformAddGroup T.Completed := Completion.isUniformAddGroup
  letI : T0Space T.Completed := Completion.t0Space X
  apply D.continuousLinearMap_ext_on_tmul
  intro a r
  have ht : completedProjectiveTensor_mapLeft j (D.incl (a ⊗ₜ[ℂ] r)) =
      P.incl (j a ⊗ₜ[ℂ] r) :=
    completedProjectiveTensor_mapLeft_tmul j a r
  have hi : p'.val.inclusionCLM (j a) = p.val.inclusionCLM a :=
    p.val.inclusion_transition p'.val hp a
  exact (congrArg J' ht).trans ((hJ' (j a) r).trans
    ((congrArg (fun x : V => T.incl (x ⊗ₜ[ℂ] r)) hi).trans (hJ a r).symm))

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G]

set_option maxHeartbeats 950000 in
/-- The projective stage inclusion intertwines the two multiplication maps. -/
theorem projectiveStageTensor_to_global_multiply
    (m : G →ₜ* Multiplicative ℝ) (α : G →ₜ* H)
    (p : WholeBruhatStage H) (q : WholeBruhatStage G) (I : Set ℝ) (hI : I.Nonempty)
    (J : (projectiveTensorModuleStructure p.val.Space (PositiveRealExponentialDecay I)).Completed
      →L[ℂ] (inductiveTensorModuleStructure (BruhatSchwartz H) (PositiveRealExponentialDecay I)).Completed)
    (F : (projectiveTensorModuleStructure p.val.Space (PositiveRealExponentialDecay I)).Completed
      →L[ℂ] WholeBruhatDecayStage m I q)
    (F' : (inductiveTensorModuleStructure (BruhatSchwartz H) (PositiveRealExponentialDecay I)).Completed
      →L[ℂ] ModulatedExponentialInductive m I)
    (hJ : ∀ (a : p.val.Space) (r : PositiveRealExponentialDecay I),
      J ((projectiveTensorModuleStructure p.val.Space (PositiveRealExponentialDecay I)).incl (a ⊗ₜ[ℂ] r)) =
        (inductiveTensorModuleStructure (BruhatSchwartz H) (PositiveRealExponentialDecay I)).incl
          (p.val.inclusionCLM a ⊗ₜ[ℂ] r))
    (hF : ∀ (a : p.val.Space) (r : PositiveRealExponentialDecay I) (g : G),
      (F ((projectiveTensorModuleStructure p.val.Space (PositiveRealExponentialDecay I)).incl
        (a ⊗ₜ[ℂ] r))).val g = p.val.realize a (α g) * r.val (m g).toAdd)
    (hF' : ∀ (a : BruhatSchwartz H) (r : PositiveRealExponentialDecay I) (g : G),
      (F' ((inductiveTensorModuleStructure (BruhatSchwartz H) (PositiveRealExponentialDecay I)).incl
        (a ⊗ₜ[ℂ] r))).val g = a.val (α g) * r.val (m g).toAdd) :
    ∀ z, F' (J z) = ModulatedExponentialInductive.stageMap q (F z) := by
  let Y := ModulatedExponentialInductive m I
  let R := PositiveRealExponentialDecay I
  let D := projectiveTensorModuleStructure p.val.Space R
  let T := inductiveTensorModuleStructure (BruhatSchwartz H) R
  letI : T2Space Y := ModulatedExponentialInductive.t2 m I hI
  let C : WholeBruhatDecayStage m I q →L[ℂ] Y :=
    ⟨ModulatedExponentialInductive.stageMap q, ModulatedExponentialInductive.stageMap_continuous q⟩
  have he : F'.comp J = C.comp F := by
    apply D.continuousLinearMap_ext_on_tmul
    intro a r
    apply ModulatedExponentialInductive.algebraicEquiv.injective
    apply Subtype.ext
    funext g
    have hs : (F' (J (D.incl (a ⊗ₜ[ℂ] r)))).val g =
        (F' (T.incl (p.val.inclusionCLM a ⊗ₜ[ℂ] r))).val g :=
      congrArg (fun z : T.Completed => (F' z).val g) (hJ a r)
    exact hs.trans ((hF' (p.val.inclusionCLM a) r g).trans (hF a r g).symm)
  exact DFunLike.congr_fun he

end
end Masullo
