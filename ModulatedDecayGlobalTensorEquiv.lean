import ModulatedDecayGlobalTensor
import ModulatedDecayProjectiveStageInclusion
import ModulatedDecayStageCoverage
import ModulatedDecayStageNaturality
import InjectiveTensorMaps

open Function Set Topology UniformSpace
open scoped TensorProduct

namespace Masullo

noncomputable section

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  (m : G →ₜ* Multiplicative ℝ) (τ : Multiplicative ℝ →ₜ* G) (hτ : RightInverse τ m)

local notation "K" => m.toMonoidHom.ker

variable [LocallyCompactSpace m.toMonoidHom.ker]

include hτ in
set_option maxHeartbeats 3200000 in
/-- Compatible fixed-stage product isomorphisms give the full inductive
tensor isomorphism by gluing their inverses. -/
theorem exists_splitGlobal_completedTensorEquiv_of_stages
    (hm : IsProperMap m) (I : Set ℝ) (hI : I.Nonempty) (hInt : OrdConnected I)
    (hLoc : ∀ (p : WholeBruhatStage K) (q : WholeBruhatStage G),
      q.val.1.kernel = p.val.1.kernel.map m.toMonoidHom.ker.subtype →
      ∃ L : (projectiveTensorModuleStructure p.val.Space (PositiveRealExponentialDecay I)).Completed
          ≃L[ℂ] WholeBruhatDecayStage m I q,
        ∀ (a : p.val.Space) (r : PositiveRealExponentialDecay I) (g : G),
          (L ((projectiveTensorModuleStructure p.val.Space (PositiveRealExponentialDecay I)).incl
            (a ⊗ₜ[ℂ] r))).val g =
            p.val.realize a (modulatedKernelProjection m τ hτ g) * r.val (m g).toAdd) :
    ∃ L : (inductiveTensorModuleStructure (BruhatSchwartz K) (PositiveRealExponentialDecay I)).Completed
        ≃L[ℂ] ModulatedExponentialInductive m I,
      ∀ (a : BruhatSchwartz K) (r : PositiveRealExponentialDecay I) (g : G),
        (L ((inductiveTensorModuleStructure (BruhatSchwartz K) (PositiveRealExponentialDecay I)).incl
          (a ⊗ₜ[ℂ] r))).val g =
          a.val (modulatedKernelProjection m τ hτ g) * r.val (m g).toAdd := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp
    (hm.isCompact_preimage (isCompact_singleton (x := (1 : Multiplicative ℝ))))
  obtain ⟨p, q, hp, hq, hCovA, hCovY, hker⟩ :=
    exists_cofinal_matchingStageSequences m hm τ hτ
  let A := BruhatSchwartz K
  let R := PositiveRealExponentialDecay I
  let X := A ⊗[ℂ] R
  let D := inductiveTensorModuleStructure A R
  let V := D.Completed
  let Y := ModulatedExponentialInductive m I
  let A₀ (n : ℕ) := (p n).val.Space
  let P (n : ℕ) := projectiveTensorModuleStructure (A₀ n) R
  let Y₀ (n : ℕ) := WholeBruhatDecayStage m I (q n)
  let α : G →ₜ* K := modulatedKernelProjection m τ hτ
  let hF₀ := exists_splitGlobal_completedTensorMap (G := G) (H := K) m hm hτ.surjective α I hI hInt
  let F : V →L[ℂ] Y := hF₀.choose
  have hF := hF₀.choose_spec
  have hE₀ (n : ℕ) : ∃ L : (P n).Completed ≃L[ℂ] Y₀ n,
      ∀ (a : A₀ n) (r : R) (g : G),
        (L ((P n).incl (a ⊗ₜ[ℂ] r))).val g = (p n).val.realize a (α g) * r.val (m g).toAdd :=
    hLoc (p n) (q n) (hker n)
  choose E hE using hE₀
  have hJ₀ (n : ℕ) : ∃ J : (P n).Completed →L[ℂ] V,
      ∀ (a : A₀ n) (r : R),
        J ((P n).incl (a ⊗ₜ[ℂ] r)) = D.incl ((p n).val.inclusionCLM a ⊗ₜ[ℂ] r) :=
    exists_projectiveStageTensor_to_global (p n) I hI hInt
  choose J hJ using hJ₀
  let B (n : ℕ) : Y₀ n →L[ℂ] V := (J n).comp (E n).symm.toContinuousLinearMap
  have hB (k n : ℕ) (hkn : k ≤ n) (x : Y₀ k) :
      B n (wholeBruhatDecayStageTransition m I (q k) (q n) (hq hkn) x) = B k x := by
    let j := (p k).val.transition (p n).val (hp hkn)
    let U : (P k).Completed →L[ℂ] (P n).Completed := completedProjectiveTensor_mapLeft j
    let T := wholeBruhatDecayStageTransition m I (q k) (q n) (hq hkn)
    have hEq : T.comp (E k).toContinuousLinearMap = (E n).toContinuousLinearMap.comp U :=
      splitStage_completedTensorMap_natural m α I hI (p k) (p n) (q k) (q n) (hp hkn) (hq hkn)
        (E k).toContinuousLinearMap (E n).toContinuousLinearMap (hE k) (hE n)
    have hJComm : (J n).comp U = J k :=
      projectiveStageTensor_to_global_refinement (p k) (p n) (hp hkn) I (J k) (J n) (hJ k) (hJ n)
    let z := (E k).symm x
    have hz : (E n) (U z) = T x :=
      (DFunLike.congr_fun hEq z).symm.trans (congrArg T ((E k).apply_symm_apply x))
    have hs : (E n).symm (T x) = U z := (E n).symm_apply_eq.mpr hz.symm
    exact (congrArg (J n) hs).trans (DFunLike.congr_fun hJComm z)
  letI : UniformSpace X := D.uniformSpace
  letI : IsUniformAddGroup X := D.uniformGroup
  letI : UniformContinuousConstSMul ℂ X := D.uniformConstSmul
  letI : PolynormableSpace ℂ X := inductiveTensor_withSeminorms.toPolynormableSpace
  letI : IsUniformAddGroup V := Completion.isUniformAddGroup
  letI : T0Space V := Completion.t0Space X
  letI : PolynormableSpace ℂ V := polynormableSpace_completion
  let hS₀ := exists_continuousLinearMap_of_cofinal_decayStages m I hm hτ.surjective hI q hq hCovY B hB
  let S : Y →L[ℂ] V := hS₀.choose
  have hS (n : ℕ) (x : Y₀ n) :
      S (ModulatedExponentialInductive.stageMap (q n) x) = B n x := hS₀.choose_spec n x
  have hMul (n : ℕ) (z : (P n).Completed) :
      F (J n z) = ModulatedExponentialInductive.stageMap (q n) (E n z) :=
    projectiveStageTensor_to_global_multiply m α (p n) (q n) I hI (J n)
      (E n).toContinuousLinearMap F (hJ n) (hE n) hF z
  have hr : F.comp S = ContinuousLinearMap.id ℂ Y := by
    apply continuousLinearMap_ext_on_cofinal_decayStages m I hm hτ.surjective hI q hq hCovY
    intro n x
    exact (congrArg F (hS n x)).trans ((hMul n ((E n).symm x)).trans
      (congrArg (ModulatedExponentialInductive.stageMap (q n)) ((E n).apply_symm_apply x)))
  have hl : S.comp F = ContinuousLinearMap.id ℂ V := by
    apply D.continuousLinearMap_ext_on_tmul
    intro a r
    obtain ⟨v, av, ha⟩ := a.property
    obtain ⟨n, hn⟩ := hCovA v
    let an := v.transition (p n).val hn av
    have han : (p n).val.inclusionCLM an = a :=
      (v.inclusion_transition (p n).val hn av).trans (Subtype.ext ha)
    let z := (P n).incl (an ⊗ₜ[ℂ] r)
    have hj : J n z = D.incl (a ⊗ₜ[ℂ] r) :=
      (hJ n an r).trans (congrArg (fun u : A => D.incl (u ⊗ₜ[ℂ] r)) han)
    change S (F (D.incl (a ⊗ₜ[ℂ] r))) = D.incl (a ⊗ₜ[ℂ] r)
    rw [← hj]
    exact (congrArg S (hMul n z)).trans ((hS n (E n z)).trans
      (congrArg (J n) ((E n).symm_apply_apply z)))
  exact ⟨ContinuousLinearEquiv.equivOfInverse F S (DFunLike.congr_fun hl)
    (DFunLike.congr_fun hr), hF⟩

end
end Masullo
