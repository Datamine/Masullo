import ModulatedDecaySplitTensor
import ModulatedDecayStructure
import CompletedInductiveTensorMaps

open Function Set Topology UniformSpace
open scoped TensorProduct

namespace Masullo

noncomputable section

variable {G H : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]
  [LocallyCompactSpace H] [CompactSpace H]

omit [SecondCountableTopology G] in
set_option maxHeartbeats 1200000 in
private theorem exists_splitProduct_on_inputStage
    (m : G →ₜ* Multiplicative ℝ) (hm : IsProperMap m) (hms : Surjective m) (α : G →ₜ* H)
    (I : Set ℝ) (hI : I.Nonempty) (hInt : OrdConnected I) (p : BruhatSchwartzStage H) :
    ∃ B : p.Space →ₗ[ℂ] PositiveRealExponentialDecay I →ₗ[ℂ] ModulatedExponentialInductive m I,
      (∀ a r g, (B a r).val g = (p.inclusion a).val (α g) * r.val (m g).toAdd) ∧
      (∀ a, Continuous (B a)) ∧ (∀ r, Continuous (B.flip r)) := by
  obtain ⟨P, hp⟩ := exists_wholeBruhatStage_refinement_of_compact p
  obtain ⟨q, hq⟩ := exists_wholeBruhatStage_kernel_le_comap m hm hms α P
  let A := P.val.Space
  let R := PositiveRealExponentialDecay I
  let Z := WholeBruhatDecayStage m I q
  have hStage : ∃ B : A →ₗ[ℂ] R →ₗ[ℂ] Z,
      (∀ a r g, (B a r).val g = P.val.realize a (α g) * r.val (m g).toAdd) ∧
      (∀ a, Continuous (B a)) ∧ (∀ r, Continuous (B.flip r)) :=
    exists_splitStageContinuousBilinear m hm α P q hq I hI hInt
  let L := hStage.choose
  have hL := hStage.choose_spec
  let j : p.Space →L[ℂ] A := p.transition P.val hp
  let k : Z →L[ℂ] ModulatedExponentialInductive m I :=
    ⟨ModulatedExponentialInductive.stageMap q, ModulatedExponentialInductive.stageMap_continuous q⟩
  let B := L.compl₁₂ j.toLinearMap (LinearMap.id : R →ₗ[ℂ] R)
  let B' := B.compr₂ k.toLinearMap
  refine ⟨B', fun a r g => ?_, fun a => ?_, fun r => ?_⟩
  · have hj : P.val.realize (j a) (α g) = (p.inclusion a).val (α g) :=
      congrArg (fun f : BruhatSchwartz H => f.val (α g)) (p.inclusion_transition P.val hp a)
    change (L (j a) r).val g = _
    exact (hL.1 (j a) r g).trans (congrArg (fun z : ℂ => z * r.val (m g).toAdd) hj)
  · exact k.continuous.comp (hL.2.1 (j a))
  · exact k.continuous.comp ((hL.2.2 r).comp j.continuous)

omit [SecondCountableTopology G] in
set_option maxHeartbeats 1000000 in
/-- Multiplication of a Schwartz--Bruhat angular test and a radial decay test
is separately continuous into the full inductive decay space. -/
theorem exists_splitGlobalProductBilinear
    (m : G →ₜ* Multiplicative ℝ) (hm : IsProperMap m) (hms : Surjective m) (α : G →ₜ* H)
    (I : Set ℝ) (hI : I.Nonempty) (hInt : OrdConnected I) :
    ∃ B : BruhatSchwartz H →ₗ[ℂ] PositiveRealExponentialDecay I →ₗ[ℂ]
        ModulatedExponentialInductive m I,
      (∀ a r g, (B a r).val g = a.val (α g) * r.val (m g).toAdd) ∧
      (∀ a, Continuous (B a)) ∧ (∀ r, Continuous (B.flip r)) := by
  let A := BruhatSchwartz H
  let R := PositiveRealExponentialDecay I
  let Y := ModulatedExponentialInductive m I
  let av : A →ₗ[ℂ] (G → ℂ) :=
    { toFun := fun a g => a.val (α g), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  let rv : R →ₗ[ℂ] (G → ℂ) :=
    { toFun := fun r g => r.val (m g).toAdd, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  let T : A ⊗[ℂ] R →ₗ[ℂ] (G → ℂ) :=
    TensorProduct.lift ((LinearMap.mul ℂ (G → ℂ)).compl₁₂ av rv)
  have hT (a : A) (r : R) (g : G) : T (a ⊗ₜ[ℂ] r) g = a.val (α g) * r.val (m g).toAdd :=
    congrFun (TensorProduct.lift.tmul (f' := (LinearMap.mul ℂ (G → ℂ)).compl₁₂ av rv) a r) g
  have hmT (w : A ⊗[ℂ] R) : T w ∈ modulatedExponentialDecaySubmodule m I := by
    induction w using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | tmul a r =>
      obtain ⟨p, u, hu⟩ := a.property
      have ha : p.inclusion u = a := Subtype.ext hu
      obtain ⟨L, hL, _, _⟩ := exists_splitProduct_on_inputStage m hm hms α I hI hInt p
      have he : T (a ⊗ₜ[ℂ] r) = (L u r).val :=
        funext fun g => (hT a r g).trans ((congrArg (fun a : A =>
          a.val (α g) * r.val (m g).toAdd) ha).symm.trans (hL u r g).symm)
      exact he.symm ▸ (ModulatedExponentialInductive.algebraicEquiv (L u r)).property
  let U : A ⊗[ℂ] R →ₗ[ℂ] Y :=
    ModulatedExponentialInductive.algebraicEquiv.symm.toLinearMap.comp (T.codRestrict _ hmT)
  let B := TensorProduct.curry U
  have hB (a : A) (r : R) (g : G) : (B a r).val g = a.val (α g) * r.val (m g).toAdd := hT a r g
  have hv : Injective (ModulatedExponentialInductive.val (m := m) (I := I)) :=
    fun _ _ he => ModulatedExponentialInductive.algebraicEquiv.injective (Subtype.ext he)
  have hLocal (p : BruhatSchwartzStage H) :
      ∃ L : p.Space →ₗ[ℂ] R →ₗ[ℂ] Y,
        (∀ u r, L u r = B (p.inclusion u) r) ∧
        (∀ u, Continuous (L u)) ∧ (∀ r, Continuous (L.flip r)) := by
    obtain ⟨L, hL, ha, hr⟩ := exists_splitProduct_on_inputStage m hm hms α I hI hInt p
    exact ⟨L, fun u r => hv (funext fun g => (hL u r g).trans (hB (p.inclusion u) r g).symm), ha, hr⟩
  refine ⟨B, hB, fun a => ?_, fun r => ?_⟩
  · obtain ⟨p, u, hu⟩ := a.property
    have ha : p.inclusion u = a := Subtype.ext hu
    obtain ⟨L, he, hL, _⟩ := hLocal p
    exact (hL u).congr fun r => (he u r).trans (congrArg (fun a : A => B a r) ha)
  · apply (locallyConvexFinal_continuous_iff
      (fun p : BruhatSchwartzStage H => p.inclusion) (B.flip r)).mpr
    intro p
    obtain ⟨L, he, _, hL⟩ := hLocal p
    exact (hL r).congr fun u => he u r

set_option maxHeartbeats 1200000 in
/-- The product of a full angular Schwartz--Bruhat test and a radial decay
test extends to the completed inductive tensor product. -/
theorem exists_splitGlobal_completedTensorMap
    (m : G →ₜ* Multiplicative ℝ) (hm : IsProperMap m) (hms : Surjective m) (α : G →ₜ* H)
    (I : Set ℝ) (hI : I.Nonempty) (hInt : OrdConnected I) :
    ∃ F : (inductiveTensorModuleStructure (BruhatSchwartz H) (PositiveRealExponentialDecay I)).Completed
        →L[ℂ] ModulatedExponentialInductive m I,
      ∀ (a : BruhatSchwartz H) (r : PositiveRealExponentialDecay I) (g : G),
        (F ((inductiveTensorModuleStructure (BruhatSchwartz H) (PositiveRealExponentialDecay I)).incl
          (a ⊗ₜ[ℂ] r))).val g = a.val (α g) * r.val (m g).toAdd := by
  let A := BruhatSchwartz H
  let R := PositiveRealExponentialDecay I
  let Y := ModulatedExponentialInductive m I
  let D := inductiveTensorModuleStructure A R
  let hProduct := exists_splitGlobalProductBilinear m hm hms α I hI hInt
  let B := hProduct.choose
  have hB := hProduct.choose_spec
  letI : IsTopologicalAddGroup A := (PolynormableSpace.withSeminorms ℂ A).topologicalAddGroup
  letI : IsTopologicalAddGroup R := (PolynormableSpace.withSeminorms ℂ R).topologicalAddGroup
  letI : UniformSpace Y := modulatedDecayUniformSpace m I
  letI : IsUniformAddGroup Y := isUniformAddGroup_of_addCommGroup
  letI : T2Space Y := ModulatedExponentialInductive.t2 m I hI
  letI : CompleteSpace Y := (modulatedDecay_complete_nuclear_montel m I hm hms hI).1
  letI : ContinuousSMul ℂ Y := (PolynormableSpace.withSeminorms ℂ Y).continuousSMul
  letI : TopologicalSpace (A ⊗[ℂ] R) := D.topology
  let T : (A ⊗[ℂ] R) →L[ℂ] Y :=
    ⟨TensorProduct.lift B, (continuous_inductiveTensor_lift_iff B).mpr ⟨hB.2.2, hB.2.1⟩⟩
  let hLift := D.exists_continuousLinearMap_extend T
  refine ⟨hLift.choose, fun a r g => ?_⟩
  have he : hLift.choose (D.incl (a ⊗ₜ[ℂ] r)) = B a r :=
    (hLift.choose_spec (a ⊗ₜ[ℂ] r)).trans (TensorProduct.lift.tmul (f' := B) a r)
  exact (congrArg (fun y : Y => y.val g) he).trans (hB.1 a r g)

omit [SecondCountableTopology G] [CompactSpace H] in
set_option maxHeartbeats 600000 in
/-- The full forward multiplication map intertwines translations on the
completed angular--radial tensor product and on the decay space. -/
theorem splitGlobal_completedTensorMap_translate
    (m : G →ₜ* Multiplicative ℝ) (hm : IsProperMap m) (hms : Surjective m)
    (α : G →ₜ* H) (I : Set ℝ) (hI : I.Nonempty) (g : G)
    (F : (inductiveTensorModuleStructure (BruhatSchwartz H) (PositiveRealExponentialDecay I)).Completed
        →L[ℂ] ModulatedExponentialInductive m I)
    (hF : ∀ (a : BruhatSchwartz H) (r : PositiveRealExponentialDecay I) (x : G),
      (F ((inductiveTensorModuleStructure (BruhatSchwartz H) (PositiveRealExponentialDecay I)).incl
        (a ⊗ₜ[ℂ] r))).val x = a.val (α x) * r.val (m x).toAdd) :
    let A := BruhatSchwartz H
    let R := PositiveRealExponentialDecay I
    letI : IsTopologicalAddGroup A := (PolynormableSpace.withSeminorms ℂ A).topologicalAddGroup
    letI : IsTopologicalAddGroup R := (PolynormableSpace.withSeminorms ℂ R).topologicalAddGroup
    ∀ z, F (completedInductiveTensor_map (bruhatSchwartz_translate (α g))
        (logExponentialDecayTranslation I hI (-(m g).toAdd)) z) =
      ModulatedExponentialInductive.translate m I g (F z) := by
  dsimp only
  let A := BruhatSchwartz H
  let R := PositiveRealExponentialDecay I
  let Y := ModulatedExponentialInductive m I
  letI : IsTopologicalAddGroup A := (PolynormableSpace.withSeminorms ℂ A).topologicalAddGroup
  letI : IsTopologicalAddGroup R := (PolynormableSpace.withSeminorms ℂ R).topologicalAddGroup
  letI : T2Space Y := ModulatedExponentialInductive.t2 m I hI
  let D := inductiveTensorModuleStructure A R
  let j := bruhatSchwartz_translate (α g)
  let k := logExponentialDecayTranslation I hI (-(m g).toAdd)
  let U : Y →L[ℂ] Y := ⟨ModulatedExponentialInductive.translate m I g,
    (ModulatedExponentialInductive.continuous_translate m I hm hms hI).comp
      (continuous_const.prodMk continuous_id)⟩
  have hEq : F.comp (completedInductiveTensor_map j k) = U.comp F := by
    apply D.continuousLinearMap_ext_on_tmul
    intro a r
    apply ModulatedExponentialInductive.algebraicEquiv.injective
    apply Subtype.ext
    funext x
    change (F (completedInductiveTensor_map j k (D.incl (a ⊗ₜ[ℂ] r)))).val x =
      (U (F (D.incl (a ⊗ₜ[ℂ] r)))).val x
    rw [completedInductiveTensor_map_tmul]
    change (F (D.incl (j a ⊗ₜ[ℂ] k r))).val x = (F (D.incl (a ⊗ₜ[ℂ] r))).val (g⁻¹ * x)
    rw [hF, hF]
    change (bruhatSchwartz_translate (α g) a).val (α x) *
      (logExponentialDecayTranslation I hI (-(m g).toAdd) r).val (m x).toAdd =
      a.val (α (g⁻¹ * x)) * r.val (m (g⁻¹ * x)).toAdd
    rw [bruhatSchwartz_translate_apply, logExponentialDecayTranslation_apply,
      map_mul α, map_inv α, map_mul m, map_inv m]
    exact congrArg (fun y : ℝ => a.val ((α g)⁻¹ * α x) * r.val y) (add_comm _ _)
  exact DFunLike.congr_fun hEq

omit [SecondCountableTopology G] [CompactSpace H] in
set_option maxHeartbeats 700000 in
/-- The fixed-stage and full-space forward maps commute with the canonical
inclusions for the completed inductive tensor topology. -/
theorem splitStage_completedInductiveTensor_to_global
    (m : G →ₜ* Multiplicative ℝ) (α : G →ₜ* H)
    (I : Set ℝ) (hI : I.Nonempty) (p : WholeBruhatStage H) (q : WholeBruhatStage G)
    (F : (inductiveTensorModuleStructure p.val.Space (PositiveRealExponentialDecay I)).Completed
      →L[ℂ] WholeBruhatDecayStage m I q)
    (F' : (inductiveTensorModuleStructure (BruhatSchwartz H) (PositiveRealExponentialDecay I)).Completed
      →L[ℂ] ModulatedExponentialInductive m I)
    (hF : ∀ (a : p.val.Space) (r : PositiveRealExponentialDecay I) (g : G),
      (F ((inductiveTensorModuleStructure p.val.Space (PositiveRealExponentialDecay I)).incl
        (a ⊗ₜ[ℂ] r))).val g = p.val.realize a (α g) * r.val (m g).toAdd)
    (hF' : ∀ (a : BruhatSchwartz H) (r : PositiveRealExponentialDecay I) (g : G),
      (F' ((inductiveTensorModuleStructure (BruhatSchwartz H) (PositiveRealExponentialDecay I)).incl
        (a ⊗ₜ[ℂ] r))).val g = a.val (α g) * r.val (m g).toAdd) :
    let A := p.val.Space
    let B := BruhatSchwartz H
    let R := PositiveRealExponentialDecay I
    letI : IsTopologicalAddGroup A := (PolynormableSpace.withSeminorms ℂ A).topologicalAddGroup
    letI : IsTopologicalAddGroup B := (PolynormableSpace.withSeminorms ℂ B).topologicalAddGroup
    letI : IsTopologicalAddGroup R := (PolynormableSpace.withSeminorms ℂ R).topologicalAddGroup
    ∀ z, ModulatedExponentialInductive.stageMap q (F z) =
      F' (completedInductiveTensor_map p.val.inclusionCLM (ContinuousLinearMap.id ℂ R) z) := by
  dsimp only
  let A := p.val.Space
  let B := BruhatSchwartz H
  let R := PositiveRealExponentialDecay I
  let Y := ModulatedExponentialInductive m I
  letI : IsTopologicalAddGroup A := (PolynormableSpace.withSeminorms ℂ A).topologicalAddGroup
  letI : IsTopologicalAddGroup B := (PolynormableSpace.withSeminorms ℂ B).topologicalAddGroup
  letI : IsTopologicalAddGroup R := (PolynormableSpace.withSeminorms ℂ R).topologicalAddGroup
  letI : T2Space Y := ModulatedExponentialInductive.t2 m I hI
  let D := inductiveTensorModuleStructure A R
  let P := inductiveTensorModuleStructure B R
  let j : A →L[ℂ] B := p.val.inclusionCLM
  let k : WholeBruhatDecayStage m I q →L[ℂ] Y :=
    ⟨ModulatedExponentialInductive.stageMap q, ModulatedExponentialInductive.stageMap_continuous q⟩
  have hComm : k.comp F = F'.comp (completedInductiveTensor_map j (ContinuousLinearMap.id ℂ R)) := by
    apply D.continuousLinearMap_ext_on_tmul
    intro a r
    apply ModulatedExponentialInductive.algebraicEquiv.injective
    apply Subtype.ext
    funext g
    change (k (F (D.incl (a ⊗ₜ[ℂ] r)))).val g =
      (F' (completedInductiveTensor_map j (ContinuousLinearMap.id ℂ R) (D.incl (a ⊗ₜ[ℂ] r)))).val g
    have hmap : completedInductiveTensor_map j (ContinuousLinearMap.id ℂ R) (D.incl (a ⊗ₜ[ℂ] r)) =
        P.incl (j a ⊗ₜ[ℂ] r) :=
      @completedInductiveTensor_map_tmul A B R R _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        j (ContinuousLinearMap.id ℂ R) a r
    have hval : (F (D.incl (a ⊗ₜ[ℂ] r))).val g = (F' (P.incl (j a ⊗ₜ[ℂ] r))).val g :=
      (hF a r g).trans (hF' (j a) r g).symm
    exact hval.trans ((congrArg (fun w : P.Completed => (F' w).val g) hmap).symm)
  exact DFunLike.congr_fun hComm

end
end Masullo
