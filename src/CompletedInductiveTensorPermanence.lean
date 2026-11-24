/-
The closed-ball argument adapts RiemannMasullo's AppC_LCTVS/Sec2a_part2.lean
at a0dc549ec3ffa52882b705f89d500e7ab8fe5074 (Apache-2.0).
See External/PROVENANCE.md and External/RiemannMasullo.LICENSE.
-/
import CompletedInductiveTensorMaps
import Mathlib.Analysis.LocallyConvex.Barrelled

open Bornology Filter Set Topology UniformSpace
open scoped TensorProduct

namespace Masullo

noncomputable section

section Barrelled

variable {E F : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
  [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]

/-- The completed inductive tensor product of two barrelled complex spaces is
barrelled, as in Proposition C.2.3.13(3). -/
theorem completedInductiveTensor_barrelled [IsTopologicalAddGroup E] [IsTopologicalAddGroup F]
    [BarrelledSpace ℂ E] [BarrelledSpace ℂ F] :
    BarrelledSpace ℂ (inductiveTensorModuleStructure E F).Completed := by
  let X := E ⊗[ℂ] F
  let D := inductiveTensorModuleStructure E F
  letI : UniformSpace X := D.uniformSpace
  letI : IsUniformAddGroup X := D.uniformGroup
  letI : UniformContinuousConstSMul ℂ X := D.uniformConstSmul
  letI : IsUniformAddGroup D.Completed := Completion.isUniformAddGroup
  letI : ContinuousConstSMul ℂ D.Completed :=
    ⟨fun c => (Completion.uniformContinuous_map (f := fun z : X => c • z)).continuous⟩
  let W : WithSeminorms (InductiveTensorTest.tensor (E := E) (F := F)) :=
    inductiveTensor_withSeminorms
  let j : X →L[ℂ] D.Completed :=
    { toFun := D.incl
      map_add' := fun x y => Completion.coe_add x y
      map_smul' := fun c x => Completion.coe_smul c x
      cont := Completion.continuous_coe X }
  constructor
  intro p hp
  let q := p.comp j.toLinearMap
  have hq : Continuous q := by
    let test : InductiveTensorTest E F :=
      { tensor := q
        first := fun y => by
          let L := (TensorProduct.mk ℂ E F).flip y
          have hL : Continuous L :=
            (W.continuous_iff_continuous_comp L).mpr fun t => t.first y
          exact (q.comp L).continuous_of_lowerSemicontinuous (hp.comp (j.continuous.comp hL))
        second := fun x => by
          let L := TensorProduct.mk ℂ E F x
          have hL : Continuous L :=
            (W.continuous_iff_continuous_comp L).mpr fun t => t.second x
          exact (q.comp L).continuous_of_lowerSemicontinuous (hp.comp (j.continuous.comp hL)) }
    exact W.continuous_seminorm test
  have hball : q.closedBall 0 1 ∈ 𝓝 (0 : X) := by
    rw [q.closedBall_zero_eq]
    exact hq.continuousAt.preimage_mem_nhds (Iic_mem_nhds (by simp))
  have hcl := Completion.isDenseInducing_coe.closure_image_mem_nhds hball
  apply p.continuous' (r := 1)
  rw [Completion.coe_zero] at hcl
  refine mem_of_superset hcl (closure_minimal ?_ ?_)
  · rintro _ ⟨x, hx, rfl⟩
    rw [Seminorm.mem_closedBall_zero] at hx ⊢
    exact hx
  · rw [Seminorm.closedBall_zero_eq]
    exact hp.isClosed_preimage 1


end Barrelled

section StageImages

variable {I J E F : Type*} {A : I → Type*} {B : J → Type*}
  [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [∀ i, AddCommGroup (A i)] [∀ i, Module ℂ (A i)] [∀ i, TopologicalSpace (A i)]
  [∀ i, IsTopologicalAddGroup (A i)]
  [∀ j, AddCommGroup (B j)] [∀ j, Module ℂ (B j)] [∀ j, TopologicalSpace (B j)]
  [∀ j, IsTopologicalAddGroup (B j)]

/-- The actual images of the completed tensor stages span a dense subspace
when the stages cover both factors, as in the repair of (C.2.3.27). -/
theorem completedInductiveTensor_stageSpan_dense
    (u : ∀ i, A i →L[ℂ] E) (v : ∀ j, B j →L[ℂ] F)
    (hu : ∀ x : E, ∃ i, x ∈ range (u i)) (hv : ∀ y : F, ∃ j, y ∈ range (v j)) :
    Dense (Submodule.span ℂ
      (⋃ i, ⋃ j, range (completedInductiveTensor_map (u i) (v j))) :
      Set (inductiveTensorModuleStructure E F).Completed) := by
  let X := E ⊗[ℂ] F
  let D := inductiveTensorModuleStructure E F
  letI : UniformSpace X := D.uniformSpace
  letI : IsUniformAddGroup X := D.uniformGroup
  let S := Submodule.span ℂ (⋃ i, ⋃ j, range (completedInductiveTensor_map (u i) (v j)))
  change Dense (S : Set D.Completed)
  apply ((Completion.denseRange_coe (α := X)) : DenseRange D.incl).mono
  rintro _ ⟨z, rfl⟩
  change D.incl z ∈ S
  induction z using TensorProduct.induction_on with
  | zero =>
    rw [show D.incl 0 = 0 from Completion.coe_zero]
    exact S.zero_mem
  | tmul x y =>
    obtain ⟨i, a, rfl⟩ := hu x
    obtain ⟨j, b, rfl⟩ := hv y
    apply Submodule.subset_span
    refine mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨j, ?_⟩⟩
    exact ⟨(inductiveTensorModuleStructure (A i) (B j)).incl (a ⊗ₜ[ℂ] b),
      completedInductiveTensor_map_tmul (u i) (v j) a b⟩
  | add x y hx hy =>
    rw [show D.incl (x + y) = D.incl x + D.incl y from Completion.coe_add x y]
    exact S.add_mem hx hy


end StageImages


section ScalarUnit

variable (E : Type*) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] [PolynormableSpace ℂ E]

/-- The scalar factor is a right unit for the inductive tensor topology. -/
def inductiveTensorScalarRightUnit :
    letI : TopologicalSpace (E ⊗[ℂ] ℂ) := inductiveTensorTopology E ℂ
    (E ⊗[ℂ] ℂ) ≃L[ℂ] E := by
  letI : TopologicalSpace (E ⊗[ℂ] ℂ) := inductiveTensorTopology E ℂ
  let W := inductiveTensor_withSeminorms (E := E) (F := ℂ)
  let e := TensorProduct.rid ℂ E
  let L := TensorProduct.curry e.toLinearMap
  have h (x : E) (c : ℂ) : L x c = c • x := TensorProduct.rid_tmul x c
  refine ⟨e, ?_, ?_⟩
  · change Continuous (TensorProduct.lift L)
    apply (continuous_inductiveTensor_lift_iff L).mpr
    refine ⟨fun c => ?_, fun x => ?_⟩
    · rw [show (fun x : E => L x c) = fun x => c • x from funext (fun x => h x c)]
      exact continuous_id.const_smul c
    · rw [show (L x : ℂ → E) = fun c => c • x from funext (h x)]
      exact continuous_id.smul (continuous_const (y := x))
  · change Continuous ((TensorProduct.mk ℂ E ℂ).flip 1)
    exact (W.continuous_iff_continuous_comp ((TensorProduct.mk ℂ E ℂ).flip 1)).mpr
      fun q => q.first 1

end ScalarUnit

section CompletedScalarUnit

variable (E : Type*) [AddCommGroup E] [Module ℂ E] [UniformSpace E]
  [IsUniformAddGroup E] [ContinuousSMul ℂ E] [PolynormableSpace ℂ E]

/-- Completing the scalar right unit identifies the completed inductive tensor
with the ordinary separated completion of the factor. -/
noncomputable def completedInductiveTensorScalarRightUnit :
    (inductiveTensorModuleStructure E ℂ).Completed ≃ᵤ Completion E := by
  let X := E ⊗[ℂ] ℂ
  let D := inductiveTensorModuleStructure E ℂ
  letI : UniformSpace X := D.uniformSpace
  letI : IsUniformAddGroup X := D.uniformGroup
  let e := inductiveTensorScalarRightUnit E
  let u : X ≃ᵤ E :=
    { toEquiv := e.toEquiv
      uniformContinuous_toFun := e.toContinuousLinearMap.uniformContinuous
      uniformContinuous_invFun := e.symm.toContinuousLinearMap.uniformContinuous }
  exact Completion.mapEquiv u

@[simp]
theorem completedInductiveTensorScalarRightUnit_incl (z : E ⊗[ℂ] ℂ) :
    completedInductiveTensorScalarRightUnit E ((inductiveTensorModuleStructure E ℂ).incl z) =
      ((TensorProduct.rid ℂ E z : E) : Completion E) := by
  letI : UniformSpace (E ⊗[ℂ] ℂ) := (inductiveTensorModuleStructure E ℂ).uniformSpace
  unfold completedInductiveTensorScalarRightUnit
  exact Completion.mapEquiv_coe _ z

end CompletedScalarUnit

section Bornological

/-- A locally convex complex space is bornological when every seminorm
bounded on von Neumann bounded sets is continuous. -/
def IsBornologicalTVS (E : Type*) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] : Prop :=
  ∀ p : Seminorm ℂ E, (∀ S : Set E, IsVonNBounded ℂ S → BddAbove (p '' S)) → Continuous p

variable {E F : Type*}
  [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] [IsTopologicalAddGroup F]

/-- Bornologicity holds for the algebraic tensor with the inductive tensor topology. -/
theorem inductiveTensor_isBornological (hE : IsBornologicalTVS E) (hF : IsBornologicalTVS F) :
    @IsBornologicalTVS (E ⊗[ℂ] F) _ _ (inductiveTensorTopology E F) := by
  letI : TopologicalSpace (E ⊗[ℂ] F) := inductiveTensorTopology E F
  let W := inductiveTensor_withSeminorms (E := E) (F := F)
  intro p hp
  let test : InductiveTensorTest E F :=
    { tensor := p
      first := fun y => by
        let L := (TensorProduct.mk ℂ E F).flip y
        have hL : Continuous L := (W.continuous_iff_continuous_comp L).mpr fun q => q.first y
        let T : E →L[ℂ] (E ⊗[ℂ] F) := ⟨L, hL⟩
        apply hE (p.comp L)
        intro S hS
        have hb := hp (T '' S) (hS.image T)
        rw [Set.image_image] at hb
        exact hb
      second := fun x => by
        let L := TensorProduct.mk ℂ E F x
        have hL : Continuous L := (W.continuous_iff_continuous_comp L).mpr fun q => q.second x
        let T : F →L[ℂ] (E ⊗[ℂ] F) := ⟨L, hL⟩
        apply hF (p.comp L)
        intro S hS
        have hb := hp (T '' S) (hS.image T)
        rw [Set.image_image] at hb
        exact hb }
  exact W.continuous_seminorm test

end Bornological

end
end Masullo
