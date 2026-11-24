import LocalBanachSpaces
import LocallyConvexApproximation
import ProjectiveTensorTopology
import TopologicalModuleCompletion

open Filter Function Set Topology UniformSpace
open scoped NNReal TensorProduct

namespace Masullo

noncomputable section

variable {E F : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
variable [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]

/-- Seminorm tests for the inductive tensor product. They make the elementary
tensor map separately continuous. -/
structure InductiveTensorTest (E F : Type*) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] where
  tensor : Seminorm ℂ (E ⊗[ℂ] F)
  first (y : F) : Continuous (fun x : E => tensor (x ⊗ₜ[ℂ] y))
  second (x : E) : Continuous (fun y : F => tensor (x ⊗ₜ[ℂ] y))

abbrev inductiveTensorTopology (E F : Type*) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] : TopologicalSpace (E ⊗[ℂ] F) :=
  (SeminormFamily.moduleFilterBasis (InductiveTensorTest.tensor (E := E) (F := F))).topology

theorem inductiveTensor_withSeminorms :
    letI : TopologicalSpace (E ⊗[ℂ] F) := inductiveTensorTopology E F
    WithSeminorms (InductiveTensorTest.tensor (E := E) (F := F)) := by
  letI : TopologicalSpace (E ⊗[ℂ] F) := inductiveTensorTopology E F
  exact ⟨rfl⟩

def inductiveTensorModuleStructure (E F : Type*) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] : TopologicalModuleStructure (E ⊗[ℂ] F) := by
  letI : TopologicalSpace (E ⊗[ℂ] F) := inductiveTensorTopology E F
  let h := inductiveTensor_withSeminorms (E := E) (F := F)
  letI : ContinuousSMul ℂ (E ⊗[ℂ] F) := h.continuousSMul
  exact ⟨inductiveTensorTopology E F, h.topologicalAddGroup, inferInstance⟩

def projectiveTensorModuleStructure (E F : Type*) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] : TopologicalModuleStructure (E ⊗[ℂ] F) := by
  letI : TopologicalSpace (E ⊗[ℂ] F) := projectiveTensorTopology E F
  let h := projectiveTensor_withSeminorms (E := E) (F := F)
  letI : ContinuousSMul ℂ (E ⊗[ℂ] F) := h.continuousSMul
  exact ⟨projectiveTensorTopology E F, h.topologicalAddGroup, inferInstance⟩

def ProjectiveTensorTest.toInductive [IsTopologicalAddGroup E] [IsTopologicalAddGroup F]
    (P : ProjectiveTensorTest E F) : InductiveTensorTest E F where
  tensor := P.tensor
  first y := by
    let L : E →ₗ[ℂ] E ⊗[ℂ] F := (TensorProduct.mk ℂ E F).flip y
    let a : NNReal := ⟨P.second y, apply_nonneg _ _⟩
    let q : Seminorm ℂ E := a • P.first
    have hq : Continuous q := continuous_const.mul P.first_continuous
    exact Seminorm.continuous_of_le (q := q) hq
      (show P.tensor.comp L ≤ q from fun x => by
        change P.tensor (x ⊗ₜ[ℂ] y) ≤ P.second y * P.first x
        rw [mul_comm]
        exact P.bound x y)
  second x := by
    let L : F →ₗ[ℂ] E ⊗[ℂ] F := TensorProduct.mk ℂ E F x
    let a : NNReal := ⟨P.first x, apply_nonneg _ _⟩
    let q : Seminorm ℂ F := a • P.second
    have hq : Continuous q := continuous_const.mul P.second_continuous
    exact Seminorm.continuous_of_le (q := q) hq
      (show P.tensor.comp L ≤ q from fun y => P.bound x y)

/-- The identity from the inductive tensor topology to the projective
tensor topology is continuous. -/
theorem inductive_to_projective_continuous [IsTopologicalAddGroup E] [IsTopologicalAddGroup F] :
    Continuous[inductiveTensorTopology E F, projectiveTensorTopology E F]
      (id : E ⊗[ℂ] F → E ⊗[ℂ] F) := by
  let X := E ⊗[ℂ] F
  letI : TopologicalSpace X := inductiveTensorTopology E F
  have hI := inductiveTensor_withSeminorms (E := E) (F := F)
  have hP := projectiveTensor_withSeminorms (E := E) (F := F)
  exact (@WithSeminorms.continuous_iff_continuous_comp ℂ ℂ X X
    _ _ _ _ _ _ _ (RingHom.id ℂ) _ _ (inductiveTensorTopology E F) hI.topologicalAddGroup
    (projectiveTensorTopology E F) hP LinearMap.id).mpr
      (fun P => hI.continuous_seminorm P.toInductive)

section CompletedComparison

variable [IsTopologicalAddGroup E] [IsTopologicalAddGroup F]

private def inductiveToProjectiveMap :
    @ContinuousLinearMap ℂ ℂ _ _ (RingHom.id ℂ)
      (E ⊗[ℂ] F) (inductiveTensorTopology E F) _
      (E ⊗[ℂ] F) (projectiveTensorTopology E F) _ _ _ :=
  @ContinuousLinearMap.mk ℂ ℂ _ _ (RingHom.id ℂ)
    (E ⊗[ℂ] F) (inductiveTensorTopology E F) _
    (E ⊗[ℂ] F) (projectiveTensorTopology E F) _ _ _
    LinearMap.id inductive_to_projective_continuous

/-- The canonical continuous map between the inductive and projective
tensor completions extends the algebraic identity. -/
def completedInductiveTensorComparison :
    (inductiveTensorModuleStructure E F).Completed →L[ℂ]
      (projectiveTensorModuleStructure E F).Completed := by
  let D := inductiveTensorModuleStructure E F
  let P := projectiveTensorModuleStructure E F
  exact @ContinuousLinearMap.completion (E ⊗[ℂ] F) (E ⊗[ℂ] F) ℂ ℂ
    D.uniformSpace _ D.uniformGroup _ _ D.uniformConstSmul _ P.uniformSpace _ P.uniformGroup
    _ P.uniformConstSmul _ (inductiveToProjectiveMap (E := E) (F := F))

@[simp]
theorem completedInductiveTensorComparison_incl (z : E ⊗[ℂ] F) :
    completedInductiveTensorComparison ((inductiveTensorModuleStructure E F).incl z) =
      (projectiveTensorModuleStructure E F).incl z := by
  let D := inductiveTensorModuleStructure E F
  let P := projectiveTensorModuleStructure E F
  exact @ContinuousLinearMap.completion_apply_coe (E ⊗[ℂ] F) (E ⊗[ℂ] F) ℂ ℂ
    D.uniformSpace _ D.uniformGroup _ _ D.uniformConstSmul _ P.uniformSpace _ P.uniformGroup
    _ P.uniformConstSmul _ (inductiveToProjectiveMap (E := E) (F := F)) z

end CompletedComparison

private theorem continuous_linear_of_continuous_norm {V H : Type*}
    [AddCommGroup V] [Module ℂ V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [NormedAddCommGroup H] [NormedSpace ℂ H] (L : V →ₗ[ℂ] H)
    (h : Continuous (fun v => ‖L v‖)) : Continuous L := by
  refine continuous_of_tendsto_nhds_zero (G := V) (M := H) L.toAddMonoidHom ?_
  rw [Metric.tendsto_nhds]
  intro ε hε
  have ht := (h.tendsto' 0 0 (by simp)).eventually (Iio_mem_nhds hε)
  filter_upwards [ht] with x hx
  exact (by simpa only [dist_zero_right] using hx : dist (L x) 0 < ε)

/-- The inductive tensor topology represents separately continuous bilinear maps. -/
theorem continuous_inductiveTensor_lift_iff [IsTopologicalAddGroup E] [IsTopologicalAddGroup F]
    {G : Type*} [AddCommGroup G] [Module ℂ G] [TopologicalSpace G] [PolynormableSpace ℂ G]
    (f : E →ₗ[ℂ] F →ₗ[ℂ] G) :
    Continuous[inductiveTensorTopology E F, inferInstance] (TensorProduct.lift f) ↔
      (∀ y, Continuous fun x => f x y) ∧ (∀ x, Continuous (f x)) := by
  letI : TopologicalSpace (E ⊗[ℂ] F) := inductiveTensorTopology E F
  let W := inductiveTensor_withSeminorms (E := E) (F := F)
  letI : IsTopologicalAddGroup (E ⊗[ℂ] F) := W.topologicalAddGroup
  constructor
  · intro h
    constructor
    · intro y
      let L : E →ₗ[ℂ] E ⊗[ℂ] F := (TensorProduct.mk ℂ E F).flip y
      have hL := (W.continuous_iff_continuous_comp L).mpr fun I => I.first y
      have he : ((TensorProduct.lift f : E ⊗[ℂ] F → G) ∘ L) = fun x => f x y :=
        funext fun x => TensorProduct.lift.tmul (f' := f) x y
      rw [← he]
      exact h.comp hL
    · intro x
      let L : F →ₗ[ℂ] E ⊗[ℂ] F := TensorProduct.mk ℂ E F x
      have hL := (W.continuous_iff_continuous_comp L).mpr fun I => I.second x
      have he : ((TensorProduct.lift f : E ⊗[ℂ] F → G) ∘ L) = f x :=
        funext fun y => TensorProduct.lift.tmul (f' := f) x y
      rw [← he]
      exact h.comp hL
  · rintro ⟨hE, hF⟩
    let WG := PolynormableSpace.withSeminorms ℂ G
    apply (WG.continuous_iff_continuous_comp (TensorProduct.lift f)).mpr
    rintro ⟨q, hq⟩
    let I : InductiveTensorTest E F :=
      ⟨q.comp (TensorProduct.lift f), fun y => hq.comp (hE y), fun x => hq.comp (hF x)⟩
    exact W.continuous_seminorm I

end

section FrechetTensor

noncomputable section

variable {E F : Type*} [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E]
variable [ContinuousSMul ℂ E] [PolynormableSpace ℂ E] [FirstCountableTopology E] [BaireSpace E]
variable [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
variable [PolynormableSpace ℂ F] [FirstCountableTopology F]

private def InductiveTensorTest.toProjective (I : InductiveTensorTest E F) : ProjectiveTensorTest E F := by
  let L := localBanachDenseMap I.tensor
  let B := TensorProduct.curry L
  have hx (y : F) : Continuous fun x => B x y := by
    apply continuous_linear_of_continuous_norm ((LinearMap.applyₗ' ℂ y).comp B)
    have he : (fun x => ‖B x y‖) = (fun x => I.tensor (x ⊗ₜ[ℂ] y)) :=
      funext fun x => norm_localBanachDenseMap I.tensor (x ⊗ₜ[ℂ] y)
    exact he.symm ▸ I.first y
  have hy (x : E) : Continuous (B x) := by
    apply continuous_linear_of_continuous_norm (B x)
    have he : (fun y => ‖B x y‖) = (fun y => I.tensor (x ⊗ₜ[ℂ] y)) :=
      funext fun y => norm_localBanachDenseMap I.tensor (x ⊗ₜ[ℂ] y)
    exact he.symm ▸ I.second x
  have hB : Continuous (fun p : E × F => B p.1 p.2) :=
    (bilinear_seqContinuous_of_separate B (fun y => (hx y).seqContinuous)
      (fun x => (hy x).seqContinuous)).continuous
  let h := continuous_bilinear_bound B hB (normSeminorm ℂ (LocalBanach I.tensor)) continuous_norm
  refine ⟨I.tensor, h.choose, h.choose_spec.choose, h.choose_spec.choose_spec.1,
    h.choose_spec.choose_spec.2.1, fun x y => ?_⟩
  have hh := h.choose_spec.choose_spec.2.2 x y
  change ‖localBanachDenseMap I.tensor (x ⊗ₜ[ℂ] y)‖ ≤ _ at hh
  simpa only [norm_localBanachDenseMap] using hh

/-- On a pair of Fréchet spaces, the inductive and projective tensor
topologies agree by the separately continuous mapping property. -/
theorem frechet_inductive_projective_tensor_equal :
    inductiveTensorTopology E F = projectiveTensorTopology E F := by
  let X := E ⊗[ℂ] F
  have hI := inductiveTensor_withSeminorms (E := E) (F := F)
  have hP := projectiveTensor_withSeminorms (E := E) (F := F)
  have h1 : Continuous[inductiveTensorTopology E F, projectiveTensorTopology E F] (id : X → X) :=
    inductive_to_projective_continuous
  have h2 : Continuous[projectiveTensorTopology E F, inductiveTensorTopology E F] (id : X → X) := by
    letI : TopologicalSpace X := projectiveTensorTopology E F
    exact (@WithSeminorms.continuous_iff_continuous_comp ℂ ℂ X X
      _ _ _ _ _ _ _ (RingHom.id ℂ) _ _ (projectiveTensorTopology E F) hP.topologicalAddGroup
      (inductiveTensorTopology E F) hI LinearMap.id).mpr
        (fun I => hP.continuous_seminorm I.toProjective)
  exact le_antisymm (continuous_id_iff_le.mp h1) (continuous_id_iff_le.mp h2)

/-- The isomorphism on completions induced by the identity on the algebraic tensor product. -/
def frechet_completedTensorEquiv :
    (inductiveTensorModuleStructure E F).Completed ≃L[ℂ]
      (projectiveTensorModuleStructure E F).Completed :=
  TopologicalModuleStructure.completionEquiv (frechet_inductive_projective_tensor_equal (E := E) (F := F))

theorem frechet_completedTensorEquiv_incl (w : E ⊗[ℂ] F) :
    frechet_completedTensorEquiv ((inductiveTensorModuleStructure E F).incl w) =
      (projectiveTensorModuleStructure E F).incl w :=
  TopologicalModuleStructure.completionEquiv_incl
    (frechet_inductive_projective_tensor_equal (E := E) (F := F)) w

end

end FrechetTensor

/-- Tensoring on the left by the identity preserves continuity for the
inductive tensor topology. -/
theorem continuous_inductiveTensor_lTensor
    {A B C : Type*}
    [AddCommGroup A] [Module ℂ A] [TopologicalSpace A] [IsTopologicalAddGroup A]
    [AddCommGroup B] [Module ℂ B] [TopologicalSpace B] [IsTopologicalAddGroup B]
    [AddCommGroup C] [Module ℂ C] [TopologicalSpace C] [IsTopologicalAddGroup C]
    (L : B →ₗ[ℂ] C) (hL : Continuous L) :
    Continuous[inductiveTensorTopology A B, inductiveTensorTopology A C] (L.lTensor A) := by
  letI : TopologicalSpace (A ⊗[ℂ] C) := inductiveTensorTopology A C
  let W := inductiveTensor_withSeminorms (E := A) (F := C)
  letI : PolynormableSpace ℂ (A ⊗[ℂ] C) := W.toPolynormableSpace
  let Bₗ := (TensorProduct.mk ℂ A C).compl₂ L
  change Continuous[inductiveTensorTopology A B, inferInstance] (TensorProduct.lift Bₗ)
  apply (continuous_inductiveTensor_lift_iff Bₗ).mpr
  refine ⟨fun b ↦ ?_, fun a ↦ ?_⟩
  · exact (W.continuous_iff_continuous_comp ((TensorProduct.mk ℂ A C).flip (L b))).mpr
      fun q ↦ q.first (L b)
  · exact ((W.continuous_iff_continuous_comp (TensorProduct.mk ℂ A C a)).mpr
      (fun q ↦ q.second a)).comp hL

/-- A linear homeomorphism on the right factor induces a linear
homeomorphism of inductive tensors. -/
def inductiveTensor_lTensorEquiv
    {A B C : Type*}
    [AddCommGroup A] [Module ℂ A] [TopologicalSpace A] [IsTopologicalAddGroup A]
    [AddCommGroup B] [Module ℂ B] [TopologicalSpace B] [IsTopologicalAddGroup B]
    [AddCommGroup C] [Module ℂ C] [TopologicalSpace C] [IsTopologicalAddGroup C]
    (e : B ≃L[ℂ] C) :
    letI : TopologicalSpace (A ⊗[ℂ] B) := inductiveTensorTopology A B
    letI : TopologicalSpace (A ⊗[ℂ] C) := inductiveTensorTopology A C
    (A ⊗[ℂ] B) ≃L[ℂ] (A ⊗[ℂ] C) := by
  letI : TopologicalSpace (A ⊗[ℂ] B) := inductiveTensorTopology A B
  letI : TopologicalSpace (A ⊗[ℂ] C) := inductiveTensorTopology A C
  exact ⟨e.toLinearEquiv.lTensor A,
    continuous_inductiveTensor_lTensor (A := A) e.toLinearEquiv.toLinearMap e.continuous,
    continuous_inductiveTensor_lTensor (A := A) e.symm.toLinearEquiv.toLinearMap e.symm.continuous⟩

end Masullo
