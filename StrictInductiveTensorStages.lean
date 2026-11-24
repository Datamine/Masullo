import InductiveTensorLimitTopology

open Filter Function Set Topology TopologicalSpace UniformSpace
open scoped TensorProduct Uniformity

namespace Masullo

noncomputable section

variable {A B E F : Type*}
  [AddCommGroup A] [Module ℂ A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [AddCommGroup B] [Module ℂ B] [TopologicalSpace B] [IsTopologicalAddGroup B]
  [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] [IsTopologicalAddGroup F]

private def inductiveToInjectiveMap [PolynormableSpace ℂ E] [PolynormableSpace ℂ F] :
    @ContinuousLinearMap ℂ ℂ _ _ (RingHom.id ℂ)
      (E ⊗[ℂ] F) (inductiveTensorTopology E F) _ (E ⊗[ℂ] F) (injectiveTensorTopology E F) _ _ _ := by
  let X := E ⊗[ℂ] F
  refine @ContinuousLinearMap.mk ℂ ℂ _ _ (RingHom.id ℂ) X (inductiveTensorTopology E F) _
    X (injectiveTensorTopology E F) _ _ _ LinearMap.id ?_
  exact @Continuous.comp X X X (inductiveTensorTopology E F) (projectiveTensorTopology E F)
    (injectiveTensorTopology E F) id id
    (projective_to_injective_continuous (E := E) (F := F))
    (inductive_to_projective_continuous (E := E) (F := F))

/-- The canonical map from the inductive completion to the injective completion. -/
def completedInductiveToInjective [PolynormableSpace ℂ E] [PolynormableSpace ℂ F] :
    (inductiveTensorModuleStructure E F).Completed →L[ℂ]
      (injectiveTensorStructure E F).Completed := by
  let X := E ⊗[ℂ] F
  let D := inductiveTensorModuleStructure E F
  let C := injectiveTensorStructure E F
  exact @ContinuousLinearMap.completion X X ℂ ℂ D.uniformSpace _ D.uniformGroup _ _
    D.uniformConstSmul _ C.uniformSpace _ C.uniformGroup _ C.uniformConstSmul _
    (inductiveToInjectiveMap (E := E) (F := F))

@[simp] theorem completedInductiveToInjective_incl [PolynormableSpace ℂ E] [PolynormableSpace ℂ F]
    (z : E ⊗[ℂ] F) :
    completedInductiveToInjective ((inductiveTensorModuleStructure E F).incl z) =
      (injectiveTensorStructure E F).incl z := by
  let D := inductiveTensorModuleStructure E F
  let C := injectiveTensorStructure E F
  exact @ContinuousLinearMap.completion_apply_coe (E ⊗[ℂ] F) (E ⊗[ℂ] F) ℂ ℂ
    D.uniformSpace _ D.uniformGroup _ _ D.uniformConstSmul _ C.uniformSpace _
    C.uniformGroup _ C.uniformConstSmul _ (inductiveToInjectiveMap (E := E) (F := F)) z

omit [IsTopologicalAddGroup A] [IsTopologicalAddGroup B]
  [IsTopologicalAddGroup E] [IsTopologicalAddGroup F] in
/-- The completed injective tensor map agrees with the algebraic map on the dense tensor product. -/
theorem completedInjectiveTensorMap_incl
    (u : A →L[ℂ] E) (v : B →L[ℂ] F) (z : A ⊗[ℂ] B) :
    completedInjectiveTensorMap u v ((injectiveTensorStructure A B).incl z) =
      (injectiveTensorStructure E F).incl (TensorProduct.map u.toLinearMap v.toLinearMap z) := by
  let D := injectiveTensorStructure A B
  let C := injectiveTensorStructure E F
  letI : UniformSpace (A ⊗[ℂ] B) := D.uniformSpace
  letI : UniformSpace (E ⊗[ℂ] F) := C.uniformSpace
  letI : IsUniformAddGroup (A ⊗[ℂ] B) := D.uniformGroup
  letI : IsUniformAddGroup (E ⊗[ℂ] F) := C.uniformGroup
  letI : UniformContinuousConstSMul ℂ (A ⊗[ℂ] B) := D.uniformConstSmul
  letI : UniformContinuousConstSMul ℂ (E ⊗[ℂ] F) := C.uniformConstSmul
  let L : (A ⊗[ℂ] B) →L[ℂ] (E ⊗[ℂ] F) :=
    ⟨TensorProduct.map u.toLinearMap v.toLinearMap, injectiveTensor_map_continuous u v⟩
  exact L.completion_apply_coe z

/-- When the stage tensor has the injective topology, its map into the
ambient inductive completion is an embedding. -/
theorem completedInductiveTensor_map_isEmbedding_of_equal
    [PolynormableSpace ℂ E] [PolynormableSpace ℂ F]
    (u : A →L[ℂ] E) (v : B →L[ℂ] F) (hu : IsEmbedding u) (hv : IsEmbedding v)
    (h : inductiveTensorTopology A B = injectiveTensorTopology A B) :
    IsEmbedding (completedInductiveTensor_map u v) := by
  let C := injectiveTensorStructure E F
  letI : UniformSpace (E ⊗[ℂ] F) := C.uniformSpace
  letI : T0Space C.Completed := Completion.t0Space (E ⊗[ℂ] F)
  let T := inductiveTensorModuleStructure A B
  let e : T.Completed ≃L[ℂ] (injectiveTensorStructure A B).Completed :=
    TopologicalModuleStructure.completionEquiv h
  let P := completedInductiveToInjective (E := E) (F := F)
  let J := completedInductiveTensor_map u v
  let K := completedInjectiveTensorMap u v
  have he : P.comp J = K.comp e.toContinuousLinearMap := by
    apply T.continuousLinearMap_ext_on_tmul
    intro a b
    change P (J (T.incl (a ⊗ₜ[ℂ] b))) = K (e (T.incl (a ⊗ₜ[ℂ] b)))
    rw [completedInductiveTensor_map_incl, completedInductiveToInjective_incl]
    rw [show e (T.incl (a ⊗ₜ[ℂ] b)) = (injectiveTensorStructure A B).incl (a ⊗ₜ[ℂ] b) from
      TopologicalModuleStructure.completionEquiv_incl h _,
      completedInjectiveTensorMap_incl]
  have hcomp : IsEmbedding ((P : _ → _) ∘ J) := by
    have hh : ((P : _ → _) ∘ J) = K ∘ e := funext (DFunLike.congr_fun he)
    rw [hh]
    exact (completedInjectiveTensorMap_isClosedEmbedding u v hu hv).isEmbedding.comp
      e.toHomeomorph.isEmbedding
  exact IsEmbedding.of_comp J.continuous P.continuous hcomp

end

section NuclearFrechet

universe u v

variable {A : Type u} {B : Type v}
  [AddCommGroup A] [Module ℂ A] [TopologicalSpace A]
  [AddCommGroup B] [Module ℂ B] [TopologicalSpace B] [T2Space B]

omit [T2Space B] in
/-- The inductive and projective tensor topologies agree on Fréchet stages. -/
theorem frechet_inductiveTensorTopology_eq_projective
    (hA : IsFrechetTVS A) (hB : IsFrechetTVS B) :
    inductiveTensorTopology A B = projectiveTensorTopology A B := by
  letI : IsTopologicalAddGroup A := hA.choose
  letI : PolynormableSpace ℂ A := hA.choose_spec.1
  letI : MetrizableSpace A := hA.choose_spec.2.1
  letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A
  letI : IsUniformAddGroup A := isUniformAddGroup_of_addCommGroup
  letI : CompleteSpace A := hA.choose_spec.2.2
  letI : ContinuousSMul ℂ A := (PolynormableSpace.withSeminorms ℂ A).continuousSMul
  haveI : (uniformity A).IsCountablyGenerated := by
    rw [uniformity_eq_comap_nhds_zero A]
    infer_instance
  letI : BaireSpace A := BaireSpace.of_completelyPseudoMetrizable
  letI : IsTopologicalAddGroup B := hB.choose
  letI : PolynormableSpace ℂ B := hB.choose_spec.1
  letI : MetrizableSpace B := hB.choose_spec.2.1
  exact frechet_inductive_projective_tensor_equal

/-- The inductive and injective tensor topologies agree on nuclear Fréchet stages. -/
theorem nuclearFrechet_inductiveTensorTopology_eq_injective
    (hA : IsFrechetTVS A) (hB : IsFrechetTVS B)
    (hN : NuclearLocallyConvex.{v} A) :
    inductiveTensorTopology A B = injectiveTensorTopology A B := by
  letI : PolynormableSpace ℂ B := hB.choose_spec.1
  exact (frechet_inductiveTensorTopology_eq_projective hA hB).trans (hN.2.2 B)

end NuclearFrechet

noncomputable section

variable {A B E F G H : Type*}
  [AddCommGroup A] [Module ℂ A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [AddCommGroup B] [Module ℂ B] [TopologicalSpace B] [IsTopologicalAddGroup B]
  [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [AddCommGroup G] [Module ℂ G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [AddCommGroup H] [Module ℂ H] [TopologicalSpace H] [IsTopologicalAddGroup H]

theorem completedInductiveTensor_map_comp
    (a : A →L[ℂ] E) (b : B →L[ℂ] F) (c : E →L[ℂ] G) (d : F →L[ℂ] H) :
    (completedInductiveTensor_map c d).comp (completedInductiveTensor_map a b) =
      completedInductiveTensor_map (c.comp a) (d.comp b) := by
  let S := inductiveTensorModuleStructure A B
  let D := inductiveTensorModuleStructure G H
  letI : UniformSpace (G ⊗[ℂ] H) := D.uniformSpace
  letI : T0Space D.Completed := Completion.t0Space (G ⊗[ℂ] H)
  apply S.continuousLinearMap_ext_on_tmul
  intro x y
  change completedInductiveTensor_map c d
      (completedInductiveTensor_map a b ((inductiveTensorModuleStructure A B).incl (x ⊗ₜ[ℂ] y))) =
    completedInductiveTensor_map (c.comp a) (d.comp b)
      ((inductiveTensorModuleStructure A B).incl (x ⊗ₜ[ℂ] y))
  rw [completedInductiveTensor_map_tmul, completedInductiveTensor_map_tmul,
    completedInductiveTensor_map_tmul, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]

theorem completedInductiveTensor_map_id :
    completedInductiveTensor_map (ContinuousLinearMap.id ℂ A) (ContinuousLinearMap.id ℂ B) =
      ContinuousLinearMap.id ℂ (inductiveTensorModuleStructure A B).Completed := by
  let D := inductiveTensorModuleStructure A B
  letI : UniformSpace (A ⊗[ℂ] B) := D.uniformSpace
  letI : T0Space D.Completed := Completion.t0Space (A ⊗[ℂ] B)
  apply D.continuousLinearMap_ext_on_tmul
  intro x y
  exact completedInductiveTensor_map_tmul (ContinuousLinearMap.id ℂ A)
    (ContinuousLinearMap.id ℂ B) x y

end

end Masullo
