import TensorCompletionExactness
import FixedFactorStrictTensor
import StrictLimitExactness
import InjectiveTensorFlip
import CompletedTensorFlip

open Function Set Topology TopologicalSpace UniformSpace
open scoped TensorProduct

namespace Masullo

noncomputable section

section Flip

variable {A B R S : Type*}
  [AddCommGroup A] [Module ℂ A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [AddCommGroup B] [Module ℂ B] [TopologicalSpace B] [IsTopologicalAddGroup B]
  [AddCommGroup R] [Module ℂ R] [TopologicalSpace R] [IsTopologicalAddGroup R]
  [AddCommGroup S] [Module ℂ S] [TopologicalSpace S] [IsTopologicalAddGroup S]

/-- The completed tensor flip commutes with changes of both factors. -/
theorem completedInductiveTensor_flip_natural
    (f : A →L[ℂ] B) (g : R →L[ℂ] S)
    (e : (inductiveTensorModuleStructure A R).Completed ≃L[ℂ]
      (inductiveTensorModuleStructure R A).Completed)
    (d : (inductiveTensorModuleStructure B S).Completed ≃L[ℂ]
      (inductiveTensorModuleStructure S B).Completed)
    (he : ∀ z, e ((inductiveTensorModuleStructure A R).incl z) =
      (inductiveTensorModuleStructure R A).incl (TensorProduct.comm ℂ A R z))
    (hd : ∀ z, d ((inductiveTensorModuleStructure B S).incl z) =
      (inductiveTensorModuleStructure S B).incl (TensorProduct.comm ℂ B S z)) :
    d.toContinuousLinearMap.comp (completedInductiveTensor_map f g) =
      (completedInductiveTensor_map g f).comp e.toContinuousLinearMap := by
  let D := inductiveTensorModuleStructure S B
  letI : UniformSpace (S ⊗[ℂ] B) := D.uniformSpace
  letI : T0Space D.Completed := Completion.t0Space (S ⊗[ℂ] B)
  apply (inductiveTensorModuleStructure A R).continuousLinearMap_ext_on_tmul
  intro a r
  change d (completedInductiveTensor_map f g ((inductiveTensorModuleStructure A R).incl (a ⊗ₜ[ℂ] r))) =
    completedInductiveTensor_map g f (e ((inductiveTensorModuleStructure A R).incl (a ⊗ₜ[ℂ] r)))
  rw [completedInductiveTensor_map_tmul, hd, he, TensorProduct.comm_tmul, TensorProduct.comm_tmul,
    completedInductiveTensor_map_tmul]

end Flip

section Stages

variable {A B C R : Type*}
  [AddCommGroup A] [Module ℂ A] [TopologicalSpace A] [IsTopologicalAddGroup A] [PolynormableSpace ℂ A]
  [AddCommGroup B] [Module ℂ B] [TopologicalSpace B] [IsTopologicalAddGroup B] [PolynormableSpace ℂ B]
  [AddCommGroup C] [Module ℂ C] [TopologicalSpace C] [IsTopologicalAddGroup C] [PolynormableSpace ℂ C]
  [AddCommGroup R] [Module ℂ R] [TopologicalSpace R] [IsTopologicalAddGroup R] [PolynormableSpace ℂ R]
  [FirstCountableTopology B] [FirstCountableTopology R]

private theorem completedInductiveTensor_stage_exact
    (f : A →L[ℂ] B) (g : B →L[ℂ] C) (hfg : Exact f g)
    (hf : IsEmbedding f) (hg : IsQuotientMap g)
    (hA : inductiveTensorTopology A R = projectiveTensorTopology A R)
    (hB : inductiveTensorTopology B R = projectiveTensorTopology B R)
    (hC : inductiveTensorTopology C R = projectiveTensorTopology C R)
    (hA' : projectiveTensorTopology A R = injectiveTensorTopology A R)
    (hB' : projectiveTensorTopology B R = injectiveTensorTopology B R) :
    let j := completedInductiveTensor_map f (ContinuousLinearMap.id ℂ R)
    let q := completedInductiveTensor_map g (ContinuousLinearMap.id ℂ R)
    IsEmbedding j ∧ Exact j q ∧ Surjective q := by
  let eA : (inductiveTensorModuleStructure A R).Completed ≃L[ℂ]
      (projectiveTensorModuleStructure A R).Completed := TopologicalModuleStructure.completionEquiv hA
  let eB : (inductiveTensorModuleStructure B R).Completed ≃L[ℂ]
      (projectiveTensorModuleStructure B R).Completed := TopologicalModuleStructure.completionEquiv hB
  let eC : (inductiveTensorModuleStructure C R).Completed ≃L[ℂ]
      (projectiveTensorModuleStructure C R).Completed := TopologicalModuleStructure.completionEquiv hC
  let idR := ContinuousLinearMap.id ℂ R
  let j := completedInductiveTensor_map f idR
  let q := completedInductiveTensor_map g idR
  let J := completedProjectiveTensorMap f idR
  let Q := completedProjectiveTensorMap g idR
  obtain ⟨hJ, hEQ, hQ⟩ := completedProjectiveTensor_stage_exact f g hfg hf hg hA' hB'
  have hj (x : (inductiveTensorModuleStructure A R).Completed) : eB (j x) = J (eA x) :=
    DFunLike.congr_fun (completedInductiveTensor_projective_natural f hA hB) x
  have hq (y : (inductiveTensorModuleStructure B R).Completed) : eC (q y) = Q (eB y) :=
    DFunLike.congr_fun (completedInductiveTensor_projective_natural g hB hC) y
  refine ⟨?_, ?_, ?_⟩
  · change IsEmbedding j
    have he : (j : _ → _) = eB.symm ∘ J ∘ eA := funext fun x =>
      (eB.symm_apply_apply (j x)).symm.trans (congrArg eB.symm (hj x))
    rw [he]
    exact eB.symm.toHomeomorph.isEmbedding.comp (hJ.isEmbedding.comp eA.toHomeomorph.isEmbedding)
  · change Exact j q
    intro y
    constructor
    · intro hy
      have h : Q (eB y) = 0 := (hq y).symm.trans (hy ▸ eC.map_zero)
      obtain ⟨x, hx⟩ := (hEQ (eB y)).mp h
      refine ⟨eA.symm x, eB.injective ?_⟩
      rw [hj, eA.apply_symm_apply, hx]
    · rintro ⟨x, rfl⟩
      apply eC.injective
      rw [map_zero, hq, hj]
      exact (hEQ (J (eA x))).mpr (mem_range_self _)
  · change Surjective q
    intro y
    obtain ⟨z, hz⟩ := hQ.surjective (eC y)
    refine ⟨eB.symm z, eC.injective ?_⟩
    rw [hq, eB.apply_symm_apply, hz]

omit [PolynormableSpace ℂ A] [PolynormableSpace ℂ B] [PolynormableSpace ℂ C]
  [PolynormableSpace ℂ R] [FirstCountableTopology B] [FirstCountableTopology R] in
private theorem completedInductiveTensor_stage_exact_flip
    (f : A →L[ℂ] B) (g : B →L[ℂ] C)
    (h : let j := completedInductiveTensor_map f (ContinuousLinearMap.id ℂ R)
         let q := completedInductiveTensor_map g (ContinuousLinearMap.id ℂ R)
         IsEmbedding j ∧ Exact j q ∧ Surjective q) :
    let j := completedInductiveTensor_map (ContinuousLinearMap.id ℂ R) f
    let q := completedInductiveTensor_map (ContinuousLinearMap.id ℂ R) g
    IsEmbedding j ∧ Exact j q ∧ Surjective q := by
  obtain ⟨eA, heA⟩ := exists_completedInductiveTensorFlip (A := R) (R := A)
  obtain ⟨eB, heB⟩ := exists_completedInductiveTensorFlip (A := R) (R := B)
  obtain ⟨eC, heC⟩ := exists_completedInductiveTensorFlip (A := R) (R := C)
  let i := ContinuousLinearMap.id ℂ R
  let j := completedInductiveTensor_map i f
  let q := completedInductiveTensor_map i g
  let J := completedInductiveTensor_map f i
  let Q := completedInductiveTensor_map g i
  have hj (x : (inductiveTensorModuleStructure R A).Completed) : eB (j x) = J (eA x) :=
    DFunLike.congr_fun (completedInductiveTensor_flip_natural i f eA eB heA heB) x
  have hq (y : (inductiveTensorModuleStructure R B).Completed) : eC (q y) = Q (eB y) :=
    DFunLike.congr_fun (completedInductiveTensor_flip_natural i g eB eC heB heC) y
  refine ⟨?_, ?_, ?_⟩
  · change IsEmbedding j
    have he : (j : _ → _) = eB.symm ∘ J ∘ eA := funext fun x =>
      (eB.symm_apply_apply (j x)).symm.trans (congrArg eB.symm (hj x))
    rw [he]
    exact eB.symm.toHomeomorph.isEmbedding.comp (h.1.comp eA.toHomeomorph.isEmbedding)
  · change Exact j q
    intro y
    constructor
    · intro hy
      have hz : Q (eB y) = 0 := (hq y).symm.trans (hy ▸ eC.map_zero)
      obtain ⟨x, hx⟩ := (h.2.1 (eB y)).mp hz
      refine ⟨eA.symm x, eB.injective ?_⟩
      rw [hj, eA.apply_symm_apply, hx]
    · rintro ⟨x, rfl⟩
      apply eC.injective
      rw [map_zero, hq, hj]
      exact (h.2.1 (J (eA x))).mpr (mem_range_self _)
  · change Surjective q
    intro y
    obtain ⟨z, hz⟩ := h.2.2 (eC y)
    refine ⟨eB.symm z, eC.injective ?_⟩
    rw [hq, eB.apply_symm_apply, hz]

end Stages

private theorem isFrechetTVS_completedInductiveTensor
    {A B : Type*} [AddCommGroup A] [Module ℂ A] [TopologicalSpace A]
    [AddCommGroup B] [Module ℂ B] [TopologicalSpace B]
    (hA : IsFrechetTVS A) (hB : IsFrechetTVS B) :
    IsFrechetTVS (inductiveTensorModuleStructure A B).Completed :=
  (congrArg (fun D : TopologicalModuleStructure (A ⊗[ℂ] B) => IsFrechetTVS D.Completed)
    (TopologicalModuleStructure.eq_of_topology_eq
      (frechet_inductiveTensorTopology_eq_projective hA hB))).mpr
    (isFrechetTVS_completedProjectiveTensor hA hB)

section Limit

universe u v
variable {A : Type u} {B : Type v} {R : Type*} {X : ℕ → Type*}
  [AddCommGroup A] [Module ℂ A] [TopologicalSpace A] [T2Space A]
  [AddCommGroup B] [Module ℂ B] [TopologicalSpace B] [T2Space B]
  [AddCommGroup R] [Module ℂ R] [TopologicalSpace R] [IsTopologicalAddGroup R]
  [PolynormableSpace ℂ R]
  [∀ n, AddCommGroup (X n)] [∀ n, Module ℂ (X n)] [∀ n, TopologicalSpace (X n)]

set_option maxHeartbeats 1500000 in
/-- Proposition C.2.3.14, pp. 684–685. The embedding of the Fréchet factor
extends to a closed embedding after completed inductive tensoring with
the strict countable limit of nuclear Fréchet spaces. -/
theorem completedInductiveTensor_strictLimit_embedding
    (f : A →L[ℂ] B) (hf : IsEmbedding f) (hA : IsFrechetTVS A) (hB : IsFrechetTVS B)
    (D : LinearInductivePresentation R X) (hD : ∀ n, IsEmbedding (D.incl n))
    (hX : ∀ n, IsFrechetTVS (X n))
    (hNu : ∀ n, NuclearLocallyConvex.{u} (X n))
    (hNv : ∀ n, NuclearLocallyConvex.{v} (X n))
    (hFinal : (inferInstance : TopologicalSpace R) =
      locallyConvexFinalTopology (fun n => (D.incl n).toLinearMap)) :
    letI : IsTopologicalAddGroup A := hA.choose
    letI : IsTopologicalAddGroup B := hB.choose
    IsClosedEmbedding (completedInductiveTensor_map f (ContinuousLinearMap.id ℂ R)) := by
  letI : IsTopologicalAddGroup A := hA.choose
  letI : IsTopologicalAddGroup B := hB.choose
  letI : PolynormableSpace ℂ A := hA.choose_spec.1
  letI : PolynormableSpace ℂ B := hB.choose_spec.1
  letI : ContinuousSMul ℂ B := (PolynormableSpace.withSeminorms ℂ B).continuousSMul
  letI : MetrizableSpace B := hB.choose_spec.2.1
  letI : ∀ n, IsTopologicalAddGroup (X n) := fun n => (hX n).choose
  letI : ∀ n, PolynormableSpace ℂ (X n) := fun n => (hX n).choose_spec.1
  letI : ∀ n, MetrizableSpace (X n) := fun n => (hX n).choose_spec.2.1
  let K := f.toLinearMap.range
  let C := B ⧸ K
  have hK : IsClosed (K : Set B) := (hA.isClosedEmbedding f hf).isClosed_range
  letI : IsClosed (K : Set B) := hK
  let q : B →L[ℂ] C := K.mkQL
  have hC : IsFrechetTVS C := isFrechetTVS_closedQuotient hB K hK
  letI : IsTopologicalAddGroup C := hC.choose
  letI : PolynormableSpace ℂ C := hC.choose_spec.1
  have hA' (n : ℕ) : inductiveTensorTopology (X n) A = injectiveTensorTopology (X n) A :=
    nuclearFrechet_inductiveTensorTopology_eq_injective (hX n) hA (hNu n)
  have hB' (n : ℕ) : inductiveTensorTopology (X n) B = injectiveTensorTopology (X n) B :=
    nuclearFrechet_inductiveTensorTopology_eq_injective (hX n) hB (hNv n)
  have hC' (n : ℕ) : inductiveTensorTopology (X n) C = injectiveTensorTopology (X n) C :=
    nuclearFrechet_inductiveTensorTopology_eq_injective (hX n) hC (hNv n)
  let t (n k : ℕ) (h : n ≤ k) := D.transition h
  have hc (n k : ℕ) (h : n ≤ k) : (D.incl k).comp (t n k h) = D.incl n :=
    ContinuousLinearMap.ext (D.incl_transition h)
  obtain ⟨DA, hDA, -, -⟩ := exists_completedInductiveTensor_presentation_of_strict_left
    D.incl t hc D.exhaust hFinal hD hA'
  obtain ⟨DB, hDB, hEB, -⟩ := exists_completedInductiveTensor_presentation_of_strict_left
    D.incl t hc D.exhaust hFinal hD hB'
  obtain ⟨DC, hDC, hEC, -⟩ := exists_completedInductiveTensor_presentation_of_strict_left
    D.incl t hc D.exhaust hFinal hD hC'
  let idR := ContinuousLinearMap.id ℂ R
  let idX (n : ℕ) := ContinuousLinearMap.id ℂ (X n)
  let J := completedInductiveTensor_map idR f
  let Q := completedInductiveTensor_map idR q
  let Jₙ (n : ℕ) := completedInductiveTensor_map (idX n) f
  let Qₙ (n : ℕ) := completedInductiveTensor_map (idX n) q
  have hJ (n : ℕ) : J.comp (DA.incl n) = (DB.incl n).comp (Jₙ n) := by
    rw [hDA n, hDB n]
    simp only [J, Jₙ, completedInductiveTensor_map_comp, idR, idX, ContinuousLinearMap.id_comp,
      ContinuousLinearMap.comp_id]
  have hQ (n : ℕ) : Q.comp (DB.incl n) = (DC.incl n).comp (Qₙ n) := by
    rw [hDB n, hDC n]
    simp only [Q, Qₙ, completedInductiveTensor_map_comp, idR, idX, ContinuousLinearMap.id_comp,
      ContinuousLinearMap.comp_id]
  have hfq : Exact f q := by
    intro y
    exact Submodule.Quotient.mk_eq_zero K
  have hStage (n : ℕ) : IsEmbedding (Jₙ n) ∧ Exact (Jₙ n) (Qₙ n) ∧ Surjective (Qₙ n) := by
    exact completedInductiveTensor_stage_exact_flip f q
      (completedInductiveTensor_stage_exact f q hfq hf K.isQuotientMap_mkQ
        (frechet_inductiveTensorTopology_eq_projective hA (hX n))
        (frechet_inductiveTensorTopology_eq_projective hB (hX n))
        (frechet_inductiveTensorTopology_eq_projective hC (hX n))
        (tensorTopologies_equal_of_flip ((hNu n).2.2 A))
        (tensorTopologies_equal_of_flip ((hNv n).2.2 B)))
  let TA := inductiveTensorModuleStructure R A
  let TB := inductiveTensorModuleStructure R B
  let TC := inductiveTensorModuleStructure R C
  letI : UniformSpace (R ⊗[ℂ] A) := TA.uniformSpace
  letI : UniformSpace (R ⊗[ℂ] B) := TB.uniformSpace
  letI : UniformSpace (R ⊗[ℂ] C) := TC.uniformSpace
  letI : IsUniformAddGroup (R ⊗[ℂ] A) := TA.uniformGroup
  letI : IsUniformAddGroup (R ⊗[ℂ] B) := TB.uniformGroup
  letI : IsUniformAddGroup (R ⊗[ℂ] C) := TC.uniformGroup
  letI : UniformContinuousConstSMul ℂ (R ⊗[ℂ] A) := TA.uniformConstSmul
  letI : PolynormableSpace ℂ (R ⊗[ℂ] A) := inductiveTensor_withSeminorms.toPolynormableSpace
  letI : PolynormableSpace ℂ TA.Completed := polynormableSpace_completion
  letI : IsUniformAddGroup TB.Completed := Completion.isUniformAddGroup
  letI : IsUniformAddGroup TC.Completed := Completion.isUniformAddGroup
  letI : IsTopologicalAddGroup TB.Completed := inferInstanceAs (IsTopologicalAddGroup (Completion (R ⊗[ℂ] B)))
  letI : IsTopologicalAddGroup TC.Completed := inferInstanceAs (IsTopologicalAddGroup (Completion (R ⊗[ℂ] C)))
  letI : T0Space TC.Completed := Completion.t0Space (R ⊗[ℂ] C)
  have hFC (n : ℕ) : IsClosed (range (DC.incl n)) :=
    ((isFrechetTVS_completedInductiveTensor (hX n) hC).isClosedEmbedding (DC.incl n) (hEC n)).isClosed_range
  have hFinalB (p : Seminorm ℂ TB.Completed)
      (hp : ∀ n, Continuous (p.comp (DB.incl n).toLinearMap)) : Continuous p :=
    completedInductiveTensor_stage_seminorm_continuous_of_strict_left D.incl t hc D.exhaust hFinal hD hB'
      p (fun n => hDB n ▸ hp n)
  have he : IsClosedEmbedding J := closedEmbedding_of_exact_inductive_presentations DA DB DC J Q
    Jₙ Qₙ hJ hQ (fun n => (hStage n).1) (fun n => (hStage n).2.1) (fun n => (hStage n).2.2)
    (fun n => isFrechetTVS_completedInductiveTensor (hX n) hB) hEB hFC hFinalB
  obtain ⟨eA, heA⟩ := exists_completedInductiveTensorFlip (A := A) (R := R)
  obtain ⟨eB, heB⟩ := exists_completedInductiveTensorFlip (A := B) (R := R)
  let j := completedInductiveTensor_map f idR
  have hn (z : (inductiveTensorModuleStructure A R).Completed) : eB (j z) = J (eA z) :=
    DFunLike.congr_fun (completedInductiveTensor_flip_natural f idR eA eB heA heB) z
  change IsClosedEmbedding j
  have heq : (j : _ → _) = eB.symm ∘ J ∘ eA := funext fun x =>
    (eB.symm_apply_apply (j x)).symm.trans (congrArg eB.symm (hn x))
  rw [heq]
  exact eB.symm.toHomeomorph.isClosedEmbedding.comp (he.comp eA.toHomeomorph.isClosedEmbedding)

end Limit

end
end Masullo
