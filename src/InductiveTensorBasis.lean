import InductiveTensorTopology
import LocallyConvexSumCompletion
import FinestLocallyConvex
import Mathlib.LinearAlgebra.TensorProduct.Basis

open Function Module Topology
open scoped Classical DirectSum TensorProduct

namespace Masullo

noncomputable section

variable {I E V : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup V] [Module ℂ V]

private def tensorBasisLinearEquiv (b : Basis I ℂ V) : E ⊗[ℂ] V ≃ₗ[ℂ] ⨁ _ : I, E :=
  (TensorProduct.equivFinsuppOfBasisRight b).trans (finsuppLequivDFinsupp ℂ)

private theorem tensorBasisLinearEquiv_tmul (b : Basis I ℂ V) (x : E) (v : V) (i : I) :
    tensorBasisLinearEquiv b (x ⊗ₜ[ℂ] v) i = b.repr v i • x :=
  TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply b x v i

private theorem tensorBasisLinearEquiv_symm_lof (b : Basis I ℂ V) (i : I) (x : E) :
    (tensorBasisLinearEquiv b).symm (DirectSum.lof ℂ I (fun _ ↦ E) i x) = x ⊗ₜ[ℂ] b i := by
  apply (tensorBasisLinearEquiv b).injective
  rw [LinearEquiv.apply_symm_apply]
  ext j
  change DFinsupp.single (β := fun _ : I ↦ E) i x j = _
  rw [tensorBasisLinearEquiv_tmul, b.repr_self, Finsupp.single_apply]
  by_cases h : i = j
  · subst j
    simp
  · rw [DFinsupp.single_eq_of_ne (Ne.symm h)]
    simp [h]

/-- An inductive tensor product with a finest-topology factor is the
locally convex direct sum of copies of the other factor along any basis. -/
def inductiveTensorBasisEquiv [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousConstSMul ℂ E]
    (b : Basis I ℂ V) :
    letI : TopologicalSpace V := finestLocallyConvexTopology V
    letI : TopologicalSpace (E ⊗[ℂ] V) := inductiveTensorTopology E V
    letI : TopologicalSpace (⨁ _ : I, E) := locallyConvexSumTopology (fun _ : I ↦ E)
    (E ⊗[ℂ] V) ≃L[ℂ] (⨁ _ : I, E) := by
  letI : TopologicalSpace V := finestLocallyConvexTopology V
  letI : TopologicalSpace (E ⊗[ℂ] V) := inductiveTensorTopology E V
  letI : TopologicalSpace (⨁ _ : I, E) := locallyConvexSumTopology (fun _ : I ↦ E)
  let j := DirectSum.lof ℂ I (fun _ ↦ E)
  let e : (E ⊗[ℂ] V) ≃ₗ[ℂ] ⨁ _ : I, E := tensorBasisLinearEquiv b
  let W := inductiveTensor_withSeminorms (E := E) (F := V)
  let W' := locallyConvexFinal_withSeminorms j
  letI : IsTopologicalAddGroup (E ⊗[ℂ] V) := W.topologicalAddGroup
  letI : IsTopologicalAddGroup (⨁ _ : I, E) := W'.topologicalAddGroup
  letI : PolynormableSpace ℂ (E ⊗[ℂ] V) := W.toPolynormableSpace
  letI : PolynormableSpace ℂ (⨁ _ : I, E) := W'.toPolynormableSpace
  refine ⟨e, ?_, ?_⟩
  · have hterm (v : V) (x : E) :
        e (x ⊗ₜ[ℂ] v) = ∑ i ∈ (b.repr v).support, j i (b.repr v i • x) := by
      ext i
      change tensorBasisLinearEquiv b (x ⊗ₜ[ℂ] v) i =
        (∑ l ∈ (b.repr v).support, DFinsupp.single (β := fun _ : I ↦ E) l (b.repr v l • x)) i
      rw [tensorBasisLinearEquiv_tmul, DFinsupp.finsetSum_apply]
      by_cases hi : i ∈ (b.repr v).support
      · rw [Finset.sum_eq_single i]
        · rw [DFinsupp.single_eq_same]
        · intro l _ hl
          exact DFinsupp.single_eq_of_ne hl.symm
        · exact fun h ↦ (h hi).elim
      · have hz := Finsupp.notMem_support_iff.mp hi
        simp only [hz, zero_smul]
        symm
        apply Finset.sum_eq_zero
        intro l hl
        exact DFinsupp.single_eq_of_ne (fun e ↦ hi (e.symm ▸ hl))
    apply (W'.continuous_iff_continuous_comp e.toLinearMap).mpr
    intro q
    refine W.continuous_seminorm (⟨q.val.comp e.toLinearMap, ?_, ?_⟩ : InductiveTensorTest E V)
    · intro v
      change Continuous (fun x : E ↦ q.val (e (x ⊗ₜ[ℂ] v)))
      simp_rw [hterm]
      have hq : Continuous q.val := W'.continuous_seminorm q
      have hs : Continuous (fun x : E ↦ ∑ i ∈ (b.repr v).support, j i (b.repr v i • x)) :=
        continuous_finsetSum _ fun i _ ↦
          (locallyConvexFinal_stage_continuous j i).comp (continuous_const_smul _)
      exact hq.comp hs
    · intro x
      change Continuous (q.val.comp (e.toLinearMap.comp (TensorProduct.mk ℂ E V x)))
      exact (finest_withSeminorms V).continuous_seminorm _
  · apply (locallyConvexFinal_continuous_iff j e.symm.toLinearMap).mpr
    intro i
    let T := (TensorProduct.mk ℂ E V).flip (b i)
    have hT : Continuous T := (W.continuous_iff_continuous_comp T).mpr fun q ↦ q.first (b i)
    exact hT.congr fun x ↦ (tensorBasisLinearEquiv_symm_lof b i x).symm

@[simp] theorem inductiveTensorBasisEquiv_tmul_apply [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousConstSMul ℂ E]
    (b : Basis I ℂ V) (x : E) (v : V) (i : I) :
    letI : TopologicalSpace V := finestLocallyConvexTopology V
    letI : TopologicalSpace (E ⊗[ℂ] V) := inductiveTensorTopology E V
    letI : TopologicalSpace (⨁ _ : I, E) := locallyConvexSumTopology (fun _ : I ↦ E)
    inductiveTensorBasisEquiv b (x ⊗ₜ[ℂ] v) i = b.repr v i • x :=
  tensorBasisLinearEquiv_tmul b x v i

@[simp] theorem inductiveTensorBasisEquiv_symm_lof [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousConstSMul ℂ E]
    (b : Basis I ℂ V) (i : I) (x : E) :
    letI : TopologicalSpace V := finestLocallyConvexTopology V
    letI : TopologicalSpace (E ⊗[ℂ] V) := inductiveTensorTopology E V
    letI : TopologicalSpace (⨁ _ : I, E) := locallyConvexSumTopology (fun _ : I ↦ E)
    (inductiveTensorBasisEquiv b).symm (DirectSum.lof ℂ I (fun _ ↦ E) i x) = x ⊗ₜ[ℂ] b i :=
  tensorBasisLinearEquiv_symm_lof b i x

/-- Tensoring an embedded subspace with a finest-topology vector space
preserves the subspace topology for the inductive tensor product. -/
theorem inductiveTensor_submodule_isEmbedding [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousConstSMul ℂ E] [PolynormableSpace ℂ E] (b : Basis I ℂ V) (P : Submodule ℂ E) :
    letI : TopologicalSpace V := finestLocallyConvexTopology V
    letI : TopologicalSpace (P ⊗[ℂ] V) := inductiveTensorTopology P V
    letI : TopologicalSpace (E ⊗[ℂ] V) := inductiveTensorTopology E V
    IsEmbedding (TensorProduct.map P.subtype (LinearMap.id : V →ₗ[ℂ] V)) := by
  letI : TopologicalSpace V := finestLocallyConvexTopology V
  letI : TopologicalSpace (P ⊗[ℂ] V) := inductiveTensorTopology P V
  letI : TopologicalSpace (E ⊗[ℂ] V) := inductiveTensorTopology E V
  letI : TopologicalSpace (⨁ _ : I, P) := locallyConvexSumTopology (fun _ : I ↦ P)
  letI : TopologicalSpace (⨁ _ : I, E) := locallyConvexSumTopology (fun _ : I ↦ E)
  letI : ContinuousConstSMul ℂ P := IsInducing.subtypeVal.continuousConstSMul id (fun {_ _} ↦ rfl)
  let eP := inductiveTensorBasisEquiv (E := P) b
  let eE := inductiveTensorBasisEquiv (E := E) b
  let T := TensorProduct.map P.subtype (LinearMap.id : V →ₗ[ℂ] V)
  let D : (⨁ _ : I, P) →ₗ[ℂ] (⨁ _ : I, E) := DFinsupp.mapRange.linearMap (fun _ ↦ P.subtype)
  have hD : IsInducing D := locallyConvexSum_submodule_isInducing (fun _ : I ↦ P)
  have hDi : Injective D := by
    intro x y h
    exact DFinsupp.ext fun j ↦ Subtype.ext (congrArg (fun z : ⨁ _ : I, E ↦ z j) h)
  have he : eE.toLinearMap.comp T = D.comp eP.toLinearMap := by
    apply TensorProduct.ext'
    intro x v
    ext j
    change eE (TensorProduct.map P.subtype (LinearMap.id : V →ₗ[ℂ] V) (x ⊗ₜ[ℂ] v)) j =
      ((eP (x ⊗ₜ[ℂ] v)) j : E)
    rw [TensorProduct.map_tmul, LinearMap.id_apply]
    change inductiveTensorBasisEquiv b (x.val ⊗ₜ[ℂ] v) j =
      ((inductiveTensorBasisEquiv b (x ⊗ₜ[ℂ] v) j : P) : E)
    rw [inductiveTensorBasisEquiv_tmul_apply, inductiveTensorBasisEquiv_tmul_apply]
    rfl
  have hEq : (eE.symm : (⨁ _ : I, E) → E ⊗[ℂ] V) ∘ D ∘ eP = T := by
    funext t
    change eE.symm (D (eP t)) = T t
    exact eE.symm_apply_eq.mpr (LinearMap.congr_fun he t).symm
  refine ⟨?_, ?_⟩
  · rw [← hEq]
    exact eE.symm.toHomeomorph.isInducing.comp (hD.comp eP.toHomeomorph.isInducing)
  · rw [← hEq]
    exact eE.symm.injective.comp (hDi.comp eP.injective)

end

end Masullo
