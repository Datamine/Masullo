import FinestNuclear
import Mathlib.Topology.Metrizable.Basic

open Bornology Filter Function Module Set Topology
open scoped TensorProduct

namespace Masullo

noncomputable section

variable {E I : Type*} [AddCommGroup E] [Module ℂ E]

private def basisStrongDualEquiv (b : Basis I ℂ E) :
    letI : TopologicalSpace E := finestLocallyConvexTopology E
    (I → ℂ) ≃ₗ[ℂ] StrongDual ℂ E := by
  letI : TopologicalSpace E := finestLocallyConvexTopology E
  let L : (I → ℂ) →ₗ[ℂ] StrongDual ℂ E :=
    { toFun := fun c => ⟨b.constr ℂ c, finest_linear_continuous _⟩
      map_add' := fun f g => ContinuousLinearMap.ext fun x =>
        DFunLike.congr_fun (map_add (b.constr ℂ) f g) x
      map_smul' := fun a f => ContinuousLinearMap.ext fun x =>
        DFunLike.congr_fun (map_smul (b.constr ℂ) a f) x }
  exact LinearEquiv.ofBijective L ⟨fun f g he => (b.constr ℂ).injective
    (congrArg ContinuousLinearMap.toLinearMap he), fun l => ⟨(b.constr ℂ).symm l.toLinearMap,
      ContinuousLinearMap.ext fun x => DFunLike.congr_fun ((b.constr ℂ).apply_symm_apply _) x⟩⟩

private theorem basisStrongDualEquiv_apply (b : Basis I ℂ E) (c : I → ℂ) (x : E) :
    basisStrongDualEquiv b c x = ∑ i ∈ (b.repr x).support, b.repr x i * c i :=
  b.constr_apply ℂ c x

private theorem continuous_basisStrongDualEquiv (b : Basis I ℂ E) :
    Continuous (basisStrongDualEquiv b) := by
  classical
  letI : TopologicalSpace E := finestLocallyConvexTopology E
  let W := finest_withSeminorms E
  letI : IsTopologicalAddGroup E := W.topologicalAddGroup
  letI : ContinuousSMul ℂ E := W.continuousSMul
  let L := (basisStrongDualEquiv b).toLinearMap.toAddMonoidHom
  refine continuous_of_tendsto_nhds_zero L ?_
  rw [ContinuousLinearMap.hasBasis_nhds_zero.tendsto_right_iff]
  rintro ⟨B, V⟩ ⟨hB, hV⟩
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hV
  letI : TopologicalSpace (I →₀ ℂ) := finestLocallyConvexTopology _
  letI : PolynormableSpace ℂ (I →₀ ℂ) := (finest_withSeminorms _).toPolynormableSpace
  let L₀ : E →L[ℂ] (I →₀ ℂ) := ⟨b.repr.toLinearMap, finest_linear_continuous _⟩
  let S : Set I := {i | ∃ x ∈ B, b.repr x i ≠ 0}
  have hS : S.Finite := by
    letI : TopologicalSpace (I →₀ ℂ) := finestLocallyConvexTopology _
    have hh := finest_finsupp_bounded_support (hB.image L₀)
    exact hh.subset (fun i ⟨x, hx, hxi⟩ => ⟨L₀ x, mem_image_of_mem L₀ hx, hxi⟩)
  let t := hS.toFinset
  let p := (weightedLoneSeminorm (fun _ : I => 1)).comp b.repr.toLinearMap
  obtain ⟨R, hR, hbound⟩ := W.isVonNBounded_iff_seminorm_bounded.mp hB p
  have hδ : 0 < ε / R := div_pos hε hR
  have ht (i : I) : ∀ᶠ c : I → ℂ in 𝓝 0, ‖c i‖ < ε / R := by
    have h := ((continuous_apply i).norm.tendsto' (0 : I → ℂ) 0 (by simp)).eventually
      (Iio_mem_nhds hδ)
    exact h
  filter_upwards [t.eventually_all.mpr fun i _ => ht i] with c hc x hx
  apply hball
  rw [Metric.mem_ball, dist_zero_right]
  change ‖basisStrongDualEquiv b c x‖ < ε
  rw [basisStrongDualEquiv_apply]
  have hs : (b.repr x).support ⊆ t := fun i hi =>
    hS.mem_toFinset.mpr ⟨x, hx, Finsupp.mem_support_iff.mp hi⟩
  calc
    ‖∑ i ∈ (b.repr x).support, b.repr x i * c i‖ ≤
        ∑ i ∈ (b.repr x).support, ‖b.repr x i * c i‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ (b.repr x).support, ‖b.repr x i‖ * (ε / R) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hc i (hs hi)).le (norm_nonneg _)
    _ = p x * (ε / R) := by
      change _ = ‖weightedLone (fun _ : I => 1) (b.repr x)‖ * (ε / R)
      rw [weightedLone_norm, Finset.sum_mul]
      simp
    _ < R * (ε / R) := mul_lt_mul_of_pos_right (hbound x hx) hδ
    _ = ε := by field_simp [hR.ne']

/-- The strong dual of a finest locally convex space is the product of its
scalar basis coordinates, equipped with the actual product topology. -/
def finest_strongDual_product (b : Basis I ℂ E) :
    letI : TopologicalSpace E := finestLocallyConvexTopology E
    (I → ℂ) ≃L[ℂ] StrongDual ℂ E := by
  letI : TopologicalSpace E := finestLocallyConvexTopology E
  refine ⟨basisStrongDualEquiv b, continuous_basisStrongDualEquiv b, ?_⟩
  apply continuous_pi
  intro i
  have he (f : StrongDual ℂ E) : (basisStrongDualEquiv b).symm f i = f (b i) := by
    have h := congrArg (fun l : StrongDual ℂ E => l (b i))
      ((basisStrongDualEquiv b).apply_symm_apply f)
    change b.constr ℂ ((basisStrongDualEquiv b).symm f) (b i) = f (b i) at h
    rwa [b.constr_basis] at h
  change Continuous (fun f : StrongDual ℂ E => (basisStrongDualEquiv b).symm f i)
  simp only [he]
  exact continuous_eval_const (b i)

/-- The product coordinates give the values on the chosen basis. -/
theorem finest_strongDual_product_apply_basis (b : Basis I ℂ E) (c : I → ℂ) (i : I) :
    letI : TopologicalSpace E := finestLocallyConvexTopology E
    finest_strongDual_product b c (b i) = c i := by
  change b.constr ℂ c (b i) = c i
  exact b.constr_basis ℂ c i

/-- Bounded convergence and pointwise convergence induce the same topology
on the dual of a finest locally convex space. -/
theorem finest_strong_weak_topology_eq (b : Basis I ℂ E) :
    letI : TopologicalSpace E := finestLocallyConvexTopology E
    (inferInstance : TopologicalSpace (StrongDual ℂ E)) =
      (inferInstance : TopologicalSpace (E →Lₚₜ[ℂ] ℂ)) := by
  letI : TopologicalSpace E := finestLocallyConvexTopology E
  let W := finest_withSeminorms E
  letI : IsTopologicalAddGroup E := W.topologicalAddGroup
  letI : ContinuousSMul ℂ E := W.continuousSMul
  let τs := (inferInstance : TopologicalSpace (StrongDual ℂ E))
  let τw := (inferInstance : TopologicalSpace (E →Lₚₜ[ℂ] ℂ))
  have hc : Continuous[τs, τw] (id : StrongDual ℂ E → StrongDual ℂ E) :=
    (ContinuousLinearMap.toPointwiseConvergenceCLM (σ := RingHom.id ℂ) (E := E) (F := ℂ)).continuous
  have he (f : E →Lₚₜ[ℂ] ℂ) :
      basisStrongDualEquiv b (fun i => f (b i)) = f := by
    apply ContinuousLinearMap.ext
    intro x
    change b.constr ℂ (fun i => f (b i)) x = f x
    have h : b.constr ℂ (fun i => f (b i)) = f.toLinearMap :=
      b.ext fun i => b.constr_basis ℂ _ i
    exact DFunLike.congr_fun h x
  have hd : Continuous[τw, τs] (id : StrongDual ℂ E → StrongDual ℂ E) := by
    have hx : Continuous[τw, inferInstance] (fun (f : E →Lₚₜ[ℂ] ℂ) i => f (b i)) :=
      continuous_pi fun i => continuous_eval_const (b i)
    let D := StrongDual ℂ E
    let h (f : D) (i : I) := f (b i)
    have hf : (basisStrongDualEquiv b : (I → ℂ) → D) ∘ h = (id : D → D) := funext he
    have hh := @Continuous.comp D (I → ℂ) D τw inferInstance τs
      h (basisStrongDualEquiv b) (continuous_basisStrongDualEquiv b) hx
    rw [hf] at hh
    exact hh
  change τs = τw
  exact le_antisymm (continuous_id_iff_le.mp hc) (continuous_id_iff_le.mp hd)

theorem finest_strongDual_frechet (b : Basis I ℂ E) [Countable I] :
    letI : TopologicalSpace E := finestLocallyConvexTopology E
    CompleteSpace (StrongDual ℂ E) ∧ TopologicalSpace.MetrizableSpace (StrongDual ℂ E) := by
  letI : TopologicalSpace E := finestLocallyConvexTopology E
  let W := finest_withSeminorms E
  letI : IsTopologicalAddGroup E := W.topologicalAddGroup
  letI : ContinuousSMul ℂ E := W.continuousSMul
  let e := finest_strongDual_product b
  exact ⟨(e.isUniformEmbedding.isUniformInducing.completeSpace_congr e.surjective).mp inferInstance,
    e.symm.toHomeomorph.isEmbedding.metrizableSpace⟩

theorem finest_strongDual_nuclear (b : Basis I ℂ E) {F : Type*}
    [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] [PolynormableSpace ℂ F] :
    letI : TopologicalSpace E := finestLocallyConvexTopology E
    projectiveTensorTopology (StrongDual ℂ E) F = injectiveTensorTopology (StrongDual ℂ E) F := by
  letI : TopologicalSpace E := finestLocallyConvexTopology E
  let W := finest_withSeminorms E
  letI : IsTopologicalAddGroup E := W.topologicalAddGroup
  letI : ContinuousSMul ℂ E := W.continuousSMul
  let D := StrongDual ℂ E
  let t := (inferInstance : TopologicalSpace (E →Lₚₜ[ℂ] ℂ))
  have h : @projectiveTensorTopology D F _ _ t _ _ _ =
      @injectiveTensorTopology D F _ _ t _ _ _ :=
    weakDual_tensorTopologies_equal (E := E) (F := F)
  let s := (inferInstance : TopologicalSpace D)
  have ht : s = t := finest_strong_weak_topology_eq b
  change @projectiveTensorTopology D F _ _ s _ _ _ =
      @injectiveTensorTopology D F _ _ s _ _ _
  rw [ht]
  exact h

end
end Masullo
