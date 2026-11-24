import FinestStrongDual
import Mathlib.Analysis.LocallyConvex.WeakDual

open Bornology Filter Function Module Set Topology

namespace Masullo

noncomputable section

variable {I E : Type*} [AddCommGroup E] [Module ℂ E]

set_option backward.isDefEq.respectTransparency false in
/-- The canonical evaluation map into the actual strong bidual is a
continuous linear isomorphism for the finest locally convex topology. -/
def finest_strongBidual (b : Basis I ℂ E) :
    letI : TopologicalSpace E := finestLocallyConvexTopology E
    E ≃L[ℂ] StrongDual ℂ (StrongDual ℂ E) := by
  letI : TopologicalSpace E := finestLocallyConvexTopology E
  let W := finest_withSeminorms E
  letI : IsTopologicalAddGroup E := W.topologicalAddGroup
  letI : ContinuousSMul ℂ E := W.continuousSMul
  letI : PolynormableSpace ℂ E := W.toPolynormableSpace
  let D := StrongDual ℂ E
  let Ds := (inferInstance : TopologicalSpace D)
  let Dw := (inferInstance : TopologicalSpace (E →Lₚₜ[ℂ] ℂ))
  have ht : Ds = Dw := finest_strong_weak_topology_eq b
  let eval : E →ₗ[ℂ] StrongDual ℂ D :=
    { toFun := fun x => ⟨
        { toFun := fun ℓ => ℓ x
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
        , continuous_eval_const x⟩
      map_add' := fun x y => ContinuousLinearMap.ext fun ℓ => ℓ.map_add x y
      map_smul' := fun c x => ContinuousLinearMap.ext fun ℓ => ℓ.map_smul c x }
  have hinj : Injective eval := by
    intro x y he
    apply b.repr.injective
    ext i
    let f : D := ⟨b.coord i, finest_linear_continuous (b.coord i)⟩
    exact congrArg (fun u : StrongDual ℂ D => u f) he
  have hsurj : Surjective eval := by
    intro f
    have hweak : Continuous[Dw, inferInstance] (f : D → ℂ) := by
      rw [← ht]
      exact f.continuous
    let g : StrongDual ℂ (E →Lₚₜ[ℂ] ℂ) := ⟨f.toLinearMap, hweak⟩
    let p := PointwiseConvergenceCLM.equivWeakDual ℂ E
    let g' : StrongDual ℂ (WeakDual ℂ E) := g.comp p.symm.toContinuousLinearMap
    obtain ⟨x, hx⟩ := LinearMap.dualEmbedding_surjective (topDualPairing ℂ E) g'
    refine ⟨x, ContinuousLinearMap.ext fun l => ?_⟩
    let l' : E →Lₚₜ[ℂ] ℂ := l
    have h := congrArg (fun L : StrongDual ℂ (WeakDual ℂ E) => L (p l')) hx
    change l x = g (p.symm (p l')) at h
    rw [p.symm_apply_apply] at h
    exact h
  let e := LinearEquiv.ofBijective eval ⟨hinj, hsurj⟩
  refine ⟨e, ?_, ?_⟩
  · change Continuous (eval : E → StrongDual ℂ D)
    let hg : IsTopologicalAddGroup (StrongDual ℂ D) :=
      ContinuousLinearMap.topologicalAddGroup (σ := RingHom.id ℂ)
    letI : ContinuousAdd (StrongDual ℂ D) :=
      @IsTopologicalAddGroup.toContinuousAdd (StrongDual ℂ D) _ _ hg
    refine continuous_of_tendsto_nhds_zero (G := E) (M := StrongDual ℂ D) eval.toAddMonoidHom ?_
    rw [ContinuousLinearMap.hasBasis_nhds_zero.tendsto_right_iff]
    rintro ⟨K, V⟩ ⟨hK, hV⟩
    obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp hV
    let q (ℓ : K) := (normSeminorm ℂ ℂ).comp ℓ.val.toLinearMap
    have hq : BddAbove (range q) := by
      apply Seminorm.bddAbove_range_iff.mpr
      intro x
      have h := ContinuousLinearMap.isVonNBounded_iff.mp hK {x}
        (isVonNBounded_singleton (𝕜 := ℂ) x)
      obtain ⟨R, hR⟩ := (NormedSpace.isVonNBounded_iff' ℂ).mp h
      refine ⟨R, ?_⟩
      rintro _ ⟨ℓ, rfl⟩
      exact hR _ ⟨ℓ.val, ℓ.property, x, mem_singleton x, rfl⟩
    let p := ⨆ ℓ : K, q ℓ
    have hp := W.continuous_seminorm p
    filter_upwards [(hp.tendsto' 0 0 (map_zero p)).eventually (Iio_mem_nhds hε)] with x hx ℓ hℓ
    apply hsub
    rw [Metric.mem_ball, dist_zero_right]
    exact (show ‖ℓ x‖ ≤ p x from (le_ciSup hq (⟨ℓ, hℓ⟩ : K)) x).trans_lt hx
  · change Continuous (e.symm.toLinearMap : StrongDual ℂ D → E)
    apply (@WithSeminorms.continuous_iff_continuous_comp ℂ ℂ (StrongDual ℂ D) E _
      _ _ _ _ _ _ (RingHom.id ℂ) _ _ _ _ _ W e.symm.toLinearMap).mpr
    intro q
    let K : Set D := {ℓ | ∀ x, ‖ℓ x‖ ≤ q x}
    have hK : IsVonNBounded ℂ K := by
      apply ContinuousLinearMap.isVonNBounded_iff.mpr
      intro B hB
      obtain ⟨R, _, hR⟩ := W.isVonNBounded_iff_seminorm_bounded.mp hB q
      apply (NormedSpace.isVonNBounded_iff' ℂ).mpr
      refine ⟨R, ?_⟩
      rintro _ ⟨ℓ, hℓ, x, hx, rfl⟩
      exact (hℓ x).trans (hR x hx).le
    have hB : {f : StrongDual ℂ D | ∀ ℓ ∈ K, f ℓ ∈ Metric.ball (0 : ℂ) 1} ∈ 𝓝 0 :=
      ContinuousLinearMap.hasBasis_nhds_zero.mem_of_mem (i := (K, Metric.ball 0 1))
        ⟨hK, Metric.ball_mem_nhds _ zero_lt_one⟩
    apply Seminorm.continuous (r := 1)
    filter_upwards [hB] with f hf
    rw [Seminorm.mem_ball_zero]
    change q (e.symm f) < 1
    obtain ⟨ℓ, hℓ, hdom⟩ := seminorm_support q (W.continuous_seminorm q) (e.symm f)
    have hval : ℓ (e.symm f) = f ℓ :=
      congrArg (fun L : StrongDual ℂ D => L ℓ) (e.apply_symm_apply f)
    rw [← hℓ, hval]
    simpa only [Metric.mem_ball, dist_zero_right] using hf ℓ hdom

@[simp] theorem finest_strongBidual_apply (b : Basis I ℂ E) (x : E) :
    letI : TopologicalSpace E := finestLocallyConvexTopology E
    ∀ ℓ : StrongDual ℂ E, finest_strongBidual b x ℓ = ℓ x := by
  intro ℓ
  rfl

end
end Masullo
