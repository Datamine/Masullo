import IntegralBilinearForms

open Filter Function Set Topology
open scoped ComplexOrder PointwiseConvergenceCLM

namespace Masullo

noncomputable section

variable {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]

theorem equicontinuousDualSet_closedAbsConvexHull
    {S : Set (E →Lₚₜ[ℂ] ℂ)} (hS : EquicontinuousDualSet S) :
    EquicontinuousDualSet (closedAbsConvexHull ℂ S) := by
  intro ε hε
  filter_upwards [hS ε hε] with x hx
  let a := PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) ℂ x
  let p := (normSeminorm ℂ ℂ).comp a.toLinearMap
  have hsub : S ⊆ p.closedBall 0 ε := fun φ hφ => p.mem_closedBall_zero.mpr (hx φ hφ)
  have hc : IsClosed (p.closedBall 0 ε) := by
    rw [Seminorm.closedBall_zero_eq]
    exact isClosed_le a.continuous.norm continuous_const
  intro φ hφ
  exact p.mem_closedBall_zero.mp
    (closedAbsConvexHull_min hsub ⟨p.balanced_closedBall_zero _,
      convex_of_nonneg_surjective_algebraMap _ (fun _ => RCLike.nonneg_iff_exists_ofReal.mp)
        (p.convex_closedBall _ _)⟩ hc hφ)

/-- The weak closure of an equicontinuous set is compact. -/
theorem equicontinuousDualSet_isCompact_closure [IsTopologicalAddGroup E] [ContinuousSMul ℂ E]
    {S : Set (E →Lₚₜ[ℂ] ℂ)} (hS : EquicontinuousDualSet S) :
    IsCompact (closure S) := by
  let toFunction : (E →Lₚₜ[ℂ] ℂ) → (E → ℂ) := fun φ => φ
  have hemb : IsEmbedding toFunction :=
    PointwiseConvergenceCLM.isEmbedding_coeFn (RingHom.id ℂ) E ℂ
  let K := closure (toFunction '' S)
  have hbound (x : E) : ∃ R : ℝ, ∀ φ ∈ S, ‖φ x‖ ≤ R := by
    have ht : Tendsto (fun c : ℂ => c • x) (𝓝[≠] 0) (𝓝 0) :=
      (tendsto_id.zero_smul_const x).mono_left nhdsWithin_le_nhds
    obtain ⟨c, hc, hc₀⟩ := ((ht.eventually (hS 1 zero_lt_one)).and self_mem_nhdsWithin).exists
    have hpos : 0 < ‖c‖ := norm_pos_iff.mpr hc₀
    refine ⟨‖c‖⁻¹, fun φ hφ => ?_⟩
    have hh : ‖c‖ * ‖φ x‖ ≤ 1 := by simpa only [map_smul, norm_smul] using hc φ hφ
    simpa only [mul_one] using (le_inv_mul_iff₀ hpos).mpr hh
  choose R hR using hbound
  have hcompact : IsCompact K := by
    have hC : IsCompact (pi univ fun x : E => Metric.closedBall (0 : ℂ) (R x)) :=
      isCompact_univ_pi fun _ => isCompact_closedBall _ _
    refine hC.of_isClosed_subset isClosed_closure (hC.isClosed.closure_subset_iff.mpr ?_)
    rintro _ ⟨φ, hφ, rfl⟩ x _
    exact Metric.mem_closedBall.mpr (by simpa only [dist_zero_right] using hR x φ hφ)
  have hb (f : E → ℂ) (hf : f ∈ K) {ε : ℝ} {x : E}
      (hx : ∀ φ ∈ S, ‖φ x‖ ≤ ε) : ‖f x‖ ≤ ε := by
    have hsub : toFunction '' S ⊆ {g | ‖g x‖ ≤ ε} := by
      rintro _ ⟨φ, hφ, rfl⟩
      exact hx φ hφ
    exact (isClosed_le (continuous_apply x).norm continuous_const).closure_subset_iff.mpr hsub hf
  have hrange : K ⊆ range toFunction := by
    intro f hf
    have hadd (x y : E) : f (x + y) = f x + f y := by
      have hsub : toFunction '' S ⊆ {g | g (x + y) = g x + g y} := by
        rintro _ ⟨φ, _, rfl⟩
        exact φ.map_add x y
      exact (isClosed_eq (continuous_apply (x + y)) ((continuous_apply x).add (continuous_apply y)))
        |>.closure_subset_iff.mpr hsub <| hf
    have hsmul (c : ℂ) (x : E) : f (c • x) = c • f x := by
      have hsub : toFunction '' S ⊆ {g | g (c • x) = c • g x} := by
        rintro _ ⟨φ, _, rfl⟩
        exact φ.map_smul c x
      have hc : Continuous (fun g : E → ℂ => c • g x) := continuous_const.mul (continuous_apply x)
      exact (isClosed_eq (continuous_apply (c • x)) hc)
        |>.closure_subset_iff.mpr hsub <| hf
    let L : E →ₗ[ℂ] ℂ := ⟨⟨f, hadd⟩, hsmul⟩
    have hc : Continuous L := by
      refine continuous_of_tendsto_nhds_zero (G := E) (M := ℂ) L.toAddMonoidHom ?_
      rw [Metric.tendsto_nhds]
      intro ε hε
      filter_upwards [hS (ε / 2) (half_pos hε)] with x hx
      change dist (f x) 0 < ε
      rw [dist_zero_right]
      exact (hb f hf hx).trans_lt (half_lt_self hε)
    exact ⟨⟨L, hc⟩, rfl⟩
  apply hemb.isInducing.isCompact_iff.mpr
  rw [hemb.isInducing.closure_eq_preimage_closure_image, image_preimage_eq_inter_range,
    inter_eq_left.mpr hrange]
  exact hcompact

/-- Weakly closed absolutely convex equicontinuous sets are cofinal among
the tests for the injective tensor topology. -/
theorem injectiveDualTest_compactology_cofinal [PolynormableSpace ℂ E] (S : InjectiveDualTest E) :
    ∃ T : InjectiveDualTest E, S.forms ⊆ T.forms ∧ AbsConvex ℂ T.forms ∧ IsClosed T.forms := by
  let hW := PolynormableSpace.withSeminorms ℂ E
  letI : IsTopologicalAddGroup E := hW.topologicalAddGroup
  letI : ContinuousSMul ℂ E := hW.continuousSMul
  let T := closedAbsConvexHull ℂ S.forms
  have hT : IsClosed T := isClosed_closedAbsConvexHull
  have he : EquicontinuousDualSet T := equicontinuousDualSet_closedAbsConvexHull S.equicontinuous
  have hc : IsCompact T := hT.closure_eq ▸ equicontinuousDualSet_isCompact_closure he
  exact ⟨⟨T, hc, he⟩, subset_closedAbsConvexHull, absConvex_convexClosedHull, hT⟩

end

end Masullo
