import WeakDifferentiability
import Mathlib.Analysis.Calculus.ContDiff.Basic

open Filter Function Set Topology Bornology

namespace Masullo

section Removable

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedSpace 𝕜 ℂ]
  [AddCommGroup E] [Module ℂ E] [Module ℝ E] [IsScalarTower ℝ ℂ E]
  [UniformSpace E] [IsUniformAddGroup E] [T2Space E] [ContinuousSMul ℂ E]
  [PolynormableSpace ℂ E] [QuasiCompleteSpace ℂ E]

omit [IsUniformAddGroup E] [T2Space E] [ContinuousSMul ℂ E] [QuasiCompleteSpace ℂ E] in
private theorem bounded_scalarExtension_slopes {K : Set 𝕜} (hK : IsCompact K)
    (hconv : Convex ℝ K) (f : 𝕜 → E) (S : Set 𝕜) (hS : S ⊆ K)
    (u d : StrongDual ℂ E → 𝕜 → ℂ)
    (hu : ∀ ℓ, EqOn (fun z => ℓ (f z)) (u ℓ) S)
    (hd : ∀ ℓ, ∀ t ∈ K, HasDerivAt (u ℓ) (d ℓ t) t)
    (hc : ∀ ℓ, ContinuousOn (d ℓ) K) :
    IsVonNBounded ℂ {w : E | ∃ x ∈ S, ∃ y ∈ S, w = ‖y - x‖⁻¹ • (f y - f x)} := by
  apply (isVonNBounded_iff_dual_images _).mpr
  intro ℓ
  obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.mp (hK.image_of_continuousOn (hc ℓ)).isBounded
  let C := max M 0
  have hC : 0 ≤ C := le_max_right _ _
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨C, ?_⟩
  rintro z ⟨_, ⟨x, hx, y, hy, rfl⟩, rfl⟩
  have hdiff : ‖u ℓ y - u ℓ x‖ ≤ C * ‖y - x‖ := hconv.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t ht => (hd ℓ t ht).hasDerivWithinAt)
    (fun t ht => (hM _ (mem_image_of_mem _ ht)).trans (le_max_left _ _)) (hS hx) (hS hy)
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ), map_smul, map_sub, norm_smul, RCLike.norm_ofReal,
    abs_of_nonneg (by positivity)]
  rw [show ℓ (f y) = u ℓ y from hu ℓ hy, show ℓ (f x) = u ℓ x from hu ℓ hx]
  by_cases he : y - x = 0
  · simpa [he] using hC
  · exact (mul_le_mul_of_nonneg_left hdiff (by positivity)).trans_eq (by
      rw [mul_comm C, ← mul_assoc, inv_mul_cancel₀ (norm_ne_zero_iff.mpr he), one_mul])

omit [NormedSpace 𝕜 ℂ] [T2Space E] [ContinuousSMul ℂ E] [QuasiCompleteSpace ℂ E] in
theorem cauchy_map_of_local_bounded_slopes (f : 𝕜 → E) (x : 𝕜) {r : ℝ} (hr : 0 < r)
    (hR : IsVonNBounded ℂ
      {w : E | ∃ a ∈ Metric.closedBall x r \ {x}, ∃ b ∈ Metric.closedBall x r \ {x},
        w = ‖b - a‖⁻¹ • (f b - f a)}) :
    Cauchy ((𝓝[≠] x).map f) := by
  rw [cauchy_map_iff', uniformity_eq_comap_nhds_zero E, tendsto_comap_iff]
  let hP := PolynormableSpace.withSeminorms ℂ E
  change Tendsto (fun p : 𝕜 × 𝕜 => f p.2 - f p.1) ((𝓝[≠] x) ×ˢ (𝓝[≠] x)) (𝓝 0)
  apply (hP.tendsto_nhds _ _).mpr
  intro p ε hε
  obtain ⟨M, hM, hb⟩ := hP.isVonNBounded_iff_seminorm_bounded.mp hR p
  let δ := min r (ε / (2 * M))
  have hδ : 0 < δ := lt_min hr (div_pos hε (by positivity))
  have hsmall : ∀ᶠ y in 𝓝[≠] x, y ∈ Metric.ball x δ ∧ y ≠ x := by
    have he : ∀ᶠ y in 𝓝[≠] x, y ∈ Metric.ball x δ :=
      mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds x hδ)
    exact he.and self_mem_nhdsWithin
  have hpair := hsmall.prod_mk hsmall
  filter_upwards [hpair] with y hy
  obtain ⟨⟨hyn, hyne⟩, ⟨hzn, hzne⟩⟩ := hy
  have hY : y.1 ∈ Metric.closedBall x r \ {x} :=
    ⟨Metric.ball_subset_closedBall (Metric.ball_subset_ball (min_le_left _ _) hyn), hyne⟩
  have hZ : y.2 ∈ Metric.closedBall x r \ {x} :=
    ⟨Metric.ball_subset_closedBall (Metric.ball_subset_ball (min_le_left _ _) hzn), hzne⟩
  rw [sub_zero]
  by_cases h : y.2 = y.1
  · simp [h, hε]
  have hn : ‖y.2 - y.1‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr h)
  have hB := hb _ ⟨y.1, hY, y.2, hZ, rfl⟩
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ), map_smul_eq_mul, RCLike.norm_ofReal,
    abs_of_nonneg (by positivity)] at hB
  have hm := mul_le_mul_of_nonneg_left hB.le (norm_nonneg (y.2 - y.1))
  rw [← mul_assoc, mul_inv_cancel₀ hn, one_mul, mul_comm ‖y.2 - y.1‖] at hm
  have hy' : dist y.1 x < ε / (2 * M) :=
    (Metric.mem_ball.mp hyn).trans_le (min_le_right _ _)
  have hz' : dist y.2 x < ε / (2 * M) :=
    (Metric.mem_ball.mp hzn).trans_le (min_le_right _ _)
  have hs : ‖y.2 - y.1‖ < ε / M := by
    rw [← dist_eq_norm]
    have htri := dist_triangle_right y.2 y.1 x
    calc
      _ ≤ dist y.2 x + dist y.1 x := htri
      _ < ε / (2 * M) + ε / (2 * M) := add_lt_add hz' hy'
      _ = _ := by field_simp; ring
  exact hm.trans_lt (by simpa [mul_div_cancel₀ _ hM.ne'] using mul_lt_mul_of_pos_left hs hM)

variable [SMulCommClass ℂ 𝕜 ℂ] [IsScalarTower 𝕜 ℂ ℂ]
  [weakModule : Module 𝕜 (WeakAlgebraicBidual E)]
  [weakTower : @IsScalarTower 𝕜 ℂ (WeakAlgebraicBidual E)
    (inferInstance : SMul 𝕜 ℂ) (inferInstance : SMul ℂ (WeakAlgebraicBidual E))
    weakModule.toDistribMulAction.toDistribSMul.toSMul]

/-- Lemma C.5.1.22. A puncture is removable when every continuous scalar
evaluation extends with a continuous derivative. The continuous extension
is unique on the open domain and agrees with each scalar extension. -/
theorem removable_weak_singularity {U : Set 𝕜} (hU : IsOpen U) {x : 𝕜} (hx : x ∈ U)
    (f : 𝕜 → E) (u d : StrongDual ℂ E → 𝕜 → ℂ)
    (hu : ∀ ℓ, EqOn (fun z => ℓ (f z)) (u ℓ) (U \ {x}))
    (hd : ∀ ℓ, ∀ t ∈ U, HasDerivAt (u ℓ) (d ℓ t) t)
    (hc : ∀ ℓ, ContinuousOn (d ℓ) U) :
    ∃ F : 𝕜 → E, ContinuousOn F U ∧ EqOn F f (U \ {x}) ∧
      (∀ ℓ, EqOn (fun z => ℓ (F z)) (u ℓ) U) ∧
      (∀ ℓ, ContinuousOn (d ℓ) U ∧ ∀ t ∈ U, HasDerivAt (fun z => ℓ (F z)) (d ℓ t) t) ∧
      (∃ B : 𝕜 → 𝕜 →L[𝕜] WeakAlgebraicBidual E,
        (∀ t ∈ U, HasFDerivAt (fun y => weakBidualEval E (F y)) (B t) t) ∧
        ContinuousOn (fun p : 𝕜 × 𝕜 => B p.1 p.2) (U ×ˢ univ)) ∧
      ∀ G : 𝕜 → E, ContinuousOn G U → EqOn G f (U \ {x}) → EqOn G F U := by
  obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hx)
  let K := Metric.closedBall x r
  let S := K \ {x}
  have hS : S ⊆ U \ {x} := sdiff_subset_sdiff_left hball
  have hKs : IsCompact K := isCompact_closedBall _ _
  have hR := bounded_scalarExtension_slopes hKs (convex_closedBall x r) f S sdiff_subset u d
    (fun ℓ => (hu ℓ).mono hS) (fun ℓ t ht => hd ℓ t (hball ht)) (fun ℓ => (hc ℓ).mono hball)
  have hC := cauchy_map_of_local_bounded_slopes f x hr hR
  let C := closure (f '' S)
  have hbound : IsVonNBounded ℂ (f '' S) := by
    apply (isVonNBounded_iff_dual_images _).mpr
    intro ℓ
    have hc' : ContinuousOn (u ℓ) K := fun t ht => (hd ℓ t (hball ht)).continuousAt.continuousWithinAt
    apply (hKs.image_of_continuousOn hc').isBounded.subset
    rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨y, hy.1, (hu ℓ (hS hy)).symm⟩
  have heS : ∀ᶠ z in 𝓝[≠] x, z ∈ S := by
    have hk : ∀ᶠ z in 𝓝[≠] x, z ∈ K :=
      mem_nhdsWithin_of_mem_nhds (Metric.closedBall_mem_nhds _ hr)
    exact hk.and self_mem_nhdsWithin
  have hcomplete : IsComplete C := QuasiCompleteSpace.quasiComplete hbound.closure isClosed_closure
  obtain ⟨L, _, hL⟩ := hcomplete _ hC
    (le_principal_iff.mpr (heS.mono fun y hy => subset_closure (mem_image_of_mem f hy)))
  classical
  let F := Function.update f x L
  have hagree : EqOn F f (U \ {x}) := fun t ht => Function.update_of_ne ht.2 _ _
  have heU : ∀ᶠ z in 𝓝[≠] x, z ∈ U \ {x} := heS.mono fun _ hz => hS hz
  have hfL : Tendsto f (𝓝[≠] x) (𝓝 L) := hL
  have hF : Tendsto F (𝓝[≠] x) (𝓝 L) :=
    hfL.congr' (heU.mono fun t ht => (hagree ht).symm)
  have hFata : ContinuousAt F x := by
    rw [ContinuousAt, ← nhdsNE_sup_pure x, tendsto_sup]
    refine ⟨?_, ?_⟩
    · simpa [F] using hF
    · rw [tendsto_pure_left]
      simpa [F] using fun _ hs => mem_of_mem_nhds hs
  have huF (ℓ : StrongDual ℂ E) : EqOn (fun z => ℓ (F z)) (u ℓ) U := by
    intro y hy
    by_cases h : y = x
    · subst y
      have huLim : Tendsto (u ℓ) (𝓝[≠] x) (𝓝 (u ℓ x)) := (hd ℓ x hx).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      have htest := (ℓ.continuous.continuousAt.tendsto.comp hF)
      have heq : (fun z => u ℓ z) =ᶠ[𝓝[≠] x] (fun z => ℓ (F z)) := by
        filter_upwards [heU] with z hz
        rw [hagree hz]
        exact (show ℓ (f z) = u ℓ z from hu ℓ hz).symm
      have hlim := huLim.congr' heq
      have hh := tendsto_nhds_unique htest hlim
      simpa [F] using hh
    · change ℓ (F y) = u ℓ y
      rw [hagree ⟨hy, h⟩]
      exact hu ℓ ⟨hy, h⟩
  have hDer (ℓ : StrongDual ℂ E) (y : 𝕜) (hy : y ∈ U) :
      HasDerivAt (fun z => ℓ (F z)) (d ℓ y) y :=
    (hd ℓ y hy).congr_of_eventuallyEq ((eventually_mem_set.mpr (hU.mem_nhds hy)).mono fun z hz => huF ℓ hz)
  have hCont : ContinuousOn F U := by
    apply continuousOn_of_continuous_weakDifferential hU F
      (fun ℓ t => (ContinuousLinearMap.id 𝕜 𝕜).smulRight (d ℓ t))
    · exact fun ℓ t ht => (hDer ℓ t ht).hasFDerivAt
    · intro ℓ
      exact continuous_snd.continuousOn.smul ((hc ℓ).comp continuous_fst.continuousOn (fun _ hp => hp.1))
  refine ⟨F, hCont, hagree, huF, fun ℓ => ⟨hc ℓ, hDer ℓ⟩,
    @continuousWeakDifferential_of_scalar_continuousDerivatives 𝕜 E _ _ _ _ _ _
      weakModule weakTower _ U F d hDer hc, ?_⟩
  intro G hG hGf y hy
  by_cases h : y = x
  · subst y
    have hGlim : Tendsto G (𝓝[≠] x) (𝓝 (G x)) :=
      (hG.continuousAt (hU.mem_nhds hx)).tendsto.mono_left nhdsWithin_le_nhds
    have heq : G =ᶠ[𝓝[≠] x] F := heU.mono fun z hz => (hGf hz).trans (hagree hz).symm
    exact tendsto_nhds_unique (hGlim.congr' heq) (hFata.tendsto.mono_left nhdsWithin_le_nhds)
  · exact (hGf ⟨hy,h⟩).trans (hagree ⟨hy,h⟩).symm

end Removable

end Masullo
