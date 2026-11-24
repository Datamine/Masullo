import NuclearIntegralOperators
import NuclearFactorization

/-! # Precompactness and finite-rank approximation in nuclear spaces -/

open Bornology Filter Function Set Topology UniformSpace
open scoped CompactConvergenceCLM TensorProduct Uniformity UniformConvergenceCLM

namespace Masullo

noncomputable section

universe u

private theorem exists_continuousSeminorm_ball_subset {E : Type*}
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [PolynormableSpace ℂ E]
    {U : Set E} (hU : U ∈ 𝓝 0) :
    ∃ (q : Seminorm ℂ E) (r : ℝ), Continuous q ∧ 0 < r ∧ q.ball 0 r ⊆ U := by
  letI : IsTopologicalAddGroup E := (PolynormableSpace.withSeminorms ℂ E).topologicalAddGroup
  obtain ⟨⟨I, r⟩, hr, hsub⟩ :=
    (PolynormableSpace.withSeminorms ℂ E).hasBasis_zero_ball.mem_iff.mp hU
  exact ⟨_, r, Seminorm.continuous_finsetSup (fun i _ => i.property), hr, hsub⟩

private theorem exists_nuclearTransition {E : Type u}
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (hE : NuclearLocallyConvex.{u, u} E) (q : Seminorm ℂ E) (hq : Continuous q) :
    ∃ (p : Seminorm ℂ E) (_ : Continuous p) (hqp : q ≤ p),
      Nonempty (BanachNuclearExpansion (localBanachTransition q p hqp)) := by
  obtain ⟨p, hp, hqp, _, f, w, hsum, hT⟩ := nuclearLocallyConvex_exists_rankOneTransition hE q hq
  exact ⟨p, hp, hqp, BanachNuclearExpansion.nonempty_of_rankOne_hasSum f w hsum hT⟩

section Precompact

variable {E : Type u} [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E]

/-- Lemma C.2.4.16(1). Every bounded set in a nuclear space is totally
bounded, and hence has compact closure in its separated completion. -/
theorem nuclearLocallyConvex_totallyBounded (hE : NuclearLocallyConvex.{u, u} E)
    {S : Set E} (hS : IsVonNBounded ℂ S) : TotallyBounded S := by
  letI : PolynormableSpace ℂ E := hE.2.1
  apply totallyBounded_iff_subset.mpr
  intro U hU
  rw [uniformity_eq_comap_nhds_zero E] at hU
  obtain ⟨V, hV, hVU⟩ := Filter.mem_comap.mp hU
  obtain ⟨q, r, hq, hr, hqV⟩ := exists_continuousSeminorm_ball_subset hV
  obtain ⟨p, hp, hqp, ⟨R⟩⟩ := exists_nuclearTransition hE q hq
  let j := localBanachMap p hp
  let k := localBanachMap q hq
  let T := localBanachTransition q p hqp
  have hk (x : E) : T (j x) = k x := localBanachTransition_denseMap q p hqp x
  have hksi : k '' S = T '' (j '' S) := by
    rw [image_image]
    exact congrArg (fun f : E → LocalBanach q => f '' S) (funext fun x => (hk x).symm)
  have htb : TotallyBounded (k '' S) := by
    rw [hksi]
    exact (R.isCompactOperator.isCompact_closure_image_of_isVonNBounded (hS.image j)).totallyBounded.subset
      subset_closure
  obtain ⟨t, hts, ht, hcover⟩ := htb.exists_subset (Metric.dist_mem_uniformity hr)
  let a (y : ↥t) : E := (hts y.property).choose
  have ha (y : ↥t) : a y ∈ S ∧ k (a y) = y := (hts y.property).choose_spec
  let A := range a
  have hA : A.Finite := by
    letI : Finite ↥t := ht.to_subtype
    exact finite_range a
  refine ⟨A, ?_, hA, ?_⟩
  · rintro _ ⟨y, rfl⟩
    exact (ha y).1
  · intro x hx
    have H := hcover (mem_image_of_mem k hx)
    simp only [mem_iUnion, mem_ofPred_eq] at H ⊢
    obtain ⟨y, hy, hxy⟩ := H
    refine ⟨a ⟨y, hy⟩, mem_range_self _, hVU (hqV ?_)⟩
    have hdist : dist (k x) (k (a ⟨y, hy⟩)) < r := by
      rw [(ha ⟨y, hy⟩).2]
      exact hxy
    apply q.mem_ball_zero.mpr
    rw [← norm_localBanachDenseMap, map_sub]
    change dist (localBanachDenseMap q x) (localBanachDenseMap q (a ⟨y, hy⟩)) < r at hdist
    simpa only [dist_eq_norm, norm_sub_rev] using hdist

theorem nuclearLocallyConvex_compactClosure_completion (hE : NuclearLocallyConvex.{u, u} E)
    {S : Set E} (hS : IsVonNBounded ℂ S) :
    IsCompact (closure (((↑) : E → Completion E) '' S)) :=
  ((nuclearLocallyConvex_totallyBounded hE hS).image (Completion.uniformContinuous_coe E)).closure
    |>.isCompact_of_isClosed isClosed_closure

/-- The uniform convergence topologies on bounded and on precompact sets
agree for a nuclear source. -/
theorem nuclearLocallyConvex_boundedConvergence_eq (hE : NuclearLocallyConvex.{u, u} E)
    (F : Type*) [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] [IsTopologicalAddGroup F] :
    UniformConvergenceCLM.instTopologicalSpace (RingHom.id ℂ) F
        {S : Set E | IsVonNBounded ℂ S} =
      UniformConvergenceCLM.instTopologicalSpace (RingHom.id ℂ) F
        {S : Set E | TotallyBounded S} := by
  letI : PolynormableSpace ℂ E := hE.2.1
  letI : ContinuousSMul ℂ E := (PolynormableSpace.withSeminorms ℂ E).continuousSMul
  have he : {S : Set E | IsVonNBounded ℂ S} = {S : Set E | TotallyBounded S} := by
    ext S
    exact ⟨nuclearLocallyConvex_totallyBounded hE, TotallyBounded.isVonNBounded ℂ⟩
  rw [he]

end Precompact

section Approximation

variable {E : Type u} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℂ E]

/-- Finite-rank endomorphisms approximate the identity on an arbitrary
bounded set in every neighborhood of zero. -/
theorem nuclearLocallyConvex_approxOn_bounded (hE : NuclearLocallyConvex.{u, u} E)
    {S : Set E} (hS : IsVonNBounded ℂ S) {V : Set E} (hV : V ∈ 𝓝 0) :
    ∃ z : (E →L[ℂ] ℂ) ⊗[ℂ] E, ∀ x ∈ S, tensorOperator E E z x - x ∈ V := by
  letI : PolynormableSpace ℂ E := hE.2.1
  obtain ⟨q, r, hq, hr, hrV⟩ := exists_continuousSeminorm_ball_subset hV
  obtain ⟨p, hp, hqp, ⟨R⟩⟩ := exists_nuclearTransition hE q hq
  let j := localBanachMap p hp
  let k := localBanachMap q hq
  let T := localBanachTransition q p hqp
  have hk (x : E) : T (j x) = k x := localBanachTransition_denseMap q p hqp x
  have hev := R.uniform_on_bounded j (ContinuousLinearMap.id ℂ (LocalBanach q)) hS
    (Metric.ball_mem_nhds 0 (show 0 < r / 2 by positivity))
  obtain ⟨n, hn⟩ := hev.exists
  have htail (x : E) (hx : x ∈ S) : ‖R.partialSum n (j x) - k x‖ < r / 2 := by
    have h := hn x hx
    change R.partialSum n (j x) - T (j x) ∈ Metric.ball 0 (r / 2) at h
    simpa only [Metric.mem_ball, dist_zero_right, hk] using h
  obtain ⟨M, hM⟩ := (NormedSpace.isVonNBounded_iff' ℂ).mp (hS.image j)
  let A := 1 + |M|
  have hA : 0 < A := by dsimp [A]; positivity
  have hb (x : E) (hx : x ∈ S) : ‖j x‖ ≤ A :=
    (hM _ (mem_image_of_mem j hx)).trans
      ((le_abs_self M).trans (le_add_of_nonneg_left zero_le_one))
  let C := 1 + ∑ i ∈ Finset.range n, ‖R.coeff i‖
  have hC : 0 < C := by
    have hn0 : 0 ≤ ∑ i ∈ Finset.range n, ‖R.coeff i‖ :=
      Finset.sum_nonneg fun _ _ => norm_nonneg _
    change 0 < 1 + _
    linarith
  let δ := (r / 2) / (A * C)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  choose y hy using fun i => (Metric.denseRange_iff.mp (localBanachDenseMap_dense q))
    (R.vector i) δ hδ
  let f (i : ℕ) := (R.coeff i • R.functional i).comp j
  let z := ∑ i ∈ Finset.range n, f i ⊗ₜ[ℂ] y i
  refine ⟨z, fun x hx => hrV (q.mem_ball_zero.mpr ?_)⟩
  have he (x : E) : k (tensorOperator E E z x) - R.partialSum n (j x) =
      ∑ i ∈ Finset.range n, f i x • (k (y i) - R.vector i) := by
    simp only [z, map_sum, sum_apply, tensorOperator_tmul, map_smul,
      BanachNuclearExpansion.partialSum, smul_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.comp_apply, f, ← mul_smul, Finset.sum_sub_distrib, smul_sub, smul_eq_mul]
  have hlift : ‖k (tensorOperator E E z x) - R.partialSum n (j x)‖ ≤ r / 2 := by
    rw [he]
    calc
      _ ≤ ∑ i ∈ Finset.range n, ‖f i x • (k (y i) - R.vector i)‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ Finset.range n, ‖R.coeff i‖ * (A * δ) := by
        refine Finset.sum_le_sum fun i _ => ?_
        have hfi : ‖R.functional i (j x)‖ ≤ A :=
          ((R.functional i).le_of_opNorm_le (R.functional_bound i) _).trans (by simpa using hb x hx)
        have hyi : ‖k (y i) - R.vector i‖ ≤ δ := by
          have h := (hy i).le
          change dist (R.vector i) (k (y i)) ≤ δ at h
          rwa [dist_comm, dist_eq_norm] at h
        rw [norm_smul]
        change ‖R.coeff i * R.functional i (j x)‖ * _ ≤ _
        rw [norm_mul, mul_assoc]
        exact mul_le_mul_of_nonneg_left (mul_le_mul hfi hyi (norm_nonneg _) hA.le) (norm_nonneg _)
      _ ≤ C * (A * δ) := by
        rw [← Finset.sum_mul]
        exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) (by positivity)
      _ = r / 2 := by
        dsimp [δ]
        field_simp [hA.ne', hC.ne']
  rw [← norm_localBanachDenseMap]
  change ‖k (tensorOperator E E z x - x)‖ < r
  rw [map_sub]
  calc
    _ ≤ ‖k (tensorOperator E E z x) - R.partialSum n (j x)‖ +
        ‖R.partialSum n (j x) - k x‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < r := by linarith [htail x hx]

end Approximation

/-- Lemma C.2.4.16(2). The tensor-to-operator map has dense image in the
topology of precompact convergence when the source is nuclear. -/
theorem nuclearLocallyConvex_dense_finiteRank {E : Type u} {F : Type*}
    [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E] [ContinuousSMul ℂ E]
    [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul ℂ F]
    (hE : NuclearLocallyConvex.{u, u} E) :
    DenseRange (fun z : (E →L[ℂ] ℂ) ⊗[ℂ] F =>
      (show E →Lᵤ[ℂ, {S : Set E | TotallyBounded S}] F from tensorOperator E F z)) := by
  let 𝔖 := {S : Set E | TotallyBounded S}
  let M := E →Lᵤ[ℂ, 𝔖] F
  let L : ((E →L[ℂ] ℂ) ⊗[ℂ] F) → M := tensorOperator E F
  have hb := UniformConvergenceCLM.hasBasis_nhds_zero (RingHom.id ℂ) F 𝔖
    ⟨∅, totallyBounded_empty⟩
    (show DirectedOn (· ⊆ ·) 𝔖 from fun S hS V hV => ⟨S ∪ V, hS.union hV,
      subset_union_left, subset_union_right⟩)
  intro A
  change A ∈ closure (range L)
  have hbA := hb.map (A + ·)
  rw [map_add_left_nhds_zero A] at hbA
  apply (mem_closure_iff_nhds_basis hbA).mpr
  rintro ⟨S, V⟩ ⟨hS, hV⟩
  let a : E →L[ℂ] F := A
  have haV : a ⁻¹' V ∈ 𝓝 (0 : E) := a.continuous.tendsto' 0 0 (map_zero a) hV
  obtain ⟨z, hz⟩ :=
    nuclearLocallyConvex_approxOn_bounded hE (TotallyBounded.isVonNBounded ℂ hS) haV
  let Y := TensorProduct.map LinearMap.id a.toLinearMap z
  have hmap (t : (E →L[ℂ] ℂ) ⊗[ℂ] E) (x : E) :
      tensorOperator E F (TensorProduct.map LinearMap.id a.toLinearMap t) x =
        a (tensorOperator E E t x) := by
    induction t using TensorProduct.induction_on with
    | zero => simp only [map_zero, zero_apply]
    | tmul f y =>
      simp only [TensorProduct.map_tmul, LinearMap.id_apply, tensorOperator_tmul, map_smul]
      rfl
    | add s t hs ht =>
      rw [map_add, map_add, map_add]
      change tensorOperator E F (TensorProduct.map LinearMap.id a.toLinearMap s) x +
        tensorOperator E F (TensorProduct.map LinearMap.id a.toLinearMap t) x =
          a (tensorOperator E E s x + tensorOperator E E t x)
      rw [map_add, hs, ht]
  refine ⟨L Y, mem_range_self _, L Y - A, ?_, add_sub_cancel _ _⟩
  intro x hx
  change tensorOperator E F (TensorProduct.map LinearMap.id a.toLinearMap z) x - a x ∈ V
  rw [hmap, ← map_sub]
  exact hz x hx

/-- Remark C.2.4.17. The finite-rank maps are dense also for bounded convergence. -/
theorem nuclearLocallyConvex_dense_finiteRank_bounded {E : Type u} {F : Type*}
    [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E] [ContinuousSMul ℂ E]
    [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul ℂ F]
    (hE : NuclearLocallyConvex.{u, u} E) :
    DenseRange (fun z : (E →L[ℂ] ℂ) ⊗[ℂ] F =>
      (show E →Lᵤ[ℂ, {S : Set E | IsVonNBounded ℂ S}] F from tensorOperator E F z)) := by
  change @DenseRange _ (UniformConvergenceCLM.instTopologicalSpace (RingHom.id ℂ) F
    {S : Set E | IsVonNBounded ℂ S}) _ (tensorOperator E F)
  rw [nuclearLocallyConvex_boundedConvergence_eq hE F]
  exact nuclearLocallyConvex_dense_finiteRank hE

/-- A bounded subset of a quasi-complete nuclear space has compact closure
in the space. -/
theorem nuclearLocallyConvex_compactClosure {E : Type u}
    [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E]
    [ContinuousSMul ℂ E] [QuasiCompleteSpace ℂ E]
    (hE : NuclearLocallyConvex.{u, u} E) {S : Set E} (hS : IsVonNBounded ℂ S) :
    IsCompact (closure S) :=
  isCompact_closure_of_totallyBounded_quasiComplete (𝕜 := ℂ)
    (nuclearLocallyConvex_totallyBounded hE hS)

end

end Masullo
