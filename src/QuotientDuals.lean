import NuclearApproximation
import TopologicalLinearLimits
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Topology.Algebra.Module.Spaces.WeakDual
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Metrizable.Uniformity

/-! # Weak and strong adjoints to quotient maps

The compact lifting and dual-embedding arguments are adapted from
the Apache-2.0 project mccorvie/riemann-masullo at 6af7aba188cecbd2af3d169176055cabadd3b243.
-/

open Bornology Filter Function Set Topology TopologicalSpace UniformSpace
open scoped Uniformity

namespace Masullo

noncomputable section

universe u

/-- An open quotient map from a complete pseudometric space onto a Hausdorff space lifts
each compact set to a compact set. -/
theorem exists_isCompact_image_eq_of_isOpenQuotientMap
    {X Y : Type*} [PseudoMetricSpace X] [CompleteSpace X] [TopologicalSpace Y] [T2Space Y]
    {f : X → Y} (hf : IsOpenQuotientMap f) {s : Set Y} (hs : IsCompact s) :
    ∃ t : Set X, IsCompact t ∧ f '' t = s := by
  classical
  let r (n : ℕ) : ℝ := (1 / 2) ^ n
  -- Shrink an open lift while retaining a finite cover by balls of radius r n.
  have step (n : ℕ) (U : Set X) (hU : IsOpen U) (hcover : s ⊆ f '' U) :
      ∃ V : Set X, IsOpen V ∧ s ⊆ f '' V ∧ closure V ⊆ U ∧
        ∃ C : Set X, C.Finite ∧ closure V ⊆ ⋃ x ∈ C, Metric.closedBall x (r n) := by
    have hsmall (x : U) : ∃ ε : ℝ, 0 < ε ∧ ε ≤ r n ∧ Metric.closedBall x.val ε ⊆ U := by
      obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds x.property)
      refine ⟨min (δ / 2) (r n), lt_min (by positivity) (by dsimp [r]; positivity),
        min_le_right _ _, ?_⟩
      exact (Metric.closedBall_subset_ball ((min_le_left _ _).trans_lt (half_lt_self hδ))).trans hball
    choose ε hε hle hsub using hsmall
    obtain ⟨I, hI⟩ := hs.elim_finite_subcover (fun x : U ↦ f '' Metric.ball x.val (ε x))
      (fun x ↦ hf.isOpenMap _ Metric.isOpen_ball) (by
        intro y hy
        obtain ⟨x, hx, rfl⟩ := hcover hy
        exact mem_iUnion.mpr ⟨⟨x, hx⟩, mem_image_of_mem f (Metric.mem_ball_self (hε _))⟩)
    let V := ⋃ x ∈ I, Metric.ball x.val (ε x)
    have hclosure : closure V ⊆ ⋃ x ∈ I, Metric.closedBall x.val (ε x) :=
      closure_minimal (iUnion₂_mono fun x _ ↦ Metric.ball_subset_closedBall)
        (isClosed_biUnion_finset fun _ _ ↦ Metric.isClosed_closedBall)
    refine ⟨V, isOpen_biUnion fun _ _ ↦ Metric.isOpen_ball, ?_,
      hclosure.trans (iUnion₂_subset fun x _ ↦ hsub x), Subtype.val '' (I : Set U),
      I.finite_toSet.image _, ?_⟩
    · simpa only [V, image_iUnion] using hI
    · intro x hx
      obtain ⟨c, hc, hxc⟩ := mem_iUnion₂.mp (hclosure hx)
      exact mem_iUnion₂.mpr ⟨c.val, mem_image_of_mem _ hc, Metric.closedBall_subset_closedBall (hle c) hxc⟩
  choose next hnextOpen hnextCover hnextSub hnextFinite using step
  let U : ℕ → {U : Set X // IsOpen U ∧ s ⊆ f '' U} :=
    Nat.rec ⟨univ, isOpen_univ, by rw [image_univ, hf.surjective.range_eq]; exact subset_univ _⟩
      (fun n V ↦ ⟨next n V.val V.property.1 V.property.2, hnextOpen n _ _ _, hnextCover n _ _ _⟩)
  let V (n : ℕ) : Set X := (U n).val
  have hnest (n : ℕ) : closure (V (n + 1)) ⊆ V n := hnextSub n _ _ _
  have hanti : Antitone V := antitone_nat_of_succ_le fun n ↦ subset_closure.trans (hnest n)
  have hfinite (n : ℕ) (δ : ℝ) (hδ : r n < δ) :
      ∃ C : Set X, C.Finite ∧ closure (V (n + 1)) ⊆ ⋃ x ∈ C, Metric.ball x δ := by
    obtain ⟨C, hC, hballs⟩ := hnextFinite n (U n).val (U n).property.1 (U n).property.2
    exact ⟨C, hC, hballs.trans (iUnion₂_mono fun _ _ ↦ Metric.closedBall_subset_ball hδ)⟩
  let A := ⋂ n, closure (V (n + 1))
  have hA : IsCompact A := by
    refine (Metric.totallyBounded_iff.mpr fun δ hδ ↦ ?_).isCompact_of_isClosed
      (isClosed_iInter fun _ ↦ isClosed_closure)
    obtain ⟨n, hn⟩ : ∃ n, r n < δ := exists_pow_lt_of_lt_one hδ (by norm_num)
    obtain ⟨C, hC, hballs⟩ := hfinite n δ hn
    exact ⟨C, hC, (iInter_subset _ n).trans hballs⟩
  refine ⟨A ∩ f ⁻¹' s, hA.inter_right (hs.isClosed.preimage hf.continuous), ?_⟩
  apply Subset.antisymm (image_subset_iff.mpr inter_subset_right)
  intro y hy
  choose x hx hfx using fun n : ℕ ↦ (U (n + 1)).property.2 hy
  have htotal : TotallyBounded (range x) := Metric.totallyBounded_iff.mpr fun δ hδ ↦ by
    obtain ⟨n, hn⟩ : ∃ n, r n < δ := exists_pow_lt_of_lt_one hδ (by norm_num)
    obtain ⟨C, hC, hballs⟩ := hfinite n δ hn
    refine ⟨C ∪ x '' Iio n, hC.union ((finite_Iio n).image x), ?_⟩
    rintro _ ⟨m, rfl⟩
    by_cases hm : m < n
    · exact mem_iUnion₂.mpr ⟨x m, Or.inr (mem_image_of_mem x hm), Metric.mem_ball_self hδ⟩
    · obtain ⟨c, hc, hxc⟩ := mem_iUnion₂.mp
        (hballs (subset_closure (hanti (Nat.succ_le_succ (Nat.le_of_not_gt hm)) (hx m))))
      exact mem_iUnion₂.mpr ⟨c, Or.inl hc, hxc⟩
  obtain ⟨z, _, φ, hφ, hlim⟩ :=
    (htotal.closure.isCompact_of_isClosed isClosed_closure).tendsto_subseq
      (fun n ↦ subset_closure (mem_range_self n))
  have hfy : f z = y := by
    apply tendsto_nhds_unique ((hf.continuous.tendsto z).comp hlim)
    have hconst : f ∘ x ∘ φ = fun _ ↦ y := funext fun m ↦ hfx (φ m)
    rw [hconst]
    exact tendsto_const_nhds
  refine ⟨z, ⟨mem_iInter.mpr fun n ↦ ?_, show f z ∈ s from hfy.symm ▸ hy⟩, hfy⟩
  apply isClosed_closure.mem_of_tendsto hlim
  filter_upwards [(hφ.tendsto_atTop.eventually (eventually_ge_atTop n))] with m hm
  exact subset_closure (hanti (Nat.succ_le_succ hm) (hx (φ m)))

section QuotientDual

variable {X : Type u} [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]

/-- Lemma 4.2.1.3, p. 163. Pullback along the quotient embeds the weak dual
and has image the continuous functionals vanishing on the closed subspace. -/
theorem quotientDual_weakEmbedding (M : Submodule ℂ X) :
    let pull := fun l : WeakDual ℂ (X ⧸ M) ↦ StrongDual.toWeakDual (l.toStrongDual.comp M.mkQL)
    IsEmbedding pull ∧ range pull = {l | ∀ x ∈ M, l x = 0} := by
  dsimp only
  constructor
  · have he : IsEmbedding (fun l : WeakDual ℂ (X ⧸ M) ↦ (l : (X ⧸ M) → ℂ)) :=
      WeakBilin.isEmbedding (B := topDualPairing ℂ (X ⧸ M)) ContinuousLinearMap.coe_injective
    have hπ := M.mkQ_surjective.isEmbedding_comp (X := ℂ) M.mkQ
    apply Topology.IsEmbedding.of_comp (g := fun l : WeakDual ℂ X ↦ (l : X → ℂ))
      (WeakDual.continuous_of_continuous_eval fun x ↦ WeakDual.eval_continuous (M.mkQ x))
      WeakDual.coeFn_continuous
    exact hπ.comp he
  · ext l
    constructor
    · rintro ⟨v, rfl⟩ x hx
      change v (Submodule.Quotient.mk x) = 0
      rw [(Submodule.Quotient.mk_eq_zero M).mpr hx, map_zero]
    · intro h
      refine ⟨StrongDual.toWeakDual (M.liftQL l.toStrongDual (fun x hx ↦ h x hx)), ?_⟩
      exact DFunLike.ext _ _ fun _ ↦ rfl

/-- Lemma 4.2.1.3, p. 163. The image of the quotient adjoint in the
strong dual consists precisely of the functionals vanishing on the subspace. -/
theorem quotientDual_strongRange (M : Submodule ℂ X) :
    range (ContinuousLinearMap.precomp (τ := RingHom.id ℂ) ℂ M.mkQL) =
      {l : StrongDual ℂ X | ∀ x ∈ M, l x = 0} := by
  exact (quotientDual_weakEmbedding M).2

/-- The closure of a bounded set in a nuclear Fréchet quotient is the exact
image of a compact set upstairs. -/
theorem nuclearFrechet_quotient_compactLift
    (M : Submodule ℂ X) (hM : IsClosed (M : Set X))
    (hN : NuclearLocallyConvex.{u, u} X) (hF : IsFrechetTVS X)
    {B : Set (X ⧸ M)} (hB : IsVonNBounded ℂ B) :
    ∃ A : Set X, IsCompact A ∧ M.mkQ '' A = closure B := by
  obtain ⟨hadd, hpoly, hmetric, hcomplete⟩ := hF
  letI : UniformSpace X := IsTopologicalAddGroup.rightUniformSpace X
  letI : CompleteSpace X := hcomplete
  letI : (uniformity X).IsCountablyGenerated := Filter.comap.isCountablyGenerated _ _
  letI : MetricSpace X := UniformSpace.metricSpace X
  letI : ContinuousSMul ℂ X := (PolynormableSpace.withSeminorms ℂ X).continuousSMul
  letI : IsClosed (M : Set X) := hM
  letI : UniformSpace (X ⧸ M) := IsTopologicalAddGroup.rightUniformSpace (X ⧸ M)
  letI : IsUniformAddGroup (X ⧸ M) := isUniformAddGroup_of_addCommGroup
  letI : CompleteSpace (X ⧸ M) := QuotientAddGroup.completeSpace_right' X M.toAddSubgroup
  have htotal := nuclearLocallyConvex_totallyBounded (nuclearLocallyConvex_quotient hN M hM) hB
  exact exists_isCompact_image_eq_of_isOpenQuotientMap M.isOpenQuotientMap_mkQ
    (htotal.closure.isCompact_of_isClosed isClosed_closure)

/-- Bounded covers along a quotient map induce a topological embedding on strong duals. -/
theorem quotientDual_strongEmbedding_of_bounded_lifts (M : Submodule ℂ X)
    (hLift : ∀ (B : Set (X ⧸ M)), IsVonNBounded ℂ B →
      ∃ A : Set X, IsVonNBounded ℂ A ∧ B ⊆ M.mkQL '' A) :
    IsEmbedding (ContinuousLinearMap.precomp (τ := RingHom.id ℂ) ℂ M.mkQL) := by
  let pull : StrongDual ℂ (X ⧸ M) →L[ℂ] StrongDual ℂ X :=
    ContinuousLinearMap.precomp (τ := RingHom.id ℂ) ℂ M.mkQL
  have hind : IsUniformInducing pull := by
    constructor
    refine le_antisymm ?_ pull.uniformContinuous.le_comap
    have hX := (ContinuousLinearMap.hasBasis_nhds_zero
      (σ := RingHom.id ℂ) («E» := X) (F := ℂ)).uniformity_of_nhds_zero
    have hQ := (ContinuousLinearMap.hasBasis_nhds_zero
      (σ := RingHom.id ℂ) («E» := X ⧸ M) (F := ℂ)).uniformity_of_nhds_zero
    refine ((hX.comap (Prod.map pull pull)).le_basis_iff hQ).mpr ?_
    rintro ⟨B, U⟩ ⟨hB, hU⟩
    obtain ⟨A, hA, hcover⟩ := hLift B hB
    refine ⟨(A, U), ⟨hA, hU⟩, ?_⟩
    intro p hp
    change ∀ x ∈ A, (pull p.2 - pull p.1) x ∈ U at hp
    change ∀ y ∈ B, (p.2 - p.1) y ∈ U
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hcover hy
    exact hp x hx
  refine ⟨hind.isInducing, ?_⟩
  intro f g hfg
  ext y
  obtain ⟨x, rfl⟩ := M.mkQ_surjective y
  exact congrArg (fun l : StrongDual ℂ X ↦ l x) hfg

/-- Lemma 4.2.1.3(1), p. 163. For a nuclear Fréchet space the quotient
adjoint also embeds the strong dual, with image the same annihilator. -/
theorem quotientDual_strongEmbedding_of_nuclear (M : Submodule ℂ X) (hM : IsClosed (M : Set X))
    (hN : NuclearLocallyConvex.{u, u} X) (hF : IsFrechetTVS X) :
    IsEmbedding (ContinuousLinearMap.precomp (τ := RingHom.id ℂ) ℂ M.mkQL) := by
  obtain ⟨hadd, hpoly, hmetric, hcomplete⟩ := hF
  letI : ContinuousSMul ℂ X := (PolynormableSpace.withSeminorms ℂ X).continuousSMul
  apply quotientDual_strongEmbedding_of_bounded_lifts M
  intro B hB
  obtain ⟨A, hA, hcover⟩ := nuclearFrechet_quotient_compactLift M hM hN
    ⟨hadd, hpoly, hmetric, hcomplete⟩ hB
  exact ⟨A, hA.isVonNBounded ℂ, fun _ hy ↦ hcover.symm ▸ subset_closure hy⟩

/-- Lemma 4.2.1.3(2), p. 164. For a Hilbert space the quotient adjoint
embeds the strong dual, with image the annihilator of the closed subspace. -/
theorem quotientDual_strongEmbedding_of_hilbert {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (M : Submodule ℂ H) (hM : IsClosed (M : Set H)) :
    IsEmbedding (ContinuousLinearMap.precomp (τ := RingHom.id ℂ) ℂ M.mkQL) := by
  have : CompleteSpace M := hM.completeSpace_coe
  let s : (H ⧸ M) →L[ℂ] H :=
    Mᗮ.subtypeL.comp M.quotientEquivOrthogonal.toLinearIsometry.toContinuousLinearMap
  let r := ContinuousLinearMap.precomp (τ := RingHom.id ℂ) ℂ s
  apply Topology.IsEmbedding.of_leftInverse (f := r) _ r.continuous
    (ContinuousLinearMap.precomp (τ := RingHom.id ℂ) ℂ M.mkQL).continuous
  intro φ
  ext x
  change φ (M.mkQ ((M.quotientEquivOrthogonal x : Mᗮ) : H)) = φ x
  congr 1
  exact (M.quotientEquivOrthogonal_symm_eq_mk _ (M.quotientEquivOrthogonal x).property).symm.trans
    (M.quotientEquivOrthogonal.symm_apply_apply x)

end QuotientDual

end

end Masullo
