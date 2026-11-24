import StrictStageTopology
import LocallyConvexSumCompletion
import NuclearPermanence

open Filter Function Set Topology
open scoped DirectSum

namespace Masullo

universe u v

noncomputable section

variable {X : ℕ → Type*} [∀ k, AddCommGroup (X k)] [∀ k, Module ℂ (X k)]
  [∀ k, TopologicalSpace (X k)]

local instance (k : ℕ) (z : X k) : Decidable (z ≠ 0) := Classical.propDecidable _

-- The difference-map and finite-support arguments follow RiemannMasullo,
-- AppC_LCTVS/Sec1.lean at 3a05683cb08307960371f8bdeaa263cf169dd505 (Apache-2.0).
/-- Paper: Definition C.1.5.8, p. 667. The map σ on the direct sum is the identity
minus the shift that sends the kth summand to the next one by its transition map. -/
def directSumDifference (j : ∀ k, X k →L[ℂ] X (k+1)) : (⨁ k, X k) →ₗ[ℂ] (⨁ k, X k) :=
  LinearMap.id - DirectSum.toModule ℂ ℕ _ (fun k ↦
    (DirectSum.lof ℂ ℕ X (k+1)).comp (j k).toLinearMap)

private theorem directSumDifference_lof (j : ∀ k, X k →L[ℂ] X (k+1)) (k : ℕ) (x : X k) :
    directSumDifference j (DirectSum.lof ℂ ℕ X k x) =
      DirectSum.lof ℂ ℕ X k x - DirectSum.lof ℂ ℕ X (k+1) (j k x) := by
  rw [directSumDifference, LinearMap.sub_apply, LinearMap.id_apply, DirectSum.toModule_lof]
  rfl

/-- Paper: Definition C.1.5.8, p. 667. The zeroth coordinate is unchanged and
coordinate k+1 subtracts the image of coordinate k under the kth transition map. -/
theorem directSumDifference_apply (j : ∀ k, X k →L[ℂ] X (k+1)) (x : ⨁ k, X k) :
    directSumDifference j x 0 = x 0 ∧
      ∀ k, directSumDifference j x (k+1) = x (k+1) - j k (x k) := by
  let shift := DirectSum.toModule ℂ ℕ (⨁ k, X k) (fun k ↦
    (DirectSum.lof ℂ ℕ X (k+1)).comp (j k).toLinearMap)
  have hzero : shift x 0 = 0 := by
    suffices (DirectSum.component ℂ ℕ X 0).comp shift = 0 from LinearMap.congr_fun this x
    apply DirectSum.linearMap_ext
    intro i
    ext y : 1
    simp [shift, DirectSum.component.of]
  have hsucc (k : ℕ) : shift x (k+1) = j k (x k) := by
    suffices (DirectSum.component ℂ ℕ X (k+1)).comp shift =
        (j k).toLinearMap.comp (DirectSum.component ℂ ℕ X k) from LinearMap.congr_fun this x
    apply DirectSum.linearMap_ext
    intro i
    ext y : 1
    by_cases h : i = k
    · subst i
      simp [shift]
    · simp [shift, DirectSum.component.of, h]
  change (x - shift x) 0 = x 0 ∧
    ∀ k, (x - shift x) (k+1) = x (k+1) - j k (x k)
  simp [DirectSum.sub_apply, hzero, hsucc]

/-- Extend the sum of the current seminorm and the prescribed seminorm to the next stage. -/
private theorem exists_strictSystem_seminorms
    [∀ k, PolynormableSpace ℂ (X k)]
    (j : ∀ k, X k →L[ℂ] X (k+1)) (hj : ∀ k, IsEmbedding (j k))
    (p : ∀ k, Seminorm ℂ (X k)) (hp : ∀ k, Continuous (p k)) :
    ∃ r : ∀ k, Seminorm ℂ (X k), (∀ k, Continuous (r k)) ∧
      ∀ k, (r (k+1)).comp (j k).toLinearMap = r k + p k := by
  choose next hnext hcomp using fun k (s : {s : Seminorm ℂ (X k) // Continuous s}) ↦
    exists_continuousSeminorm_extension (j k) (hj k) (s.val + p k)
      (show Continuous (s.val + p k) from s.property.add (hp k))
  let r : ∀ k, {s : Seminorm ℂ (X k) // Continuous s} :=
    Nat.rec ⟨0, continuous_const⟩ (fun k s ↦ ⟨next k s, hnext k s⟩)
  exact ⟨fun k ↦ (r k).val, fun k ↦ (r k).property, fun k ↦ hcomp k (r k)⟩

/-- The difference coordinates after a cutoff bound the input seminorms from the cutoff on.
The restriction identity makes the successive triangle inequalities telescope. -/
private theorem directSumDifference_tail_bound
    (j : ∀ k, X k →L[ℂ] X (k+1)) (p r : ∀ k, Seminorm ℂ (X k))
    (hr : ∀ k, (r (k+1)).comp (j k).toLinearMap = r k + p k)
    (x : ⨁ k, X k) (a : ℕ) :
    sumOfSeminorms (fun k ↦ if a ≤ k then p k else 0) x + r a (x a) ≤
      sumOfSeminorms (fun k ↦ if a < k then r k else 0) (directSumDifference j x) := by
  obtain ⟨b, hb⟩ := Finset.exists_nat_subset_range (insert a x.support)
  have hab : a ≤ b := Nat.le_of_lt (Finset.mem_range.mp (hb (Finset.mem_insert_self _ _)))
  have hs : x.support ⊆ Finset.range b := fun _ hk ↦ hb (Finset.mem_insert_of_mem hk)
  have hxb : x b = 0 := DFinsupp.notMem_support_iff.mp fun h ↦
    (Nat.lt_irrefl b) (Finset.mem_range.mp (hs h))
  let y := directSumDifference j x
  have hstep (k : ℕ) : r k (x k) + p k (x k) ≤ r (k+1) (y (k+1)) + r (k+1) (x (k+1)) := by
    have heq := DFunLike.congr_fun (hr k) (x k)
    change r (k+1) (j k (x k)) = r k (x k) + p k (x k) at heq
    have hdiff : j k (x k) - x (k+1) = -(y (k+1)) := by
      change _ = -(directSumDifference j x (k+1))
      rw [(directSumDifference_apply j x).2 k, neg_sub]
    rw [← heq, add_comm (r (k+1) (y (k+1)))]
    simpa only [hdiff, map_neg_eq_map] using le_map_add_map_sub (r (k+1)) (j k (x k)) (x (k+1))
  have hsum (n : ℕ) (hn : a ≤ n) :
      (∑ k ∈ Finset.Ico a n, p k (x k)) + r a (x a) ≤
        (∑ k ∈ Finset.Ico a n, r (k+1) (y (k+1))) + r n (x n) := by
    induction n, hn using Nat.le_induction with
    | base => simp
    | succ n hn ih =>
      rw [Finset.sum_Ico_succ_top hn, Finset.sum_Ico_succ_top hn]
      linarith only [ih, hstep n]
  have hinput : sumOfSeminorms (fun k ↦ if a ≤ k then p k else 0) x =
      ∑ k ∈ Finset.Ico a b, p k (x k) := by
    rw [sumOfSeminorms_apply_of_subset _ _ _ hs]
    simp only [DFunLike.ite_apply, zero_apply, ← Finset.sum_filter]
    congr 1
    ext k
    simp [and_comm]
  have houtput : (∑ k ∈ Finset.Ico a b, r (k+1) (y (k+1))) ≤
      sumOfSeminorms (fun k ↦ if a < k then r k else 0) y := by
    rw [Finset.sum_Ico_add' (fun k ↦ r k (y k)) a b 1]
    refine le_trans ?_ (sumOfSeminorms_bound _ y (Finset.Ico (a+1) (b+1)))
    apply Finset.sum_le_sum
    intro k hk
    simp only [ite_eq_left (Nat.lt_of_succ_le (Finset.mem_Ico.mp hk).1), le_refl]
  rw [hinput]
  exact (hsum b hab).trans (by simpa only [hxb, map_zero, add_zero] using houtput)

/-- The difference map is a topological embedding for a strict sequence.
The sum of prescribed seminorms on the source is controlled by a sum of
recursively extended seminorms on the successive differences. -/
private theorem directSumDifference_isEmbedding
    [∀ k, IsTopologicalAddGroup (X k)] [∀ k, PolynormableSpace ℂ (X k)]
    (j : ∀ k, X k →L[ℂ] X (k+1)) (hj : ∀ k, IsEmbedding (j k)) :
    letI : TopologicalSpace (⨁ k, X k) := locallyConvexSumTopology X
    IsEmbedding (directSumDifference j) := by
  let D := ⨁ k, X k
  let lof := DirectSum.lof ℂ ℕ X
  letI : TopologicalSpace D := locallyConvexSumTopology X
  let W := locallyConvexFinal_withSeminorms lof
  letI : PolynormableSpace ℂ D := W.toPolynormableSpace
  letI : IsTopologicalAddGroup D := W.topologicalAddGroup
  let σ : D →ₗ[ℂ] D := directSumDifference j
  have hσ : Continuous σ := by
    apply (locallyConvexFinal_continuous_iff lof σ).mpr
    intro k
    have heq (z : X k) : σ (lof k z) = lof k z - lof (k+1) (j k z) :=
      directSumDifference_lof j k z
    change Continuous (fun z : X k ↦ σ (lof k z))
    simp_rw [heq]
    exact (locallyConvexFinal_stage_continuous lof k).sub
      ((locallyConvexFinal_stage_continuous lof (k+1)).comp (j k).continuous)
  have hinj : Injective σ := by
    intro x y h
    apply DFinsupp.ext
    intro k
    induction k with
    | zero =>
      have hzero : directSumDifference j x 0 = directSumDifference j y 0 :=
        congrArg (fun z : D ↦ z 0) h
      rwa [(directSumDifference_apply j x).1, (directSumDifference_apply j y).1] at hzero
    | succ k ih =>
      have hstep := congrArg (fun z : D ↦ z (k+1)) h
      change directSumDifference j x (k+1) = directSumDifference j y (k+1) at hstep
      rwa [(directSumDifference_apply j x).2 k, (directSumDifference_apply j y).2 k,
        ih, sub_left_inj] at hstep
  let e := LinearEquiv.ofInjective σ hinj
  have he : Continuous e := hσ.subtype_mk _
  have heInv : Continuous e.symm := by
    apply W.continuous_of_continuous_comp
    intro p
    let s (k : ℕ) := p.val.comp (lof k)
    obtain ⟨r, hr, hrcomp⟩ := exists_strictSystem_seminorms j hj s p.property
    let t (k : ℕ) : Seminorm ℂ (X k) := if 0 < k then r k else 0
    let q := sumOfSeminorms t
    have hq : Continuous q := by
      apply locallyConvexFinal_seminorm_continuous lof q
      intro k
      change Continuous (fun z : X k ↦ sumOfSeminorms t (lof k z))
      have heq : (fun z : X k ↦ sumOfSeminorms t (lof k z)) = (t k : X k → ℝ) :=
        funext fun z ↦ sumOfSeminorms_lof t k z
      rw [heq]
      dsimp [t]
      split
      · exact hr k
      · exact continuous_zero
    have hqsub : Continuous (q.comp σ.range.subtype) := hq.comp continuous_subtype_val
    refine Seminorm.continuous_of_le hqsub fun y ↦ ?_
    let x := e.symm y
    have hx : σ x = (y : D) := congrArg Subtype.val (e.apply_symm_apply y)
    change p.val x ≤ q (y : D)
    rw [← hx]
    have hb := directSumDifference_tail_bound j s r hrcomp x 0
    simp only [Nat.zero_le, ite_true] at hb
    exact (seminorm_le_sumOfSeminorms p.val x).trans
      ((le_add_of_nonneg_right (apply_nonneg (r 0) (x 0))).trans hb)
  let homeo : D ≃ₜ σ.range := ⟨e.toEquiv, he, heInv⟩
  exact IsEmbedding.subtypeVal.comp homeo.isEmbedding

section Limit

variable {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
  {j : ∀ k, X k →L[ℂ] X (k+1)} {i : ∀ k, X k →L[ℂ] E}

/-- Paper: Equation (C.1.5.2), p. 667. The image of the difference map is the
kernel of the canonical map from the direct sum to the limit. -/
private theorem range_directSumDifference
    (hinj : ∀ k, Injective (i k)) (hcompat : ∀ k x, i (k+1) (j k x) = i k x) :
    range (directSumDifference j) =
      (DirectSum.toModule ℂ ℕ E (fun k ↦ (i k).toLinearMap)).ker := by
  let D := ⨁ k, X k
  let q : D →ₗ[ℂ] E := DirectSum.toModule ℂ ℕ E (fun k ↦ (i k).toLinearMap)
  let σ := directSumDifference j
  have hq (k : ℕ) (x : X k) : q (DirectSum.lof ℂ ℕ X k x) = i k x :=
    DirectSum.toModule_lof _ _ _
  refine subset_antisymm ?_ ?_
  · have hcomp : q.comp σ = 0 := by
      apply DirectSum.linearMap_ext
      intro k
      ext x : 1
      change q (directSumDifference j (DirectSum.lof ℂ ℕ X k x)) = 0
      rw [directSumDifference_lof, map_sub, hq, hq]
      exact sub_eq_zero.mpr (hcompat k x).symm
    rintro _ ⟨x, rfl⟩
    exact DFunLike.congr_fun hcomp x
  · classical
    intro y hy
    let s : ∀ k, X k := Nat.rec (y 0) (fun k z ↦ j k z + y (k+1))
    have hs (k : ℕ) : i k (s k) = ∑ l ∈ Finset.range (k+1), i l (y l) := by
      induction k with
      | zero => simp [s]
      | succ k ih =>
        change i (k+1) (j k (s k) + y (k+1)) = _
        have hcomp : i (k+1) (j k (s k)) = i k (s k) :=
          hcompat k (s k)
        rw [map_add, hcomp, ih]
        exact (Finset.sum_range_succ (fun l ↦ i l (y l)) (k+1)).symm
    obtain ⟨n, hn⟩ := Finset.exists_nat_subset_range y.support
    have hsum (k : ℕ) (hk : n ≤ k) : (∑ l ∈ Finset.range (k+1), i l (y l)) = q y := by
      have hqsum : q y = ∑ l ∈ y.support, i l (y l) := calc
        q y = q (∑ l ∈ y.support, DirectSum.lof ℂ ℕ X l (y l)) :=
          congrArg q (DirectSum.sum_support_of y).symm
        _ = _ := by simp only [map_sum, hq]
      rw [hqsum]
      refine (Finset.sum_subset (hn.trans (Finset.range_mono (Nat.le_succ_of_le hk))) ?_).symm
      intro l _ hl
      rw [DFinsupp.notMem_support_iff.mp hl, map_zero]
    have htail (k : ℕ) (hk : n ≤ k) : s k = 0 := hinj k <| by
      rw [hs, hsum k hk, map_zero]
      exact hy
    let x : D := DFinsupp.mk (Finset.range n) (fun k ↦ s k)
    have hx (k : ℕ) : x k = s k := by
      change (DFinsupp.mk (Finset.range n) (fun k ↦ s k)) k = _
      rw [DFinsupp.mk_apply]
      split
      · rfl
      · exact (htail k (by simpa using ‹k ∉ Finset.range n›)).symm
    refine ⟨x, DFinsupp.ext fun k ↦ ?_⟩
    cases k with
    | zero => exact (directSumDifference_apply j x).1.trans (hx 0)
    | succ k =>
      rw [(directSumDifference_apply j x).2 k, hx, hx]
      exact add_sub_cancel_left (j k (s k)) (y (k+1))

/-- The canonical sum map is an open quotient for the locally convex
inductive limit topology. -/
private theorem directSumToLimit_isOpenQuotientMap
    [∀ k, IsTopologicalAddGroup (X k)] [PolynormableSpace ℂ E]
    (hexhaust : ∀ x : E, ∃ k, x ∈ range (i k))
    (hlimit : ∀ p : Seminorm ℂ E, (∀ k, Continuous (p.comp (i k).toLinearMap)) → Continuous p) :
    letI : TopologicalSpace (⨁ k, X k) := locallyConvexSumTopology X
    IsOpenQuotientMap (DirectSum.toModule ℂ ℕ E (fun k ↦ (i k).toLinearMap)) := by
  let D := ⨁ k, X k
  let lof := DirectSum.lof ℂ ℕ X
  letI : TopologicalSpace D := locallyConvexSumTopology X
  let W := locallyConvexFinal_withSeminorms lof
  letI : PolynormableSpace ℂ D := W.toPolynormableSpace
  letI : IsTopologicalAddGroup D := W.topologicalAddGroup
  letI : ContinuousSMul ℂ D := W.continuousSMul
  let q : D →ₗ[ℂ] E := DirectSum.toModule ℂ ℕ E (fun k ↦ (i k).toLinearMap)
  have hq (k : ℕ) (x : X k) : q (lof k x) = i k x := DirectSum.toModule_lof _ _ _
  have hsurj : Surjective q := by
    intro x
    obtain ⟨k, y, rfl⟩ := hexhaust x
    exact ⟨lof k y, hq k y⟩
  have hqc : Continuous q := by
    apply (locallyConvexFinal_continuous_iff lof q).mpr
    intro k
    exact (i k).continuous.congr (fun x ↦ (hq k x).symm)
  let e := q.quotKerEquivOfSurjective hsurj
  letI : PolynormableSpace ℂ (D ⧸ q.ker) := polynormableSpace_complex_quotient q.ker
  letI : IsTopologicalAddGroup E := (PolynormableSpace.withSeminorms ℂ E).topologicalAddGroup
  have he : Continuous e := q.ker.isOpenQuotientMap_mkQ.isQuotientMap.continuous_iff.mpr hqc
  have heInv : Continuous e.symm := by
    apply (PolynormableSpace.withSeminorms ℂ (D ⧸ q.ker)).continuous_of_continuous_comp
    intro p
    apply hlimit (p.val.comp e.symm.toLinearMap)
    intro k
    have heq (x : X k) : e.symm (i k x) = q.ker.mkQ (lof k x) := by
      rw [← hq]
      exact q.quotKerEquivOfSurjective_symm_apply hsurj _
    change Continuous (fun x : X k ↦ p.val (e.symm (i k x)))
    simp_rw [heq]
    exact p.property.comp
      (q.ker.isOpenQuotientMap_mkQ.continuous.comp (locallyConvexFinal_stage_continuous lof k))
  let homeo : (D ⧸ q.ker) ≃ₜ E := ⟨e.toEquiv, he, heInv⟩
  change IsOpenQuotientMap q
  exact homeo.isOpenQuotientMap.comp q.ker.isOpenQuotientMap_mkQ

/-- Formula (D.1.5.6) for the inverse of the difference map, expressed
after including the stage in the limit. The stage inclusion is injective,
so the partial sum determines the stage coordinate uniquely. -/
theorem LinearInductivePresentation.difference_partialSum
    (D : LinearInductivePresentation E X) (x : ⨁ k, X k) (n : ℕ) :
    D.incl n (x n) = ∑ k ∈ Finset.range (n+1),
      D.incl k (directSumDifference (fun l ↦ D.transition (Nat.le_succ l)) x k) := by
  let j (k : ℕ) := D.transition (Nat.le_succ k)
  change D.incl n (x n) = ∑ k ∈ Finset.range (n+1), D.incl k (directSumDifference j x k)
  induction n with
  | zero => simp [(directSumDifference_apply j x).1]
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih, (directSumDifference_apply j x).2 n, map_sub]
    rw [show D.incl (n+1) (j n (x n)) = D.incl n (x n) from
      D.incl_transition (Nat.le_succ n) (x n)]
    abel

/-- A strict inductive presentation of a Hausdorff locally convex space has
a topologically exact difference sequence. Both direct sums carry the
locally convex coproduct topology. -/
theorem LinearInductivePresentation.topologicallyExact_difference
    [∀ k, IsTopologicalAddGroup (X k)] [∀ k, PolynormableSpace ℂ (X k)]
    [PolynormableSpace ℂ E] [T2Space E]
    (D : LinearInductivePresentation E X)
    (hemb : ∀ k, IsEmbedding (D.transition (Nat.le_succ k)))
    (hlimit : ∀ p : Seminorm ℂ E,
      (∀ k, Continuous (p.comp (D.incl k).toLinearMap)) → Continuous p) :
    letI : TopologicalSpace (⨁ k, X k) := locallyConvexSumTopology X
    let σ := directSumDifference (fun k ↦ D.transition (Nat.le_succ k))
    let q := DirectSum.toModule ℂ ℕ E (fun k ↦ (D.incl k).toLinearMap)
    IsClosedEmbedding σ ∧ LinearMap.range σ = LinearMap.ker q ∧ IsOpenQuotientMap q := by
  letI : TopologicalSpace (⨁ k, X k) := locallyConvexSumTopology X
  let σ := directSumDifference (fun k ↦ D.transition (Nat.le_succ k))
  let q := DirectSum.toModule ℂ ℕ E (fun k ↦ (D.incl k).toLinearMap)
  have hker : range σ = (LinearMap.ker q : Set (⨁ k, X k)) :=
    range_directSumDifference D.injective_incl (fun k ↦ D.incl_transition (Nat.le_succ k))
  have hq : IsOpenQuotientMap q := directSumToLimit_isOpenQuotientMap D.exhaust hlimit
  refine ⟨⟨directSumDifference_isEmbedding _ hemb, ?_⟩, SetLike.ext' hker, hq⟩
  rw [hker]
  exact isClosed_singleton.preimage hq.continuous

end Limit

/-- A Hausdorff countable locally convex limit of nuclear stages is nuclear.
This form applies directly to a realized presentation on a space of functions. -/
theorem LinearInductivePresentation.nuclear_of_stages
    {E : Type u} {X : ℕ → Type v} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [PolynormableSpace ℂ E] [T2Space E]
    [∀ n, AddCommGroup (X n)] [∀ n, Module ℂ (X n)] [∀ n, TopologicalSpace (X n)]
    (D : LinearInductivePresentation E X) (hX : ∀ n, NuclearLocallyConvex.{max u v, v} (X n))
    (hlimit : ∀ p : Seminorm ℂ E,
      (∀ n, Continuous (p.comp (D.incl n).toLinearMap)) → Continuous p) :
    NuclearLocallyConvex.{max u v, u} E := by
  let A := ⨁ n, X n
  let i := DirectSum.lof ℂ ℕ X
  letI : TopologicalSpace A := locallyConvexSumTopology X
  letI (n : ℕ) : PolynormableSpace ℂ (X n) := (hX n).2.1
  letI (n : ℕ) : IsTopologicalAddGroup (X n) :=
    (PolynormableSpace.withSeminorms ℂ (X n)).topologicalAddGroup
  letI : IsTopologicalAddGroup A := (locallyConvexFinal_withSeminorms i).topologicalAddGroup
  let q : A →ₗ[ℂ] E := DirectSum.toModule ℂ ℕ E (fun n ↦ (D.incl n).toLinearMap)
  have hq : IsOpenQuotientMap q := directSumToLimit_isOpenQuotientMap D.exhaust hlimit
  have hK : IsClosed (q.ker : Set A) := isClosed_singleton.preimage hq.continuous
  let e := q.quotKerEquivOfSurjective hq.surjective
  let π := q.ker.isOpenQuotientMap_mkQ
  have he : Continuous e := π.isQuotientMap.continuous_iff.mpr hq.continuous
  have he' : Continuous e.symm := hq.isQuotientMap.continuous_iff.mpr
    (π.continuous.congr (fun x ↦ (q.quotKerEquivOfSurjective_symm_apply hq.surjective x).symm))
  exact nuclearLocallyConvex_of_equiv ⟨e, he, he'⟩
    (nuclearLocallyConvex_quotient.{v, u} (nuclearLocallyConvex_directSum.{v, u, 0}
      (Function.Embedding.refl ℕ) hX) q.ker hK)


end

end Masullo
