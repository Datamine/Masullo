import ProjectiveTensorFinal
import InjectiveTensorMaps
import Mathlib.Topology.Algebra.IsUniformGroup.Basic

open Filter Function Set Topology UniformSpace
open scoped DirectSum NNReal TensorProduct Uniformity

namespace Masullo

noncomputable section

variable {I : Type*} [DecidableEq I] {A : I → Type*}
  [∀ i, AddCommGroup (A i)] [∀ i, Module ℂ (A i)]

local instance (i : I) (x : A i) : Decidable (x ≠ 0) := Classical.propDecidable _

private def sumOfSeminormsValue (p : ∀ i, Seminorm ℂ (A i)) (x : ⨁ i, A i) : ℝ :=
  ∑ i ∈ x.support, p i (x i)

private theorem sumOfSeminorms_on (p : ∀ i, Seminorm ℂ (A i)) (x : ⨁ i, A i)
    {s : Finset I} (hs : x.support ⊆ s) :
    sumOfSeminormsValue p x = ∑ i ∈ s, p i (x i) :=
  Finset.sum_subset hs fun i _ hi => by rw [DFinsupp.notMem_support_iff.mp hi, map_zero]

/-- Summing stage seminorms over the finite support gives a seminorm on the direct sum. -/
def sumOfSeminorms (p : ∀ i, Seminorm ℂ (A i)) : Seminorm ℂ (⨁ i, A i) := by
  refine Seminorm.of (sumOfSeminormsValue p) (fun x y => ?_) (fun a x => ?_)
  · let s := x.support ∪ y.support
    rw [sumOfSeminorms_on p (x + y) (s := s) DFinsupp.support_add,
      sumOfSeminorms_on p x (s := s) Finset.subset_union_left,
      sumOfSeminorms_on p y (s := s) Finset.subset_union_right, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun i _ => map_add_le_add (p i) (x i) (y i)
  · rw [sumOfSeminorms_on p (a • x) (DFinsupp.support_smul a x),
      sumOfSeminorms_on p x (Finset.Subset.refl _), Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => map_smul_eq_mul (p i) a (x i)

theorem sumOfSeminorms_lof (p : ∀ i, Seminorm ℂ (A i)) (i : I) (x : A i) :
    sumOfSeminorms p (DirectSum.lof ℂ I A i x) = p i x := by
  change sumOfSeminormsValue p (DFinsupp.single i x) = _
  rw [sumOfSeminorms_on _ _ DFinsupp.support_single_subset,
    Finset.sum_singleton, DFinsupp.single_eq_same]

theorem sumOfSeminorms_apply_of_subset (p : ∀ i, Seminorm ℂ (A i)) (x : ⨁ i, A i)
    (s : Finset I) (hs : x.support ⊆ s) :
    sumOfSeminorms p x = ∑ i ∈ s, p i (x i) :=
  sumOfSeminorms_on p x hs

theorem sumOfSeminorms_bound (p : ∀ i, Seminorm ℂ (A i)) (x : ⨁ i, A i)
    (s : Finset I) : ∑ i ∈ s, p i (x i) ≤ sumOfSeminorms p x := by
  change _ ≤ sumOfSeminormsValue p x
  rw [sumOfSeminorms_on p x (s := s ∪ x.support) Finset.subset_union_right]
  exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
    fun i _ _ => apply_nonneg _ _

theorem seminorm_le_sumOfSeminorms (q : Seminorm ℂ (⨁ i, A i)) :
    q ≤ sumOfSeminorms (fun i => q.comp (DirectSum.lof ℂ I A i)) := by
  intro x
  change q x ≤ ∑ i ∈ x.support, q (DirectSum.lof ℂ I A i (x i))
  calc
    q x = q (∑ i ∈ x.support, DirectSum.lof ℂ I A i (x i)) :=
      congrArg q (DFinsupp.sum_single (f := x)).symm
    _ ≤ _ := by
      induction x.support using Finset.induction_on with
      | empty => simp
      | insert i s hi ih =>
        simp only [Finset.sum_insert hi]
        exact (map_add_le_add q _ _).trans (add_le_add_right ih _)

section Topology

variable [∀ i, UniformSpace (A i)] [∀ i, IsUniformAddGroup (A i)]
  [∀ i, PolynormableSpace ℂ (A i)]

/-- The locally convex structure determined by the canonical summand maps. -/
def locallyConvexSumStructure : TopologicalModuleStructure (⨁ i, A i) := by
  let j := DirectSum.lof ℂ I A
  letI : TopologicalSpace (⨁ i, A i) := locallyConvexSumTopology A
  let W := locallyConvexFinal_withSeminorms j
  letI : ContinuousSMul ℂ (⨁ i, A i) := W.continuousSMul
  exact ⟨locallyConvexSumTopology A, W.topologicalAddGroup, inferInstance⟩

local instance : UniformSpace (⨁ i, A i) :=
  (locallyConvexSumStructure (A := A)).uniformSpace

local instance : IsUniformAddGroup (⨁ i, A i) :=
  (locallyConvexSumStructure (A := A)).uniformGroup

omit [∀ i, PolynormableSpace ℂ (A i)] [∀ i, IsUniformAddGroup (A i)] in
private theorem sumOfSeminorms_continuous (p : ∀ i, Seminorm ℂ (A i))
    (hp : ∀ i, Continuous (p i)) : Continuous (sumOfSeminorms p) := by
  apply locallyConvexFinal_seminorm_continuous (DirectSum.lof ℂ I A)
  intro i
  exact (hp i).congr fun x => (sumOfSeminorms_lof p i x).symm

private theorem directSum_coordinate_continuous (i : I) :
    Continuous (DirectSum.component ℂ I A i) := by
  apply (locallyConvexFinal_continuous_iff (DirectSum.lof ℂ I A) _).mpr
  intro j
  classical
  by_cases h : j = i
  · subst j
    exact continuous_id.congr fun x => (DirectSum.component.lof_self ℂ i x).symm
  · exact continuous_const.congr fun x => by
      simpa [h] using (DirectSum.component.of ℂ i j x).symm

theorem locallyConvexSum_t2 [∀ i, T2Space (A i)] : T2Space (⨁ i, A i) :=
  T2Space.of_injective_continuous (f := fun x i => x i)
    (fun _ _ h => DFinsupp.ext (congrFun h)) (continuous_pi directSum_coordinate_continuous)

/-- An arbitrary locally convex direct sum of complete Hausdorff spaces is complete. -/
theorem locallyConvexSum_complete [∀ i, CompleteSpace (A i)] [∀ i, T2Space (A i)] :
    CompleteSpace (⨁ i, A i) := by
  classical
  refine ⟨fun {L} hL => ?_⟩
  have hcoord (i : I) : ∃ z : A i, Tendsto (fun x : ⨁ i, A i => x i) L (𝓝 z) := by
    have hU : UniformContinuous (DirectSum.component ℂ I A i) :=
      uniformContinuous_of_continuousAt_zero (DirectSum.component ℂ I A i).toAddMonoidHom
        (directSum_coordinate_continuous i).continuousAt
    exact CompleteSpace.complete (hL.map hU)
  choose z hz using hcoord
  have hbound (p : ∀ i, Seminorm ℂ (A i)) (hp : ∀ i, Continuous (p i))
      (ε : ℝ) (he : 0 < ε) :
      ∀ᶠ x in L, ∀ s : Finset I, ∑ i ∈ s, p i (z i - x i) ≤ ε := by
    have hn := (sumOfSeminorms_continuous p hp).tendsto' (0 : (⨁ i, A i)) 0 (map_zero _)
      (Iio_mem_nhds he)
    have hmem : {u : (⨁ i, A i) × (⨁ i, A i) |
        sumOfSeminorms p (u.2 - u.1) < ε} ∈ 𝓤 (⨁ i, A i) := by
      rw [uniformity_eq_comap_nhds_zero]
      exact Filter.preimage_mem_comap (m := fun u : (⨁ i, A i) × (⨁ i, A i) => u.2 - u.1) hn
    obtain ⟨S, hS, hPair⟩ := (cauchy_iff.mp hL).2 _ hmem
    filter_upwards [hS] with x hx s
    have ht : Tendsto (fun y : ⨁ i, A i => ∑ i ∈ s, p i (y i - x i)) L
        (𝓝 (∑ i ∈ s, p i (z i - x i))) :=
      tendsto_finsetSum _ fun i _ =>
        (hp i).continuousAt.tendsto.comp ((hz i).sub tendsto_const_nhds)
    letI : L.NeBot := hL.1
    apply isClosed_Iic.mem_of_tendsto ht
    filter_upwards [hS] with y hy
    exact ((sumOfSeminorms_bound p (y - x) s).trans_lt (hPair (show (x, y) ∈ S ×ˢ S from ⟨hx, hy⟩))).le
  have hexists (i : I) (h : z i ≠ 0) :
      ∃ p : Seminorm ℂ (A i), Continuous p ∧ p (z i) = 1 := by
    let W := PolynormableSpace.withSeminorms ℂ (A i)
    obtain ⟨p, hp⟩ := W.separating_of_T1 (z i) h
    have hpos : 0 < p.val (z i) := lt_of_le_of_ne (apply_nonneg _ _) (Ne.symm hp)
    let c : ℝ≥0 := ⟨(p.val (z i))⁻¹, inv_nonneg.mpr hpos.le⟩
    refine ⟨c • p.val, continuous_const.mul p.property, ?_⟩
    change (p.val (z i))⁻¹ * p.val (z i) = 1
    exact inv_mul_cancel₀ hpos.ne'
  have hsep (i : I) : ∃ p : Seminorm ℂ (A i), Continuous p ∧ (z i ≠ 0 → p (z i) = 1) := by
    by_cases h : z i = 0
    · exact ⟨0, continuous_const, fun h' => (h' h).elim⟩
    · obtain ⟨p, hp, hpz⟩ := hexists i h
      exact ⟨p, hp, fun _ => hpz⟩
  choose p hp hpz using hsep
  letI : L.NeBot := hL.1
  obtain ⟨x, hx⟩ := (hbound p hp (1 / 2) (by norm_num)).exists
  have hsupport (i : I) (hi : i ∉ x.support) : z i = 0 := by
    by_contra hne
    have hh := hx {i}
    rw [Finset.sum_singleton, DFinsupp.notMem_support_iff.mp hi, sub_zero, hpz i hne] at hh
    norm_num at hh
  let z' : (⨁ i, A i) := DFinsupp.mk x.support (fun i => z i)
  have hval (i : I) : z' i = z i := by
    by_cases hi : i ∈ x.support
    · exact DFinsupp.mk_of_mem hi
    · exact (DFinsupp.mk_of_notMem hi).trans (hsupport i hi).symm
  refine ⟨z', ?_⟩
  change Tendsto id L (𝓝 z')
  apply ((locallyConvexFinal_withSeminorms (DirectSum.lof ℂ I A)).tendsto_nhds _ _).mpr
  intro q ε he
  let p' (i : I) := q.val.comp (DirectSum.lof ℂ I A i)
  filter_upwards [hbound p' q.property (ε / 2) (half_pos he)] with y hy
  have hh := hy (y - z').support
  have hs : sumOfSeminorms p' (y - z') ≤ ε / 2 := by
    change (∑ i ∈ (y - z').support, p' i ((y - z') i)) ≤ _
    convert hh using 1
    apply Finset.sum_congr rfl
    intro i _
    rw [DFinsupp.sub_apply, hval, ← neg_sub, map_neg_eq_map]
  exact ((seminorm_le_sumOfSeminorms q.val _).trans hs).trans_lt (half_lt_self he)


variable [∀ i, UniformContinuousConstSMul ℂ (A i)]

local instance (i : I) : PolynormableSpace ℂ (Completion (A i)) :=
  polynormableSpace_completion

/-- Apply the coordinate completion maps to a finitely supported family. -/
def directSumToCoordinateCompletions :
    (⨁ i, A i) →ₗ[ℂ] (⨁ i, Completion (A i)) :=
  DirectSum.toModule ℂ I _ fun i =>
    (DirectSum.lof ℂ I (fun i => Completion (A i)) i).comp
      (completionInclusionL (V := A i)).toLinearMap

omit [∀ i, PolynormableSpace ℂ (A i)] in
@[simp] theorem directSumToCoordinateCompletions_lof (i : I) (x : A i) :
    directSumToCoordinateCompletions (DirectSum.lof ℂ I A i x) =
      DirectSum.lof ℂ I (fun i => Completion (A i)) i (x : Completion (A i)) :=
  DirectSum.toModule_lof ℂ i x

omit [∀ i, PolynormableSpace ℂ (A i)] in
private theorem directSumToCoordinateCompletions_coordinate (x : ⨁ i, A i) (i : I) :
    directSumToCoordinateCompletions x i = (x i : Completion (A i)) := by
  induction x using DirectSum.induction_on with
  | zero => simp only [map_zero, DFinsupp.zero_apply, Completion.coe_zero]
  | of j a =>
    change directSumToCoordinateCompletions (DirectSum.lof ℂ I A j a) i =
      ((DirectSum.lof ℂ I A j a) i : Completion (A i))
    rw [directSumToCoordinateCompletions_lof]
    by_cases h : j = i
    · subst j
      simp [DirectSum.lof_eq_of, DirectSum.of_eq_same]
    · simp only [DirectSum.lof_eq_of, DirectSum.of_eq_of_ne j i _ (Ne.symm h), Completion.coe_zero]
  | add x y hx hy => rw [map_add, DFinsupp.add_apply, DFinsupp.add_apply, Completion.coe_add, hx, hy]

omit [∀ i, PolynormableSpace ℂ (A i)] in
private theorem directSumToCoordinateCompletions_continuous :
    Continuous (directSumToCoordinateCompletions (A := A)) := by
  let j := DirectSum.lof ℂ I A
  let k := DirectSum.lof ℂ I (fun i => Completion (A i))
  letI : PolynormableSpace ℂ (⨁ i, Completion (A i)) :=
    (locallyConvexFinal_withSeminorms k).toPolynormableSpace
  apply (locallyConvexFinal_continuous_iff j _).mpr
  intro i
  exact ((locallyConvexFinal_stage_continuous k i).comp (Completion.continuous_coe (A i))).congr
    fun x => (directSumToCoordinateCompletions_lof i x).symm

omit [∀ i, PolynormableSpace ℂ (A i)] in
private theorem directSumToCoordinateCompletions_dense :
    DenseRange (directSumToCoordinateCompletions (A := A)) := by
  let k := DirectSum.lof ℂ I (fun i => Completion (A i))
  let L := directSumToCoordinateCompletions (A := A)
  letI : ContinuousConstSMul ℂ (⨁ i, Completion (A i)) :=
    (locallyConvexSumStructure (A := fun i => Completion (A i))).constSmul
  intro x
  change x ∈ L.range.topologicalClosure
  induction x using DirectSum.induction_on with
  | zero => exact Submodule.zero_mem _
  | of i x =>
    change k i x ∈ L.range.topologicalClosure
    refine Completion.denseRange_coe.induction_on x
      (L.range.isClosed_topologicalClosure.preimage (locallyConvexFinal_stage_continuous k i)) ?_
    intro a
    apply Submodule.le_topologicalClosure
    exact ⟨DirectSum.lof ℂ I A i a, directSumToCoordinateCompletions_lof i a⟩
  | add x y hx hy => exact Submodule.add_mem _ hx hy

omit [∀ i, PolynormableSpace ℂ (A i)] in
private theorem directSumToCoordinateCompletions_inducing :
    IsInducing (directSumToCoordinateCompletions (A := A)) := by
  let L := directSumToCoordinateCompletions (A := A)
  let τ : TopologicalSpace (⨁ i, A i) := locallyConvexSumTopology A
  let τ' := TopologicalSpace.induced L
    (locallyConvexSumTopology (fun i => Completion (A i)))
  have h₁ : τ ≤ τ' := continuous_iff_le_induced.mp directSumToCoordinateCompletions_continuous
  have h₂ : τ' ≤ τ := by
    letI : TopologicalSpace (⨁ i, A i) := τ'
    letI : IsTopologicalAddGroup (⨁ i, A i) := topologicalAddGroup_induced L
    let j := DirectSum.lof ℂ I A
    apply continuous_id_iff_le.mp
    apply (@WithSeminorms.continuous_iff_continuous_comp ℂ ℂ (⨁ i, A i) (⨁ i, A i)
      _ _ _ _ _ _ _ (RingHom.id ℂ) _ _ τ' inferInstance τ
      (locallyConvexFinal_withSeminorms j) LinearMap.id).mpr
    intro Q
    let p := fun i => completeSeminorm (Q.val.comp (j i)) (Q.property i)
    have hp : Continuous (sumOfSeminorms p) :=
      sumOfSeminorms_continuous p fun i => completeSeminorm_continuous _ _
    have hL : Continuous L := continuous_induced_dom
    apply Seminorm.continuous_of_le (q := (sumOfSeminorms p).comp L) (hp.comp hL)
    intro x
    refine (seminorm_le_sumOfSeminorms Q.val x).trans ?_
    change (∑ i ∈ x.support, Q.val (j i (x i))) ≤ sumOfSeminorms p (L x)
    refine le_trans ?_ (sumOfSeminorms_bound p (L x) x.support)
    apply le_of_eq
    apply Finset.sum_congr rfl
    intro i _
    rw [directSumToCoordinateCompletions_coordinate, completeSeminorm_apply_coe]
    rfl
  exact @IsInducing.mk _ _ τ (locallyConvexSumTopology (fun i => Completion (A i))) L
    (le_antisymm h₁ h₂)

/-- Completion of the locally convex direct sum is the locally convex sum of
the separated coordinate completions. -/
def locallyConvexSumCompletionEquiv :
    (locallyConvexSumStructure (A := A)).Completed ≃L[ℂ] (⨁ i, Completion (A i)) := by
  let L := directSumToCoordinateCompletions (A := A)
  let T := (locallyConvexSumStructure (A := A)).Completed
  let U := (⨁ i, Completion (A i))
  letI : CompleteSpace U := locallyConvexSum_complete
  letI : T2Space U := locallyConvexSum_t2
  let pkg : AbstractCompletion (⨁ i, A i) :=
    { space := U
      coe := L
      uniformStruct := inferInstance
      complete := inferInstance
      separation := inferInstance
      isUniformInducing := AddMonoidHom.isUniformInducing_of_isInducing
        (f := L.toAddMonoidHom) directSumToCoordinateCompletions_inducing
      dense := directSumToCoordinateCompletions_dense }
  let e : T ≃ᵤ U := (Completion.cPkg (α := (⨁ i, A i))).compareEquiv pkg
  have he (x : (⨁ i, A i)) : e (x : T) = L x :=
    Completion.cPkg.compare_coe pkg x
  letI : UniformContinuousConstSMul ℂ (⨁ i, A i) :=
    (locallyConvexSumStructure (A := A)).uniformConstSmul
  letI : IsUniformAddGroup T := @Completion.isUniformAddGroup (⨁ i, A i)
    (locallyConvexSumStructure (A := A)).uniformSpace _ (locallyConvexSumStructure (A := A)).uniformGroup
  letI : UniformContinuousConstSMul ℂ T :=
    @Completion.instUniformContinuousConstSMul ℂ (⨁ i, A i)
      (locallyConvexSumStructure (A := A)).uniformSpace _
  letI : ContinuousConstSMul ℂ U :=
    (locallyConvexSumStructure (A := fun i => Completion (A i))).constSmul
  refine ⟨{ e.toEquiv with map_add' := ?_, map_smul' := ?_ },
    e.continuous, e.symm.continuous⟩
  · intro x y
    refine Completion.denseRange_coe.induction_on₂
      (p := fun x y : T => e (x + y) = e x + e y) ?_ ?_ x y
    · exact isClosed_eq (e.continuous.comp (continuous_fst.add continuous_snd))
        ((e.continuous.comp continuous_fst).add (e.continuous.comp continuous_snd))
    · intro a b
      rw [← Completion.coe_add, he, he, he, map_add]
  · intro c x
    refine Completion.denseRange_coe.induction_on x
      (isClosed_eq (e.continuous.comp (continuous_const_smul c))
        (e.continuous.const_smul c)) ?_
    intro a
    change e (c • (a : T)) = c • e (a : T)
    rw [← Completion.coe_smul, he, he, map_smul]

theorem locallyConvexSumCompletionEquiv_incl (x : ⨁ i, A i) :
    locallyConvexSumCompletionEquiv ((locallyConvexSumStructure (A := A)).incl x) =
      directSumToCoordinateCompletions x :=
  show Completion.cPkg.compare _ (Completion.cPkg.coe x) = _ from
    Completion.cPkg.compare_coe _ x

end Topology

/-- Taking the locally convex direct sum of subspaces gives the topology
induced from the locally convex direct sum of the ambient spaces. -/
theorem locallyConvexSum_submodule_isInducing [∀ i, TopologicalSpace (A i)]
    [∀ i, IsTopologicalAddGroup (A i)]
    [∀ i, PolynormableSpace ℂ (A i)] (P : ∀ i, Submodule ℂ (A i)) :
    @IsInducing (⨁ i, P i) (⨁ i, A i)
      (locallyConvexSumTopology (fun i ↦ P i)) (locallyConvexSumTopology A)
      (DFinsupp.mapRange.linearMap (fun i ↦ (P i).subtype)) := by
  letI (i : I) (x : P i) : Decidable (x ≠ 0) := Classical.propDecidable _
  let j := DirectSum.lof ℂ I (fun i ↦ P i)
  let k := DirectSum.lof ℂ I A
  let L : (⨁ i, P i) →ₗ[ℂ] ⨁ i, A i := DFinsupp.mapRange.linearMap (fun i ↦ (P i).subtype)
  let τ : TopologicalSpace (⨁ i, P i) := locallyConvexSumTopology (fun i ↦ P i)
  letI : TopologicalSpace (⨁ i, A i) := locallyConvexSumTopology A
  letI : PolynormableSpace ℂ (⨁ i, A i) := (locallyConvexFinal_withSeminorms k).toPolynormableSpace
  let τ' := TopologicalSpace.induced L (locallyConvexSumTopology A)
  have hL : Continuous[τ, locallyConvexSumTopology A] L := by
    apply (locallyConvexFinal_continuous_iff j L).mpr
    intro i
    refine ((locallyConvexFinal_stage_continuous k i).comp continuous_subtype_val).congr fun x ↦ ?_
    change DFinsupp.single i x.val = L (DFinsupp.single i x)
    exact (DFinsupp.mapRange_single (f := fun i (z : P i) ↦ z.val)
      (hf := fun _ ↦ rfl) (i := i) (b := x)).symm
  have h₁ : τ ≤ τ' := continuous_iff_le_induced.mp hL
  have h₂ : τ' ≤ τ := by
    letI : TopologicalSpace (⨁ i, P i) := τ'
    letI : IsTopologicalAddGroup (⨁ i, P i) := topologicalAddGroup_induced L
    apply continuous_id_iff_le.mp
    apply (@WithSeminorms.continuous_iff_continuous_comp ℂ ℂ (⨁ i, P i) (⨁ i, P i)
      _ _ _ _ _ _ _ (RingHom.id ℂ) _ _ τ' inferInstance τ
      (locallyConvexFinal_withSeminorms j) LinearMap.id).mpr
    intro Q
    have hQ (i : I) : ∃ p : Seminorm ℂ (A i), Continuous p ∧
        Q.val.comp (j i) ≤ p.comp (P i).subtype :=
      Seminorm.exists_le_comp_of_isInducing (Q.property i) IsInducing.subtypeVal
    choose p hp hdom using hQ
    have hP : Continuous (sumOfSeminorms p) := by
      apply locallyConvexFinal_seminorm_continuous k
      intro i
      exact (hp i).congr fun x ↦ (sumOfSeminorms_lof p i x).symm
    have hLc : Continuous L := continuous_induced_dom
    apply Seminorm.continuous_of_le (q := (sumOfSeminorms p).comp L) (hP.comp hLc)
    intro x
    refine (seminorm_le_sumOfSeminorms Q.val x).trans ?_
    rw [sumOfSeminorms_apply_of_subset _ x x.support (Finset.Subset.refl _)]
    change (∑ i ∈ x.support, Q.val (j i (x i))) ≤ sumOfSeminorms p (L x)
    refine (Finset.sum_le_sum fun i _ ↦ hdom i (x i)).trans ?_
    exact sumOfSeminorms_bound p (L x) x.support
  exact @IsInducing.mk _ _ τ (locallyConvexSumTopology A) L (le_antisymm h₁ h₂)

end
end Masullo
