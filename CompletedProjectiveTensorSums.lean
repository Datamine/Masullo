import LocallyConvexSumCompletion
import InductiveTensorTopology
import InjectiveTensorMaps
import ProjectiveTensorQuotients
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.LinearAlgebra.TensorProduct.Finiteness

open Filter Function Set Topology UniformSpace
open scoped ComplexOrder DirectSum TensorProduct

namespace Masullo

noncomputable section

private def completionCongr {X Y : Type*} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y]
    [Module ℂ Y] (D : TopologicalModuleStructure X) (E : TopologicalModuleStructure Y)
    (e : letI : TopologicalSpace X := D.topology
         letI : TopologicalSpace Y := E.topology
         X ≃L[ℂ] Y) :
    D.Completed ≃L[ℂ] E.Completed := by
  letI : UniformSpace X := D.uniformSpace
  letI : IsUniformAddGroup X := D.uniformGroup
  letI : UniformContinuousConstSMul ℂ X := D.uniformConstSmul
  letI : UniformSpace Y := E.uniformSpace
  letI : IsUniformAddGroup Y := E.uniformGroup
  letI : UniformContinuousConstSMul ℂ Y := E.uniformConstSmul
  let f := e.toContinuousLinearMap.completion
  let g := e.symm.toContinuousLinearMap.completion
  refine ContinuousLinearEquiv.equivOfInverse f g ?_ ?_
  · intro x
    refine Completion.denseRange_coe.induction_on x
      (isClosed_eq (g.continuous.comp f.continuous) continuous_id) ?_
    intro a
    change g (f (a : Completion X)) = (a : Completion X)
    dsimp only [f, g]
    rw [ContinuousLinearMap.completion_apply_coe, ContinuousLinearMap.completion_apply_coe]
    exact congrArg Completion.coe' (e.symm_apply_apply a)
  · intro y
    refine Completion.denseRange_coe.induction_on y
      (isClosed_eq (f.continuous.comp g.continuous) continuous_id) ?_
    intro b
    change f (g (b : Completion Y)) = (b : Completion Y)
    dsimp only [f, g]
    rw [ContinuousLinearMap.completion_apply_coe, ContinuousLinearMap.completion_apply_coe]
    exact congrArg Completion.coe' (e.apply_symm_apply b)


private theorem completionCongr_incl {X Y : Type*} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y]
    [Module ℂ Y] (D : TopologicalModuleStructure X) (E : TopologicalModuleStructure Y)
    (e : letI : TopologicalSpace X := D.topology
         letI : TopologicalSpace Y := E.topology
         X ≃L[ℂ] Y) (x : X) :
    completionCongr D E e (D.incl x) = E.incl (e x) := by
  letI : UniformSpace X := D.uniformSpace
  letI : IsUniformAddGroup X := D.uniformGroup
  letI : UniformContinuousConstSMul ℂ X := D.uniformConstSmul
  letI : UniformSpace Y := E.uniformSpace
  letI : IsUniformAddGroup Y := E.uniformGroup
  letI : UniformContinuousConstSMul ℂ Y := E.uniformConstSmul
  exact ContinuousLinearMap.completion_apply_coe e.toContinuousLinearMap x

variable (I : Type*) [DecidableEq I] (A : I → Type*)
  [∀ i, AddCommGroup (A i)] [∀ i, Module ℂ (A i)] [∀ i, TopologicalSpace (A i)]
  [∀ i, PolynormableSpace ℂ (A i)]
  (F : Type*) [NormedAddCommGroup F] [NormedSpace ℂ F]

private abbrev Stage (i : I) := projectiveTensorModuleStructure (A i) F

private abbrev stageSumStructure : TopologicalModuleStructure (⨁ i, A i ⊗[ℂ] F) :=
  letI : ∀ i, UniformSpace (A i ⊗[ℂ] F) := fun i => (Stage I A F i).uniformSpace
  locallyConvexSumStructure

private abbrev sumTensorStructure : TopologicalModuleStructure ((⨁ i, A i) ⊗[ℂ] F) :=
  letI : TopologicalSpace (⨁ i, A i) := locallyConvexSumTopology A
  projectiveTensorModuleStructure _ F

/-- C.2.3.9(1), completed tensors. The canonical isomorphism commutes with
the inclusions of the tensor products of the individual summands. -/
def completedProjectiveTensorDirectSum :
    letI : TopologicalSpace (⨁ i, (Stage I A F i).Completed) :=
      locallyConvexSumTopology (fun i => (Stage I A F i).Completed)
    (⨁ i, (Stage I A F i).Completed) ≃L[ℂ] (sumTensorStructure I A F).Completed := by
  letI : ∀ i, UniformSpace (A i ⊗[ℂ] F) := fun i => (Stage I A F i).uniformSpace
  letI : ∀ i, IsUniformAddGroup (A i ⊗[ℂ] F) := fun i => (Stage I A F i).uniformGroup
  letI : ∀ i, UniformContinuousConstSMul ℂ (A i ⊗[ℂ] F) :=
    fun i => (Stage I A F i).uniformConstSmul
  letI : ∀ i, PolynormableSpace ℂ (A i ⊗[ℂ] F) :=
    fun i => projectiveTensor_withSeminorms.toPolynormableSpace
  letI : TopologicalSpace (⨁ i, (Stage I A F i).Completed) :=
    locallyConvexSumTopology (fun i => (Stage I A F i).Completed)
  let e := locallyConvexSumCompletionEquiv (A := fun i => A i ⊗[ℂ] F)
  exact e.symm.trans (completionCongr (stageSumStructure I A F) (sumTensorStructure I A F)
    (projectiveTensorDirectSum I A F))


theorem completedProjectiveTensorDirectSum_incl (i : I) (x : A i) (y : F) :
    completedProjectiveTensorDirectSum I A F
      (DirectSum.lof ℂ I (fun i => (Stage I A F i).Completed) i
        ((Stage I A F i).incl (x ⊗ₜ[ℂ] y))) =
      (sumTensorStructure I A F).incl (DirectSum.lof ℂ I A i x ⊗ₜ[ℂ] y) := by
  letI : ∀ i, UniformSpace (A i ⊗[ℂ] F) := fun i => (Stage I A F i).uniformSpace
  letI : ∀ i, IsUniformAddGroup (A i ⊗[ℂ] F) := fun i => (Stage I A F i).uniformGroup
  letI : ∀ i, UniformContinuousConstSMul ℂ (A i ⊗[ℂ] F) :=
    fun i => (Stage I A F i).uniformConstSmul
  letI : ∀ i, PolynormableSpace ℂ (A i ⊗[ℂ] F) :=
    fun i => projectiveTensor_withSeminorms.toPolynormableSpace
  letI : TopologicalSpace (⨁ i, (Stage I A F i).Completed) :=
    locallyConvexSumTopology (fun i => (Stage I A F i).Completed)
  let q := DirectSum.lof ℂ I (fun i => A i ⊗[ℂ] F) i (x ⊗ₜ[ℂ] y)
  let e := locallyConvexSumCompletionEquiv (A := fun i => A i ⊗[ℂ] F)
  have he : e ((stageSumStructure I A F).incl q) =
      DirectSum.lof ℂ I (fun i => (Stage I A F i).Completed) i
        ((Stage I A F i).incl (x ⊗ₜ[ℂ] y)) := by
    rw [locallyConvexSumCompletionEquiv_incl, directSumToCoordinateCompletions_lof]
    rfl
  rw [← he]
  change completionCongr (stageSumStructure I A F) (sumTensorStructure I A F)
      (projectiveTensorDirectSum I A F) (e.symm (e ((stageSumStructure I A F).incl q))) = _
  rw [e.symm_apply_apply]
  exact (completionCongr_incl (stageSumStructure I A F) (sumTensorStructure I A F)
    (projectiveTensorDirectSum I A F) q).trans
    (congrArg (sumTensorStructure I A F).incl (projectiveTensorDirectSum_lof_tmul i x y))


section Series

variable {E F : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
  [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]

private abbrev SeriesTensor (E F : Type*) [AddCommGroup E] [Module ℂ E]
    [AddCommGroup F] [Module ℂ F] := E ⊗[ℂ] F

local instance : UniformSpace (SeriesTensor E F) :=
  (projectiveTensorModuleStructure E F).uniformSpace

local instance : IsUniformAddGroup (SeriesTensor E F) :=
  (projectiveTensorModuleStructure E F).uniformGroup

local instance : PolynormableSpace ℂ (SeriesTensor E F) :=
  (projectiveTensor_withSeminorms (E := E) (F := F)).toPolynormableSpace

local instance : UniformContinuousConstSMul ℂ (SeriesTensor E F) :=
  (projectiveTensorModuleStructure E F).uniformConstSmul

local instance : IsUniformAddGroup (Completion (SeriesTensor E F)) :=
  Completion.isUniformAddGroup

local instance : IsTopologicalAddGroup (Completion (SeriesTensor E F)) :=
  inferInstance

local instance : CompleteSpace (Completion (SeriesTensor E F)) :=
  Completion.completeSpace (SeriesTensor E F)

omit [TopologicalSpace E] [TopologicalSpace F] in
open scoped Pointwise in
/-- A tensor in a scaled absolutely convex hull has a finite expansion with coefficient
norms totaling at most the norm of the scale. -/
private theorem projectiveTensor_finite_expansion {U : Set E} {V : Set F}
    (r : ℂ) {w : E ⊗[ℂ] F}
    (hw : w ∈ absConvexHull ℂ (image2 (TensorProduct.tmul ℂ) U V)) :
    ∃ (k : ℕ) (c : Fin k → ℂ) (x : Fin k → E) (y : Fin k → F),
      (∀ i, x i ∈ U ∧ y i ∈ V) ∧ (∑ i, ‖c i‖) ≤ ‖r‖ ∧
        (∑ i, c i • (x i ⊗ₜ[ℂ] y i)) = r • w := by
  classical
  let T := E ⊗[ℂ] F
  let : Module ℝ T := Module.restrictScalars ℝ ℂ T
  let : IsScalarTower ℝ ℂ T := IsScalarTower.restrictScalars ℝ ℂ T
  let S : Set T := image2 (TensorProduct.tmul ℂ) U V
  change (w : T) ∈ absConvexHull ℂ S at hw
  rw [absConvexHull_eq_convexHull_balancedHull] at hw
  have hsub : convexHull ℂ (balancedHull ℂ S) ⊆ convexHull ℝ (balancedHull ℂ S) :=
    convexHull_min (subset_convexHull ℝ _) (convex_of_nonneg_surjective_algebraMap ℂ
      (fun _ => (RCLike.nonneg_iff_exists_ofReal (K := ℂ)).mp) (convex_convexHull ℝ _))
  have hw' := hsub hw
  obtain ⟨ι, hι, a, t, ha, hasum, ht, hsum⟩ := mem_convexHull_iff_exists_fintype.mp hw'
  let := hι
  choose b hb ht' using fun i ↦ mem_balancedHull_iff.mp (ht i)
  choose u hu htu using fun i ↦ mem_smul_set.mp (ht' i)
  choose x hx y hy hxy using fun i ↦ mem_image2.mp (hu i)
  let e := (Fintype.equivFin ι).symm
  let c (i : ι) := r * (a i : ℂ) * b i
  refine ⟨Fintype.card ι, c ∘ e, x ∘ e, y ∘ e, fun i ↦ ⟨hx _, hy _⟩, ?_, ?_⟩
  · rw [show (∑ i, ‖(c ∘ e) i‖) = ∑ i, ‖c i‖ from e.sum_comp (fun i ↦ ‖c i‖)]
    calc
      ∑ i, ‖c i‖ ≤ ∑ i, ‖r‖ * a i := Finset.sum_le_sum fun i _ ↦ by
        rw [show ‖c i‖ = ‖r‖ * a i * ‖b i‖ by
          simp [c, Complex.norm_real, Real.norm_of_nonneg (ha i)]]
        exact mul_le_of_le_one_right (mul_nonneg (norm_nonneg _) (ha i)) (hb i)
      _ = ‖r‖ := by rw [← Finset.mul_sum, hasum, mul_one]
  · rw [show (∑ i, (c ∘ e) i • ((x ∘ e) i ⊗ₜ[ℂ] (y ∘ e) i)) =
        ∑ i, c i • (x i ⊗ₜ[ℂ] y i) from e.sum_comp (fun i ↦ c i • (x i ⊗ₜ[ℂ] y i))]
    calc
      ∑ i, c i • (x i ⊗ₜ[ℂ] y i) = ∑ i, r • (a i • t i) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hxy i, ← htu i]
        change (r * (a i : ℂ) * b i) • u i = r • ((a i : ℂ) • (b i • u i))
        simp only [mul_smul]
      _ = r • (∑ i, a i • t i) := Finset.smul_sum.symm
      _ = r • (w : T) := congrArg (fun v : T ↦ r • v) hsum

/-- A point in the completion can be approximated so that each successive difference lies
in a prescribed zero-neighborhood of the algebraic projective tensor. -/
private theorem projectiveTensor_controlled_approximation
    (z : Completion (SeriesTensor E F)) {W A : ℕ → Set (SeriesTensor E F)}
    (hW : (𝓝 0).HasAntitoneBasis W) (hA : ∀ n, A n ∈ 𝓝 0) :
    ∃ a : ℕ → SeriesTensor E F, Tendsto (fun n ↦ Completion.coe' (a n)) atTop (𝓝 z) ∧
      ∀ n, a (n + 1) - a n ∈ A n := by
  let T := SeriesTensor E F
  let j : T →+ Completion T := Completion.toCompl
  have hj : IsDenseInducing j := Completion.isDenseInducing_coe
  have hlift (n : ℕ) : ∃ P ∈ 𝓝 (0 : Completion T), j ⁻¹' P ⊆ A n := by
    have h := hA n
    rw [hj.nhds_eq_comap, map_zero j, mem_comap] at h
    exact h
  choose P hP hPA using hlift
  have hsmall (n : ℕ) : ∃ D ∈ 𝓝 (0 : Completion T),
      (∀ x ∈ D, ∀ y ∈ D, x - y ∈ P n) ∧ D ⊆ closure (j '' W n) := by
    have hsub : (fun v : Completion T × Completion T ↦ v.1 - v.2) ⁻¹' P n ∈
        𝓝 ((0 : Completion T), 0) :=
      (continuous_fst.sub continuous_snd).continuousAt.preimage_mem_nhds (by simpa using hP n)
    obtain ⟨U, hU, V, hV, hUV⟩ := mem_nhds_prod_iff.mp hsub
    have hcl : closure (j '' W n) ∈ 𝓝 (0 : Completion T) := by
      simpa only [map_zero] using hj.closure_image_mem_nhds (hW.1.mem_of_mem (i := n) trivial)
    refine ⟨(U ∩ V) ∩ closure (j '' W n), inter_mem (inter_mem hU hV) hcl, ?_, fun _ h ↦ h.2⟩
    exact fun x hx y hy ↦ hUV (a := (x, y)) ⟨hx.1.1, hy.1.2⟩
  choose D hD hsub hcl using hsmall
  have hnear (n : ℕ) : ∃ a : T, j a - z ∈ D n ∩ D (n - 1) := by
    change ∃ a : T, j a ∈ (fun q : Completion T ↦ q - z) ⁻¹' (D n ∩ D (n - 1))
    apply hj.dense.mem_nhds (x := z)
    rw [← nhds_translation_sub z]
    exact preimage_mem_comap (inter_mem (hD n) (hD (n - 1)))
  choose a ha using hnear
  refine ⟨a, tendsto_sub_nhds_zero_iff.mp ?_, fun n ↦ hPA n ?_⟩
  · refine tendsto_def.mpr fun S hS ↦ ?_
    obtain ⟨C, hC, hc, hCS⟩ := exists_mem_nhds_isClosed_subset hS
    have hpre : j ⁻¹' C ∈ 𝓝 (0 : T) :=
      Completion.continuous_toCompl.continuousAt.preimage_mem_nhds (by simpa only [map_zero] using hC)
    obtain ⟨N, hN⟩ := hW.mem_iff.mp hpre
    refine eventually_atTop.mpr ⟨N, fun n hn ↦ hCS (closure_minimal ?_ hc (hcl n (ha n).1))⟩
    exact image_subset_iff.mpr ((hW.antitone hn).trans hN)
  · change j (a (n + 1) - a n) ∈ P n
    rw [map_sub, ← sub_sub_sub_cancel_right (j (a (n + 1))) (j (a n)) z]
    exact hsub n _ (by simpa using (ha (n + 1)).2) _ (ha n).1

/-- Absolutely summable coefficients give a summable series of pure tensors when both
families of factors tend to zero along the cofinite filter. -/
private theorem completedProjectiveTensor_summable_cofinite
    [IsTopologicalAddGroup E] [IsTopologicalAddGroup F] {ι : Type*}
    (c : ι → ℂ) (x : ι → E) (y : ι → F) (hc : Summable (fun i ↦ ‖c i‖))
    (hxy : Tendsto (fun i ↦ (x i, y i)) cofinite (𝓝 0)) :
    Summable (fun i ↦ (Completion.coe' (α := SeriesTensor E F) (c i • (x i ⊗ₜ[ℂ] y i)))) := by
  let T := SeriesTensor E F
  let t (i : ι) : T := x i ⊗ₜ[ℂ] y i
  have ht : Tendsto t cofinite (𝓝 0) := by
    have h := (continuous_projectiveTensor_tmul (E := E) (F := F)).continuousAt (x := 0)
    have h' := h.tendsto.comp hxy
    rw [show ((0 : E × F).1 ⊗ₜ[ℂ] (0 : E × F).2 : SeriesTensor E F) = 0 from
      TensorProduct.zero_tmul _ _] at h'
    exact h'
  apply summable_iff_cauchySeq_finset.mpr
  suffices h : CauchySeq (fun s : Finset ι ↦ ∑ i ∈ s, c i • t i) by
    have h' : CauchySeq (fun s : Finset ι ↦ Completion.toCompl (∑ i ∈ s, c i • t i)) :=
      (Completion.uniformContinuous_coe T).comp_cauchySeq h
    simp only [map_sum] at h'
    exact h'
  refine cauchySeq_finset_iff_sum_vanishing.mpr fun S hS ↦ ?_
  let hW := PolynormableSpace.withSeminorms ℂ T
  obtain ⟨⟨J, ε⟩, hε, hpS⟩ := hW.hasBasis_zero_ball.mem_iff.mp hS
  let p := J.sup (fun q : {q : Seminorm ℂ T // Continuous q} => q.val)
  have hp : Continuous p := Seminorm.continuous_finsetSup fun q _ => q.property
  have hpt : Tendsto (fun i ↦ p (t i)) cofinite (𝓝 0) :=
    (hp.tendsto' 0 0 (map_zero p)).comp ht
  obtain ⟨M, hM⟩ := hpt.bddAbove_range_of_cofinite
  have hmajor := hc.mul_left (max M 0)
  obtain ⟨s, hs⟩ := cauchySeq_finset_iff_sum_vanishing.mp (summable_iff_cauchySeq_finset.mp hmajor)
    (Iio ε) (Iio_mem_nhds hε)
  refine ⟨s, fun u hu ↦ hpS (p.mem_ball_zero.mpr (lt_of_le_of_lt ?_ (hs u hu)))⟩
  calc
    p (∑ i ∈ u, c i • t i) ≤ ∑ i ∈ u, p (c i • t i) :=
      Finset.le_sum_of_subadditive p (map_zero p).le (map_add_le_add p) _ _
    _ ≤ ∑ i ∈ u, max M 0 * ‖c i‖ := Finset.sum_le_sum fun i _ ↦ by
      rw [map_smul_eq_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right ((hM (mem_range_self i)).trans (le_max_left _ _)) (norm_nonneg _)

/-- The convergence direction of (C.2.3.16). An absolutely summable coefficient
sequence and null factor sequences give a summable series in the actual
completed projective tensor product. The seminorm argument adapts the Apache-2.0
RiemannMasullo project at commit 8ce82125e6e90415b4bfa0e2ffaaf6b11bb38897. -/
theorem completedProjectiveTensor_summable_series
    {E F : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
    (c : ℕ → ℂ) (x : ℕ → E) (y : ℕ → F) (hc : Summable (fun n => ‖c n‖))
    (hx : Tendsto x atTop (𝓝 0)) (hy : Tendsto y atTop (𝓝 0)) :
    Summable (fun n => (projectiveTensorModuleStructure E F).incl (c n • (x n ⊗ₜ[ℂ] y n))) := by
  have hxy : Tendsto (fun n ↦ (x n, y n)) cofinite (𝓝 (0 : E × F)) := by
    rw [Nat.cofinite_eq_atTop]
    exact hx.prodMk_nhds hy
  exact completedProjectiveTensor_summable_cofinite c x y hc hxy

set_option maxHeartbeats 1200000 in
/-- Paper: (C.2.3.16), p. 679. Every member of the completed projective tensor of Fréchet
spaces is an absolutely weighted sum of pure tensors from two null sequences.
The proof adapts the Apache-2.0 RiemannMasullo argument at commit 82b65fa. -/
theorem completedProjectiveTensor_exists_series [PolynormableSpace ℂ E] [PolynormableSpace ℂ F]
    [FirstCountableTopology E] [FirstCountableTopology F]
    (z : (projectiveTensorModuleStructure E F).Completed) :
    ∃ (c : ℕ → ℂ) (x : ℕ → E) (y : ℕ → F), Summable (fun n ↦ ‖c n‖) ∧
      Tendsto x atTop (𝓝 0) ∧ Tendsto y atTop (𝓝 0) ∧
      HasSum (fun n ↦ (projectiveTensorModuleStructure E F).incl (c n • (x n ⊗ₜ[ℂ] y n))) z := by
  classical
  letI : IsTopologicalAddGroup E := (PolynormableSpace.withSeminorms ℂ E).topologicalAddGroup
  letI : IsTopologicalAddGroup F := (PolynormableSpace.withSeminorms ℂ F).topologicalAddGroup
  obtain ⟨U, hU⟩ := (𝓝 (0 : E)).exists_antitone_basis
  obtain ⟨V, hV⟩ := (𝓝 (0 : F)).exists_antitone_basis
  let T := SeriesTensor E F
  let j : T →+ Completion T := Completion.toCompl
  let W (n : ℕ) : Set T := absConvexHull ℂ (image2 (TensorProduct.tmul ℂ) (U n) (V n))
  have hmono {m n : ℕ} (hmn : m ≤ n) : W n ⊆ W m :=
    absConvexHull_mono (image2_subset (hU.antitone hmn) (hV.antitone hmn))
  have hW : (𝓝 (0 : T)).HasAntitoneBasis W := by
    refine ⟨(elementaryTensorHull_basis hU.1 hV.1).to_hasBasis ?_ ?_, fun _ _ ↦ hmono⟩
    · rintro ⟨i, k⟩ _
      exact ⟨max i k, trivial,
        absConvexHull_mono (image2_subset (hU.antitone (le_max_left _ _)) (hV.antitone (le_max_right _ _)))⟩
    · exact fun n _ ↦ ⟨(n, n), ⟨trivial, trivial⟩, Subset.rfl⟩
  let r (n : ℕ) : ℂ := (1 / 2) ^ n
  have hr (n : ℕ) : r n ≠ 0 := by
    change ((1 / 2 : ℂ) ^ n) ≠ 0
    positivity
  let A (n : ℕ) : Set T := (fun w : T ↦ (r n)⁻¹ • w) ⁻¹' W n
  letI : ContinuousSMul ℂ T := (PolynormableSpace.withSeminorms ℂ T).continuousSMul
  have hA (n : ℕ) : A n ∈ 𝓝 (0 : T) :=
    (continuous_const_smul (r n)⁻¹).continuousAt.preimage_mem_nhds (by
      rw [smul_zero]
      exact hW.1.mem_of_mem (i := n) trivial)
  obtain ⟨a, ha, hadiff⟩ := projectiveTensor_controlled_approximation z hW hA
  let b : ℕ → T := fun n ↦ Nat.casesOn n 0 a
  have hb : Tendsto (fun n ↦ j (b n)) atTop (𝓝 z) :=
    (tendsto_add_atTop_iff_nat 1).mp ha
  -- The first approximant contributes one unrestricted finite block.
  have hblocks (n : ℕ) : ∃ (k : ℕ) (c : Fin k → ℂ) (x : Fin k → E) (y : Fin k → F),
      (∀ m, n = m + 1 → (∀ i, x i ∈ U m ∧ y i ∈ V m) ∧ (∑ i, ‖c i‖) ≤ ‖r m‖) ∧
        (∑ i, c i • (x i ⊗ₜ[ℂ] y i) : T) = b (n + 1) - b n := by
    cases n with
    | zero =>
      obtain ⟨k, x, y, h⟩ := TensorProduct.exists_sum_tmul_eq (a 0)
      refine ⟨k, fun _ ↦ 1, x, y, by simp, ?_⟩
      simp only [one_smul]
      change (∑ i, x i ⊗ₜ[ℂ] y i) = a 0 - (0 : T)
      rw [sub_zero]
      exact h.symm
    | succ n =>
      let w : E ⊗[ℂ] F := a (n + 1) - a n
      obtain ⟨k, c, x, y, hxy, hnorm, hsum⟩ :=
        projectiveTensor_finite_expansion (r n) (w := (r n)⁻¹ • w) (hadiff n)
      refine ⟨k, c, x, y, fun m hm ↦ ?_, ?_⟩
      · obtain rfl : n = m := Nat.succ.inj hm
        exact ⟨hxy, hnorm⟩
      · exact hsum.trans (smul_inv_smul₀ (hr n) w)
  choose k c x y hsmall hsum using hblocks
  let ι := Σ n, Fin (k n)
  let coeff (i : ι) := c i.1 i.2
  let left (i : ι) := x i.1 i.2
  let right (i : ι) := y i.1 i.2
  have hc : Summable (fun i ↦ ‖coeff i‖) := by
    refine (summable_sigma_of_nonneg (fun i ↦ norm_nonneg (coeff i))).mpr ⟨fun n ↦ (hasSum_fintype _).summable, ?_⟩
    apply (summable_nat_add_iff 1).mp
    simp only [tsum_fintype]
    have hrSum : Summable (fun n ↦ ‖r n‖) := by
      simp only [r, norm_pow]
      apply summable_geometric_of_norm_lt_one
      rw [Real.norm_of_nonneg (norm_nonneg (_ : ℂ)), norm_div, norm_one]
      norm_num
    exact hrSum.of_nonneg_of_le
      (fun n ↦ Finset.sum_nonneg fun i _ ↦ norm_nonneg _) (fun n ↦ (hsmall (n + 1) n rfl).2)
  have hindex : Tendsto (Sigma.fst : ι → ℕ) cofinite atTop := by
    refine tendsto_atTop.mpr fun N ↦ eventually_cofinite.mpr ?_
    refine ((finite_lt_nat N).biUnion
      (t := fun n ↦ range (fun i : Fin (k n) ↦ (⟨n, i⟩ : ι))) fun n _ ↦ finite_range _).subset ?_
    rintro ⟨n, i⟩ hi
    exact mem_iUnion₂.mpr ⟨n, Nat.lt_of_not_ge hi, i, rfl⟩
  have hxy : Tendsto (fun i ↦ (left i, right i)) cofinite (𝓝 0) := by
    rw [show (0 : E × F) = (0, 0) from rfl, nhds_prod_eq]
    refine (hU.1.prod hV.1).tendsto_right_iff.mpr ?_
    rintro ⟨N, M⟩ _
    filter_upwards [tendsto_atTop.mp hindex (max N M + 1)] with i hi
    rcases i with ⟨_ | n, i⟩
    · exact (Nat.not_succ_le_zero _ hi).elim
    · have hn := Nat.le_of_succ_le_succ hi
      obtain ⟨hx, hy⟩ := (hsmall (n + 1) n rfl).1 i
      exact ⟨hU.antitone ((le_max_left N M).trans hn) hx,
        hV.antitone ((le_max_right N M).trans hn) hy⟩
  let f (i : ι) := j (coeff i • (left i ⊗ₜ[ℂ] right i))
  have hf : Summable f := completedProjectiveTensor_summable_cofinite coeff left right hc hxy
  have hfiber (n : ℕ) : HasSum (fun i ↦ f ⟨n, i⟩) (j (b (n + 1)) - j (b n)) := by
    rw [← map_sub, ← hsum n]
    let g (i : Fin (k n)) : T := c n i • (x n i ⊗ₜ[ℂ] y n i)
    change HasSum (fun i ↦ j (g i)) (j (∑ i, g i))
    rw [map_sum]
    exact hasSum_fintype _
  have hgroup := hf.hasSum.sigma hfiber
  have hgroup' : HasSum (fun n ↦ j (b (n + 1)) - j (b n)) z := by
    apply hgroup.summable.hasSum_iff_tendsto_nat.mpr
    have htel (n : ℕ) :
        (∑ i ∈ Finset.range n, (j (b (i + 1)) - j (b i))) = j (b n) := by
      rw [Finset.sum_range_sub (fun i ↦ j (b i)), show j (b 0) = 0 from map_zero j, sub_zero]
    simpa only [htel] using hb
  have htotal := hgroup'.sigma_of_hasSum hfiber hf
  -- Embed the countable union of finite blocks into ℕ, padding unused indices with zeros.
  let encode : ι → ℕ := Encodable.encode
  have he : Function.Injective encode := Encodable.encode_injective
  let cn := Function.extend encode coeff 0
  let xy := Function.extend encode (fun i ↦ (left i, right i)) 0
  have hcn : Summable (fun n ↦ ‖cn n‖) := by
    refine (he.summable_iff (fun n hn ↦ ?_)).mp ?_
    · simp [cn, Function.extend_apply' _ _ _ hn]
    · simpa only [Function.comp_def, cn, he.extend_apply] using hc
  have hxyn : Tendsto xy atTop (𝓝 0) := by
    rw [← Nat.cofinite_eq_atTop]
    refine tendsto_def.mpr fun S hS ↦ eventually_cofinite.mpr ?_
    refine ((eventually_cofinite.mp (hxy.eventually_mem hS)).image encode).subset ?_
    intro n hn
    by_cases hn' : n ∈ range encode
    · obtain ⟨i, rfl⟩ := hn'
      change xy (encode i) ∉ S at hn
      simp only [xy, he.extend_apply] at hn
      exact ⟨i, hn, rfl⟩
    · change xy n ∉ S at hn
      simp only [xy, Function.extend_apply' _ _ _ hn', Pi.zero_apply] at hn
      exact (hn (mem_of_mem_nhds hS)).elim
  have hxyn' : Tendsto xy atTop (𝓝 (0 : E) ×ˢ 𝓝 (0 : F)) := by
    rw [← nhds_prod_eq]
    exact hxyn
  refine ⟨cn, fun n ↦ (xy n).1, fun n ↦ (xy n).2, hcn, hxyn'.fst, hxyn'.snd, ?_⟩
  refine (he.hasSum_iff (fun n hn ↦ ?_)).mp ?_
  · change j (cn n • ((xy n).1 ⊗ₜ[ℂ] (xy n).2)) = 0
    simp only [cn, Function.extend_apply' _ _ _ hn, Pi.zero_apply, zero_smul]
    exact map_zero j
  · simp only [Function.comp_def, cn, xy, he.extend_apply]
    exact htotal

end Series

section CompletionFactors

variable (E F : Type*) [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E]
  [UniformContinuousConstSMul ℂ E] [PolynormableSpace ℂ E]
  [AddCommGroup F] [Module ℂ F] [UniformSpace F] [IsUniformAddGroup F]
  [UniformContinuousConstSMul ℂ F] [PolynormableSpace ℂ F]

local instance (priority := 100) completionFactorPolynormable
    (V : Type*) [AddCommGroup V] [Module ℂ V] [UniformSpace V] [IsUniformAddGroup V]
    [UniformContinuousConstSMul ℂ V] [PolynormableSpace ℂ V] :
    PolynormableSpace ℂ (Completion V) := polynormableSpace_completion

-- The extension and inverse argument adapts mccorvie/riemann-masullo, f7abb54.

omit [PolynormableSpace ℂ E] [PolynormableSpace ℂ F] in
/-- The canonical bilinear map to the completed projective tensor product extends
jointly continuously to both completed factors. -/
private theorem exists_completedProjectiveTensor_bilinear :
    ∃ B : Completion E →ₗ[ℂ] Completion F →ₗ[ℂ] (projectiveTensorModuleStructure E F).Completed,
      Continuous (fun v : Completion E × Completion F ↦ B v.1 v.2) ∧
      ∀ (x : E) (y : F), B x y =
        (projectiveTensorModuleStructure E F).incl (x ⊗ₜ[ℂ] y) := by
  let X := E ⊗[ℂ] F
  let SX := projectiveTensorModuleStructure E F
  letI : UniformSpace X := SX.uniformSpace
  letI : IsUniformAddGroup X := SX.uniformGroup
  letI : UniformContinuousConstSMul ℂ X := SX.uniformConstSmul
  let G := Completion X
  letI : IsUniformAddGroup G := Completion.isUniformAddGroup
  letI : CompleteSpace G := Completion.completeSpace X
  letI : T0Space G := Completion.t0Space X
  letI : UniformContinuousConstSMul ℂ G := Completion.instUniformContinuousConstSMul ℂ X
  letI : ContinuousConstSMul ℂ G := UniformContinuousConstSMul.instContinuousConstSMul ℂ G
  let L : E →ₗ[ℂ] F →ₗ[ℂ] G :=
    (TensorProduct.mk ℂ E F).compr₂
      (completionInclusionL (V := X)).toLinearMap
  let A : E →+ F →+ G := LinearMap.toAddMonoidHom'.comp L.toAddMonoidHom
  have hA : Continuous (fun v : E × F ↦ A v.1 v.2) :=
    (Completion.continuous_coe X).comp continuous_projectiveTensor_tmul
  let de : IsDenseInducing ((↑) : E → Completion E) := Completion.isDenseInducing_coe
  let df : IsDenseInducing ((↑) : F → Completion F) := Completion.isDenseInducing_coe
  let b := (de.prodMap df).extend (fun v : E × F ↦ A v.1 v.2)
  have hb : Continuous b :=
    IsDenseInducing.extend_Z_bilin (G := G) (e := Completion.toCompl (α := E))
      (f := Completion.toCompl (α := F)) (φ := A) de df hA
  have hcoe (x : E) (y : F) : b (x, y) = L x y :=
    (de.prodMap df).extend_eq hA (x, y)
  -- Each bilinearity identity extends from the dense image by continuity.
  refine ⟨LinearMap.mk₂ ℂ (fun x y ↦ b (x, y)) ?_ ?_ ?_ ?_, hb, hcoe⟩
  · intro x x' y
    refine Completion.induction_on₃ x x' y (isClosed_eq ?_ ?_) fun a a' c ↦ ?_
    · exact hb.comp ((continuous_fst.add continuous_snd.fst).prodMk continuous_snd.snd)
    · exact (hb.comp (continuous_fst.prodMk continuous_snd.snd)).add
        (hb.comp (continuous_snd.fst.prodMk continuous_snd.snd))
    · rw [← Completion.coe_add a a']
      simp only [hcoe, map_add, LinearMap.add_apply]
  · intro c x y
    refine Completion.induction_on₂ x y (isClosed_eq ?_ ?_) fun a d ↦ ?_
    · exact hb.comp ((continuous_fst.const_smul c).prodMk continuous_snd)
    · exact hb.fun_const_smul c
    · rw [← Completion.coe_smul c a]
      simp only [hcoe, map_smul, LinearMap.smul_apply]
  · intro x y y'
    refine Completion.induction_on₃ x y y' (isClosed_eq ?_ ?_) fun a d d' ↦ ?_
    · exact hb.comp (continuous_fst.prodMk (continuous_snd.fst.add continuous_snd.snd))
    · exact (hb.comp (continuous_fst.prodMk continuous_snd.fst)).add
        (hb.comp (continuous_fst.prodMk continuous_snd.snd))
    · rw [← Completion.coe_add d d']
      simp only [hcoe, map_add]
  · intro c x y
    refine Completion.induction_on₂ x y (isClosed_eq ?_ ?_) fun a d ↦ ?_
    · exact hb.comp (continuous_fst.prodMk (continuous_snd.const_smul c))
    · exact hb.fun_const_smul c
    · rw [← Completion.coe_smul c d]
      simp only [hcoe, map_smul]

/-- Paper: §C.2.3.2, p. 679. Completing the two factors induces an isomorphism on
completed projective tensors. -/
theorem completedProjectiveTensor_completionFactors :
    IsHomeomorph (completedProjectiveTensorMap (completionInclusionL (V := E))
      (completionInclusionL (V := F))) := by
  let X := E ⊗[ℂ] F
  let Y := Completion E ⊗[ℂ] Completion F
  let SX := projectiveTensorModuleStructure E F
  let SY := projectiveTensorModuleStructure (Completion E) (Completion F)
  letI : UniformSpace X := SX.uniformSpace
  letI : IsUniformAddGroup X := SX.uniformGroup
  letI : UniformContinuousConstSMul ℂ X := SX.uniformConstSmul
  letI : UniformSpace Y := SY.uniformSpace
  letI : IsUniformAddGroup Y := SY.uniformGroup
  letI : UniformContinuousConstSMul ℂ Y := SY.uniformConstSmul
  letI : PolynormableSpace ℂ X := projectiveTensor_withSeminorms.toPolynormableSpace
  letI : PolynormableSpace ℂ (Completion X) := polynormableSpace_completion
  let i := completionInclusionL (V := E)
  let j := completionInclusionL (V := F)
  let T := TensorProduct.map i.toLinearMap j.toLinearMap
  have ht (x : E) (y : F) : T (x ⊗ₜ[ℂ] y) = (x : Completion E) ⊗ₜ[ℂ] (y : Completion F) :=
    TensorProduct.map_tmul _ _ _ _
  let forward : X →L[ℂ] Y := ⟨T, projectiveTensor_map_continuous i j⟩
  obtain ⟨B, hB, hcoe⟩ := exists_completedProjectiveTensor_bilinear E F
  let backward : Y →L[ℂ] Completion X :=
    ⟨TensorProduct.lift B,
      continuous_projectiveTensor_lift B hB⟩
  have hb (x : Completion E) (y : Completion F) : backward (x ⊗ₜ[ℂ] y) = B x y :=
    TensorProduct.lift.tmul (f' := B) x y
  letI : IsUniformAddGroup (Completion X) := Completion.isUniformAddGroup
  letI : CompleteSpace (Completion X) := Completion.completeSpace X
  have hunif : UniformContinuous backward :=
    uniformContinuous_addMonoidHom_of_continuous backward.continuous
  let extendBack : Completion Y → Completion X := Completion.extension backward
  have hBack : Continuous extendBack := Completion.continuous_extension
  have hBackCoe (z : Y) : extendBack (z : Completion Y) = backward z :=
    Completion.extension_coe hunif z
  change IsHomeomorph forward.completion
  refine isHomeomorph_iff_exists_inverse.mpr
    ⟨forward.completion.continuous, extendBack, ?_, ?_,
      hBack⟩
  · have hleft : backward.toLinearMap.comp T =
        (completionInclusionL (V := X)).toLinearMap := by
      apply TensorProduct.ext'
      intro x y
      change backward (T (x ⊗ₜ[ℂ] y)) = _
      rw [ht, hb]
      exact hcoe x y
    refine Completion.ext' (hBack.comp forward.completion.continuous)
      continuous_id fun z : X ↦ ?_
    simp only [ContinuousLinearMap.completion_apply_coe, hBackCoe]
    exact DFunLike.congr_fun hleft z
  · have hright : forward.completion.toLinearMap.comp backward.toLinearMap =
        (completionInclusionL (V := Y)).toLinearMap := by
      apply TensorProduct.ext'
      intro x y
      change forward.completion (backward (x ⊗ₜ[ℂ] y)) = Completion.coe' (α := Y) (x ⊗ₜ[ℂ] y)
      rw [hb]
      refine Completion.induction_on₂ x y
        (isClosed_eq (forward.completion.continuous.comp hB)
          ((Completion.continuous_coe Y).comp continuous_projectiveTensor_tmul)) fun a b ↦ ?_
      rw [hcoe]
      exact (forward.completion_apply_coe (a ⊗ₜ[ℂ] b)).trans
        (congrArg (Completion.coe' (α := Y)) (ht a b))
    refine Completion.ext' (forward.completion.continuous.comp hBack)
      continuous_id fun z : Y ↦ ?_
    simp only [hBackCoe]
    exact DFunLike.congr_fun hright z

end CompletionFactors

end
end Masullo
