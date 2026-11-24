import InjectiveTensorNorm
import LocallyConvexApproximation
import CompactSingularExpansion
import SchattenConvergence
import Mathlib.Analysis.InnerProductSpace.OfNorm
import Mathlib.Analysis.InnerProductSpace.TensorProduct

/-!
# Canonical Hilbert-space operator tensors

The dual inner product uses the parallelogram argument from
`RiemannMasullo/AppC_LCTVS/Sec3a_part2.lean` at
`db376192baf52253727c46e2b211619d4e6a3941` (Apache-2.0).
-/

open Filter Function Set Topology UniformSpace InnerProductSpace
open scoped TensorProduct PointwiseConvergenceCLM

namespace Masullo

noncomputable section

open InjectiveTensorTools

universe u

variable {E F : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- The canonical operator of an algebraic tensor of domain functionals and
target vectors. -/
def hilbertTensorOperator : StrongDual ℂ E ⊗[ℂ] F →ₗ[ℂ] (E →L[ℂ] F) :=
  tensorOperator E F

omit [CompleteSpace E] [CompleteSpace F] in
@[simp] theorem hilbertTensorOperator_tmul (f : StrongDual ℂ E) (v : F) (x : E) :
    hilbertTensorOperator (f ⊗ₜ[ℂ] v) x = f x • v :=
  tensorOperator_tmul f v x

omit [CompleteSpace E] [CompleteSpace F] in
private theorem hilbertTensorOperator_rank_le (z : StrongDual ℂ E ⊗[ℂ] F) :
    ∃ n : ℕ, (hilbertTensorOperator z).toLinearMap.rank ≤ n := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul f v =>
    refine ⟨1, ?_⟩
    have hr : (hilbertTensorOperator (f ⊗ₜ[ℂ] v)).toLinearMap.range ≤ ℂ ∙ v := by
      rintro _ ⟨x, rfl⟩
      rw [ContinuousLinearMap.coe_coe, hilbertTensorOperator_tmul]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)
    simpa using (Submodule.rank_mono hr).trans (rank_span_le ({v} : Set F))
  | add x y hx hy =>
    obtain ⟨m, hm⟩ := hx
    obtain ⟨n, hn⟩ := hy
    refine ⟨m + n, ?_⟩
    rw [map_add, ContinuousLinearMap.toLinearMap_add, Nat.cast_add]
    exact (LinearMap.rank_add_le _ _).trans (add_le_add hm hn)

omit [CompleteSpace E] in
private theorem hilbertTensorOperator_isCompact (z : StrongDual ℂ E ⊗[ℂ] F) :
    IsCompactOperator (hilbertTensorOperator z) := by
  obtain ⟨n, hn⟩ := hilbertTensorOperator_rank_le z
  apply isCompactOperator_of_approximationNumber_tendsto_zero
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop n] with m hm
  exact (approximationNumber_eq_zero_of_rank_le _
    (hn.trans (by exact_mod_cast hm))).symm

omit [CompleteSpace E] in
/-- C.3.6.4(1). Algebraic operator tensors belong to every Schatten class
in the stated exponent range. -/
theorem hilbertTensorOperator_isSchatten {p : ℝ} (hp : 1 ≤ p)
    (z : StrongDual ℂ E ⊗[ℂ] F) : IsSchatten p (hilbertTensorOperator z) := by
  refine ⟨hilbertTensorOperator_isCompact z, ?_⟩
  obtain ⟨n, hn⟩ := hilbertTensorOperator_rank_le z
  apply summable_of_hasFiniteSupport
  apply (Finset.range n).finite_toSet.subset
  intro m hm
  by_contra! h
  have hnm : n ≤ m := Nat.le_of_not_gt fun hm => h (Finset.mem_range.mpr hm)
  have he := approximationNumber_eq_zero_of_rank_le (hilbertTensorOperator z)
    (hn.trans (by exact_mod_cast hnm))
  apply hm
  change approximationNumber m (hilbertTensorOperator z) ^ p = 0
  rw [he, Real.zero_rpow (by linarith : p ≠ 0)]

omit [CompleteSpace F] in
private theorem exists_hilbert_dual_eval (α : StrongDual ℂ (StrongDual ℂ E)) :
    ∃ x : E, ‖x‖ ≤ ‖α‖ ∧ ∀ f : StrongDual ℂ E, α f = f x := by
  let R := InnerProductSpace.toDual ℂ E
  let g : StrongDual ℂ E :=
    { toFun := fun y => star (α (R y))
      map_add' := by intro x y; simp
      map_smul' := by intro c y; simp [map_smulₛₗ]
      cont := Complex.continuous_conj.comp (α.continuous.comp R.continuous) }
  let x := R.symm g
  have hx : ‖x‖ ≤ ‖α‖ := by
    rw [R.symm.norm_map g]
    apply g.opNorm_le_bound (norm_nonneg α) fun y => ?_
    change ‖star (α (R y))‖ ≤ _
    rw [norm_star, ← R.norm_map y]
    exact α.le_opNorm _
  refine ⟨x, hx, fun f => ?_⟩
  obtain ⟨y, rfl⟩ := R.surjective f
  have he : R x y = star (α (R y)) := congrArg (fun k : StrongDual ℂ E => k y) (R.apply_symm_apply g)
  have hr : inner ℂ x y = star (α (R y)) := he
  change α (R y) = inner ℂ y x
  rw [← inner_conj_symm]
  simpa only [starRingEnd_apply, star_star] using (congrArg star hr).symm

omit [CompleteSpace E] [CompleteSpace F] in
private theorem hilbertTensorOperator_pair (z : StrongDual ℂ E ⊗[ℂ] F) (x : E)
    (ψ : StrongDual ℂ F) :
    dualPair (asPointwise (ContinuousLinearMap.apply ℂ ℂ x)) (asPointwise ψ) z =
      ψ (hilbertTensorOperator z x) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul f v =>
    rw [dualPair_tmul, hilbertTensorOperator_tmul, map_smul]
    rfl
  | add z w hz hw => simp [map_add, hz, hw]

omit [CompleteSpace F] in
/-- The injective tensor norm is the operator norm of the canonical image. -/
theorem hilbertTensorOperator_norm_eq (z : StrongDual ℂ E ⊗[ℂ] F) :
    ‖hilbertTensorOperator z‖ = injectiveTensorNorm (StrongDual ℂ E) F z := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (apply_nonneg _ _) fun x => ?_
    obtain ⟨ψ, hψ, hv⟩ := exists_dual_vector'' ℂ (hilbertTensorOperator z x)
    have hval : ‖ψ (hilbertTensorOperator z x)‖ = ‖hilbertTensorOperator z x‖ := by
      rw [hv]
      change ‖(‖hilbertTensorOperator z x‖ : ℂ)‖ = _
      exact Complex.norm_of_nonneg (norm_nonneg _)
    have hEval : ‖ContinuousLinearMap.apply ℂ ℂ x‖ ≤ ‖x‖ := by
      apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun α => ?_
      rw [ContinuousLinearMap.apply_apply, mul_comm]
      exact α.le_opNorm x
    rw [← hval, ← hilbertTensorOperator_pair]
    refine (norm_dualPair_le_injectiveTensorNorm _ _ _).trans ?_
    calc
      _ ≤ (‖x‖ * 1) * injectiveTensorNorm _ _ z :=
        mul_le_mul_of_nonneg_right (mul_le_mul hEval hψ (norm_nonneg _) (norm_nonneg _))
          (apply_nonneg _ _)
      _ = _ := by rw [mul_one, mul_comm]
  · apply injectiveTensorNorm_le_of_dualPairs _ (norm_nonneg _) fun φ ψ hφ hψ => ?_
    obtain ⟨x, hx, he⟩ := exists_hilbert_dual_eval φ
    have hf : φ = ContinuousLinearMap.apply ℂ ℂ x :=
      DFunLike.ext _ _ he
    rw [hf, hilbertTensorOperator_pair]
    calc
      _ ≤ ‖ψ‖ * ‖hilbertTensorOperator z x‖ := ψ.le_opNorm _
      _ ≤ ‖hilbertTensorOperator z x‖ := mul_le_of_le_one_left (norm_nonneg _) hψ
      _ ≤ ‖hilbertTensorOperator z‖ * ‖x‖ := (hilbertTensorOperator z).le_opNorm _
      _ ≤ ‖hilbertTensorOperator z‖ := mul_le_of_le_one_right (norm_nonneg _) (hx.trans hφ)

omit [CompleteSpace F] in
theorem hilbertTensorOperator_injective :
    Injective (hilbertTensorOperator (E := E) (F := F)) := by
  intro z w h
  apply sub_eq_zero.mp
  apply injectiveTensorNorm_eq_zero
  rw [← hilbertTensorOperator_norm_eq, map_sub, h, sub_self, norm_zero]

section InjectiveCompletion

local instance : NormedAddCommGroup (StrongDual ℂ E ⊗[ℂ] F) :=
  injectiveTensorNormedGroup (StrongDual ℂ E) F

local instance : NormedSpace ℂ (StrongDual ℂ E ⊗[ℂ] F) where
  norm_smul_le c z := le_of_eq (map_smul_eq_mul (injectiveTensorNorm (StrongDual ℂ E) F) c z)

/-- The algebraic identification equipped with the injective tensor norm. -/
def hilbertInjectiveTensorIsometry : (StrongDual ℂ E ⊗[ℂ] F) →ₗᵢ[ℂ] (E →L[ℂ] F) :=
  ⟨hilbertTensorOperator, hilbertTensorOperator_norm_eq⟩

/-- The canonical operator map on the completion for the injective tensor norm. -/
def completedHilbertInjectiveTensor :
    Completion (StrongDual ℂ E ⊗[ℂ] F) →L[ℂ] (E →L[ℂ] F) :=
  (hilbertInjectiveTensorIsometry (E := E) (F := F)).toContinuousLinearMap.extend Completion.toComplL

@[simp] theorem completedHilbertInjectiveTensor_coe (z : StrongDual ℂ E ⊗[ℂ] F) :
    completedHilbertInjectiveTensor (z : Completion (StrongDual ℂ E ⊗[ℂ] F)) = hilbertTensorOperator z :=
  (hilbertInjectiveTensorIsometry (E := E) (F := F)).toContinuousLinearMap.extend_eq
    Completion.denseRange_coe (Completion.isUniformInducing_coe _) z

/-- The extension preserves the completed injective norm. -/
def completedHilbertInjectiveTensorIsometry :
    Completion (StrongDual ℂ E ⊗[ℂ] F) →ₗᵢ[ℂ] (E →L[ℂ] F) where
  toLinearMap := completedHilbertInjectiveTensor.toLinearMap
  norm_map' := by
    intro z
    induction z using Completion.induction_on with
    | hp =>
      exact isClosed_eq completedHilbertInjectiveTensor.continuous.norm continuous_norm
    | ih z =>
      change ‖completedHilbertInjectiveTensor (z : Completion (StrongDual ℂ E ⊗[ℂ] F))‖ = ‖(z : Completion (StrongDual ℂ E ⊗[ℂ] F))‖
      rw [completedHilbertInjectiveTensor_coe, Completion.norm_coe]
      exact hilbertTensorOperator_norm_eq z

omit [CompleteSpace E] [CompleteSpace F] in
/-- The completion for the injective norm is the manuscript's separated
injective tensor completion. -/
theorem hilbertInjectiveTensor_uniformity :
    (injectiveTensorStructure (StrongDual ℂ E) F).uniformSpace =
      (inferInstance : UniformSpace (StrongDual ℂ E ⊗[ℂ] F)) :=
  injectiveTensor_uniformity_eq_norm _ _

/-- C.3.6.4(3), injective clause. The range of the completed canonical
isometry consists of exactly the compact operators. -/
theorem completedHilbertInjectiveTensor_range :
    range (completedHilbertInjectiveTensor (E := E) (F := F)) =
      {T : E →L[ℂ] F | IsCompactOperator T} := by
  ext T
  constructor
  · rintro ⟨z, rfl⟩
    induction z using Completion.induction_on with
    | hp => exact isClosed_setOfPred_isCompactOperator.preimage completedHilbertInjectiveTensor.continuous
    | ih z =>
      rw [completedHilbertInjectiveTensor_coe]
      exact hilbertTensorOperator_isCompact z
  · intro hT
    have hclosed : IsClosed (range (completedHilbertInjectiveTensor (E := E) (F := F))) :=
      (completedHilbertInjectiveTensorIsometry (E := E) (F := F)).isometry.isClosedEmbedding.isClosed_range
    obtain ⟨s, e, f, h, _⟩ := compactOperator_hasSingularExpansion T hT
    refine hclosed.mem_of_tendsto h.tendsto_opNorm (Eventually.of_forall fun n => ?_)
    let z : StrongDual ℂ E ⊗[ℂ] F :=
      ∑ i ∈ Finset.range n, (s i : ℂ) • ((innerSL ℂ (e i)) ⊗ₜ[ℂ] f i)
    refine ⟨(z : Completion (StrongDual ℂ E ⊗[ℂ] F)), ?_⟩
    rw [completedHilbertInjectiveTensor_coe]
    ext x
    simp only [z, map_sum, map_smul, sum_apply, smul_apply, hilbertTensorOperator_tmul,
      rankOne_apply, innerSL_apply_apply]

end InjectiveCompletion


section HilbertNorm

open scoped InnerProductSpace

/-- The dual of a complex Hilbert space carries the inner product compatible
with its usual operator norm. -/
@[instance_reducible]
def hilbertStrongDualInnerProduct : InnerProductSpace ℂ (StrongDual ℂ E) :=
  InnerProductSpace.ofNorm ℂ fun a b => by
    let R := (InnerProductSpace.toDual ℂ E).symm
    simpa only [← map_add, ← map_sub, R.norm_map] using
      parallelogram_law_with_norm_mul ℂ (R a) (R b)

local instance : InnerProductSpace ℂ (E →L[ℂ] ℂ) := hilbertStrongDualInnerProduct

local instance : NormedAddCommGroup (StrongDual ℂ E ⊗[ℂ] F) :=
  TensorProduct.instNormedAddCommGroup

local instance : InnerProductSpace ℂ (StrongDual ℂ E ⊗[ℂ] F) :=
  TensorProduct.instInnerProductSpace

/-- Finite singular decompositions lift to the algebraic operator tensor. -/
theorem hilbertTensorOperator_finiteSingularTensor (z : StrongDual ℂ E ⊗[ℂ] F) :
    ∃ (n : ℕ) (s : ℕ → ℝ) (e : ℕ → E) (f : ℕ → F),
      IsSingularExpansion (hilbertTensorOperator z) s e f ∧
      (∀ m ≥ n, s m = 0) ∧
      z = ∑ i ∈ Finset.range n, (s i : ℂ) • ((innerSL ℂ (e i)) ⊗ₜ[ℂ] f i) := by
  obtain ⟨n, hn⟩ := hilbertTensorOperator_rank_le z
  obtain ⟨s, e, f, h, _⟩ :=
    compactOperator_hasSingularExpansion (hilbertTensorOperator z) (hilbertTensorOperator_isCompact z)
  have hzero (m : ℕ) (hm : n ≤ m) : s m = 0 := by
    rw [← h.approximationNumber_eq]
    exact approximationNumber_eq_zero_of_rank_le _ (hn.trans (by exact_mod_cast hm))
  refine ⟨n, s, e, f, h, hzero, ?_⟩
  apply hilbertTensorOperator_injective
  have ht := h.tail_norm_le n
  rw [hzero n le_rfl, norm_le_zero_iff, sub_eq_zero] at ht
  rw [ht]
  ext x
  simp only [map_sum, map_smul, sum_apply, smul_apply, hilbertTensorOperator_tmul, innerSL_apply_apply,
    rankOne_apply]

omit [CompleteSpace F] in
set_option backward.isDefEq.respectTransparency false in
private theorem singularTensor_sum_norm_sq {T : E →L[ℂ] F} {s : ℕ → ℝ}
    {e : ℕ → E} {f : ℕ → F} (h : IsSingularExpansion T s e f) (r : Finset ℕ) :
    ‖∑ i ∈ r, (s i : ℂ) • ((innerSL ℂ (e i) : StrongDual ℂ E) ⊗ₜ[ℂ] f i)‖ ^ 2 =
      ∑ i ∈ r, s i ^ 2 := by
  let a (i : ℕ) : StrongDual ℂ E ⊗[ℂ] F := (s i : ℂ) • ((innerSL ℂ (e i)) ⊗ₜ[ℂ] f i)
  have hn (i : ℕ) : ‖a i‖ = s i := by
    by_cases hi : 0 < s i
    · have hE : ‖e i‖ = 1 := h.sourceOrthonormal.norm_eq_one ⟨i, hi⟩
      have hF : ‖f i‖ = 1 := h.targetOrthonormal.norm_eq_one ⟨i, hi⟩
      rw [show a i = (s i : ℂ) • ((innerSL ℂ (e i) : StrongDual ℂ E) ⊗ₜ[ℂ] f i) from rfl,
        norm_smul, Complex.norm_of_nonneg (h.nonnegative i), TensorProduct.norm_tmul,
        innerSL_apply_norm, hE, hF, mul_one, mul_one]
    · simp [a, le_antisymm (le_of_not_gt hi) (h.nonnegative i)]
  have ho (i j : ℕ) (hij : i ≠ j) : ⟪a i, a j⟫_ℂ = 0 := by
    by_cases hi : 0 < s i
    · by_cases hj : 0 < s j
      · have hF : ⟪f i, f j⟫_ℂ = 0 :=
          h.targetOrthonormal.inner_eq_zero (i := ⟨i, hi⟩) (j := ⟨j, hj⟩)
            (fun he => hij (congrArg Subtype.val he))
        change inner ℂ ((s i : ℂ) • ((innerSL ℂ (e i) : StrongDual ℂ E) ⊗ₜ[ℂ] f i))
          ((s j : ℂ) • ((innerSL ℂ (e j) : StrongDual ℂ E) ⊗ₜ[ℂ] f j)) = 0
        rw [inner_smul_left, inner_smul_right, TensorProduct.inner_tmul, hF]
        simp
      · rw [norm_eq_zero.mp ((hn j).trans (le_antisymm (le_of_not_gt hj) (h.nonnegative j))),
          inner_zero_right]
    · rw [norm_eq_zero.mp ((hn i).trans (le_antisymm (le_of_not_gt hi) (h.nonnegative i))),
        inner_zero_left]
  change ‖∑ i ∈ r, a i‖ ^ 2 = _
  rw [norm_sq_eq_re_inner (𝕜 := ℂ) (∑ i ∈ r, a i), sum_inner, map_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [inner_sum, Finset.sum_eq_single_of_mem i hi]
  · rw [← norm_sq_eq_re_inner (𝕜 := ℂ), hn]
  · exact fun j _ hji => ho i j (Ne.symm hji)

set_option backward.isDefEq.respectTransparency false in
/-- C.3.6.4(2) on algebraic tensors. The Schatten-2 norm agrees with the
norm from the inner product of the two tensor factors. -/
theorem hilbertTensorOperator_schattenTwo_norm (z : StrongDual ℂ E ⊗[ℂ] F) :
    schattenNorm 2 (hilbertTensorOperator z) = ‖z‖ := by
  obtain ⟨n, s, e, f, h, hz, he⟩ := hilbertTensorOperator_finiteSingularTensor z
  have hsq : ‖z‖ ^ 2 = ∑ i ∈ Finset.range n, s i ^ 2 :=
    congrArg (fun w : StrongDual ℂ E ⊗[ℂ] F => ‖w‖ ^ 2) he |>.trans
      (singularTensor_sum_norm_sq h _)
  simp only [schattenNorm, Real.rpow_two, h.approximationNumber_eq]
  rw [tsum_eq_sum (s := Finset.range n), ← hsq, ← one_div, ← Real.sqrt_eq_rpow,
    Real.sqrt_sq (norm_nonneg _)]
  intro i hi
  simp [hz i (Nat.le_of_not_gt fun h => hi (Finset.mem_range.mpr h))]

private theorem hilbertTensorOperator_partialSquares_le (z : StrongDual ℂ E ⊗[ℂ] F)
    (s : Finset ℕ) : (∑ i ∈ s, approximationNumber i (hilbertTensorOperator z) ^ 2) ≤ ‖z‖ ^ 2 := by
  let a := fun i => approximationNumber i (hilbertTensorOperator z) ^ 2
  have hs : Summable a := by
    simpa only [a, Real.rpow_two] using (hilbertTensorOperator_isSchatten (p := 2) (by norm_num) z).2
  have hn : ‖z‖ ^ 2 = ∑' i, a i := by
    rw [← hilbertTensorOperator_schattenTwo_norm]
    simp only [schattenNorm, Real.rpow_two, a]
    rw [← one_div, ← Real.sqrt_eq_rpow, Real.sq_sqrt (tsum_nonneg fun _ => sq_nonneg _)]
  rw [hn]
  exact hs.sum_le_tsum s (fun _ _ => sq_nonneg _)

private theorem hilbertTensorOperator_le_hilbertNorm (z : StrongDual ℂ E ⊗[ℂ] F) :
    ‖hilbertTensorOperator z‖ ≤ ‖z‖ := by
  have h := hilbertTensorOperator_partialSquares_le z {0}
  rw [Finset.sum_singleton, approximationNumber_zero] at h
  simpa only [Real.sqrt_sq (norm_nonneg _)] using Real.sqrt_le_sqrt h

private def hilbertTensorToCompletion :
    (StrongDual ℂ E ⊗[ℂ] F) →ₗ[ℂ] Completion (StrongDual ℂ E ⊗[ℂ] F) :=
  (Completion.toComplL : (StrongDual ℂ E ⊗[ℂ] F) →L[ℂ]
    Completion (StrongDual ℂ E ⊗[ℂ] F)).toLinearMap

/-- The canonical operator map on the Hilbert tensor completion. -/
def completedHilbertTensor :
    Completion (StrongDual ℂ E ⊗[ℂ] F) →L[ℂ] (E →L[ℂ] F) :=
  hilbertTensorOperator.extendOfNorm hilbertTensorToCompletion

set_option backward.isDefEq.respectTransparency false in
@[simp] theorem completedHilbertTensor_coe (z : StrongDual ℂ E ⊗[ℂ] F) :
    completedHilbertTensor (z : Completion (StrongDual ℂ E ⊗[ℂ] F)) = hilbertTensorOperator z := by
  have hd : DenseRange (hilbertTensorToCompletion (E := E) (F := F)) := Completion.denseRange_coe
  have hbound (x : StrongDual ℂ E ⊗[ℂ] F) : ‖hilbertTensorOperator x‖ ≤
      1 * ‖hilbertTensorToCompletion x‖ := by
    change ‖hilbertTensorOperator x‖ ≤ 1 * ‖(x : Completion (StrongDual ℂ E ⊗[ℂ] F))‖
    rw [one_mul, Completion.norm_coe]
    exact hilbertTensorOperator_le_hilbertNorm x
  exact LinearMap.extendOfNorm_eq hd ⟨1, hbound⟩ z

/-- The Hilbert tensor completion maps to the Schatten-2 class. -/
theorem completedHilbertTensor_isSchattenTwo (z : Completion (StrongDual ℂ E ⊗[ℂ] F)) :
    IsSchatten 2 (completedHilbertTensor z) ∧ schattenNorm 2 (completedHilbertTensor z) ≤ ‖z‖ := by
  let a := fun i => approximationNumber i (completedHilbertTensor z) ^ 2
  have ha (s : Finset ℕ) : ∑ i ∈ s, a i ≤ ‖z‖ ^ 2 := by
    dsimp only [a]
    induction z using Completion.induction_on with
    | hp =>
      apply isClosed_le _ (continuous_norm.pow 2)
      exact continuous_finsetSum _ (fun i _ =>
        ((approximationNumber_continuous i).comp completedHilbertTensor.continuous).pow 2)
    | ih x =>
      rw [completedHilbertTensor_coe, Completion.norm_coe]
      exact hilbertTensorOperator_partialSquares_le x s
  have hc : IsCompactOperator (completedHilbertTensor z) := by
    clear ha a
    induction z using Completion.induction_on with
    | hp =>
      have hc : IsClosed {T : E →L[ℂ] F | IsCompactOperator T} :=
        isClosed_setOfPred_isCompactOperator
      exact hc.preimage (completedHilbertTensor (E := E) (F := F)).continuous
    | ih x => rw [completedHilbertTensor_coe]; exact hilbertTensorOperator_isCompact x
  have hs := summable_of_sum_le (fun i => sq_nonneg (approximationNumber i (completedHilbertTensor z))) ha
  refine ⟨⟨hc, by simpa only [a, Real.rpow_two] using hs⟩, ?_⟩
  simp only [schattenNorm, Real.rpow_two]
  rw [← one_div, ← Real.sqrt_eq_rpow, ← Real.sqrt_sq (norm_nonneg z)]
  exact Real.sqrt_le_sqrt (hs.tsum_le_of_sum_le ha)


/-- The Hilbert tensor completion still embeds algebraically in the operator space. -/
theorem completedHilbertTensor_injective :
    Injective (completedHilbertTensor (E := E) (F := F)) := by
  change Injective (completedHilbertTensor (E := E) (F := F)).toLinearMap
  apply LinearMap.ker_eq_bot.mp
  rw [Submodule.eq_bot_iff]
  intro z hz
  have hz0 : completedHilbertTensor z = 0 := hz
  have hle (w : Completion (StrongDual ℂ E ⊗[ℂ] F)) : ‖w‖ ≤ ‖w - z‖ := by
    induction w using Completion.induction_on with
    | hp => exact isClosed_le continuous_norm ((continuous_id.sub continuous_const).norm)
    | ih x =>
      have h := (completedHilbertTensor_isSchattenTwo
        ((x : Completion (StrongDual ℂ E ⊗[ℂ] F)) - z)).2
      rw [map_sub, completedHilbertTensor_coe, hz0, sub_zero,
        hilbertTensorOperator_schattenTwo_norm] at h
      simpa only [Completion.norm_coe] using h
  exact norm_eq_zero.mp (le_antisymm (by simpa using hle z) (norm_nonneg _))


set_option maxHeartbeats 1400000 in
/-- C.3.6.4(2) on the completion. The extended norm is exactly the Schatten-2
norm, as can be seen by lifting the compact operator's singular sums. -/
theorem completedHilbertTensor_schattenTwo_norm
    (z : Completion (StrongDual ℂ E ⊗[ℂ] F)) :
    schattenNorm 2 (completedHilbertTensor z) = ‖z‖ := by
  let T := completedHilbertTensor z
  have hT : IsSchatten 2 T := (completedHilbertTensor_isSchattenTwo z).1
  obtain ⟨s, e, f, h, _⟩ := compactOperator_hasSingularExpansion T hT.1
  have hs : Summable (fun i => s i ^ 2) := by
    simpa only [Real.rpow_two, h.approximationNumber_eq] using hT.2
  let a (i : ℕ) : StrongDual ℂ E ⊗[ℂ] F := (s i : ℂ) • ((innerSL ℂ (e i)) ⊗ₜ[ℂ] f i)
  let b (n : ℕ) : StrongDual ℂ E ⊗[ℂ] F := ∑ i ∈ Finset.range n, a i
  have hC : CauchySeq b := by
    have hc := Metric.cauchySeq_iff.mp hs.hasSum.tendsto_sum_nat.cauchySeq
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := hc (ε ^ 2) (sq_pos_of_pos hε)
    refine ⟨N, fun m hm n hn => ?_⟩
    wlog hmn : n ≤ m generalizing m n
    · rw [dist_comm]
      exact this n hn m hm (le_of_not_ge hmn)
    have hdist : dist (b m) (b n) ^ 2 =
        (∑ i ∈ Finset.range m, s i ^ 2) - ∑ i ∈ Finset.range n, s i ^ 2 := by
      rw [dist_eq_norm, show b m - b n = ∑ i ∈ Finset.Ico n m, a i from
        (Finset.sum_Ico_eq_sub a hmn).symm, singularTensor_sum_norm_sq h,
        Finset.sum_Ico_eq_sub _ hmn]
    have hscalar := hN m hm n hn
    rw [Real.dist_eq] at hscalar
    have hle := (le_abs_self _).trans_lt hscalar
    rw [← hdist] at hle
    exact lt_of_not_ge fun hge => (not_le_of_gt hle)
      (pow_le_pow_left₀ hε.le hge 2)
  have hC' : CauchySeq (fun n => (b n : Completion (StrongDual ℂ E ⊗[ℂ] F))) := by
    rw [CauchySeq, ← show (Completion.coe' : (StrongDual ℂ E ⊗[ℂ] F) → Completion _) ∘ b =
      (fun n => (b n : Completion (StrongDual ℂ E ⊗[ℂ] F))) from rfl, ← Filter.map_map]
    exact hC.map (Completion.uniformContinuous_coe (StrongDual ℂ E ⊗[ℂ] F))
  obtain ⟨y, hy'⟩ := cauchySeq_tendsto_of_complete hC'
  have heq (n : ℕ) : completedHilbertTensor (b n : Completion (StrongDual ℂ E ⊗[ℂ] F)) =
      ∑ i ∈ Finset.range n, (s i : ℂ) • rankOne ℂ (f i) (e i) := by
    rw [completedHilbertTensor_coe]
    ext x
    simp only [b, a, map_sum, map_smul, sum_apply, smul_apply, hilbertTensorOperator_tmul,
      innerSL_apply_apply, rankOne_apply]
  have hyz : y = z := by
    apply completedHilbertTensor_injective (E := E) (F := F)
    have hlim := completedHilbertTensor.continuous.continuousAt.tendsto.comp hy'
    exact tendsto_nhds_unique hlim (h.tendsto_opNorm.congr fun n => (heq n).symm)
  have hnorm : ‖y‖ ^ 2 = ∑' i, s i ^ 2 := by
    have he (n : ℕ) : ‖(b n : Completion (StrongDual ℂ E ⊗[ℂ] F))‖ ^ 2 =
        ∑ i ∈ Finset.range n, s i ^ 2 := by
      rw [Completion.norm_coe]
      exact singularTensor_sum_norm_sq h _
    exact tendsto_nhds_unique (hy'.norm.pow 2)
      (hs.hasSum.tendsto_sum_nat.congr fun n => (he n).symm)
  have hnorm' : ‖z‖ ^ 2 = ∑' i, s i ^ 2 := hyz ▸ hnorm
  change schattenNorm 2 T = ‖z‖
  simp only [schattenNorm, Real.rpow_two, h.approximationNumber_eq]
  rw [← hnorm', ← one_div, ← Real.sqrt_eq_rpow, Real.sqrt_sq (norm_nonneg _)]

end HilbertNorm

end

end Masullo
