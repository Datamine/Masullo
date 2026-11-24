import HilbertOperatorTensors
import InductiveTensorTopology

/-! # The projective tensor norm and trace-class operators -/

open Filter Function Set Topology UniformSpace InnerProductSpace
open scoped TensorProduct InnerProductSpace NNReal

namespace Masullo

noncomputable section

universe u

variable {E F : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

private abbrev OperatorTensor (E F : Type u) [NormedAddCommGroup E] [NormedSpace ℂ E]
    [AddCommGroup F] [Module ℂ F] := StrongDual ℂ E ⊗[ℂ] F

private def ProjectiveOperatorTest (E F : Type u) [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] :=
  {l : OperatorTensor E F →ₗ[ℂ] ℂ // ∀ φ v, ‖l (φ ⊗ₜ[ℂ] v)‖ ≤ ‖φ‖ * ‖v‖}

private theorem singularTensor_has_norming_form {T : E →L[ℂ] F} {s : ℕ → ℝ}
    {e : ℕ → E} {f : ℕ → F} (h : IsSingularExpansion T s e f) (J : Finset ℕ) :
    ∃ l : ProjectiveOperatorTest E F,
      l.val (∑ i ∈ J, (s i : ℂ) • ((innerSL ℂ (e i) : StrongDual ℂ E) ⊗ₜ[ℂ] f i)) =
        ((∑ i ∈ J, s i) : ℂ) := by
  classical
  let I := {i : ℕ // 0 < s i}
  let K := J.preimage (fun i : I => i.val) Subtype.val_injective.injOn
  let L (i : I) : OperatorTensor E F →ₗ[ℂ] ℂ :=
    InjectiveTensorTools.dualPair (asPointwise (ContinuousLinearMap.apply ℂ ℂ (e i.val)))
      (asPointwise (innerSL ℂ (f i.val)))
  let l := ∑ i ∈ K, L i
  have hl (φ : StrongDual ℂ E) (v : F) :
      l (φ ⊗ₜ[ℂ] v) = ∑ i ∈ K, φ (e i.val) * ⟪f i.val, v⟫_ℂ := by
    dsimp only [l]
    rw [LinearMap.sum_apply]
    exact Finset.sum_congr rfl fun i _ => rfl
  refine ⟨⟨l, fun φ v => ?_⟩, ?_⟩
  · let x := (InnerProductSpace.toDual ℂ E).symm φ
    have hφ (i : I) : ‖φ (e i.val)‖ = ‖⟪e i.val, x⟫_ℂ‖ := by
      rw [← InnerProductSpace.toDual_symm_apply, norm_inner_symm]
    have hφb : ∑ i ∈ K, ‖φ (e i.val)‖ ^ 2 ≤ ‖φ‖ ^ 2 := by
      simp_rw [hφ]
      simpa only [x, LinearIsometryEquiv.norm_map] using
        h.sourceOrthonormal.sum_inner_products_le (s := K) x
    have hvb := h.targetOrthonormal.sum_inner_products_le (s := K) v
    rw [hl]
    calc
      _ ≤ ∑ i ∈ K, ‖φ (e i.val)‖ * ‖⟪f i.val, v⟫_ℂ‖ := by
        simpa only [norm_mul] using norm_sum_le K (fun i => φ (e i.val) * ⟪f i.val, v⟫_ℂ)
      _ ≤ Real.sqrt (∑ i ∈ K, ‖φ (e i.val)‖ ^ 2) *
          Real.sqrt (∑ i ∈ K, ‖⟪f i.val, v⟫_ℂ‖ ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt K _ _
      _ ≤ _ := mul_le_mul
        (Real.sqrt_le_iff.mpr ⟨norm_nonneg _, hφb⟩)
        (Real.sqrt_le_iff.mpr ⟨norm_nonneg _, hvb⟩)
        (Real.sqrt_nonneg _) (norm_nonneg _)
  · change l _ = _
    rw [map_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    by_cases hpos : 0 < s j
    · let k : I := ⟨j, hpos⟩
      have hk : k ∈ K := Finset.mem_preimage.mpr hj
      rw [map_smul, smul_eq_mul, hl, Finset.sum_eq_single_of_mem k hk]
      · change (s j : ℂ) * (⟪e j, e j⟫_ℂ * ⟪f j, f j⟫_ℂ) = _
        have hE : ‖e j‖ = 1 := h.sourceOrthonormal.norm_eq_one k
        have hF : ‖f j‖ = 1 := h.targetOrthonormal.norm_eq_one k
        simp [inner_self_eq_norm_sq_to_K, hE, hF]
      · intro i _ hi
        have hv : ⟪f i.val, f j⟫_ℂ = 0 := h.targetOrthonormal.inner_eq_zero hi
        rw [hv, mul_zero]
    · simp [le_antisymm (le_of_not_gt hpos) (h.nonnegative j)]

variable [CompleteSpace F]

private theorem schattenOne_finiteSingularMass (z : OperatorTensor E F) :
    ∃ (n : ℕ) (s : ℕ → ℝ) (e : ℕ → E) (f : ℕ → F),
      IsSingularExpansion (hilbertTensorOperator z) s e f ∧
      z = ∑ i ∈ Finset.range n, (s i : ℂ) • ((innerSL ℂ (e i) : StrongDual ℂ E) ⊗ₜ[ℂ] f i) ∧
      schattenNorm 1 (hilbertTensorOperator z) = ∑ i ∈ Finset.range n, s i := by
  obtain ⟨n, s, e, f, h, hz, he⟩ := hilbertTensorOperator_finiteSingularTensor z
  refine ⟨n, s, e, f, h, he, ?_⟩
  simp only [schattenNorm, Real.rpow_one, inv_one, h.approximationNumber_eq]
  exact tsum_eq_sum (fun i hi => hz i (Nat.le_of_not_gt fun h => hi (Finset.mem_range.mpr h)))

private theorem projectiveOperatorTest_norm_le (l : ProjectiveOperatorTest E F)
    (z : OperatorTensor E F) : ‖l.val z‖ ≤ schattenNorm 1 (hilbertTensorOperator z) := by
  obtain ⟨n, s, e, f, h, he, hs⟩ := schattenOne_finiteSingularMass z
  rw [hs, he, map_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [map_smul, norm_smul, Complex.norm_of_nonneg (h.nonnegative i)]
  by_cases hi : 0 < s i
  · apply mul_le_of_le_one_right (h.nonnegative i)
    have hE : ‖e i‖ = 1 := h.sourceOrthonormal.norm_eq_one ⟨i, hi⟩
    have hF : ‖f i‖ = 1 := h.targetOrthonormal.norm_eq_one ⟨i, hi⟩
    simpa only [innerSL_apply_norm, hE, hF, mul_one] using
      l.property (innerSL ℂ (e i)) (f i)
  · simp [le_antisymm (le_of_not_gt hi) (h.nonnegative i)]

private theorem projectiveOperatorTest_attains (z : OperatorTensor E F) :
    ∃ l : ProjectiveOperatorTest E F, ‖l.val z‖ = schattenNorm 1 (hilbertTensorOperator z) := by
  obtain ⟨n, s, e, f, h, he, hs⟩ := schattenOne_finiteSingularMass z
  obtain ⟨l, hl⟩ := singularTensor_has_norming_form h (Finset.range n)
  exact ⟨l, by rw [hs, he, hl, ← Complex.ofReal_sum, Complex.norm_of_nonneg (Finset.sum_nonneg fun i _ => h.nonnegative i)]⟩

/-- The Schatten-1 norm on algebraic operator tensors is a seminorm,
as it is the pointwise maximum of the product-bounded bilinear tests. -/
def hilbertProjectiveTensorNorm : Seminorm ℂ (OperatorTensor E F) :=
  Seminorm.ofSMulLE (fun z => schattenNorm 1 (hilbertTensorOperator z))
    (by
      obtain ⟨l, hl⟩ := projectiveOperatorTest_attains (0 : OperatorTensor E F)
      rw [← hl, map_zero, norm_zero])
    (fun x y => by
      obtain ⟨l, hl⟩ := projectiveOperatorTest_attains (x + y)
      rw [← hl, map_add]
      exact (norm_add_le _ _).trans
        (add_le_add (projectiveOperatorTest_norm_le l x) (projectiveOperatorTest_norm_le l y)))
    (fun a x => by
      obtain ⟨l, hl⟩ := projectiveOperatorTest_attains (a • x)
      rw [← hl, map_smul, norm_smul]
      exact mul_le_mul_of_nonneg_left (projectiveOperatorTest_norm_le l x) (norm_nonneg a))

theorem hilbertProjectiveTensorNorm_tmul_le (φ : StrongDual ℂ E) (v : F) :
    hilbertProjectiveTensorNorm (φ ⊗ₜ[ℂ] v) ≤ ‖φ‖ * ‖v‖ := by
  obtain ⟨l, hl⟩ := projectiveOperatorTest_attains (φ ⊗ₜ[ℂ] v)
  change schattenNorm 1 (hilbertTensorOperator (φ ⊗ₜ[ℂ] v)) ≤ _
  rw [← hl]
  exact l.property φ v

private theorem hilbertTensorOperator_le_projectiveNorm (z : OperatorTensor E F) :
    ‖hilbertTensorOperator z‖ ≤ hilbertProjectiveTensorNorm z := by
  have h := (hilbertTensorOperator_isSchatten le_rfl z).2
  change ‖hilbertTensorOperator z‖ ≤ schattenNorm 1 (hilbertTensorOperator z)
  simp only [schattenNorm, Real.rpow_one, inv_one] at h ⊢
  rw [← approximationNumber_zero (hilbertTensorOperator z)]
  exact h.le_tsum 0 (fun i _ => approximationNumber_nonneg i _)

/-- The algebraic operator tensor with the projective norm. -/
abbrev hilbertProjectiveTensorNormedGroup (E F : Type u)
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F] :
    NormedAddCommGroup (OperatorTensor E F) :=
  AddGroupNorm.toNormedAddCommGroup ⟨hilbertProjectiveTensorNorm.toAddGroupSeminorm, fun z hz => by
    apply hilbertTensorOperator_injective
    rw [map_zero]
    apply norm_eq_zero.mp
    exact le_antisymm ((hilbertTensorOperator_le_projectiveNorm z).trans_eq hz) (norm_nonneg _)⟩


private theorem seminorm_le_hilbertProjectiveTensorNorm (P : Seminorm ℂ (OperatorTensor E F))
    (C : ℝ) (hP : ∀ φ v, P (φ ⊗ₜ[ℂ] v) ≤ C * (‖φ‖ * ‖v‖))
    (z : OperatorTensor E F) : P z ≤ C * hilbertProjectiveTensorNorm z := by
  obtain ⟨n, s, e, f, h, he, hs⟩ := schattenOne_finiteSingularMass z
  change P z ≤ C * schattenNorm 1 (hilbertTensorOperator z)
  rw [hs, he, Finset.mul_sum]
  let a (i : ℕ) : OperatorTensor E F := (s i : ℂ) • ((innerSL ℂ (e i)) ⊗ₜ[ℂ] f i)
  have hadd (J : Finset ℕ) : P (∑ i ∈ J, a i) ≤ ∑ i ∈ J, P (a i) := by
    classical
    induction J using Finset.induction_on with
    | empty => simp
    | insert x J hx hJ =>
      rw [Finset.sum_insert hx, Finset.sum_insert hx]
      exact (map_add_le_add P _ _).trans (add_le_add (le_refl _) hJ)
  apply (hadd (Finset.range n)).trans
  change (∑ i ∈ Finset.range n, P (a i)) ≤ _
  refine Finset.sum_le_sum fun i _ => ?_
  dsimp only [a]
  rw [map_smul_eq_mul, Complex.norm_of_nonneg (h.nonnegative i)]
  by_cases hi : 0 < s i
  · rw [mul_comm C (s i)]
    apply mul_le_mul_of_nonneg_left _ (h.nonnegative i)
    have hE : ‖e i‖ = 1 := h.sourceOrthonormal.norm_eq_one ⟨i, hi⟩
    have hF : ‖f i‖ = 1 := h.targetOrthonormal.norm_eq_one ⟨i, hi⟩
    simpa only [innerSL_apply_norm, hE, hF, mul_one] using hP (innerSL ℂ (e i)) (f i)
  · simp [le_antisymm (le_of_not_gt hi) (h.nonnegative i)]

/-- The algebraic norm is the greatest seminorm bounded on elementary tensors
by the product of the factor norms. -/
theorem le_hilbertProjectiveTensorNorm (P : Seminorm ℂ (OperatorTensor E F))
    (hP : ∀ φ v, P (φ ⊗ₜ[ℂ] v) ≤ ‖φ‖ * ‖v‖) : P ≤ hilbertProjectiveTensorNorm := by
  intro z
  simpa only [one_mul] using
    seminorm_le_hilbertProjectiveTensorNorm P 1
      (fun φ v => by simpa only [one_mul] using hP φ v) z

private theorem projectiveTest_le_hilbertProjectiveTensorNorm
    (P : ProjectiveTensorTest (StrongDual ℂ E) F) :
    ∃ C : ℝ≥0, ∀ z, P.tensor z ≤ (C : ℝ) * hilbertProjectiveTensorNorm z := by
  obtain ⟨a, ha⟩ := continuousSeminorm_le_norm P.first P.first_continuous
  obtain ⟨b, hb⟩ := continuousSeminorm_le_norm P.second P.second_continuous
  refine ⟨a * b, seminorm_le_hilbertProjectiveTensorNorm P.tensor _ ?_⟩
  intro φ v
  calc
    _ ≤ P.first φ * P.second v := P.bound φ v
    _ ≤ ((a : ℝ) * ‖φ‖) * ((b : ℝ) * ‖v‖) :=
      mul_le_mul (ha φ) (hb v) (apply_nonneg _ _) (by positivity)
    _ = _ := by push_cast; ring

/-- The normed projective tensor completion uses the actual projective
locally convex uniform structure of the manuscript. -/
theorem hilbertProjectiveTensor_uniformity :
    (projectiveTensorModuleStructure (StrongDual ℂ E) F).uniformSpace =
      (hilbertProjectiveTensorNormedGroup E F).toMetricSpace.toUniformSpace := by
  let G := projectiveTensorModuleStructure (StrongDual ℂ E) F
  letI : UniformSpace (OperatorTensor E F) := G.uniformSpace
  letI : IsUniformAddGroup (OperatorTensor E F) := G.uniformGroup
  letI : ContinuousConstSMul ℂ (OperatorTensor E F) := G.constSmul
  let p := hilbertProjectiveTensorNorm (E := E) (F := F)
  let P : ProjectiveTensorTest (StrongDual ℂ E) F :=
    ⟨p, normSeminorm ℂ (StrongDual ℂ E), normSeminorm ℂ F, continuous_norm, continuous_norm,
      hilbertProjectiveTensorNorm_tmul_le⟩
  have hp : Continuous p := projectiveTensor_withSeminorms.continuous_seminorm P
  apply Seminorm.uniformSpace_eq_of_hasBasis p projectiveTensor_withSeminorms.hasBasis_zero_ball
    ⟨1, mem_of_superset (Seminorm.ball_mem_nhds hp zero_lt_one) (Seminorm.ball_subset_closedBall _ _ _)⟩
  rintro ⟨I, r⟩ hr
  choose c hc using fun i => projectiveTest_le_hilbertProjectiveTensorNorm (E := E) (F := F) i
  let C : ℝ≥0 := I.sup c
  refine ⟨r / ((C : ℝ) + 1), by positivity, ?_⟩
  intro z hz
  apply (I.sup (ProjectiveTensorTest.tensor (E := StrongDual ℂ E) (F := F))).mem_ball_zero.mpr
  apply Seminorm.finset_sup_apply_lt hr
  intro i hi
  have hC : (c i : ℝ) ≤ C := by exact_mod_cast Finset.le_sup (f := c) hi
  have hz' : p z * ((C : ℝ) + 1) < r :=
    (lt_div_iff₀ (by positivity : 0 < (C : ℝ) + 1)).mp (p.mem_ball_zero.mp hz)
  exact (hc i z).trans_lt (lt_of_le_of_lt
    (by nlinarith only [mul_le_mul_of_nonneg_right hC (apply_nonneg p z), apply_nonneg p z]) hz')


section Completion

local instance : NormedAddCommGroup (OperatorTensor E F) :=
  hilbertProjectiveTensorNormedGroup E F

local instance : NormedSpace ℂ (OperatorTensor E F) where
  norm_smul_le a z := le_of_eq (map_smul_eq_mul (hilbertProjectiveTensorNorm (E := E) (F := F)) a z)

private def projectiveTensorToCompletion : OperatorTensor E F →ₗ[ℂ] Completion (OperatorTensor E F) :=
  (Completion.toComplL : OperatorTensor E F →L[ℂ] Completion (OperatorTensor E F)).toLinearMap

/-- The canonical continuous operator map from the projective tensor completion. -/
def completedHilbertProjectiveTensor :
    Completion (OperatorTensor E F) →L[ℂ] (E →L[ℂ] F) :=
  hilbertTensorOperator.extendOfNorm projectiveTensorToCompletion

@[simp] theorem completedHilbertProjectiveTensor_coe (z : OperatorTensor E F) :
    completedHilbertProjectiveTensor (z : Completion (OperatorTensor E F)) = hilbertTensorOperator z := by
  apply LinearMap.extendOfNorm_eq (Completion.denseRange_coe (α := OperatorTensor E F))
  refine ⟨1, fun w => ?_⟩
  change ‖hilbertTensorOperator w‖ ≤ 1 * ‖(w : Completion (OperatorTensor E F))‖
  rw [one_mul, Completion.norm_coe]
  exact hilbertTensorOperator_le_projectiveNorm w

/-- Convergence of finite sums of dual/vector tensors in the actual
projective completion, together with their represented operator. -/
def HilbertProjectiveTensorExpansion {ι β : Type*} (stages : β → Finset ι) (l : Filter β)
    (f : ι → StrongDual ℂ E) (v : ι → F) (A : E →L[ℂ] F) : Prop :=
  ∃ K : Completion (OperatorTensor E F),
    Tendsto (fun b => ∑ i ∈ stages b, ((f i ⊗ₜ[ℂ] v i : OperatorTensor E F) :
      Completion (OperatorTensor E F))) l (𝓝 K) ∧
    completedHilbertProjectiveTensor K = A

/-- A summable rank-one norm bound controls convergence in the projective
norm along every cofinal family of finite sums. -/
theorem hilbertProjectiveTensorExpansion_of_summable {ι β : Type*}
    (stages : β → Finset ι) (l : Filter β) (hcofinal : Tendsto stages l atTop)
    (f : ι → StrongDual ℂ E) (v : ι → F)
    (hs : Summable (fun i => ‖f i‖ * ‖v i‖)) :
    HilbertProjectiveTensorExpansion stages l f v
      (∑' i, hilbertTensorOperator (f i ⊗ₜ[ℂ] v i)) := by
  let u (i : ι) : Completion (OperatorTensor E F) := (f i ⊗ₜ[ℂ] v i : OperatorTensor E F)
  have hu : Summable u := hs.of_norm_bounded (fun i => by
    change ‖((f i ⊗ₜ[ℂ] v i : OperatorTensor E F) : Completion (OperatorTensor E F))‖ ≤ _
    rw [Completion.norm_coe]
    exact hilbertProjectiveTensorNorm_tmul_le (f i) (v i))
  refine ⟨∑' i, u i, hu.hasSum.comp hcofinal, ?_⟩
  rw [completedHilbertProjectiveTensor.map_tsum hu]
  exact tsum_congr fun i => completedHilbertProjectiveTensor_coe _

private theorem hilbertTensorOperator_partial_mass_le (z : OperatorTensor E F) (J : Finset ℕ) :
    ∑ i ∈ J, approximationNumber i (hilbertTensorOperator z) ≤ ‖z‖ := by
  have h := (hilbertTensorOperator_isSchatten le_rfl z).2
  change _ ≤ schattenNorm 1 (hilbertTensorOperator z)
  simp only [schattenNorm, Real.rpow_one, inv_one] at h ⊢
  exact h.sum_le_tsum J (fun i _ => approximationNumber_nonneg i _)

theorem completedHilbertProjectiveTensor_isSchattenOne (z : Completion (OperatorTensor E F)) :
    IsSchatten 1 (completedHilbertProjectiveTensor z) ∧
      schattenNorm 1 (completedHilbertProjectiveTensor z) ≤ ‖z‖ := by
  have hcompact : IsCompactOperator (completedHilbertProjectiveTensor z) := by
    induction z using Completion.induction_on with
    | hp =>
      have hc : IsClosed {T : E →L[ℂ] F | IsCompactOperator T} :=
        isClosed_setOfPred_isCompactOperator
      exact hc.preimage (completedHilbertProjectiveTensor (E := E) (F := F)).continuous
    | ih x =>
      rw [completedHilbertProjectiveTensor_coe]
      exact (hilbertTensorOperator_isSchatten le_rfl x).1
  let a := fun i => approximationNumber i (completedHilbertProjectiveTensor z)
  have ha (J : Finset ℕ) : ∑ i ∈ J, a i ≤ ‖z‖ := by
    clear hcompact
    dsimp only [a]
    induction z using Completion.induction_on with
    | hp =>
      apply isClosed_le _ continuous_norm
      exact continuous_finsetSum _ fun i _ =>
        (approximationNumber_continuous i).comp completedHilbertProjectiveTensor.continuous
    | ih x =>
      rw [completedHilbertProjectiveTensor_coe, Completion.norm_coe]
      exact hilbertTensorOperator_partial_mass_le x J
  have hs := summable_of_sum_le (fun i => approximationNumber_nonneg i _) ha
  refine ⟨⟨hcompact, by simpa only [a, Real.rpow_one] using hs⟩, ?_⟩
  simpa only [schattenNorm, Real.rpow_one, inv_one] using hs.tsum_le_of_sum_le ha

theorem completedHilbertProjectiveTensor_injective :
    Injective (completedHilbertProjectiveTensor (E := E) (F := F)) := by
  change Injective (completedHilbertProjectiveTensor (E := E) (F := F)).toLinearMap
  apply LinearMap.ker_eq_bot.mp
  rw [Submodule.eq_bot_iff]
  intro z hz
  have hz0 : completedHilbertProjectiveTensor z = 0 := hz
  have hle (w : Completion (OperatorTensor E F)) : ‖w‖ ≤ ‖w - z‖ := by
    induction w using Completion.induction_on with
    | hp => exact isClosed_le continuous_norm ((continuous_id.sub continuous_const).norm)
    | ih x =>
      have h := (completedHilbertProjectiveTensor_isSchattenOne
        ((x : Completion (OperatorTensor E F)) - z)).2
      rw [map_sub, completedHilbertProjectiveTensor_coe, hz0, sub_zero] at h
      change ‖x‖ ≤ ‖(x : Completion (OperatorTensor E F)) - z‖ at h
      simpa only [Completion.norm_coe] using h
  exact norm_eq_zero.mp (le_antisymm (by simpa using hle z) (norm_nonneg _))

private theorem exists_projectiveTensor_lift_of_isSchattenOne {T : E →L[ℂ] F}
    (hT : IsSchatten 1 T) :
    ∃ z : Completion (OperatorTensor E F),
      completedHilbertProjectiveTensor z = T ∧ ‖z‖ ≤ schattenNorm 1 T := by
  obtain ⟨s, e, f, h, _⟩ := compactOperator_hasSingularExpansion T hT.1
  have hs : Summable s := by
    simpa only [Real.rpow_one, h.approximationNumber_eq] using hT.2
  let a (i : ℕ) : OperatorTensor E F :=
    (s i : ℂ) • ((innerSL ℂ (e i) : StrongDual ℂ E) ⊗ₜ[ℂ] f i)
  let b (i : ℕ) : Completion (OperatorTensor E F) := a i
  have hb (i : ℕ) : ‖b i‖ ≤ s i := by
    change ‖(a i : Completion (OperatorTensor E F))‖ ≤ _
    rw [Completion.norm_coe, show a i =
      (s i : ℂ) • ((innerSL ℂ (e i) : StrongDual ℂ E) ⊗ₜ[ℂ] f i) from rfl,
      norm_smul, Complex.norm_of_nonneg (h.nonnegative i)]
    by_cases hi : 0 < s i
    · apply mul_le_of_le_one_right (h.nonnegative i)
      have hE : ‖e i‖ = 1 := h.sourceOrthonormal.norm_eq_one ⟨i, hi⟩
      have hF : ‖f i‖ = 1 := h.targetOrthonormal.norm_eq_one ⟨i, hi⟩
      change hilbertProjectiveTensorNorm
        ((innerSL ℂ (e i) : StrongDual ℂ E) ⊗ₜ[ℂ] f i) ≤ 1
      simpa only [innerSL_apply_norm, hE, hF, mul_one] using
        hilbertProjectiveTensorNorm_tmul_le (innerSL ℂ (e i)) (f i)
    · simp [le_antisymm (le_of_not_gt hi) (h.nonnegative i)]
  have hsum : Summable b := hs.of_norm_bounded hb
  refine ⟨∑' i, b i, ?_, ?_⟩
  · have hm (i : ℕ) : completedHilbertProjectiveTensor (b i) =
        (s i : ℂ) • rankOne ℂ (f i) (e i) := by
      change completedHilbertProjectiveTensor (a i : Completion (OperatorTensor E F)) = _
      rw [completedHilbertProjectiveTensor_coe, map_smul]
      congr 1
    have ht := ((completedHilbertProjectiveTensor (E := E) (F := F)).hasSum hsum.hasSum).tendsto_sum_nat
    simp only [hm] at ht
    exact tendsto_nhds_unique ht h.tendsto_opNorm
  · have hc := hsum.hasSum.norm_le_of_bounded hs.hasSum hb
    simpa only [schattenNorm, Real.rpow_one, inv_one, h.approximationNumber_eq] using hc

/-- C.3.6.4(3), projective clause. The canonical completion map is injective,
has exactly the trace-class operators in its range, and preserves the trace norm. -/
theorem completedHilbertProjectiveTensor_traceClass :
    Injective (completedHilbertProjectiveTensor (E := E) (F := F)) ∧
      range (completedHilbertProjectiveTensor (E := E) (F := F)) =
        {T : E →L[ℂ] F | IsSchatten 1 T} ∧
      ∀ z : Completion (OperatorTensor E F),
        schattenNorm 1 (completedHilbertProjectiveTensor z) = ‖z‖ := by
  refine ⟨completedHilbertProjectiveTensor_injective, ?_, ?_⟩
  · ext T
    constructor
    · rintro ⟨z, rfl⟩
      exact (completedHilbertProjectiveTensor_isSchattenOne z).1
    · intro hT
      obtain ⟨z, hz, _⟩ := exists_projectiveTensor_lift_of_isSchattenOne hT
      exact ⟨z, hz⟩
  · intro z
    have h := completedHilbertProjectiveTensor_isSchattenOne z
    obtain ⟨y, hy, hle⟩ := exists_projectiveTensor_lift_of_isSchattenOne h.1
    have hyz : y = z := completedHilbertProjectiveTensor_injective hy
    exact le_antisymm h.2 (hyz ▸ hle)

end Completion

end

end Masullo
