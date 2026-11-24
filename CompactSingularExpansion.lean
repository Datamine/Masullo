import HilbertMinMax
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.CoveringNumbers

open Filter Function InnerProductSpace Set Topology

namespace Masullo

noncomputable section

open scoped InnerProductSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

private abbrev CompactHilbertMap (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] :=
  ↥(compactOperator (RingHom.id ℂ) E F)

private theorem exists_singularStepVector (T : CompactHilbertMap E F) :
    ∃ e : E,
      ((T.val = 0 → e = 0) ∧ (T.val ≠ 0 → ‖e‖ = 1)) ∧
      ‖T.val e‖ = ‖T.val‖ ∧
      T.val.adjoint (T.val e) = (‖T.val‖ : ℂ) ^ 2 • e := by
  by_cases hz : T.val = 0
  · exact ⟨0, by simp [hz]⟩
  haveI : Nontrivial E := by
    rcases subsingleton_or_nontrivial E with h | h
    · exact (hz (ContinuousLinearMap.ext fun x => by rw [Subsingleton.elim x 0, map_zero, map_zero])).elim
    · exact h
  obtain ⟨e, he, hnorm, hEig⟩ := exists_unit_norm_eq_opNorm_of_isCompactOperator T.val T.property
  exact ⟨e, ⟨fun h => (hz h).elim, fun _ => he⟩, hnorm, hEig⟩

private def singularStepVector (T : CompactHilbertMap E F) : E :=
  (exists_singularStepVector T).choose

private theorem singularStepVector_zero {T : CompactHilbertMap E F} (h : T.val = 0) :
    singularStepVector T = 0 :=
  (exists_singularStepVector T).choose_spec.1.1 h

private theorem singularStepVector_norm {T : CompactHilbertMap E F} (h : T.val ≠ 0) :
    ‖singularStepVector T‖ = 1 :=
  (exists_singularStepVector T).choose_spec.1.2 h

private theorem singularStepVector_image (T : CompactHilbertMap E F) :
    ‖T.val (singularStepVector T)‖ = ‖T.val‖ :=
  (exists_singularStepVector T).choose_spec.2.1

private theorem singularStepVector_eigenvector (T : CompactHilbertMap E F) :
    T.val.adjoint (T.val (singularStepVector T)) =
      (‖T.val‖ : ℂ) ^ 2 • singularStepVector T :=
  (exists_singularStepVector T).choose_spec.2.2

private def singularStepResidual (T : CompactHilbertMap E F) : CompactHilbertMap E F :=
  ⟨T.val.comp (ContinuousLinearMap.id ℂ E - rankOne ℂ (singularStepVector T) (singularStepVector T)),
    T.property.comp_clm _⟩

private theorem singularStepResidual_apply (T : CompactHilbertMap E F) (x : E) :
    (singularStepResidual T).val x = T.val x -
      ⟪singularStepVector T, x⟫_ℂ • T.val (singularStepVector T) := by
  change T.val (x - ⟪singularStepVector T, x⟫_ℂ • singularStepVector T) = _
  rw [map_sub, map_smul]

private theorem singularStepResidual_eq_sub (T : CompactHilbertMap E F) :
    (singularStepResidual T).val =
      T.val - rankOne ℂ (T.val (singularStepVector T)) (singularStepVector T) := by
  ext x
  exact singularStepResidual_apply T x

private theorem singularStepResidual_norm (T : CompactHilbertMap E F) :
    ‖(singularStepResidual T).val‖ ≤ ‖T.val‖ := by
  by_cases hz : T.val = 0
  · simp [singularStepResidual, hz]
  let e := singularStepVector T
  have he : ‖e‖ = 1 := singularStepVector_norm hz
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
  let y := x - ⟪e, x⟫_ℂ • e
  have hy : ⟪e, y⟫_ℂ = 0 := by
    simp [y, inner_sub_right, inner_smul_right, inner_self_eq_norm_sq_to_K, he]
  have hxy : ‖y‖ ≤ ‖x‖ := by
    have hx : x = y + ⟪e, x⟫_ℂ • e := by simp [y]
    have horth : ⟪y, ⟪e, x⟫_ℂ • e⟫_ℂ = 0 := by
      have h : ⟪y, e⟫_ℂ = 0 := by
        rw [← inner_conj_symm y e, hy, map_zero]
      rw [inner_smul_right, h, mul_zero]
    have hs := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero y
      (⟪e, x⟫_ℂ • e) horth
    rw [← hx] at hs
    nlinarith [norm_nonneg y, norm_nonneg x, sq_nonneg ‖⟪e, x⟫_ℂ • e‖]
  change ‖T.val y‖ ≤ _
  exact (T.val.le_opNorm y).trans (mul_le_mul_of_nonneg_left hxy (norm_nonneg _))

private theorem singularStepResidual_kills (T : CompactHilbertMap E F) :
    (singularStepResidual T).val (singularStepVector T) = 0 := by
  by_cases hz : T.val = 0
  · simp [singularStepResidual_apply, hz]
  simp [singularStepResidual_apply, inner_self_eq_norm_sq_to_K, singularStepVector_norm hz]

private theorem singularStepVector_inner_of_kernel (T : CompactHilbertMap E F) {x : E} (hx : T.val x = 0) :
    ⟪singularStepVector T, x⟫_ℂ = 0 := by
  by_cases hz : T.val = 0
  · simp [singularStepVector_zero hz]
  have h := T.val.adjoint_inner_left x (T.val (singularStepVector T))
  rw [hx, inner_zero_right, singularStepVector_eigenvector, inner_smul_left] at h
  exact (mul_eq_zero.mp h).resolve_left (by simp [hz])

private theorem singularStepResidual_preserves_kernel (T : CompactHilbertMap E F) {x : E}
    (hx : T.val x = 0) : (singularStepResidual T).val x = 0 := by
  rw [singularStepResidual_apply, hx, singularStepVector_inner_of_kernel T hx, zero_smul, sub_zero]

private theorem singularStepResidual_image_orthogonal (T : CompactHilbertMap E F) (x : E) :
    ⟪T.val (singularStepVector T), (singularStepResidual T).val x⟫_ℂ = 0 := by
  rw [singularStepResidual_apply, inner_sub_right, inner_smul_right,
    inner_self_eq_norm_sq_to_K, singularStepVector_image,
    ← T.val.adjoint_inner_left, singularStepVector_eigenvector, inner_smul_left]
  simp [mul_comm]

private theorem singularStepResidual_preserves_range_orthogonal (T : CompactHilbertMap E F) {z : F}
    (hz : ∀ x, ⟪z, T.val x⟫_ℂ = 0) (x : E) :
    ⟪z, (singularStepResidual T).val x⟫_ℂ = 0 := by
  rw [singularStepResidual_apply, inner_sub_right, inner_smul_right, hz, hz, mul_zero, sub_zero]

private def singularResidual (T : CompactHilbertMap E F) : ℕ → CompactHilbertMap E F
  | 0 => T
  | n + 1 => singularStepResidual (singularResidual T n)

private def singularRight (T : CompactHilbertMap E F) (n : ℕ) : E :=
  singularStepVector (singularResidual T n)

private def singularImage (T : CompactHilbertMap E F) (n : ℕ) : F :=
  (singularResidual T n).val (singularRight T n)

private def singularValue (T : CompactHilbertMap E F) (n : ℕ) : ℝ :=
  ‖(singularResidual T n).val‖

private theorem singularImage_norm (T : CompactHilbertMap E F) (n : ℕ) :
    ‖singularImage T n‖ = singularValue T n :=
  singularStepVector_image (singularResidual T n)

private theorem singularValue_antitone (T : CompactHilbertMap E F) : Antitone (singularValue T) :=
  antitone_nat_of_succ_le (fun n => singularStepResidual_norm (singularResidual T n))

private theorem singularResidual_kills_prev (T : CompactHilbertMap E F) {i j : ℕ} (h : i < j) :
    (singularResidual T j).val (singularRight T i) = 0 := by
  induction j with
  | zero => omega
  | succ j ih =>
    by_cases hj : i = j
    · subst j
      exact singularStepResidual_kills (singularResidual T i)
    · exact singularStepResidual_preserves_kernel (singularResidual T j) (ih (by omega))

private theorem singularRight_orthogonal_lt (T : CompactHilbertMap E F) {i j : ℕ} (h : i < j) :
    ⟪singularRight T j, singularRight T i⟫_ℂ = 0 :=
  singularStepVector_inner_of_kernel (singularResidual T j) (singularResidual_kills_prev T h)

private theorem singularImage_orthogonal_residual (T : CompactHilbertMap E F) {i j : ℕ} (h : i < j) :
    ∀ x, ⟪singularImage T i, (singularResidual T j).val x⟫_ℂ = 0 := by
  induction j with
  | zero => omega
  | succ j ih =>
    by_cases hj : i = j
    · subst j
      exact singularStepResidual_image_orthogonal (singularResidual T i)
    · exact singularStepResidual_preserves_range_orthogonal (singularResidual T j) (ih (by omega))

private theorem singularImage_orthogonal_lt (T : CompactHilbertMap E F) {i j : ℕ} (h : i < j) :
    ⟪singularImage T i, singularImage T j⟫_ℂ = 0 :=
  singularImage_orthogonal_residual T h (singularRight T j)

private theorem singularResidual_eq_sub_sum (T : CompactHilbertMap E F) (n : ℕ) :
    (singularResidual T n).val =
      T.val - ∑ i ∈ Finset.range n, rankOne ℂ (singularImage T i) (singularRight T i) := by
  induction n with
  | zero => simp [singularResidual]
  | succ n ih =>
    rw [singularResidual, singularStepResidual_eq_sub, Finset.sum_range_succ, sub_add_eq_sub_sub]
    change (singularResidual T n).val - rankOne ℂ (singularImage T n) (singularRight T n) = _
    rw [ih]

private theorem singularImage_eq_original (T : CompactHilbertMap E F) (n : ℕ) :
    singularImage T n = T.val (singularRight T n) := by
  unfold singularImage
  rw [singularResidual_eq_sub_sum, sub_apply, sum_apply, sub_eq_self]
  apply Finset.sum_eq_zero
  intro i hi
  rw [rankOne_apply, ← inner_conj_symm, singularRight_orthogonal_lt T (Finset.mem_range.mp hi),
    map_zero, zero_smul]

private theorem singularValue_tendsto_zero (T : CompactHilbertMap E F) :
    Tendsto (singularValue T) atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds, ← Nat.cofinite_eq_atTop]
  intro ε hε
  let I := {i : ℕ | ε ≤ singularValue T i}
  let K := closure (T.val '' Metric.closedBall (0 : E) 1)
  have hK : IsCompact K := T.property.isCompact_closure_image_closedBall 1
  obtain ⟨C, _, hCfin, hcover⟩ := hK.finite_cover_balls (half_pos hε)
  have hImage (i : I) : singularImage T i.val ∈ K := by
    have hi : (singularResidual T i.val).val ≠ 0 :=
      norm_pos_iff.mp (hε.trans_le i.property)
    have he : ‖singularRight T i.val‖ = 1 := singularStepVector_norm hi
    rw [singularImage_eq_original]
    exact subset_closure ⟨_, Metric.mem_closedBall.mpr (by rw [dist_zero_right, he]), rfl⟩
  have hex (i : I) : ∃ c : C, dist (singularImage T i.val) c.val < ε / 2 := by
    obtain ⟨c, hc, hi⟩ := mem_iUnion₂.mp (hcover (hImage i))
    exact ⟨⟨c, hc⟩, Metric.mem_ball.mp hi⟩
  choose c hc using hex
  have hd (i j : I) (h : i.val < j.val) :
      ε ≤ dist (singularImage T i.val) (singularImage T j.val) := by
    rw [dist_eq_norm]
    have hs := norm_sub_sq (𝕜 := ℂ) (singularImage T i.val) (singularImage T j.val)
    rw [singularImage_orthogonal_lt T h, map_zero, mul_zero, sub_zero, singularImage_norm,
      singularImage_norm] at hs
    have hi : ε ^ 2 ≤ singularValue T i.val ^ 2 := pow_le_pow_left₀ hε.le i.property _
    nlinarith [sq_nonneg (singularValue T j.val),
      norm_nonneg (singularImage T i.val - singularImage T j.val)]
  have hi : Injective c := by
    intro i j hij
    by_contra hne
    have hv : i.val ≠ j.val := fun h => hne (Subtype.ext h)
    have hnear : dist (singularImage T i.val) (singularImage T j.val) < ε := by
      have h := hc j
      rw [← hij, dist_comm] at h
      exact (dist_triangle _ (c i).val _).trans_lt (by linarith [hc i])
    rcases lt_or_gt_of_ne hv with h | h
    · exact hnear.not_ge (hd i j h)
    · rw [dist_comm] at hnear
      exact hnear.not_ge (hd j i h)
  letI : Finite C := hCfin.to_subtype
  letI : Finite I := Finite.of_injective c hi
  filter_upwards [(Set.toFinite I).eventually_cofinite_notMem] with i hi
  rw [dist_zero_right, Real.norm_of_nonneg (show 0 ≤ singularValue T i from norm_nonneg _)]
  exact lt_of_not_ge hi

private def singularLeft (T : CompactHilbertMap E F) (n : ℕ) : F :=
  ((singularValue T n : ℂ)⁻¹) • singularImage T n

private theorem singularValue_mul_left (T : CompactHilbertMap E F) (n : ℕ) :
    (singularValue T n : ℂ) • singularLeft T n = singularImage T n := by
  by_cases h : singularValue T n = 0
  · have hz : singularImage T n = 0 := norm_eq_zero.mp ((singularImage_norm T n).trans h)
    simp [h, hz]
  simp [singularLeft, smul_smul, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr h)]

/-- A singular expansion allows a zero tail. The left and right vectors
are required to be orthonormal only on the indices with nonzero values. -/
structure IsSingularExpansion (T : E →L[ℂ] F) (s : ℕ → ℝ) (e : ℕ → E) (f : ℕ → F) : Prop where
  nonnegative : ∀ i, 0 ≤ s i
  decreasing : Antitone s
  vanishing : Tendsto s atTop (𝓝 0)
  sourceOrthonormal : Orthonormal ℂ (fun i : {i // 0 < s i} => e i.val)
  targetOrthonormal : Orthonormal ℂ (fun i : {i // 0 < s i} => f i.val)
  pointwise : ∀ x, Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n, (s i : ℂ) • (rankOne ℂ (f i) (e i)) x)
    atTop (𝓝 (T x))

private theorem singularRight_orthonormal (T : CompactHilbertMap E F) :
    Orthonormal ℂ (fun i : {i // 0 < singularValue T i} => singularRight T i.val) := by
  rw [orthonormal_iff_ite]
  intro i j
  by_cases h : i = j
  · subst j
    simp [inner_self_eq_norm_sq_to_K, singularRight,
      singularStepVector_norm (norm_pos_iff.mp i.property)]
  rw [ite_eq_right h]
  rcases lt_or_gt_of_ne (fun h' => h (Subtype.ext h')) with hij | hji
  · rw [← inner_conj_symm, singularRight_orthogonal_lt T hij, map_zero]
  · exact singularRight_orthogonal_lt T hji

private theorem singularLeft_orthonormal (T : CompactHilbertMap E F) :
    Orthonormal ℂ (fun i : {i // 0 < singularValue T i} => singularLeft T i.val) := by
  rw [orthonormal_iff_ite]
  intro i j
  by_cases h : i = j
  · subst j
    have hnorm : ‖singularLeft T i.val‖ = 1 := by
      simp only [singularLeft, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos i.property, singularImage_norm, inv_mul_cancel₀ i.property.ne']
    simp [inner_self_eq_norm_sq_to_K, hnorm]
  rw [ite_eq_right h]
  change ⟪singularLeft T i.val, singularLeft T j.val⟫_ℂ = 0
  simp only [singularLeft, inner_smul_left, inner_smul_right]
  have hzero : ⟪singularImage T i.val, singularImage T j.val⟫_ℂ = 0 := by
    rcases lt_or_gt_of_ne (fun h' => h (Subtype.ext h')) with hij | hji
    · exact singularImage_orthogonal_lt T hij
    · rw [← inner_conj_symm, singularImage_orthogonal_lt T hji, map_zero]
  rw [hzero, mul_zero, mul_zero]

/-- Compact Hilbert-space maps admit a decreasing singular expansion even
when their source or target is finite dimensional. -/
theorem compactOperator_hasSingularExpansion (T : E →L[ℂ] F) (hT : IsCompactOperator T) :
    ∃ (s : ℕ → ℝ) (e : ℕ → E) (f : ℕ → F), IsSingularExpansion T s e f ∧
      s 0 = ‖T‖ := by
  let A : CompactHilbertMap E F := ⟨T, hT⟩
  refine ⟨singularValue A, singularRight A, singularLeft A, ⟨fun _ => norm_nonneg _,
    singularValue_antitone A, singularValue_tendsto_zero A, singularRight_orthonormal A,
    singularLeft_orthonormal A, ?_⟩, rfl⟩
  intro x
  have hterm (i : ℕ) :
      (singularValue A i : ℂ) • (rankOne ℂ (singularLeft A i) (singularRight A i)) x =
      rankOne ℂ (singularImage A i) (singularRight A i) x := by
    simp only [rankOne_apply]
    rw [smul_comm, singularValue_mul_left]
  simp_rw [hterm]
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hlim : Tendsto (fun i => singularValue A i * ‖x‖) atTop (𝓝 0) := by
    simpa using (singularValue_tendsto_zero A).mul_const ‖x‖
  filter_upwards [hlim (Iio_mem_nhds hε)] with n hn
  simp only [dist_eq_norm]
  have hres := congrArg (fun L : E →L[ℂ] F => L x) (singularResidual_eq_sub_sum A n)
  simp only [sub_apply, sum_apply] at hres
  rw [norm_sub_rev, ← hres]
  exact ((singularResidual A n).val.le_opNorm x).trans_lt hn

private theorem orthonormal_sum_norm_sq {H ι : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {v : ι → H} (hv : Orthonormal ℂ v) (a : ι → ℂ)
    (J : Finset ι) : ‖∑ i ∈ J, a i • v i‖ ^ 2 = ∑ i ∈ J, ‖a i‖ ^ 2 := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), hv.inner_sum a a J]
  change Complex.reCLM (∑ i ∈ J, (starRingEnd ℂ) (a i) * a i) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  change ((starRingEnd ℂ) (a i) * a i).re = ‖a i‖ ^ 2
  rw [mul_comm, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

omit [CompleteSpace E] [CompleteSpace F] in
private theorem singularExpansion_sum_norm_sq {T : E →L[ℂ] F} {s : ℕ → ℝ}
    {e : ℕ → E} {f : ℕ → F} (h : IsSingularExpansion T s e f)
    (J : Finset ℕ) (x : E) :
    ‖∑ i ∈ J, (s i : ℂ) • (rankOne ℂ (f i) (e i)) x‖ ^ 2 =
      ∑ i ∈ J, s i ^ 2 * ‖⟪e i, x⟫_ℂ‖ ^ 2 := by
  classical
  let I := {i : ℕ // 0 < s i}
  let c (i : I) : ℂ := (s i.val : ℂ) * ⟪e i.val, x⟫_ℂ
  let Jpos := J.preimage (fun i : I => i.val) Subtype.val_injective.injOn
  have hz {i : ℕ} (hi : i ∉ range (fun j : I => j.val)) : s i = 0 :=
    le_antisymm (le_of_not_gt fun hpos => hi ⟨⟨i, hpos⟩, rfl⟩) (h.nonnegative i)
  have hJ :
      (∑ i ∈ Jpos, c i • f i.val) = ∑ i ∈ J, (s i : ℂ) • (rankOne ℂ (f i) (e i)) x := by
    simp only [c, rankOne_apply, smul_smul]
    exact Finset.sum_preimage (fun i : I => i.val) J Subtype.val_injective.injOn
      (fun i => ((s i : ℂ) * ⟪e i, x⟫_ℂ) • f i) (fun i _ hi => by simp [hz hi])
  rw [← hJ, orthonormal_sum_norm_sq h.targetOrthonormal]
  simp only [c, norm_mul, Complex.norm_real, Real.norm_of_nonneg (h.nonnegative _), mul_pow]
  exact Finset.sum_preimage (fun i : I => i.val) J Subtype.val_injective.injOn
    (fun i => s i ^ 2 * ‖⟪e i, x⟫_ℂ‖ ^ 2) (fun i _ hi => by simp [hz hi])

omit [CompleteSpace E] [CompleteSpace F] in
/-- Parseval on the target singular vectors gives the energy of each image. -/
theorem IsSingularExpansion.image_energy {T : E →L[ℂ] F} {s : ℕ → ℝ}
    {e : ℕ → E} {f : ℕ → F} (h : IsSingularExpansion T s e f) (x : E) :
    ‖T x‖ₑ ^ (2 : ℝ) = ∑' i, ENNReal.ofReal (s i ^ 2) * ‖⟪e i, x⟫_ℂ‖ₑ ^ (2 : ℝ) := by
  have ht : Tendsto (fun n : ℕ =>
      ENNReal.ofReal (‖∑ i ∈ Finset.range n, (s i : ℂ) • (rankOne ℂ (f i) (e i)) x‖ ^ 2))
      atTop (𝓝 (ENNReal.ofReal (‖T x‖ ^ 2))) :=
    (ENNReal.continuous_ofReal.tendsto _).comp ((h.pointwise x).norm.pow 2)
  have hs (n : ℕ) :
      ENNReal.ofReal (‖∑ i ∈ Finset.range n, (s i : ℂ) • (rankOne ℂ (f i) (e i)) x‖ ^ 2) =
        ∑ i ∈ Finset.range n, ENNReal.ofReal (s i ^ 2) * ‖⟪e i, x⟫_ℂ‖ₑ ^ (2 : ℝ) := by
    rw [singularExpansion_sum_norm_sq h, ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
    apply Finset.sum_congr rfl
    intro i _
    rw [ENNReal.ofReal_mul (sq_nonneg _), ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, ENNReal.rpow_two]
  simp_rw [hs] at ht
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm] at ht
  rw [ENNReal.rpow_two]
  exact tendsto_nhds_unique ht ENNReal.summable.hasSum.tendsto_sum_nat

omit [CompleteSpace E] [CompleteSpace F] in
private theorem singularExpansion_sum_norm_le {T : E →L[ℂ] F} {s : ℕ → ℝ}
    {e : ℕ → E} {f : ℕ → F} (h : IsSingularExpansion T s e f)
    (J : Finset ℕ) (x : E) {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ i ∈ J, s i ≤ C) :
    ‖∑ i ∈ J, (s i : ℂ) • (rankOne ℂ (f i) (e i)) x‖ ≤ C * ‖x‖ := by
  classical
  let I := {i : ℕ // 0 < s i}
  let b (i : I) : F := f i.val
  let a (i : I) : E := e i.val
  let c (i : I) : ℂ := (s i.val : ℂ) * ⟪a i, x⟫_ℂ
  let Jpos := J.preimage (fun i : I => i.val) Subtype.val_injective.injOn
  have hJ : (∑ i ∈ J, (s i : ℂ) • (rankOne ℂ (f i) (e i)) x) = ∑ i ∈ Jpos, c i • b i := by
    symm
    calc
      _ = ∑ i ∈ Jpos, (s i.val : ℂ) • (rankOne ℂ (f i.val) (e i.val)) x := by
        simp [c, b, a, smul_smul]
      _ = _ := Finset.sum_preimage (fun i : I => i.val) J Subtype.val_injective.injOn
        (fun i => (s i : ℂ) • (rankOne ℂ (f i) (e i)) x) (fun i _ hi => by
          have hs : s i = 0 := le_antisymm
            (le_of_not_gt (fun hpos => hi ⟨(⟨i, hpos⟩ : I), rfl⟩)) (h.nonnegative i)
          simp [hs])
  rw [hJ]
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))).mp
  have hsq := orthonormal_sum_norm_sq h.targetOrthonormal c Jpos
  rw [hsq, mul_pow]
  calc
    _ ≤ ∑ i ∈ Jpos, C ^ 2 * ‖⟪a i, x⟫_ℂ‖ ^ 2 := by
      refine Finset.sum_le_sum fun i hi => ?_
      have hj : i.val ∈ J := (Finset.mem_preimage.mp hi)
      rw [show ‖c i‖ = s i.val * ‖⟪a i, x⟫_ℂ‖ by
        change ‖(s i.val : ℂ) * ⟪a i, x⟫_ℂ‖ = _
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (h.nonnegative _)], mul_pow]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (h.nonnegative _) (hbound _ hj) _) (sq_nonneg _)
    _ = C ^ 2 * ∑ i ∈ Jpos, ‖⟪a i, x⟫_ℂ‖ ^ 2 := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (h.sourceOrthonormal.sum_inner_products_le x) (sq_nonneg _)

omit [CompleteSpace E] [CompleteSpace F] in
/-- Even a pointwise singular expansion converges in operator norm.
Its tail after the first `n` terms has norm at most the next value. -/
theorem IsSingularExpansion.tail_norm_le {T : E →L[ℂ] F}
    {s : ℕ → ℝ} {e : ℕ → E} {f : ℕ → F} (h : IsSingularExpansion T s e f) (n : ℕ) :
    ‖T - ∑ i ∈ Finset.range n, (s i : ℂ) • rankOne ℂ (f i) (e i)‖ ≤ s n := by
  refine ContinuousLinearMap.opNorm_le_bound _ (h.nonnegative n) (fun x => ?_)
  simp only [sub_apply, sum_apply]
  let b (i : ℕ) : F := (s i : ℂ) • (rankOne ℂ (f i) (e i)) x
  change ‖T x - ∑ i ∈ Finset.range n, b i‖ ≤ _
  have hl : Tendsto (fun m : ℕ => ‖(∑ i ∈ Finset.range m, b i) - ∑ i ∈ Finset.range n, b i‖)
      atTop (𝓝 ‖T x - ∑ i ∈ Finset.range n, b i‖) :=
    ((h.pointwise x).sub tendsto_const_nhds).norm
  apply le_of_tendsto hl
  filter_upwards [eventually_ge_atTop n] with m hm
  rw [← Finset.sum_Ico_eq_sub b hm]
  exact singularExpansion_sum_norm_le h _ x (h.nonnegative n)
    (fun i hi => h.decreasing (Finset.mem_Ico.mp hi).1)

omit [CompleteSpace E] [CompleteSpace F] in
theorem IsSingularExpansion.tendsto_opNorm {T : E →L[ℂ] F}
    {s : ℕ → ℝ} {e : ℕ → E} {f : ℕ → F} (h : IsSingularExpansion T s e f) :
    Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n, (s i : ℂ) • rankOne ℂ (f i) (e i))
      atTop (𝓝 T) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [h.vanishing (Iio_mem_nhds hε)] with n hn
  rw [dist_eq_norm, norm_sub_rev]
  exact (h.tail_norm_le n).trans_lt hn

omit [CompleteSpace E] in
theorem IsSingularExpansion.isCompactOperator {T : E →L[ℂ] F}
    {s : ℕ → ℝ} {e : ℕ → E} {f : ℕ → F} (h : IsSingularExpansion T s e f) :
    IsCompactOperator T := by
  apply isCompactOperator_of_tendsto h.tendsto_opNorm
  refine Eventually.of_forall fun n => ?_
  let C := compactOperator (RingHom.id ℂ) E F
  change (∑ i ∈ Finset.range n, (s i : ℂ) • rankOne ℂ (f i) (e i)) ∈ C
  apply Submodule.sum_mem C
  intro i _
  apply Submodule.smul_mem C
  change IsCompactOperator (rankOne ℂ (f i) (e i))
  exact (isCompactOperator_of_locallyCompactSpace_rng (ContinuousLinearMap.toSpanSingleton ℂ (f i))
    |>.comp_clm (innerSL ℂ (e i)))

omit [CompleteSpace E] [CompleteSpace F] in
theorem IsSingularExpansion.opNorm_eq_first {T : E →L[ℂ] F}
    {s : ℕ → ℝ} {e : ℕ → E} {f : ℕ → F} (h : IsSingularExpansion T s e f) :
    ‖T‖ = s 0 := by
  have hle : ‖T‖ ≤ s 0 := by simpa using h.tail_norm_le 0
  by_cases h₀ : s 0 = 0
  · exact le_antisymm hle (h₀ ▸ norm_nonneg T)
  have hs₀ : 0 < s 0 := lt_of_le_of_ne (h.nonnegative 0) (Ne.symm h₀)
  let i₀ : {i : ℕ // 0 < s i} := ⟨0, hs₀⟩
  have hu : ‖e 0‖ = 1 := h.sourceOrthonormal.norm_eq_one i₀
  have hv : ‖f 0‖ = 1 := h.targetOrthonormal.norm_eq_one i₀
  have hpart (n : ℕ) (hn : 0 < n) :
      ∑ i ∈ Finset.range n, (s i : ℂ) • (rankOne ℂ (f i) (e i)) (e 0) = (s 0 : ℂ) • f 0 := by
    rw [Finset.sum_eq_single 0]
    · simp [inner_self_eq_norm_sq_to_K, hu]
    · intro i _ hi
      by_cases hzero : s i = 0
      · simp [hzero]
      let j : {i : ℕ // 0 < s i} := ⟨i, lt_of_le_of_ne (h.nonnegative i) (Ne.symm hzero)⟩
      have hj : j ≠ i₀ := fun he => hi (congrArg Subtype.val he)
      have hinner : ⟪e i, e 0⟫_ℂ = 0 :=
        (orthonormal_iff_ite.mp h.sourceOrthonormal j i₀).trans (ite_eq_right hj)
      rw [rankOne_apply, hinner, zero_smul, smul_zero]
    · simp [hn]
  have hp : Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n, (s i : ℂ) • (rankOne ℂ (f i) (e i)) (e 0))
      atTop (𝓝 ((s 0 : ℂ) • f 0)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    exact (hpart n hn).symm
  have heq := tendsto_nhds_unique (h.pointwise (e 0)) hp
  have hge := T.le_opNorm (e 0)
  rw [heq, norm_smul, Complex.norm_real, Real.norm_of_nonneg hs₀.le, hv, mul_one, hu, mul_one] at hge
  exact le_antisymm hle hge

omit [CompleteSpace E] [CompleteSpace F] in
theorem IsSingularExpansion.apply_source {T : E →L[ℂ] F}
    {s : ℕ → ℝ} {e : ℕ → E} {f : ℕ → F} (h : IsSingularExpansion T s e f)
    {j : ℕ} (hj : 0 < s j) : T (e j) = (s j : ℂ) • f j := by
  apply tendsto_nhds_unique (h.pointwise (e j))
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop j] with n hn
  rw [Finset.sum_eq_single_of_mem j (Finset.mem_range.mpr hn)]
  · simp [inner_self_eq_norm_sq_to_K, h.sourceOrthonormal.norm_eq_one ⟨j, hj⟩]
  · intro i _ hij
    by_cases hi : 0 < s i
    · have hzero : ⟪e i, e j⟫_ℂ = 0 :=
        h.sourceOrthonormal.inner_eq_zero (i := ⟨i, hi⟩) (j := ⟨j, hj⟩)
          (fun he => hij (congrArg Subtype.val he))
      simp [rankOne_apply, hzero]
    · simp [le_antisymm (le_of_not_gt hi) (h.nonnegative i)]

/-- The singular values from the compact expansion agree at every index with
the approximation numbers, also when that index lies past the rank. -/
theorem IsSingularExpansion.approximationNumber_eq {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    {T : H →L[ℂ] K}
    {s : ℕ → ℝ} {e : ℕ → H} {f : ℕ → K} (h : IsSingularExpansion T s e f) (n : ℕ) :
    approximationNumber n T = s n := by
  classical
  let r (i : ℕ) := (s i : ℂ) • rankOne ℂ (f i) (e i)
  have hle : approximationNumber n T ≤ s n := by
    refine (approximationNumber_le T (∑ i ∈ Finset.range n, r i) ?_).trans (h.tail_norm_le n)
    rw [ContinuousLinearMap.toLinearMap_sum]
    refine (LinearMap.rank_finsetSum_le _ _).trans ?_
    calc
      _ ≤ ∑ _i ∈ Finset.range n, (1 : Cardinal) := Finset.sum_le_sum fun i _ => by
        have hin : (r i).toLinearMap.range ≤ Submodule.span ℂ {f i} := by
          rintro _ ⟨x, rfl⟩
          exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
        exact (Submodule.rank_mono hin).trans (by simpa using rank_span_le (R := ℂ) {f i})
      _ = _ := by simp
  apply le_antisymm hle
  by_cases hn : 0 < s n
  · have hi (i : Fin (n + 1)) : 0 < s i := hn.trans_le (h.decreasing (by omega : (i : ℕ) ≤ n))
    let Eₙ (i : Fin (n + 1)) := e i
    let Fₙ (i : Fin (n + 1)) := f i
    let j (i : Fin (n + 1)) : {i // 0 < s i} := ⟨i, hi i⟩
    have hj : Injective j := fun _ _ he => Fin.ext (congrArg Subtype.val he)
    have he : Orthonormal ℂ Eₙ := h.sourceOrthonormal.comp j hj
    have hf : Orthonormal ℂ Fₙ := h.targetOrthonormal.comp j hj
    let U := Submodule.span ℂ (range Eₙ)
    have hU : Module.rank ℂ U = ((n + 1 : ℕ) : Cardinal) := by
      rw [rank_span he.linearIndependent]
      simpa only [Cardinal.lift_id, Cardinal.mk_fintype, Fintype.card_fin, Cardinal.lift_natCast] using
        (Cardinal.mk_range_eq_of_injective he.linearIndependent.injective)
    have hbound (x : H) (hx : x ∈ U) : s n * ‖x‖ ≤ ‖T x‖ := by
      obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hx
      rw [← ha]
      have hmap : T (∑ i, a i • Eₙ i) = ∑ i, (a i * (s i : ℂ)) • Fₙ i := by
        simp only [map_sum, map_smul, Eₙ, Fₙ, h.apply_source (hi _), smul_smul]
      rw [hmap]
      apply (sq_le_sq₀ (mul_nonneg hn.le (norm_nonneg _)) (norm_nonneg _)).mp
      rw [mul_pow, orthonormal_sum_norm_sq he, orthonormal_sum_norm_sq hf, Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (h.nonnegative i), mul_pow, mul_comm]
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hn.le (h.decreasing (by omega : (i : ℕ) ≤ n)) 2) (sq_nonneg _)
    apply le_approximationNumber T
    intro R hR
    let L := R.toLinearMap.rangeRestrict.comp U.subtype
    have hker : L.ker ≠ ⊥ := by
      intro hz
      have hr := (L.rank_le_of_injective (LinearMap.ker_eq_bot.mp hz)).trans hR
      rw [hU] at hr
      exact (not_le_of_gt (Nat.cast_lt.mpr (Nat.lt_succ_self n))) hr
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
    have hRx : R (x : H) = 0 := congrArg Subtype.val (LinearMap.mem_ker.mp hx)
    have hnorm : 0 < ‖(x : H)‖ := norm_pos_iff.mpr fun hx' => hx0 (Subtype.ext hx')
    have hop := (T - R).le_opNorm (x : H)
    rw [sub_apply, hRx, sub_zero] at hop
    exact le_of_mul_le_mul_right ((hbound x x.property).trans hop) hnorm
  · rw [le_antisymm (le_of_not_gt hn) (h.nonnegative n)]
    exact approximationNumber_nonneg n T

/-- Compactness is equivalent to a pointwise singular expansion with an
orthonormal family indexed by the positive singular values. -/
theorem isCompactOperator_iff_singularExpansion (T : E →L[ℂ] F) :
    IsCompactOperator T ↔ ∃ (s : ℕ → ℝ) (e : ℕ → E) (f : ℕ → F), IsSingularExpansion T s e f := by
  constructor
  · intro hT
    obtain ⟨s, e, f, h, _⟩ := compactOperator_hasSingularExpansion T hT
    exact ⟨s, e, f, h⟩
  · rintro ⟨_, _, _, h⟩
    exact h.isCompactOperator

end
end Masullo
