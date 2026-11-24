import TraceClassNorm
import Mathlib.Data.Nat.Choose.Bounds

open Filter Function Set Topology InnerProductSpace
open scoped Classical InnerProductSpace

namespace Masullo
noncomputable section

variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A countable rank-one representation can be indexed by the naturals
with its total nuclear mass preserved. -/
theorem RankOneSeries.exists_nat_index_mass [Countable ι] (R : RankOneSeries ι H) :
    ∃ S : RankOneSeries ℕ H, S.operator = R.operator ∧ S.mass = R.mass := by
  obtain ⟨e,he⟩ := exists_injective_nat ι
  let u := Function.extend e R.image (0 : ℕ → H)
  let v := Function.extend e R.functional (0 : ℕ → H)
  have hs : (fun n ↦ ‖u n‖ * ‖v n‖) = Function.extend e (fun i ↦ ‖R.image i‖ * ‖R.functional i‖) 0 := by
    funext n
    by_cases hn : ∃ i, e i = n
    · obtain ⟨i,rfl⟩ := hn
      simp only [u,v,he.extend_apply]
    · simp [u,v,Function.extend_apply',hn]
  let S : RankOneSeries ℕ H := ⟨u,v, by
    rw [hs]
    exact ((hasSum_extend_zero he).mpr R.summableNorm.hasSum).summable⟩
  have hr : (fun n ↦ rankOne ℂ (u n) (v n)) =
      Function.extend e (fun i ↦ rankOne ℂ (R.image i) (R.functional i)) 0 := by
    funext n
    by_cases hn : ∃ i, e i = n
    · obtain ⟨i,rfl⟩ := hn
      simp only [u,v,he.extend_apply]
    · simp [u,v,Function.extend_apply',hn]
  refine ⟨S, ?_, ?_⟩
  · change (∑' n, rankOne ℂ (u n) (v n)) = R.operator
    rw [hr]
    exact ((hasSum_extend_zero he).mpr R.operator_summable.hasSum).tsum_eq
  · change (∑' n, ‖u n‖ * ‖v n‖) = R.mass
    rw [hs]
    exact ((hasSum_extend_zero he).mpr R.summableNorm.hasSum).tsum_eq

/-- The rank-one series from a separating coordinate system gives
a trace-class operator with its diagonal and nuclear norm controlled. -/
theorem traceClass_of_summable_biorthogonal_columns [Countable ι] [DecidableEq ι]
    (A : H →L[ℂ] H) (v : ι → H) (f : ι → StrongDual ℂ H)
    (hbi : ∀ i j, f i (v j) = if i = j then 1 else 0)
    (hzero : ∀ x : H, (∀ i, f i x = 0) → x = 0)
    (hS : Summable (fun i ↦ ‖v i‖ * ‖(f i).comp A‖)) :
    ∃ T : TraceClass H, T.toOperator = A ∧
      ‖T‖ ≤ ∑' i, ‖v i‖ * ‖(f i).comp A‖ ∧
      Summable (fun i ↦ ‖f i (A (v i))‖) ∧
      T.traceValue = ∑' i, f i (A (v i)) := by
  let u (i : ι) := (toDual ℂ H).symm ((f i).comp A)
  have hu (i : ι) (x : H) : ⟪u i,x⟫_ℂ = f i (A x) :=
    toDual_symm_apply
  let R : RankOneSeries ι H := ⟨v,u,by simpa only [u, LinearIsometryEquiv.norm_map] using hS⟩
  have hA : R.operator = A := by
    ext x : 1
    apply sub_eq_zero.mp
    apply hzero
    intro j
    rw [map_sub, R.operator_apply, (f j).map_tsum (by
      have h := R.operator_summable.hasSum.mapL (ContinuousLinearMap.apply ℂ H x)
      exact h.summable), tsum_eq_single j]
    · change f j (⟪u j,x⟫_ℂ • v j) - f j (A x) = 0
      rw [map_smul, hu, hbi]
      simp
    · intro i hi
      change f j (⟪u i,x⟫_ℂ • v i) = 0
      rw [map_smul, hbi, ite_eq_right (Ne.symm hi), smul_zero]
  obtain ⟨S,hSop,hSmass⟩ := R.exists_nat_index_mass
  refine ⟨TraceClass.ofSeries S, hSop.trans hA, ?_, ?_, ?_⟩
  · refine (TraceClass.norm_ofSeries_le S).trans_eq (hSmass.trans ?_)
    simp only [RankOneSeries.mass, R, u, LinearIsometryEquiv.norm_map]
  · simpa only [R, hu] using R.trace_summable
  · rw [TraceClass.traceValue_ofSeries, RankOneSeries.trace_eq_of_operator_eq hSop]
    exact tsum_congr (fun i ↦ hu i (v i))

/-- A triangular convolution matrix with finitely many possible jet orders and
summable coefficient sequences has a trace-class expansion. -/
theorem traceClass_of_triangular_jet_rows [Countable ι] [DecidableEq ι]
    (A : H →L[ℂ] H) (v : ι → H) (f : ι → StrongDual ℂ H)
    (hbi : ∀ i j, f i (v j) = if i = j then 1 else 0)
    (hzero : ∀ x : H, (∀ i, f i x = 0) → x = 0)
    (m : ι → ℕ) (N : ℕ) (hN : ∀ i, m i ≤ N)
    (idx : (i : ι) → Fin (m i+1) → ι)
    (hLast : ∀ i, idx i (Fin.last (m i)) = i)
    (hOther : ∀ i j, j ≠ Fin.last (m i) → idx i j ≠ i)
    (a : ι → ℕ → ℂ)
    (hrow : ∀ i, (f i).comp A = ∑ j : Fin (m i+1),
      ((m i).choose j * a i (m i-j)) • f (idx i j))
    (B D : ℝ) (hB : 0 < B) (hD : 0 < D) (hv : ∀ i, ‖v i‖ ≤ B)
    (hf : ∀ i, ‖f i‖ ≤ D)
    (ha : ∀ k ∈ Finset.range (N+1), Summable (fun i ↦ ‖a i k‖)) :
    ∃ T : TraceClass H, T.toOperator = A ∧
      ‖T‖ ≤ (B * ((N+1 : ℕ) : ℝ) * (2 : ℝ)^N * D) *
        (∑ k ∈ Finset.range (N+1), ∑' i, ‖a i k‖) ∧
      Summable (fun i ↦ ‖a i 0‖) ∧ T.traceValue = ∑' i, a i 0 := by
  let C := B * ((N+1 : ℕ) : ℝ) * (2 : ℝ)^N * D
  let b (i : ι) := ∑ k ∈ Finset.range (N+1), ‖a i k‖
  have hb (i : ι) : 0 ≤ b i := Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
  have hmajor (i : ι) : ‖v i‖ * ‖(f i).comp A‖ ≤ C * b i := by
    have hterm (j : Fin (m i+1)) :
        ‖((m i).choose j * a i (m i-j)) • f (idx i j)‖ ≤ (2 : ℝ)^N * b i * D := by
      refine (ContinuousLinearMap.opNorm_smul_le _ _).trans ?_
      rw [norm_mul, Complex.norm_natCast]
      have hchoose : ((m i).choose j : ℝ) ≤ (2 : ℝ)^N := by
        exact_mod_cast (Nat.choose_le_two_pow (m i) j).trans (Nat.pow_le_pow_right (by decide) (hN i))
      have hmem : m i - j.val ∈ Finset.range (N+1) :=
        Finset.mem_range.mpr (Nat.lt_succ_of_le ((Nat.sub_le _ _).trans (hN i)))
      have hcoeff : ‖a i (m i-j)‖ ≤ b i :=
        Finset.single_le_sum (fun k _ ↦ norm_nonneg (a i k)) hmem
      exact mul_le_mul (mul_le_mul hchoose hcoeff (norm_nonneg _) (by positivity))
        (hf _) (norm_nonneg _) (mul_nonneg (by positivity) (hb i))
    have hsum : ‖(f i).comp A‖ ≤ ((N+1 : ℕ) : ℝ) * ((2 : ℝ)^N * b i * D) := by
      rw [hrow]
      refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun j _ ↦ hterm j).trans ?_)
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.succ_le_succ (hN i))
        (mul_nonneg (mul_nonneg (by positivity) (hb i)) hD.le)
    exact (mul_le_mul (hv i) hsum (norm_nonneg _) hB.le).trans_eq (by dsimp [C]; ring)
  have hbs : Summable b := summable_sum ha
  have hS : Summable (fun i ↦ ‖v i‖ * ‖(f i).comp A‖) :=
    (hbs.mul_left C).of_nonneg_of_le (fun _ ↦ by positivity) hmajor
  have hdiag (i : ι) : f i (A (v i)) = a i 0 := by
    change ((f i).comp A) (v i) = _
    rw [hrow, sum_apply, Finset.sum_eq_single (Fin.last (m i))]
    · rw [smul_apply, smul_eq_mul, hLast, hbi]
      simp
    · intro j _ hj
      rw [smul_apply, hbi, ite_eq_right (hOther i j hj), smul_zero]
    · simp
  obtain ⟨T,hT,hTn,hTd,hTr⟩ := traceClass_of_summable_biorthogonal_columns A v f hbi hzero hS
  refine ⟨T,hT,hTn.trans ?_, ?_, hTr.trans (tsum_congr hdiag)⟩
  · calc
      _ ≤ ∑' i, C * b i := hS.tsum_le_tsum hmajor (hbs.mul_left C)
      _ = _ := by
        rw [tsum_mul_left]
        congr 1
        exact Summable.tsum_finsetSum (s := Finset.range (N+1)) ha
  · simpa only [hdiag] using hTd


/-- A linear family with trace-class representatives bounded by a continuous
seminorm lifts continuously into the trace class. -/
theorem exists_continuous_traceClass_lift
    {E : Type*} [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E] [Module ℂ E]
    (A : E →ₗ[ℂ] (H →L[ℂ] H)) (P : Seminorm ℂ E) (hP : Continuous P)
    (h : ∀ x : E, ∃ T : TraceClass H, T.toOperator = A x ∧ ‖T‖ ≤ P x) :
    ∃ L : E →L[ℂ] TraceClass H, ∀ x, (L x).toOperator = A x := by
  choose T hT hnorm using h
  let L : E →ₗ[ℂ] TraceClass H :=
    { toFun := T
      map_add' := fun x y ↦ TraceClass.toOperator_injective (by
        change (T (x+y)).toOperator = (T x).toOperator + (T y).toOperator
        rw [hT, hT, hT, map_add])
      map_smul' := fun c x ↦ TraceClass.toOperator_injective (by
        change (T (c • x)).toOperator = c • (T x).toOperator
        rw [hT, hT, map_smul]) }
  refine ⟨⟨L, continuous_of_continuousAt_zero L ?_⟩,hT⟩
  rw [ContinuousAt, map_zero, Metric.tendsto_nhds]
  intro ε hε
  have hsmall : ∀ᶠ x : E in 𝓝 0, P x < ε :=
    hP.continuousAt.eventually (gt_mem_nhds (by simpa using hε : P 0 < ε))
  filter_upwards [hsmall] with x hx
  rw [dist_zero_right]
  exact (hnorm x).trans_lt hx

end
end Masullo
