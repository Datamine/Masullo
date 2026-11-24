import CompactSingularExpansion
import SchattenConvergence
import TraceClassNorm

open Filter Function InnerProductSpace Set
open scoped InnerProductSpace Topology

namespace Masullo

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Every absolutely summable rank-one presentation gives a compact operator. -/
theorem RankOneSeries.isCompactOperator (T : RankOneSeries ℕ H) : IsCompactOperator T.operator := by
  apply isCompactOperator_of_tendsto T.operator_summable.hasSum.tendsto_sum_nat
  refine Eventually.of_forall fun n => ?_
  let K := compactOperator (RingHom.id ℂ) H H
  change (∑ i ∈ Finset.range n, rankOne ℂ (T.image i) (T.functional i)) ∈ K
  apply Submodule.sum_mem K
  intro i _
  exact (isCompactOperator_of_locallyCompactSpace_rng
    (ContinuousLinearMap.toSpanSingleton ℂ (T.image i))).comp_clm
      (innerSL ℂ (T.functional i))

omit [CompleteSpace H] in
private theorem rankOne_cross_norm {ι : Type*} {e f : ι → H}
    (he : Orthonormal ℂ e) (hf : Orthonormal ℂ f) (u v : H) :
    Summable (fun i => ‖⟪f i, rankOne ℂ u v (e i)⟫_ℂ‖) ∧
      (∑' i, ‖⟪f i, rankOne ℂ u v (e i)⟫_ℂ‖) ≤ ‖u‖ * ‖v‖ := by
  have h (J : Finset ι) : (∑ i ∈ J, ‖⟪f i, rankOne ℂ u v (e i)⟫_ℂ‖) ≤ ‖u‖ * ‖v‖ := by
    have hu := (Real.sqrt_le_sqrt (hf.sum_inner_products_le (s := J) u)).trans_eq
      (Real.sqrt_sq (norm_nonneg _))
    have hv := (Real.sqrt_le_sqrt (he.sum_inner_products_le (s := J) v)).trans_eq
      (Real.sqrt_sq (norm_nonneg _))
    simp only [inner_right_rankOne_apply, norm_mul]
    simp_rw [norm_inner_symm (𝕜 := ℂ) v (e _)]
    exact (Real.sum_mul_le_sqrt_mul_sqrt J _ _).trans
      (mul_le_mul hu hv (Real.sqrt_nonneg _) (norm_nonneg _))
  have hs := summable_of_sum_le (fun _ => norm_nonneg _) h
  exact ⟨hs, hs.tsum_le_of_sum_le h⟩

private theorem RankOneSeries.cross_norm {ι : Type*} (T : RankOneSeries ℕ H)
    {e f : ι → H} (he : Orthonormal ℂ e) (hf : Orthonormal ℂ f) :
    Summable (fun i => ‖⟪f i, T.operator (e i)⟫_ℂ‖) ∧
      (∑' i, ‖⟪f i, T.operator (e i)⟫_ℂ‖) ≤ T.mass := by
  let d (j : ℕ) (i : ι) := ⟪f i, rankOne ℂ (T.image j) (T.functional j) (e i)⟫_ℂ
  have hrow (j : ℕ) := rankOne_cross_norm he hf (T.image j) (T.functional j)
  have hprod : Summable (fun p : ℕ × ι => ‖d p.1 p.2‖) :=
    (summable_prod_of_nonneg (fun _ => norm_nonneg _)).mpr
      ⟨fun j => (hrow j).1, T.summableNorm.of_nonneg_of_le
        (fun _ => tsum_nonneg fun _ => norm_nonneg _) (fun j => (hrow j).2)⟩
  have hle (i : ι) : ‖⟪f i, T.operator (e i)⟫_ℂ‖ ≤ ∑' j, ‖d j i‖ := by
    let L := (innerSL ℂ (f i)).comp (ContinuousLinearMap.apply ℂ H (e i))
    have hd : ⟪f i, T.operator (e i)⟫_ℂ = ∑' j, d j i :=
      ((T.operator_summable.hasSum.mapL L).tsum_eq).symm
    rw [hd]
    exact norm_tsum_le_tsum_norm (hprod.prod_symm.prod_factor i)
  have hs := hprod.prod_symm.prod.of_nonneg_of_le (fun _ => norm_nonneg _) hle
  refine ⟨hs, (hs.tsum_le_tsum hle hprod.prod_symm.prod).trans ?_⟩
  rw [Summable.tsum_comm (f := fun j i => ‖d j i‖) hprod]
  exact hprod.prod.tsum_le_tsum (fun j => (hrow j).2) T.summableNorm

private theorem IsSingularExpansion.sum_le_mass {s : ℕ → ℝ} {e f : ℕ → H}
    (T : RankOneSeries ℕ H) (h : IsSingularExpansion T.operator s e f) :
    Summable s ∧ (∑' i, s i) ≤ T.mass := by
  classical
  let I := {i : ℕ // 0 < s i}
  have habs := T.cross_norm h.sourceOrthonormal h.targetOrthonormal
  have he (i : I) : ‖⟪f i.val, T.operator (e i.val)⟫_ℂ‖ = s i :=
    by
      rw [h.apply_source i.property, inner_smul_right, inner_self_eq_norm_sq_to_K,
        h.targetOrthonormal.norm_eq_one i]
      simp [Complex.norm_real, Real.norm_of_nonneg (h.nonnegative _)]
  have hsum : Summable (fun i : I => s i) := habs.1.congr he
  have hbound : (∑' i : I, s i) ≤ T.mass :=
    le_trans (le_of_eq (tsum_congr he).symm) habs.2
  have hfin (J : Finset ℕ) : (∑ i ∈ J, s i) ≤ T.mass := by
    rw [← Finset.sum_preimage (fun i : I => i.val) J Subtype.val_injective.injOn s
      (fun i _ hi => le_antisymm (le_of_not_gt fun hp => hi ⟨⟨i, hp⟩, rfl⟩) (h.nonnegative i))]
    exact (hsum.sum_le_tsum _ (fun (i : I) _ => h.nonnegative i)).trans hbound
  have hS := summable_of_sum_le h.nonnegative hfin
  exact ⟨hS, hS.tsum_le_of_sum_le hfin⟩

private theorem IsSingularExpansion.exists_series_of_summable {A : H →L[ℂ] H}
    {s : ℕ → ℝ} {e f : ℕ → H} (h : IsSingularExpansion A s e f) (hs : Summable s) :
    ∃ T : RankOneSeries ℕ H, T.operator = A ∧ T.mass = ∑' i, s i := by
  let u (i : ℕ) := (s i : ℂ) • f i
  have hu (i : ℕ) : ‖u i‖ * ‖e i‖ = s i := by
    by_cases hi : 0 < s i
    · have he : ‖e i‖ = 1 := h.sourceOrthonormal.norm_eq_one ⟨i, hi⟩
      have hf : ‖f i‖ = 1 := h.targetOrthonormal.norm_eq_one ⟨i, hi⟩
      change ‖(s i : ℂ) • f i‖ * ‖e i‖ = _
      rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (h.nonnegative i), he, hf, mul_one, mul_one]
    · have hz := le_antisymm (le_of_not_gt hi) (h.nonnegative i)
      simp [u, hz]
  let T : RankOneSeries ℕ H := ⟨u, e, hs.congr fun i => (hu i).symm⟩
  refine ⟨T, ?_, tsum_congr hu⟩
  ext x : 1
  apply tendsto_nhds_unique ?_ (h.pointwise x)
  have he := (T.operator_summable.hasSum.mapL (ContinuousLinearMap.apply ℂ H x)).tendsto_sum_nat
  change Tendsto (fun n => ∑ i ∈ Finset.range n, rankOne ℂ (u i) (e i) x) atTop
    (𝓝 (T.operator x)) at he
  apply he.congr
  intro n
  apply Finset.sum_congr rfl
  intro i _
  simp only [rankOne_apply, u, smul_comm (⟪e i, x⟫_ℂ)]

/-- The approximation-number definition of Schatten-1 gives precisely the
absolutely summable rank-one ideal. -/
theorem isSchatten_one_iff_nuclear (A : H →L[ℂ] H) :
    IsSchatten 1 A ↔ A ∈ nuclearOperators H := by
  constructor
  · rintro ⟨hc, ha⟩
    obtain ⟨s, e, f, h, _⟩ := compactOperator_hasSingularExpansion A hc
    have hs : Summable s := by simpa only [Real.rpow_one, h.approximationNumber_eq] using ha
    obtain ⟨T, hT, _⟩ := h.exists_series_of_summable hs
    exact ⟨T, hT⟩
  · rintro ⟨T, rfl⟩
    obtain ⟨s, e, f, h, _⟩ := compactOperator_hasSingularExpansion T.operator T.isCompactOperator
    exact ⟨T.isCompactOperator, by
      simpa only [Real.rpow_one, h.approximationNumber_eq] using (h.sum_le_mass T).1⟩

theorem nuclearOperators_of_finiteRank (A : H →L[ℂ] H)
    [FiniteDimensional ℂ (LinearMap.range A.toLinearMap)] : A ∈ nuclearOperators H := by
  obtain ⟨n, u, v, hA⟩ := TraceClass.finiteRank_operator_decomposition A
  rw [hA]
  apply Submodule.sum_mem
  intro i _
  exact ⟨RankOneSeries.singleRepresentation (u i) (v i),
    RankOneSeries.singleRepresentation_operator (u i) (v i)⟩

/-- The spectral Schatten-1 norm equals the infimum of nuclear presentation masses. -/
theorem schattenNorm_one_eq_nuclearTraceNorm {A : H →L[ℂ] H} (hA : A ∈ nuclearOperators H) :
    schattenNorm 1 A = nuclearTraceNorm A := by
  obtain ⟨hc, hs⟩ := (isSchatten_one_iff_nuclear A).mpr hA
  obtain ⟨s, e, f, h, _⟩ := compactOperator_hasSingularExpansion A hc
  have hs' : Summable s := by simpa only [Real.rpow_one, h.approximationNumber_eq] using hs
  obtain ⟨T, hT, hmass⟩ := h.exists_series_of_summable hs'
  simp only [schattenNorm, Real.rpow_one, inv_one, h.approximationNumber_eq]
  apply le_antisymm
  · unfold nuclearTraceNorm
    have hne : {m | ∃ R : RankOneSeries ℕ H, R.operator = A ∧ m = R.mass}.Nonempty :=
      ⟨T.mass, T, hT, rfl⟩
    apply le_csInf hne
    rintro _ ⟨R, hR, rfl⟩
    rw [← hR] at h
    exact (h.sum_le_mass R).2
  · rw [← hmass, ← hT]
    exact nuclearTraceNorm_le_representation T

theorem TraceClass.dist_eq_schattenNorm_one (T S : TraceClass H) :
    dist T S = schattenNorm 1 (T.toOperator - S.toOperator) := by
  rw [dist_eq_norm]
  change nuclearTraceNorm (T - S).toOperator = schattenNorm 1 (T - S).toOperator
  exact (schattenNorm_one_eq_nuclearTraceNorm (T - S).toOperator_mem).symm

/-- Strong convergence of uniformly bounded operators yields trace-norm
convergence after composition with a fixed nuclear operator. -/
theorem RankOneSeries.tendsto_leftComp_traceClass (T : RankOneSeries ℕ H)
    (P : ℕ → H →L[ℂ] H) {C : ℝ} (hP : ∀ n, ‖P n‖ ≤ C)
    (ht : ∀ x, Tendsto (fun n => P n x) atTop (𝓝 x)) :
    Tendsto (fun n => TraceClass.ofSeries (T.leftComp (P n))) atTop
      (𝓝 (TraceClass.ofSeries T)) := by
  rw [tendsto_iff_dist_tendsto_zero]
  have hm := T.leftCutoff_representation_mass_tendsto P hP ht
  apply squeeze_zero (fun _ => dist_nonneg) _ hm
  intro n
  let E := T.leftComp (P n - ContinuousLinearMap.id ℂ H)
  have he : TraceClass.ofSeries E =
      TraceClass.ofSeries (T.leftComp (P n)) - TraceClass.ofSeries T := by
    apply TraceClass.toOperator_injective
    change E.operator = (T.leftComp (P n)).operator - T.operator
    rw [show E.operator = (P n - ContinuousLinearMap.id ℂ H).comp T.operator
      from T.operator_leftComp _, T.operator_leftComp]
    ext x
    simp
  rw [dist_eq_norm, ← he]
  exact TraceClass.norm_ofSeries_le E

/-- On trace class the Schatten-2 norm is bounded by the Schatten-1 norm. -/
theorem schattenNorm_two_le_one {A : H →L[ℂ] H} (hA : A ∈ nuclearOperators H) :
    schattenNorm 2 A ≤ schattenNorm 1 A := by
  have hs : Summable (fun i => approximationNumber i A) := by
    simpa only [Real.rpow_one] using ((isSchatten_one_iff_nuclear A).2 hA).2
  let a (i : ℕ) := approximationNumber i A
  have ha (i : ℕ) : 0 ≤ a i := approximationNumber_nonneg i A
  have hfin (J : Finset ℕ) : (∑ i ∈ J, a i ^ 2) ≤ (∑' i, a i) ^ 2 :=
    (Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => ha i)).trans
      (pow_le_pow_left₀ (Finset.sum_nonneg fun i _ => ha i) (hs.sum_le_tsum J (fun i _ => ha i)) 2)
  have ht := (summable_of_sum_le (fun i => sq_nonneg (a i)) hfin).tsum_le_of_sum_le hfin
  simp only [schattenNorm, Real.rpow_one, inv_one, Real.rpow_two]
  rw [← one_div, ← Real.sqrt_eq_rpow, ← Real.sqrt_sq (tsum_nonneg ha)]
  exact Real.sqrt_le_sqrt ht

theorem TraceClass.tendsto_schatten_errors {ι : Type*} {l : Filter ι}
    {T : ι → TraceClass H} {A : TraceClass H} (h : Tendsto T l (𝓝 A)) :
    Tendsto (fun i => schattenNorm 1 ((T i).toOperator - A.toOperator)) l (𝓝 0) ∧
      Tendsto (fun i => schattenNorm 2 ((T i).toOperator - A.toOperator)) l (𝓝 0) := by
  have h₁ : Tendsto (fun i => schattenNorm 1 ((T i).toOperator - A.toOperator)) l (𝓝 0) := by
    simpa only [TraceClass.dist_eq_schattenNorm_one] using tendsto_iff_dist_tendsto_zero.mp h
  refine ⟨h₁, squeeze_zero (fun _ => Real.rpow_nonneg (tsum_nonneg fun _ =>
    Real.rpow_nonneg (approximationNumber_nonneg _ _) _) _) (fun i => ?_) h₁⟩
  exact schattenNorm_two_le_one (T i - A).toOperator_mem
end

end Masullo
