import Mathlib.Algebra.Module.ZLattice.Summable
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn

open Asymptotics Filter Function MeasureTheory Set
open scoped Topology

namespace Masullo

/-- On a line along a face of the unit square, a whole segment has norm one. -/
theorem supNorm_level_contains_face {y : ℝ} (hy : y ∈ Icc (-1 : ℝ) 1) :
    ‖(fun i : Fin 2 => if i = 0 then (1 : ℝ) else y)‖ = 1 := by
  apply le_antisymm
  · rw [pi_norm_le_iff_of_nonneg zero_le_one]
    intro i
    split_ifs
    · simp
    · simpa only [Real.norm_eq_abs] using abs_le.mpr hy
  · simpa using
      (norm_le_pi_norm (fun i : Fin 2 => if i = 0 then (1 : ℝ) else y) 0)

private theorem lattice_separation {E : Type*} [NormedAddCommGroup E]
    (L : Submodule ℤ E) [DiscreteTopology L] :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 2 ∧ ∀ x ∈ L, ∀ y ∈ L, x ≠ y → δ + δ ≤ dist x y := by
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_singleton_iff.mp
    (isOpen_discrete ({0} : Set L))
  let δ := min (ρ / 2) (1 / 2)
  refine ⟨δ, lt_min (by positivity) (by norm_num), min_le_right _ _, ?_⟩
  intro x hx y hy hxy
  by_contra! h
  have hdist : dist (⟨x - y, L.sub_mem hx hy⟩ : L) 0 < ρ := by
    change dist (x - y) 0 < ρ
    rw [dist_zero_right, ← dist_eq_norm]
    linarith [min_le_left (ρ / 2) (1 / 2)]
  exact hxy (sub_eq_zero.mp (congrArg Subtype.val (hball _ hdist)))

/-- Lemma 2.2.1.1. Packing disjoint balls of fixed radius into a slightly
thicker shell gives the codimension-one lattice count. The argument applies
to every discrete lattice, including lattices of full rank. -/
theorem lattice_shell_count {N : ℕ} (L : Submodule ℤ (Fin N → ℝ)) [DiscreteTopology L] :
    let shell (r : ℝ) := {x : Fin N → ℝ | ‖x‖ ∈ Ico r (r + 1)}
    (∀ r : ℝ, Bornology.IsBounded (shell r) ∧ MeasurableSet (shell r) ∧
      (shell r ∩ (L : Set (Fin N → ℝ))).Finite) ∧
    (fun r => ((shell r ∩ (L : Set (Fin N → ℝ))).ncard : ℝ))
      =O[atTop] (fun r => r ^ (N - 1)) := by
  let E := Fin N → ℝ
  let shell (r : ℝ) := {x : E | ‖x‖ ∈ Ico r (r + 1)}
  have hL : IsClosed (L : Set E) := @AddSubgroup.isClosed_of_discrete _ _ _ _ _
    L.toAddSubgroup (inferInstanceAs (DiscreteTopology L))
  have hS (r : ℝ) : Bornology.IsBounded (shell r) ∧ MeasurableSet (shell r) ∧
      (shell r ∩ (L : Set E)).Finite := by
    have hb : Bornology.IsBounded (shell r) :=
      (Metric.isBounded_ball (x := (0 : E)) (r := r + 1)).subset
        (fun x hx => by simpa using (show ‖x‖ < r + 1 from hx.2))
    exact ⟨hb, measurableSet_Ico.preimage continuous_norm.measurable,
      Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete hb hL⟩
  refine ⟨hS, ?_⟩
  obtain ⟨δ, hδ, hδ', hsep⟩ := lattice_separation L
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨4 * (N : ℝ) * 5 ^ (N - 1) / (2 * δ) ^ N, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
  let S := shell r ∩ (L : Set E)
  letI : Fintype S := (hS r).2.2.fintype
  let V : Set E := ⋃ z : S, Metric.ball z.val δ
  let outer := Metric.ball (0 : E) (r + 1 + δ)
  let inner := Metric.ball (0 : E) (r - δ)
  have hinner : 0 < r - δ := by linarith
  have houter : 0 < r + 1 + δ := by linarith
  have hdis : Pairwise (Disjoint on fun z : S => Metric.ball z.val δ) := by
    intro x y hxy
    exact Metric.ball_disjoint_ball (hsep x.val x.property.2 y.val y.property.2
      (fun h => hxy (Subtype.ext h)))
  have hV : V ⊆ outer \ inner := by
    intro x hx
    obtain ⟨z, hz⟩ := mem_iUnion.mp hx
    have hd : ‖x - z.val‖ < δ := by rwa [Metric.mem_ball, dist_eq_norm] at hz
    have hzr : ‖z.val‖ ∈ Ico r (r + 1) := z.property.1
    have h₁ := norm_sub_norm_le x z.val
    have h₂ := norm_sub_norm_le z.val x
    rw [norm_sub_rev] at h₂
    refine ⟨?_, ?_⟩
    · change dist x 0 < _
      rw [dist_zero_right]
      linarith [hzr.2]
    · change ¬ dist x 0 < _
      rw [dist_zero_right]
      linarith [hzr.1]
  have hv : volume V = ENNReal.ofReal ((S.ncard : ℝ) * (2 * δ) ^ N) := by
    rw [measure_iUnion hdis (fun _ => Metric.isOpen_ball.measurableSet)]
    simp only [Real.volume_pi_ball _ hδ, Fintype.card_fin, tsum_fintype,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Set.ncard_eq_toFinset_card']
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
    simp
  have hvol : volume (outer \ inner) =
      ENNReal.ofReal ((2 * (r + 1 + δ)) ^ N - (2 * (r - δ)) ^ N) := by
    have hs : inner ⊆ outer := Metric.ball_subset_ball (by linarith)
    rw [measure_sdiff hs Metric.isOpen_ball.nullMeasurableSet (by
      simp [inner, Real.volume_pi_ball _ hinner])]
    rw [Real.volume_pi_ball _ houter, Real.volume_pi_ball _ hinner, Fintype.card_fin,
      ENNReal.ofReal_sub _ (by positivity)]
  have hdiff : (S.ncard : ℝ) * (2 * δ) ^ N ≤
      (2 * (r + 1 + δ)) ^ N - (2 * (r - δ)) ^ N := by
    have hm := measure_mono (μ := volume) hV
    rw [hv, hvol] at hm
    exact (ENNReal.ofReal_le_ofReal_iff (by
      apply sub_nonneg.mpr
      gcongr
      linarith)).mp hm
  have hp := abs_pow_sub_pow_le (a := 2 * (r + 1 + δ)) (b := 2 * (r - δ)) (n := N)
  rw [abs_of_pos (by positivity : 0 < 2 * (r + 1 + δ)),
    abs_of_pos (by positivity : 0 < 2 * (r - δ)),
    max_eq_left (by linarith : 2 * (r - δ) ≤ 2 * (r + 1 + δ)),
    abs_of_nonneg (by linarith : 0 ≤ 2 * (r + 1 + δ) - 2 * (r - δ))] at hp
  have hpow : (2 * (r + 1 + δ)) ^ N - (2 * (r - δ)) ^ N ≤
      4 * (N : ℝ) * 5 ^ (N - 1) * r ^ (N - 1) := by
    calc
      _ ≤ (2 * (r + 1 + δ) - 2 * (r - δ)) * N * (2 * (r + 1 + δ)) ^ (N - 1) :=
        (le_abs_self _).trans hp
      _ ≤ 4 * (N : ℝ) * (5 * r) ^ (N - 1) := by
        have hwidth : 2 * (r + 1 + δ) - 2 * (r - δ) ≤ 4 := by linarith
        have hrad : 2 * (r + 1 + δ) ≤ 5 * r := by linarith
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hrad _) (by positivity)
          |>.trans' (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hwidth (by positivity)) (by positivity))
      _ = 4 * (N : ℝ) * 5 ^ (N - 1) * r ^ (N - 1) := by rw [mul_pow]; ring
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  change (S.ncard : ℝ) ≤ _
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  exact hdiff.trans hpow

/-- Disjoint fixed-radius balls around a discrete lattice give the
dimension-power bound on the number of points in a closed ball. -/
theorem lattice_closedBall_count {ι : Type*} [Fintype ι]
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L] :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 1 ≤ r →
      (Metric.closedBall (0 : ι → ℝ) r ∩ (L : Set (ι → ℝ))).Finite ∧
      ((Metric.closedBall (0 : ι → ℝ) r ∩ (L : Set (ι → ℝ))).ncard : ℝ) ≤
        C * r ^ Fintype.card ι := by
  classical
  obtain ⟨δ, hδ, _, hsep⟩ := lattice_separation L
  let n := Fintype.card ι
  refine ⟨((2 * (1 + δ)) / (2 * δ)) ^ n, by positivity, ?_⟩
  intro r hr
  let S := Metric.closedBall (0 : ι → ℝ) r ∩ (L : Set (ι → ℝ))
  have hL : IsClosed (L : Set (ι → ℝ)) :=
    @AddSubgroup.isClosed_of_discrete _ _ _ _ _ L.toAddSubgroup (inferInstanceAs (DiscreteTopology L))
  have hS : S.Finite :=
    Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete Metric.isBounded_closedBall hL
  refine ⟨hS, ?_⟩
  letI : Fintype S := hS.fintype
  let V := ⋃ z : S, Metric.ball z.val δ
  have hdis : Pairwise (Disjoint on fun z : S => Metric.ball z.val δ) := by
    intro x y hxy
    apply Metric.ball_disjoint_ball
    exact hsep _ x.property.2 _ y.property.2 (fun e => hxy (Subtype.ext e))
  have hV : V ⊆ Metric.ball (0 : ι → ℝ) ((1 + δ) * r) := by
    intro x hx
    obtain ⟨y, hy⟩ := mem_iUnion.mp hx
    have h₁ : dist x y.val < δ := hy
    have h₂ : dist y.val 0 ≤ r := y.property.1
    have h₃ : dist x 0 < δ + r := (dist_triangle _ _ _).trans_lt (add_lt_add_of_lt_of_le h₁ h₂)
    exact h₃.trans_le (by nlinarith)
  have hvol : volume V = ENNReal.ofReal ((S.ncard : ℝ) * (2 * δ) ^ n) := by
    rw [measure_iUnion hdis (fun _ => Metric.isOpen_ball.measurableSet)]
    simp only [Real.volume_pi_ball _ hδ, tsum_fintype, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, Set.ncard_eq_toFinset_card']
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
    rw [← Set.ncard_eq_toFinset_card', Set.fintypeCard_eq_ncard]
  have hm := measure_mono (μ := volume) hV
  rw [hvol, Real.volume_pi_ball _ (mul_pos (by positivity) (by linarith))] at hm
  have hn : (S.ncard : ℝ) * (2 * δ) ^ n ≤ (2 * ((1 + δ) * r)) ^ n :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hm
  change (S.ncard : ℝ) ≤ _
  have he : (((2 * (1 + δ)) / (2 * δ)) ^ n * r ^ n) =
      (2 * ((1 + δ) * r)) ^ n / (2 * δ) ^ n := by
    rw [div_pow, div_mul_eq_mul_div, ← mul_pow]
    congr 1
    rw [mul_assoc]
  exact he.symm ▸ (le_div_iff₀ (show 0 < (2 * δ) ^ n by positivity)).mpr hn

/-- The exclusion in (2.2.1.3) leaves a zero denominator for a nonsymmetric
compact parameter set, already for the lattice of integers in the real line. -/
theorem printed_shifted_lattice_exclusion_fails :
    ∃ (K : Set ℝ), IsCompact K ∧
      ∃ (z : ℤ) (x : ℝ), (z : ℝ) ∉ K ∧ x ∈ K ∧ (z : ℝ) + x = 0 := by
  refine ⟨{-1}, isCompact_singleton, 1, -1, ?_, rfl, ?_⟩ <;> norm_num

/-- Corrected Proposition 2.2.1.3. The excluded lattice points are those in
the negative of the compact parameter set. Real exponents and the shift may
vary simultaneously over the indicated region. -/
theorem shifted_lattice_rpow_uniform {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L]
    [IsZLattice ℝ L] {K : Set E} (hK : IsCompact K)
    {ε : ℝ} (hε : 0 < ε) :
    let term (z : {z : L // -(z : E) ∉ K}) (p : ℝ × E) := ‖(z.val : E) + p.2‖ ^ (-p.1)
    HasSumUniformlyOn term (fun p => ∑' z, term z p)
      (Ici ((Module.finrank ℝ E : ℝ) + ε) ×ˢ K) := by
  dsimp only
  let a : ℝ := (Module.finrank ℝ E : ℝ) + ε
  have ha : 0 < a := by dsimp [a]; positivity
  obtain ⟨R, hR, hRK⟩ := hK.isBounded.exists_pos_norm_le
  have hL : IsClosed (L : Set E) := @AddSubgroup.isClosed_of_discrete _ _ _ _ _
    L.toAddSubgroup (inferInstanceAs (DiscreteTopology L))
  let B := Metric.closedBall (0 : E) (2 * R + 2)
  have hB : (B ∩ (L : Set E)).Finite :=
    Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete Metric.isBounded_closedBall hL
  let T := {z : L // -(z : E) ∉ K}
  let e : T ↪ E := ⟨fun z => z.val.val, Subtype.val_injective.comp Subtype.val_injective⟩
  have hmajor : Summable (fun z : T => (1 / 2 : ℝ) ^ (-a) * ‖(z.val : E)‖ ^ (-a)) := by
    have hr : -a < -(Module.finrank ℤ L : ℝ) := by
      rw [ZLattice.rank ℝ L]
      dsimp [a]
      linarith
    exact ((ZLattice.summable_norm_rpow L (-a) hr).mul_left _).subtype _
  apply HasSumUniformlyOn.of_norm_le_summable_eventually hmajor
  have htail : ∀ᶠ z : T in cofinite, e z ∉ B ∩ (L : Set E) :=
    (hB.preimage_embedding e).compl_mem_cofinite
  apply htail.mono
  intro z hz p hp
  have hz' : 2 * R + 2 < ‖(z.val : E)‖ := by
    have hzB : (z.val : E) ∉ B := fun h => hz ⟨h, z.val.property⟩
    simpa only [B, Metric.mem_closedBall, dist_zero_right, not_le] using hzB
  have hbase : 1 ≤ ‖(z.val : E) + p.2‖ := by
    linarith [norm_sub_norm_le (z.val : E) (-p.2), norm_neg p.2, hRK p.2 hp.2,
      show ‖(z.val : E) - -p.2‖ = ‖(z.val : E) + p.2‖ by rw [sub_neg_eq_add]]
  have hhalf : (1 / 2 : ℝ) * ‖(z.val : E)‖ ≤ ‖(z.val : E) + p.2‖ := by
    linarith [norm_sub_norm_le (z.val : E) (-p.2), norm_neg p.2, hRK p.2 hp.2,
      show ‖(z.val : E) - -p.2‖ = ‖(z.val : E) + p.2‖ by rw [sub_neg_eq_add]]
  rw [Real.norm_of_nonneg (by positivity), ← Real.mul_rpow (by norm_num) (norm_nonneg _)]
  exact (Real.rpow_le_rpow_of_exponent_le hbase (neg_le_neg hp.1)).trans
    (Real.rpow_le_rpow_of_nonpos (mul_pos (by norm_num) (lt_trans (by linarith) hz'))
      hhalf (neg_nonpos.mpr ha.le))

end Masullo
