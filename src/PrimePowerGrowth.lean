import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Fintype.Pi

open Filter Set
open scoped BigOperators

namespace Masullo

private theorem sum_geometric_max_bound {M : ℕ} {q : ℝ} (hq : 0 < q) (hq' : q < 1)
    (L : ℕ) (s : Finset (Fin M → ℕ)) :
    ∑ k ∈ s, q ^ ((Finset.univ.sup k) - L) ≤
      (↑L + 1 : ℝ) ^ M * ∑' j : ℕ, (↑j + 1 : ℝ) ^ M * q ^ j := by
  let excess (k : Fin M → ℕ) := Finset.univ.sup k - L
  have hmajor : Summable (fun j : ℕ => (↑j + 1 : ℝ) ^ M * q ^ j) := by
    have hnorm : ‖q‖ < 1 := by rwa [Real.norm_of_nonneg hq.le]
    have h0 : Summable (fun n : ℕ => (↑n : ℝ) ^ M * q ^ n) :=
      summable_pow_mul_geometric_of_norm_lt_one M hnorm
    have hshift : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ M * q ^ (n + 1)) :=
      h0.comp_injective (fun _ _ h => Nat.add_right_cancel h)
    have he : (fun n : ℕ => (↑n + 1 : ℝ) ^ M * q ^ n) =
        fun n => q⁻¹ * (((n + 1 : ℕ) : ℝ) ^ M * q ^ (n + 1)) := by
      funext n
      push_cast
      rw [pow_succ]
      field_simp
    rw [he]
    exact hshift.mul_left (q⁻¹)
  have hcard (j : ℕ) :
      (s.filter (fun k => excess k = j)).card ≤ (L + j + 1) ^ M := by
    let b := Fintype.piFinset (fun _ : Fin M => Finset.range (L + j + 1))
    have hsub : s.filter (fun k => excess k = j) ⊆ b := by
      intro k hk
      refine Fintype.mem_piFinset.mpr fun i => Finset.mem_range.mpr ?_
      have hj := (Finset.mem_filter.mp hk).2
      have hi : k i ≤ Finset.univ.sup k := Finset.le_sup (Finset.mem_univ i)
      change Finset.univ.sup k - L = j at hj
      omega
    simpa [b, Fintype.card_piFinset] using Finset.card_le_card hsub
  classical
  calc
    _ = ∑ j ∈ s.image excess, ∑ k ∈ s.filter (fun k => excess k = j), q ^ excess k :=
      (Finset.sum_fiberwise_of_maps_to
        (fun k hk => Finset.mem_image_of_mem excess hk) (fun k => q ^ excess k)).symm
    _ ≤ ∑ j ∈ s.image excess, (↑L + 1 : ℝ) ^ M * ((↑j + 1 : ℝ) ^ M * q ^ j) := by
      refine Finset.sum_le_sum fun j _ => ?_
      have he : ∑ k ∈ s.filter (fun k => excess k = j), q ^ excess k =
          ((s.filter (fun k => excess k = j)).card : ℝ) * q ^ j := by
        rw [← nsmul_eq_mul, ← Finset.sum_const]
        exact Finset.sum_congr rfl fun k hk => congrArg (fun n => q ^ n)
          (Finset.mem_filter.mp hk).2
      rw [he, ← mul_assoc, ← mul_pow]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      refine (by exact_mod_cast hcard j : _ ≤ ((L : ℝ) + j + 1) ^ M).trans ?_
      apply pow_le_pow_left₀ (by positivity) _ _
      nlinarith [mul_nonneg (show 0 ≤ (L : ℝ) by positivity) (show 0 ≤ (j : ℝ) by positivity)]
    _ ≤ _ := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (hmajor.sum_le_tsum _ fun _ _ => by positivity)
        (by positivity)

/-- Lemma 2.4.1.2. The absolute prime-power sampling sum has logarithmic
growth near zero. The proof uses the largest coordinate to bound the tail. -/
theorem product_power_sampling_bound {M N : ℕ} (hM : 0 < M) (hN : 1 < N)
    (a : Fin M → ℝ) (ha : ∀ i, 1 < a i) (φ : ℝ → ℂ) {C A T : ℝ}
    (hC : 0 < C) (hA : 0 < A) (hT : 0 < T)
    (hglobal : ∀ t > 0, ‖φ t‖ ≤ C)
    (htail : ∀ t ≥ T, ‖φ t‖ ≤ A / t ^ N) :
    ∃ T₀ Cφ : ℝ, 0 < T₀ ∧ 0 < Cφ ∧ ∀ t, 0 < t → t < T₀ →
      Summable (fun k : Fin M → ℕ => ‖φ ((∏ i, a i ^ k i) * t)‖) ∧
        (∑' k : Fin M → ℕ, ‖φ ((∏ i, a i ^ k i) * t)‖) ≤ Cφ * |Real.log t| ^ M := by
  classical
  letI : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
  let b := Finset.univ.inf' Finset.univ_nonempty a
  have hb : 1 < b := (Finset.lt_inf'_iff _).mpr fun i _ => ha i
  have hba (i : Fin M) : b ≤ a i := Finset.inf'_le _ (Finset.mem_univ i)
  let q := (b ^ N)⁻¹
  have hq : 0 < q := by dsimp [q]; positivity
  have hq' : q < 1 := inv_lt_one_of_one_lt₀ (one_lt_pow₀ hb (by omega))
  let D := ∑' j : ℕ, (↑j + 1 : ℝ) ^ M * q ^ j
  let B := max C (A / T ^ N)
  let c := (|Real.log T| + 1) / Real.log b + 2
  have hc : 0 < c := by dsimp [c]; positivity [Real.log_pos hb]
  have hB : 0 < B := hC.trans_le (le_max_left ..)
  refine ⟨min T (Real.exp (-1)), B * (D + 1) * c ^ M,
    lt_min hT (Real.exp_pos _), by positivity, ?_⟩
  intro t ht ht₀
  have htT : t ≤ T := (lt_min_iff.mp ht₀).1.le
  have hlog : 1 ≤ |Real.log t| := by
    have h := Real.strictMonoOn_log ht (Real.exp_pos (-1)) (lt_min_iff.mp ht₀).2
    rw [Real.log_exp] at h
    exact (by linarith : (1 : ℝ) ≤ -Real.log t).trans (neg_le_abs _)
  let L := ⌈(Real.log T - Real.log t) / Real.log b⌉₊
  have hbLog : 0 < Real.log b := Real.log_pos hb
  have hL : (Real.log T - Real.log t) / Real.log b ≤ L := Nat.le_ceil _
  have hLT : T ≤ b ^ L * t := by
    apply (Real.log_le_log_iff hT (by positivity)).mp
    rw [Real.log_mul (by positivity) ht.ne', Real.log_pow]
    linarith [(div_le_iff₀ hbLog).mp hL]
  have hLbound : (↑L + 1 : ℝ) ≤ c * |Real.log t| := by
    have hle : (Real.log T - Real.log t) / Real.log b ≤
        ((|Real.log T| + 1) * |Real.log t|) / Real.log b := by
      apply div_le_div_of_nonneg_right _ hbLog.le
      have hmul := mul_le_mul_of_nonneg_left hlog (abs_nonneg (Real.log T))
      nlinarith [le_abs_self (Real.log T), neg_le_abs (Real.log t)]
    have hceil : (L : ℝ) < (Real.log T - Real.log t) / Real.log b + 1 :=
      Nat.ceil_lt_add_one (div_nonneg (sub_nonneg.mpr (Real.log_le_log ht htT)) hbLog.le)
    dsimp [c]
    calc
      _ ≤ (Real.log T - Real.log t) / Real.log b + 2 := by linarith
      _ ≤ (|Real.log T| + 1) * |Real.log t| / Real.log b + 2 * |Real.log t| := by linarith
      _ = _ := by ring
  let F (k : Fin M → ℕ) := ‖φ ((∏ i, a i ^ k i) * t)‖
  have hterm (k : Fin M → ℕ) : F k ≤ B * q ^ ((Finset.univ.sup k) - L) := by
    let m := Finset.univ.sup k
    have hprod (i : Fin M) : a i ^ k i ≤ ∏ j, a j ^ k j := by
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
      exact le_mul_of_one_le_right (pow_nonneg (zero_le_one.trans (ha i).le) _)
        (Finset.one_le_prod fun j _ => one_le_pow₀ (ha j).le)
    have hp : 0 < (∏ i, a i ^ k i) * t :=
      mul_pos (Finset.prod_pos fun i _ => pow_pos (zero_lt_one.trans (ha i)) _) ht
    by_cases hm : m ≤ L
    · simpa only [show Finset.univ.sup k - L = 0 from Nat.sub_eq_zero_of_le hm, pow_zero, mul_one]
        using (hglobal _ hp).trans (le_max_left C _)
    · obtain ⟨i, _, hi⟩ := Finset.univ.exists_mem_eq_sup Finset.univ_nonempty k
      have hbase : b ^ m ≤ ∏ j, a j ^ k j := by
        rw [show m = k i from hi]
        exact (pow_le_pow_left₀ (by positivity) (hba i) _).trans (hprod i)
      have hbex : b ^ m = b ^ L * b ^ (m - L) := by
        rw [← pow_add, Nat.add_sub_of_le (le_of_not_ge hm)]
      have harg : T * b ^ (m - L) ≤ (∏ j, a j ^ k j) * t := by
        calc
          _ ≤ (b ^ L * t) * b ^ (m - L) := mul_le_mul_of_nonneg_right hLT (by positivity)
          _ = b ^ m * t := by rw [hbex]; ring
          _ ≤ _ := mul_le_mul_of_nonneg_right hbase ht.le
      have hargT : T ≤ (∏ j, a j ^ k j) * t :=
        (le_mul_of_one_le_right hT.le (one_le_pow₀ hb.le)).trans harg
      refine (htail _ hargT).trans ?_
      calc
        _ ≤ A / (T * b ^ (m - L)) ^ N := by gcongr
        _ = (A / T ^ N) * q ^ (m - L) := by dsimp [q]; rw [mul_pow, div_mul_eq_div_div, inv_pow]; rw [← pow_mul, ← pow_mul, mul_comm (m - L) N]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
  have hsum (s : Finset (Fin M → ℕ)) :
      ∑ k ∈ s, F k ≤ B * ((↑L + 1 : ℝ) ^ M * D) := by
    refine (Finset.sum_le_sum fun k _ => hterm k).trans ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (sum_geometric_max_bound hq hq' L s) hB.le
  refine ⟨summable_of_sum_le (fun _ => norm_nonneg _) hsum,
    (Summable.tsum_le_of_sum_le (summable_of_sum_le (fun _ => norm_nonneg _) hsum) hsum).trans ?_⟩
  have hD : 0 ≤ D := tsum_nonneg fun _ => by positivity
  calc
    _ ≤ B * ((c * |Real.log t|) ^ M * (D + 1)) := by
      gcongr
      linarith
    _ = _ := by rw [mul_pow]; ring

end Masullo
