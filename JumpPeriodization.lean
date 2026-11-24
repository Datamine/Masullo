import MellinJumps
import Mathlib.Topology.Instances.Int
import Mathlib.MeasureTheory.Constructions.Polish.Basic

open Complex Filter Function MeasureTheory Set Topology

namespace Masullo

noncomputable section

/-- Exponential decay gives an absolutely summable majorant on all
integer translates of the centered unit interval. -/
theorem integerTranslate_summable_majorant {u : ℝ → ℂ} (hu : SuperExponentialLogDecay u) :
    ∃ D : ℤ → ℝ, Summable D ∧ (∀ n, 0 ≤ D n) ∧
      ∀ (x : ℝ) (n : ℤ), |x| ≤ 1 / 2 → ‖u ((n : ℝ) + x)‖ ≤ D n := by
  obtain ⟨K, hK, hb⟩ := hu.global_bound 1 zero_le_one
  let C := K * Real.exp (1 / 2)
  let D (n : ℤ) := C * Real.exp (-|(n : ℝ)|)
  have hs : Summable (fun n : ℤ => Real.exp (-|(n : ℝ)|)) := by
    apply summable_int_iff_summable_nat_and_neg.mpr
    constructor
    · simpa only [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) _)] using Real.summable_exp_neg_nat
    · simpa only [Int.cast_neg, Int.cast_natCast, abs_neg, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) _)] using
        Real.summable_exp_neg_nat
  refine ⟨D, hs.mul_left C, fun n => by dsimp [D, C]; positivity, fun x n hx => ?_⟩
  have hn : -|(n : ℝ) + x| ≤ 1 / 2 - |(n : ℝ)| := by
    have h := abs_add_le ((n : ℝ) + x) (-x)
    rw [add_neg_cancel_right, abs_neg] at h
    linarith
  calc
    _ ≤ K * Real.exp (-|(n : ℝ) + x|) := by simpa only [neg_mul, one_mul] using hb ((n : ℝ) + x)
    _ ≤ K * Real.exp (1 / 2 - |(n : ℝ)|) := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hn) hK.le
    _ = D n := by rw [sub_eq_add_neg, Real.exp_add]; simp [D, C, mul_assoc]

theorem finite_jump_integer_translate_gap (S : Finset ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 2 ∧
      ∀ (x : ℝ) (n : ℤ), 0 < |x| → |x| < δ → (n : ℝ) + x ∉ S := by
  classical
  let Z (c : S) : Set ℝ :=
    (fun n : ℤ => (c : ℝ) - n) '' {n : ℤ | (c : ℝ) - n ≠ 0}
  have hZ (c : S) : IsClosed (Z c) := by
    have h : IsClosedEmbedding (fun n : ℤ => (c : ℝ) - n) :=
      (Homeomorph.subLeft (c : ℝ)).isClosedEmbedding.comp Int.isClosedEmbedding_coe_real
    exact h.isClosedMap _ (isClosed_discrete _)
  let V := (⋃ c : S, Z c)ᶜ
  have hV : IsOpen V := (isClosed_iUnion_of_finite hZ).isOpen_compl
  have h0 : 0 ∈ V := by
    intro h
    obtain ⟨c, n, hn, he⟩ := mem_iUnion.mp h
    exact hn he
  obtain ⟨ε, hε, hsub⟩ := Metric.isOpen_iff.mp hV 0 h0
  refine ⟨min ε (1 / 2), lt_min hε (by norm_num), min_le_right _ _, fun x n hx hδ hmem => ?_⟩
  have hb : x ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero]
    exact hδ.trans_le (min_le_left _ _)
  have h := hsub (hb : x ∈ Metric.ball (0 : ℝ) ε)
  let c : S := ⟨(n : ℝ) + x, hmem⟩
  have he : (c : ℝ) - n = x := by dsimp [c]; ring
  exact h (mem_iUnion.mpr ⟨c, n, fun hn => (abs_pos.mp hx) (he.symm.trans hn), he⟩)

private theorem translated_right_difference
    {u v : ℝ → ℂ} {x : ℝ} {L : ℂ} {B : ℝ}
    (hx : 0 < x) (hv : Measurable v)
    (hd : ∀ y ∈ Ioo (0 : ℝ) x, HasDerivAt u (v y) y)
    (huc : ContinuousAt u x) (hL : Tendsto u (𝓝[>] (0 : ℝ)) (𝓝 L))
    (hB : ∀ y ∈ Ioc (0 : ℝ) x, ‖v y‖ ≤ B) :
    ‖u x - L‖ ≤ B * x := by
  have hm : ∀ᵐ y ∂volume.restrict (Ioc (0 : ℝ) x), ‖v y‖ ≤ B :=
    (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall hB)
  have hi : IntervalIntegrable v volume 0 x := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hx.le]
    exact (integrableOn_const (C := B) (measure_Ioc_lt_top.ne)).mono' hv.aestronglyMeasurable hm
  rw [← intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hx hd hi hL
    (huc.tendsto.mono_left nhdsWithin_le_nhds), intervalIntegral.integral_of_le hx.le]
  have h := norm_integral_le_of_norm_le_const hm
  simpa [Measure.real, ENNReal.toReal_ofReal hx.le] using h

/-- The midpoint condition for the periodized test follows from the
summable derivative majorant on the two sides of the finitely many jumps. -/
theorem jumpPeriodization_midpoint_bound
    {u v left right : ℝ → ℂ} (S : Finset ℝ)
    (hu : SuperExponentialLogDecay u) (hv : SuperExponentialLogDecay v)
    (hmv : Measurable v) (hd : ∀ x ∉ S, HasDerivAt u (v x) x)
    (hl : ∀ x, Tendsto u (𝓝[<] x) (𝓝 (left x)))
    (hr : ∀ x, Tendsto u (𝓝[>] x) (𝓝 (right x))) :
    let β := fun x : ℝ => ∑' n : ℤ, u ((n : ℝ) + x)
    let L := (∑' n : ℤ, left n) + ∑' n : ℤ, right n
    (Summable fun n : ℤ => ‖left n‖) ∧ (Summable fun n : ℤ => ‖right n‖) ∧
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Ioc (0 : ℝ) (1 / 2), ‖β x + β (-x) - L‖ ≤ C * x := by
  obtain ⟨A, hA, hA₀, ha⟩ := integerTranslate_summable_majorant hu
  obtain ⟨D, hD, hD₀, hder⟩ := integerTranslate_summable_majorant hv
  obtain ⟨δ, hδ, hδ₁, hgap⟩ := finite_jump_integer_translate_gap S
  let M := ∑' n : ℤ, A n
  let B := ∑' n : ℤ, D n
  let β := fun x : ℝ => ∑' n : ℤ, u ((n : ℝ) + x)
  let L₁ := ∑' n : ℤ, left n
  let L₂ := ∑' n : ℤ, right n
  have hM : 0 ≤ M := tsum_nonneg hA₀
  have hB : 0 ≤ B := tsum_nonneg hD₀
  have huLeft (n : ℤ) : ‖left n‖ ≤ A n := by
    apply le_of_tendsto ((hl n).norm)
    filter_upwards [Ioo_mem_nhdsLT (show (n : ℝ) - 1 / 2 < n by linarith)] with t ht
    have h : |t - (n : ℝ)| ≤ 1 / 2 := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hn : (n : ℝ) + (t - n) = t := by ring
    simpa only [hn] using ha (t - n) n h
  have huRight (n : ℤ) : ‖right n‖ ≤ A n := by
    apply le_of_tendsto ((hr n).norm)
    filter_upwards [Ioo_mem_nhdsGT (show (n : ℝ) < n + 1 / 2 by linarith)] with t ht
    have h : |t - (n : ℝ)| ≤ 1 / 2 := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hn : (n : ℝ) + (t - n) = t := by ring
    simpa only [hn] using ha (t - n) n h
  have hsLeft := hA.of_nonneg_of_le (fun n : ℤ => norm_nonneg (left n)) huLeft
  have hsRight := hA.of_nonneg_of_le (fun n : ℤ => norm_nonneg (right n)) huRight
  refine ⟨hsLeft, hsRight, ?_⟩
  have hs (x : ℝ) (hx : |x| ≤ 1 / 2) : Summable (fun n : ℤ => ‖u ((n : ℝ) + x)‖) :=
    hA.of_nonneg_of_le (fun _ => norm_nonneg _) fun n => ha x n hx
  have hnormβ (x : ℝ) (hx : |x| ≤ 1 / 2) : ‖β x‖ ≤ M :=
    (norm_tsum_le_tsum_norm (hs x hx)).trans ((hs x hx).tsum_le_tsum (fun n => ha x n hx) hA)
  have hL₁ : ‖L₁‖ ≤ M :=
    (norm_tsum_le_tsum_norm hsLeft).trans (hsLeft.tsum_le_tsum huLeft hA)
  have hL₂ : ‖L₂‖ ≤ M :=
    (norm_tsum_le_tsum_norm hsRight).trans (hsRight.tsum_le_tsum huRight hA)
  refine ⟨max (2 * B) (4 * M / δ), (by positivity : 0 ≤ max (2 * B) (4 * M / δ)), fun x hx => ?_⟩
  have hax : |x| ≤ 1 / 2 := (abs_of_pos hx.1).symm ▸ hx.2
  have han : |-x| ≤ 1 / 2 := abs_neg x ▸ hax
  by_cases hsmall : x < δ
  · have hplus (n : ℤ) : ‖u ((n : ℝ) + x) - right n‖ ≤ D n * x := by
      let m := (n : ℝ)
      have hnot (y : ℝ) (hy : y ∈ Ioc (0 : ℝ) x) : m + y ∉ S :=
        hgap y n (abs_pos.mpr hy.1.ne') ((abs_of_pos hy.1).symm ▸ hy.2.trans_lt hsmall)
      have hi (y : ℝ) (hy : y ∈ Ioc (0 : ℝ) x) : ‖v (m + y)‖ ≤ D n :=
        hder y n (by rw [abs_of_pos hy.1]; exact hy.2.trans hx.2)
      have hc : Continuous (fun y : ℝ => m + y) := by fun_prop
      have hdx : ContinuousAt (fun y : ℝ => u (m + y)) x :=
        ((hd _ (hnot x ⟨hx.1, le_rfl⟩)).continuousAt).comp hc.continuousAt
      have ht : Tendsto (fun y : ℝ => m + y) (𝓝[>] (0 : ℝ)) (𝓝[>] m) := by
        refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
        · simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
        · filter_upwards [self_mem_nhdsWithin] with y (hy : 0 < y)
          simpa only [mem_Ioi, lt_add_iff_pos_right] using hy
      apply translated_right_difference hx.1 (hmv.comp (measurable_const.add measurable_id)) _ hdx
        ((hr m).comp ht) hi
      intro y hy
      change HasDerivAt (fun t : ℝ => u (m + t)) (v (m + y)) y
      have hh : HasDerivAt (fun t : ℝ => m + t) (1 : ℝ) y := (hasDerivAt_id y).const_add m
      simpa only [Function.comp_def, one_smul] using (hd _ (hnot y ⟨hy.1, hy.2.le⟩)).scomp y hh
    have hminus (n : ℤ) : ‖u ((n : ℝ) + -x) - left n‖ ≤ D n * x := by
      let m := (n : ℝ)
      have hnot (y : ℝ) (hy : y ∈ Ioc (0 : ℝ) x) : m + -y ∉ S :=
        hgap (-y) n (by simp [abs_neg, hy.1.ne']) (by rw [abs_neg, abs_of_pos hy.1]; exact hy.2.trans_lt hsmall)
      have hi (y : ℝ) (hy : y ∈ Ioc (0 : ℝ) x) : ‖-v (m + -y)‖ ≤ D n := by
        rw [norm_neg]
        exact hder (-y) n (by rw [abs_neg, abs_of_pos hy.1]; exact hy.2.trans hx.2)
      have hc : Continuous (fun y : ℝ => m + -y) := by fun_prop
      have hdx : ContinuousAt (fun y : ℝ => u (m + -y)) x := by
        change ContinuousAt (u ∘ (fun y : ℝ => m + -y)) x
        exact ContinuousAt.comp (f := fun y : ℝ => m + -y) (g := u) (x := x)
          (hd _ (hnot x ⟨hx.1, le_rfl⟩)).continuousAt hc.continuousAt
      have ht : Tendsto (fun y : ℝ => m + -y) (𝓝[>] (0 : ℝ)) (𝓝[<] m) := by
        refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
        · simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
        · filter_upwards [self_mem_nhdsWithin] with y (hy : 0 < y)
          change m + -y < m
          linarith
      apply translated_right_difference (v := fun y => -v (m + -y)) hx.1
        ((hmv.comp (measurable_const.add measurable_neg)).neg) _ hdx ((hl m).comp ht) hi
      intro y hy
      have hh : HasDerivAt (fun t : ℝ => m + -t) (-1 : ℝ) y := ((hasDerivAt_id y).neg).const_add m
      simpa only [Function.comp_def, neg_smul, one_smul] using
        (hd _ (hnot y ⟨hy.1, hy.2.le⟩)).scomp y hh
    have hts (x : ℝ) (hx : |x| ≤ 1 / 2) (c : ℤ → ℂ) (hc : Summable (fun n => ‖c n‖))
        (hb : ∀ n : ℤ, ‖u ((n : ℝ) + x) - c n‖ ≤ D n * |x|) :
        ‖β x - ∑' n, c n‖ ≤ B * |x| := by
      have hsum := (hD.mul_right |x|).of_nonneg_of_le (fun n => norm_nonneg _) hb
      rw [← (hs x hx).of_norm.tsum_sub hc.of_norm]
      exact (norm_tsum_le_tsum_norm hsum).trans
        ((hsum.tsum_le_tsum hb (hD.mul_right |x|)).trans_eq tsum_mul_right)
    have hplus' : ‖β x - L₂‖ ≤ B * x := by
      simpa only [abs_of_pos hx.1] using hts x hax (fun n => right n) hsRight
        (fun n => by rw [abs_of_pos hx.1]; exact hplus n)
    have hminus' : ‖β (-x) - L₁‖ ≤ B * x := by
      simpa only [abs_neg, abs_of_pos hx.1] using hts (-x) han (fun n => left n) hsLeft
        (fun n => by rw [abs_neg, abs_of_pos hx.1]; exact hminus n)
    change ‖β x + β (-x) - (L₁ + L₂)‖ ≤ _
    rw [show β x + β (-x) - (L₁ + L₂) = (β x - L₂) + (β (-x) - L₁) by ring]
    exact (norm_add_le _ _).trans ((add_le_add hplus' hminus').trans
      ((by ring : B * x + B * x = 2 * B * x).le.trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) hx.1.le)))
  · change ‖β x + β (-x) - (L₁ + L₂)‖ ≤ _
    have h : ‖β x + β (-x) - (L₁ + L₂)‖ ≤ 4 * M := by
      have he := (norm_sub_le _ _).trans (add_le_add (norm_add_le (β x) (β (-x))) (norm_add_le L₁ L₂))
      linarith [hnormβ x hax, hnormβ (-x) han]
    refine h.trans ?_
    have hdiv : 4 * M / δ * δ = 4 * M := div_mul_cancel₀ _ hδ.ne'
    calc
      4 * M = 4 * M / δ * δ := hdiv.symm
      _ ≤ max (2 * B) (4 * M / δ) * x :=
        mul_le_mul (le_max_right _ _) (le_of_not_gt hsmall) hδ.le (by positivity)

end

end Masullo
