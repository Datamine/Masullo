import BoundaryEulerProducts
import PrimeIdealCoefficients
import TruncatedPerron

open Filter Function Set Topology NumberField Ideal IsDedekindDomain
open scoped Classical Interval NumberField

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

local notation "Place" => HeightOneSpectrum (𝓞 F)
private abbrev primePowerNorm (j : Place × ℕ) := (heckePrimePowerIdeal F j).absNorm

local notation "normOf" => primePowerNorm F

/-- Prime powers of a prescribed absolute norm. The exponent in each pair is
indexed by its predecessor. -/
def heckePrimePowerNormFiber (n : ℕ) : Finset (Place × ℕ) :=
  (heckePrimePowerNormCutoff F ((n : ℝ) + 1)).filter (fun j ↦ normOf j = n)

@[simp] theorem mem_heckePrimePowerNormFiber {n : ℕ} {j : Place × ℕ} :
    j ∈ heckePrimePowerNormFiber F n ↔ normOf j = n := by
  rw [heckePrimePowerNormFiber, Finset.mem_filter, mem_heckePrimePowerNormCutoff]
  exact ⟨And.right, fun h ↦ ⟨by change (normOf j : ℝ) < n + 1; rw [h]; exact lt_add_one _, h⟩⟩

theorem card_heckePrimePowerNormFiber (n : ℕ) :
    (heckePrimePowerNormFiber F n).card ≤ Module.finrank ℚ F := by
  let e : (Place × ℕ) ↪ (Place × ℕ) :=
    ⟨fun j ↦ (j.1, j.2 + 1), by
      intro j k h
      have hfst := congrArg (fun p : Place × ℕ ↦ p.1) h
      have hsnd := congrArg (fun p : Place × ℕ ↦ p.2) h
      exact Prod.ext hfst (Nat.succ.inj hsnd)⟩
  rw [← Finset.card_map e]
  apply card_positivePrimePowers_of_norm F _ n
  intro a ha
  obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp ha
  exact ⟨Nat.succ_pos _, (mem_heckePrimePowerNormFiber F).mp hj⟩

private theorem one_lt_normOf (j : Place × ℕ) : 1 < normOf j := by
  change 1 < (heckePrimePowerIdeal F j).absNorm
  rw [heckePrimePowerIdeal, map_pow]
  exact Nat.one_lt_pow (Nat.succ_ne_zero _) (NumberField.HeightOneSpectrum.one_lt_absNorm j.1)

/-- The norm-indexed coefficient of the negative logarithmic derivative of the
Hecke Euler product, including all prime powers of a given norm. -/
def heckeVonMangoldtCoefficient (c : Place → ℂ) (n : ℕ) : ℂ :=
  ∑ j ∈ heckePrimePowerNormFiber F n,
    c j.1 ^ (j.2+1) * (Real.log (j.1.asIdeal.absNorm : ℝ) : ℂ)

theorem norm_heckeVonMangoldtCoefficient_le (c : Place → ℂ) (hc : ∀ v, ‖c v‖ ≤ 1)
    (n : ℕ) : ‖heckeVonMangoldtCoefficient F c n‖ ≤ (Module.finrank ℚ F : ℝ) * Real.log n := by
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_natCast_nonneg n
  calc
    _ ≤ ∑ j ∈ heckePrimePowerNormFiber F n,
      ‖c j.1 ^ (j.2+1) * (Real.log (j.1.asIdeal.absNorm : ℝ) : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ _j ∈ heckePrimePowerNormFiber F n, Real.log n := by
      apply Finset.sum_le_sum
      intro j hj
      have hp := NumberField.HeightOneSpectrum.one_lt_absNorm j.1
      have hN : j.1.asIdeal.absNorm ≤ n := by
        have he : (j.1.asIdeal.absNorm) ^ (j.2 + 1) = n := by
          simpa only [primePowerNorm, heckePrimePowerIdeal, map_pow] using
            (mem_heckePrimePowerNormFiber F).mp hj
        rw [← he]
        exact Nat.le_pow (Nat.succ_pos _)
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg
        (Real.log_nonneg (by exact_mod_cast hp.le))]
      exact (mul_le_of_le_one_left (Real.log_nonneg (by exact_mod_cast hp.le))
        (pow_le_one₀ (norm_nonneg _) (hc j.1))).trans
        (Real.log_le_log (by exact_mod_cast (zero_lt_one.trans hp)) (by exact_mod_cast hN))
    _ ≤ _ := by
      rw [Finset.sum_const, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast card_heckePrimePowerNormFiber F n) hlog

theorem term_heckeVonMangoldtCoefficient (c : Place → ℂ) (s : ℂ) (n : ℕ) :
    LSeries.term (heckeVonMangoldtCoefficient F c) s n =
      ∑ j ∈ heckePrimePowerNormFiber F n, heckePrimePowerTerm F c s j := by
  by_cases hn : n = 0
  · subst n
    have he : heckePrimePowerNormFiber F 0 = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (by
      intro j hj
      have h := (mem_heckePrimePowerNormFiber F).mp hj
      have hp := one_lt_normOf F j
      omega)
    simp [he]
  · rw [LSeries.term_of_ne_zero hn, heckeVonMangoldtCoefficient, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j hj
    have he := (mem_heckePrimePowerNormFiber F).mp hj
    unfold heckePrimePowerTerm
    change _ = _ * ((normOf j : ℕ) : ℂ) ^ (-s)
    rw [he, Complex.cpow_neg, div_eq_mul_inv]

/-- On the one-line the normalized terms have the majorant used to sum
the truncated Perron error. -/
theorem norm_term_heckeVonMangoldtCoefficient_le (c : Place → ℂ)
    (hc : ∀ v, ‖c v‖ ≤ 1) {s : ℂ} (hs : s.re = 1) (n : ℕ) :
    ‖LSeries.term (heckeVonMangoldtCoefficient F c) s n‖ ≤
      (Module.finrank ℚ F : ℝ) * Real.log n / n := by
  by_cases hn : n = 0
  · subst n
    simp
  rw [LSeries.term_of_ne_zero hn, norm_div,
    Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn), hs, Real.rpow_one]
  exact div_le_div_of_nonneg_right (norm_heckeVonMangoldtCoefficient_le F c hc n) (by positivity)

/-- Each near-cutoff off-diagonal contribution is bounded by an inverse
additive distance, with the logarithmic coefficient bound of B.6.1.4. -/
theorem heckePerronError_near_le (c : Place → ℂ) (hc : ∀ v, ‖c v‖ ≤ 1)
    {s : ℂ} (hs : s.re = 1) {x κ T : ℝ} (hx : 0 < x) (hκ : 0 < κ) (hT : 0 < T)
    {n : ℕ} (hn₁ : x / 2 ≤ (n : ℝ)) (hn₂ : (n : ℝ) ≤ 2 * x) (hne : x ≠ (n : ℝ)) :
    ‖LSeries.term (heckeVonMangoldtCoefficient F c) s n‖ *
        perronError (Real.log x - Real.log (n : ℝ)) κ T ≤
      2 * ((Module.finrank ℚ F : ℝ) * Real.log (2 * x)) * Real.exp (Real.log 2 * κ) /
        (Real.pi * T * |x - (n : ℝ)|) := by
  let y : ℝ := n
  let b := Real.log x - Real.log y
  have hy : 0 < y := (half_pos hx).trans_le hn₁
  have hd : 0 < |x - y| := abs_pos.mpr (sub_ne_zero.mpr hne)
  have hmax : 0 < max x y := hx.trans_le (le_max_left _ _)
  have hb := perronLogRatio_near hx hy
  have hb₀ : b ≠ 0 := abs_pos.mp ((div_pos hd hmax).trans_le hb)
  have hlog : Real.log y ≤ Real.log (2 * x) := Real.log_le_log hy hn₂
  have hlog₀ : 0 ≤ Real.log (2 * x) := (Real.log_natCast_nonneg n).trans hlog
  have hbx : b ≤ Real.log 2 := by
    have hlog' := Real.log_le_log hx (show x ≤ 2 * y by linarith)
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hy.ne'] at hlog'
    dsimp [b]
    linarith
  have hmax₂ : max x y ≤ 2 * y := max_le (by linarith) (by linarith)
  have hcoef := norm_term_heckeVonMangoldtCoefficient_le F c hc hs n
  change ‖LSeries.term (heckeVonMangoldtCoefficient F c) s n‖ ≤
    (Module.finrank ℚ F : ℝ) * Real.log y / y at hcoef
  change ‖LSeries.term (heckeVonMangoldtCoefficient F c) s n‖ * perronError b κ T ≤ _
  rw [perronError, ite_eq_right hb₀]
  calc
    _ ≤ ((Module.finrank ℚ F : ℝ) * Real.log (2 * x) / y) *
        (Real.exp (Real.log 2 * κ) / (Real.pi * T * (|x - y| / max x y))) := by
      have hterm : ‖LSeries.term (heckeVonMangoldtCoefficient F c) s n‖ ≤
          (Module.finrank ℚ F : ℝ) * Real.log (2 * x) / y := hcoef.trans (by gcongr)
      have hexp := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hbx hκ.le)
      gcongr
    _ = (max x y / y) * (((Module.finrank ℚ F : ℝ) * Real.log (2 * x)) *
          Real.exp (Real.log 2 * κ) / (Real.pi * T * |x - y|)) := by
      simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
      ring
    _ ≤ _ := by
      have hm : max x y / y ≤ 2 := (div_le_iff₀ hy).mpr hmax₂
      calc
        _ ≤ 2 * (((Module.finrank ℚ F : ℝ) * Real.log (2 * x)) *
            Real.exp (Real.log 2 * κ) / (Real.pi * T * |x - y|)) :=
          mul_le_mul_of_nonneg_right hm (by positivity)
        _ = _ := by change _ = _ / (Real.pi * T * |x - y|); ring

private theorem tsum_heckePrimePowerNormFiber {M : Type*} [AddCommMonoid M]
    [TopologicalSpace M] (f : (Place × ℕ) → M) (n : ℕ) :
    (∑' j : (normOf ⁻¹' {n} : Set (Place × ℕ)), f j) =
      ∑ j ∈ heckePrimePowerNormFiber F n, f j := by
  have he : (normOf ⁻¹' {n} : Set (Place × ℕ)) = heckePrimePowerNormFiber F n := by
    ext j
    exact (mem_heckePrimePowerNormFiber F).symm
  rw [he, Finset.tsum_subtype']

/-- Absolute convergence survives grouping the Euler coefficients by norm. -/
theorem summable_norm_term_heckeVonMangoldtCoefficient (c : Place → ℂ)
    (hc : ∀ v, ‖c v‖ ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n ↦ ‖LSeries.term (heckeVonMangoldtCoefficient F c) s n‖) := by
  have hh := (summable_norm_heckePrimePowerTerm F c hc hs).hasSum.tsum_fiberwise normOf
  have hsum := hh.summable.congr
    (tsum_heckePrimePowerNormFiber F (fun j ↦ ‖heckePrimePowerTerm F c s j‖))
  refine hsum.of_nonneg_of_le (fun _ ↦ norm_nonneg _) fun n ↦ ?_
  rw [term_heckeVonMangoldtCoefficient]
  exact norm_sum_le _ _

/-- The actual grouped Euler coefficients give the negative logarithmic
derivative throughout the half-plane of absolute convergence. -/
theorem lseries_heckeVonMangoldtCoefficient (c : Place → ℂ) (hc : ∀ v, ‖c v‖ ≤ 1)
    {s : ℂ} (hs : 1 < s.re) :
    LSeries (heckeVonMangoldtCoefficient F c) s =
      -logDeriv (fun z ↦ ∏' v, heckeEulerFactor F c v z) s := by
  have hh := (summable_norm_heckePrimePowerTerm F c hc hs).of_norm.hasSum.tsum_fiberwise normOf
  simpa only [tsum_heckePrimePowerNormFiber F, ← term_heckeVonMangoldtCoefficient F c s,
    ← neg_logDeriv_heckeEulerProduct F c hc hs, LSeries] using hh.tsum_eq

/-- Arbitrary norm weights commute with grouping in every strict norm cutoff. -/
theorem sum_term_heckeVonMangoldtCoefficient (c : Place → ℂ) (s : ℂ) (x : ℝ) (w : ℕ → ℂ) :
    ∑ n ∈ Finset.range ⌈x⌉₊, w n * LSeries.term (heckeVonMangoldtCoefficient F c) s n =
      ∑ j ∈ heckePrimePowerNormCutoff F x, w (normOf j) * heckePrimePowerTerm F c s j := by
  have hmaps (j : Place × ℕ) (hj : j ∈ heckePrimePowerNormCutoff F x) :
      normOf j ∈ Finset.range ⌈x⌉₊ :=
    Finset.mem_range.mpr (Nat.lt_ceil.mpr ((mem_heckePrimePowerNormCutoff F).mp hj))
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  apply Finset.sum_congr rfl
  intro n hn
  rw [term_heckeVonMangoldtCoefficient, Finset.mul_sum]
  have hsets : heckePrimePowerNormFiber F n =
      (heckePrimePowerNormCutoff F x).filter (fun j ↦ normOf j = n) := by
    ext j
    rw [mem_heckePrimePowerNormFiber, Finset.mem_filter, mem_heckePrimePowerNormCutoff]
    constructor
    · intro hj
      refine ⟨?_, hj⟩
      change (normOf j : ℝ) < x
      rw [hj]
      exact Nat.lt_ceil.mp (Finset.mem_range.mp hn)
    · exact And.right
  refine Finset.sum_congr hsets fun j hj ↦ ?_
  exact congrArg (fun k ↦ w k * heckePrimePowerTerm F c s j) (Finset.mem_filter.mp hj).2.symm

/-- Reciprocal-logarithm weighting of the grouped von Mangoldt terms gives
the truncated logarithm of the Euler product. -/
theorem sum_reciprocalLog_heckeVonMangoldtCoefficient (c : Place → ℂ) (s : ℂ) (x : ℝ) :
    ∑ n ∈ Finset.range ⌈x⌉₊, ((Real.log (n : ℝ))⁻¹ : ℂ) *
      LSeries.term (heckeVonMangoldtCoefficient F c) s n = heckePrimePowerLogPartial F c x s := by
  rw [sum_term_heckeVonMangoldtCoefficient, heckePrimePowerLogPartial]
  exact Finset.sum_congr rfl fun j _ ↦ heckePrimePowerLog_from_logDerivative F c s j

theorem sum_heckeVonMangoldtCoefficient_from_two (c : Place → ℂ) (s : ℂ)
    (w : ℕ → ℂ) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 2), w k * LSeries.term (heckeVonMangoldtCoefficient F c) s k =
      ∑ k ∈ Finset.range n, w (k + 2) * LSeries.term (heckeVonMangoldtCoefficient F c) s (k + 2) := by
  have h1 : heckePrimePowerNormFiber F 1 = ∅ := by
    refine Finset.eq_empty_iff_forall_notMem.mpr fun j hj ↦ ?_
    exact (one_lt_normOf F j).ne' ((mem_heckePrimePowerNormFiber F).mp hj)
  have ht1 : LSeries.term (heckeVonMangoldtCoefficient F c) s 1 = 0 := by
    rw [term_heckeVonMangoldtCoefficient, h1, Finset.sum_empty]
  rw [Nat.add_comm n 2, Finset.sum_range_add]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, LSeries.term_zero, ht1,
    mul_zero, add_zero, zero_add, Nat.add_comm 2]

/-- A uniform bound for the strict prime-power sums of the log derivative
implies uniform convergence of the actual logarithmic Euler sums. -/
theorem heckePrimePowerLogPartial_of_boundedLogDerivative (c : Place → ℂ) (D : Set ℂ) (C : ℝ)
    (hC : ∀ (x : ℝ), 2 ≤ x → ∀ s ∈ D,
      ‖∑ j ∈ heckePrimePowerNormCutoff F x, heckePrimePowerTerm F c s j‖ ≤ C) :
    ∃ L : ℂ → ℂ, TendstoUniformlyOn (heckePrimePowerLogPartial F c) L atTop D := by
  let a (n : ℕ) (s : ℂ) := LSeries.term (heckeVonMangoldtCoefficient F c) s (n + 2)
  let w (n : ℕ) := (Real.log (((n + 2 : ℕ) : ℝ)))⁻¹
  obtain ⟨hw, h₀, hlim⟩ := abelReciprocalLogWeight
  have hb (n : ℕ) (s : ℂ) (hs : s ∈ D) : ‖∑ k ∈ Finset.range n, a k s‖ ≤ C := by
    have ha := hC ((n + 2 : ℕ) : ℝ) (by exact_mod_cast (show 2 ≤ n + 2 by omega)) s hs
    have hg := sum_term_heckeVonMangoldtCoefficient F c s ((n + 2 : ℕ) : ℝ) (fun _ ↦ 1)
    rw [Nat.ceil_natCast, sum_heckeVonMangoldtCoefficient_from_two] at hg
    simp only [one_mul] at hg
    rwa [← hg] at ha
  obtain ⟨L, hL, _⟩ := abelWeightedSums_uniform D w a hw h₀ hlim C hb
  have hidx : Tendsto (fun x : ℝ ↦ ⌈x⌉₊ - 2) atTop atTop := by
    refine tendsto_atTop.mpr fun n ↦ ?_
    filter_upwards [(tendsto_nat_ceil_atTop (α := ℝ)).eventually (eventually_ge_atTop (n + 2))] with x hx
    exact Nat.le_sub_of_add_le hx
  have hcomp : TendstoUniformlyOn (fun x : ℝ ↦
      fun s ↦ ∑ k ∈ Finset.range (⌈x⌉₊ - 2), w k • a k s) L atTop D :=
    fun u hu ↦ hidx.eventually (hL u hu)
  refine ⟨L, hcomp.congr ?_⟩
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx s _
  have hn : 2 ≤ ⌈x⌉₊ := by exact_mod_cast hx.trans (Nat.le_ceil x)
  rw [← sum_reciprocalLog_heckeVonMangoldtCoefficient]
  conv_rhs => rw [← Nat.sub_add_cancel hn]
  rw [sum_heckeVonMangoldtCoefficient_from_two]
  simp [w, a, Complex.real_smul]

/-- The prime-power sum with the half contribution at an integral cutoff. -/
def heckePerronHalfSum (c : Place → ℂ) (s : ℂ) (x : ℝ) : ℂ :=
  ∑ j ∈ heckePrimePowerNormCutoff F (x + 1),
    (if (normOf j : ℝ) < x then 1 else if (normOf j : ℝ) = x then 1 / 2 else 0) *
    heckePrimePowerTerm F c s j

/-- The full paper cutoff includes all prime powers of norm at most `x`. -/
def heckePerronFullSum (c : Place → ℂ) (s : ℂ) (x : ℝ) : ℂ :=
  ∑ j ∈ (heckePrimePowerNormCutoff F (x + 1)).filter (fun j ↦ (normOf j : ℝ) ≤ x),
    heckePrimePowerTerm F c s j

/-- Ideal norms are integers, so rounding the full cutoff down preserves
the prime-power sum. -/
theorem heckePerronFullSum_floor (c : Place → ℂ) (s : ℂ) {x : ℝ} (hx : 0 ≤ x) :
    heckePerronFullSum F c s x = heckePerronFullSum F c s (⌊x⌋₊ : ℝ) := by
  unfold heckePerronFullSum
  apply Finset.sum_congr _ (fun _ _ ↦ rfl)
  ext j
  simp only [Finset.mem_filter, mem_heckePrimePowerNormCutoff]
  have hiff : (normOf j : ℝ) ≤ (⌊x⌋₊ : ℝ) ↔ (normOf j : ℝ) ≤ x :=
    Nat.cast_le.trans (Nat.le_floor_iff hx)
  rw [show ((heckePrimePowerIdeal F j).absNorm : ℝ) = (normOf j : ℝ) from rfl]
  exact ⟨fun hj ↦ ⟨(hiff.mpr hj.2).trans_lt (lt_add_one _), hiff.mpr hj.2⟩,
    fun hj ↦ ⟨(hiff.mp hj.2).trans_lt (lt_add_one _), hiff.mp hj.2⟩⟩

/-- Passing to the full cutoff adds half of the grouped coefficient exactly
when the cutoff is an integer. -/
theorem heckePerronFullSum_sub_halfSum (c : Place → ℂ) (s : ℂ) (x : ℝ) :
    heckePerronFullSum F c s x - heckePerronHalfSum F c s x =
      if (⌈x⌉₊ : ℝ) = x then (1 / 2 : ℂ) * LSeries.term (heckeVonMangoldtCoefficient F c) s ⌈x⌉₊
      else 0 := by
  have hdiff :
      heckePerronFullSum F c s x - heckePerronHalfSum F c s x =
        (1 / 2 : ℂ) * ∑ j ∈ (heckePrimePowerNormCutoff F (x + 1)).filter
          (fun j ↦ (normOf j : ℝ) = x), heckePrimePowerTerm F c s j := by
    rw [heckePerronFullSum, heckePerronHalfSum, Finset.sum_filter, ← Finset.sum_sub_distrib,
      Finset.mul_sum, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j _
    rcases lt_trichotomy (normOf j : ℝ) x with hlt | heq | hgt
    · simp [hlt, hlt.le, hlt.ne]
    · simp [heq]
      ring
    · simp [hgt.not_ge, hgt.not_gt, hgt.ne']
  rw [hdiff]
  split_ifs with hx
  · rw [term_heckeVonMangoldtCoefficient]
    apply congrArg ((1 / 2 : ℂ) * ·)
    refine Finset.sum_congr ?_ (fun _ _ ↦ rfl)
    ext j
    rw [Finset.mem_filter, mem_heckePrimePowerNormCutoff, mem_heckePrimePowerNormFiber]
    constructor
    · intro hj
      exact_mod_cast (hj.2.trans hx.symm)
    · intro hj
      have he : (normOf j : ℝ) = x := by exact (congrArg (fun n : ℕ ↦ (n : ℝ)) hj).trans hx
      exact ⟨he ▸ lt_add_one _, he⟩
  · have hempty : (heckePrimePowerNormCutoff F (x + 1)).filter
        (fun j ↦ (normOf j : ℝ) = x) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro j hj
      have he := (Finset.mem_filter.mp hj).2
      apply hx
      rw [← he, Nat.ceil_natCast]
    rw [hempty, Finset.sum_empty, mul_zero]

/-- The diagonal correction for the full cutoff is uniformly small on the
one-line, and vanishes at nonintegral cutoffs. -/
theorem norm_heckePerronFullSum_sub_halfSum_le (c : Place → ℂ) (hc : ∀ v, ‖c v‖ ≤ 1)
    {s : ℂ} (hs : s.re = 1) (x : ℝ) :
    ‖heckePerronFullSum F c s x - heckePerronHalfSum F c s x‖ ≤
      if (⌈x⌉₊ : ℝ) = x then (Module.finrank ℚ F : ℝ) * Real.log x / (2 * x) else 0 := by
  rw [heckePerronFullSum_sub_halfSum]
  split_ifs with hx
  · rw [norm_mul, show ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) by norm_num]
    calc
      _ ≤ (1 / 2 : ℝ) * ((Module.finrank ℚ F : ℝ) * Real.log (⌈x⌉₊ : ℝ) / ⌈x⌉₊) :=
        mul_le_mul_of_nonneg_left (norm_term_heckeVonMangoldtCoefficient_le F c hc hs _) (by norm_num)
      _ = _ := by rw [hx]; ring
  · simp

/-- Truncated Perron inversion on a vertical line of absolute convergence
for the logarithmic derivative of the actual Hecke Euler product. -/
theorem heckeEulerProduct_truncatedPerron (c : Place → ℂ) (hc : ∀ v, ‖c v‖ ≤ 1)
    (s : ℂ) {x κ T : ℝ} (hx : 0 < x) (hκ : 0 < κ) (hT : 0 < T)
    (hline : 1 < s.re + κ) :
    let z (y : ℝ) : ℂ := (κ : ℂ) + (y : ℂ) * Complex.I
    let E (n : ℕ) := ‖LSeries.term (heckeVonMangoldtCoefficient F c) s n‖ *
      perronError (Real.log x - Real.log (n : ℝ)) κ T
    Summable E ∧
      ‖((∫ y in -T..T,
        -logDeriv (fun w ↦ ∏' v, heckeEulerFactor F c v w) (s + z y) *
          (Complex.exp ((Real.log x : ℂ) * z y) / z y)) / (2 * (Real.pi : ℂ))) -
        heckePerronHalfSum F c s x‖ ≤ ∑' n, E n := by
  intro z E
  let a := heckeVonMangoldtCoefficient F c
  let w (n : ℕ) : ℂ := if (n : ℝ) < x then 1 else if (n : ℝ) = x then 1 / 2 else 0
  have hs : 1 < (s + (κ : ℂ)).re := by simpa [Complex.add_re] using hline
  have h := lseries_truncatedPerron a s hx hκ hT
    (summable_norm_term_heckeVonMangoldtCoefficient F c hc hs)
  have hgroup : (∑' n, LSeries.term a s n * w n) = heckePerronHalfSum F c s x := by
    rw [tsum_eq_sum (s := Finset.range ⌈x + 1⌉₊)]
    · simp_rw [mul_comm (LSeries.term a s _)]
      exact sum_term_heckeVonMangoldtCoefficient F c s (x + 1) w
    · intro n hn
      have hn' : x + 1 ≤ (n : ℝ) := le_of_not_gt fun hlt ↦
        hn (Finset.mem_range.mpr (Nat.lt_ceil.mpr hlt))
      have hgt : x < (n : ℝ) := by linarith
      simp [w, hgt.not_gt, hgt.ne']
  refine ⟨h.1, ?_⟩
  have hcontour :
      (∫ y in -T..T, LSeries a (s + z y) * (Complex.exp ((Real.log x : ℂ) * z y) / z y)) =
        (∫ y in -T..T, -logDeriv (fun w ↦ ∏' v, heckeEulerFactor F c v w) (s + z y) *
          (Complex.exp ((Real.log x : ℂ) * z y) / z y)) := by
    apply intervalIntegral.integral_congr
    intro y _
    exact congrArg (fun v : ℂ ↦ v * (Complex.exp ((Real.log x : ℂ) * z y) / z y))
      (lseries_heckeVonMangoldtCoefficient F c hc (by
        simpa [z, Complex.add_re, Complex.mul_re] using hline))
  have hb := h.2
  change ‖((∫ y in -T..T, LSeries a (s + z y) *
    (Complex.exp ((Real.log x : ℂ) * z y) / z y)) / (2 * (Real.pi : ℂ))) -
      (∑' n, LSeries.term a s n * w n)‖ ≤ ∑' n, E n at hb
  rwa [hcontour, hgroup] at hb

end

end Masullo
