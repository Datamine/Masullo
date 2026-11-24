import HeckePrimePowerLimits
import Mathlib.Algebra.BigOperators.Module

open Filter Function Set Topology NumberField Ideal IsDedekindDomain
open scoped Classical NumberField

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

local notation "Place" => HeightOneSpectrum (𝓞 F)

private def finiteNormCutoff {ι : Type*} (j : ι → Ideal (𝓞 F)) (hj : Injective j) (x : ℝ) : Finset ι :=
  (((Ideal.finite_setOfPred_absNorm_le (S := 𝓞 F) ⌈x⌉₊).preimage hj.injOn).subset
    (fun i hi ↦ show (j i).absNorm ≤ ⌈x⌉₊ from
      Nat.cast_le.mp ((le_of_lt (show ((j i).absNorm : ℝ) < x from hi)).trans (Nat.le_ceil x)))).toFinset

private theorem mem_finiteNormCutoff {ι : Type*} (j : ι → Ideal (𝓞 F)) (hj : Injective j)
    (x : ℝ) (i : ι) : i ∈ finiteNormCutoff F j hj x ↔ ((j i).absNorm : ℝ) < x :=
  Set.Finite.mem_toFinset _

private theorem tendsto_finiteNormCutoff {ι : Type*} (j : ι → Ideal (𝓞 F)) (hj : Injective j) :
    Tendsto (finiteNormCutoff F j hj) atTop atTop := by
  apply Monotone.tendsto_atTop_finset
  · intro x y hxy i hi
    exact (mem_finiteNormCutoff F j hj y i).mpr (((mem_finiteNormCutoff F j hj x i).mp hi).trans_le hxy)
  · intro i
    exact ⟨(j i).absNorm + 1, (mem_finiteNormCutoff F j hj _ i).mpr (lt_add_one _)⟩

/-- The logarithmic Euler coefficient of the power with exponent at least two.
The exponent of the pair `(v,k)` is `k+2`. -/
def heckeHigherPrimePowerLog (c : Place → ℂ) (s : ℂ) (j : Place × ℕ) : ℂ :=
  c j.1 ^ (j.2+2) / ((j.2+2 : ℕ) : ℂ) *
    ((heckePrimePowerIdeal F (j.1,j.2+1)).absNorm : ℂ) ^ (-s)

private def higherPrimePowerWeight (a : ℝ) (j : Place × ℕ) : ℝ :=
  (j.1.asIdeal.absNorm : ℝ) ^ (-2*a) * ((2 : ℝ) ^ (-a)) ^ j.2

set_option maxHeartbeats 650000 in
private theorem higherPrimePowerWeight_summable {a : ℝ} (ha : 1/2 < a) :
    Summable (higherPrimePowerWeight F a) := by
  have h₁ : 1 < 2*a := by linarith
  have hi : Injective (fun v : Place ↦ v.asIdeal) := fun _ _ h ↦ HeightOneSpectrum.ext h
  have hu : Summable (fun v : Place ↦ (v.asIdeal.absNorm : ℝ) ^ (-(2*a))) :=
    (summable_absNorm_rpow F h₁).comp_injective hi
  let r := (2 : ℝ) ^ (-a)
  have hr : 0 ≤ r := Real.rpow_nonneg (by norm_num) _
  have hr₁ : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hg : Summable (fun k : ℕ ↦ r ^ k) := summable_geometric_of_lt_one hr hr₁
  apply (summable_prod_of_nonneg (f := higherPrimePowerWeight F a)
    (fun _ ↦ by unfold higherPrimePowerWeight; positivity)).mpr
  refine ⟨fun v ↦ hg.mul_left ((v.asIdeal.absNorm : ℝ) ^ (-2*a)), ?_⟩
  exact (hu.mul_right (∑' k : ℕ, r ^ k)).congr fun v ↦ by
    change (v.asIdeal.absNorm : ℝ) ^ (-(2*a)) * (∑' k : ℕ, r ^ k) =
      ∑' k : ℕ, (v.asIdeal.absNorm : ℝ) ^ (-2*a) * r ^ k
    rw [tsum_mul_left, neg_mul]

private theorem norm_heckeHigherPrimePowerLog_le (c : Place → ℂ) (hc : ∀ v, ‖c v‖ ≤ 1)
    {a : ℝ} (ha : 1/2 < a) (s : ℂ) (hs : a ≤ s.re) (j : Place × ℕ) :
    ‖heckeHigherPrimePowerLog F c s j‖ ≤ higherPrimePowerWeight F a j := by
  rcases j with ⟨v, k⟩
  let p : ℝ := v.asIdeal.absNorm
  have hp : 2 ≤ p := by
    change (2 : ℝ) ≤ (v.asIdeal.absNorm : ℝ)
    exact_mod_cast (Nat.succ_le_of_lt (NumberField.HeightOneSpectrum.one_lt_absNorm v))
  have hp₀ : 0 < p := by linarith
  have hp₁ : 1 ≤ p := by linarith
  have hcp : 0 ≤ p ^ (k+2) := by positivity
  have hcoeff : ‖c v‖ ^ (k+2) / (k+2 : ℝ) ≤ 1 :=
    (div_le_one (by positivity)).mpr ((pow_le_one₀ (norm_nonneg _) (hc v)).trans (by
      have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg _
      linarith))
  unfold heckeHigherPrimePowerLog higherPrimePowerWeight
  rw [heckePrimePowerIdeal, map_pow, Nat.cast_pow, norm_mul, norm_div, norm_pow,
    Complex.norm_natCast, Nat.cast_add, Nat.cast_ofNat]
  change ‖c v‖ ^ (k+2) / (k+2 : ℝ) * ‖((p : ℂ) ^ (k+2)) ^ (-s)‖ ≤ _
  rw [← Complex.ofReal_pow, Complex.norm_cpow_eq_rpow_re_of_pos (pow_pos hp₀ _), Complex.neg_re]
  calc
    _ ≤ (p ^ (k+2)) ^ (-a) := (mul_le_of_le_one_left (Real.rpow_nonneg hcp _) hcoeff).trans
      (Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ hp₁) (neg_le_neg hs))
    _ = p ^ (-2*a) * (p ^ (-a)) ^ k := by
      rw [← Real.rpow_natCast_mul hp₀.le, ← Real.rpow_natCast,
        ← Real.rpow_mul hp₀.le, ← Real.rpow_add hp₀]
      congr 1
      push_cast
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (Real.rpow_nonneg hp₀.le _)
        (Real.rpow_le_rpow_of_nonpos (by norm_num) hp (by linarith)) _) (Real.rpow_nonneg hp₀.le _)

theorem summable_norm_heckeHigherPrimePowerLog
    (c : Place → ℂ) (hc : ∀ v, ‖c v‖ ≤ 1) {s : ℂ} (hs : 1/2 < s.re) :
    Summable fun j ↦ ‖heckeHigherPrimePowerLog F c s j‖ :=
  (higherPrimePowerWeight_summable F hs).of_nonneg_of_le (fun _ ↦ norm_nonneg _)
    (norm_heckeHigherPrimePowerLog_le F c hc hs s le_rfl)

private def higherPowerIdeal (j : Place × ℕ) : Ideal (𝓞 F) := heckePrimePowerIdeal F (j.1,j.2+1)

private theorem higherPowerIdeal_injective : Injective (higherPowerIdeal F) := by
  rintro ⟨v, k⟩ ⟨w, l⟩ h
  have e : (v, k+1) = (w, l+1) := heckePrimePowerIdeal_injective F h
  obtain ⟨rfl, hl⟩ := Prod.mk.inj e
  rw [Nat.succ.inj hl]

def heckeHigherPrimePowerCutoff (x : ℝ) : Finset (Place × ℕ) :=
  finiteNormCutoff F (higherPowerIdeal F) (higherPowerIdeal_injective F) x

/-- The higher prime powers converge uniformly on every closed half-plane
strictly to the right of one half, with the actual prime-power norm cutoff. -/
theorem heckeHigherPrimePowerLog_tendstoUniformlyOn
    (c : Place → ℂ) (hc : ∀ v, ‖c v‖ ≤ 1) {a : ℝ} (ha : 1/2 < a) :
    TendstoUniformlyOn
      (fun x s ↦ ∑ j ∈ heckeHigherPrimePowerCutoff F x, heckeHigherPrimePowerLog F c s j)
      (fun s ↦ ∑' j, heckeHigherPrimePowerLog F c s j) atTop {s | a ≤ s.re} := by
  have h := tendstoUniformlyOn_tsum (higherPrimePowerWeight_summable F ha)
    (fun j s (hs : a ≤ s.re) ↦ norm_heckeHigherPrimePowerLog_le F c hc ha s hs j)
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  exact (tendsto_finiteNormCutoff F _ (higherPowerIdeal_injective F)).eventually
    (Metric.tendstoUniformlyOn_iff.mp h ε hε)

omit [NumberField F] in
private theorem placeIdeal_injective : Injective (fun v : Place ↦ v.asIdeal) :=
  fun _ _ h ↦ HeightOneSpectrum.ext h

/-- The finite primes whose ideal norm is strictly below the real cutoff. -/
def heckePrimeNormCutoff (x : ℝ) : Finset Place :=
  finiteNormCutoff F (fun v : Place ↦ v.asIdeal) (placeIdeal_injective F) x

/-- The finite prime powers whose ideal norm is strictly below the real cutoff. -/
def heckePrimePowerNormCutoff (x : ℝ) : Finset (Place × ℕ) :=
  finiteNormCutoff F (heckePrimePowerIdeal F) (heckePrimePowerIdeal_injective F) x

theorem mem_heckePrimePowerNormCutoff {x : ℝ} {j : Place × ℕ} :
    j ∈ heckePrimePowerNormCutoff F x ↔ ((heckePrimePowerIdeal F j).absNorm : ℝ) < x :=
  mem_finiteNormCutoff F _ (heckePrimePowerIdeal_injective F) x j

theorem tendsto_heckePrimePowerNormCutoff :
    Tendsto (heckePrimePowerNormCutoff F) atTop atTop :=
  tendsto_finiteNormCutoff F _ (heckePrimePowerIdeal_injective F)

/-- The logarithmic Euler sum grouped by the norms of the prime powers. -/
def heckePrimePowerLogPartial (c : Place → ℂ) (x : ℝ) (s : ℂ) : ℂ :=
  ∑ j ∈ heckePrimePowerNormCutoff F x,
    c j.1 ^ (j.2+1) / ((j.2+1 : ℕ) : ℂ) * ((heckePrimePowerIdeal F j).absNorm : ℂ) ^ (-s)

/-- The first-power prime series truncated by prime norm. -/
def heckePrimeLogPartial (c : Place → ℂ) (x : ℝ) (s : ℂ) : ℂ :=
  ∑ v ∈ heckePrimeNormCutoff F x, c v * (v.asIdeal.absNorm : ℂ) ^ (-s)

private def firstPowerEmbedding : Place ↪ Place × ℕ :=
  ⟨fun v ↦ (v, 0), fun _ _ h ↦ congrArg Prod.fst h⟩

private def higherPowerEmbedding : (Place × ℕ) ↪ Place × ℕ :=
  ⟨fun j ↦ (j.1, j.2+1), by
    rintro ⟨v,k⟩ ⟨w,l⟩ h
    obtain ⟨rfl, hl⟩ := Prod.mk.inj h
    exact Prod.ext rfl (Nat.succ.inj hl)⟩

set_option maxHeartbeats 650000 in
/-- Exactly the first and higher terms in (B.7.2.16), including the same
strict real cutoff in both sums. -/
theorem heckePrimePowerLogPartial_split (c : Place → ℂ) (x : ℝ) (s : ℂ) :
    heckePrimePowerLogPartial F c x s = heckePrimeLogPartial F c x s +
      ∑ j ∈ heckeHigherPrimePowerCutoff F x, heckeHigherPrimePowerLog F c s j := by
  classical
  let A := (heckePrimeNormCutoff F x).map (firstPowerEmbedding F)
  let B := (heckeHigherPrimePowerCutoff F x).map (higherPowerEmbedding F)
  have hA (v : Place) : (v,0) ∈ heckePrimePowerNormCutoff F x ↔ v ∈ heckePrimeNormCutoff F x := by
    exact (mem_finiteNormCutoff F _ (heckePrimePowerIdeal_injective F) _ _).trans
      ((show (((v.asIdeal ^ (0+1 : ℕ)).absNorm : ℝ) < x) ↔ (v.asIdeal.absNorm : ℝ) < x by
        norm_num).trans (mem_finiteNormCutoff F _ (placeIdeal_injective F) _ _).symm)
  have hB (v : Place) (n : ℕ) :
      (v,n+1) ∈ heckePrimePowerNormCutoff F x ↔ (v,n) ∈ heckeHigherPrimePowerCutoff F x := by
    rw [heckePrimePowerNormCutoff, heckeHigherPrimePowerCutoff,
      mem_finiteNormCutoff, mem_finiteNormCutoff]
    rfl
  have he : heckePrimePowerNormCutoff F x = A ∪ B := by
    ext j
    constructor
    · rcases j with ⟨v, _ | n⟩
      · intro h
        exact Finset.mem_union_left B (Finset.mem_map.mpr ⟨v, (hA v).mp h, rfl⟩)
      · intro h
        exact Finset.mem_union_right A (Finset.mem_map.mpr ⟨(v,n), (hB v n).mp h, rfl⟩)
    · intro h
      rcases Finset.mem_union.mp h with h | h
      · obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp h
        exact (hA v).mpr hv
      · obtain ⟨⟨v,n⟩, hv, rfl⟩ := Finset.mem_map.mp h
        exact (hB v n).mpr hv
  have hd : Disjoint A B := by
    rw [Finset.disjoint_left]
    rintro _ ha hb
    obtain ⟨v, _, rfl⟩ := Finset.mem_map.mp ha
    obtain ⟨j, _, hj⟩ := Finset.mem_map.mp hb
    exact Nat.succ_ne_zero _ (congrArg Prod.snd hj)
  unfold heckePrimePowerLogPartial
  rw [he, Finset.sum_union hd, Finset.sum_map, Finset.sum_map]
  apply congrArg (· + ∑ j ∈ heckeHigherPrimePowerCutoff F x, heckeHigherPrimePowerLog F c s j)
  apply Finset.sum_congr rfl
  intro v _
  change c v ^ (0+1 : ℕ) / ((0+1 : ℕ) : ℂ) * ((v.asIdeal ^ (0+1 : ℕ)).absNorm : ℂ) ^ (-s) =
    c v * (v.asIdeal.absNorm : ℂ) ^ (-s)
  norm_num

/-- The entire higher-power correction can be subtracted from any
locally uniform limit of the grouped logarithmic Euler sums. -/
theorem heckePrimeLogPartial_tendstoLocallyUniformlyOn
    (c : Place → ℂ) (hc : ∀ v, ‖c v‖ ≤ 1) {D : Set ℂ}
    (hD : D ⊆ {s | 1 ≤ s.re}) {L : ℂ → ℂ}
    (hL : TendstoLocallyUniformlyOn (heckePrimePowerLogPartial F c) L atTop D) :
    TendstoLocallyUniformlyOn (heckePrimeLogPartial F c)
      (fun s ↦ L s - ∑' j, heckeHigherPrimePowerLog F c s j) atTop D := by
  have h := (heckeHigherPrimePowerLog_tendstoUniformlyOn F c hc
    (a := 1) (by norm_num)).mono hD
  have ht := hL.sub h.tendstoLocallyUniformlyOn
  refine ht.congr (fun x s _ ↦ ?_)
  change heckePrimePowerLogPartial F c x s -
      ∑ j ∈ heckeHigherPrimePowerCutoff F x, heckeHigherPrimePowerLog F c s j =
    heckePrimeLogPartial F c x s
  rw [heckePrimePowerLogPartial_split, add_sub_cancel_right]

/-- The powers of selected primes whose own norm lies beyond the cutoff. -/
def heckeHigherPrimePowerCrossover (c : Place → ℂ) (x : ℝ) (s : ℂ) : ℂ := by
  classical
  exact ∑' j : Place × ℕ,
    if j.1 ∈ heckePrimeNormCutoff F x ∧ j ∉ heckeHigherPrimePowerCutoff F x
    then heckeHigherPrimePowerLog F c s j else 0

/-- The discrepancy between cutting by prime norm and by prime-power
norm vanishes uniformly on closed half-planes to the right of one half. -/
theorem heckeHigherPrimePowerCrossover_tendstoUniformlyOn
    (c : Place → ℂ) (hc : ∀ v, ‖c v‖ ≤ 1) {a : ℝ} (ha : 1/2 < a) :
    TendstoUniformlyOn (heckeHigherPrimePowerCrossover F c) (fun _ ↦ 0)
      atTop {s | a ≤ s.re} := by
  classical
  let W := higherPrimePowerWeight F a
  have hW : Summable W := higherPrimePowerWeight_summable F ha
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  have htail : ∀ᶠ A : Finset (Place × ℕ) in atTop, (∑' j : {j // j ∉ A}, W j.val) < ε :=
    (tendsto_tsum_compl_atTop_zero W).eventually (Iio_mem_nhds hε)
  obtain ⟨A, hA⟩ := htail.exists
  have hcut : ∀ᶠ x : ℝ in atTop, A ⊆ heckeHigherPrimePowerCutoff F x :=
    (tendsto_finiteNormCutoff F _ (higherPowerIdeal_injective F)).eventually (eventually_ge_atTop A)
  filter_upwards [hcut] with x hx s hs
  let r : Place × ℕ → ℂ := fun j ↦
    if j.1 ∈ heckePrimeNormCutoff F x ∧ j ∉ heckeHigherPrimePowerCutoff F x
    then heckeHigherPrimePowerLog F c s j else 0
  have hb (j : Place × ℕ) : ‖r j‖ ≤ W j := by
    dsimp only [r]
    split
    · exact norm_heckeHigherPrimePowerLog_le F c hc ha s hs j
    · exact (norm_zero (E := ℂ)).le.trans (by unfold W higherPrimePowerWeight; positivity)
  have hsum : Summable fun j ↦ ‖r j‖ := hW.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hb
  have hz : ∑ j ∈ A, r j = 0 := Finset.sum_eq_zero (fun j hj ↦ by
    simp [r, hx hj])
  change dist 0 (∑' j, r j) < ε
  rw [dist_zero_left, ← hsum.of_norm.sum_add_tsum_compl (s := A), hz, zero_add]
  exact ((norm_tsum_le_tsum_norm (hsum.subtype _)).trans
    ((hsum.subtype _).tsum_le_tsum (fun j ↦ hb j.val) (hW.subtype _))).trans_lt hA

/-- A power-saving bound for the cutoff discrepancy on and to the
right of the one-line. One may take any exponent a strictly between one
half and one. -/
theorem norm_heckeHigherPrimePowerCrossover_le
    (c : Place → ℂ) (hc : ∀ v, ‖c v‖ ≤ 1) {a x : ℝ} (ha : 1/2 < a) (ha' : a < 1)
    (hx : 0 < x) {s : ℂ} (hs : 1 ≤ s.re) :
    ‖heckeHigherPrimePowerCrossover F c x s‖ ≤
      x ^ (a-1) * ∑' j, higherPrimePowerWeight F a j := by
  classical
  let W := higherPrimePowerWeight F a
  let f : Place × ℕ → ℂ := fun j ↦
    if j.1 ∈ heckePrimeNormCutoff F x ∧ j ∉ heckeHigherPrimePowerCutoff F x
      then heckeHigherPrimePowerLog F c s j else 0
  have hW : Summable W := higherPrimePowerWeight_summable F ha
  have hBound (j : Place × ℕ) : ‖f j‖ ≤ x ^ (a-1) * W j := by
    dsimp only [f]
    split
    · rename_i hj
      let q : ℝ := (higherPowerIdeal F j).absNorm
      have hq : x ≤ q := le_of_not_gt (fun h ↦ hj.2
        ((mem_finiteNormCutoff F _ (higherPowerIdeal_injective F) x j).mpr h))
      have hq₀ : 0 < q := hx.trans_le hq
      have hq₁ : 1 ≤ q := by
        have hqNat : 1 ≤ (higherPowerIdeal F j).absNorm := by
          unfold higherPowerIdeal heckePrimePowerIdeal
          rw [map_pow]
          exact Nat.one_le_pow _ _ (NumberField.HeightOneSpectrum.one_lt_absNorm j.1).le
        change (1 : ℝ) ≤ ((higherPowerIdeal F j).absNorm : ℝ)
        exact_mod_cast hqNat
      let b : ℝ := ‖c j.1‖ ^ (j.2+2) / (j.2+2 : ℝ)
      have hb : 0 ≤ b := by dsimp [b]; positivity
      have hval (z : ℂ) : ‖heckeHigherPrimePowerLog F c z j‖ = b * q ^ (-z.re) := by
        unfold heckeHigherPrimePowerLog
        rw [norm_mul, norm_div, norm_pow, Complex.norm_natCast, ← Complex.ofReal_natCast, Nat.cast_add, Nat.cast_ofNat]
        change b * ‖(q : ℂ) ^ (-z)‖ = b * q ^ (-z.re)
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hq₀, Complex.neg_re]
      calc
        _ = b * q ^ (-s.re) := hval s
        _ ≤ b * q ^ (-1 : ℝ) := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hq₁ (neg_le_neg hs)) hb
        _ = q ^ (a-1) * (b * q ^ (-a)) := by
          rw [mul_left_comm, ← Real.rpow_add hq₀]
          congr 2
          ring
        _ ≤ x ^ (a-1) * W j := by
          apply mul_le_mul (Real.rpow_le_rpow_of_nonpos hx hq (by linarith)) ?_
            (mul_nonneg hb (Real.rpow_nonneg hq₀.le _)) (Real.rpow_nonneg hx.le _)
          rw [← show ‖heckeHigherPrimePowerLog F c (a : ℂ) j‖ = b * q ^ (-a) from hval (a : ℂ)]
          exact norm_heckeHigherPrimePowerLog_le F c hc ha (a : ℂ) le_rfl j
    · rw [norm_zero]
      unfold W higherPrimePowerWeight
      positivity
  have hm := hW.mul_left (x ^ (a-1))
  have hf := hm.of_nonneg_of_le (fun j ↦ norm_nonneg (f j)) hBound
  change ‖∑' j, f j‖ ≤ x ^ (a-1) * ∑' j, W j
  rw [← tsum_mul_left]
  exact (norm_tsum_le_tsum_norm hf).trans (hf.tsum_le_tsum hBound hm)

theorem prime_mem_of_higherPower_mem {x : ℝ} {j : Place × ℕ}
    (h : j ∈ heckeHigherPrimePowerCutoff F x) : j.1 ∈ heckePrimeNormCutoff F x := by
  have he := (mem_finiteNormCutoff F _ (higherPowerIdeal_injective F) x j).mp h
  apply (mem_finiteNormCutoff F _ (placeIdeal_injective F) x j.1).mpr
  apply lt_of_le_of_lt _ he
  change (j.1.asIdeal.absNorm : ℝ) ≤ ((j.1.asIdeal ^ (j.2+1+1)).absNorm : ℝ)
  rw [map_pow]
  exact_mod_cast Nat.le_self_pow (Nat.succ_ne_zero _) j.1.asIdeal.absNorm

/-- The grouped tail contains the prime-base tail and the extra powers of
primes already selected. Since the manuscript defines H as minus the
extra powers, converting the grouped tail to the prime-base tail adds H. -/
theorem heckeHigherPrimePowerTail_split (c : Place → ℂ) (hc : ∀ v, ‖c v‖ ≤ 1)
    (x : ℝ) {s : ℂ} (hs : 1/2 < s.re) :
    ∑' j : Place × ℕ, (if j ∉ heckeHigherPrimePowerCutoff F x then heckeHigherPrimePowerLog F c s j else 0) =
      (∑' j : Place × ℕ, if j.1 ∉ heckePrimeNormCutoff F x then heckeHigherPrimePowerLog F c s j else 0) +
      heckeHigherPrimePowerCrossover F c x s := by
  classical
  let u := heckeHigherPrimePowerLog F c s
  let a (j : Place × ℕ) := if j.1 ∉ heckePrimeNormCutoff F x then u j else 0
  let b (j : Place × ℕ) :=
    if j.1 ∈ heckePrimeNormCutoff F x ∧ j ∉ heckeHigherPrimePowerCutoff F x then u j else 0
  let d (j : Place × ℕ) := if j ∉ heckeHigherPrimePowerCutoff F x then u j else 0
  have h (p : (Place × ℕ) → Prop) [DecidablePred p] :
      Summable (fun j ↦ if p j then u j else 0) :=
    (summable_norm_heckeHigherPrimePowerLog F c hc hs).of_norm_bounded (fun j ↦ by
      split
      · exact le_rfl
      · exact (norm_zero (E := ℂ)).le.trans (norm_nonneg _))
  change ∑' j, d j = (∑' j, a j) + ∑' j, b j
  rw [← (h _).tsum_add (h _)]
  apply tsum_congr
  intro j
  by_cases ha : j.1 ∈ heckePrimeNormCutoff F x
  · simp [d, ha]
  · have hb : j ∉ heckeHigherPrimePowerCutoff F x := fun k ↦ ha (prime_mem_of_higherPower_mem F k)
    simp [d, ha, hb]

/-- The finite reciprocal Euler product with the same prime norm cutoff
as the grouped logarithmic sums. -/
def heckeReciprocalPartial (c : Place → ℂ) (x : ℝ) (s : ℂ) : ℂ :=
  ∏ v ∈ heckePrimeNormCutoff F x, (heckeEulerFactor F c v s)⁻¹

/-- The limit transfer in B.7.2.5. A locally uniform normalized
reciprocal-product limit yields the direct product limit on the
nonvanishing locus of the continuation. -/
theorem heckeEulerPartial_tendstoLocallyUniformlyOn
    (c : Place → ℂ) {D : Set ℂ} {L : ℂ → ℂ}
    (hL : ContinuousOn L D) (hL₀ : ∀ s ∈ D, L s ≠ 0)
    (h : TendstoLocallyUniformlyOn (fun x s ↦ heckeReciprocalPartial F c x s * L s)
      (fun _ ↦ 1) atTop D) :
    TendstoLocallyUniformlyOn (fun x s ↦ ∏ v ∈ heckePrimeNormCutoff F x, heckeEulerFactor F c v s)
      L atTop D := by
  have hInv := h.inv₀ continuousOn_const (fun _ _ ↦ one_ne_zero)
  have hConst : TendstoLocallyUniformlyOn (fun _ : ℝ ↦ L) L atTop D :=
    (Metric.tendstoUniformlyOn_iff.mpr fun ε hε ↦
      Eventually.of_forall fun _ s _ ↦ (dist_self (L s)).symm ▸ hε).tendstoLocallyUniformlyOn
  have ht := hConst.mul₀ hInv hL continuousOn_const
  refine (ht.congr_right (fun s _ ↦ by simp)).congr (fun x s hs ↦ ?_)
  change L s * (heckeReciprocalPartial F c x s * L s)⁻¹ = _
  rw [mul_inv, ← mul_assoc]
  unfold heckeReciprocalPartial
  rw [mul_comm _ (∏ _ ∈ _, _)⁻¹, mul_assoc, mul_inv_cancel₀ (hL₀ s hs), mul_one, Finset.prod_inv_distrib]
  simp only [inv_inv]

/-- Abel summation gives precisely twice the starting weight times the
partial-sum error bound. This applies to the remainder after subtracting
the pole model, with the manuscript's reciprocal logarithm as weight. -/
theorem norm_abelWeightedTail_le (w : ℕ → ℝ) (a : ℕ → ℂ) (hw : Antitone w)
    (h₀ : ∀ j, 0 ≤ w j) {m n : ℕ} (hmn : m < n) {ε : ℝ}
    (hε : ∀ j ≥ m, ‖∑ i ∈ Finset.range j, a i‖ ≤ ε) :
    ‖∑ j ∈ Finset.Ico m n, w j • a j‖ ≤ 2 * ε * w m := by
  let A (j : ℕ) := ∑ i ∈ Finset.range j, a i
  have ht : ∑ j ∈ Finset.Ico m (n-1), (w j - w (j+1)) = w m - w (n-1) := by
    have hmn' : m ≤ n-1 := Nat.le_sub_one_of_lt hmn
    calc
      _ = -∑ j ∈ Finset.Ico m (n-1), (w (j+1) - w j) := by simp [neg_sub]
      _ = _ := by rw [Finset.sum_Ico_sub w hmn', neg_sub]
  have hsum :
      ‖∑ j ∈ Finset.Ico m (n-1), (w (j+1) - w j) • A (j+1)‖ ≤
        (w m - w (n-1)) * ε := by
    apply (norm_sum_le _ _).trans
    rw [← ht, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro j hj
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr (hw (Nat.le_succ _))), neg_sub]
    exact mul_le_mul_of_nonneg_left (hε _ ((Finset.mem_Ico.mp hj).1.trans (Nat.le_succ _)))
      (sub_nonneg.mpr (hw (Nat.le_succ _)))
  rw [Finset.sum_Ico_by_parts w a hmn]
  change ‖w (n-1) • A n - w m • A m -
      ∑ j ∈ Finset.Ico m (n-1), (w (j+1) - w j) • A (j+1)‖ ≤ _
  have h₁ : ‖w (n-1) • A n‖ ≤ w (n-1) * ε := by
    rw [norm_smul, Real.norm_of_nonneg (h₀ _)]
    exact mul_le_mul_of_nonneg_left (hε n hmn.le) (h₀ _)
  have h₂ : ‖w m • A m‖ ≤ w m * ε := by
    rw [norm_smul, Real.norm_of_nonneg (h₀ _)]
    exact mul_le_mul_of_nonneg_left (hε m le_rfl) (h₀ _)
  apply (norm_sub_le _ _).trans
  apply (add_le_add ((norm_sub_le _ _).trans (add_le_add h₁ h₂)) hsum).trans
  ring_nf
  exact le_rfl

/-- Uniformly bounded partial sums yield uniform convergence after Abel
weighting. Any uniform bound on the partial sums beyond a given starting
index yields the corresponding sharp bound on the infinite tail. -/
theorem abelWeightedSums_uniform_eventually {Z : Type*} (D : Set Z)
    (w : ℕ → ℝ) (a : ℕ → Z → ℂ) (hw : Antitone w) (h₀ : ∀ j, 0 ≤ w j)
    (hlim : Tendsto w atTop (𝓝 0)) (C : ℝ) (N₀ : ℕ) (hC : ∀ n ≥ N₀, ∀ z ∈ D,
      ‖∑ j ∈ Finset.range n, a j z‖ ≤ C) :
    ∃ L : Z → ℂ,
      TendstoUniformlyOn (fun n z ↦ ∑ j ∈ Finset.range n, w j • a j z) L atTop D ∧
      ∀ (m : ℕ) (ε : ℝ),
        (∀ n ≥ m, ∀ z ∈ D, ‖∑ j ∈ Finset.range n, a j z‖ ≤ ε) →
        ∀ z ∈ D, ‖L z - ∑ j ∈ Finset.range m, w j • a j z‖ ≤ 2 * ε * w m := by
  classical
  let S (n : ℕ) (z : Z) := ∑ j ∈ Finset.range n, w j • a j z
  have htail (m n : ℕ) (hmn : m < n) (ε : ℝ) (hε : ∀ l ≥ m, ∀ z ∈ D,
      ‖∑ i ∈ Finset.range l, a i z‖ ≤ ε) (z : Z) (hz : z ∈ D) :
      ‖S n z - S m z‖ ≤ 2 * ε * w m := by
    rw [show S n z - S m z = ∑ j ∈ Finset.Ico m n, w j • a j z from
      (Finset.sum_Ico_eq_sub (fun j ↦ w j • a j z) hmn.le).symm]
    exact norm_abelWeightedTail_le w (fun j ↦ a j z) hw h₀ hmn (fun l hl ↦ hε l hl z hz)
  have hW : Tendsto (fun n ↦ 2 * C * w n) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := 2*C)).mul hlim
  have hS : UniformCauchySeqOn S atTop D := Metric.uniformCauchySeqOn_iff.mpr fun ε hε ↦ by
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hW.eventually (Iio_mem_nhds hε))
    refine ⟨max N N₀, fun m hm n hn z hz ↦ ?_⟩
    rcases lt_trichotomy m n with h | rfl | h
    · rw [dist_comm, dist_eq_norm]
      exact (htail m n h C (fun j hj z hz ↦
        hC j (le_max_right N N₀ |>.trans (hm.trans hj)) z hz) z hz).trans_lt
        (hN m ((le_max_left N N₀).trans hm))
    · rwa [dist_self]
    · rw [dist_eq_norm]
      exact (htail n m h C (fun j hj z hz ↦
        hC j (le_max_right N N₀ |>.trans (hn.trans hj)) z hz) z hz).trans_lt
        (hN n ((le_max_left N N₀).trans hn))
  have hex (z : Z) (hz : z ∈ D) : ∃ l, Tendsto (fun n ↦ S n z) atTop (𝓝 l) :=
    cauchySeq_tendsto_of_complete (hS.cauchySeq hz)
  let L (z : Z) : ℂ := if hz : z ∈ D then (hex z hz).choose else 0
  have hL : TendstoUniformlyOn S L atTop D := hS.tendstoUniformlyOn_of_tendsto fun z hz ↦ by
    simpa only [L, dite_eq_left hz] using (hex z hz).choose_spec
  refine ⟨L, hL, fun m ε hε z hz ↦ ?_⟩
  have ht : Tendsto (fun n ↦ ‖S n z - S m z‖) atTop (𝓝 ‖L z - S m z‖) :=
    (hL.tendsto_at hz).sub_const (S m z) |>.norm
  exact le_of_tendsto ht ((eventually_gt_atTop m).mono fun n hn ↦ htail m n hn ε hε z hz)

theorem abelWeightedSums_uniform {Z : Type*} (D : Set Z)
    (w : ℕ → ℝ) (a : ℕ → Z → ℂ) (hw : Antitone w) (h₀ : ∀ j, 0 ≤ w j)
    (hlim : Tendsto w atTop (𝓝 0)) (C : ℝ) (hC : ∀ n z, z ∈ D →
      ‖∑ j ∈ Finset.range n, a j z‖ ≤ C) :
    ∃ L : Z → ℂ,
      TendstoUniformlyOn (fun n z ↦ ∑ j ∈ Finset.range n, w j • a j z) L atTop D ∧
      ∀ (m : ℕ) (ε : ℝ),
        (∀ n ≥ m, ∀ z ∈ D, ‖∑ j ∈ Finset.range n, a j z‖ ≤ ε) →
        ∀ z ∈ D, ‖L z - ∑ j ∈ Finset.range m, w j • a j z‖ ≤ 2 * ε * w m :=
  abelWeightedSums_uniform_eventually D w a hw h₀ hlim C 0 (fun n _ ↦ hC n)

/-- Dividing each von Mangoldt term by the logarithm of its prime-power
norm gives the logarithmic Euler term with the reciprocal exponent. -/
theorem heckePrimePowerLog_from_logDerivative (c : Place → ℂ) (s : ℂ) (j : Place × ℕ) :
    ((Real.log ((heckePrimePowerIdeal F j).absNorm : ℝ))⁻¹ : ℂ) *
        heckePrimePowerTerm F c s j =
      c j.1 ^ (j.2+1) / ((j.2+1 : ℕ) : ℂ) * ((heckePrimePowerIdeal F j).absNorm : ℂ) ^ (-s) := by
  let p : ℝ := j.1.asIdeal.absNorm
  have hp : 1 < p := by
    change (1 : ℝ) < (j.1.asIdeal.absNorm : ℝ)
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm j.1
  have hl : (Real.log p : ℂ) ≠ 0 := by exact_mod_cast (Real.log_pos hp).ne'
  have hn : ((j.2+1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j.2
  have hlog : Real.log ((heckePrimePowerIdeal F j).absNorm : ℝ) =
      ((j.2+1 : ℕ) : ℝ) * Real.log p := by
    rw [heckePrimePowerIdeal, map_pow, Nat.cast_pow, Real.log_pow]
  rw [heckePrimePowerTerm, hlog, Complex.ofReal_mul, Complex.ofReal_natCast]
  change (((j.2+1 : ℕ) : ℂ) * (Real.log p : ℂ))⁻¹ *
      (c j.1 ^ (j.2+1) * (Real.log p : ℂ) * _) = _
  rw [mul_inv_rev]
  field_simp

/-- The reciprocal logarithm on norms starting at two has the positivity,
monotonicity and decay required in the Abel estimate. -/
theorem abelReciprocalLogWeight :
    let w (n : ℕ) := (Real.log (((n+2 : ℕ) : ℝ)))⁻¹
    Antitone w ∧ (∀ n, 0 ≤ w n) ∧ Tendsto w atTop (𝓝 0) := by
  let w (n : ℕ) := (Real.log (((n+2 : ℕ) : ℝ)))⁻¹
  have hp (n : ℕ) : 0 < Real.log (((n+2 : ℕ) : ℝ)) := Real.log_pos (by
    exact_mod_cast (show 1 < n+2 by omega))
  change Antitone w ∧ (∀ n, 0 ≤ w n) ∧ Tendsto w atTop (𝓝 0)
  refine ⟨?_, fun n ↦ inv_nonneg.mpr (hp n).le, ?_⟩
  · intro m n h
    apply (inv_le_inv₀ (hp n) (hp m)).mpr
    apply Real.log_le_log (by positivity)
    exact_mod_cast (Nat.add_le_add_right h 2)
  · exact tendsto_inv_atTop_zero.comp (Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2)))

end

end Masullo
