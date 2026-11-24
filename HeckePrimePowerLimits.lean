import HeckeEulerProducts
import RealPlaceRepair
import Mathlib.Analysis.Calculus.LogDerivUniformlyOn

open Filter Function Set Topology NumberField Ideal IsDedekindDomain
open scoped NumberField

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

local notation "Place" => HeightOneSpectrum (𝓞 F)

/-- Prime powers, with exponent indexed by its predecessor. -/
def heckePrimePowerIdeal (j : Place × ℕ) : Ideal (𝓞 F) := j.1.asIdeal ^ (j.2+1)

theorem heckePrimePowerIdeal_injective : Injective (heckePrimePowerIdeal F) := by
  rintro ⟨v, n⟩ ⟨w, k⟩ he
  change v.asIdeal ^ (n+1) = w.asIdeal ^ (k+1) at he
  have hd : v.asIdeal ∣ w.asIdeal := v.prime.dvd_of_dvd_pow
    (he ▸ dvd_pow_self _ (Nat.succ_ne_zero n))
  have hvw : v = w := HeightOneSpectrum.ext
    (w.isMaximal.eq_of_le v.isPrime.ne_top (Ideal.dvd_iff_le.mp hd)).symm
  subst w
  have hN := congrArg (Ideal.absNorm : Ideal (𝓞 F) → ℕ) he
  simp only [map_pow] at hN
  have hn := Nat.pow_right_injective (NumberField.HeightOneSpectrum.one_lt_absNorm v) hN
  exact Prod.ext rfl (Nat.succ.inj hn)

/-- The positive prime-power coefficient of the negative logarithmic derivative. -/
def heckePrimePowerTerm (c : Place → ℂ) (s : ℂ) (j : Place × ℕ) : ℂ :=
  c j.1 ^ (j.2+1) * (Real.log (j.1.asIdeal.absNorm : ℝ) : ℂ) *
    ((heckePrimePowerIdeal F j).absNorm : ℂ) ^ (-s)

private theorem norm_one_lt_primePower (j : Place × ℕ) :
    1 < (heckePrimePowerIdeal F j).absNorm := by
  rw [heckePrimePowerIdeal, map_pow]
  exact Nat.one_lt_pow (Nat.succ_ne_zero _) (NumberField.HeightOneSpectrum.one_lt_absNorm j.1)

-- The ideal-power injection applies the same norm majorant as original
-- RiemannMasullo/AppB_AnalyticNT/Sec4b.lean at 66e4c88d0670cb468987d376ec90fce0351a4213.
theorem heckePrimePowerTerm_majorant (c : Place → ℂ) (hc : ∀ v, ‖c v‖ ≤ 1)
    {a : ℝ} (ha : 1 < a) :
    ∃ M : Place × ℕ → ℝ, Summable M ∧
      ∀ j s, a ≤ Complex.re s → ‖heckePrimePowerTerm F c s j‖ ≤ M j := by
  let r := (1 + a) / 2
  let ε := a - r
  have hr : 1 < r := by dsimp [r]; linarith
  have hε : 0 < ε := by dsimp [ε, r]; linarith
  have hsum := (summable_absNorm_rpow F hr).comp_injective (heckePrimePowerIdeal_injective F)
  refine ⟨_, hsum.mul_left ε⁻¹, ?_⟩
  rintro ⟨v, k⟩ s hs
  let p : ℝ := v.asIdeal.absNorm
  let q : ℝ := (heckePrimePowerIdeal F (v,k)).absNorm
  have hp : 1 < p := by dsimp only [p]; exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hq : 1 < q := by dsimp only [q]; exact_mod_cast norm_one_lt_primePower F (v,k)
  have hpq : p ≤ q := by
    dsimp [p, q, heckePrimePowerIdeal]
    rw [map_pow, Nat.cast_pow, pow_succ']
    exact le_mul_of_one_le_right (zero_le_one.trans hp.le) (one_le_pow₀ hp.le)
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hq0 : 0 < q := zero_lt_one.trans hq
  have hcPow : ‖c v‖ ^ (k+1) ≤ 1 :=
    pow_le_one₀ (norm_nonneg _) (hc _)
  have hlog : Real.log p ≤ q ^ ε / ε :=
    (Real.log_le_log hp0 hpq).trans (Real.log_le_rpow_div hq0.le hε)
  change ‖c v ^ (k+1) * (Real.log p : ℂ) * (q : ℂ) ^ (-s)‖ ≤ ε⁻¹ * q ^ (-r)
  rw [norm_mul, norm_mul, norm_pow, Complex.norm_real,
    Real.norm_of_nonneg (Real.log_nonneg hp.le),
    Complex.norm_cpow_eq_rpow_re_of_pos hq0, Complex.neg_re]
  calc
    _ ≤ (q ^ ε / ε) * q ^ (-a) :=
      mul_le_mul ((mul_le_of_le_one_left (Real.log_nonneg hp.le) hcPow).trans hlog)
        (Real.rpow_le_rpow_of_exponent_le hq.le (neg_le_neg hs))
        (Real.rpow_nonneg hq0.le _) (by positivity)
    _ = ε⁻¹ * q ^ (-r) := by
      rw [div_eq_mul_inv, mul_comm (q ^ ε), mul_assoc, ← Real.rpow_add hq0]
      congr 2
      dsimp [ε]
      ring

/-- Absolute convergence throughout the Euler product half-plane. -/
theorem summable_norm_heckePrimePowerTerm (c : Place → ℂ) (hc : ∀ v, ‖c v‖ ≤ 1)
    {s : ℂ} (hs : 1 < s.re) :
    Summable fun j ↦ ‖heckePrimePowerTerm F c s j‖ := by
  obtain ⟨M, hM, hbound⟩ := heckePrimePowerTerm_majorant F c hc hs
  exact hM.of_nonneg_of_le (fun _ ↦ norm_nonneg _) fun j ↦ hbound j s le_rfl

private theorem norm_heckePrimeRatio_lt_one (c : Place → ℂ) (hc : ∀ v, ‖c v‖ ≤ 1)
    (v : Place) {s : ℂ} (hs : 1 < s.re) :
    ‖c v * (v.asIdeal.absNorm : ℂ) ^ (-s)‖ < 1 := by
  have hq : (1 : ℝ) < v.asIdeal.absNorm := by
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hq0 := zero_lt_one.trans hq
  rw [norm_mul, ← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hq0, Complex.neg_re]
  exact (mul_le_of_le_one_left (Real.rpow_nonneg hq0.le _) (hc v)).trans_lt
    (Real.rpow_lt_one_of_one_lt_of_neg hq (by linarith))

private theorem hasDerivAt_heckeEulerDenominator (c : Place → ℂ) (v : Place) (s : ℂ) :
    HasDerivAt (fun z : ℂ ↦ 1 - c v * (v.asIdeal.absNorm : ℂ) ^ (-z))
      ((Real.log (v.asIdeal.absNorm : ℝ) : ℂ) * (c v * (v.asIdeal.absNorm : ℂ) ^ (-s))) s := by
  have hq : (0 : ℝ) < v.asIdeal.absNorm := by
    exact_mod_cast (zero_lt_one.trans (NumberField.HeightOneSpectrum.one_lt_absNorm v))
  have hq' : (v.asIdeal.absNorm : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  let q : ℂ := v.asIdeal.absNorm
  have he : (Real.log (v.asIdeal.absNorm : ℝ) : ℂ) = Complex.log q := by
    rw [Complex.ofReal_log hq.le, Complex.ofReal_natCast]
  have h : HasDerivAt (fun z : ℂ ↦ 1 - c v * q ^ (-z))
      (0 - c v * (q ^ (-s) * Complex.log q * (-1))) s :=
    (hasDerivAt_const s (1 : ℂ)).sub
      (((hasDerivAt_id s).neg.const_cpow (Or.inl hq')).const_mul (c v))
  rw [← he] at h
  have hval : (0 : ℂ) - c v * (q ^ (-s) *
      (Real.log (v.asIdeal.absNorm : ℝ) : ℂ) * (-1)) =
      (Real.log (v.asIdeal.absNorm : ℝ) : ℂ) * (c v * q ^ (-s)) := by ring
  rwa [hval] at h

/-- The negative logarithmic derivative of a local factor is its geometric
series over positive prime powers. -/
theorem neg_logDeriv_heckeEulerFactor (c : Place → ℂ) (hc : ∀ v, ‖c v‖ ≤ 1)
    (v : Place) {s : ℂ} (hs : 1 < s.re) :
    -logDeriv (heckeEulerFactor F c v) s = ∑' k : ℕ, heckePrimePowerTerm F c s (v,k) := by
  let q : ℂ := v.asIdeal.absNorm
  let z := c v * q ^ (-s)
  let L : ℂ := (Real.log (v.asIdeal.absNorm : ℝ) : ℂ)
  have hnorm : ‖z‖ < 1 := norm_heckePrimeRatio_lt_one F c hc v hs
  have hz : 1 - z ≠ 0 := by
    intro he
    have h₁ : z = 1 := (sub_eq_zero.mp he).symm
    rw [h₁, norm_one] at hnorm
    exact (lt_irrefl (1 : ℝ)) hnorm
  have hInv := (hasDerivAt_heckeEulerDenominator F c v s).inv hz
  have hterm (k : ℕ) : heckePrimePowerTerm F c s (v,k) = (L * z) * z ^ k := by
    change c v ^ (k+1) * L * ((v.asIdeal ^ (k+1)).absNorm : ℂ) ^ (-s) = _
    rw [map_pow, Nat.cast_pow, ← Complex.natCast_cpow_natCast_mul,
      Complex.cpow_nat_mul, show (v.asIdeal.absNorm : ℂ) = q from rfl]
    rw [mul_comm _ L, mul_assoc, ← mul_pow, ← show c v * q ^ (-s) = z from rfl, pow_succ']
    ring
  have hl : -logDeriv (heckeEulerFactor F c v) s = L * z / (1-z) := by
    rw [logDeriv_apply, show deriv (heckeEulerFactor F c v) s =
      -(L*z)/(1-z)^2 from hInv.deriv]
    change -(-(L*z)/(1-z)^2 / (1-z)⁻¹) = _
    field_simp
  rw [hl, tsum_congr hterm, tsum_mul_left, tsum_geometric_of_norm_lt_one hnorm]
  rw [div_eq_mul_inv]

/-- To the right of one, differentiating the actual finite Euler product
gives the absolutely convergent sum indexed by prime powers. -/
theorem neg_logDeriv_heckeEulerProduct (c : Place → ℂ) (hc : ∀ v, ‖c v‖ ≤ 1)
    {s : ℂ} (hs : 1 < s.re) :
    -logDeriv (fun z ↦ ∏' v, heckeEulerFactor F c v z) s =
      ∑' j, heckePrimePowerTerm F c s j := by
  let H : Set ℂ := {z | 1 < z.re}
  have hH : IsOpen H := isOpen_lt continuous_const Complex.continuous_re
  have hd (v : Place) (z : ℂ) (hz : z ∈ H) :
      1 - c v * (v.asIdeal.absNorm : ℂ) ^ (-z) ≠ 0 := by
    intro h
    have he := (sub_eq_zero.mp h).symm
    have hh := norm_heckePrimeRatio_lt_one F c hc v hz
    rw [he, norm_one] at hh
    exact (lt_irrefl (1 : ℝ)) hh
  have hU : MultipliableLocallyUniformlyOn (heckeEulerFactor F c) H :=
    (hasProdLocallyUniformlyOn_of_forall_compact hH (fun K hKH hK ↦
      heckeEulerProduct_hasProdUniformlyOn F c hc K hK (fun z hz ↦ hKH hz))).multipliableLocallyUniformlyOn
  have hsum := (summable_norm_heckePrimePowerTerm F c hc hs).of_norm
  have hlog : Summable (fun v ↦ -logDeriv (heckeEulerFactor F c v) s) := by
    apply hsum.prod.congr
    intro v
    exact (neg_logDeriv_heckeEulerFactor F c hc v hs).symm
  rw [logDeriv_tprod_eq_tsum (f := heckeEulerFactor F c) hH (show s ∈ H from hs)
      (fun v ↦ inv_ne_zero (hd v s hs))
      (fun v z hz ↦ ((hasDerivAt_heckeEulerDenominator F c v z).inv
        (hd v z hz)).differentiableAt.differentiableWithinAt)
      (by simpa only [neg_neg] using hlog.neg) hU (heckeEulerProduct_ne_zero F c hc hs),
    ← tsum_neg, hsum.tsum_prod]
  exact tsum_congr (fun v ↦ neg_logDeriv_heckeEulerFactor F c hc v hs)

/-- The common smooth cutoff evaluated at the logarithmic prime-power norm. -/
def heckePrimePowerCutoff (j : Place × ℕ) (n : ℕ) : ℝ :=
  realPlaceCutoff n (Real.log ((heckePrimePowerIdeal F j).absNorm : ℝ))

/-- Each concrete cutoff selects only finitely many prime-power ideals. -/
theorem heckePrimePowerCutoff_finite_support (n : ℕ) :
    (Function.support (fun j ↦ heckePrimePowerCutoff F j n)).Finite := by
  let N := ⌈Real.exp ((n : ℝ) + 1)⌉₊
  let A : Set (Ideal (𝓞 F)) := ⋃ k ∈ (Finset.range (N+1) : Set ℕ), {I | I.absNorm = k}
  have hA : A.Finite :=
    (Finset.range (N+1)).finite_toSet.biUnion (fun k _ ↦
      Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 F) k)
  refine (hA.preimage (heckePrimePowerIdeal_injective F).injOn).subset fun j hj ↦ ?_
  let q := (heckePrimePowerIdeal F j).absNorm
  have hx := realPlaceCutoff_support n (subset_tsupport _ hj)
  have hq : (q : ℝ) ≤ Real.exp ((n : ℝ) + 1) :=
    Real.le_exp_of_log_le hx.2
  have hqN : q ≤ N := by
    dsimp only [N]
    exact_mod_cast hq.trans (Nat.le_ceil (Real.exp ((n : ℝ) + 1)))
  exact mem_iUnion.mpr ⟨q, mem_iUnion.mpr
    ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hqN), rfl⟩⟩

private theorem primePowerCutoff_eventually_one (j : Place × ℕ) :
    ∀ᶠ n in atTop, heckePrimePowerCutoff F j n = 1 :=
  realPlaceCutoff_eventually_one (Real.log_pos (by exact_mod_cast norm_one_lt_primePower F j))

/-- The concrete log-norm cutoff in the reference-subtracted finite-place
sum converges uniformly on each closed half-plane strictly to the right of one. -/
theorem heckePrimePowerCutoff_tendstoUniformlyOn (c : Place → ℂ) (hc : ∀ v, ‖c v‖ ≤ 1)
    {a : ℝ} (ha : 1 < a) {b : ℂ} (hb : 1 < b.re) :
    TendstoUniformlyOn
      (fun n s ↦ ∑' j, (heckePrimePowerCutoff F j n : ℂ) *
        (heckePrimePowerTerm F c s j - heckePrimePowerTerm F c b j))
      (fun s ↦ (-logDeriv (fun z ↦ ∏' v, heckeEulerFactor F c v z) s) -
        (-logDeriv (fun z ↦ ∏' v, heckeEulerFactor F c v z) b)) atTop {s | a ≤ s.re} := by
  let D (s : ℂ) (j : Place × ℕ) := heckePrimePowerTerm F c s j - heckePrimePowerTerm F c b j
  obtain ⟨M, hM, hbound⟩ := heckePrimePowerTerm_majorant F c hc (lt_min ha hb)
  have hD (s : ℂ) (hs : a ≤ s.re) (j : Place × ℕ) : ‖D s j‖ ≤ M j + M j :=
    (norm_sub_le _ _).trans (add_le_add (hbound j s ((min_le_left _ _).trans hs))
      (hbound j b (min_le_right _ _)))
  let W (j : Place × ℕ) := M j + M j
  have hW : Summable W := hM.add hM
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  obtain ⟨A, hA⟩ := ((tendsto_tsum_compl_atTop_zero W).eventually (Iio_mem_nhds hε)).exists
  have hA' : ∑' j : {j // j ∉ A}, W j.val < ε := hA
  filter_upwards [(eventually_all_finset A).mpr (fun j _ ↦ primePowerCutoff_eventually_one F j)]
    with n hn s hs
  let C (j : Place × ℕ) := (heckePrimePowerCutoff F j n : ℂ) * D s j
  let E (j : Place × ℕ) := (1 - (heckePrimePowerCutoff F j n : ℂ)) * D s j
  have hcN (j : Place × ℕ) : heckePrimePowerCutoff F j n ∈ Icc (0 : ℝ) 1 :=
    realPlaceCutoff_mem_Icc _ _
  have hC (j : Place × ℕ) : ‖C j‖ ≤ W j := by
    change ‖(heckePrimePowerCutoff F j n : ℂ) * D s j‖ ≤ W j
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hcN j).1]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hcN j).2).trans (hD s hs j)
  have hE (j : Place × ℕ) : ‖E j‖ ≤ W j := by
    change ‖(1 - (heckePrimePowerCutoff F j n : ℂ)) * D s j‖ ≤ W j
    rw [norm_mul, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_of_nonneg (sub_nonneg.mpr (hcN j).2)]
    exact (mul_le_of_le_one_left (norm_nonneg _) (sub_le_self _ (hcN j).1)).trans (hD s hs j)
  have hDs : Summable (D s) := hW.of_norm_bounded (hD s hs)
  have hCs : Summable C := hW.of_norm_bounded hC
  have hEs : Summable (fun j ↦ ‖E j‖) :=
    hW.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hE
  have hEq : ∑' j, E j = (∑' j, D s j) - ∑' j, C j := by
    calc
      _ = ∑' j, (D s j - C j) := tsum_congr fun j ↦ by dsimp [E, C]; ring
      _ = _ := hDs.tsum_sub hCs
  have hEval : ∑' j, D s j =
      (-logDeriv (fun z ↦ ∏' v, heckeEulerFactor F c v z) s) -
      (-logDeriv (fun z ↦ ∏' v, heckeEulerFactor F c v z) b) := by
    exact ((summable_norm_heckePrimePowerTerm F c hc (ha.trans_le hs)).of_norm.tsum_sub
      (summable_norm_heckePrimePowerTerm F c hc hb).of_norm).trans (by
        rw [neg_logDeriv_heckeEulerProduct F c hc (ha.trans_le hs),
          neg_logDeriv_heckeEulerProduct F c hc hb])
  change dist _ (∑' j, C j) < ε
  rw [Complex.dist_eq, ← hEval, ← hEq, ← hEs.of_norm.sum_add_tsum_compl (s := A)]
  have hzero : ∑ j ∈ A, E j = 0 := Finset.sum_eq_zero (fun j hj ↦ by
    simp only [E, hn j hj, Complex.ofReal_one, sub_self, zero_mul])
  rw [hzero, zero_add]
  have hEs' : Summable (fun j : {j // j ∉ A} ↦ ‖E j.val‖) := hEs.subtype _
  exact ((norm_tsum_le_tsum_norm hEs').trans
    (hEs'.tsum_le_tsum (fun j ↦ hE j.val) (hW.subtype _))).trans_lt hA'

/-- Pointwise form of the cutoff limit on the Euler product half-plane. -/
theorem heckePrimePowerCutoff_tendsto (c : Place → ℂ) (hc : ∀ v, ‖c v‖ ≤ 1)
    {s b : ℂ} (hs : 1 < s.re) (hb : 1 < b.re) :
    Tendsto (fun n ↦ ∑' j, (realPlaceCutoff n
      (Real.log ((heckePrimePowerIdeal F j).absNorm : ℝ)) : ℂ) *
      (heckePrimePowerTerm F c s j - heckePrimePowerTerm F c b j)) atTop
      (𝓝 ((-logDeriv (fun z ↦ ∏' v, heckeEulerFactor F c v z) s) -
        (-logDeriv (fun z ↦ ∏' v, heckeEulerFactor F c v z) b))) :=
  (heckePrimePowerCutoff_tendstoUniformlyOn F c hc hs hb).tendsto_at (show s.re ≤ s.re from le_rfl)

end

end Masullo
