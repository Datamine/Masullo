import LandauDisk
import LogDistanceMeasure

open Complex Filter MeasureTheory Metric Set
open scoped Classical ComplexConjugate ENNReal

namespace Masullo

open RiemannMasullo.External.PrimeNumberTheoremAnd

/-- On an inner disk, removing the zeros in the intermediate disk leaves
a factor bounded below by a fixed power of the bound on the outer disk. -/
theorem disk_minimum_modulus_normalized {f : ℂ → ℂ} {B : ℝ}
    (hB : 1 < B) (hf : AnalyticOnNhd ℂ f (closedBall 0 1)) (hf₀ : f 0 = 1)
    (hbound : ∀ z : ℂ, ‖z‖ ≤ 3 / 4 → ‖f z‖ ≤ B) :
    ∃ Z : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ Z ↔ ‖ρ‖ ≤ 1 / 2 ∧ f ρ = 0) ∧
      ((∑ ρ ∈ Z, analyticOrderNatAt f ρ : ℕ) : ℝ) ≤ Real.log B / Real.log (3 / 2) ∧
      ∀ z : ℂ, ‖z‖ ≤ 1 / 4 → z ∉ Z →
        (B ^ 2)⁻¹ * (∏ ρ ∈ Z, ‖z - ρ‖ ^ analyticOrderNatAt f ρ) ≤ ‖f z‖ := by
  have hfne : f 0 ≠ 0 := by simp [hf₀]
  have hfin : (SetOfZeros 1 f).Finite := by
    apply (RiemannMasullo.finite_zeros_closedBall zero_le_one hf hfne).subset
    intro z hz
    exact ⟨by simpa using hz.1, hz.2⟩
  have hr : (0 : ℝ) < 1 / 2 := by norm_num
  have hr' : (0 : ℝ) < 1 / 4 := by norm_num
  have hrr : (1 / 4 : ℝ) < 1 / 2 := by norm_num
  have hR : (1 / 2 : ℝ) < 3 / 4 := by norm_num
  have hR₁ : (3 / 4 : ℝ) < 1 := by norm_num
  have hfin' := finiteSetOfZeros_mono (hR.trans hR₁) hfin
  let Z := hfin'.toFinset
  have hZ (ρ : ℂ) : ρ ∈ Z ↔ ‖ρ‖ ≤ 1 / 2 ∧ f ρ = 0 :=
    Set.Finite.mem_toFinset hfin'
  refine ⟨Z, hZ, ?_, fun z hz hzZ ↦ ?_⟩
  · have h := ZerosBound hr (hR.trans hR₁) hR hR₁ hf hf₀ hfin hbound
    norm_num at h ⊢
    simpa only [Z, one_div, div_eq_mul_inv, mul_comm] using h
  · let G := BlaschkeB (1 / 2) (3 / 4) f
    have hG := BlaschkeAnalytic hr hR hR₁ hfin hf hfne
    have hGnz := BlaschkeNonzero hr hR hR₁ hfin hf hfne
    have hG₀ : 1 ≤ ‖G 0‖ := by
      simpa only [G, hf₀, norm_one] using norm_fOfZero_le_norm_BlaschkeOfZero hr hR hR₁ hfin hfne
    obtain ⟨J, hJ, hJ₀, _, hlog⟩ := LogOfAnalyticFunction' hr' hrr hR hG hGnz
    have hupper (w : ℂ) (hw : w ∈ ball 0 (1 / 2)) : (J w).re ≤ Real.log B := by
      rw [← hlog w hw]
      have hw₁ := ball_subset_closedBall hw
      have hp : 0 < ‖G w‖ := norm_pos_iff.mpr (hGnz w hw₁)
      have hgb : ‖G w‖ ≤ B := DiskBound hr hR hR₁ hfin hf hfne hbound
        (closedBall_subset_closedBall hR.le hw₁)
      linarith [Real.log_le_log hp hgb, Real.log_nonneg hG₀]
    have hz' : z ∈ closedBall 0 (1 / 4) := by simpa using hz
    have hJz := borelCaratheodory' (Real.log_pos hB) hr' hrr hJ.analyticOn hJ₀ hupper hz'
    have hloglower : -(2 * Real.log B) ≤ Real.log ‖G z‖ := by
      have h₁ := (neg_le_abs (J z).re).trans ((Complex.abs_re_le_norm _).trans hJz)
      rw [← hlog z (closedBall_subset_ball hrr hz')] at h₁
      norm_num at h₁
      linarith [Real.log_nonneg hG₀]
    have hlow : (B ^ 2)⁻¹ ≤ ‖G z‖ := by
      have hBn : 0 < B := zero_lt_one.trans hB
      apply (Real.log_le_log_iff (inv_pos.mpr (pow_pos hBn _))
        (norm_pos_iff.mpr (hGnz z (closedBall_subset_closedBall hrr.le hz')))).mp
      rw [Real.log_inv, Real.log_pow]
      push_cast
      exact hloglower
    let P := ∏ ρ ∈ Z, ‖z - ρ‖ ^ analyticOrderNatAt f ρ
    let Q := ∏ ρ ∈ Z, ‖(3 / 4 : ℂ) - z * conj ρ / (3 / 4 : ℂ)‖ ^ analyticOrderNatAt f ρ
    have hP : 0 < P := Finset.prod_pos (fun ρ hρ ↦
      pow_pos (norm_pos_iff.mpr (sub_ne_zero.mpr (fun e ↦ hzZ (by rwa [e])))) _)
    have hQ : Q ≤ 1 := Finset.prod_le_one (fun _ _ ↦ by positivity) (fun ρ hρ ↦ by
      apply pow_le_one₀ (norm_nonneg _) _
      have hρn := (hZ ρ).mp hρ
      have hh : ‖z‖ * ‖ρ‖ ≤ (1 / 4) * (1 / 2) := mul_le_mul hz hρn.1 (norm_nonneg _) (by norm_num)
      calc
        _ ≤ ‖(3 / 4 : ℂ)‖ + ‖z * conj ρ / (3 / 4 : ℂ)‖ := norm_sub_le _ _
        _ ≤ 1 := by
          simp only [norm_div, norm_mul, Complex.norm_conj, Complex.norm_ofNat]
          linarith)
    have hex : ‖G z‖ = (‖f z‖ / P) * Q := by
      have hn : z ∉ SetOfZeros (1 / 2) f := fun hz0 ↦ hzZ (hfin'.mem_toFinset.mpr hz0)
      simp only [G, BlaschkeB, Cf, dite_eq_left hfin', hn, dite_eq_ite, ite_false,
        norm_mul, norm_div, norm_prod, norm_pow, P, Q, Z, Complex.ofReal_div, Complex.ofReal_ofNat]
    rw [hex] at hlow
    have hquot : (B ^ 2)⁻¹ ≤ ‖f z‖ / P := hlow.trans (mul_le_of_le_one_right (by positivity) hQ)
    exact (le_div_iff₀ hP).mp hquot

set_option maxHeartbeats 400000 in
/-- A normalized analytic function on a scaled disk has a common
horizontal lower bound away from an exceptional set of specified measure. -/
theorem disk_horizontal_minimum_modulus {f : ℂ → ℂ} {T sign : ℝ} {N : ℕ}
    (hT : 1 < T) (hN : 0 < N)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 1)) (hf₀ : f 0 = 1)
    (hbound : ∀ z : ℂ, ‖z‖ ≤ 3 / 4 → ‖f z‖ ≤ T ^ N)
    (hsign : |sign| = 1)
    {B : ℝ} (hB : 1 < B) :
    let A : ℝ := 2 * (N : ℝ) + (N : ℝ) / Real.log (3 / 2) * (Real.log 16 + 2)
    ∃ E : Set ℝ, MeasurableSet E ∧ E ⊆ Icc T (T + 1) ∧ volume E = ENNReal.ofReal (1 / B) ∧
      ∀ t ∈ Icc T (T + 1) \ E, ∀ x ∈ Icc (-1 : ℝ) 2,
        T ^ (-(A * B)) < ‖f ((⟨x - 2, sign * (t - T)⟩ : ℂ) / 16)‖ := by
  intro A
  obtain ⟨Z, _, hCount, hLow⟩ :=
    disk_minimum_modulus_normalized (one_lt_pow₀ hT hN.ne') hf hf₀ hbound
  let m := analyticOrderNatAt f
  let γ (ρ : ℂ) := T + 16 * sign * ρ.im
  let M : ℝ := (N : ℝ) / Real.log (3 / 2) * Real.log T
  have hM : 0 < M := mul_pos (div_pos (Nat.cast_pos.mpr hN) (Real.log_pos (by norm_num)))
    (Real.log_pos hT)
  have hc : (∑ ρ ∈ Z, (m ρ : ℝ)) ≤ M := by
    rw [Real.log_pow, Nat.cast_sum] at hCount
    exact hCount.trans_eq (by dsimp [M]; ring)
  obtain ⟨E, hE, hEI, hEV, hGood⟩ := logDistanceLoss_off_exception Z γ m hM hc hB
  refine ⟨E, hE, hEI, hEV, fun t ht x hx ↦ ?_⟩
  let z : ℂ := (⟨x - 2, sign * (t - T)⟩ : ℂ) / 16
  have hnorm16 : ‖(16 : ℂ)‖ = 16 := by norm_num
  have h16re (w : ℂ) : (w / 16).im = w.im / 16 := by
    norm_num [Complex.div_im, Complex.normSq_apply]
  have hIm : z.im = (sign * (t - T)) / 16 := h16re _
  have hz : ‖z‖ ≤ 1 / 4 := by
    dsimp [z]
    rw [norm_div, hnorm16, div_le_iff₀ (by norm_num : (0 : ℝ) < 16)]
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    change |x - 2| + |sign * (t - T)| ≤ 1 / 4 * 16
    rw [abs_mul, hsign, one_mul, abs_of_nonpos (sub_nonpos.mpr hx.2),
      abs_of_nonneg (sub_nonneg.mpr ht.1.1)]
    linarith [hx.1, ht.1.2]
  obtain ⟨hOrd, hSum⟩ := hGood t ht
  have hSignSq : sign ^ 2 = 1 := by
    rw [← sq_abs, hsign, one_pow]
  have hRel (ρ : ℂ) : (z - ρ).im = (sign * (t - γ ρ)) / 16 := by
    rw [Complex.sub_im, hIm]
    dsimp [γ]
    linear_combination ρ.im * (hSignSq)
  have hdist (ρ : ℂ) : |t - γ ρ| / 16 ≤ ‖z - ρ‖ := by
    have h := Complex.abs_im_le_norm (z - ρ)
    rwa [hRel, abs_div, abs_mul, hsign, one_mul, abs_of_pos (by norm_num : (0 : ℝ) < 16)] at h
  have hdist₀ (ρ : ℂ) (hρ : ρ ∈ Z) : 0 < |t - γ ρ| / 16 :=
    div_pos (abs_pos.mpr (sub_ne_zero.mpr (hOrd ρ hρ))) (by norm_num)
  have hzZ : z ∉ Z := fun h ↦ by simpa using (hdist₀ z h).trans_le (hdist z)
  let P := ∏ ρ ∈ Z, ‖z - ρ‖ ^ m ρ
  have hP : 0 < P := Finset.prod_pos (fun ρ hρ ↦ pow_pos ((hdist₀ ρ hρ).trans_le (hdist ρ)) _)
  have hV : 0 < (T ^ N) ^ 2 := by positivity
  have h0 : 0 < ‖f z‖ := (mul_pos (inv_pos.mpr hV) hP).trans_le (hLow z hz hzZ)
  have hLowLog := Real.log_le_log (mul_pos (inv_pos.mpr hV) hP) (hLow z hz hzZ)
  change Real.log (((T ^ N) ^ 2)⁻¹ * P) ≤ Real.log ‖f z‖ at hLowLog
  rw [Real.log_mul (inv_ne_zero hV.ne') hP.ne', Real.log_inv, Real.log_pow, Real.log_pow] at hLowLog
  have hPlog : Real.log P = ∑ ρ ∈ Z, (m ρ : ℝ) * Real.log ‖z - ρ‖ := by
    dsimp only [P]
    rw [Real.log_prod (fun ρ hρ ↦ (pow_pos ((hdist₀ ρ hρ).trans_le (hdist ρ)) (m ρ)).ne')]
    simp_rw [Real.log_pow]
  have hLogs (ρ : ℂ) (hρ : ρ ∈ Z) :
      -logDistanceLoss (γ ρ) t - Real.log 16 ≤ Real.log ‖z - ρ‖ := by
    have h := Real.log_le_log (hdist₀ ρ hρ) (hdist ρ)
    rw [Real.log_div ((abs_pos.mpr (sub_ne_zero.mpr (hOrd ρ hρ))).ne') (by norm_num)] at h
    have hneg : -Real.log |t - γ ρ| ≤ logDistanceLoss (γ ρ) t := le_max_right _ _
    linarith
  have hSumLower : -(∑ ρ ∈ Z, (m ρ : ℝ) * logDistanceLoss (γ ρ) t) -
      (∑ ρ ∈ Z, (m ρ : ℝ)) * Real.log 16 ≤ Real.log P := by
    rw [hPlog, ← Finset.sum_neg_distrib, Finset.sum_mul, ← Finset.sum_sub_distrib]
    exact Finset.sum_le_sum fun ρ hρ ↦ by
      simpa only [mul_sub, mul_neg] using mul_le_mul_of_nonneg_left (hLogs ρ hρ) (Nat.cast_nonneg (m ρ))
  have hMain : -(A * B) * Real.log T < Real.log ‖f z‖ := by
    rw [hPlog] at hLowLog
    rw [hPlog] at hSumLower
    have hln16 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 16)
    have hmul := mul_le_mul_of_nonneg_right hc hln16
    have hmb := mul_nonneg hM.le (sub_nonneg.mpr hB.le)
    have hnb := mul_nonneg (mul_nonneg (Nat.cast_nonneg N) (Real.log_nonneg hT.le))
      (sub_nonneg.mpr hB.le)
    have hmb' := mul_nonneg hmb hln16
    dsimp [A, M] at *
    push_cast at *
    linarith [hSum, hSumLower, hLowLog, hmul, hnb, hmb']
  change T ^ (-(A * B)) < ‖f z‖
  exact (Real.log_lt_log_iff (Real.rpow_pos_of_pos (zero_lt_one.trans hT) _) h0).mp
    (by rwa [Real.log_rpow (zero_lt_one.trans hT)])

end Masullo
