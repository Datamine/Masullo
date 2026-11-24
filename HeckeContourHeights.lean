import FiniteHeckeLogDerivative
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open Complex Filter Function IsDedekindDomain MeasureTheory Metric NumberField Set
open scoped Classical NumberField Topology

namespace Masullo

noncomputable section

/-- A finite family of forbidden open intervals, with total length less
than one, cannot cover an interval of length one. -/
theorem exists_ordinate_separated {ι : Type*} (Z : Finset ι) (b : ι → ℝ)
    (Y δ : ℝ) (hδ : 0 < δ) (hshort : (Z.card : ℝ) * (2 * δ) < 1) :
    ∃ y ∈ Ioo Y (Y + 1), ∀ ρ ∈ Z, δ ≤ |y - b ρ| := by
  let U (ρ : ι) := Ioo (b ρ - δ) (b ρ + δ)
  have hCover : ¬ Ioo Y (Y + 1) ⊆ ⋃ ρ ∈ Z, U ρ := by
    intro h
    have hlen : volume (Ioo Y (Y + 1)) ≤ ∑ ρ ∈ Z, volume (U ρ) :=
      (measure_mono h).trans (measure_biUnion_finset_le Z U)
    have hm (ρ : ι) : volume (U ρ) = ENNReal.ofReal (2 * δ) := by
      simp only [U, Real.volume_Ioo]
      congr 1
      ring
    rw [Real.volume_Ioo, show Y + 1 - Y = 1 by ring, ENNReal.ofReal_one] at hlen
    simp_rw [hm] at hlen
    rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => (mul_pos two_pos hδ).le),
      Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_one] at hlen
    exact hshort.not_ge ((ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hlen)
  obtain ⟨y, hy, hy'⟩ := not_subset.mp hCover
  refine ⟨y, hy, fun ρ hρ => le_of_not_gt fun hh => hy' ?_⟩
  apply mem_iUnion.mpr
  refine ⟨ρ, mem_iUnion.mpr ⟨hρ, ?_⟩⟩
  obtain ⟨hlo, hhi⟩ := abs_lt.mp hh
  exact ⟨by linarith, by linarith⟩

variable (F : Type*) [Field F] [NumberField F]
private abbrev K := normOneIdeleClass F
private abbrev Place := HeightOneSpectrum (𝓞 F)

local instance contourHeightsNormOneMeasurable : MeasurableSpace (K F) := borel _
local instance contourHeightsNormOneBorel : BorelSpace (K F) := ⟨rfl⟩
local instance contourHeightsIdeleMeasurable : MeasurableSpace (Idele F) := borel _
local instance contourHeightsIdeleBorel : BorelSpace (Idele F) := ⟨rfl⟩

variable (ν : Measure (K F)) [ν.IsHaarMeasure]
variable (η : Measure (Idele F)) [η.IsHaarMeasure]
variable [∀ v : Place F, MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : Place F, BorelSpace (v.adicCompletion F)ˣ]
  (μ : ∀ v : Place F, Measure (v.adicCompletion F)ˣ)
  [∀ v : Place F, (μ v).IsHaarMeasure] [∀ v : Place F, SigmaFinite (μ v)]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]
variable (hν : IsWeilQuotientMeasure (principalIdeles F) η Measure.count (globalClassMeasure F ν))

set_option maxHeartbeats 500000 in
include μ hν in
/-- Every sufficiently high positive or negative unit interval supplies
a horizontal segment where the finite Hecke logarithmic derivative has a
uniform quadratic bound. -/
theorem exists_manuscriptFiniteHecke_good_ordinates (χ : PontryaginDual (IdeleClass F)) :
    ∃ (L : ℂ → ℂ) (T C : ℝ), 0 ≤ C ∧ 3 ≤ T ∧ MeromorphicNFOn L univ ∧
      EqOn L (manuscriptFiniteHeckeEuler F χ) {z | 1 < z.re} ∧
      ∀ Y : ℝ, T ≤ |Y| → ∃ y ∈ Ioo Y (Y + 1), ∀ x ∈ Icc (-1 : ℝ) 2,
        let z : ℂ := ⟨x, y⟩
        AnalyticAt ℂ L z ∧ L z ≠ 0 ∧ ‖logDeriv L z‖ ≤ C * |y| ^ 2 := by
  obtain ⟨L, N, T, hN, hT, hL, he, hDisk⟩ :=
    exists_manuscriptFiniteHecke_disk_bound_radius F ν η μ hν χ (R := 12) (by norm_num)
  let D : ℝ := (N : ℝ) / Real.log (12 / 7)
  let E : ℝ := (N : ℝ) / Real.log 2
  have hD : 0 ≤ D := div_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by norm_num))
  have hE : 0 ≤ E := div_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by norm_num))
  let C : ℝ := 25 * N + 4 * E * (1 + 2 * D)
  refine ⟨L, T+1, C, by positivity, by linarith, hL, he, fun Y hY => ?_⟩
  obtain ⟨haY, hcY, hbY⟩ := hDisk Y (by linarith)
  obtain ⟨Z, hZ, hcard⟩ := RiemannMasullo.landau_card_zeros_closedBall_le
    (by norm_num : (0 : ℝ) < 7) (by norm_num : (7 : ℝ) < 12) haY hcY hbY
  let δ : ℝ := 1 / (4 * ((Z.card : ℝ) + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδcard : (Z.card : ℝ) * (2 * δ) < 1 := by
    dsimp [δ]
    rw [← mul_assoc, mul_one_div, div_lt_iff₀ (by positivity)]
    have hn : (0 : ℝ) ≤ Z.card := Nat.cast_nonneg _
    linarith
  obtain ⟨y, hy, hSep⟩ := exists_ordinate_separated Z Complex.im Y δ hδ hδcard
  have hyY : |y-Y| ≤ 1 := abs_le.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have hYy : |Y| ≤ |y| + 1 := by
    have h := (abs_abs_sub_abs_le_abs_sub y Y).trans hyY
    linarith [(abs_le.mp h).1]
  have hyT : T ≤ |y| := by linarith
  have hy1 : 1 ≤ |y| := by linarith
  obtain ⟨ha, hc, hb⟩ := hDisk y hyT
  have hShift : ‖(⟨2, y⟩ : ℂ) - ⟨2, Y⟩‖ = |y-Y| := by
    rw [show (⟨2, y⟩ : ℂ) - ⟨2, Y⟩ = ((y-Y : ℝ) : ℂ) * I by
      apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]]
    rw [norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs]
  refine ⟨y, hy, fun x hx => ?_⟩
  let z : ℂ := ⟨x, y⟩
  have hz : z ∈ closedBall (⟨2, y⟩ : ℂ) 3 := by
    rw [mem_closedBall_iff_norm, show z - (⟨2, y⟩ : ℂ) = ((x-2 : ℝ) : ℂ) by
      apply Complex.ext <;> simp [z]]
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hNear (ρ : ℂ) (hρ : ρ ∈ closedBall (⟨2, y⟩ : ℂ) 6) (hρ₀ : L ρ = 0) :
      δ ≤ ‖z - ρ‖ := by
    have h7 : ρ ∈ closedBall (⟨2, Y⟩ : ℂ) 7 := by
      rw [mem_closedBall_iff_norm] at hρ ⊢
      calc
        _ ≤ ‖ρ - (⟨2, y⟩ : ℂ)‖ + ‖(⟨2, y⟩ : ℂ) - ⟨2, Y⟩‖ := by
          simpa only [sub_add_sub_cancel] using
            (norm_add_le (ρ - (⟨2, y⟩ : ℂ)) ((⟨2, y⟩ : ℂ) - ⟨2, Y⟩))
        _ ≤ 7 := by rw [hShift]; linarith
    exact (hSep ρ ((hZ ρ).mpr ⟨h7, hρ₀⟩)).trans (Complex.abs_im_le_norm (z-ρ))
  have hz₀ : L z ≠ 0 := fun h => (not_le_of_gt hδ) (by
    simpa using hNear z (closedBall_subset_closedBall (by norm_num) hz) h)
  refine ⟨ha _ (closedBall_subset_closedBall (by norm_num) hz), hz₀, ?_⟩
  have hLandau := RiemannMasullo.landau_norm_logDeriv_le_of_zero_separation
    (one_lt_pow₀ (by linarith : 1 < |y|) hN.ne') (by norm_num : (0 : ℝ) < 12)
    hδ ha hc hb (by simpa only [show (12 : ℝ) / 4 = 3 by norm_num] using hz)
    hz₀ (fun ρ hρ => hNear ρ (by simpa only [show (12 : ℝ) / 2 = 6 by norm_num] using hρ))
  rw [Real.log_pow] at hcard hLandau
  have hLog (u : ℝ) (hu : 0 < u) : Real.log u ≤ u :=
    (Real.log_le_sub_one_of_pos hu).trans (by linarith)
  have hcard' : (Z.card : ℝ) ≤ (2*D) * |y| := by
    calc
      _ ≤ D * Real.log |Y| := hcard.trans_eq (by dsimp [D]; ring)
      _ ≤ D * |Y| := mul_le_mul_of_nonneg_left (hLog _ (by linarith)) hD
      _ ≤ (2*D) * |y| := by
        rw [mul_assoc, mul_left_comm 2 D]
        exact mul_le_mul_of_nonneg_left (by linarith) hD
  have hδinv : δ⁻¹ ≤ (4 * (1 + 2 * D)) * |y| := by
    dsimp [δ]
    rw [one_div, inv_inv]
    have h := add_le_add hcard' hy1
    linarith
  have hlogy : Real.log |y| ≤ |y| := hLog _ (by linarith)
  have hlogy₀ : 0 ≤ Real.log |y| := Real.log_nonneg hy1
  have hterm₁ : 300 * ((N : ℝ) * Real.log |y|) / 12 ≤ 25 * N * |y| ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hlogy (show (0 : ℝ) ≤ 25 * N by positivity)
    have hs := mul_le_mul_of_nonneg_left
      (show |y| ≤ |y| ^ 2 by nlinarith) (show (0 : ℝ) ≤ 25 * N by positivity)
    linarith [h.trans hs]
  have hterm₂ : ((N : ℝ) * Real.log |y| / Real.log 2) / δ ≤
      (4 * E * (1 + 2 * D)) * |y| ^ 2 := by
    rw [div_eq_mul_inv, show (N : ℝ) * Real.log |y| / Real.log 2 = E * Real.log |y| by dsimp [E]; ring]
    calc
      _ ≤ (E * |y|) * ((4 * (1 + 2 * D)) * |y|) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hlogy hE) hδinv (by positivity) (by positivity)
      _ = _ := by ring
  exact hLandau.trans ((add_le_add hterm₁ hterm₂).trans_eq (by dsimp [C]; ring))

include μ hν in
/-- Two exhausting sequences of horizontal lines satisfy the uniform
finite Hecke logarithmic-derivative bound. -/
theorem exists_manuscriptFiniteHecke_horizontal_contours (χ : PontryaginDual (IdeleClass F)) :
    ∃ (L : ℂ → ℂ) (lo hi : ℕ → ℝ) (C : ℝ), 0 ≤ C ∧ MeromorphicNFOn L univ ∧
      EqOn L (manuscriptFiniteHeckeEuler F χ) {z | 1 < z.re} ∧
      Tendsto lo atTop atBot ∧ Tendsto hi atTop atTop ∧
      ∀ j (x : ℝ), x ∈ Icc (-1 : ℝ) 2 → ∀ y ∈ ({lo j, hi j} : Set ℝ),
        let z : ℂ := ⟨x, y⟩
        AnalyticAt ℂ L z ∧ L z ≠ 0 ∧ ‖logDeriv L z‖ ≤ C * |y| ^ 2 := by
  obtain ⟨L, T, C, hC, hT, hL, he, hGood⟩ :=
    exists_manuscriptFiniteHecke_good_ordinates F ν η μ hν χ
  have hp (j : ℕ) : T ≤ |T + (j : ℝ)| := (le_add_of_nonneg_right (Nat.cast_nonneg _)).trans (le_abs_self _)
  have hn (j : ℕ) : T ≤ |-(T + (j : ℝ) + 1)| := by
    rw [abs_neg]
    exact (show T ≤ T + (j : ℝ) + 1 by linarith [Nat.cast_nonneg (α := ℝ) j]).trans (le_abs_self _)
  choose hi hhi hHi using fun j : ℕ ↦ hGood (T + (j : ℝ)) (hp j)
  choose lo hlo hLo using fun j : ℕ ↦ hGood (-(T + (j : ℝ) + 1)) (hn j)
  refine ⟨L, lo, hi, C, hC, hL, he, ?_, ?_, ?_⟩
  · apply tendsto_atBot.mpr
    intro b
    obtain ⟨k, hk⟩ := exists_nat_ge (-b - T)
    filter_upwards [eventually_ge_atTop k] with j hj
    have hkj : (k : ℝ) ≤ j := Nat.cast_le.mpr hj
    linarith [(hlo j).2]
  · apply Filter.tendsto_atTop.mpr
    intro b
    obtain ⟨k, hk⟩ := exists_nat_ge (b - T)
    filter_upwards [eventually_ge_atTop k] with j hj
    have hkj : (k : ℝ) ≤ j := Nat.cast_le.mpr hj
    linarith [(hhi j).1]
  · intro j x hx y hy
    rcases mem_insert_iff.mp hy with rfl | h
    · exact hLo j x hx
    · rw [mem_singleton_iff.mp h]
      exact hHi j x hx

end

end Masullo
