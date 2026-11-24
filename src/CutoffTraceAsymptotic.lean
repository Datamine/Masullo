import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Filter Function MeasureTheory Set Topology
open scoped ENNReal

namespace Masullo

noncomputable section

private theorem integral_logBand {K : Type*} [MeasurableSpace K] (ν : Measure K)
    [IsFiniteMeasure ν] {a b : ℝ} (hab : a ≤ b) :
    (∫ p : ℝ × K, ((Icc a b ×ˢ (univ : Set K)).indicator (fun _ => (1 : ℝ))) p
        ∂(volume : Measure ℝ).prod ν) = (b - a) * ν.real univ := by
  rw [integral_indicator (measurableSet_Icc.prod MeasurableSet.univ), setIntegral_const,
    measureReal_def, Measure.prod_prod, ENNReal.toReal_mul, Real.volume_Icc,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hab), smul_eq_mul, mul_one, measureReal_def]

/-- The mass of a cutoff is trapped between the Haar masses of its inner
and outer logarithmic bands. No bound on its derivatives is required. -/
theorem cutoffLogBand_mass_bounds {K : Type*} [MeasurableSpace K] (ν : Measure K)
    [IsFiniteMeasure ν] {a b c d : ℝ} (hac : a ≤ c) (hcd : c ≤ d) (hdb : d ≤ b)
    (ρ : ℝ × K → ℝ) (hρI : Integrable ρ ((volume : Measure ℝ).prod ν))
    (hρ : ∀ p, 0 ≤ ρ p ∧ ρ p ≤ 1)
    (hzero : ∀ p : ℝ × K, p.1 ∉ Icc a b → ρ p = 0)
    (hone : ∀ p : ℝ × K, p.1 ∈ Icc c d → ρ p = 1) :
    (d - c) * ν.real univ ≤ ∫ p, ρ p ∂(volume : Measure ℝ).prod ν ∧
      (∫ p, ρ p ∂(volume : Measure ℝ).prod ν) ≤ (b - a) * ν.real univ := by
  let η := (volume : Measure ℝ).prod ν
  let W (l r : ℝ) := Icc l r ×ˢ (univ : Set K)
  let g (l r : ℝ) := (W l r).indicator (fun _ : ℝ × K => (1 : ℝ))
  have hg (l r : ℝ) : Integrable (g l r) η := by
    change Integrable ((W l r).indicator (fun _ : ℝ × K => (1 : ℝ))) η
    apply (integrable_indicator_iff (measurableSet_Icc.prod MeasurableSet.univ)).mpr
    exact integrableOn_const (by
      dsimp [η, W]
      rw [Measure.prod_prod]
      exact ENNReal.mul_ne_top (Real.volume_Icc ▸ ENNReal.ofReal_ne_top) (measure_ne_top ν _))
  have hlo (p : ℝ × K) : g c d p ≤ ρ p := by
    by_cases hp : p ∈ W c d
    · exact (indicator_of_mem hp _).le.trans_eq (hone p hp.1).symm
    · exact (indicator_of_notMem hp _).le.trans (hρ p).1
  have hhi (p : ℝ × K) : ρ p ≤ g a b p := by
    by_cases hp : p ∈ W a b
    · change ρ p ≤ (W a b).indicator (fun _ => (1 : ℝ)) p
      rw [indicator_of_mem hp]
      exact (hρ p).2
    · have hh : p.1 ∉ Icc a b := fun h => hp ⟨h, mem_univ _⟩
      change ρ p ≤ (W a b).indicator (fun _ => (1 : ℝ)) p
      rw [hzero p hh, indicator_of_notMem hp]
  refine ⟨?_, ?_⟩
  · rw [← integral_logBand ν hcd]
    exact integral_mono (hg c d) hρI hlo
  · rw [← integral_logBand ν (hac.trans (hcd.trans hdb))]
    exact integral_mono hρI (hg a b) hhi

private theorem cutoffLogBand_inner_sub {L ε : ℝ} (hL : 0 < L)
    (hε : 0 ≤ ε) (hgap : L⁻¹ + ε ≤ L - ε) :
    Real.log (L - ε) - Real.log (L⁻¹ + ε) - 2 * Real.log L =
      Real.log (1 - ε / L) - Real.log (1 + ε * L) := by
  have h₁ : 0 < L - ε := (add_pos_of_pos_of_nonneg (inv_pos.mpr hL) hε).trans_le hgap
  have h₂ : 0 < 1 - ε / L := by
    rw [sub_pos, div_lt_iff₀ hL, one_mul]
    linarith
  have h₃ : 0 < 1 + ε * L := by positivity
  have hu : L - ε = L * (1 - ε / L) := by field_simp
  have hd : L⁻¹ + ε = L⁻¹ * (1 + ε * L) := by field_simp
  rw [hu, hd, Real.log_mul hL.ne' h₂.ne', Real.log_mul (inv_pos.mpr hL).ne' h₃.ne', Real.log_inv]
  ring

/-- The Haar mass of the manuscript's logarithmic cutoff is
(2 \, \log \Lambda) times the angular Haar mass, up to a vanishing error,
whenever the transition width satisfies (Lambda\epsilon\to0). -/
theorem cutoffLogBand_mass_asymptotic {K ι : Type*} [MeasurableSpace K]
    (ν : Measure K) [IsFiniteMeasure ν] {l : Filter ι} {Λ ε : ι → ℝ}
    (hΛ : Tendsto Λ l atTop) (hε : Tendsto (fun i => ε i * Λ i) l (𝓝 0))
    (ρ : ι → ℝ × K → ℝ)
    (hdata : ∀ᶠ i in l, 0 ≤ ε i ∧ (Λ i)⁻¹ + ε i ≤ Λ i - ε i ∧
      Integrable (ρ i) ((volume : Measure ℝ).prod ν) ∧
      (∀ p, 0 ≤ ρ i p ∧ ρ i p ≤ 1) ∧
      (∀ p : ℝ × K, p.1 ∉ Icc (-Real.log (Λ i)) (Real.log (Λ i)) → ρ i p = 0) ∧
      (∀ p : ℝ × K,
        p.1 ∈ Icc (Real.log ((Λ i)⁻¹ + ε i)) (Real.log (Λ i - ε i)) → ρ i p = 1)) :
    Tendsto (fun i => (∫ p, ρ i p ∂(volume : Measure ℝ).prod ν) -
      (2 * Real.log (Λ i)) * ν.real univ) l (𝓝 0) := by
  have hpos : ∀ᶠ i in l, 0 < Λ i := hΛ.eventually (eventually_gt_atTop 0)
  have hratio : Tendsto (fun i => ε i / Λ i) l (𝓝 0) := by
    have h := hε.mul (hΛ.inv_tendsto_atTop.pow 2)
    have he : (fun i => ε i * Λ i * (Λ i)⁻¹ ^ 2) =ᶠ[l] fun i => ε i / Λ i :=
      hpos.mono fun i hi => by dsimp; field_simp
    exact (by simpa only [Pi.inv_apply, zero_pow two_ne_zero, mul_zero] using h : Tendsto _ l (𝓝 (0 : ℝ))).congr' he
  have ha : Tendsto (fun i => 1 - ε i / Λ i) l (𝓝 1) := by
    simpa only [sub_zero] using hratio.const_sub 1
  have hb : Tendsto (fun i => 1 + ε i * Λ i) l (𝓝 1) := by
    simpa only [add_zero] using hε.const_add 1
  have hlog := Real.continuousAt_log one_ne_zero
  have hdiff : Tendsto (fun i => Real.log (1 - ε i / Λ i) - Real.log (1 + ε i * Λ i)) l (𝓝 0) := by
    simpa only [Function.comp_apply, Real.log_one, sub_zero] using (hlog.tendsto.comp ha).sub (hlog.tendsto.comp hb)
  have hLo : Tendsto (fun i => (Real.log (1 - ε i / Λ i) - Real.log (1 + ε i * Λ i)) *
      ν.real univ) l (𝓝 0) := by simpa only [zero_mul] using hdiff.mul_const (ν.real univ)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hLo tendsto_const_nhds ?_ ?_
  all_goals
    filter_upwards [hpos, hdata] with i hi hd
    obtain ⟨hεi, hgap, hI, hR, hzero, hone⟩ := hd
    have hc : 0 < (Λ i)⁻¹ + ε i := add_pos_of_pos_of_nonneg (inv_pos.mpr hi) hεi
    have hd : 0 < Λ i - ε i := hc.trans_le hgap
    have hm := cutoffLogBand_mass_bounds ν
      (by rw [← Real.log_inv]; exact Real.log_le_log (inv_pos.mpr hi) (le_add_of_nonneg_right hεi))
      (Real.log_le_log hc hgap) (Real.log_le_log hd (sub_le_self _ hεi))
      (ρ i) hI hR hzero hone
  · have he := cutoffLogBand_inner_sub hi hεi hgap
    rw [← he, sub_mul]
    exact sub_le_sub_right hm.1 _
  · linarith [hm.2]

end
end Masullo
