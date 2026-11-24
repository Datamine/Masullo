/-
The Wiener–Ikehara comparison uses the proof from RiemannMasullo
AppB_AnalyticNT/Sec6.lean at 4cb67a2 (Apache-2.0).
See External/PROVENANCE.md and External/RiemannMasullo.LICENSE.
-/
import HeckeIdealContinuation
import External.PrimeNumberTheoremAnd.WienerIkehara
import Mathlib.NumberTheory.LSeries.Linearity

open Filter Function Ideal IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped ComplexConjugate NumberField

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

private abbrev K := normOneIdeleClass F
private abbrev Place := HeightOneSpectrum (𝓞 F)

private theorem conjugate_LSeriesHasSum (a : ℕ → ℂ) (s l : ℂ)
    (h : LSeriesHasSum a (conj s) l) :
    LSeriesHasSum (fun n ↦ conj (a n)) s (conj l) := by
  have h' := h.star
  unfold LSeriesHasSum
  convert h' using 1
  · funext n
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn]
    change _ = (starRingEnd ℂ) _
    rw [map_div₀, ← Complex.conj_cpow _ _ (by rw [Complex.natCast_arg]; positivity),
      Complex.conj_natCast]
  · rfl

private theorem idealCounts_limit :
    Tendsto (fun x : ℝ ↦ (∑ n ∈ Finset.Icc 0 ⌊x⌋₊, finiteHeckeNormMultiplicity F n) / x)
      atTop (𝓝 (dedekindZeta_residue F)) := by
  have h := (Complex.continuous_re.tendsto _).comp (finiteHeckeIdealSummatory_one_tendsto F)
  simp only [Complex.ofReal_re] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  rw [Function.comp_apply, finiteHeckeIdealSummatory_eq_sum F 1 x hx]
  simp_rw [finiteHeckeNormCoefficient_one]
  rw [← Complex.ofReal_sum, ← Complex.ofReal_div, Complex.ofReal_re]

private theorem idealCounts_linearBound :
    ∃ C : ℝ, ∀ n : ℕ, (∑ i ∈ Finset.range n, finiteHeckeNormMultiplicity F i) ≤ C * n := by
  let N := finiteHeckeNormMultiplicity F
  let S (n : ℕ) := ∑ i ∈ Finset.Icc 0 n, N i
  have hlim : Tendsto (fun n : ℕ ↦ S n / n) atTop (𝓝 (dedekindZeta_residue F)) := by
    simpa [Function.comp_def, S, N] using (idealCounts_limit F).comp tendsto_natCast_atTop_atTop
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1
    (hlim.eventually (gt_mem_nhds (lt_add_one (dedekindZeta_residue F))))
  have hSmono {m n : ℕ} (h : m ≤ n) : S m ≤ S n :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc le_rfl h)
      fun i _ _ ↦ finiteHeckeNormMultiplicity_nonneg F i
  have hS0 (n : ℕ) : 0 ≤ S n :=
    Finset.sum_nonneg fun i _ ↦ finiteHeckeNormMultiplicity_nonneg F i
  refine ⟨dedekindZeta_residue F + 1 + S n₀, fun n ↦ ?_⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hle : ∑ i ∈ Finset.range n, N i ≤ S n :=
    Finset.sum_le_sum_of_subset_of_nonneg
      (fun i hi ↦ Finset.mem_Icc.mpr ⟨Nat.zero_le _, (Finset.mem_range.mp hi).le⟩)
      fun i _ _ ↦ finiteHeckeNormMultiplicity_nonneg F i
  refine hle.trans ?_
  rcases le_or_gt n₀ n with h | h
  · have hb := hn₀ n h
    rw [div_lt_iff₀ (by linarith)] at hb
    nlinarith [hS0 n₀]
  · have hb := hSmono h.le
    nlinarith [hS0 n₀, dedekindZeta_residue_pos F]

local instance : MeasurableSpace (Idele F) := borel _
local instance : BorelSpace (Idele F) := ⟨rfl⟩
local instance : MeasurableSpace (K F) := borel _
local instance : BorelSpace (K F) := ⟨rfl⟩

section MeasureData

variable (η : Measure (Idele F)) [η.IsHaarMeasure]
variable (ν : Measure (K F)) [ν.IsHaarMeasure]
variable [∀ v : Place F, MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : Place F, BorelSpace (v.adicCompletion F)ˣ]
  (μ : ∀ v : Place F, Measure (v.adicCompletion F)ˣ)
  [∀ v : Place F, (μ v).IsHaarMeasure] [∀ v : Place F, SigmaFinite (μ v)]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]
variable (hν : IsWeilQuotientMeasure (principalIdeles F) η Measure.count (globalClassMeasure F ν))

set_option maxHeartbeats 1800000 in
include μ hν in
/-- Lemma B.6.1.2(2). Cancellation holds for every unitary idele-class
character nontrivial on norm one, with its actual finite ideal weights. -/
theorem finiteHeckeIdealSummatory_tendsto_zero_of_nontrivial
    (χ : PontryaginDual (IdeleClass F)) (hχ : heckeNormOneRestriction F χ ≠ 1) :
    Tendsto (fun x : ℝ ↦ finiteHeckeIdealSummatory F χ x / x) atTop (𝓝 0) := by
  let N := finiteHeckeNormMultiplicity F
  let a := finiteHeckeNormCoefficient F χ
  let c := dedekindZeta_residue F
  have hN (n : ℕ) : 0 ≤ N n := finiteHeckeNormMultiplicity_nonneg F n
  have ha (n : ℕ) : ‖a n‖ ≤ N n := norm_finiteHeckeNormCoefficient_le F χ n
  obtain ⟨C, hC⟩ := idealCounts_linearBound F
  obtain ⟨G, hG, hGeq⟩ := exists_idealNormMultiplicity_pole_subtraction F η ν μ hν
  obtain ⟨M, hM, hMsum⟩ := exists_finiteHeckeNormCoefficient_entire F η ν μ hν χ hχ
  have hNsum (s : ℂ) (hs : 1 < s.re) :
      LSeriesHasSum (fun n ↦ (N n : ℂ)) s (LSeries (fun n ↦ (N n : ℂ)) s) := by
    have h := manuscriptFiniteHeckeEuler_hasSum_normCoefficients F 1 hs
    rw [show finiteHeckeNormCoefficient F 1 = (fun n ↦ (finiteHeckeNormMultiplicity F n : ℂ))
      from funext (finiteHeckeNormCoefficient_one F)] at h
    exact h.LSeriesSummable.LSeriesHasSum
  have hWI (u : ℕ → ℝ) (H : ℂ → ℂ) (hu : 0 ≤ u) (hu2 : ∀ n, u n ≤ 2 * N n)
      (hH : ContinuousOn H {s | 1 ≤ s.re})
      (hsum : ∀ s : ℂ, 1 < s.re →
        LSeriesHasSum (fun n ↦ (u n : ℂ)) s (LSeries (fun n ↦ (N n : ℂ)) s + H s)) :
      Tendsto (fun x : ℝ ↦ (∑ n ∈ Finset.Icc 0 ⌊x⌋₊, u n) / x) atTop (𝓝 c) := by
    refine WienerIkehara.tendsto_sum_div (C := 2 * C) (G := fun s ↦ G s + H s)
      (fun n ↦ ?_) (hG.add hH) (fun s hs ↦ ?_) hu
    · calc
        ∑ i ∈ Finset.range n, u i ≤ ∑ i ∈ Finset.range n, 2 * N i :=
          Finset.sum_le_sum fun i _ ↦ hu2 i
        _ = 2 * ∑ i ∈ Finset.range n, N i := by rw [Finset.mul_sum]
        _ ≤ 2 * (C * n) := by linarith [hC n]
        _ = 2 * C * n := by ring
    · change G s + H s = LSeries (fun n ↦ (u n : ℂ)) s - (c : ℂ) / (s - 1)
      have h := hGeq hs
      change G s = LSeries (fun n ↦ (N n : ℂ)) s - (c : ℂ) / (s - 1) at h
      rw [h, (hsum s hs).LSeries_eq]
      ring
  let M' (s : ℂ) := conj (M (conj s))
  have hM' (s : ℂ) (hs : 1 < s.re) : LSeriesHasSum (conj ∘ a) s (M' s) :=
    conjugate_LSeriesHasSum a s _ (hMsum _ (by rwa [Complex.conj_re]))
  have hcM : Continuous M' := Complex.continuous_conj.comp (hM.continuous.comp Complex.continuous_conj)
  have hr := hWI (fun n ↦ N n + (a n).re) (fun s ↦ (M s + M' s) / 2)
    (fun n ↦ by
      change 0 ≤ N n + (a n).re
      linarith [(abs_le.mp (Complex.abs_re_le_norm (a n))).1, ha n])
    (fun n ↦ by linarith [Complex.re_le_norm (a n), ha n])
    ((hM.continuous.add hcM).div_const _).continuousOn
    (fun s hs ↦ by
      have h := (hNsum s hs).add (((hMsum s hs).add (hM' s hs)).smul (1 / 2 : ℂ))
      convert h using 1
      · funext n
        simp only [Pi.add_apply, Pi.smul_apply, Function.comp_apply, smul_eq_mul]
        push_cast
        rw [Complex.re_eq_add_conj]
        ring
      · ring)
  have hi := hWI (fun n ↦ N n + (a n).im) (fun s ↦ (M s - M' s) / (2 * Complex.I))
    (fun n ↦ by
      change 0 ≤ N n + (a n).im
      linarith [(abs_le.mp (Complex.abs_im_le_norm (a n))).1, ha n])
    (fun n ↦ by linarith [Complex.im_le_norm (a n), ha n])
    ((hM.continuous.sub hcM).div_const _).continuousOn
    (fun s hs ↦ by
      have h := (hNsum s hs).add (((hMsum s hs).sub (hM' s hs)).smul (1 / (2 * Complex.I)))
      convert h using 1
      · funext n
        simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Function.comp_apply, smul_eq_mul]
        push_cast
        rw [Complex.im_eq_sub_conj]
        ring
      · ring)
  have hdiff (u : ℕ → ℝ) (hu :
      Tendsto (fun x : ℝ ↦ (∑ n ∈ Finset.Icc 0 ⌊x⌋₊, (N n + u n)) / x) atTop (𝓝 c)) :
      Tendsto (fun x : ℝ ↦ (∑ n ∈ Finset.Icc 0 ⌊x⌋₊, u n) / x) atTop (𝓝 0) := by
    have h := hu.sub (idealCounts_limit F)
    change Tendsto _ _ (𝓝 (c - c)) at h
    rw [sub_self] at h
    refine h.congr fun x ↦ ?_
    rw [Finset.sum_add_distrib]
    ring
  have hre := hdiff _ hr
  have him := hdiff _ hi
  have hlim := ((Complex.continuous_ofReal.tendsto 0).comp hre).add
    (((Complex.continuous_ofReal.tendsto 0).comp him).mul_const Complex.I)
  simp only [Complex.ofReal_zero, zero_mul, add_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  rw [finiteHeckeIdealSummatory_eq_sum F χ x hx]
  simp only [Function.comp_apply, Complex.ofReal_div, Complex.ofReal_sum]
  rw [div_mul_eq_mul_div, ← add_div, Finset.sum_mul, ← Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_congr rfl fun n _ ↦ Complex.re_add_im (a n)

end MeasureData

set_option maxHeartbeats 1800000 in
/-- Corrected Lemma B.6.1.2 for every unitary idele-class character.
The untwisted count uses the single discriminant factor in the class-number
residue; all nontrivial norm-one components have mean zero. -/
theorem finiteHeckeIdealSummatory_asymptotics (χ : PontryaginDual (IdeleClass F)) :
    (heckeNormOneRestriction F χ = 1 →
      (∃! t : ℝ, χ = ideleNormCircle F (-t)) ∧
      ∀ t, χ = ideleNormCircle F (-t) →
        Tendsto (fun x : ℝ ↦ finiteHeckeIdealSummatory F (χ * ideleNormCircle F t) x / x)
          atTop (𝓝 (dedekindZeta_residue F : ℂ))) ∧
    (heckeNormOneRestriction F χ ≠ 1 →
      Tendsto (fun x : ℝ ↦ finiteHeckeIdealSummatory F χ x / x) atTop (𝓝 0)) := by
  constructor
  · intro hχ
    exact finiteHeckeIdealSummatory_normTwist_tendsto F χ
      (fun k ↦ DFunLike.congr_fun hχ k)
  · intro hχ
    letI : LocallyCompactSpace (Idele F) := ideles_locallyCompact
    let η₀ : Measure (Idele F) := Measure.haar
    haveI hη₀ : η₀.IsHaarMeasure := inferInstance
    obtain ⟨ν₀, hν₀, hWeil⟩ := globalClassMeasure_exists_weil F η₀
    letI := hν₀
    letI (v : Place F) : LocallyCompactSpace (v.adicCompletion F) := finitePlace_locallyCompact F v
    letI (v : Place F) : SecondCountableTopology (v.adicCompletion F) := finitePlace_secondCountable F v
    letI (v : Place F) : SecondCountableTopology (v.adicCompletion F)ˣ :=
      Units.isEmbedding_val₀.secondCountableTopology
    letI (v : Place F) : MeasurableSpace (v.adicCompletion F)ˣ := borel _
    letI (v : Place F) : BorelSpace (v.adicCompletion F)ˣ := ⟨rfl⟩
    let μ₀ (v : Place F) : Measure (v.adicCompletion F)ˣ := Measure.haar
    letI (v : Place F) : (μ₀ v).IsHaarMeasure := inferInstance
    letI (v : Place F) : SigmaFinite (μ₀ v) := inferInstance
    letI : MeasurableSpace (InfiniteAdeleRing F)ˣ := borel _
    letI : BorelSpace (InfiniteAdeleRing F)ˣ := ⟨rfl⟩
    exact finiteHeckeIdealSummatory_tendsto_zero_of_nontrivial F η₀ ν₀ μ₀ hWeil χ hχ

end
end Masullo
