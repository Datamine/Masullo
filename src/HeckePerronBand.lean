import HeckePerronContour
import FiniteHeckeZeroFree

open Complex Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical Interval NumberField Topology

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

private abbrev K := normOneIdeleClass F
private abbrev Place := HeightOneSpectrum (𝓞 F)

local instance : MeasurableSpace (K F) := borel _
local instance : BorelSpace (K F) := ⟨rfl⟩
local instance : MeasurableSpace (Idele F) := borel _
local instance : BorelSpace (Idele F) := ⟨rfl⟩

variable (ν : Measure (K F)) [ν.IsHaarMeasure]
variable (η : Measure (Idele F)) [η.IsHaarMeasure]
variable [∀ v : Place F, MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : Place F, BorelSpace (v.adicCompletion F)ˣ]
  (μ : ∀ v : Place F, Measure (v.adicCompletion F)ˣ)
  [∀ v : Place F, (μ v).IsHaarMeasure] [∀ v : Place F, SigmaFinite (μ v)]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]
variable (hν : IsWeilQuotientMeasure (principalIdeles F) η Measure.count (globalClassMeasure F ν))

include μ hν in
/-- In the positive part of the verified zero-free band, the normal-form
finite Hecke continuation is analytic and nonzero except at the unique
possible norm-twist pole. In that case the pole has order minus one. -/
theorem manuscriptFiniteHecke_perron_band (χ : PontryaginDual (IdeleClass F))
    {t : ℝ} (ht : HasHeckeHeight F χ t)
    {L : ℂ → ℂ} (hL : MeromorphicNFOn L univ)
    (he : EqOn L (manuscriptFiniteHeckeEuler F χ) {z | 1 < z.re}) :
    ∃ B : ℝ, 1 ≤ B ∧
      (heckeNormOneRestriction F χ = 1 →
        meromorphicOrderAt L (1 + (t : ℂ) * Complex.I) = (-1 : ℤ)) ∧
      ∀ z : ℂ, 0 < z.re →
        1 - finiteHeckeZeroFreeNumerator /
          ((Module.finrank ℚ F : ℝ) ^ 4 * Real.log (B * (|z.im| + 3))) ≤ z.re →
        (heckeNormOneRestriction F χ ≠ 1 ∨ z ≠ 1 + (t : ℂ) * Complex.I) →
        AnalyticAt ℂ L z ∧ L z ≠ 0 := by
  let q : ℂ := (t : ℂ) * Complex.I
  let f (z : ℂ) := z + q
  let G := L ∘ f
  have hf (z : ℂ) : AnalyticAt ℂ f z := analyticAt_id.fun_add analyticAt_const
  have hG : MeromorphicOn G univ := fun z _ ↦
    (hL.meromorphicOn (f z) (mem_univ _)).comp_analyticAt (hf z)
  have heG : EqOn G (globalFiniteHeckeEuler F (heckeNormOneRestriction F χ)) {z | 1 < z.re} := by
    intro z hz
    have hre : (f z).re = z.re := by simp [f, q, Complex.add_re, Complex.mul_re]
    have hz' : 1 < (f z).re := by simpa [hre] using hz
    change L (f z) = _
    rw [he hz', manuscriptFiniteHeckeEuler_shift F χ ht]
    simp [f, q]
  have horder (z : ℂ) : meromorphicOrderAt G (z - q) = meromorphicOrderAt L z := by
    have hd : deriv f (z - q) ≠ 0 := by simp [f]
    change meromorphicOrderAt (L ∘ f) (z - q) = _
    rw [meromorphicOrderAt_comp_of_deriv_ne_zero (hf (z - q)) hd]
    simp [f]
  obtain ⟨hp, hreg⟩ := globalFiniteHecke_positive_pole_profile F η ν μ hν
    (heckeNormOneRestriction F χ) hG heG
  obtain ⟨B, hB, hZ⟩ := manuscriptFiniteHecke_zeroFree_region F ν η μ hν χ
  refine ⟨B, hB, fun h ↦ ?_, ?_⟩
  · simpa [q] using (horder (1 + q)).symm.trans (by simpa using hp h)
  · intro z hpos hband hcase
    have hZz := hZ L hL.meromorphicOn he z hband
    have hzre : (z - q).re = z.re := by simp [q, Complex.sub_re, Complex.mul_re]
    have hcase' : heckeNormOneRestriction F χ ≠ 1 ∨ z - q ≠ 1 := by
      rcases hcase with h | h
      · exact Or.inl h
      · exact Or.inr (by simpa [sub_eq_iff_eq_add, q] using h)
    have hN := hreg (z - q) (by simpa [hzre] using hpos) hcase'
    rw [horder z] at hN
    have hn := hL (mem_univ z)
    exact ⟨hn.meromorphicOrderAt_nonneg_iff_analyticAt.mp hN,
      hn.meromorphicOrderAt_eq_zero_iff.mp (le_antisymm hZz hN)⟩

include μ hν in
/-- The finite Hecke continuation satisfies the residue identities on
rectangles whose width is chosen using the maximum possible height.
The pole term is included precisely for a trivial norm-one restriction. -/
theorem manuscriptFiniteHecke_perron_residues (χ : PontryaginDual (IdeleClass F))
    {t : ℝ} (ht : HasHeckeHeight F χ t)
    {L : ℂ → ℂ} (hL : MeromorphicNFOn L univ)
    (he : EqOn L (manuscriptFiniteHeckeEuler F χ) {z | 1 < z.re}) :
    ∃ B : ℝ, 1 ≤ B ∧
      ∀ (x : ℝ) (s : ℂ), s.re = 1 → ∀ {δ κ T : ℝ},
        0 < δ → δ < 1 → 0 < κ → 0 < T →
        δ ≤ finiteHeckeZeroFreeNumerator /
          ((Module.finrank ℚ F : ℝ) ^ 4 * Real.log (B * (|s.im| + T + 3))) →
        let q : ℂ := 1 + (t : ℂ) * Complex.I
        let H (z : ℂ) := -logDeriv L (s + z)
        (heckeNormOneRestriction F χ ≠ 1 →
          rectIntegral (perronContourIntegrand x H) (-δ) κ (-T) T =
            (2 * Real.pi * Complex.I) * (-logDeriv L s)) ∧
        (heckeNormOneRestriction F χ = 1 → |t - s.im| < T →
          ∃ A : ℂ → ℂ,
            (∀ z ∈ [[-δ, κ]] ×ℂ [[-T, T]], AnalyticAt ℂ A (s + z)) ∧
            (∀ z ∈ [[-δ, κ]] ×ℂ [[-T, T]], s + z ≠ q →
              H z = A (s + z) + 1 / (s + z - q)) ∧
            rectIntegral (perronContourIntegrand x H) (-δ) κ (-T) T =
              (2 * Real.pi * Complex.I) *
                (if q = s then A s + (Real.log x : ℂ)
                  else -logDeriv L s + Complex.exp ((Real.log x : ℂ) * (q - s)) / (q - s))) := by
  obtain ⟨B, hB, hp, hreg⟩ := manuscriptFiniteHecke_perron_band F ν η μ hν χ ht hL he
  refine ⟨B, hB, fun x s hs δ κ T hδ hδ₁ hκ hT hwidth ↦ ?_⟩
  intro q H
  let R := [[-δ, κ]] ×ℂ [[-T, T]]
  have hleft : -δ < 0 := neg_lt_zero.mpr hδ
  have hbottom : -T < 0 := neg_lt_zero.mpr hT
  have hbox (z : ℂ) (hz : z ∈ R) :
      0 < (s + z).re ∧
      1 - finiteHeckeZeroFreeNumerator /
        ((Module.finrank ℚ F : ℝ) ^ 4 * Real.log (B * (|(s + z).im| + 3))) ≤ (s + z).re := by
    have hz' := Complex.mem_reProdIm.mp hz
    rw [uIcc_of_le (hleft.le.trans hκ.le), uIcc_of_le (hbottom.le.trans hT.le)] at hz'
    have him : |(s + z).im| ≤ |s.im| + T := by
      rw [Complex.add_im]
      exact (abs_add_le _ _).trans (add_le_add le_rfl (abs_le.mpr hz'.2))
    have hre : (s + z).re = 1 + z.re := by rw [Complex.add_re, hs]
    have hlog : 0 < Real.log (B * (|(s + z).im| + 3)) := by
      apply Real.log_pos
      have hl := le_mul_of_one_le_left (by positivity : 0 ≤ |(s + z).im| + 3) hB
      linarith [abs_nonneg (s + z).im]
    have hlog_le : Real.log (B * (|(s + z).im| + 3)) ≤ Real.log (B * (|s.im| + T + 3)) := by
      exact Real.log_le_log (by positivity) (mul_le_mul_of_nonneg_left (by linarith) (zero_le_one.trans hB))
    have hd : 0 < (Module.finrank ℚ F : ℝ) := by
      exact_mod_cast (Module.finrank_pos : 0 < Module.finrank ℚ F)
    have hratio : δ ≤ finiteHeckeZeroFreeNumerator /
        ((Module.finrank ℚ F : ℝ) ^ 4 * Real.log (B * (|(s + z).im| + 3))) := by
      exact hwidth.trans (div_le_div_of_nonneg_left finiteHeckeZeroFreeNumerator_pos.le
        (mul_pos (pow_pos hd _) hlog) (mul_le_mul_of_nonneg_left hlog_le (by positivity)))
    rw [hre]
    exact ⟨by linarith [hz'.1.1], by linarith [hz'.1.1]⟩
  constructor
  · intro hnontrivial
    exact rectIntegral_perron_negLogDeriv x s hleft hκ hbottom hT fun z hz ↦
      hreg _ (hbox z hz).1 (hbox z hz).2 (.inl hnontrivial)
  · intro htrivial hpheight
    have hqre : (q - s).re = 0 := by simp [q, hs, Complex.sub_re, Complex.add_re, Complex.mul_re]
    have hqim : (q - s).im = t - s.im := by simp [q, Complex.sub_im, Complex.add_im, Complex.mul_im]
    have hre : (q - s).re ∈ Ioo (-δ) κ := by rw [hqre]; exact ⟨hleft, hκ⟩
    have him : (q - s).im ∈ Ioo (-T) T := by rw [hqim]; exact abs_lt.mp hpheight
    exact rectIntegral_perron_negLogDeriv_simplePole x s q hleft hκ hbottom hT hre him
      (hL.meromorphicOn q (mem_univ _)) (hp htrivial) fun z hz hne ↦
        hreg _ (hbox z hz).1 (hbox z hz).2 (.inr hne)

include μ hν in
/-- For a pure norm twist the raw logarithmic derivative grows without
bound on a leftward real approach to its pole. -/
theorem manuscriptFiniteHecke_norm_logDeriv_diverges_left (χ : PontryaginDual (IdeleClass F))
    {t : ℝ} (ht : HasHeckeHeight F χ t)
    {L : ℂ → ℂ} (hL : MeromorphicNFOn L univ)
    (he : EqOn L (manuscriptFiniteHeckeEuler F χ) {z | 1 < z.re})
    (htrivial : heckeNormOneRestriction F χ = 1) :
    Tendsto (fun r : ℝ ↦ ‖logDeriv L (1 + (t : ℂ) * Complex.I - (r : ℂ))‖) (𝓝[>] 0) atTop := by
  let q : ℂ := 1 + (t : ℂ) * Complex.I
  have hqre : q.re = 1 := by simp [q, Complex.add_re, Complex.mul_re]
  have hqim : q.im = t := by simp [q, Complex.add_im, Complex.mul_im]
  obtain ⟨B, hB, hres⟩ := manuscriptFiniteHecke_perron_residues F ν η μ hν χ ht hL he
  let width := finiteHeckeZeroFreeNumerator /
    ((Module.finrank ℚ F : ℝ) ^ 4 * Real.log (B * (|q.im| + 1 + 3)))
  have hd : 0 < (Module.finrank ℚ F : ℝ) := by
    exact_mod_cast (Module.finrank_pos : 0 < Module.finrank ℚ F)
  have hlog : 0 < Real.log (B * (|q.im| + 1 + 3)) := by
    apply Real.log_pos
    have hh := le_mul_of_one_le_left (by positivity : 0 ≤ |q.im| + 1 + 3) hB
    linarith [abs_nonneg q.im]
  have hw : 0 < width := div_pos finiteHeckeZeroFreeNumerator_pos (mul_pos (pow_pos hd _) hlog)
  let δ := min (1 / 2 : ℝ) width
  have hδ : 0 < δ := lt_min (by norm_num) hw
  have hδ₁ : δ < 1 := (min_le_left _ _).trans_lt (by norm_num)
  obtain ⟨A, hA, hEq, _⟩ := (hres 1 q hqre hδ hδ₁ zero_lt_one zero_lt_one
    (min_le_right _ _)).2 htrivial (by simp [hqim])
  have hAq : AnalyticAt ℂ A q := by
    have h0 : (0 : ℂ) ∈ [[-δ, (1 : ℝ)]] ×ℂ [[(-1 : ℝ), (1 : ℝ)]] := by
      rw [Complex.mem_reProdIm, uIcc_of_le (by linarith), uIcc_of_le (by norm_num)]
      simp [hδ.le]
    simpa using hA 0 h0
  have hdiv := tendsto_norm_perronPole_from_left (H := fun w ↦ -logDeriv L w) hδ hAq (by
    intro r hr
    have hmem : (-(r : ℂ)) ∈ [[-δ, (1 : ℝ)]] ×ℂ [[(-1 : ℝ), (1 : ℝ)]] := by
      rw [Complex.mem_reProdIm, uIcc_of_le (by linarith), uIcc_of_le (by norm_num)]
      simp only [Complex.neg_re, Complex.ofReal_re, Complex.neg_im, Complex.ofReal_im,
        neg_zero, mem_Icc, neg_le_neg_iff]
      exact ⟨⟨hr.2.le, by linarith [hr.1]⟩, by norm_num⟩
    have hne : q + -(r : ℂ) ≠ q := by
      simpa using (show (r : ℂ) ≠ 0 by exact_mod_cast hr.1.ne')
    simpa only [sub_eq_add_neg] using hEq (-(r : ℂ)) hmem hne)
  simpa [q] using hdiv

end

end Masullo
