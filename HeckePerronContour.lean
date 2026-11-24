import RectangleResidue

open Complex Filter MeasureTheory Set
open scoped Interval Topology

namespace Masullo

noncomputable section

/-- Perron's integrand in the contour displacement variable. -/
def perronContourIntegrand (x : ℝ) (H : ℂ → ℂ) (z : ℂ) : ℂ :=
  H z * Complex.exp ((Real.log x : ℂ) * z) / z

private theorem rectIntegral_div_sub {f : ℂ → ℂ} {p : ℂ} {a b c d : ℝ}
    (ha : a < p.re) (hb : p.re < b) (hc : c < p.im) (hd : p.im < d)
    (hf : ∀ z ∈ [[a, b]] ×ℂ [[c, d]], AnalyticAt ℂ f z) :
    rectIntegral (fun z ↦ f z / (z - p)) a b c d = (2 * Real.pi * I) * f p := by
  simpa using rectIntegral_cauchy 0 ha hb hc hd hf

private theorem continuousOn_div_sub_rectEdges {f : ℂ → ℂ} {p : ℂ} {a b c d : ℝ}
    (hp : p ∉ rectEdges a b c d) (hf : ContinuousOn f (rectEdges a b c d)) :
    ContinuousOn (fun z ↦ f z / (z - p)) (rectEdges a b c d) :=
  hf.div (continuous_id.sub continuous_const).continuousOn
    (fun _ hz ↦ sub_ne_zero.mpr (fun he ↦ hp (he ▸ hz)))

/-- The pole at the Perron kernel's origin is the only residue for a
holomorphic logarithmic derivative. -/
theorem rectIntegral_perron_holomorphic {H : ℂ → ℂ} (x : ℝ) {a b c d : ℝ}
    (ha : a < 0) (hb : 0 < b) (hc : c < 0) (hd : 0 < d)
    (hH : ∀ z ∈ [[a, b]] ×ℂ [[c, d]], AnalyticAt ℂ H z) :
    rectIntegral (perronContourIntegrand x H) a b c d =
      (2 * Real.pi * I) * H 0 := by
  have hE (z : ℂ) : AnalyticAt ℂ (fun w : ℂ ↦ Complex.exp ((Real.log x : ℂ) * w)) z := by
    fun_prop
  unfold perronContourIntegrand
  simpa using
    rectIntegral_div_sub (p := 0) (by simpa) (by simpa) (by simpa) (by simpa)
      (fun z hz ↦ (hH z hz).fun_mul (hE z))

/-- For a pole distinct from the Perron kernel's origin the two residues
combine to the divided difference of the exponential. -/
theorem rectIntegral_perron_distinct {H A : ℂ → ℂ} (x : ℝ) {p : ℂ} {a b c d : ℝ}
    (ha : a < 0) (hb : 0 < b) (hc : c < 0) (hd : 0 < d)
    (hp : p ≠ 0) (hap : a < p.re) (hbp : p.re < b) (hcp : c < p.im) (hdp : p.im < d)
    (hA : ∀ z ∈ [[a, b]] ×ℂ [[c, d]], AnalyticAt ℂ A z)
    (hH : EqOn H (fun z ↦ A z + 1 / (z - p)) (rectEdges a b c d)) :
    rectIntegral (perronContourIntegrand x H) a b c d =
      (2 * Real.pi * I) * (A 0 + (Complex.exp ((Real.log x : ℂ) * p) - 1) / p) := by
  let E (z : ℂ) := Complex.exp ((Real.log x : ℂ) * z)
  let F (z : ℂ) := perronContourIntegrand x A z
  let P (z : ℂ) := E z / (z - p)
  let Q (z : ℂ) := E z / (z - 0)
  have hE (z : ℂ) : AnalyticAt ℂ E z := by dsimp [E]; fun_prop
  have hEc : ContinuousOn E (rectEdges a b c d) := fun z _ ↦ (hE z).continuousAt.continuousWithinAt
  have h0edge : (0 : ℂ) ∉ rectEdges a b c d :=
    point_notMem_rectEdges (by simpa using ha.ne) (by simpa using hb.ne')
      (by simpa using hc.ne) (by simpa using hd.ne')
  have hpedge : p ∉ rectEdges a b c d := point_notMem_rectEdges hap.ne hbp.ne' hcp.ne hdp.ne'
  have hAc : ContinuousOn A (rectEdges a b c d) :=
    fun z hz ↦ (hA z (rectEdges_subset hz)).continuousAt.continuousWithinAt
  have hF : ContinuousOn F (rectEdges a b c d) := by
    simpa [F, perronContourIntegrand, E] using
      continuousOn_div_sub_rectEdges h0edge (hAc.mul hEc)
  have hP : ContinuousOn P (rectEdges a b c d) := continuousOn_div_sub_rectEdges hpedge hEc
  have hQ : ContinuousOn Q (rectEdges a b c d) := continuousOn_div_sub_rectEdges h0edge hEc
  have he : EqOn (perronContourIntegrand x H) (fun z ↦ F z + p⁻¹ * (P z - Q z))
      (rectEdges a b c d) := by
    intro z hz
    have hz₀ : z ≠ 0 := fun h ↦ h0edge (h ▸ hz)
    have hzp : z - p ≠ 0 := sub_ne_zero.mpr (fun h ↦ hpedge (h ▸ hz))
    simp only [perronContourIntegrand, F, P, Q, sub_zero, E, hH hz]
    field_simp
    ring
  have hPQ : ContinuousOn (fun z ↦ p⁻¹ * (P z - Q z)) (rectEdges a b c d) :=
    continuousOn_const.mul (hP.sub hQ)
  rw [rectIntegral_congr_edges he, rectIntegral_add hF hPQ, rectIntegral_const_mul]
  have hs : rectIntegral (fun z ↦ P z - Q z) a b c d =
      rectIntegral P a b c d - rectIntegral Q a b c d := by
    have hes : (fun z ↦ P z - Q z) = (fun z ↦ P z + (-1 : ℂ) * Q z) := by
      funext z
      ring
    have hNeg : ContinuousOn (fun z ↦ (-1 : ℂ) * Q z) (rectEdges a b c d) :=
      continuousOn_const.mul hQ
    rw [hes, rectIntegral_add hP hNeg, rectIntegral_const_mul]
    ring
  rw [hs, rectIntegral_perron_holomorphic x ha hb hc hd hA,
    rectIntegral_div_sub hap hbp hcp hdp (fun z _ ↦ hE z),
    rectIntegral_div_sub (p := 0) (by simpa) (by simpa) (by simpa) (by simpa) (fun z _ ↦ hE z)]
  simp only [E, mul_zero, Complex.exp_zero]
  ring

/-- At coincidence the term from the double pole is the derivative of
the exponential, namely the real logarithm of the cutoff. -/
theorem rectIntegral_perron_coincident {H A : ℂ → ℂ} (x : ℝ) {a b c d : ℝ}
    (ha : a < 0) (hb : 0 < b) (hc : c < 0) (hd : 0 < d)
    (hA : ∀ z ∈ [[a, b]] ×ℂ [[c, d]], AnalyticAt ℂ A z)
    (hH : EqOn H (fun z ↦ A z + 1 / z) (rectEdges a b c d)) :
    rectIntegral (perronContourIntegrand x H) a b c d =
      (2 * Real.pi * I) * (A 0 + (Real.log x : ℂ)) := by
  let E (z : ℂ) := Complex.exp ((Real.log x : ℂ) * z)
  let F (z : ℂ) := perronContourIntegrand x A z
  let Q (z : ℂ) := E z / (z - 0) ^ 2
  have hE (z : ℂ) : AnalyticAt ℂ E z := by dsimp [E]; fun_prop
  have hEc : ContinuousOn E (rectEdges a b c d) := fun z _ ↦ (hE z).continuousAt.continuousWithinAt
  have h0edge : (0 : ℂ) ∉ rectEdges a b c d :=
    point_notMem_rectEdges (by simpa using ha.ne) (by simpa using hb.ne')
      (by simpa using hc.ne) (by simpa using hd.ne')
  have hAc : ContinuousOn A (rectEdges a b c d) :=
    fun z hz ↦ (hA z (rectEdges_subset hz)).continuousAt.continuousWithinAt
  have hF : ContinuousOn F (rectEdges a b c d) := by
    simpa [F, perronContourIntegrand, E] using
      continuousOn_div_sub_rectEdges h0edge (hAc.mul hEc)
  have hQ : ContinuousOn Q (rectEdges a b c d) := hEc.div
    ((continuous_id.sub continuous_const).pow 2).continuousOn
    (fun z hz ↦ pow_ne_zero _ (sub_ne_zero.mpr fun he ↦ h0edge (he ▸ hz)))
  have he : EqOn (perronContourIntegrand x H) (fun z ↦ F z + Q z) (rectEdges a b c d) := by
    intro z hz
    have hz₀ : z ≠ 0 := fun h ↦ h0edge (h ▸ hz)
    simp only [perronContourIntegrand, F, Q, sub_zero, E, hH hz]
    field_simp
  have hder : deriv E 0 = (Real.log x : ℂ) := by
    have hExp := (((hasDerivAt_id' (0 : ℂ)).const_mul (Real.log x : ℂ)).cexp).deriv
    simpa [E] using hExp
  have hC : rectIntegral Q a b c d = (2 * Real.pi * I) * (Real.log x : ℂ) := by
    simpa [Q, iteratedDeriv_one, hder] using
      rectIntegral_cauchy (p := 0) 1 (by simpa) (by simpa) (by simpa) (by simpa) (fun z _ ↦ hE z)
  rw [rectIntegral_congr_edges he, rectIntegral_add hF hQ,
    rectIntegral_perron_holomorphic x ha hb hc hd hA, hC]
  ring

theorem analyticAt_neg_logDeriv {f : ℂ → ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f z) (hne : f z ≠ 0) :
    AnalyticAt ℂ (fun w ↦ -logDeriv f w) z := by
  simpa only [logDeriv_apply] using (hf.deriv.fun_div hf hne).fun_neg

/-- Subtracting the contribution of a simple pole from the negative
logarithmic derivative gives a holomorphic remainder on the zero-free set. -/
theorem exists_analytic_negLogDeriv_simplePole_remainder {L : ℂ → ℂ} {S : Set ℂ} {q : ℂ}
    (hm : MeromorphicAt L q) (ho : meromorphicOrderAt L q = (-1 : ℤ))
    (hL : ∀ w ∈ S, w ≠ q → AnalyticAt ℂ L w ∧ L w ≠ 0) :
    ∃ A : ℂ → ℂ, (∀ w ∈ S, AnalyticAt ℂ A w) ∧
      ∀ w ∈ S, w ≠ q → -logDeriv L w = A w + 1 / (w - q) := by
  classical
  obtain ⟨g, hg, hg₀, he⟩ := (meromorphicOrderAt_eq_int_iff hm).mp ho
  let G (w : ℂ) := if w = q then g q else L w * (w - q)
  have hGq : AnalyticAt ℂ G q := by
    apply hg.congr
    filter_upwards [eventually_nhdsWithin_iff.mp he] with w hw
    by_cases h : w = q
    · subst w
      simp [G]
    · have hw' := hw h
      rw [show G w = L w * (w - q) by simp [G, h], hw']
      simp only [zpow_neg, zpow_one, smul_eq_mul]
      field_simp [sub_ne_zero.mpr h]
  have hGoff {w : ℂ} (hwq : w ≠ q) :
      G =ᶠ[𝓝 w] (fun z ↦ L z * (z - q)) := by
    filter_upwards [eventually_ne_nhds hwq] with z hz
    simp [G, hz]
  let A (w : ℂ) := -logDeriv G w
  refine ⟨A, ?_, ?_⟩
  · intro w hw
    by_cases h : w = q
    · subst w
      exact analyticAt_neg_logDeriv hGq (by simpa [G] using hg₀)
    · obtain ⟨hAn, hne⟩ := hL w hw h
      have hAnG : AnalyticAt ℂ G w :=
        (hAn.fun_mul (analyticAt_id.sub analyticAt_const)).congr (hGoff h).symm
      exact analyticAt_neg_logDeriv hAnG (by simp [G, h, hne, sub_ne_zero.mpr h])
  · intro w hw h
    obtain ⟨hAn, hne⟩ := hL w hw h
    have heq : logDeriv G w = logDeriv (fun z ↦ L z * (z - q)) w := by
      simp only [logDeriv_apply]
      rw [(hGoff h).deriv_eq, (hGoff h).eq_of_nhds]
    have hlog : logDeriv G w = logDeriv L w + 1 / (w - q) := by
      rw [heq, logDeriv_mul (f := L) (g := fun z ↦ z - q) _
        hne (sub_ne_zero.mpr h) hAn.differentiableAt (differentiableAt_id.sub_const _)]
      simp [logDeriv_apply]
    dsimp only [A]
    rw [hlog]
    ring

/-- The contour of a translated negative logarithmic derivative through
a zero-free rectangle with no pole. -/
theorem rectIntegral_perron_negLogDeriv {L : ℂ → ℂ} (x : ℝ) (s : ℂ) {a b c d : ℝ}
    (ha : a < 0) (hb : 0 < b) (hc : c < 0) (hd : 0 < d)
    (hL : ∀ z ∈ [[a, b]] ×ℂ [[c, d]], AnalyticAt ℂ L (s + z) ∧ L (s + z) ≠ 0) :
    rectIntegral (perronContourIntegrand x (fun z ↦ -logDeriv L (s + z))) a b c d =
      (2 * Real.pi * I) * (-logDeriv L s) := by
  have hA (z : ℂ) (hz : z ∈ [[a, b]] ×ℂ [[c, d]]) :
      AnalyticAt ℂ (fun w ↦ -logDeriv L (s + w)) z :=
    (analyticAt_neg_logDeriv (hL z hz).1 (hL z hz).2).comp
      (analyticAt_const.fun_add analyticAt_id)
  simpa using rectIntegral_perron_holomorphic x ha hb hc hd hA

/-- The rectangular contour through a zero-free band with one simple pole.
When its displacement reaches zero, the two residues are replaced by
the regular part at the pole plus the cutoff logarithm. -/
theorem rectIntegral_perron_negLogDeriv_simplePole {L : ℂ → ℂ} (x : ℝ) (s q : ℂ)
    {a b c d : ℝ} (ha : a < 0) (hb : 0 < b) (hc : c < 0) (hd : 0 < d)
    (hpRe : (q - s).re ∈ Ioo a b) (hpIm : (q - s).im ∈ Ioo c d)
    (hm : MeromorphicAt L q) (ho : meromorphicOrderAt L q = (-1 : ℤ))
    (hL : ∀ z ∈ [[a, b]] ×ℂ [[c, d]], s + z ≠ q → AnalyticAt ℂ L (s + z) ∧ L (s + z) ≠ 0) :
    ∃ A : ℂ → ℂ,
      (∀ z ∈ [[a, b]] ×ℂ [[c, d]], AnalyticAt ℂ A (s + z)) ∧
      (∀ z ∈ [[a, b]] ×ℂ [[c, d]], s + z ≠ q →
        -logDeriv L (s + z) = A (s + z) + 1 / (s + z - q)) ∧
      rectIntegral (perronContourIntegrand x (fun z ↦ -logDeriv L (s + z))) a b c d =
        (2 * Real.pi * I) *
          (if q = s then A s + (Real.log x : ℂ)
            else -logDeriv L s + Complex.exp ((Real.log x : ℂ) * (q - s)) / (q - s)) := by
  let R := [[a, b]] ×ℂ [[c, d]]
  let S := (fun z : ℂ ↦ s + z) '' R
  have hLS : ∀ w ∈ S, w ≠ q → AnalyticAt ℂ L w ∧ L w ≠ 0 := by
    rintro w ⟨z, hz, rfl⟩ h
    exact hL z hz h
  obtain ⟨A, hA, hEq⟩ := exists_analytic_negLogDeriv_simplePole_remainder hm ho hLS
  have hMem (z : ℂ) (hz : z ∈ R) : s + z ∈ S := ⟨z, hz, rfl⟩
  have hAS (z : ℂ) (hz : z ∈ R) : AnalyticAt ℂ A (s + z) := hA _ (hMem z hz)
  have hShift (z : ℂ) (hz : z ∈ R) : AnalyticAt ℂ (fun w ↦ A (s + w)) z :=
    (hAS z hz).comp (analyticAt_const.fun_add analyticAt_id)
  refine ⟨A, hAS, fun z hz ↦ hEq _ (hMem z hz), ?_⟩
  have hpEdge : q - s ∉ rectEdges a b c d :=
    point_notMem_rectEdges hpRe.1.ne hpRe.2.ne' hpIm.1.ne hpIm.2.ne'
  have hEdge : EqOn (fun z ↦ -logDeriv L (s + z))
      (fun z ↦ A (s + z) + 1 / (z - (q - s))) (rectEdges a b c d) := by
    intro z hz
    have hq : s + z ≠ q := by
      intro he
      have hp : z = q - s := by linear_combination he
      exact hpEdge (hp ▸ hz)
    convert hEq (s + z) (hMem z (rectEdges_subset hz)) hq using 2
    ring
  by_cases hqs : q = s
  · simp only [hqs, ite_true]
    simpa only [add_zero] using
      rectIntegral_perron_coincident x ha hb hc hd hShift (by simpa [hqs] using hEdge)
  · rw [ite_eq_right hqs, rectIntegral_perron_distinct x ha hb hc hd (sub_ne_zero.mpr hqs)
      hpRe.1 hpRe.2 hpIm.1 hpIm.2 hShift hEdge]
    have h0 : (0 : ℂ) ∈ R := Complex.mem_reProdIm.mpr
      ⟨mem_uIcc_of_le (by simpa using ha.le) (by simpa using hb.le),
       mem_uIcc_of_le (by simpa using hc.le) (by simpa using hd.le)⟩
    have hAt := hEq (s + 0) (hMem 0 h0) (by simpa using Ne.symm hqs)
    simp only [add_zero] at hAt ⊢
    rw [hAt, show s - q = -(q - s) by ring, div_neg, sub_div]
    ring

private theorem norm_perronContourIntegrand (x : ℝ) (H : ℂ → ℂ) (z : ℂ) :
    ‖perronContourIntegrand x H z‖ = ‖H z‖ * Real.exp (Real.log x * z.re) / ‖z‖ := by
  rw [perronContourIntegrand, norm_div, norm_mul, Complex.norm_exp, Complex.mul_re]
  simp

/-- The simple-pole term on the left edge is bounded by the inverse of
the horizontal distance from the pole. -/
theorem norm_perronPoleSubtracted_left_le {H A : ℂ → ℂ} {p : ℂ}
    {δ M y : ℝ} (hδ : 0 < δ) (hp : p.re = 0)
    (hEq : H ((-δ : ℝ) + (y : ℂ) * I) = A ((-δ : ℝ) + (y : ℂ) * I) +
      1 / ((-δ : ℝ) + (y : ℂ) * I - p))
    (hA : ‖A ((-δ : ℝ) + (y : ℂ) * I)‖ ≤ M) :
    ‖H ((-δ : ℝ) + (y : ℂ) * I)‖ ≤ M + δ⁻¹ := by
  let z : ℂ := (-δ : ℝ) + (y : ℂ) * I
  have hre : (z - p).re = -δ := by simp [z, Complex.sub_re, Complex.add_re, Complex.mul_re, hp]
  have hdist : δ ≤ ‖z - p‖ := by
    simpa [hre, abs_of_pos hδ] using Complex.abs_re_le_norm (z - p)
  change ‖H z‖ ≤ M + δ⁻¹
  rw [hEq]
  exact (norm_add_le _ _).trans (add_le_add hA (by
    rw [one_div, norm_inv]
    exact inv_anti₀ hδ hdist))

/-- A pole cannot be included in a compact uniform bound for the raw
logarithmic derivative. Its norm diverges even along a horizontal approach
from the left. -/
theorem tendsto_norm_perronPole_from_left {H A : ℂ → ℂ} {q : ℂ} {δ₀ : ℝ}
    (hδ₀ : 0 < δ₀) (hA : AnalyticAt ℂ A q)
    (hEq : ∀ δ ∈ Ioo (0 : ℝ) δ₀, H (q - (δ : ℂ)) =
      A (q - (δ : ℂ)) + 1 / ((q - (δ : ℂ)) - q)) :
    Tendsto (fun δ : ℝ ↦ ‖H (q - (δ : ℂ))‖) (𝓝[>] 0) atTop := by
  have ht : Tendsto (fun δ : ℝ ↦ q - (δ : ℂ)) (𝓝[>] 0) (𝓝 q) := by
    have hct : Continuous (fun δ : ℝ ↦ q - (δ : ℂ)) := continuous_const.sub Complex.continuous_ofReal
    simpa using tendsto_nhdsWithin_of_tendsto_nhds (s := Ioi 0) (hct.continuousAt (x := 0))
  have hBound : ∀ᶠ δ : ℝ in 𝓝[>] 0, ‖A (q - (δ : ℂ))‖ < ‖A q‖ + 1 :=
    (hA.continuousAt.tendsto.comp ht).norm.eventually_lt_const (by linarith)
  refine tendsto_atTop.mpr fun M ↦ ?_
  filter_upwards [Ioo_mem_nhdsGT hδ₀, hBound,
    tendsto_inv_nhdsGT_zero.eventually_ge_atTop (M + ‖A q‖ + 1)] with δ hδ hB hI
  have hnorm : ‖(1 : ℂ) / ((q - (δ : ℂ)) - q)‖ = δ⁻¹ := by
    have hsub : (q - (δ : ℂ)) - q = -(δ : ℂ) := by ring
    rw [hsub, one_div, norm_inv, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ.1]
  have hsub := norm_sub_le (H (q - (δ : ℂ))) (A (q - (δ : ℂ)))
  rw [hEq δ hδ, add_sub_cancel_left] at hsub
  have hres : δ⁻¹ ≤ ‖H (q - (δ : ℂ))‖ + ‖A (q - (δ : ℂ))‖ := by
    simpa only [← hEq δ hδ, hnorm] using hsub
  linarith

/-- A left edge at distance `δ` from the origin gains the factor
`exp (-δ * log x)`. The denominator is bounded uniformly by `δ`. -/
theorem norm_perronContour_left_le {H : ℂ → ℂ} (x : ℝ) {δ T M : ℝ}
    (hδ : 0 < δ) (hT : 0 < T) (hM : 0 ≤ M)
    (hH : ∀ y ∈ Icc (-T) T, ‖H ((-δ : ℝ) + (y : ℂ) * I)‖ ≤ M) :
    ‖∫ y in -T..T, perronContourIntegrand x H ((-δ : ℝ) + (y : ℂ) * I)‖ ≤
      (M * Real.exp (Real.log x * (-δ)) / δ) * (2 * T) := by
  have hle : -T ≤ T := by linarith
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun y : ℝ ↦ perronContourIntegrand x H ((-δ : ℝ) + (y : ℂ) * I))
    (a := -T) (b := T) (C := M * Real.exp (Real.log x * (-δ)) / δ) (by
      intro y hy
      rw [uIoc_of_le hle] at hy
      let z : ℂ := (-δ : ℝ) + (y : ℂ) * I
      have hre : z.re = -δ := by simp [z, Complex.add_re, Complex.mul_re]
      have hz : δ ≤ ‖z‖ := by simpa [hre, abs_of_pos hδ] using Complex.abs_re_le_norm z
      change ‖perronContourIntegrand x H z‖ ≤ _
      rw [norm_perronContourIntegrand, hre]
      have hbound : ‖H z‖ ≤ M := hH y ⟨hy.1.le, hy.2⟩
      gcongr)
  simpa [show T - -T = 2 * T by ring, abs_of_pos (by positivity : 0 < 2 * T)] using h

/-- On a horizontal edge the denominator is at least the height. -/
theorem norm_perronContour_horizontal_le {H : ℂ → ℂ} {x a b t M : ℝ}
    (hx : 1 ≤ x) (hab : a ≤ b) (ht : 0 < |t|) (hM : 0 ≤ M)
    (hH : ∀ u ∈ Icc a b, ‖H ((u : ℂ) + (t : ℂ) * I)‖ ≤ M) :
    ‖∫ u in a..b, perronContourIntegrand x H ((u : ℂ) + (t : ℂ) * I)‖ ≤
      (M * Real.exp (Real.log x * b) / |t|) * (b - a) := by
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun u : ℝ ↦ perronContourIntegrand x H ((u : ℂ) + (t : ℂ) * I))
    (a := a) (b := b) (C := M * Real.exp (Real.log x * b) / |t|) (by
      intro u hu
      rw [uIoc_of_le hab] at hu
      let z : ℂ := (u : ℂ) + (t : ℂ) * I
      have hre : z.re = u := by simp [z, Complex.add_re, Complex.mul_re]
      have him : z.im = t := by simp [z, Complex.add_im, Complex.mul_im]
      have hz : |t| ≤ ‖z‖ := by simpa [him] using Complex.abs_im_le_norm z
      change ‖perronContourIntegrand x H z‖ ≤ _
      rw [norm_perronContourIntegrand, hre]
      have hbound : ‖H z‖ ≤ M := hH u ⟨hu.1.le, hu.2⟩
      gcongr
      exact hu.2)
  simpa [abs_of_nonneg (sub_nonneg.mpr hab)] using h

/-- The difference between the normalized right edge and the sum of the
residues is bounded by the remaining three edges. -/
theorem norm_perronContour_shift_le {H : ℂ → ℂ} {r : ℂ} {x δ κ T M N : ℝ}
    (hx : 1 ≤ x) (hδ : 0 < δ) (hκ : 0 < κ) (hT : 0 < T) (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hRes : rectIntegral (perronContourIntegrand x H) (-δ) κ (-T) T =
      (2 * Real.pi * I) * r)
    (hLeft : ∀ y ∈ Icc (-T) T, ‖H ((-δ : ℝ) + (y : ℂ) * I)‖ ≤ M)
    (hTop : ∀ u ∈ Icc (-δ) κ, ‖H ((u : ℂ) + (T : ℂ) * I)‖ ≤ N)
    (hBottom : ∀ u ∈ Icc (-δ) κ, ‖H ((u : ℂ) + (-T : ℝ) * I)‖ ≤ N) :
    ‖((∫ y in -T..T, perronContourIntegrand x H ((κ : ℂ) + (y : ℂ) * I)) /
        (2 * (Real.pi : ℂ))) - r‖ ≤
      ((M * Real.exp (Real.log x * (-δ)) / δ) * (2 * T) +
        2 * ((N * Real.exp (Real.log x * κ) / T) * (κ + δ))) / (2 * Real.pi) := by
  let F := perronContourIntegrand x H
  let left := ∫ y in -T..T, F ((-δ : ℝ) + (y : ℂ) * I)
  let right := ∫ y in -T..T, F ((κ : ℂ) + (y : ℂ) * I)
  let top := ∫ u in -δ..κ, F ((u : ℂ) + (T : ℂ) * I)
  let bottom := ∫ u in -δ..κ, F ((u : ℂ) + (-T : ℝ) * I)
  let D : ℂ := 2 * (Real.pi : ℂ)
  have hD : D ≠ 0 := by
    dsimp only [D]
    exact mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hEdges : bottom - top + I * right - I * left = D * I * r := by
    rwa [rectIntegral_eq_edges] at hRes
  have hRel : I * right - D * I * r = I * left - (bottom - top) := by
    linear_combination hEdges
  have hEq : right - D * r = left + I * (bottom - top) := by
    have h := congrArg ((-I) * ·) hRel
    simp only [mul_sub, neg_mul, ← mul_assoc, Complex.I_mul_I, neg_neg, one_mul] at h
    have hi : I * D * I * r = -(D * r) := calc
      _ = D * (I * I) * r := by ring
      _ = _ := by simp
    simp only [mul_assoc] at h hi
    rw [hi, neg_neg] at h
    linear_combination h
  have hl := norm_perronContour_left_le x hδ hT hM hLeft
  have hh : -δ ≤ κ := by linarith
  have ht := norm_perronContour_horizontal_le hx hh (abs_pos.mpr hT.ne') hN hTop
  have hb := norm_perronContour_horizontal_le hx hh (abs_pos.mpr (neg_ne_zero.mpr hT.ne')) hN hBottom
  have hNsum : ‖right - D * r‖ ≤
      (M * Real.exp (Real.log x * (-δ)) / δ) * (2 * T) +
        2 * ((N * Real.exp (Real.log x * κ) / T) * (κ + δ)) := by
    rw [hEq]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Complex.norm_I, one_mul]
    refine (add_le_add hl (norm_sub_le _ _)).trans ?_
    rw [abs_of_pos hT, sub_neg_eq_add] at ht
    rw [abs_neg, abs_of_pos hT, sub_neg_eq_add] at hb
    linarith
  change ‖right / D - r‖ ≤ _
  rw [show right / D - r = (right - D * r) / D by field_simp, norm_div]
  have hDnorm : ‖D‖ = 2 * Real.pi := by
    simp [D, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [hDnorm]
  exact div_le_div_of_nonneg_right hNsum (by positivity)

end

end Masullo
