import HeckePerronBand

open Complex Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical Interval NumberField Topology

namespace Masullo

noncomputable section

abbrev heckePerronBandWidth (A B y : ℝ) : ℝ := A / Real.log (B * (y + 3))

private theorem perronBand_log_pos {B y : ℝ} (hB : 1 ≤ B) (hy : 0 ≤ y) :
    0 < Real.log (B * (y + 3)) := by
  apply Real.log_pos
  have h := le_mul_of_one_le_left (by positivity : 0 ≤ y + 3) hB
  linarith

private theorem perronBandWidth_decreasing {A B : ℝ} (hA : 0 < A) (hB : 1 ≤ B) :
    AntitoneOn (heckePerronBandWidth A B) (Ici 0) := by
  intro y hy z _ hyz
  apply div_le_div_of_nonneg_left hA.le (perronBand_log_pos hB hy)
  exact Real.log_le_log (mul_pos (zero_lt_one.trans_le hB) (by linarith [show 0 ≤ y from hy]))
    (mul_le_mul_of_nonneg_left (by linarith) (zero_le_one.trans hB))

private theorem hasDerivAt_perronBandWidth {A B y : ℝ} (hB : 1 ≤ B) (hy : 0 ≤ y) :
    HasDerivAt (heckePerronBandWidth A B) (-A * ((y + 3)⁻¹ * (Real.log (B * (y + 3)))⁻¹ ^ 2)) y := by
  have hB₀ := zero_lt_one.trans_le hB
  have hy₀ : 0 < y + 3 := by linarith
  have h := ((hasDerivAt_id' y).add_const (3 : ℝ)).const_mul B
  have hl := h.log (mul_ne_zero hB₀.ne' hy₀.ne')
  have hd := (hasDerivAt_const y A).div hl (perronBand_log_pos hB hy).ne'
  convert hd using 1 <;> try rfl
  simp only [mul_one, zero_mul, zero_sub]
  field_simp [hB₀.ne', hy₀.ne', (perronBand_log_pos hB hy).ne']

private theorem tendsto_deriv_perronBandWidth (A : ℝ) {B : ℝ} (hB : 1 ≤ B) :
    Tendsto (deriv (heckePerronBandWidth A B)) atTop (𝓝 0) := by
  have hB₀ := zero_lt_one.trans_le hB
  have hy : Tendsto (fun y : ℝ ↦ y + 3) atTop atTop := tendsto_atTop_add_const_right _ _ tendsto_id
  have harg : Tendsto (fun y : ℝ ↦ B * (y + 3)) atTop atTop := hy.const_mul_atTop hB₀
  have hi := tendsto_inv_atTop_zero.comp hy
  have hj := tendsto_inv_atTop_zero.comp (Real.tendsto_log_atTop.comp harg)
  have ht : Tendsto (fun y : ℝ ↦ -A * ((y + 3)⁻¹ * (Real.log (B * (y + 3)))⁻¹ ^ 2))
      atTop (𝓝 0) := by
    simpa using (hi.mul (hj.pow 2)).const_mul (-A)
  refine ht.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with y hy
  exact (hasDerivAt_perronBandWidth (A := A) hB hy).deriv.symm

private theorem perronBandWidth_inv_le {A B : ℝ} (hA : 0 < A) (hB : 1 ≤ B) :
    ∃ D W : ℝ, 0 ≤ D ∧ ∀ y ≥ W, (heckePerronBandWidth A B y)⁻¹ ≤ D * Real.log y := by
  have hB₀ := zero_lt_one.trans_le hB
  refine ⟨(Real.log (B * 4) + 1) / A, max 1 (Real.exp 1), ?_, fun y hy ↦ ?_⟩
  · have hlog := perronBand_log_pos hB (y := 1) (by norm_num)
    change 0 ≤ (Real.log (B * 4) + 1) / A
    norm_num at hlog
    positivity
  have hy₁ := (le_max_left _ _).trans hy
  have hy₀ := zero_lt_one.trans_le hy₁
  have hl : 1 ≤ Real.log y := by
    simpa using Real.log_le_log (Real.exp_pos 1) ((le_max_right _ _).trans hy)
  have hlog := perronBand_log_pos hB (y := 1) (by norm_num)
  norm_num at hlog
  have hh : Real.log (B * (y + 3)) ≤ Real.log (B * 4) + Real.log y := by
    rw [← Real.log_mul (mul_pos hB₀ (by norm_num)).ne' hy₀.ne']
    apply Real.log_le_log (by positivity)
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (by linarith) hB₀.le
  have hbound : Real.log (B * (y + 3)) ≤ (Real.log (B * 4) + 1) * Real.log y := by
    nlinarith [mul_nonneg hlog.le (sub_nonneg.mpr hl)]
  rw [heckePerronBandWidth, inv_div]
  calc
    _ ≤ ((Real.log (B * 4) + 1) * Real.log y) / A := div_le_div_of_nonneg_right hbound hA.le
    _ = _ := by ring

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
/-- On a narrower logarithmic band the finite Hecke derivative satisfies
the large-height logarithmic bound. On the low-height strip the same
continuation has a compact bound after subtracting the possible pole. -/
theorem exists_manuscriptFiniteHecke_perron_derivative_bounds (χ : PontryaginDual (IdeleClass F))
    {t : ℝ} (ht : HasHeckeHeight F χ t) :
    ∃ (L : ℂ → ℂ) (A B C M Y : ℝ),
      MeromorphicNFOn L univ ∧ EqOn L (manuscriptFiniteHeckeEuler F χ) {z | 1 < z.re} ∧
      1 ≤ B ∧ 0 < A ∧ A ≤ finiteHeckeZeroFreeNumerator / (Module.finrank ℚ F : ℝ) ^ 4 ∧
      0 ≤ C ∧ 0 ≤ M ∧ 1 + |t| ≤ Y ∧
      (∀ z : ℂ, Y ≤ |z.im| → |z.re - 1| ≤ heckePerronBandWidth A B |z.im| / 2 →
        ‖logDeriv L z‖ ≤ C * Real.log |z.im| ^ 2) ∧
      ∀ z : ℂ, |z.im| ≤ Y → |z.re - 1| ≤ heckePerronBandWidth A B Y / 2 →
        z ≠ 1 + (t : ℂ) * I → ‖logDeriv L z‖ ≤ M + ‖(z - (1 + (t : ℂ) * I))⁻¹‖ := by
  obtain ⟨L, hL, heL, hhigh⟩ := exists_manuscriptFiniteHecke_logDeriv_of_zeroFree F ν η μ hν χ
  obtain ⟨B, hB, hPole, hreg⟩ := manuscriptFiniteHecke_perron_band F ν η μ hν χ ht hL heL
  let D : ℝ := Module.finrank ℚ F
  let A := min (Real.log 3 / 2) (finiteHeckeZeroFreeNumerator / D ^ 4)
  let e := heckePerronBandWidth A B
  let q : ℂ := 1 + (t : ℂ) * I
  have hD : 0 < D := by dsimp [D]; exact_mod_cast (Module.finrank_pos : 0 < Module.finrank ℚ F)
  have hA : 0 < A := lt_min (half_pos (Real.log_pos (by norm_num)))
    (div_pos finiteHeckeZeroFreeNumerator_pos (pow_pos hD _))
  have hAD : A ≤ finiteHeckeZeroFreeNumerator / D ^ 4 := min_le_right _ _
  have hAn {y : ℝ} (hy : 0 ≤ y) : 0 < e y ∧ e y ≤ 1 / 2 := by
    have hlog := perronBand_log_pos hB hy
    have hlog' : Real.log 3 ≤ Real.log (B * (y + 3)) := by
      apply Real.log_le_log (by norm_num)
      exact (by linarith : 3 ≤ y + 3).trans (le_mul_of_one_le_left (by positivity) hB)
    refine ⟨div_pos hA hlog, (div_le_iff₀ hlog).mpr ?_⟩
    exact (min_le_left _ _).trans (by linarith)
  have hWidth {y : ℝ} (hy : 0 ≤ y) : e y ≤
      finiteHeckeZeroFreeNumerator / (D ^ 4 * Real.log (B * (y + 3))) := by
    change A / _ ≤ _
    rw [← div_div]
    exact div_le_div_of_nonneg_right hAD (perronBand_log_pos hB hy).le
  have hqim : q.im = t := by simp [q, Complex.add_im, Complex.mul_im]
  have hZero : ∃ R : ℝ, ∀ z : ℂ, R ≤ |z.im| → 1 - e |z.im| < z.re → L z ≠ 0 := by
    refine ⟨1 + |t|, fun z hy hz ↦ (hreg z ?_ ?_ (.inr ?_)).2⟩
    · linarith [(hAn (abs_nonneg z.im)).2]
    · linarith [hWidth (abs_nonneg z.im)]
    · change z ≠ q
      intro h
      rw [h, hqim] at hy
      linarith
  obtain ⟨C, W, hC, hg⟩ := hhigh e (1 / 2) (by norm_num) (by norm_num)
    (fun y hy ↦ hAn hy) (fun y hy ↦ (hasDerivAt_perronBandWidth hB hy.le).differentiableAt)
    (tendsto_deriv_perronBandWidth A hB) (perronBandWidth_inv_le hA hB) hZero
  let Y := max W (1 + |t|)
  have hY : 1 + |t| ≤ Y := le_max_right _ _
  have hY₀ : 0 ≤ Y := by linarith [abs_nonneg t]
  have hY₁ : 1 ≤ Y := by linarith [abs_nonneg t]
  have hhigh' (z : ℂ) (hy : Y ≤ |z.im|) (hr : |z.re - 1| ≤ e |z.im| / 2) :
      ‖logDeriv L z‖ ≤ C * Real.log |z.im| ^ 2 := by
    have h' := abs_le.mp hr
    have hx : z.re ∈ Icc (1 - 1 / 2 * e |z.im|) (1 + 1 / 2 * e |z.im|) :=
      ⟨by linarith [h'.1], by linarith [h'.2]⟩
    convert hg z.im z.re ((le_max_left _ _).trans hy) hx using 2
  let S := Icc (1 - e Y / 2) (1 + e Y / 2) ×ℂ Icc (-Y) Y
  have hSc : IsCompact S := isCompact_Icc.reProdIm isCompact_Icc
  have hS (z : ℂ) (hz : z ∈ S) :
      0 < z.re ∧ 1 - finiteHeckeZeroFreeNumerator /
        (D ^ 4 * Real.log (B * (|z.im| + 3))) ≤ z.re := by
    obtain ⟨hx, hy⟩ := Complex.mem_reProdIm.mp hz
    have hy' := abs_le.mpr hy
    have hle := perronBandWidth_decreasing hA hB (a := |z.im|) (b := Y)
      (abs_nonneg z.im) hY₀ hy'
    have hwidth := hWidth (abs_nonneg z.im)
    exact ⟨by linarith [hx.1, (hAn hY₀).2], by linarith [hx.1, (hAn hY₀).1]⟩
  have hMem (z : ℂ) (hy : |z.im| ≤ Y) (hx : |z.re - 1| ≤ e Y / 2) : z ∈ S := by
    have h := abs_le.mp hx
    exact Complex.mem_reProdIm.mpr ⟨⟨by linarith [h.1], by linarith [h.2]⟩, abs_le.mp hy⟩
  have hlow : ∃ M : ℝ, 0 ≤ M ∧ ∀ z ∈ S, z ≠ q →
      ‖logDeriv L z‖ ≤ M + ‖(z - q)⁻¹‖ := by
    by_cases hω : heckeNormOneRestriction F χ = 1
    · obtain ⟨R, hR, hEq⟩ := exists_analytic_negLogDeriv_simplePole_remainder
        (hL.meromorphicOn q (mem_univ _)) (hPole hω)
        (fun z hz hne ↦ hreg z (hS z hz).1 (hS z hz).2 (.inr hne))
      have hRc : ContinuousOn R S := fun z hz ↦ (hR z hz).continuousAt.continuousWithinAt
      obtain ⟨M, hM⟩ := hSc.exists_bound_of_continuousOn hRc
      refine ⟨max 0 M, le_max_left _ _, fun z hz hne ↦ ?_⟩
      have he := hEq z hz hne
      rw [← norm_neg (logDeriv L z), he, one_div]
      exact (norm_add_le _ _).trans (add_le_add (hM z hz |>.trans (le_max_right _ _)) le_rfl)
    · have hRc : ContinuousOn (fun z ↦ -logDeriv L z) S := by
        intro z hz
        obtain ⟨ha, hn⟩ := hreg z (hS z hz).1 (hS z hz).2 (.inl hω)
        exact (analyticAt_neg_logDeriv ha hn).continuousAt.continuousWithinAt
      obtain ⟨M, hM⟩ := hSc.exists_bound_of_continuousOn hRc
      refine ⟨max 0 M, le_max_left _ _, fun z hz _ ↦ ?_⟩
      have h := hM z hz
      rw [norm_neg] at h
      linarith [le_max_right 0 M, norm_nonneg ((z - q)⁻¹)]
  obtain ⟨M, hM, hlow⟩ := hlow
  exact ⟨L, A, B, C, M, Y, hL, heL, hB, hA, hAD, hC, hM, hY, hhigh',
    fun z hy hx hne ↦ hlow z (hMem z hy hx) hne⟩

/-- The high and low estimates supply the pointwise majorants on the
three edges of the translated Perron rectangle. -/
theorem perron_edge_derivative_bounds {L : ℂ → ℂ} {A B C M Y t : ℝ}
    (hA : 0 < A) (hB : 1 ≤ B) (hC : 0 ≤ C) (hM : 0 ≤ M) (hY : 1 ≤ Y)
    (hHigh : ∀ z : ℂ, Y ≤ |z.im| → |z.re - 1| ≤ heckePerronBandWidth A B |z.im| / 2 →
      ‖logDeriv L z‖ ≤ C * Real.log |z.im| ^ 2)
    (hLow : ∀ z : ℂ, |z.im| ≤ Y → |z.re - 1| ≤ heckePerronBandWidth A B Y / 2 →
      z ≠ 1 + (t : ℂ) * I → ‖logDeriv L z‖ ≤ M + ‖(z - (1 + (t : ℂ) * I))⁻¹‖)
    {s : ℂ} (hs : s.re = 1) {δ κ T : ℝ} (hδ : 0 < δ)
    (hT : Y + |s.im| ≤ T)
    (hδBand : δ ≤ heckePerronBandWidth A B (|s.im| + T) / 2)
    (hκBand : κ ≤ heckePerronBandWidth A B (|s.im| + T) / 2) :
    let H (z : ℂ) := -logDeriv L (s + z)
    let N := C * Real.log (|s.im| + T) ^ 2
    (∀ y ∈ Icc (-T) T, ‖H ((-δ : ℝ) + (y : ℂ) * I)‖ ≤ M + δ⁻¹ + N) ∧
    (∀ u ∈ Icc (-δ) κ, ‖H ((u : ℂ) + (T : ℂ) * I)‖ ≤ N) ∧
    (∀ u ∈ Icc (-δ) κ, ‖H ((u : ℂ) + (-T : ℝ) * I)‖ ≤ N) := by
  intro H N
  let U := |s.im| + T
  let q : ℂ := 1 + (t : ℂ) * I
  have hYU : Y ≤ U := by dsimp [U]; linarith [abs_nonneg s.im]
  have hT₀ : 0 < T := by linarith [abs_nonneg s.im]
  have hNu : 0 ≤ N := by dsimp only [N]; positivity
  have hq : q.re = 1 := by simp [q, Complex.add_re, Complex.mul_re]
  have hWidth {u : ℝ} (hu : 0 ≤ u) (huU : u ≤ U) :
      heckePerronBandWidth A B U / 2 ≤ heckePerronBandWidth A B u / 2 :=
    div_le_div_of_nonneg_right (perronBandWidth_decreasing hA hB hu
      (show 0 ≤ U by linarith) huU) (by norm_num)
  have hAtHigh (z : ℂ) (hy : Y ≤ |z.im|) (hz : |z.im| ≤ U)
      (hr : |z.re - 1| ≤ heckePerronBandWidth A B U / 2) :
      ‖logDeriv L z‖ ≤ N := by
    have hh := hHigh z hy (hr.trans (hWidth (abs_nonneg _) hz))
    have hlog : 0 ≤ Real.log |z.im| := Real.log_nonneg (hY.trans hy)
    have hlog' := Real.log_le_log (zero_lt_one.trans_le (hY.trans hy)) hz
    exact hh.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlog hlog' _) hC)
  have hcoords (x y : ℝ) :
      (s + ((x : ℂ) + (y : ℂ) * I)).re = 1 + x ∧
      (s + ((x : ℂ) + (y : ℂ) * I)).im = s.im + y := by
    simp [hs, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  constructor
  · intro y hy
    let z : ℂ := s + ((-δ : ℝ) + (y : ℂ) * I)
    have hRe := (hcoords (-δ) y).1
    have hIm := (hcoords (-δ) y).2
    have hh : |z.im| ≤ U := by
      rw [show z.im = s.im + y from hIm]
      exact (abs_add_le _ _).trans (add_le_add le_rfl (abs_le.mpr hy))
    have hr : |z.re - 1| ≤ heckePerronBandWidth A B U / 2 := by
      rw [show z.re = 1 + (-δ) from hRe, add_sub_cancel_left, abs_neg, abs_of_pos hδ]
      exact hδBand
    change ‖-logDeriv L z‖ ≤ _
    rw [norm_neg]
    by_cases hy' : Y ≤ |z.im|
    · exact (hAtHigh z hy' hh hr).trans (by linarith [inv_nonneg.mpr hδ.le])
    · have hzq : z ≠ q := by
        intro he
        change z.re = 1 + (-δ) at hRe
        rw [he, hq] at hRe
        linarith
      have low := hLow z (le_of_not_ge hy') (hr.trans (hWidth (by linarith) hYU)) hzq
      have hdist : δ ≤ ‖z - q‖ := by
        have hRe' : (z - q).re = -δ := by
          rw [Complex.sub_re, show z.re = 1 + (-δ) from hRe, hq, add_sub_cancel_left]
        simpa [hRe', abs_of_pos hδ] using Complex.abs_re_le_norm (z - q)
      rw [norm_inv] at low
      exact low.trans ((add_le_add le_rfl (inv_anti₀ hδ hdist)).trans (le_add_of_nonneg_right hNu))
  · have hhor {y : ℝ} (hy : |y| = T) (u : ℝ) (hu : u ∈ Icc (-δ) κ) :
        ‖H ((u : ℂ) + (y : ℂ) * I)‖ ≤ N := by
      let z : ℂ := s + ((u : ℂ) + (y : ℂ) * I)
      have hIm : z.im = s.im + y := (hcoords u y).2
      have hRe : z.re = 1 + u := (hcoords u y).1
      have hhi : Y ≤ |z.im| := by
        have hi := abs_sub_abs_le_abs_sub (s.im + y) s.im
        have hi' := abs_sub_abs_le_abs_sub y (-s.im)
        rw [abs_neg, sub_neg_eq_add, add_comm y s.im] at hi'
        rw [hIm]
        linarith
      have hU : |z.im| ≤ U := by
        rw [hIm]
        exact (abs_add_le _ _).trans (add_le_add le_rfl hy.le)
      have hr : |z.re - 1| ≤ heckePerronBandWidth A B U / 2 := by
        rw [hRe, add_sub_cancel_left]
        exact abs_le.mpr ⟨(neg_le_neg hδBand).trans hu.1, hu.2.trans hκBand⟩
      change ‖-logDeriv L z‖ ≤ _
      rw [norm_neg]
      exact hAtHigh z hhi hU hr
    exact ⟨hhor (abs_of_pos hT₀), hhor (by simp [abs_of_pos hT₀])⟩

/-- With (v = sqrt{log x}), the left width (1/v) eventually fits
inside the logarithmic band. The exponential on the left edge then
dominates the polynomial factors in its bound. -/
theorem perronEdge_parameters_eventually {A B C M K ε : ℝ}
    (hA : 0 < A) (hB : 1 ≤ B) (hC : 0 ≤ C) (hM : 0 ≤ M) (hε : 0 < ε) :
    ∀ᶠ v : ℝ in atTop, 1 < v ∧ K ≤ v ∧
      ∀ u ∈ Icc 0 K,
        v⁻¹ ≤ heckePerronBandWidth A B (u + v ^ 6) / 2 ∧
        (M + v + C * Real.log (u + v ^ 6) ^ 2) *
            Real.exp (-v) * v * (2 * v ^ 6) +
          2 * (C * Real.log (u + v ^ 6) ^ 2 * Real.exp 1 / v ^ 6 * ((v ^ 2)⁻¹ + v⁻¹)) < ε := by
  let P := 2 * (M + 1 + 49 * C)
  let Q := 196 * C * Real.exp 1
  have hl : Tendsto (fun v : ℝ ↦ Real.log v / v) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have hW : Tendsto (fun v : ℝ ↦ (Real.log (5 * B) + 6 * Real.log v) / v) atTop (𝓝 0) := by
    have ht := (tendsto_inv_atTop_zero.const_mul (Real.log (5 * B))).add (hl.const_mul 6)
    convert ht using 1
    · funext v
      ring
    · ring
  have hE : Tendsto (fun v : ℝ ↦ P * (v ^ 9 * Real.exp (-v)) + Q * (v⁻¹) ^ 4)
      atTop (𝓝 0) := by
    simpa using ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 9).const_mul P).add
      ((tendsto_inv_atTop_zero.pow 4).const_mul Q)
  filter_upwards [eventually_gt_atTop (1 : ℝ), eventually_ge_atTop K,
    hW.eventually (gt_mem_nhds (half_pos hA)), hE.eventually (gt_mem_nhds hε)] with v hv hKv hw he
  refine ⟨hv, hKv, fun u hu ↦ ?_⟩
  have hv₀ := zero_lt_one.trans hv
  have hv₁ := hv.le
  have hv6 : v ≤ v ^ 6 := by
    calc
      _ = v ^ 1 := by ring
      _ ≤ _ := pow_le_pow_right₀ hv₁ (by decide)
  have hU : u + v ^ 6 ≤ 2 * v ^ 6 := by linarith [hu.2]
  have hp : 0 < u + v ^ 6 := add_pos_of_nonneg_of_pos hu.1 (pow_pos hv₀ _)
  have h1 : 1 ≤ v ^ 6 := one_le_pow₀ hv₁
  have hwd : Real.log (B * (u + v ^ 6 + 3)) ≤ Real.log (5 * B) + 6 * Real.log v := by
    calc
      _ ≤ Real.log ((5 * B) * v ^ 6) := Real.log_le_log (by positivity) (by
        have h := mul_le_mul_of_nonneg_left (show u + v ^ 6 + 3 ≤ 5 * v ^ 6 by linarith)
          (zero_le_one.trans hB)
        nlinarith only [h])
      _ = _ := by
        rw [Real.log_mul (by positivity : 5 * B ≠ 0) (pow_ne_zero _ hv₀.ne'), Real.log_pow]
        norm_num
  refine ⟨?_, ?_⟩
  · have hlog := perronBand_log_pos hB hp.le
    have hw' := (div_lt_iff₀ hv₀).mp hw
    change v⁻¹ ≤ A / Real.log (B * (u + v ^ 6 + 3)) / 2
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
    apply (le_div_iff₀ hlog).mpr
    calc
      _ ≤ (v⁻¹ * 2) * (A / 2 * v) :=
        mul_le_mul_of_nonneg_left (hwd.trans hw'.le) (by positivity)
      _ = _ := by field_simp
  have hlog₀ : 0 ≤ Real.log (u + v ^ 6) := Real.log_nonneg (by linarith [hu.1])
  have hlog : Real.log (u + v ^ 6) ≤ 7 * v := by
    have h := Real.log_le_log hp hU
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (pow_ne_zero _ hv₀.ne'),
      Real.log_pow] at h
    norm_num at h
    have hlog₂ : Real.log 2 ≤ 1 := by
      linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith [Real.log_le_sub_one_of_pos hv₀]
  have hsq : Real.log (u + v ^ 6) ^ 2 ≤ 49 * v ^ 2 := by
    nlinarith [pow_le_pow_left₀ hlog₀ hlog 2]
  have hvsq : v ≤ v ^ 2 := by nlinarith
  have hLeft : M + v + C * Real.log (u + v ^ 6) ^ 2 ≤ (M + 1 + 49 * C) * v ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hsq hC, mul_nonneg hM (show 0 ≤ v ^ 2 - 1 by nlinarith)]
  have hSum : (v ^ 2)⁻¹ + v⁻¹ ≤ 2 := by
    have h₁ := inv_le_one_of_one_le₀ (one_le_pow₀ (n := 2) hv₁)
    have h₂ := inv_le_one_of_one_le₀ hv₁
    linarith
  refine lt_of_le_of_lt ?_ he
  apply add_le_add
  · calc
      _ ≤ ((M + 1 + 49 * C) * v ^ 2) * Real.exp (-v) * v * (2 * v ^ 6) := by gcongr
      _ = P * (v ^ 9 * Real.exp (-v)) := by dsimp [P]; ring
  · calc
      _ ≤ 2 * (C * (49 * v ^ 2) * Real.exp 1 / v ^ 6 * 2) := by gcongr
      _ = Q * (v⁻¹) ^ 4 := by dsimp [Q]; field_simp; ring

set_option maxHeartbeats 500000 in
include μ hν in
/-- Uniform contour shift for the same normalized continuation used on the
right edge. The estimate holds for every bounded range of ordinates. -/
theorem exists_manuscriptFiniteHecke_perron_shift_eventually (χ : PontryaginDual (IdeleClass F))
    {t : ℝ} (ht : HasHeckeHeight F χ t) :
    ∃ L : ℂ → ℂ, MeromorphicNFOn L univ ∧
      EqOn L (manuscriptFiniteHeckeEuler F χ) {z | 1 < z.re} ∧
      ∀ (K B₁ ε : ℝ), 1 ≤ B₁ → 0 < ε → ∀ᶠ x : ℝ in atTop,
        ∀ s : ℂ, s.re = 1 → |s.im| ≤ K →
          let δ := (Real.sqrt (Real.log x))⁻¹
          let κ := (Real.log x)⁻¹
          let T := Real.log x ^ 3
          let H (z : ℂ) := -logDeriv L (s + z)
          0 < δ ∧ δ < 1 ∧ 0 < κ ∧ 0 < T ∧ |t - s.im| < T ∧
          δ ≤ finiteHeckeZeroFreeNumerator /
            ((Module.finrank ℚ F : ℝ) ^ 4 * Real.log (B₁ * (|s.im| + T + 3))) ∧
          ∀ r : ℂ, rectIntegral (perronContourIntegrand x H) (-δ) κ (-T) T =
            (2 * Real.pi * I) * r →
            ‖((∫ y in -T..T, perronContourIntegrand x H ((κ : ℂ) + (y : ℂ) * I)) /
              (2 * (Real.pi : ℂ))) - r‖ < ε := by
  obtain ⟨L, A, B, C, M, Y, hL, he, hB, hA, hAD, hC, hM, hY, hHigh, hLow⟩ :=
    exists_manuscriptFiniteHecke_perron_derivative_bounds F ν η μ hν χ ht
  refine ⟨L, hL, he, fun K B₁ ε hB₁ hε ↦ ?_⟩
  let B₂ := max B B₁
  have hB₂ : 1 ≤ B₂ := hB.trans (le_max_left _ _)
  let K₂ := max K (Y + K + 1)
  have hp := perronEdge_parameters_eventually (K := K₂) hA hB₂ hC hM
    (mul_pos (by positivity : 0 < 2 * Real.pi) hε)
  have htend := (Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop)
  filter_upwards [htend.eventually hp, eventually_ge_atTop (1 : ℝ)] with x hp hx s hs him
  dsimp only
  let v := Real.sqrt (Real.log x)
  have hv2 : v ^ 2 = Real.log x := Real.sq_sqrt (Real.log_nonneg hx)
  obtain ⟨hv, hKv, hparam⟩ := hp
  change 1 < v at hv
  change K₂ ≤ v at hKv
  have hv₀ := zero_lt_one.trans hv
  have hδ : 0 < v⁻¹ := inv_pos.mpr hv₀
  have hδ₁ : v⁻¹ < 1 := inv_lt_one_of_one_lt₀ hv
  have hκ : 0 < (v ^ 2)⁻¹ := inv_pos.mpr (pow_pos hv₀ _)
  have hT : 0 < v ^ 6 := pow_pos hv₀ _
  have hT' : Real.log x ^ 3 = v ^ 6 := by rw [← hv2]; ring
  have hu : |s.im| ∈ Icc (0 : ℝ) K₂ := ⟨abs_nonneg _, him.trans (le_max_left _ _)⟩
  obtain ⟨hwidth, herr⟩ := hparam |s.im| hu
  have hv6 : v ≤ v ^ 6 := by
    calc
      _ = v ^ 1 := by ring
      _ ≤ _ := pow_le_pow_right₀ hv.le (by decide)
  have hY₁ : 1 ≤ Y := by linarith [abs_nonneg t]
  have hTH : Y + |s.im| + 1 ≤ v ^ 6 :=
    (by linarith [him] : Y + |s.im| + 1 ≤ Y + K + 1).trans
      ((le_max_right _ _).trans (hKv.trans hv6))
  have hpole : |t - s.im| < v ^ 6 := by
    have h := abs_sub_le t (0 : ℝ) s.im
    rw [sub_zero, zero_sub, abs_neg] at h
    linarith
  have hU : 0 ≤ |s.im| + v ^ 6 := by positivity
  have hcmp {B₀ : ℝ} (h₀ : 1 ≤ B₀) (h₀₂ : B₀ ≤ B₂) :
      heckePerronBandWidth A B₂ (|s.im| + v ^ 6) ≤
        heckePerronBandWidth A B₀ (|s.im| + v ^ 6) := by
    apply div_le_div_of_nonneg_left hA.le (perronBand_log_pos h₀ hU)
    exact Real.log_le_log (mul_pos (zero_lt_one.trans_le h₀) (by linarith))
      (mul_le_mul_of_nonneg_right h₀₂ (by linarith))
  have hwidthB := hwidth.trans (div_le_div_of_nonneg_right (hcmp hB (le_max_left _ _)) (by norm_num))
  have hκδ : (v ^ 2)⁻¹ ≤ v⁻¹ := inv_anti₀ hv₀ (by nlinarith)
  have hwidth₁ : v⁻¹ ≤ finiteHeckeZeroFreeNumerator /
      ((Module.finrank ℚ F : ℝ) ^ 4 * Real.log (B₁ * (|s.im| + v ^ 6 + 3))) := by
    have hh := hwidth.trans (div_le_div_of_nonneg_right (hcmp hB₁ (le_max_right _ _)) (by norm_num))
    have hlog := perronBand_log_pos hB₁ hU
    refine hh.trans ?_
    rw [← div_div]
    exact (half_le_self (div_nonneg hA.le hlog.le)).trans (div_le_div_of_nonneg_right hAD hlog.le)
  rw [hT', ← hv2, Real.sqrt_sq hv₀.le]
  refine ⟨hδ, hδ₁, hκ, hT, hpole, hwidth₁, fun r hr ↦ ?_⟩
  obtain ⟨hLeft, hTop, hBottom⟩ := perron_edge_derivative_bounds hA hB hC hM hY₁
    hHigh hLow hs hδ (show Y + |s.im| ≤ v ^ 6 by linarith)
    hwidthB (hκδ.trans hwidthB)
  let N := C * Real.log (|s.im| + v ^ 6) ^ 2
  have hN : 0 ≤ N := by dsimp only [N]; positivity
  have hShift := norm_perronContour_shift_le hx hδ hκ hT
    (show 0 ≤ M + (v⁻¹)⁻¹ + N by positivity) hN hr hLeft hTop hBottom
  refine hShift.trans_lt ((div_lt_iff₀ (by positivity : 0 < 2 * Real.pi)).mpr ?_)
  have heLeft : Real.log x * (-v⁻¹) = -v := by rw [← hv2]; field_simp
  have heRight : Real.log x * (v ^ 2)⁻¹ = 1 := by rw [← hv2, mul_inv_cancel₀ (pow_ne_zero _ hv₀.ne')]
  rw [heLeft, heRight, inv_inv]
  simp only [div_eq_mul_inv, inv_inv, Function.comp_apply] at herr ⊢
  simpa only [mul_comm ε (2 * Real.pi)] using herr

end

end Masullo
