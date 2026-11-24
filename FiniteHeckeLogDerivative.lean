import FiniteHeckeReciprocal
import LandauDisk

open Filter Function IsDedekindDomain MeasureTheory Metric NumberField Set Topology
open scoped Classical NumberField

namespace Masullo

noncomputable section

private theorem zeroFree_band_separation {f : ℂ → ℂ} {e : ℝ → ℝ} {a T y x : ℝ}
    (ha : 0 < a) (ha' : a < 1)
    (hy : T + 1 ≤ |y|)
    (he : 0 < e |y|) (he' : e |y| ≤ 1 / 2)
    (hDiff : ∀ u ≥ T, DifferentiableAt ℝ e u)
    (hDer : ∀ u ≥ T, ‖deriv e u‖ ≤ 1)
    (hZero : ∀ z : ℂ, T ≤ |z.im| → 1 - e |z.im| < z.re → f z ≠ 0)
    (hx : 1 - a * e |y| ≤ x) {ρ : ℂ} (hρ : f ρ = 0) :
    (1 - a) / 2 * e |y| ≤ ‖(⟨x, y⟩ : ℂ) - ρ‖ := by
  let d := (1 - a) / 2 * e |y|
  have hd : d ≤ 1 := by
    dsimp [d]
    nlinarith [mul_le_mul_of_nonneg_right (show 1 - a ≤ 1 by linarith) he.le]
  by_cases hi : d ≤ |y - ρ.im|
  · exact hi.trans (Complex.abs_im_le_norm ((⟨x, y⟩ : ℂ) - ρ))
  · have hh : abs (|y| - |ρ.im|) ≤ |y - ρ.im| := abs_abs_sub_abs_le_abs_sub _ _
    have hρT : T ≤ |ρ.im| := by
      have h := (le_abs_self (|y| - |ρ.im|)).trans hh
      linarith [lt_of_not_ge hi]
    have hE := Convex.norm_image_sub_le_of_norm_deriv_le (s := Ici T) hDiff hDer
      (convex_Ici _) (show |y| ∈ Ici T from by change T ≤ |y|; linarith) hρT
    rw [Real.norm_eq_abs, Real.norm_eq_abs, one_mul, abs_sub_comm |ρ.im| |y|] at hE
    have hLower : e |y| - d ≤ e |ρ.im| := by
      have h := (neg_le_abs (e |ρ.im| - e |y|)).trans (hE.trans hh)
      linarith [lt_of_not_ge hi]
    have hRight : ρ.re ≤ 1 - e |ρ.im| :=
      le_of_not_gt fun h ↦ hZero ρ hρT h hρ
    have hReal : d ≤ x - ρ.re := by dsimp [d] at hLower ⊢; linarith
    exact hReal.trans ((le_abs_self _).trans (Complex.abs_re_le_norm ((⟨x, y⟩ : ℂ) - ρ)))

variable (F : Type*) [Field F] [NumberField F]

private abbrev Place := HeightOneSpectrum (𝓞 F)
private abbrev K := normOneIdeleClass F

local instance logDerivativeNormOneMeasurable : MeasurableSpace (K F) := borel _
local instance logDerivativeNormOneBorel : BorelSpace (K F) := ⟨rfl⟩
local instance logDerivativeIdeleMeasurable : MeasurableSpace (Idele F) := borel _
local instance logDerivativeIdeleBorel : BorelSpace (Idele F) := ⟨rfl⟩

variable (ν : Measure (K F)) [ν.IsHaarMeasure]
variable (η : Measure (Idele F)) [η.IsHaarMeasure]
variable [∀ v : Place F, MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : Place F, BorelSpace (v.adicCompletion F)ˣ]
  (μ : ∀ v : Place F, Measure (v.adicCompletion F)ˣ)
  [∀ v : Place F, (μ v).IsHaarMeasure] [∀ v : Place F, SigmaFinite (μ v)]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]
variable (hν : IsWeilQuotientMeasure (principalIdeles F) η Measure.count (globalClassMeasure F ν))

/-- Polynomial strip bounds and a positive lower bound at the center give
a polynomial relative bound on moving disks of any fixed radius. -/
theorem disk_bound_of_degree_polynomial_strip {L : ℂ → ℂ} {R T₀ c A : ℝ} {N : ℕ}
    (hR : 0 < R) (hc : 0 < c) (hA : 0 ≤ A)
    (hcenter : ∀ y : ℝ, T₀ ≤ |y| → c ≤ ‖L ⟨2, y⟩‖)
    (hAn : ∀ z : ℂ, T₀ ≤ |z.im| → AnalyticAt ℂ L z)
    (hG : ∀ w : ℂ, w.re ∈ Icc (2 - R) (2 + R) → T₀ ≤ |w.im| → ‖L w‖ ≤ A * (1 + |w.im|) ^ N) :
    ∃ T : ℝ, 2 ≤ T ∧
      ∀ y : ℝ, T ≤ |y| →
        AnalyticOnNhd ℂ L (closedBall ⟨2, y⟩ R) ∧ L ⟨2, y⟩ ≠ 0 ∧
          ∀ w ∈ closedBall (⟨2, y⟩ : ℂ) R, ‖L w / L ⟨2, y⟩‖ ≤ |y| ^ (N + 1) := by
  let B := A * (R + 2) ^ N / c
  let T := max (T₀ + R) (max 2 B)
  refine ⟨T, (le_max_left _ _).trans (le_max_right _ _), ?_⟩
  intro y hy
  have hy₁ : 1 ≤ |y| := by linarith [le_max_left (2 : ℝ) B, le_max_right (T₀ + R) (max 2 B)]
  have hyB : B ≤ |y| := (le_max_right _ _).trans ((le_max_right _ _).trans hy)
  have hyT : T₀ + R ≤ |y| := (le_max_left _ _).trans hy
  have hnorm : c ≤ ‖L ⟨2, y⟩‖ := hcenter y (by linarith)
  have hdisc (w : ℂ) (hw : w ∈ closedBall (⟨2, y⟩ : ℂ) R) :
      w.re ∈ Icc (2 - R) (2 + R) ∧ T₀ ≤ |w.im| ∧ 1 + |w.im| ≤ (R + 2) * |y| := by
    have hd := mem_closedBall_iff_norm.mp hw
    have hr : |w.re - 2| ≤ R := (Complex.abs_re_le_norm _).trans hd
    have hi : |w.im - y| ≤ R := (Complex.abs_im_le_norm _).trans hd
    have hDiff := (abs_abs_sub_abs_le_abs_sub w.im y).trans hi
    refine ⟨⟨by linarith [(abs_le.mp hr).1], by linarith [(abs_le.mp hr).2]⟩,
      by linarith [(abs_le.mp hDiff).1], ?_⟩
    nlinarith [(abs_le.mp hDiff).2, mul_nonneg (show 0 ≤ R + 1 by positivity) (sub_nonneg.mpr hy₁)]
  refine ⟨fun w hw ↦ hAn w (hdisc w hw).2.1, norm_pos_iff.mp (hc.trans_le hnorm), ?_⟩
  intro w hw
  obtain ⟨hr, hi, hsize⟩ := hdisc w hw
  rw [norm_div]
  calc
    _ ≤ ‖L w‖ / c := div_le_div_of_nonneg_left (norm_nonneg _) hc hnorm
    _ ≤ (A * ((R + 2) * |y|) ^ N) / c := div_le_div_of_nonneg_right
      ((hG _ hr hi).trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hsize _) hA)) hc.le
    _ = B * |y| ^ N := by rw [mul_pow]; dsimp [B]; ring
    _ ≤ |y| ^ (N + 1) := by
      rw [pow_succ, mul_comm (|y| ^ N)]
      exact mul_le_mul_of_nonneg_right hyB (by positivity)

theorem disk_bound_of_polynomial_strip {L : ℂ → ℂ} {R T₀ c : ℝ}
    (hR : 0 < R) (hc : 0 < c)
    (hcenter : ∀ y : ℝ, T₀ ≤ |y| → c ≤ ‖L ⟨2, y⟩‖)
    (hAn : ∀ z : ℂ, T₀ ≤ |z.im| → AnalyticAt ℂ L z)
    (hGrowth : ∃ (A : ℝ) (N : ℕ), 0 ≤ A ∧
      ∀ w : ℂ, w.re ∈ Icc (2 - R) (2 + R) → T₀ ≤ |w.im| → ‖L w‖ ≤ A * (1 + |w.im|) ^ N) :
    ∃ (N : ℕ) (T : ℝ), 0 < N ∧ 2 ≤ T ∧
      ∀ y : ℝ, T ≤ |y| →
        AnalyticOnNhd ℂ L (closedBall ⟨2, y⟩ R) ∧ L ⟨2, y⟩ ≠ 0 ∧
          ∀ w ∈ closedBall (⟨2, y⟩ : ℂ) R, ‖L w / L ⟨2, y⟩‖ ≤ |y| ^ N := by
  obtain ⟨A, N, hA, hG⟩ := hGrowth
  obtain ⟨T, hT, h⟩ := disk_bound_of_degree_polynomial_strip hR hc hA hcenter hAn hG
  exact ⟨N + 1, T, Nat.succ_pos _, hT, h⟩

include μ hν in
/-- The finite Hecke continuation satisfies the fixed-radius relative
bounds required by Landau's lemma at every sufficiently high ordinate. -/
theorem exists_manuscriptFiniteHecke_disk_bound_radius (χ : PontryaginDual (IdeleClass F))
    {R : ℝ} (hR : 0 < R) :
    ∃ (L : ℂ → ℂ) (N : ℕ) (T : ℝ), 0 < N ∧ 2 ≤ T ∧ MeromorphicNFOn L univ ∧
      EqOn L (manuscriptFiniteHeckeEuler F χ) {z | 1 < z.re} ∧
      ∀ y : ℝ, T ≤ |y| →
        AnalyticOnNhd ℂ L (closedBall ⟨2, y⟩ R) ∧ L ⟨2, y⟩ ≠ 0 ∧
          ∀ w ∈ closedBall (⟨2, y⟩ : ℂ) R, ‖L w / L ⟨2, y⟩‖ ≤ |y| ^ N := by
  obtain ⟨L, t, _, hm, he, ha, hg⟩ := exists_manuscriptFiniteHecke_polynomial_strips F ν η μ hν χ
  obtain ⟨c, hc, hC⟩ := manuscriptFiniteHecke_norm_ge_two F
  have hcenter (y : ℝ) : c ≤ ‖L ⟨2, y⟩‖ := by
    rw [he (show (1 : ℝ) < 2 by norm_num)]
    exact hC χ y
  have hAn (w : ℂ) (hh : 1 + |t| ≤ |w.im|) : AnalyticAt ℂ L w := by
    apply ha w <;> intro e
    · have hi := congrArg Complex.im e
      simp [Complex.mul_im] at hi
      rw [hi] at hh
      linarith
    · have hi := congrArg Complex.im e
      simp [Complex.add_im, Complex.mul_im] at hi
      rw [hi] at hh
      linarith
  obtain ⟨N, T, hN, hT, h⟩ := disk_bound_of_polynomial_strip hR hc
    (fun y _ ↦ hcenter y) hAn (hg (2 - R) (2 + R) (by linarith))
  let G := toMeromorphicNFOn L univ
  have hG (z : ℂ) (ha : AnalyticAt ℂ L z) : G =ᶠ[𝓝 z] L := by
    rw [← toMeromorphicNFAt_eq_self.mpr ha.meromorphicNFAt]
    exact toMeromorphicNFOn_eq_toMeromorphicNFAt_on_nhds hm (mem_univ z)
  refine ⟨G, N, T, hN, hT, meromorphicNFOn_toMeromorphicNFOn L univ, ?_, ?_⟩
  · intro z hz
    have hre : 1 < z.re := hz
    have hAnz := ha z (fun h ↦ by
      rw [h] at hre
      norm_num [Complex.mul_re] at hre) (fun h ↦ by
      rw [h] at hre
      norm_num [Complex.mul_re, Complex.add_re] at hre)
    exact (hG z hAnz).eq_of_nhds.trans (he hz)
  · intro y hy
    obtain ⟨hAn, hcenter, hB⟩ := h y hy
    have hcg := (hG ⟨2, y⟩ (hAn _ (mem_closedBall_self hR.le))).eq_of_nhds
    refine ⟨fun w hw ↦ (hAn w hw).congr (hG w (hAn w hw)).symm, hcg ▸ hcenter, ?_⟩
    intro w hw
    rw [(hG w (hAn w hw)).eq_of_nhds, hcg]
    exact hB w hw

include μ hν in
theorem exists_manuscriptFiniteHecke_disk_bound (χ : PontryaginDual (IdeleClass F)) :
    ∃ (L : ℂ → ℂ) (N : ℕ) (T : ℝ), 0 < N ∧ 2 ≤ T ∧ MeromorphicNFOn L univ ∧
      EqOn L (manuscriptFiniteHeckeEuler F χ) {z | 1 < z.re} ∧
      ∀ y : ℝ, T ≤ |y| →
        AnalyticOnNhd ℂ L (closedBall ⟨2, y⟩ 8) ∧ L ⟨2, y⟩ ≠ 0 ∧
          ∀ w ∈ closedBall (⟨2, y⟩ : ℂ) 8, ‖L w / L ⟨2, y⟩‖ ≤ |y| ^ N :=
  exists_manuscriptFiniteHecke_disk_bound_radius F ν η μ hν χ (by norm_num)

include μ hν in
/-- Moving disks at high ordinates give a multiplicity bound and a
logarithmic-derivative estimate in terms of distance from the zeros. -/
theorem exists_manuscriptFiniteHecke_disk_zero_estimates
    (χ : PontryaginDual (IdeleClass F)) :
    ∃ (L : ℂ → ℂ) (N : ℕ) (T : ℝ), 0 < N ∧ 2 ≤ T ∧ MeromorphicNFOn L univ ∧
      EqOn L (manuscriptFiniteHeckeEuler F χ) {z | 1 < z.re} ∧
      ∀ y : ℝ, T ≤ |y| →
        let c : ℂ := ⟨2, y⟩
        AnalyticOnNhd ℂ L (closedBall c 8) ∧ L c ≠ 0 ∧
          (∑ᶠ ρ ∈ closedBall c 4, (analyticOrderNatAt L ρ : ℝ)) ≤
            (N : ℝ) * Real.log |y| / Real.log 2 ∧
          ∀ z ∈ closedBall c 2, ∀ δ > (0 : ℝ),
            (∀ ρ ∈ closedBall c 4, L ρ = 0 → δ ≤ ‖z - ρ‖) →
              ‖logDeriv L z‖ ≤ 300 * ((N : ℝ) * Real.log |y|) / 8 +
                ((N : ℝ) * Real.log |y| / Real.log 2) / δ := by
  obtain ⟨L, N, T, hN, hT, hL, he, hDisk⟩ :=
    exists_manuscriptFiniteHecke_disk_bound F ν η μ hν χ
  refine ⟨L, N, T, hN, hT, hL, he, fun y hy => ?_⟩
  obtain ⟨ha, hc, hb⟩ := hDisk y hy
  refine ⟨ha, hc, ?_, fun z hz δ hδ hSep => ?_⟩
  · have h := RiemannMasullo.landau_sum_analyticOrderNatAt_le
      (by norm_num : (0 : ℝ) < 4) (by norm_num : (4 : ℝ) < 8) ha hc hb
    simpa only [Real.log_pow, show (8 : ℝ) / 4 = 2 by norm_num] using h
  · have h₀ : L z ≠ 0 := fun heq => (not_le_of_gt hδ) (by
      simpa using hSep z (closedBall_subset_closedBall (by norm_num) hz) heq)
    have h := RiemannMasullo.landau_norm_logDeriv_le_of_zero_separation
      (one_lt_pow₀ (one_lt_two.trans_le (hT.trans hy)) hN.ne') (by norm_num : (0 : ℝ) < 8)
      hδ ha hc hb (by simpa only [show (8 : ℝ) / 4 = 2 by norm_num] using hz) h₀
      (fun ρ hρ => hSep ρ (by simpa only [show (8 : ℝ) / 2 = 4 by norm_num] using hρ))
    simpa only [Real.log_pow] using h

set_option maxHeartbeats 500000 in
include μ hν in
/-- Theorem B.6.1.3. A zero-free band of half-width `e` implies the
uniform logarithmic-derivative estimate on each strictly narrower band. -/
theorem exists_manuscriptFiniteHecke_logDeriv_of_zeroFree
    (χ : PontryaginDual (IdeleClass F)) :
    ∃ L : ℂ → ℂ, MeromorphicNFOn L univ ∧
      EqOn L (manuscriptFiniteHeckeEuler F χ) {z | 1 < z.re} ∧
      ∀ (e : ℝ → ℝ) (a : ℝ), 0 < a → a < 1 →
        (∀ y ≥ 0, 0 < e y ∧ e y ≤ 1 / 2) →
        (∀ y > 0, DifferentiableAt ℝ e y) →
        Tendsto (deriv e) atTop (𝓝 0) →
        (∃ D W : ℝ, 0 ≤ D ∧ ∀ y ≥ W, (e y)⁻¹ ≤ D * Real.log y) →
        (∃ R : ℝ, ∀ z : ℂ, R ≤ |z.im| → 1 - e |z.im| < z.re → L z ≠ 0) →
        ∃ C T : ℝ, 0 ≤ C ∧ ∀ y x : ℝ, T ≤ |y| →
          x ∈ Icc (1 - a * e |y|) (1 + a * e |y|) →
          ‖logDeriv L ⟨x, y⟩‖ ≤ C * (Real.log |y|) ^ 2 := by
  obtain ⟨L, N, S, hN, hS, hm, he, hDisk⟩ :=
    exists_manuscriptFiniteHecke_disk_bound F ν η μ hν χ
  refine ⟨L, hm, he, fun e a ha ha' he₀ heD heLim ⟨D, W, hD, hInv⟩ ⟨R, hZero⟩ ↦ ?_⟩
  let c := (1 - a) / 2
  have hc : 0 < c := by dsimp [c]; linarith
  obtain ⟨U₀, hU₀⟩ := eventually_atTop.mp
    (heLim.norm.eventually_le_const (by norm_num : ‖(0 : ℝ)‖ < 1))
  let U := max 1 (max R U₀)
  let T := max (max S W) (U + 1)
  let C₁ : ℝ := 300 * (N : ℝ) / (8 * Real.log 2)
  let C₂ : ℝ := (N : ℝ) / (Real.log 2 * c)
  have hlog₂ : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨C₁ + C₂ * D, T, by dsimp [C₁, C₂]; positivity, fun y x hy hx ↦ ?_⟩
  have hSU : S ≤ |y| := (le_max_left _ _).trans ((le_max_left _ _).trans hy)
  have hWU : W ≤ |y| := (le_max_right _ _).trans ((le_max_left _ _).trans hy)
  have hUy : U + 1 ≤ |y| := (le_max_right _ _).trans hy
  have hU : 1 ≤ U := le_max_left _ _
  have hUy' : U ≤ |y| := by linarith
  have hePos := he₀ |y| (abs_nonneg y)
  have hlt : 1 - e |y| < x := by
    nlinarith [hx.1, mul_pos (sub_pos.mpr ha') hePos.1]
  have hZero' (z : ℂ) (hz : U ≤ |z.im|) (h : 1 - e |z.im| < z.re) : L z ≠ 0 :=
    hZero z ((le_max_left R U₀).trans ((le_max_right (1 : ℝ) _).trans hz)) h
  have hLz : L ⟨x, y⟩ ≠ 0 := hZero' _ hUy' hlt
  have hball : (⟨x, y⟩ : ℂ) ∈ closedBall ⟨2, y⟩ (8 / 4) := by
    rw [mem_closedBall_iff_norm]
    have hsub : (⟨x, y⟩ : ℂ) - ⟨2, y⟩ = ((x - 2 : ℝ) : ℂ) := by
      apply Complex.ext <;> simp
    rw [hsub, Complex.norm_real, Real.norm_eq_abs]
    have hh := mul_le_mul_of_nonneg_left hePos.2 ha.le
    exact abs_le.mpr ⟨by nlinarith [hx.1], by nlinarith [hx.2]⟩
  have hd : 0 < c * e |y| := mul_pos hc hePos.1
  have hSep (ρ : ℂ) (hρ : L ρ = 0) : c * e |y| ≤ ‖(⟨x, y⟩ : ℂ) - ρ‖ :=
    zeroFree_band_separation ha ha' hUy hePos.1 hePos.2
      (fun u hu ↦ heD u (zero_lt_one.trans_le (hU.trans hu)))
      (fun u hu ↦ hU₀ u ((le_max_right R U₀).trans ((le_max_right (1 : ℝ) _).trans hu)))
      hZero' hx.1 hρ
  obtain ⟨hAn, hcenter, hB⟩ := hDisk y hSU
  have hY : 1 < |y| := one_lt_two.trans_le (hS.trans hSU)
  have hLandau := RiemannMasullo.landau_norm_logDeriv_le_of_zero_separation
    (one_lt_pow₀ hY hN.ne') (by norm_num : (0 : ℝ) < 8) hd hAn hcenter hB hball hLz
    (fun ρ _ hρ ↦ hSep ρ hρ)
  rw [Real.log_pow] at hLandau
  let l := Real.log |y|
  have hl : 0 ≤ l := Real.log_nonneg hY.le
  have hll : Real.log 2 ≤ l := Real.log_le_log (by norm_num) (hS.trans hSU)
  have h₁ : 300 * ((N : ℝ) * l) / 8 ≤ C₁ * l ^ 2 := by
    have h := (le_div_iff₀ hlog₂).2 (show l * Real.log 2 ≤ l ^ 2 from by
      rw [pow_two]
      exact mul_le_mul_of_nonneg_left hll hl)
    calc
      _ = (300 * (N : ℝ) / 8) * l := by ring
      _ ≤ (300 * (N : ℝ) / 8) * (l ^ 2 / Real.log 2) := mul_le_mul_of_nonneg_left h (by positivity)
      _ = _ := by dsimp [C₁]; ring
  have h₂ : (((N : ℝ) * l) / Real.log 2) / (c * e |y|) ≤ C₂ * D * l ^ 2 := by
    have hh := mul_le_mul_of_nonneg_left (hInv _ hWU)
      (show 0 ≤ C₂ * l from mul_nonneg (by dsimp [C₂]; positivity) hl)
    calc
      _ = (C₂ * l) * (e |y|)⁻¹ := by simp only [C₂, div_eq_mul_inv, mul_inv_rev]; ring
      _ ≤ (C₂ * l) * (D * Real.log |y|) := hh
      _ = _ := by change (C₂ * l) * (D * l) = _; ring
  exact hLandau.trans ((add_le_add h₁ h₂).trans_eq (by ring))

end

end Masullo
