import MaximalAverages
import DifferentiationAverages
import Mathlib.MeasureTheory.Covering.Vitali
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open Filter Metric MeasureTheory Set Topology
open scoped ENNReal NNReal

namespace Masullo

noncomputable section

/-- Centered averages with admissible radii in a fixed set. Open intervals
give the same averages as closed intervals for measures with a density. -/
def realCenteredMaximal (ν : Measure ℝ) (radii : Set ℝ) (x : ℝ) : ℝ≥0∞ :=
  ⨆ (r : ℝ) (_ : r ∈ radii) (_ : 0 < r), ν (ball x r) / ENNReal.ofReal (2 * r)

private theorem realCenteredMaximal_lt_iff (ν : Measure ℝ) (radii : Set ℝ)
    (x : ℝ) (a : ℝ≥0∞) :
    a < realCenteredMaximal ν radii x ↔
      ∃ r ∈ radii, 0 < r ∧ a * ENNReal.ofReal (2 * r) < ν (ball x r) := by
  simp only [realCenteredMaximal, lt_iSup_iff]
  refine exists_congr fun r => ?_
  constructor
  · rintro ⟨hr, hpos, h⟩
    exact ⟨hr, hpos, (ENNReal.lt_div_iff_mul_lt
      (Or.inl (show 0 < ENNReal.ofReal (2 * r) by positivity).ne') (Or.inl ENNReal.ofReal_ne_top)).mp h⟩
  · rintro ⟨hr, hpos, h⟩
    exact ⟨hr, hpos, (ENNReal.lt_div_iff_mul_lt
      (Or.inl (show 0 < ENNReal.ofReal (2 * r) by positivity).ne') (Or.inl ENNReal.ofReal_ne_top)).mpr h⟩

private theorem real_measure_ball_eq_iSup (ν : Measure ℝ) (x r : ℝ) :
    ν (ball x r) = ⨆ s : Iio r, ν (ball x s.val) := by
  let R := fun n : ℕ => r - 1 / (n + 1 : ℝ)
  have hR (n : ℕ) : R n < r := sub_lt_self _ (by positivity)
  have hmono : Monotone (fun n => ball x (R n)) := by
    intro m n hmn
    exact ball_subset_ball (sub_le_sub_left (by gcongr) _)
  have he : ball x r = ⋃ n : ℕ, ball x (R n) := by
    ext y
    simp only [mem_ball, mem_iUnion]
    constructor
    · intro hy
      obtain ⟨n, hn⟩ := exists_nat_gt (1 / (r - dist y x))
      use n
      have hpos : 0 < r - dist y x := sub_pos.mpr hy
      have hnp : 0 < (n : ℝ) + 1 := by positivity
      have hn' : 1 < ((n : ℝ) + 1) * (r - dist y x) := by
        have hlt := (div_lt_iff₀ hpos).mp hn
        nlinarith
      have hsmall := (div_lt_iff₀ hnp).mpr (by simpa only [mul_comm] using hn')
      change dist y x < r - 1 / ((n : ℝ) + 1)
      linarith
    · rintro ⟨n, hn⟩
      exact hn.trans (hR n)
  apply le_antisymm
  · rw [he, hmono.measure_iUnion]
    exact iSup_le fun n => le_iSup (fun s : Iio r => ν (ball x s.val)) ⟨R n, hR n⟩
  · exact iSup_le fun s => measure_mono (ball_subset_ball s.property.le)

theorem realCenteredMaximal_measurable (ν : Measure ℝ) (radii : Set ℝ) :
    Measurable (realCenteredMaximal ν radii) := by
  apply measurable_of_Ioi
  intro a
  apply IsOpen.measurableSet
  apply Metric.isOpen_iff.mpr
  intro x hx
  obtain ⟨r, hr, hr₀, hx⟩ := (realCenteredMaximal_lt_iff ν radii x a).mp hx
  rw [real_measure_ball_eq_iSup ν] at hx
  obtain ⟨s, hs⟩ := lt_iSup_iff.mp hx
  refine ⟨r - s, sub_pos.mpr s.property, fun y hy => ?_⟩
  apply (realCenteredMaximal_lt_iff ν radii y a).mpr
  refine ⟨r, hr, hr₀, hs.trans_le (measure_mono (ball_subset_ball' ?_))⟩
  have hd : dist x y < r - s := by simpa [mem_ball, dist_comm] using hy
  linarith

/-- The global weak estimate for positive finite mass, with the exact real
Vitali constant three. -/
theorem realCenteredMaximal_weak (ν : Measure ℝ) (hν : ν univ < ⊤)
    (radii : Set ℝ) {a : ℝ} (ha : 0 < a) :
    volume {x | ENNReal.ofReal a < realCenteredMaximal ν radii x} ≤
      ENNReal.ofReal (3 / a) * ν univ := by
  let t : Set (ℝ × ℝ) := {p | p.2 ∈ radii ∧ 0 < p.2 ∧
    ENNReal.ofReal a * ENNReal.ofReal (2 * p.2) < ν (ball p.1 p.2)}
  let L := (ν univ).toReal / a / 2
  have ht (p : ℝ × ℝ) (hp : p ∈ t) : p.2 ≤ L := by
    have h := hp.2.2.trans_le (measure_mono (subset_univ _))
    rw [← ENNReal.ofReal_mul ha.le, ← ENNReal.ofReal_toReal hν.ne] at h
    have hp0 : 0 < p.2 := hp.2.1
    have h' := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity : 0 ≤ a * (2 * p.2))).mp h
    apply le_of_lt
    dsimp [L]
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 2), lt_div_iff₀ ha]
    linarith
  have hw (τ : ℝ) (hτ : 3 < τ) :
      volume {x | ENNReal.ofReal a < realCenteredMaximal ν radii x} ≤
        ENNReal.ofReal (τ / a) * ν univ := by
    obtain ⟨u, hu, hd, hc⟩ :=
      Vitali.exists_disjoint_subfamily_covering_enlargement_ball t Prod.fst Prod.snd L ht τ hτ
    have hcount : u.Countable :=
      hd.countable_of_isOpen (fun _ _ => isOpen_ball)
        (fun p hp => ⟨p.1, mem_ball_self (hu hp).2.1⟩)
    have hsub : {x | ENNReal.ofReal a < realCenteredMaximal ν radii x} ⊆
        ⋃ p ∈ u, ball p.1 (τ * p.2) := by
      intro x hx
      obtain ⟨r, hr, hr₀, hval⟩ := (realCenteredMaximal_lt_iff ν radii x (ENNReal.ofReal a)).mp hx
      obtain ⟨p, hp, hcov⟩ := hc (x, r) ⟨hr, hr₀, hval⟩
      exact mem_iUnion₂.mpr ⟨p, hp, hcov (mem_ball_self hr₀)⟩
    refine (measure_mono hsub).trans ?_
    calc
      _ ≤ ∑' p : u, volume (ball p.val.1 (τ * p.val.2)) :=
        measure_biUnion_le volume hcount _
      _ ≤ ∑' p : u, ENNReal.ofReal (τ / a) * ν (ball p.val.1 p.val.2) := by
        apply ENNReal.tsum_le_tsum
        intro p
        have hτ' : 0 ≤ τ / a := by positivity
        have hval := ((hu p.property).2.2).le
        rw [Real.volume_ball]
        refine le_trans ?_ (mul_le_mul_of_nonneg_left hval zero_le)
        rw [← mul_assoc (ENNReal.ofReal (τ / a)), ← ENNReal.ofReal_mul hτ']
        have h : τ / a * a = τ := div_mul_cancel₀ _ ha.ne'
        rw [h, ← ENNReal.ofReal_mul (by positivity : 0 ≤ τ)]
        exact ENNReal.ofReal_le_ofReal (by linarith)
      _ = ENNReal.ofReal (τ / a) * ν (⋃ p ∈ u, ball p.1 p.2) := by
        rw [ENNReal.tsum_mul_left, measure_biUnion hcount hd (fun _ _ => measurableSet_ball)]
      _ ≤ _ := mul_le_mul_of_nonneg_left (measure_mono (subset_univ _)) zero_le
  let T (n : ℕ) := 3 + (1 / (n + 1 : ℝ))
  have hT : Tendsto T atTop (𝓝 3) := by
    have h := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    simpa [T] using tendsto_const_nhds.add h
  rw [← ENNReal.ofReal_toReal hν.ne, ← ENNReal.ofReal_mul (by positivity : 0 ≤ 3 / a)]
  have hC : Continuous (fun τ : ℝ => ENNReal.ofReal (τ / a * (ν univ).toReal)) :=
    ENNReal.continuous_ofReal.comp ((continuous_id.div_const a).mul_const _)
  apply le_of_tendsto_of_tendsto' tendsto_const_nhds (hC.continuousAt.tendsto.comp hT)
  intro n
  have hgt : 3 < T n := lt_add_of_pos_right _ (by positivity)
  simpa only [Function.comp_apply, ENNReal.ofReal_mul (show 0 ≤ T n / a from by positivity),
    ENNReal.ofReal_toReal hν.ne] using hw (T n) hgt

/-- Centered Hardy–Littlewood maximal averages of a nonnegative real input. -/
def realHardyLittlewood (radii : Set ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ≥0∞ :=
  realCenteredMaximal (volume.withDensity (fun y => ENNReal.ofReal (f y))) radii x

theorem realHardyLittlewood_measurable (radii : Set ℝ) (f : ℝ → ℝ) :
    Measurable (realHardyLittlewood radii f) :=
  realCenteredMaximal_measurable _ _

theorem realHardyLittlewood_weak (radii : Set ℝ) (f : ℝ → ℝ)
    (hf : (∫⁻ y, ENNReal.ofReal (f y)) < ⊤) {a : ℝ} (ha : 0 < a) :
    volume {x | ENNReal.ofReal a < realHardyLittlewood radii f x} ≤
      ENNReal.ofReal (3 / a) * ∫⁻ y, ENNReal.ofReal (f y) := by
  let ν := volume.withDensity (fun y => ENNReal.ofReal (f y))
  have hν : ν univ = ∫⁻ y, ENNReal.ofReal (f y) := by
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  rw [← hν]
  exact realCenteredMaximal_weak ν (hν.symm ▸ hf) radii ha

private theorem realHardyLittlewood_finite_of_integral (radii : Set ℝ) (f : ℝ → ℝ)
    (hf : (∫⁻ y, ENNReal.ofReal (f y)) < ⊤) :
    ∀ᵐ x, realHardyLittlewood radii f x < ⊤ := by
  apply ae_iff.mpr
  let V := ∫⁻ y, ENNReal.ofReal (f y)
  have h (n : ℕ) : volume {x | ¬realHardyLittlewood radii f x < ⊤} ≤
      ENNReal.ofReal (3 * V.toReal * (1 / (n + 1 : ℝ))) := by
    have ha : 0 < (n + 1 : ℝ) := by positivity
    have hs : {x | ¬realHardyLittlewood radii f x < ⊤} ⊆
        {x | ENNReal.ofReal (n + 1 : ℝ) < realHardyLittlewood radii f x} := by
      intro x hx
      have hx' : realHardyLittlewood radii f x = ⊤ := top_unique (not_lt.mp hx)
      change ENNReal.ofReal (n + 1 : ℝ) < realHardyLittlewood radii f x
      rw [hx']
      exact ENNReal.ofReal_lt_top
    refine (measure_mono hs).trans ((realHardyLittlewood_weak radii f hf ha).trans_eq ?_)
    change ENNReal.ofReal (3 / (n + 1 : ℝ)) * V = _
    have hV : V ≠ ⊤ := hf.ne
    rw [← ENNReal.ofReal_toReal hV, ← ENNReal.ofReal_mul (by positivity : 0 ≤ 3 / (n + 1 : ℝ))]
    simp only [ENNReal.toReal_ofReal ENNReal.toReal_nonneg]
    congr 1
    ring
  apply nonpos_iff_eq_zero.mp
  have hlim := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (3 * V.toReal)
  have hl : Tendsto (fun n : ℕ => ENNReal.ofReal (3 * V.toReal * (1 / (n + 1 : ℝ)))) atTop
      (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero, ENNReal.ofReal_zero] using
      (ENNReal.continuous_ofReal.continuousAt.tendsto.comp hlim)
  exact le_of_tendsto_of_tendsto' tendsto_const_nhds hl h

private theorem realHardyLittlewood_le_truncation_add
    (radii : Set ℝ) (f : ℝ → ℝ) (hf : Measurable f) (t : ℝ) (x : ℝ) :
    let F := {y | t < f y}.indicator f
    realHardyLittlewood radii f x ≤ realHardyLittlewood radii F x + ENNReal.ofReal t := by
  let F := {y | t < f y}.indicator f
  have hmeas : Measurable F := hf.indicator (measurableSet_lt measurable_const hf)
  have hpoint (y : ℝ) : ENNReal.ofReal (f y) ≤ ENNReal.ofReal (F y) + ENNReal.ofReal t := by
    by_cases hy : t < f y
    · rw [show F y = f y from indicator_of_mem (show y ∈ {z | t < f z} from hy) f]
      exact le_self_add
    · rw [show F y = 0 from indicator_of_notMem (show y ∉ {z | t < f z} from hy) f, ENNReal.ofReal_zero, zero_add]
      exact ENNReal.ofReal_le_ofReal (not_lt.mp hy)
  simp only [realHardyLittlewood, realCenteredMaximal]
  refine iSup_le fun r => iSup_le fun hr => iSup_le fun hr₀ => ?_
  have h := lintegral_mono (μ := volume.restrict (ball x r)) hpoint
  rw [lintegral_add_left hmeas.ennreal_ofReal, setLIntegral_const, Real.volume_ball] at h
  change _ ≤ realHardyLittlewood radii F x + ENNReal.ofReal t
  rw [withDensity_apply _ measurableSet_ball]
  refine (ENNReal.div_le_div_right h _).trans ?_
  rw [ENNReal.add_div, ENNReal.mul_div_cancel_right
    (show 0 < ENNReal.ofReal (2 * r) by positivity).ne' ENNReal.ofReal_ne_top]
  apply add_le_add_left
  rw [← withDensity_apply _ measurableSet_ball]
  exact le_iSup_of_le r (le_iSup_of_le hr (le_iSup_of_le hr₀ le_rfl))

private theorem realHardyLittlewood_trunc_integral_finite (f : ℝ → ℝ)
    (hn : ∀ x, 0 ≤ f x) {p t : ℝ} (hp : 1 < p) (ht : 0 < t)
    (hpint : (∫⁻ y, ENNReal.ofReal (f y ^ p)) < ⊤) :
    (∫⁻ y, ENNReal.ofReal ({y | t < f y}.indicator f y)) < ⊤ := by
  let C := (t ^ (p - 1))⁻¹
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hmul (y : ℝ) :
      ENNReal.ofReal ({y | t < f y}.indicator f y) ≤
        ENNReal.ofReal C * ENNReal.ofReal (f y ^ p) := by
    rw [← ENNReal.ofReal_mul hC]
    apply ENNReal.ofReal_le_ofReal
    by_cases h : t < f y
    · rw [show {y | t < f y}.indicator f y = f y from indicator_of_mem (show y ∈ {z | t < f z} from h) f]
      have he : f y ^ p = f y * f y ^ (p - 1) := by
        nth_rewrite 1 [← show 1 + (p - 1) = p by ring]
        rw [Real.rpow_add (ht.trans h), Real.rpow_one]
      have hm : t ^ (p - 1) * f y ≤ f y ^ p := by
        rw [he, mul_comm (t ^ (p - 1))]
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow ht.le h.le (sub_nonneg.mpr hp.le)) (hn y)
      exact (le_inv_mul_iff₀ (Real.rpow_pos_of_pos ht _)).mpr hm
    · rw [show {y | t < f y}.indicator f y = 0 from indicator_of_notMem (show y ∉ {z | t < f z} from h) f]
      exact mul_nonneg hC (Real.rpow_nonneg (hn y) _)
  refine (lintegral_mono hmul).trans_lt ?_
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hpint

/-- The strong estimate over the full range of radii, with the constant
from (A.5.1.4). The result holds for any fixed set of admissible radii. -/
theorem realHardyLittlewood_rpow (radii : Set ℝ) (f : ℝ → ℝ)
    (hf : Measurable f) (hn : ∀ x, 0 ≤ f x) {p : ℝ} (hp : 1 < p)
    (hfp : (∫⁻ y, ENNReal.ofReal (f y ^ p)) < ⊤) :
    (∫⁻ x, realHardyLittlewood radii f x ^ p) ≤
      ENNReal.ofReal (2 ^ p * 3 * p / (p - 1)) * ∫⁻ x, ENNReal.ofReal (f x ^ p) := by
  let M := realHardyLittlewood radii f
  let g := fun x => (M x).toReal
  have hg : Measurable g := (realHardyLittlewood_measurable radii f).ennreal_toReal
  have hfinite : ∀ᵐ x, M x < ⊤ := by
    let F := {y | (1 : ℝ) < f y}.indicator f
    have hF := realHardyLittlewood_finite_of_integral radii F
      (realHardyLittlewood_trunc_integral_finite f hn hp zero_lt_one hfp)
    filter_upwards [hF] with x hx
    exact (realHardyLittlewood_le_truncation_add radii f hf 1 x).trans_lt
      (ENNReal.add_lt_top.mpr ⟨hx, ENNReal.ofReal_lt_top⟩)
  have hweak (a : ℝ) (ha : 0 < a) :
      volume {x | a < g x} ≤ ENNReal.ofReal (6 / a) *
        ∫⁻ y in {x | (1 / 2 : ℝ) * a < f x}, ENNReal.ofReal (f y) := by
    let t := (1 / 2 : ℝ) * a
    let F := {y | t < f y}.indicator f
    have ht : 0 < t := by positivity
    have hs : {x | a < g x} ⊆ {x | ENNReal.ofReal t < realHardyLittlewood radii F x} := by
      intro x hx
      have h₁ : ENNReal.ofReal a < M x := by
        have hx0 : a < (M x).toReal := hx
        have hne : M x ≠ ⊤ := fun he => by simp [he, not_lt.mpr ha.le] at hx0
        rw [← ENNReal.ofReal_toReal hne]
        exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ha.le).mpr hx0
      by_contra! h
      have hadd : ENNReal.ofReal t + ENNReal.ofReal t = ENNReal.ofReal a := by
        rw [← ENNReal.ofReal_add ht.le ht.le]
        congr 1
        dsimp [t]
        ring
      have hleF : realHardyLittlewood radii F x ≤ ENNReal.ofReal t := not_lt.mp h
      have hle := (realHardyLittlewood_le_truncation_add radii f hf t x).trans
        (add_le_add_left hleF (ENNReal.ofReal t))
      exact (not_lt_of_ge (hadd ▸ hle)) h₁
    refine (measure_mono hs).trans ((realHardyLittlewood_weak radii F
      (realHardyLittlewood_trunc_integral_finite f hn hp ht hfp) ht).trans_eq ?_)
    have hcoeff : 3 / t = 6 / a := by dsimp [t]; ring
    rw [hcoeff, ← lintegral_indicator (measurableSet_lt measurable_const hf)]
    congr 2 with y
    change ENNReal.ofReal (F y) = {z | t < f z}.indicator (fun y => ENNReal.ofReal (f y)) y
    by_cases h : y ∈ {z | t < f z}
    · dsimp only [F]
      rw [indicator_of_mem h, indicator_of_mem h]
    · dsimp only [F]
      rw [indicator_of_notMem h, indicator_of_notMem h, ENNReal.ofReal_zero]
  have hEq : ∀ᵐ x, M x ^ p = ENNReal.ofReal (g x ^ p) := by
    filter_upwards [hfinite] with x hx
    rw [← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg
      ((zero_lt_one.trans hp).le), ENNReal.ofReal_toReal hx.ne]
  rw [lintegral_congr_ae hEq]
  refine (lintegral_rpow_le_of_truncated_weak_bound volume volume hg hf
    (fun _ => ENNReal.toReal_nonneg) hn hp (by norm_num : 0 < (1 / 2 : ℝ))
    (by norm_num : 0 ≤ (6 : ℝ)) hweak).trans_eq ?_
  congr 2
  rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.inv_rpow (by norm_num)]
  have hpow : (2 : ℝ) ^ p = 2 * 2 ^ (p - 1) := by
    nth_rewrite 1 [← show 1 + (p - 1) = p by ring]
    rw [Real.rpow_add (by norm_num : 0 < (2 : ℝ)), Real.rpow_one]
  rw [hpow]
  field_simp [(Real.rpow_pos_of_pos (by norm_num : 0 < (2 : ℝ)) (p - 1)).ne', (sub_pos.mpr hp).ne']
  ring

/-- Local integrability suffices for almost-everywhere finiteness when the
admissible radii have a finite upper bound. -/
theorem realHardyLittlewood_finite_local (radii : Set ℝ) (f : ℝ → ℝ) {R : ℝ}
    (hr : ∀ r ∈ radii, r ≤ R)
    (hf : ∀ n : ℕ, (∫⁻ y in Icc (-(n : ℝ) - R) ((n : ℝ) + R),
      ENNReal.ofReal (f y)) < ⊤) :
    ∀ᵐ x, realHardyLittlewood radii f x < ⊤ := by
  let B (n : ℕ) := Icc (-(n : ℝ)) (n : ℝ)
  let K (n : ℕ) := Icc (-(n : ℝ) - R) ((n : ℝ) + R)
  let F (n : ℕ) := (K n).indicator f
  have hF (n : ℕ) : (∫⁻ y, ENNReal.ofReal (F n y)) < ⊤ := by
    have he : (fun y => ENNReal.ofReal (F n y)) = (K n).indicator (fun y => ENNReal.ofReal (f y)) := by
      funext y
      by_cases hy : y ∈ K n
      · dsimp only [F]
        rw [indicator_of_mem hy, indicator_of_mem hy]
      · dsimp only [F]
        rw [indicator_of_notMem hy, indicator_of_notMem hy, ENNReal.ofReal_zero]
    rw [he, lintegral_indicator measurableSet_Icc]
    exact hf n
  have hEq (n : ℕ) (x : ℝ) (hx : x ∈ B n) :
      realHardyLittlewood radii f x = realHardyLittlewood radii (F n) x := by
    simp only [realHardyLittlewood, realCenteredMaximal]
    congr 1 with r
    congr 1 with hrad
    congr 1 with hpos
    congr 1
    rw [withDensity_apply _ measurableSet_ball, withDensity_apply _ measurableSet_ball]
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
    have h : |y - x| < r := by rwa [mem_ball, Real.dist_eq] at hy
    have hyK : y ∈ K n := by
      have hrad' := hr r hrad
      exact ⟨by linarith [hx.1, (abs_lt.mp h).1], by linarith [hx.2, (abs_lt.mp h).2]⟩
    dsimp only [F]
    rw [indicator_of_mem hyK]
  have hfinite (n : ℕ) : ∀ᵐ x, realHardyLittlewood radii (F n) x < ⊤ :=
    realHardyLittlewood_finite_of_integral radii (F n) (hF n)
  filter_upwards [ae_all_iff.mpr hfinite] with x hx
  obtain ⟨n, hn⟩ := exists_nat_gt |x|
  exact (hEq n x (abs_le.mp hn.le)).symm ▸ hx n

/-- For the unbounded set of radii the printed local assertion fails even
for a smooth polynomial with all local logarithmic moments finite. -/
theorem realHardyLittlewood_quadratic_unbounded (x : ℝ) :
    realHardyLittlewood univ (fun y => y ^ 2) x = ⊤ := by
  have hvalue (r : ℝ) (hr : 0 < r) :
      volume.withDensity (fun y : ℝ => ENNReal.ofReal (y ^ 2)) (ball x r) /
        ENNReal.ofReal (2 * r) = ENNReal.ofReal (x ^ 2 + r ^ 2 / 3) := by
    have hi : IntegrableOn (fun y : ℝ => y ^ 2) (Icc (x - r) (x + r)) volume :=
      ContinuousOn.integrableOn_compact isCompact_Icc ((continuous_id' : Continuous (fun y : ℝ => y)).pow _).continuousOn
    have he : volume.restrict (ball x r) = volume.restrict (Icc (x - r) (x + r)) := by
      rw [Real.ball_eq_Ioo, Measure.restrict_congr_set Ioo_ae_eq_Ioc,
        Measure.restrict_congr_set Ioc_ae_eq_Icc]
    rw [withDensity_apply _ measurableSet_ball, he]
    rw [← ofReal_integral_eq_lintegral_ofReal hi (.of_forall fun y => sq_nonneg y)]
    rw [← ENNReal.ofReal_div_of_pos (by positivity : 0 < 2 * r)]
    congr 1
    simpa [symmetricQuadraticAverage, div_eq_mul_inv, mul_comm] using
      symmetricQuadraticAverage_eq hr x
  apply top_unique
  apply le_of_not_gt
  intro h
  let a := (realHardyLittlewood univ (fun y => y ^ 2) x).toReal
  have ha : 0 ≤ a := ENNReal.toReal_nonneg
  let r := 3 * (a + 1)
  have hr : 0 < r := by dsimp [r]; positivity
  have hlarge : a < x ^ 2 + r ^ 2 / 3 := by
    dsimp [r]
    nlinarith [sq_nonneg x, sq_nonneg a]
  have hlarge' : ENNReal.ofReal a < ENNReal.ofReal (x ^ 2 + r ^ 2 / 3) :=
    (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ha).mpr hlarge
  rw [← hvalue r hr] at hlarge'
  have hd := (ENNReal.lt_div_iff_mul_lt (Or.inl
    (show 0 < ENNReal.ofReal (2 * r) by positivity).ne') (Or.inl ENNReal.ofReal_ne_top)).mp hlarge'
  have hi := (realCenteredMaximal_lt_iff _ _ x (ENNReal.ofReal a)).mpr
    ⟨r, mem_univ r, hr, hd⟩
  change ENNReal.ofReal a < realHardyLittlewood univ (fun y => y ^ 2) x at hi
  rw [ENNReal.ofReal_toReal h.ne] at hi
  exact (lt_irrefl _) hi

/-- A.5.1.1 for complex-valued functions. The local clause uses bounded radii.
The weak and strong estimates here use all positive radii. -/
theorem hardyLittlewood_real (f : ℝ → ℂ) (hfm : Measurable f) :
    let M := realHardyLittlewood univ (fun y => ‖f y‖)
    let Mloc := realHardyLittlewood (Iic 1) (fun y => ‖f y‖)
    Measurable M ∧ Measurable Mloc ∧
      (LocallyIntegrable f volume → ∀ᵐ x, Mloc x < ⊤) ∧
      (Integrable f volume → ∀ a > (0 : ℝ),
        volume {x | ENNReal.ofReal a < M x} ≤ ENNReal.ofReal (3 / a * ∫ y, ‖f y‖)) ∧
      ∀ p > (1 : ℝ), MemLp f (ENNReal.ofReal p) volume →
        (∫⁻ x, M x ^ p) ≤ ENNReal.ofReal (2 ^ p * 3 * p / (p - 1)) *
          ∫⁻ y, ENNReal.ofReal (‖f y‖ ^ p) := by
  refine ⟨realHardyLittlewood_measurable _ _, realHardyLittlewood_measurable _ _, ?_, ?_, ?_⟩
  · intro hf
    apply realHardyLittlewood_finite_local _ _ (R := 1)
      (fun _ hr => hr)
    exact fun _ => (hf.integrableOn_isCompact isCompact_Icc).norm.lintegral_lt_top
  · intro hf a ha
    have h := realHardyLittlewood_weak univ (fun y => ‖f y‖) hf.norm.lintegral_lt_top ha
    rw [← ofReal_integral_eq_lintegral_ofReal hf.norm (.of_forall fun _ => norm_nonneg _),
      ← ENNReal.ofReal_mul (by positivity : 0 ≤ 3 / a)] at h
    exact h
  · intro p hp hfp
    have hi : Integrable (fun y => ‖f y‖ ^ p) volume := by
      simpa only [ENNReal.toReal_ofReal (zero_lt_one.trans hp).le] using
        hfp.integrable_norm_rpow (by positivity) ENNReal.ofReal_ne_top
    exact realHardyLittlewood_rpow univ (fun y => ‖f y‖) hfm.norm (fun _ => norm_nonneg _) hp
      hi.lintegral_lt_top

end

end Masullo
