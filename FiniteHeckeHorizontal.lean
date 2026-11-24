import FiniteHeckeLogDerivative
import DiskMinimumModulus

open Filter Function IsDedekindDomain MeasureTheory Metric NumberField Set Topology
open scoped Classical ENNReal NumberField

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

private abbrev Place := HeightOneSpectrum (𝓞 F)
private abbrev K := normOneIdeleClass F

variable (χ : PontryaginDual (IdeleClass F)) (S : Finset (Place F))

private abbrev coefficient := heckeEulerCoefficient F χ (chosenFiniteUniformizer F)
private abbrev factor := heckeEulerFactor F (coefficient F χ)

private abbrev reciprocalLocal (v : Place F) (z : ℂ) : ℂ :=
  1 - coefficient F χ v * (v.asIdeal.absNorm : ℂ) ^ (-z)

/-- The factor that removes the finitely many specified finite Euler factors. -/
def finiteHeckeOmissionMultiplier (z : ℂ) : ℂ :=
  ∏ v ∈ S, reciprocalLocal F χ v z

/-- The Euler product outside the specified finite set. -/
def manuscriptFiniteHeckeEulerOutside (z : ℂ) : ℂ :=
  ∏' v : {v : Place F // v ∉ S}, factor F χ v.val z

private theorem local_q_pos (v : Place F) : 0 < (v.asIdeal.absNorm : ℝ) := by
  exact_mod_cast zero_lt_one.trans (NumberField.HeightOneSpectrum.one_lt_absNorm v)

private theorem local_one_le_q (v : Place F) : 1 < (v.asIdeal.absNorm : ℝ) := by
  exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v

private theorem norm_local_term_le (v : Place F) (z : ℂ) :
    ‖coefficient F χ v * (v.asIdeal.absNorm : ℂ) ^ (-z)‖ ≤ (v.asIdeal.absNorm : ℝ) ^ (-z.re) := by
  rw [norm_mul, ← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos (local_q_pos F v),
    Complex.neg_re]
  exact mul_le_of_le_one_left (Real.rpow_nonneg (local_q_pos F v).le _)
    (norm_heckeEulerCoefficient_le_one F χ _ _)

theorem finiteHeckeOmissionMultiplier_analytic (z : ℂ) :
    AnalyticAt ℂ (finiteHeckeOmissionMultiplier F χ S) z := by
  apply S.analyticAt_fun_prod
  intro v _
  have hq : (v.asIdeal.absNorm : ℂ) ≠ 0 := by exact_mod_cast (local_q_pos F v).ne'
  letI : NeZero (v.asIdeal.absNorm : ℂ) := ⟨hq⟩
  have hpow : AnalyticAt ℂ (fun w : ℂ ↦ (v.asIdeal.absNorm : ℂ) ^ w) (-z) :=
    (differentiable_const_cpow_of_neZero _).analyticAt _
  exact analyticAt_const.sub (analyticAt_const.mul (hpow.comp (f := fun w : ℂ ↦ -w) analyticAt_id.neg))

theorem finiteHeckeOmissionMultiplier_norm_le (a : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, a ≤ z.re → ‖finiteHeckeOmissionMultiplier F χ S z‖ ≤ C := by
  refine ⟨∏ v ∈ S, (1 + (v.asIdeal.absNorm : ℝ) ^ (-a)), by positivity, fun z hz ↦ ?_⟩
  rw [finiteHeckeOmissionMultiplier, norm_prod]
  exact Finset.prod_le_prod (fun _ _ ↦ norm_nonneg _) (fun v _ ↦ by
    have h := (norm_sub_le (1 : ℂ) (coefficient F χ v * (v.asIdeal.absNorm : ℂ) ^ (-z)))
    rw [norm_one] at h
    exact h.trans (add_le_add_right ((norm_local_term_le F χ v z).trans
      (Real.rpow_le_rpow_of_exponent_le (local_one_le_q F v).le (neg_le_neg hz))) 1))

theorem finiteHeckeOmissionMultiplier_norm_ge_of_re_ge {a : ℝ} (ha : 0 < a) :
    ∃ c : ℝ, 0 < c ∧ ∀ z : ℂ, a ≤ z.re → c ≤ ‖finiteHeckeOmissionMultiplier F χ S z‖ := by
  have hpos (v : Place F) : 0 < 1 - (v.asIdeal.absNorm : ℝ) ^ (-a) :=
    sub_pos.mpr (Real.rpow_lt_one_of_one_lt_of_neg (local_one_le_q F v) (neg_lt_zero.mpr ha))
  refine ⟨∏ v ∈ S, (1 - (v.asIdeal.absNorm : ℝ) ^ (-a)),
    Finset.prod_pos (fun v _ ↦ hpos v), fun z hz ↦ ?_⟩
  rw [finiteHeckeOmissionMultiplier, norm_prod]
  apply Finset.prod_le_prod (fun v _ ↦ (hpos v).le)
  intro v _
  have h := (norm_local_term_le F χ v z).trans
    (Real.rpow_le_rpow_of_exponent_le (local_one_le_q F v).le (neg_le_neg hz))
  change ‖(1 : ℂ) - _‖ ≥ _
  have h' := norm_sub_norm_le (1 : ℂ) (coefficient F χ v * (v.asIdeal.absNorm : ℂ) ^ (-z))
  rw [norm_one] at h'
  exact (sub_le_sub_left h _).trans h'

theorem finiteHeckeOmissionMultiplier_norm_ge_two :
    ∃ c : ℝ, 0 < c ∧ ∀ y : ℝ, c ≤ ‖finiteHeckeOmissionMultiplier F χ S ⟨2, y⟩‖ := by
  obtain ⟨c, hc, h⟩ := finiteHeckeOmissionMultiplier_norm_ge_of_re_ge F χ S (by norm_num : (0 : ℝ) < 2)
  exact ⟨c, hc, fun y ↦ h ⟨2, y⟩ le_rfl⟩

private theorem finite_mul_tprod_compl {ι : Type*} (P : Finset ι) (a : ι → ℂ)
    (h : Summable fun i ↦ ‖a i - 1‖) :
    (∏ i ∈ P, a i) * (∏' i : {i // i ∉ P}, a i.val) = ∏' i, a i := by
  have hs : Summable (fun i : {i // i ∉ P} ↦ ‖a i.val - 1‖) :=
    h.comp_injective Subtype.val_injective
  have ht : Multipliable (fun i : {i // i ∉ P} ↦ a i.val) := by
    simpa only [add_sub_cancel] using multipliable_one_add_of_summable hs
  have hfin : Multipliable (fun i : (P : Set ι) ↦ a i.val) := Multipliable.of_finite
  have he := hfin.tprod_mul_tprod_compl ht
  rw [Finset.tprod_subtype'] at he
  exact he

theorem manuscriptFiniteHeckeEulerOutside_eq {z : ℂ} (hz : 1 < z.re) :
    manuscriptFiniteHeckeEulerOutside F χ S z =
      finiteHeckeOmissionMultiplier F χ S z * manuscriptFiniteHeckeEuler F χ z := by
  obtain ⟨g, hg⟩ := (heckeEulerFactor_summableUniformlyOn F (coefficient F χ)
    (norm_heckeEulerCoefficient_le_one F χ _) {z} isCompact_singleton (by simpa using hz)).exists
  have he := finite_mul_tprod_compl S (fun v ↦ factor F χ v z) (hg.hasSum (mem_singleton z)).summable
  change (∏ v ∈ S, factor F χ v z) * manuscriptFiniteHeckeEulerOutside F χ S z =
    manuscriptFiniteHeckeEuler F χ z at he
  have hne (v : Place F) : reciprocalLocal F χ v z ≠ 0 := by
    intro h
    have hh := (norm_local_term_le F χ v z).trans_lt (Real.rpow_lt_one_of_one_lt_of_neg
      (local_one_le_q F v) (by linarith))
    rw [← sub_eq_zero.mp h, norm_one] at hh
    exact lt_irrefl _ hh
  rw [← he, ← mul_assoc, finiteHeckeOmissionMultiplier, ← Finset.prod_mul_distrib]
  have hprod : (∏ v ∈ S, reciprocalLocal F χ v z * factor F χ v z) = 1 :=
    Finset.prod_eq_one (fun v _ ↦ mul_inv_cancel₀ (hne v))
  rw [hprod, one_mul]

local instance horizontalNormOneMeasurable : MeasurableSpace (K F) := borel _
local instance horizontalNormOneBorel : BorelSpace (K F) := ⟨rfl⟩
local instance horizontalIdeleMeasurable : MeasurableSpace (Idele F) := borel _
local instance horizontalIdeleBorel : BorelSpace (Idele F) := ⟨rfl⟩

variable (ν : Measure (K F)) [ν.IsHaarMeasure]
variable (η : Measure (Idele F)) [η.IsHaarMeasure]
variable [∀ v : Place F, MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : Place F, BorelSpace (v.adicCompletion F)ˣ]
  (μ : ∀ v : Place F, Measure (v.adicCompletion F)ˣ)
  [∀ v : Place F, (μ v).IsHaarMeasure] [∀ v : Place F, SigmaFinite (μ v)]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]
variable (hν : IsWeilQuotientMeasure (principalIdeles F) η Measure.count (globalClassMeasure F ν))

include μ hν in
theorem exists_manuscriptFiniteHeckeOutside_polynomial_strips :
    ∃ (L : ℂ → ℂ) (T : ℝ) (c : ℝ), 0 < c ∧ MeromorphicOn L univ ∧
      EqOn L (manuscriptFiniteHeckeEulerOutside F χ S) {z | 1 < z.re} ∧
      (∀ y : ℝ, c ≤ ‖L ⟨2, y⟩‖) ∧
      (∀ z : ℂ, T ≤ |z.im| → AnalyticAt ℂ L z) ∧
      ∀ a b : ℝ, a < b → ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧
        ∀ z : ℂ, z.re ∈ Icc a b → T ≤ |z.im| → ‖L z‖ ≤ C * (1 + |z.im|) ^ N := by
  obtain ⟨L, t, _, hm, he, ha, hg⟩ := exists_manuscriptFiniteHecke_polynomial_strips F ν η μ hν χ
  let P := finiteHeckeOmissionMultiplier F χ S
  obtain ⟨c, hc, hC⟩ := manuscriptFiniteHecke_norm_ge_two F
  obtain ⟨d, hd, hD⟩ := finiteHeckeOmissionMultiplier_norm_ge_two F χ S
  refine ⟨P * L, 1 + |t|, d * c, mul_pos hd hc,
    fun z hz ↦ (finiteHeckeOmissionMultiplier_analytic F χ S z).meromorphicAt.mul (hm z hz),
    ?_, ?_, ?_, ?_⟩
  · intro z hz
    change P z * L z = _
    rw [he hz, manuscriptFiniteHeckeEulerOutside_eq F χ S hz]
  · intro y
    change d * c ≤ ‖P ⟨2, y⟩ * L ⟨2, y⟩‖
    rw [norm_mul, he (show (1 : ℝ) < 2 by norm_num)]
    exact mul_le_mul (hD y) (hC χ y) hc.le (norm_nonneg _)
  · intro z hz
    apply (finiteHeckeOmissionMultiplier_analytic F χ S z).mul
    apply ha z <;> intro e
    · have hi := congrArg Complex.im e
      simp [Complex.mul_im] at hi
      rw [hi] at hz
      linarith
    · have hi := congrArg Complex.im e
      simp [Complex.add_im, Complex.mul_im] at hi
      rw [hi] at hz
      linarith
  · intro a b hab
    obtain ⟨A, hA, hP⟩ := finiteHeckeOmissionMultiplier_norm_le F χ S a
    obtain ⟨B, n, hB, hL⟩ := hg a b hab
    refine ⟨A * B, n, mul_nonneg hA hB, fun z hz ht ↦ ?_⟩
    change ‖P z * L z‖ ≤ _
    rw [norm_mul, mul_assoc]
    exact mul_le_mul (hP z hz.1) (hL z hz ht) (norm_nonneg _) hA

private theorem horizontal_lower_bound_from_disk {L : ℂ → ℂ} {c T sign : ℝ} {N : ℕ}
    (hc : 0 < c) (hT : 1 < T) (hTc : c⁻¹ ≤ T) (hN : 0 < N) (hsign : |sign| = 1)
    (hcenter : c ≤ ‖L ⟨2, sign * T⟩‖)
    (hAn : AnalyticOnNhd ℂ L (closedBall ⟨2, sign * T⟩ 16))
    (hRatio : ∀ w ∈ closedBall (⟨2, sign * T⟩ : ℂ) 16, ‖L w / L ⟨2, sign * T⟩‖ ≤ T ^ N)
    {B : ℝ} (hB : 1 < B) :
    let A : ℝ := 2 * (N : ℝ) + (N : ℝ) / Real.log (3 / 2) * (Real.log 16 + 2) + 1
    ∃ E : Set ℝ, MeasurableSet E ∧ E ⊆ Icc T (T + 1) ∧ volume E = ENNReal.ofReal (1 / B) ∧
      ∀ t ∈ Icc T (T + 1) \ E, ∀ x ∈ Icc (-1 : ℝ) 2,
        T ^ (-(A * B)) < ‖L ⟨x, sign * t⟩‖ := by
  intro A
  let center : ℂ := ⟨2, sign * T⟩
  let k (w : ℂ) := center + (16 : ℂ) * w
  let f (w : ℂ) := L (k w) / L center
  have hcenter₀ : L center ≠ 0 := norm_pos_iff.mp (hc.trans_le hcenter)
  have hk (w : ℂ) (hw : ‖w‖ ≤ 1) : k w ∈ closedBall center 16 := by
    rw [mem_closedBall_iff_norm]
    dsimp [k]
    rw [add_sub_cancel_left, norm_mul, show ‖(16 : ℂ)‖ = 16 by norm_num]
    linarith
  have hfAn : AnalyticOnNhd ℂ f (closedBall 0 1) := by
    intro w hw
    have ha : AnalyticAt ℂ k w := analyticAt_const.add (analyticAt_const.mul analyticAt_id)
    exact ((hAn _ (hk w (by simpa using hw))).comp (f := k) ha).div analyticAt_const hcenter₀
  have hf₀ : f 0 = 1 := by simp [f, k, hcenter₀]
  have hfBound (w : ℂ) (hw : ‖w‖ ≤ 3 / 4) : ‖f w‖ ≤ T ^ N :=
    hRatio _ (hk w (hw.trans (by norm_num)))
  obtain ⟨E, hE, hEI, hEV, hLow⟩ := disk_horizontal_minimum_modulus hT hN hfAn hf₀ hfBound hsign hB
  refine ⟨E, hE, hEI, hEV, fun t ht x hx ↦ ?_⟩
  have h := hLow t ht x hx
  rw [show 2 * (N : ℝ) + (N : ℝ) / Real.log (3 / 2) * (Real.log 16 + 2) = A - 1 by dsimp [A]; ring] at h
  have hkz : k ((⟨x - 2, sign * (t - T)⟩ : ℂ) / 16) = ⟨x, sign * t⟩ := by
    dsimp [k]
    rw [← mul_div_assoc, mul_div_cancel_left₀ _ (by norm_num)]
    apply Complex.ext
    · simp [center]
    · simp [center]; ring
  dsimp only [f] at h
  rw [hkz, norm_div] at h
  have hT₀ := zero_lt_one.trans hT
  have hNorm : 0 < ‖L center‖ := hc.trans_le hcenter
  have hCenterPow : T ^ (-B) ≤ ‖L center‖ := calc
    _ ≤ T ^ (-(1 : ℝ)) := Real.rpow_le_rpow_of_exponent_le hT.le (by linarith)
    _ = T⁻¹ := Real.rpow_neg_one _
    _ ≤ c := (inv_le_comm₀ hT₀ hc).mpr hTc
    _ ≤ _ := hcenter
  calc
    T ^ (-(A * B)) = T ^ (-((A - 1) * B)) * T ^ (-B) := by
      rw [← Real.rpow_add hT₀]
      congr 1
      ring
    _ ≤ T ^ (-((A - 1) * B)) * ‖L center‖ :=
      mul_le_mul_of_nonneg_left hCenterPow (Real.rpow_nonneg hT₀.le _)
    _ < ‖L ⟨x, sign * t⟩‖ := (lt_div_iff₀ hNorm).mp h

set_option maxHeartbeats 500000 in
include μ hν in
/-- Theorem B.6.1.7, with the finite places recorded in `S`. The height
threshold works for every size of the exceptional set. -/
theorem exists_manuscriptFiniteHeckeOutside_horizontal_lower_bounds :
    ∃ (L : ℂ → ℂ) (A U : ℝ), 0 < A ∧ MeromorphicOn L univ ∧
      EqOn L (manuscriptFiniteHeckeEulerOutside F χ S) {z | 1 < z.re} ∧
      (∃ T₀ : ℝ, (∀ z : ℂ, T₀ ≤ |z.im| → AnalyticAt ℂ L z) ∧
        ∀ a b : ℝ, a < b → ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧
          ∀ z : ℂ, z.re ∈ Icc a b → T₀ ≤ |z.im| → ‖L z‖ ≤ C * (1 + |z.im|) ^ N) ∧
      (∀ sign : ℝ, |sign| = 1 → ∀ T ≥ U, ∃ t ∈ Ioo T (T + 1), ∀ x ∈ Icc (-1 : ℝ) 2,
        |t| ^ (-A) < ‖L ⟨x, sign * t⟩‖) ∧
      ∀ sign : ℝ, |sign| = 1 → ∀ T ≥ U, ∀ B > (1 : ℝ),
        ∃ E : Set ℝ, MeasurableSet E ∧ E ⊆ Icc T (T + 1) ∧ volume E = ENNReal.ofReal (1 / B) ∧
          ∀ t ∈ Icc T (T + 1) \ E, ∀ x ∈ Icc (-1 : ℝ) 2, T ^ (-(A * B)) < ‖L ⟨x, sign * t⟩‖ := by
  obtain ⟨L, T₀, c, hc, hm, he, hcenter, han, hp⟩ :=
    exists_manuscriptFiniteHeckeOutside_polynomial_strips F χ S ν η μ hν
  obtain ⟨N, T₁, hN, hT₁, hD⟩ := disk_bound_of_polynomial_strip (by norm_num : (0 : ℝ) < 16)
    hc (fun y _ ↦ hcenter y) han (hp (2 - 16) (2 + 16) (by norm_num))
  let U := max T₁ c⁻¹
  let A₀ : ℝ := 2 * (N : ℝ) + (N : ℝ) / Real.log (3 / 2) * (Real.log 16 + 2) + 1
  have hA : 0 < A₀ := by
    dsimp [A₀]
    have h := Real.log_pos (by norm_num : (1 : ℝ) < 3 / 2)
    have h' := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 16)
    positivity
  have hVol (sign : ℝ) (hsign : |sign| = 1) (T : ℝ) (hT : U ≤ T) {B : ℝ} (hB : 1 < B) :
      ∃ E : Set ℝ, MeasurableSet E ∧ E ⊆ Icc T (T + 1) ∧ volume E = ENNReal.ofReal (1 / B) ∧
        ∀ t ∈ Icc T (T + 1) \ E, ∀ x ∈ Icc (-1 : ℝ) 2, T ^ (-(A₀ * B)) < ‖L ⟨x, sign * t⟩‖ := by
    have hT' := (le_max_left T₁ (c⁻¹)).trans hT
    have hT₀' := one_lt_two.trans_le (hT₁.trans hT')
    have hHeight : |sign * T| = T := by rw [abs_mul, hsign, one_mul, abs_of_pos (zero_lt_one.trans hT₀')]
    obtain ⟨ha, _, hr⟩ := hD (sign * T) (by rwa [hHeight])
    rw [hHeight] at hr
    exact horizontal_lower_bound_from_disk hc hT₀' ((le_max_right T₁ (c⁻¹)).trans hT) hN hsign
      (hcenter (sign * T)) ha hr hB
  refine ⟨L, 2 * A₀, U, by positivity, hm, he, ⟨T₀, han, hp⟩, ?_, ?_⟩
  · intro sign hsign T hT
    obtain ⟨E, _, _, hE, h⟩ := hVol sign hsign T hT one_lt_two
    have hex : (Ioo T (T + 1) \ E).Nonempty := by
      by_contra hEmpty
      have hsub : Ioo T (T + 1) ⊆ E := fun x hx ↦ by
        by_contra hxE
        exact hEmpty ⟨x, hx, hxE⟩
      have hmeasure := measure_mono (μ := volume) hsub
      rw [Real.volume_Ioo, hE] at hmeasure
      have hm := (ENNReal.ofReal_le_ofReal_iff (by norm_num)).mp hmeasure
      linarith
    obtain ⟨t, ht, htE⟩ := hex
    have hT₀' := one_lt_two.trans_le (hT₁.trans ((le_max_left T₁ (c⁻¹)).trans hT))
    refine ⟨t, ht, fun x hx ↦ lt_of_le_of_lt ?_ (h t ⟨Ioo_subset_Icc_self ht, htE⟩ x hx)⟩
    rw [abs_of_pos ((zero_lt_one.trans hT₀').trans ht.1), mul_comm (2 : ℝ)]
    exact Real.rpow_le_rpow_of_nonpos (zero_lt_one.trans hT₀') ht.1.le (by nlinarith)
  · intro sign hsign T hT B hB
    obtain ⟨E, hE, hEI, hEV, h⟩ := hVol sign hsign T hT hB
    have hT' := hT₁.trans ((le_max_left T₁ (c⁻¹)).trans hT)
    refine ⟨E, hE, hEI, hEV, fun t ht x hx ↦ lt_of_le_of_lt ?_ (h t ht x hx)⟩
    exact Real.rpow_le_rpow_of_exponent_le (one_le_two.trans hT') (by nlinarith)

set_option maxHeartbeats 400000 in
/-- At an ordinate with a polynomial lower bound on the segment, shrinking
the Cauchy disk keeps the whole disk away from zeros. -/
theorem reciprocal_derivatives_on_horizontal_segments {L : ℂ → ℂ} {T₀ : ℝ} {q : ℕ}
    (hq : 0 < q) (hAn : ∀ z : ℂ, T₀ ≤ |z.im| → AnalyticAt ℂ L z)
    (hGrowth : ∃ (C : ℝ) (p : ℕ), 0 ≤ C ∧
      ∀ z : ℂ, z.re ∈ Icc (-3) 4 → T₀ ≤ |z.im| → ‖L z‖ ≤ C * (1 + |z.im|) ^ p)
    (n : ℕ) :
    ∃ (A U : ℝ) (β : ℕ), 0 < A ∧ 0 < β ∧
      ∀ y : ℝ, U ≤ |y| → (∀ x ∈ Icc (-1 : ℝ) 2, (|y| ^ q)⁻¹ ≤ ‖L ⟨x, y⟩‖) →
        ∀ x ∈ Icc (-1 : ℝ) 2, ‖iteratedDeriv n (fun z ↦ (L z)⁻¹) ⟨x, y⟩‖ ≤ A * |y| ^ β := by
  obtain ⟨C, p, hC, hD⟩ := iteratedDeriv_polynomial_strip
    (a := -2) (b := 3) hAn (by norm_num at hGrowth ⊢; exact hGrowth) 1
  let M := max 1 (C * 3 ^ p)
  have hM : 1 ≤ M := le_max_left _ _
  have hM₀ : 0 < M := zero_lt_one.trans_le hM
  refine ⟨(n.factorial : ℝ) * 2 * (2 * M) ^ n, max 1 (T₀ + 2), q + (p + q) * n,
    by positivity, by omega, fun y hy hl x hx ↦ ?_⟩
  let z : ℂ := ⟨x, y⟩
  let Y := |y|
  have hY₁ : 1 ≤ Y := (le_max_left _ _).trans hy
  have hY₀ : 0 < Y := zero_lt_one.trans_le hY₁
  let r := (2 * M * Y ^ (p + q))⁻¹
  have hr : 0 < r := inv_pos.mpr (by positivity)
  have hr₁ : r ≤ 1 := inv_le_one_of_one_le₀ <|
    one_le_mul_of_one_le_of_one_le (by linarith) (one_le_pow₀ hY₁)
  have hDisk (w : ℂ) (hw : w ∈ closedBall z r) :
      w.re ∈ Icc (-2) 3 ∧ 1 + T₀ ≤ |w.im| ∧ 1 + |w.im| ≤ 3 * Y := by
    have hd := (mem_closedBall_iff_norm.mp hw).trans hr₁
    have hre : |w.re - x| ≤ 1 := (Complex.abs_re_le_norm _).trans hd
    have him : |w.im - y| ≤ 1 := (Complex.abs_im_le_norm _).trans hd
    have hDiff := (abs_abs_sub_abs_le_abs_sub w.im y).trans him
    have ht : T₀ + 2 ≤ Y := (le_max_right _ _).trans hy
    exact ⟨⟨by linarith [hx.1, (abs_le.mp hre).1], by linarith [hx.2, (abs_le.mp hre).2]⟩,
      by linarith [(abs_le.mp hDiff).1], by linarith [(abs_le.mp hDiff).2]⟩
  have hD₁ (w : ℂ) (hw : w ∈ closedBall z r) : ‖deriv L w‖ ≤ M * Y ^ p := by
    obtain ⟨hw', ht, hs⟩ := hDisk w hw
    have h := hD w hw' ht
    rw [show (1 : ℕ) = 0 + 1 by rfl, iteratedDeriv_succ, iteratedDeriv_zero] at h
    calc
      _ ≤ C * (1 + |w.im|) ^ p := h
      _ ≤ C * (3 * Y) ^ p := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hs _) hC
      _ = (C * 3 ^ p) * Y ^ p := by rw [mul_pow, mul_assoc]
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
  have hLa (w : ℂ) (hw : w ∈ closedBall z r) : AnalyticAt ℂ L w :=
    hAn w ((by linarith : T₀ ≤ 1 + T₀).trans (hDisk w hw).2.1)
  have hLow (w : ℂ) (hw : w ∈ closedBall z r) : (Y ^ q)⁻¹ / 2 ≤ ‖L w‖ := by
    have h := Convex.norm_image_sub_le_of_norm_deriv_le
      (fun w hw ↦ (hLa w hw).differentiableAt) hD₁ (convex_closedBall z r)
      (mem_closedBall_self hr.le) hw
    have hd : ‖L w - L z‖ ≤ (Y ^ q)⁻¹ / 2 := by
      apply h.trans
      calc
        _ ≤ M * Y ^ p * r := mul_le_mul_of_nonneg_left (mem_closedBall_iff_norm.mp hw) (by positivity)
        _ = _ := by dsimp [r]; rw [pow_add]; field_simp
    have hnorm := norm_sub_norm_le (L z) (L w)
    rw [norm_sub_rev] at hnorm
    linarith [hl x hx]
  have hLow₀ (w : ℂ) (hw : w ∈ closedBall z r) : 0 < ‖L w‖ :=
    (div_pos (inv_pos.mpr (pow_pos hY₀ _)) (by norm_num)).trans_le (hLow w hw)
  have ha : AnalyticOnNhd ℂ (fun w ↦ (L w)⁻¹) (closedBall z r) :=
    fun w hw ↦ (hLa w hw).fun_inv (norm_pos_iff.mp (hLow₀ w hw))
  have hSphere (w : ℂ) (hw : w ∈ sphere z r) : ‖(L w)⁻¹‖ ≤ 2 * Y ^ q := by
    rw [norm_inv]
    apply (inv_le_comm₀ (hLow₀ w (sphere_subset_closedBall hw)) (by positivity)).2
    simpa only [mul_inv_rev, div_eq_mul_inv] using hLow w (sphere_subset_closedBall hw)
  have hdiff : DiffContOnCl ℂ (fun w ↦ (L w)⁻¹) (ball z r) := by
    refine ⟨fun w hw ↦ (ha w (ball_subset_closedBall hw)).differentiableAt.differentiableWithinAt, ?_⟩
    rw [closure_ball z hr.ne']
    exact ha.continuousOn
  refine (Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hr hdiff hSphere).trans_eq ?_
  change (n.factorial : ℝ) * (2 * Y ^ q) / r ^ n =
    (n.factorial : ℝ) * 2 * (2 * M) ^ n * Y ^ (q + (p + q) * n)
  dsimp [r]
  rw [inv_pow, div_inv_eq_mul, mul_pow, ← pow_mul, pow_add]
  ring

set_option maxHeartbeats 500000 in
include μ hν in
/-- Corollary B.6.1.8. A two-sided sequence of ordinates has linear growth
and supports the polynomial reciprocal derivative bound on every segment. -/
theorem exists_manuscriptFiniteHeckeOutside_reciprocal_derivative_heights (m : ℕ) :
    let l := comap (abs : ℤ → ℤ) atTop
    ∃ (L : ℂ → ℂ) (A β : ℝ) (H : ℤ → ℝ), 0 < A ∧ 0 < β ∧ MeromorphicOn L univ ∧
      EqOn L (manuscriptFiniteHeckeEulerOutside F χ S) {z | 1 < z.re} ∧ Monotone H ∧
      Tendsto (abs ∘ H) l atTop ∧ (H =O[l] fun k ↦ |(k : ℝ)|) ∧
      ∀ k : ℤ, ∀ x ∈ Icc (-1 : ℝ) 2,
        ‖iteratedDeriv m (fun z ↦ (L z)⁻¹) ⟨x, H k⟩‖ ≤ A * |H k| ^ β := by
  intro l
  obtain ⟨L, P, U, _, hm, he, ⟨T₀, hAn, hg⟩, hLower, _⟩ :=
    exists_manuscriptFiniteHeckeOutside_horizontal_lower_bounds F χ S ν η μ hν
  obtain ⟨q, hq⟩ := exists_nat_gt (max P 0)
  have hq₀ : 0 < q := Nat.cast_pos.mp ((le_max_right P (0 : ℝ)).trans_lt hq)
  have hqP : P ≤ q := (le_max_left P (0 : ℝ)).trans hq.le
  obtain ⟨A, U', β, hA, hβ, hD⟩ :=
    reciprocal_derivatives_on_horizontal_segments hq₀ hAn (hg (-3) 4 (by norm_num)) m
  let V := max (max U U') 2
  let base (k : ℤ) := V + |(k : ℝ)|
  let sign (k : ℤ) : ℝ := if 0 ≤ k then 1 else -1
  have hv₂ : 2 ≤ V := le_max_right _ _
  have hs (k : ℤ) : |sign k| = 1 := by dsimp [sign]; split_ifs <;> norm_num
  have hbase (k : ℤ) : U ≤ base k :=
    ((le_max_left _ _).trans (le_max_left _ _)).trans (le_add_of_nonneg_right (abs_nonneg _))
  choose t ht hL using fun k ↦ hLower (sign k) (hs k) (base k) (hbase k)
  let H (k : ℤ) := sign k * t k
  have hpos (k : ℤ) : 0 < t k := by
    have h := (ht k).1
    dsimp [base] at h
    linarith [abs_nonneg (k : ℝ)]
  have habs (k : ℤ) : |H k| = t k := by
    change |sign k * t k| = t k
    rw [abs_mul, hs, one_mul, abs_of_pos (hpos k)]
  have hMono : Monotone H := by
    intro i j hij
    rcases eq_or_lt_of_le hij with rfl | hij
    · rfl
    have hp : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast (show i + 1 ≤ j by omega)
    have hti := ht i
    have htj := ht j
    by_cases hi : 0 ≤ i
    · have hj : 0 ≤ j := hi.trans hij.le
      simp only [H, sign, hi, hj, ite_true, one_mul]
      have hti' := hti.2
      have htj' := htj.1
      dsimp [base] at hti' htj'
      rw [abs_of_nonneg (by exact_mod_cast hi)] at hti'
      rw [abs_of_nonneg (by exact_mod_cast hj)] at htj'
      linarith
    · by_cases hj : 0 ≤ j
      · simp only [H, sign, hi, hj, ite_false, ite_true, neg_one_mul, one_mul]
        linarith [hpos i, hpos j]
      · simp only [H, sign, hi, hj, ite_false, neg_one_mul]
        have hti' := hti.1
        have htj' := htj.2
        dsimp [base] at hti' htj'
        rw [abs_of_nonpos (by exact_mod_cast (le_of_not_ge hi))] at hti'
        rw [abs_of_nonpos (by exact_mod_cast (le_of_not_ge hj))] at htj'
        linarith
  have hCast : Tendsto (fun k : ℤ ↦ |(k : ℝ)|) l atTop := by
    have h := (tendsto_intCast_atTop_atTop (R := ℝ)).comp
      (tendsto_comap : Tendsto (abs : ℤ → ℤ) l atTop)
    apply h.congr
    intro k
    change ((|k| : ℤ) : ℝ) = |(k : ℝ)|
    exact Int.cast_abs
  refine ⟨L, A, β, H, hA, Nat.cast_pos.mpr hβ, hm, he, hMono, ?_, ?_, ?_⟩
  · apply Filter.tendsto_atTop.mpr
    intro b
    filter_upwards [hCast.eventually_ge_atTop b] with k hk
    have h := (ht k).1
    dsimp [base] at h
    rw [Function.comp_apply, habs]
    linarith
  · apply Asymptotics.IsBigO.of_bound (V + 2)
    filter_upwards [hCast.eventually_ge_atTop 1] with k hk
    have h := (ht k).2
    dsimp [base] at h
    rw [Real.norm_eq_abs, habs, Real.norm_eq_abs, abs_abs]
    nlinarith [mul_nonneg (show 0 ≤ V + 1 by linarith) (sub_nonneg.mpr hk)]
  · intro k x hx
    have hU' : U' ≤ V := (le_max_right U U').trans (le_max_left _ _)
    have hT : V ≤ t k := (le_add_of_nonneg_right (abs_nonneg _)).trans (ht k).1.le
    rw [Real.rpow_natCast]
    apply hD _ (hU'.trans (hT.trans_eq (habs k).symm)) _ x hx
    intro u hu
    rw [habs k]
    have hY : 1 ≤ t k := one_le_two.trans (hv₂.trans hT)
    have hh := hL k u hu
    have hEq : |t k| = t k := abs_of_pos (hpos k)
    rw [hEq] at hh
    refine (le_trans ?_ hh.le)
    rw [← Real.rpow_natCast, ← Real.rpow_neg (hpos k).le]
    exact Real.rpow_le_rpow_of_exponent_le hY (neg_le_neg hqP)

end

end Masullo
