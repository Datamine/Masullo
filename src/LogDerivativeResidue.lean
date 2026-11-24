import RectangleResidue

open Complex Filter Function Set
open scoped Topology

namespace Masullo

/-- At a point of finite meromorphic order, the logarithmic derivative has
principal term equal to the signed order divided by the centered coordinate. -/
theorem logDeriv_eventuallyEq_order_div_add {L : ℂ → ℂ} {p : ℂ} {n : ℤ}
    (hL : MeromorphicAt L p) (hn : meromorphicOrderAt L p = n) :
    ∃ R : ℂ → ℂ, AnalyticAt ℂ R p ∧
      logDeriv L =ᶠ[𝓝[≠] p] fun z ↦ (n : ℂ) / (z - p) + R z := by
  obtain ⟨g, hg, hg0, he⟩ := (meromorphicOrderAt_eq_int_iff hL).1 hn
  have heq : L =ᶠ[𝓝[≠] p] fun z ↦ (z - p) ^ n * g z := by
    change ∀ᶠ z in 𝓝[≠] p, L z = (z - p) ^ n * g z
    simpa only [smul_eq_mul] using he
  refine ⟨logDeriv g, ?_, ?_⟩
  · rw [show logDeriv g = fun z ↦ deriv g z / g z from rfl]
    exact hg.deriv.div hg hg0
  · have hne : ∀ᶠ z in 𝓝[≠] p, z ≠ p :=
      eventually_mem_nhdsWithin
    have hgNear : ∀ᶠ z in 𝓝[≠] p, AnalyticAt ℂ g z ∧ g z ≠ 0 :=
      (hg.eventually_analyticAt.and (hg.continuousAt.eventually_ne hg0)).filter_mono nhdsWithin_le_nhds
    filter_upwards [heq, heq.nhdsNE_deriv, hne, hgNear] with z hz hd hzp hgz
    have hld : logDeriv L z = logDeriv (fun w ↦ (w - p) ^ n * g w) z := by
      simp only [logDeriv_apply, hz, hd]
    have hdsub : DifferentiableAt ℂ (fun w : ℂ ↦ w - p) z := by fun_prop
    rw [hld, logDeriv_mul (f := fun w ↦ (w - p) ^ n) (g := g) z
        (zpow_ne_zero n (sub_ne_zero.mpr hzp)) hgz.2
        (hdsub.zpow (Or.inl (sub_ne_zero.mpr hzp))) hgz.1.differentiableAt,
      logDeriv_fun_zpow hdsub]
    have hl : logDeriv (fun w : ℂ ↦ w - p) z = 1 / (z - p) := by
      rw [logDeriv_apply, deriv_sub_const, deriv_id'']
    rw [hl, mul_one_div]

/-- Pairing the logarithmic derivative with a holomorphic test gives
the test value weighted by the signed meromorphic order. -/
theorem meromorphicResidue_mul_logDeriv {L Φ : ℂ → ℂ} {p : ℂ} {n : ℤ}
    (hL : MeromorphicAt L p) (hn : meromorphicOrderAt L p = n) (hΦ : AnalyticAt ℂ Φ p) :
    meromorphicResidue (Φ * logDeriv L) p = (n : ℂ) * Φ p := by
  obtain ⟨R, hR, hEq⟩ := logDeriv_eventuallyEq_order_div_add hL hn
  let A (z : ℂ) := (n : ℂ) * Φ z + Φ z * R z * (z - p)
  have hA : AnalyticAt ℂ A p :=
    (analyticAt_const.fun_mul hΦ).add ((hΦ.fun_mul hR).fun_mul (by fun_prop))
  have he : Φ * logDeriv L =ᶠ[𝓝[≠] p] fun z ↦ A z / (z - p) := by
    have hne : ∀ᶠ z in 𝓝[≠] p, z ≠ p := eventually_mem_nhdsWithin
    filter_upwards [hEq, hne] with z hz hzp
    change Φ z * logDeriv L z = A z / (z - p)
    rw [hz, eq_div_iff (sub_ne_zero.mpr hzp)]
    dsimp [A]
    field_simp [sub_ne_zero.mpr hzp]
  rw [meromorphicResidue_congr he, meromorphicResidue_div_sub hA]
  simp [A]

/-- The logarithmic derivative has a pole precisely where the original
function has a nonzero finite order. Each such pole is simple. -/
theorem meromorphicOrderAt_logDeriv_of_ne_zero {L : ℂ → ℂ} {p : ℂ} {n : ℤ}
    (hL : MeromorphicAt L p) (hn : meromorphicOrderAt L p = n) (hn0 : n ≠ 0) :
    meromorphicOrderAt (logDeriv L) p = (-1 : ℤ) := by
  obtain ⟨R, hR, hEq⟩ := logDeriv_eventuallyEq_order_div_add hL hn
  let A (z : ℂ) := (n : ℂ) + R z * (z - p)
  have hA : AnalyticAt ℂ A p := analyticAt_const.add (hR.fun_mul (by fun_prop))
  have hAn : A p ≠ 0 := by simpa [A] using hn0
  have hm : MeromorphicAt (logDeriv L) p := hL.deriv.div hL
  refine (meromorphicOrderAt_eq_int_iff hm).2 ⟨A, hA, hAn, ?_⟩
  have hne : ∀ᶠ z in 𝓝[≠] p, z ≠ p := eventually_mem_nhdsWithin
  filter_upwards [hEq, hne] with z hz hzp
  rw [hz, zpow_neg_one, smul_eq_mul]
  field_simp [sub_ne_zero.mpr hzp]
  simp [A, mul_comm]

/-- No pole occurs in the logarithmic derivative at a point of order zero. -/
theorem meromorphicOrderAt_logDeriv_nonneg_of_order_zero {L : ℂ → ℂ} {p : ℂ}
    (hL : MeromorphicAt L p) (hn : meromorphicOrderAt L p = 0) :
    0 ≤ meromorphicOrderAt (logDeriv L) p := by
  obtain ⟨R, hR, hEq⟩ := logDeriv_eventuallyEq_order_div_add (n := 0) hL (by simpa using hn)
  have he : logDeriv L =ᶠ[𝓝[≠] p] R := by simpa using hEq
  rw [meromorphicOrderAt_congr he]
  exact hR.meromorphicOrderAt_nonneg

/-- When the weighted divisor is summable and supported in the strip, the
contour exhaustion converges to its unordered sum. -/
theorem tendsto_sum_divisor_rectanglePoles {L Φ : ℂ → ℂ} {a b : ℝ} {low high : ℕ → ℝ}
    (hL : MeromorphicOn L univ) (hNonzero : ∃ p, meromorphicOrderAt L p ≠ ⊤)
    (hSupport : ∀ p, MeromorphicOn.divisor L univ p ≠ 0 → p.re ∈ Icc a b)
    (hlo : Tendsto low atTop atBot) (hhi : Tendsto high atTop atTop)
    (hSum : Summable (fun p => (MeromorphicOn.divisor L univ p : ℂ) * Φ p)) :
    Tendsto (fun j => ∑ p ∈ rectanglePoles (logDeriv L) a b (low j) (high j)
      (fun z _ => hL.logDeriv z (mem_univ z)), (MeromorphicOn.divisor L univ p : ℂ) * Φ p) atTop
      (𝓝 (∑' p, (MeromorphicOn.divisor L univ p : ℂ) * Φ p)) := by
  classical
  let S : ℕ → Finset ℂ := fun j => rectanglePoles (logDeriv L) a b (low j) (high j)
    (fun z _ => hL.logDeriv z (mem_univ z))
  let D : Set ℂ := {p | MeromorphicOn.divisor L univ p ≠ 0}
  let f (p : ℂ) := (MeromorphicOn.divisor L univ p : ℂ) * Φ p
  obtain ⟨z, hz⟩ := hNonzero
  have hPole (p : ℂ) : meromorphicOrderAt (logDeriv L) p < 0 ↔ p ∈ D := by
    have hp := (hL.exists_meromorphicOrderAt_ne_top_iff_forall isConnected_univ).mp
      ⟨⟨z, mem_univ z⟩, hz⟩ ⟨p, mem_univ p⟩
    let n := (meromorphicOrderAt L p).untop₀
    have horder : meromorphicOrderAt L p = n :=
      (WithTop.coe_untop₀_of_ne_top hp).symm
    have hD : p ∈ D ↔ n ≠ 0 := by
      change MeromorphicOn.divisor L univ p ≠ 0 ↔ _
      rw [hL.divisor_apply (mem_univ p)]
    rw [hD]
    by_cases h : n = 0
    · have hzero : meromorphicOrderAt L p = 0 := by simpa only [h, WithTop.coe_zero] using horder
      simp [h, not_lt_of_ge (meromorphicOrderAt_logDeriv_nonneg_of_order_zero (hL p trivial) hzero)]
    · rw [meromorphicOrderAt_logDeriv_of_ne_zero (hL p trivial) horder h]
      exact iff_of_true (WithTop.coe_lt_coe.mpr (by decide : (-1 : ℤ) < 0)) h
  have hFilter : Tendsto (fun j => (S j).subtype (· ∈ D)) atTop atTop := by
    apply tendsto_atTop.mpr
    intro T
    change ∀ᶠ j in atTop, ∀ p ∈ T, p ∈ (S j).subtype (· ∈ D)
    apply (eventually_all_finset T).mpr
    intro p _
    filter_upwards [tendsto_atBot.mp hlo p.val.im, tendsto_atTop.mp hhi p.val.im] with j hjlo hjhi
    have hR := hSupport p.val p.property
    apply Finset.mem_subtype.mpr
    apply mem_rectanglePoles.mpr
    exact ⟨Complex.mem_reProdIm.mpr ⟨Icc_subset_uIcc hR, Icc_subset_uIcc ⟨hjlo, hjhi⟩⟩,
      (hPole p.val).mpr p.property⟩
  have hInd : D.indicator f = f := by
    funext p
    by_cases hp : p ∈ D
    · simp [hp]
    · have hzero : MeromorphicOn.divisor L univ p = 0 := by simpa [D] using hp
      simp [hp, f, hzero]
  have hSub : HasSum (f ∘ Subtype.val : D → ℂ) (∑' p, f p) :=
    hasSum_subtype_iff_indicator.mpr (hInd.symm ▸ hSum.hasSum)
  refine (hSub.comp hFilter).congr fun j => ?_
  change (∑ p ∈ (S j).subtype (· ∈ D), f p.val) = ∑ p ∈ S j, f p
  rw [Finset.sum_subtype_eq_sum_filter]
  congr 1
  exact Finset.filter_eq_self.mpr fun p hp => (hPole p).mp (mem_rectanglePoles.mp hp).2

/-- The contour limit for a logarithmic derivative gives the signed
divisor sum over the exhausting rectangles, and identifies the unordered
sum when the weighted divisor is summable and supported in the strip. -/
theorem asymptotic_residue_logDeriv {L Φ : ℂ → ℂ} {a b : ℝ} {low high : ℕ → ℝ} {m : ℕ}
    (hab : a < b) (hL : MeromorphicOn L univ)
    (hNonzero : ∃ p, meromorphicOrderAt L p ≠ ⊤)
    (hΦ : AnalyticOnNhd ℂ Φ (Complex.re ⁻¹' Icc a b))
    (hlo : Tendsto low atTop atBot) (hhi : Tendsto high atTop atTop)
    (hHoriz : ∃ A C : ℝ, 0 ≤ A ∧ ∀ᶠ j in atTop, ∀ x ∈ Icc a b,
      ∀ y ∈ ({low j, high j} : Set ℝ),
        AnalyticAt ℂ (logDeriv L) ((x : ℂ) + (y : ℂ) * I) ∧
        ‖logDeriv L ((x : ℂ) + (y : ℂ) * I)‖ ≤ A * |y| ^ m ∧
        |y| ^ (m + 1) * ‖Φ ((x : ℂ) + (y : ℂ) * I)‖ ≤ C)
    (hVert : ∀ x ∈ ({a, b} : Set ℝ),
      (∀ y : ℝ, AnalyticAt ℂ (logDeriv L) ((x : ℂ) + (y : ℂ) * I)) ∧
      ∃ B D R : ℝ, 0 ≤ B ∧ ∀ y : ℝ, R ≤ |y| →
        ‖logDeriv L ((x : ℂ) + (y : ℂ) * I)‖ ≤ B * |y| ^ m ∧
        |y| ^ (m + 2) * ‖Φ ((x : ℂ) + (y : ℂ) * I)‖ ≤ D) :
    let W := fun x y : ℝ => Φ ((x : ℂ) + (y : ℂ) * I) * logDeriv L ((x : ℂ) + (y : ℂ) * I)
    let C := (I * (∫ y : ℝ, W b y) - I * (∫ y : ℝ, W a y)) / (2 * Real.pi * I)
    MeasureTheory.Integrable (W a) ∧ MeasureTheory.Integrable (W b) ∧
    (Tendsto (fun j => ∑ p ∈ rectanglePoles (logDeriv L) a b (low j) (high j)
      (fun z _ => hL.logDeriv z (mem_univ z)), (MeromorphicOn.divisor L univ p : ℂ) * Φ p) atTop
      (𝓝 C)) ∧
    ((∀ p, MeromorphicOn.divisor L univ p ≠ 0 → p.re ∈ Icc a b) →
      Summable (fun p => (MeromorphicOn.divisor L univ p : ℂ) * Φ p) →
      HasSum (fun p => (MeromorphicOn.divisor L univ p : ℂ) * Φ p) C) := by
  have hLog : MeromorphicOn (logDeriv L) (Complex.re ⁻¹' Icc a b) :=
    fun z _ => hL.logDeriv z (mem_univ z)
  obtain ⟨ha, hb, hlim⟩ := asymptotic_residue_product hab hLog hΦ hlo hhi hHoriz hVert
  obtain ⟨z, hz⟩ := hNonzero
  have hFinite (p : ℂ) : meromorphicOrderAt L p ≠ ⊤ :=
    (hL.exists_meromorphicOrderAt_ne_top_iff_forall isConnected_univ).mp
      ⟨⟨z, mem_univ z⟩, hz⟩ ⟨p, mem_univ p⟩
  refine ⟨ha, hb, ?_⟩
  have hDiv := hlim.congr (f₂ := fun j =>
    ∑ p ∈ rectanglePoles (logDeriv L) a b (low j) (high j)
      (fun z _ => hL.logDeriv z (mem_univ z)), (MeromorphicOn.divisor L univ p : ℂ) * Φ p) (fun j => by
    apply Finset.sum_congr rfl
    intro p hp
    have hpStrip : p ∈ Complex.re ⁻¹' Icc a b := by
      simpa only [mem_preimage, uIcc_of_le hab.le] using
        (Complex.mem_reProdIm.mp (mem_rectanglePoles.mp hp).1).1
    rw [hL.divisor_apply (mem_univ p)]
    exact meromorphicResidue_mul_logDeriv (hL p (mem_univ p))
      (WithTop.coe_untop₀_of_ne_top (hFinite p)).symm (hΦ p hpStrip))
  refine ⟨hDiv, fun hSupport hSummable => ?_⟩
  have hSumLimit := tendsto_sum_divisor_rectanglePoles hL ⟨z, hz⟩ hSupport hlo hhi hSummable
  exact (tendsto_nhds_unique hSumLimit hDiv) ▸ hSummable.hasSum

/-- Differentiating the reflected functional equation gives a minus sign
both on the reflected logarithmic derivative and on the multiplier term. -/
theorem logDeriv_of_reflection {L dual ε : ℂ → ℂ} {p : ℂ}
    (hL : AnalyticAt ℂ L p) (hDual : AnalyticAt ℂ dual (1 - p))
    (hε : AnalyticAt ℂ ε p) (hL0 : L p ≠ 0) (hε0 : ε p ≠ 0)
    (hEq : (fun z ↦ dual (1 - z)) =ᶠ[𝓝[≠] p] L * ε) :
    logDeriv L p = -logDeriv dual (1 - p) - logDeriv ε p := by
  let r : ℂ → ℂ := fun z ↦ 1 - z
  have hr : HasDerivAt r (-1) p := by
    have hs := (hasDerivAt_const p (1 : ℂ)).sub (hasDerivAt_id p)
    change HasDerivAt r (0 - 1) p at hs
    simpa only [zero_sub] using hs
  have hd : DifferentiableAt ℂ (dual ∘ r) p := hDual.differentiableAt.comp p hr.differentiableAt
  have he : dual ∘ r =ᶠ[𝓝 p] L * ε :=
    (hd.continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
      (hL.fun_mul hε).continuousAt).mp hEq
  have hlog : logDeriv (dual ∘ r) p = logDeriv (fun z ↦ L z * ε z) p := by
    rw [logDeriv_apply, logDeriv_apply, he.deriv_eq, he.eq_of_nhds]
    rfl
  rw [logDeriv_comp hDual.differentiableAt hr.differentiableAt, hr.deriv,
    logDeriv_mul _ hL0 hε0 hL.differentiableAt hε.differentiableAt] at hlog
  change logDeriv dual (1 - p) * (-1) = _ at hlog
  linear_combination -hlog

end Masullo
