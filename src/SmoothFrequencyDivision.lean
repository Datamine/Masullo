import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open Filter Function MeasureTheory Set Topology
open scoped ContDiff SchwartzMap

namespace Masullo

noncomputable section

private theorem finiteOrder_lt_infty (n : ℕ) : (n : ℕ∞ω) < ∞ :=
  WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top n)

private def affineDerivativeAverage (a : ℝ) (f : ℝ → ℂ) (n : ℕ) (x : ℝ) : ℂ :=
  ∫ t in Ioc (0 : ℝ) 1, t ^ n • iteratedDeriv (n + 1) f (a + t * (x - a))

private theorem affineDerivativeAverage_hasDerivAt {f : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) (a x : ℝ) (n : ℕ) :
    HasDerivAt (affineDerivativeAverage a f n) (affineDerivativeAverage a f (n + 1) x) x := by
  let μ := volume.restrict (Ioc (0 : ℝ) 1)
  let F (n : ℕ) (x t : ℝ) := t ^ n • iteratedDeriv (n+1) f (a + t * (x-a))
  have hC (j : ℕ) : Continuous (uncurry (F j)) := by
    have hD := hf.continuous_iteratedDeriv (j + 1) (finiteOrder_lt_infty _).le
    exact (continuous_snd.pow j).smul (hD.comp (by fun_prop))
  have hI (j : ℕ) (y : ℝ) : Integrable (F j y) μ := by
    change IntegrableOn (F j y) (Ioc 0 1)
    have hc := (hC j).comp (continuous_const.prodMk continuous_id : Continuous (fun t : ℝ ↦ (y,t)))
    exact (hc.continuousOn.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
  obtain ⟨C, hCbound⟩ := ((isCompact_closedBall x 1).prod (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1))).exists_bound_of_continuousOn
    (hC (n+1)).continuousOn
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (F := F n)
    (F' := F (n + 1)) (bound := fun _ ↦ C) (Metric.ball_mem_nhds x one_pos)
    (.of_forall fun y ↦ (hI n y).aestronglyMeasurable) (hI n x)
    (hI (n+1) x).aestronglyMeasurable ?_ ?_ ?_).2
  · filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ioc] with t ht y hy
    exact hCbound (y,t) ⟨Metric.ball_subset_closedBall hy, Ioc_subset_Icc_self ht⟩
  · change IntegrableOn (fun _ : ℝ ↦ C) (Ioc 0 1)
    exact ((continuous_const (y := C)).continuousOn.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
  · refine .of_forall fun t y _ ↦ ?_
    have hh : HasDerivAt (fun y : ℝ ↦ a + t * (y - a)) t y := by
      simpa using ((((hasDerivAt_id y).sub_const a).const_mul t).const_add a)
    have hD : HasDerivAt (iteratedDeriv (n+1) f)
        (iteratedDeriv (n+2) f (a+t*(y-a))) (a+t*(y-a)) := by
      rw [show iteratedDeriv (n+2) f = _ from iteratedDeriv_succ (n := n+1)]
      exact ((hf.differentiable_iteratedDeriv (n+1) (finiteOrder_lt_infty _)) _).hasDerivAt
    convert ((hD.scomp y hh).const_smul (t ^ n)) using 1
    · rfl
    · simp only [F, pow_succ, mul_smul]

private theorem affineDerivativeAverage_smooth {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    (a : ℝ) (n : ℕ) : ContDiff ℝ ∞ (affineDerivativeAverage a f n) := by
  apply contDiff_infty.mpr
  intro k
  induction k generalizing n with
  | zero =>
    exact contDiff_zero.mpr (continuous_iff_continuousAt.mpr
      fun x ↦ (affineDerivativeAverage_hasDerivAt hf a x n).continuousAt)
  | succ k ih =>
    have hderiv : deriv (affineDerivativeAverage a f n) = affineDerivativeAverage a f (n+1) :=
      funext fun x ↦ (affineDerivativeAverage_hasDerivAt hf a x n).deriv
    rw [Nat.cast_succ, contDiff_succ_iff_deriv, hderiv]
    exact ⟨fun x ↦ (affineDerivativeAverage_hasDerivAt hf a x n).differentiableAt, by simp, ih _⟩

private theorem affineDerivativeAverage_iteratedDeriv {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    (a : ℝ) (n : ℕ) :
    iteratedDeriv n (affineDerivativeAverage a f 0) = affineDerivativeAverage a f n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    exact funext fun x ↦ (affineDerivativeAverage_hasDerivAt hf a x n).deriv

private theorem sub_eq_smul_affineDerivativeAverage {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    (a x : ℝ) : f x - f a = (x - a) • affineDerivativeAverage a f 0 x := by
  let g (t : ℝ) := f (a + t * (x - a))
  have hder : ∀ t ∈ uIcc (0 : ℝ) 1,
      HasDerivAt g ((x-a) • deriv f (a + t * (x-a))) t := by
    intro t _
    have hh : HasDerivAt (fun t : ℝ ↦ a + t * (x-a)) (x-a) t := by
      simpa using (((hasDerivAt_id t).mul_const (x-a)).const_add a)
    exact (((hf.differentiable (by simp) _).hasDerivAt).scomp t hh)
  have hd : Continuous (deriv f) := hf.continuous_deriv (finiteOrder_lt_infty 1).le
  have hlin : Continuous (fun t : ℝ ↦ a + t * (x-a)) := by fun_prop
  have hct : Continuous (fun t : ℝ ↦ (x-a) • deriv f (a + t * (x-a))) :=
    (continuous_const (y := x-a)).smul (hd.comp hlin)
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt hder (hct.intervalIntegrable 0 1)
  rw [intervalIntegral.integral_of_le zero_le_one, integral_smul] at hi
  simpa [g, affineDerivativeAverage, iteratedDeriv_one, sub_add_cancel] using hi.symm

/-- Vanishing of the first `m` derivatives permits smooth division by
the `m`-th power of a real linear factor. -/
theorem exists_smooth_divide_sub_pow {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    (a : ℝ) (m : ℕ) (hzero : ∀ j < m, iteratedDeriv j f a = 0) :
    ∃ g : ℝ → ℂ, ContDiff ℝ ∞ g ∧ ∀ x, f x = (x-a)^m • g x := by
  induction m generalizing f with
  | zero => exact ⟨f, hf, fun x ↦ by simp⟩
  | succ m ih =>
    let h := affineDerivativeAverage a f 0
    have hhs : ContDiff ℝ ∞ h := affineDerivativeAverage_smooth hf a 0
    have hha (j : ℕ) (hj : j < m) : iteratedDeriv j h a = 0 := by
      change iteratedDeriv j (affineDerivativeAverage a f 0) a = 0
      rw [affineDerivativeAverage_iteratedDeriv hf]
      simp [affineDerivativeAverage, hzero (j+1) (Nat.succ_lt_succ hj)]
    obtain ⟨g, hg, he⟩ := ih hhs hha
    refine ⟨g, hg, fun x ↦ ?_⟩
    have hfa : f a = 0 := hzero 0 (Nat.zero_lt_succ _)
    have hx := sub_eq_smul_affineDerivativeAverage hf a x
    rw [hfa, sub_zero] at hx
    change f x = (x-a) • h x at hx
    rw [hx, he, smul_smul, pow_succ']

private theorem analytic_factor_on_real {D : ℂ → ℂ} {x : ℝ} (hD : AnalyticAt ℂ D (x : ℂ))
    (m : ℕ) (hm : analyticOrderAt D (x : ℂ) = m) :
    ∃ c : ℝ → ℂ, ContDiffAt ℝ ∞ c x ∧ c x ≠ 0 ∧
      ∀ᶠ y : ℝ in 𝓝 x, D (y : ℂ) = (y - x)^m • c y := by
  obtain ⟨g, hg, hg₀, he⟩ := hD.analyticOrderAt_eq_natCast.mp hm
  let c (y : ℝ) := g y
  have hgs : ContDiffAt ℝ ∞ g (x : ℂ) := (hg.restrictScalars (𝕜 := ℝ)).contDiffAt
  refine ⟨c, hgs.comp x Complex.ofRealCLM.contDiff.contDiffAt, hg₀, ?_⟩
  filter_upwards [Complex.continuous_ofReal.continuousAt.tendsto.eventually he] with y hy
  rw [hy, Complex.real_smul, Complex.ofReal_pow, Complex.ofReal_sub, smul_eq_mul]

/-- Only finitely many real zeros of an analytic multiplier lie in a
compact window if the multiplier has finite analytic order everywhere. -/
theorem finite_analyticZeros_on_compact_real
    (D : ℂ → ℂ) (hD : ∀ x : ℝ, AnalyticAt ℂ D (x : ℂ))
    (order : ℝ → ℕ) (horder : ∀ x : ℝ, analyticOrderAt D (x : ℂ) = order x)
    (K : Set ℝ) (hK : IsCompact K) :
    {x ∈ K | D (x : ℂ) = 0}.Finite := by
  by_contra h
  obtain ⟨x, _, hx⟩ := Set.Infinite.exists_accPt_of_subset_isCompact h hK (fun _ h ↦ h.1)
  obtain ⟨g, hg, hg₀, he⟩ := analytic_factor_on_real (hD x) (order x) (horder x)
  have hg' : ∀ᶠ y in 𝓝 x, g y ≠ 0 := hg.continuousAt.eventually_ne hg₀
  have hne : ∀ᶠ y : ℝ in 𝓝[≠] x, D (y : ℂ) ≠ 0 := by
    filter_upwards [he.filter_mono nhdsWithin_le_nhds, hg'.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin (s := {x}ᶜ)] with y hye hyg hy
    rw [hye, Complex.real_smul]
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (pow_ne_zero _ (sub_ne_zero.mpr hy))) hyg
  exact ((accPt_iff_frequently_nhdsNE.mp hx).mono (fun _ hy ↦ hy.2)) hne

/-- A compactly supported smooth real frequency profile can be divided
by the restriction of a complex analytic function if its jets vanish
to the analytic order of the divisor at every real point. -/
theorem exists_compactSchwartz_divide_analytic
    (D : ℂ → ℂ) (hD : ∀ x : ℝ, AnalyticAt ℂ D (x : ℂ))
    (order : ℝ → ℕ) (horder : ∀ x : ℝ, analyticOrderAt D (x : ℂ) = order x)
    (b : 𝓢(ℝ, ℂ)) (hb : HasCompactSupport b)
    (hjets : ∀ x : ℝ, ∀ j < order x, iteratedDeriv j (b : ℝ → ℂ) x = 0) :
    ∃ q : 𝓢(ℝ, ℂ), tsupport (q : ℝ → ℂ) ⊆ tsupport (b : ℝ → ℂ) ∧
      ∀ x : ℝ, D (x : ℂ) * q x = b x := by
  classical
  have hloc (x : ℝ) :
      ∃ c : ℝ → ℂ, ContDiffAt ℝ ∞ c x ∧
        (∀ᶠ y : ℝ in 𝓝 x, D (y : ℂ) * c y = b y) ∧
        (∀ᶠ y : ℝ in 𝓝[≠] x, D (y : ℂ) ≠ 0) := by
    obtain ⟨g, hg, hg₀, he⟩ := analytic_factor_on_real (hD x) (order x) (horder x)
    obtain ⟨a, ha, ha'⟩ := exists_smooth_divide_sub_pow (b.smooth ⊤) x (order x) (hjets x)
    let c (y : ℝ) := a y * (g y)⁻¹
    have hgn : ∀ᶠ y in 𝓝 x, g y ≠ 0 := hg.continuousAt.eventually_ne hg₀
    refine ⟨c, ha.contDiffAt.mul (hg.inv hg₀), ?_, ?_⟩
    · filter_upwards [he, hgn] with y hdy hgy
      rw [hdy, ha', Complex.real_smul, Complex.real_smul]
      change ((↑((y-x)^order x) : ℂ) * g y) * (a y * (g y)⁻¹) =
        (↑((y-x)^order x) : ℂ) * a y
      rw [mul_assoc, mul_left_comm (g y), mul_inv_cancel₀ hgy, mul_one]
    · filter_upwards [he.filter_mono nhdsWithin_le_nhds, hgn.filter_mono nhdsWithin_le_nhds,
        self_mem_nhdsWithin (s := {x}ᶜ)] with y hdy hgy hy
      rw [hdy, Complex.real_smul]
      exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (pow_ne_zero _ (sub_ne_zero.mpr hy))) hgy
  choose c hc hce hn using hloc
  have hUnique (x : ℝ) (p q : ℝ → ℂ) (hp : ContinuousAt p x) (hq : ContinuousAt q x)
      (hp' : ∀ᶠ y : ℝ in 𝓝 x, D (y : ℂ) * p y = b y)
      (hq' : ∀ᶠ y : ℝ in 𝓝 x, D (y : ℂ) * q y = b y) : p x = q x := by
    apply ((hp.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE hq).mp ?_).eq_of_nhds
    filter_upwards [hp'.filter_mono nhdsWithin_le_nhds, hq'.filter_mono nhdsWithin_le_nhds, hn x]
      with y hpy hqy hy
    exact mul_left_cancel₀ hy (hpy.trans hqy.symm)
  let q (x : ℝ) := c x x
  have hq (x : ℝ) : ∀ᶠ y in 𝓝 x, q y = c x y := by
    have hcont : ContDiffAt ℝ 0 (c x) x := (hc x).of_le (by simp)
    filter_upwards [eventually_eventually_nhds.mpr (hce x), hcont.eventually (by simp)] with y hy hyc
    exact hUnique y (c y) (c x) (hc y).continuousAt hyc.continuousAt (hce y) hy
  have hqs : ContDiff ℝ ∞ q := contDiff_iff_contDiffAt.mpr fun x ↦
    (hc x).congr_of_eventuallyEq (hq x)
  have hqSupp : tsupport q ⊆ tsupport (b : ℝ → ℂ) := by
    apply closure_minimal _ isClosed_closure
    intro x hx
    by_contra hxn
    have hbz := notMem_tsupport_iff_eventuallyEq.mp hxn
    have he : ∀ᶠ y : ℝ in 𝓝 x, D (y : ℂ) * 0 = b y := by
      filter_upwards [hbz] with y hy
      rw [mul_zero, hy]
      rfl
    exact (mem_support.mp hx) (hUnique x (c x) 0 (hc x).continuousAt continuousAt_const (hce x) he)
  let q' : 𝓢(ℝ, ℂ) := HasCompactSupport.toSchwartzMap
    (hb.of_isClosed_subset isClosed_closure hqSupp) hqs
  exact ⟨q', hqSupp, fun x ↦ (hce x).self_of_nhds⟩

end
end Masullo
