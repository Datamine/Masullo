import FiniteHeckeLogDerivative
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Topology.MetricSpace.Thickening

open Filter Function IsDedekindDomain MeasureTheory Metric NumberField Set Topology
open scoped Classical NumberField

namespace Masullo

noncomputable section

private theorem hasDerivAt_horizontal_log_norm {f : ℂ → ℂ} {b : ℂ} {x : ℝ}
    (hAn : AnalyticAt ℂ f ((x : ℂ) + b)) (h0 : f ((x : ℂ) + b) ≠ 0) :
    HasDerivAt (fun u : ℝ ↦ Real.log ‖f ((u : ℂ) + b)‖)
      (logDeriv f ((x : ℂ) + b)).re x := by
  let c := f ((x : ℂ) + b)
  let g (z : ℂ) := f (z + b) / c
  have hg : HasDerivAt g (logDeriv f ((x : ℂ) + b)) (x : ℂ) := by
    have hd := (hAn.differentiableAt.hasDerivAt.comp_of_eq (x := (x : ℂ))
      ((hasDerivAt_id (x : ℂ)).add_const b) rfl).div_const c
    simpa only [Function.comp_apply, g, logDeriv_apply, c, mul_one, id_eq] using hd
  have h1 : g (x : ℂ) = 1 := div_self h0
  have hd := (hg.clog (h1 ▸ Complex.one_mem_slitPlane)).real_of_complex
  rw [h1, div_one] at hd
  have hG : ContinuousAt (fun u : ℝ ↦ f ((u : ℂ) + b)) x := by
    have hc : ContinuousAt (fun u : ℝ ↦ (u : ℂ) + b) x :=
      Complex.continuous_ofReal.continuousAt.add continuousAt_const
    exact hAn.continuousAt.comp (f := fun u : ℝ ↦ (u : ℂ) + b) hc
  apply (hd.add_const (Real.log ‖c‖)).congr_of_eventuallyEq
  filter_upwards [hG.eventually_ne h0] with u hu
  change Real.log ‖f ((u : ℂ) + b)‖ = (Complex.log (g (u : ℂ))).re + Real.log ‖c‖
  rw [Complex.log_re, show g (u : ℂ) = f ((u : ℂ) + b) / c from rfl, norm_div,
    Real.log_div (norm_ne_zero_iff.mpr hu) (norm_ne_zero_iff.mpr h0), sub_add_cancel]

variable (F : Type*) [Field F] [NumberField F]
private abbrev K := normOneIdeleClass F
private abbrev Place := HeightOneSpectrum (𝓞 F)

private theorem hecke_field_degree_one_le : 1 ≤ (Module.finrank ℚ F : ℝ) := by
  exact_mod_cast (show 1 ≤ Module.finrank ℚ F from Module.finrank_pos)

private theorem finiteEuler_ne_zero (ω : PontryaginDual (K F)) {z : ℂ} (hz : 1 < z.re) :
    globalFiniteHeckeEuler F ω z ≠ 0 :=
  heckeEulerProduct_ne_zero F _ (norm_heckeEulerCoefficient_le_one F _ _) hz

/-- Differentiating the monotone three-factor Euler product gives the
three logarithmic-derivative inequality, including the doubled height. -/
theorem finiteHecke_logDeriv_three_factor (ω : PontryaginDual (K F))
    {L₀ L₁ L₂ : ℂ → ℂ}
    (he₀ : EqOn L₀ (globalFiniteHeckeEuler F 1) {z | 1 < z.re})
    (he₁ : EqOn L₁ (globalFiniteHeckeEuler F ω) {z | 1 < z.re})
    (he₂ : EqOn L₂ (globalFiniteHeckeEuler F (ω ^ 2)) {z | 1 < z.re})
    {x y : ℝ} (hx : 1 < x)
    (h₀ : AnalyticAt ℂ L₀ (x : ℂ))
    (h₁ : AnalyticAt ℂ L₁ ⟨x,y⟩) (h₂ : AnalyticAt ℂ L₂ ⟨x,2*y⟩) :
    0 ≤ 3 * (-(logDeriv L₀ (x : ℂ)).re) + 4 * (-(logDeriv L₁ ⟨x,y⟩).re) +
      (-(logDeriv L₂ ⟨x,2*y⟩).re) := by
  let b : ℂ := (y : ℂ) * Complex.I
  have hEq₁ (u : ℝ) : (u : ℂ) + b = ⟨u, y⟩ := by
    apply Complex.ext <;> simp [b, Complex.mul_re, Complex.mul_im]
  have hEq₂ (u : ℝ) : (u : ℂ) + 2 * b = ⟨u, 2 * y⟩ := by
    apply Complex.ext <;> simp [b, Complex.mul_re, Complex.mul_im]
  have hn₀ (u : ℝ) (hu : 1 < u) : L₀ (u : ℂ) ≠ 0 := by
    have h : (u : ℂ) ∈ {z : ℂ | 1 < z.re} := by simpa using hu
    rw [he₀ h]
    exact finiteEuler_ne_zero F 1 h
  have hn₁ (u : ℝ) (hu : 1 < u) : L₁ ((u : ℂ) + b) ≠ 0 := by
    have h : (u : ℂ) + b ∈ {z : ℂ | 1 < z.re} := by rwa [hEq₁]
    rw [he₁ h]
    exact finiteEuler_ne_zero F ω h
  have hn₂ (u : ℝ) (hu : 1 < u) : L₂ ((u : ℂ) + 2 * b) ≠ 0 := by
    have h : (u : ℂ) + 2 * b ∈ {z : ℂ | 1 < z.re} := by rwa [hEq₂]
    rw [he₂ h]
    exact finiteEuler_ne_zero F (ω ^ 2) h
  have hd₀ : HasDerivAt (fun u : ℝ ↦ Real.log ‖L₀ (u : ℂ)‖) (logDeriv L₀ (x : ℂ)).re x :=
    by
      have hh := hasDerivAt_horizontal_log_norm (f := L₀) (b := 0) (x := x)
        (by simpa only [add_zero] using h₀) (by simpa only [add_zero] using hn₀ x hx)
      simpa only [add_zero] using hh
  have hd₁ := hasDerivAt_horizontal_log_norm (b := b) (by rwa [hEq₁]) (hn₁ x hx)
  have hd₂ := hasDerivAt_horizontal_log_norm (b := 2 * b) (by rwa [hEq₂]) (hn₂ x hx)
  let g (u : ℝ) := 3 * Real.log ‖L₀ (u : ℂ)‖ +
    4 * Real.log ‖L₁ ((u : ℂ) + b)‖ + Real.log ‖L₂ ((u : ℂ) + 2 * b)‖
  have hLog (u : ℝ) (hu : 1 < u) :
      g u = Real.log ‖globalFiniteHeckeEuler F 1 u ^ 3 *
        globalFiniteHeckeEuler F ω ((u : ℂ) + b) ^ 4 *
        globalFiniteHeckeEuler F (ω ^ 2) ((u : ℂ) + 2 * b)‖ := by
    have hu₀ : (u : ℂ) ∈ {z : ℂ | 1 < z.re} := by simpa using hu
    have hu₁ : (u : ℂ) + b ∈ {z : ℂ | 1 < z.re} := by rwa [hEq₁]
    have hu₂ : (u : ℂ) + 2 * b ∈ {z : ℂ | 1 < z.re} := by rwa [hEq₂]
    rw [← he₀ hu₀, ← he₁ hu₁, ← he₂ hu₂, norm_mul, norm_mul, norm_pow, norm_pow,
      Real.log_mul (mul_ne_zero (pow_ne_zero _ (norm_ne_zero_iff.mpr (hn₀ u hu)))
        (pow_ne_zero _ (norm_ne_zero_iff.mpr (hn₁ u hu)))) (norm_ne_zero_iff.mpr (hn₂ u hu)),
      Real.log_mul (pow_ne_zero _ (norm_ne_zero_iff.mpr (hn₀ u hu)))
        (pow_ne_zero _ (norm_ne_zero_iff.mpr (hn₁ u hu))), Real.log_pow, Real.log_pow]
    rfl
  have hAnti : AntitoneOn g (Ioi 1) := by
    intro u hu v hv huv
    rw [hLog u hu, hLog v hv]
    apply Real.log_le_log
    · rw [← he₀ (show (v : ℂ) ∈ {z : ℂ | 1 < z.re} by simpa using hv),
        ← he₁ (show (v : ℂ) + b ∈ {z : ℂ | 1 < z.re} by rwa [hEq₁]),
        ← he₂ (show (v : ℂ) + 2 * b ∈ {z : ℂ | 1 < z.re} by rwa [hEq₂])]
      exact norm_pos_iff.mpr (mul_ne_zero (mul_ne_zero (pow_ne_zero _ (hn₀ _ hv))
        (pow_ne_zero _ (hn₁ _ hv))) (hn₂ _ hv))
    · exact globalFiniteHeckeEuler_product_norm_antitone F ω y hu hv huv
  have hd := (hd₀.const_mul (3 : ℝ)).add (hd₁.const_mul (4 : ℝ)) |>.add hd₂
  have hh : derivWithin g (Ioi 1) x =
      3 * (logDeriv L₀ (x : ℂ)).re + 4 * (logDeriv L₁ ((x : ℂ) + b)).re +
        (logDeriv L₂ ((x : ℂ) + 2 * b)).re :=
    hd.hasDerivWithinAt.derivWithin (uniqueDiffOn_Ioi _ _ hx)
  have hp := hAnti.derivWithin_nonpos (x := x)
  rw [hh, hEq₁, hEq₂] at hp
  linarith

private theorem neg_re_logDeriv_le_simple_pole {L : ℂ → ℂ}
    (hm : MeromorphicAt L 1) (ho : meromorphicOrderAt L 1 = (-1 : ℤ)) :
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧ ∀ x ∈ Ioo (1 : ℝ) (1 + δ),
      -(logDeriv L (x : ℂ)).re ≤ (x - 1)⁻¹ + C := by
  obtain ⟨g, ha, hg, he⟩ := (meromorphicOrderAt_eq_int_iff hm).mp ho
  have hct : ContinuousAt (logDeriv g) (1 : ℂ) := by
    change ContinuousAt (deriv g / g) (1 : ℂ)
    exact ha.deriv.continuousAt.div ha.continuousAt hg
  let C := ‖logDeriv g (1 : ℂ)‖ + 1
  have hB : ∀ᶠ z in 𝓝 (1 : ℂ), ‖logDeriv g z‖ < C :=
    hct.norm.tendsto.eventually_lt_const (by dsimp [C]; linarith)
  have hD : ∀ᶠ z in 𝓝 (1 : ℂ), DifferentiableAt ℂ g z :=
    ha.eventually_analyticAt.mono fun _ hz ↦ hz.differentiableAt
  have he' : ∀ᶠ z in 𝓝 (1 : ℂ), z ≠ 1 → L z = g z / (z - 1) := by
    filter_upwards [eventually_nhdsWithin_iff.mp he] with z hz hne
    simpa [zpow_neg, div_eq_mul_inv, mul_comm] using hz hne
  obtain ⟨O, hO, hOpen, h1⟩ := _root_.eventually_nhds_iff.mp
    (hB.and (hD.and ((ha.continuousAt.eventually_ne hg).and he')))
  obtain ⟨δ, hδ, hδO⟩ := Metric.isOpen_iff.mp hOpen 1 h1
  refine ⟨C, δ, by positivity, hδ, fun x hx ↦ ?_⟩
  let z : ℂ := (x : ℂ)
  have hzO : z ∈ O := by
    apply hδO
    rw [mem_ball, dist_eq_norm, show z - 1 = ((x - 1 : ℝ) : ℂ) by simp [z],
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (sub_pos.mpr hx.1)]
    linarith [hx.2]
  have hz1 : z ≠ 1 := by
    change (x : ℂ) ≠ 1
    exact_mod_cast hx.1.ne'
  have hEq : L =ᶠ[𝓝 z] fun w ↦ g w / (w - 1) := by
    filter_upwards [hOpen.mem_nhds hzO, isOpen_ne.mem_nhds hz1] with w hw hne
    exact (hO w hw).2.2.2 hne
  have hzD : DifferentiableAt ℂ (fun w : ℂ ↦ w - 1) z := differentiableAt_id.sub_const _
  have hLog : logDeriv L z = logDeriv g z - 1 / (z - 1) := by
    calc
      _ = logDeriv (fun w ↦ g w / (w - 1)) z := by
        simp only [logDeriv_apply]
        rw [hEq.deriv_eq, hEq.eq_of_nhds]
      _ = _ := by
        rw [logDeriv_div (f := g) (g := fun w : ℂ ↦ w - 1) z
          (hO z hzO).2.2.1 (sub_ne_zero.mpr hz1) (hO z hzO).2.1 hzD]
        simp [logDeriv_apply]
  change -(logDeriv L z).re ≤ _
  rw [hLog, Complex.sub_re, show (1 : ℂ) / (z - 1) = (((x - 1)⁻¹ : ℝ) : ℂ) by
    simp only [z, one_div, Complex.ofReal_inv, Complex.ofReal_sub, Complex.ofReal_one], Complex.ofReal_re]
  have hh := (neg_le_abs (logDeriv g z).re).trans ((Complex.abs_re_le_norm _).trans (hO z hzO).1.le)
  linarith


private theorem canonical_finiteHecke_disk_data (ω : PontryaginDual (K F)) {L : ℂ → ℂ}
    (he : EqOn L (globalFiniteHeckeEuler F ω) {z | 1 < z.re})
    (ha : ∀ z : ℂ, z ≠ 0 → z ≠ 1 → AnalyticAt ℂ L z)
    (hp : ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, z.re ∈ Icc (-6) 10 → 1 ≤ |z.im| →
      ‖L z‖ ≤ C * (1 + |z.im|) ^ (Module.finrank ℚ F * 7)) :
    ∃ T : ℝ, 2 ≤ T ∧
      ∀ y : ℝ, T ≤ |y| →
        AnalyticOnNhd ℂ L (closedBall ⟨2, y⟩ 8) ∧ L ⟨2, y⟩ ≠ 0 ∧
          ∀ w ∈ closedBall (⟨2, y⟩ : ℂ) 8, ‖L w / L ⟨2, y⟩‖ ≤ |y| ^ (Module.finrank ℚ F * 7 + 1) := by
  obtain ⟨c, hc, hC⟩ := globalFiniteHeckeEuler_norm_ge_two F
  have hc' (y : ℝ) : c ≤ ‖L ⟨2, y⟩‖ := by
    rw [he (show (1 : ℝ) < 2 by norm_num)]
    exact hC ω y
  have ha' (z : ℂ) (ht : 1 ≤ |z.im|) : AnalyticAt ℂ L z :=
    ha z (by intro e; norm_num [e] at ht) (by intro e; norm_num [e] at ht)
  obtain ⟨A, hA, h⟩ := hp
  exact disk_bound_of_degree_polynomial_strip (by norm_num : (0 : ℝ) < 8) hc hA
    (fun y _ ↦ hc' y) ha' (by norm_num at h ⊢; exact h)

private theorem horizontal_mem_disk {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 2) :
    (⟨x, y⟩ : ℂ) ∈ closedBall ⟨2, y⟩ 2 := by
  rw [mem_closedBall_iff_norm, show (⟨x, y⟩ : ℂ) - ⟨2, y⟩ = ((x - 2 : ℝ) : ℂ) by
    apply Complex.ext <;> simp, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonpos (sub_nonpos.mpr hx.2)]
  linarith [hx.1]

private theorem canonical_finiteHecke_one_sided (ω : PontryaginDual (K F)) {L : ℂ → ℂ}
    (he : EqOn L (globalFiniteHeckeEuler F ω) {z | 1 < z.re}) {N : ℕ} (hN : 0 < N)
    {x y : ℝ} (hx : x ∈ Ioc (1 : ℝ) 2) (hy : 2 ≤ |y|)
    (hAn : AnalyticOnNhd ℂ L (closedBall ⟨2, y⟩ 8)) (hc : L ⟨2, y⟩ ≠ 0)
    (hB : ∀ w ∈ closedBall (⟨2, y⟩ : ℂ) 8, ‖L w / L ⟨2, y⟩‖ ≤ |y| ^ N) :
    let K := RiemannMasullo.landauConstant 2 4 6 8 * (N : ℝ);
    -(logDeriv L ⟨x, y⟩).re ≤ K * Real.log |y| ∧
      (∀ β ∈ Icc (0 : ℝ) 1, L ⟨β, y⟩ = 0 →
        -(logDeriv L ⟨x, y⟩).re ≤ -((x - β)⁻¹) + K * Real.log |y|) := by
  intro K
  have hX : (⟨x, y⟩ : ℂ) ∈ closedBall ⟨2, y⟩ 2 :=
    horizontal_mem_disk ⟨zero_le_one.trans hx.1.le, hx.2⟩
  have hL : L ⟨x, y⟩ ≠ 0 := by
    rw [he (show (⟨x, y⟩ : ℂ) ∈ {z : ℂ | 1 < z.re} from hx.1)]
    exact finiteEuler_ne_zero F ω hx.1
  have hLeft (w : ℂ) (_ : w ∈ closedBall (⟨2,y⟩ : ℂ) 4) (hw : L w = 0) :
      w.re ≤ (⟨x,y⟩ : ℂ).re := by
    by_contra! h
    have h' : 1 < w.re := hx.1.trans h
    rw [he h'] at hw
    exact finiteEuler_ne_zero F ω h' hw
  have hB₀ : 1 < |y| ^ N := one_lt_pow₀ (one_lt_two.trans_le hy) hN.ne'
  have h₁ := RiemannMasullo.landau_neg_re_logDeriv_le_of_forall_re_le hB₀
    (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) < 4)
    (by norm_num : (4 : ℝ) < 6) (by norm_num : (6 : ℝ) < 8) hAn hc hB hX hL hLeft
  rw [Real.log_pow, ← mul_assoc] at h₁
  refine ⟨h₁, fun β hβ hZ ↦ ?_⟩
  have hρ := closedBall_subset_closedBall (by norm_num : (2 : ℝ) ≤ 4)
    (horizontal_mem_disk (y := y) ⟨hβ.1, hβ.2.trans one_le_two⟩)
  have h₂ := RiemannMasullo.landau_neg_re_logDeriv_le_of_zero hB₀
    (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) < 4)
    (by norm_num : (4 : ℝ) < 6) (by norm_num : (6 : ℝ) < 8) hAn hc hB hX hL hLeft hρ hZ
  have hEq : ((⟨x,y⟩ : ℂ) - ⟨β,y⟩) = ((x - β : ℝ) : ℂ) := by
    apply Complex.ext <;> simp
  rw [hEq, one_div, ← Complex.ofReal_inv, Complex.ofReal_re, Real.log_pow, ← mul_assoc] at h₂
  exact h₂

local instance zeroFreeNormOneMeasurable : MeasurableSpace (K F) := borel _
local instance zeroFreeNormOneBorel : BorelSpace (K F) := ⟨rfl⟩
local instance zeroFreeIdeleMeasurable : MeasurableSpace (Idele F) := borel _
local instance zeroFreeIdeleBorel : BorelSpace (Idele F) := ⟨rfl⟩

variable (ν : Measure (K F)) [ν.IsHaarMeasure]
variable (η : Measure (Idele F)) [η.IsHaarMeasure]
variable [∀ v : Place F, MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : Place F, BorelSpace (v.adicCompletion F)ˣ]
  (μ : ∀ v : Place F, Measure (v.adicCompletion F)ˣ)
  [∀ v : Place F, (μ v).IsHaarMeasure] [∀ v : Place F, SigmaFinite (μ v)]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]
variable (hν : IsWeilQuotientMeasure (principalIdeles F) η Measure.count (globalClassMeasure F ν))


private theorem heckeLandauConstant_pos : 0 < RiemannMasullo.landauConstant 2 4 6 8 :=
  RiemannMasullo.landauConstant_pos (by norm_num) (by norm_num) (by norm_num) (by norm_num)

private noncomputable def heckeZeroFreeBase : ℝ :=
  (4 * (2 + 48 * RiemannMasullo.landauConstant 2 4 6 8))⁻¹

private theorem heckeZeroFreeBase_pos : 0 < heckeZeroFreeBase :=
  inv_pos.mpr (by have h := heckeLandauConstant_pos; positivity)

set_option maxHeartbeats 500000 in
include μ hν in
/-- A large-height zero-free band with an absolute numerator and a
denominator linear in both the field degree and the logarithmic height. -/
theorem exists_globalFiniteHecke_degree_zeroFree (ω : PontryaginDual (K F)) :
    ∃ (L : ℂ → ℂ) (T : ℝ), 2 ≤ T ∧
      MeromorphicOn L univ ∧ EqOn L (globalFiniteHeckeEuler F ω) {z | 1 < z.re} ∧
      (∀ z : ℂ, z ≠ 0 → z ≠ 1 → AnalyticAt ℂ L z) ∧
      (∀ z : ℂ, T ≤ |z.im| →
        1 - (heckeZeroFreeBase / 8) / ((Module.finrank ℚ F : ℝ) * Real.log |z.im|) ≤ z.re → L z ≠ 0) ∧
      ∀ y : ℝ, T ≤ |y| →
        AnalyticOnNhd ℂ L (closedBall ⟨2, y⟩ 8) ∧ L ⟨2, y⟩ ≠ 0 ∧
          ∀ w ∈ closedBall (⟨2, y⟩ : ℂ) 8, ‖L w / L ⟨2, y⟩‖ ≤ |y| ^ (Module.finrank ℚ F * 7 + 1) := by
  obtain ⟨L, hm, he, ha, _, _, hp⟩ := exists_globalFiniteHecke_degree_polynomial_strips F ω ν η μ hν
  obtain ⟨G, _, he₂, ha₂, _, _, hp₂⟩ := exists_globalFiniteHecke_degree_polynomial_strips F (ω ^ 2) ν η μ hν
  obtain ⟨Z, hz, he₀, ha₀, _, _⟩ := exists_globalFiniteHecke_polynomial_strips F 1 ν η μ hν
  have ho : meromorphicOrderAt Z 1 = (-1 : ℤ) :=
    ((globalFiniteHecke_pole_and_trivial_zero F η ν μ hν 1 hz he₀).2 rfl).1
  obtain ⟨C, δ, hC, hδ, hP⟩ := neg_re_logDeriv_le_simple_pole (hz 1 (mem_univ _)) ho
  obtain ⟨U₁, hU₁, hD₁⟩ := canonical_finiteHecke_disk_data F ω he ha hp
  obtain ⟨U₂, hU₂, hD₂⟩ := canonical_finiteHecke_disk_data F (ω ^ 2) he₂ ha₂ hp₂
  let d : ℝ := Module.finrank ℚ F
  have hd : 1 ≤ d := hecke_field_degree_one_le F
  let N := Module.finrank ℚ F * 7 + 1
  have hN : 0 < N := Nat.succ_pos _
  have hNd : (N : ℝ) ≤ 8 * d := by dsimp [N, d]; push_cast; linarith
  let K := RiemannMasullo.landauConstant 2 4 6 8
  let J := K * (N : ℝ)
  have hK : 0 < K := heckeLandauConstant_pos
  have hJ : 0 ≤ J := mul_nonneg hK.le (Nat.cast_nonneg _)
  let E := 1 + 6 * J
  let a := heckeZeroFreeBase / d
  have haPos : 0 < a := div_pos heckeZeroFreeBase_pos (zero_lt_one.trans_le hd)
  have ha₁ : a ≤ 1 / 4 := by
    refine (div_le_self heckeZeroFreeBase_pos.le hd).trans ?_
    change (4 * (2 + 48 * K))⁻¹ ≤ 1 / 4
    rw [one_div]
    exact inv_anti₀ (by norm_num : (0 : ℝ) < 4) (by linarith)
  have hEa : E * a ≤ 1 / 4 := by
    have he : E ≤ (2 + 48 * K) * d := by
      dsimp [E, J]
      nlinarith [mul_le_mul_of_nonneg_left hNd hK.le]
    have hh := mul_le_mul_of_nonneg_right he haPos.le
    have hd₀ : d ≠ 0 := (zero_lt_one.trans_le hd).ne'
    have hK₀ : 2 + 48 * K ≠ 0 := by positivity
    refine hh.trans_eq ?_
    calc
      _ = (2 + 48 * K) * heckeZeroFreeBase := by
        change (2 + 48 * K) * d * (heckeZeroFreeBase / d) = _
        field_simp [hd₀]
      _ = 1 / 4 := by
        change (2 + 48 * K) * (4 * (2 + 48 * K))⁻¹ = _
        field_simp [hK₀]
  let T := max (max U₁ U₂) (Real.exp (max (max 1 (3 * C)) (2 * a / δ)))
  have hTT : 2 ≤ T := hU₁.trans ((le_max_left _ _).trans (le_max_left _ _))
  refine ⟨L, T, hTT, hm, he, ha, ?_,
    fun y hy ↦ hD₁ y (((le_max_left _ _).trans (le_max_left _ _)).trans hy)⟩
  intro ρ hρ hb hzero
  let y := ρ.im
  let β := ρ.re
  have hy₂ : 2 ≤ |y| := hTT.trans hρ
  let ℓ := Real.log |y|
  have hℓMax : max (max 1 (3 * C)) (2 * a / δ) ≤ ℓ := by
    have h := Real.log_le_log (Real.exp_pos _) ((le_max_right _ _).trans hρ)
    rwa [Real.log_exp] at h
  have hℓ₁ : 1 ≤ ℓ := (le_max_left _ _).trans ((le_max_left _ _).trans hℓMax)
  have hℓ : 0 < ℓ := zero_lt_one.trans_le hℓ₁
  have hβ₁ : β ≤ 1 := by
    by_contra! h
    rw [he h] at hzero
    exact finiteEuler_ne_zero F ω h hzero
  have hb' : 1 - (a / 8) / ℓ ≤ β := by
    have heq : (a / 8) / ℓ = (heckeZeroFreeBase / 8) / (d * ℓ) := by
      dsimp [a]; ring
    rwa [heq]
  have hβ₀ : 0 ≤ β := by
    have h := div_le_div_of_nonneg_left (show 0 ≤ a / 8 by positivity) zero_lt_one hℓ₁
    norm_num at h
    linarith
  let x := 1 + a / ℓ
  have hd : 0 < a / ℓ := div_pos haPos hℓ
  have hx : 1 < x := lt_add_of_pos_right _ hd
  have hxd : a / ℓ ≤ a := div_le_self haPos.le hℓ₁
  have hx₂ : x ≤ 2 := by dsimp [x]; linarith
  have hxδ : x < 1 + δ := by
    have h := (div_le_iff₀ hδ).mp ((le_max_right (max 1 (3 * C)) _).trans hℓMax)
    have h' := (div_le_iff₀ hℓ).mpr (show a ≤ δ / 2 * ℓ by nlinarith)
    dsimp [x]
    linarith
  have hy₁ : U₁ ≤ |y| := ((le_max_left _ _).trans (le_max_left _ _)).trans hρ
  have hy' : |y| ≤ |2 * y| := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    linarith [abs_nonneg y]
  have hy₂' : U₂ ≤ |2 * y| := ((le_max_right _ _).trans (le_max_left _ _)).trans (hρ.trans hy')
  obtain ⟨hAn, hc, hB⟩ := hD₁ y hy₁
  obtain ⟨hAn₂, hc₂, hB₂⟩ := hD₂ (2 * y) hy₂'
  have hJ' := (canonical_finiteHecke_one_sided F ω he hN ⟨hx, hx₂⟩ hy₂ hAn hc hB).2
    β ⟨hβ₀, hβ₁⟩ (by simpa [β, y] using hzero)
  have hG := (canonical_finiteHecke_one_sided F (ω ^ 2) he₂ hN ⟨hx, hx₂⟩
    (hy₂.trans hy') hAn₂ hc₂ hB₂).1
  have hLog₂ : Real.log |2 * y| ≤ 2 * ℓ := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
      Real.log_mul (by norm_num) (zero_lt_one.trans_le (one_le_two.trans hy₂)).ne']
    linarith [Real.log_le_log (by norm_num : (0 : ℝ) < 2) hy₂]
  have hG' := hG.trans (mul_le_mul_of_nonneg_left hLog₂ hJ)
  have hZ := hP x ⟨hx, hxδ⟩
  have hn (v : ℂ) (hv : 1 < v.re) : v ≠ 0 ∧ v ≠ 1 := by
    constructor <;> intro e <;> norm_num [e] at hv
  have h₀ := hn (x : ℂ) (by simpa using hx)
  have h₁ := hn ⟨x, y⟩ hx
  have h₂ := hn ⟨x, 2*y⟩ hx
  have hsum := finiteHecke_logDeriv_three_factor F ω he₀ he he₂ hx
    (ha₀ _ h₀.1 h₀.2) (ha _ h₁.1 h₁.2) (ha₂ _ h₂.1 h₂.2)
  have hdistance : 0 < x - β := sub_pos.mpr (hβ₁.trans_lt hx)
  have hdist' : x - β ≤ 9 * a / (8 * ℓ) := by
    calc
      _ ≤ a / ℓ + (a / 8) / ℓ := by dsimp only [x]; linarith
      _ = _ := by ring
  have hreflect : (32 / 9) * (ℓ / a) ≤ 4 * (x - β)⁻¹ := by
    have h := (inv_le_inv₀ (by positivity : 0 < 9 * a / (8 * ℓ)) hdistance).2 hdist'
    calc
      _ = 4 * (9 * a / (8 * ℓ))⁻¹ := by field_simp; norm_num
      _ ≤ _ := mul_le_mul_of_nonneg_left h (by norm_num)
  have hcentre : (x - 1)⁻¹ = ℓ / a := by simp [x, inv_div]
  have hError : E * ℓ ≤ (1 / 4) * (ℓ / a) := by
    rw [← mul_div_assoc]
    apply (le_div_iff₀ haPos).2
    nlinarith [mul_le_mul_of_nonneg_right hEa hℓ.le]
  change -(logDeriv L ⟨x, y⟩).re ≤ -((x - β)⁻¹) + J * ℓ at hJ'
  change -(logDeriv G ⟨x, 2 * y⟩).re ≤ J * (2 * ℓ) at hG'
  rw [hcentre] at hZ
  have hCℓ : 3 * C ≤ ℓ := (le_max_right _ _).trans ((le_max_left _ _).trans hℓMax)
  have hcomb : 4 * (x - β)⁻¹ ≤ 3 * (ℓ / a) + E * ℓ := by
    dsimp [E]
    linarith [hZ, hJ', hG', hsum, hCℓ]
  linarith [div_pos hℓ haPos]


include μ hν in
/-- The large-height band with its field-dependent width exposed. -/
theorem exists_globalFiniteHecke_largeHeight_zeroFree (ω : PontryaginDual (K F)) :
    ∃ (L : ℂ → ℂ) (a T : ℝ) (N : ℕ), 0 < a ∧ 2 ≤ T ∧ 0 < N ∧
      MeromorphicOn L univ ∧ EqOn L (globalFiniteHeckeEuler F ω) {z | 1 < z.re} ∧
      (∀ z : ℂ, T ≤ |z.im| → 1 - a / Real.log |z.im| ≤ z.re → L z ≠ 0) ∧
      ∀ y : ℝ, T ≤ |y| →
        AnalyticOnNhd ℂ L (closedBall ⟨2, y⟩ 8) ∧ L ⟨2, y⟩ ≠ 0 ∧
          ∀ w ∈ closedBall (⟨2, y⟩ : ℂ) 8, ‖L w / L ⟨2, y⟩‖ ≤ |y| ^ N := by
  obtain ⟨L, T, hT, hm, he, _, hZ, hD⟩ := exists_globalFiniteHecke_degree_zeroFree F ν η μ hν ω
  have hd : 0 < (Module.finrank ℚ F : ℝ) := Nat.cast_pos.mpr Module.finrank_pos
  have h := heckeZeroFreeBase_pos
  refine ⟨L, (heckeZeroFreeBase / 8) / (Module.finrank ℚ F : ℝ), T, Module.finrank ℚ F * 7 + 1,
    by positivity, hT, Nat.succ_pos _, hm, he, ?_, hD⟩
  simpa only [div_div, mul_assoc] using hZ

private theorem log_abs_sub_le {y t : ℝ} (hy : 2 ≤ |y|) (hyt : 2 ≤ |y - t|)
    (ht : |t| ≤ |y|) : Real.log |y - t| ≤ 2 * Real.log |y| := by
  have hs : |y - t| ≤ 2 * |y| := by linarith [abs_sub y t]
  have h := Real.log_le_log (zero_lt_one.trans (one_lt_two.trans_le hyt)) hs
  rw [Real.log_mul (by norm_num) (by linarith : |y| ≠ 0)] at h
  linarith [Real.log_le_log (by norm_num : (0 : ℝ) < 2) hy]

include μ hν in
/-- A zero-free band at large absolute heights for the finite continuation
of every unitary idele-class character in its original parameter. -/
theorem exists_manuscriptFiniteHecke_largeHeight_zeroFree (χ : PontryaginDual (IdeleClass F)) :
    ∃ (L : ℂ → ℂ) (a T : ℝ), 0 < a ∧ 2 ≤ T ∧ MeromorphicOn L univ ∧
      EqOn L (manuscriptFiniteHeckeEuler F χ) {z | 1 < z.re} ∧
      ∀ z : ℂ, T ≤ |z.im| → 1 - a / Real.log |z.im| ≤ z.re → L z ≠ 0 := by
  obtain ⟨t, ht, _⟩ := existsUnique_heckeHeight F χ
  obtain ⟨f, a, T, _, ha, hT, _, hm, he, hZ, _⟩ :=
    exists_globalFiniteHecke_largeHeight_zeroFree F ν η μ hν (heckeNormOneRestriction F χ)
  let b : ℂ := (t : ℂ) * Complex.I
  let q (z : ℂ) := z - b
  have hre (z : ℂ) : (q z).re = z.re := by simp [q, b, Complex.sub_re, Complex.mul_re]
  have him (z : ℂ) : (q z).im = z.im - t := by simp [q, b, Complex.sub_im, Complex.mul_im]
  refine ⟨f ∘ q, a / 2, T + |t|, by positivity, by linarith [abs_nonneg t],
    fun z _ ↦ (hm (q z) (mem_univ _)).comp_analyticAt (g := q) (analyticAt_id.sub analyticAt_const), ?_, ?_⟩
  · intro z hz
    rw [manuscriptFiniteHeckeEuler_shift F χ ht]
    exact he (show 1 < (q z).re by rwa [hre])
  · intro z hy hσ
    have hzT : T ≤ |z.im - t| := by linarith [abs_sub_abs_le_abs_sub z.im t]
    have hy₂ : 2 ≤ |z.im| := by linarith [abs_nonneg t]
    have hlog := log_abs_sub_le hy₂ (hT.trans hzT) (by linarith : |t| ≤ |z.im|)
    have hℓ : 0 < Real.log |z.im - t| := Real.log_pos (one_lt_two.trans_le (hT.trans hzT))
    have hcomp : (a / 2) / Real.log |z.im| ≤ a / Real.log |z.im - t| := by
      rw [div_div]
      exact div_le_div_of_nonneg_left ha.le hℓ hlog
    apply hZ (q z) (by rwa [him])
    rw [him, hre]
    linarith

set_option maxHeartbeats 400000 in
include μ hν in
private theorem exists_globalFiniteHecke_logDeriv_oneLine (ω : PontryaginDual (K F)) :
    ∃ (L : ℂ → ℂ) (A T : ℝ), 0 ≤ A ∧ 2 ≤ T ∧ MeromorphicOn L univ ∧
      EqOn L (globalFiniteHeckeEuler F ω) {z | 1 < z.re} ∧
      ∀ y : ℝ, T ≤ |y| → L ⟨1, y⟩ ≠ 0 ∧ ‖logDeriv L ⟨1, y⟩‖ ≤ A * (Real.log |y|) ^ 2 := by
  obtain ⟨L, a, T, N, ha, hT, hN, hm, he, hZero, hD⟩ :=
    exists_globalFiniteHecke_largeHeight_zeroFree F ν η μ hν ω
  let b := Real.log 2
  have hb : 0 < b := Real.log_pos (by norm_num)
  refine ⟨L, (N : ℝ) * (300 / (8 * b) + 3 / (b * a)), T + 4, by positivity,
    by linarith, hm, he, fun y hy ↦ ?_⟩
  let ℓ := Real.log |y|
  have hyT : T ≤ |y| := by linarith
  have hy₂ : 2 ≤ |y| := hT.trans hyT
  have hℓb : b ≤ ℓ := Real.log_le_log (by norm_num) hy₂
  have hℓ : 0 < ℓ := hb.trans_le hℓb
  have hNz : L ⟨1, y⟩ ≠ 0 := hZero _ hyT (by dsimp; linarith [div_nonneg ha.le hℓ.le])
  have hSep (ρ : ℂ) (hρ : ρ ∈ closedBall (⟨2, y⟩ : ℂ) (8 / 2)) (hZ : L ρ = 0) :
      a / (3 * ℓ) ≤ ‖(⟨1, y⟩ : ℂ) - ρ‖ := by
    have hdist := mem_closedBall_iff_norm.mp hρ
    have hIm : |ρ.im - y| ≤ 4 := (Complex.abs_im_le_norm _).trans (by norm_num at hdist ⊢; exact hdist)
    have hDiff := abs_le.mp ((abs_abs_sub_abs_le_abs_sub ρ.im y).trans hIm)
    have hρθ : T ≤ |ρ.im| := by linarith [hDiff.1]
    have hℓρ : 0 < Real.log |ρ.im| := Real.log_pos (one_lt_two.trans_le (hT.trans hρθ))
    have hbound : |ρ.im| ≤ 3 * |y| := by linarith [hDiff.2]
    have hLog := Real.log_le_log (zero_lt_one.trans (one_lt_two.trans_le (hT.trans hρθ))) hbound
    rw [Real.log_mul (by norm_num) (zero_lt_one.trans_le (one_le_two.trans hy₂)).ne'] at hLog
    have h3 : Real.log (3 : ℝ) ≤ 2 * ℓ := by
      have hh : (3 : ℝ) ≤ |y| ^ 2 := (by norm_num : (3 : ℝ) ≤ 2 ^ 2).trans
        (pow_le_pow_left₀ (by norm_num) hy₂ _)
      have h := Real.log_le_log (by norm_num : (0 : ℝ) < 3) hh
      rwa [Real.log_pow, Nat.cast_ofNat] at h
    have h3ℓ : Real.log |ρ.im| ≤ 3 * ℓ := by linarith
    have hg : ρ.re < 1 - a / Real.log |ρ.im| :=
      lt_of_not_ge (fun hz ↦ hZero ρ hρθ hz hZ)
    have h := div_le_div_of_nonneg_left ha.le hℓρ h3ℓ
    have hRe : a / (3 * ℓ) ≤ 1 - ρ.re := by linarith
    exact hRe.trans ((le_abs_self _).trans (Complex.abs_re_le_norm ((⟨1, y⟩ : ℂ) - ρ)))
  obtain ⟨hAn, hc, hB⟩ := hD y hyT
  have h := RiemannMasullo.landau_norm_logDeriv_le_of_zero_separation
    (one_lt_pow₀ (one_lt_two.trans_le hy₂) hN.ne') (by norm_num : (0 : ℝ) < 8)
    (div_pos ha (by positivity : 0 < 3 * ℓ)) hAn hc hB
    (by norm_num) hNz hSep
  refine ⟨hNz, h.trans ?_⟩
  rw [Real.log_pow]
  change 300 * ((N : ℝ) * ℓ) / 8 + (((N : ℝ) * ℓ) / b) / (a / (3 * ℓ)) ≤ _
  have h₁ : 300 * ((N : ℝ) * ℓ) / 8 ≤ (N : ℝ) * (300 / (8 * b)) * ℓ ^ 2 := by
    have ht : ℓ * b ≤ ℓ ^ 2 := by rw [pow_two]; exact mul_le_mul_of_nonneg_left hℓb hℓ.le
    calc
      _ = (N : ℝ) * 300 / 8 * ℓ := by ring
      _ ≤ ((N : ℝ) * 300 / 8) * (ℓ ^ 2 / b) :=
        mul_le_mul_of_nonneg_left ((le_div_iff₀ hb).2 ht) (by positivity)
      _ = _ := by ring
  have h₂ : (((N : ℝ) * ℓ) / b) / (a / (3 * ℓ)) = (N : ℝ) * (3 / (b * a)) * ℓ ^ 2 := by
    field_simp
  rw [h₂]
  refine (add_le_add_left h₁ _).trans_eq ?_
  ring

set_option maxHeartbeats 400000 in
include μ hν in
/-- Corollary B.6.1.5. The logarithmic derivative of the actual finite Hecke
continuation on real part one is (O((log |t|)^2)) at both ends of the line. -/
theorem exists_manuscriptFiniteHecke_logDeriv_oneLine (χ : PontryaginDual (IdeleClass F)) :
    ∃ (L : ℂ → ℂ) (C T : ℝ), 0 ≤ C ∧ MeromorphicOn L univ ∧
      EqOn L (manuscriptFiniteHeckeEuler F χ) {z | 1 < z.re} ∧
      ∀ y : ℝ, T ≤ |y| → L ⟨1, y⟩ ≠ 0 ∧ ‖logDeriv L ⟨1, y⟩‖ ≤ C * (Real.log |y|) ^ 2 := by
  obtain ⟨t, ht, _⟩ := existsUnique_heckeHeight F χ
  obtain ⟨L, C, T, hC, hT, hm, he, hL⟩ :=
    exists_globalFiniteHecke_logDeriv_oneLine F ν η μ hν (heckeNormOneRestriction F χ)
  let b : ℂ := (t : ℂ) * Complex.I
  let q (z : ℂ) := z - b
  have hre (z : ℂ) : (q z).re = z.re := by simp [q, b, Complex.sub_re, Complex.mul_re]
  refine ⟨L ∘ q, 4 * C, T + |t|, by positivity,
    fun z _ ↦ (hm (q z) (mem_univ _)).comp_analyticAt (g := q) (analyticAt_id.sub analyticAt_const), ?_, ?_⟩
  · intro z hz
    rw [manuscriptFiniteHeckeEuler_shift F χ ht]
    exact he (show 1 < (q z).re by rwa [hre])
  intro y hy
  have hyt : T ≤ |y - t| := by linarith [abs_sub_abs_le_abs_sub y t]
  obtain ⟨hn, h⟩ := hL (y - t) hyt
  have hy₂ : 2 ≤ |y| := by linarith [abs_nonneg t]
  have heq : q ⟨1, y⟩ = ⟨1, y - t⟩ := by
    apply Complex.ext <;> simp [q, b, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im]
  have hlog : logDeriv (L ∘ q) ⟨1, y⟩ = logDeriv L ⟨1, y - t⟩ := by
    simp only [logDeriv_apply, Function.comp_apply]
    rw [show deriv (L ∘ q) ⟨1, y⟩ = deriv L (q ⟨1, y⟩) from deriv_comp_sub_const _ _ _, heq]
  have hlog₁ : Real.log |y - t| ≤ 2 * Real.log |y| := by
    exact log_abs_sub_le hy₂ (hT.trans hyt) (by linarith)
  have hlog₀ : 0 ≤ Real.log |y - t| := Real.log_nonneg (one_le_two.trans (hT.trans hyt))
  refine ⟨by simpa only [Function.comp_apply, heq] using hn, ?_⟩
  rw [hlog]
  calc
    _ ≤ C * (Real.log |y - t|) ^ 2 := h
    _ ≤ C * (2 * Real.log |y|) ^ 2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlog₀ hlog₁ _) hC
    _ = _ := by ring


/-- A meromorphic function has no positive-order zeros close to a point
where its order is nonpositive, including when that point is a pole. -/
private theorem isOpen_nonpositive_meromorphic_order {L : ℂ → ℂ} (hm : MeromorphicOn L univ) :
    IsOpen {z | meromorphicOrderAt L z ≤ 0} := by
  apply isOpen_iff_mem_nhds.mpr
  intro z hz
  change meromorphicOrderAt L z ≤ 0 at hz
  have hf := hm z (mem_univ _)
  have hn : meromorphicOrderAt L z ≠ ⊤ := ne_of_lt (lt_of_le_of_lt hz (by simp))
  have hn' := (meromorphicOrderAt_ne_top_iff_eventually_ne_zero hf).mp hn
  have he : ∀ᶠ w in 𝓝[≠] z, meromorphicOrderAt L w ≤ 0 := by
    filter_upwards [hf.eventually_analyticAt, hn'] with w ha hw
    exact (ha.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr hw).le
  filter_upwards [eventually_nhdsWithin_iff.mp he] with w hw
  by_cases h : w = z
  · simpa only [h] using hz
  · exact hw h

private theorem nonpositive_meromorphic_order_near_oneLine {L : ℂ → ℂ}
    (hm : MeromorphicOn L univ) (hline : ∀ y : ℝ, meromorphicOrderAt L ⟨1, y⟩ ≤ 0)
    (T : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z : ℂ, |z.im| ≤ T → z.re ∈ Icc (1 - δ) 1 →
      meromorphicOrderAt L z ≤ 0 := by
  let f (y : ℝ) : ℂ := ⟨1, y⟩
  have hf : Continuous f := by
    have he : f = fun y : ℝ ↦ 1 + (y : ℂ) * Complex.I := by
      funext y
      apply Complex.ext <;> simp [f, Complex.mul_re, Complex.mul_im]
    rw [he]
    fun_prop
  let D := f '' Icc (-T) T
  let U := {z | meromorphicOrderAt L z ≤ 0}
  have hDU : D ⊆ U := fun _ ⟨y, _, h⟩ ↦ h ▸ hline y
  obtain ⟨δ, hδ, h⟩ := (isCompact_Icc.image hf).exists_cthickening_subset_open
    (isOpen_nonpositive_meromorphic_order hm) hDU
  refine ⟨δ, hδ, fun z hz hx ↦ h ?_⟩
  apply mem_cthickening_of_dist_le z (f z.im) δ D ⟨z.im, abs_le.mp hz, rfl⟩
  have he : z - f z.im = ((z.re - 1 : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [f]
  rw [dist_eq_norm, he, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr hx.2)]
  linarith [hx.1]

/-- An absolute numerator for the Hecke zero-free region. -/
noncomputable def finiteHeckeZeroFreeNumerator : ℝ := heckeZeroFreeBase / 8

theorem finiteHeckeZeroFreeNumerator_pos : 0 < finiteHeckeZeroFreeNumerator :=
  div_pos heckeZeroFreeBase_pos (by norm_num)

set_option maxHeartbeats 450000 in
include μ hν in
private theorem exists_globalFiniteHecke_zeroFree_all_heights (ω : PontryaginDual (K F)) :
    ∃ (L : ℂ → ℂ) (B : ℝ), 1 ≤ B ∧ MeromorphicOn L univ ∧
      EqOn L (globalFiniteHeckeEuler F ω) {z | 1 < z.re} ∧
      ∀ z : ℂ,
        1 - finiteHeckeZeroFreeNumerator /
          ((Module.finrank ℚ F : ℝ) ^ 4 * Real.log (B * (|z.im| + 3))) ≤ z.re →
        meromorphicOrderAt L z ≤ 0 := by
  obtain ⟨L, T, hT, hm, he, ha, hZ, _⟩ :=
    exists_globalFiniteHecke_degree_zeroFree F ν η μ hν ω
  have hline (y : ℝ) : meromorphicOrderAt L ⟨1, y⟩ ≤ 0 := by
    have h := globalFiniteHecke_order_le_zero_one_line F η ν μ hν ω y hm he
    have hEq : 1 + (y : ℂ) * Complex.I = ⟨1, y⟩ := by
      apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
    rwa [hEq] at h
  obtain ⟨δ, hδ, hSmall⟩ := nonpositive_meromorphic_order_near_oneLine hm hline T
  let A := finiteHeckeZeroFreeNumerator
  have hA : 0 < A := finiteHeckeZeroFreeNumerator_pos
  let d : ℝ := Module.finrank ℚ F
  have hd : 1 ≤ d := hecke_field_degree_one_le F
  have hdPow : d ≤ d ^ 4 := by
    rw [show (4 : ℕ) = 1 + 3 by decide, pow_add, pow_one]
    exact le_mul_of_one_le_right (by positivity) (one_le_pow₀ hd)
  let B := Real.exp (1 + A / δ)
  have hB : 1 ≤ B := Real.one_le_exp (by positivity)
  refine ⟨L, B, hB, hm, he, fun z hz ↦ ?_⟩
  by_cases hRight : 1 < z.re
  · have hz₀ : z ≠ 0 := by intro e; norm_num [e] at hRight
    have hz₁ : z ≠ 1 := by intro e; norm_num [e] at hRight
    have hn : L z ≠ 0 := by rw [he hRight]; exact finiteEuler_ne_zero F ω hRight
    exact ((ha z hz₀ hz₁).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr hn).le
  have hRe : z.re ≤ 1 := le_of_not_gt hRight
  have hlog : Real.log B ≤ Real.log (B * (|z.im| + 3)) := by
    apply Real.log_le_log (zero_lt_one.trans_le hB)
    exact le_mul_of_one_le_right (zero_le_one.trans hB) (by linarith [abs_nonneg z.im])
  rw [show Real.log B = 1 + A / δ by exact Real.log_exp _] at hlog
  by_cases hLarge : T ≤ |z.im|
  · have hel : 0 < Real.log |z.im| := Real.log_pos (one_lt_two.trans_le (hT.trans hLarge))
    have hBig : Real.log |z.im| ≤ Real.log (B * (|z.im| + 3)) :=
      Real.log_le_log (zero_lt_one.trans (one_lt_two.trans_le (hT.trans hLarge)))
        (by nlinarith [mul_nonneg (sub_nonneg.mpr hB) (abs_nonneg z.im)])
    have hden : d * Real.log |z.im| ≤ d ^ 4 * Real.log (B * (|z.im| + 3)) :=
      mul_le_mul hdPow hBig hel.le (by positivity)
    have hw := div_le_div_of_nonneg_left hA.le (by positivity : 0 < d * Real.log |z.im|) hden
    have hz' : 1 - A / (d * Real.log |z.im|) ≤ z.re := by linarith
    have hn : L z ≠ 0 := hZ z hLarge hz'
    have hz₀ : z ≠ 0 := by intro e; rw [e] at hLarge; norm_num at hLarge; linarith
    have hz₁ : z ≠ 1 := by intro e; rw [e] at hLarge; norm_num at hLarge; linarith
    exact ((ha z hz₀ hz₁).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr hn).le
  · have hD : A / δ ≤ d ^ 4 * Real.log (B * (|z.im| + 3)) := by
      have hL : A / δ ≤ Real.log (B * (|z.im| + 3)) := by linarith
      exact (le_mul_of_one_le_left (by positivity : 0 ≤ A / δ) (one_le_pow₀ hd)).trans
        (mul_le_mul_of_nonneg_left hL (by positivity))
    have hp : 0 < Real.log (B * (|z.im| + 3)) :=
      (show 0 < 1 + A / δ by positivity).trans_le hlog
    have hwidth : A / (d ^ 4 * Real.log (B * (|z.im| + 3))) ≤ δ :=
      (div_le_comm₀ (by positivity) hδ).mpr hD
    exact hSmall z (le_of_lt (lt_of_not_ge hLarge)) ⟨by linarith, hRe⟩

set_option maxHeartbeats 350000 in
include μ hν in
/-- Corrected Proposition B.6.1.1, with a character-dependent scale
and a universal numerator. Nonpositive order distinguishes poles from zeros. -/
theorem exists_manuscriptFiniteHecke_zeroFree_region (χ : PontryaginDual (IdeleClass F)) :
    ∃ (L : ℂ → ℂ) (B : ℝ), 1 ≤ B ∧ MeromorphicOn L univ ∧
      EqOn L (manuscriptFiniteHeckeEuler F χ) {z | 1 < z.re} ∧
      ∀ z : ℂ,
        1 - finiteHeckeZeroFreeNumerator /
          ((Module.finrank ℚ F : ℝ) ^ 4 * Real.log (B * (|z.im| + 3))) ≤ z.re →
        meromorphicOrderAt L z ≤ 0 := by
  obtain ⟨t, ht, _⟩ := existsUnique_heckeHeight F χ
  obtain ⟨L, B, hB, hm, he, hZ⟩ :=
    exists_globalFiniteHecke_zeroFree_all_heights F ν η μ hν (heckeNormOneRestriction F χ)
  let b : ℂ := (t : ℂ) * Complex.I
  let q (z : ℂ) := z - b
  have hre (z : ℂ) : (q z).re = z.re := by simp [q, b, Complex.sub_re, Complex.mul_re]
  have him (z : ℂ) : (q z).im = z.im - t := by simp [q, b, Complex.sub_im, Complex.mul_im]
  let D := B * (1 + |t|)
  have hD : 1 ≤ D := one_le_mul_of_one_le_of_one_le hB (by linarith [abs_nonneg t])
  have hq (z : ℂ) : AnalyticAt ℂ q z := analyticAt_id.sub analyticAt_const
  refine ⟨L ∘ q, D, hD, fun z _ ↦ (hm (q z) (mem_univ _)).comp_analyticAt (g := q) (hq z), ?_, ?_⟩
  · intro z hz
    rw [manuscriptFiniteHeckeEuler_shift F χ ht]
    exact he (show 1 < (q z).re by rwa [hre])
  · intro z hz
    rw [meromorphicOrderAt_comp_of_deriv_ne_zero (hq z) (by simp [q])]
    apply hZ (q z)
    rw [him, hre]
    have hlog : 0 < Real.log (B * (|z.im - t| + 3)) := by
      apply Real.log_pos
      have h := le_mul_of_one_le_left (show 0 ≤ |z.im - t| + 3 by positivity) hB
      linarith [abs_nonneg (z.im - t)]
    have hlog' : Real.log (B * (|z.im - t| + 3)) ≤ Real.log (D * (|z.im| + 3)) := by
      apply Real.log_le_log (by positivity : 0 < B * (|z.im - t| + 3))
      dsimp [D]
      rw [mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (zero_le_one.trans hB)
      nlinarith [abs_sub z.im t, mul_nonneg (abs_nonneg t) (abs_nonneg z.im), abs_nonneg t]
    have hw := div_le_div_of_nonneg_left finiteHeckeZeroFreeNumerator_pos.le
      (mul_pos (pow_pos (zero_lt_one.trans_le (hecke_field_degree_one_le F)) 4) hlog)
      (mul_le_mul_of_nonneg_left hlog' (pow_nonneg (zero_le_one.trans (hecke_field_degree_one_le F)) 4))
    linarith

private theorem meromorphicOrder_eq_of_agree_right {L G : ℂ → ℂ}
    (hL : MeromorphicOn L univ) (hG : MeromorphicOn G univ)
    (he : EqOn L G {z | 1 < z.re}) (z : ℂ) :
    meromorphicOrderAt L z = meromorphicOrderAt G z := by
  have hm : MeromorphicOn (L - G) univ := hL.sub hG
  have htop : meromorphicOrderAt (L - G) (2 : ℂ) = ⊤ := by
    apply meromorphicOrderAt_eq_top_iff.mpr
    have hmem : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 : ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    have hevent : ∀ᶠ w : ℂ in 𝓝 (2 : ℂ), 1 < w.re := hmem
    filter_upwards [hevent.filter_mono nhdsWithin_le_nhds] with w hw
    exact sub_eq_zero.mpr (he hw)
  have hz : meromorphicOrderAt (L - G) z = ⊤ := by
    by_contra hn
    exact (hm.meromorphicOrderAt_ne_top_of_isPreconnected isPreconnected_univ
      (mem_univ z) (mem_univ (2 : ℂ)) hn) htop
  apply meromorphicOrderAt_congr
  filter_upwards [meromorphicOrderAt_eq_top_iff.mp hz] with w hw
  exact sub_eq_zero.mp hw

include μ hν in
/-- The corrected zero-free region for every meromorphic continuation of
the finite Euler product. Its constant is the same for all number fields. -/
theorem manuscriptFiniteHecke_zeroFree_region (χ : PontryaginDual (IdeleClass F)) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ L : ℂ → ℂ, MeromorphicOn L univ →
      EqOn L (manuscriptFiniteHeckeEuler F χ) {z | 1 < z.re} →
      ∀ z : ℂ,
        1 - finiteHeckeZeroFreeNumerator /
          ((Module.finrank ℚ F : ℝ) ^ 4 * Real.log (B * (|z.im| + 3))) ≤ z.re →
        meromorphicOrderAt L z ≤ 0 := by
  obtain ⟨G, B, hB, hg, he, hZ⟩ := exists_manuscriptFiniteHecke_zeroFree_region F ν η μ hν χ
  refine ⟨B, hB, fun L hL heL z hz ↦ ?_⟩
  rw [meromorphicOrder_eq_of_agree_right hL hg (fun w hw ↦ (heL hw).trans (he hw).symm) z]
  exact hZ z hz

end

end Masullo
