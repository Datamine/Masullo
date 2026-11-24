/-
Adapted from the Apache-2.0 RiemannMasullo project, commit 3b1902a.
See External/PROVENANCE.md and External/RiemannMasullo.LICENSE.
-/
import MellinBergman
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

open Filter Function MeasureTheory Set
open scoped ContDiff ENNReal FourierTransform Topology

namespace Masullo

noncomputable section

local notation "verticalPoint" =>
  (fun (σ y : ℝ) ↦ (σ : ℂ) + (y : ℂ) * Complex.I)
local notation "verticalTrace" =>
  (fun (Φ : ℂ → ℂ) (σ : ℝ) (y : ℝ) ↦ Φ (verticalPoint σ y))
local notation "atAbsInfty" => (comap abs atTop)
local notation "closedStrip" => (fun a b : ℝ ↦ Complex.re ⁻¹' Icc a b)
set_option quotPrecheck false in
local notation "stripWithTop" =>
  (fun (a : ℝ) (b : WithTop ℝ) ↦ {s : ℂ | a < s.re ∧ (s.re : WithTop ℝ) < b})
local notation "logWeight" =>
  (fun (σ x : ℝ) ↦ (Real.exp (σ * x) : ℂ))
local notation "fromLog" => (fun (f : ℝ → ℂ) (t : ℝ) ↦ f (Real.log t))

/-- The logarithmic profile in (B.2.1.19) is
m-times continuously differentiable and its derivatives through order m vanish at infinity. -/
def MemLogContDiffZero (m : ℕ) (f : ℝ → ℂ) : Prop :=
  ContDiff ℝ (m : ℕ∞) f ∧
    ∀ j ≤ m, Tendsto (iteratedDeriv j f) (cocompact ℝ) (𝓝 0)

/-- An upward vertical line integral uses
the parameter y ↦ σ + iy and its differential i dy. -/
private def verticalLineIntegral (Φ : ℂ → ℂ) (σ : ℝ) : ℂ :=
  Complex.I * ∫ y : ℝ, Φ (verticalPoint σ y)

open scoped Interval in
/-- Two integrable vertical traces of a holomorphic function have equal
integrals if the horizontal contributions tend to zero, even along different
sequences of lower and upper heights. -/
theorem verticalTrace_integral_eq_of_contour_limits {ι : Type*} {l : Filter ι} [l.NeBot] [l.IsCountablyGenerated]
    {K : ℂ → ℂ} {c d : ℝ} (hcd : c ≤ d)
    (hK : DifferentiableOn ℂ K (Complex.re ⁻¹' Icc c d))
    (hc : Complex.VerticalIntegrable K c) (hd : Complex.VerticalIntegrable K d)
    {lo hi : ι → ℝ} (hlo : Tendsto lo l atBot) (hhi : Tendsto hi l atTop)
    (hLower : Tendsto (fun n ↦ ∫ x in c..d, K (verticalPoint x (lo n))) l (𝓝 0))
    (hUpper : Tendsto (fun n ↦ ∫ x in c..d, K (verticalPoint x (hi n))) l (𝓝 0)) :
    (∫ y : ℝ, K (verticalPoint d y)) = ∫ y : ℝ, K (verticalPoint c y) := by
  have hrect (t : ι) :
      (∫ x in c..d, K (verticalPoint x (lo t))) - (∫ x in c..d, K (verticalPoint x (hi t))) +
      Complex.I • (∫ y in lo t..hi t, K (verticalPoint d y)) -
      Complex.I • (∫ y in lo t..hi t, K (verticalPoint c y)) = 0 := by
    apply Complex.integral_boundary_rect_eq_zero_of_differentiableOn K (⟨c, lo t⟩ : ℂ) (⟨d, hi t⟩ : ℂ)
    apply hK.mono
    intro w hw
    simpa only [uIcc_of_le hcd] using hw.1
  have hv (x : ℝ) (hi' : Complex.VerticalIntegrable K x) :=
    intervalIntegral_tendsto_integral hi' hlo hhi
  have hlim := (((hLower.sub hUpper).add ((hv d hd).const_smul Complex.I)).sub
    ((hv c hc).const_smul Complex.I))
  have heq := tendsto_nhds_unique hlim (tendsto_const_nhds.congr fun t ↦ (hrect t).symm)
  apply mul_left_cancel₀ Complex.I_ne_zero
  simpa [smul_eq_mul, sub_eq_zero] using heq

/-- Shifting symmetric expanding rectangles is a special case of the
contour limit with independently chosen heights. -/
private theorem verticalIntegral_eq_of_contour_shift {K : ℂ → ℂ} {c d : ℝ} (hcd : c ≤ d)
    (hK : DifferentiableOn ℂ K (Complex.re ⁻¹' Icc c d))
    (hc : Complex.VerticalIntegrable K c) (hd : Complex.VerticalIntegrable K d)
    (hh : Tendsto (fun y : ℝ ↦ ∫ x in c..d, K (verticalPoint x y)) atAbsInfty (𝓝 0)) :
    verticalLineIntegral K d = verticalLineIntegral K c := by
  have ht : Tendsto (fun t : ℝ ↦ t) atTop atAbsInfty := by
    apply tendsto_comap_iff.mpr
    exact tendsto_abs_atTop_atTop
  have hn : Tendsto (fun t : ℝ ↦ -t) atTop atAbsInfty := by
    apply tendsto_comap_iff.mpr
    simpa [Function.comp_def] using tendsto_abs_atTop_atTop
  exact congrArg (Complex.I * ·) (verticalTrace_integral_eq_of_contour_limits
    hcd hK hc hd tendsto_neg_atTop_atBot tendsto_id (hh.comp hn) (hh.comp ht))

/-- A weighted bound on a positive closed strip gives uniform decay in the height. -/
private theorem verticalTrace_polynomialDecay {F : ℂ → ℂ} {c d N : ℝ} (hc : 0 < c)
    (hN : 0 ≤ N)
    (hBound : BddAbove ((fun s : ℂ ↦ ‖s‖ ^ N * ‖F s‖) '' closedStrip c d)) :
    ∃ C ≥ (0 : ℝ), ∀ σ ∈ Icc c d, ∀ y : ℝ,
      ‖verticalTrace F σ y‖ ≤ C * (1 + ‖y‖) ^ (-N) := by
  obtain ⟨B, hB⟩ := hBound
  let A := 1 + c⁻¹
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨A ^ N * max B 0, by positivity, ?_⟩
  intro σ hσ y
  let z := verticalPoint σ y
  have hre : c ≤ ‖z‖ := hσ.1.trans (by
    simpa [z, abs_of_pos (hc.trans_le hσ.1)] using Complex.abs_re_le_norm z)
  have him : ‖y‖ ≤ ‖z‖ := by simpa [z, Real.norm_eq_abs] using Complex.abs_im_le_norm z
  have hone : 1 ≤ c⁻¹ * ‖z‖ := (one_le_inv_mul₀ hc).mpr hre
  have hle : 1 + ‖y‖ ≤ A * ‖z‖ := by
    calc
      1 + ‖y‖ ≤ c⁻¹ * ‖z‖ + ‖z‖ := add_le_add hone him
      _ = A * ‖z‖ := by dsimp only [A]; ring
  have hz : z ∈ closedStrip c d := by simpa [z] using hσ
  have hF := (hB (mem_image_of_mem _ hz)).trans (le_max_left B 0)
  rw [Real.rpow_neg (by positivity), ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  calc
    ‖F z‖ * (1 + ‖y‖) ^ N ≤ ‖F z‖ * (A * ‖z‖) ^ N := by
      gcongr
    _ = A ^ N * (‖z‖ ^ N * ‖F z‖) := by rw [Real.mul_rpow hA.le (norm_nonneg _)]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hF (by positivity)

/-- An integrable power envelope controls every moment whose remaining decay has exponent
greater than one. -/
private theorem integrable_verticalTrace_moment {f : ℝ → ℂ} (hf : Continuous f)
    {C N : ℝ} (hbound : ∀ y, ‖f y‖ ≤ C * (1 + ‖y‖) ^ (-N))
    (j : ℕ) (hj : (j : ℝ) < N - 1) :
    Integrable (fun y : ℝ ↦ y ^ j • f y) := by
  have hmodel : Integrable (fun y : ℝ ↦ (1 + ‖y‖) ^ (-(N - (j : ℝ)))) :=
    integrable_one_add_norm (by simpa using (show 1 < N - (j : ℝ) by linarith))
  apply (hmodel.const_mul C).mono' (by fun_prop)
  filter_upwards with y
  rw [norm_smul]
  calc
    ‖y ^ j‖ * ‖f y‖ ≤ (1 + ‖y‖) ^ j * (C * (1 + ‖y‖) ^ (-N)) := by
      rw [norm_pow]
      gcongr
      · exact le_add_of_nonneg_left zero_le_one
      · exact hbound y
    _ = C * (1 + ‖y‖) ^ (-(N - (j : ℝ))) := by
      rw [← Real.rpow_natCast, mul_left_comm, ← Real.rpow_add (by positivity)]
      congr 2
      ring

/-- The inverse Mellin integral agrees on either side of a closed strip when the
vertical traces are integrable and have uniform power decay with exponent at least one. -/
theorem mellinInv_eq_of_verticalTrace_decay {F : ℂ → ℂ} {c d C N : ℝ}
    (hcd : c ≤ d) (hF : DifferentiableOn ℂ F (closedStrip c d))
    (hc : Complex.VerticalIntegrable F c) (hd : Complex.VerticalIntegrable F d)
    (hC : 0 ≤ C) (hN : 1 ≤ N)
    (hdecay : ∀ σ ∈ Icc c d, ∀ y : ℝ, ‖verticalTrace F σ y‖ ≤ C * (1 + ‖y‖) ^ (-N))
    {t : ℝ} (ht : 0 < t) : mellinInv c F t = mellinInv d F t := by
  let P (s : ℂ) := (t : ℂ) ^ (-s)
  let K (s : ℂ) := P s * F s
  have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have hP : Differentiable ℂ P := differentiable_id.neg.const_cpow (.inl ht0)
  have hnorm (σ y : ℝ) : ‖P (verticalPoint σ y)‖ = t ^ (-σ) := by
    simp [P, Complex.norm_cpow_eq_rpow_re_of_pos ht]
  have hi (σ : ℝ) (h : Complex.VerticalIntegrable F σ) : Complex.VerticalIntegrable K σ := by
    have hcont : Continuous (verticalTrace P σ) := hP.continuous.comp (by fun_prop)
    exact h.bdd_mul hcont.aestronglyMeasurable (Eventually.of_forall fun y ↦ (hnorm σ y).le)
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := c) (b := d)).bddAbove_image
    ((Real.continuous_const_rpow ht.ne').comp continuous_neg).continuousOn
  have hh : Tendsto (fun y : ℝ ↦ ∫ x in c..d, K (verticalPoint x y)) atAbsInfty (𝓝 0) := by
    apply squeeze_zero_norm'
    · filter_upwards with y
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro σ hσ
      have hσ' := Ioc_subset_Icc_self ((uIoc_of_le hcd) ▸ hσ)
      have hb : t ^ (-σ) ≤ B := hB (mem_image_of_mem _ hσ')
      have hpow : (1 + ‖y‖) ^ (-N) ≤ (1 + ‖y‖)⁻¹ := by
        rw [← Real.rpow_neg_one]
        exact Real.rpow_le_rpow_of_exponent_le (by simp) (by linarith)
      change ‖P (verticalPoint σ y) * F (verticalPoint σ y)‖ ≤ _
      rw [norm_mul, hnorm, mul_comm (t ^ (-σ))]
      calc
        _ ≤ (C * (1 + ‖y‖) ^ (-N)) * t ^ (-σ) :=
          mul_le_mul_of_nonneg_right (hdecay σ hσ' y) (by positivity)
        _ ≤ (C * (1 + ‖y‖)⁻¹) * B :=
          mul_le_mul (mul_le_mul_of_nonneg_left hpow hC) hb (by positivity) (by positivity)
        _ = C * B / (1 + ‖y‖) := by ring
    · have hy : Tendsto (fun y : ℝ ↦ 1 + ‖y‖) atAbsInfty atTop := by
        simpa only [Real.norm_eq_abs] using
          tendsto_atTop_add_const_left atAbsInfty (1 : ℝ) (tendsto_comap :
            Tendsto (abs : ℝ → ℝ) atAbsInfty atTop)
      simpa only [zero_mul] using
        (((tendsto_const_nhds (x := C * B)).div_atTop hy).mul_const |d - c|)
  have heq := verticalIntegral_eq_of_contour_shift hcd (hP.differentiableOn.mul hF)
    (hi c hc) (hi d hd) hh
  unfold verticalLineIntegral at heq
  exact congrArg ((1 / (2 * Real.pi)) • ·) (mul_left_cancel₀ Complex.I_ne_zero heq).symm

/-- In logarithmic coordinates the normalized inverse Mellin integral is the
Fourier transform of the appropriately rescaled vertical trace. -/
theorem mellinInv_exp_eq_fourier (F : ℂ → ℂ) (σ x : ℝ) :
    mellinInv σ F (Real.exp x) =
      logWeight (-σ) x * 𝓕 (fun y : ℝ ↦ verticalTrace F σ (2 * Real.pi * y)) x := by
  rw [mellinInv_eq_fourierInv _ _ (Real.exp_pos x), Real.log_exp, Real.fourierInv_eq_fourier_neg,
    neg_neg, smul_eq_mul, Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero x)),
    ← Complex.ofReal_log (Real.exp_pos x).le, Real.log_exp]
  simp only [Complex.ofReal_exp, Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_ofNat,
    mul_comm (x : ℂ) (-(σ : ℂ))]

/-- Proposition B.2.1.8. Polynomial decay of a holomorphic
function on closed interior strips gives a Mellin inverse with the stated differentiability,
vanishing and square-integrability properties. The measure dt/t becomes
Lebesgue measure in logarithmic coordinates. -/
theorem exists_mellin_of_polynomial_decay
    (a : ℝ) (b : WithTop ℝ) (ha : 0 < a) (hab : (a : WithTop ℝ) < b)
    (N : ℝ) (hN : 2 < N) (F : ℂ → ℂ) (hF : DifferentiableOn ℂ F (stripWithTop a b))
    (hBound : ∀ c d : ℝ, a < c → c ≤ d → (d : WithTop ℝ) < b →
      BddAbove ((fun s : ℂ ↦ ‖s‖ ^ N * ‖F s‖) '' closedStrip c d))
    (m : ℕ) (hm : (m : ℝ) < N - 1) :
    ∃ φ : ℝ → ℂ, ContDiffOn ℝ (m : ℕ∞) φ (Ioi 0) ∧
      (∀ σ : ℝ, a < σ → (σ : WithTop ℝ) < b →
        MemLogContDiffZero m (fun x : ℝ ↦ logWeight σ x * φ (Real.exp x)) ∧
        MemLp (fun x : ℝ ↦ logWeight σ x * φ (Real.exp x)) 2 volume) ∧
      ∀ s ∈ stripWithTop a b, HasMellin φ s (F s) := by
  let trace (σ : ℝ) := fun y : ℝ ↦ verticalTrace F σ (2 * Real.pi * y)
  let g (σ : ℝ) : ℝ → ℂ := 𝓕 (trace σ)
  have between {σ : ℝ} (hσ : (σ : WithTop ℝ) < b) :
      ∃ d : ℝ, σ < d ∧ (d : WithTop ℝ) < b := by
    obtain ⟨d, hd₁, hd₂⟩ := exists_between hσ
    lift d to ℝ using ne_of_lt (hd₂.trans_le le_top)
    exact ⟨d, WithTop.coe_lt_coe.mp hd₁, hd₂⟩
  obtain ⟨σ₀, hσ₀a, hσ₀b⟩ := between hab
  have hcont (σ : ℝ) (hσa : a < σ) (hσb : (σ : WithTop ℝ) < b) :
      Continuous (verticalTrace F σ) :=
    hF.continuousOn.comp_continuous (by fun_prop) fun y ↦ by simpa using And.intro hσa hσb
  have hverticalMoment (σ : ℝ) (hσa : a < σ) (hσb : (σ : WithTop ℝ) < b)
      (j : ℕ) (hj : (j : ℝ) < N - 1) : Integrable (fun y : ℝ ↦ y ^ j • verticalTrace F σ y) := by
    obtain ⟨C, _, hdecay⟩ := verticalTrace_polynomialDecay (ha.trans hσa)
      (by linarith : 0 ≤ N) (hBound σ σ hσa le_rfl hσb)
    exact integrable_verticalTrace_moment (hcont σ hσa hσb) (hdecay σ ⟨le_rfl, le_rfl⟩) j hj
  have hline (σ : ℝ) (hσa : a < σ) (hσb : (σ : WithTop ℝ) < b) :
      Complex.VerticalIntegrable F σ := by
    simpa [Complex.VerticalIntegrable] using hverticalMoment σ hσa hσb 0 (by simp; linarith)
  have hmoment (σ : ℝ) (hσa : a < σ) (hσb : (σ : WithTop ℝ) < b) (j : ℕ) (hj : j ≤ m) :
      Integrable (fun y : ℝ ↦ y ^ j • trace σ y) := by
    have hscale : 2 * Real.pi ≠ 0 := by positivity
    have hi := hverticalMoment σ hσa hσb j ((Nat.cast_le.mpr hj).trans_lt hm)
    convert (hi.comp_mul_left' hscale).smul ((2 * Real.pi)⁻¹ ^ j) using 1
    funext y
    simp only [trace, Pi.smul_apply, smul_smul, ← mul_pow, ← mul_assoc,
      inv_mul_cancel₀ hscale, one_mul]
  have hsmooth (σ : ℝ) (hσa : a < σ) (hσb : (σ : WithTop ℝ) < b) :
      MemLogContDiffZero m (g σ) := by
    have hmom (j : ℕ) (hj : (j : ℕ∞) ≤ m) := hmoment σ hσa hσb j (by exact_mod_cast hj)
    refine ⟨Real.contDiff_fourier (fun j hj ↦ ?_), fun j hj ↦ ?_⟩
    · simpa only [norm_smul, norm_pow] using (hmom j hj).norm
    · change Tendsto (iteratedDeriv j (𝓕 (trace σ))) _ _
      rw [Real.iteratedDeriv_fourier (N := (m : ℕ∞)) hmom (by exact_mod_cast hj)]
      exact Real.zero_at_infty_fourier _
  have hordered (c d : ℝ) (hca : a < c) (hcd : c ≤ d) (hdb : (d : WithTop ℝ) < b)
      {t : ℝ} (ht : 0 < t) : mellinInv c F t = mellinInv d F t := by
    have hcb : (c : WithTop ℝ) < b := (WithTop.coe_le_coe.mpr hcd).trans_lt hdb
    obtain ⟨C, hC, hdecay⟩ := verticalTrace_polynomialDecay (ha.trans hca)
      (by linarith : 0 ≤ N) (hBound c d hca hcd hdb)
    refine mellinInv_eq_of_verticalTrace_decay hcd (hF.mono ?_) (hline c hca hcb)
      (hline d (hca.trans_le hcd) hdb) hC (by linarith) hdecay ht
    intro z hz
    exact ⟨hca.trans_le hz.1, (WithTop.coe_le_coe.mpr hz.2).trans_lt hdb⟩
  let p (x : ℝ) := logWeight (-σ₀) x * g σ₀ x
  have hp : ContDiff ℝ (m : ℕ∞) p := by
    have hw : ContDiff ℝ (m : ℕ∞) (logWeight (-σ₀)) :=
      Complex.ofRealCLM.contDiff.comp (by fun_prop : ContDiff ℝ (m : ℕ∞)
        (fun x : ℝ ↦ Real.exp (-σ₀ * x)))
    exact hw.mul (hsmooth σ₀ hσ₀a hσ₀b).1
  have hweight (σ : ℝ) (hσa : a < σ) (hσb : (σ : WithTop ℝ) < b) :
      (fun x ↦ logWeight σ x * p x) = g σ := by
    funext x
    have hshift : mellinInv σ₀ F (Real.exp x) = mellinInv σ F (Real.exp x) := by
      rcases le_total σ₀ σ with h | h
      · exact hordered σ₀ σ hσ₀a h hσb (Real.exp_pos x)
      · exact (hordered σ σ₀ hσa h hσ₀b (Real.exp_pos x)).symm
    rw [mellinInv_exp_eq_fourier, mellinInv_exp_eq_fourier] at hshift
    change logWeight σ x * p x = g σ x
    rw [show p x = logWeight (-σ) x * g σ x from hshift, ← mul_assoc, ← Complex.ofReal_mul,
      ← Real.exp_add]
    simp
  have htransition (σ τ : ℝ) (hσa : a < σ) (hσb : (σ : WithTop ℝ) < b)
      (hτa : a < τ) (hτb : (τ : WithTop ℝ) < b) (x : ℝ) :
      g σ x = logWeight (σ - τ) x * g τ x := by
    have he : logWeight σ x = logWeight (σ - τ) x * logWeight τ x := by
      change (Real.exp (σ * x) : ℂ) = (Real.exp ((σ - τ) * x) : ℂ) * (Real.exp (τ * x) : ℂ)
      rw [← Complex.ofReal_mul, ← Real.exp_add, sub_mul, sub_add_cancel]
    calc
      g σ x = logWeight σ x * p x := (congrFun (hweight σ hσa hσb) x).symm
      _ = (logWeight (σ - τ) x * logWeight τ x) * p x := congrArg (· * p x) he
      _ = logWeight (σ - τ) x * (logWeight τ x * p x) := mul_assoc _ _ _
      _ = _ := congrArg (logWeight (σ - τ) x * ·) (congrFun (hweight τ hτa hτb) x)
  let K (σ : ℝ) := ∫ y, ‖trace σ y‖
  have hK (σ : ℝ) (x : ℝ) : ‖g σ x‖ ≤ K σ :=
    VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _
  -- Shifting left for negative log coordinates and right for positive ones gives integrable tails.
  have hgInt (σ : ℝ) (hσa : a < σ) (hσb : (σ : WithTop ℝ) < b) : Integrable (g σ) := by
    obtain ⟨c, hca, hcσ⟩ := exists_between hσa
    obtain ⟨d, hσd, hdb⟩ := between hσb
    have hcb : (c : WithTop ℝ) < b := (WithTop.coe_lt_coe.mpr hcσ).trans hσb
    have hda := hσa.trans hσd
    have hmeas : AEStronglyMeasurable (g σ) volume :=
      (hsmooth σ hσa hσb).1.continuous.aestronglyMeasurable
    rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ)), integrableOn_union]
    constructor
    · apply ((integrableOn_exp_mul_Iic (sub_pos.mpr hcσ) 0).const_mul (K c)).mono'
        hmeas.restrict
      filter_upwards with x
      rw [htransition σ c hσa hσb hca hcb x, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (Real.exp_pos _).le, mul_comm]
      exact mul_le_mul_of_nonneg_right (hK c x) (Real.exp_pos _).le
    · apply ((integrableOn_exp_mul_Ioi (sub_neg.mpr hσd) 0).const_mul (K d)).mono'
        hmeas.restrict
      filter_upwards with x
      rw [htransition σ d hσa hσb hda hdb x, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (Real.exp_pos _).le, mul_comm]
      exact mul_le_mul_of_nonneg_right (hK d x) (Real.exp_pos _).le
  refine ⟨fromLog p, hp.contDiffOn.comp (Real.contDiffOn_log.mono ?_) (mapsTo_univ _ _), ?_, ?_⟩
  · intro x hx
    exact ne_of_gt hx
  · intro σ hσa hσb
    simp only [Real.log_exp, hweight σ hσa hσb]
    refine ⟨hsmooth σ hσa hσb, ?_⟩
    apply (integrable_norm_rpow_iff (hgInt σ hσa hσb).aestronglyMeasurable
      (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by simp)).mp
    apply ((hgInt σ hσa hσb).norm.const_mul (K σ)).mono'
      (((hsmooth σ hσa hσb).1.continuous.norm).rpow_const
        (fun _ => Or.inr ENNReal.toReal_nonneg)).aestronglyMeasurable
    filter_upwards with x
    simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_of_nonneg (sq_nonneg _)]
    rw [sq]
    exact mul_le_mul_of_nonneg_right (hK σ x) (norm_nonneg _)
  · intro s hs
    have hi := hgInt s.re hs.1 hs.2
    refine ⟨mellinConvergent_of_integrable_logWeight p s (by rwa [hweight s.re hs.1 hs.2]), ?_⟩
    rw [mellin_eq_fourier]
    have hEq : (fun u : ℝ ↦ Real.exp (-s.re * u) • p (Real.log (Real.exp (-u)))) =
        𝓕⁻ (trace s.re) := by
      funext u
      rw [Real.log_exp, Complex.real_smul, neg_mul, ← mul_neg, Real.fourierInv_eq_fourier_neg]
      exact congrFun (hweight s.re hs.1 hs.2) (-u)
    have hct : Continuous (trace s.re) := (hcont s.re hs.1 hs.2).comp (by fun_prop)
    have hit : Integrable (trace s.re) := by simpa using hmoment s.re hs.1 hs.2 0 (Nat.zero_le m)
    rw [hEq, hct.fourier_fourierInv_eq hit hi]
    change F (verticalPoint s.re (2 * Real.pi * (s.im / (2 * Real.pi)))) = F s
    rw [← mul_div_assoc, mul_div_cancel_left₀ _ (show 2 * Real.pi ≠ 0 by positivity)]
    exact congrArg F (Complex.re_add_im s)

end
end Masullo
