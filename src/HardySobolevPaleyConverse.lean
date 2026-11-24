import HardySobolevPaleyWiener
import MellinPolynomialInversion

open Complex Filter Function MeasureTheory Set Topology
open scoped ContDiff FourierTransform ENNReal SchwartzMap

namespace Masullo

noncomputable section

local notation "vpoint" => (fun (r y : ℝ) => (r : ℂ) + (y : ℂ) * Complex.I)

private theorem vpoint_eq (r y : ℝ) : vpoint r y = (⟨r, y⟩ : ℂ) := by
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]

private theorem inverseMellin_vanishes_positive {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ r ≥ 0, ∀ y : ℝ, ‖F (vpoint r y)‖ ≤ C * (1 + ‖y‖) ^ (-(2 : ℝ)))
    {x : ℝ} (hx : 0 < x) : mellinInv 0 F (Real.exp x) = 0 := by
  let q (y : ℝ) := C * (1 + ‖y‖) ^ (-(2 : ℝ))
  have hq : Integrable q := by
    exact (integrable_one_add_norm (μ := (volume : Measure ℝ))
      (r := 2) (by simp)).const_mul C
  have hI (r : ℝ) (hr : 0 ≤ r) : Complex.VerticalIntegrable F r :=
    hq.mono' (hF.continuous.comp (by fun_prop)).aestronglyMeasurable (.of_forall (hbound r hr))
  have heq (r : ℝ) (hr : 0 ≤ r) : mellinInv 0 F (Real.exp x) = mellinInv r F (Real.exp x) :=
    mellinInv_eq_of_verticalTrace_decay hr hF.differentiableOn (hI 0 le_rfl) (hI r hr)
      hC (by norm_num : (1 : ℝ) ≤ 2) (fun σ hσ y => hbound σ hσ.1 y) (Real.exp_pos x)
  have hlim : Tendsto (fun r : ℝ => mellinInv r F (Real.exp x)) atTop (𝓝 0) := by
    have hB : ∀ᶠ r : ℝ in atTop, ‖mellinInv r F (Real.exp x)‖ ≤
        (1 / (2 * Real.pi)) * (Real.exp (-r * x) * ∫ y, q y) := by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with r hr
      have hnorm (y : ℝ) : ‖((Real.exp x : ℝ) : ℂ) ^ (-(vpoint r y))‖ =
          Real.exp (-r * x) := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos (Real.exp_pos _),
          Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp, vpoint_eq, Complex.neg_re]
        change Real.exp (x * -r) = _
        rw [mul_comm]
      unfold mellinInv
      rw [norm_smul, Real.norm_of_nonneg (by positivity : 0 ≤ 1 / (2 * Real.pi))]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      calc
        _ ≤ ∫ y : ℝ, ‖((Real.exp x : ℝ) : ℂ) ^ (-(vpoint r y)) • F (vpoint r y)‖ :=
          norm_integral_le_integral_norm _
        _ ≤ ∫ y, Real.exp (-r * x) * q y := by
          apply integral_mono_of_nonneg (.of_forall fun _ => norm_nonneg _)
            (hq.const_mul _)
          exact .of_forall fun y => by
            change ‖((Real.exp x : ℝ) : ℂ) ^ (-(vpoint r y)) • F (vpoint r y)‖ ≤
              Real.exp (-r * x) * q y
            rw [norm_smul, hnorm]
            exact mul_le_mul_of_nonneg_left (hbound r hr y) (Real.exp_pos _).le
        _ = Real.exp (-r * x) * ∫ y, q y := integral_const_mul _ _
    have hlin : Tendsto (fun r : ℝ => r * x) atTop atTop :=
      (tendsto_id : Tendsto (fun r : ℝ => r) atTop atTop).atTop_mul_const hx
    have hExp : Tendsto (fun r : ℝ => Real.exp (-r * x)) atTop (𝓝 0) := by
      have h := Real.tendsto_exp_neg_atTop_nhds_zero.comp hlin
      change Tendsto (fun r : ℝ => Real.exp (-(r * x))) atTop (𝓝 0) at h
      simpa only [neg_mul] using h
    exact squeeze_zero_norm' hB (by
      simpa only [zero_mul, mul_zero] using (hExp.mul_const (∫ y, q y)).const_mul (1 / (2 * Real.pi)))
  exact tendsto_nhds_unique
    (tendsto_const_nhds.congr' ((eventually_ge_atTop (0 : ℝ)).mono fun r hr => heq r hr)) hlim


private theorem inverseMellin_zeroLine_pairing
    {f : ℝ → ℂ} (hf : Integrable f) (g : 𝓢(ℝ, ℂ)) (δ : ℝ)
    (F : ℂ → ℂ) (hF : ∀ y : ℝ, F (vpoint 0 y) = ∫ t : ℝ,
      Complex.exp ((y : ℂ) * Complex.I * (t : ℂ)) * f t)
    (G : ℂ → ℂ) (hG : ∀ y : ℝ, G (vpoint 0 (2 * Real.pi * y)) = (𝓕 g) y) :
    mellinInv 0 (F * G) (Real.exp δ) = ∫ t : ℝ, g (t - δ) * f t := by
  let H := 𝓕 g
  let P (y t : ℝ) := Complex.exp (((2 * Real.pi * y * (t - δ) : ℝ) : ℂ) * Complex.I) *
    (H y * f t)
  have hPc : Continuous (fun p : ℝ × ℝ =>
      Complex.exp (((2 * Real.pi * p.1 * (p.2 - δ) : ℝ) : ℂ) * Complex.I)) := by fun_prop
  have hP : Integrable (uncurry P) ((volume : Measure ℝ).prod volume) := by
    have hm := (H.integrable (μ := (volume : Measure ℝ))).mul_prod hf
    apply hm.norm.mono' (hPc.aestronglyMeasurable.mul hm.aestronglyMeasurable)
    exact .of_forall fun p => by
      change ‖P p.1 p.2‖ ≤ ‖H p.1 * f p.2‖
      simp [P, Complex.norm_exp, Complex.mul_re]
  rw [mellinInv_exp_eq_fourier]
  simp only [neg_zero, zero_mul, Real.exp_zero, Complex.ofReal_one, one_mul]
  rw [Real.fourier_eq']
  calc
    _ = ∫ y, ∫ t, P y t := by
      apply integral_congr_ae
      refine .of_forall fun y => ?_
      have hphase (t : ℝ) : (↑(-2 * Real.pi * (y * δ)) : ℂ) * Complex.I +
          ((↑(2 * Real.pi * y) : ℂ) * Complex.I * (t : ℂ)) =
          (↑(2 * Real.pi * y * (t - δ)) : ℂ) * Complex.I := by push_cast; ring
      simp only [Pi.mul_apply, hF, hG, Real.inner_apply, smul_eq_mul]
      rw [← integral_mul_const, ← integral_const_mul]
      apply integral_congr_ae
      refine .of_forall fun t => ?_
      dsimp [P, H]
      rw [← hphase, Complex.exp_add]
      ring
    _ = ∫ t, ∫ y, P y t := integral_integral_swap hP
    _ = _ := by
      apply integral_congr_ae
      refine .of_forall fun t => ?_
      have hInv : 𝓕⁻ (H : ℝ → ℂ) (t - δ) = g (t - δ) := by
        rw [show (H : ℝ → ℂ) = 𝓕 (g : ℝ → ℂ) from SchwartzMap.fourier_coe g]
        exact g.integrable.fourierInv_fourier_eq
          (by rw [← SchwartzMap.fourier_coe]; exact H.integrable) g.continuous.continuousAt
      change (∫ y, P y t) = g (t - δ) * f t
      rw [← hInv, Real.fourierInv_eq', ← integral_mul_const]
      apply integral_congr_ae
      refine .of_forall fun y => ?_
      simp only [P, Real.inner_apply, smul_eq_mul]
      rw [← mul_assoc]
      congr 3
      ring_nf


private theorem reflectedMellinTest {ψ : ℝ → ℂ} (hc : HasCompactSupport ψ)
    (hs : ContDiff ℝ ∞ ψ) (hpos : ∀ x < 0, ψ x = 0) :
    ∃ G : ℂ → ℂ, Differentiable ℂ G ∧
      (∀ y : ℝ, G (vpoint 0 (2 * Real.pi * y)) = 𝓕 ψ y) ∧
      ∃ D ≥ 0, ∀ r ≥ 0, ∀ y : ℝ, ‖G (vpoint r y)‖ ≤ D * (1 + ‖y‖) ^ (-(2 : ℝ)) := by
  let f (t : ℝ) := ψ (Real.log t)
  let h : logExponentialDecaySubmodule (univ : Set ℝ) :=
    ⟨ψ, mem_logExponentialDecaySubmodule_of_hasCompactSupport univ hc hs⟩
  have hw (r : ℝ) : MellinSchwartzAt f r := by
    apply mellinSchwartzAt_iff_positive_log.mpr
    refine ⟨logExponentialDecayTwist univ ⟨r, mem_univ r⟩ h, ?_⟩
    funext x
    rw [logExponentialDecayTwist_apply, Complex.real_smul]
    simp only [f, Real.log_exp]
    rfl
  have hbelow : ∀ t ∈ Ioo (0 : ℝ) 1, f t = 0 :=
    fun t ht => hpos (Real.log t) (Real.log_neg ht.1 ht.2)
  let G (z : ℂ) := mellin f (-z)
  refine ⟨G, (mellin_exponential_decay hw).2.1.comp differentiable_neg, ?_, ?_⟩
  · intro y
    dsimp [G]
    rw [mellin_eq_log_integral, Real.fourier_eq']
    apply integral_congr_ae
    refine .of_forall fun x => ?_
    have hp : -(vpoint 0 (2 * Real.pi * y)) * (x : ℂ) =
        (↑(-2 * Real.pi * (x * y)) : ℂ) * Complex.I := by
      simp only [ofReal_zero, zero_add]
      push_cast
      ring
    change Complex.exp (-(vpoint 0 (2 * Real.pi * y)) * (x : ℂ)) * f (Real.exp x) =
      Complex.exp _ • ψ x
    rw [hp]
    simp only [f, Real.log_exp, Real.inner_apply, smul_eq_mul]
  · obtain ⟨C₀, hc₀, h₀⟩ := mellin_supported_left_halfplane_power (hw 0) hbelow 0
    obtain ⟨C₂, hc₂, h₂⟩ := mellin_supported_left_halfplane_power (hw 0) hbelow 2
    refine ⟨2 * (C₀ + C₂), by positivity, fun r hr y => ?_⟩
    have hneg : (-(vpoint r y)).re ≤ 0 := by rw [vpoint_eq, neg_re]; exact neg_nonpos.mpr hr
    have hs₀ : ‖G (vpoint r y)‖ ≤ C₀ := by simpa only [G, pow_zero, one_mul] using h₀ _ hneg
    have hs₂ : ‖y‖ ^ 2 * ‖G (vpoint r y)‖ ≤ C₂ := by
      simpa only [vpoint_eq, Complex.neg_im, abs_neg, Real.norm_eq_abs, G] using h₂ _ hneg
    rw [Real.rpow_neg (by positivity), show (1 + ‖y‖) ^ (2 : ℝ) = (1 + ‖y‖) ^ (2 : ℕ)
      from Real.rpow_natCast _ 2, ← div_eq_mul_inv]
    apply (le_div_iff₀ (by positivity)).mpr
    calc
      _ ≤ ‖G (vpoint r y)‖ * (2 * (1 + ‖y‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg (‖y‖ - 1)]) (norm_nonneg _)
      _ = 2 * (‖G (vpoint r y)‖ + ‖y‖ ^ 2 * ‖G (vpoint r y)‖) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add hs₀ hs₂) (by norm_num)


/-- A uniformly bounded holomorphic continuation of the logarithmic Fourier
trace into the right half-plane forces its profile to vanish on the positive ray. -/
theorem paleyWiener_rightBound_vanish_positive
    {f : ℝ → ℂ} (hf : Integrable f) (F : ℂ → ℂ) (hF : Differentiable ℂ F)
    (hline : ∀ y : ℝ, F (vpoint 0 y) = ∫ t : ℝ,
      Complex.exp ((y : ℂ) * Complex.I * (t : ℂ)) * f t)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ z : ℂ, 0 ≤ z.re → ‖F z‖ ≤ C) :
    ∀ᵐ x ∂(volume : Measure ℝ), 0 < x → f x = 0 := by
  apply (isOpen_Ioi (a := (0 : ℝ))).ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (hf.locallyIntegrable.locallyIntegrableOn _)
  intro φ hφ hφc hU
  by_cases hn : (tsupport φ).Nonempty
  · obtain ⟨δ, hδ, hmin⟩ := hφc.exists_isMinOn hn continuousOn_id
    have hδpos : 0 < δ := hU hδ
    let e := Homeomorph.addRight δ
    let ψ (x : ℝ) : ℂ := φ (x + δ)
    have hψc : HasCompactSupport ψ :=
      (hφc.comp_left Complex.ofReal_zero).comp_homeomorph e
    have hψs : ContDiff ℝ ∞ ψ :=
      Complex.ofRealCLM.contDiff.comp (hφ.comp (contDiff_id.add contDiff_const))
    have hψ0 (x : ℝ) (hx : x < 0) : ψ x = 0 := by
      have hnot : x + δ ∉ tsupport φ := fun h => (not_le_of_gt (by linarith : x + δ < δ)) (hmin h)
      change (φ (x + δ) : ℂ) = 0
      rw [image_eq_zero_of_notMem_tsupport hnot, Complex.ofReal_zero]
    obtain ⟨G, hG, hlineG, D, hD, hGb⟩ := reflectedMellinTest hψc hψs hψ0
    have hz : mellinInv 0 (F * G) (Real.exp δ) = 0 := by
      apply inverseMellin_vanishes_positive (hF.mul hG) (mul_nonneg hC hD) _ hδpos
      intro r hr y
      simp only [Pi.mul_apply, norm_mul]
      have hFr := hbound (vpoint r y) (by rwa [vpoint_eq])
      calc
        _ ≤ C * (D * (1 + ‖y‖) ^ (-(2 : ℝ))) :=
          mul_le_mul hFr (hGb r hr y) (norm_nonneg _) hC
        _ = _ := (mul_assoc _ _ _).symm
    let g := hψc.toSchwartzMap hψs
    have hp := inverseMellin_zeroLine_pairing hf g δ F hline G hlineG
    rw [hz] at hp
    calc
      _ = ∫ t : ℝ, g (t - δ) * f t := by
        apply integral_congr_ae
        refine .of_forall fun t => ?_
        change φ t • f t = (φ ((t - δ) + δ) : ℂ) * f t
        rw [sub_add_cancel, Complex.real_smul]
      _ = 0 := hp.symm
  · have hz : ∀ t, φ t = 0 := fun t =>
      image_eq_zero_of_notMem_tsupport (fun h => hn ⟨t, h⟩)
    simp [hz]


/-- An integrable profile is determined almost everywhere by its Fourier trace. -/
theorem integrable_logFourier_ae_zero {f : ℝ → ℂ} (hf : Integrable f)
    (hzero : ∀ y : ℝ, (∫ t : ℝ, Complex.exp ((y : ℂ) * Complex.I * (t : ℂ)) * f t) = 0) :
    f =ᵐ[volume] 0 := by
  have h := (isOpen_univ (X := ℝ)).ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (hf.locallyIntegrable.locallyIntegrableOn (univ : Set ℝ))
  apply Eventually.mono (h ?_)
  · exact fun _ hzero => hzero (mem_univ _)
  · intro φ hφ hφc _
    let g := (hφc.comp_left Complex.ofReal_zero).toSchwartzMap (Complex.ofRealCLM.contDiff.comp hφ)
    let G (z : ℂ) := (𝓕 g) (z.im / (2 * Real.pi))
    have hG (y : ℝ) : G (vpoint 0 (2 * Real.pi * y)) = (𝓕 g) y := by
      rw [vpoint_eq]
      change (𝓕 g) ((2 * Real.pi * y) / (2 * Real.pi)) = (𝓕 g) y
      congr 1
      field_simp [Real.pi_ne_zero]
    have hp := inverseMellin_zeroLine_pairing hf g 0 (fun _ => 0) (fun y => (hzero y).symm) G hG
    have hInv : mellinInv 0 ((fun _ : ℂ => (0 : ℂ)) * G) (Real.exp 0) = 0 := by
      unfold mellinInv
      simp
    rw [hInv] at hp
    calc
      _ = ∫ t : ℝ, g (t - 0) * f t := by
        apply integral_congr_ae
        refine .of_forall fun t => ?_
        change φ t • f t = g (t - 0) * f t
        rw [sub_zero, Complex.real_smul]
        rfl
      _ = 0 := hp.symm

/-- Every available logarithmic Mellin moment has its integral representation
on each lower-cutoff weighted class, including the integrable endpoint orders. -/
theorem cutoffSobolev_mellinMoment_functional_of_le {a b s c : ℝ} (hc : c ≤ 0)
    (hs : 0 ≤ s) {z : ℂ} (hz : z.re ≤ b) (k : ℕ)
    (hEval : z.re < b ∨ 2 * (k : ℝ) + 1 < s) :
    ∃ L : StrongDual ℂ (supportedSobolevCompletion a b s (Ioi c)),
      ∀ u : supportedSobolevCompletion a b s (Ioi c),
        Integrable (fun x => u.val x * mellinEvaluationKernel k z x) ∧
        L u = ∫ x, u.val x * mellinEvaluationKernel k z x := by
  let U := Ioi c
  let E := supportedSobolevCompletion a b s U
  obtain ⟨l, hl⟩ := (hardySobolev_cutoff_mellinEvaluation_exists_iff (a := a)
    hc hz hs k).mpr hEval
  obtain ⟨L, hL, _⟩ := exists_extension_norm_eq E l
  let g := (stripSobolevDuality a b s).symm L
  have hK : Continuous (mellinEvaluationKernel k z) := by unfold mellinEvaluationKernel; fun_prop
  have hg : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ U → g x = mellinEvaluationKernel k z x := by
    apply stripDual_rep_eq_on_support_of_testPairing a b s hK isOpen_Ioi L
    intro f hf
    exact (hL (supportedSobolevTest a b s U f hf)).trans
      ((hl f hf).trans (mellinEvaluation_test_integral f k z))
  refine ⟨l, fun u => ?_⟩
  have hu := (mem_supportedSobolevCompletion_iff a b s isOpen_Ioi u.val).mp u.property
  have he : (fun x => u.val x * g x) =ᵐ[volume] fun x => u.val x * mellinEvaluationKernel k z x := by
    filter_upwards [hu, hg] with x hx hy
    by_cases h : x ∈ U
    · rw [hy h]
    · simp [hx h]
  refine ⟨(stripSobolevDuality_integrable a b s u.val g).congr he, ?_⟩
  rw [← hL u, ← (stripSobolevDuality a b s).apply_symm_apply L, stripSobolevDuality_apply]
  exact integral_congr_ae he

theorem cutoffSobolev_mellinMoment_functional {a b s c : ℝ} (hc : c ≤ 0)
    (hs : 0 ≤ s) {z : ℂ} (hz : z.re < b) (k : ℕ) :
    ∃ L : StrongDual ℂ (supportedSobolevCompletion a b s (Ioi c)),
      ∀ u : supportedSobolevCompletion a b s (Ioi c),
        Integrable (fun x => u.val x * mellinEvaluationKernel k z x) ∧
        L u = ∫ x, u.val x * mellinEvaluationKernel k z x :=
  cutoffSobolev_mellinMoment_functional_of_le hc hs hz.le k (Or.inl hz)

theorem cutoffSobolev_mellinMoment_integrable {a b s c : ℝ} (hc : c ≤ 0)
    (hs : 0 ≤ s) (u : supportedSobolevCompletion a b s (Ioi c))
    {z : ℂ} (hz : z.re < b) (k : ℕ) :
    Integrable (fun x => u.val x * mellinEvaluationKernel k z x) :=
  ((cutoffSobolev_mellinMoment_functional hc hs hz k).choose_spec u).1

/-- Paley–Wiener converse for the lower cutoff. An entire continuation with
the bounded-interval growth estimate, agreeing on one interior vertical line,
forces the class to belong to the bounded-interval term of the exact sequence. -/
theorem cutoffSobolev_mem_bounded_of_mellin_growth {a b s c r₀ : ℝ} (hc : c ≤ 0)
    (hs : 0 ≤ s) (hr : r₀ < b) (u : supportedSobolevCompletion a b s (Ioi c))
    (F : ℂ → ℂ) (hF : Differentiable ℂ F)
    (hline : ∀ y : ℝ, F (vpoint r₀ y) = ∫ x : ℝ, u.val x * Complex.exp (vpoint r₀ y * (x : ℂ)))
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ z : ℂ, ‖F z‖ ≤ C * Real.sqrt (∫ x in Icc c 0, Real.exp (2 * z.re * x))) :
    u.val ∈ supportedSobolevCompletion a b s (Ioo c 0) := by
  let f (x : ℝ) := u.val x * Complex.exp ((r₀ : ℂ) * (x : ℂ))
  have hf : Integrable f := by
    simpa only [mellinEvaluationKernel, pow_zero, mul_one, f] using
      cutoffSobolev_mellinMoment_integrable hc hs u (z := (r₀ : ℂ)) hr 0
  let P (z : ℂ) := F (z + r₀)
  have hP : Differentiable ℂ P := hF.comp (differentiable_id.add_const _)
  have hpLine (y : ℝ) : P (vpoint 0 y) = ∫ t : ℝ,
      Complex.exp ((y : ℂ) * Complex.I * (t : ℂ)) * f t := by
    have he : vpoint 0 y + (r₀ : ℂ) = vpoint r₀ y := by
      simp [add_comm]
    dsimp only [P]
    rw [he, hline]
    apply integral_congr_ae
    refine .of_forall fun t => ?_
    simp only [f, add_mul, Complex.exp_add]
    ring
  let D := C * Real.sqrt (∫ x in Icc c 0, Real.exp (2 * r₀ * x))
  have hD : 0 ≤ D := mul_nonneg hC (Real.sqrt_nonneg _)
  have hbnd (z : ℂ) (hz : 0 ≤ z.re) : ‖P z‖ ≤ D := by
    apply (hbound (z + r₀)).trans
    apply mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) hC
    refine integral_mono_ae ?_ ?_ ?_
    · exact (by fun_prop : Continuous (fun x : ℝ => Real.exp (2 * (z + (r₀ : ℂ)).re * x))).continuousOn.integrableOn_Icc
    · exact (by fun_prop : Continuous (fun x : ℝ => Real.exp (2 * r₀ * x))).continuousOn.integrableOn_Icc
    · filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Icc] with x hx
      apply Real.exp_le_exp.mpr
      apply mul_le_mul_of_nonpos_right _ hx.2
      simp only [Complex.add_re, Complex.ofReal_re]
      linarith
  have hzero := paleyWiener_rightBound_vanish_positive hf P hP hpLine hD hbnd
  have hu := (mem_supportedSobolevCompletion_iff a b s isOpen_Ioi u.val).mp u.property
  apply (mem_supportedSobolevCompletion_iff a b s isOpen_Ioo u.val).mpr
  have hne : ∀ᵐ x : ℝ ∂(volume : Measure ℝ), x ≠ 0 := by simp [ae_iff, measure_singleton]
  filter_upwards [hzero, hu, hne] with x hx hl hne hxI
  by_cases hxc : c < x
  · have hx0 : 0 < x := lt_of_le_of_ne (le_of_not_gt fun h => hxI ⟨hxc, h⟩) hne.symm
    have hf0 : u.val x * Complex.exp ((r₀ : ℂ) * (x : ℂ)) = 0 := hx hx0
    exact (mul_eq_zero.mp hf0).resolve_right (Complex.exp_ne_zero _)
  · exact hl hxc

end
end Masullo
