import HardySobolevSurjectivity

open Filter Function MeasureTheory Set Topology
open scoped ENNReal

namespace Masullo

noncomputable section

/-- Entire extensions of the right Hardy–Sobolev functions with the
bounded logarithmic interval growth estimate. -/
def RightPaleyWiener (b c : ℝ) (N : ℕ) (F : ℂ → ℂ) : Prop :=
  Differentiable ℂ F ∧ UniformMellinLineBound (Ioi b) N F ∧
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ,
      ‖F z‖ ≤ C * Real.sqrt (∫ x in Icc c 0, Real.exp (2 * z.re * x))

private theorem uniformMellinLineBound_reflect {b : ℝ} {N : ℕ} {F : ℂ → ℂ}
    (h : UniformMellinLineBound (Ioi b) N F) :
    UniformMellinLineBound (Iio (-b)) N (fun z => F (-z)) := by
  intro k hk
  obtain ⟨C, hC⟩ := h k hk
  refine ⟨C, fun r hr => ?_⟩
  let T (y : ℝ) := iteratedDeriv k F (⟨-r, y⟩ : ℂ)
  have hbr : b < -r := by
    have : r < -b := hr
    linarith
  obtain ⟨hm, hnorm⟩ := hC (-r) hbr
  have hp (y : ℝ) : iteratedDeriv k (fun z => F (-z)) (⟨r, y⟩ : ℂ) =
      (-1 : ℂ) ^ k • T (-y) := by rw [iteratedDeriv_comp_neg]; rfl
  change MemLp (fun y => iteratedDeriv k (fun z => F (-z)) (⟨r, y⟩ : ℂ)) 2 volume ∧ _
  refine ⟨?_, ?_⟩
  · simp_rw [hp]
    exact (hm.comp_measurePreserving (Measure.measurePreserving_neg (volume : Measure ℝ))).const_smul
      ((-1 : ℂ) ^ k)
  · change (∫ y : ℝ, ‖iteratedDeriv k (fun z => F (-z)) (⟨r, y⟩ : ℂ)‖ ^ 2) ≤ C
    simp_rw [hp, norm_smul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    rw [integral_neg_eq_self (fun y : ℝ => ‖T y‖ ^ 2) volume]
    exact hnorm

private theorem rightPaleyWiener_reflected_support {b c s : ℝ} (hs : 0 ≤ s)
    (u : supportedSobolevCompletion (-b) (-b) s (Ioi 0)) {F : ℂ → ℂ}
    (hF : Differentiable ℂ F)
    (hU : ∀ z : ℂ, z.re < -b → F (-z) = cutoffMellinIntegral u.val 0 z)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ z : ℂ, ‖F z‖ ≤ C * Real.sqrt (∫ x in Icc c 0, Real.exp (2 * z.re * x))) :
    u.val ∈ supportedSobolevCompletion (-b) (-b) s (Ioo 0 (-c)) := by
  let L := -c
  let r := -b - 1
  have hr : r < -b := by dsimp [r]; linarith
  let p (x : ℝ) := u.val x * Complex.exp ((r : ℂ) * (x : ℂ))
  have hp : Integrable p := by
    simpa only [p, mellinEvaluationKernel, pow_zero, mul_one] using
      cutoffSobolev_mellinMoment_integrable le_rfl hs u (z := (r : ℂ)) hr 0
  let f (x : ℝ) := p (x + L)
  let G (z : ℂ) := Complex.exp (-(L : ℂ) * z) * F (-(z + (r : ℂ)))
  have hf : Integrable f :=
    (measurePreserving_add_right (volume : Measure ℝ) L).integrable_comp_of_integrable hp
  have h1 : Differentiable ℂ (fun z : ℂ => Complex.exp (-(L : ℂ) * z)) := by fun_prop
  have h2 : Differentiable ℂ (fun z : ℂ => -(z + (r : ℂ))) := by fun_prop
  have hG : Differentiable ℂ G := h1.mul (hF.comp h2)
  have hline (y : ℝ) : G (0 + (y : ℂ) * Complex.I) =
      ∫ x : ℝ, Complex.exp ((y : ℂ) * Complex.I * (x : ℂ)) * f x := by
    let iy := (y : ℂ) * Complex.I
    have hzr : (iy + (r : ℂ)).re < -b := by simp [iy, Complex.mul_re, hr]
    simp only [zero_add]
    change Complex.exp (-(L : ℂ) * iy) * F (-(iy + (r : ℂ))) = _
    rw [hU _ hzr]
    unfold cutoffMellinIntegral
    simp only [mellinEvaluationKernel, pow_zero, mul_one]
    rw [← integral_const_mul]
    rw [← integral_add_right_eq_self
      (fun x : ℝ => Complex.exp (-(L : ℂ) * iy) *
        (u.val x * Complex.exp ((iy + (r : ℂ)) * (x : ℂ)))) L]
    apply integral_congr_ae
    refine .of_forall fun x => ?_
    have he : -(L : ℂ) * iy + (iy + (r : ℂ)) * ((x + L : ℝ) : ℂ) =
        iy * (x : ℂ) + (r : ℂ) * ((x + L : ℝ) : ℂ) := by push_cast; ring
    change Complex.exp (-(L : ℂ) * iy) * (u.val (x + L) *
      Complex.exp ((iy + (r : ℂ)) * ((x + L : ℝ) : ℂ))) =
      Complex.exp (iy * (x : ℂ)) * (u.val (x + L) * Complex.exp ((r : ℂ) * ((x + L : ℝ) : ℂ)))
    rw [mul_comm (u.val (x + L)), ← mul_assoc, ← Complex.exp_add, he, Complex.exp_add]
    ring
  let D := C * Real.sqrt (∫ x in Icc c 0, Real.exp (2 * (-r) * x))
  have hD : 0 ≤ D := mul_nonneg hC (Real.sqrt_nonneg _)
  have hGrowth (z : ℂ) (hz : 0 ≤ z.re) : ‖G z‖ ≤ D := by
    have hnorm : ‖Complex.exp (-(L : ℂ) * z)‖ = Real.exp (-L * z.re) := by
      simp [Complex.norm_exp, Complex.mul_re]
    dsimp only [G]
    rw [norm_mul, hnorm]
    refine (mul_le_mul_of_nonneg_left (hbound (-(z + (r : ℂ)))) (Real.exp_pos _).le).trans ?_
    rw [← mul_left_comm, ← Real.sqrt_sq (Real.exp_pos (-L * z.re)).le, ← Real.sqrt_mul (sq_nonneg _),
      ← Real.exp_nat_mul, ← integral_const_mul]
    apply mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) hC
    refine integral_mono_ae ?_ ?_ ?_
    · exact (by fun_prop : Continuous fun x : ℝ =>
        Real.exp (↑(2 : ℕ) * (-L * z.re)) * Real.exp (2 * (-(z + (r : ℂ))).re * x)).continuousOn.integrableOn_Icc
    · exact (by fun_prop : Continuous fun x : ℝ => Real.exp (2 * (-r) * x)).continuousOn.integrableOn_Icc
    · filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Icc] with x hx
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hsum : 0 ≤ L + x := by dsimp [L]; linarith [hx.1]
      simp only [Nat.cast_ofNat, Complex.neg_re, Complex.add_re, Complex.ofReal_re]
      nlinarith [mul_nonneg hz hsum]
  have hzero := paleyWiener_rightBound_vanish_positive hf G hG hline hD hGrowth
  have hZeroL : ∀ᵐ x : ℝ ∂volume, L < x → u.val x = 0 := by
    have hshift := (measurePreserving_add_right (volume : Measure ℝ) (-L)).quasiMeasurePreserving.ae
      (p := fun x : ℝ => 0 < x → f x = 0) hzero
    filter_upwards [hshift] with x hx h
    have he := hx (by linarith)
    change p (x + -L + L) = 0 at he
    rw [neg_add_cancel_right] at he
    exact (mul_eq_zero.mp he).resolve_right (Complex.exp_ne_zero _)
  have hu := (mem_supportedSobolevCompletion_iff (-b) (-b) s isOpen_Ioi u.val).mp u.property
  have hne : ∀ᵐ x : ℝ ∂volume, x ≠ L := by rw [ae_iff]; simp
  apply (mem_supportedSobolevCompletion_iff (-b) (-b) s isOpen_Ioo u.val).mpr
  filter_upwards [hZeroL, hu, hne] with x hz hf hn hout
  by_cases hx : 0 < x
  · exact hz (lt_of_le_of_ne (le_of_not_gt (fun h : x < L => hout ⟨hx, h⟩)) hn.symm)
  · exact hf hx

/-- The entire right Paley–Wiener functions are precisely the Mellin
transforms of profiles supported in the bounded logarithmic interval. -/
theorem rightPaleyWiener_iff_exists_compactCutoff {b c : ℝ} {N : ℕ} (F : ℂ → ℂ) :
    RightPaleyWiener b c N F ↔
      ∃ w : supportedSobolevCompletion b b (2 * (N : ℝ)) (Ioo c 0),
        F = cutoffMellinIntegral w.val 0 := by
  have hkernel (f : ℝ → ℂ) :
      cutoffMellinIntegral f 0 = fun z : ℂ => ∫ x, compactMellinKernel f z x := by
    funext z
    simp only [cutoffMellinIntegral, compactMellinKernel, mellinEvaluationKernel, pow_zero, mul_one]
  constructor
  · rintro ⟨hF, hB, C, hC, hGrowth⟩
    obtain ⟨u, hu⟩ := exists_cutoffMellinIntegral_of_leftHardySobolev
      (hF.comp differentiable_neg).differentiableOn (uniformMellinLineBound_reflect hB)
    let s := 2 * (N : ℝ)
    have hSupport := rightPaleyWiener_reflected_support (by positivity : 0 ≤ s) u hF hu hC hGrowth
    have hrefl : MeasurePreserving (fun x : ℝ => -x) (stripMeasure b b s) (stripMeasure (-b) (-b) s) := by
      simpa only [neg_neg] using stripMeasure_neg_preserving (-b) s
    let w := Lp.compMeasurePreserving (fun x : ℝ => -x) hrefl u.val
    have hEq : (w : ℝ → ℂ) =ᵐ[volume] fun x => u.val (-x) :=
      (absolutelyContinuous_amplitudeMeasure volume _ (stripSobolevAmplitude_continuous b b s).measurable
        (stripSobolevAmplitude_pos b b s)).ae_le (Lp.coeFn_compMeasurePreserving u.val hrefl)
    have hPos := (mem_supportedSobolevCompletion_iff (-b) (-b) s isOpen_Ioo u.val).mp hSupport
    have hPosNeg := (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae
      (p := fun x : ℝ => x ∉ Ioo 0 (-c) → u.val x = 0) hPos
    have hw : w ∈ supportedSobolevCompletion b b s (Ioo c 0) := by
      apply (mem_supportedSobolevCompletion_iff b b s isOpen_Ioo w).mpr
      filter_upwards [hEq, hPosNeg] with x hx hy hnx
      rw [hx]
      exact hy (fun h => hnx ⟨neg_lt_neg_iff.mp h.2, neg_pos.mp h.1⟩)
    let W : supportedSobolevCompletion b b s (Ioo c 0) := ⟨w, hw⟩
    refine ⟨W, ?_⟩
    have hh : Differentiable ℂ (cutoffMellinIntegral W.val 0) := by
      rw [hkernel]
      exact (boundedStripSobolev_mellin_entire_bound b b s c W).2.1
    have hEqRight (z : ℂ) (hz : b < z.re) : F z = cutoffMellinIntegral W.val 0 z := by
      have he := congrFun (reflectedMellinIntegral_eq (f := u.val) (g := W.val) hEq) (-z)
      have hb : (-z).re < -b := by simpa only [Complex.neg_re] using neg_lt_neg hz
      simpa only [Function.comp_apply, neg_neg] using (hu (-z) hb).trans he
    have hz : b < ((b + 1 : ℝ) : ℂ).re := by simp
    exact (hF.differentiableOn.analyticOnNhd isOpen_univ).eq_of_eventuallyEq
      (hh.differentiableOn.analyticOnNhd isOpen_univ)
      ((show ∀ᶠ z in 𝓝 (((b + 1 : ℝ) : ℂ)), b < z.re from
        (isOpen_Ioi.preimage Complex.continuous_re).mem_nhds hz).mono hEqRight)
  · rintro ⟨w, rfl⟩
    obtain ⟨_, hF, hG⟩ := boundedStripSobolev_mellin_entire_bound b b _ c w
    refine ⟨(hkernel w.val).symm ▸ hF, ?_, ?_⟩
    · intro k hk
      exact ⟨2 * Real.pi * ‖w‖ ^ 2, fun r hr => compactCutoffMellinIntegral_right_bound hk w hr⟩
    · refine ⟨Real.sqrt (∫ x in Icc c 0, ‖w.val x‖ ^ 2), Real.sqrt_nonneg _, fun z => ?_⟩
      rw [hkernel]
      exact hG z

end
end Masullo
