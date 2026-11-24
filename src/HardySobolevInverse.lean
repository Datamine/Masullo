import HardySobolevContour
import HardySobolevBoundary
import RealFourierPlancherel
import MellinStrip

open Filter Function MeasureTheory Set Topology
open scoped ContDiff ENNReal FourierTransform SchwartzMap InnerProductSpace ComplexConjugate

namespace Masullo

noncomputable section

local notation "planePoint" => (fun (r y : ℝ) => (r : ℂ) + (y : ℂ) * Complex.I)
local notation "scale" => (-(2 * Real.pi))
local notation "H" => (Lp ℂ 2 (volume : Measure ℝ))

private theorem scaledVerticalTrace_memLp {F : ℂ → ℂ} {r : ℝ}
    (hFc : Continuous (fun y : ℝ => F (planePoint r y)))
    (hF : MemLp (fun y : ℝ => F (planePoint r y)) 2 volume) :
    MemLp (fun y : ℝ => F (planePoint r (scale * y))) 2 volume := by
  have hFs : Continuous (fun y : ℝ => F (planePoint r (scale * y))) :=
    hFc.comp (continuous_const.mul continuous_id)
  apply (memLp_two_iff_integrable_sq_norm hFs.aestronglyMeasurable).mpr
  have hi := (memLp_two_iff_integrable_sq_norm hF.aestronglyMeasurable).mp hF
  exact (integrable_comp_mul_left_iff (fun y => ‖F (planePoint r y)‖ ^ 2)
    (R := scale) (neg_ne_zero.mpr (mul_ne_zero two_ne_zero Real.pi_ne_zero))).mpr hi

/-- The inverse L² Fourier profile of one vertical line, with the Mellin sign
and the change of height coordinate from Fourier frequency. -/
def inverseVerticalTraceL2 (F : ℂ → ℂ) (r : ℝ)
    (hFc : Continuous (fun y : ℝ => F (planePoint r y)))
    (hF : MemLp (fun y : ℝ => F (planePoint r y)) 2 volume) : H :=
  realFourierL2.symm ((scaledVerticalTrace_memLp hFc hF).toLp _)

private theorem fourier_test_conj_eq_reflectedMellin {φ : ℝ → ℝ} (r y : ℝ) :
    conj (𝓕 (fun x : ℝ => (φ x : ℂ) * Complex.exp (((-r : ℝ) : ℂ) * (x : ℂ))) y) =
      mellin (fun t => (φ (Real.log t) : ℂ)) (-planePoint r (scale * y)) := by
  rw [Real.fourier_eq', ← integral_conj, mellin_eq_log_integral]
  apply integral_congr_ae
  refine .of_forall fun x => ?_
  simp only [smul_eq_mul, map_mul, ← Complex.exp_conj, Complex.conj_ofReal,
    Complex.conj_I, Real.log_exp, Real.inner_apply]
  have he : (↑(-2 * Real.pi * (x * y)) : ℂ) * (-Complex.I) +
      (↑(-r) : ℂ) * (x : ℂ) = -(planePoint r (scale * y)) * (x : ℂ) := by
    push_cast
    ring
  rw [mul_comm (φ x : ℂ), ← mul_assoc, ← Complex.exp_add, he]

/-- Pair the inverse vertical profile against a compact smooth logarithmic
test function. The exponential in the pairing removes the line's weight. -/
theorem inverseVerticalTraceL2_pairing {F : ℂ → ℂ} {r : ℝ}
    (hFc : Continuous (fun y : ℝ => F (planePoint r y)))
    (hF : MemLp (fun y : ℝ => F (planePoint r y)) 2 volume)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
    let G (z : ℂ) := mellin (fun t => (φ (Real.log t) : ℂ)) (-z)
    (∫ y : ℝ, F (planePoint r y) * G (planePoint r y)) =
      (2 * Real.pi : ℝ) • ∫ x : ℝ,
        (φ x : ℂ) * Complex.exp (((-r : ℝ) : ℂ) * (x : ℂ)) * inverseVerticalTraceL2 F r hFc hF x := by
  intro G
  let q (x : ℝ) : ℂ := (φ x : ℂ) * Complex.exp (((-r : ℝ) : ℂ) * (x : ℂ))
  have hq : ContDiff ℝ ∞ q := (Complex.ofRealCLM.contDiff.comp hφ).mul
    ((contDiff_const.mul Complex.ofRealCLM.contDiff).cexp)
  have hqc : HasCompactSupport q :=
    (hφc.comp_left Complex.ofReal_zero).mul_right
  let g := hqc.toSchwartzMap hq
  let Q := g.toLp 2 volume
  let P := inverseVerticalTraceL2 F r hFc hF
  let T := (scaledVerticalTrace_memLp hFc hF).toLp _
  have hU : realFourierL2 P = T := realFourierL2.apply_symm_apply T
  have hT : (T : ℝ → ℂ) =ᵐ[volume] fun y => F (planePoint r (scale * y)) :=
    (scaledVerticalTrace_memLp hFc hF).coeFn_toLp
  have hQ : (realFourierL2 Q : ℝ → ℂ) =ᵐ[volume] 𝓕 (g : ℝ → ℂ) := by
    rw [realFourierL2_onSchwartz]
    exact ((𝓕 g).coeFn_toLp 2 volume).trans
      (.of_forall fun y => congrFun (SchwartzMap.fourier_coe g) y)
  have ha (y : ℝ) : conj (𝓕 (g : ℝ → ℂ) y) = G (planePoint r (scale * y)) :=
    fourier_test_conj_eq_reflectedMellin r y
  have hpaired : (∫ y : ℝ, F (planePoint r (scale * y)) * G (planePoint r (scale * y))) =
      inner ℂ (realFourierL2 Q) (realFourierL2 P) := by
    rw [L2.inner_def, hU]
    apply integral_congr_ae
    filter_upwards [hT, hQ] with y hy hgy
    change F (planePoint r (scale * y)) * G (planePoint r (scale * y)) =
      inner ℂ (realFourierL2 Q y) (T y)
    rw [RCLike.inner_apply, hy, hgy, ha]
  have hQg (x : ℝ) : conj (g x) = q x := by
    change conj (q x) = q x
    simp [q, ← Complex.exp_conj]
  let K (y : ℝ) : ℂ := F (planePoint r y) * G (planePoint r y)
  change (∫ y, K y) = (2 * Real.pi : ℝ) • ∫ x, q x * P x
  calc
    _ = (2 * Real.pi : ℝ) • ∫ y, K (scale * y) := by
      rw [Measure.integral_comp_mul_left, smul_smul, abs_inv, abs_neg,
        abs_of_pos (by positivity : 0 < (2 * Real.pi)), mul_inv_cancel₀ (by positivity), one_smul]
    _ = (2 * Real.pi : ℝ) • inner ℂ Q P := by
      rw [hpaired, realFourierL2.inner_map_map]
    _ = _ := by
      rw [L2.inner_def]
      congr 1
      apply integral_congr_ae
      filter_upwards [g.coeFn_toLp 2 volume] with x hx
      change inner ℂ (Q x) (P x) = q x * P x
      rw [RCLike.inner_apply, show Q x = g x from hx, hQg, mul_comm]

private theorem complex_verticalLine_continuous {F : ℂ → ℂ} {c d r : ℝ}
    (hF : ContinuousOn F (Complex.re ⁻¹' Icc c d)) (hr : r ∈ Icc c d) :
    Continuous (fun y : ℝ => F (planePoint r y)) := by
  apply hF.comp_continuous (by fun_prop)
  intro y
  change (planePoint r y).re ∈ Icc c d
  simpa [Complex.mul_re] using hr

/-- The inverse L² profiles on two abscissae of a Hardy strip agree after
removing their exponential weights. -/
theorem inverseVerticalTraceL2_unweight_ae_eq {F : ℂ → ℂ} {c d A : ℝ} (hcd : c ≤ d)
    (hF : DifferentiableOn ℂ F (Complex.re ⁻¹' Icc c d))
    (hFL : ∀ r ∈ Icc c d, MemLp (fun y => F (planePoint r y)) 2 volume ∧
      (∫ y, ‖F (planePoint r y)‖ ^ 2) ≤ A) :
    let rc := complex_verticalLine_continuous hF.continuousOn (show c ∈ Icc c d from ⟨le_rfl, hcd⟩)
    let rd := complex_verticalLine_continuous hF.continuousOn (show d ∈ Icc c d from ⟨hcd, le_rfl⟩)
    let P := inverseVerticalTraceL2 F c rc (hFL c ⟨le_rfl, hcd⟩).1
    let Q := inverseVerticalTraceL2 F d rd (hFL d ⟨hcd, le_rfl⟩).1
    (fun x : ℝ => Complex.exp (((-c : ℝ) : ℂ) * (x : ℂ)) * P x) =ᵐ[volume]
      fun x : ℝ => Complex.exp (((-d : ℝ) : ℂ) * (x : ℂ)) * Q x := by
  intro rc rd P Q
  let e (r x : ℝ) := Complex.exp (((-r : ℝ) : ℂ) * (x : ℂ))
  have hE (r : ℝ) : Continuous (e r) := by dsimp [e]; fun_prop
  have hloc (u : H) (r : ℝ) : LocallyIntegrable (fun x : ℝ => e r x * u x) volume :=
    ((Lp.memLp u).locallyIntegrable (by norm_num)).continuous_smul (hE r)
  apply ae_eq_of_integral_contDiff_smul_eq (hloc P c) (hloc Q d)
  intro φ hφ hφc
  let ψ : ℝ → ℂ := fun x => φ x
  have hψ : ContDiff ℝ ∞ ψ := Complex.ofRealCLM.contDiff.comp hφ
  have hψc : HasCompactSupport ψ := hφc.comp_left Complex.ofReal_zero
  have heq := verticalTrace_pairing_eq_of_uniformL2 hcd hF hFL hψ hψc
  have hP := inverseVerticalTraceL2_pairing rc (hFL c ⟨le_rfl, hcd⟩).1 hφ hφc
  have hQ := inverseVerticalTraceL2_pairing rd (hFL d ⟨hcd, le_rfl⟩).1 hφ hφc
  let G (z : ℂ) := mellin (fun t => ψ (Real.log t)) (-z)
  have hp : (∫ y : ℝ, F (planePoint c y) * G (planePoint c y)) =
      (2 * Real.pi : ℝ) • ∫ x : ℝ, (φ x : ℂ) * e c x * P x := hP
  have hq : (∫ y : ℝ, F (planePoint d y) * G (planePoint d y)) =
      (2 * Real.pi : ℝ) • ∫ x : ℝ, (φ x : ℂ) * e d x * Q x := hQ
  change (∫ y : ℝ, F (planePoint d y) * G (planePoint d y)) =
    ∫ y : ℝ, F (planePoint c y) * G (planePoint c y) at heq
  rw [hp, hq] at heq
  have hC : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hi := (smul_right_injective ℂ hC) heq
  simpa only [Complex.real_smul, mul_assoc] using hi.symm

/-- The inverse vertical profile has the exact normalized Plancherel energy. -/
theorem inverseVerticalTraceL2_norm_sq {F : ℂ → ℂ} {r : ℝ}
    (hFc : Continuous (fun y : ℝ => F (planePoint r y)))
    (hF : MemLp (fun y : ℝ => F (planePoint r y)) 2 volume) :
    ‖inverseVerticalTraceL2 F r hFc hF‖ ^ 2 =
      (2 * Real.pi)⁻¹ * ∫ y : ℝ, ‖F (planePoint r y)‖ ^ 2 := by
  unfold inverseVerticalTraceL2
  rw [realFourierL2.symm.norm_map, norm_sq_toLp_two]
  exact (Measure.integral_comp_mul_left (fun y => ‖F (planePoint r y)‖ ^ 2) scale).trans
    (by rw [abs_inv, abs_neg, abs_of_pos (by positivity : 0 < 2 * Real.pi)]; rfl)

private theorem ae_zero_of_uniform_logRay_energy {f : ℝ → ℂ} (hf : AEStronglyMeasurable f volume)
    {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (h : ∀ n : ℕ, (∫⁻ x : ℝ, ENNReal.ofReal
      (‖Complex.exp (-(n : ℂ) * (x : ℂ)) * f x‖ ^ 2)) ≤ C) :
    ∀ᵐ x : ℝ ∂volume, x < 0 → f x = 0 := by
  let E (n : ℕ) (x : ℝ) := ENNReal.ofReal (‖Complex.exp (-(n : ℂ) * (x : ℂ)) * f x‖ ^ 2)
  have hE (n : ℕ) : AEMeasurable (E n) volume := by
    have hcont : Continuous (fun x : ℝ => Complex.exp (-(n : ℂ) * (x : ℂ))) := by fun_prop
    exact ((hcont.aestronglyMeasurable.mul hf).norm.pow 2).aemeasurable.ennreal_ofReal
  have hm : (∫⁻ x : ℝ, liminf (fun n => E n x) atTop) ≤ C :=
    (lintegral_liminf_le' hE).trans ((liminf_le_liminf (.of_forall h)).trans_eq (liminf_const C))
  have ht : ∀ᵐ x : ℝ ∂volume, liminf (fun n => E n x) atTop < ⊤ :=
    ae_lt_top' (by
      simp_rw [liminf_eq_iSup_iInf_of_nat']
      exact AEMeasurable.iSup fun n => AEMeasurable.iInf fun i => hE (i + n))
      (hm.trans_lt (lt_top_iff_ne_top.mpr hC)).ne
  filter_upwards [ht] with x hx hneg
  by_contra hne
  have hExp : Tendsto (fun n : ℕ => Real.exp (2 * (-x) * n)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_natCast_atTop_atTop.const_mul_atTop (mul_pos two_pos (neg_pos.mpr hneg)))
  have hT : Tendsto (fun n => E n x) atTop (𝓝 (⊤ : ℝ≥0∞)) := by
    have h' := ENNReal.tendsto_ofReal_atTop.comp (hExp.atTop_mul_const (sq_pos_of_pos (norm_pos_iff.mpr hne)))
    refine h'.congr fun n => ?_
    simp only [Function.comp_def, E, norm_mul, mul_pow, Complex.norm_exp, Complex.mul_re,
      Complex.neg_re, Complex.neg_im, Complex.natCast_re, Complex.natCast_im, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero, ← Real.exp_nat_mul]
    push_cast
    congr 3
    ring
  rw [hT.liminf_eq] at hx
  exact (lt_irrefl _ hx)

private theorem hardyVerticalLine_continuous {F : ℂ → ℂ} {b r : ℝ}
    (hF : DifferentiableOn ℂ F (Complex.re ⁻¹' Iio b)) (hr : r < b) :
    Continuous (fun y : ℝ => F (planePoint r y)) :=
  hF.continuousOn.comp_continuous (by fun_prop) (fun y => by
    change (planePoint r y).re < b
    simpa [Complex.mul_re] using hr)

/-- Uniform L² control on the whole left half-plane forces the inverse profile
of each vertical line to vanish on the negative logarithmic ray. -/
theorem inverseVerticalTraceL2_supported_positive {F : ℂ → ℂ} {b r A : ℝ}
    (hF : DifferentiableOn ℂ F (Complex.re ⁻¹' Iio b)) (hr : r < b)
    (hFL : ∀ s < b, MemLp (fun y => F (planePoint s y)) 2 volume ∧
      (∫ y, ‖F (planePoint s y)‖ ^ 2) ≤ A) :
    ∀ᵐ x : ℝ ∂volume, x < 0 →
      inverseVerticalTraceL2 F r (hardyVerticalLine_continuous hF hr) (hFL r hr).1 x = 0 := by
  let P := inverseVerticalTraceL2 F r (hardyVerticalLine_continuous hF hr) (hFL r hr).1
  apply ae_zero_of_uniform_logRay_energy (Lp.aestronglyMeasurable P)
    (C := ENNReal.ofReal ((2 * Real.pi)⁻¹ * A)) ENNReal.ofReal_ne_top
  intro n
  let c := r - n
  have hcr : c ≤ r := sub_le_self _ (by positivity)
  have hcb : c < b := hcr.trans_lt hr
  let Q := inverseVerticalTraceL2 F c (hardyVerticalLine_continuous hF hcb) (hFL c hcb).1
  have hdiff : DifferentiableOn ℂ F (Complex.re ⁻¹' Icc c r) :=
    hF.mono (fun _ hz => hz.2.trans_lt hr)
  have hh : ∀ s ∈ Icc c r, MemLp (fun y => F (planePoint s y)) 2 volume ∧
      (∫ y, ‖F (planePoint s y)‖ ^ 2) ≤ A :=
    fun s hs => hFL s (hs.2.trans_lt hr)
  have huv := inverseVerticalTraceL2_unweight_ae_eq hcr hdiff hh
  have htwist : (Q : ℝ → ℂ) =ᵐ[volume] fun x => Complex.exp (-(n : ℂ) * (x : ℂ)) * P x := by
    filter_upwards [huv] with x hx
    change Complex.exp (((-c : ℝ) : ℂ) * (x : ℂ)) * Q x =
      Complex.exp (((-r : ℝ) : ℂ) * (x : ℂ)) * P x at hx
    have hphase : -(n : ℂ) * (x : ℂ) + (((-c : ℝ) : ℂ) * (x : ℂ)) =
        ((-r : ℝ) : ℂ) * (x : ℂ) := by
      dsimp [c]
      push_cast
      ring
    apply mul_left_cancel₀ (Complex.exp_ne_zero (((-c : ℝ) : ℂ) * (x : ℂ)))
    rw [hx, ← mul_assoc, mul_comm (Complex.exp (((-c : ℝ) : ℂ) * (x : ℂ))),
      ← Complex.exp_add, hphase]
  have hsq : (fun x : ℝ => ENNReal.ofReal (‖Complex.exp (-(n : ℂ) * (x : ℂ)) * P x‖ ^ 2))
      =ᵐ[volume] (fun x : ℝ => ENNReal.ofReal (‖Q x‖ ^ 2)) :=
    htwist.symm.mono fun x hx => congrArg (fun z : ℂ => ENNReal.ofReal (‖z‖ ^ 2)) hx
  rw [lintegral_congr_ae hsq]
  have hInt := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable Q)).mp (Lp.memLp Q)
  rw [← ofReal_integral_eq_lintegral_ofReal hInt (.of_forall fun _ => sq_nonneg _)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hn : ‖Q‖ ^ 2 = ∫ x : ℝ, ‖Q x‖ ^ 2 := by
    simpa only [Lp.toLp_coeFn] using norm_sq_toLp_two (Lp.memLp Q)
  rw [← hn, show ‖Q‖ ^ 2 = (2 * Real.pi)⁻¹ * ∫ y, ‖F (planePoint c y)‖ ^ 2 from
    inverseVerticalTraceL2_norm_sq _ _]
  exact mul_le_mul_of_nonneg_left (hFL c hcb).2 (by positivity)

/-- The inverse of the scalar left half-plane Hardy transform in degree zero.
The reconstructed profile is in the upper-endpoint weighted space and is
supported on the positive logarithmic ray. -/
theorem exists_cutoffMellinIntegral_of_uniform_leftL2 {F : ℂ → ℂ} {b A : ℝ}
    (hF : DifferentiableOn ℂ F (Complex.re ⁻¹' Iio b))
    (hFL : ∀ s < b, MemLp (fun y => F (planePoint s y)) 2 volume ∧
      (∫ y, ‖F (planePoint s y)‖ ^ 2) ≤ A) :
    ∃ u : supportedSobolevCompletion b b 0 (Ioi 0),
      ∀ z : ℂ, z.re < b → F z = cutoffMellinIntegral u.val 0 z := by
  let r : Iio b := ⟨b - 1, by simp⟩
  let P (s : Iio b) := inverseVerticalTraceL2 F s.val
    (hardyVerticalLine_continuous hF s.property) (hFL s.val s.property).1
  let e (s x : ℝ) := Complex.exp ((s : ℂ) * (x : ℂ))
  let v (x : ℝ) := e (-r.val) x * P r x
  have hc (s : ℝ) : Continuous (e s) := by dsimp [e]; fun_prop
  have hv : AEStronglyMeasurable v volume :=
    (hc (-r.val)).aestronglyMeasurable.mul (Lp.aestronglyMeasurable (P r))
  have hlineOrder (s t : Iio b) (hst : s.val ≤ t.val) :
      (fun x : ℝ => e (-s.val) x * P s x) =ᵐ[volume] fun x : ℝ => e (-t.val) x * P t x :=
    inverseVerticalTraceL2_unweight_ae_eq hst (hF.mono fun _ hz => hz.2.trans_lt t.property)
      (fun y hy => hFL y (hy.2.trans_lt t.property))
  have hline (s : Iio b) :
      (P s : ℝ → ℂ) =ᵐ[volume] fun x => e s.val x * v x := by
    have heq : (fun x : ℝ => e (-s.val) x * P s x) =ᵐ[volume] v := by
      rcases le_total s.val r.val with h | h
      · exact hlineOrder s r h
      · exact (hlineOrder r s h).symm
    filter_upwards [heq] with x hx
    change e (-s.val) x * P s x = v x at hx
    rw [← hx, ← mul_assoc]
    have h : e s.val x * e (-s.val) x = 1 := by
      simp [e, ← Complex.exp_add]
    rw [h, one_mul]
  have hvpos : ∀ᵐ x : ℝ ∂volume, x ∉ Ioi (0 : ℝ) → v x = 0 := by
    have hzero : ∀ᵐ x : ℝ ∂volume, x ≠ 0 := by rw [ae_iff]; simp
    filter_upwards [hzero, inverseVerticalTraceL2_supported_positive hF r.property hFL]
      with x hx hf hn
    change ¬ 0 < x at hn
    have hpx : P r x = 0 := hf (lt_of_le_of_ne (le_of_not_gt hn) hx)
    simp [v, hpx]
  let t (n : ℕ) : Iio b := ⟨b - (1 / ((n : ℝ) + 1)), by
    apply mem_Iio.mpr
    exact sub_lt_self _ (by positivity)⟩
  let E (n : ℕ) (x : ℝ) := ENNReal.ofReal (‖e (t n).val x * v x‖ ^ 2)
  let W (x : ℝ) := e b x * v x
  have hW : AEStronglyMeasurable W volume := (hc b).aestronglyMeasurable.mul hv
  have hE (n : ℕ) : AEMeasurable (E n) volume :=
    (((hc (t n).val).aestronglyMeasurable.mul hv).norm.pow 2).aemeasurable.ennreal_ofReal
  have hbound (n : ℕ) : (∫⁻ x, E n x) ≤ ENNReal.ofReal ((2 * Real.pi)⁻¹ * A) := by
    rw [lintegral_congr_ae ((hline (t n)).symm.mono fun _ hx =>
      congrArg (fun z : ℂ => ENNReal.ofReal (‖z‖ ^ 2)) hx)]
    have hInt := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable (P (t n)))).mp
      (Lp.memLp (P (t n)))
    rw [← ofReal_integral_eq_lintegral_ofReal hInt (.of_forall fun _ => sq_nonneg _)]
    apply ENNReal.ofReal_le_ofReal
    have hn : ‖P (t n)‖ ^ 2 = ∫ x : ℝ, ‖P (t n) x‖ ^ 2 := by
      simpa only [Lp.toLp_coeFn] using norm_sq_toLp_two (Lp.memLp (P (t n)))
    rw [← hn, show ‖P (t n)‖ ^ 2 =
      (2 * Real.pi)⁻¹ * ∫ y, ‖F (planePoint (t n).val y)‖ ^ 2 from inverseVerticalTraceL2_norm_sq _ _]
    exact mul_le_mul_of_nonneg_left (hFL _ (t n).property).2 (by positivity)
  have ht : Tendsto (fun n => (t n).val) atTop (𝓝 b) := by
    simpa only [t, sub_zero] using
      (tendsto_const_nhds (x := b)).sub (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hlim (x : ℝ) : ENNReal.ofReal (‖W x‖ ^ 2) = liminf (fun n => E n x) atTop := by
    have hc' : Continuous fun s : ℝ => ENNReal.ofReal (‖e s x * v x‖ ^ 2) := by
      apply ENNReal.continuous_ofReal.comp
      dsimp [e]
      fun_prop
    exact (hc'.continuousAt.tendsto.comp ht).liminf_eq.symm
  have hWLp : MemLp W 2 volume := by
    apply (memLp_two_iff_integrable_sq_norm hW).mpr
    refine ⟨hW.norm.pow 2, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (.of_forall fun _ => sq_nonneg _)]
    simp_rw [hlim]
    exact ((lintegral_liminf_le' hE).trans
      ((liminf_le_liminf (.of_forall hbound)).trans_eq (liminf_const _))).trans_lt ENNReal.ofReal_lt_top
  let a := stripSobolevAmplitude b b 0
  have ha : Measurable a := (stripSobolevAmplitude_continuous b b 0).measurable
  have hme : (fun x => a x • v x) = W := by
    funext x
    simp [a, stripSobolevAmplitude, W, e, Complex.real_smul, Complex.ofReal_exp]
  have hVM : MemLp v 2 (stripMeasure b b 0) :=
    (memLp_amplitudeMeasure_iff volume a ha hv).mpr (hme.symm ▸ hWLp)
  let U : StripSobolev b b 0 := hVM.toLp v
  have ha' : (volume : Measure ℝ) ≪ stripMeasure b b 0 :=
    absolutelyContinuous_amplitudeMeasure volume a ha (stripSobolevAmplitude_pos b b 0)
  have hU : (U : ℝ → ℂ) =ᵐ[volume] v := ha'.ae_le hVM.coeFn_toLp
  have hUs : U ∈ supportedSobolevCompletion b b 0 (Ioi 0) := by
    apply (mem_supportedSobolevCompletion_iff b b 0 isOpen_Ioi U).mpr
    filter_upwards [hU, hvpos] with x hx hneg hs
    rw [hx, hneg hs]
  let u : supportedSobolevCompletion b b 0 (Ioi 0) := ⟨U, hUs⟩
  refine ⟨u, fun z hz => ?_⟩
  let s : Iio b := ⟨z.re, hz⟩
  have hI : Integrable (fun x => U x * mellinEvaluationKernel 0 (s.val : ℂ) x) :=
    cutoffSobolev_mellinMoment_integrable le_rfl le_rfl u (z := (s.val : ℂ)) hz 0
  have hP : (P s : ℝ → ℂ) =ᵐ[volume] fun x => U x * mellinEvaluationKernel 0 (s.val : ℂ) x := by
    filter_upwards [hline s, hU] with x hpx hux
    change P s x = _ at hpx
    rw [hpx, hux, mellinEvaluationKernel, pow_zero, mul_one, mul_comm]
  have hPs := realFourierL2_ae_eq_fourier (P s) (hI.congr hP.symm)
  let f (y : ℝ) := F (planePoint s.val (scale * y))
  have hfs : (realFourierL2 (P s) : ℝ → ℂ) =ᵐ[volume] f := by
    change (realFourierL2 (realFourierL2.symm _) : ℝ → ℂ) =ᵐ[volume] f
    rw [LinearIsometryEquiv.apply_symm_apply]
    apply MemLp.coeFn_toLp
  have hpoint (y : ℝ) : 𝓕 (fun x => U x * mellinEvaluationKernel 0 (s.val : ℂ) x) y =
      cutoffMellinIntegral u.val 0 (planePoint s.val (scale * y)) := by
    rw [Real.fourier_eq', cutoffMellinIntegral]
    apply integral_congr_ae
    refine .of_forall fun x => ?_
    have hc' : (↑(-2 * Real.pi * (x * y)) : ℂ) * Complex.I + (s.val : ℂ) * (x : ℂ) =
        planePoint s.val (scale * y) * (x : ℂ) := by push_cast; ring
    simp only [mellinEvaluationKernel, pow_zero, mul_one, Real.inner_apply, smul_eq_mul]
    rw [mul_comm (U x), ← mul_assoc, ← Complex.exp_add, hc', mul_comm]
  have hEq : f =ᵐ[volume] fun y => cutoffMellinIntegral u.val 0 (planePoint s.val (scale * y)) :=
    hfs.symm.trans (hPs.trans (.of_forall fun y => (Real.fourier_congr_ae hP y).trans (hpoint y)))
  have hfc : Continuous f := (hardyVerticalLine_continuous hF s.property).comp
    (continuous_const.mul continuous_id)
  have hpos (y : ℝ) : (planePoint s.val (scale * y)).re = s.val := by simp [Complex.mul_re]
  have hgc : Continuous (fun y => cutoffMellinIntegral u.val 0 (planePoint s.val (scale * y))) :=
    (cutoffMellinIntegral_differentiableOn le_rfl le_rfl u).continuousOn.comp_continuous
      (by fun_prop) (fun y => by
        change (planePoint s.val (scale * y)).re < b
        rw [hpos]
        exact s.property)
  have heq := Measure.eq_of_ae_eq hEq hfc hgc
  have hs : scale ≠ 0 := neg_ne_zero.mpr (mul_ne_zero two_ne_zero Real.pi_ne_zero)
  have hzPoint : planePoint s.val (scale * (z.im / scale)) = z := by
    rw [mul_div_cancel₀ _ hs]
    exact Complex.re_add_im z
  simpa only [f, hzPoint] using congrFun heq (z.im / scale)

end
end Masullo
