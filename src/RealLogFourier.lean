import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open Filter Function MeasureTheory Set Topology
open scoped FourierTransform SchwartzMap

namespace Masullo

noncomputable section

set_option maxHeartbeats 1200000

/-- The log-weighted pairing is absolutely integrable on every real Schwartz test. -/
theorem realLogSchwartz_integrable (f : 𝓢(ℝ, ℂ)) :
    Integrable (fun x : ℝ ↦ Real.log ‖x‖ • f x) := by
  let S := Icc (-1 : ℝ) 1
  have hm : StronglyMeasurable (fun x : ℝ ↦ Real.log ‖x‖ • f x) :=
    ((Real.measurable_log.comp continuous_norm.measurable).smul f.continuous.measurable).stronglyMeasurable
  have hlog : IntegrableOn Real.log S :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (-1 : ℝ) ≤ 1)).mp
      intervalIntegral.intervalIntegrable_log'
  have hin : IntegrableOn (fun x : ℝ ↦ Real.log ‖x‖ • f x) S := by
    refine (hlog.norm.const_mul (SchwartzMap.seminorm ℂ 0 0 f)).mono' hm.aestronglyMeasurable
      (.of_forall fun x ↦ ?_)
    change ‖Real.log ‖x‖ • f x‖ ≤ SchwartzMap.seminorm ℂ 0 0 f * ‖Real.log x‖
    rw [norm_smul, Real.norm_eq_abs x, Real.log_abs, mul_comm (SchwartzMap.seminorm ℂ 0 0 f)]
    exact mul_le_mul_of_nonneg_left (f.norm_le_seminorm ℂ x) (norm_nonneg _)
  have hout : IntegrableOn (fun x : ℝ ↦ Real.log ‖x‖ • f x) Sᶜ := by
    refine ((f.integrable_pow_mul volume 1).norm.integrableOn).mono' hm.aestronglyMeasurable ?_
    refine (ae_restrict_mem isClosed_Icc.isOpen_compl.measurableSet).mono fun x hx ↦ ?_
    have hx' : 1 < ‖x‖ := by
      by_contra! h
      exact hx (abs_le.mp h)
    rw [norm_smul, Real.norm_of_nonneg (Real.log_nonneg hx'.le), norm_mul, norm_norm, pow_one]
    rw [Real.norm_of_nonneg (norm_nonneg x)]
    exact mul_le_mul_of_nonneg_right
      ((Real.log_le_sub_one_of_pos (zero_lt_one.trans hx')).trans (sub_le_self _ zero_le_one))
      (norm_nonneg _)
  simpa only [union_compl_self, integrableOn_univ] using hin.union hout

/-- The additive logarithm paired with the real Fourier transform. -/
def realLogFourierPairing (f : 𝓢(ℝ, ℂ)) : ℂ :=
  ∫ x : ℝ, Real.log ‖x‖ • (𝓕 f) x

/-- Either Fourier sign gives the same pairing against the even logarithm. -/
theorem realLogFourierPairing_eq_inverse (f : 𝓢(ℝ, ℂ)) :
    realLogFourierPairing f = ∫ x : ℝ, Real.log ‖x‖ • (𝓕⁻ f) x := by
  let g (x : ℝ) := Real.log ‖x‖ • (𝓕 f) x
  unfold realLogFourierPairing
  change (∫ x : ℝ, g x) = _
  rw [← integral_neg_eq_self g volume]
  apply integral_congr_ae
  refine .of_forall fun x ↦ ?_
  change Real.log ‖-x‖ • (𝓕 f) (-x) = Real.log ‖x‖ • (𝓕⁻ f) x
  rw [norm_neg, SchwartzMap.fourierInv_coe, SchwartzMap.fourier_coe,
    Real.fourierInv_eq_fourier_neg]

/-- Dilation by a positive scalar in the real Schwartz space. -/
def realSchwartzDilate (a : ℝ) (ha : 0 < a) (f : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (LinearEquiv.smulOfNeZero ℝ ℝ a⁻¹ (inv_ne_zero ha.ne')).toContinuousLinearEquiv f

theorem realSchwartzDilate_apply (a : ℝ) (ha : 0 < a) (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    realSchwartzDilate a ha f x = f (a⁻¹ * x) := rfl

theorem realFourier_dilate (a : ℝ) (ha : 0 < a) (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    (𝓕 (realSchwartzDilate a ha f)) x = a • (𝓕 f) (a * x) := by
  simp only [SchwartzMap.fourier_coe, Real.fourier_real_eq_integral_exp_smul]
  let g (y : ℝ) := Complex.exp (↑(-2 * Real.pi * y * (a * x)) * Complex.I) • f y
  have h (y : ℝ) : Complex.exp (↑(-2 * Real.pi * y * x) * Complex.I) •
      realSchwartzDilate a ha f y = g (a⁻¹ * y) := by
    rw [realSchwartzDilate_apply]
    congr 1
    have he : -2 * Real.pi * y * x = -2 * Real.pi * (a⁻¹ * y) * (a * x) := by
      field_simp
    exact congrArg (fun t : ℝ ↦ Complex.exp ((t : ℂ) * Complex.I)) he
  calc
    _ = ∫ y : ℝ, g (a⁻¹ * y) := integral_congr_ae (.of_forall h)
    _ = _ := by
      rw [Measure.integral_comp_inv_mul_left, abs_of_pos ha]

theorem integral_realSchwartz_fourier (f : 𝓢(ℝ, ℂ)) : (∫ y : ℝ, (𝓕 f) y) = f 0 := by
  have he : (𝓕⁻ (𝓕 f : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ)) = f :=
    FourierTransform.fourierInv_fourier_eq (F := 𝓢(ℝ, ℂ)) f
  have h := congrArg (fun g : 𝓢(ℝ, ℂ) ↦ g 0) he
  change (𝓕⁻ (𝓕 f)) 0 = f 0 at h
  rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq_fourier_neg, neg_zero,
    Real.fourier_real_eq_integral_exp_smul] at h
  simpa only [mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_smul] using h

/-- A positive dilation changes the real logarithmic Fourier pairing by one
logarithm times evaluation at zero. -/
theorem realLogFourierPairing_dilate (a : ℝ) (ha : 0 < a) (f : 𝓢(ℝ, ℂ)) :
    realLogFourierPairing (realSchwartzDilate a ha f) =
      realLogFourierPairing f - Real.log a • f 0 := by
  let g (y : ℝ) := Real.log ‖a⁻¹ * y‖ • (𝓕 f) y
  have hg : (fun y : ℝ ↦ g y) =ᵐ[volume]
      fun y ↦ Real.log ‖y‖ • (𝓕 f) y - Real.log a • (𝓕 f) y := by
    have hzero : ∀ᵐ y : ℝ ∂volume, y ≠ 0 := ae_iff.mpr (by
      simpa only [not_not, ofPred_eq_eq_singleton] using measure_singleton (0 : ℝ) (μ := volume))
    filter_upwards [hzero] with y hy
    change Real.log ‖a⁻¹ * y‖ • (𝓕 f) y =
      Real.log ‖y‖ • (𝓕 f) y - Real.log a • (𝓕 f) y
    rw [norm_mul, Real.norm_of_nonneg (inv_nonneg.mpr ha.le),
      Real.log_mul (inv_ne_zero ha.ne') (norm_ne_zero_iff.mpr hy), Real.log_inv, neg_add_eq_sub, sub_smul]
  unfold realLogFourierPairing
  calc
    _ = a • (∫ y : ℝ, g (a * y)) := by
      rw [← integral_smul]
      apply integral_congr_ae
      refine .of_forall fun y ↦ ?_
      change Real.log ‖y‖ • (𝓕 (realSchwartzDilate a ha f)) y = a • g (a * y)
      rw [realFourier_dilate]
      dsimp only [g]
      rw [inv_mul_cancel_left₀ ha.ne', smul_comm]
    _ = ∫ y : ℝ, g y := by
      rw [Measure.integral_comp_mul_left, abs_of_pos (inv_pos.mpr ha), smul_smul,
        mul_inv_cancel₀ ha.ne', one_smul]
    _ = _ := by
      have hi : Integrable (fun y : ℝ ↦ Real.log a • (𝓕 f) y) :=
        ((SchwartzMap.integrable (𝓕 f) (μ := volume)).smul (Real.log a))
      rw [integral_congr_ae hg, integral_sub (realLogSchwartz_integrable (𝓕 f)) hi,
        integral_smul, integral_realSchwartz_fourier]

/-- The real cutoff convention in (B.4.3.13). -/
def realLogCutoff (f : 𝓢(ℝ, ℂ)) (ε : ℝ) : ℂ :=
  (∫ x in {x : ℝ | ε ≤ ‖x‖}, ‖x‖⁻¹ • f x) + (2 * Real.log ε : ℝ) • f 0

/-- The truncated integral is absolutely convergent at every positive cutoff. -/
theorem realLogCutoff_integrableOn (f : 𝓢(ℝ, ℂ)) {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun x : ℝ ↦ ‖x‖⁻¹ • f x) {x : ℝ | ε ≤ ‖x‖} := by
  have hL : MeasurableSet {x : ℝ | ε ≤ ‖x‖} :=
    (isClosed_le continuous_const continuous_norm).measurableSet
  refine (f.integrable.norm.const_mul ε⁻¹).integrableOn.mono'
    (continuous_norm.measurable.inv.smul f.continuous.measurable).aestronglyMeasurable ?_
  refine (ae_restrict_mem hL).mono fun x hx ↦ ?_
  change ‖‖x‖⁻¹ • f x‖ ≤ ε⁻¹ * ‖f x‖
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg x))]
  exact mul_le_mul_of_nonneg_right (inv_anti₀ hε hx) (norm_nonneg _)

/-- A locally subtracted integrand for the finite part of the real cutoff. -/
def realLogCutoffRemainder (f : 𝓢(ℝ, ℂ)) (x : ℝ) : ℂ :=
  ‖x‖⁻¹ • (f x - {y : ℝ | ‖y‖ ≤ 1}.indicator (fun _ ↦ f 0) x)

theorem realLogCutoffRemainder_integrable (f : 𝓢(ℝ, ℂ)) :
    Integrable (realLogCutoffRemainder f) := by
  let S := {x : ℝ | ‖x‖ ≤ 1}
  have hS : S = Icc (-1 : ℝ) 1 := by
    ext x
    change |x| ≤ (1 : ℝ) ↔ -1 ≤ x ∧ x ≤ 1
    exact abs_le
  have hSm : MeasurableSet S := hS ▸ measurableSet_Icc
  let M := SchwartzMap.seminorm ℂ 0 1 f
  have hM : 0 ≤ M := apply_nonneg _ _
  let m := Real.toNNReal M
  have hM' : (m : ℝ) = M := Real.coe_toNNReal _ hM
  have hl : LipschitzWith m (f : ℝ → ℂ) := by
    apply lipschitzWith_of_nnnorm_fderiv_le (𝕜 := ℝ) f.differentiable
    intro x
    rw [← NNReal.coe_le_coe, coe_nnnorm, hM', ← norm_iteratedFDeriv_one]
    exact f.norm_iteratedFDeriv_le_seminorm ℂ 1 x
  have hm : Measurable (realLogCutoffRemainder f) :=
    continuous_norm.measurable.inv.smul (f.continuous.measurable.sub (measurable_const.indicator hSm))
  have hin : IntegrableOn (realLogCutoffRemainder f) S := by
    letI : IsFiniteMeasure (volume.restrict S) := ⟨by rw [Measure.restrict_apply_univ, hS]; exact measure_Icc_lt_top⟩
    refine (integrable_const M).mono' hm.aestronglyMeasurable ?_
    refine (ae_restrict_mem hSm).mono fun x hx ↦ ?_
    change ‖‖x‖⁻¹ • (f x - S.indicator (fun _ ↦ f 0) x)‖ ≤ M
    rw [indicator_of_mem hx, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg x))]
    by_cases hx₀ : x = 0
    · subst x; simp [hM]
    have h := hl.dist_le_mul x 0
    rw [dist_eq_norm, dist_zero_right, hM'] at h
    exact (inv_mul_le_iff₀ (norm_pos_iff.mpr hx₀)).mpr (by simpa only [mul_comm] using h)
  have hout : IntegrableOn (realLogCutoffRemainder f) Sᶜ := by
    refine f.integrable.norm.integrableOn.mono' hm.aestronglyMeasurable ?_
    refine (ae_restrict_mem hSm.compl).mono fun x hx ↦ ?_
    change ‖‖x‖⁻¹ • (f x - S.indicator (fun _ ↦ f 0) x)‖ ≤ ‖f x‖
    rw [indicator_of_notMem hx, sub_zero, norm_smul,
      Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg x))]
    have hp : 1 < ‖x‖ := lt_of_not_ge hx
    exact mul_le_of_le_one_left (norm_nonneg _) (inv_le_one_of_one_le₀ hp.le)
  simpa only [union_compl_self, integrableOn_univ] using hin.union hout

private theorem realLogCutoff_shell_integral {ε : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1) :
    (∫ x in {x : ℝ | ε ≤ ‖x‖ ∧ ‖x‖ ≤ 1}, ‖x‖⁻¹) = -2 * Real.log ε := by
  let P := Icc ε 1
  let N := Icc (-1 : ℝ) (-ε)
  have hn : {x : ℝ | ε ≤ ‖x‖ ∧ ‖x‖ ≤ 1} = P ∪ N := by
    ext x
    change (ε ≤ |x| ∧ |x| ≤ 1) ↔ (ε ≤ x ∧ x ≤ 1) ∨ (-1 ≤ x ∧ x ≤ -ε)
    by_cases hx : 0 ≤ x
    · rw [abs_of_nonneg hx]
      constructor
      · exact Or.inl
      · rintro (h | h)
        · exact h
        · linarith [h.2]
    · rw [abs_of_neg (lt_of_not_ge hx)]
      constructor
      · intro h
        exact Or.inr ⟨by linarith [h.2], by linarith [h.1]⟩
      · rintro (h | h)
        · linarith [h.1]
        · exact ⟨by linarith [h.2], by linarith [h.1]⟩
  have hP : IntegrableOn (fun x : ℝ ↦ ‖x‖⁻¹) P := by
    apply ContinuousOn.integrableOn_Icc
    exact continuous_norm.continuousOn.inv₀ fun x hx ↦
      norm_ne_zero_iff.mpr (ne_of_gt (hε.trans_le hx.1))
  have hN : IntegrableOn (fun x : ℝ ↦ ‖x‖⁻¹) N := by
    apply ContinuousOn.integrableOn_Icc
    exact continuous_norm.continuousOn.inv₀ fun x hx ↦
      norm_ne_zero_iff.mpr (ne_of_lt (hx.2.trans_lt (neg_lt_zero.mpr hε)))
  have hdis : Disjoint P N := by
    rw [Set.disjoint_left]
    intro x hx hy
    exact (hε.trans_le hx.1).not_ge (hy.2.trans (neg_nonpos.mpr hε.le))
  have he : (∫ x in N, ‖x‖⁻¹) = ∫ x in P, ‖x‖⁻¹ := by
    rw [← integral_indicator (measurableSet_Icc : MeasurableSet N),
      ← integral_indicator (measurableSet_Icc : MeasurableSet P)]
    let g := N.indicator (fun x : ℝ ↦ ‖x‖⁻¹)
    rw [← integral_neg_eq_self g volume]
    apply integral_congr_ae
    refine .of_forall fun x ↦ ?_
    have hm : -x ∈ N ↔ x ∈ P := by
      change -1 ≤ -x ∧ -x ≤ -ε ↔ ε ≤ x ∧ x ≤ 1
      rw [neg_le_neg_iff, neg_le_neg_iff, and_comm]
    by_cases hx : x ∈ P
    · change N.indicator _ (-x) = P.indicator _ x
      rw [indicator_of_mem (hm.mpr hx), indicator_of_mem hx, norm_neg]
    · change N.indicator _ (-x) = P.indicator _ x
      rw [indicator_of_notMem (mt hm.mp hx), indicator_of_notMem hx]
  have hp : (∫ x in P, ‖x‖⁻¹) = -Real.log ε := by
    calc
      _ = ∫ x in P, x⁻¹ := setIntegral_congr_fun measurableSet_Icc fun x hx ↦ by
        rw [Real.norm_of_nonneg (hε.le.trans hx.1)]
      _ = ∫ x in ε..1, x⁻¹ := by
        rw [intervalIntegral.integral_of_le hε₁, integral_Icc_eq_integral_Ioc]
      _ = _ := by
        rw [integral_inv, one_div, Real.log_inv]
        rw [uIcc_of_le hε₁]
        exact fun h ↦ hε.not_ge h.1
  rw [hn, setIntegral_union hdis measurableSet_Icc hP hN, he, hp]
  ring

private theorem realLogCutoff_eq_remainder (f : 𝓢(ℝ, ℂ)) {ε : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1) :
    realLogCutoff f ε = ∫ x in {x : ℝ | ε ≤ ‖x‖}, realLogCutoffRemainder f x := by
  let L := {x : ℝ | ε ≤ ‖x‖}
  let S := {x : ℝ | ‖x‖ ≤ 1}
  let g (x : ℝ) := ‖x‖⁻¹ • f x
  let h (x : ℝ) := ‖x‖⁻¹ • S.indicator (fun _ ↦ f 0) x
  have hL : MeasurableSet L := (isClosed_le continuous_const continuous_norm).measurableSet
  have hS : MeasurableSet S := (isClosed_le continuous_norm continuous_const).measurableSet
  have hg : IntegrableOn g L := realLogCutoff_integrableOn f hε
  have hd (x : ℝ) : realLogCutoffRemainder f x = g x - h x := by
    unfold realLogCutoffRemainder
    exact smul_sub ..
  have hi : IntegrableOn h L := by
    refine (hg.sub (realLogCutoffRemainder_integrable f).integrableOn).congr
      (.of_forall fun x ↦ ?_)
    change g x - realLogCutoffRemainder f x = h x
    rw [hd, sub_sub_cancel]
  have he : (∫ x in L, h x) = (-2 * Real.log ε : ℝ) • f 0 := by
    calc
      _ = ∫ x in L ∩ S, ‖x‖⁻¹ • f 0 := by
        rw [← integral_indicator hL, ← integral_indicator (hL.inter hS)]
        apply integral_congr_ae
        refine .of_forall fun x ↦ ?_
        change L.indicator h x = (L ∩ S).indicator (fun y : ℝ ↦ ‖y‖⁻¹ • f 0) x
        by_cases hx : x ∈ L
        · rw [indicator_of_mem hx]
          by_cases hy : x ∈ S
          · rw [indicator_of_mem (show x ∈ L ∩ S from ⟨hx, hy⟩)]
            simp only [h, indicator_of_mem hy]
          · rw [indicator_of_notMem (fun H : x ∈ L ∩ S ↦ hy H.2)]
            simp only [h, indicator_of_notMem hy, smul_zero]
        · rw [indicator_of_notMem hx, indicator_of_notMem (fun H : x ∈ L ∩ S ↦ hx H.1)]
      _ = _ := by
        rw [integral_smul_const]
        have hh : (∫ x in L ∩ S, ‖x‖⁻¹) = -2 * Real.log ε := realLogCutoff_shell_integral hε hε₁
        rw [hh]
  have hs : (∫ x in L, realLogCutoffRemainder f x) = (∫ x in L, g x) - ∫ x in L, h x := by
    exact (integral_congr_ae (.of_forall hd)).trans (integral_sub hg hi)
  change (∫ x in L, g x) + (2 * Real.log ε : ℝ) • f 0 = _
  rw [hs, he, neg_mul, neg_smul, sub_neg_eq_add]

/-- The cutoff limit in the real formula exists on the full Schwartz space. -/
theorem realLogCutoff_tendsto (f : 𝓢(ℝ, ℂ)) :
    Tendsto (realLogCutoff f) (𝓝[>] 0)
      (𝓝 (∫ x : ℝ, realLogCutoffRemainder f x)) := by
  let g := realLogCutoffRemainder f
  let L (ε : ℝ) := {x : ℝ | ε ≤ ‖x‖}
  have hm (ε : ℝ) : MeasurableSet (L ε) := (isClosed_le continuous_const continuous_norm).measurableSet
  have hi : Integrable g := realLogCutoffRemainder_integrable f
  have ht : Tendsto (fun ε : ℝ ↦ ∫ x : ℝ, (L ε).indicator g x) (𝓝[>] 0) (𝓝 (∫ x : ℝ, g x)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun x : ℝ ↦ ‖g x‖)
      (.of_forall fun ε ↦ hi.aestronglyMeasurable.indicator (hm ε))
      (.of_forall fun ε ↦ .of_forall fun x ↦ ?_) hi.norm ?_
    · by_cases hx : x ∈ L ε
      · rw [indicator_of_mem hx]
      · rw [indicator_of_notMem hx, norm_zero]
        exact norm_nonneg _
    · have hn : ∀ᵐ x : ℝ ∂volume, x ≠ 0 := ae_iff.mpr (by
        simpa only [not_not, ofPred_eq_eq_singleton] using measure_singleton (0 : ℝ) (μ := volume))
      filter_upwards [hn] with x hx
      refine tendsto_const_nhds.congr' ?_
      have he := (show ∀ᶠ ε : ℝ in 𝓝 0, ε < ‖x‖ from Iio_mem_nhds (norm_pos_iff.mpr hx)).filter_mono
        (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
      filter_upwards [he] with ε hε
      exact (indicator_of_mem (show x ∈ L ε from le_of_lt hε) g).symm
  apply ht.congr'
  have hlt : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε < 1 :=
    (show ∀ᶠ ε : ℝ in 𝓝 0, ε < 1 from Iio_mem_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hlt] with ε hε hε₁
  rw [integral_indicator (hm ε), realLogCutoff_eq_remainder f hε hε₁.le]

theorem realLogCutoff_dilate (a ε : ℝ) (ha : 0 < a) (hε : 0 < ε) (f : 𝓢(ℝ, ℂ)) :
    realLogCutoff (realSchwartzDilate a ha f) ε =
      realLogCutoff f (ε / a) + (2 * Real.log a : ℝ) • f 0 := by
  let L (r : ℝ) : Set ℝ := {x | r ≤ ‖x‖}
  have hm (r : ℝ) : MeasurableSet (L r) := (isClosed_le continuous_const continuous_norm).measurableSet
  let g := (L (ε / a)).indicator (fun x : ℝ ↦ ‖x‖⁻¹ • f x)
  have hlocal : (∫ x in L ε, ‖x‖⁻¹ • realSchwartzDilate a ha f x) =
      ∫ x in L (ε / a), ‖x‖⁻¹ • f x := by
    rw [← integral_indicator (hm ε), ← integral_indicator (hm (ε / a))]
    calc
      _ = a⁻¹ • (∫ x : ℝ, g (a⁻¹ * x)) := by
        rw [← integral_smul]
        apply integral_congr_ae
        refine .of_forall fun x ↦ ?_
        have he : a⁻¹ * x ∈ L (ε / a) ↔ x ∈ L ε := by
          change ε / a ≤ ‖a⁻¹ * x‖ ↔ ε ≤ ‖x‖
          rw [norm_mul, Real.norm_of_nonneg (inv_nonneg.mpr ha.le), inv_mul_eq_div,
            div_le_div_iff_of_pos_right ha]
        change (L ε).indicator (fun x : ℝ ↦ ‖x‖⁻¹ • realSchwartzDilate a ha f x) x =
          a⁻¹ • (L (ε / a)).indicator (fun z : ℝ ↦ ‖z‖⁻¹ • f z) (a⁻¹ * x)
        by_cases hx : x ∈ L ε
        · rw [indicator_of_mem hx, indicator_of_mem (he.mpr hx), realSchwartzDilate_apply,
            norm_mul, Real.norm_of_nonneg (inv_nonneg.mpr ha.le), mul_inv, inv_inv,
            smul_smul, ← mul_assoc, inv_mul_cancel₀ ha.ne', one_mul]
        · rw [indicator_of_notMem hx, indicator_of_notMem (mt he.mp hx), smul_zero]
      _ = _ := by
        rw [Measure.integral_comp_inv_mul_left, abs_of_pos ha, smul_smul, inv_mul_cancel₀ ha.ne', one_smul]
  unfold realLogCutoff
  change (∫ x in L ε, ‖x‖⁻¹ • realSchwartzDilate a ha f x) + _ = _
  rw [hlocal, realSchwartzDilate_apply, mul_zero, Real.log_div hε.ne' ha.ne']
  rw [mul_sub, sub_smul]
  abel

private theorem tendsto_realLogCutoff_scale {a : ℝ} (ha : 0 < a) :
    Tendsto (fun ε : ℝ ↦ ε / a) (𝓝[>] 0) (𝓝[>] 0) := by
  apply tendsto_nhdsWithin_iff.mpr
  have ht : ContinuousAt (fun ε : ℝ ↦ ε / a) 0 := continuous_id.continuousAt.div_const _
  exact ⟨(by simpa only [zero_div] using ht.tendsto.mono_left nhdsWithin_le_nhds),
    (show ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ∈ Ioi 0 from self_mem_nhdsWithin).mono
      (fun ε hε ↦ div_pos hε ha)⟩

theorem realLogCutoffRemainder_dilate (a : ℝ) (ha : 0 < a) (f : 𝓢(ℝ, ℂ)) :
    (∫ x : ℝ, realLogCutoffRemainder (realSchwartzDilate a ha f) x) =
      (∫ x : ℝ, realLogCutoffRemainder f x) + (2 * Real.log a : ℝ) • f 0 := by
  let g := realSchwartzDilate a ha f
  have hs := (realLogCutoff_tendsto f).comp (tendsto_realLogCutoff_scale ha)
  have he : (fun ε : ℝ ↦ realLogCutoff f (ε / a) + (2 * Real.log a : ℝ) • f 0) =ᶠ[𝓝[>] 0]
      realLogCutoff g := by
    filter_upwards [show ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ∈ Ioi 0 from self_mem_nhdsWithin] with ε hε
    exact (realLogCutoff_dilate a ε ha hε f).symm
  exact tendsto_nhds_unique (realLogCutoff_tendsto g) ((hs.add tendsto_const_nhds).congr' he)

/-- Any formula of this cutoff form valid on all real Schwartz functions
must use coefficient minus one half. -/
theorem realLogFourier_cutoff_coefficient_unique (A B : ℂ)
    (h : ∀ f : 𝓢(ℝ, ℂ), realLogFourierPairing f =
      A * (∫ x : ℝ, realLogCutoffRemainder f x) + B * f 0) :
    A = -(1 / 2 : ℂ) := by
  let bump : ContDiffBump (0 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩
  let f : 𝓢(ℝ, ℂ) := (bump.hasCompactSupport.comp_left Complex.ofReal_zero).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp bump.contDiff)
  have hf : f 0 = 1 := by
    change (bump 0 : ℂ) = 1
    rw [bump.one_of_mem_closedBall, Complex.ofReal_one]
    exact Metric.mem_closedBall_self bump.rIn_pos.le
  let g := realSchwartzDilate 2 (by norm_num) f
  have hg : g 0 = 1 := by rw [realSchwartzDilate_apply, mul_zero, hf]
  have hEq := h g
  rw [hg, realLogFourierPairing_dilate 2 (by norm_num) f,
    realLogCutoffRemainder_dilate 2 (by norm_num) f, h f, hf] at hEq
  simp only [Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_ofNat, mul_one] at hEq
  have hz : (Real.log 2 : ℂ) * (2 * A + 1) = 0 := by linear_combination -hEq
  have hlog : (Real.log 2 : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  have hc := (mul_eq_zero.mp hz).resolve_left hlog
  linear_combination hc / 2

/-- No choice of delta constant makes the full printed real cutoff coefficient
in (B.4.3.13) compatible with the logarithmic Fourier pairing. -/
theorem realLogFourier_printed_coefficient_false (b : ℂ) :
    ¬ ∀ f : 𝓢(ℝ, ℂ), Tendsto (realLogCutoff f) (𝓝[>] 0)
      (𝓝 (-realLogFourierPairing f - b * f 0)) := by
  intro h
  have hEq (f : 𝓢(ℝ, ℂ)) : realLogFourierPairing f =
      (-1 : ℂ) * (∫ x : ℝ, realLogCutoffRemainder f x) + (-b) * f 0 := by
    have h := tendsto_nhds_unique (realLogCutoff_tendsto f) (h f)
    rw [h]
    ring
  have hbad := realLogFourier_cutoff_coefficient_unique (-1) (-b) hEq
  norm_num at hbad

end
end Masullo
