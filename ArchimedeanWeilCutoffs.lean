import ArchimedeanLogDistribution
import RealTateFunctionalEquation
import ComplexTateFunctionalEquation

open Filter Function MeasureTheory Set Topology
open scoped ContDiff ENNReal NNReal SchwartzMap RealInnerProductSpace

namespace Masullo

noncomputable section

section Test

variable {K : Type*} [RCLike K]

/-- Extend a local multiplicative test by zero on the additive origin. -/
def archWeilZeroExtension (f : Kˣ → ℂ) (x : K) : ℂ :=
  if h : x = 0 then 0 else f (Units.mk0 x h)

@[simp] theorem archWeilZeroExtension_unit (f : Kˣ → ℂ) (u : Kˣ) :
    archWeilZeroExtension f u.val = f u := by
  rw [archWeilZeroExtension, dite_eq_right u.ne_zero]
  congr 1
  exact Units.ext rfl

private theorem archWeilZeroExtension_tsupport_subset (f : Kˣ → ℂ) (hf : HasCompactSupport f) :
    tsupport (archWeilZeroExtension f) ⊆ (Units.val : Kˣ → K) '' tsupport f := by
  apply closure_minimal _ (hf.isCompact.image Units.continuous_val).isClosed
  intro x hx
  have hn : x ≠ 0 := by
    intro h
    exact hx (by simp [archWeilZeroExtension, h])
  refine ⟨Units.mk0 x hn, subset_closure ?_, rfl⟩
  change f (Units.mk0 x hn) ≠ 0
  exact (archWeilZeroExtension_unit f (Units.mk0 x hn)) ▸ hx

private theorem archWeilZeroExtension_eventually_zero (f : Kˣ → ℂ) (hf : HasCompactSupport f) :
    archWeilZeroExtension f =ᶠ[𝓝 (0 : K)] 0 := by
  have hO := (hf.isCompact.image (Units.continuous_val (M := K))).isClosed.isOpen_compl
  have h0 : (0 : K) ∈ ((Units.val : Kˣ → K) '' tsupport f)ᶜ := by
    rintro ⟨u, _, hu⟩
    exact u.ne_zero hu
  filter_upwards [hO.mem_nhds h0] with x hx
  exact Function.notMem_support.mp (fun h ↦ hx
    (archWeilZeroExtension_tsupport_subset f hf (subset_closure h)))

/-- The affine involution interchanging zero and one. -/
def oneSubHomeomorph (K : Type*) [RCLike K] : K ≃ₜ K where
  toFun x := 1 - x
  invFun x := 1 - x
  left_inv x := sub_sub_cancel 1 x
  right_inv x := sub_sub_cancel 1 x
  continuous_toFun := continuous_const.sub continuous_id
  continuous_invFun := continuous_const.sub continuous_id

private theorem archWeilWeightedTest_hasCompactSupport (n : ℕ) (f : Kˣ → ℂ)
    (hf : HasCompactSupport f) :
    HasCompactSupport (fun x : K => ‖x‖ ^ (-(n : ℝ) / 2) • archWeilZeroExtension f x) :=
  (hf.isCompact.image Units.continuous_val).of_isClosed_subset isClosed_closure
    (closure_minimal (fun x hx ↦ archWeilZeroExtension_tsupport_subset f hf
      (subset_closure (fun h ↦ hx (by simp [h]))))
      (hf.isCompact.image Units.continuous_val).isClosed)

/-- Additive Schwartz test for the multiplicative cutoff after the change
of variable `x = 1 - g`. The exponent is half the local modulus degree. -/
def archWeilShiftedTest (n : ℕ) (f : Kˣ → ℂ) (hf : HasCompactSupport f)
    (hs : ContDiffOn ℝ ∞ (archWeilZeroExtension f) ({0} : Set K)ᶜ) : 𝓢(K, ℂ) := by
  let q (x : K) := ‖x‖ ^ (-(n : ℝ) / 2) • archWeilZeroExtension f x
  have hqC : HasCompactSupport q := archWeilWeightedTest_hasCompactSupport n f hf
  have hqs : ContDiff ℝ ∞ q := by
    rw [contDiff_iff_contDiffAt]
    intro x
    rcases eq_or_ne x 0 with rfl | hx
    · apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
      filter_upwards [archWeilZeroExtension_eventually_zero f hf] with x hx
      change archWeilZeroExtension f x = 0 at hx
      simp [q, hx]
    · have hn : ContDiffAt ℝ ∞ (fun x : K ↦ ‖x‖ ^ (-(n : ℝ) / 2)) x :=
        (contDiffAt_norm ℝ hx).rpow_const_of_ne (norm_ne_zero_iff.mpr hx)
      apply hn.smul
      exact (hs x hx).contDiffAt (isOpen_compl_singleton.mem_nhds hx)
  exact (hqC.comp_homeomorph (oneSubHomeomorph K)).toSchwartzMap
    (hqs.comp (contDiff_const.sub contDiff_id))

theorem archWeilShiftedTest_apply (n : ℕ) (f : Kˣ → ℂ) (hf : HasCompactSupport f)
    (hs : ContDiffOn ℝ ∞ (archWeilZeroExtension f) ({0} : Set K)ᶜ) (x : K) :
    archWeilShiftedTest n f hf hs x =
      ‖1 - x‖ ^ (-(n : ℝ) / 2) • archWeilZeroExtension f (1 - x) := rfl

@[simp] theorem archWeilShiftedTest_zero (n : ℕ) (f : Kˣ → ℂ) (hf : HasCompactSupport f)
    (hs : ContDiffOn ℝ ∞ (archWeilZeroExtension f) ({0} : Set K)ᶜ) :
    archWeilShiftedTest n f hf hs 0 = f 1 := by
  rw [archWeilShiftedTest_apply, sub_zero, norm_one, Real.one_rpow, one_smul]
  exact archWeilZeroExtension_unit f 1

theorem archWeilShiftedTest_hasCompactSupport (n : ℕ) (f : Kˣ → ℂ)
    (hf : HasCompactSupport f)
    (hs : ContDiffOn ℝ ∞ (archWeilZeroExtension f) ({0} : Set K)ᶜ) :
    HasCompactSupport (archWeilShiftedTest n f hf hs : K → ℂ) :=
  (archWeilWeightedTest_hasCompactSupport n f hf).comp_homeomorph (oneSubHomeomorph K)

end Test

section Integral

variable {K : Type*} [RCLike K] [MeasurableSpace Kˣ] [BorelSpace Kˣ]
  [MeasureSpace K] [BorelSpace K] [Measure.IsAddHaarMeasure (volume : Measure K)]

/-- The raw multiplicative integral truncated in the normalized local
absolute value of `1 - g`. -/
def archWeilTruncated (n : ℕ) (μ : Measure Kˣ) (f : Kˣ → ℂ) (ε : ℝ) : ℂ :=
  ∫ u in {u : Kˣ | ε ≤ ‖1 - u.val‖ ^ n},
    (‖1 - u.val‖ ^ n)⁻¹ • (‖u.val‖ ^ ((n : ℝ) / 2) • f u) ∂μ

/-- Pullback of the additive cutoff to a multiplicative Haar integral, with
its Jacobian and the half-modulus in the numerator. -/
theorem archWeilTruncated_eq_additive (n : ℕ) (μ : Measure Kˣ) (c : ℝ≥0)
    (hμ : Measure.map (Units.val : Kˣ → K)
      (μ.withDensity fun u ↦ ENNReal.ofReal (‖u.val‖ ^ n)) = c • volume)
    (f : Kˣ → ℂ) (hf : HasCompactSupport f)
    (hs : ContDiffOn ℝ ∞ (archWeilZeroExtension f) ({0} : Set K)ᶜ) (ε : ℝ) :
    archWeilTruncated n μ f ε =
      c • ∫ x in {x : K | ε ≤ ‖x‖ ^ n}, (‖x‖ ^ n)⁻¹ • archWeilShiftedTest n f hf hs x := by
  let L : Set K := {x : K | ε ≤ ‖x‖ ^ n}
  let b := archWeilShiftedTest n f hf hs
  let G : K → ℂ := L.indicator (fun x ↦ (‖x‖ ^ n)⁻¹ • b x)
  have hL : MeasurableSet L := (isClosed_le continuous_const (continuous_norm.pow n)).measurableSet
  have hG : Measurable G :=
    ((continuous_norm.measurable.pow_const n).inv.smul b.continuous.measurable).indicator hL
  have hW : Measurable (fun u : Kˣ ↦ ENNReal.ofReal (‖u.val‖ ^ n)) :=
    (Units.continuous_val.measurable.norm.pow_const n).ennreal_ofReal
  have hSub (x : K) : b (1 - x) = ‖x‖ ^ (-(n : ℝ) / 2) • archWeilZeroExtension f x := by
    rw [archWeilShiftedTest_apply, sub_sub_cancel]
  have hvol : (∫ x, G (1 - x)) = ∫ x, G x :=
    (Measure.measurePreserving_sub_left volume (1 : K)).integral_comp
      (MeasurableEquiv.subLeft (1 : K)).measurableEmbedding G
  have hMap : (∫ x, G (1 - x) ∂(c • volume : Measure K)) = c • ∫ x, G x := by
    rw [integral_smul_nnreal_measure, hvol]
  have hGM : Measurable (fun x : K ↦ G (1 - x)) :=
    hG.comp (continuous_const.sub continuous_id).measurable
  rw [← hμ, integral_map Units.continuous_val.measurable.aemeasurable hGM.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul hW (.of_forall fun _ ↦ ENNReal.ofReal_lt_top)] at hMap
  let T := (fun u : Kˣ ↦ 1 - u.val) ⁻¹' L
  have hTm : MeasurableSet T :=
    hL.preimage (continuous_const.sub Units.continuous_val).measurable
  change (∫ u in T, (‖1 - u.val‖ ^ n)⁻¹ • (‖u.val‖ ^ ((n : ℝ) / 2) • f u) ∂μ) =
    c • ∫ x in L, (‖x‖ ^ n)⁻¹ • b x
  rw [← integral_indicator hTm, ← integral_indicator hL, ← hMap]
  apply integral_congr_ae
  refine .of_forall fun u ↦ ?_
  by_cases hu : (1 - u.val) ∈ L
  · have huT : u ∈ T := hu
    simp only [indicator_of_mem huT, G, indicator_of_mem hu,
      ENNReal.toReal_ofReal (pow_nonneg (norm_nonneg _) _), hSub,
      archWeilZeroExtension_unit, smul_smul]
    have hn : 0 < ‖u.val‖ := norm_pos_iff.mpr u.ne_zero
    have hp : ‖u.val‖ ^ n * ‖u.val‖ ^ (-(n : ℝ) / 2) = ‖u.val‖ ^ ((n : ℝ) / 2) := by
      rw [← Real.rpow_natCast ‖u.val‖ n, ← Real.rpow_add hn]
      congr 1
      ring
    rw [← hp]
    congr 1
    ring
  · have huT : u ∉ T := hu
    simp only [indicator_of_notMem huT, G, indicator_of_notMem hu, smul_zero]

end Integral

section RealPlace

variable [MeasurableSpace ℝˣ] [BorelSpace ℝˣ]

/-- The normalized real-place principal value in multiplicative coordinates. -/
theorem realWeilTruncated_tendsto (f : ℝˣ → ℂ) (hf : HasCompactSupport f)
    (hs : ContDiffOn ℝ ∞ (archWeilZeroExtension f) ({0} : Set ℝ)ᶜ) :
    Tendsto (fun ε ↦ (2 : ℝ)⁻¹ • (archWeilTruncated 1 realArchMultiplicativeHaar f ε +
      (2 * Real.log ε : ℝ) • f 1) +
      (Real.eulerMascheroniConstant + Real.log (2 * Real.pi)) • f 1)
      (𝓝[>] 0) (𝓝 (-realLogFourierDistribution (archWeilShiftedTest 1 f hf hs))) := by
  let b := archWeilShiftedTest 1 f hf hs
  have h := ((archimedeanLogFourier_cutoff_corrected).1 b).neg
  apply h.congr'
  apply Eventually.of_forall
  intro ε
  have hI := archWeilTruncated_eq_additive 1 realArchMultiplicativeHaar 1
    (by simpa only [pow_one, one_smul] using realArchHaar_weighted_map) f hf hs ε
  simp only [pow_one, one_smul] at hI
  change -(-(2 : ℝ)⁻¹ • realLogCutoff b ε -
    (Real.eulerMascheroniConstant + Real.log (2 * Real.pi)) • b 0) =
      (2 : ℝ)⁻¹ • (archWeilTruncated 1 realArchMultiplicativeHaar f ε +
        (2 * Real.log ε : ℝ) • f 1) +
      (Real.eulerMascheroniConstant + Real.log (2 * Real.pi)) • f 1
  rw [hI]
  simp only [realLogCutoff, b, archWeilShiftedTest_zero, neg_sub, neg_smul]
  abel

end RealPlace

section ComplexPlace

variable [MeasurableSpace ℂˣ] [BorelSpace ℂˣ]

/-- The normalized complex-place principal value uses the squared-modulus
cutoff and the factor two in the Tamagawa density. -/
theorem complexWeilTruncated_tendsto (f : ℂˣ → ℂ) (hf : HasCompactSupport f)
    (hs : ContDiffOn ℝ ∞ (archWeilZeroExtension f) ({0} : Set ℂ)ᶜ) :
    Tendsto (fun ε ↦ (2 * Real.pi)⁻¹ • (archWeilTruncated 2 complexArchMultiplicativeHaar f ε +
      (2 * Real.pi * Real.log ε : ℝ) • f 1) +
      (2 * (Real.eulerMascheroniConstant + Real.log (2 * Real.pi))) • f 1)
      (𝓝[>] 0) (𝓝 (-complexTraceLogFourierDistribution (archWeilShiftedTest 2 f hf hs))) := by
  let b := archWeilShiftedTest 2 f hf hs
  have h := ((archimedeanLogFourier_cutoff_corrected).2 b).neg
  apply h.congr'
  apply Eventually.of_forall
  intro ε
  have hI := archWeilTruncated_eq_additive 2 complexArchMultiplicativeHaar 2
    complexArchHaar_weighted_map f hf hs ε
  change -(-((2 : ℝ) * Real.pi)⁻¹ • complexLogCutoff b ε -
    (2 * (Real.eulerMascheroniConstant + Real.log (2 * Real.pi))) • b 0) =
      (2 * Real.pi)⁻¹ • (archWeilTruncated 2 complexArchMultiplicativeHaar f ε +
        (2 * Real.pi * Real.log ε : ℝ) • f 1) +
      (2 * (Real.eulerMascheroniConstant + Real.log (2 * Real.pi))) • f 1
  rw [hI]
  simp only [complexLogCutoff, b, archWeilShiftedTest_zero, neg_sub,
    smul_add, smul_smul, NNReal.smul_def, NNReal.coe_ofNat, mul_assoc]
  module

end ComplexPlace


end
end Masullo
