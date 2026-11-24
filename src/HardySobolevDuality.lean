import WeightedL2Coordinates
import WeightedTrace
import SobolevDuality
import L2Multipliers
import MellinBergman
import MellinStrip
import Mathlib.Analysis.Normed.Lp.SmoothApprox

open Filter Function MeasureTheory Set Topology
open scoped ContDiff ENNReal NNReal SchwartzMap

namespace Masullo

noncomputable section

local notation "realMeasure" => (volume : Measure ℝ)

private instance : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩

/-- The square root of the strip weight uses the left endpoint on
the negative logarithmic ray and the right endpoint on the positive ray. -/
def stripSobolevAmplitude (a b s x : ℝ) : ℝ :=
  Real.exp ((if x ≤ 0 then a else b) * x) * (1 + x ^ 2) ^ (s / 4)

theorem stripSobolevAmplitude_pos (a b s x : ℝ) : 0 < stripSobolevAmplitude a b s x :=
  mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos (by positivity) _)

theorem stripSobolevAmplitude_continuous (a b s : ℝ) : Continuous (stripSobolevAmplitude a b s) := by
  unfold stripSobolevAmplitude
  apply Continuous.mul
  · simpa only [ite_mul, apply_ite] using
      (continuous_if (p := fun x : ℝ => x ≤ 0) (f := fun x => Real.exp (a * x))
        (g := fun x => Real.exp (b * x)) (by
          intro x hx
          have hx0 : x = 0 := by
            change x ∈ frontier (Iic (0 : ℝ)) at hx
            simpa [frontier_Iic] using hx
          simp [hx0]) (by fun_prop) (by fun_prop))
  · exact (by fun_prop : Continuous (fun x : ℝ => 1 + x ^ 2)).rpow_const
      (fun x => Or.inl (by positivity))

theorem stripSobolevAmplitude_neg (a b s x : ℝ) :
    stripSobolevAmplitude (-a) (-b) (-s) x = (stripSobolevAmplitude a b s x)⁻¹ := by
  unfold stripSobolevAmplitude
  rw [mul_inv, ← Real.exp_neg, ← Real.rpow_neg (by positivity : (0 : ℝ) ≤ 1 + x ^ 2)]
  by_cases hx : x ≤ 0 <;> simp [hx, neg_div]

theorem stripSobolevAmplitude_sq {a b : ℝ} (hab : a ≤ b) (s x : ℝ) :
    stripSobolevAmplitude a b s x ^ 2 = hardySobolevWeight a b s x := by
  unfold stripSobolevAmplitude hardySobolevWeight
  rw [mul_pow, ← Real.exp_nat_mul, ← Real.rpow_natCast ((1 + x ^ 2) ^ (s / 4)) 2,
    ← Real.rpow_mul (by positivity : 0 ≤ 1 + x ^ 2)]
  have hs : (s / 4) * ((2 : ℕ) : ℝ) = s / 2 := by norm_num; ring
  rw [hs]
  by_cases hx : x ≤ 0
  · have h : Real.exp (2 * b * x) ≤ Real.exp (2 * a * x) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_right (by linarith) hx)
    rw [ite_eq_left hx, max_eq_left h]
    push_cast
    ring_nf
  · have h : Real.exp (2 * a * x) ≤ Real.exp (2 * b * x) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by linarith) (le_of_not_ge hx))
    rw [ite_eq_right hx, max_eq_right h]
    push_cast
    ring_nf

/-- The weighted L² space in logarithmic coordinates. -/
abbrev StripSobolev (a b s : ℝ) := Lp ℂ 2 (amplitudeMeasure realMeasure (stripSobolevAmplitude a b s))

abbrev stripMeasure (a b s : ℝ) :=
  amplitudeMeasure realMeasure (stripSobolevAmplitude a b s)

theorem stripMeasure_eq (a b s : ℝ) (hab : a ≤ b) :
    stripMeasure a b s = hardySobolevMeasure realMeasure id a b s := by
  unfold stripMeasure amplitudeMeasure hardySobolevMeasure
  simp only [id_eq, stripSobolevAmplitude_sq hab]

/-- Negating the amplitude parameters on the same two rays produces the reciprocal measure. -/
theorem stripReciprocalMeasure_eq (a b s : ℝ) (hab : a ≤ b) :
    stripMeasure (-a) (-b) (-s) = (realMeasure).withDensity
      (fun x => ENNReal.ofReal ((hardySobolevWeight a b s x)⁻¹)) := by
  unfold stripMeasure amplitudeMeasure
  congr 1
  funext x
  rw [stripSobolevAmplitude_neg, inv_pow, stripSobolevAmplitude_sq hab]


private abbrev stripCoordinates (a b s : ℝ) :=
  amplitudeL2Iso realMeasure (stripSobolevAmplitude a b s)
    (stripSobolevAmplitude_continuous a b s).measurable (stripSobolevAmplitude_pos a b s)

private def indicatorL2 (U : Set ℝ) (hU : MeasurableSet U) :
    Lp ℂ 2 realMeasure →L[ℂ] Lp ℂ 2 realMeasure :=
  (lpTwo_measurableCutoff (μ := realMeasure) hU).choose

private theorem indicatorL2_ae (U : Set ℝ) (hU : MeasurableSet U) (f : Lp ℂ 2 realMeasure) :
    (indicatorL2 U hU f : ℝ → ℂ) =ᵐ[realMeasure] U.indicator (f : ℝ → ℂ) :=
  ((lpTwo_measurableCutoff (μ := realMeasure) hU).choose_spec.2.2 f).2

/-- The zero-abscissa Sobolev amplitude times a Schwartz test in ordinary L². -/
def weightedSchwartzL2 (s : ℝ) : 𝓢(ℝ, ℂ) →L[ℂ] Lp ℂ 2 realMeasure :=
  (SchwartzMap.toLpCLM ℂ ℂ 2 realMeasure).comp
    (SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => ((1 + x ^ 2) ^ (s / 4) : ℝ) : ℝ → ℂ))

theorem weightedSchwartzL2_ae (s : ℝ) (f : 𝓢(ℝ, ℂ)) :
    (weightedSchwartzL2 s f : ℝ → ℂ) =ᵐ[realMeasure] fun x => (1 + x ^ 2) ^ (s / 4) • f x := by
  have h : (fun x : ℝ => (1 + x ^ 2) ^ (s / 4)).HasTemperateGrowth := by
    simpa only [Real.norm_eq_abs, sq_abs] using
      Function.hasTemperateGrowth_one_add_norm_sq_rpow ℝ (s / 4)
  unfold weightedSchwartzL2
  rw [ContinuousLinearMap.comp_apply, SchwartzMap.toLpCLM_apply]
  refine (SchwartzMap.coeFn_toLp _ _ _).trans (.of_forall fun x => ?_)
  have hc : (fun x : ℝ => (((1 + x ^ 2) ^ (s / 4) : ℝ) : ℂ)).HasTemperateGrowth :=
    Complex.hasTemperateGrowth_ofReal.comp h
  rw [SchwartzMap.smulLeftCLM_apply_apply hc]
  exact Complex.real_smul.symm

private def decayTwistCLM (J : Set ℝ) (a : J) :
    PositiveRealExponentialDecay J →L[ℂ] 𝓢(ℝ, ℂ) :=
  ⟨logExponentialDecayTwist J a,
    (continuous_apply a).comp (positiveRealExponentialDecay_isEmbedding J ⟨a, a.property⟩).continuous⟩

private def stripTestCoordinates (J : Set ℝ) (a b : J) (s : ℝ) :
    PositiveRealExponentialDecay J →L[ℂ] Lp ℂ 2 realMeasure :=
  (indicatorL2 (Iic 0) measurableSet_Iic).comp ((weightedSchwartzL2 s).comp (decayTwistCLM J a)) +
  (indicatorL2 (Ioi 0) measurableSet_Ioi).comp ((weightedSchwartzL2 s).comp (decayTwistCLM J b))

set_option backward.isDefEq.respectTransparency false in
private theorem stripTestCoordinates_ae (J : Set ℝ) (a b : J) (s : ℝ)
    (f : PositiveRealExponentialDecay J) :
    (stripTestCoordinates J a b s f : ℝ → ℂ) =ᵐ[realMeasure]
      fun x => stripSobolevAmplitude a b s x • f.val x := by
  let ga := weightedSchwartzL2 s (decayTwistCLM J a f)
  let gb := weightedSchwartzL2 s (decayTwistCLM J b f)
  let A := indicatorL2 (Iic 0) measurableSet_Iic ga
  let B := indicatorL2 (Ioi 0) measurableSet_Ioi gb
  change (↑(A + B) : ℝ → ℂ) =ᵐ[realMeasure] _
  filter_upwards [Lp.coeFn_add A B, indicatorL2_ae (Iic 0) measurableSet_Iic ga,
    indicatorL2_ae (Ioi 0) measurableSet_Ioi gb, weightedSchwartzL2_ae s (decayTwistCLM J a f),
    weightedSchwartzL2_ae s (decayTwistCLM J b f)] with x h hA hB ha hb
  rw [h, Pi.add_apply, hA, hB]
  have htwistA : decayTwistCLM J a f x = Real.exp ((a : ℝ) * x) • f.val x :=
    logExponentialDecayTwist_apply J a f x
  have htwistB : decayTwistCLM J b f x = Real.exp ((b : ℝ) * x) • f.val x :=
    logExponentialDecayTwist_apply J b f x
  change ga x = _ at ha
  change gb x = _ at hb
  by_cases hx : x ≤ 0
  · rw [indicator_of_mem (show x ∈ Iic (0 : ℝ) from hx),
      indicator_of_notMem (show x ∉ Ioi (0 : ℝ) from not_lt.mpr hx), add_zero, ha, htwistA, smul_smul,
      stripSobolevAmplitude, ite_eq_left hx, mul_comm]
  · rw [indicator_of_notMem (show x ∉ Iic (0 : ℝ) from hx),
      indicator_of_mem (show x ∈ Ioi (0 : ℝ) from lt_of_not_ge hx), zero_add, hb, htwistB, smul_smul,
      stripSobolevAmplitude, ite_eq_right hx, mul_comm]

/-- The inclusion of exponential-decay tests whose interval contains the
two abscissae is continuous in the actual weighted Hilbert norm. -/
def stripSobolevTest (J : Set ℝ) (a b : J) (s : ℝ) :
    PositiveRealExponentialDecay J →L[ℂ] StripSobolev a b s :=
  (stripCoordinates a b s).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (stripTestCoordinates J a b s)

theorem stripSobolevTest_ae (J : Set ℝ) (a b : J) (s : ℝ)
    (f : PositiveRealExponentialDecay J) :
    (stripSobolevTest J a b s f : ℝ → ℂ) =ᵐ[stripMeasure a b s] f.val := by
  let r := stripSobolevAmplitude (a : ℝ) (b : ℝ) s
  change ((stripCoordinates a b s).symm (stripTestCoordinates J a b s f) : ℝ → ℂ) =ᵐ[_] _
  filter_upwards [amplitudeL2Iso_symm_ae realMeasure r (stripSobolevAmplitude_continuous a b s).measurable
      (stripSobolevAmplitude_pos a b s) (stripTestCoordinates J a b s f),
    (amplitudeMeasure_absolutelyContinuous realMeasure r).ae_le (stripTestCoordinates_ae J a b s f)]
    with x hx hy
  rw [hx, hy, smul_smul, inv_mul_cancel₀ (stripSobolevAmplitude_pos a b s x).ne', one_smul]



/-- On a compact base, the supremum norm is the Hilbert norm of the test inclusion. -/
theorem stripSobolevTest_norm (J : Set ℝ) (a b : J) (hab : (a : ℝ) ≤ b) (s : ℝ)
    (f : PositiveRealExponentialDecay J) :
    (hardySobolevIntervalENorm realMeasure id (Icc (a : ℝ) b) s f.val).toReal =
      ‖stripSobolevTest J a b s f‖ := by
  rw [hardySobolevIntervalENorm_Icc _ _ hab, ← stripMeasure_eq _ _ _ hab,
    Lp.norm_def, eLpNorm_congr_ae (stripSobolevTest_ae J a b s f)]

/-- The positive strip norm is the square root of its weighted energy. -/
theorem stripSobolevTest_energy (J : Set ℝ) (a b : J) (hab : (a : ℝ) ≤ b) (s : ℝ)
    (f : PositiveRealExponentialDecay J) :
    let energy := fun x : ℝ => ‖f.val x‖ ^ 2 * hardySobolevWeight a b s x
    Integrable energy ∧
      hardySobolevIntervalENorm realMeasure id (Icc (a : ℝ) b) s f.val =
        ENNReal.ofReal (Real.sqrt (∫ x, energy x)) := by
  let U := stripCoordinates (a : ℝ) b s
  let u := stripSobolevTest J a b s f
  let v := stripTestCoordinates J a b s f
  have huv : U u = v := U.apply_symm_apply v
  have he : (fun x : ℝ => ‖v x‖ ^ 2) =ᵐ[realMeasure]
      fun x : ℝ => ‖f.val x‖ ^ 2 * hardySobolevWeight a b s x := by
    filter_upwards [stripTestCoordinates_ae J a b s f] with x hx
    change v x = _ at hx
    simp only [hx, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, stripSobolevAmplitude_sq hab]
    exact mul_comm _ _
  have hv := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable v)).mp (Lp.memLp v)
  refine ⟨hv.congr he, ?_⟩
  rw [hardySobolevIntervalENorm_Icc _ _ hab, ← stripMeasure_eq _ _ _ hab,
    ← eLpNorm_congr_ae (stripSobolevTest_ae J a b s f)]
  change eLpNorm u 2 (stripMeasure a b s) = _
  rw [← ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top u), ← Lp.norm_def, ← U.norm_map u, huv,
    Lp.norm_def, toReal_eLpNorm (Lp.aestronglyMeasurable v), lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num)
      (Lp.aestronglyMeasurable v)]
  norm_num [Real.sqrt_eq_rpow, Real.rpow_natCast, inv_eq_one_div]
  rw [integral_congr_ae he]

private instance stripMeasureFinite (a b s : ℝ) :
    IsFiniteMeasureOnCompacts (stripMeasure a b s) := by
  refine ⟨fun K hK => ?_⟩
  obtain ⟨C, hC⟩ := (hK.image ((stripSobolevAmplitude_continuous a b s).pow 2)).bddAbove
  change amplitudeMeasure realMeasure (stripSobolevAmplitude a b s) K < (∞ : ℝ≥0∞)
  rw [amplitudeMeasure, withDensity_apply _ hK.measurableSet]
  calc
    _ ≤ ∫⁻ _ in K, ENNReal.ofReal C := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
      exact ENNReal.ofReal_le_ofReal (hC (mem_image_of_mem _ hx))
    _ < (∞ : ℝ≥0∞) := by
      rw [lintegral_const, Measure.restrict_apply_univ]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK.measure_lt_top

/-- Compact logarithmic intervals have finite weighted strip measure. -/
theorem stripMeasure_compact_lt_top (a b s : ℝ) {A : Set ℝ} (hA : IsCompact A) :
    stripMeasure a b s A < ⊤ :=
  hA.measure_lt_top

/-- Compactly supported smooth tests lie in the exponential test space
and are dense in the weighted Hilbert space. -/
theorem stripSobolevTest_denseRange (J : Set ℝ) (a b : J) (s : ℝ) :
    DenseRange (stripSobolevTest J a b s) := by
  refine Dense.mono ?_ (Lp.dense_hasCompactSupport_contDiff (μ := stripMeasure a b s)
    (F := ℂ) (p := 2) (by norm_num))
  rintro u ⟨g, hug, hgc, hg⟩
  let f : PositiveRealExponentialDecay J :=
    ⟨g, mem_logExponentialDecaySubmodule_of_hasCompactSupport J hgc hg⟩
  exact ⟨f, Lp.ext ((stripSobolevTest_ae J a b s f).trans hug.symm)⟩

/-- Precomposition by a linear isometry transports the strong dual isometrically. -/
def precomposeDualIso {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace ℂ E] [NormedSpace ℂ F] (e : E ≃ₗᵢ[ℂ] F) :
    StrongDual ℂ F ≃ₗᵢ[ℂ] StrongDual ℂ E where
  toFun f := f.comp e.toContinuousLinearEquiv.toContinuousLinearMap
  invFun f := f.comp e.symm.toContinuousLinearEquiv.toContinuousLinearMap
  left_inv _ := by ext x; simp
  right_inv _ := by ext x; simp
  map_add' _ _ := by ext x; rfl
  map_smul' _ _ := by ext x; rfl
  norm_map' f := ContinuousLinearMap.opNorm_comp_linearIsometryEquiv f e

/-- The reciprocal-weight space represents the strong dual of the
positive-weight Hilbert space. Both weights use the same endpoint split. -/
def stripSobolevDuality (a b s : ℝ) :
    StripSobolev (-a) (-b) (-s) ≃ₗᵢ[ℂ] StrongDual ℂ (StripSobolev a b s) :=
  (stripCoordinates (-a) (-b) (-s)).trans
    ((sobolevBilinearDual realMeasure).trans (precomposeDualIso (stripCoordinates a b s)))

theorem stripSobolevDuality_integrable (a b s : ℝ) (f : StripSobolev a b s)
    (g : StripSobolev (-a) (-b) (-s)) :
    Integrable (fun x : ℝ => f x * g x) realMeasure := by
  let F := stripCoordinates a b s f
  let G := stripCoordinates (-a) (-b) (-s) g
  have hg : Integrable (fun x : ℝ => F x * G x) realMeasure :=
    MemLp.integrable_mul (p := 2) (q := 2) (Lp.memLp F) (Lp.memLp G)
  apply hg.congr
  filter_upwards [amplitudeL2Iso_ae realMeasure _ _ _ f, amplitudeL2Iso_ae realMeasure _ _ _ g] with x hF hG
  change F x = _ at hF
  change G x = _ at hG
  rw [hF, hG, stripSobolevAmplitude_neg, Complex.real_smul, Complex.real_smul,
    mul_mul_mul_comm, ← Complex.ofReal_mul,
    mul_inv_cancel₀ (stripSobolevAmplitude_pos a b s x).ne', Complex.ofReal_one, one_mul]

theorem stripSobolevDuality_apply (a b s : ℝ) (f : StripSobolev a b s)
    (g : StripSobolev (-a) (-b) (-s)) :
    stripSobolevDuality a b s g f = ∫ x : ℝ, f x * g x := by
  change sobolevBilinearDual realMeasure (stripCoordinates (-a) (-b) (-s) g)
    (stripCoordinates a b s f) = _
  rw [sobolevBilinearDual_apply]
  apply integral_congr_ae
  filter_upwards [amplitudeL2Iso_ae realMeasure _ _ _ f, amplitudeL2Iso_ae realMeasure _ _ _ g] with x hF hG
  rw [hF, hG, stripSobolevAmplitude_neg, Complex.real_smul, Complex.real_smul,
    mul_mul_mul_comm, ← Complex.ofReal_mul,
    mul_inv_cancel₀ (stripSobolevAmplitude_pos a b s x).ne', Complex.ofReal_one, one_mul]

/-- A dual represented in the positive-weight Hilbert model by a
bilinear Riesz vector ψ corresponds to wψ in the reciprocal-weight space. -/
theorem stripSobolevDuality_symm_ae {a b : ℝ} (hab : a ≤ b) (s : ℝ)
    (ψ : StripSobolev a b s) :
    ((stripSobolevDuality a b s).symm (sobolevBilinearDual (stripMeasure a b s) ψ) : ℝ → ℂ)
      =ᵐ[realMeasure] fun x => hardySobolevWeight a b s x • ψ x := by
  let U := stripCoordinates a b s
  let V := stripCoordinates (-a) (-b) (-s)
  let f := (stripSobolevDuality a b s).symm (sobolevBilinearDual (stripMeasure a b s) ψ)
  have hnorm : ∀ p : StripSobolev a b s,
      sobolevBilinearDual (stripMeasure a b s) ψ p =
        sobolevBilinearDual realMeasure (U ψ) (U p) := by
    intro p
    rw [sobolevBilinearDual_apply, sobolevBilinearDual_apply]
    let ρ : ℝ → ℝ≥0 := fun x => Real.toNNReal (stripSobolevAmplitude a b s x ^ 2)
    have hρ : Measurable ρ :=
      ((stripSobolevAmplitude_continuous a b s).measurable.pow_const 2).real_toNNReal
    calc
      _ = ∫ x, ρ x • (p x * ψ x) ∂realMeasure := by
        exact integral_withDensity_eq_integral_smul hρ (fun x => p x * ψ x)
      _ = _ := by
        apply integral_congr_ae
        have h (q : StripSobolev a b s) :
            (U q : ℝ → ℂ) =ᵐ[realMeasure] fun x => stripSobolevAmplitude a b s x • q x :=
          amplitudeL2Iso_ae realMeasure _ _ _ q
        filter_upwards [h p, h ψ] with x hp hψ
        rw [hp, hψ, NNReal.smul_def, show (ρ x : ℝ) = stripSobolevAmplitude a b s x ^ 2 from
          Real.coe_toNNReal _ (sq_nonneg _), Complex.real_smul, Complex.real_smul,
          Complex.real_smul, mul_mul_mul_comm, ← Complex.ofReal_mul, pow_two]
  have hVU : V f = U ψ := by
    apply (sobolevBilinearDual realMeasure).injective
    ext q
    obtain ⟨p, rfl⟩ := U.surjective q
    exact (congrArg (fun l : StrongDual ℂ (StripSobolev a b s) => l p)
      ((stripSobolevDuality a b s).apply_symm_apply _)).trans (hnorm p)
  have hf : f = V.symm (U ψ) := V.injective (by rw [hVU, V.apply_symm_apply])
  change (f : ℝ → ℂ) =ᵐ[realMeasure] _
  rw [hf]
  filter_upwards [(absolutelyContinuous_amplitudeMeasure realMeasure _
      (stripSobolevAmplitude_continuous (-a) (-b) (-s)).measurable
      (stripSobolevAmplitude_pos (-a) (-b) (-s))).ae_le
        (amplitudeL2Iso_symm_ae realMeasure _ _ _ (U ψ)),
    amplitudeL2Iso_ae realMeasure _ _ _ ψ] with x h₁ h₂
  rw [h₁, h₂, stripSobolevAmplitude_neg, inv_inv, smul_smul, ← pow_two,
    stripSobolevAmplitude_sq hab]

/-- Integration is jointly continuous on the two weighted Hilbert completions. -/
theorem stripSobolev_pairing_continuous (a b s : ℝ) :
    Continuous (fun p : StripSobolev a b s × StripSobolev (-a) (-b) (-s) =>
      ∫ x : ℝ, p.1 x * p.2 x) := by
  have h : Continuous (fun p : StripSobolev a b s × StripSobolev (-a) (-b) (-s) =>
      stripSobolevDuality a b s p.2 p.1) :=
    ((stripSobolevDuality a b s).continuous.comp continuous_snd).clm_apply continuous_fst
  exact h.congr fun p => stripSobolevDuality_apply a b s p.1 p.2

/-- The unweighted pairing is absolutely convergent with respect to dt/t. -/
theorem stripSobolev_log_pairing_convergent (a b s : ℝ) (f : StripSobolev a b s)
    (g : StripSobolev (-a) (-b) (-s)) :
    MellinConvergent (fun t => f (Real.log t) * g (Real.log t)) 0 := by
  apply mellinConvergent_of_integrable_logWeight (fun x => f x * g x) 0
  simpa using stripSobolevDuality_integrable a b s f g

/-- Returning from logarithmic coordinates gives the manuscript's integral against dt/t. -/
theorem stripSobolev_log_pairing (f g : ℝ → ℂ) :
    mellin (fun t => f (Real.log t) * g (Real.log t)) 0 = ∫ x : ℝ, f x * g x := by
  rw [mellin_eq_log_integral]
  simp only [zero_mul, Complex.exp_zero, one_mul, Real.log_exp]

/-- The integral pairing on tests is jointly continuous for intervals
containing the respective original and reflected abscissae. -/
theorem stripSobolev_test_pairing_continuous {a b s : ℝ} {J K : Set ℝ}
    (ha : a ∈ J) (hb : b ∈ J) (hna : -a ∈ K) (hnb : -b ∈ K) :
    Continuous (fun p : PositiveRealExponentialDecay J × PositiveRealExponentialDecay K =>
      ∫ x : ℝ, p.1.val x * p.2.val x) := by
  let A := stripSobolevTest J ⟨a, ha⟩ ⟨b, hb⟩ s
  let B := stripSobolevTest K ⟨-a, hna⟩ ⟨-b, hnb⟩ (-s)
  have hc : Continuous (fun p : PositiveRealExponentialDecay J × PositiveRealExponentialDecay K =>
      stripSobolevDuality a b s (B p.2) (A p.1)) :=
    ((stripSobolevDuality a b s).continuous.comp (B.continuous.comp continuous_snd)).clm_apply
      (A.continuous.comp continuous_fst)
  refine hc.congr fun p => ?_
  rw [stripSobolevDuality_apply]
  apply integral_congr_ae
  filter_upwards [(absolutelyContinuous_amplitudeMeasure realMeasure _
      (stripSobolevAmplitude_continuous a b s).measurable
      (stripSobolevAmplitude_pos a b s)).ae_le (stripSobolevTest_ae J ⟨a, ha⟩ ⟨b, hb⟩ s p.1),
    (absolutelyContinuous_amplitudeMeasure realMeasure _
      (stripSobolevAmplitude_continuous (-a) (-b) (-s)).measurable
      (stripSobolevAmplitude_pos (-a) (-b) (-s))).ae_le
        (stripSobolevTest_ae K ⟨-a, hna⟩ ⟨-b, hnb⟩ (-s) p.2)] with x h₁ h₂
  change A p.1 x = _ at h₁
  change B p.2 x = _ at h₂
  rw [h₁, h₂]

end
end Masullo
