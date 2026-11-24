import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

open Filter Function MeasureTheory MeasureTheory.Measure Set Topology

namespace Masullo

private theorem integrable_logSobolevWeight_real {s : ℝ} (hs : 0 ≤ s) :
    Integrable (fun x : ℝ => (1 + ‖x‖ ^ 2) ^ (-s / 2)) ↔ 1 < s := by
  constructor
  · intro h
    have hcomp : IntegrableOn (fun x : ℝ => (2 : ℝ) ^ (-s / 2) * x ^ (-s)) (Ioi 1) := by
      apply (h.integrableOn (s := Ioi 1)).mono'
      · refine (Measurable.aestronglyMeasurable ?_)
        fun_prop
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
        have hx : 1 < x := hx
        have hpos : 0 < x := zero_lt_one.trans hx
        have hsq : 1 + x ^ 2 ≤ 2 * x ^ 2 := by nlinarith [sq_nonneg (x - 1)]
        rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg hpos.le]
        calc
          _ = (2 * x ^ 2) ^ (-s / 2) := by
            rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_natCast,
              ← Real.rpow_mul hpos.le]
            congr 1
            norm_num [mul_comm]
            ring_nf
          _ ≤ _ := Real.rpow_le_rpow_of_nonpos (by positivity) hsq (by linarith)
    have he := hcomp.const_mul ((2 : ℝ) ^ (-s / 2))⁻¹
    have hp : IntegrableOn (fun x : ℝ => x ^ (-s)) (Ioi 1) := by
      have hpos : 0 < (2 : ℝ) ^ (-s / 2) := Real.rpow_pos_of_pos (by norm_num) _
      simp only [IntegrableOn] at he ⊢
      simpa only [← mul_assoc, inv_mul_cancel₀ hpos.ne', one_mul] using he
    linarith [(integrableOn_Ioi_rpow_iff (show (0 : ℝ) < 1 by norm_num)).mp hp]
  · intro h
    exact integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume) (by simpa using h)

private theorem integrable_comp_logNorm_iff {G : Type*} [AddCommGroup G]
    [TopologicalSpace G] [IsTopologicalAddGroup G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [IsAddHaarMeasure μ]
    (logNorm : G →+ ℝ) (hc : Continuous logNorm) (hsurj : Surjective logNorm)
    (hproper : Tendsto logNorm (cocompact G) (cocompact ℝ)) {w : ℝ → ℝ} (hw : Measurable w) :
    Integrable (w ∘ logNorm) μ ↔ Integrable w volume := by
  let ν := μ.map logNorm
  letI : IsAddHaarMeasure ν := isAddHaarMeasure_map μ logNorm hc hsurj hproper
  have hν : ν = addHaarScalarFactor ν volume • volume :=
    isAddLeftInvariant_eq_smul ν volume
  have hνpos := (addHaarScalarFactor_pos_of_isAddHaarMeasure ν volume).ne'
  calc
    _ ↔ Integrable w ν := (integrable_map_measure hw.aestronglyMeasurable hc.measurable.aemeasurable).symm
    _ ↔ Integrable w volume := by
      rw [hν]
      exact integrable_smul_measure (by exact_mod_cast hνpos) ENNReal.coe_ne_top

/-- The logarithm of the modulus of an ℝ₊-modulated group is a proper
surjective additive homomorphism in additive notation. The pushforward
of Haar measure gives the exact threshold in Lemma 9.1.2.4. -/
theorem integrable_logSobolevWeight_iff {G : Type*} [AddCommGroup G]
    [TopologicalSpace G] [IsTopologicalAddGroup G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [IsAddHaarMeasure μ]
    (logNorm : G →+ ℝ) (hc : Continuous logNorm) (hsurj : Surjective logNorm)
    (hproper : Tendsto logNorm (cocompact G) (cocompact ℝ))
    {s : ℝ} (hs : 0 ≤ s) :
    Integrable (fun x : G => (1 + ‖logNorm x‖ ^ 2) ^ (-s / 2)) μ ↔ 1 < s :=
  (integrable_comp_logNorm_iff μ logNorm hc hsurj hproper (by fun_prop)).trans
    (integrable_logSobolevWeight_real hs)

/-- Sharp integrability of the squared logarithmic moment on the real line. -/
theorem integrable_logSobolevMoment_real {s : ℝ} (hs : 0 ≤ s) (m : ℕ) :
    Integrable (fun x : ℝ => ‖x‖ ^ (2 * m) * (1 + ‖x‖ ^ 2) ^ (-s / 2)) volume ↔
      1 < s - 2 * (m : ℝ) := by
  let c : ℝ := (2 : ℝ) ^ (-s / 2)
  have hc : 0 < c := Real.rpow_pos_of_pos (by norm_num) _
  constructor
  · intro h
    have hlower : IntegrableOn (fun x : ℝ => c * x ^ (2 * (m : ℝ) - s)) (Ioi 1) := by
      apply (h.integrableOn (s := Ioi 1)).mono' (Measurable.aestronglyMeasurable (by fun_prop))
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hx' : 1 < x := hx
      have hpos : 0 < x := zero_lt_one.trans hx
      have hsq : 1 + x ^ 2 ≤ 2 * x ^ 2 := by nlinarith [sq_nonneg (x - 1)]
      rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg hpos.le]
      calc
        _ = x ^ (2 * m) * (2 * x ^ 2) ^ (-s / 2) := by
          rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_natCast x 2,
            ← Real.rpow_mul hpos.le, ← Real.rpow_natCast x (2 * m), mul_left_comm,
            ← Real.rpow_add hpos]
          push_cast
          congr 2
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos (by positivity) hsq (by linarith)) (by positivity)
    have htail := hlower.const_mul c⁻¹
    have htail' : IntegrableOn (fun x : ℝ => x ^ (2 * (m : ℝ) - s)) (Ioi 1) := by
      simp only [IntegrableOn]
      simpa only [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul] using htail
    linarith [(integrableOn_Ioi_rpow_iff (show (0 : ℝ) < 1 by norm_num)).mp htail']
  · intro h
    have hmajor := (integrable_logSobolevWeight_real (s := s - 2 * (m : ℝ)) (by linarith)).mpr h
    apply hmajor.mono' (Measurable.aestronglyMeasurable (by fun_prop))
    filter_upwards with x
    rw [Real.norm_of_nonneg (by positivity), pow_mul]
    let q := 1 + ‖x‖ ^ 2
    have hq : 0 < q := by dsimp [q]; positivity
    calc
      _ ≤ q ^ m * q ^ (-s / 2) := by
        gcongr
        dsimp [q]
        exact le_add_of_nonneg_left zero_le_one
      _ = q ^ (-(s - 2 * (m : ℝ)) / 2) := by
        rw [← Real.rpow_natCast, ← Real.rpow_add hq]
        congr 1
        ring

/-- The sharp moment threshold in Proposition 9.1.2.5. -/
theorem integrable_logSobolevMoment_iff {G : Type*} [AddCommGroup G]
    [TopologicalSpace G] [IsTopologicalAddGroup G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [IsAddHaarMeasure μ] (logNorm : G →+ ℝ) (hc : Continuous logNorm)
    (hsurj : Surjective logNorm) (hproper : Tendsto logNorm (cocompact G) (cocompact ℝ))
    {s : ℝ} (hs : 0 ≤ s) (m : ℕ) :
    Integrable (fun x : G => ‖logNorm x‖ ^ (2 * m) * (1 + ‖logNorm x‖ ^ 2) ^ (-s / 2)) μ ↔
      (m : ℝ) < (s - 1) / 2 := by
  have h := (integrable_comp_logNorm_iff μ logNorm hc hsurj hproper (by fun_prop)).trans
    (integrable_logSobolevMoment_real hs m)
  exact h.trans ⟨fun h' => by linarith, fun h' => by linarith⟩

/-- Membership of the oscillatory logarithmic moments in the negative
weighted L² space, in the reciprocal-weight coordinate. -/
theorem logSobolev_characterMoment_memLp_iff {G : Type*} [AddCommGroup G]
    [TopologicalSpace G] [IsTopologicalAddGroup G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [IsAddHaarMeasure μ] (logNorm : G →+ ℝ) (hc : Continuous logNorm)
    (hsurj : Surjective logNorm) (hproper : Tendsto logNorm (cocompact G) (cocompact ℝ))
    {s : ℝ} (hs : 0 ≤ s) (t : ℝ) (m : ℕ) :
    MemLp (fun x : G => ((1 + ‖logNorm x‖ ^ 2) ^ (-s / 4) : ℝ) *
      Complex.exp (Complex.ofReal (t * logNorm x) * Complex.I) * (logNorm x : ℂ) ^ m) 2 μ ↔
      (m : ℝ) < (s - 1) / 2 := by
  let q (x : G) : ℝ := 1 + ‖logNorm x‖ ^ 2
  let f (x : G) : ℂ := (q x ^ (-s / 4) : ℝ) *
    Complex.exp (Complex.ofReal (t * logNorm x) * Complex.I) * (logNorm x : ℂ) ^ m
  have hf : Continuous f := by
    have hq : Continuous q := continuous_const.add (hc.norm.pow 2)
    have hp : Continuous (fun x => q x ^ (-s / 4)) := by
      apply continuous_iff_continuousAt.mpr
      intro x
      exact hq.continuousAt.rpow_const (Or.inl (by dsimp [q]; positivity))
    have he : Continuous (fun x => Complex.exp (Complex.ofReal (t * logNorm x) * Complex.I)) := by
      exact Complex.continuous_exp.comp
        ((Complex.continuous_ofReal.comp (continuous_const.mul hc)).mul continuous_const)
    exact ((Complex.continuous_ofReal.comp hp).mul he).mul ((Complex.continuous_ofReal.comp hc).pow m)
  have hmag (x : G) : ‖f x‖ ^ 2 = ‖logNorm x‖ ^ (2 * m) * q x ^ (-s / 2) := by
    have hphase : ‖Complex.exp (Complex.ofReal (t * logNorm x) * Complex.I)‖ = 1 := by
      simp [Complex.norm_exp, Complex.mul_re]
    have hwt : (q x ^ (-s / 4)) ^ (2 : ℕ) = q x ^ (-s / 2) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by dsimp [q]; positivity)]
      congr 1
      ring
    dsimp [f]
    rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (by positivity),
      hphase, mul_one, Complex.norm_real, mul_pow, hwt, ← pow_mul, mul_comm m 2, mul_comm,
      Real.norm_eq_abs]
  change MemLp f 2 μ ↔ _
  rw [memLp_two_iff_integrable_sq_norm hf.measurable.aestronglyMeasurable]
  simpa only [hmag] using integrable_logSobolevMoment_iff μ logNorm hc hsurj hproper hs m

section HolderMultiplication

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {w : X → ℂ}

private theorem lpTwoProductMem (hw : MemLp w 2 μ) (u : Lp ℂ 2 μ) :
    MemLp (fun x => w x * u x) 1 μ :=
  MemLp.mul' (p := 2) (q := 2) (r := 1) (Lp.memLp u) hw

private noncomputable def lpTwoProduct (hw : MemLp w 2 μ) (u : Lp ℂ 2 μ) : Lp ℂ 1 μ :=
  (lpTwoProductMem hw u).toLp _

private theorem lpTwoProduct_ae (hw : MemLp w 2 μ) (u : Lp ℂ 2 μ) :
    (lpTwoProduct hw u : X → ℂ) =ᵐ[μ] fun x => w x * u x :=
  (lpTwoProductMem hw u).coeFn_toLp

set_option maxHeartbeats 1000000 in
private theorem lpTwoProduct_le (hw : MemLp w 2 μ) (u : Lp ℂ 2 μ) :
    ‖lpTwoProduct hw u‖ ≤ ‖hw.toLp w‖ * ‖u‖ := by
  have hu : MemLp (u : X → ℂ) 2 μ := Lp.memLp u
  have h : eLpNorm (fun x => w x * u x) 1 μ ≤ eLpNorm w 2 μ * eLpNorm (u : X → ℂ) 2 μ := by
    have hS := eLpNorm_smul_le_mul_eLpNorm (p := 2) (q := 2) (r := 1)
      hu.aestronglyMeasurable hw.aestronglyMeasurable
    simpa only [Pi.smul_apply, smul_eq_mul, Pi.mul_def] using hS
  calc
    ‖lpTwoProduct hw u‖ = (eLpNorm (fun x => w x * u x) 1 μ).toReal :=
      Lp.norm_toLp _ (lpTwoProductMem hw u)
    _ ≤ (eLpNorm w 2 μ * eLpNorm (u : X → ℂ) 2 μ).toReal :=
      ENNReal.toReal_mono (ENNReal.mul_ne_top hw.eLpNorm_ne_top hu.eLpNorm_ne_top) h
    _ = ‖hw.toLp w‖ * ‖u‖ :=
      ENNReal.toReal_mul.trans (congrArg₂ (· * ·) (Lp.norm_toLp w hw).symm (Lp.norm_def u).symm)

private noncomputable def lpTwo_mul_toL1 (hw : MemLp w 2 μ) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 1 μ :=
  let v := lpTwoProduct hw
  let T : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 1 μ :=
    { toFun := v
      map_add' := fun u z => Lp.ext (by
        filter_upwards [lpTwoProduct_ae hw (u + z), lpTwoProduct_ae hw u, lpTwoProduct_ae hw z,
          Lp.coeFn_add u z, Lp.coeFn_add (v u) (v z)] with x h₀ h₁ h₂ h₃ h₄
        change v (u + z) x = (v u + v z) x
        simp only [Pi.add_apply] at h₃ h₄
        rw [h₀, h₃, h₄, h₁, h₂, mul_add])
      map_smul' := fun c u => Lp.ext (by
        filter_upwards [lpTwoProduct_ae hw (c • u), lpTwoProduct_ae hw u,
          Lp.coeFn_smul c u, Lp.coeFn_smul c (v u)] with x h₀ h₁ h₂ h₃
        change v (c • u) x = (c • v u) x
        simp only [Pi.smul_apply, smul_eq_mul] at h₂ h₃
        rw [h₀, h₂, h₃, h₁]
        ring) }
  T.mkContinuous ‖hw.toLp w‖ (lpTwoProduct_le hw)

end HolderMultiplication

set_option maxHeartbeats 1000000 in
/-- Proposition 9.1.2.6. In the weighted-L² coordinate
`u(x) = (1 + ‖logNorm x‖²) ^ (s/4) * f(x)`, multiplication by the
reciprocal weight gives the continuous inclusion into L¹. The norm bound
also holds for every measurable representative with the stated weight. -/
theorem logSobolev_continuous_inclusion_L1 {G : Type*} [AddCommGroup G]
    [TopologicalSpace G] [IsTopologicalAddGroup G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [IsAddHaarMeasure μ]
    (logNorm : G →+ ℝ) (hc : Continuous logNorm) (hsurj : Surjective logNorm)
    (hproper : Tendsto logNorm (cocompact G) (cocompact ℝ)) {s : ℝ} (hs : 1 < s) :
    let q (x : G) : ℝ := 1 + ‖logNorm x‖ ^ 2
    ∃ (C : ℝ) (I : Lp ℂ 2 μ →L[ℂ] Lp ℂ 1 μ), 0 < C ∧
      (∀ u : Lp ℂ 2 μ, ‖I u‖ ≤ C * ‖u‖) ∧
      (∀ u : Lp ℂ 2 μ, (I u : G → ℂ) =ᵐ[μ] fun x => ((q x ^ (-s / 4) : ℝ) : ℂ) * u x) ∧
      (∀ (f : G → ℂ) (hf : MemLp (fun x => ((q x ^ (s / 4) : ℝ) : ℂ) * f x) 2 μ),
        Integrable f μ ∧ (∫ x, ‖f x‖ ∂μ) ≤ C * ‖hf.toLp _‖) := by
  let q (x : G) : ℝ := 1 + ‖logNorm x‖ ^ 2
  let w (x : G) : ℂ := (q x ^ (-s / 4) : ℝ)
  have hwSq (x : G) : ‖w x‖ ^ 2 = q x ^ (-s / 2) := by
    dsimp [w]
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity), ← Real.rpow_natCast,
      ← Real.rpow_mul (by dsimp [q]; positivity)]
    congr 1
    ring
  have hw : MemLp w 2 μ := by
    have hq : Continuous q := continuous_const.add (hc.norm.pow 2)
    have hpow : Continuous (fun x : G => q x ^ (-s / 4)) := by
      apply continuous_iff_continuousAt.mpr
      intro x
      exact hq.continuousAt.rpow_const (Or.inl (by dsimp [q]; positivity))
    have hwm : Measurable w := Complex.continuous_ofReal.measurable.comp hpow.measurable
    apply (memLp_two_iff_integrable_sq_norm hwm.aestronglyMeasurable).mpr
    simpa only [hwSq] using
      (integrable_logSobolevWeight_iff μ logNorm hc hsurj hproper (by linarith)).mpr hs
  let I := lpTwo_mul_toL1 hw
  let C := max 1 ‖I‖
  have hC : 0 < C := zero_lt_one.trans_le (le_max_left _ _)
  have hInorm (u : Lp ℂ 2 μ) : ‖I u‖ ≤ C * ‖u‖ :=
    (I.le_opNorm u).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))
  have hI (u : Lp ℂ 2 μ) : (I u : G → ℂ) =ᵐ[μ] fun x => w x * u x :=
    lpTwoProduct_ae hw u
  refine ⟨C, I, hC, hInorm, hI, fun f hf => ?_⟩
  have hcancel (x : G) : w x * (((q x ^ (s / 4) : ℝ) : ℂ) * f x) = f x := by
    dsimp [w]
    rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.rpow_add (by dsimp [q]; positivity),
      show -s / 4 + s / 4 = 0 by ring, Real.rpow_zero, Complex.ofReal_one, one_mul]
  have hweighted : MemLp (fun x => w x * (((q x ^ (s / 4) : ℝ) : ℂ) * f x)) 1 μ :=
    MemLp.mul' (p := 2) (q := 2) (r := 1) hf hw
  have hmem : MemLp f 1 μ := (memLp_congr_ae (.of_forall hcancel)).mp hweighted
  have hEq : I (hf.toLp _) = hmem.toLp f := by
    apply Lp.ext
    filter_upwards [hI (hf.toLp _), hf.coeFn_toLp, hmem.coeFn_toLp] with x h₁ h₂ h₃
    rw [h₁, h₂, h₃, hcancel]
  refine ⟨memLp_one_iff_integrable.mp hmem, ?_⟩
  have hnorm : ‖hmem.toLp f‖ = ∫ x, ‖f x‖ ∂μ := by
    rw [Lp.norm_toLp, toReal_eLpNorm hmem.aestronglyMeasurable,
      lpNorm_one_eq_integral_norm hmem.aestronglyMeasurable]
  rw [← hnorm, ← hEq]
  exact hInorm (hf.toLp _)

end Masullo
