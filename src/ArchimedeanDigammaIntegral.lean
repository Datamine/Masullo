module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
public import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Gauss's integral for the digamma difference

The difference of two beta integrals gives the digamma difference when one parameter
tends to zero. In exponential coordinates the kernel admits an integrable majorant
after multiplication by a vertical weight with finite first absolute moment.

Adapted from Neal Patel (MIT) via the original Masullo project (Apache-2.0).
See External/PROVENANCE.md and the retained licence notices.
-/

@[expose] public noncomputable section

open Complex Filter MeasureTheory Set
open scoped Topology

namespace Masullo

private noncomputable def digammaKernel (z : ℂ) (t : ℝ) : ℂ :=
  ((t : ℂ) ^ (z - 1) - 1) / (1 - (t : ℂ))

private theorem integrableOn_digammaKernel {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn (digammaKernel z) (Ioo 0 1) := by
  have hpower : IntervalIntegrable (fun t : ℝ ↦ (t : ℂ) ^ (z - 1)) volume 0 (1 / 2) :=
    intervalIntegral.intervalIntegrable_cpow' (by simpa using sub_lt_sub_right hz 1)
  have hleft : IntervalIntegrable (digammaKernel z) volume 0 (1 / 2) := by
    unfold digammaKernel
    simp only [div_eq_mul_inv]
    apply (hpower.sub intervalIntegrable_const).mul_continuousOn
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    refine (show Continuous (fun t : ℝ ↦ (1 : ℂ) - (t : ℂ)) by fun_prop).continuousOn.inv₀ ?_
    intro t ht
    rw [sub_ne_zero, ← Complex.ofReal_one, Ne, Complex.ofReal_inj]
    linarith [ht.2]
  let f (t : ℝ) := (t : ℂ) ^ (z - 1)
  have hf (t : ℝ) (ht : 0 < t) : DifferentiableAt ℝ f t := by
    by_cases h : z - 1 = 0
    · simp [f, h]
    · exact differentiableAt_id.ofReal_cpow_const ht.ne' h
  have hright : IntervalIntegrable (digammaKernel z) volume (1 / 2) 1 := by
    have hcont : ContinuousOn (fun t ↦ -dslope f 1 t) (Icc (1 / 2 : ℝ) 1) := by
      apply ContinuousOn.neg
      intro t ht
      rcases eq_or_ne t 1 with rfl | ht1
      · exact (continuousAt_dslope_same.mpr (hf 1 zero_lt_one)).continuousWithinAt
      · exact ((continuousAt_dslope_of_ne ht1).mpr
          (hf t (lt_of_lt_of_le (by norm_num) ht.1)).continuousAt).continuousWithinAt
    have hi : IntervalIntegrable (fun t ↦ -dslope f 1 t) volume (1 / 2) 1 :=
      hcont.intervalIntegrable_of_Icc (by norm_num)
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)] at hi ⊢
    refine (integrableOn_congr_fun ?_ measurableSet_Ioo).mp hi
    intro t ht
    change -dslope f 1 t = digammaKernel z t
    rw [dslope_of_ne f ht.2.ne, slope, Complex.real_smul]
    simp only [f, Complex.ofReal_one, one_cpow, digammaKernel, Complex.ofReal_inv,
      Complex.ofReal_sub, vsub_eq_sub]
    rw [show (t : ℂ) - 1 = -(1 - (t : ℂ)) by ring, inv_neg, neg_mul, neg_neg, div_eq_mul_inv,
      mul_comm]
  exact (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mp (hleft.trans hright)

private theorem betaDifference_eq_quotient {z : ℂ} (hz : 0 < z.re) {e : ℝ} (he : 0 < e) :
    (∫ t in Ioo (0 : ℝ) 1, digammaKernel z t * (1 - (t : ℂ)) ^ (e : ℂ)) =
      (Gamma z * Gamma (1 + (e : ℂ)) / Gamma (z + (e : ℂ)) - 1) / (e : ℂ) := by
  have he' : 0 < (e : ℂ).re := he
  have hz' : 0 < (z + (e : ℂ)).re := add_pos hz he'
  have he0 : (e : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr he.ne'
  have hbeta : betaIntegral (1 : ℂ) (e : ℂ) = 1 / (e : ℂ) :=
    (betaIntegral_symm _ _).trans (betaIntegral_eval_one_right he')
  have hdiff : (∫ t in Ioo (0 : ℝ) 1, digammaKernel z t * (1 - (t : ℂ)) ^ (e : ℂ)) =
      betaIntegral z (e : ℂ) - betaIntegral 1 (e : ℂ) := by
    simp only [betaIntegral, intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
    rw [← integral_sub
      ((intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mp (betaIntegral_convergent hz he'))
      ((intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mp
        (betaIntegral_convergent (by simp : 0 < (1 : ℂ).re) he'))]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro t ht
    have hb : (1 : ℂ) - t ≠ 0 := by
      rw [sub_ne_zero, ← Complex.ofReal_one, Ne, Complex.ofReal_inj]
      exact ht.2.ne.symm
    simp only [digammaKernel, sub_self, cpow_zero, one_mul, cpow_sub _ _ hb, cpow_one]
    ring
  rw [hdiff, hbeta, betaIntegral_eq_Gamma_mul_div _ _ hz he', add_comm (1 : ℂ), Gamma_add_one _ he0]
  field_simp

private theorem tendsto_gammaDifference {z : ℂ} (hz : 0 < z.re) :
    Tendsto (fun e : ℝ ↦ (Gamma z * Gamma (1 + (e : ℂ)) / Gamma (z + (e : ℂ)) - 1) / (e : ℂ))
      (𝓝[>] 0) (𝓝 (digamma 1 - digamma z)) := by
  have hz0 := Gamma_ne_zero_of_re_pos hz
  let F (e : ℂ) := Gamma z * Gamma (1 + e) / Gamma (z + e)
  have hF0 : F 0 = 1 := by simp [F, hz0]
  have htranslate (w : ℂ) (hw : 0 < w.re) :
      HasDerivAt (fun e : ℂ ↦ Gamma (w + e)) (deriv Gamma w) 0 := by
    have h := (differentiableAt_Gamma w (fun n hn => by
      have hre := congrArg Complex.re hn
      simp at hre
      linarith [Nat.cast_nonneg (α := ℝ) n])).hasDerivAt
    exact HasDerivAt.comp_const_add w 0 (by simpa only [add_zero] using h)
  have hF : HasDerivAt F (digamma 1 - digamma z) (0 : ℂ) := by
    have hD := ((htranslate 1 (by simp)).const_mul (Gamma z)).div (htranslate z hz)
      (by simpa using hz0)
    have hvalue :
        (Gamma z * deriv Gamma 1 * Gamma (z + 0) -
          Gamma z * Gamma (1 + 0) * deriv Gamma z) / Gamma (z + 0) ^ 2 =
          digamma 1 - digamma z := by
      simp only [digamma_def, logDeriv_apply, Gamma_one, div_one, add_zero, mul_one]
      field_simp
    rw [hvalue] at hD
    exact hD
  have hreal : HasDerivAt (fun e : ℝ ↦ F (e : ℂ)) (digamma 1 - digamma z) 0 := by
    exact HasDerivAt.comp_ofReal (by simpa only [Complex.ofReal_zero] using hF)
  have hreal0 : F ((0 : ℝ) : ℂ) = 1 := by simpa only [Complex.ofReal_zero] using hF0
  have h := hreal.tendsto_slope_zero_right
  simp only [zero_add, Complex.real_smul, Complex.ofReal_inv, hreal0] at h
  simpa only [div_eq_inv_mul, F] using h

/-- The subtracted Gauss integral on the open right half-plane, with absolute integrability. -/
theorem digamma_one_sub_eq_integral {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn (fun t : ℝ ↦ ((t : ℂ) ^ (z - 1) - 1) / (1 - (t : ℂ))) (Ioo 0 1) ∧
    (∫ t in Ioo (0 : ℝ) 1, ((t : ℂ) ^ (z - 1) - 1) / (1 - (t : ℂ))) = digamma 1 - digamma z := by
  have hK := integrableOn_digammaKernel hz
  refine ⟨hK, ?_⟩
  change (∫ t in Ioo (0 : ℝ) 1, digammaKernel z t) = _
  let F (e : ℝ) (t : ℝ) := digammaKernel z t * (1 - (t : ℂ)) ^ (e : ℂ)
  have hb (t : ℝ) : (1 : ℂ) - (t : ℂ) = ((1 - t : ℝ) : ℂ) := by push_cast; rfl
  have hlim : Tendsto (fun e ↦ ∫ t in Ioo (0 : ℝ) 1, F e t) (𝓝[>] 0)
      (𝓝 (∫ t in Ioo (0 : ℝ) 1, digammaKernel z t)) := by
    refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (fun t ↦ ‖digammaKernel z t‖) ?_ ?_ hK.norm ?_
    refine Eventually.of_forall ?_
    · intro e
      have hc : ContinuousOn (fun t : ℝ ↦ (1 - (t : ℂ)) ^ (e : ℂ)) (Ioo (0 : ℝ) 1) := by
        intro t ht
        refine ContinuousAt.continuousWithinAt (ContinuousAt.cpow (by fun_prop) continuousAt_const ?_)
        rw [hb, Complex.ofReal_mem_slitPlane]
        exact sub_pos.mpr ht.2
      exact hK.aestronglyMeasurable.mul (hc.aestronglyMeasurable measurableSet_Ioo)
    · filter_upwards [self_mem_nhdsWithin (s := Ioi (0 : ℝ))] with e he
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      change ‖digammaKernel z t * (1 - (t : ℂ)) ^ (e : ℂ)‖ ≤ ‖digammaKernel z t‖
      rw [norm_mul, hb, norm_cpow_eq_rpow_re_of_pos (sub_pos.mpr ht.2), Complex.ofReal_re]
      exact mul_le_of_le_one_right (norm_nonneg _) <|
        Real.rpow_le_one (by linarith [ht.2]) (by linarith [ht.1]) he.le
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      have hb0 : (1 : ℂ) - (t : ℂ) ≠ 0 := by
        rw [hb, Complex.ofReal_ne_zero]
        exact (sub_pos.mpr ht.2).ne'
      have hpow : ContinuousAt (fun e : ℝ ↦ (1 - (t : ℂ)) ^ (e : ℂ)) 0 :=
        Complex.continuous_ofReal.continuousAt.const_cpow (Or.inl hb0)
      have hprod : ContinuousAt (F · t) 0 := continuousAt_const.mul hpow
      have hzero : F 0 t = digammaKernel z t := by simp [F]
      rw [← hzero]
      exact hprod.continuousWithinAt
  refine tendsto_nhds_unique hlim ((tendsto_gammaDifference hz).congr' ?_)
  filter_upwards [self_mem_nhdsWithin (s := Ioi (0 : ℝ))] with e he
  exact (betaDifference_eq_quotient hz he).symm

/-- The Gauss difference after the substitution `t = exp (-d * x)`.
Keep the two terms together at the origin. -/
def gaussDigammaDifference (d : ℝ) (w : ℂ) (x : ℝ) : ℂ :=
  (exp (-(d : ℂ) * (x : ℂ)) - exp (-w * (x : ℂ))) /
    (1 - exp (-(d : ℂ) * (x : ℂ)))

/-- Write the Gauss integral in log coordinates using `t = exp (-d * x)`. -/
theorem integral_gaussDigammaDifference {w : ℂ} {d : ℝ}
    (hd : 0 < d) (hw : 0 < (w / (d : ℂ)).re) :
    IntegrableOn (gaussDigammaDifference d w) (Ioi 0) ∧
      (∫ x in Ioi (0 : ℝ), gaussDigammaDifference d w x) =
        (digamma (w / (d : ℂ)) - digamma 1) / (d : ℂ) := by
  let K := gaussDigammaDifference d w
  let Q (t : ℝ) := ((t : ℂ) ^ (w / (d : ℂ) - 1) - 1) / (1 - (t : ℂ))
  obtain ⟨hQ, hval⟩ := digamma_one_sub_eq_integral hw
  change IntegrableOn Q (Ioo 0 1) at hQ
  change (∫ t in Ioo (0 : ℝ) 1, Q t) = _ at hval
  have hd₀ : (d : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hd.ne'
  let f (x : ℝ) := Real.exp (-d * x)
  let f' (x : ℝ) := -d * f x
  have hder (x : ℝ) (_ : x ∈ Ioi (0 : ℝ)) : HasDerivWithinAt f (f' x) (Ioi 0) x := by
    simpa only [f, f', mul_comm, id_eq, one_mul, mul_one] using
      ((hasDerivAt_id x).const_mul (-d)).exp.hasDerivWithinAt (s := Ioi 0)
  have hinj : InjOn f (Ioi (0 : ℝ)) := by
    intro x _ y _ h
    exact mul_left_cancel₀ (neg_ne_zero.mpr hd.ne') (Real.exp_injective h)
  have himage : f '' Ioi 0 = Ioo 0 1 := by
    ext t
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨Real.exp_pos _, Real.exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos (neg_neg_of_pos hd) hx)⟩
    · intro ht
      refine ⟨-Real.log t / d, div_pos (neg_pos.mpr (Real.log_neg ht.1 ht.2)) hd, ?_⟩
      change Real.exp (-d * (-Real.log t / d)) = t
      rw [show -d * (-Real.log t / d) = Real.log t by field_simp, Real.exp_log ht.1]
  have hchange : EqOn (fun x ↦ |f' x| • Q (f x)) (fun x ↦ (-(d : ℂ)) * K x) (Ioi 0) := by
    intro x _
    have hf : 0 < f x := Real.exp_pos _
    have habs : |f' x| = d * f x := by
      rw [show f' x = -(d * f x) by simp [f'], abs_neg, abs_of_nonneg (mul_pos hd hf).le]
    have hcast : (f x : ℂ) = exp (-(d : ℂ) * (x : ℂ)) := by
      simp only [f, Complex.ofReal_exp, Complex.ofReal_mul, Complex.ofReal_neg]
    have hlog : log (f x : ℂ) = -(d : ℂ) * (x : ℂ) := by
      rw [← Complex.ofReal_log hf.le, show Real.log (f x) = -d * x from Real.log_exp _]
      push_cast; rfl
    have hpow : (f x : ℂ) ^ (w / (d : ℂ) - 1) =
        exp ((-(d : ℂ) * (x : ℂ)) * (w / (d : ℂ) - 1)) := by
      rw [cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hf.ne'), hlog]
    simp only [habs, Complex.real_smul, Complex.ofReal_mul, Q, K, gaussDigammaDifference]
    rw [hpow, hcast, show -w * (x : ℂ) =
      (-(d : ℂ) * (x : ℂ)) + (-(d : ℂ) * (x : ℂ)) * (w / (d : ℂ) - 1) by
        field_simp; ring, Complex.exp_add]
    ring
  have hi := (integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi hder hinj Q).mp
    (himage.symm ▸ hQ)
  have hKi : IntegrableOn K (Ioi 0) := by
    have hscaled := (integrableOn_congr_fun hchange measurableSet_Ioi).mp hi
    simpa only [IntegrableOn, ← mul_assoc, inv_mul_cancel₀ (neg_ne_zero.mpr hd₀), one_mul]
      using hscaled.const_mul ((-(d : ℂ))⁻¹)
  have heq := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hder hinj Q
  rw [himage, hval, setIntegral_congr_fun measurableSet_Ioi hchange, integral_const_mul] at heq
  refine ⟨hKi, (eq_div_iff hd₀).mpr ?_⟩
  change (∫ x in Ioi (0 : ℝ), K x) * (d : ℂ) = _
  linear_combination heq

private theorem one_sub_exp_neg_le (y : ℝ) : 1 - Real.exp (-y) ≤ y := by
  linarith [Real.add_one_le_exp (-y)]

private theorem abs_real_damping_sub_le (d u : ℝ) {x : ℝ} (hx : 0 < x) :
    |Real.exp (-d * x) - Real.exp (-u * x)| ≤ x * Real.exp (-min d u * x) * |d - u| := by
  wlog h : d ≤ u generalizing d u
  · simpa only [abs_sub_comm, min_comm] using this u d (le_of_not_ge h)
  have horder : Real.exp (-u * x) ≤ Real.exp (-d * x) := by
    apply Real.exp_le_exp.mpr
    gcongr
  rw [abs_of_nonneg (sub_nonneg.mpr horder), min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h),
    show -u * x = -d * x + -((u - d) * x) by ring, Real.exp_add, ← mul_one_sub]
  calc
    _ ≤ Real.exp (-d * x) * ((u - d) * x) :=
      mul_le_mul_of_nonneg_left (one_sub_exp_neg_le _) (Real.exp_pos _).le
    _ = _ := by ring

theorem norm_gaussDigammaDifference_le {d u v x : ℝ} (hd : 0 < d) (hx : 0 < x) :
    ‖gaussDigammaDifference d ((u : ℂ) + (v : ℂ) * I) x‖ ≤
      (|d - u| + |v|) * ((1 / d + x) * Real.exp (-min d u * x)) := by
  let E (q : ℝ) := Real.exp (-q * x)
  let P := exp (I * ((-v * x : ℝ) : ℂ))
  have hdamp (q : ℝ) : exp (-(q : ℂ) * (x : ℂ)) = (E q : ℂ) := by
    dsimp only [E]
    rw [Complex.ofReal_exp, Complex.ofReal_mul, Complex.ofReal_neg]
  have hphase : exp (-((u : ℂ) + (v : ℂ) * I) * (x : ℂ)) = (E u : ℂ) * P := by
    rw [← hdamp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hchord : ‖(1 : ℂ) - P‖ ≤ |v| * x := by
    rw [norm_sub_rev]
    simpa [P, Real.norm_eq_abs, abs_mul, abs_of_pos hx] using
      (Real.norm_exp_I_mul_ofReal_sub_one_le (x := -v * x))
  have hmono : E u ≤ E (min d u) := by
    dsimp [E]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_neg (min_le_right d u)) hx.le)
  have hnum : ‖(E d : ℂ) - (E u : ℂ) * P‖ ≤ x * E (min d u) * (|d - u| + |v|) := by
    rw [show (E d : ℂ) - (E u : ℂ) * P = ((E d : ℂ) - (E u : ℂ)) + (E u : ℂ) * (1 - P) by ring]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ x * E (min d u) * |d - u| + E (min d u) * (|v| * x) :=
        add_le_add (abs_real_damping_sub_le d u hx)
          (mul_le_mul hmono hchord (norm_nonneg _) (Real.exp_pos _).le)
      _ = _ := by ring
  -- `1 + dx ≤ exp (dx)` bounds the denominator from below near zero.
  have hd0 : 0 < 1 - E d :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos (neg_neg_of_pos hd) hx))
  have hrecip : (d * x + 1) * E d ≤ 1 := by
    dsimp [E]
    rw [show -d * x = -(d * x) by ring, Real.exp_neg, mul_inv_le_iff₀ (Real.exp_pos _), one_mul]
    exact Real.add_one_le_exp _
  have hxden : x ≤ (1 / d + x) * (1 - E d) := by
    apply (mul_le_mul_iff_right₀ hd).mp
    have h : d * x ≤ (d * x + 1) * (1 - E d) := by
      linarith only [hrecip, mul_sub (d * x + 1) 1 (E d)]
    calc
      d * x ≤ (d * x + 1) * (1 - E d) := h
      _ = d * ((1 / d + x) * (1 - E d)) := by field_simp; ring
  rw [gaussDigammaDifference, hdamp, hphase, norm_div, ← Complex.ofReal_one,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd0]
  apply (div_le_iff₀ hd0).2
  refine hnum.trans ?_
  calc
    _ ≤ ((1 / d + x) * (1 - E d)) * E (min d u) * (|d - u| + |v|) := by gcongr
    _ = _ := by ring

/-- The Gauss integral gives a linear bound on the closed half-plane
with real part at least one half. -/
theorem exists_norm_digamma_le_of_half_le_re :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, 1 / 2 ≤ z.re → ‖digamma z‖ ≤ C * (1 + ‖z‖) := by
  let g (x : ℝ) := (1 + x) * Real.exp (-(1 / 2 : ℝ) * x)
  have hg : IntegrableOn g (Ioi 0) := by
    have he := integrableOn_exp_mul_Ioi (by norm_num : -(1 / 2 : ℝ) < 0) 0
    have hx : IntegrableOn (fun x : ℝ ↦ x * Real.exp (-(1 / 2 : ℝ) * x)) (Ioi 0) := by
      simpa using (integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := 1)
        (by norm_num) le_rfl (by norm_num : (0 : ℝ) < 1 / 2))
    exact (he.add hx).congr (.of_forall fun x => by dsimp [g]; ring)
  let M := ∫ x in Ioi (0 : ℝ), g x
  have hM : 0 ≤ M := setIntegral_nonneg measurableSet_Ioi
    (fun x hx => mul_nonneg (by linarith [mem_Ioi.mp hx]) (Real.exp_nonneg _))
  refine ⟨‖digamma 1‖ + 2*M, by positivity, fun z hz => ?_⟩
  obtain ⟨hK, hk⟩ := integral_gaussDigammaDifference (w := z) (d := 1) one_pos
    (by simpa using (show 0 < z.re by linarith))
  simp only [ofReal_one, div_one] at hk
  have hbound : ‖digamma z - digamma 1‖ ≤ (|1 - z.re| + |z.im|) * M := by
    rw [← hk, ← integral_const_mul]
    refine (norm_integral_le_integral_norm _).trans
      (integral_mono_ae hK.norm (hg.const_mul _) ?_)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have h := norm_gaussDigammaDifference_le (d := 1) (u := z.re) (v := z.im) one_pos hx
    rw [Complex.re_add_im] at h
    refine h.trans ?_
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [one_div_one]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by linarith [mem_Ioi.mp hx])
    exact mul_le_mul_of_nonneg_right (neg_le_neg (le_min (by norm_num) hz)) (mem_Ioi.mp hx).le
  have hcoord : |1 - z.re| + |z.im| ≤ 2 * (1 + ‖z‖) := by
    have h := abs_sub_le (1 : ℝ) 0 z.re
    simp only [sub_zero, abs_one, zero_sub, abs_neg] at h
    linarith [Complex.abs_re_le_norm z, Complex.abs_im_le_norm z]
  calc
    ‖digamma z‖ ≤ ‖digamma z - digamma 1‖ + ‖digamma 1‖ := by
      simpa only [sub_add_cancel] using norm_add_le (digamma z - digamma 1) (digamma 1)
    _ ≤ (2 * (1 + ‖z‖)) * M + ‖digamma 1‖ :=
      add_le_add (hbound.trans (mul_le_mul_of_nonneg_right hcoord hM)) le_rfl
    _ ≤ _ := by nlinarith [mul_nonneg (norm_nonneg (digamma 1)) (norm_nonneg z)]

/-- Two applications of the recurrence extend the linear bound across
the critical strip at ordinates at least one away from the real axis. -/
theorem exists_norm_digamma_le_high :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, -1 ≤ z.re → 1 ≤ |z.im| →
      ‖digamma z‖ ≤ C * (1 + ‖z‖) := by
  obtain ⟨C, hC, h⟩ := exists_norm_digamma_le_of_half_le_re
  refine ⟨3*C + 2, by positivity, fun z hz hi => ?_⟩
  have hreg (n : ℕ) : z ≠ -(n : ℂ) := by
    intro hEq
    have hh := congrArg Complex.im hEq
    simp at hh
    simp [hh] at hi
    linarith
  have hreg' (n : ℕ) : z + 1 ≠ -(n : ℂ) := by
    intro hEq
    have hh := congrArg Complex.im hEq
    simp [Complex.add_im] at hh
    simp [hh] at hi
    linarith
  have hEq : digamma z = digamma ((z+1)+1) - (z+1)⁻¹ - z⁻¹ := by
    rw [digamma_apply_add_one _ hreg', digamma_apply_add_one _ hreg]
    ring
  have hzi : ‖z⁻¹‖ ≤ 1 := by
    rw [norm_inv]
    exact inv_le_one_of_one_le₀ (hi.trans (Complex.abs_im_le_norm z))
  have hzi' : ‖(z+1)⁻¹‖ ≤ 1 := by
    rw [norm_inv]
    exact inv_le_one_of_one_le₀ ((by simpa [Complex.add_im] using hi :
      1 ≤ |(z+1).im|).trans (Complex.abs_im_le_norm _))
  have hre : 1 / 2 ≤ ((z+1)+1).re := by simp [Complex.add_re]; linarith
  have hNorm : ‖(z+1)+1‖ ≤ ‖z‖ + 2 := calc
    _ ≤ ‖z+1‖ + 1 := by simpa using norm_add_le (z+1) (1 : ℂ)
    _ ≤ (‖z‖ + 1) + 1 := add_le_add (by simpa using norm_add_le z (1 : ℂ)) le_rfl
    _ = _ := by ring
  rw [hEq]
  calc
    _ ≤ (‖digamma ((z+1)+1)‖ + ‖(z+1)⁻¹‖) + ‖z⁻¹‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ (C * (1 + (‖z‖ + 2)) + 1) + 1 :=
      add_le_add (add_le_add ((h _ hre).trans (mul_le_mul_of_nonneg_left
        (add_le_add le_rfl hNorm) hC)) hzi') hzi
    _ ≤ _ := by nlinarith [norm_nonneg z, mul_nonneg hC (norm_nonneg z)]

/-- Any measurable weight with an integrable first absolute ordinate moment
permits exchange on the right line *with the subtraction intact*. -/
theorem integrable_mul_gaussDigammaDifference {a d b τ k : ℝ} (hab : 0 < a + b)
    (hd : 0 < d) (hk : 0 < k) {W : ℝ → ℂ} (hW : Measurable W)
    (hWt : Integrable (fun t ↦ ‖W t‖ * (1 + |t|))) :
    Integrable (fun p : ℝ × ℝ ↦ W p.1 * gaussDigammaDifference d
      ((k : ℂ) * (((a : ℂ) + (p.1 : ℂ) * I) + ((b : ℂ) + (τ : ℂ) * I))) p.2)
      ((volume : Measure ℝ).prod (volume.restrict (Ioi 0))) := by
  let m := min d (k * (a + b))
  let C := |d - k * (a + b)| + k * |τ| + k
  have hm : 0 < m := lt_min hd (mul_pos hk hab)
  have he : IntegrableOn (fun x : ℝ ↦ Real.exp (-m * x)) (Ioi 0) :=
    integrableOn_exp_mul_Ioi (neg_neg_of_pos hm) 0
  have hxe : IntegrableOn (fun x : ℝ ↦ x * Real.exp (-m * x)) (Ioi 0) := by
    simpa using (integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := 1) (by norm_num) le_rfl hm)
  have hEnv : IntegrableOn (fun x : ℝ ↦ (1 / d + x) * Real.exp (-m * x)) (Ioi 0) := by
    exact ((he.const_mul (1 / d)).add hxe).congr
      (Filter.Eventually.of_forall fun x ↦ (add_mul (1 / d) x _).symm)
  refine (hWt.mul_prod (hEnv.const_mul C)).mono'
    (Measurable.aestronglyMeasurable (by unfold gaussDigammaDifference; fun_prop)) ?_
  have hx : ∀ᵐ p : ℝ × ℝ ∂((volume : Measure ℝ).prod (volume.restrict (Ioi 0))), p.2 ∈ Ioi 0 :=
    (Measure.ae_prod_mem_iff_ae_ae_mem (measurable_snd measurableSet_Ioi)).mpr <|
      Filter.Eventually.of_forall fun _ ↦ ae_restrict_mem measurableSet_Ioi
  filter_upwards [hx] with ⟨t, x⟩ hx
  have hx' : 0 < x := hx
  change ‖W t * gaussDigammaDifference d _ x‖ ≤ ‖W t‖ * (1 + |t|) *
    (C * ((1 / d + x) * Real.exp (-m * x)))
  rw [norm_mul, show (k : ℂ) * (((a : ℂ) + (t : ℂ) * I) + ((b : ℂ) + (τ : ℂ) * I)) =
    ((k * (a + b) : ℝ) : ℂ) + ((k * (t + τ) : ℝ) : ℂ) * I by push_cast; ring]
  have hC : |d - k * (a + b)| + |k * (t + τ)| ≤ (1 + |t|) * C := by
    calc
      _ ≤ |d - k * (a + b)| + k * (|t| + |τ|) := by
        rw [abs_mul, abs_of_pos hk]
        gcongr
        exact abs_add_le t τ
      _ ≤ _ := by
        dsimp [C]
        nlinarith [mul_nonneg (abs_nonneg t) (abs_nonneg (d - k * (a + b))),
          mul_nonneg (abs_nonneg t) (mul_nonneg hk.le (abs_nonneg τ))]
  calc
    _ ≤ ‖W t‖ * ((|d - k * (a + b)| + |k * (t + τ)|) * ((1 / d + x) * Real.exp (-m * x))) :=
      mul_le_mul_of_nonneg_left (norm_gaussDigammaDifference_le hd hx') (norm_nonneg _)
    _ ≤ ‖W t‖ * (((1 + |t|) * C) * ((1 / d + x) * Real.exp (-m * x))) := by gcongr
    _ = _ := by ring

end Masullo
