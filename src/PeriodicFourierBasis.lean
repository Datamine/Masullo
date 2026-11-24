import PeriodicDerivativeTopology
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.PSeries
import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn
import Mathlib.Topology.UniformSpace.Equicontinuity

open AddCircle Bornology Filter Function MeasureTheory Set Topology
open scoped ContDiff

namespace Masullo

noncomputable section

variable (d : ℝ) [Fact (0 < d)]

private theorem period_pos : 0 < d := Fact.out

/-- The complex frequency of a logarithmically periodic mode. -/
def periodicFrequency (m : ℤ) : ℂ := 2 * Real.pi * Complex.I * m / d

/-- A Fourier mode pulled back from the logarithmic circle to the real axis. -/
def periodicFourierMode (m : ℤ) : SmoothPeriodic d := by
  let g (t : ℝ) := Complex.exp (periodicFrequency d m * (t : ℂ))
  have he (t : ℝ) : g t = fourier m (t : AddCircle d) := by
    rw [fourier_coe_apply]
    congr 1
    unfold g periodicFrequency
    ring
  have hg : ContDiff ℝ ∞ g := (contDiff_const.mul Complex.ofRealCLM.contDiff).cexp
  refine ⟨g, hg, ?_⟩
  intro t
  simp only [he]
  congr 1
  exact AddCircle.coe_add_period d t

theorem periodicFourierMode_apply (m : ℤ) (t : ℝ) :
    (periodicFourierMode d m).val t = Complex.exp (periodicFrequency d m * (t : ℂ)) := rfl

theorem periodicFourierMode_circle (m : ℤ) (t : ℝ) :
    (periodicFourierMode d m).val t = fourier m (t : AddCircle d) := by
  rw [periodicFourierMode_apply, fourier_coe_apply]
  congr 1
  unfold periodicFrequency
  ring

def periodicCircleFunction (f : SmoothPeriodic d) : C(AddCircle d, ℂ) :=
  ⟨f.property.2.lift, QuotientAddGroup.isOpenQuotientMap_mk.continuous_comp_iff.mp
    f.property.1.continuous⟩

@[simp] theorem periodicCircleFunction_coe (f : SmoothPeriodic d) (x : ℝ) :
    periodicCircleFunction d f (x : AddCircle d) = f.val x :=
  f.property.2.lift_coe x

/-- The genuine Fourier coefficient for the normalized Haar measure on the circle. -/
def periodicFourierCoefficient (f : SmoothPeriodic d) (m : ℤ) : ℂ :=
  fourierCoeff (periodicCircleFunction d f) m

theorem periodicFourierCoefficient_interval (f : SmoothPeriodic d) (m : ℤ) :
    periodicFourierCoefficient d f m =
      (1 / d : ℝ) • ∫ x in (0 : ℝ)..d, fourier (-m) (x : AddCircle d) • f.val x := by
  rw [periodicFourierCoefficient, fourierCoeff_eq_intervalIntegral _ _ 0, zero_add]
  simp only [periodicCircleFunction_coe]

private theorem periodicFourierCoefficient_fourierCoeffOn (f : SmoothPeriodic d) (m : ℤ) :
    periodicFourierCoefficient d f m = fourierCoeffOn (period_pos d) f.val m := by
  rw [periodicFourierCoefficient_interval, fourierCoeffOn_eq_integral, sub_zero]

private theorem periodicFourierMode_coefficient (n m : ℤ) :
    periodicFourierCoefficient d (periodicFourierMode d n) m = Pi.single (M := fun _ : ℤ => ℂ) n 1 m := by
  have he : periodicCircleFunction d (periodicFourierMode d n) = fourier n := by
    ext x
    obtain ⟨a, rfl⟩ := Quotient.exists_rep x
    rw [periodicCircleFunction_coe, periodicFourierMode_circle]
  rw [periodicFourierCoefficient, he, fourierCoeff_fourier]

private def periodicIteratedDeriv (n : ℕ) (f : SmoothPeriodic d) : SmoothPeriodic d :=
  ⟨iteratedDeriv n f.val, by rw [iteratedDeriv_eq_iterate]; exact f.property.1.iterate_deriv n, by
    intro x
    have he : (fun y => f.val (y + d)) = f.val := funext f.property.2
    rw [← congrFun (iteratedDeriv_comp_add_const n f.val d) x, he]⟩

private theorem periodicIteratedDeriv_succ (n : ℕ) (f : SmoothPeriodic d) :
    (periodicIteratedDeriv d (n + 1) f).val = deriv (periodicIteratedDeriv d n f).val :=
  iteratedDeriv_succ

private theorem periodicFourierCoefficient_deriv (f : SmoothPeriodic d) (m : ℤ) (hm : m ≠ 0) :
    periodicFourierCoefficient d (periodicIteratedDeriv d 1 f) m =
      periodicFrequency d m * periodicFourierCoefficient d f m := by
  have hD (x : ℝ) : HasDerivAt f.val (deriv f.val x) x :=
    ((f.property.1.differentiable (by simp)) x).hasDerivAt
  have hF := fourierCoeffOn_of_hasDerivAt (period_pos d) hm
    (fun x _ => hD x) ((f.property.1.continuous_deriv (by simp)).intervalIntegrable 0 d)
  have hval : f.val d = f.val 0 := by simpa using f.property.2 0
  rw [hval, sub_self, mul_zero, zero_sub, Complex.ofReal_zero, sub_zero] at hF
  rw [periodicFourierCoefficient_fourierCoeffOn, periodicFourierCoefficient_fourierCoeffOn]
  change fourierCoeffOn (period_pos d) (iteratedDeriv 1 f.val) m = _
  rw [iteratedDeriv_one]
  have hn : (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ)) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero))
      Complex.I_ne_zero) (Int.cast_ne_zero.mpr hm)
  rw [hF, periodicFrequency]
  field_simp [hn, (period_pos d).ne']


private theorem periodicFourierCoefficient_iterated (f : SmoothPeriodic d) (m : ℤ) (hm : m ≠ 0)
    (n : ℕ) :
    periodicFourierCoefficient d (periodicIteratedDeriv d n f) m =
      periodicFrequency d m ^ n * periodicFourierCoefficient d f m := by
  induction n with
  | zero =>
    have h : periodicIteratedDeriv d 0 f = f := Subtype.ext iteratedDeriv_zero
    rw [h, pow_zero, one_mul]
  | succ n hn =>
    have he : periodicIteratedDeriv d (n + 1) f =
        periodicIteratedDeriv d 1 (periodicIteratedDeriv d n f) := by
      apply Subtype.ext
      rw [periodicIteratedDeriv_succ]
      exact iteratedDeriv_one.symm
    rw [he, periodicFourierCoefficient_deriv d _ m hm, hn, pow_succ']
    ring

theorem periodicFourierMode_iteratedDeriv (m : ℤ) (n : ℕ) :
    iteratedDeriv n (periodicFourierMode d m).val =
      fun t : ℝ => periodicFrequency d m ^ n * (periodicFourierMode d m).val t := by
  let c := periodicFrequency d m
  have hD (t : ℝ) : HasDerivAt (periodicFourierMode d m).val
      (c * (periodicFourierMode d m).val t) t := by
    have hcast : HasDerivAt (fun x : ℝ => (x : ℂ)) 1 t := by
      change HasDerivAt (⇑Complex.ofRealCLM) (Complex.ofRealCLM 1) t
      exact Complex.ofRealCLM.hasFDerivAt.hasDerivAt
    have h := (hcast.const_mul c).cexp
    change HasDerivAt (fun t : ℝ => Complex.exp (c * (t : ℂ))) (c * Complex.exp (c * (t : ℂ))) t
    simpa only [mul_one, mul_comm] using h
  induction n with
  | zero => simp
  | succ n hn =>
    rw [iteratedDeriv_succ, hn]
    funext t
    rw [((hD t).const_mul (c ^ n)).deriv, pow_succ]
    ring

private theorem periodicFourierMode_norm (m : ℤ) (t : ℝ) :
    ‖(periodicFourierMode d m).val t‖ = 1 := by
  rw [periodicFourierMode_circle, fourier_apply, Circle.norm_coe]

private theorem periodicFourierCoefficient_norm_le (f : SmoothPeriodic d) (m : ℤ) :
    ‖periodicFourierCoefficient d f m‖ ≤ ‖periodicDerivativeLM d 0 f‖ := by
  change ‖∫ x, fourier (-m) x • periodicCircleFunction d f x ∂(haarAddCircle (T := d))‖ ≤ _
  have h := norm_integral_le_of_norm_le_const (μ := haarAddCircle (T := d))
    (f := fun x => fourier (-m) x • periodicCircleFunction d f x)
    (C := ‖periodicDerivativeLM d 0 f‖) (Filter.Eventually.of_forall fun x => ?_)
  · simpa using h
  · obtain ⟨t, rfl⟩ := Quotient.exists_rep x
    rw [periodicCircleFunction_coe, norm_smul, fourier_apply, Circle.norm_coe, one_mul]
    simpa using iteratedDeriv_le_periodicDerivativeNorm (period_pos d) f 0 t

/-- Each Fourier coefficient is controlled by every derivative seminorm,
with the corresponding power of the nonzero frequency. -/
theorem periodicFourierCoefficient_rapid (f : SmoothPeriodic d) (m : ℤ) (hm : m ≠ 0)
    (n : ℕ) :
    ‖periodicFrequency d m‖ ^ n * ‖periodicFourierCoefficient d f m‖ ≤
      ‖periodicDerivativeLM d n f‖ := by
  have h := periodicFourierCoefficient_norm_le d (periodicIteratedDeriv d n f) m
  rw [periodicFourierCoefficient_iterated d f m hm n, norm_mul, norm_pow] at h
  have he : periodicDerivativeLM d 0 (periodicIteratedDeriv d n f) = periodicDerivativeLM d n f := by
    ext x
    simp [periodicDerivativeLM, periodicIteratedDeriv]
  rwa [he] at h


private def periodicFourierCoefficientLM (m : ℤ) : SmoothPeriodic d →ₗ[ℂ] ℂ where
  toFun f := periodicFourierCoefficient d f m
  map_add' f g := by
    have he : periodicCircleFunction d (f + g) =
        periodicCircleFunction d f + periodicCircleFunction d g := by
      apply ContinuousMap.ext
      intro x
      obtain ⟨t, rfl⟩ := Quotient.exists_rep x
      simp only [periodicCircleFunction_coe, ContinuousMap.add_apply]
      rfl
    have hInt (f : SmoothPeriodic d) : Integrable (periodicCircleFunction d f) (haarAddCircle (T := d)) :=
      (periodicCircleFunction d f).continuous.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    simp only [periodicFourierCoefficient, he]
    exact congrFun (fourierCoeff.add (hInt f) (hInt g)) m
  map_smul' c f := by
    have he : periodicCircleFunction d (c • f) = c • periodicCircleFunction d f := by
      apply ContinuousMap.ext
      intro x
      obtain ⟨t, rfl⟩ := Quotient.exists_rep x
      simp only [periodicCircleFunction_coe, ContinuousMap.smul_apply]
      rfl
    simp only [periodicFourierCoefficient, he, RingHom.id_apply]
    exact fourierCoeff.const_smul (periodicCircleFunction d f) c m

/-- Fourier coefficients are continuous in the full derivative topology. -/
def periodicFourierCoefficientCLM (m : ℤ) : SmoothPeriodic d →L[ℂ] ℂ := by
  refine ⟨periodicFourierCoefficientLM d m, ?_⟩
  rw [smoothPeriodic_topology_eq_derivative d]
  refine WithSeminorms.continuous_of_isBounded (periodicDerivative_withSeminorms d)
    (norm_withSeminorms ℂ ℂ) (periodicFourierCoefficientLM d m) ?_
  apply Seminorm.IsBounded.of_real
  intro i
  refine ⟨{⟨0, 0⟩}, 1, fun f => ?_⟩
  simpa [SeminormFamily.comp_apply, periodicDerivativeSeminorms, periodicFourierCoefficientLM] using
    periodicFourierCoefficient_norm_le d f m

private theorem periodicFourierCoefficient_deriv_zero (f : SmoothPeriodic d) :
    periodicFourierCoefficient d (periodicIteratedDeriv d 1 f) 0 = 0 := by
  rw [periodicFourierCoefficient_interval]
  have hf' := (f.property.1.continuous_deriv (by simp)).intervalIntegrable (μ := volume) 0 d
  have hD : ∀ x ∈ Set.uIcc (0 : ℝ) d, DifferentiableAt ℝ f.val x :=
    fun x _ => (f.property.1.differentiable (by simp)) x
  have hv : f.val d = f.val 0 := by simpa using f.property.2 0
  change (1 / d : ℝ) • ∫ x in (0 : ℝ)..d, fourier (-0) (x : AddCircle d) •
    iteratedDeriv 1 f.val x = 0
  simp only [neg_zero, fourier_zero, one_smul, iteratedDeriv_one]
  rw [intervalIntegral.integral_deriv_eq_sub hD hf', hv, sub_self, smul_zero]

private theorem periodicFourierCoefficient_iterated_all (f : SmoothPeriodic d) (m : ℤ)
    (n : ℕ) :
    periodicFourierCoefficient d (periodicIteratedDeriv d n f) m =
      periodicFrequency d m ^ n * periodicFourierCoefficient d f m := by
  by_cases hm : m = 0
  · subst m
    cases n with
    | zero =>
      rw [show periodicIteratedDeriv d 0 f = f from Subtype.ext iteratedDeriv_zero, pow_zero, one_mul]
    | succ n =>
      have he : periodicIteratedDeriv d (n + 1) f =
          periodicIteratedDeriv d 1 (periodicIteratedDeriv d n f) := by
        apply Subtype.ext
        rw [periodicIteratedDeriv_succ]
        exact iteratedDeriv_one.symm
      rw [he, periodicFourierCoefficient_deriv_zero]
      simp [periodicFrequency]
  · exact periodicFourierCoefficient_iterated d f m hm n

private theorem periodicFrequency_norm (m : ℤ) :
    ‖periodicFrequency d m‖ = (2 * Real.pi / d) * |(m : ℝ)| := by
  have hd := (period_pos d).le
  simp only [periodicFrequency, norm_div, norm_mul, Complex.norm_ofNat, Complex.norm_I,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg Real.pi_pos.le, Complex.norm_intCast,
    abs_of_nonneg hd, mul_one]
  ring

private theorem periodicMode_derivativeNorm_le (m : ℤ) (n : ℕ) :
    ‖periodicDerivativeLM d n (periodicFourierMode d m)‖ ≤ ‖periodicFrequency d m‖ ^ n := by
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro x
  change ‖iteratedDeriv n (periodicFourierMode d m).val x.val‖ ≤ _
  rw [periodicFourierMode_iteratedDeriv, norm_mul, norm_pow, periodicFourierMode_norm, mul_one]

private theorem periodicMode_derivativeNorm_eq (m : ℤ) (n : ℕ) :
    ‖periodicDerivativeLM d n (periodicFourierMode d m)‖ = ‖periodicFrequency d m‖ ^ n := by
  apply le_antisymm (periodicMode_derivativeNorm_le d m n)
  let x : PeriodInterval d := ⟨0, ⟨le_rfl, (period_pos d).le⟩⟩
  have h := (periodicDerivativeLM d n (periodicFourierMode d m)).norm_coe_le_norm x
  change ‖iteratedDeriv n (periodicFourierMode d m).val (x : ℝ)‖ ≤ _ at h
  rw [periodicFourierMode_iteratedDeriv, norm_mul, norm_pow, periodicFourierMode_norm, mul_one] at h
  exact h

private def inverseSquareFrequency (m : ℤ) : ℝ := 1 / (m : ℝ) ^ 2

private theorem periodicTerm_norm_le (f : SmoothPeriodic d) (n : ℕ) (m : ℤ) :
    ‖periodicDerivativeLM d n (periodicFourierCoefficient d f m • periodicFourierMode d m)‖ ≤
      (if m = 0 then ‖periodicDerivativeLM d 0 f‖ else 0) +
        (d / (2 * Real.pi)) ^ 2 * ‖periodicDerivativeLM d (n + 2) f‖ * inverseSquareFrequency m := by
  rw [map_smul, norm_smul]
  refine (mul_le_mul_of_nonneg_left (periodicMode_derivativeNorm_le d m n) (norm_nonneg _)).trans ?_
  by_cases hm : m = 0
  · subst m
    simp only [periodicFrequency, Int.cast_zero, mul_zero, zero_div, inverseSquareFrequency,
      ite_true, norm_zero, zero_pow two_ne_zero, div_zero, mul_zero, add_zero]
    calc
      _ ≤ ‖periodicFourierCoefficient d f 0‖ * 1 :=
        mul_le_mul_of_nonneg_left (zero_pow_le_one _) (norm_nonneg _)
      _ ≤ _ := by simpa using periodicFourierCoefficient_norm_le d f 0
  · rw [if_neg hm, zero_add]
    have hbound := periodicFourierCoefficient_rapid d f m hm (n + 2)
    let c := 2 * Real.pi / d
    have hc : 0 < c := by dsimp [c]; positivity [period_pos d]
    have hm' : (m : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hm
    have heq : ‖periodicFrequency d m‖ ^ 2 = c ^ 2 * (m : ℝ) ^ 2 := by
      rw [periodicFrequency_norm, mul_pow, sq_abs]
    rw [pow_add, heq] at hbound
    rw [inverseSquareFrequency]
    have hpos : 0 < c ^ 2 * (m : ℝ) ^ 2 := by positivity
    have hc' : (d / (2 * Real.pi)) = c⁻¹ := by dsimp [c]; rw [inv_div]
    rw [hc', inv_pow]
    have he : (c ^ 2)⁻¹ * ‖periodicDerivativeLM d (n + 2) f‖ * (1 / (m : ℝ) ^ 2) =
        ‖periodicDerivativeLM d (n + 2) f‖ / (c ^ 2 * (m : ℝ) ^ 2) := by
      field_simp [hc.ne', hm']
    rw [he]
    exact (le_div_iff₀ hpos).mpr (by simpa only [mul_left_comm, mul_comm, mul_assoc] using hbound)

theorem periodicFourierSeries_absolute (f : SmoothPeriodic d) (n : ℕ) :
    Summable (fun m : ℤ =>
      ‖periodicDerivativeLM d n (periodicFourierCoefficient d f m • periodicFourierMode d m)‖) := by
  have h₁ : Summable (fun m : ℤ => if m = 0 then ‖periodicDerivativeLM d 0 f‖ else 0) :=
    summable_of_hasFiniteSupport ((finite_singleton (0 : ℤ)).subset (fun m hm => by
      by_contra hn
      exact hm (if_neg (fun h => hn h))))
  have h₂ : Summable inverseSquareFrequency := Real.summable_one_div_int_pow.mpr (by decide : 1 < (2 : ℕ))
  exact (h₁.add (h₂.mul_left _)).of_nonneg_of_le (fun _ => norm_nonneg _) (periodicTerm_norm_le d f n)


private theorem periodicFourierCoefficient_summable (f : SmoothPeriodic d) :
    Summable (periodicFourierCoefficient d f) := by
  apply Summable.of_norm
  refine (periodicFourierSeries_absolute d f 0).congr fun m => ?_
  rw [map_smul, norm_smul, periodicMode_derivativeNorm_eq, pow_zero, mul_one]

private def circleRestriction : C(AddCircle d, ℂ) →L[ℂ] C(PeriodInterval d, ℂ) :=
  ContinuousMap.compCLM ℂ ℂ ⟨fun x : PeriodInterval d => (x.val : AddCircle d),
    QuotientAddGroup.continuous_mk.comp continuous_subtype_val⟩

/-- Fourier expansion converges unconditionally in all derivative seminorms. -/
theorem periodicFourierSeries_hasSum (f : SmoothPeriodic d) :
    HasSum (fun m : ℤ => periodicFourierCoefficient d f m • periodicFourierMode d m) f := by
  rw [HasSum]
  rw [smoothPeriodic_topology_eq_derivative]
  rw [periodicDerivativeTopology, nhds_induced, tendsto_comap_iff]
  apply tendsto_pi_nhds.mpr
  intro n
  let g := periodicIteratedDeriv d n f
  have hcs : Summable (fourierCoeff (periodicCircleFunction d g)) := periodicFourierCoefficient_summable d g
  have hsum := (circleRestriction d).hasSum (hasSum_fourier_series_of_summable hcs)
  have he (m : ℤ) :
      circleRestriction d (fourierCoeff (periodicCircleFunction d g) m • fourier m) =
        periodicDerivativeLM d n (periodicFourierCoefficient d f m • periodicFourierMode d m) := by
    apply ContinuousMap.ext
    intro x
    change periodicFourierCoefficient d g m * fourier m (x.val : AddCircle d) = _
    rw [map_smul]
    change periodicFourierCoefficient d g m * fourier m (x.val : AddCircle d) =
      periodicFourierCoefficient d f m * iteratedDeriv n (periodicFourierMode d m).val x.val
    rw [periodicFourierMode_iteratedDeriv]
    change periodicFourierCoefficient d (periodicIteratedDeriv d n f) m *
      fourier m (x.val : AddCircle d) = periodicFourierCoefficient d f m *
        (periodicFrequency d m ^ n * (periodicFourierMode d m).val x.val)
    rw [periodicFourierMode_circle, periodicFourierCoefficient_iterated_all]
    ring
  have hvalue : circleRestriction d (periodicCircleFunction d g) = periodicDerivativeLM d n f := by
    apply ContinuousMap.ext
    intro x
    exact periodicCircleFunction_coe d g x.val
  simp_rw [he, hvalue] at hsum
  rw [HasSum] at hsum
  refine hsum.congr' (Eventually.of_forall fun s => ?_)
  change (∑ m ∈ s, periodicDerivativeLM d n (periodicFourierCoefficient d f m •
    periodicFourierMode d m)) = periodicDerivativeLM d n (∑ m ∈ s,
      periodicFourierCoefficient d f m • periodicFourierMode d m)
  exact (map_sum (periodicDerivativeLM d n) _ _).symm


theorem smoothPeriodic_withDerivativeSeminorms :
    WithSeminorms (periodicDerivativeSeminorms d) := by
  rw [smoothPeriodic_topology_eq_derivative d]
  exact periodicDerivative_withSeminorms d

/-- The cyclic exponentials of Remark 4.2.1.8 are unbounded for every
positive period. Adapted from mccorvie/riemann-masullo, commit 99f18d0 (Apache-2.0). -/
theorem periodicFourierMode_not_bounded :
    ¬ IsVonNBounded ℂ (range (periodicFourierMode d)) := by
  intro h
  let w := smoothPeriodic_withDerivativeSeminorms d
  letI : IsTopologicalAddGroup (SmoothPeriodic d) := w.topologicalAddGroup
  letI : ContinuousSMul ℂ (SmoothPeriodic d) := w.continuousSMul
  obtain ⟨r, _, hr⟩ := w.isVonNBounded_iff_seminorm_bounded.mp h ⟨1, 0⟩
  let c := 2 * Real.pi / d
  have hc : 0 < c := div_pos Real.two_pi_pos (period_pos d)
  obtain ⟨n, hn⟩ := exists_nat_gt (r / c)
  let m : ℤ := n
  have hfreq : r < ‖periodicFrequency d m‖ := by
    rw [periodicFrequency_norm, abs_of_nonneg (by positivity : 0 ≤ (m : ℝ))]
    change r < c * (m : ℝ)
    rw [mul_comm]
    exact (div_lt_iff₀ hc).mp (by exact_mod_cast hn)
  have hder := iteratedDeriv_le_periodicDerivativeNorm (period_pos d) (periodicFourierMode d m) 1 0
  rw [periodicFourierMode_iteratedDeriv, pow_one, norm_mul, periodicFourierMode_norm, mul_one] at hder
  exact (hfreq.trans_le hder).not_gt (hr _ ⟨m, rfl⟩)

/-- On each bounded set, all summands in a dual Fourier expansion have a
common summable majorant. -/
private theorem periodicFourierDual_majorant (L : StrongDual ℂ (SmoothPeriodic d))
    {B : Set (SmoothPeriodic d)} (hB : IsVonNBounded ℂ B) :
    ∃ u : ℤ → ℝ, Summable u ∧ (∀ m, 0 ≤ u m) ∧
      ∀ m f, f ∈ B → ‖(L (periodicFourierMode d m) • periodicFourierCoefficientCLM d m) f‖ ≤ u m := by
  classical
  have hW := smoothPeriodic_withDerivativeSeminorms d
  letI : IsTopologicalAddGroup (SmoothPeriodic d) := hW.topologicalAddGroup
  letI : ContinuousSMul ℂ (SmoothPeriodic d) := hW.continuousSMul
  let p := periodicDerivativeSeminorms d
  let q := (normSeminorm ℂ ℂ).comp L.toLinearMap
  have hq : Continuous q := continuous_norm.comp L.continuous
  obtain ⟨s, C, _, hC⟩ := Seminorm.bound_of_continuous hW q hq
  choose M hM hBbound using hW.isVonNBounded_iff_seminorm_bounded.mp hB
  let M₀ := M ⟨0, 0⟩
  let D := (d / (2 * Real.pi)) ^ 2 * ∑ i ∈ s, M ⟨i.1 + 2, 0⟩
  let u (m : ℤ) := (C : ℝ) *
    ((if m = 0 then (s.card : ℝ) * M₀ else 0) + D * inverseSquareFrequency m)
  have hu : Summable u := by
    apply Summable.mul_left
    apply Summable.add
    · exact summable_of_hasFiniteSupport ((finite_singleton (0 : ℤ)).subset (fun m hm => by
        by_contra hn
        exact hm (if_neg (fun h => hn h))))
    · exact (Real.summable_one_div_int_pow.mpr (by decide : 1 < (2 : ℕ))).mul_left D
  let v (m : ℤ) (f : SmoothPeriodic d) :=
    L (periodicFourierMode d m) * periodicFourierCoefficient d f m
  have hv (m : ℤ) (f : SmoothPeriodic d) (hf : f ∈ B) : ‖v m f‖ ≤ u m := by
    let y := periodicFourierCoefficient d f m • periodicFourierMode d m
    have hy : v m f = L y := by
      rw [map_smul, smul_eq_mul, mul_comm]
    rw [hy]
    have hsup : s.sup p y ≤ ∑ i ∈ s, p i y :=
      Seminorm.finset_sup_apply_le (Finset.sum_nonneg fun i _ => apply_nonneg _ _)
        (fun i hi => Finset.single_le_sum (fun j _ => apply_nonneg _ _) hi)
    refine (hC y).trans ?_
    change (C : ℝ) * (s.sup p) y ≤ _
    apply mul_le_mul_of_nonneg_left _ C.coe_nonneg
    refine hsup.trans ?_
    have hterm (i : ((_ : ℕ) × Fin 1)) (hi : i ∈ s) :
        p i y ≤ (if m = 0 then M₀ else 0) +
          (d / (2 * Real.pi)) ^ 2 * M ⟨i.1 + 2, 0⟩ * inverseSquareFrequency m := by
      refine (periodicTerm_norm_le d f i.1 m).trans ?_
      have h0 : ‖periodicDerivativeLM d 0 f‖ ≤ M₀ := (hBbound ⟨0, 0⟩ f hf).le
      have h2 : ‖periodicDerivativeLM d (i.1 + 2) f‖ ≤ M ⟨i.1 + 2, 0⟩ :=
        (hBbound ⟨i.1 + 2, 0⟩ f hf).le
      have he : (if m = 0 then ‖periodicDerivativeLM d 0 f‖ else 0) ≤
          (if m = 0 then M₀ else 0) := by split <;> simp_all
      exact add_le_add he (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 (by positivity))
        (by unfold inverseSquareFrequency; positivity))
    refine (Finset.sum_le_sum hterm).trans_eq ?_
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, Finset.sum_const]
    simp only [nsmul_eq_mul, D]
    split <;> simp
  refine ⟨u, hu, fun m => ?_, fun m f hf => hv m f hf⟩
  have hM₀ : 0 ≤ M₀ := (hM ⟨0, 0⟩).le
  have hD : 0 ≤ D := mul_nonneg (sq_nonneg _)
    (Finset.sum_nonneg fun i _ => (hM ⟨i.1 + 2, 0⟩).le)
  have hi : 0 ≤ inverseSquareFrequency m := by unfold inverseSquareFrequency; positivity
  exact mul_nonneg C.coe_nonneg (add_nonneg (by split <;> positivity) (mul_nonneg hD hi))

/-- The Fourier coefficient functionals give the unconditional expansion
in the strong dual, with uniform convergence on every bounded set. -/
theorem periodicFourierDual_hasSum (L : StrongDual ℂ (SmoothPeriodic d)) :
    HasSum (fun m : ℤ => L (periodicFourierMode d m) • periodicFourierCoefficientCLM d m) L := by
  classical
  rw [HasSum]
  apply (UniformConvergenceCLM.tendsto_iff_tendstoUniformlyOn (RingHom.id ℂ) ℂ
    {B : Set (SmoothPeriodic d) | IsVonNBounded ℂ B}).mpr
  intro B hB
  obtain ⟨u, hu, _, hv⟩ := periodicFourierDual_majorant d L hB
  let v (m : ℤ) (f : SmoothPeriodic d) :=
    L (periodicFourierMode d m) * periodicFourierCoefficient d f m
  have hsum : HasSumUniformlyOn v (fun f => ∑' m, v m f) B :=
    HasSumUniformlyOn.of_norm_le_summable hu hv
  have he (f : SmoothPeriodic d) : HasSum (fun m => v m f) (L f) := by
    have hm := L.hasSum (periodicFourierSeries_hasSum d f)
    have heq : (fun m : ℤ => L (periodicFourierCoefficient d f m • periodicFourierMode d m)) =
        (fun m : ℤ => v m f) := by
      funext m
      rw [map_smul, smul_eq_mul]
      exact mul_comm _ _
    rwa [heq] at hm
  have hlim := (hasSumUniformlyOn_iff_tendstoUniformlyOn.mp hsum).congr_right
    (fun f _ => (he f).tsum_eq)
  refine hlim.congr (Eventually.of_forall fun s f hf => ?_)
  change (∑ m ∈ s, (L (periodicFourierMode d m) • periodicFourierCoefficientCLM d m) f) =
    (∑ m ∈ s, L (periodicFourierMode d m) • periodicFourierCoefficientCLM d m) f
  exact (sum_apply ..).symm


/-- Fourier coefficients are biorthogonal to the Fourier modes. -/
theorem periodicFourierCoefficientCLM_mode (n m : ℤ) :
    periodicFourierCoefficientCLM d m (periodicFourierMode d n) =
      Pi.single (M := fun _ : ℤ => ℂ) n 1 m :=
  periodicFourierMode_coefficient d n m

/-- Absolute summability in each continuous seminorm of the strong dual. -/
theorem periodicFourierDual_absolute (L : StrongDual ℂ (SmoothPeriodic d))
    (q : Seminorm ℂ (StrongDual ℂ (SmoothPeriodic d))) (hq : Continuous q) :
    Summable (fun m : ℤ => q (L (periodicFourierMode d m) • periodicFourierCoefficientCLM d m)) := by
  let hBasis : (𝓝 (0 : StrongDual ℂ (SmoothPeriodic d))).HasBasis
      (fun i : Set (SmoothPeriodic d) × ℝ => IsVonNBounded ℂ i.1 ∧ 0 < i.2)
      (fun i => {K | ∀ f ∈ i.1, ‖K f‖ < i.2}) :=
    ContinuousLinearMap.hasBasis_nhds_zero_of_basis
      (NormedAddGroup.nhds_zero_basis_norm_lt (E := ℂ))
  obtain ⟨⟨B, ε⟩, ⟨hB, hε⟩, hsub⟩ := hBasis.mem_iff.mp (Seminorm.ball_mem_nhds hq zero_lt_one)
  obtain ⟨u, hu, h₀, hmajor⟩ := periodicFourierDual_majorant d L hB
  refine (hu.mul_left (2 / ε)).of_nonneg_of_le (fun m => apply_nonneg _ _) ?_
  intro m
  let K := L (periodicFourierMode d m) • periodicFourierCoefficientCLM d m
  change q K ≤ 2 / ε * u m
  by_contra! hn
  have hpos : 0 < q K := (mul_nonneg (by positivity) (h₀ m)).trans_lt hn
  let c : ℝ := 2 / q K
  have hc : 0 < c := by dsimp [c]; positivity
  have hpre : (c : ℂ) • K ∈ {J : StrongDual ℂ (SmoothPeriodic d) | ∀ f ∈ B, ‖J f‖ < ε} := by
    intro f hf
    change ‖(c : ℂ) * K f‖ < ε
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hc.le]
    refine (mul_le_mul_of_nonneg_left (hmajor m f hf) hc.le).trans_lt ?_
    dsimp [c]
    calc
      2 / q K * u m = (2 * u m) / q K := by ring
      _ < ε := (div_lt_iff₀ hpos).2 (by
        have hh := (div_lt_iff₀ hε).1 (show 2 * u m / ε < q K by rwa [div_mul_eq_mul_div] at hn)
        simpa [mul_comm] using hh)
  have hsmall := hsub hpre
  rw [Seminorm.mem_ball_zero, map_smul_eq_mul, Complex.norm_real, Real.norm_of_nonneg hc.le] at hsmall
  dsimp [c] at hsmall
  have htwo : 2 / q K * q K = 2 := div_mul_cancel₀ _ hpos.ne'
  rw [htwo] at hsmall
  norm_num at hsmall

/-- The Fourier coefficient functionals are equicontinuous on smooth periodic functions. -/
theorem periodicFourierCoefficients_equicontinuous :
    Equicontinuous (fun m : ℤ => fun f : SmoothPeriodic d => periodicFourierCoefficientCLM d m f) := by
  intro f
  apply ((𝓝 f).basis_sets.equicontinuousAt_iff Metric.uniformity_basis_dist).2
  intro ε hε
  let P := periodicDerivativeSeminorms d ⟨0, 0⟩
  have hW := smoothPeriodic_withDerivativeSeminorms d
  letI : IsTopologicalAddGroup (SmoothPeriodic d) := hW.topologicalAddGroup
  have hcont : Continuous (fun g : SmoothPeriodic d => P (f - g)) :=
    (hW.continuous_seminorm ⟨0, 0⟩).comp (continuous_const.sub continuous_id)
  refine ⟨{g | P (f - g) < ε}, ?_, ?_⟩
  · have hh : Set.Iio ε ∈ 𝓝 (P (f - f)) := by simpa using (Iio_mem_nhds hε)
    exact hcont.continuousAt hh
  · intro g hg m
    change dist (periodicFourierCoefficientCLM d m f) (periodicFourierCoefficientCLM d m g) < ε
    rw [dist_eq_norm, ← map_sub]
    exact (periodicFourierCoefficient_norm_le d (f - g) m).trans_lt hg

/-- The Fourier coefficient functionals form a bounded subset of the strong dual. -/
theorem periodicFourierCoefficients_strongBounded :
    IsVonNBounded ℂ (range (periodicFourierCoefficientCLM d)) := by
  apply (ContinuousLinearMap.hasBasis_nhds_zero_of_basis NormedAddGroup.nhds_zero_basis_norm_lt).isVonNBounded_iff.mpr
  rintro ⟨B, ε⟩ ⟨hB, hε⟩
  obtain ⟨M, hM, hMb⟩ := (smoothPeriodic_withDerivativeSeminorms d).isVonNBounded_iff_seminorm_bounded.mp hB ⟨0, 0⟩
  rw [absorbs_iff_norm]
  refine ⟨(M + 1) / ε, fun c hc => ?_⟩
  have hc₀ : 0 < ‖c‖ := (div_pos (by positivity) hε).trans_le hc
  rintro K ⟨m, rfl⟩
  refine ⟨c⁻¹ • periodicFourierCoefficientCLM d m, ?_, smul_inv_smul₀ (norm_pos_iff.mp hc₀) _⟩
  intro f hf
  change ‖c⁻¹ * periodicFourierCoefficient d f m‖ < ε
  rw [norm_mul, norm_inv, ← div_eq_inv_mul, div_lt_iff₀ hc₀]
  have hMl : ‖periodicDerivativeLM d 0 f‖ < M := hMb f hf
  have hh := calc
    ‖periodicFourierCoefficient d f m‖ ≤ ‖periodicDerivativeLM d 0 f‖ :=
      periodicFourierCoefficient_norm_le d f m
    _ < M := hMl
    _ ≤ ε * ‖c‖ := by
      have := (div_le_iff₀ hε).mp hc
      linarith
  exact hh

/-- The Fourier coefficient using the Haar measure of mass equal to the period. -/
theorem periodicFourierCoefficient_quotientHaar (f : SmoothPeriodic d) (m : ℤ) :
    periodicFourierCoefficient d f m =
      (1 / d : ℝ) • ∫ t : AddCircle d, fourier (-m) t • periodicCircleFunction d f t := by
  rw [periodicFourierCoefficient, fourierCoeff, integral_haarAddCircle, one_div]

/-- Continuity and biorthogonality give uniqueness of the primal coordinates. -/
theorem periodicFourierSeries_unique (f : SmoothPeriodic d) (c : ℤ → ℂ)
    (h : HasSum (fun m => c m • periodicFourierMode d m) f) (n : ℤ) :
    c n = periodicFourierCoefficient d f n := by
  classical
  let A := periodicFourierCoefficientCLM d n
  have hs := A.hasSum h
  have hz (m : ℤ) (hm : m ≠ n) : A (c m • periodicFourierMode d m) = 0 := by
    simp [A, periodicFourierCoefficientCLM_mode, Pi.single_eq_of_ne (Ne.symm hm)]
  have hn : A (c n • periodicFourierMode d n) = c n := by
    simp [A, periodicFourierCoefficientCLM_mode]
  exact hn ▸ (hasSum_single n hz).unique hs

/-- Evaluation at Fourier modes gives uniqueness of the dual coordinates. -/
theorem periodicFourierDual_unique (L : StrongDual ℂ (SmoothPeriodic d)) (c : ℤ → ℂ)
    (h : HasSum (fun m => c m • periodicFourierCoefficientCLM d m) L) (n : ℤ) :
    c n = L (periodicFourierMode d n) := by
  classical
  let A : StrongDual ℂ (SmoothPeriodic d) →+ ℂ :=
    ⟨⟨fun K => K (periodicFourierMode d n), rfl⟩, fun _ _ => rfl⟩
  letI : ContinuousSMul ℂ (SmoothPeriodic d) :=
    (smoothPeriodic_withDerivativeSeminorms d).continuousSMul
  have hA : Continuous A := continuous_eval_const (periodicFourierMode d n)
  have hs := h.map A hA
  have hz (m : ℤ) (hm : m ≠ n) : A (c m • periodicFourierCoefficientCLM d m) = 0 := by
    change c m * periodicFourierCoefficientCLM d m (periodicFourierMode d n) = 0
    simp [periodicFourierCoefficientCLM_mode, Pi.single_eq_of_ne hm]
  have hn : A (c n • periodicFourierCoefficientCLM d n) = c n := by
    change c n * periodicFourierCoefficientCLM d n (periodicFourierMode d n) = c n
    simp [periodicFourierCoefficientCLM_mode]
  exact hn ▸ (hasSum_single n hz).unique hs

/-- The Fourier coefficient in the original positive-real coordinate.
The factor `t⁻¹` is the logarithmic Haar density. -/
theorem periodicFourierCoefficient_multiplicative_interval (f : SmoothPeriodic d) (m : ℤ) :
    periodicFourierCoefficient d f m =
      (1 / d : ℝ) • ∫ t in (1 : ℝ)..Real.exp d, t⁻¹ •
        (f.val (Real.log t) * Complex.exp (-periodicFrequency d m * (Real.log t : ℂ))) := by
  let g (t : ℝ) := t⁻¹ • (f.val (Real.log t) * Complex.exp (-periodicFrequency d m * (Real.log t : ℂ)))
  have hg : ContinuousOn g (Real.exp '' uIcc (0 : ℝ) d) := by
    intro t ht
    obtain ⟨x, _, rfl⟩ := ht
    have hn := (Real.exp_pos x).ne'
    have hl := Real.continuousAt_log hn
    exact ((continuousAt_id.inv₀ hn).smul
      ((f.property.1.continuous.continuousAt.comp hl).mul
        (Complex.continuous_exp.continuousAt.comp
          (continuousAt_const.mul (Complex.continuous_ofReal.continuousAt.comp hl))))).continuousWithinAt
  have he := intervalIntegral.integral_deriv_smul_comp'
    (fun x (_ : x ∈ uIcc (0 : ℝ) d) => Real.hasDerivAt_exp x)
    Real.continuous_exp.continuousOn hg
  rw [Real.exp_zero] at he
  rw [periodicFourierCoefficient_interval]
  change _ = (1 / d : ℝ) • ∫ t in (1 : ℝ)..Real.exp d, g t
  rw [← he]
  apply congrArg ((1 / d : ℝ) • ·)
  apply intervalIntegral.integral_congr
  intro t ht
  change fourier (-m) (t : AddCircle d) • f.val t = Real.exp t • ((Real.exp t)⁻¹ •
      (f.val (Real.log (Real.exp t)) * Complex.exp (-periodicFrequency d m * (Real.log (Real.exp t) : ℂ))))
  rw [Real.log_exp, smul_smul, mul_inv_cancel₀ (Real.exp_pos t).ne', one_smul]
  rw [smul_eq_mul, mul_comm, ← periodicFourierMode_circle d (-m) t, periodicFourierMode_apply]
  congr 2
  unfold periodicFrequency
  push_cast
  ring

end
end Masullo
