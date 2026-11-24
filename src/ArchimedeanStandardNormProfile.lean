import ArchimedeanNormFibreFlow
import ExponentialDecayStructure
import Mathlib.Analysis.Calculus.ParametricIntegral

open Filter Function MeasureTheory NumberField NumberField.Units.dirichletUnitTheorem Set Topology
open scoped SchwartzMap NumberField Classical ContDiff

namespace Masullo
noncomputable section

variable (F : Type*) [Field F] [NumberField F]

private theorem archNormRay_logCoordinate_continuous (w : InfinitePlace F) :
    Continuous (fun t => fullArchLog F (archNormRay F t) w) := by
  have hv : Continuous (fun u : ℝ => (archNormRay F u).val) :=
    (Units.continuous_val : Continuous (Units.val : InfiniteIdeles F → InfiniteAdeleRing F)).comp
      (archNormRay_continuous F)
  have hC : Continuous (fun u : ℝ => ‖(archNormRay F u).val w‖) := ((continuous_apply w).comp hv).norm
  apply continuous_iff_continuousAt.mpr
  intro t
  have h := norm_ne_zero_iff.mpr (infiniteCoord_nonzero F (archNormRay F t) w)
  have hl : ContinuousAt (fun u : ℝ => Real.log ‖(archNormRay F u).val w‖) t :=
    (Real.continuousAt_log (x := ‖(archNormRay F t).val w‖) h).comp
      (f := fun u : ℝ => ‖(archNormRay F u).val w‖) hC.continuousAt
  exact continuous_const.continuousAt.mul hl

private theorem min_exp_neg_le_of_shift {x y : ℝ} (h : |x - y| ≤ 1) :
    min 1 (Real.exp (-x)) ≤ Real.exp 1 * min 1 (Real.exp (-y)) := by
  rw [mul_min_of_nonneg _ _ (Real.exp_pos 1).le, mul_one, ← Real.exp_add]
  apply min_le_min (Real.one_le_exp zero_le_one)
  apply Real.exp_le_exp.mpr
  linarith only [(abs_le.mp h).1]

/-- The standard average evaluated on the canonical norm section. -/
def archStandardNormProfile [MeasurableSpace (archNormOne F)]
    (μ : Measure (archNormOne F)) {J : Type*} [Fintype J] (r : J → InfiniteIdeles F)
    (χ : InfiniteIdeles F →ₜ* Circle) (f : 𝓢(mixedEmbedding.mixedSpace F, ℂ)) (t : ℝ) : ℂ :=
  ∑ j, ∫ g : archNormOne F,
    f (InfiniteAdeleRing.ringEquiv_mixedSpace F ((r j * g.val)⁻¹ * archNormRay F t).val) * (χ (r j * g.val) : ℂ) ∂μ

/-- Differentiation of the archimedean norm profile is differentiation of
the underlying Schwartz test by the normalized Euler field. -/
theorem archStandardNormProfile_hasDerivAt
    [MeasurableSpace (archNormOne F)] [BorelSpace (archNormOne F)]
    (μ : Measure (archNormOne F)) [μ.IsHaarMeasure]
    {J : Type*} [Fintype J] (r : J → InfiniteIdeles F)
    (χ : InfiniteIdeles F →ₜ* Circle) (f : 𝓢(mixedEmbedding.mixedSpace F, ℂ)) (t : ℝ) :
    HasDerivAt (archStandardNormProfile F μ r χ f)
      (archStandardNormProfile F μ r χ (archNormRayEuler F f) t) t := by
  unfold archStandardNormProfile
  apply HasDerivAt.fun_sum
  intro j _
  let x := archNormRay F t
  let y := (r j)⁻¹ * x
  let a (g : archNormOne F) := (r j * g.val)⁻¹
  let U (v : 𝓢(mixedEmbedding.mixedSpace F, ℂ)) (s : ℝ) (g : archNormOne F) :=
    v (InfiniteAdeleRing.ringEquiv_mixedSpace F (a g * archNormRay F s).val) * (χ (r j * g.val) : ℂ)
  let D := archNormRayEuler F f
  have hInt (v : 𝓢(mixedEmbedding.mixedSpace F, ℂ)) (s : ℝ) : Integrable (U v s) μ := by
    obtain ⟨C, _, hC⟩ := archNormOne_standardAverage_logBound F μ r χ v
    exact (hC (archNormRay F s)).1 j
  let S := {s : ℝ | ∀ w : InfinitePlace F,
    |fullArchLog F (archNormRay F s) w - fullArchLog F x w| ≤ 1}
  have hs : S ∈ 𝓝 t := by
    apply eventually_all.mpr
    intro w
    have h := (archNormRay_logCoordinate_continuous F w).continuousAt.tendsto.eventually
      (Metric.ball_mem_nhds (fullArchLog F x w) zero_lt_one)
    exact h.mono fun s hs =>
      (by simpa only [Metric.mem_ball, Real.dist_eq] using hs :
        |fullArchLog F (archNormRay F s) w - fullArchLog F x w| < 1).le
  obtain ⟨C, hC, hSch⟩ := archSchwartz_fullArchLog_bound F D
  obtain ⟨c, -, hKi⟩ := archNormOne_logFibreKernel_integral F μ
  let B (g : archNormOne F) := archimedeanLogFibreKernel (max 0 (-Real.log ‖y.val‖))
    (fun w : {w : InfinitePlace F // w ≠ w₀} => fullArchLog F y w - (archRegulatorLog F g).toAdd w)
  have hBi : Integrable B μ := (hKi y).1
  let n := Fintype.card (InfinitePlace F)
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := U f) (F' := U D)
    (bound := fun g => (C * Real.exp 1 ^ n) * B g) hs (.of_forall fun s => (hInt f s).aestronglyMeasurable)
    (hInt f t) (hInt D t).aestronglyMeasurable (.of_forall fun g s hS => ?_)
    (hBi.const_mul _) (.of_forall fun g s _ => ?_)).2
  · have he (w : InfinitePlace F) :
        |fullArchLog F (a g * archNormRay F s) w - fullArchLog F (a g * x) w| ≤ 1 := by
      rw [fullArchLog_mul, fullArchLog_mul]
      change |(fullArchLog F (a g) w + fullArchLog F (archNormRay F s) w) -
        (fullArchLog F (a g) w + fullArchLog F x w)| ≤ 1
      rw [add_sub_add_left_eq_sub]
      exact hS w
    have hprod : (∏ w : InfinitePlace F, min 1 (Real.exp (-fullArchLog F (a g * archNormRay F s) w))) ≤
        Real.exp 1 ^ n * ∏ w : InfinitePlace F, min 1 (Real.exp (-fullArchLog F (a g * x) w)) := by
      rw [show Real.exp 1 ^ n = ∏ _w : InfinitePlace F, Real.exp 1 by simp [n], ← Finset.prod_mul_distrib]
      exact Finset.prod_le_prod (fun _ _ => le_min zero_le_one (Real.exp_pos _).le)
        (fun w _ => min_exp_neg_le_of_shift (he w))
    have hB : (∏ w : InfinitePlace F, min 1 (Real.exp (-fullArchLog F (a g * x) w))) ≤ B g := by
      rw [show a g * x = g.val⁻¹ * y from by simp only [a, y, mul_inv_rev, mul_assoc]]
      exact archLogFibre_product_le_kernel F y g
    change ‖D (InfiniteAdeleRing.ringEquiv_mixedSpace F (a g * archNormRay F s).val) * (χ (r j * g.val) : ℂ)‖ ≤ _
    rw [norm_mul, Circle.norm_coe, mul_one]
    calc
      _ ≤ _ := hSch (a g * archNormRay F s)
      _ ≤ C * (Real.exp 1 ^ n * ∏ w, min 1 (Real.exp (-fullArchLog F (a g * x) w))) := mul_le_mul_of_nonneg_left hprod hC
      _ = (C * Real.exp 1 ^ n) * ∏ w, min 1 (Real.exp (-fullArchLog F (a g * x) w)) := (mul_assoc _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hB (by positivity)
  · exact (archNormRay_test_hasDerivAt F f (a g) s).mul_const (χ (r j * g.val) : ℂ)

section IteratedDerivatives

variable [MeasurableSpace (archNormOne F)] [BorelSpace (archNormOne F)]
  (μ : Measure (archNormOne F)) [μ.IsHaarMeasure]
  {J : Type*} [Fintype J] (r : J → InfiniteIdeles F) (χ : InfiniteIdeles F →ₜ* Circle)

/-- The norm profile is smooth, with a Schwartz test at every derivative. -/
theorem archStandardNormProfile_contDiff (f : 𝓢(mixedEmbedding.mixedSpace F, ℂ)) :
    ContDiff ℝ ∞ (archStandardNormProfile F μ r χ f) := by
  apply contDiff_infty.mpr
  intro n
  induction n generalizing f with
  | zero => exact contDiff_zero.mpr (continuous_iff_continuousAt.mpr fun t =>
      (archStandardNormProfile_hasDerivAt F μ r χ f t).continuousAt)
  | succ n ih =>
    rw [Nat.cast_succ, contDiff_succ_iff_deriv]
    refine ⟨fun t => (archStandardNormProfile_hasDerivAt F μ r χ f t).differentiableAt, by simp, ?_⟩
    have hD : deriv (archStandardNormProfile F μ r χ f) =
        archStandardNormProfile F μ r χ (archNormRayEuler F f) :=
      funext fun t => (archStandardNormProfile_hasDerivAt F μ r χ f t).deriv
    rw [hD]
    exact ih _

/-- The logarithmic derivatives are obtained by iterating the Euler operator
before taking the same character-weighted average. -/
theorem archStandardNormProfile_iteratedDeriv (f : 𝓢(mixedEmbedding.mixedSpace F, ℂ)) (n : ℕ) :
    iteratedDeriv n (archStandardNormProfile F μ r χ f) =
      archStandardNormProfile F μ r χ ((archNormRayEuler F)^[n] f) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iteratedDeriv_succ, ih, Function.iterate_succ_apply']
    exact funext fun t => (archStandardNormProfile_hasDerivAt F μ r χ _ t).deriv

/-- Every logarithmic derivative satisfies the logarithmic and large-modulus
bounds along the norm section. -/
theorem archStandardNormProfile_derivatives_bounds (f : 𝓢(mixedEmbedding.mixedSpace F, ℂ)) (n k : ℕ) :
    (∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      ‖iteratedDeriv n (archStandardNormProfile F μ r χ f) t‖ ≤
        C * (1 + |t|) ^ (Fintype.card (InfinitePlace F) - 1)) ∧
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 ≤ t →
      ‖iteratedDeriv n (archStandardNormProfile F μ r χ f) t‖ ≤ C * Real.exp (-(k : ℝ) * t) := by
  rw [archStandardNormProfile_iteratedDeriv]
  let g := (archNormRayEuler F)^[n] f
  constructor
  · obtain ⟨C, hC, h⟩ := archNormOne_standardAverage_logBound F μ r χ g
    refine ⟨C, hC, fun t => ?_⟩
    exact (by simpa only [archStandardNormProfile, archNormRay_norm, Real.log_exp, g] using (h (archNormRay F t)).2)
  · obtain ⟨C, hC, h⟩ := archNormOne_standardAverage_forwardBound F μ r χ g k
    refine ⟨C, hC, fun t ht => ?_⟩
    have hx : 1 ≤ ‖(archNormRay F t).val‖ := by rw [archNormRay_norm]; exact Real.one_le_exp ht
    simpa only [archStandardNormProfile, archNormRay_norm, Real.log_exp, g] using h (archNormRay F t) hx

private theorem pow_mul_exp_neg_mul_le (a u : ℝ) (ha : 0 < a) (hu : 0 ≤ u) (m : ℕ) :
    u ^ m * Real.exp (-a * u) ≤ (m.factorial : ℝ) / a ^ m := by
  have h := Real.pow_div_factorial_le_exp (a * u) (mul_nonneg ha.le hu) m
  rw [mul_pow] at h
  have h' := (div_le_iff₀ (by positivity : 0 < (m.factorial : ℝ))).mp h
  rw [neg_mul, Real.exp_neg, ← div_eq_mul_inv]
  apply (div_le_div_iff₀ (Real.exp_pos _) (by positivity : 0 < a ^ m)).mpr
  nlinarith only [h']

/-- Every strictly positive norm weight gives a Schwartz profile on the log
line. This is the forward-decay replacement compatible with logarithmic
small-modulus growth. -/
theorem archStandardNormProfile_mem_positiveDecay (f : 𝓢(mixedEmbedding.mixedSpace F, ℂ)) :
    archStandardNormProfile F μ r χ f ∈ logExponentialDecaySubmodule (Ioi 0) := by
  let A := archStandardNormProfile F μ r χ f
  have hSmooth := archStandardNormProfile_contDiff F μ r χ f
  apply (Submodule.mem_iInf _).mpr
  intro a
  change logExponentialWeight (a : ℝ) A ∈ realSchwartzCoe.range
  apply (logExponentialWeight_mem_range_iff a hSmooth).mpr
  intro m n
  have ha : 0 < (a : ℝ) := a.property
  obtain ⟨N, hN⟩ := exists_nat_gt ((a : ℝ) + 1)
  let d := Fintype.card (InfinitePlace F) - 1
  obtain ⟨⟨D, hD, hleft⟩, ⟨E, hE, hright⟩⟩ := archStandardNormProfile_derivatives_bounds F μ r χ f n N
  let P := D * Real.exp a * ((m + d).factorial / (a : ℝ) ^ (m + d))
  let Q := E * m.factorial
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  refine ⟨P + Q, add_nonneg hP hQ, fun t => ?_⟩
  have hscaled : Real.exp (a.val * t) * (|t| ^ m * ‖iteratedDeriv n A t‖) ≤ P + Q := by
    rcases le_total 0 t with ht | ht
    · refine le_trans ?_ (le_add_of_nonneg_left hP)
      have hcoef : (a : ℝ) + 1 ≤ N := hN.le
      have hexp : Real.exp ((a.val - N) * t) ≤ Real.exp (-1 * t) := by
        apply Real.exp_le_exp.mpr
        nlinarith only [mul_nonneg (sub_nonneg.mpr hcoef) ht]
      rw [abs_of_nonneg ht]
      calc
        _ ≤ Real.exp (a.val * t) * (t ^ m * (E * Real.exp (-(N : ℝ) * t))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hright t ht) (by positivity)) (by positivity)
        _ = E * (t ^ m * Real.exp ((a.val - N) * t)) := by
          rw [show Real.exp ((a.val - N) * t) = Real.exp (a.val * t) * Real.exp (-(N : ℝ) * t) by
            rw [← Real.exp_add]; congr 1; ring]
          ring
        _ ≤ E * (t ^ m * Real.exp (-1 * t)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexp (by positivity)) hE
        _ ≤ Q := mul_le_mul_of_nonneg_left (by simpa using pow_mul_exp_neg_mul_le 1 t one_pos ht m) hE
    · refine le_trans ?_ (le_add_of_nonneg_right hQ)
      let u := -t
      have hu : 0 ≤ u := neg_nonneg.mpr ht
      have hpow : u ^ m * (1 + u) ^ d ≤ (1 + u) ^ (m + d) := by
        rw [pow_add]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hu (by linarith) _) (by positivity)
      rw [abs_of_nonpos ht]
      calc
        _ ≤ Real.exp (a.val * t) * (u ^ m * (D * (1 + u) ^ d)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (by simpa [u, abs_of_nonpos ht, A, d] using hleft t)
            (by positivity)) (by positivity)
        _ = (D * Real.exp a) * ((u ^ m * (1 + u) ^ d) * Real.exp (-a.val * (1 + u))) := by
          rw [show Real.exp (a.val * t) = Real.exp a * Real.exp (-a.val * (1 + u)) by
            rw [← Real.exp_add]; congr 1; dsimp [u]; ring]
          ring
        _ ≤ (D * Real.exp a) * ((1 + u) ^ (m + d) * Real.exp (-a.val * (1 + u))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpow (by positivity)) (by positivity)
        _ ≤ P := mul_le_mul_of_nonneg_left (pow_mul_exp_neg_mul_le a (1 + u) ha (by positivity) _) (by positivity)
  rw [Real.exp_neg, ← div_eq_mul_inv]
  exact (le_div_iff₀' (Real.exp_pos _)).mpr hscaled

end IteratedDerivatives

end
end Masullo
