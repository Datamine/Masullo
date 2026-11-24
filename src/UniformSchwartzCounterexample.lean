import Mathlib.Analysis.LocallyConvex.Bounded
import PeriodicFourierBasis
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.SpecialFunctions.Sqrt

open Filter Set Topology
open scoped BoundedContinuousFunction ContDiff SchwartzMap

namespace Masullo

noncomputable section

private def cuspBump : ContDiffBump (0 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩

private def cuspLimit (x : ℝ) : ℂ := Complex.ofReal (cuspBump x * |x|)

private theorem cuspLimit_not_differentiable : ¬ DifferentiableAt ℝ cuspLimit 0 := by
  intro h
  have hd := Complex.reCLM.differentiableAt.comp 0 h
  apply not_differentiableAt_abs_zero
  apply hd.congr_of_eventuallyEq
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (show (0 : ℝ) < 1 by norm_num)] with x hx
  have h1 : cuspBump x = 1 := cuspBump.one_of_mem_closedBall (Metric.ball_subset_closedBall hx)
  simp [cuspLimit, h1]

set_option maxHeartbeats 900000 in
private def smoothCusp (a : ℝ) (ha : 0 < a) : 𝓢(ℝ, ℂ) := by
  let h (x : ℝ) : ℝ := cuspBump x * Real.sqrt (x ^ 2 + a ^ 2)
  have hs : ContDiff ℝ ∞ (fun x : ℝ => Real.sqrt (x ^ 2 + a ^ 2)) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    have hg : ContDiff ℝ ∞ (fun t : ℝ => t ^ 2 + a ^ 2) := (contDiff_id.pow 2).add contDiff_const
    exact (Real.contDiffAt_sqrt (ne_of_gt (show 0 < x ^ 2 + a ^ 2 by positivity))).comp x
      hg.contDiffAt
  have hc : ContDiff ℝ ∞ h := cuspBump.contDiff.mul hs
  have hk : HasCompactSupport h := cuspBump.hasCompactSupport.mul_right
  have hk' : HasCompactSupport (fun x => Complex.ofReal (h x)) := hk.comp_left (g := Complex.ofReal) Complex.ofReal_zero
  exact hk'.toSchwartzMap (Complex.ofRealCLM.contDiff.comp hc)

private theorem smoothCusp_apply (a : ℝ) (ha : 0 < a) (x : ℝ) :
    smoothCusp a ha x = Complex.ofReal (cuspBump x * Real.sqrt (x ^ 2 + a ^ 2)) := rfl

private theorem smoothAbs_error (a : ℝ) (ha : 0 < a) (x : ℝ) :
    0 ≤ Real.sqrt (x ^ 2 + a ^ 2) - |x| ∧ Real.sqrt (x ^ 2 + a ^ 2) - |x| ≤ a := by
  have h0 : 0 ≤ x ^ 2 + a ^ 2 := by positivity
  have hLo : |x| ≤ Real.sqrt (x ^ 2 + a ^ 2) := by
    apply le_of_pow_le_pow_left₀ two_ne_zero (by positivity)
    rw [sq_abs, Real.sq_sqrt h0]
    nlinarith [sq_nonneg a]
  have hHi : Real.sqrt (x ^ 2 + a ^ 2) ≤ |x| + a := by
    apply le_of_pow_le_pow_left₀ two_ne_zero (by positivity)
    rw [Real.sq_sqrt h0, add_sq, sq_abs]
    nlinarith [mul_nonneg (abs_nonneg x) ha.le]
  exact ⟨sub_nonneg.mpr hLo, sub_le_iff_le_add.mpr (by simpa only [add_comm a |x|] using hHi)⟩

private theorem smoothCusp_error (a : ℝ) (ha : 0 < a) (x : ℝ) :
    ‖smoothCusp a ha x - cuspLimit x‖ ≤ a := by
  obtain ⟨h0, h1⟩ := smoothAbs_error a ha x
  rw [smoothCusp_apply, cuspLimit, ← Complex.ofReal_sub, ← mul_sub]
  rw [Complex.norm_real (cuspBump x * (Real.sqrt (x ^ 2 + a ^ 2) - |x|)),
    Real.norm_eq_abs, abs_mul, abs_of_nonneg cuspBump.nonneg, abs_of_nonneg h0]
  exact (mul_le_mul_of_nonneg_right cuspBump.le_one h0).trans (by simpa only [one_mul] using h1)

private def boundCusp : ℝ →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup cuspLimit
    (Complex.ofRealCLM.continuous.comp (cuspBump.continuous.mul continuous_abs)) 2 fun x => by
    change ‖Complex.ofReal (cuspBump x * |x|)‖ ≤ 2
    rw [Complex.norm_real (cuspBump x * |x|), Real.norm_eq_abs, abs_mul,
      abs_of_nonneg cuspBump.nonneg, abs_abs]
    by_cases hx : |x| ≤ 2
    · exact (mul_le_mul_of_nonneg_right cuspBump.le_one (abs_nonneg x)).trans (by simpa using hx)
    · have hz : cuspBump x = 0 := cuspBump.zero_of_le_dist (by
        change 2 ≤ dist x 0
        rw [Real.dist_eq, sub_zero]
        exact (lt_of_not_ge hx).le)
      rw [hz, zero_mul]
      norm_num

/-- The scalar Schwartz space is incomplete for uniform convergence of values.
The approximating Schwartz functions have a uniform limit with a cusp at zero. -/
theorem schwartz_uniformValue_incomplete :
    ∃ f : ℕ → 𝓢(ℝ, ℂ), ∃ h : ℝ →ᵇ ℂ,
      Tendsto (fun n => SchwartzMap.toBoundedContinuousFunctionCLM ℂ ℝ ℂ (f n)) atTop (𝓝 h) ∧
      ¬ ∃ g : 𝓢(ℝ, ℂ), SchwartzMap.toBoundedContinuousFunctionCLM ℂ ℝ ℂ g = h := by
  let a (n : ℕ) : ℝ := ((n : ℝ) + 1)⁻¹
  have ha (n : ℕ) : 0 < a n := by dsimp [a]; positivity
  refine ⟨fun n => smoothCusp (a n) (ha n), boundCusp, ?_, ?_⟩
  · have hlim : Tendsto a atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hlim ε hε
    refine ⟨N, fun n hn => lt_of_le_of_lt (b := a n) ?_ ?_⟩
    · rw [dist_eq_norm]
      exact (BoundedContinuousFunction.norm_le (ha n).le).mpr (smoothCusp_error (a n) (ha n))
    · simpa [Real.dist_eq, abs_of_pos (ha n)] using hN n hn
  · rintro ⟨g, hg⟩
    apply cuspLimit_not_differentiable
    have hs : ContDiff ℝ 1 (g : ℝ → ℂ) := g.smooth 1
    apply (hs.differentiable_one 0).congr_of_eventuallyEq
    exact .of_forall fun x => (congrArg (fun w : ℝ →ᵇ ℂ => w x) hg).symm

private theorem not_quasiComplete_range_of_limit
    {E V : Type*} [AddCommGroup E] [Module ℂ E] [NormedAddCommGroup V] [NormedSpace ℂ V]
    (J : E →ₗ[ℂ] V) {f : ℕ → E} {L : V}
    (hL : Tendsto (fun n => J (f n)) atTop (𝓝 L))
    (hnot : ¬ ∃ g : E, J g = L) : ¬ QuasiCompleteSpace ℂ J.range := by
  intro h
  let u (n : ℕ) : J.range := ⟨J (f n), mem_range_self (f n)⟩
  have hu : CauchySeq u := by
    refine Metric.cauchySeq_iff.mpr fun ε hε => ?_
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hL.cauchySeq ε hε
    exact ⟨N, fun n hn m hm => hN n hn m hm⟩
  have hb : Bornology.IsVonNBounded ℂ (closure (range u)) :=
    (NormedSpace.isVonNBounded_iff (𝕜 := ℂ)).mpr hu.isBounded_range.closure
  obtain ⟨x, -, hx⟩ := cauchySeq_tendsto_of_isComplete
    (h.quasiComplete hb isClosed_closure) (fun n => subset_closure (mem_range_self n)) hu
  have he : (x : V) = L := tendsto_nhds_unique (continuous_subtype_val.continuousAt.tendsto.comp hx) hL
  obtain ⟨g, hg⟩ := x.property
  exact hnot ⟨g, hg.trans he⟩

/-- Even quasi-completeness fails for the uniform topology on scalar Schwartz functions. -/
theorem schwartz_uniformValue_not_quasiComplete :
    ¬ QuasiCompleteSpace ℂ (SchwartzMap.toBoundedContinuousFunctionCLM ℂ ℝ ℂ).range := by
  obtain ⟨f, L, hL, hnot⟩ := schwartz_uniformValue_incomplete
  exact not_quasiComplete_range_of_limit (SchwartzMap.toBoundedContinuousFunctionCLM ℂ ℝ ℂ).toLinearMap
    hL hnot

private def periodicCusp (x : ℝ) : ℂ := Complex.ofReal (|Real.sin x|)

private theorem periodicCusp_not_differentiable : ¬ DifferentiableAt ℝ periodicCusp 0 := by
  intro h
  have hd := Complex.reCLM.differentiableAt.comp 0 h
  have ha : DifferentiableAt ℝ Real.arcsin 0 :=
    (Real.hasDerivAt_arcsin (by norm_num) (by norm_num)).differentiableAt
  have hda : DifferentiableAt ℝ (fun x => Complex.re (periodicCusp (Real.arcsin x))) 0 := by
    have hd' : DifferentiableAt ℝ (Complex.reCLM ∘ periodicCusp) (Real.arcsin 0) := by
      simpa only [Real.arcsin_zero] using hd
    exact hd'.comp 0 ha
  apply not_differentiableAt_abs_zero
  apply hda.congr_of_eventuallyEq
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (show (0 : ℝ) < 1 by norm_num)] with x hx
  have hx' : |x| < 1 := by simpa [Metric.mem_ball, Real.dist_eq] using hx
  have hs := Real.sin_arcsin (abs_lt.mp hx').1.le (abs_lt.mp hx').2.le
  simp [periodicCusp, hs]

private theorem periodicCusp_periodic : Function.Periodic periodicCusp (2 * Real.pi) :=
  fun x => by simp only [periodicCusp, Real.sin_add_two_pi]

local instance : Fact (0 < 2 * Real.pi) := ⟨mul_pos two_pos Real.pi_pos⟩

private def periodicCuspCircle : C(AddCircle (2 * Real.pi), ℂ) := by
  exact ⟨periodicCusp_periodic.lift, QuotientAddGroup.isOpenQuotientMap_mk.continuous_comp_iff.mp
    (Complex.ofRealCLM.continuous.comp (continuous_abs.comp Real.continuous_sin))⟩

private theorem periodicCuspCircle_apply_coe (x : ℝ) :
    periodicCuspCircle (x : AddCircle (2 * Real.pi)) = periodicCusp x := by
  exact periodicCusp_periodic.lift_coe x

private def smoothPeriodicCusp (a : ℝ) (ha : 0 < a) : SmoothPeriodic (2 * Real.pi) := by
  let f (x : ℝ) : ℝ := Real.sqrt ((Real.sin x) ^ 2 + a ^ 2)
  have hf : ContDiff ℝ ∞ f := by
    rw [contDiff_iff_contDiffAt]
    intro x
    have hg : ContDiff ℝ ∞ (fun t : ℝ => (Real.sin t) ^ 2 + a ^ 2) :=
      (Real.contDiff_sin.pow 2).add contDiff_const
    exact (Real.contDiffAt_sqrt (ne_of_gt (show 0 < (Real.sin x) ^ 2 + a ^ 2 by positivity))).comp x
      hg.contDiffAt
  exact ⟨fun x => Complex.ofReal (f x), Complex.ofRealCLM.contDiff.comp hf,
    fun x => by simp only [f, Real.sin_add_two_pi]⟩

/-- The same failure of completeness occurs on the circle with the sup norm. -/
theorem periodic_uniformValue_incomplete :
    ∃ f : ℕ → SmoothPeriodic (2 * Real.pi), ∃ h : C(AddCircle (2 * Real.pi), ℂ),
      Tendsto (fun n => periodicCircleFunction (2 * Real.pi) (f n)) atTop (𝓝 h) ∧
      ¬ ∃ g : SmoothPeriodic (2 * Real.pi), periodicCircleFunction (2 * Real.pi) g = h := by
  let a (n : ℕ) : ℝ := ((n : ℝ) + 1)⁻¹
  have ha (n : ℕ) : 0 < a n := by dsimp [a]; positivity
  refine ⟨fun n => smoothPeriodicCusp (a n) (ha n), periodicCuspCircle, ?_, ?_⟩
  · have hlim : Tendsto a atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hlim ε hε
    refine ⟨N, fun n hn => lt_of_le_of_lt (b := a n) ?_ ?_⟩
    · rw [dist_eq_norm]
      apply (ContinuousMap.norm_le _ (ha n).le).mpr
      intro z
      obtain ⟨x, rfl⟩ := Quotient.exists_rep z
      simp only [ContinuousMap.sub_apply, periodicCircleFunction_coe, periodicCuspCircle_apply_coe]
      change ‖Complex.ofReal (Real.sqrt ((Real.sin x) ^ 2 + (a n) ^ 2)) -
        Complex.ofReal (|Real.sin x|)‖ ≤ a n
      obtain ⟨h0, h1⟩ := smoothAbs_error (a n) (ha n) (Real.sin x)
      rwa [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0]
    · simpa [Real.dist_eq, abs_of_pos (ha n)] using hN n hn
  · rintro ⟨g, hg⟩
    apply periodicCusp_not_differentiable
    have hs : ContDiff ℝ ∞ (g.val : ℝ → ℂ) := g.property.1
    apply (hs.differentiable (by simp) 0).congr_of_eventuallyEq
    filter_upwards with x
    simpa only [periodicCircleFunction_coe, periodicCuspCircle_apply_coe] using
      (congrArg (fun w : C(AddCircle (2 * Real.pi), ℂ) => w (x : AddCircle (2 * Real.pi))) hg).symm

/-- Values of a smooth periodic function on the circle, with the uniform topology in the codomain. -/
def circlePeriodicValue : SmoothPeriodic (2 * Real.pi) →ₗ[ℂ] C(AddCircle (2 * Real.pi), ℂ) where
  toFun := periodicCircleFunction (2 * Real.pi)
  map_add' f g := by
    apply ContinuousMap.ext
    intro z
    obtain ⟨x, rfl⟩ := Quotient.exists_rep z
    simp only [ContinuousMap.add_apply, periodicCircleFunction_coe]
    rfl
  map_smul' c f := by
    apply ContinuousMap.ext
    intro z
    obtain ⟨x, rfl⟩ := Quotient.exists_rep z
    simp only [ContinuousMap.smul_apply, periodicCircleFunction_coe]
    rfl

/-- The scalar space of smooth functions on the circle is also not quasi-complete
for the uniform topology of values. -/
theorem periodic_uniformValue_not_quasiComplete : ¬ QuasiCompleteSpace ℂ circlePeriodicValue.range := by
  obtain ⟨f, L, hL, hnot⟩ := periodic_uniformValue_incomplete
  exact not_quasiComplete_range_of_limit circlePeriodicValue hL hnot

end
end Masullo
