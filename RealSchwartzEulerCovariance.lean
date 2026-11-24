import ArchimedeanSupportedEigen
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.MeanValue

open Filter Function Set Topology
open scoped Classical ContDiff SchwartzMap

namespace Masullo

noncomputable section

private abbrev Tests := 𝓢(ℝ, ℂ)

/-- The infinitesimal generator of positive real dilations on Schwartz tests. -/
def realSchwartzEuler : Tests →L[ℂ] Tests :=
  (SchwartzMap.smulLeftCLM ℂ (Complex.ofReal : ℝ → ℂ)).comp (SchwartzMap.derivCLM ℂ ℂ)

@[simp] theorem realSchwartzEuler_apply (f : Tests) (x : ℝ) :
    realSchwartzEuler f x = (x : ℂ) * deriv (f : ℝ → ℂ) x := by
  rw [realSchwartzEuler, ContinuousLinearMap.comp_apply,
    SchwartzMap.smulLeftCLM_apply_apply
      (Complex.hasTemperateGrowth_ofReal : Function.HasTemperateGrowth (Complex.ofReal : ℝ → ℂ)),
    SchwartzMap.derivCLM_apply, smul_eq_mul]

private theorem realSchwartzEuler_iteratedDeriv (f : Tests) (n : ℕ) (x : ℝ) :
    iteratedDeriv n (realSchwartzEuler f : ℝ → ℂ) x =
      (x : ℂ) * iteratedDeriv (n + 1) (f : ℝ → ℂ) x +
        (n : ℂ) * iteratedDeriv n (f : ℝ → ℂ) x := by
  have h (n : ℕ) : (iteratedDeriv n (realSchwartzEuler f : ℝ → ℂ)) =
      fun x : ℝ => (x : ℂ) * iteratedDeriv (n + 1) (f : ℝ → ℂ) x +
        (n : ℂ) * iteratedDeriv n (f : ℝ → ℂ) x := by
    induction n with
    | zero =>
      funext x
      simp [iteratedDeriv_one]
    | succ n ih =>
      funext x
      rw [iteratedDeriv_succ, ih]
      have hd (k : ℕ) : HasDerivAt (iteratedDeriv k (f : ℝ → ℂ))
          (iteratedDeriv (k + 1) (f : ℝ → ℂ) x) x := by
        rw [iteratedDeriv_succ]
        exact ((f.smooth (k + 1)).differentiable_iteratedDeriv' k x).hasDerivAt
      have hx : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 x := by
        simpa using (hasDerivAt_id x).ofReal_comp
      rw [((hx.fun_mul (hd (n + 1))).fun_add ((hd n).const_mul (n : ℂ))).deriv]
      simp only [Nat.cast_succ, one_mul]
      ring
  exact congrFun (h n) x

private def expDilationUnit (t : ℝ) : ℝˣ := Units.mk0 (Real.exp (-t)) (Real.exp_ne_zero _)

private def expDilation (f : Tests) (t : ℝ) : Tests :=
  archSchwartzDilation (expDilationUnit t) f

private theorem expDilation_apply (f : Tests) (t x : ℝ) :
    expDilation f t x = f (Real.exp t * x) := by
  rw [expDilation, archSchwartzDilation_apply, Units.val_inv_eq_inv_val]
  change f (x * (Real.exp (-t))⁻¹) = _
  rw [Real.exp_neg, inv_inv, mul_comm]

private theorem expDilation_zero (f : Tests) : expDilation f 0 = f := by
  ext x
  simp [expDilation_apply]

private theorem expDilation_iteratedDeriv (f : Tests) (n : ℕ) (t x : ℝ) :
    iteratedDeriv n (expDilation f t : ℝ → ℂ) x =
      (Real.exp t : ℂ) ^ n * iteratedDeriv n (f : ℝ → ℂ) (Real.exp t * x) := by
  rw [show (expDilation f t : ℝ → ℂ) = fun x => f (Real.exp t * x) from
    funext (expDilation_apply f t)]
  rw [iteratedDeriv_comp_const_smul (f.smooth n) (Real.exp t)]
  simp only [Complex.real_smul, Complex.ofReal_pow]

private def differentiatedDilation (f : Tests) (n : ℕ) (t x : ℝ) : ℂ :=
  (Real.exp t : ℂ) ^ n *
    ((Real.exp t * x : ℝ) * iteratedDeriv (n + 1) (f : ℝ → ℂ) (Real.exp t * x) +
      (n : ℂ) * iteratedDeriv n (f : ℝ → ℂ) (Real.exp t * x))

private theorem differentiatedDilation_zero (f : Tests) (n : ℕ) (x : ℝ) :
    differentiatedDilation f n 0 x = iteratedDeriv n (realSchwartzEuler f : ℝ → ℂ) x := by
  rw [realSchwartzEuler_iteratedDeriv]
  simp [differentiatedDilation]

private theorem differentiatedDilation_continuous (f : Tests) (n : ℕ) :
    Continuous (fun p : ℝ × ℝ => differentiatedDilation f n p.1 p.2) := by
  have hc (k : ℕ) : Continuous (iteratedDeriv k (f : ℝ → ℂ)) :=
    (f.smooth k).continuous_iteratedDeriv' k
  unfold differentiatedDilation
  fun_prop (disch := first | exact hc _)

private theorem expDilation_iteratedDeriv_hasDerivAt (f : Tests) (n : ℕ) (t x : ℝ) :
    HasDerivAt (fun t => iteratedDeriv n (expDilation f t : ℝ → ℂ) x)
      (differentiatedDilation f n t x) t := by
  simp_rw [expDilation_iteratedDeriv]
  have hd : HasDerivAt (iteratedDeriv n (f : ℝ → ℂ))
      (iteratedDeriv (n + 1) (f : ℝ → ℂ) (Real.exp t * x)) (Real.exp t * x) := by
    rw [iteratedDeriv_succ]
    exact ((f.smooth (n + 1)).differentiable_iteratedDeriv' n _).hasDerivAt
  have he := (Real.hasDerivAt_exp t).mul_const x
  have hex : HasDerivAt (fun s : ℝ => (Real.exp s : ℂ)) (Real.exp t : ℂ) t :=
    (Real.hasDerivAt_exp t).ofReal_comp
  have hp := hex.fun_pow n
  have hc : HasDerivAt (fun s => iteratedDeriv n (f : ℝ → ℂ) (Real.exp s * x))
      ((Real.exp t * x) • iteratedDeriv (n + 1) (f : ℝ → ℂ) (Real.exp t * x)) t := by
    simpa only [Function.comp_apply] using! hd.scomp t he
  have heq : differentiatedDilation f n t x =
      ((n : ℂ) * (Real.exp t : ℂ) ^ (n - 1) * (Real.exp t : ℂ)) *
          iteratedDeriv n (f : ℝ → ℂ) (Real.exp t * x) +
        (Real.exp t : ℂ) ^ n *
          ((Real.exp t * x) • iteratedDeriv (n + 1) (f : ℝ → ℂ) (Real.exp t * x)) := by
    unfold differentiatedDilation
    simp only [Complex.real_smul]
    cases n with
    | zero => norm_num
    | succ n => rw [Nat.succ_sub_one, pow_succ]; ring
  rw [heq]
  exact hp.fun_mul hc

/-- The generator is the actual limit of the dilation difference quotient
for compactly supported Schwartz tests. -/
theorem tendsto_realSchwartzEuler_of_compact (f : Tests) (hf : HasCompactSupport f) :
    Tendsto (fun t : ℝ => t⁻¹ • (expDilation f t - f)) (𝓝[≠] 0)
      (𝓝 (realSchwartzEuler f)) := by
  classical
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_ball (0 : ℝ)).mp hf.isBounded
  let R := (1 + |r|) * Real.exp 1
  have hR : 0 < R := by dsimp [R]; positivity
  have hfzero (x : ℝ) (hx : r < ‖x‖) : x ∉ tsupport f := fun h => by
    have he := hr h
    rw [Metric.mem_ball, dist_zero_right] at he
    exact (not_lt_of_ge hx.le) he
  let d (t : ℝ) := t⁻¹ • (expDilation f t - f) - realSchwartzEuler f
  have hdiff (t x : ℝ) (n : ℕ) :
      iteratedDeriv n (d t : ℝ → ℂ) x =
        t⁻¹ • (iteratedDeriv n (expDilation f t : ℝ → ℂ) x - iteratedDeriv n (f : ℝ → ℂ) x) -
          iteratedDeriv n (realSchwartzEuler f : ℝ → ℂ) x := by
    change iteratedDeriv n
      (fun x => t⁻¹ • ((expDilation f t) x - f x) - realSchwartzEuler f x) x = _
    rw [iteratedDeriv_fun_sub ((((expDilation f t).smooth n).sub (f.smooth n)).contDiffAt.const_smul (t⁻¹))
      ((realSchwartzEuler f).smooth n).contDiffAt]
    rw [iteratedDeriv_fun_const_smul_field,
      iteratedDeriv_fun_sub ((expDilation f t).smooth n).contDiffAt (f.smooth n).contDiffAt]
  apply ((schwartz_withSeminorms ℂ ℝ ℂ).tendsto_nhds _ _).mpr
  rintro ⟨k, n⟩ ε hε
  let δ := ε / (2 * (1 + R ^ k))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  let err (p : ℝ × ℝ) := ‖differentiatedDilation f n p.1 p.2 - differentiatedDilation f n 0 p.2‖
  have herr : Continuous err := ((differentiatedDilation_continuous f n).sub
    ((differentiatedDilation_continuous f n).comp (continuous_const.prodMk continuous_snd))).norm
  have he : ∀ᶠ t : ℝ in 𝓝 0, ∀ x ∈ Metric.closedBall (0 : ℝ) R, err (t,x) < δ := by
    apply (isCompact_closedBall (0 : ℝ) R).eventually_forall_of_forall_eventually
    intro x _
    have hx : err (0,x) < δ := by simpa [err] using hδ
    exact herr.continuousAt.eventually_lt continuousAt_const hx
  obtain ⟨η, hη, hηb⟩ := Metric.mem_nhds_iff.mp he
  let ρ := min (η / 2) (1 : ℝ)
  have hρ : 0 < ρ := lt_min (half_pos hη) zero_lt_one
  have hsmall : ∀ᶠ t : ℝ in 𝓝[≠] 0, |t| < ρ ∧ t ≠ 0 := by
    have hb : ∀ᶠ t : ℝ in 𝓝 0, t ∈ Metric.ball 0 ρ := Metric.ball_mem_nhds (0 : ℝ) hρ
    filter_upwards [hb.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with t ht ht'
    exact ⟨by simpa [Real.dist_eq] using ht, ht'⟩
  filter_upwards [hsmall] with t ht
  change SchwartzMap.seminorm ℂ k n (d t) < ε
  apply (SchwartzMap.seminorm_le_bound ℂ k n _ (half_pos hε).le ?_).trans_lt (half_lt_self hε)
  intro x
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, hdiff]
  by_cases hx : x ∈ Metric.closedBall (0 : ℝ) R
  · let q (s : ℝ) := iteratedDeriv n (expDilation f s : ℝ → ℂ) x -
        s • differentiatedDilation f n 0 x
    have ho : ∀ s ∈ Icc (-ρ) ρ, ‖differentiatedDilation f n s x - differentiatedDilation f n 0 x‖ ≤ δ := by
      intro s hs
      exact (hηb (show s ∈ Metric.ball (0 : ℝ) η from by
        rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
        have hρη : ρ < η := (min_le_left _ _).trans_lt (half_lt_self hη)
        exact ⟨by linarith [hs.1], hs.2.trans_lt hρη⟩) x hx).le
    have hq (s : ℝ) : HasDerivAt q
        (differentiatedDilation f n s x - differentiatedDilation f n 0 x) s := by
      have hd : HasDerivAt (fun (s : ℝ) => s • differentiatedDilation f n 0 x)
          (differentiatedDilation f n 0 x) s := by
        simpa using (hasDerivAt_id s).smul_const (differentiatedDilation f n 0 x)
      exact (expDilation_iteratedDeriv_hasDerivAt f n s x).sub hd
    obtain ⟨htl, htu⟩ := abs_lt.mp ht.1
    have hb := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun s _ => (hq s).hasDerivWithinAt) ho (convex_Icc (-ρ) ρ)
      (show 0 ∈ Icc (-ρ) ρ from ⟨by linarith, hρ.le⟩)
      (show t ∈ Icc (-ρ) ρ from ⟨htl.le, htu.le⟩)
    have hrw : t⁻¹ • (q t - q 0) =
        t⁻¹ • (iteratedDeriv n (expDilation f t : ℝ → ℂ) x - iteratedDeriv n (f : ℝ → ℂ) x) -
          iteratedDeriv n (realSchwartzEuler f : ℝ → ℂ) x := by
      dsimp only [q]
      rw [zero_smul, sub_zero, expDilation_zero, ← differentiatedDilation_zero,
        sub_right_comm, smul_sub, inv_smul_smul₀ ht.2]
    rw [← hrw, norm_smul, norm_inv]
    have hnorm : ‖x‖ ≤ R := by simpa [Metric.mem_closedBall, dist_zero_right] using hx
    rw [sub_zero] at hb
    have hn : ‖t‖ ≠ 0 := norm_ne_zero_iff.mpr ht.2
    calc
      _ ≤ R ^ k * (‖t‖⁻¹ * (δ * ‖t‖)) := by gcongr
      _ = R ^ k * δ := by field_simp
      _ ≤ (1 + R ^ k) * δ :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) hδ.le
      _ = ε / 2 := by dsimp [δ]; field_simp
  · have hxR : R < ‖x‖ := lt_of_not_ge (fun h => hx (by simpa [Metric.mem_closedBall, dist_zero_right] using h))
    have hxt : r < ‖Real.exp t * x‖ := by
      rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos t).le]
      have ht₀ : -1 < t := (neg_le_neg (min_le_right _ _)).trans_lt (abs_lt.mp ht.1).1
      have he₀ : Real.exp (-1) ≤ Real.exp t := Real.exp_le_exp.mpr ht₀.le
      have h₁ : Real.exp (-1) * R = 1 + |r| := by
        dsimp [R]
        rw [mul_left_comm, ← Real.exp_add]
        norm_num
      have h₂ := mul_lt_mul_of_pos_left hxR (Real.exp_pos (-1))
      linarith [le_abs_self r, mul_le_mul_of_nonneg_right he₀ (norm_nonneg x)]
    have hxr : r < ‖x‖ := by
      have ht' : R ≥ 1 + |r| := le_mul_of_one_le_right (by positivity) (Real.one_le_exp_iff.mpr zero_le_one)
      linarith [le_abs_self r]
    have hz (y : ℝ) (hy : r < ‖y‖) (j : ℕ) : iteratedDeriv j (f : ℝ → ℂ) y = 0 := by
      rw [(notMem_tsupport_iff_eventuallyEq.mp (hfzero y hy)).iteratedDeriv_eq]
      simp
    rw [expDilation_iteratedDeriv, realSchwartzEuler_iteratedDeriv, hz _ hxt, hz _ hxr, hz _ hxr]
    simp
    positivity

/-- Dilation covariance forces the corresponding infinitesimal Euler
equation on compactly supported tests. -/
theorem realWeilEigen_Euler_compact (T : StrongDual ℂ Tests) (a : ℕ) (z : ℂ)
    (hcov : ∀ u f, T (archSchwartzDilation u f) = realArchUnitWeight a z u * T f)
    (f : Tests) (hf : HasCompactSupport f) :
    T (realSchwartzEuler f) = -z * T f := by
  have ht : Tendsto (fun t : ℝ => T (t⁻¹ • (expDilation f t - f))) (𝓝[≠] 0)
      (𝓝 (T (realSchwartzEuler f))) :=
    T.continuous.continuousAt.tendsto.comp (tendsto_realSchwartzEuler_of_compact f hf)
  have he (t : ℝ) : T (expDilation f t) = Complex.exp ((t : ℂ) * (-z)) * T f := by
    rw [expDilation, hcov]
    unfold realArchUnitWeight
    change ((|Real.exp (-t)| : ℝ) : ℂ) ^ z *
      (if Real.exp (-t) < 0 then (-1 : ℂ) ^ a else 1) * T f = _
    rw [abs_of_pos (Real.exp_pos _), ite_eq_right (Real.exp_pos _).not_gt, mul_one,
      Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)),
      ← Complex.ofReal_log (Real.exp_pos _).le, Real.log_exp, Complex.ofReal_neg, neg_mul, mul_neg]
  have hd : HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * (-z)) * T f) (-z * T f) 0 := by
    simpa using (((Complex.ofRealCLM.hasFDerivAt (x := (0 : ℝ))).hasDerivAt.mul_const (-z)).cexp.mul_const (T f))
  have he' := hd.tendsto_slope_zero
  have hre (t : ℝ) :
      T (t⁻¹ • (expDilation f t - f)) =
        t⁻¹ • (Complex.exp ((t : ℂ) * (-z)) * T f - T f) := by
    have h := (T.restrictScalars ℝ).map_smul t⁻¹ (expDilation f t - f)
    change T (t⁻¹ • (expDilation f t - f)) = t⁻¹ • T (expDilation f t - f) at h
    rw [h, map_sub, he]
  exact tendsto_nhds_unique (ht.congr' (.of_forall hre)) (by simpa using he')

end
end Masullo
