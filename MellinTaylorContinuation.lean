import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Normed.Group.FunctionSeries

open Asymptotics Filter MeasureTheory Set
open scoped ContDiff ENNReal NNReal Topology

namespace Masullo

noncomputable section

theorem iteratedDeriv_complex_ofReal (k : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) :
    iteratedDeriv k (fun x => (h x : ℂ)) = fun x => Complex.ofReal (iteratedDeriv k h x) := by
  induction k generalizing h with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ', iteratedDeriv_succ']
    have he : deriv (fun x => (h x : ℂ)) = fun x => Complex.ofReal (deriv h x) := by
      funext x
      exact (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt x
        ((hh.differentiable (by simp) x).hasDerivAt)).deriv
    rw [he]
    exact ih (contDiff_infty_iff_deriv.mp hh).2

/-- Scalar contributed by (k) transposed applications of ((2πi)^{-1}∂)
to a Dirac distribution. -/
def archimedeanDeltaDerivativeScale (k : ℕ) : ℂ :=
  (-((2 * (Real.pi : ℂ)) * Complex.I)⁻¹) ^ k

theorem archimedeanDeltaDerivativeScale_cancel (k : ℕ) :
    (2 * (Real.pi : ℂ)) ^ k * (-Complex.I) ^ k * archimedeanDeltaDerivativeScale k = 1 := by
  have hπ : (2 * (Real.pi : ℂ)) ≠ 0 :=
    mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  have h : (2 * (Real.pi : ℂ)) * (-Complex.I) *
      (-((2 * (Real.pi : ℂ)) * Complex.I)⁻¹) = 1 := by
    calc
      _ = (2 * (Real.pi : ℂ) * Complex.I) * (2 * (Real.pi : ℂ) * Complex.I)⁻¹ := by ring
      _ = 1 := mul_inv_cancel₀ (mul_ne_zero hπ Complex.I_ne_zero)
  rw [archimedeanDeltaDerivativeScale, ← mul_pow, ← mul_pow, h, one_pow]

theorem archimedean_negativeI_even (n : ℕ) : (-Complex.I) ^ (2 * n) = (-1 : ℂ) ^ n := by
  have h : (-Complex.I) ^ (2 : ℕ) = -1 := by simp
  rw [pow_mul, h]

/-- Taylor coefficient of a smooth radial profile at the origin. -/
def mellinTaylorCoeff (f : ℝ → ℂ) (k : ℕ) : ℂ :=
  (k.factorial : ℂ)⁻¹ * iteratedDeriv k f 0

private def mellinTaylorTerm (f : ℝ → ℂ) (k : ℕ) : ℝ → ℂ :=
  (Ioc (0 : ℝ) 1).indicator (fun t => mellinTaylorCoeff f k * (t : ℂ) ^ k)

private def mellinTaylorRemainder (f : ℝ → ℂ) (n : ℕ) : ℝ → ℂ :=
  fun t => f t - ∑ k ∈ Finset.range (n + 1), mellinTaylorTerm f k t

private theorem mellinTaylorRemainder_succ (f : ℝ → ℂ) (n : ℕ) :
    mellinTaylorRemainder f (n + 1) =
      fun t => mellinTaylorRemainder f n t - mellinTaylorTerm f (n + 1) t := by
  funext t
  rw [mellinTaylorRemainder, Finset.sum_range_succ, ← sub_sub]
  rfl

private theorem mellinTaylorTerm_integrable (f : ℝ → ℂ) (k : ℕ) :
    Integrable (mellinTaylorTerm f k) := by
  apply (integrable_indicator_iff measurableSet_Ioc).2
  have hc : Continuous (fun t : ℝ => mellinTaylorCoeff f k * (t : ℂ) ^ k) :=
    continuous_const.mul (Complex.continuous_ofReal.pow _)
  exact (hc.continuousOn.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self

private theorem mellinTaylorRemainder_locallyIntegrable {f : ℝ → ℂ} (hf : Continuous f) (n : ℕ) :
    LocallyIntegrableOn (mellinTaylorRemainder f n) (Ioi 0) := by
  apply (hf.continuousOn.locallyIntegrableOn measurableSet_Ioi).sub
  have hI : Integrable (fun t : ℝ => ∑ k ∈ Finset.range (n + 1), mellinTaylorTerm f k t) :=
    integrable_finsetSum _ (fun k _ => mellinTaylorTerm_integrable f k)
  exact hI.locallyIntegrable.locallyIntegrableOn _

private theorem mellinTaylorRemainder_eventually_atTop (f : ℝ → ℂ) (n : ℕ) :
    mellinTaylorRemainder f n =ᶠ[atTop] f := by
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
  have h : t ∉ Ioc (0 : ℝ) 1 := fun hm => (not_le_of_gt ht) hm.2
  simp [mellinTaylorRemainder, mellinTaylorTerm, h]

private theorem mellinTaylorRemainder_eq_taylor (f : ℝ → ℂ) (n : ℕ)
    (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) :
    mellinTaylorRemainder f n t = f t - taylorWithinEval f n univ 0 t := by
  simp only [mellinTaylorRemainder, mellinTaylorTerm, indicator_of_mem ht, taylor_within_apply,
    sub_zero, iteratedDerivWithin_univ]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [mellinTaylorCoeff, Complex.real_smul]
  push_cast
  ring

private theorem mellinTaylorRemainder_bigO {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (n : ℕ) :
    mellinTaylorRemainder f n =O[𝓝[>] (0 : ℝ)] (fun t => t ^ (-(-((n + 1 : ℕ) : ℝ)))) := by
  let N := n + 1
  have hI : ∀ᶠ t : ℝ in 𝓝[>] 0, t ∈ Ioc (0 : ℝ) 1 := by
    filter_upwards [self_mem_nhdsWithin (s := Ioi (0 : ℝ)),
      mem_nhdsWithin_of_mem_nhds (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with t h₀ h₁
    exact ⟨h₀, h₁.le⟩
  have hdiff : ContDiff ℝ N f := hf.of_le (WithTop.coe_le_coe.mpr le_top)
  have h₁ : mellinTaylorRemainder f N =O[𝓝[>] (0 : ℝ)] (fun t => t ^ N) := by
    have ht := (taylor_isLittleO_univ (x₀ := 0) hdiff).isBigO.mono
      (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    have he : mellinTaylorRemainder f N =ᶠ[𝓝[>] (0 : ℝ)]
        (fun t => f t - taylorWithinEval f N univ 0 t) :=
      hI.mono (mellinTaylorRemainder_eq_taylor f N)
    exact he.trans_isBigO (by simpa only [sub_zero] using ht)
  have h₂ : mellinTaylorTerm f N =O[𝓝[>] (0 : ℝ)] (fun t => t ^ N) := by
    apply IsBigO.of_bound ‖mellinTaylorCoeff f N‖
    filter_upwards [hI] with t ht
    simp only [mellinTaylorTerm, indicator_of_mem ht, norm_mul, norm_pow, Complex.norm_real, le_rfl]
  have he : mellinTaylorRemainder f n =
      fun t => mellinTaylorRemainder f N t + mellinTaylorTerm f N t := by
    unfold N
    rw [mellinTaylorRemainder_succ]
    simp only [sub_add_cancel]
  rw [he]
  simpa only [neg_neg, Real.rpow_natCast] using h₁.add h₂

private theorem hasMellinTaylorTerm (f : ℝ → ℂ) (k : ℕ) (s : ℂ) (hs : 0 < s.re + k) :
    HasMellin (mellinTaylorTerm f k) s (mellinTaylorCoeff f k / (s + k)) := by
  have h := hasMellin_cpow_Ioc (k : ℂ) (s := s) (by simpa using hs)
  have hc := hasMellin_const_smul h.1 (mellinTaylorCoeff f k)
  rw [h.2] at hc
  have he : mellinTaylorTerm f k = fun t =>
      mellinTaylorCoeff f k • (Ioc (0 : ℝ) 1).indicator (fun x => (x : ℂ) ^ (k : ℂ)) t := by
    funext t
    by_cases ht : t ∈ Ioc (0 : ℝ) 1 <;> simp [mellinTaylorTerm, Complex.cpow_natCast, smul_eq_mul, ht]
  rw [he]
  simpa only [smul_eq_mul, div_eq_mul_inv, one_mul] using hc

private def mellinTaylorChart (f : ℝ → ℂ) (n : ℕ) (s : ℂ) : ℂ :=
  mellin (mellinTaylorRemainder f n) s +
    ∑ k ∈ Finset.range (n + 1), mellinTaylorCoeff f k / (s + k)

private theorem mellinTaylorChart_exists (s : ℂ) : ∃ n : ℕ, -((n + 1 : ℕ) : ℝ) < s.re := by
  obtain ⟨n, hn⟩ := exists_nat_gt (-s.re)
  exact ⟨n, by push_cast; linarith⟩

/-- The Mellin continuation obtained by subtracting Taylor terms near zero.
It is chart-independent for smooth profiles with rapid decay at infinity. -/
def mellinTaylorContinued (f : ℝ → ℂ) (s : ℂ) : ℂ :=
  mellinTaylorChart f (mellinTaylorChart_exists s).choose s

section SmoothProfile

variable {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
  (hdec : ∀ a : ℝ, f =O[atTop] (fun t => t ^ (-a)))

include hf hdec

private theorem mellinTaylorRemainder_convergent (n : ℕ) {s : ℂ}
    (hs : -((n + 1 : ℕ) : ℝ) < s.re) :
    MellinConvergent (mellinTaylorRemainder f n) s :=
  mellinConvergent_of_isBigO_rpow (mellinTaylorRemainder_locallyIntegrable hf.continuous n)
    ((mellinTaylorRemainder_eventually_atTop f n).trans_isBigO (hdec (s.re + 1)))
    (lt_add_one _) (mellinTaylorRemainder_bigO hf n) hs

private theorem mellinTaylorRemainder_analytic (n : ℕ) {s : ℂ}
    (hs : -((n + 1 : ℕ) : ℝ) < s.re) :
    AnalyticAt ℂ (mellin (mellinTaylorRemainder f n)) s := by
  let U := {z : ℂ | -((n + 1 : ℕ) : ℝ) < z.re}
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hD : DifferentiableOn ℂ (mellin (mellinTaylorRemainder f n)) U := by
    intro z hz
    apply DifferentiableAt.differentiableWithinAt
    exact mellin_differentiableAt_of_isBigO_rpow (mellinTaylorRemainder_locallyIntegrable hf.continuous n)
      ((mellinTaylorRemainder_eventually_atTop f n).trans_isBigO (hdec (z.re + 1)))
      (lt_add_one _) (mellinTaylorRemainder_bigO hf n) hz
  exact hD.analyticOnNhd hU s hs

private theorem mellinTaylorChart_eq_succ (n : ℕ) {s : ℂ}
    (hs : -((n + 1 : ℕ) : ℝ) < s.re) :
    mellinTaylorChart f n s = mellinTaylorChart f (n + 1) s := by
  have h : 0 < s.re + ((n + 1 : ℕ) : ℝ) := by linarith
  have hterm := hasMellinTaylorTerm f (n + 1) s h
  have hrem := (hasMellin_sub (mellinTaylorRemainder_convergent hf hdec n hs) hterm.1).2
  rw [← mellinTaylorRemainder_succ, hterm.2] at hrem
  unfold mellinTaylorChart
  rw [hrem, Finset.sum_range_succ (n := n + 1)]
  abel

private theorem mellinTaylorChart_eq_of_le {n m : ℕ} (h : n ≤ m) {s : ℂ}
    (hs : -((n + 1 : ℕ) : ℝ) < s.re) :
    mellinTaylorChart f n s = mellinTaylorChart f m s := by
  induction m, h using Nat.le_induction with
  | base => rfl
  | succ m hm ih =>
    have he : ((n + 1 : ℕ) : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ hm
    exact ih.trans (mellinTaylorChart_eq_succ hf hdec m (by linarith))

private theorem mellinTaylorContinued_eq_chart (n : ℕ) {s : ℂ}
    (hs : -((n + 1 : ℕ) : ℝ) < s.re) :
    mellinTaylorContinued f s = mellinTaylorChart f n s := by
  let m := (mellinTaylorChart_exists s).choose
  have hm : -((m + 1 : ℕ) : ℝ) < s.re := (mellinTaylorChart_exists s).choose_spec
  change mellinTaylorChart f m s = _
  rcases le_total m n with h | h
  · exact mellinTaylorChart_eq_of_le hf hdec h hm
  · exact (mellinTaylorChart_eq_of_le hf hdec h hs).symm

/-- The continuation on a Taylor half-plane, split at radius one. -/
theorem mellinTaylorContinued_eq_split (n : ℕ) {s : ℂ}
    (hs : -((n + 1 : ℕ) : ℝ) < s.re) :
    mellinTaylorContinued f s =
      (∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (s - 1) * f t) +
      (∫ t in Ioc (0 : ℝ) 1, (t : ℂ) ^ (s - 1) *
        (f t - ∑ k ∈ Finset.range (n + 1), mellinTaylorCoeff f k * (t : ℂ) ^ k)) +
      ∑ k ∈ Finset.range (n + 1), mellinTaylorCoeff f k / (s + k) := by
  have hi := mellinTaylorRemainder_convergent hf hdec n hs
  rw [mellinTaylorContinued_eq_chart hf hdec n hs, mellinTaylorChart, mellin]
  have hd : Disjoint (Ioc (0 : ℝ) 1) (Ioi 1) :=
    disjoint_left.mpr fun _ h₀ h₁ => (not_lt_of_ge h₀.2) h₁
  have h₀ := hi.mono_set (s := Ioc (0 : ℝ) 1) (fun _ h => h.1)
  have h₁ := hi.mono_set (s := Ioi (1 : ℝ)) (Ioi_subset_Ioi zero_le_one)
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one, setIntegral_union hd measurableSet_Ioi h₀ h₁,
    add_comm (∫ t in Ioc (0 : ℝ) 1, _)]
  congr 1
  congr 1
  · apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    have ht' : t ∉ Ioc (0 : ℝ) 1 := fun h => (not_lt_of_ge h.2) ht
    simp [mellinTaylorRemainder, mellinTaylorTerm, ht', smul_eq_mul]
  · apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    simp [mellinTaylorRemainder, mellinTaylorTerm, ht, smul_eq_mul]

/-- The original positive-half-plane integral converges absolutely and agrees with the continuation. -/
theorem mellinTaylorContinued_eq_mellin {s : ℂ} (hs : 0 < s.re) :
    HasMellin f s (mellinTaylorContinued f s) := by
  have h₀ : -((0 + 1 : ℕ) : ℝ) < s.re := by norm_num; linarith
  have hterm := hasMellinTaylorTerm f 0 s (by simpa using hs)
  have hrem := hasMellin_add (mellinTaylorRemainder_convergent hf hdec 0 h₀) hterm.1
  have hkernel : (fun t => mellinTaylorRemainder f 0 t + mellinTaylorTerm f 0 t) = f := by
    funext t
    simp [mellinTaylorRemainder]
  rw [hkernel, hterm.2] at hrem
  rw [mellinTaylorContinued_eq_chart hf hdec 0 h₀]
  simpa [mellinTaylorChart] using hrem

/-- The continued Mellin transform of the smooth radial profile is meromorphic on the plane. -/
theorem mellinTaylorContinued_meromorphic : Meromorphic (mellinTaylorContinued f) := by
  intro s
  obtain ⟨n, hn⟩ := mellinTaylorChart_exists s
  have ht : MeromorphicAt (mellinTaylorChart f n) s := by
    apply MeromorphicAt.add (mellinTaylorRemainder_analytic hf hdec n hn).meromorphicAt
    exact MeromorphicAt.fun_sum fun k _ =>
      (MeromorphicAt.const _ _).div (analyticAt_id.add analyticAt_const).meromorphicAt
  apply ht.congr
  have hU : {z : ℂ | -((n + 1 : ℕ) : ℝ) < z.re} ∈ 𝓝 s :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hn
  filter_upwards [mem_nhdsWithin_of_mem_nhds hU] with z hz
  exact (mellinTaylorContinued_eq_chart hf hdec n hz).symm

/-- The only candidate poles are the nonpositive integers. -/
theorem mellinTaylorContinued_analyticAt {s : ℂ} (hs : ∀ k : ℕ, s + k ≠ 0) :
    AnalyticAt ℂ (mellinTaylorContinued f) s := by
  obtain ⟨n, hn⟩ := mellinTaylorChart_exists s
  have ha : AnalyticAt ℂ (mellinTaylorChart f n) s := by
    apply (mellinTaylorRemainder_analytic hf hdec n hn).add
    exact Finset.analyticAt_fun_sum _ fun k _ =>
      analyticAt_const.div (analyticAt_id.add analyticAt_const) (hs k)
  apply ha.congr
  have hU : {z : ℂ | -((n + 1 : ℕ) : ℝ) < z.re} ∈ 𝓝 s :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hn
  filter_upwards [hU] with z hz
  exact (mellinTaylorContinued_eq_chart hf hdec n hz).symm

/-- Near a candidate pole the continuation is an analytic function plus
the single principal term given by the Taylor coefficient. -/
theorem mellinTaylorContinued_principalPart (k : ℕ) :
    ∃ A : ℂ → ℂ, AnalyticAt ℂ A (-(k : ℂ)) ∧
      mellinTaylorContinued f =ᶠ[𝓝 (-(k : ℂ))]
        fun z => A z + mellinTaylorCoeff f k / (z + k) := by
  let A (z : ℂ) := mellin (mellinTaylorRemainder f k) z +
    ∑ j ∈ Finset.range k, mellinTaylorCoeff f j / (z + j)
  have h₀ : -((k + 1 : ℕ) : ℝ) < (-(k : ℂ)).re := by simp
  refine ⟨A, ?_, ?_⟩
  · apply (mellinTaylorRemainder_analytic hf hdec k h₀).add
    apply Finset.analyticAt_fun_sum
    intro j hj
    have hjk : j < k := Finset.mem_range.mp hj
    apply analyticAt_const.div (analyticAt_id.add analyticAt_const)
    intro h
    have h' : -(k : ℝ) + (j : ℝ) = 0 := by simpa using congrArg Complex.re h
    have : (j : ℝ) < k := by exact_mod_cast hjk
    linarith
  · have hU : {z : ℂ | -((k + 1 : ℕ) : ℝ) < z.re} ∈ 𝓝 (-(k : ℂ)) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds h₀
    filter_upwards [hU] with z hz
    rw [mellinTaylorContinued_eq_chart hf hdec k hz, mellinTaylorChart, Finset.sum_range_succ]
    simp [A, add_assoc]

/-- The polar coefficient equals the Taylor coefficient, including at a removable point. -/
theorem mellinTaylorContinued_residue (k : ℕ) :
    Tendsto (fun z => (z + k) * mellinTaylorContinued f z) (𝓝[≠] (-(k : ℂ)))
      (𝓝 (mellinTaylorCoeff f k)) := by
  obtain ⟨A, hA, h⟩ := mellinTaylorContinued_principalPart hf hdec k
  have ht : ContinuousAt (fun z : ℂ => (z + k) * A z + mellinTaylorCoeff f k) (-(k : ℂ)) :=
    ((continuousAt_id.add continuousAt_const).mul hA.continuousAt).add continuousAt_const
  have hlim : Tendsto (fun z : ℂ => (z + k) * A z + mellinTaylorCoeff f k) (𝓝[≠] (-(k : ℂ)))
      (𝓝 (mellinTaylorCoeff f k)) := by
    simpa using ht.tendsto.mono_left nhdsWithin_le_nhds
  apply hlim.congr'
  filter_upwards [h.filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin (s := {-(k : ℂ)}ᶜ)] with z he hz
  have hn : z + (k : ℂ) ≠ 0 := by
    intro hz0
    exact hz (mem_singleton_iff.mpr (eq_neg_of_add_eq_zero_left hz0))
  rw [he, mul_add]
  field_simp [hn]

/-- A negative-integer chart is analytic exactly when its principal coefficient
vanishes, and otherwise has a simple pole. -/
theorem mellinTaylorContinued_order (k : ℕ) :
    if mellinTaylorCoeff f k = 0 then
      AnalyticAt ℂ (mellinTaylorContinued f) (-(k : ℂ))
    else meromorphicOrderAt (mellinTaylorContinued f) (-(k : ℂ)) = (-1 : ℤ) := by
  obtain ⟨A, hA, he⟩ := mellinTaylorContinued_principalPart hf hdec k
  split_ifs with hzero
  · apply hA.congr
    filter_upwards [he] with z hz
    simpa [hzero] using hz.symm
  · apply (meromorphicOrderAt_eq_int_iff (mellinTaylorContinued_meromorphic hf hdec _)).2
    refine ⟨fun z => (z + k) * A z + mellinTaylorCoeff f k,
      ((analyticAt_id.add analyticAt_const).mul hA).add analyticAt_const, by simpa, ?_⟩
    filter_upwards [he.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin (s := {-(k : ℂ)}ᶜ)] with z hz hz'
    have hn : z + (k : ℂ) ≠ 0 := by
      intro hz0
      exact hz' (mem_singleton_iff.mpr (eq_neg_of_add_eq_zero_left hz0))
    rw [hz, sub_neg_eq_add, zpow_neg_one, smul_eq_mul, mul_add, ← mul_assoc,
      inv_mul_cancel₀ hn, one_mul, div_eq_mul_inv, mul_comm ((z + (k : ℂ))⁻¹)]


end SmoothProfile

open scoped SchwartzMap

private abbrev RadialTests := 𝓢(ℝ, ℂ)

theorem schwartz_radial_rapid (f : RadialTests) (r : ℝ) :
    (f : ℝ → ℂ) =O[atTop] (fun t => t ^ (-r)) := by
  apply ((f.isBigO_cocompact_rpow (-r)).mono atTop_le_cocompact).trans
  apply EventuallyEq.isBigO
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  rw [Real.norm_of_nonneg ht]

private def radialTaylorCoeff (k : ℕ) : RadialTests →L[ℂ] ℂ :=
  SchwartzMap.mkCLMtoNormedSpace (fun f => mellinTaylorCoeff f k)
    (fun f g => by
      change (k.factorial : ℂ)⁻¹ * iteratedDeriv k (fun x => f x + g x) 0 = _
      rw [iteratedDeriv_fun_add (f.smooth k).contDiffAt (g.smooth k).contDiffAt,
        mul_add]
      rfl)
    (fun c f => by
      change (k.factorial : ℂ)⁻¹ * iteratedDeriv k (fun x => c • f x) 0 =
        c * ((k.factorial : ℂ)⁻¹ * iteratedDeriv k f 0)
      rw [iteratedDeriv_fun_const_smul_field, smul_eq_mul, mul_left_comm])
    ⟨{(0, k)}, ‖(k.factorial : ℂ)⁻¹‖, norm_nonneg _, fun f => by
      rw [mellinTaylorCoeff, norm_mul, Finset.sup_singleton]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      change ‖iteratedDeriv k f 0‖ ≤ SchwartzMap.seminorm ℂ 0 k f
      simpa only [pow_zero, one_mul] using SchwartzMap.le_seminorm' ℂ 0 k f 0⟩

private theorem radialTaylor_remainder_bound (f : RadialTests) (n : ℕ) {t : ℝ}
    (ht : t ∈ Ioc (0 : ℝ) 1) :
    ‖mellinTaylorRemainder f n t‖ ≤
      (SchwartzMap.seminorm ℂ 0 (n + 1) f / n.factorial) * t ^ (n + 1) := by
  have hu := uniqueDiffOn_Icc (show (0 : ℝ) < 1 by norm_num)
  have hz : (0 : ℝ) ∈ Icc 0 1 := ⟨le_rfl, zero_le_one⟩
  have he : taylorWithinEval f n (Icc 0 1) 0 t = taylorWithinEval f n univ 0 t := by
    simp only [taylor_within_apply, iteratedDerivWithin_univ]
    exact Finset.sum_congr rfl fun k _ => by
      rw [iteratedDerivWithin_eq_iteratedDeriv hu (f.smooth k).contDiffAt hz]
  have hb := taylor_mean_remainder_bound zero_le_one (f.smooth (n + 1)).contDiffOn
    (Ioc_subset_Icc_self ht) (C := SchwartzMap.seminorm ℂ 0 (n + 1) f)
    (fun y hy => by
      rw [iteratedDerivWithin_eq_iteratedDeriv hu (f.smooth (n + 1)).contDiffAt hy]
      simpa only [pow_zero, one_mul] using SchwartzMap.le_seminorm' ℂ 0 (n + 1) f y)
  rw [he, sub_zero, mul_div_right_comm] at hb
  rwa [mellinTaylorRemainder_eq_taylor f n t ht]

private theorem radialTaylor_tail_bound (f : RadialTests) (n m : ℕ) {t : ℝ}
    (ht : 1 < t) :
    ‖mellinTaylorRemainder f n t‖ ≤ SchwartzMap.seminorm ℂ m 0 f * t ^ (-(m : ℝ)) := by
  have hp : 0 < t := zero_lt_one.trans ht
  have hI : t ∉ Ioc (0 : ℝ) 1 := fun h => (not_le_of_gt ht) h.2
  simp only [mellinTaylorRemainder, mellinTaylorTerm, indicator_of_notMem hI, Finset.sum_const_zero, sub_zero]
  rw [Real.rpow_neg hp.le, Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ (pow_pos hp _)]
  simpa only [abs_of_pos hp, iteratedDeriv_zero, mul_comm] using SchwartzMap.le_seminorm' ℂ m 0 f t

private theorem radialTaylor_mellin_bound (n : ℕ) {σ₀ σ₁ : ℝ}
    (hs : -((n + 1 : ℕ) : ℝ) < σ₀) :
    ∃ (A B : ℝ) (m : ℕ), 0 ≤ A ∧ 0 ≤ B ∧ ∀ (f : RadialTests) (s : ℂ),
      σ₀ ≤ s.re → s.re ≤ σ₁ → ‖mellin (mellinTaylorRemainder f n) s‖ ≤
        A * SchwartzMap.seminorm ℂ 0 (n + 1) f + B * SchwartzMap.seminorm ℂ m 0 f := by
  obtain ⟨m, hm⟩ := exists_nat_gt σ₁
  let a := σ₀ - 1 + ((n + 1 : ℕ) : ℝ)
  let b := σ₁ - 1 - (m : ℝ)
  have h₀ : IntegrableOn (fun t : ℝ => t ^ a) (Ioc 0 1) volume :=
    (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1)
      (show -1 < a by dsimp [a]; linarith)).1
  have h₁ : IntegrableOn (fun t : ℝ => t ^ b) (Ioi 1) volume :=
    integrableOn_Ioi_rpow_of_lt (show b < -1 by dsimp [b]; linarith) zero_lt_one
  let A := ∫ t : ℝ in Ioc 0 1, t ^ a
  let B := ∫ t : ℝ in Ioi 1, t ^ b
  have hA : 0 ≤ A :=
    setIntegral_nonneg measurableSet_Ioc (fun t ht => Real.rpow_nonneg ht.1.le _)
  have hB : 0 ≤ B :=
    setIntegral_nonneg measurableSet_Ioi (fun t ht => Real.rpow_nonneg (zero_lt_one.trans ht).le _)
  refine ⟨A / n.factorial, B, m, div_nonneg hA (Nat.cast_nonneg _), hB, fun f s hlow hhigh => ?_⟩
  let F : ℝ → ℂ := fun t => (t : ℂ) ^ (s - 1) • mellinTaylorRemainder f n t
  have hF : IntegrableOn F (Ioi 0) volume :=
    mellinTaylorRemainder_convergent f.smooth' (schwartz_radial_rapid f) n (hs.trans_le hlow)
  have hF₀ := hF.mono_set (s := Ioc (0 : ℝ) 1) (fun _ ht => ht.1)
  have hF₁ := hF.mono_set (s := Ioi (1 : ℝ)) (Ioi_subset_Ioi zero_le_one)
  let P := SchwartzMap.seminorm ℂ 0 (n + 1) f / n.factorial
  let Q := SchwartzMap.seminorm ℂ m 0 f
  have hnF (t : ℝ) (ht : 0 < t) :
      ‖F t‖ = t ^ (s.re - 1) * ‖mellinTaylorRemainder f n t‖ := by
    simp [F, Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.sub_re]
  have hb₀ (t : ℝ) (ht : t ∈ Ioc 0 1) : ‖F t‖ ≤ P * t ^ a := by
    rw [hnF t ht.1]
    calc
      _ ≤ t ^ (σ₀ - 1) * (P * t ^ (n + 1)) :=
        mul_le_mul (Real.rpow_le_rpow_of_exponent_ge ht.1 ht.2 (sub_le_sub_right hlow 1))
          (radialTaylor_remainder_bound f n ht) (norm_nonneg _) (Real.rpow_nonneg ht.1.le _)
      _ = P * t ^ a := by
        change _ = P * t ^ (σ₀ - 1 + ((n + 1 : ℕ) : ℝ))
        rw [Real.rpow_add ht.1, Real.rpow_natCast, mul_left_comm P]
  have hb₁ (t : ℝ) (ht : t ∈ Ioi 1) : ‖F t‖ ≤ Q * t ^ b := by
    have hp : 0 < t := zero_lt_one.trans ht
    rw [hnF t hp]
    calc
      _ ≤ t ^ (σ₁ - 1) * (Q * t ^ (-(m : ℝ))) :=
        mul_le_mul (Real.rpow_le_rpow_of_exponent_le ht.le (sub_le_sub_right hhigh 1))
          (radialTaylor_tail_bound f n m ht) (norm_nonneg _) (Real.rpow_nonneg hp.le _)
      _ = Q * t ^ b := by
        change _ = Q * t ^ ((σ₁ - 1) + (-(m : ℝ)))
        rw [Real.rpow_add hp, mul_left_comm Q]
  change ‖∫ t in Ioi (0 : ℝ), F t‖ ≤ _
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one, setIntegral_union _ measurableSet_Ioi hF₀ hF₁]
  · calc
      _ ≤ (∫ t in Ioc (0 : ℝ) 1, ‖F t‖) + ∫ t in Ioi (1 : ℝ), ‖F t‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_integral_le_integral_norm _)
          (norm_integral_le_integral_norm _))
      _ ≤ (∫ t in Ioc (0 : ℝ) 1, P * t ^ a) + ∫ t in Ioi (1 : ℝ), Q * t ^ b :=
        add_le_add (setIntegral_mono_on hF₀.norm (h₀.const_mul P) measurableSet_Ioc hb₀)
          (setIntegral_mono_on hF₁.norm (h₁.const_mul Q) measurableSet_Ioi hb₁)
      _ = _ := by rw [integral_const_mul, integral_const_mul]; dsimp [P, Q]; ring
  · exact Set.disjoint_left.mpr fun _ hx hy => (not_lt_of_ge hx.2) hy

private theorem radialTaylorRemainder_add (f g : RadialTests) (n : ℕ) :
    mellinTaylorRemainder (f + g : RadialTests) n =
      fun t => mellinTaylorRemainder f n t + mellinTaylorRemainder g n t := by
  funext t
  have hterm (k : ℕ) : mellinTaylorTerm (f + g : RadialTests) k t =
      mellinTaylorTerm f k t + mellinTaylorTerm g k t := by
    have hc := (radialTaylorCoeff k).map_add f g
    change mellinTaylorCoeff (f + g : RadialTests) k = mellinTaylorCoeff f k + mellinTaylorCoeff g k at hc
    by_cases ht : t ∈ Ioc (0 : ℝ) 1
    · simp only [mellinTaylorTerm, indicator_of_mem ht, hc, add_mul]
    · simp only [mellinTaylorTerm, indicator_of_notMem ht, add_zero]
  simp only [mellinTaylorRemainder, hterm, Finset.sum_add_distrib]
  change f t + g t - _ = _
  abel

private theorem radialTaylorRemainder_smul (f : RadialTests) (c : ℂ) (n : ℕ) :
    mellinTaylorRemainder (c • f : RadialTests) n = fun t => c • mellinTaylorRemainder f n t := by
  funext t
  have hterm (k : ℕ) : mellinTaylorTerm (c • f : RadialTests) k t = c * mellinTaylorTerm f k t := by
    have hc := (radialTaylorCoeff k).map_smul c f
    change mellinTaylorCoeff (c • f : RadialTests) k = c * mellinTaylorCoeff f k at hc
    by_cases ht : t ∈ Ioc (0 : ℝ) 1
    · simp only [mellinTaylorTerm, indicator_of_mem ht, hc, mul_assoc]
    · simp only [mellinTaylorTerm, indicator_of_notMem ht, mul_zero]
  simp only [mellinTaylorRemainder, hterm, ← Finset.mul_sum, smul_eq_mul]
  change c * f t - _ = _
  rw [mul_sub]

private def radialTaylorRemainderCLM (n : ℕ) (s : ℂ)
    (hs : -((n + 1 : ℕ) : ℝ) < s.re) : RadialTests →L[ℂ] ℂ :=
  SchwartzMap.mkCLMtoNormedSpace (fun f => mellin (mellinTaylorRemainder f n) s)
    (fun f g => by
      rw [radialTaylorRemainder_add]
      exact (hasMellin_add (mellinTaylorRemainder_convergent f.smooth' (schwartz_radial_rapid f) n hs)
        (mellinTaylorRemainder_convergent g.smooth' (schwartz_radial_rapid g) n hs)).2)
    (fun c f => by
      rw [radialTaylorRemainder_smul]
      exact (hasMellin_const_smul
        (mellinTaylorRemainder_convergent f.smooth' (schwartz_radial_rapid f) n hs) c).2)
    (by
      obtain ⟨A, B, m, hA, hB, hbound⟩ := radialTaylor_mellin_bound n (σ₁ := s.re) hs
      let J : Finset (ℕ × ℕ) := {(0, n + 1), (m, 0)}
      refine ⟨J, A + B, add_nonneg hA hB, fun f => (hbound f s le_rfl le_rfl).trans ?_⟩
      rw [add_mul]
      exact add_le_add (mul_le_mul_of_nonneg_left
        ((Finset.le_sup (f := schwartzSeminormFamily ℂ ℝ ℂ)
          (show (0, n + 1) ∈ J by simp [J])) f) hA)
        (mul_le_mul_of_nonneg_left
          ((Finset.le_sup (f := schwartzSeminormFamily ℂ ℝ ℂ)
            (show (m, 0) ∈ J by simp [J])) f) hB))

/-- A power series of continuous functionals converges in the strong dual
when it converges uniformly on each smaller disc and each bounded test set. -/
def StrongDualTaylorOnBall {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (Z : ℂ → E →L[ℂ] ℂ) (c : ℂ) (R : ℝ) : Prop :=
  ∃ a : ℕ → E →L[ℂ] ℂ, ∀ r : ℝ, 0 ≤ r → r < R →
    ∀ B : Set E, Bornology.IsVonNBounded ℂ B →
    TendstoUniformlyOn
      (fun N (p : ℂ × E) => ∑ n ∈ Finset.range N, (p.1 - c) ^ n * a n p.2)
      (fun p => Z p.1 p.2) atTop (Metric.closedBall c r ×ˢ B)

/-- Change the radial exponent linearly and precompose the test with a continuous linear map. -/
theorem StrongDualTaylorOnBall.reparametrize
    {E F : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
    {Z : ℂ → F →L[ℂ] ℂ} {c d : ℂ} {R : ℝ}
    (h : StrongDualTaylorOnBall Z (d*c) R) (hd : d ≠ 0) (L : E →L[ℂ] F) :
    StrongDualTaylorOnBall (fun z => (Z (d*z)).comp L) c (R / ‖d‖) := by
  obtain ⟨a, ha⟩ := h
  refine ⟨fun n => d^n • (a n).comp L, fun r hr hrR B hB => ?_⟩
  let T (p : ℂ × E) : ℂ × F := (d*p.1, L p.2)
  have hd' : 0 < ‖d‖ := norm_pos_iff.mpr hd
  have hr' : ‖d‖ * r < R := by
    rw [mul_comm]
    exact (lt_div_iff₀ hd').mp hrR
  have H := (ha (‖d‖ * r) (by positivity) hr' (L '' B) (hB.image L)).comp T
  have hsubset : Metric.closedBall c r ×ˢ B ⊆
      T ⁻¹' (Metric.closedBall (d*c) (‖d‖*r) ×ˢ (L '' B)) := by
    intro p hp
    refine ⟨?_, mem_image_of_mem L hp.2⟩
    have he : ‖p.1 - c‖ ≤ r := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hp.1
    change dist (d*p.1) (d*c) ≤ ‖d‖ * r
    rw [dist_eq_norm, ← mul_sub, norm_mul]
    gcongr
  convert H.mono hsubset using 1
  · funext N p
    simp only [Function.comp_apply, smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul, T,
      ← mul_sub, mul_pow]
    exact Finset.sum_congr rfl fun n _ => by ring
  · rfl

private theorem schwartzStrongTaylorOnBall_of_cauchy (Z : ℂ → RadialTests →L[ℂ] ℂ)
    (c : ℂ) (R : ℝ≥0) (hR : 0 < R)
    (hZ : ∀ f, AnalyticOnNhd ℂ (fun z => Z z f) (Metric.closedBall c R))
    (J : Finset (ℕ × ℕ)) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ z ∈ Metric.closedBall c R, ∀ f : RadialTests,
      ‖Z z f‖ ≤ C * J.sup (schwartzSeminormFamily ℂ ℝ ℂ) f) :
    StrongDualTaylorOnBall Z c R := by
  let P (f : RadialTests) := cauchyPowerSeries (fun z => Z z f) c R
  let p := J.sup (schwartzSeminormFamily ℂ ℝ ℂ)
  let χ (n : ℕ) (f : RadialTests) := P f n (fun _ => 1)
  have hps (f : RadialTests) : HasFPowerSeriesOnBall (fun z => Z z f) (P f) c R :=
    (hZ f).differentiableOn.hasFPowerSeriesOnBall hR
  have hc : c ∈ Metric.closedBall c (R : ℝ) := Metric.mem_closedBall_self R.coe_nonneg
  have hderiv (n : ℕ) (f : RadialTests) :
      χ n f = (n.factorial : ℂ)⁻¹ • iteratedDeriv n (fun z => Z z f) c := by
    have he := (hps f).factorial_smul (y := 1) n
    rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, Finset.prod_const_one, one_smul,
      ← Nat.cast_smul_eq_nsmul ℂ] at he
    rw [← he, smul_smul, inv_mul_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero n), one_smul]
  have hcoeff (n : ℕ) (f : RadialTests) : ‖χ n f‖ ≤ (C * (R : ℝ)⁻¹ ^ n) * p f := by
    have hpoint (θ : ℝ) : ‖Z (circleMap c R θ) f‖ ≤ C * p f :=
      hbound _ (Metric.sphere_subset_closedBall (circleMap_mem_sphere c R.coe_nonneg θ)) _
    have hI : IntervalIntegrable (fun θ : ℝ => ‖Z (circleMap c R θ) f‖)
        volume 0 (2 * Real.pi) := by
      have hcont : Continuous (fun θ : ℝ => Z (circleMap c R θ) f) := by
        apply (hZ f).continuousOn.comp_continuous (continuous_circleMap c R)
        exact fun θ => Metric.sphere_subset_closedBall (circleMap_mem_sphere c R.coe_nonneg θ)
      exact hcont.norm.intervalIntegrable _ _
    have hint := intervalIntegral.integral_mono Real.two_pi_pos.le hI intervalIntegrable_const hpoint
    simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hint
    calc
      _ ≤ ‖P f n‖ := by
        simpa only [norm_one, Finset.prod_const_one, mul_one] using
          (P f n).le_opNorm (fun _ => (1 : ℂ))
      _ ≤ ((2 * Real.pi)⁻¹ * ∫ θ : ℝ in 0..2 * Real.pi, ‖Z (circleMap c R θ) f‖) *
          |(R : ℝ)|⁻¹ ^ n := norm_cauchyPowerSeries_le _ _ _ _
      _ ≤ ((2 * Real.pi)⁻¹ * ((2 * Real.pi) * (C * p f))) * |(R : ℝ)|⁻¹ ^ n :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hint (by positivity)) (by positivity)
      _ = _ := by
        rw [abs_of_nonneg R.coe_nonneg, inv_mul_cancel_left₀ Real.two_pi_pos.ne']
        ring
  let a (n : ℕ) : RadialTests →L[ℂ] ℂ :=
    SchwartzMap.mkCLMtoNormedSpace (χ n)
      (fun f g => by
        rw [hderiv, hderiv, hderiv]
        have he : (fun z => Z z (f + g)) = fun z => Z z f + Z z g :=
          funext fun z => (Z z).map_add f g
        rw [he, iteratedDeriv_fun_add ((hZ f c hc).contDiffAt) ((hZ g c hc).contDiffAt), smul_add])
      (fun d f => by
        rw [hderiv, hderiv]
        have he : (fun z => Z z (d • f)) = fun z => d • Z z f :=
          funext fun z => (Z z).map_smul d f
        rw [he, iteratedDeriv_fun_const_smul_field, smul_comm]; rfl)
      ⟨J, C * (R : ℝ)⁻¹ ^ n, by positivity, hcoeff n⟩
  refine ⟨a, fun r hr hrR B hB => ?_⟩
  obtain ⟨M, hM, hMp⟩ :=
    (schwartz_withSeminorms ℂ ℝ ℂ).isVonNBounded_iff_finset_seminorm_bounded.mp hB J
  let q := r / (R : ℝ)
  have hR' : 0 < (R : ℝ) := hR
  have hq : ‖q‖ < 1 := by rw [Real.norm_of_nonneg (div_nonneg hr hR'.le)]; exact (div_lt_one hR').mpr hrR
  let terms (n : ℕ) (y : ℂ × RadialTests) := (y.1 - c) ^ n * χ n y.2
  have hterms (n : ℕ) (y : ℂ × RadialTests) (hy : y ∈ Metric.closedBall c r ×ˢ B) :
      ‖terms n y‖ ≤ (C * M) * q ^ n := by
    have hyr : ‖y.1 - c‖ ≤ r := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hy.1
    have hf := hcoeff n y.2
    simp only [terms, norm_mul, norm_pow]
    calc
      _ ≤ r ^ n * ((C * (R : ℝ)⁻¹ ^ n) * p y.2) :=
        mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hyr n) hf (norm_nonneg _) (by positivity)
      _ ≤ r ^ n * ((C * (R : ℝ)⁻¹ ^ n) * M) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hMp _ hy.2).le (by positivity)) (by positivity)
      _ = _ := by dsimp [q]; rw [div_pow, div_eq_mul_inv, inv_pow]; ring
  have hsum (y : ℂ × RadialTests) (hy : y ∈ Metric.closedBall c r ×ˢ B) :
      (∑' n, terms n y) = Z y.1 y.2 := by
    have hyr : ‖y.1 - c‖ ≤ r := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hy.1
    have hyR : y.1 - c ∈ Metric.eball (0 : ℂ) R := by
      rw [Metric.mem_eball, edist_dist, dist_zero_right, ENNReal.ofReal_lt_coe_iff (norm_nonneg _)]
      exact hyr.trans_lt hrR
    have hh := ((hps y.2).hasSum hyR).tsum_eq
    rw [show c + (y.1 - c) = y.1 by abel] at hh
    rw [← hh]
    apply tsum_congr
    intro n
    simp [terms, χ, P, cauchyPowerSeries, ContinuousMultilinearMap.mkPiRing_apply,
      smul_eq_mul]
  have hu := tendstoUniformlyOn_tsum_nat ((summable_geometric_of_norm_lt_one hq).mul_left (C * M))
    hterms
  exact hu.congr_right hsum

/-- Evaluation of the continued Mellin family at each parameter is continuous
and complex linear on Schwartz tests. -/
def schwartzMellinContinuedCLM (s : ℂ) : RadialTests →L[ℂ] ℂ :=
  let n := (mellinTaylorChart_exists s).choose
  radialTaylorRemainderCLM n s (mellinTaylorChart_exists s).choose_spec +
    ∑ k ∈ Finset.range (n + 1), (s + k)⁻¹ • radialTaylorCoeff k

@[simp] theorem schwartzMellinContinuedCLM_apply (s : ℂ) (f : RadialTests) :
    schwartzMellinContinuedCLM s f = mellinTaylorContinued f s := by
  simp only [schwartzMellinContinuedCLM, add_apply,
    sum_apply, smul_apply, smul_eq_mul]
  unfold mellinTaylorContinued mellinTaylorChart
  congr 1
  exact Finset.sum_congr rfl fun k _ => by
    change (s + k)⁻¹ * mellinTaylorCoeff f k = _
    rw [div_eq_mul_inv, mul_comm]


set_option maxHeartbeats 1000000 in
/-- Local strong meromorphy of the Mellin family. The analytic part has a power
series uniform on smaller discs and bounded Schwartz test sets. The remaining
term is the single explicitly identified Dirac-jet functional divided by (z-c). -/
theorem schwartzMellinContinued_strongPrincipalPart (c : ℂ) :
    ∃ (R : ℝ) (Z : ℂ → RadialTests →L[ℂ] ℂ) (P : RadialTests →L[ℂ] ℂ),
      0 < R ∧ StrongDualTaylorOnBall Z c R ∧
      (∀ z ∈ Metric.closedBall c R, schwartzMellinContinuedCLM z = Z z + (z-c)⁻¹ • P) ∧
      (∀ k : ℕ, c = -(k : ℂ) → ∀ f : RadialTests, P f = mellinTaylorCoeff f k) ∧
      ((∀ k : ℕ, c ≠ -(k : ℂ)) → P = 0) := by
  classical
  obtain ⟨n, hn⟩ := mellinTaylorChart_exists c
  let K := Finset.range (n + 1)
  let J := K.filter (fun k : ℕ => c + (k : ℂ) ≠ 0)
  let L := K.filter (fun k : ℕ => c + (k : ℂ) = 0)
  let U := {z : ℂ | -((n + 1 : ℕ) : ℝ) < z.re} ∩
    ⋂ k : J, {z : ℂ | z + (k.val : ℂ) ≠ 0}
  have hU : IsOpen U := by
    apply (isOpen_lt continuous_const Complex.continuous_re).inter
    exact isOpen_iInter_of_finite fun k =>
      isOpen_ne_fun (continuous_id.add continuous_const) continuous_const
  have hc : c ∈ U := ⟨hn, Set.mem_iInter.mpr fun k => (Finset.mem_filter.mp k.property).2⟩
  obtain ⟨r, hr, hclosed⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hc)
  let R : ℝ≥0 := ⟨r, hr.le⟩
  let Z (z : ℂ) : RadialTests →L[ℂ] ℂ :=
    (if hz : -((n + 1 : ℕ) : ℝ) < z.re then radialTaylorRemainderCLM n z hz else 0) +
      ∑ k ∈ J, (z + k)⁻¹ • radialTaylorCoeff k
  let P : RadialTests →L[ℂ] ℂ := ∑ k ∈ L, radialTaylorCoeff k
  have hZeval (z : ℂ) (hz : -((n + 1 : ℕ) : ℝ) < z.re) (f : RadialTests) :
      Z z f = mellin (mellinTaylorRemainder f n) z +
        ∑ k ∈ J, mellinTaylorCoeff f k / (z + k) := by
    simp only [Z, dite_eq_left hz, add_apply, sum_apply, smul_apply, smul_eq_mul]
    congr 1
    exact Finset.sum_congr rfl fun k _ => by
      change (z + k)⁻¹ * mellinTaylorCoeff f k = _
      rw [div_eq_mul_inv, mul_comm]
  have hZ : ∀ f : RadialTests, AnalyticOnNhd ℂ (fun z => Z z f) (Metric.closedBall c R) := by
    intro f z hz
    have hzu := hclosed hz
    have hfun : (fun y => Z y f) =ᶠ[𝓝 z] fun y =>
        mellin (mellinTaylorRemainder f n) y + ∑ k ∈ J, mellinTaylorCoeff f k / (y + k) := by
      filter_upwards [hU.mem_nhds hzu] with y hy using hZeval y hy.1 f
    apply AnalyticAt.congr _ hfun.symm
    apply (mellinTaylorRemainder_analytic f.smooth' (schwartz_radial_rapid f) n hzu.1).add
    exact Finset.analyticAt_fun_sum _ fun k hk => analyticAt_const.div
      (analyticAt_id.add analyticAt_const) (Set.mem_iInter.mp hzu.2 ⟨k, hk⟩)
  let D := Metric.closedBall c (R : ℝ)
  obtain ⟨σ₀, hσ₀, hlo⟩ := (isCompact_closedBall c (R : ℝ)).exists_isMinOn
    ⟨c, Metric.mem_closedBall_self R.coe_nonneg⟩ Complex.continuous_re.continuousOn
  obtain ⟨σ₁, hσ₁, hhi⟩ := (isCompact_closedBall c (R : ℝ)).exists_isMaxOn
    ⟨c, Metric.mem_closedBall_self R.coe_nonneg⟩ Complex.continuous_re.continuousOn
  obtain ⟨A, B, m, hA, hB, hrem⟩ :=
    radialTaylor_mellin_bound n (σ₁ := σ₁.re) (hclosed hσ₀).1
  have hRational : ∀ k ∈ J, ∃ M : ℝ, 0 ≤ M ∧ ∀ z ∈ D, ‖(z + (k : ℂ))⁻¹‖ ≤ M := by
    intro k hk
    have hcon : ContinuousOn (fun z : ℂ => ‖(z + (k : ℂ))⁻¹‖) D :=
      ((continuous_id.add continuous_const).continuousOn.inv₀ fun z hz =>
        Set.mem_iInter.mp (hclosed hz).2 ⟨k, hk⟩).norm
    obtain ⟨u, hu⟩ := (isCompact_closedBall c (R : ℝ)).bddAbove_image hcon
    exact ⟨max 0 u, le_max_left _ _, fun z hz => (hu (mem_image_of_mem _ hz)).trans (le_max_right _ _)⟩
  choose M hM hMb using hRational
  let V : Finset (ℕ × ℕ) := {(0, n + 1), (m, 0)} ∪ J.image (fun k => (0, k))
  let q := V.sup (schwartzSeminormFamily ℂ ℝ ℂ)
  have hnV : (0, n + 1) ∈ V := Finset.mem_union_left _ (by simp)
  have hmV : (m, 0) ∈ V := Finset.mem_union_left _ (by simp)
  have hle (i : ℕ × ℕ) (hi : i ∈ V) (f : RadialTests) :
      SchwartzMap.seminorm ℂ i.1 i.2 f ≤ q f :=
    (Finset.le_sup (f := schwartzSeminormFamily ℂ ℝ ℂ) hi) f
  let S := ∑ k ∈ J, (if hk : k ∈ J then M k hk else 0) * ‖(k.factorial : ℂ)⁻¹‖
  have hS : 0 ≤ S :=
    Finset.sum_nonneg fun k hk => mul_nonneg (by simpa only [dite_eq_left hk] using hM k hk) (norm_nonneg _)
  have hzbound (z : ℂ) (hz : z ∈ D) (f : RadialTests) :
      ‖Z z f‖ ≤ (A + B + S) * q f := by
    rw [hZeval z (hclosed hz).1 f]
    have hrem' := hrem f z (hlo hz) (hhi hz)
    have hsum : ‖∑ k ∈ J, mellinTaylorCoeff f k / (z + k)‖ ≤ S * q f := by
      refine (norm_sum_le _ _).trans ?_
      unfold S
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro k hk
      rw [dite_eq_left hk, div_eq_mul_inv, mellinTaylorCoeff, norm_mul, norm_mul]
      have hder₀ : ‖iteratedDeriv k f 0‖ ≤ SchwartzMap.seminorm ℂ 0 k f :=
        by simpa only [pow_zero, one_mul] using SchwartzMap.le_seminorm' ℂ 0 k f 0
      have hder : ‖iteratedDeriv k f 0‖ ≤ q f := hder₀.trans
        (hle (0, k) (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hk)) f)
      calc
        _ = ‖(z + (k : ℂ))⁻¹‖ * (‖(k.factorial : ℂ)⁻¹‖ * ‖iteratedDeriv k f 0‖) := mul_comm _ _
        _ ≤ M k hk * (‖(k.factorial : ℂ)⁻¹‖ * q f) :=
          mul_le_mul (hMb k hk z hz) (mul_le_mul_of_nonneg_left hder (norm_nonneg _))
            (by positivity) (hM k hk)
        _ = _ := by ring
    calc
      _ ≤ _ := norm_add_le _ _
      _ ≤ (A * q f + B * q f) + S * q f := add_le_add (hrem'.trans (add_le_add
        (mul_le_mul_of_nonneg_left (hle (0, n + 1) hnV f) hA)
        (mul_le_mul_of_nonneg_left (hle (m, 0) hmV f) hB))) hsum
      _ = _ := by ring
  refine ⟨r, Z, P, hr, schwartzStrongTaylorOnBall_of_cauchy Z c R hr hZ V
    (A+B+S) (by positivity) hzbound, ?_, ?_, ?_⟩
  · intro z hz
    apply ContinuousLinearMap.ext
    intro f
    rw [schwartzMellinContinuedCLM_apply, mellinTaylorContinued_eq_chart (f := (f : ℝ → ℂ)) f.smooth' (schwartz_radial_rapid f)
      n (hclosed hz).1, add_apply, hZeval z (hclosed hz).1 f, mellinTaylorChart]
    rw [← Finset.sum_filter_add_sum_filter_not K (fun k : ℕ => c + (k : ℂ) ≠ 0)]
    simp only [J, L, P, not_ne_iff, add_assoc, smul_apply, sum_apply, smul_eq_mul, Finset.mul_sum]
    congr 2
    apply Finset.sum_congr rfl
    intro k hk
    have he := (Finset.mem_filter.mp hk).2
    rw [show z + (k : ℂ) = z - c by linear_combination he, div_eq_mul_inv, mul_comm]
    rfl
  · intro k hk f
    have hkn : k ≤ n := by
      rw [hk, Complex.neg_re, Complex.natCast_re] at hn
      exact Nat.lt_succ_iff.mp (by exact_mod_cast (neg_lt_neg_iff.mp hn))
    have hL : L = {k} := by
      ext j
      change j ∈ K.filter (fun i : ℕ => c + (i : ℂ) = 0) ↔ j ∈ ({k} : Finset ℕ)
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · intro hj
        have he : (j : ℂ) = k := by rw [hk] at hj; linear_combination hj.2
        exact_mod_cast he
      · rintro rfl
        exact ⟨Finset.mem_range_succ_iff.mpr hkn, by simp [hk]⟩
    simp [P, hL]
    rfl
  · intro hc'
    have hL : L = ∅ := Finset.filter_false_of_mem fun k _ h =>
      hc' k (eq_neg_of_add_eq_zero_left h)
    simp [P, hL]


end

end Masullo
