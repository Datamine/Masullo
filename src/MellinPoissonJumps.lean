import JumpPoisson
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.Analysis.MeanInequalities

open Complex Filter Function MeasureTheory Set Topology

namespace Masullo

noncomputable section

private theorem superExponentialLogDecay_of_global
    {u : ℝ → ℂ} (h : ∀ R : ℝ, 0 ≤ R →
      ∃ K : ℝ, 0 < K ∧ ∀ x, ‖u x‖ ≤ K * Real.exp (-R * |x|)) :
    SuperExponentialLogDecay u := by
  constructor
  · obtain ⟨K, _, hK⟩ := h 0 le_rfl
    exact ⟨K, fun x => by simpa using hK x⟩
  · intro n
    obtain ⟨K, hK, hbound⟩ := h n (Nat.cast_nonneg n)
    exact ⟨K, 1, hK, zero_lt_one, fun x _ => hbound x⟩

private theorem SuperExponentialLogDecay.const_mul {u : ℝ → ℂ} (hu : SuperExponentialLogDecay u)
    (z : ℂ) : SuperExponentialLogDecay (fun x => z * u x) := by
  apply superExponentialLogDecay_of_global
  intro R hR
  obtain ⟨M, hM, hMb⟩ := hu.global_bound R hR
  refine ⟨(‖z‖ + 1) * M, by positivity, fun x => ?_⟩
  rw [norm_mul, mul_assoc]
  exact mul_le_mul (by linarith) (hMb x) (norm_nonneg _) (by positivity)

private theorem SuperExponentialLogDecay.add {u v : ℝ → ℂ} (hu : SuperExponentialLogDecay u)
    (hv : SuperExponentialLogDecay v) : SuperExponentialLogDecay (fun x => u x + v x) := by
  apply superExponentialLogDecay_of_global
  intro R hR
  obtain ⟨K, hK, hKu⟩ := hu.global_bound R hR
  obtain ⟨M, hM, hMv⟩ := hv.global_bound R hR
  refine ⟨K + M, by positivity, fun x => ?_⟩
  rw [add_mul]
  exact (norm_add_le _ _).trans (add_le_add (hKu x) (hMv x))

private def twistOnLattice (u : ℝ → ℂ) (d : ℝ) (ζ : ℂ) (x : ℝ) : ℂ :=
  Complex.exp (ζ * (x : ℂ)) * u (d * x)

private theorem SuperExponentialLogDecay.twist {u : ℝ → ℂ} (hu : SuperExponentialLogDecay u)
    {d : ℝ} (hd : d ≠ 0) (ζ : ℂ) : SuperExponentialLogDecay (twistOnLattice u d ζ) := by
  apply superExponentialLogDecay_of_global
  intro R hR
  have hd₀ := abs_pos.mpr hd
  obtain ⟨K, hK, hb⟩ := hu.global_bound ((R + |ζ.re|) / |d|) (by positivity)
  refine ⟨K, hK, fun x => ?_⟩
  have he : ‖Complex.exp (ζ * (x : ℂ))‖ ≤ Real.exp (|ζ.re| * |x|) := by
    rw [norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    exact Real.exp_le_exp.mpr ((le_abs_self (ζ.re * x)).trans_eq (abs_mul _ _))
  have hb' : ‖u (d * x)‖ ≤ K * Real.exp (-(R + |ζ.re|) * |x|) := by
    have hh := hb (d * x)
    rw [abs_mul, ← mul_assoc, neg_mul, div_mul_cancel₀ _ hd₀.ne'] at hh
    exact hh
  calc
    _ ≤ Real.exp (|ζ.re| * |x|) * (K * Real.exp (-(R + |ζ.re|) * |x|)) := by
      rw [twistOnLattice, norm_mul]
      exact mul_le_mul he hb' (norm_nonneg _) (Real.exp_nonneg _)
    _ = K * (Real.exp (|ζ.re| * |x|) * Real.exp (-(R + |ζ.re|) * |x|)) := by ring
    _ = _ := by rw [← Real.exp_add]; congr 2; ring

private theorem twistOnLattice_measurable {u : ℝ → ℂ} (hu : Measurable u) (d : ℝ) (ζ : ℂ) :
    Measurable (twistOnLattice u d ζ) := by
  have hc : Continuous (fun x : ℝ => Complex.exp (ζ * (x : ℂ))) := by fun_prop
  exact hc.measurable.mul (hu.comp (measurable_const.mul measurable_id))

private theorem twistOnLattice_deriv {u : ℝ → ℂ} {d x : ℝ} {v ζ : ℂ}
    (h : HasDerivAt u v (d * x)) :
    HasDerivAt (twistOnLattice u d ζ)
      (Complex.exp (ζ * (x : ℂ)) * (ζ * u (d * x) + (d : ℂ) * v)) x := by
  have he : HasDerivAt (fun y : ℝ => Complex.exp (ζ * (y : ℂ)))
      (Complex.exp (ζ * (x : ℂ)) * ζ) x := by
    simpa only [one_mul, mul_one] using (((hasDerivAt_id' (x : ℂ)).const_mul ζ).cexp).comp_ofReal
  have hh : HasDerivAt (fun t : ℝ => d * t) d x := (hasDerivAt_id x).const_mul d |>.congr_deriv (mul_one _)
  have hd := he.mul (h.scomp x hh)
  simp only [Function.comp_def, Complex.real_smul] at hd
  have hval : Complex.exp (ζ * (x : ℂ)) * ζ * u (d * x) +
      Complex.exp (ζ * (x : ℂ)) * ((d : ℂ) * v) =
      Complex.exp (ζ * (x : ℂ)) * (ζ * u (d * x) + (d : ℂ) * v) := by ring
  rw [hval] at hd
  exact hd

private theorem scale_between_rays {d x : ℝ} (hd : d ≠ 0) :
    (Tendsto (fun t : ℝ => d * t) (𝓝[<] x)
      (if 0 < d then 𝓝[<] (d * x) else 𝓝[>] (d * x))) ∧
    (Tendsto (fun t : ℝ => d * t) (𝓝[>] x)
      (if 0 < d then 𝓝[>] (d * x) else 𝓝[<] (d * x))) := by
  have hc : Continuous (fun t : ℝ => d * t) := by fun_prop
  by_cases h : 0 < d
  · simp only [ite_eq_left h]
    constructor
    · refine tendsto_nhdsWithin_iff.mpr ⟨(hc.tendsto x).mono_left nhdsWithin_le_nhds, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with t (ht : t < x)
      exact mul_lt_mul_of_pos_left ht h
    · refine tendsto_nhdsWithin_iff.mpr ⟨(hc.tendsto x).mono_left nhdsWithin_le_nhds, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with t (ht : x < t)
      exact mul_lt_mul_of_pos_left ht h
  · simp only [ite_eq_right h]
    have hn : d < 0 := lt_of_le_of_ne (le_of_not_gt h) hd
    constructor
    · refine tendsto_nhdsWithin_iff.mpr ⟨(hc.tendsto x).mono_left nhdsWithin_le_nhds, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with t (ht : t < x)
      exact mul_lt_mul_of_neg_left ht hn
    · refine tendsto_nhdsWithin_iff.mpr ⟨(hc.tendsto x).mono_left nhdsWithin_le_nhds, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with t (ht : x < t)
      exact mul_lt_mul_of_neg_left ht hn

private theorem poissonMellin_coefficient (φ : ℝ → ℂ) (d : ℝ) (ζ : ℂ) (m : ℤ) :
    (∫ x, poissonPhase m x * twistOnLattice (fun z => φ (Real.exp z)) d ζ x) =
      (|d|⁻¹ : ℝ) • mellin φ ((ζ + (m : ℂ) * (2 * Real.pi * I)) / d) := by
  rw [← mellin_comp_rpow, mellin_eq_log_integral]
  apply integral_congr_ae
  filter_upwards [] with x
  unfold poissonPhase twistOnLattice
  rw [Real.rpow_def_of_pos (Real.exp_pos x), Real.log_exp, mul_comm x d,
    ← mul_assoc, ← Complex.exp_add]
  congr 2
  ring

/-- Corrected B.4.1.2. The spectral sum is taken over symmetric intervals of
integers. The sample factor is the positive length of the log lattice,
including for a reversed generator. The character on the cyclic lattice
is parametrized by the nonzero value `Complex.exp ζ` on its generator. -/
theorem mellin_poisson_finite_jumps
    (φ : ℝ → ℂ) (S : Finset ℝ) (v left right : ℝ → ℂ)
    {θ : ℝ} (hθ : 0 < θ) (hθ₁ : θ ≠ 1) (ζ : ℂ)
    (hu : SuperExponentialLogDecay (fun x => φ (Real.exp x)))
    (hv : SuperExponentialLogDecay v)
    (hderiv : ∀ x ∉ S, HasDerivAt (fun y => φ (Real.exp y)) (v x) x)
    (hcv : ContinuousOn v ((S : Set ℝ)ᶜ))
    (hl : ∀ x, Tendsto (fun y => φ (Real.exp y)) (𝓝[<] x) (𝓝 (left x)))
    (hr : ∀ x, Tendsto (fun y => φ (Real.exp y)) (𝓝[>] x) (𝓝 (right x))) :
    let d := Real.log θ
    let samples := fun n : ℤ =>
      Complex.exp ζ ^ n * (left (d * n) + right (d * n)) / 2
    (Summable fun n => ‖samples n‖) ∧
      Tendsto (fun N : ℕ => ∑ m ∈ Finset.Icc (-(N : ℤ)) N,
        mellin φ ((ζ + (m : ℂ) * (2 * Real.pi * I)) / d)) atTop
        (𝓝 (((|d| : ℝ) : ℂ) * ∑' n : ℤ, samples n)) := by
  classical
  let d := Real.log θ
  have hd : d ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one hθ hθ₁
  let u := fun x => φ (Real.exp x)
  let U := twistOnLattice u d ζ
  let W := fun x => ζ * u x + (d : ℂ) * v x
  let V := twistOnLattice W d ζ
  let e : ℝ ↪ ℝ := ⟨fun x => x / d, fun _ _ he => (div_left_inj' hd).mp he⟩
  let J := S.map e
  let L (x : ℝ) := Complex.exp (ζ * (x : ℂ)) * (if 0 < d then left (d * x) else right (d * x))
  let R (x : ℝ) := Complex.exp (ζ * (x : ℂ)) * (if 0 < d then right (d * x) else left (d * x))
  have hmu : Measurable u := ContinuousOn.measurable_of_countable_compl
    (s := (S : Set ℝ)ᶜ) (fun x hx => (hderiv x hx).continuousAt.continuousWithinAt)
    (by simpa only [compl_compl] using S.finite_toSet.countable)
  have hmv : Measurable v := ContinuousOn.measurable_of_countable_compl hcv
    (by simpa only [compl_compl] using S.finite_toSet.countable)
  have hmU : Measurable U := twistOnLattice_measurable hmu d ζ
  have hmV : Measurable V := twistOnLattice_measurable
    ((measurable_const.mul hmu).add (measurable_const.mul hmv)) d ζ
  have hU : SuperExponentialLogDecay U := hu.twist hd ζ
  have hV : SuperExponentialLogDecay V := ((hu.const_mul ζ).add (hv.const_mul (d : ℂ))).twist hd ζ
  have Hderiv (x : ℝ) (hx : x ∉ J) : HasDerivAt U (V x) x := by
    apply twistOnLattice_deriv
    apply hderiv
    intro hh
    apply hx
    apply Finset.mem_map.mpr
    refine ⟨d * x, hh, ?_⟩
    change d * x / d = x
    rw [mul_comm, mul_div_cancel_right₀ _ hd]
  have he : Continuous (fun x : ℝ => Complex.exp (ζ * (x : ℂ))) := by fun_prop
  have hL (x : ℝ) : Tendsto U (𝓝[<] x) (𝓝 (L x)) := by
    apply ((he.tendsto x).mono_left nhdsWithin_le_nhds).mul
    have h := (scale_between_rays (x := x) hd).1
    by_cases hp : 0 < d
    · rw [ite_eq_left hp] at h ⊢
      exact (hl (d * x)).comp h
    · rw [ite_eq_right hp] at h ⊢
      exact (hr (d * x)).comp h
  have hR (x : ℝ) : Tendsto U (𝓝[>] x) (𝓝 (R x)) := by
    apply ((he.tendsto x).mono_left nhdsWithin_le_nhds).mul
    have h := (scale_between_rays (x := x) hd).2
    by_cases hp : 0 < d
    · rw [ite_eq_left hp] at h ⊢
      exact (hr (d * x)).comp h
    · rw [ite_eq_right hp] at h ⊢
      exact (hl (d * x)).comp h
  obtain ⟨hs, ht⟩ := jumpPoisson_period_one J hU hV hmU hmV (hU.integrable hmU) Hderiv hL hR
  have hsamp (n : ℤ) : (L n + R n) / 2 =
      Complex.exp ζ ^ n * (left (d * n) + right (d * n)) / 2 := by
    dsimp only [L, R]
    rw [← mul_add, mul_comm ζ, Complex.ofReal_intCast, Complex.exp_int_mul]
    by_cases hp : 0 < d
    · simp [hp]
    · simp [hp, add_comm]
  simp only [hsamp] at hs ht
  refine ⟨hs, ?_⟩
  have hb : ((|d| : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (abs_pos.mpr hd).ne'
  have hscaled := ht.const_mul ((|d| : ℝ) : ℂ)
  apply hscaled.congr'
  filter_upwards [] with N
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  rw [poissonMellin_coefficient, Complex.real_smul, Complex.ofReal_inv, ← mul_assoc,
    mul_inv_cancel₀ hb, one_mul]


/-- The logarithmic sampling locations are the actual powers of the
positive generator. -/
theorem mellin_poisson_log_sample (θ : ℝ) (hθ : 0 < θ) (n : ℤ) :
    Real.exp (Real.log θ * (n : ℝ)) = θ ^ n := by
  apply Complex.ofReal_injective
  rw [Complex.ofReal_exp, Complex.ofReal_mul, Complex.ofReal_intCast, mul_comm,
    Complex.exp_int_mul, ← Complex.ofReal_exp, Real.exp_log hθ, Complex.ofReal_zpow]

/-- Passage through the logarithmic coordinate preserves both one-sided
limits of the original test at every positive argument. -/
theorem mellin_poisson_oneSided_at_exp
    {φ : ℝ → ℂ} {x : ℝ} {a b : ℂ}
    (ha : Tendsto (fun y => φ (Real.exp y)) (𝓝[<] x) (𝓝 a))
    (hb : Tendsto (fun y => φ (Real.exp y)) (𝓝[>] x) (𝓝 b)) :
    Tendsto φ (𝓝[<] (Real.exp x)) (𝓝 a) ∧
      Tendsto φ (𝓝[>] (Real.exp x)) (𝓝 b) := by
  have h : Tendsto Real.log (𝓝 (Real.exp x)) (𝓝 x) := by
    simpa only [Real.log_exp] using
      (Real.continuousAt_log (Real.exp_pos x).ne').tendsto
  have hL : Tendsto Real.log (𝓝[<] (Real.exp x)) (𝓝[<] x) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨h.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [Ioo_mem_nhdsLT (Real.exp_pos x)] with y hy
    exact (Real.log_exp x) ▸ Real.strictMonoOn_log hy.1 (Real.exp_pos x) hy.2
  have hR : Tendsto Real.log (𝓝[>] (Real.exp x)) (𝓝[>] x) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨h.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with y (hy : Real.exp x < y)
    exact (Real.log_exp x) ▸ Real.strictMonoOn_log (Real.exp_pos x)
      ((Real.exp_pos x).trans hy) hy
  refine ⟨(ha.comp hL).congr' ?_, (hb.comp hR).congr' ?_⟩
  · filter_upwards [Ioo_mem_nhdsLT (Real.exp_pos x)] with y hy
    exact congrArg φ (Real.exp_log hy.1)
  · filter_upwards [self_mem_nhdsWithin] with y (hy : Real.exp x < y)
    exact congrArg φ (Real.exp_log ((Real.exp_pos x).trans hy))


open ContinuousMap Filter MeasureTheory Set in
open scoped Asymptotics FourierTransform in
/-- If a continuously differentiable function and its derivative both decay at least as
fast as the inverse square, its Fourier samples on the integer lattice are absolutely summable. -/
private theorem summable_norm_fourier_int_of_isBigO {g : ℝ → ℂ} (hg : ContDiff ℝ 1 g)
    (h : g =O[cocompact ℝ] (fun x : ℝ ↦ |x| ^ (-2 : ℝ)))
    (h' : deriv g =O[cocompact ℝ] (fun x : ℝ ↦ |x| ^ (-2 : ℝ))) :
    Summable (fun m : ℤ ↦ ‖𝓕 g (m : ℝ)‖) := by
  have hs (v : C(ℝ, ℂ)) (hv : (v : ℝ → ℂ) =O[cocompact ℝ] (fun x : ℝ ↦ |x| ^ (-2 : ℝ)))
      (K : TopologicalSpace.Compacts ℝ) :
      Summable (fun m : ℤ ↦ ‖(v.comp (ContinuousMap.addRight m)).restrict K‖) :=
    summable_of_isBigO (Real.summable_abs_int_rpow one_lt_two)
      ((isBigO_norm_restrict_cocompact v (by norm_num) hv K).comp_tendsto Int.tendsto_coe_cofinite)
  -- Periodize the derivative and use Parseval to get square-summable samples.
  let v : C(ℝ, ℂ) := ⟨deriv g, hg.continuous_deriv (by simp)⟩
  let V : C(UnitAddCircle, ℂ) :=
    ⟨(v.periodic_tsum_comp_add_zsmul 1).lift,
      continuous_coinduced_dom.mpr (map_continuous _)⟩
  have hv (m : ℤ) : fourierCoeff V m = 𝓕 (deriv g) (m : ℝ) :=
    Real.fourierCoeff_tsum_comp_add (hs v h') m
  have hsq : Summable (fun m : ℤ ↦ ‖𝓕 (deriv g) (m : ℝ)‖ ^ 2) := by
    simpa only [fourierCoeff_toLp, hv] using
      (hasSum_sq_fourierCoeff (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ V)).summable
  let u : C(ℝ, ℂ) := ⟨g, hg.continuous⟩
  let K : TopologicalSpace.Compacts ℝ := ⟨Icc 0 1, isCompact_Icc⟩
  have hi : Integrable g := Real.integrable_of_summable_norm_Icc (f := u) (hs u h K)
  have hi' : Integrable (deriv g) := Real.integrable_of_summable_norm_Icc (f := v) (hs v h' K)
  -- On nonzero modes the derivative contributes a factor of `2 * π * |m|`.
  have hpow : Summable (fun m : ℤ ↦ (|(m : ℝ)|⁻¹) ^ (2 : ℝ)) := by
    simpa only [Real.inv_rpow (abs_nonneg _), Real.rpow_neg (abs_nonneg _)] using
      Real.summable_abs_int_rpow one_lt_two
  have hprod := Real.summable_mul_of_Lp_Lq_of_nonneg Real.HolderConjugate.two_two
    (fun m : ℤ ↦ norm_nonneg (𝓕 (deriv g) (m : ℝ)))
    (fun m : ℤ ↦ inv_nonneg.mpr (abs_nonneg (m : ℝ)))
    (by simpa only [Real.rpow_two] using hsq) hpow
  apply (hprod.mul_left ((2 * Real.pi)⁻¹)).of_norm_bounded_eventually
  filter_upwards [eventually_cofinite_ne (0 : ℤ)] with m hm
  have hm' : |(m : ℝ)| ≠ 0 := abs_ne_zero.mpr (by exact_mod_cast hm)
  rw [Real.fourier_deriv hi (hg.differentiable (by simp)) hi', norm_smul]
  simp only [Complex.norm_mul, Complex.norm_ofNat 2, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg Real.pi_pos.le, Complex.norm_I, mul_one, abs_of_nonneg (norm_nonneg _)]
  field_simp [Real.pi_ne_zero, hm']
  exact le_rfl


open scoped Asymptotics FourierTransform in
/-- The smooth case of Remark B.4.1.4. One continuous logarithmic derivative
with superexponential decay suffices. The Parseval argument adapts the
Apache-2.0 RiemannMasullo project at commit 41e71dade6ccde0d61e2230c32ec2ba0ae3fb975. -/
theorem mellin_poisson_samples_summable_of_smooth (φ : ℝ → ℂ)
    {d : ℝ} (hd : d ≠ 0) (ζ : ℂ)
    (hsmooth : ContDiff ℝ 1 (fun x => φ (Real.exp x)))
    (hu : SuperExponentialLogDecay (fun x => φ (Real.exp x)))
    (hv : SuperExponentialLogDecay (deriv (fun x => φ (Real.exp x)))) :
    Summable (fun m : ℤ => ‖mellin φ ((ζ + (m : ℂ) * (2 * Real.pi * I)) / d)‖) := by
  let u : ℝ → ℂ := fun x => φ (Real.exp x)
  let g := twistOnLattice u d ζ
  have hg : ContDiff ℝ 1 g := by
    unfold g twistOnLattice
    exact ((contDiff_const.mul (Complex.ofRealCLM.contDiff (n := 1))).cexp).mul
      (hsmooth.comp (contDiff_const.mul contDiff_id))
  have hD : deriv g = fun x =>
      ζ * twistOnLattice u d ζ x + (d : ℂ) * twistOnLattice (deriv u) d ζ x := by
    funext x
    rw [(twistOnLattice_deriv (ζ := ζ) ((hsmooth.differentiable (by simp) (d*x)).hasDerivAt)).deriv]
    unfold twistOnLattice
    ring
  have hg' : SuperExponentialLogDecay (deriv g) := by
    rw [hD]
    exact ((hu.twist hd ζ).const_mul ζ).add ((hv.twist hd ζ).const_mul d)
  have hbig {v : ℝ → ℂ} (h : SuperExponentialLogDecay v) :
      v =O[cocompact ℝ] (fun x : ℝ => |x| ^ (-2 : ℝ)) := by
    obtain ⟨C, _, hC⟩ := h.global_bound 1 zero_le_one
    refine (Asymptotics.IsBigO.of_bound (g := fun x : ℝ => Real.exp (-|x|)) C
      (Eventually.of_forall fun x => ?_)).trans ?_
    · simpa only [Real.norm_eq_abs, Real.abs_exp, neg_one_mul] using hC x
    · simpa only [Function.comp_def, neg_one_mul, Real.norm_eq_abs] using
        (isLittleO_exp_neg_mul_rpow_atTop Real.zero_lt_one (-2)).isBigO.comp_tendsto
          (tendsto_norm_cocompact_atTop (E := ℝ))
  have hsum := (summable_norm_fourier_int_of_isBigO hg (hbig (hu.twist hd ζ)) (hbig hg')).comp_injective
    (neg_injective : Function.Injective (fun m : ℤ => -m))
  refine (hsum.mul_left |d|).congr fun m => ?_
  have hsample : 𝓕 g ((-m : ℤ) : ℝ) =
      (|d|⁻¹ : ℝ) • mellin φ ((ζ + (m : ℂ) * (2 * Real.pi * I)) / d) := by
    rw [Real.fourier_real_eq_integral_exp_smul, ← poissonMellin_coefficient φ d ζ m]
    apply integral_congr_ae
    refine Eventually.of_forall fun x => ?_
    change Complex.exp ((↑(-2 * Real.pi * x * ((-m : ℤ) : ℝ)) : ℂ) * I) • g x =
      poissonPhase m x * g x
    rw [smul_eq_mul, poissonPhase]
    congr 2
    push_cast
    ring
  change |d| * ‖𝓕 g ((-m : ℤ) : ℝ)‖ = _
  rw [hsample, norm_smul, Real.norm_eq_abs, abs_inv, abs_abs, ← mul_assoc,
    mul_inv_cancel₀ (abs_ne_zero.mpr hd), one_mul]

end
end Masullo
