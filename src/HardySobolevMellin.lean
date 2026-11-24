import HardySobolevDuality
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

open Filter Function MeasureTheory Set Topology
open scoped ENNReal FourierTransform SchwartzMap

namespace Masullo

noncomputable section

local notation "Tests" => (logExponentialDecaySubmodule (univ : Set ℝ))

private def momentKernel (f : Tests) (n : ℕ) (z : ℂ) (x : ℝ) : ℂ :=
  Complex.exp (z * (x : ℂ)) * ((x : ℂ) ^ n * f.val x)

private def momentTwist (f : Tests) (n : ℕ) (a : ℝ) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => (x : ℂ) ^ n)
    (logExponentialDecayTwist univ ⟨a, mem_univ a⟩ f)

private theorem momentTwist_apply (f : Tests) (n : ℕ) (a x : ℝ) :
    momentTwist f n a x = Real.exp (a * x) * ((x : ℂ) ^ n * f.val x) := by
  have h : (fun x : ℝ => (x : ℂ) ^ n).HasTemperateGrowth :=
    (Complex.hasTemperateGrowth_ofReal.comp Function.HasTemperateGrowth.id').pow n
  unfold momentTwist
  rw [SchwartzMap.smulLeftCLM_apply_apply h, logExponentialDecayTwist_apply, smul_eq_mul]
  ring


private theorem momentTwist_norm_sq (f : Tests) (n : ℕ) (a x : ℝ) :
    ‖momentTwist f n a x‖ ^ 2 = ‖f.val x‖ ^ 2 *
      (Real.exp (2 * a * x) * (x ^ 2) ^ n) := by
  have hp : (|x| ^ n) ^ 2 = (x ^ 2) ^ n := by
    rw [← pow_mul, Nat.mul_comm, pow_mul, sq_abs]
  simp only [momentTwist_apply, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), mul_pow, hp, ← Real.exp_nat_mul]
  push_cast
  ring_nf

private theorem momentKernel_norm (f : Tests) (n : ℕ) (z : ℂ) (x : ℝ) :
    ‖momentKernel f n z x‖ = ‖momentTwist f n z.re x‖ := by
  simp only [momentKernel, momentTwist_apply, norm_mul, Complex.norm_exp,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
    Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]

private theorem momentKernel_meas (f : Tests) (n : ℕ) (z : ℂ) :
    AEStronglyMeasurable (momentKernel f n z) volume := by
  have hf : Continuous f.val := by
    apply (momentTwist f 0 0).continuous.congr
    intro x
    simp only [momentTwist_apply, zero_mul, Real.exp_zero, Complex.ofReal_one, pow_zero, one_mul]
  exact (((Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).mul
    ((Complex.continuous_ofReal.pow n).mul hf)).aestronglyMeasurable :
      AEStronglyMeasurable (momentKernel f n z) volume)

private theorem momentIntegral_hasDerivAt (f : Tests) (n : ℕ) (z : ℂ) :
    HasDerivAt (fun w => ∫ x, momentKernel f n w x)
      (∫ x, momentKernel f (n + 1) z x) z := by
  let a := z.re - 1
  let b := z.re + 1
  have hz : Complex.re ⁻¹' Ioo a b ∈ 𝓝 z :=
    (isOpen_Ioo.preimage Complex.continuous_re).mem_nhds (show a < z.re ∧ z.re < b by
      dsimp [a, b]; constructor <;> linarith)
  let A := momentTwist f (n + 1) a
  let B := momentTwist f (n + 1) b
  have hbound (w : ℂ) (hw : w ∈ Complex.re ⁻¹' Ioo a b) (x : ℝ) :
      ‖momentKernel f (n + 1) w x‖ ≤ ‖A x‖ + ‖B x‖ := by
    have ha : a < w.re := hw.1
    have hb : w.re < b := hw.2
    rw [momentKernel_norm]
    dsimp [A, B]
    simp only [momentTwist_apply, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    by_cases hx : 0 ≤ x
    · exact (mul_le_mul_of_nonneg_right
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hb.le hx)) (by positivity)).trans
          (le_add_of_nonneg_left (by positivity))
    · exact (mul_le_mul_of_nonneg_right
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_right ha.le (le_of_not_ge hx))) (by positivity)).trans
          (le_add_of_nonneg_right (by positivity))
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le hz
    (.of_forall (momentKernel_meas f n))
    ((momentTwist f n z.re).integrable.norm.mono' (momentKernel_meas f n z)
      (.of_forall fun x => (momentKernel_norm f n z x).le))
    (momentKernel_meas f (n + 1) z) (.of_forall fun x w hw => hbound w hw x)
    (A.integrable.norm.add B.integrable.norm) (.of_forall fun x w _ => ?_)).2
  have hd := (((hasDerivAt_id' w).mul_const (x : ℂ)).cexp).mul_const ((x : ℂ) ^ n * f.val x)
  convert hd using 1
  all_goals first | rfl | (simp only [momentKernel, pow_succ]; ring)

/-- All logarithmic moments of an exponential test have absolutely convergent
Mellin integrals at every complex point. -/
theorem integrable_mellin_test_moment (f : Tests) (n : ℕ) (z : ℂ) :
    Integrable (fun x : ℝ => Complex.exp (z * (x : ℂ)) * ((x : ℂ) ^ n * f.val x)) := by
  apply (momentTwist f n z.re).integrable.norm.mono' (momentKernel_meas f n z)
  exact .of_forall fun x => (momentKernel_norm f n z x).le

/-- Each complex derivative of the Mellin transform is the Mellin transform
of the corresponding logarithmic moment. -/
theorem mellin_iteratedDeriv_log_moment (f : Tests) (n : ℕ) :
    iteratedDeriv n (mellin fun t => f.val (Real.log t)) =
      mellin (fun t => (Real.log t : ℂ) ^ n * f.val (Real.log t)) := by
  have hi (k : ℕ) :
      mellin (fun t => (Real.log t : ℂ) ^ k * f.val (Real.log t)) =
        fun z => ∫ x, momentKernel f k z x := by
    funext z
    rw [mellin_eq_log_integral]
    simp only [momentKernel, Real.log_exp]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih, hi, hi]
    funext z
    exact (momentIntegral_hasDerivAt f n z).deriv


/-- Plancherel on a Mellin line, with the factor (2π) for unscaled height measure. -/
theorem mellin_iteratedDeriv_line_energy (f : Tests) (n : ℕ) (a : ℝ) :
    let trace := fun y : ℝ => iteratedDeriv n
      (mellin fun t => f.val (Real.log t)) (⟨a, y⟩ : ℂ)
    MemLp trace 2 volume ∧
      (∫ y, ‖trace y‖ ^ 2) = (2 * Real.pi) *
        ∫ x : ℝ, ‖f.val x‖ ^ 2 * (Real.exp (2 * a * x) * (x ^ 2) ^ n) := by
  let h := momentTwist f n a
  let H := 𝓕 h
  let c : ℝ := -(2 * Real.pi)⁻¹
  have hc : c ≠ 0 := neg_ne_zero.mpr (inv_ne_zero (by positivity))
  let u : ℝˣ := Units.mk0 c hc
  let T := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (ContinuousLinearEquiv.unitsEquivAut ℝ u) H
  have htrace (y : ℝ) :
      iteratedDeriv n (mellin fun t => f.val (Real.log t)) (⟨a, y⟩ : ℂ) = H (c * y) := by
    rw [mellin_iteratedDeriv_log_moment, mellin_eq_log_integral, SchwartzMap.fourier_coe, Real.fourier_eq']
    apply integral_congr_ae
    refine .of_forall fun x => ?_
    have hphase : (-2 : ℝ) * Real.pi * (x * (c * y)) = y * x := by
      dsimp [c]
      field_simp
    dsimp only
    change _ = _ • momentTwist f n a x
    have he : (⟨a, y⟩ : ℂ) * (x : ℂ) = ((y * x : ℝ) : ℂ) * Complex.I + (a * x : ℝ) := by
      apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
    rw [Real.log_exp, momentTwist_apply, Real.inner_apply, hphase, smul_eq_mul, he,
      Complex.exp_add, Complex.ofReal_exp, mul_assoc]
  dsimp only
  have hT (y : ℝ) : T y = H (c * y) := by
    rw [show T = _ from rfl, SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
      Function.comp_apply, ContinuousLinearEquiv.unitsEquivAut_apply]
    change H (y * c) = H (c * y)
    rw [mul_comm y c]
  refine ⟨(T.memLp 2 volume).ae_eq (.of_forall fun y => (hT y).trans (htrace y).symm), ?_⟩
  simp_rw [htrace]
  rw [Measure.integral_comp_mul_left (fun z : ℝ => ‖H z‖ ^ 2) c, smul_eq_mul,
    show |c⁻¹| = 2 * Real.pi by simp [c, abs_of_nonneg (show 0 ≤ 2 * Real.pi by positivity)],
    SchwartzMap.integral_norm_sq_fourier]
  congr 1
  apply integral_congr_ae
  refine .of_forall fun x => ?_
  change ‖momentTwist f n a x‖ ^ 2 = _
  exact momentTwist_norm_sq f n a x

def mellinLineEnergy (f : Tests) (n : ℕ) (a : ℝ) : ℝ :=
  ∫ y : ℝ, ‖iteratedDeriv n (mellin fun t => f.val (Real.log t)) (⟨a, y⟩ : ℂ)‖ ^ 2


/-- The square root of the line energy is the (L^2) seminorm in (9.2.2.5). -/
theorem sqrt_mellinLineEnergy (f : Tests) (k : ℕ) (a : ℝ) :
    Real.sqrt (mellinLineEnergy f k a) =
      lpNorm (fun y : ℝ => iteratedDeriv k
        (mellin fun t => f.val (Real.log t)) (⟨a, y⟩ : ℂ)) 2 volume := by
  rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num)
    (mellin_iteratedDeriv_line_energy f k a).1.aestronglyMeasurable, Real.sqrt_eq_rpow]
  norm_num [mellinLineEnergy, Real.rpow_natCast, inv_eq_one_div]

private def singleEndpointEnergy (f : Tests) (a : ℝ) (N : ℕ) : ℝ :=
  ∫ x : ℝ, ‖f.val x‖ ^ 2 * (Real.exp (2 * a * x) * (1 + x ^ 2) ^ N)

private theorem weightedMoment_integrable (f : Tests) (a : ℝ) (n : ℕ) :
    Integrable (fun x : ℝ => ‖f.val x‖ ^ 2 * (Real.exp (2 * a * x) * (x ^ 2) ^ n)) := by
  let h := momentTwist f n a
  have hi := (memLp_two_iff_integrable_sq_norm (h.memLp 2 volume).aestronglyMeasurable).mp
    (h.memLp 2 volume)
  apply hi.congr
  refine .of_forall fun x => ?_
  change ‖momentTwist f n a x‖ ^ 2 = _
  exact momentTwist_norm_sq f n a x

private theorem endpointEnergy_eq (f : Tests) (a : ℝ) (N : ℕ) :
    (2 * Real.pi) * singleEndpointEnergy f a N =
      ∑ k ∈ Finset.range (N + 1), (N.choose k : ℝ) * mellinLineEnergy f k a := by
  have hpow (x : ℝ) : (1 + x ^ 2) ^ N =
      ∑ k ∈ Finset.range (N + 1), (N.choose k : ℝ) * (x ^ 2) ^ k := by
    rw [add_comm, add_pow]
    simp only [one_pow, mul_one, mul_comm]
  unfold singleEndpointEnergy mellinLineEnergy
  simp_rw [(mellin_iteratedDeriv_line_energy f _ a).2]
  calc
    _ = (2 * Real.pi) * ∑ k ∈ Finset.range (N + 1), ∫ x : ℝ,
        (N.choose k : ℝ) * (‖f.val x‖ ^ 2 * (Real.exp (2 * a * x) * (x ^ 2) ^ k)) := by
      congr 1
      rw [← integral_finsetSum]
      · apply integral_congr_ae
        refine .of_forall fun x => ?_
        dsimp only
        rw [hpow, Finset.mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl (fun k _ => by ring)
      · intro k _
        exact (weightedMoment_integrable f a k).const_mul _
    _ = _ := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun k _ => by rw [integral_const_mul]; ring)

/-- The finite Mellin derivative traces give an equivalent norm on a compact
base interval. In squared norms the binomial-weighted sum is between one and
two times the original energy, after accounting for the Mellin normalization. -/
theorem hardySobolev_compact_mellin_energy_bounds (a b : ℝ) (hab : a ≤ b)
    (N : ℕ) (f : Tests) :
    let w := (hardySobolevIntervalENorm volume id (Icc a b) (2 * (N : ℝ)) f.val).toReal
    let E := ∑ k ∈ Finset.range (N + 1), (N.choose k : ℝ) *
      (mellinLineEnergy f k a + mellinLineEnergy f k b)
    (2 * Real.pi) * w ^ 2 ≤ E ∧ E ≤ (2 * Real.pi) * (2 * w ^ 2) := by
  let J := (univ : Set ℝ)
  let energy (x : ℝ) := ‖f.val x‖ ^ 2 * hardySobolevWeight a b (2 * (N : ℝ)) x
  let endpoint (d x : ℝ) := ‖f.val x‖ ^ 2 * (Real.exp (2 * d * x) * (1 + x ^ 2) ^ N)
  have h := stripSobolevTest_energy J ⟨a, mem_univ a⟩ ⟨b, mem_univ b⟩ hab
    (2 * (N : ℝ)) f
  have he : Integrable energy := h.1
  have hpos : ∀ x, 0 ≤ energy x := fun x => mul_nonneg (sq_nonneg _) (hardySobolevWeight_nonneg ..)
  have hd' (d : ℝ) := (stripSobolevTest_energy J ⟨d, mem_univ d⟩ ⟨d, mem_univ d⟩ le_rfl
    (2 * (N : ℝ)) f).1
  have hweight (p q x : ℝ) : hardySobolevWeight p q (2 * (N : ℝ)) x =
      max (Real.exp (2 * p * x)) (Real.exp (2 * q * x)) * (1 + x ^ 2) ^ N := by
    unfold hardySobolevWeight
    rw [mul_div_cancel_left₀ _ two_ne_zero, Real.rpow_natCast]
  have hd (d : ℝ) : Integrable (endpoint d) := by
    simpa only [hweight, max_self, endpoint] using hd' d
  have hlo (x : ℝ) : energy x ≤ endpoint a x + endpoint b x := by
    simp only [energy, endpoint, hweight, ← mul_add, ← add_mul]
    gcongr
    exact max_le (le_add_of_nonneg_right (Real.exp_pos _).le)
      (le_add_of_nonneg_left (Real.exp_pos _).le)
  have hhi (x : ℝ) : endpoint a x + endpoint b x ≤ 2 * energy x := by
    have hd_le (d : ℝ) (hle : Real.exp (2 * d * x) ≤
        max (Real.exp (2 * a * x)) (Real.exp (2 * b * x))) : endpoint d x ≤ energy x := by
      simp only [energy, endpoint, hweight]
      gcongr
    rw [two_mul]
    exact add_le_add (hd_le a (le_max_left _ _)) (hd_le b (le_max_right _ _))
  dsimp only
  rw [h.2, ENNReal.toReal_ofReal (Real.sqrt_nonneg _),
    Real.sq_sqrt (integral_nonneg hpos)]
  have hE : ∑ k ∈ Finset.range (N + 1), (N.choose k : ℝ) *
      (mellinLineEnergy f k a + mellinLineEnergy f k b) =
        (2 * Real.pi) * ∫ x, endpoint a x + endpoint b x := by
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib, ← endpointEnergy_eq, ← endpointEnergy_eq,
      ← mul_add, integral_add (hd a) (hd b)]
    rfl
  rw [hE]
  refine ⟨mul_le_mul_of_nonneg_left (integral_mono he ((hd a).add (hd b)) hlo) (by positivity),
    mul_le_mul_of_nonneg_left ?_ (by positivity)⟩
  rw [← integral_const_mul]
  exact integral_mono ((hd a).add (hd b)) (he.const_mul _) hhi


theorem mellinLineEnergy_nonneg (f : Tests) (k : ℕ) (σ : ℝ) :
    0 ≤ mellinLineEnergy f k σ := integral_nonneg fun _ => sq_nonneg _

/-- At a single abscissa, the weighted square norm is exactly the
binomial-weighted sum of Mellin derivative energies divided by (2π). -/
theorem hardySobolev_singleton_mellin_energy (a : ℝ) (N : ℕ) (f : Tests) :
    (2 * Real.pi) *
      (eLpNorm f.val 2 (hardySobolevMeasure volume id a a (2 * (N : ℝ)))).toReal ^ 2 =
        ∑ k ∈ Finset.range (N + 1), (N.choose k : ℝ) * mellinLineEnergy f k a := by
  have h := (stripSobolevTest_energy univ ⟨a, mem_univ a⟩ ⟨a, mem_univ a⟩ le_rfl
    (2 * (N : ℝ)) f).2
  rw [hardySobolevIntervalENorm_Icc _ _ le_rfl] at h
  change eLpNorm f.val 2 (hardySobolevMeasure volume id a a (2 * (N : ℝ))) = _ at h
  have hn : ∀ x : ℝ, 0 ≤ ‖f.val x‖ ^ 2 * hardySobolevWeight a a (2 * (N : ℝ)) x :=
    fun x => mul_nonneg (sq_nonneg _) (hardySobolevWeight_nonneg ..)
  rw [h, ENNReal.toReal_ofReal (Real.sqrt_nonneg _), Real.sq_sqrt (integral_nonneg hn),
    ← endpointEnergy_eq]
  have hN : 2 * (N : ℝ) / 2 = (N : ℝ) := by ring
  simp only [singleEndpointEnergy, hardySobolevWeight, max_self, hN, Real.rpow_natCast]

/-- Every individual line energy is bounded by the squared interval norm.
This applies to any finite-norm test, including the corrected half-line domains. -/
theorem mellinLineEnergy_le_interval (I : Set ℝ) {a : ℝ} (ha : a ∈ I) (N k : ℕ) (hk : k ≤ N)
    (f : Tests) (hfin : hardySobolevIntervalENorm volume id I (2 * (N : ℝ)) f.val ≠ (∞ : ℝ≥0∞)) :
    mellinLineEnergy f k a ≤ (2 * Real.pi) *
      (hardySobolevIntervalENorm volume id I (2 * (N : ℝ)) f.val).toReal ^ 2 := by
  have hcast : (1 : ℝ) ≤ (N.choose k : ℝ) := by exact_mod_cast Nat.choose_pos hk
  have hsum : mellinLineEnergy f k a ≤
      ∑ j ∈ Finset.range (N + 1), (N.choose j : ℝ) * mellinLineEnergy f j a := by
    calc
      _ ≤ (N.choose k : ℝ) * mellinLineEnergy f k a :=
        le_mul_of_one_le_left (mellinLineEnergy_nonneg f k a) hcast
      _ ≤ _ := Finset.single_le_sum
        (fun j _ => mul_nonneg (Nat.cast_nonneg _) (mellinLineEnergy_nonneg f j a))
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))
  rw [← hardySobolev_singleton_mellin_energy a N f] at hsum
  have hw := ENNReal.toReal_mono hfin
    (le_iSup₂_of_le (⟨a, ha⟩ : I) (⟨a, ha⟩ : I) le_rfl)
  exact hsum.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ ENNReal.toReal_nonneg hw 2) (by positivity))


/-- Finite endpoint control and the individual trace bounds compare the norm
topologies. The statement uses arbitrary filters and thus applies to the
topologies generated by the corresponding seminorms, applied to differences. -/
theorem hardySobolev_finite_traces_tendsto_iff {ι : Type*} {l : Filter ι}
    {I A : Set ℝ} (hAI : A ⊆ I) {a b : ℝ} (ha : a ∈ A) (hb : b ∈ A)
    (N : ℕ) (f : ι → Tests)
    (hfin : ∀ i, hardySobolevIntervalENorm volume id I (2 * (N : ℝ)) (f i).val ≠ (∞ : ℝ≥0∞))
    (hlow : ∀ i,
      (2 * Real.pi) *
        (hardySobolevIntervalENorm volume id I (2 * (N : ℝ)) (f i).val).toReal ^ 2 ≤
        ∑ k ∈ Finset.range (N + 1), (N.choose k : ℝ) *
          (mellinLineEnergy (f i) k a + mellinLineEnergy (f i) k b)) :
    Tendsto (fun i =>
        (hardySobolevIntervalENorm volume id I (2 * (N : ℝ)) (f i).val).toReal) l (𝓝 0) ↔
      ∀ σ ∈ A, ∀ k ≤ N, Tendsto (fun i => mellinLineEnergy (f i) k σ) l (𝓝 0) := by
  let w (i : ι) := (hardySobolevIntervalENorm volume id I (2 * (N : ℝ)) (f i).val).toReal
  have hp : 0 < 2 * Real.pi := by positivity
  constructor
  · intro hw σ hσ k hk
    have hg : Tendsto (fun i => (2 * Real.pi) * w i ^ 2) l (𝓝 0) := by
      simpa using ((show Tendsto w l (𝓝 0) from hw).pow 2).const_mul (2 * Real.pi)
    exact squeeze_zero (fun i => mellinLineEnergy_nonneg (f i) k σ)
      (fun i => mellinLineEnergy_le_interval I (hAI hσ) N k hk (f i) (hfin i)) hg
  · intro h
    let E (i : ι) := ∑ k ∈ Finset.range (N + 1), (N.choose k : ℝ) *
      (mellinLineEnergy (f i) k a + mellinLineEnergy (f i) k b)
    have hE : Tendsto E l (𝓝 0) := by
      have hs := tendsto_finsetSum (Finset.range (N + 1))
        (fun k hk => show Tendsto (fun i => (N.choose k : ℝ) *
          (mellinLineEnergy (f i) k a + mellinLineEnergy (f i) k b)) l (𝓝 0) from by
            have hkn : k ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
            simpa using ((h a ha k hkn).add (h b hb k hkn)).const_mul (N.choose k : ℝ))
      simpa [E] using hs
    have hs : Tendsto (fun i => Real.sqrt (E i / (2 * Real.pi))) l (𝓝 0) := by
      simpa using (hE.div_const (2 * Real.pi)).sqrt
    have hle (i : ι) : w i ≤ Real.sqrt (E i / (2 * Real.pi)) := by
      have hEi : 0 ≤ E i := Finset.sum_nonneg fun k _ => mul_nonneg (Nat.cast_nonneg _)
        (add_nonneg (mellinLineEnergy_nonneg (f i) k a) (mellinLineEnergy_nonneg (f i) k b))
      refine (Real.le_sqrt ENNReal.toReal_nonneg (div_nonneg hEi hp.le)).mpr ?_
      apply (le_div_iff₀ hp).mpr
      rw [mul_comm]
      exact hlow i
    exact squeeze_zero (fun _ => ENNReal.toReal_nonneg) hle hs

end
end Masullo
