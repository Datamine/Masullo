/-
Adapted from the Apache-2.0 RiemannMasullo project, commits
ab046ba2e3e749917950400be35190897b6f20f7 and
1a3eb015d521c4bcbaf366e2d4c8046c7797878f. See External/PROVENANCE.md.
-/
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Bounds for the gamma function on vertical strips
-/

open Filter Function MeasureTheory Set
open scoped Asymptotics Topology ComplexConjugate

namespace Masullo

private theorem gamma_recurrence_product (g : ℂ → ℂ) (δ : ℝ)
    (hstep : ∀ z : ℂ, z ≠ 0 → g (z + (δ : ℂ)) = g z * (z / (2 * (Real.pi : ℂ))))
    (z : ℂ) (n : ℕ) (hz : ∀ j : ℕ, j < n → z + (j : ℂ) * (δ : ℂ) ≠ 0) :
    g (z + (n : ℂ) * (δ : ℂ)) =
      g z * ∏ j ∈ Finset.range n, (z + (j : ℂ) * (δ : ℂ)) / (2 * (Real.pi : ℂ)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ, add_mul, one_mul, ← add_assoc, hstep _ (hz n (Nat.lt_succ_self n)),
      ih (fun j hj ↦ hz j (Nat.lt_trans hj (Nat.lt_succ_self n))),
      Finset.prod_range_succ, mul_assoc]

private theorem gamma_recurrence_norm_ratio (g : ℂ → ℂ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hstep : ∀ z : ℂ, z ≠ 0 → g (z + (δ : ℂ)) = g z * (z / (2 * (Real.pi : ℂ))))
    (hconj : ∀ z : ℂ, ‖g (conj z)‖ = ‖g z‖)
    (z : ℂ) (hgz : g z ≠ 0) (n : ℕ)
    (hz : ∀ j : ℕ, j < n → conj z + (j : ℂ) * (δ : ℂ) ≠ 0) :
    ‖g (conj z + (n : ℂ) * (δ : ℂ)) * (g z)⁻¹‖ ≤
      ((‖z‖ + (n : ℝ) * δ) / (2 * Real.pi)) ^ n := by
  rw [gamma_recurrence_product g δ hstep (conj z) n hz, norm_mul, norm_mul, hconj, norm_inv]
  rw [mul_right_comm, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hgz), one_mul, norm_prod]
  rw [show ((‖z‖ + (n : ℝ) * δ) / (2 * Real.pi)) ^ n =
    ∏ _ ∈ Finset.range n, (‖z‖ + (n : ℝ) * δ) / (2 * Real.pi) by
      simp only [Finset.prod_const, Finset.card_range]]
  apply Finset.prod_le_prod (fun _ _ ↦ norm_nonneg _)
  intro j hj
  rw [norm_div, norm_mul, Complex.norm_ofNat, Complex.norm_of_nonneg Real.pi_pos.le]
  apply div_le_div_of_nonneg_right _ (by positivity)
  calc
    _ ≤ ‖conj z‖ + ‖(j : ℂ) * (δ : ℂ)‖ := norm_add_le _ _
    _ = ‖z‖ + (j : ℝ) * δ := by
      simp only [Complex.norm_conj, norm_mul, Complex.norm_natCast, Complex.norm_of_nonneg hδ]
    _ ≤ _ := by
      gcongr
      exact_mod_cast (Finset.mem_range.mp hj).le

theorem gammaReal_norm_conj (z : ℂ) : ‖Complex.Gammaℝ (conj z)‖ = ‖Complex.Gammaℝ z‖ := by
  simp only [Complex.Gammaℝ_def, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
  have h (w : ℂ) : conj w / 2 = conj (w / 2) := by
    rw [map_div₀, map_ofNat]
  rw [h, Complex.Gamma_conj, Complex.norm_conj]
  congr 1
  simp [Complex.div_ofNat_re]

theorem gammaComplex_norm_conj (z : ℂ) :
    ‖Complex.Gammaℂ (conj z)‖ = ‖Complex.Gammaℂ z‖ := by
  have h : 0 < 2 * Real.pi := by positivity
  have he (w : ℂ) : ‖(2 * (Real.pi : ℂ)) ^ w‖ = (2 * Real.pi) ^ w.re := by
    rw [← Complex.ofReal_ofNat, ← Complex.ofReal_mul, Complex.norm_cpow_eq_rpow_re_of_pos h]
  simp only [Complex.Gammaℂ_def, norm_mul, Complex.norm_ofNat, Complex.Gamma_conj,
    Complex.norm_conj, he, Complex.neg_re, Complex.conj_re]

/-- The reflected real Gamma ratio is bounded by the recurrence polynomial
at every argument. At a pole the totalized reciprocal factor is zero. -/
theorem norm_gammaReal_reflected_steps_all (z : ℂ) (n : ℕ) :
    ‖Complex.Gammaℝ (conj z + (n : ℂ) * 2) * (Complex.Gammaℝ z)⁻¹‖ ≤
      ((‖z‖ + (n : ℝ) * 2) / (2 * Real.pi)) ^ n := by
  by_cases hgz : Complex.Gammaℝ z = 0
  · simp only [hgz, inv_zero, mul_zero, norm_zero]
    positivity
  have hstep (w : ℂ) (hw : w ≠ 0) :
      Complex.Gammaℝ (w + (2 : ℝ)) = Complex.Gammaℝ w * (w / (2 * (Real.pi : ℂ))) := by
    rw [Complex.ofReal_ofNat, Complex.Gammaℝ_add_two hw]
    ring
  apply gamma_recurrence_norm_ratio _ 2 (by norm_num) hstep gammaReal_norm_conj z hgz n
  intro j _ hj
  apply hgz
  refine Complex.Gammaℝ_eq_zero_iff.mpr ⟨j, ?_⟩
  have hj' := congrArg (conj : ℂ → ℂ) (eq_neg_of_add_eq_zero_left hj)
  have htwo : conj (2 : ℂ) = 2 := map_ofNat _ _
  simpa [htwo, mul_comm] using hj'

/-- The reflected complex Gamma ratio is bounded uniformly in the same
way, including real arguments. -/
theorem norm_gammaComplex_reflected_steps_all (z : ℂ) (n : ℕ) :
    ‖Complex.Gammaℂ (conj z + (n : ℂ)) * (Complex.Gammaℂ z)⁻¹‖ ≤
      ((‖z‖ + (n : ℝ)) / (2 * Real.pi)) ^ n := by
  by_cases hgz : Complex.Gammaℂ z = 0
  · simp only [hgz, inv_zero, mul_zero, norm_zero]
    positivity
  have hstep (w : ℂ) (hw : w ≠ 0) :
      Complex.Gammaℂ (w + (1 : ℝ)) = Complex.Gammaℂ w * (w / (2 * (Real.pi : ℂ))) := by
    rw [Complex.ofReal_one, Complex.Gammaℂ_add_one hw]
    ring
  have hz (j : ℕ) (_ : j < n) : conj z + (j : ℂ) * (1 : ℝ) ≠ 0 := by
    intro hj
    apply hgz
    have h : z = -(j : ℂ) := by
      have hj' := congrArg (conj : ℂ → ℂ) (eq_neg_of_add_eq_zero_left hj)
      simpa using hj'
    rw [Complex.Gammaℂ_def, h, Complex.Gamma_neg_nat_eq_zero, mul_zero]
  simpa only [Complex.ofReal_one, mul_one] using
    gamma_recurrence_norm_ratio _ 1 zero_le_one hstep gammaComplex_norm_conj z hgz n hz

/-- Reflection followed by a nonnegative number of real Gamma recurrence
steps has a polynomial bound, with no Stirling estimate. -/
theorem norm_gammaReal_reflected_steps (z : ℂ) (_hz : z.im ≠ 0)
    (_hgz : Complex.Gammaℝ z ≠ 0) (n : ℕ) :
    ‖Complex.Gammaℝ (conj z + (n : ℂ) * 2) * (Complex.Gammaℝ z)⁻¹‖ ≤
      ((‖z‖ + (n : ℝ) * 2) / (2 * Real.pi)) ^ n :=
  norm_gammaReal_reflected_steps_all z n

/-- Reflection followed by a nonnegative number of complex Gamma recurrence
steps has the corresponding polynomial bound. -/
theorem norm_gammaComplex_reflected_steps (z : ℂ) (_hz : z.im ≠ 0)
    (_hgz : Complex.Gammaℂ z ≠ 0) (n : ℕ) :
    ‖Complex.Gammaℂ (conj z + (n : ℂ)) * (Complex.Gammaℂ z)⁻¹‖ ≤
      ((‖z‖ + (n : ℝ)) / (2 * Real.pi)) ^ n :=
  norm_gammaComplex_reflected_steps_all z n

local notation "atHeight" => comap (abs ∘ Complex.im) atTop

/-- On the right half-plane the norm of Euler's gamma integral is bounded by
the gamma integral at the real part. -/
theorem norm_Gamma_le_real_Gamma {z : ℂ} (hz : 0 < z.re) :
    ‖Complex.Gamma z‖ ≤ Real.Gamma z.re := by
  rw [Complex.Gamma_eq_integral hz, Real.Gamma_eq_integral hz, Complex.GammaIntegral]
  refine (norm_integral_le_integral_norm _).trans_eq (integral_congr_ae ?_)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
    Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.sub_re, Complex.one_re]

/-- A real Gamma factor is bounded on every fixed closed strip of
positive real parts. -/
theorem exists_norm_GammaReal_le_on_strip {a b : ℝ} (ha : 0 < a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, z.re ∈ Icc a b → ‖Complex.Gammaℝ z‖ ≤ C := by
  have hc : ContinuousOn (fun x : ℝ ↦ Real.Gamma (x / 2)) (Icc a b) :=
    Real.differentiableOn_Gamma_Ioi.continuousOn.comp (by fun_prop) fun x hx ↦
      half_pos (ha.trans_le hx.1)
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  refine ⟨max C 0, le_max_right _ _, fun z hz ↦ ?_⟩
  have hz₀ : 0 < z.re := ha.trans_le hz.1
  have hPi : ‖(Real.pi : ℂ) ^ (-z / 2)‖ ≤ 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    apply Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.pi_gt_three])
    simp only [Complex.div_ofNat_re, Complex.neg_re]
    linarith
  have hGamma : ‖Complex.Gamma (z / 2)‖ ≤ max C 0 := by
    have h := norm_Gamma_le_real_Gamma (z := z / 2) (by simpa using hz₀)
    rw [Complex.div_ofNat_re] at h
    exact h.trans ((le_abs_self _).trans ((hC z.re hz).trans (le_max_left _ _)))
  rw [Complex.Gammaℝ_def, norm_mul]
  simpa only [one_mul] using mul_le_mul hPi hGamma (norm_nonneg _) zero_le_one

/-- The analogous bound at a complex place follows by duplication. -/
theorem exists_norm_GammaComplex_le_on_strip {a b : ℝ} (ha : 0 < a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, z.re ∈ Icc a b → ‖Complex.Gammaℂ z‖ ≤ C := by
  obtain ⟨A, hA, h₁⟩ := exists_norm_GammaReal_le_on_strip (b := b) ha
  obtain ⟨B, hB, h₂⟩ := exists_norm_GammaReal_le_on_strip (b := b + 1) ha
  refine ⟨A * B, mul_nonneg hA hB, fun z hz ↦ ?_⟩
  rw [← Complex.Gammaℝ_mul_Gammaℝ_add_one, norm_mul]
  exact mul_le_mul (h₁ _ hz) (h₂ _ (by
    rw [Complex.add_re, Complex.one_re]
    exact ⟨by linarith [hz.1], by linarith [hz.2]⟩)) (norm_nonneg _) hA

/-- On any fixed strip, the reciprocal gamma function is bounded by a constant
times `exp (π * |im z|)` at absolute heights at least one. -/
theorem exists_norm_inv_Gamma_le_exp_mul_abs_im (a b : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, z.re ∈ Icc a b → 1 ≤ |z.im| →
      ‖(Complex.Gamma z)⁻¹‖ ≤ C * Real.exp (Real.pi * |z.im|) := by
  obtain ⟨n, hn⟩ := exists_nat_gt b
  have hCont : ContinuousOn Real.Gamma (Icc (1 - b + n) (1 - a + n)) :=
    Real.differentiableOn_Gamma_Ioi.continuousOn.mono fun x hx ↦
      show 0 < x from lt_of_lt_of_le (by linarith) hx.1
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hCont
  refine ⟨max M 0 / Real.pi, by positivity, fun z hz ht ↦ ?_⟩
  have hShift (w : ℂ) (hw : 1 ≤ |w.im|) (k : ℕ) :
      ‖Complex.Gamma w‖ ≤ ‖Complex.Gamma (w + k)‖ := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Nat.cast_succ, ← add_assoc]
      have hnorm : 1 ≤ ‖w + k‖ :=
        (show 1 ≤ |(w + k).im| by simpa using hw).trans (Complex.abs_im_le_norm _)
      have hne : w + k ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt (zero_lt_one.trans_le hnorm))
      apply ih.trans
      rw [Complex.Gamma_add_one _ hne, norm_mul]
      exact le_mul_of_one_le_left (norm_nonneg _) hnorm
  have hRe : (1 - z + (n : ℂ)).re ∈ Icc (1 - b + n) (1 - a + n) := by
    simp only [Complex.add_re, Complex.sub_re, Complex.one_re, Complex.natCast_re, mem_Icc]
    exact ⟨by linarith [hz.2], by linarith [hz.1]⟩
  have hGamma : ‖Complex.Gamma (1 - z)‖ ≤ max M 0 := by
    refine (hShift (1 - z) (by simpa using ht) n).trans ?_
    refine (norm_Gamma_le_real_Gamma (lt_of_lt_of_le (by linarith) hRe.1)).trans ?_
    exact (le_abs_self _).trans ((hM _ hRe).trans (le_max_left _ _))
  have hSin (w : ℂ) : ‖Complex.sin w‖ ≤ Real.exp |w.im| := by
    have h := norm_sub_le (Complex.exp (-w * Complex.I)) (Complex.exp (w * Complex.I))
    have he := congrArg (fun z : ℂ ↦ ‖z‖) (Complex.two_sin w)
    simp only [norm_mul, Complex.norm_I, mul_one] at he
    norm_num [Complex.norm_exp, Complex.mul_re] at he h
    have h₁ := Real.exp_le_exp.mpr (le_abs_self w.im)
    have h₂ := Real.exp_le_exp.mpr (neg_le_abs w.im)
    linarith
  have him : z.im ≠ 0 := by
    intro he
    norm_num [he] at ht
  have hGne : Complex.Gamma z ≠ 0 := Complex.Gamma_ne_zero fun k he ↦ him (by
    rw [he]
    simp)
  have hSne : Complex.sin ((Real.pi : ℂ) * z) ≠ 0 := by
    rw [Complex.sin_ne_zero_iff]
    intro k he
    have him' := congrArg Complex.im he
    have hprod : Real.pi * z.im = 0 := by
      simpa only [Complex.im_ofReal_mul, ← Complex.ofReal_intCast, ← Complex.ofReal_mul,
        Complex.ofReal_im] using him'
    exact (mul_ne_zero Real.pi_ne_zero him) hprod
  have hReflect : (Complex.Gamma z)⁻¹ =
      Complex.Gamma (1 - z) * Complex.sin ((Real.pi : ℂ) * z) / (Real.pi : ℂ) := by
    apply (eq_div_iff (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)).2
    calc
      _ = (Complex.Gamma z)⁻¹ * ((Complex.Gamma z * Complex.Gamma (1 - z)) *
          Complex.sin ((Real.pi : ℂ) * z)) := by
        rw [Complex.Gamma_mul_Gamma_one_sub, div_mul_cancel₀ _ hSne]
      _ = _ := by rw [← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hGne, one_mul]
  rw [hReflect, norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le,
    div_mul_eq_mul_div]
  apply div_le_div_of_nonneg_right _ Real.pi_pos.le
  refine mul_le_mul hGamma ?_ (norm_nonneg _) (le_max_right _ _)
  simpa only [Complex.im_ofReal_mul, abs_mul, abs_of_pos Real.pi_pos] using
    hSin ((Real.pi : ℂ) * z)

/-- Shifting a real archimedean gamma factor contributes a constant to its reciprocal
exponential bound on a fixed strip. -/
theorem inv_Gammaℝ_add_isBigO_exp (a b : ℝ) (w : ℂ) :
    (fun s : ℂ ↦ (Complex.Gammaℝ (s + w))⁻¹) =O[atHeight ⊓ 𝓟 (Complex.re ⁻¹' Icc a b)]
      fun s ↦ Real.exp ((Real.pi / 2) * |s.im|) := by
  let A := (a + w.re) / 2
  let B := (b + w.re) / 2
  obtain ⟨C, hC, hΓ⟩ := exists_norm_inv_Gamma_le_exp_mul_abs_im A B
  have hPow : Continuous (fun x : ℝ => Real.pi ^ x) := by
    simp only [Real.rpow_def_of_pos Real.pi_pos]
    fun_prop
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := A) (b := B)).exists_bound_of_continuousOn hPow.continuousOn
  have hHeight : Tendsto (fun s : ℂ ↦ |s.im|) (atHeight ⊓ 𝓟 (Complex.re ⁻¹' Icc a b)) atTop :=
    tendsto_inf_left tendsto_comap
  have hStrip : ∀ᶠ s : ℂ in atHeight ⊓ 𝓟 (Complex.re ⁻¹' Icc a b), s.re ∈ Icc a b :=
    eventually_inf_principal.mpr (Eventually.of_forall fun _ hs ↦ hs)
  refine Asymptotics.IsBigO.of_bound (max M 0 * C * Real.exp ((Real.pi / 2) * |w.im|)) ?_
  filter_upwards [hStrip, hHeight.eventually_ge_atTop (2 + |w.im|)] with s hs ht
  let z := (s + w) / 2
  have hz : z.re ∈ Icc A B := by
    simp only [z, A, B, Complex.div_ofNat_re, Complex.add_re, mem_Icc]
    exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hiz : |z.im| = |s.im + w.im| / 2 := by
    simp [z, Complex.div_ofNat_im, abs_div]
  have hzLower : 1 ≤ |z.im| := by
    rw [hiz]
    have hTriangle := abs_sub_abs_le_abs_sub s.im (-w.im)
    rw [abs_neg, sub_neg_eq_add] at hTriangle
    linarith
  have hzUpper : |z.im| ≤ (|s.im| + |w.im|) / 2 := by
    rw [hiz]
    exact div_le_div_of_nonneg_right (abs_add_le _ _) (by norm_num)
  rw [Complex.Gammaℝ_def, mul_inv_rev, neg_div, ← Complex.cpow_neg,
    neg_neg, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos,
    Real.norm_of_nonneg (Real.exp_pos _).le]
  change ‖(Complex.Gamma z)⁻¹‖ * Real.pi ^ z.re ≤ _
  calc
    _ ≤ (C * Real.exp (Real.pi * |z.im|)) * max M 0 :=
      mul_le_mul (hΓ z hz hzLower) ((le_abs_self _).trans ((hM _ hz).trans (le_max_left _ _)))
        (Real.rpow_nonneg Real.pi_pos.le _) (by positivity)
    _ ≤ (C * Real.exp ((Real.pi / 2) * (|s.im| + |w.im|))) * max M 0 := by
      refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC)
        (le_max_right _ _)
      linarith [mul_le_mul_of_nonneg_left hzUpper Real.pi_pos.le]
    _ = _ := by rw [mul_add, Real.exp_add]; ring

/- Adapted from RiemannMasullo commit 6e43723 (Apache-2.0). -/

/-- Reflection bounds the reciprocal of gamma on the central line with
exponential rate π/2. -/
private theorem norm_inv_Gamma_half (w : ℂ) (hw : w.re = 1 / 2) :
    ‖(Complex.Gamma w)⁻¹‖ ≤ Real.exp (Real.pi * |w.im| / 2) := by
  have hc : 1 - w = conj w := by
    apply Complex.ext <;> simp [hw]
    ring
  have he := congrArg (fun t : ℂ ↦ ‖t⁻¹‖) (Complex.Gamma_mul_Gamma_one_sub w)
  simp only [hc, Complex.Gamma_conj, inv_div, norm_div, norm_inv, norm_mul, Complex.norm_conj,
    Complex.norm_of_nonneg Real.pi_pos.le, mul_inv] at he
  have hSin (z : ℂ) : ‖Complex.sin z‖ ≤ Real.exp |z.im| := by
    have h := norm_sub_le (Complex.exp (-z * Complex.I)) (Complex.exp (z * Complex.I))
    have he := congrArg (fun a : ℂ ↦ ‖a‖) (Complex.two_sin z)
    simp only [norm_mul, Complex.norm_I, mul_one] at he
    norm_num [Complex.norm_exp, Complex.mul_re] at he h
    linarith [Real.exp_le_exp.mpr (le_abs_self z.im), Real.exp_le_exp.mpr (neg_le_abs z.im)]
  have h := (div_le_self (norm_nonneg (Complex.sin (Real.pi * w)))
    (by linarith [Real.pi_gt_three] : 1 ≤ Real.pi)).trans (hSin ((Real.pi : ℂ) * w))
  rw [← he, Complex.im_ofReal_mul, abs_mul, abs_of_pos Real.pi_pos] at h
  have he₂ : Real.exp (Real.pi * |w.im|) = Real.exp (Real.pi * |w.im| / 2) ^ 2 := by
    rw [sq, ← Real.exp_add, add_halves]
  rw [he₂] at h
  rw [norm_inv]
  nlinarith [Real.exp_pos (Real.pi * |w.im| / 2)]

/-- In the positive half-plane a Beta integral compares gamma at height t
to gamma at the same height on the central line. -/
theorem exists_norm_inv_Gamma_le_half_exp_on_strip (a b : ℝ) (ha : 0 < a) :
    ∃ C > 0, ∀ z : ℂ, z.re ∈ Icc a b →
      ‖(Complex.Gamma z)⁻¹‖ ≤ C * (1 + |z.im|) * Real.exp (Real.pi * |z.im| / 2) := by
  let k (u v : ℂ) (x : ℝ) := (x : ℂ) ^ (u - 1) * (1 - (x : ℂ)) ^ (v - 1)
  let B := ∫ x : ℝ in 0..1, ‖k (1/2) (1/2) x‖
  have hs : ContinuousOn (fun t : ℝ ↦ (Real.Gamma t)⁻¹) (Icc (a + 1/2) (b + 1/2)) := by
    have hdom : Icc (a + 1/2) (b + 1/2) ⊆ Ioi (0 : ℝ) := fun x hx ↦ by
      change 0 < x; linarith [hx.1]
    exact (Real.differentiableOn_Gamma_Ioi.continuousOn.mono hdom).inv₀ fun x hx ↦
      (Real.Gamma_pos_of_pos (hdom hx)).ne'
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hs
  let C := (1 + |b|) * (1 + |B|) * (1 + |M|)
  refine ⟨C, by dsimp [C]; positivity, fun z hz ↦ ?_⟩
  let w : ℂ := ⟨1/2, z.im⟩
  let v := z.re + 1/2
  have hw : w.re = 1/2 := rfl
  have hv : 0 < v := by dsimp [v]; linarith [hz.1]
  have hsum : w + (v : ℂ) = z + 1 := by
    apply Complex.ext <;> simp [w, v]
    ring
  have hβ : ‖Complex.betaIntegral w (v : ℂ)‖ ≤ B := by
    apply (intervalIntegral.norm_integral_le_integral_norm zero_le_one).trans
    apply intervalIntegral.integral_mono_on_of_le_Ioo zero_le_one
      (Complex.betaIntegral_convergent (by change (0 : ℝ) < 1/2; norm_num) hv).norm
      (Complex.betaIntegral_convergent (u := (1/2 : ℂ)) (v := (1/2 : ℂ)) (by norm_num) (by norm_num)).norm
    intro x hx
    have hy : 0 < 1 - x := sub_pos.mpr hx.2
    simp only [norm_mul, ← Complex.ofReal_one, ← Complex.ofReal_sub,
      Complex.norm_cpow_eq_rpow_re_of_pos hx.1, Complex.norm_cpow_eq_rpow_re_of_pos hy]
    apply mul_le_mul _ _ (Real.rpow_nonneg hy.le _) (Real.rpow_nonneg hx.1.le _)
    · simp [hw]
    · apply Real.rpow_le_rpow_of_exponent_ge hy (by linarith [hx.1])
      simp [v]; linarith [hz.1]
  have he := Complex.Gamma_mul_Gamma_eq_betaIntegral (s := w) (t := (v : ℂ))
    (show 0 < w.re by rw [hw]; norm_num) hv
  rw [hsum, Complex.Gamma_add_one z (show z ≠ 0 from fun h ↦ by
    have h₀ := ha.trans_le hz.1; simp [h] at h₀)] at he
  have hwG : Complex.Gamma w ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by rw [hw]; norm_num)
  have hzG : Complex.Gamma z ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (ha.trans_le hz.1)
  have hvG : Complex.Gamma (v : ℂ) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hv
  have hquot : (Complex.Gamma z)⁻¹ =
      z * Complex.betaIntegral w v * (Complex.Gamma (v : ℂ))⁻¹ * (Complex.Gamma w)⁻¹ := by
    field_simp [hwG, hzG, hvG]
    linear_combination he
  have hzN : ‖z‖ ≤ (1 + |b|) * (1 + |z.im|) := by
    refine (Complex.norm_le_abs_re_add_abs_im z).trans ?_
    rw [abs_of_pos (ha.trans_le hz.1)]
    nlinarith [hz.2, le_abs_self b, abs_nonneg z.im, mul_nonneg (abs_nonneg b) (abs_nonneg z.im)]
  have hvM : ‖(Complex.Gamma (v : ℂ))⁻¹‖ ≤ 1 + |M| := by
    rw [Complex.Gamma_ofReal, ← Complex.ofReal_inv, Complex.norm_real]
    exact (hM v ⟨by dsimp [v]; linarith [hz.1], by dsimp [v]; linarith [hz.2]⟩).trans
      (by linarith [le_abs_self M])
  rw [hquot, norm_mul, norm_mul, norm_mul]
  calc
    _ ≤ ((1 + |b|) * (1 + |z.im|)) * (1 + |B|) * (1 + |M|) * Real.exp (Real.pi * |z.im| / 2) := by
      gcongr
      · exact hβ.trans (by linarith [le_abs_self B])
      · exact norm_inv_Gamma_half w hw
    _ = _ := by dsimp [C]; ring

/-- A fixed complex shift of the real archimedean factor costs a constant
on a positive strip. The exponential rate is π/4 in the original height. -/
theorem exists_norm_inv_GammaReal_add_le_on_strip (a b : ℝ) (ha : 0 < a) (w : ℂ) (hw : 0 ≤ w.re) :
    ∃ C > 0, ∀ s : ℂ, s.re ∈ Icc a b →
      ‖(Complex.Gammaℝ (s + w))⁻¹‖ ≤ C * ((1 + |s.im|) * Real.exp (Real.pi * |s.im| / 4)) := by
  let A := (a + w.re) / 2
  let B := (b + w.re) / 2
  obtain ⟨C, hC, hΓ⟩ := exists_norm_inv_Gamma_le_half_exp_on_strip A B
    (by dsimp [A]; linarith)
  let P := Real.pi ^ B
  refine ⟨C * (1 + |w.im|) * Real.exp (Real.pi * |w.im| / 4) * P, by dsimp [P]; positivity,
    fun s hs ↦ ?_⟩
  let z := (s + w) / 2
  have hz : z.re ∈ Icc A B := by
    simp only [z, A, B, Complex.div_ofNat_re, Complex.add_re]
    exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have him : |z.im| ≤ (|s.im| + |w.im|) / 2 := by
    simp only [z, Complex.div_ofNat_im, Complex.add_im, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact div_le_div_of_nonneg_right (abs_add_le _ _) (by norm_num)
  have hpoly : 1 + |z.im| ≤ (1 + |w.im|) * (1 + |s.im|) := by
    nlinarith [abs_nonneg w.im, abs_nonneg s.im, mul_nonneg (abs_nonneg w.im) (abs_nonneg s.im)]
  have hexp : Real.exp (Real.pi * |z.im| / 2) ≤
      Real.exp (Real.pi * |w.im| / 4) * Real.exp (Real.pi * |s.im| / 4) := by
    rw [← Real.exp_add, Real.exp_le_exp]
    linarith [mul_le_mul_of_nonneg_left him Real.pi_pos.le]
  rw [Complex.Gammaℝ_def, mul_inv_rev, neg_div, ← Complex.cpow_neg, neg_neg,
    norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
  change ‖(Complex.Gamma z)⁻¹‖ * Real.pi ^ z.re ≤ _
  calc
    _ ≤ (C * ((1 + |w.im|) * (1 + |s.im|)) *
        (Real.exp (Real.pi * |w.im| / 4) * Real.exp (Real.pi * |s.im| / 4))) * P := by
      refine mul_le_mul ((hΓ z hz).trans ?_) (Real.rpow_le_rpow_of_exponent_le
        (by linarith [Real.pi_gt_three]) hz.2) (Real.rpow_nonneg Real.pi_pos.le _) (by positivity)
      gcongr
    _ = _ := by ring

/-- The complex archimedean Euler factor has reciprocal exponential rate
π/2 on a positive strip, including a fixed shift of nonnegative real part. -/
theorem exists_norm_inv_GammaComplex_add_le_on_strip
    (a b : ℝ) (ha : 0 < a) (w : ℂ) (hw : 0 ≤ w.re) :
    ∃ C > 0, ∀ s : ℂ, s.re ∈ Icc a b →
      ‖(Complex.Gammaℂ (s + w))⁻¹‖ ≤
        C * ((1 + |s.im|) * Real.exp (Real.pi * |s.im| / 2)) := by
  obtain ⟨C, hC, hΓ⟩ := exists_norm_inv_Gamma_le_half_exp_on_strip
    (a + w.re) (b + w.re) (by linarith)
  let P := (2 * Real.pi) ^ (b + w.re)
  have hP : 0 < P := by dsimp [P]; positivity
  refine ⟨C * (1 + |w.im|) * Real.exp (Real.pi * |w.im| / 2) * P, by positivity, fun s hs ↦ ?_⟩
  have hstrip : (s + w).re ∈ Icc (a + w.re) (b + w.re) := by
    simp only [Complex.add_re, mem_Icc, add_le_add_iff_right]
    exact hs
  have him : |(s + w).im| ≤ |s.im| + |w.im| := by simpa only [Complex.add_im] using abs_add_le s.im w.im
  have hpoly : 1 + |(s + w).im| ≤ (1 + |w.im|) * (1 + |s.im|) := by
    nlinarith [mul_nonneg (abs_nonneg w.im) (abs_nonneg s.im)]
  have hexp : Real.exp (Real.pi * |(s + w).im| / 2) ≤
      Real.exp (Real.pi * |w.im| / 2) * Real.exp (Real.pi * |s.im| / 2) := by
    rw [← Real.exp_add, Real.exp_le_exp]
    linarith [mul_le_mul_of_nonneg_left him Real.pi_pos.le]
  rw [Complex.Gammaℂ_def, mul_inv_rev, mul_inv_rev, ← Complex.cpow_neg, neg_neg,
    norm_mul, norm_mul, show 2 * (Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; rfl,
    Complex.norm_cpow_eq_rpow_re_of_pos (by positivity : 0 < 2 * Real.pi), ← mul_assoc]
  have htwo : ‖(2 : ℂ)⁻¹‖ ≤ 1 := by norm_num [norm_inv]
  have hb : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  calc
    _ ≤ (C * ((1 + |(s + w).im|) * Real.exp (Real.pi * |(s + w).im| / 2))) * P * 1 := by
      gcongr
      · simpa only [mul_assoc] using hΓ _ hstrip
      · exact Real.rpow_le_rpow_of_exponent_le hb hstrip.2
    _ ≤ (C * (((1 + |w.im|) * (1 + |s.im|)) *
        (Real.exp (Real.pi * |w.im| / 2) * Real.exp (Real.pi * |s.im| / 2)))) * P * 1 := by
      gcongr
    _ = _ := by ring

end Masullo
