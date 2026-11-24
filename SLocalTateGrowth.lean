import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.Asymptotics.Defs
import GammaStripBounds
import PolynomialStrip

open Complex Filter Metric Set
open scoped Asymptotics ComplexConjugate

namespace Masullo

private theorem gamma_norm_natShift (z : ℂ) (n : ℕ)
    (hz : ∀ j : ℕ, j < n → z + j ≠ 0) :
    ‖Complex.Gamma (z + n)‖ = ‖Complex.Gamma z‖ *
      ∏ j ∈ Finset.range n, ‖z + (j : ℂ)‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ, ← add_assoc, Complex.Gamma_add_one _ (hz n n.lt_succ_self),
      norm_mul, ih (fun j hj ↦ hz j (hj.trans n.lt_succ_self)), Finset.prod_range_succ]
    ring

private theorem gamma_avoids_poles_of_re_pos {z : ℂ} (hz : 0 < z.re) (n : ℕ) :
    z ≠ -(n : ℂ) := by
  intro h
  rw [h, Complex.neg_re, Complex.natCast_re] at hz
  exact (not_lt_of_ge (neg_nonpos.mpr (Nat.cast_nonneg n))) hz

/-- When the reflected arguments stay in the positive half-plane, integer
recurrence on the edges and three-lines give polynomial growth in between. -/
theorem gamma_reflectedRatio_sharp_on_positive_strip (c : ℝ) (n : ℕ)
    (hn : 0 < n) (ha : 1 ≤ (c - n) / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, z.re ∈ Icc ((c - n) / 2) ((c + n) / 2) →
      ‖Complex.Gamma z / Complex.Gamma ((c : ℂ) - z)‖ ≤
        C * (1 + |z.im|) ^ (2 * z.re - c) := by
  let a := (c - n) / 2
  let b := (c + n) / 2
  let w (z : ℂ) := (c : ℂ) - z
  let f (z : ℂ) := Complex.Gamma z / Complex.Gamma (w z)
  have hab : a < b := by dsimp [a, b]; linarith [show (0 : ℝ) < n by exact_mod_cast hn]
  have hstrip (z : ℂ) (hz : z.re ∈ Icc a b) : (w z).re ∈ Icc a b := by
    simp only [w, Complex.sub_re, Complex.ofReal_re]
    exact ⟨by dsimp [a, b] at *; linarith [hz.2],
      by dsimp [a, b] at *; linarith [hz.1]⟩
  have hf (z : ℂ) (hz : z.re ∈ Icc a b) : DifferentiableAt ℂ f z := by
    have hwp := gamma_avoids_poles_of_re_pos ((zero_lt_one.trans_le ha).trans_le (hstrip z hz).1)
    have hzp := gamma_avoids_poles_of_re_pos ((zero_lt_one.trans_le ha).trans_le hz.1)
    exact (Complex.differentiableAt_Gamma z hzp).div
      ((Complex.differentiableAt_Gamma (w z) hwp).comp z
        ((differentiableAt_const (c : ℂ)).sub differentiableAt_id)) (Complex.Gamma_ne_zero hwp)
  have hd : DiffContOnCl ℂ f (HadamardThreeLines.verticalStrip a b) := by
    refine ⟨fun z hz ↦ (hf z ⟨hz.1.le, hz.2.le⟩).differentiableWithinAt, ?_⟩
    have hclosed : closure (HadamardThreeLines.verticalStrip a b) ⊆ Complex.re ⁻¹' Icc a b :=
      closure_minimal (fun _ hz ↦ ⟨hz.1.le, hz.2.le⟩) (isClosed_Icc.preimage Complex.continuous_re)
    exact fun z hz ↦ (hf z (hclosed hz)).continuousAt.continuousWithinAt
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (Real.differentiableOn_Gamma_Ioi.continuousOn.mono
      (fun x (hx : x ∈ Icc a b) ↦ (zero_lt_one.trans_le ha).trans_le hx.1))
  obtain ⟨D, hD, hDb⟩ := exists_norm_inv_Gamma_le_half_exp_on_strip a b (zero_lt_one.trans_le ha)
  have him (z : ℂ) : |(w z).im| = |z.im| := by simp [w, Complex.sub_im]
  have hg (z : ℂ) (hz : z.re ∈ Icc a b) :
      ‖f z‖ ≤ (max M 0 * D) * Real.exp ((1 + Real.pi / 2) * |z.im|) := by
    have hnum : ‖Complex.Gamma z‖ ≤ max M 0 :=
      (norm_Gamma_le_real_Gamma ((zero_lt_one.trans_le ha).trans_le hz.1)).trans
        ((le_abs_self _).trans ((hM _ hz).trans (le_max_left _ _)))
    have hden := hDb (w z) (hstrip z hz)
    rw [him] at hden
    rw [show f z = Complex.Gamma z * (Complex.Gamma (w z))⁻¹ from div_eq_mul_inv _ _, norm_mul]
    calc
      _ ≤ max M 0 * (D * ((1 + |z.im|) * Real.exp (Real.pi * |z.im| / 2))) :=
        mul_le_mul hnum (by simpa only [mul_assoc] using hden) (norm_nonneg _) (le_max_right _ _)
      _ ≤ max M 0 * (D * (Real.exp |z.im| * Real.exp (Real.pi * |z.im| / 2))) := by
        gcongr
        linarith [Real.add_one_le_exp |z.im|]
      _ = _ := by rw [← Real.exp_add]; ring_nf
  have hstep (z : ℂ) (hz : a ≤ z.re) (j : ℕ) : 1 ≤ ‖z + (j : ℂ)‖ := by
    refine le_trans ?_ ((le_abs_self _).trans (Complex.abs_re_le_norm _))
    rw [Complex.add_re, Complex.natCast_re]
    linarith [show 1 ≤ a from ha, show (0 : ℝ) ≤ j by positivity]
  have hrec (z : ℂ) (hz : a ≤ z.re) :
      ‖Complex.Gamma (z + n)‖ = ‖Complex.Gamma z‖ *
        ∏ j ∈ Finset.range n, ‖z + (j : ℂ)‖ :=
    gamma_norm_natShift z n (fun j _ hzero ↦ by
      have hj := hstep z hz j
      rw [hzero, norm_zero] at hj
      norm_num at hj)
  have hleft (z : ℂ) (hz : z.re = a) :
      ‖f z‖ ≤ (2 : ℝ) ^ n * (1 + |z.im|) ^ (-(n : ℝ)) := by
    have hw : w z = conj (z + n) := by
      apply Complex.ext <;> simp [w, Complex.sub_re, Complex.sub_im, Complex.add_re, hz, a]
      ring
    let u := 1 + |z.im|
    have hu : 0 < u := by dsimp [u]; positivity
    have hprod : (u / 2) ^ n ≤ ∏ j ∈ Finset.range n, ‖z + (j : ℂ)‖ := by
      rw [← show (∏ _j ∈ Finset.range n, u / 2) = (u / 2) ^ n by simp [div_pow]]
      apply Finset.prod_le_prod (fun j _ ↦ by positivity : ∀ j ∈ Finset.range n, 0 ≤ u / 2)
      intro j _
      have him : |z.im| ≤ ‖z + (j : ℂ)‖ := by
        simpa only [Complex.add_im, Complex.natCast_im, add_zero] using
          Complex.abs_im_le_norm (z + (j : ℂ))
      dsimp [u]
      linarith [hstep z hz.ge j]
    have hG : ‖Complex.Gamma z‖ ≠ 0 := norm_ne_zero_iff.mpr
      (Complex.Gamma_ne_zero (gamma_avoids_poles_of_re_pos ((zero_lt_one.trans_le ha).trans_le hz.ge)))
    change ‖Complex.Gamma z / Complex.Gamma (w z)‖ ≤ _
    rw [hw, Complex.Gamma_conj, norm_div, Complex.norm_conj, hrec z hz.ge,
      mul_comm ‖Complex.Gamma z‖, div_mul_cancel_right₀ hG]
    have hp : 0 < (u / 2) ^ n := pow_pos (by positivity) _
    refine ((inv_le_inv₀ (hp.trans_le hprod) hp).mpr hprod).trans_eq ?_
    change ((u / 2) ^ n)⁻¹ = (2 : ℝ) ^ n * u ^ (-(n : ℝ))
    rw [Real.rpow_neg hu.le, Real.rpow_natCast, div_pow, inv_div, div_eq_mul_inv]
  have hb (z : ℂ) (hz : z.re = b) : ‖f z‖ ≤ (a + n + 1) ^ n * (1 + |z.im|) ^ (n : ℝ) := by
    have hw : (w z).re = a := by simp [w, Complex.sub_re, hz, a, b]; ring
    have he : z = conj (w z + n) := by
      apply Complex.ext <;> simp [w, Complex.sub_re, Complex.sub_im, Complex.add_re, hz, b]
      ring
    have hG : ‖Complex.Gamma (w z)‖ ≠ 0 := norm_ne_zero_iff.mpr
      (Complex.Gamma_ne_zero (gamma_avoids_poles_of_re_pos ((zero_lt_one.trans_le ha).trans_le hw.ge)))
    change ‖Complex.Gamma z / Complex.Gamma (w z)‖ ≤ _
    have hnum : ‖Complex.Gamma z‖ = ‖Complex.Gamma (w z)‖ *
        ∏ j ∈ Finset.range n, ‖w z + (j : ℂ)‖ := by
      calc
        _ = ‖Complex.Gamma (conj (w z + n))‖ := congrArg (fun u ↦ ‖Complex.Gamma u‖) he
        _ = _ := by rw [Complex.Gamma_conj, Complex.norm_conj, hrec _ hw.ge]
    rw [norm_div, hnum, mul_comm, mul_div_cancel_right₀ _ hG, Real.rpow_natCast, ← mul_pow]
    conv_rhs => rw [← show
      (∏ _j ∈ Finset.range n, (a + (n : ℝ) + 1) * (1 + |z.im|)) =
        ((a + (n : ℝ) + 1) * (1 + |z.im|)) ^ n by simp]
    apply Finset.prod_le_prod (fun _ _ ↦ norm_nonneg _)
    intro j hj
    have hjn : (j : ℝ) ≤ n := by exact_mod_cast (Finset.mem_range.mp hj).le
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    have ha₀ : 0 ≤ a := le_trans zero_le_one ha
    rw [Complex.add_re, Complex.natCast_re, hw, abs_of_nonneg (by positivity : 0 ≤ a + (j : ℝ)),
      Complex.add_im, Complex.natCast_im, add_zero, him]
    nlinarith [mul_nonneg (show 0 ≤ a + n by positivity) (abs_nonneg z.im)]
  have hC : 0 ≤ (a + (n : ℝ) + 1) ^ n := by positivity
  obtain ⟨C, hC, hbound⟩ := polynomial_threeLines_signed_exponents hab hd
    (mul_nonneg (le_max_right _ _) hD.le) (by positivity : 0 ≤ 1 + Real.pi / 2)
    hg (show 0 ≤ (2 : ℝ) ^ n by positivity) hC hleft hb
  refine ⟨C, hC, fun z hz ↦ ?_⟩
  have he : (1 - (z.re - a) / (b - a)) * (-(n : ℝ)) +
      (z.re - a) / (b - a) * (n : ℝ) = 2 * z.re - c := by
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    dsimp [a, b]
    rw [show (c + (n : ℝ)) / 2 - (c - (n : ℝ)) / 2 = n by ring]
    field_simp
    ring
  simpa only [he] using hbound z hz

/-- The weaker nonnegative-degree bound on the symmetric positive strip. -/
theorem gamma_reflectedRatio_norm_le_on_positive_strip (c : ℝ) (n : ℕ)
    (hn : 0 < n) (ha : 1 ≤ (c - n) / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, z.re ∈ Icc ((c - n) / 2) ((c + n) / 2) →
      ‖Complex.Gamma z / Complex.Gamma ((c : ℂ) - z)‖ ≤
        C * (1 + |z.im|) ^ (n : ℝ) := by
  obtain ⟨C, hC, h⟩ := gamma_reflectedRatio_sharp_on_positive_strip c n hn ha
  exact ⟨C, hC, fun z hz ↦ (h z hz).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg z.im]) (by linarith [hz.2])) hC)⟩

/-- The reflected gamma ratio has a sharp signed power bound on every closed
vertical strip at absolute heights at least one. Common upward shifts
reduce both gamma arguments to the positive-strip estimate. -/
theorem gamma_reflectedRatio_sharp_on_strip (c l r : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, z.re ∈ Icc l r → 1 ≤ |z.im| →
      ‖Complex.Gamma z / Complex.Gamma ((c : ℂ) - z)‖ ≤ C * (1 + |z.im|) ^ (2 * z.re - c) := by
  obtain ⟨n, hn⟩ := exists_nat_gt (max |2 * l - c| |2 * r - c| + 1)
  have hn₀ : 0 < n := by
    have : (0 : ℝ) < n := by
      linarith [abs_nonneg (2 * l - c), le_max_left |2 * l - c| |2 * r - c|]
    exact_mod_cast this
  obtain ⟨N, hN⟩ := exists_nat_gt ((n - c) / 2 + 1)
  let d := c + 2 * (N : ℝ)
  have hd : 1 ≤ (d - n) / 2 := by dsimp [d]; linarith
  obtain ⟨A, hA, hAb⟩ := gamma_reflectedRatio_sharp_on_positive_strip d n hn₀ hd
  let M := |c| + max |l| |r| + (N : ℝ) + 1
  have hM : 1 ≤ M := by
    dsimp [M]
    linarith [abs_nonneg c, abs_nonneg l, le_max_left |l| |r|, Nat.cast_nonneg (α := ℝ) N]
  have hM₀ : 0 ≤ M := zero_le_one.trans hM
  refine ⟨A * (2 * M) ^ N, mul_nonneg hA (pow_nonneg (by positivity) _), ?_⟩
  intro z hz ht
  let w := (c : ℂ) - z
  let P (u : ℂ) := ∏ j ∈ Finset.range N, ‖u + (j : ℂ)‖
  have hwim : |w.im| = |z.im| := by simp [w, Complex.sub_im]
  have hmin (u : ℂ) (hu : 1 ≤ |u.im|) (j : ℕ) : 1 ≤ ‖u + (j : ℂ)‖ := by
    refine hu.trans ?_
    simpa only [Complex.add_im, Complex.natCast_im, add_zero] using
      Complex.abs_im_le_norm (u + (j : ℂ))
  have hpMin : 1 ≤ P z := by
    simpa [P] using (Finset.prod_le_prod (s := Finset.range N)
      (f := fun _ ↦ (1 : ℝ)) (fun _ _ ↦ zero_le_one) (fun j _ ↦ hmin z ht j))
  have hwMin (j : ℕ) : 1 ≤ ‖w + (j : ℂ)‖ := hmin w (hwim.symm ▸ ht) j
  have hrec (u : ℂ) (hu : ∀ j : ℕ, 1 ≤ ‖u + (j : ℂ)‖) :
      ‖Complex.Gamma (u + N)‖ = ‖Complex.Gamma u‖ * P u :=
    gamma_norm_natShift u N (fun j _ hzero ↦ by
      have hj := hu j
      rw [hzero, norm_zero] at hj
      norm_num at hj)
  have hpMax : P w ≤ (2 * M) ^ N * P z := by
    dsimp only [P]
    rw [← show (∏ _j ∈ Finset.range N, 2 * M) = (2 * M) ^ N by simp,
      ← Finset.prod_mul_distrib]
    apply Finset.prod_le_prod (fun _ _ ↦ norm_nonneg _)
    intro j hj
    have hjn : (j : ℝ) ≤ N := by exact_mod_cast (Finset.mem_range.mp hj).le
    have hzre : |z.re| ≤ max |l| |r| := abs_le.mpr
      ⟨(neg_le_neg ((neg_le_abs l).trans (le_max_left _ _))).trans (by linarith [hz.1]),
        hz.2.trans ((le_abs_self r).trans (le_max_right _ _))⟩
    have hwre : |(w + (j : ℂ)).re| ≤ |c| + max |l| |r| + (N : ℝ) := by
      simp only [w, Complex.add_re, Complex.sub_re, Complex.ofReal_re, Complex.natCast_re]
      exact (abs_add_le _ _).trans (add_le_add
        ((abs_sub _ _).trans (by linarith))
        (by rwa [abs_of_nonneg (Nat.cast_nonneg _)]))
    have him : |(w + (j : ℂ)).im| = |z.im| := by
      simpa only [Complex.add_im, Complex.natCast_im, add_zero] using hwim
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    rw [him]
    have hi : |z.im| ≤ ‖z + (j : ℂ)‖ := by
      simpa only [Complex.add_im, Complex.natCast_im, add_zero] using
        Complex.abs_im_le_norm (z + (j : ℂ))
    have hbound : 1 + |z.im| ≤ 2 * ‖z + (j : ℂ)‖ := by linarith
    calc
      _ ≤ M * (1 + |z.im|) := by
        nlinarith [mul_nonneg (show 0 ≤ M - 1 by linarith) (abs_nonneg z.im)]
      _ ≤ _ := by
        rw [mul_comm (2 : ℝ) M, mul_assoc]
        exact mul_le_mul_of_nonneg_left hbound hM₀
  have hs : (z + N).re ∈ Icc ((d - n) / 2) ((d + n) / 2) := by
    rw [Complex.add_re, Complex.natCast_re]
    dsimp [d]
    have hL : -(2 * l - c) ≤ max |2 * l - c| |2 * r - c| :=
      (neg_le_abs _).trans (le_max_left _ _)
    have hR : 2 * r - c ≤ max |2 * l - c| |2 * r - c| :=
      (le_abs_self _).trans (le_max_right _ _)
    exact ⟨by linarith [hz.1], by linarith [hz.2]⟩
  have he : (d : ℂ) - (z + (N : ℂ)) = w + (N : ℂ) := by
    dsimp [d, w]
    push_cast
    ring
  have hpos := hAb (z + N) hs
  rw [he, Complex.add_im, Complex.natCast_im, add_zero, Complex.add_re, Complex.natCast_re,
    show 2 * (z.re + (N : ℝ)) - d = 2 * z.re - c by dsimp [d]; ring] at hpos
  have hpz : P z ≠ 0 := (lt_of_lt_of_le zero_lt_one hpMin).ne'
  have hpw : P w ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ ↦
    (lt_of_lt_of_le zero_lt_one (hwMin j)).ne'
  have hGw : ‖Complex.Gamma w‖ ≠ 0 := norm_ne_zero_iff.mpr
    (Complex.Gamma_ne_zero fun m hm ↦ by
      have him := congrArg Complex.im hm
      simp only [Complex.neg_im, Complex.natCast_im, neg_zero] at him
      rw [← hwim, him, abs_zero] at ht
      norm_num at ht)
  have heq : ‖Complex.Gamma z / Complex.Gamma w‖ =
      ‖Complex.Gamma (z + N) / Complex.Gamma (w + N)‖ * P w / P z := by
    rw [norm_div, norm_div, hrec z (hmin z ht), hrec w hwMin]
    field_simp [hpz, hpw, hGw]
  rw [heq, mul_div_assoc]
  have hratio : P w / P z ≤ (2 * M) ^ N :=
    (div_le_iff₀ (lt_of_lt_of_le zero_lt_one hpMin)).mpr hpMax
  calc
    _ ≤ (A * (1 + |z.im|) ^ (2 * z.re - c)) * (2 * M) ^ N :=
      mul_le_mul hpos hratio (div_nonneg (Finset.prod_nonneg fun _ _ ↦ norm_nonneg _) (zero_le_one.trans hpMin))
        (by positivity)
    _ = _ := by ring

/-- The weaker nonnegative-degree bound on an arbitrary closed strip. -/
theorem gamma_reflectedRatio_norm_le_on_strip (c l r : ℝ) :
    ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧ ∀ z : ℂ, z.re ∈ Icc l r → 1 ≤ |z.im| →
      ‖Complex.Gamma z / Complex.Gamma ((c : ℂ) - z)‖ ≤ C * (1 + |z.im|) ^ k := by
  obtain ⟨C, hC, h⟩ := gamma_reflectedRatio_sharp_on_strip c l r
  obtain ⟨k, hk⟩ := exists_nat_gt (2*r-c)
  refine ⟨C, k, hC, fun z hz ht ↦ (h z hz ht).trans ?_⟩
  rw [← Real.rpow_natCast]
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg z.im]) (by linarith [hz.2])) hC

/-- Comparing two positive bases up to a factor controls powers of either sign. -/
theorem rpow_le_mul_rpow_of_comparable {x y B e M : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hB : 1 ≤ B) (hxy : x ≤ B * y) (hyx : y ≤ B * x) (hM : |e| ≤ M) :
    x ^ e ≤ B ^ M * y ^ e := by
  have hb : 0 < B := zero_lt_one.trans_le hB
  by_cases he : 0 ≤ e
  · calc
      _ ≤ (B * y) ^ e := Real.rpow_le_rpow hx.le hxy he
      _ = B ^ e * y ^ e := Real.mul_rpow hb.le hy.le
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_le hB ((le_abs_self e).trans hM)) (by positivity)
  · have hle : y / B ≤ x := (div_le_iff₀ hb).mpr (by simpa only [mul_comm x B] using hyx)
    calc
      _ ≤ (y / B) ^ e := Real.rpow_le_rpow_of_nonpos (div_pos hy hb) hle (le_of_not_ge he)
      _ = B ^ (-e) * y ^ e := by
        rw [Real.div_rpow hy.le hb.le, Real.rpow_neg hb.le, div_eq_mul_inv, mul_comm]
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_le hB ((neg_le_abs e).trans hM)) (by positivity)

/-- The powers of the positive normalization constants in the Deligne
factors change a strip bound by only a constant. -/
theorem gamma_normalizedReflectedRatio_sharp_on_strip (q c l r : ℝ) (hq : 1 ≤ q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, z.re ∈ Icc l r → 1 ≤ |z.im| →
      ‖((q : ℂ) ^ (-z) * Complex.Gamma z) /
        ((q : ℂ) ^ (-((c : ℂ) - z)) * Complex.Gamma ((c : ℂ) - z))‖ ≤
        C * (1 + |z.im|) ^ (2 * z.re - c) := by
  obtain ⟨C, hC, hb⟩ := gamma_reflectedRatio_sharp_on_strip c l r
  have hq₀ : 0 < q := zero_lt_one.trans_le hq
  refine ⟨q ^ (c - 2*l) * C, mul_nonneg (Real.rpow_nonneg hq₀.le _) hC, fun z hz ht ↦ ?_⟩
  have hnorm : ‖(q : ℂ) ^ (-z)‖ / ‖(q : ℂ) ^ (-((c : ℂ) - z))‖ =
      q ^ (c - 2*z.re) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hq₀, Complex.norm_cpow_eq_rpow_re_of_pos hq₀,
      ← Real.rpow_sub hq₀]
    simp only [Complex.neg_re, Complex.sub_re, Complex.ofReal_re]
    congr 1
    ring
  rw [mul_div_mul_comm, norm_mul, norm_div, hnorm]
  calc
    _ ≤ q ^ (c - 2*l) * (C * (1 + |z.im|) ^ (2 * z.re - c)) :=
      mul_le_mul (Real.rpow_le_rpow_of_exponent_le hq (by linarith [hz.1]))
        (hb z hz ht) (norm_nonneg _) (Real.rpow_nonneg hq₀.le _)
    _ = _ := by ring

/-- Polynomial growth of the normalized ratio survives the fixed
imaginary twist, parity or angular shift, and real-place scaling. -/
theorem gamma_affineReflectedRatio_sharp_on_strip (q m d l r : ℝ)
    (hq : 1 ≤ q) (hd : 0 < d) (a : ℂ) (ha : a.re = 0) :
    ∃ C T : ℝ, 0 ≤ C ∧ ∀ z : ℂ, z.re ∈ Icc l r → T ≤ |z.im| →
      let G (w : ℂ) := (q : ℂ) ^ (-w) * Complex.Gamma w
      ‖G ((z + a + (m : ℂ)) / (d : ℂ)) / G ((1 - z - a + (m : ℂ)) / (d : ℂ))‖ ≤
        C * (1 + |z.im|) ^ ((2 * z.re - 1) / d) := by
  let c := (1 + 2*m) / d
  obtain ⟨A, hA, hb⟩ := gamma_normalizedReflectedRatio_sharp_on_strip q c
    ((l+m)/d) ((r+m)/d) hq
  let B₁ := 1 + (1 + |a.im|) / d
  let B₂ := 1 + d + |a.im|
  let B := max B₁ B₂
  let M := (2 * max |l| |r| + 1) / d
  have hB : 1 ≤ B := (le_add_of_nonneg_right (by positivity : 0 ≤ (1 + |a.im|) / d)).trans
    (le_max_left _ _)
  refine ⟨A * B ^ M, d + |a.im|, mul_nonneg hA (Real.rpow_nonneg (zero_le_one.trans hB) _),
    fun z hz ht ↦ ?_⟩
  intro G
  let u := (z + a + (m : ℂ)) / (d : ℂ)
  have hure : u.re = (z.re + m) / d := by
    simp [u, Complex.div_ofReal_re, Complex.add_re, ha]
  have huim : |u.im| = |z.im + a.im| / d := by
    simp [u, Complex.div_ofReal_im, Complex.add_im, abs_div, abs_of_pos hd]
  have hstrip : u.re ∈ Icc ((l+m)/d) ((r+m)/d) := by
    rw [hure]
    exact ⟨div_le_div_of_nonneg_right (by linarith [hz.1]) hd.le,
      div_le_div_of_nonneg_right (by linarith [hz.2]) hd.le⟩
  have hheight : 1 ≤ |u.im| := by
    rw [huim, le_div_iff₀ hd, one_mul]
    have htri := abs_add_le (z.im+a.im) (-a.im)
    rw [add_neg_cancel_right, abs_neg] at htri
    linarith
  have hscale : 1 + |u.im| ≤ B * (1 + |z.im|) := by
    apply le_trans _ (mul_le_mul_of_nonneg_right (le_max_left B₁ B₂) (by positivity))
    rw [huim]
    have htri := div_le_div_of_nonneg_right (abs_add_le z.im a.im) hd.le
    have he : B₁ * (1 + |z.im|) = 1 + (|z.im| + |a.im|) / d +
        (|z.im| + 1 / d + (|a.im| / d) * |z.im|) := by
      dsimp only [B₁]
      ring
    rw [he]
    exact (add_le_add_right htri 1).trans (le_add_of_nonneg_right (by positivity))
  have hreverse : 1 + |z.im| ≤ B * (1 + |u.im|) := by
    apply le_trans _ (mul_le_mul_of_nonneg_right (le_max_right B₁ B₂) (by positivity))
    have htri : |z.im| ≤ |z.im + a.im| + |a.im| := by
      simpa using abs_add_le (z.im + a.im) (-a.im)
    have he : d * |u.im| = |z.im + a.im| := by rw [huim, mul_div_cancel₀ _ hd.ne']
    dsimp [B₂]
    linarith [mul_nonneg (show 0 ≤ 1 + |a.im| by positivity) (abs_nonneg u.im)]
  let e := (2 * z.re - 1) / d
  have he : 2 * u.re - c = e := by rw [hure]; dsimp [c,e]; ring
  have hM : |e| ≤ M := by
    have hz' : |z.re| ≤ max |l| |r| := abs_le.mpr
      ⟨(neg_le_neg ((neg_le_abs l).trans (le_max_left _ _))).trans (by simpa using hz.1),
        hz.2.trans ((le_abs_self r).trans (le_max_right _ _))⟩
    dsimp [e,M]
    rw [abs_div, abs_of_pos hd]
    apply div_le_div_of_nonneg_right _ hd.le
    refine (abs_sub _ _).trans ?_
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_one]
    linarith
  have hpower := rpow_le_mul_rpow_of_comparable
    (x := 1 + |u.im|) (y := 1 + |z.im|) (by positivity) (by positivity)
    hB hscale hreverse hM
  have hreflect : (c : ℂ) - u = (1 - z - a + (m : ℂ)) / (d : ℂ) := by
    dsimp [c, u]
    push_cast
    ring
  rw [← hreflect]
  calc
    _ ≤ A * (1 + |u.im|) ^ e := by simpa only [he] using hb u hstrip hheight
    _ ≤ A * (B ^ M * (1 + |z.im|) ^ e) := mul_le_mul_of_nonneg_left hpower hA
    _ = _ := by rw [mul_assoc]

/-- The powers of the positive normalization constants in the Deligne
factors change a strip bound by only a constant. -/
theorem gamma_normalizedReflectedRatio_norm_le_on_strip (q c l r : ℝ) (hq : 1 ≤ q) :
    ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧ ∀ z : ℂ, z.re ∈ Icc l r → 1 ≤ |z.im| →
      ‖((q : ℂ) ^ (-z) * Complex.Gamma z) /
        ((q : ℂ) ^ (-((c : ℂ) - z)) * Complex.Gamma ((c : ℂ) - z))‖ ≤
        C * (1 + |z.im|) ^ k := by
  obtain ⟨C, hC, hb⟩ := gamma_normalizedReflectedRatio_sharp_on_strip q c l r hq
  obtain ⟨k, hk⟩ := exists_nat_gt (2*r-c)
  refine ⟨C, k, hC, fun z hz ht ↦ (hb z hz ht).trans ?_⟩
  rw [← Real.rpow_natCast]
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg z.im]) (by linarith [hz.2])) hC

/-- Polynomial growth of the normalized ratio survives the fixed
imaginary twist, parity or angular shift, and real-place scaling. -/
theorem gamma_affineReflectedRatio_norm_le_on_strip (q m d l r : ℝ)
    (hq : 1 ≤ q) (hd : 0 < d) (a : ℂ) (ha : a.re = 0) :
    ∃ (C T : ℝ) (k : ℕ), 0 ≤ C ∧ ∀ z : ℂ, z.re ∈ Icc l r → T ≤ |z.im| →
      let G (w : ℂ) := (q : ℂ) ^ (-w) * Complex.Gamma w
      ‖G ((z + a + (m : ℂ)) / (d : ℂ)) / G ((1 - z - a + (m : ℂ)) / (d : ℂ))‖ ≤
        C * (1 + |z.im|) ^ k := by
  obtain ⟨C,T,hC,hb⟩ := gamma_affineReflectedRatio_sharp_on_strip q m d l r hq hd a ha
  obtain ⟨k,hk⟩ := exists_nat_gt ((2*r-1)/d)
  refine ⟨C,T,k,hC, fun z hz ht ↦ (hb z hz ht).trans ?_⟩
  rw [← Real.rpow_natCast]
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le
    (by linarith [abs_nonneg z.im]) ((div_le_div_of_nonneg_right (by linarith [hz.2]) hd.le).trans hk.le)) hC

/-- An affine vertical growth exponent survives all complex derivatives with
one logarithmic factor per derivative. The Cauchy circle shrinks on the
inverse-logarithmic scale to keep the exponent variation bounded. -/
theorem iteratedDeriv_affine_vertical_bound {f : ℂ → ℂ}
    (ha : ∀ z : ℂ, 0 < z.re → AnalyticAt ℂ f z)
    (D : ℝ) (hD : 0 ≤ D) (l r : ℝ) (hl : 0 < l)
    (hb : ∃ C T : ℝ, 0 ≤ C ∧ ∀ z : ℂ, z.re ∈ Icc (l / 2) (r + 1) → T ≤ |z.im| →
      ‖f z‖ ≤ C * (1 + |z.im|) ^ (D * (z.re - 1/2)))
    (k : ℕ) :
    ∃ C T : ℝ, 0 ≤ C ∧ ∀ z : ℂ, z.re ∈ Icc l r → T ≤ |z.im| →
      ‖iteratedDeriv k f z‖ ≤
        C * (1 + |z.im|) ^ (D * (z.re - 1/2)) * Real.log (1 + |z.im|) ^ k := by
  obtain ⟨C,T,hC,hbound⟩ := hb
  let c := min (l / 2) 1
  have hc : 0 < c := lt_min (by positivity) zero_lt_one
  let K := c⁻¹ / Real.log 2 + 1
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  let M := D * (max |l / 2| |r + 1| + 1/2)
  let A := C * (2 ^ M * Real.exp D)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨k.factorial * A * K^k, max 1 (T + 1), by positivity, fun z hz ht ↦ ?_⟩
  let B := 1 + |z.im|
  have hB : 2 ≤ B := by dsimp [B]; linarith [((le_max_left (1 : ℝ) (T+1)).trans ht)]
  have hB₀ : 0 < B := by linarith
  have hlogB : Real.log 2 ≤ Real.log B := Real.log_le_log (by norm_num) hB
  have hlog : 0 < Real.log B := hlog2.trans_le hlogB
  let R := min c (Real.log B)⁻¹
  have hR : 0 < R := lt_min hc (inv_pos.mpr hlog)
  have hRc : R ≤ c := min_le_left _ _
  have hR1 : R ≤ 1 := hRc.trans (min_le_right _ _)
  have hRl : R ≤ l / 2 := hRc.trans (min_le_left _ _)
  have hRlog : R * Real.log B ≤ 1 := by
    simpa only [inv_mul_cancel₀ hlog.ne'] using
      mul_le_mul_of_nonneg_right (min_le_right c (Real.log B)⁻¹) hlog.le
  have hRinv : R⁻¹ ≤ K * Real.log B := by
    have hleft : c⁻¹ ≤ (c⁻¹ / Real.log 2) * Real.log B := by
      calc
        _ = (c⁻¹ / Real.log 2) * Real.log 2 := (div_mul_cancel₀ _ hlog2.ne').symm
        _ ≤ _ := mul_le_mul_of_nonneg_left hlogB (by positivity)
    dsimp [R,K]
    rw [add_mul, one_mul]
    rcases le_total c (Real.log B)⁻¹ with hh | hh
    · rw [min_eq_left hh]
      exact hleft.trans (le_add_of_nonneg_right hlog.le)
    · rw [min_eq_right hh, inv_inv]
      exact le_add_of_nonneg_left (by positivity)
  have hdisc (w : ℂ) (hw : w ∈ closedBall z R) :
      w.re ∈ Icc (l / 2) (r + 1) ∧ T ≤ |w.im| ∧
      |w.re - z.re| ≤ R ∧ |w.im - z.im| ≤ R := by
    have hr := mem_closedBall_iff_norm.mp hw
    have hre : |w.re - z.re| ≤ R := by simpa only [Complex.sub_re] using
      (Complex.abs_re_le_norm (w - z)).trans hr
    have him : |w.im - z.im| ≤ R := by simpa only [Complex.sub_im] using
      (Complex.abs_im_le_norm (w - z)).trans hr
    have hti := (abs_abs_sub_abs_le_abs_sub w.im z.im).trans him
    exact ⟨⟨by linarith [hz.1, (abs_le.mp hre).1],
      by linarith [hz.2, (abs_le.mp hre).2]⟩,
      by linarith [(abs_le.mp hti).1, (le_max_right (1 : ℝ) (T+1)).trans ht],
      hre, him⟩
  have hhol : AnalyticOnNhd ℂ f (closedBall z R) := fun w hw ↦
    ha w ((by positivity : 0 < l/2).trans_le (hdisc w hw).1.1)
  have hdiff : DiffContOnCl ℂ f (ball z R) := by
    refine ⟨fun w hw ↦ (hhol w (ball_subset_closedBall hw)).differentiableAt.differentiableWithinAt, ?_⟩
    rw [closure_ball z hR.ne']
    exact hhol.continuousOn
  have hsphere (w : ℂ) (hw : w ∈ sphere z R) :
      ‖f w‖ ≤ A * B ^ (D * (z.re - 1/2)) := by
    obtain ⟨hwI,hwT,hre,him⟩ := hdisc w (sphere_subset_closedBall hw)
    let e := D * (w.re - 1/2)
    have hM : |e| ≤ M := by
      have habs : |w.re| ≤ max |l / 2| |r + 1| :=
        abs_le.mpr ⟨(neg_le_neg ((neg_le_abs (l/2)).trans (le_max_left _ _))).trans
          (by simpa using hwI.1), hwI.2.trans ((le_abs_self _).trans (le_max_right _ _))⟩
      dsimp [e,M]
      rw [abs_mul, abs_of_nonneg hD]
      apply mul_le_mul_of_nonneg_left _ hD
      exact (abs_sub _ _).trans (by rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1/2)]; linarith)
    have hgap := (abs_le.mp ((abs_abs_sub_abs_le_abs_sub w.im z.im).trans him))
    have hpow : (1 + |w.im|) ^ e ≤ (2 : ℝ)^M * B^e :=
      rpow_le_mul_rpow_of_comparable (by positivity) hB₀ (by norm_num)
        (by dsimp [B]; linarith [hgap.2, abs_nonneg z.im])
        (by dsimp [B]; linarith [hgap.1, abs_nonneg w.im]) hM
    have hE : B ^ e ≤ B ^ (D * (z.re - 1/2)) * Real.exp D := by
      have he : e ≤ D * (z.re - 1/2) + D * R := by
        dsimp [e]
        nlinarith [mul_le_mul_of_nonneg_left (abs_le.mp hre).2 hD]
      rw [Real.rpow_def_of_pos hB₀, Real.rpow_def_of_pos hB₀, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      calc
        _ ≤ Real.log B * (D * (z.re - 1/2) + D * R) :=
          mul_le_mul_of_nonneg_left he hlog.le
        _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hRlog hD]
    calc
      ‖f w‖ ≤ C * (1 + |w.im|)^e := hbound w hwI hwT
      _ ≤ C * ((2 : ℝ)^M * B^e) := mul_le_mul_of_nonneg_left hpow hC
      _ ≤ C * ((2 : ℝ)^M * (B ^ (D * (z.re - 1/2)) * Real.exp D)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hE (by positivity)) hC
      _ = _ := by dsimp [A]; ring
  have hCauchy := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k hR hdiff hsphere
  rw [div_eq_mul_inv, ← inv_pow] at hCauchy
  refine hCauchy.trans ?_
  calc
    _ ≤ (k.factorial * (A * B^(D * (z.re - 1/2)))) * (K * Real.log B)^k :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hRinv _) (by positivity)
    _ = _ := by rw [mul_pow]; ring

/-- The zero-angular complex ratio in (3.3.1.19) has quadratic growth
on the line with real part three halves. -/
theorem complexTateGammaRatio_threeHalves (t : ℝ) :
    let s := (3 / 2 : ℂ) + (t : ℂ) * Complex.I
    ‖Complex.Gamma s / Complex.Gamma (1 - s)‖ = t ^ 2 + 1 / 4 := by
  intro s
  let w := (-1 / 2 : ℂ) + (t : ℂ) * Complex.I
  have hw₁ : w.re = -1 / 2 := by norm_num [w, Complex.mul_re]
  have hw₂ : w.im = t := by simp [w, Complex.mul_im]
  have hw₀ : w ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hw₁
    norm_num at hw₁
  have hwOne : w + 1 ≠ 0 := by
    intro h
    have he := congrArg Complex.re h
    rw [Complex.add_re, hw₁, Complex.one_re, Complex.zero_re] at he
    norm_num at he
  have hΓ : Complex.Gamma w ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro n hn
    have he := congrArg Complex.re hn
    rw [hw₁, Complex.neg_re, Complex.natCast_re] at he
    have hc : (n : ℝ) < 1 := by linarith
    have hn : n = 0 := Nat.lt_one_iff.mp (by exact_mod_cast hc)
    simp [hn] at he
  have hs : s = (w + 1) + 1 := by dsimp [s, w]; ring
  have hwconj : 1 - s = conj w := by
    simp only [s, w, map_add, map_div₀, map_neg, map_one, map_ofNat, map_mul,
      Complex.conj_ofReal, Complex.conj_I]
    ring
  have he : w + 1 = -(conj w) := by
    apply Complex.ext <;> norm_num [hw₁, hw₂]
  rw [hs, Complex.Gamma_add_one (w + 1) hwOne, Complex.Gamma_add_one w hw₀, ← hs, hwconj,
    Complex.Gamma_conj, norm_div, norm_mul, norm_mul, Complex.norm_conj, ← mul_assoc,
    mul_div_cancel_right₀ _ (norm_ne_zero_iff.mpr hΓ), he, norm_neg, Complex.norm_conj, ← sq,
    Complex.sq_norm, Complex.normSq_apply, hw₁, hw₂]
  ring

/-- The linear bound asserted for the zero-angular complex Gamma ratio
in Proposition 3.3.1.5(3) fails already without derivatives. -/
theorem printed_complexTateGammaRatio_not_isBigO :
    ¬ (fun t : ℝ =>
      let s := (3 / 2 : ℂ) + (t : ℂ) * Complex.I
      Complex.Gamma s / Complex.Gamma (1 - s)) =O[atTop] (fun t : ℝ => t) := by
  intro h
  obtain ⟨C, hC⟩ := Asymptotics.isBigO_iff.mp h
  obtain ⟨t, ht⟩ := eventually_atTop.mp hC
  let u := max t (max 1 (C + 1))
  have hu : t ≤ u := le_max_left _ _
  have hu₁ : 1 ≤ u := (le_max_left _ _).trans (le_max_right _ _)
  have huC : C + 1 ≤ u := (le_max_right _ _).trans (le_max_right _ _)
  have hb' := ht u hu
  rw [complexTateGammaRatio_threeHalves, Real.norm_of_nonneg (zero_le_one.trans hu₁)] at hb'
  nlinarith

end Masullo
