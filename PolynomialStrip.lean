import Mathlib.Analysis.Complex.Hadamard
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Convex.Continuous

open Complex Filter Function Set Topology

namespace Masullo

noncomputable section

/-- Polynomial growth on a vertical line, with inequalities required only
outside a bounded interval of imaginary parts. -/
def VerticalPolynomialBound (f : ℂ → ℂ) (x k : ℝ) : Prop :=
  ∃ C T : ℝ, 0 ≤ C ∧ ∀ y : ℝ, T ≤ |y| →
    ‖f ((x : ℂ) + (y : ℂ) * I)‖ ≤ C * (1 + |y|) ^ k

private theorem gaussian_poly_bound {k d : ℝ} (hk : 0 ≤ k) (hd : 0 ≤ d) :
    (1 + d) ^ k * Real.exp (-(d ^ 2)) ≤ Real.exp (k ^ 2 / 4) := by
  rw [Real.rpow_def_of_pos (by positivity), ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hlog : Real.log (1 + d) ≤ d := by
    have h := Real.log_le_sub_one_of_pos (show 0 < 1 + d by positivity)
    linarith
  have hh := mul_le_mul_of_nonneg_right hlog hk
  nlinarith [sq_nonneg (d - k / 2)]

private theorem gaussian_cutoff_bound (f : ℂ → ℂ) {C k : ℝ} (hC : 0 ≤ C)
    (y : ℝ) (z : ℂ) (hf : ‖f z‖ ≤ C * (1 + |z.im|) ^ k) :
    ‖f z * Complex.exp ((z - (y : ℂ) * I) ^ 2)‖ ≤
      C * Real.exp (z.re ^ 2 + k ^ 2 / 4) * (1 + |y|) ^ k := by
  let d := |z.im - y|
  have hd : 0 ≤ d := abs_nonneg _
  have hforward : 1 + |z.im| ≤ (1 + |y|) * (1 + d) := by
    have htriangle := abs_add_le (z.im - y) y
    rw [sub_add_cancel] at htriangle
    nlinarith [mul_nonneg (abs_nonneg y) hd]
  have hback : 1 + |y| ≤ (1 + |z.im|) * (1 + d) := by
    have htriangle := abs_add_le (y - z.im) z.im
    rw [sub_add_cancel, abs_sub_comm] at htriangle
    nlinarith [mul_nonneg (abs_nonneg z.im) hd]
  have hpoly : (1 + |z.im|) ^ k ≤ (1 + |y|) ^ k * (1 + d) ^ |k| := by
    by_cases hk : 0 ≤ k
    · rw [abs_of_nonneg hk, ← Real.mul_rpow (by positivity) (by positivity)]
      exact Real.rpow_le_rpow (by positivity) hforward hk
    · have hneg := lt_of_not_ge hk
      calc
        _ ≤ ((1 + |y|) / (1 + d)) ^ k :=
          Real.rpow_le_rpow_of_nonpos (by positivity) ((div_le_iff₀ (by positivity)).mpr hback) hneg.le
        _ = _ := by
          rw [abs_of_neg hneg, Real.div_rpow (by positivity) (by positivity),
            Real.rpow_neg (by positivity), div_eq_mul_inv]
  have hdecay : (1 + d) ^ |k| * Real.exp (-(d ^ 2)) ≤ Real.exp (k ^ 2 / 4) := by
    simpa only [sq_abs] using gaussian_poly_bound (abs_nonneg k) hd
  have hreal : ((z - (y : ℂ) * I) ^ 2).re = z.re ^ 2 - d ^ 2 := by
    dsimp only [d]
    rw [sq_abs, pow_two, mul_re]
    simp [mul_re, mul_im, pow_two]
  rw [norm_mul, norm_exp, hreal, sub_eq_add_neg, Real.exp_add]
  calc
    _ ≤ (C * ((1 + |y|) ^ k * (1 + d) ^ |k|)) *
        (Real.exp (z.re ^ 2) * Real.exp (-(d ^ 2))) :=
      mul_le_mul_of_nonneg_right (hf.trans (mul_le_mul_of_nonneg_left hpoly hC)) (by positivity)
    _ = C * Real.exp (z.re ^ 2) * (1 + |y|) ^ k *
        ((1 + d) ^ |k| * Real.exp (-(d ^ 2))) := by ring
    _ ≤ C * Real.exp (z.re ^ 2) * (1 + |y|) ^ k * Real.exp (k ^ 2 / 4) :=
      mul_le_mul_of_nonneg_left hdecay (by positivity)
    _ = _ := by rw [Real.exp_add]; ring

private theorem polynomial_threeLines_of_gaussian_bounded {f : ℂ → ℂ} {a b C₁ C₂ k₁ k₂ : ℝ} (hab : a < b)
    (hd : DiffContOnCl ℂ f (HadamardThreeLines.verticalStrip a b))
    (hB : ∀ y : ℝ, BddAbove ((norm ∘ (fun z : ℂ ↦ f z * Complex.exp ((z - (y : ℂ) * I) ^ 2)))
      '' HadamardThreeLines.verticalClosedStrip a b))
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hL : ∀ z : ℂ, z.re = a → ‖f z‖ ≤ C₁ * (1 + |z.im|) ^ k₁)
    (hR : ∀ z : ℂ, z.re = b → ‖f z‖ ≤ C₂ * (1 + |z.im|) ^ k₂) :
    ∀ z : ℂ, z.re ∈ Icc a b →
      ‖f z‖ ≤ max (C₁ * Real.exp (a ^ 2 + k₁ ^ 2 / 4))
        (C₂ * Real.exp (b ^ 2 + k₂ ^ 2 / 4)) * (1 + |z.im|) ^ ((1 - (z.re - a) / (b - a)) * k₁ +
        ((z.re - a) / (b - a)) * k₂) := by
  let A₁ := C₁ * Real.exp (a ^ 2 + k₁ ^ 2 / 4)
  let A₂ := C₂ * Real.exp (b ^ 2 + k₂ ^ 2 / 4)
  let C := max A₁ A₂
  have hA₁ : 0 ≤ A₁ := by dsimp [A₁]; positivity
  have hA₂ : 0 ≤ A₂ := by dsimp [A₂]; positivity
  have hC : 0 ≤ C := hA₁.trans (le_max_left _ _)
  intro z hz
  change ‖f z‖ ≤ C * _
  let y := z.im
  let T := 1 + |y|
  let G (w : ℂ) := f w * Complex.exp ((w - (y : ℂ) * I) ^ 2)
  let t := (z.re - a) / (b - a)
  have hT : 0 < T := by dsimp [T]; positivity
  have ht₀ : 0 ≤ t := div_nonneg (sub_nonneg.mpr hz.1) (sub_pos.mpr hab).le
  have ht₁ : t ≤ 1 := (div_le_one₀ (sub_pos.mpr hab)).mpr (sub_le_sub_right hz.2 _)
  have hg : Differentiable ℂ (fun w : ℂ => Complex.exp ((w - (y : ℂ) * I) ^ 2)) := by fun_prop
  have hG : DiffContOnCl ℂ G (HadamardThreeLines.verticalStrip a b) :=
    ⟨hd.1.mul hg.differentiableOn, hd.2.mul hg.continuous.continuousOn⟩
  have hsup := hB y
  have hL' (w : ℂ) (hw : w ∈ re ⁻¹' {a}) : ‖G w‖ ≤ C * T ^ k₁ := by
    have hre : w.re = a := hw
    refine (gaussian_cutoff_bound f hC₁ y w (hL w hre)).trans ?_
    rw [hre]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  have hR' (w : ℂ) (hw : w ∈ re ⁻¹' {b}) : ‖G w‖ ≤ C * T ^ k₂ := by
    have hre : w.re = b := hw
    refine (gaussian_cutoff_bound f hC₂ y w (hR w hre)).trans ?_
    rw [hre]
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
  have hGG := HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip' hab
    (z := z) hz hG hsup hL' hR'
  have hle : ‖f z‖ ≤ ‖G z‖ := by
    have hh : ((z - (y : ℂ) * I) ^ 2).re = z.re ^ 2 := by
      simp [y, pow_two, mul_re, mul_im]
    rw [show ‖G z‖ = ‖f z‖ * Real.exp (z.re ^ 2) by simp only [G, norm_mul, norm_exp, hh]]
    exact le_mul_of_one_le_right (norm_nonneg _) (Real.one_le_exp (sq_nonneg _))
  refine hle.trans (hGG.trans_eq ?_)
  change (C * T ^ k₁) ^ (1 - t) * (C * T ^ k₂) ^ t = C * T ^ ((1 - t) * k₁ + t * k₂)
  by_cases hCzero : C = 0
  · rw [hCzero, zero_mul, zero_mul, zero_mul]
    rcases eq_or_ne t 0 with ht | ht
    · rw [ht]
      norm_num
    · rw [Real.zero_rpow ht, mul_zero]
  have hCpos : 0 < C := lt_of_le_of_ne hC (Ne.symm hCzero)
  rw [Real.mul_rpow hC (by positivity), Real.mul_rpow hC (by positivity),
    ← Real.rpow_mul hT.le, ← Real.rpow_mul hT.le]
  calc
    _ = (C ^ (1 - t) * C ^ t) * (T ^ (k₁ * (1 - t)) * T ^ (k₂ * t)) := by ring
    _ = _ := by
      rw [← Real.rpow_add hCpos, ← Real.rpow_add hT,
        show 1 - t + t = 1 by ring, Real.rpow_one, mul_comm k₁, mul_comm k₂]

/-- Polynomial three-lines inequality with the interpolated exponent.
The Gaussian is centered at the imaginary coordinate where the bound is needed. -/
theorem polynomial_threeLines {f : ℂ → ℂ} {a b A K C₁ C₂ k₁ k₂ : ℝ} (hab : a < b)
    (hd : DiffContOnCl ℂ f (HadamardThreeLines.verticalStrip a b))
    (hA : 0 ≤ A) (_hK : 0 ≤ K)
    (hB : ∀ z : ℂ, z.re ∈ Icc a b → ‖f z‖ ≤ A * (1 + |z.im|) ^ K)
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (_hk₁ : 0 ≤ k₁) (_hk₂ : 0 ≤ k₂)
    (hL : ∀ z : ℂ, z.re = a → ‖f z‖ ≤ C₁ * (1 + |z.im|) ^ k₁)
    (hR : ∀ z : ℂ, z.re = b → ‖f z‖ ≤ C₂ * (1 + |z.im|) ^ k₂) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, z.re ∈ Icc a b →
      ‖f z‖ ≤ C * (1 + |z.im|) ^ ((1 - (z.re - a) / (b - a)) * k₁ +
        ((z.re - a) / (b - a)) * k₂) := by
  refine ⟨_, le_trans (by positivity) (le_max_left _ _),
    polynomial_threeLines_of_gaussian_bounded hab hd ?_ hC₁ hC₂ hL hR⟩
  intro y
  let T := 1 + |y|
  let R := max |a| |b|
  have hR₀ : 0 ≤ R := (abs_nonneg a).trans (le_max_left _ _)
  refine ⟨A * Real.exp (R ^ 2 + K ^ 2 / 4) * T ^ K, ?_⟩
  rintro _ ⟨w, hw, rfl⟩
  have hw' : w.re ∈ Icc a b := hw
  have hx : |w.re| ≤ R := by
    apply abs_le.mpr
    exact ⟨(neg_le.mpr ((neg_le_abs a).trans (le_max_left _ _))).trans hw'.1,
      hw'.2.trans ((le_abs_self b).trans (le_max_right _ _))⟩
  refine (gaussian_cutoff_bound f hA y w (hB w hw')).trans ?_
  have hsq : w.re ^ 2 ≤ R ^ 2 := by simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hx 2
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (add_le_add_left hsq _)) hA) (by positivity)

private theorem polynomial_threeLines_of_exponential_growth_explicit {f : ℂ → ℂ}
    {a b A K C₁ C₂ k₁ k₂ : ℝ} (hab : a < b)
    (hd : DiffContOnCl ℂ f (HadamardThreeLines.verticalStrip a b))
    (hA : 0 ≤ A) (hK : 0 ≤ K)
    (hB : ∀ z : ℂ, z.re ∈ Icc a b → ‖f z‖ ≤ A * Real.exp (K * |z.im|))
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hL : ∀ z : ℂ, z.re = a → ‖f z‖ ≤ C₁ * (1 + |z.im|) ^ k₁)
    (hR : ∀ z : ℂ, z.re = b → ‖f z‖ ≤ C₂ * (1 + |z.im|) ^ k₂) :
    ∀ z : ℂ, z.re ∈ Icc a b →
      ‖f z‖ ≤ max (C₁ * Real.exp (a ^ 2 + k₁ ^ 2 / 4))
        (C₂ * Real.exp (b ^ 2 + k₂ ^ 2 / 4)) * (1 + |z.im|) ^ ((1 - (z.re - a) / (b - a)) * k₁ +
        ((z.re - a) / (b - a)) * k₂) := by
  apply polynomial_threeLines_of_gaussian_bounded hab hd _ hC₁ hC₂ hL hR
  intro y
  let R := max |a| |b|
  refine ⟨A * Real.exp (R ^ 2 + K * |y| + K ^ 2 / 4), ?_⟩
  rintro _ ⟨w, hw, rfl⟩
  have hw' : w.re ∈ Icc a b := hw
  have hx : |w.re| ≤ R :=
    abs_le.mpr ⟨(neg_le.mpr ((neg_le_abs a).trans (le_max_left _ _))).trans hw'.1,
      hw'.2.trans ((le_abs_self b).trans (le_max_right _ _))⟩
  have hsq : w.re ^ 2 ≤ R ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hx 2
  have hreal : ((w - (y : ℂ) * I) ^ 2).re = w.re ^ 2 - (w.im - y) ^ 2 := by
    simp [mul_re, mul_im, pow_two]
  change ‖f w * Complex.exp ((w - (y : ℂ) * I) ^ 2)‖ ≤ _
  rw [norm_mul, norm_exp, hreal]
  refine (mul_le_mul_of_nonneg_right (hB w hw') (Real.exp_nonneg _)).trans ?_
  rw [mul_assoc, ← Real.exp_add]
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr _) hA
  have htri : |w.im| ≤ |w.im - y| + |y| := by
    simpa only [sub_add_cancel] using abs_add_le (w.im - y) y
  nlinarith [mul_le_mul_of_nonneg_left htri hK, sq_abs (w.im - y),
    sq_nonneg (|w.im - y| - K / 2)]

/-- Polynomial boundary estimates interpolate with the same exponents
when the holomorphic function has at most exponential growth in the strip. -/
theorem polynomial_threeLines_signed_exponents {f : ℂ → ℂ}
    {a b A K C₁ C₂ k₁ k₂ : ℝ} (hab : a < b)
    (hd : DiffContOnCl ℂ f (HadamardThreeLines.verticalStrip a b))
    (hA : 0 ≤ A) (hK : 0 ≤ K)
    (hB : ∀ z : ℂ, z.re ∈ Icc a b → ‖f z‖ ≤ A * Real.exp (K * |z.im|))
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hL : ∀ z : ℂ, z.re = a → ‖f z‖ ≤ C₁ * (1 + |z.im|) ^ k₁)
    (hR : ∀ z : ℂ, z.re = b → ‖f z‖ ≤ C₂ * (1 + |z.im|) ^ k₂) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, z.re ∈ Icc a b →
      ‖f z‖ ≤ C * (1 + |z.im|) ^ ((1 - (z.re - a) / (b - a)) * k₁ +
        ((z.re - a) / (b - a)) * k₂) := by
  exact ⟨_, le_trans (by positivity) (le_max_left _ _),
    polynomial_threeLines_of_exponential_growth_explicit hab hd hA hK hB hC₁ hC₂ hL hR⟩

/-- The nonnegative-exponent form of the polynomial three-lines inequality. -/
theorem polynomial_threeLines_of_exponential_growth {f : ℂ → ℂ}
    {a b A K C₁ C₂ k₁ k₂ : ℝ} (hab : a < b)
    (hd : DiffContOnCl ℂ f (HadamardThreeLines.verticalStrip a b))
    (hA : 0 ≤ A) (hK : 0 ≤ K)
    (hB : ∀ z : ℂ, z.re ∈ Icc a b → ‖f z‖ ≤ A * Real.exp (K * |z.im|))
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (_hk₁ : 0 ≤ k₁) (_hk₂ : 0 ≤ k₂)
    (hL : ∀ z : ℂ, z.re = a → ‖f z‖ ≤ C₁ * (1 + |z.im|) ^ k₁)
    (hR : ∀ z : ℂ, z.re = b → ‖f z‖ ≤ C₂ * (1 + |z.im|) ^ k₂) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, z.re ∈ Icc a b →
      ‖f z‖ ≤ C * (1 + |z.im|) ^ ((1 - (z.re - a) / (b - a)) * k₁ +
        ((z.re - a) / (b - a)) * k₂) :=
  polynomial_threeLines_signed_exponents hab hd hA hK hB hC₁ hC₂ hL hR

/-- The nonnegative growth exponent used in Lemma B.1.1.1. -/
def verticalGrowthExponent (f : ℂ → ℂ) (x : ℝ) : ℝ :=
  sInf {k : ℝ | 0 ≤ k ∧ VerticalPolynomialBound f x k}

private theorem verticalGrowth_bddBelow (f : ℂ → ℂ) (x : ℝ) :
    BddBelow {k : ℝ | 0 ≤ k ∧ VerticalPolynomialBound f x k} :=
  ⟨0, fun _ hk => hk.1⟩

private theorem verticalPolynomialBound_mono {f : ℂ → ℂ} {x k l : ℝ} (hk : k ≤ l)
    (hb : VerticalPolynomialBound f x k) : VerticalPolynomialBound f x l := by
  obtain ⟨C, T, hC, h⟩ := hb
  exact ⟨C, T, hC, fun y hy => (h y hy).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg y]) hk) hC)⟩

private theorem verticalGrowth_bound_above_inf {f : ℂ → ℂ} {x ε : ℝ}
    (hn : {k : ℝ | 0 ≤ k ∧ VerticalPolynomialBound f x k}.Nonempty) (hε : 0 < ε) :
    VerticalPolynomialBound f x (verticalGrowthExponent f x + ε) := by
  obtain ⟨k, hk, hlt⟩ := exists_lt_of_csInf_lt hn
    (show verticalGrowthExponent f x < verticalGrowthExponent f x + ε by linarith)
  exact verticalPolynomialBound_mono hlt.le hk.2

private theorem verticalPoly_extend_to_all {f : ℂ → ℂ} {a b k : ℝ}
    (hc : ContinuousOn f (re ⁻¹' Icc a b)) (hk : 0 ≤ k)
    (h : ∃ C T : ℝ, 0 ≤ C ∧ ∀ z : ℂ, z.re ∈ Icc a b → T ≤ |z.im| →
      ‖f z‖ ≤ C * (1 + |z.im|) ^ k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, z.re ∈ Icc a b → ‖f z‖ ≤ C * (1 + |z.im|) ^ k := by
  obtain ⟨C, T, hC, h⟩ := h
  let K := (Icc a b) ×ℂ (Icc (-T) T)
  have hK : IsCompact K :=
    equivRealProdCLM.toHomeomorph.isCompact_preimage.mpr (isCompact_Icc.prod isCompact_Icc)
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn
    (hc.mono (fun _ hz => (mem_reProdIm.mp hz).1))
  refine ⟨max M C, hC.trans (le_max_right _ _), fun z hz => ?_⟩
  by_cases ht : T ≤ |z.im|
  · exact (h z hz ht).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
  · have hzK : z ∈ K := mem_reProdIm.mpr ⟨hz, abs_le.mp (le_of_lt (not_le.mp ht))⟩
    exact (hM z hzK).trans ((le_max_left _ _).trans
      (le_mul_of_one_le_right (hC.trans (le_max_right _ _))
        (Real.one_le_rpow (by linarith [abs_nonneg z.im]) hk)))

private theorem verticalPolynomialBound_extend_to_all {f : ℂ → ℂ} {x k : ℝ}
    (hc : ContinuousOn f (re ⁻¹' {x})) (hk : 0 ≤ k) (h : VerticalPolynomialBound f x k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, z.re = x → ‖f z‖ ≤ C * (1 + |z.im|) ^ k := by
  obtain ⟨C, T, hC, h⟩ := h
  have hf : ∀ z : ℂ, z.re ∈ Icc x x → T ≤ |z.im| →
      ‖f z‖ ≤ C * (1 + |z.im|) ^ k := by
    intro z hz ht
    have hz' : z.re = x := le_antisymm hz.2 hz.1
    have he : (x : ℂ) + (z.im : ℂ) * I = z := hz' ▸ re_add_im z
    have hh := h z.im ht
    rwa [he] at hh
  have hc' : ContinuousOn f (re ⁻¹' Icc x x) := by simpa only [Icc_self] using hc
  obtain ⟨A, hA, hb⟩ := verticalPoly_extend_to_all hc' hk ⟨C, T, hC, hf⟩
  exact ⟨A, hA, fun z hz => hb z (hz ▸ left_mem_Icc.mpr le_rfl)⟩

private theorem holomorphic_exponential_strip_bound {f : ℂ → ℂ} {a b K : ℝ}
    (hc : ContinuousOn f (re ⁻¹' Icc a b)) (hK : 0 ≤ K)
    (hB : f =O[Filter.comap (abs ∘ im) atTop ⊓ 𝓟 (re ⁻¹' Icc a b)]
      fun z : ℂ ↦ Real.exp (K * |z.im|)) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ z : ℂ, z.re ∈ Icc a b → ‖f z‖ ≤ A * Real.exp (K * |z.im|) := by
  obtain ⟨A, hA, hb⟩ := hB.exists_pos
  have hfar : ∀ᶠ z : ℂ in Filter.comap (abs ∘ im) atTop, z.re ∈ Icc a b →
      ‖f z‖ ≤ A * Real.exp (K * |z.im|) := by
    apply eventually_inf_principal.mp
    exact hb.bound.mono fun z hz ↦ by simpa only [Real.norm_of_nonneg (Real.exp_nonneg _)] using hz
  obtain ⟨T, hT⟩ := eventually_atTop.mp (eventually_comap.mp hfar)
  let Q := (Icc a b) ×ℂ (Icc (-T) T)
  have hQ : IsCompact Q :=
    equivRealProdCLM.toHomeomorph.isCompact_preimage.mpr (isCompact_Icc.prod isCompact_Icc)
  obtain ⟨N, hN⟩ := hQ.exists_bound_of_continuousOn
    (hc.mono (fun _ hz ↦ (mem_reProdIm.mp hz).1))
  have hA' : 0 ≤ max N A := hA.le.trans (le_max_right _ _)
  refine ⟨max N A, hA', fun z hz ↦ ?_⟩
  by_cases hzT : T ≤ |z.im|
  · exact (hT _ hzT z rfl hz).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_nonneg _))
  · exact (hN z (mem_reProdIm.mpr ⟨hz, abs_le.mp (not_le.mp hzT).le⟩)).trans
      ((le_max_left _ _).trans (le_mul_of_one_le_right hA' (Real.one_le_exp (by positivity))))

/-- Explicit polynomial bound inside a strip when both boundary constants
hold on their full lines. The constant in the interior depends only on the
boundary data, even if the exponential growth constant varies by function. -/
theorem holomorphic_poly_interpolate_exp_explicit {f : ℂ → ℂ} {a b k₁ k₂ K C₁ C₂ : ℝ}
    (hab : a < b) (hD : ∀ z : ℂ, z.re ∈ Icc a b → AnalyticAt ℂ f z) (hK : 0 ≤ K)
    (hB : f =O[Filter.comap (abs ∘ im) atTop ⊓ 𝓟 (re ⁻¹' Icc a b)]
      fun z : ℂ ↦ Real.exp (K * |z.im|))
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (_hk₁ : 0 ≤ k₁) (_hk₂ : 0 ≤ k₂)
    (hL : ∀ z : ℂ, z.re = a → ‖f z‖ ≤ C₁ * (1 + |z.im|) ^ k₁)
    (hR : ∀ z : ℂ, z.re = b → ‖f z‖ ≤ C₂ * (1 + |z.im|) ^ k₂) :
    ∀ z : ℂ, z.re ∈ Icc a b →
      ‖f z‖ ≤ max (C₁ * Real.exp (a ^ 2 + k₁ ^ 2 / 4))
        (C₂ * Real.exp (b ^ 2 + k₂ ^ 2 / 4)) *
          (1 + |z.im|) ^ ((1 - (z.re - a) / (b - a)) * k₁ +
            ((z.re - a) / (b - a)) * k₂) := by
  have hc : ContinuousOn f (re ⁻¹' Icc a b) := fun z hz ↦ (hD z hz).continuousAt.continuousWithinAt
  have hd : DiffContOnCl ℂ f (HadamardThreeLines.verticalStrip a b) := by
    refine ⟨fun z hz ↦ (hD z ⟨hz.1.le, hz.2.le⟩).differentiableAt.differentiableWithinAt, ?_⟩
    simpa only [HadamardThreeLines.verticalStrip, closure_preimage_re, closure_Ioo hab.ne] using hc
  obtain ⟨A, hA, hg⟩ := holomorphic_exponential_strip_bound hc hK hB
  exact polynomial_threeLines_of_exponential_growth_explicit hab hd hA hK hg
    hC₁ hC₂ hL hR

/-- The exponential three-lines estimate with all three growth hypotheses
given only at sufficiently large absolute height. -/
theorem holomorphic_poly_interpolate_exp {f : ℂ → ℂ} {a b k₁ k₂ K : ℝ} (hab : a < b)
    (hD : ∀ z : ℂ, z.re ∈ Icc a b → AnalyticAt ℂ f z) (hK : 0 ≤ K)
    (hB : f =O[Filter.comap (abs ∘ im) atTop ⊓ 𝓟 (re ⁻¹' Icc a b)]
      fun z : ℂ ↦ Real.exp (K * |z.im|))
    (hk₁ : 0 ≤ k₁) (hk₂ : 0 ≤ k₂)
    (h₁ : VerticalPolynomialBound f a k₁) (h₂ : VerticalPolynomialBound f b k₂) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, z.re ∈ Icc a b →
      ‖f z‖ ≤ C * (1 + |z.im|) ^ ((1 - (z.re - a) / (b - a)) * k₁ +
        ((z.re - a) / (b - a)) * k₂) := by
  have hc : ContinuousOn f (re ⁻¹' Icc a b) := fun z hz ↦ (hD z hz).continuousAt.continuousWithinAt
  obtain ⟨A₁, hA₁, hL⟩ := verticalPolynomialBound_extend_to_all
    (hc.mono (fun z hz ↦ by
      change z.re ∈ Icc a b
      rw [show z.re = a from hz]
      exact left_mem_Icc.mpr hab.le)) hk₁ h₁
  obtain ⟨A₂, hA₂, hR⟩ := verticalPolynomialBound_extend_to_all
    (hc.mono (fun z hz ↦ by
      change z.re ∈ Icc a b
      rw [show z.re = b from hz]
      exact right_mem_Icc.mpr hab.le)) hk₂ h₂
  exact ⟨_, le_trans (by positivity) (le_max_left _ _),
    holomorphic_poly_interpolate_exp_explicit hab hD hK hB hA₁ hA₂ hk₁ hk₂ hL hR⟩

private theorem holomorphic_poly_interpolate {f : ℂ → ℂ} {a b k₁ k₂ : ℝ} (hab : a < b)
    (hD : ∀ z : ℂ, z.re ∈ Icc a b → AnalyticAt ℂ f z)
    (hB : ∃ C T K : ℝ, 0 ≤ C ∧ 0 ≤ K ∧
      ∀ z : ℂ, z.re ∈ Icc a b → T ≤ |z.im| → ‖f z‖ ≤ C * (1 + |z.im|) ^ K)
    (hk₁ : 0 ≤ k₁) (hk₂ : 0 ≤ k₂)
    (h₁ : VerticalPolynomialBound f a k₁) (h₂ : VerticalPolynomialBound f b k₂) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, z.re ∈ Icc a b →
      ‖f z‖ ≤ C * (1 + |z.im|) ^ ((1 - (z.re - a) / (b - a)) * k₁ +
        ((z.re - a) / (b - a)) * k₂) := by
  have hc : ContinuousOn f (re ⁻¹' Icc a b) := fun z hz => (hD z hz).continuousAt.continuousWithinAt
  have hd : DiffContOnCl ℂ f (HadamardThreeLines.verticalStrip a b) := by
    refine ⟨fun z hz => (hD z ⟨hz.1.le, hz.2.le⟩).differentiableAt.differentiableWithinAt, ?_⟩
    simpa only [HadamardThreeLines.verticalStrip, closure_preimage_re, closure_Ioo hab.ne] using hc
  obtain ⟨C, T, K, hC, hK, h⟩ := hB
  obtain ⟨A, hA, hB'⟩ := verticalPoly_extend_to_all hc hK ⟨C, T, hC, h⟩
  obtain ⟨A₁, hA₁, hL⟩ := verticalPolynomialBound_extend_to_all
    (hc.mono (fun z hz => by
      change z.re ∈ Icc a b
      rw [show z.re = a from hz]
      exact left_mem_Icc.mpr hab.le)) hk₁ h₁
  obtain ⟨A₂, hA₂, hR⟩ := verticalPolynomialBound_extend_to_all
    (hc.mono (fun z hz => by
      change z.re ∈ Icc a b
      rw [show z.re = b from hz]
      exact right_mem_Icc.mpr hab.le)) hk₂ h₂
  exact polynomial_threeLines hab hd hA hK hB' hA₁ hA₂ hk₁ hk₂ hL hR

private def ordinate (x y : ℝ) : ℂ := (x : ℂ) + (y : ℂ) * I

@[simp] private theorem ordinate_re (x y : ℝ) : (ordinate x y).re = x := by simp [ordinate, mul_re]
@[simp] private theorem ordinate_im (x y : ℝ) : (ordinate x y).im = y := by simp [ordinate, mul_im]

private theorem verticalGrowth_convex_holomorphic {f : ℂ → ℂ} {a : ℝ}
    (hD : AnalyticOnNhd ℂ f (re ⁻¹' Ioi a))
    (hB : ∃ C T K : ℝ, 0 ≤ C ∧ 0 ≤ K ∧
      ∀ z : ℂ, a < z.re → T ≤ |z.im| → ‖f z‖ ≤ C * (1 + |z.im|) ^ K) :
    ConvexOn ℝ (Ioi a) (verticalGrowthExponent f) := by
  obtain ⟨C, T, K, hC, hK, h⟩ := hB
  have hnonempty (x : ℝ) (hx : a < x) :
      {k : ℝ | 0 ≤ k ∧ VerticalPolynomialBound f x k}.Nonempty := by
    refine ⟨K, hK, C, T, hC, fun y hy => ?_⟩
    have h₁ := h (ordinate x y) (by simpa only [ordinate_re] using hx)
      (by simpa only [ordinate_im] using hy)
    change ‖f (ordinate x y)‖ ≤ C * (1 + |y|) ^ K
    simpa only [ordinate_im] using h₁
  have hmu_nonneg (x : ℝ) (hx : a < x) : 0 ≤ verticalGrowthExponent f x :=
    le_csInf (hnonempty x hx) fun _ hk => hk.1
  have hineq (x y r s : ℝ) (hx : a < x) (hy : a < y) (hxy : x < y)
      (hr : 0 ≤ r) (hs : 0 ≤ s) (hrs : r + s = 1) :
      verticalGrowthExponent f (r * x + s * y) ≤
        r * verticalGrowthExponent f x + s * verticalGrowthExponent f y := by
    let w := r * x + s * y
    have hwi : w ∈ Icc x y := by
      have hl := mul_nonneg hs (sub_nonneg.mpr hxy.le)
      have hu := mul_nonneg hr (sub_nonneg.mpr hxy.le)
      change x ≤ r * x + s * y ∧ r * x + s * y ≤ y
      exact ⟨by nlinarith [congrArg (· * x) hrs], by nlinarith [congrArg (· * y) hrs]⟩
    have hw : a < w := hx.trans_le hwi.1
    apply le_of_forall_pos_le_add
    intro ε hε
    have hxε := verticalGrowth_bound_above_inf (hnonempty x hx) hε
    have hyε := verticalGrowth_bound_above_inf (hnonempty y hy) hε
    have h₁ : 0 ≤ verticalGrowthExponent f x + ε := add_nonneg (hmu_nonneg x hx) hε.le
    have h₂ : 0 ≤ verticalGrowthExponent f y + ε := add_nonneg (hmu_nonneg y hy) hε.le
    obtain ⟨M, hM, hb⟩ := holomorphic_poly_interpolate hxy
      (fun z hz => hD z (hx.trans_le hz.1))
      ⟨C, T, K, hC, hK, fun z hz => h z (hx.trans_le hz.1)⟩ h₁ h₂ hxε hyε
    have heq : (w - x) / (y - x) = s := by
      apply (div_eq_iff (sub_ne_zero.mpr hxy.ne')).mpr
      dsimp [w]
      nlinarith [congrArg (· * x) hrs]
    have heq' : 1 - s = r := by linarith
    have hk : r * (verticalGrowthExponent f x + ε) + s * (verticalGrowthExponent f y + ε) =
        r * verticalGrowthExponent f x + s * verticalGrowthExponent f y + ε := by nlinarith [congrArg (· * ε) hrs]
    apply csInf_le (verticalGrowth_bddBelow f w)
    refine ⟨hk ▸ add_nonneg (mul_nonneg hr h₁) (mul_nonneg hs h₂), M, 0, hM, fun t _ => ?_⟩
    have hh := hb (ordinate w t) (by simpa only [ordinate_re] using hwi)
    rw [ordinate_re, ordinate_im, heq, heq', hk] at hh
    exact hh
  refine ⟨convex_Ioi _, fun x hx y hy r s hr hs hrs => ?_⟩
  rcases lt_trichotomy x y with hxy | hxy | hyx
  · exact hineq x y r s hx hy hxy hr hs hrs
  · subst y
    simp only [smul_eq_mul, ← add_mul, hrs, one_mul, le_refl]
  · simpa only [smul_eq_mul, add_comm] using hineq y x s r hy hx hyx hs hr (by linarith)

private theorem verticalGrowth_uniform_holomorphic {f : ℂ → ℂ} {a : ℝ}
    (hD : AnalyticOnNhd ℂ f (re ⁻¹' Ioi a))
    (hB : ∃ C T K : ℝ, 0 ≤ C ∧ 0 ≤ K ∧
      ∀ z : ℂ, a < z.re → T ≤ |z.im| → ‖f z‖ ≤ C * (1 + |z.im|) ^ K)
    {l u ε : ℝ} (hl : a < l) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, z.re ∈ Icc l u →
      ‖f z‖ ≤ C * (1 + |z.im|) ^ (verticalGrowthExponent f z.re + ε) := by
  have hc := (verticalGrowth_convex_holomorphic hD hB).continuousOn isOpen_Ioi
  obtain ⟨C, T, K, hC, hK, h⟩ := hB
  have hn (x : ℝ) (hx : a < x) : {k : ℝ | 0 ≤ k ∧ VerticalPolynomialBound f x k}.Nonempty := by
    refine ⟨K, hK, C, T, hC, fun y hy => ?_⟩
    change ‖f (ordinate x y)‖ ≤ C * (1 + |y|) ^ K
    simpa only [ordinate_re, ordinate_im] using
      h (ordinate x y) (by simpa only [ordinate_re] using hx) (by simpa only [ordinate_im] using hy)
  have hm (x : ℝ) (hx : a < x) : 0 ≤ verticalGrowthExponent f x :=
    le_csInf (hn x hx) fun _ hK => hK.1
  have hlocal (x : Icc l u) :
      ∃ (d C' : ℝ), 0 < d ∧ 0 ≤ C' ∧ ∀ z : ℂ, z.re ∈ Icc (x.val - d) (x.val + d) →
        ‖f z‖ ≤ C' * (1 + |z.im|) ^ (verticalGrowthExponent f z.re + ε) := by
    have hx : a < (x : ℝ) := hl.trans_le x.2.1
    have hcx := (isOpen_Ioi.continuousOn_iff.mp hc) (show (x : ℝ) ∈ Ioi a from hx)
    obtain ⟨δ, hδ, hNear⟩ := Metric.continuousAt_iff.mp hcx (ε / 4) (by positivity)
    let d := min (δ / 2) ((x.val - a) / 2)
    have hd : 0 < d := lt_min (by positivity) (by linarith)
    have hleft : a < x.val - d := by
      have h := min_le_right (δ / 2) ((x.val - a) / 2)
      change d ≤ _ at h
      linarith
    have hdδ : d < δ := (min_le_left _ _).trans_lt (by linarith)
    have hh : x.val - d < x.val + d := by linarith
    have hclose (w : ℝ) (hw : w ∈ Icc (x.val - d) (x.val + d)) :
        |verticalGrowthExponent f w - verticalGrowthExponent f x.val| < ε / 4 := by
      apply hNear
      rw [Real.dist_eq]
      exact abs_lt.mpr ⟨by linarith [hw.1], by linarith [hw.2]⟩
    have h₁ := hclose _ ⟨le_rfl, hh.le⟩
    have h₂ := hclose _ ⟨hh.le, le_rfl⟩
    have hr : a < x.val + d := hleft.trans hh
    let k₁ := verticalGrowthExponent f (x.val - d) + ε / 4
    let k₂ := verticalGrowthExponent f (x.val + d) + ε / 4
    obtain ⟨M, hM, hbound⟩ := holomorphic_poly_interpolate hh
      (fun z hz => hD z (hleft.trans_le hz.1))
      ⟨C, T, K, hC, hK, fun z hz => h z (hleft.trans_le hz.1)⟩
      (add_nonneg (hm _ hleft) (by positivity)) (add_nonneg (hm _ hr) (by positivity))
      (verticalGrowth_bound_above_inf (hn _ hleft) (by positivity : 0 < ε / 4))
      (verticalGrowth_bound_above_inf (hn _ hr) (by positivity : 0 < ε / 4))
    refine ⟨d, M, hd, hM, fun z hz => (hbound z hz).trans ?_⟩
    apply mul_le_mul_of_nonneg_left _ hM
    apply Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg z.im])
    let s := (z.re - (x.val - d)) / ((x.val + d) - (x.val - d))
    have hs₀ : 0 ≤ s := div_nonneg (sub_nonneg.mpr hz.1) (sub_pos.mpr hh).le
    have hs₁ : s ≤ 1 := (div_le_one₀ (sub_pos.mpr hh)).mpr (sub_le_sub_right hz.2 _)
    have hzLower := (abs_lt.mp (hclose z.re hz)).1
    have h₁' : k₁ ≤ verticalGrowthExponent f z.re + ε := by
      dsimp only [k₁]
      linarith [(abs_lt.mp h₁).2]
    have h₂' : k₂ ≤ verticalGrowthExponent f z.re + ε := by
      dsimp only [k₂]
      linarith [(abs_lt.mp h₂).2]
    change (1 - s) * k₁ + s * k₂ ≤ _
    calc
      _ ≤ (1 - s) * (verticalGrowthExponent f z.re + ε) +
          s * (verticalGrowthExponent f z.re + ε) :=
        add_le_add (mul_le_mul_of_nonneg_left h₁' (sub_nonneg.mpr hs₁))
          (mul_le_mul_of_nonneg_left h₂' hs₀)
      _ = _ := by ring
  choose d M hd hM hbd using hlocal
  let V (x : Icc l u) := Ioo (x.val - d x) (x.val + d x)
  have cover : Icc l u ⊆ ⋃ x : Icc l u, V x := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, by
      change x - d ⟨x, hx⟩ < x ∧ x < x + d ⟨x, hx⟩
      exact ⟨sub_lt_self x (hd _), lt_add_of_pos_right _ (hd _)⟩⟩
  classical
  obtain ⟨s, hs⟩ := isCompact_Icc.elim_finite_subcover V (fun _ => isOpen_Ioo) cover
  refine ⟨∑ x ∈ s, M x, Finset.sum_nonneg fun x _ => hM x, fun z hz => ?_⟩
  obtain ⟨x, hx, hxV⟩ := mem_iUnion₂.mp (hs hz)
  exact (hbd x z (Ioo_subset_Icc_self hxV)).trans
    (mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun i _ => hM i) hx) (by positivity))

private def normalizedPoleFactor (P : Finset ℂ) (d : ℝ) (z : ℂ) : ℂ :=
  ∏ p ∈ P, (z - p) / (z - (d : ℂ))

private theorem poleFactor_analytic {P : Finset ℂ} {d : ℝ} {x : ℂ} (hx : x ≠ (d : ℂ)) :
    AnalyticAt ℂ (normalizedPoleFactor P d) x := by
  apply Finset.analyticAt_fun_prod
  intro p _
  exact (analyticAt_id.sub analyticAt_const).div (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr hx)

private theorem normalizedPoleFactor_nonneg_order {P : Finset ℂ} {d : ℝ} {x : ℂ}
    (hx : x ≠ (d : ℂ)) (hP : x ∈ P) :
    1 ≤ meromorphicOrderAt (normalizedPoleFactor P d) x := by
  classical
  have hF (p : ℂ) : AnalyticAt ℂ (fun z => (z - p) / (z - (d : ℂ))) x :=
    (analyticAt_id.sub analyticAt_const).div (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr hx)
  have hOne : meromorphicOrderAt (fun z : ℂ => (z - x) / (z - (d : ℂ))) x = 1 := by
    have hn : (x - (d : ℂ))⁻¹ ≠ 0 := inv_ne_zero (sub_ne_zero.mpr hx)
    have hi : AnalyticAt ℂ (fun z : ℂ => (z - (d : ℂ))⁻¹) x :=
      (analyticAt_id.sub analyticAt_const).inv (sub_ne_zero.mpr hx)
    rw [show (fun z : ℂ => (z - x) / (z - (d : ℂ))) =
      (fun z : ℂ => (z - (d : ℂ))⁻¹) * (fun z : ℂ => z - x) by
        funext z; simp [div_eq_mul_inv, mul_comm]]
    exact (meromorphicOrderAt_mul_of_ne_zero hi hn).trans meromorphicOrderAt_id_sub_const
  have he : meromorphicOrderAt (normalizedPoleFactor P d) x =
      ∑ p ∈ P, meromorphicOrderAt (fun z => (z - p) / (z - (d : ℂ))) x := by
    rw [show normalizedPoleFactor P d = ∏ p ∈ P, (fun z : ℂ => (z - p) / (z - (d : ℂ))) by
      funext z; simp [normalizedPoleFactor, Finset.prod_apply]]
    exact meromorphicOrderAt_prod (s := P) (fun p _ => (hF p).meromorphicAt)
  rw [he, ← Finset.sum_erase_add P _ hP, hOne]
  exact le_add_of_nonneg_left (Finset.sum_nonneg fun p _ => (hF p).meromorphicOrderAt_nonneg)

private theorem normalizedPoleFactor_bounded (P : Finset ℂ) (d : ℝ) :
    ∃ T : ℝ, 0 < T ∧ ∀ z : ℂ, T ≤ |z.im| →
      (1 / 2 : ℝ) ^ P.card ≤ ‖normalizedPoleFactor P d z‖ ∧
        ‖normalizedPoleFactor P d z‖ ≤ (3 / 2 : ℝ) ^ P.card ∧ z ∉ P := by
  let T := 1 + ∑ p ∈ P, (2 * ‖p - (d : ℂ)‖ + |p.im|)
  have hsum : 0 ≤ ∑ p ∈ P, (2 * ‖p - (d : ℂ)‖ + |p.im|) :=
    Finset.sum_nonneg fun p _ => by positivity
  have hT : 0 < T := by dsimp [T]; linarith
  refine ⟨T, hT, fun z hz => ?_⟩
  have hsize : |z.im| ≤ ‖z - (d : ℂ)‖ := by
    simpa only [sub_im, ofReal_im, sub_zero] using abs_im_le_norm (z - (d : ℂ))
  have hne : z - (d : ℂ) ≠ 0 := norm_pos_iff.mp (hT.trans_le (hz.trans hsize))
  have hsumle (p : ℂ) (hp : p ∈ P) :
      2 * ‖p - (d : ℂ)‖ + |p.im| ≤ ∑ p ∈ P, (2 * ‖p - (d : ℂ)‖ + |p.im|) :=
    Finset.single_le_sum (f := fun p : ℂ => 2 * ‖p - (d : ℂ)‖ + |p.im|)
      (fun p _ => by positivity) hp
  have hEach (p : ℂ) (hp : p ∈ P) :
      (1 / 2 : ℝ) ≤ ‖(z - p) / (z - (d : ℂ))‖ ∧ ‖(z - p) / (z - (d : ℂ))‖ ≤ 3 / 2 := by
    have hhalf : ‖(p - (d : ℂ)) / (z - (d : ℂ))‖ ≤ 1 / 2 := by
      rw [norm_div, div_le_iff₀ (norm_pos_iff.mpr hne)]
      dsimp [T] at hz
      linarith [hsumle p hp, abs_nonneg p.im]
    let w := (z - p) / (z - (d : ℂ))
    have hd : ‖w - 1‖ ≤ 1 / 2 := by
      have he : w - 1 = -((p - (d : ℂ)) / (z - (d : ℂ))) := by
        dsimp [w]
        field_simp [hne]
        ring
      rwa [he, norm_neg]
    have h₁ := norm_add_le (1 - w) w
    have h₂ := norm_add_le (w - 1) (1 : ℂ)
    rw [sub_add_cancel, norm_one, norm_sub_rev (1 : ℂ) w] at h₁
    rw [sub_add_cancel, norm_one] at h₂
    change (1 / 2 : ℝ) ≤ ‖w‖ ∧ ‖w‖ ≤ 3 / 2
    exact ⟨by linarith, by linarith⟩
  have hlo :
      (∏ _p ∈ P, (1 / 2 : ℝ)) ≤ ∏ p ∈ P, ‖(z - p) / (z - (d : ℂ))‖ :=
    Finset.prod_le_prod (fun _ _ => by positivity) (fun p hp => (hEach p hp).1)
  have hup :
      (∏ p ∈ P, ‖(z - p) / (z - (d : ℂ))‖) ≤ ∏ _p ∈ P, (3 / 2 : ℝ) :=
    Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun p hp => (hEach p hp).2)
  refine ⟨?_, ?_, fun hp => ?_⟩
  · simpa only [Finset.prod_const, normalizedPoleFactor, norm_prod] using hlo
  · simpa only [Finset.prod_const, normalizedPoleFactor, norm_prod] using hup
  · have h := hsumle z hp
    dsimp [T] at hz
    linarith [norm_nonneg (z - (d : ℂ))]

private theorem remove_simple_poles_of_meromorphic {f : ℂ → ℂ} {a : ℝ} {P : Finset ℂ}
    (hf : MeromorphicOn f (re ⁻¹' Ioi a))
    (hreg : ∀ z : ℂ, a < z.re → z ∉ P → AnalyticAt ℂ f z)
    (hp : ∀ z : ℂ, a < z.re → z ∈ P → (-1 : WithTop ℤ) ≤ meromorphicOrderAt f z) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (re ⁻¹' Ioi a) ∧
      ∃ L H T : ℝ, 0 < L ∧ 0 ≤ H ∧ ∀ z : ℂ, a < z.re → T ≤ |z.im| →
        L * ‖f z‖ ≤ ‖g z‖ ∧ ‖g z‖ ≤ H * ‖f z‖ := by
  classical
  let U := re ⁻¹' Ioi a
  let d := a - 1
  let p := normalizedPoleFactor P d
  let q := p * f
  have hne (z : ℂ) (hz : a < z.re) : z ≠ (d : ℂ) := by
    intro he
    have hr : z.re = d := by rw [he, ofReal_re]
    dsimp [d] at hr
    linarith
  have hpA (z : ℂ) (hz : a < z.re) : AnalyticAt ℂ p z :=
    poleFactor_analytic (hne z hz)
  have hq : MeromorphicOn q U := fun z hz => (hpA z hz).meromorphicAt.mul (hf z hz)
  let g := toMeromorphicNFOn q U
  refine ⟨g, fun z hz => ?_, ?_⟩
  · rw [show g = toMeromorphicNFOn q U from rfl]
    have he := toMeromorphicNFOn_eq_toMeromorphicNFAt_on_nhds hq hz
    apply (analyticAt_congr he).mpr
    apply ((hq z hz).meromorphicOrderAt_nonneg_iff_analyticAt_toMeromorphicNFAt).mp
    by_cases hy : z ∈ P
    · have h₁ := normalizedPoleFactor_nonneg_order (hne z hz) hy
      have h₂ := hp z hz hy
      rw [show q = p * f from rfl, meromorphicOrderAt_mul (hpA z hz).meromorphicAt (hf z hz)]
      have hl : (1 : WithTop ℤ) + (-1 : WithTop ℤ) ≤
          meromorphicOrderAt p z + meromorphicOrderAt f z := add_le_add h₁ h₂
      norm_num at hl ⊢
      exact hl
    · exact ((hpA z hz).mul (hreg z hz hy)).meromorphicOrderAt_nonneg
  · obtain ⟨T, _, hb⟩ := normalizedPoleFactor_bounded P d
    refine ⟨(1 / 2) ^ P.card, (3 / 2) ^ P.card, T, by positivity, by positivity, fun z hz ht => ?_⟩
    obtain ⟨hL, hH, hnot⟩ := hb z ht
    have hA := (hpA z hz).mul (hreg z hz hnot)
    have he : g z = p z * f z := by
      rw [show g = toMeromorphicNFOn q U from rfl, toMeromorphicNFOn_eq_toMeromorphicNFAt hq hz,
        toMeromorphicNFAt_eq_self.mpr hA.meromorphicNFAt]
      rfl
    rw [he, norm_mul]
    exact ⟨mul_le_mul_of_nonneg_right hL (norm_nonneg _),
      mul_le_mul_of_nonneg_right hH (norm_nonneg _)⟩

/-- Lemma B.1.1.1. Removing finitely many simple poles by a bounded
rational factor preserves the vertical growth exponent. The exponent is
convex and continuous, and the epsilon bound is uniform on closed substrips. -/
theorem meromorphic_verticalGrowth {f : ℂ → ℂ} {a : ℝ} {P : Finset ℂ}
    (hf : MeromorphicOn f (re ⁻¹' Ioi a))
    (hreg : ∀ z : ℂ, a < z.re → z ∉ P → AnalyticAt ℂ f z)
    (hp : ∀ z : ℂ, a < z.re → z ∈ P → (-1 : WithTop ℤ) ≤ meromorphicOrderAt f z)
    (hB : ∃ C T K : ℝ, 0 ≤ C ∧ 0 ≤ K ∧
      ∀ z : ℂ, a < z.re → T ≤ |z.im| → ‖f z‖ ≤ C * (1 + |z.im|) ^ K) :
    (∀ x ∈ Ioi a, 0 ≤ verticalGrowthExponent f x ∧
      ∃ K : ℝ, 0 ≤ K ∧ VerticalPolynomialBound f x K) ∧
    ConvexOn ℝ (Ioi a) (verticalGrowthExponent f) ∧
    ContinuousOn (verticalGrowthExponent f) (Ioi a) ∧
    ∀ l u ε : ℝ, a < l → l < u → 0 < ε →
      ∃ C T : ℝ, 0 ≤ C ∧ ∀ z : ℂ, z.re ∈ Icc l u → T ≤ |z.im| →
        ‖f z‖ ≤ C * (1 + |z.im|) ^ (verticalGrowthExponent f z.re + ε) := by
  obtain ⟨g, hg, L, H, T₀, hL, hH, hb⟩ := remove_simple_poles_of_meromorphic hf hreg hp
  obtain ⟨C, T, K, hC, hK, h⟩ := hB
  have hn (x : ℝ) (hx : a < x) : {k : ℝ | 0 ≤ k ∧ VerticalPolynomialBound f x k}.Nonempty := by
    refine ⟨K, hK, C, T, hC, fun y hy => ?_⟩
    change ‖f (ordinate x y)‖ ≤ C * (1 + |y|) ^ K
    simpa only [ordinate_im] using
      h (ordinate x y) (by simpa only [ordinate_re] using hx) (by simpa only [ordinate_im] using hy)
  have hpow (x : ℝ) (hx : a < x) (k : ℝ) :
      VerticalPolynomialBound f x k ↔ VerticalPolynomialBound g x k := by
    constructor
    · rintro ⟨A, T', hA, hF⟩
      refine ⟨H * A, max T₀ T', mul_nonneg hH hA, fun y hy => ?_⟩
      change ‖g (ordinate x y)‖ ≤ H * A * (1 + |y|) ^ k
      have hz : a < (ordinate x y).re := by simpa only [ordinate_re] using hx
      have hT : T₀ ≤ |(ordinate x y).im| := by
        simpa only [ordinate_im] using (le_max_left T₀ T').trans hy
      rw [mul_assoc]
      exact (hb _ hz hT).2.trans (mul_le_mul_of_nonneg_left (hF y ((le_max_right _ _).trans hy)) hH)
    · rintro ⟨A, T', hA, hG⟩
      refine ⟨A / L, max T₀ T', div_nonneg hA hL.le, fun y hy => ?_⟩
      change ‖f (ordinate x y)‖ ≤ A / L * (1 + |y|) ^ k
      have hz : a < (ordinate x y).re := by simpa only [ordinate_re] using hx
      have hT : T₀ ≤ |(ordinate x y).im| := by
        simpa only [ordinate_im] using (le_max_left T₀ T').trans hy
      rw [div_mul_eq_mul_div, le_div_iff₀ hL, mul_comm ‖f (ordinate x y)‖]
      exact (hb _ hz hT).1.trans (hG y ((le_max_right _ _).trans hy))
  have he (x : ℝ) (hx : a < x) : verticalGrowthExponent f x = verticalGrowthExponent g x := by
    unfold verticalGrowthExponent
    congr 1
    ext k
    simp only [mem_ofPred_eq, hpow x hx k]
  have hgB : ∃ C T K : ℝ, 0 ≤ C ∧ 0 ≤ K ∧
      ∀ z : ℂ, a < z.re → T ≤ |z.im| → ‖g z‖ ≤ C * (1 + |z.im|) ^ K := by
    refine ⟨H * C, max T₀ T, K, mul_nonneg hH hC, hK, fun z hz ht => ?_⟩
    rw [mul_assoc]
    exact (hb z hz ((le_max_left _ _).trans ht)).2.trans
      (mul_le_mul_of_nonneg_left (h z hz ((le_max_right _ _).trans ht)) hH)
  have hv : ConvexOn ℝ (Ioi a) (verticalGrowthExponent f) :=
    (verticalGrowth_convex_holomorphic hg hgB).congr (fun x hx => (he x hx).symm)
  refine ⟨fun x hx => ⟨le_csInf (hn x hx) (fun _ hk => hk.1), hn x hx⟩,
    hv, hv.continuousOn isOpen_Ioi, fun l u ε hl _ hε => ?_⟩
  obtain ⟨A, hA, hUniform⟩ := verticalGrowth_uniform_holomorphic hg hgB (u := u) hl hε
  refine ⟨A / L, T₀, div_nonneg hA hL.le, fun z hz ht => ?_⟩
  have hz' : a < z.re := hl.trans_le hz.1
  rw [he z.re hz', div_mul_eq_mul_div, le_div_iff₀ hL, mul_comm ‖f z‖]
  exact (hb z hz' ht).1.trans (hUniform z hz)

/-- The unnormalized pole factor does not raise the nonnegative growth
exponent by one when the original function decays along vertical lines. -/
theorem printed_pole_factor_exponent_shift_fails (x : ℝ) :
    let f : ℂ → ℂ := fun z => (z - 1)⁻¹
    let g : ℂ → ℂ := fun _ => 1
    (∀ z ≠ 1, g z = (z - 1) * f z) ∧
      verticalGrowthExponent f x = 0 ∧ verticalGrowthExponent g x = 0 := by
  dsimp only
  let f : ℂ → ℂ := fun z => (z - 1)⁻¹
  let g : ℂ → ℂ := fun _ => 1
  have nonneg (h : ℂ → ℂ) (hb : VerticalPolynomialBound h x 0) :
      verticalGrowthExponent h x = 0 := by
    have hmem : 0 ∈ {k : ℝ | 0 ≤ k ∧ VerticalPolynomialBound h x k} := ⟨le_rfl, hb⟩
    exact (csInf_le (verticalGrowth_bddBelow h x) hmem).antisymm
      (le_csInf ⟨0, hmem⟩ fun _ hi => hi.1)
  refine ⟨fun z hz => (mul_inv_cancel₀ (sub_ne_zero.mpr hz)).symm, nonneg f ?_, nonneg g ?_⟩
  · refine ⟨1, 1, zero_le_one, fun y hy => ?_⟩
    change ‖(ordinate x y - 1)⁻¹‖ ≤ 1 * (1 + |y|) ^ (0 : ℝ)
    have h := abs_im_le_norm (ordinate x y - 1)
    rw [sub_im, ordinate_im, one_im, sub_zero] at h
    rw [Real.rpow_zero, mul_one, norm_inv]
    exact inv_le_one_of_one_le₀ (hy.trans h)
  · exact ⟨1, 0, zero_le_one, fun _ _ => by simp [g]⟩

end

end Masullo
