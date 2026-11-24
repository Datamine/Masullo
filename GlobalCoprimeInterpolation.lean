import GlobalPrincipalValueShift
import SLocalPrimaryJetInterpolation
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-! The cardinal interpolation and strip estimates adapt the Apache-2.0
RiemannMasullo proof in Ch07_SchauderBasesZeta/Sec5.lean at 84e748f. -/

open Filter Function IsDedekindDomain Metric NumberField Set Topology
open scoped Classical NumberField

namespace Masullo

noncomputable section

private abbrev B := SchwartzBergman (univ : Set ℝ)

/-- Cardinal interpolation of summable values on the exponential lattice. The divided
difference of the exponential is one at zero and vanishes at the other lattice points.
Its imaginary translates are uniformly bounded on each vertical strip. -/
private theorem exists_exponentialLattice_cardinal (a : ℤ → ℂ) (ha : Summable fun n ↦ ‖a n‖) :
    ∃ A : ℂ → ℂ, Differentiable ℂ A ∧
      (∀ R : ℝ, ∃ C : ℝ, ∀ z : ℂ, |z.re| ≤ R → ‖A z‖ ≤ C) ∧
      ∀ n : ℤ, A (n * (2 * Real.pi * Complex.I)) = a n := by
  let K := dslope Complex.exp 0
  let p (n : ℤ) : ℂ := n * (2 * Real.pi * Complex.I)
  have hK : Differentiable ℂ K := differentiableOn_univ.mp
    ((Complex.differentiableOn_dslope (univ_mem : (univ : Set ℂ) ∈ 𝓝 0)).mpr
      Complex.differentiable_exp.differentiableOn)
  have hKr (R : ℝ) : ∃ C : ℝ, ∀ z : ℂ, |z.re| ≤ R → ‖K z‖ ≤ C := by
    obtain ⟨C, hC⟩ :=
      (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn hK.continuous.continuousOn
    refine ⟨max C (Real.exp R + 1), fun z hz ↦ ?_⟩
    by_cases h : ‖z‖ ≤ 1
    · exact (hC z (mem_closedBall_zero_iff.mpr h)).trans (le_max_left ..)
    · have hne : z ≠ 0 := fun he ↦ h (by simp [he])
      rw [show K z = (Complex.exp z - 1) / z by simp [K, dslope_of_ne _ hne, slope_def_field], norm_div]
      apply le_trans _ (le_max_right ..)
      apply (div_le_self (norm_nonneg _) (by linarith : 1 ≤ ‖z‖)).trans
      exact (norm_sub_le _ _).trans (by rw [Complex.norm_exp, norm_one]; gcongr; exact (le_abs_self _).trans hz)
  let F (n : ℤ) (z : ℂ) := a n * K (z - p n)
  have bound (R : ℝ) : ∃ u : ℤ → ℝ, Summable u ∧
      ∀ n (z : ℂ), |z.re| ≤ R → ‖F n z‖ ≤ u n := by
    obtain ⟨C, hC⟩ := hKr R
    refine ⟨_, ha.mul_right C, fun n z hz ↦ ?_⟩
    exact (norm_mul ..).le.trans (mul_le_mul_of_nonneg_left
      (hC (z - p n) (by simpa [p] using hz)) (norm_nonneg _))
  refine ⟨fun z ↦ ∑' n, F n z, fun z ↦ ?_, fun R ↦ ?_, fun n ↦ ?_⟩
  · let R := |z.re| + 1
    obtain ⟨u, hu, hbu⟩ := bound R
    have hopen : IsOpen {w : ℂ | |w.re| < R} :=
      isOpen_lt (continuous_abs.comp Complex.continuous_re) continuous_const
    exact (Complex.differentiableOn_tsum_of_summable_norm hu
      (fun n ↦ ((hK.comp (differentiable_id.sub_const (p n))).const_mul (a n)).differentiableOn)
      hopen (fun n w hw ↦ hbu n w (le_of_lt hw))).differentiableAt
        (hopen.mem_nhds (show |z.re| < R by dsimp [R]; linarith))
  · obtain ⟨u, hu, hbu⟩ := bound R
    exact ⟨∑' n, u n, fun z hz ↦ tsum_of_norm_bounded hu.hasSum (fun n ↦ hbu n z hz)⟩
  · change ∑' m, F m (p n) = _
    rw [tsum_eq_single n]
    · simp [F, K, dslope_same, Complex.deriv_exp]
    · intro m hm
      have hne : p n - p m ≠ 0 := by
        rw [show p n - p m = ((n : ℂ) - m) * (2 * Real.pi * Complex.I) by simp [p, sub_mul]]
        exact mul_ne_zero (sub_ne_zero.mpr (by exact_mod_cast hm.symm)) (by simp [Real.pi_ne_zero])
      simp [F, K, dslope_of_ne _ hne, slope_def_field, Complex.exp_sub, p,
        Complex.exp_int_mul_two_pi_mul_I]

/-- Interpolate the inverse of a function on a single Euler lattice. Dividing the samples
by a power of `1 - z` makes their norms summable. The cardinal series then gives a bounded
holomorphic interpolant on each strip, and restoring the power recovers the inverse. -/
private theorem exists_exponentialLattice_reciprocal (H : ℂ → ℂ)
    (hne : ∀ z : ℂ, z.re = 0 → H z ≠ 0)
    (hbound : ∃ (k : ℕ) (C T : ℝ), ∀ z : ℂ, z.re = 0 → T ≤ |z.im| →
      ‖(H z)⁻¹‖ ≤ C * |z.im| ^ k) (c : ℂ) (hc : ‖c‖ = 1) (l : ℝ) (hl : 0 < l) :
    ∃ (k : ℕ) (u : ℂ → ℂ), Differentiable ℂ u ∧
      (∀ R : ℝ, ∃ C : ℝ, ∀ z : ℂ, |z.re| ≤ R → ‖u z‖ ≤ C) ∧
      ∀ z : ℂ, c * Complex.exp (-(l : ℂ) * z) = 1 → H z * (1 - z) ^ k * u z = 1 := by
  obtain ⟨k, C, T, hC⟩ := hbound
  let w (z : ℂ) := Complex.log c - (l : ℂ) * z
  let d := -(2 * Real.pi) / l
  let b := -c.arg / (2 * Real.pi)
  let t (n : ℤ) := d * ((n : ℝ) + b)
  let s (n : ℤ) : ℂ := ⟨0, t n⟩
  have hd : d ≠ 0 := div_ne_zero (neg_ne_zero.mpr Real.two_pi_pos.ne') hl.ne'
  have hw (n : ℤ) : w (s n) = n * (2 * Real.pi * Complex.I) := by
    apply Complex.ext
    · simp [w, s, Complex.log_re, hc]
    · simp [w, s, t, d, b, Complex.log_im, Complex.mul_im]
      field_simp
      ring
  let a (n : ℤ) := (H (s n))⁻¹ / (1 - s n) ^ (k + 2)
  have ha : Summable fun n ↦ ‖a n‖ := by
    have hs := (Real.summable_one_div_int_add_rpow b 2).2 (by norm_num)
    simp only [Real.rpow_two] at hs
    apply (hs.mul_left (C / |d| ^ 2)).of_norm_bounded_eventually
    have hlim : Filter.Tendsto (fun n : ℤ ↦ |(n : ℝ)|) Filter.cofinite Filter.atTop :=
      tendsto_norm_cocompact_atTop.comp Int.tendsto_coe_cofinite
    filter_upwards [hlim.eventually_gt_atTop (|b| + (max T 1) / |d|)] with n hn
    have htd : max T 1 < |t n| := by
      rw [show |t n| = |((n : ℝ) + b)| * |d| by rw [mul_comm]; exact abs_mul ..]
      apply (div_lt_iff₀ (abs_pos.mpr hd)).mp
      have h := abs_sub ((n : ℝ) + b) b
      rw [add_sub_cancel_right] at h
      linarith
    have ht := (le_max_left T 1).trans htd.le
    have hpos : 0 < |t n| := zero_lt_one.trans ((le_max_right ..).trans_lt htd)
    have hnorm : |t n| ≤ ‖1 - s n‖ := by simpa [s] using Complex.abs_im_le_norm (1 - s n)
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    change ‖(H (s n))⁻¹ / (1 - s n) ^ (k + 2)‖ ≤ _
    rw [norm_div, norm_pow]
    calc
      _ ≤ (C * |t n| ^ k) / |t n| ^ (k + 2) :=
        (div_le_div_of_nonneg_left (norm_nonneg _) (pow_pos hpos _)
          (pow_le_pow_left₀ hpos.le hnorm _)).trans
            (div_le_div_of_nonneg_right (hC (s n) rfl ht) (pow_nonneg hpos.le _))
      _ = (C / |d| ^ 2) * (1 / |(n : ℝ) + b| ^ 2) := by
        rw [pow_add, mul_comm (|t n| ^ k), mul_div_mul_right _ _ (pow_ne_zero k hpos.ne')]
        simp [t, abs_mul, mul_pow, div_eq_mul_inv, mul_left_comm, mul_comm]
  obtain ⟨A, hA, hstrip, hval⟩ := exists_exponentialLattice_cardinal a ha
  have hlog : (Complex.log c).re = 0 := by rw [Complex.log_re, hc, Real.log_one]
  refine ⟨k + 2, A ∘ w, hA.comp ((differentiable_const _).sub (differentiable_id.const_mul _)),
    fun R ↦ ?_, fun z hz ↦ ?_⟩
  · obtain ⟨C, hC⟩ := hstrip (l * R)
    refine ⟨C, fun z hz ↦ hC _ ?_⟩
    simpa [w, Complex.mul_re, hlog, abs_mul, abs_of_pos hl] using mul_le_mul_of_nonneg_left hz hl.le
  · have hexp : Complex.exp (w z) = 1 := by
      simpa [w, sub_eq_add_neg, Complex.exp_add,
        Complex.exp_log (norm_ne_zero_iff.mp (hc.trans_ne one_ne_zero))] using hz
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hexp
    have hzinj : Injective w := fun _ _ h ↦
      mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hl.ne') (sub_right_injective h)
    have hzs := hzinj (hn.trans (hw n).symm)
    rw [hzs, Function.comp_apply, hw, hval]
    have h₁ : (1 : ℂ) - s n ≠ 0 := by intro e; have := congrArg Complex.re e; simp [s] at this
    dsimp only [a]
    field_simp [hne (s n) rfl, h₁]

/-- The entire interpolating multiplier preserves rapid decay on each vertical strip.
Above the height threshold its polynomial growth is absorbed by a higher Schwartz weight.
The remaining rectangle is compact. -/
private theorem schwartzBergman_mul_polynomial_strip (H u : ℂ → ℂ)
    (hH : Differentiable ℂ H) (hu : Differentiable ℂ u) (k : ℕ)
    (hpoly : ∀ R : ℝ, ∃ (m : ℕ) (T : ℝ), ∀ z : ℂ, |z.re| ≤ R → T ≤ |z.im| →
      ‖H z‖ ≤ ‖z‖ ^ m) (hb : ∀ R : ℝ, ∃ C : ℝ, ∀ z : ℂ, |z.re| ≤ R → ‖u z‖ ≤ C)
    (φ : B) : (fun z ↦ H z * (1 - z) ^ k * u z * φ.val z) ∈ schwartzBergmanSubmodule univ := by
  let f (z : ℂ) := H z * (1 - z) ^ k * u z * φ.val z
  have hφ : Differentiable ℂ φ.val := differentiableOn_univ.mp (by simpa using φ.property.2.1)
  have hf : Differentiable ℂ f := ((hH.mul ((differentiable_id.const_sub 1).pow k)).mul hu).mul hφ
  refine ⟨fun z hz ↦ (hz (mem_univ _)).elim, hf.differentiableOn, fun a b hab hI N ↦ ?_⟩
  let R := |a| + |b|
  obtain ⟨m, T, hT⟩ := hpoly R
  obtain ⟨C, hC⟩ := hb R
  obtain ⟨Bφ, hBφ⟩ := φ.property.2.2 a b hab hI (N + m + 2 * k)
  obtain ⟨B₀, hB₀⟩ := (isCompact_closedBall (0 : ℂ) (R + max T 3)).exists_bound_of_continuousOn
    (((continuous_id.pow N).mul hf.continuous).continuousOn)
  refine ⟨max B₀ (max C 0 * Bφ), ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  change ‖z ^ N * f z‖ ≤ _
  have hre : |z.re| ≤ R := by
    apply abs_le.mpr
    dsimp [R]
    constructor <;> linarith [hz.1, hz.2, neg_abs_le a, le_abs_self b, abs_nonneg a, abs_nonneg b]
  by_cases ht : max T 3 ≤ |z.im|
  · have hn : 3 ≤ ‖z‖ := ((le_max_right _ _).trans ht).trans (Complex.abs_im_le_norm z)
    have h₁ : ‖1 - z‖ ≤ ‖z‖ ^ 2 := (norm_sub_le ..).trans (by rw [norm_one]; nlinarith)
    have h₂ : ‖z ^ (N + m + 2 * k) * φ.val z‖ ≤ Bφ := hBφ ⟨z, hz, rfl⟩
    apply le_trans _ (le_max_right ..)
    calc
      ‖z ^ N * f z‖ = ‖u z‖ * (‖z‖ ^ N * ‖H z‖ * ‖1 - z‖ ^ k * ‖φ.val z‖) := by
        simp only [f, norm_mul, norm_pow]; ring
      _ ≤ max C 0 * (‖z‖ ^ N * ‖z‖ ^ m * (‖z‖ ^ 2) ^ k * ‖φ.val z‖) := by
        gcongr
        · exact (hC z hre).trans (le_max_left ..)
        · exact hT z hre ((le_max_left ..).trans ht)
      _ = max C 0 * ‖z ^ (N + m + 2 * k) * φ.val z‖ := by rw [norm_mul, norm_pow, pow_add, pow_add, pow_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left h₂ (le_max_right ..)
  · exact (hB₀ z (mem_closedBall_zero_iff.mpr ((Complex.norm_le_abs_re_add_abs_im z).trans
      (add_le_add hre (le_of_not_ge ht))))).trans (le_max_left ..)

variable (F : Type*) [Field F] [NumberField F]
private abbrev Place := HeightOneSpectrum (𝓞 F)
variable (ξ : PontryaginDual (IdeleClass F))
private abbrev E := finiteHeckeOmissionMultiplier F ξ
private abbrev c (v : Place F) := heckeEulerCoefficient F ξ (chosenFiniteUniformizer F) v
private abbrev l (v : Place F) := Real.log (v.asIdeal.absNorm : ℝ)

private theorem logNorm_pos (v : Place F) : 0 < l F v :=
  Real.log_pos (by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v)

theorem euler_singleton_exp (v : Place F) (z : ℂ) :
    E F ξ {v} z = 1 - c F ξ v * Complex.exp (-(l F v : ℂ) * z) := by
  have hq : (v.asIdeal.absNorm : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr
    (zero_lt_one.trans (HeightOneSpectrum.one_lt_absNorm v)).ne'
  unfold E finiteHeckeOmissionMultiplier
  rw [Finset.prod_singleton]
  change 1 - c F ξ v * (v.asIdeal.absNorm : ℂ) ^ (-z) = _
  rw [Complex.cpow_def_of_ne_zero hq, ← Complex.ofReal_natCast,
    Complex.ofReal_log (Nat.cast_nonneg _), mul_neg, neg_mul]

private theorem euler_singleton_divide (v : Place F) (hc : c F ξ v ≠ 0) (f : B)
    (hf : ∀ z, E F ξ {v} z = 0 → f.val z = 0) :
    ∃ b : B, ∀ z, f.val z = E F ξ {v} z * b.val z := by
  let D := E F ξ {v}
  have hd : Differentiable ℂ D := fun z ↦ (finiteHeckeOmissionMultiplier_analytic F ξ {v} z).differentiableAt
  have hfd : Differentiable ℂ f.val := by
    simpa only [preimage_univ, differentiableOn_univ] using f.property.2.1
  have hD : D = fun z ↦ 1 - c F ξ v * Complex.exp (-(l F v : ℂ) * z) :=
    funext (euler_singleton_exp F ξ v)
  obtain ⟨q, hq, he⟩ := (entire_divisibility_iff_orders hd hfd).mpr (by
    intro z
    by_cases hz : D z = 0
    · have hder : deriv D z ≠ 0 := by
        rw [hD]
        apply ((((hasDerivAt_id z).const_mul (-(l F v : ℂ))).cexp.const_mul (c F ξ v)).const_sub
          1).deriv.trans_ne
        have hn : (l F v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (logNorm_pos F v).ne'
        have hl : Complex.log (v.asIdeal.absNorm : ℂ) ≠ 0 := by
          rw [← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg _)]
          exact hn
        simp [hc, hl]
      rw [(hd.analyticAt z).analyticOrderAt_eq_one_of_zero_deriv_ne_zero hz hder]
      exact Order.one_le_iff_ne_zero.mpr ((hfd.analyticAt z).analyticOrderAt_ne_zero.mpr (hf z hz))
    · rw [(hd.analyticAt z).analyticOrderAt_eq_zero.mpr hz]
      exact bot_le)
  have hB : q ∈ schwartzBergmanSubmodule univ :=
    schwartzBergman_of_finiteHeckeOmission_mul F ξ {v} hq ((funext he) ▸ f.property)
  exact ⟨⟨q, hB⟩, he⟩

/-- A Hecke divisor with a normalized entire multiplier that has polynomial
strip growth and a polynomial reciprocal bound on the zero line is
comaximal with every finite reciprocal Euler divisor in Schwartz–Bergman
space. Each division is applied to the preceding quotient, with repeated
zeros retained. -/
theorem euler_divisor_bezout_of_normalization
    {g A : ℂ → ℂ} (hg : Differentiable ℂ g) (hA : Differentiable ℂ A)
    (hne : ∀ z : ℂ, z.re = 0 → g z * A z ≠ 0)
    (hpoly : ∀ R : ℝ, ∃ (m : ℕ) (T : ℝ), ∀ z : ℂ, |z.re| ≤ R → T ≤ |z.im| →
      ‖g z * A z‖ ≤ ‖z‖ ^ m)
    (hinv : ∃ (k : ℕ) (C T : ℝ), ∀ z : ℂ, z.re = 0 → T ≤ |z.im| →
      ‖(g z * A z)⁻¹‖ ≤ C * |z.im| ^ k)
    (W : Finset (Place F)) (f : B) :
    ∃ b : B, ∃ u : ℂ → ℂ, Differentiable ℂ u ∧
      ∀ z, f.val z = g z * u z + E F ξ W z * b.val z := by
  let H : ℂ → ℂ := fun z ↦ g z * A z
  have hH : Differentiable ℂ H := hg.mul hA
  induction W using Finset.induction_on generalizing f with
  | empty => exact ⟨f, 0, differentiable_const _, by simp [finiteHeckeOmissionMultiplier]⟩
  | @insert v W hv ih =>
    let D := E F ξ {v}
    have hD (z : ℂ) : E F ξ (insert v W) z = D z * E F ξ W z := by
      unfold D E finiteHeckeOmissionMultiplier
      rw [Finset.prod_insert hv, Finset.prod_singleton]
    by_cases hc : unramifiedFiniteCharacter F ξ v
    swap
    · have hd (z : ℂ) : D z = 1 := by
        simp [D, finiteHeckeOmissionMultiplier, heckeEulerCoefficient, hc]
      obtain ⟨b, u, hu, he⟩ := ih f
      exact ⟨b, u, hu, fun z ↦ by simpa only [hD, hd, one_mul] using he z⟩
    have hcn : ‖c F ξ v‖ = 1 := by
      simp only [c, heckeEulerCoefficient, ite_eq_left hc, Circle.norm_coe]
    obtain ⟨k, u, hu, hstrip, hmatch⟩ := exists_exponentialLattice_reciprocal H hne hinv
      (c F ξ v) hcn (l F v) (logNorm_pos F v)
    let w : B := ⟨_, schwartzBergman_mul_polynomial_strip H u hH hu k hpoly hstrip f⟩
    have hm (z : ℂ) (hz : D z = 0) : w.val z = f.val z := by
      change E F ξ {v} z = 0 at hz
      rw [euler_singleton_exp F ξ v z, sub_eq_zero] at hz
      exact (congrArg (· * f.val z) (hmatch z hz.symm)).trans (one_mul _)
    have hc₀ : c F ξ v ≠ 0 := norm_ne_zero_iff.mp (hcn.trans_ne one_ne_zero)
    obtain ⟨d, hd⟩ := euler_singleton_divide F ξ v hc₀ (f - w)
      (fun z hz ↦ sub_eq_zero.mpr (hm z hz).symm)
    obtain ⟨b, q, hq, hbe⟩ := ih d
    have hdD : Differentiable ℂ D := fun z ↦
      (finiteHeckeOmissionMultiplier_analytic F ξ {v} z).differentiableAt
    have hfD : Differentiable ℂ f.val := by
      simpa only [preimage_univ, differentiableOn_univ] using f.property.2.1
    let a (z : ℂ) := A z * (1 - z)^k * u z * f.val z
    have ha : Differentiable ℂ a :=
      ((hA.mul ((differentiable_id.const_sub 1).pow k)).mul hu).mul hfD
    refine ⟨b, fun z ↦ a z + D z * q z, ha.add (hdD.mul hq), fun z ↦ ?_⟩
    have he : f.val z - w.val z = D z * d.val z := hd z
    rw [hbe z] at he
    have hw : w.val z = g z * a z := by
      change (g z * A z) * (1 - z)^k * u z * f.val z = _
      dsimp only [a]
      ring
    rw [hw] at he
    rw [hD]
    linear_combination he

#print axioms euler_divisor_bezout_of_normalization

end

end Masullo
