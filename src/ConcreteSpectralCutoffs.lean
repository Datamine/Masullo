import RealPlaceRepair
import SpectralLimit
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.ContDiff.Deriv

open Filter Function MeasureTheory Set Topology
open scoped ContDiff FourierTransform

namespace Masullo

noncomputable section

private def transitionC (x : ℝ) : ℂ := Real.smoothTransition x

private theorem transitionC_smooth : ContDiff ℝ ∞ transitionC :=
  Complex.ofRealCLM.contDiff.comp Real.smoothTransition.contDiff

private theorem transitionC_norm_le (x : ℝ) : ‖transitionC x‖ ≤ 1 := by
  change ‖(Real.smoothTransition x : ℂ)‖ ≤ 1
  rw [Complex.norm_real, Real.norm_of_nonneg (Real.smoothTransition.nonneg _)]
  exact Real.smoothTransition.le_one _

private theorem transitionC_derivative_zero_outside {k : ℕ} (hk : 0 < k) {x : ℝ}
    (hx : x ∉ Icc (0 : ℝ) 1) : iteratedDeriv k transitionC x = 0 := by
  have hs : x < 0 ∨ 1 < x := by
    simp only [mem_Icc, not_and_or, not_le] at hx
    exact hx
  rcases hs with h | h
  · have he : transitionC =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds h] with y hy
      simp [transitionC, Real.smoothTransition.zero_of_nonpos (le_of_lt hy)]
    rw [he.iteratedDeriv_eq k]
    cases k <;> simp_all [iteratedDeriv_const]
  · have he : transitionC =ᶠ[𝓝 x] fun _ => 1 := by
      filter_upwards [Ioi_mem_nhds h] with y hy
      simp [transitionC, Real.smoothTransition.one_of_one_le (le_of_lt hy)]
    rw [he.iteratedDeriv_eq k]
    cases k <;> simp_all [iteratedDeriv_const]

private theorem transitionC_has_uniform_derivative_bounds :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : ℝ,
      ‖iteratedDeriv 1 transitionC x‖ ≤ K ∧ ‖iteratedDeriv 2 transitionC x‖ ≤ K := by
  have hex (k : ℕ) (hk : 0 < k) : ∃ C ≥ 0, ∀ x, ‖iteratedDeriv k transitionC x‖ ≤ C := by
    have hcont := transitionC_smooth.continuous_iteratedDeriv k (mod_cast le_top)
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
      (s := Icc (0 : ℝ) 1) hcont.continuousOn
    refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
    by_cases hx : x ∈ Icc (0 : ℝ) 1
    · exact (hC x hx).trans (le_max_left _ _)
    · rw [transitionC_derivative_zero_outside hk hx, norm_zero]
      exact le_max_right _ _
  obtain ⟨C, hC, hc⟩ := hex 1 (by decide)
  obtain ⟨D, _, hd⟩ := hex 2 (by decide)
  exact ⟨max C D, hC.trans (le_max_left _ _), fun x =>
    ⟨(hc x).trans (le_max_left _ _), (hd x).trans (le_max_right _ _)⟩⟩

private theorem transitionC_affine_iteratedDeriv (k : ℕ) (a b : ℝ) (x : ℝ) :
    iteratedDeriv k (fun t : ℝ => transitionC (a * t + b)) x =
      a ^ k • iteratedDeriv k transitionC (a * x + b) := by
  let f (t : ℝ) := transitionC (t + b)
  have hf : ContDiff ℝ k f := (transitionC_smooth.comp (by fun_prop)).of_le (mod_cast le_top)
  change iteratedDeriv k (fun t : ℝ => f (a * t)) x = _
  rw [iteratedDeriv_comp_const_smul hf, show iteratedDeriv k f = _ from
    iteratedDeriv_comp_add_const k transitionC b]

private def cutoffScale (n : ℕ) : ℝ := (n : ℝ) + 1

private theorem cutoffScale_pos (n : ℕ) : 0 < cutoffScale n := by
  unfold cutoffScale
  positivity

private def lowerCutoff (n : ℕ) (x : ℝ) : ℂ := transitionC (cutoffScale n * x - 1)

private def upperCutoff (n : ℕ) (x : ℝ) : ℂ := transitionC (cutoffScale n - x)

private theorem lowerCutoff_smooth (n : ℕ) : ContDiff ℝ ∞ (lowerCutoff n) :=
  transitionC_smooth.comp (by fun_prop)

private theorem upperCutoff_smooth (n : ℕ) : ContDiff ℝ ∞ (upperCutoff n) :=
  transitionC_smooth.comp (by fun_prop)

private theorem cutoff_factorization (n : ℕ) (g : ℝ → ℂ) :
    (fun x => (realPlaceCutoff n x : ℂ) * g x) =
      lowerCutoff n * (upperCutoff n * g) := by
  funext x
  simp [realPlaceCutoff, lowerCutoff, upperCutoff, cutoffScale, transitionC, mul_assoc]

private theorem lowerCutoff_iteratedDeriv_eq (k n : ℕ) (x : ℝ) :
    iteratedDeriv k (lowerCutoff n) x =
      cutoffScale n ^ k • iteratedDeriv k transitionC (cutoffScale n * x - 1) := by
  change iteratedDeriv k (fun t => transitionC (cutoffScale n * t - 1)) x = _
  simpa only [sub_eq_add_neg] using transitionC_affine_iteratedDeriv k (cutoffScale n) (-1) x

private theorem upperCutoff_iteratedDeriv_eq (k n : ℕ) (x : ℝ) :
    iteratedDeriv k (upperCutoff n) x =
      (-1 : ℝ) ^ k • iteratedDeriv k transitionC (cutoffScale n - x) := by
  change iteratedDeriv k (fun t => transitionC (cutoffScale n - t)) x = _
  simpa only [neg_mul, one_mul, sub_eq_add_neg, add_comm] using
    transitionC_affine_iteratedDeriv k (-1) (cutoffScale n) x

private def lowerTransitionInterval (n : ℕ) : Set ℝ :=
  Icc (1 / cutoffScale n) (2 / cutoffScale n)

private theorem lowerTransitionInterval_iff (n : ℕ) (x : ℝ) :
    x ∈ lowerTransitionInterval n ↔ cutoffScale n * x - 1 ∈ Icc (0 : ℝ) 1 := by
  unfold lowerTransitionInterval
  simp only [mem_Icc, div_le_iff₀ (cutoffScale_pos n), le_div_iff₀ (cutoffScale_pos n)]
  constructor <;> rintro ⟨hl, hu⟩ <;> constructor <;> linarith [mul_comm (cutoffScale n) x]

private theorem lowerCutoff_derivative_bound {K : ℝ}
    (hK : ∀ x, ‖iteratedDeriv 1 transitionC x‖ ≤ K ∧ ‖iteratedDeriv 2 transitionC x‖ ≤ K)
    (n : ℕ) (x : ℝ) (k : ℕ) (hk : k = 1 ∨ k = 2) :
    ‖iteratedDeriv k (lowerCutoff n) x‖ ≤
      (lowerTransitionInterval n).indicator (fun _ => cutoffScale n ^ k * K) x := by
  rw [lowerCutoff_iteratedDeriv_eq]
  by_cases hx : x ∈ lowerTransitionInterval n
  · rw [indicator_of_mem hx, norm_smul, Real.norm_of_nonneg (pow_nonneg (cutoffScale_pos n).le _)]
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg (cutoffScale_pos n).le _)
    rcases hk with rfl | rfl
    · exact (hK _).1
    · exact (hK _).2
  · have ht : cutoffScale n * x - 1 ∉ Icc (0 : ℝ) 1 :=
      fun h => hx ((lowerTransitionInterval_iff n x).mpr h)
    rw [transitionC_derivative_zero_outside (by omega) ht, smul_zero, norm_zero, indicator_of_notMem hx]

private theorem upperCutoff_derivative_bound {K : ℝ}
    (hK : ∀ x, ‖iteratedDeriv 1 transitionC x‖ ≤ K ∧ ‖iteratedDeriv 2 transitionC x‖ ≤ K)
    (n : ℕ) (x : ℝ) (k : ℕ) (hk : k = 1 ∨ k = 2) :
    ‖iteratedDeriv k (upperCutoff n) x‖ ≤ K := by
  rw [upperCutoff_iteratedDeriv_eq, norm_smul, norm_pow]
  norm_num
  rcases hk with rfl | rfl
  · exact (hK _).1
  · exact (hK _).2

/-- The cutoff profile and its first two derivatives are integrable. -/
theorem realPlaceCutoff_profile_integrable (n : ℕ) {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g) :
    let p := fun x => (realPlaceCutoff n x : ℂ) * g x
    Integrable p ∧ Integrable (deriv p) ∧ Integrable (deriv (deriv p)) ∧
      Differentiable ℝ p ∧ Differentiable ℝ (deriv p) := by
  let p := fun x => (realPlaceCutoff n x : ℂ) * g x
  have hp : ContDiff ℝ ∞ p :=
    (Complex.ofRealCLM.contDiff.comp (realPlaceCutoff_smooth n)).mul hg
  have hC : HasCompactSupport p := by
    refine HasCompactSupport.intro isCompact_Icc (K := Icc (cutoffScale n)⁻¹ (cutoffScale n)) ?_
    intro x hx
    have hz := notMem_support.mp fun h => hx (realPlaceCutoff_support n (subset_tsupport _ h))
    simp [p, hz]
  have hp' : ContDiff ℝ ∞ (deriv p) := by simpa using ContDiff.iterate_deriv 1 hp
  have hp'' : Continuous (deriv (deriv p)) := hp'.continuous_deriv (by simp)
  exact ⟨hp.continuous.integrable_of_hasCompactSupport hC,
    hp'.continuous.integrable_of_hasCompactSupport hC.deriv,
    hp''.integrable_of_hasCompactSupport hC.deriv.deriv,
    hp.differentiable (by simp), hp'.differentiable (by simp)⟩

private theorem cutoff_product_second (g h : ℝ → ℂ) (hg : ContDiff ℝ ∞ g) (hh : ContDiff ℝ ∞ h)
    (x : ℝ) :
    iteratedDeriv 2 (g * h) x =
      g x * iteratedDeriv 2 h x + 2 * (iteratedDeriv 1 g x * iteratedDeriv 1 h x) +
      iteratedDeriv 2 g x * h x := by
  have hg₂ : ContDiff ℝ (2 : ℕ) g := hg.of_le (by decide)
  have hh₂ : ContDiff ℝ (2 : ℕ) h := hh.of_le (by decide)
  rw [iteratedDeriv_mul hg₂.contDiffAt hh₂.contDiffAt]
  simp [Finset.sum_range_succ, Nat.choose, iteratedDeriv_zero, mul_assoc]

private theorem cutoff_product_first (g h : ℝ → ℂ) (hg : ContDiff ℝ ∞ g) (hh : ContDiff ℝ ∞ h)
    (x : ℝ) :
    iteratedDeriv 1 (g * h) x = g x * iteratedDeriv 1 h x + iteratedDeriv 1 g x * h x := by
  rw [iteratedDeriv_one, deriv_mul (hg.differentiable (by simp) x)
    (hh.differentiable (by simp) x)]
  rw [iteratedDeriv_one, iteratedDeriv_one, add_comm]

private theorem norm_cutoff_product_second_le (g h : ℝ → ℂ)
    (hg : ContDiff ℝ ∞ g) (hh : ContDiff ℝ ∞ h) (x : ℝ) :
    ‖iteratedDeriv 2 (g * h) x‖ ≤
      ‖g x‖ * ‖iteratedDeriv 2 h x‖ +
      2 * (‖iteratedDeriv 1 g x‖ * ‖iteratedDeriv 1 h x‖) +
      ‖iteratedDeriv 2 g x‖ * ‖h x‖ := by
  rw [cutoff_product_second g h hg hh]
  have hab := norm_add_le (g x * iteratedDeriv 2 h x)
    (2 * (iteratedDeriv 1 g x * iteratedDeriv 1 h x))
  have h := norm_add_le
    (g x * iteratedDeriv 2 h x + 2 * (iteratedDeriv 1 g x * iteratedDeriv 1 h x))
    (iteratedDeriv 2 g x * h x)
  refine (h.trans (add_le_add hab (le_refl _))).trans_eq ?_
  simp only [norm_mul, Complex.norm_ofNat]

private theorem norm_cutoff_product_first_le (g h : ℝ → ℂ)
    (hg : ContDiff ℝ ∞ g) (hh : ContDiff ℝ ∞ h) (x : ℝ) :
    ‖iteratedDeriv 1 (g * h) x‖ ≤
      ‖g x‖ * ‖iteratedDeriv 1 h x‖ + ‖iteratedDeriv 1 g x‖ * ‖h x‖ := by
  rw [cutoff_product_first g h hg hh]
  simpa only [norm_mul] using norm_add_le
    (g x * iteratedDeriv 1 h x) (iteratedDeriv 1 g x * h x)

private theorem lowerTransitionInterval_measure (n : ℕ) :
    volume.real (lowerTransitionInterval n) = 1 / cutoffScale n := by
  unfold lowerTransitionInterval
  rw [Real.volume_real_Icc_of_le (div_le_div_of_nonneg_right (by norm_num) (cutoffScale_pos n).le)]
  ring

private theorem cutoffProfile_zero_nonpos (n : ℕ) (g : ℝ → ℂ) {x : ℝ} (hx : x ≤ 0) :
    (fun y => (realPlaceCutoff n y : ℂ) * g y) =ᶠ[𝓝 x] (fun _ => 0) := by
  have hl : x < (cutoffScale n)⁻¹ := hx.trans_lt (inv_pos.mpr (cutoffScale_pos n))
  filter_upwards [Iio_mem_nhds hl] with y hy
  have hz := notMem_support.mp fun h =>
    hy.not_ge (realPlaceCutoff_support n (subset_tsupport _ h)).1
  simp [hz]

/-- Uniform L¹ estimates for the concrete cutoff when the profile vanishes
at zero and has exponential envelopes for its first two derivatives. -/
theorem realPlaceCutoff_profile_uniform_integrals {C δ : ℝ} (hC : 0 ≤ C) (hδ : 0 < δ) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ (g : ℝ → ℂ), ContDiff ℝ ∞ g → g 0 = 0 →
      (∀ k : ℕ, k ≤ 2 → ∀ x ≥ 0, ‖iteratedDeriv k g x‖ ≤ C * Real.exp (-δ * x)) →
      ∀ n : ℕ,
        let p := fun x => (realPlaceCutoff n x : ℂ) * g x
        (∫ x, ‖p x‖) ≤ A ∧ (∫ x, ‖deriv (deriv p) x‖) ≤ B := by
  obtain ⟨K, hK, hθ⟩ := transitionC_has_uniform_derivative_bounds
  let D := 2 * K * C + 2 * K * ((1 + K) * C)
  let M := (1 + 3 * K) * C
  have hD : 0 ≤ D := by positivity
  have hM : 0 ≤ M := by positivity
  refine ⟨C / δ, D + M / δ, by positivity, by positivity, ?_⟩
  intro g hg hg0 hgrowth n
  let p := fun x => (realPlaceCutoff n x : ℂ) * g x
  let q := upperCutoff n * g
  have hq : ContDiff ℝ ∞ q := (upperCutoff_smooth n).mul hg
  have hint := realPlaceCutoff_profile_integrable n hg
  have hp : p = lowerCutoff n * q := cutoff_factorization n g
  have hE : IntegrableOn (fun x : ℝ => Real.exp (-δ * x)) (Ioi 0) :=
    integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hδ) 0
  have hEval : (∫ x in Ioi (0 : ℝ), Real.exp (-δ * x)) = 1 / δ := by
    rw [integral_exp_mul_Ioi (neg_lt_zero.mpr hδ)]
    simp
  let envelope (A x : ℝ) := (Ioi 0 : Set ℝ).indicator (fun x => A * Real.exp (-δ * x)) x
  have hEnv (A : ℝ) : Integrable (envelope A) :=
    (integrable_indicator_iff measurableSet_Ioi).mpr (hE.const_mul A)
  have hEnvI (A : ℝ) : (∫ x, envelope A x) = A / δ := by
    rw [show envelope A = (Ioi 0 : Set ℝ).indicator (fun x => A * Real.exp (-δ * x)) from rfl,
      integral_indicator measurableSet_Ioi, integral_const_mul, hEval]
    ring
  have hg0b (x : ℝ) (hx : 0 ≤ x) : ‖g x‖ ≤ C * Real.exp (-δ * x) := by
    simpa using hgrowth 0 (by decide) x hx
  have hglin (x : ℝ) (hx : 0 ≤ x) : ‖g x‖ ≤ C * x := by
    have hb := norm_image_sub_le_of_norm_deriv_le_segment'
      (a := (0 : ℝ)) (b := x) (f := g) (f' := deriv g)
      (fun y _ => (hg.differentiable (by simp) y).hasDerivAt.hasDerivWithinAt)
      (C := C) (fun y hy => ?_) x ⟨hx, le_rfl⟩
    · simpa [hg0] using hb
    · have hg' := hgrowth 1 (by decide) y hy.1
      rw [iteratedDeriv_one] at hg'
      exact hg'.trans (mul_le_of_le_one_right hC (Real.exp_le_one_iff.mpr (by nlinarith [hy.1])))
  have hfirst (x : ℝ) (hx : 0 ≤ x) : ‖iteratedDeriv 1 q x‖ ≤
      ((1 + K) * C) * Real.exp (-δ * x) := by
    refine (norm_cutoff_product_first_le _ _ (upperCutoff_smooth n) hg x).trans ?_
    have h₁ := mul_le_mul (transitionC_norm_le (cutoffScale n - x)) (hgrowth 1 (by decide) x hx)
      (norm_nonneg _) zero_le_one
    have h₂ := mul_le_mul (upperCutoff_derivative_bound hθ n x 1 (.inl rfl)) (hg0b x hx)
      (norm_nonneg _) hK
    exact (add_le_add h₁ h₂).trans_eq (by ring)
  have hsecond (x : ℝ) (hx : 0 ≤ x) : ‖iteratedDeriv 2 q x‖ ≤ M * Real.exp (-δ * x) := by
    refine (norm_cutoff_product_second_le _ _ (upperCutoff_smooth n) hg x).trans ?_
    have h₁ := mul_le_mul (transitionC_norm_le (cutoffScale n - x)) (hgrowth 2 (by decide) x hx)
      (norm_nonneg _) zero_le_one
    have h₂ := mul_le_mul (upperCutoff_derivative_bound hθ n x 1 (.inl rfl)) (hgrowth 1 (by decide) x hx)
      (norm_nonneg _) hK
    have h₃ := mul_le_mul (upperCutoff_derivative_bound hθ n x 2 (.inr rfl)) (hg0b x hx)
      (norm_nonneg _) hK
    exact (add_le_add (add_le_add h₁ (mul_le_mul_of_nonneg_left h₂ (by norm_num))) h₃).trans_eq
      (by dsimp [M]; ring)
  have hqLinear (x : ℝ) (hx : 0 ≤ x) : ‖q x‖ ≤ C * x := by
    change ‖upperCutoff n x * g x‖ ≤ _
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right (transitionC_norm_le _) (norm_nonneg _)).trans (by simpa using hglin x hx)
  have hpoint₀ (x : ℝ) : ‖p x‖ ≤ envelope C x := by
    by_cases hx : 0 < x
    · rw [show envelope C x = C * Real.exp (-δ * x) from indicator_of_mem hx _]
      change ‖(realPlaceCutoff n x : ℂ) * g x‖ ≤ _
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (realPlaceCutoff_mem_Icc n x).1]
      exact (mul_le_of_le_one_left (norm_nonneg _) (realPlaceCutoff_mem_Icc n x).2).trans
        (hg0b x hx.le)
    · have hz := (cutoffProfile_zero_nonpos n g (le_of_not_gt hx)).eq_of_nhds
      change p x = 0 at hz
      rw [hz, norm_zero]
      exact le_of_eq (indicator_of_notMem hx _).symm
  have hpoint₂ (x : ℝ) : ‖iteratedDeriv 2 p x‖ ≤
      (lowerTransitionInterval n).indicator (fun _ => cutoffScale n * D) x + envelope M x := by
    by_cases hx : 0 < x
    · rw [show envelope M x = M * Real.exp (-δ * x) from indicator_of_mem hx _]
      have hl₀ := mul_le_mul (transitionC_norm_le (cutoffScale n * x - 1)) (hsecond x hx.le)
        (norm_nonneg _) zero_le_one
      have hl₀' : ‖lowerCutoff n x‖ * ‖iteratedDeriv 2 q x‖ ≤ M * Real.exp (-δ * x) := by
        simpa only [lowerCutoff, one_mul] using hl₀
      rw [hp]
      refine (norm_cutoff_product_second_le _ _ (lowerCutoff_smooth n) hq x).trans ?_
      have hl₁ := lowerCutoff_derivative_bound hθ n x 1 (.inl rfl)
      have hl₂ := lowerCutoff_derivative_bound hθ n x 2 (.inr rfl)
      by_cases hI : x ∈ lowerTransitionInterval n
      · rw [indicator_of_mem hI, pow_one] at hl₁
        rw [indicator_of_mem hI] at hl₂ ⊢
        have hq' : ‖iteratedDeriv 1 q x‖ ≤ (1 + K) * C :=
          (hfirst x hx.le).trans (mul_le_of_le_one_right (by positivity)
            (Real.exp_le_one_iff.mpr (by nlinarith [hx.le])))
        have hl₁' := mul_le_mul hl₁ hq' (norm_nonneg _)
          (mul_nonneg (cutoffScale_pos n).le hK)
        have hl₂' := mul_le_mul hl₂ (hqLinear x hx.le) (norm_nonneg _)
          (mul_nonneg (sq_nonneg _) hK)
        have hbound : cutoffScale n ^ 2 * K * (C * x) ≤ cutoffScale n * (2 * K * C) := by
          have hx' := (le_div_iff₀ (cutoffScale_pos n)).mp hI.2
          calc
            _ = (cutoffScale n * K * C) * (x * cutoffScale n) := by ring
            _ ≤ (cutoffScale n * K * C) * 2 := mul_le_mul_of_nonneg_left hx' (mul_nonneg (mul_nonneg (cutoffScale_pos n).le hK) hC)
            _ = _ := by ring
        have htotal := add_le_add (add_le_add hl₀'
          (mul_le_mul_of_nonneg_left hl₁' (show 0 ≤ (2 : ℝ) by norm_num))) (hl₂'.trans hbound)
        refine htotal.trans_eq ?_
        unfold D
        ring
      · rw [indicator_of_notMem hI] at hl₁ hl₂ ⊢
        rw [le_antisymm hl₁ (norm_nonneg _), le_antisymm hl₂ (norm_nonneg _)]
        simpa using hl₀'
    · have hz := (cutoffProfile_zero_nonpos n g (le_of_not_gt hx)).iteratedDeriv_eq 2
      change iteratedDeriv 2 p x = _ at hz
      rw [hz]
      have hI : x ∉ lowerTransitionInterval n := fun h => hx ((div_pos one_pos (cutoffScale_pos n)).trans_le h.1)
      simp [iteratedDeriv_const, indicator_of_notMem hI, envelope, hx]
  have hiStep : Integrable ((lowerTransitionInterval n).indicator (fun _ => cutoffScale n * D)) := by
    apply (integrable_indicator_iff measurableSet_Icc).mpr
    exact integrableOn_const (hs := isCompact_Icc.measure_ne_top)
  have hStepIntegral : (∫ x, (lowerTransitionInterval n).indicator (fun _ => cutoffScale n * D) x) = D := by
    have hmeas : MeasurableSet (lowerTransitionInterval n) := measurableSet_Icc
    rw [integral_indicator_const _ hmeas, lowerTransitionInterval_measure, smul_eq_mul]
    field_simp [(cutoffScale_pos n).ne']
  refine ⟨?_, ?_⟩
  · have h := integral_mono hint.1.norm (hEnv C) hpoint₀
    rwa [hEnvI] at h
  · have hpt (x : ℝ) : ‖deriv (deriv p) x‖ ≤
        (lowerTransitionInterval n).indicator (fun _ => cutoffScale n * D) x + envelope M x := by
      simpa [iteratedDeriv_succ, iteratedDeriv_one] using hpoint₂ x
    have h := integral_mono hint.2.2.1.norm (hiStep.add (hEnv M)) hpt
    change _ ≤ ∫ x, (lowerTransitionInterval n).indicator (fun _ => cutoffScale n * D) x + envelope M x at h
    rwa [integral_add hiStep (hEnv M), hStepIntegral, hEnvI] at h

private theorem iteratedDeriv_cexp_real (k : ℕ) (a : ℂ) :
    iteratedDeriv k (fun x : ℝ => Complex.exp (a * (x : ℂ))) =
      fun x : ℝ => a ^ k * Complex.exp (a * (x : ℂ)) := by
  have hd (x : ℝ) : HasDerivAt (fun t : ℝ => Complex.exp (a * (t : ℂ)))
      (Complex.exp (a * (x : ℂ)) * a) x := by
    have h : HasDerivAt ((↑) : ℝ → ℂ) (1 : ℂ) x := Complex.ofRealCLM.hasFDerivAt.hasDerivAt
    simpa using (h.const_mul a).cexp
  induction k with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    rw [((hd x).const_mul (a ^ k)).deriv, pow_succ]
    ring

private def subtractedExponentialProfile (u : ℝ) (z b : ℂ) (x : ℝ) : ℂ :=
  Complex.exp (((u : ℂ) - z) * (x : ℂ)) - Complex.exp (((u : ℂ) - b) * (x : ℂ))

private theorem subtractedExponentialProfile_smooth (u : ℝ) (z b : ℂ) :
    ContDiff ℝ ∞ (subtractedExponentialProfile u z b) :=
  ((contDiff_const.mul Complex.ofRealCLM.contDiff).cexp).sub
    ((contDiff_const.mul Complex.ofRealCLM.contDiff).cexp)

private theorem subtractedExponentialProfile_envelope {R δ : ℝ} {z b : ℂ}
    (hz : R + δ ≤ z.re) (hb : R + δ ≤ b.re)
    {u : ℝ} (hu : |u| ≤ R) (k : ℕ) (hk : k ≤ 2) (x : ℝ) (hx : 0 ≤ x) :
    ‖iteratedDeriv k (subtractedExponentialProfile u z b) x‖ ≤
      (2 * (1 + R + ‖z‖ + ‖b‖) ^ 2) * Real.exp (-δ * x) := by
  let M := (1 + R + ‖z‖ + ‖b‖)
  have hR : 0 ≤ R := (abs_nonneg u).trans hu
  have hM : 1 ≤ M := by dsimp [M]; linarith [norm_nonneg z, norm_nonneg b]
  have hcoef (w : ℂ) (hw : ‖w‖ ≤ ‖z‖ + ‖b‖) :
      ‖((u : ℂ) - w) ^ k‖ ≤ M ^ 2 := by
    rw [norm_pow]
    have hn := norm_sub_le (u : ℂ) w
    rw [Complex.norm_real, Real.norm_eq_abs] at hn
    have hl : ‖(u : ℂ) - w‖ ≤ M := hn.trans (by dsimp [M]; linarith)
    exact (pow_le_pow_left₀ (norm_nonneg _) hl _).trans (pow_le_pow_right₀ hM hk)
  have hdecay (w : ℂ) (hw : R + δ ≤ w.re) :
      ‖Complex.exp (((u : ℂ) - w) * (x : ℂ))‖ ≤ Real.exp (-δ * x) := by
    rw [Complex.norm_exp, Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, Complex.sub_re]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by linarith [(le_abs_self u).trans hu]) hx)
  let g (w : ℂ) := fun t : ℝ => Complex.exp (((u : ℂ) - w) * (t : ℂ))
  have hs (w : ℂ) : ContDiff ℝ k (g w) := (contDiff_const.mul Complex.ofRealCLM.contDiff).cexp
  change ‖iteratedDeriv k (fun y => g z y - g b y) x‖ ≤ _
  rw [iteratedDeriv_fun_sub (hs z).contDiffAt (hs b).contDiffAt]
  have he (w : ℂ) : iteratedDeriv k (g w) x = ((u : ℂ) - w) ^ k * g w x :=
    congrFun (iteratedDeriv_cexp_real k ((u : ℂ) - w)) x
  rw [he, he]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul, norm_mul]
  have h₁ := mul_le_mul (hcoef z (le_add_of_nonneg_right (norm_nonneg _))) (hdecay z hz)
    (norm_nonneg _) (sq_nonneg _)
  have h₂ := mul_le_mul (hcoef b (le_add_of_nonneg_left (norm_nonneg _))) (hdecay b hb)
    (norm_nonneg _) (sq_nonneg _)
  exact (add_le_add h₁ h₂).trans_eq (by dsimp [M]; ring)

private def concreteSpectralProfile (n : ℕ) (z b w : ℂ) (x : ℝ) : ℂ :=
  (realPlaceCutoff n x : ℂ) * subtractedExponentialProfile w.re z b x

private def spectralFourierFrequency (w : ℂ) : ℝ :=
  -w.im / (2 * Real.pi)

private theorem concreteSpectralProfile_fourier (n : ℕ) (z b w : ℂ) :
    𝓕 (concreteSpectralProfile n z b w) (spectralFourierFrequency w) =
      ∫ x in Ioi (0 : ℝ), (realPlaceCutoff n x : ℂ) *
        (Complex.exp ((w - z) * (x : ℂ)) - Complex.exp ((w - b) * (x : ℂ))) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  let p (x : ℝ) := Complex.exp (↑(-2 * Real.pi * x * spectralFourierFrequency w) * Complex.I) •
    concreteSpectralProfile n z b w x
  change (∫ x, p x) = _
  have hz (x : ℝ) (hx : x ∉ Ioi (0 : ℝ)) : p x = 0 := by
    have heq := (cutoffProfile_zero_nonpos n (subtractedExponentialProfile w.re z b)
      (le_of_not_gt hx)).eq_of_nhds
    change concreteSpectralProfile n z b w x = 0 at heq
    simp [p, heq]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioi (0 : ℝ)) hz]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x _
  have hphase : ↑(-2 * Real.pi * x * spectralFourierFrequency w) * Complex.I =
      (w.im : ℂ) * Complex.I * (x : ℂ) := by
    unfold spectralFourierFrequency
    push_cast
    have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    field_simp
    <;> ring
  have he (a : ℂ) :
      (w.im : ℂ) * Complex.I * (x : ℂ) + ((w.re : ℂ) - a) * (x : ℂ) =
        (w - a) * (x : ℂ) := by
    conv_rhs => rw [← Complex.re_add_im w]
    ring
  unfold p concreteSpectralProfile subtractedExponentialProfile
  rw [hphase, smul_eq_mul, mul_left_comm, mul_sub, ← Complex.exp_add, ← Complex.exp_add, he, he]

private theorem fourierFrequency_weight_summable {ι : Type*} (zeros : ι → ℂ) (multiplicity : ι → ℕ)
    (hcount : Summable (fun i => (multiplicity i : ℝ) / (1 + (zeros i).im ^ 2))) :
    Summable (fun i => (multiplicity i : ℝ) / (1 + (spectralFourierFrequency (zeros i)) ^ 2)) := by
  let a := 2 * Real.pi
  have ha : 0 < a := by dsimp [a]; positivity
  have ha₂ : 1 ≤ a ^ 2 := by
    dsimp [a]
    nlinarith [Real.two_le_pi, sq_nonneg (Real.pi - 2)]
  apply (hcount.mul_left (a ^ 2)).of_nonneg_of_le (fun i => by positivity)
  intro i
  let y := (zeros i).im
  let m := (multiplicity i : ℝ)
  change m / (1 + (-y / a) ^ 2) ≤ a ^ 2 * (m / (1 + y ^ 2))
  rw [neg_div, neg_sq, div_pow]
  have he : (m / (1 + y ^ 2 / a ^ 2)) = (a ^ 2) * (m / (a ^ 2 + y ^ 2)) := by
    field_simp [ha.ne', show a ^ 2 + y ^ 2 ≠ 0 by positivity]
    <;> ring
  rw [he]
  gcongr

/-- For the paper's specific smooth cutoffs, the subtracted spectral sums
converge to the sum of resolvent differences under a weighted zero count. -/
theorem concreteSpectralCutoff_tendsto {ι : Type*} (zeros : ι → ℂ) (multiplicity : ι → ℕ)
    {R : ℝ} {z b : ℂ} (hz : R < z.re) (hb : R < b.re)
    (hstrip : ∀ i, |(zeros i).re| ≤ R)
    (hcount : Summable (fun i => (multiplicity i : ℝ) / (1 + (zeros i).im ^ 2))) :
    Tendsto
      (fun n => ∑' i, (multiplicity i : ℂ) * ∫ x in Ioi (0 : ℝ),
        (realPlaceCutoff n x : ℂ) * (Complex.exp ((zeros i - z) * (x : ℂ)) -
          Complex.exp ((zeros i - b) * (x : ℂ)))) atTop
      (𝓝 (∑' i, (multiplicity i : ℂ) * ((z - zeros i)⁻¹ - (b - zeros i)⁻¹))) := by
  let δ := min (z.re - R) (b.re - R)
  have hδ : 0 < δ := lt_min (sub_pos.mpr hz) (sub_pos.mpr hb)
  have hzδ : R + δ ≤ z.re := by dsimp [δ]; linarith [min_le_left (z.re - R) (b.re - R)]
  have hbδ : R + δ ≤ b.re := by dsimp [δ]; linarith [min_le_right (z.re - R) (b.re - R)]
  let C := 2 * (1 + R + ‖z‖ + ‖b‖) ^ 2
  obtain ⟨A, B, hA, hB, hL⟩ := realPlaceCutoff_profile_uniform_integrals
    (C := C) (by dsimp [C]; positivity) hδ
  let p (n : ℕ) (i : ι) := concreteSpectralProfile n z b (zeros i)
  have hint (n : ℕ) (i : ι) :
      Integrable (p n i) ∧ Integrable (deriv (p n i)) ∧ Integrable (deriv (deriv (p n i))) ∧
        Differentiable ℝ (p n i) ∧ Differentiable ℝ (deriv (p n i)) :=
    realPlaceCutoff_profile_integrable n (subtractedExponentialProfile_smooth (zeros i).re z b)
  have hbound (n : ℕ) (i : ι) :
      (∫ x, ‖p n i x‖) ≤ A ∧ (∫ x, ‖deriv (deriv (p n i)) x‖) ≤ B :=
    hL _ (subtractedExponentialProfile_smooth (zeros i).re z b)
      (by simp [subtractedExponentialProfile])
      (fun k hk x hx => subtractedExponentialProfile_envelope hzδ hbδ (hstrip i) k hk x hx) n
  have hlim (i : ι) : Tendsto (fun n => 𝓕 (p n i) (spectralFourierFrequency (zeros i)))
      atTop (𝓝 ((z - zeros i)⁻¹ - (b - zeros i)⁻¹)) := by
    have hzi := ((le_abs_self ((zeros i).re)).trans (hstrip i)).trans_lt hz
    have hbi := ((le_abs_self ((zeros i).re)).trans (hstrip i)).trans_lt hb
    simpa only [p, concreteSpectralProfile_fourier] using
      spectralLaplaceCutoff_tendsto z b (zeros i) hzi hbi realPlaceCutoff
        (fun n => (realPlaceCutoff_smooth n).continuous.measurable) realPlaceCutoff_mem_Icc
        (fun x hx => tendsto_const_nhds.congr' (realPlaceCutoff_eventually_one hx).symm)
  simpa only [p, concreteSpectralProfile_fourier] using
    spectralFourierCutoff_tendsto (fun i => spectralFourierFrequency (zeros i)) multiplicity
      (fourierFrequency_weight_summable zeros multiplicity hcount) p
      (fun i => (z - zeros i)⁻¹ - (b - zeros i)⁻¹)
      (fun n i => (hint n i).1) (fun n i => (hint n i).2.1)
      (fun n i => (hint n i).2.2.1) (fun n i => (hint n i).2.2.2.1)
      (fun n i => (hint n i).2.2.2.2) hA hB (fun n i => (hbound n i).1)
      (fun n i => (hbound n i).2) hlim

def cutoffLaplaceIntegral (n : ℕ) (z b w : ℂ) : ℂ :=
  ∫ x in Ioi (0 : ℝ), (realPlaceCutoff n x : ℂ) *
    (Complex.exp ((w - z) * (x : ℂ)) - Complex.exp ((w - b) * (x : ℂ)))

def subtractedResolvent (z b w : ℂ) : ℂ := (z - w)⁻¹ - (b - w)⁻¹

private def cutoffErrorEnvelope (δ : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  2 * (1 - realPlaceCutoff n x) * Real.exp (-δ * x)

private theorem cutoffErrorEnvelope_tendsto (δ : ℝ) (hδ : 0 < δ) :
    Tendsto (fun n : ℕ => ∫ x in Ioi (0 : ℝ), cutoffErrorEnvelope δ n x) atTop (𝓝 0) := by
  have hie : IntegrableOn (fun x : ℝ => 2 * Real.exp (-δ * x)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hδ) 0).const_mul 2
  rw [show 𝓝 (0 : ℝ) = 𝓝 (∫ x in Ioi (0 : ℝ), (0 : ℝ)) by simp]
  apply tendsto_integral_of_dominated_convergence (fun x => 2 * Real.exp (-δ * x))
  · intro n
    have h : Continuous (cutoffErrorEnvelope δ n) := by
      unfold cutoffErrorEnvelope
      exact (continuous_const.mul (continuous_const.sub (realPlaceCutoff_smooth n).continuous)).mul
        (Real.continuous_exp.comp (continuous_const.mul continuous_id))
    exact h.measurable.aestronglyMeasurable
  · exact hie
  · intro n
    apply Eventually.of_forall
    intro x
    obtain ⟨h₀, h₁⟩ := realPlaceCutoff_mem_Icc n x
    rw [Real.norm_of_nonneg (show 0 ≤ cutoffErrorEnvelope δ n x from
      mul_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr h₁)) (Real.exp_pos _).le)]
    change 2 * (1 - realPlaceCutoff n x) * Real.exp (-δ * x) ≤ 2 * Real.exp (-δ * x)
    exact mul_le_mul_of_nonneg_right (by linarith [h₀]) (Real.exp_pos _).le
  · filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with x hx
    apply tendsto_const_nhds.congr'
    filter_upwards [realPlaceCutoff_eventually_one hx] with n hn
    simp [cutoffErrorEnvelope, hn]

private theorem cutoffLaplace_error_le (n : ℕ) (z b w : ℂ) {δ : ℝ} (hδ : 0 < δ)
    (hz : δ ≤ z.re - w.re) (hb : δ ≤ b.re - w.re) :
    ‖cutoffLaplaceIntegral n z b w - subtractedResolvent z b w‖ ≤
      ∫ x in Ioi (0 : ℝ), cutoffErrorEnvelope δ n x := by
  let μ := volume.restrict (Ioi (0 : ℝ))
  let F (x : ℝ) := Complex.exp ((w - z) * (x : ℂ)) - Complex.exp ((w - b) * (x : ℂ))
  have hz' : (w - z).re < 0 := by simp; linarith
  have hb' : (w - b).re < 0 := by simp; linarith
  have hzi := integrableOn_exp_mul_complex_Ioi hz' 0
  have hbi := integrableOn_exp_mul_complex_Ioi hb' 0
  have hi : Integrable F μ := hzi.sub hbi
  have hres : (∫ x, F x ∂μ) = subtractedResolvent z b w := by
    change (∫ x in Ioi (0 : ℝ), _) = _
    unfold F subtractedResolvent
    rw [integral_sub hzi hbi, integral_exp_mul_complex_Ioi hz', integral_exp_mul_complex_Ioi hb']
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, neg_div, one_div, ← inv_neg, neg_sub]
  have hcut0 (x : ℝ) : 0 ≤ realPlaceCutoff n x := (realPlaceCutoff_mem_Icc n x).1
  have hcut1 (x : ℝ) : realPlaceCutoff n x ≤ 1 := (realPlaceCutoff_mem_Icc n x).2
  have hci : Integrable (fun x => (realPlaceCutoff n x : ℂ) * F x) μ := by
    have hc : Continuous (fun x : ℝ => (realPlaceCutoff n x : ℂ)) :=
      Complex.continuous_ofReal.comp (realPlaceCutoff_smooth n).continuous
    apply hi.norm.mono' (hc.aestronglyMeasurable.mul hi.aestronglyMeasurable)
    exact Eventually.of_forall (fun x => by
      change ‖(realPlaceCutoff n x : ℂ) * F x‖ ≤ ‖F x‖
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hcut0 x)]
      exact mul_le_of_le_one_left (norm_nonneg _) (hcut1 x))
  have he : Integrable (cutoffErrorEnvelope δ n) μ := by
    let G := fun x : ℝ => Real.exp (-δ * x)
    have hG : Integrable G μ := integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hδ) 0
    have hc : Continuous (cutoffErrorEnvelope δ n) := by
      unfold cutoffErrorEnvelope
      exact (continuous_const.mul (continuous_const.sub (realPlaceCutoff_smooth n).continuous)).mul
        (Real.continuous_exp.comp (continuous_const.mul continuous_id))
    apply (hG.const_mul 2).mono' hc.aestronglyMeasurable
    exact Eventually.of_forall (fun x => by
      change ‖cutoffErrorEnvelope δ n x‖ ≤ 2 * G x
      rw [Real.norm_of_nonneg (show 0 ≤ cutoffErrorEnvelope δ n x from
        mul_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr (hcut1 x))) (Real.exp_pos _).le)]
      change 2 * (1 - realPlaceCutoff n x) * Real.exp (-δ * x) ≤ 2 * Real.exp (-δ * x)
      exact mul_le_mul_of_nonneg_right (by linarith [hcut0 x]) (Real.exp_pos _).le)
  rw [← hres]
  change ‖(∫ x, (realPlaceCutoff n x : ℂ) * F x ∂μ) - ∫ x, F x ∂μ‖ ≤ _
  rw [← integral_sub hci hi]
  apply norm_integral_le_of_norm_le he
  filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with x hx
  have hx₀ : 0 ≤ x := hx.le
  have hbase (a : ℂ) (ha : δ ≤ a.re - w.re) :
      ‖Complex.exp ((w - a) * (x : ℂ))‖ ≤ Real.exp (-δ * x) := by
    rw [Complex.norm_exp, Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, Complex.sub_re]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by linarith) hx₀)
  have hF : ‖F x‖ ≤ 2 * Real.exp (-δ * x) := by
    refine (norm_sub_le _ _).trans ?_
    linarith [hbase z hz, hbase b hb]
  rw [← sub_one_mul, norm_mul, show (realPlaceCutoff n x : ℂ) - 1 =
    ((realPlaceCutoff n x - 1 : ℝ) : ℂ) by simp,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr (hcut1 x)), neg_sub]
  exact (mul_le_mul_of_nonneg_left hF (sub_nonneg.mpr (hcut1 x))).trans_eq (by
    unfold cutoffErrorEnvelope
    ring)

private theorem uniform_limit_of_dominated_sums {ι X : Type*} {K : Set X}
    (fn : ℕ → ι → X → ℂ) (f : ι → X → ℂ) (g : ι → ℝ)
    (hg : Summable g)
    (hfn : ∀ n i x, x ∈ K → ‖fn n i x‖ ≤ g i)
    (hf : ∀ i x, x ∈ K → ‖f i x‖ ≤ g i)
    (hfin : ∀ s : Finset ι, TendstoUniformlyOn (fun n x => ∑ i ∈ s, fn n i x)
      (fun x => ∑ i ∈ s, f i x) atTop K) :
    TendstoUniformlyOn (fun n x => ∑' i, fn n i x) (fun x => ∑' i, f i x) atTop K := by
  classical
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have htail : ∃ s : Finset ι, (∑' i : ↥(↑s : Set ι)ᶜ, g i.val) < ε / 3 := by
    have hlim : Tendsto (fun s : Finset ι => ∑ i ∈ s, g i) atTop (𝓝 (∑' i, g i)) :=
      hg.hasSum
    have he := (Metric.tendsto_nhds.mp hlim (ε / 3) (by positivity)).exists
    obtain ⟨s, hs⟩ := he
    refine ⟨s, ?_⟩
    have heq := hg.sum_add_tsum_subtype_compl s
    rw [dist_eq_norm, ← heq, sub_add_cancel_left, norm_neg, Real.norm_eq_abs] at hs
    exact (le_abs_self _).trans_lt hs
  obtain ⟨s, hs⟩ := htail
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp (hfin s) (ε / 3) (by positivity)] with n hn
  intro x hx
  have hsfn : Summable (fun i => ‖fn n i x‖) := hg.of_nonneg_of_le (fun _ => norm_nonneg _) (fun i => hfn n i x hx)
  have hsf : Summable (fun i => ‖f i x‖) := hg.of_nonneg_of_le (fun _ => norm_nonneg _) (fun i => hf i x hx)
  let I := ↥(↑s : Set ι)ᶜ
  have htailL : ‖∑' i : I, fn n i.val x‖ ≤ ∑' i : I, g i.val :=
    (norm_tsum_le_tsum_norm (hsfn.subtype _)).trans ((hsfn.subtype _).tsum_le_tsum
      (fun i => hfn n i.val x hx) (hg.subtype _))
  have htailR : ‖∑' i : I, f i.val x‖ ≤ ∑' i : I, g i.val :=
    (norm_tsum_le_tsum_norm (hsf.subtype _)).trans ((hsf.subtype _).tsum_le_tsum
      (fun i => hf i.val x hx) (hg.subtype _))
  have hp := hn x hx
  rw [dist_eq_norm] at hp ⊢
  rw [← (hsfn.of_norm).sum_add_tsum_subtype_compl s, ← (hsf.of_norm).sum_add_tsum_subtype_compl s,
    add_sub_add_comm]
  refine (norm_add_le _ _).trans_lt ?_
  change (∑' i : I, g i.val) < ε / 3 at hs
  change ‖(∑ i ∈ s, f i x) - ∑ i ∈ s, fn n i x‖ +
    ‖(∑' i : I, f i.val x) - ∑' i : I, fn n i.val x‖ < ε
  linarith [norm_sub_le (∑' i : I, f i.val x) (∑' i : I, fn n i.val x)]

/-- The subtracted concrete spectral sums converge uniformly for any bounded
set of exponents separated to the right of the strip. -/
theorem concreteSpectralCutoff_tendstoUniformlyOn {ι : Type*} (zeros : ι → ℂ) (multiplicity : ι → ℕ)
    {K : Set ℂ} {R δ Z : ℝ} {b : ℂ} (hR : 0 ≤ R) (hδ : 0 < δ) (hZ : 0 ≤ Z)
    (hz : ∀ z ∈ K, R + δ ≤ z.re ∧ ‖z‖ ≤ Z) (hb : R + δ ≤ b.re)
    (hstrip : ∀ i, |(zeros i).re| ≤ R)
    (hcount : Summable (fun i => (multiplicity i : ℝ) / (1 + (zeros i).im ^ 2))) :
    TendstoUniformlyOn (fun n z => ∑' i, (multiplicity i : ℂ) * cutoffLaplaceIntegral n z b (zeros i))
      (fun z => ∑' i, (multiplicity i : ℂ) * subtractedResolvent z b (zeros i)) atTop K := by
  let C := 2 * (1 + R + Z + ‖b‖) ^ 2
  obtain ⟨A, B, hA, hB, hL⟩ := realPlaceCutoff_profile_uniform_integrals
    (C := C) (by dsimp [C]; positivity) hδ
  let c := 2 * A + 2 * B / (2 * Real.pi) ^ 2
  let fn (n : ℕ) (i : ι) (z : ℂ) := (multiplicity i : ℂ) * cutoffLaplaceIntegral n z b (zeros i)
  let f (i : ι) (z : ℂ) := (multiplicity i : ℂ) * subtractedResolvent z b (zeros i)
  let g (i : ι) := c * ((multiplicity i : ℝ) / (1 + (spectralFourierFrequency (zeros i)) ^ 2))
  have hg : Summable g := (fourierFrequency_weight_summable zeros multiplicity hcount).mul_left c
  have hfn (n : ℕ) (i : ι) {z : ℂ} (hzK : z ∈ K) : ‖fn n i z‖ ≤ g i := by
    have hgrowth (k : ℕ) (hk : k ≤ 2) (x : ℝ) (hx : 0 ≤ x) :
        ‖iteratedDeriv k (subtractedExponentialProfile (zeros i).re z b) x‖ ≤
          C * Real.exp (-δ * x) := by
      refine (subtractedExponentialProfile_envelope (hz z hzK).1 hb (hstrip i) k hk x hx).trans ?_
      exact mul_le_mul_of_nonneg_right (by
        dsimp [C]
        gcongr
        exact (hz z hzK).2) (Real.exp_pos _).le
    have H := realPlaceCutoff_profile_integrable n (subtractedExponentialProfile_smooth (zeros i).re z b)
    have hL₀ := hL _ (subtractedExponentialProfile_smooth (zeros i).re z b)
      (by simp [subtractedExponentialProfile]) hgrowth n
    have bound := norm_fourier_le_one_add_sq H.1 H.2.1 H.2.2.1 H.2.2.2.1 H.2.2.2.2
      hA hB hL₀.1 hL₀.2 (spectralFourierFrequency (zeros i))
    change ‖𝓕 (concreteSpectralProfile n z b (zeros i)) (spectralFourierFrequency (zeros i))‖ ≤ _ at bound
    rw [concreteSpectralProfile_fourier] at bound
    unfold fn g
    rw [norm_mul, Complex.norm_natCast]
    refine (mul_le_mul_of_nonneg_left bound (Nat.cast_nonneg _)).trans_eq ?_
    ring
  have hprim (z : ℂ) (hzK : z ∈ K) (i : ι) :
      Tendsto (fun n => fn n i z) atTop (𝓝 (f i z)) := by
    have hzi := ((le_abs_self ((zeros i).re)).trans (hstrip i)).trans_lt
      ((lt_add_of_pos_right R hδ).trans_le (hz z hzK).1)
    have hbi := ((le_abs_self ((zeros i).re)).trans (hstrip i)).trans_lt
      ((lt_add_of_pos_right R hδ).trans_le hb)
    have hs := spectralLaplaceCutoff_tendsto z b (zeros i) hzi hbi realPlaceCutoff
      (fun n => (realPlaceCutoff_smooth n).continuous.measurable) realPlaceCutoff_mem_Icc
      (fun x hx => tendsto_const_nhds.congr' (realPlaceCutoff_eventually_one hx).symm)
    exact hs.const_mul _
  apply uniform_limit_of_dominated_sums fn f g hg (fun n i _ hx => hfn n i hx)
  · intro i z hzK
    exact le_of_tendsto' (hprim z hzK i).norm (fun n => hfn n i hzK)
  · intro s
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    let D : ℝ := ∑ i ∈ s, (multiplicity i : ℝ)
    have hlim := (cutoffErrorEnvelope_tendsto δ hδ).const_mul D
    filter_upwards [hlim (show Iio ε ∈ 𝓝 (D * 0) by simpa using Iio_mem_nhds hε)] with n hn
    intro z hzK
    rw [dist_eq_norm, ← Finset.sum_sub_distrib]
    refine (norm_sum_le _ _).trans_lt ?_
    let E := ∫ x in Ioi (0 : ℝ), cutoffErrorEnvelope δ n x
    have hsum : (∑ i ∈ s, ‖f i z - fn n i z‖) ≤ ∑ i ∈ s, (multiplicity i : ℝ) * E := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_sub_rev]
      change ‖(multiplicity i : ℂ) * cutoffLaplaceIntegral n z b (zeros i) -
        (multiplicity i : ℂ) * subtractedResolvent z b (zeros i)‖ ≤
        (multiplicity i : ℝ) * ∫ x in Ioi (0 : ℝ), cutoffErrorEnvelope δ n x
      rw [← mul_sub, norm_mul, Complex.norm_natCast]
      have hreal : (zeros i).re ≤ R := (le_abs_self _).trans (hstrip i)
      exact mul_le_mul_of_nonneg_left
        (cutoffLaplace_error_le n z b (zeros i) hδ (by linarith [(hz z hzK).1]) (by linarith))
        (Nat.cast_nonneg _)
    refine hsum.trans_lt ?_
    rw [← Finset.sum_mul]
    exact hn

end
end Masullo
