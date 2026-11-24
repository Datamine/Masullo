import MellinDiscreteSummation
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Algebra.PontryaginDual

open Filter Function MeasureTheory Set Topology
open scoped ContDiff FourierTransform

namespace Masullo

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

private theorem norm_realFourier_le_integral {g : ℝ → E} (hg : Integrable g) (y : ℝ) :
    ‖𝓕 g y‖ ≤ ∫ x, ‖g x‖ := by
  rw [Real.fourier_eq']
  apply norm_integral_le_of_norm_le hg.norm
  exact Eventually.of_forall fun x => by
    rw [norm_smul, Complex.norm_exp]
    simp

private theorem norm_realFourier_le_secondDeriv {f : ℝ → E}
    (hf : Integrable f) (hd₁ : Differentiable ℝ f)
    (hf₁ : Integrable (deriv f)) (hd₂ : Differentiable ℝ (deriv f))
    (hf₂ : Integrable (deriv (deriv f))) (y : ℝ) :
    (2 * Real.pi * |y|) ^ 2 * ‖𝓕 f y‖ ≤ ∫ x, ‖deriv (deriv f) x‖ := by
  have h₁ := congrFun (Real.fourier_deriv hf hd₁ hf₁) y
  have h₂ := congrFun (Real.fourier_deriv hf₁ hd₂ hf₂) y
  calc
    _ = ‖𝓕 (deriv (deriv f)) y‖ := by
      rw [h₂, h₁, norm_smul, norm_smul]
      simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos, pow_two,
        mul_assoc, mul_left_comm, mul_comm]
    _ ≤ _ := norm_realFourier_le_integral hf₂ y

private theorem continuous_weightedDeriv₂ [CompleteSpace E] {f : ℝ → E}
    (hf : ContDiff ℝ 2 f) :
    Continuous (fun p : ℝ × ℝ => deriv (deriv (fun x : ℝ => Real.exp (p.1 * x) • f x)) p.2) := by
  let W (σ x : ℝ) := Real.exp (σ * x)
  have hW (σ : ℝ) : ContDiff ℝ 2 (W σ) := by dsimp [W]; fun_prop
  have h (p : ℝ × ℝ) :
      deriv (deriv (fun x : ℝ => W p.1 x • f x)) p.2 =
        ∑ i ∈ Finset.range (2 + 1), (Nat.choose 2 i) •
          ((p.1 ^ i * W p.1 p.2) • iteratedDeriv (2 - i) f p.2) := by
    have he := iteratedDerivWithin_smul (Set.mem_univ p.2) uniqueDiffOn_univ
      (hW p.1).contDiffAt.contDiffWithinAt hf.contDiffAt.contDiffWithinAt
    change deriv (deriv (W p.1 • f)) p.2 = _
    simpa only [iteratedDerivWithin_univ, iteratedDeriv_exp_const_mul,
      show (fun x : ℝ => W p.1 x) = (fun x => Real.exp (p.1 * x)) from rfl,
      iteratedDeriv_succ, iteratedDeriv_zero] using he
  have heq := funext h
  rw [heq]
  apply continuous_finset_sum
  intro i hi
  have hf' : Continuous (iteratedDeriv (2 - i) f) :=
    hf.continuous_iteratedDeriv _ (by exact_mod_cast Nat.sub_le 2 i)
  have h : Continuous (fun a : ℝ × ℝ => (a.1 ^ i * W a.1 a.2) • iteratedDeriv (2 - i) f a.2) :=
    ((continuous_fst.pow i).mul (by dsimp [W]; fun_prop)).smul (hf'.comp continuous_snd)
  refine (h.const_smul (Nat.choose 2 i : ℝ)).congr fun a => ?_
  simp only [Pi.smul_apply, Nat.cast_smul_eq_nsmul]

private theorem HasCompactSupport.continuousL1_uniform {B : Type*} [TopologicalSpace B]
    [CompleteSpace E] {s : Set B} (hs : IsCompact s)
    (g : B → ℝ → E) (hg : Continuous (fun p : B × ℝ => g p.1 p.2))
    {R : ℝ} (hR : 0 ≤ R) (hzero : ∀ b x, x ∉ Icc (-R) R → g b x = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ b ∈ s, (∫ x, ‖g b x‖) ≤ C := by
  obtain ⟨M, hM⟩ := (hs.prod isCompact_Icc).exists_bound_of_continuousOn hg.continuousOn
  let D := Icc (-R) R
  refine ⟨volume.real D * max M 0, mul_nonneg ENNReal.toReal_nonneg (le_max_right _ _), ?_⟩
  intro b hb
  have hsupp : HasCompactSupport (g b) :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc
      (fun x hx => not_not.mp (fun h => hx (hzero b x h)))
  have hcont : Continuous (g b) := hg.comp (continuous_const.prodMk continuous_id)
  rw [← MeasureTheory.setIntegral_eq_integral_of_ae_compl_eq_zero (s := D) (μ := volume)
    (ae_of_all _ fun x hx => by rw [hzero b x hx, norm_zero])]
  have h' : ∀ x ∈ D, ‖g b x‖ ≤ max M 0 :=
    fun x hx => (hM (b, x) ⟨hb, hx⟩).trans (le_max_left _ _)
  exact (setIntegral_mono_on (hcont.norm.integrable_of_hasCompactSupport hsupp.norm).integrableOn
    (integrableOn_const (by simp [D, Real.volume_Icc])) measurableSet_Icc h').trans_eq (by
      simp only [setIntegral_const, smul_eq_mul, D])


/-- A smooth compactly supported vector profile has uniform reciprocal-square
Fourier decay after every real twist in a fixed compact interval. -/
theorem compactProfile_fourier_weighted_bound [CompleteSpace E] {f : ℝ → E}
    (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) (a b : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ ∈ Icc a b, ∀ y : ℝ,
      (1 + (2 * Real.pi * |y|) ^ 2) * ‖𝓕 (fun x : ℝ => Real.exp (σ * x) • f x) y‖ ≤ C := by
  let W (σ x : ℝ) := Real.exp (σ * x) • f x
  obtain ⟨r, hr, hball⟩ := hc.isBounded.subset_closedBall_lt 0 (0 : ℝ)
  have hI : tsupport f ⊆ Icc (-r) r := by
    intro x hx
    have h := hball hx
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_le] at h
    exact h
  have hs (σ : ℝ) : tsupport (W σ) ⊆ tsupport f := by
    apply closure_mono
    intro x hx hf0
    exact hx (show W σ x = 0 by simp [W, hf0])
  have hcW (σ : ℝ) : HasCompactSupport (W σ) :=
    hc.of_isClosed_subset isClosed_closure (hs σ)
  have hd (σ : ℝ) : ContDiff ℝ 2 (W σ) := (show ContDiff ℝ 2 (fun x => Real.exp (σ * x)) by
    fun_prop).smul hf
  have hj : Continuous (fun p : ℝ × ℝ => W p.1 p.2) := by
    exact (show Continuous (fun p : ℝ × ℝ => Real.exp (p.1 * p.2)) by fun_prop).smul
      (hf.continuous.comp continuous_snd)
  have hz (σ x : ℝ) (hx : x ∉ Icc (-r) r) : W σ x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hx (hI (hs σ h)))
  have hz₂ (σ x : ℝ) (hx : x ∉ Icc (-r) r) : deriv (deriv (W σ)) x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hx (hI (hs σ (tsupport_deriv_subset
      (tsupport_deriv_subset h)))))
  obtain ⟨C₀, hC₀, h₀⟩ := HasCompactSupport.continuousL1_uniform (s := Icc a b)
    isCompact_Icc W hj hr.le hz
  obtain ⟨C₂, hC₂, h₂⟩ := HasCompactSupport.continuousL1_uniform (s := Icc a b)
    isCompact_Icc (fun σ => deriv (deriv (W σ))) (continuous_weightedDeriv₂ hf) hr.le hz₂
  refine ⟨C₀ + C₂, add_nonneg hC₀ hC₂, ?_⟩
  intro σ hσ y
  have hInt : Integrable (W σ) := (hd σ).continuous.integrable_of_hasCompactSupport (hcW σ)
  have hCd : ContDiff ℝ 1 (deriv (W σ)) := by
    have htwo : ContDiff ℝ (1 + 1) (W σ) := by
      rw [one_add_one_eq_two]
      exact hd σ
    exact htwo.deriv'
  have hInt₁ : Integrable (deriv (W σ)) :=
    hCd.continuous.integrable_of_hasCompactSupport (hcW σ).deriv
  have hInt₂ : Integrable (deriv (deriv (W σ))) :=
    hCd.continuous_deriv (by norm_num) |>.integrable_of_hasCompactSupport (hcW σ).deriv.deriv
  rw [add_mul, one_mul]
  exact add_le_add ((norm_realFourier_le_integral hInt y).trans (h₀ σ hσ))
    ((norm_realFourier_le_secondDeriv hInt ((hd σ).differentiable (by norm_num))
      hInt₁ (hCd.differentiable (by norm_num)) hInt₂ y).trans (h₂ σ hσ))

/-- The compact character average of a translated test is its dilated radial
average times the character of the inverse compact component. This is the
Haar-integral identity in Discussion 4.4.1.1(3), adapted from original 56834aa. -/
theorem modulatedMellin_average_translate {G A : Type*} [CommGroup G] [Group A]
    (m : G →* A) (τ : A →* G) (hτ : Function.RightInverse τ m)
    [MeasurableSpace m.ker] [MeasurableMul m.ker] (μ : Measure m.ker)
    [Measure.IsMulLeftInvariant μ] (χ : G →* Circle) (f : G → ℂ) (γ : G) (t : A) :
    (∫ k : m.ker, (χ k.val : ℂ) * f (γ * (k.val * τ t)) ∂μ) =
      (χ (τ (m γ) * γ⁻¹) : ℂ) *
        (∫ k : m.ker, (χ k.val : ℂ) * f (k.val * τ (m γ * t)) ∂μ) := by
  let k₀ : m.ker := ⟨γ * (τ (m γ))⁻¹, by
    change m (γ * (τ (m γ))⁻¹) = 1
    rw [map_mul, map_inv, hτ, mul_inv_cancel]⟩
  have hterm (k : m.ker) :
      (χ k.val : ℂ) * f (γ * (k.val * τ t)) =
        (χ (τ (m γ) * γ⁻¹) : ℂ) *
          ((χ (k₀ * k).val : ℂ) * f ((k₀ * k).val * τ (m γ * t))) := by
    have htranslate : γ * (k.val * τ t) = (k₀ * k).val * τ (m γ * t) := by
      change γ * (k.val * τ t) = (γ * (τ (m γ))⁻¹ * k.val) * τ (m γ * t)
      rw [map_mul, mul_assoc γ, mul_assoc γ, mul_comm _ k.val,
        mul_assoc k.val, inv_mul_cancel_left]
    have hcharacter : k.val = τ (m γ) * γ⁻¹ * (k₀ * k).val := by
      change k.val = τ (m γ) * γ⁻¹ * (γ * (τ (m γ))⁻¹ * k.val)
      rw [mul_assoc, ← mul_assoc γ⁻¹, inv_mul_cancel_left, mul_inv_cancel_left]
    rw [htranslate, ← mul_assoc, ← Circle.coe_mul, ← map_mul, ← hcharacter]
  simp_rw [hterm]
  rw [integral_const_mul]
  congr 1
  exact integral_mul_left_eq_self
    (fun k : m.ker => (χ k.val : ℂ) * f (k.val * τ (m γ * t))) k₀

section CompactFactor

variable {K : Type*} [TopologicalSpace K] [CompactSpace K] [T2Space K]
  [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [IsFiniteMeasure μ]

/-- Integrating against a compact character defines a bounded functional. -/
def compactCharacterIntegral (χ : C(K, ℂ)) (hχ : ∀ x, ‖χ x‖ = 1) :
    C(K, ℂ) →L[ℂ] ℂ := by
  have hInt (g : C(K, ℂ)) : Integrable (fun x => g x * χ x) μ :=
    (g.continuous.mul χ.continuous).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let L : C(K, ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun g => ∫ x, g x * χ x ∂μ
      map_add' := by
        intro f g
        simp only [ContinuousMap.add_apply, add_mul, integral_add (hInt f) (hInt g)]
      map_smul' := by
        intro c g
        simp only [ContinuousMap.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc, integral_const_mul] }
  refine L.mkContinuous (μ.real univ) fun g => ?_
  change ‖∫ x, g x * χ x ∂μ‖ ≤ μ.real univ * ‖g‖
  rw [mul_comm]
  apply norm_integral_le_of_norm_le_const
  filter_upwards [] with x
  rw [norm_mul, hχ x, mul_one]
  exact g.norm_coe_le_norm x

/-- The Mellin integral at a unitary compact character in log-norm coordinates. -/
def compactFactorMellin (f : ℝ → C(K, ℂ)) (χ : C(K, ℂ)) (z : ℂ) : ℂ :=
  ∫ t : ℝ, Complex.exp (z * (t : ℂ)) * (∫ x, f t x * χ x ∂μ)

private theorem compactFactorMellin_fourier {f : ℝ → C(K, ℂ)}
    (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) (χ : C(K, ℂ)) (hχ : ∀ x, ‖χ x‖ = 1)
    (z : ℂ) :
    compactFactorMellin μ f χ z =
      compactCharacterIntegral μ χ hχ
        (𝓕 (fun x : ℝ => Real.exp (z.re * x) • f x) (-z.im / (2 * Real.pi))) := by
  let w (t : ℝ) := Real.exp (z.re * t) • f t
  let L := compactCharacterIntegral μ χ hχ
  let y := -z.im / (2 * Real.pi)
  have hw : Continuous w := (show Continuous (fun t : ℝ => Real.exp (z.re * t)) by fun_prop).smul
    hf.continuous
  have hi : Integrable w := hw.integrable_of_hasCompactSupport (by
    change HasCompactSupport ((fun t : ℝ => Real.exp (z.re * t)) • f)
    exact hc.smul_left)
  change _ = L (𝓕 w y)
  rw [Real.fourier_eq']
  have he (t : ℝ) :
      L (Complex.exp (-(2 * Real.pi * y * t) * Complex.I) • w t) =
        Complex.exp (z * (t : ℂ)) * (∫ x, f t x * χ x ∂μ) := by
    rw [map_smul]
    have hL : L (w t) = (Real.exp (z.re * t) : ℂ) * ∫ x, f t x * χ x ∂μ := by
      have hwc : w t = (Real.exp (z.re * t) : ℂ) • f t := by
        ext x
        change (Real.exp (z.re * t) : ℝ) • (f t x) = (Real.exp (z.re * t) : ℂ) • (f t x)
        simp only [Complex.real_smul, smul_eq_mul]
      rw [hwc, map_smul]
      rfl
    rw [hL, smul_eq_mul, ← mul_assoc, Complex.ofReal_exp, ← Complex.exp_add]
    congr 2
    have hp : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    have hy : -(2 * Real.pi * y * t) = z.im * t := by
      dsimp [y]
      field_simp
    have hyc : (-(2 * (Real.pi : ℂ) * (y : ℂ) * (t : ℂ))) = ((z.im * t : ℝ) : ℂ) := by
      exact_mod_cast hy
    rw [hyc]
    push_cast
    calc
      _ = ((z.re : ℂ) + z.im * Complex.I) * (t : ℂ) := by ring
      _ = _ := congrArg (· * (t : ℂ)) (Complex.re_add_im z)
  have hkernel : Integrable (fun t : ℝ => Complex.exp (-(2 * Real.pi * y * t) * Complex.I) • w t) := by
    apply hi.norm.mono' _ (Filter.Eventually.of_forall fun t => ?_)
    · exact ((show Continuous (fun t : ℝ => Complex.exp (-(2 * Real.pi * y * t) * Complex.I)) by
        fun_prop).smul hw).aestronglyMeasurable
    · rw [norm_smul]
      simp [Complex.norm_exp]
  have hfou (t : ℝ) :
      Complex.exp (↑(-2 * Real.pi * inner ℝ t y) * Complex.I) • w t =
        Complex.exp (-(2 * Real.pi * y * t) * Complex.I) • w t := by
    congr 2
    simp only [Real.inner_apply, Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_ofNat]
    ring
  simp_rw [hfou]
  rw [← L.integral_comp_comm hkernel]
  apply integral_congr_ae
  filter_upwards [] with t
  exact (he t).symm

/-- The bound is uniform in the compact character and in the real part
of the Mellin variable on a fixed strip. -/
theorem compactFactorMellin_weighted_bound {f : ℝ → C(K, ℂ)}
    (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) (a b : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (χ : C(K, ℂ)), (∀ x, ‖χ x‖ = 1) →
      ∀ z : ℂ, z.re ∈ Icc a b →
        (1 + z.im ^ 2) * ‖compactFactorMellin μ f χ z‖ ≤ C := by
  obtain ⟨C, hC, hbound⟩ := compactProfile_fourier_weighted_bound hf hc a b
  refine ⟨μ.real univ * C, mul_nonneg ENNReal.toReal_nonneg hC, ?_⟩
  intro χ hχ z hz
  rw [compactFactorMellin_fourier μ hf hc χ hχ]
  let g := 𝓕 (fun x : ℝ => Real.exp (z.re * x) • f x) (-z.im / (2 * Real.pi))
  have hnorm : ‖compactCharacterIntegral μ χ hχ g‖ ≤ ‖g‖ * μ.real univ := by
    change ‖∫ x, g x * χ x ∂μ‖ ≤ _
    apply norm_integral_le_of_norm_le_const
    filter_upwards [] with x
    rw [norm_mul, hχ x, mul_one]
    exact g.norm_coe_le_norm x
  have he : 2 * Real.pi * |(-z.im / (2 * Real.pi))| = |z.im| := by
    rw [abs_div, abs_neg, abs_of_pos (by positivity : 0 < 2 * Real.pi), mul_div_cancel₀]
    positivity
  have hB := hbound z.re hz (-z.im / (2 * Real.pi))
  rw [he, sq_abs] at hB
  calc
    _ ≤ (1 + z.im ^ 2) * (‖g‖ * μ.real univ) := mul_le_mul_of_nonneg_left hnorm (by positivity)
    _ = μ.real univ * ((1 + z.im ^ 2) * ‖g‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hB ENNReal.toReal_nonneg

/-- Corrected B.4.4.8. A common vertical strip and a dyadic count of order
T log T guarantee absolute Mellin summability, uniformly across unitary
characters of the compact factor. -/
theorem compactFactorMellin_absoluteSum_of_dyadic_count
    {Shell : ℕ → Type*} [∀ n, Fintype (Shell n)]
    {f : ℝ → C(K, ℂ)} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f)
    (χ : (Σ n, Shell n) → C(K, ℂ)) (hχ : ∀ i x, ‖χ i x‖ = 1)
    (z : (Σ n, Shell n) → ℂ) (w : (Σ n, Shell n) → ℕ)
    {a b C : ℝ} (hstrip : ∀ i, (z i).re ∈ Icc a b)
    (hlower : ∀ n (i : Shell n), (2 : ℝ) ^ n ≤ max 1 |(z ⟨n, i⟩).im|)
    (hcount : ∀ n, (∑ i : Shell n, (w ⟨n, i⟩ : ℝ)) ≤ C * ((n : ℝ) + 1) * 2 ^ n) :
    Summable (fun i => (w i : ℝ) * ‖compactFactorMellin μ f (χ i) (z i)‖) := by
  obtain ⟨M, hM, hbound⟩ := compactFactorMellin_weighted_bound μ hf hc a b
  have hsum := (dyadic_zero_count_summable (fun i => (z i).im) w hlower hcount).mul_left M
  apply hsum.of_nonneg_of_le (fun _ => by positivity)
  intro i
  have hle : ‖compactFactorMellin μ f (χ i) (z i)‖ ≤ M / (1 + (z i).im ^ 2) := by
    apply (le_div_iff₀ (by positivity)).mpr
    rw [mul_comm]
    exact hbound (χ i) (hχ i) (z i) (hstrip i)
  calc
    _ ≤ (w i : ℝ) * (M / (1 + (z i).im ^ 2)) :=
      mul_le_mul_of_nonneg_left hle (Nat.cast_nonneg (w i))
    _ = _ := by ring

/-- The logarithmic product Haar measure realizes the iterated Mellin integral
as the integral of the test against the actual norm-twisted character. -/
theorem compactFactorMellin_eq_product_integral {f : ℝ → C(K, ℂ)}
    (hf : Continuous f) (hc : HasCompactSupport f) (χ : C(K, ℂ)) (z : ℂ) :
    compactFactorMellin μ f χ z =
      ∫ p : ℝ × K, f p.1 p.2 * (Complex.exp (z * (p.1 : ℂ)) * χ p.2)
        ∂(volume.prod μ) := by
  let g (p : ℝ × K) := Complex.exp (z * (p.1 : ℂ)) * (f p.1 p.2 * χ p.2)
  have hev : Continuous (fun p : ℝ × K => f p.1 p.2) :=
    continuous_eval.comp ((hf.comp continuous_fst).prodMk continuous_snd)
  have hcont : Continuous g :=
    (show Continuous (fun p : ℝ × K => Complex.exp (z * (p.1 : ℂ))) by fun_prop).mul
      (hev.mul (χ.continuous.comp continuous_snd))
  have hcomp : HasCompactSupport g := by
    apply HasCompactSupport.of_support_subset_isCompact (hc.prod (isCompact_univ (X := K)))
    intro p hp
    refine ⟨subset_tsupport f ?_, mem_univ _⟩
    intro h
    exact hp (by simp [g, h])
  have hint : Integrable g (volume.prod μ) := hcont.integrable_of_hasCompactSupport hcomp
  have horder : (fun p : ℝ × K => f p.1 p.2 * (Complex.exp (z * (p.1 : ℂ)) * χ p.2)) = g := by
    funext p
    dsimp [g]
    ring
  rw [horder, integral_prod _ hint]
  change (∫ t : ℝ, Complex.exp (z * (t : ℂ)) * (∫ x, f t x * χ x ∂μ)) =
    ∫ t : ℝ, ∫ x, g (t, x) ∂μ
  simp only [g, integral_const_mul]

/-- View a jointly continuous profile on a compact factor as a curve in
the space of continuous functions with its uniform norm. -/
def curryCompactProfile (f : ℝ × K → ℂ) (hf : Continuous f) (t : ℝ) : C(K, ℂ) :=
  ⟨fun k => f (t, k), hf.comp (continuous_const.prodMk continuous_id)⟩

theorem curryCompactProfile_continuous (f : ℝ × K → ℂ) (hf : Continuous f) :
    Continuous (curryCompactProfile f hf) :=
  ContinuousMap.continuous_of_continuous_uncurry _ hf

/-- Continuous scalar derivatives in the log variable on a compact factor
give derivatives in the uniform norm. -/
theorem curryCompactProfile_hasDerivAt
    (f d : ℝ × K → ℂ) (hf : Continuous f) (hd : Continuous d)
    (hD : ∀ t k, HasDerivAt (fun x : ℝ => f (x, k)) (d (t, k)) t) (t : ℝ) :
    HasDerivAt (curryCompactProfile f hf) (curryCompactProfile d hd t) t := by
  apply hasDerivAt_iff_isLittleO.mpr
  apply Asymptotics.isLittleO_iff.mpr
  intro ε hε
  have hloc (k : K) : ∀ᶠ z : ℝ × K in 𝓝 (t, k), ‖d z - d (t, z.2)‖ < ε :=
    ((hd.sub (hd.comp (continuous_const.prodMk continuous_snd))).norm.continuousAt
      (Iio_mem_nhds (by simpa using hε)))
  have huni : ∀ᶠ u : ℝ in 𝓝 t, ∀ k ∈ (univ : Set K), ‖d (u, k) - d (t, k)‖ < ε :=
    isCompact_univ.eventually_forall_of_forall_eventually fun k _ => hloc k
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp huni
  filter_upwards [Metric.ball_mem_nhds t hr] with u hu
  apply (ContinuousMap.norm_le _ (mul_nonneg hε.le (norm_nonneg _))).mpr
  intro k
  let R : ℝ → ℂ := (fun s => f (s, k)) - fun s => (s - t) • d (t, k)
  have hR (s : ℝ) : HasDerivAt R (d (s, k) - d (t, k)) s := by
    have h := (hD s k).sub (((hasDerivAt_id s).sub_const t).smul_const (d (t, k)))
    simpa only [R, id_eq, one_smul] using h
  have hbound (s : ℝ) (hs : s ∈ Metric.ball t r) : ‖deriv R s‖ ≤ ε := by
    rw [(hR s).deriv]
    exact (hball hs k (mem_univ _)).le
  have h := (convex_ball t r).norm_image_sub_le_of_norm_deriv_le
    (fun s _ => (hR s).differentiableAt) hbound (Metric.mem_ball_self hr) hu
  change ‖f (u, k) - f (t, k) - (u - t) • d (t, k)‖ ≤ _
  exact (show R u - R t = f (u, k) - f (t, k) - (u - t) • d (t, k) by
    change f (u, k) - (u - t) • d (t, k) - (f (t, k) - (t - t) • d (t, k)) = _
    rw [sub_self, zero_smul, sub_zero]
    abel) ▸ h

/-- Jointly continuous first and second log derivatives suffice for the
uniform-norm regularity of a compact-factor test. -/
theorem curryCompactProfile_contDiff_two
    (f d e : ℝ × K → ℂ) (hf : Continuous f) (hd : Continuous d) (he : Continuous e)
    (hD : ∀ t k, HasDerivAt (fun x : ℝ => f (x, k)) (d (t, k)) t)
    (hE : ∀ t k, HasDerivAt (fun x : ℝ => d (x, k)) (e (t, k)) t) :
    ContDiff ℝ 2 (curryCompactProfile f hf) := by
  have hD' := curryCompactProfile_hasDerivAt f d hf hd hD
  have hE' := curryCompactProfile_hasDerivAt d e hd he hE
  have hd' : ContDiff ℝ 1 (curryCompactProfile d hd) := by
    apply contDiff_one_iff_deriv.mpr
    refine ⟨fun t => (hE' t).differentiableAt, ?_⟩
    rw [show deriv (curryCompactProfile d hd) = curryCompactProfile e he from funext fun t =>
      (hE' t).deriv]
    exact curryCompactProfile_continuous e he
  rw [← one_add_one_eq_two]
  refine contDiff_succ_iff_deriv.mpr ⟨fun t => (hD' t).differentiableAt, by simp, ?_⟩
  rw [show deriv (curryCompactProfile f hf) = curryCompactProfile d hd from funext fun t =>
    (hD' t).deriv]
  exact hd'

variable [CommGroup K] [IsTopologicalGroup K]

private def complexCompactCharacter (χ : PontryaginDual K) : C(K, ℂ) :=
  ⟨fun x => (χ x : ℂ), continuous_subtype_val.comp χ.continuous⟩

/-- The repaired convergence theorem written for genuine group characters and
the product Haar integral in a logarithmic splitting. -/
theorem compactProductMellin_absoluteSum_of_dyadic_count
    {Shell : ℕ → Type*} [∀ n, Fintype (Shell n)]
    {f : ℝ → C(K, ℂ)} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f)
    (χ : (Σ n, Shell n) → PontryaginDual K)
    (z : (Σ n, Shell n) → ℂ) (w : (Σ n, Shell n) → ℕ)
    {a b C : ℝ} (hstrip : ∀ i, (z i).re ∈ Icc a b)
    (hlower : ∀ n (i : Shell n), (2 : ℝ) ^ n ≤ max 1 |(z ⟨n, i⟩).im|)
    (hcount : ∀ n, (∑ i : Shell n, (w ⟨n, i⟩ : ℝ)) ≤ C * ((n : ℝ) + 1) * 2 ^ n) :
    Summable (fun i => (w i : ℝ) * ‖∫ p : ℝ × K,
      f p.1 p.2 * (Complex.exp (z i * (p.1 : ℂ)) * (χ i p.2 : ℂ)) ∂(volume.prod μ)‖) := by
  have h := compactFactorMellin_absoluteSum_of_dyadic_count μ hf hc
    (fun i => complexCompactCharacter (χ i)) (fun i x => Circle.norm_coe (χ i x))
    z w hstrip hlower hcount
  refine h.congr fun i => ?_
  rw [compactFactorMellin_eq_product_integral μ hf.continuous hc]
  rfl

/-- Repaired Lemma B.4.4.8 for a smooth compactly supported test on the
logarithmic product. The two log derivatives are jointly continuous and
there is a quantitative count over all sampled characters. -/
theorem smoothCompactProductMellin_absoluteSum_of_dyadic_count
    {Shell : ℕ → Type*} [∀ n, Fintype (Shell n)]
    {f d e : ℝ × K → ℂ} (hf : Continuous f) (hd : Continuous d) (he : Continuous e)
    (hc : HasCompactSupport f)
    (hD : ∀ t k, HasDerivAt (fun x : ℝ => f (x, k)) (d (t, k)) t)
    (hE : ∀ t k, HasDerivAt (fun x : ℝ => d (x, k)) (e (t, k)) t)
    (χ : (Σ n, Shell n) → PontryaginDual K)
    (z : (Σ n, Shell n) → ℂ) (w : (Σ n, Shell n) → ℕ)
    {a b C : ℝ} (hstrip : ∀ i, (z i).re ∈ Icc a b)
    (hlower : ∀ n (i : Shell n), (2 : ℝ) ^ n ≤ max 1 |(z ⟨n, i⟩).im|)
    (hcount : ∀ n, (∑ i : Shell n, (w ⟨n, i⟩ : ℝ)) ≤ C * ((n : ℝ) + 1) * 2 ^ n) :
    Summable (fun i => (w i : ℝ) * ‖∫ p : ℝ × K,
      f p * (Complex.exp (z i * (p.1 : ℂ)) * (χ i p.2 : ℂ)) ∂(volume.prod μ)‖) := by
  have hcur : HasCompactSupport (curryCompactProfile f hf) := by
    apply HasCompactSupport.of_support_subset_isCompact (hc.image continuous_fst)
    intro t ht
    by_contra hn
    apply ht
    apply ContinuousMap.ext
    intro k
    change f (t, k) = 0
    exact image_eq_zero_of_notMem_tsupport (fun hk => hn ⟨(t, k), hk, rfl⟩)
  exact compactProductMellin_absoluteSum_of_dyadic_count μ
    (curryCompactProfile_contDiff_two f d e hf hd he hD hE) hcur χ z w hstrip hlower hcount

/-- The character coefficient of an invariant test vanishes if the character
is nontrivial on the subgroup of invariance. This applies to the deleted terms
in the proof of B.4.4.9. -/
theorem compactCharacterMellin_zero_of_invariance [μ.IsHaarMeasure]
    (f : ℝ → C(K, ℂ)) (χ : PontryaginDual K) (x : K)
    (hχ : χ x ≠ 1) (hf : ∀ t k, f t (x * k) = f t k) (z : ℂ) :
    compactFactorMellin μ f (complexCompactCharacter χ) z = 0 := by
  suffices h : ∀ t : ℝ, (∫ y, f t y * (χ y : ℂ) ∂μ) = 0 by
    simp [compactFactorMellin, complexCompactCharacter, h]
  intro t
  have he := integral_mul_left_eq_self (μ := μ) (fun y => f t y * (χ y : ℂ)) x
  have hval (y : K) : f t (x * y) * (χ (x * y) : ℂ) =
      (χ x : ℂ) * (f t y * (χ y : ℂ)) := by
    rw [hf, map_mul, Circle.coe_mul]
    ring
  simp_rw [hval, integral_const_mul] at he
  have hn : (χ x : ℂ) - 1 ≠ 0 := by
    apply sub_ne_zero.mpr
    intro hx
    exact hχ (Subtype.ext hx)
  apply (mul_eq_zero.mp ?_).resolve_left hn
  rw [sub_mul, he, one_mul, sub_self]

end CompactFactor

end
end Masullo
