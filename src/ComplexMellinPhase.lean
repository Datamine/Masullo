import ArchimedeanMellinMonomials
import ComplexLogFourier
import SchwartzGaussian

open Filter MeasureTheory Set
open scoped FourierTransform LineDeriv SchwartzMap Topology

namespace Masullo

noncomputable section

local notation "π" => Real.pi
local notation "I" => Complex.I
local notation "Tests" => 𝓢(ℂ, ℂ)

private def gaussian (b : ℝ) (hb : 0 < b) : Tests :=
  (exists_gaussian_schwartz (E := ℂ) b hb).choose

private theorem gaussian_apply (b : ℝ) (hb : 0 < b) (z : ℂ) :
    gaussian b hb z = (Real.exp (-b * ‖z‖ ^ 2) : ℂ) :=
  (exists_gaussian_schwartz (E := ℂ) b hb).choose_spec z

private theorem gaussian_lineDeriv (b : ℝ) (hb : 0 < b) (v z : ℂ) :
    ∂_{v} (gaussian b hb) z = (-(2 * b : ℝ) * inner ℝ z v : ℝ) • gaussian b hb z := by
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
  have h := (((hasStrictFDerivAt_norm_sq z).hasFDerivAt.const_mul (-b)).exp)
  have hc := Complex.ofRealCLM.hasFDerivAt.comp z h
  have hg : (gaussian b hb : ℂ → ℂ) = Complex.ofRealCLM ∘ (fun z : ℂ ↦ Real.exp (-b * ‖z‖ ^ 2)) :=
    funext (gaussian_apply b hb)
  rw [hg, hc.fderiv]
  simp only [ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply,
    smul_apply, innerSL_apply_apply, smul_eq_mul, Function.comp_apply,
    Complex.real_smul, ← Complex.ofReal_mul]
  congr 1
  ring

private theorem inner_real_coordinates (z : ℂ) :
    (inner ℝ z (1 : ℂ) : ℂ) + I * (inner ℝ z I : ℂ) = z := by
  simp only [Complex.inner, one_mul, Complex.conj_re, Complex.mul_re,
    Complex.I_re, Complex.I_im, zero_mul, Complex.conj_im, one_mul, zero_sub, neg_neg]
  rw [mul_comm I]
  exact Complex.re_add_im z

private theorem fourier_gaussian (b : ℝ) (hb : 0 < b) (w : ℂ) :
    (𝓕 (gaussian b hb)) w = (((π / b) * Real.exp (-(π ^ 2 * ‖w‖ ^ 2 / b)) : ℝ) : ℂ) := by
  have hg : (gaussian b hb : ℂ → ℂ) = fun z : ℂ ↦ Complex.exp (-(b : ℂ) * (‖z‖ : ℂ) ^ 2) := by
    funext z
    rw [gaussian_apply, Complex.ofReal_exp]
    push_cast
    rfl
  rw [SchwartzMap.fourier_coe, hg, fourier_gaussian_innerProductSpace (by simpa using hb : 0 < (b : ℂ).re),
    Complex.finrank_real_complex, show ((2 : ℕ) : ℂ) / 2 = 1 by norm_num,
    Complex.cpow_one]
  push_cast
  rw [neg_mul, neg_div]

private theorem fourier_z_gaussian (b : ℝ) (hb : 0 < b) (w : ℂ) :
    (𝓕 (complexMellinMonomial 1 0 (gaussian b hb))) w =
      (-(π : ℂ) * I / b) * w * (𝓕 (gaussian b hb)) w := by
  let g := gaussian b hb
  let P := complexMellinMonomial 1 0 g
  have hD : (∂_{(1 : ℂ)} g) + I • (∂_{I} g) = (-(2 * b : ℝ) : ℂ) • P := by
    ext z
    simp only [add_apply, smul_apply, g, gaussian_lineDeriv, P, complexMellinMonomial_apply,
      pow_zero, pow_one, mul_one, Complex.real_smul, smul_eq_mul,
      Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_neg]
    have h := inner_real_coordinates z
    linear_combination ((-(2 * (b : ℂ))) * g z) * h
  have h := congrArg (fun a : Tests ↦ (𝓕 a : Tests) w) hD
  rw [FourierTransform.fourier_add, FourierTransform.fourier_smul, FourierTransform.fourier_smul,
    SchwartzMap.fourier_lineDerivOp_eq, SchwartzMap.fourier_lineDerivOp_eq] at h
  have H (v : ℂ) : (fun z : ℂ ↦ inner ℝ z v).HasTemperateGrowth :=
    ((innerSL ℝ).flip v).hasTemperateGrowth
  simp only [add_apply, smul_apply, SchwartzMap.smulLeftCLM_apply_apply (H _),
    Complex.real_smul, smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_ofNat] at h
  have ht := inner_real_coordinates w
  change (𝓕 P : Tests) w = _
  have hb' : (b : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hb.ne'
  field_simp [hb']
  linear_combination (h - (2 * (π : ℂ) * I * (𝓕 g : Tests) w) * ht) / 2

private def traceGauss : Tests := gaussian (2 * π) (by positivity)

private def traceGaussZ : Tests := complexMellinMonomial 1 0 traceGauss

/-- The first angular Gaussian acquires the unit `-i` for the negative trace sign. -/
theorem complexTraceFourier_firstAngularGaussian (z : ℂ) :
    complexTraceFourier traceGaussZ z = -I * star z * traceGauss z := by
  rw [complexTraceFourier, traceGaussZ, traceGauss, fourier_z_gaussian, fourier_gaussian,
    gaussian_apply, norm_smul, Complex.conjLIE.norm_map, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
    Complex.conjLIE_apply, Complex.real_smul, Complex.real_smul]
  have harg : -(π ^ 2 * (2 * ‖z‖) ^ 2 / (2 * π)) = -(2 * π) * ‖z‖ ^ 2 := by
    field_simp [Real.pi_ne_zero]
  rw [harg]
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
  simp only [Complex.star_def]

attribute [local instance] complexZeta_circleMeasurable

private def firstAngularGaussianFourier : Tests := -I • complexMellinMonomial 0 1 traceGauss

private theorem firstAngularGaussianFourier_apply (z : ℂ) :
    firstAngularGaussianFourier z = complexTraceFourier traceGaussZ z := by
  rw [complexTraceFourier_firstAngularGaussian]
  simp [firstAngularGaussianFourier, mul_assoc]

private theorem zeta_firstAngularGaussian_profile (t : ℝ) :
    complexZetaProfile complexTamagawaAngularMeasure (-1) traceGaussZ t =
      ((4 * π * (t * Real.exp (-(2 * π) * t ^ 2)) : ℝ) : ℂ) := by
  have he (u : Circle) : (u : ℂ) ^ (-1 : ℤ) * traceGaussZ (t • (u : ℂ)) =
      ((t * Real.exp (-(2 * π) * t ^ 2) : ℝ) : ℂ) := by
    have hn : ‖t • (u : ℂ)‖ = |t| := by
      rw [norm_smul, Circle.norm_coe, mul_one, Real.norm_eq_abs]
    rw [traceGaussZ, complexMellinMonomial_apply, pow_one, pow_zero, mul_one, traceGauss,
      gaussian_apply, hn, sq_abs, Complex.real_smul, zpow_neg_one, Complex.ofReal_mul]
    have hu : (u : ℂ) ≠ 0 := Circle.coe_ne_zero u
    field_simp [hu]
  unfold complexZetaProfile
  simp_rw [he]
  rw [integral_const, complexTamagawaAngularMeasure_mass, Complex.real_smul, ← Complex.ofReal_mul]

private theorem zeta_firstAngularGaussianFourier_profile (t : ℝ) :
    complexZetaProfile complexTamagawaAngularMeasure 1 firstAngularGaussianFourier t =
      -I * complexZetaProfile complexTamagawaAngularMeasure (-1) traceGaussZ t := by
  have hc (u : Circle) : (u : ℂ) ^ (1 : ℤ) * firstAngularGaussianFourier (t • (u : ℂ)) =
      -I * ((t * Real.exp (-(2 * π) * t ^ 2) : ℝ) : ℂ) := by
    have hn : ‖t • (u : ℂ)‖ = |t| := by
      rw [norm_smul, Circle.norm_coe, mul_one, Real.norm_eq_abs]
    have hu : (u : ℂ) ≠ 0 := Circle.coe_ne_zero u
    have ht : star (t : ℂ) = (t : ℂ) := Complex.conj_ofReal t
    have hU : star (u : ℂ) = (u : ℂ)⁻¹ :=
      (Circle.coe_inv_eq_conj u).symm.trans (Circle.coe_inv u)
    rw [firstAngularGaussianFourier_apply, complexTraceFourier_firstAngularGaussian, traceGauss,
      gaussian_apply, hn, sq_abs, Complex.real_smul, star_mul', ht, hU, zpow_one,
      Complex.ofReal_mul]
    field_simp [hu]
  rw [zeta_firstAngularGaussian_profile, complexZetaProfile]
  simp_rw [hc]
  rw [integral_const, complexTamagawaAngularMeasure_mass, Complex.real_smul, Complex.ofReal_mul]
  push_cast
  ring

local notation "half" => ((1 : ℂ) / 2)

private theorem zeta_firstAngularGaussian_center :
    complexArchimedeanZetaContinued complexTamagawaAngularMeasure (-1) traceGaussZ half =
      (1 : ℂ) := by
  have h := (complexArchimedeanZetaContinued_eq_radial complexTamagawaAngularMeasure
    (-1) traceGaussZ (s := half) (by norm_num [Complex.div_ofNat_re])).2
  rw [show (2 : ℂ) * half = 1 by ring] at h
  rw [← h]
  have hpow (t : ℝ) : (t : ℂ) ^ ((1 : ℂ) - 1) = 1 := by simp
  simp only [mellin, hpow, one_smul, zeta_firstAngularGaussian_profile, integral_complex_ofReal]
  have hchange := integral_comp_rpow_Ioi_of_pos (p := 2)
    (g := fun u : ℝ ↦ Real.exp (-(2 * π) * u)) (by norm_num)
  simp only [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, Real.rpow_two,
    smul_eq_mul, mul_assoc, integral_const_mul] at hchange
  have he : (∫ t in Ioi (0 : ℝ), Real.exp (-(2 * π) * t)) = (2 * π)⁻¹ := by
    have hh := integral_exp_mul_Ioi (a := -(2 * π)) (neg_neg_of_pos Real.two_pi_pos) 0
    simpa using hh
  rw [integral_const_mul]
  have hg : (∫ t in Ioi (0 : ℝ), t * Real.exp (-(2 * π) * t ^ 2)) = (4 * π)⁻¹ := by
    rw [he] at hchange
    have hπ : (2 * π)⁻¹ = 2 * (4 * π)⁻¹ := by
      field_simp [Real.pi_ne_zero]
      norm_num
    linarith
  rw [hg, mul_inv_cancel₀ (by positivity : (4 * π : ℝ) ≠ 0), Complex.ofReal_one]

private theorem zeta_firstAngularGaussianFourier_center :
    complexArchimedeanZetaContinued complexTamagawaAngularMeasure 1 firstAngularGaussianFourier half = -I := by
  have h₁ := (complexArchimedeanZetaContinued_eq_radial complexTamagawaAngularMeasure
    1 firstAngularGaussianFourier (s := half) (by norm_num [Complex.div_ofNat_re])).2
  have h₀ := (complexArchimedeanZetaContinued_eq_radial complexTamagawaAngularMeasure
    (-1) traceGaussZ (s := half) (by norm_num [Complex.div_ofNat_re])).2
  rw [show (2 : ℂ) * half = 1 by ring] at h₀ h₁
  rw [← h₁, mellin, show (1 : ℂ) - 1 = 0 by ring]
  simp_rw [Complex.cpow_zero, one_smul, zeta_firstAngularGaussianFourier_profile, integral_const_mul]
  have hM : (∫ t in Ioi (0 : ℝ), complexZetaProfile complexTamagawaAngularMeasure (-1) traceGaussZ t) = 1 := by
    have h := h₀.trans zeta_firstAngularGaussian_center
    simpa only [mellin, sub_self, Complex.cpow_zero, one_smul] using h
  rw [hM, mul_one]

/-- A real phase cannot implement the complex local Fourier reflection at the center
for angular weight `-1`. In particular the printed phase `(-1)^|n|` fails. -/
theorem complexMellin_printed_phase_false (c : ℝ) :
    ∃ f fHat : Tests, (∀ z, fHat z = complexTraceFourier f z) ∧
      complexArchimedeanZetaContinued complexTamagawaAngularMeasure (-1) f half ≠
        (c : ℂ) * complexArchimedeanZetaContinued complexTamagawaAngularMeasure 1 fHat half := by
  refine ⟨traceGaussZ, firstAngularGaussianFourier, firstAngularGaussianFourier_apply, ?_⟩
  rw [zeta_firstAngularGaussian_center, zeta_firstAngularGaussianFourier_center]
  intro h
  have hr := congrArg Complex.re h
  simp [Complex.mul_re] at hr

/-- The Gaussian determines the scalar for the negative trace Fourier sign. -/
theorem complexMellin_firstAngularGaussian_phase (c : ℂ) :
    complexArchimedeanZetaContinued complexTamagawaAngularMeasure (-1) traceGaussZ half =
        c * complexArchimedeanZetaContinued complexTamagawaAngularMeasure 1 firstAngularGaussianFourier half
      ↔ c = I := by
  rw [zeta_firstAngularGaussian_center, zeta_firstAngularGaussianFourier_center]
  have hI : I * -I = 1 := by rw [mul_neg, Complex.I_mul_I, neg_neg]
  constructor
  · intro h
    exact mul_right_cancel₀ (neg_ne_zero.mpr Complex.I_ne_zero) (h.symm.trans hI.symm)
  · rintro rfl
    exact hI.symm

end
end Masullo
