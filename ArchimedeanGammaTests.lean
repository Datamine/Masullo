import ArchimedeanMellinMonomials
import SchwartzGaussian
import HomogeneousThetaMellin
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv

open Filter MeasureTheory Set Topology
open scoped SchwartzMap

namespace Masullo

noncomputable section

attribute [local instance] complexZeta_circleMeasurable

private theorem mellin_exp_mul (b : ℝ) (hb : 0 < b) (s : ℂ) (hs : 0 < s.re) :
    mellin (fun t : ℝ ↦ (Real.exp (-b * t) : ℂ)) s =
      (b : ℂ)^(-s) * Complex.Gamma s := by
  have he : (fun t : ℝ ↦ (Real.exp (-b * t) : ℂ)) =
      fun t : ℝ ↦ (Real.exp (-(b*t)) : ℂ) := by funext t; rw [neg_mul]
  rw [he]
  calc
    _ = (b : ℂ)^(-s) • mellin (fun t : ℝ ↦ (Real.exp (-t) : ℂ)) s :=
      mellin_comp_mul_left (fun t : ℝ ↦ (Real.exp (-t) : ℂ)) s hb
    _ = _ := by rw [← Complex.GammaIntegral_eq_mellin, ← Complex.Gamma_eq_integral hs, smul_eq_mul]

private theorem mellin_exp_square (b : ℝ) (hb : 0 < b) (s : ℂ) (hs : 0 < s.re) :
    mellin (fun t : ℝ ↦ (Real.exp (-b * t^2) : ℂ)) s =
      (2 : ℂ)⁻¹ * ((b : ℂ)^(-(s/2)) * Complex.Gamma (s/2)) := by
  have he : (fun t : ℝ ↦ (Real.exp (-b * t^2) : ℂ)) =
      fun t : ℝ ↦ (Real.exp (-b * (t ^ (2 : ℝ))) : ℂ) := by
    funext t
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [he]
  calc
    _ = |(2 : ℝ)|⁻¹ • mellin (fun t : ℝ ↦ (Real.exp (-b*t) : ℂ)) (s / (2 : ℝ)) :=
      mellin_comp_rpow (fun t : ℝ ↦ (Real.exp (-b*t) : ℂ)) s 2
    _ = _ := by
      have hp : 0 < (s/2).re := by rw [Complex.div_ofNat_re]; positivity
      simp only [abs_of_pos (by norm_num : (0 : ℝ) < 2), Complex.real_smul, Complex.ofReal_inv,
        Complex.ofReal_ofNat, mellin_exp_mul b hb _ hp]

private theorem realGaussian_zeta_germ (a : ℕ) (ha : Even a)
    (g : 𝓢(ℝ, ℂ)) (hg : ∀ t, g t = Real.exp (-Real.pi * ‖t‖^2)) (c : ℂ) :
    realArchimedeanZetaContinued a g =ᶠ[𝓝[≠] c] Complex.Gammaℝ := by
  have hm : Meromorphic Complex.Gammaℝ := by
    intro z
    have h := (realArchZetaDenominator_analytic 0 z).meromorphicAt.inv
    simpa only [realArchZetaDenominator, Nat.zero_mod, Nat.cast_zero, add_zero, Pi.inv_def,
      inv_inv] using h
  refine boundedPoleMellinSpace_unique_germs
    (isOpen_lt (continuous_const (y := (0 : ℝ))) Complex.continuous_re)
    ⟨1, by simp⟩ (realArchimedeanZetaContinued_meromorphic a g) hm ?_ c
  intro z hz
  have hz' : 0 < z.re := hz
  have he : (realZetaProfile a g : ℝ → ℂ) =
      fun t : ℝ ↦ (2 : ℂ) • (Real.exp (-Real.pi * t^2) : ℂ) := by
    funext t
    rw [realZetaProfile_apply, hg t, hg (-t), norm_neg, Real.norm_eq_abs, sq_abs]
    have ha' : (-1 : ℂ) ^ a = 1 := ha.neg_one_pow
    rw [ha', one_mul, smul_eq_mul, two_mul]
  change mellinTaylorContinued (realZetaProfile a g) z = Complex.Gammaℝ z
  have hmellin : mellin (realZetaProfile a g : ℝ → ℂ) z =
      mellinTaylorContinued (realZetaProfile a g : ℝ → ℂ) z :=
    (mellinTaylorContinued_eq_mellin (realZetaProfile a g).smooth'
      (schwartz_radial_rapid _) hz').2
  rw [← hmellin, he, mellin_const_smul,
    mellin_exp_square Real.pi Real.pi_pos z hz', smul_eq_mul, Complex.Gammaℝ_def]
  rw [← mul_assoc, mul_inv_cancel₀ (by norm_num : (2 : ℂ) ≠ 0), one_mul, neg_div]

private theorem add_tendsto_nhdsNE (c a : ℂ) :
    Tendsto (fun z : ℂ ↦ z + a) (𝓝[≠] c) (𝓝[≠] (c + a)) := by
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨(continuous_id.add continuous_const).continuousAt.tendsto.mono_left nhdsWithin_le_nhds, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact fun he ↦ hz (add_right_cancel (mem_singleton_iff.mp he))

/-- A real Gaussian with its parity monomial has precisely the real Euler
factor as its Mellin transform, as an identity of meromorphic germs. -/
theorem exists_realGammaTest_explicit (a : ℕ) :
    ∃ f : 𝓢(ℝ, ℂ),
      (∀ x : ℝ, f x = (x : ℂ) ^ (a % 2) * (Real.exp (-Real.pi * ‖x‖^2) : ℂ)) ∧
      ∀ c : ℂ, realArchimedeanZetaContinued a f =ᶠ[𝓝[≠] c]
        fun z ↦ Complex.Gammaℝ (z + ((a % 2 : ℕ) : ℂ)) := by
  obtain ⟨g, hg⟩ := exists_gaussian_schwartz (E := ℝ) Real.pi Real.pi_pos
  let n := a % 2
  have hEven : Even (a+n) := by
    rw [even_iff_two_dvd, Nat.dvd_iff_mod_eq_zero]
    dsimp [n]
    omega
  refine ⟨realMellinMonomial n g, fun x ↦ by rw [realMellinMonomial_apply, hg],
    fun c ↦ (realMellinMonomial_shift a n g c).trans ?_⟩
  exact (realGaussian_zeta_germ (a+n) hEven g hg (c+n)).comp_tendsto
    (add_tendsto_nhdsNE c n)

theorem exists_realGammaTest (a : ℕ) :
    ∃ f : 𝓢(ℝ, ℂ), ∀ c : ℂ, realArchimedeanZetaContinued a f =ᶠ[𝓝[≠] c]
      fun z ↦ Complex.Gammaℝ (z + ((a % 2 : ℕ) : ℂ)) :=
  (exists_realGammaTest_explicit a).imp fun _ h ↦ h.2

private theorem complexGaussian_zeta_right
    (g : 𝓢(ℂ, ℂ)) (hg : ∀ t, g t = Real.exp (-(2*Real.pi) * ‖t‖^2))
    (s : ℂ) (hs : 0 < s.re) :
    complexArchimedeanZetaContinued complexTamagawaAngularMeasure 0
      ((Real.pi : ℂ)⁻¹ • g) s = Complex.Gammaℂ s := by
  have hprof : complexZetaProfile complexTamagawaAngularMeasure 0 g =
      fun t : ℝ ↦ (4 * (Real.pi : ℂ)) • (Real.exp (-(2*Real.pi) * t^2) : ℂ) := by
    funext t
    unfold complexZetaProfile
    have he (u : Circle) : g (t • (u : ℂ)) = (Real.exp (-(2*Real.pi) * t^2) : ℂ) := by
      rw [hg, norm_smul, Circle.norm_coe, mul_one, Real.norm_eq_abs, sq_abs]
    simp only [zpow_zero, one_mul]
    simp_rw [he]
    rw [integral_const, measureReal_def]
    change (complexTamagawaAngularMeasure.real univ : ℝ) • _ = _
    rw [complexTamagawaAngularMeasure_mass, Complex.real_smul, Complex.ofReal_mul,
      Complex.ofReal_ofNat]
    rfl
  have h2 : 0 < (2*s).re := by
    norm_num [Complex.mul_re]
    positivity
  have h := (complexArchimedeanZetaContinued_eq_radial complexTamagawaAngularMeasure 0 g hs).2
  rw [hprof, mellin_const_smul,
    mellin_exp_square (2*Real.pi) (by positivity) _ h2] at h
  have he : (2*s)/2 = s := by ring
  rw [he, smul_eq_mul] at h
  rw [← complexArchimedeanZetaContinuedCLM_apply, map_smul, complexArchimedeanZetaContinuedCLM_apply,
    ← h, Complex.Gammaℂ_def, smul_eq_mul]
  push_cast
  field_simp [Real.pi_ne_zero, Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
  ring

private theorem complexGaussian_zeta_germ
    (g : 𝓢(ℂ, ℂ)) (hg : ∀ t, g t = Real.exp (-(2*Real.pi) * ‖t‖^2)) (c : ℂ) :
    complexArchimedeanZetaContinued complexTamagawaAngularMeasure 0
      ((Real.pi : ℂ)⁻¹ • g) =ᶠ[𝓝[≠] c] Complex.Gammaℂ := by
  have hm : Meromorphic Complex.Gammaℂ := by
    intro z
    have h := (complexArchZetaDenominator_analytic 0 z).meromorphicAt.inv
    simpa only [complexArchZetaDenominator, Int.natAbs_zero, Nat.cast_zero, zero_div,
      add_zero, Pi.inv_def, inv_inv] using h
  refine boundedPoleMellinSpace_unique_germs
    (isOpen_lt (continuous_const (y := (0 : ℝ))) Complex.continuous_re) ⟨1, by simp⟩
    (complexArchimedeanZetaContinued_meromorphic _ _ _) hm ?_ c
  exact fun z hz ↦ complexGaussian_zeta_right g hg z hz

/-- A complex Gaussian with the matching angular monomial has precisely
the complex Euler factor as its Mellin transform, in the Tamagawa normalization. -/
theorem exists_complexGammaTest_explicit (m : ℤ) :
    ∃ f : 𝓢(ℂ, ℂ),
      (∀ x : ℂ, f x = (x ^ (-m).toNat * star x ^ m.toNat) *
        ((Real.pi : ℂ)⁻¹ * (Real.exp (-(2 * Real.pi) * ‖x‖^2) : ℂ))) ∧
      ∀ c : ℂ,
        complexArchimedeanZetaContinued complexTamagawaAngularMeasure m f =ᶠ[𝓝[≠] c]
          fun z ↦ Complex.Gammaℂ (z + (m.natAbs : ℂ) / 2) := by
  obtain ⟨g, hg⟩ := exists_gaussian_schwartz (E := ℂ) (2*Real.pi) (by positivity)
  let p := (-m).toNat
  let q := m.toNat
  let b := (Real.pi : ℂ)⁻¹ • g
  have hpq : m + (p : ℤ) - q = 0 := by dsimp [p,q]; omega
  have hpq' : p + q = m.natAbs := by dsimp [p,q]; omega
  have hshift : ((p : ℂ) + q) / 2 = (m.natAbs : ℂ) / 2 := by
    rw [← Nat.cast_add, hpq']
  refine ⟨complexMellinMonomial p q b, ?_, fun c ↦ ?_⟩
  · intro x
    rw [complexMellinMonomial_apply]
    change _ * ((Real.pi : ℂ)⁻¹ * g x) = _
    rw [hg]
  have hs := complexMellinMonomial_shift complexTamagawaAngularMeasure m p q b c
  rw [hpq, hshift] at hs
  refine hs.trans ?_
  let a : ℂ := (m.natAbs : ℂ) / 2
  exact (complexGaussian_zeta_germ g hg (c+a)).comp_tendsto (add_tendsto_nhdsNE c a)

theorem exists_complexGammaTest (m : ℤ) :
    ∃ f : 𝓢(ℂ, ℂ), ∀ c : ℂ,
      complexArchimedeanZetaContinued complexTamagawaAngularMeasure m f =ᶠ[𝓝[≠] c]
        fun z ↦ Complex.Gammaℂ (z + (m.natAbs : ℂ) / 2) :=
  (exists_complexGammaTest_explicit m).imp fun _ h ↦ h.2

end

end Masullo
