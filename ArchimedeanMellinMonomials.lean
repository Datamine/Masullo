import RealArchimedeanZeta
import ComplexArchimedeanZeta
import RealLogFourierGaussian

open Filter MeasureTheory Set
open scoped SchwartzMap Topology

namespace Masullo

noncomputable section

attribute [local instance] complexZeta_circleMeasurable

/-- Multiplication of real Schwartz tests by the coordinate monomial. -/
def realMellinMonomial (n : ℕ) : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (fun x : ℝ ↦ (x : ℂ) ^ n)

@[simp] theorem realMellinMonomial_apply (n : ℕ) (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    realMellinMonomial n f x = (x : ℂ) ^ n * f x :=
  SchwartzMap.smulLeftCLM_apply_apply (Complex.ofRealCLM.hasTemperateGrowth.pow n) f x

/-- Multiplication of complex Schwartz tests by a mixed coordinate monomial. -/
def complexMellinMonomial (p q : ℕ) : 𝓢(ℂ, ℂ) →L[ℂ] 𝓢(ℂ, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (fun z : ℂ ↦ z ^ p * star z ^ q)

@[simp] theorem complexMellinMonomial_apply (p q : ℕ) (f : 𝓢(ℂ, ℂ)) (z : ℂ) :
    complexMellinMonomial p q f z = (z ^ p * star z ^ q) * f z :=
  SchwartzMap.smulLeftCLM_apply_apply
    ((Function.HasTemperateGrowth.id'.pow p).mul (Complex.conjCLE.hasTemperateGrowth.pow q)) f z

private theorem mellinMonomial_germs {f g : ℂ → ℂ} (hf : Meromorphic f) (hg : Meromorphic g)
    (he : EqOn f g {z | 0 < z.re}) (z : ℂ) : f =ᶠ[𝓝[≠] z] g := by
  let d := f - g
  have hd : Meromorphic d := hf.sub hg
  have hopen : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have h1 : (1 : ℂ) ∈ {w : ℂ | 0 < w.re} := by simp
  have hz₀ : d =ᶠ[𝓝[≠] (1 : ℂ)] 0 := by
    filter_upwards [(eventually_mem_set.mpr (hopen.mem_nhds h1)).filter_mono nhdsWithin_le_nhds] with w hw
    exact sub_eq_zero.mpr (he hw)
  have hp : meromorphicOrderAt d z = ⊤ := by
    by_contra hn
    exact (hd.meromorphicOn (s := (univ : Set ℂ))).meromorphicOrderAt_ne_top_of_isPreconnected
      isPreconnected_univ (mem_univ z) (mem_univ 1) hn (meromorphicOrderAt_eq_top_iff.mpr hz₀)
  exact (meromorphicOrderAt_eq_top_iff.mp hp).mono fun w hw ↦ sub_eq_zero.mp hw

private theorem realMellinMonomial_shift_right (a n : ℕ) (f : 𝓢(ℝ, ℂ)) {s : ℂ}
    (hs : 0 < s.re) : realArchimedeanZetaContinued a (realMellinMonomial n f) s =
      realArchimedeanZetaContinued (a + n) f (s + n) := by
  have hp : (realZetaProfile a (realMellinMonomial n f) : ℝ → ℂ) =
      fun t : ℝ ↦ (t : ℂ) ^ (n : ℂ) • realZetaProfile (a + n) f t := by
    funext t
    rw [realZetaProfile_apply, realMellinMonomial_apply, realMellinMonomial_apply,
      Complex.cpow_natCast, realZetaProfile_apply, Complex.ofReal_neg,
      ← neg_one_mul (t : ℂ), mul_pow, pow_add, smul_eq_mul]
    ring
  have hsn : 0 < (s + (n : ℂ)).re := by
    rw [Complex.add_re, Complex.natCast_re]
    positivity
  unfold realArchimedeanZetaContinued
  calc
    _ = mellin ((realZetaProfile a (realMellinMonomial n f)) : ℝ → ℂ) s :=
      (mellinTaylorContinued_eq_mellin (realZetaProfile a (realMellinMonomial n f)).smooth'
        (schwartz_radial_rapid _) hs).2.symm
    _ = mellin (realZetaProfile (a + n) f : ℝ → ℂ) (s + n) := by
      rw [hp, mellin_cpow_smul]
    _ = _ := (mellinTaylorContinued_eq_mellin (realZetaProfile (a + n) f).smooth'
      (schwartz_radial_rapid _) hsn).2

/-- Corrected real shift in (5.3.3.28): the left test is multiplied by `x^n`. -/
theorem realMellinMonomial_shift (a n : ℕ) (f : 𝓢(ℝ, ℂ)) (s : ℂ) :
    realArchimedeanZetaContinued a (realMellinMonomial n f) =ᶠ[𝓝[≠] s]
      fun z ↦ realArchimedeanZetaContinued (a + n) f (z + n) := by
  apply mellinMonomial_germs (realArchimedeanZetaContinued_meromorphic _ _)
  · intro z
    exact (realArchimedeanZetaContinued_meromorphic (a + n) f (z + n)).comp_analyticAt
      (g := fun w : ℂ ↦ w + n)
      (analyticAt_id.add analyticAt_const)
  · exact fun z hz ↦ realMellinMonomial_shift_right a n f hz

/-- A real Gaussian refutes the version of (5.3.3.28) that omits the multiplier. -/
theorem realMellin_printed_shift_false :
    ∃ f : 𝓢(ℝ, ℂ), realArchimedeanZetaContinued 0 f 1 ≠
      realArchimedeanZetaContinued 1 f 2 := by
  refine ⟨realGaussianPi, ?_⟩
  have hZero : (realZetaProfile 1 realGaussianPi : ℝ → ℂ) = 0 := by
    funext x
    simp only [realZetaProfile_apply, realGaussianPi_apply, neg_sq, pow_one, neg_one_mul,
      add_neg_cancel, Pi.zero_apply]
  have hz : realArchimedeanZetaContinued 1 realGaussianPi 2 = 0 := by
    have h := (mellinTaylorContinued_eq_mellin (realZetaProfile 1 realGaussianPi).smooth'
      (schwartz_radial_rapid _) (s := (2 : ℂ)) (by simp)).2
    change mellin ((realZetaProfile 1 realGaussianPi) : ℝ → ℂ) 2 =
      realArchimedeanZetaContinued 1 realGaussianPi 2 at h
    simpa only [hZero, mellin, Pi.zero_apply, smul_zero, integral_zero] using h.symm
  have hone : realArchimedeanZetaContinued 0 realGaussianPi 1 = 1 := by
    rw [(realArchimedeanZetaContinued_eq_integral 0 realGaussianPi (s := 1) (by simp)).2,
      realArchimedeanZetaIntegral]
    simp only [realArchimedeanZetaIntegrand, sub_self, Complex.cpow_zero, pow_zero,
      ite_self, one_mul, realGaussianPi_apply, integral_complex_ofReal]
    have h := integral_gaussian Real.pi
    rw [div_self Real.pi_ne_zero, Real.sqrt_one] at h
    simpa only [neg_mul, Complex.ofReal_one] using congrArg Complex.ofReal h
  rw [hone, hz]
  exact one_ne_zero

private theorem complexMellinMonomial_profile (ν : Measure Circle) (n : ℤ) (p q : ℕ)
    (f : 𝓢(ℂ, ℂ)) (t : ℝ) :
    complexZetaProfile ν n (complexMellinMonomial p q f) t =
      (t : ℂ) ^ (p + q) • complexZetaProfile ν (n + (p : ℤ) - q) f t := by
  simp only [complexZetaProfile, smul_eq_mul]
  rw [← integral_const_mul]
  refine integral_congr_ae (.of_forall fun u ↦ ?_)
  have hu : (u : ℂ) ≠ 0 := Circle.coe_ne_zero u
  have hs : star (u : ℂ) = (u : ℂ)⁻¹ := by
    exact (Circle.coe_inv_eq_conj u).symm.trans (Circle.coe_inv u)
  have ht : star (t : ℂ) = (t : ℂ) := Complex.conj_ofReal t
  change (u : ℂ) ^ n * complexMellinMonomial p q f (t • (u : ℂ)) =
    (t : ℂ) ^ (p + q) * ((u : ℂ) ^ (n + (p : ℤ) - q) * f (t • (u : ℂ)))
  rw [complexMellinMonomial_apply, Complex.real_smul, star_mul', ht, hs, mul_pow, mul_pow,
    pow_add, zpow_sub₀ hu, zpow_add₀ hu, zpow_natCast, zpow_natCast, div_eq_mul_inv, inv_pow]
  ring

private theorem complexMellinMonomial_shift_right (ν : Measure Circle) [IsFiniteMeasure ν]
    (n : ℤ) (p q : ℕ) (f : 𝓢(ℂ, ℂ)) {s : ℂ} (hs : 0 < s.re) :
    complexArchimedeanZetaContinued ν n (complexMellinMonomial p q f) s =
      complexArchimedeanZetaContinued ν (n + (p : ℤ) - q) f (s + ((p : ℂ) + q) / 2) := by
  have hr : 0 < (s + ((p : ℂ) + q) / 2).re := by
    rw [Complex.add_re, Complex.div_ofNat_re, Complex.add_re, Complex.natCast_re, Complex.natCast_re]
    positivity
  rw [← (complexArchimedeanZetaContinued_eq_radial ν n _ hs).2,
    ← (complexArchimedeanZetaContinued_eq_radial ν (n + (p : ℤ) - q) f hr).2]
  have he : complexZetaProfile ν n (complexMellinMonomial p q f) =
      fun t : ℝ ↦ (t : ℂ) ^ (((p + q : ℕ) : ℂ)) • complexZetaProfile ν (n + (p : ℤ) - q) f t := by
    funext t
    simpa only [Complex.cpow_natCast] using complexMellinMonomial_profile ν n p q f t
  rw [he, mellin_cpow_smul]
  congr 1
  push_cast
  ring

/-- The mixed complex monomial has the radial and angular shifts of (5.3.3.30). -/
theorem complexMellinMonomial_shift (ν : Measure Circle) [IsFiniteMeasure ν]
    (n : ℤ) (p q : ℕ) (f : 𝓢(ℂ, ℂ)) (s : ℂ) :
    complexArchimedeanZetaContinued ν n (complexMellinMonomial p q f) =ᶠ[𝓝[≠] s]
      fun z ↦ complexArchimedeanZetaContinued ν (n + (p : ℤ) - q) f (z + ((p : ℂ) + q) / 2) := by
  apply mellinMonomial_germs (complexArchimedeanZetaContinued_meromorphic _ _ _)
  · intro z
    exact (complexArchimedeanZetaContinued_meromorphic ν (n + (p : ℤ) - q) f
      (z + ((p : ℂ) + q) / 2)).comp_analyticAt (g := fun w : ℂ ↦ w + ((p : ℂ) + q) / 2)
        (analyticAt_id.add analyticAt_const)
  · exact fun z hz ↦ complexMellinMonomial_shift_right ν n p q f hz

end
end Masullo
