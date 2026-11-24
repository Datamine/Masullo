import MellinBergman
import BergmanDivisorInterpolation
import Mathlib.Analysis.Fourier.Convolution

open Filter Function MeasureTheory Set Topology FourierTransform
open scoped FourierTransform Convolution SchwartzMap ENat

namespace Masullo

noncomputable section

private abbrev E := PositiveRealExponentialDecay (univ : Set ℝ)
private abbrev A := SchwartzBergman (univ : Set ℝ)

/-- The scalar Fourier–Mellin equivalence on the entire decay space. -/
def entireMellin : E ≃L[ℂ] A :=
  positiveRealFourierMellin univ isOpen_univ ordConnected_univ univ_nonempty

private theorem entireMellin_imaginary (f : E) (t : ℝ) :
    (entireMellin f).val ((t : ℂ) * Complex.I) = 𝓕 f.val (- (t / (2 * Real.pi))) := by
  rw [entireMellin, positiveRealFourierMellin_apply _ _ _ _ _ _ (mem_univ _), mellin_eq_fourier]
  simp only [Complex.mul_I_re, Complex.ofReal_im, neg_zero, zero_mul, Real.exp_zero, one_smul,
    Real.log_exp, Complex.mul_I_im, Complex.ofReal_re]
  rw [← Real.fourierInv_eq_fourier_comp_neg, Real.fourierInv_eq_fourier_neg]

private def zeroTwist (f : E) : 𝓢(ℝ, ℂ) :=
  logExponentialDecayTwist univ ⟨0, mem_univ _⟩ f

private theorem zeroTwist_val (f : E) : (zeroTwist f : ℝ → ℂ) = f.val := by
  funext x
  let a : (univ : Set ℝ) := ⟨0, mem_univ _⟩
  simpa [zeroTwist, a] using logExponentialDecayTwist_apply univ a
    (show logExponentialDecaySubmodule univ from f) x

private theorem entireDecay_integrable (f : E) : Integrable f.val volume := by
  rw [← zeroTwist_val]
  exact (zeroTwist f).integrable

private def slowGaussian : A :=
  ⟨fun z ↦ Complex.exp (z ^ 2),
    by simpa using gaussian_mem_schwartzBergmanSubmodule univ isOpen_univ⟩

private def bergmanProduct (f g : A) : A := by
  refine ⟨f.val * g.val, ?_⟩
  refine ⟨by simp, f.property.2.1.mul g.property.2.1, ?_⟩
  intro a b hab hI N
  obtain ⟨C, hC⟩ := f.property.2.2 a b hab hI N
  obtain ⟨D, hD⟩ := g.property.2.2 a b hab hI 0
  refine ⟨max C 0 * max D 0, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  have hc := hC ⟨z, hz, rfl⟩
  have hd := hD ⟨z, hz, rfl⟩
  change ‖z ^ N * (f.val z * g.val z)‖ ≤ _
  rw [← mul_assoc, norm_mul]
  exact mul_le_mul (hc.trans (le_max_left _ _))
    ((by simpa using hd : ‖g.val z‖ ≤ D).trans (le_max_left _ _))
    (norm_nonneg _) (le_max_right _ _)

private def fastGaussian : A := bergmanProduct slowGaussian slowGaussian

/-- The Mellin inverse of the product represents the actual pointwise
convolution of any two entire-decay tests in logarithmic coordinates. -/
theorem entireDecay_convolution_fourierMellin (φ f : E) :
    ∃ ψ : E, ψ.val = φ.val ⋆[ContinuousLinearMap.mul ℂ ℂ] f.val ∧
      ∀ z, (entireMellin ψ).val z = (entireMellin φ).val z * (entireMellin f).val z := by
  let B := bergmanProduct (entireMellin φ) (entireMellin f)
  let ψ := entireMellin.symm B
  have hB : entireMellin ψ = B := entireMellin.apply_symm_apply B
  have hprod (z : ℂ) :
      (entireMellin ψ).val z = (entireMellin φ).val z * (entireMellin f).val z := by
    rw [hB]
    rfl
  refine ⟨ψ, ?_, hprod⟩
  let C := SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) (zeroTwist φ) (zeroTwist f)
  have hF : 𝓕 (zeroTwist ψ) = 𝓕 C := by
    ext y
    let t := -(y * (2 * Real.pi))
    have hy : -(t / (2 * Real.pi)) = y := by
      dsimp [t]
      field_simp [Real.pi_ne_zero]
    have hp := hprod ((t : ℂ) * Complex.I)
    simp only [entireMellin_imaginary, hy] at hp
    change 𝓕 (zeroTwist ψ) y = 𝓕 C y
    rw [SchwartzMap.fourier_coe, zeroTwist_val]
    change 𝓕 ψ.val y = 𝓕 C y
    rw [SchwartzMap.fourier_convolution_apply, zeroTwist_val, zeroTwist_val,
      Real.fourier_mul_convolution_eq (entireDecay_integrable φ) (entireDecay_integrable f)]
    exact hp
  have hψ : zeroTwist ψ = C := by
    simpa only [fourierInv_fourier_eq] using congrArg (fun u : 𝓢(ℝ, ℂ) ↦ 𝓕⁻ u) hF
  funext x
  rw [← congrFun (zeroTwist_val ψ) x, hψ]
  change C x = _
  rw [SchwartzMap.convolution_apply, zeroTwist_val, zeroTwist_val]

/-- For the scalar logarithmic group, generation by the ordinary
convolution ideal is exactly divisibility with a Schwartz–Bergman quotient. -/
theorem entireDecay_principalConvolution_iff_bergman (φ ψ : E) :
    (∃ f : E, ψ.val = φ.val ⋆[ContinuousLinearMap.mul ℂ ℂ] f.val) ↔
      ∃ H : A, ∀ z, (entireMellin ψ).val z = (entireMellin φ).val z * H.val z := by
  constructor
  · rintro ⟨f, hf⟩
    obtain ⟨q, hq, hprod⟩ := entireDecay_convolution_fourierMellin φ f
    have he : q = ψ := Subtype.ext (hq.trans hf.symm)
    exact ⟨entireMellin f, he ▸ hprod⟩
  · rintro ⟨H, hH⟩
    let f := entireMellin.symm H
    have hF : entireMellin f = H := entireMellin.apply_symm_apply H
    obtain ⟨q, hq, hprod⟩ := entireDecay_convolution_fourierMellin φ f
    have he : q = ψ := by
      apply entireMellin.injective
      apply Subtype.ext
      funext z
      rw [hprod, hF, hH]
    exact ⟨f, he ▸ hq⟩

/-- For a scalar test with finitely many Mellin zeros, the quotient by
the vanishing-jet ideal in the original decay space is the full finite space
of its Taylor coefficients, with the quotient topology. -/
theorem exists_entireDecay_finiteMellinJetEquiv (φ : E)
    (hzeros : Set.Finite {z : ℂ | (entireMellin φ).val z = 0}) :
    let g := entireMellin φ
    let I : Set (ℂ × ℕ) := {i | (i.2 : ℕ∞) < analyticOrderAt g.val i.1}
    let D := (bergmanDivisorSubmodule g.val).comap entireMellin.toLinearMap
    ∃ e : (E ⧸ D) ≃L[ℂ] (I → ℂ),
      ∀ f i, e (D.mkQ f) i = bergmanNormalizedJet i.val.1 i.val.2 (entireMellin f) := by
  intro g I D
  let W := bergmanDivisorSubmodule g.val
  obtain ⟨e, he⟩ := exists_bergmanDivisor_finiteJetEquiv g hzeros
  let J := D.liftQL (W.mkQL.comp entireMellin.toContinuousLinearMap) (by
    intro f hf
    change W.mkQ (entireMellin f) = 0
    exact (Submodule.Quotient.mk_eq_zero W).mpr hf)
  let K := W.liftQL (D.mkQL.comp entireMellin.symm.toContinuousLinearMap) (by
    intro f hf
    change D.mkQ (entireMellin.symm f) = 0
    apply (Submodule.Quotient.mk_eq_zero D).mpr
    change entireMellin (entireMellin.symm f) ∈ W
    rwa [entireMellin.apply_symm_apply])
  have hJ (f : E) : J (D.mkQ f) = W.mkQ (entireMellin f) := rfl
  have hK (f : A) : K (W.mkQ f) = D.mkQ (entireMellin.symm f) := rfl
  let Q := ContinuousLinearEquiv.equivOfInverse J K (by
    intro u
    obtain ⟨f, rfl⟩ := D.mkQ_surjective u
    rw [hJ, hK, entireMellin.symm_apply_apply]) (by
    intro u
    obtain ⟨f, rfl⟩ := W.mkQ_surjective u
    rw [hK, hJ, entireMellin.apply_symm_apply])
  exact ⟨Q.trans e, fun f i ↦ (congrArg (fun u ↦ e u i) (hJ f)).trans (he _ i)⟩

/-- Lemma 9.3.2.5 fails for the ordinary principal convolution ideal, even
on the positive-real group with the trivial phase and the interval [-1,1].
The fast Gaussian has no Mellin zeros. The slow Gaussian lies outside its
convolution ideal in the entire exponential-decay space. -/
theorem zeroFreeMellin_principalConvolution_ne_univ :
    ∃ φ ψ : E, (∀ z : ℂ, mellin (fun t ↦ φ.val (Real.log t)) z ≠ 0) ∧
      ∀ f : E, ψ.val ≠ φ.val ⋆[ContinuousLinearMap.mul ℂ ℂ] f.val := by
  let φ := entireMellin.symm fastGaussian
  let ψ := entireMellin.symm slowGaussian
  have hφ : entireMellin φ = fastGaussian := entireMellin.apply_symm_apply _
  have hψ : entireMellin ψ = slowGaussian := entireMellin.apply_symm_apply _
  refine ⟨φ, ψ, fun z ↦ ?_, fun f hf ↦ ?_⟩
  · rw [← positiveRealFourierMellin_apply univ isOpen_univ ordConnected_univ univ_nonempty
      φ z (mem_univ z.re)]
    change (entireMellin φ).val z ≠ 0
    rw [hφ]
    exact mul_ne_zero (Complex.exp_ne_zero _) (Complex.exp_ne_zero _)
  · let H := entireMellin f
    have h (t : ℝ) : (slowGaussian).val ((t : ℂ) * Complex.I) =
        (fastGaussian).val ((t : ℂ) * Complex.I) * H.val ((t : ℂ) * Complex.I) := by
      rw [← hψ, ← hφ, show H = entireMellin f from rfl, entireMellin_imaginary, hf,
        Real.fourier_mul_convolution_eq (entireDecay_integrable φ) (entireDecay_integrable f),
        entireMellin_imaginary, entireMellin_imaginary]
    have hval (t : ℝ) : H.val ((t : ℂ) * Complex.I) =
        Complex.exp (-(((t : ℂ) * Complex.I) ^ 2)) := by
      let z := (t : ℂ) * Complex.I
      have h' : Complex.exp (z ^ 2) =
          (Complex.exp (z ^ 2) * Complex.exp (z ^ 2)) * H.val z := h t
      have hh : Complex.exp (z ^ 2) * H.val z = 1 := by
        apply mul_left_cancel₀ (Complex.exp_ne_zero (z ^ 2))
        rw [← mul_assoc, ← h', mul_one]
      change H.val z = Complex.exp (-(z ^ 2))
      apply mul_left_cancel₀ (Complex.exp_ne_zero (z ^ 2))
      rw [hh, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
    obtain ⟨M, hM⟩ := H.property.2.2 0 0 le_rfl (subset_univ _) 0
    let t := max M 1 + 1
    have ht : 1 ≤ t := by dsimp only [t]; linarith [le_max_right M 1]
    have htM : M < t := lt_of_le_of_lt (le_max_left M 1) (lt_add_one _)
    let z := (t : ℂ) * Complex.I
    have hz : z ∈ Complex.re ⁻¹' Icc (0 : ℝ) 0 := by simp [z]
    have hbounded := hM (show ‖z ^ 0 * H.val z‖ ∈ _ from ⟨z, hz, rfl⟩)
    change ‖z ^ 0 * H.val z‖ ≤ M at hbounded
    rw [pow_zero, one_mul, hval t, Complex.norm_exp] at hbounded
    have hre : (-z ^ 2).re = t ^ 2 := by
      simp [z, pow_two, Complex.mul_re, Complex.mul_im]
    change Real.exp (-z ^ 2).re ≤ M at hbounded
    rw [hre] at hbounded
    have htsq : t ≤ t ^ 2 := by nlinarith
    linarith [Real.add_one_le_exp (t ^ 2)]

end

end Masullo
