import SLocalThetaDerivatives
import SLocalZetaUnfolding
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

open Bornology Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped NumberField SchwartzMap FourierTransform ContDiff

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]
variable (S : Finset (HeightOneSpectrum (𝓞 F)))

private abbrev E := sLocalBruhatImage F S
private abbrev K := SLocalThetaNormOne F S

variable [MeasurableSpace (K F S)] [BorelSpace (K F S)]

private theorem pow_mul_exp_neg_abs_le (c : ℝ) (hc : 0 < c) (j : ℕ) (t : ℝ) :
    |t| ^ j * Real.exp (-c * |t|) ≤ (j.factorial : ℝ) / c ^ j := by
  have h := Real.pow_div_factorial_le_exp (c * |t|) (mul_nonneg hc.le (abs_nonneg t)) j
  rw [mul_pow, div_le_iff₀ (by positivity)] at h
  rw [neg_mul, Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _),
    div_mul_eq_mul_div, le_div_iff₀ (pow_pos hc _)]
  simpa only [mul_comm] using h

private def radialThetaEval (ν : Measure (K F S)) [ν.IsHaarMeasure]
    (χ : PontryaginDual (K F S)) (t : ℝ) : E F S →ₗ[ℂ] ℂ := by
  let q := (QuotientGroup.mk (sLocalExpSection F S (Multiplicative.ofAdd t)) : SIdeleQuotient F S)
  let T (k : K F S) : E F S →ₗ[ℂ] ℂ :=
    ((χ k : Circle) : ℂ) • ((sLocalThetaEval F S ((k.val * q).out)).comp (sLocalBruhatImage F S).subtype)
  have h (f : E F S) :
      (fun k ↦ T k f) = fun k ↦ ((χ k : Circle) : ℂ) *
        sLocalTheta F S (sLocalBruhatRestriction F S f.val) (k.val * q) := by
    funext k
    change ((χ k : Circle) : ℂ) * sLocalThetaEval F S (k.val * q).out f.val = _
    conv_rhs =>
      rw [← Quotient.out_eq' (k.val * q), sLocalTheta_mk]
    rfl
  have hi (f : E F S) : Integrable (fun k ↦ T k f) ν :=
    h f ▸ sLocalHomogeneousTheta_integrable F S ν χ f.val q
  exact
    { toFun := fun f ↦ ∫ k, T k f ∂ν
      map_add' := fun f g ↦ by
        simp_rw [map_add]
        exact integral_add (hi f) (hi g)
      map_smul' := fun c f ↦ by simp only [map_smul, integral_smul, RingHom.id_apply] }

private theorem radialThetaEval_apply (ν : Measure (K F S)) [ν.IsHaarMeasure]
    (χ : PontryaginDual (K F S)) (t : ℝ) (f : E F S) :
    radialThetaEval F S ν χ t f = sLocalHomogeneousTheta F S ν χ f.val
      (QuotientGroup.mk (sLocalExpSection F S (Multiplicative.ofAdd t))) := by
  unfold radialThetaEval sLocalHomogeneousTheta
  apply integral_congr_ae
  apply ae_of_all
  intro k
  let q := (QuotientGroup.mk (sLocalExpSection F S (Multiplicative.ofAdd t)) : SIdeleQuotient F S)
  change ((χ k : Circle) : ℂ) * sLocalThetaEval F S (k.val * q).out f.val =
    ((χ k : Circle) : ℂ) * sLocalTheta F S (sLocalBruhatRestriction F S f.val) (k.val * q)
  conv_rhs => rw [← Quotient.out_eq' (k.val * q), sLocalTheta_mk]
  rfl

set_option maxHeartbeats 1500000 in
/-- The real logarithmic Mellin profiles are bounded in Schwartz space as the
real part of the spectral parameter ranges over a positive compact interval. -/
private theorem exists_sLocalRadialSchwartz_family
    (ν : Measure (K F S)) [ν.IsHaarMeasure] (χ : PontryaginDual (K F S))
    (f : E F S) (a b : ℝ) (ha : 0 < a) :
    ∃ g : Icc a b → 𝓢(ℝ, ℂ), IsVonNBounded ℂ (range g) ∧
      ∀ σ t, g σ t = Complex.exp ((σ.val : ℂ) * (t : ℂ)) *
        radialThetaEval F S ν χ t f := by
  let D := sLocalBruhatDerivative F S (sLocalExpSection F S) (sLocalExpSection_continuous F S)
  let Θ (g : E F S) (t : ℝ) := radialThetaEval F S ν χ t g
  let A (σ : ℝ) (g : E F S) := D g + (σ : ℂ) • g
  let T (σ : ℝ) (g : E F S) (t : ℝ) := Complex.exp ((σ : ℂ) * (t : ℂ)) * Θ g t
  have hD (σ : ℝ) (g : E F S) (t : ℝ) : HasDerivAt (T σ g) (T σ (A σ g) t) t := by
    have hΘ := sLocalHomogeneousTheta_log_hasDerivAt F S (sLocalExpSection F S)
      (sLocalExpSection_continuous F S) ν χ g t
    have hΘ' : HasDerivAt (Θ g) (Θ (D g) t) t := by
      simpa only [Θ, radialThetaEval_apply, D] using hΘ
    have hc : HasDerivAt (fun t : ℝ ↦ (t : ℂ)) 1 t := by
      change HasDerivAt (⇑Complex.ofRealCLM) (Complex.ofRealCLM 1) t
      exact Complex.ofRealCLM.hasFDerivAt.hasDerivAt
    have hexp : HasDerivAt (fun x : ℝ ↦ Complex.exp ((σ : ℂ) * (x : ℂ)))
        (Complex.exp ((σ : ℂ) * (t : ℂ)) * (σ : ℂ)) t := by
      simpa only [mul_one] using (hc.const_mul (σ : ℂ)).cexp
    have he :
        Complex.exp ((σ : ℂ) * (t : ℂ)) * (σ : ℂ) * Θ g t +
          Complex.exp ((σ : ℂ) * (t : ℂ)) * Θ (D g) t = T σ (A σ g) t := by
      dsimp only [A, T, Θ]
      rw [map_add, map_smul, smul_eq_mul]
      ring
    exact he ▸ hexp.mul hΘ'
  let U (σ : ℝ) (j : ℕ) := (A σ)^[j] f
  have hiter (σ : ℝ) (j : ℕ) : iteratedDeriv j (T σ f) = T σ (U σ j) := by
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [iteratedDeriv_succ, ih]
      funext t
      rw [(hD σ (U σ j) t).deriv]
      simp only [U, Function.iterate_succ_apply']
  have hsmooth (σ : ℝ) : ContDiff ℝ ∞ (T σ f) := by
    apply contDiff_iff_iteratedDeriv.2
    refine ⟨fun j _ ↦ ?_, fun j _ ↦ ?_⟩
    · rw [hiter]
      exact continuous_iff_continuousAt.mpr fun t ↦ (hD σ (U σ j) t).continuousAt
    · rw [hiter]
      exact fun t ↦ (hD σ (U σ j) t).differentiableAt
  have hU (j : ℕ) : Continuous (fun σ ↦ U σ j) := by
    induction j with
    | zero => exact continuous_const
    | succ j ih =>
      simp only [U, Function.iterate_succ_apply']
      exact (D.continuous.comp ih).add (Complex.continuous_ofReal.smul ih)
  have hbound (k j : ℕ) : ∃ M : ℝ, 0 ≤ M ∧ ∀ σ ∈ Icc a b, ∀ t : ℝ,
      ‖t‖ ^ k * ‖iteratedFDeriv ℝ j (T σ f) t‖ ≤ M := by
    let B := (fun σ ↦ U σ j) '' Icc a b
    have hB : IsVonNBounded ℂ B := (isCompact_Icc.image (hU j)).isVonNBounded ℂ
    obtain ⟨c, C, hc, hC, _, hmaj⟩ := sLocalRadialMellin_strip_majorant F S (sLocalExpSection F S)
      (sLocalIdeleNorm_expSection F S) ν χ B hB a b ha
    refine ⟨C * ((k.factorial : ℝ) / c ^ k), by positivity, fun σ hσ t ↦ ?_⟩
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, hiter, Real.norm_eq_abs]
    have h := hmaj (U σ j) (mem_image_of_mem _ hσ) (σ : ℂ)
      (by simpa only [Complex.ofReal_re] using hσ.1) (by simpa only [Complex.ofReal_re] using hσ.2) t
    calc
      _ ≤ |t| ^ k * (C * Real.exp (-c * |t|)) :=
        mul_le_mul_of_nonneg_left (by simpa only [T, Θ, radialThetaEval_apply] using h) (by positivity)
      _ = C * (|t| ^ k * Real.exp (-c * |t|)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (pow_mul_exp_neg_abs_le c hc k t) hC.le
  choose M hM hEst using hbound
  let g (σ : Icc a b) : 𝓢(ℝ, ℂ) :=
    ⟨T σ f, hsmooth σ, fun k j ↦ ⟨M k j, hEst k j σ σ.property⟩⟩
  refine ⟨g, (schwartz_withSeminorms ℂ ℝ ℂ).isVonNBounded_iff_seminorm_bounded.2 ?_, fun _ _ ↦ rfl⟩
  rintro ⟨k, j⟩
  refine ⟨M k j + 1, add_pos_of_nonneg_of_pos (hM k j) zero_lt_one, ?_⟩
  rintro _ ⟨σ, rfl⟩
  exact (SchwartzMap.seminorm_le_bound ℂ k j (g σ) (hM k j) (hEst k j σ σ.property)).trans_lt
    (lt_add_one _)

/-- Each positive exponential weight makes a homogeneous logarithmic profile Schwartz. -/
theorem exists_sLocalRadialSchwartz (ν : Measure (K F S)) [ν.IsHaarMeasure]
    (χ : PontryaginDual (K F S)) (f : E F S) (σ : ℝ) (hσ : 0 < σ) :
    ∃ g : 𝓢(ℝ, ℂ), ∀ t, g t = Complex.exp ((σ : ℂ) * (t : ℂ)) *
      sLocalHomogeneousTheta F S ν χ f.val
        (QuotientGroup.mk (sLocalExpSection F S (Multiplicative.ofAdd t))) := by
  obtain ⟨g, _, hg⟩ := exists_sLocalRadialSchwartz_family F S ν χ f σ σ hσ
  exact ⟨g ⟨σ, by simp⟩, fun t ↦ by
    rw [hg, radialThetaEval_apply]⟩

attribute [local instance] sLocalZetaUnfolding_classMeasurable sLocalZetaUnfolding_classBorel
attribute [local instance] sLocalZetaUnfolding_idelesMeasurable sLocalZetaUnfolding_idelesBorel

omit [MeasurableSpace (K F S)] [BorelSpace (K F S)] in
/-- Lemma 3.3.1.7(1). The actual idelic zeta integral has Schwartz
vertical traces, bounded in the Schwartz topology on positive closed strips. -/
theorem sLocalIdelicZeta_vertical_schwartz
    (μ : Measure (SAdeles F S)ˣ) [μ.IsHaarMeasure] (χ : PontryaginDual (K F S))
    (f : E F S) (a b : ℝ) (ha : 0 < a) :
    ∃ g : Icc a b → 𝓢(ℝ, ℂ), IsVonNBounded ℂ (range g) ∧
      ∀ σ t, g σ t = sLocalIdelicZetaIntegral F S μ χ f ⟨σ.val, t⟩ := by
  obtain ⟨ν, hν, hweil⟩ := sLocalClassHaar_exists_weil F S μ
  letI := hν
  obtain ⟨g, hB, hg⟩ := exists_sLocalRadialSchwartz_family F S ν χ f a b ha
  let u : ℝˣ := Units.mk0 (-1 / (2 * Real.pi)) (by positivity [Real.pi_pos])
  let L : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) := (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (ContinuousLinearEquiv.unitsEquivAut ℝ u)).comp (SchwartzMap.fourierTransformCLM ℂ)
  refine ⟨fun σ ↦ L (g σ), ?_, fun σ t ↦ ?_⟩
  · rw [show range (fun σ ↦ L (g σ)) = L '' range g from (range_comp L g)]
    exact hB.image L
  have hpos : 0 < (⟨σ.val, t⟩ : ℂ).re := ha.trans_le σ.property.1
  rw [(sLocalIdelicZeta_integrable_eq_theta F S μ ν hweil χ f _ hpos).2,
    (sLocalThetaZeta_integrable_eq_radial F S ν χ f _ hpos).2]
  change SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (ContinuousLinearEquiv.unitsEquivAut ℝ u)
    (𝓕 (g σ)) t = _
  rw [SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
    ContinuousLinearEquiv.unitsEquivAut_apply, SchwartzMap.fourier_coe,
    Real.fourier_real_eq_integral_exp_smul]
  unfold sLocalRadialMellin
  apply integral_congr_ae
  apply ae_of_all
  intro x
  dsimp only
  rw [hg, radialThetaEval_apply, smul_eq_mul, ← mul_assoc, ← Complex.exp_add]
  have hu : -2 * Real.pi * x * (t * (u : ℝ)) = t * x := by
    change -2 * Real.pi * x * (t * (-1 / (2 * Real.pi))) = _
    field_simp [Real.pi_ne_zero]
  rw [hu]
  congr 2
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]

end

end Masullo
