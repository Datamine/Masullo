import SLocalZetaUnfolding
import CompactCharacterCompleteness
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped FourierTransform NumberField

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]
variable (S : Finset (HeightOneSpectrum (𝓞 F)))

private abbrev Q := SIdeleQuotient F S
private abbrev K := SLocalThetaNormOne F S
private abbrev E := sLocalBruhatImage F S

/-- The actual theta orbit-sum map, with its test-space domain. -/
def sLocalThetaOperator : E F S →ₗ[ℂ] (Q F S → ℂ) where
  toFun f := sLocalTheta F S (sLocalBruhatRestriction F S f.val)
  map_add' f g := by
    funext q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    exact (sLocalThetaEval F S x).map_add f.val g.val
  map_smul' c f := by
    funext q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    exact (sLocalThetaEval F S x).map_smul c f.val

/-- The S-local space in Definition 5.1.1.1(3), with the quotient topology
of the kernel of the theta orbit-sum map. -/
abbrev SLocalThetaQuotient := E F S ⧸ (sLocalThetaOperator F S).ker

private abbrev ray (t : ℝ) : Q F S := QuotientGroup.mk
  (sLocalExpSection F S (Multiplicative.ofAdd t))

local instance sLocalThetaKernels_classMeasurable : MeasurableSpace (Q F S) := borel _
local instance sLocalThetaKernels_classBorel : BorelSpace (Q F S) := ⟨rfl⟩
variable (ν : Measure (K F S)) [ν.IsHaarMeasure]

private theorem homogeneous_zero_of_ray_zero (ω : PontryaginDual (K F S)) (f : E F S)
    (h : ∀ t : ℝ, sLocalHomogeneousTheta F S ν ω f.val (ray F S t) = 0) :
    ∀ q, sLocalHomogeneousTheta F S ν ω f.val q = 0 := by
  intro q
  obtain ⟨⟨t,k⟩, rfl⟩ := (sLocalZetaSplit F S).surjective q
  change sLocalHomogeneousTheta F S ν ω f.val (ray F S t * k.val) = 0
  rw [mul_comm (ray F S t) k.val, sLocalHomogeneousTheta_translate, h t, mul_zero]

/-- The homogeneous kernel is detected on any vertical line of absolute
convergence in its character component. This is the Fourier-injectivity step
of Lemma 5.1.2.2(2). -/
theorem sLocalHomogeneousTheta_zero_iff_verticalZeta (ω : PontryaginDual (K F S))
    (f : E F S) (σ : ℝ) (hσ : 0 < σ) :
    (∀ q, sLocalHomogeneousTheta F S ν ω f.val q = 0) ↔
      ∀ y : ℝ, sLocalThetaZetaIntegral F S ν ω f ((σ : ℂ) + (y : ℂ) * Complex.I) = 0 := by
  constructor
  · intro h y
    let z := (σ : ℂ) + (y : ℂ) * Complex.I
    have hz : 0 < z.re := by simpa [z] using hσ
    rw [(sLocalThetaZeta_integrable_eq_radial F S ν ω f z hz).2]
    simp [sLocalRadialMellin, h]
  · intro h
    let R (t : ℝ) := Complex.exp ((σ : ℂ) * (t : ℂ)) *
      sLocalHomogeneousTheta F S ν ω f.val (ray F S t)
    have hI : Integrable R := sLocalRadialMellin_integrable F S (sLocalExpSection F S)
      (sLocalExpSection_continuous F S) (sLocalIdeleNorm_expSection F S) ν ω f σ
      (by simpa using hσ)
    have hC : Continuous R := by
      have hr : Continuous (ray F S) := QuotientGroup.continuous_mk.comp
        ((sLocalExpSection_continuous F S).comp continuous_ofAdd)
      exact (by fun_prop : Continuous (fun t : ℝ => Complex.exp ((σ : ℂ) * (t : ℂ)))).mul
        ((sLocalHomogeneousTheta_continuous F S ν ω f.val).comp hr)
    have hF : 𝓕 R = 0 := by
      funext y
      let b := -2 * Real.pi * y
      let z := (σ : ℂ) + (b : ℂ) * Complex.I
      have hz : 0 < z.re := by simpa [z] using hσ
      have hZ := h b
      change sLocalThetaZetaIntegral F S ν ω f z = 0 at hZ
      rw [(sLocalThetaZeta_integrable_eq_radial F S ν ω f z hz).2] at hZ
      change sLocalRadialMellin F S (sLocalExpSection F S) ν ω f z = _
          at hZ
      change 𝓕 R y = (0 : ℂ)
      rw [← hZ, Real.fourier_eq', sLocalRadialMellin]
      apply integral_congr_ae
      filter_upwards with t
      simp only [R, ray, RCLike.inner_apply, conj_trivial, smul_eq_mul]
      change Complex.exp ((↑(-2 * Real.pi * (y * t)) : ℂ) * Complex.I) *
          (Complex.exp ((σ : ℂ) * (t : ℂ)) * sLocalHomogeneousTheta F S ν ω f.val (ray F S t)) =
        Complex.exp (z * (t : ℂ)) * sLocalHomogeneousTheta F S ν ω f.val (ray F S t)
      rw [← mul_assoc, ← Complex.exp_add]
      congr 2
      push_cast
      simp only [z, b, Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_ofNat]
      ring
    have hinv := hC.fourierInv_fourier_eq hI (hF ▸ integrable_zero _ _ _)
    apply homogeneous_zero_of_ray_zero F S ν ω f
    intro t
    have ht : R t = 0 := by
      have ht := congrFun hinv t
      rw [hF, Real.fourierInv_eq'] at ht
      simpa only [Pi.zero_apply, smul_zero, integral_zero] using ht.symm
    exact (mul_eq_zero.mp ht).resolve_left (Complex.exp_ne_zero _)

variable [ν.WeaklyRegular]

/-- The full theta kernel is the intersection of the homogeneous kernels.
Compact-group Fourier completeness is applied to the continuous theta profile
at each radial point. -/
theorem sLocalTheta_zero_iff_homogeneous_zero (f : E F S) :
    sLocalThetaOperator F S f = 0 ↔
      ∀ (ω : PontryaginDual (K F S)) q, sLocalHomogeneousTheta F S ν ω f.val q = 0 := by
  constructor
  · intro h ω q
    change (∫ k : K F S, (ω k : ℂ) * sLocalThetaOperator F S f (k.val * q) ∂ν) = 0
    simp [h]
  · intro h
    funext q
    letI : T1Space (Q F S) := QuotientGroup.t1Space_iff.mpr (sUnitImage_closed F S)
    letI : T2Space (K F S) := inferInstance
    letI := sLocalThetaNormOne_compact F S
    letI : IsFiniteMeasure ν := ⟨isCompact_univ.measure_lt_top⟩
    let g (k : K F S) := sLocalThetaOperator F S f (k.val * q)
    have hg : Continuous g :=
      (sLocalTheta_continuous F S f.val).comp
        (show Continuous (fun k : K F S => k.val * q) from
          continuous_subtype_val.mul (continuous_const (y := q)))
    have hZ (ω : PontryaginDual (K F S)) : ∫ k, star (ω k : ℂ) * g k ∂ν = 0 := by
      have he : (fun k => star (ω k : ℂ) * g k) = fun k => (ω⁻¹ k : ℂ) * g k := by
        funext k
        exact congrArg (· * g k) (Circle.coe_inv_eq_conj (ω k)).symm
      rw [he]
      exact h ω⁻¹ q
    have hae := ae_eq_zero_of_character_integral_eq_zero ν
      (hg.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) hZ
    have he := (hg.ae_eq_iff_eq ν continuous_const).mp hae
    have h1 : g 1 = (0 : ℂ) := congrFun he 1
    change sLocalThetaOperator F S f q = 0
    change sLocalThetaOperator F S f ((1 : Q F S) * q) = 0 at h1
    have hmul : (1 : Q F S) * q = q := one_mul q
    exact (congrArg (sLocalThetaOperator F S f) hmul).symm.trans h1

/-- The full theta kernel is detected by the Mellin transforms on one common
vertical line. No continuation outside absolute convergence is needed for
this kernel comparison. -/
theorem sLocalTheta_zero_iff_verticalZeta (f : E F S) (σ : ℝ) (hσ : 0 < σ) :
    sLocalThetaOperator F S f = 0 ↔
      ∀ (ω : PontryaginDual (K F S)) (y : ℝ),
        sLocalThetaZetaIntegral F S ν ω f ((σ : ℂ) + (y : ℂ) * Complex.I) = 0 := by
  rw [sLocalTheta_zero_iff_homogeneous_zero F S ν f]
  exact forall_congr' fun ω => sLocalHomogeneousTheta_zero_iff_verticalZeta F S ν ω f σ hσ

include ν in
/-- The kernel of the actual S-local theta map is closed in the test topology. -/
theorem sLocalThetaOperator_closedKer :
    IsClosed ((sLocalThetaOperator F S).ker : Set (E F S)) := by
  have hr (y : ℝ) : 0 < ((1 : ℂ) + (y : ℂ) * Complex.I).re := by simp
  have he : ((sLocalThetaOperator F S).ker : Set (E F S)) =
      ⋂ (ω : PontryaginDual (K F S)) (y : ℝ),
        (sLocalThetaZetaCLM F S ν ω ((1 : ℂ) + (y : ℂ) * Complex.I) (hr y)).ker := by
    ext f
    simp only [SetLike.mem_coe, LinearMap.mem_ker, mem_iInter]
    exact sLocalTheta_zero_iff_verticalZeta F S ν f 1 zero_lt_one
  rw [he]
  exact isClosed_iInter fun ω => isClosed_iInter fun y =>
    (sLocalThetaZetaCLM F S ν ω _ (hr y)).isClosed_ker

end
end Masullo
