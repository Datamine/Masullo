import GlobalOrbitalMarkushevich
import ModulatedDecayAngularBounds
import ArchimedeanMellinMonomials
import BruhatCompactTestTopology
import IdelicStageCofinalBasis

open Filter Function MeasureTheory NumberField Set Topology
open scoped CompactlySupported FourierTransform NumberField SchwartzMap

namespace Masullo
noncomputable section

section CompactKernel

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  (m : G →ₜ* Multiplicative ℝ) (τ : Multiplicative ℝ →ₜ* G) (hτ : RightInverse τ m)
  (U : Subgroup G) (hU : m.toMonoidHom.ker = U)
  [CompactSpace U] [MeasurableSpace U] [BorelSpace U]
  (η : Measure U) [η.IsHaarMeasure] (χ : PontryaginDual U)

private def angularCoeff : BruhatSchwartz G →L[ℂ] 𝓢(ℝ, ℂ) := by
  subst U
  exact bruhatAngularFourier m τ hτ η χ

private theorem angularCoeff_apply (f : BruhatSchwartz G) (x : ℝ) :
    angularCoeff m τ hτ U hU η χ f x =
      ∫ k : U, f.val (τ (Multiplicative.ofAdd x) * k.val) * (χ k : ℂ) ∂η := by
  subst U
  exact bruhatAngularFourier_apply m τ hτ η χ f x

end CompactKernel

variable (F : Type*) [Field F] [NumberField F]
private abbrev Q := IdeleClass F
private abbrev K := normOneIdeleClass F

local instance orbitalConvolutionQMeasure : MeasurableSpace (Q F) := borel _
local instance orbitalConvolutionQBorel : BorelSpace (Q F) := ⟨rfl⟩
local instance orbitalConvolutionQT2 : T2Space (Q F) := ideleClasses_hausdorff
local instance orbitalConvolutionQLC : LocallyCompactSpace (Q F) := ideleClasses_locallyCompact
local instance orbitalConvolutionQSecondCountable : SecondCountableTopology (Q F) := ideleClass_secondCountable F

private abbrev logNorm (g : Q F) : ℝ := (ideleClassLogNorm F g).toAdd

variable (μ : Measure (Q F)) [μ.IsHaarMeasure]

/-- The logarithmic coefficient of the actual Haar convolution test at an orbital exponent. -/
def orbitalConvolutionCoefficient (φ : Q F → ℂ) (χ : PontryaginDual (Q F))
    (z : ℂ) (m : ℕ) : ℂ :=
  ∫ g, φ g * orbitalMomentPhase F χ z g * (logNorm F g : ℂ)^m ∂μ

set_option maxHeartbeats 1200000 in
/-- The actual global convolution acts triangularly on each block of orbital moments. -/
theorem orbitalSobolevMomentCLM_convolution (s : ℝ) (hs : 0 ≤ s)
    (φ : C_c(Q F, ℂ)) (χ : PontryaginDual (Q F)) (z : ℂ) (hz : z.re = 0)
    (m : ℕ) (hm : (m : ℝ) < (s-1)/2) (u : Lp ℂ 2 μ) :
    orbitalSobolevMomentCLM F μ s hs χ z hz m hm
        (globalHardySobolevConvolution F μ 0 0 s hs φ u) =
      ∑ j : Fin (m+1), (m.choose j : ℂ) * orbitalConvolutionCoefficient F μ φ χ z (m-j) *
        ∫ g, u g * orbitalSobolevMoment F χ s z j g ∂μ := by
  letI : μ.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure μ
  let L := orbitalSobolevMomentCLM F μ s hs χ z hz m hm
  let T (g : Q F) := hardySobolevMulTranslation μ (ideleClassLogNorm F) (ideleClassLogNorm_continuous F)
    0 0 s hs g
  let c (j : ℕ) (g : Q F) := φ g * orbitalMomentPhase F χ z g * (logNorm F g : ℂ)^(m-j)
  let a (j : ℕ) := (m.choose j : ℂ) * ∫ g, u g * orbitalSobolevMoment F χ s z j g ∂μ
  have hi (j : ℕ) : Integrable (c j) μ := by
    have hlog : Continuous (logNorm F) := continuous_toAdd.comp (ideleClassLogNorm_continuous F)
    have hphase : Continuous (orbitalMomentPhase F χ z) := by
      change Continuous (fun g : Q F ↦ (χ g : ℂ) * Complex.exp (z * (logNorm F g : ℂ)))
      have hχ : Continuous (fun g : Q F ↦ (χ g : ℂ)) := continuous_subtype_val.comp χ.continuous
      fun_prop
    have hp : Continuous (fun g : Q F ↦ (logNorm F g : ℂ)^(m-j)) :=
      (Complex.continuous_ofReal.comp hlog).pow _
    exact ((φ.continuous.mul hphase).mul hp).integrable_of_hasCompactSupport
      φ.hasCompactSupport.mul_right.mul_right
  have hA (g : Q F) : L (φ g • T g u) = ∑ j : Fin (m+1), c j g * a j := by
    rw [map_smul, smul_eq_mul, orbitalSobolevMomentCLM_translate]
    rw [Fin.sum_univ_eq_sum_range (fun j : ℕ ↦ c j g * a j)]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    dsimp [a,c]
    ring
  change L (∫ g, φ g • T g u ∂μ) = _
  rw [← L.integral_comp_comm (integrable_hardySobolev_convolution_orbit μ
    (ideleClassLogNorm F) (ideleClassLogNorm_continuous F) 0 0 s hs φ u)]
  calc
    _ = ∫ g, ∑ j : Fin (m+1), c j g * a j ∂μ :=
      integral_congr_ae (.of_forall hA)
    _ = _ := by
      rw [integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro j _
        rw [integral_mul_const]
        change (∫ g, c j g ∂μ) * a j = _
        unfold orbitalConvolutionCoefficient
        dsimp only [a,c]
        ring
      · exact fun j _ ↦ (hi j).mul_const _


local instance orbitalConvolutionKMeasure : MeasurableSpace (K F) := borel _
local instance orbitalConvolutionKBorel : BorelSpace (K F) := ⟨rfl⟩
local instance orbitalConvolutionKCompact : CompactSpace (K F) := normOneIdeleClass_compact F

private abbrev logNormHom : Q F →ₜ* Multiplicative ℝ :=
  ⟨ideleClassLogNorm F, ideleClassLogNorm_continuous F⟩
private abbrev expSection : Multiplicative ℝ →ₜ* Q F :=
  ⟨ideleClassExpSection F, ideleClassExpSection_continuous F⟩
private theorem logNorm_rightInverse : RightInverse (expSection F) (logNormHom F) :=
  ideleClassLogNorm_expSection F

variable (ν : Measure (K F)) [ν.IsHaarMeasure]

private local instance orbitalConvolutionFinite : IsFiniteMeasure ν := ⟨isCompact_univ.measure_lt_top⟩
private local instance orbitalConvolutionSplitHaar : (globalClassMeasure F ν).IsHaarMeasure :=
  globalClassMeasure_isHaar F ν

private abbrev normOneAngularCoeff (ω : PontryaginDual (K F)) :
    BruhatSchwartz (Q F) →L[ℂ] 𝓢(ℝ, ℂ) :=
  angularCoeff (logNormHom F) (expSection F) (logNorm_rightInverse F)
    (K F) (ideleClassLogNorm_ker_eq_normOne F) ν ω

/-- The Mellin coefficients are Schwartz functions of Fourier frequency,
continuously in the original compact Bruhat test topology. -/
def orbitalConvolutionSchwartzCoefficients (ω : PontryaginDual (K F)) (m : ℕ) :
    BruhatCompactTest (Q F) →L[ℂ] 𝓢(ℝ, ℂ) :=
  (SchwartzMap.fourierTransformCLM ℂ).comp
    ((realMellinMonomial m).comp ((normOneAngularCoeff F ν ω).comp bruhatCompactTest_toSchwartz))

set_option maxHeartbeats 2200000 in
theorem orbitalConvolutionSchwartzCoefficients_apply (ω : PontryaginDual (K F)) (m : ℕ)
    (φ : BruhatCompactTest (Q F)) (ξ : ℝ) :
    orbitalConvolutionSchwartzCoefficients F ν ω m φ ξ =
      orbitalConvolutionCoefficient F (globalClassMeasure F ν) φ.val.val
        (normOneEulerCharacter F ω) ((↑(-2 * Real.pi * ξ) : ℂ) * Complex.I) m := by
  let e := (ideleClassLogCoordinates F).toMeasurableEquiv
  let z : ℂ := (↑(-2 * Real.pi * ξ) : ℂ) * Complex.I
  let A := normOneAngularCoeff F ν ω φ.val
  let B (t : ℝ) : ℂ := Complex.exp ((↑(-2 * Real.pi * t * ξ) : ℂ) * Complex.I) * (t : ℂ)^m
  let a (y : ℝ × K F) : ℂ := φ.val.val (e y)
  let c (y : ℝ × K F) : ℂ := (ω y.2 : ℂ)
  let b (y : ℝ × K F) : ℂ := B y.1 * (a y * c y)
  have hφ : HasCompactSupport φ.val.val := (BruhatCompactTest.algebraicEquiv φ).property
  have hb : Integrable b (volume.prod ν) := by
    have ha : Continuous a := (bruhatSchwartz_continuous φ.val).comp (ideleClassLogCoordinates F).continuous
    have hc : Continuous c := (continuous_subtype_val.comp ω.continuous).comp continuous_snd
    have hw : Continuous (fun y : ℝ × K F ↦ B y.1) := by dsimp [B]; fun_prop
    apply (hw.mul (ha.mul hc)).integrable_of_hasCompactSupport
    exact (hφ.comp_homeomorph (ideleClassLogCoordinates F)).mul_right.mul_left
  change (𝓕 (realMellinMonomial m A) : 𝓢(ℝ, ℂ)) ξ = _
  rw [SchwartzMap.fourier_coe, Real.fourier_real_eq_integral_exp_smul]
  let g (q : Q F) := φ.val.val q * orbitalMomentPhase F (normOneEulerCharacter F ω) z q *
    (logNorm F q : ℂ)^m
  change (∫ t : ℝ, Complex.exp ((↑(-2 * Real.pi * t * ξ) : ℂ) * Complex.I) •
    realMellinMonomial m A t) = ∫ q, g q ∂Measure.map e (volume.prod ν)
  rw [integral_map_equiv]
  have hg (y : ℝ × K F) : g (e y) = b y := by
    have hL : logNorm F (e y) = y.1 := congrArg Prod.fst
      ((ideleClassLogCoordinates F).symm_apply_apply y)
    have hK : ideleClassNormOnePart F (e y) = y.2 := congrArg Prod.snd
      ((ideleClassLogCoordinates F).symm_apply_apply y)
    have hχ : (normOneEulerCharacter F ω (e y) : ℂ) = (ω y.2 : ℂ) := by
      change (ω (ideleClassNormOnePart F (e y)) : ℂ) = _
      rw [hK]
    change (a y * ((normOneEulerCharacter F ω (e y) : ℂ) *
      Complex.exp (z * (logNorm F (e y) : ℂ)))) * (logNorm F (e y) : ℂ)^m = b y
    rw [hL, hχ]
    have he : z * (y.1 : ℂ) = (↑(-2 * Real.pi * y.1 * ξ) : ℂ) * Complex.I := by
      dsimp only [z]
      push_cast
      ring
    rw [he]
    dsimp only [b, B, c]
    ring
  simp_rw [hg]
  rw [integral_prod _ hb]
  apply integral_congr_ae
  refine .of_forall fun t ↦ ?_
  change Complex.exp ((↑(-2 * Real.pi * t * ξ) : ℂ) * Complex.I) •
    realMellinMonomial m A t = ∫ k : K F, b (t,k) ∂ν
  rw [realMellinMonomial_apply, smul_eq_mul, ← mul_assoc]
  change B t * A t = ∫ k : K F, B t * (a (t,k) * c (t,k)) ∂ν
  rw [integral_const_mul]
  apply congrArg (B t * ·)
  have hA := angularCoeff_apply (logNormHom F) (expSection F) (logNorm_rightInverse F)
    (K F) (ideleClassLogNorm_ker_eq_normOne F) ν ω φ.val t
  change A t = _ at hA
  rw [hA]
  apply integral_congr_ae
  refine .of_forall fun k ↦ congrArg (fun q : Q F ↦ φ.val.val q * (ω k : ℂ)) ?_
  change ideleClassExpSection F (Multiplicative.ofAdd t) * k.val =
    k.val * ideleClassExpSection F (Multiplicative.ofAdd t)
  exact mul_comm (ideleClassExpSection F (Multiplicative.ofAdd t)) (k.val : Q F)

end
end Masullo
