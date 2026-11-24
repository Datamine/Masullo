import SLocalPairedMellin
import SLocalFourierInversion
import RealTateFunctionalEquation
import ComplexTateFunctionalEquation
import FiniteTateFunctionalEquation
import SLocalMellinFourierFactor
import ArchimedeanGammaProductTest
import SLocalTateGrowth
import SLocalZetaStripGrowth
import StrictQuotientStages
import SLocalPairedMellinCovariance
import Mathlib.Analysis.Calculus.Deriv.Star

open Bornology Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology TopologicalSpace FourierTransform
open scoped Classical ENNReal NNReal NumberField SchwartzMap ComplexConjugate

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]
variable (S : Finset (HeightOneSpectrum (𝓞 F)))

private abbrev R := {w : InfinitePlace F // w.IsReal}
private abbrev C := {w : InfinitePlace F // w.IsComplex}
private abbrev X := mixedEmbedding.mixedSpace F
private abbrev K (v : S) := v.val.adicCompletion F

private def tateKernel (t : ℝ) : ℂ := Complex.exp (↑(2 * Real.pi * t) * Complex.I)

private theorem tateKernel_sum {ι : Type*} [Fintype ι] (h : ι → ℝ) :
    tateKernel (∑ v, h v) = ∏ v, tateKernel (h v) := by
  unfold tateKernel
  rw [Finset.mul_sum, Complex.ofReal_sum, Finset.sum_mul, Complex.exp_sum]

private theorem archTateKernel_split (x y : X F) :
    tateKernel (adelicArchTrace F (x*y)) =
      (∏ v : R F, tateKernel (x.1 v * y.1 v)) *
        ∏ v : C F, tateKernel (2 * (x.2 v * y.2 v).re) := by
  rw [adelicArchTrace_eq_sum_places]
  change tateKernel ((∑ v : R F, x.1 v * y.1 v) + ∑ v : C F, 2 * (x.2 v*y.2 v).re) = _
  have h (u v : ℝ) : tateKernel (u+v) = tateKernel u * tateKernel v := by
    unfold tateKernel
    rw [mul_add, Complex.ofReal_add, add_mul, Complex.exp_add]
  rw [h, tateKernel_sum, tateKernel_sum]

private theorem archTateIntegral_pure (φ : 𝓢(X F, ℂ))
    (f : R F → 𝓢(ℝ, ℂ)) (g : C F → 𝓢(ℂ, ℂ))
    (hφ : ∀ x : X F, φ x = (∏ v, f v (x.1 v)) * ∏ v, g v (x.2 v)) (y : X F) :
    (∫ x : X F, φ x * tateKernel (adelicArchTrace F (x*y)) ∂archAdditiveTamagawa F) =
      (∏ v : R F, (𝓕⁻ (f v)) (y.1 v)) * ∏ v : C F, complexTateFourier (g v) (y.2 v) := by
  let h (v : R F) (x : ℝ) := f v x * tateKernel (x * y.1 v)
  let k (v : C F) (x : ℂ) := g v x * tateKernel (2 * (x * y.2 v).re)
  have hsplit (x : X F) :
      φ x * tateKernel (adelicArchTrace F (x*y)) =
        (∏ v : R F, h v (x.1 v)) * ∏ v : C F, k v (x.2 v) := by
    rw [hφ, archTateKernel_split, mul_mul_mul_comm, ← Finset.prod_mul_distrib,
      ← Finset.prod_mul_distrib]
  simp_rw [hsplit]
  rw [archAdditiveTamagawa, integral_smul_nnreal_measure]
  change ((2 : ℝ≥0) ^ InfinitePlace.nrComplexPlaces F) •
    (∫ x, (∏ v : R F, h v (x.1 v)) * ∏ v : C F, k v (x.2 v)
      ∂(Measure.pi (fun _ : R F ↦ volume)).prod (Measure.pi (fun _ : C F ↦ volume))) = _
  have hp := integral_prod_mul (μ := Measure.pi (fun _ : R F ↦ (volume : Measure ℝ)))
    (ν := Measure.pi (fun _ : C F ↦ (volume : Measure ℂ)))
    (fun x ↦ ∏ v : R F, h v (x v)) (fun x ↦ ∏ v : C F, k v (x v))
  erw [hp, integral_fintype_prod_eq_prod, integral_fintype_prod_eq_prod]
  have hR (v : R F) : (𝓕⁻ (f v)) (y.1 v) = ∫ x, h v x := by
    rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq']
    apply integral_congr_ae
    exact .of_forall fun x ↦ by
      change Complex.exp (↑(2 * Real.pi * (y.1 v * x)) * Complex.I) * f v x =
        f v x * tateKernel (x * y.1 v)
      unfold tateKernel
      rw [mul_comm (y.1 v) x, mul_comm]
  have hC (v : C F) : complexTateFourier (g v) (y.2 v) = 2 * ∫ x, k v x :=
    complexTateFourier_eq_integral (g v) (y.2 v)
  simp_rw [hR, hC, Finset.prod_mul_distrib, Finset.prod_const]
  change ((2 : ℝ≥0) ^ InfinitePlace.nrComplexPlaces F) • (_ * _) =
    _ * ((2 : ℂ) ^ Fintype.card (C F) * _)
  rw [NNReal.smul_def, NNReal.coe_pow, Complex.real_smul, Complex.ofReal_pow]
  change (2 : ℂ) ^ InfinitePlace.nrComplexPlaces F * (_ * _) =
    _ * ((2 : ℂ) ^ InfinitePlace.nrComplexPlaces F * _)
  ring

local instance : MeasurableSpace (InfiniteAdeleRing F) := borel _
local instance : BorelSpace (InfiniteAdeleRing F) := ⟨rfl⟩
local instance (v : HeightOneSpectrum (𝓞 F)) : MeasurableSpace (v.adicCompletion F) := borel _
local instance (v : HeightOneSpectrum (𝓞 F)) : BorelSpace (v.adicCompletion F) := ⟨rfl⟩
local instance (v : HeightOneSpectrum (𝓞 F)) : (additiveHaarDifferent F v).IsAddHaarMeasure :=
  additiveHaarDifferent_isHaar F v

/-- The selected-place Fourier integral on a separated test is exactly
the product of the verified real, complex and finite local transforms. -/
theorem sLocalSelectedFourier_pure_tate (φ : 𝓢(X F, ℂ))
    (f : R F → 𝓢(ℝ, ℂ)) (g : C F → 𝓢(ℂ, ℂ))
    (hφ : ∀ x : X F, φ x = (∏ v, f v (x.1 v)) * ∏ v, g v (x.2 v))
    (h : ∀ v : S, locallyConstantTests (K F S v)) (ξ : SAdeles F S) :
    let y := infiniteAdeleMixedHomeomorph F ξ.1
    sLocalBruhatRestriction F S
      (sLocalSelectedFourier F S (sLocalBruhatPure F S φ (locallyConstantTestPiProduct h))).val ξ =
      ((∏ v : R F, (𝓕⁻ (f v)) (y.1 v)) * ∏ v : C F, complexTateFourier (g v) (y.2 v)) *
        ∏ v : S, (finitePlaceFourierTest F v.val (additiveHaarDifferent F v.val) (h v)).val (ξ.2 v) := by
  intro y
  let ν (v : S) := additiveHaarDifferent F v.val
  letI (v : S) : (ν v).IsAddHaarMeasure := additiveHaarDifferent_isHaar F v.val
  letI (v : S) : SigmaFinite (ν v) := by
    letI := finitePlace_secondCountable F v.val
    letI := finitePlace_locallyCompact F v.val
    infer_instance
  let e := (infiniteAdeleMixedHomeomorph F).symm
  letI : SecondCountableTopology (InfiniteAdeleRing F) := e.symm.isEmbedding.secondCountableTopology
  let eM := e.toMeasurableEquiv
  letI : SFinite (archAdditiveTamagawa F) := by unfold archAdditiveTamagawa; infer_instance
  let W (x : InfiniteAdeleRing F) := φ (e.symm x) *
    tateKernel (adelicArchTrace F (e.symm x * y))
  let U (v : S) (x : K F S v) := (h v).val x *
    ((finitePlaceTraceCharacter F v.val (x * ξ.2 v)).toMul : ℂ)
  rw [sLocalSelectedFourier_restrict, sLocalAdditiveProduct]
  have hsplit (x : SAdeles F S) :
      sLocalBruhatRestriction F S (sLocalBruhatPure F S φ (locallyConstantTestPiProduct h)).val x *
        ((standardAdelicCharacter F (sLocalBruhatPad F S (x*ξ))).toMul : ℂ) =
          W x.1 * ∏ v : S, U v (x.2 v) := by
    rw [sLocalBruhatPure_restrict, locallyConstantTestPiProduct_apply, sLocalFourier_phase_factor,
      archAdele_mul_adele, standardAdelicCharacter_arch, Circle.coe_exp]
    have hm : mixedArch (sLocalBruhatPad F S ξ) = y := rfl
    rw [hm, Finset.prod_mul_distrib]
    change (_ * _) * (_ * _) = _
    unfold W
    rw [mul_mul_mul_comm]
    rfl
  simp_rw [hsplit]
  have hFubini := integral_prod_mul (μ := Measure.map e (archAdditiveTamagawa F))
    (ν := Measure.pi ν) W (fun x ↦ ∏ v : S, U v (x v))
  erw [hFubini, integral_fintype_prod_eq_prod]
  have hArch : (∫ x, W x ∂Measure.map e (archAdditiveTamagawa F)) =
      (∏ v : R F, (𝓕⁻ (f v)) (y.1 v)) * ∏ v : C F, complexTateFourier (g v) (y.2 v) := by
    change (∫ x, W x ∂Measure.map eM (archAdditiveTamagawa F)) = _
    rw [integral_map_equiv]
    change (∫ x : X F, W (e x) ∂archAdditiveTamagawa F) = _
    simpa only [W, Homeomorph.symm_apply_apply] using archTateIntegral_pure F φ f g hφ y
  rw [hArch]
  rfl

private abbrev AUnits := (InfiniteAdeleRing F)ˣ
private abbrev E := sLocalBruhatImage F S
private abbrev Characters := PontryaginDual (SLocalThetaNormOne F S)

attribute [local instance] realArchUnitsMeasurable complexArchUnitsMeasurable
  realArchUnitsBorel complexArchUnitsBorel realArchUnitsSigmaCompact complexArchUnitsSigmaCompact
  complexZeta_circleMeasurable sLocalZetaUnfolding_idelesMeasurable
  sLocalZetaUnfolding_idelesBorel

variable [MeasurableSpace (AUnits F)] [BorelSpace (AUnits F)]
  [∀ v : S, MeasurableSpace (K F S v)ˣ] [∀ v : S, BorelSpace (K F S v)ˣ]
  (μ : ∀ v : S, Measure (K F S v)ˣ)
  [∀ v : S, (μ v).IsHaarMeasure] [∀ v : S, SigmaFinite (μ v)]

private abbrev a (ω : Characters F S) := sLocalRealArchParameters F S ω
private abbrev b (ω : Characters F S) := sLocalComplexArchParameters F S ω
private abbrev χ (ω : Characters F S) := sLocalFiniteZetaPhases F S ω
private abbrev ν := sLocalZetaProductMeasure F S μ (archimedeanMultiplicativeHaar F)

private theorem sLocalIdelicZeta_of_separated_restrict (ω : Characters F S) (z : ℂ)
    (hz : 0 < z.re) (p : E F S)
    (f : R F → 𝓢(ℝ, ℂ)) (g : C F → 𝓢(ℂ, ℂ))
    (h : ∀ v : S, locallyConstantTests (K F S v))
    (hp : ∀ x : SAdeles F S, let y := infiniteAdeleMixedHomeomorph F x.1
      sLocalBruhatRestriction F S p.val x =
        ((∏ v : R F, f v (y.1 v)) * ∏ v : C F, g v (y.2 v)) * ∏ v : S, (h v).val (x.2 v)) :
    sLocalIdelicZetaIntegral F S (ν F S μ) ω p z =
      ((∏ v : R F, realArchimedeanZetaContinued (a F S ω v).2 (f v) (z + (a F S ω v).1)) *
        ∏ v : C F, complexArchimedeanZetaContinued complexTamagawaAngularMeasure
          (b F S ω v).2 (g v) (z + (b F S ω v).1)) *
        ∏ v : S, finiteZetaIntegral F v.val (μ v) (χ F S ω v) (h v) z := by
  let P (v : R F) (u : ℝˣ) := sLocalRealArchWeight F S ω v z u * f v u.val
  let Q (v : C F) (u : ℂˣ) := sLocalComplexArchWeight F S ω v z u * g v u.val
  let H (v : S) (u : (K F S v)ˣ) := (h v).val u.val * (χ F S ω v u : ℂ) * finiteZetaWeight F v.val z u
  let B : ℂ := (∏ v : R F, ∫ u, P v u ∂realArchMultiplicativeHaar) *
    ∏ v : C F, ∫ u, Q v u ∂complexArchMultiplicativeHaar
  have hArch (u : ∀ v : S, (K F S v)ˣ) :
      sLocalArchZetaIntegral F S (archimedeanMultiplicativeHaar F) ω
          (sLocalBruhatFiniteSlice F S (fun v ↦ (u v).val) p) z =
        B * ∏ v : S, (h v).val (u v).val := by
    rw [sLocalArchZetaIntegral_eq_productCoordinates]
    have he (w : (R F → ℝˣ) × (C F → ℂˣ)) :
        sLocalBruhatFiniteSlice F S (fun v ↦ (u v).val) p
          (fun v ↦ (w.1 v).val, fun v ↦ (w.2 v).val) =
          ((∏ v : R F, f v (w.1 v).val) * ∏ v : C F, g v (w.2 v).val) *
            ∏ v : S, (h v).val (u v).val := by
      let y : X F := (fun v ↦ (w.1 v).val, fun v ↦ (w.2 v).val)
      let x := (infiniteAdeleMixedHomeomorph F).symm y
      have hxy : (infiniteAdeleMixedHomeomorph F) x = y :=
        (infiniteAdeleMixedHomeomorph F).apply_symm_apply y
      change (sLocalBruhatFiniteSlice F S (fun v ↦ (u v).val) p) y =
        ((∏ v : R F, f v (y.1 v)) * ∏ v : C F, g v (y.2 v)) *
        ∏ v : S, (h v).val (u v).val
      rw [← hxy]
      change (sLocalBruhatFiniteSlice F S (fun v ↦ (u v).val) p)
        ((InfiniteAdeleRing.ringEquiv_mixedSpace F) x) = _
      rw [sLocalBruhatFiniteSlice_apply]
      exact hp (x, fun v ↦ (u v).val)
    simp_rw [he]
    have he' (w : (R F → ℝˣ) × (C F → ℂˣ)) :
        ((∏ v : R F, sLocalRealArchWeight F S ω v z (w.1 v)) *
          ∏ v : C F, sLocalComplexArchWeight F S ω v z (w.2 v)) *
          (((∏ v : R F, f v (w.1 v).val) * ∏ v : C F, g v (w.2 v).val) *
            ∏ v : S, (h v).val (u v).val) =
          ((∏ v : R F, P v (w.1 v)) * ∏ v : C F, Q v (w.2 v)) *
            ∏ v : S, (h v).val (u v).val := by
      rw [← mul_assoc, mul_mul_mul_comm, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    simp_rw [he']
    rw [integral_mul_const]
    unfold archimedeanCoordinateMeasure B
    have hi := integral_prod_mul (μ := Measure.pi (fun _ : R F ↦ realArchMultiplicativeHaar))
      (ν := Measure.pi (fun _ : C F ↦ complexArchMultiplicativeHaar))
      (fun x ↦ ∏ v : R F, P v (x v)) (fun x ↦ ∏ v : C F, Q v (x v))
    erw [hi, integral_fintype_prod_eq_prod, integral_fintype_prod_eq_prod]
  rw [sLocalIdelicZetaIntegral_eq_finiteSlices F S μ (archimedeanMultiplicativeHaar F) ω p z hz]
  simp_rw [hArch, mul_assoc, ← Finset.prod_mul_distrib]
  rw [integral_const_mul]
  have hH (u : ∀ v : S, (K F S v)ˣ) :
      (∏ v : S, (h v).val (u v).val *
        ((χ F S ω v (u v) : ℂ) * finiteZetaWeight F v.val z (u v))) =
      ∏ v : S, H v (u v) := by simp only [H, mul_assoc]
  simp_rw [hH]
  erw [integral_fintype_prod_eq_prod]
  have hr (v : R F) : (∫ u, P v u ∂realArchMultiplicativeHaar) =
      realArchimedeanZetaContinued (a F S ω v).2 (f v) (z + (a F S ω v).1) := by
    have hv : 0 < (z + (a F S ω v).1).re := by
      simpa only [Complex.add_re, a, sLocalRealArchParameters_re, add_zero] using hz
    simpa only [P, sLocalRealArchWeight, Real.norm_eq_abs] using
      (realArchimedeanZetaContinued_eq_unitIntegral (a F S ω v).2 (f v) hv).2.symm
  have hc (v : C F) : (∫ u, Q v u ∂complexArchMultiplicativeHaar) =
      complexArchimedeanZetaContinued complexTamagawaAngularMeasure
        (b F S ω v).2 (g v) (z + (b F S ω v).1) := by
    have hv : 0 < (z + (b F S ω v).1).re := by
      simpa only [Complex.add_re, b, sLocalComplexArchParameters_re, add_zero] using hz
    exact (complexArchimedeanZetaContinued_eq_unitIntegral (b F S ω v).2 (g v) hv).2.symm
  unfold B
  simp_rw [hr, hc]
  rw [mul_assoc]
  rfl

private abbrev N (ω : Characters F S) (p : E F S) :=
  sLocalEulerNormalizedMellin F S μ ω p

private abbrev realTateValue (ω : Characters F S) (v : R F) (f : 𝓢(ℝ, ℂ)) (z : ℂ) :=
  let a := a F S ω v
  realArchZetaDenominator a.2 (z+a.1) * realArchimedeanZetaContinued a.2 f (z+a.1)

private abbrev complexTateValue (ω : Characters F S) (v : C F) (g : 𝓢(ℂ, ℂ)) (z : ℂ) :=
  let b := b F S ω v
  complexArchZetaDenominator b.2 (z+b.1) *
    complexArchimedeanZetaContinued complexTamagawaAngularMeasure b.2 g (z+b.1)

private theorem sLocalNormalizedMellin_of_separated_restrict (ω : Characters F S) (z : ℂ)
    (hz : 0 < z.re) (p : E F S)
    (f : R F → 𝓢(ℝ, ℂ)) (g : C F → 𝓢(ℂ, ℂ))
    (h : ∀ v : S, locallyConstantTests (K F S v))
    (hp : ∀ x : SAdeles F S, let y := infiniteAdeleMixedHomeomorph F x.1
      sLocalBruhatRestriction F S p.val x =
        ((∏ v : R F, f v (y.1 v)) * ∏ v : C F, g v (y.2 v)) * ∏ v : S, (h v).val (x.2 v)) :
    N F S μ ω p z =
      ((∏ v : R F, realTateValue F S ω v (f v) z) * ∏ v : C F, complexTateValue F S ω v (g v) z) *
        ∏ v : S, finiteProductClearedLocal F S μ (χ F S ω) v (h v) z := by
  have hZ := normalizedMellin_eq_mul_idelic F S μ ω p z hz
  change N F S μ ω p z = sLocalEulerDenominator F S ω z *
    sLocalIdelicZetaIntegral F S (ν F S μ) ω p z at hZ
  rw [hZ, sLocalIdelicZeta_of_separated_restrict F S μ ω z hz p f g h hp]
  simp only [sLocalEulerDenominator, archimedeanNumberFieldZetaDenominator,
    sLocalFiniteZetaDenominator, realTateValue, complexTateValue,
    finiteProductClearedLocal_eq F S μ (χ F S ω) _ _ _ hz, Finset.prod_mul_distrib]
  ring

omit [MeasurableSpace (AUnits F)] [BorelSpace (AUnits F)]
  [∀ v : S, MeasurableSpace (K F S v)ˣ] [∀ v : S, BorelSpace (K F S v)ˣ] in
private theorem realTateValue_reflect (ω : Characters F S) (v : R F)
    (z : ℂ) (hz : 0 < z.re) (hr : z.re < 1) (f : 𝓢(ℝ, ℂ)) :
    realTateValue F S ω v f z = (-Complex.I) ^ ((a F S ω v).2 % 2) *
      realTateValue F S ω⁻¹ v (𝓕⁻ f) (1-z) := by
  have ha := sLocalRealArchParameters_inv F S ω v
  have he (j k : ℕ) (h : j % 2 = k % 2) (g : 𝓢(ℝ, ℂ)) (w : ℂ) :
      realArchimedeanZetaContinued j g w = realArchimedeanZetaContinued k g w := by
    unfold realArchimedeanZetaContinued
    congr 1
    ext x
    rw [realZetaProfile_apply, realZetaProfile_apply, neg_one_pow_eq_pow_mod_two j,
      neg_one_pow_eq_pow_mod_two k, h]
  let u := z + (a F S ω v).1
  have hu : u.re = z.re := by simp [u, a, Complex.add_re, sLocalRealArchParameters_re]
  have hw : 1-u = 1-z + (a F S ω⁻¹ v).1 := by
    rw [show (a F S ω⁻¹ v).1 = -(a F S ω v).1 from ha.1]
    dsimp only [u]
    ring
  have hD (w : ℂ) : realArchZetaDenominator (a F S ω v).2 w =
      realArchZetaDenominator (a F S ω⁻¹ v).2 w := by
    unfold realArchZetaDenominator
    rw [show (a F S ω⁻¹ v).2 % 2 = (a F S ω v).2 % 2 from ha.2]
  change _ = _ * (realArchZetaDenominator (a F S ω⁻¹ v).2 _ *
    realArchimedeanZetaContinued (a F S ω⁻¹ v).2 _ _)
  rw [← hD, he _ _ ha.2, ← hw]
  exact realTate_normalized_fourier (a F S ω v).2 u (by rwa [hu]) (by rwa [hu]) f

omit [MeasurableSpace (AUnits F)] [BorelSpace (AUnits F)]
  [∀ v : S, MeasurableSpace (K F S v)ˣ] [∀ v : S, BorelSpace (K F S v)ˣ] in
private theorem complexTateValue_reflect (ω : Characters F S) (v : C F)
    (z : ℂ) (hz : 0 < z.re) (hr : z.re < 1) (f : 𝓢(ℂ, ℂ)) :
    complexTateValue F S ω v f z = (-Complex.I) ^ (b F S ω v).2.natAbs *
      complexTateValue F S ω⁻¹ v (complexTateFourier f) (1-z) := by
  let u := z + (b F S ω v).1
  have hu : u.re = z.re := by simp [u, b, Complex.add_re, sLocalComplexArchParameters_re]
  have hb : b F S ω⁻¹ v = (-(b F S ω v).1, -(b F S ω v).2) :=
    sLocalComplexArchParameters_inv F S ω v
  have hw : 1-u = 1-z + (b F S ω⁻¹ v).1 := by rw [hb]; dsimp only [u]; ring
  have H := complexTate_normalized_fourier (b F S ω v).2 u (by rwa [hu]) (by rwa [hu]) f
  change _ = _ * (complexArchZetaDenominator (b F S ω⁻¹ v).2 _ *
    complexArchimedeanZetaContinued complexTamagawaAngularMeasure (b F S ω⁻¹ v).2 _ _)
  rw [← hw, hb]
  exact H

private abbrev finiteTateTransform (v : S) :=
  finitePlaceFourierTest F v.val (additiveHaarDifferent F v.val)

/-- The local multipliers multiply on separated tests for the actual
S-local Mellin continuation and selected-place Fourier transform. -/
theorem exists_sLocalTateProduct_separated (ω : Characters F S) :
    ∃ ε : S → ℂ → ℂ,
      (∀ v, IsFiniteTateMultiplier F S μ (χ F S ω) v (ε v)) ∧
      ∀ (φ : 𝓢(X F, ℂ)) (f : R F → 𝓢(ℝ, ℂ)) (g : C F → 𝓢(ℂ, ℂ)),
        (∀ x : X F, φ x = (∏ v, f v (x.1 v)) * ∏ v, g v (x.2 v)) →
        ∀ (h : ∀ v : S, locallyConstantTests (K F S v)) (z : ℂ),
          0 < z.re → z.re < 1 →
          let p := sLocalBruhatPure F S φ (locallyConstantTestPiProduct h)
          N F S μ ω p z =
            (((∏ v : R F, (-Complex.I) ^ ((a F S ω v).2 % 2)) *
              ∏ v : C F, (-Complex.I) ^ (b F S ω v).2.natAbs) * ∏ v : S, ε v z) *
                N F S μ ω⁻¹ (sLocalSelectedFourier F S p) (1-z) := by
  letI : TopologicalSpace (locallyConstantTests (∀ v : S, K F S v)) := finestLocallyConvexTopology _
  obtain ⟨ε, hε, he⟩ := exists_sLocalFiniteZeta_fourier_product F S μ (χ F S ω)
  refine ⟨ε, hε, fun φ f g hφ h z hz hr ↦ ?_⟩
  let p := sLocalBruhatPure F S φ (locallyConstantTestPiProduct h)
  have hz' : 0 < (1-z).re := by simpa [Complex.sub_re, sub_pos] using hr
  have hp := sLocalNormalizedMellin_of_separated_restrict F S μ ω z hz p f g h (fun x ↦ by
    change sLocalBruhatRestriction F S p.val x =
      ((∏ v : R F, f v ((infiniteAdeleMixedHomeomorph F x.1).1 v)) *
        ∏ v : C F, g v ((infiniteAdeleMixedHomeomorph F x.1).2 v)) * ∏ v : S, (h v).val (x.2 v)
    rw [sLocalBruhatPure_restrict, locallyConstantTestPiProduct_apply, hφ]
    rfl)
  have hFourier := sLocalNormalizedMellin_of_separated_restrict F S μ ω⁻¹ (1-z) hz'
    (sLocalSelectedFourier F S p) (fun v ↦ 𝓕⁻ (f v)) (fun v ↦ complexTateFourier (g v))
    (fun v ↦ finiteTateTransform F S v (h v))
    (sLocalSelectedFourier_pure_tate F S φ f g hφ h)
  have hFin := he h z
  rw [sLocalFiniteZetaCleared_piProduct, sLocalFiniteZetaCleared_piProduct] at hFin
  have hχ : (fun v ↦ (χ F S ω v)⁻¹) = χ F S ω⁻¹ := funext fun v ↦
    (sLocalFiniteZetaPhases_inv F S ω v).symm
  rw [hχ] at hFin
  change N F S μ ω p z = _ * N F S μ ω⁻¹ (sLocalSelectedFourier F S p) (1-z)
  rw [hp, hFourier, hFin]
  simp_rw [realTateValue_reflect F S ω _ z hz hr, complexTateValue_reflect F S ω _ z hz hr,
    Finset.prod_mul_distrib]
  ring

/-- The product of the real, complex, and selected finite epsilon factors. -/
def sLocalTateEpsilonProduct (ω : Characters F S) (ε : S → ℂ → ℂ) (z : ℂ) : ℂ :=
  ((∏ v : R F, (-Complex.I) ^ ((a F S ω v).2 % 2)) *
    ∏ v : C F, (-Complex.I) ^ (b F S ω v).2.natAbs) * ∏ v : S, ε v z

omit [MeasurableSpace (AUnits F)] [BorelSpace (AUnits F)] [∀ v : S, SigmaFinite (μ v)] in
private theorem finiteTateMultiplier_norm_le_on_strip (ξ : ∀ v : S,
    (K F S v)ˣ →ₜ* Circle) (v : S) (ε : ℂ → ℂ)
    (hε : IsFiniteTateMultiplier F S μ ξ v ε) (l r : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, z.re ∈ Icc l r → ‖ε z‖ ≤ C := by
  obtain ⟨b, B, hB, hb⟩ := exists_cleared_finite_reference F S μ (fun v ↦ (ξ v)⁻¹) v
  obtain ⟨g, hg⟩ := finitePlaceFourierTest_tamagawa_surjective F v.val b
  obtain ⟨M, hM, hbound⟩ :=
    finiteZeta_localCleared_norm_le_on_strip F v.val (μ v) (ξ v) g l r
  refine ⟨M * ‖B⁻¹‖, mul_nonneg hM (norm_nonneg _), fun z hz ↦ ?_⟩
  have he := hε.2.2.2.1 g z
  change _ = ε z * finiteProductClearedLocal F S μ (fun v ↦ (ξ v)⁻¹) v
    (finitePlaceFourierTest F v.val (additiveHaarDifferent F v.val) g) (1 - z) at he
  rw [hg, hb] at he
  have hεz : ε z = finiteProductClearedLocal F S μ ξ v g z * B⁻¹ := by
    rw [he, mul_assoc, mul_inv_cancel₀ hB, mul_one]
  rw [hεz, norm_mul]
  exact mul_le_mul_of_nonneg_right (hbound z hz) (norm_nonneg _)

omit [MeasurableSpace (AUnits F)] [BorelSpace (AUnits F)] [∀ v : S, SigmaFinite (μ v)] in
private theorem inverseFiniteTateMultiplier_norm_le_on_strip (ξ : ∀ v : S,
    (K F S v)ˣ →ₜ* Circle) (v : S) (ε : ℂ → ℂ)
    (hε : IsFiniteTateMultiplier F S μ ξ v ε) (l r : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, z.re ∈ Icc l r → ‖(ε z)⁻¹‖ ≤ C := by
  obtain ⟨f, B, hB, hf⟩ := exists_cleared_finite_reference F S μ ξ v
  let g := finitePlaceFourierTest F v.val (additiveHaarDifferent F v.val) f
  obtain ⟨M, hM, hb⟩ := finiteZeta_localCleared_norm_le_on_strip F v.val (μ v)
    ((ξ v)⁻¹) g (1-r) (1-l)
  refine ⟨M * ‖B⁻¹‖, mul_nonneg hM (norm_nonneg _), fun z hz ↦ ?_⟩
  have he := hε.2.2.2.1 f z
  change _ = ε z * finiteProductClearedLocal F S μ (fun v ↦ (ξ v)⁻¹) v g (1-z) at he
  rw [hf] at he
  have hi : (ε z)⁻¹ = finiteProductClearedLocal F S μ (fun v ↦ (ξ v)⁻¹) v g (1-z) * B⁻¹ := by
    rw [he, mul_inv, mul_left_comm, mul_inv_cancel₀ (right_ne_zero_of_mul (he ▸ hB)), mul_one]
  rw [hi, norm_mul]
  have hz' : (1-z).re ∈ Icc (1-r) (1-l) := by
    simp only [Complex.sub_re, Complex.one_re, mem_Icc]
    constructor <;> linarith [hz.1, hz.2]
  exact mul_le_mul_of_nonneg_right (hb _ hz') (norm_nonneg _)

omit [MeasurableSpace (AUnits F)] [BorelSpace (AUnits F)] [∀ v : S, SigmaFinite (μ v)] in
private theorem inverseTateEpsilonProduct_norm_le_on_strip (ω : Characters F S) (ε : S → ℂ → ℂ)
    (hε : ∀ v, IsFiniteTateMultiplier F S μ (χ F S ω) v (ε v)) (l r : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, z.re ∈ Icc l r → ‖(sLocalTateEpsilonProduct F S ω ε z)⁻¹‖ ≤ C := by
  choose C hC hb using fun v ↦
    inverseFiniteTateMultiplier_norm_le_on_strip F S μ (χ F S ω) v (ε v) (hε v) l r
  refine ⟨∏ v, C v, Finset.prod_nonneg fun v _ ↦ hC v, fun z hz ↦ ?_⟩
  simp only [sLocalTateEpsilonProduct, mul_inv, ← Finset.prod_inv_distrib, norm_mul, norm_prod,
    norm_inv, norm_pow, norm_neg, Complex.norm_I, one_pow, inv_one, Finset.prod_const_one, mul_one]
  simpa only [norm_inv, one_mul] using
    (Finset.prod_le_prod (s := Finset.univ) (fun v _ ↦ norm_nonneg ((ε v z)⁻¹)) (fun v _ ↦ hb v z hz))

omit [MeasurableSpace (AUnits F)] [BorelSpace (AUnits F)] [∀ v : S, SigmaFinite (μ v)] in
/-- The entire multiplier in the S-local Tate equation is uniformly
bounded on closed vertical strips, including at ramified places. -/
theorem sLocalTateEpsilonProduct_norm_le_on_strip (ω : Characters F S) (ε : S → ℂ → ℂ)
    (hε : ∀ v, IsFiniteTateMultiplier F S μ (χ F S ω) v (ε v)) (l r : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, z.re ∈ Icc l r →
      ‖sLocalTateEpsilonProduct F S ω ε z‖ ≤ C := by
  choose C hC hb using fun v ↦
    finiteTateMultiplier_norm_le_on_strip F S μ (χ F S ω) v (ε v) (hε v) l r
  refine ⟨∏ v, C v, Finset.prod_nonneg fun v _ ↦ hC v, fun z hz ↦ ?_⟩
  simp only [sLocalTateEpsilonProduct, norm_mul, norm_prod, norm_pow, norm_neg,
    Complex.norm_I, one_pow, Finset.prod_const_one, one_mul]
  exact Finset.prod_le_prod (fun _ _ ↦ norm_nonneg _) (fun v _ ↦ hb v z hz)

omit [MeasurableSpace (AUnits F)] [BorelSpace (AUnits F)]
  [∀ v : S, MeasurableSpace (K F S v)ˣ] [∀ v : S, BorelSpace (K F S v)ˣ] in
private theorem realTateRatio_sharp_on_strip (ω : Characters F S) (v : R F) (l r : ℝ) :
    ∃ C T : ℝ, 0 ≤ C ∧ ∀ z : ℂ, z.re ∈ Icc l r → T ≤ |z.im| →
      ‖realArchZetaDenominator (a F S ω⁻¹ v).2 (1-z+(a F S ω⁻¹ v).1) /
        realArchZetaDenominator (a F S ω v).2 (z+(a F S ω v).1)‖ ≤
        C * (1 + |z.im|) ^ (z.re - 1/2) := by
  let m := (a F S ω v).2 % 2
  let α := (a F S ω v).1
  obtain ⟨C, T, hC, hbound⟩ := gamma_affineReflectedRatio_sharp_on_strip
    Real.pi (m : ℝ) 2 l r (by linarith [Real.pi_gt_three]) (by norm_num) α
    (sLocalRealArchParameters_re F S ω v)
  refine ⟨C, T, hC, fun z hz ht ↦ ?_⟩
  have h := sLocalRealArchParameters_inv F S ω v
  unfold realArchZetaDenominator
  rw [h.1, h.2, inv_div_inv, Complex.Gammaℝ_def, Complex.Gammaℝ_def]
  rw [show z.re - 1/2 = (2 * z.re - 1) / 2 by ring]
  simpa only [neg_div, sub_eq_add_neg, Complex.ofReal_ofNat, Complex.ofReal_natCast] using
    hbound z hz ht

omit [MeasurableSpace (AUnits F)] [BorelSpace (AUnits F)]
  [∀ v : S, MeasurableSpace (K F S v)ˣ] [∀ v : S, BorelSpace (K F S v)ˣ] in
private theorem complexTateRatio_sharp_on_strip (ω : Characters F S) (v : C F) (l r : ℝ) :
    ∃ C T : ℝ, 0 ≤ C ∧ ∀ z : ℂ, z.re ∈ Icc l r → T ≤ |z.im| →
      ‖complexArchZetaDenominator (b F S ω⁻¹ v).2 (1-z+(b F S ω⁻¹ v).1) /
        complexArchZetaDenominator (b F S ω v).2 (z+(b F S ω v).1)‖ ≤
        C * (1 + |z.im|) ^ (2 * (z.re - 1/2)) := by
  let m := (b F S ω v).2.natAbs
  let α := (b F S ω v).1
  obtain ⟨C, T, hC, hbound⟩ := gamma_affineReflectedRatio_sharp_on_strip
    (2 * Real.pi) ((m : ℝ) / 2) 1 l r (by linarith [Real.pi_gt_three]) zero_lt_one α
    (sLocalComplexArchParameters_re F S ω v)
  refine ⟨C, T, hC, fun z hz ht ↦ ?_⟩
  rw [show b F S ω⁻¹ v = (-α, -(b F S ω v).2) from sLocalComplexArchParameters_inv F S ω v]
  unfold complexArchZetaDenominator
  simp only [Int.natAbs_neg, inv_div_inv, Complex.Gammaℂ_def, mul_assoc, mul_div_mul_left _ _ (by norm_num : (2 : ℂ) ≠ 0)]
  rw [show 2 * (z.re - 1/2) = (2 * z.re - 1) / 1 by ring]
  simpa only [Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_natCast, Complex.ofReal_div,
    Complex.ofReal_one, div_one, sub_eq_add_neg] using hbound z hz ht

private theorem stripFiniteProd_sharp {ι : Type*} [Fintype ι] (f : ι → ℂ → ℂ)
    (e : ℂ → ℝ) (l r : ℝ)
    (hf : ∀ i, ∃ C T : ℝ, 0 ≤ C ∧ ∀ z : ℂ, z.re ∈ Icc l r → T ≤ |z.im| →
      ‖f i z‖ ≤ C * (1 + |z.im|) ^ e z) :
    ∃ C T : ℝ, 0 ≤ C ∧ ∀ z : ℂ, z.re ∈ Icc l r → T ≤ |z.im| →
      ‖∏ i, f i z‖ ≤ C * (1 + |z.im|) ^ ((Fintype.card ι : ℝ) * e z) := by
  choose C T hC h using hf
  refine ⟨∏ i, C i, ∑ i, max (T i) 0, Finset.prod_nonneg (fun i _ ↦ hC i), ?_⟩
  intro z hz ht
  have hexp : (Fintype.card ι : ℝ) * e z = ∑ _i : ι, e z := by simp
  rw [norm_prod, hexp, Real.rpow_sum_of_pos (by positivity), ← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod (fun _ _ ↦ norm_nonneg _)
  intro i hi
  exact h i z hz ((le_max_left _ _).trans
    ((Finset.single_le_sum (fun j _ ↦ le_max_right (T j) 0) hi).trans ht))

omit [MeasurableSpace (AUnits F)] [BorelSpace (AUnits F)]
  [∀ v : S, MeasurableSpace (K F S v)ˣ] [∀ v : S, BorelSpace (K F S v)ˣ] in
/-- The real and complex Gamma powers add to the field-degree exponent. -/
theorem sLocalTateArchimedeanRatio_sharp_on_strip (ω : Characters F S) (l r : ℝ) :
    ∃ C T : ℝ, 0 ≤ C ∧ ∀ z : ℂ, z.re ∈ Icc l r → T ≤ |z.im| →
      ‖archimedeanNumberFieldZetaDenominator F (a F S ω⁻¹) (b F S ω⁻¹) (1 - z) /
        archimedeanNumberFieldZetaDenominator F (a F S ω) (b F S ω) z‖ ≤
        C * (1 + |z.im|) ^ ((Module.finrank ℚ F : ℝ) * (z.re - 1/2)) := by
  obtain ⟨C₁,T₁,hC₁,h₁⟩ := stripFiniteProd_sharp _ (fun z ↦ z.re - 1/2) l r
    (fun v ↦ realTateRatio_sharp_on_strip F S ω v l r)
  obtain ⟨C₂,T₂,hC₂,h₂⟩ := stripFiniteProd_sharp _ (fun z ↦ 2 * (z.re - 1/2)) l r
    (fun v ↦ complexTateRatio_sharp_on_strip F S ω v l r)
  refine ⟨C₁ * C₂, max T₁ T₂, mul_nonneg hC₁ hC₂, fun z hz ht ↦ ?_⟩
  simp only [archimedeanNumberFieldZetaDenominator, div_eq_mul_inv, mul_inv, ← Finset.prod_inv_distrib]
  rw [mul_mul_mul_comm, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, norm_mul]
  have hd : (Fintype.card (R F) : ℝ) + 2 * (Fintype.card (C F) : ℝ) =
      Module.finrank ℚ F := by
    exact_mod_cast InfinitePlace.card_add_two_mul_card_eq_rank F
  calc
    _ ≤ (C₁ * (1 + |z.im|) ^ ((Fintype.card (R F) : ℝ) * (z.re - 1/2))) *
        (C₂ * (1 + |z.im|) ^ ((Fintype.card (C F) : ℝ) * (2 * (z.re - 1/2)))) :=
      mul_le_mul (h₁ z hz ((le_max_left _ _).trans ht)) (h₂ z hz ((le_max_right _ _).trans ht))
        (norm_nonneg _) (by positivity)
    _ = _ := by
      rw [mul_mul_mul_comm C₁ _, ← Real.rpow_add (by positivity), ← hd]
      congr 2
      ring

omit [MeasurableSpace (AUnits F)] [BorelSpace (AUnits F)]
  [∀ v : S, MeasurableSpace (K F S v)ˣ] [∀ v : S, BorelSpace (K F S v)ˣ] in
/-- A nonnegative integral degree suffices when only polynomial growth is needed. -/
theorem sLocalTateArchimedeanRatio_norm_le_on_strip (ω : Characters F S) (l r : ℝ) :
    ∃ (C T : ℝ) (k : ℕ), 0 ≤ C ∧ ∀ z : ℂ, z.re ∈ Icc l r → T ≤ |z.im| →
      ‖archimedeanNumberFieldZetaDenominator F (a F S ω⁻¹) (b F S ω⁻¹) (1 - z) /
        archimedeanNumberFieldZetaDenominator F (a F S ω) (b F S ω) z‖ ≤
        C * (1 + |z.im|)^k := by
  obtain ⟨C,T,hC,h⟩ := sLocalTateArchimedeanRatio_sharp_on_strip F S ω l r
  let D : ℝ := Module.finrank ℚ F
  obtain ⟨k,hk⟩ := exists_nat_gt (D * (r - 1/2))
  refine ⟨C,T,k,hC,fun z hz ht ↦ (h z hz ht).trans ?_⟩
  rw [← Real.rpow_natCast]
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le
    (by linarith [abs_nonneg z.im])
    ((mul_le_mul_of_nonneg_left (sub_le_sub_right hz.2 _) (by positivity : 0 ≤ D)).trans hk.le)) hC

omit [MeasurableSpace (AUnits F)] [BorelSpace (AUnits F)] [∀ v : S, SigmaFinite (μ v)] in
private theorem tateRatio_finiteCleared_norm_le_on_strip (ω : Characters F S)
    (P : ℂ → ℂ) (l r : ℝ)
    (hP : ∃ E : ℝ, 0 ≤ E ∧ ∀ z : ℂ, z.re ∈ Icc l r → ‖P z‖ ≤ E)
    (hr : r < 1) :
    ∃ (C T : ℝ) (k : ℕ), 0 ≤ C ∧ ∀ z : ℂ, z.re ∈ Icc l r → T ≤ |z.im| →
      ‖sLocalFiniteZetaDenominator F S (χ F S ω) z *
        sLocalExplicitTateFactor F S ω P z‖ ≤
        C * (1 + |z.im|)^k := by
  obtain ⟨E, hE, hEp⟩ := hP
  obtain ⟨A, T, k, hA, hAp⟩ := sLocalTateArchimedeanRatio_norm_le_on_strip F S ω l r
  refine ⟨E * A * 2^S.card, T, k, by positivity, fun z hz ht ↦ ?_⟩
  let D (ξ : Characters F S) := sLocalFiniteZetaDenominator F S (χ F S ξ)
  let G (ξ : Characters F S) := archimedeanNumberFieldZetaDenominator F (a F S ξ) (b F S ξ)
  have hfactor : D ω z * sLocalExplicitTateFactor F S ω P z =
      (D ω z * (D ω z)⁻¹) * (P z * (G ω⁻¹ (1-z) / G ω z) * D ω⁻¹ (1-z)) := by
    unfold sLocalExplicitTateFactor sLocalEulerFactor sLocalEulerDenominator
    change D ω z * (P z * (G ω z * D ω z)⁻¹ * (G ω⁻¹ (1-z) * D ω⁻¹ (1-z))) = _
    simp only [mul_inv, div_eq_mul_inv]
    ring
  change ‖D ω z * sLocalExplicitTateFactor F S ω P z‖ ≤ _
  rw [hfactor, norm_mul, norm_mul, norm_mul]
  have hD : ‖D ω z * (D ω z)⁻¹‖ ≤ 1 := by
    by_cases he : D ω z = 0
    · simp [he]
    · simp [mul_inv_cancel₀ he]
  have hpos : 0 < (1-z).re := by
    rw [Complex.sub_re, Complex.one_re]
    linarith [hz.2]
  simp only [norm_mul] at hD ⊢
  have hG := hAp z hz ht
  calc
    _ ≤ 1 * ((E * (A * (1 + |z.im|)^k)) * 2^S.card) := by
      exact mul_le_mul hD
        (mul_le_mul (mul_le_mul (hEp _ hz) hG (by positivity) hE)
          (norm_sLocalFiniteZetaDenominator_le F S _ _ hpos) (norm_nonneg _) (by positivity))
        (by positivity) zero_le_one
    _ = _ := by ring

omit [MeasurableSpace (AUnits F)] [BorelSpace (AUnits F)] [∀ v : S, SigmaFinite (μ v)] in
/-- Clearing the finite Euler denominator gives polynomial strip growth. -/
theorem sLocalTateRatio_finiteCleared_norm_le_on_strip (ω : Characters F S)
    (ε : S → ℂ → ℂ) (hε : ∀ v, IsFiniteTateMultiplier F S μ (χ F S ω) v (ε v))
    (l r : ℝ) (hr : r < 1) :
    ∃ (C T : ℝ) (k : ℕ), 0 ≤ C ∧ ∀ z : ℂ, z.re ∈ Icc l r → T ≤ |z.im| →
      ‖sLocalFiniteZetaDenominator F S (χ F S ω) z *
        sLocalExplicitTateFactor F S ω (sLocalTateEpsilonProduct F S ω ε) z‖ ≤
        C * (1 + |z.im|)^k :=
  tateRatio_finiteCleared_norm_le_on_strip F S ω _ l r
    (sLocalTateEpsilonProduct_norm_le_on_strip F S μ ω ε hε l r) hr

omit [MeasurableSpace (AUnits F)] [BorelSpace (AUnits F)]
  [∀ v : S, BorelSpace (K F S v)ˣ] [∀ v : S, SigmaFinite (μ v)] in
private theorem inverseFiniteDenominator_bound (ω : Characters F S) (l : ℝ) (hl : 0 < l) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, l ≤ z.re →
      ‖(sLocalFiniteZetaDenominator F S (χ F S ω) z)⁻¹‖ ≤ C := by
  let L (v : S) := Real.log (v.val.asIdeal.absNorm : ℝ)
  let a (v : S) := 1 - Real.exp (-l * L v)
  have hL (v : S) : 0 < L v := Real.log_pos (by
    exact_mod_cast HeightOneSpectrum.one_lt_absNorm v.val)
  have ha (v : S) : 0 < a v := sub_pos.mpr (Real.exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos
    (neg_neg_of_pos hl) (hL v)))
  refine ⟨∏ v, max 1 (a v)⁻¹, Finset.prod_nonneg fun _ _ ↦ zero_le_one.trans (le_max_left _ _),
    fun z hz ↦ ?_⟩
  unfold sLocalFiniteZetaDenominator
  rw [← Finset.prod_inv_distrib, norm_prod]
  apply Finset.prod_le_prod (fun _ _ ↦ norm_nonneg _)
  intro v _
  split_ifs with hv
  · have he : ‖finiteZetaRatio F v.val (χ F S ω v) z‖ = Real.exp (-z.re * L v) := by
      simp only [finiteZetaRatio, L, norm_mul, Circle.norm_coe, one_mul, Complex.norm_exp,
        Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    have hq : a v ≤ ‖finiteZetaDenominator F v.val (χ F S ω v) z‖ := by
      unfold finiteZetaDenominator
      calc
        _ ≤ 1 - ‖finiteZetaRatio F v.val (χ F S ω v) z‖ := by
          rw [he]
          have h := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_neg hz) (hL v).le)
          dsimp [a]
          linarith
        _ ≤ _ := by simpa only [norm_one] using
          (norm_sub_norm_le (1 : ℂ) (finiteZetaRatio F v.val (χ F S ω v) z))
    rw [norm_inv]
    exact (inv_le_inv₀ ((ha v).trans_le hq) (ha v)).mpr hq |>.trans (le_max_right _ _)
  · simpa only [inv_one, norm_one] using (le_max_left (1 : ℝ) (a v)⁻¹)

omit [MeasurableSpace (AUnits F)] [BorelSpace (AUnits F)]
  [∀ v : S, BorelSpace (K F S v)ˣ] in
private theorem sLocalFiniteZetaDenominator_norm_le_of_re_ge (ω : Characters F S) (l : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, l ≤ z.re →
      ‖sLocalFiniteZetaDenominator F S (χ F S ω) z‖ ≤ C := by
  let L (v : S) := Real.log (v.val.asIdeal.absNorm : ℝ)
  have hL (v : S) : 0 ≤ L v := (Real.log_pos (by
    exact_mod_cast HeightOneSpectrum.one_lt_absNorm v.val)).le
  refine ⟨∏ v, (1 + Real.exp (-l * L v)), by positivity, fun z hz ↦ ?_⟩
  unfold sLocalFiniteZetaDenominator
  rw [norm_prod]
  apply Finset.prod_le_prod (fun _ _ ↦ norm_nonneg _)
  intro v _
  split_ifs
  · unfold finiteZetaDenominator
    have hnorm : ‖finiteZetaRatio F v.val (χ F S ω v) z‖ = Real.exp (-z.re * L v) := by
      simp only [finiteZetaRatio, L, norm_mul, Circle.norm_coe, one_mul, Complex.norm_exp,
        Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    calc
      _ ≤ ‖(1 : ℂ)‖ + ‖finiteZetaRatio F v.val (χ F S ω v) z‖ := norm_sub_le _ _
      _ ≤ _ := by rw [norm_one, hnorm]; gcongr
  · rw [norm_one]
    exact le_add_of_nonneg_right (Real.exp_nonneg _)

omit [MeasurableSpace (AUnits F)] [BorelSpace (AUnits F)] [∀ v : S, SigmaFinite (μ v)] in
/-- The actual S-local Tate multiplier has the field-degree vertical exponent
on every strictly positive closed strip, including strips crossing one. -/
theorem sLocalTateRatio_sharp_on_strip (ω : Characters F S)
    (ε : S → ℂ → ℂ) (hε : ∀ v, IsFiniteTateMultiplier F S μ (χ F S ω) v (ε v))
    (l r : ℝ) (hl : 0 < l) :
    let ρ := sLocalExplicitTateFactor F S ω (sLocalTateEpsilonProduct F S ω ε)
    ∃ C T : ℝ, 0 ≤ C ∧ ∀ z : ℂ, z.re ∈ Icc l r → T ≤ |z.im| →
      ‖ρ z‖ ≤ C * (1 + |z.im|) ^ ((Module.finrank ℚ F : ℝ) * (z.re - 1/2)) := by
  intro ρ
  obtain ⟨E,hE,hP⟩ := sLocalTateEpsilonProduct_norm_le_on_strip F S μ ω ε hε l r
  obtain ⟨A,T,hA,hG⟩ := sLocalTateArchimedeanRatio_sharp_on_strip F S ω l r
  obtain ⟨B,hB,hD⟩ := inverseFiniteDenominator_bound F S ω l hl
  obtain ⟨C,hC,hR⟩ := sLocalFiniteZetaDenominator_norm_le_of_re_ge F S ω⁻¹ (1-r)
  refine ⟨E * A * B * C,T,by positivity,fun z hz ht ↦ ?_⟩
  let D (ξ : Characters F S) := sLocalFiniteZetaDenominator F S (χ F S ξ)
  let G (ξ : Characters F S) := archimedeanNumberFieldZetaDenominator F (a F S ξ) (b F S ξ)
  have he : ρ z = sLocalTateEpsilonProduct F S ω ε z *
      (G ω⁻¹ (1-z) / G ω z) * (D ω z)⁻¹ * D ω⁻¹ (1-z) := by
    change sLocalTateEpsilonProduct F S ω ε z * (G ω z * D ω z)⁻¹ *
      (G ω⁻¹ (1-z) * D ω⁻¹ (1-z)) = _
    simp only [mul_inv, div_eq_mul_inv]
    ring
  rw [he, norm_mul, norm_mul, norm_mul]
  calc
    _ ≤ E * (A * (1 + |z.im|) ^ ((Module.finrank ℚ F : ℝ) * (z.re - 1/2))) * B * C :=
      mul_le_mul (mul_le_mul (mul_le_mul (hP z hz) (hG z hz ht) (norm_nonneg _) hE)
        (hD z hz.1) (norm_nonneg _) (by positivity))
        (hR (1-z) (by simp only [Complex.sub_re, Complex.one_re]; linarith [hz.2]))
        (norm_nonneg _) (by positivity)
    _ = _ := by ring

omit [MeasurableSpace (AUnits F)] [BorelSpace (AUnits F)] [∀ v : S, SigmaFinite (μ v)] in
/-- Corrected Proposition 3.3.1.5(3), with one logarithmic factor per derivative
and the sum of the real and complex Gamma exponents. -/
theorem sLocalTateRatio_iteratedDeriv_sharp (ω : Characters F S)
    (ε : S → ℂ → ℂ) (hε : ∀ v, IsFiniteTateMultiplier F S μ (χ F S ω) v (ε v))
    (k : ℕ) :
    let ρ := sLocalExplicitTateFactor F S ω (sLocalTateEpsilonProduct F S ω ε)
    (∀ z : ℂ, 0 < z.re → AnalyticAt ℂ (iteratedDeriv k ρ) z) ∧
    ∀ l r : ℝ, 0 < l → ∃ C T : ℝ, 0 ≤ C ∧
      ∀ z : ℂ, z.re ∈ Icc l r → T ≤ |z.im| →
        ‖iteratedDeriv k ρ z‖ ≤ C *
          (1 + |z.im|) ^ ((Module.finrank ℚ F : ℝ) * (z.re - 1/2)) *
            Real.log (1 + |z.im|) ^ k := by
  intro ρ
  have ha (z : ℂ) (hz : 0 < z.re) : AnalyticAt ℂ ρ z := by
    have hp : AnalyticAt ℂ (sLocalTateEpsilonProduct F S ω ε) z :=
      analyticAt_const.mul (Finset.analyticAt_fun_prod _ fun v _ ↦ (hε v).1 z trivial)
    have hR := (sLocalEulerDenominator_analytic F S ω⁻¹ (1-z)).comp
      (f := fun u : ℂ ↦ 1-u) (x := z) (analyticAt_const.sub analyticAt_id)
    exact (hp.mul ((sLocalEulerDenominator_analytic F S ω z).inv
      (sLocalEulerDenominator_ne_zero_of_pos F S ω hz))).mul hR
  refine ⟨fun z hz ↦ by simpa only [iteratedDeriv_eq_iterate] using (ha z hz).iterated_deriv k,
    fun l r hl ↦ ?_⟩
  exact iteratedDeriv_affine_vertical_bound ha (Module.finrank ℚ F : ℝ) (by positivity)
    l r hl (sLocalTateRatio_sharp_on_strip F S μ ω ε hε (l/2) (r+1) (by positivity)) k

set_option maxHeartbeats 700000 in
omit [MeasurableSpace (AUnits F)] [BorelSpace (AUnits F)] [∀ v : S, SigmaFinite (μ v)] in
private theorem tateRatio_overlap_growth (ω : Characters F S)
    (P : ℂ → ℂ) (hP : ∀ z, AnalyticAt ℂ P z)
    (hB : ∀ l r : ℝ, ∃ E : ℝ, 0 ≤ E ∧ ∀ z : ℂ, z.re ∈ Icc l r → ‖P z‖ ≤ E) :
    let ρ := sLocalExplicitTateFactor F S ω P
    (∀ z : ℂ, 0 < z.re → z.re < 1 → AnalyticAt ℂ ρ z) ∧
    ∀ l r : ℝ, 0 < l → r < 1 →
      ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧ ∀ z : ℂ, z.re ∈ Icc l r →
        ‖ρ z‖ ≤ C * (1 + |z.im|)^k := by
  intro ρ
  let D := sLocalFiniteZetaDenominator F S (χ F S ω)
  have hA (z : ℂ) (hz : 0 < z.re) : AnalyticAt ℂ ρ z := by
    have hR := (sLocalEulerDenominator_analytic F S ω⁻¹ (1-z)).comp
      (f := fun u : ℂ ↦ 1-u) (x := z) (analyticAt_const.sub analyticAt_id)
    exact ((hP z).mul ((sLocalEulerDenominator_analytic F S ω z).inv
      (sLocalEulerDenominator_ne_zero_of_pos F S ω hz))).mul hR
  refine ⟨fun z hz _ ↦ hA z hz, fun l r hl hr ↦ ?_⟩
  obtain ⟨A,T,k,hA₀,hb⟩ := tateRatio_finiteCleared_norm_le_on_strip F S ω P l r (hB l r) hr
  obtain ⟨B,hB₀,hD⟩ := inverseFiniteDenominator_bound F S ω l hl
  let R := Icc l r ×ℂ Icc (-(max T 0)) (max T 0)
  have hR : IsCompact R := by
    apply Metric.isCompact_of_isClosed_isBounded
    · exact (isClosed_Icc.preimage Complex.continuous_re).inter
        (isClosed_Icc.preimage Complex.continuous_im)
    · exact (Metric.isBounded_Icc _ _).reProdIm (Metric.isBounded_Icc _ _)
  have hcont : ContinuousOn (fun z ↦ ‖ρ z‖) R := fun z hz ↦
    ((hA z (hl.trans_le hz.1.1)).continuousAt.norm).continuousWithinAt
  obtain ⟨M,hM⟩ := (hR.image_of_continuousOn hcont).bddAbove
  let K := max (B*A) (max M 0)
  have hK : 0 ≤ K := (le_max_right M 0).trans (le_max_right _ _)
  refine ⟨K,k,hK, fun z hz ↦ ?_⟩
  by_cases ht : T ≤ |z.im|
  · have hn : D z ≠ 0 :=
      sLocalFiniteZetaDenominator_ne_zero_of_pos F S (χ F S ω) z (hl.trans_le hz.1)
    have he : ‖ρ z‖ = ‖(D z)⁻¹‖ * ‖D z * ρ z‖ := by
      rw [← norm_mul, ← mul_assoc, inv_mul_cancel₀ hn, one_mul]
    rw [he]
    calc
      _ ≤ B * (A * (1 + |z.im|)^k) := mul_le_mul (hD z hz.1) (hb z hz ht) (norm_nonneg _) hB₀
      _ ≤ K * (1 + |z.im|)^k := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  · have hzR : z ∈ R := ⟨hz, abs_le.mp ((le_of_lt (lt_of_not_ge ht)).trans (le_max_left _ _))⟩
    have h₁ : 1 ≤ (1 + |z.im|)^k := one_le_pow₀ (by linarith [abs_nonneg z.im])
    exact (hM (mem_image_of_mem _ hzR)).trans
      ((le_max_left _ _).trans ((le_max_right _ _).trans (le_mul_of_one_le_right hK h₁)))

omit [MeasurableSpace (AUnits F)] [BorelSpace (AUnits F)] [∀ v : S, SigmaFinite (μ v)] in
/-- The actual Tate factor is holomorphic and grows polynomially on closed
substrips of the overlap. -/
theorem sLocalTateRatio_overlap_growth (ω : Characters F S)
    (ε : S → ℂ → ℂ) (hε : ∀ v, IsFiniteTateMultiplier F S μ (χ F S ω) v (ε v)) :
    let ρ := sLocalExplicitTateFactor F S ω (sLocalTateEpsilonProduct F S ω ε)
    (∀ z : ℂ, 0 < z.re → z.re < 1 → AnalyticAt ℂ ρ z) ∧
    ∀ l r : ℝ, 0 < l → r < 1 →
      ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧ ∀ z : ℂ, z.re ∈ Icc l r →
        ‖ρ z‖ ≤ C * (1 + |z.im|)^k :=
  tateRatio_overlap_growth F S ω _
    (fun z ↦ analyticAt_const.mul (Finset.analyticAt_fun_prod _ fun v _ ↦ (hε v).1 z trivial))
    (sLocalTateEpsilonProduct_norm_le_on_strip F S μ ω ε hε)

omit [MeasurableSpace (AUnits F)] [BorelSpace (AUnits F)] [∀ v : S, SigmaFinite (μ v)] in
/-- The reciprocal of the actual Tate factor has the same holomorphy and
polynomial strip growth on the overlap. -/
theorem sLocalTateRatio_inverse_overlap_growth (ω : Characters F S)
    (ε : S → ℂ → ℂ) (hε : ∀ v, IsFiniteTateMultiplier F S μ (χ F S ω) v (ε v)) :
    let ρ := sLocalExplicitTateFactor F S ω (sLocalTateEpsilonProduct F S ω ε)
    (∀ z : ℂ, 0 < z.re → z.re < 1 → ρ z ≠ 0 ∧ AnalyticAt ℂ (fun w ↦ (ρ w)⁻¹) z) ∧
    ∀ l r : ℝ, 0 < l → r < 1 →
      ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧ ∀ z : ℂ, z.re ∈ Icc l r →
        ‖(ρ z)⁻¹‖ ≤ C * (1 + |z.im|)^k := by
  intro ρ
  let P := sLocalTateEpsilonProduct F S ω ε
  have hP (z : ℂ) : AnalyticAt ℂ P z :=
    analyticAt_const.mul (Finset.analyticAt_fun_prod _ fun v _ ↦ (hε v).1 z trivial)
  have hn (z : ℂ) : P z ≠ 0 := by
    unfold P sLocalTateEpsilonProduct
    exact mul_ne_zero (mul_ne_zero
      (Finset.prod_ne_zero_iff.mpr fun _ _ ↦ pow_ne_zero _ (neg_ne_zero.mpr Complex.I_ne_zero))
      (Finset.prod_ne_zero_iff.mpr fun _ _ ↦ pow_ne_zero _ (neg_ne_zero.mpr Complex.I_ne_zero)))
      (Finset.prod_ne_zero_iff.mpr fun v _ ↦ (hε v).2.1 z)
  let Q (z : ℂ) := (P (1-z))⁻¹
  have hQ (z : ℂ) : AnalyticAt ℂ Q z :=
    (((hP (1-z)).comp (f := fun w : ℂ ↦ 1-w) (x := z)
      (analyticAt_const.sub analyticAt_id))).inv (hn _)
  have hreflect {l r : ℝ} {z : ℂ} (hz : z.re ∈ Icc l r) :
      (1-z).re ∈ Icc (1-r) (1-l) := by
    simp only [Complex.sub_re, Complex.one_re, mem_Icc]
    constructor <;> linarith [hz.1, hz.2]
  have hBound (l r : ℝ) : ∃ E : ℝ, 0 ≤ E ∧ ∀ z : ℂ, z.re ∈ Icc l r → ‖Q z‖ ≤ E := by
    obtain ⟨E,hE,h⟩ := inverseTateEpsilonProduct_norm_le_on_strip F S μ ω ε hε (1-r) (1-l)
    exact ⟨E,hE,fun z hz ↦ h (1-z) (hreflect hz)⟩
  have he (z : ℂ) : (ρ z)⁻¹ = sLocalExplicitTateFactor F S ω⁻¹ Q (1-z) := by
    change (P z * (sLocalEulerDenominator F S ω z)⁻¹ *
      sLocalEulerDenominator F S ω⁻¹ (1-z))⁻¹ = _
    unfold sLocalExplicitTateFactor sLocalEulerFactor Q
    simp only [sub_sub_cancel, mul_inv, inv_inv]
    ring
  refine ⟨fun z hz hr ↦ ?_, fun l r hl hr ↦ ?_⟩
  · have hp : 0 < (1-z).re := by simpa [Complex.sub_re, sub_pos] using hr
    have hρ : ρ z ≠ 0 := mul_ne_zero
      (mul_ne_zero (hn z) (inv_ne_zero (sLocalEulerDenominator_ne_zero_of_pos F S ω hz)))
      (sLocalEulerDenominator_ne_zero_of_pos F S ω⁻¹ hp)
    exact ⟨hρ, ((sLocalTateRatio_overlap_growth F S μ ω ε hε).1 z hz hr).inv hρ⟩
  · obtain ⟨C,k,hC,h⟩ := (tateRatio_overlap_growth F S ω⁻¹ Q hQ hBound).2
      (1-r) (1-l) (by linarith) (by linarith)
    refine ⟨C,k,hC,fun z hz ↦ ?_⟩
    rw [he]
    simpa only [Complex.sub_im, Complex.one_im, zero_sub, abs_neg] using h (1-z) (hreflect hz)


set_option maxHeartbeats 550000 in
omit [MeasurableSpace (AUnits F)] [BorelSpace (AUnits F)]
  [∀ v : S, BorelSpace (K F S v)ˣ] [∀ v : S, SigmaFinite (μ v)] in
private theorem eulerDenominator_norm_inv_conj (ω : Characters F S) (z : ℂ) :
    ‖sLocalEulerDenominator F S ω⁻¹ (conj z)‖ = ‖sLocalEulerDenominator F S ω z‖ := by
  unfold sLocalEulerDenominator archimedeanNumberFieldZetaDenominator sLocalFiniteZetaDenominator
  simp only [norm_mul, norm_prod]
  congr 1
  · congr 1
    · refine Finset.prod_congr rfl fun v _ ↦ ?_
      let p := a F S ω v
      have hc : conj p.1 = -p.1 := by
        apply Complex.ext <;> simp [p, sLocalRealArchParameters_re]
      have hi := sLocalRealArchParameters_inv F S ω v
      simp only [hi.1, hi.2, realArchZetaDenominator, norm_inv]
      rw [show conj z + -p.1 + ((p.2 % 2 : ℕ) : ℂ) =
          conj (z + p.1 + ((p.2 % 2 : ℕ) : ℂ)) by simp only [map_add, map_natCast,hc],
        gammaReal_norm_conj]
    · refine Finset.prod_congr rfl fun v _ ↦ ?_
      let p := b F S ω v
      have hc : conj p.1 = -p.1 := by
        apply Complex.ext <;> simp [p, sLocalComplexArchParameters_re]
      have hi := sLocalComplexArchParameters_inv F S ω v
      simp only [hi, Int.natAbs_neg, complexArchZetaDenominator, norm_inv]
      rw [show conj z + -p.1 + (p.2.natAbs : ℂ) / 2 =
          conj (z + p.1 + (p.2.natAbs : ℂ) / 2) by
          simp only [map_add,map_div₀,map_natCast,map_ofNat,hc], gammaComplex_norm_conj]
  · refine Finset.prod_congr rfl fun v _ ↦ ?_
    rw [sLocalFiniteZetaPhases_inv]
    have hχ (u : (K F S v)ˣ) : ((χ F S ω v)⁻¹) u = ((χ F S ω v) u)⁻¹ := rfl
    have he : finiteZetaUnramified F v.val (χ F S ω v)⁻¹ ↔
        finiteZetaUnramified F v.val (χ F S ω v) := by
      simp only [finiteZetaUnramified, hχ, inv_eq_one]
    rw [he]
    split_ifs
    · have hf : finiteZetaDenominator F v.val (χ F S ω v)⁻¹ (conj z) =
          conj (finiteZetaDenominator F v.val (χ F S ω v) z) := by
        simp only [finiteZetaDenominator, finiteZetaRatio, map_sub,map_one,map_mul,map_neg,
          Complex.conj_ofReal, ← Complex.exp_conj, hχ, Circle.coe_inv_eq_conj]
      rw [hf,Complex.norm_conj]
    · rfl

omit [MeasurableSpace (AUnits F)] [BorelSpace (AUnits F)] [∀ v : S, SigmaFinite (μ v)] in
/-- On the central line the actual Tate multiplier has unit modulus. -/
theorem sLocalTateRatio_norm_critical (ω : Characters F S)
    (ε : S → ℂ → ℂ) (hε : ∀ v, IsFiniteTateMultiplier F S μ (χ F S ω) v (ε v))
    (z : ℂ) (hz : z.re = 1/2) :
    ‖sLocalExplicitTateFactor F S ω (sLocalTateEpsilonProduct F S ω ε) z‖ = 1 := by
  have he : 1-z = conj z := by
    apply Complex.ext
    · simp only [Complex.sub_re,Complex.one_re,Complex.conj_re]
      linarith
    · simp [Complex.sub_im, Complex.conj_im]
  have hP : ‖sLocalTateEpsilonProduct F S ω ε z‖ = 1 := by
    simp only [sLocalTateEpsilonProduct, norm_mul, norm_prod, norm_pow, norm_neg, Complex.norm_I,
      one_pow, fun v : S ↦ (hε v).2.2.1 z hz, Finset.prod_const_one, mul_one]
  have hD : sLocalEulerDenominator F S ω z ≠ 0 :=
    sLocalEulerDenominator_ne_zero_of_pos F S ω (by linarith)
  unfold sLocalExplicitTateFactor sLocalEulerFactor
  rw [he,norm_mul,norm_mul,norm_inv,hP,one_mul,eulerDenominator_norm_inv_conj,
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr hD)]

set_option maxHeartbeats 1000000 in
omit [MeasurableSpace (AUnits F)] [BorelSpace (AUnits F)] [∀ v : S, SigmaFinite (μ v)] in
/-- For the actual S-local Tate matching equation, an entire extension
of the right component has rapid decay on every bounded strip. -/
theorem sLocalTate_entire_mem_schwartzBergman (ω : Characters F S)
    (ε : S → ℂ → ℂ) (hε : ∀ v, IsFiniteTateMultiplier F S μ (χ F S ω) v (ε v))
    (p : SchwartzBergman (Ioi (0 : ℝ)) × SchwartzBergman (Iio (1 : ℝ)))
    (hp : p ∈ sLocalBergmanGluing
      (sLocalExplicitTateFactor F S ω (sLocalTateEpsilonProduct F S ω ε)))
    (G : ℂ → ℂ) (hG : AnalyticOnNhd ℂ G univ) (hEq : EqOn G p.1.val {z | 0 < z.re}) :
    G ∈ schwartzBergmanSubmodule (univ : Set ℝ) := by
  let D := sLocalFiniteZetaDenominator F S (χ F S ω)
  let P := sLocalTateEpsilonProduct F S ω ε
  let ρ := sLocalExplicitTateFactor F S ω P
  have hP (z : ℂ) : AnalyticAt ℂ P z := by
    unfold P sLocalTateEpsilonProduct
    exact analyticAt_const.mul (Finset.analyticAt_fun_prod _ fun v _ ↦ (hε v).1 z trivial)
  have hρ := sLocalExplicitTateFactor_meromorphic F S ω P hP
  have hdiff : Differentiable ℂ G := fun z ↦ (hG z trivial).differentiableAt
  refine ⟨by simp, hdiff.differentiableOn, fun x y _ _ n ↦ ?_⟩
  let l := min x (-1)
  let r := max y 1
  let H (z : ℂ) := z ^ n * G z
  have hH : Differentiable ℂ H := (differentiable_id.pow n).mul hdiff
  have hl : l < 0 := (min_le_right _ _).trans_lt (by norm_num)
  have hr : (0 : ℝ) < r := zero_lt_one.trans_le (le_max_right _ _)
  obtain ⟨C, T, k, hC, hpol⟩ := sLocalTateRatio_finiteCleared_norm_le_on_strip F S μ ω ε hε
    (l - 1) (3/4) (by norm_num)
  obtain ⟨L, hL⟩ := p.2.property.2.2 (l - 1) (3/4) (by linarith)
    (fun z hz ↦ hz.2.trans_lt (by norm_num)) (n+k)
  obtain ⟨R, hR⟩ := p.1.property.2.2 (1/2) r
    (by have : (1 : ℝ) ≤ r := le_max_right _ _; linarith)
    (fun z hz ↦ (by norm_num : (0 : ℝ) < 1/2).trans_le hz.1) n
  let A := max ((C * (2 : ℝ)^k) * max L 0) ((2 : ℝ)^S.card * max R 0)
  have hleft (z : ℂ) (hz : z.re ∈ Icc (l - 1) (3/4)) (ht : max 1 T ≤ |z.im|) :
      ‖D z * (z ^ n * (ρ * p.2.val) z)‖ ≤ A := by
    have hnorm : (1 : ℝ) ≤ ‖z‖ := (le_max_left _ _).trans (ht.trans (Complex.abs_im_le_norm z))
    have hscale : 1 + |z.im| ≤ 2 * ‖z‖ := by linarith [Complex.abs_im_le_norm z]
    have hdec : ‖z ^ (n+k) * p.2.val z‖ ≤ max L 0 :=
      (hL (mem_image_of_mem _ hz)).trans (le_max_left _ _)
    have he : D z * (z^n * (ρ * p.2.val) z) = (D z * ρ z) * (z^n * p.2.val z) := by
      change D z * (z^n * (ρ z * p.2.val z)) = _
      ring
    rw [he, norm_mul]
    calc
      _ ≤ (C * (1 + |z.im|)^k) * ‖z^n * p.2.val z‖ :=
        mul_le_mul_of_nonneg_right (hpol z hz ((le_max_right _ _).trans ht)) (norm_nonneg _)
      _ ≤ (C * (2 * ‖z‖)^k) * ‖z^n * p.2.val z‖ := by gcongr
      _ = (C * (2 : ℝ)^k) * ‖z^(n+k) * p.2.val z‖ := by
        simp only [norm_mul, norm_pow, mul_pow, pow_add]
        ring
      _ ≤ A := (mul_le_mul_of_nonneg_left hdec (by positivity)).trans (le_max_left _ _)
  have hlarge (z : ℂ) (hz : z.re ∈ Icc l r) (ht : max 1 T < |z.im|) :
      ‖D z * H z‖ ≤ A := by
    by_cases h : z.re ≤ 1/2
    · have hDcont : Continuous D := continuous_iff_continuousAt.mpr fun w ↦
        (sLocalFiniteZetaDenominator_analytic F S (χ F S ω) w (mem_univ _)).continuousAt
      apply le_of_tendsto (x := 𝓝[≠] z)
        ((hDcont.mul hH.continuous).continuousAt.norm.tendsto.mono_left nhdsWithin_le_nhds)
      have hloc : ∀ᶠ w : ℂ in 𝓝 z, w.re ∈ Ioo (l - 1) (3/4) :=
        (isOpen_Ioo.preimage Complex.continuous_re).mem_nhds ⟨by linarith [hz.1], by linarith⟩
      have hhi : ∀ᶠ w : ℂ in 𝓝 z, max 1 T < |w.im| :=
        (isOpen_lt continuous_const Complex.continuous_im.abs).mem_nhds ht
      have hmatch := sLocalBergmanGluing_entire_eventuallyEq_left ρ hρ p hp G hG hEq z
        (by linarith)
      filter_upwards [hloc.filter_mono nhdsWithin_le_nhds, hhi.filter_mono nhdsWithin_le_nhds,
        hmatch] with w hw hwh he
      change ‖D w * (w^n * G w)‖ ≤ A
      rw [← he]
      exact hleft w (Ioo_subset_Icc_self hw) hwh.le
    · have hpos : 0 < z.re := by linarith
      have hz' : z.re ∈ Icc (1/2 : ℝ) r := ⟨le_of_not_ge h, hz.2⟩
      have hdec : ‖z^n * p.1.val z‖ ≤ max R 0 :=
        (hR (mem_image_of_mem _ hz')).trans (le_max_left _ _)
      rw [show H z = z^n * p.1.val z from congrArg (z^n * ·) (hEq hpos), norm_mul]
      exact (mul_le_mul (norm_sLocalFiniteZetaDenominator_le F S _ _ hpos) hdec
        (norm_nonneg _) (by positivity)).trans (le_max_right _ _)
  obtain ⟨M, hM⟩ := sLocal_entire_bounded_of_finiteCleared F S (χ F S ω) H hH hl hr hlarge
  exact ⟨M, by
    rintro _ ⟨z, hz, rfl⟩
    exact hM z ⟨(min_le_left _ _).trans hz.1, hz.2.trans (le_max_left _ _)⟩⟩

omit [MeasurableSpace (AUnits F)] [BorelSpace (AUnits F)]
  [∀ v : S, MeasurableSpace (K F S v)ˣ] [∀ v : S, BorelSpace (K F S v)ˣ] in
/-- The assembled meromorphic factor is the product of the three
families of local Euler ratios with their respective epsilon factors. -/
theorem sLocalTateFactor_eq_prod (ω : Characters F S) (ε : S → ℂ → ℂ) (z : ℂ) :
    sLocalExplicitTateFactor F S ω (sLocalTateEpsilonProduct F S ω ε) z =
      ((∏ v : R F, (-Complex.I) ^ ((a F S ω v).2 % 2) *
        (realArchZetaDenominator (a F S ω⁻¹ v).2 (1-z + (a F S ω⁻¹ v).1) /
          realArchZetaDenominator (a F S ω v).2 (z + (a F S ω v).1))) *
        ∏ v : C F, (-Complex.I) ^ (b F S ω v).2.natAbs *
          (complexArchZetaDenominator (b F S ω⁻¹ v).2 (1-z + (b F S ω⁻¹ v).1) /
            complexArchZetaDenominator (b F S ω v).2 (z + (b F S ω v).1))) *
        ∏ v : S, ε v z *
          ((if finiteZetaUnramified F v.val (χ F S ω⁻¹ v)
            then finiteZetaDenominator F v.val (χ F S ω⁻¹ v) (1-z) else 1) /
            (if finiteZetaUnramified F v.val (χ F S ω v)
            then finiteZetaDenominator F v.val (χ F S ω v) z else 1)) := by
  simp only [sLocalExplicitTateFactor, sLocalTateEpsilonProduct, sLocalEulerFactor,
    sLocalEulerDenominator, archimedeanNumberFieldZetaDenominator, sLocalFiniteZetaDenominator,
    div_eq_mul_inv, mul_inv, Finset.prod_inv_distrib, Finset.prod_mul_distrib]
  ring

/-- The local product gives the normalized functional equation on the
entire S-local test space, including coupled Schwartz tests. -/
theorem exists_sLocalTateProduct_fourier (ω : Characters F S) :
    ∃ ε : S → ℂ → ℂ,
      (∀ v, IsFiniteTateMultiplier F S μ (χ F S ω) v (ε v)) ∧
      let P := sLocalTateEpsilonProduct F S ω ε
      AnalyticOnNhd ℂ P univ ∧ (∀ z, P z ≠ 0) ∧
        (∀ z : ℂ, z.re = 1/2 → ‖P z‖ = 1) ∧
        ∀ (p : E F S) (z : ℂ), N F S μ ω p z =
          P z * N F S μ ω⁻¹ (sLocalSelectedFourier F S p) (1-z) := by
  obtain ⟨ε, hε, hpure⟩ := exists_sLocalTateProduct_separated F S μ ω
  obtain ⟨e, he, _, _, hAll, _, _⟩ := exists_sLocalMellin_fourier_functionalEquation F S μ ω
  obtain ⟨φ, f, g, h, c, hc, hφ, hconst⟩ :=
    exists_sLocalEulerNormalizedMellin_separated_constant F S μ ω
  let p := sLocalBruhatPure F S φ (locallyConstantTestPiProduct h)
  let A : ℂ := (∏ v : R F, (-Complex.I) ^ ((a F S ω v).2 % 2)) *
    ∏ v : C F, (-Complex.I) ^ (b F S ω v).2.natAbs
  let P (z : ℂ) := A * ∏ v : S, ε v z
  have hP : AnalyticOnNhd ℂ P univ := analyticOnNhd_const.mul
    (Finset.analyticOnNhd_fun_prod _ (fun v _ ↦ (hε v).1))
  have hAn : A ≠ 0 := mul_ne_zero
    (Finset.prod_ne_zero_iff.mpr fun _ _ ↦ pow_ne_zero _ (neg_ne_zero.mpr Complex.I_ne_zero))
    (Finset.prod_ne_zero_iff.mpr fun _ _ ↦ pow_ne_zero _ (neg_ne_zero.mpr Complex.I_ne_zero))
  have hPn (z : ℂ) : P z ≠ 0 :=
    mul_ne_zero hAn (Finset.prod_ne_zero_iff.mpr fun v _ ↦ (hε v).2.1 z)
  have hunit (z : ℂ) (hz : z.re = 1/2) : ‖P z‖ = 1 := by
    simp only [P, A, norm_mul, norm_prod, norm_pow, norm_neg, Complex.norm_I, one_pow,
      fun v : S ↦ (hε v).2.2.1 z hz, Finset.prod_const_one, mul_one]
  have hEq : e = P := by
    let U := {z : ℂ | 0 < z.re ∧ z.re < 1}
    have hU : IsOpen U := (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
    have hU₀ : (1 / 2 : ℂ) ∈ U := by
      change 0 < (1 / 2 : ℂ).re ∧ (1 / 2 : ℂ).re < 1
      norm_num [Complex.div_ofNat_re]
    apply he.eq_of_eventuallyEq hP (z₀ := (1 / 2 : ℂ))
    filter_upwards [hU.mem_nhds hU₀] with z hz
    have h1 : N F S μ ω p z =
        e z * N F S μ ω⁻¹ (sLocalSelectedFourier F S p) (1-z) := hAll p z
    have h2 : N F S μ ω p z =
        P z * N F S μ ω⁻¹ (sLocalSelectedFourier F S p) (1-z) :=
      hpure φ f g hφ h z hz.1 hz.2
    have hn : N F S μ ω⁻¹ (sLocalSelectedFourier F S p) (1-z) ≠ 0 := by
      intro hn
      apply hc
      rw [hn, mul_zero] at h1
      exact (congrFun hconst z).symm.trans h1
    exact mul_right_cancel₀ hn (h1.symm.trans h2)
  refine ⟨ε, hε, hP, hPn, hunit, ?_⟩
  intro p z
  exact (hAll p z).trans (congrArg (fun m : ℂ → ℂ ↦
    m z * N F S μ ω⁻¹ (sLocalSelectedFourier F S p) (1-z)) hEq)

attribute [local instance] sLocalZetaUnfolding_classMeasurable sLocalZetaUnfolding_classBorel

/-- The entire normalized multipliers of the two dual components are reciprocal.
Two Fourier transforms act on theta by a positive scalar, and the midpoint
unit-modulus identities identify that scalar as one. -/
theorem sLocalTateEpsilon_dual (ω : Characters F S) (P Q : ℂ → ℂ)
    (hP : AnalyticOnNhd ℂ P univ) (hQ : AnalyticOnNhd ℂ Q univ)
    (hPu : ∀ z : ℂ, z.re = 1/2 → ‖P z‖ = 1)
    (hQu : ∀ z : ℂ, z.re = 1/2 → ‖Q z‖ = 1)
    (hp : ∀ (f : E F S) z, N F S μ ω f z =
      P z * N F S μ ω⁻¹ (sLocalSelectedFourier F S f) (1-z))
    (hq : ∀ (f : E F S) z, N F S μ ω⁻¹ f z =
      Q z * N F S μ ω (sLocalSelectedFourier F S f) (1-z)) :
    ∀ z : ℂ, P z * Q (1-z) = 1 := by
  letI : (ν F S μ).IsHaarMeasure :=
    sLocalZetaProductMeasure_isHaar F S μ (archimedeanMultiplicativeHaar F)
  obtain ⟨m, hm, hweil⟩ := sLocalClassHaar_exists_weil F S (ν F S μ)
  letI := hm
  let a := ideleNorm F (sLocalCodifferentTailIdele F S)
  let d := (sLocalFourierTailVolume F S).toReal
  have ha : 0 < a := ideleNorm_pos F _
  have hd : 0 < d := sLocalFourierTailVolume_pos F S
  let t := d⁻¹ * d⁻¹ * a⁻¹
  have ht : 0 < t := by dsimp [t]; positivity
  let T := sLocalSelectedFourier F S
  let C := sLocalFourierCompression F S
  let θ := sLocalThetaOperator F S
  have hθ (f : E F S) : θ (T (T f)) = (t : ℂ) • θ f := by
    have he : θ (C (C f)) = ((a : ℂ)⁻¹) • θ f := by
      have hC : (a : ℂ) • θ (C (C f)) = θ f := sLocalFourierCompression_double_theta F S f
      have h := congrArg (((a : ℂ)⁻¹) • ·) hC
      have han : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
      simpa only [smul_smul, inv_mul_cancel₀ han, one_smul] using h
    change θ ((d : ℂ)⁻¹ • C ((d : ℂ)⁻¹ • C f)) = _
    rw [map_smul C, smul_smul, map_smul θ, he, smul_smul]
    simp only [t, Complex.ofReal_mul, Complex.ofReal_inv]
  have hN (f : E F S) (z : ℂ) (hz : 0 < z.re) :
      N F S μ ω (T (T f)) z = (t : ℂ) * N F S μ ω f z := by
    have h₁ := normalizedMellin_eq_mul_idelic F S μ ω (T (T f)) z hz
    have h₂ := normalizedMellin_eq_mul_idelic F S μ ω f z hz
    change N F S μ ω (T (T f)) z = _ at h₁
    change N F S μ ω f z = _ at h₂
    rw [h₁, h₂,
      (sLocalIdelicZeta_integrable_eq_theta F S (ν F S μ) m hweil ω (T (T f)) z hz).2,
      (sLocalIdelicZeta_integrable_eq_theta F S (ν F S μ) m hweil ω f z hz).2]
    have he (q : SIdeleQuotient F S) :
        sLocalZetaWeight F S ω z q * θ (T (T f)) q =
          (t : ℂ) * (sLocalZetaWeight F S ω z q * θ f q) := by
      rw [hθ f]
      change _ * ((t : ℂ) * _) = _
      ring
    unfold sLocalThetaZetaIntegral
    change sLocalEulerDenominator F S ω z *
        (∫ q, sLocalZetaWeight F S ω z q * θ (T (T f)) q ∂sLocalClassHaar F S m) =
      (t : ℂ) * (sLocalEulerDenominator F S ω z *
        ∫ q, sLocalZetaWeight F S ω z q * θ f q ∂sLocalClassHaar F S m)
    simp_rw [he, integral_const_mul]
    ring
  obtain ⟨f,B,hB,hconst⟩ := exists_sLocalEulerNormalizedMellin_constant F S μ ω
  have hEq (z : ℂ) (hz : 0 < z.re) : P z * Q (1-z) * (t : ℂ) = 1 := by
    have h1 := hp f z
    have h2 := hq (T f) (1-z)
    change N F S μ ω f z = P z * N F S μ ω⁻¹ (T f) (1-z) at h1
    rw [sub_sub_cancel] at h2
    have hBz : N F S μ ω f z = B := congrFun hconst z
    rw [h2, hN f z hz, hBz] at h1
    exact mul_right_cancel₀ hB (by simpa only [one_mul, mul_assoc] using h1.symm)
  have hs : ((1/2 : ℂ)).re = 1/2 := by norm_num [Complex.div_ofNat_re]
  have hsu : (1-(1/2 : ℂ)).re = 1/2 := by rw [Complex.sub_re, Complex.one_re, hs]; ring
  have hmid := congrArg norm (hEq (1/2) (by norm_num [Complex.div_ofNat_re]))
  rw [norm_mul, norm_mul, hPu _ hs, hQu _ hsu, one_mul, one_mul, norm_one,
    Complex.norm_real, Real.norm_of_nonneg ht.le] at hmid
  have hRight (z : ℂ) (hz : 0 < z.re) : P z * Q (1-z) = 1 := by
    simpa [hmid] using hEq z hz
  have hprod : AnalyticOnNhd ℂ (fun z ↦ P z * Q (1-z)) univ := fun z _ ↦
    (hP z trivial).mul ((hQ (1-z) trivial).comp (analyticAt_const.sub analyticAt_id))
  have he := hprod.eq_of_eventuallyEq analyticOnNhd_const (z₀ := (1 : ℂ)) (by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show 0 < (1 : ℂ).re by simp)] with z hz using hRight z hz)
  exact fun z ↦ congrFun he z

omit [MeasurableSpace (AUnits F)] [BorelSpace (AUnits F)]
  [∀ v : S, BorelSpace (K F S v)ˣ] in
private theorem sLocalTateEuler_eventually_nonzero (ω : Characters F S) (c : ℂ) :
    ∀ᶠ z in 𝓝[≠] c, sLocalEulerDenominator F S ω z ≠ 0 := by
  let D := sLocalEulerDenominator F S ω
  have hD : AnalyticOnNhd ℂ D univ := fun z _ ↦ sLocalEulerDenominator_analytic F S ω z
  rcases (hD c trivial).eventually_eq_zero_or_eventually_ne_zero with hz | hz
  · have he := hD.eq_of_eventuallyEq analyticOnNhd_const (z₀ := c) hz
    exact False.elim (sLocalEulerDenominator_ne_zero_of_pos F S ω
      (show 0 < (1 : ℂ).re by simp) (congrFun he 1))
  · exact hz

private theorem meromorphic_conj_precompose_conj {f : ℂ → ℂ} (hf : Meromorphic f) :
    Meromorphic (fun z ↦ conj (f (conj z))) := by
  intro z
  obtain ⟨n, hn⟩ := hf (conj z)
  refine ⟨n, ?_⟩
  let G (w : ℂ) := (w - conj z)^n * f w
  have hg : AnalyticAt ℂ G (conj z) := hn
  have he : AnalyticAt ℂ (fun w ↦ conj (G (conj w))) z := by
    apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
    filter_upwards [Complex.continuous_conj.continuousAt
      (Complex.analyticAt_iff_eventually_differentiableAt.mp hg)] with w hw
    exact differentiableAt_conj_conj_iff.mpr hw
  simpa only [G, map_mul, map_pow, map_sub, starRingEnd_self_apply, smul_eq_mul] using he

private theorem meromorphic_germ_eq_of_one_germ {f g : ℂ → ℂ} (hf : Meromorphic f)
    (hg : Meromorphic g) {c : ℂ} (he : f =ᶠ[𝓝[≠] c] g) (z : ℂ) :
    f =ᶠ[𝓝[≠] z] g := by
  have hzero : (f - g) =ᶠ[𝓝[≠] c] 0 := he.mono fun w hw ↦ sub_eq_zero.mpr hw
  have ho := (hf.sub hg).meromorphicOn (s := (univ : Set ℂ))
  have ht : meromorphicOrderAt (f - g) z = ⊤ := by
    by_contra hn
    exact ho.meromorphicOrderAt_ne_top_of_isPreconnected isPreconnected_univ (mem_univ z)
      (mem_univ c) hn (meromorphicOrderAt_eq_top_iff.mpr hzero)
  exact (meromorphicOrderAt_eq_top_iff.mp ht).mono fun w hw ↦ sub_eq_zero.mp hw

omit [∀ v : S, SigmaFinite (μ v)] in
/-- Duality and conjugation for the actual S-local factors, as identities
of meromorphic germs. The S-unit minus one has trivial class. -/
theorem sLocalTateRatio_dual_conj (ω : Characters F S)
    (ε ε' : S → ℂ → ℂ)
    (hε : ∀ v, IsFiniteTateMultiplier F S μ (χ F S ω) v (ε v))
    (hε' : ∀ v, IsFiniteTateMultiplier F S μ (χ F S ω⁻¹) v (ε' v))
    (hdual : ∀ z : ℂ, sLocalTateEpsilonProduct F S ω ε z *
      sLocalTateEpsilonProduct F S ω⁻¹ ε' (1-z) = 1) :
    let ρ := sLocalExplicitTateFactor F S ω (sLocalTateEpsilonProduct F S ω ε)
    let ρ' := sLocalExplicitTateFactor F S ω⁻¹ (sLocalTateEpsilonProduct F S ω⁻¹ ε')
    (∀ c : ℂ, (fun z ↦ ρ z * ρ' (1-z)) =ᶠ[𝓝[≠] c] fun _ ↦ 1) ∧
    (∀ c : ℂ, (fun z ↦ conj (ρ' (conj z))) =ᶠ[𝓝[≠] c] ρ) := by
  intro ρ ρ'
  let D := sLocalEulerDenominator F S
  let P := sLocalTateEpsilonProduct F S ω ε
  let P' := sLocalTateEpsilonProduct F S ω⁻¹ ε'
  have hP (z : ℂ) : AnalyticAt ℂ P z :=
    analyticAt_const.mul (Finset.analyticAt_fun_prod _ fun v _ ↦ (hε v).1 z trivial)
  have hP' (z : ℂ) : AnalyticAt ℂ P' z :=
    analyticAt_const.mul (Finset.analyticAt_fun_prod _ fun v _ ↦ (hε' v).1 z trivial)
  have hrefl (z : ℂ) (h₁ : D ω z ≠ 0) (h₂ : D ω⁻¹ (1-z) ≠ 0) :
      ρ z * ρ' (1-z) = 1 := by
    change (P z * (D ω z)⁻¹ * D ω⁻¹ (1-z)) *
      (P' (1-z) * (D ω⁻¹ (1-z))⁻¹ * D (ω⁻¹)⁻¹ (1-(1-z))) = 1
    rw [inv_inv, sub_sub_cancel]
    calc
      _ = (P z * P' (1-z)) * ((D ω z)⁻¹ * D ω z) *
          ((D ω⁻¹ (1-z))⁻¹ * D ω⁻¹ (1-z)) := by ring
      _ = _ := by rw [hdual, inv_mul_cancel₀ h₁, inv_mul_cancel₀ h₂, mul_one, mul_one]
  constructor
  · intro c
    let f (z : ℂ) := D ω⁻¹ (1-z)
    have hf : AnalyticOnNhd ℂ f univ := fun z _ ↦
      (sLocalEulerDenominator_analytic F S ω⁻¹ (1-z)).comp (analyticAt_const.sub analyticAt_id)
    have hn : ∀ᶠ z in 𝓝[≠] c, f z ≠ 0 := by
      rcases (hf c trivial).eventually_eq_zero_or_eventually_ne_zero with h | h
      · have he := hf.eq_of_eventuallyEq analyticOnNhd_const (z₀ := c) h
        exact False.elim (sLocalEulerDenominator_ne_zero_of_pos F S ω⁻¹
          (show 0 < (1-(0 : ℂ)).re by simp) (congrFun he 0))
      · exact h
    filter_upwards [sLocalTateEuler_eventually_nonzero F S ω c, hn]
      with z hz hw using hrefl z hz hw
  · let g (z : ℂ) := conj (ρ' (conj z))
    have hρ := sLocalExplicitTateFactor_meromorphic F S ω P hP
    have hρ' := sLocalExplicitTateFactor_meromorphic F S ω⁻¹ P' hP'
    have hg := meromorphic_conj_precompose_conj hρ'
    have hline (z : ℂ) (hz : z.re = 1/2) : g z = ρ z := by
      have he : 1-z = conj z := by
        apply Complex.ext
        · norm_num [Complex.sub_re, hz]
        · simp [Complex.sub_im]
      have h := hrefl z
        (sLocalEulerDenominator_ne_zero_of_pos F S ω (by rw [hz]; norm_num))
        (sLocalEulerDenominator_ne_zero_of_pos F S ω⁻¹ (by rw [he, Complex.conj_re, hz]; norm_num))
      have hn : ‖ρ z‖ = 1 := sLocalTateRatio_norm_critical F S μ ω ε hε z hz
      have hunit : ρ z * conj (ρ z) = 1 := by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hn]
        norm_num
      have hs : ρ' (conj z) = conj (ρ z) :=
        mul_left_cancel₀ (norm_ne_zero_iff.mp (by rw [hn]; norm_num)) ((he ▸ h).trans hunit.symm)
      dsimp [g]
      rw [hs, starRingEnd_self_apply]
    let b : ℂ := 1/2
    let s (x : ℝ) := b + (x : ℂ) * Complex.I
    have hb : b.re = 1/2 := by norm_num [b, Complex.div_ofNat_re]
    have H : Tendsto s (𝓝[≠] (0 : ℝ)) (𝓝[≠] b) := by
      apply tendsto_nhdsWithin_iff.mpr
      have hc : Continuous s := by fun_prop
      have h0 : s 0 = b := by simp [s]
      refine ⟨h0 ▸ hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds, ?_⟩
      filter_upwards [self_mem_nhdsWithin (s := ({0} : Set ℝ)ᶜ) (a := (0 : ℝ))] with x hx
      intro hx'
      have he := congrArg Complex.im (Set.mem_singleton_iff.mp hx')
      apply hx
      exact Set.mem_singleton_iff.mpr (by simpa [s, Complex.mul_im] using he)
    have hfreq : ∃ᶠ z in 𝓝[≠] b, g z = ρ z := H.frequently
      ((Eventually.of_forall fun x : ℝ ↦ hline (s x) (by simp [s, hb, Complex.mul_re])).frequently)
    have hA (z : ℂ) (hz : 0 < z.re) : AnalyticAt ℂ ρ z := by
      refine ((hP z).mul ((sLocalEulerDenominator_analytic F S ω z).inv
        (sLocalEulerDenominator_ne_zero_of_pos F S ω hz))).mul ?_
      exact (sLocalEulerDenominator_analytic F S ω⁻¹ (1-z)).comp
        (analyticAt_const.sub analyticAt_id)
    have hB (z : ℂ) (hz : 0 < z.re) : AnalyticAt ℂ ρ' z := by
      refine ((hP' z).mul ((sLocalEulerDenominator_analytic F S ω⁻¹ z).inv
        (sLocalEulerDenominator_ne_zero_of_pos F S ω⁻¹ hz))).mul ?_
      exact (sLocalEulerDenominator_analytic F S (ω⁻¹)⁻¹ (1-z)).comp
        (analyticAt_const.sub analyticAt_id)
    have hgb : AnalyticAt ℂ g b := by
      apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
      have hbr : 0 < (conj b).re := by rw [Complex.conj_re, hb]; norm_num
      filter_upwards [Complex.continuous_conj.continuousAt
        (Complex.analyticAt_iff_eventually_differentiableAt.mp (hB _ hbr))] with w hw
      exact differentiableAt_conj_conj_iff.mpr hw
    have he := (hgb.frequently_eq_iff_eventually_eq (hA b (by rw [hb]; norm_num))).mp hfreq
    exact fun c ↦ meromorphic_germ_eq_of_one_germ hg hρ
      (he.filter_mono nhdsWithin_le_nhds) c

/-- Corrected Proposition 3.3.1.5 for the S-local quasi-character charts.
The exponent counts a real place once and a complex place twice. -/
theorem exists_sLocalTateRatio_asymptoticBehavior (ω : Characters F S) :
    ∃ ε ε' : S → ℂ → ℂ,
      (∀ v, IsFiniteTateMultiplier F S μ (χ F S ω) v (ε v)) ∧
      (∀ v, IsFiniteTateMultiplier F S μ (χ F S ω⁻¹) v (ε' v)) ∧
      let ρ := sLocalExplicitTateFactor F S ω (sLocalTateEpsilonProduct F S ω ε)
      let ρ' := sLocalExplicitTateFactor F S ω⁻¹ (sLocalTateEpsilonProduct F S ω⁻¹ ε')
      Meromorphic ρ ∧ Meromorphic ρ' ∧
      (∀ c : ℂ, (fun z ↦ ρ z * ρ' (1-z)) =ᶠ[𝓝[≠] c] fun _ ↦ 1) ∧
      (∀ c : ℂ, (fun z ↦ conj (ρ' (conj z))) =ᶠ[𝓝[≠] c] ρ) ∧
      (∀ z : ℂ, z.re = 1/2 → AnalyticAt ℂ ρ z ∧ ‖ρ z‖ = 1) ∧
      ∀ k : ℕ, (∀ z : ℂ, 0 < z.re → AnalyticAt ℂ (iteratedDeriv k ρ) z) ∧
        ∀ l r : ℝ, 0 < l → ∃ C T : ℝ, 0 ≤ C ∧
          ∀ z : ℂ, z.re ∈ Icc l r → T ≤ |z.im| →
            ‖iteratedDeriv k ρ z‖ ≤ C *
              (1 + |z.im|) ^ ((Module.finrank ℚ F : ℝ) * (z.re - 1/2)) *
                Real.log (1 + |z.im|) ^ k := by
  obtain ⟨ε,hε,hP,_,hPn,hEq⟩ := exists_sLocalTateProduct_fourier F S μ ω
  obtain ⟨ε',hε',hQ,_,hQn,hEq'⟩ := exists_sLocalTateProduct_fourier F S μ ω⁻¹
  have hEq'' (f : E F S) (z : ℂ) : N F S μ ω⁻¹ f z =
      sLocalTateEpsilonProduct F S ω⁻¹ ε' z * N F S μ ω (sLocalSelectedFourier F S f) (1-z) := by
    simpa only [inv_inv] using hEq' f z
  have hdual := sLocalTateEpsilon_dual F S μ ω _ _ hP hQ hPn hQn hEq hEq''
  obtain ⟨hreflect,hconj⟩ := sLocalTateRatio_dual_conj F S μ ω ε ε' hε hε' hdual
  have hderiv k := sLocalTateRatio_iteratedDeriv_sharp F S μ ω ε hε k
  refine ⟨ε,ε',hε,hε',
    sLocalExplicitTateFactor_meromorphic F S ω _ (fun z ↦ hP z trivial),
    sLocalExplicitTateFactor_meromorphic F S ω⁻¹ _ (fun z ↦ hQ z trivial),
    hreflect,hconj,fun z hz ↦ ⟨?_,sLocalTateRatio_norm_critical F S μ ω ε hε z hz⟩,hderiv⟩
  simpa only [iteratedDeriv_zero] using (hderiv 0).1 z (by rw [hz]; norm_num)

private abbrev continuedZeta (ω : Characters F S) (f : E F S) :=
  sLocalProductZetaContinued F S μ ω (a F S ω) (b F S ω) f

/-- The local product of Tate multipliers gives the actual S-local
functional equation, with its exact negative divisor and the pole bound
for every continued test integral. -/
theorem exists_sLocalTateProduct_functionalEquation (ω : Characters F S) :
    ∃ ε : S → ℂ → ℂ,
      (∀ v, IsFiniteTateMultiplier F S μ (χ F S ω) v (ε v)) ∧
      let P := sLocalTateEpsilonProduct F S ω ε
      let ρ := sLocalExplicitTateFactor F S ω P
      AnalyticOnNhd ℂ P univ ∧ (∀ z, P z ≠ 0) ∧ (∀ z : ℂ, z.re = 1/2 → ‖P z‖ = 1) ∧
      Meromorphic ρ ∧
      (∀ (f : E F S) (z : ℂ), 0 < z.re → z.re < 1 →
        sLocalIdelicZetaIntegral F S (ν F S μ) ω f z =
          ρ z * sLocalIdelicZetaIntegral F S (ν F S μ) ω⁻¹ (sLocalSelectedFourier F S f) (1-z)) ∧
      (∀ (f : E F S), Meromorphic (continuedZeta F S μ ω f) ∧
        EqOn (continuedZeta F S μ ω f) (sLocalIdelicZetaIntegral F S (ν F S μ) ω f)
          {z | 0 < z.re}) ∧
      (∀ (f : E F S) (c : ℂ), continuedZeta F S μ ω f =ᶠ[𝓝[≠] c] fun z ↦
        ρ z * continuedZeta F S μ ω⁻¹ (sLocalSelectedFourier F S f) (1-z)) ∧
      (∀ (f : E F S) (c : ℂ),
        min (meromorphicOrderAt ρ c) 0 ≤ meromorphicOrderAt (continuedZeta F S μ ω f) c) := by
  obtain ⟨ε, hε, hP, hPn, hunit, hNorm⟩ := exists_sLocalTateProduct_fourier F S μ ω
  obtain ⟨e, _, _, hstrip, hAll, hGerm, hPole⟩ := exists_sLocalMellin_fourier_functionalEquation F S μ ω
  obtain ⟨p, C, hC, hp⟩ := exists_sLocalEulerNormalizedMellin_constant F S μ ω
  let P := sLocalTateEpsilonProduct F S ω ε
  have he : e = P := by
    funext z
    have h1 : N F S μ ω p z =
        e z * N F S μ ω⁻¹ (sLocalSelectedFourier F S p) (1-z) := hAll p z
    have h2 : N F S μ ω p z =
        P z * N F S μ ω⁻¹ (sLocalSelectedFourier F S p) (1-z) := hNorm p z
    have hn : N F S μ ω⁻¹ (sLocalSelectedFourier F S p) (1-z) ≠ 0 := by
      intro hn
      apply hC
      rw [hn, mul_zero] at h1
      exact (congrFun hp z).symm.trans h1
    exact mul_right_cancel₀ hn (h1.symm.trans h2)
  subst e
  exact ⟨ε, hε, hP, hPn, hunit, sLocalExplicitTateFactor_meromorphic F S ω P
    (fun z ↦ hP z trivial), hstrip, sLocalIdelicZeta_meromorphic_continuation F S μ ω,
    hGerm, hPole⟩

section PolarFree

attribute [local instance] sLocalZetaUnfolding_classMeasurable sLocalZetaUnfolding_classBorel

variable [MeasurableSpace (InfiniteAdeleRing F)] [BorelSpace (InfiniteAdeleRing F)]

/-- At the canonical norm section, every polar-free Tate matching pair
comes from a flat test, and the resulting paired image is closed. -/
theorem exists_sLocalTate_polarFreePaired_range
    (m : Measure (SLocalThetaNormOne F S)) [m.IsHaarMeasure]
    (hm : IsWeilQuotientMeasure (sUnitImage F S) (ν F S μ) Measure.count
      (sLocalClassHaar F S m)) (ω : Characters F S) :
    ∃ ε : S → ℂ → ℂ, (∀ v, IsFiniteTateMultiplier F S μ (χ F S ω) v (ε v)) ∧
      (∀ (f : E F S) (z : ℂ), N F S μ ω f z =
        sLocalTateEpsilonProduct F S ω ε z * N F S μ ω⁻¹ (sLocalSelectedFourier F S f) (1-z)) ∧
      let ρ := sLocalExplicitTateFactor F S ω (sLocalTateEpsilonProduct F S ω ε)
      let W := {p : SchwartzBergman (Ioi (0 : ℝ)) × SchwartzBergman (Iio (1 : ℝ)) |
        p ∈ sLocalBergmanGluing ρ ∧
          ∀ s : ℂ, s.re < 1 → 0 ≤ meromorphicOrderAt (ρ * p.2.val) s}
      IsClosed W ∧
        range (fun g : sLocalPolarFreeTestSubspace F S ↦
          sLocalPairedBergmanMellin F S m ω (Submodule.Quotient.mk g.val)) = W := by
  obtain ⟨ε, hε, hP, _, _, hnormalized⟩ := exists_sLocalTateProduct_fourier F S μ ω
  obtain ⟨e, _, _, heq, hclosed, hrange, hext⟩ :=
    exists_sLocalPairedBergmanMellin_polarFree_range F S μ m hm ω
  obtain ⟨f, C, hC, hf⟩ := exists_sLocalEulerNormalizedMellin_constant F S μ ω
  let P := sLocalTateEpsilonProduct F S ω ε
  have he : e = P := by
    funext z
    have h₁ : N F S μ ω f z = e z * N F S μ ω⁻¹ (sLocalSelectedFourier F S f) (1-z) :=
      heq f z
    have h₂ : N F S μ ω f z = P z * N F S μ ω⁻¹ (sLocalSelectedFourier F S f) (1-z) :=
      hnormalized f z
    have hne : N F S μ ω⁻¹ (sLocalSelectedFourier F S f) (1-z) ≠ 0 := by
      intro h
      rw [h, mul_zero] at h₁
      exact hC ((congrFun hf z).symm.trans h₁)
    exact mul_right_cancel₀ hne (h₁.symm.trans h₂)
  subst e
  refine ⟨ε, hε, hnormalized, hclosed, ?_⟩
  exact le_antisymm (fun _ h ↦ (hrange ▸ h).2) fun p hp ↦ by
    let ρ := sLocalExplicitTateFactor F S ω P
    have hρ := sLocalExplicitTateFactor_meromorphic F S ω P (fun z ↦ hP z trivial)
    obtain ⟨G, hG, hEq⟩ := (sLocalBergmanGluing_entire_iff ρ hρ p hp.1).mp hp.2
    have hb := sLocalTate_entire_mem_schwartzBergman F S μ ω ε hε p hp.1 G hG hEq
    rw [hext]
    exact ⟨hp.1, ⟨G, hb⟩, hEq⟩

variable (m : Measure (SLocalThetaNormOne F S)) [m.IsHaarMeasure] (ω : Characters F S)

private abbrev Flat := sLocalPolarFreeTestSubspace F S
private abbrev ThetaKernel := sLocalHomogeneousThetaKernel F S m ω
private abbrev PairedBergman := SchwartzBergman (Ioi (0 : ℝ)) × SchwartzBergman (Iio (1 : ℝ))
private abbrev EntireBergman := SchwartzBergman (univ : Set ℝ)

section SubmoduleQuotient

variable {X : Type*} [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
  (P M : Submodule ℂ X)

set_option backward.isDefEq.respectTransparency false in
local instance submoduleHasQuotient : HasQuotient P (Submodule ℂ P) := by
  exact @Submodule.hasQuotient ℂ P _ P.addCommGroup P.module

private abbrev RestrictedQuotient := P ⧸ M.comap P.subtype

private def restrictedQuotientMk : P →L[ℂ] RestrictedQuotient P M :=
  (M.comap P.subtype).mkQL

private theorem restrictedQuotientMk_surjective : Surjective (restrictedQuotientMk P M) :=
  (M.comap P.subtype).mkQ_surjective

set_option backward.isDefEq.respectTransparency false in
private def restrictedQuotientInclusion : RestrictedQuotient P M →L[ℂ] (X ⧸ M) := by
  let J := M.comap P.subtype
  let B : P →L[ℂ] (X ⧸ M) := M.mkQL.comp P.subtypeL
  have h : J ≤ B.ker := by
    intro g hg
    change M.mkQ g.val = 0
    exact (Submodule.Quotient.mk_eq_zero M).mpr hg
  exact J.liftQL B h

private theorem restrictedQuotientInclusion_injective :
    Injective (restrictedQuotientInclusion P M) := by
  apply LinearMap.ker_eq_bot.mp
  rw [Submodule.eq_bot_iff]
  intro q hq
  obtain ⟨g, rfl⟩ := (M.comap P.subtype).mkQ_surjective q
  change Submodule.Quotient.mk (p := M) g.val = 0 at hq
  exact (Submodule.Quotient.mk_eq_zero _).mpr ((Submodule.Quotient.mk_eq_zero M).mp hq)

end SubmoduleQuotient

/-- The actual flat theta quotient, with the quotient topology from the
flat test space and the restricted homogeneous theta kernel. -/
abbrev SLocalPolarFreeThetaQuotient :=
  RestrictedQuotient (Flat F S) (ThetaKernel F S m ω)

/-- The canonical injection from the flat theta quotient into the ordinary
homogeneous theta quotient. -/
def sLocalPolarFreeThetaInclusion :
    SLocalPolarFreeThetaQuotient F S m ω →L[ℂ] SLocalHomogeneousThetaQuotient F S m ω :=
  restrictedQuotientInclusion (Flat F S) (ThetaKernel F S m ω)

omit [MeasurableSpace (AUnits F)] [BorelSpace (AUnits F)]
  [∀ v : S, MeasurableSpace (K F S v)ˣ] [∀ v : S, BorelSpace (K F S v)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)]
  [BorelSpace (InfiniteAdeleRing F)] in
theorem sLocalPolarFreeThetaInclusion_injective :
    Injective (sLocalPolarFreeThetaInclusion F S m ω) :=
  restrictedQuotientInclusion_injective (Flat F S) (ThetaKernel F S m ω)

/-- The ambient paired Schwartz–Bergman space is Fréchet. -/
theorem sLocalPairedBergman_frechet : IsFrechetTVS PairedBergman := by
  obtain ⟨ha, hp, hm, hc⟩ :=
    schwartzBergman_frechet (Ioi (0 : ℝ)) isOpen_Ioi ordConnected_Ioi nonempty_Ioi
  obtain ⟨ha', hp', hm', hc'⟩ :=
    schwartzBergman_frechet (Iio (1 : ℝ)) isOpen_Iio ordConnected_Iio nonempty_Iio
  letI : MetrizableSpace (SchwartzBergman (Ioi (0 : ℝ))) := hm
  letI : MetrizableSpace (SchwartzBergman (Iio (1 : ℝ))) := hm'
  letI : CompleteSpace (SchwartzBergman (Ioi (0 : ℝ))) := by
    rwa [← IsUniformAddGroup.rightUniformSpace_eq (G := SchwartzBergman (Ioi (0 : ℝ)))]
  letI : CompleteSpace (SchwartzBergman (Iio (1 : ℝ))) := by
    rwa [← IsUniformAddGroup.rightUniformSpace_eq (G := SchwartzBergman (Iio (1 : ℝ)))]
  refine ⟨inferInstance, inferInstance, inferInstance, ?_⟩
  rw [IsUniformAddGroup.rightUniformSpace_eq (G := PairedBergman)]
  infer_instance

set_option maxHeartbeats 2000000 in
/-- A continuous lift from the entire Schwartz–Bergman space gives inverse
continuity on the closed flat paired range. -/
theorem exists_sLocalTate_polarFreePaired_closedEmbedding
    (hm : IsWeilQuotientMeasure (sUnitImage F S) (ν F S μ) Measure.count
      (sLocalClassHaar F S m)) :
    ∃ ε : S → ℂ → ℂ, (∀ v, IsFiniteTateMultiplier F S μ (χ F S ω) v (ε v)) ∧
      let ρ := sLocalExplicitTateFactor F S ω (sLocalTateEpsilonProduct F S ω ε)
      let T := (sLocalPairedBergmanMellin F S m ω).comp (sLocalPolarFreeThetaInclusion F S m ω)
      IsClosedEmbedding T ∧ range T =
        {p : PairedBergman | p ∈ sLocalBergmanGluing ρ ∧
          ∀ s : ℂ, s.re < 1 → 0 ≤ meromorphicOrderAt (ρ * p.2.val) s} := by
  obtain ⟨ε, hε, _, hclosed, hrange⟩ := exists_sLocalTate_polarFreePaired_range F S μ m hm ω
  let ρ := sLocalExplicitTateFactor F S ω (sLocalTateEpsilonProduct F S ω ε)
  let T := (sLocalPairedBergmanMellin F S m ω).comp (sLocalPolarFreeThetaInclusion F S m ω)
  let mk := restrictedQuotientMk (Flat F S) (ThetaKernel F S m ω)
  have hmk : Surjective mk := restrictedQuotientMk_surjective (Flat F S) (ThetaKernel F S m ω)
  have heq : range T = range (fun g : Flat F S ↦
      sLocalPairedBergmanMellin F S m ω (Submodule.Quotient.mk g.val)) := by
    exact (hmk.range_comp T).symm
  have hT : IsClosed (range T) := by rw [heq, hrange]; exact hclosed
  have hi : Injective T :=
    (sLocalPairedBergmanMellin_injective F S m ω).comp
      (sLocalPolarFreeThetaInclusion_injective F S m ω)
  let V := T.toLinearMap.range
  let Q := T.rangeRestrict
  have hQ : Injective Q := fun _ _ h ↦ hi (congrArg Subtype.val h)
  have hcV : IsClosed (V : Set PairedBergman) := hT
  obtain ⟨L, hL⟩ := exists_sLocalPolarFree_zeta_eq_schwartzBergmanCLM F S μ m hm ω
  let A := mk.comp L
  have hsurj : Surjective (Q.comp A) := by
    rintro ⟨p, q, rfl⟩
    have hp : T q ∈ {p : PairedBergman | p ∈ sLocalBergmanGluing ρ ∧
        ∀ s : ℂ, s.re < 1 → 0 ≤ meromorphicOrderAt (ρ * p.2.val) s} := by
      rw [← hrange, ← heq]
      exact ⟨q, rfl⟩
    have hρ : Meromorphic ρ :=
      sLocalExplicitTateFactor_meromorphic F S ω _ fun z ↦
        analyticAt_const.mul (Finset.analyticAt_fun_prod _ fun v _ ↦ (hε v).1 z trivial)
    obtain ⟨G, hG, hEq⟩ := (sLocalBergmanGluing_entire_iff ρ hρ (T q) hp.1).mp hp.2
    let g : EntireBergman := ⟨G, sLocalTate_entire_mem_schwartzBergman F S μ ω ε hε
      (T q) hp.1 G hG hEq⟩
    refine ⟨g, Subtype.ext ?_⟩
    apply congrArg (sLocalPairedBergmanMellin F S m ω)
    apply sLocalRightBergmanMellin_injective F S m ω
    apply Subtype.ext
    funext z
    change (T (A g)).1.val z = (T q).1.val z
    by_cases hz : 0 < z.re
    · letI : (ν F S μ).IsHaarMeasure :=
        sLocalZetaProductMeasure_isHaar F S μ (archimedeanMultiplicativeHaar F)
      let f := (L g).val
      have hri := (sLocalPairedBergmanMellin_idelic F S m ω (ν F S μ) hm f).1 z hz
      have hzeta := (sLocalIdelicZeta_meromorphic_continuation F S μ ω f).2 hz
      exact hri.trans (hzeta.symm.trans ((hL g hz).trans (hEq hz)))
    · exact ((T (A g)).1.property.1 hz).trans ((T q).1.property.1 hz).symm
  obtain ⟨hadd, hpoly, hmet, hcomplete⟩ :=
    schwartzBergman_frechet (univ : Set ℝ) isOpen_univ ordConnected_univ univ_nonempty
  letI : MetrizableSpace EntireBergman := hmet
  letI : @CompleteSpace EntireBergman (IsTopologicalAddGroup.rightUniformSpace _) := hcomplete
  letI : ContinuousSMul ℂ EntireBergman := (PolynormableSpace.withSeminorms ℂ _).continuousSMul
  obtain ⟨hVadd, hVpoly, hVmet, hVcomplete⟩ :=
    isFrechetTVS_closedSubmodule sLocalPairedBergman_frechet V hcV
  letI : IsTopologicalAddGroup V := hVadd
  letI : UniformSpace V := IsTopologicalAddGroup.rightUniformSpace V
  letI : IsUniformAddGroup V := isUniformAddGroup_of_addCommGroup
  letI : MetrizableSpace V := hVmet
  letI : CompleteSpace V := hVcomplete
  letI : PolynormableSpace ℂ V := hVpoly
  letI : ContinuousSMul ℂ V := (PolynormableSpace.withSeminorms ℂ V).continuousSMul
  obtain ⟨_, _, h₁⟩ := schwartzBergman_schwartzLine_topology (Ioi (0 : ℝ))
    isOpen_Ioi ordConnected_Ioi nonempty_Ioi
  obtain ⟨_, _, h₂⟩ := schwartzBergman_schwartzLine_topology (Iio (1 : ℝ))
    isOpen_Iio ordConnected_Iio nonempty_Iio
  letI : T2Space (SchwartzBergman (Ioi (0 : ℝ))) := h₁.t2Space
  letI : T2Space (SchwartzBergman (Iio (1 : ℝ))) := h₂.t2Space
  letI : (uniformity V).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  letI : BaireSpace V := BaireSpace.of_completelyPseudoMetrizable
  have hopen : IsOpenMap (Q.comp A) := isOpenMap_of_surjective_complete_baire _ hsurj
  have hA : Surjective A := by
    intro x
    obtain ⟨g, hg⟩ := hsurj (Q x)
    exact ⟨g, hQ hg⟩
  have hQo : IsOpenMap Q := IsOpenMap.of_comp A.continuous hA hopen
  have hQe := (IsOpenEmbedding.of_continuous_injective_isOpenMap Q.continuous hQ hQo).isEmbedding
  exact ⟨ε, hε, ⟨IsEmbedding.subtypeVal.comp hQe, hT⟩, heq.trans hrange⟩

private def pairedBergmanShift (d : ℂ) (hd : d.re = 0) : PairedBergman ≃L[ℂ] PairedBergman :=
  (schwartzBergmanVerticalShiftEquiv _ isOpen_Ioi ordConnected_Ioi nonempty_Ioi d hd).prodCongr
    (schwartzBergmanVerticalShiftEquiv _ isOpen_Iio ordConnected_Iio nonempty_Iio d hd)

private theorem pairedBergmanShift_polarFree_iff (ρ : ℂ → ℂ) (d : ℂ) (hd : d.re = 0)
    (p : PairedBergman) :
    let q := pairedBergmanShift d hd p
    let ρ' := fun z ↦ ρ (z+d)
    (q ∈ sLocalBergmanGluing ρ' ∧
      ∀ s : ℂ, s.re < 1 → 0 ≤ meromorphicOrderAt (ρ' * q.2.val) s) ↔
    (p ∈ sLocalBergmanGluing ρ ∧
      ∀ s : ℂ, s.re < 1 → 0 ≤ meromorphicOrderAt (ρ * p.2.val) s) := by
  intro q ρ'
  have hre (z : ℂ) : (z+d).re = z.re := by simp [hd]
  have hre' (z : ℂ) : (z-d).re = z.re := by simp [hd]
  have ho (s : ℂ) : meromorphicOrderAt (ρ' * q.2.val) s =
      meromorphicOrderAt (ρ * p.2.val) (s+d) := by
    change meromorphicOrderAt ((ρ * p.2.val) ∘ fun z ↦ z+d) s = _
    have hderiv : HasDerivAt (fun z : ℂ ↦ z + d) 1 s := (hasDerivAt_id s).add_const d
    exact meromorphicOrderAt_comp_of_deriv_ne_zero
      (analyticAt_id.add analyticAt_const) (by rw [hderiv.deriv]; exact one_ne_zero)
  constructor
  · rintro ⟨hmatch, horders⟩
    refine ⟨fun z hz h₁ ↦ ?_, fun s hs ↦ ?_⟩
    · have h := hmatch (z-d) (by rwa [hre']) (by rwa [hre'])
      change p.1.val (z-d+d) = ρ (z-d+d) * p.2.val (z-d+d) at h
      simpa only [sub_add_cancel] using h
    · have h := horders (s-d) (by rwa [hre'])
      rwa [ho, sub_add_cancel] at h
  · rintro ⟨hmatch, horders⟩
    refine ⟨fun z hz h₁ ↦ ?_, fun s hs ↦ ?_⟩
    · exact hmatch (z+d) (by rwa [hre]) (by rwa [hre])
    · rw [ho]
      exact horders (s+d) (by rwa [hre])

/-- A purely imaginary change of chart preserves the closed embedding and
translates its matching multiplier. -/
theorem exists_sLocalTate_polarFreePaired_shift_closedEmbedding
    (hm : IsWeilQuotientMeasure (sUnitImage F S) (ν F S μ) Measure.count
      (sLocalClassHaar F S m)) (d : ℂ) (hd : d.re = 0) :
    ∃ ε : S → ℂ → ℂ, (∀ v, IsFiniteTateMultiplier F S μ (χ F S ω) v (ε v)) ∧
      let ρ := fun z ↦ sLocalExplicitTateFactor F S ω (sLocalTateEpsilonProduct F S ω ε) (z+d)
      let T := (sLocalPairedBergmanMellin_shift F S m ω d hd).comp
        (sLocalPolarFreeThetaInclusion F S m ω)
      IsClosedEmbedding T ∧ range T =
        {p : PairedBergman | p ∈ sLocalBergmanGluing ρ ∧
          ∀ s : ℂ, s.re < 1 → 0 ≤ meromorphicOrderAt (ρ * p.2.val) s} := by
  obtain ⟨ε, hε, hclosed, hrange⟩ :=
    exists_sLocalTate_polarFreePaired_closedEmbedding F S μ m ω hm
  let e := pairedBergmanShift d hd
  let T := (sLocalPairedBergmanMellin F S m ω).comp (sLocalPolarFreeThetaInclusion F S m ω)
  let ρ := sLocalExplicitTateFactor F S ω (sLocalTateEpsilonProduct F S ω ε)
  refine ⟨ε, hε, e.toHomeomorph.isClosedEmbedding.comp hclosed, ?_⟩
  change range (e ∘ T) = _
  ext p
  constructor
  · rintro ⟨x, rfl⟩
    apply (pairedBergmanShift_polarFree_iff ρ d hd (T x)).2
    have hx : T x ∈ range T := ⟨x, rfl⟩
    have heq : range T = {p : PairedBergman | p ∈ sLocalBergmanGluing ρ ∧
        ∀ s : ℂ, s.re < 1 → 0 ≤ meromorphicOrderAt (ρ * p.2.val) s} := hrange
    rw [heq] at hx
    exact hx
  · intro hp
    let q := e.symm p
    have he : e q = p := e.apply_symm_apply p
    have hq : q ∈ range T := by
      rw [hrange]
      apply (pairedBergmanShift_polarFree_iff ρ d hd q).1
      simpa only [show pairedBergmanShift d hd q = p from he, mem_ofPred_eq] using hp
    obtain ⟨x, hx⟩ := hq
    exact ⟨x, (congrArg e hx).trans he⟩

/-- The polar-free paired transform for every continuous homomorphic norm
section, in the corresponding quasi-character chart. -/
theorem exists_sLocalTate_polarFreePaired_for_section
    (hm : IsWeilQuotientMeasure (sUnitImage F S) (ν F S μ) Measure.count
      (sLocalClassHaar F S m))
    (τ : Multiplicative ℝ →* SIdeleQuotient F S) (hτ : Continuous τ)
    (hmod : ∀ t : ℝ, sLocalClassModulus F S (τ (Multiplicative.ofAdd t)) = Real.exp t) :
    ∃ (d : ℂ) (hd : d.re = 0) (ε : S → ℂ → ℂ),
      (∀ v, IsFiniteTateMultiplier F S μ (χ F S ω) v (ε v)) ∧
      (∀ (z : ℂ) (t : ℝ) (k : SLocalThetaNormOne F S),
        sLocalZetaWeight F S ω (z-d) (τ (Multiplicative.ofAdd t) * k.val) =
          Complex.exp (z * (t : ℂ)) * (ω k : ℂ)) ∧
      let ρ := fun z ↦ sLocalExplicitTateFactor F S ω (sLocalTateEpsilonProduct F S ω ε) (z-d)
      let T := (sLocalPairedBergmanMellin_shift F S m ω (-d) (by simp [hd])).comp
        (sLocalPolarFreeThetaInclusion F S m ω)
      IsClosedEmbedding T ∧ range T =
        {p : PairedBergman | p ∈ sLocalBergmanGluing ρ ∧
          ∃ G : ℂ → ℂ, AnalyticOnNhd ℂ G univ ∧ EqOn G p.1.val {z | 0 < z.re}} := by
  obtain ⟨d, hd, hweight⟩ := exists_sLocalSection_phase F S ω τ hτ hmod
  obtain ⟨ε, hε, hclosed, hrange⟩ :=
    exists_sLocalTate_polarFreePaired_shift_closedEmbedding F S μ m ω hm (-d) (by simp [hd])
  refine ⟨d, hd, ε, hε, hweight, hclosed, ?_⟩
  let ρ := sLocalExplicitTateFactor F S ω (sLocalTateEpsilonProduct F S ω ε)
  let ρ' (z : ℂ) := ρ (z-d)
  have hρ : Meromorphic ρ := sLocalExplicitTateFactor_meromorphic F S ω _
    (fun z ↦ analyticAt_const.mul (Finset.analyticAt_fun_prod _ fun v _ ↦ (hε v).1 z trivial))
  have hρ' : Meromorphic ρ' := fun z ↦
    (hρ (z-d)).comp_analyticAt (g := fun w : ℂ ↦ w-d) (x := z)
      (show AnalyticAt ℂ (fun w : ℂ ↦ w-d) z from analyticAt_id.sub analyticAt_const)
  simp only [← sub_eq_add_neg] at hrange
  rw [hrange]
  ext p
  show (p ∈ sLocalBergmanGluing ρ' ∧ _) ↔ (p ∈ sLocalBergmanGluing ρ' ∧ _)
  exact and_congr_right fun hp ↦ sLocalBergmanGluing_entire_iff ρ' hρ' p hp

section PairedTranslation

omit [MeasurableSpace (AUnits F)] [BorelSpace (AUnits F)]
  [∀ v : S, MeasurableSpace (K F S v)ˣ] [∀ v : S, BorelSpace (K F S v)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)] [BorelSpace (InfiniteAdeleRing F)]

/-- Left translation in the paired target multiplies both holomorphic
components by the quasi-character in the chosen chart. -/
def sLocalPairedTateTranslate (d : ℂ) (q : SIdeleQuotient F S) (p : PairedBergman) :
    PairedBergman :=
  let u := (sLocalZetaSplit F S).symm q
  (Complex.exp (d * (u.1 : ℂ)) * (ω u.2 : ℂ)) •
    (schwartzBergmanRadialTranslate _ isOpen_Ioi ordConnected_Ioi nonempty_Ioi u.1 p.1,
      schwartzBergmanRadialTranslate _ isOpen_Iio ordConnected_Iio nonempty_Iio u.1 p.2)

set_option maxHeartbeats 1000000 in
theorem continuous_sLocalPairedTateTranslate (d : ℂ) :
    Continuous (fun p : SIdeleQuotient F S × PairedBergman ↦
      sLocalPairedTateTranslate F S ω d p.1 p.2) := by
  let U := fun p : SIdeleQuotient F S × PairedBergman ↦ (sLocalZetaSplit F S).symm p.1
  have hU : Continuous U := (sLocalZetaSplit F S).symm.continuous.comp continuous_fst
  have hs : Continuous (fun p : SIdeleQuotient F S × PairedBergman ↦
      Complex.exp (d * ((U p).1 : ℂ)) * (ω (U p).2 : ℂ)) :=
    (Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp hU.fst))).mul
      (continuous_subtype_val.comp (ω.continuous.comp hU.snd))
  have hp := schwartzBergman_frechet (Ioi (0 : ℝ)) isOpen_Ioi ordConnected_Ioi nonempty_Ioi
  have hn := schwartzBergman_frechet (Iio (1 : ℝ)) isOpen_Iio ordConnected_Iio nonempty_Iio
  letI : PolynormableSpace ℂ (SchwartzBergman (Ioi (0 : ℝ))) := hp.choose_spec.1
  letI : PolynormableSpace ℂ (SchwartzBergman (Iio (1 : ℝ))) := hn.choose_spec.1
  letI : ContinuousSMul ℂ (SchwartzBergman (Ioi (0 : ℝ))) :=
    (PolynormableSpace.withSeminorms ℂ _).continuousSMul
  letI : ContinuousSMul ℂ (SchwartzBergman (Iio (1 : ℝ))) :=
    (PolynormableSpace.withSeminorms ℂ _).continuousSMul
  have h₁ := (continuous_schwartzBergmanRadialTranslate (Ioi (0 : ℝ)) isOpen_Ioi
    ordConnected_Ioi nonempty_Ioi).comp (hU.fst.prodMk continuous_snd.fst)
  have h₂ := (continuous_schwartzBergmanRadialTranslate (Iio (1 : ℝ)) isOpen_Iio
    ordConnected_Iio nonempty_Iio).comp (hU.fst.prodMk continuous_snd.snd)
  exact (hs.smul h₁).prodMk (hs.smul h₂)

theorem sLocalPairedTateTranslate_apply (d : ℂ) (q : SIdeleQuotient F S) (p : PairedBergman) :
    (∀ z, 0 < z.re → (sLocalPairedTateTranslate F S ω d q p).1.val z =
      sLocalZetaWeight F S ω (z+d) q * p.1.val z) ∧
    (∀ z, z.re < 1 → (sLocalPairedTateTranslate F S ω d q p).2.val z =
      sLocalZetaWeight F S ω (z+d) q * p.2.val z) := by
  let u := (sLocalZetaSplit F S).symm q
  have h (z : ℂ) : sLocalZetaWeight F S ω (z+d) q =
      Complex.exp (z * (u.1 : ℂ)) * Complex.exp (d * (u.1 : ℂ)) * (ω u.2 : ℂ) := by
    rw [← show sLocalZetaSplit F S u = q from (sLocalZetaSplit F S).apply_symm_apply q,
      sLocalZetaWeight_split, add_mul, Complex.exp_add]
  constructor
  · intro z hz
    let A := Complex.exp (d * (u.1 : ℂ)) * (ω u.2 : ℂ)
    change A * (schwartzBergmanRadialTranslate (Ioi (0 : ℝ)) isOpen_Ioi
      ordConnected_Ioi nonempty_Ioi u.1 p.1).val z = _
    calc
      _ = A * (Complex.exp (z * (u.1 : ℂ)) * p.1.val z) :=
        congrArg (A * ·) (schwartzBergmanRadialTranslate_apply (Ioi (0 : ℝ))
          isOpen_Ioi ordConnected_Ioi nonempty_Ioi u.1 p.1 z hz)
      _ = _ := by rw [h]; dsimp only [A]; ring
  · intro z hz
    let A := Complex.exp (d * (u.1 : ℂ)) * (ω u.2 : ℂ)
    change A * (schwartzBergmanRadialTranslate (Iio (1 : ℝ)) isOpen_Iio
      ordConnected_Iio nonempty_Iio u.1 p.2).val z = _
    calc
      _ = A * (Complex.exp (z * (u.1 : ℂ)) * p.2.val z) :=
        congrArg (A * ·) (schwartzBergmanRadialTranslate_apply (Iio (1 : ℝ))
          isOpen_Iio ordConnected_Iio nonempty_Iio u.1 p.2 z hz)
      _ = _ := by rw [h]; dsimp only [A]; ring

private theorem pairedBergman_ext {p q : PairedBergman}
    (h₁ : ∀ z : ℂ, 0 < z.re → p.1.val z = q.1.val z)
    (h₂ : ∀ z : ℂ, z.re < 1 → p.2.val z = q.2.val z) : p = q := by
  refine Prod.ext (Subtype.ext (funext fun z ↦ ?_)) (Subtype.ext (funext fun z ↦ ?_))
  · by_cases hz : 0 < z.re
    · exact h₁ z hz
    · exact (p.1.property.1 hz).trans (q.1.property.1 hz).symm
  · by_cases hz : z.re < 1
    · exact h₂ z hz
    · exact (p.2.property.1 hz).trans (q.2.property.1 hz).symm

theorem sLocalPairedTateTranslate_one (d : ℂ) (p : PairedBergman) :
    sLocalPairedTateTranslate F S ω d 1 p = p := by
  have h (z : ℂ) : sLocalZetaWeight F S ω z 1 = 1 := by
    have he : sLocalZetaSplit F S (0, 1) = 1 := by
      change (QuotientGroup.mk' (sUnitImage F S)) (sLocalExpSection F S 1) * 1 = 1
      rw [map_one, map_one]
      exact one_mul (1 : SIdeleQuotient F S)
    rw [← he, sLocalZetaWeight_split]
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, map_one, Circle.coe_one, mul_one]
  apply pairedBergman_ext
  · intro z hz
    rw [(sLocalPairedTateTranslate_apply F S ω d 1 p).1 z hz]
    simp only [h, one_mul]
  · intro z hz
    rw [(sLocalPairedTateTranslate_apply F S ω d 1 p).2 z hz]
    simp only [h, one_mul]

theorem sLocalPairedTateTranslate_mul (d : ℂ) (c b : SIdeleQuotient F S) (p : PairedBergman) :
    sLocalPairedTateTranslate F S ω d (c*b) p =
      sLocalPairedTateTranslate F S ω d c (sLocalPairedTateTranslate F S ω d b p) := by
  apply pairedBergman_ext
  · intro z hz
    rw [(sLocalPairedTateTranslate_apply F S ω d (c*b) p).1 z hz,
      (sLocalPairedTateTranslate_apply F S ω d c _).1 z hz,
      (sLocalPairedTateTranslate_apply F S ω d b p).1 z hz, sLocalZetaWeight_mul, mul_assoc]
  · intro z hz
    rw [(sLocalPairedTateTranslate_apply F S ω d (c*b) p).2 z hz,
      (sLocalPairedTateTranslate_apply F S ω d c _).2 z hz,
      (sLocalPairedTateTranslate_apply F S ω d b p).2 z hz, sLocalZetaWeight_mul, mul_assoc]

end PairedTranslation

omit [MeasurableSpace (InfiniteAdeleRing F)] [BorelSpace (InfiniteAdeleRing F)] in
/-- The corrected target action is equivariant with the actual homogeneous
theta action in every imaginary-shifted chart. -/
theorem sLocalPairedTateTranslate_intertwines
    (hm : IsWeilQuotientMeasure (sUnitImage F S) (ν F S μ) Measure.count
      (sLocalClassHaar F S m)) (d : ℂ) (hd : d.re = 0)
    (c : SIdeleQuotient F S) (u : SLocalHomogeneousThetaQuotient F S m ω) :
    let T := sLocalPairedBergmanMellin_shift F S m ω d hd
    T (sLocalHomogeneousThetaTranslate F S m ω c u) =
      sLocalPairedTateTranslate F S ω d c (T u) := by
  intro T
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective c
  letI : (ν F S μ).IsHaarMeasure :=
    sLocalZetaProductMeasure_isHaar F S μ (archimedeanMultiplicativeHaar F)
  obtain ⟨h₁, h₂⟩ := sLocalPairedBergmanMellin_translate F S m ω (ν F S μ) hm g u
  obtain ⟨h₁', h₂'⟩ := sLocalPairedTateTranslate_apply F S ω d (QuotientGroup.mk g) (T u)
  apply pairedBergman_ext
  · intro z hz
    rw [h₁' z hz, (sLocalPairedBergmanMellin_shift_apply F S m ω d hd _ z).1,
      (sLocalPairedBergmanMellin_shift_apply F S m ω d hd u z).1]
    exact h₁ _ (by simpa [Complex.add_re, hd] using hz)
  · intro z hz
    rw [h₂' z hz, (sLocalPairedBergmanMellin_shift_apply F S m ω d hd _ z).2,
      (sLocalPairedBergmanMellin_shift_apply F S m ω d hd u z).2]
    exact h₂ _ (by simpa [Complex.add_re, hd] using hz)

/-- The class action restricts to a jointly continuous action on the flat
quotient and is intertwined by the shifted paired Mellin map. -/
theorem exists_sLocalPolarFreeThetaTranslate
    (hm : IsWeilQuotientMeasure (sUnitImage F S) (ν F S μ) Measure.count
      (sLocalClassHaar F S m)) (d : ℂ) (hd : d.re = 0) :
    let X := SLocalPolarFreeThetaQuotient F S m ω
    let J := sLocalPolarFreeThetaInclusion F S m ω
    let T := (sLocalPairedBergmanMellin_shift F S m ω d hd).comp J
    ∃ A : SIdeleQuotient F S × X → X, Continuous A ∧
      (∀ c u, J (A (c,u)) = sLocalHomogeneousThetaTranslate F S m ω c (J u)) ∧
      (∀ c u, T (A (c,u)) = sLocalPairedTateTranslate F S ω d c (T u)) ∧
      (∀ u, A (1,u) = u) ∧ (∀ c b u, A (c*b,u) = A (c,A (b,u))) := by
  intro X J T
  obtain ⟨_, _, hT, _⟩ :=
    exists_sLocalTate_polarFreePaired_shift_closedEmbedding F S μ m ω hm d hd
  let mk := restrictedQuotientMk (Flat F S) (ThetaKernel F S m ω)
  have hmk : Surjective mk := restrictedQuotientMk_surjective (Flat F S) (ThetaKernel F S m ω)
  have hinv (c : SIdeleQuotient F S) (u : X) :
      ∃ v : X, J v = sLocalHomogeneousThetaTranslate F S m ω c (J u) := by
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective c
    obtain ⟨f, rfl⟩ := hmk u
    let f' : Flat F S := ⟨sLocalBruhatLeftTranslate F S g f.val,
      sLocalBruhatLeftTranslate_mem_polarFree F S g f.property⟩
    exact ⟨mk f', (sLocalHomogeneousThetaTranslate_mkQ F S m ω g f.val).symm⟩
  let B (x : SIdeleQuotient F S × X) := sLocalPairedTateTranslate F S ω d x.1 (T x.2)
  have hB (c : SIdeleQuotient F S) (u v : X)
      (hv : J v = sLocalHomogeneousThetaTranslate F S m ω c (J u)) : T v = B (c,u) := by
    change (sLocalPairedBergmanMellin_shift F S m ω d hd) (J v) = _
    rw [hv]
    exact sLocalPairedTateTranslate_intertwines F S μ m ω hm d hd c (J u)
  have hb (x : SIdeleQuotient F S × X) : B x ∈ range T := by
    obtain ⟨v, hv⟩ := hinv x.1 x.2
    exact ⟨v, hB x.1 x.2 v hv⟩
  let A (x : SIdeleQuotient F S × X) := hT.isEmbedding.toHomeomorph.symm ⟨B x, hb x⟩
  have hAT (x : SIdeleQuotient F S × X) : T (A x) = B x :=
    congrArg Subtype.val (hT.isEmbedding.toHomeomorph.apply_symm_apply ⟨B x, hb x⟩)
  have hAc : Continuous A := hT.isEmbedding.continuous_iff.mpr
    (((continuous_sLocalPairedTateTranslate F S ω d).comp
      (continuous_fst.prodMk (T.continuous.comp continuous_snd))).congr fun x ↦ (hAT x).symm)
  have hAJ (c : SIdeleQuotient F S) (u : X) :
      J (A (c,u)) = sLocalHomogeneousThetaTranslate F S m ω c (J u) := by
    obtain ⟨v, hv⟩ := hinv c u
    rw [hT.injective ((hAT _).trans (hB c u v hv).symm)]
    exact hv
  refine ⟨A, hAc, hAJ, fun c u ↦ hAT (c,u), ?_, ?_⟩
  · intro u
    apply sLocalPolarFreeThetaInclusion_injective F S m ω
    rw [hAJ, sLocalHomogeneousThetaTranslate_one]
  · intro c b u
    apply sLocalPolarFreeThetaInclusion_injective F S m ω
    rw [hAJ, hAJ, hAJ, sLocalHomogeneousThetaTranslate_mul]

omit [MeasurableSpace (InfiniteAdeleRing F)] [BorelSpace (InfiniteAdeleRing F)] in
/-- The flat quotient transform uses the two actual idelic integrals in the
shifted exponent chart. -/
theorem sLocalPolarFreePaired_idelic
    (hm : IsWeilQuotientMeasure (sUnitImage F S) (ν F S μ) Measure.count
      (sLocalClassHaar F S m))
    (d : ℂ) (hd : d.re = 0) (f : Flat F S) :
    let q := restrictedQuotientMk (Flat F S) (ThetaKernel F S m ω) f
    let p := sLocalPairedBergmanMellin_shift F S m ω d hd
      (sLocalPolarFreeThetaInclusion F S m ω q)
    (∀ z, 0 < z.re → p.1.val z = sLocalIdelicZetaIntegral F S (ν F S μ) ω f.val (z+d)) ∧
    (∀ z, z.re < 1 → p.2.val z = sLocalIdelicZetaIntegral F S (ν F S μ) ω⁻¹
      (sLocalSelectedFourier F S f.val) (1-(z+d))) := by
  intro q p
  letI : (ν F S μ).IsHaarMeasure :=
    sLocalZetaProductMeasure_isHaar F S μ (archimedeanMultiplicativeHaar F)
  obtain ⟨h₁, h₂⟩ := sLocalPairedBergmanMellin_idelic F S m ω (ν F S μ) hm f.val
  constructor
  · intro z hz
    exact h₁ _ (by simpa [Complex.add_re, hd] using hz)
  · intro z hz
    exact h₂ _ (by simpa [Complex.add_re, hd] using hz)

end PolarFree

/-- The pole bounds of Theorem 7.1.3.2(3)(b) hold for the same Tate factor
that gives the S-local functional equation on every test and at every
meromorphic germ. -/
theorem exists_sLocalTateProduct_algebraicNormTwist_bounds
    (ω : Characters F S) (χ₀ : SIdeleQuotient F S → ℂ) (s₀ : ℂ)
    (htwist : ∀ g, sLocalZetaWeight F S ω 0 g = χ₀ g * (sLocalClassModulus F S g : ℂ) ^ s₀)
    (hinfty : sLocalIntegralInfinityType F S χ₀)
    (hfinite : ∀ v : S, finiteZetaUnramified F v.val (sLocalFiniteZetaPhases F S ω v) →
      IsAlgebraic ℚ (χ₀ (QuotientGroup.mk (sLocalFiniteZetaInsert F S v
        (chosenFiniteUniformizer F v.val))))) :
    ∃ ε : S → ℂ → ℂ,
      (∀ v, IsFiniteTateMultiplier F S μ (χ F S ω) v (ε v)) ∧
      let ρ := sLocalExplicitTateFactor F S ω (sLocalTateEpsilonProduct F S ω ε)
      Meromorphic ρ ∧
      (∀ (f : E F S) (c : ℂ), continuedZeta F S μ ω f =ᶠ[𝓝[≠] c] fun z ↦
        ρ z * continuedZeta F S μ ω⁻¹ (sLocalSelectedFourier F S f) (1-z)) ∧
      (SchanuelConjecture → ∀ z,
        meromorphicOrderAt ρ z < -(Module.finrank ℚ F : WithTop ℤ) →
        z.re = 0 ∧ (0 < sLocalArchPoleCount F S ω z ∨ z = -(s₀.im : ℂ) * Complex.I)) ∧
      (SixExponentialsTheorem → ∀ z,
        meromorphicOrderAt ρ z < -((2 * Module.finrank ℚ F : ℕ) : WithTop ℤ) →
        z = -(s₀.im : ℂ) * Complex.I) := by
  obtain ⟨ε, hε, hP, hPn, _, hMer, _, _, hGerm, _⟩ :=
    exists_sLocalTateProduct_functionalEquation F S μ ω
  obtain ⟨hS, hSix⟩ := sLocalExplicitTateFactor_algebraicNormTwist_bounds
    F S ω χ₀ s₀ htwist hinfty hfinite (sLocalTateEpsilonProduct F S ω ε)
    (fun z ↦ hP z (mem_univ z)) hPn
  exact ⟨ε, hε, hMer, hGerm, hS, hSix⟩

omit [MeasurableSpace (AUnits F)] [BorelSpace (AUnits F)]
  [∀ v : S, MeasurableSpace (K F S v)ˣ] [∀ v : S, BorelSpace (K F S v)ˣ] in
/-- Every unitary S-local character is represented by an imaginary exponent
in the canonical norm-one chart. -/
theorem sLocalZetaWeight_represents_unitary (ψ : QuasiCharacter (SIdeleQuotient F S))
    (hψ : ∀ q, ‖ψ q‖ = 1) :
    ∃ (ω : Characters F S) (x : ℝ), ∀ q, ψ q =
      sLocalZetaWeight F S ω ((x : ℂ) * Complex.I) q := by
  obtain ⟨ω, z, hrep, _⟩ := sLocalZetaWeight_represents F S ψ
  have hn := norm_sLocalZetaWeight_mk F S ω z
    (sLocalExpSection F S (Multiplicative.ofAdd 1))
  rw [← hrep, hψ, sLocalIdeleNorm_expSection, Real.log_exp, mul_one] at hn
  have hz : z.re = 0 := Real.exp_injective (hn.symm.trans Real.exp_zero.symm)
  refine ⟨ω, z.im, fun q ↦ (hrep q).trans ?_⟩
  congr 1
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, hz]

omit [MeasurableSpace (AUnits F)] [BorelSpace (AUnits F)]
  [∀ v : S, MeasurableSpace (K F S v)ˣ] [∀ v : S, BorelSpace (K F S v)ˣ] in
/-- On the open unramified locus, global norm twists descend to the
S-local chart with the same norm exponent. -/
theorem sLocalZetaWeight_represents_globalNormTwist (ψ ψ₀ : sUnramified F S) (s₀ : ℂ)
    (hψ : ∀ q, ‖ψ.val q‖ = 1)
    (hnorm : ∀ q, ψ.val q = ψ₀.val q * (ideleClassNorm F q : ℂ) ^ s₀) :
    ∃ (ω : Characters F S) (x : ℝ), ∀ q,
      sLocalZetaWeight F S ω ((x : ℂ) * Complex.I) q =
        sCharacterRestriction F S ψ₀ q * (sLocalClassModulus F S q : ℂ) ^ s₀ := by
  let π := sIdeleClassToLocal F S
  have hsurj : Surjective π := (sIdeleClassToLocal_isOpenQuotientMap F S).surjective
  obtain ⟨ω, x, hchart⟩ := sLocalZetaWeight_represents_unitary F S
    (sCharacterRestriction F S ψ) (by
      intro q
      obtain ⟨b, rfl⟩ := hsurj q
      rw [sCharacterRestriction_block, hψ])
  refine ⟨ω, x, fun q ↦ (hchart q).symm.trans ?_⟩
  obtain ⟨b, rfl⟩ := hsurj q
  have hn : sLocalClassModulus F S (π b) = ideleClassNorm F (sIdeleClassInclusion F S b) := by
    unfold sLocalClassModulus
    rw [sQuotientNorm_toLocal F S b]
    rfl
  rw [sCharacterRestriction_block, sCharacterRestriction_block, hn, hnorm]

omit [MeasurableSpace (AUnits F)] [BorelSpace (AUnits F)]
  [∀ v : S, MeasurableSpace (K F S v)ˣ] [∀ v : S, BorelSpace (K F S v)ˣ] in
private theorem sLocalNormTwist_at_zero (ω : Characters F S)
    (χ₀ : SIdeleQuotient F S → ℂ) (d s₀ : ℂ)
    (h : ∀ g, sLocalZetaWeight F S ω d g = χ₀ g * (sLocalClassModulus F S g : ℂ) ^ s₀)
    (g : SIdeleQuotient F S) :
    sLocalZetaWeight F S ω 0 g = χ₀ g * (sLocalClassModulus F S g : ℂ) ^ (s₀ - d) := by
  let q := sLocalClassModulus F S g
  have hq : 0 < q := sLocalClassModulus_pos F S g
  have hq₀ : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq.ne'
  have he : sLocalZetaWeight F S ω 0 g * (q : ℂ) ^ d = sLocalZetaWeight F S ω d g := by
    rw [Complex.cpow_def_of_ne_zero hq₀, ← Complex.ofReal_log hq.le]
    unfold sLocalZetaWeight
    simp only [zero_mul, Complex.exp_zero, one_mul]
    change _ * Complex.exp ((Real.log q : ℂ) * d) = Complex.exp (d * (Real.log q : ℂ)) * _
    rw [mul_comm (Real.log q : ℂ) d, mul_comm]
  apply mul_right_cancel₀ (Complex.cpow_ne_zero_iff.mpr (Or.inl hq₀))
  rw [he, h g, mul_assoc, ← Complex.cpow_add _ _ hq₀, sub_add_cancel]

/-- The S-local algebraic norm-twist bounds in the spectral coordinate
of any unitary base on the component. The multiplier and the functional
equation are translated by the same imaginary displacement. -/
theorem exists_sLocalTateProduct_algebraicNormTwist_shifted_bounds
    (ω : Characters F S) (χ₀ : SIdeleQuotient F S → ℂ) (s₀ : ℂ) (x : ℝ)
    (htwist : ∀ g, sLocalZetaWeight F S ω ((x : ℂ) * Complex.I) g =
      χ₀ g * (sLocalClassModulus F S g : ℂ) ^ s₀)
    (hinfty : sLocalIntegralInfinityType F S χ₀)
    (hfinite : ∀ v : S, finiteZetaUnramified F v.val (sLocalFiniteZetaPhases F S ω v) →
      IsAlgebraic ℚ (χ₀ (QuotientGroup.mk (sLocalFiniteZetaInsert F S v
        (chosenFiniteUniformizer F v.val))))) :
    ∃ ε : S → ℂ → ℂ,
      (∀ v, IsFiniteTateMultiplier F S μ (χ F S ω) v (ε v)) ∧
      let d := (x : ℂ) * Complex.I
      let ρ (z : ℂ) := sLocalExplicitTateFactor F S ω (sLocalTateEpsilonProduct F S ω ε) (z + d)
      Meromorphic ρ ∧
      (∀ (f : E F S) (c : ℂ),
        (fun z ↦ continuedZeta F S μ ω f (z + d)) =ᶠ[𝓝[≠] c] fun z ↦
          ρ z * continuedZeta F S μ ω⁻¹ (sLocalSelectedFourier F S f) (1 - (z + d))) ∧
      (SchanuelConjecture → ∀ z,
        meromorphicOrderAt ρ z < -(Module.finrank ℚ F : WithTop ℤ) →
        z.re = 0 ∧ (0 < sLocalArchPoleCount F S ω (z + d) ∨ z = -(s₀.im : ℂ) * Complex.I)) ∧
      (SixExponentialsTheorem → ∀ z,
        meromorphicOrderAt ρ z < -((2 * Module.finrank ℚ F : ℕ) : WithTop ℤ) →
        z = -(s₀.im : ℂ) * Complex.I) := by
  let d := (x : ℂ) * Complex.I
  obtain ⟨ε, hε, hMer, hGerm, hS, hSix⟩ :=
    exists_sLocalTateProduct_algebraicNormTwist_bounds F S μ ω χ₀ (s₀ - d)
      (sLocalNormTwist_at_zero F S ω χ₀ d s₀ htwist) hinfty hfinite
  let ρ := sLocalExplicitTateFactor F S ω (sLocalTateEpsilonProduct F S ω ε)
  have han (z : ℂ) : AnalyticAt ℂ (fun w : ℂ ↦ w + d) z := analyticAt_id.add analyticAt_const
  have ho (z : ℂ) : meromorphicOrderAt (fun w ↦ ρ (w + d)) z =
      meromorphicOrderAt ρ (z + d) :=
    meromorphicOrderAt_comp_of_deriv_ne_zero (f := ρ) (han z) (by
      have hderiv : HasDerivAt (fun w : ℂ ↦ w + d) 1 z := (hasDerivAt_id z).add_const d
      rw [hderiv.deriv]
      exact one_ne_zero)
  have hd : d.re = 0 := by simp [d, Complex.mul_re]
  have hc (z : ℂ) (hz : z + d = -((s₀ - d).im : ℂ) * Complex.I) :
      z = -(s₀.im : ℂ) * Complex.I := by
    apply Complex.ext
    · have he := congrArg Complex.re hz
      simpa [Complex.mul_re, hd] using he
    · have he := congrArg Complex.im hz
      simp [Complex.mul_im] at he ⊢
      linarith
  refine ⟨ε, hε, ?_, ?_, ?_, ?_⟩
  · intro z
    exact (hMer (z + d)).comp_analyticAt (g := fun w : ℂ ↦ w + d) (han z)
  · intro f c
    have ht : Tendsto (fun z : ℂ ↦ z + d) (𝓝[≠] c) (𝓝[≠] (c + d)) :=
      (Homeomorph.addRight d).map_punctured_nhds_eq c |>.le
    exact (hGerm f (c + d)).comp_tendsto ht
  · intro hSch z hz
    have hz' : meromorphicOrderAt ρ (z + d) < -(Module.finrank ℚ F : WithTop ℤ) :=
      (ho z) ▸ hz
    obtain ⟨hRe, hEx⟩ := hS hSch (z + d) hz'
    exact ⟨by simpa only [Complex.add_re, hd, add_zero] using hRe, hEx.imp_right (hc z)⟩
  · intro hExp z hz
    have hz' : meromorphicOrderAt ρ (z + d) < -((2 * Module.finrank ℚ F : ℕ) : WithTop ℤ) :=
      (ho z) ▸ hz
    exact hc z (hSix hExp (z + d) hz')

end

end Masullo
