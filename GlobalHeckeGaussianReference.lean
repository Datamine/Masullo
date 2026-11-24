import SLocalEulerReference
import AdelicTamagawaProduct
import SLocalFourierIntegral
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

open Filter Function Ideal IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical ENNReal NNReal NumberField SchwartzMap

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

private abbrev Place := HeightOneSpectrum (𝓞 F)
private abbrev R := {v : InfinitePlace F // v.IsReal}
private abbrev C := {v : InfinitePlace F // v.IsComplex}
private abbrev E := mixedEmbedding.mixedSpace F

private def realGaussian (a x : ℝ) : ℂ := Real.exp (-a * x ^ 2)

private theorem integral_realGaussian (a : ℝ) :
    (∫ x : ℝ, realGaussian a x) = (Real.sqrt (Real.pi / a) : ℂ) := by
  simp only [realGaussian, integral_complex_ofReal, integral_gaussian]

private theorem integral_complexGaussian :
    (∫ x : ℂ, (Real.exp (-(2 * Real.pi) * ‖x‖ ^ 2) : ℂ)) = 1 / 2 := by
  let a := 2 * Real.pi
  let g := realGaussian a
  have he (x : ℂ) : (Real.exp (-(2 * Real.pi) * ‖x‖ ^ 2) : ℂ) =
      g (Complex.measurableEquivRealProd x).1 * g (Complex.measurableEquivRealProd x).2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    dsimp only [g, a, realGaussian]
    change (Real.exp (-(2 * Real.pi) * (x.re * x.re + x.im * x.im)) : ℂ) =
      (Real.exp (-(2 * Real.pi) * x.re ^ 2) : ℂ) *
        (Real.exp (-(2 * Real.pi) * x.im ^ 2) : ℂ)
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    congr 2
    ring
  simp_rw [he]
  rw [Complex.volume_preserving_equiv_real_prod.integral_comp
      Complex.measurableEquivRealProd.measurableEmbedding (fun p : ℝ × ℝ ↦ g p.1 * g p.2)]
  change (∫ p : ℝ × ℝ, g p.1 * g p.2 ∂(volume : Measure ℝ).prod volume) = _
  rw [integral_prod_mul, show (∫ x : ℝ, g x) = (Real.sqrt (Real.pi / a) : ℂ)
    from integral_realGaussian a, ← Complex.ofReal_mul, ← pow_two, Real.sq_sqrt]
  · have hπ := Real.pi_pos.ne'
    rw [show Real.pi / a = (1 / 2 : ℝ) by dsimp [a]; field_simp]
    norm_num
  · positivity

private theorem mixedGaussian_integral (φ : 𝓢(E F, ℂ))
    (f : R F → 𝓢(ℝ, ℂ)) (g : C F → 𝓢(ℂ, ℂ))
    (hφ : ∀ x : E F, φ x = (∏ v, f v (x.1 v)) * ∏ v, g v (x.2 v))
    (hf : ∀ i x, f i x = realGaussian Real.pi x)
    (hg : ∀ i x, g i x = (Real.pi : ℂ)⁻¹ * (Real.exp (-(2 * Real.pi) * ‖x‖ ^ 2) : ℂ)) :
    φ 0 = (1 / (Real.pi : ℂ)) ^ InfinitePlace.nrComplexPlaces F ∧
      (∫ x, φ x ∂archAdditiveTamagawa F) = φ 0 := by
  have hzero : φ 0 = ((Real.pi : ℂ)⁻¹) ^ InfinitePlace.nrComplexPlaces F := by
    rw [hφ]
    simp [hf, hg, realGaussian, InfinitePlace.nrComplexPlaces]
  have hR (i : R F) : (∫ x, f i x) = 1 := by
    simp_rw [hf]
    rw [integral_realGaussian, div_self Real.pi_pos.ne']
    simp
  have hC (i : C F) : (∫ x, g i x) = (Real.pi : ℂ)⁻¹ * (1 / 2) := by
    simp_rw [hg]
    rw [integral_const_mul, integral_complexGaussian]
  refine ⟨by simpa only [one_div] using hzero, ?_⟩
  rw [archAdditiveTamagawa, integral_smul_nnreal_measure, hzero]
  simp_rw [hφ]
  change (((2 : ℝ≥0) ^ InfinitePlace.nrComplexPlaces F : ℝ≥0) : ℝ) •
    (∫ p : (R F → ℝ) × (C F → ℂ),
      (∏ v, f v (p.1 v)) * ∏ v, g v (p.2 v) ∂
      ((volume : Measure (R F → ℝ)).prod (volume : Measure (C F → ℂ)))) = _
  rw [integral_prod_mul (fun p : R F → ℝ ↦ ∏ v, f v (p v))
    (fun p : C F → ℂ ↦ ∏ v, g v (p v))]
  rw [volume_pi, volume_pi, integral_fintype_prod_eq_prod, integral_fintype_prod_eq_prod]
  simp only [hR, hC, Finset.prod_const_one, one_mul, Finset.prod_const, Finset.card_univ,
    NNReal.coe_pow, NNReal.coe_ofNat, Complex.real_smul, Complex.ofReal_pow, Complex.ofReal_ofNat]
  change (2 : ℂ) ^ InfinitePlace.nrComplexPlaces F *
    ((Real.pi : ℂ)⁻¹ * (1 / 2)) ^ InfinitePlace.nrComplexPlaces F = _
  rw [← mul_pow]
  congr 1
  ring

variable (S : Finset (Place F))

private abbrev trivialReal (v : R F) := sLocalRealArchParameters F S 1 v
private abbrev trivialComplex (v : C F) := sLocalComplexArchParameters F S 1 v

/-- The trivial archimedean reference has equal additive integral and
value at zero. Its Euler factor agrees pointwise in the right half-plane. -/
theorem exists_trivialArchGamma_reference_exact :
    ∃ φ : 𝓢(E F, ℂ),
      φ 0 = (1 / (Real.pi : ℂ)) ^ InfinitePlace.nrComplexPlaces F ∧
      (∫ x, φ x ∂archAdditiveTamagawa F) = φ 0 ∧
      (∀ c : ℂ,
        (fun z ↦ archimedeanNumberFieldZeta F complexTamagawaAngularMeasure
          (trivialReal F S) (trivialComplex F S) z φ) =ᶠ[𝓝[≠] c]
            fun z ↦ (archimedeanNumberFieldZetaDenominator F
              (trivialReal F S) (trivialComplex F S) z)⁻¹) ∧
      ∀ z : ℂ, 0 < z.re →
        archimedeanNumberFieldZeta F complexTamagawaAngularMeasure
          (trivialReal F S) (trivialComplex F S) z φ =
          Complex.Gammaℝ z ^ InfinitePlace.nrRealPlaces F *
            Complex.Gammaℂ z ^ InfinitePlace.nrComplexPlaces F := by
  obtain ⟨φ, f, g, hφ, hf, hg, hM⟩ := exists_archimedeanGammaProductTest_separated_explicit_exact F
    (trivialReal F S) (trivialComplex F S)
    (sLocalRealArchParameters_re F S 1) (sLocalComplexArchParameters_re F S 1)
  have h := mixedGaussian_integral F φ f g hφ ?_ ?_
  · refine ⟨φ, h.1, h.2, hM.1, fun z hz => ?_⟩
    have he := hM.2 (show z ∈ {w : ℂ | 0 < w.re} from hz)
    dsimp only at he
    rw [he]
    unfold archimedeanNumberFieldZetaDenominator
    rw [mul_inv_rev, ← Finset.prod_inv_distrib, ← Finset.prod_inv_distrib]
    simp only [realArchZetaDenominator, complexArchZetaDenominator, inv_inv,
      sLocalComplexArchParameters_one, sLocalRealArchParameters_one, Int.natAbs_zero,
      Nat.cast_zero, zero_div, add_zero, Finset.prod_const, Finset.card_univ, mul_comm]
  · intro i x
    rw [hf, (sLocalRealArchParameters_one F S i).2, pow_zero, one_mul]
    simp [realGaussian, Real.norm_eq_abs, sq_abs]
  · intro i x
    rw [hg]
    simp [trivialComplex, sLocalComplexArchParameters_one]

/-- The trivial Euler reference also gives its meromorphic germs at all points. -/
theorem exists_trivialArchGamma_reference :
    ∃ φ : 𝓢(E F, ℂ),
      φ 0 = (1 / (Real.pi : ℂ)) ^ InfinitePlace.nrComplexPlaces F ∧
      (∫ x, φ x ∂archAdditiveTamagawa F) = φ 0 ∧
      ∀ c : ℂ,
        (fun z ↦ archimedeanNumberFieldZeta F complexTamagawaAngularMeasure
          (trivialReal F S) (trivialComplex F S) z φ) =ᶠ[𝓝[≠] c]
            fun z ↦ (archimedeanNumberFieldZetaDenominator F
              (trivialReal F S) (trivialComplex F S) z)⁻¹ := by
  obtain ⟨φ, h0, hI, h, _⟩ := exists_trivialArchGamma_reference_exact F S
  exact ⟨φ, h0, hI, h⟩

private abbrev integerBox :=
  locallyConstantTestPiProduct (fun v : S ↦ finiteCompletionIntegerRingTest F v.val)

private theorem integerBox_origin :
    (integerBox F S).val 0 = 1 := by
  rw [locallyConstantTestPiProduct_apply]
  apply Finset.prod_eq_one
  intro v _
  change (v.val.adicCompletionIntegers F : Set (v.val.adicCompletion F)).indicator
    (fun _ ↦ (1 : ℂ)) 0 = 1
  exact indicator_of_mem (v.val.adicCompletionIntegers F).zero_mem _

private theorem trivialEuler_reference_origin (φ : 𝓢(E F, ℂ)) :
    GlobalBruhat.evaluation F 0 (sLocalBruhatPure F S φ (integerBox F S)).val = φ 0 := by
  rw [sLocalBruhatRestriction_reconstruct, map_zero, sLocalBruhatPure_restrict]
  rw [show (0 : SAdeles F S).1 = 0 from rfl, map_zero,
    show (0 : SAdeles F S).2 = 0 from rfl, integerBox_origin]
  have hz : ∀ v ∉ S, (0 : Adeles F).2 v ∈ v.adicCompletionIntegers F :=
    fun v _ ↦ (v.adicCompletionIntegers F).zero_mem
  simp only [ite_eq_left hz, mul_one]

section AdditiveMeasures

local instance : MeasurableSpace (InfiniteAdeleRing F) := borel _
local instance : BorelSpace (InfiniteAdeleRing F) := ⟨rfl⟩
local instance (v : Place F) : MeasurableSpace (v.adicCompletion F) := borel _
local instance (v : Place F) : BorelSpace (v.adicCompletion F) := ⟨rfl⟩

private theorem integerLocal_integral (v : Place F) :
    (∫ x : v.adicCompletion F, (finiteCompletionIntegerRingTest F v).val x
      ∂additiveHaarDifferent F v) = ((differentPrimeMass F v).toReal : ℂ) := by
  change (∫ x : v.adicCompletion F, (v.adicCompletionIntegers F : Set _).indicator
    (fun _ ↦ (1 : ℂ)) x ∂additiveHaarDifferent F v) = _
  have hm : MeasurableSet (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
    (Valued.isOpen_valuationSubring _).measurableSet
  rw [integral_indicator hm, setIntegral_const, Complex.real_smul, mul_one]
  simp only [Measure.real, additiveHaarDifferent_integers]

/-- The Fourier transform at the origin of a mixed Schwartz function
times all finite integer-ring indicators is its archimedean integral
times the reciprocal square root of the discriminant. -/
theorem trivialEuler_reference_fourier_origin (φ : 𝓢(E F, ℂ)) :
    GlobalBruhat.evaluation F 0
      (GlobalBruhat.fourier F (sLocalBruhatPure F S φ (integerBox F S)).val) =
      (((NNReal.sqrt ‖discr F‖₊ : ℝ≥0∞)⁻¹).toReal : ℂ) *
        ∫ x, φ x ∂archAdditiveTamagawa F := by
  let r := sLocalBruhatPure F S φ (integerBox F S)
  have h := sLocalFourierCompression_restrict F S r 0
  change sLocalBruhatRestriction F S
      (sLocalBruhatCorestrict F S (GlobalBruhat.fourier F r.val)).val 0 = _ at h
  rw [sLocalBruhatCorestrict_restrict] at h
  have hpad : sLocalBruhatPad F S 0 = 0 := by
    simpa only [mul_zero, zero_mul] using sLocalBruhatPad_mul_project F S 0 0
  change GlobalBruhat.evaluation F (sLocalBruhatPad F S 0) (GlobalBruhat.fourier F r.val) = _ at h
  simp only [mul_zero, hpad, map_zero, toMul_zero, Circle.coe_one, mul_one] at h
  change GlobalBruhat.evaluation F 0 (GlobalBruhat.fourier F r.val) = _
  rw [h, sLocalFourierCompressionMeasure, integral_smul_measure]
  simp_rw [r, sLocalBruhatPure_restrict, locallyConstantTestPiProduct_apply]
  let e := (infiniteAdeleMixedHomeomorph F).toMeasurableEquiv
  let T := ∏ᶠ v : {v : Place F // v ∉ S}, differentPrimeMass F v.val
  let ν := Measure.pi (fun v : S => additiveHaarDifferent F v.val)
  let f (x : InfiniteAdeleRing F) := φ (e x)
  let g (y : (v : S) → v.val.adicCompletion F) :=
    ∏ v : S, (finiteCompletionIntegerRingTest F v.val).val (y v)
  letI (v : Place F) : LocallyCompactSpace (v.adicCompletion F) := finitePlace_locallyCompact F v
  letI (v : Place F) : SecondCountableTopology (v.adicCompletion F) := finitePlace_secondCountable F v
  letI (v : S) : (additiveHaarDifferent F v.val).IsAddHaarMeasure :=
    additiveHaarDifferent_isHaar F v.val
  letI : SFinite (archAdditiveTamagawa F) := by unfold archAdditiveTamagawa; infer_instance
  change T.toReal • (∫ p : SAdeles F S, f p.1 * g p.2 ∂
    ((archAdditiveTamagawa F).map e.symm).prod ν) = _
  rw [integral_prod_mul f g, integral_map_equiv]
  have hf : (fun x ↦ f (e.symm x)) = (φ : E F → ℂ) := by
    funext x
    simp [f]
  rw [hf]
  have hg : (∫ y, g y ∂ν) = (∏ v : S, (differentPrimeMass F v.val).toReal : ℝ) := by
    unfold g ν
    rw [integral_fintype_prod_eq_prod]
    simp only [integerLocal_integral, Complex.ofReal_prod]
  rw [hg, Complex.real_smul]
  rw [← differentPrimeMass_split F S, ENNReal.toReal_mul, ENNReal.toReal_prod,
    Complex.ofReal_mul]
  ring

end AdditiveMeasures

section MultiplicativeMeasures

variable [∀ v : S, MeasurableSpace (v.val.adicCompletion F)ˣ]
  [∀ v : S, BorelSpace (v.val.adicCompletion F)ˣ]
  (μ : ∀ v : S, Measure (v.val.adicCompletion F)ˣ)
  [∀ v : S, (μ v).IsHaarMeasure] [∀ v : S, SigmaFinite (μ v)]

/-- An explicit constant-normalized trivial Euler reference has a known
Fourier value at the origin for the globally normalized additive Haar measure. -/
theorem exists_trivialEuler_reference_origin_ratio :
    ∃ (r : sLocalBruhatImage F S) (b : ℂ), b ≠ 0 ∧
      sLocalEulerNormalizedMellin F S μ 1 r = (fun _ ↦ b) ∧
      GlobalBruhat.evaluation F 0 r.val = (1 / (Real.pi : ℂ)) ^ InfinitePlace.nrComplexPlaces F ∧
      GlobalBruhat.evaluation F 0 (GlobalBruhat.fourier F r.val) =
        (((NNReal.sqrt ‖discr F‖₊ : ℝ≥0∞)⁻¹).toReal : ℂ) *
          GlobalBruhat.evaluation F 0 r.val := by
  obtain ⟨φ, hz, hI, hM⟩ := exists_trivialArchGamma_reference F S
  let g (v : S) := finiteCompletionIntegerRingTest F v.val
  let c (v : S) : ℂ := ((μ v).real (finitePlaceIntegralUnits F v.val) : ℂ)
  have hc (v : S) : c v ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (finiteZetaUnitMass_pos F v.val (μ v)).ne'
  have htriv (v : S) (u : (v.val.adicCompletion F)ˣ) :
      sLocalFiniteZetaPhases F S 1 v u = 1 := by
    apply Circle.coe_injective
    change sLocalZetaWeight F S 1 0 (QuotientGroup.mk (sLocalFiniteZetaInsert F S v u)) = 1
    simp [sLocalZetaWeight]
  have hg (v : S) (z : ℂ) :
      finiteProductClearedLocal F S μ (sLocalFiniteZetaPhases F S 1) v (g v) z = c v := by
    have hv : finiteZetaUnramified F v.val (sLocalFiniteZetaPhases F S 1 v) :=
      fun u _ ↦ htriv v u
    rw [finiteProductClearedLocal, ite_eq_left hv]
    exact finiteZetaClearedDistribution_integerRing_unramified F v.val (μ v)
      (sLocalFiniteZetaPhases F S 1 v) hv z
  refine ⟨sLocalBruhatPure F S φ (integerBox F S), ∏ v, c v,
    Finset.prod_ne_zero_iff.mpr (fun v _ ↦ hc v),
    sLocalEulerNormalizedMellin_const_of_separated F S μ 1 φ g c hM hg, ?_, ?_⟩
  · rw [trivialEuler_reference_origin, hz]
  · rw [trivialEuler_reference_fourier_origin, trivialEuler_reference_origin, hI]

end MultiplicativeMeasures

end

end Masullo
