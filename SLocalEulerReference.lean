import SLocalArchGammaWitness
import SLocalLaurentFormula

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical NumberField SchwartzMap

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]
variable (S : Finset (HeightOneSpectrum (𝓞 F)))
private abbrev L (v : S) := v.val.adicCompletion F
private abbrev K := SLocalThetaNormOne F S

variable [∀ v : S, MeasurableSpace (L F S v)ˣ] [∀ v : S, BorelSpace (L F S v)ˣ]
  (μ : ∀ v : S, Measure (L F S v)ˣ)
  [∀ v : S, (μ v).IsHaarMeasure] [∀ v : S, SigmaFinite (μ v)]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]

omit [∀ v : S, SigmaFinite (μ v)] [MeasurableSpace (InfiniteAdeleRing F)ˣ]
  [BorelSpace (InfiniteAdeleRing F)ˣ] in
theorem exists_cleared_finite_reference
    (χ : ∀ v : S, (L F S v)ˣ →ₜ* Circle) (v : S) :
    ∃ (f : locallyConstantTests (L F S v)) (C : ℂ), C ≠ 0 ∧
      ∀ z, finiteProductClearedLocal F S μ χ v f z = C := by
  by_cases hv : finiteZetaUnramified F v.val (χ v)
  · let C : ℂ := (μ v).real (finitePlaceIntegralUnits F v.val)
    refine ⟨finiteCompletionIntegerRingTest F v.val, C, ?_, fun z ↦ ?_⟩
    · exact Complex.ofReal_ne_zero.mpr (finiteZetaUnitMass_pos F v.val (μ v)).ne'
    · rw [finiteProductClearedLocal, ite_eq_left hv]
      exact finiteZetaClearedDistribution_integerRing_unramified F v.val (μ v) (χ v) hv z
  · obtain ⟨f, C, _, hc, hI, _⟩ := exists_finiteMellinUnitTest F v.val (μ v) (χ v)
    refine ⟨f, C, hc, fun z ↦ ?_⟩
    rw [finiteProductClearedLocal, ite_eq_right hv]
    have he : finiteZetaContinuation F v.val (μ v) (χ v) f = fun _ ↦ C := by
      have han := finiteZetaContinuation_analytic_of_ramified F v.val (μ v) (χ v) hv f
      apply han.eq_of_eventuallyEq analyticOnNhd_const (z₀ := (1 : ℂ))
      filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
        (by norm_num : 0 < (1 : ℂ).re)] with w hw
      exact (finiteZetaContinuation_eq_integral F v.val (μ v) (χ v) f w hw).2.symm.trans (hI w hw)
    exact congrFun he z

omit [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ] in
/-- Separated archimedean and finite reference factors give a constant
normalized continuation on the actual S-local test space. -/
theorem sLocalEulerNormalizedMellin_const_of_separated (ω : PontryaginDual (K F S))
    (φ : 𝓢(mixedEmbedding.mixedSpace F, ℂ))
    (g : ∀ v : S, locallyConstantTests (L F S v)) (C : S → ℂ)
    (hφ : ∀ c : ℂ,
      (fun z ↦ archimedeanNumberFieldZeta F complexTamagawaAngularMeasure
        (sLocalRealArchParameters F S ω) (sLocalComplexArchParameters F S ω) z φ) =ᶠ[𝓝[≠] c]
        fun z ↦ (archimedeanNumberFieldZetaDenominator F
          (sLocalRealArchParameters F S ω) (sLocalComplexArchParameters F S ω) z)⁻¹)
    (hg : ∀ v z, finiteProductClearedLocal F S μ (sLocalFiniteZetaPhases F S ω) v (g v) z = C v) :
    sLocalEulerNormalizedMellin F S μ ω (sLocalBruhatPure F S φ (locallyConstantTestPiProduct g)) =
      fun _ ↦ ∏ v, C v := by
  let a := sLocalRealArchParameters F S ω
  let j := sLocalComplexArchParameters F S ω
  let χ := sLocalFiniteZetaPhases F S ω
  let f := sLocalBruhatPure F S φ (locallyConstantTestPiProduct g)
  let B := ∏ v, C v
  let N := sLocalEulerNormalizedMellin F S μ ω f
  let D := sLocalEulerDenominator F S ω
  let Da := archimedeanNumberFieldZetaDenominator F a j
  let Df := sLocalFiniteZetaDenominator F S χ
  have hDe (z : ℂ) : D z = Da z * Df z := rfl
  funext c
  obtain ⟨V, hV, hVn, he, _⟩ := sLocalEulerDenominator_exists_leadingFactor F S ω c
  have hne : ∀ᶠ z in 𝓝[≠] c, D z ≠ 0 := by
    have hV' : ∀ᶠ z in 𝓝 c, V z ≠ 0 := hV.continuousAt.eventually_ne hVn
    filter_upwards [he.filter_mono nhdsWithin_le_nhds, hV'.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with z hz hw hc
    change sLocalEulerDenominator F S ω z ≠ 0
    rw [hz]
    exact mul_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr hc)) hw
  have hval : N =ᶠ[𝓝[≠] c] fun _ ↦ B := by
    filter_upwards [hφ c, hne, sLocalEulerNormalizedMellin_eq_germ F S μ ω f c] with z hφz hz hn
    have hDa : Da z ≠ 0 := fun he ↦ hz (by rw [hDe, he, zero_mul])
    have hDf : Df z ≠ 0 := fun he ↦ hz (by rw [hDe, he, mul_zero])
    change N z = B
    rw [show N z = D z * sLocalProductZetaContinued F S μ ω a j f z from hn, hDe]
    simp only [f, sLocalProductZetaContinued, sLocalFiniteZetaSchwartzTest,
      sLocalBruhatContractFinite_pure, map_smul, smul_eq_mul]
    rw [show archimedeanNumberFieldZeta F complexTamagawaAngularMeasure a j z φ = (Da z)⁻¹ from hφz]
    have hfinite : sLocalFiniteZetaContinued F S μ χ z (locallyConstantTestPiProduct g) =
        (Df z)⁻¹ * B := by
      simp only [sLocalFiniteZetaContinued, smul_apply, smul_eq_mul, sLocalFiniteZetaCleared_piProduct]
      exact congrArg ((Df z)⁻¹ * ·) (Finset.prod_congr rfl fun v _ ↦ hg v z)
    change (Da z * Df z) * (sLocalFiniteZetaContinued F S μ χ z (locallyConstantTestPiProduct g) * (Da z)⁻¹) = B
    rw [hfinite]
    calc
      _ = (Da z * (Da z)⁻¹) * (Df z * (Df z)⁻¹) * B := by ring
      _ = _ := by rw [mul_inv_cancel₀ hDa, mul_inv_cancel₀ hDf, one_mul, one_mul]
  have hcont : ContinuousAt N c := (sLocalEulerNormalizedMellin_entire F S μ ω f c (mem_univ _)).continuousAt
  exact ((hcont.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE continuousAt_const).mp hval).eq_of_nhds

omit [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ] in
/-- One actual S-local test realizes the full Euler product. Its
pole-cleared Mellin continuation is a nonzero constant on the plane. -/
theorem exists_sLocalEulerNormalizedMellin_separated_constant (ω : PontryaginDual (K F S)) :
    ∃ (φ : 𝓢(mixedEmbedding.mixedSpace F, ℂ))
      (r : {v : InfinitePlace F // v.IsReal} → 𝓢(ℝ, ℂ))
      (k : {v : InfinitePlace F // v.IsComplex} → 𝓢(ℂ, ℂ))
      (g : ∀ v : S, locallyConstantTests (L F S v)) (C : ℂ), C ≠ 0 ∧
      (∀ x : mixedEmbedding.mixedSpace F, φ x = (∏ v, r v (x.1 v)) * ∏ v, k v (x.2 v)) ∧
      sLocalEulerNormalizedMellin F S μ ω (sLocalBruhatPure F S φ (locallyConstantTestPiProduct g)) = fun _ ↦ C := by
  let a := sLocalRealArchParameters F S ω
  let j := sLocalComplexArchParameters F S ω
  let χ := sLocalFiniteZetaPhases F S ω
  obtain ⟨φ, r, k, hsep, hφ⟩ := exists_archimedeanGammaProductTest_separated F a j
    (sLocalRealArchParameters_re F S ω) (sLocalComplexArchParameters_re F S ω)
  choose g C hC hg using exists_cleared_finite_reference F S μ χ
  let f := sLocalBruhatPure F S φ (locallyConstantTestPiProduct g)
  let B := ∏ v, C v
  refine ⟨φ, r, k, g, B, Finset.prod_ne_zero_iff.mpr (fun v _ ↦ hC v), hsep, ?_⟩
  exact sLocalEulerNormalizedMellin_const_of_separated F S μ ω φ g C hφ hg

omit [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ] in
/-- A pure finite-stage reference whose normalized continuation is a nonzero constant. -/
theorem exists_sLocalEulerNormalizedMellin_pure_constant (ω : PontryaginDual (K F S)) :
    ∃ (φ : 𝓢(mixedEmbedding.mixedSpace F, ℂ))
      (ψ : locallyConstantTests (∀ v : S, L F S v)) (C : ℂ), C ≠ 0 ∧
      sLocalEulerNormalizedMellin F S μ ω (sLocalBruhatPure F S φ ψ) = fun _ ↦ C := by
  obtain ⟨φ, _, _, g, C, hC, _, h⟩ := exists_sLocalEulerNormalizedMellin_separated_constant F S μ ω
  exact ⟨φ, locallyConstantTestPiProduct g, C, hC, h⟩

omit [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ] in
theorem exists_sLocalEulerNormalizedMellin_constant (ω : PontryaginDual (K F S)) :
    ∃ (f : sLocalBruhatImage F S) (C : ℂ), C ≠ 0 ∧
      sLocalEulerNormalizedMellin F S μ ω f = fun _ ↦ C := by
  obtain ⟨φ, ψ, C, hC, he⟩ := exists_sLocalEulerNormalizedMellin_pure_constant F S μ ω
  exact ⟨sLocalBruhatPure F S φ ψ, C, hC, he⟩

end

end Masullo
