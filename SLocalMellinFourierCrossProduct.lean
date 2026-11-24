import SLocalFourierPairing
import SLocalPairedMellinCovariance
import MellinFourierCrossProduct
import IdelicDoublingTransfer
import SLocalUnitHaarDensity
import HomogeneousThetaMellin

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped ENNReal NNReal NumberField

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]
variable (S : Finset (HeightOneSpectrum (𝓞 F)))

private abbrev E := sLocalBruhatImage F S
private abbrev G := (SAdeles F S)ˣ
private abbrev K := SLocalThetaNormOne F S

attribute [local instance] sLocalZetaUnfolding_classMeasurable sLocalZetaUnfolding_classBorel
  sLocalZetaUnfolding_idelesMeasurable sLocalZetaUnfolding_idelesBorel

variable [MeasurableSpace (InfiniteAdeleRing F)] [BorelSpace (InfiniteAdeleRing F)]
  [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)]

local instance : BorelSpace (SAdeles F S) := by
  letI : SecondCountableTopology (InfiniteAdeleRing F) :=
    (infiniteAdeleMixedHomeomorph F).isEmbedding.secondCountableTopology
  letI (v : HeightOneSpectrum (𝓞 F)) :
      SecondCountableTopology (v.adicCompletion F) := finitePlace_secondCountable F v
  infer_instance

private abbrev η := sLocalAdditiveProduct F S (fun v ↦ additiveHaarDifferent F v.val)

private def zetaMonoidWeight (ω : PontryaginDual (K F S)) (z : ℂ) : G F S →* ℂ where
  toFun u := sLocalZetaWeight F S ω z (QuotientGroup.mk u)
  map_one' := by
    change sLocalZetaWeight F S ω z 1 = 1
    have h : sLocalZetaSplit F S (0, 1) = 1 := by
      change (QuotientGroup.mk' (sUnitImage F S)) ((sLocalExpSection F S) 1) * 1 = 1
      rw [map_one, map_one]
      exact one_mul (1 : SIdeleQuotient F S)
    rw [← h, sLocalZetaWeight_split]
    simp
  map_mul' u v := by
    change sLocalZetaWeight F S ω z (QuotientGroup.mk (u*v)) =
      sLocalZetaWeight F S ω z (QuotientGroup.mk u) * sLocalZetaWeight F S ω z (QuotientGroup.mk v)
    rw [QuotientGroup.mk_mul, sLocalZetaWeight_mul]

private theorem integral_mul_norm_on_units (μ : Measure (G F S)) (c : ℝ≥0∞)
    (hDensity : Measure.map (Units.val : G F S → SAdeles F S)
      (μ.withDensity (fun x ↦ ENNReal.ofReal (sLocalIdeleNorm F S x))) = c • η F S)
    (h : SAdeles F S → ℂ) (hh : Measurable h) :
    (∫ x, (sLocalIdeleNorm F S x : ℂ) * h x.val ∂μ) =
      c.toReal • ∫ x, h x ∂η F S := by
  let W (u : G F S) : ℝ≥0 := (sLocalIdeleNorm F S u).toNNReal
  have hm : Measurable W := (sLocalIdeleNorm_continuous F S).measurable.real_toNNReal
  have hu : Measurable (Units.val : G F S → SAdeles F S) := Units.continuous_val.measurable
  rw [← integral_smul_measure, ← hDensity, integral_map hu.aemeasurable hh.aestronglyMeasurable]
  change _ = ∫ x, h x.val ∂μ.withDensity (fun x ↦ (W x : ℝ≥0∞))
  rw [integral_withDensity_eq_integral_smul hm]
  apply integral_congr_ae
  exact .of_forall fun x ↦ by
    change _ = (W x : ℝ) • h x.val
    rw [Complex.real_smul]
    have hn := sLocalIdeleNorm_positive F S x
    rw [show (W x : ℝ) = sLocalIdeleNorm F S x from Real.coe_toNNReal _ hn.le]

/-- On the critical strip the paired test values satisfy the cross-product
form of the local functional equation under the additive-to-multiplicative
Haar comparison. This comparison is stated as an equality of actual measures. -/
theorem sLocalMellin_fourier_crossProduct_of_density
    (μ : Measure (G F S)) [μ.IsHaarMeasure] [SigmaFinite μ] [SFinite (η F S)]
    (c : ℝ≥0∞)
    (hDensity : Measure.map (Units.val : G F S → SAdeles F S)
      (μ.withDensity (fun x ↦ ENNReal.ofReal (sLocalIdeleNorm F S x))) = c • η F S)
    (ω : PontryaginDual (K F S)) (z : ℂ) (hr : 0 < z.re) (hl : z.re < 1)
    (f g : E F S) :
    sLocalIdelicZetaIntegral F S μ ω f z *
        sLocalIdelicZetaIntegral F S μ ω⁻¹ (sLocalSelectedFourier F S g) (1-z) =
      sLocalIdelicZetaIntegral F S μ ω g z *
        sLocalIdelicZetaIntegral F S μ ω⁻¹ (sLocalSelectedFourier F S f) (1-z) := by
  letI := sLocalIdeles_secondCountable F S
  obtain ⟨ν, hνHaar, hν⟩ := sLocalClassHaar_exists_weil F S μ
  letI := hνHaar
  let χ := (zetaMonoidWeight F S ω⁻¹ (1-z)).toHomUnits
  let r (h : E F S) (x : G F S) := (sLocalIdeleNorm F S x : ℂ) *
    sLocalBruhatRestriction F S h.val x.val
  let l (h : E F S) (x : G F S) :=
    sLocalBruhatRestriction F S (sLocalSelectedFourier F S h).val x.val
  have hs : 0 < (1-z).re := by simpa [Complex.sub_re, sub_pos] using hl
  have hw (h : E F S) :
      (fun x ↦ ((χ x : ℂ)⁻¹) * r h x) = sLocalIdelicZetaIntegrand F S ω z h := by
    funext x
    change (sLocalZetaWeight F S ω⁻¹ (1-z) (QuotientGroup.mk x))⁻¹ *
        ((sLocalIdeleNorm F S x : ℂ) * sLocalBruhatRestriction F S h.val x.val) =
      sLocalZetaWeight F S ω z (QuotientGroup.mk x) * sLocalBruhatRestriction F S h.val x.val
    rw [← sLocalZetaWeight_inverse_argument, ← mul_assoc,
      mul_comm (sLocalZetaWeight F S ω⁻¹ (1-z) (QuotientGroup.mk x)⁻¹),
      ← sLocalClassModulus_mk, sLocalZetaWeight_reflected_dilation]
  have hf : Integrable (fun x ↦ ((χ x : ℂ)⁻¹) * r f x) μ := by
    rw [hw]
    exact (sLocalIdelicZeta_integrable_eq_theta F S μ ν hν ω f z hr).1
  have hg : Integrable (fun x ↦ ((χ x : ℂ)⁻¹) * r g x) μ := by
    rw [hw]
    exact (sLocalIdelicZeta_integrable_eq_theta F S μ ν hν ω g z hr).1
  have hf' : Integrable (fun x ↦ (χ x : ℂ) * l f x) μ :=
    (sLocalIdelicZeta_integrable_eq_theta F S μ ν hν ω⁻¹ (sLocalSelectedFourier F S f) (1-z) hs).1
  have hg' : Integrable (fun x ↦ (χ x : ℂ) * l g x) μ :=
    (sLocalIdelicZeta_integrable_eq_theta F S μ ν hν ω⁻¹ (sLocalSelectedFourier F S g) (1-z) hs).1
  have hPair (u : G F S) (a b : E F S) :
      (∫ x, r a x * l b (u*x) ∂μ) =
        c.toReal • ∫ y, sLocalBruhatRestriction F S a.val y *
          sLocalBruhatRestriction F S (sLocalSelectedFourier F S b).val (u.val*y) ∂η F S := by
    let H y := sLocalBruhatRestriction F S a.val y *
      sLocalBruhatRestriction F S (sLocalSelectedFourier F S b).val (u.val*y)
    have hH : Continuous H := (sLocalBruhatRestriction_continuous F S a.val).mul
      ((sLocalBruhatRestriction_continuous F S (sLocalSelectedFourier F S b).val).comp
        (continuous_const.mul continuous_id))
    calc
      _ = ∫ x, (sLocalIdeleNorm F S x : ℂ) * H x.val ∂μ := by
        apply integral_congr_ae
        exact .of_forall fun x ↦ mul_assoc _ _ _
      _ = _ := integral_mul_norm_on_units F S μ c hDensity H hH.measurable
  have hpair (u : G F S) : (∫ x, r f x * l g (u*x) ∂μ) = ∫ x, r g x * l f (u*x) ∂μ := by
    rw [hPair, hPair, sLocalSelectedFourier_pairing]
  have h := mellin_fourier_crossProduct μ χ (r f) (r g) (l f) (l g) hf hg hf' hg' hpair
  rw [hw, hw] at h
  exact h

/-- The actual S-local Mellin integrals and their reflected Fourier
partners satisfy the test-independent cross-product identity. -/
theorem sLocalMellin_fourier_crossProduct
    (μ : Measure (G F S)) [μ.IsHaarMeasure]
    (ω : PontryaginDual (K F S)) (z : ℂ) (hr : 0 < z.re) (hl : z.re < 1)
    (f g : E F S) :
    sLocalIdelicZetaIntegral F S μ ω f z *
        sLocalIdelicZetaIntegral F S μ ω⁻¹ (sLocalSelectedFourier F S g) (1-z) =
      sLocalIdelicZetaIntegral F S μ ω g z *
        sLocalIdelicZetaIntegral F S μ ω⁻¹ (sLocalSelectedFourier F S f) (1-z) := by
  letI := sLocalIdeles_locallyCompact F S
  letI := sLocalIdeles_secondCountable F S
  letI : SecondCountableTopology (InfiniteAdeleRing F) :=
    (infiniteAdeleMixedHomeomorph F).isEmbedding.secondCountableTopology
  letI (v : HeightOneSpectrum (𝓞 F)) :
      SecondCountableTopology (v.adicCompletion F) := finitePlace_secondCountable F v
  letI (v : HeightOneSpectrum (𝓞 F)) :
      LocallyCompactSpace (v.adicCompletion F) := finitePlace_locallyCompact F v
  letI : SecondCountableTopology (SAdeles F S) :=
    inferInstanceAs (SecondCountableTopology (InfiniteAdeleRing F × ((v : S) → v.val.adicCompletion F)))
  letI : LocallyCompactSpace (SAdeles F S) :=
    inferInstanceAs (LocallyCompactSpace (InfiniteAdeleRing F × ((v : S) → v.val.adicCompletion F)))
  letI : (η F S).IsAddHaarMeasure := sLocalSelectedAdditive_isHaar F S
  obtain ⟨c, _, hDensity⟩ := sLocalSelectedAdditive_density F S μ
  exact sLocalMellin_fourier_crossProduct_of_density F S μ (c : ℝ≥0∞) hDensity ω z hr hl f g

variable [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]
  [∀ v : S, MeasurableSpace (v.val.adicCompletion F)ˣ]
  [∀ v : S, BorelSpace (v.val.adicCompletion F)ˣ]

private abbrev continuedMellin
    (μ : ∀ v : S, Measure (v.val.adicCompletion F)ˣ)
    [∀ v : S, (μ v).IsHaarMeasure] [∀ v : S, SigmaFinite (μ v)]
    (ω : PontryaginDual (K F S)) (f : E F S) :=
  sLocalProductZetaContinued F S μ ω (sLocalRealArchParameters F S ω)
    (sLocalComplexArchParameters F S ω) f

/-- The two local Mellin transforms and their reflected Fourier partners
satisfy the cross-product identity as meromorphic germs at every center. -/
theorem sLocalContinuedMellin_fourier_crossProduct
    (μ : ∀ v : S, Measure (v.val.adicCompletion F)ˣ)
    [∀ v : S, (μ v).IsHaarMeasure] [∀ v : S, SigmaFinite (μ v)]
    (ω : PontryaginDual (K F S)) (f g : E F S) (c : ℂ) :
    (fun z ↦ continuedMellin F S μ ω f z *
      continuedMellin F S μ ω⁻¹ (sLocalSelectedFourier F S g) (1 - z)) =ᶠ[𝓝[≠] c]
    (fun z ↦ continuedMellin F S μ ω g z *
      continuedMellin F S μ ω⁻¹ (sLocalSelectedFourier F S f) (1 - z)) := by
  let ηM := sLocalZetaProductMeasure F S μ (archimedeanMultiplicativeHaar F)
  letI : ηM.IsHaarMeasure :=
    sLocalZetaProductMeasure_isHaar F S μ (archimedeanMultiplicativeHaar F)
  have hM (ξ : PontryaginDual (K F S)) (a : E F S) :
      Meromorphic (continuedMellin F S μ ξ a) :=
    (sLocalIdelicZeta_meromorphic_continuation F S μ ξ a).1
  have hR (a : E F S) :
      Meromorphic (fun z ↦ continuedMellin F S μ ω⁻¹ (sLocalSelectedFourier F S a) (1 - z)) := by
    intro z
    exact (hM ω⁻¹ (sLocalSelectedFourier F S a) (1 - z)).comp_analyticAt
      (analyticAt_const.fun_sub analyticAt_id)
  refine boundedPoleMellinSpace_unique_germs (D := {z : ℂ | 0 < z.re ∧ z.re < 1})
    ((isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const))
    ⟨1 / 2, by simp only [mem_ofPred_eq, Complex.div_ofNat_re, Complex.one_re]; norm_num⟩
    (fun z ↦ (hM ω f z).mul (hR g z))
    (fun z ↦ (hM ω g z).mul (hR f z)) ?_ c
  intro z hz
  have hr : 0 < (1 - z).re := by simpa [Complex.sub_re, sub_pos] using hz.2
  have he (ξ : PontryaginDual (K F S)) (a : E F S) (w : ℂ) (hw : 0 < w.re) :
      continuedMellin F S μ ξ a w = sLocalIdelicZetaIntegral F S ηM ξ a w :=
    (sLocalIdelicZeta_meromorphic_continuation F S μ ξ a).2 hw
  change continuedMellin F S μ ω f z *
      continuedMellin F S μ ω⁻¹ (sLocalSelectedFourier F S g) (1 - z) =
    continuedMellin F S μ ω g z *
      continuedMellin F S μ ω⁻¹ (sLocalSelectedFourier F S f) (1 - z)
  rw [he _ _ z hz.1, he _ _ z hz.1, he _ _ (1 - z) hr, he _ _ (1 - z) hr]
  exact sLocalMellin_fourier_crossProduct F S ηM ω z hz.1 hz.2 f g

end

end Masullo
