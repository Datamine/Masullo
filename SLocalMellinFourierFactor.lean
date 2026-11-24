import SLocalMellinFourierCrossProduct
import SLocalEulerReference
import SLocalFourierInversion
import SLocalEntireStrip

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped NumberField

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]
variable (S : Finset (HeightOneSpectrum (𝓞 F)))

private abbrev E := sLocalBruhatImage F S
private abbrev K := SLocalThetaNormOne F S

variable [MeasurableSpace (InfiniteAdeleRing F)] [BorelSpace (InfiniteAdeleRing F)]
  [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]
  [∀ v : S, MeasurableSpace (v.val.adicCompletion F)ˣ]
  [∀ v : S, BorelSpace (v.val.adicCompletion F)ˣ]
  (μ : ∀ v : S, Measure (v.val.adicCompletion F)ˣ)
  [∀ v : S, (μ v).IsHaarMeasure] [∀ v : S, SigmaFinite (μ v)]

attribute [local instance] sLocalZetaUnfolding_idelesMeasurable sLocalZetaUnfolding_idelesBorel
  sLocalZetaUnfolding_classMeasurable sLocalZetaUnfolding_classBorel

private abbrev N (ω : PontryaginDual (K F S)) (f : E F S) :=
  sLocalEulerNormalizedMellin F S μ ω f

private abbrev R (ω : PontryaginDual (K F S)) (f : E F S) (z : ℂ) :=
  N F S μ ω⁻¹ (sLocalSelectedFourier F S f) (1 - z)

private abbrev productHaar :=
  sLocalZetaProductMeasure F S μ (archimedeanMultiplicativeHaar F)

omit [MeasurableSpace (InfiniteAdeleRing F)] [BorelSpace (InfiniteAdeleRing F)]
  [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)] in
theorem normalizedMellin_eq_mul_idelic
    (ω : PontryaginDual (K F S)) (f : E F S) (z : ℂ) (hz : 0 < z.re) :
    N F S μ ω f z = sLocalEulerDenominator F S ω z *
      sLocalIdelicZetaIntegral F S (productHaar F S μ) ω f z := by
  have hreg : z ∈ sLocalMellinRegularSet F S ω := by
    rw [sLocalMellinRegularSet_iff_noEulerPole, ← not_lt, sLocalEulerFactor_order_lt_zero_iff]
    exact sLocalEulerDenominator_ne_zero_of_pos F S ω hz
  exact (normalizedMellin_eq_euler_mul_regular F S μ ω f z hreg).trans
    (congrArg (sLocalEulerDenominator F S ω z * ·)
      ((sLocalIdelicZeta_meromorphic_continuation F S μ ω f).2 hz))

omit [MeasurableSpace (InfiniteAdeleRing F)] [BorelSpace (InfiniteAdeleRing F)]
  [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ] in
private theorem normalizedFourier_analytic (ω : PontryaginDual (K F S)) (f : E F S) :
    AnalyticOnNhd ℂ (R F S μ ω f) univ := by
  intro z _
  exact (sLocalEulerNormalizedMellin_entire F S μ ω⁻¹ (sLocalSelectedFourier F S f)
    (1 - z) trivial).comp (analyticAt_const.fun_sub analyticAt_id)

private theorem normalizedMellin_fourier_cross
    (ω : PontryaginDual (K F S)) (f g : E F S) :
    N F S μ ω f * R F S μ ω g = N F S μ ω g * R F S μ ω f := by
  letI : (productHaar F S μ).IsHaarMeasure :=
    sLocalZetaProductMeasure_isHaar F S μ (archimedeanMultiplicativeHaar F)
  have hN := sLocalEulerNormalizedMellin_entire F S μ ω
  have hR := normalizedFourier_analytic F S μ ω
  let U := {z : ℂ | 0 < z.re ∧ z.re < 1}
  have hU : IsOpen U := (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt Complex.continuous_re continuous_const)
  have hs : (1 / 2 : ℂ) ∈ U := by
    change 0 < (1 / 2 : ℂ).re ∧ (1 / 2 : ℂ).re < 1
    norm_num [Complex.div_ofNat_re]
  apply (hN f |>.mul (hR g)).eq_of_eventuallyEq (hN g |>.mul (hR f)) (z₀ := (1 / 2 : ℂ))
  filter_upwards [hU.mem_nhds hs] with z hz
  have hr : 0 < (1 - z).re := by simpa [Complex.sub_re, sub_pos] using hz.2
  have he := normalizedMellin_eq_mul_idelic F S μ
  change N F S μ ω f z * N F S μ ω⁻¹ (sLocalSelectedFourier F S g) (1 - z) =
    N F S μ ω g z * N F S μ ω⁻¹ (sLocalSelectedFourier F S f) (1 - z)
  rw [he _ _ z hz.1, he _ _ z hz.1, he _ _ _ hr, he _ _ _ hr]
  have h := sLocalMellin_fourier_crossProduct F S (productHaar F S μ) ω z hz.1 hz.2 f g
  linear_combination
    (sLocalEulerDenominator F S ω z * sLocalEulerDenominator F S ω⁻¹ (1 - z)) * h

omit [MeasurableSpace (InfiniteAdeleRing F)] [BorelSpace (InfiniteAdeleRing F)]
  [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]
  [∀ v : S, MeasurableSpace (v.val.adicCompletion F)ˣ]
  [∀ v : S, BorelSpace (v.val.adicCompletion F)ˣ] in
theorem sLocalSelectedFourier_surjective : Surjective (sLocalSelectedFourier F S) := by
  intro a
  let d : ℂ := (sLocalFourierTailVolume F S).toReal
  have hd : d ≠ 0 := Complex.ofReal_ne_zero.mpr (sLocalFourierTailVolume_pos F S).ne'
  obtain ⟨f, hf⟩ := sLocalFourierCompression_surjective F S (d • a)
  refine ⟨f, ?_⟩
  change d⁻¹ • sLocalFourierCompression F S f = a
  rw [hf, smul_smul, inv_mul_cancel₀ hd, one_smul]

/-- After division by the respective Euler factors, the local functional
equation has a single test-independent, nowhere-vanishing entire multiplier. -/
theorem exists_sLocalNormalizedMellin_fourierFactor (ω : PontryaginDual (K F S)) :
    ∃ A : ℂ → ℂ, AnalyticOnNhd ℂ A univ ∧ (∀ z, A z ≠ 0) ∧
      ∀ (f : E F S) (z : ℂ), R F S μ ω f z = A z * N F S μ ω f z := by
  obtain ⟨g, C, hC, hg⟩ := exists_sLocalEulerNormalizedMellin_constant F S μ ω
  let A : ℂ → ℂ := fun z ↦ C⁻¹ * R F S μ ω g z
  have he (f : E F S) (z : ℂ) : R F S μ ω f z = A z * N F S μ ω f z := by
    have h := congrFun (normalizedMellin_fourier_cross F S μ ω g f) z
    change N F S μ ω g z * R F S μ ω f z = N F S μ ω f z * R F S μ ω g z at h
    rw [show N F S μ ω g z = C from congrFun hg z] at h
    change _ = C⁻¹ * R F S μ ω g z * N F S μ ω f z
    calc
      _ = C⁻¹ * (C * R F S μ ω f z) := by rw [← mul_assoc, inv_mul_cancel₀ hC, one_mul]
      _ = _ := by rw [h]; ring
  refine ⟨A, analyticOnNhd_const.mul (normalizedFourier_analytic F S μ ω g), ?_, he⟩
  obtain ⟨b, B, hB, hb⟩ := exists_sLocalEulerNormalizedMellin_constant F S μ ω⁻¹
  obtain ⟨a, ha⟩ := sLocalSelectedFourier_surjective F S b
  intro z hz
  have h := he a z
  rw [hz, zero_mul] at h
  change N F S μ ω⁻¹ (sLocalSelectedFourier F S a) (1 - z) = 0 at h
  rw [ha] at h
  exact hB ((congrFun hb (1 - z)).symm.trans h)

/-- The paired integrals glue on the critical strip with the quotient
of the two Euler denominators and the entire Fourier multiplier. -/
theorem exists_sLocalMellin_fourier_gluing (ω : PontryaginDual (K F S)) :
    ∃ A : ℂ → ℂ, AnalyticOnNhd ℂ A univ ∧ (∀ z, A z ≠ 0) ∧
      (∀ (f : E F S) (z : ℂ), R F S μ ω f z = A z * N F S μ ω f z) ∧
      ∀ (f : E F S) (z : ℂ), 0 < z.re → z.re < 1 →
      sLocalIdelicZetaIntegral F S (productHaar F S μ) ω f z =
        (sLocalEulerDenominator F S ω⁻¹ (1 - z) /
          (A z * sLocalEulerDenominator F S ω z)) *
        sLocalIdelicZetaIntegral F S (productHaar F S μ) ω⁻¹ (sLocalSelectedFourier F S f) (1 - z) := by
  obtain ⟨A, hA, hn, he⟩ := exists_sLocalNormalizedMellin_fourierFactor F S μ ω
  refine ⟨A, hA, hn, he, fun f z hz hr ↦ ?_⟩
  have hr' : 0 < (1 - z).re := by simpa [Complex.sub_re, sub_pos] using hr
  have h := he f z
  change N F S μ ω⁻¹ (sLocalSelectedFourier F S f) (1 - z) =
    A z * N F S μ ω f z at h
  rw [normalizedMellin_eq_mul_idelic F S μ _ _ _ hr',
    normalizedMellin_eq_mul_idelic F S μ _ _ _ hz, ← mul_assoc] at h
  have hD := mul_ne_zero (hn z) (sLocalEulerDenominator_ne_zero_of_pos F S ω hz)
  rw [div_mul_eq_mul_div, h, mul_comm, mul_div_cancel_right₀ _ hD]

private abbrev Z (ω : PontryaginDual (K F S)) (f : E F S) :=
  sLocalProductZetaContinued F S μ ω (sLocalRealArchParameters F S ω)
    (sLocalComplexArchParameters F S ω) f

/-- The S-local functional equation with the entire epsilon factor
determined by the selected Fourier transform and an Euler reference test.
The factor has the claimed pole bound, with multiplicities. -/
theorem exists_sLocalMellin_fourier_functionalEquation (ω : PontryaginDual (K F S)) :
    ∃ ε : ℂ → ℂ, AnalyticOnNhd ℂ ε univ ∧ (∀ z, ε z ≠ 0) ∧
      (∀ (f : E F S) (z : ℂ), 0 < z.re → z.re < 1 →
        sLocalIdelicZetaIntegral F S (productHaar F S μ) ω f z =
          sLocalExplicitTateFactor F S ω ε z *
            sLocalIdelicZetaIntegral F S (productHaar F S μ) ω⁻¹
              (sLocalSelectedFourier F S f) (1 - z)) ∧
      (∀ (f : E F S) (z : ℂ), N F S μ ω f z = ε z * R F S μ ω f z) ∧
      (∀ (f : E F S) (c : ℂ), Z F S μ ω f =ᶠ[𝓝[≠] c] fun z ↦
        sLocalExplicitTateFactor F S ω ε z *
          Z F S μ ω⁻¹ (sLocalSelectedFourier F S f) (1 - z)) ∧
      (∀ (f : E F S) (c : ℂ),
        min (meromorphicOrderAt (sLocalExplicitTateFactor F S ω ε) c) 0 ≤
          meromorphicOrderAt (Z F S μ ω f) c) := by
  obtain ⟨A, hA, hAn, hAR, hGlue⟩ := exists_sLocalMellin_fourier_gluing F S μ ω
  let ε z := (A z)⁻¹
  have hε : ∀ z, AnalyticAt ℂ ε z := fun z ↦ (hA z trivial).inv (hAn z)
  have hεn : ∀ z, ε z ≠ 0 := fun z ↦ inv_ne_zero (hAn z)
  have hStrip (f : E F S) (z : ℂ) (hz : 0 < z.re) (hr : z.re < 1) :
      sLocalIdelicZetaIntegral F S (productHaar F S μ) ω f z =
        sLocalExplicitTateFactor F S ω ε z *
          sLocalIdelicZetaIntegral F S (productHaar F S μ) ω⁻¹
            (sLocalSelectedFourier F S f) (1 - z) := by
    rw [hGlue f z hz hr]
    unfold sLocalExplicitTateFactor sLocalEulerFactor ε
    rw [div_eq_mul_inv, mul_inv]
    ring
  refine ⟨ε, fun z _ ↦ hε z, hεn, hStrip, ?_, ?_, ?_⟩
  · intro f z
    rw [hAR]
    change _ = (A z)⁻¹ * (A z * _)
    rw [← mul_assoc, inv_mul_cancel₀ (hAn z), one_mul]
  · intro f c
    let g := sLocalSelectedFourier F S f
    have hM (ξ : PontryaginDual (K F S)) (a : E F S) : Meromorphic (Z F S μ ξ a) :=
      (sLocalIdelicZeta_meromorphic_continuation F S μ ξ a).1
    have hR : Meromorphic (fun z ↦ Z F S μ ω⁻¹ g (1 - z)) := fun z ↦
      (hM ω⁻¹ g (1 - z)).comp_analyticAt (analyticAt_const.fun_sub analyticAt_id)
    have hρ := sLocalExplicitTateFactor_meromorphic F S ω ε hε
    refine boundedPoleMellinSpace_unique_germs (D := {z : ℂ | 0 < z.re ∧ z.re < 1})
      ((isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt Complex.continuous_re continuous_const))
      ⟨1 / 2, by change 0 < (1 / 2 : ℂ).re ∧ (1 / 2 : ℂ).re < 1
                 norm_num [Complex.div_ofNat_re]⟩
      (hM ω f) (fun z ↦ (hρ z).mul (hR z)) ?_ c
    intro z hz
    have hr : 0 < (1 - z).re := by simpa [Complex.sub_re, sub_pos] using hz.2
    change Z F S μ ω f z = sLocalExplicitTateFactor F S ω ε z * Z F S μ ω⁻¹ g (1 - z)
    exact ((sLocalIdelicZeta_meromorphic_continuation F S μ ω f).2 hz.1).trans
      ((hStrip f z hz.1 hz.2).trans
        (congrArg (sLocalExplicitTateFactor F S ω ε z * ·)
          ((sLocalIdelicZeta_meromorphic_continuation F S μ ω⁻¹ g).2 hr).symm))
  · intro f c
    rw [show min (meromorphicOrderAt (sLocalExplicitTateFactor F S ω ε) c) 0 =
        min (meromorphicOrderAt (sLocalEulerFactor F S ω) c) 0 from
      sLocalEulerRatio_negativeDivisor F S ω ω⁻¹ hε hεn c]
    exact (min_le_left _ _).trans (sLocalZeta_poleOrder_le_euler F S μ ω f c)

/-- The corrected principal-part formula uses the actual test-level
functional equation. The leading eigendistribution is the reflected,
Euler-cleared zeta value multiplied by the same entire epsilon factor. -/
theorem sLocalPrincipalParts_reflected (ω : PontryaginDual (K F S)) (c : ℂ)
    (hc : sLocalEulerPoleLattices F S ω c) :
    ∃ ε V : ℂ → ℂ, AnalyticOnNhd ℂ ε univ ∧ (∀ z, ε z ≠ 0) ∧
      (∀ (f : E F S) (z : ℂ), N F S μ ω f z = ε z * R F S μ ω f z) ∧
      AnalyticAt ℂ V c ∧
      let m := sLocalPoleCount F S ω c
      let D := sLocalEulerLeadingDenominator F S ω c
      let Δ : E F S →L[ℂ] ℂ := D • sLocalLaurentCoeff F S μ ω c m
      meromorphicOrderAt (sLocalExplicitTateFactor F S ω ε) c = -(m : WithTop ℤ) ∧
      ((fun z ↦ (z - c)^m * sLocalExplicitTateFactor F S ω ε z) =ᶠ[𝓝[≠] c] V) ∧
      V c = ε c * sLocalEulerDenominator F S ω⁻¹ (1 - c) / D ∧
      (∀ f : E F S, Δ f = ε c * R F S μ ω f c) ∧
      Δ ≠ 0 ∧
      (∀ (u : (SAdeles F S)ˣ) (f : E F S),
        Δ (sLocalBruhatLeftTranslate F S u f) =
          sLocalZetaWeight F S ω c (QuotientGroup.mk u) * Δ f) ∧
      (∀ f : E F S, sLocalLaurentCoeff F S μ ω c m f = D⁻¹ * Δ f) ∧
      (∀ (f : E F S) (k : ℕ), k ≤ m →
        sLocalLaurentCoeff F S μ ω c k f =
          ∑ j ∈ Finset.range (m - k + 1), taylorCoeff V c j *
            taylorCoeff (fun z ↦ Z F S μ ω⁻¹ (sLocalSelectedFourier F S f) (1 - z))
              c (m - k - j)) := by
  obtain ⟨e, he, hen, _, hNorm, hGerm, _⟩ :=
    exists_sLocalMellin_fourier_functionalEquation F S μ ω
  let m := sLocalPoleCount F S ω c
  let D := sLocalEulerLeadingDenominator F S ω c
  let Δ : E F S →L[ℂ] ℂ := D • sLocalLaurentCoeff F S μ ω c m
  obtain ⟨U, _, hUn, _, hUD⟩ := sLocalEulerDenominator_exists_leadingFactor F S ω c
  have hD : D ≠ 0 := fun h ↦ hUn (hUD.trans h)
  have hΔ (f : E F S) : Δ f = N F S μ ω f c := by
    change D * sLocalLaurentCoeff F S μ ω c m f = _
    rw [sLocalLaurentCoeff_top_localProduct F S μ ω f c, ← mul_assoc, mul_inv_cancel₀ hD, one_mul]
  have hAll (f : E F S) := sLocalLaurentCoeff_of_reflected_pair F S μ ω f
    (sLocalSelectedFourier F S f) e c hc (he c trivial) (hGerm f c)
  obtain ⟨V, hV, hVG, hVc, _⟩ := hAll 0
  refine ⟨e, V, he, hen, hNorm, hV,
    sLocalExplicitTateFactor_order_eq_neg_count F S ω e (fun z ↦ he z trivial) hen hc,
    hVG, hVc, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun f ↦ (hΔ f).trans (hNorm f c)
  · obtain ⟨g, C, hC, hg⟩ := exists_sLocalEulerNormalizedMellin_constant F S μ ω
    intro h
    apply hC
    change Δ = 0 at h
    exact (congrFun hg c).symm.trans ((hΔ g).symm.trans
      (congrArg (fun L : E F S →L[ℂ] ℂ ↦ L g) h))
  · intro u f
    change D * sLocalLaurentCoeff F S μ ω c m (sLocalBruhatLeftTranslate F S u f) =
      _ * (D * sLocalLaurentCoeff F S μ ω c m f)
    rw [show m = sLocalAllowedPoleOrder F S ω c from (sLocalAllowedPoleOrder_eq_count F S ω c).symm,
      sLocalLaurentCoeff_top_translate, mul_left_comm]
  · intro f
    change _ = D⁻¹ * (D * _)
    rw [← mul_assoc, inv_mul_cancel₀ hD, one_mul]
    rfl
  · intro f k hk
    obtain ⟨V', hV', hVG', _, hK⟩ := hAll f
    change sLocalLaurentCoeff F S μ ω c k f =
      ∑ j ∈ Finset.range (m - k + 1), taylorCoeff V c j * _ at ⊢
    rw [hK k hk]
    have hVV' := (hV.continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
      hV'.continuousAt).mp (hVG.symm.trans hVG')
    simp_rw [taylorCoeff_congr hVV']
    rfl

/-- The paired Schwartz–Bergman profiles satisfying a given strip equation. -/
def sLocalBergmanGluing (ρ : ℂ → ℂ) :
    Submodule ℂ (SchwartzBergman (Ioi (0 : ℝ)) × SchwartzBergman (Iio (1 : ℝ))) where
  carrier := {p | ∀ z : ℂ, 0 < z.re → z.re < 1 → p.1.val z = ρ z * p.2.val z}
  zero_mem' := by
    intro z _ _
    change 0 = ρ z * 0
    rw [mul_zero]
  add_mem' := by
    intro p q hp hq z hz hr
    change p.1.val z + q.1.val z = ρ z * (p.2.val z + q.2.val z)
    rw [hp z hz hr, hq z hz hr, mul_add]
  smul_mem' := by
    intro b p hp z hz hr
    change b * p.1.val z = ρ z * (b * p.2.val z)
    rw [hp z hz hr, mul_left_comm]

theorem sLocalBergmanGluing_isClosed (ρ : ℂ → ℂ) :
    IsClosed (sLocalBergmanGluing ρ).carrier := by
  change IsClosed {p : SchwartzBergman (Ioi (0 : ℝ)) × SchwartzBergman (Iio (1 : ℝ)) |
    ∀ z : ℂ, 0 < z.re → z.re < 1 → p.1.val z = ρ z * p.2.val z}
  simp only [ofPred_forall]
  refine isClosed_iInter fun z ↦ isClosed_iInter fun hz ↦ isClosed_iInter fun hr ↦ ?_
  exact isClosed_eq
    ((bergman_continuous_evaluation isOpen_Ioi ordConnected_Ioi z hz).comp continuous_fst)
    (continuous_const.mul
      ((bergman_continuous_evaluation isOpen_Iio ordConnected_Iio z hr).comp continuous_snd))

private theorem bergman_poleCancellation_isClosed {I : Set ℝ}
    (hI : IsOpen I) (hInt : OrdConnected I) (ρ : ℂ → ℂ) (s : ℂ) (hs : s.re ∈ I)
    (hρ : MeromorphicAt ρ s) :
    IsClosed {b : SchwartzBergman I | 0 ≤ meromorphicOrderAt (ρ * b.val) s} := by
  have hb (b : SchwartzBergman I) : AnalyticAt ℂ b.val s :=
    b.property.2.1.analyticAt ((hI.preimage Complex.continuous_re).mem_nhds hs)
  cases h : meromorphicOrderAt ρ s with
  | top =>
    convert isClosed_univ using 1
    ext b
    simp [meromorphicOrderAt_mul hρ (hb b).meromorphicAt, h]
  | coe k =>
    by_cases hk : 0 ≤ k
    · convert isClosed_univ using 1
      ext b
      simp only [mem_ofPred_eq, mem_univ, iff_true]
      rw [meromorphicOrderAt_mul hρ (hb b).meromorphicAt, h]
      exact add_nonneg (WithTop.coe_nonneg.mpr hk) (hb b).meromorphicOrderAt_nonneg
    · let N := (-k).toNat
      have hN : (N : ℤ) = -k := Int.toNat_of_nonneg (by omega)
      have he (b : SchwartzBergman I) :
          (0 ≤ meromorphicOrderAt (ρ * b.val) s) ↔
            ∀ n < N, iteratedDeriv n b.val s = 0 := by
        rw [← natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hb b),
          meromorphicOrderAt_mul hρ (hb b).meromorphicAt, h, (hb b).meromorphicOrderAt_eq]
        cases hord : analyticOrderAt b.val s with
        | top => simp
        | coe m =>
          rw [show (↑m : ℕ∞) = (m : ENat) from rfl, ENat.map_natCast, ← WithTop.coe_add]
          norm_cast
          omega
      have hset : {b : SchwartzBergman I | 0 ≤ meromorphicOrderAt (ρ * b.val) s} =
          ⋂ (n : ℕ) (_ : n < N), {b : SchwartzBergman I | iteratedDeriv n b.val s = 0} := by
        ext b
        simp only [mem_ofPred_eq, mem_iInter, he]
      rw [hset]
      refine isClosed_iInter fun n ↦ isClosed_iInter fun _ ↦ ?_
      obtain ⟨L, hL⟩ := exists_schwartzBergman_jetEvaluation hI hInt s hs n
      simpa only [hL] using
        (isClosed_eq L.continuous continuous_const : IsClosed {b | L b = 0})

/-- The polar-free matching conditions of Proposition 5.4.1.4 are closed in the
paired Schwartz–Bergman topology. At each pole they impose vanishing of finitely
many continuous jets. -/
theorem sLocalBergmanGluing_polarFree_isClosed (ρ : ℂ → ℂ) (hρ : Meromorphic ρ) :
    IsClosed {p : SchwartzBergman (Ioi (0 : ℝ)) × SchwartzBergman (Iio (1 : ℝ)) |
      p ∈ sLocalBergmanGluing ρ ∧
        ∀ s : ℂ, s.re < 1 → 0 ≤ meromorphicOrderAt (ρ * p.2.val) s} := by
  have he : {p : SchwartzBergman (Ioi (0 : ℝ)) × SchwartzBergman (Iio (1 : ℝ)) |
      ∀ s : ℂ, s.re < 1 → 0 ≤ meromorphicOrderAt (ρ * p.2.val) s} =
      ⋂ (s : ℂ) (_ : s.re < 1), Prod.snd ⁻¹'
        {b : SchwartzBergman (Iio (1 : ℝ)) | 0 ≤ meromorphicOrderAt (ρ * b.val) s} := by
    ext p
    simp only [mem_ofPred_eq, mem_iInter, mem_preimage]
  have horders : IsClosed _ := he.symm ▸
    (isClosed_iInter fun s ↦ isClosed_iInter fun hs ↦
      (bergman_poleCancellation_isClosed isOpen_Iio ordConnected_Iio ρ s hs
        (hρ s)).preimage continuous_snd)
  exact (sLocalBergmanGluing_isClosed ρ).inter horders

/-- An entire extension of a matching right component agrees with the
meromorphic left formula as germs on the left half-plane. -/
theorem sLocalBergmanGluing_entire_eventuallyEq_left (ρ : ℂ → ℂ) (hρ : Meromorphic ρ)
    (p : SchwartzBergman (Ioi (0 : ℝ)) × SchwartzBergman (Iio (1 : ℝ)))
    (hp : p ∈ sLocalBergmanGluing ρ) (G : ℂ → ℂ)
    (hG : AnalyticOnNhd ℂ G univ) (hEq : EqOn G p.1.val {z | 0 < z.re})
    (s : ℂ) (hs : s.re < 1) :
    ρ * p.2.val =ᶠ[𝓝[≠] s] G := by
  let U : Set ℂ := {z | z.re < 1}
  let R : Set ℂ := {z | 0 < z.re}
  have hU : IsOpen U := isOpen_lt Complex.continuous_re continuous_const
  have hR : IsOpen R := isOpen_lt continuous_const Complex.continuous_re
  have hleft := p.2.property.2.1.analyticOnNhd hU
  let D (z : ℂ) := (ρ * p.2.val) z - G z
  have hD : MeromorphicOn D U := fun z hz ↦
    ((hρ z).mul (hleft z hz).meromorphicAt).sub (hG z (mem_univ z)).meromorphicAt
  have hmid : (1 / 2 : ℂ) ∈ R ∩ U := by
    change 0 < (1 / 2 : ℂ).re ∧ (1 / 2 : ℂ).re < 1
    norm_num [Complex.div_ofNat_re]
  have hzero : meromorphicOrderAt D (1 / 2) = ⊤ := by
    rw [meromorphicOrderAt_eq_top_iff]
    filter_upwards [nhdsWithin_le_nhds ((hR.inter hU).mem_nhds hmid)] with z hz
    exact sub_eq_zero.mpr ((hp z hz.1 hz.2).symm.trans (hEq hz.1).symm)
  have hz : meromorphicOrderAt D s = ⊤ := by
    by_contra hne
    exact (hD.exists_meromorphicOrderAt_ne_top_iff_forall_mem
      ⟨⟨_, hmid.2⟩, (convex_halfSpace_re_lt 1).isPreconnected⟩).mp
      ⟨s, hs, hne⟩ _ hmid.2 hzero
  filter_upwards [meromorphicOrderAt_eq_top_iff.mp hz] with z hz
  exact sub_eq_zero.mp hz

/-- The right component of a matching pair has an entire extension exactly
when all the left pole conditions hold. -/
theorem sLocalBergmanGluing_entire_iff (ρ : ℂ → ℂ) (hρ : Meromorphic ρ)
    (p : SchwartzBergman (Ioi (0 : ℝ)) × SchwartzBergman (Iio (1 : ℝ)))
    (hp : p ∈ sLocalBergmanGluing ρ) :
    (∀ s : ℂ, s.re < 1 → 0 ≤ meromorphicOrderAt (ρ * p.2.val) s) ↔
      ∃ G : ℂ → ℂ, AnalyticOnNhd ℂ G univ ∧ EqOn G p.1.val {z | 0 < z.re} := by
  let U : Set ℂ := {z | z.re < 1}
  let R : Set ℂ := {z | 0 < z.re}
  have hU : IsOpen U := isOpen_lt Complex.continuous_re continuous_const
  have hR : IsOpen R := isOpen_lt continuous_const Complex.continuous_re
  have hleft := p.2.property.2.1.analyticOnNhd hU
  have hright := p.1.property.2.1.analyticOnNhd hR
  let g := toMeromorphicNFOn (ρ * p.2.val) U
  have hm : MeromorphicOn (ρ * p.2.val) U := fun z hz ↦
    (hρ z).mul (hleft z hz).meromorphicAt
  refine ⟨fun horders ↦ ?_, ?_⟩
  swap
  · rintro ⟨G, hG, hEq⟩ s hs
    rw [meromorphicOrderAt_congr (sLocalBergmanGluing_entire_eventuallyEq_left ρ hρ p hp G hG hEq s hs)]
    exact (hG s (mem_univ s)).meromorphicOrderAt_nonneg
  have ha : AnalyticOnNhd ℂ g U := by
    intro z hz
    apply (meromorphicNFOn_toMeromorphicNFOn _ _ hz).meromorphicOrderAt_nonneg_iff_analyticAt.mp
    rw [meromorphicOrderAt_toMeromorphicNFOn hm hz]
    exact horders z hz
  have hEq (z : ℂ) (hl : z ∈ U) (hr : z ∈ R) : p.1.val z = g z := by
    have he : g =ᶠ[𝓝[≠] z] p.1.val := by
      filter_upwards [hm.toMeromorphicNFOn_eq_self_on_nhdsNE hl,
        nhdsWithin_le_nhds ((hR.inter hU).mem_nhds ⟨hr, hl⟩)] with w hw hwmem
      exact hw.trans (hp w hwmem.1 hwmem.2).symm
    exact (tendsto_nhds_unique
      (((ha z hl).continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' he)
      ((hright z hr).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)).symm
  classical
  let G (z : ℂ) := if z ∈ R then p.1.val z else g z
  refine ⟨G, ?_, fun z hz ↦ ite_eq_left hz⟩
  intro z _
  by_cases hz : z ∈ R
  · apply (hright z hz).congr
    filter_upwards [hR.mem_nhds hz] with w hw
    exact (ite_eq_left hw).symm
  · have h : z ∈ U := by
      change ¬ 0 < z.re at hz
      change z.re < 1
      linarith
    apply (ha z h).congr
    filter_upwards [hU.mem_nhds h] with w hw
    by_cases hr : w ∈ R
    · exact (hEq w hw hr).symm.trans (ite_eq_left hr).symm
    · exact (ite_eq_right hr).symm

/-- For the actual paired transform, the left-hand pole conditions are
equivalent to entireness of the normalized continuation of the original test. -/
theorem exists_sLocalPairedBergmanMellin_polarFree
    (ν : Measure (K F S)) [ν.IsHaarMeasure]
    (hν : IsWeilQuotientMeasure (sUnitImage F S) (productHaar F S μ) Measure.count
      (sLocalClassHaar F S ν)) (ω : PontryaginDual (K F S)) :
    ∃ ε : ℂ → ℂ, AnalyticOnNhd ℂ ε univ ∧ (∀ z, ε z ≠ 0) ∧
      (∀ (f : E F S) (z : ℂ), N F S μ ω f z = ε z * R F S μ ω f z) ∧
      let ρ := sLocalExplicitTateFactor F S ω ε
      IsClosed {p : SchwartzBergman (Ioi (0 : ℝ)) × SchwartzBergman (Iio (1 : ℝ)) |
        p ∈ sLocalBergmanGluing ρ ∧
          ∀ s : ℂ, s.re < 1 → 0 ≤ meromorphicOrderAt (ρ * p.2.val) s} ∧
      ∀ f : E F S,
        let p := sLocalPairedBergmanMellin F S ν ω (Submodule.Quotient.mk f)
        (p ∈ sLocalBergmanGluing ρ ∧
          ∀ s : ℂ, s.re < 1 → 0 ≤ meromorphicOrderAt (ρ * p.2.val) s) ↔
          AnalyticOnNhd ℂ (toMeromorphicNFOn (Z F S μ ω f) univ) univ := by
  obtain ⟨ε, hε, hεn, hstrip, hnormalized, hGerms, _⟩ :=
    exists_sLocalMellin_fourier_functionalEquation F S μ ω
  refine ⟨ε, hε, hεn, hnormalized, ?_⟩
  intro ρ
  refine ⟨sLocalBergmanGluing_polarFree_isClosed ρ
    (sLocalExplicitTateFactor_meromorphic F S ω ε (fun z ↦ hε z trivial)), ?_⟩
  intro f p
  letI : (productHaar F S μ).IsHaarMeasure :=
    sLocalZetaProductMeasure_isHaar F S μ (archimedeanMultiplicativeHaar F)
  obtain ⟨hR, hL⟩ := sLocalPairedBergmanMellin_idelic F S ν ω (productHaar F S μ) hν f
  have hmatch : p ∈ sLocalBergmanGluing ρ := by
    intro z hz hr
    change p.1.val z = ρ z * p.2.val z
    rw [hR z hz, hL z hr]
    exact hstrip f z hz hr
  have horders (s : ℂ) (hs : s.re < 1) :
      meromorphicOrderAt (Z F S μ ω f) s = meromorphicOrderAt (ρ * p.2.val) s := by
    apply meromorphicOrderAt_congr ((hGerms f s).trans ?_)
    filter_upwards [nhdsWithin_le_nhds
      ((isOpen_lt Complex.continuous_re continuous_const).mem_nhds hs)] with z hz
    have hr : 0 < (1 - z).re := by simpa [Complex.sub_re, sub_pos] using hz
    exact congrArg (ρ z * ·)
      (((sLocalIdelicZeta_meromorphic_continuation F S μ ω⁻¹
        (sLocalSelectedFourier F S f)).2 hr).trans (hL z hz).symm)
  have hmer : MeromorphicOn (Z F S μ ω f) univ :=
    (sLocalIdelicZeta_meromorphic_continuation F S μ ω f).1.meromorphicOn
  have hNF (s : ℂ) (hs : s ∈ (univ : Set ℂ)) :
      AnalyticAt ℂ (toMeromorphicNFOn (Z F S μ ω f) univ) s ↔
        0 ≤ meromorphicOrderAt (Z F S μ ω f) s := by
    rw [← (meromorphicNFOn_toMeromorphicNFOn _ _ hs).meromorphicOrderAt_nonneg_iff_analyticAt,
      meromorphicOrderAt_toMeromorphicNFOn hmer hs]
  constructor
  · rintro ⟨_, ho⟩ s hs
    apply (hNF s hs).2
    by_cases hleft : s.re < 1
    · rw [horders s hleft]
      exact ho s hleft
    · have hpos : 0 < s.re := by linarith
      have ha : AnalyticAt ℂ p.1.val s := p.1.property.2.1.analyticAt
        ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hpos)
      have he : Z F S μ ω f =ᶠ[𝓝[≠] s] p.1.val := by
        filter_upwards [nhdsWithin_le_nhds
          ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hpos)] with z hz
        exact ((sLocalIdelicZeta_meromorphic_continuation F S μ ω f).2 hz).trans (hR z hz).symm
      rw [meromorphicOrderAt_congr he]
      exact ha.meromorphicOrderAt_nonneg
  · intro ha
    refine ⟨hmatch, fun s hs ↦ ?_⟩
    rw [← horders s hs]
    exact (hNF s (mem_univ s)).1 (ha s (mem_univ s))

/-- The flat paired image is the intersection of the ordinary paired image
with the closed polar-free matching locus. Among matching pairs, belonging
to the flat image is equivalent to admitting an entire Schwartz–Bergman
extension of the right component. -/
theorem exists_sLocalPairedBergmanMellin_polarFree_range
    (ν : Measure (K F S)) [ν.IsHaarMeasure]
    (hν : IsWeilQuotientMeasure (sUnitImage F S) (productHaar F S μ) Measure.count
      (sLocalClassHaar F S ν)) (ω : PontryaginDual (K F S)) :
    ∃ ε : ℂ → ℂ, AnalyticOnNhd ℂ ε univ ∧ (∀ z, ε z ≠ 0) ∧
      (∀ (f : E F S) (z : ℂ), N F S μ ω f z = ε z * R F S μ ω f z) ∧
      let ρ := sLocalExplicitTateFactor F S ω ε
      let W := {p : SchwartzBergman (Ioi (0 : ℝ)) × SchwartzBergman (Iio (1 : ℝ)) |
        p ∈ sLocalBergmanGluing ρ ∧
          ∀ s : ℂ, s.re < 1 → 0 ≤ meromorphicOrderAt (ρ * p.2.val) s}
      let V := range (fun g : sLocalPolarFreeTestSubspace F S ↦
        sLocalPairedBergmanMellin F S ν ω (Submodule.Quotient.mk g.val))
      IsClosed W ∧ V = range (sLocalPairedBergmanMellin F S ν ω) ∩ W ∧
      V = {p | p ∈ sLocalBergmanGluing ρ ∧
        ∃ G : SchwartzBergman (univ : Set ℝ), EqOn G.val p.1.val {z | 0 < z.re}} := by
  obtain ⟨ε, hε, hεn, hnormalized, hW, hflat⟩ :=
    exists_sLocalPairedBergmanMellin_polarFree F S μ ν hν ω
  refine ⟨ε, hε, hεn, hnormalized, hW, ?_, ?_⟩
  · ext p
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨⟨_, rfl⟩, (hflat g.val).2
        (sLocalProductZeta_entire_of_polarFree F S μ ω g.val g.property)⟩
    · rintro ⟨⟨q, rfl⟩, hp⟩
      let M := sLocalHomogeneousThetaKernel F S ν ω
      obtain ⟨f, rfl⟩ := M.mkQ_surjective q
      obtain ⟨g, hg⟩ := (sLocal_entire_iff_flat_and_profile F S μ ν hν ω f).1.mp
        ((hflat f).1 hp)
      have he : (Submodule.Quotient.mk (p := M) g.val) = Submodule.Quotient.mk f := by
        rw [Submodule.Quotient.eq, mem_sLocalHomogeneousThetaKernel_iff,
          sLocalHomogeneousTheta_zero_iff_meromorphicZeta F S μ ν hν, map_sub, hg, sub_self]
      exact ⟨g, congrArg (sLocalPairedBergmanMellin F S ν ω) he⟩
  let ρ := sLocalExplicitTateFactor F S ω ε
  letI : (productHaar F S μ).IsHaarMeasure :=
    sLocalZetaProductMeasure_isHaar F S μ (archimedeanMultiplicativeHaar F)
  have right (f : E F S) (z : ℂ) (hz : 0 < z.re) :
      (sLocalPairedBergmanMellin F S ν ω (Submodule.Quotient.mk f)).1.val z =
        Z F S μ ω f z :=
    ((sLocalPairedBergmanMellin_idelic F S ν ω (productHaar F S μ) hν f).1 z hz).trans
      ((sLocalIdelicZeta_meromorphic_continuation F S μ ω f).2 hz).symm
  have matching (g : sLocalPolarFreeTestSubspace F S) :=
    (hflat g.val).2 (sLocalProductZeta_entire_of_polarFree F S μ ω g.val g.property)
  ext p
  constructor
  · rintro ⟨g, rfl⟩
    let G := toMeromorphicNFOn (Z F S μ ω g.val) univ
    have hG := sLocalProductZeta_entire_of_polarFree F S μ ω g.val g.property
    have hmer : MeromorphicOn (Z F S μ ω g.val) univ :=
      (sLocalIdelicZeta_meromorphic_continuation F S μ ω g.val).1.meromorphicOn
    have hEq (z : ℂ) : Z F S μ ω g.val =ᶠ[𝓝[≠] z] G :=
      (hmer.toMeromorphicNFOn_eq_self_on_nhdsNE (mem_univ z)).symm
    have hMem := sLocal_entire_mem_schwartzBergman F S μ ν hν ω g.val G
      (fun z ↦ (hG z (mem_univ z)).differentiableAt) hEq
    refine ⟨(matching g).1, ⟨G, hMem⟩, fun z hz ↦ ?_⟩
    let b := (sLocalPairedBergmanMellin F S ν ω (Submodule.Quotient.mk g.val)).1
    have hb := b.property.2.1.continuousOn.continuousAt
      ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz)
    have hGz := (hG z (mem_univ z)).continuousAt
    have h : G =ᶠ[𝓝[≠] z] b.val := by
      filter_upwards [(hEq z).symm, nhdsWithin_le_nhds
        ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz)] with w hw hwpos
      exact hw.trans (right g.val w hwpos).symm
    exact tendsto_nhds_unique ((hGz.tendsto.mono_left nhdsWithin_le_nhds).congr' h)
      (hb.tendsto.mono_left nhdsWithin_le_nhds)
  · rintro ⟨hp, G, hG⟩
    obtain ⟨g, hg⟩ := exists_sLocalPolarFree_zeta_eq_schwartzBergman F S μ ν hν ω G
    let b := sLocalPairedBergmanMellin F S ν ω (Submodule.Quotient.mk g.val)
    have hright (z : ℂ) (hz : 0 < z.re) : b.1.val z = p.1.val z :=
      (right g.val z hz).trans ((hg hz).trans (hG hz))
    have hleft : EqOn b.2.val p.2.val {z | z.re < 1} := by
      have hOpen := isOpen_lt Complex.continuous_re (continuous_const (y := (1 : ℝ)))
      refine (b.2.property.2.1.analyticOnNhd hOpen).eqOn_of_preconnected_of_eventuallyEq
        (p.2.property.2.1.analyticOnNhd hOpen)
        (convex_halfSpace_re_lt 1).isPreconnected
        (z₀ := 1 / 2) ?_ ?_
      · norm_num [Complex.div_ofNat_re]
      · have hmid : (1 / 2 : ℂ) ∈ {z : ℂ | 0 < z.re ∧ z.re < 1} := by
          norm_num [Complex.div_ofNat_re]
        filter_upwards [((isOpen_lt continuous_const Complex.continuous_re).inter hOpen).mem_nhds
          hmid] with z hz
        have hz' : 0 < (1 - z).re := by simpa [Complex.sub_re, sub_pos] using hz.2
        have hn : ρ z ≠ 0 := mul_ne_zero
          (mul_ne_zero (hεn z) (inv_ne_zero (sLocalEulerDenominator_ne_zero_of_pos F S ω hz.1)))
          (sLocalEulerDenominator_ne_zero_of_pos F S ω⁻¹ hz')
        exact mul_left_cancel₀ hn (((matching g).1 z hz.1 hz.2).symm.trans
          ((hright z hz.1).trans (hp z hz.1 hz.2)))
    refine ⟨g, Prod.ext (Subtype.ext (funext fun z ↦ ?_)) (Subtype.ext (funext fun z ↦ ?_))⟩
    · by_cases hz : 0 < z.re
      · exact hright z hz
      · exact (b.1.property.1 hz).trans (p.1.property.1 hz).symm
    · by_cases hz : z.re < 1
      · exact hleft hz
      · exact (b.2.property.1 hz).trans (p.2.property.1 hz).symm

/-- Strip gluing defines a closed subspace of the paired Schwartz–Bergman
space and contains the actual paired transform. -/
theorem exists_sLocalPairedBergmanMellin_closed_gluing
    (ν : Measure (K F S)) [ν.IsHaarMeasure]
    (hν : IsWeilQuotientMeasure (sUnitImage F S) (productHaar F S μ) Measure.count
      (sLocalClassHaar F S ν)) (ω : PontryaginDual (K F S)) :
    ∃ A : ℂ → ℂ, AnalyticOnNhd ℂ A univ ∧ (∀ z, A z ≠ 0) ∧
      let W := sLocalBergmanGluing fun z ↦ sLocalEulerDenominator F S ω⁻¹ (1 - z) /
        (A z * sLocalEulerDenominator F S ω z)
      IsClosed W.carrier ∧ range (sLocalPairedBergmanMellin F S ν ω) ⊆ W.carrier := by
  obtain ⟨A, hA, hn, _, hGlue⟩ := exists_sLocalMellin_fourier_gluing F S μ ω
  let ρ z := sLocalEulerDenominator F S ω⁻¹ (1 - z) /
    (A z * sLocalEulerDenominator F S ω z)
  refine ⟨A, hA, hn, sLocalBergmanGluing_isClosed ρ, ?_⟩
  · rintro _ ⟨q, rfl⟩
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    letI : (productHaar F S μ).IsHaarMeasure :=
      sLocalZetaProductMeasure_isHaar F S μ (archimedeanMultiplicativeHaar F)
    obtain ⟨hR, hL⟩ := sLocalPairedBergmanMellin_idelic F S ν ω (productHaar F S μ) hν f
    intro z hz hr
    change _ = ρ z * _
    rw [hR z hz, hL z hr]
    exact hGlue f z hz hr

end

end Masullo
