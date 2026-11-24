import GlobalConverseLeftEdge
import VerticalJetInterpolation

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical NumberField

namespace Masullo

noncomputable section

private abbrev twoPi : ℂ := 2 * (Real.pi : ℂ)

private theorem twoPi_ne_zero : twoPi ≠ 0 :=
  mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)

private theorem invGammaReal_step (u : ℂ) :
    (Complex.Gammaℝ u)⁻¹ = (u / twoPi) * (Complex.Gammaℝ (u + 2))⁻¹ := by
  by_cases h : u = 0
  · subst u
    have hz : Complex.Gammaℝ 0 = 0 :=
      Complex.Gammaℝ_eq_zero_iff.mpr ⟨0, by simp⟩
    simp [hz]
  have hu : u / twoPi ≠ 0 := div_ne_zero h twoPi_ne_zero
  have he : Complex.Gammaℝ (u + 2) = (u / twoPi) * Complex.Gammaℝ u := by
    rw [Complex.Gammaℝ_add_two h]
    dsimp [twoPi]
    ring
  rw [he, mul_inv, ← mul_assoc, mul_inv_cancel₀ hu, one_mul]

private theorem invGammaComplex_step (u : ℂ) :
    (Complex.Gammaℂ u)⁻¹ = (u / twoPi) * (Complex.Gammaℂ (u + 1))⁻¹ := by
  by_cases h : u = 0
  · subst u
    have hzero : Complex.Gamma 0 = 0 := by simp
    simp [Complex.Gammaℂ_def, hzero]
  have hu : u / twoPi ≠ 0 := div_ne_zero h twoPi_ne_zero
  have he : Complex.Gammaℂ (u + 1) = (u / twoPi) * Complex.Gammaℂ u := by
    rw [Complex.Gammaℂ_add_one h]
    dsimp [twoPi]
    ring
  rw [he, mul_inv, ← mul_assoc, mul_inv_cancel₀ hu, one_mul]

private theorem invGammaComplex_two_steps (u : ℂ) :
    (Complex.Gammaℂ u)⁻¹ = (u / twoPi * ((u + 1) / twoPi)) *
      (Complex.Gammaℂ (u + 2))⁻¹ := by
  rw [invGammaComplex_step u, invGammaComplex_step (u + 1), ← mul_assoc]
  congr 3
  ring

private theorem affineProduct_growth {ι : Type*} [Fintype ι] (c : ι → ℂ) :
    ∃ M > (0 : ℝ), ∀ z : ℂ,
      ‖∏ i, (z + c i) / twoPi‖ ≤ M * (1 + ‖z‖) ^ Fintype.card ι := by
  let b (i : ι) : ℝ := (1 + ‖c i‖) / ‖twoPi‖
  have hb (i : ι) : 0 < b i := div_pos (by positivity) (norm_pos_iff.mpr twoPi_ne_zero)
  refine ⟨∏ i, b i, Finset.prod_pos fun i _ ↦ hb i, fun z ↦ ?_⟩
  have hp : (∏ _ : ι, (1 + ‖z‖)) = (1 + ‖z‖) ^ Fintype.card ι := by simp
  rw [norm_prod, ← hp, ← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod (fun i _ ↦ norm_nonneg _)
  intro i _
  rw [norm_div]
  refine (div_le_div_of_nonneg_right (norm_add_le _ _) (norm_nonneg _)).trans ?_
  dsimp only [b]
  rw [div_mul_eq_mul_div]
  apply div_le_div_of_nonneg_right _ (norm_nonneg _)
  nlinarith [norm_nonneg z, norm_nonneg (c i), mul_nonneg (norm_nonneg z) (norm_nonneg (c i))]

private theorem affineProduct_lower {ι : Type*} [Fintype ι] (c : ι → ℂ)
    (hc : ∀ i, 0 ≤ (c i).re) {a : ℝ} (ha : 0 < a) (z : ℂ) (hz : a ≤ z.re) :
    (a / ‖twoPi‖) ^ Fintype.card ι ≤ ‖∏ i, (z + c i) / twoPi‖ := by
  have h : (∏ _ : ι, a / ‖twoPi‖) = (a / ‖twoPi‖) ^ Fintype.card ι := by
    simp only [Finset.prod_const, Finset.card_univ]
  rw [← h, norm_prod]
  apply Finset.prod_le_prod (fun _ _ ↦ by positivity)
  intro i _
  rw [norm_div]
  apply div_le_div_of_nonneg_right _ (norm_nonneg _)
  have hab : a ≤ (z + c i).re := by
    rw [Complex.add_re]
    linarith [hc i]
  exact hab.trans ((le_abs_self _).trans (Complex.abs_re_le_norm _))

variable (F : Type*) [Field F] [NumberField F]
variable (S : Finset (HeightOneSpectrum (𝓞 F)))
variable (ω : PontryaginDual (normOneIdeleClass F)) (hS : Surjective (sIdeleClassInclusion F S))
variable (hω : globalNormOneCharacter F ω ∈
  (sUnramified F S : Set (QuasiCharacter (IdeleClass F))))

private abbrev σ := sLocalNormOneCharacterOfGlobal F ω S hS hω

/-- On the strip used for the converse, the poles at the chosen finite
stage can be cleared using a factor of polynomial growth. The residual
denominator is the reciprocal archimedean product at the shifted argument. -/
theorem exists_stageEulerPoleClearing :
    ∃ (Q : ℂ → ℂ) (M : ℝ) (d : ℕ), 0 ≤ M ∧ AnalyticOnNhd ℂ Q univ ∧
      (∀ z : ℂ, (-1 : ℝ) ≤ z.re → ‖Q z‖ ≤ M * (1 + ‖z‖) ^ d) ∧
      (∀ a > (0 : ℝ), ∃ c > (0 : ℝ), ∀ z : ℂ, a ≤ z.re → c ≤ ‖Q z‖) ∧
      ∀ z : ℂ, sLocalEulerDenominator F S (σ F S ω hS hω) z =
        Q z * completedTateReciprocalArch F S hS ω hω (z + 2) := by
  let r := sLocalRealArchParameters F S (σ F S ω hS hω)
  let c := sLocalComplexArchParameters F S (σ F S ω hS hω)
  let a (v : {v : InfinitePlace F // v.IsReal}) : ℂ := (r v).1 + ((r v).2 % 2 : ℕ)
  let b (v : {v : InfinitePlace F // v.IsComplex}) : ℂ := (c v).1 + (c v).2.natAbs / (2 : ℂ)
  let b' (v : {v : InfinitePlace F // v.IsComplex}) : ℂ := b v + 1
  let A (z : ℂ) := (∏ v, (z + a v) / twoPi) *
    (∏ v, (z + b v) / twoPi) * (∏ v, (z + b' v) / twoPi)
  let P := finiteHeckeOmissionMultiplier F (normOneEulerCharacter F ω) S
  have hAffine (v z : ℂ) : AnalyticAt ℂ (fun w : ℂ ↦ (w + v) / twoPi) z :=
    (analyticAt_id.add analyticAt_const).div analyticAt_const twoPi_ne_zero
  have hA (z : ℂ) : AnalyticAt ℂ A z :=
    ((Finset.univ.analyticAt_fun_prod fun v _ ↦ hAffine (a v) z).mul
      (Finset.univ.analyticAt_fun_prod fun v _ ↦ hAffine (b v) z)).mul
      (Finset.univ.analyticAt_fun_prod fun v _ ↦ hAffine (b' v) z)
  obtain ⟨M, hM, hbP⟩ := finiteHeckeOmissionMultiplier_norm_le F (normOneEulerCharacter F ω) S (-1)
  obtain ⟨D, hD, hDa⟩ := affineProduct_growth a
  obtain ⟨E, hE, hEb⟩ := affineProduct_growth b
  obtain ⟨G, hG, hGb⟩ := affineProduct_growth b'
  let d := InfinitePlace.nrRealPlaces F + InfinitePlace.nrComplexPlaces F +
    InfinitePlace.nrComplexPlaces F
  refine ⟨A * P, D * E * G * M, d, by positivity,
    fun z _ ↦ (hA z).mul (finiteHeckeOmissionMultiplier_analytic F (normOneEulerCharacter F ω) S z),
    ?_, ?_, ?_⟩
  · intro z hz
    have h₁ := hDa z
    have h₂ := hEb z
    have h₃ := hGb z
    change ‖A z * P z‖ ≤ _
    simp only [A, d, norm_mul, pow_add]
    calc
      _ ≤ ((D * (1 + ‖z‖) ^ InfinitePlace.nrRealPlaces F) *
          (E * (1 + ‖z‖) ^ InfinitePlace.nrComplexPlaces F) *
          (G * (1 + ‖z‖) ^ InfinitePlace.nrComplexPlaces F)) * M := by
        gcongr
        exact hbP z hz
      _ = _ := by ring
  · intro l hl
    obtain ⟨C, hC, hP⟩ := finiteHeckeOmissionMultiplier_norm_ge_of_re_ge
      F (normOneEulerCharacter F ω) S hl
    have ha (v : {v : InfinitePlace F // v.IsReal}) : 0 ≤ (a v).re := by
      simp [a, r, Complex.add_re, sLocalRealArchParameters_re]
    have hb (v : {v : InfinitePlace F // v.IsComplex}) : 0 ≤ (b v).re := by
      simp only [b, c, Complex.add_re, Complex.div_ofNat_re, Complex.natCast_re,
        sLocalComplexArchParameters_re, zero_add]
      positivity
    have hb' (v : {v : InfinitePlace F // v.IsComplex}) : 0 ≤ (b' v).re := by
      simp only [b', Complex.add_re, Complex.one_re]
      linarith [hb v]
    let k := l / ‖twoPi‖
    have hk : 0 < k := div_pos hl (norm_pos_iff.mpr twoPi_ne_zero)
    refine ⟨(k ^ d) * C, mul_pos (pow_pos hk _) hC, fun z hz ↦ ?_⟩
    change _ ≤ ‖A z * P z‖
    simp only [A, d, norm_mul, pow_add]
    gcongr
    · exact affineProduct_lower a ha hl z hz
    · exact affineProduct_lower b hb hl z hz
    · exact affineProduct_lower b' hb' hl z hz
    · exact hP z hz
  · intro z
    rw [stageEulerDenominator_eq_arch_mul_omission F S ω hS hω]
    have hArch (w : ℂ) : completedTateReciprocalArch F S hS ω hω w =
        (∏ v, (Complex.Gammaℝ (w + a v))⁻¹) * (∏ v, (Complex.Gammaℂ (w + b v))⁻¹) := by
      simp only [completedTateReciprocalArch, archimedeanNumberFieldZetaDenominator,
        realArchZetaDenominator, complexArchZetaDenominator, a, b, r, c, add_assoc]
    rw [hArch, hArch]
    change
      ((∏ v, (Complex.Gammaℝ (z + a v))⁻¹) * (∏ v, (Complex.Gammaℂ (z + b v))⁻¹)) * P z =
        (A z * P z) *
          ((∏ v, (Complex.Gammaℝ (z + 2 + a v))⁻¹) *
           (∏ v, (Complex.Gammaℂ (z + 2 + b v))⁻¹))
    have hR (v : {v : InfinitePlace F // v.IsReal}) :
        (Complex.Gammaℝ (z + a v))⁻¹ =
          ((z + a v) / twoPi) * (Complex.Gammaℝ (z + 2 + a v))⁻¹ := by
      rw [invGammaReal_step (z + a v), add_right_comm]
    have hC (v : {v : InfinitePlace F // v.IsComplex}) :
        (Complex.Gammaℂ (z + b v))⁻¹ = ((z + b v) / twoPi) * ((z + b' v) / twoPi) *
          (Complex.Gammaℂ (z + 2 + b v))⁻¹ := by
      rw [invGammaComplex_two_steps (z + b v),
        show z + b v + 2 = z + 2 + b v by ring,
        show z + b v + 1 = z + b' v by simp [b', add_assoc]]
    simp_rw [hR, hC, Finset.prod_mul_distrib]
    dsimp [A]
    ring

#print axioms exists_stageEulerPoleClearing

private abbrev K := normOneIdeleClass F
private abbrev Place := HeightOneSpectrum (𝓞 F)

local instance : MeasurableSpace (K F) := borel _
local instance : BorelSpace (K F) := ⟨rfl⟩
local instance : MeasurableSpace (Idele F) := borel _
local instance : BorelSpace (Idele F) := ⟨rfl⟩

variable (ν : Measure (K F)) [ν.IsHaarMeasure]
variable (η : Measure (Idele F)) [η.IsHaarMeasure]
variable [∀ v : Place F, MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : Place F, BorelSpace (v.adicCompletion F)ˣ]
  (μ : ∀ v : Place F, Measure (v.adicCompletion F)ˣ)
  [∀ v : Place F, (μ v).IsHaarMeasure] [∀ v : Place F, SigmaFinite (μ v)]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]
variable (hν : IsWeilQuotientMeasure (principalIdeles F) η Measure.count (globalClassMeasure F ν))

private abbrev Z (f : sLocalBruhatImage F S) :=
  sLocalProductZetaContinued F S (fun v : S ↦ μ v.val) (σ F S ω hS hω)
    (sLocalRealArchParameters F S (σ F S ω hS hω))
    (sLocalComplexArchParameters F S (σ F S ω hS hω)) f

include μ hν in
/-- On closed positive substrips up to real part two, a multiplier for a
global Schwartz–Bergman transform also gives a rapidly decreasing local
coordinate. The polynomial pole clearer permits the rectangle to cross zero. -/
theorem globalMellinMultiplier_rapid_on_stage_positive_strip
    (f : sLocalBruhatImage F S) {m : ℂ → ℂ} (hm : Differentiable ℂ m)
    (b : SchwartzBergman (univ : Set ℝ))
    (hb : ∀ z, (fun w ↦ m w *
      globalZetaContinued F ν f.val (compactIdeleClassCharacter F ω) 0 w) =ᶠ[𝓝[≠] z] b.val)
    {a d : ℝ} (ha : 0 < a) (hd : d ≤ 2) :
    ∀ n : ℕ, BddAbove
      ((fun z : ℂ ↦ ‖z ^ n * (m z * Z F S ω hS hω μ f z)‖) '' (Complex.re ⁻¹' Icc a d)) := by
  let σ₀ := σ F S ω hS hω
  let Z₀ := Z F S ω hS hω μ f
  let E := completedTateReciprocalArch F S hS ω hω
  let N := sLocalEulerNormalizedMellin F S (fun v : S ↦ μ v.val) σ₀ f
  let H (z : ℂ) := m z * N z / E (z + 2)
  let strip := Complex.re ⁻¹' Icc (-1 : ℝ) 2
  obtain ⟨Q, M, k, hM, hQa, hQbound, hQlower, hD⟩ := exists_stageEulerPoleClearing F S ω hS hω
  obtain ⟨L, hLm, hLe, ⟨V, hVa⟩, hStrip⟩ :=
    exists_globalConverse_Outside_strip_transfer_both_edges F ν η μ hν (normOneEulerCharacter F ω) S
  obtain ⟨A, hA, hProd⟩ :=
    globalContinuedMellin_eq_outside_mul_stage F ν η μ hν S ω hS hω hLm hLe
  have hEpos (z : ℂ) (hz : -1 ≤ z.re) : E (z + 2) ≠ 0 := by
    apply archimedeanNumberFieldZetaDenominator_ne_zero_of_pos
    · intro v
      norm_num [Complex.add_re, sLocalRealArchParameters_re]
      linarith
    · intro v
      norm_num [Complex.add_re, sLocalComplexArchParameters_re]
      linarith
  have hHa (z : ℂ) (hz : -1 ≤ z.re) : AnalyticAt ℂ H z := by
    refine ((hm.analyticAt z).mul
      (sLocalEulerNormalizedMellin_entire F S (fun v : S ↦ μ v.val) σ₀ f z trivial)).div ?_ (hEpos z hz)
    exact (archimedeanNumberFieldZetaDenominator_analytic _ _ _ (z + 2)).comp
      (f := fun w : ℂ ↦ w + 2) (analyticAt_id.add analyticAt_const)
  have hHprod (z : ℂ) (hz : -1 ≤ z.re) :
      H =ᶠ[𝓝[≠] z] fun w ↦ Q w * (m w * Z₀ w) := by
    have hEn : ∀ᶠ w in 𝓝[≠] z, E (w + 2) ≠ 0 :=
      (((archimedeanNumberFieldZetaDenominator_analytic _ _ _ (z + 2)).continuousAt.comp
        (f := fun w : ℂ ↦ w + 2) (continuous_id.add continuous_const).continuousAt).eventually_ne
          (hEpos z hz)).filter_mono nhdsWithin_le_nhds
    filter_upwards [hEn, sLocalEulerNormalizedMellin_eq_germ F S (fun v : S ↦ μ v.val) σ₀ f z] with w hE hN
    change N w = sLocalEulerDenominator F S σ₀ w * Z₀ w at hN
    dsimp only [H]
    rw [hN, hD]
    apply (div_eq_iff hE).mpr
    ring
  have hHL (z : ℂ) (hz : z ∈ strip) (hbig : V ≤ |z.im|) :
      L z * H z = A⁻¹ * Q z * b.val z := by
    have hEq : (fun w ↦ L w * H w) =ᶠ[𝓝[≠] z] fun w ↦ A⁻¹ * Q w * b.val w := by
      filter_upwards [hHprod z hz.1, hProd f z, hb z] with w hHw hGw hbw
      change m w * globalZetaContinued F ν f.val (compactIdeleClassCharacter F ω) 0 w = b.val w at hbw
      change globalZetaContinued F ν f.val (compactIdeleClassCharacter F ω) 0 w =
        A * L w * Z₀ w at hGw
      rw [hGw] at hbw
      rw [hHw, ← hbw]
      calc
        _ = (A⁻¹ * A) * (L w * (Q w * (m w * Z₀ w))) := by
          rw [inv_mul_cancel₀ hA, one_mul]
        _ = _ := by ring
    have hbDiff : Differentiable ℂ b.val := by
      simpa only [preimage_univ, differentiableOn_univ] using b.property.2.1
    have hLc := (hVa z hbig).continuousAt.mul (hHa z hz.1).continuousAt
    have hRc : ContinuousAt (fun w ↦ A⁻¹ * Q w * b.val w) z :=
      (continuousAt_const.mul (hQa z trivial).continuousAt).mul (hbDiff z).continuousAt
    exact ((hLc.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE hRc).mp hEq).eq_of_nhds
  have hHrapid : ∀ n : ℕ, BddAbove ((fun z : ℂ ↦ ‖z ^ n * H z‖) '' strip) := by
    apply hStrip (fun z hz ↦ (hHa z hz.1).differentiableAt.differentiableWithinAt) (max V 1)
    intro n
    obtain ⟨C, hC⟩ := b.property.2.2 (-1) 2 (by norm_num) (subset_univ _) (n + k)
    refine ⟨‖A⁻¹‖ * M * 2 ^ k * C, ?_⟩
    rintro _ ⟨z, ⟨hz, hy⟩, rfl⟩
    have hnorm : 1 ≤ ‖z‖ := (le_max_right V 1).trans (hy.trans (Complex.abs_im_le_norm z))
    have hbQ : ‖Q z‖ ≤ (M * 2 ^ k) * ‖z‖ ^ k := by
      apply (hQbound z hz.1).trans
      rw [mul_assoc, ← mul_pow]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by linarith) k) hM
    change ‖z ^ n * (L z * H z)‖ ≤ _
    rw [hHL z hz ((le_max_left V 1).trans hy)]
    calc
      _ = ‖A⁻¹‖ * ‖Q z‖ * ‖z ^ n * b.val z‖ := by simp only [norm_mul]; ring
      _ ≤ (‖A⁻¹‖ * (M * 2 ^ k)) * ‖z ^ (n + k) * b.val z‖ := by
        have h := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hbQ (norm_nonneg A⁻¹)) (norm_nonneg (z ^ n * b.val z))
        refine h.trans_eq ?_
        simp only [pow_add, norm_mul, norm_pow]
        ring
      _ ≤ ‖A⁻¹‖ * M * 2 ^ k * C := by
        rw [mul_assoc ‖A⁻¹‖ M]
        exact mul_le_mul_of_nonneg_left (hC ⟨z, hz, rfl⟩) (by positivity)
  obtain ⟨c, hc, hQl⟩ := hQlower a ha
  intro n
  obtain ⟨C, hC⟩ := hHrapid n
  refine ⟨C / c, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  have hz' : z ∈ strip := ⟨by linarith [hz.1], hz.2.trans hd⟩
  have hzpos : 0 < z.re := ha.trans_le hz.1
  have hZc := sLocalProductZetaContinued_continuousAt_pos F μ S σ₀ f z hzpos
  have hQc := (hQa z trivial).continuousAt
  have hmc := (hm z).continuousAt
  have hPoint := (((hHa z hz'.1).continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
    (hQc.mul (hmc.mul hZc))).mp (hHprod z hz'.1)).eq_of_nhds
  change H z = Q z * (m z * Z₀ z) at hPoint
  apply (le_div_iff₀ hc).mpr
  calc
    ‖z ^ n * (m z * Z₀ z)‖ * c ≤ ‖z ^ n * (m z * Z₀ z)‖ * ‖Q z‖ :=
      mul_le_mul_of_nonneg_left (hQl z hz.1) (norm_nonneg _)
    _ = ‖z ^ n * H z‖ := by rw [hPoint]; simp only [norm_mul]; ring
    _ ≤ C := hC ⟨z, hz', rfl⟩

#print axioms globalMellinMultiplier_rapid_on_stage_positive_strip

omit [∀ v : Place F, MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : Place F, BorelSpace (v.adicCompletion F)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ] in
set_option maxHeartbeats 500000 in
private theorem finiteEuler_norm_ge_right_half :
    ∃ c > (0 : ℝ), ∀ z : ℂ, 2 ≤ z.re → c ≤ ‖globalFiniteHeckeEuler F ω z‖ := by
  let H := max 1 ‖globalFiniteHeckeEuler F 1 (2 : ℂ)‖
  have hH : 0 < H := zero_lt_one.trans_le (le_max_left _ _)
  refine ⟨H⁻¹, inv_pos.mpr hH, fun z hz ↦ ?_⟩
  let w : ℂ := (z.re : ℂ) + 2 * ((z.im : ℂ) * Complex.I)
  have hprod := globalFiniteHeckeEuler_product_norm_ge_one F ω
    (show 1 < z.re by linarith) z.im
  rw [Complex.re_add_im z] at hprod
  change 1 ≤ ‖globalFiniteHeckeEuler F 1 (z.re : ℂ) ^ 3 *
    globalFiniteHeckeEuler F ω z ^ 4 * globalFiniteHeckeEuler F (ω ^ 2) w‖ at hprod
  rw [norm_mul, norm_mul, norm_pow, norm_pow] at hprod
  have hζ : ‖globalFiniteHeckeEuler F 1 (z.re : ℂ)‖ ≤ H :=
    (globalFiniteHeckeEuler_bounded_right F 1 (by norm_num : (1 : ℝ) < 2)
      (by simpa using hz)).trans (le_max_right _ _)
  have hω₂ : ‖globalFiniteHeckeEuler F (ω ^ 2) w‖ ≤ H :=
    (globalFiniteHeckeEuler_bounded_right F (ω ^ 2) (by norm_num : (1 : ℝ) < 2)
      (by simpa [w, Complex.mul_re, Complex.mul_im] using hz)).trans (le_max_right _ _)
  have hpow : 1 ≤ (H * ‖globalFiniteHeckeEuler F ω z‖) ^ 4 := by
    refine hprod.trans ?_
    calc
      _ ≤ H ^ 3 * ‖globalFiniteHeckeEuler F ω z‖ ^ 4 * H :=
        mul_le_mul (mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (norm_nonneg _) hζ _) (by positivity)) hω₂ (norm_nonneg _) (by positivity)
      _ = _ := by ring
  apply (inv_le_iff_one_le_mul₀' hH).mpr
  by_contra! hbad
  exact (pow_lt_pow_left₀ hbad (by positivity) (by decide : (4 : ℕ) ≠ 0)).not_ge
    (by simpa using hpow)

include μ hν in
/-- On the canonical norm-one chart, rapid decay of a multiplied global
transform gives rapid decay of its multiplied local transform on every
closed positive substrip. The half-plane beyond real part two is controlled
directly by the absolutely convergent exterior Euler product. -/
theorem globalMellinMultiplier_rapid_on_stage
    (f : sLocalBruhatImage F S) {m : ℂ → ℂ} (hm : Differentiable ℂ m)
    (b : SchwartzBergman (univ : Set ℝ))
    (hb : ∀ z, (fun w ↦ m w *
      globalZetaContinued F ν f.val (compactIdeleClassCharacter F ω) 0 w) =ᶠ[𝓝[≠] z] b.val)
    {a d : ℝ} (ha : 0 < a) (had : a ≤ d) :
    ∀ n : ℕ, BddAbove
      ((fun z : ℂ ↦ ‖z ^ n * (m z * Z F S ω hS hω μ f z)‖) '' (Complex.re ⁻¹' Icc a d)) := by
  let χ := normOneEulerCharacter F ω
  let P := finiteHeckeOmissionMultiplier F χ S
  let Z₀ := Z F S ω hS hω μ f
  obtain ⟨g, hf, he, hfa, _, _⟩ := exists_globalFiniteHecke_polynomial_strips F ω ν η μ hν
  let L := P * g
  have hL : MeromorphicOn L univ := fun z hz ↦
    (finiteHeckeOmissionMultiplier_analytic F χ S z).meromorphicAt.mul (hf z hz)
  have hLe : EqOn L (manuscriptFiniteHeckeEulerOutside F χ S) {z | 1 < z.re} := by
    intro z hz
    change P z * g z = _
    rw [he hz, manuscriptFiniteHeckeEulerOutside_eq F χ S hz]
    rfl
  obtain ⟨A, hA, hStage⟩ := globalContinuedMellin_eq_outside_mul_stage F ν η μ hν S ω hS hω hL hLe
  obtain ⟨c, hc, hcL⟩ := finiteEuler_norm_ge_right_half F ω
  obtain ⟨e, hep, hP⟩ := finiteHeckeOmissionMultiplier_norm_ge_of_re_ge F χ S (by norm_num : (0 : ℝ) < 2)
  have hBdiff : Differentiable ℂ b.val := by
    simpa only [preimage_univ, differentiableOn_univ] using b.property.2.1
  intro n
  obtain ⟨C, hC⟩ := globalMellinMultiplier_rapid_on_stage_positive_strip F S ω hS hω ν η μ hν
    f hm b hb (a := a) (d := 2) ha le_rfl n
  obtain ⟨B, hB⟩ := b.property.2.2 a d had (subset_univ _) n
  let k := ‖A‖ * e * c
  have hk : 0 < k := mul_pos (mul_pos (norm_pos_iff.mpr hA) hep) hc
  refine ⟨max C (B / k), ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  by_cases h₂ : z.re ≤ 2
  · exact (hC ⟨z, ⟨hz.1, h₂⟩, rfl⟩).trans (le_max_left _ _)
  have hzpos : 0 < z.re := by linarith
  have hg : AnalyticAt ℂ g z := hfa z
    (by intro h; norm_num [h] at h₂) (by intro h; norm_num [h] at h₂)
  have hLc : ContinuousAt L z := (finiteHeckeOmissionMultiplier_analytic F χ S z).continuousAt.mul
    hg.continuousAt
  have hEq : (fun w ↦ A * L w * (m w * Z₀ w)) =ᶠ[𝓝[≠] z] b.val := by
    filter_upwards [hStage f z, hb z] with w h₁ h₂
    change globalZetaContinued F ν f.val (compactIdeleClassCharacter F ω) 0 w = A * L w * Z₀ w at h₁
    change m w * globalZetaContinued F ν f.val (compactIdeleClassCharacter F ω) 0 w = b.val w at h₂
    rw [← h₂, h₁]
    ring
  have hcProd : ContinuousAt (fun w ↦ A * L w * (m w * Z₀ w)) z :=
    (continuousAt_const.mul hLc).mul ((hm z).continuousAt.mul
      (sLocalProductZetaContinued_continuousAt_pos F μ S _ f z hzpos))
  have hpoint := ((hcProd.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
    (hBdiff z).continuousAt).mp hEq).eq_of_nhds
  change A * L z * (m z * Z₀ z) = b.val z at hpoint
  have hkL : k ≤ ‖A‖ * ‖L z‖ := by
    change ‖A‖ * e * c ≤ ‖A‖ * ‖P z * g z‖
    rw [mul_assoc, norm_mul, he (show 1 < z.re by linarith)]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul (hP z (le_of_not_ge h₂)) (hcL z (le_of_not_ge h₂)) hc.le (norm_nonneg _)) (norm_nonneg _)
  refine ((le_div_iff₀ hk).mpr ?_).trans (le_max_right _ _)
  calc
    _ ≤ ‖z ^ n * (m z * Z₀ z)‖ * (‖A‖ * ‖L z‖) :=
      mul_le_mul_of_nonneg_left hkL (norm_nonneg _)
    _ = ‖z ^ n * b.val z‖ := by rw [← hpoint]; simp only [norm_mul]; ring
    _ ≤ B := hB ⟨z, hz, rfl⟩

#print axioms globalMellinMultiplier_rapid_on_stage

include μ hν in
/-- Fourier reflection gives rapid decay of the second local coordinate
on every closed substrip of the half-plane to the left of one. The stage
contains the different so that the test's adelic Fourier transform stays in it. -/
theorem globalMellinMultiplier_rapid_on_reflected_stage
    (hω' : globalNormOneCharacter F ω⁻¹ ∈
      (sUnramified F S : Set (QuasiCharacter (IdeleClass F))))
    (hDiff : ∀ v : Place F, v.asIdeal ∣ differentIdeal ℤ (𝓞 F) → v ∈ S)
    (f : sLocalBruhatImage F S) {m : ℂ → ℂ} (hm : Differentiable ℂ m)
    (b : SchwartzBergman (univ : Set ℝ))
    (hb : ∀ z, (fun w ↦ m w *
      globalZetaContinued F ν f.val (compactIdeleClassCharacter F ω) 0 w) =ᶠ[𝓝[≠] z] b.val)
    {a d : ℝ} (had : a ≤ d) (hd : d < 1) :
    let f' : sLocalBruhatImage F S := ⟨GlobalBruhat.fourier F f.val,
      sLocalFourier_preserves_stage_of_different F S hDiff f.val f.property⟩
    ∀ n : ℕ, BddAbove
      ((fun z : ℂ ↦ ‖z ^ n * (m z * Z F S ω⁻¹ hS hω' μ f' (1 - z))‖) ''
        (Complex.re ⁻¹' Icc a d)) := by
  intro f'
  let R (z : ℂ) := 1 - z
  let b' : SchwartzBergman (univ : Set ℝ) :=
    ⟨fun z ↦ b.val (R z), schwartzBergmanSubmodule_reflect_one b.val b.property⟩
  have hm' : Differentiable ℂ (m ∘ R) :=
    hm.comp (by fun_prop : Differentiable ℂ (fun z : ℂ ↦ 1 - z))
  have hb' (z : ℂ) :
      (fun w ↦ (m ∘ R) w * globalZetaContinued F ν f'.val (compactIdeleClassCharacter F ω⁻¹) 0 w)
        =ᶠ[𝓝[≠] z] b'.val := by
    filter_upwards [(reflect_punctured z).eventually (hb (R z))] with w hw
    have he := globalZetaContinued_compact_functionalEquation F ν f.val ω (1 - w)
    rw [sub_sub_cancel] at he
    exact (congrArg (m (R w) * ·) he.symm).trans hw
  have hg := globalMellinMultiplier_rapid_on_stage F S ω⁻¹ hS hω' ν η μ hν
    f' hm' b' hb' (a := 1 - d) (d := 1 - a) (by linarith) (by linarith)
  intro n
  obtain ⟨B, hB⟩ := hg 0
  obtain ⟨C, hC⟩ := hg n
  refine ⟨2 ^ n * max B C, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  let w := R z
  let u := m z * Z F S ω⁻¹ hS hω' μ f' w
  have hw : w.re ∈ Icc (1 - d) (1 - a) := by
    simp only [w, R, Complex.sub_re, Complex.one_re]
    exact ⟨sub_le_sub_left hz.2 1, sub_le_sub_left hz.1 1⟩
  have hu₀ : ‖u‖ ≤ B := by
    have h := hB ⟨w, hw, rfl⟩
    change ‖w ^ (0 : ℕ) * (m (R w) * Z F S ω⁻¹ hS hω' μ f' w)‖ ≤ B at h
    simpa [R, w, u] using h
  have hu : ‖w ^ n * u‖ ≤ C := by
    have h := hC ⟨w, hw, rfl⟩
    change ‖w ^ n * (m (R w) * Z F S ω⁻¹ hS hω' μ f' w)‖ ≤ C at h
    simpa [R, w, u] using h
  have hnorm : ‖z‖ ≤ 2 * max 1 ‖w‖ := by
    have h := norm_sub_le (1 : ℂ) w
    rw [show (1 : ℂ) - w = z by simp [w, R], norm_one] at h
    exact h.trans (by linarith [le_max_left (1 : ℝ) ‖w‖, le_max_right (1 : ℝ) ‖w‖])
  change ‖z ^ n * u‖ ≤ _
  rw [norm_mul, norm_pow]
  calc
    _ ≤ (2 * max 1 ‖w‖) ^ n * ‖u‖ :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hnorm _) (norm_nonneg _)
    _ = 2 ^ n * ((max 1 ‖w‖) ^ n * ‖u‖) := by rw [mul_pow, mul_assoc]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      by_cases h : ‖w‖ ≤ 1
      · simpa only [max_eq_left h, one_pow, one_mul] using hu₀.trans (le_max_left B C)
      · rw [max_eq_right (le_of_not_ge h), ← norm_pow, ← norm_mul]
        exact hu.trans (le_max_right B C)

#print axioms globalMellinMultiplier_rapid_on_reflected_stage

end

end Masullo
