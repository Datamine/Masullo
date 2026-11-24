import HeckeDivisorSummability

open Complex Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped Classical NumberField Topology

namespace Masullo

noncomputable section

private abbrev CenteredTest := PositiveRealExponentialDecay (univ : Set ℝ)
private abbrev ordinate (y : ℝ) : ℂ := ⟨2,y⟩
private abbrev Φ (g : CenteredTest) (s : ℂ) := mellin (g.val ∘ Real.log) (s - 1 / 2)
private abbrev centeredWeight (g : CenteredTest) := mellinWeight (g.val ∘ Real.log) (-(1/2))

/-- A local gamma contribution to the centered formula, with the
Euler–Mascheroni contact term separated from the convergent integral. -/
def heckeCenteredGammaTerm (g : CenteredTest) (k P : ℝ) (b b' : ℂ) : ℂ :=
  (∫ x in Ioi (0 : ℝ), localGammaExplicitKernel k b b' (centeredWeight g) x) -
    2 * (k : ℂ) * ((Real.eulerMascheroniConstant : ℂ) + (Real.log P : ℂ)) * g.val 0

private def gammaLeg (g : CenteredTest) (k P : ℝ) (b b' : ℂ) (y : ℝ) : ℂ :=
  Φ g (ordinate y) * logDeriv (scaledGamma k P b) (ordinate y) +
    Φ g (1 - ordinate y) * logDeriv (scaledGamma k P b') (ordinate y)

private theorem gammaLeg_and_kernel_integral (g : CenteredTest) (k P : ℝ) (hk : 0 < k)
    (b b' : ℂ) (hb : 0 ≤ b.re) (hb' : 0 ≤ b'.re) :
    Integrable (gammaLeg g k P b b') ∧
      IntegrableOn (localGammaExplicitKernel k b b' (centeredWeight g)) (Ioi 0) ∧
      (∫ y, gammaLeg g k P b b' y) / (2 * (Real.pi : ℂ)) =
        heckeCenteredGammaTerm g k P b b' := by
  obtain ⟨hS, hC⟩ := exponentialLogProfile_mellinHypotheses g
  have hcont (u : ℝ) (hu : 0 < u) : ContinuousAt (centeredWeight g) u := by
    have hpower : ContinuousAt (fun x : ℝ => (x : ℂ) ^ (↑(-(1/2 : ℝ)) : ℂ)) u := by
      apply ContinuousAt.cpow continuous_ofReal.continuousAt continuousAt_const
      rwa [Complex.ofReal_mem_slitPlane]
    exact hpower.smul (hC u hu)
  have hM (s : ℂ) : mellin (centeredWeight g) s = Φ g s := by
    simp [centeredWeight, Φ, sub_eq_add_neg]
  have h1 : centeredWeight g 1 = g.val 0 := by simp [centeredWeight, mellinWeight]
  obtain ⟨hI, hK, hVal⟩ := localGamma_explicitContour (centeredWeight g)
    (fun σ => mellinSchwartzAt_weight (hS (σ - 1/2))) hcont k P 2 hk b b'
    (by linarith) (by linarith)
  have hOrd (y : ℝ) : ((2 : ℂ) + (y : ℂ) * I) = ordinate y := by
    apply Complex.ext <;> simp [Complex.add_re, Complex.mul_re, Complex.add_im, Complex.mul_im]
  refine ⟨?_, hK, ?_⟩
  · change Integrable (fun y : ℝ =>
      mellin (centeredWeight g) ((2 : ℂ) + (y : ℂ) * I) *
        logDeriv (scaledGamma k P b) ((2 : ℂ) + (y : ℂ) * I) +
      mellin (centeredWeight g) (1 - ((2 : ℂ) + (y : ℂ) * I)) *
        logDeriv (scaledGamma k P b') ((2 : ℂ) + (y : ℂ) * I)) at hI
    simp_rw [hOrd, hM] at hI
    exact hI
  · change (∫ y : ℝ, mellin (centeredWeight g) ((2 : ℂ) + (y : ℂ) * I) *
        logDeriv (scaledGamma k P b) ((2 : ℂ) + (y : ℂ) * I) +
      mellin (centeredWeight g) (1 - ((2 : ℂ) + (y : ℂ) * I)) *
        logDeriv (scaledGamma k P b') ((2 : ℂ) + (y : ℂ) * I)) / _ = _ at hVal
    simpa only [hOrd, hM, h1, heckeCenteredGammaTerm, gammaLeg] using hVal

/-- The compensated gamma kernel is absolutely integrable on the full
positive radial interval, including the singular endpoint. -/
theorem heckeCenteredGammaKernel_integrable (g : CenteredTest) (k : ℝ) (hk : 0 < k)
    (b b' : ℂ) (hb : 0 ≤ b.re) (hb' : 0 ≤ b'.re) :
    IntegrableOn (localGammaExplicitKernel k b b' (centeredWeight g)) (Ioi 0) :=
  (gammaLeg_and_kernel_integral g k 1 hk b b' hb hb').2.1

private theorem gammaLeg_integral (g : CenteredTest) (k P : ℝ) (hk : 0 < k)
    (b b' : ℂ) (hb : 0 ≤ b.re) (hb' : 0 ≤ b'.re) :
    Integrable (gammaLeg g k P b b') ∧
      (∫ y, gammaLeg g k P b b' y) / (2 * (Real.pi : ℂ)) =
        heckeCenteredGammaTerm g k P b b' := by
  obtain ⟨hI, _, hv⟩ := gammaLeg_and_kernel_integral g k P hk b b' hb hb'
  exact ⟨hI, hv⟩

variable (F : Type*) [Field F] [NumberField F]
private abbrev K := normOneIdeleClass F
private abbrev Place := HeightOneSpectrum (𝓞 F)
private abbrev R := {v : InfinitePlace F // v.IsReal}
private abbrev C := {v : InfinitePlace F // v.IsComplex}
variable (χ : PontryaginDual (IdeleClass F)) (S : Finset (Place F))
  (hs : Surjective (sIdeleClassInclusion F S))
  (hu : globalNormOneCharacter F (heckeNormOneRestriction F χ) ∈
    (sUnramified F S : Set (QuasiCharacter (IdeleClass F))))

/-- The centered prime-power sample with the two character weights. -/
def heckeCenteredPrimeTerm (g : CenteredTest) (j : Place F × ℕ) : ℂ :=
  let x := Real.log ((heckePrimePowerIdeal F j).absNorm : ℝ)
  let c := heckeEulerCoefficient F χ (chosenFiniteUniformizer F)
  let c' := heckeEulerCoefficient F χ⁻¹ (chosenFiniteUniformizer F)
  let p := (Real.log (j.1.asIdeal.absNorm : ℝ) : ℂ)
  exp (-(x : ℂ) / 2) *
    (c j.1 ^ (j.2+1) * p * g.val x + c' j.1 ^ (j.2+1) * p * g.val (-x))

private theorem primeLeg_integral (g : CenteredTest) :
    let P := fun y : ℝ =>
      Φ g (ordinate y) * logDeriv (manuscriptFiniteHeckeEuler F χ) (ordinate y) +
        Φ g (1 - ordinate y) * logDeriv (manuscriptFiniteHeckeEuler F χ⁻¹) (ordinate y)
    Integrable P ∧ Summable (fun j => ‖heckeCenteredPrimeTerm F χ g j‖) ∧
      (∫ y : ℝ, P y) / (2 * (Real.pi : ℂ)) = -(∑' j, heckeCenteredPrimeTerm F χ g j) := by
  intro P
  obtain ⟨hI,hAbs,hS⟩ := manuscriptFiniteHecke_centeredExplicitContour F χ g (a := 2) (by norm_num)
  have hOrd (y : ℝ) : ((2 : ℂ) + (y : ℂ) * I) = ordinate y := by
    apply Complex.ext <;> simp [Complex.add_re, Complex.mul_re, Complex.add_im, Complex.mul_im]
  have hRef (y : ℝ) : (1 / 2 : ℂ) - ordinate y = 1 - ordinate y - 1 / 2 := by ring
  change Integrable (fun y : ℝ =>
    Φ g ((2 : ℂ) + (y : ℂ) * I) * logDeriv (manuscriptFiniteHeckeEuler F χ) ((2 : ℂ) + (y : ℂ) * I) +
    mellin (g.val ∘ Real.log) (1 / 2 - ((2 : ℂ) + (y : ℂ) * I)) *
      logDeriv (manuscriptFiniteHeckeEuler F χ⁻¹) ((2 : ℂ) + (y : ℂ) * I)) at hI
  simp_rw [hOrd, hRef] at hI
  change HasSum (heckeCenteredPrimeTerm F χ g)
    (-(∫ y : ℝ,
      Φ g ((2 : ℂ) + (y : ℂ) * I) * logDeriv (manuscriptFiniteHeckeEuler F χ) ((2 : ℂ) + (y : ℂ) * I) +
      mellin (g.val ∘ Real.log) (1 / 2 - ((2 : ℂ) + (y : ℂ) * I)) *
        logDeriv (manuscriptFiniteHeckeEuler F χ⁻¹) ((2 : ℂ) + (y : ℂ) * I)) / (2 * (Real.pi : ℂ))) at hS
  simp_rw [hOrd, hRef] at hS
  refine ⟨hI, hAbs, ?_⟩
  have h := congrArg Neg.neg hS.tsum_eq
  rw [neg_div, neg_neg] at h
  exact h.symm

variable (U : Finset (Place F)) (hU : Surjective (sIdeleClassInclusion F U))
  (hUχ : globalNormOneCharacter F (heckeNormOneRestriction F χ⁻¹) ∈
    (sUnramified F U : Set (QuasiCharacter (IdeleClass F))))

/-- The sum of the corrected real and complex gamma contributions. -/
def heckeCenteredArchTerm (t : ℝ) (g : CenteredTest) : ℂ :=
  (∑ v : R F, heckeCenteredGammaTerm g (1 / 2) Real.pi
    (manuscriptHeckeRealGammaShift F χ S hs hu t v)
    (manuscriptHeckeRealGammaShift F χ⁻¹ U hU hUχ (-t) v)) +
  ∑ v : C F, heckeCenteredGammaTerm g 1 (2 * Real.pi)
    (manuscriptHeckeComplexGammaShift F χ S hs hu t v)
    (manuscriptHeckeComplexGammaShift F χ⁻¹ U hU hUχ (-t) v)

private theorem archLeg_integral (t : ℝ) (g : CenteredTest) :
    let H := fun y : ℝ =>
      Φ g (ordinate y) * logDeriv (manuscriptHeckeArchGamma F χ S hs hu t) (ordinate y) +
        Φ g (1 - ordinate y) * logDeriv (manuscriptHeckeArchGamma F χ⁻¹ U hU hUχ (-t)) (ordinate y)
    Integrable H ∧
      (∫ y : ℝ, H y) / (2 * (Real.pi : ℂ)) = heckeCenteredArchTerm F χ S hs hu U hU hUχ t g := by
  intro H
  let G (v : R F) := gammaLeg g (1 / 2) Real.pi
    (manuscriptHeckeRealGammaShift F χ S hs hu t v)
    (manuscriptHeckeRealGammaShift F χ⁻¹ U hU hUχ (-t) v)
  let J (v : C F) := gammaLeg g 1 (2 * Real.pi)
    (manuscriptHeckeComplexGammaShift F χ S hs hu t v)
    (manuscriptHeckeComplexGammaShift F χ⁻¹ U hU hUχ (-t) v)
  have hG (v : R F) := gammaLeg_integral g (1 / 2) Real.pi (by norm_num) _ _
    (manuscriptHeckeRealGammaShift_re_nonneg F χ S hs hu t v)
    (manuscriptHeckeRealGammaShift_re_nonneg F χ⁻¹ U hU hUχ (-t) v)
  have hJ (v : C F) := gammaLeg_integral g 1 (2 * Real.pi) one_pos _ _
    (manuscriptHeckeComplexGammaShift_re_nonneg F χ S hs hu t v)
    (manuscriptHeckeComplexGammaShift_re_nonneg F χ⁻¹ U hU hUχ (-t) v)
  have heq : H = fun y => (∑ i, G i y) + ∑ i, J i y := by
    funext y
    dsimp only [H]
    have hz : 0 < (ordinate y).re := by norm_num [ordinate]
    rw [manuscriptHeckeArchGamma_right_logDeriv_sum F χ S hs hu t hz,
      manuscriptHeckeArchGamma_right_logDeriv_sum F χ⁻¹ U hU hUχ (-t) hz]
    simp only [G, J, gammaLeg, mul_add, Finset.mul_sum, Finset.sum_add_distrib]
    ring
  have hGi : Integrable (fun y => ∑ v, G v y) := integrable_finsetSum _ fun v _ => (hG v).1
  have hJi : Integrable (fun y => ∑ v, J v y) := integrable_finsetSum _ fun v _ => (hJ v).1
  refine ⟨heq ▸ hGi.add hJi, ?_⟩
  rw [heq, integral_add hGi hJi, add_div,
    integral_finsetSum _ (fun v _ => (hG v).1), integral_finsetSum _ (fun v _ => (hJ v).1),
    Finset.sum_div, Finset.sum_div]
  unfold heckeCenteredArchTerm
  exact congrArg₂ (· + ·) (Finset.sum_congr rfl (fun v _ => (hG v).2))
    (Finset.sum_congr rfl (fun v _ => (hJ v).2))

local instance explicitFormulaNormOneMeasurable : MeasurableSpace (K F) := borel _
local instance explicitFormulaNormOneBorel : BorelSpace (K F) := ⟨rfl⟩
local instance explicitFormulaIdeleMeasurable : MeasurableSpace (Idele F) := borel _
local instance explicitFormulaIdeleBorel : BorelSpace (Idele F) := ⟨rfl⟩

variable (ν : Measure (K F)) [ν.IsHaarMeasure]
variable (η : Measure (Idele F)) [η.IsHaarMeasure]
variable [∀ v : Place F, MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : Place F, BorelSpace (v.adicCompletion F)ˣ]
  (μ : ∀ v : Place F, Measure (v.adicCompletion F)ˣ)
  [∀ v : Place F, (μ v).IsHaarMeasure] [∀ v : Place F, SigmaFinite (μ v)]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]
variable (hν : IsWeilQuotientMeasure (principalIdeles F) η Measure.count (globalClassMeasure F ν))

include μ hν in
/-- The signed divisor uses positive zero multiplicity and the two actual
simple poles, which occur only for a pure norm twist. -/
theorem manuscriptCompletedHecke_divisor_zero_and_pole_weights
    {t : ℝ} (ht : HasHeckeHeight F χ t) (L : ℂ → ℂ) (hL : MeromorphicOn L univ)
    (he : EqOn L (manuscriptCompletedHeckeEuler F χ S hs hu t) {z | 1 < z.re}) (p : ℂ) :
    let d := MeromorphicOn.divisor L univ p
    let b := (t : ℂ) * I
    d = max d 0 -
      (if heckeNormOneRestriction F χ = 1 ∧ (p = b ∨ p = 1 + b) then (1 : ℤ) else 0) := by
  obtain ⟨_, _, _, M, _, _, hM, _, hMe, _, hEntire, hPole, _⟩ :=
    manuscriptHecke_regularities F χ S hs hu η ν μ hν t ht
  let b := (t : ℂ) * I
  let d := MeromorphicOn.divisor L univ p
  have heq := meromorphicOrderAt_congr (globalHeckeContinuation_unique_germ hL hM he hMe p)
  change d = max d 0 -
    (if heckeNormOneRestriction F χ = 1 ∧ (p = b ∨ p = 1 + b) then (1 : ℤ) else 0)
  split_ifs with h
  · obtain ⟨hw, rfl | rfl⟩ := h
    · have hd : d = -1 := by
        dsimp only [d]
        rw [hL.divisor_apply (mem_univ _), heq, (hPole hw).1]
        rfl
      norm_num [hd]
    · have hd : d = -1 := by
        dsimp only [d]
        rw [hL.divisor_apply (mem_univ _), heq, (hPole hw).2.1]
        rfl
      norm_num [hd]
  · have hA : AnalyticAt ℂ M p := by
      by_cases hw : heckeNormOneRestriction F χ = 1
      · exact (hPole hw).2.2.1 p (fun hp => h ⟨hw, Or.inl hp⟩) (fun hp => h ⟨hw, Or.inr hp⟩)
      · exact hEntire hw p (mem_univ _)
    have hn : 0 ≤ d := by
      dsimp only [d]
      rw [hL.divisor_apply (mem_univ p), heq]
      exact WithTop.untop₀_nonneg.mpr hA.meromorphicOrderAt_nonneg
    rw [max_eq_left hn, sub_zero]

set_option maxHeartbeats 650000 in
include μ hν in
/-- Corrected B.4.2.2. In the actual character chart, the signed,
multiplicity-weighted divisor sum equals the discriminant–conductor
contact term, minus the prime-power sum, plus the compensated gamma integrals. -/
theorem manuscriptCompletedHecke_explicitFormula {t : ℝ} (ht : HasHeckeHeight F χ t)
    (g : CenteredTest) :
    ∃ (L : ℂ → ℂ) (U : Finset (Place F)) (hU : Surjective (sIdeleClassInclusion F U))
      (hUχ : globalNormOneCharacter F (heckeNormOneRestriction F χ⁻¹) ∈
        (sUnramified F U : Set (QuasiCharacter (IdeleClass F)))),
      MeromorphicNFOn L univ ∧
      EqOn L (manuscriptCompletedHeckeEuler F χ S hs hu t) {z | 1 < z.re} ∧
      (∀ p : ℂ, let d := MeromorphicOn.divisor L univ p
        let b := (t : ℂ) * I
        d = max d 0 -
          (if heckeNormOneRestriction F χ = 1 ∧ (p = b ∨ p = 1 + b) then (1 : ℤ) else 0)) ∧
      Summable (fun z => ‖(MeromorphicOn.divisor L univ z : ℂ) * Φ g z‖) ∧
      Summable (fun j => ‖heckeCenteredPrimeTerm F χ g j‖) ∧
      HasSum (fun z => (MeromorphicOn.divisor L univ z : ℂ) * Φ g z)
        ((Real.log (heckeDiscriminantConductor F χ) : ℂ) * g.val 0 -
          (∑' j, heckeCenteredPrimeTerm F χ g j) +
          heckeCenteredArchTerm F χ S hs hu U hU hUχ t g) := by
  obtain ⟨L, U, hU, hUχ, V, hL, hV, hLe, hVe, hAbs, _, _, hSum⟩ :=
    exists_manuscriptCompletedHecke_reflected_divisor_contour F χ S hs hu ν η μ hν ht g
  obtain ⟨hPi, hPAbs, hP⟩ := primeLeg_integral F χ g
  obtain ⟨hGi, hG⟩ := archLeg_integral F χ S hs hu U hU hUχ t g
  refine ⟨L, U, hU, hUχ, hL, hLe,
    manuscriptCompletedHecke_divisor_zero_and_pole_weights F χ S hs hu ν η μ hν ht L hL.meromorphicOn hLe,
    hAbs, hPAbs, ?_⟩
  let P (y : ℝ) :=
    Φ g (ordinate y) * logDeriv (manuscriptFiniteHeckeEuler F χ) (ordinate y) +
      Φ g (1 - ordinate y) * logDeriv (manuscriptFiniteHeckeEuler F χ⁻¹) (ordinate y)
  let G (y : ℝ) :=
    Φ g (ordinate y) * logDeriv (manuscriptHeckeArchGamma F χ S hs hu t) (ordinate y) +
      Φ g (1 - ordinate y) * logDeriv (manuscriptHeckeArchGamma F χ⁻¹ U hU hUχ (-t)) (ordinate y)
  have heq (y : ℝ) :
      Φ g (ordinate y) * logDeriv L (ordinate y) +
        Φ g (1 - ordinate y) * logDeriv V (ordinate y) = P y + G y := by
    rw [manuscriptCompletedHecke_right_logDeriv_split F χ S hs hu ν η μ hν t L hLe
        (by norm_num [ordinate]),
      manuscriptCompletedHecke_right_logDeriv_split F χ⁻¹ U hU hUχ ν η μ hν (-t) V hVe
        (by norm_num [ordinate])]
    dsimp only [P, G]
    ring
  change HasSum _ (((∫ y : ℝ, Φ g (ordinate y) * logDeriv L (ordinate y) +
    Φ g (1 - ordinate y) * logDeriv V (ordinate y)) / (2 * (Real.pi : ℂ))) + _) at hSum
  rw [show (fun y : ℝ => Φ g (ordinate y) * logDeriv L (ordinate y) +
      Φ g (1 - ordinate y) * logDeriv V (ordinate y)) = (fun y => P y + G y) from funext heq,
    integral_add hPi hGi, add_div, hP, hG] at hSum
  convert hSum using 1
  ring

end

end Masullo
