import IdelicWeilArchRadial
import IdelicWeilCharacterSynthesis
import RealWeilRadialCutoff

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical NumberField SchwartzMap

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

local instance : LocallyCompactSpace (IdeleClass F) := ideleClasses_locallyCompact
local instance : T2Space (IdeleClass F) := ideleClasses_hausdorff

private abbrev RealPlace := {v : InfinitePlace F // v.IsReal}

private def realWeilIdelicShiftedTest (f : BruhatCompactTest (IdeleClass F))
    (v : RealPlace F) : 𝓢(ℝ, ℂ) :=
  archWeilShiftedTest 1 (f.val.val ∘ realPlaceWeilInsertion F v.val v.property)
    (realPlaceWeilTest_hasCompactSupport F f v.val v.property)
    (realPlaceWeilTest_smooth F f v.val v.property)

private theorem realWeilIdelicShiftedTest_zero (f : BruhatCompactTest (IdeleClass F))
    (v : RealPlace F) : realWeilIdelicShiftedTest F f v 0 = f.val.val 1 := by
  simp [realWeilIdelicShiftedTest]

private theorem realWeilIdelicShiftedTest_signs (f : BruhatCompactTest (IdeleClass F))
    (v : RealPlace F) (r : ℝ) (hr : 0 < r) :
    let h := realWeilIdelicShiftedTest F f v
    (r / 2 : ℝ) • (‖1 - r‖⁻¹ • h (1 - r) + ‖1 + r‖⁻¹ • h (1 + r)) =
      idelicWeilRealRadialSlice F f v r hr := by
  let u : ℝˣ := Units.mk0 r hr.ne'
  have hpos : archWeilZeroExtension (f.val.val ∘ realPlaceWeilInsertion F v.val v.property) r =
      f.val.val (realPlaceWeilInsertion F v.val v.property u) :=
    archWeilZeroExtension_unit _ u
  have hneg : archWeilZeroExtension (f.val.val ∘ realPlaceWeilInsertion F v.val v.property) (-r) =
      f.val.val (realPlaceWeilInsertion F v.val v.property (-u)) :=
    archWeilZeroExtension_unit _ (-u)
  dsimp only [realWeilIdelicShiftedTest]
  rw [archWeilShiftedTest_apply, archWeilShiftedTest_apply, sub_sub_cancel,
    show 1 - (1 + r) = -r by ring, hpos, hneg, norm_neg, Real.norm_of_nonneg hr.le]
  simp only [idelicWeilRealRadialSlice, Real.norm_eq_abs, Nat.cast_one]
  have hpow : r * r ^ (-(1 : ℝ) / 2) = r ^ (1 / 2 : ℝ) := by
    nth_rw 1 [← Real.rpow_one r]
    rw [← Real.rpow_add hr]
    congr 1
    ring
  have hpow' : (r : ℂ) * (r ^ (-(1 : ℝ) / 2) : ℝ) = (r ^ (1 / 2 : ℝ) : ℝ) := by
    exact_mod_cast hpow
  simp only [Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_div, Complex.ofReal_ofNat]
  rw [← hpow']
  ring

/-- The normalized real radial kernel before subtracting its identity term. -/
def idelicWeilRealRadialDensity (f : BruhatCompactTest (IdeleClass F))
    (v : RealPlace F) (t : ℝ) : ℂ :=
  (2 : ℝ)⁻¹ •
    (idelicWeilRealRadialSlice F f v (Real.exp (t / 2)) (Real.exp_pos _) +
      idelicWeilRealRadialSlice F f v (Real.exp (-t / 2)) (Real.exp_pos _))

/-- On an actual idelic test, the normalized logarithmic radial finite part
has the same geometric local term with the real gamma contact constant removed. -/
theorem realPlaceIdelicWeil_radialCutoff_tendsto (f : BruhatCompactTest (IdeleClass F))
    (v : RealPlace F) :
    Tendsto (fun δ : ℝ => (∫ t in Ioi δ, idelicWeilRealRadialDensity F f v t) +
      Real.log δ • f.val.val 1) (𝓝[>] 0)
      (𝓝 (realPlaceIdelicWeilTerm F f v.val v.property -
        (Real.eulerMascheroniConstant + Real.log Real.pi) • f.val.val 1)) := by
  let h := realWeilIdelicShiftedTest F f v
  have hz : h 0 = f.val.val 1 := realWeilIdelicShiftedTest_zero F f v
  have hp : realWeilShiftedRadial h = fun t =>
      idelicWeilRealRadialSlice F f v (Real.exp (t / 2)) (Real.exp_pos _) +
        idelicWeilRealRadialSlice F f v (Real.exp (-t / 2)) (Real.exp_pos _) := by
    funext t
    exact congrArg₂ (· + ·)
      (realWeilIdelicShiftedTest_signs F f v _ (Real.exp_pos (t / 2)))
      (realWeilIdelicShiftedTest_signs F f v _ (Real.exp_pos (-t / 2)))
  have ht : realPlaceIdelicWeilTerm F f v.val v.property =
      -realLogFourierDistribution h := rfl
  rw [ht, realLogFourierDistribution_apply, realLogFourierPairing_eq_finitePart,
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero, ← hz]
  convert realWeil_radialCutoff_tendsto h using 1
  · funext δ
    unfold idelicWeilRealRadialDensity
    rw [hp, integral_smul]
  · congr 1
    simp only [neg_sub, neg_smul, add_smul]
    abel

/-- An integrable, identity-subtracted real radial density computes the real
idelic Weil term with its finite gamma contact constant. -/
theorem realPlaceIdelicWeilTerm_eq_radialIntegral (f : BruhatCompactTest (IdeleClass F))
    (v : RealPlace F)
    (hf : IntegrableOn (fun t : ℝ => idelicWeilRealRadialDensity F f v t -
      (Real.exp (-t) / (1 - Real.exp (-t))) • f.val.val 1) (Ioi 0)) :
    realPlaceIdelicWeilTerm F f v.val v.property =
      (∫ t in Ioi (0 : ℝ), idelicWeilRealRadialDensity F f v t -
        (Real.exp (-t) / (1 - Real.exp (-t))) • f.val.val 1) +
      (Real.eulerMascheroniConstant + Real.log Real.pi) • f.val.val 1 := by
  have he := tendsto_nhds_unique (realPlaceIdelicWeil_radialCutoff_tendsto F f v)
    (idelicWeil_radialFinitePart_tendsto (idelicWeilRealRadialDensity F f v) (f.val.val 1) hf)
  exact sub_eq_iff_eq_add.mp he

private abbrev K := normOneIdeleClass F
private abbrev Place := HeightOneSpectrum (𝓞 F)
private abbrev χ (w : PontryaginDual (K F)) := heckeOrdinateCharacter F w 0

local instance : MeasurableSpace (K F) := borel _
local instance : BorelSpace (K F) := ⟨rfl⟩

variable (ν : Measure (K F)) [ν.IsHaarMeasure]
  (E : ∀ w : PontryaginDual (K F), CompletedHeckeChart F w)
  (T : PontryaginDual (K F) → Finset (Place F))
  (hT : ∀ w, Surjective (sIdeleClassInclusion F (T w)))
  (huT : ∀ w, globalNormOneCharacter F (heckeNormOneRestriction F (χ F w)⁻¹) ∈
    (sUnramified F (T w) : Set (QuasiCharacter (IdeleClass F))))

private theorem realForward_unramified (w : PontryaginDual (K F)) :
    globalNormOneCharacter F (heckeNormOneRestriction F (χ F w)) ∈
      (sUnramified F (E w).stage : Set (QuasiCharacter (IdeleClass F))) := by
  rw [heckeNormOneRestriction_ordinateCharacter]
  exact (E w).unramified

private abbrev b (v : RealPlace F) (w : PontryaginDual (K F)) :=
  manuscriptHeckeRealGammaShift F (χ F w) (E w).stage (E w).surj
    (realForward_unramified F E w) 0 v

private abbrev b' (v : RealPlace F) (w : PontryaginDual (K F)) :=
  manuscriptHeckeRealGammaShift F (χ F w)⁻¹ (T w) (hT w) (huT w) 0 v

set_option maxHeartbeats 1200000 in
/-- A single real character component contributes precisely its signed
centered gamma term, including the contact term. -/
theorem realPlaceIdelicWeilTerm_characterComponent
    (f p : BruhatCompactTest (IdeleClass F)) (v : RealPlace F) (w : PontryaginDual (K F))
    (hp : ∀ x : IdeleClass F, p.val.val x =
      ((ν.real univ : ℂ)⁻¹ * idelicWeilLogProfile F ν w f (ideleClassLogNorm F x).toAdd) *
        (((normOneEulerCharacter F w x)⁻¹ : Circle) : ℂ)) :
    realPlaceIdelicWeilTerm F p v.val v.property =
      -(ν.real univ : ℂ)⁻¹ * heckeCenteredGammaTerm (idelicWeilCenteredTest F ν w f)
        (1 / 2) Real.pi (b F E v w) (b' F T hT huT v w) := by
  let d (t : ℝ) := idelicWeilRealRadialDensity F p v t -
    (Real.exp (-t) / (1 - Real.exp (-t))) • p.val.val 1
  let L (ψ : PontryaginDual (K F)) (q : ℝ → ℂ) :=
    localGammaExplicitKernel (1 / 2) (b F E v ψ) (b' F T hT huT v ψ)
      (mellinWeight (q ∘ Real.log) (-(1 / 2)))
  let A := -(ν.real univ : ℂ)⁻¹
  let g := idelicWeilLogProfile F ν w f
  have hd (t : ℝ) (ht : 0 < t) : d t = A * L w g t := by
    have hs := idelicWeil_realGammaKernel_hasSum F ν E T hT huT p v ht
    change HasSum (fun ψ => A * L ψ (idelicWeilLogProfile F ν ψ p) t) _ at hs
    have hs' : HasSum (fun ψ => if ψ = w then A * L w g t else 0) (d t) := by
      convert hs using 1
      · funext ψ
        have hq : idelicWeilLogProfile F ν ψ p = fun u => if ψ = w then g u else 0 :=
          funext fun u => idelicWeilLogProfile_characterComponent F ν f p w hp ψ u
        rw [hq]
        by_cases h : ψ = w
        · subst ψ
          simp
        · simp only [ite_eq_right h, L, localGammaExplicitKernel_centered_log, mul_zero, sub_zero,
            zero_mul, zero_div]
      · simp only [d, idelicWeilRealRadialDensity, Complex.real_smul, Complex.ofReal_inv,
          Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_exp, Complex.ofReal_neg,
          Complex.ofReal_one, Complex.ofReal_ofNat]
        ring
    exact hs'.unique (hasSum_ite_eq w (A * L w g t))
  have hi : IntegrableOn (L w g) (Ioi 0) :=
    heckeCenteredGammaKernel_integrable (idelicWeilCenteredTest F ν w f) (1 / 2)
      (by norm_num) _ _
      (manuscriptHeckeRealGammaShift_re_nonneg F (χ F w) _ _ _ 0 v)
      (manuscriptHeckeRealGammaShift_re_nonneg F (χ F w)⁻¹ _ _ _ 0 v)
  have hscaled : IntegrableOn (fun t => A * L w g t) (Ioi 0) := hi.const_mul A
  have hdi : IntegrableOn d (Ioi 0) :=
    hscaled.congr_fun (fun t ht => (hd t ht).symm) measurableSet_Ioi
  have hc : p.val.val 1 = -A * g 0 := by
    rw [hp]
    simp [A, g]
  rw [realPlaceIdelicWeilTerm_eq_radialIntegral F p v hdi]
  change (∫ t in Ioi (0 : ℝ), d t) +
    (Real.eulerMascheroniConstant + Real.log Real.pi) • p.val.val 1 = _
  rw [setIntegral_congr_fun measurableSet_Ioi (fun t ht => hd t ht), integral_const_mul, hc]
  change A * (∫ t in Ioi (0 : ℝ), L w g t) +
    (Real.eulerMascheroniConstant + Real.log Real.pi) • (-A * g 0) =
      A * ((∫ t in Ioi (0 : ℝ), L w g t) -
        2 * ((1 / 2 : ℝ) : ℂ) * ((Real.eulerMascheroniConstant : ℂ) + (Real.log Real.pi : ℂ)) * g 0)
  simp only [Complex.real_smul, Complex.ofReal_add, Complex.ofReal_div, Complex.ofReal_one,
    Complex.ofReal_ofNat]
  ring

/-- The centered gamma contributions sum unconditionally to the signed
geometric real-place term. -/
theorem idelicWeil_realComparison_hasSum (f : BruhatCompactTest (IdeleClass F))
    (v : RealPlace F) :
    HasSum (fun w : PontryaginDual (K F) =>
      (ν.real univ : ℂ)⁻¹ * heckeCenteredGammaTerm (idelicWeilCenteredTest F ν w f)
        (1 / 2) Real.pi (b F E v w) (b' F T hT huT v w))
      (-realPlaceIdelicWeilTerm F f v.val v.property) := by
  obtain ⟨P, hP, hsum, _⟩ := exists_idelicWeil_infinite_characterSynthesis F ν f
  have hs := (hsum v.val).neg
  simp only [infinitePlaceIdelicWeilDual_apply_real F v.val v.property] at hs
  refine hs.congr_fun fun w => ?_
  rw [realPlaceIdelicWeilTerm_characterComponent F ν E T hT huT f (P w) v w (hP w),
    neg_mul, neg_neg]

end
end Masullo
