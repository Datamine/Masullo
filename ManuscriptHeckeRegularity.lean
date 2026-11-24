import GlobalHeckeResidues
import ManuscriptHeckeCharacterChart

open Filter Function Ideal IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical NumberField

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]
private abbrev K := normOneIdeleClass F
private abbrev Place := HeightOneSpectrum (𝓞 F)

private abbrev iHeight (t : ℝ) : ℂ := (t : ℂ) * Complex.I

variable (χ : PontryaginDual (IdeleClass F))
variable (S : Finset (Place F)) (hs : Surjective (sIdeleClassInclusion F S))
variable (hu : globalNormOneCharacter F (heckeNormOneRestriction F χ) ∈
  (sUnramified F S : Set (QuasiCharacter (IdeleClass F))))

private abbrev archPhase :=
  sLocalNormOneCharacterOfGlobal F (heckeNormOneRestriction F χ) S hs hu

private abbrev complexGammaScale := (2 : ℂ)⁻¹ ^ InfinitePlace.nrComplexPlaces F

private theorem complexGammaScale_ne_zero : complexGammaScale F ≠ 0 :=
  pow_ne_zero _ (inv_ne_zero (by norm_num))

/-- The displayed Euler product uses the actual finite values of the unitary
character and half of Deligne's gamma factor at each complex place. The
archimedean exponents are recovered from the norm-one chart and its height. -/
def manuscriptCompletedHeckeEuler (t : ℝ) (s : ℂ) : ℂ :=
  complexGammaScale F *
    ((archimedeanNumberFieldZetaDenominator F
      (sLocalRealArchParameters F S (archPhase F χ S hs hu))
      (sLocalComplexArchParameters F S (archPhase F χ S hs hu)) (s - iHeight t))⁻¹ *
      manuscriptFiniteHeckeEuler F χ s)

/-- The shifted archimedean exponents and sign or angular indices represent
the weight of the actual character on the archimedean coordinate group. -/
theorem manuscriptHecke_archWeight (t : ℝ) (ht : HasHeckeHeight F χ t)
    (a : (InfiniteAdeleRing F)ˣ) (s : ℂ) :
    let p := infiniteAdeleUnitsCoordinates F a
    (χ (ideleClassMap F (archIntoIdeles F a)) : ℂ) * Complex.exp (s * (Real.log ‖a.val‖ : ℂ)) =
      (∏ v : {v : InfinitePlace F // v.IsReal},
        sLocalRealArchWeight F S (archPhase F χ S hs hu) v (s - iHeight t) (p.1 v)) *
      ∏ v : {v : InfinitePlace F // v.IsComplex},
        sLocalComplexArchWeight F S (archPhase F χ S hs hu) v (s - iHeight t) (p.2 v) := by
  intro p
  rw [← sLocalArchZetaWeight_eq_product F S, sLocalZetaWeight_global_arch_apply F S]
  have hn : Real.log (ideleClassNorm F (ideleClassMap F (archIntoIdeles F a))) =
      Real.log ‖a.val‖ := by
    rw [ideleClassNorm_mk]
    have hh := archIntoIdeles_logNorm F a
    rw [infiniteIdeleLogNorm_eq] at hh
    exact congrArg Multiplicative.toAdd hh
  rw [ht, hn, sub_mul, sub_eq_add_neg, Complex.exp_add]
  change (_ * _) * _ = _ * (normOneEulerCharacter F (heckeNormOneRestriction F χ)
    (ideleClassMap F (archIntoIdeles F a)) : ℂ)
  rw [neg_mul]
  ring

theorem manuscriptCompletedHeckeEuler_shift (t : ℝ) (ht : HasHeckeHeight F χ t) (s : ℂ) :
    manuscriptCompletedHeckeEuler F χ S hs hu t s =
      complexGammaScale F *
        globalCompletedHeckeEuler F (heckeNormOneRestriction F χ) S hs hu (s - iHeight t) := by
  rw [manuscriptCompletedHeckeEuler, manuscriptFiniteHeckeEuler_shift F χ ht]
  rfl

theorem manuscriptCompletedHeckeEuler_stage_eq (t : ℝ) (ht : HasHeckeHeight F χ t)
    (T : Finset (Place F)) (hT : Surjective (sIdeleClassInclusion F T))
    (huT : globalNormOneCharacter F (heckeNormOneRestriction F χ) ∈
      (sUnramified F T : Set (QuasiCharacter (IdeleClass F)))) :
    manuscriptCompletedHeckeEuler F χ S hs hu t = manuscriptCompletedHeckeEuler F χ T hT huT t := by
  funext z
  rw [manuscriptCompletedHeckeEuler_shift F χ S hs hu t ht,
    manuscriptCompletedHeckeEuler_shift F χ T hT huT t ht,
    globalCompletedHeckeEuler_stage_eq F (heckeNormOneRestriction F χ) S hs hu T hT huT]

theorem tendsto_sub_punctured (b p : ℂ) :
    Tendsto (fun z : ℂ ↦ z - b) (𝓝[≠] (p + b)) (𝓝[≠] p) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · have h : Continuous (fun z : ℂ ↦ z - b) := continuous_id.sub continuous_const
    simpa only [add_sub_cancel_right] using
      (h.continuousAt (x := p + b)).tendsto.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with z hz
    change z - b ≠ p
    intro he
    exact hz (sub_eq_iff_eq_add.mp he)

private abbrev shifted (t : ℝ) (L : ℂ → ℂ) (z : ℂ) :=
  complexGammaScale F * L (z - iHeight t)

private theorem shifted_analytic {L : ℂ → ℂ} (t : ℝ) {z : ℂ}
    (h : AnalyticAt ℂ L (z - iHeight t)) : AnalyticAt ℂ (shifted F t L) z :=
  analyticAt_const.mul (h.comp (f := fun w : ℂ ↦ w - iHeight t)
    (analyticAt_id.sub analyticAt_const))

private theorem shifted_meromorphic {L : ℂ → ℂ} (t : ℝ) (h : MeromorphicOn L univ) :
    MeromorphicOn (shifted F t L) univ := fun z _ ↦
  (MeromorphicAt.const _ z).mul ((h _ (mem_univ _)).comp_analyticAt
    (g := fun w : ℂ ↦ w - iHeight t) (analyticAt_id.sub analyticAt_const))

private theorem shifted_order {L : ℂ → ℂ} (t : ℝ) (h : MeromorphicOn L univ) (z : ℂ) :
    meromorphicOrderAt (shifted F t L) z = meromorphicOrderAt L (z - iHeight t) := by
  let q (w : ℂ) := w - iHeight t
  have hq : AnalyticAt ℂ q z := analyticAt_id.sub analyticAt_const
  have hd : deriv q z ≠ 0 := by simp [q]
  change meromorphicOrderAt ((fun _ : ℂ ↦ complexGammaScale F) * (L ∘ q)) z = _
  rw [meromorphicOrderAt_mul (MeromorphicAt.const _ _) ((h _ (mem_univ _)).comp_analyticAt hq),
    meromorphicOrderAt_const, ite_eq_right (complexGammaScale_ne_zero F), zero_add,
    meromorphicOrderAt_comp_of_deriv_ne_zero hq hd]

private theorem shifted_residue {L : ℂ → ℂ} (t : ℝ) {p c : ℂ}
    (h : Tendsto (fun z : ℂ ↦ (z - p) * L z) (𝓝[≠] p) (𝓝 c)) :
    Tendsto (fun z : ℂ ↦ (z - (p + iHeight t)) * shifted F t L z)
      (𝓝[≠] (p + iHeight t)) (𝓝 (complexGammaScale F * c)) := by
  apply ((h.comp (tendsto_sub_punctured (iHeight t) p)).const_mul (complexGammaScale F)).congr'
  exact Eventually.of_forall fun z ↦ by dsimp only [Function.comp_apply, shifted]; ring

private theorem shifted_re (z : ℂ) (t : ℝ) : (z - iHeight t).re = z.re := by
  simp [Complex.sub_re, Complex.mul_re]

private abbrev canonicalResidueOne :=
  (1 / (Real.pi : ℂ)) ^ InfinitePlace.nrComplexPlaces F * (dedekindZeta_residue F : ℂ)

private abbrev manuscriptResidueOne :=
  ((2 * (Real.pi : ℂ))⁻¹) ^ InfinitePlace.nrComplexPlaces F * (dedekindZeta_residue F : ℂ)

private theorem scale_residue_one :
    complexGammaScale F * canonicalResidueOne F = manuscriptResidueOne F := by
  simp only [complexGammaScale, canonicalResidueOne, manuscriptResidueOne, one_div]
  rw [← mul_assoc, ← mul_pow, ← mul_inv]

local instance : MeasurableSpace (Idele F) := borel _
local instance : BorelSpace (Idele F) := ⟨rfl⟩
local instance : MeasurableSpace (K F) := borel _
local instance : BorelSpace (K F) := ⟨rfl⟩

variable (η : Measure (Idele F)) [η.IsHaarMeasure]
variable (ν : Measure (K F)) [ν.IsHaarMeasure]
variable [∀ v : Place F, MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : Place F, BorelSpace (v.adicCompletion F)ˣ]
  (μ : ∀ v : Place F, Measure (v.adicCompletion F)ˣ)
  [∀ v : Place F, (μ v).IsHaarMeasure] [∀ v : Place F, SigmaFinite (μ v)]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]
variable (hν : IsWeilQuotientMeasure (principalIdeles F) η Measure.count (globalClassMeasure F ν))

include μ hν in
private theorem canonical_trivial_residues_of_continuation
    (ω₀ : PontryaginDual (K F)) (hω₀ : ω₀ = 1)
    (S₀ : Finset (Place F)) (hs₀ : Surjective (sIdeleClassInclusion F S₀))
    (hu₀ : globalNormOneCharacter F ω₀ ∈ (sUnramified F S₀ : Set (QuasiCharacter (IdeleClass F))))
    {L : ℂ → ℂ} (hm : MeromorphicOn L univ)
    (he : EqOn L (globalCompletedHeckeEuler F ω₀ S₀ hs₀ hu₀) {z | 1 < z.re}) :
    let d : ℝ := Real.sqrt ((differentIdeal ℤ (𝓞 F)).absNorm : ℝ)
    Tendsto (fun z ↦ z * L z) (𝓝[≠] (0 : ℂ)) (𝓝 (-((d : ℂ) * canonicalResidueOne F))) ∧
      Tendsto (fun z ↦ (z - 1) * L z) (𝓝[≠] (1 : ℂ)) (𝓝 (canonicalResidueOne F)) := by
  subst ω₀
  obtain ⟨L₀, hm₀, he₀, h₀, h₁⟩ := exists_globalCompletedHecke_trivial_exact_residues
    F S₀ hs₀ hu₀ η ν μ hν
  have hg (p : ℂ) := globalCompletedHeckeContinuation_unique_germ F 1 S₀ hs₀ hu₀
    hm₀ hm he₀ he p
  exact ⟨h₀.congr' (EventuallyEq.mul (.refl _ _) (hg 0)),
    h₁.congr' (EventuallyEq.mul (.refl _ _) (hg 1))⟩

set_option maxHeartbeats 800000 in
include μ hν in
/-- Corrected Proposition 3.2.1.3 for every unitary idele-class character.
The two residues use the normalization of the displayed Euler product. -/
theorem manuscriptHecke_regularities (t : ℝ) (ht : HasHeckeHeight F χ t) :
    ∃ (T : Finset (Place F)) (ht' : Surjective (sIdeleClassInclusion F T))
      (hu' : globalNormOneCharacter F (heckeNormOneRestriction F χ⁻¹) ∈
        (sUnramified F T : Set (QuasiCharacter (IdeleClass F))))
      (L L' ε : ℂ → ℂ),
      let ω := heckeNormOneRestriction F χ
      let b := iHeight t
      let d : ℝ := Real.sqrt ((differentIdeal ℤ (𝓞 F)).absNorm : ℝ)
      MeromorphicOn L univ ∧ MeromorphicOn L' univ ∧
      EqOn L (manuscriptCompletedHeckeEuler F χ S hs hu t) {z | 1 < z.re} ∧
      EqOn L' (manuscriptCompletedHeckeEuler F χ⁻¹ T ht' hu' (-t)) {z | 1 < z.re} ∧
      (ω ≠ 1 → AnalyticOnNhd ℂ L univ) ∧
      (ω = 1 → meromorphicOrderAt L b = (-1 : ℤ) ∧
        meromorphicOrderAt L (1 + b) = (-1 : ℤ) ∧
        (∀ z, z ≠ b → z ≠ 1 + b → AnalyticAt ℂ L z) ∧
        Tendsto (fun z ↦ (z - b) * L z) (𝓝[≠] b)
          (𝓝 (-((d : ℂ) * manuscriptResidueOne F))) ∧
        Tendsto (fun z ↦ (z - (1 + b)) * L z) (𝓝[≠] (1 + b))
          (𝓝 (manuscriptResidueOne F))) ∧
      (AnalyticOnNhd ℂ ε univ ∧ (∀ z, ε z ≠ 0) ∧
        ∀ c, (fun z ↦ L' (1 - z)) =ᶠ[𝓝[≠] c] L * ε) ∧
      ∀ z, 1 ≤ z.re → (ω ≠ 1 ∨ z ≠ 1 + b) → L z ≠ 0 := by
  let ω := heckeNormOneRestriction F χ
  let b := iHeight t
  obtain ⟨A, hm, he, hAn, hP⟩ :=
    exists_globalCompletedHecke_analytic_or_simple_poles F ω S hs hu η ν μ hν
  obtain ⟨T, hT, hωT, A₀, B, e, hm₀, hBm, he₀, hB, hEa, hEn, hR⟩ :=
    exists_globalCompletedHecke_functionalEquation F ω S hs hu η ν μ hν
  let hu' : globalNormOneCharacter F (heckeNormOneRestriction F χ⁻¹) ∈
      (sUnramified F T : Set (QuasiCharacter (IdeleClass F))) := by
    rw [heckeNormOneRestriction_inv]
    exact hωT
  have hB' : EqOn B (globalCompletedHeckeEuler F (heckeNormOneRestriction F χ⁻¹)
      T hT hu') {z | 1 < z.re} := by
    have hEq (ω' : PontryaginDual (K F)) (hw : ω' = ω⁻¹)
        (hU : globalNormOneCharacter F ω' ∈ (sUnramified F T : Set (QuasiCharacter (IdeleClass F)))) :
        EqOn B (globalCompletedHeckeEuler F ω' T hT hU) {z | 1 < z.re} := by
      subst ω'
      exact hB
    exact hEq _ (heckeNormOneRestriction_inv F χ) hu'
  let Q := shifted F t A
  let R := shifted F (-t) B
  let ε (z : ℂ) := e (z - b)
  have hq : EqOn Q (manuscriptCompletedHeckeEuler F χ S hs hu t) {z | 1 < z.re} := by
    intro z hz
    change complexGammaScale F * A (z - b) = _
    rw [manuscriptCompletedHeckeEuler_shift F χ S hs hu t ht,
      he (show 1 < (z - b).re by rwa [shifted_re])]
  have hr : EqOn R (manuscriptCompletedHeckeEuler F χ⁻¹ T hT hu' (-t)) {z | 1 < z.re} := by
    intro z hz
    change complexGammaScale F * B (z - iHeight (-t)) = _
    rw [manuscriptCompletedHeckeEuler_shift F χ⁻¹ T hT hu' (-t) (HasHeckeHeight.inv F ht),
      hB' (show 1 < (z - iHeight (-t)).re by rwa [shifted_re])]
  refine ⟨T, hT, hu', Q, R, ε, shifted_meromorphic F t hm, shifted_meromorphic F (-t) hBm,
    hq, hr, fun hω z _ ↦ shifted_analytic F t (hAn hω _ (mem_univ _)), ?_, ?_, ?_⟩
  · intro hω
    obtain ⟨h₀, h₁⟩ := canonical_trivial_residues_of_continuation
      F η ν μ hν ω hω S hs hu hm he
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [shifted_order F t hm, sub_self, (hP hω).1]
    · rw [shifted_order F t hm, add_sub_cancel_right, (hP hω).2.1]
    · intro z hz₀ hz₁
      exact shifted_analytic F t ((hP hω).2.2 _
        (fun e₀ ↦ hz₀ (by simpa using sub_eq_iff_eq_add.mp e₀))
        (fun e₁ ↦ hz₁ (sub_eq_iff_eq_add.mp e₁)))
    · have ht₀ := shifted_residue F t (p := 0) (by simpa only [sub_zero] using h₀)
      have hscale (d : ℂ) : complexGammaScale F * (-(d * canonicalResidueOne F)) =
          -(d * manuscriptResidueOne F) := by rw [← scale_residue_one]; ring
      simpa only [zero_add, hscale] using ht₀
    · simpa only [scale_residue_one] using shifted_residue F t (p := 1) h₁
  · refine ⟨fun z _ ↦ (hEa _ (mem_univ _)).comp
      (f := fun w : ℂ ↦ w - b) (analyticAt_id.sub analyticAt_const),
      fun z ↦ hEn (z - b), fun c ↦ ?_⟩
    have hp := tendsto_sub_punctured b (c - b)
    rw [sub_add_cancel] at hp
    have hg := globalCompletedHeckeContinuation_unique_germ F ω S hs hu hm₀ hm he₀ he (c - b)
    filter_upwards [hp.eventually (hR (c - b)), hp.eventually hg] with z h₁ h₂
    change complexGammaScale F * B ((1 - z) - iHeight (-t)) =
      (complexGammaScale F * A (z - b)) * e (z - b)
    have harg : (1 - z) - iHeight (-t) = 1 - (z - b) := by
      simp only [b, iHeight, Complex.ofReal_neg]
      ring
    change B (1 - (z - b)) = A₀ (z - b) * e (z - b) at h₁
    change A₀ (z - b) = A (z - b) at h₂
    rw [harg, h₁, h₂, mul_assoc]
  · intro z hz hreg
    have hA : AnalyticAt ℂ A (z - b) := by
      by_cases hω : ω = 1
      · apply (hP hω).2.2
        · intro hzero
          have heq : z = b := by simpa using sub_eq_iff_eq_add.mp hzero
          have hre := congrArg Complex.re heq
          simp [b, Complex.mul_re] at hre
          linarith
        · exact fun h₁ ↦ (hreg.resolve_left (not_not.mpr hω)) (sub_eq_iff_eq_add.mp h₁)
      · exact hAn hω _ (mem_univ _)
    exact mul_ne_zero (complexGammaScale_ne_zero F)
      (globalCompletedHecke_ne_zero_of_one_le_re F η ν μ hν ω S hs hu hm he
        (by rwa [shifted_re]) hA)

end

end Masullo
