import HeckeConductorReflection

open Complex Filter Function Ideal IsDedekindDomain MeasureTheory Metric NumberField Set Topology
open scoped Classical ComplexConjugate NumberField

namespace Masullo

noncomputable section

private theorem completedReflection_norm_midpoint {L L' : ℂ → ℂ} {A : ℂ} {k : ℝ}
    (hL : AnalyticOnNhd ℂ L ({0, 1} : Set ℂ)ᶜ)
    (hL' : AnalyticOnNhd ℂ L' ({0, 1} : Set ℂ)ᶜ)
    (hNZ : L 2 ≠ 0)
    (hConj : ∀ z : ℂ, 1 < z.re → L' (conj z) = conj (L z))
    (hRef : ∀ c : ℂ, (fun z ↦ L' (1 - z)) =ᶠ[𝓝[≠] c]
      fun z ↦ L z * (A * Complex.exp ((k : ℂ) * (z - 1 / 2)))) :
    ‖A‖ = 1 := by
  let U : Set ℂ := ({0, 1} : Set ℂ)ᶜ
  have hU : IsOpen U := (Set.finite_singleton (1 : ℂ)).insert 0 |>.isClosed.isOpen_compl
  have hPre : IsPreconnected U :=
    ((Set.finite_singleton (1 : ℂ)).insert 0).countable.isConnected_compl_of_one_lt_rank
      (by simp) |>.isPreconnected
  have h2 : (2 : ℂ) ∈ U := by norm_num [U]
  have hhalf : (1 / 2 : ℂ) ∈ U := by
    change (1 / 2 : ℂ) ∉ ({0, 1} : Set ℂ)
    norm_num
  have hG : AnalyticOnNhd ℂ (fun z ↦ conj (L' (conj z))) U := by
    apply DifferentiableOn.analyticOnNhd _ hU
    intro z hz
    apply DifferentiableAt.differentiableWithinAt
    apply differentiableAt_conj_conj_iff.mpr
    apply (hL' _ ?_).differentiableAt
    change conj z ∉ ({0, 1} : Set ℂ)
    change z ∉ ({0, 1} : Set ℂ) at hz
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, map_eq_zero_iff _ (starRingEnd ℂ).injective,
      map_eq_one_iff _ (starRingEnd ℂ).injective] using hz
  have hEq : EqOn (fun z ↦ conj (L' (conj z))) L U :=
    hG.eqOn_of_preconnected_of_eventuallyEq hL hPre h2
      (eventuallyEq_of_mem ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds
        (by norm_num : (1 : ℝ) < (2 : ℂ).re)) fun z hz ↦ by rw [hConj z hz]; simp)
  have hNear : ∀ᶠ z in 𝓝[≠] (1 / 2 : ℂ), L z ≠ 0 := by
    obtain h | h := (hL _ hhalf).eventually_eq_zero_or_eventually_ne_zero
    · exact False.elim (hNZ (hL.eqOn_zero_of_preconnected_of_eventuallyEq_zero hPre hhalf h h2))
    · exact h
  obtain ⟨V, hV, hVne⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hNear
  obtain ⟨r, hr, hb⟩ := Metric.mem_nhds_iff.mp hV
  let z : ℂ := ⟨1 / 2, r / 2⟩
  have hz : z ∈ U := by
    change z ∉ ({0, 1} : Set ℂ)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    constructor <;> intro e <;> have h := congrArg Complex.re e <;> norm_num [z] at h
  have hzConj : 1 - z = conj z := by
    apply Complex.ext <;> norm_num [z, Complex.sub_re, Complex.sub_im]
  have hzne : z ≠ (1 / 2 : ℂ) := by
    intro e
    have he := congrArg Complex.im e
    norm_num [z] at he
    linarith
  have hdist : z ∈ ball (1 / 2 : ℂ) r := by
    rw [mem_ball, dist_eq_norm]
    have he : z - (1 / 2 : ℂ) = (r / 2 : ℝ) * Complex.I := by
      apply Complex.ext <;> norm_num [z, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
        Complex.div_ofNat_re, Complex.div_ofNat_im]
    rw [he, norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs,
      abs_of_pos (half_pos hr)]
    linarith
  have hLz : L z ≠ 0 := hVne ⟨hb hdist, hzne⟩
  have hL'z : conj z ∈ U := hzConj ▸ (show 1 - z ∈ U from by
    change 1 - z ∉ ({0, 1} : Set ℂ)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    constructor <;> intro e <;> have h := congrArg Complex.re e <;>
      norm_num [z, Complex.sub_re] at h)
  have hl : ContinuousAt (fun w ↦ L' (1 - w)) z :=
    (hL' _ (hzConj.symm ▸ hL'z)).continuousAt.comp
      (continuous_const.sub continuous_id).continuousAt
  have hr' : ContinuousAt (fun w ↦ L w * (A * Complex.exp ((k : ℂ) * (w - 1 / 2)))) z :=
    (hL _ hz).continuousAt.mul (by fun_prop)
  have hEqz := ((hl.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE hr').mp (hRef z)).eq_of_nhds
  rw [hzConj] at hEqz
  have hstar : L' (conj z) = conj (L z) := by
    simpa using congrArg (starRingEnd ℂ) (hEq hz)
  rw [hstar] at hEqz
  have hn := congrArg norm hEqz
  have hexp : (((k : ℂ) * (z - 1 / 2))).re = 0 := by
    simp [z, Complex.mul_re, Complex.sub_re]
  simp only [Complex.norm_conj, norm_mul, norm_exp, hexp, Real.exp_zero, mul_one] at hn
  exact (mul_left_cancel₀ (norm_ne_zero_iff.mpr hLz) (by simpa using hn.symm :
    ‖L z‖ * ‖A‖ = ‖L z‖ * 1))

private theorem rootNumber_reflect_punctured (c : ℂ) :
    Tendsto (fun z : ℂ ↦ 1 - z) (𝓝[≠] c) (𝓝[≠] (1 - c)) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · exact ((continuous_const.sub continuous_id).continuousAt (x := c)).tendsto.mono_left
      nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with z hz
    change 1 - z ≠ 1 - c
    intro h
    exact hz (sub_right_injective h)

variable (F : Type*) [Field F] [NumberField F]
private abbrev RootNormOne := normOneIdeleClass F
private abbrev RootPlace := HeightOneSpectrum (𝓞 F)

local instance rootNumberNormOneMeasurable : MeasurableSpace (RootNormOne F) := borel _
local instance rootNumberNormOneBorel : BorelSpace (RootNormOne F) := ⟨rfl⟩
local instance rootNumberIdeleMeasurable : MeasurableSpace (Idele F) := borel _
local instance rootNumberIdeleBorel : BorelSpace (Idele F) := ⟨rfl⟩
local instance (v : RootPlace F) : MeasurableSpace (v.adicCompletion F) := borel _
local instance (v : RootPlace F) : BorelSpace (v.adicCompletion F) := ⟨rfl⟩

variable (ν : Measure (RootNormOne F)) [ν.IsHaarMeasure]
variable (η : Measure (Idele F)) [η.IsHaarMeasure]
variable [∀ v : RootPlace F, MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : RootPlace F, BorelSpace (v.adicCompletion F)ˣ]
  (μ : ∀ v : RootPlace F, Measure (v.adicCompletion F)ˣ)
  [∀ v : RootPlace F, (μ v).IsHaarMeasure] [∀ v : RootPlace F, SigmaFinite (μ v)]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]
variable (hν : IsWeilQuotientMeasure (principalIdeles F) η Measure.count (globalClassMeasure F ν))

set_option maxHeartbeats 800000 in
include μ hν in
/-- The conductor reflection for the actual completed Hecke continuations
has a factor of modulus one on the critical line. -/
theorem exists_globalCompletedHecke_unit_conductorReflection
    (ω : PontryaginDual (RootNormOne F)) (S : Finset (RootPlace F))
    (hs : Surjective (sIdeleClassInclusion F S))
    (hu : globalNormOneCharacter F ω ∈ (sUnramified F S : Set (QuasiCharacter (IdeleClass F))))
    (hu' : globalNormOneCharacter F ω⁻¹ ∈ (sUnramified F S : Set (QuasiCharacter (IdeleClass F))))
    (hD : ∀ v : RootPlace F, v.asIdeal ∣ differentIdeal ℤ (𝓞 F) → v ∈ S) :
    ∃ (L L' : ℂ → ℂ) (A : ℂ),
      MeromorphicOn L univ ∧ MeromorphicOn L' univ ∧
      AnalyticOnNhd ℂ L ({0, 1} : Set ℂ)ᶜ ∧ AnalyticOnNhd ℂ L' ({0, 1} : Set ℂ)ᶜ ∧
      EqOn L (globalCompletedHeckeEuler F ω S hs hu) {z | 1 < z.re} ∧
      EqOn L' (globalCompletedHeckeEuler F ω⁻¹ S hs hu') {z | 1 < z.re} ∧ ‖A‖ = 1 ∧
      let k := (Real.log (heckeDiscriminantConductor F (normOneEulerCharacter F ω)) : ℂ)
      ∀ c, (fun z ↦ L' (1 - z)) =ᶠ[𝓝[≠] c] fun z ↦ L z * (A * exp (k * (z - 1 / 2))) := by
  obtain ⟨P, P', A, hPm, hPm', hPe, hPe', _, href⟩ :=
    exists_globalCompletedHecke_conductorReflection F η ν μ hν ω S hs hu hu' hD
  obtain ⟨L, hLm, hLe, hLa, hLp⟩ :=
    exists_globalCompletedHecke_analytic_or_simple_poles F ω S hs hu η ν μ hν
  obtain ⟨L', hLm', hLe', hLa', hLp'⟩ :=
    exists_globalCompletedHecke_analytic_or_simple_poles F ω⁻¹ S hs hu' η ν μ hν
  have han {ψ : PontryaginDual (RootNormOne F)} {Q : ℂ → ℂ}
      (h : ψ ≠ 1 → AnalyticOnNhd ℂ Q univ)
      (h' : ψ = 1 → meromorphicOrderAt Q 0 = (-1 : ℤ) ∧ meromorphicOrderAt Q 1 = (-1 : ℤ) ∧
        ∀ z, z ≠ 0 → z ≠ 1 → AnalyticAt ℂ Q z) :
      AnalyticOnNhd ℂ Q ({0, 1} : Set ℂ)ᶜ := by
    by_cases hψ : ψ = 1
    · intro z hz
      have hz' : ¬ (z = 0 ∨ z = 1) := by simpa using hz
      exact (h' hψ).2.2 z (fun he ↦ hz' (Or.inl he)) (fun he ↦ hz' (Or.inr he))
    · exact (h hψ).mono (subset_univ _)
  have hA := han hLa hLp
  have hA' := han hLa' hLp'
  have hConj (z : ℂ) (hz : 1 < z.re) : L' (conj z) = conj (L z) := by
    rw [hLe hz, hLe' (show 1 < (conj z).re from hz)]
    exact globalCompletedHeckeEuler_inv_conj F S hs ω hu hu' z
  have hNZ : L 2 ≠ 0 := by
    have htwo : (1 : ℝ) < (2 : ℂ).re := by norm_num
    rw [hLe htwo]
    exact globalCompletedHeckeEuler_ne_zero F ω S hs hu htwo
  have hRefL (c : ℂ) : (fun z ↦ L' (1 - z)) =ᶠ[𝓝[≠] c] fun z ↦ L z *
      (A * exp ((Real.log (heckeDiscriminantConductor F (normOneEulerCharacter F ω)) : ℂ) *
        (z - 1 / 2))) := by
    have hleft := globalHeckeContinuation_unique_germ hLm' hPm' hLe' hPe' (1 - c)
    have hright := globalHeckeContinuation_unique_germ hLm hPm hLe hPe c
    filter_upwards [(rootNumber_reflect_punctured c).eventually hleft, hright, href c] with z h₁ h₂ h₃
    exact h₁.trans (h₃.trans (congrArg (· * _) h₂.symm))
  exact ⟨L, L', A, hLm, hLm', hA, hA', hLe, hLe',
    completedReflection_norm_midpoint hA hA' hNZ hConj hRefL, hRefL⟩

end

end Masullo
