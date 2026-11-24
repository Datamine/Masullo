import HeckeIdealDirichletSeries
import GlobalHeckeResidues

open Filter Function Ideal IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped NumberField

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

private abbrev K := normOneIdeleClass F
private abbrev Place := HeightOneSpectrum (𝓞 F)

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
private theorem exists_finiteEuler_continuations (ω : PontryaginDual (K F)) :
    ∃ L : ℂ → ℂ,
      MeromorphicOn L univ ∧ EqOn L (globalFiniteHeckeEuler F ω) {z | 1 < z.re} ∧
      (ω ≠ 1 → AnalyticOnNhd ℂ L univ) ∧
      (ω = 1 → meromorphicOrderAt L 1 = (-1 : ℤ) ∧
        ∀ z, 0 < z.re → z ≠ 1 → AnalyticAt ℂ L z) := by
  obtain ⟨S, hS⟩ := exists_homogeneousThetaPlaceBase F ω
  obtain ⟨hs, hu⟩ := hS S Subset.rfl
  obtain ⟨A, hm, he, hAn, hPole⟩ :=
    exists_globalCompletedHecke_analytic_or_simple_poles F ω S hs hu η ν μ hν
  let a := sLocalNormOneCharacterOfGlobal F ω S hs hu
  let D := archimedeanNumberFieldZetaDenominator F
    (sLocalRealArchParameters F S a) (sLocalComplexArchParameters F S a)
  have hD (z : ℂ) : AnalyticAt ℂ D z :=
    archimedeanNumberFieldZetaDenominator_analytic _ _ _ z
  have hne {z : ℂ} (hz : 0 < z.re) : D z ≠ 0 := by
    apply archimedeanNumberFieldZetaDenominator_ne_zero_of_pos
    · intro v
      simpa only [Complex.add_re, sLocalRealArchParameters_re, add_zero] using hz
    · intro v
      simpa only [Complex.add_re, sLocalComplexArchParameters_re, add_zero] using hz
  refine ⟨D * A, fun z hz ↦ (hD z).meromorphicAt.mul (hm z hz), ?_, ?_, ?_⟩
  · intro z hz
    change D z * A z = _
    rw [he hz]
    change D z * ((D z)⁻¹ * globalFiniteHeckeEuler F ω z) = _
    rw [← mul_assoc, mul_inv_cancel₀ (hne (zero_lt_one.trans hz)), one_mul]
  · exact fun hω z hz ↦ (hD z).mul (hAn hω z hz)
  · intro hω
    obtain ⟨_, ho, hreg⟩ := hPole hω
    refine ⟨?_, fun z hz h₁ ↦ (hD z).mul (hreg z (by aesop) h₁)⟩
    rw [meromorphicOrderAt_mul_of_ne_zero (hD 1) (hne (by simp)), ho]

include μ hν in
/-- The actual ideal coefficients of any nontrivial norm-one component have an
entire Dirichlet continuation, in the original spectral parameter. -/
theorem exists_finiteHeckeNormCoefficient_entire (χ : PontryaginDual (IdeleClass F))
    (hχ : heckeNormOneRestriction F χ ≠ 1) :
    ∃ L : ℂ → ℂ, Differentiable ℂ L ∧
      ∀ s, 1 < s.re → LSeriesHasSum (finiteHeckeNormCoefficient F χ) s (L s) := by
  obtain ⟨t, ht, _⟩ := existsUnique_heckeHeight F χ
  obtain ⟨A, _, he, hAn, _⟩ :=
    exists_finiteEuler_continuations F η ν μ hν (heckeNormOneRestriction F χ)
  let L (z : ℂ) := A (z - (t : ℂ) * Complex.I)
  have hA : Differentiable ℂ A := fun z ↦ (hAn hχ z (mem_univ _)).differentiableAt
  refine ⟨L, hA.comp (differentiable_id.sub (differentiable_const _)), fun z hz ↦ ?_⟩
  have hs : z - (t : ℂ) * Complex.I ∈ {z : ℂ | 1 < z.re} := by
    simpa [Complex.sub_re, Complex.mul_re] using hz
  have hEq : L z = manuscriptFiniteHeckeEuler F χ z :=
    (he hs).trans (manuscriptFiniteHeckeEuler_shift F χ ht z).symm
  rw [hEq]
  exact manuscriptFiniteHeckeEuler_hasSum_normCoefficients F χ hz

private theorem tendsto_real_punctured_one :
    Tendsto (fun r : ℝ ↦ (r : ℂ)) (𝓝[>] (1 : ℝ)) (𝓝[≠] (1 : ℂ)) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within (fun r : ℝ ↦ (r : ℂ))
    ((Complex.continuous_ofReal.tendsto' 1 1 (by simp)).mono_left nhdsWithin_le_nhds) ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact fun h ↦ (ne_of_gt (Set.mem_Ioi.mp hr))
    (by exact_mod_cast (Set.mem_singleton_iff.mp h))

include μ hν in
/-- Subtracting the class-number residue from the actual ideal-count
Dirichlet series gives a continuous function on the closed right half-plane. -/
theorem exists_idealNormMultiplicity_pole_subtraction :
    ∃ G : ℂ → ℂ, ContinuousOn G {z | 1 ≤ z.re} ∧ EqOn G
      (fun z ↦ LSeries (fun n ↦ (finiteHeckeNormMultiplicity F n : ℂ)) z -
        (dedekindZeta_residue F : ℂ) / (z - 1)) {z | 1 < z.re} := by
  obtain ⟨L, hm, he, _, hPole⟩ := exists_finiteEuler_continuations F η ν μ hν 1
  obtain ⟨ho, hreg⟩ := hPole rfl
  obtain ⟨g, hg, _, heq⟩ :=
    (meromorphicOrderAt_eq_int_iff (hm 1 (mem_univ _))).mp ho
  let c : ℂ := dedekindZeta_residue F
  have hnear : ∀ᶠ z in 𝓝[≠] (1 : ℂ), (z - 1) * L z = g z := by
    filter_upwards [heq, self_mem_nhdsWithin] with z hz hne
    rw [hz]
    simp only [smul_eq_mul, zpow_neg, zpow_one, ← mul_assoc]
    rw [mul_inv_cancel₀ (sub_ne_zero.mpr hne), one_mul]
  have hgc : g 1 = c := by
    apply tendsto_nhds_unique
      ((hg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).comp tendsto_real_punctured_one)
    apply (tendsto_sub_one_mul_dedekindZeta_nhdsGT F).congr'
    filter_upwards [tendsto_real_punctured_one.eventually hnear, self_mem_nhdsWithin] with r hr hr'
    have hrr : (r : ℂ) ∈ {z : ℂ | 1 < z.re} := by simpa using hr'
    dsimp only [Function.comp_apply] at hr ⊢
    rw [← hr, he hrr, globalFiniteHeckeEuler_trivial_eq_dedekindZeta F hrr]
  let A (z : ℂ) := L z - c / (z - 1)
  let G := Function.update A 1 (deriv g 1)
  refine ⟨G, fun z hz ↦ ?_, fun z hz ↦ ?_⟩
  · apply ContinuousAt.continuousWithinAt
    by_cases h₁ : z = 1
    · subst z
      have hevent : G =ᶠ[𝓝 1] dslope g 1 := by
        filter_upwards [eventually_nhdsWithin_iff.mp hnear] with z hz
        by_cases h : z = 1
        · subst z
          simp [G, dslope_same]
        · have hne : z - 1 ≠ 0 := sub_ne_zero.mpr h
          simp only [G, Function.update_of_ne h, dslope_of_ne _ h, slope_def_field, A, hgc]
          have hl : L z = g z / (z - 1) := (eq_div_iff hne).mpr (by simpa [mul_comm] using hz h)
          rw [hl, sub_div]
      exact (continuousAt_dslope_same.mpr hg.differentiableAt).congr hevent.symm
    · have hA : ContinuousAt A z :=
        (hreg z (zero_lt_one.trans_le hz) h₁).continuousAt.sub
          (continuousAt_const.div (continuousAt_id.sub continuousAt_const) (sub_ne_zero.mpr h₁))
      exact hA.congr ((eventually_ne_nhds h₁).mono fun w hw ↦ (Function.update_of_ne hw _ _).symm)
  · have h₁ : z ≠ 1 := by rintro rfl; simpa using hz
    have hzeta : LSeries (fun n ↦ (finiteHeckeNormMultiplicity F n : ℂ)) z = dedekindZeta F z := by
      have h := manuscriptFiniteHeckeEuler_hasSum_normCoefficients F 1 hz
      rw [show finiteHeckeNormCoefficient F 1 = (fun n ↦ (finiteHeckeNormMultiplicity F n : ℂ))
        from funext (finiteHeckeNormCoefficient_one F)] at h
      rw [h.LSeries_eq]
      have hw : normOneEulerCharacter F 1 = 1 := DFunLike.ext _ _ fun _ ↦ rfl
      have heuler : manuscriptFiniteHeckeEuler F 1 z = globalFiniteHeckeEuler F 1 z := by
        change (∏' v : Place F, heckeEulerFactor F
          (heckeEulerCoefficient F 1 (chosenFiniteUniformizer F)) v z) =
          ∏' v : Place F, heckeEulerFactor F
            (heckeEulerCoefficient F (normOneEulerCharacter F 1) (chosenFiniteUniformizer F)) v z
        rw [hw]
      exact heuler.trans (globalFiniteHeckeEuler_trivial_eq_dedekindZeta F hz)
    change G z = LSeries (fun n ↦ (finiteHeckeNormMultiplicity F n : ℂ)) z -
      (dedekindZeta_residue F : ℂ) / (z - 1)
    rw [hzeta]
    simp only [G, Function.update_of_ne h₁, A, c]
    rw [he hz, globalFiniteHeckeEuler_trivial_eq_dedekindZeta F hz]

end
end Masullo
