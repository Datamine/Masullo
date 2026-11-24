import HeckeRootNumber
import IdelicHeckeFrequencyBoxes

open Filter Function Ideal IsDedekindDomain MeasureTheory NumberField Set
open scoped NumberField Topology

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]
variable (χ : PontryaginDual (IdeleClass F))
variable (S : Finset (HeightOneSpectrum (𝓞 F)))
variable (hs : Surjective (sIdeleClassInclusion F S))
variable (hu : globalNormOneCharacter F (heckeNormOneRestriction F χ) ∈
  (sUnramified F S : Set (QuasiCharacter (IdeleClass F))))
variable (hu' : globalNormOneCharacter F (heckeNormOneRestriction F χ)⁻¹ ∈
  (sUnramified F S : Set (QuasiCharacter (IdeleClass F))))

private abbrev uniformGrowthPhase :=
  sLocalNormOneCharacterOfGlobal F (heckeNormOneRestriction F χ) S hs hu

private theorem norm_shift_le_of_height_box {t T : ℝ} {x : ℂ}
    (ht : |t| ≤ T) (hx : ‖-(t : ℂ) * Complex.I + x‖ ≤ T) :
    ‖x‖ ≤ 2 * T := by
  have h := norm_add_le (-(t : ℂ) * Complex.I + x) ((t : ℂ) * Complex.I)
  have hsum : -(t : ℂ) * Complex.I + x + (t : ℂ) * Complex.I = x := by ring
  rw [hsum, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs] at h
  linarith

/-- The Hecke parameter box bounds the complete reflected archimedean
quotient by a fixed-degree polynomial on a left boundary line. -/
theorem completedTateArchRatio_of_Hecke_box (n : ℕ) {t T : ℝ} (ht : |t| ≤ T)
    (hb : manuscriptHeckeArchParametersInBox F χ S hs hu t T)
    (z : ℂ) (hz : z.re = 1 / 2 - (n : ℝ)) :
    ‖completedTateReciprocalArch F S hs (heckeNormOneRestriction F χ) hu z *
      (completedTateReciprocalArch F S hs (heckeNormOneRestriction F χ)⁻¹ hu' (1 - z))⁻¹‖ ≤
        ((‖z‖ + (1 + 5 / 2 * T) + (2 * n : ℝ)) / (2 * Real.pi)) ^
          (Module.finrank ℚ F * n) := by
  obtain ⟨hr, hc, ha⟩ := hb
  have hT : 0 ≤ T := (abs_nonneg t).trans ht
  refine completedTateArchRatio_half_integer_uniform F S hs (heckeNormOneRestriction F χ)
    hu hu' n (1 + 5 / 2 * T) (by positivity) ?_ ?_ z hz
  · intro v
    let a := sLocalRealArchParameters F S (uniformGrowthPhase F χ S hs hu) v
    have hparity : ((a.2 % 2 : ℕ) : ℝ) ≤ 1 := by
      exact_mod_cast (show a.2 % 2 ≤ 1 from by omega)
    refine (norm_add_le a.1 (((a.2 % 2 : ℕ) : ℂ))).trans ?_
    rw [Complex.norm_natCast]
    have hradial : ‖a.1‖ ≤ 2 * T := norm_shift_le_of_height_box ht (hr v)
    linarith
  · intro v
    let j := sLocalComplexArchParameters F S (uniformGrowthPhase F χ S hs hu) v
    have hj : (j.2.natAbs : ℝ) ≤ T := by
      rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
      exact ha v
    refine (norm_add_le j.1 ((j.2.natAbs : ℂ) / 2)).trans ?_
    rw [norm_div, Complex.norm_natCast, Complex.norm_ofNat]
    have hradial : ‖j.1‖ ≤ 2 * T := norm_shift_le_of_height_box ht (hc v)
    linarith

private abbrev GrowthNormOne := normOneIdeleClass F
private abbrev GrowthPlace := HeightOneSpectrum (𝓞 F)

local instance : MeasurableSpace (GrowthNormOne F) := borel _
local instance : BorelSpace (GrowthNormOne F) := ⟨rfl⟩
local instance : MeasurableSpace (Idele F) := borel _
local instance : BorelSpace (Idele F) := ⟨rfl⟩
local instance (v : GrowthPlace F) : MeasurableSpace (v.adicCompletion F) := borel _
local instance (v : GrowthPlace F) : BorelSpace (v.adicCompletion F) := ⟨rfl⟩

variable (ν : Measure (GrowthNormOne F)) [ν.IsHaarMeasure]
variable (η : Measure (Idele F)) [η.IsHaarMeasure]
variable [∀ v : GrowthPlace F, MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : GrowthPlace F, BorelSpace (v.adicCompletion F)ˣ]
  (μ : ∀ v : GrowthPlace F, Measure (v.adicCompletion F)ˣ)
  [∀ v : GrowthPlace F, (μ v).IsHaarMeasure] [∀ v : GrowthPlace F, SigmaFinite (μ v)]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]
variable (hν : IsWeilQuotientMeasure (principalIdeles F) η Measure.count (globalClassMeasure F ν))

set_option maxHeartbeats 900000 in
include hu' μ hν in
/-- The finite Hecke continuation has a left boundary bound controlled by
the number field, the joint parameter box, and an upper bound for the
discriminant–conductor product. It holds at every ordinate. -/
theorem exists_globalFiniteHecke_left_bound_of_box_analytic
    (hD : ∀ v : GrowthPlace F, v.asIdeal ∣ differentIdeal ℤ (𝓞 F) → v ∈ S)
    (n : ℕ) (hn : 1 ≤ n) {t T Q : ℝ} (ht : |t| ≤ T)
    (hb : manuscriptHeckeArchParametersInBox F χ S hs hu t T)
    (hQ : 1 ≤ Q)
    (hCond : (heckeDiscriminantConductor F
      (normOneEulerCharacter F (heckeNormOneRestriction F χ)) : ℝ) ≤ Q) :
    ∃ f : ℂ → ℂ, MeromorphicOn f univ ∧ AnalyticOnNhd ℂ f ({0, 1} : Set ℂ)ᶜ ∧
      EqOn f (globalFiniteHeckeEuler F (heckeNormOneRestriction F χ)) {z | 1 < z.re} ∧
      ∀ z : ℂ, z.re = 1 / 2 - (n : ℝ) →
        ‖f z‖ ≤ Q ^ n * ‖globalFiniteHeckeEuler F 1 ((1 / 2 + (n : ℝ) : ℝ) : ℂ)‖ *
          ((‖z‖ + (1 + 5 / 2 * T) + (2 * n : ℝ)) / (2 * Real.pi)) ^
            (Module.finrank ℚ F * n) := by
  let ω := heckeNormOneRestriction F χ
  obtain ⟨L, L', A, hL, _, ha, ha', he, he', hA, hReflect⟩ :=
    exists_globalCompletedHecke_unit_conductorReflection F ν η μ hν ω S hs hu hu' hD
  let D := completedTateReciprocalArch F S hs ω hu
  let D' := completedTateReciprocalArch F S hs ω⁻¹ hu'
  let d : ℝ := heckeDiscriminantConductor F (normOneEulerCharacter F ω)
  let f := D * L
  have hDan (z : ℂ) : AnalyticAt ℂ D z :=
    archimedeanNumberFieldZetaDenominator_analytic _ _ _ _
  have hDne (z : ℂ) (hz : 0 < z.re) : D z ≠ 0 := by
    apply archimedeanNumberFieldZetaDenominator_ne_zero_of_pos
    · intro v
      simpa only [Complex.add_re, sLocalRealArchParameters_re, add_zero] using hz
    · intro v
      simpa only [Complex.add_re, sLocalComplexArchParameters_re, add_zero] using hz
  refine ⟨f, fun z hz ↦ (hDan z).meromorphicAt.mul (hL z hz),
    fun z hz ↦ (hDan z).mul (ha z hz), ?_, ?_⟩
  · intro z hz
    change D z * L z = _
    rw [he hz]
    change D z * ((D z)⁻¹ * _) = _
    rw [← mul_assoc, mul_inv_cancel₀ (hDne z (zero_lt_one.trans hz)), one_mul]
    rfl
  intro z hz
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hzNeg : z.re < 0 := by linarith
  have hr : (1 - z).re = 1 / 2 + (n : ℝ) := by
    rw [Complex.sub_re, Complex.one_re, hz]
    ring
  have hr' : 1 < (1 - z).re := by rw [hr]; linarith
  have hzU : z ∈ ({0, 1} : Set ℂ)ᶜ := by
    simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
    constructor <;> (intro e; rw [e] at hzNeg; norm_num at hzNeg)
  have hzU' : 1 - z ∈ ({0, 1} : Set ℂ)ᶜ := by
    simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
    constructor <;> (intro e; rw [e] at hr'; norm_num at hr')
  have hCL : ContinuousAt (fun w : ℂ ↦ L' (1 - w)) z :=
    (ha' _ hzU').continuousAt.comp (continuous_const.sub continuous_id).continuousAt
  have hCR : ContinuousAt (fun w : ℂ ↦ L w *
      (A * Complex.exp ((Real.log d : ℂ) * (w - 1 / 2)))) z :=
    (ha _ hzU).continuousAt.mul (by fun_prop)
  have hEq := ((hCL.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE hCR).mp (hReflect z)).eq_of_nhds
  have hExp : (((Real.log d : ℂ) * (z - 1 / 2))).re = -((n : ℝ) * Real.log d) := by
    simp [Complex.mul_re, Complex.sub_re, hz]
    ring
  have hNorm : ‖L z‖ = ‖L' (1 - z)‖ * Real.exp ((n : ℝ) * Real.log d) := by
    have hnorm := congrArg norm hEq
    change ‖L' (1 - z)‖ = ‖L z * (A * Complex.exp ((Real.log d : ℂ) * (z - 1 / 2)))‖ at hnorm
    rw [norm_mul, norm_mul, hA, one_mul, Complex.norm_exp, hExp] at hnorm
    rw [hnorm, mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
  have hpow : Real.exp ((n : ℝ) * Real.log d) ≤ Q ^ n := by
    have hd : 0 ≤ d := Nat.cast_nonneg _
    have hlog : Real.log d ≤ Real.log Q := by
      rcases hd.eq_or_lt with heq | hpos
      · rw [← heq, Real.log_zero]
        exact Real.log_nonneg hQ
      · exact Real.log_le_log hpos hCond
    calc
      _ ≤ Real.exp ((n : ℝ) * Real.log Q) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg _))
      _ = Q ^ n := by rw [Real.exp_nat_mul, Real.exp_log (zero_lt_one.trans_le hQ)]
  have hright := globalFiniteHeckeEuler_bounded_right F ω⁻¹
    (r := 1 / 2 + (n : ℝ)) (by linarith) hr.ge
  have hArch := completedTateArchRatio_of_Hecke_box F χ S hs hu hu' n ht hb z hz
  change ‖D z * L z‖ ≤ _
  rw [norm_mul, hNorm, he' hr']
  change ‖D z‖ * (‖(D' (1 - z))⁻¹ * globalFiniteHeckeEuler F ω⁻¹ (1 - z)‖ *
      Real.exp ((n : ℝ) * Real.log d)) ≤ _
  rw [norm_mul]
  calc
    _ = Real.exp ((n : ℝ) * Real.log d) * ‖globalFiniteHeckeEuler F ω⁻¹ (1 - z)‖ *
        ‖D z * (D' (1 - z))⁻¹‖ := by rw [norm_mul]; ring
    _ ≤ _ := mul_le_mul (mul_le_mul hpow hright (norm_nonneg _) (by positivity)) hArch
      (norm_nonneg _) (by positivity)

include hu' μ hν in
/-- The uniform finite Hecke left boundary bound in meromorphic form. -/
theorem exists_globalFiniteHecke_left_bound_of_box
    (hD : ∀ v : GrowthPlace F, v.asIdeal ∣ differentIdeal ℤ (𝓞 F) → v ∈ S)
    (n : ℕ) (hn : 1 ≤ n) {t T Q : ℝ} (ht : |t| ≤ T)
    (hb : manuscriptHeckeArchParametersInBox F χ S hs hu t T)
    (hQ : 1 ≤ Q)
    (hCond : (heckeDiscriminantConductor F
      (normOneEulerCharacter F (heckeNormOneRestriction F χ)) : ℝ) ≤ Q) :
    ∃ f : ℂ → ℂ, MeromorphicOn f univ ∧
      EqOn f (globalFiniteHeckeEuler F (heckeNormOneRestriction F χ)) {z | 1 < z.re} ∧
      ∀ z : ℂ, z.re = 1 / 2 - (n : ℝ) →
        ‖f z‖ ≤ Q ^ n * ‖globalFiniteHeckeEuler F 1 ((1 / 2 + (n : ℝ) : ℝ) : ℂ)‖ *
          ((‖z‖ + (1 + 5 / 2 * T) + (2 * n : ℝ)) / (2 * Real.pi)) ^
            (Module.finrank ℚ F * n) := by
  obtain ⟨f, hm, _, he, hb⟩ :=
    exists_globalFiniteHecke_left_bound_of_box_analytic F χ S hs hu hu' ν η μ hν hD n hn ht hb hQ hCond
  exact ⟨f, hm, he, hb⟩

end

end Masullo
