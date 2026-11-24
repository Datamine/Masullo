import HeckeUniformArchimedeanGrowth
import FiniteHeckeGrowth
import FiniteHeckeReciprocal
import Mathlib.Analysis.Complex.JensenFormula

open Filter Function Ideal IsDedekindDomain MeasureTheory MeromorphicOn Metric NumberField Set Topology
open scoped Classical NumberField Topology

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]
private abbrev K := normOneIdeleClass F
private abbrev Place := HeightOneSpectrum (𝓞 F)

local instance : MeasurableSpace (K F) := borel _
local instance : BorelSpace (K F) := ⟨rfl⟩
local instance : MeasurableSpace (Idele F) := borel _
local instance : BorelSpace (Idele F) := ⟨rfl⟩
local instance (v : Place F) : MeasurableSpace (v.adicCompletion F) := borel _
local instance (v : Place F) : BorelSpace (v.adicCompletion F) := ⟨rfl⟩

variable (ν : Measure (K F)) [ν.IsHaarMeasure]
variable (η : Measure (Idele F)) [η.IsHaarMeasure]
variable [∀ v : Place F, MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : Place F, BorelSpace (v.adicCompletion F)ˣ]
  (μ : ∀ v : Place F, Measure (v.adicCompletion F)ˣ)
  [∀ v : Place F, (μ v).IsHaarMeasure] [∀ v : Place F, SigmaFinite (μ v)]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]
variable (hν : IsWeilQuotientMeasure (principalIdeles F) η Measure.count (globalClassMeasure F ν))

private theorem punctured_eventually_ne (z p : ℂ) : ∀ᶠ w in 𝓝[≠] z, w ≠ p := by
  rcases eq_or_ne z p with rfl | h
  · exact self_mem_nhdsWithin
  · have he : ∀ᶠ w in 𝓝 z, w ≠ p := isOpen_compl_singleton.mem_nhds h
    exact he.filter_mono nhdsWithin_le_nhds

omit [∀ v : Place F, MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : Place F, BorelSpace (v.adicCompletion F)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ] in
private theorem norm_poleFactor_le_sq (ω : PontryaginDual (K F)) (z : ℂ) :
    ‖globalHeckePoleFactor F ω z‖ ≤ (1 + ‖z‖) ^ 2 := by
  by_cases h : ω = 1
  · simp only [globalHeckePoleFactor, h, ite_true, norm_mul]
    rw [pow_two]
    exact mul_le_mul (by linarith : ‖z‖ ≤ 1 + ‖z‖)
      ((norm_sub_le (1 : ℂ) z).trans_eq (by rw [norm_one]))
      (norm_nonneg _) (by positivity)
  · simp only [globalHeckePoleFactor, h, ite_false, norm_one]
    nlinarith [norm_nonneg z]

omit [∀ v : Place F, MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : Place F, BorelSpace (v.adicCompletion F)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ] in
private theorem norm_poleFactor_ge_one_at_two (ω : PontryaginDual (K F)) (y : ℝ) :
    1 ≤ ‖globalHeckePoleFactor F ω (⟨2, y⟩ : ℂ)‖ := by
  by_cases h : ω = 1
  · simp only [globalHeckePoleFactor, h, ite_true, norm_mul]
    have h₁ := Complex.abs_re_le_norm (⟨2, y⟩ : ℂ)
    have h₂ := Complex.abs_re_le_norm (1 - (⟨2, y⟩ : ℂ))
    norm_num [Complex.sub_re] at h₁ h₂
    exact one_le_mul_of_one_le_of_one_le (by linarith) h₂
  · simp [globalHeckePoleFactor, h]

set_option maxHeartbeats 1400000 in
include μ hν in
/-- Uniform polynomial growth of the analytic, pole-cleared finite reference.
Its center values are uniformly bounded below, and its orders dominate the
orders of the completed continuation. -/
theorem exists_globalHecke_cleared_uniform_strip :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ (χ : PontryaginDual (IdeleClass F)) (S : Finset (Place F))
      (hs : Surjective (sIdeleClassInclusion F S))
      (hu : globalNormOneCharacter F (heckeNormOneRestriction F χ) ∈
        (sUnramified F S : Set (QuasiCharacter (IdeleClass F))))
      (_hu' : globalNormOneCharacter F (heckeNormOneRestriction F χ)⁻¹ ∈
        (sUnramified F S : Set (QuasiCharacter (IdeleClass F)))),
      (∀ v : Place F, v.asIdeal ∣ differentIdeal ℤ (𝓞 F) → v ∈ S) →
      ∀ t T Q : ℝ, |t| ≤ T → manuscriptHeckeArchParametersInBox F χ S hs hu t T →
        1 ≤ Q →
        (heckeDiscriminantConductor F (normOneEulerCharacter F (heckeNormOneRestriction F χ)) : ℝ) ≤ Q →
      ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g univ ∧
        (∀ y : ℝ, c ≤ ‖g ⟨2, y⟩‖) ∧
        (∀ z : ℂ, z.re ∈ Icc (-6 : ℝ) 10 →
          ‖g z‖ ≤ C * Q ^ 7 * (1 + T) ^ (Module.finrank ℚ F * 7) *
            (1 + |z.im|) ^ (Module.finrank ℚ F * 7 + 2)) ∧
        ∀ (L : ℂ → ℂ), MeromorphicOn L univ →
          EqOn L (globalCompletedHeckeEuler F (heckeNormOneRestriction F χ) S hs hu)
            {z | 1 < z.re} →
          ∀ z, meromorphicOrderAt L z ≤ meromorphicOrderAt g z := by
  let m := Module.finrank ℚ F * 7
  let N : ℕ := m + 2
  let CL := ‖globalFiniteHeckeEuler F 1 (15 / 2)‖ * 24 ^ m
  let CR := ‖globalFiniteHeckeEuler F 1 10‖
  let E := max (Real.exp ((-(13 / 2 : ℝ)) ^ 2 + (N : ℝ) ^ 2 / 4))
      (Real.exp (10 ^ 2 + (N : ℝ) ^ 2 / 4))
  let C := 121 * (1 + CL + CR) * E
  obtain ⟨c, hc, hcenter⟩ := globalFiniteHeckeEuler_norm_ge_two F
  have hCL : 0 ≤ CL := by dsimp only [CL]; positivity
  have hCR : 0 ≤ CR := norm_nonneg _
  have hE : 0 < E := (Real.exp_pos _).trans_le (le_max_left _ _)
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, c, hC, hc, ?_⟩
  intro χ S hs hu hu' hD t T Q ht hb hQ hCond
  have hT : 0 ≤ T := (abs_nonneg t).trans ht
  let ω := heckeNormOneRestriction F χ
  obtain ⟨f, hf, hfa, hfe, hfleft⟩ :=
    exists_globalFiniteHecke_left_bound_of_box_analytic F χ S hs hu hu' ν η μ hν hD
      7 (by norm_num) ht hb hQ hCond
  obtain ⟨r, L₀, hL₀e, hL₀, _, _, ⟨B, hB, hscale⟩, _⟩ :=
    exists_globalCompletedHeckeContinuation F ω S hs hu η ν μ hν
  let D := completedTateReciprocalArch F S hs ω hu
  let p := globalHeckePoleFactor F ω
  let g (z : ℂ) := D z * (B⁻¹ * globalHeckeClearedZeta F ν ω r z)
  obtain ⟨hg, hgExp⟩ :=
    finiteClearedHeckeReference_exponential_strip F S hs ω hu ν r B (-(13 / 2)) 10
  have hCleared (z : ℂ) (hz₀ : z ≠ 0) (hz₁ : z ≠ 1) : g z = p z * (D z * L₀ z) := by
    dsimp only [g]
    rw [globalHeckeClearedZeta_eq F ν ω r z hz₀ hz₁]
    change D z * (B⁻¹ * (p z * _)) = _
    rw [show globalZetaContinued F ν r (compactIdeleClassCharacter F ω) 0 z = B * L₀ z
      from congrFun hscale z]
    calc
      _ = (B⁻¹ * B) * (p z * (D z * L₀ z)) := by ring
      _ = _ := by rw [inv_mul_cancel₀ hB, one_mul]
  have hGerm (z : ℂ) : g =ᶠ[𝓝[≠] z] p * f := by
    filter_upwards [punctured_eventually_ne z 0, punctured_eventually_ne z 1,
      globalFiniteHeckeContinuation_germ F ω S hs hu hL₀ hf hL₀e hfe z] with w hw₀ hw₁ hw
    exact (hCleared w hw₀ hw₁).trans (congrArg (p w * ·) hw.symm)
  have hPoint (z : ℂ) (hz₀ : z ≠ 0) (hz₁ : z ≠ 1) : g z = p z * f z := by
    have h : z ∈ ({0, 1} : Set ℂ)ᶜ := by simp [hz₀, hz₁]
    have hc' : ContinuousAt (p * f) z :=
      (globalHeckePoleFactor_analytic F ω z).continuousAt.mul (hfa z h).continuousAt
    exact (((hg z (mem_univ z)).continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE hc').mp
      (hGerm z)).eq_of_nhds
  have hGcenter (y : ℝ) : c ≤ ‖g ⟨2, y⟩‖ := by
    let z : ℂ := ⟨2, y⟩
    have hz₀ : z ≠ 0 := fun h ↦ by have := congrArg Complex.re h; norm_num [z] at this
    have hz₁ : z ≠ 1 := fun h ↦ by have := congrArg Complex.re h; norm_num [z] at this
    rw [hPoint z hz₀ hz₁, hfe (show (1 : ℝ) < z.re by norm_num [z]), norm_mul]
    exact (hcenter ω y).trans
      (le_mul_of_one_le_left (norm_nonneg _) (norm_poleFactor_ge_one_at_two F ω y))
  have hLeft (z : ℂ) (hz : z.re = -(13 / 2 : ℝ)) :
      ‖f z‖ ≤ CL * Q ^ 7 * (1 + T) ^ m * (1 + |z.im|) ^ m := by
    have h := hfleft z (by rw [hz]; norm_num)
    have hzN := Complex.norm_le_abs_re_add_abs_im z
    rw [hz, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 13 / 2)] at hzN
    have hPi : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
    have hb' : (‖z‖ + (1 + 5 / 2 * T) + (2 * (7 : ℕ) : ℝ)) / (2 * Real.pi) ≤
        24 * (1 + T) * (1 + |z.im|) := by
      apply (div_le_iff₀ (by positivity : 0 < 2 * Real.pi)).2
      refine le_trans ?_ (le_mul_of_one_le_right (by positivity) hPi)
      push_cast
      nlinarith [abs_nonneg z.im, mul_nonneg hT (abs_nonneg z.im)]
    refine h.trans ((mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) hb' m) (by positivity)).trans_eq ?_)
    norm_num only [Nat.cast_ofNat]
    unfold CL
    rw [mul_pow, mul_pow]
    norm_num
    ring
  let P : ℝ := Q ^ 7 * (1 + T) ^ m
  have hP : 1 ≤ P := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hQ) (one_le_pow₀ (by linarith))
  let W := 121 * (1 + CL + CR) * P
  have hW : 0 ≤ W := by dsimp only [W]; positivity
  have hboundary (z : ℂ) (hz : z.re = -(13 / 2 : ℝ) ∨ z.re = 10) :
      ‖g z‖ ≤ W * (1 + |z.im|) ^ (N : ℝ) := by
    have hz₀ : z ≠ 0 := by rintro rfl; rcases hz with h | h <;> norm_num at h
    have hz₁ : z ≠ 1 := by rintro rfl; rcases hz with h | h <;> norm_num at h
    have hzR : |z.re| ≤ 10 := by
      rcases hz with h | h <;> rw [h] <;> norm_num
    have hzN := Complex.norm_le_abs_re_add_abs_im z
    have hp : ‖p z‖ ≤ 121 * (1 + |z.im|) ^ 2 := by
      refine (norm_poleFactor_le_sq F ω z).trans ?_
      calc
        _ ≤ (11 * (1 + |z.im|)) ^ 2 := by
          apply pow_le_pow_left₀ (by positivity)
          linarith [abs_nonneg z.im]
        _ = _ := by ring
    have hfB : ‖f z‖ ≤ (1 + CL + CR) * P * (1 + |z.im|) ^ m := by
      rcases hz with hl | hr
      · refine (hLeft z hl).trans ?_
        calc
          _ = CL * P * (1 + |z.im|) ^ m := by dsimp only [P]; ring
          _ ≤ _ := by gcongr; linarith
      · rw [hfe (show 1 < z.re by rw [hr]; norm_num)]
        refine (globalFiniteHeckeEuler_bounded_right F ω (r := 10) (by norm_num) hr.ge).trans ?_
        apply le_trans (show CR ≤ (1 + CL + CR) * P from
          (show CR ≤ 1 + CL + CR by linarith).trans (le_mul_of_one_le_right (by positivity) hP))
        exact le_mul_of_one_le_right (by positivity) (one_le_pow₀ (by linarith [abs_nonneg z.im]))
    rw [hPoint z hz₀ hz₁, norm_mul, Real.rpow_natCast]
    refine (mul_le_mul hp hfB (norm_nonneg _) (by positivity)).trans_eq ?_
    dsimp only [W, N]
    rw [pow_add]
    ring
  have hStrip := holomorphic_poly_interpolate_exp_explicit
    (by norm_num : -(13 / 2 : ℝ) < 10) (fun z _ ↦ hg z (mem_univ _)) (by positivity)
    hgExp hW hW (Nat.cast_nonneg N) (Nat.cast_nonneg N)
    (fun z hz ↦ hboundary z (Or.inl hz)) (fun z hz ↦ hboundary z (Or.inr hz))
  refine ⟨g, hg, hGcenter, ?_, ?_⟩
  · intro z hz
    have h := hStrip z ⟨(by norm_num : -(13 / 2 : ℝ) ≤ -6).trans hz.1, hz.2⟩
    rw [show (1 - (z.re - -(13 / 2 : ℝ)) / (10 - -(13 / 2 : ℝ))) * (N : ℝ) +
        (z.re - -(13 / 2 : ℝ)) / (10 - -(13 / 2 : ℝ)) * (N : ℝ) = (N : ℝ) by ring,
      Real.rpow_natCast, ← mul_max_of_nonneg _ _ hW] at h
    convert h using 1
    dsimp only [W, E, C, P]
    ring
  · intro L hL hLe z
    have he := globalFiniteHeckeContinuation_germ F ω S hs hu hL hf hLe hfe z
    have he' : g =ᶠ[𝓝[≠] z] (p * D) * L := by
      filter_upwards [hGerm z, he] with w hw hw'
      change g w = (p w * D w) * L w
      change g w = p w * f w at hw
      change f w = D w * L w at hw'
      rw [hw, hw', mul_assoc]
    rw [meromorphicOrderAt_congr he', meromorphicOrderAt_mul
      ((globalHeckePoleFactor_analytic F ω z).mul
        (archimedeanNumberFieldZetaDenominator_analytic F _ _ z)).meromorphicAt
      (hL z (mem_univ z))]
    exact le_add_of_nonneg_left (((globalHeckePoleFactor_analytic F ω z).mul
      (archimedeanNumberFieldZetaDenominator_analytic F _ _ z)).meromorphicOrderAt_nonneg)

/-- The closed critical strip in a window of radius one about the ordinate. -/
def heckeHeightWindow (y : ℝ) : Set ℂ :=
  Icc (0 : ℝ) 1 ×ℂ Icc (y - 1) (y + 1)

private theorem heckeHeightWindow_subset_disk (y : ℝ) :
    heckeHeightWindow y ⊆ closedBall (⟨2, y⟩ : ℂ) 4 := by
  intro z hz
  obtain ⟨hr, hi⟩ := Complex.mem_reProdIm.mp hz
  rw [mem_closedBall, dist_eq_norm]
  apply (Complex.norm_le_abs_re_add_abs_im _).trans
  have hre : |z.re - 2| ≤ 2 := abs_le.mpr ⟨by linarith [hr.1], by linarith [hr.2]⟩
  have him : |z.im - y| ≤ 1 := abs_le.mpr ⟨by linarith [hi.1], by linarith [hi.2]⟩
  change |z.re - 2| + |z.im - y| ≤ 4
  linarith

private theorem positiveDivisor_finiteSupport (L : ℂ → ℂ) {B : Set ℂ} (hB : IsCompact B) :
    (Function.support fun z ↦ max (divisor L B z) 0).Finite :=
  ((divisor L B).finiteSupport hB).subset (by
    intro z hz
    contrapose! hz
    simp only [Function.notMem_support] at hz ⊢
    rw [hz, max_self])

private theorem heckeHeightWindow_jensen {g L : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g univ)
    (hL : MeromorphicOn L univ) (hord : ∀ z, meromorphicOrderAt L z ≤ meromorphicOrderAt g z)
    (y c M : ℝ) (hc : 0 < c) (hM : 1 ≤ M) (hlow : c ≤ ‖g ⟨2, y⟩‖)
    (hhigh : ∀ z ∈ sphere (⟨2, y⟩ : ℂ) 8, ‖g z‖ ≤ M) :
    ((∑ᶠ z, max (divisor L (heckeHeightWindow y) z) 0 : ℤ) : ℝ) ≤
      Real.log (M / c) / Real.log 2 := by
  let z₀ : ℂ := ⟨2, y⟩
  let B := heckeHeightWindow y
  let D := closedBall z₀ 4
  have hpos : 0 < ‖g z₀‖ := hc.trans_le hlow
  have hzero : g z₀ ≠ 0 := norm_ne_zero_iff.mp hpos.ne'
  have ha := hg z₀ (mem_univ z₀)
  have ho₀ : meromorphicOrderAt g z₀ = 0 := by
    rw [ha.meromorphicOrderAt_eq, ha.analyticOrderAt_eq_zero.mpr hzero]
    rfl
  have ho (z : ℂ) : meromorphicOrderAt g z ≠ ⊤ :=
    (hg.meromorphicOn.exists_meromorphicOrderAt_ne_top_iff_forall isConnected_univ).mp
      ⟨⟨z₀, mem_univ z₀⟩, ho₀.trans_ne (by simp)⟩ ⟨z, mem_univ z⟩
  have hJB := AnalyticOnNhd.sum_divisor_le (c := z₀) (r := 4) (R := 8)
    (by norm_num) (by norm_num) hM (hg.mono (subset_univ _)) hzero
    (by simpa only [abs_of_nonneg (show (0 : ℝ) ≤ 8 by norm_num)] using hhigh)
  have hd : AnalyticOnNhd ℂ g D := hg.mono (subset_univ _)
  have hB : IsCompact B := isCompact_Icc.reProdIm isCompact_Icc
  have hFin := positiveDivisor_finiteSupport L hB
  have hcompare : (∑ᶠ z, max (divisor L B z) 0) ≤ ∑ᶠ z, divisor g D z := by
    refine finsum_le_finsum' hFin
      ((divisor g D).finiteSupport (isCompact_closedBall _ _)) fun z ↦ ?_
    apply max_le _ (hd.divisor_nonneg z)
    by_cases hz : z ∈ B
    · have hzD : z ∈ D := heckeHeightWindow_subset_disk y hz
      rw [MeromorphicOn.divisor_apply (fun w _ ↦ hL w (mem_univ w)) hz,
        MeromorphicOn.divisor_apply hd.meromorphicOn hzD]
      exact WithTop.untop₀_le_untop₀ (ho z) (hord z)
    · rw [(divisor L B).apply_eq_zero_of_notMem hz]
      exact hd.divisor_nonneg z
  calc
    _ ≤ ((∑ᶠ z, divisor g D z : ℤ) : ℝ) := by exact_mod_cast hcompare
    _ ≤ Real.log (M / ‖g z₀‖) / Real.log 2 := by
      rw [show |(4 : ℝ)| = 4 by norm_num, show (8 : ℝ) / 4 = 2 by norm_num] at hJB
      exact hJB
    _ ≤ Real.log (M / c) / Real.log 2 := by
      apply div_le_div_of_nonneg_right _ (Real.log_nonneg (by norm_num))
      apply Real.log_le_log (by positivity)
      exact div_le_div_of_nonneg_left (zero_le_one.trans hM) hc hlow

set_option maxHeartbeats 900000 in
include μ hν in
/-- Across a Hecke parameter box the multiplicity of completed zeros in
each height window satisfies a single Jensen bound. -/
theorem globalCompletedHecke_zeroMultiplicity_uniform :
    ∃ A : ℝ, 0 < A ∧
    ∀ (χ : PontryaginDual (IdeleClass F)) (S : Finset (Place F))
      (hs : Surjective (sIdeleClassInclusion F S))
      (hu : globalNormOneCharacter F (heckeNormOneRestriction F χ) ∈
        (sUnramified F S : Set (QuasiCharacter (IdeleClass F))))
      (_hu' : globalNormOneCharacter F (heckeNormOneRestriction F χ)⁻¹ ∈
        (sUnramified F S : Set (QuasiCharacter (IdeleClass F)))),
      (∀ v : Place F, v.asIdeal ∣ differentIdeal ℤ (𝓞 F) → v ∈ S) →
      ∀ t T Q : ℝ, |t| ≤ T → manuscriptHeckeArchParametersInBox F χ S hs hu t T →
        1 ≤ Q →
        (heckeDiscriminantConductor F (normOneEulerCharacter F (heckeNormOneRestriction F χ)) : ℝ) ≤ Q →
      ∀ (L : ℂ → ℂ), MeromorphicOn L univ →
        EqOn L (globalCompletedHeckeEuler F (heckeNormOneRestriction F χ) S hs hu) {z | 1 < z.re} →
      ∀ y : ℝ, ((∑ᶠ z, max (divisor L (heckeHeightWindow y) z) 0 : ℤ) : ℝ) ≤
        Real.log (A * Q ^ 7 * (1 + T) ^ (Module.finrank ℚ F * 7) *
          (1 + |y|) ^ (Module.finrank ℚ F * 7 + 2)) / Real.log 2 := by
  obtain ⟨C, c, hC, hc, hStrip⟩ := exists_globalHecke_cleared_uniform_strip F ν η μ hν
  let m := Module.finrank ℚ F * 7
  let N := m + 2
  let A := (1 + C) * 9 ^ N / c
  refine ⟨A, by dsimp only [A]; positivity, ?_⟩
  intro χ S hs hu hu' hD t T Q ht hb hQ hCond L hL he y
  obtain ⟨g, hg, hlow, hgB, hord⟩ := hStrip χ S hs hu hu' hD t T Q ht hb hQ hCond
  have hT : 0 ≤ T := (abs_nonneg t).trans ht
  let M := (1 + C) * Q ^ 7 * (1 + T) ^ m * (9 * (1 + |y|)) ^ N
  have hm : 1 ≤ M := by
    apply one_le_mul_of_one_le_of_one_le
    · apply one_le_mul_of_one_le_of_one_le
      · exact one_le_mul_of_one_le_of_one_le (by linarith) (one_le_pow₀ hQ)
      · exact one_le_pow₀ (by linarith)
    · exact one_le_pow₀ (by linarith [abs_nonneg y])
  have hhigh (z : ℂ) (hz : z ∈ sphere (⟨2, y⟩ : ℂ) 8) : ‖g z‖ ≤ M := by
    have hd : ‖z - (⟨2, y⟩ : ℂ)‖ = 8 := by rwa [mem_sphere, dist_eq_norm] at hz
    have hr := Complex.abs_re_le_norm (z - (⟨2, y⟩ : ℂ))
    have hi := Complex.abs_im_le_norm (z - (⟨2, y⟩ : ℂ))
    rw [hd] at hr hi
    change |z.re - 2| ≤ 8 at hr
    change |z.im - y| ≤ 8 at hi
    have hmem : z.re ∈ Icc (-6 : ℝ) 10 := by
      obtain ⟨hl, hu⟩ := abs_le.mp hr
      exact ⟨by linarith, by linarith⟩
    have him : 1 + |z.im| ≤ 9 * (1 + |y|) := by
      have h := abs_add_le (z.im - y) y
      rw [sub_add_cancel] at h
      linarith [abs_nonneg y]
    refine (hgB z hmem).trans ?_
    change C * Q ^ 7 * (1 + T) ^ m * (1 + |z.im|) ^ N ≤ M
    dsimp only [M]
    gcongr
    linarith
  have h := heckeHeightWindow_jensen hg hL (hord L hL he) y c M hc hm (hlow y) hhigh
  have hM : M / c = A * Q ^ 7 * (1 + T) ^ m * (1 + |y|) ^ N := by
    dsimp only [M, A]
    rw [mul_pow]
    ring
  rwa [hM] at h

/-- The completed zeros considered up to a fixed absolute height. -/
def heckeTruncatedStrip (H : ℕ) : Set ℂ :=
  Icc (0 : ℝ) 1 ×ℂ Icc (-(H : ℝ)) (H : ℝ)

private theorem heckeTruncatedStrip_count_le_sum {L : ℂ → ℂ} (hL : MeromorphicOn L univ)
    (H : ℕ) :
    (∑ᶠ z, max (divisor L (heckeTruncatedStrip H) z) 0) ≤
      ∑ j ∈ Finset.Icc (-(H : ℤ)) (H : ℤ), ∑ᶠ z, max (divisor L (heckeHeightWindow j) z) 0 := by
  let B := heckeTruncatedStrip H
  let J := Finset.Icc (-(H : ℤ)) (H : ℤ)
  let w (j : ℤ) (z : ℂ) := max (divisor L (heckeHeightWindow j) z) 0
  have hFin (j : ℤ) : (Function.support (w j)).Finite :=
    positiveDivisor_finiteSupport L (isCompact_Icc.reProdIm isCompact_Icc)
  have hsumFin : (Function.support fun z ↦ ∑ j ∈ J, w j z).Finite := by
    classical
    apply (J.finite_toSet.biUnion fun j _ ↦ hFin j).subset
    intro z hz
    contrapose! hz
    apply Function.notMem_support.mpr
    apply Finset.sum_eq_zero
    intro j hj
    have hjz : z ∉ Function.support (w j) :=
      fun he ↦ hz (mem_iUnion₂.mpr ⟨j, hj, he⟩)
    exact Function.notMem_support.mp hjz
  change (∑ᶠ z, max (divisor L B z) 0) ≤ ∑ j ∈ J, ∑ᶠ z, w j z
  rw [sum_finsum_comm J w (fun j _ ↦ hFin j)]
  refine finsum_le_finsum' (positiveDivisor_finiteSupport L
    (isCompact_Icc.reProdIm isCompact_Icc)) hsumFin fun z ↦ ?_
  by_cases hz : z ∈ B
  · obtain ⟨hr, hi⟩ := Complex.mem_reProdIm.mp hz
    let j := ⌊z.im⌋
    have hlo : -(H : ℤ) ≤ j := Int.le_floor.mpr (by simpa using hi.1)
    have hup : j ≤ (H : ℤ) := Int.floor_le_iff.mpr (by push_cast; linarith [hi.2])
    have hj : j ∈ J := Finset.mem_Icc.mpr ⟨hlo, hup⟩
    have hwin : z ∈ heckeHeightWindow j := Complex.mem_reProdIm.mpr
      ⟨hr, ⟨by linarith [Int.floor_le z.im], (Int.lt_floor_add_one z.im).le⟩⟩
    have hEq : max (divisor L B z) 0 = w j z := by
      unfold w
      rw [MeromorphicOn.divisor_apply (fun x _ ↦ hL x (mem_univ x)) hz,
        MeromorphicOn.divisor_apply (fun x _ ↦ hL x (mem_univ x)) hwin]
    rw [hEq]
    exact Finset.single_le_sum (f := fun i : ℤ ↦ w i z) (fun i _ ↦ le_max_right _ _) hj
  · rw [(divisor L B).apply_eq_zero_of_notMem hz, max_self]
    exact Finset.sum_nonneg fun i _ ↦ (le_max_right (divisor L (heckeHeightWindow i) z) 0)

set_option maxHeartbeats 900000 in
include μ hν in
/-- A single polynomial bounds the total completed zero multiplicity up to
the radius of an archimedean box. -/
theorem globalCompletedHecke_truncatedMultiplicity_uniform :
    ∃ A : ℝ, 0 < A ∧
    ∀ (χ : PontryaginDual (IdeleClass F)) (S : Finset (Place F))
      (hs : Surjective (sIdeleClassInclusion F S))
      (hu : globalNormOneCharacter F (heckeNormOneRestriction F χ) ∈
        (sUnramified F S : Set (QuasiCharacter (IdeleClass F))))
      (_hu' : globalNormOneCharacter F (heckeNormOneRestriction F χ)⁻¹ ∈
        (sUnramified F S : Set (QuasiCharacter (IdeleClass F)))),
      (∀ v : Place F, v.asIdeal ∣ differentIdeal ℤ (𝓞 F) → v ∈ S) →
      ∀ (H : ℕ) (t Q : ℝ), |t| ≤ H → manuscriptHeckeArchParametersInBox F χ S hs hu t H →
        1 ≤ Q →
        (heckeDiscriminantConductor F (normOneEulerCharacter F (heckeNormOneRestriction F χ)) : ℝ) ≤ Q →
      ∀ (L : ℂ → ℂ), MeromorphicOn L univ →
        EqOn L (globalCompletedHeckeEuler F (heckeNormOneRestriction F χ) S hs hu) {z | 1 < z.re} →
        ((∑ᶠ z, max (divisor L (heckeTruncatedStrip H) z) 0 : ℤ) : ℝ) ≤
          A * Q ^ 7 * (1 + (H : ℝ)) ^ (Module.finrank ℚ F * 14 + 3) := by
  obtain ⟨A, hA, hbound⟩ := globalCompletedHecke_zeroMultiplicity_uniform F ν η μ hν
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨2 * (A / Real.log 2), by positivity, ?_⟩
  intro χ S hs hu hu' hD H t Q ht hb hQ hCond L hL he
  let J := Finset.Icc (-(H : ℤ)) (H : ℤ)
  let m := Module.finrank ℚ F * 7
  let N := m + 2
  let W := (A / Real.log 2) * Q ^ 7 * (1 + (H : ℝ)) ^ (m + N)
  have hW : 0 ≤ W := by dsimp only [W]; positivity
  have hOne (j : ℤ) (hj : j ∈ J) :
      ((∑ᶠ z, max (divisor L (heckeHeightWindow j) z) 0 : ℤ) : ℝ) ≤ W := by
    have hj' := Finset.mem_Icc.mp hj
    have hjAbs : |(j : ℝ)| ≤ H := abs_le.mpr ⟨by exact_mod_cast hj'.1, by exact_mod_cast hj'.2⟩
    refine (hbound χ S hs hu hu' hD t H Q ht hb hQ hCond L hL he j).trans ?_
    let x := A * Q ^ 7 * (1 + (H : ℝ)) ^ m * (1 + |(j : ℝ)|) ^ N
    have hx : 0 < x := by dsimp only [x]; positivity
    change Real.log x / Real.log 2 ≤ W
    calc
      _ ≤ x / Real.log 2 := div_le_div_of_nonneg_right
        ((Real.log_le_sub_one_of_pos hx).trans (by linarith)) hlog.le
      _ ≤ _ := by
        dsimp only [x, W]
        rw [pow_add (1 + (H : ℝ)) m N]
        calc
          _ = (A / Real.log 2) * Q ^ 7 * (1 + (H : ℝ)) ^ m * (1 + |(j : ℝ)|) ^ N := by ring
          _ ≤ (A / Real.log 2) * Q ^ 7 * (1 + (H : ℝ)) ^ m * (1 + (H : ℝ)) ^ N :=
            mul_le_mul_of_nonneg_left
              (pow_le_pow_left₀ (by positivity) (show 1 + |(j : ℝ)| ≤ 1 + (H : ℝ) by linarith) N)
              (by positivity)
          _ = _ := by ring
  have hJ : J.card = 2 * H + 1 := by
    dsimp only [J]
    rw [Int.card_Icc]
    omega
  have hbase := heckeTruncatedStrip_count_le_sum hL H
  calc
    _ ≤ ∑ j ∈ J, ((∑ᶠ z, max (divisor L (heckeHeightWindow j) z) 0 : ℤ) : ℝ) := by
      exact_mod_cast hbase
    _ ≤ ∑ j ∈ J, W := Finset.sum_le_sum hOne
    _ = (J.card : ℝ) * W := by simp
    _ ≤ (2 * (1 + (H : ℝ))) * W := by
      apply mul_le_mul_of_nonneg_right _ hW
      rw [hJ]
      push_cast
      linarith
    _ = _ := by
      dsimp only [W]
      rw [show Module.finrank ℚ F * 14 + 3 = m + N + 1 by dsimp only [m, N]; omega,
        pow_succ]
      ring

end
end Masullo
