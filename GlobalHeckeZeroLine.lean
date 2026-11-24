import HeckeEulerNonvanishing
import CompactSpectrumDivision

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical FourierTransform NumberField SchwartzMap

namespace Masullo
noncomputable section

variable (F : Type*) [Field F] [NumberField F]

private abbrev K := normOneIdeleClass F
private abbrev Place := HeightOneSpectrum (𝓞 F)

local instance zeroLineIdeleMeasurable : MeasurableSpace (Idele F) := borel _
local instance zeroLineIdeleBorel : BorelSpace (Idele F) := ⟨rfl⟩
local instance zeroLineNormOneMeasurable : MeasurableSpace (K F) := borel _
local instance zeroLineNormOneBorel : BorelSpace (K F) := ⟨rfl⟩

variable (η : Measure (Idele F)) [η.IsHaarMeasure]
variable (ν : Measure (K F)) [ν.IsHaarMeasure]
variable [∀ v : Place F, MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : Place F, BorelSpace (v.adicCompletion F)ˣ]
  (μ : ∀ v : Place F, Measure (v.adicCompletion F)ˣ)
  [∀ v : Place F, (μ v).IsHaarMeasure] [∀ v : Place F, SigmaFinite (μ v)]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]
variable (hν : IsWeilQuotientMeasure (principalIdeles F) η Measure.count (globalClassMeasure F ν))

private abbrev Z (ω : PontryaginDual (K F)) (f : GlobalBruhat F) :=
  globalZetaContinued F ν f (compactIdeleClassCharacter F ω) 0

include μ hν in
/-- At each regular point of the zero line, an actual adelic test has a
continued zeta transform of order zero. The test is the Fourier transform
of a completed Euler reference for the inverse character. -/
theorem exists_globalZeta_order_eq_zero_zero_line (ω : PontryaginDual (K F))
    (z : ℂ) (hz : z.re = 0) (hcase : ω ≠ 1 ∨ z ≠ 0) :
    ∃ f : GlobalBruhat F, meromorphicOrderAt (Z F ν ω f) z = 0 := by
  obtain ⟨S, hS⟩ := exists_homogeneousThetaPlaceBase F ω⁻¹
  obtain ⟨hs, hu⟩ := hS S Subset.rfl
  obtain ⟨r, L, he, hL, ho, _, _, _⟩ :=
    exists_globalCompletedHeckeContinuation F ω⁻¹ S hs hu η ν μ hν
  have hc : ω⁻¹ ≠ 1 ∨ (1 - z).im ≠ 0 := by
    rcases hcase with hω | hz₀
    · exact Or.inl (fun h ↦ hω (inv_eq_one.mp h))
    · right
      intro h
      apply hz₀
      exact Complex.ext (by simpa using hz) (by simpa [Complex.sub_im] using h)
  have hp : (1 - z : ℂ) = 1 + ((1 - z : ℂ).im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [Complex.sub_re, Complex.mul_re, Complex.mul_im, hz]
  have hL₀ : meromorphicOrderAt L (1 - z) = 0 := by
    rw [hp]
    exact globalCompletedHecke_order_eq_zero_one_line F η ν μ hν ω⁻¹ S hs hu _ hL he hc
  refine ⟨GlobalBruhat.fourier F r, ?_⟩
  have hFE : Z F ν ω (GlobalBruhat.fourier F r) =
      Z F ν ω⁻¹ r ∘ (fun w : ℂ ↦ 1 - w) := by
    funext w
    have h := globalZetaContinued_compact_functionalEquation F ν r ω⁻¹ (1 - w)
    simpa only [Z, Function.comp_apply, inv_inv, sub_sub_cancel] using h.symm
  have ha : AnalyticAt ℂ (fun w : ℂ ↦ 1 - w) z := analyticAt_const.sub analyticAt_id
  have hd : deriv (fun w : ℂ ↦ 1 - w) z ≠ 0 := by simp
  rw [hFE, meromorphicOrderAt_comp_of_deriv_ne_zero ha hd, ← ho, hL₀]

omit [ν.IsHaarMeasure]
  [∀ v : Place F, MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : Place F, BorelSpace (v.adicCompletion F)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ] in
private theorem normOneWeight_eq (ω : PontryaginDual (K F)) (k : K F) (z : ℂ) :
    (ideleNormTwist F (compactIdeleClassCharacter F ω) z k.val : ℂ) = (ω k : ℂ) := by
  change (compactIdeleClassCharacter F ω k.val : ℂ) * ideleNormPower F z k.val = _
  rw [compactIdeleClassCharacter_apply_normOne F ω k, ideleNormPower, k.property,
    Real.log_one, Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one]

include μ hν in
/-- At a nontrivial angular character, the polar-free adelic tests have
no common zero on the zero line, including at zero frequency. -/
theorem exists_polarFree_globalZeta_ne_zero_zero_line_of_ne_one
    (ω : PontryaginDual (K F)) (hω : ω ≠ 1) (z : ℂ) (hz : z.re = 0) :
    ∃ f : GlobalBruhat F, GlobalBruhat.polarEvaluation F f = 0 ∧ Z F ν ω f z ≠ 0 := by
  obtain ⟨f, hf⟩ := exists_globalZeta_order_eq_zero_zero_line F η ν μ hν ω z hz (Or.inl hω)
  have ha : AnalyticAt ℂ (Z F ν ω f) z :=
    globalZetaContinued_entire_of_polar_zero F ν f _ (compactIdeleClassCharacter_unitary F ω)
      0 (Or.inl ((compactIdeleClassCharacter_integral F ν ω).trans (ite_eq_right hω))) z (mem_univ z)
  have hval := ha.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mp hf
  obtain ⟨k, hk⟩ : ∃ k : K F, ω k ≠ 1 := by
    by_contra! h
    apply hω
    ext k
    exact congrArg Subtype.val (h k)
  obtain ⟨g, hg⟩ := ideleClassMap_surjective F k.val
  have hgN : ideleNorm F g = 1 := by
    rw [← ideleClassNorm_mk, hg]
    exact k.property
  refine ⟨GlobalBruhat.leftTranslate F g f - f, ?_, ?_⟩
  · rw [map_sub, polarEvaluation_leftTranslate, hgN, one_smul]
    exact sub_eq_zero.mpr (Prod.eta _)
  · have he := globalZetaContinued_leftTranslate F η ν hν g f ω z
      (fun h ↦ (hω h).elim)
    change Z F ν ω (GlobalBruhat.leftTranslate F g f) z =
      (ideleNormTwist F (compactIdeleClassCharacter F ω) z (ideleClassMap F g) : ℂ) *
        Z F ν ω f z at he
    rw [hg, normOneWeight_eq F ω k] at he
    simp only [Z, ← globalContinuedMellinEval_apply, map_sub]
    simp only [globalContinuedMellinEval_apply]
    change Z F ν ω (GlobalBruhat.leftTranslate F g f) z - Z F ν ω f z ≠ 0
    rw [he, ← sub_one_mul]
    exact mul_ne_zero (sub_ne_zero.mpr (fun h ↦ hk (Circle.coe_injective
      (h.trans Circle.coe_one.symm)))) hval

omit [ν.IsHaarMeasure]
  [∀ v : Place F, MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : Place F, BorelSpace (v.adicCompletion F)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ] in
private theorem radial_trivialWeight (g : Idele F) (d : ℝ)
    (hg : ideleClassMap F g = ideleClassExpSection F (Multiplicative.ofAdd d)) (z : ℂ) :
    (ideleNormTwist F (compactIdeleClassCharacter F 1) z (ideleClassMap F g) : ℂ) =
      Complex.exp (z * (d : ℂ)) := by
  change (compactIdeleClassCharacter F 1 (ideleClassMap F g) : ℂ) *
    ideleNormPower F z (ideleClassMap F g) = _
  rw [hg]
  have hc : (compactIdeleClassCharacter F 1
      (ideleClassExpSection F (Multiplicative.ofAdd d)) : ℂ) = 1 := by
    exact compactIdeleClassCharacter_apply_ray F 1 d
  rw [hc, one_mul, ideleNormPower, ideleClassNorm_expSection, Real.log_exp]
  rfl

include μ hν in
/-- At a nonzero ordinate on the zero line of the trivial character,
two translation differences kill the polar evaluations and preserve
nonvanishing at the specified ordinate. -/
theorem exists_polarFree_globalZeta_ne_zero_zero_line_trivial
    (z : ℂ) (hz : z.re = 0) (hz₀ : z ≠ 0) :
    ∃ f : GlobalBruhat F, GlobalBruhat.polarEvaluation F f = 0 ∧ Z F ν 1 f z ≠ 0 := by
  obtain ⟨f, hf⟩ := exists_globalZeta_order_eq_zero_zero_line F η ν μ hν 1 z hz (Or.inr hz₀)
  have hz₁ : z ≠ 1 := fun h ↦ by simp [h] at hz
  have ha : AnalyticAt ℂ (Z F ν 1 f) z :=
    globalZetaContinued_analyticAt F ν f _ (compactIdeleClassCharacter_unitary F 1) 0 z
      (by simpa using hz₀) (by simpa using sub_ne_zero.mpr hz₁)
  have hval := ha.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mp hf
  have him : z.im ≠ 0 := fun h ↦ hz₀ (Complex.ext (by simpa using hz) (by simpa using h))
  let d := Real.pi / z.im
  obtain ⟨g, hg⟩ := ideleClassMap_surjective F (ideleClassExpSection F (Multiplicative.ofAdd d))
  have hp : z * (d : ℂ) = (Real.pi : ℂ) * Complex.I := by
    apply Complex.ext
    · simp [Complex.mul_re, hz]
    · simpa [Complex.mul_im, d, mul_comm] using (div_mul_cancel₀ Real.pi him)
  have hw : (ideleNormTwist F (compactIdeleClassCharacter F 1) z (ideleClassMap F g) : ℂ)
      = -1 := by
    rw [radial_trivialWeight F g d hg, hp, Complex.exp_pi_mul_I]
  have hcov (u : GlobalBruhat F) :
      Z F ν 1 (GlobalBruhat.leftTranslate F g u) z = - Z F ν 1 u z := by
    have h := globalZetaContinued_leftTranslate F η ν hν g u 1 z (fun _ ↦ ⟨hz₀, hz₁⟩)
    change Z F ν 1 (GlobalBruhat.leftTranslate F g u) z =
      (ideleNormTwist F (compactIdeleClassCharacter F 1) z (ideleClassMap F g) : ℂ) * Z F ν 1 u z at h
    simpa only [hw, neg_one_mul] using h
  let u := GlobalBruhat.leftTranslate F g f - f
  let c := ideleNorm F g
  refine ⟨GlobalBruhat.leftTranslate F g u - (c : ℂ) • u, ?_, ?_⟩
  · have hu : (GlobalBruhat.polarEvaluation F u).1 = 0 := by
      simp only [u, map_sub, polarEvaluation_leftTranslate, Prod.fst_sub, sub_self]
    rw [map_sub, polarEvaluation_leftTranslate, map_smul, hu]
    apply sub_eq_zero.mpr
    apply Prod.ext
    · simp [hu]
    · simp [Complex.real_smul, c]
  · have hu : Z F ν 1 u z = -2 * Z F ν 1 f z := by
      dsimp only [u]
      simp only [Z, ← globalContinuedMellinEval_apply, map_sub]
      simp only [globalContinuedMellinEval_apply]
      change Z F ν 1 (GlobalBruhat.leftTranslate F g f) z - Z F ν 1 f z = _
      rw [hcov]
      ring
    simp only [Z, ← globalContinuedMellinEval_apply, map_sub, map_smul, smul_eq_mul]
    simp only [globalContinuedMellinEval_apply]
    change Z F ν 1 (GlobalBruhat.leftTranslate F g u) z - (c : ℂ) * Z F ν 1 u z ≠ 0
    rw [hcov, ← neg_one_mul (Z F ν 1 u z), ← sub_mul, hu]
    have hc : 0 < c := ideleNorm_pos F g
    have hcoeff : (-1 : ℂ) - (c : ℂ) ≠ 0 := by
      intro h
      have he := congrArg Complex.re h
      simp at he
      linarith
    exact mul_ne_zero hcoeff (mul_ne_zero (by norm_num) hval)

include hν in
omit [∀ v : Place F, MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : Place F, BorelSpace (v.adicCompletion F)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ] in
/-- At the origin, a radial translation difference removes the simple
pole of a test with polar values `(1, 0)` and leaves a nonzero value. -/
theorem exists_polarFree_globalZeta_ne_zero_at_origin :
    ∃ f : GlobalBruhat F, GlobalBruhat.polarEvaluation F f = 0 ∧ Z F ν 1 f 0 ≠ 0 := by
  obtain ⟨f, hf⟩ := GlobalBruhat.polarEvaluation_surjective F (1,0)
  obtain ⟨g, hg⟩ := ideleClassMap_surjective F (ideleClassExpSection F (Multiplicative.ofAdd 1))
  let u := GlobalBruhat.leftTranslate F g f - f
  have hpol : GlobalBruhat.polarEvaluation F u = 0 := by
    dsimp only [u]
    rw [map_sub, polarEvaluation_leftTranslate, hf]
    simp
  refine ⟨u, hpol, ?_⟩
  let χ := compactIdeleClassCharacter F 1
  have hf₀ : (GlobalBruhat.algebraicEquiv F f).val 0 = 1 := congrArg Prod.fst hf
  have hmass : (ν.real univ : ℂ) ≠ 0 := by
    letI := normOneIdeleClass_compact F
    letI : IsFiniteMeasure ν := ⟨isCompact_univ.measure_lt_top⟩
    exact_mod_cast (measureReal_univ_pos (μ := ν)).ne'
  have hpole : meromorphicOrderAt (Z F ν 1 f) 0 = (-1 : ℤ) := by
    have hp := (globalZetaContinued_pole_order F ν f χ (compactIdeleClassCharacter_unitary F 1) 0).1
    have hc := compactIdeleClassCharacter_integral F ν (1 : PontryaginDual (K F))
    simp only [ite_true] at hc
    change (∫ k : K F, (χ k.val : ℂ) ∂ν) = _ at hc
    rw [hc, hf₀, mul_one, ite_eq_right hmass, neg_zero] at hp
    exact hp
  let e (z : ℂ) := Complex.exp z - 1
  have hE : AnalyticAt ℂ e 0 := analyticAt_id.cexp.sub analyticAt_const
  have horder : meromorphicOrderAt e 0 = 1 := by
    rw [hE.meromorphicOrderAt_eq, hE.analyticOrderAt_eq_one_of_zero_deriv_ne_zero
      (by simp [e]) (by simp [e])]
    rfl
  have hrelation : Z F ν 1 u =ᶠ[𝓝[≠] (0 : ℂ)] e * Z F ν 1 f := by
    filter_upwards [self_mem_nhdsWithin (s := {(0 : ℂ)}ᶜ),
      eventually_ne_nhdsWithin (s := {(0 : ℂ)}ᶜ) (zero_ne_one : (0 : ℂ) ≠ 1)] with z hz₀ hz₁
    have hc := globalZetaContinued_leftTranslate F η ν hν g f 1 z
      (fun _ ↦ ⟨hz₀, hz₁⟩)
    change Z F ν 1 (GlobalBruhat.leftTranslate F g f) z =
      (ideleNormTwist F χ z (ideleClassMap F g) : ℂ) * Z F ν 1 f z at hc
    rw [radial_trivialWeight F g 1 hg, Complex.ofReal_one, mul_one] at hc
    dsimp only [u]
    simp only [Z, ← globalContinuedMellinEval_apply, map_sub]
    simp only [globalContinuedMellinEval_apply]
    change Z F ν 1 (GlobalBruhat.leftTranslate F g f) z - Z F ν 1 f z = e z * Z F ν 1 f z
    change _ = (Complex.exp z - 1) * Z F ν 1 f z
    rw [hc, sub_one_mul]
  have hA : AnalyticAt ℂ (Z F ν 1 u) 0 :=
    globalZetaContinued_entire_of_polar_zero F ν u χ (compactIdeleClassCharacter_unitary F 1) 0
      (Or.inr ⟨congrArg Prod.fst hpol, congrArg Prod.snd hpol⟩) 0 (mem_univ _)
  apply hA.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mp
  have hfM := globalZetaContinued_meromorphic F ν f χ (compactIdeleClassCharacter_unitary F 1) 0
    0 (mem_univ _)
  rw [meromorphicOrderAt_congr hrelation, meromorphicOrderAt_mul hE.meromorphicAt hfM, horder, hpole]
  decide

include μ hν in
/-- The polar-free adelic tests have no common zero anywhere on the zero
line, for any norm-one character. -/
theorem exists_polarFree_globalZeta_ne_zero_zero_line
    (ω : PontryaginDual (K F)) (z : ℂ) (hz : z.re = 0) :
    ∃ f : GlobalBruhat F, GlobalBruhat.polarEvaluation F f = 0 ∧ Z F ν ω f z ≠ 0 := by
  by_cases hω : ω = 1
  · subst ω
    rcases eq_or_ne z 0 with rfl | hn
    · exact exists_polarFree_globalZeta_ne_zero_at_origin F η ν hν
    · exact exists_polarFree_globalZeta_ne_zero_zero_line_trivial F η ν μ hν z hz hn
  · exact exists_polarFree_globalZeta_ne_zero_zero_line_of_ne_one F η ν μ hν ω hω z hz

include μ hν in
/-- Every minimal adelic zeta reference, after pole cancellation, is nonzero
on the entire zero line. At the origin of the trivial component the assertion
comes from the actual residue. -/
theorem globalHeckeClearedZeta_ne_zero_zero_line_of_min
    (ω : PontryaginDual (K F)) (r : GlobalBruhat F)
    (hmin : ∀ (f : GlobalBruhat F) (z : ℂ),
      meromorphicOrderAt (Z F ν ω r) z ≤ meromorphicOrderAt (Z F ν ω f) z)
    (z : ℂ) (hz : z.re = 0) : globalHeckeClearedZeta F ν ω r z ≠ 0 := by
  by_cases hcase : ω ≠ 1 ∨ z ≠ 0
  · have hz₁ : z ≠ 1 := by
      intro h
      subst z
      simp at hz
    obtain ⟨f, hf⟩ := exists_globalZeta_order_eq_zero_zero_line F η ν μ hν ω z hz hcase
    have hp : globalHeckePoleFactor F ω z ≠ 0 := by
      by_cases hω : ω = 1
      · have hz₀ := hcase.resolve_left (not_not.mpr hω)
        simpa only [globalHeckePoleFactor, ite_eq_left hω] using
          mul_ne_zero hz₀ (sub_ne_zero.mpr hz₁.symm)
      · simp [globalHeckePoleFactor, hω]
    have ha := globalHeckePoleFactor_analytic F ω z
    have ho : meromorphicOrderAt (globalHeckePoleFactor F ω) z = 0 := by
      rw [ha.meromorphicOrderAt_eq, ha.analyticOrderAt_eq_zero.mpr hp]
      rfl
    have hle : meromorphicOrderAt (globalHeckeClearedZeta F ν ω r) z ≤ 0 := by
      rw [globalHeckeClearedZeta_meromorphicOrder, ho, zero_add]
      exact (hmin f z).trans_eq hf
    have hA := globalHeckeClearedZeta_analytic F ν ω r z
    exact hA.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mp
      (le_antisymm hle hA.meromorphicOrderAt_nonneg)
  · push Not at hcase
    obtain ⟨rfl, rfl⟩ := hcase
    exact (trivial_reference_regularized_nonzero F ν r hmin).1

omit [∀ v : Place F, MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : Place F, BorelSpace (v.adicCompletion F)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ] in
private theorem finiteReciprocalHeckeEulerProduct_zero_line
    (ω : PontryaginDual (K F)) (S : Finset (Place F)) {z : ℂ}
    (hz : (∏ v ∈ S, (heckeEulerFactor F
        (heckeEulerCoefficient F (normOneEulerCharacter F ω) (chosenFiniteUniformizer F)) v z)⁻¹) = 0) :
    z.re = 0 := by
  classical
  obtain ⟨v, _, hv⟩ := Finset.prod_eq_zero_iff.mp hz
  rw [heckeEulerFactor, inv_inv, sub_eq_zero] at hv
  unfold heckeEulerCoefficient at hv
  split_ifs at hv with hvu
  · have hq := NumberField.HeightOneSpectrum.one_lt_absNorm v
    have hq₁ : 1 < (v.asIdeal.absNorm : ℝ) := by exact_mod_cast hq
    have he := congrArg norm hv.symm
    simp only [norm_one, norm_mul, Circle.norm_coe, one_mul] at he
    rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans hq₁),
      Real.rpow_def_of_pos (zero_lt_one.trans hq₁), Real.exp_eq_one_iff] at he
    have hlog := Real.log_pos hq₁
    exact neg_eq_zero.mp (by simpa only [Complex.neg_re] using
      (mul_eq_zero.mp he).resolve_left hlog.ne')
  · simp at hv

include μ hν in
/-- The actual reciprocal Euler polynomial in (7.5.0.17) and the
pole-cleared minimal adelic reference have no common zero. -/
theorem globalHeckeClearedZeta_ne_zero_of_reciprocalEulerProduct_zero
    (ω : PontryaginDual (K F)) (r : GlobalBruhat F)
    (hmin : ∀ (f : GlobalBruhat F) (z : ℂ),
      meromorphicOrderAt (Z F ν ω r) z ≤ meromorphicOrderAt (Z F ν ω f) z)
    (S : Finset (Place F)) (z : ℂ)
    (hz : (∏ v ∈ S, (heckeEulerFactor F
        (heckeEulerCoefficient F (normOneEulerCharacter F ω) (chosenFiniteUniformizer F)) v z)⁻¹) = 0) :
    globalHeckeClearedZeta F ν ω r z ≠ 0 :=
  globalHeckeClearedZeta_ne_zero_zero_line_of_min F η ν μ hν ω r hmin z
    (finiteReciprocalHeckeEulerProduct_zero_line F ω S hz)

omit [∀ v : Place F, BorelSpace (v.adicCompletion F)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ] in
/-- The radial Schwartz profile of a polar-free adelic theta is the
logarithmic restriction of its homogeneous theta component. -/
def polarFreeThetaRadialSchwartz (ω : PontryaginDual (K F)) (f : GlobalBruhat F)
    (hf : GlobalBruhat.polarEvaluation F f = 0) : 𝓢(ℝ, ℂ) :=
  adelicHomogeneousTheta_radialSchwartz F ν ω f
    (Or.inr ⟨congrArg Prod.fst hf, congrArg Prod.snd hf⟩)

omit [∀ v : Place F, MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : Place F, BorelSpace (v.adicCompletion F)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ] in
/-- The real Fourier transform of the radial theta profile is its
continued zeta transform on the zero line, with Mathlib's Fourier normalization. -/
theorem polarFreeThetaRadialSchwartz_fourier (ω : PontryaginDual (K F))
    (f : GlobalBruhat F) (hf : GlobalBruhat.polarEvaluation F f = 0) (ξ : ℝ) :
    𝓕 (polarFreeThetaRadialSchwartz F ν ω f hf : ℝ → ℂ) ξ =
      Z F ν ω f ((↑(-2 * Real.pi * ξ) : ℂ) * Complex.I) := by
  let χ := compactIdeleClassCharacter F ω
  let z := (↑(-2 * Real.pi * ξ) : ℂ) * Complex.I
  have hp : globalZetaPolarVanishes F f χ :=
    (globalZetaPolarVanishes_compact_iff F f ω).mpr
      (Or.inr ⟨congrArg Prod.fst hf, congrArg Prod.snd hf⟩)
  have hχ := compactIdeleClassCharacter_unitary F ω
  have h := globalRadialZeta_eq_continued F ν f χ hχ (κ := 0) Complex.zero_re
    (fun t ↦ by
      change (compactIdeleClassCharacter F ω _ : ℂ) = Complex.exp ((0 : ℂ) * (t : ℂ))
      rw [compactIdeleClassCharacter_apply_ray, zero_mul, Complex.exp_zero])
    (ideleClassExpSection F) (ideleClassNorm_expSection F) z (Or.inr hp)
  change 𝓕 (polarFreeThetaRadialSchwartz F ν ω f hf : ℝ → ℂ) ξ = Z F ν ω f z
  change _ = Z F ν ω f z at h
  rw [Real.fourier_real_eq_integral_exp_smul, ← h]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro t
  let q := ideleClassExpSection F (Multiplicative.ofAdd t)
  unfold globalRadialZetaIntegrand
  rw [normOnePontryaginCharacter_compactIdeleClassCharacter]
  change Complex.exp (↑(-2 * Real.pi * t * ξ) * Complex.I) *
      adelicHomogeneousTheta F ν ω (GlobalBruhat.algebraicEquiv F f).val q =
    ((χ q : ℂ) * ideleNormPower F z q) *
      adelicHomogeneousTheta F ν ω (GlobalBruhat.algebraicEquiv F f).val q
  have hc : (χ q : ℂ) = 1 := compactIdeleClassCharacter_apply_ray F ω t
  rw [hc, one_mul, ideleNormPower, ideleClassNorm_expSection, Real.log_exp]
  congr 2
  change (↑(-2 * Real.pi * t * ξ) : ℂ) * Complex.I = z * (t : ℂ)
  dsimp only [z]
  push_cast
  ring

include μ hν in
/-- For every angular character, the actual radial Schwartz theta profiles
have no common real Fourier zero. -/
theorem exists_polarFreeThetaRadialSchwartz_fourier_ne_zero
    (ω : PontryaginDual (K F)) (ξ : ℝ) :
    ∃ (f : GlobalBruhat F) (hf : GlobalBruhat.polarEvaluation F f = 0),
      𝓕 (polarFreeThetaRadialSchwartz F ν ω f hf : ℝ → ℂ) ξ ≠ 0 := by
  obtain ⟨f, hf, hz⟩ := exists_polarFree_globalZeta_ne_zero_zero_line F η ν μ hν ω
    ((↑(-2 * Real.pi * ξ) : ℂ) * Complex.I) (by simp [Complex.mul_re])
  exact ⟨f, hf, (polarFreeThetaRadialSchwartz_fourier F ν ω f hf ξ).symm ▸ hz⟩

include μ hν in
/-- Every band-limited Schwartz profile is generated by finitely many
radial convolutions of actual polar-free theta profiles in its isotype. -/
theorem exists_polarFreeThetaRadialSchwartz_finite_convolution
    (ω : PontryaginDual (K F)) (b : 𝓢(ℝ, ℂ))
    (hb : HasCompactSupport (𝓕 b : 𝓢(ℝ, ℂ))) :
    ∃ (J : Finset (GlobalBruhat.polarEvaluation F).ker)
      (c : (GlobalBruhat.polarEvaluation F).ker → 𝓢(ℝ, ℂ)),
      (∀ i, HasCompactSupport (𝓕 (c i) : 𝓢(ℝ, ℂ))) ∧
      (∑ i ∈ J, SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ)
        (polarFreeThetaRadialSchwartz F ν ω i.val i.property) (c i)) = b := by
  apply compactSpectrum_finite_convolution _ _ b hb
  intro ξ
  obtain ⟨f, hf, hne⟩ := exists_polarFreeThetaRadialSchwartz_fourier_ne_zero F η ν μ hν ω ξ
  exact ⟨⟨f, hf⟩, hne⟩

end
end Masullo
