import GlobalConverseStripBounds
import SLocalMellinContour

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical NumberField

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

private abbrev Place := HeightOneSpectrum (𝓞 F)
private abbrev K := normOneIdeleClass F

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

include μ hν in
/-- The vertical line of real part minus one is reflected to real part two.
The finite continuation has a positive uniform lower bound there at large
absolute height. -/
theorem globalFiniteHecke_norm_ge_left_edge (ω : PontryaginDual (K F))
    {f : ℂ → ℂ} (hf : MeromorphicOn f univ)
    (he : EqOn f (globalFiniteHeckeEuler F ω) {z | 1 < z.re})
    (hfa : ∀ z, z.re = -1 → AnalyticAt ℂ f z) :
    ∃ c T : ℝ, 0 < c ∧ ∀ z : ℂ, z.re = -1 → T ≤ |z.im| → c ≤ ‖f z‖ := by
  obtain ⟨S, hS, hω, hω', hD⟩ := exists_globalHeckeTateStage F ω
  let σ := sLocalNormOneCharacterOfGlobal F ω S hS hω
  let τ := sLocalNormOneCharacterOfGlobal F ω⁻¹ S hS hω'
  let D := completedTateReciprocalArch F S hS ω hω
  let E := completedTateReciprocalArch F S hS ω⁻¹ hω'
  have hi : τ = σ⁻¹ := by
    ext k
    obtain ⟨g, rfl⟩ := globalNormOneToSLocal_surjective F S hS k
    dsimp only [τ]
    rw [sLocalNormOneCharacterOfGlobal_match]
    change (↑((ω g)⁻¹) : ℂ) =
      ↑((sLocalNormOneCharacterOfGlobal F ω S hS hω (globalNormOneToSLocal F S hS g))⁻¹)
    rw [sLocalNormOneCharacterOfGlobal_match]
  obtain ⟨L, L', ε, hLm, hL'm, hLe, hL'e, hεa, _, ⟨e, B, _, heT, hε⟩, _, hFE⟩ :=
    exists_globalCompletedHecke_tateReflection F S hS ω hω hω' η ν μ hν hD
  obtain ⟨A, hA, hAb⟩ := sLocalTateEpsilonProduct_norm_le_on_strip F S
    (fun v : S ↦ μ v.val) σ e heT (-1) (-1)
  obtain ⟨G, T, hG, hGb⟩ := sLocalTateArchimedeanRatio_sharp_on_strip F S σ (-1) (-1)
  obtain ⟨T', hDn⟩ := sLocalArchDenominator_nonzero_at_height F S σ
  obtain ⟨d, hd, hright⟩ := globalFiniteHeckeEuler_norm_ge_two F
  let C := max 1 G * max 1 (‖B‖ * A)
  have hC : 0 < C := mul_pos
    (zero_lt_one.trans_le (le_max_left _ _)) (zero_lt_one.trans_le (le_max_left _ _))
  refine ⟨d / C, max T T', div_pos hd hC, fun z hz ht ↦ ?_⟩
  have hzR : 1 < (1 - z).re := by norm_num [Complex.sub_re, hz]
  have hDnz : D z ≠ 0 := hDn z ((le_max_right _ _).trans ht)
  have hratio : ‖E (1 - z) / D z‖ ≤ max 1 G := by
    have h := hGb z ⟨hz.ge, hz.le⟩ ((le_max_left _ _).trans ht)
    change ‖archimedeanNumberFieldZetaDenominator F (sLocalRealArchParameters F S σ⁻¹)
      (sLocalComplexArchParameters F S σ⁻¹) (1 - z) / D z‖ ≤ _ at h
    rw [← hi] at h
    refine h.trans ((mul_le_of_le_one_right hG ?_).trans (le_max_right _ _))
    apply Real.rpow_le_one_of_one_le_of_nonpos (by linarith [abs_nonneg z.im])
    rw [hz]
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (by norm_num)
  have hεb : ‖ε z‖ ≤ max 1 (‖B‖ * A) := by
    rw [hε, norm_mul]
    exact (mul_le_mul_of_nonneg_left (hAb z ⟨hz.ge, hz.le⟩) (norm_nonneg _)).trans (le_max_right _ _)
  let w := 1 - z
  have hwr : w.re = 2 := by norm_num [w, Complex.sub_re, hz]
  obtain ⟨f', hf', he', hfa', _, _⟩ :=
    exists_globalFiniteHecke_polynomial_strips F ω⁻¹ ν η μ hν
  have hFEg : (fun v ↦ D v * f' (1 - v)) =ᶠ[𝓝[≠] z]
      fun v ↦ f v * E (1 - v) * ε v := by
    have h₁ := globalFiniteHeckeContinuation_germ F ω S hS hω hLm hf hLe he z
    have h₂ := globalFiniteHeckeContinuation_germ F ω⁻¹ S hS hω' hL'm hf' hL'e he' w
    filter_upwards [h₁, (reflect_punctured z).eventually h₂, hFE z] with v hv hv' hFEv
    change f v = D v * L v at hv
    change f' (1 - v) = E (1 - v) * L' (1 - v) at hv'
    change L' (1 - v) = L v * ε v at hFEv
    rw [hv', hv, hFEv]
    ring
  have hReflect : ContinuousAt (fun v : ℂ ↦ 1 - v) z :=
    (continuous_const.sub continuous_id).continuousAt
  have hfa'w : AnalyticAt ℂ f' w :=
    hfa' w (by intro hw; norm_num [hw] at hwr) (by intro hw; norm_num [hw] at hwr)
  have hGcont : ContinuousAt (fun v ↦ D v * f' (1 - v)) z :=
    (archimedeanNumberFieldZetaDenominator_analytic _ _ _ z).continuousAt.mul
      (hfa'w.continuousAt.comp (f := fun v : ℂ ↦ 1 - v) hReflect)
  have hEw : ContinuousAt E w :=
    (archimedeanNumberFieldZetaDenominator_analytic _ _ _ w).continuousAt
  have hFcont : ContinuousAt (fun v ↦ f v * E (1 - v) * ε v) z :=
    ((hfa z hz).continuousAt.mul (hEw.comp (f := fun v : ℂ ↦ 1 - v) hReflect)).mul
      ((hεa z (mem_univ _)).continuousAt)
  have heq := ((hGcont.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE hFcont).mp hFEg).eq_of_nhds
  change D z * f' w = f z * E w * ε z at heq
  rw [he' hzR] at heq
  have hsolve : globalFiniteHeckeEuler F ω⁻¹ w = f z * (E w / D z) * ε z := by
    apply mul_left_cancel₀ hDnz
    rw [heq]
    field_simp
  have hr : d ≤ ‖globalFiniteHeckeEuler F ω⁻¹ w‖ := by
    simpa only [← hwr] using hright ω⁻¹ w.im
  apply (div_le_iff₀ hC).mpr
  rw [hsolve, norm_mul, norm_mul] at hr
  exact hr.trans (by
    dsimp only [C]
    rw [← mul_assoc]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hratio (norm_nonneg _)) hεb
      (norm_nonneg _) (by positivity))


variable (χ : PontryaginDual (IdeleClass F)) (S : Finset (Place F))

omit [∀ v : Place F, MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : Place F, BorelSpace (v.adicCompletion F)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ] in
private theorem omissionMultiplier_norm_ge_left_edge :
    ∃ d > (0 : ℝ), ∀ z : ℂ, z.re = -1 → d ≤ ‖finiteHeckeOmissionMultiplier F χ S z‖ := by
  let d (v : Place F) : ℝ :=
    if unramifiedFiniteCharacter F χ v then (v.asIdeal.absNorm : ℝ) - 1 else 1
  have hd (v : Place F) : 0 < d v := by
    dsimp only [d]
    split_ifs
    · exact sub_pos.mpr (by exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v)
    · exact zero_lt_one
  refine ⟨∏ v ∈ S, d v, Finset.prod_pos fun v _ ↦ hd v, fun z hz ↦ ?_⟩
  rw [finiteHeckeOmissionMultiplier, norm_prod]
  apply Finset.prod_le_prod (fun v _ ↦ (hd v).le)
  intro v _
  change d v ≤ ‖1 - heckeEulerCoefficient F χ (chosenFiniteUniformizer F) v *
    (v.asIdeal.absNorm : ℂ) ^ (-z)‖
  unfold heckeEulerCoefficient
  dsimp [d]
  split_ifs with hu
  · have hq : (0 : ℝ) < v.asIdeal.absNorm := by
      exact_mod_cast zero_lt_one.trans (NumberField.HeightOneSpectrum.one_lt_absNorm v)
    have hnorm : ‖(χ (QuotientGroup.mk (singleFiniteIdele F v (chosenFiniteUniformizer F v))) : ℂ) *
        (v.asIdeal.absNorm : ℂ) ^ (-z)‖ = (v.asIdeal.absNorm : ℝ) := by
      rw [norm_mul, Circle.norm_coe, one_mul, ← Complex.ofReal_natCast,
        Complex.norm_cpow_eq_rpow_re_of_pos hq, Complex.neg_re, hz, neg_neg, Real.rpow_one]
    have h := norm_sub_norm_le
      ((χ (QuotientGroup.mk (singleFiniteIdele F v (chosenFiniteUniformizer F v))) : ℂ) *
        (v.asIdeal.absNorm : ℂ) ^ (-z)) (1 : ℂ)
    rw [hnorm, norm_one, norm_sub_rev] at h
    exact h
  · simp

include μ hν in
/-- Removing any finite set of Euler factors preserves the positive lower
bound at large height on the line of real part minus one. The assertion
allows every unitary norm twist. -/
theorem manuscriptFiniteHeckeOutside_norm_ge_left_edge
    {L : ℂ → ℂ} (hL : MeromorphicOn L univ)
    (heL : EqOn L (manuscriptFiniteHeckeEulerOutside F χ S) {z | 1 < z.re})
    (hLa : ∃ U : ℝ, ∀ z : ℂ, U ≤ |z.im| → AnalyticAt ℂ L z) :
    ∃ c T : ℝ, 0 < c ∧ ∀ z : ℂ, z.re = -1 → T ≤ |z.im| → c ≤ ‖L z‖ := by
  let ω := heckeNormOneRestriction F χ
  obtain ⟨t, ht, _⟩ := existsUnique_heckeHeight F χ
  obtain ⟨f, hf, hef, hfa, _, _⟩ := exists_globalFiniteHecke_polynomial_strips F ω ν η μ hν
  have han (z : ℂ) (hz : z.re = -1) : AnalyticAt ℂ f z :=
    hfa z (by intro h; norm_num [h] at hz) (by intro h; norm_num [h] at hz)
  obtain ⟨c, T, hc, hleft⟩ := globalFiniteHecke_norm_ge_left_edge F ν η μ hν ω hf hef han
  obtain ⟨d, hd, hD⟩ := omissionMultiplier_norm_ge_left_edge F χ S
  obtain ⟨U, hU⟩ := hLa
  let q (z : ℂ) := z - (t : ℂ) * Complex.I
  let P := finiteHeckeOmissionMultiplier F χ S
  let g (z : ℂ) := P z * f (q z)
  have hqa (z : ℂ) : AnalyticAt ℂ q z := analyticAt_id.sub analyticAt_const
  have hre (z : ℂ) : (q z).re = z.re := by simp [q, Complex.sub_re, Complex.mul_re]
  have him (z : ℂ) : (q z).im = z.im - t := by simp [q, Complex.sub_im, Complex.mul_im]
  have hgm : MeromorphicOn g univ := fun z _ ↦
    (finiteHeckeOmissionMultiplier_analytic F χ S z).meromorphicAt.mul
      ((hf (q z) (mem_univ _)).comp_analyticAt (hqa z))
  have heg : EqOn g (manuscriptFiniteHeckeEulerOutside F χ S) {z | 1 < z.re} := by
    intro z hz
    change P z * f (q z) = _
    rw [hef (show 1 < (q z).re by rwa [hre]), ← manuscriptFiniteHeckeEuler_shift F χ ht,
      manuscriptFiniteHeckeEulerOutside_eq F χ S hz]
  refine ⟨d * c, max U (T + |t|), mul_pos hd hc, fun z hz hT ↦ ?_⟩
  have hga : AnalyticAt ℂ g z := (finiteHeckeOmissionMultiplier_analytic F χ S z).mul
    ((han (q z) ((hre z).trans hz)).comp (f := q) (hqa z))
  have hEq := globalHeckeContinuation_unique_germ hL hgm heL heg z
  have hpoint := (((hU z ((le_max_left _ _).trans hT)).continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
    hga.continuousAt).mp hEq).eq_of_nhds
  have hlarge : T ≤ |(q z).im| := by
    have hT' := (le_max_right U (T + |t|)).trans hT
    have htriangle := abs_add_le (z.im - t) t
    rw [sub_add_cancel] at htriangle
    rw [him]
    linarith
  rw [hpoint]
  change d * c ≤ ‖P z * f (q z)‖
  rw [norm_mul]
  exact mul_le_mul (hD z hz) (hleft (q z) ((hre z).trans hz) hlarge) hc.le (norm_nonneg _)

include μ hν in
/-- The outside Euler product gives all four boundary estimates for
holomorphic division on the closed strip from real part minus one to two.
Only rapid decay of the product at large height is needed. -/
theorem exists_globalConverse_Outside_strip_transfer_both_edges :
    let strip := Complex.re ⁻¹' Icc (-1 : ℝ) 2
    ∃ L : ℂ → ℂ, MeromorphicOn L univ ∧
      EqOn L (manuscriptFiniteHeckeEulerOutside F χ S) {z | 1 < z.re} ∧
      (∃ V : ℝ, ∀ z : ℂ, V ≤ |z.im| → AnalyticAt ℂ L z) ∧
      ∀ {H : ℂ → ℂ}, DifferentiableOn ℂ H strip →
        ∀ Y : ℝ,
        (∀ m : ℕ, BddAbove
          ((fun z : ℂ ↦ ‖z ^ m * (L z * H z)‖) '' {z ∈ strip | Y ≤ |z.im|})) →
        ∀ n : ℕ, BddAbove ((fun z : ℂ ↦ ‖z ^ n * H z‖) '' strip) := by
  intro strip
  obtain ⟨L, A, U, _, hMer, he, ⟨V, hVa, _⟩, hLower, _⟩ :=
    exists_manuscriptFiniteHeckeOutside_horizontal_lower_bounds F χ S ν η μ hν
  obtain ⟨c, T, hc, hLeft⟩ :=
    manuscriptFiniteHeckeOutside_norm_ge_left_edge F ν η μ hν χ S hMer he ⟨V, hVa⟩
  obtain ⟨M, _, d, hd, _, heM, hcenter, _⟩ :=
    exists_manuscriptFiniteHeckeOutside_polynomial_strips F χ S ν η μ hν
  have hRight (z : ℂ) (hz : z.re = 2) : d ≤ ‖L z‖ := by
    have h := show 1 < z.re by rw [hz]; norm_num
    rw [he h, ← heM h]
    simpa only [← hz] using hcenter z.im
  refine ⟨L, hMer, he, ⟨V, hVa⟩, ?_⟩
  intro H hH Y hprod
  have hlt : (-1 : ℝ) < 2 := by norm_num
  apply rapidStrip_of_sparse_horizontal_lower (A := A) (U := U) hlt hH hLower hprod
  have hl := rapidVerticalBoundary_of_product (T := T) (left_mem_Icc.mpr hlt.le)
    hc hH.continuousOn hLeft hprod
  have hr := rapidVerticalBoundary_of_product (T := 0) (right_mem_Icc.mpr hlt.le)
    hd hH.continuousOn (fun z hz _ ↦ hRight z hz) hprod
  intro n
  obtain ⟨B, hB⟩ := hl n
  obtain ⟨C, hC⟩ := hr n
  refine ⟨max B C, fun z hz ↦ ?_⟩
  rcases hz with h | h
  · exact (hB z h).trans (le_max_left _ _)
  · exact (hC z h).trans (le_max_right _ _)

section StageProduct

variable (ω : PontryaginDual (K F)) (hS : Surjective (sIdeleClassInclusion F S))
variable (hω : globalNormOneCharacter F ω ∈
  (sUnramified F S : Set (QuasiCharacter (IdeleClass F))))

private abbrev localPhase := sLocalNormOneCharacterOfGlobal F ω S hS hω

private abbrev localContinued (f : sLocalBruhatImage F S) :=
  sLocalProductZetaContinued F S (fun v : S ↦ μ v.val) (localPhase F S ω hS hω)
    (sLocalRealArchParameters F S (localPhase F S ω hS hω))
    (sLocalComplexArchParameters F S (localPhase F S ω hS hω)) f

private abbrev globalContinued (f : sLocalBruhatImage F S) :=
  globalZetaContinued F ν f.val (compactIdeleClassCharacter F ω) 0

omit [∀ v : Place F, MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : Place F, BorelSpace (v.adicCompletion F)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ] in
/-- The stage denominator is the reciprocal archimedean product times the
finite multiplier that removes the selected factors from the global product. -/
theorem stageEulerDenominator_eq_arch_mul_omission (z : ℂ) :
    sLocalEulerDenominator F S (localPhase F S ω hS hω) z =
      completedTateReciprocalArch F S hS ω hω z *
        finiteHeckeOmissionMultiplier F (normOneEulerCharacter F ω) S z := by
  unfold sLocalEulerDenominator
  rw [sLocalFiniteZetaDenominator_eq_heckeProduct F ω S hS hω z]
  unfold finiteHeckeOmissionMultiplier
  rw [← Finset.prod_inv_distrib]
  simp only [heckeEulerFactor, inv_inv]

include μ hν in
/-- At a fixed stage the global zeta transform of every test is locally
the stage transform times the exterior finite Euler continuation and a
single nonzero Haar scalar. The result holds at punctured meromorphic germs. -/
theorem globalContinuedMellin_eq_outside_mul_stage
    {L : ℂ → ℂ} (hL : MeromorphicOn L univ)
    (heL : EqOn L (manuscriptFiniteHeckeEulerOutside F (normOneEulerCharacter F ω) S)
      {z | 1 < z.re}) :
    ∃ A : ℂ, A ≠ 0 ∧ ∀ (f : sLocalBruhatImage F S) c,
      globalContinued F ν S ω f =ᶠ[𝓝[≠] c]
        fun z ↦ A * L z * localContinued F μ S ω hS hω f z := by
  let σ := localPhase F S ω hS hω
  let D := sLocalEulerDenominator F S σ
  let E := completedTateReciprocalArch F S hS ω hω
  let G := globalContinued F ν S ω
  let Z := localContinued F μ S ω hS hω
  let P := finiteHeckeOmissionMultiplier F (normOneEulerCharacter F ω) S
  obtain ⟨r, C, hC, hr, hfinite, _⟩ :=
    exists_globalMellin_order_reference F η ω S hS hω μ ν hν
  obtain ⟨B, hB, hBr⟩ :=
    globalZetaContinued_reference_eq_completedEuler F ω S hS hω η ν μ hν r C hr (hfinite 2)
  have hD : ∀ z, D z = E z * P z := stageEulerDenominator_eq_arch_mul_omission F S ω hS hω
  let A := B / C
  refine ⟨A, div_ne_zero hB hC, fun f ↦ ?_⟩
  have hχ := compactIdeleClassCharacter_unitary F ω
  apply boundedPoleMellinSpace_unique_germs
    (D := {z : ℂ | 1 < z.re}) (isOpen_lt continuous_const Complex.continuous_re)
    ⟨2, by change (1 : ℝ) < 2; norm_num⟩
    (fun z ↦ globalZetaContinued_meromorphic F ν f.val _ hχ 0 z (mem_univ _))
    (fun z ↦ ((MeromorphicAt.const A z).mul (hL z (mem_univ _))).mul
      (sLocalProductZetaContinued_meromorphic F S (fun v : S ↦ μ v.val) σ _ _ f z))
  intro z hz
  have hzpos : 0 < z.re := zero_lt_one.trans hz
  have hd : D z ≠ 0 := sLocalEulerDenominator_ne_zero_of_pos F S σ hzpos
  have he : E z ≠ 0 := left_ne_zero_of_mul (hD z ▸ hd)
  have hEq := sLocalEulerNormalizedMellin_eq_germ F S (fun v : S ↦ μ v.val) σ r z
  change sLocalEulerNormalizedMellin F S (fun v : S ↦ μ v.val) σ r = _ at hr
  rw [hr] at hEq
  change (fun _ : ℂ ↦ C) =ᶠ[𝓝[≠] z] fun w ↦ D w * Z r w at hEq
  have hn : D z * Z r z = C := by
    have hDc : ContinuousAt D z := (sLocalEulerDenominator_analytic F S σ z).continuousAt
    have hZc : ContinuousAt (Z r) z :=
      sLocalProductZetaContinued_continuousAt_pos F μ S σ r z hzpos
    have hCc : ContinuousAt (fun _ : ℂ ↦ C) z := continuousAt_const
    exact ((hCc.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
      (hDc.mul hZc)).mp hEq).eq_of_nhds.symm
  have hZnz : Z r z ≠ 0 := by
    intro h
    rw [h, mul_zero] at hn
    exact hC hn.symm
  have hprod : D z * globalCompletedHeckeEuler F ω S hS hω z = L z := by
    rw [hD, heL hz, manuscriptFiniteHeckeEulerOutside_eq F (normOneEulerCharacter F ω) S hz]
    change (E z * P z) * ((E z)⁻¹ * globalFiniteHeckeEuler F ω z) =
      P z * globalFiniteHeckeEuler F ω z
    rw [mul_mul_mul_comm, mul_inv_cancel₀ he, one_mul]
  have hGr : G r z = A * L z * Z r z := by
    have hBrz : G r z = B * globalCompletedHeckeEuler F ω S hS hω z := hBr hz
    apply mul_left_cancel₀ hd
    rw [hBrz]
    calc
      D z * (B * globalCompletedHeckeEuler F ω S hS hω z) = B * L z := by
        rw [mul_left_comm, hprod]
      _ = D z * (A * L z * Z r z) := by
        rw [show D z * (A * L z * Z r z) = A * L z * (D z * Z r z) by ring, hn]
        dsimp [A]
        field_simp
  have hid (a : sLocalBruhatImage F S) :
      G a z = idelicZetaIntegral F η (GlobalBruhat.algebraicEquiv F a.val).val
        (compactIdeleClassCharacter F ω) z :=
    globalZetaContinued_eq_idelic F η ν hν a.val _ hχ (κ := 0) Complex.zero_re
      (fun t ↦ by simp) z hz
  have hcross := globalIdelicMellin_cross_local F η ω S hS hω μ f r z hz
  rw [← hid f, ← hid r] at hcross
  change G f z * Z r z = G r z * Z f z at hcross
  apply mul_right_cancel₀ hZnz
  change G f z * Z r z = (A * L z * Z f z) * Z r z
  exact hcross.trans (by rw [hGr]; ring)

end StageProduct

end

end Masullo
