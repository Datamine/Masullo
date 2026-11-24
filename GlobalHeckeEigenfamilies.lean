import GlobalHeckeEulerComparison
import AdelicMellinCompact
import AdelicBruhatStructure
import AdelicThetaTranslations
import VectorHolomorphyDerivatives

open Filter Function IsDedekindDomain MeasureTheory Metric NumberField Set Topology
open scoped Classical NNReal NumberField SchwartzMap

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]
private abbrev K := normOneIdeleClass F
private abbrev E := GlobalBruhat F

local instance : MeasurableSpace (K F) := borel _
local instance : BorelSpace (K F) := ⟨rfl⟩
local instance : MeasurableSpace (Idele F) := borel _

variable (ν : Measure (K F)) [ν.IsHaarMeasure] (ω : PontryaginDual (K F))

private abbrev Z (f : E F) (z : ℂ) := globalContinuedMellinEval F ν ω z f

private theorem eventually_ne_at (c p : ℂ) : ∀ᶠ z in 𝓝[≠] c, z ≠ p := by
  by_cases h : c = p
  · subst p
    exact self_mem_nhdsWithin
  · exact eventually_ne_nhdsWithin h

private theorem meromorphic_eventually_regular {L : ℂ → ℂ} (c : ℂ)
    (hL : MeromorphicAt L c) (hf : meromorphicOrderAt L c ≠ ⊤) :
    ∀ᶠ w in 𝓝[≠] c, AnalyticAt ℂ L w ∧ L w ≠ 0 ∧ w ≠ 0 ∧ w ≠ 1 :=
  hL.eventually_analyticAt.and <|
    (hL.eventually_eq_zero_or_eventually_ne_zero.resolve_left
      (fun h => hf (meromorphicOrderAt_eq_top_iff.mpr h))).and
      ((eventually_ne_at c 0).and (eventually_ne_at c 1))

private theorem eq_at_of_puncturedEq {f g : ℂ → ℂ} {c : ℂ}
    (hf : ContinuousAt f c) (hg : ContinuousAt g c) (he : f =ᶠ[𝓝[≠] c] g) :
    f c = g c :=
  ((hf.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE hg).mp he).eq_of_nhds

private theorem quotient_at_regular {L U : ℂ → ℂ} {z : ℂ} (f : E F)
    (hL : AnalyticAt ℂ L z) (hU : AnalyticAt ℂ U z)
    (hreg : (ω, z) ∈ globalMellinRegularSet F)
    (he : (fun w => Z F ν ω f w) =ᶠ[𝓝[≠] z] L * U) :
    Z F ν ω f z = L z * U z :=
  eq_at_of_puncturedEq (globalContinuedMellinEval_regular_analytic F ν f (ω, z) hreg).continuousAt
    (hL.mul hU).continuousAt he

section ScalarAnalytic

variable (L : ℂ → ℂ) (hL : MeromorphicOn L univ)
variable (hfinite : ∀ z, meromorphicOrderAt L z ≠ ⊤)
variable (U : E F → ℂ → ℂ) (hU : ∀ f, AnalyticOnNhd ℂ (U f) univ)
variable (hfactor : ∀ f c, (fun z => Z F ν ω f z) =ᶠ[𝓝[≠] c] L * U f)

include hL hfinite hU hfactor in
private theorem normalized_seminorm_bound (c : ℂ) :
    ∃ p : Seminorm ℂ (E F), Continuous p ∧ ∀ f, ‖U f c‖ ≤ p f := by
  let Rgood : Set ℂ := {w | AnalyticAt ℂ L w ∧ L w ≠ 0 ∧ w ≠ 0 ∧ w ≠ 1}
  have hgood : Rgood ∈ 𝓝[≠] c := meromorphic_eventually_regular c (hL c trivial) (hfinite c)
  obtain ⟨V, hV, hsub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hgood
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hV
  let R := r / 2
  have hR : 0 < R := half_pos hr
  have hSphere : sphere c R ⊆ Rgood := by
    intro w hw
    have hd := mem_sphere.mp hw
    refine hsub ⟨hball (mem_ball.mpr (hd.trans_lt (half_lt_self hr))), ?_⟩
    rw [mem_compl_iff, mem_singleton_iff]
    rintro rfl
    rw [dist_self] at hd
    exact hR.ne' hd.symm
  let T := (fun w : ℂ => (ω, w)) '' sphere c R
  have hT : IsCompact T := (isCompact_sphere c R).image (continuous_const.prodMk continuous_id)
  have hreg : T ⊆ globalMellinRegularSet F := by
    rintro _ ⟨w, hw, rfl⟩ _
    exact (hSphere hw).2.2
  obtain ⟨p, hp, hz⟩ := globalContinuedMellin_compact_seminorm F ν hT hreg
  have hinv : ContinuousOn (fun w => (L w)⁻¹) (sphere c R) :=
    fun w hw => (((hSphere hw).1.inv (hSphere hw).2.1).continuousAt).continuousWithinAt
  obtain ⟨M, hM⟩ := (isCompact_sphere c R).exists_bound_of_continuousOn hinv
  let C : ℝ≥0 := ⟨max 0 M, le_max_left _ _⟩
  refine ⟨C • p, by exact continuous_const.mul hp, fun f => ?_⟩
  have hd : DiffContOnCl ℂ (U f) (ball c R) :=
    (differentiableOn_univ.mp (hU f).differentiableOn).diffContOnCl
  have hb (w : ℂ) (hw : w ∈ sphere c R) : ‖U f w‖ ≤ C * p f := by
    have hTmem : (ω, w) ∈ T := ⟨w, hw, rfl⟩
    have he := quotient_at_regular F ν ω f (hSphere hw).1 (hU f w trivial)
      (hreg hTmem) (hfactor f w)
    have hq : U f w = (L w)⁻¹ * Z F ν ω f w := by
      rw [he, ← mul_assoc, inv_mul_cancel₀ (hSphere hw).2.1, one_mul]
    rw [hq, norm_mul]
    exact mul_le_mul ((hM w hw).trans (le_max_right _ _)) (hz f (ω,w) hTmem)
      (norm_nonneg _) C.coe_nonneg
  have he := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le 0 hR hd hb
  simpa only [iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one, one_mul, pow_zero,
    div_one, smul_apply, NNReal.smul_def, smul_eq_mul] using he

include hL hfinite hU hfactor in
private def normalized_global_linear (c : ℂ) : E F →ₗ[ℂ] ℂ where
  toFun f := U f c
  map_add' f g := by
    apply eq_at_of_puncturedEq (hU (f + g) c trivial).continuousAt
      ((hU f c trivial).add (hU g c trivial)).continuousAt
    filter_upwards [hfactor (f + g) c, hfactor f c, hfactor g c,
      meromorphic_eventually_regular c (hL c trivial) (hfinite c)] with w h₁ h₂ h₃ hw
    change Z F ν ω (f + g) w = L w * U (f + g) w at h₁
    change Z F ν ω f w = L w * U f w at h₂
    change Z F ν ω g w = L w * U g w at h₃
    change U (f + g) w = U f w + U g w
    apply mul_left_cancel₀ hw.2.1
    rw [← h₁, mul_add, ← h₂, ← h₃]
    exact map_add (globalContinuedMellinEval F ν ω w) f g
  map_smul' a f := by
    apply eq_at_of_puncturedEq (hU (a • f) c trivial).continuousAt
      (analyticAt_const.mul (hU f c trivial)).continuousAt
    filter_upwards [hfactor (a • f) c, hfactor f c,
      meromorphic_eventually_regular c (hL c trivial) (hfinite c)] with w h₁ h₂ hw
    change Z F ν ω (a • f) w = L w * U (a • f) w at h₁
    change Z F ν ω f w = L w * U f w at h₂
    change U (a • f) w = a * U f w
    apply mul_left_cancel₀ hw.2.1
    rw [← h₁, mul_left_comm, ← h₂]
    exact map_smul (globalContinuedMellinEval F ν ω w) a f

include hL hfinite hU hfactor in
private def normalized_global_dual (c : ℂ) : StrongDual ℂ (E F) := by
  let A := normalized_global_linear F ν ω L hL hfinite U hU hfactor c
  refine ⟨A, ?_⟩
  obtain ⟨p, hp, hbound⟩ := normalized_seminorm_bound F ν ω L hL hfinite U hU hfactor c
  apply WithSeminorms.continuous_of_continuous_comp (norm_withSeminorms ℂ ℂ) A
  intro i
  apply Seminorm.continuous_of_le hp
  exact hbound

include hL hfinite hU hfactor in
private theorem normalized_global_dual_holomorphic :
    Differentiable ℂ (normalized_global_dual F ν ω L hL hfinite U hU hfactor) := by
  let D := StrongDual ℂ (E F)
  letI : UniformSpace (E F) := IsTopologicalAddGroup.rightUniformSpace _
  letI : IsUniformAddGroup (E F) := isUniformAddGroup_of_addCommGroup
  letI : CompleteSpace (E F) := globalBruhat_complete F
  letI : BarrelledSpace ℂ (E F) := globalBruhat_barrelled F
  letI : CompleteSpace D := globalBruhat_strongDual_complete F
  letI : PolynormableSpace ℂ D := strongDual_withBoundedSeminorms.toPolynormableSpace
  obtain ⟨e, he⟩ := strongBidual_equiv_of_nuclear (globalBruhat_nuclear F)
  apply differentiableOn_univ.mp
  apply differentiableOn_of_weaklyHolomorphicOn isOpen_univ
  intro φ
  obtain ⟨f, hf⟩ := e.surjective φ
  exact (hU f).differentiableOn.congr fun z _ =>
    ((he f (normalized_global_dual F ν ω L hL hfinite U hU hfactor z)).symm.trans
      (DFunLike.congr_fun hf _)).symm

end ScalarAnalytic

variable (η : Measure (Idele F)) [η.IsHaarMeasure]
variable [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)ˣ]
  (μ : ∀ v : HeightOneSpectrum (𝓞 F), Measure (v.adicCompletion F)ˣ)
  [∀ v : HeightOneSpectrum (𝓞 F), (μ v).IsHaarMeasure]
  [∀ v : HeightOneSpectrum (𝓞 F), SigmaFinite (μ v)]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]
variable (hν : IsWeilQuotientMeasure (principalIdeles F) η Measure.count (globalClassMeasure F ν))

private abbrev weight (g : Idele F) (z : ℂ) : ℂ :=
  ideleNormTwist F (compactIdeleClassCharacter F ω) z (ideleClassMap F g)

include μ hν in
/-- The completed Hecke factor normalizes the global zeta distributions
to an entire family in the strong Schwartz–Bruhat dual. The family is
nonzero at every parameter and obeys idelic eigen-covariance everywhere. -/
theorem exists_globalNormalizedHeckeFamily
    (S : Finset (HeightOneSpectrum (𝓞 F))) (hs : Surjective (sIdeleClassInclusion F S))
    (hu : globalNormOneCharacter F ω ∈ (sUnramified F S : Set (QuasiCharacter (IdeleClass F)))) :
    ∃ (r₀ : E F) (L : ℂ → ℂ) (Δ : ℂ → StrongDual ℂ (E F)),
      EqOn L (globalCompletedHeckeEuler F ω S hs hu) {z | 1 < z.re} ∧
      MeromorphicOn L univ ∧
      Differentiable ℂ Δ ∧
      (∀ z, Δ z r₀ = 1) ∧
      (∀ z, globalContinuedMellinEval F ν ω =ᶠ[𝓝[≠] z] fun w => L w • Δ w) ∧
      ∀ (g : Idele F) (f : E F) (z : ℂ),
        Δ z (GlobalBruhat.leftTranslate F g f) = weight F ω g z * Δ z f := by
  obtain ⟨r, L, hEq, hL, hord, hstrip, ⟨B, hB, hr⟩, hfac⟩ :=
    exists_globalCompletedHeckeContinuation F ω S hs hu η ν μ hν
  have hf₂ : meromorphicOrderAt L (2 : ℂ) = 0 := hstrip 2 (Or.inr (by norm_num))
  have hfinite (z : ℂ) : meromorphicOrderAt L z ≠ ⊤ :=
    (hL.exists_meromorphicOrderAt_ne_top_iff_forall_mem isConnected_univ).mp
      ⟨2, mem_univ _, hf₂ ▸ WithTop.coe_ne_top⟩ z (mem_univ _)
  have hfac' (f : E F) : ∃ U : ℂ → ℂ, AnalyticOnNhd ℂ U univ ∧
      ∀ c, (fun z => Z F ν ω f z) =ᶠ[𝓝[≠] c] L * U := by
    obtain ⟨U, hU, he⟩ := hfac f
    refine ⟨U, hU, fun c => ?_⟩
    filter_upwards [he c] with w hw
    exact (globalContinuedMellinEval_apply F ν ω w f).trans hw
  choose U hU hfactor using hfac'
  let Δ := normalized_global_dual F ν ω L hL hfinite U hU hfactor
  refine ⟨B⁻¹ • r, L, Δ, hEq, hL,
    normalized_global_dual_holomorphic F ν ω L hL hfinite U hU hfactor, ?_, ?_, ?_⟩
  · intro z
    have hnorm : U r z = B := by
      apply eq_at_of_puncturedEq (hU r z trivial).continuousAt continuousAt_const
      filter_upwards [hfactor r z, meromorphic_eventually_regular z (hL z trivial) (hfinite z)]
        with w hw hreg
      change Z F ν ω r w = L w * U r w at hw
      have he := (globalContinuedMellinEval_apply F ν ω w r).symm.trans hw
      exact mul_left_cancel₀ hreg.2.1 (he.symm.trans ((congrFun hr w).trans (mul_comm B (L w))))
    rw [map_smul, smul_eq_mul]
    change B⁻¹ * U r z = 1
    rw [hnorm, inv_mul_cancel₀ hB]
  · intro z
    filter_upwards [meromorphic_eventually_regular z (hL z trivial) (hfinite z)] with w hw
    apply LinearMap.ext
    intro f
    exact quotient_at_regular F ν ω f hw.1 (hU f w trivial) (fun _ => hw.2.2)
      (hfactor f w)
  · intro g f z
    let t := GlobalBruhat.leftTranslate F g f
    have ha : AnalyticAt ℂ (weight F ω g) z :=
      analyticAt_const.mul ((analyticAt_id.mul analyticAt_const).cexp)
    change U t z = weight F ω g z * U f z
    apply eq_at_of_puncturedEq (hU t z trivial).continuousAt (ha.mul (hU f z trivial)).continuousAt
    filter_upwards [hfactor t z, hfactor f z,
      meromorphic_eventually_regular z (hL z trivial) (hfinite z)] with w ht hf hw
    have he := globalZetaContinued_leftTranslate F η ν hν g f ω w (fun _ => hw.2.2)
    change globalZetaContinued F ν t (compactIdeleClassCharacter F ω) 0 w =
      weight F ω g w * globalZetaContinued F ν f (compactIdeleClassCharacter F ω) 0 w at he
    have ht' := (globalContinuedMellinEval_apply F ν ω w t).symm.trans ht
    have hf' := (globalContinuedMellinEval_apply F ν ω w f).symm.trans hf
    change _ = L w * U t w at ht'
    change _ = L w * U f w at hf'
    rw [ht', hf', mul_left_comm (weight F ω g w)] at he
    exact mul_left_cancel₀ hw.2.1 he

include hν in
/-- On an admissible conductor stage, the normalized global family agrees,
up to one constant, with the normalized local Mellin numerator for every
test and every parameter. -/
theorem globalNormalizedHeckeFamily_stage
    (S : Finset (HeightOneSpectrum (𝓞 F))) (hs : Surjective (sIdeleClassInclusion F S))
    (hu : globalNormOneCharacter F ω ∈ (sUnramified F S : Set (QuasiCharacter (IdeleClass F))))
    (L : ℂ → ℂ) (hL : MeromorphicOn L univ) (hfinite : ∀ c, meromorphicOrderAt L c ≠ ⊤)
    (hEq : EqOn L (globalCompletedHeckeEuler F ω S hs hu) {z | 1 < z.re})
    (Δ : ℂ → StrongDual ℂ (E F)) (hΔ : Continuous Δ)
    (hfac : ∀ z, globalContinuedMellinEval F ν ω =ᶠ[𝓝[≠] z] fun w => L w • Δ w)
    (r : sLocalBruhatImage F S) (C : ℂ) (hC : C ≠ 0)
    (hr : sLocalEulerNormalizedMellin F S (fun v ↦ μ v.val)
      (sLocalNormOneCharacterOfGlobal F ω S hs hu) r = fun _ => C) :
    ∃ B : ℂ, B ≠ 0 ∧ ∀ (f : sLocalBruhatImage F S) (z : ℂ),
      Δ z f.val = B * sLocalEulerNormalizedMellin F S (fun v ↦ μ v.val)
        (sLocalNormOneCharacterOfGlobal F ω S hs hu) f z := by
  let σ := sLocalNormOneCharacterOfGlobal F ω S hs hu
  let N := sLocalEulerNormalizedMellin F S (fun v ↦ μ v.val) σ
  let G (f : sLocalBruhatImage F S) :=
    globalZetaContinued F ν f.val (compactIdeleClassCharacter F ω) 0
  have horder := globalMellin_reference_order_ne_top F η ω S hs hu μ ν hν r C hC hr 2
  obtain ⟨D, hD, hDr⟩ := globalZetaContinued_reference_eq_completedEuler
    F ω S hs hu η ν μ hν r C hr horder
  let R := (fun _ : ℂ => D⁻¹) * G r
  have hm : MeromorphicOn R univ := fun z hz => (MeromorphicAt.const D⁻¹ z).mul
    (globalZetaContinued_meromorphic F ν r.val _ (compactIdeleClassCharacter_unitary F ω) 0 z hz)
  have hR : EqOn R (globalCompletedHeckeEuler F ω S hs hu) {z | 1 < z.re} := by
    intro z hz
    change D⁻¹ * G r z = _
    have h := hDr hz
    change G r z = _ at h
    rw [h, ← mul_assoc, inv_mul_cancel₀ hD, one_mul]
  refine ⟨D / C, div_ne_zero hD hC, fun f z => ?_⟩
  have hcont : ContinuousAt (fun w => Δ w f.val) z :=
    ((strongBidualEvaluation f.val).continuous.comp hΔ).continuousAt
  have hN := sLocalEulerNormalizedMellin_entire F S (fun v ↦ μ v.val) σ f z (mem_univ z)
  apply eq_at_of_puncturedEq hcont (analyticAt_const.mul hN).continuousAt
  have hRgerm := globalCompletedHeckeContinuation_unique_germ F ω S hs hu hL hm hEq hR z
  have hcross := globalContinuedMellin_cross_normalized F η ω S hs hu μ ν hν f r z
  filter_upwards [hRgerm, hcross, hfac z, meromorphic_eventually_regular z (hL z trivial) (hfinite z)]
    with w h₁ h₂ h₃ hw
  change L w = D⁻¹ * G r w at h₁
  have hGr : G r w = D * L w := by rw [h₁, ← mul_assoc, mul_inv_cancel₀ hD, one_mul]
  change G f w * N r w = G r w * N f w at h₂
  have hGf : G f w = L w * Δ w f.val :=
    (globalContinuedMellinEval_apply F ν ω w f.val).symm.trans (DFunLike.congr_fun h₃ f.val)
  change N r = _ at hr
  rw [hGf, congrFun hr w, hGr, mul_assoc, mul_comm D (L w), mul_assoc] at h₂
  change Δ w f.val = D / C * N f w
  rw [div_mul_eq_mul_div]
  exact (eq_div_iff hC).mpr (mul_left_cancel₀ hw.2.1 h₂)

omit [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ] in
/-- On a pure stage test the normalized Mellin numerator is the product of
the cleared archimedean integral and the individual cleared finite integrals. -/
theorem sLocalEulerNormalizedMellin_pure_germ
    (S : Finset (HeightOneSpectrum (𝓞 F))) (σ : PontryaginDual (SLocalThetaNormOne F S))
    (φ : 𝓢(mixedEmbedding.mixedSpace F, ℂ))
    (g : ∀ v : S, locallyConstantTests (v.val.adicCompletion F)) (c : ℂ) :
    let a := sLocalRealArchParameters F S σ
    let j := sLocalComplexArchParameters F S σ
    let χ := sLocalFiniteZetaPhases F S σ
    let f := sLocalBruhatPure F S φ (locallyConstantTestPiProduct g)
    sLocalEulerNormalizedMellin F S (fun v ↦ μ v.val) σ f =ᶠ[𝓝[≠] c]
      fun z => (archimedeanNumberFieldZetaDenominator F a j z *
        archimedeanNumberFieldZeta F complexTamagawaAngularMeasure a j z φ) *
        ∏ v : S, finiteProductClearedLocal F S (fun v ↦ μ v.val) χ v (g v) z := by
  intro a j χ f
  let D := sLocalEulerDenominator F S σ
  let Df := sLocalFiniteZetaDenominator F S χ
  have ha := (sLocalEulerDenominator_analytic F S σ c).meromorphicAt
  have hm : MeromorphicOn D univ :=
    fun z _ => (sLocalEulerDenominator_analytic F S σ z).meromorphicAt
  have h1 := sLocalEulerDenominator_analytic F S σ 1
  have ho : meromorphicOrderAt D 1 = 0 := by
    rw [h1.meromorphicOrderAt_eq, h1.analyticOrderAt_eq_zero.mpr
      (sLocalEulerDenominator_ne_zero_of_pos F S σ (by norm_num))]
    rfl
  have hf : meromorphicOrderAt D c ≠ ⊤ :=
    hm.meromorphicOrderAt_ne_top_of_isPreconnected isPreconnected_univ
      (mem_univ (1 : ℂ)) (mem_univ c) (ho ▸ WithTop.coe_ne_top)
  have hne := ha.eventually_eq_zero_or_eventually_ne_zero.resolve_left
    (fun h => hf (meromorphicOrderAt_eq_top_iff.mpr h))
  filter_upwards [sLocalEulerNormalizedMellin_eq_germ F S (fun v ↦ μ v.val) σ f c, hne]
    with z hz hd
  have hd' : Df z ≠ 0 := fun h => hd (by
    change archimedeanNumberFieldZetaDenominator F a j z * Df z = 0
    rw [h, mul_zero])
  rw [hz]
  simp only [sLocalProductZetaContinued, sLocalFiniteZetaSchwartzTest, f,
    sLocalBruhatContractFinite_pure, map_smul, smul_eq_mul]
  change (archimedeanNumberFieldZetaDenominator F a j z * Df z) *
    (sLocalFiniteZetaContinued F S (fun v ↦ μ v.val) χ z (locallyConstantTestPiProduct g) *
      archimedeanNumberFieldZeta F complexTamagawaAngularMeasure a j z φ) = _
  rw [sLocalFiniteZetaContinued, smul_apply, smul_eq_mul, sLocalFiniteZetaCleared_piProduct]
  let Da := archimedeanNumberFieldZetaDenominator F a j z
  let A := archimedeanNumberFieldZeta F complexTamagawaAngularMeasure a j z φ
  let P := ∏ v : S, finiteProductClearedLocal F S (fun v ↦ μ v.val) χ v (g v) z
  change (Da * Df z) * ((Df z)⁻¹ * P * A) = (Da * A) * P
  calc
    _ = (Df z * (Df z)⁻¹) * ((Da * A) * P) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hd', one_mul]

end

end Masullo
