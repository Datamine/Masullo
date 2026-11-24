import GlobalConversePoleClearing
import GlobalHeckeDivisor
import SLocalOrdinaryPairedMellin

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
local instance : MeasurableSpace (InfiniteAdeleRing F) := borel _
local instance : BorelSpace (InfiniteAdeleRing F) := ⟨rfl⟩

attribute [local instance] sLocalZetaUnfolding_classMeasurable sLocalZetaUnfolding_classBorel
  sLocalZetaUnfolding_idelesMeasurable sLocalZetaUnfolding_idelesBorel

variable (ν : Measure (K F)) [ν.IsHaarMeasure]
variable (η : Measure (Idele F)) [η.IsHaarMeasure]
variable [∀ v : Place F, MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : Place F, BorelSpace (v.adicCompletion F)ˣ]
  (μ : ∀ v : Place F, Measure (v.adicCompletion F)ˣ)
  [∀ v : Place F, (μ v).IsHaarMeasure] [∀ v : Place F, SigmaFinite (μ v)]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]
variable (hν : IsWeilQuotientMeasure (principalIdeles F) η Measure.count (globalClassMeasure F ν))
variable (S : Finset (Place F)) (ω : PontryaginDual (K F))
  (hS : Surjective (sIdeleClassInclusion F S))
  (hω : globalNormOneCharacter F ω ∈ (sUnramified F S : Set (QuasiCharacter (IdeleClass F))))

private abbrev E := sLocalBruhatImage F S
private abbrev phase := sLocalNormOneCharacterOfGlobal F ω S hS hω
private abbrev Z (ψ : PontryaginDual (SLocalThetaNormOne F S)) (f : E F S) :=
  sLocalProductZetaContinued F S (fun v : S ↦ μ v.val) ψ
    (sLocalRealArchParameters F S ψ) (sLocalComplexArchParameters F S ψ) f
private abbrev G (f : E F S) :=
  globalZetaContinued F ν f.val (compactIdeleClassCharacter F ω) 0

omit [∀ v : Place F, MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : Place F, BorelSpace (v.adicCompletion F)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ] in
private theorem selectedFourier_val_eq
    (hDiff : ∀ v : Place F, v.asIdeal ∣ differentIdeal ℤ (𝓞 F) → v ∈ S) (f : E F S) :
    (sLocalSelectedFourier F S f).val = GlobalBruhat.fourier F f.val := by
  have ht : sLocalFourierTailVolume F S = 1 := by
    apply finprod_eq_one_of_forall_eq_one
    intro v
    have hv : ¬ v.val.asIdeal ∣ differentIdeal ℤ (𝓞 F) := fun h ↦ v.property (hDiff v.val h)
    simp [differentPrimeMass, multiplicity_eq_zero.mpr hv]
  simp only [sLocalSelectedFourier, ht, ENNReal.toReal_one, Complex.ofReal_one, inv_one, one_smul]
  exact sLocalBruhatProjection_fixes F S _
    (sLocalFourier_preserves_stage_of_different F S hDiff f.val f.property)

include μ hν hS hω in
/-- Realize the product of a global stage transform and an entire multiplier
by a test at the same stage when the product is Schwartz–Bergman. The
conclusion compares the actual meromorphic germs. -/
theorem globalMellinMultiplier_realized_on_stage
    (hω' : globalNormOneCharacter F ω⁻¹ ∈
      (sUnramified F S : Set (QuasiCharacter (IdeleClass F))))
    (hDiff : ∀ v : Place F, v.asIdeal ∣ differentIdeal ℤ (𝓞 F) → v ∈ S)
    (f : E F S) {m : ℂ → ℂ} (hm : Differentiable ℂ m)
    (b : SchwartzBergman (univ : Set ℝ))
    (hb : ∀ z, (fun w ↦ m w * G F ν S ω f w) =ᶠ[𝓝[≠] z] b.val) :
    ∃ g : E F S, ∀ c, G F ν S ω g =ᶠ[𝓝[≠] c] b.val := by
  let σ := phase F S ω hS hω
  let σ' := phase F S ω⁻¹ hS hω'
  let f' := sLocalSelectedFourier F S f
  have hFourier : f'.val = GlobalBruhat.fourier F f.val := selectedFourier_val_eq F S hDiff f
  have hσ' : σ' = σ⁻¹ := by
    ext k
    obtain ⟨g, rfl⟩ := globalNormOneToSLocal_surjective F S hS k
    dsimp only [σ', phase]
    rw [sLocalNormOneCharacterOfGlobal_match]
    change (↑((ω g)⁻¹) : ℂ) =
      ↑((sLocalNormOneCharacterOfGlobal F ω S hS hω (globalNormOneToSLocal F S hS g))⁻¹)
    rw [sLocalNormOneCharacterOfGlobal_match]
  let μ₀ := fun v : S ↦ μ v.val
  let ρ := sLocalZetaProductMeasure F S μ₀ (archimedeanMultiplicativeHaar F)
  letI : ρ.IsHaarMeasure := sLocalZetaProductMeasure_isHaar F S μ₀ (archimedeanMultiplicativeHaar F)
  obtain ⟨ν₀, hhaar, hν₀⟩ := sLocalClassHaar_exists_weil F S ρ
  letI := hhaar
  let U := sLocalPairedBergmanMellin F S ν₀ σ
  obtain ⟨ε, _, _, _, _, hRange⟩ := exists_sLocalOrdinaryPaired_range F S μ₀ ν₀ hν₀ σ
  let τ := sLocalExplicitTateFactor F S σ ε
  let p := U (Submodule.Quotient.mk f)
  have hp : p ∈ sLocalBergmanGluing τ := by
    change p ∈ (sLocalBergmanGluing (sLocalExplicitTateFactor F S σ ε) : Set _)
    rw [← hRange]
    exact ⟨_, rfl⟩
  have hpair (t : E F S) :
      (∀ z, 0 < z.re → (U (Submodule.Quotient.mk t)).1.val z = Z F μ S σ t z) ∧
      (∀ z, z.re < 1 →
        (U (Submodule.Quotient.mk t)).2.val z = Z F μ S σ⁻¹ (sLocalSelectedFourier F S t) (1-z)) := by
    obtain ⟨hR, hL⟩ := sLocalPairedBergmanMellin_idelic F S ν₀ σ ρ hν₀ t
    exact ⟨fun z hz ↦ (hR z hz).trans ((sLocalIdelicZeta_meromorphic_continuation F S μ₀ σ t).2 hz).symm,
      fun z hz ↦ (hL z hz).trans ((sLocalIdelicZeta_meromorphic_continuation F S μ₀ σ⁻¹
        (sLocalSelectedFourier F S t)).2 (by simpa [Complex.sub_re, sub_pos] using hz)).symm⟩
  let R := Ioi (0 : ℝ)
  let L := Iio (1 : ℝ)
  have hR : (fun z ↦ m z * p.1.val z) ∈ schwartzBergmanSubmodule R := by
    refine ⟨fun z hz ↦ ?_,
      hm.differentiableOn.mul p.1.property.2.1, ?_⟩
    · change m z * p.1.val z = 0
      exact (congrArg (m z * ·) (p.1.property.1 hz)).trans (mul_zero _)
    intro a d had hsub n
    have ha := hsub (left_mem_Icc.mpr had)
    obtain ⟨C, hC⟩ := globalMellinMultiplier_rapid_on_stage F S ω hS hω ν η μ hν f hm b hb ha had n
    refine ⟨C, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    change ‖z ^ n * (m z * p.1.val z)‖ ≤ C
    rw [(hpair f).1 z (hsub hz)]
    exact hC ⟨z, hz, rfl⟩
  have hL : (fun z ↦ m z * p.2.val z) ∈ schwartzBergmanSubmodule L := by
    refine ⟨fun z hz ↦ ?_,
      hm.differentiableOn.mul p.2.property.2.1, ?_⟩
    · change m z * p.2.val z = 0
      exact (congrArg (m z * ·) (p.2.property.1 hz)).trans (mul_zero _)
    intro a d had hsub n
    have hd := hsub (right_mem_Icc.mpr had)
    have hFourierEq : (⟨GlobalBruhat.fourier F f.val,
      sLocalFourier_preserves_stage_of_different F S hDiff f.val f.property⟩ : E F S) = f' :=
      Subtype.ext hFourier.symm
    have h := globalMellinMultiplier_rapid_on_reflected_stage F S ω hS ν η μ hν hω' hDiff f hm b hb had hd n
    change BddAbove ((fun z : ℂ ↦ ‖z ^ n * (m z *
      Z F μ S σ' ⟨GlobalBruhat.fourier F f.val,
        sLocalFourier_preserves_stage_of_different F S hDiff f.val f.property⟩ (1-z))‖) ''
      (Complex.re ⁻¹' Icc a d)) at h
    rw [hFourierEq, hσ'] at h
    obtain ⟨C, hC⟩ := h
    refine ⟨C, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    change ‖z ^ n * (m z * p.2.val z)‖ ≤ C
    rw [(hpair f).2 z (hsub hz)]
    exact hC ⟨z, hz, rfl⟩
  let q : SchwartzBergman R × SchwartzBergman L := ⟨⟨_, hR⟩, ⟨_, hL⟩⟩
  have hq : q ∈ sLocalBergmanGluing τ := by
    intro z hz hr
    change m z * p.1.val z = τ z * (m z * p.2.val z)
    rw [hp z hz hr]
    ring
  have hU : q ∈ range U := by
    change q ∈ range (sLocalPairedBergmanMellin F S ν₀ σ)
    rw [hRange]
    exact hq
  obtain ⟨x, hx⟩ := hU
  obtain ⟨g, rfl⟩ := (sLocalHomogeneousThetaKernel F S ν₀ σ).mkQ_surjective x
  have hLocal (z : ℂ) (hz : 0 < z.re) : Z F μ S σ g z = m z * Z F μ S σ f z := by
    have he := congrArg (fun v : SchwartzBergman R × SchwartzBergman L ↦ v.1.val z) hx
    change (U (Submodule.Quotient.mk g)).1.val z = m z * p.1.val z at he
    rw [(hpair g).1 z hz, (hpair f).1 z hz] at he
    exact he
  obtain ⟨W, _, _, _, hW, heW, _, _⟩ :=
    exists_manuscriptFiniteHeckeOutside_polynomial_strips F (normOneEulerCharacter F ω) S ν η μ hν
  obtain ⟨A, _, hExterior⟩ :=
    globalContinuedMellin_eq_outside_mul_stage F ν η μ hν S ω hS hω hW heW
  have hLocalGerm (c : ℂ) :
      Z F μ S σ g =ᶠ[𝓝[≠] c] fun z ↦ m z * Z F μ S σ f z := by
    apply boundedPoleMellinSpace_unique_germs (D := {z : ℂ | 0 < z.re})
      (isOpen_lt continuous_const Complex.continuous_re) ⟨1, by norm_num⟩
    · exact sLocalProductZetaContinued_meromorphic F S μ₀ σ _ _ g
    · exact fun z ↦ (hm.analyticAt z).meromorphicAt.mul
        (sLocalProductZetaContinued_meromorphic F S μ₀ σ _ _ f z)
    · exact fun z hz ↦ hLocal z hz
  refine ⟨g, fun c ↦ ?_⟩
  filter_upwards [hExterior g c, hExterior f c, hLocalGerm c, hb c] with z hg hf hmz hbz
  change G F ν S ω g z = A * W z * Z F μ S σ g z at hg
  change G F ν S ω f z = A * W z * Z F μ S σ f z at hf
  change m z * G F ν S ω f z = b.val z at hbz
  rw [hg, hmz, ← hbz, hf]
  ring

include μ hν hS hω in
/-- The realized transform has a representative with both polar evaluations
zero, and equals the entire target at the two possible pole centers as well. -/
theorem globalMellinMultiplier_realized_polarFree_on_stage
    (hω' : globalNormOneCharacter F ω⁻¹ ∈
      (sUnramified F S : Set (QuasiCharacter (IdeleClass F))))
    (hDiff : ∀ v : Place F, v.asIdeal ∣ differentIdeal ℤ (𝓞 F) → v ∈ S)
    (f : E F S) {m : ℂ → ℂ} (hm : Differentiable ℂ m)
    (b : SchwartzBergman (univ : Set ℝ))
    (hb : ∀ z, (fun w ↦ m w * G F ν S ω f w) =ᶠ[𝓝[≠] z] b.val) :
    ∃ g : E F S, GlobalBruhat.polarEvaluation F g.val = 0 ∧ G F ν S ω g = b.val := by
  obtain ⟨t, ht⟩ := globalMellinMultiplier_realized_on_stage F ν η μ hν S ω hS hω hω' hDiff f hm b hb
  have hd : Differentiable ℂ b.val := by
    simpa only [preimage_univ, differentiableOn_univ] using b.property.2.1
  obtain ⟨g, hg, he⟩ : ∃ g : E F S, GlobalBruhat.polarEvaluation F g.val = 0 ∧
      ∀ z, G F ν S ω g =ᶠ[𝓝[≠] z] b.val := by
    by_cases htriv : ω = 1
    · refine ⟨t, ?_, ht⟩
      apply ((globalMellin_nonneg_orders_iff F ω ν t.val).mp ?_).resolve_left (not_not_intro htriv)
      change 0 ≤ meromorphicOrderAt (G F ν S ω t) 0 ∧ 0 ≤ meromorphicOrderAt (G F ν S ω t) 1
      rw [meromorphicOrderAt_congr (ht 0), meromorphicOrderAt_congr (ht 1)]
      exact ⟨(hd.analyticAt 0).meromorphicOrderAt_nonneg, (hd.analyticAt 1).meromorphicOrderAt_nonneg⟩
    · obtain ⟨g, hg, hq⟩ := exists_sLocal_polarEvaluation_zero_same_globalClass F η ω S hS hω ν hν htriv t
      have hEq : G F ν S ω g = G F ν S ω t := globalMellin_eq_of_mkQ_eq F η ω ν hν hq
      exact ⟨g, hg, fun z ↦ hEq ▸ ht z⟩
  have hp : globalZetaPolarVanishes F g.val (compactIdeleClassCharacter F ω) :=
    (globalZetaPolarVanishes_compact_iff F g.val ω).mpr
      (Or.inr ⟨congrArg Prod.fst hg, congrArg Prod.snd hg⟩)
  have hB := globalZetaContinued_mem_schwartzBergman F ν ω g.val hp
  have hG : Differentiable ℂ (G F ν S ω g) := by
    simpa only [preimage_univ, differentiableOn_univ] using hB.2.1
  refine ⟨g, hg, funext fun z ↦ ?_⟩
  exact ((hG.continuous.continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
    hd.continuous.continuousAt).mp (he z)).eq_of_nhds

include μ hν hS hω in
/-- Every member of the cleared divisor ideal of a reference test is realized
by a polar-free test at the same admissible stage. -/
theorem globalHeckeDivisor_realized_on_stage
    (hω' : globalNormOneCharacter F ω⁻¹ ∈
      (sUnramified F S : Set (QuasiCharacter (IdeleClass F))))
    (hDiff : ∀ v : Place F, v.asIdeal ∣ differentIdeal ℤ (𝓞 F) → v ∈ S)
    (r : E F S) (b : SchwartzBergman (univ : Set ℝ))
    (hb : b ∈ bergmanDivisorSubmodule (globalHeckeClearedZeta F ν ω r.val)) :
    ∃ g : E F S, GlobalBruhat.polarEvaluation F g.val = 0 ∧ G F ν S ω g = b.val := by
  have hD : Differentiable ℂ (globalHeckeClearedZeta F ν ω r.val) :=
    fun z ↦ (globalHeckeClearedZeta_analytic F ν ω r.val z).differentiableAt
  obtain ⟨u, hu, he⟩ := (bergmanDivisorSubmodule_mem_iff hD b).mp hb
  let m : ℂ → ℂ := fun z ↦ globalHeckePoleFactor F ω z * u z
  have hp : Differentiable ℂ (globalHeckePoleFactor F ω) :=
    fun z ↦ (globalHeckePoleFactor_analytic F ω z).differentiableAt
  have hm : Differentiable ℂ m := hp.mul hu
  apply globalMellinMultiplier_realized_polarFree_on_stage F ν η μ hν S ω hS hω hω' hDiff r hm b
  intro c
  have hne (p : ℂ) : ∀ᶠ z in 𝓝[≠] c, z ≠ p := by
    rcases eq_or_ne c p with rfl | h
    · exact self_mem_nhdsWithin
    · exact eventually_ne_nhdsWithin h
  filter_upwards [hne 0, hne 1] with z hz₀ hz₁
  rw [he z, globalHeckeClearedZeta_eq F ν ω r.val z hz₀ hz₁]
  dsimp only [m, G]
  ring

include μ hν in
/-- Each cleared reference has a common finite stage realizing all the
Schwartz–Bergman functions divisible by that reference. -/
theorem globalHeckeDivisor_realized (r : GlobalBruhat F) :
    ∃ T : Finset (Place F), ∀ b : SchwartzBergman (univ : Set ℝ),
      b ∈ bergmanDivisorSubmodule (globalHeckeClearedZeta F ν ω r) →
        ∃ g : E F T, GlobalBruhat.polarEvaluation F g.val = 0 ∧ G F ν T ω g = b.val := by
  obtain ⟨U, rU, hrU⟩ := globalBruhat_exhausted F r
  obtain ⟨V, hV, hχ, hχ', hD⟩ := exists_globalHeckeTateStage F ω
  let T := V ∪ U
  have hVT : V ⊆ T := Finset.subset_union_left
  have hUT : U ⊆ T := Finset.subset_union_right
  have hT : Surjective (sIdeleClassInclusion F T) := by
    intro x
    obtain ⟨a, rfl⟩ := hV x
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    exact ⟨QuotientGroup.mk (sIdeleTransition F hVT a), rfl⟩
  have hunram {χ : QuasiCharacter (IdeleClass F)}
      (h : χ ∈ (sUnramified F V : Set (QuasiCharacter (IdeleClass F)))) :
      χ ∈ (sUnramified F T : Set (QuasiCharacter (IdeleClass F))) :=
    (mem_sUnramified_iff F T _).mpr fun v hv u ↦
      (mem_sUnramified_iff F V _).mp h v (fun hv' ↦ hv (hVT hv')) u
  let rT := sLocalBruhatTransition F hUT rU
  have hrT : rT.val = r := hrU
  have hrealize (b : SchwartzBergman (univ : Set ℝ))
      (hb : b ∈ bergmanDivisorSubmodule (globalHeckeClearedZeta F ν ω r)) :
      ∃ g : E F T, GlobalBruhat.polarEvaluation F g.val = 0 ∧ G F ν T ω g = b.val := by
    apply globalHeckeDivisor_realized_on_stage F ν η μ hν T ω hT (hunram hχ) (hunram hχ')
      (fun v hv ↦ hVT (hD v hv)) rT b
    rwa [hrT]
  exact ⟨T, hrealize⟩

include μ hν in
/-- The actual polar-free adelic Mellin image is the closed entire divisor
ideal, and every member is realized on one common finite stage. -/
theorem exists_globalHeckeDivisor_polarFree_range :
    ∃ (r : GlobalBruhat F) (T : Finset (Place F)),
      (∀ z, analyticOrderAt (globalHeckeClearedZeta F ν ω r) z ≠ ⊤) ∧
      (∀ b : SchwartzBergman (univ : Set ℝ),
        b ∈ bergmanDivisorSubmodule (globalHeckeClearedZeta F ν ω r) →
          ∃ g : E F T, GlobalBruhat.polarEvaluation F g.val = 0 ∧ G F ν T ω g = b.val) ∧
      ∀ b : SchwartzBergman (univ : Set ℝ),
        b ∈ bergmanDivisorSubmodule (globalHeckeClearedZeta F ν ω r) ↔
          ∃ g : GlobalBruhat F, GlobalBruhat.polarEvaluation F g = 0 ∧
            globalZetaContinued F ν g (compactIdeleClassCharacter F ω) 0 = b.val := by
  obtain ⟨r, hr, hforward, _⟩ := exists_globalHeckeDivisor F η ν ω μ hν
  obtain ⟨T, hrealize⟩ := globalHeckeDivisor_realized F ν η μ hν ω r
  refine ⟨r, T, hr, hrealize, fun b ↦ ⟨?_, ?_⟩⟩
  · intro hb
    obtain ⟨g, hg, he⟩ := hrealize b hb
    exact ⟨g.val, hg, he⟩
  · rintro ⟨g, hg, he⟩
    have hp : globalZetaPolarVanishes F g (compactIdeleClassCharacter F ω) :=
      (globalZetaPolarVanishes_compact_iff F g ω).mpr
        (Or.inr ⟨congrArg Prod.fst hg, congrArg Prod.snd hg⟩)
    have hb : globalPoleFreeZetaBergman F ν ω g hp = b := Subtype.ext he
    exact hb ▸ hforward g hp

include μ hν in
/-- The image of the global test space with both polar evaluations zero is
closed in the actual entire Schwartz–Bergman topology. -/
theorem globalPoleFreeMellin_image_isClosed :
    IsClosed {b : SchwartzBergman (univ : Set ℝ) |
      ∃ f : GlobalBruhat F, GlobalBruhat.polarEvaluation F f = 0 ∧
        globalZetaContinued F ν f (compactIdeleClassCharacter F ω) 0 = b.val} := by
  obtain ⟨r, _, _, _, he⟩ := exists_globalHeckeDivisor_polarFree_range F ν η μ hν ω
  have h := bergmanDivisorSubmodule_isClosed (g := globalHeckeClearedZeta F ν ω r)
    (fun z ↦ (globalHeckeClearedZeta_analytic F ν ω r z).differentiableAt)
  convert h using 1
  exact Set.ext fun b ↦ (he b).symm

#print axioms globalMellinMultiplier_realized_on_stage
#print axioms globalMellinMultiplier_realized_polarFree_on_stage
#print axioms globalHeckeDivisor_realized_on_stage
#print axioms exists_globalHeckeDivisor_polarFree_range
#print axioms globalPoleFreeMellin_image_isClosed

end

end Masullo
