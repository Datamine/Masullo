import GlobalHeckeBergman
import BergmanVerticalTranslation

open Bornology Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical ENat NumberField

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]
private abbrev Place := HeightOneSpectrum (𝓞 F)
private abbrev E := sLocalBruhatImage F
private abbrev K := normOneIdeleClass F

local instance : MeasurableSpace (Idele F) := borel _
local instance : MeasurableSpace (K F) := borel _
local instance : BorelSpace (K F) := ⟨rfl⟩

variable (η : Measure (Idele F)) [η.IsHaarMeasure]
variable (ν : Measure (K F)) [ν.IsHaarMeasure]
variable (ω : PontryaginDual (K F))
variable [∀ v : Place F, MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : Place F, BorelSpace (v.adicCompletion F)ˣ]
  (μ : ∀ v : Place F, Measure (v.adicCompletion F)ˣ)
  [∀ v : Place F, (μ v).IsHaarMeasure] [∀ v : Place F, SigmaFinite (μ v)]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]

private abbrev Z (f : GlobalBruhat F) :=
  globalZetaContinued F ν f (compactIdeleClassCharacter F ω) 0

private abbrev χ := globalNormOneCharacter F ω
private abbrev A (S : Finset (Place F)) (hs : Surjective (sIdeleClassInclusion F S))
    (hu : χ F ω ∈ (sUnramified F S : Set (QuasiCharacter (IdeleClass F)))) :=
  sLocalNormOneCharacterOfGlobal F ω S hs hu

private abbrev N (S : Finset (Place F)) (ϕ : PontryaginDual (SLocalThetaNormOne F S)) :=
  sLocalEulerNormalizedMellin F S (fun v ↦ μ v.val) ϕ

private abbrev L (S : Finset (Place F)) (ϕ : PontryaginDual (SLocalThetaNormOne F S)) :=
  sLocalProductZetaContinued F S (fun v ↦ μ v.val) ϕ (sLocalRealArchParameters F S ϕ)
    (sLocalComplexArchParameters F S ϕ)

variable (S : Finset (Place F)) (hs : Surjective (sIdeleClassInclusion F S))
variable (hu : χ F ω ∈ (sUnramified F S : Set (QuasiCharacter (IdeleClass F))))

omit [∀ v : Place F, MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : Place F, BorelSpace (v.adicCompletion F)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ] in
private theorem denominator_order (ϕ : PontryaginDual (SLocalThetaNormOne F S)) (c : ℂ) :
    meromorphicOrderAt (sLocalEulerDenominator F S ϕ) c =
      (sLocalPoleCount F S ϕ c : WithTop ℤ) := by
  obtain ⟨U, hU, hn, he, _⟩ := sLocalEulerDenominator_exists_leadingFactor F S ϕ c
  have hD := sLocalEulerDenominator_analytic F S ϕ c
  rw [hD.meromorphicOrderAt_eq, hD.analyticOrderAt_eq_natCast.mpr ⟨U, hU, hn, he⟩,
    ENat.map_natCast]
  rfl

omit [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ] in
private theorem numerator_order (ϕ : PontryaginDual (SLocalThetaNormOne F S))
    (f : E F S) (c : ℂ) :
    meromorphicOrderAt (N F μ S ϕ f) c =
      (sLocalPoleCount F S ϕ c : WithTop ℤ) + meromorphicOrderAt (L F μ S ϕ f) c := by
  have h := meromorphicOrderAt_congr
    (sLocalEulerNormalizedMellin_eq_germ F S (fun v ↦ μ v.val) ϕ f c)
  change meromorphicOrderAt (N F μ S ϕ f) c =
    meromorphicOrderAt (sLocalEulerDenominator F S ϕ * L F μ S ϕ f) c at h
  rw [h, meromorphicOrderAt_mul (sLocalEulerDenominator_analytic F S ϕ c).meromorphicAt
    (sLocalProductZetaContinued_meromorphic F S (fun v ↦ μ v.val) ϕ _ _ f c),
    denominator_order F S ϕ c]

/-- Padding a test changes its local Mellin order and its Euler pole count
by opposite amounts, so the order of its normalized numerator is invariant. -/
theorem sLocalEulerNormalizedMellin_order_pad
    {T : Finset (Place F)} (hST : S ⊆ T)
    (ht : Surjective (sIdeleClassInclusion F T))
    (hv : χ F ω ∈ (sUnramified F T : Set (QuasiCharacter (IdeleClass F))))
    (f : E F S) (c : ℂ) :
    meromorphicOrderAt (N F μ S (A F ω S hs hu) f) c =
      meromorphicOrderAt (N F μ T (A F ω T ht hv) (sLocalBruhatTransition F hST f)) c := by
  rw [numerator_order, numerator_order]
  have hL := sLocalProductZetaContinued_global_pad_order F S ω hs hu μ hST ht hv f c
  change meromorphicOrderAt (L F μ S (A F ω S hs hu) f) c = _ at hL
  have hD := sLocalPoleCount_global_pad F S ω hs hu hST ht hv c
  change sLocalPoleCount F T (A F ω T ht hv) c = _ at hD
  rw [hL, hD, Nat.cast_add, add_assoc]

variable (hν : IsWeilQuotientMeasure (principalIdeles F) η Measure.count (globalClassMeasure F ν))

include hν in
/-- Every Euler reference with a nonzero constant local numerator minimizes
the global order at every center among all adelic test transforms. -/
theorem globalHeckeOrderReference_min (r : E F S) (C : ℂ) (hC : C ≠ 0)
    (hN : N F μ S (A F ω S hs hu) r = fun _ ↦ C) (f : GlobalBruhat F) (c : ℂ) :
    meromorphicOrderAt (Z F ν ω r.val) c ≤ meromorphicOrderAt (Z F ν ω f) c := by
  obtain ⟨U, fU, hfU⟩ := globalBruhat_exhausted F f
  let T := S ∪ U
  have hST : S ⊆ T := Finset.subset_union_left
  have hUT : U ⊆ T := Finset.subset_union_right
  have ht : Surjective (sIdeleClassInclusion F T) := by
    intro x
    obtain ⟨a, rfl⟩ := hs x
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective a
    exact ⟨QuotientGroup.mk (sIdeleTransition F hST b), rfl⟩
  have huT : χ F ω ∈ (sUnramified F T : Set (QuasiCharacter (IdeleClass F))) :=
    (mem_sUnramified_iff F T _).mpr fun v hv u ↦
      (mem_sUnramified_iff F S _).mp hu v (fun h ↦ hv (hST h)) u
  obtain ⟨t, _, _, _, _, hT⟩ := exists_globalMellin_order_reference F η ω T ht huT μ ν hν
  let rT := sLocalBruhatTransition F hST r
  let fT := sLocalBruhatTransition F hUT fU
  have hrT : rT.val = r.val := rfl
  have hfT : fT.val = f := hfU
  have he := sLocalEulerNormalizedMellin_order_pad F ω μ S hs hu hST ht huT r c
  change meromorphicOrderAt (N F μ S (A F ω S hs hu) r) c =
    meromorphicOrderAt (N F μ T (A F ω T ht huT) rT) c at he
  change N F μ S (A F ω S hs hu) r = _ at hN
  rw [hN, meromorphicOrderAt_const, ite_eq_right hC] at he
  have hTr := hT rT c
  change meromorphicOrderAt (Z F ν ω rT.val) c = meromorphicOrderAt (Z F ν ω t.val) c +
    meromorphicOrderAt (N F μ T (A F ω T ht huT) rT) c at hTr
  rw [hrT, ← he, add_zero] at hTr
  rw [hTr, ← hfT, hT fT c]
  exact le_add_of_nonneg_right
    (sLocalEulerNormalizedMellin_entire F T _ (A F ω T ht huT) fT c trivial).meromorphicOrderAt_nonneg

include μ hν in
/-- A single global zeta reference attains the minimum at every center. -/
theorem exists_globalHeckeOrderReference :
    ∃ r : GlobalBruhat F, (∀ c : ℂ, meromorphicOrderAt (Z F ν ω r) c ≠ ⊤) ∧
      ∀ (f : GlobalBruhat F) (c : ℂ),
        meromorphicOrderAt (Z F ν ω r) c ≤ meromorphicOrderAt (Z F ν ω f) c := by
  obtain ⟨B, hB⟩ := exists_homogeneousThetaPlaceBase F ω
  obtain ⟨hb, huB⟩ := hB B Subset.rfl
  obtain ⟨r, C, hC, hN, hfinite, _⟩ :=
    exists_globalMellin_order_reference F η ω B hb huB μ ν hν
  exact ⟨r.val, hfinite, globalHeckeOrderReference_min F η ν ω μ B hb huB hν r C hC hN⟩

theorem analyticOrder_le_of_meromorphicOrder_le
    {g f : ℂ → ℂ} {c : ℂ} (hg : AnalyticAt ℂ g c) (hf : AnalyticAt ℂ f c)
    (hfinite : analyticOrderAt g c ≠ ⊤) (hle : meromorphicOrderAt g c ≤ meromorphicOrderAt f c) :
    analyticOrderAt g c ≤ analyticOrderAt f c := by
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hfinite
  rw [hg.meromorphicOrderAt_eq, hf.meromorphicOrderAt_eq, ← hn] at hle
  rw [← hn]
  cases hm : analyticOrderAt f c using ENat.recTopCoe with
  | top => exact le_top
  | coe m =>
    rw [hm, ENat.map_natCast, ENat.map_natCast] at hle
    have hnm : (n : ℤ) ≤ (m : ℤ) := WithTop.coe_le_coe.mp hle
    exact_mod_cast hnm

omit [∀ v : Place F, MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : Place F, BorelSpace (v.adicCompletion F)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ] in
/-- A minimal reference on the trivial component retains both simple poles. -/
theorem trivial_reference_regularized_nonzero (r : GlobalBruhat F)
    (hmin : ∀ (f : GlobalBruhat F) (c : ℂ),
      meromorphicOrderAt (Z F ν 1 r) c ≤ meromorphicOrderAt (Z F ν 1 f) c) :
    globalHeckeClearedZeta F ν 1 r 0 ≠ 0 ∧ globalHeckeClearedZeta F ν 1 r 1 ≠ 0 := by
  letI := normOneIdeleClass_compact F
  letI : IsFiniteMeasure ν := ⟨isCompact_univ.measure_lt_top⟩
  have hmass : (ν.real univ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (ENNReal.toReal_pos (isOpen_univ.measure_ne_zero ν univ_nonempty) (measure_ne_top _ _)).ne'
  obtain ⟨f, hf⟩ := GlobalBruhat.polarEvaluation_surjective F (1, 1)
  have h₀ : (GlobalBruhat.algebraicEquiv F f).val 0 = 1 := congrArg Prod.fst hf
  have h₁ : (GlobalBruhat.algebraicEquiv F (GlobalBruhat.fourier F f)).val 0 = 1 :=
    congrArg Prod.snd hf
  have poles (f : GlobalBruhat F) := globalZetaContinued_pole_order F ν f
    (compactIdeleClassCharacter F 1) (compactIdeleClassCharacter_unitary F 1) 0
  have hf₀ : meromorphicOrderAt (Z F ν 1 f) 0 = (-1 : ℤ) := by
    simpa only [compactIdeleClassCharacter_integral, ite_true, h₀, mul_one,
      ite_eq_right hmass, neg_zero] using (poles f).1
  have hf₁ : meromorphicOrderAt (Z F ν 1 f) 1 = (-1 : ℤ) := by
    simpa only [compactIdeleClassCharacter_integral, ite_true, h₁, mul_one,
      ite_eq_right hmass, sub_zero] using (poles f).2
  constructor
  · rw [globalHeckeClearedZeta_trivial_zero, neg_ne_zero]
    intro h
    have hr : AnalyticAt ℂ (Z F ν 1 r) 0 := by
      simpa only [compactIdeleClassCharacter_integral, ite_true, ite_eq_left h, neg_zero]
        using (poles r).1
    have hbad := hr.meromorphicOrderAt_nonneg.trans (hmin f 0)
    rw [hf₀] at hbad
    exact (by norm_num : ¬ (0 : ℤ) ≤ -1) (WithTop.coe_le_coe.mp hbad)
  · rw [globalHeckeClearedZeta_trivial_one, neg_ne_zero]
    intro h
    have hr : AnalyticAt ℂ (Z F ν 1 r) 1 := by
      simpa only [compactIdeleClassCharacter_integral, ite_true, ite_eq_left h, sub_zero]
        using (poles r).2
    have hbad := hr.meromorphicOrderAt_nonneg.trans (hmin f 1)
    rw [hf₁] at hbad
    exact (by norm_num : ¬ (0 : ℤ) ≤ -1) (WithTop.coe_le_coe.mp hbad)

omit [∀ v : Place F, MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : Place F, BorelSpace (v.adicCompletion F)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ] in
private theorem poleFactor_order_zero (c : ℂ) (hc : ω ≠ 1 ∨ c ≠ 0 ∧ c ≠ 1) :
    meromorphicOrderAt (globalHeckePoleFactor F ω) c = 0 := by
  have hne : globalHeckePoleFactor F ω c ≠ 0 := by
    by_cases hω : ω = 1
    · obtain ⟨h₀, h₁⟩ := hc.resolve_left (not_not.mpr hω)
      simpa only [globalHeckePoleFactor, ite_eq_left hω] using
        mul_ne_zero h₀ (sub_ne_zero.mpr h₁.symm)
    · rw [globalHeckePoleFactor, ite_eq_right hω]
      exact one_ne_zero
  have h := globalHeckePoleFactor_analytic F ω c
  rw [h.meromorphicOrderAt_eq, h.analyticOrderAt_eq_zero.mpr hne]
  rfl

omit [∀ v : Place F, MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : Place F, BorelSpace (v.adicCompletion F)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ] in
private theorem zeta_order_reflect (f : GlobalBruhat F) (c : ℂ) :
    meromorphicOrderAt (Z F ν ω f) c =
      meromorphicOrderAt (Z F ν ω⁻¹ (GlobalBruhat.fourier F f)) (1 - c) := by
  have he : Z F ν ω f = Z F ν ω⁻¹ (GlobalBruhat.fourier F f) ∘ (fun z : ℂ => 1 - z) :=
    funext (globalZetaContinued_compact_functionalEquation F ν f ω)
  rw [he]
  have ha : AnalyticAt ℂ (fun z : ℂ => 1 - z) c := analyticAt_const.sub analyticAt_id
  have hd : deriv (fun z : ℂ => 1 - z) c ≠ 0 := by simp
  exact meromorphicOrderAt_comp_of_deriv_ne_zero ha hd

omit [∀ v : Place F, MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : Place F, BorelSpace (v.adicCompletion F)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ] in
/-- The pointwise minimum of the global zeta orders reflects under the
functional equation and character inversion. -/
theorem globalHeckeOrderReference_reflect (r r' : GlobalBruhat F)
    (hr : ∀ (f : GlobalBruhat F) (z : ℂ),
      meromorphicOrderAt (Z F ν ω r) z ≤ meromorphicOrderAt (Z F ν ω f) z)
    (hr' : ∀ (f : GlobalBruhat F) (z : ℂ),
      meromorphicOrderAt (Z F ν ω⁻¹ r') z ≤ meromorphicOrderAt (Z F ν ω⁻¹ f) z)
    (c : ℂ) :
    meromorphicOrderAt (Z F ν ω r) c = meromorphicOrderAt (Z F ν ω⁻¹ r') (1 - c) := by
  apply le_antisymm
  · have h := zeta_order_reflect F ν ω⁻¹ r' (1 - c)
    rw [inv_inv, sub_sub_cancel] at h
    rw [h]
    exact hr (GlobalBruhat.fourier F r') c
  · rw [zeta_order_reflect F ν ω r c]
    exact hr' (GlobalBruhat.fourier F r) (1 - c)

private abbrev Bergman := SchwartzBergman (univ : Set ℝ)

/-- The undamped continued transform of a pole-free adelic test. -/
def globalPoleFreeZetaBergman (f : GlobalBruhat F)
    (hf : globalZetaPolarVanishes F f (compactIdeleClassCharacter F ω)) : Bergman :=
  ⟨Z F ν ω f, globalZetaContinued_mem_schwartzBergman F ν ω f hf⟩

omit [∀ v : Place F, MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : Place F, BorelSpace (v.adicCompletion F)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ] in
/-- An adelic reference attaining the pointwise minimum gives the divisor
inclusion for every pole-free zeta transform. -/
theorem globalPoleFreeZetaBergman_mem_divisor_of_min (r : GlobalBruhat F)
    (hr : ∀ z, meromorphicOrderAt (Z F ν ω r) z ≠ ⊤)
    (hmin : ∀ (f : GlobalBruhat F) z,
      meromorphicOrderAt (Z F ν ω r) z ≤ meromorphicOrderAt (Z F ν ω f) z)
    (f : GlobalBruhat F)
    (hf : globalZetaPolarVanishes F f (compactIdeleClassCharacter F ω)) :
    globalPoleFreeZetaBergman F ν ω f hf ∈
      bergmanDivisorSubmodule (globalHeckeClearedZeta F ν ω r) := by
  let g := globalHeckeClearedZeta F ν ω r
  have hfinite := globalHeckeClearedZeta_order_ne_top F ν ω r hr
  have hg (z : ℂ) : AnalyticAt ℂ g z := globalHeckeClearedZeta_analytic F ν ω r z
  let p := globalPoleFreeZetaBergman F ν ω f hf
  have hp : Differentiable ℂ p.val := by
    simpa only [preimage_univ, differentiableOn_univ] using p.property.2.1
  have hg' : Differentiable ℂ g := fun z => (hg z).differentiableAt
  exact (bergmanDivisorSubmodule_mem_iff hg' p).mpr ((entire_divisibility_iff_orders hg' hp).mpr (by
    intro z
    by_cases hz : ω ≠ 1 ∨ z ≠ 0 ∧ z ≠ 1
    · apply analyticOrder_le_of_meromorphicOrder_le (hg z) (hp.analyticAt z) (hfinite z)
      change meromorphicOrderAt (globalHeckeClearedZeta F ν ω r) z ≤
        meromorphicOrderAt (Z F ν ω f) z
      rw [globalHeckeClearedZeta_meromorphicOrder, poleFactor_order_zero F ω z hz, zero_add]
      exact hmin f z
    · push Not at hz
      obtain ⟨hω, h⟩ := hz
      subst ω
      have he := trivial_reference_regularized_nonzero F ν r hmin
      rcases eq_or_ne z 0 with rfl | h₀
      · rw [(hg 0).analyticOrderAt_eq_zero.mpr he.1]
        exact bot_le
      · have h₁ := h h₀
        subst z
        rw [(hg 1).analyticOrderAt_eq_zero.mpr he.2]
        exact bot_le))

include μ hν in
/-- One cleared divisor works for all conductor stages. Every actual
pole-free global Mellin transform is in its Schwartz–Bergman divisibility
subspace, and its quotient admits biorthogonal vectors on each strip. -/
theorem exists_globalHeckeDivisor :
    ∃ r : GlobalBruhat F,
      let g := globalHeckeClearedZeta F ν ω r
      (∀ z, analyticOrderAt g z ≠ ⊤) ∧
      (∀ (f : GlobalBruhat F)
        (hf : globalZetaPolarVanishes F f (compactIdeleClassCharacter F ω)),
        globalPoleFreeZetaBergman F ν ω f hf ∈ bergmanDivisorSubmodule g) ∧
      ∀ (a b : ℝ), a ≤ b →
        let I : Set ({z : ℂ // z.re ∈ Icc a b} × ℕ) := {i | (i.2 : ℕ∞) < analyticOrderAt g i.1}
        ∃ J : I → StrongDual ℂ (Bergman ⧸ bergmanDivisorSubmodule g),
          (∀ i p, J i ((bergmanDivisorSubmodule g).mkQ p) =
            bergmanNormalizedJet i.val.1 i.val.2 p) ∧
          Equicontinuous (fun i (p : Bergman ⧸ bergmanDivisorSubmodule g) ↦ J i p) ∧
          IsVonNBounded ℂ (range J) ∧
          ∀ i, ∃ x, ∀ j, J j x = if j = i then 1 else 0 := by
  obtain ⟨r, hr, hmin⟩ := exists_globalHeckeOrderReference F η ν ω μ hν
  let g := globalHeckeClearedZeta F ν ω r
  have hfinite := globalHeckeClearedZeta_order_ne_top F ν ω r hr
  refine ⟨r, hfinite, ?_, fun a b hab => ?_⟩
  · intro f hf
    exact globalPoleFreeZetaBergman_mem_divisor_of_min F ν ω r hr hmin f hf
  · exact bergmanDivisor_quotientJets_biorthogonal g
      (globalHeckeBergmanRepresentative F ν ω r)
      (globalHeckeBergmanRepresentative_order F ν ω r) hfinite a b hab

/-- Translation of the spectral parameter transports entire divisibility
in both directions, with the same translation applied to the divisor. -/
theorem bergmanDivisorSubmodule_shift_mem_iff {g : ℂ → ℂ} (hg : Differentiable ℂ g)
    (d : ℂ) (f : Bergman) :
    schwartzBergmanEntireShift d f ∈ bergmanDivisorSubmodule (fun z ↦ g (z + d)) ↔
      f ∈ bergmanDivisorSubmodule g := by
  have hgd : Differentiable ℂ (fun z ↦ g (z + d)) :=
    hg.comp (differentiable_id.add_const d)
  rw [bergmanDivisorSubmodule_mem_iff hgd, bergmanDivisorSubmodule_mem_iff hg]
  simp only [schwartzBergmanEntireShift_apply]
  constructor
  · rintro ⟨u, hu, he⟩
    refine ⟨fun z ↦ u (z - d), hu.comp (differentiable_id.sub_const d), fun z ↦ ?_⟩
    simpa only [sub_add_cancel] using he (z - d)
  · rintro ⟨u, hu, he⟩
    exact ⟨fun z ↦ u (z + d), hu.comp (differentiable_id.add_const d), fun z ↦ he (z + d)⟩

/-- The spectral shift descends to an isomorphism of the two divisor quotients
with their quotient topologies. -/
theorem exists_bergmanDivisorQuotient_shift {g : ℂ → ℂ} (hg : Differentiable ℂ g) (d : ℂ) :
    let D := bergmanDivisorSubmodule g
    let D' := bergmanDivisorSubmodule (fun z ↦ g (z + d))
    ∃ e : (Bergman ⧸ D) ≃L[ℂ] (Bergman ⧸ D'),
      ∀ f, e (D.mkQ f) = D'.mkQ (schwartzBergmanEntireShift d f) := by
  intro D D'
  let E := schwartzBergmanEntireShift d
  have hmem (f : Bergman) : E f ∈ D' ↔ f ∈ D :=
    bergmanDivisorSubmodule_shift_mem_iff hg d f
  let A := D.liftQL (D'.mkQL.comp E.toContinuousLinearMap) (by
    intro f hf
    change D'.mkQ (E f) = 0
    exact (Submodule.Quotient.mk_eq_zero D').mpr ((hmem f).mpr hf))
  let B := D'.liftQL (D.mkQL.comp E.symm.toContinuousLinearMap) (by
    intro f hf
    change D.mkQ (E.symm f) = 0
    apply (Submodule.Quotient.mk_eq_zero D).mpr
    exact (hmem (E.symm f)).mp (by rwa [E.apply_symm_apply]))
  have hA (f : Bergman) : A (D.mkQ f) = D'.mkQ (E f) := rfl
  have hB (f : Bergman) : B (D'.mkQ f) = D.mkQ (E.symm f) := rfl
  refine ⟨ContinuousLinearEquiv.equivOfInverse A B ?_ ?_, hA⟩
  · intro x
    obtain ⟨f, rfl⟩ := D.mkQ_surjective x
    rw [hA, hB, E.symm_apply_apply]
  · intro x
    obtain ⟨f, rfl⟩ := D'.mkQ_surjective x
    rw [hB, hA, E.apply_symm_apply]

include μ hν in
/-- For the pole-free adelic Mellin image, the spectral shift in (7.4.0.1)
gives a subspace of the translated, closed divisor denominator. Both image
closedness and equality with the divisor subspace are invariant under the shift. -/
theorem exists_globalPoleFreeZetaBergman_shift_comparison :
    ∃ r : GlobalBruhat F, ∀ d : ℂ,
      let g := globalHeckeClearedZeta F ν ω r
      let D := bergmanDivisorSubmodule g
      let D' := bergmanDivisorSubmodule (fun z ↦ g (z + d))
      let ZB := fun f : {f : GlobalBruhat F |
          globalZetaPolarVanishes F f (compactIdeleClassCharacter F ω)} ↦
        globalPoleFreeZetaBergman F ν ω f.val f.property
      IsClosed (D' : Set Bergman) ∧
        range (schwartzBergmanEntireShift d ∘ ZB) ⊆ D' ∧
        (range (schwartzBergmanEntireShift d ∘ ZB) = D' ↔ range ZB = D) ∧
        (IsClosed (range (schwartzBergmanEntireShift d ∘ ZB)) ↔ IsClosed (range ZB)) := by
  obtain ⟨r, _, hr, _⟩ := exists_globalHeckeDivisor F η ν ω μ hν
  refine ⟨r, fun d ↦ ?_⟩
  intro g D D' ZB
  have hg : Differentiable ℂ g := fun z ↦
    (globalHeckeClearedZeta_analytic F ν ω r z).differentiableAt
  let E := schwartzBergmanEntireShift d
  have hmem (f : Bergman) : E f ∈ D' ↔ f ∈ D :=
    bergmanDivisorSubmodule_shift_mem_iff hg d f
  have htrans : E '' (D : Set Bergman) = D' := by
    ext f
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact (hmem u).mpr hu
    · intro hf
      obtain ⟨u, rfl⟩ := E.surjective f
      exact ⟨u, (hmem u).mp hf, rfl⟩
  have hgd : Differentiable ℂ (fun z ↦ g (z + d)) :=
    hg.comp (differentiable_id.add_const d)
  refine ⟨bergmanDivisorSubmodule_isClosed hgd, ?_, ?_, ?_⟩
  · rintro _ ⟨f, rfl⟩
    exact (hmem (ZB f)).mpr (hr f.val f.property)
  · change range (E ∘ ZB) = D' ↔ range ZB = D
    rw [range_comp, ← htrans, E.injective.image_injective.eq_iff]
  · change IsClosed (range (E ∘ ZB)) ↔ IsClosed (range ZB)
    rw [range_comp]
    exact E.toHomeomorph.isClosed_image

end

end Masullo
