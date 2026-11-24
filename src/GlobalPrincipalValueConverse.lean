import GlobalConverseMeromorphic
import SLocalCech

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology TopologicalSpace
open scoped Classical NumberField

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]
private abbrev K := normOneIdeleClass F
private abbrev Place := HeightOneSpectrum (𝓞 F)
private abbrev E (S : Finset (Place F)) := sLocalBruhatImage F S
private abbrev B := SchwartzBergman (univ : Set ℝ)

local instance : MeasurableSpace (K F) := borel _
local instance : BorelSpace (K F) := ⟨rfl⟩
local instance : MeasurableSpace (Idele F) := borel _
local instance : BorelSpace (Idele F) := ⟨rfl⟩

section Adelics

attribute [local instance] sLocalZetaUnfolding_classMeasurable sLocalZetaUnfolding_classBorel
  sLocalZetaUnfolding_idelesMeasurable sLocalZetaUnfolding_idelesBorel

variable (ν : Measure (K F)) [ν.IsHaarMeasure] (η : Measure (Idele F)) [η.IsHaarMeasure]
variable [∀ v : Place F, MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : Place F, BorelSpace (v.adicCompletion F)ˣ]
  (μ : ∀ v : Place F, Measure (v.adicCompletion F)ˣ)
  [∀ v : Place F, (μ v).IsHaarMeasure] [∀ v : Place F, SigmaFinite (μ v)]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]
variable (hν : IsWeilQuotientMeasure (principalIdeles F) η Measure.count (globalClassMeasure F ν))
variable (ω : PontryaginDual (K F))

private abbrev Z (f : GlobalBruhat F) :=
  globalZetaContinued F ν f (compactIdeleClassCharacter F ω) 0
private abbrev P := finiteHeckeOmissionMultiplier F (normOneEulerCharacter F ω)

variable {S : Finset (Place F)}
variable (hs : Surjective (sIdeleClassInclusion F S))
variable (hu : globalNormOneCharacter F ω ∈ (sUnramified F S : Set (QuasiCharacter (IdeleClass F))))

private abbrev phase := sLocalNormOneCharacterOfGlobal F ω S hs hu
private abbrev valEmbedding (S : Finset (Place F)) : S ↪ Place F :=
  ⟨Subtype.val, Subtype.val_injective⟩

omit [∀ v : Place F, MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : Place F, BorelSpace (v.adicCompletion F)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ] in
private theorem stage_selectedMultiplier_eq (W : Finset S) (z : ℂ) :
    sLocalSelectedEulerMultiplier F S (phase F ω hs hu) W z = P F ω (W.map (valEmbedding F S)) z := by
  simp only [sLocalSelectedEulerMultiplier, finiteHeckeOmissionMultiplier, Finset.prod_map]
  apply Finset.prod_congr rfl
  intro v _
  rw [sLocalFiniteWeilMultiplier_eq_heckeFactor_inv F ω S hs hu v z]
  simp only [heckeEulerFactor, inv_inv, valEmbedding, Function.Embedding.coeFn_mk]

include μ hν hs hu in
private theorem stage_globalPV_zeta_germ (W : Finset S) (f : E F S) (c : ℂ) :
    Z F ν ω (globalWeilPrincipalValues F (W.map (valEmbedding F S)) f.val) =ᶠ[𝓝[≠] c]
      fun z ↦ P F ω (W.map (valEmbedding F S)) z * Z F ν ω f.val z := by
  let σ := phase F ω hs hu
  let μ₀ := fun v : S ↦ μ v.val
  let ρ := sLocalZetaProductMeasure F S μ₀ (archimedeanMultiplicativeHaar F)
  letI : ρ.IsHaarMeasure := sLocalZetaProductMeasure_isHaar F S μ₀ (archimedeanMultiplicativeHaar F)
  obtain ⟨ν₀, hHaar, hν₀⟩ := sLocalClassHaar_exists_weil F S ρ
  letI := hHaar
  let g := sLocalWeilPrincipalValues F S W f
  let L (u : E F S) := sLocalProductZetaContinued F S μ₀ σ
    (sLocalRealArchParameters F S σ) (sLocalComplexArchParameters F S σ) u
  have hG : globalWeilPrincipalValues F (W.map (valEmbedding F S)) f.val = g.val :=
    globalWeilPrincipalValues_stage F S W f
  rw [hG]
  obtain ⟨D, _, _, _, hD, hEq, _, _, _⟩ :=
    exists_manuscriptFiniteHeckeOutside_polynomial_strips F (normOneEulerCharacter F ω) S ν η μ hν
  obtain ⟨A, _, hExterior⟩ :=
    globalContinuedMellin_eq_outside_mul_stage F ν η μ hν S ω hs hu hD hEq
  have hLocal : L g =ᶠ[𝓝[≠] c]
      fun z ↦ sLocalSelectedEulerMultiplier F S σ W z * L f z :=
    sLocalWeilPrincipalValues_continued F S μ₀ ν₀ hν₀ σ W f c
  filter_upwards [hExterior g c, hExterior f c, hLocal] with z hg hf hl
  change Z F ν ω g.val z = A * D z * L g z at hg
  change Z F ν ω f.val z = A * D z * L f z at hf
  change L g z = sLocalSelectedEulerMultiplier F S σ W z * L f z at hl
  rw [hg, hf, hl, stage_selectedMultiplier_eq F ω hs hu W z]
  ring

include μ hν in
/-- Applying global Weil principal values multiplies the actual continued
Mellin transform by the selected reciprocal Euler factors, as germs at
every spectral parameter. This includes ramified places and tests on any stage. -/
theorem globalWeilPrincipalValues_zeta_germ (W : Finset (Place F)) (f : GlobalBruhat F) (c : ℂ) :
    Z F ν ω (globalWeilPrincipalValues F W f) =ᶠ[𝓝[≠] c]
      fun z ↦ P F ω W z * Z F ν ω f z := by
  obtain ⟨U, fU, hfU⟩ := globalBruhat_exhausted F f
  obtain ⟨V, hV⟩ := exists_homogeneousThetaPlaceBase F ω
  let T := V ∪ (U ∪ W)
  have hUT : U ⊆ T := Finset.subset_union_left.trans Finset.subset_union_right
  have hWT : W ⊆ T := Finset.subset_union_right.trans Finset.subset_union_right
  obtain ⟨hT, hχ⟩ := hV T Finset.subset_union_left
  let fT := sLocalBruhatTransition F hUT fU
  have hfT : fT.val = f := hfU
  let W' : Finset T := Finset.univ.filter (fun v ↦ v.val ∈ W)
  have hW' : W'.map (valEmbedding F T) = W := by
    ext v
    constructor
    · rintro h
      obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp h
      exact (Finset.mem_filter.mp ha).2
    · intro h
      exact Finset.mem_map.mpr ⟨⟨v, hWT h⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩, rfl⟩
  have h := stage_globalPV_zeta_germ F ν η μ hν ω hT hχ W' fT c
  rw [hW', hfT] at h
  exact h

end Adelics

section EulerDivision

variable (ξ : PontryaginDual (IdeleClass F))
private abbrev eulerFactor (v : Place F) (z : ℂ) :=
  1 - heckeEulerCoefficient F ξ (chosenFiniteUniformizer F) v * (v.asIdeal.absNorm : ℂ) ^ (-z)

private theorem eulerFactor_periodic (v : Place F) :
    ∃ T : ℝ, 0 < T ∧ Periodic (eulerFactor F ξ v) ((T : ℂ) * Complex.I) := by
  let q : ℝ := v.asIdeal.absNorm
  have hq : 1 < q := by dsimp [q]; exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
  have hq₀ : 0 < q := zero_lt_one.trans hq
  have hq' : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq₀.ne'
  have hlog : (Real.log q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.log_pos hq).ne'
  let T := 2 * Real.pi / Real.log q
  have hPow : (q : ℂ) ^ ((T : ℂ) * Complex.I) = 1 := by
    rw [Complex.cpow_def_of_ne_zero hq', ← Complex.ofReal_log hq₀.le]
    have hT : (T : ℂ) = 2 * Real.pi / Real.log q := by simp [T]
    rw [hT, show (Real.log q : ℂ) * (2 * (Real.pi : ℂ) / Real.log q * Complex.I) =
      2 * Real.pi * Complex.I by field_simp]
    exact Complex.exp_two_pi_mul_I
  refine ⟨T, div_pos (by positivity) (Real.log_pos hq), fun z ↦ ?_⟩
  change 1 - _ * (q : ℂ) ^ (-(z + (T : ℂ) * Complex.I)) = 1 - _ * (q : ℂ) ^ (-z)
  rw [neg_add, Complex.cpow_add _ _ hq', Complex.cpow_neg _ ((T : ℂ) * Complex.I), hPow, inv_one, mul_one]

private theorem eulerFactor_at_two_ne_zero (v : Place F) :
    eulerFactor F ξ v 2 ≠ 0 := by
  obtain ⟨a, ha, hA⟩ := finiteHeckeOmissionMultiplier_norm_ge_of_re_ge F ξ {v}
    (a := 2) (by norm_num)
  have hl := hA (2 : ℂ) (by norm_num)
  rw [finiteHeckeOmissionMultiplier, Finset.prod_singleton] at hl
  exact norm_pos_iff.mp (ha.trans_le hl)

/-- Division by a finite reciprocal Euler product preserves all strip
seminorm bounds when the quotient is entire. -/
theorem schwartzBergman_of_finiteHeckeOmission_mul (W : Finset (Place F))
    {g : ℂ → ℂ} (hg : Differentiable ℂ g)
    (hb : (fun z ↦ finiteHeckeOmissionMultiplier F ξ W z * g z) ∈ schwartzBergmanSubmodule univ) :
    g ∈ schwartzBergmanSubmodule univ := by
  induction W using Finset.induction_on with
  | empty => simpa [finiteHeckeOmissionMultiplier] using hb
  | @insert v W hv ih =>
    obtain ⟨T, hT, hP⟩ := eulerFactor_periodic F ξ v
    have hvEq : finiteHeckeOmissionMultiplier F ξ {v} = eulerFactor F ξ v := by
      funext z
      unfold finiteHeckeOmissionMultiplier
      rw [Finset.prod_singleton]
    have hvDiff : Differentiable ℂ (eulerFactor F ξ v) := hvEq ▸
      fun z ↦ (finiteHeckeOmissionMultiplier_analytic F ξ {v} z).differentiableAt
    have hW : Differentiable ℂ (finiteHeckeOmissionMultiplier F ξ W) :=
      fun z ↦ (finiteHeckeOmissionMultiplier_analytic F ξ W z).differentiableAt
    apply ih
    apply schwartzBergman_of_periodic_mul hvDiff ⟨2, eulerFactor_at_two_ne_zero F ξ v⟩ hT hP (hW.mul hg)
    have hEq : (fun z ↦ eulerFactor F ξ v z * (finiteHeckeOmissionMultiplier F ξ W * g) z) =
        fun z ↦ finiteHeckeOmissionMultiplier F ξ (insert v W) z * g z := by
      funext z
      unfold finiteHeckeOmissionMultiplier
      rw [Finset.prod_insert hv]
      simp only [Pi.mul_apply, mul_assoc]
    exact hEq.symm ▸ hb

/-- Multiplication by the selected reciprocal Euler product is continuous on
the entire Schwartz–Bergman space. -/
def finiteHeckeOmissionBergmanMul (W : Finset (Place F)) : B →L[ℂ] B :=
  schwartzBergmanRestrictMul isOpen_univ ordConnected_univ univ_nonempty
    isOpen_univ ordConnected_univ univ_nonempty Subset.rfl
    (finiteHeckeOmissionMultiplier F ξ W)
    (fun z _ ↦ finiteHeckeOmissionMultiplier_analytic F ξ W z) (by
      intro a b _ _
      obtain ⟨C, hC, hB⟩ := finiteHeckeOmissionMultiplier_norm_le F ξ W a
      exact ⟨C, 0, hC, fun z hz ↦ by simpa only [pow_zero, mul_one] using hB z hz.1⟩)

@[simp] theorem finiteHeckeOmissionBergmanMul_apply (W : Finset (Place F)) (b : B) (z : ℂ) :
    (finiteHeckeOmissionBergmanMul F ξ W b).val z = finiteHeckeOmissionMultiplier F ξ W z * b.val z :=
  schwartzBergmanRestrictMul_apply _ _ _ _ _ _ _ _ _ _ _ _ (mem_univ _)

/-- Euler multiplication maps an entire divisor ideal onto the closed
divisibility subspace of the product divisor. -/
theorem finiteHeckeOmissionBergmanMul_divisor_range (W : Finset (Place F))
    {g : ℂ → ℂ} (hg : Differentiable ℂ g) (b : B) :
    (∃ a : B, a ∈ bergmanDivisorSubmodule g ∧ finiteHeckeOmissionBergmanMul F ξ W a = b) ↔
      b ∈ bergmanDivisorSubmodule (fun z ↦ finiteHeckeOmissionMultiplier F ξ W z * g z) := by
  let p := finiteHeckeOmissionMultiplier F ξ W
  have hp : Differentiable ℂ p := fun z ↦ (finiteHeckeOmissionMultiplier_analytic F ξ W z).differentiableAt
  have hd : Differentiable ℂ (fun z ↦ finiteHeckeOmissionMultiplier F ξ W z * g z) := hp.mul hg
  rw [bergmanDivisorSubmodule_mem_iff hd]
  constructor
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨k, hk, he⟩ := (bergmanDivisorSubmodule_mem_iff hg a).mp ha
    refine ⟨k, hk, fun z ↦ ?_⟩
    rw [finiteHeckeOmissionBergmanMul_apply, he z]
    ring
  · rintro ⟨k, hk, he⟩
    have hEq : (fun z ↦ p z * (g z * k z)) = b.val := by
      funext z
      rw [he z]
      ring
    have hB : (fun z ↦ g z * k z) ∈ schwartzBergmanSubmodule univ :=
      schwartzBergman_of_finiteHeckeOmission_mul F ξ W (hg.mul hk) (hEq.symm ▸ b.property)
    let a : B := ⟨fun z ↦ g z * k z, hB⟩
    refine ⟨a, (bergmanDivisorSubmodule_mem_iff hg a).mpr ⟨k, hk, fun _ ↦ rfl⟩,
      Subtype.ext (funext fun z ↦ ?_)⟩
    rw [finiteHeckeOmissionBergmanMul_apply]
    exact congrFun hEq z

/-- Euler multiplication identifies the two divisor ideals topologically.
Both are closed subspaces of the entire Schwartz–Bergman space. -/
theorem exists_finiteHeckeOmission_divisor_equiv (W : Finset (Place F))
    {g : ℂ → ℂ} (hg : Differentiable ℂ g) :
    let p := finiteHeckeOmissionMultiplier F ξ W
    ∃ e : bergmanDivisorSubmodule g ≃L[ℂ] bergmanDivisorSubmodule (fun z ↦ p z * g z),
      ∀ a, (e a).val = finiteHeckeOmissionBergmanMul F ξ W a.val := by
  intro p
  let D := bergmanDivisorSubmodule g
  let N := bergmanDivisorSubmodule (fun z ↦ p z * g z)
  let M := finiteHeckeOmissionBergmanMul F ξ W
  have hp : Differentiable ℂ p := fun z ↦ (finiteHeckeOmissionMultiplier_analytic F ξ W z).differentiableAt
  have hN : IsClosed (N : Set B) := bergmanDivisorSubmodule_isClosed
    (show Differentiable ℂ (fun z ↦ p z * g z) from hp.mul hg)
  let L : D →L[ℂ] N := (M.comp D.subtypeL).codRestrict N
    fun a ↦ (finiteHeckeOmissionBergmanMul_divisor_range F ξ W hg _).mp ⟨a.val, a.property, rfl⟩
  have hsur : Surjective L := by
    intro b
    obtain ⟨a, ha, he⟩ := (finiteHeckeOmissionBergmanMul_divisor_range F ξ W hg b.val).mpr b.property
    exact ⟨⟨a, ha⟩, Subtype.ext he⟩
  have hinj : Injective L := by
    intro a b he
    have he' : M a.val = M b.val := congrArg Subtype.val he
    have hDiff (u : B) : Differentiable ℂ u.val := by
      simpa only [preimage_univ, differentiableOn_univ] using u.property.2.1
    have ha : AnalyticOnNhd ℂ a.val.val univ := fun z _ ↦ (hDiff a.val).analyticAt z
    have hb : AnalyticOnNhd ℂ b.val.val univ := fun z _ ↦ (hDiff b.val).analyticAt z
    obtain ⟨C, hC, hLow⟩ := finiteHeckeOmissionMultiplier_norm_ge_of_re_ge F ξ W
      (a := 1) (by norm_num)
    have h₂ : (2 : ℂ) ∈ {z : ℂ | 1 < z.re} := by norm_num
    have hNear : ∀ᶠ z in 𝓝 (2 : ℂ), 1 < z.re :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds h₂
    have hGerm : a.val.val =ᶠ[𝓝 (2 : ℂ)] b.val.val := by
      filter_upwards [hNear] with z hz
      have hv := congrArg (fun u : B ↦ u.val z) he'
      change (finiteHeckeOmissionBergmanMul F ξ W a.val).val z =
        (finiteHeckeOmissionBergmanMul F ξ W b.val).val z at hv
      rw [finiteHeckeOmissionBergmanMul_apply, finiteHeckeOmissionBergmanMul_apply] at hv
      exact mul_left_cancel₀ (norm_pos_iff.mp (hC.trans_le (hLow z hz.le))) hv
    exact Subtype.ext (Subtype.ext (funext fun z ↦
      ha.eqOn_of_preconnected_of_eventuallyEq hb isPreconnected_univ (mem_univ _) hGerm (mem_univ z)))
  have hOpen : IsOpenMap L := by
    have hB := schwartzBergman_frechet (univ : Set ℝ) isOpen_univ ordConnected_univ univ_nonempty
    obtain ⟨hDa,hDp,hDm,hDc⟩ := isFrechetTVS_closedSubmodule hB D (bergmanDivisorSubmodule_isClosed hg)
    obtain ⟨hNa,hNp,hNm,hNc⟩ := isFrechetTVS_closedSubmodule hB N hN
    letI : UniformSpace D := IsTopologicalAddGroup.rightUniformSpace _
    letI : CompleteSpace D := hDc
    letI : MetrizableSpace D := hDm
    letI : PolynormableSpace ℂ D := hDp
    letI : ContinuousSMul ℂ D := (PolynormableSpace.withSeminorms ℂ D).continuousSMul
    letI : UniformSpace N := IsTopologicalAddGroup.rightUniformSpace _
    letI : IsUniformAddGroup N := isUniformAddGroup_of_addCommGroup
    letI : CompleteSpace N := hNc
    letI : MetrizableSpace N := hNm
    letI : PolynormableSpace ℂ N := hNp
    letI : ContinuousSMul ℂ N := (PolynormableSpace.withSeminorms ℂ N).continuousSMul
    letI : (uniformity N).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
    letI : BaireSpace N := BaireSpace.of_completelyPseudoMetrizable
    exact isOpenMap_of_surjective_complete_baire L hsur
  let e := LinearEquiv.ofBijective L.toLinearMap ⟨hinj, hsur⟩
  let E := e.toEquiv.toHomeomorphOfContinuousOpen L.continuous hOpen
  exact ⟨⟨e, E.continuous_toFun, E.symm.continuous_toFun⟩, fun _ ↦ rfl⟩

end EulerDivision

section GlobalRange

variable (ν : Measure (K F)) [ν.IsHaarMeasure] (η : Measure (Idele F)) [η.IsHaarMeasure]
variable [∀ v : Place F, MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : Place F, BorelSpace (v.adicCompletion F)ˣ]
  (μ : ∀ v : Place F, Measure (v.adicCompletion F)ˣ)
  [∀ v : Place F, (μ v).IsHaarMeasure] [∀ v : Place F, SigmaFinite (μ v)]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]
variable (hν : IsWeilQuotientMeasure (principalIdeles F) η Measure.count (globalClassMeasure F ν))
variable (ω : PontryaginDual (K F))

private abbrev G (f : GlobalBruhat F) := globalHeckeClearedZeta F ν ω f

include μ hν in
/-- Euler multiplication also holds for the entire representatives after
clearing the two possible global poles, including at their centers. -/
theorem globalWeilPrincipalValues_clearedZeta_eq_mul (W : Finset (Place F)) (f : GlobalBruhat F) :
    G F ν ω (globalWeilPrincipalValues F W f) =
      fun z ↦ P F ω W z * G F ν ω f z := by
  have hG (u : GlobalBruhat F) : Continuous (G F ν ω u) :=
    (show Differentiable ℂ (G F ν ω u) from fun z ↦
      (globalHeckeClearedZeta_analytic F ν ω u z).differentiableAt).continuous
  have hP : Continuous (P F ω W) :=
    (show Differentiable ℂ (P F ω W) from fun z ↦
      (finiteHeckeOmissionMultiplier_analytic F (normOneEulerCharacter F ω) W z).differentiableAt).continuous
  funext c
  apply (((hG _).continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
    (hP.mul (hG f)).continuousAt).mp ?_).eq_of_nhds
  have hne (a : ℂ) : ∀ᶠ z in 𝓝[≠] c, z ≠ a := by
    rcases eq_or_ne c a with rfl | h
    · exact self_mem_nhdsWithin
    · exact eventually_ne_nhdsWithin h
  filter_upwards [hne 0, hne 1, globalWeilPrincipalValues_zeta_germ F ν η μ hν ω W f c]
    with z hz₀ hz₁ h
  change Z F ν ω (globalWeilPrincipalValues F W f) z = P F ω W z * Z F ν ω f z at h
  change G F ν ω (globalWeilPrincipalValues F W f) z = P F ω W z * G F ν ω f z
  simp only [G, globalHeckeClearedZeta_eq F ν ω _ z hz₀ hz₁]
  change globalHeckePoleFactor F ω z * Z F ν ω (globalWeilPrincipalValues F W f) z =
    P F ω W z * (globalHeckePoleFactor F ω z * Z F ν ω f z)
  rw [h]
  ring

include μ hν in
theorem globalPV_polarEvaluation_eq_zero (W : Finset (Place F)) (f : GlobalBruhat F)
    (hf : GlobalBruhat.polarEvaluation F f = 0) :
    GlobalBruhat.polarEvaluation F (globalWeilPrincipalValues F W f) = 0 := by
  let g := globalWeilPrincipalValues F W f
  have hd : Differentiable ℂ (Z F ν 1 f) := by
    have hp := (globalZetaPolarVanishes_compact_iff F f 1).mpr
      (Or.inr ⟨congrArg Prod.fst hf, congrArg Prod.snd hf⟩)
    have hb := globalZetaContinued_mem_schwartzBergman F ν 1 f hp
    simpa only [preimage_univ, differentiableOn_univ] using hb.2.1
  have hn (c : ℂ) : 0 ≤ meromorphicOrderAt (Z F ν 1 g) c := by
    rw [meromorphicOrderAt_congr (globalWeilPrincipalValues_zeta_germ F ν η μ hν 1 W f c)]
    exact ((finiteHeckeOmissionMultiplier_analytic F (normOneEulerCharacter F 1) W c).mul
      (hd.analyticAt c)).meromorphicOrderAt_nonneg
  exact ((globalMellin_nonneg_orders_iff F 1 ν g).mp ⟨hn 0, hn 1⟩).resolve_left (not_not_intro rfl)

include μ hν in
theorem globalPV_polarFree_zeta_eq_mul (W : Finset (Place F)) (f : GlobalBruhat F)
    (hf : GlobalBruhat.polarEvaluation F f = 0) :
    Z F ν ω (globalWeilPrincipalValues F W f) = fun z ↦ P F ω W z * Z F ν ω f z := by
  have hb (u : GlobalBruhat F) (hu : GlobalBruhat.polarEvaluation F u = 0) : Continuous (Z F ν ω u) := by
    have hp := (globalZetaPolarVanishes_compact_iff F u ω).mpr
      (Or.inr ⟨congrArg Prod.fst hu, congrArg Prod.snd hu⟩)
    have h := globalZetaContinued_mem_schwartzBergman F ν ω u hp
    have hd : Differentiable ℂ (Z F ν ω u) := by
      simpa only [preimage_univ, differentiableOn_univ] using h.2.1
    exact hd.continuous
  have hP : Continuous (P F ω W) :=
    (show Differentiable ℂ (P F ω W) from fun z ↦
      (finiteHeckeOmissionMultiplier_analytic F (normOneEulerCharacter F ω) W z).differentiableAt).continuous
  funext c
  have hC : ContinuousAt (Z F ν ω (globalWeilPrincipalValues F W f)) c :=
    (hb _ (globalPV_polarEvaluation_eq_zero F ν η μ hν W f hf)).continuousAt
  exact ((hC.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE (hP.mul (hb f hf)).continuousAt).mp
    (globalWeilPrincipalValues_zeta_germ F ν η μ hν ω W f c)).eq_of_nhds

include μ hν in
/-- The actual polar-free principal-value Mellin transforms fill exactly the
closed ideal obtained by multiplying the Hecke divisor by the selected factors. -/
theorem globalPV_polarFree_divisor_range_of_min (r : GlobalBruhat F)
    (hr : ∀ z, meromorphicOrderAt (Z F ν ω r) z ≠ ⊤)
    (hmin : ∀ f : GlobalBruhat F, ∀ z,
      meromorphicOrderAt (Z F ν ω r) z ≤ meromorphicOrderAt (Z F ν ω f) z)
    (W : Finset (Place F)) (b : B) :
    b ∈ bergmanDivisorSubmodule (fun z ↦ P F ω W z * G F ν ω r z) ↔
      ∃ f : GlobalBruhat F, GlobalBruhat.polarEvaluation F f = 0 ∧
        Z F ν ω (globalWeilPrincipalValues F W f) = b.val := by
  have hD : Differentiable ℂ (G F ν ω r) := fun z ↦
    (globalHeckeClearedZeta_analytic F ν ω r z).differentiableAt
  rw [← finiteHeckeOmissionBergmanMul_divisor_range F (normOneEulerCharacter F ω) W hD b]
  have hRange := globalConverse_polarFree_range_of_min F ν η hν μ ω r hr hmin
  constructor
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨f, hf, he⟩ := (hRange a).mp ha
    refine ⟨f, hf, funext fun z ↦ ?_⟩
    have he' : Z F ν ω f = a.val := he
    rw [globalPV_polarFree_zeta_eq_mul F ν η μ hν ω W f hf, finiteHeckeOmissionBergmanMul_apply]
    change P F ω W z * Z F ν ω f z = P F ω W z * a.val z
    rw [he']
  · rintro ⟨f, hf, he⟩
    have hp := (globalZetaPolarVanishes_compact_iff F f ω).mpr
      (Or.inr ⟨congrArg Prod.fst hf, congrArg Prod.snd hf⟩)
    let a := globalPoleFreeZetaBergman F ν ω f hp
    refine ⟨a, (hRange a).mpr ⟨f, hf, rfl⟩, Subtype.ext (funext fun z ↦ ?_)⟩
    rw [finiteHeckeOmissionBergmanMul_apply, ← he, globalPV_polarFree_zeta_eq_mul F ν η μ hν ω W f hf]
    rfl

include μ hν in
/-- After the two global poles are cleared, the full trivial principal-value
Mellin image is the selected Euler product times the ordinary divisor ideal. -/
theorem globalPV_trivial_cleared_divisor_range_of_min (r : GlobalBruhat F)
    (hr : ∀ z, meromorphicOrderAt (Z F ν 1 r) z ≠ ⊤)
    (hmin : ∀ f : GlobalBruhat F, ∀ z,
      meromorphicOrderAt (Z F ν 1 r) z ≤ meromorphicOrderAt (Z F ν 1 f) z)
    (W : Finset (Place F)) (b : B) :
    b ∈ bergmanDivisorSubmodule (fun z ↦ P F 1 W z * G F ν 1 r z) ↔
      ∃ f : GlobalBruhat F, G F ν 1 (globalWeilPrincipalValues F W f) = b.val := by
  have hD : Differentiable ℂ (G F ν 1 r) := fun z ↦
    (globalHeckeClearedZeta_analytic F ν 1 r z).differentiableAt
  rw [← finiteHeckeOmissionBergmanMul_divisor_range F (normOneEulerCharacter F 1) W hD b]
  have hPolar := globalConverse_polarFree_range_of_min F ν η hν μ 1 r hr hmin
  have hRange := globalTrivialClearedZeta_range_of_min F ν η hν r hr hmin (fun a ↦ (hPolar a).mp)
  constructor
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨f, he⟩ := (hRange a).mp ha
    have he' : G F ν 1 f = a.val := he
    refine ⟨f, funext fun z ↦ ?_⟩
    rw [globalWeilPrincipalValues_clearedZeta_eq_mul F ν η μ hν 1 W f,
      finiteHeckeOmissionBergmanMul_apply]
    change P F 1 W z * G F ν 1 f z = P F 1 W z * a.val z
    rw [he']
  · rintro ⟨f, he⟩
    let a : B := ⟨G F ν 1 f, globalTrivialClearedZeta_mem_schwartzBergman F ν η hν f⟩
    refine ⟨a, (hRange a).mpr ⟨f, rfl⟩, Subtype.ext (funext fun z ↦ ?_)⟩
    rw [finiteHeckeOmissionBergmanMul_apply, ← he,
      globalWeilPrincipalValues_clearedZeta_eq_mul F ν η μ hν 1 W f]

omit [∀ v : Place F, MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : Place F, BorelSpace (v.adicCompletion F)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ] in
theorem globalPV_trivial_multiplier_zero (W : Finset (Place F)) (hW : W.Nonempty) :
    P F 1 W 0 = 0 := by
  obtain ⟨v, hv⟩ := hW
  unfold P finiteHeckeOmissionMultiplier
  apply Finset.prod_eq_zero hv
  have hχ (q : IdeleClass F) : normOneEulerCharacter F 1 q = 1 := rfl
  have hu : unramifiedFiniteCharacter F (normOneEulerCharacter F 1) v := fun _ _ ↦ hχ _
  change 1 - heckeEulerCoefficient F (normOneEulerCharacter F 1) (chosenFiniteUniformizer F) v *
    (v.asIdeal.absNorm : ℂ) ^ (-(0 : ℂ)) = 0
  simp only [heckeEulerCoefficient, ite_eq_left hu, hχ, Circle.coe_one, neg_zero, Complex.cpow_zero,
    mul_one, sub_self]

include μ hν in
/-- Every nonempty principal-value selection kills the first ordinary
residue on the trivial component. The ordinary residue pair on this image
therefore cannot be surjective onto two independent coordinates. -/
theorem globalPV_trivial_first_residue_zero (W : Finset (Place F)) (hW : W.Nonempty)
    (f : GlobalBruhat F) :
    Tendsto (fun z ↦ z * Z F ν 1 (globalWeilPrincipalValues F W f) z)
      (𝓝[≠] (0 : ℂ)) (𝓝 0) := by
  have hp : Tendsto (P F 1 W) (𝓝[≠] (0 : ℂ)) (𝓝 0) := by
    have ht : Tendsto (P F 1 W) (𝓝 (0 : ℂ)) (𝓝 (P F 1 W 0)) :=
      (finiteHeckeOmissionMultiplier_analytic F (normOneEulerCharacter F 1) W 0).continuousAt.tendsto
    rw [globalPV_trivial_multiplier_zero F W hW] at ht
    exact ht.mono_left nhdsWithin_le_nhds
  have h := hp.mul (globalZetaContinued_trivial_residues F ν f).1
  simp only [zero_mul] at h
  apply h.congr'
  filter_upwards [globalWeilPrincipalValues_zeta_germ F ν η μ hν 1 W f 0] with z hz
  change Z F ν 1 (globalWeilPrincipalValues F W f) z = P F 1 W z * Z F ν 1 f z at hz
  change P F 1 W z * (z * Z F ν 1 f z) = z * Z F ν 1 (globalWeilPrincipalValues F W f) z
  rw [hz]
  ring

include μ hν in
/-- Dividing the Mellin germ by the selected Euler factors recovers the
original continued transform and hence both residue coordinates. -/
theorem globalPV_divide_euler_germ (W : Finset (Place F)) (f : GlobalBruhat F) (c : ℂ) :
    (fun z ↦ Z F ν ω (globalWeilPrincipalValues F W f) z / P F ω W z) =ᶠ[𝓝[≠] c] Z F ν ω f := by
  have ha : AnalyticOnNhd ℂ (P F ω W) univ :=
    fun z _ ↦ finiteHeckeOmissionMultiplier_analytic F (normOneEulerCharacter F ω) W z
  obtain ⟨a, ha₀, hA⟩ := finiteHeckeOmissionMultiplier_norm_ge_of_re_ge F (normOneEulerCharacter F ω) W
    (a := 2) (by norm_num)
  have h₀ : P F ω W 2 ≠ 0 := norm_pos_iff.mp (ha₀.trans_le (hA 2 (by norm_num)))
  have hDisc := (ha.eqOn_zero_or_eventually_ne_zero_of_preconnected isPreconnected_univ).resolve_left
    (fun he ↦ h₀ (he (mem_univ _)))
  have hn : ∀ᶠ z in 𝓝[≠] c, P F ω W z ≠ 0 := by
    change {z | P F ω W z ≠ 0} ∈ 𝓝[≠] c
    simpa only [compl_univ, union_empty] using
      (mem_codiscreteWithin_iff_forall_mem_nhdsNE.mp hDisc) c (mem_univ _)
  filter_upwards [globalWeilPrincipalValues_zeta_germ F ν η μ hν ω W f c, hn] with z hz hp
  change Z F ν ω (globalWeilPrincipalValues F W f) z = P F ω W z * Z F ν ω f z at hz
  rw [hz, mul_comm, mul_div_cancel_right₀ _ hp]

include μ hν in
theorem globalPV_trivial_recovered_residues (W : Finset (Place F)) (f : GlobalBruhat F) :
    let V (z : ℂ) := Z F ν 1 (globalWeilPrincipalValues F W f) z / P F 1 W z
    Tendsto (fun z ↦ z * V z) (𝓝[≠] (0 : ℂ))
      (𝓝 (-((ν.real univ : ℂ) * (GlobalBruhat.polarEvaluation F f).1))) ∧
    Tendsto (fun z ↦ (z - 1) * V z) (𝓝[≠] (1 : ℂ))
      (𝓝 ((ν.real univ : ℂ) * (GlobalBruhat.polarEvaluation F f).2)) := by
  intro V
  have hr := globalZetaContinued_trivial_residues F ν f
  exact ⟨hr.1.congr' ((globalPV_divide_euler_germ F ν η μ hν 1 W f 0).symm.mono
    (fun z h ↦ congrArg (z * ·) h)),
    hr.2.congr' ((globalPV_divide_euler_germ F ν η μ hν 1 W f 1).symm.mono
      (fun z h ↦ congrArg ((z - 1) * ·) h))⟩

include μ hν in
theorem globalPV_zeta_eq_mul_right (W : Finset (Place F)) (f : GlobalBruhat F)
    (z : ℂ) (hz : 1 < z.re) :
    Z F ν ω (globalWeilPrincipalValues F W f) z = P F ω W z * Z F ν ω f z := by
  have h₀ : z ≠ 0 := fun h ↦ by rw [h] at hz; norm_num at hz
  have h₁ : z ≠ 1 := fun h ↦ by rw [h] at hz; norm_num at hz
  have an (u : GlobalBruhat F) : AnalyticAt ℂ (Z F ν ω u) z :=
    globalZetaContinued_analyticAt F ν u _ (compactIdeleClassCharacter_unitary F ω) 0 z
      (by simpa only [add_zero] using h₀) (by simpa only [add_zero] using sub_ne_zero.mpr h₁)
  have hp := finiteHeckeOmissionMultiplier_analytic F (normOneEulerCharacter F ω) W z
  exact (((an _).continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
    (hp.mul (an f)).continuousAt).mp (globalWeilPrincipalValues_zeta_germ F ν η μ hν ω W f z)).eq_of_nhds

private abbrev H := globalIdelicZetaComponentKernel F η ω
private abbrev Q := GlobalBruhat F ⧸ H F η ω

include μ hν in
/-- The actual global principal-value operator descends continuously to
each homogeneous adelic theta quotient. -/
def globalHomogeneousPrincipalValues (W : Finset (Place F)) : Q F η ω →L[ℂ] Q F η ω :=
  (H F η ω).liftQL ((H F η ω).mkQL.comp (globalWeilPrincipalValues F W)) (by
    intro f hf
    change (H F η ω).mkQ (globalWeilPrincipalValues F W f) = 0
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    apply (mem_globalIdelicZetaComponentKernel F η ν hν ω _).mpr
    apply globalZetaContinued_zero_of_halfPlane
    intro z hz
    change Z F ν ω (globalWeilPrincipalValues F W f) z = 0
    have hZero : Z F ν ω f z = 0 := (mem_globalIdelicZetaComponentKernel F η ν hν ω f).mp hf z
    rw [globalPV_zeta_eq_mul_right F ν η μ hν ω W f z hz, hZero, mul_zero])

@[simp] theorem globalHomogeneousPrincipalValues_mk (W : Finset (Place F)) (f : GlobalBruhat F) :
    globalHomogeneousPrincipalValues F ν η μ hν ω W ((H F η ω).mkQ f) =
      (H F η ω).mkQ (globalWeilPrincipalValues F W f) := rfl

theorem globalHomogeneousPrincipalValues_injective (W : Finset (Place F)) :
    Injective (globalHomogeneousPrincipalValues F ν η μ hν ω W) := by
  change Injective (globalHomogeneousPrincipalValues F ν η μ hν ω W).toLinearMap
  apply LinearMap.ker_eq_bot.mp
  apply eq_bot_iff.mpr
  intro x hx
  obtain ⟨f, rfl⟩ := (H F η ω).mkQ_surjective x
  have hfx : globalHomogeneousPrincipalValues F ν η μ hν ω W ((H F η ω).mkQ f) = 0 := hx
  rw [globalHomogeneousPrincipalValues_mk] at hfx
  have hf := (mem_globalIdelicZetaComponentKernel F η ν hν ω _).mp
    ((Submodule.Quotient.mk_eq_zero (H F η ω)).mp hfx)
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  apply (mem_globalIdelicZetaComponentKernel F η ν hν ω _).mpr
  apply globalZetaContinued_zero_of_halfPlane
  intro z hz
  have hz' : P F ω W z * Z F ν ω f z = 0 :=
    (globalPV_zeta_eq_mul_right F ν η μ hν ω W f z hz).symm.trans (hf z)
  obtain ⟨a, ha, hlow⟩ := finiteHeckeOmissionMultiplier_norm_ge_of_re_ge F (normOneEulerCharacter F ω) W
    (a := 1) zero_lt_one
  exact (mul_eq_zero.mp hz').resolve_left (norm_pos_iff.mp (ha.trans_le (hlow z hz.le)))

include μ hν in
/-- On polar-free classes the actual principal-value Mellin map is a
continuous linear equivalence onto the closed selected Euler divisor ideal. -/
theorem exists_globalPV_polarFree_equiv_of_min (r : GlobalBruhat F)
    (hr : ∀ z, meromorphicOrderAt (Z F ν ω r) z ≠ ⊤)
    (hmin : ∀ f : GlobalBruhat F, ∀ z,
      meromorphicOrderAt (Z F ν ω r) z ≤ meromorphicOrderAt (Z F ν ω f) z)
    (W : Finset (Place F)) :
    let A := (GlobalBruhat.polarEvaluation F).ker
    let X := A.map (H F η ω).mkQ
    ∃ e : X ≃L[ℂ] bergmanDivisorSubmodule (fun z ↦ P F ω W z * G F ν ω r z),
      ∀ f : A, ∀ z : ℂ,
        (e (globalPolarFreeTestClass F η ω f)).val.val z =
          Z F ν ω (globalWeilPrincipalValues F W f.val) z := by
  intro A X
  have hRange := globalConverse_polarFree_range_of_min F ν η hν μ ω r hr hmin
  obtain ⟨e, he⟩ := globalPolarFreeMellin_equiv_of_range F ν η hν ω r hRange
  have hG : Differentiable ℂ (G F ν ω r) :=
    fun z ↦ (globalHeckeClearedZeta_analytic F ν ω r z).differentiableAt
  obtain ⟨m, hm⟩ := exists_finiteHeckeOmission_divisor_equiv F (normOneEulerCharacter F ω) W hG
  refine ⟨e.trans m, fun f z ↦ ?_⟩
  change (m (e (globalPolarFreeTestClass F η ω f))).val.val z = _
  rw [hm, finiteHeckeOmissionBergmanMul_apply, he, globalPolarFreeMellin_val,
    globalPV_polarFree_zeta_eq_mul F ν η μ hν ω W f.val f.property]
  have h := globalQuotientMellinFunction_mk F ν η hν ω f.val
  exact congrArg (fun k : ℂ → ℂ ↦ P F ω W z * k z) h

include μ hν in
/-- The principal-value map on polar-free homogeneous classes is a closed
embedding into the actual homogeneous theta quotient. -/
theorem globalHomogeneousPrincipalValues_polarFree_isClosedEmbedding
    (W : Finset (Place F)) :
    let X := (GlobalBruhat.polarEvaluation F).ker.map (H F η ω).mkQ
    IsClosedEmbedding ((globalHomogeneousPrincipalValues F ν η μ hν ω W).comp X.subtypeL) := by
  intro X
  let T : X →L[ℂ] Q F η ω := (globalHomogeneousPrincipalValues F ν η μ hν ω W).comp X.subtypeL
  let R : X →L[ℂ] X := T.codRestrict X (by
    intro x
    obtain ⟨f, hf, he⟩ := Submodule.mem_map.mp x.property
    change globalHomogeneousPrincipalValues F ν η μ hν ω W x.val ∈ X
    rw [← he, globalHomogeneousPrincipalValues_mk]
    exact Submodule.mem_map.mpr ⟨_, globalPV_polarEvaluation_eq_zero F ν η μ hν W f hf, rfl⟩)
  obtain ⟨r, hr, hmin⟩ := exists_globalHeckeOrderReference F η ν ω μ hν
  have hRange := globalConverse_polarFree_range_of_min F ν η hν μ ω r hr hmin
  obtain ⟨e, he⟩ := globalPolarFreeMellin_equiv_of_range F ν η hν ω r hRange
  obtain ⟨m, hm⟩ := exists_globalPV_polarFree_equiv_of_min F ν η μ hν ω r hr hmin W
  let L : X →L[ℂ] B := globalPolarFreeMellin F ν η hν ω
  have hL : IsEmbedding L := by
    have hEq : (L : X → B) = Subtype.val ∘ e := funext fun x ↦ (he x).symm
    rw [hEq]
    exact IsEmbedding.subtypeVal.comp e.toHomeomorph.isEmbedding
  have hComp : (L : X → B) ∘ R = Subtype.val ∘ m := by
    funext x
    obtain ⟨f, hf, hx⟩ := Submodule.mem_map.mp x.property
    let f₀ : (GlobalBruhat.polarEvaluation F).ker := ⟨f, hf⟩
    have hx' : x = globalPolarFreeTestClass F η ω f₀ := Subtype.ext hx.symm
    rw [hx']
    apply Subtype.ext
    funext z
    have hm' := hm f₀ z
    change (L (R (globalPolarFreeTestClass F η ω f₀))).val z = _
    change (globalPolarFreeMellin F ν η hν ω (R (globalPolarFreeTestClass F η ω f₀))).val z = _
    rw [globalPolarFreeMellin_val]
    change globalQuotientMellinFunction F ν η hν ω
      (globalHomogeneousPrincipalValues F ν η μ hν ω W ((H F η ω).mkQ f)) z = _
    rw [globalHomogeneousPrincipalValues_mk, globalQuotientMellinFunction_mk]
    exact hm'.symm
  have hG : Differentiable ℂ (G F ν ω r) :=
    fun z ↦ (globalHeckeClearedZeta_analytic F ν ω r z).differentiableAt
  have hp : Differentiable ℂ (P F ω W) :=
    fun z ↦ (finiteHeckeOmissionMultiplier_analytic F (normOneEulerCharacter F ω) W z).differentiableAt
  have hN : IsClosed (bergmanDivisorSubmodule (fun z ↦ P F ω W z * G F ν ω r z) : Set B) :=
    bergmanDivisorSubmodule_isClosed (show Differentiable ℂ (fun z ↦ P F ω W z * G F ν ω r z) from hp.mul hG)
  have hLR : IsClosedEmbedding ((L : X → B) ∘ R) := by
    rw [hComp]
    exact hN.isClosedEmbedding_subtypeVal.comp m.toHomeomorph.isHomeomorph.isClosedEmbedding
  exact (globalPolarFreeQuotient_isClosed F ν η hν ω).isClosedEmbedding_subtypeVal.comp
    (IsClosedEmbedding.of_comp hL hLR)

include μ hν in
/-- The actual principal-value endomorphism of every global homogeneous
theta quotient is a closed embedding. -/
theorem globalHomogeneousPrincipalValues_isClosedEmbedding (W : Finset (Place F)) :
    IsClosedEmbedding (globalHomogeneousPrincipalValues F ν η μ hν ω W) := by
  let V := globalHomogeneousPrincipalValues F ν η μ hν ω W
  let X := (GlobalBruhat.polarEvaluation F).ker.map (H F η ω).mkQ
  let Y := V.toLinearMap.range
  have hQ : IsFrechetTVS (Q F η ω) := (globalHomogeneousTheta_nuclearFrechet F ω η).1
  letI : MetrizableSpace (Q F η ω) := hQ.2.2.1
  have hX : (X.map V.toLinearMap : Set (Q F η ω)) = range (V.comp X.subtypeL) := by
    ext q
    constructor
    · intro h
      obtain ⟨x, hx, he⟩ := Submodule.mem_map.mp h
      exact ⟨⟨x, hx⟩, he⟩
    · rintro ⟨x, hx⟩
      exact Submodule.mem_map.mpr ⟨x.val, x.property, hx⟩
  have hXV : IsClosed (X.map V.toLinearMap : Set (Q F η ω)) := hX.symm ▸
    (globalHomogeneousPrincipalValues_polarFree_isClosedEmbedding F ν η μ hν ω W).isClosed_range
  have hk : H F η ω = (globalHomogeneousThetaOperator F ν ω).ker :=
    globalIdelicZetaComponentKernel_eq_homogeneous F ν η hν ω
  have hY : IsClosed (Y : Set (Q F η ω)) := by
    by_cases ht : ω = 1
    · subst ω
      have he := globalHomogeneousTheta_trivial_residue_exact F ν
      rw [← hk] at he
      obtain ⟨R, _, hR, _, _, _⟩ := he
      have hXker : R.toLinearMap.ker = X := hR
      letI : X.CoFG := hXker ▸ Submodule.CoFG.ker R.toLinearMap
      exact LinearMap.isClosed_range_of_isClosed_map_of_finiteDimensional_quotient hXV
    · have he := globalPolarFree_image_eq_top_of_ne_one F ν ω ht
      rw [← hk] at he
      have htop : X = ⊤ := he
      rw [htop, Submodule.map_top] at hXV
      exact hXV
  let L : Q F η ω →L[ℂ] Y := V.rangeRestrict
  have hSur : Surjective L := V.toLinearMap.surjective_rangeRestrict
  have hInj : Injective L := fun _ _ h ↦ globalHomogeneousPrincipalValues_injective F ν η μ hν ω W
    (congrArg Subtype.val h)
  have hOpen : IsOpenMap L := by
    obtain ⟨hYa, hYp, hYm, hYc⟩ := isFrechetTVS_closedSubmodule hQ Y hY
    obtain ⟨hQa, hQp, hQm, hQc⟩ := hQ
    letI : UniformSpace (Q F η ω) := IsTopologicalAddGroup.rightUniformSpace _
    letI : CompleteSpace (Q F η ω) := hQc
    letI : PolynormableSpace ℂ (Q F η ω) := hQp
    letI : ContinuousSMul ℂ (Q F η ω) := (PolynormableSpace.withSeminorms ℂ (Q F η ω)).continuousSMul
    letI : UniformSpace Y := IsTopologicalAddGroup.rightUniformSpace _
    letI : IsUniformAddGroup Y := isUniformAddGroup_of_addCommGroup
    letI : CompleteSpace Y := hYc
    letI : MetrizableSpace Y := hYm
    letI : PolynormableSpace ℂ Y := hYp
    letI : ContinuousSMul ℂ Y := (PolynormableSpace.withSeminorms ℂ Y).continuousSMul
    letI : (uniformity Y).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
    letI : BaireSpace Y := BaireSpace.of_completelyPseudoMetrizable
    exact isOpenMap_of_surjective_complete_baire L hSur
  exact ⟨IsEmbedding.subtypeVal.comp
    (IsOpenEmbedding.of_continuous_injective_isOpenMap L.continuous hInj hOpen).isEmbedding, hY⟩

end GlobalRange

#print axioms globalWeilPrincipalValues_zeta_germ
#print axioms schwartzBergman_of_finiteHeckeOmission_mul
#print axioms finiteHeckeOmissionBergmanMul_divisor_range
#print axioms exists_finiteHeckeOmission_divisor_equiv
#print axioms globalWeilPrincipalValues_clearedZeta_eq_mul
#print axioms globalPV_polarFree_divisor_range_of_min
#print axioms globalPV_trivial_cleared_divisor_range_of_min
#print axioms globalPV_trivial_first_residue_zero
#print axioms globalPV_trivial_recovered_residues
#print axioms globalHomogeneousPrincipalValues_injective
#print axioms exists_globalPV_polarFree_equiv_of_min
#print axioms globalHomogeneousPrincipalValues_polarFree_isClosedEmbedding
#print axioms globalHomogeneousPrincipalValues_isClosedEmbedding

end

end Masullo
