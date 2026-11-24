import GlobalCoprimeInterpolation
import FiniteHeckeReciprocal
import GlobalHeckeZeroLine
import StrictLimitQuotients

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology TopologicalSpace
open scoped Classical NumberField

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]
private abbrev K := normOneIdeleClass F
private abbrev Place := HeightOneSpectrum (𝓞 F)
private abbrev B := SchwartzBergman (univ : Set ℝ)

local instance : MeasurableSpace (K F) := borel _
local instance : BorelSpace (K F) := ⟨rfl⟩
local instance : MeasurableSpace (Idele F) := borel _
local instance : BorelSpace (Idele F) := ⟨rfl⟩

variable (ν : Measure (K F)) [ν.IsHaarMeasure] (η : Measure (Idele F)) [η.IsHaarMeasure]
variable [∀ v : Place F, MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : Place F, BorelSpace (v.adicCompletion F)ˣ]
  (μ : ∀ v : Place F, Measure (v.adicCompletion F)ˣ)
  [∀ v : Place F, (μ v).IsHaarMeasure] [∀ v : Place F, SigmaFinite (μ v)]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]
variable (hν : IsWeilQuotientMeasure (principalIdeles F) η Measure.count (globalClassMeasure F ν))
variable (ω : PontryaginDual (K F))

private abbrev Z (f : GlobalBruhat F) := globalZetaContinued F ν f (compactIdeleClassCharacter F ω) 0
private abbrev G (f : GlobalBruhat F) := globalHeckeClearedZeta F ν ω f
private abbrev P := finiteHeckeOmissionMultiplier F (normOneEulerCharacter F ω)

omit [∀ v : Place F, MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : Place F, BorelSpace (v.adicCompletion F)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ] in
private theorem poleFactor_norm_both (z : ℂ) (hz : 2 ≤ ‖z‖) :
    1 ≤ ‖globalHeckePoleFactor F ω z‖ ∧ ‖globalHeckePoleFactor F ω z‖ ≤ ‖z‖ ^ 3 := by
  by_cases hω : ω = 1
  · rw [globalHeckePoleFactor, ite_eq_left hω, norm_mul]
    have h₁ : 1 ≤ ‖1 - z‖ := by
      have h := norm_sub_norm_le z (1 : ℂ)
      rw [norm_one, ← norm_neg (z - 1), neg_sub] at h
      linarith
    have h₂ : ‖1 - z‖ ≤ 1 + ‖z‖ := by simpa only [norm_one] using norm_sub_le (1 : ℂ) z
    have hq : 1 + ‖z‖ ≤ ‖z‖^2 := by nlinarith [sq_nonneg (‖z‖ - 2)]
    have hmul : ‖z‖ * ‖1 - z‖ ≤ ‖z‖ * ‖z‖^2 :=
      mul_le_mul_of_nonneg_left (h₂.trans hq) (norm_nonneg _)
    exact ⟨one_le_mul_of_one_le_of_one_le (by linarith) h₁, by
      simpa only [pow_succ', show (3 : ℕ) = 2 + 1 by decide] using hmul⟩
  · rw [globalHeckePoleFactor, ite_eq_right hω, norm_one]
    exact ⟨le_rfl, one_le_pow₀ (by linarith)⟩

set_option maxHeartbeats 850000 in
include μ hν in
/-- Reflecting the completed reference and removing the reflected
archimedean factors gives the polynomial strip normalization used for
strong co-primality. -/
theorem exists_globalCoprime_normalization :
    ∃ (r : GlobalBruhat F) (A : ℂ → ℂ),
      (∀ z, meromorphicOrderAt (Z F ν ω r) z ≠ ⊤) ∧
      (∀ f : GlobalBruhat F, ∀ z, meromorphicOrderAt (Z F ν ω r) z ≤ meromorphicOrderAt (Z F ν ω f) z) ∧
      Differentiable ℂ A ∧
      (∀ z : ℂ, z.re = 0 → G F ν ω r z * A z ≠ 0) ∧
      (∀ R : ℝ, ∃ (m : ℕ) (T : ℝ), ∀ z : ℂ, |z.re| ≤ R → T ≤ |z.im| →
        ‖G F ν ω r z * A z‖ ≤ ‖z‖ ^ m) ∧
      ∃ (k : ℕ) (C T : ℝ), ∀ z : ℂ, z.re = 0 → T ≤ |z.im| →
        ‖(G F ν ω r z * A z)⁻¹‖ ≤ C * |z.im| ^ k := by
  obtain ⟨S, hS, hω, hω', hDiff⟩ := exists_globalHeckeTateStage F ω
  obtain ⟨r, c, hc, hN, hFin, _⟩ := exists_globalMellin_order_reference F η ω S hS hω μ ν hν
  have hmin := globalHeckeOrderReference_min F η ν ω μ S hS hω hν r c hc hN
  obtain ⟨C, hC, hEuler⟩ := globalZetaContinued_reference_eq_completedEuler F ω S hS hω η ν μ hν r c hN (hFin 2)
  obtain ⟨L, L', ε, hL, hL', heL, heL', hε, hεn, _, _, hFE⟩ :=
    exists_globalCompletedHecke_tateReflection F S hS ω hω hω' η ν μ hν hDiff
  obtain ⟨m, n, _, hm, hme, hma, hpoly, hLow⟩ :=
    exists_globalFiniteHecke_oneLine_lower_bound F ν η μ hν ω⁻¹
  let D := completedTateReciprocalArch F S hS ω⁻¹ hω'
  let A (z : ℂ) := ε z * D (1-z)
  let pp := globalHeckePoleFactor F ω
  have hA : Differentiable ℂ A := by
    have hD : Differentiable ℂ D := fun z ↦
      (archimedeanNumberFieldZetaDenominator_analytic _ _ _ z).differentiableAt
    have hεd : Differentiable ℂ ε := fun z ↦ (hε z (mem_univ _)).differentiableAt
    exact hεd.mul (hD.comp (differentiable_id.const_sub 1))
  have hG (z : ℂ) : (Z F ν ω r.val) =ᶠ[𝓝[≠] z] fun w ↦ C * L w := by
    apply boundedPoleMellinSpace_unique_germs (D := {w : ℂ | 1 < w.re})
      (isOpen_lt continuous_const Complex.continuous_re) ⟨2, by norm_num⟩
    · exact fun w ↦ globalZetaContinued_meromorphic F ν r.val _ (compactIdeleClassCharacter_unitary F ω)
        0 w (mem_univ _)
    · exact fun w ↦ (MeromorphicAt.const C w).mul (hL w (mem_univ _))
    · intro w hw
      exact (hEuler hw).trans (congrArg (C * ·) (heL hw).symm)
  have hIdentity (z : ℂ) (hz : 1 ≤ |z.im|) :
      G F ν ω r.val z * A z = C * pp z * m (1-z) := by
    have ha (w : ℂ) : w ≠ 0 → w ≠ 1 → AnalyticAt ℂ m w := hma w
    have hj₀ : 1-z ≠ 0 := by intro he; have := congrArg Complex.im he; simp at this; norm_num [this] at hz
    have hj₁ : 1-z ≠ 1 := by intro he; have := congrArg Complex.im he; simp at this; norm_num [this] at hz
    have h₁ : ContinuousAt (fun w ↦ G F ν ω r.val w * A w) z :=
      (globalHeckeClearedZeta_analytic F ν ω r.val z).continuousAt.mul hA.continuous.continuousAt
    have h₂ : ContinuousAt (fun w ↦ C * pp w * m (1-w)) z :=
      (continuousAt_const.mul (globalHeckePoleFactor_analytic F ω z).continuousAt).mul
        ((ha _ hj₀ hj₁).continuousAt.comp (continuous_const.sub continuous_id).continuousAt)
    apply ((h₁.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE h₂).mp ?_).eq_of_nhds
    have hz₀ : z ≠ 0 := by intro he; norm_num [he] at hz
    have hz₁ : z ≠ 1 := by intro he; norm_num [he] at hz
    have hF := globalFiniteHeckeContinuation_germ F ω⁻¹ S hS hω' hL' hm heL' hme (1-z)
    filter_upwards [eventually_ne_nhdsWithin hz₀, eventually_ne_nhdsWithin hz₁,
      hG z, hFE z, (reflect_punctured z).eventually hF] with w hw₀ hw₁ hg hfe hf
    change Z F ν ω r.val w = C * L w at hg
    change L' (1-w) = L w * ε w at hfe
    change m (1-w) = D (1-w) * L' (1-w) at hf
    dsimp only [G, A]
    rw [globalHeckeClearedZeta_eq F ν ω r.val w hw₀ hw₁]
    change pp w * Z F ν ω r.val w * (ε w * D (1-w)) = C * pp w * m (1-w)
    rw [hg, hf, hfe]
    ring
  refine ⟨r.val, A, hFin, hmin, hA, ?_, ?_, ?_⟩
  · intro z hz
    have hPos : 0 < (1-z).re := by norm_num [Complex.sub_re, hz]
    have hD : D (1-z) ≠ 0 := by
      apply archimedeanNumberFieldZetaDenominator_ne_zero_of_pos
      · intro v
        simpa only [Complex.add_re, sLocalRealArchParameters_re, add_zero] using hPos
      · intro v
        simpa only [Complex.add_re, sLocalComplexArchParameters_re, add_zero] using hPos
    exact mul_ne_zero (globalHeckeClearedZeta_ne_zero_zero_line_of_min F η ν μ hν ω r.val hmin z hz)
      (mul_ne_zero (hεn z) hD)
  · intro R
    let q := |R| + 1
    obtain ⟨a, k, ha, hBound⟩ := hpoly (1-q) (1+q) (by dsimp [q]; linarith [abs_nonneg R])
    refine ⟨3+k+1, max 2 (‖C‖ * a * 2^k), fun z hzr hz ↦ ?_⟩
    have h₂ : 2 ≤ |z.im| := (le_max_left _ _).trans hz
    have h₁ : 1 ≤ |z.im| := (by norm_num : (1 : ℝ) ≤ 2).trans h₂
    have hnorm : 2 ≤ ‖z‖ := h₂.trans (Complex.abs_im_le_norm z)
    have hqz : |z.re| ≤ q := hzr.trans (by dsimp [q]; linarith [le_abs_self R])
    have hstrip : (1-z).re ∈ Icc (1-q) (1+q) := by
      simp only [Complex.sub_re, Complex.one_re]
      exact ⟨sub_le_sub_left (abs_le.mp hqz).2 1, by linarith [(abs_le.mp hqz).1]⟩
    have hF := hBound (1-z) hstrip (by simpa using h₁)
    have hfa : ‖m (1-z)‖ ≤ (a * 2^k) * ‖z‖^k := by
      have hy : 1 + |(1-z).im| ≤ 2 * ‖z‖ := by
        simp only [Complex.sub_im, Complex.one_im, zero_sub, abs_neg]
        linarith [Complex.abs_im_le_norm z]
      exact hF.trans (by rw [mul_assoc, ← mul_pow]; gcongr)
    have hC' : ‖C‖ * a * 2^k ≤ ‖z‖ := (le_max_right _ _).trans (hz.trans (Complex.abs_im_le_norm z))
    rw [hIdentity z h₁, norm_mul, norm_mul, pow_succ, pow_add]
    calc
      _ ≤ ‖C‖ * ‖z‖^3 * ((a * 2^k) * ‖z‖^k) := by
        gcongr
        exact (poleFactor_norm_both F ω z hnorm).2
      _ = (‖z‖^3 * ‖z‖^k) * (‖C‖ * a * 2^k) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hC' (by positivity)
  · obtain ⟨T, hT⟩ := eventually_atTop.mp (eventually_comap.mp hLow)
    refine ⟨n, ‖C‖⁻¹, max T 2, fun z hz hht ↦ ?_⟩
    have h₂ : 2 ≤ |z.im| := (le_max_right _ _).trans hht
    have hn₁ : 1 ≤ |z.im| := (by norm_num : (1 : ℝ) ≤ 2).trans h₂
    have hnorm : 2 ≤ ‖z‖ := h₂.trans (Complex.abs_im_le_norm z)
    have heq : 1-z = (⟨1, -z.im⟩ : ℂ) := by apply Complex.ext <;> simp [hz]
    have hlow := (hT |z.im| ((le_max_left _ _).trans hht) (-z.im) (abs_neg _)).2
    rw [abs_neg] at hlow
    have hy : 0 < |z.im|^n := pow_pos (zero_lt_one.trans_le hn₁) _
    have hmPos : 0 < ‖m ⟨1, -z.im⟩‖ := (inv_pos.mpr hy).trans_le hlow
    have hRec : ‖m ⟨1, -z.im⟩‖⁻¹ ≤ |z.im|^n := (inv_le_comm₀ hmPos hy).mpr hlow
    have hp := inv_le_one_of_one_le₀ (poleFactor_norm_both F ω z hnorm).1
    rw [hIdentity z hn₁, heq, norm_inv, norm_mul, norm_mul, mul_inv_rev, mul_inv_rev]
    calc
      _ = ‖C‖⁻¹ * (‖pp z‖⁻¹ * ‖m ⟨1, -z.im⟩‖⁻¹) := by ring
      _ ≤ ‖C‖⁻¹ * (1 * |z.im|^n) := by gcongr
      _ = _ := by rw [one_mul]

private theorem bergmanDivisor_inf_of_no_common_zero {p g : ℂ → ℂ}
    (hp : Differentiable ℂ p) (hg : Differentiable ℂ g)
    (hne : ∀ z, p z = 0 → g z ≠ 0) :
    bergmanDivisorSubmodule g ⊓ bergmanDivisorSubmodule p =
      bergmanDivisorSubmodule (fun z ↦ p z * g z) := by
  ext b
  have hbd : Differentiable ℂ b.val := by
    simpa only [preimage_univ, differentiableOn_univ] using b.property.2.1
  have hpg : Differentiable ℂ (fun z ↦ p z * g z) := hp.mul hg
  rw [Submodule.mem_inf, bergmanDivisorSubmodule_mem_iff hg, bergmanDivisorSubmodule_mem_iff hp,
    bergmanDivisorSubmodule_mem_iff hpg, entire_divisibility_iff_orders hg hbd,
    entire_divisibility_iff_orders hp hbd, entire_divisibility_iff_orders hpg hbd]
  have hOrd (z : ℂ) : analyticOrderAt (fun z ↦ p z * g z) z =
      analyticOrderAt p z + analyticOrderAt g z := analyticOrderAt_mul (hp.analyticAt z) (hg.analyticAt z)
  simp only [hOrd]
  constructor
  · rintro ⟨hg', hp'⟩ z
    by_cases h : p z = 0
    · rw [(hg.analyticAt z).analyticOrderAt_eq_zero.mpr (hne z h), add_zero]
      exact hp' z
    · rw [(hp.analyticAt z).analyticOrderAt_eq_zero.mpr h, zero_add]
      exact hg' z
  · intro h
    exact ⟨fun z ↦ (self_le_add_left _ _).trans (h z), fun z ↦ (self_le_add_right _ _).trans (h z)⟩

include μ hν in
/-- The selected reciprocal Euler ideal and the completed Hecke ideal are
comaximal in the entire Schwartz–Bergman space. Their intersection is the
principal-value divisor ideal with all selected multiplicities. -/
theorem exists_globalHeckeDivisor_coprime_ideals (W : Finset (Place F)) :
    ∃ r : GlobalBruhat F,
      (∀ z, meromorphicOrderAt (Z F ν ω r) z ≠ ⊤) ∧
      (∀ f : GlobalBruhat F, ∀ z, meromorphicOrderAt (Z F ν ω r) z ≤ meromorphicOrderAt (Z F ν ω f) z) ∧
      let D := bergmanDivisorSubmodule (G F ν ω r)
      let E := bergmanDivisorSubmodule (P F ω W)
      D ⊔ E = ⊤ ∧ D ⊓ E = bergmanDivisorSubmodule (fun z ↦ P F ω W z * G F ν ω r z) := by
  obtain ⟨r, a, hr, hmin, ha, hn, hpoly, hinv⟩ := exists_globalCoprime_normalization F ν η μ hν ω
  have hg : Differentiable ℂ (G F ν ω r) := fun z ↦ (globalHeckeClearedZeta_analytic F ν ω r z).differentiableAt
  have hp : Differentiable ℂ (P F ω W) := fun z ↦
    (finiteHeckeOmissionMultiplier_analytic F (normOneEulerCharacter F ω) W z).differentiableAt
  have hne (z : ℂ) (hz : P F ω W z = 0) : G F ν ω r z ≠ 0 := by
    apply globalHeckeClearedZeta_ne_zero_of_reciprocalEulerProduct_zero F η ν μ hν ω r hmin W z
    simp only [heckeEulerFactor, inv_inv]
    exact hz
  refine ⟨r, hr, hmin, eq_top_iff.mpr ?_, bergmanDivisor_inf_of_no_common_zero hp hg hne⟩
  intro f _
  obtain ⟨b, u, hu, hf⟩ := euler_divisor_bezout_of_normalization
    F (normOneEulerCharacter F ω) hg ha hn hpoly hinv W f
  let v := finiteHeckeOmissionBergmanMul F (normOneEulerCharacter F ω) W b
  have hv (z : ℂ) : v.val z = P F ω W z * b.val z := finiteHeckeOmissionBergmanMul_apply _ _ _ _ _
  have hbd : Differentiable ℂ b.val := by
    simpa only [preimage_univ, differentiableOn_univ] using b.property.2.1
  have hV : v ∈ bergmanDivisorSubmodule (P F ω W) :=
    (bergmanDivisorSubmodule_mem_iff hp v).mpr ⟨b.val, hbd, hv⟩
  have hU : f - v ∈ bergmanDivisorSubmodule (G F ν ω r) := by
    apply (bergmanDivisorSubmodule_mem_iff hg _).mpr
    refine ⟨u, hu, fun z ↦ ?_⟩
    change f.val z - v.val z = _
    rw [hf z, hv, add_sub_cancel_right]
  exact Submodule.mem_sup.mpr ⟨f-v, hU, v, hV, sub_add_cancel _ _⟩

private abbrev H := globalIdelicZetaComponentKernel F η ω
private abbrev X := (GlobalBruhat.polarEvaluation F).ker.map (H F η ω).mkQ

include μ hν in
/-- The selected principal-value endomorphism restricted to polar-free
homogeneous classes. -/
def globalPolarFreePrincipalValues (W : Finset (Place F)) : X F η ω →L[ℂ] X F η ω :=
  ((globalHomogeneousPrincipalValues F ν η μ hν ω W).comp (X F η ω).subtypeL).codRestrict (X F η ω)
    (by
      intro x
      obtain ⟨f, hf, he⟩ := Submodule.mem_map.mp x.property
      change globalHomogeneousPrincipalValues F ν η μ hν ω W x.val ∈ X F η ω
      rw [← he, globalHomogeneousPrincipalValues_mk]
      exact Submodule.mem_map.mpr ⟨_, globalPV_polarEvaluation_eq_zero F ν η μ hν W f hf, rfl⟩)

private theorem frechet_equiv_of_bijective {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    [Module ℂ X] [Module ℂ Y] [TopologicalSpace X] [TopologicalSpace Y]
    (hX : IsFrechetTVS X) (hY : IsFrechetTVS Y) (L : X →L[ℂ] Y) (hL : Bijective L) :
    ∃ e : X ≃L[ℂ] Y, ∀ x, e x = L x := by
  obtain ⟨hXa, hXp, hXm, hXc⟩ := hX
  obtain ⟨hYa, hYp, hYm, hYc⟩ := hY
  letI : UniformSpace X := IsTopologicalAddGroup.rightUniformSpace _
  letI : CompleteSpace X := hXc
  letI : MetrizableSpace X := hXm
  letI : PolynormableSpace ℂ X := hXp
  letI : ContinuousSMul ℂ X := (PolynormableSpace.withSeminorms ℂ X).continuousSMul
  letI : UniformSpace Y := IsTopologicalAddGroup.rightUniformSpace _
  letI : IsUniformAddGroup Y := isUniformAddGroup_of_addCommGroup
  letI : CompleteSpace Y := hYc
  letI : MetrizableSpace Y := hYm
  letI : PolynormableSpace ℂ Y := hYp
  letI : ContinuousSMul ℂ Y := (PolynormableSpace.withSeminorms ℂ Y).continuousSMul
  letI : (uniformity Y).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  letI : BaireSpace Y := BaireSpace.of_completelyPseudoMetrizable
  have ho := isOpenMap_of_surjective_complete_baire L hL.2
  let e := LinearEquiv.ofBijective L.toLinearMap hL
  let E := e.toEquiv.toHomeomorphOfContinuousOpen L.continuous ho
  exact ⟨⟨e, E.continuous_toFun, E.symm.continuous_toFun⟩, fun _ ↦ rfl⟩

set_option maxHeartbeats 850000 in
include μ hν in
/-- In the canonical Mellin chart the actual adelic principal-value
quotient is the entire Bergman quotient by the selected reciprocal Euler
divisor. The isomorphism is induced by the ordinary Mellin transform. -/
theorem exists_globalCoprime_mellinQuotient (W : Finset (Place F)) :
    let V := globalPolarFreePrincipalValues F ν η μ hν ω W
    let N := V.toLinearMap.range
    let E := bergmanDivisorSubmodule (P F ω W)
    ∃ e : (X F η ω ⧸ N) ≃L[ℂ] (B ⧸ E),
      ∀ x : X F η ω, e (N.mkQ x) = E.mkQ (globalPolarFreeMellin F ν η hν ω x) := by
  intro V N E
  obtain ⟨r, hr, hmin, hsum, hinter⟩ := exists_globalHeckeDivisor_coprime_ideals F ν η μ hν ω W
  let D := bergmanDivisorSubmodule (G F ν ω r)
  let D₀ := bergmanDivisorSubmodule (fun z ↦ P F ω W z * G F ν ω r z)
  obtain ⟨e, he⟩ := globalPolarFreeMellin_equiv_of_range F ν η hν ω r
    (globalConverse_polarFree_range_of_min F ν η hν μ ω r hr hmin)
  obtain ⟨m, hm⟩ := exists_globalPV_polarFree_equiv_of_min F ν η μ hν ω r hr hmin W
  let T : X F η ω →L[ℂ] (B ⧸ E) := E.mkQL.comp (globalPolarFreeMellin F ν η hν ω)
  have hT (x : X F η ω) : T x = E.mkQ (e x).val := (congrArg E.mkQ (he x)).symm
  have hV (x : X F η ω) : (e (V x)).val = (m x).val := by
    obtain ⟨f, hf, hfx⟩ := Submodule.mem_map.mp x.property
    let f₀ : (GlobalBruhat.polarEvaluation F).ker := ⟨f, hf⟩
    have hex : x = globalPolarFreeTestClass F η ω f₀ := Subtype.ext hfx.symm
    apply Subtype.ext
    funext z
    rw [hex, he, globalPolarFreeMellin_val]
    have hz := hm f₀ z
    change globalQuotientMellinFunction F ν η hν ω
      (globalHomogeneousPrincipalValues F ν η μ hν ω W ((H F η ω).mkQ f)) z = _
    rw [globalHomogeneousPrincipalValues_mk, globalQuotientMellinFunction_mk]
    exact hz.symm
  have hker : T.toLinearMap.ker = N := by
    apply Submodule.ext
    intro x
    rw [LinearMap.mem_ker]
    change T x = 0 ↔ x ∈ N
    rw [hT]
    change (Submodule.Quotient.mk (e x).val : B ⧸ E) = 0 ↔ _
    rw [Submodule.Quotient.mk_eq_zero E]
    have hEq : (e x).val ∈ E ↔ (e x).val ∈ D₀ := by
      have hInter : D ⊓ E = D₀ := hinter
      rw [← hInter]
      exact ⟨fun h ↦ ⟨(e x).property, h⟩, fun h ↦ h.2⟩
    rw [hEq]
    constructor
    · intro hx
      obtain ⟨y, hy⟩ := m.surjective (⟨(e x).val, hx⟩ : D₀)
      exact ⟨y, e.injective (Subtype.ext ((hV y).trans (congrArg Subtype.val hy)))⟩
    · rintro ⟨y, rfl⟩
      change (e (V y)).val ∈ D₀
      exact (hV y).symm ▸ (m y).property
  have hsur : Surjective T := by
    intro q
    obtain ⟨f, rfl⟩ := E.mkQ_surjective q
    have hf : f ∈ D ⊔ E := hsum.symm ▸ Submodule.mem_top
    obtain ⟨a, ha, b, hb, heq⟩ := Submodule.mem_sup.mp hf
    obtain ⟨x, hx⟩ := e.surjective (⟨a, ha⟩ : D)
    refine ⟨x, ?_⟩
    rw [hT, hx]
    change E.mkQ a = E.mkQ f
    have hb' : E.mkQ b = 0 := (Submodule.Quotient.mk_eq_zero E).mpr hb
    rw [← heq, map_add, hb', add_zero]
  let L : (X F η ω ⧸ N) →L[ℂ] (B ⧸ E) := N.liftQL T hker.ge
  have hBij : Bijective L := by
    constructor
    · change Injective L.toLinearMap
      apply LinearMap.ker_eq_bot.mp
      exact Submodule.ker_liftQ_eq_bot' _ _ hker.symm
    · intro z
      obtain ⟨x, hx⟩ := hsur z
      exact ⟨N.mkQ x, hx⟩
  have hp : Differentiable ℂ (P F ω W) := fun z ↦
    (finiteHeckeOmissionMultiplier_analytic F (normOneEulerCharacter F ω) W z).differentiableAt
  have hE : IsClosed (E : Set B) := bergmanDivisorSubmodule_isClosed hp
  letI : IsClosed (E : Set B) := hE
  have hN : IsClosed (N : Set (X F η ω)) := hker ▸ T.isClosed_ker
  have hX := isFrechetTVS_closedSubmodule (globalHomogeneousTheta_nuclearFrechet F ω η).1 (X F η ω)
    (globalPolarFreeQuotient_isClosed F ν η hν ω)
  have hB := schwartzBergman_frechet (univ : Set ℝ) isOpen_univ ordConnected_univ univ_nonempty
  obtain ⟨a, ha⟩ := frechet_equiv_of_bijective (isFrechetTVS_closedQuotient hX N hN)
    (isFrechetTVS_closedQuotient hB E hE) L hBij
  exact ⟨a, fun x ↦ ha (N.mkQ x)⟩

#print axioms exists_globalCoprime_normalization
#print axioms exists_globalHeckeDivisor_coprime_ideals
#print axioms exists_globalCoprime_mellinQuotient

end

end Masullo
