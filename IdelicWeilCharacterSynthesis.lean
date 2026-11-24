import IdelicWeilCompactFourier
import BruhatCyclicPeriodizationCorollary
import BruhatCyclicPeriodizationLift
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

open Filter Function MeasureTheory Metric NumberField Set Topology
open scoped Classical ContDiff NumberField

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

private abbrev G := IdeleClass F
private abbrev K := normOneIdeleClass F

private theorem cyclicNormal (γ : G F) : (Subgroup.zpowers γ).Normal where
  conj_mem x hx y := by
    rwa [mul_comm y x, mul_assoc, mul_inv_cancel, mul_one]

local instance weilSynthesisClassT2 : T2Space (G F) := ideleClasses_hausdorff
local instance weilSynthesisClassLC : LocallyCompactSpace (G F) := ideleClasses_locallyCompact
local instance weilSynthesisClassSecondCountable : SecondCountableTopology (G F) :=
  ideleClass_secondCountable F
local instance weilSynthesisNormOneCompact : CompactSpace (K F) := normOneIdeleClass_compact F

set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

private theorem exists_cyclicCompactLift {X : Type*} [CommGroup X] [TopologicalSpace X]
    [IsTopologicalGroup X] [T2Space X] [LocallyCompactSpace X]
    (m : X →ₜ* Multiplicative ℝ) (hm : IsProperMap m) (hms : Surjective m)
    (γ : X) (hγ : 0 < (m γ).toAdd)
    [T2Space (X ⧸ Subgroup.zpowers γ)] [LocallyCompactSpace (X ⧸ Subgroup.zpowers γ)]
    (b : ℝ → ℂ) (hb : ContDiff ℝ ∞ b) (B : Set ℝ) (hB : IsCompact B) (hs : support b ⊆ B)
    :
    ∃ L : BruhatSchwartz (X ⧸ Subgroup.zpowers γ) →L[ℂ] BruhatCompactTest X,
      ∀ (u : BruhatSchwartz (X ⧸ Subgroup.zpowers γ)) (x : X),
        (L u).val.val x = b (m x).toAdd * u.val (QuotientGroup.mk x) :=
  ⟨bruhatCyclicCompactCutoffLift m hm hms γ hγ b hb B hB hs,
    bruhatCyclicCutoffLift_apply m hm hms γ hγ b hb B hB hs⟩

section Quotient

variable (γ : G F)
local notation "Q" => G F ⧸ Subgroup.zpowers γ
local instance weilSynthesisQuotientNormal : (Subgroup.zpowers γ).Normal := cyclicNormal F γ
local instance weilSynthesisQuotientCommGroup : CommGroup Q :=
  QuotientGroup.Quotient.commGroup (Subgroup.zpowers γ)
private theorem characterSynthesis_of_cyclic_lift
    (hClosed : IsClosed ((Subgroup.zpowers γ : Subgroup (G F)) : Set (G F)))
    (hCompact : CompactSpace Q) (b : ℝ → ℂ)
    (L : BruhatSchwartz Q →L[ℂ] BruhatCompactTest (G F))
    (hL : ∀ (u : BruhatSchwartz Q) (x : G F),
      (L u).val.val x = b (ideleClassLogNorm F x).toAdd * u.val (QuotientGroup.mk x))
    (p : BruhatSchwartz Q) (f : BruhatCompactTest (G F)) (hrec : L p = f) :
    ∃ P : PontryaginDual (K F) → BruhatCompactTest (G F), HasSum P f ∧
      ∀ (w : PontryaginDual (K F)) (k : K F) (x : G F),
        (P w).val.val (k.val * x) = (((w k)⁻¹ : Circle) : ℂ) * (P w).val.val x := by
  letI : IsClosed ((Subgroup.zpowers γ : Subgroup (G F)) : Set (G F)) := hClosed
  letI : CompactSpace Q := hCompact
  letI : MeasurableSpace Q := borel Q
  letI : BorelSpace Q := ⟨rfl⟩
  letI : UniformSpace (BruhatSchwartz Q) := bruhatSchwartzUniformSpace
  letI : IsUniformAddGroup (BruhatSchwartz Q) := isUniformAddGroup_of_addCommGroup
  letI : T2Space (BruhatSchwartz Q) := bruhatSchwartz_t2
  letI : CompleteSpace (BruhatSchwartz Q) := bruhatSchwartz_complete
  let Haar : Measure Q := Measure.haar
  letI : Haar.IsHaarMeasure := inferInstanceAs (Measure.haar : Measure Q).IsHaarMeasure
  let J : K F →ₜ* Q := ⟨(QuotientGroup.mk' (Subgroup.zpowers γ)).comp (K F).subtype,
    QuotientGroup.continuous_mk.comp continuous_subtype_val⟩
  let res (ψ : PontryaginDual Q) := ψ.comp J
  let mode (ψ : PontryaginDual Q) :=
    compactBruhatFourierCoeff Haar ψ p • compactBruhatCharacter ψ⁻¹
  have hpSum : HasSum mode p := hasSum_compactBruhatFourierSeries Haar p
  let P (w : PontryaginDual (K F)) := L (∑' ψ : res ⁻¹' {w}, mode ψ.val)
  have hgroup := (hpSum.tsum_fiberwise res).mapL L
  rw [hrec] at hgroup
  refine ⟨P, hgroup, fun w k x => ?_⟩
  have hk : (ideleClassLogNorm F (k.val * x)).toAdd = (ideleClassLogNorm F x).toAdd := by
    have hk' : ideleClassLogNorm F k.val = 1 := by
      change Multiplicative.ofAdd (Real.log (ideleClassNorm F k.val)) = 1
      rw [show ideleClassNorm F k.val = 1 from k.property, Real.log_one]
      rfl
    rw [map_mul, hk', one_mul]
  let ev (a : Q) : BruhatSchwartz Q →L[ℂ] ℂ :=
    ⟨(LinearMap.proj a).comp (bruhatSchwartzSubmodule (G := Q)).subtype,
      bruhatSchwartz_continuous_eval a⟩
  have hfiber : Summable (fun ψ : res ⁻¹' {w} => mode ψ.val) := hpSum.summable.subtype _
  have heval (a : Q) :
      (∑' ψ : res ⁻¹' {w}, mode ψ.val).val a =
        ∑' ψ : res ⁻¹' {w}, (mode ψ.val).val a :=
    (ev a).map_tsum hfiber
  change (L (∑' ψ : res ⁻¹' {w}, mode ψ.val)).val.val (k.val * x) =
    _ * (L (∑' ψ : res ⁻¹' {w}, mode ψ.val)).val.val x
  rw [hL, hL, hk, heval, heval, ← mul_assoc]
  have hpoint (ψ : res ⁻¹' {w}) :
      (mode ψ.val).val (QuotientGroup.mk (k.val * x)) =
        (((w k)⁻¹ : Circle) : ℂ) * (mode ψ.val).val (QuotientGroup.mk x) := by
    have hres : ψ.val (QuotientGroup.mk k.val) = w k :=
      congrArg (fun θ : PontryaginDual (K F) => θ k) (mem_singleton_iff.mp ψ.property)
    change compactBruhatFourierCoeff Haar ψ.val p *
        (((ψ.val (QuotientGroup.mk (k.val * x)))⁻¹ : Circle) : ℂ) =
      _ * (compactBruhatFourierCoeff Haar ψ.val p *
        (((ψ.val (QuotientGroup.mk x))⁻¹ : Circle) : ℂ))
    rw [QuotientGroup.mk_mul, map_mul, hres, mul_inv_rev, Circle.coe_mul]
    ring
  simp_rw [hpoint]
  rw [tsum_mul_left]
  ring

end Quotient

/-- The norm-one isotypic components of a compact idelic Bruhat test
sum unconditionally in the original compact-test topology. -/
theorem exists_idelicWeil_characterSynthesis (f : BruhatCompactTest (G F)) :
    ∃ P : PontryaginDual (K F) → BruhatCompactTest (G F), HasSum P f ∧
      ∀ (w : PontryaginDual (K F)) (k : K F) (x : G F),
        (P w).val.val (k.val * x) = (((w k)⁻¹ : Circle) : ℂ) * (P w).val.val x := by
  let m := mellinClassModulus F
  let ℓ (x : G F) : ℝ := (m x).toAdd
  have hℓ : Continuous ℓ := continuous_toAdd.comp m.continuous
  have hm : IsProperMap m :=
    isProperMap_snd_of_compactSpace.comp (ideleClassSplitHomeomorph F).isProperMap
  have hms : Surjective m :=
    fun t => ⟨ideleClassExpSection F t, ideleClassLogNorm_expSection F t⟩
  obtain ⟨A, hA⟩ := (f.property.image hℓ).isBounded.exists_norm_le
  let D := max A 1
  have hD : 0 < D := zero_lt_one.trans_le (le_max_right _ _)
  have hbnd (x : G F) (hx : x ∈ tsupport f.val.val) : |ℓ x| ≤ D :=
    (by simpa only [Real.norm_eq_abs] using hA (ℓ x) ⟨x, hx, rfl⟩ : |ℓ x| ≤ A).trans
      (le_max_left _ _)
  let bump : ContDiffBump (0 : ℝ) :=
    ⟨D, D + 1, hD, by linarith⟩
  let b (t : ℝ) : ℂ := (bump t : ℂ)
  have hb : ContDiff ℝ ∞ b := Complex.ofRealCLM.contDiff.comp bump.contDiff
  let B := closedBall (0 : ℝ) (D + 1)
  have hB : IsCompact B := isCompact_closedBall _ _
  have hbs : support b ⊆ B := by
    intro x hx
    have hf : x ∈ support (bump : ℝ → ℝ) := by
      intro h
      exact hx (by simp only [b, h, Complex.ofReal_zero])
    rw [bump.support_eq] at hf
    exact ball_subset_closedBall hf
  obtain ⟨γ, hγ⟩ := hms (Multiplicative.ofAdd (2 * D + 3))
  have hγℓ : ℓ γ = 2 * D + 3 := congrArg Multiplicative.toAdd hγ
  have hγpos : 0 < (m γ).toAdd := by change 0 < ℓ γ; rw [hγℓ]; linarith
  letI : (Subgroup.zpowers γ).Normal := cyclicNormal F γ
  letI : CommGroup (G F ⧸ Subgroup.zpowers γ) :=
    QuotientGroup.Quotient.commGroup (Subgroup.zpowers γ)
  letI : IsClosed ((Subgroup.zpowers γ : Subgroup (G F)) : Set (G F)) :=
    modulatedCyclicSubgroup_isClosed m γ hγpos
  letI : CompactSpace (G F ⧸ Subgroup.zpowers γ) := modulatedCyclicQuotient_compact m hm γ hγpos
  letI : MeasurableSpace (G F ⧸ Subgroup.zpowers γ) := borel (G F ⧸ Subgroup.zpowers γ)
  letI : BorelSpace (G F ⧸ Subgroup.zpowers γ) := ⟨rfl⟩
  let p := bruhatCyclicPeriodization m hm γ hγpos hms f.val
  have hp (x : G F) (hx : ℓ x ∈ B) : p.val (QuotientGroup.mk x) = f.val.val x := by
    have hx' : |ℓ x| ≤ D + 1 := by
      simpa only [B, mem_closedBall, dist_zero_right, Real.norm_eq_abs] using hx
    change (bruhatCyclicPeriodization m hm γ hγpos hms f.val).val (QuotientGroup.mk x) = _
    rw [bruhatCyclicPeriodization_apply, bruhatSchwartz_cyclicOrbitSum_apply, tsum_eq_single 0]
    · simp
    · intro n hn
      apply image_eq_zero_of_notMem_tsupport
      intro h
      have h₁ := hbnd (γ ^ n * x) h
      have he : ℓ (γ ^ n * x) = (n : ℝ) * (2 * D + 3) + ℓ x := by
        change (m (γ ^ n * x)).toAdd = _
        rw [map_mul, map_zpow, toAdd_mul, toAdd_zpow, zsmul_eq_mul,
          show (m γ).toAdd = 2 * D + 3 from hγℓ]
      have hn₁ : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hn
      have h₃ : 2 * D + 3 ≤ |(n : ℝ)| * (2 * D + 3) := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hn₁ (show 0 ≤ 2 * D + 3 by linarith)
      have h₄ := abs_sub ((n : ℝ) * (2 * D + 3) + ℓ x) (ℓ x)
      rw [add_sub_cancel_right, abs_mul, abs_of_pos (show 0 < 2 * D + 3 by linarith), ← he] at h₄
      linarith
  letI : T2Space (G F ⧸ Subgroup.zpowers γ) := QuotientGroup.instT2Space
  letI : LocallyCompactSpace (G F ⧸ Subgroup.zpowers γ) :=
    QuotientGroup.instLocallyCompactSpace (Subgroup.zpowers γ)
  obtain ⟨L, hL⟩ := exists_cyclicCompactLift m hm hms γ hγpos b hb B hB hbs
  have hrec : L p = f := by
    apply BruhatCompactTest.val_injective
    apply Subtype.ext
    funext x
    change (L p).val.val x = f.val.val x
    rw [hL p x]
    by_cases hx : x ∈ tsupport f.val.val
    · have hclosed : ℓ x ∈ closedBall (0 : ℝ) bump.rIn := by
        simpa only [bump, mem_closedBall, dist_zero_right, Real.norm_eq_abs] using hbnd x hx
      have hbump := bump.one_of_mem_closedBall hclosed
      have hxB : ℓ x ∈ B := by
        simp only [B, mem_closedBall, dist_zero_right, Real.norm_eq_abs]
        linarith [hbnd x hx]
      rw [hp x hxB, show b (ℓ x) = (1 : ℂ) by simp only [b, hbump, Complex.ofReal_one], one_mul]
    · have hz := image_eq_zero_of_notMem_tsupport hx
      by_cases hxB : ℓ x ∈ B
      · rw [hp x hxB, hz, mul_zero]
      · have hbz : b (ℓ x) = 0 := notMem_support.mp fun ht => hxB (hbs ht)
        rw [hbz, hz, zero_mul]
  exact characterSynthesis_of_cyclic_lift F γ
    (modulatedCyclicSubgroup_isClosed m γ hγpos)
    (modulatedCyclicQuotient_compact m hm γ hγpos) b L hL p f hrec

local instance weilSynthesisNormOneMeasurable : MeasurableSpace (K F) := borel _
local instance weilSynthesisNormOneBorel : BorelSpace (K F) := ⟨rfl⟩
local instance weilSynthesisNormOneSecondCountable : SecondCountableTopology (K F) :=
  IsInducing.subtypeVal.secondCountableTopology

variable (ν : Measure (K F)) [ν.IsHaarMeasure]

private theorem exists_compactTest_sliceFunctional (w : PontryaginDual (K F)) (x : G F) :
    ∃ L : BruhatCompactTest (G F) →L[ℂ] ℂ, ∀ u,
      L u = (ν.real univ : ℂ)⁻¹ * ∫ k : K F, (w k : ℂ) * u.val.val (k.val * x) ∂ν := by
  letI : IsFiniteMeasure ν := ⟨isCompact_univ.measure_lt_top⟩
  letI : Measure.Regular ν := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure ν
  letI : ν.IsInvInvariant := Measure.IsHaarMeasure.isInvInvariant_of_regular ν
  obtain ⟨A, hA⟩ := exists_bruhatSchwartz_compactAverage (G := G F) (K F) ν w
  let ev : BruhatSchwartz (G F) →L[ℂ] ℂ :=
    ⟨(LinearMap.proj x).comp (bruhatSchwartzSubmodule (G := G F)).subtype,
      bruhatSchwartz_continuous_eval x⟩
  refine ⟨(ν.real univ : ℂ)⁻¹ • (ev.comp (A.comp bruhatCompactTest_toSchwartz)), fun u => ?_⟩
  change (ν.real univ : ℂ)⁻¹ * ev (A u.val) = _
  have h := (hA u.val ev).2
  have hleft : ev (A u.val) =
      ∫ k : K F, (((w k)⁻¹ : Circle) : ℂ) * u.val.val (k.val⁻¹ * x) ∂ν := by
    rw [h]
    apply integral_congr_ae
    exact Eventually.of_forall fun k => by
      change (((w k)⁻¹ : Circle) : ℂ) * (bruhatSchwartz_translate k.val u.val).val x = _
      rw [bruhatSchwartz_translate_apply]
  rw [hleft]
  apply congrArg ((ν.real univ : ℂ)⁻¹ * ·)
  simpa only [map_inv, Subgroup.coe_inv] using
    (integral_inv_eq_self (μ := ν) (fun k : K F => (w k : ℂ) * u.val.val (k.val * x)))

/-- The isotypic expansion of a compact idelic test converges
unconditionally as compact tests. Its components are exactly the normalized
logarithmic Fourier profiles multiplied by the inverse local phase. -/
theorem exists_idelicWeil_logProfile_characterSynthesis (f : BruhatCompactTest (G F)) :
    ∃ P : PontryaginDual (K F) → BruhatCompactTest (G F), HasSum P f ∧
      ∀ w (x : G F),
        (P w).val.val x =
          ((ν.real univ : ℂ)⁻¹ * idelicWeilLogProfile F ν w f (ideleClassLogNorm F x).toAdd) *
            (((normOneEulerCharacter F w x)⁻¹ : Circle) : ℂ) := by
  letI : T2Space (BruhatCompactTest (G F)) := bruhatCompactTest_t2
  letI : IsFiniteMeasure ν := ⟨isCompact_univ.measure_lt_top⟩
  obtain ⟨P, hP, hEig⟩ := exists_idelicWeil_characterSynthesis F f
  refine ⟨P, hP, fun w x => ?_⟩
  let t := ideleClassLogNorm F x
  let a := ideleClassExpSection F t
  let k := ideleClassNormOnePart F x
  obtain ⟨L, hL⟩ := exists_compactTest_sliceFunctional F ν w a
  have hν : (ν.real univ : ℂ) ≠ 0 := by
    apply Complex.ofReal_ne_zero.mpr
    exact ENNReal.toReal_ne_zero.mpr
      ⟨fun h => (NeZero.ne ν) (Measure.measure_univ_eq_zero.mp h), measure_ne_top _ _⟩
  have hLmode (ψ : PontryaginDual (K F)) : L (P ψ) =
      if ψ = w then (P w).val.val a else 0 := by
    rw [hL]
    simp_rw [hEig ψ]
    have he : (∫ b : K F, (w b : ℂ) * (((ψ b)⁻¹ : Circle) : ℂ) * (P ψ).val.val a ∂ν) =
        (if ψ = w then (ν.real univ : ℂ) else 0) * (P ψ).val.val a := by
      rw [integral_mul_const]
      apply congrArg (· * (P ψ).val.val a)
      simpa only [mul_comm (w _ : ℂ), Circle.coe_inv_eq_conj, ← Complex.star_def] using
        integral_character_pair ν ψ w
    simp_rw [← mul_assoc]
    rw [he]
    by_cases h : ψ = w
    · subst ψ
      rw [ite_eq_left rfl, ← mul_assoc, inv_mul_cancel₀ hν, one_mul, ite_eq_left rfl]
    · rw [ite_eq_right h, ite_eq_right h, zero_mul, mul_zero]
  have hsum := (hP.mapL L).congr_fun fun ψ => (hLmode ψ).symm
  have hcoeff := hsum.unique (hasSum_ite_eq w ((P w).val.val a))
  have hval : (P w).val.val a = (ν.real univ : ℂ)⁻¹ * idelicWeilLogProfile F ν w f t.toAdd := by
    rw [← hcoeff, hL]
    rfl
  have hk : k.val * a = x := (ideleClassSplit F).left_inv x
  calc
    (P w).val.val x = (P w).val.val (k.val * a) := congrArg (P w).val.val hk.symm
    _ = (((w k)⁻¹ : Circle) : ℂ) * (P w).val.val a := hEig w k a
    _ = _ := by
      rw [hval]
      exact mul_comm _ _

/-- A normalized character component has the original logarithmic profile at
its own character and zero profile at every other character. -/
theorem idelicWeilLogProfile_characterComponent
    (f p : BruhatCompactTest (G F)) (w : PontryaginDual (K F))
    (hp : ∀ x : G F, p.val.val x =
      ((ν.real univ : ℂ)⁻¹ * idelicWeilLogProfile F ν w f (ideleClassLogNorm F x).toAdd) *
        (((normOneEulerCharacter F w x)⁻¹ : Circle) : ℂ))
    (ψ : PontryaginDual (K F)) (t : ℝ) :
    idelicWeilLogProfile F ν ψ p t = if ψ = w then idelicWeilLogProfile F ν w f t else 0 := by
  let c := idelicWeilLogProfile F ν w f t
  let M := (ν.real univ : ℂ)
  letI : IsFiniteMeasure ν := ⟨isCompact_univ.measure_lt_top⟩
  have hM : M ≠ 0 := by
    apply Complex.ofReal_ne_zero.mpr
    exact ENNReal.toReal_ne_zero.mpr
      ⟨fun h => (NeZero.ne ν) (Measure.measure_univ_eq_zero.mp h), measure_ne_top _ _⟩
  unfold idelicWeilLogProfile
  change (∫ k : K F, (ψ k : ℂ) * p.val.val
    (k.val * ideleClassExpSection F (Multiplicative.ofAdd t)) ∂ν) =
      if ψ = w then c else 0
  have hSplit (k : K F) :
      ideleClassSplit F (k.val * ideleClassExpSection F (Multiplicative.ofAdd t)) =
        (k, Multiplicative.ofAdd t) :=
    (ideleClassSplit F).apply_symm_apply (k, Multiplicative.ofAdd t)
  have h := integral_character_pair ν w ψ
  have he : (∫ k : K F, (ψ k : ℂ) * (((w k)⁻¹ : Circle) : ℂ) ∂ν) =
      if ψ = w then M else 0 := by
    simpa only [mul_comm (ψ _ : ℂ), Circle.coe_inv_eq_conj, ← Complex.star_def,
      eq_comm (a := w) (b := ψ)] using h
  calc
    _ = ∫ k : K F, ((ψ k : ℂ) * (((w k)⁻¹ : Circle) : ℂ)) * (M⁻¹ * c) ∂ν := by
      apply integral_congr_ae
      exact Eventually.of_forall fun k => by
        dsimp only
        rw [hp]
        have ht := congrArg Prod.snd (hSplit k)
        have hw := congrArg (w ∘ Prod.fst) (hSplit k)
        change ideleClassLogNorm F (k.val * ideleClassExpSection F (Multiplicative.ofAdd t)) =
          Multiplicative.ofAdd t at ht
        change normOneEulerCharacter F w
          (k.val * ideleClassExpSection F (Multiplicative.ofAdd t)) = w k at hw
        rw [ht, hw]
        change (ψ k : ℂ) * ((M⁻¹ * c) * (((w k)⁻¹ : Circle) : ℂ)) = _
        ring
    _ = _ := by
      rw [integral_mul_const, he]
      split <;> simp [← mul_assoc, hM]

/-- The singular infinite-place functionals commute with the full
norm-one isotypic expansion in the compact-test topology. -/
theorem exists_idelicWeil_infinite_characterSynthesis (f : BruhatCompactTest (G F)) :
    ∃ P : PontryaginDual (K F) → BruhatCompactTest (G F),
      (∀ w (x : G F),
        (P w).val.val x =
          ((ν.real univ : ℂ)⁻¹ * idelicWeilLogProfile F ν w f (ideleClassLogNorm F x).toAdd) *
            (((normOneEulerCharacter F w x)⁻¹ : Circle) : ℂ)) ∧
      (∀ v : InfinitePlace F, HasSum (fun w => infinitePlaceIdelicWeilDual F v (P w))
        (infinitePlaceIdelicWeilDual F v f)) ∧
      HasSum (fun w => infinitePlaceIdelicWeilSum F (P w)) (infinitePlaceIdelicWeilSum F f) := by
  obtain ⟨P, hP, heval⟩ := exists_idelicWeil_logProfile_characterSynthesis F ν f
  exact ⟨P, heval, fun v => hP.mapL (infinitePlaceIdelicWeilDual F v),
    hP.mapL (infinitePlaceIdelicWeilSum F)⟩

end
end Masullo
