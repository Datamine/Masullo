import SLocalPaddingCharacters
import SLocalEulerReference
import SLocalPrincipalRangeGlobal
import SLocalMeromorphicKernels
import AdelicThetaKernels
import AdelicZetaUnfolding
import AdelicPolarDistributions
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Order.Filter.AtTopBot.Finset

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical ENNReal NumberField

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

private abbrev Place := HeightOneSpectrum (𝓞 F)

local instance : MeasurableSpace (Idele F) := borel _
local instance : BorelSpace (Idele F) := ⟨rfl⟩

variable (η : Measure (Idele F)) [η.IsHaarMeasure]
variable (ω : PontryaginDual (normOneIdeleClass F))
variable (S : Finset (Place F))
variable (hs : Surjective (sIdeleClassInclusion F S))
variable (hu : globalNormOneCharacter F ω ∈ (sUnramified F S : Set (QuasiCharacter (IdeleClass F))))

private abbrev G := (SAdeles F S)ˣ
private abbrev E := sLocalBruhatImage F S
private abbrev τ := sLocalNormOneCharacterOfGlobal F ω S hs hu

/-- The idelic zeta integrand for the canonical extension of the norm-one character. -/
def globalMellinIntegrand (f : GlobalBruhat F) (z : ℂ) (g : Idele F) : ℂ :=
  (GlobalBruhat.algebraicEquiv F f).val g.val *
    (ideleNormTwist F (compactIdeleClassCharacter F ω) z (ideleClassMap F g) : ℂ)

private theorem globalWeight_on_block (z : ℂ) (g : sIdeleBlock F S) :
    (ideleNormTwist F (compactIdeleClassCharacter F ω) z (ideleClassMap F g.val) : ℂ) =
      sLocalZetaWeight F S (τ F ω S hs hu) z (QuotientGroup.mk (sBlockUnitProduct F S g).1) := by
  let q : SIdeleQuotient F S := QuotientGroup.mk (sBlockUnitProduct F S g).1
  let p := (sLocalZetaSplit F S).symm q
  have hN : p.1 = Real.log (ideleClassNorm F (ideleClassMap F g.val)) := by
    rw [← sLocalZetaSplit_logModulus F S p, show sLocalZetaSplit F S p = q from
      (sLocalZetaSplit F S).apply_symm_apply q]
    dsimp only [q]
    rw [sLocalClassModulus_mk, sBlock_norm_eq]
    rfl
  have hχ : ((τ F ω S hs hu p.2) : ℂ) =
      globalNormOneCharacter F ω (ideleClassMap F g.val) := by
    simpa only [sLocalZetaWeight, zero_mul, Complex.exp_zero, one_mul] using
      sLocalZetaWeight_zero_global_block F S ω hs hu g
  change globalNormOneCharacter F ω (ideleClassMap F g.val) *
      Complex.exp (z * (Real.log (ideleClassNorm F (ideleClassMap F g.val)) : ℂ)) =
    Complex.exp (z * (p.1 : ℂ)) * (τ F ω S hs hu p.2 : ℂ)
  rw [hN, hχ, mul_comm]

/-- The integrand on an open block is pulled back from its S-ideles.
All factors from the unramified integral tail disappear pointwise. -/
theorem globalMellinIntegrand_on_block (f : E F S) (z : ℂ) (g : sIdeleBlock F S) :
    globalMellinIntegrand F ω f.val z g.val =
      sLocalIdelicZetaIntegrand F S (τ F ω S hs hu) z f (sBlockUnitProduct F S g).1 := by
  have htail (v : Place F) (hv : v ∉ S) : g.val.val.2 v ∈ v.adicCompletionIntegers F :=
    g.property.1 v hv
  unfold globalMellinIntegrand sLocalIdelicZetaIntegrand
  change GlobalBruhat.evaluation F g.val.val f.val * _ = _
  rw [sLocalBruhatRestriction_reconstruct, ite_eq_left htail, mul_one, globalWeight_on_block F ω S hs hu]
  exact mul_comm _ _

private abbrev B := (SIntegralTail F S)ˣ
private abbrev H := sIdeleBlock F S

local instance : MeasurableSpace (B F S) := borel _
local instance : BorelSpace (B F S) := ⟨rfl⟩
local instance : MeasurableSpace (G F S) := borel _
local instance : BorelSpace (G F S) := ⟨rfl⟩

/-- Integration on the open block is a scalar multiple of the S-local
integral. Haar normalization determines the scalar, independently of the
test and the spectral parameter. -/
theorem globalMellin_block_integral_eq_smul (μ : Measure (G F S)) [μ.IsHaarMeasure] :
    ∃ C : ℝ, ∀ (f : E F S) (z : ℂ),
      (∫ g in (sIdeleBlock F S : Set (Idele F)), globalMellinIntegrand F ω f.val z g ∂η) =
        C • sLocalIdelicZetaIntegral F S μ (τ F ω S hs hu) f z := by
  letI (v : {v : Place F // v ∉ S}) : CompactSpace (v.val.adicCompletionIntegers F) :=
    compactSpace_adicIntegers v.val
  letI : CompactSpace (B F S) := compactSpace_units_of_compactSpace _
  letI : LocallyCompactSpace (Idele F) := ideles_locallyCompact
  letI : LocallyCompactSpace (G F S) := sLocalIdeles_locallyCompact F S
  letI : SecondCountableTopology (G F S) := sLocalIdeles_secondCountable F S
  letI : LocallyCompactSpace (H F S) := (sIdeleBlock_open F S).locallyCompactSpace
  letI : SecondCountableTopology (Adeles F) := adeles_secondCountable F
  letI : SecondCountableTopology (Adeles F)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  letI : SecondCountableTopology (Idele F) := Units.isEmbedding_embedProduct.secondCountableTopology
  letI : SecondCountableTopology (H F S) :=
    (sIdeleBlock_open F S).isOpenEmbedding_subtypeVal.isEmbedding.secondCountableTopology
  let e := sBlockUnitProduct F S
  letI : SecondCountableTopology (G F S × B F S) :=
    e.symm.toHomeomorph.isEmbedding.secondCountableTopology
  let tail : Measure (B F S) := Measure.haar
  let ν := μ.prod tail
  let ηH := η.comap (Subtype.val : H F S → Idele F)
  letI : ηH.IsHaarMeasure := by
    change (η.comap (sIdeleBlock F S).subtype).IsHaarMeasure
    exact Measure.IsHaarMeasure.comap (mH := inferInstance) (f := (sIdeleBlock F S).subtype) η
      (sIdeleBlock_open F S).isOpenEmbedding_subtypeVal
  letI : (ηH.map e).IsHaarMeasure :=
    e.toMulEquiv.isHaarMeasure_map ηH e.continuous e.symm.continuous
  let c := Measure.haarScalarFactor (ηH.map e) ν
  have hmap : ηH.map e = c • ν := Measure.isMulLeftInvariant_eq_smul (ηH.map e) ν
  refine ⟨(c : ℝ) * tail.real univ, fun f z ↦ ?_⟩
  rw [← integral_subtype_comap (sIdeleBlock_open F S).measurableSet]
  let A := sLocalIdelicZetaIntegrand F S (τ F ω S hs hu) z f
  have hAe : (fun g : H F S ↦ globalMellinIntegrand F ω f.val z g.val) =
      fun g ↦ A (e g).1 :=
    funext (globalMellinIntegrand_on_block F ω S hs hu f z)
  change (∫ g : H F S, globalMellinIntegrand F ω f.val z g.val ∂ηH) = _
  rw [hAe]
  have hme : MeasurableEmbedding (e : H F S → G F S × B F S) :=
    e.toHomeomorph.toMeasurableEquiv.measurableEmbedding
  rw [← hme.integral_map (fun p : G F S × B F S ↦ A p.1), hmap,
    integral_smul_nnreal_measure, integral_fun_fst]
  simp only [NNReal.smul_def, sLocalIdelicZetaIntegral, mul_smul]
  rfl

variable [∀ v : Place F, MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : Place F, BorelSpace (v.adicCompletion F)ˣ]
  (μ : ∀ v : Place F, Measure (v.adicCompletion F)ˣ)
  [∀ v : Place F, (μ v).IsHaarMeasure] [∀ v : Place F, SigmaFinite (μ v)]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]

private abbrev L (U : Finset (Place F)) (τ : PontryaginDual (SLocalThetaNormOne F U))
    (f : sLocalBruhatImage F U) :=
  sLocalProductZetaContinued F U (fun v ↦ μ v.val) τ (sLocalRealArchParameters F U τ)
    (sLocalComplexArchParameters F U τ) f

/-- The S-local continuation is continuous in the half-plane of absolute convergence. -/
theorem sLocalProductZetaContinued_continuousAt_pos
    (U : Finset (Place F)) (τ : PontryaginDual (SLocalThetaNormOne F U))
    (f : sLocalBruhatImage F U) (z : ℂ) (hz : 0 < z.re) :
    ContinuousAt (L F μ U τ f) z := by
  let ρ := sLocalZetaProductMeasure F U (fun v ↦ μ v.val) (archimedeanMultiplicativeHaar F)
  letI : ρ.IsHaarMeasure :=
    sLocalZetaProductMeasure_isHaar F U (fun v ↦ μ v.val) (archimedeanMultiplicativeHaar F)
  apply (sLocalIdelicZeta_analytic F U ρ τ f z hz).continuousAt.congr
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz] with w hw
  exact ((sLocalIdelicZeta_meromorphic_continuation F U (fun v ↦ μ v.val) τ f).2 hw).symm

theorem sLocalProductZetaContinued_global_pad_right
    {T : Finset (Place F)} (hST : S ⊆ T)
    (hT : Surjective (sIdeleClassInclusion F T))
    (huT : globalNormOneCharacter F ω ∈ (sUnramified F T : Set (QuasiCharacter (IdeleClass F))))
    (f : E F S) (z : ℂ) (hz : 0 < z.re) :
    sLocalMellinPaddingDenominator F S
        (sLocalFiniteZetaPhases F T (τ F ω T hT huT)) z *
      L F μ T (τ F ω T hT huT) (sLocalBruhatTransition F hST f) z =
        sLocalMellinPaddingHaarMass F μ S T * L F μ S (τ F ω S hs hu) f z := by
  let τT := τ F ω T hT huT
  let D := sLocalMellinPaddingDenominator F S (sLocalFiniteZetaPhases F T τT)
  have hD : ContinuousAt D z := (Finset.analyticAt_fun_prod _
    (fun (v : {v : T // v.val ∉ S}) _ ↦
      finiteZetaDenominator_analytic F v.val.val (sLocalFiniteZetaPhases F T τT v.val) z)).continuousAt
  have hL := hD.mul (sLocalProductZetaContinued_continuousAt_pos F μ T τT
    (sLocalBruhatTransition F hST f) z hz)
  have hR : ContinuousAt
      (fun w ↦ sLocalMellinPaddingHaarMass F μ S T * L F μ S (τ F ω S hs hu) f w) z :=
    continuousAt_const.mul (sLocalProductZetaContinued_continuousAt_pos F μ S (τ F ω S hs hu) f z hz)
  exact ((hL.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE hR).mp
    (sLocalProductZetaContinued_global_pad F S ω hs hu μ hST hT huT f z)).eq_of_nhds

omit [∀ v : Place F, MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : Place F, BorelSpace (v.adicCompletion F)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ] in
/-- A cofinal increasing sequence of open idelic blocks containing the given
stage and meeting every idele class. -/
theorem exists_ideleBlock_tower :
    ∃ T : ℕ → Finset (Place F), Monotone T ∧
      (∀ n, S ⊆ T n) ∧
      (∀ n, Surjective (sIdeleClassInclusion F (T n))) ∧
      Tendsto T atTop atTop ∧
      (⋃ n, (sIdeleBlock F (T n) : Set (Idele F))) = univ := by
  obtain ⟨B, hB⟩ := sIdeleClass_eventually_surjective F
  letI := finitePlaces_countable F
  obtain ⟨e, he⟩ := exists_injective_nat (Place F)
  let fin (n : ℕ) : {v : Place F | e v < n}.Finite := (finite_lt_nat n).preimage he.injOn
  let T (n : ℕ) := (S ∪ B) ∪ (fin n).toFinset
  have hmono : Monotone T := by
    intro m n h
    apply Finset.union_subset_union_right (s := S ∪ B)
    intro v hv
    exact (fin n).mem_toFinset.mpr (((fin m).mem_toFinset.mp hv).trans_le h)
  refine ⟨T, hmono, fun _ ↦ Finset.subset_union_left.trans Finset.subset_union_left,
    fun n ↦ hB (T n) (Finset.subset_union_right.trans Finset.subset_union_left), ?_, ?_⟩
  · apply hmono.tendsto_atTop_finset
    intro v
    exact ⟨e v + 1, Finset.mem_union_right _ ((fin _).mem_toFinset.mpr (Nat.lt_succ_self _))⟩
  · apply eq_univ_of_forall
    intro a
    let W := (ideleOrder_finite_support F a).toFinset
    let n := W.sup e + 1
    have hW : W ⊆ T n := by
      intro v hv
      exact Finset.mem_union_right _ ((fin n).mem_toFinset.mpr
        ((Finset.le_sup hv).trans_lt (Nat.lt_succ_self _)))
    apply mem_iUnion.mpr
    refine ⟨n, (sIdeleBlock_mem_iff F _ a).mpr fun v hv ↦ ?_⟩
    by_contra h
    exact hv (hW ((ideleOrder_finite_support F a).mem_toFinset.mpr h))

/-- Any two tests on the same S-local stage have the same proportionality
between the global integral and their original S-local continuation.
The identity avoids choosing a denominator that could vanish on a test. -/
theorem globalIdelicMellin_cross_local (f g : E F S) (z : ℂ) (hz : 1 < z.re) :
    idelicZetaIntegral F η (GlobalBruhat.algebraicEquiv F f.val).val
        (compactIdeleClassCharacter F ω) z * L F μ S (τ F ω S hs hu) g z =
      idelicZetaIntegral F η (GlobalBruhat.algebraicEquiv F g.val).val
        (compactIdeleClassCharacter F ω) z * L F μ S (τ F ω S hs hu) f z := by
  obtain ⟨T, hT, hST, hTsurj, _, hcover⟩ := exists_ideleBlock_tower F S
  let LS := L F μ S (τ F ω S hs hu)
  have hint (a : E F S) : Integrable (globalMellinIntegrand F ω a.val z) η :=
    idelicZeta_integrable F η a.val _ (compactIdeleClassCharacter_unitary F ω) z hz
  have hlim (a : E F S) :
      Tendsto (fun n ↦ ∫ x in (sIdeleBlock F (T n) : Set (Idele F)),
        globalMellinIntegrand F ω a.val z x ∂η) atTop
        (𝓝 (∫ x, globalMellinIntegrand F ω a.val z x ∂η)) := by
    have hmono : Monotone (fun n ↦ (sIdeleBlock F (T n) : Set (Idele F))) := by
      intro m n hm x hx
      exact (sIdeleTransition F (hT hm) ⟨x, hx⟩).property
    have h := tendsto_setIntegral_of_monotone
      (fun n ↦ (sIdeleBlock_open F (T n)).measurableSet) hmono (hint a).integrableOn
    rwa [hcover, Measure.restrict_univ] at h
  have hfinite (n : ℕ) :
      (∫ x in (sIdeleBlock F (T n) : Set (Idele F)), globalMellinIntegrand F ω f.val z x ∂η) * LS g z =
        (∫ x in (sIdeleBlock F (T n) : Set (Idele F)), globalMellinIntegrand F ω g.val z x ∂η) * LS f z := by
    let U := T n
    have hSU : S ⊆ U := hST n
    have hUs := hTsurj n
    have huU : globalNormOneCharacter F ω ∈ (sUnramified F U : Set (QuasiCharacter (IdeleClass F))) := by
      apply (mem_sUnramified_iff F U _).mpr
      intro v hv u
      exact (mem_sUnramified_iff F S _).mp hu v (fun h ↦ hv (hSU h)) u
    let τU := τ F ω U hUs huU
    let ρ := sLocalZetaProductMeasure F U (fun v ↦ μ v.val) (archimedeanMultiplicativeHaar F)
    letI : ρ.IsHaarMeasure :=
      sLocalZetaProductMeasure_isHaar F U (fun v ↦ μ v.val) (archimedeanMultiplicativeHaar F)
    obtain ⟨C, hC⟩ := globalMellin_block_integral_eq_smul F η ω U hUs huU ρ
    let D := sLocalMellinPaddingDenominator F S (sLocalFiniteZetaPhases F U τU) z
    let M := sLocalMellinPaddingHaarMass F μ S U
    have hp : 0 < z.re := zero_lt_one.trans hz
    have hD : D ≠ 0 := Finset.prod_ne_zero_iff.mpr fun v _ ↦
      finiteZetaDenominator_ne_zero_of_pos F v.val.val (sLocalFiniteZetaPhases F U τU v.val) z hp
    have he (a : E F S) :
        (∫ x in (sIdeleBlock F U : Set (Idele F)), globalMellinIntegrand F ω a.val z x ∂η) =
          (C : ℂ) * (D⁻¹ * M * LS a z) := by
      let b := sLocalBruhatTransition F hSU a
      have heq := hC b z
      change (∫ x in (sIdeleBlock F U : Set (Idele F)), globalMellinIntegrand F ω a.val z x ∂η) =
        C • sLocalIdelicZetaIntegral F U ρ τU b z at heq
      rw [← (sLocalIdelicZeta_meromorphic_continuation F U (fun v ↦ μ v.val) τU b).2 hp] at heq
      rw [heq, Complex.real_smul]
      have h := sLocalProductZetaContinued_global_pad_right F ω S hs hu μ hSU hUs huU a z hp
      change D * L F μ U τU b z = M * LS a z at h
      have hn := congrArg ((D⁻¹ : ℂ) * ·) h
      rw [← mul_assoc, inv_mul_cancel₀ hD, one_mul, ← mul_assoc] at hn
      exact congrArg ((C : ℂ) * ·) hn
    rw [he f, he g]
    ring
  exact tendsto_nhds_unique ((hlim f).mul tendsto_const_nhds)
    (((hlim g).mul tendsto_const_nhds).congr' (.of_forall fun n ↦ (hfinite n).symm))

local instance : MeasurableSpace (normOneIdeleClass F) := borel _
local instance : BorelSpace (normOneIdeleClass F) := ⟨rfl⟩
local instance : MeasurableSpace (IdeleClass F) := borel _
local instance : BorelSpace (IdeleClass F) := ⟨rfl⟩
local instance (T : Finset (Place F)) : MeasurableSpace (SIdeleQuotient F T) := borel _
local instance (T : Finset (Place F)) : BorelSpace (SIdeleQuotient F T) := ⟨rfl⟩

variable (ν : Measure (normOneIdeleClass F)) [ν.IsHaarMeasure]
variable (hν : IsWeilQuotientMeasure (principalIdeles F) η Measure.count (globalClassMeasure F ν))

private abbrev ZG (f : E F S) :=
  globalZetaContinued F ν f.val (compactIdeleClassCharacter F ω) 0

private abbrev Z (f : GlobalBruhat F) :=
  globalZetaContinued F ν f (compactIdeleClassCharacter F ω) 0

private abbrev NS (f : E F S) :=
  sLocalEulerNormalizedMellin F S (fun v ↦ μ v.val) (τ F ω S hs hu) f

include hν in
/-- The global and local continuations remain proportional as germs at
every center. -/
theorem globalContinuedMellin_cross_local (f g : E F S) (c : ℂ) :
    (ZG F ω S ν f * L F μ S (τ F ω S hs hu) g) =ᶠ[𝓝[≠] c]
      (ZG F ω S ν g * L F μ S (τ F ω S hs hu) f) := by
  let χ := compactIdeleClassCharacter F ω
  have hc := compactIdeleClassCharacter_unitary F ω
  have hG (a : E F S) : Meromorphic (ZG F ω S ν a) :=
    fun z ↦ (globalZetaContinued_meromorphic F ν a.val χ hc 0) z (mem_univ _)
  have hL (a : E F S) : Meromorphic (L F μ S (τ F ω S hs hu) a) :=
    sLocalProductZetaContinued_meromorphic F S (fun v ↦ μ v.val) _ _ _ a
  refine boundedPoleMellinSpace_unique_germs
    (D := {z : ℂ | 1 < z.re})
    (isOpen_lt continuous_const Complex.continuous_re)
    ⟨2, show (1 : ℝ) < (2 : ℂ).re by norm_num⟩
    (fun z ↦ (hG f z).mul (hL g z)) (fun z ↦ (hG g z).mul (hL f z)) ?_ c
  intro z hz
  have he (a : E F S) : ZG F ω S ν a z =
      idelicZetaIntegral F η (GlobalBruhat.algebraicEquiv F a.val).val χ z :=
    globalZetaContinued_eq_idelic F η ν hν a.val χ hc (κ := 0) Complex.zero_re
      (fun t ↦ by simp [χ]) z hz
  change ZG F ω S ν f z * L F μ S (τ F ω S hs hu) g z =
    ZG F ω S ν g z * L F μ S (τ F ω S hs hu) f z
  rw [he f, he g]
  exact globalIdelicMellin_cross_local F η ω S hs hu μ f g z hz

include hν in
/-- Global zeta values and the normalized local numerators satisfy the
same cross-product identity at every meromorphic germ. -/
theorem globalContinuedMellin_cross_normalized (f g : E F S) (c : ℂ) :
    (ZG F ω S ν f * NS F ω S hs hu μ g) =ᶠ[𝓝[≠] c]
      ZG F ω S ν g * NS F ω S hs hu μ f := by
  let σ := τ F ω S hs hu
  let D := sLocalEulerDenominator F S σ
  filter_upwards [globalContinuedMellin_cross_local F η ω S hs hu μ ν hν f g c,
    sLocalEulerNormalizedMellin_eq_germ F S (fun v ↦ μ v.val) σ f c,
    sLocalEulerNormalizedMellin_eq_germ F S (fun v ↦ μ v.val) σ g c] with z hz hf hg
  change ZG F ω S ν f z * L F μ S σ g z = ZG F ω S ν g z * L F μ S σ f z at hz
  change NS F ω S hs hu μ f z = D z * L F μ S σ f z at hf
  change NS F ω S hs hu μ g z = D z * L F μ S σ g z at hg
  change ZG F ω S ν f z * NS F ω S hs hu μ g z =
    ZG F ω S ν g z * NS F ω S hs hu μ f z
  rw [hf, hg, mul_left_comm (ZG F ω S ν f z), mul_left_comm (ZG F ω S ν g z), hz]

omit [∀ v : Place F, MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : Place F, BorelSpace (v.adicCompletion F)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ] in
private theorem globalMellin_zero_of_order_top (f : GlobalBruhat F) (c : ℂ)
    (htop : meromorphicOrderAt (Z F ω ν f) c = ⊤) : ∀ z, Z F ω ν f z = 0 := by
  let X := Z F ω ν f
  let χ := compactIdeleClassCharacter F ω
  have hχ := compactIdeleClassCharacter_unitary F ω
  have hm : MeromorphicOn X univ := globalZetaContinued_meromorphic F ν f χ hχ 0
  have htop' (z : ℂ) : meromorphicOrderAt X z = ⊤ := by
    by_contra hn
    exact (hm.meromorphicOrderAt_ne_top_of_isPreconnected isPreconnected_univ
      (mem_univ z) (mem_univ c) hn) htop
  apply globalZetaContinued_zero_of_halfPlane F ν f ω
  intro z hz
  have h0 : z + 0 ≠ 0 := by
    intro h
    simp at h
    norm_num [h] at hz
  have h1 : z + 0 - 1 ≠ 0 := by
    intro h
    have hz1 : z = 1 := by simpa using sub_eq_zero.mp h
    simp [hz1] at hz
  have ha : AnalyticAt ℂ X z := globalZetaContinued_analyticAt F ν f χ hχ 0 z h0 h1
  exact ((ha.continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE continuousAt_const).mp
    (meromorphicOrderAt_eq_top_iff.mp (htop' z))).eq_of_nhds

include hν in
/-- A test with nonzero constant normalized Mellin numerator has finite
global meromorphic order at every center. -/
theorem globalMellin_reference_order_ne_top (r : E F S) (C : ℂ) (hc : C ≠ 0)
    (hr : NS F ω S hs hu μ r = fun _ ↦ C) (c : ℂ) :
    meromorphicOrderAt (ZG F ω S ν r) c ≠ ⊤ := by
  intro htop
  have hzero := globalMellin_zero_of_order_top F ω ν r.val c htop
  have hk := (mem_globalIdelicZetaComponentKernel F η ν hν ω r.val).mpr hzero
  let ρ := sLocalZetaProductMeasure F S (fun v ↦ μ v.val) (archimedeanMultiplicativeHaar F)
  letI : ρ.IsHaarMeasure :=
    sLocalZetaProductMeasure_isHaar F S (fun v ↦ μ v.val) (archimedeanMultiplicativeHaar F)
  obtain ⟨νS, hνS, hWS⟩ := sLocalClassHaar_exists_weil F S ρ
  letI := hνS
  let σ := τ F ω S hs hu
  let M := sLocalHomogeneousThetaKernel F S νS σ
  have hq : M.mkQ r = 0 := by
    apply (sLocalHomogeneousThetaToGlobal_isClosedEmbedding F η ω S hs hu νS).injective
    rw [map_zero]
    exact (DFunLike.congr_fun (sLocalHomogeneousThetaToGlobal_comp F η ω S hs hu νS)
      ((sLocalThetaOperator F S).ker.mkQ r)).trans
        ((Submodule.Quotient.mk_eq_zero _).mpr hk)
  have hmem := (Submodule.Quotient.mk_eq_zero M).mp hq
  have hL0 := (sLocalHomogeneousTheta_zero_iff_meromorphicZeta F S (fun v ↦ μ v.val) νS hWS σ r).mp
    ((mem_sLocalHomogeneousThetaKernel_iff F S νS σ r).mp hmem)
  change Submodule.Quotient.mk (p := zeroMeromorphicGerms)
    (⟨L F μ S σ r, sLocalProductZetaContinued_meromorphic F S (fun v ↦ μ v.val) σ _ _ r⟩ :
      meromorphicRepresentatives) = 0 at hL0
  rw [Submodule.Quotient.mk_eq_zero] at hL0
  change ∀ z : ℂ, L F μ S σ r =ᶠ[𝓝[≠] z] 0 at hL0
  have he : NS F ω S hs hu μ r =ᶠ[𝓝[≠] (0 : ℂ)] 0 := by
    filter_upwards [hL0 0, sLocalEulerNormalizedMellin_eq_germ F S (fun v ↦ μ v.val) σ r 0]
      with w hL hN
    change sLocalEulerNormalizedMellin F S (fun v ↦ μ v.val) σ r w = 0
    exact hN.trans (mul_eq_zero.mpr (Or.inr hL))
  rw [hr] at he
  obtain ⟨_, he'⟩ := he.exists
  exact hc he'

include hν in
/-- The raw global order differs from the pole-cleared local order by
the global continuation of an actual Euler reference test. -/
theorem exists_globalMellin_order_reference :
    ∃ (r : E F S) (C : ℂ), C ≠ 0 ∧
      NS F ω S hs hu μ r = (fun _ ↦ C) ∧
      (∀ c, meromorphicOrderAt (ZG F ω S ν r) c ≠ ⊤) ∧
      ∀ (f : E F S) (c : ℂ), meromorphicOrderAt (ZG F ω S ν f) c =
        meromorphicOrderAt (ZG F ω S ν r) c + meromorphicOrderAt (NS F ω S hs hu μ f) c := by
  let σ := τ F ω S hs hu
  obtain ⟨r, C, hc, hr⟩ :=
    exists_sLocalEulerNormalizedMellin_constant F S (fun v ↦ μ v.val) σ
  refine ⟨r, C, hc, hr, globalMellin_reference_order_ne_top F η ω S hs hu μ ν hν r C hc hr,
    fun f c ↦ ?_⟩
  let G := ZG F ω S ν
  let N := NS F ω S hs hu μ
  have he := globalContinuedMellin_cross_normalized F η ω S hs hu μ ν hν f r c
  change G f * N r =ᶠ[𝓝[≠] c] G r * N f at he
  change N r = _ at hr
  rw [hr] at he
  have ha (a : E F S) : MeromorphicAt (G a) c :=
    globalZetaContinued_meromorphic F ν a.val _ (compactIdeleClassCharacter_unitary F ω) 0 c (mem_univ _)
  have hN : MeromorphicAt (N f) c :=
    (sLocalEulerNormalizedMellin_entire F S (fun v ↦ μ v.val) σ f c (mem_univ _)).meromorphicAt
  have hh := meromorphicOrderAt_congr he
  change meromorphicOrderAt (G f * fun _ ↦ C) c = meromorphicOrderAt (G r * N f) c at hh
  rw [meromorphicOrderAt_mul (ha f) (MeromorphicAt.const C c),
    meromorphicOrderAt_mul (ha r) hN, meromorphicOrderAt_const, ite_eq_right hc, add_zero] at hh
  exact hh

local instance (T : Finset (Place F)) : MeasurableSpace (SAdeles F T)ˣ := borel _
local instance (T : Finset (Place F)) : BorelSpace (SAdeles F T)ˣ := ⟨rfl⟩

variable (νS : Measure (SLocalThetaNormOne F S)) [νS.IsHaarMeasure]
variable (hνS : IsWeilQuotientMeasure (sUnitImage F S)
  (sLocalZetaProductMeasure F S (fun v ↦ μ v.val) (archimedeanMultiplicativeHaar F))
  Measure.count (sLocalClassHaar F S νS))

include hν hνS in
/-- Corrected Proposition 7.2.2.1. The absolute order bound for the
continued global transform uses the actual global Euler reference order
at each selected center. The same reference works for every test and
every subset of places in this stage. -/
theorem exists_globalMellin_selected_order_iff_principalValue_range :
    ∃ (r : E F S) (C : ℂ), C ≠ 0 ∧
      NS F ω S hs hu μ r = (fun _ ↦ C) ∧
      (∀ c, meromorphicOrderAt (ZG F ω S ν r) c ≠ ⊤) ∧
      ∀ (W : Finset S) (f : E F S),
        let σ := τ F ω S hs hu
        let M := sLocalHomogeneousThetaKernel F S νS σ
        let coefficients := ∀ c : ℂ, 0 < sLocalSelectedFinitePoleCount F S σ W c →
          ∀ k : ℕ, sLocalPoleCount F S σ c - sLocalSelectedFinitePoleCount F S σ W c < k →
            k ≤ sLocalPoleCount F S σ c → sLocalLaurentCoeff F S (fun v ↦ μ v.val) σ c k f = 0
        let globalBound := ∀ c : ℂ, 0 < sLocalSelectedFinitePoleCount F S σ W c →
          meromorphicOrderAt (ZG F ω S ν r) c +
              (sLocalSelectedFinitePoleCount F S σ W c : WithTop ℤ) ≤
            meromorphicOrderAt (ZG F ω S ν f) c
        let localRange := M.mkQ f ∈ (sLocalFiniteNonzeroTestSubspace F S W).map M.mkQ
        let globalRange := sLocalHomogeneousThetaToGlobal F η ω S hs hu νS (M.mkQ f) ∈
          range (fun g : GlobalBruhat F ↦
            (globalIdelicZetaComponentKernel F η ω).mkQ
              (globalWeilPrincipalValues F (W.map ⟨Subtype.val, Subtype.val_injective⟩) g))
        (coefficients ↔ globalBound) ∧ (localRange ↔ coefficients) ∧ (globalRange ↔ localRange) := by
  obtain ⟨r, C, hc, hr, hRef, hOrder⟩ := exists_globalMellin_order_reference F η ω S hs hu μ ν hν
  refine ⟨r, C, hc, hr, hRef, fun W f ↦ ⟨?_, ?_, ?_⟩⟩
  · apply forall_congr'
    intro c
    apply imp_congr_right
    intro _
    let σ := τ F ω S hs hu
    let d := sLocalPoleCount F S σ c
    let t := sLocalSelectedFinitePoleCount F S σ W c
    let a (k : ℕ) := sLocalLaurentCoeff F S (fun v ↦ μ v.val) σ c k f
    have hfiniteBand : (∀ k > d - t, a k = 0) ↔ (∀ k > d - t, k ≤ d → a k = 0) := by
      refine ⟨fun h k hk _ ↦ h k hk, fun h k hk ↦ ?_⟩
      by_cases hkd : k ≤ d
      · exact h k hk hkd
      · have hbound := sLocalZeta_poleOrder_le_euler F S (fun v ↦ μ v.val) σ f c
        rw [sLocalEulerFactor_order F S σ c, sLocalAllowedPoleOrder_eq_count F S σ c] at hbound
        exact (sLocalLaurentCoeff_vanish_iff F S (fun v ↦ μ v.val) σ c d f).mpr
          hbound k (lt_of_not_ge hkd)
    rw [hOrder f c, WithTop.add_le_add_iff_left (hRef c)]
    exact hfiniteBand.symm.trans
      (sLocal_removedLaurent_iff_normalized_order F S (fun v ↦ μ v.val) σ W f c)
  · exact sLocal_mk_mem_selected_finiteImage_iff_removed_coefficients F S
      (fun v ↦ μ v.val) νS hνS (τ F ω S hs hu) W f
  · exact sLocalHomogeneousThetaToGlobal_mem_principalValue_range_iff F η ω S hs hu νS μ hνS W _

include hν hνS in
private theorem stage_globalWeilPrincipalValues_order (W : Finset S) (f : E F S) (c : ℂ) :
    meromorphicOrderAt (ZG F ω S ν (sLocalWeilPrincipalValues F S W f)) c =
      (sLocalSelectedFinitePoleCount F S (τ F ω S hs hu) W c : WithTop ℤ) +
        meromorphicOrderAt (ZG F ω S ν f) c := by
  obtain ⟨r, _, _, _, _, hOrder⟩ := exists_globalMellin_order_reference F η ω S hs hu μ ν hν
  let σ := τ F ω S hs hu
  let D := sLocalEulerDenominator F S σ
  have hN (g : E F S) : meromorphicOrderAt (NS F ω S hs hu μ g) c =
      meromorphicOrderAt D c + meromorphicOrderAt (L F μ S σ g) c :=
    (meromorphicOrderAt_congr (sLocalEulerNormalizedMellin_eq_germ F S (fun v ↦ μ v.val) σ g c)).trans
      (meromorphicOrderAt_mul (sLocalEulerDenominator_analytic F S σ c).meromorphicAt
        (sLocalProductZetaContinued_meromorphic F S (fun v ↦ μ v.val) σ _ _ g c))
  let p := sLocalWeilPrincipalValues F S W f
  rw [hOrder p c, hOrder f c, hN p, hN f]
  have he := sLocalWeilPrincipalValues_order F S (fun v ↦ μ v.val) νS hνS σ W f c
  change meromorphicOrderAt (L F μ S σ p) c = _ at he
  rw [he]
  ac_rfl

include μ hν in
/-- The actual global order shifts by the selected finite pole count, for
every global test, including tests initially represented on another stage. -/
theorem globalWeilPrincipalValues_order (W : Finset S) (g : GlobalBruhat F) (c : ℂ) :
    meromorphicOrderAt (Z F ω ν (globalWeilPrincipalValues F
      (W.map ⟨Subtype.val, Subtype.val_injective⟩) g)) c =
      (sLocalSelectedFinitePoleCount F S (τ F ω S hs hu) W c : WithTop ℤ) +
        meromorphicOrderAt (Z F ω ν g) c := by
  obtain ⟨A, a, ha⟩ := globalBruhat_exhausted F g
  obtain ⟨B, hB⟩ := sIdeleClass_eventually_surjective F
  let U := (S ∪ A) ∪ B
  have hSU : S ⊆ U := Finset.subset_union_left.trans Finset.subset_union_left
  have hAU : A ⊆ U := Finset.subset_union_right.trans Finset.subset_union_left
  have hU := hB U Finset.subset_union_right
  have huU : globalNormOneCharacter F ω ∈ (sUnramified F U : Set (QuasiCharacter (IdeleClass F))) :=
    (mem_sUnramified_iff F U _).mpr fun v hv u ↦
      (mem_sUnramified_iff F S _).mp hu v (fun h ↦ hv (hSU h)) u
  let ρ := sLocalZetaProductMeasure F U (fun v ↦ μ v.val) (archimedeanMultiplicativeHaar F)
  letI : ρ.IsHaarMeasure :=
    sLocalZetaProductMeasure_isHaar F U (fun v ↦ μ v.val) (archimedeanMultiplicativeHaar F)
  obtain ⟨νU, hνU, hweil⟩ := sLocalClassHaar_exists_weil F U ρ
  letI := hνU
  let e : S ↪ U := ⟨fun v ↦ ⟨v.val, hSU v.property⟩,
    fun _ _ h ↦ Subtype.ext (congrArg (fun w : U ↦ w.val) h)⟩
  let b := sLocalBruhatTransition F hAU a
  have hb : b.val = g := ha
  have hV : (W.map e).map (⟨Subtype.val, Subtype.val_injective⟩ : U ↪ _) =
      W.map (⟨Subtype.val, Subtype.val_injective⟩ : S ↪ _) := by
    rw [Finset.map_map]
    rfl
  have he := stage_globalWeilPrincipalValues_order F η ω U hU huU μ ν hν νU hweil (W.map e) b c
  have hp := globalWeilPrincipalValues_stage F U (W.map e) b
  have hcount := sLocalSelectedFinitePoleCount_global_pad F S ω hs hu hSU hU huU W c
  change sLocalSelectedFinitePoleCount F U (τ F ω U hU huU) (W.map e) c = _ at hcount
  change meromorphicOrderAt (Z F ω ν (sLocalWeilPrincipalValues F U (W.map e) b).val) c =
    (sLocalSelectedFinitePoleCount F U (τ F ω U hU huU) (W.map e) c : WithTop ℤ) +
      meromorphicOrderAt (Z F ω ν b.val) c at he
  rw [← hp, hV, hcount, hb] at he
  exact he

include hν in
omit [∀ v : Place F, MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : Place F, BorelSpace (v.adicCompletion F)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ] in
theorem globalMellin_eq_of_mkQ_eq {f g : GlobalBruhat F}
    (h : (globalIdelicZetaComponentKernel F η ω).mkQ f =
      (globalIdelicZetaComponentKernel F η ω).mkQ g) :
    Z F ω ν f = Z F ω ν g := by
  have hk := (Submodule.Quotient.eq _).mp h
  have he := (mem_globalIdelicZetaComponentKernel F η ν hν ω (f - g)).mp hk
  funext z
  have hz := he z
  change Z F ω ν (f - g) z = 0 at hz
  simp only [Z, ← globalContinuedMellinEval_apply, map_sub, sub_eq_zero] at hz ⊢
  exact hz

omit [∀ v : Place F, MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : Place F, BorelSpace (v.adicCompletion F)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ] in
/-- The two possible global poles are absent if the character is
nontrivial or if both test evaluations are zero. -/
theorem globalMellin_nonneg_orders_iff (f : GlobalBruhat F) :
    (0 ≤ meromorphicOrderAt (Z F ω ν f) 0 ∧ 0 ≤ meromorphicOrderAt (Z F ω ν f) 1) ↔
      ω ≠ 1 ∨ GlobalBruhat.polarEvaluation F f = 0 := by
  let χ := compactIdeleClassCharacter F ω
  let a := ∫ k : normOneIdeleClass F, (χ k.val : ℂ) ∂ν
  let p := GlobalBruhat.polarEvaluation F f
  have hp := globalZetaContinued_pole_order F ν f χ (compactIdeleClassCharacter_unitary F ω) 0
  have he0 : p.1 = (GlobalBruhat.algebraicEquiv F f).val 0 := rfl
  have he1 : p.2 = (GlobalBruhat.algebraicEquiv F (GlobalBruhat.fourier F f)).val 0 := rfl
  have h0 : if a * p.1 = 0 then AnalyticAt ℂ (Z F ω ν f) 0
      else meromorphicOrderAt (Z F ω ν f) 0 = (-1 : ℤ) := by
    rw [he0]
    simpa only [neg_zero] using hp.1
  have h1 : if a * p.2 = 0 then AnalyticAt ℂ (Z F ω ν f) 1
      else meromorphicOrderAt (Z F ω ν f) 1 = (-1 : ℤ) := by
    rw [he1]
    simpa only [sub_zero] using hp.2
  have hneg : ¬ (0 : WithTop ℤ) ≤ ((-1 : ℤ) : WithTop ℤ) :=
    fun h ↦ (by decide : ¬ (0 : ℤ) ≤ -1) (WithTop.coe_le_coe.mp h)
  have e0 : 0 ≤ meromorphicOrderAt (Z F ω ν f) 0 ↔ a * p.1 = 0 := by
    split_ifs at h0 with h
    · exact iff_of_true h0.meromorphicOrderAt_nonneg h
    · exact iff_of_false (fun he ↦ hneg (h0 ▸ he)) h
  have e1 : 0 ≤ meromorphicOrderAt (Z F ω ν f) 1 ↔ a * p.2 = 0 := by
    split_ifs at h1 with h
    · exact iff_of_true h1.meromorphicOrderAt_nonneg h
    · exact iff_of_false (fun he ↦ hneg (h1 ▸ he)) h
  rw [e0, e1]
  have hmass : (ν.real univ : ℂ) ≠ 0 := by
    letI := normOneIdeleClass_compact F
    letI : IsFiniteMeasure ν := ⟨isCompact_univ.measure_lt_top⟩
    exact_mod_cast (measureReal_univ_pos (μ := ν)).ne'
  change a * p.1 = 0 ∧ a * p.2 = 0 ↔ ω ≠ 1 ∨ p = 0
  have ha : a = if ω = 1 then (ν.real univ : ℂ) else 0 :=
    compactIdeleClassCharacter_integral F ν ω
  by_cases hω : ω = 1
  · rw [ha, ite_eq_left hω]
    simp only [hω, ne_eq, not_true_eq_false, false_or,
      mul_eq_zero, hmass, false_or]
    exact ⟨fun h ↦ Prod.ext h.1 h.2, fun h ↦ ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩⟩
  · simp [ha, hω]

include hs hu hν in
omit [∀ v : Place F, MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : Place F, BorelSpace (v.adicCompletion F)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ] in
/-- At a nontrivial character every S-local homogeneous class has a
representative with both polar evaluations zero on that same stage. -/
theorem exists_sLocal_polarEvaluation_zero_same_globalClass (hω : ω ≠ 1) (f : E F S) :
    ∃ g : E F S, GlobalBruhat.polarEvaluation F g.val = 0 ∧
      (globalIdelicZetaComponentKernel F η ω).mkQ g.val =
        (globalIdelicZetaComponentKernel F η ω).mkQ f.val := by
  obtain ⟨k, hk⟩ : ∃ k : normOneIdeleClass F, ω k ≠ 1 := by
    by_contra! h
    apply hω
    ext k
    exact congrArg Subtype.val (h k)
  obtain ⟨q, hq⟩ := hs k.val
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
  change ideleClassMap F a.val = k.val at hq
  let u := (sBlockUnitProduct F S a).1
  let b := sLocalEmbed F S u
  have hb : (sBlockUnitProduct F S b).1 = u := by
    have he := (sBlockUnitProduct F S).apply_symm_apply (u, 1)
    have he' := congrArg Prod.fst he
    exact he'
  have hnorm : ideleNorm F b.val = 1 := by
    change sLocalIdeleNorm F S u = 1
    rw [show sLocalIdeleNorm F S u = ideleNorm F a.val from sBlock_norm_eq F S a,
      ← ideleClassNorm_mk, hq]
    exact k.property
  let j : normOneIdeleClass F := ⟨ideleClassMap F b.val, by
    change ideleClassNorm F (ideleClassMap F b.val) = 1
    rwa [ideleClassNorm_mk]⟩
  have hp := (sLocalZetaWeight_zero_global_block F S ω hs hu b).symm
  rw [hb, sLocalZetaWeight_zero_global_block F S ω hs hu a, hq] at hp
  have hc (x : normOneIdeleClass F) : globalNormOneCharacter F ω x.val = (ω x : ℂ) := by
    change (compactIdeleClassCharacter F ω x.val : ℂ) = _
    exact compactIdeleClassCharacter_apply_normOne F ω x
  change globalNormOneCharacter F ω j.val = globalNormOneCharacter F ω k.val at hp
  rw [hc, hc] at hp
  let C : ℂ := (ω j : ℂ)
  have hC : C ≠ 1 := fun h ↦ hk (Circle.coe_injective (by simpa [C, ← hp] using h))
  let t := sLocalBruhatLeftTranslate F S u f
  let g := (1 - C)⁻¹ • (t - C • f)
  have htr : t.val = GlobalBruhat.leftTranslate F b.val f.val := rfl
  have hpole : GlobalBruhat.polarEvaluation F t.val = GlobalBruhat.polarEvaluation F f.val := by
    rw [htr, polarEvaluation_leftTranslate, hnorm, one_smul]
  have hg : GlobalBruhat.polarEvaluation F g.val = GlobalBruhat.polarEvaluation F f.val := by
    change GlobalBruhat.polarEvaluation F ((1 - C)⁻¹ • (t.val - C • f.val)) = _
    rw [map_smul, map_sub, map_smul, hpole]
    let p := GlobalBruhat.polarEvaluation F f.val
    change (1 - C)⁻¹ • (p - C • p) = p
    have he : (1 - C) • p = p - C • p := by rw [sub_smul, one_smul]
    rw [← he, smul_smul,
      inv_mul_cancel₀ (sub_ne_zero.mpr (Ne.symm hC)), one_smul]
  have hkg : g.val ∈ globalIdelicZetaComponentKernel F η ω := by
    apply (mem_globalIdelicZetaComponentKernel F η ν hν ω g.val).mpr
    apply (adelicHomogeneousTheta_zero_iff_continuedZeta F ν g.val ω).mp
    have he : globalHomogeneousThetaOperator F ν ω g.val = 0 := by
      change globalHomogeneousThetaOperator F ν ω ((1 - C)⁻¹ • (t.val - C • f.val)) = 0
      rw [map_smul, map_sub, map_smul, htr, globalHomogeneousThetaOperator_translate F ν ω j b.val rfl]
      change (1 - C)⁻¹ • (C • _ - C • _) = 0
      rw [sub_self, smul_zero]
    exact fun x ↦ congrFun he x
  refine ⟨f - g, ?_, ?_⟩
  · change GlobalBruhat.polarEvaluation F (f.val - g.val) = 0
    rw [map_sub, hg, sub_self]
  · change (globalIdelicZetaComponentKernel F η ω).mkQ (f.val - g.val) = _
    have hq : (globalIdelicZetaComponentKernel F η ω).mkQ g.val = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr hkg
    rw [map_sub, hq, sub_zero]

include μ hν in
private theorem polar_bounds_of_principalValue {f g : GlobalBruhat F} (W : Finset S)
    (hq : (globalIdelicZetaComponentKernel F η ω).mkQ
        (globalWeilPrincipalValues F (W.map ⟨Subtype.val, Subtype.val_injective⟩) g) =
      (globalIdelicZetaComponentKernel F η ω).mkQ f) (c : ℂ) :
    (sLocalSelectedFinitePoleCount F S (τ F ω S hs hu) W c : WithTop ℤ) ≤
      meromorphicOrderAt (Z F ω ν f) c ↔ 0 ≤ meromorphicOrderAt (Z F ω ν g) c := by
  have he := globalMellin_eq_of_mkQ_eq F η ω ν hν hq
  rw [← he, globalWeilPrincipalValues_order F η ω S hs hu μ ν hν W g c]
  simpa only [add_zero] using
    (WithTop.add_le_add_iff_left (WithTop.natCast_ne_top
      (sLocalSelectedFinitePoleCount F S (τ F ω S hs hu) W c)) :
      _ + 0 ≤ _ + meromorphicOrderAt (Z F ω ν g) c ↔ _)

include hs hu μ hν in
private theorem globalWeilPrincipalValues_mkQ_congr (W : Finset S) {f g : GlobalBruhat F}
    (h : (globalIdelicZetaComponentKernel F η ω).mkQ f =
      (globalIdelicZetaComponentKernel F η ω).mkQ g) :
    (globalIdelicZetaComponentKernel F η ω).mkQ
        (globalWeilPrincipalValues F (W.map ⟨Subtype.val, Subtype.val_injective⟩) f) =
      (globalIdelicZetaComponentKernel F η ω).mkQ
        (globalWeilPrincipalValues F (W.map ⟨Subtype.val, Subtype.val_injective⟩) g) := by
  let Q := globalIdelicZetaComponentKernel F η ω
  let P := globalWeilPrincipalValues F (W.map ⟨Subtype.val, Subtype.val_injective⟩)
  have hz := (mem_globalIdelicZetaComponentKernel F η ν hν ω (f - g)).mp
    ((Submodule.Quotient.eq Q).mp h)
  have htop : meromorphicOrderAt (Z F ω ν (f - g)) 2 = ⊤ :=
    meromorphicOrderAt_eq_top_iff.mpr (.of_forall hz)
  have ho : meromorphicOrderAt (Z F ω ν (P (f - g))) 2 = ⊤ := by
    change meromorphicOrderAt (Z F ω ν (globalWeilPrincipalValues F
      (W.map ⟨Subtype.val, Subtype.val_injective⟩) (f - g))) 2 = ⊤
    rw [globalWeilPrincipalValues_order F η ω S hs hu μ ν hν W, htop, WithTop.add_top]
  have hmem := (mem_globalIdelicZetaComponentKernel F η ν hν ω (P (f - g))).mpr
    (globalMellin_zero_of_order_top F ω ν _ 2 ho)
  apply (Submodule.Quotient.eq Q).mpr
  rwa [map_sub] at hmem

omit [∀ v : Place F, MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : Place F, BorelSpace (v.adicCompletion F)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ] in
/-- The two evaluations of the padded test are the evaluations at zero
on the S-adeles, using the genuine local Fourier compression. -/
theorem sLocalPolarEvaluation_zero_iff (f : E F S) :
    GlobalBruhat.polarEvaluation F f.val = 0 ↔
      sLocalBruhatRestriction F S f.val 0 = 0 ∧
      sLocalBruhatRestriction F S (sLocalFourierCompression F S f).val 0 = 0 := by
  have hpad : sLocalBruhatPad F S 0 = 0 := by
    apply Prod.ext
    · rfl
    · apply DFunLike.ext
      intro v
      change finiteCoordinateSplit F S ((0 : SAdeles F S).2, 0) v = 0
      rw [finiteCoordinateSplit_apply]
      split <;> rfl
  have hzero (g : GlobalBruhat F) :
      sLocalBruhatRestriction F S g 0 = GlobalBruhat.evaluation F 0 g := by
    change GlobalBruhat.evaluation F (sLocalBruhatPad F S 0) g = _
    rw [hpad]
  have hF :
      sLocalBruhatRestriction F S (sLocalFourierCompression F S f).val 0 =
        GlobalBruhat.evaluation F 0 (GlobalBruhat.fourier F f.val) := by
    change sLocalBruhatRestriction F S
      (sLocalBruhatCorestrict F S (GlobalBruhat.fourier F f.val)).val 0 = _
    rw [sLocalBruhatCorestrict_restrict, hzero]
  rw [hzero, hF]
  exact ⟨fun h ↦ ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩, fun h ↦ Prod.ext h.1 h.2⟩

include hs μ hν in
/-- The principal-value product sends the two-evaluation kernel into itself. -/
theorem globalWeilPrincipalValues_preserves_polar (W : Finset S) (f : GlobalBruhat F)
    (hf : GlobalBruhat.polarEvaluation F f = 0) :
    GlobalBruhat.polarEvaluation F
      (globalWeilPrincipalValues F (W.map ⟨Subtype.val, Subtype.val_injective⟩) f) = 0 := by
  let χ : PontryaginDual (normOneIdeleClass F) := 1
  have hc (q : IdeleClass F) : globalNormOneCharacter F χ q = 1 := by
    change (χ (ideleClassNormOnePart F q) : ℂ) = 1
    simp [χ]
  have huχ : globalNormOneCharacter F χ ∈ (sUnramified F S : Set (QuasiCharacter (IdeleClass F))) := by
    apply (mem_sUnramified_iff F S _).mpr
    intro v hv u
    exact hc _
  let p := globalWeilPrincipalValues F (W.map ⟨Subtype.val, Subtype.val_injective⟩) f
  have hfZ := (globalMellin_nonneg_orders_iff F χ ν f).mpr (Or.inr hf)
  have h (c : ℂ) (hc : 0 ≤ meromorphicOrderAt (Z F χ ν f) c) :
      0 ≤ meromorphicOrderAt (Z F χ ν p) c := by
    change 0 ≤ meromorphicOrderAt (Z F χ ν (globalWeilPrincipalValues F
      (W.map ⟨Subtype.val, Subtype.val_injective⟩) f)) c
    rw [globalWeilPrincipalValues_order F η χ S hs huχ μ ν hν W]
    exact add_nonneg (by positivity) hc
  exact ((globalMellin_nonneg_orders_iff F χ ν p).mp ⟨h 0 hfZ.1, h 1 hfZ.2⟩).resolve_left
    (not_not_intro rfl)

include hν hνS in
/-- Corrected Corollary 7.2.2.2. In addition to the ordinary finite
coefficient test, the continued global transform must have at least the
selected multiplicity at both possible polar centers. This ensures that
dividing by the selected multiplier preserves holomorphy there. -/
theorem exists_globalMellin_polar_selected_order_iff_principalValue_range :
    ∃ (r : E F S) (C : ℂ), C ≠ 0 ∧
      NS F ω S hs hu μ r = (fun _ ↦ C) ∧
      (∀ c, meromorphicOrderAt (ZG F ω S ν r) c ≠ ⊤) ∧
      ∀ (W : Finset S) (f : E F S),
        let σ := τ F ω S hs hu
        let M := sLocalHomogeneousThetaKernel F S νS σ
        let t (c : ℂ) := sLocalSelectedFinitePoleCount F S σ W c
        let coefficients := ∀ c : ℂ, 0 < t c →
          ∀ k : ℕ, sLocalPoleCount F S σ c - t c < k →
            k ≤ sLocalPoleCount F S σ c → sLocalLaurentCoeff F S (fun v ↦ μ v.val) σ c k f = 0
        let globalBound := ∀ c : ℂ, 0 < t c →
          meromorphicOrderAt (ZG F ω S ν r) c + (t c : WithTop ℤ) ≤
            meromorphicOrderAt (ZG F ω S ν f) c
        let polarBound := (t 0 : WithTop ℤ) ≤ meromorphicOrderAt (ZG F ω S ν f) 0 ∧
          (t 1 : WithTop ℤ) ≤ meromorphicOrderAt (ZG F ω S ν f) 1
        let localRange := M.mkQ f ∈ range
          (fun g : {g : E F S // GlobalBruhat.polarEvaluation F g.val = 0} ↦
            M.mkQ (sLocalWeilPrincipalValues F S W g.val))
        let globalRange := sLocalHomogeneousThetaToGlobal F η ω S hs hu νS (M.mkQ f) ∈
          range (fun g : (GlobalBruhat.polarEvaluation F).ker ↦
            (globalIdelicZetaComponentKernel F η ω).mkQ
              (globalWeilPrincipalValues F (W.map ⟨Subtype.val, Subtype.val_injective⟩) g.val))
        ((coefficients ∧ polarBound) ↔ (globalBound ∧ polarBound)) ∧
          (localRange ↔ (coefficients ∧ polarBound)) ∧ (globalRange ↔ localRange) := by
  obtain ⟨r, C, hC, hr, hRef, hProp⟩ :=
    exists_globalMellin_selected_order_iff_principalValue_range F η ω S hs hu μ ν hν νS hνS
  refine ⟨r, C, hC, hr, hRef, fun W f ↦ ?_⟩
  obtain ⟨hcoeff, hlocal, hglobal⟩ := hProp W f
  let M := sLocalHomogeneousThetaKernel F S νS (τ F ω S hs hu)
  let j := sLocalHomogeneousThetaToGlobal F η ω S hs hu νS
  let Q := (globalIdelicZetaComponentKernel F η ω).mkQ
  let P := sLocalWeilPrincipalValues F S W
  let R := globalWeilPrincipalValues F (W.map ⟨Subtype.val, Subtype.val_injective⟩)
  have hj (x : E F S) : j (M.mkQ x) = Q x.val :=
    DFunLike.congr_fun (sLocalHomogeneousThetaToGlobal_comp F η ω S hs hu νS)
      ((sLocalThetaOperator F S).ker.mkQ x)
  have hP (x : E F S) : R x.val = (P x).val := globalWeilPrincipalValues_stage F S W x
  have hinj := (sLocalHomogeneousThetaToGlobal_isClosedEmbedding F η ω S hs hu νS).injective
  have hbound (g : GlobalBruhat F) (eq : Q (R g) = Q f.val) (c : ℂ) :=
    polar_bounds_of_principalValue F η ω S hs hu μ ν hν W eq c
  have hp (g : GlobalBruhat F) (hg : GlobalBruhat.polarEvaluation F g = 0) :=
    (globalMellin_nonneg_orders_iff F ω ν g).mpr (Or.inr hg)
  dsimp only
  refine ⟨and_congr hcoeff Iff.rfl, ?_⟩
  suffices hpolar :
      M.mkQ f ∈ range (fun g : {g : E F S // GlobalBruhat.polarEvaluation F g.val = 0} ↦
        M.mkQ (P g.val)) ↔
      (∀ c : ℂ, 0 < sLocalSelectedFinitePoleCount F S (τ F ω S hs hu) W c →
        ∀ k : ℕ, sLocalPoleCount F S (τ F ω S hs hu) c -
          sLocalSelectedFinitePoleCount F S (τ F ω S hs hu) W c < k →
          k ≤ sLocalPoleCount F S (τ F ω S hs hu) c →
          sLocalLaurentCoeff F S (fun v ↦ μ v.val) (τ F ω S hs hu) c k f = 0) ∧
        (sLocalSelectedFinitePoleCount F S (τ F ω S hs hu) W 0 : WithTop ℤ) ≤
            meromorphicOrderAt (ZG F ω S ν f) 0 ∧
        (sLocalSelectedFinitePoleCount F S (τ F ω S hs hu) W 1 : WithTop ℤ) ≤
            meromorphicOrderAt (ZG F ω S ν f) 1 by
    refine ⟨hpolar, ?_⟩
    constructor
    · rintro ⟨g, hgq⟩
      have he : Q (R g.val) = Q f.val := hgq.trans (hj f)
      have ho : j (M.mkQ f) ∈ range (fun u : GlobalBruhat F ↦ Q (R u)) := ⟨g.val, hgq⟩
      have h0 := (hbound g.val he 0).mpr (hp g.val g.property).1
      have h1 := (hbound g.val he 1).mpr (hp g.val g.property).2
      exact hpolar.mpr ⟨hlocal.mp (hglobal.mp ho), h0, h1⟩
    · rintro ⟨⟨g, hg⟩, hgq⟩
      refine ⟨⟨g.val, hg⟩, ?_⟩
      change Q (R g.val) = j (M.mkQ f)
      rw [hP, ← hj, show M.mkQ (P g) = M.mkQ f from hgq]
  · constructor
    · rintro ⟨⟨g, hg⟩, hgq⟩
      have hq : M.mkQ (P g) = M.mkQ f := hgq
      have he : Q (R g.val) = Q f.val := by
        rw [hP, ← hj, hq, hj]
      have hm : M.mkQ f ∈ (sLocalFiniteNonzeroTestSubspace F S W).map M.mkQ := by
        refine ⟨P g, ?_, hq⟩
        rw [← sLocalWeilPrincipalValues_range_eq_nonzeroTestSubspace]
        exact ⟨g, rfl⟩
      exact ⟨hlocal.mp hm, (hbound g.val he 0).mpr (hp g.val hg).1,
        (hbound g.val he 1).mpr (hp g.val hg).2⟩
    · rintro ⟨hc, h0, h1⟩
      obtain ⟨y, hy, hyq⟩ := hlocal.mpr hc
      rw [← sLocalWeilPrincipalValues_range_eq_nonzeroTestSubspace] at hy
      obtain ⟨g, rfl⟩ := hy
      have hq : M.mkQ (P g) = M.mkQ f := hyq
      have he : Q (R g.val) = Q f.val := by
        rw [hP, ← hj, hq, hj]
      rcases (globalMellin_nonneg_orders_iff F ω ν g.val).mp
          ⟨(hbound g.val he 0).mp h0, (hbound g.val he 1).mp h1⟩ with hω | hg
      · obtain ⟨p, hp, hpq⟩ := exists_sLocal_polarEvaluation_zero_same_globalClass
          F η ω S hs hu ν hν hω g
        have hm : M.mkQ (P p) = M.mkQ (P g) := by
          apply hinj
          rw [hj, hj, ← hP, ← hP]
          exact globalWeilPrincipalValues_mkQ_congr F η ω S hs hu μ ν hν W hpq
        exact ⟨⟨p, hp⟩, hm.trans hq⟩
      · exact ⟨⟨g, hg⟩, hq⟩

end

end Masullo
