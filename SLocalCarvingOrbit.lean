import HomogeneousThetaPlaceLimit
import SLocalFlatComponents
import SLocalPaleyWiener

open Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped NumberField SchwartzMap

namespace Masullo
noncomputable section

variable (F : Type*) [Field F] [NumberField F]
variable (S : Finset (HeightOneSpectrum (𝓞 F)))

/-- The outside unit tensor is evaluated on ideles, with an indicator that
every finite place outside S has integral-unit coordinate. -/
def sLocalCarvingIdeleTest (f : sLocalBruhatImage F S) (g : Idele F) : ℂ :=
  (sIdeleBlock F S : Set (Idele F)).indicator
    (fun g ↦ sLocalBruhatRestriction F S f.val (sAdelesProjection F S g.val)) g

/-- The actual principal orbit sum of the test with outside unit factors. -/
def sLocalCarvingOrbitSum (f : sLocalBruhatImage F S) (g : Idele F) : ℂ :=
  ∑' t : Fˣ, sLocalCarvingIdeleTest F S f (principalIdele F t * g)

theorem sLocalCarvingOrbitSum_principal_mul (f : sLocalBruhatImage F S)
    (a : Fˣ) (g : Idele F) :
    sLocalCarvingOrbitSum F S f (principalIdele F a * g) = sLocalCarvingOrbitSum F S f g := by
  unfold sLocalCarvingOrbitSum
  simp only [← mul_assoc, ← map_mul]
  exact (Equiv.mulRight a).tsum_eq (fun t : Fˣ ↦ sLocalCarvingIdeleTest F S f (principalIdele F t * g))

/-- At an S-idele representative the outside unit factors select exactly
the S-units in the principal orbit. This holds on the entire block,
including representatives with nontrivial outside unit coordinates. -/
theorem sLocalCarvingOrbitSum_of_block (f : sLocalBruhatImage F S)
    (g : sIdeleBlock F S) :
    sLocalCarvingOrbitSum F S f g.val =
      sLocalThetaOnIdeles F S (sLocalBruhatRestriction F S f.val)
        (Units.map (sAdelesProjection F S).toMonoidHom g.val) := by
  classical
  let d := sUnitToField F S
  let b (t : Fˣ) := sLocalBruhatRestriction F S f.val
    (sAdelesProjection F S (principalIdele F t * g.val).val)
  have hmem (t : Fˣ) : principalIdele F t * g.val ∈ sIdeleBlock F S ↔ t ∈ d.range := by
    rw [Subgroup.mul_mem_cancel_right (sIdeleBlock F S) g.property]
    exact principalIdele_mem_sBlock F S t
  have hterm (t : Fˣ) :
      sLocalCarvingIdeleTest F S f (principalIdele F t * g.val) = (d.range : Set Fˣ).indicator b t := by
    unfold sLocalCarvingIdeleTest
    by_cases ht : t ∈ d.range
    · rw [indicator_of_mem ((hmem t).mpr ht), indicator_of_mem ht]
    · rw [indicator_of_notMem (fun h ↦ ht ((hmem t).mp h)), indicator_of_notMem ht]
  let u : Additive (sIntegerRing F S)ˣ → d.range := fun x ↦ ⟨d x.toMul, ⟨x.toMul, rfl⟩⟩
  have hu : Bijective u := by
    constructor
    · intro x y h
      exact Additive.toMul.injective (sUnitToField_injective F S (congrArg Subtype.val h))
    · rintro ⟨y, x, rfl⟩
      exact ⟨Additive.ofMul x, rfl⟩
  rw [sLocalCarvingOrbitSum, tsum_congr hterm, ← tsum_subtype]
  refine ((Equiv.ofBijective u hu).tsum_eq (fun t ↦ b t.val)).symm.trans ?_
  unfold sLocalThetaOnIdeles
  apply tsum_congr
  intro x
  change sLocalBruhatRestriction F S f.val
      (sAdelesProjection F S (principalIdele F (d x.toMul) * g.val).val) = _
  rw [Units.val_mul, map_mul]
  rfl

/-- The outside-unit orbit sum descends to all idele classes. -/
def sLocalCarvingTheta (f : sLocalBruhatImage F S) : IdeleClass F → ℂ :=
  Quotient.lift (sLocalCarvingOrbitSum F S f) (by
    intro a b hab
    have h : a⁻¹ * b ∈ principalIdeles F := QuotientGroup.leftRel_apply.mp hab
    obtain ⟨t, ht⟩ := h
    have hb : b = principalIdele F t * a := by
      rw [ht, mul_comm a⁻¹ b, mul_assoc, inv_mul_cancel, mul_one]
    rw [hb, sLocalCarvingOrbitSum_principal_mul])

@[simp] theorem sLocalCarvingTheta_mk (f : sLocalBruhatImage F S) (g : Idele F) :
    sLocalCarvingTheta F S f (ideleClassMap F g) = sLocalCarvingOrbitSum F S f g := rfl

/-- Forget the outside integral units after choosing the ordinary S-idelic
representative class. Trivial S-class group makes this available on all classes. -/
def sLocalCarvingClassMap (hS : Surjective (sIdeleClassInclusion F S)) :
    IdeleClass F →ₜ* SIdeleQuotient F S :=
  let e : SIdeleClass F S ≃ₜ* IdeleClass F :=
    ContinuousMulEquiv.mk'
      ((sIdeleClassInclusion_openEmbedding F S).isEmbedding.toHomeomorphOfSurjective hS)
      (map_mul (sIdeleClassInclusion F S))
  ⟨(sIdeleClassToLocal F S).comp e.symm.toMonoidHom,
    (sIdeleClassToLocal_isOpenQuotientMap F S).continuous.comp e.symm.continuous⟩

theorem sLocalCarvingClassMap_on_block (hS : Surjective (sIdeleClassInclusion F S))
    (b : SIdeleClass F S) :
    sLocalCarvingClassMap F S hS (sIdeleClassInclusion F S b) = sIdeleClassToLocal F S b := by
  unfold sLocalCarvingClassMap
  exact congrArg (sIdeleClassToLocal F S) (ContinuousMulEquiv.symm_apply_apply _ b)

theorem sLocalCarvingTheta_eq_local (hS : Surjective (sIdeleClassInclusion F S))
    (f : sLocalBruhatImage F S) (q : IdeleClass F) :
    sLocalCarvingTheta F S f q =
      sLocalThetaOperator F S f (sLocalCarvingClassMap F S hS q) := by
  obtain ⟨b, rfl⟩ := hS q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective b
  rw [sLocalCarvingClassMap_on_block, sIdeleClassToLocal_mk]
  change sLocalCarvingOrbitSum F S f g.val =
    sLocalThetaOnIdeles F S (sLocalBruhatRestriction F S f.val) (sBlockUnitProduct F S g).1
  rw [sLocalCarvingOrbitSum_of_block]
  rfl

theorem sLocalCarvingClassMap_norm (hS : Surjective (sIdeleClassInclusion F S)) (q : IdeleClass F) :
    sQuotientNorm F S (sLocalCarvingClassMap F S hS q) = globalNormUnits F q := by
  obtain ⟨b,rfl⟩ := hS q
  rw [sLocalCarvingClassMap_on_block, sQuotientNorm_toLocal]

theorem sLocalCarvingClassMap_normOne (hS : Surjective (sIdeleClassInclusion F S))
    (k : normOneIdeleClass F) :
    sLocalCarvingClassMap F S hS k.val = (globalNormOneToSLocal F S hS k).val := by
  obtain ⟨b,hb⟩ := hS k.val
  rw [globalNormOneToSLocal_val_of_block F S hS k b hb, ← hb, sLocalCarvingClassMap_on_block]

local instance : MeasurableSpace (normOneIdeleClass F) := borel _
local instance : BorelSpace (normOneIdeleClass F) := ⟨rfl⟩
local instance : CompactSpace (normOneIdeleClass F) := normOneIdeleClass_compact F
local instance : MeasurableSpace (SLocalThetaNormOne F S) := borel _
local instance : BorelSpace (SLocalThetaNormOne F S) := ⟨rfl⟩

/-- Haar averaging of the true outside-unit orbit sum is exactly the local
homogeneous theta evaluated at the class obtained by forgetting the tail. -/
theorem sLocalCarvingTheta_average_eq_local
    (hS : Surjective (sIdeleClassInclusion F S))
    (ω : PontryaginDual (normOneIdeleClass F))
    (hω : globalNormOneCharacter F ω ∈ (sUnramified F S : Set (QuasiCharacter (IdeleClass F))))
    (ν : Measure (normOneIdeleClass F)) [ν.IsHaarMeasure]
    (f : sLocalBruhatImage F S) (q : IdeleClass F) :
    (∫ k, (ω k : ℂ) * sLocalCarvingTheta F S f (k.val * q) ∂ν) =
      sLocalHomogeneousTheta F S (Measure.map (globalNormOneToSLocal F S hS) ν)
        (sLocalNormOneCharacterOfGlobal F ω S hS hω) f.val (sLocalCarvingClassMap F S hS q) := by
  let m := globalNormOneToSLocal F S hS
  let σ := sLocalNormOneCharacterOfGlobal F ω S hS hω
  letI : IsFiniteMeasure ν := ⟨isCompact_univ.measure_lt_top⟩
  letI : (Measure.map m ν).IsHaarMeasure :=
    ν.isHaarMeasure_map_of_isFiniteMeasure m.toMonoidHom m.continuous
      (globalNormOneToSLocal_surjective F S hS)
  let I (k : SLocalThetaNormOne F S) : ℂ :=
    ((σ k : Circle) : ℂ) * sLocalThetaOperator F S f (k.val * sLocalCarvingClassMap F S hS q)
  have hI : AEStronglyMeasurable I (Measure.map m ν) :=
    (sLocalHomogeneousTheta_integrable F S (Measure.map m ν) σ f.val
      (sLocalCarvingClassMap F S hS q)).aestronglyMeasurable
  have hmap : (∫ y, I y ∂Measure.map m ν) = ∫ x, I (m x) ∂ν :=
    integral_map (by exact m.continuous.measurable.aemeasurable) hI
  change _ = ∫ y, I y ∂Measure.map m ν
  refine Eq.trans ?_ hmap.symm
  apply integral_congr_ae
  refine .of_forall fun k ↦ ?_
  change ((ω k : Circle) : ℂ) * sLocalCarvingTheta F S f (k.val * q) =
    ((σ (m k) : Circle) : ℂ) * sLocalThetaOperator F S f ((m k).val * sLocalCarvingClassMap F S hS q)
  have hchar : σ (m k) = ω k := sLocalNormOneCharacterOfGlobal_match F ω S hS hω k
  rw [sLocalCarvingTheta_eq_local F S hS, map_mul, sLocalCarvingClassMap_normOne F S hS, hchar]

theorem sLocalCarvingClassMap_logRay (hS : Surjective (sIdeleClassInclusion F S)) (t : ℝ) :
    sLocalCarvingClassMap F S hS (ideleClassExpSection F (Multiplicative.ofAdd t)) =
      sLocalLogNormRay F S t := by
  let a := sLocalExpSection F S (Multiplicative.ofAdd t)
  let b : SIdeleClass F S := QuotientGroup.mk (sLocalEmbed F S a)
  have hb : sIdeleClassInclusion F S b = ideleClassExpSection F (Multiplicative.ofAdd t) :=
    congrArg (ideleClassMap F) (sLocalExpSection_embed F S t)
  rw [← hb, sLocalCarvingClassMap_on_block]
  change sIdeleClassToLocal F S (QuotientGroup.mk (sLocalEmbed F S a)) = QuotientGroup.mk a
  rw [sIdeleClassToLocal_mk]
  exact congrArg QuotientGroup.mk
    (congrArg Prod.fst ((sBlockUnitProduct F S).apply_symm_apply (a,1)))

/-- The norm-one character projection of the outside-unit orbit sum. -/
def sLocalCarvingAverage (ω : PontryaginDual (normOneIdeleClass F))
    (ν : Measure (normOneIdeleClass F)) (f : sLocalBruhatImage F S) (q : IdeleClass F) : ℂ :=
  ∫ k, ((ω k : Circle) : ℂ) * sLocalCarvingTheta F S f (k.val * q) ∂ν

theorem sLocalCarvingAverage_radial
    (hS : Surjective (sIdeleClassInclusion F S))
    (ω : PontryaginDual (normOneIdeleClass F))
    (hω : globalNormOneCharacter F ω ∈ (sUnramified F S : Set (QuasiCharacter (IdeleClass F))))
    (ν : Measure (normOneIdeleClass F)) [ν.IsHaarMeasure]
    (f : sLocalBruhatImage F S) (q : IdeleClass F) :
    sLocalCarvingAverage F S ω ν f q =
      (((ω (ideleClassNormOnePart F q) : Circle) : ℂ)⁻¹) *
        sLocalHomogeneousTheta F S (Measure.map (globalNormOneToSLocal F S hS) ν)
          (sLocalNormOneCharacterOfGlobal F ω S hS hω) f.val
          (sLocalLogNormRay F S (ideleClassLogNorm F q).toAdd) := by
  let m := globalNormOneToSLocal F S hS
  let σ := sLocalNormOneCharacterOfGlobal F ω S hS hω
  let η := Measure.map m ν
  letI : IsFiniteMeasure ν := ⟨isCompact_univ.measure_lt_top⟩
  letI : η.IsHaarMeasure := ν.isHaarMeasure_map_of_isFiniteMeasure m.toMonoidHom m.continuous
    (globalNormOneToSLocal_surjective F S hS)
  let k := ideleClassNormOnePart F q
  let t := (ideleClassLogNorm F q).toAdd
  have hq : k.val * ideleClassExpSection F (Multiplicative.ofAdd t) = q := by
    change q / ideleClassExpSection F (ideleClassLogNorm F q) *
      ideleClassExpSection F (ideleClassLogNorm F q) = q
    exact div_mul_cancel _ _
  have hlocal : sLocalCarvingClassMap F S hS q = (m k).val * sLocalLogNormRay F S t := by
    calc
      sLocalCarvingClassMap F S hS q =
          sLocalCarvingClassMap F S hS (k.val * ideleClassExpSection F (Multiplicative.ofAdd t)) :=
        congrArg (sLocalCarvingClassMap F S hS) hq.symm
      _ = _ := by rw [map_mul, sLocalCarvingClassMap_normOne, sLocalCarvingClassMap_logRay]
  calc
    _ = sLocalHomogeneousTheta F S η σ f.val (sLocalCarvingClassMap F S hS q) :=
      sLocalCarvingTheta_average_eq_local F S hS ω hω ν f q
    _ = _ := by
      rw [hlocal, sLocalHomogeneousTheta_translate F S η σ]
      have he : σ (m k) = ω k := sLocalNormOneCharacterOfGlobal_match F ω S hS hω k
      rw [he]

/-- The projected S-local generators realize all compact smooth radial
profiles on the flat, locally vanishing test subspace. -/
theorem exists_sLocalCarvingTheta_average_of_compact_profile
    (hS : Surjective (sIdeleClassInclusion F S))
    (ω : PontryaginDual (normOneIdeleClass F))
    (hω : globalNormOneCharacter F ω ∈ (sUnramified F S : Set (QuasiCharacter (IdeleClass F))))
    (ν : Measure (normOneIdeleClass F)) [ν.IsHaarMeasure]
    {p : ℝ → ℂ} (hp : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) p) (hpc : HasCompactSupport p) :
    ∃ f : sLocalPolarFreeTestSubspace F S, ∀ q : IdeleClass F,
      (∫ k, ((ω k : Circle) : ℂ) * sLocalCarvingTheta F S f.val (k.val * q) ∂ν) =
        (((ω (ideleClassNormOnePart F q) : Circle) : ℂ)⁻¹) *
          p (ideleClassLogNorm F q).toAdd := by
  let m := globalNormOneToSLocal F S hS
  let σ := sLocalNormOneCharacterOfGlobal F ω S hS hω
  let η := Measure.map m ν
  letI : IsFiniteMeasure ν := ⟨isCompact_univ.measure_lt_top⟩
  letI : η.IsHaarMeasure := ν.isHaarMeasure_map_of_isFiniteMeasure m.toMonoidHom m.continuous
    (globalNormOneToSLocal_surjective F S hS)
  let φ : PositiveRealExponentialDecay univ :=
    ⟨p, mem_logExponentialDecaySubmodule_of_hasCompactSupport univ hpc hp⟩
  obtain ⟨f, hf⟩ := exists_sLocalHomogeneousTheta_polarFree_of_profile F S η σ φ
  refine ⟨f, fun q ↦ ?_⟩
  let t := (ideleClassLogNorm F q).toAdd
  let character : ℂ := (((ω (ideleClassNormOnePart F q) : Circle) : ℂ)⁻¹)
  change sLocalCarvingAverage F S ω ν f.val q = character * p t
  exact (sLocalCarvingAverage_radial F S hS ω hω ν f.val q).trans
    (congrArg (character * ·) (hf t))

private theorem sLocalFlat_eval_zero (f : sLocalPolarFreeTestSubspace F S) :
    (GlobalBruhat.polarEvaluation F f.val.val).1 = 0 := by
  classical
  change GlobalBruhat.evaluation F 0 f.val.val = 0
  apply sLocalPolarFree_induction F S
    (fun f ↦ GlobalBruhat.evaluation F 0 f.val.val = 0) _ _ _ _ f
  · intro a g hg
    have h0 := (mem_schwartzFlatSubspace _ _).mp a.property (0 : mixedEmbedding.mixedSpace F)
      (by
        obtain ⟨v⟩ := (inferInstance : Nonempty (InfinitePlace F))
        by_cases hv : v.IsReal
        · exact Or.inl ⟨⟨v,hv⟩,rfl⟩
        · exact Or.inr ⟨⟨v, InfinitePlace.not_isReal_iff_isComplex.mp hv⟩,rfl⟩) 0
    have ha : a.val 0 = 0 := norm_eq_zero.mp
      (by simpa only [norm_iteratedFDeriv_zero, norm_zero] using congrArg norm h0)
    change GlobalBruhat.evaluation F 0 (sLocalBruhatPure F S a.val (locallyConstantTestPiProduct g)).val = 0
    rw [sLocalBruhatRestriction_reconstruct, map_zero, sLocalBruhatPure_restrict]
    rw [show (0 : SAdeles F S).1 = 0 from rfl, map_zero, ha, zero_mul, zero_mul]
  · simp
  · intro x y hx hy
    change GlobalBruhat.evaluation F 0 (x.val.val + y.val.val) = 0
    simp [hx,hy]
  · intro c x hx
    change GlobalBruhat.evaluation F 0 (c • x.val.val) = 0
    simp [hx]

private theorem sLocalCarvingAverage_sub_smul
    (hS : Surjective (sIdeleClassInclusion F S))
    (ω : PontryaginDual (normOneIdeleClass F))
    (hω : globalNormOneCharacter F ω ∈ (sUnramified F S : Set (QuasiCharacter (IdeleClass F))))
    (ν : Measure (normOneIdeleClass F)) [ν.IsHaarMeasure]
    (f g : sLocalBruhatImage F S) (c : ℂ) (q : IdeleClass F) :
    sLocalCarvingAverage F S ω ν (f - c • g) q =
      sLocalCarvingAverage F S ω ν f q - c * sLocalCarvingAverage F S ω ν g q := by
  let m := globalNormOneToSLocal F S hS
  let σ := sLocalNormOneCharacterOfGlobal F ω S hS hω
  let η := Measure.map m ν
  let q₀ := sLocalCarvingClassMap F S hS q
  letI : IsFiniteMeasure ν := ⟨isCompact_univ.measure_lt_top⟩
  letI : η.IsHaarMeasure := ν.isHaarMeasure_map_of_isFiniteMeasure m.toMonoidHom m.continuous
    (globalNormOneToSLocal_surjective F S hS)
  unfold sLocalCarvingAverage
  simp only [sLocalCarvingTheta_average_eq_local F S hS ω hω ν]
  let I (x : sLocalBruhatImage F S) (k : SLocalThetaNormOne F S) : ℂ :=
    ((σ k : Circle) : ℂ) * sLocalThetaOperator F S x (k.val * q₀)
  have hi (x : sLocalBruhatImage F S) : Integrable (I x) η :=
    sLocalHomogeneousTheta_integrable F S η σ x.val q₀
  change (∫ k, I (f - c • g) k ∂η) = (∫ k, I f k ∂η) - c * (∫ k, I g k ∂η)
  rw [← integral_const_mul, ← integral_sub (hi f) ((hi g).const_mul c)]
  apply integral_congr_ae
  exact .of_forall fun k ↦ by
    dsimp only [I]
    rw [map_sub, map_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring

private theorem sLocalCarvingAverage_rayTranslate
    (hS : Surjective (sIdeleClassInclusion F S))
    (ω : PontryaginDual (normOneIdeleClass F))
    (hω : globalNormOneCharacter F ω ∈ (sUnramified F S : Set (QuasiCharacter (IdeleClass F))))
    (ν : Measure (normOneIdeleClass F)) [ν.IsHaarMeasure]
    (f : sLocalBruhatImage F S) (t : ℝ) (q : IdeleClass F) :
    sLocalCarvingAverage F S ω ν
      (sLocalBruhatLeftTranslate F S (sLocalExpSection F S (Multiplicative.ofAdd t)) f) q =
      sLocalCarvingAverage F S ω ν f ((ideleClassExpSection F (Multiplicative.ofAdd t))⁻¹ * q) := by
  unfold sLocalCarvingAverage
  simp only [sLocalCarvingTheta_average_eq_local F S hS ω hω ν]
  rw [sLocalHomogeneousTheta_translate_test, map_mul, map_inv, sLocalCarvingClassMap_logRay]
  rfl

set_option maxHeartbeats 1500000 in
/-- Compact radial profiles on a prescribed right half-line have S-local
representatives with both zero evaluations. The translate used to remove
the Fourier evaluation has its radial support strictly below the cutoff. -/
theorem exists_sLocalCarvingPolarFree_on_halfline
    (hS : Surjective (sIdeleClassInclusion F S))
    (ω : PontryaginDual (normOneIdeleClass F))
    (hω : globalNormOneCharacter F ω ∈ (sUnramified F S : Set (QuasiCharacter (IdeleClass F))))
    (ν : Measure (normOneIdeleClass F)) [ν.IsHaarMeasure]
    {p : ℝ → ℂ} (hp : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) p) (hpc : HasCompactSupport p)
    (a : ℝ) :
    ∃ f : sLocalBruhatImage F S, GlobalBruhat.polarEvaluation F f.val = 0 ∧
      ∀ q : IdeleClass F, a ≤ (ideleClassLogNorm F q).toAdd →
        sLocalCarvingAverage F S ω ν f q =
          (((ω (ideleClassNormOnePart F q) : Circle) : ℂ)⁻¹) *
            p (ideleClassLogNorm F q).toAdd := by
  obtain ⟨g,hg⟩ := exists_sLocalCarvingTheta_average_of_compact_profile F S hS ω hω ν hp hpc
  obtain ⟨b,hb⟩ := hpc.isCompact.bddAbove
  let t := a - b - 1
  let u := sLocalExpSection F S (Multiplicative.ofAdd t)
  let v := sLocalBruhatLeftTranslate F S u g.val
  let n : ℝ := ideleNorm F (sLocalEmbed F S u).val
  have hn : (n : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ideleNorm_pos F _).ne'
  refine ⟨g.val - (n : ℂ)⁻¹ • v, ?_, ?_⟩
  · have hzero := sLocalFlat_eval_zero F S g
    have hv : GlobalBruhat.polarEvaluation F v.val =
        ((GlobalBruhat.polarEvaluation F g.val.val).1, n • (GlobalBruhat.polarEvaluation F g.val.val).2) :=
      polarEvaluation_leftTranslate F (sLocalEmbed F S u).val g.val.val
    change GlobalBruhat.polarEvaluation F (g.val.val - (n : ℂ)⁻¹ • v.val) = 0
    rw [map_sub, map_smul, hv]
    apply Prod.ext
    · simp [hzero]
    · change (GlobalBruhat.polarEvaluation F g.val.val).2 -
        (n : ℂ)⁻¹ * (n • (GlobalBruhat.polarEvaluation F g.val.val).2) = 0
      rw [Complex.real_smul, ← mul_assoc, inv_mul_cancel₀ hn, one_mul, sub_self]
  · intro q hq
    have hr : (ideleClassLogNorm F ((ideleClassExpSection F (Multiplicative.ofAdd t))⁻¹ * q)).toAdd =
        (ideleClassLogNorm F q).toAdd - t := by
      rw [map_mul, map_inv, ideleClassLogNorm_expSection]
      change -t + (ideleClassLogNorm F q).toAdd = _
      ring
    have hval : p ((ideleClassLogNorm F q).toAdd - t) = 0 := by
      by_contra hne
      have hle := hb (subset_closure (show (ideleClassLogNorm F q).toAdd - t ∈ support p from hne))
      dsimp [t] at hle
      linarith
    rw [sLocalCarvingAverage_sub_smul F S hS ω hω, sLocalCarvingAverage_rayTranslate F S hS ω hω]
    change sLocalCarvingAverage F S ω ν g.val q -
        (n : ℂ)⁻¹ * sLocalCarvingAverage F S ω ν g.val
          ((ideleClassExpSection F (Multiplicative.ofAdd t))⁻¹ * q) = _
    unfold sLocalCarvingAverage
    rw [hg, hg, hr, hval, mul_zero, mul_zero, sub_zero]

end
end Masullo
