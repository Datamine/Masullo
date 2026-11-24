import HomogeneousThetaStructure

open Bornology Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical NNReal NumberField

namespace Masullo

noncomputable section

set_option maxHeartbeats 1600000

universe u

variable (F : Type u) [Field F] [NumberField F]

private abbrev Place := HeightOneSpectrum (𝓞 F)
private abbrev K := normOneIdeleClass F
private abbrev KS (S : Finset (Place F)) := SLocalThetaNormOne F S
private abbrev G := GlobalThetaQuotient F
private abbrev L (S : Finset (Place F)) := SLocalThetaQuotient F S

local instance : MeasurableSpace (Idele F) := borel _
local instance : BorelSpace (Idele F) := ⟨rfl⟩
local instance (S : Finset (Place F)) : MeasurableSpace (SIdeleQuotient F S) := borel _
local instance (S : Finset (Place F)) : BorelSpace (SIdeleQuotient F S) := ⟨rfl⟩

section Block

variable (S : Finset (Place F)) (hS : Surjective (sIdeleClassInclusion F S))

private def globalBlockEquiv : SIdeleClass F S ≃* IdeleClass F :=
  MulEquiv.ofBijective (sIdeleClassInclusion F S)
    ⟨(sIdeleClassInclusion_openEmbedding F S).injective, hS⟩

private theorem globalBlockEquiv_inv_continuous :
    Continuous (globalBlockEquiv F S hS).symm := by
  apply (sIdeleClassInclusion_openEmbedding F S).isEmbedding.continuous_iff.mpr
  have he : (sIdeleClassInclusion F S) ∘ (globalBlockEquiv F S hS).symm = id :=
    funext (globalBlockEquiv F S hS).apply_symm_apply
  rw [he]
  exact continuous_id

private theorem globalNormUnits_eq_one_iff (q : IdeleClass F) :
    globalNormUnits F q = 1 ↔ ideleClassNorm F q = 1 := by
  constructor
  · intro h
    exact congrArg (fun n : ℝ≥0ˣ ↦ (n.val : ℝ)) h
  · intro h
    exact Units.ext (NNReal.eq h)

private theorem globalBlock_toLocal_normOne (k : K F) :
    sIdeleClassToLocal F S ((globalBlockEquiv F S hS).symm k.val) ∈ KS F S := by
  change sQuotientNorm F S (sIdeleClassToLocal F S ((globalBlockEquiv F S hS).symm k.val)) = 1
  rw [sQuotientNorm_toLocal]
  change globalNormUnits F (globalBlockEquiv F S hS ((globalBlockEquiv F S hS).symm k.val)) = 1
  rw [MulEquiv.apply_symm_apply]
  exact (globalNormUnits_eq_one_iff F k.val).mpr k.property

/-- For an open block meeting every idele class, forgetting the integral tail
is a surjective homomorphism on the norm-one classes. -/
def globalNormOneToSLocal : K F →ₜ* KS F S where
  toFun k := ⟨sIdeleClassToLocal F S ((globalBlockEquiv F S hS).symm k.val),
    globalBlock_toLocal_normOne F S hS k⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' k l := by
    apply Subtype.ext
    change sIdeleClassToLocal F S ((globalBlockEquiv F S hS).symm (k.val * l.val)) =
      sIdeleClassToLocal F S ((globalBlockEquiv F S hS).symm k.val) *
        sIdeleClassToLocal F S ((globalBlockEquiv F S hS).symm l.val)
    rw [map_mul, map_mul]
  continuous_toFun :=
    ((sIdeleClassToLocal_isOpenQuotientMap F S).continuous.comp
      ((globalBlockEquiv_inv_continuous F S hS).comp continuous_subtype_val)).subtype_mk _

theorem globalNormOneToSLocal_surjective : Surjective (globalNormOneToSLocal F S hS) := by
  intro a
  obtain ⟨b, hb⟩ := (sIdeleClassToLocal_isOpenQuotientMap F S).surjective a.val
  have he := sQuotientNorm_toLocal F S b
  rw [hb, show sQuotientNorm F S a.val = 1 from a.property] at he
  refine ⟨⟨sIdeleClassInclusion F S b, (globalNormUnits_eq_one_iff F _).mp he.symm⟩, ?_⟩
  apply Subtype.ext
  change sIdeleClassToLocal F S ((globalBlockEquiv F S hS).symm ((globalBlockEquiv F S hS) b)) = a.val
  rwa [MulEquiv.symm_apply_apply]

theorem globalNormOneToSLocal_val_of_block (k : K F) (b : SIdeleClass F S)
    (hb : sIdeleClassInclusion F S b = k.val) :
    (globalNormOneToSLocal F S hS k).val = sIdeleClassToLocal F S b := by
  change (globalBlockEquiv F S hS) b = k.val at hb
  change sIdeleClassToLocal F S ((globalBlockEquiv F S hS).symm k.val) = _
  rw [← hb, MulEquiv.symm_apply_apply]

theorem sLocalThetaToGlobal_normOne (k : K F) (q : L F S) :
    sLocalThetaToGlobal F S (sLocalNormOneAction F S (globalNormOneToSLocal F S hS k) q) =
      globalThetaNormOneAction F k (sLocalThetaToGlobal F S q) := by
  have h := sLocalThetaToGlobal_translate_blockClass F S ((globalBlockEquiv F S hS).symm k.val) q
  rw [show sIdeleClassInclusion F S ((globalBlockEquiv F S hS).symm k.val) = k.val
    from (globalBlockEquiv F S hS).apply_symm_apply k.val] at h
  exact h

end Block

/-- The global extension of a norm-one character that is trivial on the norm ray. -/
def globalNormOneCharacter (ω : PontryaginDual (K F)) : QuasiCharacter (IdeleClass F) :=
  ⟨Circle.coeHom.comp (ω.toMonoidHom.comp
    ((MonoidHom.fst _ _).comp (ideleClassSplit F).toMonoidHom)),
    continuous_subtype_val.comp (ω.continuous.comp
      (continuous_fst.comp (ideleClassSplitHomeomorph F).continuous))⟩

theorem globalNormOneCharacter_apply (ω : PontryaginDual (K F)) (k : K F) :
    globalNormOneCharacter F ω k.val = (ω k : ℂ) := by
  change (ω (ideleClassNormOnePart F k.val) : ℂ) = (ω k : ℂ)
  congr 2
  apply Subtype.ext
  change k.val / ideleClassExpSection F (ideleClassLogNorm F k.val) = k.val
  have h : ideleClassLogNorm F k.val = 1 := by
    change Multiplicative.ofAdd (Real.log (ideleClassNorm F k.val)) = 1
    rw [show ideleClassNorm F k.val = 1 from k.property, Real.log_one]
    rfl
  rw [h, map_one, div_one]

section AnyPlaceSet

variable (ω : PontryaginDual (K F)) (S : Finset (Place F))
  (hω : globalNormOneCharacter F ω ∈ (sUnramified F S : Set (QuasiCharacter (IdeleClass F))))

private def blockNormOneGlobal (b : SIdeleClass F S)
    (hb : sIdeleClassToLocal F S b ∈ KS F S) : K F :=
  ⟨sIdeleClassInclusion F S b, (globalNormUnits_eq_one_iff F _).mp <|
    (sQuotientNorm_toLocal F S b).symm.trans hb⟩

/-- Restriction of a global norm-one character through an arbitrary finite
block, provided that the character is unramified at the omitted places. -/
def sLocalRestrictedNormOneCharacter : PontryaginDual (KS F S) := by
  let c : sUnramified F S := ⟨globalNormOneCharacter F ω, hω⟩
  let d := sCharacterRestriction F S c
  have hm (a : KS F S) : d a.val ∈ Submonoid.unitSphere ℂ := by
    obtain ⟨b, hb⟩ := (sIdeleClassToLocal_isOpenQuotientMap F S).surjective a.val
    let k := blockNormOneGlobal F S b (hb ▸ a.property)
    rw [← hb, sCharacterRestriction_block, ← show k.val = sIdeleClassInclusion F S b from rfl,
      globalNormOneCharacter_apply]
    exact (ω k).property
  exact {
    toFun a := ⟨d a.val, hm a⟩
    map_one' := Subtype.ext (map_one d)
    map_mul' a b := Subtype.ext (map_mul d a.val b.val)
    continuous_toFun := (d.continuous.comp continuous_subtype_val).subtype_mk hm }

theorem sLocalRestrictedNormOneCharacter_block (b : SIdeleClass F S)
    (hb : sIdeleClassToLocal F S b ∈ KS F S) :
    sLocalRestrictedNormOneCharacter F ω S hω ⟨sIdeleClassToLocal F S b, hb⟩ =
      ω (blockNormOneGlobal F S b hb) := by
  apply Subtype.ext
  change sCharacterRestriction F S ⟨globalNormOneCharacter F ω, hω⟩ (sIdeleClassToLocal F S b) = _
  rw [sCharacterRestriction_block]
  exact globalNormOneCharacter_apply F ω (blockNormOneGlobal F S b hb)

end AnyPlaceSet

theorem sLocalRestrictedNormOneCharacter_eq_restriction
    (ω : PontryaginDual (K F)) (S : Finset (Place F))
    (hω : globalNormOneCharacter F ω ∈ (sUnramified F S : Set (QuasiCharacter (IdeleClass F))))
    (c : sUnramified F S) (hc : ∀ k : K F, c.val k.val = (ω k : ℂ))
    (a : KS F S) :
    (sLocalRestrictedNormOneCharacter F ω S hω a : ℂ) = sCharacterRestriction F S c a.val := by
  obtain ⟨b, hb⟩ := (sIdeleClassToLocal_isOpenQuotientMap F S).surjective a.val
  have hn : sIdeleClassToLocal F S b ∈ KS F S := hb ▸ a.property
  have ha : (⟨sIdeleClassToLocal F S b, hn⟩ : KS F S) = a := Subtype.ext hb
  rw [← ha, sLocalRestrictedNormOneCharacter_block, sCharacterRestriction_block]
  exact (hc (blockNormOneGlobal F S b hn)).symm

/-- Remark 5.2.3.3. Unramifiedness off S is equivalent to unique descent of
the restricted norm-one character along the map which forgets the integral tail. -/
theorem normOneCharacter_unramified_iff_unique_descent
    (ω : PontryaginDual (K F)) (S : Finset (Place F)) :
    globalNormOneCharacter F ω ∈ (sUnramified F S : Set (QuasiCharacter (IdeleClass F))) ↔
      ∃! χ : PontryaginDual (KS F S), ∀ (b : SIdeleClass F S)
        (hb : sIdeleClassToLocal F S b ∈ KS F S),
        χ ⟨sIdeleClassToLocal F S b, hb⟩ = ω (blockNormOneGlobal F S b hb) := by
  constructor
  · intro hω
    refine ⟨sLocalRestrictedNormOneCharacter F ω S hω,
      sLocalRestrictedNormOneCharacter_block F ω S hω, ?_⟩
    intro χ hχ
    ext a
    obtain ⟨b, hb⟩ := (sIdeleClassToLocal_isOpenQuotientMap F S).surjective a.val
    have hn : sIdeleClassToLocal F S b ∈ KS F S := hb ▸ a.property
    have ha : (⟨sIdeleClassToLocal F S b, hn⟩ : KS F S) = a := Subtype.ext hb
    rw [← ha, hχ b hn, sLocalRestrictedNormOneCharacter_block]
  · rintro ⟨χ, hχ, _⟩
    change (globalNormOneCharacter F ω).comp _ ∈ ({1} : Set _)
    apply Set.mem_singleton_iff.mpr
    ext a
    let b : SIdeleClass F S := QuotientGroup.mk (sTailEmbed F S a)
    have hb : sIdeleClassToLocal F S b = 1 := by
      rw [sIdeleClassToLocal_mk]
      change QuotientGroup.mk ((sBlockUnitProduct F S
        ((sBlockUnitProduct F S).symm (1, a))).1) = 1
      rw [ContinuousMulEquiv.apply_symm_apply]
      exact map_one (QuotientGroup.mk' (sUnitImage F S))
    have hn : sIdeleClassToLocal F S b ∈ KS F S := hb ▸ (KS F S).one_mem
    have he : (⟨sIdeleClassToLocal F S b, hn⟩ : KS F S) = 1 := Subtype.ext hb
    change globalNormOneCharacter F ω (blockNormOneGlobal F S b hn).val = 1
    rw [globalNormOneCharacter_apply, ← hχ b hn, he, map_one]
    rfl

section AnyPlaceSet

variable (ω : PontryaginDual (K F)) (S : Finset (Place F))
  (hω : globalNormOneCharacter F ω ∈ (sUnramified F S : Set (QuasiCharacter (IdeleClass F))))

variable (μ : Measure (Idele F)) [μ.IsHaarMeasure]
  (ν : Measure (KS F S)) [ν.IsHaarMeasure]

/-- The homogeneous padding square commutes on every unramified finite block. -/
theorem exists_sLocalHomogeneousThetaToGlobal_comp :
    ∃ j : SLocalHomogeneousThetaQuotient F S ν (sLocalRestrictedNormOneCharacter F ω S hω)
        →L[ℂ] (GlobalBruhat F ⧸ globalIdelicZetaComponentKernel F μ ω),
      j.comp (sLocalThetaToComponent F S ν (sLocalRestrictedNormOneCharacter F ω S hω)) =
        (globalThetaToComponent F μ ω).comp (sLocalThetaToGlobal F S) := by
  letI : T2Space (GlobalBruhat F ⧸ globalIdelicZetaComponentKernel F μ ω) :=
    (globalHomogeneousTheta_primalStructure F μ ω).1.1
  let A := (globalThetaToComponent F μ ω).comp (sLocalThetaToGlobal F S)
  let τ := sLocalRestrictedNormOneCharacter F ω S hω
  let p := sLocalThetaToComponent F S ν τ
  obtain ⟨s, hs, _, hKer⟩ := sLocalThetaComponent_isotypicSection F S ν τ
  have hA : p.ker ≤ A.ker := by
    change (sLocalThetaToComponent F S ν τ).ker ≤ A.ker
    rw [hKer]
    apply Submodule.topologicalClosure_minimal _ _ A.isClosed_ker
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨k, q⟩, rfl⟩
    obtain ⟨b, hb⟩ := (sIdeleClassToLocal_isOpenQuotientMap F S).surjective k.val
    have hk : sIdeleClassToLocal F S b ∈ KS F S := hb ▸ k.property
    have hkb : (⟨sIdeleClassToLocal F S b, hk⟩ : KS F S) = k := Subtype.ext hb
    let a := blockNormOneGlobal F S b hk
    have hτ : τ k = ω a :=
      hkb ▸ sLocalRestrictedNormOneCharacter_block F ω S hω b hk
    have he : A (sLocalNormOneAction F S k q) = (ω a : ℂ) • A q := by
      have h := sLocalThetaToGlobal_translate_blockClass F S b q
      change sLocalThetaToGlobal F S (sLocalThetaTranslate F S (sIdeleClassToLocal F S b) q) =
        globalThetaTranslate F (sIdeleClassInclusion F S b) (sLocalThetaToGlobal F S q) at h
      rw [hb] at h
      change globalThetaToComponent F μ ω
        (sLocalThetaToGlobal F S (sLocalThetaTranslate F S k.val q)) = _
      rw [h]
      exact globalThetaToComponent_normOne F μ ω a _
    change A (q - (((τ k)⁻¹ : Circle) : ℂ) • sLocalNormOneAction F S k q) = 0
    rw [map_sub, map_smul, he, hτ, Circle.coe_inv, smul_smul,
      inv_mul_cancel₀ (Circle.coe_ne_zero _), one_smul, sub_self]
  refine ⟨A.comp s, ContinuousLinearMap.ext fun q ↦ ?_⟩
  have hq : q - s (p q) ∈ p.ker := by
    change p (q - s (p q)) = 0
    rw [map_sub, hs (p q), sub_self]
  have hz := hA hq
  change A (q - s (p q)) = 0 at hz
  rw [map_sub, sub_eq_zero] at hz
  exact hz.symm

end AnyPlaceSet

/-- The cofinal stage character is the restriction through that block. -/
def sLocalNormOneCharacterOfGlobal (ω : PontryaginDual (K F)) (S : Finset (Place F))
    (_hS : Surjective (sIdeleClassInclusion F S))
    (hω : globalNormOneCharacter F ω ∈ (sUnramified F S : Set (QuasiCharacter (IdeleClass F)))) :
    PontryaginDual (KS F S) :=
  sLocalRestrictedNormOneCharacter F ω S hω

theorem sLocalNormOneCharacterOfGlobal_match (ω : PontryaginDual (K F)) (S : Finset (Place F))
    (hS : Surjective (sIdeleClassInclusion F S))
    (hω : globalNormOneCharacter F ω ∈ (sUnramified F S : Set (QuasiCharacter (IdeleClass F))))
    (k : K F) :
    sLocalNormOneCharacterOfGlobal F ω S hS hω (globalNormOneToSLocal F S hS k) = ω k := by
  apply Subtype.ext
  let c : sUnramified F S := ⟨globalNormOneCharacter F ω, hω⟩
  change sCharacterRestriction F S c (sIdeleClassToLocal F S ((globalBlockEquiv F S hS).symm k.val)) =
    (ω k : ℂ)
  rw [sCharacterRestriction_block, show sIdeleClassInclusion F S ((globalBlockEquiv F S hS).symm k.val) =
    k.val from (globalBlockEquiv F S hS).apply_symm_apply k.val]
  exact globalNormOneCharacter_apply F ω k

section Stages

variable (μ : Measure (Idele F)) [μ.IsHaarMeasure] (ω : PontryaginDual (K F))

private abbrev HG := GlobalBruhat F ⧸ globalIdelicZetaComponentKernel F μ ω

variable (S : Finset (Place F)) (hS : Surjective (sIdeleClassInclusion F S))
  (hω : globalNormOneCharacter F ω ∈ (sUnramified F S : Set (QuasiCharacter (IdeleClass F))))
  (ν : Measure (KS F S)) [ν.IsHaarMeasure]

private abbrev ωS := sLocalNormOneCharacterOfGlobal F ω S hS hω
private abbrev HS := SLocalHomogeneousThetaQuotient F S ν (ωS F ω S hS hω)
private abbrev pS := sLocalThetaToComponent F S ν (ωS F ω S hS hω)
private abbrev pG := globalThetaToComponent F μ ω

private def jS : HS F ω S hS hω ν →L[ℂ] L F S :=
  (sLocalThetaComponent_isotypicSection F S ν (ωS F ω S hS hω)).choose

private def jG : HG F μ ω →L[ℂ] G F :=
  (globalThetaComponent_isotypicSection F μ ω).choose

private theorem pS_jS : LeftInverse (pS F ω S hS hω ν) (jS F ω S hS hω ν) :=
  (sLocalThetaComponent_isotypicSection F S ν (ωS F ω S hS hω)).choose_spec.1

private theorem pG_jG : LeftInverse (pG F μ ω) (jG F μ ω) :=
  (globalThetaComponent_isotypicSection F μ ω).choose_spec.1

/-- The global idele-class action on a homogeneous theta quotient. -/
def globalHomogeneousThetaTranslate (c : IdeleClass F) : HG F μ ω →L[ℂ] HG F μ ω :=
  (pG F μ ω).comp ((globalThetaTranslate F c).comp (jG F μ ω))

private theorem globalHomogeneousThetaTranslate_section (c : IdeleClass F) (q : HG F μ ω) :
    jG F μ ω (globalHomogeneousThetaTranslate F μ ω c q) =
      globalThetaTranslate F c (jG F μ ω q) := by
  apply ((globalThetaComponent_isotypicSection F μ ω).choose_spec.2.1 _).mpr
  intro k
  change globalThetaTranslate F k.val (globalThetaTranslate F c (jG F μ ω q)) =
    (ω k : ℂ) • globalThetaTranslate F c (jG F μ ω q)
  have h : globalThetaTranslate F k.val (jG F μ ω q) = (ω k : ℂ) • jG F μ ω q :=
    (globalThetaComponent_isotypicSection F μ ω).choose_spec.2.2 q k
  rw [← ContinuousLinearMap.comp_apply, ← globalThetaTranslate_mul, mul_comm k.val c,
    globalThetaTranslate_mul, ContinuousLinearMap.comp_apply, h, map_smul]

/-- The induced global action is jointly continuous. -/
theorem continuous_globalHomogeneousThetaTranslate :
    Continuous (fun z : IdeleClass F × HG F μ ω ↦ globalHomogeneousThetaTranslate F μ ω z.1 z.2) :=
  (pG F μ ω).continuous.comp <| (continuous_globalThetaTranslate F).comp
    (continuous_fst.prodMk ((jG F μ ω).continuous.comp continuous_snd))

theorem globalHomogeneousThetaTranslate_one :
    globalHomogeneousThetaTranslate F μ ω 1 = ContinuousLinearMap.id ℂ _ := by
  apply ContinuousLinearMap.ext
  intro q
  change pG F μ ω (globalThetaTranslate F 1 (jG F μ ω q)) = q
  rw [globalThetaTranslate_one]
  exact pG_jG F μ ω q

theorem globalHomogeneousThetaTranslate_mul (c d : IdeleClass F) :
    globalHomogeneousThetaTranslate F μ ω (c * d) =
      (globalHomogeneousThetaTranslate F μ ω c).comp (globalHomogeneousThetaTranslate F μ ω d) := by
  apply ContinuousLinearMap.ext
  intro q
  change pG F μ ω (globalThetaTranslate F (c * d) (jG F μ ω q)) =
    pG F μ ω (globalThetaTranslate F c (jG F μ ω (globalHomogeneousThetaTranslate F μ ω d q)))
  rw [globalHomogeneousThetaTranslate_section, globalThetaTranslate_mul, ContinuousLinearMap.comp_apply]

/-- Padding homogeneous theta tests, on a stage that meets every idele class
and contains the ramified places of the prescribed character. -/
def sLocalHomogeneousThetaToGlobal : HS F ω S hS hω ν →L[ℂ] HG F μ ω :=
  (pG F μ ω).comp ((sLocalThetaToGlobal F S).comp (jS F ω S hS hω ν))

theorem sLocalHomogeneousThetaToGlobal_comp :
    (sLocalHomogeneousThetaToGlobal F μ ω S hS hω ν).comp (pS F ω S hS hω ν) =
      (pG F μ ω).comp (sLocalThetaToGlobal F S) := by
  obtain ⟨j, hj⟩ := exists_sLocalHomogeneousThetaToGlobal_comp F ω S hω μ ν
  apply ContinuousLinearMap.ext
  intro q
  let A := (pG F μ ω).comp (sLocalThetaToGlobal F S)
  let p := pS F ω S hS hω ν
  let s := jS F ω S hS hω ν
  have he (x : L F S) : j (p x) = A x := DFunLike.congr_fun hj x
  change A (s (p q)) = A q
  rw [← he (s (p q)), pS_jS F ω S hS hω ν (p q), he q]

private theorem jG_sLocalHomogeneousThetaToGlobal (q : HS F ω S hS hω ν) :
    jG F μ ω (sLocalHomogeneousThetaToGlobal F μ ω S hS hω ν q) =
      sLocalThetaToGlobal F S (jS F ω S hS hω ν q) := by
  let x := jS F ω S hS hω ν q
  change jG F μ ω (pG F μ ω (sLocalThetaToGlobal F S x)) = sLocalThetaToGlobal F S x
  apply ((globalThetaComponent_isotypicSection F μ ω).choose_spec.2.1 _).mpr
  intro k
  rw [← sLocalThetaToGlobal_normOne F S hS k]
  have h := (sLocalThetaComponent_isotypicSection F S ν (ωS F ω S hS hω)).choose_spec.2.1
    q (globalNormOneToSLocal F S hS k)
  change sLocalNormOneAction F S (globalNormOneToSLocal F S hS k) x =
    (ωS F ω S hS hω (globalNormOneToSLocal F S hS k) : ℂ) • x at h
  rw [h, sLocalNormOneCharacterOfGlobal_match F ω S hS hω k, map_smul]

theorem sLocalHomogeneousThetaToGlobal_exists_retraction :
    ∃ r : HG F μ ω →L[ℂ] HS F ω S hS hω ν,
      LeftInverse r (sLocalHomogeneousThetaToGlobal F μ ω S hS hω ν) := by
  obtain ⟨r, hr⟩ := sLocalThetaToGlobal_exists_retraction F S
  refine ⟨(pS F ω S hS hω ν).comp (r.comp (jG F μ ω)), ?_⟩
  intro q
  change pS F ω S hS hω ν (r (jG F μ ω (sLocalHomogeneousThetaToGlobal F μ ω S hS hω ν q))) = q
  rw [jG_sLocalHomogeneousThetaToGlobal, hr, pS_jS]

theorem sLocalHomogeneousThetaToGlobal_isClosedEmbedding :
    IsClosedEmbedding (sLocalHomogeneousThetaToGlobal F μ ω S hS hω ν) := by
  obtain ⟨r, hr⟩ := sLocalHomogeneousThetaToGlobal_exists_retraction F μ ω S hS hω ν
  let i := sLocalHomogeneousThetaToGlobal F μ ω S hS hω ν
  letI : T2Space (HG F μ ω) := (globalHomogeneousTheta_primalStructure F μ ω).1.1
  refine ⟨hr.isEmbedding r.continuous i.continuous, ?_⟩
  have he : range i = {q : HG F μ ω | i (r q) = q} := by
    ext q
    change (∃ x, i x = q) ↔ i (r q) = q
    exact ⟨by rintro ⟨x, rfl⟩; rw [hr x], fun h ↦ ⟨r q, h⟩⟩
  rw [he]
  exact isClosed_eq (i.continuous.comp r.continuous) continuous_id

end Stages

/-- A finite base can contain all ramified places and meet every global ideal class. -/
theorem exists_homogeneousThetaPlaceBase (ω : PontryaginDual (K F)) :
    ∃ B : Finset (Place F), ∀ T : Finset (Place F), B ⊆ T →
      Surjective (sIdeleClassInclusion F T) ∧
      globalNormOneCharacter F ω ∈ (sUnramified F T : Set (QuasiCharacter (IdeleClass F))) := by
  obtain ⟨A, hA⟩ := sIdeleClass_eventually_surjective F
  obtain ⟨B, hB⟩ := exists_sUnramified F (globalNormOneCharacter F ω)
  refine ⟨A ∪ B, fun T hT ↦ ⟨hA T (Finset.subset_union_left.trans hT), ?_⟩⟩
  apply (mem_sUnramified_iff F T _).mpr
  intro v hv u
  exact (mem_sUnramified_iff F B _).mp hB v
    (fun hb ↦ hv (hT (Finset.mem_union_right A hb))) u

private def normOneStageHaar (S : Finset (Place F)) : Measure (KS F S) := by
  letI := sLocalThetaNormOne_compact F S
  exact Measure.haar

private instance normOneStageHaar_isHaar (S : Finset (Place F)) :
    (normOneStageHaar F S).IsHaarMeasure := by
  letI := sLocalThetaNormOne_compact F S
  unfold normOneStageHaar
  infer_instance

section Cofinal

variable (μ : Measure (Idele F)) [μ.IsHaarMeasure] (ω : PontryaginDual (K F))
variable (B : Finset (Place F))
  (hB : ∀ T : Finset (Place F), B ⊆ T → Surjective (sIdeleClassInclusion F T) ∧
    globalNormOneCharacter F ω ∈ (sUnramified F T : Set (QuasiCharacter (IdeleClass F))))

private abbrev stageSurj (S : Finset (Place F)) := (hB (B ∪ S) Finset.subset_union_left).1
private abbrev stageUnram (S : Finset (Place F)) := (hB (B ∪ S) Finset.subset_union_left).2

/-- The actual homogeneous quotient at the cofinal place set `B ∪ S`. -/
abbrev HomogeneousThetaPlaceStage (S : Finset (Place F)) :=
  HS F ω (B ∪ S) (stageSurj F ω B hB S) (stageUnram F ω B hB S) (normOneStageHaar F (B ∪ S))

private abbrev Stage := HomogeneousThetaPlaceStage F ω B hB

private abbrev placeStage_p (S : Finset (Place F)) : L F (B ∪ S) →L[ℂ] Stage F ω B hB S :=
  pS F ω (B ∪ S) (stageSurj F ω B hB S) (stageUnram F ω B hB S) (normOneStageHaar F (B ∪ S))

private abbrev placeStage_j (S : Finset (Place F)) : Stage F ω B hB S →L[ℂ] L F (B ∪ S) :=
  jS F ω (B ∪ S) (stageSurj F ω B hB S) (stageUnram F ω B hB S) (normOneStageHaar F (B ∪ S))

private theorem placeStage_p_j (S : Finset (Place F)) :
    LeftInverse (placeStage_p F ω B hB S) (placeStage_j F ω B hB S) :=
  pS_jS F ω (B ∪ S) _ _ _

/-- Canonical insertion by padding with integer-ring indicators. -/
abbrev homogeneousThetaPlaceInclusion (S : Finset (Place F)) : Stage F ω B hB S →L[ℂ] HG F μ ω :=
  sLocalHomogeneousThetaToGlobal F μ ω (B ∪ S) (stageSurj F ω B hB S)
    (stageUnram F ω B hB S) (normOneStageHaar F (B ∪ S))

private theorem homogeneousThetaPlaceInclusion_pad (S : Finset (Place F)) (q : L F (B ∪ S)) :
    homogeneousThetaPlaceInclusion F μ ω B hB S (placeStage_p F ω B hB S q) =
      pG F μ ω (sLocalThetaToGlobal F (B ∪ S) q) :=
  DFunLike.congr_fun (sLocalHomogeneousThetaToGlobal_comp F μ ω (B ∪ S) _ _ _) q

/-- Cofinal homogeneous padding is a closed topological embedding. -/
theorem homogeneousThetaPlaceInclusion_isClosedEmbedding (S : Finset (Place F)) :
    IsClosedEmbedding (homogeneousThetaPlaceInclusion F μ ω B hB S) :=
  sLocalHomogeneousThetaToGlobal_isClosedEmbedding F μ ω (B ∪ S) _ _ _

/-- The stage-to-stage map induced by padding the tests. -/
def homogeneousThetaPlaceTransition {S T : Finset (Place F)} (h : S ⊆ T) :
    Stage F ω B hB S →L[ℂ] Stage F ω B hB T :=
  (placeStage_p F ω B hB T).comp
    ((sLocalThetaTransition F (Finset.union_subset_union_right (s := B) h)).comp (placeStage_j F ω B hB S))

theorem homogeneousThetaPlaceInclusion_transition {S T : Finset (Place F)} (h : S ⊆ T)
    (q : Stage F ω B hB S) :
    homogeneousThetaPlaceInclusion F μ ω B hB T (homogeneousThetaPlaceTransition F ω B hB h q) =
      homogeneousThetaPlaceInclusion F μ ω B hB S q := by
  change homogeneousThetaPlaceInclusion F μ ω B hB T (placeStage_p F ω B hB T
    (sLocalThetaTransition F (Finset.union_subset_union_right (s := B) h) (placeStage_j F ω B hB S q))) = _
  rw [homogeneousThetaPlaceInclusion_pad, sLocalThetaToGlobal_transition]
  rfl

include μ in
theorem homogeneousThetaPlaceTransition_pad {S T : Finset (Place F)} (h : S ⊆ T)
    (q : L F (B ∪ S)) :
    homogeneousThetaPlaceTransition F ω B hB h (placeStage_p F ω B hB S q) =
      placeStage_p F ω B hB T (sLocalThetaTransition F (Finset.union_subset_union_right (s := B) h) q) := by
  apply (homogeneousThetaPlaceInclusion_isClosedEmbedding F μ ω B hB T).isEmbedding.injective
  rw [homogeneousThetaPlaceInclusion_transition, homogeneousThetaPlaceInclusion_pad,
    homogeneousThetaPlaceInclusion_pad, sLocalThetaToGlobal_transition]

include μ in
theorem homogeneousThetaPlaceTransition_unique {S T : Finset (Place F)} (h : S ⊆ T)
    (A : Stage F ω B hB S →L[ℂ] Stage F ω B hB T)
    (hA : ∀ q, A (placeStage_p F ω B hB S q) =
      placeStage_p F ω B hB T (sLocalThetaTransition F (Finset.union_subset_union_right (s := B) h) q)) :
    A = homogeneousThetaPlaceTransition F ω B hB h := by
  apply ContinuousLinearMap.ext
  intro x
  have hx := placeStage_p_j F ω B hB S x
  rw [← hx, hA, homogeneousThetaPlaceTransition_pad F μ ω B hB h]

include μ in
theorem homogeneousThetaPlaceTransition_isClosedEmbedding {S T : Finset (Place F)} (h : S ⊆ T) :
    IsClosedEmbedding (homogeneousThetaPlaceTransition F ω B hB h) := by
  apply (homogeneousThetaPlaceInclusion_isClosedEmbedding F μ ω B hB T).of_comp_iff.mp
  rw [show homogeneousThetaPlaceInclusion F μ ω B hB T ∘ homogeneousThetaPlaceTransition F ω B hB h =
    homogeneousThetaPlaceInclusion F μ ω B hB S from funext (homogeneousThetaPlaceInclusion_transition F μ ω B hB h)]
  exact homogeneousThetaPlaceInclusion_isClosedEmbedding F μ ω B hB S

include μ in
theorem homogeneousThetaPlaceTransition_comp {S T U : Finset (Place F)} (h : S ⊆ T) (g : T ⊆ U)
    (q : Stage F ω B hB S) :
    homogeneousThetaPlaceTransition F ω B hB g (homogeneousThetaPlaceTransition F ω B hB h q) =
      homogeneousThetaPlaceTransition F ω B hB (h.trans g) q := by
  apply (homogeneousThetaPlaceInclusion_isClosedEmbedding F μ ω B hB U).isEmbedding.injective
  rw [homogeneousThetaPlaceInclusion_transition, homogeneousThetaPlaceInclusion_transition,
    homogeneousThetaPlaceInclusion_transition]

/-- The local idele-class action on a homogeneous stage. -/
def homogeneousThetaPlaceTranslate (S : Finset (Place F)) (c : SIdeleQuotient F (B ∪ S)) :
    Stage F ω B hB S →L[ℂ] Stage F ω B hB S :=
  (placeStage_p F ω B hB S).comp ((sLocalThetaTranslate F (B ∪ S) c).comp (placeStage_j F ω B hB S))

theorem continuous_homogeneousThetaPlaceTranslate (S : Finset (Place F)) :
    Continuous (fun z : SIdeleQuotient F (B ∪ S) × Stage F ω B hB S ↦
      homogeneousThetaPlaceTranslate F ω B hB S z.1 z.2) :=
  (placeStage_p F ω B hB S).continuous.comp <| (continuous_sLocalThetaTranslate F (B ∪ S)).comp
    (continuous_fst.prodMk ((placeStage_j F ω B hB S).continuous.comp continuous_snd))

/-- Homogeneous padding intertwines the open-block actions. -/
theorem homogeneousThetaPlaceInclusion_equivariant (S : Finset (Place F))
    (c : SIdeleClass F (B ∪ S)) (q : Stage F ω B hB S) :
    homogeneousThetaPlaceInclusion F μ ω B hB S
        (homogeneousThetaPlaceTranslate F ω B hB S (sIdeleClassToLocal F (B ∪ S) c) q) =
      globalHomogeneousThetaTranslate F μ ω (sIdeleClassInclusion F (B ∪ S) c)
        (homogeneousThetaPlaceInclusion F μ ω B hB S q) := by
  change homogeneousThetaPlaceInclusion F μ ω B hB S (placeStage_p F ω B hB S
    (sLocalThetaTranslate F (B ∪ S) (sIdeleClassToLocal F (B ∪ S) c) (placeStage_j F ω B hB S q))) =
    pG F μ ω (globalThetaTranslate F (sIdeleClassInclusion F (B ∪ S) c)
      (jG F μ ω (homogeneousThetaPlaceInclusion F μ ω B hB S q)))
  rw [homogeneousThetaPlaceInclusion_pad, sLocalThetaToGlobal_translate_blockClass,
    show jG F μ ω (homogeneousThetaPlaceInclusion F μ ω B hB S q) =
      sLocalThetaToGlobal F (B ∪ S) (placeStage_j F ω B hB S q)
      from jG_sLocalHomogeneousThetaToGlobal F μ ω (B ∪ S) _ _ _ q]

include μ in
theorem homogeneousThetaPlaceTranslate_one (S : Finset (Place F)) :
    homogeneousThetaPlaceTranslate F ω B hB S 1 = ContinuousLinearMap.id ℂ _ := by
  apply ContinuousLinearMap.ext
  intro q
  apply (homogeneousThetaPlaceInclusion_isClosedEmbedding F μ ω B hB S).isEmbedding.injective
  have h := homogeneousThetaPlaceInclusion_equivariant F μ ω B hB S 1 q
  rw [map_one, map_one, globalHomogeneousThetaTranslate_one] at h
  exact h

include μ in
theorem homogeneousThetaPlaceTranslate_mul (S : Finset (Place F)) (a b : SIdeleQuotient F (B ∪ S)) :
    homogeneousThetaPlaceTranslate F ω B hB S (a * b) =
      (homogeneousThetaPlaceTranslate F ω B hB S a).comp (homogeneousThetaPlaceTranslate F ω B hB S b) := by
  obtain ⟨c, rfl⟩ := (sIdeleClassToLocal_isOpenQuotientMap F (B ∪ S)).surjective a
  obtain ⟨d, rfl⟩ := (sIdeleClassToLocal_isOpenQuotientMap F (B ∪ S)).surjective b
  apply ContinuousLinearMap.ext
  intro q
  apply (homogeneousThetaPlaceInclusion_isClosedEmbedding F μ ω B hB S).isEmbedding.injective
  rw [ContinuousLinearMap.comp_apply, ← map_mul (sIdeleClassToLocal F (B ∪ S)),
    homogeneousThetaPlaceInclusion_equivariant, homogeneousThetaPlaceInclusion_equivariant,
    homogeneousThetaPlaceInclusion_equivariant, map_mul (sIdeleClassInclusion F (B ∪ S)),
    globalHomogeneousThetaTranslate_mul, ContinuousLinearMap.comp_apply]

include μ in
/-- Padding between two stages is equivariant for classes in the smaller block. -/
theorem homogeneousThetaPlaceTransition_equivariant {S T : Finset (Place F)} (h : S ⊆ T)
    (c : SIdeleClass F (B ∪ S)) (d : SIdeleClass F (B ∪ T))
    (hd : sIdeleClassInclusion F (B ∪ S) c = sIdeleClassInclusion F (B ∪ T) d)
    (q : Stage F ω B hB S) :
    homogeneousThetaPlaceTransition F ω B hB h
      (homogeneousThetaPlaceTranslate F ω B hB S (sIdeleClassToLocal F (B ∪ S) c) q) =
    homogeneousThetaPlaceTranslate F ω B hB T (sIdeleClassToLocal F (B ∪ T) d)
      (homogeneousThetaPlaceTransition F ω B hB h q) := by
  apply (homogeneousThetaPlaceInclusion_isClosedEmbedding F μ ω B hB T).isEmbedding.injective
  rw [homogeneousThetaPlaceInclusion_transition, homogeneousThetaPlaceInclusion_equivariant,
    homogeneousThetaPlaceInclusion_equivariant, homogeneousThetaPlaceInclusion_transition, hd]

theorem homogeneousThetaPlace_exhausted (q : HG F μ ω) :
    ∃ S : Finset (Place F), ∃ x : Stage F ω B hB S,
      homogeneousThetaPlaceInclusion F μ ω B hB S x = q := by
  obtain ⟨S, _, _, x, hx⟩ := globalThetaQuotient_exhausted_by_different_stages F ∅ (jG F μ ω q)
  let y := sLocalThetaTransition F (show S ⊆ B ∪ S from Finset.subset_union_right) x
  refine ⟨S, placeStage_p F ω B hB S y, ?_⟩
  rw [homogeneousThetaPlaceInclusion_pad, show sLocalThetaToGlobal F (B ∪ S) y = sLocalThetaToGlobal F S x
    from sLocalThetaToGlobal_transition F Finset.subset_union_right x, hx, pG_jG]

/-- The actual global homogeneous topology is locally convex final for the padded maps. -/
theorem homogeneousThetaPlace_continuous_of_stages {R : Type*} [AddCommGroup R] [Module ℂ R]
    [TopologicalSpace R] [PolynormableSpace ℂ R] (T : HG F μ ω →ₗ[ℂ] R)
    (hT : ∀ S : Finset (Place F), Continuous
      (T.comp (homogeneousThetaPlaceInclusion F μ ω B hB S).toLinearMap)) : Continuous T := by
  have h : Continuous (T.comp (pG F μ ω).toLinearMap) := by
    apply globalThetaQuotient_continuous_of_stages F
    intro S
    let a := sLocalThetaTransition F (show S ⊆ B ∪ S from Finset.subset_union_right)
    have he : (T.comp (pG F μ ω).toLinearMap).comp (sLocalThetaToGlobal F S).toLinearMap =
        (T.comp (homogeneousThetaPlaceInclusion F μ ω B hB S).toLinearMap).comp
          ((placeStage_p F ω B hB S).comp a).toLinearMap := by
      apply LinearMap.ext
      intro x
      change T (pG F μ ω (sLocalThetaToGlobal F S x)) =
        T (homogeneousThetaPlaceInclusion F μ ω B hB S (placeStage_p F ω B hB S (a x)))
      rw [homogeneousThetaPlaceInclusion_pad, sLocalThetaToGlobal_transition]
    rw [he]
    exact (hT S).comp ((placeStage_p F ω B hB S).comp a).continuous
  exact (h.comp (jG F μ ω).continuous).congr fun q ↦
    congrArg T (pG_jG F μ ω q)

/-- The actual homogeneous theta quotient is the strict limit of any cofinal
sequence of stages above the prescribed base. -/
def homogeneousThetaPlace_tower (S : ℕ → Finset (Place F)) (hS : Monotone S)
    (hcof : ∀ T, ∃ n, T ⊆ S n) :
    LinearInductivePresentation (HG F μ ω) (fun n ↦ Stage F ω B hB (S n)) where
  incl n := homogeneousThetaPlaceInclusion F μ ω B hB (S n)
  transition h := homogeneousThetaPlaceTransition F ω B hB (hS h)
  injective_incl n := (homogeneousThetaPlaceInclusion_isClosedEmbedding F μ ω B hB (S n)).isEmbedding.injective
  incl_transition h q := homogeneousThetaPlaceInclusion_transition F μ ω B hB (hS h) q
  exhaust q := by
    obtain ⟨T, x, hx⟩ := homogeneousThetaPlace_exhausted F μ ω B hB q
    obtain ⟨n, hn⟩ := hcof T
    exact ⟨n, homogeneousThetaPlaceTransition F ω B hB hn x,
      (homogeneousThetaPlaceInclusion_transition F μ ω B hB hn x).trans hx⟩
  continuous_limit T := ⟨fun h n ↦ h.comp (homogeneousThetaPlaceInclusion F μ ω B hB (S n)).continuous,
    fun h ↦ homogeneousThetaPlace_continuous_of_stages F μ ω B hB T (fun U ↦ by
      obtain ⟨n, hn⟩ := hcof U
      have he : T.comp (homogeneousThetaPlaceInclusion F μ ω B hB U).toLinearMap =
        (T.comp (homogeneousThetaPlaceInclusion F μ ω B hB (S n)).toLinearMap).comp
          (homogeneousThetaPlaceTransition F ω B hB hn).toLinearMap :=
        LinearMap.ext fun q ↦ congrArg T
          (homogeneousThetaPlaceInclusion_transition F μ ω B hB hn q).symm
      rw [he]
      exact (h n).comp (homogeneousThetaPlaceTransition F ω B hB hn).continuous)⟩

/-- Compatible linear maps out of the homogeneous stages descend uniquely to
the global homogeneous quotient. -/
theorem homogeneousThetaPlace_existsUnique_lift {R : Type*} [AddCommGroup R] [Module ℂ R]
    [TopologicalSpace R] [PolynormableSpace ℂ R]
    (A : ∀ S, Stage F ω B hB S →L[ℂ] R)
    (hA : ∀ (S T : Finset (Place F)) (h : S ⊆ T) x,
      A T (homogeneousThetaPlaceTransition F ω B hB h x) = A S x) :
    ∃! J : HG F μ ω →L[ℂ] R, ∀ S x, J (homogeneousThetaPlaceInclusion F μ ω B hB S x) = A S x := by
  let z (S : Finset (Place F)) : L F S →L[ℂ] R :=
    (A S).comp ((placeStage_p F ω B hB S).comp
      (sLocalThetaTransition F (show S ⊆ B ∪ S from Finset.subset_union_right)))
  have hz (S T : Finset (Place F)) (h : S ⊆ T) x :
      z T (sLocalThetaTransition F h x) = z S x := by
    change A T (placeStage_p F ω B hB T
      (sLocalThetaTransition F Finset.subset_union_right (sLocalThetaTransition F h x))) =
      A S (placeStage_p F ω B hB S (sLocalThetaTransition F Finset.subset_union_right x))
    have he : sLocalThetaTransition F (show T ⊆ B ∪ T from Finset.subset_union_right)
        (sLocalThetaTransition F h x) =
        sLocalThetaTransition F (Finset.union_subset_union_right (s := B) h)
          (sLocalThetaTransition F (show S ⊆ B ∪ S from Finset.subset_union_right) x) := by
      apply sLocalThetaToGlobal_injective F (B ∪ T)
      simp only [sLocalThetaToGlobal_transition]
    rw [he, ← homogeneousThetaPlaceTransition_pad F μ ω B hB h, hA]
  obtain ⟨J, hJ, _⟩ := globalThetaQuotient_existsUnique_lift F z hz
  refine ⟨J.comp (jG F μ ω), ?_, ?_⟩
  · intro S x
    have hj : jG F μ ω (homogeneousThetaPlaceInclusion F μ ω B hB S x) =
        sLocalThetaToGlobal F (B ∪ S) (placeStage_j F ω B hB S x) :=
      jG_sLocalHomogeneousThetaToGlobal F μ ω (B ∪ S) _ _ _ x
    change J (jG F μ ω (homogeneousThetaPlaceInclusion F μ ω B hB S x)) = A S x
    rw [hj, hJ]
    exact hA S (B ∪ S) Finset.subset_union_right x
  · intro J' hJ'
    apply ContinuousLinearMap.ext
    intro q
    obtain ⟨S, x, rfl⟩ := homogeneousThetaPlace_exhausted F μ ω B hB q
    rw [hJ']
    have hj := jG_sLocalHomogeneousThetaToGlobal F μ ω (B ∪ S)
      (stageSurj F ω B hB S) (stageUnram F ω B hB S) (normOneStageHaar F (B ∪ S)) x
    change A S x = J (jG F μ ω (homogeneousThetaPlaceInclusion F μ ω B hB S x))
    rw [hj, hJ]
    exact (hA S (B ∪ S) Finset.subset_union_right x).symm

private def homogeneousThetaPlaceRetraction (S : Finset (Place F)) :
    HG F μ ω →L[ℂ] Stage F ω B hB S :=
  (sLocalHomogeneousThetaToGlobal_exists_retraction F μ ω (B ∪ S) (stageSurj F ω B hB S)
    (stageUnram F ω B hB S) (normOneStageHaar F (B ∪ S))).choose

/-- A continuous global projection onto an actual homogeneous place stage. -/
def homogeneousThetaPlaceProjection (S : Finset (Place F)) : HG F μ ω →L[ℂ] HG F μ ω :=
  (homogeneousThetaPlaceInclusion F μ ω B hB S).comp
    (homogeneousThetaPlaceRetraction F μ ω B hB S)

theorem homogeneousThetaPlaceProjection_identity (S : Finset (Place F)) (x : Stage F ω B hB S) :
    homogeneousThetaPlaceProjection F μ ω B hB S (homogeneousThetaPlaceInclusion F μ ω B hB S x) =
      homogeneousThetaPlaceInclusion F μ ω B hB S x := by
  apply congrArg (homogeneousThetaPlaceInclusion F μ ω B hB S)
  exact (sLocalHomogeneousThetaToGlobal_exists_retraction F μ ω (B ∪ S) _ _ _).choose_spec x

theorem homogeneousThetaPlaceProjection_range (S : Finset (Place F)) :
    range (homogeneousThetaPlaceProjection F μ ω B hB S) =
      range (homogeneousThetaPlaceInclusion F μ ω B hB S) :=
  subset_antisymm (by
    rintro _ ⟨x, rfl⟩
    exact ⟨homogeneousThetaPlaceRetraction F μ ω B hB S x, rfl⟩) (by
    rintro _ ⟨x, rfl⟩
    exact ⟨_, homogeneousThetaPlaceProjection_identity F μ ω B hB S x⟩)

theorem homogeneousThetaPlaceProjection_idempotent (S : Finset (Place F)) :
    (homogeneousThetaPlaceProjection F μ ω B hB S).comp
      (homogeneousThetaPlaceProjection F μ ω B hB S) = homogeneousThetaPlaceProjection F μ ω B hB S := by
  apply ContinuousLinearMap.ext
  intro q
  exact homogeneousThetaPlaceProjection_identity F μ ω B hB S
    (homogeneousThetaPlaceRetraction F μ ω B hB S q)

/-- Every bounded family is fixed pointwise from one place set onward. -/
theorem homogeneousThetaPlaceProjection_eventually_eqOn_bounded
    (C : Set (HG F μ ω)) (hC : IsVonNBounded ℂ C) :
    ∀ᶠ S : Finset (Place F) in atTop, EqOn (homogeneousThetaPlaceProjection F μ ω B hB S) id C := by
  obtain ⟨T, A, _, hA⟩ := (globalThetaQuotient_bounded_iff F (jG F μ ω '' C)).mp (hC.image (jG F μ ω))
  filter_upwards [eventually_ge_atTop T] with S hS x hx
  have hx' : jG F μ ω x ∈ sLocalThetaToGlobal F T '' A := hA ▸ mem_image_of_mem _ hx
  obtain ⟨a, _, ha⟩ := hx'
  have hST : T ⊆ B ∪ S := hS.trans Finset.subset_union_right
  let y := sLocalThetaTransition F hST a
  have he : homogeneousThetaPlaceInclusion F μ ω B hB S (placeStage_p F ω B hB S y) = x := by
    rw [homogeneousThetaPlaceInclusion_pad, show sLocalThetaToGlobal F (B ∪ S) y = sLocalThetaToGlobal F T a
      from sLocalThetaToGlobal_transition F hST a, ha, pG_jG]
  change homogeneousThetaPlaceProjection F μ ω B hB S x = x
  rw [← he]
  exact homogeneousThetaPlaceProjection_identity F μ ω B hB S _

/-- The homogeneous stage projections converge in the topology of bounded convergence. -/
theorem homogeneousThetaPlaceProjection_tendsto :
    Tendsto (homogeneousThetaPlaceProjection F μ ω B hB) atTop
      (𝓝 (ContinuousLinearMap.id ℂ (HG F μ ω))) := by
  let I := ContinuousLinearMap.id ℂ (HG F μ ω)
  have h : Tendsto (fun S ↦ homogeneousThetaPlaceProjection F μ ω B hB S - I) atTop (𝓝 0) := by
    apply (ContinuousLinearMap.hasBasis_nhds_zero (σ := RingHom.id ℂ)
      («E» := HG F μ ω) (F := HG F μ ω)).tendsto_right_iff.mpr
    rintro ⟨C, U⟩ ⟨hC, hU⟩
    filter_upwards [homogeneousThetaPlaceProjection_eventually_eqOn_bounded F μ ω B hB C hC] with S hS
    intro x hx
    change homogeneousThetaPlaceProjection F μ ω B hB S x - x ∈ U
    rw [show homogeneousThetaPlaceProjection F μ ω B hB S x = x from hS hx, sub_self]
    exact mem_of_mem_nhds hU
  simpa only [sub_add_cancel, zero_add] using h.add (tendsto_const_nhds (x := I))

end Cofinal

end
end Masullo
