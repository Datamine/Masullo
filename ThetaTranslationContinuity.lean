import AdelicSchwartzNuclear
import SLocalThetaFourier

open Bornology Filter Function IsDedekindDomain NumberField Set Topology
open scoped Classical NumberField

namespace Masullo

noncomputable section

/-- A locally compact parameter family of continuous linear maps on a barrelled
space acts jointly continuously if each orbit is continuous. -/
theorem continuous_joint_of_barrelled {G E : Type*}
    [TopologicalSpace G] [LocallyCompactSpace G]
    [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E]
    [ContinuousSMul ℂ E] [PolynormableSpace ℂ E] [BarrelledSpace ℂ E]
    (A : G → E →L[ℂ] E) (hA : ∀ x, Continuous (fun g ↦ A g x)) :
    Continuous (fun z : G × E ↦ A z.1 z.2) := by
  apply continuous_iff_continuousAt.mpr
  rintro ⟨g, x⟩
  obtain ⟨K, hK, hKg⟩ := exists_compact_mem_nhds g
  let W := PolynormableSpace.withSeminorms ℂ E
  let f (a : K) : E →L[ℂ] E := A a.val
  have hb (y : E) : IsVonNBounded ℂ (range fun a : K ↦ f a y) := by
    have hC := (hK.image (hA y)).isVonNBounded ℂ
    exact hC.subset (by rintro _ ⟨a, rfl⟩; exact ⟨a.val, a.property, rfl⟩)
  have he := PolynormableSpace.banach_steinhaus (𝓕 := f) hb
  have hQ := (W.uniformEquicontinuous_iff_exists_continuous_seminorm
    (fun k : K ↦ (f k).toLinearMap)).mp he
  have hzero : Tendsto (fun z : G × E ↦ A z.1 (z.2 - x)) (𝓝 (g, x)) (𝓝 0) := by
    apply (W.tendsto_nhds _ _).mpr
    intro q ε hε
    obtain ⟨p, hp, hqp⟩ := hQ q
    have hsmall : Tendsto (fun z : G × E ↦ p (z.2 - x)) (𝓝 (g, x)) (𝓝 0) :=
      (hp.tendsto' 0 0 (map_zero p)).comp ((continuous_snd.sub continuous_const).tendsto'
        (g, x) 0 (sub_self x))
    have hK' := (continuous_fst.tendsto' (g, x) g rfl).eventually hKg
    filter_upwards [hK', hsmall (Iio_mem_nhds hε)] with z hz hpz
    rw [sub_zero]
    exact (hqp ⟨z.1, hz⟩ (z.2 - x)).trans_lt hpz
  have horbit := ((hA x).comp continuous_fst).tendsto' (g, x) (A g x) rfl
  change Tendsto (fun z : G × E ↦ A z.1 z.2) (𝓝 (g, x)) (𝓝 (A g x))
  simpa only [map_sub, Function.comp_apply, sub_add_cancel, zero_add] using hzero.add horbit

universe u

variable (F : Type u) [Field F] [NumberField F]
variable (S : Finset (HeightOneSpectrum (𝓞 F)))

/-- Translation by ideles is jointly continuous on the ordinary global theta quotient. -/
theorem continuous_globalThetaTranslateIdeles :
    Continuous (fun z : Idele F × GlobalThetaQuotient F ↦
      globalThetaTranslateIdeles F z.1 z.2) := by
  have hOrbit (q : GlobalThetaQuotient F) :
      Continuous (fun g : Idele F ↦ globalThetaTranslateIdeles F g q) := by
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    exact (globalThetaOperator F).ker.mkQL.continuous.comp
      (GlobalBruhat.continuous_leftTranslate_orbit F f)
  letI : LocallyCompactSpace (Idele F) := ideles_locallyCompact
  letI : UniformSpace (GlobalThetaQuotient F) := IsTopologicalAddGroup.rightUniformSpace _
  letI : IsUniformAddGroup (GlobalThetaQuotient F) := isUniformAddGroup_of_addCommGroup
  letI : BarrelledSpace ℂ (GlobalThetaQuotient F) := globalThetaQuotient_barrelled F
  letI : PolynormableSpace ℂ (GlobalThetaQuotient F) :=
    polynormableSpace_complex_quotient (globalThetaOperator F).ker
  exact continuous_joint_of_barrelled (globalThetaTranslateIdeles F) hOrbit

/-- The ordinary global theta quotient carries a jointly continuous action of
the idele class group. -/
theorem continuous_globalThetaTranslate :
    Continuous (fun z : IdeleClass F × GlobalThetaQuotient F ↦
      globalThetaTranslate F z.1 z.2) := by
  let Q := GlobalThetaQuotient F
  have hp : IsOpenQuotientMap (ideleClassMap F : Idele F → IdeleClass F) :=
    QuotientGroup.isOpenQuotientMap_mk
  apply (hp.prodMap (IsOpenQuotientMap.id (X := Q))).isQuotientMap.continuous_iff.mpr
  exact (continuous_globalThetaTranslateIdeles F).congr fun z ↦ by
    change globalThetaTranslateIdeles F z.1 z.2 =
      globalThetaTranslate F (ideleClassMap F z.1) z.2
    rw [globalThetaTranslate_class]

/-- The joint action on the ordinary S-local theta quotient is induced by the
global action under the closed stage embedding. -/
theorem continuous_sLocalThetaTranslateIdeles :
    Continuous (fun z : (SAdeles F S)ˣ × SLocalThetaQuotient F S ↦
      sLocalThetaTranslateIdeles F S z.1 z.2) := by
  have he : Continuous (fun g : (SAdeles F S)ˣ ↦ (sLocalEmbed F S g).val) :=
    continuous_subtype_val.comp
      ((sBlockUnitProduct F S).symm.continuous.comp (continuous_id.prodMk continuous_const))
  apply (sLocalThetaToGlobal_isClosedEmbedding F S).isEmbedding.isInducing.continuous_iff.mpr
  have h := (continuous_globalThetaTranslateIdeles F).comp
    ((he.comp continuous_fst).prodMk ((sLocalThetaToGlobal F S).continuous.comp continuous_snd))
  exact h.congr fun z ↦ (sLocalThetaToGlobal_translate F S z.1 z.2).symm

/-- The action by S-local idele classes is jointly continuous on theta. -/
theorem continuous_sLocalThetaTranslate :
    Continuous (fun z : SIdeleQuotient F S × SLocalThetaQuotient F S ↦
      sLocalThetaTranslate F S z.1 z.2) := by
  let Q := SLocalThetaQuotient F S
  have hp : IsOpenQuotientMap (QuotientGroup.mk : (SAdeles F S)ˣ → SIdeleQuotient F S) :=
    QuotientGroup.isOpenQuotientMap_mk
  exact (hp.prodMap (IsOpenQuotientMap.id (X := Q))).isQuotientMap.continuous_iff.mpr
    (continuous_sLocalThetaTranslateIdeles F S)

theorem bruhatTranslate_block_eq (a : sIdeleBlock F S) (f : sLocalBruhatImage F S) :
    GlobalBruhat.leftTranslate F a.val f.val =
      GlobalBruhat.leftTranslate F (sLocalEmbed F S (sBlockUnitProduct F S a).1).val f.val := by
  let b := sLocalEmbed F S (sBlockUnitProduct F S a).1
  have ha : sAdelesProjection F S (a.val⁻¹).val = (sBlockUnitProduct F S a).1.inv := rfl
  have hb : sAdelesProjection F S (b.val⁻¹).val = (sBlockUnitProduct F S a).1.inv := by
    rw [show b.val⁻¹ = (sLocalEmbed F S ((sBlockUnitProduct F S a).1⁻¹)).val by
      rw [map_inv, Subgroup.coe_inv], sLocalEmbed_project]
    rfl
  have htail (c : sIdeleBlock F S) (x : Adeles F) :
      (∀ w ∉ S, ((c.val⁻¹).val * x).2 w ∈ w.adicCompletionIntegers F) ↔
      (∀ w ∉ S, x.2 w ∈ w.adicCompletionIntegers F) := by
    refine forall₂_congr fun w hw ↦ ?_
    change c.val.inv.2 w * x.2 w ∈ w.adicCompletionIntegers F ↔
      x.2 w ∈ w.adicCompletionIntegers F
    constructor
    · intro hx
      have he : c.val.val.2 w * c.val.inv.2 w = 1 :=
        congrArg (fun y : Adeles F ↦ y.2 w) c.val.val_inv
      have h := mul_mem (c.property.1 w hw) hx
      change c.val.val.2 w * (c.val.inv.2 w * x.2 w) ∈ w.adicCompletionIntegers F at h
      rwa [← mul_assoc, he, one_mul] at h
    · exact mul_mem (c.property.2 w hw)
  apply (GlobalBruhat.algebraicEquiv F).injective
  apply Subtype.ext
  funext x
  change GlobalBruhat.evaluation F x (GlobalBruhat.leftTranslate F a.val f.val) =
    GlobalBruhat.evaluation F x (GlobalBruhat.leftTranslate F b.val f.val)
  simp only [GlobalBruhat.leftTranslate_apply, sLocalBruhatRestriction_reconstruct, map_mul, ha, hb, htail]

/-- Compatibility through the quotient of the open idele-class block. -/
theorem sLocalThetaToGlobal_translate_blockClass (c : SIdeleClass F S)
    (q : SLocalThetaQuotient F S) :
    sLocalThetaToGlobal F S (sLocalThetaTranslate F S (sIdeleClassToLocal F S c) q) =
      globalThetaTranslate F (sIdeleClassInclusion F S c) (sLocalThetaToGlobal F S q) := by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective c
  rw [sIdeleClassToLocal_mk]
  rw [sLocalThetaToGlobal_translate_class]
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  change globalThetaTranslate F (ideleClassMap F (sLocalEmbed F S (sBlockUnitProduct F S a).1).val)
      (Submodule.Quotient.mk f.val) =
    globalThetaTranslate F (ideleClassMap F a.val) (Submodule.Quotient.mk f.val)
  rw [globalThetaTranslate_class, globalThetaTranslate_class,
    globalThetaTranslateIdeles_mk, globalThetaTranslateIdeles_mk,
    bruhatTranslate_block_eq F S a f]

/-- The jointly continuous action of the open block factors through the
quotient discarding the integral tail. -/
theorem continuous_sLocalThetaTranslate_blockClass :
    Continuous (fun z : SIdeleClass F S × SLocalThetaQuotient F S ↦
      sLocalThetaTranslate F S (sIdeleClassToLocal F S z.1) z.2) :=
  (continuous_sLocalThetaTranslate F S).comp
    (((sIdeleClassToLocal_isOpenQuotientMap F S).continuous.comp continuous_fst).prodMk
      continuous_snd)

theorem sLocalThetaTranslate_one (q : SLocalThetaQuotient F S) :
    sLocalThetaTranslate F S 1 q = q := by
  apply sLocalThetaToGlobal_injective F S
  rw [← (sIdeleClassToLocal F S).map_one, sLocalThetaToGlobal_translate_blockClass,
    map_one, globalThetaTranslate_one]
  rfl

/-- The finite-stage principal-translation differences in (6.1.1.1)
are zero on the ordinary theta quotient. -/
theorem sLocalTheta_principalDifference_zero (g : sUnitImage F S) :
    ContinuousLinearMap.id ℂ (SLocalThetaQuotient F S) -
      sLocalThetaTranslate F S (QuotientGroup.mk g.val) = 0 := by
  have hg : (QuotientGroup.mk g.val : SIdeleQuotient F S) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr g.property
  rw [hg]
  ext q
  change q - sLocalThetaTranslate F S 1 q = 0
  rw [sLocalThetaTranslate_one, sub_self]

/-- Every principal-translation difference in (6.1.1.2) is zero
on the ordinary global theta quotient. -/
theorem globalTheta_principalDifference_zero (t : Fˣ) :
    ContinuousLinearMap.id ℂ (GlobalThetaQuotient F) -
      globalThetaTranslate F (ideleClassMap F (principalIdele F t)) = 0 := by
  have ht : ideleClassMap F (principalIdele F t) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr ⟨t,rfl⟩
  rw [ht, globalThetaTranslate_one, sub_self]

theorem sLocalThetaTranslate_mul (c d : SIdeleQuotient F S) (q : SLocalThetaQuotient F S) :
    sLocalThetaTranslate F S (c * d) q = sLocalThetaTranslate F S c (sLocalThetaTranslate F S d q) := by
  obtain ⟨a, rfl⟩ := (sIdeleClassToLocal_isOpenQuotientMap F S).surjective c
  obtain ⟨b, rfl⟩ := (sIdeleClassToLocal_isOpenQuotientMap F S).surjective d
  apply sLocalThetaToGlobal_injective F S
  rw [← map_mul, sLocalThetaToGlobal_translate_blockClass, map_mul, globalThetaTranslate_mul,
    ContinuousLinearMap.comp_apply, sLocalThetaToGlobal_translate_blockClass,
    sLocalThetaToGlobal_translate_blockClass]

/-- A continuous transition induced by padding the tests is unique. -/
theorem sLocalThetaTransition_unique {A B : Finset (HeightOneSpectrum (𝓞 F))} (h : A ⊆ B)
    (L : SLocalThetaQuotient F A →L[ℂ] SLocalThetaQuotient F B)
    (hL : ∀ f : sLocalBruhatImage F A,
      L (Submodule.Quotient.mk f) = Submodule.Quotient.mk (sLocalBruhatTransition F h f)) :
    L = sLocalThetaTransition F h := by
  ext q
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rw [hL, sLocalThetaTransition_mk]

end

end Masullo
