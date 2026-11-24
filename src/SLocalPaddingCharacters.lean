import SLocalMellinPadding
import HomogeneousThetaPlaceLimit
import IdelicOrbitalProducts
import SLocalLaurentFormula

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical NumberField SchwartzMap

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]
private abbrev Place := HeightOneSpectrum (𝓞 F)
/-- The Picard-group hypothesis of Proposition 7.2.2.1 makes the
original finite block meet every idele class. -/
theorem sIdeleClassInclusion_surjective_of_trivial_picard
    (S : Finset (Place F)) [Subsingleton (SPicardGroup F S)] :
    Surjective (sIdeleClassInclusion F S) := by
  let e := sIdeleClass_cokernelEquiv F S
  intro c
  have h : (QuotientGroup.mk c : IdeleClass F ⧸ (sIdeleClassInclusion F S).range) = 1 :=
    e.injective (Subsingleton.elim _ _)
  exact (QuotientGroup.eq_one_iff _).mp h

variable (S : Finset (Place F)) (ω : PontryaginDual (normOneIdeleClass F))
variable (hS : Surjective (sIdeleClassInclusion F S))
variable (hu : globalNormOneCharacter F ω ∈ (sUnramified F S : Set (QuasiCharacter (IdeleClass F))))

private theorem globalNormOneCharacter_expSection (t : Multiplicative ℝ) :
    globalNormOneCharacter F ω (ideleClassExpSection F t) = 1 := by
  change ((ω (ideleClassNormOnePart F (ideleClassExpSection F t))) : ℂ) = 1
  have h : ideleClassNormOnePart F (ideleClassExpSection F t) = 1 := by
    apply Subtype.ext
    change ideleClassExpSection F t / ideleClassExpSection F
      (ideleClassLogNorm F (ideleClassExpSection F t)) = 1
    rw [ideleClassLogNorm_expSection, div_self']
  rw [h, map_one, Circle.coe_one]

private theorem sLocal_zetaWeight_zero_eq_restriction (q : SIdeleQuotient F S) :
    sLocalZetaWeight F S (sLocalRestrictedNormOneCharacter F ω S hu) 0 q =
      sCharacterRestriction F S ⟨globalNormOneCharacter F ω, hu⟩ q := by
  let χ : sUnramified F S := ⟨globalNormOneCharacter F ω, hu⟩
  let c := sCharacterRestriction F S χ
  obtain ⟨⟨t, k⟩, rfl⟩ := (sLocalZetaSplit F S).surjective q
  rw [sLocalZetaWeight_split, zero_mul, Complex.exp_zero, one_mul]
  change c k.val = c (QuotientGroup.mk
    (sLocalExpSection F S (Multiplicative.ofAdd t)) * k.val)
  have hblock : ideleExpSection F (Multiplicative.ofAdd t) ∈ sIdeleBlock F S := by
    apply (sIdeleBlock_mem_iff F S _).mpr
    intro v _
    apply (ideleOrder_eq_zero_iff F _ v).mpr
    rw [(ideleExpSection_components F (Multiplicative.ofAdd t)).2]
    exact map_one _
  let g : sIdeleBlock F S := ⟨ideleExpSection F (Multiplicative.ofAdd t), hblock⟩
  have hray : c (QuotientGroup.mk (sLocalExpSection F S (Multiplicative.ofAdd t))) = 1 := by
    change c (sIdeleClassToLocal F S (QuotientGroup.mk g)) = 1
    rw [show c (sIdeleClassToLocal F S (QuotientGroup.mk g)) =
      χ.val (sIdeleClassInclusion F S (QuotientGroup.mk g)) from sCharacterRestriction_block F S χ _]
    exact globalNormOneCharacter_expSection F ω _
  rw [map_mul, hray, one_mul]

theorem sLocalZetaWeight_zero_restricted_global_block (g : sIdeleBlock F S) :
    sLocalZetaWeight F S (sLocalRestrictedNormOneCharacter F ω S hu) 0
      (QuotientGroup.mk (sBlockUnitProduct F S g).1) =
    globalNormOneCharacter F ω (ideleClassMap F g.val) := by
  rw [sLocal_zetaWeight_zero_eq_restriction F S ω hu]
  exact sCharacterRestriction_block F S ⟨globalNormOneCharacter F ω, hu⟩ (QuotientGroup.mk g)

theorem sLocalZetaWeight_zero_global_block (g : sIdeleBlock F S) :
    sLocalZetaWeight F S (sLocalNormOneCharacterOfGlobal F ω S hS hu) 0
      (QuotientGroup.mk (sBlockUnitProduct F S g).1) =
    globalNormOneCharacter F ω (ideleClassMap F g.val) :=
  sLocalZetaWeight_zero_restricted_global_block F S ω hu g

private theorem sLocalEmbed_finiteZetaInsert (v : S) (u : (v.val.adicCompletion F)ˣ) :
    (sLocalEmbed F S (sLocalFiniteZetaInsert F S v u)).val =
      singleFiniteIdele F v.val u := by
  apply Units.ext
  apply Prod.ext
  · rw [sLocalEmbed_arch]
    rfl
  · apply DFunLike.ext
    intro w
    by_cases hw : w ∈ S
    · have h := sLocalEmbed_finite F S (sLocalFiniteZetaInsert F S v u) ⟨w, hw⟩
      change _ = (Pi.mulSingle (M := fun v : S ↦ (v.val.adicCompletion F)ˣ) v u ⟨w, hw⟩).val at h
      rw [h]
      change _ = Function.update (fun j : Place F ↦ (1 : j.adicCompletion F)) v.val u.val w
      by_cases hwv : w = v.val
      · subst w
        change (Pi.mulSingle (M := fun v : S ↦ (v.val.adicCompletion F)ˣ) v u v).val = _
        rw [Pi.mulSingle_eq_same, Function.update_self]
      · rw [Pi.mulSingle_eq_of_ne (fun e ↦ hwv (congrArg Subtype.val e)), Function.update_of_ne hwv]
        rfl
    · rw [sLocalEmbed_outside_one F S _ w hw]
      change 1 = Function.update (fun j : Place F ↦ (1 : j.adicCompletion F)) v.val u.val w
      have hvw : w ≠ v.val := fun e ↦ hw (e.symm ▸ v.property)
      rw [Function.update_of_ne hvw]

/-- Each finite phase on the restricted stage is the original global
character evaluated on the same single-place idele. -/
theorem sLocalFiniteZetaPhases_of_global_restricted
    (v : S) (u : (v.val.adicCompletion F)ˣ) :
    (sLocalFiniteZetaPhases F S (sLocalRestrictedNormOneCharacter F ω S hu) v u : ℂ) =
      globalNormOneCharacter F ω (ideleClassMap F (singleFiniteIdele F v.val u)) := by
  let a := sLocalFiniteZetaInsert F S v u
  have h : (sBlockUnitProduct F S (sLocalEmbed F S a)).1 = a :=
    congrArg Prod.fst ((sBlockUnitProduct F S).apply_symm_apply (a, 1))
  have he := sLocalZetaWeight_zero_restricted_global_block F S ω hu (sLocalEmbed F S a)
  rw [h, sLocalEmbed_finiteZetaInsert F S v u] at he
  exact he

theorem sLocalFiniteZetaPhases_of_global
    (v : S) (u : (v.val.adicCompletion F)ˣ) :
    (sLocalFiniteZetaPhases F S (sLocalNormOneCharacterOfGlobal F ω S hS hu) v u : ℂ) =
      globalNormOneCharacter F ω (ideleClassMap F (singleFiniteIdele F v.val u)) :=
  sLocalFiniteZetaPhases_of_global_restricted F S ω hu v u

private theorem sLocalEmbed_archZetaInsert (a : (InfiniteAdeleRing F)ˣ) :
    (sLocalEmbed F S (sLocalArchZetaInsert F S a)).val = archIntoIdeles F a := by
  apply Units.ext
  apply Prod.ext
  · rw [sLocalEmbed_arch]
    rfl
  · apply DFunLike.ext
    intro w
    by_cases hw : w ∈ S
    · rw [sLocalEmbed_finite F S (sLocalArchZetaInsert F S a) ⟨w, hw⟩]
      rfl
    · rw [sLocalEmbed_outside_one F S _ w hw]
      rfl

private theorem sLocalZetaWeight_zero_global_arch (a : (InfiniteAdeleRing F)ˣ) :
    sLocalZetaWeight F S (sLocalRestrictedNormOneCharacter F ω S hu) 0
      (QuotientGroup.mk (sLocalArchZetaInsert F S a)) =
    globalNormOneCharacter F ω (ideleClassMap F (archIntoIdeles F a)) := by
  let b := sLocalArchZetaInsert F S a
  have hb : (sBlockUnitProduct F S (sLocalEmbed F S b)).1 = b :=
    congrArg Prod.fst ((sBlockUnitProduct F S).apply_symm_apply (b, 1))
  have he := sLocalZetaWeight_zero_restricted_global_block F S ω hu (sLocalEmbed F S b)
  rw [hb, sLocalEmbed_archZetaInsert F S a] at he
  exact he

/-- On an archimedean idele the stage weight is the actual global
norm-one character multiplied by the spectral power of the norm. -/
theorem sLocalZetaWeight_restricted_global_arch_apply (a : (InfiniteAdeleRing F)ˣ) (z : ℂ) :
    sLocalZetaWeight F S (sLocalRestrictedNormOneCharacter F ω S hu) z
      (QuotientGroup.mk (sLocalArchZetaInsert F S a)) =
    Complex.exp (z * (Real.log ‖a.val‖ : ℂ)) *
      globalNormOneCharacter F ω (ideleClassMap F (archIntoIdeles F a)) := by
  let b : SIdeleQuotient F S := QuotientGroup.mk (sLocalArchZetaInsert F S a)
  let τ := sLocalRestrictedNormOneCharacter F ω S hu
  have hb : ((sLocalZetaSplit F S).symm b).1 = Real.log ‖a.val‖ := by
    rw [← sLocalZetaSplit_logModulus F S, Homeomorph.apply_symm_apply]
    change Real.log (sLocalClassModulus F S (QuotientGroup.mk (sLocalArchZetaInsert F S a))) = _
    rw [sLocalClassModulus_mk, sLocalArchZetaInsert, sLocalZetaIdeleCoordinates_norm,
      InfiniteAdeleRing.norm_def]
    simp
  have hphase : (τ ((sLocalZetaSplit F S).symm b).2 : ℂ) =
      globalNormOneCharacter F ω (ideleClassMap F (archIntoIdeles F a)) := by
    simpa only [sLocalZetaWeight, zero_mul, Complex.exp_zero, one_mul] using
      sLocalZetaWeight_zero_global_arch F S ω hu a
  change Complex.exp (z * (((sLocalZetaSplit F S).symm b).1 : ℂ)) *
    (τ ((sLocalZetaSplit F S).symm b).2 : ℂ) = _
  rw [hb, hphase]

theorem sLocalZetaWeight_global_arch_apply (a : (InfiniteAdeleRing F)ˣ) (z : ℂ) :
    sLocalZetaWeight F S (sLocalNormOneCharacterOfGlobal F ω S hS hu) z
      (QuotientGroup.mk (sLocalArchZetaInsert F S a)) =
    Complex.exp (z * (Real.log ‖a.val‖ : ℂ)) *
      globalNormOneCharacter F ω (ideleClassMap F (archIntoIdeles F a)) :=
  sLocalZetaWeight_restricted_global_arch_apply F S ω hu a z

/-- Archimedean weights on two stages of the same global character are
identical, including the norm twist. -/
theorem sLocalZetaWeight_global_arch_eq
    (T : Finset (Place F)) (hT : Surjective (sIdeleClassInclusion F T))
    (huT : globalNormOneCharacter F ω ∈ (sUnramified F T : Set (QuasiCharacter (IdeleClass F))))
    (a : (InfiniteAdeleRing F)ˣ) (z : ℂ) :
    sLocalZetaWeight F T (sLocalNormOneCharacterOfGlobal F ω T hT huT) z
      (QuotientGroup.mk (sLocalArchZetaInsert F T a)) =
    sLocalZetaWeight F S (sLocalNormOneCharacterOfGlobal F ω S hS hu) z
      (QuotientGroup.mk (sLocalArchZetaInsert F S a)) := by
  rw [sLocalZetaWeight_global_arch_apply F T ω hT huT,
    sLocalZetaWeight_global_arch_apply F S ω hS hu]

/-- Agreement of the finite phases at each old place. -/
theorem sLocalFiniteZetaPhases_global_eq
    {T : Finset (Place F)} (hST : S ⊆ T)
    (hT : Surjective (sIdeleClassInclusion F T))
    (huT : globalNormOneCharacter F ω ∈ (sUnramified F T : Set (QuasiCharacter (IdeleClass F))))
    (v : S) :
    sLocalFiniteZetaPhases F T (sLocalNormOneCharacterOfGlobal F ω T hT huT) ⟨v.val, hST v.property⟩ =
      sLocalFiniteZetaPhases F S (sLocalNormOneCharacterOfGlobal F ω S hS hu) v := by
  ext u
  exact (sLocalFiniteZetaPhases_of_global F T ω hT huT ⟨v.val, hST v.property⟩ u).trans
    (sLocalFiniteZetaPhases_of_global F S ω hS hu v u).symm

include hu in
/-- Every newly added place is unramified when the smaller stage already
contains all the ramification of the global character. -/
theorem sLocalFiniteZetaPhases_global_unramified_new
    {T : Finset (Place F)} (hT : Surjective (sIdeleClassInclusion F T))
    (huT : globalNormOneCharacter F ω ∈ (sUnramified F T : Set (QuasiCharacter (IdeleClass F))))
    (v : T) (hv : v.val ∉ S) :
    finiteZetaUnramified F v.val
      (sLocalFiniteZetaPhases F T (sLocalNormOneCharacterOfGlobal F ω T hT huT) v) := by
  intro u hunit
  let a : (v.val.adicCompletionIntegers F)ˣ :=
    ⟨⟨u.val, hunit.1⟩, ⟨u.inv, hunit.2⟩, Subtype.ext u.val_inv, Subtype.ext u.inv_val⟩
  have ha : Units.map (v.val.adicCompletionIntegers F).subtype.toMonoidHom a = u := by
    apply Units.ext
    rfl
  apply Subtype.ext
  change (sLocalFiniteZetaPhases F T (sLocalNormOneCharacterOfGlobal F ω T hT huT) v u : ℂ) = 1
  rw [sLocalFiniteZetaPhases_of_global F T ω hT huT v u, ← ha]
  exact (mem_sUnramified_iff F S (globalNormOneCharacter F ω)).mp hu v.val hv a

variable [∀ v : Place F, MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : Place F, BorelSpace (v.adicCompletion F)ˣ]
  (μ : ∀ v : Place F, Measure (v.adicCompletion F)ˣ)
  [∀ v : Place F, (μ v).IsHaarMeasure] [∀ v : Place F, SigmaFinite (μ v)]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]

private abbrev Z (U : Finset (Place F)) (τ : PontryaginDual (SLocalThetaNormOne F U))
    (f : sLocalBruhatImage F U) :=
  sLocalProductZetaContinued F U (fun v ↦ μ v.val) τ (sLocalRealArchParameters F U τ)
    (sLocalComplexArchParameters F U τ) f

/-- The finite-stage Mellin germ comparison for the restrictions of a
single global character unramified outside the smaller stage. -/
theorem sLocalProductZetaContinued_global_pad
    {T : Finset (Place F)} (hST : S ⊆ T)
    (hT : Surjective (sIdeleClassInclusion F T))
    (huT : globalNormOneCharacter F ω ∈ (sUnramified F T : Set (QuasiCharacter (IdeleClass F))))
    (f : sLocalBruhatImage F S) (c : ℂ) :
    let ωS := sLocalNormOneCharacterOfGlobal F ω S hS hu
    let ωT := sLocalNormOneCharacterOfGlobal F ω T hT huT
    (fun z ↦ sLocalMellinPaddingDenominator F S (sLocalFiniteZetaPhases F T ωT) z *
        Z F μ T ωT (sLocalBruhatTransition F hST f) z) =ᶠ[𝓝[≠] c]
      fun z ↦ sLocalMellinPaddingHaarMass F μ S T * Z F μ S ωS f z := by
  intro ωS ωT
  apply sLocalProductZetaContinued_pad_germ_of_archIntegral F hST μ ωS ωT
    (sLocalFiniteZetaPhases_global_eq F S ω hS hu hST hT huT)
    (sLocalFiniteZetaPhases_global_unramified_new F S ω hu hT huT) _ f c
  intro φ z _
  apply integral_congr_ae
  exact .of_forall fun a ↦ congrArg (· * φ (InfiniteAdeleRing.ringEquiv_mixedSpace F a.val))
    (sLocalZetaWeight_global_arch_eq F S ω hS hu T hT huT a z)

/-- The order on the original stage equals the order of the padded
continuation plus the number of newly introduced Euler poles. -/
theorem sLocalProductZetaContinued_global_pad_order
    {T : Finset (Place F)} (hST : S ⊆ T)
    (hT : Surjective (sIdeleClassInclusion F T))
    (huT : globalNormOneCharacter F ω ∈ (sUnramified F T : Set (QuasiCharacter (IdeleClass F))))
    (f : sLocalBruhatImage F S) (c : ℂ) :
    let ωS := sLocalNormOneCharacterOfGlobal F ω S hS hu
    let ωT := sLocalNormOneCharacterOfGlobal F ω T hT huT
    meromorphicOrderAt (Z F μ S ωS f) c =
      (sLocalMellinPaddingPoleCount F S (sLocalFiniteZetaPhases F T ωT) c : WithTop ℤ) +
        meromorphicOrderAt (Z F μ T ωT (sLocalBruhatTransition F hST f)) c := by
  intro ωS ωT
  let D := sLocalMellinPaddingDenominator F S (sLocalFiniteZetaPhases F T ωT)
  let C := sLocalMellinPaddingHaarMass F μ S T
  have hD : AnalyticAt ℂ D c :=
    Finset.analyticAt_fun_prod _ (fun (v : {v : T // v.val ∉ S}) _ ↦
      finiteZetaDenominator_analytic F v.val.val (sLocalFiniteZetaPhases F T ωT v.val) c)
  have hS' : Meromorphic (Z F μ S ωS f) :=
    sLocalProductZetaContinued_meromorphic F S (fun v ↦ μ v.val) ωS _ _ f
  have hT' : Meromorphic (Z F μ T ωT (sLocalBruhatTransition F hST f)) :=
    sLocalProductZetaContinued_meromorphic F T (fun v ↦ μ v.val) ωT _ _ _
  have h := meromorphicOrderAt_congr
    (sLocalProductZetaContinued_global_pad F S ω hS hu μ hST hT huT f c)
  change meromorphicOrderAt (D * Z F μ T ωT (sLocalBruhatTransition F hST f)) c =
    meromorphicOrderAt ((fun _ ↦ C) * Z F μ S ωS f) c at h
  rw [meromorphicOrderAt_mul hD.meromorphicAt (hT' c),
    meromorphicOrderAt_mul (MeromorphicAt.const C c) (hS' c),
    meromorphicOrderAt_const, ite_eq_right (sLocalMellinPaddingHaarMass_ne_zero F μ (S := S) (T := T)), zero_add] at h
  rw [← h, sLocalMellinPaddingDenominator_order]

omit [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ] in
/-- The total allowed pole order grows by exactly the new finite factors. -/
theorem sLocalPoleCount_global_pad
    {T : Finset (Place F)} (hST : S ⊆ T)
    (hT : Surjective (sIdeleClassInclusion F T))
    (huT : globalNormOneCharacter F ω ∈ (sUnramified F T : Set (QuasiCharacter (IdeleClass F))))
    (c : ℂ) :
    let ωS := sLocalNormOneCharacterOfGlobal F ω S hS hu
    let ωT := sLocalNormOneCharacterOfGlobal F ω T hT huT
    sLocalPoleCount F T ωT c = sLocalPoleCount F S ωS c +
      sLocalMellinPaddingPoleCount F S (sLocalFiniteZetaPhases F T ωT) c := by
  intro ωS ωT
  obtain ⟨hR, hC⟩ := sLocalArchZetaDenominators_eq_of_weight F S ωS ωT
    (fun a ↦ (sLocalZetaWeight_global_arch_eq F S ω hS hu T hT huT a 0).symm)
  have hArch : sLocalArchPoleCount F S ωS c = sLocalArchPoleCount F T ωT c := by
    change
      (Finset.univ.filter fun v ↦ realArchZetaDenominator (sLocalRealArchParameters F S ωS v).2
        (c + (sLocalRealArchParameters F S ωS v).1) = 0).card +
      (Finset.univ.filter fun v ↦ complexArchZetaDenominator (sLocalComplexArchParameters F S ωS v).2
        (c + (sLocalComplexArchParameters F S ωS v).1) = 0).card =
      (Finset.univ.filter fun v ↦ realArchZetaDenominator (sLocalRealArchParameters F T ωT v).2
        (c + (sLocalRealArchParameters F T ωT v).1) = 0).card +
      (Finset.univ.filter fun v ↦ complexArchZetaDenominator (sLocalComplexArchParameters F T ωT v).2
        (c + (sLocalComplexArchParameters F T ωT v).1) = 0).card
    simp_rw [hR, hC]
  unfold sLocalPoleCount
  rw [← hArch, sLocalFinitePoleCount_pad F hST ωS ωT
    (sLocalFiniteZetaPhases_global_eq F S ω hS hu hST hT huT)
    (sLocalFiniteZetaPhases_global_unramified_new F S ω hu hT huT), add_assoc]

omit [∀ v : Place F, BorelSpace (v.adicCompletion F)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ] in
/-- The selected pole count is unchanged when the selected places are
viewed in a larger stage. -/
theorem sLocalSelectedFinitePoleCount_global_pad
    {T : Finset (Place F)} (hST : S ⊆ T)
    (hT : Surjective (sIdeleClassInclusion F T))
    (huT : globalNormOneCharacter F ω ∈ (sUnramified F T : Set (QuasiCharacter (IdeleClass F))))
    (W : Finset S) (c : ℂ) :
    let e : S ↪ T := ⟨fun v ↦ ⟨v.val, hST v.property⟩, fun _ _ h ↦ Subtype.ext (congrArg (fun w : T ↦ w.val) h)⟩
    sLocalSelectedFinitePoleCount F T (sLocalNormOneCharacterOfGlobal F ω T hT huT) (W.map e) c =
    sLocalSelectedFinitePoleCount F S (sLocalNormOneCharacterOfGlobal F ω S hS hu) W c := by
  intro e
  let p (v : T) := finiteZetaWeilMultiplier F v.val
    (sLocalFiniteZetaPhases F T (sLocalNormOneCharacterOfGlobal F ω T hT huT) v) c = 0
  let q (v : S) := finiteZetaWeilMultiplier F v.val
    (sLocalFiniteZetaPhases F S (sLocalNormOneCharacterOfGlobal F ω S hS hu) v) c = 0
  have hEq : p ∘ e = q := funext fun v ↦ by
    dsimp only [Function.comp_apply, p, q]
    rw [show sLocalFiniteZetaPhases F T (sLocalNormOneCharacterOfGlobal F ω T hT huT) (e v) =
      sLocalFiniteZetaPhases F S (sLocalNormOneCharacterOfGlobal F ω S hS hu) v from
      sLocalFiniteZetaPhases_global_eq F S ω hS hu hST hT huT v]
    rfl
  change ((W.map e).filter p).card = (W.filter q).card
  rw [Finset.filter_map, Finset.card_map]
  exact congrArg (fun p : S → Prop ↦ (W.filter p).card) hEq

/-- The selected principal-part order bound is equivalent before and
after padding, with the same finite places selected. -/
theorem sLocalSelectedPoleBound_global_pad_iff
    {T : Finset (Place F)} (hST : S ⊆ T)
    (hT : Surjective (sIdeleClassInclusion F T))
    (huT : globalNormOneCharacter F ω ∈ (sUnramified F T : Set (QuasiCharacter (IdeleClass F))))
    (W : Finset S) (f : sLocalBruhatImage F S) (c : ℂ) :
    let e : S ↪ T := ⟨fun v ↦ ⟨v.val, hST v.property⟩, fun _ _ h ↦ Subtype.ext (congrArg (fun w : T ↦ w.val) h)⟩
    let ωS := sLocalNormOneCharacterOfGlobal F ω S hS hu
    let ωT := sLocalNormOneCharacterOfGlobal F ω T hT huT
    (((sLocalSelectedFinitePoleCount F S ωS W c : ℤ) - (sLocalPoleCount F S ωS c : ℤ) : ℤ) ≤
      meromorphicOrderAt (Z F μ S ωS f) c) ↔
    (((sLocalSelectedFinitePoleCount F T ωT (W.map e) c : ℤ) - (sLocalPoleCount F T ωT c : ℤ) : ℤ) ≤
      meromorphicOrderAt (Z F μ T ωT (sLocalBruhatTransition F hST f)) c) := by
  intro e ωS ωT
  let d := sLocalPoleCount F S ωS c
  let t := sLocalSelectedFinitePoleCount F S ωS W c
  let n := sLocalMellinPaddingPoleCount F S (sLocalFiniteZetaPhases F T ωT) c
  have ho := sLocalProductZetaContinued_global_pad_order F S ω hS hu μ hST hT huT f c
  have hd : sLocalPoleCount F T ωT c = d + n :=
    sLocalPoleCount_global_pad F S ω hS hu hST hT huT c
  have ht : sLocalSelectedFinitePoleCount F T ωT (W.map e) c = t :=
    sLocalSelectedFinitePoleCount_global_pad F S ω hS hu hST hT huT W c
  change meromorphicOrderAt (Z F μ S ωS f) c =
    (n : WithTop ℤ) + meromorphicOrderAt (Z F μ T ωT (sLocalBruhatTransition F hST f)) c at ho
  rw [ho, hd, ht]
  cases meromorphicOrderAt (Z F μ T ωT (sLocalBruhatTransition F hST f)) c with
  | top => simp
  | coe k =>
    rw [show (n : WithTop ℤ) = ((n : ℤ) : WithTop ℤ) from rfl, ← WithTop.coe_add]
    simp only [WithTop.coe_le_coe, Nat.cast_add]
    omega

end

end Masullo
