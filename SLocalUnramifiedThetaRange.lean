import SLocalThetaStageRetraction
import SLocalPaleyWiener
import GlobalMellinPadding
import NuclearCriteria

open Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical NumberField

namespace Masullo

noncomputable section

universe u

variable (F : Type u) [Field F] [NumberField F]

private abbrev Place := HeightOneSpectrum (𝓞 F)
private abbrev E := sLocalBruhatImage F
private abbrev K := normOneIdeleClass F

local instance unramifiedThetaNormOneMeasurable : MeasurableSpace (K F) := borel _
local instance unramifiedThetaNormOneBorel : BorelSpace (K F) := ⟨rfl⟩

variable (νG : Measure (K F)) [νG.IsHaarMeasure]
variable (ω : PontryaginDual (K F))

private theorem globalHomogeneousTheta_integralUnit
    {S : Finset (Place F)}
    (hω : globalNormOneCharacter F ω ∈ (sUnramified F S : Set (QuasiCharacter (IdeleClass F))))
    (v : Place F) (hv : v ∉ S) (u : (v.adicCompletion F)ˣ)
    (hu : u ∈ finitePlaceIntegralUnits F v) (f : GlobalBruhat F) :
    globalHomogeneousThetaOperator F νG ω (GlobalBruhat.leftTranslate F (singleFiniteIdele F v u) f) =
      globalHomogeneousThetaOperator F νG ω f := by
  let g := singleFiniteIdele F v u
  have hg : ideleNorm F g = 1 :=
    (singleFiniteIdele_norm F v u).trans
      ((finiteCompletion_norm_eq_one_iff F v u).mpr ((localIntegralUnits_value F v u).mp hu))
  let k : K F := ⟨ideleClassMap F g, by
    change ideleClassNorm F (ideleClassMap F g) = 1
    rw [ideleClassNorm_mk, hg]⟩
  change globalHomogeneousThetaOperator F νG ω (GlobalBruhat.leftTranslate F g f) = _
  rw [globalHomogeneousThetaOperator_translate F νG ω k g rfl]
  have hu' := (Submonoid.mem_units_iff (v.adicCompletionIntegers F).toSubmonoid u).mp hu
  let a : (v.adicCompletionIntegers F)ˣ :=
    ⟨⟨u.val, hu'.1⟩, ⟨u.inv, hu'.2⟩, Subtype.ext u.val_inv, Subtype.ext u.inv_val⟩
  have ha : Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom a = u := Units.ext rfl
  have hχ := (mem_sUnramified_iff F S (globalNormOneCharacter F ω)).mp hω v hv a
  rw [ha] at hχ
  change globalNormOneCharacter F ω k.val = 1 at hχ
  rw [globalNormOneCharacter_apply F ω k] at hχ
  rw [hχ, one_smul]

private theorem globalHomogeneousTheta_translate_on_stage
    (S : Finset (Place F)) (a : Idele F) (f : E F S) :
    ∃ g : E F S,
      globalHomogeneousThetaOperator F νG ω (GlobalBruhat.leftTranslate F a f.val) =
        globalHomogeneousThetaOperator F νG ω g.val := by
  let t := Real.log (ideleNorm F a)
  let r := ideleExpSection F (Multiplicative.ofAdd t)
  let d := a * r⁻¹
  have hr : ideleNorm F r = ideleNorm F a := by
    change ideleNorm F (ideleExpSection F (Multiplicative.ofAdd t)) = _
    rw [ideleNorm_expSection, toAdd_ofAdd, Real.exp_log (ideleNorm_pos F a)]
  have hd : ideleNorm F d = 1 := by
    dsimp only [d]
    rw [map_mul, map_inv (ideleNorm F), hr, mul_inv_cancel₀ (ideleNorm_pos F a).ne']
  let k : K F := ⟨ideleClassMap F d, by
    change ideleClassNorm F (ideleClassMap F d) = 1
    rw [ideleClassNorm_mk, hd]⟩
  let b := sLocalBruhatLeftTranslate F S (sLocalExpSection F S (Multiplicative.ofAdd t)) f
  have hb : b.val = GlobalBruhat.leftTranslate F r f.val := by
    change GlobalBruhat.leftTranslate F
      (sLocalEmbed F S (sLocalExpSection F S (Multiplicative.ofAdd t))).val f.val = _
    rw [sLocalExpSection_embed]
  have ha : GlobalBruhat.leftTranslate F a f.val = GlobalBruhat.leftTranslate F d b.val := by
    rw [hb]
    apply (GlobalBruhat.algebraicEquiv F).injective
    apply Subtype.ext
    funext x
    change GlobalBruhat.evaluation F x (GlobalBruhat.leftTranslate F a f.val) =
      GlobalBruhat.evaluation F x (GlobalBruhat.leftTranslate F d (GlobalBruhat.leftTranslate F r f.val))
    rw [GlobalBruhat.leftTranslate_apply, GlobalBruhat.leftTranslate_apply,
      GlobalBruhat.leftTranslate_apply, ← mul_assoc]
    have he : d * r = a := by simp [d]
    rw [← Units.val_mul, ← mul_inv_rev, he]
  refine ⟨(ω k : ℂ) • b, ?_⟩
  change globalHomogeneousThetaOperator F νG ω (GlobalBruhat.leftTranslate F a f.val) =
    globalHomogeneousThetaOperator F νG ω ((ω k : ℂ) • b.val)
  rw [ha, map_smul, globalHomogeneousThetaOperator_translate F νG ω k d rfl]

private theorem exists_sLocalBaseRepresentative_union
    (S B : Finset (Place F)) (hB : Disjoint B S)
    (hω : globalNormOneCharacter F ω ∈ (sUnramified F S : Set (QuasiCharacter (IdeleClass F))))
    (f : E F (B ∪ S)) :
    ∃ g : E F S, globalHomogeneousThetaOperator F νG ω f.val =
      globalHomogeneousThetaOperator F νG ω g.val := by
  induction B using Finset.induction_on with
  | empty =>
    exact ⟨⟨f.val, by simpa only [Finset.empty_union] using f.property⟩,rfl⟩
  | insert v B hv ih =>
    obtain ⟨hvS,hBS⟩ := Finset.disjoint_insert_left.mp hB
    let A := B ∪ S
    have hvA : v ∉ A := by simp [A,hv,hvS]
    let f' : E F (insert v A) := ⟨f.val, by
      rw [← Finset.insert_union]; exact f.property⟩
    obtain ⟨g,hg⟩ := exists_sLocalBaseRepresentative_onePlace F A v hvA
      (globalHomogeneousThetaOperator F νG ω)
      (globalHomogeneousTheta_integralUnit F νG ω hω v hvS)
      (fun n a ↦ globalHomogeneousTheta_translate_on_stage F νG ω A
        (singleFiniteIdele F v (chosenFiniteUniformizer F v ^ n)) a) f'
    obtain ⟨b,hb⟩ := ih hBS g
    exact ⟨b,hg.trans hb⟩

/-- Enlarging an unramified stage does not enlarge the image of that stage
under the global homogeneous theta map. -/
theorem exists_sLocalBaseRepresentative_of_unramified
    {S T : Finset (Place F)} (hST : S ⊆ T)
    (hω : globalNormOneCharacter F ω ∈ (sUnramified F S : Set (QuasiCharacter (IdeleClass F))))
    (f : E F T) :
    ∃ g : E F S, globalHomogeneousThetaOperator F νG ω f.val =
      globalHomogeneousThetaOperator F νG ω g.val := by
  let f' : E F ((T \ S) ∪ S) := ⟨f.val, by
    rw [Finset.sdiff_union_of_subset hST]; exact f.property⟩
  exact exists_sLocalBaseRepresentative_union F νG ω S (T \ S) Finset.sdiff_disjoint hω f'


section Quotients

local instance unramifiedThetaIdeleMeasurable : MeasurableSpace (Idele F) := borel _
local instance unramifiedThetaIdeleBorel : BorelSpace (Idele F) := ⟨rfl⟩
attribute [local instance] sLocalZetaUnfolding_classMeasurable sLocalZetaUnfolding_classBorel

variable (η : Measure (Idele F)) [η.IsHaarMeasure]
variable (hν : IsWeilQuotientMeasure (principalIdeles F) η Measure.count (globalClassMeasure F νG))

include hν in
private theorem globalComponent_mkQ_eq_of_homogeneousTheta_eq (f g : GlobalBruhat F)
    (he : globalHomogeneousThetaOperator F νG ω f = globalHomogeneousThetaOperator F νG ω g) :
    (globalIdelicZetaComponentKernel F η ω).mkQ f =
      (globalIdelicZetaComponentKernel F η ω).mkQ g := by
  apply (Submodule.Quotient.eq _).mpr
  apply (mem_globalIdelicZetaComponentKernel F η νG hν ω (f-g)).mpr
  apply (adelicHomogeneousTheta_zero_iff_continuedZeta F νG (f-g) ω).mp
  have h : globalHomogeneousThetaOperator F νG ω (f-g) = 0 := by
    rw [map_sub, he, sub_self]
  exact congrFun h

theorem sIdeleClassInclusion_surjective_mono {S T : Finset (Place F)} (hST : S ⊆ T)
    (hS : Surjective (sIdeleClassInclusion F S)) : Surjective (sIdeleClassInclusion F T) := by
  intro x
  obtain ⟨a,rfl⟩ := hS x
  obtain ⟨g,rfl⟩ := QuotientGroup.mk_surjective a
  exact ⟨QuotientGroup.mk (sIdeleTransition F hST g),rfl⟩

theorem sUnramified_mono {S T : Finset (Place F)} (hST : S ⊆ T)
    {χ : QuasiCharacter (IdeleClass F)} (hχ : χ ∈ (sUnramified F S : Set _)) :
    χ ∈ (sUnramified F T : Set _) :=
  (mem_sUnramified_iff F T χ).mpr fun v hv u ↦
    (mem_sUnramified_iff F S χ).mp hχ v (fun h ↦ hv (hST h)) u

/-- Triviality of the localized ideal class group is the covering hypothesis
for the open S-idèle class block. -/
theorem sIdeleClassInclusion_surjective_of_subsingleton_sPicard
    (S : Finset (Place F)) [Subsingleton (SPicardGroup F S)] :
    Surjective (sIdeleClassInclusion F S) := by
  intro a
  have ha : a ∈ (sLocalizedIdeleClassMap F S).ker := Subsingleton.elim _ _
  rw [sLocalizedIdeleClassMap_ker] at ha
  exact ha

/-- The global isotype is exhausted by any unramified block meeting every
idele class. The lift is provided by reducing finite tests place by place. -/
theorem sLocalHomogeneousThetaToGlobal_surjective
    (S : Finset (Place F)) (hs : Surjective (sIdeleClassInclusion F S))
    (hu : globalNormOneCharacter F ω ∈ (sUnramified F S : Set (QuasiCharacter (IdeleClass F))))
    (ν : Measure (SLocalThetaNormOne F S)) [ν.IsHaarMeasure] :
    Surjective (sLocalHomogeneousThetaToGlobal F η ω S hs hu ν) := by
  obtain ⟨ρ, hρ, hW⟩ := globalClassMeasure_exists_weil F η
  intro x
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective (globalIdelicZetaComponentKernel F η ω) x
  obtain ⟨T, hST, _, q, hq⟩ := globalThetaQuotient_exhausted_by_different_stages F S
    (Submodule.Quotient.mk f)
  obtain ⟨g, rfl⟩ := Submodule.Quotient.mk_surjective (sLocalThetaOperator F T).ker q
  obtain ⟨b, hb⟩ := exists_sLocalBaseRepresentative_of_unramified F ρ ω hST hu g
  let p := sLocalThetaToComponent F S ν (sLocalNormOneCharacterOfGlobal F ω S hs hu)
  refine ⟨p (Submodule.Quotient.mk b), ?_⟩
  have hp := DFunLike.congr_fun (sLocalHomogeneousThetaToGlobal_comp F η ω S hs hu ν)
    (Submodule.Quotient.mk b)
  change sLocalHomogeneousThetaToGlobal F η ω S hs hu ν (p (Submodule.Quotient.mk b)) =
    globalThetaToComponent F η ω (sLocalThetaToGlobal F S (Submodule.Quotient.mk b)) at hp
  rw [hp, sLocalThetaToGlobal_mk]
  rw [sLocalThetaToGlobal_mk] at hq
  change (globalIdelicZetaComponentKernel F η ω).mkQ b.val =
    (globalIdelicZetaComponentKernel F η ω).mkQ f
  rw [← globalComponent_mkQ_eq_of_homogeneousTheta_eq F ρ ω η hW g.val b.val hb]
  exact congrArg (globalThetaToComponent F η ω) hq

/-- The canonical padding map onto the global homogeneous theta quotient is
a continuous linear equivalence. -/
def sLocalHomogeneousThetaToGlobalEquiv
    (S : Finset (Place F)) (hs : Surjective (sIdeleClassInclusion F S))
    (hu : globalNormOneCharacter F ω ∈ (sUnramified F S : Set (QuasiCharacter (IdeleClass F))))
    (ν : Measure (SLocalThetaNormOne F S)) [ν.IsHaarMeasure] :
    SLocalHomogeneousThetaQuotient F S ν (sLocalNormOneCharacterOfGlobal F ω S hs hu) ≃L[ℂ]
      (GlobalBruhat F ⧸ globalIdelicZetaComponentKernel F η ω) := by
  let j := sLocalHomogeneousThetaToGlobal F η ω S hs hu ν
  let h := sLocalHomogeneousThetaToGlobal_exists_retraction F η ω S hs hu ν
  exact ContinuousLinearEquiv.equivOfInverse j h.choose h.choose_spec (h.choose_spec.rightInverse_of_surjective
    (sLocalHomogeneousThetaToGlobal_surjective F ω η S hs hu ν))

include η in
/-- The two polar moments have rank two on the trivial homogeneous S-local
theta quotient when the S-local idele classes cover the global classes. -/
theorem sLocalPolarFree_image_codimension_trivial
    (S : Finset (Place F)) (hs : Surjective (sIdeleClassInclusion F S))
    (hu : globalNormOneCharacter F 1 ∈ (sUnramified F S : Set (QuasiCharacter (IdeleClass F))))
    (ν : Measure (SLocalThetaNormOne F S)) [ν.IsHaarMeasure] :
    let M := sLocalHomogeneousThetaKernel F S ν (sLocalNormOneCharacterOfGlobal F 1 S hs hu)
    let P := ((GlobalBruhat.polarEvaluation F).comp (E F S).subtypeL).ker
    Module.finrank ℂ ((E F S ⧸ M) ⧸ P.map M.mkQ) = 2 := by
  intro M P
  obtain ⟨ρ, hρ, hW⟩ := globalClassMeasure_exists_weil F η
  let N := globalIdelicZetaComponentKernel F η 1
  let e := sLocalHomogeneousThetaToGlobalEquiv F 1 η S hs hu ν
  have he (f : E F S) : e (M.mkQ f) = N.mkQ f.val :=
    DFunLike.congr_fun (sLocalHomogeneousThetaToGlobal_comp F η 1 S hs hu ν)
      ((sLocalThetaOperator F S).ker.mkQ f)
  have hN : N ≤ (GlobalBruhat.polarEvaluation F).ker := by
    intro f hf
    change GlobalBruhat.polarEvaluation F f = 0
    apply globalPolarEvaluation_eq_zero_of_trivialHomogeneous F ρ f
    exact (adelicHomogeneousTheta_zero_iff_continuedZeta F ρ f 1).mpr
      ((mem_globalIdelicZetaComponentKernel F η ρ hW 1 f).mp hf)
  let A := (GlobalBruhat.polarEvaluation F).toLinearMap
  let B := N.liftQ A hN
  let C := B.comp e.toLinearMap
  have hC (f : E F S) : C (M.mkQ f) = GlobalBruhat.polarEvaluation F f.val := by
    change B (e (M.mkQ f)) = _
    rw [he]
    rfl
  have hsurj : Surjective C := by
    intro x
    obtain ⟨f, hf⟩ := GlobalBruhat.polarEvaluation_surjective F x
    obtain ⟨q, hq⟩ := e.surjective (N.mkQ f)
    refine ⟨q, ?_⟩
    change B (e q) = x
    rw [hq]
    exact hf
  have hker : C.ker = P.map M.mkQ := by
    ext q
    obtain ⟨f, rfl⟩ := M.mkQ_surjective q
    constructor
    · intro hf
      refine Submodule.mem_map.mpr ⟨f, ?_, rfl⟩
      change GlobalBruhat.polarEvaluation F f.val = 0
      exact (hC f).symm.trans (LinearMap.mem_ker.mp hf)
    · rintro ⟨g, hg, heq⟩
      rw [← heq]
      exact (hC g).trans hg
  rw [← hker, (C.quotKerEquivOfSurjective hsurj).finrank_eq,
    Module.finrank_prod, Module.finrank_self]

/-- A character of a block meeting every global class is the descended
character of its pullback to the global norm-one group. -/
theorem exists_globalNormOneCharacter_of_local
    (T : Finset (Place F)) (hs : Surjective (sIdeleClassInclusion F T))
    (χ : PontryaginDual (SLocalThetaNormOne F T)) :
    ∃ (ω : PontryaginDual (K F))
      (hu : globalNormOneCharacter F ω ∈ (sUnramified F T : Set (QuasiCharacter (IdeleClass F)))),
      (∀ k, ω k = χ (globalNormOneToSLocal F T hs k)) ∧
      sLocalNormOneCharacterOfGlobal F ω T hs hu = χ := by
  let ω := χ.comp (globalNormOneToSLocal F T hs)
  have hu := (normOneCharacter_unramified_iff_unique_descent F ω T).mpr ?_
  · refine ⟨ω, hu, fun _ ↦ rfl, ?_⟩
    ext a
    obtain ⟨k, rfl⟩ := globalNormOneToSLocal_surjective F T hs a
    exact congrArg Subtype.val (sLocalNormOneCharacterOfGlobal_match F ω T hs hu k)
  · refine ⟨χ, ?_, ?_⟩
    · intro b hb
      change χ _ = χ _
      congr 1
      apply Subtype.ext
      exact (globalNormOneToSLocal_val_of_block F T hs _ b rfl).symm
    · intro ψ hψ
      ext a
      obtain ⟨b, ha⟩ := (sIdeleClassToLocal_isOpenQuotientMap F T).surjective a.val
      have hb : sIdeleClassToLocal F T b ∈ SLocalThetaNormOne F T := ha ▸ a.property
      have he : (⟨sIdeleClassToLocal F T b, hb⟩ : SLocalThetaNormOne F T) = a := Subtype.ext ha
      rw [← he, hψ b hb]
      change (χ _ : ℂ) = _
      congr 2
      apply Subtype.ext
      exact globalNormOneToSLocal_val_of_block F T hs _ b rfl

include η in
/-- Canonical padding between two blocks beyond the conductor is a
continuous linear equivalence, and sends each source test to its padded test. -/
theorem exists_homogeneousTheta_paddingEquiv
    {S T : Finset (Place F)} (hST : S ⊆ T)
    (hs : Surjective (sIdeleClassInclusion F S))
    (hu : globalNormOneCharacter F ω ∈ (sUnramified F S : Set (QuasiCharacter (IdeleClass F))))
    (νS : Measure (SLocalThetaNormOne F S)) [νS.IsHaarMeasure]
    (νT : Measure (SLocalThetaNormOne F T)) [νT.IsHaarMeasure] :
    let pS := sLocalThetaToComponent F S νS (sLocalNormOneCharacterOfGlobal F ω S hs hu)
    let pT := sLocalThetaToComponent F T νT
      (sLocalNormOneCharacterOfGlobal F ω T (sIdeleClassInclusion_surjective_mono F hST hs)
        (sUnramified_mono F hST hu))
    ∃ e : _ ≃L[ℂ] _, ∀ f : E F S,
      e (pS (Submodule.Quotient.mk f)) =
        pT (Submodule.Quotient.mk (sLocalBruhatTransition F hST f)) := by
  dsimp only
  let hsT := sIdeleClassInclusion_surjective_mono F hST hs
  let huT := sUnramified_mono F hST hu
  let eS := sLocalHomogeneousThetaToGlobalEquiv F ω η S hs hu νS
  let eT := sLocalHomogeneousThetaToGlobalEquiv F ω η T hsT huT νT
  refine ⟨eS.trans eT.symm, fun f ↦ eT.injective ?_⟩
  rw [ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.apply_symm_apply]
  change sLocalHomogeneousThetaToGlobal F η ω S hs hu νS _ =
    sLocalHomogeneousThetaToGlobal F η ω T hsT huT νT _
  have hS := DFunLike.congr_fun (sLocalHomogeneousThetaToGlobal_comp F η ω S hs hu νS)
    (Submodule.Quotient.mk f)
  have hT := DFunLike.congr_fun (sLocalHomogeneousThetaToGlobal_comp F η ω T hsT huT νT)
    (Submodule.Quotient.mk (sLocalBruhatTransition F hST f))
  exact hS.trans hT.symm

include η in
/-- The local character of the larger stage in Theorem 6.2.1.1(1) is
regarded on the global norm-one group via the canonical projection. -/
theorem exists_homogeneousTheta_paddingEquiv_of_local
    {S T : Finset (Place F)} (hST : S ⊆ T) [Subsingleton (SPicardGroup F S)]
    (χ : PontryaginDual (SLocalThetaNormOne F T))
    (hu : globalNormOneCharacter F
      (χ.comp (globalNormOneToSLocal F T (sIdeleClassInclusion_surjective_mono F hST
        (sIdeleClassInclusion_surjective_of_subsingleton_sPicard F S)))) ∈
      (sUnramified F S : Set (QuasiCharacter (IdeleClass F))))
    (νS : Measure (SLocalThetaNormOne F S)) [νS.IsHaarMeasure]
    (νT : Measure (SLocalThetaNormOne F T)) [νT.IsHaarMeasure] :
    let hs := sIdeleClassInclusion_surjective_of_subsingleton_sPicard F S
    let ω := χ.comp (globalNormOneToSLocal F T (sIdeleClassInclusion_surjective_mono F hST hs))
    let pS := sLocalThetaToComponent F S νS (sLocalNormOneCharacterOfGlobal F ω S hs hu)
    let pT := sLocalThetaToComponent F T νT χ
    ∃ e : _ ≃L[ℂ] _, ∀ f : E F S,
      e (pS (Submodule.Quotient.mk f)) =
        pT (Submodule.Quotient.mk (sLocalBruhatTransition F hST f)) := by
  dsimp only
  let hs := sIdeleClassInclusion_surjective_of_subsingleton_sPicard F S
  let hsT := sIdeleClassInclusion_surjective_mono F hST hs
  let ω := χ.comp (globalNormOneToSLocal F T hsT)
  have he : sLocalNormOneCharacterOfGlobal F ω T hsT (sUnramified_mono F hST hu) = χ := by
    ext a
    obtain ⟨k, rfl⟩ := globalNormOneToSLocal_surjective F T hsT a
    exact congrArg Subtype.val (sLocalNormOneCharacterOfGlobal_match F ω T hsT _ k)
  have h := exists_homogeneousTheta_paddingEquiv F ω η hST hs hu νS νT
  dsimp only at h
  generalize sLocalNormOneCharacterOfGlobal F ω T hsT (sUnramified_mono F hST hu) = ψ at he h
  subst ψ
  exact h

include hν in
/-- Every enlarged homogeneous class has an inserted representative
at the original unramified stage. If the given test has both moments zero,
the representative can be chosen with the same two zero moments. -/
theorem exists_sLocalBaseRepresentative_preserves_zero_moments
    {S T : Finset (Place F)} (hST : S ⊆ T)
    (hs : Surjective (sIdeleClassInclusion F S))
    (hu : globalNormOneCharacter F ω ∈ (sUnramified F S : Set (QuasiCharacter (IdeleClass F))))
    (νT : Measure (SLocalThetaNormOne F T)) [νT.IsHaarMeasure]
    (f : E F T) :
    let hsT := sIdeleClassInclusion_surjective_mono F hST hs
    let huT := sUnramified_mono F hST hu
    let M := sLocalHomogeneousThetaKernel F T νT (sLocalNormOneCharacterOfGlobal F ω T hsT huT)
    ∃ g : E F S, M.mkQ f = M.mkQ (sLocalBruhatTransition F hST g) ∧
      (GlobalBruhat.polarEvaluation F f.val = 0 → GlobalBruhat.polarEvaluation F g.val = 0) := by
  dsimp only
  let hsT := sIdeleClassInclusion_surjective_mono F hST hs
  let huT := sUnramified_mono F hST hu
  let M := sLocalHomogeneousThetaKernel F T νT (sLocalNormOneCharacterOfGlobal F ω T hsT huT)
  let j := sLocalHomogeneousThetaToGlobal F η ω T hsT huT νT
  let Q := (globalIdelicZetaComponentKernel F η ω).mkQ
  have hj (x : E F T) : j (M.mkQ x) = Q x.val :=
    DFunLike.congr_fun (sLocalHomogeneousThetaToGlobal_comp F η ω T hsT huT νT)
      ((sLocalThetaOperator F T).ker.mkQ x)
  have hq (g : E F S) (h : Q f.val = Q g.val) : M.mkQ f = M.mkQ (sLocalBruhatTransition F hST g) := by
    apply (sLocalHomogeneousThetaToGlobal_isClosedEmbedding F η ω T hsT huT νT).injective
    rw [hj, hj]
    exact h
  change ∃ g : E F S, M.mkQ f = M.mkQ (sLocalBruhatTransition F hST g) ∧
    (GlobalBruhat.polarEvaluation F f.val = 0 → GlobalBruhat.polarEvaluation F g.val = 0)
  obtain ⟨g,hg⟩ := exists_sLocalBaseRepresentative_of_unramified F νG ω hST hu f
  have h := globalComponent_mkQ_eq_of_homogeneousTheta_eq F νG ω η hν f.val g.val hg
  by_cases hw : ω = 1
  · refine ⟨g, hq g h, fun hzero ↦ ?_⟩
    have he : globalHomogeneousThetaOperator F νG 1 (f.val-g.val) = 0 := by
      rw [← hw, map_sub, hg, sub_self]
    have hp := globalPolarEvaluation_eq_zero_of_trivialHomogeneous F νG (f.val-g.val)
      (congrFun he)
    rw [map_sub, hzero, zero_sub, neg_eq_zero] at hp
    exact hp
  · obtain ⟨g',hzero,hg'⟩ :=
      exists_sLocal_polarEvaluation_zero_same_globalClass F η ω S hs hu νG hν hw g
    exact ⟨g',hq g' (h.trans hg'.symm),fun _ ↦ hzero⟩

end Quotients

section Frechet

local instance unramifiedThetaPaddingIdeleMeasurable : MeasurableSpace (Idele F) := borel _
local instance unramifiedThetaPaddingIdeleBorel : BorelSpace (Idele F) := ⟨rfl⟩
attribute [local instance] sLocalZetaUnfolding_classMeasurable sLocalZetaUnfolding_classBorel

/-- Every S-local norm-one character has an open integral-unit level in its
kernel. At each selected place, its finite-place restriction is locally constant. -/
theorem exists_sLocalNormOneCharacter_unitLevel
    (S : Finset (Place F)) (χ : PontryaginDual (SLocalThetaNormOne F S)) :
    ∃ H : ∀ v : S, Subgroup (v.val.adicCompletion F)ˣ,
      (∀ v : S, IsOpen (H v : Set (v.val.adicCompletion F)ˣ)) ∧
      (∀ (v : S) (a : H v), ‖a.val.val‖ = 1) ∧
      ∀ a : ∀ v : S, H v, ∃ k : SLocalThetaNormOne F S,
        k.val = QuotientGroup.mk (angularLocalIdele F S H a) ∧ χ k = 1 := by
  let d (v : S) : (v.val.adicCompletion F)ˣ →ₜ* ℂ :=
    ⟨Circle.coeHom.comp (sLocalFiniteZetaPhases F S χ v).toMonoidHom,
      continuous_subtype_val.comp (sLocalFiniteZetaPhases F S χ v).continuous⟩
  let H (v : S) := principalIntegralUnits F v.val ⊓ (d v).toMonoidHom.ker
  have hH (v : S) : IsOpen (H v : Set (v.val.adicCompletion F)ˣ) := by
    have hu : (principalIntegralUnits F v.val : Set (v.val.adicCompletion F)ˣ) =
        finitePlaceIntegralUnits F v.val := by
      ext u
      exact (finiteCompletion_norm_eq_one_iff F v.val u).trans
        (localIntegralUnits_value F v.val u).symm
    have hU : IsOpen (principalIntegralUnits F v.val : Set (v.val.adicCompletion F)ˣ) :=
      hu ▸ localIntegralUnits_open F v.val
    exact hU.inter
      (IsLocallyConstant.iff_isOpen_fiber.mp (finiteQuasiCharacter_isLocallyConstant F v.val (d v)) 1)
  have hn (v : S) (a : H v) : ‖a.val.val‖ = 1 := a.property.1
  refine ⟨H, hH, hn, fun a ↦ ?_⟩
  let g := angularLocalIdele F S H a
  have hg : g = (sLocalZetaIdeleCoordinates F S).symm (1, fun v ↦ (a v).val) := rfl
  have hk : QuotientGroup.mk g ∈ SLocalThetaNormOne F S := by
    apply Units.ext
    apply NNReal.eq
    change sLocalClassModulus F S (QuotientGroup.mk g) = 1
    rw [sLocalClassModulus_mk, hg, sLocalZetaIdeleCoordinates_norm]
    have ho (w : InfinitePlace F) : (1 : InfiniteAdeleRing F) w = 1 := rfl
    simp only [Units.val_one, ho, norm_one, one_pow, Finset.prod_const_one, one_mul, hn]
  let k : SLocalThetaNormOne F S := ⟨QuotientGroup.mk g, hk⟩
  refine ⟨k, rfl, Subtype.ext ?_⟩
  rw [← sLocalNormOnePhase_normOne F S χ k]
  change ((sLocalNormOnePhase F S χ (QuotientGroup.mk g)).val : ℂ) = 1
  have harch : sLocalArchZetaInsert F S 1 = 1 := by
    change (sLocalZetaIdeleCoordinates F S).symm 1 = 1
    exact map_one _
  let p := (sLocalNormOnePhase F S χ).toMonoidHom.comp (QuotientGroup.mk' (sUnitImage F S))
  have hv (v : S) : p (sLocalFiniteZetaInsert F S v (a v).val) = 1 := by
    apply Units.ext
    exact (a v).property.2
  change (p g).val = 1
  rw [hg, sLocalZetaIdeleCoordinates_factor, harch, one_mul, map_prod]
  simp [hv]

/-- The S-local homogeneous theta quotient is Fréchet for every isotype. -/
theorem sLocalHomogeneousTheta_isFrechet (S : Finset (Place F))
    (ν : Measure (SLocalThetaNormOne F S)) [ν.IsHaarMeasure]
    (χ : PontryaginDual (SLocalThetaNormOne F S)) :
    IsFrechetTVS (SLocalHomogeneousThetaQuotient F S ν χ) := by
  obtain ⟨H, hH, hn, hχ⟩ := exists_sLocalNormOneCharacter_unitLevel F S χ
  exact sLocalHomogeneousTheta_isFrechet_of_unitLevel F S ν χ H hH hn hχ

/-- Theorem 5.4.1.1(2). The S-local homogeneous quotient is separable
nuclear Fréchet for every norm-one character. -/
theorem sLocalHomogeneousTheta_separableNuclearFrechet (S : Finset (Place F))
    (ν : Measure (SLocalThetaNormOne F S)) [ν.IsHaarMeasure]
    (χ : PontryaginDual (SLocalThetaNormOne F S)) :
    let Q := SLocalHomogeneousThetaQuotient F S ν χ
    TopologicalSpace.SeparableSpace Q ∧ NuclearLocallyConvex.{u, u} Q ∧ IsFrechetTVS Q := by
  let Q := SLocalHomogeneousThetaQuotient F S ν χ
  have hF := sLocalHomogeneousTheta_isFrechet F S ν χ
  have hN := (sLocalHomogeneousTheta_primalStructure F S ν χ).1
  letI : TopologicalSpace.MetrizableSpace Q := hF.2.2.1
  exact ⟨nuclearLocallyConvex_separable_of_firstCountable hN, hN, hF⟩

/-- Corollary 6.2.1.2. The global homogeneous theta quotient is nuclear Fréchet
for each continuous norm-one character. -/
theorem globalHomogeneousTheta_nuclearFrechet
    (η : Measure (Idele F)) [η.IsHaarMeasure] :
    let Q := GlobalBruhat F ⧸ globalIdelicZetaComponentKernel F η ω
    IsFrechetTVS Q ∧ NuclearLocallyConvex.{u, u} Q := by
  obtain ⟨S, hS⟩ := exists_homogeneousThetaPlaceBase F ω
  obtain ⟨hs, hu⟩ := hS S le_rfl
  letI := sLocalThetaNormOne_compact F S
  let ν : Measure (SLocalThetaNormOne F S) := Measure.haar
  let χ := sLocalNormOneCharacterOfGlobal F ω S hs hu
  let e := sLocalHomogeneousThetaToGlobalEquiv F ω η S hs hu ν
  obtain ⟨_, hpoly, hmet, _⟩ := sLocalHomogeneousTheta_isFrechet F S ν χ
  obtain ⟨hN, hC, _⟩ := globalHomogeneousTheta_primalStructure F η ω
  refine ⟨⟨inferInstance, ?_, e.symm.toHomeomorph.isEmbedding.metrizableSpace, hC⟩, hN⟩
  exact (e.symm.toHomeomorph.isInducing.withSeminorms (f := e.symm.toLinearMap)
    (PolynormableSpace.withSeminorms ℂ (SLocalHomogeneousThetaQuotient F S ν χ))).toPolynormableSpace

end Frechet

end

end Masullo
