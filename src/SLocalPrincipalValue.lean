import SLocalBruhatProjections
import WeilPrincipalValue
import LocallyConstantProduct
import Mathlib.Data.Finset.NoncommProd

open Filter Function IsDedekindDomain NumberField Set Topology
open scoped Classical NumberField SchwartzMap TensorProduct

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

private abbrev Place := HeightOneSpectrum (𝓞 F)
private abbrev Arch := 𝓢(mixedEmbedding.mixedSpace F, ℂ)
private abbrev Coord (S : Finset (Place F)) := (v : S) → v.val.adicCompletion F
private abbrev Test (S : Finset (Place F)) := locallyConstantTests (Coord F S)
private abbrev Local (v : Place F) := locallyConstantTests (v.adicCompletion F)

def sLocalFiniteCoordinateSplit (S : Finset (Place F)) (v : S) :
    Coord F S ≃ₜ v.val.adicCompletion F × ((w : {w : S // w ≠ v}) → w.val.val.adicCompletion F) :=
  Homeomorph.piSplitAt v _

/-- Apply a finite-place endomorphism to the selected coordinate of the
actual S-local finite test function. -/
def sLocalCoordinateMap (S : Finset (Place F)) (v : S) (L : Local F v →ₗ[ℂ] Local F v) :
    Test F S →ₗ[ℂ] Test F S :=
  let e := locallyConstantTestCongr (sLocalFiniteCoordinateSplit F S v)
  e.symm.toLinearMap.comp ((locallyConstantTestMapFirst L).comp e.toLinearMap)

private def sLocalCoordinateSection (S : Finset (Place F)) (v : S) (f : Test F S)
    (x : Coord F S) : Local F v :=
  locallyConstantTestSection (locallyConstantTestCongr (sLocalFiniteCoordinateSplit F S v) f)
    (sLocalFiniteCoordinateSplit F S v x).2

private theorem sLocalFiniteCoordinateSplit_symm_same (S : Finset (Place F)) (v : S)
    (x : Coord F S) (a : v.val.adicCompletion F) :
    (sLocalFiniteCoordinateSplit F S v).symm (a, (sLocalFiniteCoordinateSplit F S v x).2) = Function.update x v a := by
  funext w
  by_cases hw : w = v
  · subst w
    simp [sLocalFiniteCoordinateSplit, Homeomorph.piSplitAt, Equiv.piSplitAt]
  · simp [sLocalFiniteCoordinateSplit, Homeomorph.piSplitAt, Equiv.piSplitAt, hw]

theorem sLocalCoordinateSection_apply (S : Finset (Place F)) (v : S)
    (f : Test F S) (x : Coord F S) (a : v.val.adicCompletion F) :
    (sLocalCoordinateSection F S v f x).val a = f.val (Function.update x v a) := by
  change f.val ((sLocalFiniteCoordinateSplit F S v).symm (a, (sLocalFiniteCoordinateSplit F S v x).2)) = _
  rw [sLocalFiniteCoordinateSplit_symm_same]

theorem sLocalCoordinateMap_apply (S : Finset (Place F)) (v : S) (L : Local F v →ₗ[ℂ] Local F v)
    (f : Test F S) (x : Coord F S) :
    (sLocalCoordinateMap F S v L f).val x = (L (sLocalCoordinateSection F S v f x)).val (x v) := by
  let e := sLocalFiniteCoordinateSplit F S v
  let g := locallyConstantTestCongr e f
  change (locallyConstantTestMapFirst L g).val (e x) =
    (L (locallyConstantTestSection g (e x).2)).val (e x).1
  rw [← locallyConstantTestMapFirst_section]
  rfl

/-- A coordinate operator that commutes with multiplication in its local
field commutes with all product translations of the finite test space. -/
theorem sLocalCoordinateMap_translate (S : Finset (Place F)) (v : S)
    (L : Local F v →ₗ[ℂ] Local F v) (g : (Coord F S)ˣ)
    (hL : ∀ (r : (v.val.adicCompletion F)ˣ) (f : Local F v),
      L (locallyConstantTestTranslate _ r f) = locallyConstantTestTranslate _ r (L f))
    (f : Test F S) :
    sLocalCoordinateMap F S v L (locallyConstantTestTranslate _ g f) =
      locallyConstantTestTranslate _ g (sLocalCoordinateMap F S v L f) := by
  let r := Units.map (Pi.evalRingHom (fun w : S ↦ w.val.adicCompletion F) v).toMonoidHom g
  apply Subtype.ext
  funext x
  have hup (a : v.val.adicCompletion F) :
      g⁻¹ • Function.update x v a = Function.update (g⁻¹ • x) v (r⁻¹ • a) := by
    funext w
    by_cases hw : w = v
    · subst w
      change g.inv v * Function.update x v a v = Function.update (g⁻¹ • x) v (r.inv * a) v
      rw [Function.update_self, Function.update_self]
      rfl
    · change g.inv w * Function.update x v a w =
        Function.update (g⁻¹ • x) v (r⁻¹ • a) w
      rw [Function.update_of_ne hw, Function.update_of_ne hw]
      rfl
  have hSection :
      sLocalCoordinateSection F S v (locallyConstantTestTranslate _ g f) x =
        locallyConstantTestTranslate _ r (sLocalCoordinateSection F S v f (g⁻¹ • x)) := by
    apply Subtype.ext
    funext a
    rw [sLocalCoordinateSection_apply]
    change f.val (g⁻¹ • Function.update x v a) =
      (sLocalCoordinateSection F S v f (g⁻¹ • x)).val (r⁻¹ • a)
    rw [hup, sLocalCoordinateSection_apply]
  rw [sLocalCoordinateMap_apply, hSection, hL]
  change (L (sLocalCoordinateSection F S v f (g⁻¹ • x))).val (r⁻¹ • x v) =
    (sLocalCoordinateMap F S v L f).val (g⁻¹ • x)
  rw [sLocalCoordinateMap_apply]
  rfl

theorem sLocalCoordinateMap_piProduct (S : Finset (Place F)) (v : S) (L : Local F v.val →ₗ[ℂ] Local F v.val)
    (g : ∀ w : S, Local F w.val) :
    sLocalCoordinateMap F S v L (locallyConstantTestPiProduct g) =
      locallyConstantTestPiProduct (Function.update g v (L (g v))) := by
  apply Subtype.ext
  funext x
  let I := (Finset.univ : Finset S).erase v
  let a : ℂ := ∏ w ∈ I, (g w).val (x w)
  have hSplit (b : v.val.adicCompletion F) :
      (locallyConstantTestPiProduct g).val (Function.update x v b) = a * (g v).val b := by
    change (∏ w, (g w).val (Function.update x v b w)) = a * (g v).val b
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ v), Function.update_self]
    congr 1
    apply Finset.prod_congr rfl
    intro w hw
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hw)]
  have he : ∀ b, (sLocalCoordinateSection F S v (locallyConstantTestPiProduct g) x).val b =
      (a • g v).val b := by
    intro b
    rw [sLocalCoordinateSection_apply, hSplit]
    rfl
  rw [sLocalCoordinateMap_apply, Subtype.ext (funext he), map_smul]
  change a * (L (g v)).val (x v) = ∏ w, (Function.update g v (L (g v)) w).val (x w)
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ v), Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro w hw
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hw)]

private theorem sLocalCoordinateMap_leftInverse (S : Finset (Place F)) (v : S)
    (L M : Local F v →ₗ[ℂ] Local F v) (h : LeftInverse M L) :
    LeftInverse (sLocalCoordinateMap F S v M) (sLocalCoordinateMap F S v L) := by
  intro f
  apply Subtype.ext
  funext x
  let e := sLocalFiniteCoordinateSplit F S v
  let g := locallyConstantTestCongr e f
  change (locallyConstantTestMapFirst M
    (locallyConstantTestCongr e ((locallyConstantTestCongr e).symm
      (locallyConstantTestMapFirst L g)))).val (e x) = _
  rw [LinearEquiv.apply_symm_apply]
  have he : ∀ k : locallyConstantTests
      (v.val.adicCompletion F × ((w : {w : S // w ≠ v}) → w.val.val.adicCompletion F)),
      k.val (e x) = (locallyConstantTestSection k (e x).2).val (e x).1 := fun _ => rfl
  rw [he, locallyConstantTestMapFirst_section, locallyConstantTestMapFirst_section, h]
  change f.val (e.symm (e x)) = _
  rw [Homeomorph.symm_apply_apply]

private abbrev OtherCoordinate (S : Finset (Place F)) (v : S) :=
  (t : {t : S // t ≠ v}) → t.val.val.adicCompletion F

def sLocalCoordinatePure (S : Finset (Place F)) (v : S)
    (f : Local F v) (g : locallyConstantTests (OtherCoordinate F S v)) : Test F S :=
  (locallyConstantTestCongr (sLocalFiniteCoordinateSplit F S v)).symm (locallyConstantTestProduct f g)

theorem sLocalCoordinateMap_pure_self (S : Finset (Place F)) (v : S)
    (L : Local F v →ₗ[ℂ] Local F v) (f : Local F v)
    (g : locallyConstantTests (OtherCoordinate F S v)) :
    sLocalCoordinateMap F S v L (sLocalCoordinatePure F S v f g) = sLocalCoordinatePure F S v (L f) g := by
  unfold sLocalCoordinateMap sLocalCoordinatePure
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,
    locallyConstantTestMapFirst_product]

private theorem sLocalCoordinateMap_pure_other (S : Finset (Place F)) (v w : S) (hvw : v ≠ w)
    (M : Local F w →ₗ[ℂ] Local F w) (g : locallyConstantTests (OtherCoordinate F S v)) :
    ∃ g' : locallyConstantTests (OtherCoordinate F S v), ∀ f : Local F v,
      sLocalCoordinateMap F S w M (sLocalCoordinatePure F S v f g) = sLocalCoordinatePure F S v f g' := by
  let K := v.val.adicCompletion F
  let O : Set K := v.val.adicCompletionIntegers F
  let χ := compactOpenIndicator K ⟨O, finitePlaceIntegral_compact F v.val,
    Valued.isOpen_valuationSubring K⟩
  have hχ : χ.val 0 = 1 := by
    change O.indicator (fun _ => (1 : ℂ)) 0 = 1
    exact Set.indicator_of_mem (show (0 : K) ∈ O from zero_mem _) _
  let e := sLocalFiniteCoordinateSplit F S v
  let A := sLocalCoordinateMap F S w M (sLocalCoordinatePure F S v χ g)
  let g' := locallyConstantTestSection
    (locallyConstantTestCongr (e.trans (Homeomorph.prodComm K (OtherCoordinate F S v))) A) 0
  refine ⟨g', fun f => ?_⟩
  apply Subtype.ext
  funext x
  let x₀ := Function.update x v (0 : K)
  have hx (a : w.val.adicCompletion F) :
      (e (Function.update x w a)).2 = (e (Function.update x₀ w a)).2 := by
    funext t
    change Function.update x w a t.val = Function.update (Function.update x v (0 : K)) w a t.val
    by_cases ht : t.val = w
    · rw [ht, Function.update_self, Function.update_self]
    · rw [Function.update_of_ne ht, Function.update_of_ne ht, Function.update_of_ne t.property]
  have hs : sLocalCoordinateSection F S w (sLocalCoordinatePure F S v f g) x =
      f.val (x v) • sLocalCoordinateSection F S w (sLocalCoordinatePure F S v χ g) x₀ := by
    apply Subtype.ext
    funext a
    change (sLocalCoordinateSection F S w (sLocalCoordinatePure F S v f g) x).val a =
      f.val (x v) * (sLocalCoordinateSection F S w (sLocalCoordinatePure F S v χ g) x₀).val a
    rw [sLocalCoordinateSection_apply, sLocalCoordinateSection_apply]
    change f.val (Function.update x w a v) * g.val (e (Function.update x w a)).2 =
      f.val (x v) * (χ.val (Function.update x₀ w a v) * g.val (e (Function.update x₀ w a)).2)
    rw [Function.update_of_ne hvw, Function.update_of_ne hvw,
      show x₀ v = 0 from Function.update_self v 0 x, hχ, one_mul, hx]
  rw [sLocalCoordinateMap_apply, hs, map_smul]
  change f.val (x v) * (M (sLocalCoordinateSection F S w (sLocalCoordinatePure F S v χ g) x₀)).val (x w) =
    f.val (x v) * A.val (e.symm (0, (e x).2))
  rw [sLocalFiniteCoordinateSplit_symm_same, show x₀ = Function.update x v (0 : K) from rfl]
  change _ = f.val (x v) *
    (sLocalCoordinateMap F S w M (sLocalCoordinatePure F S v χ g)).val x₀
  rw [sLocalCoordinateMap_apply, show x₀ w = x w from Function.update_of_ne hvw.symm _ _]

/-- Operators in distinct finite coordinates commute on the actual finite test space. -/
theorem sLocalCoordinateMap_commute (S : Finset (Place F)) (v w : S) (hvw : v ≠ w)
    (L : Local F v →ₗ[ℂ] Local F v) (M : Local F w →ₗ[ℂ] Local F w)
    (f : Test F S) :
    sLocalCoordinateMap F S v L (sLocalCoordinateMap F S w M f) =
      sLocalCoordinateMap F S w M (sLocalCoordinateMap F S v L f) := by
  let e := locallyConstantTestCongr (sLocalFiniteCoordinateSplit F S v)
  let E := locallyConstantTestProductEquiv (X := v.val.adicCompletion F)
    (Y := OtherCoordinate F S v)
  obtain ⟨t, rfl⟩ := (E.trans e.symm).surjective f
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    obtain ⟨b', hb⟩ := sLocalCoordinateMap_pure_other F S v w hvw M b
    have he : (E.trans e.symm) (a ⊗ₜ[ℂ] b) = sLocalCoordinatePure F S v a b :=
      congrArg e.symm (locallyConstantTestProductEquiv_tmul a b)
    rw [he, hb a, sLocalCoordinateMap_pure_self, sLocalCoordinateMap_pure_self, hb (L a)]
  | add a b ha hb => simp only [map_add, ha, hb]

/-- Lift an endomorphism of the finite test factor to the actual S-local
Schwartz–Bruhat space with its slice topology. -/
def sLocalBruhatFiniteMap (S : Finset (Place F)) (L : Test F S →ₗ[ℂ] Test F S) :
    sLocalBruhatImage F S →L[ℂ] sLocalBruhatImage F S := by
  letI : TopologicalSpace (Test F S) := finestLocallyConvexTopology _
  letI : TopologicalSpace (Arch F ⊗[ℂ] Test F S) := inductiveTensorTopology _ _
  let e := (sLocalBruhatTensorEquiv F S).toLinearEquiv
  let T := e.toLinearMap.comp ((TensorProduct.map LinearMap.id L).comp e.symm.toLinearMap)
  refine ⟨T, ?_⟩
  apply continuous_sLocal_of_pure F S
    (PolynormableSpace.withSeminorms ℂ (sLocalBruhatImage F S)) T
  intro ψ
  have hp (φ : Arch F) : e (φ ⊗ₜ[ℂ] ψ) = sLocalBruhatPure F S φ ψ :=
    TensorProduct.lift.tmul _ _
  have he (φ : Arch F) :
      T (sLocalBruhatPure F S φ ψ) = sLocalBruhatPure F S φ (L ψ) := by
    change e ((TensorProduct.map LinearMap.id L) (e.symm (sLocalBruhatPure F S φ ψ))) = _
    rw [← hp, e.symm_apply_apply, TensorProduct.map_tmul, LinearMap.id_apply]
    exact TensorProduct.lift.tmul _ _
  change Continuous (fun φ : Arch F => T (sLocalBruhatPure F S φ ψ))
  simp_rw [he]
  have hslice : Continuous (fun φ : Arch F => φ ⊗ₜ[ℂ] L ψ) :=
    ((inductiveTensor_withSeminorms (E := Arch F) (F := Test F S)).continuous_iff_continuous_comp
      ((TensorProduct.mk ℂ (Arch F) (Test F S)).flip (L ψ))).mpr (fun i => i.first (L ψ))
  exact (sLocalBruhatPure_lift_continuous F S).comp hslice

@[simp] theorem sLocalBruhatFiniteMap_pure (S : Finset (Place F)) (L : Test F S →ₗ[ℂ] Test F S)
    (φ : Arch F) (ψ : Test F S) :
    sLocalBruhatFiniteMap F S L (sLocalBruhatPure F S φ ψ) =
      sLocalBruhatPure F S φ (L ψ) := by
  letI : TopologicalSpace (Test F S) := finestLocallyConvexTopology _
  letI : TopologicalSpace (Arch F ⊗[ℂ] Test F S) := inductiveTensorTopology _ _
  let e := (sLocalBruhatTensorEquiv F S).toLinearEquiv
  have hψ : e.symm (sLocalBruhatPure F S φ ψ) = φ ⊗ₜ[ℂ] ψ := by
    apply e.injective
    rw [e.apply_symm_apply]
    exact (TensorProduct.lift.tmul _ _).symm
  change e ((TensorProduct.map LinearMap.id L) (e.symm (sLocalBruhatPure F S φ ψ))) = _
  rw [hψ, TensorProduct.map_tmul, LinearMap.id_apply]
  exact TensorProduct.lift.tmul _ _

private theorem sLocalBruhatFiniteMap_leftInverse (S : Finset (Place F)) (L M : Test F S →ₗ[ℂ] Test F S)
    (h : LeftInverse M L) :
    LeftInverse (sLocalBruhatFiniteMap F S M) (sLocalBruhatFiniteMap F S L) := by
  intro f
  letI : TopologicalSpace (Test F S) := finestLocallyConvexTopology _
  letI : TopologicalSpace (Arch F ⊗[ℂ] Test F S) := inductiveTensorTopology _ _
  let e := (sLocalBruhatTensorEquiv F S)
  obtain ⟨t, rfl⟩ := e.surjective f
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul φ ψ =>
    change sLocalBruhatFiniteMap F S M (sLocalBruhatFiniteMap F S L
      (sLocalBruhatPure F S φ ψ)) = _
    rw [sLocalBruhatFiniteMap_pure, sLocalBruhatFiniteMap_pure, h]
    rfl
  | add a b ha hb => simp only [map_add, ha, hb]

private theorem sLocalCoordinateMap_extend {S T : Finset (Place F)} (hST : S ⊆ T)
    (v : S) (L : Local F v →ₗ[ℂ] Local F v) (f : Test F S) :
    sLocalCoordinateMap F T ⟨v.val, hST v.property⟩ L (sLocalFiniteExtend F S T f) =
      sLocalFiniteExtend F S T (sLocalCoordinateMap F S v L f) := by
  apply Subtype.ext
  funext x
  let vT : T := ⟨v.val, hST v.property⟩
  let y : Coord F S := fun w => x ⟨w.val, hST w.property⟩
  let P (x : Coord F T) := ∀ w : T, w.val ∉ S → x w ∈ w.val.adicCompletionIntegers F
  let c : ℂ := if P x then 1 else 0
  have hs : sLocalCoordinateSection F T vT (sLocalFiniteExtend F S T f) x =
      c • sLocalCoordinateSection F S v f y := by
    apply Subtype.ext
    funext a
    have hupdate :
        (fun w : S => Function.update x vT a (⟨w.val, hST w.property⟩ : T)) =
          Function.update y v a := by
      funext w
      by_cases hw : w = v
      · subst w
        rw [Function.update_self]
        exact (Function.update_self v a y).symm
      · have hn : (⟨w.val, hST w.property⟩ : T) ≠ vT :=
          fun he => hw (Subtype.ext (congrArg (fun z : T => z.val) he))
        rw [Function.update_of_ne hn, Function.update_of_ne hw]
    have htail : P (Function.update x vT a) ↔ P x := by
      have he (w : T) (hw : w.val ∉ S) : Function.update x vT a w = x w :=
        Function.update_of_ne (show w ≠ vT from fun hwv => hw (by
          rw [congrArg (fun z : T => z.val) hwv]
          exact v.property)) a x
      constructor <;> intro h w hw
      · rw [← he w hw]
        exact h w hw
      · rw [he w hw]
        exact h w hw
    change (sLocalCoordinateSection F T vT (sLocalFiniteExtend F S T f) x).val a =
      c * (sLocalCoordinateSection F S v f y).val a
    rw [sLocalCoordinateSection_apply, sLocalFiniteExtend_apply F hST,
      sLocalCoordinateSection_apply, hupdate]
    change f.val (Function.update y v a) * (if P (Function.update x vT a) then 1 else 0) =
      c * f.val (Function.update y v a)
    by_cases hp : P x
    · simp only [c, ite_eq_left hp, ite_eq_left (htail.mpr hp), mul_one, one_mul]
    · simp only [c, ite_eq_right hp, ite_eq_right (fun h => hp (htail.mp h)), mul_zero, zero_mul]
  change (sLocalCoordinateMap F T vT L (sLocalFiniteExtend F S T f)).val x = _
  rw [sLocalCoordinateMap_apply, hs, map_smul, sLocalFiniteExtend_apply F hST]
  change c * (L (sLocalCoordinateSection F S v f y)).val (x vT) =
    (sLocalCoordinateMap F S v L f).val y * c
  rw [sLocalCoordinateMap_apply]
  exact mul_comm _ _

theorem sLocalBruhatCoordinateMap_transition {S T : Finset (Place F)} (hST : S ⊆ T)
    (v : S) (L : Local F v →ₗ[ℂ] Local F v) (f : sLocalBruhatImage F S) :
    sLocalBruhatFiniteMap F T (sLocalCoordinateMap F T ⟨v.val, hST v.property⟩ L)
        (sLocalBruhatTransition F hST f) =
      sLocalBruhatTransition F hST
        (sLocalBruhatFiniteMap F S (sLocalCoordinateMap F S v L) f) := by
  letI : TopologicalSpace (Test F S) := finestLocallyConvexTopology _
  letI : TopologicalSpace (Arch F ⊗[ℂ] Test F S) := inductiveTensorTopology _ _
  let e := (sLocalBruhatTensorEquiv F S)
  obtain ⟨t, rfl⟩ := e.surjective f
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul φ ψ =>
    change sLocalBruhatFiniteMap F T _ (sLocalBruhatTransition F hST
      (sLocalBruhatPure F S φ ψ)) = sLocalBruhatTransition F hST
      (sLocalBruhatFiniteMap F S _ (sLocalBruhatPure F S φ ψ))
    rw [sLocalBruhatTransition_pure F hST, sLocalBruhatFiniteMap_pure, sLocalBruhatFiniteMap_pure,
      sLocalBruhatTransition_pure F hST, sLocalCoordinateMap_extend F hST]
  | add a b ha hb => simp only [map_add, ha, hb]

/-- The canonical single-place operator on S-local Schwartz–Bruhat tests. -/
def sLocalWeilPrincipalValue (S : Finset (Place F)) (v : S) :
    sLocalBruhatImage F S →L[ℂ] sLocalBruhatImage F S :=
  sLocalBruhatFiniteMap F S (sLocalCoordinateMap F S v (weilPrincipalValue F v))

/-- Before passage to theta coinvariants the S-local operator is a split
topological embedding, with closed range. -/
theorem sLocalWeilPrincipalValue_split (S : Finset (Place F)) (v : S) :
    ∃ R : sLocalBruhatImage F S →L[ℂ] sLocalBruhatImage F S,
      LeftInverse R (sLocalWeilPrincipalValue F S v) := by
  let P := weilPrincipalValue F v
  have hP : Injective P := by
    letI : TopologicalSpace (Local F v.val) := finestLocallyConvexTopology _
    exact (weilPrincipalValue_embedding F v).2.1.injective
  obtain ⟨Q, hQ⟩ := P.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hP)
  have h : LeftInverse Q P := fun f => DFunLike.congr_fun hQ f
  exact ⟨sLocalBruhatFiniteMap F S (sLocalCoordinateMap F S v Q),
    sLocalBruhatFiniteMap_leftInverse F S _ _ (sLocalCoordinateMap_leftInverse F S v P Q h)⟩

theorem sLocalWeilPrincipalValue_closedEmbedding (S : Finset (Place F)) (v : S) :
    IsClosedEmbedding (sLocalWeilPrincipalValue F S v) := by
  obtain ⟨R, hR⟩ := sLocalWeilPrincipalValue_split F S v
  exact hR.isClosedEmbedding R.continuous (sLocalWeilPrincipalValue F S v).continuous

private def stageCoordinateMap (v : Place F) (L : Local F v →ₗ[ℂ] Local F v)
    (S : Finset (Place F)) (h : v ∈ S) :
    sLocalBruhatImage F S →L[ℂ] sLocalBruhatImage F S :=
  sLocalBruhatFiniteMap F S (sLocalCoordinateMap F S ⟨v, h⟩ L)

private theorem exists_stage_containing (v : Place F) (f : GlobalBruhat F) :
    ∃ S : Finset (Place F), v ∈ S ∧ f ∈ sLocalBruhatImage F S := by
  obtain ⟨S, hS⟩ := sLocalBruhat_bounded_subset F {f} (Bornology.isVonNBounded_singleton f)
  exact ⟨insert v S, Finset.mem_insert_self v S,
    sLocalBruhatImage_mono F (Finset.subset_insert v S) (hS (mem_singleton f))⟩

private def globalCoordinateMapAux (v : Place F) (L : Local F v →ₗ[ℂ] Local F v)
    (f : GlobalBruhat F) : GlobalBruhat F :=
  let h := exists_stage_containing F v f
  (stageCoordinateMap F v L h.choose h.choose_spec.1 ⟨f, h.choose_spec.2⟩).val

private theorem globalCoordinateMapAux_stage (v : Place F) (L : Local F v →ₗ[ℂ] Local F v)
    (S : Finset (Place F)) (h : v ∈ S) (f : sLocalBruhatImage F S) :
    globalCoordinateMapAux F v L f.val = (stageCoordinateMap F v L S h f).val := by
  let h₀ := exists_stage_containing F v f.val
  let S₀ := h₀.choose
  let f₀ : sLocalBruhatImage F S₀ := ⟨f.val, h₀.choose_spec.2⟩
  let T := S₀ ∪ S
  let h₁ : S₀ ⊆ T := Finset.subset_union_left
  let h₂ : S ⊆ T := Finset.subset_union_right
  have hEq : sLocalBruhatTransition F h₁ f₀ = sLocalBruhatTransition F h₂ f := Subtype.ext rfl
  have ha := sLocalBruhatCoordinateMap_transition F h₁ ⟨v, h₀.choose_spec.1⟩ L f₀
  have hb := sLocalBruhatCoordinateMap_transition F h₂ ⟨v, h⟩ L f
  have hh := congrArg (fun z : sLocalBruhatImage F T =>
    (stageCoordinateMap F v L T (h₂ h) z).val) hEq
  exact (congrArg Subtype.val ha).symm.trans (hh.trans (congrArg Subtype.val hb))

/-- Glue the single-coordinate operator on the actual global test space.
The gluing uses agreement on every larger stage containing the selected place. -/
def globalBruhatCoordinateMap (v : Place F) (L : Local F v →ₗ[ℂ] Local F v) :
    GlobalBruhat F →L[ℂ] GlobalBruhat F := by
  let A := globalCoordinateMapAux F v L
  let M : GlobalBruhat F →ₗ[ℂ] GlobalBruhat F :=
    { toFun := A
      map_add' := fun f g => by
        obtain ⟨S, hvS, hf⟩ := exists_stage_containing F v f
        obtain ⟨T, hvT, hg⟩ := exists_stage_containing F v g
        let h : v ∈ S ∪ T := Finset.subset_union_left hvS
        let f' : sLocalBruhatImage F (S ∪ T) :=
          ⟨f, sLocalBruhatImage_mono F Finset.subset_union_left hf⟩
        let g' : sLocalBruhatImage F (S ∪ T) :=
          ⟨g, sLocalBruhatImage_mono F Finset.subset_union_right hg⟩
        change A (f' + g').val = A f'.val + A g'.val
        dsimp only [A]
        rw [globalCoordinateMapAux_stage F v L _ h (f' + g'),
          globalCoordinateMapAux_stage F v L _ h f',
          globalCoordinateMapAux_stage F v L _ h g', map_add]
        rfl
      map_smul' := fun c f => by
        obtain ⟨S, h, hf⟩ := exists_stage_containing F v f
        let f' : sLocalBruhatImage F S := ⟨f, hf⟩
        change A (c • f').val = c • A f'.val
        dsimp only [A]
        rw [globalCoordinateMapAux_stage F v L _ h (c • f'),
          globalCoordinateMapAux_stage F v L _ h f', map_smul]
        rfl }
  refine ⟨M, GlobalBruhat.continuous_of_pure F
    (PolynormableSpace.withSeminorms ℂ (GlobalBruhat F)) M ?_⟩
  intro ψ
  obtain ⟨S, hS⟩ := sLocalBruhatProjection_pure_eventually F ψ
  let T := insert v S
  let h : v ∈ T := Finset.mem_insert_self _ _
  let f' (φ : Arch F) : sLocalBruhatImage F T :=
    sLocalBruhatCorestrict F T (GlobalBruhat.pure F ψ φ)
  have he (φ : Arch F) : (f' φ).val = GlobalBruhat.pure F ψ φ :=
    hS T (Finset.subset_insert _ _) φ
  have hA : (fun φ : Arch F => M (GlobalBruhat.pure F ψ φ)) =
      fun φ => (stageCoordinateMap F v L T h (f' φ)).val := by
    funext φ
    change A _ = _
    rw [← he]
    exact globalCoordinateMapAux_stage F v L T h (f' φ)
  rw [hA]
  exact continuous_subtype_val.comp ((stageCoordinateMap F v L T h).continuous.comp
    ((sLocalBruhatCorestrict F T).continuous.comp (GlobalBruhat.pure_continuous F ψ)))

theorem globalBruhatCoordinateMap_stage (v : Place F) (L : Local F v →ₗ[ℂ] Local F v)
    (S : Finset (Place F)) (h : v ∈ S) (f : sLocalBruhatImage F S) :
    globalBruhatCoordinateMap F v L f.val = (stageCoordinateMap F v L S h f).val :=
  globalCoordinateMapAux_stage F v L S h f

private theorem globalBruhatCoordinateMap_leftInverse (v : Place F)
    (L R : Local F v →ₗ[ℂ] Local F v) (h : LeftInverse R L) :
    LeftInverse (globalBruhatCoordinateMap F v R) (globalBruhatCoordinateMap F v L) := by
  intro f
  obtain ⟨S, hv, hf⟩ := exists_stage_containing F v f
  let f' : sLocalBruhatImage F S := ⟨f, hf⟩
  have h' : LeftInverse (stageCoordinateMap F v R S hv) (stageCoordinateMap F v L S hv) :=
    sLocalBruhatFiniteMap_leftInverse F S _ _
      (sLocalCoordinateMap_leftInverse F S ⟨v,hv⟩ L R h)
  change globalBruhatCoordinateMap F v R (globalBruhatCoordinateMap F v L f'.val) = f'.val
  rw [globalBruhatCoordinateMap_stage F v L S hv f',
    globalBruhatCoordinateMap_stage F v R S hv, h' f']

/-- The global single-place principal-value operator before theta descent. -/
def globalWeilPrincipalValue (v : Place F) : GlobalBruhat F →L[ℂ] GlobalBruhat F :=
  globalBruhatCoordinateMap F v (weilPrincipalValue F v)

theorem globalWeilPrincipalValue_stage (S : Finset (Place F)) (v : S)
    (f : sLocalBruhatImage F S) :
    globalWeilPrincipalValue F v f.val = (sLocalWeilPrincipalValue F S v f).val :=
  globalBruhatCoordinateMap_stage F v (weilPrincipalValue F v) S v.property f

theorem globalWeilPrincipalValue_closedEmbedding (v : Place F) :
    IsClosedEmbedding (globalWeilPrincipalValue F v) := by
  let P := weilPrincipalValue F v
  have hP : Injective P := by
    letI : TopologicalSpace (Local F v) := finestLocallyConvexTopology _
    exact (weilPrincipalValue_embedding F v).2.1.injective
  obtain ⟨Q, hQ⟩ := P.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hP)
  have h : LeftInverse Q P := fun f => DFunLike.congr_fun hQ f
  exact (globalBruhatCoordinateMap_leftInverse F v P Q h).isClosedEmbedding
    (globalBruhatCoordinateMap F v Q).continuous (globalWeilPrincipalValue F v).continuous


theorem sLocalWeilPrincipalValue_commute (S : Finset (Place F)) (v w : S) :
    Commute (sLocalWeilPrincipalValue F S v) (sLocalWeilPrincipalValue F S w) := by
  by_cases hvw : v = w
  · subst w
    exact Commute.refl _
  · apply ContinuousLinearMap.ext
    intro f
    letI : TopologicalSpace (Test F S) := finestLocallyConvexTopology _
    letI : TopologicalSpace (Arch F ⊗[ℂ] Test F S) := inductiveTensorTopology _ _
    let e := sLocalBruhatTensorEquiv F S
    obtain ⟨t, rfl⟩ := e.surjective f
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul φ ψ =>
      change sLocalBruhatFiniteMap F S _ (sLocalBruhatFiniteMap F S _
        (sLocalBruhatPure F S φ ψ)) =
        sLocalBruhatFiniteMap F S _ (sLocalBruhatFiniteMap F S _
          (sLocalBruhatPure F S φ ψ))
      simp only [sLocalBruhatFiniteMap_pure]
      rw [sLocalCoordinateMap_commute F S v w hvw]
    | add a b ha hb => simp only [map_add, ha, hb]

theorem globalWeilPrincipalValue_commute (v w : Place F) :
    Commute (globalWeilPrincipalValue F v) (globalWeilPrincipalValue F w) := by
  apply ContinuousLinearMap.ext
  intro f
  obtain ⟨T, hv, hf⟩ := exists_stage_containing F v f
  let S := insert w T
  let v' : S := ⟨v, Finset.mem_insert_of_mem hv⟩
  let w' : S := ⟨w, Finset.mem_insert_self _ _⟩
  let g : sLocalBruhatImage F S := ⟨f, sLocalBruhatImage_mono F (Finset.subset_insert _ _) hf⟩
  change globalWeilPrincipalValue F v' (globalWeilPrincipalValue F w' g.val) =
    globalWeilPrincipalValue F w' (globalWeilPrincipalValue F v' g.val)
  rw [globalWeilPrincipalValue_stage F S w' g, globalWeilPrincipalValue_stage F S v' g,
    globalWeilPrincipalValue_stage, globalWeilPrincipalValue_stage]
  exact congrArg Subtype.val (DFunLike.congr_fun (sLocalWeilPrincipalValue_commute F S v' w').eq g)

/-- The order-independent principal-value operator for a finite subset of an S-local stage. -/
def sLocalWeilPrincipalValues (S : Finset (Place F)) (s : Finset S) :
    sLocalBruhatImage F S →L[ℂ] sLocalBruhatImage F S :=
  s.noncommProd (sLocalWeilPrincipalValue F S)
    (fun v _ w _ _ => sLocalWeilPrincipalValue_commute F S v w)

/-- The order-independent principal-value operator for a finite set of global places. -/
def globalWeilPrincipalValues (s : Finset (Place F)) : GlobalBruhat F →L[ℂ] GlobalBruhat F :=
  s.noncommProd (globalWeilPrincipalValue F)
    (fun v _ w _ _ => globalWeilPrincipalValue_commute F v w)

theorem sLocalWeilPrincipalValues_closedEmbedding (S : Finset (Place F)) (s : Finset S) :
    IsClosedEmbedding (sLocalWeilPrincipalValues F S s) := by
  unfold sLocalWeilPrincipalValues
  refine Finset.noncommProd_induction s (sLocalWeilPrincipalValue F S) _
    (fun L : sLocalBruhatImage F S →L[ℂ] sLocalBruhatImage F S => IsClosedEmbedding L) ?_ ?_ ?_
  · exact fun _ _ ha hb => ha.comp hb
  · exact IsClosedEmbedding.id
  · exact fun v _ => sLocalWeilPrincipalValue_closedEmbedding F S v

theorem globalWeilPrincipalValues_closedEmbedding (s : Finset (Place F)) :
    IsClosedEmbedding (globalWeilPrincipalValues F s) := by
  unfold globalWeilPrincipalValues
  refine Finset.noncommProd_induction s (globalWeilPrincipalValue F) _
    (fun L : GlobalBruhat F →L[ℂ] GlobalBruhat F => IsClosedEmbedding L) ?_ ?_ ?_
  · exact fun _ _ ha hb => ha.comp hb
  · exact IsClosedEmbedding.id
  · exact fun v _ => globalWeilPrincipalValue_closedEmbedding F v

/-- The global finite-place operator restricts to the corresponding S-local
operator when the stage contains the selected places. -/
theorem globalWeilPrincipalValues_stage (S : Finset (Place F)) (s : Finset S)
    (f : sLocalBruhatImage F S) :
    globalWeilPrincipalValues F (s.map ⟨Subtype.val, Subtype.val_injective⟩) f.val =
      (sLocalWeilPrincipalValues F S s f).val := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have hx : sLocalWeilPrincipalValues F S ∅ = 1 := Finset.noncommProd_empty _ _
    have hy : globalWeilPrincipalValues F ∅ = 1 := Finset.noncommProd_empty _ _
    rw [Finset.map_empty, hx, hy]
    rfl
  | insert v s hv ih =>
    have h : v.val ∉ s.map (⟨Subtype.val, Subtype.val_injective⟩ : S ↪ Place F) := by
      intro hn
      obtain ⟨w, hw, hEq⟩ := Finset.mem_map.mp hn
      exact hv (Subtype.ext hEq ▸ hw)
    have hx : sLocalWeilPrincipalValues F S (insert v s) =
        sLocalWeilPrincipalValue F S v * sLocalWeilPrincipalValues F S s :=
      Finset.noncommProd_insert_of_notMem s v _ _ hv
    have hy : globalWeilPrincipalValues F
        (insert v.val (s.map ⟨Subtype.val, Subtype.val_injective⟩)) =
      globalWeilPrincipalValue F v.val *
        globalWeilPrincipalValues F (s.map ⟨Subtype.val, Subtype.val_injective⟩) :=
      Finset.noncommProd_insert_of_notMem _ _ _ _ h
    rw [Finset.map_insert]
    change globalWeilPrincipalValues F
        (insert v.val (s.map ⟨Subtype.val, Subtype.val_injective⟩)) f.val = _
    rw [hx, hy]
    change globalWeilPrincipalValue F v.val
      (globalWeilPrincipalValues F (s.map ⟨Subtype.val, Subtype.val_injective⟩) f.val) =
      (sLocalWeilPrincipalValue F S v (sLocalWeilPrincipalValues F S s f)).val
    rw [ih, globalWeilPrincipalValue_stage F S v]


/-- Enlarging the S-local stage commutes with the product for the same selected
finite places. -/
theorem sLocalWeilPrincipalValues_transition {S T : Finset (Place F)} (hST : S ⊆ T)
    (s : Finset S) (f : sLocalBruhatImage F S) :
    let e : S ↪ T := ⟨fun v => ⟨v.val, hST v.property⟩, fun _ _ h => Subtype.ext
      (congrArg (fun w : T => w.val) h)⟩
    sLocalWeilPrincipalValues F T (s.map e) (sLocalBruhatTransition F hST f) =
      sLocalBruhatTransition F hST (sLocalWeilPrincipalValues F S s f) := by
  dsimp only
  let e : S ↪ T := ⟨fun v => ⟨v.val, hST v.property⟩, fun _ _ h => Subtype.ext
    (congrArg (fun w : T => w.val) h)⟩
  let i : S ↪ Place F := ⟨Subtype.val, Subtype.val_injective⟩
  let j : T ↪ Place F := ⟨Subtype.val, Subtype.val_injective⟩
  have hs : (s.map e).map j = s.map i := by
    rw [Finset.map_map]
    rfl
  apply Subtype.ext
  change (sLocalWeilPrincipalValues F T (s.map e) (sLocalBruhatTransition F hST f)).val =
    (sLocalWeilPrincipalValues F S s f).val
  rw [← globalWeilPrincipalValues_stage F T (s.map e), ← globalWeilPrincipalValues_stage F S s]
  change globalWeilPrincipalValues F ((s.map e).map j) f.val =
    globalWeilPrincipalValues F (s.map i) f.val
  rw [hs]


end
end Masullo
