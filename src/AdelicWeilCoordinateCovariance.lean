import MixedArchWeilEigen
import GlobalHeckeTamagawaEigen
import SLocalThetaFourier
import SLocalFinitePlaceTranslation

open Function IsDedekindDomain NumberField Set
open scoped Classical NumberField SchwartzMap

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

private abbrev Place := HeightOneSpectrum (𝓞 F)
private abbrev R := {v : InfinitePlace F // v.IsReal}
private abbrev C := {v : InfinitePlace F // v.IsComplex}
private abbrev Stage (S : Finset (Place F)) := sLocalBruhatImage F S
private abbrev Test (S : Finset (Place F)) := locallyConstantTests (∀ v : S, v.val.adicCompletion F)
private abbrev ArchUnits := (InfiniteAdeleRing F)ˣ
private abbrev Characters := PontryaginDual (normOneIdeleClass F)

private theorem adelicWeil_stage_ext {S : Finset (Place F)} {f g : Stage F S}
    (h : ∀ x, sLocalBruhatRestriction F S f.val x = sLocalBruhatRestriction F S g.val x) : f = g := by
  apply Subtype.ext
  apply (GlobalBruhat.algebraicEquiv F).injective
  apply Subtype.ext
  funext x
  change GlobalBruhat.evaluation F x f.val = GlobalBruhat.evaluation F x g.val
  rw [sLocalBruhatRestriction_reconstruct, sLocalBruhatRestriction_reconstruct, h]

private def realArchUnit (v : R F) (u : ℝˣ) : ArchUnits F :=
  (infiniteAdeleUnitsCoordinates F).symm (Pi.mulSingle v u, 1)

private def complexArchUnit (v : C F) (u : ℂˣ) : ArchUnits F :=
  (infiniteAdeleUnitsCoordinates F).symm (1, Pi.mulSingle v u)

omit [NumberField F] in
private theorem realArchUnit_inverse_coordinates (v : R F) (u : ℝˣ) :
    infiniteAdeleUnitsCoordinates F (realArchUnit F v u)⁻¹ = (Pi.mulSingle v u⁻¹, 1) := by
  unfold realArchUnit
  rw [map_inv, ContinuousMulEquiv.apply_symm_apply, Prod.inv_mk, inv_one, Pi.mulSingle_inv]

omit [NumberField F] in
private theorem complexArchUnit_inverse_coordinates (v : C F) (u : ℂˣ) :
    infiniteAdeleUnitsCoordinates F (complexArchUnit F v u)⁻¹ = (1, Pi.mulSingle v u⁻¹) := by
  unfold complexArchUnit
  rw [map_inv, ContinuousMulEquiv.apply_symm_apply, Prod.inv_mk, inv_one, Pi.mulSingle_inv]

private theorem stageWeil_archTranslate_real (S : Finset (Place F)) (ψ : Test F S)
    (v : R F) (u : ℝˣ) (f : R F → 𝓢(ℝ, ℂ)) (g : C F → 𝓢(ℂ, ℂ)) :
    sLocalBruhatLeftTranslate F S (sLocalArchZetaInsert F S (realArchUnit F v u))
      (sLocalBruhatPure F S (mixedWeilTest F f g) ψ) =
    sLocalBruhatPure F S (mixedWeilTest F (update f v (archSchwartzDilation u (f v))) g) ψ := by
  apply adelicWeil_stage_ext F
  intro x
  rw [sLocalBruhatLeftTranslate_restrict, sLocalBruhatPure_restrict, sLocalBruhatPure_restrict]
  let a := realArchUnit F v u
  change mixedWeilTest F f g (InfiniteAdeleRing.ringEquiv_mixedSpace F ((a⁻¹).val * x.1)) *
      ψ.val ((1 : ∀ v : S, v.val.adicCompletion F) * x.2) = _
  rw [one_mul, map_mul, mixedWeilTest_apply, mixedWeilTest_apply]
  have hc := realArchUnit_inverse_coordinates F v u
  have hr (w : R F) :
      (InfiniteAdeleRing.ringEquiv_mixedSpace F (a⁻¹).val).1 w = ((Pi.mulSingle v u⁻¹ : R F → ℝˣ) w).val := by
    rw [← infiniteAdeleUnitsCoordinates_real_val, hc]
  have hi (w : C F) : (InfiniteAdeleRing.ringEquiv_mixedSpace F (a⁻¹).val).2 w = 1 := by
    rw [← infiniteAdeleUnitsCoordinates_complex_val, hc]
    rfl
  congr 2
  · apply Finset.prod_congr rfl
    intro w _
    change f w ((InfiniteAdeleRing.ringEquiv_mixedSpace F (a⁻¹).val).1 w *
      (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1).1 w) = _
    rw [hr]
    by_cases hw : w = v
    · subst w
      rw [Pi.mulSingle_eq_same, update_self, archSchwartzDilation_apply, mul_comm]
    · rw [Pi.mulSingle_eq_of_ne hw, Units.val_one, one_mul, update_of_ne hw]
  · apply Finset.prod_congr rfl
    intro w _
    change g w ((InfiniteAdeleRing.ringEquiv_mixedSpace F (a⁻¹).val).2 w *
      (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1).2 w) = _
    rw [hi, one_mul]

private theorem stageWeil_archTranslate_complex (S : Finset (Place F)) (ψ : Test F S)
    (v : C F) (u : ℂˣ) (f : R F → 𝓢(ℝ, ℂ)) (g : C F → 𝓢(ℂ, ℂ)) :
    sLocalBruhatLeftTranslate F S (sLocalArchZetaInsert F S (complexArchUnit F v u))
      (sLocalBruhatPure F S (mixedWeilTest F f g) ψ) =
    sLocalBruhatPure F S (mixedWeilTest F f (update g v (archSchwartzDilation u (g v)))) ψ := by
  apply adelicWeil_stage_ext F
  intro x
  rw [sLocalBruhatLeftTranslate_restrict, sLocalBruhatPure_restrict, sLocalBruhatPure_restrict]
  let a := complexArchUnit F v u
  change mixedWeilTest F f g (InfiniteAdeleRing.ringEquiv_mixedSpace F ((a⁻¹).val * x.1)) *
      ψ.val ((1 : ∀ v : S, v.val.adicCompletion F) * x.2) = _
  rw [one_mul, map_mul, mixedWeilTest_apply, mixedWeilTest_apply]
  have hc := complexArchUnit_inverse_coordinates F v u
  have hr (w : R F) : (InfiniteAdeleRing.ringEquiv_mixedSpace F (a⁻¹).val).1 w = 1 := by
    rw [← infiniteAdeleUnitsCoordinates_real_val, hc]
    rfl
  have hi (w : C F) :
      (InfiniteAdeleRing.ringEquiv_mixedSpace F (a⁻¹).val).2 w = ((Pi.mulSingle v u⁻¹ : C F → ℂˣ) w).val := by
    rw [← infiniteAdeleUnitsCoordinates_complex_val, hc]
  congr 2
  · apply Finset.prod_congr rfl
    intro w _
    change f w ((InfiniteAdeleRing.ringEquiv_mixedSpace F (a⁻¹).val).1 w *
      (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1).1 w) = _
    rw [hr, one_mul]
  · apply Finset.prod_congr rfl
    intro w _
    change g w ((InfiniteAdeleRing.ringEquiv_mixedSpace F (a⁻¹).val).2 w *
      (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1).2 w) = _
    rw [hi]
    by_cases hw : w = v
    · subst w
      rw [Pi.mulSingle_eq_same, update_self, archSchwartzDilation_apply, mul_comm]
    · rw [Pi.mulSingle_eq_of_ne hw, Units.val_one, one_mul, update_of_ne hw]

/-- The actual adelic weight on a norm-one character component. -/
def globalWeilWeight (ω : Characters F) (z : ℂ) (a : Idele F) : ℂ :=
  ideleNormTwist F (compactIdeleClassCharacter F ω) z (ideleClassMap F a)

def IsGlobalWeilEigen (ω : Characters F) (z : ℂ) (T : StrongDual ℂ (GlobalBruhat F)) : Prop :=
  ∀ a f, T (GlobalBruhat.leftTranslate F a f) = globalWeilWeight F ω z a * T f

private theorem globalWeilWeight_apply (ω : Characters F) (z : ℂ) (a : Idele F) :
    globalWeilWeight F ω z a =
      globalNormOneCharacter F ω (ideleClassMap F a) *
        Complex.exp (z * (Real.log (ideleNorm F a) : ℂ)) := by
  unfold globalWeilWeight ideleNormTwist ideleNormPower
  rw [← ideleClassNorm_mk]
  rfl

private theorem stageArchEmbed_eq (S : Finset (Place F)) (a : ArchUnits F) :
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

variable (S : Finset (Place F)) (ω : Characters F)
    (hs : Surjective (sIdeleClassInclusion F S))
    (hu : globalNormOneCharacter F ω ∈ (sUnramified F S : Set (QuasiCharacter (IdeleClass F))))

private abbrev τ := sLocalNormOneCharacterOfGlobal F ω S hs hu

private theorem globalWeilWeight_arch (z : ℂ) (a : ArchUnits F) :
    globalWeilWeight F ω z (sLocalEmbed F S (sLocalArchZetaInsert F S a)).val =
      sLocalZetaWeight F S (τ F S ω hs hu) z (QuotientGroup.mk (sLocalArchZetaInsert F S a)) := by
  rw [stageArchEmbed_eq, globalWeilWeight_apply, sLocalZetaWeight_global_arch_apply, mul_comm]
  have hnorm : Real.log (ideleNorm F (archIntoIdeles F a)) = Real.log ‖a.val‖ := by
    have h := archIntoIdeles_logNorm F a
    rw [infiniteIdeleLogNorm_eq] at h
    exact congrArg Multiplicative.toAdd h
  rw [hnorm]

section ArchWeights

variable (σ : PontryaginDual (SLocalThetaNormOne F S)) (z : ℂ)

private theorem stageWeilWeight_real (v : R F) (u : ℝˣ) :
    sLocalZetaWeight F S σ z (QuotientGroup.mk (sLocalArchZetaInsert F S (realArchUnit F v u))) =
      realArchUnitWeight (sLocalRealArchParameters F S σ v).2
        (z + (sLocalRealArchParameters F S σ v).1) u := by
  rw [sLocalArchZetaWeight_eq_product]
  unfold realArchUnit
  rw [ContinuousMulEquiv.apply_symm_apply]
  rw [show (∏ w : C F, sLocalComplexArchWeight F S σ w z ((1 : C F → ℂˣ) w)) = 1 by
    simp [sLocalComplexArchWeight], mul_one]
  rw [Finset.prod_eq_single v]
  · simp only [Pi.mulSingle_eq_same]
    rfl
  · intro w _ hw
    simp [Pi.mulSingle_eq_of_ne hw, sLocalRealArchWeight]
  · simp

private theorem stageWeilWeight_complex (v : C F) (u : ℂˣ) :
    sLocalZetaWeight F S σ z (QuotientGroup.mk (sLocalArchZetaInsert F S (complexArchUnit F v u))) =
      complexArchUnitWeight (sLocalComplexArchParameters F S σ v).2
        (z + (sLocalComplexArchParameters F S σ v).1) u := by
  rw [sLocalArchZetaWeight_eq_product]
  unfold complexArchUnit
  rw [ContinuousMulEquiv.apply_symm_apply]
  rw [show (∏ w : R F, sLocalRealArchWeight F S σ w z ((1 : R F → ℝˣ) w)) = 1 by
    simp [sLocalRealArchWeight], one_mul]
  rw [Finset.prod_eq_single v]
  · simp only [Pi.mulSingle_eq_same]
    rfl
  · intro w _ hw
    simp [Pi.mulSingle_eq_of_ne hw, sLocalComplexArchWeight]
  · simp

end ArchWeights

private theorem globalWeilWeight_real (z : ℂ) (v : R F) (u : ℝˣ) :
    globalWeilWeight F ω z
      (sLocalEmbed F S (sLocalArchZetaInsert F S (realArchUnit F v u))).val =
    realArchUnitWeight (sLocalRealArchParameters F S (τ F S ω hs hu) v).2
      (z + (sLocalRealArchParameters F S (τ F S ω hs hu) v).1) u := by
  exact (globalWeilWeight_arch F S ω hs hu z (realArchUnit F v u)).trans
    (stageWeilWeight_real F S (τ F S ω hs hu) z v u)

private theorem globalWeilWeight_complex (z : ℂ) (v : C F) (u : ℂˣ) :
    globalWeilWeight F ω z
      (sLocalEmbed F S (sLocalArchZetaInsert F S (complexArchUnit F v u))).val =
    complexArchUnitWeight (sLocalComplexArchParameters F S (τ F S ω hs hu) v).2
      (z + (sLocalComplexArchParameters F S (τ F S ω hs hu) v).1) u := by
  exact (globalWeilWeight_arch F S ω hs hu z (complexArchUnit F v u)).trans
    (stageWeilWeight_complex F S (τ F S ω hs hu) z v u)

private abbrev realParameters := sLocalRealArchParameters F S (τ F S ω hs hu)
private abbrev complexParameters := sLocalComplexArchParameters F S (τ F S ω hs hu)

private def stageWeilArchRestriction (T : StrongDual ℂ (GlobalBruhat F)) (ψ : Test F S) :
    StrongDual ℂ 𝓢(mixedEmbedding.mixedSpace F, ℂ) :=
  T.comp ⟨GlobalBruhat.pure F (insertFinite F S ψ), GlobalBruhat.pure_continuous F (insertFinite F S ψ)⟩

/-- On every finite test slice, the restriction of a global eigendistribution
has the exact real and complex local pairings for that stage. -/
theorem globalWeil_archRestriction_eval (z : ℂ)
    (T : StrongDual ℂ (GlobalBruhat F)) (hT : IsGlobalWeilEigen F ω z T)
    (ψ : Test F S) (f : R F → 𝓢(ℝ, ℂ)) (g : C F → 𝓢(ℂ, ℂ)) :
    T (sLocalBruhatPure F S (mixedWeilTest F f g) ψ).val =
      T (sLocalBruhatPure F S (mixedWeilTest F
        (mixedWeilRealReference F (realParameters F S ω hs hu))
        (mixedWeilComplexReference F (complexParameters F S ω hs hu))) ψ).val *
        sLocalNormalizedArchWeilTensor F S (τ F S ω hs hu) f g z := by
  let U := stageWeilArchRestriction F S T ψ
  have hReal (v : R F) (u : ℝˣ) (f : R F → 𝓢(ℝ, ℂ)) (g : C F → 𝓢(ℂ, ℂ)) :
      U (mixedWeilTest F (update f v (archSchwartzDilation u (f v))) g) =
        realArchUnitWeight (realParameters F S ω hs hu v).2 (z + (realParameters F S ω hs hu v).1) u *
          U (mixedWeilTest F f g) := by
    change T (sLocalBruhatPure F S (mixedWeilTest F (update f v (archSchwartzDilation u (f v))) g) ψ).val = _
    rw [← stageWeil_archTranslate_real]
    change T (GlobalBruhat.leftTranslate F _ (sLocalBruhatPure F S (mixedWeilTest F f g) ψ).val) = _
    rw [hT, globalWeilWeight_real F S ω hs hu]
    rfl
  have hComplex (v : C F) (u : ℂˣ) (f : R F → 𝓢(ℝ, ℂ)) (g : C F → 𝓢(ℂ, ℂ)) :
      U (mixedWeilTest F f (update g v (archSchwartzDilation u (g v)))) =
        complexArchUnitWeight (complexParameters F S ω hs hu v).2 (z + (complexParameters F S ω hs hu v).1) u *
          U (mixedWeilTest F f g) := by
    change T (sLocalBruhatPure F S (mixedWeilTest F f (update g v (archSchwartzDilation u (g v)))) ψ).val = _
    rw [← stageWeil_archTranslate_complex]
    change T (GlobalBruhat.leftTranslate F _ (sLocalBruhatPure F S (mixedWeilTest F f g) ψ).val) = _
    rw [hT, globalWeilWeight_complex F S ω hs hu]
    rfl
  exact mixedWeilEigen_eval F (realParameters F S ω hs hu) (complexParameters F S ω hs hu)
    z U hReal hComplex f g

private theorem globalWeilWeight_finite (z : ℂ) (v : S) (u : (v.val.adicCompletion F)ˣ) :
    globalWeilWeight F ω z (sLocalEmbed F S (sLocalFiniteZetaInsert F S v u)).val =
      ((sLocalFiniteZetaPhases F S (τ F S ω hs hu) v u : ℂ) * finiteZetaWeight F v.val z u) := by
  rw [sLocalFiniteZetaInsert_embed_eq_singleFiniteIdele, globalWeilWeight_apply, singleFiniteIdele_norm,
    sLocalFiniteZetaPhases_of_global F S ω hs hu]
  rfl

private abbrev FiniteTests (v : S) := locallyConstantTests (v.val.adicCompletion F)

/-- On a separated finite test, adelic translation in one selected finite
place has the Tate action and the exact local quasi-character. -/
theorem globalWeil_finiteRestriction_covariance (z : ℂ)
    (T : StrongDual ℂ (GlobalBruhat F)) (hT : IsGlobalWeilEigen F ω z T)
    (v : S) (u : (v.val.adicCompletion F)ˣ)
    (φ : 𝓢(mixedEmbedding.mixedSpace F, ℂ)) (k : ∀ w : S, FiniteTests F S w) :
    T (sLocalBruhatPure F S φ (locallyConstantTestPiProduct
        (update k v (locallyConstantTestTranslate _ u (k v))))).val =
      ((sLocalFiniteZetaPhases F S (τ F S ω hs hu) v u : ℂ) * finiteZetaWeight F v.val z u) *
        T (sLocalBruhatPure F S φ (locallyConstantTestPiProduct k)).val := by
  rw [← sLocalBruhatLeftTranslate_finiteInsert_piProduct]
  change T (GlobalBruhat.leftTranslate F _ _) = _
  rw [hT, globalWeilWeight_finite F S ω hs hu]
  rfl

section LocalStage

variable (σ : PontryaginDual (SLocalThetaNormOne F S)) (z : ℂ)
variable (T : StrongDual ℂ (Stage F S))
variable (hT : ∀ g f, T (sLocalBruhatLeftTranslate F S g f) =
  sLocalZetaWeight F S σ z (QuotientGroup.mk g) * T f)

private theorem stageWeilWeight_finite (v : S) (u : (v.val.adicCompletion F)ˣ) :
    sLocalZetaWeight F S σ z (QuotientGroup.mk (sLocalFiniteZetaInsert F S v u)) =
      (sLocalFiniteZetaPhases F S σ v u : ℂ) * finiteZetaWeight F v.val z u := by
  unfold sLocalFiniteZetaInsert
  rw [sLocalZetaWeight_product]
  have hone : sLocalZetaWeight F S σ z (1 : SIdeleQuotient F S) = 1 := by
    have h := sLocalZetaWeight_mul F S σ z (1 : SIdeleQuotient F S) 1
    have h1 : (1 : SIdeleQuotient F S) * 1 = 1 := mul_one (1 : SIdeleQuotient F S)
    rw [h1] at h
    have hn : sLocalZetaWeight F S σ z (1 : SIdeleQuotient F S) ≠ 0 :=
      mul_ne_zero (Complex.exp_ne_zero _) (Circle.coe_ne_zero _)
    exact mul_left_cancel₀ hn (by rw [← h, mul_one])
  rw [show sLocalArchZetaInsert F S (1 : ArchUnits F) = 1 by simp [sLocalArchZetaInsert],
    QuotientGroup.mk_one, hone, one_mul, Finset.prod_eq_single v]
  · simp [Pi.mulSingle_eq_same]
  · intro w _ hw
    simp [Pi.mulSingle_eq_of_ne hw, finiteZetaWeight]
  · simp

include hT in
/-- Independent coordinate actions give the archimedean tensor pairing for
any continuous S-local eigenfunctional. -/
theorem sLocalWeil_archRestriction_eval
    (ψ : Test F S) (f : R F → 𝓢(ℝ, ℂ)) (g : C F → 𝓢(ℂ, ℂ)) :
    T (sLocalBruhatPure F S (mixedWeilTest F f g) ψ) =
      T (sLocalBruhatPure F S (mixedWeilTest F
        (mixedWeilRealReference F (sLocalRealArchParameters F S σ))
        (mixedWeilComplexReference F (sLocalComplexArchParameters F S σ))) ψ) *
        sLocalNormalizedArchWeilTensor F S σ f g z := by
  let A : 𝓢(mixedEmbedding.mixedSpace F, ℂ) →L[ℂ] Stage F S :=
    ⟨(sLocalBruhatPure F S).flip ψ,
      (GlobalBruhat.pure_continuous F (insertFinite F S ψ)).subtype_mk _⟩
  let U := T.comp A
  refine mixedWeilEigen_eval F _ _ z U ?_ ?_ f g
  · intro v u f g
    change T (sLocalBruhatPure F S (mixedWeilTest F (update f v (archSchwartzDilation u (f v))) g) ψ) = _
    rw [← stageWeil_archTranslate_real, hT, stageWeilWeight_real]
    rfl
  · intro v u f g
    change T (sLocalBruhatPure F S (mixedWeilTest F f (update g v (archSchwartzDilation u (g v)))) ψ) = _
    rw [← stageWeil_archTranslate_complex, hT, stageWeilWeight_complex]
    rfl

include hT in
/-- The selected finite-coordinate action is the one-place Tate dilation. -/
theorem sLocalWeil_finiteRestriction_covariance
    (v : S) (u : (v.val.adicCompletion F)ˣ)
    (φ : 𝓢(mixedEmbedding.mixedSpace F, ℂ)) (k : ∀ w : S, FiniteTests F S w) :
    T (sLocalBruhatPure F S φ (locallyConstantTestPiProduct
        (update k v (locallyConstantTestTranslate _ u (k v))))) =
      ((sLocalFiniteZetaPhases F S σ v u : ℂ) * finiteZetaWeight F v.val z u) *
        T (sLocalBruhatPure F S φ (locallyConstantTestPiProduct k)) := by
  rw [← sLocalBruhatLeftTranslate_finiteInsert_piProduct, hT, stageWeilWeight_finite]

end LocalStage

end
end Masullo
