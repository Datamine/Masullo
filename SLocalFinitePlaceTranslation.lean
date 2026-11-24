import SLocalZetaProduct
import SLocalThetaFourier
import HeckeEulerProducts

open Function IsDedekindDomain NumberField Set
open scoped Classical NumberField SchwartzMap

namespace Masullo
noncomputable section

variable (F : Type*) [Field F] [NumberField F]
private abbrev Place := HeightOneSpectrum (𝓞 F)
private abbrev Stage (S : Finset (Place F)) := sLocalBruhatImage F S
variable (S : Finset (Place F))

private theorem finitePlaceTranslation_stage_ext {S : Finset (Place F)} {f g : Stage F S}
    (h : ∀ x, sLocalBruhatRestriction F S f.val x = sLocalBruhatRestriction F S g.val x) : f = g := by
  apply Subtype.ext
  apply (GlobalBruhat.algebraicEquiv F).injective
  apply Subtype.ext
  funext x
  change GlobalBruhat.evaluation F x f.val = GlobalBruhat.evaluation F x g.val
  rw [sLocalBruhatRestriction_reconstruct, sLocalBruhatRestriction_reconstruct, h]

theorem sLocalFiniteZetaInsert_embed_eq_singleFiniteIdele (v : S) (u : (v.val.adicCompletion F)ˣ) :
    (sLocalEmbed F S (sLocalFiniteZetaInsert F S v u)).val = singleFiniteIdele F v.val u := by
  apply Units.ext
  apply Prod.ext
  · rw [sLocalEmbed_arch]
    rfl
  · apply DFunLike.ext
    intro w
    by_cases hw : w ∈ S
    · have h := sLocalEmbed_finite F S (sLocalFiniteZetaInsert F S v u) ⟨w, hw⟩
      change _ = (Pi.mulSingle (M := fun v : S => (v.val.adicCompletion F)ˣ) v u ⟨w, hw⟩).val at h
      rw [h]
      change _ = update (fun j : Place F => (1 : j.adicCompletion F)) v.val u.val w
      by_cases hwv : w = v.val
      · subst w
        change (Pi.mulSingle (M := fun v : S => (v.val.adicCompletion F)ˣ) v u v).val = _
        rw [Pi.mulSingle_eq_same, update_self]
      · rw [Pi.mulSingle_eq_of_ne (fun e => hwv (congrArg Subtype.val e)), update_of_ne hwv]
        rfl
    · rw [sLocalEmbed_outside_one F S _ w hw]
      change 1 = update (fun j : Place F => (1 : j.adicCompletion F)) v.val u.val w
      have hn : w ≠ v.val := fun e => hw (e.symm ▸ v.property)
      rw [update_of_ne hn]

private abbrev FiniteTests (v : S) := locallyConstantTests (v.val.adicCompletion F)

theorem sLocalBruhatLeftTranslate_finiteInsert_piProduct (v : S) (u : (v.val.adicCompletion F)ˣ)
    (φ : 𝓢(mixedEmbedding.mixedSpace F, ℂ)) (k : ∀ w : S, FiniteTests F S w) :
    sLocalBruhatLeftTranslate F S (sLocalFiniteZetaInsert F S v u)
      (sLocalBruhatPure F S φ (locallyConstantTestPiProduct k)) =
    sLocalBruhatPure F S φ (locallyConstantTestPiProduct
      (update k v (locallyConstantTestTranslate _ u (k v)))) := by
  apply finitePlaceTranslation_stage_ext F
  intro x
  rw [sLocalBruhatLeftTranslate_restrict, sLocalBruhatPure_restrict, sLocalBruhatPure_restrict]
  have hi : (sLocalFiniteZetaInsert F S v u)⁻¹ = sLocalFiniteZetaInsert F S v u⁻¹ := by
    unfold sLocalFiniteZetaInsert
    rw [← map_inv, Prod.inv_mk, inv_one, Pi.mulSingle_inv]
  have he : (sLocalFiniteZetaInsert F S v u).inv = (sLocalFiniteZetaInsert F S v u⁻¹).val :=
    congrArg Units.val hi
  rw [he]
  let m : ∀ w : S, (w.val.adicCompletion F)ˣ := Pi.mulSingle v u⁻¹
  change φ (InfiniteAdeleRing.ringEquiv_mixedSpace F (1 * x.1)) *
      (∏ w : S, (k w).val ((m w).val * x.2 w)) =
      φ (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1) *
        ∏ w : S, (update k v (locallyConstantTestTranslate _ u (k v)) w).val (x.2 w)
  rw [one_mul]
  congr 1
  apply Finset.prod_congr rfl
  intro w _
  by_cases hw : w = v
  · subst w
    rw [update_self, show m v = u⁻¹ from Pi.mulSingle_eq_same _ _]
    rfl
  · rw [update_of_ne hw, show m w = 1 from Pi.mulSingle_eq_of_ne hw _,
      Units.val_one, one_mul]

end
end Masullo
