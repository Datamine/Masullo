import IdelicWeilArchAverage
import HeckeExplicitFormula

open Function IsDedekindDomain NumberField Set
open scoped Classical NumberField

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

private abbrev R := {v : InfinitePlace F // v.IsReal}
private abbrev C := {v : InfinitePlace F // v.IsComplex}
private abbrev Place := HeightOneSpectrum (𝓞 F)

variable (χ : PontryaginDual (IdeleClass F)) (S T : Finset (Place F))
  (hs : Surjective (sIdeleClassInclusion F S)) (ht : Surjective (sIdeleClassInclusion F T))
  (hu : globalNormOneCharacter F (heckeNormOneRestriction F χ) ∈
    (sUnramified F S : Set (QuasiCharacter (IdeleClass F))))
  (hu' : globalNormOneCharacter F (heckeNormOneRestriction F χ⁻¹) ∈
    (sUnramified F T : Set (QuasiCharacter (IdeleClass F))))

private abbrev phase := sLocalNormOneCharacterOfGlobal F (heckeNormOneRestriction F χ) S hs hu
private abbrev phaseInv := sLocalNormOneCharacterOfGlobal F (heckeNormOneRestriction F χ⁻¹) T ht hu'

/-- The forward and reflected local characters have opposite radial
and complex angular parameters, even if their Tate stages differ. -/
theorem idelicWeil_gammaParameters_inv :
    (∀ v : R F,
      (sLocalRealArchParameters F T (phaseInv F χ T ht hu') v).1 =
        -(sLocalRealArchParameters F S (phase F χ S hs hu) v).1 ∧
      (sLocalRealArchParameters F T (phaseInv F χ T ht hu') v).2 % 2 =
        (sLocalRealArchParameters F S (phase F χ S hs hu) v).2 % 2) ∧
    (∀ v : C F, sLocalComplexArchParameters F T (phaseInv F χ T ht hu') v =
      (-(sLocalComplexArchParameters F S (phase F χ S hs hu) v).1,
        -(sLocalComplexArchParameters F S (phase F χ S hs hu) v).2)) := by
  let ω := heckeNormOneRestriction F χ
  have h (a : (InfiniteAdeleRing F)ˣ) :
      sLocalZetaWeight F S (phase F χ S hs hu)⁻¹ 0 (QuotientGroup.mk (sLocalArchZetaInsert F S a)) =
        sLocalZetaWeight F T (phaseInv F χ T ht hu') 0 (QuotientGroup.mk (sLocalArchZetaInsert F T a)) := by
    rw [sLocalZetaUnitaryWeight_inv, sLocalZetaWeight_global_arch_apply,
      sLocalZetaWeight_global_arch_apply]
    simp only [zero_mul, Complex.exp_zero, one_mul, heckeNormOneRestriction_inv]
    change ((ω (ideleClassNormOnePart F (ideleClassMap F (archIntoIdeles F a))) : ℂ))⁻¹ =
      ((ω⁻¹ (ideleClassNormOnePart F (ideleClassMap F (archIntoIdeles F a))) : Circle) : ℂ)
    exact (Circle.coe_inv _).symm
  obtain ⟨hR, hC⟩ := sLocalArchParameters_eq_of_weight F S (phase F χ S hs hu)⁻¹
    (phaseInv F χ T ht hu') h
  constructor
  · intro v
    exact ⟨(hR v).1.symm.trans (sLocalRealArchParameters_inv F S (phase F χ S hs hu) v).1,
      (hR v).2.symm.trans (sLocalRealArchParameters_inv F S (phase F χ S hs hu) v).2⟩
  · intro v
    exact (hC v).symm.trans (sLocalComplexArchParameters_inv F S (phase F χ S hs hu) v)

/-- The reflected real gamma shift, expressed using the forward stage. -/
theorem idelicWeil_realGammaShift_inv (t : ℝ) (v : R F) :
    manuscriptHeckeRealGammaShift F χ⁻¹ T ht hu' (-t) v =
      -(sLocalRealArchParameters F S (phase F χ S hs hu) v).1 +
        (((sLocalRealArchParameters F S (phase F χ S hs hu) v).2 % 2 : ℕ) : ℂ) +
        (t : ℂ) * Complex.I := by
  obtain ⟨h, _⟩ := idelicWeil_gammaParameters_inv F χ S T hs ht hu hu'
  obtain ⟨h₁, h₂⟩ := h v
  change (sLocalRealArchParameters F T (phaseInv F χ T ht hu') v).1 +
      (((sLocalRealArchParameters F T (phaseInv F χ T ht hu') v).2 % 2 : ℕ) : ℂ) -
        ((-t : ℝ) : ℂ) * Complex.I = _
  rw [h₁, h₂, Complex.ofReal_neg]
  ring

/-- The reflected complex gamma shift, expressed using the forward stage. -/
theorem idelicWeil_complexGammaShift_inv (t : ℝ) (v : C F) :
    manuscriptHeckeComplexGammaShift F χ⁻¹ T ht hu' (-t) v =
      -(sLocalComplexArchParameters F S (phase F χ S hs hu) v).1 +
        ((sLocalComplexArchParameters F S (phase F χ S hs hu) v).2.natAbs : ℂ) / 2 +
        (t : ℂ) * Complex.I := by
  obtain ⟨_, h⟩ := idelicWeil_gammaParameters_inv F χ S T hs ht hu hu'
  change (sLocalComplexArchParameters F T (phaseInv F χ T ht hu') v).1 +
      ((sLocalComplexArchParameters F T (phaseInv F χ T ht hu') v).2.natAbs : ℂ) / 2 -
        ((-t : ℝ) : ℂ) * Complex.I = _
  rw [h v, Int.natAbs_neg, Complex.ofReal_neg]
  ring

end
end Masullo
