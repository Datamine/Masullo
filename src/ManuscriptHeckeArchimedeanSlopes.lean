import IdelicStageRank
import ManuscriptHeckeRegularity
import IdelicMellinSummation

open Function IsDedekindDomain NumberField
open scoped Classical NumberField

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

private abbrev RealPlace := {v : InfinitePlace F // v.IsReal}
private abbrev ComplexPlace := {v : InfinitePlace F // v.IsComplex}
private abbrev Arch := mixedEmbedding.mixedSpace F

private def mixedInfiniteExp (x : Multiplicative (Arch F)) : (InfiniteAdeleRing F)ˣ :=
  Units.map (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm.toMonoidHom (mixedExpUnits F x)

/-- The idele-class flow along an archimedean velocity, with all finite components trivial. -/
def manuscriptArchFlow (v : Arch F) : Multiplicative ℝ →ₜ* IdeleClass F :=
  (archimedeanClassExponential F).comp
    { toMonoidHom := (show ℝ →+ Arch F from
        { toFun := fun x ↦ x • v
          map_zero' := zero_smul ℝ v
          map_add' := fun x y ↦ add_smul x y v }).toMultiplicative
      continuous_toFun := continuous_ofAdd.comp (continuous_toAdd.smul continuous_const) }

private theorem archIntoIdeles_mixedInfiniteExp (x : Multiplicative (Arch F)) :
    archIntoIdeles F (mixedInfiniteExp F x) = mixedArchExpIdele F x := by
  apply Units.ext
  rfl

private theorem ofReal_cpow_exp (x : ℝ) (z : ℂ) :
    ((Real.exp x : ℝ) : ℂ) ^ z = Complex.exp (z * (x : ℂ)) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero x)),
    ← Complex.ofReal_log (Real.exp_pos x).le, Real.log_exp, mul_comm]

private theorem exp_div_norm (x : ℂ) :
    Complex.exp x / (‖Complex.exp x‖ : ℂ) = Complex.exp ((x.im : ℂ) * Complex.I) := by
  rw [Complex.norm_exp, Complex.ofReal_exp, div_eq_iff (Complex.exp_ne_zero _),
    ← Complex.exp_add, add_comm, Complex.re_add_im]

variable (χ : PontryaginDual (IdeleClass F))
variable (S : Finset (HeightOneSpectrum (𝓞 F)))
variable (hs : Surjective (sIdeleClassInclusion F S))
variable (hu : globalNormOneCharacter F (heckeNormOneRestriction F χ) ∈
  (sUnramified F S : Set (QuasiCharacter (IdeleClass F))))

private abbrev slopeArchPhase :=
  sLocalNormOneCharacterOfGlobal F (heckeNormOneRestriction F χ) S hs hu

/-- The coefficient of the archimedean velocity in the character and norm twist.
The complex radial term uses the squared absolute value. -/
def manuscriptArchExponent (t : ℝ) (s : ℂ) (v : Arch F) : ℂ :=
  (∑ j : RealPlace F,
    (s - (t : ℂ) * Complex.I + (sLocalRealArchParameters F S (slopeArchPhase F χ S hs hu) j).1) *
      (v.1 j : ℂ)) +
  ∑ j : ComplexPlace F,
    ((s - (t : ℂ) * Complex.I + (sLocalComplexArchParameters F S (slopeArchPhase F χ S hs hu) j).1) *
      ((2 * (v.2 j).re : ℝ) : ℂ) +
      ((sLocalComplexArchParameters F S (slopeArchPhase F χ S hs hu) j).2 : ℂ) *
        ((v.2 j).im : ℂ) * Complex.I)

/-- The character along the actual archimedean flow is the exponential of
the sum of the finite list of radial and angular parameter evaluations. -/
theorem manuscriptHecke_archFlow (t : ℝ) (ht : HasHeckeHeight F χ t) (s : ℂ)
    (v : Arch F) (x : ℝ) :
    (χ (manuscriptArchFlow F v (Multiplicative.ofAdd x)) : ℂ) *
      Complex.exp (s * ((ideleClassLogNorm F
        (manuscriptArchFlow F v (Multiplicative.ofAdd x))).toAdd : ℂ)) =
      Complex.exp (manuscriptArchExponent F χ S hs hu t s v * (x : ℂ)) := by
  let a := mixedInfiniteExp F (Multiplicative.ofAdd (x • v))
  have hf : manuscriptArchFlow F v (Multiplicative.ofAdd x) =
      ideleClassMap F (archIntoIdeles F a) := by
    rw [archIntoIdeles_mixedInfiniteExp]
    rfl
  have hn : (ideleClassLogNorm F (ideleClassMap F (archIntoIdeles F a))).toAdd =
      Real.log ‖a.val‖ := by
    change Real.log (ideleClassNorm F (ideleClassMap F (archIntoIdeles F a))) = _
    rw [ideleClassNorm_mk]
    have h := archIntoIdeles_logNorm F a
    rw [infiniteIdeleLogNorm_eq] at h
    exact congrArg Multiplicative.toAdd h
  rw [hf, hn, manuscriptHecke_archWeight F χ S hs hu t ht]
  have hR (j : RealPlace F) :
      (((infiniteAdeleUnitsCoordinates F a).1 j : ℝˣ) : ℝ) = Real.exp (x * v.1 j) := by
    rw [infiniteAdeleUnitsCoordinates_real_val]
    change ((InfiniteAdeleRing.ringEquiv_mixedSpace F)
      ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (mixedExp F (x • v)))).1 j = _
    rw [RingEquiv.apply_symm_apply]
    rfl
  have hC (j : ComplexPlace F) :
      (((infiniteAdeleUnitsCoordinates F a).2 j : ℂˣ) : ℂ) =
        Complex.exp ((x : ℂ) * v.2 j) := by
    rw [infiniteAdeleUnitsCoordinates_complex_val]
    change ((InfiniteAdeleRing.ringEquiv_mixedSpace F)
      ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (mixedExp F (x • v)))).2 j = _
    rw [RingEquiv.apply_symm_apply]
    rfl
  simp only [sLocalRealArchWeight, hR, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    not_lt_of_ge (Real.exp_pos _).le, ite_false, mul_one, ofReal_cpow_exp,
    sLocalComplexArchWeight, hC]
  simp_rw [exp_div_norm, ← Complex.exp_int_mul, Complex.norm_exp, sq, ← Real.exp_add,
    ofReal_cpow_exp, ← Complex.exp_add, ← Complex.exp_sum]
  rw [← Complex.exp_add]
  apply congrArg Complex.exp
  unfold manuscriptArchExponent
  rw [add_mul, Finset.sum_mul, Finset.sum_mul]
  congr 1
  · apply Finset.sum_congr rfl
    intro j _
    push_cast
    ring
  · apply Finset.sum_congr rfl
    intro j _
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, add_zero]
    push_cast
    ring

/-- The invariant Mellin symbol is evaluated using the actual Hecke parameters. -/
theorem manuscriptHecke_archSlope (t : ℝ) (ht : HasHeckeHeight F χ t) (a : ℝ) (v : Arch F) :
    mellinOrbitSlope (G := IdeleClass F) (mellinClassModulus F) a χ (manuscriptArchFlow F v) =
      manuscriptArchExponent F χ S hs hu t a v :=
  mellinOrbitSlope_eq_of_orbit_exp (G := IdeleClass F) (mellinClassModulus F) a χ _ _
    (manuscriptHecke_archFlow F χ S hs hu t ht a v)

private theorem manuscriptArchFlow_apply (v : Arch F) (x : ℝ) :
    manuscriptArchFlow F v (Multiplicative.ofAdd x) =
      archimedeanClassExponential F (Multiplicative.ofAdd (x • v)) := rfl

/-- The symbol of an arbitrary idele-class direction is evaluated by a single
archimedean velocity, independent of the character. -/
theorem exists_manuscriptArchFlow_eq (c : Multiplicative ℝ →ₜ* IdeleClass F) :
    ∃ v : Arch F, c = manuscriptArchFlow F v := by
  obtain ⟨v, hv⟩ := exists_archimedeanClassExponential_direction F c
  refine ⟨v, ContinuousMonoidHom.ext fun x ↦ ?_⟩
  exact (hv x.toAdd).trans (manuscriptArchFlow_apply F v x.toAdd).symm

set_option maxHeartbeats 600000 in
/-- The flow used to compute the Mellin symbol projects by the same linear
velocity map as the one used in an elementary Bruhat stage. -/
theorem exists_manuscriptArchFlow_stageVelocity (P : WholeBruhatStage (IdeleClass F)) :
    ∃ L : Arch F →ₗ[ℝ]
      (EuclideanSpace ℝ (Fin P.val.2.realDim) × EuclideanSpace ℝ (Fin P.val.2.torusDim)),
      Surjective L ∧ ∀ v x, P.coordinates (manuscriptArchFlow F v (Multiplicative.ofAdd x)) =
        elementaryOneParameter (L v) (Multiplicative.ofAdd x) := by
  simpa only [manuscriptArchFlow_apply] using exists_ideleClassStage_archimedeanVelocity F P

/-- The radial symbol at a real place is its shifted gamma parameter. -/
theorem manuscriptHecke_realSlope (t : ℝ) (ht : HasHeckeHeight F χ t) (a : ℝ)
    (j : RealPlace F) :
    mellinOrbitSlope (G := IdeleClass F) (mellinClassModulus F) a χ
      (manuscriptArchFlow F (Pi.single j 1, 0)) =
        (a : ℂ) - (t : ℂ) * Complex.I +
          (sLocalRealArchParameters F S (slopeArchPhase F χ S hs hu) j).1 := by
  rw [manuscriptHecke_archSlope F χ S hs hu t ht]
  simp [manuscriptArchExponent, Pi.single_apply, apply_ite Complex.ofReal, mul_ite]

/-- The radial symbol at a complex place uses half-speed in the ordinary modulus. -/
theorem manuscriptHecke_complexRadialSlope (t : ℝ) (ht : HasHeckeHeight F χ t) (a : ℝ)
    (j : ComplexPlace F) :
    mellinOrbitSlope (G := IdeleClass F) (mellinClassModulus F) a χ
      (manuscriptArchFlow F (0, Pi.single j ((1 : ℂ) / 2))) =
        (a : ℂ) - (t : ℂ) * Complex.I +
          (sLocalComplexArchParameters F S (slopeArchPhase F χ S hs hu) j).1 := by
  rw [manuscriptHecke_archSlope F χ S hs hu t ht]
  have hhalf : (1 : ℂ) / 2 = ((1 / 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
  simp [manuscriptArchExponent, Pi.single_apply, hhalf, apply_ite Complex.re,
    apply_ite Complex.im, apply_ite Complex.ofReal, mul_ite]

/-- The angular symbol at a complex place is its integral angular index times (i). -/
theorem manuscriptHecke_complexAngularSlope (t : ℝ) (ht : HasHeckeHeight F χ t) (a : ℝ)
    (j : ComplexPlace F) :
    mellinOrbitSlope (G := IdeleClass F) (mellinClassModulus F) a χ
      (manuscriptArchFlow F (0, Pi.single j Complex.I)) =
        ((sLocalComplexArchParameters F S (slopeArchPhase F χ S hs hu) j).2 : ℂ) * Complex.I := by
  rw [manuscriptHecke_archSlope F χ S hs hu t ht]
  simp [manuscriptArchExponent, Pi.single_apply, apply_ite Complex.re,
    apply_ite Complex.im, apply_ite Complex.ofReal, mul_ite]

/-- The flow along the global logarithmic norm coordinate. -/
def manuscriptNormFlow : Multiplicative ℝ →ₜ* IdeleClass F :=
  ⟨ideleClassExpSection F, ideleClassExpSection_continuous F⟩

/-- The symbol in the global norm direction recovers the manuscript's height, with sign minus. -/
theorem manuscriptHecke_normSlope (t : ℝ) (ht : HasHeckeHeight F χ t) (a : ℝ) :
    mellinOrbitSlope (G := IdeleClass F) (mellinClassModulus F) a χ (manuscriptNormFlow F) = (a : ℂ) - (t : ℂ) * Complex.I := by
  apply mellinOrbitSlope_eq_of_orbit_exp
  intro x
  let u := ideleClassExpSection F (Multiplicative.ofAdd x)
  have hpart : ideleClassNormOnePart F u = 1 := by
    apply Subtype.ext
    change u / ideleClassExpSection F (ideleClassLogNorm F u) = 1
    rw [show ideleClassLogNorm F u = Multiplicative.ofAdd x from ideleClassLogNorm_expSection F _]
    exact div_self' u
  have hp : (normOneEulerCharacter F (heckeNormOneRestriction F χ) u : ℂ) = 1 := by
    change (heckeNormOneRestriction F χ (ideleClassNormOnePart F u) : ℂ) = 1
    rw [hpart, map_one, Circle.coe_one]
  change (χ u : ℂ) * Complex.exp ((a : ℂ) * ((ideleClassLogNorm F u).toAdd : ℂ)) = _
  rw [ht, hp, one_mul, ideleClassNorm_expSection, Real.log_exp, ideleClassLogNorm_expSection,
    ← Complex.exp_add]
  apply congrArg Complex.exp
  change _ * (x : ℂ) + (a : ℂ) * (x : ℂ) = _
  ring

end

end Masullo
