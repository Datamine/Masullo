import IdelicWeilCompactFourier
import ManuscriptHeckeRegularity
import ArchimedeanWeilAngular

open Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical NumberField

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

private abbrev K := normOneIdeleClass F
private abbrev Place := HeightOneSpectrum (𝓞 F)
private abbrev R := {v : InfinitePlace F // v.IsReal}
private abbrev C := {v : InfinitePlace F // v.IsComplex}

local instance weilArchSampleClassLC : LocallyCompactSpace (IdeleClass F) :=
  ideleClasses_locallyCompact
local instance weilArchSampleClassT2 : T2Space (IdeleClass F) := ideleClasses_hausdorff
local instance weilArchSampleNormOneMeasurable : MeasurableSpace (K F) := borel _
local instance weilArchSampleNormOneBorel : BorelSpace (K F) := ⟨rfl⟩

set_option maxHeartbeats 1000000

private abbrev realCompletionUnit (v : R F) (u : ℝˣ) :=
  Units.map (InfinitePlace.Completion.ringEquivRealOfIsReal v.property).symm.toMonoidHom u

private abbrev complexCompletionUnit (v : C F) (u : ℂˣ) :=
  Units.map (InfinitePlace.Completion.ringEquivComplexOfIsComplex v.property).symm.toMonoidHom u

/-- The real insertion uses the ordinary absolute value as local modulus. -/
theorem realPlaceWeilInsertion_norm (v : R F) (u : ℝˣ) :
    ideleClassNorm F (realPlaceWeilInsertion F v.val v.property u) = ‖u.val‖ := by
  change ideleClassNorm F (infinitePlaceInsertion F v.val (realCompletionUnit F v u)) = _
  rw [infinitePlaceInsertion_norm, v.property.mult_eq_one, pow_one]
  let e := InfinitePlace.Completion.isometryEquivRealOfIsReal v.property
  have h := e.symm.isometry.dist_eq u.val (0 : ℝ)
  rw [show e.symm (0 : ℝ) = 0 from
    (InfinitePlace.Completion.ringEquivRealOfIsReal v.property).symm.map_zero,
    dist_zero_right, dist_zero_right] at h
  exact h

/-- The complex insertion uses the squared absolute value as local modulus. -/
theorem complexPlaceWeilInsertion_norm (v : C F) (u : ℂˣ) :
    ideleClassNorm F (complexPlaceWeilInsertion F v.val v.property u) = ‖u.val‖ ^ 2 := by
  change ideleClassNorm F (infinitePlaceInsertion F v.val (complexCompletionUnit F v u)) = _
  rw [infinitePlaceInsertion_norm, v.property.mult_eq_two]
  let e := InfinitePlace.Completion.isometryEquivComplexOfIsComplex v.property
  have h := e.symm.isometry.dist_eq u.val (0 : ℂ)
  rw [show e.symm (0 : ℂ) = 0 from
    (InfinitePlace.Completion.ringEquivComplexOfIsComplex v.property).symm.map_zero,
    dist_zero_right, dist_zero_right] at h
  exact congrArg (fun x : ℝ => x ^ 2) h

private def singleInfiniteComponent (v : InfinitePlace F) (u : v.Completionˣ) :
    (InfiniteAdeleRing F)ˣ :=
  Units.map (MonoidHom.fst (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))
    (singleInfiniteIdele F v u)

private theorem singleInfiniteComponent_val (v : InfinitePlace F) (u : v.Completionˣ) :
    (singleInfiniteComponent F v u).val =
      Function.update (fun w : InfinitePlace F => (1 : w.Completion)) v u.val := rfl

private theorem archIntoIdeles_singleInfiniteComponent (v : InfinitePlace F) (u : v.Completionˣ) :
    archIntoIdeles F (singleInfiniteComponent F v u) = singleInfiniteIdele F v u :=
  Units.ext rfl

private theorem infiniteCoordinates_realSingle (v : R F) (u : ℝˣ) :
    infiniteAdeleUnitsCoordinates F (singleInfiniteComponent F v.val (realCompletionUnit F v u)) =
      (Pi.mulSingle v u, 1) := by
  apply Prod.ext
  · funext w
    apply Units.ext
    rw [infiniteAdeleUnitsCoordinates_real_val, InfiniteAdeleRing.ringEquiv_mixedSpace_apply,
      singleInfiniteComponent_val]
    change (InfinitePlace.Completion.ringEquivRealOfIsReal w.property)
      (Function.update (fun z : InfinitePlace F => (1 : z.Completion)) v.val
        (realCompletionUnit F v u).val w.val) = ((Pi.mulSingle v u : R F → ℝˣ) w).val
    by_cases hw : w = v
    · subst w
      rw [Function.update_self, Pi.mulSingle_eq_same]
      exact (InfinitePlace.Completion.ringEquivRealOfIsReal v.property).apply_symm_apply u.val
    · rw [Function.update_of_ne (fun h => hw (Subtype.ext h)), Pi.mulSingle_eq_of_ne hw]
      exact map_one _
  · funext w
    apply Units.ext
    rw [infiniteAdeleUnitsCoordinates_complex_val, InfiniteAdeleRing.ringEquiv_mixedSpace_apply,
      singleInfiniteComponent_val]
    change (InfinitePlace.Completion.ringEquivComplexOfIsComplex w.property)
      (Function.update (fun z : InfinitePlace F => (1 : z.Completion)) v.val
        (realCompletionUnit F v u).val w.val) = 1
    have hw : w.val ≠ v.val := fun h =>
      (InfinitePlace.not_isReal_iff_isComplex.mpr w.property) (h.symm ▸ v.property)
    rw [Function.update_of_ne hw, map_one]

private theorem infiniteCoordinates_complexSingle (v : C F) (u : ℂˣ) :
    infiniteAdeleUnitsCoordinates F (singleInfiniteComponent F v.val (complexCompletionUnit F v u)) =
      (1, Pi.mulSingle v u) := by
  apply Prod.ext
  · funext w
    apply Units.ext
    rw [infiniteAdeleUnitsCoordinates_real_val, InfiniteAdeleRing.ringEquiv_mixedSpace_apply,
      singleInfiniteComponent_val]
    change (InfinitePlace.Completion.ringEquivRealOfIsReal w.property)
      (Function.update (fun z : InfinitePlace F => (1 : z.Completion)) v.val
        (complexCompletionUnit F v u).val w.val) = 1
    have hw : w.val ≠ v.val := fun h =>
      (InfinitePlace.not_isReal_iff_isComplex.mpr v.property) (h ▸ w.property)
    rw [Function.update_of_ne hw, map_one]
  · funext w
    apply Units.ext
    rw [infiniteAdeleUnitsCoordinates_complex_val, InfiniteAdeleRing.ringEquiv_mixedSpace_apply,
      singleInfiniteComponent_val]
    change (InfinitePlace.Completion.ringEquivComplexOfIsComplex w.property)
      (Function.update (fun z : InfinitePlace F => (1 : z.Completion)) v.val
        (complexCompletionUnit F v u).val w.val) = ((Pi.mulSingle v u : C F → ℂˣ) w).val
    by_cases hw : w = v
    · subst w
      rw [Function.update_self, Pi.mulSingle_eq_same]
      exact (InfinitePlace.Completion.ringEquivComplexOfIsComplex v.property).apply_symm_apply u.val
    · rw [Function.update_of_ne (fun h => hw (Subtype.ext h)), Pi.mulSingle_eq_of_ne hw]
      exact map_one _

variable (χ : PontryaginDual (IdeleClass F)) (S : Finset (Place F))
  (hs : Surjective (sIdeleClassInclusion F S))
  (hu : globalNormOneCharacter F (heckeNormOneRestriction F χ) ∈
    (sUnramified F S : Set (QuasiCharacter (IdeleClass F))))

private abbrev phase := sLocalNormOneCharacterOfGlobal F (heckeNormOneRestriction F χ) S hs hu

private theorem realArchWeight_one (z : ℂ) (v : R F) :
    sLocalRealArchWeight F S (phase F χ S hs hu) v z 1 = 1 := by
  simp [sLocalRealArchWeight]

private theorem complexArchWeight_one (z : ℂ) (v : C F) :
    sLocalComplexArchWeight F S (phase F χ S hs hu) v z 1 = 1 := by
  simp [sLocalComplexArchWeight]

/-- The real-place factor in the gamma formula uses the character of
the actual real idele insertion. -/
theorem realPlaceWeilInsertion_character {t : ℝ} (ht : HasHeckeHeight F χ t)
    (v : R F) (u : ℝˣ) :
    (χ (realPlaceWeilInsertion F v.val v.property u) : ℂ) =
      sLocalRealArchWeight F S (phase F χ S hs hu) v (-(t : ℂ) * Complex.I) u := by
  let a := singleInfiniteComponent F v.val (realCompletionUnit F v u)
  let z : ℂ := -(t : ℂ) * Complex.I
  let p := infiniteAdeleUnitsCoordinates F a
  have hp : p = (Pi.mulSingle v u, 1) := infiniteCoordinates_realSingle F v u
  have hR : (∏ w : R F, sLocalRealArchWeight F S (phase F χ S hs hu) w z (p.1 w)) =
      sLocalRealArchWeight F S (phase F χ S hs hu) v z u := by
    rw [hp, Finset.prod_eq_single v]
    · exact congrArg (sLocalRealArchWeight F S (phase F χ S hs hu) v z) (by simp only [Pi.mulSingle_eq_same])
    · intro w _ hw
      change sLocalRealArchWeight F S (phase F χ S hs hu) w z ((Pi.mulSingle v u : R F → ℝˣ) w) = 1
      rw [Pi.mulSingle_eq_of_ne hw, realArchWeight_one]
    · simp
  have hC : (∏ w : C F, sLocalComplexArchWeight F S (phase F χ S hs hu) w z (p.2 w)) = 1 := by
    rw [hp]
    exact Finset.prod_eq_one fun w _ => complexArchWeight_one F χ S hs hu z w
  have hz : (0 : ℂ) - (t : ℂ) * Complex.I = z := by dsimp [z]; ring
  have h := manuscriptHecke_archWeight F χ S hs hu t ht a 0
  change (χ (ideleClassMap F (archIntoIdeles F a)) : ℂ) * Complex.exp (0 * (Real.log ‖a.val‖ : ℂ)) =
    (∏ w : R F, sLocalRealArchWeight F S (phase F χ S hs hu) w (0 - (t : ℂ) * Complex.I) (p.1 w)) *
      (∏ w : C F, sLocalComplexArchWeight F S (phase F χ S hs hu) w (0 - (t : ℂ) * Complex.I) (p.2 w)) at h
  rw [zero_mul, Complex.exp_zero, mul_one, hz, hR, hC, mul_one] at h
  have ha : ideleClassMap F (archIntoIdeles F a) = realPlaceWeilInsertion F v.val v.property u :=
    congrArg (ideleClassMap F) (archIntoIdeles_singleInfiniteComponent F v.val (realCompletionUnit F v u))
  exact (congrArg (fun j => (χ j : ℂ)) ha).symm.trans h

/-- The complex-place factor in the gamma formula uses the character of
the actual complex idele insertion. -/
theorem complexPlaceWeilInsertion_character {t : ℝ} (ht : HasHeckeHeight F χ t)
    (v : C F) (u : ℂˣ) :
    (χ (complexPlaceWeilInsertion F v.val v.property u) : ℂ) =
      sLocalComplexArchWeight F S (phase F χ S hs hu) v (-(t : ℂ) * Complex.I) u := by
  let a := singleInfiniteComponent F v.val (complexCompletionUnit F v u)
  let z : ℂ := -(t : ℂ) * Complex.I
  let p := infiniteAdeleUnitsCoordinates F a
  have hp : p = (1, Pi.mulSingle v u) := infiniteCoordinates_complexSingle F v u
  have hR : (∏ w : R F, sLocalRealArchWeight F S (phase F χ S hs hu) w z (p.1 w)) = 1 := by
    rw [hp]
    exact Finset.prod_eq_one fun w _ => realArchWeight_one F χ S hs hu z w
  have hC : (∏ w : C F, sLocalComplexArchWeight F S (phase F χ S hs hu) w z (p.2 w)) =
      sLocalComplexArchWeight F S (phase F χ S hs hu) v z u := by
    rw [hp, Finset.prod_eq_single v]
    · exact congrArg (sLocalComplexArchWeight F S (phase F χ S hs hu) v z) (by simp only [Pi.mulSingle_eq_same])
    · intro w _ hw
      change sLocalComplexArchWeight F S (phase F χ S hs hu) w z ((Pi.mulSingle v u : C F → ℂˣ) w) = 1
      rw [Pi.mulSingle_eq_of_ne hw, complexArchWeight_one]
    · simp
  have hz : (0 : ℂ) - (t : ℂ) * Complex.I = z := by dsimp [z]; ring
  have h := manuscriptHecke_archWeight F χ S hs hu t ht a 0
  change (χ (ideleClassMap F (archIntoIdeles F a)) : ℂ) * Complex.exp (0 * (Real.log ‖a.val‖ : ℂ)) =
    (∏ w : R F, sLocalRealArchWeight F S (phase F χ S hs hu) w (0 - (t : ℂ) * Complex.I) (p.1 w)) *
      (∏ w : C F, sLocalComplexArchWeight F S (phase F χ S hs hu) w (0 - (t : ℂ) * Complex.I) (p.2 w)) at h
  rw [zero_mul, Complex.exp_zero, mul_one, hz, hR, hC, one_mul] at h
  have ha : ideleClassMap F (archIntoIdeles F a) = complexPlaceWeilInsertion F v.val v.property u :=
    congrArg (ideleClassMap F) (archIntoIdeles_singleInfiniteComponent F v.val (complexCompletionUnit F v u))
  exact (congrArg (fun j => (χ j : ℂ)) ha).symm.trans h

variable (ν : Measure (K F)) [ν.IsHaarMeasure]

/-- The norm-one Fourier expansion reconstructs the test on every real
or complex local insertion with its actual modulus and inverse phase. -/
theorem idelicWeil_archSample_hasSum {A : Type*} [Monoid A] [TopologicalSpace A]
    (ι : A →ₜ* IdeleClass F) (f : BruhatCompactTest (IdeleClass F)) (u : A) :
    let t := (ideleClassLogNorm F (ι u)).toAdd
    HasSum (fun ω : PontryaginDual (K F) =>
      ((ν.real univ : ℂ)⁻¹ * idelicWeilLogProfile F ν ω f t) *
        (((normOneEulerCharacter F ω (ι u))⁻¹ : Circle) : ℂ))
      (f.val.val (ι u)) := by
  let t := ideleClassLogNorm F (ι u)
  let g := ideleClassExpSection F t
  let k := ideleClassNormOnePart F (ι u)
  have hk : k.val * g = ι u := (ideleClassSplit F).left_inv (ι u)
  have h := hasSum_idelicWeil_compactCoefficients F ν f g k
  rw [hk] at h
  exact h

/-- Real logarithmic samples are evaluated at the log of the ordinary absolute value. -/
theorem idelicWeil_realSample_hasSum (f : BruhatCompactTest (IdeleClass F)) (v : R F) (u : ℝˣ) :
    HasSum (fun ω : PontryaginDual (K F) =>
      ((ν.real univ : ℂ)⁻¹ * idelicWeilLogProfile F ν ω f (Real.log ‖u.val‖)) *
        (((normOneEulerCharacter F ω (realPlaceWeilInsertion F v.val v.property u))⁻¹ : Circle) : ℂ))
      (f.val.val (realPlaceWeilInsertion F v.val v.property u)) := by
  have h := idelicWeil_archSample_hasSum F ν (realPlaceWeilInsertion F v.val v.property) f u
  have ht : (ideleClassLogNorm F (realPlaceWeilInsertion F v.val v.property u)).toAdd =
      Real.log ‖u.val‖ := by
    change Real.log (ideleClassNorm F (realPlaceWeilInsertion F v.val v.property u)) = _
    rw [realPlaceWeilInsertion_norm]
  dsimp only at h
  rwa [ht] at h

/-- Complex logarithmic samples are evaluated at the log of the squared absolute value. -/
theorem idelicWeil_complexSample_hasSum (f : BruhatCompactTest (IdeleClass F)) (v : C F) (u : ℂˣ) :
    HasSum (fun ω : PontryaginDual (K F) =>
      ((ν.real univ : ℂ)⁻¹ * idelicWeilLogProfile F ν ω f (Real.log (‖u.val‖ ^ 2))) *
        (((normOneEulerCharacter F ω (complexPlaceWeilInsertion F v.val v.property u))⁻¹ : Circle) : ℂ))
      (f.val.val (complexPlaceWeilInsertion F v.val v.property u)) := by
  have h := idelicWeil_archSample_hasSum F ν (complexPlaceWeilInsertion F v.val v.property) f u
  have ht : (ideleClassLogNorm F (complexPlaceWeilInsertion F v.val v.property u)).toAdd =
      Real.log (‖u.val‖ ^ 2) := by
    change Real.log (ideleClassNorm F (complexPlaceWeilInsertion F v.val v.property u)) = _
    rw [complexPlaceWeilInsertion_norm]
  dsimp only at h
  rwa [ht] at h

end
end Masullo
