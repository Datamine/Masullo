import IdelicHeckeFrequencyBoxes

open Function IsDedekindDomain NumberField
open scoped Classical NumberField

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]
private abbrev K := normOneIdeleClass F
private abbrev RealPlace := {v : InfinitePlace F // v.IsReal}
private abbrev ComplexPlace := {v : InfinitePlace F // v.IsComplex}

/-- The unitary character obtained by adding the norm phase of ordinate `y`
to a norm-one character. -/
def heckeOrdinateCharacter (ω : PontryaginDual (K F)) (y : ℝ) :
    PontryaginDual (IdeleClass F) where
  toFun g := normOneEulerCharacter F ω g *
    Circle.exp (y * (ideleClassLogNorm F g).toAdd)
  map_one' := by simp
  map_mul' g h := by
    rw [map_mul (normOneEulerCharacter F ω), map_mul (ideleClassLogNorm F)]
    change _ * Circle.exp (y * ((ideleClassLogNorm F g).toAdd +
      (ideleClassLogNorm F h).toAdd)) = _
    rw [mul_add, Circle.exp_add]
    ac_rfl
  continuous_toFun := (normOneEulerCharacter F ω).continuous.mul (Circle.exp.continuous.comp
    (continuous_const.mul (continuous_toAdd.comp (ideleClassLogNorm_continuous F))))

private theorem normOnePart_subtype (x : K F) : ideleClassNormOnePart F x.val = x := by
  apply Subtype.ext
  have h : ideleClassLogNorm F x.val = 1 := by
    change Multiplicative.ofAdd (Real.log (ideleClassNorm F x.val)) = 1
    rw [x.property, Real.log_one]
    rfl
  change x.val / ideleClassExpSection F (ideleClassLogNorm F x.val) = x.val
  rw [h, map_one, div_one]

@[simp] theorem heckeNormOneRestriction_ordinateCharacter (ω : PontryaginDual (K F)) (y : ℝ) :
    heckeNormOneRestriction F (heckeOrdinateCharacter F ω y) = ω := by
  apply PontryaginDual.ext
  intro x
  have h : (ideleClassLogNorm F x.val).toAdd = 0 := by
    change Real.log (ideleClassNorm F x.val) = _
    rw [x.property, Real.log_one]
  change ω (ideleClassNormOnePart F x.val) * Circle.exp (y * (ideleClassLogNorm F x.val).toAdd) = ω x
  rw [normOnePart_subtype, h, mul_zero, Circle.exp_zero, mul_one]

/-- The spectrum convention (\omega|\cdot|^{\rho}) uses height minus the zero's
ordinate in the manuscript's unitary character chart. -/
theorem heckeOrdinateCharacter_hasHeight (ω : PontryaginDual (K F)) (y : ℝ) :
    HasHeckeHeight F (heckeOrdinateCharacter F ω y) (-y) := by
  intro g
  rw [heckeNormOneRestriction_ordinateCharacter]
  change ((normOneEulerCharacter F ω g * Circle.exp (y *
    (ideleClassLogNorm F g).toAdd) : Circle) : ℂ) = _
  rw [Circle.coe_mul, Circle.coe_exp]
  change _ * Complex.exp (((y * Real.log (ideleClassNorm F g) : ℝ) : ℂ) * Complex.I) =
    _ * Complex.exp (-(((-y : ℝ) : ℂ) * Complex.I) * (Real.log (ideleClassNorm F g) : ℂ))
  rw [Complex.ofReal_mul, Complex.ofReal_neg]
  apply congrArg (fun z ↦ (normOneEulerCharacter F ω g : ℂ) * Complex.exp z)
  ring

/-- The norm, real radial, complex radial, and complex angular directions
that measure the size of a spectral character. -/
abbrev HeckeFrequencyDirection :=
  Option (RealPlace F ⊕ (ComplexPlace F ⊕ ComplexPlace F))

def heckeFrequencyFlow (j : HeckeFrequencyDirection F) :
    Multiplicative ℝ →ₜ* IdeleClass F :=
  match j with
  | none => manuscriptNormFlow F
  | some (.inl v) => manuscriptArchFlow F (Pi.single v 1, 0)
  | some (.inr (.inl v)) => manuscriptArchFlow F (0, Pi.single v ((1 : ℂ) / 2))
  | some (.inr (.inr v)) => manuscriptArchFlow F (0, Pi.single v Complex.I)

private theorem norm_eq_abs_im_of_re_zero {z : ℂ} (h : z.re = 0) : ‖z‖ = |z.im| := by
  calc
    ‖z‖ = ‖(z.im : ℂ) * Complex.I‖ := by
      congr 1
      have h' := Complex.re_add_im z
      rw [h, Complex.ofReal_zero, zero_add] at h'
      exact h'.symm
    _ = _ := by rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]

variable (χ : PontryaginDual (IdeleClass F))
variable (S : Finset (HeightOneSpectrum (𝓞 F)))
variable (hs : Surjective (sIdeleClassInclusion F S))
variable (hu : globalNormOneCharacter F (heckeNormOneRestriction F χ) ∈
  (sUnramified F S : Set (QuasiCharacter (IdeleClass F))))

/-- Bounds on all the spectral directions are exactly the joint Hecke box
used in the uniform count. -/
theorem heckeFrequencyFlow_box_iff (t T : ℝ) (ht : HasHeckeHeight F χ t) :
    (∀ j : HeckeFrequencyDirection F,
      |(mellinOrbitSlope (G := IdeleClass F) (mellinClassModulus F) 0 χ
        (heckeFrequencyFlow F j)).im| ≤ T) ↔
      |t| ≤ T ∧ manuscriptHeckeArchParametersInBox F χ S hs hu t T := by
  let ω := sLocalNormOneCharacterOfGlobal F (heckeNormOneRestriction F χ) S hs hu
  have hn : |(mellinOrbitSlope (G := IdeleClass F) (mellinClassModulus F) 0 χ
      (heckeFrequencyFlow F none)).im| = |t| := by
    rw [heckeFrequencyFlow, manuscriptHecke_normSlope F χ t ht]
    simp [Complex.mul_im]
  have hr (v : RealPlace F) :
      |(mellinOrbitSlope (G := IdeleClass F) (mellinClassModulus F) 0 χ
        (heckeFrequencyFlow F (some (.inl v)))).im| =
        ‖-(t : ℂ) * Complex.I + (sLocalRealArchParameters F S ω v).1‖ := by
    rw [heckeFrequencyFlow, manuscriptHecke_realSlope F χ S hs hu t ht]
    simp only [Complex.ofReal_zero, zero_sub, neg_mul]
    symm
    apply norm_eq_abs_im_of_re_zero
    simp [Complex.add_re, Complex.mul_re, sLocalRealArchParameters_re, ω]
  have hc (v : ComplexPlace F) :
      |(mellinOrbitSlope (G := IdeleClass F) (mellinClassModulus F) 0 χ
        (heckeFrequencyFlow F (some (.inr (.inl v))))).im| =
        ‖-(t : ℂ) * Complex.I + (sLocalComplexArchParameters F S ω v).1‖ := by
    rw [heckeFrequencyFlow, manuscriptHecke_complexRadialSlope F χ S hs hu t ht]
    simp only [Complex.ofReal_zero, zero_sub, neg_mul]
    symm
    apply norm_eq_abs_im_of_re_zero
    simp [Complex.add_re, Complex.mul_re, sLocalComplexArchParameters_re, ω]
  have ha (v : ComplexPlace F) :
      |(mellinOrbitSlope (G := IdeleClass F) (mellinClassModulus F) 0 χ
        (heckeFrequencyFlow F (some (.inr (.inr v))))).im| =
        |((sLocalComplexArchParameters F S ω v).2 : ℝ)| := by
    rw [heckeFrequencyFlow, manuscriptHecke_complexAngularSlope F χ S hs hu t ht]
    simp [Complex.mul_im, ω]
  constructor
  · intro h
    exact ⟨hn ▸ h none, fun v ↦ hr v ▸ h (some (.inl v)),
      fun v ↦ hc v ▸ h (some (.inr (.inl v))), fun v ↦ ha v ▸ h (some (.inr (.inr v)))⟩
  · rintro ⟨ht', hr', hc', ha'⟩ j
    rcases j with _ | (v | (v | v))
    · rwa [hn]
    · rw [hr]; exact hr' v
    · rw [hc]; exact hc' v
    · rw [ha]; exact ha' v

end
end Masullo
