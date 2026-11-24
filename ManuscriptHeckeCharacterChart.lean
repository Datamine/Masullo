import GlobalHeckeEulerComparison
import ModulatedSobolevQuasiCharacters

open Filter Function Ideal IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical NumberField

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]
private abbrev K := normOneIdeleClass F
private abbrev Place := HeightOneSpectrum (𝓞 F)

/-- The restriction of an actual unitary idele-class character to norm one. -/
def heckeNormOneRestriction (χ : PontryaginDual (IdeleClass F)) : PontryaginDual (K F) where
  toMonoidHom := χ.toMonoidHom.comp (K F).subtype
  continuous_toFun := χ.continuous.comp continuous_subtype_val

private abbrev iHeight (t : ℝ) : ℂ := (t : ℂ) * Complex.I

/-- The parameter convention in Proposition 3.2.1.3. The character is its
norm-one extension times the imaginary power with exponent (-it). -/
def HasHeckeHeight (χ : PontryaginDual (IdeleClass F)) (t : ℝ) : Prop :=
  ∀ g : IdeleClass F, (χ g : ℂ) =
    (normOneEulerCharacter F (heckeNormOneRestriction F χ) g : ℂ) *
      Complex.exp (-iHeight t * (Real.log (ideleClassNorm F g) : ℂ))

/-- Every unitary idele-class character has a unique height in this convention. -/
theorem existsUnique_heckeHeight (χ : PontryaginDual (IdeleClass F)) :
    ∃! t : ℝ, HasHeckeHeight F χ t := by
  let c : Multiplicative ℝ →ₜ* ℂ :=
    { toMonoidHom := Circle.coeHom.comp (χ.toMonoidHom.comp (ideleClassExpSection F))
      continuous_toFun := continuous_subtype_val.comp
        (χ.continuous.comp (ideleClassExpSection_continuous F)) }
  obtain ⟨a, ha, huniq⟩ := existsUnique_logComplexExponential c
  have hre : a.re = 0 := by
    have h := congrArg norm (ha 1)
    change ‖(χ (ideleClassExpSection F (Multiplicative.ofAdd 1)) : ℂ)‖ =
      ‖Complex.exp (a * ((1 : ℝ) : ℂ))‖ at h
    rw [Circle.norm_coe, Complex.ofReal_one, mul_one, Complex.norm_exp, ← Real.exp_zero,
      Real.exp_eq_exp] at h
    exact h.symm
  have hparam : -iHeight (-a.im) = a := by
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, hre]
  have hpart (g : IdeleClass F) :
      g = (ideleClassNormOnePart F g).val * ideleClassExpSection F (ideleClassLogNorm F g) :=
    ((ideleClassSplit F).symm_apply_apply g).symm
  have hnorm (x : ℝ) :
      normOneEulerCharacter F (heckeNormOneRestriction F χ) (ideleClassExpSection F (Multiplicative.ofAdd x)) = 1 := by
    let g := ideleClassExpSection F (Multiplicative.ofAdd x)
    have h : ideleClassNormOnePart F g = 1 := by
      apply Subtype.ext
      change g / ideleClassExpSection F (ideleClassLogNorm F g) = (1 : K F).val
      rw [show ideleClassLogNorm F g = Multiplicative.ofAdd x from ideleClassLogNorm_expSection F _,
        Subgroup.coe_one]
      exact div_self' g
    change heckeNormOneRestriction F χ (ideleClassNormOnePart F g) = 1
    rw [h, map_one]
  refine ⟨-a.im, fun g ↦ ?_, fun t ht ↦ ?_⟩
  · have hg := congrArg (fun x : IdeleClass F ↦ (χ x : ℂ)) (hpart g)
    rw [map_mul, Circle.coe_mul] at hg
    change (χ g : ℂ) = (normOneEulerCharacter F (heckeNormOneRestriction F χ) g : ℂ) *
      c (Multiplicative.ofAdd (Real.log (ideleClassNorm F g))) at hg
    rw [hg, ha, hparam]
  · have he : -iHeight t = a := by
      apply huniq
      intro x
      have h := ht (ideleClassExpSection F (Multiplicative.ofAdd x))
      rw [hnorm, Circle.coe_one, one_mul, ideleClassNorm_expSection, Real.log_exp] at h
      exact h
    have hi := congrArg Complex.im he
    simp [Complex.mul_im] at hi
    linarith

/-- On the trivial norm-one component the height is exactly the unique
parameter of the pure norm power specified in clause (2). -/
theorem existsUnique_heckePureNormTwist (χ : PontryaginDual (IdeleClass F))
    (hχ : heckeNormOneRestriction F χ = 1) :
    ∃! t : ℝ, ∀ g : IdeleClass F, (χ g : ℂ) =
      (ideleClassNorm F g : ℂ) ^ (-iHeight t) := by
  have h (t : ℝ) : HasHeckeHeight F χ t ↔ ∀ g : IdeleClass F, (χ g : ℂ) =
      (ideleClassNorm F g : ℂ) ^ (-iHeight t) := by
    unfold HasHeckeHeight
    rw [hχ]
    apply forall_congr'
    intro g
    have hunit : normOneEulerCharacter F 1 g = 1 := rfl
    rw [hunit, Circle.coe_one, one_mul, Complex.cpow_def_of_ne_zero
      (Complex.ofReal_ne_zero.mpr (ideleClassNorm_pos F g).ne'),
      ← Complex.ofReal_log (ideleClassNorm_pos F g).le, mul_comm]
  obtain ⟨t, ht, huniq⟩ := existsUnique_heckeHeight F χ
  exact ⟨t, (h t).mp ht, fun t' ht' ↦ huniq t' ((h t').mpr ht')⟩

@[simp] theorem heckeNormOneRestriction_inv (χ : PontryaginDual (IdeleClass F)) :
    heckeNormOneRestriction F χ⁻¹ = (heckeNormOneRestriction F χ)⁻¹ := by
  ext x
  rfl

private theorem normOneEulerCharacter_inv_apply (ω : PontryaginDual (K F)) (g : IdeleClass F) :
    normOneEulerCharacter F ω⁻¹ g = (normOneEulerCharacter F ω g)⁻¹ := rfl

theorem HasHeckeHeight.inv {χ : PontryaginDual (IdeleClass F)} {t : ℝ}
    (ht : HasHeckeHeight F χ t) : HasHeckeHeight F χ⁻¹ (-t) := by
  intro g
  change (((χ g)⁻¹ : Circle) : ℂ) = _
  rw [Circle.coe_inv, ht g, mul_inv, heckeNormOneRestriction_inv, normOneEulerCharacter_inv_apply,
    Circle.coe_inv, ← Complex.exp_neg]
  congr 2
  simp only [iHeight, Complex.ofReal_neg]
  ring

private theorem finiteEulerFactor_heckeHeight (χ : PontryaginDual (IdeleClass F))
    {t : ℝ} (ht : HasHeckeHeight F χ t) (v : Place F) (s : ℂ) :
    heckeEulerFactor F (heckeEulerCoefficient F χ (chosenFiniteUniformizer F)) v s =
      heckeEulerFactor F (heckeEulerCoefficient F
        (normOneEulerCharacter F (heckeNormOneRestriction F χ)) (chosenFiniteUniformizer F))
        v (s - iHeight t) := by
  let χ₀ := normOneEulerCharacter F (heckeNormOneRestriction F χ)
  have hunit (u : (v.adicCompletion F)ˣ) (hu : ‖(u : v.adicCompletion F)‖ = 1) :
      χ (ideleClassMap F (singleFiniteIdele F v u)) =
        χ₀ (ideleClassMap F (singleFiniteIdele F v u)) := by
    apply Circle.coe_injective
    rw [ht, ideleClassNorm_mk, singleFiniteIdele_norm, hu, Real.log_one,
      Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one]
  have hram : unramifiedFiniteCharacter F χ v ↔ unramifiedFiniteCharacter F χ₀ v := by
    constructor <;> intro h u hu
    · rw [← hunit u hu]
      exact h u hu
    · rw [hunit u hu]
      exact h u hu
  unfold heckeEulerFactor heckeEulerCoefficient
  change (1 - (if unramifiedFiniteCharacter F χ v then _ else 0) * _)⁻¹ =
    (1 - (if unramifiedFiniteCharacter F χ₀ v then _ else 0) * _)⁻¹
  rw [hram]
  split_ifs
  · rw [ht, ideleClassNorm_mk, singleFiniteIdele_norm,
      norm_finiteUniformizer F v _ (chosenFiniteUniformizer_spec F v), Real.log_inv]
    have hq : (v.asIdeal.absNorm : ℂ) ≠ 0 := by
      exact_mod_cast (zero_lt_one.trans (NumberField.HeightOneSpectrum.one_lt_absNorm v)).ne'
    rw [Complex.cpow_def_of_ne_zero hq, Complex.cpow_def_of_ne_zero hq]
    simp only [← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg _),
      Complex.ofReal_neg, mul_assoc, ← Complex.exp_add]
    congr 4
    ring
  · simp

/-- The finite Euler product in the original parameter of a unitary
idele-class character. -/
def manuscriptFiniteHeckeEuler (χ : PontryaginDual (IdeleClass F)) (s : ℂ) : ℂ :=
  ∏' v, heckeEulerFactor F (heckeEulerCoefficient F χ (chosenFiniteUniformizer F)) v s

theorem manuscriptFiniteHeckeEuler_shift (χ : PontryaginDual (IdeleClass F))
    {t : ℝ} (ht : HasHeckeHeight F χ t) (s : ℂ) :
    manuscriptFiniteHeckeEuler F χ s =
      globalFiniteHeckeEuler F (heckeNormOneRestriction F χ) (s - (t : ℂ) * Complex.I) := by
  unfold manuscriptFiniteHeckeEuler globalFiniteHeckeEuler
  simp_rw [finiteEulerFactor_heckeHeight F χ ht]

end

end Masullo
