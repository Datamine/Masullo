import AdelicTheta
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Algebra.ContinuousMonoidHom

open MeasureTheory
open scoped NumberField

noncomputable section

namespace Masullo

variable (F : Type*) [Field F] [NumberField F]

/-- The quasi-characters of the actual idele class group in §3.1.1. -/
abbrev IdeleQuasiCharacter := IdeleClass F →ₜ* ℂˣ

/-- The unitary condition used to choose a base point for a family of twists. -/
def IsUnitary (χ : IdeleQuasiCharacter F) : Prop :=
  ∀ g, ‖(χ g : ℂ)‖ = 1

/-- The norm twist on the positive idele class modulus. The exponential
expression fixes the real logarithm and hence the branch of the power. -/
def ideleNormPower (s : ℂ) (g : IdeleClass F) : ℂ :=
  Complex.exp (s * (Real.log (ideleClassNorm F g) : ℂ))

@[simp] theorem ideleNormPower_one (s : ℂ) : ideleNormPower F s 1 = 1 := by
  simp [ideleNormPower]

theorem ideleNormPower_ne_zero (s : ℂ) (g : IdeleClass F) :
    ideleNormPower F s g ≠ 0 := Complex.exp_ne_zero _

theorem ideleNormPower_mul (s : ℂ) (g h : IdeleClass F) :
    ideleNormPower F s (g * h) = ideleNormPower F s g * ideleNormPower F s h := by
  simp [ideleNormPower, Real.log_mul (ideleClassNorm_pos F g).ne'
    (ideleClassNorm_pos F h).ne', mul_add, Complex.exp_add]

theorem ideleNormPower_continuous (s : ℂ) : Continuous (ideleNormPower F s) := by
  unfold ideleNormPower
  have hlog : Continuous (fun g => Real.log (ideleClassNorm F g)) := by
    apply continuous_iff_continuousAt.mpr
    intro g
    exact (Real.continuousAt_log (ideleClassNorm_pos F g).ne').comp
      (ideleClassNorm_continuous F).continuousAt
  exact Complex.continuous_exp.comp
    (continuous_const.mul (Complex.continuous_ofReal.comp hlog))

/-- Multiplication by the norm power gives the quasi-character χ |·|ˢ. -/
def ideleNormTwist (χ : IdeleQuasiCharacter F) (s : ℂ) : IdeleQuasiCharacter F where
  toFun g := χ g * Units.mk0 (ideleNormPower F s g) (ideleNormPower_ne_zero F s g)
  map_one' := by ext; simp
  map_mul' g h := by
    apply Units.ext
    simp [ideleNormPower_mul, mul_assoc, mul_left_comm, mul_comm]
  continuous_toFun := by
    apply (map_continuous χ).mul
    apply Units.continuous_iff.mpr
    constructor
    · exact ideleNormPower_continuous F s
    · exact (ideleNormPower_continuous F s).inv₀ (ideleNormPower_ne_zero F s)

/-- The real part of the parameter is the exponent of the modulus for a unitary
base character, giving the norm identity underlying Definition 3.1.1.1. -/
theorem norm_ideleNormTwist (χ : IdeleQuasiCharacter F) (hχ : IsUnitary F χ)
    (s : ℂ) (g : IdeleClass F) :
    ‖(ideleNormTwist F χ s g : ℂ)‖ = (ideleClassNorm F g) ^ s.re := by
  change ‖(χ g : ℂ) * ideleNormPower F s g‖ = _
  rw [norm_mul, hχ g, one_mul, ideleNormPower, Complex.norm_exp]
  rw [Real.rpow_def_of_pos (ideleClassNorm_pos F g)]
  simp [Complex.mul_re, mul_comm]

/-- Restriction to the norm-one subgroup in equation (3.1.1.1). -/
def restrictToNormOne (χ : IdeleQuasiCharacter F) : normOneIdeleClass F →ₜ* ℂˣ where
  toMonoidHom := χ.toMonoidHom.comp (normOneIdeleClass F).subtype
  continuous_toFun := (map_continuous χ).comp continuous_subtype_val

/-- A character of the norm-one subgroup lifts via the continuous splitting. -/
def extendFromNormOne (χ : normOneIdeleClass F →ₜ* ℂˣ) : IdeleQuasiCharacter F where
  toMonoidHom := χ.toMonoidHom.comp
    ((MonoidHom.fst (normOneIdeleClass F) (Multiplicative ℝ)).comp (ideleClassSplit F).toMonoidHom)
  continuous_toFun :=
    (map_continuous χ).comp (continuous_fst.comp (ideleClassSplitHomeomorph F).continuous)

theorem restrictToNormOne_extend (χ : normOneIdeleClass F →ₜ* ℂˣ) :
    restrictToNormOne F (extendFromNormOne F χ) = χ := by
  ext u
  change (χ (ideleClassNormOnePart F u.val) : ℂ) = (χ u : ℂ)
  have hp : ideleClassNormOnePart F u.val = u := by
    apply Subtype.ext
    change u.val / ideleClassExpSection F (ideleClassLogNorm F u.val) = u.val
    have h : ideleClassNorm F u.val = 1 := u.property
    have hu : ideleClassLogNorm F u.val = 1 := by
      change Multiplicative.ofAdd (Real.log (ideleClassNorm F u.val)) = 1
      simp [h]
    simp [hu]
  rw [hp]

theorem restrictToNormOne_surjective : Function.Surjective (restrictToNormOne F) :=
  fun χ => ⟨extendFromNormOne F χ, restrictToNormOne_extend F χ⟩

theorem restrictToNormOne_twist (χ : IdeleQuasiCharacter F) (s : ℂ) :
    restrictToNormOne F (ideleNormTwist F χ s) = restrictToNormOne F χ := by
  ext u
  have h : ideleClassNorm F u.val = 1 := u.property
  change (χ u.val : ℂ) * ideleNormPower F s u.val = χ u.val
  simp [ideleNormPower, h]

/-- Restrict a quasi-character to the chosen section of the modulus. -/
def restrictToNormRay (χ : IdeleQuasiCharacter F) : Multiplicative ℝ →ₜ* ℂˣ where
  toMonoidHom := χ.toMonoidHom.comp (ideleClassExpSection F)
  continuous_toFun := (map_continuous χ).comp (ideleClassExpSection_continuous F)

/-- The two restrictions jointly determine a quasi-character. This is the
group decomposition underlying the character fibers in §3.1.1. -/
theorem quasiCharacter_eq_of_restrictions {χ ψ : IdeleQuasiCharacter F}
    (h₁ : restrictToNormOne F χ = restrictToNormOne F ψ)
    (h₂ : restrictToNormRay F χ = restrictToNormRay F ψ) : χ = ψ := by
  ext g
  let u := ideleClassNormOnePart F g
  let t := ideleClassLogNorm F g
  have hg : u.val * ideleClassExpSection F t = g := (ideleClassSplit F).left_inv g
  have hu : χ u.val = ψ u.val := DFunLike.congr_fun h₁ u
  have ht : χ (ideleClassExpSection F t) = ψ (ideleClassExpSection F t) := DFunLike.congr_fun h₂ t
  have he : χ g = ψ g := by
    rw [← hg, map_mul, map_mul, hu, ht]
  exact congrArg Units.val he

/-- The global zeta integral on ideles with the chosen multiplicative
measure. Its convergence and continuation are separate assertions. -/
def idelicZetaIntegral (μ : @Measure (Idele F) (borel (Idele F)))
    (f : Adeles F → ℂ) (χ : IdeleQuasiCharacter F) (s : ℂ) : ℂ :=
  letI := borel (Idele F)
  ∫ g, f g.val * (ideleNormTwist F χ s (ideleClassMap F g) : ℂ) ∂μ

/-- The class-group expression in Chapter 3 after unfolding the theta sum. -/
def thetaZetaIntegral (μ : @Measure (IdeleClass F) (borel (IdeleClass F)))
    (f : Adeles F → ℂ) (χ : IdeleQuasiCharacter F) (s : ℂ) : ℂ :=
  letI := borel (IdeleClass F)
  ∫ g, adelicTheta F f g * (ideleNormTwist F χ s g : ℂ) ∂μ

end Masullo
