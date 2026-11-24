import ComplexSupportedWeilEigen
import SchwartzDilationContinuity
import SchwartzReflexivity
import StrongDualBoundedSeries
import Mathlib.MeasureTheory.Group.Prod

open Bornology Filter Function MeasureTheory Set Topology WithSeminorms
open scoped Classical NNReal SchwartzMap

namespace Masullo

noncomputable section

private abbrev Tests := 𝓢(ℂ, ℂ)
attribute [local instance] complexZeta_circleMeasurable complexZeta_circleBorel

private theorem exists_angularPettis (μ : Measure Circle) [IsFiniteMeasure μ]
    {f : Circle → Tests} (hf : Continuous f) :
    ∃ g : Tests, HasPositivePettisIntegral μ f g := by
  have hi (ℓ : StrongDual ℂ Tests) : Integrable (ℓ ∘ f) μ :=
    (ℓ.continuous.comp hf).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let L := positiveWeakPettisIntegral μ f hi
  let B : {B : Set Tests // IsVonNBounded ℂ B} :=
    ⟨range f, (isCompact_range hf).isVonNBounded ℂ⟩
  have hL (ℓ : StrongDual ℂ Tests) : ‖L ℓ‖ ≤ μ.real univ * strongDualBoundedSeminorm B ℓ := by
    change ‖∫ u, ℓ (f u) ∂μ‖ ≤ _
    rw [mul_comm]
    exact norm_integral_le_of_norm_le_const
      (.of_forall fun u => strongDualBoundedSeminorm_dom B ℓ (mem_range_self u))
  have hc : Continuous L := by
    apply continuous_of_isBounded (strongDual_withBoundedSeminorms (E := Tests))
      (norm_withSeminorms ℂ ℂ) L
    intro i
    refine ⟨{B}, (μ.real univ).toNNReal, fun ℓ => ?_⟩
    rw [Finset.sup_singleton]
    change ‖L ℓ‖ ≤ (μ.real univ).toNNReal • strongDualBoundedSeminorm B ℓ
    rw [NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ measureReal_nonneg]
    exact hL ℓ
  obtain ⟨e, he⟩ := classicalSchwartz_reflexive ℂ
  obtain ⟨g, hg⟩ := e.surjective (⟨L, hc⟩ : StrongDual ℂ (StrongDual ℂ Tests))
  exact ⟨g, fun ℓ => ⟨hi ℓ, (he g ℓ).symm.trans (DFunLike.congr_fun hg ℓ)⟩⟩

private def rotation (u : Circle) : ℂ ≃L[ℝ] ℂ :=
  (ContinuousLinearEquiv.unitsEquivAut ℂ (Circle.toUnits u)).restrictScalars ℝ

private theorem rotation_apply (u : Circle) (x : ℂ) :
    rotation u x = x * (u : ℂ) := rfl

private theorem rotation_continuous :
    Continuous (fun u : Circle => (rotation u).toContinuousLinearMap) := by
  have h : (fun u : Circle => (rotation u).toContinuousLinearMap) =
      fun u : Circle => (ContinuousLinearMap.mul ℝ ℂ).flip (u : ℂ) := by
    funext u
    ext x
    exact rotation_apply u x
  rw [h]
  exact (ContinuousLinearMap.mul ℝ ℂ).flip.continuous.comp continuous_subtype_val

private theorem rotation_continuous_symm :
    Continuous (fun u : Circle => (rotation u).symm.toContinuousLinearMap) := by
  have h : (fun u : Circle => (rotation u).symm.toContinuousLinearMap) =
      fun u : Circle => (rotation u⁻¹).toContinuousLinearMap := by
    funext u
    ext x
    rfl
  rw [h]
  exact rotation_continuous.comp continuous_inv

private def angularOrbit (m : ℤ) (f : Tests) (u : Circle) : Tests :=
  ((u : ℂ) ^ m) • SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (rotation u) f

private theorem angularOrbit_continuous (m : ℤ) (f : Tests) : Continuous (angularOrbit m f) := by
  have h : Continuous (fun u : Circle => (u : ℂ) ^ m) := by
    exact (continuous_subtype_val : Continuous (fun u : Circle => (u : ℂ))).zpow₀ m
      (fun u => Or.inl (Circle.coe_ne_zero u))
  exact h.smul (continuous_schwartz_linearPullback rotation rotation_continuous rotation_continuous_symm f)

private theorem angularOrbit_apply (m : ℤ) (f : Tests) (u : Circle) (x : ℂ) :
    angularOrbit m f u x = (u : ℂ) ^ m * f (x * (u : ℂ)) := rfl

/-- The angular average is a Schwartz function and can be evaluated by
an arbitrary continuous Schwartz functional before or after integration. -/
theorem exists_complexSchwartz_angularAverage (μ : Measure Circle) [IsFiniteMeasure μ]
    (m : ℤ) (f : Tests) :
    ∃ g : Tests, (∀ x, g x = ∫ u : Circle, (u : ℂ) ^ m * f (x * (u : ℂ)) ∂μ) ∧
      ∀ T : StrongDual ℂ Tests, T g = ∫ u : Circle, T (angularOrbit m f u) ∂μ := by
  obtain ⟨g, hg⟩ := exists_angularPettis μ (angularOrbit_continuous m f)
  refine ⟨g, ?_, fun T => (hg T).2⟩
  intro x
  exact (hg ((BoundedContinuousFunction.evalCLM ℂ x).comp
    (SchwartzMap.toBoundedContinuousFunctionCLM ℂ ℂ ℂ))).2

private theorem complexWeilEigen_angularOrbit_eval (T : StrongDual ℂ Tests)
    (m : ℤ) (z : ℂ)
    (hT : ∀ u f, T (archSchwartzDilation u f) = complexArchUnitWeight m z u * T f)
    (f : Tests) (u : Circle) :
    T (angularOrbit m f u) = T f := by
  have he : SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (rotation u) f =
      archSchwartzDilation (Circle.toUnits u)⁻¹ f := by
    ext x
    rw [archSchwartzDilation_apply, inv_inv]
    rfl
  have hw : complexArchUnitWeight m z (Circle.toUnits u)⁻¹ = (u : ℂ)⁻¹ ^ m := by
    change ((‖(u : ℂ)⁻¹‖ ^ 2 : ℝ) : ℂ) ^ z * ((u : ℂ)⁻¹ / (‖(u : ℂ)⁻¹‖ : ℂ)) ^ m = _
    simp only [norm_inv, Circle.norm_coe, inv_one, one_pow, Complex.ofReal_one, Complex.one_cpow,
      div_one, one_mul]
  unfold angularOrbit
  rw [he, map_smul, hT, hw, smul_eq_mul, ← mul_assoc, ← mul_zpow,
    mul_inv_cancel₀ (Circle.coe_ne_zero u), one_zpow, one_mul]

/-- The selected angular Fourier mode has the same pairing as the original
test against a complex local eigendistribution. -/
theorem complexWeilEigen_eq_angularAverage (μ : Measure Circle) [IsProbabilityMeasure μ]
    (T : StrongDual ℂ Tests) (m : ℤ) (z : ℂ)
    (hT : ∀ u f, T (archSchwartzDilation u f) = complexArchUnitWeight m z u * T f)
    (f g : Tests) (hg : ∀ x, g x = ∫ u : Circle, (u : ℂ) ^ m * f (x * (u : ℂ)) ∂μ) :
    T g = T f := by
  obtain ⟨g', hg', he⟩ := exists_complexSchwartz_angularAverage μ m f
  have h : g = g' := by ext x; exact (hg x).trans (hg' x).symm
  rw [h, he]
  simp_rw [complexWeilEigen_angularOrbit_eval T m z hT f]
  simp

end
end Masullo
