import ComplexPuncturedWeilEigen

open Filter Topology
open scoped SchwartzMap

namespace Masullo

noncomputable section

/-- The angular Gaussian at the manuscript's scalar, with the conjugation
chosen to cancel the weight of the quasi-character. -/
def correctedComplexWeilReference (m : ℤ) : 𝓢(ℂ, ℂ) :=
  (2 : ℂ)⁻¹ • (complexGammaNormalized_distribution m).choose

theorem correctedComplexWeilReference_apply (m : ℤ) (x : ℂ) :
    correctedComplexWeilReference m x =
      (x ^ (-m).toNat * star x ^ m.toNat) *
        ((2 * Real.pi : ℂ)⁻¹ * (Real.exp (-(2 * Real.pi) * ‖x‖ ^ 2) : ℂ)) := by
  change (2 : ℂ)⁻¹ * (complexGammaNormalized_distribution m).choose x = _
  rw [(complexGammaNormalized_distribution m).choose_spec.choose_spec.1 x, mul_inv]
  ring

/-- As printed in (3.4.3.5)–(3.4.3.6), the Gaussian has the angular
frequency of the character itself. -/
def printedComplexWeilReference (m : ℤ) : 𝓢(ℂ, ℂ) := correctedComplexWeilReference (-m)

theorem printedComplexWeilReference_weightOne_vanishes
    (z : ℂ) (T : complexWeilEigenspace 1 z) :
    T.val (printedComplexWeilReference 1) = 0 := by
  let u := Units.mk0 Complex.I Complex.I_ne_zero
  let f := printedComplexWeilReference 1
  have hf (x : ℂ) : f x =
      x * ((2 * Real.pi : ℂ)⁻¹ * (Real.exp (-(2 * Real.pi) * ‖x‖ ^ 2) : ℂ)) := by
    simpa [f, printedComplexWeilReference] using correctedComplexWeilReference_apply (-1) x
  have hu : (u⁻¹ : ℂˣ).val = -Complex.I := Complex.inv_I
  have hD : archSchwartzDilation u f = (-Complex.I) • f := by
    ext x
    change f (x * (u⁻¹ : ℂˣ).val) = (-Complex.I) * f x
    rw [hf, hf, hu, norm_mul, norm_neg, Complex.norm_I, mul_one]
    ring
  have hw : complexArchUnitWeight 1 z u = Complex.I := by
    change ((‖Complex.I‖ ^ 2 : ℝ) : ℂ) ^ z *
      (Complex.I / (‖Complex.I‖ : ℂ)) ^ (1 : ℤ) = _
    simp
  have h := T.property u f
  rw [hD, hw, map_smul, smul_eq_mul] at h
  change T.val f = 0
  have he : (-2 * Complex.I : ℂ) * T.val f = 0 := by linear_combination h
  exact (mul_eq_zero.mp he).resolve_left (mul_ne_zero (by norm_num) Complex.I_ne_zero)

/-- The entire normalized family for the corrected angular Gaussian. -/
def correctedComplexWeilNormalizedFamily (m : ℤ) (z : ℂ) : StrongDual ℂ 𝓢(ℂ, ℂ) :=
  (2 : ℂ) • complexWeilNormalizedFamily m z

theorem correctedComplexWeilNormalizedFamily_reference (m : ℤ) (z : ℂ) :
    correctedComplexWeilNormalizedFamily m z (correctedComplexWeilReference m) = 1 := by
  change (2 : ℂ) * complexWeilNormalizedFamily m z
    ((2 : ℂ)⁻¹ • (complexGammaNormalized_distribution m).choose) = 1
  have h : complexWeilNormalizedFamily m z (complexGammaNormalized_distribution m).choose = 1 :=
    (complexGammaNormalized_distribution m).choose_spec.choose_spec.2.2.1 z
  rw [map_smul, smul_eq_mul, h, mul_one, mul_inv_cancel₀ (by norm_num : (2 : ℂ) ≠ 0)]

theorem correctedComplexWeilNormalizedFamily_factor (m : ℤ) (c : ℂ) :
    complexArchimedeanZetaContinuedCLM complexTamagawaAngularMeasure m =ᶠ[𝓝[≠] c]
      fun z => (Complex.Gammaℂ (z + (m.natAbs : ℂ) / 2) / 2) •
        correctedComplexWeilNormalizedFamily m z := by
  filter_upwards [(complexGammaNormalized_distribution m).choose_spec.choose_spec.2.2.2 c]
    with z hz
  rw [hz, correctedComplexWeilNormalizedFamily, smul_smul, div_mul_cancel₀ _ (by norm_num : (2 : ℂ) ≠ 0)]
  rfl

theorem correctedComplexWeilNormalizedFamily_holomorphic (m : ℤ) :
    Differentiable ℂ (correctedComplexWeilNormalizedFamily m) := by
  let M := (2 : ℂ) • ContinuousLinearMap.id ℂ (StrongDual ℂ 𝓢(ℂ, ℂ))
  change Differentiable ℂ (M ∘ complexWeilNormalizedFamily m)
  intro z
  obtain ⟨D, hD⟩ := (complexGammaNormalized_distribution m).choose_spec.choose_spec.2.1 z
  refine ⟨M.comp D, HasFDerivAt.of_isLittleOTVS ?_⟩
  simpa only [complexWeilNormalizedFamily, Function.comp_def, ContinuousLinearMap.comp_apply, map_sub]
    using M.isBigOTVS_comp.trans_isLittleOTVS hD.isLittleOTVS

end
end Masullo
