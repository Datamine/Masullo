import FiniteGaussTest
import CompactBruhatFourierStages

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped NumberField Classical

namespace Masullo
noncomputable section

variable (F : Type*) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

local notation "K" => v.adicCompletion F
local notation "U" => finitePlaceIntegralUnits F v

/-- The standard test on the unit shell selects exactly the restriction of
the character to local units, at every complex exponent. -/
theorem finiteGaussTest_mellin_eq_if_unitCharacter
    [MeasurableSpace Kˣ] [BorelSpace Kˣ] (μ : Measure Kˣ) [μ.IsHaarMeasure]
    (χ ψ : Kˣ →ₜ* Circle) (z : ℂ) :
    finiteZetaIntegral F v μ ψ (finiteGaussTest F v χ) z =
      if ∀ u ∈ U, χ u = ψ u then (μ.real U : ℂ) else 0 := by
  classical
  let θ : PontryaginDual Kˣ := χ⁻¹ * ψ
  let f := (U).indicator (fun _ => (1 : ℂ))
  have hU (u : Kˣ) : u ∈ U ↔ ‖u.val‖ = 1 := by
    rw [← finiteZetaShell_zero, finiteZetaShell, mem_ofPred_eq, neg_zero, zpow_zero]
  have hUm : MeasurableSet U := by
    rw [← finiteZetaShell_zero]
    exact (finiteZetaShell_closed F v 0).measurableSet
  have he (u : Kˣ) :
      (finiteGaussTest F v χ).val u.val * (ψ u : ℂ) * finiteZetaWeight F v z u =
        f u * (θ u : ℂ) := by
    rw [finiteGaussTest_apply_units F v χ u]
    change _ = f u * (((χ u)⁻¹ * ψ u : Circle) : ℂ)
    by_cases hu : u ∈ U
    · have hn := (hU u).mp hu
      simp [hn, f, hu, Circle.coe_mul, finiteZetaWeight]
    · rw [ite_eq_right (fun hn => hu ((hU u).mpr hn))]
      simp [f, hu]
  unfold finiteZetaIntegral
  simp_rw [he]
  by_cases hc : ∀ u ∈ U, χ u = ψ u
  · rw [ite_eq_left hc]
    have ht (u : Kˣ) : f u * (θ u : ℂ) = f u := by
      by_cases hu : u ∈ U
      · change f u * (((χ u)⁻¹ * ψ u : Circle) : ℂ) = f u
        rw [hc u hu, inv_mul_cancel, Circle.coe_one, mul_one]
      · simp [f, hu]
    simp_rw [ht]
    rw [show f = (U).indicator (fun _ => (1 : ℂ)) from rfl, integral_indicator hUm, setIntegral_const]
    simp [Complex.real_smul]
  · rw [ite_eq_right hc]
    push Not at hc
    obtain ⟨u, hu, hneq⟩ := hc
    have hθ : θ u ≠ 1 := by
      change (χ u)⁻¹ * ψ u ≠ 1
      exact fun h => hneq (inv_mul_eq_one.mp h)
    apply integral_character_eq_zero_of_invariant μ θ f u ?_ hθ
    intro x
    have hmem : u * x ∈ U ↔ x ∈ U := by
      rw [hU, hU, Units.val_mul, norm_mul, (hU u).mp hu, one_mul]
    by_cases hx : x ∈ U
    · simp [f, hx, hmem.mpr hx]
    · have hx' : u * x ∉ U := fun h => hx (hmem.mp h)
      exact (indicator_of_notMem hx' _).trans (indicator_of_notMem hx _).symm

/-- The ramified standard test is nonzero at exponent zero as well as on the
positive half-plane. -/
theorem finiteGaussTest_mellin_ne_zero_at_zero
    [MeasurableSpace Kˣ] [BorelSpace Kˣ] (μ : Measure Kˣ) [μ.IsHaarMeasure]
    (χ : Kˣ →ₜ* Circle) : finiteZetaIntegral F v μ χ (finiteGaussTest F v χ) 0 ≠ 0 := by
  rw [finiteGaussTest_mellin]
  exact Complex.ofReal_ne_zero.mpr (finiteZetaUnitMass_pos F v μ).ne'

/-- The finite average of (6.2.2.4) on compactly supported multiplicative
tests. Haar substitution expresses it as a scalar times the character. -/
def finiteStandardThetaAverageCLM [MeasurableSpace Kˣ] [BorelSpace Kˣ]
    (μ : Measure Kˣ) [μ.IsHaarMeasure] (χ : Kˣ →ₜ* Circle) :
    letI : TopologicalSpace (locallyConstantTests Kˣ) := finestLocallyConvexTopology _
    locallyConstantTests Kˣ →L[ℂ] C(Kˣ, ℂ) := by
  letI : TopologicalSpace (locallyConstantTests Kˣ) := finestLocallyConvexTopology _
  let φ : C(Kˣ, ℂ) := ⟨fun x => (χ x : ℂ), continuous_subtype_val.comp χ.continuous⟩
  let A (f : locallyConstantTests Kˣ) : ℂ := ∫ y, f.val y * ((χ y)⁻¹ : Circle) ∂μ
  have hi (f : locallyConstantTests Kˣ) :
      Integrable (fun y => f.val y * ((χ y)⁻¹ : Circle)) μ := by
    have hc : Continuous (fun y => f.val y * ((χ y)⁻¹ : Circle)) :=
      f.property.1.continuous.mul (continuous_subtype_val.comp χ.continuous.inv)
    exact hc.integrable_of_hasCompactSupport (f.property.2.mul_right)
  let L : locallyConstantTests Kˣ →ₗ[ℂ] ℂ :=
    { toFun := A
      map_add' := fun f g => by
        change (∫ y, (f.val y + g.val y) * ((χ y)⁻¹ : Circle) ∂μ) = A f + A g
        simp only [add_mul, integral_add (hi f) (hi g), A]
      map_smul' := fun c f => by
        change (∫ y, (c * f.val y) * ((χ y)⁻¹ : Circle) ∂μ) = c * A f
        simp only [mul_assoc, integral_const_mul, A] }
  exact (⟨L, finest_linear_continuous L⟩ : locallyConstantTests Kˣ →L[ℂ] ℂ).smulRight φ

/-- The continuous operator agrees pointwise with the printed finite integral. -/
theorem finiteStandardThetaAverageCLM_apply [MeasurableSpace Kˣ] [BorelSpace Kˣ]
    (μ : Measure Kˣ) [μ.IsHaarMeasure] (χ : Kˣ →ₜ* Circle)
    (f : locallyConstantTests Kˣ) (x : Kˣ) :
    finiteStandardThetaAverageCLM F v μ χ f x = ∫ g, f.val (g⁻¹ * x) * (χ g : ℂ) ∂μ := by
  letI : LocallyCompactSpace K := finitePlace_locallyCompact F v
  letI : SecondCountableTopology K := finitePlace_secondCountable F v
  let e : IsOpenEmbedding (Units.val : Kˣ → K) := IsOpenUnits.isOpenEmbedding_unitsVal
  letI := e.locallyCompactSpace
  letI := e.isEmbedding.secondCountableTopology
  letI := e.isEmbedding.metrizableSpace
  letI : μ.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _
  let A (y : Kˣ) : ℂ := f.val y * ((χ y)⁻¹ : Circle)
  change (∫ y, A y ∂μ) * (χ x : ℂ) = _
  rw [← integral_mul_const, ← integral_div_left_eq_self (fun y => A y * (χ x : ℂ)) μ x]
  apply integral_congr_ae
  exact .of_forall fun g => by
    change (f.val (x / g) * ((χ (x / g))⁻¹ : Circle)) * (χ x : ℂ) = _
    rw [div_eq_mul_inv, mul_comm x, mul_assoc]
    have h : (χ (g⁻¹ * x))⁻¹ * χ x = χ g := by
      rw [map_mul, map_inv, mul_inv_rev, inv_inv, mul_comm ((χ x)⁻¹), mul_assoc,
        inv_mul_cancel, mul_one]
    rw [← Circle.coe_mul, h]

theorem finiteStandardThetaAverage_isClosed_ker [MeasurableSpace Kˣ] [BorelSpace Kˣ]
    (μ : Measure Kˣ) [μ.IsHaarMeasure] (χ : Kˣ →ₜ* Circle) :
    letI : TopologicalSpace (locallyConstantTests Kˣ) := finestLocallyConvexTopology _
    IsClosed ((finiteStandardThetaAverageCLM F v μ χ).ker : Set (locallyConstantTests Kˣ)) := by
  letI : TopologicalSpace (locallyConstantTests Kˣ) := finestLocallyConvexTopology _
  exact (finiteStandardThetaAverageCLM F v μ χ).isClosed_ker

end
end Masullo
