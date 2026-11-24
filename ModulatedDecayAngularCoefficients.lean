import ModulatedExponentialRadial
import ModulatedCyclicFourier
import Mathlib.Topology.Metrizable.Urysohn

open Function MeasureTheory Set Topology

namespace Masullo

noncomputable section

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  (m : G →ₜ* Multiplicative ℝ) (τ : Multiplicative ℝ →ₜ* G) (hτ : RightInverse τ m)

local notation "K" => m.toMonoidHom.ker

variable [MeasurableSpace m.toMonoidHom.ker] [BorelSpace m.toMonoidHom.ker]
  (ν : Measure m.toMonoidHom.ker) [ν.IsHaarMeasure]
  (ω : PontryaginDual m.toMonoidHom.ker) (I : Set ℝ) (hI : I.Nonempty) (hm : IsProperMap m)

include hτ in
/-- The angular Fourier coefficient is a continuous linear map into the
radial decay space, with its full topology of weighted Schwartz profiles. -/
def modulatedDecayAngularCoefficient :
    ModulatedExponentialInductive m I →L[ℂ] PositiveRealExponentialDecay I :=
  (modulatedDecayRadialRestriction m τ hτ I hI).comp
    (modulatedDecay_kernelAverage m ν ω I hm hτ.surjective hI)

include hτ in
/-- The coefficient uses the positive character in the integral, so the
associated Fourier term uses the inverse character. -/
theorem modulatedDecayAngularCoefficient_apply (f : ModulatedExponentialInductive m I) (x : ℝ) :
    (modulatedDecayAngularCoefficient m τ hτ ν ω I hI hm f).val x =
      ∫ k : K, f.val (τ (Multiplicative.ofAdd x) * k.val) * (ω k : ℂ) ∂ν := by
  change (modulatedDecayRadialRestriction m τ hτ I hI
    (modulatedDecay_kernelAverage m ν ω I hm hτ.surjective hI f)).val x = _
  rw [modulatedDecayRadialRestriction_apply, modulatedDecay_kernelAverage_apply]
  letI : CompactSpace K := isCompact_iff_compactSpace.mp
    (hm.isCompact_preimage (isCompact_singleton (x := (1 : Multiplicative ℝ))))
  letI : SecondCountableTopology K := IsInducing.subtypeVal.secondCountableTopology
  letI : Measure.Regular ν := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure ν
  letI : ν.IsInvInvariant := Measure.IsHaarMeasure.isInvInvariant_of_regular ν
  let S (k : K) := f.val (τ (Multiplicative.ofAdd x) * k.val) * (ω k : ℂ)
  have h := integral_inv_eq_self S ν
  change (∫ k : K, (((ω k)⁻¹ : Circle) : ℂ) * f.val (k.val⁻¹ * τ (Multiplicative.ofAdd x)) ∂ν) =
    ∫ k : K, S k ∂ν
  rw [← h]
  apply integral_congr_ae
  exact .of_forall fun k => by
    change (((ω k)⁻¹ : Circle) : ℂ) * f.val (k.val⁻¹ * τ (Multiplicative.ofAdd x)) =
      f.val (τ (Multiplicative.ofAdd x) * k.val⁻¹) * (ω k⁻¹ : ℂ)
    rw [map_inv, mul_comm k.val⁻¹, mul_comm]

include hτ in
/-- Taking an angular coefficient of a separated product leaves the radial
profile multiplied by the scalar coefficient of the angular test. -/
theorem modulatedDecayAngularCoefficient_of_product [CompactSpace K] [IsProbabilityMeasure ν]
    [LocallyCompactSpace K] (a : BruhatSchwartz K) (r : PositiveRealExponentialDecay I)
    (f : ModulatedExponentialInductive m I)
    (hf : ∀ (x : ℝ) (k : K), f.val (τ (Multiplicative.ofAdd x) * k.val) = a.val k * r.val x) :
    modulatedDecayAngularCoefficient m τ hτ ν ω I hI hm f =
      compactBruhatFourierCoeff ν ω a • r := by
  apply Subtype.ext
  funext x
  change (modulatedDecayAngularCoefficient m τ hτ ν ω I hI hm f).val x =
    compactBruhatFourierCoeff ν ω a * r.val x
  rw [modulatedDecayAngularCoefficient_apply, compactBruhatFourierCoeff_apply]
  have hν : (ν.real univ : ℂ)⁻¹ = 1 := by
    rw [measureReal_def, measure_univ, ENNReal.toReal_one, Complex.ofReal_one, inv_one]
  rw [hν, one_mul, ← integral_mul_const]
  apply integral_congr_ae
  exact .of_forall fun k => (congrArg (fun z : ℂ => z * (ω k : ℂ)) (hf x k)).trans
    (mul_right_comm (a.val k) (r.val x) (ω k : ℂ))

end

end Masullo
