import SLocalMeromorphicKernels
import SLocalThetaDerivatives
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped NumberField

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]
variable (S : Finset (HeightOneSpectrum (𝓞 F)))

private abbrev K := SLocalThetaNormOne F S
private abbrev E := sLocalBruhatImage F S

/-- Differentiation along the canonical logarithmic norm section. -/
def sLocalRadialDerivative : E F S →L[ℂ] E F S :=
  sLocalBruhatDerivative F S (sLocalExpSection F S) (sLocalExpSection_continuous F S)

section RadialIntegral

variable [MeasurableSpace (K F S)] [BorelSpace (K F S)]
variable (ν : Measure (K F S)) [ν.IsHaarMeasure]

/-- Integration by parts in the real logarithmic coordinate of the actual
S-idele class group. -/
theorem sLocalRadialMellin_derivative (ω : PontryaginDual (K F S)) (f : E F S) (z : ℂ)
    (hz : 0 < z.re) :
    sLocalRadialMellin F S (sLocalExpSection F S) ν ω (sLocalRadialDerivative F S f) z =
      -z * sLocalRadialMellin F S (sLocalExpSection F S) ν ω f z := by
  let γ := sLocalExpSection F S
  let U (t : ℝ) := Complex.exp (z * (t : ℂ))
  let V (g : E F S) (t : ℝ) := sLocalHomogeneousTheta F S ν ω g.val
    (QuotientGroup.mk (γ (Multiplicative.ofAdd t)))
  let D := sLocalRadialDerivative F S
  have hU (t : ℝ) : HasDerivAt U (z * U t) t := by
    have ht : HasDerivAt (fun t : ℝ ↦ (t : ℂ)) 1 t := by
      change HasDerivAt (⇑Complex.ofRealCLM) (Complex.ofRealCLM 1) t
      exact Complex.ofRealCLM.hasFDerivAt.hasDerivAt
    simpa only [U, mul_one, one_mul, mul_comm z] using (ht.const_mul z).cexp
  have hV (t : ℝ) : HasDerivAt (V f) (V (D f) t) t :=
    sLocalHomogeneousTheta_log_hasDerivAt F S γ (sLocalExpSection_continuous F S) ν ω f t
  have hi (g : E F S) : Integrable (U * V g) :=
    sLocalRadialMellin_integrable F S γ (sLocalExpSection_continuous F S)
      (sLocalIdeleNorm_expSection F S) ν ω g z hz
  have hi' : Integrable ((fun t ↦ z * U t) * V f) := by
    change Integrable (fun t ↦ (z * U t) * V f t)
    simp_rw [mul_assoc]
    exact (hi f).const_mul z
  have h := integral_mul_deriv_eq_deriv_mul_of_integrable
    (fun t _ ↦ hU t) (fun t _ ↦ hV t) (hi (D f)) hi' (hi f)
  change (∫ t : ℝ, U t * V (D f) t) = -z * ∫ t : ℝ, U t * V f t
  rw [h]
  simp only [mul_assoc, integral_const_mul, neg_mul]

end RadialIntegral

attribute [local instance] sLocalZetaUnfolding_classMeasurable sLocalZetaUnfolding_classBorel
  sLocalZetaUnfolding_idelesMeasurable

variable [∀ v : S, MeasurableSpace (v.val.adicCompletion F)ˣ]
  [∀ v : S, BorelSpace (v.val.adicCompletion F)ˣ]
  (μ : ∀ v : S, Measure (v.val.adicCompletion F)ˣ)
  [∀ v : S, (μ v).IsHaarMeasure] [∀ v : S, SigmaFinite (μ v)]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]

variable (ν : Measure (K F S)) [ν.IsHaarMeasure]
variable (hν : IsWeilQuotientMeasure (sUnitImage F S)
  (sLocalZetaProductMeasure F S μ (archimedeanMultiplicativeHaar F))
  Measure.count (sLocalClassHaar F S ν))

private abbrev Z (ω : PontryaginDual (K F S)) (f : E F S) :=
  sLocalProductZetaContinued F S μ ω (sLocalRealArchParameters F S ω)
    (sLocalComplexArchParameters F S ω) f

include hν in
/-- Radial differentiation on the half-plane of convergence gives
pointwise multiplication by the spectral power. -/
theorem sLocalContinuedZeta_iterate_radialDerivative_of_pos
    (ω : PontryaginDual (K F S)) (f : E F S) (n : ℕ) (z : ℂ) (hz : 0 < z.re) :
    Z F S μ ω ((sLocalRadialDerivative F S)^[n] f) z = (-z) ^ n * Z F S μ ω f z := by
  have h (g : E F S) :
      Z F S μ ω g z = sLocalRadialMellin F S (sLocalExpSection F S) ν ω g z :=
    (sLocalContinuedZeta_eq_theta F S μ ν hν ω g hz).trans
      (sLocalThetaZeta_integrable_eq_radial F S ν ω g z hz).2
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', h, sLocalRadialMellin_derivative F S ν ω _ z hz,
      ← h, ih, pow_succ', mul_assoc]

set_option maxHeartbeats 600000 in
include hν in
/-- Radial differentiation multiplies the continued Mellin germ by the
negative spectral parameter, with the same identity for all iterates. -/
theorem sLocalContinuedZeta_iterate_radialDerivative
    (ω : PontryaginDual (K F S)) (f : E F S) (n : ℕ) (z : ℂ) :
    Z F S μ ω ((sLocalRadialDerivative F S)^[n] f) =ᶠ[𝓝[≠] z]
      fun w ↦ (-w) ^ n * Z F S μ ω f w := by
  let g := (sLocalRadialDerivative F S)^[n] f
  let A : meromorphicRepresentatives :=
    ⟨Z F S μ ω g, sLocalProductZetaContinued_meromorphic F S μ ω _ _ g⟩
  have hP : AnalyticOnNhd ℂ (fun w : ℂ ↦ (-w) ^ n) univ :=
    (analyticOnNhd_id.neg).pow n
  let B : meromorphicRepresentatives :=
    ⟨fun w ↦ (-w) ^ n * Z F S μ ω f w, fun w ↦
      (hP w (mem_univ _)).meromorphicAt.mul
        (sLocalProductZetaContinued_meromorphic F S μ ω _ _ f w)⟩
  have h := planeMeromorphicFunctions_mk_eq_of_eqOn_right A B
    (fun w hw ↦ sLocalContinuedZeta_iterate_radialDerivative_of_pos F S μ ν hν ω f n w hw)
  rw [← sub_eq_zero, ← map_sub, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h
  change ∀ c : ℂ, (fun w ↦ Z F S μ ω g w - (-w) ^ n * Z F S μ ω f w)
    =ᶠ[𝓝[≠] c] 0 at h
  filter_upwards [h z] with w hw
  exact sub_eq_zero.mp hw

end

end Masullo
