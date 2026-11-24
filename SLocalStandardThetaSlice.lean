import SLocalArchSchwartzDilation
import FiniteStandardThetaTest

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical NumberField SchwartzMap

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]
variable (S : Finset (HeightOneSpectrum (𝓞 F)))

private abbrev K := SLocalThetaNormOne F S
private abbrev Arch := 𝓢(mixedEmbedding.mixedSpace F, ℂ)
private abbrev Finite := locallyConstantTests (∀ v : S, v.val.adicCompletion F)
private abbrev Tests := sLocalBruhatImage F S

variable [∀ v : S, MeasurableSpace (v.val.adicCompletion F)ˣ]
  [∀ v : S, BorelSpace (v.val.adicCompletion F)ˣ]
  (μ : ∀ v : S, Measure (v.val.adicCompletion F)ˣ)
  [∀ v : S, (μ v).IsHaarMeasure] [∀ v : S, SigmaFinite (μ v)]

/-- The finite factor is the integer-ring test at an unramified place and
the unit-shell test with the conjugate phase at a ramified place. -/
def sLocalStandardFiniteTest (ω : PontryaginDual (K F S)) : Finite F S :=
  locallyConstantTestPiProduct fun v =>
    let χ := sLocalFiniteZetaPhases F S ω v
    if finiteZetaUnramified F v.val χ then finiteCompletionIntegerRingTest F v.val
      else finiteGaussTest F v.val χ

/-- The cleared Mellin numerator of the standard finite factor is its
positive product of unit-shell Haar masses. -/
theorem sLocalStandardFiniteTest_cleared (ω : PontryaginDual (K F S))
    (z : ℂ) (hz : 0 < z.re) :
    sLocalFiniteZetaCleared F S μ (sLocalFiniteZetaPhases F S ω) z
        (sLocalStandardFiniteTest F S ω) =
      ∏ v : S, ( (μ v).real (finitePlaceIntegralUnits F v.val) : ℂ) := by
  unfold sLocalStandardFiniteTest
  rw [sLocalFiniteZetaCleared_piProduct]
  refine Finset.prod_congr rfl fun v _ => ?_
  let χ := sLocalFiniteZetaPhases F S ω v
  change (if finiteZetaUnramified F v.val χ then _ else _) = _
  by_cases h : finiteZetaUnramified F v.val χ
  · simp only [ite_eq_left h]
    change finiteZetaClearedDistribution F v.val (μ v) χ z
      (if finiteZetaUnramified F v.val χ then _ else _) = _
    rw [ite_eq_left h]
    exact finiteZetaClearedDistribution_integerRing_unramified F v.val (μ v) χ h z
  · change finiteProductClearedLocal F S μ (sLocalFiniteZetaPhases F S ω) v
      (if finiteZetaUnramified F v.val χ then _ else _) z = _
    simp only [ite_eq_right h]
    change (if finiteZetaUnramified F v.val χ then _ else finiteZetaContinuation F v.val
      (μ v) χ (finiteGaussTest F v.val χ) z) = _
    rw [ite_eq_right h, ← (finiteZetaContinuation_eq_integral F v.val (μ v) χ _ z hz).2,
      finiteGaussTest_mellin]

variable [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]

private abbrev Z (ω : PontryaginDual (K F S)) (f : Tests F S) (z : ℂ) :=
  sLocalContinuedMellinEval F S μ ω z f

omit [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ] in
set_option maxHeartbeats 900000 in
/-- The product formula for an archimedean Schwartz test tensored with an
arbitrary coupled finite test. The finite factor retains its Euler denominator. -/
theorem sLocalStandardThetaSlice_mellin (ω : PontryaginDual (K F S))
    (f : Arch F) (g : Finite F S) (z : ℂ) :
    sLocalContinuedMellinEval F S μ ω z (sLocalBruhatPure F S f g) =
      (sLocalFiniteZetaDenominator F S (sLocalFiniteZetaPhases F S ω) z)⁻¹ *
        sLocalFiniteZetaCleared F S μ (sLocalFiniteZetaPhases F S ω) z g *
        archimedeanNumberFieldZeta F complexTamagawaAngularMeasure
          (sLocalRealArchParameters F S ω) (sLocalComplexArchParameters F S ω) z f := by
  change sLocalProductZetaContinued F S μ ω _ _ (sLocalBruhatPure F S f g) z = _
  simp only [sLocalProductZetaContinued, sLocalFiniteZetaSchwartzTest, sLocalBruhatContractFinite_pure,
    map_smul, ContinuousLinearMap.coe_coe, sLocalFiniteZetaContinued, smul_apply, smul_eq_mul]

omit [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ] in
private theorem standardSlice_mul_numerator (ω : PontryaginDual (K F S))
    (f : Arch F) (g h : Finite F S) (z : ℂ) :
    sLocalFiniteZetaCleared F S μ (sLocalFiniteZetaPhases F S ω) z h *
        Z F S μ ω (sLocalBruhatPure F S f g) z =
      sLocalFiniteZetaCleared F S μ (sLocalFiniteZetaPhases F S ω) z g *
        Z F S μ ω (sLocalBruhatPure F S f h) z := by
  change _ * sLocalContinuedMellinEval F S μ ω z (sLocalBruhatPure F S f g) =
    _ * sLocalContinuedMellinEval F S μ ω z (sLocalBruhatPure F S f h)
  rw [sLocalStandardThetaSlice_mellin, sLocalStandardThetaSlice_mellin]
  ring

private theorem standardSlice_exp (ω : PontryaginDual (K F S))
    (f : Arch F) (g : Finite F S) (t : ℝ) :
    ∃ f' : Arch F, ∀ z : ℂ, 0 < z.re →
      Z F S μ ω (sLocalBruhatPure F S f' g) z =
        Complex.exp ((t : ℂ) * z) * Z F S μ ω (sLocalBruhatPure F S f g) z := by
  refine ⟨schwartzScalarPullback (Real.exp (-t / Module.finrank ℚ F))
    (Real.exp_pos _).ne' f, fun z hz => ?_⟩
  rw [← sLocalBruhatLeftTranslate_expSection_pure F S t f g]
  have hreg : z ∈ sLocalMellinRegularSet F S ω :=
    (sLocalMellinRegularSet_iff_noEulerPole F S ω z).mpr
      (le_of_not_gt (fun h => sLocalEulerDenominator_ne_zero_of_pos F S ω hz
        ((sLocalEulerFactor_order_lt_zero_iff F S ω z).mp h)))
  change sLocalProductZetaContinued F S μ ω _ _
    (sLocalBruhatLeftTranslate F S (sLocalExpSection F S (Multiplicative.ofAdd t))
      (sLocalBruhatPure F S f g)) z = _
  rw [sLocalProductZetaContinued_leftTranslate F S μ ω _ _ hreg,
    sLocalZetaWeight_expSection F S ω t, mul_comm z]
  rfl

/-- Every S-local test has the same Mellin integral on the half-plane of
convergence as a test with the fixed standard finite factor. -/
theorem exists_sLocalStandardThetaSlice (ω : PontryaginDual (K F S)) (a : Tests F S) :
    ∃ f : Arch F, ∀ z : ℂ, 0 < z.re →
      Z F S μ ω (sLocalBruhatPure F S f (sLocalStandardFiniteTest F S ω)) z =
        Z F S μ ω a z := by
  let g := sLocalStandardFiniteTest F S ω
  let P := (sLocalBruhatPure F S).flip g
  let C : ℂ := ∏ v : S, ((μ v).real (finitePlaceIntegralUnits F v.val) : ℂ)
  have hC : C ≠ 0 := Finset.prod_ne_zero_iff.mpr fun v _ =>
    Complex.ofReal_ne_zero.mpr (finiteZetaUnitMass_pos F v.val (μ v)).ne'
  have zadd (z : ℂ) (a b : Tests F S) : Z F S μ ω (a + b) z = Z F S μ ω a z + Z F S μ ω b z :=
    map_add (sLocalContinuedMellinEval F S μ ω z) a b
  have zsmul (z c : ℂ) (a : Tests F S) : Z F S μ ω (c • a) z = c * Z F S μ ω a z :=
    map_smul (sLocalContinuedMellinEval F S μ ω z) c a
  have hm (f : Arch F) {m : ℂ → ℂ} (hm : m ∈ mellinExponentialAlgebra) :
      ∃ q : Arch F, ∀ z : ℂ, 0 < z.re → Z F S μ ω (P q) z = m z * Z F S μ ω (P f) z := by
    change m ∈ mellinExponentialAlgebra.toSubmodule at hm
    rw [mellinExponentialAlgebra_toSubmodule] at hm
    induction hm using Submodule.span_induction with
    | mem m hh =>
      obtain ⟨t, rfl⟩ := hh
      exact standardSlice_exp F S μ ω f g t
    | zero => exact ⟨0, fun z _ => by simp [P]⟩
    | add m n _ _ hm hn =>
      obtain ⟨p, hp⟩ := hm
      obtain ⟨q, hq⟩ := hn
      exact ⟨p + q, fun z hz => by
        rw [map_add P, zadd, hp z hz, hq z hz, Pi.add_apply, add_mul]⟩
    | smul c m _ hm =>
      obtain ⟨p, hp⟩ := hm
      exact ⟨c • p, fun z hz => by
        rw [map_smul P, zsmul, hp z hz, Pi.smul_apply]
        simp only [smul_eq_mul, mul_assoc]⟩
  have ha : a ∈ Submodule.span ℂ {x : Tests F S |
      ∃ (f : Arch F) (h : Finite F S), sLocalBruhatPure F S f h = x} := by
    rw [sLocalBruhatPure_span]
    trivial
  change ∃ f, ∀ z : ℂ, 0 < z.re → Z F S μ ω (P f) z = Z F S μ ω a z
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨f, h, rfl⟩ := ha
    obtain ⟨q, hq⟩ := hm f (sLocalFiniteZetaCleared_mem_exponentialAlgebra F S μ
      (sLocalFiniteZetaPhases F S ω) h)
    refine ⟨C⁻¹ • q, fun z hz => ?_⟩
    rw [map_smul P, zsmul, hq z hz]
    have he := standardSlice_mul_numerator F S μ ω f h g z
    rw [sLocalStandardFiniteTest_cleared F S μ ω z hz] at he
    change C * Z F S μ ω (sLocalBruhatPure F S f h) z = _ at he
    rw [show P f = sLocalBruhatPure F S f g from rfl, ← he, ← mul_assoc, inv_mul_cancel₀ hC, one_mul]
  | zero => exact ⟨0, fun z _ => by rw [map_zero P]⟩
  | add a b _ _ ha hb =>
    obtain ⟨f, hf⟩ := ha
    obtain ⟨h, hh⟩ := hb
    exact ⟨f + h, fun z hz => by
      rw [map_add P, zadd, zadd, hf z hz, hh z hz]⟩
  | smul c a _ ha =>
    obtain ⟨f, hf⟩ := ha
    exact ⟨c • f, fun z hz => by
      rw [map_smul P, zsmul, zsmul, hf z hz]⟩

end
end Masullo
