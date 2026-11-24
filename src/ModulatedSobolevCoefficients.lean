import L2HilbertTensorProduct
import HardySobolevPaleyConverse
import Mathlib.Topology.Algebra.PontryaginDual

open Filter MeasureTheory Set Topology
open scoped ENNReal

namespace Masullo

noncomputable section

variable {K X : Type*} [MeasurableSpace K] [MeasurableSpace X]
variable {μ : Measure K} {ν : Measure X} [SFinite μ] [SFinite ν]

private def swapLpTwo :
    Lp ℂ 2 (μ.prod ν) →ₗᵢ[ℂ] Lp ℂ 2 (ν.prod μ) :=
  Lp.compMeasurePreservingₗᵢ ℂ Prod.swap Measure.measurePreserving_swap

/-- Form an integral coefficient along the first factor of a product (L^2) class. -/
def lpTwoFirstCoefficient (v : Lp ℂ 2 μ) : Lp ℂ 2 (μ.prod ν) →L[ℂ] Lp ℂ 2 ν :=
  (ContinuousLinearMap.apply ℂ (Lp ℂ 2 ν) v).comp
    (kernelIntegralOperatorCLM.comp swapLpTwo.toContinuousLinearMap)

theorem lpTwoFirstCoefficient_ae (v : Lp ℂ 2 μ) (u : Lp ℂ 2 (μ.prod ν)) :
    ∀ᵐ x ∂ν, Integrable (fun k => u (k, x) * v k) μ ∧
      lpTwoFirstCoefficient v u x = ∫ k, u (k, x) * v k ∂μ := by
  have hswap : (swapLpTwo u : X × K → ℂ) =ᵐ[ν.prod μ] u ∘ Prod.swap :=
    Lp.coeFn_compMeasurePreserving u Measure.measurePreserving_swap
  filter_upwards [kernelIntegralOperator_apply (swapLpTwo u) v,
    Measure.ae_ae_of_ae_prod hswap] with x hx he
  have hp : (fun k => swapLpTwo u (x, k) * v k) =ᵐ[μ] fun k => u (k, x) * v k :=
    he.mono fun k hk => congrArg (· * v k) hk
  exact ⟨hx.1.congr hp, hx.2.trans (integral_congr_ae hp)⟩

/-- The closed-support condition in product coordinates is imposed on the radial variable. -/
def lpTwoRadialSupport (μ : Measure K) (ν : Measure X) (U : Set X) :
    Submodule ℂ (Lp ℂ 2 (μ.prod ν)) where
  carrier := {u | ∀ᵐ p ∂μ.prod ν, p.2 ∉ U → u p = 0}
  zero_mem' := (Lp.coeFn_zero ℂ 2 (μ.prod ν)).mono fun _ h _ => h
  add_mem' {u w} hu hw := by
    filter_upwards [hu, hw, Lp.coeFn_add u w] with p h₁ h₂ h hp
    change (u + w) p = 0
    rw [h, Pi.add_apply, h₁ hp, h₂ hp, add_zero]
  smul_mem' a u hu := by
    filter_upwards [hu, Lp.coeFn_smul a u] with p h₁ h hp
    change (a • u) p = 0
    rw [h, Pi.smul_apply, h₁ hp, smul_zero]

theorem lpTwoFirstCoefficient_radialSupport (v : Lp ℂ 2 μ) {U : Set X}
    (u : lpTwoRadialSupport μ ν U) :
    ∀ᵐ x ∂ν, x ∉ U → lpTwoFirstCoefficient v u.val x = 0 := by
  have hs : ∀ᵐ p ∂ν.prod μ, p.1 ∉ U → u.val (p.2, p.1) = 0 :=
    Measure.measurePreserving_swap.quasiMeasurePreserving.ae (u.property :
      ∀ᵐ p ∂μ.prod ν, p.2 ∉ U → u.val p = 0)
  filter_upwards [Measure.ae_ae_of_ae_prod hs, lpTwoFirstCoefficient_ae v u.val]
    with x hx hi hU
  rw [hi.2]
  exact (integral_congr_ae (hx.mono fun k hk => by rw [hk hU, zero_mul])).trans (integral_zero K ℂ)

section Character

variable [TopologicalSpace K] [BorelSpace K] [CommGroup K] [IsFiniteMeasure μ]

omit [SFinite μ] in
private theorem compactCharacter_memLp (χ : PontryaginDual K) :
    MemLp (fun k => (χ k : ℂ)) 2 μ := by
  have hχ : Continuous (fun k => (χ k : ℂ)) := continuous_subtype_val.comp χ.continuous
  exact MemLp.of_bound (hχ.aestronglyMeasurable (μ := μ)) 1
    (Eventually.of_forall fun k => (Circle.norm_coe (χ k)).le)

/-- The character coefficient with the Mellin convention of multiplying by the character. -/
def lpTwoCharacterCoefficient (χ : PontryaginDual K) :
    Lp ℂ 2 (μ.prod ν) →L[ℂ] Lp ℂ 2 ν :=
  lpTwoFirstCoefficient ((compactCharacter_memLp (μ := μ) χ).toLp (fun k => (χ k : ℂ)))

theorem lpTwoCharacterCoefficient_ae (χ : PontryaginDual K) (u : Lp ℂ 2 (μ.prod ν)) :
    ∀ᵐ x ∂ν, Integrable (fun k => (χ k : ℂ) * u (k, x)) μ ∧
      lpTwoCharacterCoefficient χ u x = ∫ k, (χ k : ℂ) * u (k, x) ∂μ := by
  let v := (compactCharacter_memLp (μ := μ) χ).toLp (fun k => (χ k : ℂ))
  have hv : (v : K → ℂ) =ᵐ[μ] fun k => (χ k : ℂ) :=
    (compactCharacter_memLp (μ := μ) χ).coeFn_toLp
  filter_upwards [lpTwoFirstCoefficient_ae v u] with x hx
  have h : (fun k => u (k, x) * v k) =ᵐ[μ] fun k => (χ k : ℂ) * u (k, x) :=
    hv.mono fun k hk => by
      change u (k, x) * v k = (χ k : ℂ) * u (k, x)
      exact (congrArg (u (k, x) * ·) hk).trans (mul_comm _ _)
  exact ⟨hx.1.congr h, hx.2.trans (integral_congr_ae h)⟩

variable (μ) in
/-- A compact character coefficient preserves the supported scalar Hardy–Sobolev completion. -/
def modulatedSobolevCoefficient (b s : ℝ) {U : Set ℝ} (hU : IsOpen U)
    (χ : PontryaginDual K) :
    lpTwoRadialSupport μ (stripMeasure b b s) U →L[ℂ] supportedSobolevCompletion b b s U := by
  let v := (compactCharacter_memLp (μ := μ) χ).toLp (fun k => (χ k : ℂ))
  let F := (lpTwoFirstCoefficient (ν := stripMeasure b b s) v).comp
    (lpTwoRadialSupport μ (stripMeasure b b s) U).subtypeL
  refine F.codRestrict _ fun u => (mem_supportedSobolevCompletion_iff b b s hU _).mpr ?_
  exact (absolutelyContinuous_amplitudeMeasure volume _
    (stripSobolevAmplitude_continuous b b s).measurable
    (stripSobolevAmplitude_pos b b s)).ae_le (lpTwoFirstCoefficient_radialSupport v u)

theorem modulatedSobolevCoefficient_ae (b s : ℝ) {U : Set ℝ} (hU : IsOpen U)
    (χ : PontryaginDual K) (u : lpTwoRadialSupport μ (stripMeasure b b s) U) :
    ∀ᵐ x ∂(volume : Measure ℝ), Integrable (fun k => (χ k : ℂ) * u.val (k, x)) μ ∧
      (modulatedSobolevCoefficient μ b s hU χ u).val x =
        ∫ k, (χ k : ℂ) * u.val (k, x) ∂μ :=
  (absolutelyContinuous_amplitudeMeasure volume _
    (stripSobolevAmplitude_continuous b b s).measurable
    (stripSobolevAmplitude_pos b b s)).ae_le (lpTwoCharacterCoefficient_ae χ u.val)

/-- Bounded Mellin evaluation on a single character of the supported product
space. The outer integral is absolutely convergent in logarithmic coordinates. -/
theorem modulatedSobolev_mellinMoment (b s : ℝ) {c : ℝ} (hc : c ≤ 0)
    (hs : 0 ≤ s) {z : ℂ} (hz : z.re < b) (k : ℕ) (χ : PontryaginDual K) :
    ∃! L : StrongDual ℂ (lpTwoRadialSupport μ (stripMeasure b b s) (Ioi c)),
      ∀ u : lpTwoRadialSupport μ (stripMeasure b b s) (Ioi c),
        let F x := (∫ j, (χ j : ℂ) * u.val (j, x) ∂μ) * mellinEvaluationKernel k z x
        Integrable F ∧ L u = ∫ x, F x := by
  obtain ⟨L, hL⟩ := cutoffSobolev_mellinMoment_functional (a := b) hc hs hz k
  let A := modulatedSobolevCoefficient μ b s (U := Ioi c) isOpen_Ioi χ
  let M := L.comp A
  have hM (u : lpTwoRadialSupport μ (stripMeasure b b s) (Ioi c)) :
      let F x := (∫ j, (χ j : ℂ) * u.val (j, x) ∂μ) * mellinEvaluationKernel k z x
      Integrable F ∧ M u = ∫ x, F x := by
    have he : (fun x => (A u).val x * mellinEvaluationKernel k z x) =ᵐ[volume]
        (fun x => (∫ j, (χ j : ℂ) * u.val (j, x) ∂μ) * mellinEvaluationKernel k z x) :=
      (modulatedSobolevCoefficient_ae b s isOpen_Ioi χ u).mono fun x hx =>
        congrArg (· * mellinEvaluationKernel k z x) hx.2
    exact ⟨(hL (A u)).1.congr he, (hL (A u)).2.trans (integral_congr_ae he)⟩
  refine ⟨M, hM, fun Q hQ => ?_⟩
  ext u
  exact ((hQ u).2).trans ((hM u).2).symm

end Character

end

end Masullo
