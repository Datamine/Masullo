import WeightedKernelDiagonal
import Mathlib.Analysis.Normed.Module.Bases

open Filter MeasureTheory InnerProductSpace
open scoped ENNReal NNReal InnerProductSpace Topology Pointwise

namespace Masullo

noncomputable section

section ProjectionKernel

variable {X : Type*} [MeasurableSpace X] {ν : Measure X} [SFinite ν]

/-- The Riesz vector for a Schauder coordinate. -/
def schauderCoordinateVector (b : SchauderBasis ℂ (X →₂[ν] ℂ)) (i : ℕ) : X →₂[ν] ℂ :=
  (toDual ℂ (X →₂[ν] ℂ)).symm (b.coord i)

/-- The kernel of a left Schauder-basis projection followed by a bounded operator. -/
def schauderCutoffKernel (b : SchauderBasis ℂ (X →₂[ν] ℂ))
    (A : (X →₂[ν] ℂ) →L[ℂ] (X →₂[ν] ℂ)) (n : ℕ) (z : X × X) : ℂ :=
  ∑ i ∈ Finset.range n, b i z.1 * star ((A.adjoint (schauderCoordinateVector b i)) z.2)

theorem schauderCutoffKernel_operator (b : SchauderBasis ℂ (X →₂[ν] ℂ))
    (A : (X →₂[ν] ℂ) →L[ℂ] (X →₂[ν] ℂ)) (n : ℕ) :
    ∃ hk : MemLp (schauderCutoffKernel b A n) 2 (ν.prod ν),
      kernelIntegralOperator (hk.toLp (schauderCutoffKernel b A n)) = (b.proj n).comp A := by
  let u (i : ℕ) := b i
  let v (i : ℕ) := A.adjoint (schauderCoordinateVector b i)
  let h (i : ℕ) := (memLp_rankOneKernel (Lp.memLp (u i)) (Lp.memLp (v i))).1
  let kr (i : ℕ) := (h i).toLp (fun z : X × X => u i z.1 * star (v i z.2))
  let K := ∑ i ∈ Finset.range n, kr i
  have he : (K : X × X → ℂ) =ᵐ[ν.prod ν] schauderCutoffKernel b A n := by
    filter_upwards [Lp.coeFn_fun_finsetSum (Finset.range n) kr,
      ae_all_iff.mpr (fun i => (h i).coeFn_toLp)] with z hz hzi
    exact hz.trans (Finset.sum_congr rfl fun i _ => hzi i)
  let hk := (Lp.memLp K).ae_eq he
  have hK : hk.toLp (schauderCutoffKernel b A n) = K :=
    ((MemLp.toLp_eq_toLp_iff hk (Lp.memLp K)).mpr he.symm).trans (Lp.toLp_coeFn _ _)
  refine ⟨hk, ?_⟩
  rw [hK]
  change kernelIntegralOperatorCLM (∑ i ∈ Finset.range n, kr i) = _
  rw [map_sum]
  ext x : 1
  rw [sum_apply, ContinuousLinearMap.comp_apply, b.proj_apply]
  apply Finset.sum_congr rfl
  intro i _
  have hr : kernelIntegralOperatorCLM (kr i) = rankOne ℂ (u i) (v i) := by
    change kernelIntegralOperator (kr i) = _
    rw [show kernelIntegralOperator (kr i) =
      rankOne ℂ ((Lp.memLp (u i)).toLp (u i)) ((Lp.memLp (v i)).toLp (v i)) from
      kernelIntegralOperator_rankOne (Lp.memLp (u i)) (Lp.memLp (v i)), Lp.toLp_coeFn, Lp.toLp_coeFn]
  rw [hr, rankOne_apply]
  change ⟪A.adjoint (schauderCoordinateVector b i), x⟫_ℂ • b i = b.coord i (A x) • b i
  rw [A.adjoint_inner_left, schauderCoordinateVector, toDual_symm_apply]

end ProjectionKernel

section WeightedDuality

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) {w : X → ℝ}

private abbrev density (μ : Measure X) (w : X → ℝ) : Measure X :=
  μ.withDensity (fun x => ENNReal.ofReal (w x))

/-- The reciprocal-density representative of the bilinear functional associated
with a weighted L² Riesz vector. -/
def reciprocalDensityDual (d : X →₂[density μ w] ℂ) (x : X) : ℂ := (w x : ℂ) * star (d x)

theorem reciprocalDensityDual_pairing (hw : Measurable w) (hp : ∀ x, 0 < w x)
    (d f : X →₂[density μ w] ℂ) :
    (∫ x, reciprocalDensityDual μ d x * f x ∂μ) = ⟪d, f⟫_ℂ := by
  rw [MeasureTheory.L2.inner_def,
    integral_withDensity_eq_integral_toReal_smul hw.ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro x
  change reciprocalDensityDual μ d x * f x = (ENNReal.ofReal (w x)).toReal • ⟪d x, f x⟫_ℂ
  rw [RCLike.inner_apply, ENNReal.toReal_ofReal (hp x).le, Complex.real_smul]
  unfold reciprocalDensityDual
  simp only [starRingEnd_apply]
  ring

theorem reciprocalDensityDual_memLp (hw : Measurable w) (hp : ∀ x, 0 < w x)
    (d : X →₂[density μ w] ℂ) :
    MemLp (reciprocalDensityDual μ d) 2 (density μ fun x => (w x)⁻¹) := by
  have hm : Measurable (reciprocalDensityDual μ d) :=
    (Complex.continuous_ofReal.measurable.comp hw).mul
      (continuous_star.measurable.comp (Lp.stronglyMeasurable d).measurable)
  refine ⟨hm.aestronglyMeasurable, ?_⟩
  have he : eLpNorm (reciprocalDensityDual μ d) 2 (density μ fun x => (w x)⁻¹) =
      eLpNorm d 2 (density μ w) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
      eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
    simp only [ENNReal.toReal_ofNat]
    congr 1
    unfold density
    rw [lintegral_withDensity_eq_lintegral_mul μ (f := fun x => ENNReal.ofReal ((w x)⁻¹))
      hw.inv.ennreal_ofReal (hm.enorm.pow_const (2 : ℝ)),
      lintegral_withDensity_eq_lintegral_mul μ hw.ennreal_ofReal
        ((Lp.stronglyMeasurable d).measurable.enorm.pow_const (2 : ℝ))]
    apply lintegral_congr
    intro x
    have hi : (ENNReal.ofReal (w x))⁻¹ * ENNReal.ofReal (w x) = 1 :=
      ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr (hp x)).ne' ENNReal.ofReal_ne_top
    simp only [Pi.mul_apply]
    rw [ENNReal.ofReal_inv_of_pos (hp x), reciprocalDensityDual, enorm_mul,
      ← ofReal_norm ((w x : ℂ)), Complex.norm_real, Real.norm_of_nonneg (hp x).le,
      ← ofReal_norm (star _), norm_star, ofReal_norm, ENNReal.rpow_two, ENNReal.rpow_two, mul_pow]
    calc
      _ = ((ENNReal.ofReal (w x))⁻¹ * ENNReal.ofReal (w x)) *
          (ENNReal.ofReal (w x) * ‖d x‖ₑ ^ 2) := by rw [pow_two]; ac_rfl
      _ = _ := by rw [hi, one_mul]
  rw [he]
  exact (Lp.memLp d).eLpNorm_lt_top

/-- The reciprocal-density bilinear transpose is represented by the Hilbert adjoint. -/
theorem reciprocalDensityDual_adjoint (hw : Measurable w) (hp : ∀ x, 0 < w x)
    (A : (X →₂[density μ w] ℂ) →L[ℂ] (X →₂[density μ w] ℂ)) (d f : X →₂[density μ w] ℂ) :
    (∫ x, reciprocalDensityDual μ (A.adjoint d) x * f x ∂μ) =
      ∫ x, reciprocalDensityDual μ d x * (A f) x ∂μ := by
  rw [reciprocalDensityDual_pairing μ hw hp, reciprocalDensityDual_pairing μ hw hp, A.adjoint_inner_left]

theorem schauderCutoffKernel_reciprocalDensity
    (hp : ∀ x, 0 < w x) (b : SchauderBasis ℂ (X →₂[density μ w] ℂ))
    (A : (X →₂[density μ w] ℂ) →L[ℂ] (X →₂[density μ w] ℂ)) (n : ℕ) (z : X × X) :
    schauderCutoffKernel b A n z =
      ∑ i ∈ Finset.range n, b i z.1 *
        (reciprocalDensityDual μ (A.adjoint (schauderCoordinateVector b i)) z.2 / (w z.2 : ℂ)) := by
  apply Finset.sum_congr rfl
  intro i _
  rw [reciprocalDensityDual, mul_comm (↑(w z.2) : ℂ),
    mul_div_cancel_right₀ _ (Complex.ofReal_ne_zero.mpr (hp z.2).ne')]

end WeightedDuality

section WeightedCutoff

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure] [SigmaFinite μ] (w : G → ℝ)

/-- Theorem 12.1.1.2(4). The actual Schauder partial sums give the stated
projected kernels and both ambient limits, along with the bounded-test limit on
their smoothed diagonals. The argument works for every Schauder basis. -/
theorem weighted_schauderCutoffKernel_limits
    (hw : Continuous w) (hpos : ∀ x, 0 < w x) {U : ℕ → Set G}
    (hU : DoublingSequence μ U) (hcof : CofinalAtOne U)
    {C : ℝ≥0} (hC : 0 < C) (hDiff : ∀ n, μ (U n * (U n)⁻¹) < C * μ (U n))
    (b : SchauderBasis ℂ (G →₂[density μ w] ℂ))
    (T : RankOneSeries ℕ (G →₂[density μ w] ℂ))
    {k : G × G → ℂ} (hk : MemLp k 2 ((density μ w).prod (density μ w)))
    (hop : kernelIntegralOperator (hk.toLp k) = T.operator) :
    let ν := density μ w
    let kN (n : ℕ) := schauderCutoffKernel b T.operator (n + 1)
    let smooth (f : G × G → ℂ) :=
      regularizedLimit (fun n => translatedAverage (μ.prod μ) (U n ×ˢ U n) f)
    ∃ hkN : ∀ n, MemLp (kN n) 2 (ν.prod ν),
      (∀ n, kernelIntegralOperator ((hkN n).toLp (kN n)) = (b.proj (n + 1)).comp T.operator) ∧
      (Tendsto (fun n => (hkN n).toLp (kN n)) atTop (𝓝 (hk.toLp k))) ∧
      (∃ (hsN : ∀ n, MemLp (smooth (kN n)) 2 (ν.prod ν)) (hs : MemLp (smooth k) 2 (ν.prod ν)),
        Tendsto (fun n => (hsN n).toLp (smooth (kN n))) atTop (𝓝 (hs.toLp (smooth k)))) ∧
      (∀ ρ : G → ℂ, MemLp ρ ⊤ ν →
        Tendsto (fun n => ∫ x, ρ x * smooth (kN n) (x, x) ∂ν) atTop
          (𝓝 (∫ x, ρ x * smooth k (x, x) ∂ν))) := by
  let ν := density μ w
  letI : IsLocallyFiniteMeasure ν := IsLocallyFiniteMeasure.withDensity_ofReal hw
  let kN (n : ℕ) := schauderCutoffKernel b T.operator (n + 1)
  let P (n : ℕ) := b.proj (n + 1)
  let S (n : ℕ) := T.leftComp (P n)
  choose hkN hkernel using fun n : ℕ => schauderCutoffKernel_operator b T.operator (n + 1)
  have hS (n : ℕ) : kernelIntegralOperator ((hkN n).toLp (kN n)) = (S n).operator :=
    (hkernel n).trans (T.operator_leftComp (P n)).symm
  obtain ⟨B, hB⟩ := b.exists_norm_proj_le
  have hP (x : G →₂[ν] ℂ) : Tendsto (fun n => P n x) atTop (𝓝 x) :=
    (b.tendsto_proj x).comp (tendsto_add_atTop_nat 1)
  have htr := T.tendsto_leftComp_traceClass P (fun n => hB (n + 1)) hP
  obtain ⟨h₁, h₂⟩ := TraceClass.tendsto_schatten_errors htr
  exact ⟨hkN, hkernel,
    tendsto_weighted_kernel_smoothings μ w hw hpos hU hcof hC hDiff hkN hk hS hop h₁ h₂⟩

end WeightedCutoff

end

end Masullo
