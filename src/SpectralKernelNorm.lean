import RadonKernelTrace
import CompactSingularExpansion
import SchattenConvergence
import Mathlib.Topology.Metrizable.Urysohn

open Filter MeasureTheory
open scoped ENNReal NNReal InnerProductSpace Topology Pointwise

namespace Masullo

noncomputable section

universe u

variable {H K : Type u}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

omit [CompleteSpace H] [CompleteSpace K] in
/-- The energy in a Hilbert basis is the sum of squared approximation numbers. -/
theorem IsSingularExpansion.basis_energy {ι : Type*} (b : HilbertBasis ι ℂ H)
    {T : H →L[ℂ] K} {s : ℕ → ℝ} {e : ℕ → H} {f : ℕ → K}
    (h : IsSingularExpansion T s e f) :
    (∑' i, ‖T (b i)‖ₑ ^ (2 : ℝ)) = ∑' n, ENNReal.ofReal (approximationNumber n T ^ 2) := by
  simp_rw [h.approximationNumber_eq, h.image_energy]
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro n
  rw [ENNReal.tsum_mul_left, tsum_enorm_basis_inner_sq b]
  by_cases hn : 0 < s n
  · have he := h.sourceOrthonormal.norm_eq_one ⟨n, hn⟩
    change ‖e n‖ = 1 at he
    simp [← ofReal_norm (e n), he]
  · simp [le_antisymm (le_of_not_gt hn) (h.nonnegative n)]

variable {X : Type*} [TopologicalSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [SFinite μ]

/-- The manuscript's spectral Schatten-2 norm equals the L² norm of the kernel. -/
theorem kernelIntegralOperator_schatten_two (k : (X × X) →₂[μ.prod μ] ℂ) :
    IsSchatten 2 (kernelIntegralOperator k) ∧
      schattenNorm 2 (kernelIntegralOperator k) = ‖k‖ := by
  have hc := (radonKernel_hilbertSchmidt μ k).1
  obtain ⟨s, e, f, h, _⟩ := compactOperator_hasSingularExpansion (kernelIntegralOperator k) hc
  obtain ⟨I, hI, ⟨b⟩⟩ := exists_countable_hilbertBasis_L2 (ν := μ)
  letI : Countable I := hI.to_subtype
  have he := (h.basis_energy b).symm.trans (kernelIntegralOperator_hilbertSchmidt_sq b k)
  have hf : (∑' n, ENNReal.ofReal (approximationNumber n (kernelIntegralOperator k) ^ 2)) ≠ ⊤ :=
    he.trans_ne (ENNReal.rpow_lt_top_of_nonneg (by norm_num) enorm_ne_top).ne
  refine ⟨⟨hc, ?_⟩, ?_⟩
  · simpa only [Real.rpow_two, ENNReal.toReal_ofReal (sq_nonneg _)] using ENNReal.summable_toReal hf
  · have ht := congrArg ENNReal.toReal he
    rw [ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top)] at ht
    simp only [ENNReal.toReal_ofReal (sq_nonneg _), ENNReal.rpow_two, ENNReal.toReal_pow, toReal_enorm] at ht
    simp only [schattenNorm, Real.rpow_two, ht]
    rw [← Real.rpow_natCast_mul (norm_nonneg _) 2]
    norm_num

/-- A spectral Schatten-2 limit of integral operators gives an L² limit of their
actual kernel classes. -/
theorem tendsto_kernel_of_schatten_two {ι : Type*} {l : Filter ι}
    {k : ι → (X × X) →₂[μ.prod μ] ℂ} {K₀ : (X × X) →₂[μ.prod μ] ℂ}
    (h : Tendsto (fun n => schattenNorm 2 (kernelIntegralOperator (k n) - kernelIntegralOperator K₀))
      l (𝓝 0)) : Tendsto k l (𝓝 K₀) := by
  rw [tendsto_iff_dist_tendsto_zero]
  have he (n : ι) : schattenNorm 2 (kernelIntegralOperator (k n) - kernelIntegralOperator K₀) =
      dist (k n) K₀ := by
    change schattenNorm 2 (kernelIntegralOperatorCLM (k n) - kernelIntegralOperatorCLM K₀) = _
    rw [← map_sub, dist_eq_norm]
    exact (kernelIntegralOperator_schatten_two μ (k n - K₀)).2
  simpa only [he] using h

section Haar

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  (ν : Measure G) [ν.IsHaarMeasure] [SigmaFinite ν]

/-- On the product Haar space, double-window smoothing recovers any locally
integrable representative almost everywhere. -/
theorem doubleWindowSmoothing_ae_eq_of_locallyIntegrable {U : ℕ → Set G}
    (hU : DoublingSequence ν U) (hcof : CofinalAtOne U) (hUc : IsCompact (closure (U 0)))
    {C : ℝ≥0} (hC : 0 < C) (hDiff : ∀ n, ν (U n * (U n)⁻¹) < C * ν (U n))
    {k : G × G → ℂ} (hk : LocallyIntegrable k (ν.prod ν)) :
    regularizedLimit (fun n => translatedAverage (ν.prod ν) (U n ×ˢ U n) k) =ᵐ[ν.prod ν] k := by
  letI : Measure.Regular (ν.prod ν) :=
    Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _
  let W (n : ℕ) := U n ×ˢ U n
  have hWd : DoublingSequence (ν.prod ν) W := doublingSequence_measure_prod hU hU
  have hWcof : CofinalAtOne W :=
    doublingSequence_prod_properties.1 hU.decreasing hU.decreasing hcof hcof
  have hWc : IsCompact (closure (W 0)) := by
    rw [show W 0 = U 0 ×ˢ U 0 from rfl, closure_prod_eq]
    exact hUc.prod hUc
  have hdiff (n : ℕ) : (ν.prod ν) (W n * (W n)⁻¹) < (↑(C * C) : ℝ≥0∞) * (ν.prod ν) (W n) := by
    simp only [W, Set.inv_prod, Set.prod_mul_prod_comm, Measure.prod_prod, ENNReal.coe_mul]
    simpa only [mul_mul_mul_comm] using ENNReal.mul_lt_mul (hDiff n) (hDiff n)
  filter_upwards [(translatedAverage_ae_of_locallyIntegrable_of_isCompact_closure
    (ν.prod ν) hWd hWcof hWc (mul_pos hC hC) hdiff hk).2] with p hp
  exact regularizedLimit_tendsto hp

/-- Smoothing with double Haar windows yields the same ambient L² class. -/
theorem doubleWindowSmoothing_ae_eq {U : ℕ → Set G}
    (hU : DoublingSequence ν U) (hcof : CofinalAtOne U) (hUc : IsCompact (closure (U 0)))
    {C : ℝ≥0} (hC : 0 < C) (hDiff : ∀ n, ν (U n * (U n)⁻¹) < C * ν (U n))
    {k : G × G → ℂ} (hk : MemLp k 2 (ν.prod ν)) :
    regularizedLimit (fun n => translatedAverage (ν.prod ν) (U n ×ˢ U n) k) =ᵐ[ν.prod ν] k :=
  doubleWindowSmoothing_ae_eq_of_locallyIntegrable ν hU hcof hUc hC hDiff
    (hk.locallyIntegrable (by norm_num))

/-- The ambient L² conclusions of Theorem 12.1.1.2(3) for Haar measure.
The original and smoothed sequences converge in L² to their respective limits. -/
theorem tendsto_doubleWindowKernels_of_schatten_two {U : ℕ → Set G}
    (hU : DoublingSequence ν U) (hcof : CofinalAtOne U) (hUc : IsCompact (closure (U 0)))
    {C : ℝ≥0} (hC : 0 < C) (hDiff : ∀ n, ν (U n * (U n)⁻¹) < C * ν (U n))
    {ι : Type*} {l : Filter ι} {k : ι → G × G → ℂ} {K₀ : G × G → ℂ}
    (hk : ∀ n, MemLp (k n) 2 (ν.prod ν)) (hK₀ : MemLp K₀ 2 (ν.prod ν))
    (h : Tendsto (fun n => schattenNorm 2
      (kernelIntegralOperator ((hk n).toLp (k n)) - kernelIntegralOperator (hK₀.toLp K₀))) l (𝓝 0)) :
    let smooth (f : G × G → ℂ) :=
      regularizedLimit (fun n => translatedAverage (ν.prod ν) (U n ×ˢ U n) f)
    ∃ (hk' : ∀ n, MemLp (smooth (k n)) 2 (ν.prod ν)) (hK₀' : MemLp (smooth K₀) 2 (ν.prod ν)),
      Tendsto (fun n => (hk n).toLp (k n)) l (𝓝 (hK₀.toLp K₀)) ∧
        Tendsto (fun n => (hk' n).toLp (smooth (k n))) l (𝓝 (hK₀'.toLp (smooth K₀))) := by
  let smooth (f : G × G → ℂ) := regularizedLimit (fun n => translatedAverage (ν.prod ν) (U n ×ˢ U n) f)
  have he {f : G × G → ℂ} (hf : MemLp f 2 (ν.prod ν)) : smooth f =ᵐ[ν.prod ν] f :=
    doubleWindowSmoothing_ae_eq ν hU hcof hUc hC hDiff hf
  have hk' (n : ι) : MemLp (smooth (k n)) 2 (ν.prod ν) := (hk n).ae_eq (he (hk n)).symm
  have hK₀' : MemLp (smooth K₀) 2 (ν.prod ν) := hK₀.ae_eq (he hK₀).symm
  have ht := tendsto_kernel_of_schatten_two ν h
  refine ⟨hk', hK₀', ht, ?_⟩
  have heK := (MemLp.toLp_eq_toLp_iff hK₀' hK₀).mpr (he hK₀)
  rw [heK]
  apply ht.congr
  intro n
  exact ((MemLp.toLp_eq_toLp_iff (hk' n) (hk n)).mpr (he (hk n))).symm

end Haar

end

end Masullo
