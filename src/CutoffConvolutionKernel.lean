import WeightedKernelDiagonal
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.Unique

open Filter Function MeasureTheory Set Topology
open scoped ENNReal Pointwise

namespace Masullo

noncomputable section

section Convolution

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure] {w : G → ℝ}

/- The bounded measurable symbol argument follows RiemannMasullo commit 20a1db3,
   under Apache-2.0. See External/PROVENANCE.md. -/

/-- The cutoff kernel against the weighted measure. The density is in the
integration variable, so writing the action against Haar measure cancels it. -/
def cutoffConvolutionKernel (w : G → ℝ) (ρ φ : G → ℂ) (z : G × G) : ℂ :=
  ρ z.1 * φ (z.1 * z.2⁻¹) / (w z.2 : ℂ)

theorem cutoffConvolutionKernel_memLp_of_measurable_cutoff
    (hw : Continuous w) (hpos : ∀ x, 0 < w x)
    {ρ φ : G → ℂ} (hρ : Measurable ρ) (hφ : AEMeasurable φ μ)
    (hρb : ∃ R : ℝ, ∀ x, ‖ρ x‖ ≤ R)
    (hφb : ∃ C : ℝ, ∀ x, ‖φ x‖ ≤ C)
    (hρc : HasCompactSupport ρ) (hφc : HasCompactSupport φ) :
    MemLp (cutoffConvolutionKernel w ρ φ) 2
      ((μ.withDensity (fun x => ENNReal.ofReal (w x))).prod
        (μ.withDensity (fun x => ENNReal.ofReal (w x)))) := by
  let ν := μ.withDensity (fun x => ENNReal.ofReal (w x))
  letI : IsLocallyFiniteMeasure ν := IsLocallyFiniteMeasure.withDensity_ofReal hw
  let K : Set G := tsupport ρ
  let J : Set G := tsupport φ
  let L := J⁻¹ * K
  have hL : IsCompact L := hφc.inv.mul hρc
  have hs : support (cutoffConvolutionKernel w ρ φ) ⊆ K ×ˢ L := by
    intro z hz
    have hρz : ρ z.1 ≠ 0 := fun h => hz (by simp [cutoffConvolutionKernel, h])
    have hφz : φ (z.1 * z.2⁻¹) ≠ 0 := fun h => hz (by simp [cutoffConvolutionKernel, h])
    have hKz : z.1 ∈ K := subset_closure hρz
    have hJz : z.1 * z.2⁻¹ ∈ J := subset_closure hφz
    exact ⟨hKz, ⟨(z.1 * z.2⁻¹)⁻¹, by simpa only [Set.mem_inv, inv_inv] using hJz,
      z.1, hKz, by simp [mul_inv_rev, mul_assoc]⟩⟩
  obtain ⟨R, hR⟩ := hρb
  obtain ⟨B, hB⟩ := hL.exists_bound_of_continuousOn
    (f := fun y => (w y)⁻¹) (hw.inv₀ fun y => (hpos y).ne').continuousOn
  obtain ⟨C, hC⟩ := hφb
  have hbound (p : G × G) : ‖cutoffConvolutionKernel w ρ φ p‖ ≤ max R 0 * max C 0 * max B 0 := by
    by_cases hp : cutoffConvolutionKernel w ρ φ p = 0
    · rw [hp, norm_zero]
      positivity
    obtain ⟨_, hy⟩ := hs hp
    unfold cutoffConvolutionKernel
    rw [div_eq_mul_inv, norm_mul, norm_mul, norm_inv, Complex.norm_real, ← norm_inv]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul ((hR _).trans (le_max_left _ _)) ((hC _).trans (le_max_left _ _))
        (norm_nonneg _) (le_max_right _ _)) (norm_nonneg _) |>.trans
      (mul_le_mul_of_nonneg_left ((hB _ hy).trans (le_max_left _ _)) (by positivity))
  have hν : ν ≪ μ := withDensity_absolutelyContinuous μ _
  have hdiv : AEMeasurable (fun p : G × G => φ (p.1 * p.2⁻¹)) (μ.prod μ) := by
    have h := hφ.comp_quasiMeasurePreserving (quasiMeasurePreserving_div μ μ)
    change AEMeasurable (fun p : G × G => φ (p.1 / p.2)) (μ.prod μ) at h
    simpa only [div_eq_mul_inv] using h
  have hmeas : AEMeasurable (cutoffConvolutionKernel w ρ φ) (μ.prod μ) :=
    ((hρ.comp measurable_fst).aemeasurable.mul hdiv).div
      (Complex.measurable_ofReal.comp (hw.measurable.comp measurable_snd)).aemeasurable
  exact (memLp_top_of_bound (hmeas.mono_ac (hν.prod hν)).aestronglyMeasurable _
    (.of_forall hbound)).mono_exponent_of_measure_support_ne_top
    (fun p hp => by_contra fun h => hp (hs h)) (hρc.prod hL).measure_lt_top.ne le_top

theorem cutoffConvolutionKernel_memLp_of_aeMeasurable
    (hw : Continuous w) (hpos : ∀ x, 0 < w x)
    {ρ φ : G → ℂ} (hρ : Continuous ρ) (hφ : AEMeasurable φ μ)
    (hφb : ∃ C : ℝ, ∀ x, ‖φ x‖ ≤ C)
    (hρc : HasCompactSupport ρ) (hφc : HasCompactSupport φ) :
    MemLp (cutoffConvolutionKernel w ρ φ) 2
      ((μ.withDensity (fun x => ENNReal.ofReal (w x))).prod
        (μ.withDensity (fun x => ENNReal.ofReal (w x)))) :=
  cutoffConvolutionKernel_memLp_of_measurable_cutoff μ hw hpos hρ.measurable hφ
    (hρc.exists_bound_of_continuous hρ) hφb hρc hφc

theorem cutoffConvolutionKernel_memLp
    (hw : Continuous w) (hpos : ∀ x, 0 < w x)
    {ρ φ : G → ℂ} (hρ : Continuous ρ) (hφ : Continuous φ)
    (hρc : HasCompactSupport ρ) (hφc : HasCompactSupport φ) :
    MemLp (cutoffConvolutionKernel w ρ φ) 2
      ((μ.withDensity (fun x => ENNReal.ofReal (w x))).prod
        (μ.withDensity (fun x => ENNReal.ofReal (w x)))) :=
  cutoffConvolutionKernel_memLp_of_aeMeasurable μ hw hpos hρ hφ.measurable.aemeasurable
    (hφc.exists_bound_of_continuous hφ) hρc hφc

/-- The actual L² integral operator of the cutoff kernel acts by the truncated
Haar convolution, with the same orientation as (10.4.3.34). -/
theorem cutoffConvolutionKernel_apply_of_measurable_cutoff [SigmaFinite μ]
    (hw : Continuous w) (hpos : ∀ x, 0 < w x)
    {ρ φ : G → ℂ} (hρ : Measurable ρ) (hφ : AEMeasurable φ μ)
    (hρb : ∃ R : ℝ, ∀ x, ‖ρ x‖ ≤ R)
    (hφb : ∃ C : ℝ, ∀ x, ‖φ x‖ ≤ C)
    (hρc : HasCompactSupport ρ) (hφc : HasCompactSupport φ)
    (f : G →₂[μ.withDensity (fun x => ENNReal.ofReal (w x))] ℂ) :
    let h := cutoffConvolutionKernel_memLp_of_measurable_cutoff μ hw hpos hρ hφ hρb hφb hρc hφc
    ∀ᵐ x ∂μ, kernelIntegralOperator (h.toLp (cutoffConvolutionKernel w ρ φ)) f x =
      ρ x * ∫ y, φ y * f (y⁻¹ * x) ∂μ := by
  letI : Measure.Regular μ := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _
  let h := cutoffConvolutionKernel_memLp_of_measurable_cutoff μ hw hpos hρ hφ hρb hφb hρc hφc
  filter_upwards [kernelIntegralOperator_haarDensity_apply μ w hw hpos h f] with x hx
  rw [hx.2]
  have he (y : G) : (w y : ℂ) * cutoffConvolutionKernel w ρ φ (x, y) * f y =
      ρ x * (φ (x * y⁻¹) * f y) := by
    unfold cutoffConvolutionKernel
    rw [mul_comm (w y : ℂ), div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr (hpos y).ne')]
    exact mul_assoc _ _ _
  simp_rw [he, integral_const_mul]
  congr 1
  let F (y : G) := φ (x * y⁻¹) * f y
  have hchange : (∫ y, F (y⁻¹ * x) ∂μ) = ∫ y, F y ∂μ := by
    rw [integral_inv_eq_self (fun y => F (y * x)) μ, integral_mul_right_eq_self F x]
  simpa only [F, mul_inv_rev, inv_inv, ← mul_assoc, mul_inv_cancel, one_mul] using hchange.symm

theorem cutoffConvolutionKernel_apply_of_aeMeasurable [SigmaFinite μ]
    (hw : Continuous w) (hpos : ∀ x, 0 < w x)
    {ρ φ : G → ℂ} (hρ : Continuous ρ) (hφ : AEMeasurable φ μ)
    (hφb : ∃ C : ℝ, ∀ x, ‖φ x‖ ≤ C)
    (hρc : HasCompactSupport ρ) (hφc : HasCompactSupport φ)
    (f : G →₂[μ.withDensity (fun x => ENNReal.ofReal (w x))] ℂ) :
    let h := cutoffConvolutionKernel_memLp_of_aeMeasurable μ hw hpos hρ hφ hφb hρc hφc
    ∀ᵐ x ∂μ, kernelIntegralOperator (h.toLp (cutoffConvolutionKernel w ρ φ)) f x =
      ρ x * ∫ y, φ y * f (y⁻¹ * x) ∂μ :=
  cutoffConvolutionKernel_apply_of_measurable_cutoff μ hw hpos hρ.measurable hφ
    (hρc.exists_bound_of_continuous hρ) hφb hρc hφc f

theorem cutoffConvolutionKernel_apply [SigmaFinite μ]
    (hw : Continuous w) (hpos : ∀ x, 0 < w x)
    {ρ φ : G → ℂ} (hρ : Continuous ρ) (hφ : Continuous φ)
    (hρc : HasCompactSupport ρ) (hφc : HasCompactSupport φ)
    (f : G →₂[μ.withDensity (fun x => ENNReal.ofReal (w x))] ℂ) :
    let h := cutoffConvolutionKernel_memLp μ hw hpos hρ hφ hρc hφc
    ∀ᵐ x ∂μ, kernelIntegralOperator (h.toLp (cutoffConvolutionKernel w ρ φ)) f x =
      ρ x * ∫ y, φ y * f (y⁻¹ * x) ∂μ :=
  cutoffConvolutionKernel_apply_of_aeMeasurable μ hw hpos hρ hφ.measurable.aemeasurable
    (hφc.exists_bound_of_continuous hφ) hρc hφc f

/-- The squared Hilbert–Schmidt norm of the truncated convolution is the
squared kernel norm in the product of the two weighted Haar measures. -/
theorem cutoffConvolutionKernel_hilbertSchmidt
    (hw : Continuous w) (hpos : ∀ x, 0 < w x)
    {ρ φ : G → ℂ} (hρ : Continuous ρ) (hφ : AEMeasurable φ μ)
    (hφb : ∃ C : ℝ, ∀ x, ‖φ x‖ ≤ C) (hρc : HasCompactSupport ρ) (hφc : HasCompactSupport φ) :
    let ν := μ.withDensity (fun x => ENNReal.ofReal (w x))
    let k := cutoffConvolutionKernel w ρ φ
    ∃ (hk : MemLp k 2 (ν.prod ν)),
      (∀ f : G →₂[ν] ℂ, ∀ᵐ x ∂μ, kernelIntegralOperator (hk.toLp k) f x =
        ρ x * ∫ y, φ y * f (y⁻¹ * x) ∂μ) ∧
      IsCompactOperator (kernelIntegralOperator (hk.toLp k)) ∧
      ∃ (s : Set (G →₂[ν] ℂ)) (_ : s.Countable) (b : HilbertBasis s ℂ (G →₂[ν] ℂ)),
        Summable (fun i => ‖kernelIntegralOperator (hk.toLp k) (b i)‖ ^ 2) ∧
          (∑' i, ‖kernelIntegralOperator (hk.toLp k) (b i)‖ ^ 2) = ‖hk.toLp k‖ ^ 2 := by
  intro ν k
  letI : IsLocallyFiniteMeasure ν := IsLocallyFiniteMeasure.withDensity_ofReal hw
  let hk := cutoffConvolutionKernel_memLp_of_aeMeasurable μ hw hpos hρ hφ hφb hρc hφc
  exact ⟨hk, cutoffConvolutionKernel_apply_of_aeMeasurable μ hw hpos hρ hφ hφb hρc hφc,
    radonKernel_hilbertSchmidt ν (hk.toLp k)⟩

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] in
/-- On the pointwise diagonal of the displayed kernel, the source density
cancels against the weight of the integration measure. -/
theorem cutoffConvolutionKernel_integrable_densityDiagonal
    (hpos : ∀ x, 0 < w x) {ρ φ : G → ℂ}
    (hρ : Continuous ρ) (hρc : HasCompactSupport ρ) :
    Integrable (fun x => cutoffConvolutionKernel w ρ φ (x, x) * (w x : ℂ)) μ ∧
      (∫ x, cutoffConvolutionKernel w ρ φ (x, x) * (w x : ℂ) ∂μ) =
        (∫ x, ρ x ∂μ) * φ 1 := by
  have h (x : G) : cutoffConvolutionKernel w ρ φ (x, x) * (w x : ℂ) = ρ x * φ 1 := by
    rw [cutoffConvolutionKernel, mul_inv_cancel,
      div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr (hpos x).ne')]
  simp only [h]
  exact ⟨(hρ.integrable_of_hasCompactSupport hρc).mul_const _, integral_mul_const _ _⟩

end Convolution

end

end Masullo
