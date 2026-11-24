import Mathlib.Analysis.Complex.Poisson

open MeasureTheory Metric Set

namespace Masullo

private theorem circleIntegrable_inverse_squared {r : ℝ} (hr : 1 < r) :
    CircleIntegrable (fun u : ℂ => (‖u - 1‖ ^ 2)⁻¹) 0 r := by
  apply ContinuousOn.circleIntegrable (zero_lt_one.trans hr).le
  apply (continuous_norm.comp (continuous_id.sub continuous_const)).continuousOn.pow 2 |>.inv₀
  intro u hu
  have hun : ‖u‖ = r := by simpa [mem_sphere, dist_eq_norm] using hu
  intro he
  change ‖u - 1‖ ^ 2 = 0 at he
  have hzero : ‖u - 1‖ = 0 := sq_eq_zero_iff.mp he
  have : u = 1 := sub_eq_zero.mp (norm_eq_zero.mp hzero)
  simp [this] at hun
  exact hr.ne hun

/-- The normalized angular average of the squared complex-place kernel.
For normalized local modulus t = r², the angular average is exactly 1/(t-1). -/
theorem complexPlace_angular_average {r : ℝ} (hr : 1 < r) :
    Real.circleAverage (fun u : ℂ => ((‖u - 1‖ ^ 2)⁻¹ : ℝ)) 0 r = (r ^ 2 - 1)⁻¹ := by
  have hf : DiffContOnCl ℂ (fun _ : ℂ => (1 : ℂ)) (ball 0 r) :=
    ⟨differentiableOn_const _, continuous_const.continuousOn⟩
  have hball : (1 : ℂ) ∈ ball 0 r := by simpa [mem_ball, dist_eq_norm] using hr
  have h := hf.circleAverage_poissonKernel_smul hball
  have hr₀ : 0 < r := zero_lt_one.trans hr
  let f (u : ℂ) : ℝ := (‖u - 1‖ ^ 2)⁻¹
  have hcircle : CircleIntegrable f 0 r := circleIntegrable_inverse_squared hr
  have hrew : Real.circleAverage (poissonKernel 0 1 • (fun _ : ℂ => (1 : ℂ))) 0 r =
      Real.circleAverage (fun u : ℂ => (((r ^ 2 - 1) • f u : ℝ) : ℂ)) 0 r := by
    apply Real.circleAverage_congr_sphere
    intro u hu
    have hnorm : ‖u‖ = r := by
      simpa [mem_sphere, dist_eq_norm, abs_of_pos hr₀] using hu
    simp [poissonKernel_def, hnorm, f, div_eq_mul_inv, Complex.real_smul]
  rw [hrew] at h
  change Real.circleAverage (Complex.ofRealCLM ∘ ((r ^ 2 - 1 : ℝ) • f)) 0 r = 1 at h
  rw [Complex.ofRealCLM.circleAverage_comp_comm hcircle.const_smul, Real.circleAverage_smul] at h
  have hh : (r ^ 2 - 1) * Real.circleAverage f 0 r = 1 := by
    exact_mod_cast (show (((r ^ 2 - 1) * Real.circleAverage f 0 r : ℝ) : ℂ) = 1 from h)
  have hpos : 0 < r ^ 2 - 1 := by nlinarith
  rw [← one_div]
  exact (eq_div_iff hpos.ne').mpr (by simpa [mul_comm] using hh)

/-- The complex-place angular integral with a unitary character is bounded by
the same radial kernel, after normalizing the angular measure to mass one. -/
theorem complexPlace_weighted_angular_bound {r : ℝ} (hr : 1 < r) (weight : ℂ → ℂ)
    (hw : ∀ u ∈ sphere 0 r, ‖weight u‖ ≤ 1) :
    ‖Real.circleAverage (fun u => ((‖u - 1‖ ^ 2)⁻¹ : ℝ) • weight u) 0 r‖ ≤
      (r ^ 2 - 1)⁻¹ := by
  rw [← complexPlace_angular_average hr]
  unfold Real.circleAverage
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity), smul_eq_mul]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  apply intervalIntegral.norm_integral_le_of_norm_le (by positivity) _
    (circleIntegrable_inverse_squared hr)
  refine Filter.Eventually.of_forall fun θ _ => ?_
  let u := circleMap 0 r θ
  have hu : u ∈ sphere 0 r := circleMap_mem_sphere 0 (zero_lt_one.trans hr).le θ
  have hnorm := hw u hu
  change ‖((‖u - 1‖ ^ 2)⁻¹ : ℝ) • weight u‖ ≤ (‖u - 1‖ ^ 2)⁻¹
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact mul_le_of_le_one_right (by positivity) hnorm

end Masullo
