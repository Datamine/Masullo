import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open Filter MeasureTheory Set Topology

noncomputable section

namespace Masullo

/-- Two kernels can agree on product measure and differ everywhere on the
diagonal. This obstruction applies to any nonatomic space with a measurable diagonal. -/
theorem null_diagonal {X : Type*} [MeasurableSpace X] [MeasurableEq X]
    (μ : Measure X) [SFinite μ] [NullSingletonClass μ] :
    μ.prod μ (diagonal X) = 0 := by
  rw [Measure.prod_apply measurableSet_diagonal]
  have h (x : X) : Prod.mk x ⁻¹' diagonal X = {x} := by
    ext y
    simp [mem_diagonal_iff, eq_comm]
  simp_rw [h, measure_singleton, lintegral_zero]

theorem kernel_ae_eq_with_different_diagonal :
    ∃ f g : ℝ × ℝ → ℂ, Measurable f ∧ Measurable g ∧
      f =ᵐ[(volume : Measure ℝ).prod volume] g ∧
      (∀ x, f (x, x) = 1 ∧ g (x, x) = 0) := by
  let f : ℝ × ℝ → ℂ := (diagonal ℝ).indicator (fun _ => 1)
  refine ⟨f, 0, measurable_const.indicator measurableSet_diagonal, measurable_const, ?_, ?_⟩
  · have hae : ∀ᵐ x ∂(volume : Measure ℝ).prod volume, x ∉ diagonal ℝ := by
      rw [ae_iff]
      simp only [not_not]
      change (volume.prod volume) (diagonal ℝ) = 0
      exact null_diagonal (volume : Measure ℝ)
    filter_upwards [hae] with x hx
    exact indicator_of_notMem hx _
  · intro x
    simp [f, mem_diagonal_iff]

/-- A one-dimensional averaged kernel in a neighborhood of its diagonal. -/
def diagonalAverage (k : ℝ → ℝ → ℂ) (r x : ℝ) : ℂ :=
  ((2 * r)⁻¹ : ℝ) • ∫ t in -r..r, k x (x + t)

private theorem diagonalAverage_sub_bound {k : ℝ → ℝ → ℂ} {x r M : ℝ} (hr : 0 < r)
    (hc : Continuous (k x))
    (h : ∀ t ∈ Icc (-r) r, ‖k x (x + t) - k x x‖ ≤ M) :
    ‖diagonalAverage k r x - k x x‖ ≤ M := by
  have hr' : 0 < 2 * r := by positivity
  have hf : IntervalIntegrable (fun t => k x (x + t)) volume (-r) r :=
    (hc.comp (continuous_const.add continuous_id)).intervalIntegrable _ _
  have he : diagonalAverage k r x - k x x =
      ((2 * r)⁻¹ : ℝ) • ∫ t in -r..r, (k x (x + t) - k x x) := by
    rw [intervalIntegral.integral_sub hf intervalIntegrable_const, smul_sub]
    apply congrArg (fun c => diagonalAverage k r x - c)
    rw [intervalIntegral.integral_const, smul_smul]
    rw [show r - -r = 2 * r by ring, inv_mul_cancel₀ hr'.ne', one_smul]
  rw [he, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hr'.le)]
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := -r) (b := r) (C := M) (f := fun t => k x (x + t) - k x x) (fun t ht => by
      rw [Set.uIoc_of_le (by linarith)] at ht
      exact h t ⟨ht.1.le, ht.2⟩)
  calc
    _ ≤ (2 * r)⁻¹ * (M * |r - -r|) := mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = M := by rw [show r - -r = 2 * r by ring, abs_of_pos hr']
                field_simp

/-- Continuity in the second variable determines the pointwise averaged trace.
The one-sided approach keeps all averaging intervals nondegenerate. -/
theorem diagonalAverage_tendsto {k : ℝ → ℝ → ℂ} (x : ℝ) (hc : Continuous (k x)) :
    Tendsto (fun r => diagonalAverage k r x) (𝓝[>] 0) (𝓝 (k x x)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hcont⟩ := Metric.continuousAt_iff.mp (hc.continuousAt (x := x)) (ε / 2) (by positivity)
  have hr₀ : ∀ᶠ r : ℝ in 𝓝[>] 0, r ∈ Ioi 0 := self_mem_nhdsWithin
  have hrδ : ∀ᶠ r : ℝ in 𝓝[>] 0, r < δ :=
    (nhdsWithin_le_nhds (gt_mem_nhds hδ) : {r : ℝ | r < δ} ∈ 𝓝[>] 0)
  filter_upwards [hr₀, hrδ] with r hr hrd
  rw [dist_eq_norm]
  refine (diagonalAverage_sub_bound (M := ε / 2) hr hc ?_).trans_lt (by linarith)
  intro t ht
  apply le_of_lt
  rw [← dist_eq_norm]
  apply hcont
  rw [Real.dist_eq, add_sub_cancel_left]
  exact (abs_le.mpr ht).trans_lt hrd

/-- A sufficient integrated-diagonal theorem with an explicit integrable
majorant and measurability. This is a model of the limit needed in §12.2. -/
theorem integral_diagonalAverage_tendsto {k : ℝ → ℝ → ℂ} {μ : Measure ℝ}
    (r : ℕ → ℝ) (hpositive : ∀ n, 0 < r n) (hr : Tendsto r atTop (𝓝 0))
    (hc : ∀ x, Continuous (k x))
    (hmeas : ∀ n, AEStronglyMeasurable (diagonalAverage k (r n)) μ)
    (majorant : ℝ → ℝ) (hi : Integrable majorant μ)
    (hbound : ∀ n, ∀ᵐ x ∂μ, ‖diagonalAverage k (r n) x‖ ≤ majorant x) :
    Tendsto (fun n => ∫ x, diagonalAverage k (r n) x ∂μ) atTop (𝓝 (∫ x, k x x ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence majorant hmeas hi hbound
  have hr' : Tendsto r atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hr, Eventually.of_forall hpositive⟩
  exact Eventually.of_forall fun x => (diagonalAverage_tendsto x (hc x)).comp hr'

end Masullo
