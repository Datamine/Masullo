import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

open Filter Metric Set Topology

namespace Masullo

/-- A circle can lie in a punctured domain while enclosing the omitted
point. The printed Cauchy coefficient formula then fails for a function
holomorphic throughout its domain. -/
theorem laurent_coefficient_contour_hole :
    let U : Set ℂ := {(2 : ℂ)}ᶜ
    let f : ℂ → ℂ := fun z => (z - 2)⁻¹
    IsOpen U ∧ IsConnected U ∧ DifferentiableOn ℂ f U ∧
      sphere (0 : ℂ) 3 ⊆ U ∧ (0 : ℂ) ∈ U ∩ ball 0 3 ∧
      (∮ z in C((0 : ℂ), (3 : ℝ)), f z / z) = 0 ∧ f 0 ≠ 0 := by
  dsimp only
  have h₀s : (0 : ℂ) ∉ sphere (0 : ℂ) 3 := by
    simp
  have h₂norm : ‖(2 : ℂ)‖ = (2 : ℝ) := by norm_num
  have h₂s : (2 : ℂ) ∉ sphere (0 : ℂ) 3 := by
    norm_num [mem_sphere, dist_zero_right, h₂norm]
  have h₂b : (2 : ℂ) ∈ ball (0 : ℂ) 3 := by
    norm_num [mem_ball, dist_zero_right, h₂norm]
  have h₀b : (0 : ℂ) ∈ ball (0 : ℂ) 3 := mem_ball_self (by norm_num)
  refine ⟨isClosed_singleton.isOpen_compl, ?_, ?_, ?_, ⟨by simp, h₀b⟩, ?_, by norm_num⟩
  · apply isConnected_compl_singleton_of_one_lt_rank
    rw [Complex.rank_real_complex]
    norm_num
  · intro z hz
    have hn : z - (2 : ℂ) ≠ 0 := sub_ne_zero.mpr (fun h => hz (mem_singleton_iff.mpr h))
    have hd : DifferentiableAt ℂ (fun w : ℂ => w - 2) z := by fun_prop
    exact (hd.inv hn).differentiableWithinAt
  · intro z hz hz₂
    exact h₂s ((mem_singleton_iff.mp hz₂) ▸ hz)
  · let A (z : ℂ) := (z - 2)⁻¹
    let B (z : ℂ) := (z - 0)⁻¹
    have hA : CircleIntegrable A 0 3 := by
      apply ContinuousOn.circleIntegrable'
      apply (continuous_id.sub continuous_const).continuousOn.inv₀
      intro z hz
      have hzs : z ∈ sphere (0 : ℂ) 3 := by simpa using hz
      apply sub_ne_zero.mpr
      intro h
      have he : z = (2 : ℂ) := h
      exact h₂s (he ▸ hzs)
    have hB : CircleIntegrable B 0 3 := by
      apply ContinuousOn.circleIntegrable'
      apply (continuous_id.sub continuous_const).continuousOn.inv₀
      intro z hz
      have hzs : z ∈ sphere (0 : ℂ) 3 := by simpa using hz
      apply sub_ne_zero.mpr
      intro h
      have he : z = (0 : ℂ) := h
      exact h₀s (he ▸ hzs)
    calc
      (∮ z in C((0 : ℂ), (3 : ℝ)), (z - 2)⁻¹ / z) =
          ∮ z in C((0 : ℂ), (3 : ℝ)), (2 : ℂ)⁻¹ • (A z - B z) := by
        apply circleIntegral.integral_congr (by norm_num)
        intro z hz
        have hz₀ : z ≠ 0 := fun h => h₀s (h ▸ hz)
        have hz₂ : z - (2 : ℂ) ≠ 0 := sub_ne_zero.mpr (fun h => h₂s (h ▸ hz))
        simp only [A, B, sub_zero, smul_eq_mul]
        field_simp [hz₀, hz₂]
        ring
      _ = 0 := by
        rw [circleIntegral.integral_smul, circleIntegral.integral_sub hA hB]
        change (2 : ℂ)⁻¹ • ((∮ z in C((0 : ℂ), (3 : ℝ)), (z - 2)⁻¹) -
          (∮ z in C((0 : ℂ), (3 : ℝ)), (z - 0)⁻¹)) = 0
        rw [circleIntegral.integral_sub_inv_of_mem_ball h₂b,
          circleIntegral.integral_sub_inv_of_mem_ball h₀b, sub_self, smul_zero]

end Masullo
