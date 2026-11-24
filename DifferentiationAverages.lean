import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Algebra.Order.Group.Pointwise.Interval

open Set Filter Topology MeasureTheory
open scoped ENNReal Pointwise

namespace Masullo

noncomputable section

/-- A fixed symmetric interval average of the real quadratic function. -/
def symmetricQuadraticAverage (r x : ℝ) : ℝ :=
  (2 * r)⁻¹ * ∫ y in Icc (x - r) (x + r), y ^ 2

theorem symmetricQuadraticAverage_eq {r : ℝ} (hr : 0 < r) (x : ℝ) :
    symmetricQuadraticAverage r x = x ^ 2 + r ^ 2 / 3 := by
  unfold symmetricQuadraticAverage
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith : x - r ≤ x + r),
    integral_pow]
  norm_num
  field_simp [hr.ne']
  ring

/-- The global uniform continuity claimed in A.5.4.1(1) fails at every
positive radius, even for a smooth locally integrable function on ℝ. -/
theorem not_uniformContinuous_symmetricQuadraticAverage {r : ℝ} (hr : 0 < r) :
    ¬ UniformContinuous (symmetricQuadraticAverage r) := by
  intro h
  obtain ⟨δ, hδ, hosc⟩ := Metric.uniformContinuous_iff.mp h 1 zero_lt_one
  let x : ℝ := 1 / δ
  let y : ℝ := x + δ / 2
  have hxy : dist x y < δ := by
    rw [Real.dist_eq, show x - y = -(δ / 2) by dsimp [y]; ring, abs_neg,
      abs_of_nonneg (by positivity : 0 ≤ δ / 2)]
    linarith
  have hdiff : symmetricQuadraticAverage r y - symmetricQuadraticAverage r x =
      1 + (δ / 2) ^ 2 := by
    rw [symmetricQuadraticAverage_eq hr, symmetricQuadraticAverage_eq hr]
    dsimp [x, y]
    field_simp [hδ.ne']
    ring
  have hd := hosc hxy
  rw [dist_comm, Real.dist_eq, hdiff, abs_of_nonneg (by positivity)] at hd
  linarith [sq_nonneg (δ / 2)]

/-- The intervals of radius `1 / (k + 1)` meet the hypotheses of the paper's
real additive D′-sequence: positive finite volumes, nesting, cofinality and
uniform adjacent-stage doubling. -/
theorem real_interval_doubling_basis :
    let U : ℕ → Set ℝ := fun n => Icc (-(1 / ((n : ℝ) + 1))) (1 / ((n : ℝ) + 1))
    (∀ n, 0 ∈ U n ∧ MeasurableSet (U n) ∧ 0 < volume (U n) ∧ volume (U n) < ⊤) ∧
    Antitone U ∧
    (∀ V ∈ 𝓝 (0 : ℝ), ∃ n, U n ⊆ V) ∧
    (∀ n, 0 < volume (U (n + 1) + U n) ∧ volume (U (n + 1) + U n) < 4 * volume (U (n + 1))) := by
  let r (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
  let U (n : ℕ) : Set ℝ := Icc (-r n) (r n)
  have hr (n : ℕ) : 0 < r n := by dsimp [r]; positivity
  have hvol (n : ℕ) : volume (U n) = ENNReal.ofReal (2 * r n) := by
    simp only [U, Real.volume_Icc]
    congr 1
    ring
  change (∀ n, 0 ∈ U n ∧ MeasurableSet (U n) ∧ 0 < volume (U n) ∧ volume (U n) < ⊤) ∧
    Antitone U ∧ (∀ V ∈ 𝓝 (0 : ℝ), ∃ n, U n ⊆ V) ∧ _
  have hzero (n : ℕ) : 0 ∈ U n := ⟨neg_nonpos.mpr (hr n).le, (hr n).le⟩
  have hpos (n : ℕ) : 0 < volume (U n) := by rw [hvol, ENNReal.ofReal_pos]; positivity
  refine ⟨fun n => ⟨hzero n, measurableSet_Icc, hpos n, by rw [hvol]; exact ENNReal.ofReal_lt_top⟩,
    ?_, ?_, ?_⟩
  · intro m n hmn
    have h : r n ≤ r m := by
      apply one_div_le_one_div_of_le (by positivity : 0 < (m : ℝ) + 1)
      exact add_le_add (by exact_mod_cast hmn) le_rfl
    exact Icc_subset_Icc (neg_le_neg h) h
  · intro V hV
    obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp hV
    have he : ∀ᶠ n in atTop, r n < ε :=
      tendsto_one_div_add_atTop_nhds_zero_nat.eventually (gt_mem_nhds hε)
    obtain ⟨n, hn⟩ := he.exists
    refine ⟨n, fun x hx => hsub ?_⟩
    have hx' : |x| ≤ r n := abs_le.mpr hx
    simpa [Metric.mem_ball, Real.dist_eq] using hx'.trans_lt hn
  · intro n
    have hin : U (n + 1) ⊆ U (n + 1) + U n := by
      intro z hz
      exact ⟨z, hz, 0, hzero n, add_zero z⟩
    refine ⟨(hpos _).trans_le (measure_mono hin), ?_⟩
    have hsum : volume (U (n + 1) + U n) ≤ ENNReal.ofReal (2 * (r (n + 1) + r n)) := by
      refine (measure_mono (Icc_add_Icc_subset _ _ _ _)).trans_eq ?_
      rw [Real.volume_Icc]
      congr 1
      ring
    have hratio : r n ≤ 2 * r (n + 1) := by
      dsimp [r]
      norm_cast
      push_cast
      have h₁ : 0 < (n : ℝ) + 1 := by positivity
      have h₂ : 0 < (n : ℝ) + 1 + 1 := by positivity
      rw [mul_one_div, div_le_div_iff₀ h₁ h₂]
      linarith
    rw [hvol, ← show ENNReal.ofReal 4 = 4 by norm_num, ← ENNReal.ofReal_mul (by norm_num : 0 ≤ (4 : ℝ))]
    have hstrict : 2 * (r (n + 1) + r n) < 4 * (2 * r (n + 1)) := by
      linarith [hr (n + 1)]
    exact hsum.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr hstrict)

theorem square_locallyIntegrable : LocallyIntegrable (fun x : ℝ => x ^ 2) volume :=
  (continuous_id.pow 2).locallyIntegrable

end

end Masullo
