import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Instances.Int

open Filter Function Set Topology
open scoped ContDiff

namespace Masullo

noncomputable section

/-- Periodization by a cyclic translation subgroup in the logarithmic
coordinate. -/
def integerPeriodization (d : ℝ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∑' m : ℤ, f (x + d * (m : ℝ))

theorem compact_integerTranslate_support_finite {K : Set ℝ} (hK : IsCompact K)
    {f : ℝ → ℂ} (hf : support f ⊆ K) {d : ℝ} (hd : d ≠ 0) (x : ℝ) :
    (support fun m : ℤ => f (x + d * (m : ℝ))).Finite := by
  let e := (Homeomorph.mulLeft₀ d hd).trans (Homeomorph.addLeft x)
  have hEmb : IsClosedEmbedding (fun m : ℤ => x + d * (m : ℝ)) :=
    e.isClosedEmbedding.comp Int.isClosedEmbedding_coe_real
  exact (hEmb.isCompact_preimage hK).finite_of_discrete.subset fun _ hm => hf hm

theorem compact_integerTranslate_summable {K : Set ℝ} (hK : IsCompact K)
    {f : ℝ → ℂ} (hf : support f ⊆ K) {d : ℝ} (hd : d ≠ 0) (x : ℝ) :
    Summable (fun m : ℤ => f (x + d * (m : ℝ))) := by
  classical
  let h := compact_integerTranslate_support_finite hK hf hd x
  refine summable_of_ne_finset_zero (s := h.toFinset) fun m hm => ?_
  by_contra hn
  exact hm (h.mem_toFinset.mpr hn)

private theorem continuous_support_subset_interior {f : ℝ → ℂ} {K : Set ℝ}
    (hf : Continuous f) (hK : support f ⊆ K) :
    support f ⊆ interior K :=
  (isClosed_eq hf continuous_const).isOpen_compl.subset_interior_iff.mpr hK

/-- The closed interval of one period covers all orbits, while every
continuous test supported there periodizes to zero at the endpoint. This
is the obstruction to the coverage criterion of Proposition 4.2.2.2. -/
theorem printed_compact_periodization_coverage_fails :
    (∀ x : ℝ, ∃ n : ℤ, x + n ∈ Icc (0 : ℝ) 1) ∧
      ∀ f : ℝ → ℂ, Continuous f → support f ⊆ Icc (0 : ℝ) 1 →
        integerPeriodization 1 f 0 = 0 := by
  constructor
  · intro x
    refine ⟨-⌊x⌋, ?_⟩
    have hl := Int.floor_le x
    have hr := Int.lt_floor_add_one x
    simp only [Int.cast_neg, mem_Icc]
    constructor <;> linarith
  · intro f hf hK
    have h := continuous_support_subset_interior hf hK
    rw [interior_Icc] at h
    have hz (n : ℤ) : f (0 + 1 * (n : ℝ)) = 0 := by
      by_contra hn
      have hb : (n : ℝ) ∈ Ioo (0 : ℝ) 1 := h (by simpa using hn)
      have hl : (0 : ℤ) < n := by exact_mod_cast hb.1
      have hr : n < (1 : ℤ) := by exact_mod_cast hb.2
      omega
    simp only [integerPeriodization, hz, tsum_zero]

private def periodizationBump : ContDiffBump (1 / 2 : ℝ) where
  rIn := 1 / 8
  rOut := 1 / 4
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

private def periodizationBumpC (x : ℝ) : ℂ := ↑(periodizationBump x)

private theorem periodizationBump_support : support periodizationBumpC ⊆ Ioo (0 : ℝ) 1 := by
  intro x hx
  have hB : x ∈ support (periodizationBump : ℝ → ℝ) := by
    intro hz
    exact hx (by simp [periodizationBumpC, show periodizationBump x = 0 from hz])
  rw [periodizationBump.support_eq] at hB
  have ha : |x - 1 / 2| < (1 / 4 : ℝ) := by
    simpa only [Metric.mem_ball, Real.dist_eq, periodizationBump] using hB
  obtain ⟨hL, hR⟩ := abs_lt.mp ha
  exact ⟨by linarith, by linarith⟩

/-- At the printed symmetric support bound in 4.2.2.2(2), the proposed
solution would have support in a singleton. A nonzero smooth test in
the kernel of periodization disproves this bound. -/
theorem printed_periodic_difference_support_fails :
    ∃ f : ℝ → ℂ, ContDiff ℝ ∞ f ∧ support f ⊆ Icc (-1 : ℝ) 1 ∧
      (∀ x, integerPeriodization 1 f x = 0) ∧ f (1 / 2) = 1 ∧
      ¬ ∃ ψ : ℝ → ℂ, Continuous ψ ∧ support ψ ⊆ Icc (0 : ℝ) 0 ∧
        ∀ x, ψ x - ψ (x + 1) = f x := by
  let g := periodizationBumpC
  let f (x : ℝ) := g x - g (x + 1)
  have hg := periodizationBump_support
  have hC : ContDiff ℝ ∞ g := Complex.ofRealCLM.contDiff.comp periodizationBump.contDiff
  have hval : f (1 / 2) = 1 := by
    have hb : g (1 / 2) = 1 := by
      change (periodizationBump (1 / 2) : ℂ) = 1
      rw [periodizationBump.one_of_mem_closedBall]
      · simp
      · simp [Metric.mem_closedBall, periodizationBump]
    have hz : g (1 / 2 + 1) = 0 := by
      by_contra hn
      have h : 1 / 2 + 1 ∈ Ioo (0 : ℝ) 1 := hg hn
      norm_num at h
    change g (1 / 2) - g (1 / 2 + 1) = 1
    rw [hb, hz, sub_zero]
  refine ⟨f, hC.sub (hC.comp (by fun_prop)), ?_, ?_, hval, ?_⟩
  · intro x hx
    by_contra! hn
    have h₁ : g x = 0 := by
      by_contra he
      have hh : x ∈ Ioo (0 : ℝ) 1 := hg he
      exact hn ⟨by linarith [hh.1], hh.2.le⟩
    have h₂ : g (x + 1) = 0 := by
      by_contra he
      have hh : x + 1 ∈ Ioo (0 : ℝ) 1 := hg he
      exact hn ⟨by linarith [hh.1], by linarith [hh.2]⟩
    exact hx (by simp [f, h₁, h₂])
  · intro x
    have h₁ := compact_integerTranslate_summable isCompact_Icc
      (hg.trans Ioo_subset_Icc_self) (by norm_num : (1 : ℝ) ≠ 0) x
    have h₂ : Summable (fun m : ℤ => g (x + m + 1)) := by
      have hEq : (fun m : ℤ => g (x + m + 1)) =
          (fun m : ℤ => g (x + 1 * (m : ℝ))) ∘ Equiv.addRight (1 : ℤ) := by
        funext m
        simp [Equiv.addRight, add_assoc]
      rw [hEq]
      exact (Equiv.addRight (1 : ℤ)).summable_iff.mpr h₁
    have hEq : (∑' m : ℤ, g (x + m + 1)) = ∑' m : ℤ, g (x + m) := by
      have h := (Equiv.addRight (1 : ℤ)).tsum_eq (fun m : ℤ => g (x + m))
      simpa [Equiv.addRight, add_assoc] using h
    change (∑' m : ℤ, (g (x + 1 * (m : ℝ)) - g (x + 1 * (m : ℝ) + 1))) = 0
    simp only [one_mul] at h₁ ⊢
    rw [h₁.tsum_sub h₂, hEq, sub_self]
  · rintro ⟨ψ, hψ, hK, hEq⟩
    have h := continuous_support_subset_interior hψ hK
    rw [interior_Icc, Ioo_self] at h
    have hψ₀ (x : ℝ) : ψ x = 0 := by
      by_contra hx
      exact h hx
    have hz := hEq (1 / 2)
    rw [hψ₀, hψ₀, sub_self, hval] at hz
    exact zero_ne_one hz

end
end Masullo
