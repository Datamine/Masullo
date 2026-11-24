import PeriodicDerivativeTopology
import PeriodicDifference
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

open Function Set
open scoped ContDiff

namespace Masullo

noncomputable section

/-- The logarithmic interval for `b · [1 / a, a]` covers the quotient
by positive periods `log γ` under the manuscript's strict length condition. -/
theorem compact_multipleInterval_interior_coverage {a b γ : ℝ}
    (ha : 1 < a) (hb : 0 < b) (hγ : 1 < γ) (hwidth : Real.log γ < 2 * Real.log a) :
    ∀ x : ℝ, ∃ n : ℤ,
      x + Real.log γ * (n : ℝ) ∈ interior (Icc (Real.log (b / a)) (Real.log (b * a))) := by
  have ha₀ : 0 < a := zero_lt_one.trans ha
  rw [interior_Icc, Real.log_div hb.ne' ha₀.ne', Real.log_mul hb.ne' ha₀.ne']
  exact openInterval_covers_integerTranslations (Real.log_pos hγ) (by linarith)

/-- In the original multiplicative coordinate the corrected support is
`[γ * lo, hi]` and the equation holds with its actual support union. -/
theorem compact_multiplicative_periodization_difference {lo hi γ : ℝ} {f : ℝ → ℂ}
    (hlo : 0 < lo) (hhi : 0 < hi) (hγ : 1 < γ)
    (hf : support f ⊆ Icc lo hi) (hC : ContDiffOn ℝ ∞ f (Ioi 0))
    (hzero : ∀ x, integerPeriodization (Real.log γ) (f ∘ Real.exp) x = 0) :
    ∃ ψ : ℝ → ℂ, ContDiffOn ℝ ∞ ψ (Ioi 0) ∧ support ψ ⊆ Icc (γ * lo) hi ∧
      (∀ t > 0, ψ t - ψ (γ * t) = f t) ∧
      support f ⊆ Icc (γ * lo) hi ∪ ((fun t : ℝ => γ * t) ⁻¹' Icc (γ * lo) hi) := by
  have hlogSupp : support (f ∘ Real.exp) ⊆ Icc (Real.log lo) (Real.log hi) := by
    intro x hx
    have hx' := hf hx
    exact ⟨by simpa only [Real.log_exp] using Real.log_le_log hlo hx'.1,
      (Real.le_log_iff_exp_le hhi).mpr hx'.2⟩
  have hlogC : ContDiff ℝ ∞ (f ∘ Real.exp) := by
    rw [← contDiffOn_univ]
    exact hC.comp Real.contDiff_exp.contDiffOn (fun x _ => Real.exp_pos x)
  obtain ⟨g, hgC, hg, he⟩ :=
    compact_periodization_difference hlogSupp hlogC (Real.log_pos hγ) hzero
  let ψ (t : ℝ) := if 0 < t then g (Real.log t) else 0
  have hψC : ContDiffOn ℝ ∞ ψ (Ioi 0) := by
    have hlog : ContDiffOn ℝ ∞ Real.log (Ioi 0) := Real.contDiffOn_log.mono
      (fun _ hx => ne_of_gt hx)
    refine (hgC.comp_contDiffOn hlog).congr (fun x hx => ?_)
    simp [ψ, show 0 < x from hx]
  have hψS : support ψ ⊆ Icc (γ * lo) hi := by
    intro t ht
    have ht₀ : 0 < t := by by_contra h; exact ht (if_neg h)
    have hm : g (Real.log t) ≠ 0 := by simpa [ψ, ht₀] using ht
    have hh := hg hm
    have hγ₀ : 0 < γ := zero_lt_one.trans hγ
    rw [add_comm, ← Real.log_mul hγ₀.ne' hlo.ne'] at hh
    exact ⟨(Real.log_le_log_iff (mul_pos hγ₀ hlo) ht₀).mp hh.1,
      (Real.log_le_log_iff ht₀ hhi).mp hh.2⟩
  have hEq (t : ℝ) (ht : 0 < t) : ψ t - ψ (γ * t) = f t := by
    have hγ₀ : 0 < γ := zero_lt_one.trans hγ
    simpa [ψ, ht, mul_pos hγ₀ ht, Real.log_mul hγ₀.ne' ht.ne',
      add_comm (Real.log γ), Function.comp_apply, Real.exp_log ht] using he (Real.log t)
  refine ⟨ψ, hψC, hψS, hEq, ?_⟩
  intro t ht
  by_contra hn
  have ht₀ := hlo.trans_le (hf ht).1
  have h₁ : ψ t = 0 := notMem_support.mp (fun h => hn (Or.inl (hψS h)))
  have h₂ : ψ (γ * t) = 0 := notMem_support.mp (fun h => hn (Or.inr (hψS h)))
  exact ht (by simpa [h₁, h₂] using (hEq t ht₀).symm)

/-- The symmetric collar in Proposition 4.5.2.1(3) fails for a shifted
window. The example uses logarithmic endpoints 12 and 14 and period 1. -/
theorem printed_compact_multiplicative_collar_fails :
    let a := Real.exp 1
    let b := Real.exp 13
    let γ := Real.exp 1
    let A := |(-Real.log γ + Real.log (max (a * b) (a / b)))|
    1 < a ∧ 0 < b ∧ 1 < γ ∧ Real.log γ < 2 * Real.log a ∧
    ∃ f : ℝ → ℂ, ContDiffOn ℝ ∞ f (Ioi 0) ∧ support f ⊆ Icc (b / a) (b * a) ∧
      (∀ x, integerPeriodization (Real.log γ) (f ∘ Real.exp) x = 0) ∧
      ¬ ∃ ψ : ℝ → ℂ, support ψ ⊆ Icc (Real.exp (-A)) (Real.exp A) ∧
        ∀ t > 0, ψ t - ψ (γ * t) = f t := by
  dsimp only
  refine ⟨Real.one_lt_exp_iff.mpr zero_lt_one, Real.exp_pos _, Real.one_lt_exp_iff.mpr zero_lt_one,
    by simp, ?_⟩
  obtain ⟨g, hgC, hgS, hg0, hg1, _⟩ := printed_periodic_difference_support_fails
  let f (t : ℝ) := if 0 < t then g (Real.log t - 13) else 0
  have hA : |(-Real.log (Real.exp 1) +
      Real.log (max (Real.exp 1 * Real.exp 13) (Real.exp 1 / Real.exp 13)))| = 13 := by
    rw [← Real.exp_add, ← Real.exp_sub, max_eq_left (Real.exp_le_exp.mpr (by norm_num)),
      Real.log_exp, Real.log_exp]
    norm_num
  refine ⟨f, ?_, ?_, ?_, ?_⟩
  · have hl : ContDiffOn ℝ ∞ Real.log (Ioi (0 : ℝ)) :=
      Real.contDiffOn_log.mono (fun _ ht ↦ ne_of_gt ht)
    have ht : ContDiffOn ℝ ∞ (fun t ↦ g (Real.log t - 13)) (Ioi (0 : ℝ)) :=
      hgC.comp_contDiffOn (hl.sub contDiffOn_const)
    refine ht.congr (fun t ht ↦ ?_)
    simp [f, show 0 < t from ht]
  · intro t ht
    have ht₀ : 0 < t := by
      by_contra hn
      exact ht (by simp [f, hn])
    have hg' : g (Real.log t - 13) ≠ 0 := by simpa [f, ht₀] using ht
    have hh := hgS hg'
    rw [← Real.exp_sub, ← Real.exp_add]
    exact ⟨(Real.le_log_iff_exp_le ht₀).mp (by linarith [hh.1]),
      (Real.log_le_iff_le_exp ht₀).mp (by linarith [hh.2])⟩
  · intro x
    rw [Real.log_exp, ← hg0 (x - 13)]
    unfold integerPeriodization
    congr 1
    funext n
    simp only [Function.comp_apply, f, Real.exp_pos, ite_true, Real.log_exp]
    congr 1
    ring
  · rintro ⟨ψ, hψS, he⟩
    rw [hA] at hψS
    let t := Real.exp (13 + 1 / 2)
    have ht : 0 < t := Real.exp_pos _
    have h₁ : ψ t = 0 := notMem_support.mp fun h ↦
      (not_le_of_gt (Real.exp_lt_exp.mpr (by norm_num : (13 : ℝ) < 13 + 1 / 2))) (hψS h).2
    have h₂ : ψ (Real.exp 1 * t) = 0 := notMem_support.mp fun h ↦ by
      have hu := (hψS h).2
      rw [show t = _ from rfl, ← Real.exp_add, Real.exp_le_exp] at hu
      norm_num at hu
    have hf : f t = 1 := by
      rw [show f t = g (Real.log t - 13) by simp [f, ht]]
      change g (Real.log (Real.exp (13 + 1 / 2)) - 13) = 1
      rw [Real.log_exp, show (13 + 1 / 2 : ℝ) - 13 = 1 / 2 by norm_num, hg1]
    have h := he t ht
    rw [h₁, h₂, hf, sub_zero] at h
    exact zero_ne_one h

end
end Masullo
