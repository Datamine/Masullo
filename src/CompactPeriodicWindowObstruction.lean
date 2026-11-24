import CompactPeriodizationSection

open Function Set
open scoped ContDiff

namespace Masullo

noncomputable section

/-- The opening assertion of Theorem 4.5.2.3 fails for a short window.
For the trivial character on the positive real group in logarithmic
coordinates, tests supported in this window miss the zero phase. The full
smooth compact test space reaches it. -/
theorem shortWindow_periodization_misses_zeroPhase :
    (interior (Icc (1 / 4 : ℝ) (1 / 2))).Nonempty ∧
      (∀ f : ℝ → ℂ, support f ⊆ Icc (1 / 4 : ℝ) (1 / 2) →
        integerPeriodization 1 f 0 = 0) ∧
      ∃ g : ℝ → ℂ, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧ integerPeriodization 1 g = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [interior_Icc]
    exact ⟨3 / 8, by norm_num⟩
  · intro f hf
    have hn (j : ℤ) : f (0 + 1 * (j : ℝ)) = 0 := by
      apply notMem_support.mp
      intro h
      have hl := (hf h).1
      have hu := (hf h).2
      simp only [one_mul, zero_add] at hl hu
      have hj : 0 < j := by exact_mod_cast ((by norm_num : (0 : ℝ) < 1 / 4).trans_le hl)
      have hj' : (1 : ℤ) ≤ j := hj
      have hj'' : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj'
      linarith
    simp only [integerPeriodization, hn, tsum_zero]
  · have hcov (x : ℝ) : ∃ j : ℤ, x + 1 * (j : ℝ) ∈ interior (Icc (0 : ℝ) 2) := by
      rw [interior_Icc]
      exact openInterval_covers_integerTranslations (by norm_num) (by norm_num) x
    obtain ⟨g, hg, hgs, hp⟩ := integerPeriodization_extends_periodic isCompact_Icc
      (by norm_num : (0 : ℝ) < 1) hcov
    refine ⟨g, hg, HasCompactSupport.intro isCompact_Icc fun x hx ↦
      notMem_support.mp (fun hx' ↦ hx (hgs hx')), ?_⟩
    change integerPeriodization 1 g = fun _ ↦ 1
    simpa only [mul_one] using hp (fun _ ↦ 1) (fun _ ↦ rfl)

end

end Masullo
