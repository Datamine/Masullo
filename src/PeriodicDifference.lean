import CompactPeriodization
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

open Filter Function Set Topology
open scoped ContDiff

namespace Masullo

noncomputable section

/-- The positive translation tail of a compactly supported test. -/
def positivePeriodizationTail (d : ℝ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∑' n : ℕ, f (x + d * (n : ℝ))

private theorem compact_natTranslate_summable {a b d : ℝ} {f : ℝ → ℂ}
    (hf : support f ⊆ Icc a b) (hd : 0 < d) (x : ℝ) :
    Summable (fun n : ℕ => f (x + d * (n : ℝ))) := by
  obtain ⟨N, hN⟩ := exists_nat_gt ((b - x) / d)
  refine summable_of_ne_finset_zero (s := Finset.range N) fun n hn => ?_
  have hNn : (N : ℝ) ≤ n := by exact_mod_cast (Nat.le_of_not_gt (fun h => hn (Finset.mem_range.mpr h)))
  have hlt : b < x + d * (n : ℝ) := by
    have h := (div_lt_iff₀ hd).mp (hN.trans_le hNn)
    linarith [mul_comm d (n : ℝ)]
  by_contra h
  exact hlt.not_ge (hf h).2

private theorem positivePeriodizationTail_smooth {a b d : ℝ} {f : ℝ → ℂ}
    (hf : support f ⊆ Icc a b) (hC : ContDiff ℝ ∞ f) (hd : 0 < d) :
    ContDiff ℝ ∞ (positivePeriodizationTail d f) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  obtain ⟨N, hN⟩ := exists_nat_gt ((b - (x - 1)) / d)
  let p (y : ℝ) := ∑ n ∈ Finset.range N, f (y + d * (n : ℝ))
  have hp : ContDiff ℝ ∞ p := by
    apply ContDiff.sum
    intro n _
    exact hC.comp (by fun_prop)
  apply hp.contDiffAt.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds (show x - 1 < x by linarith)] with y hy
  have hy' : x - 1 < y := hy
  unfold positivePeriodizationTail p
  apply tsum_eq_sum
  intro n hn
  have hNn : (N : ℝ) ≤ n := by exact_mod_cast (Nat.le_of_not_gt (fun h => hn (Finset.mem_range.mpr h)))
  have hlt : b < y + d * (n : ℝ) := by
    have h := (div_lt_iff₀ hd).mp (hN.trans_le hNn)
    linarith [mul_comm d (n : ℝ)]
  by_contra h
  exact hlt.not_ge (hf h).2

private theorem positivePeriodizationTail_difference {a b d : ℝ} {f : ℝ → ℂ}
    (hf : support f ⊆ Icc a b) (hd : 0 < d) (x : ℝ) :
    positivePeriodizationTail d f x - positivePeriodizationTail d f (x + d) = f x := by
  have hs := compact_natTranslate_summable hf hd x
  have he (n : ℕ) : x + d * ((n + 1 : ℕ) : ℝ) = x + d + d * (n : ℝ) := by
    push_cast
    ring
  unfold positivePeriodizationTail
  rw [hs.tsum_eq_zero_add]
  simp only [Nat.cast_zero, mul_zero, add_zero, he, add_sub_cancel_right]

/-- If the full cyclic periodization vanishes, the difference equation
has a compactly supported smooth solution. Its actual support collar is
`[a + d, b]` in the logarithmic coordinate. -/
theorem compact_periodization_difference {a b d : ℝ} {f : ℝ → ℂ}
    (hf : support f ⊆ Icc a b) (hC : ContDiff ℝ ∞ f) (hd : 0 < d)
    (hzero : ∀ x, integerPeriodization d f x = 0) :
    ∃ ψ : ℝ → ℂ, ContDiff ℝ ∞ ψ ∧ support ψ ⊆ Icc (a + d) b ∧
      ∀ x, ψ x - ψ (x + d) = f x := by
  refine ⟨positivePeriodizationTail d f, positivePeriodizationTail_smooth hf hC hd, ?_,
    positivePeriodizationTail_difference hf hd⟩
  intro x hx
  constructor
  · by_contra! hlow
    have hi := compact_integerTranslate_summable isCompact_Icc hf hd.ne' x
    have h := tsum_int_eq_zero_add_tsum_pnat hi
    have hneg (n : ℕ+) : f (x + d * (-(n : ℕ) : ℤ)) = 0 := by
      by_contra hn
      have hN : (1 : ℝ) ≤ (n : ℕ) := by exact_mod_cast n.property
      have hb := (hf hn).1
      push_cast at hb
      nlinarith [mul_le_mul_of_nonneg_left hN hd.le]
    have h₁ := hzero x
    change (∑' m : ℤ, f (x + d * (m : ℝ))) = 0 at h₁
    simp only [hneg, tsum_zero, add_zero] at h
    rw [h] at h₁
    push_cast at h₁
    rw [tsum_pnat_eq_tsum_succ (f := fun n : ℕ => f (x + d * (n : ℝ)))] at h₁
    have h₂ := (compact_natTranslate_summable hf hd x).tsum_eq_zero_add
    exact hx (h₂.trans (by simpa using h₁))
  · by_contra! hhigh
    have hn (n : ℕ) : f (x + d * (n : ℝ)) = 0 := by
      by_contra h
      have hb := (hf h).2
      exact hhigh.not_ge ((le_add_of_nonneg_right (by positivity)).trans hb)
    exact hx (by simp [positivePeriodizationTail, hn])

end
end Masullo
