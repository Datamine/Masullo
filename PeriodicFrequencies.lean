import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Nat.Prime.Basic

open Function Set

namespace Masullo

noncomputable section

private def periodicPhase (c : ℝ) : Circle :=
  Circle.exp ((2 * Real.pi) * c)

private theorem periodicPhase_pow_isOne_iff_rat (c : ℝ) :
    IsOfFinOrder (periodicPhase c) ↔ ∃ q : ℚ, c = q := by
  rw [isOfFinOrder_iff_pow_eq_one]
  constructor
  · rintro ⟨n, hn, hp⟩
    rw [periodicPhase, ← Circle.exp_natCast_mul] at hp
    obtain ⟨m, hm⟩ := Circle.exp_eq_one.mp hp
    refine ⟨(m : ℚ) / (n : ℚ), ?_⟩
    push_cast
    have hπ : (2 * Real.pi) ≠ 0 := by positivity
    apply (eq_div_iff (Nat.cast_ne_zero.mpr hn.ne')).mpr
    apply mul_right_cancel₀ hπ
    convert hm using 1
    ring
  · rintro ⟨q, rfl⟩
    refine ⟨q.den, q.den_pos, ?_⟩
    rw [periodicPhase, ← Circle.exp_natCast_mul]
    apply Circle.exp_eq_one.mpr
    refine ⟨q.num, ?_⟩
    rw [Rat.cast_def]
    field_simp [Nat.cast_ne_zero.mpr q.den_ne_zero]

private theorem periodicPhase_finite_iff_rat (c : ℝ) :
    (range fun m : ℤ => periodicPhase ((m : ℝ) * c)).Finite ↔ ∃ q : ℚ, c = q := by
  have he (m : ℤ) : periodicPhase ((m : ℝ) * c) = (periodicPhase c) ^ m := by
    unfold periodicPhase
    rw [show 2 * Real.pi * ((m : ℝ) * c) = (m : ℝ) * (2 * Real.pi * c) by ring,
      Circle.exp_intCast_mul]
  simp only [he]
  constructor
  · intro h
    apply (periodicPhase_pow_isOne_iff_rat c).mp
    apply (finite_powers).mp
    apply h.subset
    rintro a ⟨n, rfl⟩
    exact ⟨n, zpow_natCast _ n⟩
  · intro h
    have hf := (periodicPhase_pow_isOne_iff_rat c).mpr h
    have he' : range (fun m : ℤ => periodicPhase c ^ m) =
        (Subgroup.zpowers (periodicPhase c) : Set Circle) := rfl
    rw [he', ← hf.powers_eq_zpowers]
    exact hf.finite_powers

/-- The set of complex powers in (4.6.1.11). The bases are positive, so
their complex powers use the real logarithm. -/
def periodicFrequencyValues {ι : Type*} (b : ι → ℝ) : Set ℂ :=
  ⋃ k : ι, ⋃ h : ι, range fun m : ℤ =>
    (b k : ℂ) ^ ((2 * (Real.pi : ℂ) * Complex.I * (m : ℂ)) / (Real.log (b h) : ℂ))

private theorem periodicFrequency_component {ι : Type*} (b : ι → ℝ) (hb : ∀ k, 1 < b k)
    (k h : ι) (m : ℤ) :
    (b k : ℂ) ^ ((2 * (Real.pi : ℂ) * Complex.I * (m : ℂ)) / (Real.log (b h) : ℂ)) =
      (periodicPhase ((m : ℝ) * (Real.log (b k) / Real.log (b h))) : ℂ) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (zero_lt_one.trans (hb k)).ne'),
    ← Complex.ofReal_log (zero_lt_one.trans (hb k)).le, periodicPhase, Circle.coe_exp]
  congr 1
  push_cast
  ring

/-- Corrected Lemma 4.6.1.4. It is the logarithms of the positive bases
that must have a common rational span. -/
theorem periodic_frequencies_finite_iff_commensurable {ι : Type*} [Finite ι] [Nonempty ι]
    (b : ι → ℝ) (hb : ∀ k, 1 < b k) :
    (periodicFrequencyValues b).Finite ↔
      ∃ B : ℝ, 1 < B ∧ ∀ k, ∃ q : ℚ, Real.log (b k) = (q : ℝ) * Real.log B := by
  have hcomp (k h : ι) : (range fun m : ℤ =>
      (b k : ℂ) ^ ((2 * (Real.pi : ℂ) * Complex.I * (m : ℂ)) / (Real.log (b h) : ℂ))).Finite ↔
        ∃ q : ℚ, Real.log (b k) / Real.log (b h) = q := by
    simp only [periodicFrequency_component b hb]
    change (range (((↑) : Circle → ℂ) ∘
      (fun m : ℤ => periodicPhase ((m : ℝ) * (Real.log (b k) / Real.log (b h)))))).Finite ↔ _
    let g : Circle → ℂ := Circle.coeHom
    let q (m : ℤ) := periodicPhase ((m : ℝ) * (Real.log (b k) / Real.log (b h)))
    change (range (g ∘ q)).Finite ↔ _
    rw [range_comp, finite_image_iff (show InjOn g (range q) from Circle.coe_injective.injOn)]
    exact periodicPhase_finite_iff_rat _
  have hall : (periodicFrequencyValues b).Finite ↔
      ∀ k h, ∃ q : ℚ, Real.log (b k) / Real.log (b h) = q := by
    constructor
    · intro h k j
      apply (hcomp k j).mp
      apply h.subset
      intro x hx
      exact mem_iUnion.mpr ⟨k, mem_iUnion.mpr ⟨j, hx⟩⟩
    · intro h
      exact finite_iUnion fun k => finite_iUnion fun j => (hcomp k j).mpr (h k j)
  rw [hall]
  constructor
  · intro h
    let i : ι := Classical.choice inferInstance
    refine ⟨b i, hb i, fun k => ?_⟩
    obtain ⟨q, hq⟩ := h k i
    exact ⟨q, (div_eq_iff (Real.log_pos (hb i)).ne').mp hq⟩
  · rintro ⟨B, hB, h⟩ k j
    obtain ⟨q, hq⟩ := h k
    obtain ⟨r, hr⟩ := h j
    have hne : (r : ℝ) ≠ 0 := by
      intro hzero
      rw [hzero, zero_mul] at hr
      exact (Real.log_pos (hb j)).ne' hr
    refine ⟨q / r, ?_⟩
    rw [hq, hr, Rat.cast_div, mul_div_mul_right _ _ (Real.log_pos hB).ne']

private theorem log_two_div_log_three_not_rat :
    ¬ ∃ q : ℚ, Real.log 2 / Real.log 3 = (q : ℝ) := by
  rintro ⟨q, hq⟩
  have h₂ : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h₃ : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hq₀ : 0 < q := by
    exact_mod_cast (hq ▸ div_pos h₂ h₃ : (0 : ℝ) < (q : ℝ))
  have hnum : 0 < q.num := Rat.num_pos.mpr hq₀
  have hd : (q.den : ℝ) ≠ 0 := by exact_mod_cast q.den_ne_zero
  have he : (q.den : ℝ) * Real.log 2 = (q.num : ℝ) * Real.log 3 := by
    have hc := (div_eq_iff h₃.ne').mp hq
    rw [Rat.cast_def, div_mul_eq_mul_div] at hc
    have h := (eq_div_iff hd).mp hc
    simpa only [mul_comm (Real.log 2)] using h
  have hnat : (q.num.toNat : ℝ) = (q.num : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hnum.le
  rw [← hnat] at he
  have hp := congrArg Real.exp he
  rw [Real.exp_nat_mul, Real.exp_nat_mul, Real.exp_log (by norm_num : 0 < (2 : ℝ)),
    Real.exp_log (by norm_num : 0 < (3 : ℝ))] at hp
  have hpow : (2 : ℕ) ^ q.den = 3 ^ q.num.toNat := by exact_mod_cast hp
  have hdiv : 2 ∣ (3 : ℕ) := Nat.prime_two.dvd_of_dvd_pow (hpow ▸ dvd_pow_self 2 q.den_ne_zero)
  norm_num at hdiv

/-- The raw bases 2 and 3 span a single rational line, but their complex
frequency values form an infinite set. -/
theorem printed_periodic_frequencies_condition_fails :
    let b : Bool → ℝ := fun k => if k then 3 else 2
    (∃ B : ℝ, 1 < B ∧ ∀ k, ∃ q : ℚ, b k = (q : ℝ) * Real.log B) ∧
      ¬ (periodicFrequencyValues b).Finite := by
  dsimp only
  let b : Bool → ℝ := fun k => if k then 3 else 2
  refine ⟨⟨Real.exp 1, Real.one_lt_exp_iff.mpr zero_lt_one, fun k => ?_⟩, ?_⟩
  · cases k
    · exact ⟨2, by simp [Real.log_exp]⟩
    · exact ⟨3, by simp [Real.log_exp]⟩
  · intro h
    have hB : ∀ k, 1 < b k := by intro k; cases k <;> norm_num [b]
    obtain ⟨B, hB', h⟩ := (periodic_frequencies_finite_iff_commensurable b hB).mp h
    obtain ⟨q, hq⟩ := h false
    obtain ⟨r, hr⟩ := h true
    apply log_two_div_log_three_not_rat
    refine ⟨q / r, ?_⟩
    change Real.log (b false) / Real.log (b true) = _
    rw [hq, hr, Rat.cast_div, mul_div_mul_right _ _ (Real.log_pos hB').ne']


end

end Masullo
