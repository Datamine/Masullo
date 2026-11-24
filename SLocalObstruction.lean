import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.Tactic

namespace Masullo

/-- For `F = ℚ` and only the archimedean place, the S-local quotient is
`ℝ / ℤ`. The residue of one half has order two, so this additive group
cannot underlie a rational vector space. -/
theorem rationalArchimedeanQuotient_has_two_torsion :
    ∃ x : AddCircle (1 : ℝ), x ≠ 0 ∧ 2 • x = 0 := by
  refine ⟨((1 / 2 : ℝ) : AddCircle (1 : ℝ)), ?_, ?_⟩
  · intro h
    obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp h
    have hc : (n : ℝ) = 1 / 2 := by simpa [zsmul_eq_mul] using hn
    have hi : 2 * n = 1 := by exact_mod_cast (show 2 * (n : ℝ) = 1 by linarith)
    omega
  · rw [two_nsmul, ← AddCircle.coe_add, show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num]
    exact AddCircle.coe_period (1 : ℝ)

/-- Divisibility survives quotienting the additive group of a rational
vector space by an arbitrary additive subgroup. -/
theorem quotient_rationalVectorSpace_divisible {V : Type*} [AddCommGroup V] [Module ℚ V]
    (S : AddSubgroup V) (n : ℕ) (hn : n ≠ 0) :
    Function.Surjective (fun x : V ⧸ S => n • x) := by
  intro x
  obtain ⟨v, rfl⟩ := QuotientAddGroup.mk_surjective x
  let q := QuotientAddGroup.mk' S
  refine ⟨q ((n : ℚ)⁻¹ • v), ?_⟩
  change n • q ((n : ℚ)⁻¹ • v) = q v
  rw [← map_nsmul, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul,
    mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hn), one_smul]

end Masullo
