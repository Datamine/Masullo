/-
The jet-kernel proof is adapted from the Apache-2.0 RiemannMasullo project,
commit 9202f25. See External/PROVENANCE.md and External/RiemannMasullo.LICENSE.
-/
import SchwartzBergman
import Mathlib.Analysis.Meromorphic.NormalForm

open Set
open scoped ENat

namespace Masullo

/-- Entire divisibility is determined by analytic orders, including for the zero divisor. -/
theorem entire_divisibility_iff_orders {g f : ℂ → ℂ}
    (hg : Differentiable ℂ g) (hf : Differentiable ℂ f) :
    (∃ k : ℂ → ℂ, Differentiable ℂ k ∧ ∀ z, f z = g z * k z) ↔
      ∀ z, analyticOrderAt g z ≤ analyticOrderAt f z := by
  constructor
  · rintro ⟨k, hk, he⟩ z
    rw [show f = g * k from funext he, analyticOrderAt_mul (hg.analyticAt z) (hk.analyticAt z)]
    exact self_le_add_right _ _
  · intro hord
    let q := f / g
    have hq : MeromorphicOn q univ := fun z _ ↦
      (hf.analyticAt z).meromorphicAt.div (hg.analyticAt z).meromorphicAt
    refine ⟨toMeromorphicNFOn q univ, ?_, ?_⟩
    · intro z
      apply AnalyticAt.differentiableAt
      have hnf := meromorphicNFOn_toMeromorphicNFOn q univ (mem_univ z)
      apply hnf.meromorphicOrderAt_nonneg_iff_analyticAt.mp
      rw [meromorphicOrderAt_toMeromorphicNFOn hq (mem_univ z),
        meromorphicOrderAt_div (hf.analyticAt z).meromorphicAt (hg.analyticAt z).meromorphicAt,
        (hf.analyticAt z).meromorphicOrderAt_eq, (hg.analyticAt z).meromorphicOrderAt_eq]
      have hle := hord z
      generalize analyticOrderAt f z = m at hle ⊢
      generalize analyticOrderAt g z = n at hle ⊢
      cases m using ENat.recTopCoe with
      | top => simp
      | coe m =>
        cases n using ENat.recTopCoe with
        | top => simp at hle
        | coe n =>
          exact WithTop.coe_le_coe.mpr (sub_nonneg.mpr (by exact_mod_cast hle : (n : ℤ) ≤ m))
    · intro z
      by_cases hz : g z = 0
      · have hpos := lt_of_lt_of_le
          (pos_iff_ne_zero.mpr ((hg.analyticAt z).analyticOrderAt_ne_zero.mpr hz)) (hord z)
        rw [hz, zero_mul]
        exact (hf.analyticAt z).analyticOrderAt_ne_zero.mp hpos.ne'
      · rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hq (mem_univ z),
          toMeromorphicNFAt_eq_self.mpr ((hf.analyticAt z).div (hg.analyticAt z) hz).meromorphicNFAt]
        exact (mul_div_cancel₀ _ hz).symm

/-- The entire divisibility subspace is closed in the actual Schwartz–Bergman topology. -/
theorem schwartzBergman_entireDivisibility_isClosed {g : ℂ → ℂ} (hg : Differentiable ℂ g) :
    IsClosed {f : SchwartzBergman univ |
      ∃ k : ℂ → ℂ, Differentiable ℂ k ∧ ∀ z, f.val z = g z * k z} := by
  have hf (f : SchwartzBergman (univ : Set ℝ)) : Differentiable ℂ f.val := by
    have hd := f.property.2.1
    simpa only [preimage_univ, differentiableOn_univ] using hd
  choose jet hjet using fun (z : ℂ) (i : ℕ) ↦
    exists_schwartzBergman_jetEvaluation (I := univ) isOpen_univ Set.ordConnected_univ z
      (mem_univ z.re) i
  have heq : {f : SchwartzBergman univ |
      ∃ k : ℂ → ℂ, Differentiable ℂ k ∧ ∀ z, f.val z = g z * k z} =
      ⋂ (z : ℂ) (n : ℕ) (_ : (n : ℕ∞) ≤ analyticOrderAt g z)
        (i : ℕ) (_ : i < n), ((jet z i).ker : Set (SchwartzBergman univ)) := by
    ext f
    simp only [mem_ofPred_eq, entire_divisibility_iff_orders hg (hf f), mem_iInter,
      SetLike.mem_coe, LinearMap.mem_ker, ContinuousLinearMap.coe_coe, hjet]
    apply forall_congr'
    intro z
    rw [← ENat.forall_natCast_le_iff_le]
    simp_rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero ((hf f).analyticAt z)]
  rw [heq]
  exact isClosed_iInter fun z ↦ isClosed_iInter fun n ↦ isClosed_iInter fun _ ↦
    isClosed_iInter fun i ↦ isClosed_iInter fun _ ↦ (jet z i).isClosed_ker

end Masullo
