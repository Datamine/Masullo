import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus

open Bornology Set

namespace Masullo

private def SeminormedCopy {E : Type*} [AddCommGroup E] [Module ℂ E] (_ : Seminorm ℂ E) := E

private instance {E : Type*} [AddCommGroup E] [Module ℂ E] (p : Seminorm ℂ E) :
    SeminormedAddCommGroup (SeminormedCopy p) := p.toSeminormedAddCommGroup

private instance {E : Type*} [AddCommGroup E] [Module ℂ E] (p : Seminorm ℂ E) :
    NormedSpace ℂ (SeminormedCopy p) where
  toModule := inferInstanceAs (Module ℂ E)
  norm_smul_le c x := (map_smul_eq_mul p c x).le

/-- To bound a continuous seminorm at a vector, it suffices to bound all
continuous functionals dominated by that seminorm. -/
theorem seminorm_le_of_dual_unit_bounds {E : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [PolynormableSpace ℂ E]
    (p : {p : Seminorm ℂ E // Continuous p}) (x : E) {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ ℓ : StrongDual ℂ E, (∀ y, ‖ℓ y‖ ≤ p.1 y) → ‖ℓ x‖ ≤ M) : p.1 x ≤ M := by
  let P := SeminormedCopy p.1
  let j : E →ₗ[ℂ] P := LinearMap.id
  have hj : Continuous j := by
    apply (PolynormableSpace.withSeminorms ℂ E).continuous_normedSpace_rng P j
    refine ⟨{p}, 1, ?_⟩
    rw [Finset.sup_singleton, one_smul]
    intro y
    exact le_rfl
  let J : E →L[ℂ] P := ⟨j, hj⟩
  change ‖J x‖ ≤ M
  apply NormedSpace.norm_le_dual_bound ℂ (J x) hM
  intro ℓ
  by_cases hℓ : ‖ℓ‖ = 0
  · have hzero := (ℓ.le_opNorm (J x)).trans_eq (by rw [hℓ, zero_mul])
    simpa [hℓ] using hzero
  have hℓpos : 0 < ‖ℓ‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hℓ)
  let L : StrongDual ℂ E := ((‖ℓ‖⁻¹ : ℝ) : ℂ) • (ℓ.comp J)
  have hL (y : E) : ‖L y‖ = ‖ℓ‖⁻¹ * ‖ℓ (J y)‖ := by
    simp [L, Complex.norm_real]
  have hb := h L (fun y => by
    rw [hL]
    exact (mul_le_mul_of_nonneg_left (ℓ.le_opNorm (J y)) (by positivity)).trans_eq (by
      rw [← mul_assoc, inv_mul_cancel₀ hℓ, one_mul]
      rfl))
  rw [hL] at hb
  rwa [← div_eq_inv_mul, div_le_iff₀ hℓpos] at hb

/-- Proposition C.1.4.1. For each continuous seminorm, apply uniform
boundedness to the evaluations on the Banach dual of the seminormed space. -/
theorem isVonNBounded_iff_dual_images {E : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [PolynormableSpace ℂ E] (B : Set E) :
    IsVonNBounded ℂ B ↔ ∀ f : StrongDual ℂ E, IsBounded (f '' B) := by
  constructor
  · intro h f
    exact (NormedSpace.isVonNBounded_iff ℂ).mp (h.image f)
  · intro h
    let hp := PolynormableSpace.withSeminorms ℂ E
    apply hp.isVonNBounded_iff_seminorm_bounded.mpr
    intro i
    let p := (i : Seminorm ℂ E)
    let P := SeminormedCopy p
    let j : E →ₗ[ℂ] P := LinearMap.id
    have hj : Continuous j := by
      apply hp.continuous_normedSpace_rng P j
      refine ⟨{i}, 1, ?_⟩
      rw [Finset.sup_singleton, one_smul]
      intro x
      exact le_rfl
    let J : E →L[ℂ] P := ⟨j, hj⟩
    let ev (x : B) : StrongDual ℂ (StrongDual ℂ P) := NormedSpace.inclusionInDoubleDual ℂ P (J x)
    have hpoint (f : StrongDual ℂ P) : ∃ M, ∀ x : B, ‖ev x f‖ ≤ M := by
      obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.mp (h (f.comp J))
      exact ⟨M, fun x => hM _ (mem_image_of_mem (f.comp J) x.property)⟩
    obtain ⟨M, hM⟩ := banach_steinhaus (g := ev) hpoint
    refine ⟨max M 0 + 1, by positivity, fun x hx => ?_⟩
    have hnorm : ‖ev ⟨x, hx⟩‖ = p x := (NormedSpace.inclusionInDoubleDualLi ℂ).norm_map (J x)
    exact hnorm ▸ (hM ⟨x, hx⟩).trans_lt ((le_max_left _ _).trans_lt (lt_add_one _))

end Masullo
