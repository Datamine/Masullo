import QuotientBasisTransfer

open Bornology Filter Function Set Topology

namespace Masullo

noncomputable section

variable {X Y : Type*} [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
  [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]

/-- A split continuous linear surjection induces an equivalence on its
kernel quotient with any prescribed nonzero scalar normalization. -/
theorem splitQuotientEquiv_scaled (T : X →L[ℂ] Y) (S : Y →L[ℂ] X)
    [ContinuousConstSMul ℂ X] [ContinuousConstSMul ℂ Y]
    (hS : RightInverse S T) (c : ℂ) (hc : c ≠ 0) :
    ∃ e : (X ⧸ T.ker) ≃L[ℂ] Y, ∀ x, e (T.ker.mkQ x) = c • T x := by
  let F := c • T
  have hk : T.ker ≤ F.ker := by
    intro x hx
    change c • T x = 0
    rw [show T x = 0 from hx, smul_zero]
  let A := T.ker.liftQL F hk
  let B := T.ker.mkQL.comp (c⁻¹ • S)
  have hA (x : X) : A (T.ker.mkQ x) = c • T x := rfl
  have hB (y : Y) : B y = T.ker.mkQ (c⁻¹ • S y) := rfl
  have hab (y : Y) : A (B y) = y := by
    rw [hB, hA, map_smul, hS y, smul_smul, mul_inv_cancel₀ hc, one_smul]
  have hba (z : X ⧸ T.ker) : B (A z) = z := by
    obtain ⟨x, rfl⟩ := T.ker.mkQ_surjective z
    rw [hA, hB, S.map_smul, smul_smul, inv_mul_cancel₀ hc, one_smul]
    exact (Submodule.Quotient.eq T.ker).mpr
      (show T (S (T x) - x) = 0 by rw [map_sub, hS (T x), sub_self])
  let L : (X ⧸ T.ker) ≃ₗ[ℂ] Y :=
    { A.toLinearMap with
      invFun := B
      left_inv := hba
      right_inv := hab }
  exact ⟨⟨L, A.continuous, B.continuous⟩, hA⟩

/-- If a supported subspace contains the image of a section, its kernel
quotient identifies with the full kernel quotient by the inclusion. -/
theorem splitQuotientEquiv_restrict (T : X →L[ℂ] Y) (U : Submodule ℂ X)
    [ContinuousConstSMul ℂ X] [ContinuousConstSMul ℂ Y]
    (S : Y →L[ℂ] U) (hS : RightInverse S (T.comp U.subtypeL))
    (e : (X ⧸ T.ker) ≃L[ℂ] Y) (c : ℂ) (hc : c ≠ 0)
    (he : ∀ x, e (T.ker.mkQ x) = c • T x) :
    let T₀ := T.comp U.subtypeL
    ∃ j : (U ⧸ T₀.ker) ≃L[ℂ] (X ⧸ T.ker),
      ∀ u : U, j (T₀.ker.mkQ u) = T.ker.mkQ u.val := by
  dsimp only
  let T₀ := T.comp U.subtypeL
  letI : ContinuousConstSMul ℂ U :=
    ⟨fun c ↦ ((continuous_const_smul c : Continuous fun x : X ↦ c • x).comp
      continuous_subtype_val).subtype_mk _⟩
  obtain ⟨e₀, he₀⟩ := splitQuotientEquiv_scaled T₀ S hS c hc
  refine ⟨e₀.trans e.symm, fun u ↦ e.injective ?_⟩
  change e (e.symm (e₀ (T₀.ker.mkQ u))) = e (T.ker.mkQ u.val)
  exact (e.apply_symm_apply _).trans ((he₀ u).trans (he u.val).symm)

variable [IsTopologicalAddGroup X] [ContinuousSMul ℂ X]
  [IsTopologicalAddGroup Y] [ContinuousSMul ℂ Y]

omit [IsTopologicalAddGroup X] [IsTopologicalAddGroup Y] in
/-- For a split surjection the quotient strong dual has the topology
induced from the source strong dual on the kernel annihilator. -/
theorem splitQuotientStrongDual_isEmbedding (T : X →L[ℂ] Y) (S : Y →L[ℂ] X)
    (hS : RightInverse S T) :
    IsEmbedding (T.ker.mkQL.precomp (τ := RingHom.id ℂ) ℂ :
      StrongDual ℂ (X ⧸ T.ker) →L[ℂ] StrongDual ℂ X) := by
  obtain ⟨e, he⟩ := splitQuotientEquiv_scaled T S hS 1 one_ne_zero
  let R := S.comp e.toContinuousLinearMap
  have hR (y : X ⧸ T.ker) : T.ker.mkQ (R y) = y := by
    apply e.injective
    rw [he, one_smul]
    exact hS (e y)
  refine quotientDual_strongEmbedding_of_bounded_lifts T.ker fun B hB ↦ ?_
  refine ⟨R '' B, hB.image R, fun y hy ↦ ?_⟩
  exact ⟨R y, ⟨y, hy, rfl⟩, hR y⟩

omit [IsTopologicalAddGroup X] [IsTopologicalAddGroup Y] in
/-- A continuous linear equivalence transports both strong-dual and
ordinary absolute Schauder expansions. -/
theorem absoluteBasis_pullback_withStrongDual (e : X ≃L[ℂ] Y)
    (y : ℕ → Y) (b : ℕ → StrongDual ℂ Y)
    (hb : IsSchauderBasis y b) (ha : IsAbsolute y b)
    (hu : IsUnconditional b (fun n ↦ strongBidualEvaluation (y n))) :
    let x := fun n ↦ e.symm (y n)
    let a := fun n ↦ (b n).comp e.toContinuousLinearMap
    IsSchauderBasis x a ∧ IsAbsolute x a ∧ IsShrinking x a ∧
      IsUnconditional a (fun n ↦ strongBidualEvaluation (x n)) := by
  classical
  dsimp only
  let x := fun n ↦ e.symm (y n)
  let a := fun n ↦ (b n).comp e.toContinuousLinearMap
  obtain ⟨hbx, hax⟩ := absoluteBasis_pullback e (fun n ↦ e.apply_symm_apply (y n)) hb ha
  have hux : IsUnconditional a (fun n ↦ strongBidualEvaluation (x n)) := by
    intro g
    let R : StrongDual ℂ Y →L[ℂ] StrongDual ℂ X := e.toContinuousLinearMap.precomp ℂ
    let u : StrongDual ℂ Y := g.comp e.symm.toContinuousLinearMap
    have he : R u = g := ContinuousLinearMap.ext fun z ↦ congrArg g (e.symm_apply_apply z)
    have h := R.hasSum (hu u)
    rw [he] at h
    exact h.congr_fun fun n ↦ (R.map_smul (g (x n)) (b n)).symm
  refine ⟨hbx, hax, ⟨fun m n ↦ ?_, fun g ↦ ?_⟩, hux⟩
  · change a n (x m) = _
    rw [hbx.1]
    simp [eq_comm]
  · exact Tendsto.mono_left (hux g) (SummationFilter.conditional ℕ).le_atTop

end

end Masullo
