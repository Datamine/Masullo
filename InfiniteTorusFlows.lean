import FourierSymbols
import Mathlib.Topology.Compactness.LocallyCompact

open Filter Function Set Topology

namespace Masullo

noncomputable section

/-- A countable product of real lines has no compact neighborhood of zero. -/
theorem realSequence_not_locallyCompact : ¬ LocallyCompactSpace (ℕ → ℝ) := by
  intro h
  letI : LocallyCompactSpace (ℕ → ℝ) := h
  obtain ⟨K, hK, hKn⟩ := exists_compact_mem_nhds (0 : ℕ → ℝ)
  rw [nhds_pi, Filter.mem_pi'] at hKn
  obtain ⟨s, V, hV, hsub⟩ := hKn
  obtain ⟨i, hi⟩ := Infinite.exists_notMem_finset s
  have hproj : (fun a : ℕ → ℝ => a i) '' K = univ := by
    apply eq_univ_of_forall
    intro t
    let x := Function.update (0 : ℕ → ℝ) i t
    refine ⟨x, hsub ?_, Function.update_self _ _ _⟩
    intro j hj
    have hj' : j ≠ i := fun hji => hi (hji ▸ hj)
    change x j ∈ V j
    rw [show x j = (0 : ℕ → ℝ) j from Function.update_of_ne hj' _ _]
    exact mem_of_mem_nhds (hV j)
  have hc : IsCompact (univ : Set ℝ) := hproj ▸ hK.image (continuous_apply i)
  exact (not_compactSpace_iff.mpr (inferInstance : NoncompactSpace ℝ)) (isCompact_univ_iff.mp hc)

private def torusCoord (n : ℕ) : (ℕ → Circle) →ₜ* Circle where
  toFun x := x n
  continuous_toFun := continuous_apply n
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The real slopes define the componentwise exponentials into a torus. -/
private def torusFlow (r : ℕ → ℝ) : Multiplicative ℝ →ₜ* (ℕ → Circle) where
  toFun t n := Circle.exp (r n * Multiplicative.toAdd t)
  continuous_toFun :=
    continuous_pi fun n => Circle.exp.continuous.comp (continuous_toAdd.const_mul _)
  map_one' := by funext n; simp
  map_mul' t u := by
    funext n
    change Circle.exp (r n * (Multiplicative.toAdd t + Multiplicative.toAdd u)) =
      Circle.exp (r n * Multiplicative.toAdd t) * Circle.exp (r n * Multiplicative.toAdd u)
    rw [mul_add, Circle.exp_add]

/-- The compact-open space of continuous one-parameter groups of the
countable compact torus is the countable product of real lines. -/
def infiniteTorusFlowsHomeomorph : (ℕ → ℝ) ≃ₜ (Multiplicative ℝ →ₜ* (ℕ → Circle)) where
  toFun := torusFlow
  invFun f n := Multiplicative.toAdd (characterSlope (ContinuousMonoidHom.id (Multiplicative ℝ))
    ((torusCoord n).comp f))
  left_inv r := by
    funext n
    exact characterSlope_unique (ContinuousMonoidHom.id (Multiplicative ℝ))
      ((torusCoord n).comp (torusFlow r)) (r n) (fun _ => rfl)
  right_inv f := by
    apply DFunLike.ext
    intro t
    funext n
    have h := characterSlope_eq_exp (ContinuousMonoidHom.id (Multiplicative ℝ))
      ((torusCoord n).comp f) (Multiplicative.toAdd t)
    exact h.symm
  continuous_toFun := by
    apply ContinuousMonoidHom.continuous_of_continuous_uncurry
    apply continuous_pi
    intro n
    exact Circle.exp.continuous.comp
      (((continuous_apply n).comp continuous_fst).mul (continuous_toAdd.comp continuous_snd))
  continuous_invFun := by
    apply continuous_pi
    intro n
    exact continuous_toAdd.comp
      ((characterSlope_continuous (ContinuousMonoidHom.id (Multiplicative ℝ))).comp
        (ContinuousMonoidHom.continuous_comp_right (torusCoord n)))

/-- This compact Hausdorff abelian group contradicts the local
compactness claim for the one-parameter group space in D.1.6.4. -/
theorem infiniteTorusFlows_not_locallyCompact :
    ¬ LocallyCompactSpace (Multiplicative ℝ →ₜ* (ℕ → Circle)) := by
  intro h
  letI : LocallyCompactSpace (Multiplicative ℝ →ₜ* (ℕ → Circle)) := h
  exact realSequence_not_locallyCompact infiniteTorusFlowsHomeomorph.isClosedEmbedding.locallyCompactSpace

end

end Masullo
