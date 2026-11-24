import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Complex.Basic

open Filter Function Set Topology

namespace Masullo

noncomputable section

variable {E Y : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup Y] [NormedSpace ℂ Y] [FiniteDimensional ℂ Y]

/-- A dense linear test space remains dense in the common kernel of
finitely many continuous linear constraints after imposing those
constraints exactly on the tests. -/
theorem closure_inf_ker_eq_of_finiteDimensional
    (A : Submodule ℂ E) (hA : Dense (A : Set E)) (J : E →L[ℂ] Y) :
    (A ⊓ J.ker).topologicalClosure = J.ker := by
  let B := A.map J.toLinearMap
  have hB : IsClosed (B : Set Y) := B.closed_of_finiteDimensional
  have hJB (x : E) : J x ∈ B := by
    exact (closure_minimal (fun a ha ↦ show J a ∈ B from ⟨a, ha, rfl⟩)
      (hB.preimage J.continuous)) (hA x)
  let J₀ := J.codRestrict B hJB
  let J₁ := J₀.comp A.subtypeL
  have hJ₁ : J₁.range = ⊤ := by
    apply LinearMap.range_eq_top.mpr
    intro y
    obtain ⟨a, ha, hay⟩ := y.property
    exact ⟨⟨a, ha⟩, Subtype.ext hay⟩
  obtain ⟨R, hR⟩ := J₁.exists_rightInverse_of_surjective hJ₁
  let P := ContinuousLinearMap.id ℂ E - A.subtypeL.comp (R.comp J₀)
  have hPJ (x : E) : J (P x) = 0 := by
    have he : J ((R (J₀ x)).val) = J x :=
      congrArg Subtype.val (DFunLike.congr_fun hR (J₀ x))
    change J (x - (R (J₀ x)).val) = 0
    rw [map_sub, he, sub_self]
  have hPfix (x : E) (hx : x ∈ J.ker) : P x = x := by
    have he : J₀ x = 0 := Subtype.ext hx
    change x - (R (J₀ x)).val = x
    rw [he, map_zero]
    exact sub_zero x
  apply le_antisymm
  · exact Submodule.topologicalClosure_minimal _ inf_le_right J.isClosed_ker
  · intro x hx
    have hx' : P x ∈ (A ⊓ J.ker).topologicalClosure := by
      apply (closure_minimal _ ((Submodule.isClosed_topologicalClosure (A ⊓ J.ker)).preimage P.continuous)) (hA x)
      intro a ha
      apply Submodule.le_topologicalClosure
      exact ⟨A.sub_mem ha (R (J₀ a)).property, hPJ a⟩
    exact hPfix x hx ▸ hx'

/-- Finite continuous moment constraints can be imposed exactly while
approximating in the closure of a fixed linear test subspace. -/
theorem mem_closure_tests_with_finite_moments
    {ι : Type*} [Finite ι] (A : Submodule ℂ E) (M : ι → E →L[ℂ] ℂ) (x : E)
    (hx : x ∈ A.topologicalClosure) (hM : ∀ i, M i x = 0) :
    x ∈ closure ((A : Set E) ∩ {y | ∀ i, M i y = 0}) := by
  classical
  let V := A.topologicalClosure
  let U := A.comap V.subtype
  let x' : V := ⟨x, hx⟩
  have hU : Dense (U : Set V) := by
    rw [Subtype.dense_iff]
    have he : Subtype.val '' (U : Set V) = A := by
      ext y
      constructor
      · rintro ⟨a, ha, rfl⟩
        exact ha
      · intro hy
        exact ⟨⟨y, Submodule.le_topologicalClosure _ hy⟩, hy, rfl⟩
    change (V : Set E) ⊆ closure ((Subtype.val : V → E) '' (U : Set V))
    rw [he]
    exact subset_rfl
  letI := Fintype.ofFinite ι
  let J := ContinuousLinearMap.pi (fun i ↦ (M i).comp V.subtypeL)
  have hj : x' ∈ J.ker := by
    change (fun i ↦ M i x) = 0
    exact funext hM
  have hmem : x' ∈ (U ⊓ J.ker).topologicalClosure :=
    (closure_inf_ker_eq_of_finiteDimensional U hU J).symm ▸ hj
  have hMap : MapsTo (Subtype.val : V → E) (U ⊓ J.ker : Submodule ℂ V)
      ((A : Set E) ∩ {y | ∀ i, M i y = 0}) := by
    intro y hy
    exact ⟨hy.1, fun i ↦ congrFun (show J y = 0 from hy.2) i⟩
  exact hMap.closure continuous_subtype_val hmem

end

end Masullo
