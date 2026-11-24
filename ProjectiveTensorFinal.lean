import ProjectiveTensorTopology
import TopologicalLinearLimits
import Mathlib.LinearAlgebra.DirectSum.TensorProduct
import Mathlib.LinearAlgebra.TensorProduct.DirectLimit

open Filter Function Set Topology
open scoped NNReal TensorProduct

namespace Masullo

noncomputable section

variable {I E F : Type*} {A : I → Type*}
  [AddCommGroup E] [Module ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [∀ i, AddCommGroup (A i)] [∀ i, Module ℂ (A i)] [∀ i, TopologicalSpace (A i)]
  [∀ i, PolynormableSpace ℂ (A i)]

private abbrev UnitBall (F : Type*) [Norm F] := {y : F // ‖y‖ ≤ 1}

private def tensorUnitBallSeminorm (q : Seminorm ℂ (E ⊗[ℂ] F)) (y : UnitBall F) :
    Seminorm ℂ E :=
  q.comp ((TensorProduct.mk ℂ E F).flip y.val)

private theorem normed_continuous_seminorm_le (p : Seminorm ℂ F) (hp : Continuous p) :
    ∃ C : ℝ≥0, ∀ y, p y ≤ (C : ℝ) * ‖y‖ := by
  obtain ⟨s, C, _, hs⟩ := Seminorm.bound_of_continuous (norm_withSeminorms ℂ F) p hp
  refine ⟨C, fun y => (hs y).trans ?_⟩
  have h : s.sup (fun _ => normSeminorm ℂ F) ≤ normSeminorm ℂ F :=
    Finset.sup_le fun _ _ => le_rfl
  exact mul_le_mul_of_nonneg_left (h y) C.coe_nonneg

private theorem projective_stage_bound
    (j : ∀ i, A i →ₗ[ℂ] E) (q : Seminorm ℂ (E ⊗[ℂ] F)) (i : I)
    (hq : Continuous[projectiveTensorTopology (A i) F, inferInstance]
      (q.comp ((j i).rTensor F))) :
    ∃ p : Seminorm ℂ (A i), Continuous p ∧ ∀ x y, q (j i x ⊗ₜ[ℂ] y) ≤ p x * ‖y‖ := by
  letI : PolynormableSpace ℂ F := (norm_withSeminorms ℂ F).toPolynormableSpace
  letI : IsTopologicalAddGroup (A i) := (PolynormableSpace.withSeminorms ℂ (A i)).topologicalAddGroup
  letI : TopologicalSpace (A i ⊗[ℂ] F) := projectiveTensorTopology (A i) F
  letI : TopologicalSpace (E ⊗[ℂ] F) := ⊥
  let B : A i →ₗ[ℂ] F →ₗ[ℂ] E ⊗[ℂ] F :=
    (TensorProduct.curry ((j i).rTensor F))
  have hB : Continuous (fun z : A i × F => q (B z.1 z.2)) := by
    exact hq.comp (continuous_projectiveTensor_tmul (E := A i) (F := F))
  obtain ⟨p, r, hp, hr, h⟩ := bilinear_bound_of_nhds B q
    (((hB.tendsto' (0, 0) 0 (by simp)).eventually (Iic_mem_nhds zero_lt_one)))
  obtain ⟨C, hC⟩ := normed_continuous_seminorm_le r hr
  refine ⟨C • p, continuous_const.mul hp, fun x y => ?_⟩
  calc
    q (j i x ⊗ₜ[ℂ] y) ≤ p x * r y := h x y
    _ ≤ p x * ((C : ℝ) * ‖y‖) := mul_le_mul_of_nonneg_left (hC y) (apply_nonneg p x)
    _ = (C • p) x * ‖y‖ := by change _ = ((C : ℝ) * p x) * ‖y‖; ring

/-- The projective tensor topology commutes with locally convex final topologies
from a spanning family when the other tensor factor is normable. -/
theorem projectiveTensor_final_of_normed
    (j : ∀ i, A i →ₗ[ℂ] E)
    (hspan : Submodule.span ℂ (⋃ i, range (j i)) = ⊤) :
    letI : TopologicalSpace E := locallyConvexFinalTopology j
    letI : ∀ i, TopologicalSpace (A i ⊗[ℂ] F) := fun i => projectiveTensorTopology (A i) F
    projectiveTensorTopology E F = locallyConvexFinalTopology (fun i => (j i).rTensor F) := by
  letI : TopologicalSpace E := locallyConvexFinalTopology j
  letI : ∀ i, TopologicalSpace (A i ⊗[ℂ] F) := fun i => projectiveTensorTopology (A i) F
  let k := fun i => (j i).rTensor F
  let D := E ⊗[ℂ] F
  letI : ∀ i, IsTopologicalAddGroup (A i) :=
    fun i => (PolynormableSpace.withSeminorms ℂ (A i)).topologicalAddGroup
  letI : PolynormableSpace ℂ E := (locallyConvexFinal_withSeminorms j).toPolynormableSpace
  letI : PolynormableSpace ℂ F := (norm_withSeminorms ℂ F).toPolynormableSpace
  letI : ∀ i, IsTopologicalAddGroup (A i ⊗[ℂ] F) :=
    fun i => (projectiveTensor_withSeminorms (E := A i) (F := F)).topologicalAddGroup
  let P := projectiveTensorTopology E F
  let L := locallyConvexFinalTopology k
  have hPL : Continuous[P, L] (id : D → D) := by
    letI : TopologicalSpace D := P
    have hWP := projectiveTensor_withSeminorms (E := E) (F := F)
    letI : IsTopologicalAddGroup D := hWP.topologicalAddGroup
    let W := locallyConvexFinal_withSeminorms k
    apply (@WithSeminorms.continuous_iff_continuous_comp ℂ ℂ D D
      _ _ _ _ _ _ _ (RingHom.id ℂ) _ _ P inferInstance L W LinearMap.id).mpr
    intro q
    have hs (i : I) := projective_stage_bound j q.val i (q.property i)
    choose p hp hq using hs
    let V : Submodule ℂ E :=
      { carrier := {x | ∃ C : ℝ, ∀ y : UnitBall F, tensorUnitBallSeminorm q.val y x ≤ C}
        zero_mem' := ⟨0, fun y => by simp⟩
        add_mem' := by
          rintro x z ⟨C, hC⟩ ⟨B, hB⟩
          exact ⟨C + B, fun y => (map_add_le_add (tensorUnitBallSeminorm q.val y) x z).trans
            (add_le_add (hC y) (hB y))⟩
        smul_mem' := by
          rintro a x ⟨C, hC⟩
          refine ⟨‖a‖ * C, fun y => ?_⟩
          rw [map_smul_eq_mul]
          exact mul_le_mul_of_nonneg_left (hC y) (norm_nonneg _) }
    have hstage (i : I) (x : A i) (y : UnitBall F) :
        tensorUnitBallSeminorm q.val y (j i x) ≤ p i x :=
      (hq i x y.val).trans (mul_le_of_le_one_right (apply_nonneg _ _) y.property)
    have hV : V = ⊤ := by
      apply top_unique
      rw [← hspan]
      apply Submodule.span_le.mpr
      intro x hx
      obtain ⟨i, a, rfl⟩ := mem_iUnion.mp hx
      exact ⟨p i a, hstage i a⟩
    have hb : BddAbove (range (tensorUnitBallSeminorm q.val (F := F))) := by
      apply Seminorm.bddAbove_range_iff.mpr
      intro x
      obtain ⟨C, hC⟩ : x ∈ V := hV ▸ Submodule.mem_top
      refine ⟨C, ?_⟩
      rintro v ⟨y, hy⟩
      exact hy ▸ hC y
    let r : Seminorm ℂ E := ⨆ y : UnitBall F, tensorUnitBallSeminorm q.val y
    have hr_apply (x : E) : r x = ⨆ y : UnitBall F, tensorUnitBallSeminorm q.val y x :=
      Seminorm.iSup_apply hb
    letI : Nonempty (UnitBall F) := ⟨⟨0, by simp⟩⟩
    have hr : Continuous r := by
      apply locallyConvexFinal_seminorm_continuous j
      intro i
      exact Seminorm.continuous_of_le (q := p i) (hp i) fun x => by
        change r (j i x) ≤ p i x
        rw [hr_apply]
        exact ciSup_le (hstage i x)
    have hBound (x : E) (y : F) : q.val (x ⊗ₜ[ℂ] y) ≤ r x * ‖y‖ := by
      by_cases hy : y = 0
      · simp [hy]
      let a : ℂ := (‖y‖ : ℝ)
      have ha : a ≠ 0 := by simpa [a] using hy
      have han : ‖a‖ = ‖y‖ := by simp [a]
      let u : UnitBall F := ⟨a⁻¹ • y, by
        rw [norm_smul, norm_inv, han, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hy)]⟩
      have hu : a • u.val = y := by
        change a • (a⁻¹ • y) = y
        rw [smul_smul, mul_inv_cancel₀ ha, one_smul]
      have hle : tensorUnitBallSeminorm q.val u x ≤ r x := by
        rw [hr_apply]
        exact le_ciSup ((Seminorm.bddAbove_range_iff.mp hb) x) u
      calc
        q.val (x ⊗ₜ[ℂ] y) = ‖a‖ * tensorUnitBallSeminorm q.val u x := by
          rw [← hu, TensorProduct.tmul_smul, map_smul_eq_mul]
          rfl
        _ ≤ r x * ‖y‖ := by
          rw [han, mul_comm (r x)]
          exact mul_le_mul_of_nonneg_left hle (norm_nonneg _)
    exact hWP.continuous_seminorm
      (⟨q.val, r, normSeminorm ℂ F, hr, continuous_norm, hBound⟩ : ProjectiveTensorTest E F)
  have hLP : Continuous[L, P] (id : D → D) := by
    letI : TopologicalSpace D := P
    letI : PolynormableSpace ℂ D := projectiveTensor_withSeminorms.toPolynormableSpace
    apply (locallyConvexFinal_continuous_iff k (LinearMap.id : D →ₗ[ℂ] D)).mpr
    intro i
    exact projectiveTensor_map_continuous
      ⟨j i, locallyConvexFinal_stage_continuous j i⟩ (ContinuousLinearMap.id ℂ F)
  exact le_antisymm (continuous_id_iff_le.mp hPL) (continuous_id_iff_le.mp hLP)


open scoped DirectSum

variable (A F)

/-- The direct sum of a family with the locally convex final topology. -/
abbrev locallyConvexSumTopology [DecidableEq I] : TopologicalSpace (⨁ i, A i) :=
  locallyConvexFinalTopology (DirectSum.lof ℂ I A)

variable {A F}

private def projectiveTensor_final_equiv {Y : Type*} [AddCommGroup Y] [Module ℂ Y]
    (j : ∀ i, A i →ₗ[ℂ] E) (k : ∀ i, A i ⊗[ℂ] F →ₗ[ℂ] Y)
    (hspan : Submodule.span ℂ (⋃ i, range (j i)) = ⊤)
    (e : E ⊗[ℂ] F ≃ₗ[ℂ] Y) (he : ∀ i, e.toLinearMap.comp ((j i).rTensor F) = k i) :
    letI : TopologicalSpace E := locallyConvexFinalTopology j
    letI : ∀ i, TopologicalSpace (A i ⊗[ℂ] F) := fun i => projectiveTensorTopology (A i) F
    letI : TopologicalSpace Y := locallyConvexFinalTopology k
    letI : TopologicalSpace (E ⊗[ℂ] F) := projectiveTensorTopology E F
    E ⊗[ℂ] F ≃L[ℂ] Y := by
  letI : TopologicalSpace E := locallyConvexFinalTopology j
  letI : ∀ i, TopologicalSpace (A i ⊗[ℂ] F) := fun i => projectiveTensorTopology (A i) F
  letI : ∀ i, IsTopologicalAddGroup (A i ⊗[ℂ] F) :=
    fun i => (projectiveTensor_withSeminorms (E := A i) (F := F)).topologicalAddGroup
  letI : TopologicalSpace Y := locallyConvexFinalTopology k
  letI : TopologicalSpace (E ⊗[ℂ] F) := projectiveTensorTopology E F
  letI : PolynormableSpace ℂ Y := (locallyConvexFinal_withSeminorms k).toPolynormableSpace
  letI : PolynormableSpace ℂ (E ⊗[ℂ] F) :=
    (projectiveTensor_withSeminorms (E := E) (F := F)).toPolynormableSpace
  have h := projectiveTensor_final_of_normed (F := F) j hspan
  refine ⟨e, ?_, ?_⟩
  · change Continuous[projectiveTensorTopology E F, locallyConvexFinalTopology k] e.toLinearMap
    rw [h]
    apply (locallyConvexFinal_continuous_iff (fun i => (j i).rTensor F) _).mpr
    intro i
    rw [he]
    exact locallyConvexFinal_stage_continuous k i
  · apply (locallyConvexFinal_continuous_iff k e.symm.toLinearMap).mpr
    intro i
    change Continuous[projectiveTensorTopology (A i) F, projectiveTensorTopology E F]
      (e.symm.toLinearMap.comp (k i))
    rw [h, ← he, ← LinearMap.comp_assoc, LinearEquiv.symm_comp, LinearMap.id_comp]
    exact locallyConvexFinal_stage_continuous (fun i => (j i).rTensor F) i

/-- C.2.3.9(1), algebraic tensors. This is the canonical map from the sum of
the projective tensor products to the projective tensor product of the sum. -/
def projectiveTensorDirectSum (I : Type*) [DecidableEq I] (A : I → Type*)
    [∀ i, AddCommGroup (A i)] [∀ i, Module ℂ (A i)] [∀ i, TopologicalSpace (A i)]
    [∀ i, PolynormableSpace ℂ (A i)] (F : Type*) [NormedAddCommGroup F] [NormedSpace ℂ F] :
    letI : TopologicalSpace (⨁ i, A i) := locallyConvexSumTopology A
    letI : ∀ i, TopologicalSpace (A i ⊗[ℂ] F) := fun i => projectiveTensorTopology (A i) F
    letI : TopologicalSpace (⨁ i, A i ⊗[ℂ] F) := locallyConvexSumTopology (fun i => A i ⊗[ℂ] F)
    letI : TopologicalSpace ((⨁ i, A i) ⊗[ℂ] F) := projectiveTensorTopology (⨁ i, A i) F
    (⨁ i, A i ⊗[ℂ] F) ≃L[ℂ] ((⨁ i, A i) ⊗[ℂ] F) := by
  let j := DirectSum.lof ℂ I A
  let k := DirectSum.lof ℂ I (fun i => A i ⊗[ℂ] F)
  have hspan : Submodule.span ℂ (⋃ i, range (j i)) = ⊤ := by
    apply top_unique
    intro x hx
    clear hx
    induction x using DirectSum.induction_on with
    | zero => exact Submodule.zero_mem _
    | of i a =>
      apply Submodule.subset_span
      exact mem_iUnion.mpr ⟨i, a, rfl⟩
    | add x y hx hy => exact Submodule.add_mem _ hx hy
  have he (i : I) : (TensorProduct.directSumLeft ℂ ℂ A F).toLinearMap.comp ((j i).rTensor F) =
      k i := by
    apply TensorProduct.ext'
    exact TensorProduct.directSumLeft_tmul_lof ℂ ℂ i
  letI : TopologicalSpace (⨁ i, A i) := locallyConvexSumTopology A
  letI : ∀ i, TopologicalSpace (A i ⊗[ℂ] F) := fun i => projectiveTensorTopology (A i) F
  letI : TopologicalSpace (⨁ i, A i ⊗[ℂ] F) := locallyConvexSumTopology (fun i => A i ⊗[ℂ] F)
  letI : TopologicalSpace ((⨁ i, A i) ⊗[ℂ] F) := projectiveTensorTopology (⨁ i, A i) F
  exact (projectiveTensor_final_equiv j k hspan _ he).symm


theorem projectiveTensorDirectSum_lof_tmul [DecidableEq I] (i : I) (x : A i) (y : F) :
    projectiveTensorDirectSum I A F
      (DirectSum.lof ℂ I (fun i => A i ⊗[ℂ] F) i (x ⊗ₜ[ℂ] y)) =
      DirectSum.lof ℂ I A i x ⊗ₜ[ℂ] y :=
  TensorProduct.directSumLeft_symm_lof_tmul ℂ ℂ i x y

variable [DecidableEq I] [Preorder I] [IsDirectedOrder I] [Nonempty I]

/-- C.2.3.9(2). The canonical projective tensor map from a filtered limit
is a topological isomorphism for a normable second factor. -/
def projectiveTensorDirectLimit (f : ∀ i j, i ≤ j → A i →ₗ[ℂ] A j)
    [DirectedSystem A (f · · ·)] :
    let j := Module.DirectLimit.of ℂ I A f
    let g := fun i k h => (f i k h).rTensor F
    let L := Module.DirectLimit A f
    let T := Module.DirectLimit (fun i => A i ⊗[ℂ] F) g
    letI : TopologicalSpace L := locallyConvexFinalTopology j
    letI : ∀ i, TopologicalSpace (A i ⊗[ℂ] F) := fun i => projectiveTensorTopology (A i) F
    letI : TopologicalSpace T := locallyConvexFinalTopology (Module.DirectLimit.of ℂ I _ g)
    letI : TopologicalSpace (L ⊗[ℂ] F) := projectiveTensorTopology L F
    T ≃L[ℂ] (L ⊗[ℂ] F) := by
  let j := Module.DirectLimit.of ℂ I A f
  let k := Module.DirectLimit.of ℂ I (fun i => A i ⊗[ℂ] F) (fun i l h => (f i l h).rTensor F)
  have hspan : Submodule.span ℂ (⋃ i, range (j i)) = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨i, a, rfl⟩ := Module.DirectLimit.exists_of x
    exact Submodule.subset_span (mem_iUnion.mpr ⟨i, a, rfl⟩)
  have he (i : I) : (TensorProduct.directLimitLeft f F).toLinearMap.comp ((j i).rTensor F) =
      k i := LinearMap.ext fun z => TensorProduct.directLimitLeft_rTensor_of f F z
  letI : TopologicalSpace (Module.DirectLimit A f) := locallyConvexFinalTopology j
  letI : ∀ i, TopologicalSpace (A i ⊗[ℂ] F) := fun i => projectiveTensorTopology (A i) F
  letI : TopologicalSpace (Module.DirectLimit (fun i => A i ⊗[ℂ] F)
      (fun i l h => (f i l h).rTensor F)) := locallyConvexFinalTopology k
  letI : TopologicalSpace (Module.DirectLimit A f ⊗[ℂ] F) := projectiveTensorTopology _ F
  exact (projectiveTensor_final_equiv j k hspan _ he).symm


theorem projectiveTensorDirectLimit_of_tmul (f : ∀ i j, i ≤ j → A i →ₗ[ℂ] A j)
    [DirectedSystem A (f · · ·)] (i : I) (x : A i) (y : F) :
    projectiveTensorDirectLimit (F := F) f
      (Module.DirectLimit.of ℂ I (fun i => A i ⊗[ℂ] F)
        (fun i j h => (f i j h).rTensor F) i (x ⊗ₜ[ℂ] y)) =
      Module.DirectLimit.of ℂ I A f i x ⊗ₜ[ℂ] y :=
  TensorProduct.directLimitLeft_symm_of_tmul f F (i := i) x y

end
end Masullo
