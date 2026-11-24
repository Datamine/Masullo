import NormedTensorLimits
import TensorDirectLimits
import TopologicalLinearLimits

open Function Module Set Topology
open scoped TensorProduct

namespace Masullo

noncomputable section

variable {A B : ℕ → Type*}
variable [∀ n, NormedAddCommGroup (A n)] [∀ n, NormedSpace ℂ (A n)]
variable [∀ n, NormedAddCommGroup (B n)] [∀ n, NormedSpace ℂ (B n)]
variable (f : ∀ m n, m ≤ n → A m →ₗ[ℂ] A n) (g : ∀ m n, m ≤ n → B m →ₗ[ℂ] B n)
variable [DirectedSystem A (f · · ·)] [DirectedSystem B (g · · ·)]

abbrev normedDirectLimitTopology {C : ℕ → Type*} [∀ n, NormedAddCommGroup (C n)]
    [∀ n, NormedSpace ℂ (C n)] (m : ∀ a b, a ≤ b → C a →ₗ[ℂ] C b) :
    TopologicalSpace (Module.DirectLimit C m) :=
  locallyConvexFinalTopology (Module.DirectLimit.of ℂ ℕ C m)

abbrev tensorStageFinalTopology : TopologicalSpace (TensorStageLimit f g) :=
  letI (p : ℕ × ℕ) : TopologicalSpace (TensorStage (A := A) (B := B) p) :=
    projectiveTensorTopology (A p.1) (B p.2)
  locallyConvexFinalTopology (tensorStageInclusion f g)

/-- C.2.3.10. The canonical tensor map is a linear topological isomorphism
for the locally convex limits of countably many normable stages. -/
def countable_normed_projectiveTensor_directLimit :
    letI : TopologicalSpace (Module.DirectLimit A f) := normedDirectLimitTopology f
    letI : TopologicalSpace (Module.DirectLimit B g) := normedDirectLimitTopology g
    letI : TopologicalSpace (TensorStageLimit f g) := tensorStageFinalTopology f g
    letI : TopologicalSpace (Module.DirectLimit A f ⊗[ℂ] Module.DirectLimit B g) :=
      projectiveTensorTopology (Module.DirectLimit A f) (Module.DirectLimit B g)
    TensorStageLimit f g ≃L[ℂ] (Module.DirectLimit A f ⊗[ℂ] Module.DirectLimit B g) := by
  let X := Module.DirectLimit A f
  let Y := Module.DirectLimit B g
  letI : TopologicalSpace X := normedDirectLimitTopology f
  letI : TopologicalSpace Y := normedDirectLimitTopology g
  letI : TopologicalSpace (TensorStageLimit f g) := tensorStageFinalTopology f g
  letI : TopologicalSpace (X ⊗[ℂ] Y) := projectiveTensorTopology X Y
  letI (p : ℕ × ℕ) : TopologicalSpace (TensorStage (A := A) (B := B) p) :=
    projectiveTensorTopology (A p.1) (B p.2)
  letI (p : ℕ × ℕ) : IsTopologicalAddGroup (TensorStage (A := A) (B := B) p) :=
    (projectiveTensor_withSeminorms (E := A p.1) (F := B p.2)).topologicalAddGroup
  let a := Module.DirectLimit.of ℂ ℕ A f
  let b := Module.DirectLimit.of ℂ ℕ B g
  letI : PolynormableSpace ℂ X := (locallyConvexFinal_withSeminorms a).toPolynormableSpace
  letI : PolynormableSpace ℂ Y := (locallyConvexFinal_withSeminorms b).toPolynormableSpace
  let i (n : ℕ) : A n →L[ℂ] X := ⟨a n, locallyConvexFinal_stage_continuous a n⟩
  let j (n : ℕ) : B n →L[ℂ] Y := ⟨b n, locallyConvexFinal_stage_continuous b n⟩
  let e := tensorDirectLimitEquiv f g
  let W := projectiveTensor_withSeminorms (E := X) (F := Y)
  letI : PolynormableSpace ℂ (X ⊗[ℂ] Y) := W.toPolynormableSpace
  letI : IsTopologicalAddGroup (X ⊗[ℂ] Y) := W.topologicalAddGroup
  have he (p : ℕ × ℕ) :
      e.toLinearMap.comp (tensorStageInclusion f g p) =
        TensorProduct.map (i p.1).toLinearMap (j p.2).toLinearMap :=
    LinearMap.ext (tensorDirectLimitEquiv_on_stage f g p)
  refine ⟨e, ?_, ?_⟩
  · apply (locallyConvexFinal_continuous_iff (tensorStageInclusion f g) e.toLinearMap).mpr
    intro p
    rw [he p]
    exact projectiveTensor_map_continuous (i p.1) (j p.2)
  · apply ((locallyConvexFinal_withSeminorms (tensorStageInclusion f g)).continuous_iff_continuous_comp
      e.symm.toLinearMap).mpr
    intro Q
    let R := Q.val.comp e.symm.toLinearMap
    have hX : ∀ x : X, ∃ n, x ∈ range (i n) := Module.DirectLimit.exists_of
    have hY : ∀ y : Y, ∃ n, y ∈ range (j n) := Module.DirectLimit.exists_of
    have hc := (countable_projectiveTensor_stageCriterion i j hX hY
      (locallyConvexFinal_seminorm_continuous a) (locallyConvexFinal_seminorm_continuous b) R).mpr
    apply hc
    intro m n
    letI : TopologicalSpace (A m ⊗[ℂ] B n) := projectiveTensorTopology (A m) (B n)
    have he' : e.symm.toLinearMap.comp
        (TensorProduct.map (i m).toLinearMap (j n).toLinearMap) = tensorStageInclusion f g (m, n) := by
      apply LinearMap.ext
      intro z
      change e.symm (TensorProduct.map (i m).toLinearMap (j n).toLinearMap z) =
        tensorStageInclusion f g (m, n) z
      rw [← tensorDirectLimitEquiv_on_stage f g (m, n) z]
      exact e.symm_apply_apply _
    have hfun : (fun z : A m ⊗[ℂ] B n =>
        R (TensorProduct.map (i m).toLinearMap (j n).toLinearMap z)) =
        (fun z => Q.val (tensorStageInclusion f g (m, n) z)) :=
      funext fun z => congrArg Q.val (DFunLike.congr_fun he' z)
    change Continuous (fun z : A m ⊗[ℂ] B n =>
      R (TensorProduct.map (i m).toLinearMap (j n).toLinearMap z))
    exact hfun.symm ▸ Q.property (m, n)

end

end Masullo
