import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Topology.Algebra.LinearMapCompletion
import Mathlib.Topology.Algebra.UniformMulAction

open Topology UniformSpace
open scoped TensorProduct

namespace Masullo

noncomputable section

/-- The topology and continuity data that determine the canonical
separated completion of a topological complex vector space. -/
structure TopologicalModuleStructure (X : Type*) [AddCommGroup X] [Module ℂ X] where
  topology : TopologicalSpace X
  group : @IsTopologicalAddGroup X topology _
  constSmul : @ContinuousConstSMul ℂ X topology _

namespace TopologicalModuleStructure

variable {X : Type*} [AddCommGroup X] [Module ℂ X]

abbrev uniformSpace (D : TopologicalModuleStructure X) : UniformSpace X :=
  @IsTopologicalAddGroup.rightUniformSpace X _ D.topology D.group

abbrev uniformGroup (D : TopologicalModuleStructure X) : @IsUniformAddGroup X D.uniformSpace _ :=
  @isUniformAddGroup_of_addCommGroup X _ D.topology D.group

abbrev uniformConstSmul (D : TopologicalModuleStructure X) :
    @UniformContinuousConstSMul ℂ X D.uniformSpace _ :=
  @uniformContinuousConstSMul_of_continuousConstSMul ℂ X _ _ D.uniformSpace
    D.uniformGroup D.constSmul

abbrev Completed (D : TopologicalModuleStructure X) : Type _ :=
  @Completion X D.uniformSpace

instance (D : TopologicalModuleStructure X) : UniformSpace D.Completed :=
  inferInstanceAs (UniformSpace (@Completion X D.uniformSpace))

instance (D : TopologicalModuleStructure X) : AddCommGroup D.Completed :=
  @Completion.instAddCommGroup X D.uniformSpace _ D.uniformGroup

instance (D : TopologicalModuleStructure X) : Module ℂ D.Completed :=
  @Completion.instModule ℂ X D.uniformSpace _ D.uniformGroup _ _ D.uniformConstSmul

/-- The canonical image of a vector in the separated completion. -/
def incl (D : TopologicalModuleStructure X) (x : X) : D.Completed :=
  @Completion.coe' X D.uniformSpace x

/-- A continuous linear map to a complete Hausdorff space extends to the completion. -/
theorem exists_continuousLinearMap_extend
    {X Y : Type*} [AddCommGroup X] [Module ℂ X]
    [UniformSpace Y] [AddCommGroup Y] [Module ℂ Y] [IsUniformAddGroup Y]
    [CompleteSpace Y] [T2Space Y] [ContinuousConstSMul ℂ Y]
    (D : TopologicalModuleStructure X)
    (f : letI : TopologicalSpace X := D.topology; X →L[ℂ] Y) :
    ∃ F : D.Completed →L[ℂ] Y, ∀ x, F (D.incl x) = f x := by
  letI : UniformSpace X := D.uniformSpace
  letI : IsUniformAddGroup X := D.uniformGroup
  letI : UniformContinuousConstSMul ℂ X := D.uniformConstSmul
  let t := f.toAddMonoidHom
  let L := t.extension f.continuous
  have hc : Continuous L := t.continuous_extension f.continuous
  have hv (x : X) : L (D.incl x) = f x := t.extension_coe f.continuous x
  refine ⟨⟨{ __ := L, map_smul' := fun a z => ?_ }, hc⟩, hv⟩
  have ha : Continuous (fun w : Completion X => a • w) := by
    change Continuous (Completion.map (fun x : X => a • x))
    exact Completion.continuous_map
  refine Completion.denseRange_coe.induction_on z
    (isClosed_eq (hc.comp ha) (hc.const_smul a)) ?_
  intro x
  change L (a • (x : Completion X)) = a • L (x : Completion X)
  rw [← Completion.coe_smul]
  exact (hv (a • x)).trans ((f.map_smul a x).trans (congrArg (a • ·) (hv x).symm))

/-- Continuous linear maps out of a tensor completion are determined on elementary tensors. -/
theorem continuousLinearMap_ext_on_tmul
    {A R V : Type*} [AddCommGroup A] [Module ℂ A]
    [AddCommGroup R] [Module ℂ R]
    [AddCommGroup V] [Module ℂ V] [TopologicalSpace V] [T2Space V]
    (D : TopologicalModuleStructure (A ⊗[ℂ] R))
    {F G : D.Completed →L[ℂ] V}
    (h : ∀ a r, F (D.incl (a ⊗ₜ[ℂ] r)) =
      G (D.incl (a ⊗ₜ[ℂ] r))) : F = G := by
  let X := A ⊗[ℂ] R
  letI : UniformSpace X := D.uniformSpace
  letI : IsUniformAddGroup X := D.uniformGroup
  have hx (z : X) : F (D.incl z) = G (D.incl z) := by
    induction z using TensorProduct.induction_on with
    | zero =>
      rw [show D.incl 0 = 0 from Completion.coe_zero, map_zero, map_zero]
    | tmul a r => exact h a r
    | add x y hx hy =>
      rw [show D.incl (x+y) = D.incl x + D.incl y from Completion.coe_add x y,
        map_add, map_add, hx, hy]
  apply ContinuousLinearMap.ext
  intro z
  exact Completion.denseRange_coe.induction_on z (isClosed_eq F.continuous G.continuous) hx

theorem eq_of_topology_eq {D D' : TopologicalModuleStructure X} (h : D.topology = D'.topology) :
    D = D' := by
  cases D
  cases D'
  cases h
  rfl

/-- Equal topologies give the canonical continuous-linear isomorphism of completions. -/
def completionEquiv {D D' : TopologicalModuleStructure X} (h : D.topology = D'.topology) :
    D.Completed ≃L[ℂ] D'.Completed := by
  have he := eq_of_topology_eq h
  subst D'
  exact ContinuousLinearEquiv.refl ℂ D.Completed

theorem completionEquiv_incl {D D' : TopologicalModuleStructure X}
    (h : D.topology = D'.topology) (x : X) :
    completionEquiv h (D.incl x) = D'.incl x := by
  have he := eq_of_topology_eq h
  subst D'
  rfl

end TopologicalModuleStructure

end

end Masullo
