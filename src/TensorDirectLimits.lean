import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.TensorProduct.DirectLimit

open Function Module
open scoped TensorProduct

namespace Masullo

noncomputable section

variable {I J : Type*} [Preorder I] [Preorder J] [DecidableEq I] [DecidableEq J]
variable {A : I → Type*} {B : J → Type*}
variable [∀ n, AddCommGroup (A n)] [∀ n, Module ℂ (A n)]
variable [∀ n, AddCommGroup (B n)] [∀ n, Module ℂ (B n)]
variable (f : ∀ m n, m ≤ n → A m →ₗ[ℂ] A n) (g : ∀ m n, m ≤ n → B m →ₗ[ℂ] B n)

abbrev TensorStage (p : I × J) := A p.1 ⊗[ℂ] B p.2

def tensorStageMap (p q : I × J) (h : p ≤ q) :
    TensorStage (A := A) (B := B) p →ₗ[ℂ] TensorStage (A := A) (B := B) q :=
  TensorProduct.map (f p.1 q.1 h.1) (g p.2 q.2 h.2)

abbrev TensorStageLimit := Module.DirectLimit (TensorStage (A := A) (B := B)) (tensorStageMap f g)

abbrev tensorStageInclusion (p : I × J) :
    TensorStage (A := A) (B := B) p →ₗ[ℂ] TensorStageLimit f g :=
  Module.DirectLimit.of ℂ _ _ (tensorStageMap f g) p

private def firstStageInclusion (n : I) : A n →ₗ[ℂ] Module.DirectLimit A f :=
  Module.DirectLimit.of ℂ _ _ f n

private def secondStageInclusion (n : J) : B n →ₗ[ℂ] Module.DirectLimit B g :=
  Module.DirectLimit.of ℂ _ _ g n

/-- The canonical map from the two-index algebraic direct limit of stage
tensors to the tensor of the algebraic direct limits. -/
def tensorDirectLimitMap :
    TensorStageLimit f g →ₗ[ℂ] (Module.DirectLimit A f ⊗[ℂ] Module.DirectLimit B g) :=
  Module.DirectLimit.lift ℂ _ _ (tensorStageMap f g)
    (fun p => TensorProduct.map (firstStageInclusion f p.1) (secondStageInclusion g p.2))
    (fun p q h z => by
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul x y =>
        simp [tensorStageMap, firstStageInclusion, secondStageInclusion]
      | add z z' hz hz' => simp [map_add, hz, hz'])

@[simp] theorem tensorDirectLimitMap_on_stage (p : I × J)
    (w : TensorStage (A := A) (B := B) p) :
    tensorDirectLimitMap f g (tensorStageInclusion f g p w) =
      TensorProduct.map (Module.DirectLimit.of ℂ I A f p.1)
        (Module.DirectLimit.of ℂ J B g p.2) w := by
  rw [tensorDirectLimitMap, Module.DirectLimit.lift_of]
  rfl

variable [DirectedSystem A (f · · ·)] [DirectedSystem B (g · · ·)]

private def tensorRow (m : I) : A m →ₗ[ℂ] Module.DirectLimit B g →ₗ[ℂ] TensorStageLimit f g :=
  (Module.DirectLimit.lift ℂ J B g
    (fun n => ((TensorProduct.mk ℂ (A m) (B n)).flip).compr₂ (tensorStageInclusion f g (m, n)))
    (fun n n' hn y => by
      apply LinearMap.ext
      intro x
      change tensorStageInclusion f g (m, n') (x ⊗ₜ[ℂ] g n n' hn y) =
        tensorStageInclusion f g (m, n) (x ⊗ₜ[ℂ] y)
      have h : (m, n) ≤ (m, n') := ⟨le_rfl, hn⟩
      have he := Module.DirectLimit.of_f (f := tensorStageMap f g)
        (hij := h) (x := x ⊗ₜ[ℂ] y)
      simpa only [tensorStageMap, TensorProduct.map_tmul, DirectedSystem.map_self'] using he)).flip

omit [DirectedSystem B (g · · ·)] in
@[simp] private theorem tensorRow_on_stage (m : I) (n : J) (x : A m) (y : B n) :
    tensorRow f g m x (secondStageInclusion g n y) =
      tensorStageInclusion f g (m, n) (x ⊗ₜ[ℂ] y) := by
  rw [tensorRow, LinearMap.flip_apply, secondStageInclusion, Module.DirectLimit.lift_of]
  rfl

private def tensorFromLimits :
    (Module.DirectLimit A f ⊗[ℂ] Module.DirectLimit B g) →ₗ[ℂ] TensorStageLimit f g :=
  TensorProduct.lift (Module.DirectLimit.lift ℂ I A f (tensorRow f g)
    (fun m m' hm x => by
      apply Module.DirectLimit.hom_ext
      intro n
      apply LinearMap.ext
      intro y
      have h : (m, n) ≤ (m', n) := ⟨hm, le_rfl⟩
      have he := Module.DirectLimit.of_f (f := tensorStageMap f g)
        (hij := h) (x := x ⊗ₜ[ℂ] y)
      change tensorRow f g m' (f m m' hm x) (secondStageInclusion g n y) =
        tensorRow f g m x (secondStageInclusion g n y)
      rw [tensorRow_on_stage, tensorRow_on_stage]
      simpa only [tensorStageMap, TensorProduct.map_tmul, DirectedSystem.map_self'] using he))

@[simp] private theorem tensorFromLimits_on_tmul (m : I) (n : J) (x : A m) (y : B n) :
    tensorFromLimits f g (firstStageInclusion f m x ⊗ₜ[ℂ] secondStageInclusion g n y) =
      tensorStageInclusion f g (m, n) (x ⊗ₜ[ℂ] y) := by
  rw [tensorFromLimits, TensorProduct.lift.tmul, firstStageInclusion, Module.DirectLimit.lift_of]
  exact tensorRow_on_stage f g m n x y

variable [Nonempty I] [Nonempty J] [IsDirectedOrder I] [IsDirectedOrder J]

/-- Taking algebraic tensors commutes with the two-index direct limit. -/
def tensorDirectLimitEquiv :
    TensorStageLimit f g ≃ₗ[ℂ] (Module.DirectLimit A f ⊗[ℂ] Module.DirectLimit B g) := by
  apply LinearEquiv.ofLinear (tensorDirectLimitMap f g) (tensorFromLimits f g)
  · apply TensorProduct.ext'
    intro x y
    obtain ⟨m, x, rfl⟩ := Module.DirectLimit.exists_of x
    obtain ⟨n, y, rfl⟩ := Module.DirectLimit.exists_of y
    change tensorDirectLimitMap f g
        (tensorFromLimits f g (firstStageInclusion f m x ⊗ₜ[ℂ] secondStageInclusion g n y)) =
      firstStageInclusion f m x ⊗ₜ[ℂ] secondStageInclusion g n y
    rw [tensorFromLimits_on_tmul, tensorDirectLimitMap_on_stage, TensorProduct.map_tmul]
    rfl
  · apply Module.DirectLimit.hom_ext
    intro p
    apply TensorProduct.ext'
    intro x y
    change tensorFromLimits f g
        (tensorDirectLimitMap f g (tensorStageInclusion f g p (x ⊗ₜ[ℂ] y))) =
      tensorStageInclusion f g p (x ⊗ₜ[ℂ] y)
    rw [tensorDirectLimitMap_on_stage, TensorProduct.map_tmul]
    exact tensorFromLimits_on_tmul f g p.1 p.2 x y

@[simp] theorem tensorDirectLimitEquiv_on_stage (p : I × J)
    (w : TensorStage (A := A) (B := B) p) :
    tensorDirectLimitEquiv f g (tensorStageInclusion f g p w) =
      TensorProduct.map (Module.DirectLimit.of ℂ I A f p.1)
        (Module.DirectLimit.of ℂ J B g p.2) w :=
  tensorDirectLimitMap_on_stage f g p w

end

end Masullo
