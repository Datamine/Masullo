import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.LocallyConvex.Barrelled
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Topology.Algebra.Module.Spaces.CompactConvergenceCLM

open Bornology Filter Function Set
open scoped CompactConvergenceCLM TensorProduct Topology UniformConvergenceCLM

namespace Masullo

universe u

section Sequential

variable {E F G : Type*} [AddCommGroup E] [Module ℂ E] [UniformSpace E]
  [IsUniformAddGroup E] [ContinuousSMul ℂ E] [FirstCountableTopology E] [BaireSpace E]
  [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
  [AddCommGroup G] [Module ℂ G] [UniformSpace G] [IsUniformAddGroup G]
  [ContinuousSMul ℂ G] [PolynormableSpace ℂ G]

/-- Proposition C.2.3.11. Separate sequential continuity implies joint
sequential continuity with a first-countable Baire first factor. -/
theorem bilinear_seqContinuous_of_separate (A : E →ₗ[ℂ] F →ₗ[ℂ] G)
    (hE : ∀ y, SeqContinuous fun x => A x y) (hF : ∀ x, SeqContinuous (A x)) :
    SeqContinuous fun p : E × F => A p.1 p.2 := by
  intro u p hu
  have hx : Tendsto (fun n => (u n).1) atTop (𝓝 p.1) := continuous_fst.continuousAt.tendsto.comp hu
  have hy : Tendsto (fun n => (u n).2) atTop (𝓝 p.2) := continuous_snd.continuousAt.tendsto.comp hu
  let B (n : ℕ) : E →L[ℂ] G := ⟨(LinearMap.applyₗ' ℂ ((u n).2)).comp A, (hE _).continuous⟩
  have hpoint (x : E) : IsVonNBounded ℂ (range fun n => B n x) :=
    ((hF x) hy).isVonNBounded_range ℂ
  have heq : EquicontinuousAt (fun n x => B n x) (0 : E) :=
    (PolynormableSpace.banach_steinhaus (𝓕 := B) hpoint).equicontinuous 0
  have hzero : Tendsto (fun n => (u n).1 - p.1) atTop (𝓝 0) := by
    have hc : Tendsto (fun _ : ℕ => p.1) atTop (𝓝 p.1) := tendsto_const_nhds
    simpa only [sub_self] using hx.sub hc
  have hsmall : Tendsto (fun n => B n ((u n).1 - p.1)) atTop (𝓝 0) := by
    apply tendsto_def.mpr
    intro V hV
    have hUV : {z : G × G | z.2 - z.1 ∈ V} ∈ uniformity G := by
      rw [uniformity_eq_comap_nhds_zero G]
      exact preimage_mem_comap hV
    have hev := hzero.eventually (heq _ hUV)
    filter_upwards [hev] with n hn
    change B n ((u n).1 - p.1) ∈ V
    simpa only [mem_ofPred_eq, map_zero, sub_zero] using hn n
  have hsum := hsmall.add ((hF p.1) hy)
  rw [zero_add] at hsum
  refine hsum.congr fun n => ?_
  change B n ((u n).1 - p.1) + B n p.1 = B n (u n).1
  rw [map_sub, sub_add_cancel]

end Sequential

section Approximation

variable {E F G : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℂ E]
  [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul ℂ F]
  [AddCommGroup G] [Module ℂ G] [TopologicalSpace G] [IsTopologicalAddGroup G] [ContinuousSMul ℂ G]

/-- The tensor-to-operator map in (C.2.4.6), with compact convergence on the target. -/
noncomputable def tensorOperator (E F : Type*) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul ℂ F] :
    ((E →L[ℂ] ℂ) ⊗[ℂ] F) →ₗ[ℂ] (E →L_c[ℂ] F) :=
  TensorProduct.lift {
    toFun := fun φ => {
      toFun := fun y => φ.smulRight y
      map_add' := by
        intro x y
        ext z
        exact smul_add (φ z) x y
      map_smul' := by
        intro c y
        ext z
        exact smul_comm (φ z) c y }
    map_add' := by
      intro φ ψ
      ext y z
      exact add_smul (φ z) (ψ z) y
    map_smul' := by
      intro c φ
      ext y z
      exact mul_smul c (φ z) y }

omit [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] in
@[simp]
theorem tensorOperator_tmul (φ : E →L[ℂ] ℂ) (y : F) (x : E) :
    tensorOperator E F (φ ⊗ₜ[ℂ] y) x = φ x • y := by
  rw [tensorOperator, TensorProduct.lift.tmul]
  rfl

omit [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] in
private theorem tensorOperator_postcomp (A : F →L[ℂ] G) :
    MapsTo (A.postcompCompactConvergenceCLM E)
      (range (tensorOperator E F)) (range (tensorOperator E G)) := by
  rintro _ ⟨v, rfl⟩
  induction v using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp only [map_zero]⟩
  | tmul φ y =>
      refine ⟨φ ⊗ₜ[ℂ] (A y), ?_⟩
      ext x
      change tensorOperator E G (φ ⊗ₜ[ℂ] (A y)) x = A (tensorOperator E F (φ ⊗ₜ[ℂ] y) x)
      simp only [tensorOperator_tmul, map_smul]
  | add v w hv hw =>
      obtain ⟨v', hv'⟩ := hv
      obtain ⟨w', hw'⟩ := hw
      exact ⟨v' + w', by simp only [map_add, hv', hw']⟩

omit [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] [IsTopologicalAddGroup F] [ContinuousSMul ℂ F] in
private theorem tensorOperator_precomp (A : E →L[ℂ] F) :
    MapsTo (A.precompCompactConvergenceCLM G)
      (range (tensorOperator F G)) (range (tensorOperator E G)) := by
  rintro _ ⟨v, rfl⟩
  induction v using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp only [map_zero]⟩
  | tmul φ y =>
      refine ⟨(φ.comp A) ⊗ₜ[ℂ] y, ?_⟩
      ext x
      change tensorOperator E G ((φ.comp A) ⊗ₜ[ℂ] y) x = tensorOperator F G (φ ⊗ₜ[ℂ] y) (A x)
      simp only [tensorOperator_tmul, ContinuousLinearMap.comp_apply]
  | add v w hv hw =>
      obtain ⟨v', hv'⟩ := hv
      obtain ⟨w', hw'⟩ := hw
      exact ⟨v' + w', by simp only [map_add, hv', hw']⟩

private theorem closure_of_tensorOperator_image {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : Continuous f) {s : Set X} {t : Set Y} (h : MapsTo f s t) :
    MapsTo f (closure s) (closure t) := h.closure hf

/-- The compact-convergence variant of the approximation property. -/
def HasCompactApproximation (E : Type*) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] : Prop :=
  (ContinuousLinearMap.id ℂ E : E →L_c[ℂ] E) ∈ closure (range (tensorOperator E E))

theorem compactApproximation_dense_out (h : HasCompactApproximation E) :
    DenseRange (tensorOperator E F) := by
  intro A
  let A' : E →L[ℂ] F := A
  exact closure_of_tensorOperator_image (A'.postcompCompactConvergenceCLM E).continuous
    (tensorOperator_postcomp A') h

omit [IsTopologicalAddGroup F] [ContinuousSMul ℂ F] in
theorem compactApproximation_dense_in (h : HasCompactApproximation E) :
    DenseRange (tensorOperator F E) := by
  intro A
  let A' : F →L[ℂ] E := A
  exact closure_of_tensorOperator_image (A'.precompCompactConvergenceCLM E).continuous
    (tensorOperator_precomp A') h

/-- The four approximation tests using uniform convergence on compact sets. -/
theorem compactApproximation_criteria (E : Type u) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] :
    (HasCompactApproximation E ↔ DenseRange (tensorOperator E E)) ∧
    (HasCompactApproximation E ↔ ∀ (F : Type u) [AddCommGroup F] [Module ℂ F]
      [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul ℂ F], DenseRange (tensorOperator E F)) ∧
    (HasCompactApproximation E ↔ ∀ (F : Type u) [AddCommGroup F] [Module ℂ F]
      [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul ℂ F], DenseRange (tensorOperator F E)) :=
  ⟨⟨compactApproximation_dense_out, fun h => h _⟩,
    ⟨fun h _ _ _ _ _ _ => compactApproximation_dense_out h, fun h => h E _⟩,
    ⟨fun h _ _ _ _ _ _ => compactApproximation_dense_in h, fun h => h E _⟩⟩

/-- The tensor-to-operator map with the manuscript's precompact convergence
topology on the target. -/
noncomputable def precompactTensorOperator (E F : Type*) [AddCommGroup E] [Module ℂ E]
    [UniformSpace E] [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
    [IsTopologicalAddGroup F] [ContinuousSMul ℂ F] :
    ((E →L[ℂ] ℂ) ⊗[ℂ] F) →ₗ[ℂ] (E →Lᵤ[ℂ, {S : Set E | TotallyBounded S}] F) :=
  tensorOperator E F

/-- Approximation of the identity in the precompact convergence topology. -/
def HasPrecompactApproximation (E : Type*) [AddCommGroup E] [Module ℂ E] [UniformSpace E]
    [IsUniformAddGroup E] [ContinuousSMul ℂ E] : Prop :=
  (ContinuousLinearMap.id ℂ E : E →Lᵤ[ℂ, {S : Set E | TotallyBounded S}] E) ∈
    closure (range (precompactTensorOperator E E))

/-- Approximation of the identity implies density for every target. -/
theorem precompactApproximation_dense_out {X Y : Type*} [AddCommGroup X] [Module ℂ X]
    [UniformSpace X] [IsUniformAddGroup X] [ContinuousSMul ℂ X]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y] [IsTopologicalAddGroup Y] [ContinuousSMul ℂ Y]
    (h : HasPrecompactApproximation X) : DenseRange (precompactTensorOperator X Y) := by
  intro A
  let a : X →L[ℂ] Y := A
  let post := a.postcompUniformConvergenceCLM (σ := RingHom.id ℂ) (ρ := RingHom.id ℂ)
    {S : Set X | TotallyBounded S}
  have hp : MapsTo post (range (precompactTensorOperator X X))
      (range (precompactTensorOperator X Y)) := by
    intro B hB
    exact tensorOperator_postcomp a hB
  exact hp.closure post.continuous h

/-- Approximation of the identity implies density for every source. -/
theorem precompactApproximation_dense_in {X Y : Type*} [AddCommGroup X] [Module ℂ X]
    [UniformSpace X] [IsUniformAddGroup X] [ContinuousSMul ℂ X]
    [AddCommGroup Y] [Module ℂ Y] [UniformSpace Y] [IsUniformAddGroup Y]
    (h : HasPrecompactApproximation X) : DenseRange (precompactTensorOperator Y X) := by
  intro A
  let a : Y →L[ℂ] X := A
  let pre := a.precompUniformConvergenceCLM (τ := RingHom.id ℂ) (ρ := RingHom.id ℂ)
    X {S : Set Y | TotallyBounded S}
    {S : Set X | TotallyBounded S} (fun S hS => hS.image a.uniformContinuous)
  have hp : MapsTo pre (range (precompactTensorOperator X X))
      (range (precompactTensorOperator Y X)) := by
    intro B hB
    exact tensorOperator_precomp a hB
  exact hp.closure pre.continuous h

/-- Lemma C.2.4.15 in the topology of uniform convergence on precompact sets. -/
theorem precompactApproximation_criteria (X : Type u) [AddCommGroup X] [Module ℂ X]
    [UniformSpace X] [IsUniformAddGroup X] [ContinuousSMul ℂ X] :
    (HasPrecompactApproximation X ↔ DenseRange (precompactTensorOperator X X)) ∧
    (HasPrecompactApproximation X ↔ ∀ (Y : Type u) [AddCommGroup Y] [Module ℂ Y]
      [UniformSpace Y] [IsUniformAddGroup Y] [ContinuousSMul ℂ Y],
        DenseRange (precompactTensorOperator X Y)) ∧
    (HasPrecompactApproximation X ↔ ∀ (Y : Type u) [AddCommGroup Y] [Module ℂ Y]
      [UniformSpace Y] [IsUniformAddGroup Y] [ContinuousSMul ℂ Y],
        DenseRange (precompactTensorOperator Y X)) :=
  ⟨⟨precompactApproximation_dense_out, fun h => h _⟩,
    ⟨fun h _ _ _ _ _ _ => precompactApproximation_dense_out h, fun h => h X _⟩,
    ⟨fun h _ _ _ _ _ _ => precompactApproximation_dense_in h, fun h => h X _⟩⟩

end Approximation

end Masullo
