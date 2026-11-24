import CountableLimitContinuity
import FrechetFactorization
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient

open Function Set Topology
open scoped ComplexOrder

namespace Masullo

noncomputable section

variable {E X : Type*} {A B : ℕ → Type*}
variable [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [IsTopologicalAddGroup E] [T2Space E]
variable [AddCommGroup X] [Module ℂ X] [TopologicalSpace X] [IsTopologicalAddGroup X]
variable [∀ n, UniformSpace (A n)] [∀ n, AddCommGroup (A n)] [∀ n, Module ℂ (A n)]
variable [∀ n, IsUniformAddGroup (A n)] [∀ n, ContinuousSMul ℂ (A n)]
variable [∀ n, CompleteSpace (A n)] [∀ n, FirstCountableTopology (A n)] [∀ n, T2Space (A n)]
variable [∀ n, LocallyConvexSpace ℂ (A n)]
variable [∀ n, UniformSpace (B n)] [∀ n, AddCommGroup (B n)] [∀ n, Module ℂ (B n)]
variable [∀ n, IsUniformAddGroup (B n)] [∀ n, ContinuousSMul ℂ (B n)]
variable [∀ n, CompleteSpace (B n)] [∀ n, FirstCountableTopology (B n)]

/-- The LF open mapping theorem with a source exhausted by images of
Fréchet spaces. The quotient carries its actual quotient topology. -/
theorem lf_open_mapping (i : ∀ n, A n →L[ℂ] E) (j : ∀ n, B n →L[ℂ] X)
    (hi : ∀ y : E, ∃ n, y ∈ range (i n)) (hj : ∀ x : X, ∃ n, x ∈ range (j n))
    (hseminorm : ∀ p : Seminorm ℂ E,
      (∀ n, Continuous (p.comp (i n).toLinearMap)) → Continuous p)
    (q : X →L[ℂ] E) (hq : Surjective q) :
    IsOpenMap q ∧ ∃ e : (X ⧸ q.ker) ≃L[ℂ] E, e.toContinuousLinearMap.comp q.ker.mkQL = q := by
  let K := q.ker
  let r : X →L[ℂ] X ⧸ K := K.mkQL
  let e : (X ⧸ K) ≃ₗ[ℂ] E := q.toLinearMap.quotKerEquivOfSurjective hq
  have he (x : X) : e (r x) = q x := q.toLinearMap.quotKerEquivOfSurjective_apply_mk hq x
  have heinv (x : X) : e.symm (q x) = r x :=
    q.toLinearMap.quotKerEquivOfSurjective_symm_apply hq x
  have hecont : Continuous e := by
    apply K.isOpenQuotientMap_mkQL.continuous_comp_iff.mp
    have hid : (e : (X ⧸ K) → E) ∘ K.mkQL = q := funext he
    rw [hid]
    exact q.continuous
  have hinv : Continuous e.symm :=
    continuous_of_countable_stage_restrictions i hi hseminorm e.symm.toLinearMap fun n => by
      apply continuous_restriction_of_frechet_exhaustion (i n) (fun m => q.comp (j m))
      · intro y
        obtain ⟨x, rfl⟩ := hq y
        obtain ⟨m, z, rfl⟩ := hj x
        exact ⟨m, z, rfl⟩
      · intro m
        have hEq : (e.symm.toLinearMap.comp (q.comp (j m)).toLinearMap : B m → X ⧸ K) =
            r.comp (j m) := funext fun z => heinv (j m z)
        rw [hEq]
        exact (r.comp (j m)).continuous
  let eL : (X ⧸ K) ≃L[ℂ] E := ⟨e, hecont, hinv⟩
  have hcomp : eL.toContinuousLinearMap.comp r = q := ContinuousLinearMap.ext he
  refine ⟨?_, eL, hcomp⟩
  rw [← hcomp]
  exact eL.isOpenMap.comp K.isOpenMap_mkQ

end

end Masullo
