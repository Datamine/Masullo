import QuotientDuals
import NuclearPermanence

open Function Set Topology
open scoped Classical

namespace Masullo

noncomputable section

universe u

variable {E F : Type u}
  [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
  [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]

/-- Nuclearity passes through linear topological embeddings. -/
theorem nuclearLocallyConvex_of_embedding (f : E →L[ℂ] F) (hf : IsEmbedding f)
    (hF : NuclearLocallyConvex.{u, u} F) : NuclearLocallyConvex.{u, u} E := by
  let e := LinearEquiv.ofInjective f.toLinearMap hf.injective
  have he : IsInducing e := IsInducing.subtypeVal.of_comp_iff.mp hf.isInducing
  let h := e.toEquiv.toHomeomorphOfIsInducing he
  let eL : E ≃L[ℂ] f.toLinearMap.range := ⟨e, h.continuous, h.symm.continuous⟩
  exact nuclearLocallyConvex_of_equiv eL.symm
    (nuclearLocallyConvex_submodule hF f.toLinearMap.range)

/-- Precomposition with a continuous linear equivalence embeds the strong dual
with its bounded-convergence topology. -/
theorem strongDual_precomp_isEmbedding (e : E ≃L[ℂ] F) :
    IsEmbedding (ContinuousLinearMap.precomp ℂ e.toContinuousLinearMap :
      StrongDual ℂ F →L[ℂ] StrongDual ℂ E) := by
  let a : StrongDual ℂ F →L[ℂ] StrongDual ℂ E :=
    ContinuousLinearMap.precomp ℂ e.toContinuousLinearMap
  let b : StrongDual ℂ E →L[ℂ] StrongDual ℂ F :=
    ContinuousLinearMap.precomp ℂ e.symm.toContinuousLinearMap
  have h : LeftInverse b a := by
    intro l
    ext x
    change l (e (e.symm x)) = l x
    rw [e.apply_symm_apply]
  exact h.isEmbedding b.continuous a.continuous

/-- Nuclearity of the strong dual is invariant under continuous linear equivalence. -/
theorem strongDual_nuclear_of_equiv (e : E ≃L[ℂ] F)
    (hE : NuclearLocallyConvex.{u, u} (StrongDual ℂ E)) :
    NuclearLocallyConvex.{u, u} (StrongDual ℂ F) :=
  nuclearLocallyConvex_of_embedding (ContinuousLinearMap.precomp ℂ e.toContinuousLinearMap)
    (strongDual_precomp_isEmbedding e) hE

/-- The strong dual of a finite product of spaces with nuclear strong duals
is nuclear. -/
theorem strongDual_nuclear_pi_finite {I : Type u} [Finite I] {X : I → Type u}
    [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)] [∀ i, TopologicalSpace (X i)]
    (hX : ∀ i, NuclearLocallyConvex.{u, u} (StrongDual ℂ (X i))) :
    NuclearLocallyConvex.{u, u} (StrongDual ℂ (∀ i, X i)) := by
  letI := Fintype.ofFinite I
  let a : StrongDual ℂ (∀ i, X i) →L[ℂ] (∀ i, StrongDual ℂ (X i)) :=
    ContinuousLinearMap.pi fun i ↦ ContinuousLinearMap.precomp ℂ (ContinuousLinearMap.single ℂ X i)
  let b : (∀ i, StrongDual ℂ (X i)) →L[ℂ] StrongDual ℂ (∀ i, X i) :=
    ∑ i, (ContinuousLinearMap.precomp ℂ (ContinuousLinearMap.proj i)).comp
      (ContinuousLinearMap.proj i)
  have h : LeftInverse b a := by
    intro l
    ext x
    simp only [b, sum_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]
    change (∑ i, l (ContinuousLinearMap.single ℂ X i (x i))) = l x
    rw [← map_sum]
    apply congrArg l
    funext i
    simp
  exact nuclearLocallyConvex_of_embedding a (h.isEmbedding b.continuous a.continuous)
    (nuclearLocallyConvex_pi hX)

/-- For a closed quotient of a nuclear Fréchet space, nuclearity of the
ambient strong dual passes to the strong dual of the quotient. -/
theorem strongDual_nuclear_of_closedQuotient (W : Submodule ℂ E) (hW : IsClosed (W : Set E))
    (hFr : IsFrechetTVS E) (hN : NuclearLocallyConvex.{u, u} E)
    (hD : NuclearLocallyConvex.{u, u} (StrongDual ℂ E)) :
    NuclearLocallyConvex.{u, u} (StrongDual ℂ (E ⧸ W)) :=
  nuclearLocallyConvex_of_embedding (ContinuousLinearMap.precomp ℂ W.mkQL)
    (quotientDual_strongEmbedding_of_nuclear W hW hN hFr) hD

end

end Masullo
