import FinestLocallyConvex
import StrictInductiveBounds
import Mathlib.Topology.Algebra.Module.Complement
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.LocallyConvex.Barrelled
import Mathlib.Topology.Metrizable.Basic

open Bornology Filter Function Module Set Topology

namespace Masullo

noncomputable section

variable {E : Type*} [AddCommGroup E] [Module ℂ E]

theorem finest_submodule_family_final {J : Type*} (P : J → Submodule ℂ E) :
    letI : TopologicalSpace E := finestLocallyConvexTopology E
    locallyConvexFinalTopology (fun j => (P j).subtype) =
      finestLocallyConvexTopology E := by
  letI : TopologicalSpace E := finestLocallyConvexTopology E
  let W := finest_withSeminorms E
  letI : IsTopologicalAddGroup E := W.topologicalAddGroup
  letI : ContinuousSMul ℂ E := W.continuousSMul
  letI : T2Space E := finest_t2 E
  let f (j : J) : (P j) →ₗ[ℂ] E := (P j).subtype
  let T (j : J) : TopologicalSpace (P j) :=
    TopologicalSpace.induced ((P j).subtype : (P j) → E) (finestLocallyConvexTopology E)
  have hp (p : Seminorm ℂ E) (j : J) :
      Continuous[T j, inferInstance] (p.comp (f j)) := by
    letI : TopologicalSpace (P j) := T j
    exact (W.continuous_seminorm p).comp continuous_induced_dom
  let τ := @locallyConvexFinalTopology J E _ _ _ _ _ T f
  let S := @FinalSeminorm J E _ _ _ _ _ T f
  have H : @WithSeminorms ℂ E S _ _ _ (fun p => p.val) τ :=
    @locallyConvexFinal_withSeminorms J E _ _ _ _ _ T f
  have h₁ : Continuous[τ, finestLocallyConvexTopology E] (id : E → E) := by
    letI : TopologicalSpace E := τ
    exact (@WithSeminorms.continuous_iff_continuous_comp ℂ ℂ E E
      _ _ _ _ _ _ _ (RingHom.id ℂ) _ _ τ H.topologicalAddGroup
      (finestLocallyConvexTopology E) W LinearMap.id).mpr
        (fun p => H.continuous_seminorm ⟨p, hp p⟩)
  have h₂ : Continuous[finestLocallyConvexTopology E, τ] (id : E → E) := by
    letI : TopologicalSpace E := finestLocallyConvexTopology E
    exact (@WithSeminorms.continuous_iff_continuous_comp ℂ ℂ E E
      _ _ _ _ _ _ _ (RingHom.id ℂ) _ _ (finestLocallyConvexTopology E) W.topologicalAddGroup
      τ H LinearMap.id).mpr (fun p => W.continuous_seminorm p.val)
  exact le_antisymm (continuous_id_iff_le.mp h₁) (continuous_id_iff_le.mp h₂)

/-- The finite-dimensional subspaces with their Euclidean topologies
present the finest locally convex topology. -/
theorem finest_finiteDimensional_final :
    letI : TopologicalSpace E := finestLocallyConvexTopology E
    locallyConvexFinalTopology
      (fun P : {P : Submodule ℂ E // FiniteDimensional ℂ P} => P.val.subtype) =
        finestLocallyConvexTopology E :=
  finest_submodule_family_final Subtype.val

/-- Subspace and quotient topologies of the finest locally convex space are
finest. Every subspace has a continuous algebraic complement and is closed. -/
theorem finest_submodule_quotient (P : Submodule ℂ E) :
    letI : TopologicalSpace E := finestLocallyConvexTopology E
    (∃ Q : Submodule ℂ E, P.IsTopCompl Q) ∧ IsClosed (P : Set E) ∧
      (inferInstance : TopologicalSpace P) = finestLocallyConvexTopology P ∧
      (inferInstance : TopologicalSpace (E ⧸ P)) = finestLocallyConvexTopology (E ⧸ P) := by
  letI : TopologicalSpace E := finestLocallyConvexTopology E
  let W := finest_withSeminorms E
  letI : IsTopologicalAddGroup E := W.topologicalAddGroup
  letI : ContinuousSMul ℂ E := W.continuousSMul
  letI : T2Space E := finest_t2 E
  letI : PolynormableSpace ℂ E := W.toPolynormableSpace
  obtain ⟨Q, hQ⟩ := P.exists_isCompl
  have hTop : P.IsTopCompl Q := ⟨hQ, finest_linear_continuous (P.projection Q hQ)⟩
  have hClosed : IsClosed (P : Set E) := hTop.symm.isClosed'
  let p := P.projectionOnto Q hQ
  let τ := (inferInstance : TopologicalSpace P)
  let ν := finestLocallyConvexTopology P
  have h₁ : Continuous[τ, ν] (id : P → P) := by
    letI : TopologicalSpace P := ν
    letI : PolynormableSpace ℂ P := (finest_withSeminorms P).toPolynormableSpace
    have hp : Continuous[finestLocallyConvexTopology E, ν] p := finest_linear_continuous p
    have hv : Continuous[τ, finestLocallyConvexTopology E] (fun x : P => (x : E)) :=
      continuous_subtype_val
    have hc := @Continuous.comp P E P τ (finestLocallyConvexTopology E) ν _ _ hp hv
    exact (show (fun x : P => p x) = id from funext (Submodule.projectionOnto_apply_left hQ)) ▸ hc
  have h₂ : Continuous[ν, τ] (id : P → P) := by
    letI : TopologicalSpace P := τ
    letI : PolynormableSpace ℂ P := P.subtype.withSeminorms_induced W |>.toPolynormableSpace
    exact finest_linear_continuous (LinearMap.id : P →ₗ[ℂ] P)
  have he : τ = ν := le_antisymm (continuous_id_iff_le.mp h₁) (continuous_id_iff_le.mp h₂)
  let A := E ⧸ P
  let τq := (inferInstance : TopologicalSpace A)
  let νq := finestLocallyConvexTopology A
  have h₃ : Continuous[τq, νq] (id : A → A) := by
    have hq : @IsQuotientMap E A (finestLocallyConvexTopology E) τq P.mkQ :=
      P.isQuotientMap_mkQ
    letI : TopologicalSpace A := νq
    letI : PolynormableSpace ℂ A := (finest_withSeminorms A).toPolynormableSpace
    exact (@IsQuotientMap.continuous_iff E A A P.mkQ id (finestLocallyConvexTopology E) τq νq
      hq).mpr (finest_linear_continuous P.mkQ)
  have h₄ : Continuous[νq, τq] (id : A → A) := by
    letI : TopologicalSpace A := τq
    let e := Submodule.quotientEquivOfIsTopCompl P Q hTop
    have hh : Continuous[νq, inferInstance] e.toLinearEquiv.toLinearMap := by
      letI : PolynormableSpace ℂ Q := Q.subtype.withSeminorms_induced W |>.toPolynormableSpace
      exact finest_linear_continuous e.toLinearEquiv.toLinearMap
    have hc := @Continuous.comp A Q A νq inferInstance τq _ _ e.symm.continuous hh
    exact (show (fun x : A => e.symm (e x)) = id from funext e.symm_apply_apply) ▸ hc
  exact ⟨⟨Q, hTop⟩, hClosed, he,
    le_antisymm (continuous_id_iff_le.mp h₃) (continuous_id_iff_le.mp h₄)⟩

theorem finest_bounded_iff {B : Set E} :
    letI : TopologicalSpace E := finestLocallyConvexTopology E
    IsVonNBounded ℂ B ↔ ∃ (P : Submodule ℂ E), FiniteDimensional ℂ P ∧
      B ⊆ P ∧ IsVonNBounded ℂ ((↑) ⁻¹' B : Set P) := by
  letI : TopologicalSpace E := finestLocallyConvexTopology E
  let W := finest_withSeminorms E
  letI : IsTopologicalAddGroup E := W.topologicalAddGroup
  letI : ContinuousSMul ℂ E := W.continuousSMul
  let b := Basis.ofVectorSpace ℂ E
  let I := Basis.ofVectorSpaceIndex ℂ E
  letI : TopologicalSpace (I →₀ ℂ) := finestLocallyConvexTopology _
  letI : PolynormableSpace ℂ (I →₀ ℂ) := (finest_withSeminorms _).toPolynormableSpace
  constructor
  · intro hB
    let L : E →L[ℂ] (I →₀ ℂ) := ⟨b.repr.toLinearMap, finest_linear_continuous _⟩
    let S : Set I := {i | ∃ y ∈ L '' B, y i ≠ 0}
    have hS : S.Finite := finest_finsupp_bounded_support (hB.image L)
    let P := Submodule.span ℂ (b '' S)
    have hP : FiniteDimensional ℂ P := FiniteDimensional.span_of_finite ℂ (hS.image b)
    have hBP : B ⊆ P := by
      intro x hx
      apply b.mem_span_image.mpr
      intro i hi
      exact ⟨L x, mem_image_of_mem L hx, Finsupp.mem_support_iff.mp hi⟩
    exact ⟨P, hP, hBP, LinearInductivePresentation.bounded_preimage_of_embedding P.subtypeL IsEmbedding.subtypeVal hB⟩
  · rintro ⟨P, _, hBP, hP⟩
    refine (hP.image P.subtypeL).subset fun x hx => ?_
    exact ⟨⟨x, hBP hx⟩, hx, rfl⟩

theorem finest_isSeqClosed_iff {C : Set E} :
    letI : TopologicalSpace E := finestLocallyConvexTopology E
    IsSeqClosed C ↔ ∀ (P : Submodule ℂ E) [FiniteDimensional ℂ P],
      IsClosed ((↑) ⁻¹' C : Set P) := by
  letI : TopologicalSpace E := finestLocallyConvexTopology E
  let W := finest_withSeminorms E
  letI : IsTopologicalAddGroup E := W.topologicalAddGroup
  letI : ContinuousSMul ℂ E := W.continuousSMul
  letI : T2Space E := finest_t2 E
  constructor
  · intro h P hP
    let b := Module.finBasis ℂ P
    let e := b.equivFun.toContinuousLinearEquiv
    letI : SecondCountableTopology P := e.toHomeomorph.secondCountableTopology
    exact (h.preimage continuous_subtype_val.seqContinuous).isClosed
  · intro h u x hu hlim
    have hb := IsVonNBounded.insert x (hlim.isVonNBounded_range ℂ)
    obtain ⟨P, hP, hcover, _⟩ := finest_bounded_iff.mp hb
    letI : FiniteDimensional ℂ P := hP
    let u' (n : ℕ) : P := ⟨u n, hcover (mem_insert_of_mem _ (mem_range_self n))⟩
    let x' : P := ⟨x, hcover (mem_insert _ _)⟩
    have ht : Tendsto u' atTop (𝓝 x') := tendsto_subtype_rng.mpr hlim
    exact (h P).mem_of_tendsto ht (Eventually.of_forall hu)

theorem finest_barrelled :
    @BarrelledSpace ℂ E _ _ _ (finestLocallyConvexTopology E) := by
  letI : TopologicalSpace E := finestLocallyConvexTopology E
  exact ⟨fun p _ => (finest_withSeminorms E).continuous_seminorm p⟩

theorem finest_closed_bounded_isCompact {B : Set E} :
    letI : TopologicalSpace E := finestLocallyConvexTopology E
    IsClosed B → IsVonNBounded ℂ B → IsCompact B := by
  letI : TopologicalSpace E := finestLocallyConvexTopology E
  let W := finest_withSeminorms E
  letI : IsTopologicalAddGroup E := W.topologicalAddGroup
  letI : ContinuousSMul ℂ E := W.continuousSMul
  letI : T2Space E := finest_t2 E
  intro hc hb
  obtain ⟨P, hP, hsub, hbP⟩ := finest_bounded_iff.mp hb
  letI : FiniteDimensional ℂ P := hP
  let b := Module.finBasis ℂ P
  let e := b.equivFun.toContinuousLinearEquiv
  let C : Set P := (↑) ⁻¹' B
  have hcP : IsClosed C := hc.preimage continuous_subtype_val
  have hcompact : IsCompact (e '' C) :=
    Metric.isCompact_of_isClosed_isBounded (e.toHomeomorph.isClosedMap C hcP)
      ((NormedSpace.isVonNBounded_iff ℂ).mp (hbP.image e.toContinuousLinearMap))
  have he : (fun y => (e.symm y : E)) '' (e '' C) = B := by
    rw [Set.image_image]
    simp only [ContinuousLinearEquiv.symm_apply_apply]
    change (Subtype.val : P → E) '' ((Subtype.val : P → E) ⁻¹' B) = B
    rw [Set.image_preimage_eq_inter_range, Subtype.range_val]
    exact inter_eq_left.mpr hsub
  exact he ▸ hcompact.image (continuous_subtype_val.comp e.symm.continuous)

end
end Masullo
