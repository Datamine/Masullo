import GlobalThetaStageRetraction

open Bornology Function IsDedekindDomain NumberField Set Topology UniformSpace
open scoped Classical NumberField SchwartzMap UniformConvergence UniformConvergenceCLM

namespace Masullo

noncomputable section

/-- If continuity of scalar linear forms is detected by continuous maps
from sequential spaces, the strong dual is complete. -/
theorem strongDual_complete_of_sequentialSlices
    {E I : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [ContinuousSMul ℂ E]
    {X : I → Type*} [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)]
    [∀ i, TopologicalSpace (X i)] [∀ i, IsTopologicalAddGroup (X i)]
    [∀ i, ContinuousSMul ℂ (X i)] [∀ i, SequentialSpace (X i)]
    (j : ∀ i, X i →L[ℂ] E)
    (hfinal : ∀ l : E →ₗ[ℂ] ℂ, (∀ i, Continuous (l.comp (j i).toLinearMap)) → Continuous l) :
    CompleteSpace (StrongDual ℂ E) := by
  let B := {s : Set E | IsVonNBounded ℂ s}
  let B' (i : I) := {s : Set (X i) | IsVonNBounded ℂ s}
  change CompleteSpace (E →SLᵤ[RingHom.id ℂ, B] ℂ)
  rw [completeSpace_iff_isComplete_range (UniformConvergenceCLM.isUniformInducing_coeFn _ _ B)]
  apply IsClosed.isComplete
  let p (i : I) (f : E →ᵤ[B] ℂ) : X i →ᵤ[B' i] ℂ :=
    UniformOnFun.ofFun (B' i) (UniformOnFun.toFun B f ∘ j i)
  have hp (i : I) : Continuous (p i) :=
    (UniformOnFun.precomp_uniformContinuous
      (f := j i) (𝔖 := B) (𝔗 := B' i)
      (fun _ hs ↦ (show IsVonNBounded ℂ _ from hs).image (j i))).continuous
  let C := (UniformOnFun.toFun B) ⁻¹' range ((↑) : (E →ₗ[ℂ] ℂ) → E → ℂ)
  let D (i : I) := (p i) ⁻¹' {f | Continuous (UniformOnFun.toFun (B' i) f)}
  have hC : IsClosed C := (LinearMap.isClosed_range_coe E ℂ (RingHom.id ℂ)).preimage
    (UniformOnFun.uniformContinuous_toFun (sUnion_isVonNBounded_eq_univ (𝕜 := ℂ))).continuous
  have hD (i : I) : IsClosed (D i) := by
    have hc : IsCoherentWith (B' i) :=
      IsCoherentWith.of_seq fun _ _ h ↦ (h.isVonNBounded_range ℂ).insert _
    exact (UniformOnFun.isClosed_setOfPred_continuous hc).preimage (hp i)
  suffices he : range (UniformOnFun.ofFun B ∘ DFunLike.coe :
      (E →SLᵤ[RingHom.id ℂ, B] ℂ) → (E →ᵤ[B] ℂ)) = C ∩ ⋂ i, D i by
    rw [he]
    exact hC.inter (isClosed_iInter hD)
  ext f
  constructor
  · rintro ⟨l, rfl⟩
    refine ⟨⟨l.toLinearMap, rfl⟩, mem_iInter.mpr ?_⟩
    intro i
    exact l.continuous.comp (j i).continuous
  · rintro ⟨⟨l, hl⟩, hd⟩
    have hf : Continuous l := hfinal l fun i ↦ by
      have hi := mem_iInter.mp hd i
      change Continuous (UniformOnFun.toFun B f ∘ j i) at hi
      rw [← hl] at hi
      exact hi
    exact ⟨⟨l, hf⟩, hl⟩

variable (F : Type*) [Field F] [NumberField F]

private abbrev Arch := 𝓢(mixedEmbedding.mixedSpace F, ℂ)
private abbrev Place := HeightOneSpectrum (𝓞 F)

/-- The strong dual of the actual global ordinary theta quotient is complete. -/
theorem globalThetaQuotient_strongDual_complete :
    CompleteSpace (StrongDual ℂ (GlobalThetaQuotient F)) := by
  let N := (globalThetaOperator F).ker
  let j (ψ : FiniteBruhat F) : Arch F →L[ℂ] GlobalThetaQuotient F :=
    N.mkQL.comp ⟨GlobalBruhat.pure F ψ, GlobalBruhat.pure_continuous F ψ⟩
  apply strongDual_complete_of_sequentialSlices j
  intro l hl
  apply N.isQuotientMap_mkQ.continuous_iff.mpr
  exact GlobalBruhat.continuous_of_pure F (norm_withSeminorms ℂ ℂ)
    (l.comp N.mkQ) hl

/-- The strong dual of each actual S-local ordinary theta quotient is complete. -/
theorem sLocalThetaQuotient_strongDual_complete (S : Finset (Place F)) :
    CompleteSpace (StrongDual ℂ (SLocalThetaQuotient F S)) := by
  let N := (sLocalThetaOperator F S).ker
  let j (ψ : locallyConstantTests ((v : S) → v.val.adicCompletion F)) :
      Arch F →L[ℂ] SLocalThetaQuotient F S :=
    N.mkQL.comp ⟨(sLocalBruhatPure F S).flip ψ,
      (GlobalBruhat.pure_continuous F _).subtype_mk _⟩
  apply strongDual_complete_of_sequentialSlices j
  intro l hl
  apply N.isQuotientMap_mkQ.continuous_iff.mpr
  exact continuous_sLocal_of_pure F S (norm_withSeminorms ℂ ℂ) (l.comp N.mkQ) hl

end

end Masullo
