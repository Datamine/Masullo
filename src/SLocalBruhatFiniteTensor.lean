import LocallyConstantFiniteTensor
import SLocalBruhatProjections

open IsDedekindDomain NumberField
open scoped BigOperators Classical NumberField SchwartzMap TensorProduct

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

private abbrev Place := HeightOneSpectrum (𝓞 F)
private abbrev Arch := 𝓢(mixedEmbedding.mixedSpace F, ℂ)
private abbrev LocalTensor (S : Finset (Place F)) :=
  ⨂[ℂ] w : S, locallyConstantTests (w.val.adicCompletion F)
private abbrev FiniteTest (S : Finset (Place F)) : Type _ :=
  locallyConstantTests ((w : S) → w.val.adicCompletion F)

/-- Proposition 2.1.4.1(1). The canonical topological tensor isomorphism
with every finite place displayed as an individual factor. -/
theorem exists_sLocalBruhatFiniteTensorEquiv (S : Finset (Place F)) :
    letI : TopologicalSpace (LocalTensor F S) := finestLocallyConvexTopology (LocalTensor F S)
    letI : TopologicalSpace (Arch F ⊗[ℂ] LocalTensor F S) :=
      inductiveTensorTopology (Arch F) (LocalTensor F S)
    ∃ e : (Arch F ⊗[ℂ] LocalTensor F S) ≃L[ℂ] sLocalBruhatImage F S,
      ∀ (φ : Arch F) (g : (w : S) → locallyConstantTests (w.val.adicCompletion F)),
        e (φ ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, g w)) =
          sLocalBruhatPure F S φ (locallyConstantTestPiProduct g) := by
  let A := Arch F
  let B := LocalTensor F S
  let C := FiniteTest F S
  letI : TopologicalSpace B := finestLocallyConvexTopology B
  letI : TopologicalSpace C := finestLocallyConvexTopology C
  letI : IsTopologicalAddGroup B := (finest_withSeminorms B).topologicalAddGroup
  letI : IsTopologicalAddGroup C := (finest_withSeminorms C).topologicalAddGroup
  letI : PolynormableSpace ℂ B := (finest_withSeminorms B).toPolynormableSpace
  letI : PolynormableSpace ℂ C := (finest_withSeminorms C).toPolynormableSpace
  letI : TopologicalSpace (A ⊗[ℂ] B) := inductiveTensorTopology A B
  letI : TopologicalSpace (A ⊗[ℂ] C) := inductiveTensorTopology A C
  obtain ⟨e, he⟩ := exists_locallyConstantTestFiniteTensorEquiv
    (X := fun w : Place F ↦ w.adicCompletion F) S
  let eL : B ≃L[ℂ] C :=
    ⟨e, finest_linear_continuous (E := B) (F := C) e.toLinearMap,
      finest_linear_continuous (E := C) (F := B) e.symm.toLinearMap⟩
  let E := inductiveTensor_lTensorEquiv (A := A) (B := B) (C := C) eL
  refine ⟨E.trans (sLocalBruhatTensorEquiv F S), fun φ g ↦ ?_⟩
  change sLocalBruhatTensorEquiv F S (e.lTensor A (φ ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, g w))) = _
  rw [LinearEquiv.lTensor_tmul]
  have hp : e (⨂ₜ[ℂ] w, g w) = locallyConstantTestPiProduct g :=
    Subtype.ext (funext (he g))
  rw [hp]
  exact TensorProduct.lift.tmul (f' := sLocalBruhatPure F S) _ _

/-- Under the canonical isomorphisms the transition on elementary tensors
keeps the archimedean factor and pads the finite test by the integer indicators. -/
theorem sLocalBruhatFiniteTensor_transition {S T : Finset (Place F)} (hST : S ⊆ T)
    (φ : Arch F) (g : (w : S) → locallyConstantTests (w.val.adicCompletion F))
    (x : SAdeles F T) :
    sLocalBruhatRestriction F T
        (sLocalBruhatTransition F hST
          (sLocalBruhatPure F S φ (locallyConstantTestPiProduct g))).val x =
      φ (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1) *
        ((∏ w : S, (g w).val (x.2 ⟨w.val, hST w.property⟩)) *
          if ∀ w : T, w.val ∉ S → x.2 w ∈ w.val.adicCompletionIntegers F then 1 else 0) := by
  rw [sLocalBruhatTransition_pure, sLocalBruhatPure_restrict, sLocalFiniteExtend_apply,
    locallyConstantTestPiProduct_apply]

end
end Masullo
