import AdelicBruhatTensor
import LocallyConstantProduct
import SLocalBruhatFrechet

open Function IsDedekindDomain NumberField Topology
open scoped Classical NumberField RestrictedProduct SchwartzMap TensorProduct

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

private abbrev Place := HeightOneSpectrum (𝓞 F)
private abbrev Arch := 𝓢(mixedEmbedding.mixedSpace F, ℂ)
private abbrev Coord (S : Finset (Place F)) := (w : S) → w.val.adicCompletion F
private abbrev Tail (S : Finset (Place F)) :=
  Πʳ w : {w : Place F // w ∉ S}, [w.val.adicCompletion F, w.val.adicCompletionIntegers F]

private def finiteProductTestEquiv {X Y Z : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] [T2Space X] [T2Space Y]
    (d : X × Y ≃ₜ Z) :
    let B : Type _ := locallyConstantTests X
    let C : Type _ := locallyConstantTests Y
    let D : Type _ := locallyConstantTests Z
    letI : TopologicalSpace B := finestLocallyConvexTopology B
    letI : TopologicalSpace C := finestLocallyConvexTopology C
    letI : TopologicalSpace D := finestLocallyConvexTopology D
    letI : TopologicalSpace (B ⊗[ℂ] C) := inductiveTensorTopology B C
    (B ⊗[ℂ] C) ≃L[ℂ] D := by
  let B : Type _ := locallyConstantTests X
  let C : Type _ := locallyConstantTests Y
  let E : Type _ := locallyConstantTests (X × Y)
  let D : Type _ := locallyConstantTests Z
  letI : TopologicalSpace B := finestLocallyConvexTopology B
  letI : TopologicalSpace C := finestLocallyConvexTopology C
  letI : TopologicalSpace (B ⊗[ℂ] C) := inductiveTensorTopology B C
  letI : TopologicalSpace E := finestLocallyConvexTopology E
  letI : TopologicalSpace D := finestLocallyConvexTopology D
  letI : PolynormableSpace ℂ E := (finest_withSeminorms E).toPolynormableSpace
  letI : PolynormableSpace ℂ D := (finest_withSeminorms D).toPolynormableSpace
  let e : E ≃L[ℂ] D := ⟨locallyConstantTestCongr d,
    finest_linear_continuous (locallyConstantTestCongr d).toLinearMap,
    finest_linear_continuous (locallyConstantTestCongr d).symm.toLinearMap⟩
  exact (locallyConstantTestProductContinuousEquiv (X := X) (Y := Y)).trans e

private theorem finiteProductTestEquiv_tmul {X Y Z : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] [T2Space X] [T2Space Y]
    (d : X × Y ≃ₜ Z) (f : locallyConstantTests X) (g : locallyConstantTests Y) (z : Z) :
    ((finiteProductTestEquiv d) (f ⊗ₜ[ℂ] g)).val z = f.val (d.symm z).1 * g.val (d.symm z).2 := by
  change (locallyConstantTestCongr d (locallyConstantTestProductEquiv (f ⊗ₜ[ℂ] g))).val z = _
  rw [locallyConstantTestCongr_apply, locallyConstantTestProductEquiv_tmul, locallyConstantTestProduct_apply]

/-- Assemble the tensor for newly adjoined finite test coordinates. -/
private def appendBruhatTensor (S : Finset (Place F)) {Y Z : Type*}
    [TopologicalSpace Y] [TopologicalSpace Z] [T2Space Y] (d : Coord F S × Y ≃ₜ Z) :
    let A := Arch F
    let W : Type _ := sLocalBruhatImage F S
    let C : Type _ := locallyConstantTests Y
    let D : Type _ := locallyConstantTests Z
    letI : TopologicalSpace C := finestLocallyConvexTopology C
    letI : TopologicalSpace D := finestLocallyConvexTopology D
    letI : TopologicalSpace (W ⊗[ℂ] C) := inductiveTensorTopology W C
    letI : TopologicalSpace (A ⊗[ℂ] D) := inductiveTensorTopology A D
    (W ⊗[ℂ] C) ≃L[ℂ] (A ⊗[ℂ] D) := by
  let A := Arch F
  let W : Type _ := sLocalBruhatImage F S
  let B : Type _ := locallyConstantTests (Coord F S)
  let C : Type _ := locallyConstantTests Y
  let D : Type _ := locallyConstantTests Z
  letI : TopologicalSpace B := finestLocallyConvexTopology B
  letI : TopologicalSpace C := finestLocallyConvexTopology C
  letI : TopologicalSpace D := finestLocallyConvexTopology D
  letI : IsTopologicalAddGroup B := (finest_withSeminorms B).topologicalAddGroup
  letI : IsTopologicalAddGroup C := (finest_withSeminorms C).topologicalAddGroup
  letI : IsTopologicalAddGroup D := (finest_withSeminorms D).topologicalAddGroup
  letI : TopologicalSpace (A ⊗[ℂ] B) := inductiveTensorTopology A B
  letI : TopologicalSpace (B ⊗[ℂ] C) := inductiveTensorTopology B C
  letI : TopologicalSpace (W ⊗[ℂ] C) := inductiveTensorTopology W C
  letI : TopologicalSpace ((A ⊗[ℂ] B) ⊗[ℂ] C) := inductiveTensorTopology (A ⊗[ℂ] B) C
  letI : TopologicalSpace (A ⊗[ℂ] (B ⊗[ℂ] C)) := inductiveTensorTopology A (B ⊗[ℂ] C)
  letI : TopologicalSpace (A ⊗[ℂ] D) := inductiveTensorTopology A D
  letI : IsTopologicalAddGroup (A ⊗[ℂ] B) := inductiveTensor_withSeminorms.topologicalAddGroup
  letI : IsTopologicalAddGroup (B ⊗[ℂ] C) := inductiveTensor_withSeminorms.topologicalAddGroup
  let a := inductiveTensor_rTensorEquiv (C := C) (sLocalBruhatTensorEquiv F S).symm
  let b := inductiveTensor_assoc (A := A) (B := B) (C := C)
  let c := inductiveTensor_lTensorEquiv (A := A) (B := B ⊗[ℂ] C) (C := D) (finiteProductTestEquiv d)
  exact a.trans (b.trans c)

private theorem appendBruhatTensor_tmul (S : Finset (Place F)) {Y Z : Type*}
    [TopologicalSpace Y] [TopologicalSpace Z] [T2Space Y] (d : Coord F S × Y ≃ₜ Z)
    (φ : Arch F) (p : locallyConstantTests (Coord F S)) (g : locallyConstantTests Y) :
    appendBruhatTensor F S d ((sLocalBruhatTensorEquiv F S) (φ ⊗ₜ[ℂ] p) ⊗ₜ[ℂ] g) =
      φ ⊗ₜ[ℂ] (finiteProductTestEquiv d (p ⊗ₜ[ℂ] g)) := by
  let B : Type _ := locallyConstantTests (Coord F S)
  let C : Type _ := locallyConstantTests Y
  let D : Type _ := locallyConstantTests Z
  letI : TopologicalSpace B := finestLocallyConvexTopology B
  letI : TopologicalSpace C := finestLocallyConvexTopology C
  letI : TopologicalSpace D := finestLocallyConvexTopology D
  letI : TopologicalSpace (B ⊗[ℂ] C) := inductiveTensorTopology B C
  letI : TopologicalSpace (Arch F ⊗[ℂ] B) := inductiveTensorTopology (Arch F) B
  change (finiteProductTestEquiv d).toLinearEquiv.lTensor (Arch F)
    (TensorProduct.assoc ℂ _ _ _
      ((sLocalBruhatTensorEquiv F S).symm.toLinearEquiv.rTensor _
        ((sLocalBruhatTensorEquiv F S) (φ ⊗ₜ[ℂ] p) ⊗ₜ[ℂ] g))) = _
  rw [LinearEquiv.rTensor_tmul]
  change (finiteProductTestEquiv d).toLinearEquiv.lTensor (Arch F)
    (TensorProduct.assoc ℂ _ _ _
      ((sLocalBruhatTensorEquiv F S).symm (sLocalBruhatTensorEquiv F S (φ ⊗ₜ[ℂ] p)) ⊗ₜ[ℂ] g)) = _
  rw [ContinuousLinearEquiv.symm_apply_apply, TensorProduct.assoc_tmul, LinearEquiv.lTensor_tmul]
  rfl

private def finiteDifferenceSplit {S T : Finset (Place F)} (hST : S ⊆ T) :
    Coord F T ≃ₜ Coord F S × Coord F (T \ S) := by
  let e₁ : S ≃ {w : T // w.val ∈ S} :=
    { toFun := fun w => ⟨⟨w.val, hST w.property⟩, w.property⟩
      invFun := fun w => ⟨w.val.val, w.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let e₂ : (T \ S : Finset _) ≃ {w : T // w.val ∉ S} :=
    { toFun := fun w => ⟨⟨w.val, (Finset.mem_sdiff.mp w.property).1⟩, (Finset.mem_sdiff.mp w.property).2⟩
      invFun := fun w => ⟨w.val.val, Finset.mem_sdiff.mpr ⟨w.val.property, w.property⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact (Homeomorph.piEquivPiSubtypeProd (fun w : T => w.val ∈ S) _).trans
    ((Homeomorph.piCongrLeft (Y := fun w => w.val.val.adicCompletion F) e₁).symm.prodCongr
     (Homeomorph.piCongrLeft (Y := fun w => w.val.val.adicCompletion F) e₂).symm)

private theorem appendBruhatTensor_eval (S : Finset (Place F)) {Y Z : Type*}
    [TopologicalSpace Y] [TopologicalSpace Z] [T2Space Y] (d : Coord F S × Y ≃ₜ Z)
    (x : InfiniteAdeleRing F) (z : Z)
    (ev : Arch F ⊗[ℂ] locallyConstantTests Z →ₗ[ℂ] ℂ)
    (hev : ∀ (φ : Arch F) (p : locallyConstantTests Z),
      ev (φ ⊗ₜ[ℂ] p) = φ (InfiniteAdeleRing.ringEquiv_mixedSpace F x) * p.val z)
    (f : sLocalBruhatImage F S) (g : locallyConstantTests Y) :
    ev (appendBruhatTensor F S d (f ⊗ₜ[ℂ] g)) =
      sLocalBruhatRestriction F S f.val (x, (d.symm z).1) * g.val (d.symm z).2 := by
  let B : Type _ := locallyConstantTests (Coord F S)
  letI : TopologicalSpace B := finestLocallyConvexTopology B
  letI : TopologicalSpace (Arch F ⊗[ℂ] B) := inductiveTensorTopology (Arch F) B
  obtain ⟨u, rfl⟩ := (sLocalBruhatTensorEquiv F S).surjective f
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul φ p =>
    rw [appendBruhatTensor_tmul, hev, finiteProductTestEquiv_tmul, ← mul_assoc]
    have hp : sLocalBruhatTensorEquiv F S (φ ⊗ₜ[ℂ] p) = sLocalBruhatPure F S φ p :=
      TensorProduct.lift.tmul (f' := sLocalBruhatPure F S) φ p
    rw [hp, sLocalBruhatPure_restrict]
  | add u v hu hv =>
    simp only [map_add, TensorProduct.add_tmul] at *
    rw [hu, hv]
    change _ = ((sLocalBruhatRestriction F S _ (x, (d.symm z).1)) +
      (sLocalBruhatRestriction F S _ (x, (d.symm z).1))) * _
    rw [add_mul]

private theorem completeSpace_of_additiveHomeomorph {X Y : Type*}
    [AddCommGroup X] [Module ℂ X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y] [IsTopologicalAddGroup Y]
    (e : X ≃L[ℂ] Y)
    (hy : @CompleteSpace Y (IsTopologicalAddGroup.rightUniformSpace Y)) :
    @CompleteSpace X (IsTopologicalAddGroup.rightUniformSpace X) := by
  letI : UniformSpace X := IsTopologicalAddGroup.rightUniformSpace X
  letI : UniformSpace Y := IsTopologicalAddGroup.rightUniformSpace Y
  letI : IsUniformAddGroup X := isUniformAddGroup_of_addCommGroup
  letI : IsUniformAddGroup Y := isUniformAddGroup_of_addCommGroup
  have h : IsUniformInducing e.toLinearEquiv.toLinearMap.toAddMonoidHom :=
    AddMonoidHom.isUniformInducing_of_isInducing e.toHomeomorph.isInducing
  exact (h.completeSpace_congr e.surjective).mpr hy

/-- The full archimedean–finite inductive tensor is already complete. -/
theorem globalBruhatTensor_complete :
    let A := Arch F
    let B : Type _ := locallyConstantTests (FiniteAdeleRing (𝓞 F) F)
    letI : TopologicalSpace B := finestLocallyConvexTopology B
    letI : TopologicalSpace (A ⊗[ℂ] B) := inductiveTensorTopology A B
    letI : IsTopologicalAddGroup (A ⊗[ℂ] B) := inductiveTensor_withSeminorms.topologicalAddGroup
    @CompleteSpace (A ⊗[ℂ] B) (IsTopologicalAddGroup.rightUniformSpace _) := by
  let A := Arch F
  let B : Type _ := locallyConstantTests (FiniteAdeleRing (𝓞 F) F)
  letI : TopologicalSpace B := finestLocallyConvexTopology B
  letI : TopologicalSpace (A ⊗[ℂ] B) := inductiveTensorTopology A B
  letI : IsTopologicalAddGroup (A ⊗[ℂ] B) := inductiveTensor_withSeminorms.topologicalAddGroup
  exact completeSpace_of_additiveHomeomorph (globalBruhatTensorEquiv F) (globalBruhat_complete F)

/-- Corollary 2.1.4.2, global part. Multiplying S-local and restricted-tail
tests gives the global test space and the inductive tensor is complete. -/
theorem sLocalBruhatTailTensor (S : Finset (Place F)) :
    let W : Type _ := sLocalBruhatImage F S
    let H : Type _ := locallyConstantTests (Tail F S)
    letI : TopologicalSpace H := finestLocallyConvexTopology H
    letI : TopologicalSpace (W ⊗[ℂ] H) := inductiveTensorTopology W H
    letI : IsTopologicalAddGroup (W ⊗[ℂ] H) := inductiveTensor_withSeminorms.topologicalAddGroup
    (∃ e : (W ⊗[ℂ] H) ≃L[ℂ] GlobalBruhat F, ∀ (f : W) (g : H) (a : Adeles F),
      GlobalBruhat.evaluation F a (e (f ⊗ₜ[ℂ] g)) =
        sLocalBruhatRestriction F S f.val (sAdelesProjection F S a) *
          g.val ((finiteCoordinateSplit F S).symm a.2).2) ∧
      @CompleteSpace (W ⊗[ℂ] H) (IsTopologicalAddGroup.rightUniformSpace _) := by
  let A := Arch F
  let W : Type _ := sLocalBruhatImage F S
  let H : Type _ := locallyConstantTests (Tail F S)
  let D : Type _ := locallyConstantTests (FiniteAdeleRing (𝓞 F) F)
  letI : T2Space (Tail F S) := (finiteProducts_locallyConstantTests_context F S).2.1
  letI : TopologicalSpace H := finestLocallyConvexTopology H
  letI : TopologicalSpace D := finestLocallyConvexTopology D
  letI : TopologicalSpace (W ⊗[ℂ] H) := inductiveTensorTopology W H
  letI : TopologicalSpace (A ⊗[ℂ] D) := inductiveTensorTopology A D
  letI : IsTopologicalAddGroup (W ⊗[ℂ] H) := inductiveTensor_withSeminorms.topologicalAddGroup
  let d := (finiteCoordinateSplit F S).toHomeomorph
  let e := (appendBruhatTensor F S d).trans (globalBruhatTensorEquiv F)
  refine ⟨⟨e, fun f g a => ?_⟩, completeSpace_of_additiveHomeomorph e (globalBruhat_complete F)⟩
  let ev := (GlobalBruhat.evaluation F a).comp (globalBruhatTensorEquiv F).toLinearEquiv.toLinearMap
  have hev (φ : A) (p : D) : ev (φ ⊗ₜ[ℂ] p) =
      φ (InfiniteAdeleRing.ringEquiv_mixedSpace F a.1) * p.val a.2 := by
    change GlobalBruhat.evaluation F a (globalBruhatTensorEquiv F (φ ⊗ₜ[ℂ] p)) = _
    rw [globalBruhatTensorEquiv_tmul]
    rfl
  have hcoords : (a.1, (d.symm a.2).1) = sAdelesProjection F S a := by
    refine Prod.ext rfl (funext fun w => ?_)
    have h := congrArg (fun x : FiniteAdeleRing (𝓞 F) F => x w.val) (d.apply_symm_apply a.2)
    change finiteCoordinateSplit F S (d.symm a.2) w.val = a.2 w.val at h
    rwa [finiteCoordinateSplit_apply, dite_eq_left w.property] at h
  change ev (appendBruhatTensor F S d (f ⊗ₜ[ℂ] g)) =
    sLocalBruhatRestriction F S f.val (sAdelesProjection F S a) * g.val (d.symm a.2).2
  simpa only [hcoords] using appendBruhatTensor_eval F S d a.1 a.2 ev hev f g

/-- Corollary 2.1.4.2, finite enlargement. The new-place test factor
identifies the inductive tensor with the larger S-local space. -/
theorem sLocalBruhatDifferenceTensor {S T : Finset (Place F)} (hST : S ⊆ T) :
    let W : Type _ := sLocalBruhatImage F S
    let H : Type _ := locallyConstantTests (Coord F (T \ S))
    letI : TopologicalSpace H := finestLocallyConvexTopology H
    letI : TopologicalSpace (W ⊗[ℂ] H) := inductiveTensorTopology W H
    letI : IsTopologicalAddGroup (W ⊗[ℂ] H) := inductiveTensor_withSeminorms.topologicalAddGroup
    (∃ e : (W ⊗[ℂ] H) ≃L[ℂ] sLocalBruhatImage F T, ∀ (f : W) (g : H) (a : SAdeles F T),
      sLocalBruhatRestriction F T (e (f ⊗ₜ[ℂ] g)).val a =
        sLocalBruhatRestriction F S f.val (a.1, fun w : S => a.2 ⟨w.val, hST w.property⟩) *
          g.val (fun w : (T \ S : Finset _) => a.2 ⟨w.val, (Finset.mem_sdiff.mp w.property).1⟩)) ∧
      @CompleteSpace (W ⊗[ℂ] H) (IsTopologicalAddGroup.rightUniformSpace _) := by
  let A := Arch F
  let W : Type _ := sLocalBruhatImage F S
  let H : Type _ := locallyConstantTests (Coord F (T \ S))
  let D : Type _ := locallyConstantTests (Coord F T)
  letI : TopologicalSpace H := finestLocallyConvexTopology H
  letI : TopologicalSpace D := finestLocallyConvexTopology D
  letI : TopologicalSpace (W ⊗[ℂ] H) := inductiveTensorTopology W H
  letI : TopologicalSpace (A ⊗[ℂ] D) := inductiveTensorTopology A D
  letI : IsTopologicalAddGroup (W ⊗[ℂ] H) := inductiveTensor_withSeminorms.topologicalAddGroup
  let d := (finiteDifferenceSplit F hST).symm
  let e := (appendBruhatTensor F S d).trans (sLocalBruhatTensorEquiv F T)
  refine ⟨⟨e, fun f g a => ?_⟩, completeSpace_of_additiveHomeomorph e (sLocalBruhat_complete F T)⟩
  let r := (LinearMap.proj a).comp ((sLocalBruhatRestriction F T).comp (sLocalBruhatImage F T).subtype)
  let ev := r.comp (sLocalBruhatTensorEquiv F T).toLinearEquiv.toLinearMap
  have hev (φ : A) (p : D) : ev (φ ⊗ₜ[ℂ] p) =
      φ (InfiniteAdeleRing.ringEquiv_mixedSpace F a.1) * p.val a.2 := by
    have hp : sLocalBruhatTensorEquiv F T (φ ⊗ₜ[ℂ] p) = sLocalBruhatPure F T φ p :=
      TensorProduct.lift.tmul (f' := sLocalBruhatPure F T) φ p
    change sLocalBruhatRestriction F T (sLocalBruhatTensorEquiv F T (φ ⊗ₜ[ℂ] p)).val a = _
    rw [hp, sLocalBruhatPure_restrict]
  exact appendBruhatTensor_eval F S d a.1 a.2 ev hev f g

end
end Masullo
