import LocallyConstantProduct
import Mathlib.LinearAlgebra.PiTensorProduct.Generators

/-! The finite-set induction adapts the proof in
`RiemannMasullo/Ch02_AdelicTheta/Sec1.lean` at
`104e24a4a3294d99501b15893941fc4ad11eb575` (Apache-2.0). -/

open Function Set Topology
open scoped BigOperators Classical TensorProduct

namespace Masullo

noncomputable section

variable {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)]

private abbrev insertedIndex (S : Finset ι) (v : ι) : ↥(insert v S) :=
  ⟨v, Finset.mem_insert_self ..⟩

private def insertedComplement (S : Finset ι) (v : ι) (hv : v ∉ S) :
    ({insertedIndex S v}ᶜ : Set ↥(insert v S)) ≃ ↥S where
  toFun w := ⟨w.val.val, (Finset.mem_insert.mp w.val.property).resolve_left
    (fun h ↦ w.property (Subtype.ext h))⟩
  invFun w := ⟨⟨w.val, Finset.mem_insert_of_mem w.property⟩,
    fun h ↦ hv ((show w.val = v from congrArg Subtype.val h) ▸ w.property)⟩
  left_inv _ := rfl
  right_inv _ := rfl

private def splitInsert (S : Finset ι) (v : ι) (hv : v ∉ S) :
    (∀ w : ↥(insert v S), X w.val) ≃ₜ (∀ w : S, X w.val) × X v :=
  (Homeomorph.piSplitAt (insertedIndex S v) (fun w ↦ X w.val)).trans
    ((Homeomorph.prodComm ..).trans
      ((Homeomorph.piCongrLeft (Y := fun w ↦ X w.val.val)
        (insertedComplement S v hv).symm).symm.prodCongr (Homeomorph.refl _)))

private def splitTensor (S : Finset ι) (v : ι) (hv : v ∉ S) :
    (⨂[ℂ] w : ↥(insert v S), locallyConstantTests (X w.val)) ≃ₗ[ℂ]
      (⨂[ℂ] w : S, locallyConstantTests (X w.val)) ⊗[ℂ] locallyConstantTests (X v) :=
  (PiTensorProduct.equivPiTensorComplSingletonTensor ℂ
    (fun w : ↥(insert v S) ↦ locallyConstantTests (X w.val)) (insertedIndex S v)).trans
    ((PiTensorProduct.reindex ℂ (fun w ↦ locallyConstantTests (X w.val.val))
      (insertedComplement S v hv)).rTensor _)

private theorem splitTensor_tprod (S : Finset ι) (v : ι) (hv : v ∉ S)
    (g : (w : ↥(insert v S)) → locallyConstantTests (X w.val)) :
    splitTensor S v hv (⨂ₜ[ℂ] w, g w) =
      (⨂ₜ[ℂ] w : S, g ⟨w.val, Finset.mem_insert_of_mem w.property⟩) ⊗ₜ[ℂ]
        g (insertedIndex S v) := by
  let i := insertedIndex S v
  let e := PiTensorProduct.equivPiTensorComplSingletonTensor ℂ
    (fun w : ↥(insert v S) ↦ locallyConstantTests (X w.val)) i
  let r := PiTensorProduct.reindex ℂ (fun w ↦ locallyConstantTests (X w.val.val))
    (insertedComplement S v hv)
  change r.rTensor (locallyConstantTests (X v)) (e (⨂ₜ[ℂ] w, g w)) = _
  rw [PiTensorProduct.equivPiTensorComplSingletonTensor_tprod, LinearEquiv.rTensor_tmul,
    PiTensorProduct.reindex_tprod]
  rfl

private theorem prod_subtype_insert (S : Finset ι) (v : ι) (hv : v ∉ S)
    (g : ↥(insert v S) → ℂ) :
    (∏ w : S, g ⟨w.val, Finset.mem_insert_of_mem w.property⟩) * g (insertedIndex S v) =
      ∏ w, g w := by
  let f (w : ι) := if h : w ∈ insert v S then g ⟨w, h⟩ else 1
  have h₁ (w : S) : g ⟨w.val, Finset.mem_insert_of_mem w.property⟩ = f w.val :=
    by simp only [f, dite_eq_left (Finset.mem_insert_of_mem w.property)]
  have h₂ (w : ↥(insert v S)) : g w = f w.val :=
    by simp only [f, dite_eq_left w.property]
  rw [Finset.prod_congr rfl (fun w _ ↦ h₁ w), Finset.prod_congr rfl (fun w _ ↦ h₂ w),
    Finset.prod_coe_sort, Finset.prod_coe_sort, Finset.prod_insert hv, mul_comm]
  exact congrArg (· * ∏ w ∈ S, f w) (h₂ (insertedIndex S v))

private def constantTestEquiv (Y : Type*) [TopologicalSpace Y] [Unique Y] :
    ℂ ≃ₗ[ℂ] locallyConstantTests Y where
  toFun c := ⟨fun _ ↦ c, IsLocallyConstant.const c, by
    letI : CompactSpace Y := Finite.compactSpace
    exact HasCompactSupport.of_compactSpace _⟩
  invFun f := f.val default
  left_inv _ := rfl
  right_inv f := Subtype.ext (funext fun y ↦ congrArg f.val (Subsingleton.elim _ y))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable [∀ i, T2Space (X i)]

/-- The locally convex topology making the finite elementary tensor map
separately continuous is the finest topology when each factor is finest. -/
theorem finiteTensor_finalTopology_eq_finest {I : Type*} (M : I → Type*)
    [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)] :
    letI (i : I) : TopologicalSpace (M i) := finestLocallyConvexTopology (M i)
    locallyConvexFinalTopology
      (fun a : (∀ i, M i) × I ↦ (PiTensorProduct.tprod ℂ (s := M)).toLinearMap a.1 a.2) =
      finestLocallyConvexTopology (⨂[ℂ] i, M i) := by
  letI (i : I) : TopologicalSpace (M i) := finestLocallyConvexTopology (M i)
  letI (i : I) : IsTopologicalAddGroup (M i) := (finest_withSeminorms (M i)).topologicalAddGroup
  let T := ⨂[ℂ] i, M i
  let j (a : (∀ i, M i) × I) := (PiTensorProduct.tprod ℂ (s := M)).toLinearMap a.1 a.2
  change locallyConvexFinalTopology j = finestLocallyConvexTopology T
  apply le_antisymm
  · letI : TopologicalSpace T := finestLocallyConvexTopology T
    letI : PolynormableSpace ℂ T := (finest_withSeminorms T).toPolynormableSpace
    exact continuous_id_iff_le.mp <|
      (locallyConvexFinal_continuous_iff j (LinearMap.id : T →ₗ[ℂ] T)).mpr
        fun a ↦ finest_linear_continuous (j a)
  · letI : TopologicalSpace T := locallyConvexFinalTopology j
    letI : PolynormableSpace ℂ T := (locallyConvexFinal_withSeminorms j).toPolynormableSpace
    exact continuous_id_iff_le.mp (finest_linear_continuous (LinearMap.id : T →ₗ[ℂ] T))

/-- The algebraic finite tensor product of coordinate tests maps bijectively
to the compactly supported locally constant tests on the product. -/
theorem exists_locallyConstantTestFiniteTensorEquiv (S : Finset ι) :
    ∃ e : (⨂[ℂ] w : S, locallyConstantTests (X w.val)) ≃ₗ[ℂ]
        locallyConstantTests (∀ w : S, X w.val),
      ∀ (g : (w : S) → locallyConstantTests (X w.val)) (x : ∀ w : S, X w.val),
        (e (⨂ₜ[ℂ] w, g w)).val x = ∏ w, (g w).val (x w) := by
  induction S using Finset.induction_on with
  | empty =>
    let I := ↥(∅ : Finset ι)
    let r := PiTensorProduct.isEmptyEquiv (R := ℂ)
      (s := fun w : I ↦ locallyConstantTests (X w.val)) I
    refine ⟨r.trans (constantTestEquiv (∀ w : I, X w.val)), fun g x ↦ ?_⟩
    change r (⨂ₜ[ℂ] w, g w) = _
    rw [PiTensorProduct.isEmptyEquiv_apply_tprod, Finset.prod_of_isEmpty]
  | insert v S hv ih =>
    obtain ⟨e, he⟩ := ih
    refine ⟨(splitTensor S v hv).trans ((e.rTensor _).trans
      (locallyConstantTestProductEquiv.trans (locallyConstantTestCongr
        (splitInsert (X := X) S v hv).symm))), fun g x ↦ ?_⟩
    simp only [LinearEquiv.trans_apply, splitTensor_tprod, LinearEquiv.rTensor_tmul,
      locallyConstantTestProductEquiv_tmul, locallyConstantTestCongr_apply,
      Homeomorph.symm_symm, locallyConstantTestProduct_apply]
    change (e (⨂ₜ[ℂ] w : S, g ⟨w.val, Finset.mem_insert_of_mem w.property⟩)).val
      (fun w ↦ x ⟨w.val, Finset.mem_insert_of_mem w.property⟩) *
        (g (insertedIndex S v)).val (x (insertedIndex S v)) = _
    rw [he]
    exact prod_subtype_insert S v hv (fun w ↦ (g w).val (x w))

end
end Masullo
