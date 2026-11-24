import StrictInductiveTensorLimits
import InductiveLimitDuals

open Function Set Topology UniformSpace
open scoped TensorProduct

namespace Masullo

noncomputable section

variable {T W : Type*} {P : T → Type*}
  [AddCommGroup W] [Module ℂ W] [TopologicalSpace W] [IsTopologicalAddGroup W]
  [PolynormableSpace ℂ W]
  [∀ i, AddCommGroup (P i)] [∀ i, Module ℂ (P i)] [∀ i, TopologicalSpace (P i)]
  [∀ i, IsTopologicalAddGroup (P i)]

/-- The continuous seminorm tests characterize the final locally convex topology. -/
theorem locallyConvexFinalTopology_eq_of_seminormTests
    (j : ∀ i, P i →L[ℂ] W)
    (h : ∀ p : Seminorm ℂ W, (∀ i, Continuous (p.comp (j i).toLinearMap)) → Continuous p) :
    (inferInstance : TopologicalSpace W) = locallyConvexFinalTopology (fun i => (j i).toLinearMap) := by
  let k (i : T) := (j i).toLinearMap
  let U : TopologicalSpace W := inferInstance
  change U = locallyConvexFinalTopology k
  apply le_antisymm <;> rw [← continuous_id_iff_le]
  · have hf := locallyConvexFinal_withSeminorms k
    exact (@WithSeminorms.continuous_iff_continuous_comp ℂ ℂ W W
      _ _ _ _ _ _ _ (RingHom.id ℂ) _ _ U inferInstance
      (locallyConvexFinalTopology k) hf LinearMap.id).mpr fun p => h p.val p.property
  · exact (locallyConvexFinal_continuous_iff k (LinearMap.id : W →ₗ[ℂ] W)).mpr
      fun i => (j i).continuous

variable {A R : Type*} {X : ℕ → Type*}
  [AddCommGroup A] [Module ℂ A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [PolynormableSpace ℂ A]
  [AddCommGroup R] [Module ℂ R] [TopologicalSpace R] [IsTopologicalAddGroup R]
  [PolynormableSpace ℂ R]
  [∀ n, AddCommGroup (X n)] [∀ n, Module ℂ (X n)] [∀ n, TopologicalSpace (X n)]
  [∀ n, IsTopologicalAddGroup (X n)]

/-- The completed inductive tensor of a countable strict limit with one
fixed factor is covered by the images of the completed stage tensors. -/
theorem completedInductiveTensor_exists_stage_of_strict_left
    (u : ∀ n, X n →L[ℂ] A) (t : ∀ n k, n ≤ k → X n →L[ℂ] X k)
    (hcompat : ∀ n k h, (u k).comp (t n k h) = u n)
    (hcover : ∀ x : A, ∃ n, x ∈ range (u n))
    (hfinal : (inferInstance : TopologicalSpace A) =
      locallyConvexFinalTopology (fun n => (u n).toLinearMap))
    (hemb : ∀ n, IsEmbedding (u n))
    (ht : ∀ n, inductiveTensorTopology (X n) R = injectiveTensorTopology (X n) R)
    (w : (inductiveTensorModuleStructure A R).Completed) :
    ∃ n, w ∈ range (completedInductiveTensor_map (u n) (ContinuousLinearMap.id ℂ R)) := by
  let v : Unit → R →L[ℂ] R := fun _ => ContinuousLinearMap.id ℂ R
  let s : ∀ i j : Unit, i ≤ j → R →L[ℂ] R := fun _ _ _ => ContinuousLinearMap.id ℂ R
  have hcompatV (i j : Unit) (h : i ≤ j) : (v j).comp (s i j h) = v i :=
    ContinuousLinearMap.ext fun _ => rfl
  have hfinalR := locallyConvexFinalTopology_eq_of_seminormTests v
    (fun p hp => hp ())
  let S := completedTensorStageSpan u v
  have hS : S = ⊤ := completedTensorStageSpan_eq_top_of_strict u v t s hcompat hcompatV
    hcover (fun r => ⟨(), r, rfl⟩) hfinal hfinalR hemb (fun _ => IsEmbedding.id) (fun n _ => ht n)
  let z : S := ⟨w, hS.symm ▸ Submodule.mem_top⟩
  obtain ⟨p, y, hy⟩ := completedTensorStageSpan_exhaust u v t s hcompat hcompatV z
  exact ⟨p.1, y, congrArg Subtype.val hy⟩

/-- Stagewise continuous seminorms are continuous on the full completed
inductive tensor of a countable strict limit with a fixed factor. -/
theorem completedInductiveTensor_stage_seminorm_continuous_of_strict_left
    (u : ∀ n, X n →L[ℂ] A) (t : ∀ n k, n ≤ k → X n →L[ℂ] X k)
    (hcompat : ∀ n k h, (u k).comp (t n k h) = u n)
    (hcover : ∀ x : A, ∃ n, x ∈ range (u n))
    (hfinal : (inferInstance : TopologicalSpace A) =
      locallyConvexFinalTopology (fun n => (u n).toLinearMap))
    (hemb : ∀ n, IsEmbedding (u n))
    (ht : ∀ n, inductiveTensorTopology (X n) R = injectiveTensorTopology (X n) R)
    (p : Seminorm ℂ (inductiveTensorModuleStructure A R).Completed)
    (hp : ∀ n, Continuous (p.comp
      (completedInductiveTensor_map (u n) (ContinuousLinearMap.id ℂ R)).toLinearMap)) :
    Continuous p := by
  let v : Unit → R →L[ℂ] R := fun _ => ContinuousLinearMap.id ℂ R
  let S := completedTensorStageSpan u v
  have hfinalR := locallyConvexFinalTopology_eq_of_seminormTests v (fun p hp => hp ())
  have hC : Continuous (p.comp S.subtype) :=
    completedTensorStageSpan_seminorm_continuous u v hcover (fun r => ⟨(), r, rfl⟩)
      hfinal hfinalR (p.comp S.subtype) (fun n j => hp n)
  have hs : ∀ w : (inductiveTensorModuleStructure A R).Completed, w ∈ S := by
    intro w
    obtain ⟨n, y, rfl⟩ :=
      completedInductiveTensor_exists_stage_of_strict_left u t hcompat hcover hfinal hemb ht w
    exact (completedTensorStageIntoSpan u v n () y).property
  let j (w : (inductiveTensorModuleStructure A R).Completed) : S := ⟨w, hs w⟩
  have hj : Continuous j := continuous_id.subtype_mk hs
  exact hC.comp hj

/-- A strict limit tensored with a fixed factor has its canonical completed stage presentation. -/
theorem exists_completedInductiveTensor_presentation_of_strict_left
    (u : ∀ n, X n →L[ℂ] A) (t : ∀ n k, n ≤ k → X n →L[ℂ] X k)
    (hcompat : ∀ n k h, (u k).comp (t n k h) = u n)
    (hcover : ∀ x : A, ∃ n, x ∈ range (u n))
    (hfinal : (inferInstance : TopologicalSpace A) =
      locallyConvexFinalTopology (fun n => (u n).toLinearMap))
    (hemb : ∀ n, IsEmbedding (u n))
    (ht : ∀ n, inductiveTensorTopology (X n) R = injectiveTensorTopology (X n) R) :
    let Z := (inductiveTensorModuleStructure A R).Completed
    let Y (n : ℕ) := (inductiveTensorModuleStructure (X n) R).Completed
    ∃ D : LinearInductivePresentation Z Y,
      (∀ n, D.incl n = completedInductiveTensor_map (u n) (ContinuousLinearMap.id ℂ R)) ∧
      (∀ n, IsEmbedding (D.incl n)) ∧
      (inferInstance : TopologicalSpace Z) =
        locallyConvexFinalTopology (fun n => (D.incl n).toLinearMap) := by
  let V := inductiveTensorModuleStructure A R
  let W (n : ℕ) := inductiveTensorModuleStructure (X n) R
  let Z := V.Completed
  let Y (n : ℕ) := (W n).Completed
  letI : UniformSpace (A ⊗[ℂ] R) := V.uniformSpace
  letI : IsUniformAddGroup (A ⊗[ℂ] R) := V.uniformGroup
  letI : UniformContinuousConstSMul ℂ (A ⊗[ℂ] R) := V.uniformConstSmul
  letI : PolynormableSpace ℂ (A ⊗[ℂ] R) := inductiveTensor_withSeminorms.toPolynormableSpace
  letI : IsUniformAddGroup Z := Completion.isUniformAddGroup
  letI : IsTopologicalAddGroup Z := inferInstanceAs (IsTopologicalAddGroup (Completion (A ⊗[ℂ] R)))
  letI : PolynormableSpace ℂ Z := polynormableSpace_completion
  letI : ∀ n, IsTopologicalAddGroup (Y n) := fun n => by
    letI : UniformSpace (X n ⊗[ℂ] R) := (W n).uniformSpace
    letI : IsUniformAddGroup (X n ⊗[ℂ] R) := (W n).uniformGroup
    letI : IsUniformAddGroup (Y n) := Completion.isUniformAddGroup
    exact inferInstanceAs (IsTopologicalAddGroup (Completion (X n ⊗[ℂ] R)))
  let idR := ContinuousLinearMap.id ℂ R
  let j (n : ℕ) : Y n →L[ℂ] Z := completedInductiveTensor_map (u n) idR
  have hj (n : ℕ) : IsEmbedding (j n) :=
    completedInductiveTensor_map_isEmbedding_of_equal (u n) idR (hemb n) IsEmbedding.id (ht n)
  have htZ : (inferInstance : TopologicalSpace Z) =
      locallyConvexFinalTopology (fun n => (j n).toLinearMap) :=
    locallyConvexFinalTopology_eq_of_seminormTests j
      (completedInductiveTensor_stage_seminorm_continuous_of_strict_left u t
        hcompat hcover hfinal hemb ht)
  let D : LinearInductivePresentation Z Y :=
    { incl := j
      transition := fun h => completedInductiveTensor_map (t _ _ h) idR
      injective_incl := fun n => (hj n).injective
      incl_transition := fun {n k} h z => by
        have hc : (j k).comp (completedInductiveTensor_map (t n k h) idR) = j n := by
          change (completedInductiveTensor_map (u k) idR).comp _ = _
          rw [completedInductiveTensor_map_comp, hcompat, ContinuousLinearMap.id_comp]
        exact DFunLike.congr_fun hc z
      exhaust := completedInductiveTensor_exists_stage_of_strict_left u t hcompat hcover hfinal hemb ht
      continuous_limit := fun l => by
        let f : Z → ℂ := l
        let P : Prop := ∀ n, Continuous (l.comp (j n).toLinearMap)
        have he := congrArg (fun t : TopologicalSpace Z =>
          @Continuous Z ℂ t inferInstance f ↔ P) htZ.symm
        exact he.mp (locallyConvexFinal_continuous_iff (fun n => (j n).toLinearMap) l) }
  exact ⟨D, fun _ => rfl, hj, htZ⟩

end
end Masullo
