import CompletedInductiveTensorPermanence
import TopologicalLinearLimits
import TensorDirectLimits
import InjectiveTensorMaps
import NuclearPermanence

open Filter Function Set Topology UniformSpace
open scoped DirectSum TensorProduct

namespace Masullo

noncomputable section

section CompletionMap

variable {A B R S : Type*}
  [AddCommGroup A] [Module ℂ A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [AddCommGroup B] [Module ℂ B] [TopologicalSpace B] [IsTopologicalAddGroup B]
  [AddCommGroup R] [Module ℂ R] [TopologicalSpace R] [IsTopologicalAddGroup R]
  [AddCommGroup S] [Module ℂ S] [TopologicalSpace S] [IsTopologicalAddGroup S]

theorem completedInductiveTensor_map_incl
    (j : A →L[ℂ] B) (k : R →L[ℂ] S) (z : A ⊗[ℂ] R) :
    completedInductiveTensor_map j k ((inductiveTensorModuleStructure A R).incl z) =
      (inductiveTensorModuleStructure B S).incl (TensorProduct.map j.toLinearMap k.toLinearMap z) := by
  let D := inductiveTensorModuleStructure A R
  let P := inductiveTensorModuleStructure B S
  letI : UniformSpace (A ⊗[ℂ] R) := D.uniformSpace
  letI : UniformSpace (B ⊗[ℂ] S) := P.uniformSpace
  letI : IsUniformAddGroup (A ⊗[ℂ] R) := D.uniformGroup
  letI : IsUniformAddGroup (B ⊗[ℂ] S) := P.uniformGroup
  change completedInductiveTensor_map j k (D.incl z) =
    P.incl (TensorProduct.map j.toLinearMap k.toLinearMap z)
  induction z using TensorProduct.induction_on with
  | zero =>
    rw [map_zero, show D.incl 0 = 0 from Completion.coe_zero,
      show P.incl 0 = 0 from Completion.coe_zero, map_zero]
  | tmul a r =>
    rw [TensorProduct.map_tmul]
    exact completedInductiveTensor_map_tmul j k a r
  | add z w hz hw =>
    rw [map_add, show D.incl (z + w) = D.incl z + D.incl w from Completion.coe_add z w,
      map_add, hz, hw]
    exact (Completion.coe_add _ _).symm


end CompletionMap

private theorem isQuotientMap_finalStageSum
    {K W : Type*} [DecidableEq K] {V : K → Type*}
    [AddCommGroup W] [Module ℂ W] [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    [∀ i, TopologicalSpace (V i)] [∀ i, IsTopologicalAddGroup (V i)]
    (stage : ∀ i, V i →ₗ[ℂ] W) (hs : Surjective (DirectSum.toModule ℂ K W stage)) :
    letI : TopologicalSpace (⨁ i, V i) := locallyConvexFinalTopology (DirectSum.lof ℂ K V)
    letI : TopologicalSpace W := locallyConvexFinalTopology stage
    IsQuotientMap (DirectSum.toModule ℂ K W stage) := by
  let lof := DirectSum.lof ℂ K V
  let D := ⨁ i, V i
  letI : TopologicalSpace D := locallyConvexFinalTopology lof
  letI : TopologicalSpace W := locallyConvexFinalTopology stage
  let H := locallyConvexFinal_withSeminorms lof
  letI : IsTopologicalAddGroup D := H.topologicalAddGroup
  letI : ContinuousSMul ℂ D := H.continuousSMul
  letI : PolynormableSpace ℂ D := H.toPolynormableSpace
  letI : PolynormableSpace ℂ W := (locallyConvexFinal_withSeminorms stage).toPolynormableSpace
  let q := DirectSum.toModule ℂ K W stage
  have hq (i : K) (x : V i) : q (lof i x) = stage i x := DirectSum.toModule_lof ℂ i x
  have hqc : Continuous q := (locallyConvexFinal_continuous_iff lof q).mpr fun i =>
    (locallyConvexFinal_stage_continuous stage i).congr fun x => (hq i x).symm
  let N := q.ker
  letI : PolynormableSpace ℂ (D ⧸ N) := polynormableSpace_complex_quotient N
  let e := q.quotKerEquivOfSurjective hs
  have he : Continuous e := N.isOpenQuotientMap_mkQ.isQuotientMap.continuous_iff.mpr hqc
  have hes : Continuous e.symm := by
    apply (locallyConvexFinal_continuous_iff stage e.symm.toLinearMap).mpr
    intro i
    refine (N.mkQL.continuous.comp (locallyConvexFinal_stage_continuous lof i)).congr fun x => ?_
    change N.mkQ (lof i x) = e.symm (stage i x)
    rw [← hq]
    exact (q.quotKerEquivOfSurjective_symm_apply hs (lof i x)).symm
  exact (Homeomorph.mk e.toEquiv he hes).isQuotientMap.comp N.isOpenQuotientMap_mkQ.isQuotientMap

section Stages

variable {I J E F : Type*} {A : I → Type*} {B : J → Type*}
  [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [∀ i, AddCommGroup (A i)] [∀ i, Module ℂ (A i)] [∀ i, TopologicalSpace (A i)]
  [∀ i, IsTopologicalAddGroup (A i)]
  [∀ j, AddCommGroup (B j)] [∀ j, Module ℂ (B j)] [∀ j, TopologicalSpace (B j)]
  [∀ j, IsTopologicalAddGroup (B j)]

omit [IsTopologicalAddGroup E] [IsTopologicalAddGroup F] in
/-- A seminorm on the inductive tensor is continuous if it is continuous on
every pair of algebraic stages of the covering final topologies. -/
theorem continuous_inductiveTensor_seminorm_of_stages
    (u : ∀ i, A i →L[ℂ] E) (v : ∀ j, B j →L[ℂ] F)
    (hu : ∀ x : E, ∃ i, x ∈ range (u i)) (hv : ∀ y : F, ∃ j, y ∈ range (v j))
    (hE : ‹TopologicalSpace E› = locallyConvexFinalTopology (fun i => (u i).toLinearMap))
    (hF : ‹TopologicalSpace F› = locallyConvexFinalTopology (fun j => (v j).toLinearMap))
    (p : Seminorm ℂ (E ⊗[ℂ] F))
    (hp : ∀ i j, Continuous[inductiveTensorTopology (A i) (B j), inferInstance]
      (p.comp (TensorProduct.map (u i).toLinearMap (v j).toLinearMap))) :
    Continuous[inductiveTensorTopology E F, inferInstance] p := by
  let t : InductiveTensorTest E F :=
    { tensor := p
      first := fun y => by
        obtain ⟨j, b, rfl⟩ := hv y
        change Continuous (p.comp ((TensorProduct.mk ℂ E F).flip (v j b)))
        rw [hE]
        apply locallyConvexFinal_seminorm_continuous
        intro i
        letI : TopologicalSpace (A i ⊗[ℂ] B j) := inductiveTensorTopology (A i) (B j)
        let L := (TensorProduct.mk ℂ (A i) (B j)).flip b
        have hc : Continuous L :=
          ((inductiveTensor_withSeminorms (E := A i) (F := B j)).continuous_iff_continuous_comp L).mpr
            fun q => q.first b
        convert (hp i j).comp hc using 1
        funext a
        change p (u i a ⊗ₜ[ℂ] v j b) =
          p (TensorProduct.map (u i).toLinearMap (v j).toLinearMap (a ⊗ₜ[ℂ] b))
        simp only [TensorProduct.map_tmul, ContinuousLinearMap.coe_coe]
      second := fun x => by
        obtain ⟨i, a, rfl⟩ := hu x
        change Continuous (p.comp (TensorProduct.mk ℂ E F (u i a)))
        rw [hF]
        apply locallyConvexFinal_seminorm_continuous
        intro j
        letI : TopologicalSpace (A i ⊗[ℂ] B j) := inductiveTensorTopology (A i) (B j)
        let L := TensorProduct.mk ℂ (A i) (B j) a
        have hc : Continuous L :=
          ((inductiveTensor_withSeminorms (E := A i) (F := B j)).continuous_iff_continuous_comp L).mpr
            fun q => q.second a
        convert (hp i j).comp hc using 1
        funext b
        change p (u i a ⊗ₜ[ℂ] v j b) =
          p (TensorProduct.map (u i).toLinearMap (v j).toLinearMap (a ⊗ₜ[ℂ] b))
        simp only [TensorProduct.map_tmul, ContinuousLinearMap.coe_coe] }
  letI : TopologicalSpace (E ⊗[ℂ] F) := inductiveTensorTopology E F
  exact inductiveTensor_withSeminorms.continuous_seminorm t

/-- The subspace spanned by the images of the completed tensor stages. -/
def completedTensorStageSpan (u : ∀ i, A i →L[ℂ] E) (v : ∀ j, B j →L[ℂ] F) :
    Submodule ℂ (inductiveTensorModuleStructure E F).Completed :=
  Submodule.span ℂ (⋃ i, ⋃ j, range (completedInductiveTensor_map (u i) (v j)))

/-- The completed stage map with its codomain restricted to the span. -/
def completedTensorStageIntoSpan (u : ∀ i, A i →L[ℂ] E) (v : ∀ j, B j →L[ℂ] F)
    (i : I) (j : J) :
    (inductiveTensorModuleStructure (A i) (B j)).Completed →L[ℂ] completedTensorStageSpan u v :=
  (completedInductiveTensor_map (u i) (v j)).codRestrict (completedTensorStageSpan u v)
    (fun z => Submodule.subset_span (mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨j, z, rfl⟩⟩))

private theorem continuous_linear_of_norm {V H : Type*}
    [AddCommGroup V] [Module ℂ V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [NormedAddCommGroup H] [NormedSpace ℂ H] (L : V →ₗ[ℂ] H)
    (h : Continuous (fun v => ‖L v‖)) : Continuous L := by
  refine continuous_of_tendsto_nhds_zero (G := V) (M := H) L.toAddMonoidHom ?_
  rw [Metric.tendsto_nhds]
  intro ε hε
  have ht := (h.tendsto' 0 0 (by simp)).eventually (Iio_mem_nhds hε)
  filter_upwards [ht] with x hx
  exact (by simpa only [dist_zero_right] using hx : dist (L x) 0 < ε)

/-- A stagewise continuous seminorm on the span of the actual completed
images is continuous for the subspace topology. -/
theorem completedTensorStageSpan_seminorm_continuous
    (u : ∀ i, A i →L[ℂ] E) (v : ∀ j, B j →L[ℂ] F)
    (hu : ∀ x : E, ∃ i, x ∈ range (u i)) (hv : ∀ y : F, ∃ j, y ∈ range (v j))
    (hE : ‹TopologicalSpace E› = locallyConvexFinalTopology (fun i => (u i).toLinearMap))
    (hF : ‹TopologicalSpace F› = locallyConvexFinalTopology (fun j => (v j).toLinearMap))
    (p : Seminorm ℂ (completedTensorStageSpan u v))
    (hp : ∀ i j, Continuous (p.comp (completedTensorStageIntoSpan u v i j).toLinearMap)) :
    Continuous p := by
  let X := E ⊗[ℂ] F
  let D := inductiveTensorModuleStructure E F
  letI : UniformSpace X := D.uniformSpace
  letI : IsUniformAddGroup X := D.uniformGroup
  letI : UniformContinuousConstSMul ℂ X := D.uniformConstSmul
  let S := completedTensorStageSpan u v
  let c (i : I) (j : J) := completedTensorStageIntoSpan u v i j
  let j₀ : X →ₗ[ℂ] D.Completed :=
    { toFun := D.incl
      map_add' := fun x y => Completion.coe_add x y
      map_smul' := fun a x => Completion.coe_smul a x }
  have hm (z : X) : j₀ z ∈ S := by
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero]
              exact S.zero_mem
    | tmul a b =>
      obtain ⟨i, x, rfl⟩ := hu a
      obtain ⟨j', y, rfl⟩ := hv b
      have hxy := (c i j' ((inductiveTensorModuleStructure (A i) (B j')).incl (x ⊗ₜ[ℂ] y))).property
      change D.incl (u i x ⊗ₜ[ℂ] v j' y) ∈ S
      exact (completedInductiveTensor_map_tmul (u i) (v j') x y) ▸ hxy
    | add a b ha hb => exact (map_add j₀ a b).symm ▸ S.add_mem ha hb
  let j := j₀.codRestrict S hm
  let q := p.comp j
  have hn (i : I) (j' : J) (w : A i ⊗[ℂ] B j') :
      j (TensorProduct.map (u i).toLinearMap (v j').toLinearMap w) =
      c i j' ((inductiveTensorModuleStructure (A i) (B j')).incl w) := by
    apply Subtype.ext
    exact (completedInductiveTensor_map_incl (u i) (v j') w).symm
  have hq : Continuous q := by
    apply continuous_inductiveTensor_seminorm_of_stages u v hu hv hE hF
    intro i j'
    let D' := inductiveTensorModuleStructure (A i) (B j')
    letI : UniformSpace (A i ⊗[ℂ] B j') := D'.uniformSpace
    have h₁ : Continuous D'.incl := Completion.continuous_coe _
    exact ((hp i j').comp h₁).congr fun z => congrArg p (hn i j' z).symm
  let f : X →L[ℂ] LocalBanach p := ⟨(localBanachDenseMap p).comp j,
    continuous_linear_of_norm _ (hq.congr fun x => (norm_localBanachDenseMap p (j x)).symm)⟩
  let ext := D.exists_continuousLinearMap_extend f
  let L := ext.choose
  have hL := ext.choose_spec
  have hStage (i : I) (j' : J) (w : (inductiveTensorModuleStructure (A i) (B j')).Completed) :
      localBanachDenseMap p (c i j' w) = L (completedInductiveTensor_map (u i) (v j') w) := by
    let D' := inductiveTensorModuleStructure (A i) (B j')
    letI : UniformSpace (A i ⊗[ℂ] B j') := D'.uniformSpace
    letI : IsUniformAddGroup (A i ⊗[ℂ] B j') := D'.uniformGroup
    letI : IsUniformAddGroup D'.Completed := Completion.isUniformAddGroup
    have hc : Continuous ((localBanachDenseMap p).comp (c i j').toLinearMap) :=
      continuous_linear_of_norm _ ((hp i j').congr
        fun w => (norm_localBanachDenseMap p (c i j' w)).symm)
    exact Completion.ext' hc (L.continuous.comp (completedInductiveTensor_map (u i) (v j')).continuous)
      (fun z => (congrArg (localBanachDenseMap p) (hn i j' z).symm).trans
        ((hL _).symm.trans (congrArg L (completedInductiveTensor_map_incl (u i) (v j') z).symm))) w
  let δ := localBanachDenseMap p - L.toLinearMap.comp S.subtype
  have hδ : S ≤ δ.ker.map S.subtype := by
    apply Submodule.span_le.mpr
    intro z hz
    obtain ⟨i, hi⟩ := mem_iUnion.mp hz
    obtain ⟨j', hj⟩ := mem_iUnion.mp hi
    obtain ⟨w, rfl⟩ := hj
    refine ⟨c i j' w, ?_, rfl⟩
    exact LinearMap.mem_ker.mpr (sub_eq_zero.mpr (hStage i j' w))
  have hpL (x : S) : p x = ‖L x.val‖ := by
    obtain ⟨y, hy, hyx⟩ := hδ x.property
    have hxy : y = x := Subtype.ext hyx
    have hd : δ x = 0 := LinearMap.mem_ker.mp (hxy ▸ hy)
    have he := sub_eq_zero.mp hd
    exact (norm_localBanachDenseMap p x).symm.trans (congrArg norm he)
  exact (L.continuous.comp continuous_subtype_val).norm.congr fun x => (hpL x).symm

/-- The completed-stage span carries precisely the final locally convex
topology of the completed stage maps, as a subspace of the full completion. -/
theorem completedTensorStageSpan_topology
    (u : ∀ i, A i →L[ℂ] E) (v : ∀ j, B j →L[ℂ] F)
    (hu : ∀ x : E, ∃ i, x ∈ range (u i)) (hv : ∀ y : F, ∃ j, y ∈ range (v j))
    (hE : ‹TopologicalSpace E› = locallyConvexFinalTopology (fun i => (u i).toLinearMap))
    (hF : ‹TopologicalSpace F› = locallyConvexFinalTopology (fun j => (v j).toLinearMap)) :
    (inferInstance : TopologicalSpace (completedTensorStageSpan u v)) =
      locallyConvexFinalTopology
        (fun ij : I × J => (completedTensorStageIntoSpan u v ij.1 ij.2).toLinearMap) := by
  let X := E ⊗[ℂ] F
  let D := inductiveTensorModuleStructure E F
  letI : UniformSpace X := D.uniformSpace
  letI : IsUniformAddGroup X := D.uniformGroup
  letI : UniformContinuousConstSMul ℂ X := D.uniformConstSmul
  letI : PolynormableSpace ℂ X := inductiveTensor_withSeminorms.toPolynormableSpace
  letI : IsUniformAddGroup D.Completed := Completion.isUniformAddGroup
  letI : PolynormableSpace ℂ D.Completed := polynormableSpace_completion
  let S := completedTensorStageSpan u v
  let k (ij : I × J) := (completedTensorStageIntoSpan u v ij.1 ij.2).toLinearMap
  letI : ∀ ij : I × J, IsTopologicalAddGroup
      (inductiveTensorModuleStructure (A ij.1) (B ij.2)).Completed := fun ij => by
    let U := inductiveTensorModuleStructure (A ij.1) (B ij.2)
    letI : UniformSpace (A ij.1 ⊗[ℂ] B ij.2) := U.uniformSpace
    letI : IsUniformAddGroup (A ij.1 ⊗[ℂ] B ij.2) := U.uniformGroup
    letI : IsUniformAddGroup U.Completed := Completion.isUniformAddGroup
    infer_instance
  let s : TopologicalSpace S := inferInstance
  change s = locallyConvexFinalTopology k
  apply le_antisymm <;> rw [← continuous_id_iff_le]
  · have h := locallyConvexFinal_withSeminorms k
    have hS : @IsTopologicalAddGroup S s _ := inferInstance
    exact (@WithSeminorms.continuous_iff_continuous_comp ℂ ℂ S S
      _ _ _ _ _ _ _ (RingHom.id ℂ) _ _ s hS (locallyConvexFinalTopology k) h LinearMap.id).mpr
      fun p => completedTensorStageSpan_seminorm_continuous u v hu hv hE hF p.val
        (fun i j => p.property (i,j))
  · exact (locallyConvexFinal_continuous_iff k (LinearMap.id : S →ₗ[ℂ] S)).mpr
      (fun ij => (completedTensorStageIntoSpan u v ij.1 ij.2).continuous)


/-- The algebraic pairwise-stage map is continuous for the inductive tensor topologies. -/
theorem continuous_inductiveTensorStageMap
    (u : ∀ i, A i →L[ℂ] E) (v : ∀ j, B j →L[ℂ] F) (i : I) (j : J) :
    Continuous[inductiveTensorTopology (A i) (B j), inductiveTensorTopology E F]
      (TensorProduct.map (u i).toLinearMap (v j).toLinearMap) := by
  let X := E ⊗[ℂ] F
  let Y := A i ⊗[ℂ] B j
  let D := inductiveTensorModuleStructure E F
  let C := inductiveTensorModuleStructure (A i) (B j)
  letI : UniformSpace X := D.uniformSpace
  letI : UniformSpace Y := C.uniformSpace
  apply (Completion.isUniformInducing_coe X).isInducing.continuous_iff.mpr
  exact ((completedInductiveTensor_map (u i) (v j)).continuous.comp
    (Completion.continuous_coe Y)).congr (completedInductiveTensor_map_incl (u i) (v j))

/-- The algebraic tensor of the factors with their final topologies has the
locally convex final topology of the pairwise tensor stages. -/
theorem inductiveTensor_topology_eq_final_of_stages
    (u : ∀ i, A i →L[ℂ] E) (v : ∀ j, B j →L[ℂ] F)
    (hu : ∀ x : E, ∃ i, x ∈ range (u i)) (hv : ∀ y : F, ∃ j, y ∈ range (v j))
    (hE : ‹TopologicalSpace E› = locallyConvexFinalTopology (fun i => (u i).toLinearMap))
    (hF : ‹TopologicalSpace F› = locallyConvexFinalTopology (fun j => (v j).toLinearMap)) :
    letI (ij : I × J) : TopologicalSpace (A ij.1 ⊗[ℂ] B ij.2) :=
      inductiveTensorTopology (A ij.1) (B ij.2)
    inductiveTensorTopology E F =
      locallyConvexFinalTopology (fun ij : I × J =>
        TensorProduct.map (u ij.1).toLinearMap (v ij.2).toLinearMap) := by
  let X := E ⊗[ℂ] F
  letI (ij : I × J) : TopologicalSpace (A ij.1 ⊗[ℂ] B ij.2) :=
    inductiveTensorTopology (A ij.1) (B ij.2)
  letI (ij : I × J) : IsTopologicalAddGroup (A ij.1 ⊗[ℂ] B ij.2) :=
    (inductiveTensor_withSeminorms (E := A ij.1) (F := B ij.2)).topologicalAddGroup
  letI : TopologicalSpace X := inductiveTensorTopology E F
  let W := inductiveTensor_withSeminorms (E := E) (F := F)
  letI : PolynormableSpace ℂ X := W.toPolynormableSpace
  let k (ij : I × J) := TensorProduct.map (u ij.1).toLinearMap (v ij.2).toLinearMap
  change (inductiveTensorTopology E F : TopologicalSpace X) = locallyConvexFinalTopology k
  apply le_antisymm <;> rw [← continuous_id_iff_le]
  · have h := locallyConvexFinal_withSeminorms k
    exact (@WithSeminorms.continuous_iff_continuous_comp ℂ ℂ X X
      _ _ _ _ _ _ _ (RingHom.id ℂ) _ _ (inductiveTensorTopology E F) W.topologicalAddGroup
      (locallyConvexFinalTopology k) h LinearMap.id).mpr
      (fun p => continuous_inductiveTensor_seminorm_of_stages u v hu hv hE hF p.val
        (fun i j => p.property (i, j)))
  · exact (locallyConvexFinal_continuous_iff k (LinearMap.id : X →ₗ[ℂ] X)).mpr
      fun ij => continuous_inductiveTensorStageMap u v ij.1 ij.2

set_option maxHeartbeats 1200000 in
/-- The completed stage sum maps onto the span with its subspace topology as
a topological quotient. -/
theorem completedTensorStageSpan_isQuotientMap [DecidableEq (I × J)]
    (u : ∀ i, A i →L[ℂ] E) (v : ∀ j, B j →L[ℂ] F)
    (hu : ∀ x : E, ∃ i, x ∈ range (u i)) (hv : ∀ y : F, ∃ j, y ∈ range (v j))
    (hE : ‹TopologicalSpace E› = locallyConvexFinalTopology (fun i => (u i).toLinearMap))
    (hF : ‹TopologicalSpace F› = locallyConvexFinalTopology (fun j => (v j).toLinearMap)) :
    let V (ij : I × J) := (inductiveTensorModuleStructure (A ij.1) (B ij.2)).Completed
    letI : TopologicalSpace (⨁ ij, V ij) := locallyConvexFinalTopology (DirectSum.lof ℂ (I × J) V)
    IsQuotientMap (DirectSum.toModule ℂ (I × J) (completedTensorStageSpan u v)
      (fun ij => (completedTensorStageIntoSpan u v ij.1 ij.2).toLinearMap)) := by
  let V (ij : I × J) := (inductiveTensorModuleStructure (A ij.1) (B ij.2)).Completed
  letI : ∀ ij : I × J, IsTopologicalAddGroup (V ij) := fun ij => by
    let U := inductiveTensorModuleStructure (A ij.1) (B ij.2)
    letI : UniformSpace (A ij.1 ⊗[ℂ] B ij.2) := U.uniformSpace
    letI : IsUniformAddGroup (A ij.1 ⊗[ℂ] B ij.2) := U.uniformGroup
    letI : IsUniformAddGroup U.Completed := Completion.isUniformAddGroup
    infer_instance
  let S := completedTensorStageSpan u v
  let k (ij : I × J) := (completedTensorStageIntoSpan u v ij.1 ij.2).toLinearMap
  let q := DirectSum.toModule ℂ (I × J) S k
  have hRange : S ≤ (S.subtype.comp q).range := by
    apply Submodule.span_le.mpr
    intro w hw
    obtain ⟨i, hi⟩ := mem_iUnion.mp hw
    obtain ⟨j, hj⟩ := mem_iUnion.mp hi
    obtain ⟨z, rfl⟩ := hj
    refine ⟨DirectSum.lof ℂ (I × J) V (i, j) z, ?_⟩
    change S.subtype (q (DirectSum.lof ℂ (I × J) V (i, j) z)) =
      completedInductiveTensor_map (u i) (v j) z
    have he : q (DirectSum.lof ℂ (I × J) V (i, j) z) = k (i, j) z :=
      DirectSum.toModule_lof ℂ (M := V) (φ := k) (i, j) z
    exact congrArg (fun x : S => (x : (inductiveTensorModuleStructure E F).Completed)) he
  have hqs : Surjective q := fun x =>
    let hx := hRange x.property
    ⟨hx.choose, Subtype.ext hx.choose_spec⟩
  change @IsQuotientMap (⨁ ij, V ij) S
    (locallyConvexFinalTopology (DirectSum.lof ℂ (I × J) V)) inferInstance q
  rw [completedTensorStageSpan_topology u v hu hv hE hF]
  exact isQuotientMap_finalStageSum k hqs

end Stages

section DirectedLimits

variable {I J : Type*} [Preorder I] [Preorder J] [DecidableEq I] [DecidableEq J]
  {A : I → Type*} {B : J → Type*}
  [∀ i, AddCommGroup (A i)] [∀ i, Module ℂ (A i)] [∀ i, TopologicalSpace (A i)]
  [∀ i, IsTopologicalAddGroup (A i)]
  [∀ j, AddCommGroup (B j)] [∀ j, Module ℂ (B j)] [∀ j, TopologicalSpace (B j)]
  [∀ j, IsTopologicalAddGroup (B j)]

variable (f : ∀ m n, m ≤ n → A m →ₗ[ℂ] A n) (g : ∀ m n, m ≤ n → B m →ₗ[ℂ] B n)
variable [DirectedSystem A (f · · ·)] [DirectedSystem B (g · · ·)]
variable [Nonempty I] [Nonempty J] [IsDirectedOrder I] [IsDirectedOrder J]

abbrev inductiveTensorStageLimitTopology : TopologicalSpace (TensorStageLimit f g) :=
  letI (p : I × J) : TopologicalSpace (TensorStage (A := A) (B := B) p) :=
    inductiveTensorTopology (A p.1) (B p.2)
  locallyConvexFinalTopology (tensorStageInclusion f g)

/-- The canonical algebraic tensor identification in (C.2.3.26) is a
continuous linear equivalence for the locally convex direct-limit topologies. -/
def inductiveTensorDirectLimitEquiv :
    letI : TopologicalSpace (Module.DirectLimit A f) :=
      locallyConvexFinalTopology (Module.DirectLimit.of ℂ I A f)
    letI : TopologicalSpace (Module.DirectLimit B g) :=
      locallyConvexFinalTopology (Module.DirectLimit.of ℂ J B g)
    letI : TopologicalSpace (TensorStageLimit f g) := inductiveTensorStageLimitTopology f g
    letI : TopologicalSpace (Module.DirectLimit A f ⊗[ℂ] Module.DirectLimit B g) :=
      inductiveTensorTopology (Module.DirectLimit A f) (Module.DirectLimit B g)
    TensorStageLimit f g ≃L[ℂ] (Module.DirectLimit A f ⊗[ℂ] Module.DirectLimit B g) := by
  let X := Module.DirectLimit A f
  let Y := Module.DirectLimit B g
  let a := Module.DirectLimit.of ℂ I A f
  let b := Module.DirectLimit.of ℂ J B g
  letI : TopologicalSpace X := locallyConvexFinalTopology a
  letI : TopologicalSpace Y := locallyConvexFinalTopology b
  letI : TopologicalSpace (TensorStageLimit f g) := inductiveTensorStageLimitTopology f g
  letI : TopologicalSpace (X ⊗[ℂ] Y) := inductiveTensorTopology X Y
  letI (p : I × J) : TopologicalSpace (TensorStage (A := A) (B := B) p) :=
    inductiveTensorTopology (A p.1) (B p.2)
  letI (p : I × J) : IsTopologicalAddGroup (TensorStage (A := A) (B := B) p) :=
    (inductiveTensor_withSeminorms (E := A p.1) (F := B p.2)).topologicalAddGroup
  letI : IsTopologicalAddGroup X := (locallyConvexFinal_withSeminorms a).topologicalAddGroup
  letI : IsTopologicalAddGroup Y := (locallyConvexFinal_withSeminorms b).topologicalAddGroup
  letI : PolynormableSpace ℂ (X ⊗[ℂ] Y) := inductiveTensor_withSeminorms.toPolynormableSpace
  letI : IsTopologicalAddGroup (X ⊗[ℂ] Y) := inductiveTensor_withSeminorms.topologicalAddGroup
  let u (i : I) : A i →L[ℂ] X := ⟨a i, locallyConvexFinal_stage_continuous a i⟩
  let v (j : J) : B j →L[ℂ] Y := ⟨b j, locallyConvexFinal_stage_continuous b j⟩
  let e := tensorDirectLimitEquiv f g
  have he (p : I × J) :
      e.toLinearMap.comp (tensorStageInclusion f g p) =
        TensorProduct.map (u p.1).toLinearMap (v p.2).toLinearMap :=
    LinearMap.ext (tensorDirectLimitEquiv_on_stage f g p)
  refine ⟨e, ?_, ?_⟩
  · apply (locallyConvexFinal_continuous_iff (tensorStageInclusion f g) e.toLinearMap).mpr
    intro p
    rw [he p]
    exact continuous_inductiveTensorStageMap u v p.1 p.2
  · apply ((locallyConvexFinal_withSeminorms (tensorStageInclusion f g)).continuous_iff_continuous_comp
      e.symm.toLinearMap).mpr
    intro Q
    have hX : ∀ x : X, ∃ i, x ∈ range (u i) := Module.DirectLimit.exists_of
    have hY : ∀ y : Y, ∃ j, y ∈ range (v j) := Module.DirectLimit.exists_of
    apply continuous_inductiveTensor_seminorm_of_stages u v hX hY rfl rfl
    intro i j
    have hinv (z : A i ⊗[ℂ] B j) :
        e.symm (TensorProduct.map (u i).toLinearMap (v j).toLinearMap z) =
          tensorStageInclusion f g (i, j) z := by
      have hz := tensorDirectLimitEquiv_on_stage f g (i, j) z
      change e (tensorStageInclusion f g (i, j) z) =
        TensorProduct.map (u i).toLinearMap (v j).toLinearMap z at hz
      rw [← hz]
      exact e.symm_apply_apply (tensorStageInclusion f g (i, j) z)
    exact (Q.property (i, j)).congr fun z => congrArg Q.val (hinv z).symm

@[simp] theorem inductiveTensorDirectLimitEquiv_on_stage (p : I × J)
    (z : TensorStage (A := A) (B := B) p) :
    inductiveTensorDirectLimitEquiv f g (tensorStageInclusion f g p z) =
      TensorProduct.map (Module.DirectLimit.of ℂ I A f p.1)
        (Module.DirectLimit.of ℂ J B g p.2) z :=
  tensorDirectLimitEquiv_on_stage f g p z

end DirectedLimits

end
end Masullo
