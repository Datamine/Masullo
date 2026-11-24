import ProjectiveTensorQuotients
import StrictInductiveTensorStages
import TopologicalLinearLimits
import Mathlib.Topology.DenseEmbedding

open Filter Function Set Topology TopologicalSpace UniformSpace
open scoped TensorProduct Uniformity

namespace Masullo

noncomputable section

variable {X Y A B : Type*}
  [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
  [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]
  [AddCommGroup A] [Module ℂ A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [AddCommGroup B] [Module ℂ B] [TopologicalSpace B] [T1Space B]

/-- Extending an open linear map from a dense source preserves its kernel
up to taking the closure in the larger source. -/
theorem kernel_eq_closure_of_dense_open
    (i : X →L[ℂ] A) (j : Y →L[ℂ] B) (p : X →L[ℂ] Y) (q : A →L[ℂ] B)
    (hi : DenseRange i) (hj : IsInducing j) (hp : IsOpenMap p)
    (h : q.comp i = j.comp p) :
    (q.ker : Set A) = closure (i '' (p.ker : Set X)) := by
  have hpoint (x : X) : q (i x) = j (p x) := DFunLike.congr_fun h x
  apply subset_antisymm
  · intro a ha
    have hqa : q a = 0 := ha
    apply mem_closure_iff_nhds.mpr
    intro U hU
    let sub : A × A → A := fun z => z.1 - z.2
    have hsub : Continuous sub := continuous_fst.sub continuous_snd
    have hUV : sub ⁻¹' U ∈ 𝓝 (a, 0) := by
      apply hsub.continuousAt.preimage_mem_nhds
      simpa [sub] using hU
    obtain ⟨V, hV, W, hW, hsubmem⟩ := mem_nhds_prod_iff.mp hUV
    obtain ⟨W₀, hW₀W, hW₀, h0W₀⟩ := mem_nhds_iff.mp hW
    let Z : Set Y := p '' (i ⁻¹' W₀)
    have hZ : IsOpen Z := hp _ (hW₀.preimage i.continuous)
    have h0Z : 0 ∈ Z := ⟨0, by simpa only [mem_preimage, map_zero] using h0W₀, p.map_zero⟩
    obtain ⟨Z', hZ', hZZ'⟩ := isOpen_induced_iff.mp (hj.eq_induced ▸ hZ)
    have h0Z' : 0 ∈ Z' := by
      have hmem : 0 ∈ j ⁻¹' Z' := hZZ'.symm ▸ h0Z
      simpa only [mem_preimage, map_zero] using hmem
    have haZ' : a ∈ q ⁻¹' Z' := by simpa only [mem_preimage, hqa] using h0Z'
    have hN : V ∩ q ⁻¹' Z' ∈ 𝓝 a :=
      inter_mem hV ((hZ'.preimage q.continuous).mem_nhds haZ')
    obtain ⟨_, hx, ⟨x, rfl⟩⟩ := mem_closure_iff_nhds.mp (hi a) _ hN
    have hxZ : p x ∈ Z := by
      rw [← hZZ']
      show j (p x) ∈ Z'
      rw [← hpoint]
      exact hx.2
    obtain ⟨y, hy, hyx⟩ := hxZ
    refine ⟨i (x - y), ?_, x - y, ?_, rfl⟩
    · rw [map_sub]
      exact hsubmem (show (i x, i y) ∈ V ×ˢ W from ⟨hx.1, hW₀W hy⟩)
    · show p (x - y) = 0
      rw [map_sub, hyx, sub_self]
  · apply closure_minimal _ q.isClosed_ker
    rintro _ ⟨x, hx, rfl⟩
    change p x = 0 at hx
    change q (i x) = 0
    rw [hpoint, hx, map_zero]

variable {X₀ A₀ : Type*}
  [AddCommGroup X₀] [Module ℂ X₀] [TopologicalSpace X₀]
  [AddCommGroup A₀] [Module ℂ A₀] [TopologicalSpace A₀]

/-- Exactness persists after extension when the extended kernel map has closed range. -/
theorem exact_of_dense_open_of_closed_range
    (i₀ : X₀ →L[ℂ] A₀) (i : X →L[ℂ] A) (j : Y →L[ℂ] B)
    (v : X₀ →L[ℂ] X) (p : X →L[ℂ] Y) (V : A₀ →L[ℂ] A) (q : A →L[ℂ] B)
    (hi₀ : DenseRange i₀) (hi : DenseRange i) (hj : IsInducing j) (hp : IsOpenMap p)
    (h : q.comp i = j.comp p) (hV : V.comp i₀ = i.comp v)
    (hclosed : IsClosed (range V)) (hex : Function.Exact v p) :
    Function.Exact V q := by
  have hpoint (x : X₀) : V (i₀ x) = i (v x) := DFunLike.congr_fun hV x
  have hs : i '' (p.ker : Set X) = V '' range i₀ := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨z, rfl⟩ := (hex x).mp hx
      exact ⟨i₀ z, mem_range_self _, hpoint z⟩
    · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
      exact ⟨v z, (hex _).mpr (mem_range_self _), (hpoint z).symm⟩
  have hcl : closure (V '' range i₀) = range V := by
    apply subset_antisymm (closure_minimal (image_subset_range _ _) hclosed)
    rintro _ ⟨z, rfl⟩
    exact image_closure_subset_closure_image V.continuous (mem_image_of_mem V (hi₀ z))
  intro y
  change y ∈ (q.ker : Set A) ↔ y ∈ range V
  rw [kernel_eq_closure_of_dense_open i j p q hi hj hp h, hs, hcl]

namespace TopologicalModuleStructure

/-- The canonical map into the separated completion, as a continuous linear map. -/
def inclCLM {X : Type*} [AddCommGroup X] [Module ℂ X] (D : TopologicalModuleStructure X) :
    letI : TopologicalSpace X := D.topology
    X →L[ℂ] D.Completed := by
  letI : UniformSpace X := D.uniformSpace
  letI : IsUniformAddGroup X := D.uniformGroup
  letI : UniformContinuousConstSMul ℂ X := D.uniformConstSmul
  exact ⟨⟨⟨D.incl, Completion.coe_add⟩, Completion.coe_smul⟩, Completion.continuous_coe X⟩

end TopologicalModuleStructure

section Projective

variable {E₀ E₁ E₂ F : Type*}
  [AddCommGroup E₀] [Module ℂ E₀] [TopologicalSpace E₀] [PolynormableSpace ℂ E₀]
  [AddCommGroup E₁] [Module ℂ E₁] [TopologicalSpace E₁] [PolynormableSpace ℂ E₁]
  [AddCommGroup E₂] [Module ℂ E₂] [TopologicalSpace E₂] [PolynormableSpace ℂ E₂]
  [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] [PolynormableSpace ℂ F]

/-- The middle exactness of the completed projective tensor sequence in
(C.2.3.29), when the completed left map has closed range. -/
theorem completedProjectiveTensor_exact_of_closed_range
    (f : E₀ →L[ℂ] E₁) (g : E₁ →L[ℂ] E₂) (hfg : Function.Exact f g)
    (hg : IsQuotientMap g)
    (hclosed : IsClosed (range (completedProjectiveTensorMap f (ContinuousLinearMap.id ℂ F)))) :
    Function.Exact (completedProjectiveTensorMap f (ContinuousLinearMap.id ℂ F))
      (completedProjectiveTensorMap g (ContinuousLinearMap.id ℂ F)) := by
  let X₀ := E₀ ⊗[ℂ] F
  let X₁ := E₁ ⊗[ℂ] F
  let X₂ := E₂ ⊗[ℂ] F
  let D₀ := projectiveTensorModuleStructure E₀ F
  let D₁ := projectiveTensorModuleStructure E₁ F
  let D₂ := projectiveTensorModuleStructure E₂ F
  letI : UniformSpace X₀ := D₀.uniformSpace
  letI : UniformSpace X₁ := D₁.uniformSpace
  letI : UniformSpace X₂ := D₂.uniformSpace
  letI : IsUniformAddGroup X₀ := D₀.uniformGroup
  letI : IsUniformAddGroup X₁ := D₁.uniformGroup
  letI : IsUniformAddGroup X₂ := D₂.uniformGroup
  letI : UniformContinuousConstSMul ℂ X₀ := D₀.uniformConstSmul
  letI : UniformContinuousConstSMul ℂ X₁ := D₁.uniformConstSmul
  letI : UniformContinuousConstSMul ℂ X₂ := D₂.uniformConstSmul
  letI : IsUniformAddGroup D₁.Completed := Completion.isUniformAddGroup
  letI : IsTopologicalAddGroup D₁.Completed := inferInstanceAs (IsTopologicalAddGroup (Completion X₁))
  letI : T0Space D₂.Completed := Completion.t0Space X₂
  let idF := ContinuousLinearMap.id ℂ F
  let v : X₀ →L[ℂ] X₁ :=
    ⟨f.toLinearMap.rTensor F, projectiveTensor_map_continuous f idF⟩
  let p : X₁ →L[ℂ] X₂ :=
    ⟨g.toLinearMap.rTensor F, projectiveTensor_map_continuous g idF⟩
  have hv (x : X₀) :
      (completedProjectiveTensorMap f idF) (D₀.inclCLM x) = D₁.inclCLM (v x) :=
    v.completion_apply_coe x
  have hp (x : X₁) :
      (completedProjectiveTensorMap g idF) (D₁.inclCLM x) = D₂.inclCLM (p x) :=
    p.completion_apply_coe x
  exact exact_of_dense_open_of_closed_range D₀.inclCLM D₁.inclCLM D₂.inclCLM v p
    (completedProjectiveTensorMap f idF) (completedProjectiveTensorMap g idF)
    Completion.denseRange_coe Completion.denseRange_coe (Completion.isUniformInducing_coe X₂).isInducing
    (projectiveTensor_map_openQuotient g idF hg IsQuotientMap.id).isOpenMap
    (ContinuousLinearMap.ext hp) (ContinuousLinearMap.ext hv) hclosed
    (rTensor_exact F hfg hg.surjective)

/-- On nuclear Fréchet stages the closed embedding on injective tensors
gives the closed embedding in the projective sequence (C.2.3.29). -/
theorem completedProjectiveTensor_isClosedEmbedding_of_equal
    (f : E₀ →L[ℂ] E₁) (hf : IsEmbedding f)
    (h₀ : projectiveTensorTopology E₀ F = injectiveTensorTopology E₀ F)
    (h₁ : projectiveTensorTopology E₁ F = injectiveTensorTopology E₁ F) :
    IsClosedEmbedding (completedProjectiveTensorMap f (ContinuousLinearMap.id ℂ F)) := by
  let U := projectiveTensorModuleStructure E₀ F
  let V := projectiveTensorModuleStructure E₁ F
  let X := injectiveTensorStructure E₀ F
  let Y := injectiveTensorStructure E₁ F
  let t₀ : U.Completed ≃L[ℂ] X.Completed := TopologicalModuleStructure.completionEquiv h₀
  let t₁ : V.Completed ≃L[ℂ] Y.Completed := TopologicalModuleStructure.completionEquiv h₁
  let idF := ContinuousLinearMap.id ℂ F
  let P := completedProjectiveTensorMap f idF
  let Q := completedInjectiveTensorMap f idF
  letI : UniformSpace (E₀ ⊗[ℂ] F) := U.uniformSpace
  letI : UniformSpace (E₁ ⊗[ℂ] F) := V.uniformSpace
  letI : IsUniformAddGroup (E₀ ⊗[ℂ] F) := U.uniformGroup
  letI : IsUniformAddGroup (E₁ ⊗[ℂ] F) := V.uniformGroup
  letI : UniformContinuousConstSMul ℂ (E₀ ⊗[ℂ] F) := U.uniformConstSmul
  letI : UniformContinuousConstSMul ℂ (E₁ ⊗[ℂ] F) := V.uniformConstSmul
  letI : T0Space Y.Completed := @Completion.t0Space _ Y.uniformSpace
  let L : (E₀ ⊗[ℂ] F) →L[ℂ] (E₁ ⊗[ℂ] F) :=
    ⟨TensorProduct.map f.toLinearMap idF.toLinearMap, projectiveTensor_map_continuous f idF⟩
  have hP (z : E₀ ⊗[ℂ] F) : P (U.incl z) = V.incl (L z) := L.completion_apply_coe z
  have hcomm : t₁.toContinuousLinearMap.comp P = Q.comp t₀.toContinuousLinearMap := by
    apply U.continuousLinearMap_ext_on_tmul
    intro a r
    let z := a ⊗ₜ[ℂ] r
    change t₁ (P (U.incl z)) = Q (t₀ (U.incl z))
    rw [hP, TopologicalModuleStructure.completionEquiv_incl h₁,
      TopologicalModuleStructure.completionEquiv_incl h₀, completedInjectiveTensorMap_incl]
    rfl
  have hfun : (P : _ → _) = t₁.symm ∘ Q ∘ t₀ := by
    funext z
    exact (t₁.symm_apply_apply (P z)).symm.trans
      (congrArg t₁.symm (DFunLike.congr_fun hcomm z))
  rw [hfun]
  exact t₁.symm.toHomeomorph.isClosedEmbedding.comp
    ((completedInjectiveTensorMap_isClosedEmbedding f idF hf IsEmbedding.id).comp
      t₀.toHomeomorph.isClosedEmbedding)

/-- The completed projective stage sequence (C.2.3.29) is topologically exact. -/
theorem completedProjectiveTensor_stage_exact
    [FirstCountableTopology E₁] [FirstCountableTopology F]
    (f : E₀ →L[ℂ] E₁) (g : E₁ →L[ℂ] E₂) (hfg : Function.Exact f g)
    (hf : IsEmbedding f) (hg : IsQuotientMap g)
    (h₀ : projectiveTensorTopology E₀ F = injectiveTensorTopology E₀ F)
    (h₁ : projectiveTensorTopology E₁ F = injectiveTensorTopology E₁ F) :
    let j := completedProjectiveTensorMap f (ContinuousLinearMap.id ℂ F)
    let q := completedProjectiveTensorMap g (ContinuousLinearMap.id ℂ F)
    IsClosedEmbedding j ∧ Function.Exact j q ∧ IsOpenQuotientMap q := by
  let idF := ContinuousLinearMap.id ℂ F
  let q := completedProjectiveTensorMap g idF
  have hj := completedProjectiveTensor_isClosedEmbedding_of_equal f hf h₀ h₁
  have hs : Surjective q := completedProjectiveTensorMap_surjective g idF hg IsQuotientMap.id
  have hr : IsOpen (range q) := hs.range_eq.symm ▸ isOpen_univ
  have hqr := completedProjectiveTensorMap_isOpenQuotient_range g idF hg IsQuotientMap.id
  have ho : IsOpenMap q := hr.isOpenMap_subtype_val.comp hqr.isOpenMap
  exact ⟨hj, completedProjectiveTensor_exact_of_closed_range f g hfg hg hj.isClosed_range,
    ⟨hs, q.continuous, ho⟩⟩

end Projective

section Frechet

variable {E F : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
  [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]

/-- The completed projective tensor of two Fréchet spaces is Fréchet. -/
theorem isFrechetTVS_completedProjectiveTensor
    (hE : IsFrechetTVS E) (hF : IsFrechetTVS F) :
    IsFrechetTVS (projectiveTensorModuleStructure E F).Completed := by
  letI : PolynormableSpace ℂ E := hE.choose_spec.1
  letI : PolynormableSpace ℂ F := hF.choose_spec.1
  letI : MetrizableSpace E := hE.choose_spec.2.1
  letI : MetrizableSpace F := hF.choose_spec.2.1
  let X := E ⊗[ℂ] F
  let D := projectiveTensorModuleStructure E F
  let Y := D.Completed
  letI : UniformSpace X := D.uniformSpace
  letI : IsUniformAddGroup X := D.uniformGroup
  letI : UniformContinuousConstSMul ℂ X := D.uniformConstSmul
  letI : PolynormableSpace ℂ X := projectiveTensor_withSeminorms.toPolynormableSpace
  letI : IsUniformAddGroup Y := Completion.isUniformAddGroup
  letI : T0Space Y := Completion.t0Space X
  letI : IsTopologicalAddGroup Y := inferInstanceAs (IsTopologicalAddGroup (Completion X))
  letI : CompleteSpace Y := Completion.completeSpace X
  obtain ⟨U, hU, -⟩ := (𝓝 (0 : E)).exists_antitone_basis
  obtain ⟨V, hV, -⟩ := (𝓝 (0 : F)).exists_antitone_basis
  have hX := elementaryTensorHull_basis hU hV
  have hC := hX.hasBasis_of_isDenseInducing (Completion.isDenseInducing_coe (α := X))
  letI : (𝓝 (0 : Y)).IsCountablyGenerated :=
    (show (𝓝 ((0 : X) : Completion X)).IsCountablyGenerated from hC.isCountablyGenerated)
  letI : (𝓤 Y).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  refine ⟨inferInstance, polynormableSpace_completion, UniformSpace.metrizableSpace, ?_⟩
  rw [IsUniformAddGroup.rightUniformSpace_eq]
  infer_instance

end Frechet

section Comparison

variable {A B R : Type*}
  [AddCommGroup A] [Module ℂ A] [TopologicalSpace A] [IsTopologicalAddGroup A] [PolynormableSpace ℂ A]
  [AddCommGroup B] [Module ℂ B] [TopologicalSpace B] [IsTopologicalAddGroup B] [PolynormableSpace ℂ B]
  [AddCommGroup R] [Module ℂ R] [TopologicalSpace R] [IsTopologicalAddGroup R] [PolynormableSpace ℂ R]

/-- The change from inductive to projective topology is natural for the
canonical completed tensor maps when the algebraic topologies agree. -/
theorem completedInductiveTensor_projective_natural
    (f : A →L[ℂ] B)
    (hA : inductiveTensorTopology A R = projectiveTensorTopology A R)
    (hB : inductiveTensorTopology B R = projectiveTensorTopology B R) :
    let eA : (inductiveTensorModuleStructure A R).Completed
        ≃L[ℂ] (projectiveTensorModuleStructure A R).Completed :=
      TopologicalModuleStructure.completionEquiv hA
    let eB : (inductiveTensorModuleStructure B R).Completed
        ≃L[ℂ] (projectiveTensorModuleStructure B R).Completed :=
      TopologicalModuleStructure.completionEquiv hB
    eB.toContinuousLinearMap.comp (completedInductiveTensor_map f (ContinuousLinearMap.id ℂ R)) =
      (completedProjectiveTensorMap f (ContinuousLinearMap.id ℂ R)).comp eA.toContinuousLinearMap := by
  let U := inductiveTensorModuleStructure A R
  let V := inductiveTensorModuleStructure B R
  let P := projectiveTensorModuleStructure A R
  let Q := projectiveTensorModuleStructure B R
  let eA : U.Completed ≃L[ℂ] P.Completed := TopologicalModuleStructure.completionEquiv hA
  let eB : V.Completed ≃L[ℂ] Q.Completed := TopologicalModuleStructure.completionEquiv hB
  let idR := ContinuousLinearMap.id ℂ R
  letI : UniformSpace (A ⊗[ℂ] R) := P.uniformSpace
  letI : UniformSpace (B ⊗[ℂ] R) := Q.uniformSpace
  letI : IsUniformAddGroup (A ⊗[ℂ] R) := P.uniformGroup
  letI : IsUniformAddGroup (B ⊗[ℂ] R) := Q.uniformGroup
  letI : UniformContinuousConstSMul ℂ (A ⊗[ℂ] R) := P.uniformConstSmul
  letI : UniformContinuousConstSMul ℂ (B ⊗[ℂ] R) := Q.uniformConstSmul
  letI : T0Space Q.Completed := Completion.t0Space (B ⊗[ℂ] R)
  let L : (A ⊗[ℂ] R) →L[ℂ] (B ⊗[ℂ] R) :=
    ⟨TensorProduct.map f.toLinearMap idR.toLinearMap, projectiveTensor_map_continuous f idR⟩
  change eB.toContinuousLinearMap.comp (completedInductiveTensor_map f idR) =
    (completedProjectiveTensorMap f idR).comp eA.toContinuousLinearMap
  apply U.continuousLinearMap_ext_on_tmul
  intro a r
  change eB ((completedInductiveTensor_map f idR) (U.incl (a ⊗ₜ[ℂ] r))) =
    (completedProjectiveTensorMap f idR) (eA (U.incl (a ⊗ₜ[ℂ] r)))
  have ha : eA (U.incl (a ⊗ₜ[ℂ] r)) = P.incl (a ⊗ₜ[ℂ] r) :=
    TopologicalModuleStructure.completionEquiv_incl hA _
  have hb : eB (V.incl (f a ⊗ₜ[ℂ] r)) = Q.incl (f a ⊗ₜ[ℂ] r) :=
    TopologicalModuleStructure.completionEquiv_incl hB _
  rw [ha, completedInductiveTensor_map_tmul]
  change eB (V.incl (f a ⊗ₜ[ℂ] r)) =
    (completedProjectiveTensorMap f idR) (P.incl (a ⊗ₜ[ℂ] r))
  rw [hb]
  exact (L.completion_apply_coe (a ⊗ₜ[ℂ] r)).symm

end Comparison

end
end Masullo
