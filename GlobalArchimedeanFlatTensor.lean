import AdelicBruhatTensor
import AdelicFourierDerivative
import ArchimedeanFlatMellin
import InductiveTensorBasis

open Function IsDedekindDomain MeasureTheory Module NumberField Set Topology
open scoped Classical DirectSum NumberField SchwartzMap TensorProduct

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

private abbrev V := mixedEmbedding.mixedSpace F
private abbrev Arch := 𝓢(V F, ℂ)
private abbrev FinTest := locallyConstantTests (FiniteAdeleRing (𝓞 F) F)

private def archZeroEval : Arch F →L[ℂ] ℂ :=
  (BoundedContinuousFunction.evalCLM ℂ 0).comp
    (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (V F) ℂ)

/-- The flat archimedean factor in (7.4.3.1). On the trivial angular
component impose both polar moments, using additive Haar measure. -/
def archimedeanFlatPolarSubspace (trivial : Prop) : Submodule ℂ (Arch F) :=
  archimedeanFlatTestSubspace F ⊓
    if trivial then (archZeroEval F).ker ⊓ (SchwartzMap.integralCLM ℂ (volume : Measure (V F))).ker
    else ⊤

theorem archimedeanFlatPolarSubspace_isClosed (trivial : Prop) :
    IsClosed (archimedeanFlatPolarSubspace F trivial : Set (Arch F)) := by
  unfold archimedeanFlatPolarSubspace
  by_cases h : trivial
  · rw [ite_eq_left h, Submodule.coe_inf, Submodule.coe_inf]
    exact (archimedeanFlatTestSubspace_isClosed F).inter
      ((archZeroEval F).isClosed_ker.inter (SchwartzMap.integralCLM ℂ (volume : Measure (V F))).isClosed_ker)
  · rw [ite_eq_right h, inf_top_eq]
    exact archimedeanFlatTestSubspace_isClosed F

private theorem directSumCoord_continuous {I E : Type*}
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [PolynormableSpace ℂ E]
    (i : I) :
    letI : TopologicalSpace (⨁ _ : I, E) := locallyConvexSumTopology (fun _ : I => E)
    Continuous (fun x : ⨁ _ : I, E => x i) := by
  letI : TopologicalSpace (⨁ _ : I, E) := locallyConvexSumTopology (fun _ : I => E)
  change Continuous (DirectSum.component ℂ I (fun _ => E) i)
  apply (locallyConvexFinal_continuous_iff (DirectSum.lof ℂ I (fun _ => E)) _).2
  intro j
  by_cases h : j = i
  · subst j
    exact continuous_id.congr fun x => (DirectSum.component.lof_self (M := fun _ : I => E) ℂ i x).symm
  · exact continuous_const.congr fun x => by
      simpa [h] using (DirectSum.component.of (M := fun _ : I => E) ℂ i j x).symm

/-- The corrected tensor topology in (7.4.3.1). Multiplication of flat
archimedean and finite tests gives a closed linear embedding with the
inductive tensor topology and the actual adelic target. -/
theorem globalBruhat_archimedeanFlatTensor_isClosedEmbedding
    (P : Submodule ℂ (Arch F)) (hP : IsClosed (P : Set (Arch F))) :
    letI : TopologicalSpace (FinTest F) := finestLocallyConvexTopology _
    letI : TopologicalSpace (P ⊗[ℂ] FinTest F) := inductiveTensorTopology _ _
    IsClosedEmbedding ((globalBruhatTensorEquiv F).toLinearMap.comp
      (TensorProduct.map P.subtype (LinearMap.id : FinTest F →ₗ[ℂ] FinTest F))) := by
  let A := Arch F
  let B := FinTest F
  letI : TopologicalSpace B := finestLocallyConvexTopology B
  letI : TopologicalSpace (P ⊗[ℂ] B) := inductiveTensorTopology P B
  letI : TopologicalSpace (A ⊗[ℂ] B) := inductiveTensorTopology A B
  letI : PolynormableSpace ℂ A := (schwartz_withSeminorms ℂ (V F) ℂ).toPolynormableSpace
  let b := Module.Free.chooseBasis ℂ B
  let I := Module.Free.ChooseBasisIndex ℂ B
  letI : TopologicalSpace (⨁ _ : I, A) := locallyConvexSumTopology (fun _ : I => A)
  letI : TopologicalSpace (⨁ _ : I, P) := locallyConvexSumTopology (fun _ : I => P)
  let e := globalBruhatTensorEquiv F
  let eA := inductiveTensorBasisEquiv (E := A) b
  let eP := inductiveTensorBasisEquiv (E := P) b
  let T := TensorProduct.map P.subtype (LinearMap.id : B →ₗ[ℂ] B)
  have hT : IsEmbedding T := inductiveTensor_submodule_isEmbedding b P
  refine ⟨e.toHomeomorph.isEmbedding.comp hT, ?_⟩
  have hcoord (z : P ⊗[ℂ] B) (i : I) : eA (T z) i = (eP z i : A) := by
    induction z using TensorProduct.induction_on with
    | zero => simp [map_zero]
    | tmul w v =>
      change inductiveTensorBasisEquiv b (TensorProduct.map P.subtype (LinearMap.id : B →ₗ[ℂ] B)
        (w ⊗ₜ[ℂ] v)) i = ((inductiveTensorBasisEquiv b (w ⊗ₜ[ℂ] v)) i : A)
      rw [TensorProduct.map_tmul, LinearMap.id_apply, inductiveTensorBasisEquiv_tmul_apply,
        inductiveTensorBasisEquiv_tmul_apply]
      rfl
    | add w z hw hz => simp only [map_add, DirectSum.add_apply, hw, hz, Submodule.coe_add]
  have hrange : range T = ⋂ i : I, {x | eA x i ∈ P} := by
    ext x
    rw [mem_iInter]
    constructor
    · rintro ⟨z, rfl⟩ i
      rw [Set.mem_ofPred_eq, hcoord]
      exact (eP z i).property
    · intro hx
      let y : ⨁ _ : I, P := DFinsupp.mk (eA x).support (fun j => ⟨eA x j.val, hx j.val⟩)
      refine ⟨eP.symm y, eA.injective (DFinsupp.ext fun i => ?_)⟩
      rw [hcoord, eP.apply_symm_apply]
      by_cases hi : i ∈ (eA x).support
      · rw [show y i = _ from DFinsupp.mk_of_mem hi]
      · rw [show y i = 0 from DFinsupp.mk_of_notMem hi, Submodule.coe_zero,
          DFinsupp.notMem_support_iff.mp hi]
  have hclosed : IsClosed (range T) := by
    rw [hrange]
    exact isClosed_iInter fun i =>
      hP.preimage ((directSumCoord_continuous (E := A) i).comp eA.continuous)
  change IsClosed (range (e ∘ T))
  rw [range_comp]
  exact e.toHomeomorph.isClosedMap _ hclosed

/-- In particular the archimedean factor with the character-dependent
moment conditions gives the closed test embedding used in §7.4.3. -/
theorem globalBruhat_archimedeanFlatPolarTensor_isClosedEmbedding (trivial : Prop) :
    let P := archimedeanFlatPolarSubspace F trivial
    letI : TopologicalSpace (FinTest F) := finestLocallyConvexTopology _
    letI : TopologicalSpace (P ⊗[ℂ] FinTest F) := inductiveTensorTopology _ _
    IsClosedEmbedding ((globalBruhatTensorEquiv F).toLinearMap.comp
      (TensorProduct.map P.subtype (LinearMap.id : FinTest F →ₗ[ℂ] FinTest F))) :=
  globalBruhat_archimedeanFlatTensor_isClosedEmbedding F _
    (archimedeanFlatPolarSubspace_isClosed F trivial)

/-- The embedding of the corrected tensor acts by pointwise multiplication
of the two test factors. -/
theorem globalBruhat_archimedeanFlatTensor_tmul
    (P : Submodule ℂ (Arch F)) (a : P) (b : FinTest F) (x : Adeles F) :
    (GlobalBruhat.algebraicEquiv F ((globalBruhatTensorEquiv F).toLinearMap.comp
      (TensorProduct.map P.subtype (LinearMap.id : FinTest F →ₗ[ℂ] FinTest F))
      (a ⊗ₜ[ℂ] b))).val x =
      a.val (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1) * b.val x.2 := by
  simp only [LinearMap.comp_apply, TensorProduct.map_tmul, Submodule.subtype_apply, LinearMap.id_apply]
  change (GlobalBruhat.algebraicEquiv F ((globalBruhatTensorEquiv F)
    (a.val ⊗ₜ[ℂ] b))).val x = _
  rw [globalBruhatTensorEquiv_tmul]
  rfl

/-- Under the trivial angular condition the image satisfies the two actual
adelic polar equations. -/
theorem globalBruhat_archimedeanFlatPolarTensor_mem_polarKernel
    (z : archimedeanFlatPolarSubspace F True ⊗[ℂ] FinTest F) :
    GlobalBruhat.polarEvaluation F ((globalBruhatTensorEquiv F).toLinearMap.comp
      (TensorProduct.map (archimedeanFlatPolarSubspace F True).subtype LinearMap.id) z) = 0 := by
  let P := archimedeanFlatPolarSubspace F True
  let T := (globalBruhatTensorEquiv F).toLinearMap.comp
    (TensorProduct.map P.subtype (LinearMap.id : FinTest F →ₗ[ℂ] FinTest F))
  let A := (GlobalBruhat.polarEvaluation F).toLinearMap.comp T
  change A z = 0
  induction z using TensorProduct.induction_on with
  | zero => exact A.map_zero
  | tmul a b =>
    have h : a.val ∈ archimedeanFlatTestSubspace F ⊓
        ((archZeroEval F).ker ⊓ (SchwartzMap.integralCLM ℂ (volume : Measure (V F))).ker) := by
      have ha : a.val ∈ archimedeanFlatPolarSubspace F True := a.property
      simpa only [archimedeanFlatPolarSubspace, ite_eq_left trivial] using ha
    have ha₀ : a.val 0 = 0 := h.2.1
    have ha₁ : (∫ x : V F, a.val x) = 0 := h.2.2
    let ψ : FiniteBruhat F := ⟨⟨b.val, b.property.1⟩, b.property.2⟩
    have hp : T (a ⊗ₜ[ℂ] b) = GlobalBruhat.pure F ψ a.val := by
      change (globalBruhatTensorEquiv F) (TensorProduct.map P.subtype LinearMap.id
        (a ⊗ₜ[ℂ] b)) = _
      rw [TensorProduct.map_tmul, LinearMap.id_apply, globalBruhatTensorEquiv_tmul]
      rfl
    change GlobalBruhat.polarEvaluation F (T (a ⊗ₜ[ℂ] b)) = 0
    rw [hp]
    apply Prod.ext
    · change a.val (InfiniteAdeleRing.ringEquiv_mixedSpace F 0) * b.val 0 = 0
      rw [map_zero, ha₀, zero_mul]
    · exact globalBruhatFourier_pure_zero_of_archIntegral_zero F ψ a.val ha₁
  | add a b ha hb => rw [map_add, ha, hb, add_zero]

end

end Masullo
