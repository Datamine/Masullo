import SLocalBruhatProjections
import InductiveTensorAssociativity

open Function IsDedekindDomain NumberField Topology
open scoped BigOperators Classical NumberField RestrictedProduct SchwartzMap TensorProduct

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

private abbrev Place := HeightOneSpectrum (𝓞 F)
private abbrev Arch := 𝓢(mixedEmbedding.mixedSpace F, ℂ)
private abbrev FinAdeles := FiniteAdeleRing (𝓞 F) F
private abbrev FinTest : Type _ := locallyConstantTests (FinAdeles F)

private def finiteBruhatOfTest (ψ : FinTest F) : FiniteBruhat F :=
  ⟨⟨ψ.val, ψ.property.1⟩, ψ.property.2⟩

/-- The global elementary tensor map with the finite input expressed
as a locally constant, compactly supported test. -/
def globalBruhatPure : Arch F →ₗ[ℂ] FinTest F →ₗ[ℂ] GlobalBruhat F := by
  refine LinearMap.flip ?_
  refine { toFun := fun ψ => GlobalBruhat.pure F (finiteBruhatOfTest F ψ)
           map_add' := ?_, map_smul' := ?_ }
  · intro ψ ξ
    apply LinearMap.ext
    intro φ
    apply (GlobalBruhat.algebraicEquiv F).injective
    apply Subtype.ext
    funext a
    change φ _ * (ψ.val a.2 + ξ.val a.2) = φ _ * ψ.val a.2 + φ _ * ξ.val a.2
    exact mul_add ..
  · intro c ψ
    apply LinearMap.ext
    intro φ
    apply (GlobalBruhat.algebraicEquiv F).injective
    apply Subtype.ext
    funext a
    change φ _ * (c * ψ.val a.2) = c * (φ _ * ψ.val a.2)
    exact mul_left_comm ..

private theorem globalBruhatPure_lift_bijective :
    Bijective (TensorProduct.lift (globalBruhatPure F)) := by
  let A := Arch F
  let B := FinTest F
  let L := TensorProduct.lift (globalBruhatPure F)
  constructor
  · let a (x : InfiniteAdeleRing F) : A →ₗ[ℂ] ℂ :=
      { toFun := fun φ => φ (InfiniteAdeleRing.ringEquiv_mixedSpace F x)
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    let b (y : FinAdeles F) := (LinearMap.proj y).comp (locallyConstantTests (FinAdeles F)).subtype
    apply tensor_injective_of_separated_evaluations L a b
      (fun x y => GlobalBruhat.evaluation F (x, y))
    · intro φ hφ
      ext x
      obtain ⟨y, rfl⟩ := (InfiniteAdeleRing.ringEquiv_mixedSpace F).surjective x
      exact hφ y
    · intro ψ hψ
      exact Subtype.ext (funext hψ)
    · intro x y φ ψ
      change GlobalBruhat.evaluation F (x, y) (TensorProduct.lift (globalBruhatPure F) (φ ⊗ₜ[ℂ] ψ)) = _
      rw [TensorProduct.lift.tmul]
      rfl
  · intro f
    let E := GlobalBruhat.algebraicEquiv F
    have hp : ∀ (x : Adeles F → ℂ) (hx : x ∈ bruhatSubmodule F), E.symm ⟨x, hx⟩ ∈ L.range := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨φ, ψ, rfl⟩ := hx
        let g : B := ⟨ψ.toLocallyConstant, ψ.toLocallyConstant.isLocallyConstant, ψ.compactSupport⟩
        exact ⟨φ ⊗ₜ[ℂ] g, TensorProduct.lift.tmul (f' := globalBruhatPure F) φ g⟩
      | zero =>
        change E.symm 0 ∈ L.range
        rw [map_zero]
        exact L.range.zero_mem
      | add x y hx hy hx' hy' =>
        change E.symm ((⟨x, hx⟩ : bruhatSubmodule F) + ⟨y, hy⟩) ∈ _
        rw [map_add]
        exact L.range.add_mem hx' hy'
      | smul c x hx hx' =>
        change E.symm (c • (⟨x, hx⟩ : bruhatSubmodule F)) ∈ _
        rw [map_smul]
        exact L.range.smul_mem c hx'
    change f ∈ L.range
    simpa only [E.symm_apply_apply] using hp (E f).val (E f).property

/-- The global Schwartz–Bruhat topology is the inductive tensor topology
of the archimedean Schwartz and full finite test spaces. -/
def globalBruhatTensorEquiv :
    letI : TopologicalSpace (FinTest F) := finestLocallyConvexTopology (FinTest F)
    letI : TopologicalSpace (Arch F ⊗[ℂ] FinTest F) := inductiveTensorTopology (Arch F) (FinTest F)
    (Arch F ⊗[ℂ] FinTest F) ≃L[ℂ] GlobalBruhat F := by
  let A := Arch F
  let B := FinTest F
  letI : TopologicalSpace B := finestLocallyConvexTopology B
  letI : IsTopologicalAddGroup B := (finest_withSeminorms B).topologicalAddGroup
  letI : TopologicalSpace (A ⊗[ℂ] B) := inductiveTensorTopology A B
  let e := LinearEquiv.ofBijective _ (globalBruhatPure_lift_bijective F)
  refine ⟨e, ?_, ?_⟩
  · change Continuous (TensorProduct.lift (globalBruhatPure F))
    apply (continuous_inductiveTensor_lift_iff (globalBruhatPure F)).mpr
    exact ⟨fun ψ => GlobalBruhat.pure_continuous F (finiteBruhatOfTest F ψ),
      fun φ => finest_linear_continuous (globalBruhatPure F φ)⟩
  · change Continuous e.symm.toLinearMap
    apply GlobalBruhat.continuous_of_pure F (inductiveTensor_withSeminorms (E := A) (F := B))
    intro ψ
    let g : B := ⟨ψ.toLocallyConstant, ψ.toLocallyConstant.isLocallyConstant, ψ.compactSupport⟩
    have hg (φ : A) : e.symm (GlobalBruhat.pure F ψ φ) = φ ⊗ₜ[ℂ] g := by
      apply e.injective
      rw [e.apply_symm_apply]
      exact (TensorProduct.lift.tmul (f' := globalBruhatPure F) φ g).symm
    exact (continuous_inductiveTensor_tmul_left g).congr fun φ => (hg φ).symm

theorem globalBruhatTensorEquiv_tmul (φ : Arch F) (ψ : FinTest F) :
    (globalBruhatTensorEquiv F) (φ ⊗ₜ[ℂ] ψ) = globalBruhatPure F φ ψ :=
  TensorProduct.lift.tmul (f' := globalBruhatPure F) φ ψ

end
end Masullo
