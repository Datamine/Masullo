import NuclearPermanence
import InjectiveTensorAssociativity
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# The projective tensor product of nuclear spaces

The seminorm test for inverse projective reassociation adapts
`RiemannMasullo/AppC_LCTVS/Sec2b.lean`. The separation argument adapts
`RiemannMasullo/AppC_LCTVS/Sec2a_part2.lean`. Both refer to commit
cd84b23dd5e4f741037cf31aee06bc90161c6514 under Apache-2.0.
-/

open Function Set Topology
open scoped NNReal PointwiseConvergenceCLM TensorProduct

namespace Masullo

open InjectiveTensorTools

noncomputable section

variable {E F Z : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
    [AddCommGroup Z] [Module ℂ Z] [TopologicalSpace Z]

private theorem polynormable_separating {X : Type*} [AddCommGroup X] [Module ℂ X]
    [TopologicalSpace X] [PolynormableSpace ℂ X] [T1Space X] : SeparatingDual ℂ X := by
  let h := PolynormableSpace.withSeminorms ℂ X
  letI : IsTopologicalAddGroup X := h.topologicalAddGroup
  letI : ContinuousSMul ℂ X := h.continuousSMul
  constructor
  intro x hx
  obtain ⟨⟨p, hp⟩, hpx⟩ := h.separating_of_T1 x hx
  obtain ⟨φ, hφ, _⟩ := seminorm_support p hp x
  exact ⟨φ, fun e => hpx (by simpa only [e, norm_zero] using hφ.symm)⟩

private theorem dualPair_ext [SeparatingDual ℂ E] [SeparatingDual ℂ F]
    {z w : E ⊗[ℂ] F} (h : ∀ (φ : E →Lₚₜ[ℂ] ℂ) (ψ : F →Lₚₜ[ℂ] ℂ),
      dualPair φ ψ z = dualPair φ ψ w) : z = w := by
  classical
  let b := Module.Free.chooseBasis ℂ F
  let e := TensorProduct.equivFinsuppOfBasisRight (M := E) b
  let L (φ : StrongDual ℂ E) := (TensorProduct.lid ℂ F).toLinearMap.comp
    (TensorProduct.map φ.toLinearMap LinearMap.id)
  have hL (φ : StrongDual ℂ E) : L φ z = L φ w := by
    apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).mpr
    intro ψ
    have he : ψ.toLinearMap.comp (L φ) = dualPair φ ψ := by
      apply TensorProduct.ext'
      intro x y
      change ψ (L φ (x ⊗ₜ[ℂ] y)) = dualPair
        (show E →Lₚₜ[ℂ] ℂ from φ) (show F →Lₚₜ[ℂ] ℂ from ψ) (x ⊗ₜ[ℂ] y)
      rw [dualPair_tmul]
      simp [L]
      rfl
    exact (LinearMap.congr_fun he z).trans ((h φ ψ).trans (LinearMap.congr_fun he w).symm)
  apply e.injective
  ext i
  apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).mpr
  intro φ
  let coord : (E ⊗[ℂ] F) →ₗ[ℂ] E := (Finsupp.lapply i).comp e.toLinearMap
  have hc : φ.toLinearMap.comp coord = (b.coord i).comp (L φ) := by
    apply TensorProduct.ext'
    intro x y
    simp [coord, e, L, mul_comm]
  exact (LinearMap.congr_fun hc z).trans
    ((congrArg (b.coord i) (hL φ)).trans (LinearMap.congr_fun hc w).symm)

/-- On Hausdorff locally convex factors, the injective tensor tests separate
points of the algebraic tensor product. -/
theorem injectiveTensor_t2 [PolynormableSpace ℂ E] [PolynormableSpace ℂ F] [T2Space E] [T2Space F] :
    @T2Space (E ⊗[ℂ] F) (injectiveTensorTopology E F) := by
  letI : TopologicalSpace (E ⊗[ℂ] F) := injectiveTensorTopology E F
  letI : IsTopologicalAddGroup (E ⊗[ℂ] F) := injectiveTensor_withSeminorms.topologicalAddGroup
  letI : SeparatingDual ℂ E := polynormable_separating
  letI : SeparatingDual ℂ F := polynormable_separating
  letI : T1Space (E ⊗[ℂ] F) := injectiveTensor_withSeminorms.T1_of_separating (by
    intro z hz
    by_contra! h
    apply hz
    apply dualPair_ext
    intro φ ψ
    let p := (normSeminorm ℂ ℂ).comp φ.toLinearMap
    let q := (normSeminorm ℂ ℂ).comp ψ.toLinearMap
    let S := seminormPolarTest p φ.continuous.norm
    let T := seminormPolarTest q ψ.continuous.norm
    have hb := norm_dualPair_le S T z (show φ ∈ S.forms from fun _ => le_rfl)
      (show ψ ∈ T.forms from fun _ => le_rfl)
    rw [h (S, T)] at hb
    rw [map_zero]
    exact norm_le_zero_iff.mp hb)
  infer_instance

private theorem projectiveTensor_t2 [PolynormableSpace ℂ E] [PolynormableSpace ℂ F]
    [T2Space E] [T2Space F] : @T2Space (E ⊗[ℂ] F) (projectiveTensorTopology E F) :=
  @T2Space.of_injective_continuous _ _ (projectiveTensorTopology E F) (injectiveTensorTopology E F)
    injectiveTensor_t2 id injective_id projective_to_injective_continuous

set_option maxHeartbeats 800000 in
/-- The inverse associator is continuous for the iterated projective
topologies. -/
theorem projectiveTensor_assoc_symm_continuous [PolynormableSpace ℂ E]
    [PolynormableSpace ℂ F] [PolynormableSpace ℂ Z] :
    letI : TopologicalSpace (E ⊗[ℂ] F) := projectiveTensorTopology E F
    letI : TopologicalSpace (F ⊗[ℂ] Z) := projectiveTensorTopology F Z
    Continuous[projectiveTensorTopology E (F ⊗[ℂ] Z), projectiveTensorTopology (E ⊗[ℂ] F) Z]
      (TensorProduct.assoc ℂ E F Z).symm := by
  let R := E ⊗[ℂ] F
  let S := F ⊗[ℂ] Z
  letI : TopologicalSpace R := projectiveTensorTopology E F
  letI : TopologicalSpace S := projectiveTensorTopology F Z
  letI : TopologicalSpace (E ⊗[ℂ] S) := projectiveTensorTopology E S
  letI : TopologicalSpace (R ⊗[ℂ] Z) := projectiveTensorTopology R Z
  letI : IsTopologicalAddGroup E := (PolynormableSpace.withSeminorms ℂ E).topologicalAddGroup
  letI : IsTopologicalAddGroup F := (PolynormableSpace.withSeminorms ℂ F).topologicalAddGroup
  letI : IsTopologicalAddGroup Z := (PolynormableSpace.withSeminorms ℂ Z).topologicalAddGroup
  letI : IsTopologicalAddGroup S := projectiveTensor_withSeminorms.topologicalAddGroup
  letI : IsTopologicalAddGroup (E ⊗[ℂ] S) := projectiveTensor_withSeminorms.topologicalAddGroup
  letI : PolynormableSpace ℂ S := projectiveTensor_withSeminorms.toPolynormableSpace
  let A := (TensorProduct.assoc ℂ E F Z).symm.toLinearMap
  change Continuous A
  apply projectiveTensor_withSeminorms.continuous_of_continuous_comp A
  intro P
  obtain ⟨a, b, ha, hb, hab⟩ := continuous_bilinear_bound
    (TensorProduct.mk ℂ E F) continuous_projectiveTensor_tmul P.first P.first_continuous
  let B := {x : E // a x ≤ 1}
  letI : Nonempty B := ⟨⟨0, by simp⟩⟩
  let r (x : B) : Seminorm ℂ S := P.tensor.comp (A.comp (TensorProduct.mk ℂ E S x.val))
  have hr (x : B) (y : F) (z : Z) : r x (y ⊗ₜ[ℂ] z) ≤ b y * P.second z := by
    change P.tensor ((TensorProduct.assoc ℂ E F Z).symm (x.val ⊗ₜ[ℂ] (y ⊗ₜ[ℂ] z))) ≤ _
    rw [TensorProduct.assoc_symm_tmul]
    exact (P.bound _ _).trans (mul_le_mul_of_nonneg_right
      ((hab _ _).trans (mul_le_of_le_one_left (apply_nonneg b y) x.property))
      (apply_nonneg P.second z))
  have hbound : BddAbove (range r) := Seminorm.bddAbove_range_iff.mpr fun t => by
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, forall_mem_range.mpr fun x => le_of_eq (map_zero (r x))⟩
    | tmul y z => exact ⟨b y * P.second z, forall_mem_range.mpr fun x => hr x y z⟩
    | add s t hs ht =>
      obtain ⟨C, hC⟩ := hs
      obtain ⟨D, hD⟩ := ht
      exact ⟨C + D, forall_mem_range.mpr fun x => (map_add_le_add (r x) s t).trans
        (add_le_add (hC (mem_range_self x)) (hD (mem_range_self x)))⟩
  let d : Seminorm ℂ S := ⨆ x, r x
  let P' : ProjectiveTensorTest F Z := ⟨d, b, P.second, hb, P.second_continuous, fun y z =>
    (Seminorm.iSup_apply hbound).trans_le (ciSup_le fun x => hr x y z)⟩
  have hd : Continuous d := projectiveTensor_withSeminorms.continuous_seminorm P'
  have hnear : ∀ᶠ v : E × S in 𝓝 0, a v.1 ≤ 1 :=
    ((ha.comp continuous_fst).tendsto' 0 0 (by simp : a ((0 : E × S).1) = 0)).eventually
      (Iic_mem_nhds zero_lt_one)
  let C := P.tensor.comp A
  have hC : {v : E × S | C (v.1 ⊗ₜ[ℂ] v.2) ≤ 1} ∈ 𝓝 (0, 0) := by
    have hnear' : ∀ᶠ v : E × S in 𝓝 0, d v.2 ≤ 1 :=
      ((hd.comp continuous_snd).tendsto' 0 0 (by simp : d ((0 : E × S).2) = 0)).eventually
        (Iic_mem_nhds zero_lt_one)
    filter_upwards [hnear, hnear'] with v h₁ h₂
    exact ((le_ciSup hbound ⟨v.1, h₁⟩ : r ⟨v.1, h₁⟩ ≤ d) v.2).trans h₂
  obtain ⟨p, q, hp, hq, hpq⟩ := bilinear_bound_of_nhds (TensorProduct.mk ℂ E S) C hC
  exact projectiveTensor_withSeminorms.continuous_seminorm ⟨C, p, q, hp, hq, hpq⟩

universe u v w

/-- The projective tensor product of two nuclear locally convex spaces is
nuclear. This is Lemma C.2.4.10(3). -/
theorem nuclearLocallyConvex_projectiveTensor {X : Type u} {Y : Type w}
    [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]
    (hX : NuclearLocallyConvex.{max w v, u} X) (hY : NuclearLocallyConvex.{v, w} Y) :
    letI : TopologicalSpace (X ⊗[ℂ] Y) := projectiveTensorTopology X Y
    NuclearLocallyConvex.{v, max u w} (X ⊗[ℂ] Y) := by
  letI : PolynormableSpace ℂ X := hX.2.1
  letI : PolynormableSpace ℂ Y := hY.2.1
  letI : T2Space X := hX.1
  letI : T2Space Y := hY.1
  let R := X ⊗[ℂ] Y
  letI : TopologicalSpace R := projectiveTensorTopology X Y
  letI : PolynormableSpace ℂ R := projectiveTensor_withSeminorms.toPolynormableSpace
  letI : T2Space R := projectiveTensor_t2
  refine ⟨inferInstance, inferInstance, fun G _ _ _ _ _ => ?_⟩
  let S := Y ⊗[ℂ] G
  letI : TopologicalSpace S := projectiveTensorTopology Y G
  letI : PolynormableSpace ℂ S := projectiveTensor_withSeminorms.toPolynormableSpace
  letI : T2Space S := projectiveTensor_t2
  have hXY : projectiveTensorTopology X Y = injectiveTensorTopology X Y := by
    let Y' := ULift.{v} Y
    letI : PolynormableSpace ℂ Y' :=
      (Homeomorph.ulift.isInducing).polynormableSpace (f := ULift.moduleEquiv.toLinearMap)
    let lift : Y →L[ℂ] Y' := ⟨ULift.moduleEquiv.symm.toLinearMap, continuous_uliftUp⟩
    let down : Y' →L[ℂ] Y := ⟨ULift.moduleEquiv.toLinearMap, continuous_uliftDown⟩
    let idX := ContinuousLinearMap.id ℂ X
    have h1 := projectiveTensor_map_continuous idX down
    rw [hX.2.2 Y'] at h1
    have h2 := injectiveTensor_map_continuous idX lift
    apply tensorTopologies_equal_of_continuous_projectiveTests
    intro P
    have hp : Continuous[projectiveTensorTopology X Y, _] P.tensor := by
      letI : TopologicalSpace (X ⊗[ℂ] Y) := projectiveTensorTopology X Y
      exact projectiveTensor_withSeminorms.continuous_seminorm P
    have hc : Continuous[injectiveTensorTopology X Y', _]
        (fun z => P.tensor (TensorProduct.map idX.toLinearMap down.toLinearMap z)) :=
      @Continuous.comp _ _ _ (injectiveTensorTopology X Y') (projectiveTensorTopology X Y)
        _ _ _ hp h1
    refine @Continuous.congr _ _ (injectiveTensorTopology X Y) _ _ _
      (@Continuous.comp _ _ _ (injectiveTensorTopology X Y) (injectiveTensorTopology X Y')
        _ _ _ hc h2) ?_
    intro z
    dsimp only [Function.comp_apply]
    rw [← LinearMap.comp_apply, ← TensorProduct.map_comp]
    have hd : down.toLinearMap.comp lift.toLinearMap = LinearMap.id :=
      LinearMap.ext fun _ => rfl
    rw [hd]
    change P.tensor (TensorProduct.map LinearMap.id LinearMap.id z) = _
    rw [TensorProduct.map_id, LinearMap.id_apply]
  have hA : Continuous[injectiveTensorTopology R G, injectiveTensorTopology X S]
      (TensorProduct.assoc ℂ X Y G) := by
    rw [show injectiveTensorTopology R G =
      @injectiveTensorTopology R G _ _ (injectiveTensorTopology X Y) _ _ _ by
        exact congrArg (fun t => @injectiveTensorTopology R G _ _ t _ _ _) hXY]
    rw [show injectiveTensorTopology X S =
      @injectiveTensorTopology X S _ _ _ _ _ (injectiveTensorTopology Y G) by
        exact congrArg (fun t => @injectiveTensorTopology X S _ _ _ _ _ t) (hY.2.2 G)]
    letI : TopologicalSpace R := injectiveTensorTopology X Y
    letI : TopologicalSpace S := injectiveTensorTopology Y G
    letI : TopologicalSpace (R ⊗[ℂ] G) := injectiveTensorTopology R G
    letI : TopologicalSpace (X ⊗[ℂ] S) := injectiveTensorTopology X S
    exact (injectiveTensor_assoc (X := X) (Y := Y) (Z := G)).continuous
  have hback : Continuous[injectiveTensorTopology X S, projectiveTensorTopology R G]
      (TensorProduct.assoc ℂ X Y G).symm := by
    rw [← hX.2.2 S]
    exact projectiveTensor_assoc_symm_continuous
  have hc := @Continuous.comp _ _ _ (injectiveTensorTopology R G) (injectiveTensorTopology X S)
    (projectiveTensorTopology R G) _ _ hback hA
  have hid : Continuous[injectiveTensorTopology R G, projectiveTensorTopology R G]
      (id : R ⊗[ℂ] G → R ⊗[ℂ] G) :=
    @Continuous.congr _ _ (injectiveTensorTopology R G) (projectiveTensorTopology R G)
      _ _ hc (TensorProduct.assoc ℂ X Y G).symm_apply_apply
  apply le_antisymm
  · simpa only [induced_id] using continuous_iff_le_induced.mp
      (projective_to_injective_continuous (E := R) (F := G))
  · simpa only [induced_id] using continuous_iff_le_induced.mp hid

end
end Masullo
