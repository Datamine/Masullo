import InjectiveTensorMaps

open Filter Function Set Topology UniformSpace
open scoped NNReal PointwiseConvergenceCLM TensorProduct Uniformity

namespace Masullo

noncomputable section

open scoped Classical
open InjectiveTensorTools

set_option maxHeartbeats 1800000

variable {X Y X' Y' : Type*}
variable [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
variable [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]
variable [AddCommGroup X'] [Module ℂ X'] [TopologicalSpace X']
variable [AddCommGroup Y'] [Module ℂ Y'] [TopologicalSpace Y']

section Association

variable {Z : Type*} [AddCommGroup Z] [Module ℂ Z] [TopologicalSpace Z]

private def pairDualMap (S : InjectiveDualTest X) (T : InjectiveDualTest Y) :
    letI : TopologicalSpace (X ⊗[ℂ] Y) := injectiveTensorTopology X Y
    S.forms × T.forms → ((X ⊗[ℂ] Y) →Lₚₜ[ℂ] ℂ) := by
  letI : TopologicalSpace (X ⊗[ℂ] Y) := injectiveTensorTopology X Y
  letI : IsTopologicalAddGroup (X ⊗[ℂ] Y) := injectiveTensor_withSeminorms.topologicalAddGroup
  intro p
  refine ⟨dualPair p.1.val p.2.val, ?_⟩
  apply (norm_withSeminorms ℂ ℂ).continuous_of_continuous_comp
  intro _
  exact Seminorm.continuous_of_le (injectiveTensor_withSeminorms.continuous_seminorm (S, T))
    (fun z => norm_dualPair_le S T z p.1.property p.2.property)

private def pairDualTest (S : InjectiveDualTest X) (T : InjectiveDualTest Y) :
    @InjectiveDualTest (X ⊗[ℂ] Y) _ _ (injectiveTensorTopology X Y) := by
  letI : TopologicalSpace (X ⊗[ℂ] Y) := injectiveTensorTopology X Y
  letI : CompactSpace S.forms := isCompact_iff_compactSpace.mp S.compact
  letI : CompactSpace T.forms := isCompact_iff_compactSpace.mp T.compact
  refine ⟨range (pairDualMap S T), isCompact_range ?_, ?_⟩
  · apply PointwiseConvergenceCLM.continuous_of_continuous_eval
    intro x
    exact (tensorPairEvaluation S.forms T.forms x).continuous.congr
      (fun p => (dualPair_eq_tensorPairEvaluation S T x p.1 p.2).symm)
  · intro ε hε
    have h := (injectiveTensor_withSeminorms.continuous_seminorm (S, T)).tendsto'
      0 0 (map_zero _)
    filter_upwards [h (Iic_mem_nhds hε)] with x hx φ hφ
    obtain ⟨p, rfl⟩ := hφ
    exact (norm_dualPair_le S T x p.1.property p.2.property).trans hx

private def rightContract (ψ : Z →Lₚₜ[ℂ] ℂ) :
    ((X ⊗[ℂ] Y) ⊗[ℂ] Z) →ₗ[ℂ] (X ⊗[ℂ] Y) :=
  (TensorProduct.rid ℂ _).toLinearMap.comp (TensorProduct.map LinearMap.id ψ.toLinearMap)

private theorem dualPair_contract (ψ : Z →Lₚₜ[ℂ] ℂ)
    (η : letI : TopologicalSpace (X ⊗[ℂ] Y) := injectiveTensorTopology X Y
         (X ⊗[ℂ] Y) →Lₚₜ[ℂ] ℂ) (z : (X ⊗[ℂ] Y) ⊗[ℂ] Z) :
    letI : TopologicalSpace (X ⊗[ℂ] Y) := injectiveTensorTopology X Y
    dualPair η ψ z = η (rightContract ψ z) := by
  letI : TopologicalSpace (X ⊗[ℂ] Y) := injectiveTensorTopology X Y
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    rw [dualPair_tmul]
    change η a * ψ b = η ((ψ b) • a)
    rw [map_smul, smul_eq_mul, mul_comm]
  | add u v hu hv => simp only [map_add, hu, hv]

private theorem dualPair_contract_assoc
    (S : InjectiveDualTest Y) (T : InjectiveDualTest Z)
    (φ : X →Lₚₜ[ℂ] ℂ) (p : S.forms × T.forms) (z : (X ⊗[ℂ] Y) ⊗[ℂ] Z) :
    letI : TopologicalSpace (Y ⊗[ℂ] Z) := injectiveTensorTopology Y Z
    dualPair φ p.1.val (rightContract p.2.val z) =
      dualPair φ (pairDualMap S T p) (TensorProduct.assoc ℂ X Y Z z) := by
  letI : TopologicalSpace (Y ⊗[ℂ] Z) := injectiveTensorTopology Y Z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    induction a using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
      rw [TensorProduct.assoc_tmul, dualPair_tmul]
      change dualPair φ p.1.val (p.2.val b • (x ⊗ₜ[ℂ] y)) =
        φ x * dualPair p.1.val p.2.val (y ⊗ₜ[ℂ] b)
      rw [map_smul, smul_eq_mul, dualPair_tmul, dualPair_tmul]
      ring
    | add u v hu hv => simp only [TensorProduct.add_tmul, map_add, hu, hv]
  | add u v hu hv => simp only [map_add, hu, hv]

private theorem bounded_dualTest_by_tensor_tests
    (P : @InjectiveDualTest (X ⊗[ℂ] Y) _ _ (injectiveTensorTopology X Y)) :
    ∃ (I : Finset (InjectiveDualTest X × InjectiveDualTest Y)) (c : ℝ≥0),
      letI : TopologicalSpace (X ⊗[ℂ] Y) := injectiveTensorTopology X Y
      ∀ η ∈ P.forms, ∀ x, ‖η x‖ ≤ c * (I.sup injectiveTensorSeminorm) x := by
  letI : TopologicalSpace (X ⊗[ℂ] Y) := injectiveTensorTopology X Y
  obtain ⟨⟨I, r⟩, hr, hI⟩ := injectiveTensor_withSeminorms.hasBasis_zero_ball.mem_iff.mp
    (P.equicontinuous 1 zero_lt_one)
  let c : ℝ≥0 := ⟨r⁻¹, inv_nonneg.mpr hr.le⟩
  let q : Seminorm ℂ (X ⊗[ℂ] Y) := c • (I.sup injectiveTensorSeminorm)
  refine ⟨I, c, fun η hη => ?_⟩
  apply seminorm_bound_of_unitBall ((normSeminorm ℂ ℂ).comp η.toLinearMap) q
  intro x hx
  apply hI _ η hη
  apply (I.sup injectiveTensorSeminorm).mem_ball_zero.mpr
  exact (inv_mul_lt_iff₀ hr).mp hx |>.trans_eq (mul_one _)

private theorem injectiveTensor_assoc_symm_continuous :
    letI : TopologicalSpace (X ⊗[ℂ] Y) := injectiveTensorTopology X Y
    letI : TopologicalSpace (Y ⊗[ℂ] Z) := injectiveTensorTopology Y Z
    Continuous[injectiveTensorTopology X (Y ⊗[ℂ] Z), injectiveTensorTopology (X ⊗[ℂ] Y) Z]
      (TensorProduct.assoc ℂ X Y Z).symm := by
  letI : TopologicalSpace (X ⊗[ℂ] Y) := injectiveTensorTopology X Y
  letI : TopologicalSpace (Y ⊗[ℂ] Z) := injectiveTensorTopology Y Z
  letI : TopologicalSpace (X ⊗[ℂ] (Y ⊗[ℂ] Z)) := injectiveTensorTopology X (Y ⊗[ℂ] Z)
  letI : IsTopologicalAddGroup (X ⊗[ℂ] (Y ⊗[ℂ] Z)) := injectiveTensor_withSeminorms.topologicalAddGroup
  letI : TopologicalSpace ((X ⊗[ℂ] Y) ⊗[ℂ] Z) := injectiveTensorTopology (X ⊗[ℂ] Y) Z
  let L := (TensorProduct.assoc ℂ X Y Z).symm.toLinearMap
  apply (injectiveTensor_withSeminorms.continuous_iff_continuous_comp L).mpr
  rintro ⟨P, T⟩
  obtain ⟨I, c, hc⟩ := bounded_dualTest_by_tensor_tests P
  let Q (i : InjectiveDualTest X × InjectiveDualTest Y) := injectiveTensorSeminorm (i.1, pairDualTest i.2 T)
  refine Seminorm.continuous_of_le (q := c • I.sup Q) ?_ ?_
  · exact continuous_const.mul (Seminorm.continuous_finsetSup fun i _ =>
      injectiveTensor_withSeminorms.continuous_seminorm (i.1, pairDualTest i.2 T))
  intro z
  apply injectiveTensorSeminorm_le P T _ (apply_nonneg (c • I.sup Q) z)
  intro η hη ψ hψ
  change ‖dualPair η ψ (L z)‖ ≤ _
  rw [dualPair_contract]
  refine (hc η hη _).trans (mul_le_mul_of_nonneg_left ?_ c.property)
  have hb : ∀ i ∈ I, injectiveTensorSeminorm i (rightContract ψ (L z)) ≤ (I.sup Q) z := by
    rintro ⟨S, U⟩ hi
    refine (injectiveTensorSeminorm_le S U _ (apply_nonneg _ _) ?_).trans (Seminorm.le_finset_sup_apply (p := Q) hi)
    intro φ hφ ξ hξ
    let p : U.forms × T.forms := (⟨ξ, hξ⟩, ⟨ψ, hψ⟩)
    have h := dualPair_contract_assoc U T φ p (L z)
    change dualPair φ ξ (rightContract ψ (L z)) =
      dualPair φ (pairDualMap U T p) ((TensorProduct.assoc ℂ X Y Z) (L z)) at h
    rw [show (TensorProduct.assoc ℂ X Y Z) (L z) = z from LinearEquiv.apply_symm_apply _ _] at h
    rw [h]
    exact norm_dualPair_le S (pairDualTest U T) z hφ (mem_range_self p)
  change (I.sup injectiveTensorSeminorm) (rightContract ψ (L z)) ≤ _
  exact Seminorm.finset_sup_apply_le (apply_nonneg _ _) hb

private theorem dualPair_comm (φ : X →Lₚₜ[ℂ] ℂ) (ψ : Y →Lₚₜ[ℂ] ℂ)
    (z : X ⊗[ℂ] Y) :
    dualPair ψ φ (TensorProduct.comm ℂ X Y z) = dualPair φ ψ z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [mul_comm]
  | add x y hx hy => simp only [map_add, hx, hy]

private def injectiveTensorCommL :
    letI : TopologicalSpace (X ⊗[ℂ] Y) := injectiveTensorTopology X Y
    letI : TopologicalSpace (Y ⊗[ℂ] X) := injectiveTensorTopology Y X
    (X ⊗[ℂ] Y) →L[ℂ] (Y ⊗[ℂ] X) := by
  letI : TopologicalSpace (X ⊗[ℂ] Y) := injectiveTensorTopology X Y
  letI : IsTopologicalAddGroup (X ⊗[ℂ] Y) := injectiveTensor_withSeminorms.topologicalAddGroup
  letI : TopologicalSpace (Y ⊗[ℂ] X) := injectiveTensorTopology Y X
  let L := (TensorProduct.comm ℂ X Y).toLinearMap
  refine ⟨L, (injectiveTensor_withSeminorms.continuous_iff_continuous_comp L).mpr ?_⟩
  rintro ⟨S, T⟩
  apply Seminorm.continuous_of_le (injectiveTensor_withSeminorms.continuous_seminorm (T, S))
  intro z
  apply injectiveTensorSeminorm_le S T _ (apply_nonneg (injectiveTensorSeminorm (T, S)) z)
  intro φ hφ ψ hψ
  change ‖dualPair φ ψ (TensorProduct.comm ℂ X Y z)‖ ≤ _
  rw [dualPair_comm]
  exact norm_dualPair_le T S z hψ hφ

private def injectiveTensorMapL (f : X →L[ℂ] X') (g : Y →L[ℂ] Y') :
    letI : TopologicalSpace (X ⊗[ℂ] Y) := injectiveTensorTopology X Y
    letI : TopologicalSpace (X' ⊗[ℂ] Y') := injectiveTensorTopology X' Y'
    (X ⊗[ℂ] Y) →L[ℂ] (X' ⊗[ℂ] Y') := by
  letI : TopologicalSpace (X ⊗[ℂ] Y) := injectiveTensorTopology X Y
  letI : TopologicalSpace (X' ⊗[ℂ] Y') := injectiveTensorTopology X' Y'
  exact ⟨TensorProduct.map f.toLinearMap g.toLinearMap, injectiveTensor_map_continuous f g⟩

/-- Rebracketing three injective tensor factors is a linear homeomorphism. -/
theorem injectiveTensor_assoc :
    letI : TopologicalSpace (X ⊗[ℂ] Y) := injectiveTensorTopology X Y
    letI : TopologicalSpace (Y ⊗[ℂ] Z) := injectiveTensorTopology Y Z
    @IsHomeomorph _ _ (injectiveTensorTopology (X ⊗[ℂ] Y) Z)
      (injectiveTensorTopology X (Y ⊗[ℂ] Z)) (TensorProduct.assoc ℂ X Y Z) := by
  letI : TopologicalSpace (X ⊗[ℂ] Y) := injectiveTensorTopology X Y
  letI : TopologicalSpace (Y ⊗[ℂ] Z) := injectiveTensorTopology Y Z
  letI : TopologicalSpace (Y ⊗[ℂ] X) := injectiveTensorTopology Y X
  letI : TopologicalSpace (Z ⊗[ℂ] Y) := injectiveTensorTopology Z Y
  letI : TopologicalSpace ((X ⊗[ℂ] Y) ⊗[ℂ] Z) := injectiveTensorTopology (X ⊗[ℂ] Y) Z
  letI : TopologicalSpace ((Z ⊗[ℂ] Y) ⊗[ℂ] X) := injectiveTensorTopology (Z ⊗[ℂ] Y) X
  letI : TopologicalSpace (Z ⊗[ℂ] (X ⊗[ℂ] Y)) := injectiveTensorTopology Z (X ⊗[ℂ] Y)
  letI : TopologicalSpace (Z ⊗[ℂ] (Y ⊗[ℂ] X)) := injectiveTensorTopology Z (Y ⊗[ℂ] X)
  letI : TopologicalSpace ((Y ⊗[ℂ] Z) ⊗[ℂ] X) := injectiveTensorTopology (Y ⊗[ℂ] Z) X
  letI : TopologicalSpace (X ⊗[ℂ] (Y ⊗[ℂ] Z)) := injectiveTensorTopology X (Y ⊗[ℂ] Z)
  let R : (Z ⊗[ℂ] (Y ⊗[ℂ] X)) →L[ℂ] ((Z ⊗[ℂ] Y) ⊗[ℂ] X) :=
    ⟨(TensorProduct.assoc ℂ Z Y X).symm.toLinearMap, injectiveTensor_assoc_symm_continuous⟩
  let L := (injectiveTensorCommL (X := Y ⊗[ℂ] Z) (Y := X)).comp
    ((injectiveTensorMapL (injectiveTensorCommL (X := Z) (Y := Y)) (ContinuousLinearMap.id ℂ X)).comp
      (R.comp ((injectiveTensorMapL (ContinuousLinearMap.id ℂ Z)
        (injectiveTensorCommL (X := X) (Y := Y))).comp
        (injectiveTensorCommL (X := X ⊗[ℂ] Y) (Y := Z)))))
  have he : L.toLinearMap = (TensorProduct.assoc ℂ X Y Z).toLinearMap := by
    apply TensorProduct.ext'
    intro w z
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
      change TensorProduct.comm ℂ (Y ⊗[ℂ] Z) X
        ((TensorProduct.map (TensorProduct.comm ℂ Z Y).toLinearMap LinearMap.id)
          ((TensorProduct.assoc ℂ Z Y X).symm
            ((TensorProduct.map LinearMap.id (TensorProduct.comm ℂ X Y).toLinearMap)
              (TensorProduct.comm ℂ (X ⊗[ℂ] Y) Z ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] z))))) =
          TensorProduct.assoc ℂ X Y Z ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] z)
      simp [TensorProduct.map_tmul, TensorProduct.assoc_tmul, TensorProduct.assoc_symm_tmul]
    | add u v hu hv => simp only [TensorProduct.add_tmul, map_add, hu, hv]
  have hc : Continuous (TensorProduct.assoc ℂ X Y Z) := by
    have h := L.continuous
    change Continuous L.toLinearMap at h
    rwa [he] at h
  exact (TensorProduct.assoc ℂ X Y Z).toEquiv.isHomeomorph_iff.mpr
    ⟨hc, injectiveTensor_assoc_symm_continuous⟩

end Association

end

end Masullo
