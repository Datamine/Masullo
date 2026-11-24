import HilbertSchmidtKernels
import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.Analysis.Normed.Operator.Extend

open Filter Function MeasureTheory Set Topology UniformSpace
open scoped ENNReal InnerProductSpace TensorProduct

namespace Masullo

noncomputable section

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν]

local notation "ScalarL2(" μ ")" => (Lp ℂ 2 μ)

omit [SFinite μ] [SFinite ν] in
private theorem lpTwoProduct_memLp (u : ScalarL2(μ)) (v : ScalarL2(ν)) :
    MemLp (fun p : X × Y => u p.1 * v p.2) 2 (μ.prod ν) := by
  have hu := Lp.memLp u
  have hv := Lp.memLp v
  have hu' := Measure.quasiMeasurePreserving_fst (μ := μ) (ν := ν)
  have hv' := Measure.quasiMeasurePreserving_snd (μ := μ) (ν := ν)
  apply (memLp_two_iff_integrable_sq_norm
    ((hu.1.comp_quasiMeasurePreserving hu').mul (hv.1.comp_quasiMeasurePreserving hv'))).2
  simpa only [norm_mul, mul_pow, Pi.mul_apply, Function.comp_apply] using
    Integrable.mul_prod ((memLp_two_iff_integrable_sq_norm hu.1).1 hu)
      ((memLp_two_iff_integrable_sq_norm hv.1).1 hv)

/-- The ordinary product of two L² functions as a class on the product measure. -/
def lpTwoProduct (u : ScalarL2(μ)) (v : ScalarL2(ν)) : ScalarL2(μ.prod ν) :=
  (lpTwoProduct_memLp u v).toLp (fun p => u p.1 * v p.2)

omit [SFinite μ] [SFinite ν] in
theorem lpTwoProduct_ae (u : ScalarL2(μ)) (v : ScalarL2(ν)) :
    (lpTwoProduct u v : X × Y → ℂ) =ᵐ[μ.prod ν] fun p => u p.1 * v p.2 :=
  (lpTwoProduct_memLp u v).coeFn_toLp

omit [SFinite μ] [SFinite ν] in
private theorem lpTwoProduct_add_left (u w : ScalarL2(μ)) (v : ScalarL2(ν)) :
    lpTwoProduct (u + w) v = lpTwoProduct u v + lpTwoProduct w v := by
  apply Lp.ext
  filter_upwards [lpTwoProduct_ae (u + w) v, lpTwoProduct_ae u v, lpTwoProduct_ae w v,
    Lp.coeFn_add (lpTwoProduct u v) (lpTwoProduct w v),
    (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := ν)).ae_eq_comp (Lp.coeFn_add u w)]
    with p ha hu hw hb hc
  change (u + w) p.1 = u p.1 + w p.1 at hc
  rw [ha, hb, Pi.add_apply, hu, hw, hc, add_mul]

omit [SFinite μ] [SFinite ν] in
private theorem lpTwoProduct_add_right (u : ScalarL2(μ)) (v w : ScalarL2(ν)) :
    lpTwoProduct u (v + w) = lpTwoProduct u v + lpTwoProduct u w := by
  apply Lp.ext
  filter_upwards [lpTwoProduct_ae u (v + w), lpTwoProduct_ae u v, lpTwoProduct_ae u w,
    Lp.coeFn_add (lpTwoProduct u v) (lpTwoProduct u w),
    (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := ν)).ae_eq_comp (Lp.coeFn_add v w)]
    with p ha hv hw hb hc
  change (v + w) p.2 = v p.2 + w p.2 at hc
  rw [ha, hb, Pi.add_apply, hv, hw, hc, mul_add]

omit [SFinite μ] [SFinite ν] in
private theorem lpTwoProduct_smul_left (d : ℂ) (u : ScalarL2(μ)) (v : ScalarL2(ν)) :
    lpTwoProduct (d • u) v = d • lpTwoProduct u v := by
  apply Lp.ext
  filter_upwards [lpTwoProduct_ae (d • u) v, lpTwoProduct_ae u v, Lp.coeFn_smul d (lpTwoProduct u v),
    (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := ν)).ae_eq_comp (Lp.coeFn_smul d u)]
    with p ha hu hb hc
  change (d • u) p.1 = d • u p.1 at hc
  rw [ha, hb, Pi.smul_apply, hu, hc, smul_mul_assoc]

omit [SFinite μ] [SFinite ν] in
private theorem lpTwoProduct_smul_right (d : ℂ) (u : ScalarL2(μ)) (v : ScalarL2(ν)) :
    lpTwoProduct u (d • v) = d • lpTwoProduct u v := by
  apply Lp.ext
  filter_upwards [lpTwoProduct_ae u (d • v), lpTwoProduct_ae u v, Lp.coeFn_smul d (lpTwoProduct u v),
    (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := ν)).ae_eq_comp (Lp.coeFn_smul d v)]
    with p ha hu hb hc
  change (d • v) p.2 = d • v p.2 at hc
  rw [ha, hb, Pi.smul_apply, hu, hc, mul_smul_comm]

private def lpTwoProductBilin : ScalarL2(μ) →ₗ[ℂ] ScalarL2(ν) →ₗ[ℂ] ScalarL2(μ.prod ν) :=
  LinearMap.mk₂ ℂ lpTwoProduct lpTwoProduct_add_left lpTwoProduct_smul_left
    lpTwoProduct_add_right lpTwoProduct_smul_right

private def lpTwoTensorLinear : (ScalarL2(μ) ⊗[ℂ] ScalarL2(ν)) →ₗ[ℂ] ScalarL2(μ.prod ν) :=
  TensorProduct.lift lpTwoProductBilin

private theorem lpTwoTensorLinear_tmul (u : ScalarL2(μ)) (v : ScalarL2(ν)) :
    lpTwoTensorLinear (u ⊗ₜ[ℂ] v) = lpTwoProduct u v := rfl

private theorem lpTwoProduct_inner (u u' : ScalarL2(μ)) (v v' : ScalarL2(ν)) :
    ⟪lpTwoProduct u v, lpTwoProduct u' v'⟫_ℂ = ⟪u, u'⟫_ℂ * ⟪v, v'⟫_ℂ := by
  simp only [L2.inner_def]
  rw [← integral_prod_mul]
  apply integral_congr_ae
  filter_upwards [lpTwoProduct_ae u v, lpTwoProduct_ae u' v'] with p hp hp'
  change ⟪lpTwoProduct u v p, lpTwoProduct u' v' p⟫_ℂ = ⟪u p.1, u' p.1⟫_ℂ * ⟪v p.2, v' p.2⟫_ℂ
  rw [hp, hp']
  simp only [RCLike.inner_apply, map_mul]
  ring

/-- The algebraic Hilbert tensor of two L² spaces isometrically embeds into
the L² space of their product. -/
def lpTwoTensorIsometry : (ScalarL2(μ) ⊗[ℂ] ScalarL2(ν)) →ₗᵢ[ℂ] ScalarL2(μ.prod ν) :=
  lpTwoTensorLinear.isometryOfInner fun x y => by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x x' hx hx' => simp [hx, hx', inner_add_left]
    | tmul u v =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add y y' hy hy' => simp [hy, hy', inner_add_right]
      | tmul u' v' => simpa only [lpTwoTensorLinear_tmul, TensorProduct.inner_tmul] using lpTwoProduct_inner u u' v v'

theorem lpTwoTensorIsometry_tmul (u : ScalarL2(μ)) (v : ScalarL2(ν)) :
    lpTwoTensorIsometry (u ⊗ₜ[ℂ] v) = lpTwoProduct u v := rfl

private theorem lpTwoProduct_inner_kernel (u : ScalarL2(μ)) (v : ScalarL2(ν)) (k : ScalarL2(μ.prod ν)) :
    ⟪lpTwoProduct u v, k⟫_ℂ =
      ⟪u, kernelIntegralOperator k ((Lp.memLp v).star.toLp (fun y => star (v y)))⟫_ℂ := by
  let w := (Lp.memLp v).star.toLp (fun y => star (v y))
  have hw : (w : Y → ℂ) =ᵐ[ν] fun y => star (v y) := (Lp.memLp v).star.coeFn_toLp
  have hki := L2.integrable_inner (𝕜 := ℂ) (lpTwoProduct u v) k
  simp only [L2.inner_def]
  rw [integral_prod _ hki]
  apply integral_congr_ae
  filter_upwards [kernelIntegralOperator_apply k w, Measure.ae_ae_of_ae_prod (lpTwoProduct_ae u v)]
    with x hx hy
  change (∫ y, ⟪lpTwoProduct u v (x, y), k (x, y)⟫_ℂ ∂ν) =
    ⟪u x, kernelIntegralOperator k w x⟫_ℂ
  rw [hx.2, RCLike.inner_apply, ← integral_mul_const]
  apply integral_congr_ae
  filter_upwards [hy, hw] with y hxy hwy
  change lpTwoProduct u v (x, y) = u x * v y at hxy
  change w y = star (v y) at hwy
  rw [hxy, hwy]
  simp only [RCLike.inner_apply, map_mul, Complex.star_def]
  ring

/-- Separable L² on the second factor is enough for density of the algebraic
Hilbert tensor in the product L² space. -/
theorem denseRange_lpTwoTensorIsometry [MeasureTheory.IsSeparable ν] :
    DenseRange (lpTwoTensorIsometry (μ := μ) (ν := ν)) := by
  let J := lpTwoTensorIsometry (μ := μ) (ν := ν)
  let S := (LinearMap.range J.toLinearMap).topologicalClosure
  suffices hS : S = ⊤ by
    intro x
    change x ∈ (S : Set (ScalarL2(μ.prod ν)))
    simp [hS]
  letI : CompleteSpace S := (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  apply Submodule.orthogonal_eq_bot_iff.mp
  apply (Submodule.eq_bot_iff Sᗮ).mpr
  intro k hk
  change k = 0
  obtain ⟨s, hs, ⟨b⟩⟩ := exists_countable_hilbertBasis_L2 (ν := ν)
  letI : Countable s := hs.to_subtype
  apply kernelIntegralOperator_injective b
  change kernelIntegralOperator k = kernelIntegralOperatorCLM 0
  rw [map_zero]
  ext w : 1
  let v := (Lp.memLp w).star.toLp (fun y => star (w y))
  have htwist : ((Lp.memLp v).star.toLp (fun y => star (v y))) = w := by
    apply Lp.ext
    filter_upwards [(Lp.memLp w).star.coeFn_toLp, (Lp.memLp v).star.coeFn_toLp] with y hy h
    change v y = star (w y) at hy
    change ((Lp.memLp v).star.toLp (fun t => star (v t))) y = star (v y) at h
    rw [h, hy, star_star]
  have hM (u : ScalarL2(μ)) : lpTwoProduct u v ∈ S := by
    apply Submodule.le_topologicalClosure
    exact ⟨u ⊗ₜ[ℂ] v, lpTwoTensorIsometry_tmul u v⟩
  have hz := (Submodule.mem_orthogonal S k).mp hk _ (hM (kernelIntegralOperator k w))
  rw [lpTwoProduct_inner_kernel, htwist, inner_self_eq_zero] at hz
  simpa using hz

/-- Extend an isometric linear map to the norm completion of its source. -/
def completionLinearIsometry {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F] (J : E →ₗᵢ[ℂ] F) :
    Completion E →ₗᵢ[ℂ] F := by
  let i : E →ₗᵢ[ℂ] Completion E := Completion.toComplₗᵢ
  let L := J.toLinearMap.extendOfNorm i.toLinearMap
  have hd : DenseRange i := Completion.denseRange_coe
  have hB : ∃ C : ℝ, ∀ x, ‖J x‖ ≤ C * ‖i x‖ :=
    ⟨1, fun x => by rw [one_mul, J.norm_map, i.norm_map]⟩
  refine { L.toLinearMap with norm_map' := fun v => ?_ }
  refine hd.induction (fun _ ⟨x, hx⟩ => ?_) (isClosed_eq L.continuous.norm continuous_norm) v
  change ‖L _‖ = ‖_‖
  rw [← hx, show L (i x) = J x from LinearMap.extendOfNorm_eq hd hB x, J.norm_map, i.norm_map]

theorem completionLinearIsometry_coe {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F] (J : E →ₗᵢ[ℂ] F) (x : E) :
    completionLinearIsometry J (x : Completion E) = J x := by
  apply LinearMap.extendOfNorm_eq Completion.denseRange_coe
  exact ⟨1, fun u => by simp⟩

/-- An isometric embedding with dense range identifies the completion with its target. -/
def completionLinearIsometryEquiv {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F] (J : E →ₗᵢ[ℂ] F)
    (hJ : DenseRange J) : Completion E ≃ₗᵢ[ℂ] F :=
  LinearIsometryEquiv.ofSurjective (completionLinearIsometry J) (by
    intro y
    apply closure_minimal (s := range J) (t := range (completionLinearIsometry J)) ?_
      (completionLinearIsometry J).isometry.isClosedEmbedding.isClosed_range (hJ y)
    rintro _ ⟨x, rfl⟩
    exact ⟨x, completionLinearIsometry_coe J x⟩)

theorem completionLinearIsometryEquiv_coe {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    [CompleteSpace F] (J : E →ₗᵢ[ℂ] F) (hJ : DenseRange J) (x : E) :
    completionLinearIsometryEquiv J hJ (x : Completion E) = J x :=
  completionLinearIsometry_coe J x

/-- The Hilbert tensor product of two scalar L² spaces is the L² space of the
product measure, acting by ordinary multiplication on simple tensors. -/
def completedLpTwoTensorEquiv [MeasureTheory.IsSeparable ν] :
    Completion (ScalarL2(μ) ⊗[ℂ] ScalarL2(ν)) ≃ₗᵢ[ℂ] ScalarL2(μ.prod ν) :=
  completionLinearIsometryEquiv lpTwoTensorIsometry denseRange_lpTwoTensorIsometry

theorem completedLpTwoTensorEquiv_tmul [MeasureTheory.IsSeparable ν] (u : ScalarL2(μ)) (v : ScalarL2(ν)) :
    completedLpTwoTensorEquiv
      ((u ⊗ₜ[ℂ] v : ScalarL2(μ) ⊗[ℂ] ScalarL2(ν)) : Completion (ScalarL2(μ) ⊗[ℂ] ScalarL2(ν))) = lpTwoProduct u v :=
  (completionLinearIsometryEquiv_coe lpTwoTensorIsometry denseRange_lpTwoTensorIsometry
    (u ⊗ₜ[ℂ] v)).trans (lpTwoTensorIsometry_tmul u v)

end
end Masullo
