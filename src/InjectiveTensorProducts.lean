import InjectiveTensorMaps
import Mathlib.LinearAlgebra.TensorProduct.Pi

open Filter Function Set Topology UniformSpace
open scoped NNReal PointwiseConvergenceCLM TensorProduct Uniformity

namespace Masullo

noncomputable section

open scoped Classical
open InjectiveTensorTools

set_option maxHeartbeats 1800000

section Products

variable {I J : Type*} (A : I → Type*) (B : J → Type*)
variable [∀ i, AddCommGroup (A i)] [∀ i, Module ℂ (A i)] [∀ i, TopologicalSpace (A i)]
variable [∀ j, AddCommGroup (B j)] [∀ j, Module ℂ (B j)] [∀ j, TopologicalSpace (B j)]

/-- The tensor of the two coordinate projections. -/
def injectiveTensorCoordinate (p : I × J) :
    ((∀ i, A i) ⊗[ℂ] (∀ j, B j)) →ₗ[ℂ] (A p.1 ⊗[ℂ] B p.2) :=
  TensorProduct.map (LinearMap.proj p.1) (LinearMap.proj p.2)

private theorem dualTest_finite_coordinates (S : InjectiveDualTest (∀ i, A i)) :
    ∃ U : Finset I, ∀ φ ∈ S.forms, ∀ x : ∀ i, A i,
      φ x = ∑ i ∈ U, (pullDual (ContinuousLinearMap.single ℂ A i) φ) (x i) := by
  obtain ⟨U, T, hT, hsub⟩ := Filter.mem_pi'.mp
    (nhds_pi (a := (0 : ∀ i, A i)) ▸ S.equicontinuous 1 zero_lt_one)
  refine ⟨U, fun φ hφ x => ?_⟩
  have hzero (y : ∀ i, A i) (hy : ∀ i ∈ U, y i = 0) : φ y = 0 := by
    by_contra h
    let c : ℂ := 2 / φ y
    have hc : c • y ∈ Set.pi (U : Set I) T := by
      intro i hi
      change c • y i ∈ T i
      have hmem : (0 : A i) ∈ T i := mem_of_mem_nhds (hT i)
      simpa only [hy i hi, smul_zero] using hmem
    have hb := hsub hc φ hφ
    have he : φ (c • y) = 2 := by
      change (φ : (∀ i, A i) →ₗ[ℂ] ℂ) (c • y) = 2
      rw [map_smul, smul_eq_mul]
      change 2 / φ y * φ y = 2
      exact div_mul_cancel₀ _ h
    rw [he] at hb
    norm_num at hb
  let z := ∑ i ∈ U, Pi.single i (x i)
  have hz : ∀ i ∈ U, (x - z) i = 0 := by
    intro i hi
    change x i - (∑ k ∈ U, Pi.single k (x k)) i = 0
    rw [Finset.sum_apply, Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      exact Pi.single_eq_of_ne hji.symm _
    · exact fun h => (h hi).elim
  have hz' := hzero (x - z) hz
  change (φ : (∀ i, A i) →ₗ[ℂ] ℂ) (x - z) = 0 at hz'
  rw [map_sub, sub_eq_zero] at hz'
  refine hz'.trans ?_
  change (φ : (∀ i, A i) →ₗ[ℂ] ℂ) z = _
  rw [map_sum]
  rfl

private theorem tensorCoordinate_dualPair_sum
    {U : Finset I} {V : Finset J} (φ : (∀ i, A i) →Lₚₜ[ℂ] ℂ)
    (ψ : (∀ j, B j) →Lₚₜ[ℂ] ℂ)
    (hφ : ∀ x, φ x = ∑ i ∈ U, (pullDual (ContinuousLinearMap.single ℂ A i) φ) (x i))
    (hψ : ∀ y, ψ y = ∑ j ∈ V, (pullDual (ContinuousLinearMap.single ℂ B j) ψ) (y j))
    (z : (∀ i, A i) ⊗[ℂ] (∀ j, B j)) :
    dualPair φ ψ z = ∑ i ∈ U, ∑ j ∈ V,
      dualPair (pullDual (ContinuousLinearMap.single ℂ A i) φ)
        (pullDual (ContinuousLinearMap.single ℂ B j) ψ) (injectiveTensorCoordinate A B (i, j) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    simp only [injectiveTensorCoordinate, TensorProduct.map_tmul, dualPair_tmul, LinearMap.proj_apply]
    conv_lhs => rw [hφ x, hψ y]
    rw [Finset.sum_mul]
    simp only [Finset.mul_sum]
  | add x y hx hy =>
    simp only [map_add, hx, hy, Finset.sum_add_distrib]

def injectiveTensorCoordinates :
    ((∀ i, A i) ⊗[ℂ] (∀ j, B j)) →ₗ[ℂ] (∀ p : I × J, A p.1 ⊗[ℂ] B p.2) :=
  LinearMap.pi (injectiveTensorCoordinate A B)

abbrev injectiveTensorCoordinateTopology :
    TopologicalSpace (∀ p : I × J, A p.1 ⊗[ℂ] B p.2) :=
  @Pi.topologicalSpace _ _ fun p => injectiveTensorTopology (A p.1) (B p.2)

private theorem tensorCoordinates_continuous :
    Continuous[injectiveTensorTopology (∀ i, A i) (∀ j, B j), injectiveTensorCoordinateTopology A B]
      (injectiveTensorCoordinates A B) := by
  letI (p : I × J) : TopologicalSpace (A p.1 ⊗[ℂ] B p.2) := injectiveTensorTopology (A p.1) (B p.2)
  letI : TopologicalSpace ((∀ i, A i) ⊗[ℂ] (∀ j, B j)) :=
    injectiveTensorTopology (∀ i, A i) (∀ j, B j)
  apply continuous_pi
  intro p
  exact injectiveTensor_map_continuous
    (ContinuousLinearMap.proj (R := ℂ) (φ := A) p.1)
    (ContinuousLinearMap.proj (R := ℂ) (φ := B) p.2)

private theorem tensorCoordinates_inducing :
    @IsInducing _ _ (injectiveTensorTopology (∀ i, A i) (∀ j, B j)) (injectiveTensorCoordinateTopology A B)
      (injectiveTensorCoordinates A B) := by
  let X := (∀ i, A i) ⊗[ℂ] (∀ j, B j)
  let τ := injectiveTensorTopology (∀ i, A i) (∀ j, B j)
  letI (p : I × J) : TopologicalSpace (A p.1 ⊗[ℂ] B p.2) := injectiveTensorTopology (A p.1) (B p.2)
  letI (p : I × J) : IsTopologicalAddGroup (A p.1 ⊗[ℂ] B p.2) :=
    injectiveTensor_withSeminorms.topologicalAddGroup
  let τcoord := TopologicalSpace.induced (injectiveTensorCoordinates A B) (injectiveTensorCoordinateTopology A B)
  have hle : τ ≤ τcoord := continuous_iff_le_induced.mp (tensorCoordinates_continuous A B)
  letI : TopologicalSpace X := τcoord
  letI : IsTopologicalAddGroup X := topologicalAddGroup_induced (injectiveTensorCoordinates A B)
  have hW : WithSeminorms (topology := τ) (injectiveTensorSeminorm (E := ∀ i, A i) (F := ∀ j, B j)) :=
    injectiveTensor_withSeminorms
  have hc : Continuous[inferInstance, τ] (LinearMap.id : X →ₗ[ℂ] X) := by
    refine @WithSeminorms.continuous_of_continuous_comp ℂ ℂ X X _ _ _ _ _ _ _ _ _ _ τcoord _ τ hW LinearMap.id ?_
    rintro ⟨S, T⟩
    obtain ⟨U, hU⟩ := dualTest_finite_coordinates A S
    obtain ⟨V, hV⟩ := dualTest_finite_coordinates B T
    let Q (i : I) (j : J) : Seminorm ℂ X :=
      (injectiveTensorSeminorm (pullDualTest S (ContinuousLinearMap.single ℂ A i),
        pullDualTest T (ContinuousLinearMap.single ℂ B j))).comp (injectiveTensorCoordinate A B (i, j))
    have hQ (i : I) (j : J) : Continuous (Q i j) := by
      letI : TopologicalSpace (A i ⊗[ℂ] B j) := injectiveTensorTopology (A i) (B j)
      have hcoord : Continuous (injectiveTensorCoordinate A B (i, j)) := by
        change Continuous ((fun z : ∀ p : I × J, A p.1 ⊗[ℂ] B p.2 => z (i, j)) ∘
          injectiveTensorCoordinates A B)
        exact (continuous_apply (i, j)).comp
          (show Continuous[τcoord, injectiveTensorCoordinateTopology A B] (injectiveTensorCoordinates A B) from
            continuous_induced_dom)
      exact (injectiveTensor_withSeminorms.continuous_seminorm _).comp hcoord
    apply Seminorm.continuous_of_le (q := ∑ i ∈ U, ∑ j ∈ V, Q i j)
    · exact Seminorm.continuous_finsetSum fun i _ => Seminorm.continuous_finsetSum fun j _ => hQ i j
    intro z
    change injectiveTensorSeminorm (S, T) z ≤ _
    change _ ≤ FunLike.coeAddMonoidHom _ _ _ (∑ i ∈ U, ∑ j ∈ V, Q i j) z
    simp_rw [map_sum, Finset.sum_apply]
    refine injectiveTensorSeminorm_le S T z (Finset.sum_nonneg fun i _ =>
      Finset.sum_nonneg fun j _ => apply_nonneg (Q i j) z) ?_
    intro φ hφ ψ hψ
    rw [tensorCoordinate_dualPair_sum A B φ ψ (hU φ hφ) (hV ψ hψ)]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => (norm_sum_le _ _).trans ?_)
    exact Finset.sum_le_sum fun j _ => norm_dualPair_le _ _ _ ⟨φ, hφ, rfl⟩ ⟨ψ, hψ, rfl⟩
  have hreverse : τcoord ≤ τ := by
    simpa only [continuous_iff_le_induced, LinearMap.id_coe, induced_id] using hc
  exact @IsInducing.mk _ _ τ (injectiveTensorCoordinateTopology A B) _
    (le_antisymm hle hreverse)

private def coordinateInsert (p : I × J) :
    (A p.1 ⊗[ℂ] B p.2) →ₗ[ℂ] ((∀ i, A i) ⊗[ℂ] (∀ j, B j)) :=
  TensorProduct.map (LinearMap.single ℂ A p.1) (LinearMap.single ℂ B p.2)

omit [∀ i, TopologicalSpace (A i)] [∀ j, TopologicalSpace (B j)] in
private theorem coord_insert_self (p : I × J) (x : A p.1 ⊗[ℂ] B p.2) :
    injectiveTensorCoordinate A B p (coordinateInsert A B p x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    simp [injectiveTensorCoordinate, coordinateInsert, TensorProduct.map_tmul, LinearMap.single_apply]
  | add x y hx hy => simp [hx, hy]

omit [∀ i, TopologicalSpace (A i)] [∀ j, TopologicalSpace (B j)] in
private theorem coord_insert_ne (p q : I × J) (h : p ≠ q) (x : A q.1 ⊗[ℂ] B q.2) :
    injectiveTensorCoordinate A B p (coordinateInsert A B q x) = 0 := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    simp only [injectiveTensorCoordinate, coordinateInsert, TensorProduct.map_tmul,
      LinearMap.proj_apply, LinearMap.single_apply]
    by_cases hp : p.1 = q.1
    · have hq : p.2 ≠ q.2 := fun he => h (Prod.ext hp he)
      rw [Pi.single_eq_of_ne hq, TensorProduct.tmul_zero]
    · rw [Pi.single_eq_of_ne hp, TensorProduct.zero_tmul]
  | add x y hx hy => simp [hx, hy]

private def rebuildTensorCoordinates (U : Finset I) (V : Finset J) :
    (∀ p : I × J, A p.1 ⊗[ℂ] B p.2) →ₗ[ℂ] ((∀ i, A i) ⊗[ℂ] (∀ j, B j)) :=
  ∑ i ∈ U, ∑ j ∈ V, (coordinateInsert A B (i, j)).comp (LinearMap.proj (i, j))

omit [∀ i, TopologicalSpace (A i)] [∀ j, TopologicalSpace (B j)] in
private theorem tensorCoordinates_rebuild (U : Finset I) (V : Finset J)
    (z : ∀ p : I × J, A p.1 ⊗[ℂ] B p.2) (p : I × J) (hp : p.1 ∈ U) (hq : p.2 ∈ V) :
    injectiveTensorCoordinates A B (rebuildTensorCoordinates A B U V z) p = z p := by
  change injectiveTensorCoordinate A B p (rebuildTensorCoordinates A B U V z) = _
  rcases p with ⟨a, b⟩
  simp only [rebuildTensorCoordinates, LinearMap.sum_apply, map_sum, LinearMap.comp_apply, LinearMap.proj_apply]
  rw [Finset.sum_eq_single a]
  · rw [Finset.sum_eq_single b]
    · exact coord_insert_self A B (a, b) (z (a, b))
    · intro j _ hj
      exact coord_insert_ne A B (a, b) (a, j) (fun h => hj (congrArg Prod.snd h).symm) _
    · exact fun h => (h hq).elim
  · intro i _ hi
    exact Finset.sum_eq_zero fun j _ =>
      coord_insert_ne A B (a, b) (i, j) (fun h => hi (congrArg Prod.fst h).symm) _
  · exact fun h => (h hp).elim

private theorem tensorCoordinates_dense :
    @DenseRange _ (injectiveTensorCoordinateTopology A B) _ (injectiveTensorCoordinates A B) := by
  letI (p : I × J) : TopologicalSpace (A p.1 ⊗[ℂ] B p.2) := injectiveTensorTopology (A p.1) (B p.2)
  intro z
  apply mem_closure_iff_nhds.mpr
  intro W hW
  rw [nhds_pi] at hW
  obtain ⟨P, R, hR, hRW⟩ := Filter.mem_pi'.mp hW
  let U := P.image Prod.fst
  let V := P.image Prod.snd
  refine ⟨injectiveTensorCoordinates A B (rebuildTensorCoordinates A B U V z), hRW ?_, mem_range_self _⟩
  intro p hp
  rw [tensorCoordinates_rebuild A B U V z p (Finset.mem_image_of_mem _ hp) (Finset.mem_image_of_mem _ hp)]
  exact mem_of_mem_nhds (hR p)

/-- C.2.3.6(1). The algebraic injective tensor product commutes with finite products. -/
theorem injectiveTensor_finiteProducts [Fintype I] [Fintype J] :
    @IsHomeomorph _ _ (injectiveTensorTopology (∀ i, A i) (∀ j, B j)) (injectiveTensorCoordinateTopology A B)
      (injectiveTensorCoordinates A B) := by
  letI (p : I × J) : TopologicalSpace (A p.1 ⊗[ℂ] B p.2) := injectiveTensorTopology (A p.1) (B p.2)
  letI : TopologicalSpace ((∀ i, A i) ⊗[ℂ] (∀ j, B j)) := injectiveTensorTopology (∀ i, A i) (∀ j, B j)
  have hright : RightInverse (rebuildTensorCoordinates A B Finset.univ Finset.univ) (injectiveTensorCoordinates A B) :=
    fun z => funext fun p => tensorCoordinates_rebuild A B _ _ z p (Finset.mem_univ _) (Finset.mem_univ _)
  have hleft : LeftInverse (rebuildTensorCoordinates A B Finset.univ Finset.univ) (injectiveTensorCoordinates A B) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
      simp only [rebuildTensorCoordinates, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply,
        injectiveTensorCoordinates, LinearMap.pi_apply, injectiveTensorCoordinate, coordinateInsert,
        TensorProduct.map_tmul, LinearMap.proj_apply, LinearMap.single_apply]
      simp_rw [← TensorProduct.tmul_sum]
      rw [← TensorProduct.sum_tmul, Finset.univ_sum_single, Finset.univ_sum_single]
    | add x y hx hy => simp [map_add, hx, hy]
  have h := tensorCoordinates_inducing A B
  exact isHomeomorph_iff_isEmbedding_surjective.mpr ⟨⟨h, hleft.injective⟩, hright.surjective⟩

/-- The coordinate projections on the completed injective tensor product. -/
def completedInjectiveTensorCoordinates :
    (injectiveTensorStructure (∀ i, A i) (∀ j, B j)).Completed →L[ℂ]
      (∀ p : I × J, (injectiveTensorStructure (A p.1) (B p.2)).Completed) := by
  let X := (∀ i, A i) ⊗[ℂ] (∀ j, B j)
  let DX := injectiveTensorStructure (∀ i, A i) (∀ j, B j)
  letI : UniformSpace X := DX.uniformSpace
  letI : IsUniformAddGroup X := DX.uniformGroup
  letI : UniformContinuousConstSMul ℂ X := DX.uniformConstSmul
  apply ContinuousLinearMap.pi
  intro p
  let DY := injectiveTensorStructure (A p.1) (B p.2)
  letI : UniformSpace (A p.1 ⊗[ℂ] B p.2) := DY.uniformSpace
  letI : IsUniformAddGroup (A p.1 ⊗[ℂ] B p.2) := DY.uniformGroup
  letI : UniformContinuousConstSMul ℂ (A p.1 ⊗[ℂ] B p.2) := DY.uniformConstSmul
  let L : X →L[ℂ] (A p.1 ⊗[ℂ] B p.2) := ⟨injectiveTensorCoordinate A B p,
    injectiveTensor_map_continuous (ContinuousLinearMap.proj (R := ℂ) (φ := A) p.1)
      (ContinuousLinearMap.proj (R := ℂ) (φ := B) p.2)⟩
  exact L.completion

/-- C.2.3.6(2). The completed injective tensor commutes with arbitrary products. -/
theorem completedInjectiveTensor_products :
    IsHomeomorph (completedInjectiveTensorCoordinates A B) := by
  let X := (∀ i, A i) ⊗[ℂ] (∀ j, B j)
  let DX := injectiveTensorStructure (∀ i, A i) (∀ j, B j)
  let DY (p : I × J) := injectiveTensorStructure (A p.1) (B p.2)
  letI : UniformSpace X := DX.uniformSpace
  letI : IsUniformAddGroup X := DX.uniformGroup
  letI (p : I × J) : UniformSpace (A p.1 ⊗[ℂ] B p.2) := (DY p).uniformSpace
  letI (p : I × J) : IsUniformAddGroup (A p.1 ⊗[ℂ] B p.2) := (DY p).uniformGroup
  letI : UniformContinuousConstSMul ℂ X := DX.uniformConstSmul
  letI (p : I × J) : UniformContinuousConstSMul ℂ (A p.1 ⊗[ℂ] B p.2) := (DY p).uniformConstSmul
  let c : (∀ p : I × J, A p.1 ⊗[ℂ] B p.2) → (∀ p : I × J, (DY p).Completed) :=
    Pi.map fun p => (DY p).incl
  letI (p : I × J) : CompleteSpace (DY p).Completed :=
    @Completion.completeSpace _ (DY p).uniformSpace
  letI (p : I × J) : T0Space (DY p).Completed :=
    inferInstanceAs (T0Space (Completion (A p.1 ⊗[ℂ] B p.2)))
  have hc : IsUniformInducing c := by
    rw [isUniformInducing_iff, Pi.uniformity, Filter.comap_iInf, Pi.uniformity]
    congr 1
    ext p : 1
    rw [← (Completion.isUniformInducing_coe (A p.1 ⊗[ℂ] B p.2)).comap_uniformity,
      Filter.comap_comap, Filter.comap_comap]
    rfl
  have hd : DenseRange c := DenseRange.piMap fun p => Completion.denseRange_coe
  have hL : IsUniformInducing (injectiveTensorCoordinates A B) :=
    AddMonoidHom.isUniformInducing_of_isInducing
      (f := (injectiveTensorCoordinates A B).toAddMonoidHom) (tensorCoordinates_inducing A B)
  let P : AbstractCompletion X :=
    { space := ∀ p : I × J, (DY p).Completed
      coe := c ∘ injectiveTensorCoordinates A B
      uniformStruct := inferInstance
      complete := inferInstance
      separation := inferInstance
      isUniformInducing := hc.comp hL
      dense := hd.comp (tensorCoordinates_dense A B) hc.uniformContinuous.continuous }
  let u : Completion X ≃ᵤ (∀ p : I × J, (DY p).Completed) := Completion.cPkg.compareEquiv P
  let e := u.toHomeomorph
  have he (x : X) : e (x : Completion X) =
      (completedInjectiveTensorCoordinates A B) (x : Completion X) := by
    have h : e (x : Completion X) = P.coe x := Completion.cPkg.compare_coe P x
    rw [h]
    funext p
    change _ = (ContinuousLinearMap.completion _ : Completion X →L[ℂ] (DY p).Completed) x
    rw [ContinuousLinearMap.completion_apply_coe]
    rfl
  have heq : (e : Completion X → _) = completedInjectiveTensorCoordinates A B :=
    Completion.ext e.continuous (completedInjectiveTensorCoordinates A B).continuous he
  exact heq ▸ e.isHomeomorph

end Products

end

end Masullo
