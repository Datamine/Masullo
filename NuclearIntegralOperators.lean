import NuclearPermanence
import InjectiveTensorNorm
import Mathlib.Analysis.Convex.Gauge
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# Integral local transitions and nuclearity

The proof uses the local transition argument of
`RiemannMasullo/AppC_LCTVS/Sec2b.lean` at
cd84b23dd5e4f741037cf31aee06bc90161c6514 (Apache-2.0).
-/

open Filter Function Set Topology
open scoped NNReal PointwiseConvergenceCLM TensorProduct

namespace Masullo

noncomputable section

open InjectiveTensorTools

universe u v

private def evaluationBilinear {E B F : Type*} [AddCommGroup E] [Module ℂ E]
    [NormedAddCommGroup B] [NormedSpace ℂ B] [AddCommGroup F] [Module ℂ F]
    (T : E →ₗ[ℂ] B) (j : F →ₗ[ℂ] StrongDual ℂ B) : E →ₗ[ℂ] F →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ (fun x y => j y (T x))
    (by intros; simp) (by intros; simp) (by intros; simp) (by intros; simp)

private theorem evaluationBilinear_continuous {E B F : Type*}
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [NormedAddCommGroup B] [NormedSpace ℂ B] [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
    (T : E →L[ℂ] B) (j : F →L[ℂ] StrongDual ℂ B) :
    Continuous (fun z : E × F => evaluationBilinear T.toLinearMap j.toLinearMap z.1 z.2) :=
  (ContinuousLinearMap.apply ℂ (E := B) ℂ).continuous₂.comp
    ((T.continuous.comp continuous_fst).prodMk (j.continuous.comp continuous_snd))

/-- The evaluation form of an operator on the algebraic tensor with the
normed continuous dual of its codomain. -/
def operatorEvaluation {B C : Type*} [NormedAddCommGroup B] [NormedSpace ℂ B]
    [NormedAddCommGroup C] [NormedSpace ℂ C] (T : B →L[ℂ] C) :
    B ⊗[ℂ] StrongDual ℂ C →ₗ[ℂ] ℂ :=
  TensorProduct.lift (evaluationBilinear T.toLinearMap LinearMap.id)

@[simp] theorem operatorEvaluation_tmul {B C : Type*} [NormedAddCommGroup B] [NormedSpace ℂ B]
    [NormedAddCommGroup C] [NormedSpace ℂ C] (T : B →L[ℂ] C) (x : B) (φ : StrongDual ℂ C) :
    operatorEvaluation T (x ⊗ₜ[ℂ] φ) = φ (T x) :=
  TensorProduct.lift.tmul _ _

/-- An integral operator has a continuous evaluation linearization on the
injective tensor product with the strong dual of its codomain. -/
def IsIntegralOperator {B C : Type*} [NormedAddCommGroup B] [NormedSpace ℂ B]
    [NormedAddCommGroup C] [NormedSpace ℂ C] (T : B →L[ℂ] C) : Prop :=
  Continuous[injectiveTensorTopology B (StrongDual ℂ C), _] (operatorEvaluation T)

/-- Precomposing an integral operator by a bounded linear map preserves integrality. -/
theorem IsIntegralOperator.precomp {A B C : Type*}
    [NormedAddCommGroup A] [NormedSpace ℂ A] [NormedAddCommGroup B] [NormedSpace ℂ B]
    [NormedAddCommGroup C] [NormedSpace ℂ C] {T : B →L[ℂ] C}
    (hT : IsIntegralOperator T) (S : A →L[ℂ] B) : IsIntegralOperator (T.comp S) := by
  let D := StrongDual ℂ C
  letI : PolynormableSpace ℂ A := (norm_withSeminorms ℂ A).toPolynormableSpace
  letI : PolynormableSpace ℂ B := (norm_withSeminorms ℂ B).toPolynormableSpace
  letI : PolynormableSpace ℂ D := (norm_withSeminorms ℂ D).toPolynormableSpace
  let idD := ContinuousLinearMap.id ℂ D
  let M := TensorProduct.map S.toLinearMap idD.toLinearMap
  have he : operatorEvaluation (T.comp S) = (operatorEvaluation T).comp M := by
    apply TensorProduct.ext'
    intro x φ
    change operatorEvaluation (T.comp S) (x ⊗ₜ[ℂ] φ) =
      operatorEvaluation T (M (x ⊗ₜ[ℂ] φ))
    dsimp only [M]
    rw [TensorProduct.map_tmul, operatorEvaluation_tmul, operatorEvaluation_tmul]
    rfl
  letI : TopologicalSpace (A ⊗[ℂ] D) := injectiveTensorTopology A D
  letI : TopologicalSpace (B ⊗[ℂ] D) := injectiveTensorTopology B D
  change Continuous (operatorEvaluation (T.comp S))
  rw [he, LinearMap.coe_comp]
  exact hT.comp (injectiveTensor_map_continuous S idD)

/-- Postcomposing an integral operator by a bounded linear map preserves integrality. -/
theorem IsIntegralOperator.postcomp {A B C : Type*}
    [NormedAddCommGroup A] [NormedSpace ℂ A] [NormedAddCommGroup B] [NormedSpace ℂ B]
    [NormedAddCommGroup C] [NormedSpace ℂ C] {T : A →L[ℂ] B}
    (hT : IsIntegralOperator T) (R : B →L[ℂ] C) : IsIntegralOperator (R.comp T) := by
  let DB := StrongDual ℂ B
  let DC := StrongDual ℂ C
  letI : PolynormableSpace ℂ A := (norm_withSeminorms ℂ A).toPolynormableSpace
  letI : PolynormableSpace ℂ DB := (norm_withSeminorms ℂ DB).toPolynormableSpace
  letI : PolynormableSpace ℂ DC := (norm_withSeminorms ℂ DC).toPolynormableSpace
  let idA := ContinuousLinearMap.id ℂ A
  let pull : DC →L[ℂ] DB := (ContinuousLinearMap.compL ℂ B C ℂ).flip R
  let M := TensorProduct.map idA.toLinearMap pull.toLinearMap
  have he : operatorEvaluation (R.comp T) = (operatorEvaluation T).comp M := by
    apply TensorProduct.ext'
    intro x φ
    change operatorEvaluation (R.comp T) (x ⊗ₜ[ℂ] φ) =
      operatorEvaluation T (M (x ⊗ₜ[ℂ] φ))
    dsimp only [M]
    rw [TensorProduct.map_tmul, operatorEvaluation_tmul, operatorEvaluation_tmul]
    rfl
  letI : TopologicalSpace (A ⊗[ℂ] DB) := injectiveTensorTopology A DB
  letI : TopologicalSpace (A ⊗[ℂ] DC) := injectiveTensorTopology A DC
  change Continuous (operatorEvaluation (R.comp T))
  rw [he, LinearMap.coe_comp]
  exact hT.comp (injectiveTensor_map_continuous idA pull)

/-- An integral operator from a complex Hilbert space sends every orthonormal
family to a family with summable squared norms. The proof uses a norming
functional at each image vector as a tensor test. -/
theorem IsIntegralOperator.summable_norm_sq_orthonormal {H B ι : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup B] [NormedSpace ℂ B]
    {T : H →L[ℂ] B} (hT : IsIntegralOperator T) {b : ι → H} (hb : Orthonormal ℂ b) :
    Summable (fun i => ‖T (b i)‖ ^ 2) := by
  classical
  have hn : Continuous[injectiveTensorTopology H (StrongDual ℂ B), _]
      ((normSeminorm ℂ ℂ).comp (operatorEvaluation T)) := by
    letI : TopologicalSpace (H ⊗[ℂ] StrongDual ℂ B) :=
      injectiveTensorTopology H (StrongDual ℂ B)
    exact hT.norm
  obtain ⟨I, hI⟩ := continuous_injectiveTensor_seminorm_domination _ hn
  letI : PolynormableSpace ℂ H := (norm_withSeminorms ℂ H).toPolynormableSpace
  letI : PolynormableSpace ℂ (StrongDual ℂ B) :=
    (norm_withSeminorms ℂ (StrongDual ℂ B)).toPolynormableSpace
  let P := injectiveAsProjectiveTest I
  obtain ⟨A, hA⟩ := continuousSeminorm_le_norm P.first P.first_continuous
  obtain ⟨C, hC⟩ := continuousSeminorm_le_norm P.second P.second_continuous
  refine summable_of_sum_le (fun _ => sq_nonneg _) (c := ((A : ℝ) * C) ^ 2) ?_
  intro s
  let r (i : ι) := ‖T (b i)‖
  let M := ∑ i ∈ s, r i ^ 2
  have hM : 0 ≤ M := Finset.sum_nonneg fun _ _ => sq_nonneg _
  choose ψ hψ hψT using fun i => exists_dual_vector'' ℂ (T (b i))
  let z : H ⊗[ℂ] StrongDual ℂ B := ∑ i ∈ s, (r i : ℂ) • (b i ⊗ₜ[ℂ] ψ i)
  have hval : operatorEvaluation T z = (M : ℂ) := by
    simp only [z, M, map_sum, map_smul, operatorEvaluation_tmul, smul_eq_mul,
      Complex.ofReal_sum, hψT, r, pow_two, Complex.ofReal_mul]
    rfl
  have hz : injectiveTensorSeminorm I z ≤ (A : ℝ) * C * Real.sqrt M := by
    refine injectiveTensorSeminorm_le I.1 I.2 z
      (mul_nonneg (mul_nonneg A.coe_nonneg C.coe_nonneg) (Real.sqrt_nonneg _)) ?_
    intro φ hφ ξ hξ
    let f : StrongDual ℂ H := φ
    have hf : ‖f‖ ≤ A := ContinuousLinearMap.opNorm_le_bound _ A.coe_nonneg
      fun x => (dualTestSeminorm_dom I.1 ⟨φ, hφ⟩ x).trans (hA x)
    let w := (InnerProductSpace.toDual ℂ H).symm f
    have hw : ‖w‖ = ‖f‖ := (InnerProductSpace.toDual ℂ H).symm.norm_map f
    have hBessel : (∑ i ∈ s, ‖φ (b i)‖ ^ 2) ≤ (A : ℝ) ^ 2 := by
      calc
        (∑ i ∈ s, ‖φ (b i)‖ ^ 2) = ∑ i ∈ s, ‖inner ℂ (b i) w‖ ^ 2 := by
          refine Finset.sum_congr rfl fun i _ => ?_
          change ‖f (b i)‖ ^ 2 = _
          rw [← InnerProductSpace.toDual_symm_apply, norm_inner_symm]
        _ ≤ ‖w‖ ^ 2 := hb.sum_inner_products_le w
        _ ≤ (A : ℝ) ^ 2 := by rw [hw]; gcongr
    have hξψ (i : ι) : ‖ξ (ψ i)‖ ≤ C :=
      ((dualTestSeminorm_dom I.2 ⟨ξ, hξ⟩ (ψ i)).trans (hC _)).trans
        (mul_le_of_le_one_right C.coe_nonneg (hψ i))
    calc
      ‖dualPair φ ξ z‖ ≤ ∑ i ∈ s, (r i * ‖φ (b i)‖) * ‖ξ (ψ i)‖ := by
        simp only [z, map_sum, map_smul, dualPair_tmul, smul_eq_mul]
        calc
          _ ≤ ∑ i ∈ s, ‖(r i : ℂ) * (φ (b i) * ξ (ψ i))‖ := norm_sum_le _ _
          _ = _ := by
            simp only [norm_mul, r, Complex.norm_of_nonneg (norm_nonneg (T (b _))), mul_assoc]
      _ ≤ ∑ i ∈ s, (r i * ‖φ (b i)‖) * C := by
        exact Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_left (hξψ i) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ ≤ (A : ℝ) * C * Real.sqrt M := by
        rw [← Finset.sum_mul, mul_right_comm (A : ℝ), mul_comm (A : ℝ)]
        apply mul_le_mul_of_nonneg_right _ C.coe_nonneg
        exact (Real.sum_mul_le_sqrt_mul_sqrt s r (fun i => ‖φ (b i)‖)).trans
          (mul_le_mul_of_nonneg_left (Real.sqrt_le_iff.mpr ⟨A.coe_nonneg, hBessel⟩)
            (Real.sqrt_nonneg _))
  have hle : M ≤ (A : ℝ) * C * Real.sqrt M := by
    have he := hI z
    change ‖operatorEvaluation T z‖ ≤ _ at he
    rw [hval, Complex.norm_of_nonneg hM] at he
    exact he.trans hz
  change M ≤ ((A : ℝ) * C) ^ 2
  have hsqrt := Real.sq_sqrt hM
  by_cases hzero : Real.sqrt M = 0
  · rw [hzero, zero_pow (by decide : (2 : ℕ) ≠ 0)] at hsqrt
    rw [← hsqrt]
    exact sq_nonneg _
  · have hpos : 0 < Real.sqrt M :=
      lt_of_le_of_ne (Real.sqrt_nonneg M) (Ne.symm hzero)
    have hroot : Real.sqrt M ≤ (A : ℝ) * C := by
      apply le_of_mul_le_mul_right _ hpos
      rwa [← pow_two, hsqrt]
    rw [← hsqrt]
    gcongr

/-- The adjoint of an integral map between Hilbert spaces also has
square-summable images of an orthonormal family. -/
theorem IsIntegralOperator.summable_norm_sq_adjoint {G H ι : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {S : G →L[ℂ] H} (hS : IsIntegralOperator S) {b : ι → H} (hb : Orthonormal ℂ b) :
    Summable (fun j => ‖S.adjoint (b j)‖ ^ 2) := by
  obtain ⟨κ, a, _⟩ := exists_hilbertBasis ℂ G
  have hs := hS.summable_norm_sq_orthonormal a.orthonormal
  let c (j : ι) (i : ↥κ) := ‖inner ℂ (b j) (S (a i))‖ ^ 2
  have hc (j : ι) (i : ↥κ) : c j i = ‖inner ℂ (a i) (S.adjoint (b j))‖ ^ 2 := by
    rw [ContinuousLinearMap.adjoint_inner_right, norm_inner_symm]
  have hcol (j : ι) : Summable (c j) := by
    rw [show c j = _ from funext (hc j)]
    exact a.orthonormal.inner_products_summable (x := S.adjoint (b j))
  have hparseval (j : ι) : (∑' i, c j i) = ‖S.adjoint (b j)‖ ^ 2 := by
    rw [← a.repr.norm_map (S.adjoint (b j))]
    simpa only [hc, HilbertBasis.repr_apply_apply, ENNReal.toReal_ofNat, Real.rpow_two] using
      (lp.norm_rpow_eq_tsum (p := 2) (by norm_num) (a.repr (S.adjoint (b j)))).symm
  refine summable_of_sum_le (fun _ => sq_nonneg _) (c := ∑' i, ‖S (a i)‖ ^ 2) ?_
  intro s
  calc
    (∑ j ∈ s, ‖S.adjoint (b j)‖ ^ 2) = ∑ j ∈ s, ∑' i, c j i := by
      simp only [hparseval]
    _ = ∑' i, ∑ j ∈ s, c j i := (Summable.tsum_finsetSum (fun j _ => hcol j)).symm
    _ ≤ ∑' i, ‖S (a i)‖ ^ 2 :=
      (summable_sum (fun j _ => hcol j)).tsum_le_tsum
        (fun i => hb.sum_inner_products_le (S (a i))) hs

/-- Two integral maps through a Hilbert space have a rank-one expansion
whose operator norms are summable, provided the source is Hilbert. -/
theorem IsIntegralOperator.hasSum_rankOne_comp {G H B ι : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B]
    {S : G →L[ℂ] H} {T : H →L[ℂ] B} (hS : IsIntegralOperator S)
    (hT : IsIntegralOperator T) (b : HilbertBasis ι ℂ H) :
    let f := fun i => innerSL ℂ (S.adjoint (b i))
    let v := fun i => T (b i)
    Summable (fun i => ‖f i‖ * ‖v i‖) ∧
      HasSum (fun i => (f i).smulRight (v i)) (T.comp S) := by
  let f (i : ι) := innerSL ℂ (S.adjoint (b i))
  let v (i : ι) := T (b i)
  change Summable (fun i => ‖f i‖ * ‖v i‖) ∧
    HasSum (fun i => (f i).smulRight (v i)) (T.comp S)
  have hf : Summable (fun i => ‖f i‖ ^ 2) := by
    simpa only [f, innerSL_apply_norm] using hS.summable_norm_sq_adjoint b.orthonormal
  have hv : Summable (fun i => ‖v i‖ ^ 2) := hT.summable_norm_sq_orthonormal b.orthonormal
  have hs : Summable (fun i => ‖f i‖ * ‖v i‖) := by
    refine summable_of_sum_le (fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (c := Real.sqrt (∑' i, ‖f i‖ ^ 2) * Real.sqrt (∑' i, ‖v i‖ ^ 2)) ?_
    intro s
    refine (Real.sum_mul_le_sqrt_mul_sqrt s _ _).trans ?_
    gcongr
    · exact hf.sum_le_tsum s (fun _ _ => sq_nonneg _)
    · exact hv.sum_le_tsum s (fun _ _ => sq_nonneg _)
  refine ⟨hs, ?_⟩
  have hop : Summable (fun i => (f i).smulRight (v i)) :=
    hs.of_norm_bounded fun i => ((f i).norm_smulRight_apply (v i)).le
  suffices he : (∑' i, (f i).smulRight (v i)) = T.comp S by
    exact he ▸ hop.hasSum
  ext x
  have hx := (ContinuousLinearMap.apply ℂ B x).hasSum hop.hasSum
  have hb := (b.hasSum_repr (S x)).mapL T
  simp only [map_smul, HilbertBasis.repr_apply_apply] at hb
  apply hx.unique
  simpa only [ContinuousLinearMap.apply_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.comp_apply, f, v, innerSL_apply_apply,
    ContinuousLinearMap.adjoint_inner_left] using hb

private theorem exists_dense_hilbert_domination {E : Type u}
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (hE : NuclearLocallyConvex.{max u v, u} E) (p : Seminorm ℂ E) (hp : Continuous p) :
    ∃ (H : Type (max u v)) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (_ : CompleteSpace H) (a : E →L[ℂ] H), DenseRange a ∧ ∀ x, p x ≤ ‖a x‖ := by
  obtain ⟨K, _, _, _, a, C, hC, hpC⟩ := nuclearLocallyConvex_hilbert_domination hE p hp
  let d := (C : ℂ) • a
  let H := (LinearMap.range d.toLinearMap).topologicalClosure
  let e : E →L[ℂ] H := d.codRestrict H fun x =>
    Submodule.le_topologicalClosure _ (LinearMap.mem_range_self d.toLinearMap x)
  refine ⟨H, inferInstance, inferInstance, inferInstance, e, ?_, ?_⟩
  · intro z
    rw [IsEmbedding.subtypeVal.closure_eq_preimage_closure_image]
    change (z : K) ∈ closure (Subtype.val '' range e)
    rw [← range_comp]
    exact z.property
  · intro x
    change p x ≤ ‖(C : ℂ) • a x‖
    rw [norm_smul, Complex.norm_of_nonneg hC]
    exact hpC x

private theorem localBanach_hilbert_comparison {E H : Type*}
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
    (a : E →L[ℂ] H) (ha : DenseRange a) (p : Seminorm ℂ E) (hp : ∀ x, p x ≤ ‖a x‖) :
    let r := (normSeminorm ℂ H).comp a.toLinearMap
    ∃ (up : LocalBanach r →L[ℂ] H) (down : H →L[ℂ] LocalBanach p),
      (∀ x, up (localBanachDenseMap r x) = a x) ∧
      (∀ x, down (a x) = localBanachDenseMap p x) := by
  let r := (normSeminorm ℂ H).comp a.toLinearMap
  have hUp (x : E) : ‖a x‖ ≤ 1 * ‖localBanachDenseMap r x‖ := by
    rw [one_mul, norm_localBanachDenseMap]
    exact le_rfl
  have hDown (x : E) : ‖localBanachDenseMap p x‖ ≤ 1 * ‖a x‖ := by
    simpa only [one_mul, norm_localBanachDenseMap] using hp x
  exact ⟨a.toLinearMap.extendOfNorm (localBanachDenseMap r),
    (localBanachDenseMap p).extendOfNorm a.toLinearMap,
    LinearMap.extendOfNorm_eq (localBanachDenseMap_dense r) ⟨1, hUp⟩,
    LinearMap.extendOfNorm_eq ha ⟨1, hDown⟩⟩

private theorem continuous_of_injective_bound {X Y : Type*}
    [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]
    (l : X ⊗[ℂ] Y →ₗ[ℂ] ℂ) (I : InjectiveDualTest X × InjectiveDualTest Y)
    (h : ∀ z, ‖l z‖ ≤ injectiveTensorSeminorm I z) :
    Continuous[injectiveTensorTopology X Y, _] l :=
  (continuous_injectiveTensor_iff l).mpr
    ⟨I.1.forms, I.2.forms, I.1.compact, I.2.compact, I.1.equicontinuous, I.2.equicontinuous, h⟩

private def evaluationInOperator {B C : Type*} [NormedAddCommGroup B] [NormedSpace ℂ B]
    [NormedAddCommGroup C] [NormedSpace ℂ C] :
    B ⊗[ℂ] StrongDual ℂ C →ₗ[ℂ] StrongDual ℂ (B →L[ℂ] C) :=
  TensorProduct.lift (LinearMap.mk₂ ℂ (fun x φ => φ.comp (ContinuousLinearMap.apply ℂ C x))
    (by intros; ext; simp) (by intros; ext; simp)
    (by intros; ext; simp) (by intros; ext; simp))

private theorem evaluationInOperator_apply {B C : Type*} [NormedAddCommGroup B] [NormedSpace ℂ B]
    [NormedAddCommGroup C] [NormedSpace ℂ C] (T : B →L[ℂ] C) (z : B ⊗[ℂ] StrongDual ℂ C) :
    evaluationInOperator z T = operatorEvaluation T z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x φ =>
    rw [operatorEvaluation_tmul]
    exact congrArg (fun f : StrongDual ℂ (B →L[ℂ] C) => f T) (TensorProduct.lift.tmul _ _)
  | add x y hx hy => simp [hx, hy]

private theorem operatorEvaluation_rankOne {B C : Type*} [NormedAddCommGroup B] [NormedSpace ℂ B]
    [NormedAddCommGroup C] [NormedSpace ℂ C] (f : StrongDual ℂ B) (w : C)
    (z : B ⊗[ℂ] StrongDual ℂ C) :
    operatorEvaluation (f.smulRight w) z = dualPair (asPointwise f) (asPointwise (ContinuousLinearMap.apply ℂ ℂ w)) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x φ =>
    rw [operatorEvaluation_tmul, dualPair_tmul, ContinuousLinearMap.smulRight_apply, map_smul]
    rfl
  | add x y hx hy => simp [hx, hy]

set_option maxHeartbeats 1200000 in
/-- A rank-one expansion with summable products of factor norms defines an
integral operator. -/
theorem isIntegralOperator_of_rankOne_hasSum {B C ι : Type*}
    [NormedAddCommGroup B] [NormedSpace ℂ B] [NormedAddCommGroup C] [NormedSpace ℂ C]
    {T : B →L[ℂ] C} (f : ι → StrongDual ℂ B) (w : ι → C)
    (hn : Summable (fun i => ‖f i‖ * ‖w i‖))
    (hs : HasSum (fun i => (f i).smulRight (w i)) T) :
    IsIntegralOperator T := by
  let D := StrongDual ℂ C
  let P := injectiveTensorNorm B D
  have hbound (z : B ⊗[ℂ] D) : ‖operatorEvaluation T z‖ ≤ (∑' i, ‖f i‖ * ‖w i‖) * P z := by
    have h := (evaluationInOperator z).hasSum hs
    simp only [evaluationInOperator_apply] at h
    refine h.norm_le_of_bounded (hn.hasSum.mul_right (P z)) fun i => ?_
    rw [operatorEvaluation_rankOne]
    refine (norm_dualPair_le_injectiveTensorNorm (f i) (ContinuousLinearMap.apply ℂ ℂ (w i)) z).trans ?_
    apply mul_le_mul_of_nonneg_right _ (apply_nonneg _ _)
    exact mul_le_mul_of_nonneg_left
      (ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun φ =>
        mul_comm ‖φ‖ ‖w i‖ ▸ φ.le_opNorm (w i)) (norm_nonneg _)
  letI : TopologicalSpace (B ⊗[ℂ] D) := injectiveTensorTopology B D
  letI : IsTopologicalAddGroup (B ⊗[ℂ] D) := injectiveTensor_withSeminorms.topologicalAddGroup
  have hP : Continuous P := injectiveTensor_withSeminorms.continuous_seminorm _
  have hn0 : 0 ≤ ∑' i, ‖f i‖ * ‖w i‖ :=
    tsum_nonneg fun i => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  let c : ℝ≥0 := ⟨_, hn0⟩
  let R : Seminorm ℂ (B ⊗[ℂ] D) := c • P
  have hR : Continuous R := continuous_const.mul hP
  change Continuous (operatorEvaluation T)
  have hnT : Continuous ((normSeminorm ℂ ℂ).comp (operatorEvaluation T)) :=
    Seminorm.continuous_of_le hR
      (show (normSeminorm ℂ ℂ).comp (operatorEvaluation T) ≤ R from hbound)
  apply continuous_of_tendsto_nhds_zero (operatorEvaluation T).toAddMonoidHom
  change Continuous (fun z => ‖operatorEvaluation T z‖) at hnT
  have h := hnT.tendsto' 0 0 (by simp)
  rw [Metric.tendsto_nhds] at h ⊢
  intro ε hε
  change ∀ᶠ z in 𝓝 (0 : B ⊗[ℂ] D), dist (operatorEvaluation T z) 0 < ε
  simpa only [dist_zero_right, Real.norm_of_nonneg (norm_nonneg _)] using h ε hε

set_option maxHeartbeats 1200000 in
/-- Equality against Banach factors suffices to construct the integral
transition for each continuous local seminorm. -/
theorem exists_integralTransition_of_banach_tensor_topologies {E : Type u}
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [PolynormableSpace ℂ E]
    (hE : ∀ (F : Type (max u v)) [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F],
      projectiveTensorTopology E F = injectiveTensorTopology E F)
    (q : Seminorm ℂ E) (hq : Continuous q) :
    ∃ (p : Seminorm ℂ E) (_ : Continuous p) (hqp : q ≤ p),
      IsIntegralOperator (localBanachTransition q p hqp) := by
  letI : IsTopologicalAddGroup E := (PolynormableSpace.withSeminorms ℂ E).topologicalAddGroup
  let Y := StrongDual ℂ (LocalBanach q)
  let F := ULift.{v} Y
  let up : Y →L[ℂ] F := ⟨ULift.moduleEquiv.symm.toLinearMap, continuous_uliftUp⟩
  let down : F →L[ℂ] Y := ⟨ULift.moduleEquiv.toLinearMap, continuous_uliftDown⟩
  letI : PolynormableSpace ℂ Y := (norm_withSeminorms ℂ Y).toPolynormableSpace
  letI : PolynormableSpace ℂ F := (norm_withSeminorms ℂ F).toPolynormableSpace
  let B := evaluationBilinear (localBanachMap q hq).toLinearMap down.toLinearMap
  let l := TensorProduct.lift B
  have hl := continuous_projectiveTensor_lift B (evaluationBilinear_continuous (localBanachMap q hq) down)
  rw [hE F] at hl
  have hln : Continuous[injectiveTensorTopology E F, _] ((normSeminorm ℂ ℂ).comp l) := by
    letI : TopologicalSpace (E ⊗[ℂ] F) := injectiveTensorTopology E F
    exact hl.norm
  obtain ⟨I, hI⟩ := continuous_injectiveTensor_seminorm_domination _ hln
  let P := injectiveAsProjectiveTest I
  let p := q ⊔ P.first
  have hp : Continuous p := hq.sup P.first_continuous
  have hqp : q ≤ p := le_sup_left
  let X := LocalBanach p
  let i := localBanachMap p hp
  letI : PolynormableSpace ℂ X := (norm_withSeminorms ℂ X).toPolynormableSpace
  let T := localBanachTransition q p hqp
  refine ⟨p, hp, hqp, ?_⟩
  let A := seminormPolarTest (normSeminorm ℂ X) continuous_norm
  obtain ⟨C, hC⟩ := continuousSeminorm_le_norm P.second P.second_continuous
  let D := seminormPolarTest (C • normSeminorm ℂ Y) (continuous_const.mul continuous_norm)
  have hi : DenseRange (localBanachDenseMap p) := localBanachDenseMap_dense p
  have hφ (φ : I.1.forms) :
      ∃ ψ ∈ A.forms, pullDual i ψ = φ.val := by
    have hb (x : E) : ‖φ.val x‖ ≤ 1 * ‖localBanachDenseMap p x‖ := by
      rw [one_mul, norm_localBanachDenseMap]
      exact (dualTestSeminorm_dom I.1 φ x).trans ((le_sup_right : P.first ≤ p) x)
    let ψ := φ.val.toLinearMap.extendOfNorm (localBanachDenseMap p)
    refine ⟨ψ, ?_, ?_⟩
    · intro x
      change ‖ψ x‖ ≤ ‖x‖
      simpa only [one_mul] using LinearMap.norm_extendOfNorm_apply_le hi 1 hb x
    · ext x
      exact LinearMap.extendOfNorm_eq hi ⟨1, hb⟩ x
  let M := TensorProduct.map i.toLinearMap down.toLinearMap
  have hM : (operatorEvaluation T).comp M = l := by
    apply TensorProduct.ext'
    intro x y
    change operatorEvaluation T (M (x ⊗ₜ[ℂ] y)) = l (x ⊗ₜ[ℂ] y)
    dsimp only [M]
    rw [TensorProduct.map_tmul, operatorEvaluation_tmul, TensorProduct.lift.tmul]
    change down y (T (localBanachDenseMap p x)) = down y (localBanachDenseMap q x)
    rw [localBanachTransition_denseMap]
  have hb (z : E ⊗[ℂ] F) : ‖operatorEvaluation T (M z)‖ ≤ injectiveTensorSeminorm (A, D) (M z) := by
    change ‖((operatorEvaluation T).comp M) z‖ ≤ _
    rw [hM]
    refine (hI z).trans ?_
    apply injectiveTensorSeminorm_le _ _ _ (apply_nonneg _ _)
    intro φ hφmem ψ hψmem
    obtain ⟨φ', hφ', hφi⟩ := hφ ⟨φ, hφmem⟩
    let ψ' := pullDual up ψ
    have hψ' : ψ' ∈ D.forms := fun y => by
      change ‖ψ (up y)‖ ≤ (C : ℝ) * ‖y‖
      exact (dualTestSeminorm_dom I.2 ⟨ψ, hψmem⟩ (up y)).trans (hC (up y))
    have hψd : pullDual down ψ' = ψ := by ext y; rfl
    have h := norm_dualPair_le A D (M z) hφ' hψ'
    dsimp only [M] at h
    rwa [dualPair_tensorMap, hφi, hψd] at h
  apply continuous_of_injective_bound _ (A, D)
  letI : TopologicalSpace (X ⊗[ℂ] Y) := projectiveTensorTopology X Y
  have hMd : DenseRange M := projectiveTensor_map_denseRange i.toLinearMap down.toLinearMap
    hi (show Surjective down from fun y => ⟨up y, rfl⟩).denseRange
  have he : Continuous (operatorEvaluation T) :=
    continuous_projectiveTensor_lift _ (evaluationBilinear_continuous T (ContinuousLinearMap.id ℂ Y))
  exact fun z => hMd.induction_on z (isClosed_le he.norm
    (projectiveTensor_withSeminorms.continuous_seminorm (injectiveAsProjectiveTest (A, D)))) hb

/-- On a nuclear space, every local seminorm is dominated by a continuous
seminorm for which the induced Banach transition is integral. -/
theorem nuclearLocallyConvex_exists_integralTransition {E : Type u}
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (hE : NuclearLocallyConvex.{max u v, u} E) (q : Seminorm ℂ E) (hq : Continuous q) :
    ∃ (p : Seminorm ℂ E) (_ : Continuous p) (hqp : q ≤ p),
      IsIntegralOperator (localBanachTransition q p hqp) := by
  letI : PolynormableSpace ℂ E := hE.2.1
  refine exists_integralTransition_of_banach_tensor_topologies.{u, v} (fun F _ _ _ => ?_) q hq
  letI : PolynormableSpace ℂ F := (norm_withSeminorms ℂ F).toPolynormableSpace
  exact hE.2.2 F

set_option maxHeartbeats 800000 in
/-- Every continuous seminorm on a nuclear space is dominated by one whose
canonical gauge transition has an absolutely convergent rank-one expansion. -/
theorem nuclearLocallyConvex_exists_rankOneTransition {E : Type u}
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (hE : NuclearLocallyConvex.{max u v, u} E) (q : Seminorm ℂ E) (hq : Continuous q) :
    ∃ (s : Seminorm ℂ E) (_ : Continuous s) (hqs : q ≤ s)
      (ι : Type (max u v)) (f : ι → StrongDual ℂ (LocalBanach s)) (w : ι → LocalBanach q),
      Summable (fun i => ‖f i‖ * ‖w i‖) ∧
        HasSum (fun i => (f i).smulRight (w i)) (localBanachTransition q s hqs) := by
  obtain ⟨p, hp, hqp, hP⟩ := nuclearLocallyConvex_exists_integralTransition hE q hq
  obtain ⟨H, _, _, _, a, ha, hap⟩ := exists_dense_hilbert_domination hE p hp
  let r := (normSeminorm ℂ H).comp a.toLinearMap
  have hr : Continuous r := a.continuous.norm
  obtain ⟨ar, ap, har, hapr⟩ := localBanach_hilbert_comparison a ha p hap
  obtain ⟨t, ht, hrt, hQ⟩ := nuclearLocallyConvex_exists_integralTransition hE r hr
  obtain ⟨G, _, _, _, d, hd, hdt⟩ := exists_dense_hilbert_domination hE t ht
  let s := (normSeminorm ℂ G).comp d.toLinearMap
  obtain ⟨ds, dt, hds, hdts⟩ := localBanach_hilbert_comparison d hd t hdt
  have hqs : q ≤ s := hqp.trans ((show p ≤ r from hap).trans (hrt.trans hdt))
  let T := (localBanachTransition q p hqp).comp ap
  let S := ar.comp ((localBanachTransition r t hrt).comp dt)
  have hT : IsIntegralOperator T := hP.precomp ap
  have hS : IsIntegralOperator S := (hQ.precomp dt).postcomp ar
  obtain ⟨ι, b, _⟩ := exists_hilbertBasis ℂ H
  let f (i : ↥ι) := innerSL ℂ (S.adjoint (b i))
  let w (i : ↥ι) := T (b i)
  have ⟨hprod, hsum⟩ := hS.hasSum_rankOne_comp hT b
  change Summable (fun i => ‖f i‖ * ‖w i‖) at hprod
  change HasSum (fun i => (f i).smulRight (w i)) (T.comp S) at hsum
  have hmatch : (T.comp S).comp ds = localBanachTransition q s hqs := by
    apply DFunLike.coe_injective
    apply (localBanachDenseMap_dense s).equalizer
      ((T.comp S).comp ds).continuous (localBanachTransition q s hqs).continuous
    funext x
    change T (S (ds (localBanachDenseMap s x))) =
      localBanachTransition q s hqs (localBanachDenseMap s x)
    rw [hds, localBanachTransition_denseMap]
    change localBanachTransition q p hqp
      (ap (ar (localBanachTransition r t hrt (dt (d x))))) = _
    rw [hdts, localBanachTransition_denseMap, har, hapr, localBanachTransition_denseMap]
  refine ⟨s, d.continuous.norm, hqs, ↥ι, fun i => (f i).comp ds, w, ?_, ?_⟩
  · refine (hprod.mul_right ‖ds‖).of_norm_bounded fun i => ?_
    rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)), mul_right_comm]
    exact mul_le_mul_of_nonneg_right ((f i).opNorm_comp_le ds) (norm_nonneg _)
  · let J := (ContinuousLinearMap.compL ℂ (LocalBanach s) G (LocalBanach q)).flip ds
    have he (i : ↥ι) : J ((f i).smulRight (w i)) = ((f i).comp ds).smulRight (w i) := by
      ext x
      rfl
    simpa only [he, show J (T.comp S) = localBanachTransition q s hqs from hmatch] using
      J.hasSum hsum

set_option maxHeartbeats 1200000 in
/-- Integral transitions dominating each continuous seminorm imply
nuclearity in the tensor-topology definition. -/
theorem nuclearLocallyConvex_of_integralTransition {E : Type u}
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [PolynormableSpace ℂ E] [T2Space E]
    (h : ∀ (q : Seminorm ℂ E), Continuous q →
      ∃ (p : Seminorm ℂ E) (_ : Continuous p) (hqp : q ≤ p),
        IsIntegralOperator (localBanachTransition q p hqp)) :
    NuclearLocallyConvex.{v, u} E := by
  letI : IsTopologicalAddGroup E := (PolynormableSpace.withSeminorms ℂ E).topologicalAddGroup
  refine ⟨inferInstance, inferInstance, fun F _ _ _ _ _ => ?_⟩
  letI : IsTopologicalAddGroup F := (PolynormableSpace.withSeminorms ℂ F).topologicalAddGroup
  apply tensorTopologies_equal_of_continuous_projectiveTests
  intro P
  let q := P.first
  let s := P.second
  obtain ⟨p, hp, hqp, ht⟩ := h q P.first_continuous
  let X := LocalBanach p
  let Y := StrongDual ℂ (LocalBanach q)
  let T := localBanachTransition q p hqp
  let i := localBanachMap p hp
  have hln : Continuous[injectiveTensorTopology X Y, _] ((normSeminorm ℂ ℂ).comp (operatorEvaluation T)) := by
    letI : TopologicalSpace (X ⊗[ℂ] Y) := injectiveTensorTopology X Y
    exact ht.norm
  obtain ⟨I, hI⟩ := continuous_injectiveTensor_seminorm_domination _ hln
  letI : PolynormableSpace ℂ X := (norm_withSeminorms ℂ X).toPolynormableSpace
  letI : PolynormableSpace ℂ Y := (norm_withSeminorms ℂ Y).toPolynormableSpace
  let U := injectiveAsProjectiveTest I
  obtain ⟨C, hC⟩ := continuousSeminorm_le_norm U.first U.first_continuous
  obtain ⟨D, hD⟩ := continuousSeminorm_le_norm U.second U.second_continuous
  let A := seminormPolarTest (C • p) (continuous_const.mul hp)
  let B := seminormPolarTest (D • s) (continuous_const.mul P.second_continuous)
  let V := LocalBanach P.tensor
  let κ := localBanachDenseMap P.tensor
  let J : F →ₗ[ℂ] E →ₗ[ℂ] V := ((TensorProduct.mk ℂ E F).compr₂ κ).flip
  obtain ⟨d, hde, hdn⟩ := extendBilinearSecond s q J (fun y x => by
    change ‖localBanachDenseMap P.tensor (x ⊗ₜ[ℂ] y)‖ ≤ s y * q x
    rw [norm_localBanachDenseMap, mul_comm]
    exact P.bound x y)
  let dL : F →L[ℂ] (LocalBanach q →L[ℂ] V) := ⟨d, by
    apply continuous_of_tendsto_nhds_zero (G := F) (M := LocalBanach q →L[ℂ] V) d.toAddMonoidHom
    rw [Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [(P.second_continuous.tendsto' 0 0 (map_zero s)).eventually
      (Iio_mem_nhds hε)] with y hy
    rw [dist_zero_right]
    exact (hdn y).trans_lt hy⟩
  have hbound (z : E ⊗[ℂ] F) : P.tensor z ≤ injectiveTensorSeminorm (A, B) z := by
    obtain ⟨g, hg, hgz⟩ := exists_dual_vector'' ℂ (κ z)
    let k : F →L[ℂ] Y :=
      (ContinuousLinearMap.compL ℂ (LocalBanach q) V ℂ g).comp dL
    have hk (y : F) : ‖k y‖ ≤ s y := by
      have hG (x : LocalBanach q) : ‖k y x‖ ≤ s y * ‖x‖ := by
        change ‖g (d y x)‖ ≤ s y * ‖x‖
        calc
          _ ≤ ‖d y x‖ := (g.le_opNorm _).trans
            (mul_le_of_le_one_left (norm_nonneg (d y x)) hg)
          _ ≤ ‖d y‖ * ‖x‖ := (d y).le_opNorm x
          _ ≤ _ := mul_le_mul_of_nonneg_right (hdn y) (norm_nonneg x)
      exact (k y).opNorm_le_bound (apply_nonneg s y) hG
    let M := TensorProduct.map i.toLinearMap k.toLinearMap
    have hM : (operatorEvaluation T).comp M = g.toLinearMap.comp κ := by
      apply TensorProduct.ext'
      intro x y
      change operatorEvaluation T (M (x ⊗ₜ[ℂ] y)) = g (κ (x ⊗ₜ[ℂ] y))
      dsimp only [M]
      rw [TensorProduct.map_tmul, operatorEvaluation_tmul]
      change g (d y (T (localBanachDenseMap p x))) = _
      rw [localBanachTransition_denseMap, hde]
      rfl
    have he : operatorEvaluation T (M z) = (‖κ z‖ : ℂ) :=
      (LinearMap.congr_fun hM z).trans hgz
    calc
      P.tensor z = ‖operatorEvaluation T (M z)‖ := by
        rw [he, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]
        exact (norm_localBanachDenseMap _ _).symm
      _ ≤ injectiveTensorSeminorm I (M z) := hI _
      _ ≤ injectiveTensorSeminorm (A, B) z := by
        apply injectiveTensorSeminorm_le _ _ _ (apply_nonneg _ _)
        intro φ hφ ψ hψ
        have hφ' : pullDual i φ ∈ A.forms := fun x => by
          change ‖φ (i x)‖ ≤ (C : ℝ) * p x
          have hb := (dualTestSeminorm_dom I.1 ⟨φ, hφ⟩ (i x)).trans (hC (i x))
          change ‖φ (i x)‖ ≤ (C : ℝ) * ‖localBanachDenseMap p x‖ at hb
          rwa [norm_localBanachDenseMap] at hb
        have hψ' : pullDual k ψ ∈ B.forms := fun y => by
          change ‖ψ (k y)‖ ≤ (D : ℝ) * s y
          exact ((dualTestSeminorm_dom I.2 ⟨ψ, hψ⟩ (k y)).trans (hD (k y))).trans
            (mul_le_mul_of_nonneg_left (hk y) D.coe_nonneg)
        dsimp only [M]
        rw [dualPair_tensorMap]
        exact norm_dualPair_le A B z hφ' hψ'
  letI : TopologicalSpace (E ⊗[ℂ] F) := injectiveTensorTopology E F
  letI : IsTopologicalAddGroup (E ⊗[ℂ] F) := injectiveTensor_withSeminorms.topologicalAddGroup
  exact Seminorm.continuous_of_le (injectiveTensor_withSeminorms.continuous_seminorm (A, B)) hbound

section Neighborhoods

variable {E : Type u} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [PolynormableSpace ℂ E]

private theorem absorbent_zeroNeighborhood {U : Set E} (hU : U ∈ 𝓝 (0 : E)) :
    Absorbent ℝ U := by
  letI : ContinuousSMul ℂ E := (PolynormableSpace.withSeminorms ℂ E).continuousSMul
  letI : ContinuousSMul ℝ E := IsScalarTower.continuousSMul ℂ
  exact absorbent_nhds_zero hU

/-- The seminorm of a balanced convex neighborhood used to form the
manuscript's local Banach space. -/
def neighborhoodGauge {U : Set E} (hU : U ∈ 𝓝 (0 : E))
    (bU : Balanced ℂ U) (cU : Convex ℝ U) : Seminorm ℂ E :=
  gaugeSeminorm bU cU (absorbent_zeroNeighborhood hU)

private theorem neighborhoodGauge_continuous {U : Set E}
    (hU : U ∈ 𝓝 (0 : E)) (bU : Balanced ℂ U) (cU : Convex ℝ U) :
    Continuous (neighborhoodGauge hU bU cU) := by
  let hW := PolynormableSpace.withSeminorms ℂ E
  letI : IsTopologicalAddGroup E := hW.topologicalAddGroup
  letI : ContinuousSMul ℂ E := hW.continuousSMul
  letI : ContinuousSMul ℝ E := IsScalarTower.continuousSMul ℂ
  exact continuous_gauge cU hU

/-- Inclusion of neighborhoods reverses the order of their gauges. -/
theorem neighborhoodGauge_mono {U V : Set E}
    {hU : U ∈ 𝓝 (0 : E)} {hV : V ∈ 𝓝 (0 : E)}
    {bU : Balanced ℂ U} {bV : Balanced ℂ V} {cU : Convex ℝ U} {cV : Convex ℝ V}
    (h : V ⊆ U) : neighborhoodGauge hU bU cU ≤ neighborhoodGauge hV bV cV :=
  gauge_mono (absorbent_zeroNeighborhood hV) h

private theorem neighborhoodGauge_ball (p : Seminorm ℂ E) (h : p.ball 0 1 ∈ 𝓝 0) :
    neighborhoodGauge h (p.balanced_ball_zero 1) (p.convex_ball 0 1) = p :=
  DFunLike.coe_injective (p.restrictScalars ℝ).gauge_ball

omit [TopologicalSpace E] [PolynormableSpace ℂ E] in
private theorem integralTransition_congr {p q p' q' : Seminorm ℂ E}
    (hq : q = q') (hp : p = p') {h : q ≤ p} {h' : q' ≤ p'} :
    IsIntegralOperator (localBanachTransition q p h) ↔
      IsIntegralOperator (localBanachTransition q' p' h') := by
  subst q'
  subst p'
  rfl

omit [TopologicalSpace E] [PolynormableSpace ℂ E] in
private theorem rankOneTransition_congr {q p p' : Seminorm ℂ E}
    (hp : p = p') {h : q ≤ p} {h' : q ≤ p'} {ι : Type*}
    (hs : ∃ (f : ι → StrongDual ℂ (LocalBanach p)) (w : ι → LocalBanach q),
      Summable (fun i => ‖f i‖ * ‖w i‖) ∧
        HasSum (fun i => (f i).smulRight (w i)) (localBanachTransition q p h)) :
    ∃ (f : ι → StrongDual ℂ (LocalBanach p')) (w : ι → LocalBanach q),
      Summable (fun i => ‖f i‖ * ‖w i‖) ∧
        HasSum (fun i => (f i).smulRight (w i)) (localBanachTransition q p' h') := by
  subst p'
  exact hs

/-- The forward local operator clause of C.2.4.2 on the actual neighborhood
gauges, expressed as an absolutely convergent series in operator norm. -/
theorem nuclearLocallyConvex_exists_rankOneLocalBanach
    (h : NuclearLocallyConvex.{max u v, u} E) (U : Set E) (hU : U ∈ 𝓝 0)
    (bU : Balanced ℂ U) (cU : Convex ℝ U) :
    ∃ (V : Set E) (hV : V ∈ 𝓝 0) (bV : Balanced ℂ V) (cV : Convex ℝ V) (hVU : V ⊆ U),
      let p := neighborhoodGauge hV bV cV
      let q := neighborhoodGauge hU bU cU
      ∃ (ι : Type (max u v)) (f : ι → StrongDual ℂ (LocalBanach p)) (w : ι → LocalBanach q),
        Summable (fun i => ‖f i‖ * ‖w i‖) ∧
          HasSum (fun i => (f i).smulRight (w i))
            (localBanachTransition q p (neighborhoodGauge_mono hVU)) := by
  let q := neighborhoodGauge hU bU cU
  obtain ⟨p, hp, hqp, ι, f, w, hfn, hsum⟩ :=
    nuclearLocallyConvex_exists_rankOneTransition h q (neighborhoodGauge_continuous hU bU cU)
  have hV : p.ball 0 1 ∈ 𝓝 0 := p.ball_mem_nhds hp one_pos
  have hVU : p.ball 0 1 ⊆ U := fun x hx =>
    setOfPred_gauge_lt_one_subset_self cU (mem_of_mem_nhds hU) (absorbent_zeroNeighborhood hU)
      ((hqp x).trans_lt (p.mem_ball_zero.mp hx))
  refine ⟨p.ball 0 1, hV, p.balanced_ball_zero 1, p.convex_ball 0 1, hVU, ?_⟩
  exact ⟨ι, rankOneTransition_congr (neighborhoodGauge_ball p hV).symm
    (h := hqp) ⟨f, w, hfn, hsum⟩⟩

/-- Theorem C.2.4.9. A Hausdorff locally convex space is nuclear exactly
when each balanced convex zero-neighborhood has a smaller such
neighborhood with an integral transition between the gauge completions. -/
theorem nuclearLocallyConvex_iff_integralLocalBanach [T2Space E] :
    NuclearLocallyConvex.{max u v, u} E ↔
    ∀ (U : Set E) (hU : U ∈ 𝓝 0) (bU : Balanced ℂ U) (cU : Convex ℝ U),
      ∃ (V : Set E) (hV : V ∈ 𝓝 0) (bV : Balanced ℂ V) (cV : Convex ℝ V) (hVU : V ⊆ U),
        IsIntegralOperator (localBanachTransition
          (neighborhoodGauge hU bU cU) (neighborhoodGauge hV bV cV) (neighborhoodGauge_mono hVU)) := by
  letI : IsTopologicalAddGroup E := (PolynormableSpace.withSeminorms ℂ E).topologicalAddGroup
  constructor
  · intro h U hU bU cU
    let q := neighborhoodGauge hU bU cU
    obtain ⟨p, hp, hqp, hT⟩ := nuclearLocallyConvex_exists_integralTransition.{u, v}
      h q (neighborhoodGauge_continuous hU bU cU)
    have hV : p.ball 0 1 ∈ 𝓝 0 := p.ball_mem_nhds hp one_pos
    have hVU : p.ball 0 1 ⊆ U := fun x hx =>
      setOfPred_gauge_lt_one_subset_self cU (mem_of_mem_nhds hU) (absorbent_zeroNeighborhood hU)
        ((hqp x).trans_lt (p.mem_ball_zero.mp hx))
    refine ⟨p.ball 0 1, hV, p.balanced_ball_zero 1, p.convex_ball 0 1, hVU, ?_⟩
    exact (integralTransition_congr rfl (neighborhoodGauge_ball p hV)).mpr hT
  · intro h
    apply nuclearLocallyConvex_of_integralTransition
    intro q hq
    have hU : q.ball 0 1 ∈ 𝓝 0 := q.ball_mem_nhds hq one_pos
    obtain ⟨V, hV, bV, cV, hVU, hT⟩ :=
      h (q.ball 0 1) hU (q.balanced_ball_zero 1) (q.convex_ball 0 1)
    refine ⟨neighborhoodGauge hV bV cV, neighborhoodGauge_continuous hV bV cV,
      ?_, ?_⟩
    · simpa only [neighborhoodGauge_ball] using neighborhoodGauge_mono
        (hU := hU) (bU := q.balanced_ball_zero 1) (cU := q.convex_ball 0 1)
        (hV := hV) (bV := bV) (cV := cV) hVU
    · exact (integralTransition_congr (neighborhoodGauge_ball q hU) rfl).mp hT

/-- Equivalence of nuclearity and absolutely convergent rank-one local
transitions on the actual gauge completions. -/
theorem nuclearLocallyConvex_iff_rankOneLocalBanach [T2Space E] :
    NuclearLocallyConvex.{max u v, u} E ↔
    ∀ (U : Set E) (hU : U ∈ 𝓝 0) (bU : Balanced ℂ U) (cU : Convex ℝ U),
      ∃ (V : Set E) (hV : V ∈ 𝓝 0) (bV : Balanced ℂ V) (cV : Convex ℝ V) (hVU : V ⊆ U),
        let p := neighborhoodGauge hV bV cV
        let q := neighborhoodGauge hU bU cU
        ∃ (ι : Type (max u v)) (f : ι → StrongDual ℂ (LocalBanach p)) (w : ι → LocalBanach q),
          Summable (fun i => ‖f i‖ * ‖w i‖) ∧ HasSum (fun i => (f i).smulRight (w i))
            (localBanachTransition q p (neighborhoodGauge_mono hVU)) := by
  refine ⟨fun h => nuclearLocallyConvex_exists_rankOneLocalBanach h, ?_⟩
  intro h
  apply nuclearLocallyConvex_iff_integralLocalBanach.mpr
  intro U hU bU cU
  obtain ⟨V, hV, bV, cV, hVU, ι, f, w, hn, hs⟩ := h U hU bU cU
  exact ⟨V, hV, bV, cV, hVU, isIntegralOperator_of_rankOne_hasSum f w hn hs⟩

end Neighborhoods

end
end Masullo
