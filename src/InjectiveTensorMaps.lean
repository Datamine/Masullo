import WeakDualNuclear
import Mathlib.Analysis.LocallyConvex.HahnBanach
import Mathlib.LinearAlgebra.Basis.VectorSpace
import TopologicalModuleCompletion
import Mathlib.Topology.UniformSpace.Pi

/-!
# Maps and completions of injective tensor products

The uniform Hahn–Banach extension argument follows
`RiemannMasullo/AppC_LCTVS/Sec2a_part2.lean` at
cd84b23dd5e4f741037cf31aee06bc90161c6514 under Apache-2.0.
-/

open Filter Function Set Topology UniformSpace
open scoped NNReal PointwiseConvergenceCLM TensorProduct Uniformity

namespace Masullo

noncomputable section

open scoped Classical

set_option maxHeartbeats 1800000

variable {X Y X' Y' : Type*}
variable [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
variable [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]
variable [AddCommGroup X'] [Module ℂ X'] [TopologicalSpace X']
variable [AddCommGroup Y'] [Module ℂ Y'] [TopologicalSpace Y']

namespace InjectiveTensorTools

theorem injectiveTensor_withSeminorms :
    letI : TopologicalSpace (X ⊗[ℂ] Y) := injectiveTensorTopology X Y
    WithSeminorms (injectiveTensorSeminorm (E := X) (F := Y)) := by
  letI : TopologicalSpace (X ⊗[ℂ] Y) := injectiveTensorTopology X Y
  exact ⟨rfl⟩

def pullDual (f : X →L[ℂ] X') (φ : X' →Lₚₜ[ℂ] ℂ) : X →Lₚₜ[ℂ] ℂ :=
  PointwiseConvergenceCLM.precomp ℂ f φ

def pullDualTest (S : InjectiveDualTest X') (f : X →L[ℂ] X') : InjectiveDualTest X where
  forms := pullDual f '' S.forms
  compact := S.compact.image (PointwiseConvergenceCLM.precomp ℂ f).continuous
  equicontinuous := by
    intro ε hε
    have h := f.continuous.tendsto' 0 0 f.map_zero
    filter_upwards [h (S.equicontinuous ε hε)] with x hx ψ hψ
    obtain ⟨φ, hφ, rfl⟩ := hψ
    exact hx φ hφ

def dualPair (φ : X →Lₚₜ[ℂ] ℂ) (ψ : Y →Lₚₜ[ℂ] ℂ) :
    X ⊗[ℂ] Y →ₗ[ℂ] ℂ :=
  TensorProduct.lift ((LinearMap.mul ℂ ℂ).compl₁₂ φ.toLinearMap ψ.toLinearMap)

@[simp] theorem dualPair_tmul (φ : X →Lₚₜ[ℂ] ℂ) (ψ : Y →Lₚₜ[ℂ] ℂ)
    (x : X) (y : Y) : dualPair φ ψ (x ⊗ₜ[ℂ] y) = φ x * ψ y := by
  simp [dualPair]
  rfl

theorem dualPair_eq_tensorPairEvaluation
    (S : InjectiveDualTest X) (T : InjectiveDualTest Y)
    (z : X ⊗[ℂ] Y) (φ : S.forms) (ψ : T.forms) :
    dualPair φ.val ψ.val z = tensorPairEvaluation S.forms T.forms z (φ, ψ) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp
  | add x y hx hy => simp [map_add, ContinuousMap.add_apply, hx, hy]

theorem norm_dualPair_le (S : InjectiveDualTest X) (T : InjectiveDualTest Y)
    (z : X ⊗[ℂ] Y) {φ : X →Lₚₜ[ℂ] ℂ} {ψ : Y →Lₚₜ[ℂ] ℂ}
    (hφ : φ ∈ S.forms) (hψ : ψ ∈ T.forms) :
    ‖dualPair φ ψ z‖ ≤ injectiveTensorSeminorm (S, T) z := by
  letI : CompactSpace S.forms := isCompact_iff_compactSpace.mp S.compact
  letI : CompactSpace T.forms := isCompact_iff_compactSpace.mp T.compact
  rw [dualPair_eq_tensorPairEvaluation S T z ⟨φ, hφ⟩ ⟨ψ, hψ⟩]
  exact (tensorPairEvaluation S.forms T.forms z).norm_coe_le_norm _

theorem injectiveTensorSeminorm_le
    (S : InjectiveDualTest X) (T : InjectiveDualTest Y) (z : X ⊗[ℂ] Y) {r : ℝ}
    (hr : 0 ≤ r) (h : ∀ φ ∈ S.forms, ∀ ψ ∈ T.forms, ‖dualPair φ ψ z‖ ≤ r) :
    injectiveTensorSeminorm (S, T) z ≤ r := by
  letI : CompactSpace S.forms := isCompact_iff_compactSpace.mp S.compact
  letI : CompactSpace T.forms := isCompact_iff_compactSpace.mp T.compact
  apply (ContinuousMap.norm_le _ hr).mpr
  rintro ⟨φ, ψ⟩
  rw [← dualPair_eq_tensorPairEvaluation]
  exact h φ.val φ.property ψ.val ψ.property

theorem dualPair_tensorMap (f : X →L[ℂ] X') (g : Y →L[ℂ] Y')
    (φ : X' →Lₚₜ[ℂ] ℂ) (ψ : Y' →Lₚₜ[ℂ] ℂ) (z : X ⊗[ℂ] Y) :
    dualPair φ ψ (TensorProduct.map f.toLinearMap g.toLinearMap z) =
      dualPair (pullDual f φ) (pullDual g ψ) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    rw [TensorProduct.map_tmul, dualPair_tmul, dualPair_tmul]
    rfl
  | add x y hx hy => simp [map_add, hx, hy]

end InjectiveTensorTools

open InjectiveTensorTools

theorem injectiveTensor_map_continuous (f : X →L[ℂ] X') (g : Y →L[ℂ] Y') :
    Continuous[injectiveTensorTopology X Y, injectiveTensorTopology X' Y']
      (TensorProduct.map f.toLinearMap g.toLinearMap) := by
  letI : TopologicalSpace (X ⊗[ℂ] Y) := injectiveTensorTopology X Y
  letI : TopologicalSpace (X' ⊗[ℂ] Y') := injectiveTensorTopology X' Y'
  let L := TensorProduct.map f.toLinearMap g.toLinearMap
  letI : IsTopologicalAddGroup (X ⊗[ℂ] Y) := injectiveTensor_withSeminorms.topologicalAddGroup
  apply (injectiveTensor_withSeminorms.continuous_iff_continuous_comp L).mpr
  rintro ⟨S, T⟩
  let A := pullDualTest S f
  let B := pullDualTest T g
  have h (z : X ⊗[ℂ] Y) : (injectiveTensorSeminorm (S, T)).comp L z ≤
      injectiveTensorSeminorm (A, B) z := by
    apply injectiveTensorSeminorm_le _ _ _ (apply_nonneg _ _)
    intro φ hφ ψ hψ
    rw [dualPair_tensorMap]
    exact norm_dualPair_le A B z ⟨φ, hφ, rfl⟩ ⟨ψ, hψ, rfl⟩
  exact Seminorm.continuous_of_le (injectiveTensor_withSeminorms.continuous_seminorm (A, B)) h

namespace InjectiveTensorTools

theorem seminorm_bound_of_unitBall {V : Type*} [AddCommGroup V] [Module ℂ V]
    (p q : Seminorm ℂ V) (h : ∀ x, q x < 1 → p x ≤ 1) : p ≤ q := by
  intro x
  by_contra! hlt
  obtain ⟨r, hr, hp⟩ := exists_between hlt
  have hr₀ : 0 < r := (apply_nonneg q x).trans_lt hr
  have hnorm : ‖(r : ℂ)⁻¹‖ = r⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg hr₀.le]
  have hx : q ((r : ℂ)⁻¹ • x) < 1 := by
    rwa [map_smul_eq_mul, hnorm, inv_mul_lt_iff₀ hr₀, mul_one]
  have hle := h _ hx
  rw [map_smul_eq_mul, hnorm, inv_mul_le_iff₀ hr₀, mul_one] at hle
  exact (not_lt_of_ge hle) hp

private theorem exists_continuousSeminorm_of_unitBall [PolynormableSpace ℂ X]
    {U : Set X} (hU : U ∈ 𝓝 (0 : X)) :
    ∃ q : Seminorm ℂ X, Continuous q ∧ q.ball 0 1 ⊆ U := by
  let hW := PolynormableSpace.withSeminorms ℂ X
  letI : IsTopologicalAddGroup X := hW.topologicalAddGroup
  obtain ⟨⟨I, r⟩, hr, hIU⟩ := hW.hasBasis_zero_ball.mem_iff.mp hU
  let p := I.sup (fun q : {q : Seminorm ℂ X // Continuous q} => q.val)
  let a : ℝ≥0 := ⟨r⁻¹, inv_nonneg.mpr hr.le⟩
  let q : Seminorm ℂ X := a • p
  have hp : Continuous p := Seminorm.continuous_finsetSup fun p _ => p.property
  refine ⟨q, continuous_const.mul hp, ?_⟩
  intro x hx
  apply hIU
  exact p.mem_ball_zero.mpr
    (by simpa only [inv_mul_lt_iff₀ hr, mul_one] using (show r⁻¹ * p x < 1 from q.mem_ball_zero.mp hx))

theorem extend_form_with_bound [PolynormableSpace ℂ X']
    (f : X →L[ℂ] X') (hf : Injective f) (p : Seminorm ℂ X') (hp : Continuous p)
    (φ : X →Lₚₜ[ℂ] ℂ) (hφ : ∀ x, ‖φ x‖ ≤ p (f x)) :
    ∃ ψ ∈ (seminormPolarTest p hp).forms, pullDual f ψ = φ := by
  letI : IsTopologicalAddGroup X' := (PolynormableSpace.withSeminorms ℂ X').topologicalAddGroup
  let e := LinearEquiv.ofInjective f.toLinearMap hf
  let l := φ.toLinearMap.comp e.symm.toLinearMap
  obtain ⟨ψ, hψ, hle⟩ := Module.Dual.exists_continuous_extension_of_le_seminorm
    f.toLinearMap.range l hp (fun y => by
      change ‖φ (e.symm y)‖ ≤ p y
      have he : f (e.symm y) = (y : X') := congrArg Subtype.val (e.apply_symm_apply y)
      rw [← he]
      exact hφ (e.symm y))
  refine ⟨ψ, hle, ContinuousLinearMap.ext fun x => ?_⟩
  have hx := hψ (e x)
  change ψ (f x) = φ (e.symm (e x)) at hx
  change ψ (f x) = φ x
  simpa only [e.symm_apply_apply] using hx

end InjectiveTensorTools

private theorem extend_dualTest [PolynormableSpace ℂ X']
    (f : X →L[ℂ] X') (hf : IsEmbedding f) (S : InjectiveDualTest X) :
    ∃ T : InjectiveDualTest X', ∀ φ ∈ S.forms, ∃ ψ ∈ T.forms, pullDual f ψ = φ := by
  have hS := S.equicontinuous 1 zero_lt_one
  rw [hf.isInducing.nhds_eq_comap 0, f.map_zero] at hS
  obtain ⟨U, hU, hsub⟩ := mem_comap.mp hS
  obtain ⟨q, hq, hqU⟩ := exists_continuousSeminorm_of_unitBall hU
  refine ⟨seminormPolarTest q hq, fun φ hφ => extend_form_with_bound f hf.injective q hq φ ?_⟩
  apply seminorm_bound_of_unitBall ((normSeminorm ℂ ℂ).comp φ.toLinearMap) (q.comp f.toLinearMap)
  intro x hx
  exact hsub (hqU (q.mem_ball_zero.mpr hx)) φ hφ

/-- Unit tests on pairs of equicontinuous dual sets form a zero-neighborhood basis
for the injective topology (C.2.3.8). The proof adapts the scaled unit tests from
`RiemannMasullo/AppC_LCTVS/Sec2a_part2.lean` at 770033a under Apache-2.0. -/
theorem injectiveTensor_equicontinuous_zero_basis
    [PolynormableSpace ℂ X] [PolynormableSpace ℂ Y] :
    letI : TopologicalSpace (X ⊗[ℂ] Y) := injectiveTensorTopology X Y
    (𝓝 (0 : X ⊗[ℂ] Y)).HasBasis
      (fun AB : Set (X →Lₚₜ[ℂ] ℂ) × Set (Y →Lₚₜ[ℂ] ℂ) =>
        EquicontinuousDualSet AB.1 ∧ EquicontinuousDualSet AB.2)
      (fun AB => {z | ∀ φ ∈ AB.1, ∀ ψ ∈ AB.2, ‖dualPair φ ψ z‖ ≤ 1}) := by
  letI : TopologicalSpace (X ⊗[ℂ] Y) := injectiveTensorTopology X Y
  letI : IsTopologicalAddGroup (X ⊗[ℂ] Y) := injectiveTensor_withSeminorms.topologicalAddGroup
  let p := injectiveTensorSeminorm (E := X) (F := Y)
  refine injectiveTensor_withSeminorms.hasBasis_zero_ball.to_hasBasis' ?_ ?_
  · rintro ⟨s, r⟩ hr
    change 0 < r at hr
    obtain ⟨a, ha, har⟩ := NormedField.exists_norm_lt ℂ hr
    have ha₀ := norm_pos_iff.mp ha
    let A := ⋃ ST ∈ s, (fun φ : X →Lₚₜ[ℂ] ℂ => a⁻¹ • φ) '' ST.1.forms
    let B := ⋃ ST ∈ s, ST.2.forms
    have hA : EquicontinuousDualSet A := by
      intro ε hε
      have he := s.eventually_all.mpr fun ST _ =>
        ST.1.equicontinuous (‖a‖ * ε) (mul_pos ha hε)
      filter_upwards [he] with x hx φ hφ
      obtain ⟨ST, hST, ψ, hψ, rfl⟩ := mem_iUnion₂.mp hφ
      simpa [norm_smul, norm_inv, ← div_eq_inv_mul, div_le_iff₀ ha, mul_comm ε] using
        hx ST hST ψ hψ
    have hB : EquicontinuousDualSet B := by
      intro ε hε
      have he := s.eventually_all.mpr fun ST _ => ST.2.equicontinuous ε hε
      filter_upwards [he] with y hy ψ hψ
      obtain ⟨ST, hST, hψ⟩ := mem_iUnion₂.mp hψ
      exact hy ST hST ψ hψ
    refine ⟨(A, B), ⟨hA, hB⟩, ?_⟩
    intro z hz
    apply (Seminorm.mem_ball_zero _).mpr
    refine (Seminorm.finset_sup_apply_le ha.le fun ST hST => ?_).trans_lt har
    apply injectiveTensorSeminorm_le _ _ _ ha.le
    intro φ hφ ψ hψ
    have he : dualPair φ ψ = a • dualPair (a⁻¹ • φ) ψ := by
      apply TensorProduct.ext'
      intro x y
      simp [smul_apply, ← mul_assoc, ha₀]
    rw [he]
    change ‖a • dualPair (a⁻¹ • φ) ψ z‖ ≤ ‖a‖
    rw [norm_smul]
    exact mul_le_of_le_one_right ha.le
      (hz _ (mem_iUnion₂.mpr ⟨ST, hST, φ, hφ, rfl⟩)
          _ (mem_iUnion₂.mpr ⟨ST, hST, hψ⟩))
  · rintro ⟨A, B⟩ ⟨hA, hB⟩
    obtain ⟨qX, hqX, hX⟩ := exists_continuousSeminorm_of_unitBall (hA 1 one_pos)
    obtain ⟨qY, hqY, hY⟩ := exists_continuousSeminorm_of_unitBall (hB 1 one_pos)
    let S := seminormPolarTest qX hqX
    let T := seminormPolarTest qY hqY
    have hsubA : A ⊆ S.forms := by
      intro φ hφ
      change ∀ x, ‖φ x‖ ≤ qX x
      exact seminorm_bound_of_unitBall ((normSeminorm ℂ ℂ).comp φ.toLinearMap) qX
        (fun x hx => hX (qX.mem_ball_zero.mpr hx) φ hφ)
    have hsubB : B ⊆ T.forms := by
      intro ψ hψ
      change ∀ y, ‖ψ y‖ ≤ qY y
      exact seminorm_bound_of_unitBall ((normSeminorm ℂ ℂ).comp ψ.toLinearMap) qY
        (fun y hy => hY (qY.mem_ball_zero.mpr hy) ψ hψ)
    refine Filter.mem_of_superset
      ((p (S, T)).ball_mem_nhds (injectiveTensor_withSeminorms.continuous_seminorm (S, T)) one_pos)
      ?_
    intro z hz φ hφ ψ hψ
    exact (norm_dualPair_le S T z (hsubA hφ) (hsubB hψ)).trans
      ((p (S, T)).mem_ball_zero.mp hz).le

/-- The algebraic injective tensor of two linear topological embeddings is a
linear topological embedding. -/
theorem injectiveTensor_map_isEmbedding [PolynormableSpace ℂ X'] [PolynormableSpace ℂ Y']
    (f : X →L[ℂ] X') (g : Y →L[ℂ] Y') (hf : IsEmbedding f) (hg : IsEmbedding g) :
    @IsEmbedding _ _ (injectiveTensorTopology X Y) (injectiveTensorTopology X' Y')
      (TensorProduct.map f.toLinearMap g.toLinearMap) := by
  let L := TensorProduct.map f.toLinearMap g.toLinearMap
  let τ := injectiveTensorTopology X Y
  letI : TopologicalSpace (X' ⊗[ℂ] Y') := injectiveTensorTopology X' Y'
  letI : IsTopologicalAddGroup (X' ⊗[ℂ] Y') := injectiveTensor_withSeminorms.topologicalAddGroup
  let τ' := TopologicalSpace.induced L (injectiveTensorTopology X' Y')
  letI : TopologicalSpace (X ⊗[ℂ] Y) := τ'
  letI : IsTopologicalAddGroup (X ⊗[ℂ] Y) := topologicalAddGroup_induced L
  have hle : τ ≤ τ' := continuous_iff_le_induced.mp (injectiveTensor_map_continuous f g)
  have hW : WithSeminorms (topology := τ) (injectiveTensorSeminorm (E := X) (F := Y)) :=
    injectiveTensor_withSeminorms
  have hre : τ' ≤ τ := by
    apply continuous_id_iff_le.mp
    change Continuous[τ', τ] (LinearMap.id : (X ⊗[ℂ] Y) →ₗ[ℂ] (X ⊗[ℂ] Y))
    refine @WithSeminorms.continuous_of_continuous_comp ℂ ℂ _ _ _ _ _ _ _ _ _ _ _ _ τ' _ τ
      hW LinearMap.id ?_
    rintro ⟨S, T⟩
    obtain ⟨S', hS⟩ := extend_dualTest f hf S
    obtain ⟨T', hT⟩ := extend_dualTest g hg T
    let Q := (injectiveTensorSeminorm (S', T')).comp L
    have hQ : Continuous Q :=
      (injectiveTensor_withSeminorms.continuous_seminorm (S', T')).comp continuous_induced_dom
    apply Seminorm.continuous_of_le hQ
    intro z
    apply injectiveTensorSeminorm_le S T z (apply_nonneg Q z)
    intro φ hφ ψ hψ
    obtain ⟨φ', hφ', rfl⟩ := hS φ hφ
    obtain ⟨ψ', hψ', rfl⟩ := hT ψ hψ
    rw [← dualPair_tensorMap]
    exact norm_dualPair_le S' T' _ hφ' hψ'
  have hi := @IsInducing.mk _ _ τ (injectiveTensorTopology X' Y') L (le_antisymm hle hre)
  obtain ⟨l, hl⟩ := f.toLinearMap.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hf.injective)
  obtain ⟨r, hr⟩ := g.toLinearMap.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hg.injective)
  have he : (TensorProduct.map l r).comp L = LinearMap.id := by
    dsimp only [L]
    rw [← TensorProduct.map_comp, hl, hr, TensorProduct.map_id]
  have hleft : LeftInverse (TensorProduct.map l r) L := fun z => DFunLike.congr_fun he z
  have hinj := hleft.injective
  exact @IsEmbedding.mk _ _ τ (injectiveTensorTopology X' Y') L hi hinj

/-- The uniform structure used to complete the injective tensor product. -/
def injectiveTensorStructure (X Y : Type*) [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y] : TopologicalModuleStructure (X ⊗[ℂ] Y) where
  topology := injectiveTensorTopology X Y
  group := by
    letI : TopologicalSpace (X ⊗[ℂ] Y) := injectiveTensorTopology X Y
    exact injectiveTensor_withSeminorms.topologicalAddGroup
  constSmul := by
    letI : TopologicalSpace (X ⊗[ℂ] Y) := injectiveTensorTopology X Y
    letI : ContinuousSMul ℂ (X ⊗[ℂ] Y) := injectiveTensor_withSeminorms.continuousSMul
    infer_instance


/-- The elementary tensor map is jointly continuous for the injective topology. -/
private theorem injectiveTensor_tmul_continuous [PolynormableSpace ℂ X] [PolynormableSpace ℂ Y] :
    Continuous[inferInstance, injectiveTensorTopology X Y]
      (fun p : X × Y => p.1 ⊗ₜ[ℂ] p.2) := by
  letI : IsTopologicalAddGroup X := (PolynormableSpace.withSeminorms ℂ X).topologicalAddGroup
  letI : IsTopologicalAddGroup Y := (PolynormableSpace.withSeminorms ℂ Y).topologicalAddGroup
  exact @Continuous.comp (X × Y) (X ⊗[ℂ] Y) (X ⊗[ℂ] Y) inferInstance
    (projectiveTensorTopology X Y) (injectiveTensorTopology X Y) _
    _ projective_to_injective_continuous continuous_projectiveTensor_tmul

/-- The tensor of two dense maps has dense range in the injective tensor topology. -/
theorem injectiveTensor_map_denseRange [PolynormableSpace ℂ X'] [PolynormableSpace ℂ Y']
    (f : X →L[ℂ] X') (g : Y →L[ℂ] Y') (hf : DenseRange f) (hg : DenseRange g) :
    @DenseRange _ (injectiveTensorTopology X' Y') _ (TensorProduct.map f.toLinearMap g.toLinearMap) := by
  letI : TopologicalSpace (X' ⊗[ℂ] Y') := injectiveTensorTopology X' Y'
  letI : IsTopologicalAddGroup (X' ⊗[ℂ] Y') := injectiveTensor_withSeminorms.topologicalAddGroup
  letI : ContinuousSMul ℂ (X' ⊗[ℂ] Y') := injectiveTensor_withSeminorms.continuousSMul
  let L := TensorProduct.map f.toLinearMap g.toLinearMap
  let C := L.range.topologicalClosure
  have hC : closure (range L) = C := rfl
  intro z
  rw [hC]
  change z ∈ C
  induction z using TensorProduct.induction_on with
  | zero => exact C.zero_mem
  | tmul x y =>
    have hc := injectiveTensor_tmul_continuous (X := X') (Y := Y')
    refine (hf.prodMap hg).induction_on (p := fun p => p.1 ⊗ₜ[ℂ] p.2 ∈ C) (x, y)
      (L.range.isClosed_topologicalClosure.preimage hc) ?_
    rintro ⟨a, b⟩
    exact L.range.le_topologicalClosure ⟨a ⊗ₜ[ℂ] b, TensorProduct.map_tmul _ _ _ _⟩
  | add x y hx hy => exact C.add_mem hx hy

/-- A map on completed injective tensors extends the algebraic tensor of its factor maps. -/
def completedInjectiveTensorMap (f : X →L[ℂ] X') (g : Y →L[ℂ] Y') :
    (injectiveTensorStructure X Y).Completed →L[ℂ] (injectiveTensorStructure X' Y').Completed := by
  let DX := injectiveTensorStructure X Y
  let DY := injectiveTensorStructure X' Y'
  letI : UniformSpace (X ⊗[ℂ] Y) := DX.uniformSpace
  letI : IsUniformAddGroup (X ⊗[ℂ] Y) := DX.uniformGroup
  letI : UniformContinuousConstSMul ℂ (X ⊗[ℂ] Y) := DX.uniformConstSmul
  letI : UniformSpace (X' ⊗[ℂ] Y') := DY.uniformSpace
  letI : IsUniformAddGroup (X' ⊗[ℂ] Y') := DY.uniformGroup
  letI : UniformContinuousConstSMul ℂ (X' ⊗[ℂ] Y') := DY.uniformConstSmul
  let L : (X ⊗[ℂ] Y) →L[ℂ] (X' ⊗[ℂ] Y') :=
    ⟨TensorProduct.map f.toLinearMap g.toLinearMap, injectiveTensor_map_continuous f g⟩
  exact L.completion

private theorem completion_map_isClosedEmbedding {V W : Type*} [UniformSpace V] [UniformSpace W]
    {f : V → W} (hf : IsUniformInducing f) : IsClosedEmbedding (Completion.map f) := by
  let q : V → Completion W := fun x => (f x : Completion W)
  let D := closure (range q)
  let i : V → D := fun x => ⟨q x, subset_closure (mem_range_self x)⟩
  have hi : IsUniformInducing i := (isUniformEmbedding_subtype_val.isUniformInducing.of_comp_iff).mp
    ((Completion.isUniformInducing_coe W).comp hf)
  have hd : DenseRange i := by
    rw [DenseRange, Subtype.dense_iff, ← range_comp]
    exact subset_rfl
  letI : CompleteSpace D := isClosed_closure.completeSpace_coe
  let pkg : AbstractCompletion V :=
    { space := D
      coe := i
      uniformStruct := inferInstance
      complete := inferInstance
      separation := inferInstance
      isUniformInducing := hi
      dense := hd }
  let e : Completion V ≃ᵤ D := Completion.cPkg.compareEquiv pkg
  have he : (Subtype.val : D → Completion W) ∘ e = Completion.map f := by
    apply Completion.ext (continuous_subtype_val.comp e.continuous) Completion.continuous_map
    intro x
    rw [comp_apply, Completion.map_coe hf.uniformContinuous]
    have hx : e (x : Completion V) = i x := Completion.cPkg.compare_coe pkg x
    rw [hx]
  rw [← he]
  exact isClosed_closure.isClosedEmbedding_subtypeVal.comp e.toHomeomorph.isClosedEmbedding

/-- The induced map between completed injective tensors is an embedding. -/
theorem completedInjectiveTensorMap_isClosedEmbedding
    [PolynormableSpace ℂ X'] [PolynormableSpace ℂ Y']
    (f : X →L[ℂ] X') (g : Y →L[ℂ] Y') (hf : IsEmbedding f) (hg : IsEmbedding g) :
    IsClosedEmbedding (completedInjectiveTensorMap f g) := by
  let DX := injectiveTensorStructure X Y
  let DY := injectiveTensorStructure X' Y'
  letI : UniformSpace (X ⊗[ℂ] Y) := DX.uniformSpace
  letI : IsUniformAddGroup (X ⊗[ℂ] Y) := DX.uniformGroup
  letI : UniformSpace (X' ⊗[ℂ] Y') := DY.uniformSpace
  letI : IsUniformAddGroup (X' ⊗[ℂ] Y') := DY.uniformGroup
  exact completion_map_isClosedEmbedding
    (AddMonoidHom.isUniformInducing_of_isInducing
      (f := (TensorProduct.map f.toLinearMap g.toLinearMap).toAddMonoidHom)
      (injectiveTensor_map_isEmbedding f g hf hg).isInducing)

/-- Dense embeddings of both factors induce a topological linear isomorphism
on the completed injective tensors. -/
theorem completedInjectiveTensorMap_isHomeomorph_of_dense
    [PolynormableSpace ℂ X'] [PolynormableSpace ℂ Y']
    (f : X →L[ℂ] X') (g : Y →L[ℂ] Y') (hf : IsEmbedding f) (hg : IsEmbedding g)
    (hfd : DenseRange f) (hgd : DenseRange g) : IsHomeomorph (completedInjectiveTensorMap f g) := by
  let DX := injectiveTensorStructure X Y
  let DY := injectiveTensorStructure X' Y'
  letI : UniformSpace (X ⊗[ℂ] Y) := DX.uniformSpace
  letI : UniformSpace (X' ⊗[ℂ] Y') := DY.uniformSpace
  let L := TensorProduct.map f.toLinearMap g.toLinearMap
  have hL : UniformContinuous L := by
    letI : IsUniformAddGroup (X ⊗[ℂ] Y) := DX.uniformGroup
    letI : IsUniformAddGroup (X' ⊗[ℂ] Y') := DY.uniformGroup
    exact uniformContinuous_of_continuousAt_zero L.toAddMonoidHom
      (injectiveTensor_map_continuous f g).continuousAt
  have hm := completedInjectiveTensorMap_isClosedEmbedding f g hf hg
  have hd : DenseRange (completedInjectiveTensorMap f g) := by
    refine (Completion.denseRange_coe.comp (injectiveTensor_map_denseRange f g hfd hgd)
      (Completion.continuous_coe _)).mono ?_
    rintro _ ⟨x, rfl⟩
    exact ⟨DX.incl x, Completion.map_coe hL x⟩
  exact isHomeomorph_iff_isEmbedding_surjective.mpr
    ⟨hm.isEmbedding, range_eq_univ.mp (hm.isClosed_range.closure_eq ▸ hd.closure_range)⟩

section CompletionSeminorms

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [UniformSpace V] [IsUniformAddGroup V]
variable [UniformContinuousConstSMul ℂ V]

/-- The unique continuous extension of a continuous seminorm to the completion. -/
def completeSeminorm (p : Seminorm ℂ V) (hp : Continuous p) :
    Seminorm ℂ (Completion V) where
  toFun := Completion.extension p
  map_zero' := by
    rw [← Completion.coe_zero, Completion.extension_coe (p.uniformContinuous_of_continuousAt_zero
      hp.continuousAt), map_zero]
  add_le' x y := by
    let h : Completion V → ℝ := Completion.extension p
    have hc : Continuous h := Completion.continuous_extension
    have he (x : V) : h x = p x :=
      Completion.extension_coe (p.uniformContinuous_of_continuousAt_zero hp.continuousAt) x
    refine Completion.denseRange_coe.induction_on₂
      (p := fun x y => h (x + y) ≤ h x + h y) ?_ ?_ x y
    · exact isClosed_le (hc.comp (continuous_fst.add continuous_snd))
        ((hc.comp continuous_fst).add (hc.comp continuous_snd))
    · intro a b
      rw [← Completion.coe_add, he, he, he]
      exact map_add_le_add p a b
  neg' x := by
    let h : Completion V → ℝ := Completion.extension p
    have hc : Continuous h := Completion.continuous_extension
    have he (x : V) : h x = p x :=
      Completion.extension_coe (p.uniformContinuous_of_continuousAt_zero hp.continuousAt) x
    refine Completion.denseRange_coe.induction_on (p := fun x => h (-x) = h x) x ?_ ?_
    · exact isClosed_eq (hc.comp continuous_neg) hc
    · intro a
      rw [← Completion.coe_neg, he, he, map_neg_eq_map]
  smul' c x := by
    let h : Completion V → ℝ := Completion.extension p
    have hc : Continuous h := Completion.continuous_extension
    have he (x : V) : h x = p x :=
      Completion.extension_coe (p.uniformContinuous_of_continuousAt_zero hp.continuousAt) x
    refine Completion.denseRange_coe.induction_on (p := fun x => h (c • x) = ‖c‖ * h x) x ?_ ?_
    · exact isClosed_eq (hc.comp (continuous_const_smul c)) (continuous_const.mul hc)
    · intro a
      rw [← Completion.coe_smul, he, he, map_smul_eq_mul]

theorem completeSeminorm_apply_coe (p : Seminorm ℂ V) (hp : Continuous p) (x : V) :
    completeSeminorm p hp x = p x :=
  Completion.extension_coe (p.uniformContinuous_of_continuousAt_zero hp.continuousAt) x

theorem completeSeminorm_continuous (p : Seminorm ℂ V) (hp : Continuous p) :
    Continuous (completeSeminorm p hp) := Completion.continuous_extension

/-- The continuous extensions of the generating seminorms generate the completion topology. -/
theorem polynormableSpace_completion [PolynormableSpace ℂ V] :
    PolynormableSpace ℂ (Completion V) := by
  let P (p : {q : Seminorm ℂ V // Continuous q}) := completeSeminorm p.val p.property
  apply WithSeminorms.toPolynormableSpace (p := P)
  refine (SeminormFamily.withSeminorms_iff_nhds_eq_iInf _).mpr (le_antisymm ?_ ?_)
  · apply le_iInf
    intro p
    exact tendsto_iff_comap.mp ((completeSeminorm_continuous p.val p.property).tendsto' 0 0 (map_zero _))
  · intro U hU
    obtain ⟨W, ⟨hW, hWc⟩, hWU⟩ := (closed_nhds_basis (0 : Completion V)).mem_iff.mp hU
    obtain ⟨q, hq, hqW⟩ := exists_continuousSeminorm_of_unitBall
      ((Completion.continuous_coe V).tendsto' 0 0 Completion.coe_zero hW)
    let Q := P ⟨q, hq⟩
    have hsub : Q.ball 0 1 ⊆ W := by
      have hQo : IsOpen (Q.ball 0 1) := by
        rw [Seminorm.ball_zero_eq]
        exact isOpen_lt (completeSeminorm_continuous q hq) continuous_const
      refine (Completion.denseRange_coe.subset_closure_image_preimage_of_isOpen hQo).trans ?_
      apply closure_minimal _ hWc
      rintro _ ⟨x, hx, rfl⟩
      apply hqW
      apply q.mem_ball_zero.mpr
      have hx' := Q.mem_ball_zero.mp hx
      rwa [show Q (x : Completion V) = q x from completeSeminorm_apply_coe q hq x] at hx' 
    refine mem_of_superset ((iInf_le (fun p => (𝓝 0).comap (P p)) ⟨q, hq⟩) ?_)
      (hsub.trans hWU)
    rw [Seminorm.ball_zero_eq]
    exact preimage_mem_comap (Iio_mem_nhds zero_lt_one)

/-- The canonical continuous linear map into the separated completion. -/
def completionInclusionL : V →L[ℂ] Completion V where
  toFun := Completion.coe'
  map_add' := Completion.coe_add
  map_smul' := Completion.coe_smul
  cont := Completion.continuous_coe _

/-- The extensions of generating seminorms separate points in the completion. -/
theorem completion_eq_zero_of_generatingSeminorms {ι : Type*}
    (p : SeminormFamily ℂ V ι) (hp : WithSeminorms p) (z : Completion V)
    (hz : ∀ i, completeSeminorm (p i) (hp.continuous_seminorm i) z = 0) : z = 0 := by
  letI : PolynormableSpace ℂ V := hp.toPolynormableSpace
  letI : PolynormableSpace ℂ (Completion V) := polynormableSpace_completion
  letI : T0Space (Completion V) := Completion.t0Space V
  by_contra hne
  obtain ⟨Q, hQ⟩ := (PolynormableSpace.withSeminorms ℂ (Completion V)).separating_of_T1 z hne
  let q : Seminorm ℂ V := Q.val.comp completionInclusionL.toLinearMap
  have hq : Continuous q := Q.property.comp (Completion.continuous_coe V)
  obtain ⟨s, C, _, hC⟩ := Seminorm.bound_of_continuous hp q hq
  let P (w : Completion V) := C • ∑ i ∈ s, completeSeminorm (p i) (hp.continuous_seminorm i) w
  have hP : Continuous P := continuous_const.smul
    (continuous_finsetSum _ (fun i _ => completeSeminorm_continuous (p i) (hp.continuous_seminorm i)))
  have hle : Q.val z ≤ P z := by
    refine Completion.denseRange_coe.induction_on z (isClosed_le Q.property hP) ?_
    intro x
    have hs : (s.sup p) x ≤ ∑ i ∈ s, p i x :=
      Seminorm.finset_sup_apply_le (Finset.sum_nonneg (fun i _ => apply_nonneg (p i) x))
        (fun i hi => Finset.single_le_sum (fun j _ => apply_nonneg (p j) x) hi)
    have hv : P x = C • ∑ i ∈ s, p i x := by
      unfold P
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      exact completeSeminorm_apply_coe (p i) (hp.continuous_seminorm i) x
    rw [hv]
    exact (hC x).trans (smul_le_smul_of_nonneg_left hs zero_le)
  have hzero : P z = 0 := by simp [P, hz]
  exact hQ (le_antisymm (hzero ▸ hle) (apply_nonneg Q.val z))

end CompletionSeminorms

/-- Completing each factor before forming the completed injective tensor
product gives its canonical topological linear isomorphism. -/
theorem completedInjectiveTensor_completionFactors
    {V W : Type*} [AddCommGroup V] [Module ℂ V] [UniformSpace V] [IsUniformAddGroup V]
    [UniformContinuousConstSMul ℂ V] [PolynormableSpace ℂ V] [T2Space V]
    [AddCommGroup W] [Module ℂ W] [UniformSpace W] [IsUniformAddGroup W]
    [UniformContinuousConstSMul ℂ W] [PolynormableSpace ℂ W] [T2Space W] :
    IsHomeomorph (completedInjectiveTensorMap (completionInclusionL (V := V))
      (completionInclusionL (V := W))) := by
  letI : PolynormableSpace ℂ (Completion V) := polynormableSpace_completion
  letI : PolynormableSpace ℂ (Completion W) := polynormableSpace_completion
  exact completedInjectiveTensorMap_isHomeomorph_of_dense _ _
    (Completion.isUniformEmbedding_coe V).isEmbedding (Completion.isUniformEmbedding_coe W).isEmbedding
    Completion.denseRange_coe Completion.denseRange_coe

end

end Masullo
