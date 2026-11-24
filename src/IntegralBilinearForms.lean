import PositiveRepresentation
import Mathlib.Analysis.LocallyConvex.AbsConvex
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Topology.Algebra.Module.Spaces.PointwiseConvergenceCLM

open Function MeasureTheory Set Topology
open scoped ComplexOrder NNReal PointwiseConvergenceCLM TensorProduct

namespace Masullo

noncomputable section

variable {E F : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
variable [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]

/-- Tensor evaluation on compact sets of continuous forms. The supremum
norm of this map is the corresponding injective tensor seminorm. -/
def tensorPairEvaluation (S : Set (E →Lₚₜ[ℂ] ℂ)) (T : Set (F →Lₚₜ[ℂ] ℂ)) :
    (E ⊗[ℂ] F) →ₗ[ℂ] C(S × T, ℂ) :=
  TensorProduct.lift (LinearMap.mk₂ ℂ
    (fun x y => ⟨fun p => p.1.val x * p.2.val y, by
      exact ((PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) ℂ x).continuous.comp
        (continuous_subtype_val.comp continuous_fst)).mul
        ((PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) ℂ y).continuous.comp
          (continuous_subtype_val.comp continuous_snd))⟩)
    (fun x y z => ContinuousMap.ext fun p => by
      change p.1.val (x + y) * p.2.val z = p.1.val x * p.2.val z + p.1.val y * p.2.val z
      rw [map_add, add_mul])
    (fun c x y => ContinuousMap.ext fun p => by
      change p.1.val (c • x) * p.2.val y = c * (p.1.val x * p.2.val y)
      rw [map_smul, smul_eq_mul, mul_assoc])
    (fun x y z => ContinuousMap.ext fun p => by
      change p.1.val x * p.2.val (y + z) = p.1.val x * p.2.val y + p.1.val x * p.2.val z
      rw [map_add, mul_add])
    (fun c x y => ContinuousMap.ext fun p => by
      change p.1.val x * p.2.val (c • y) = c * (p.1.val x * p.2.val y)
      rw [map_smul, smul_eq_mul, mul_left_comm]))

@[simp] theorem tensorPairEvaluation_tmul
    (S : Set (E →Lₚₜ[ℂ] ℂ)) (T : Set (F →Lₚₜ[ℂ] ℂ)) (x : E) (y : F) (p : S × T) :
    tensorPairEvaluation S T (x ⊗ₜ[ℂ] y) p = p.1.val x * p.2.val y := by
  rw [tensorPairEvaluation, TensorProduct.lift.tmul]
  rfl

private theorem tensor_integral_bound
    (S : Set (E →Lₚₜ[ℂ] ℂ)) (T : Set (F →Lₚₜ[ℂ] ℂ))
    [CompactSpace S] [CompactSpace T] [MeasurableSpace (S × T)] [BorelSpace (S × T)]
    (u : (E ⊗[ℂ] F) →ₗ[ℂ] ℂ) (μ : Measure (S × T)) (hmass : μ univ ≤ 1)
    (he : ∀ x y, u (x ⊗ₜ[ℂ] y) = ∫ p, p.1.val x * p.2.val y ∂μ) (w : E ⊗[ℂ] F) :
    ‖u w‖ ≤ ‖tensorPairEvaluation S T w‖ := by
  let P := tensorPairEvaluation S T
  letI : IsFiniteMeasure μ := ⟨hmass.trans_lt ENNReal.one_lt_top⟩
  have hintegrable (z : E ⊗[ℂ] F) : Integrable (P z) μ :=
    (P z).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hrepr : u w = ∫ p, P w p ∂μ := by
    induction w using TensorProduct.induction_on with
    | zero => simp [P]
    | tmul x y => simpa only [P, tensorPairEvaluation_tmul] using he x y
    | add z z' h₁ h₂ =>
      rw [map_add, h₁, h₂, map_add]
      exact (integral_add (hintegrable z) (hintegrable z')).symm
  rw [hrepr]
  refine (norm_integral_le_of_norm_le_const
    (Filter.Eventually.of_forall (fun p => (P w).norm_coe_le_norm p))).trans ?_
  have hr : μ.real univ ≤ 1 := by
    exact (ENNReal.toReal_le_toReal (hmass.trans_lt ENNReal.one_lt_top).ne ENNReal.one_ne_top).mpr hmass
  calc
    ‖P w‖ * μ.real univ ≤ ‖P w‖ * 1 := mul_le_mul_of_nonneg_left hr (norm_nonneg _)
    _ = _ := mul_one _

/-- The representation uses the Borel measure on the actual product of
the two subspaces of the weak duals. -/
def HasBilinearMeasureRepOn (u : (E ⊗[ℂ] F) →ₗ[ℂ] ℂ)
    (S : Set (E →Lₚₜ[ℂ] ℂ)) (T : Set (F →Lₚₜ[ℂ] ℂ)) : Prop :=
  letI : MeasurableSpace (S × T) := borel _
  ∃ μ : Measure (S × T), μ.Regular ∧ μ univ ≤ 1 ∧
    ∀ x y, u (x ⊗ₜ[ℂ] y) = ∫ p, p.1.val x * p.2.val y ∂μ

/-- For a fixed balanced compact pair of dual sets, the injective
seminorm bound is equivalent to a positive Radon measure representation. -/
theorem integral_bilinear_on_compact_pair
    (S : Set (E →Lₚₜ[ℂ] ℂ)) (T : Set (F →Lₚₜ[ℂ] ℂ))
    (hS : IsCompact S) (hT : IsCompact T) (hneS : S.Nonempty) (hneT : T.Nonempty)
    (hbal : Balanced ℂ S) (u : (E ⊗[ℂ] F) →ₗ[ℂ] ℂ) :
    letI : CompactSpace S := isCompact_iff_compactSpace.mp hS
    letI : CompactSpace T := isCompact_iff_compactSpace.mp hT
    (∀ w, ‖u w‖ ≤ ‖tensorPairEvaluation S T w‖) ↔ HasBilinearMeasureRepOn u S T := by
  letI : CompactSpace S := isCompact_iff_compactSpace.mp hS
  letI : CompactSpace T := isCompact_iff_compactSpace.mp hT
  letI : Nonempty S := hneS.to_subtype
  letI : Nonempty T := hneT.to_subtype
  letI : MeasurableSpace (S × T) := borel _
  letI : BorelSpace (S × T) := ⟨rfl⟩
  let P := tensorPairEvaluation S T
  unfold HasBilinearMeasureRepOn
  constructor
  · intro h
    letI : MeasurableSpace ((S × T) × ComplexUnitDisk) := borel _
    letI : BorelSpace ((S × T) × ComplexUnitDisk) := ⟨rfl⟩
    obtain ⟨ν, hν, hmass, hνeq⟩ := probability_with_disk_of_norm_domination P u h
    letI : ν.Regular := hν
    letI : IsProbabilityMeasure ν := ⟨hmass⟩
    let g (p : (S × T) × ComplexUnitDisk) : S × T :=
      (⟨(p.2 : ℂ) • p.1.1.val,
        hbal.smul_mem (by
          have hd : dist (p.2 : ℂ) 0 ≤ 1 := p.2.property
          rwa [dist_zero_right] at hd)
          p.1.1.property⟩, p.1.2)
    have hg : Continuous g := by
      apply Continuous.prodMk
      · apply Continuous.subtype_mk
        apply PointwiseConvergenceCLM.continuous_of_continuous_eval
        intro x
        change Continuous (fun p : (S × T) × ComplexUnitDisk => (p.2 : ℂ) * p.1.1.val x)
        exact (continuous_subtype_val.comp continuous_snd).smul
          ((PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) ℂ x).continuous.comp
            (continuous_subtype_val.comp (continuous_fst.comp continuous_fst)))
      · exact continuous_snd.comp continuous_fst
    let μ := Measure.map g ν
    letI : μ.InnerRegular := Measure.InnerRegular.map_of_continuous hg
    have hμ : μ.Regular := ⟨fun _ hU => Measure.InnerRegular.innerRegular hU.measurableSet⟩
    have hμm : μ univ = 1 := by
      rw [Measure.map_apply hg.measurable MeasurableSet.univ, preimage_univ, hmass]
    refine ⟨μ, hμ, hμm.le, fun x y => ?_⟩
    rw [hνeq (x ⊗ₜ[ℂ] y)]
    have hc : Continuous (fun p : S × T => p.1.val x * p.2.val y) := by
      simpa only [← tensorPairEvaluation_tmul] using (P (x ⊗ₜ[ℂ] y)).continuous
    rw [integral_map hg.measurable.aemeasurable hc.aestronglyMeasurable]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun p => by
      simp only [P, tensorPairEvaluation_tmul]
      change (p.2 : ℂ) * (p.1.1.val x * p.1.2.val y) =
        ((p.2 : ℂ) * p.1.1.val x) * p.1.2.val y
      exact (mul_assoc _ _ _).symm
  · rintro ⟨μ, -, hmass, he⟩ w
    exact tensor_integral_bound S T u μ hmass he w

section TestingSets

open Filter
open scoped Pointwise

/-- Equicontinuity of a set of linear forms, expressed at zero. -/
def EquicontinuousDualSet (S : Set (E →Lₚₜ[ℂ] ℂ)) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ x in 𝓝 (0 : E), ∀ φ ∈ S, ‖φ x‖ ≤ ε

private theorem weakDual_smul_continuous :
    Continuous (fun p : ℂ × (E →Lₚₜ[ℂ] ℂ) => p.1 • p.2) := by
  apply PointwiseConvergenceCLM.continuous_of_continuous_eval
  intro x
  exact continuous_fst.mul
    ((PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) ℂ x).continuous.comp continuous_snd)

private theorem compact_balancedHull {S : Set (E →Lₚₜ[ℂ] ℂ)} (hS : IsCompact S) :
    IsCompact (balancedHull ℂ S) := by
  have he : balancedHull ℂ S = (fun p : ℂ × (E →Lₚₜ[ℂ] ℂ) => p.1 • p.2) ''
      (Metric.closedBall 0 1 ×ˢ S) := by
    ext φ
    constructor
    · rintro h
      obtain ⟨a, ha, ψ, hψ, rfl⟩ := mem_balancedHull_iff.mp h
      exact ⟨(a, ψ), ⟨by simpa [Metric.mem_closedBall, dist_zero_right] using ha, hψ⟩, rfl⟩
    · rintro ⟨⟨a, ψ⟩, ⟨ha, hψ⟩, rfl⟩
      exact mem_balancedHull_iff.mpr
        ⟨a, by simpa [Metric.mem_closedBall, dist_zero_right] using ha, ψ, hψ, rfl⟩
  rw [he]
  exact ((isCompact_closedBall _ _).prod hS).image weakDual_smul_continuous

private theorem equicontinuous_balancedHull {S : Set (E →Lₚₜ[ℂ] ℂ)} (hS : EquicontinuousDualSet S) :
    EquicontinuousDualSet (balancedHull ℂ S) := by
  intro ε hε
  filter_upwards [hS ε hε] with x hx φ hφ
  obtain ⟨a, ha, ψ, hψ, rfl⟩ := mem_balancedHull_iff.mp hφ
  change ‖a * ψ x‖ ≤ ε
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_right ha (norm_nonneg _)).trans (by simpa using hx ψ hψ)

private theorem tensorPairEvaluation_mono
    {S S' : Set (E →Lₚₜ[ℂ] ℂ)} {T T' : Set (F →Lₚₜ[ℂ] ℂ)}
    [CompactSpace S] [CompactSpace S'] [CompactSpace T] [CompactSpace T']
    (hS : S ⊆ S') (hT : T ⊆ T') (w : E ⊗[ℂ] F) :
    ‖tensorPairEvaluation S T w‖ ≤ ‖tensorPairEvaluation S' T' w‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
  intro p
  let p' : S' × T' := (⟨p.1, hS p.1.property⟩, ⟨p.2, hT p.2.property⟩)
  have he : tensorPairEvaluation S T w p = tensorPairEvaluation S' T' w p' := by
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [p']
    | add x y hx hy => simp [map_add, hx, hy]
  rw [he]
  exact (tensorPairEvaluation S' T' w).norm_coe_le_norm p'

/-- Integral forms are controlled by a single injective seminorm, given by
the supremum on a pair of weakly compact equicontinuous sets. -/
def HasInjectiveTensorBound (u : (E ⊗[ℂ] F) →ₗ[ℂ] ℂ) : Prop :=
  ∃ (S : Set (E →Lₚₜ[ℂ] ℂ)) (T : Set (F →Lₚₜ[ℂ] ℂ))
    (hS : IsCompact S) (hT : IsCompact T),
    EquicontinuousDualSet S ∧ EquicontinuousDualSet T ∧
    (letI : CompactSpace S := isCompact_iff_compactSpace.mp hS
     letI : CompactSpace T := isCompact_iff_compactSpace.mp hT
     ∀ w, ‖u w‖ ≤ ‖tensorPairEvaluation S T w‖)

private theorem equicontinuous_insert_zero {S : Set (E →Lₚₜ[ℂ] ℂ)}
    (hS : EquicontinuousDualSet S) : EquicontinuousDualSet (insert 0 S) := by
  intro ε hε
  filter_upwards [hS ε hε] with x hx φ hφ
  rcases mem_insert_iff.mp hφ with rfl | hφ
  · simpa using hε.le
  · exact hx φ hφ

private theorem equicontinuous_union {S T : Set (E →Lₚₜ[ℂ] ℂ)}
    (hS : EquicontinuousDualSet S) (hT : EquicontinuousDualSet T) :
    EquicontinuousDualSet (S ∪ T) := by
  intro ε hε
  filter_upwards [hS ε hε, hT ε hε] with x hx hy φ hφ
  exact Or.elim hφ (hx φ) (hy φ)

/-- A weakly compact equicontinuous set of linear forms. -/
structure InjectiveDualTest (E : Type*) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] where
  forms : Set (E →Lₚₜ[ℂ] ℂ)
  compact : IsCompact forms
  equicontinuous : EquicontinuousDualSet forms

private def InjectiveDualTest.union (S T : InjectiveDualTest E) : InjectiveDualTest E :=
  ⟨S.forms ∪ T.forms, S.compact.union T.compact, equicontinuous_union S.equicontinuous T.equicontinuous⟩

private def InjectiveDualTest.scale (a : ℂ) (S : InjectiveDualTest E) : InjectiveDualTest E where
  forms := (fun φ => a • φ) '' S.forms
  compact := S.compact.image (weakDual_smul_continuous.comp (continuous_const.prodMk continuous_id))
  equicontinuous := by
    intro ε hε
    by_cases ha : a = 0
    · refine Eventually.of_forall fun x ψ hψ => ?_
      obtain ⟨φ, _, rfl⟩ := hψ
      change ‖a * φ x‖ ≤ ε
      simpa [ha] using hε.le
    · have hn : 0 < ‖a‖ := norm_pos_iff.mpr ha
      filter_upwards [S.equicontinuous (ε / ‖a‖) (div_pos hε hn)] with x hx ψ hψ
      obtain ⟨φ, hφ, rfl⟩ := hψ
      change ‖a * φ x‖ ≤ ε
      rw [norm_mul, mul_comm]
      exact (le_div_iff₀ hn).mp (hx φ hφ)

instance : Nonempty (InjectiveDualTest E) :=
  ⟨⟨∅, isCompact_empty, fun _ _ => Eventually.of_forall fun _ _ h => h.elim⟩⟩

/-- The compact-dual-pair seminorm family for the injective tensor topology. -/
def injectiveTensorSeminorm (I : InjectiveDualTest E × InjectiveDualTest F) :
    Seminorm ℂ (E ⊗[ℂ] F) :=
  letI : CompactSpace I.1.forms := isCompact_iff_compactSpace.mp I.1.compact
  letI : CompactSpace I.2.forms := isCompact_iff_compactSpace.mp I.2.compact
  (normSeminorm ℂ _).comp (tensorPairEvaluation I.1.forms I.2.forms)

/-- The locally convex topology on the algebraic injective tensor product. -/
abbrev injectiveTensorTopology (E F : Type*) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] : TopologicalSpace (E ⊗[ℂ] F) :=
  (SeminormFamily.moduleFilterBasis
    (injectiveTensorSeminorm (E := E) (F := F))).topology

private theorem injectiveTensorSeminorm_mono
    {S T : InjectiveDualTest E × InjectiveDualTest F}
    (h₁ : S.1.forms ⊆ T.1.forms) (h₂ : S.2.forms ⊆ T.2.forms) :
    injectiveTensorSeminorm S ≤ injectiveTensorSeminorm T := by
  letI : CompactSpace S.1.forms := isCompact_iff_compactSpace.mp S.1.compact
  letI : CompactSpace S.2.forms := isCompact_iff_compactSpace.mp S.2.compact
  letI : CompactSpace T.1.forms := isCompact_iff_compactSpace.mp T.1.compact
  letI : CompactSpace T.2.forms := isCompact_iff_compactSpace.mp T.2.compact
  exact tensorPairEvaluation_mono h₁ h₂

private theorem injectiveTensorSeminorm_scale
    (a : ℝ≥0) (I : InjectiveDualTest E × InjectiveDualTest F) :
    a • injectiveTensorSeminorm I ≤ injectiveTensorSeminorm (I.1.scale (a : ℂ), I.2) := by
  intro w
  let S := I.1.forms
  let T := I.2.forms
  let S' := (I.1.scale (a : ℂ)).forms
  letI : CompactSpace S := isCompact_iff_compactSpace.mp I.1.compact
  letI : CompactSpace T := isCompact_iff_compactSpace.mp I.2.compact
  letI : CompactSpace S' := isCompact_iff_compactSpace.mp (I.1.scale (a : ℂ)).compact
  change (a : ℝ) * ‖tensorPairEvaluation S T w‖ ≤ ‖tensorPairEvaluation S' T w‖
  rw [← show ‖(a : ℂ)‖ = (a : ℝ) by simp, ← norm_smul]
  apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
  intro p
  let p' : S' × T := (⟨(a : ℂ) • p.1.val, ⟨p.1.val, p.1.property, rfl⟩⟩, p.2)
  have he : ((a : ℂ) • tensorPairEvaluation S T w) p = tensorPairEvaluation S' T w p' := by
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
      simp only [ContinuousMap.smul_apply, tensorPairEvaluation_tmul, smul_eq_mul]
      exact (mul_assoc _ _ _).symm
    | add x y hx hy =>
      rw [map_add, smul_add, map_add, ContinuousMap.add_apply, ContinuousMap.add_apply, hx, hy]
  rw [he]
  exact (tensorPairEvaluation S' T w).norm_coe_le_norm p'

/-- One compact-dual-pair seminorm dominates any continuous seminorm for the
injective tensor topology. -/
theorem continuous_injectiveTensor_seminorm_domination (p : Seminorm ℂ (E ⊗[ℂ] F))
    (hp : Continuous[injectiveTensorTopology E F, _] p) :
    ∃ I, p ≤ injectiveTensorSeminorm I := by
  letI : TopologicalSpace (E ⊗[ℂ] F) := injectiveTensorTopology E F
  have hW : WithSeminorms (injectiveTensorSeminorm (E := E) (F := F)) := ⟨rfl⟩
  obtain ⟨s, a, -, ha⟩ := Seminorm.bound_of_continuous hW p hp
  have hdom (r : Finset (InjectiveDualTest E × InjectiveDualTest F)) :
      ∃ I, r.sup injectiveTensorSeminorm ≤ injectiveTensorSeminorm I := by
    classical
    induction r using Finset.induction_on with
    | empty => exact ⟨Classical.choice inferInstance, bot_le⟩
    | insert J r hj ih =>
      obtain ⟨I, hI⟩ := ih
      let K := (I.1.union J.1, I.2.union J.2)
      refine ⟨K, ?_⟩
      rw [Finset.sup_insert]
      exact sup_le (injectiveTensorSeminorm_mono subset_union_right subset_union_right)
        (hI.trans (injectiveTensorSeminorm_mono subset_union_left subset_union_left))
  obtain ⟨I, hI⟩ := hdom s
  refine ⟨(I.1.scale (a : ℂ), I.2), fun w => ?_⟩
  have hi := mul_le_mul_of_nonneg_left (hI w) a.coe_nonneg
  exact (ha w).trans (hi.trans (injectiveTensorSeminorm_scale a I w))

/-- Continuity on the injective tensor product is equivalent to domination
by one compact-dual-pair seminorm. -/
theorem continuous_injectiveTensor_iff (u : (E ⊗[ℂ] F) →ₗ[ℂ] ℂ) :
    Continuous[injectiveTensorTopology E F, inferInstance] u ↔ HasInjectiveTensorBound u := by
  letI : TopologicalSpace (E ⊗[ℂ] F) := injectiveTensorTopology E F
  have hW : WithSeminorms (injectiveTensorSeminorm (E := E) (F := F)) := ⟨rfl⟩
  constructor
  · intro hu
    obtain ⟨J, hJ⟩ := continuous_injectiveTensor_seminorm_domination ((normSeminorm ℂ ℂ).comp u) hu.norm
    exact ⟨J.1.forms, J.2.forms, J.1.compact, J.2.compact, J.1.equicontinuous,
      J.2.equicontinuous, hJ⟩
  · rintro ⟨S, T, hS, hT, heS, heT, hb⟩
    let I : InjectiveDualTest E × InjectiveDualTest F := (⟨S, hS, heS⟩, ⟨T, hT, heT⟩)
    apply WithSeminorms.continuous_normedSpace_rng ℂ hW u
    refine ⟨{I}, 1, ?_⟩
    rw [Finset.sup_singleton, one_smul]
    exact fun w => hb w

set_option maxHeartbeats 1300000 in
/-- An integral bilinear form has a positive Radon representation on a
product of compact equicontinuous sets in the two weak duals, and conversely. -/
theorem integral_bilinear_representation (u : (E ⊗[ℂ] F) →ₗ[ℂ] ℂ) :
    HasInjectiveTensorBound u ↔
      ∃ (S : Set (E →Lₚₜ[ℂ] ℂ)) (T : Set (F →Lₚₜ[ℂ] ℂ)),
      IsCompact S ∧ IsCompact T ∧ EquicontinuousDualSet S ∧ EquicontinuousDualSet T ∧
      HasBilinearMeasureRepOn u S T := by
  constructor
  · rintro ⟨S, T, hS, hT, heS, heT, h⟩
    let S' := balancedHull ℂ (insert 0 S)
    let T' := insert 0 T
    have hS' : IsCompact S' := compact_balancedHull (hS.insert 0)
    have hT' : IsCompact T' := hT.insert 0
    have hin : insert 0 S ⊆ S' := by
      intro φ hφ
      change φ ∈ balancedHull ℂ (insert 0 S)
      exact mem_balancedHull_iff.mpr ⟨1, norm_one.le, φ, hφ, one_smul ℂ φ⟩
    have hSS' : S ⊆ S' := fun φ hφ => hin (mem_insert_of_mem 0 hφ)
    have hTT' : T ⊆ T' := subset_insert 0 T
    have hneS' : S'.Nonempty := ⟨0, hin (mem_insert 0 S)⟩
    have hneT' : T'.Nonempty := ⟨0, mem_insert 0 T⟩
    have hbal : Balanced ℂ S' := balancedHull.balanced (𝕜 := ℂ) (E := E →Lₚₜ[ℂ] ℂ) (insert 0 S)
    have heS' := equicontinuous_balancedHull (equicontinuous_insert_zero heS)
    have heT' := equicontinuous_insert_zero heT
    refine ⟨S', T', hS', hT', heS', heT', ?_⟩
    have hAux := (integral_bilinear_on_compact_pair S' T' hS' hT' hneS' hneT' hbal u).mp
    apply hAux
    letI : CompactSpace S := isCompact_iff_compactSpace.mp hS
    letI : CompactSpace T := isCompact_iff_compactSpace.mp hT
    letI : CompactSpace S' := isCompact_iff_compactSpace.mp hS'
    letI : CompactSpace T' := isCompact_iff_compactSpace.mp hT'
    exact fun w => (h w).trans (tensorPairEvaluation_mono hSS' hTT' w)
  · rintro ⟨S, T, hS, hT, heS, heT, hμ⟩
    letI : CompactSpace S := isCompact_iff_compactSpace.mp hS
    letI : CompactSpace T := isCompact_iff_compactSpace.mp hT
    letI : MeasurableSpace (S × T) := borel _
    letI : BorelSpace (S × T) := ⟨rfl⟩
    unfold HasBilinearMeasureRepOn at hμ
    obtain ⟨μ, -, hmass, he⟩ := hμ
    exact ⟨S, T, hS, hT, heS, heT, tensor_integral_bound S T u μ hmass he⟩

/-- C.2.4.8, in the equivalent formulation using the linearization on the
algebraic injective tensor product. -/
theorem continuous_injectiveTensor_iff_radon_representation
    (u : (E ⊗[ℂ] F) →ₗ[ℂ] ℂ) :
    Continuous[injectiveTensorTopology E F, inferInstance] u ↔
      ∃ (S : Set (E →Lₚₜ[ℂ] ℂ)) (T : Set (F →Lₚₜ[ℂ] ℂ)),
      IsCompact S ∧ IsCompact T ∧ EquicontinuousDualSet S ∧ EquicontinuousDualSet T ∧
      HasBilinearMeasureRepOn u S T :=
  (continuous_injectiveTensor_iff u).trans (integral_bilinear_representation u)

end TestingSets

end

end Masullo
