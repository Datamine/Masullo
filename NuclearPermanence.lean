import InjectiveTensorMaps
import CompactSupportInductiveLimit
import Mathlib.LinearAlgebra.TensorProduct.DirectLimit
import Mathlib.LinearAlgebra.DirectSum.TensorProduct
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-!
# Permanence of nuclear locally convex spaces

The product, Hilbert-space domination, subspace, and quotient arguments adapt
`RiemannMasullo/AppC_LCTVS/Sec2b.lean` at
cd84b23dd5e4f741037cf31aee06bc90161c6514 under Apache-2.0.
-/

open Filter Function MeasureTheory Set Topology
open scoped ComplexOrder DirectSum NNReal PointwiseConvergenceCLM TensorProduct

namespace Masullo
open InjectiveTensorTools

noncomputable section

universe u v w

/-- Nuclearity by equality of the two tensor topologies for every Hausdorff
locally convex second factor, as in Definition C.2.4.1. -/
def NuclearLocallyConvex.{test, carrier} (E : Type carrier)
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] : Prop :=
  T2Space E ∧ PolynormableSpace ℂ E ∧
    ∀ (F : Type test) [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
      [T2Space F] [PolynormableSpace ℂ F],
      projectiveTensorTopology E F = injectiveTensorTopology E F

theorem tensorTopologies_equal_of_continuous_projectiveTests [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [PolynormableSpace ℂ E]
    [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] [PolynormableSpace ℂ F]
    (h : ∀ P : ProjectiveTensorTest E F, Continuous[injectiveTensorTopology E F, _] P.tensor) :
    projectiveTensorTopology E F = injectiveTensorTopology E F := by
  apply le_antisymm
  · have hc := projective_to_injective_continuous (E := E) (F := F)
    simpa only [induced_id] using continuous_iff_le_induced.mp hc
  · letI : TopologicalSpace (E ⊗[ℂ] F) := injectiveTensorTopology E F
    have hc : Continuous[injectiveTensorTopology E F, projectiveTensorTopology E F]
        (id : E ⊗[ℂ] F → E ⊗[ℂ] F) :=
      (@WithSeminorms.continuous_iff_continuous_comp ℂ ℂ (E ⊗[ℂ] F) (E ⊗[ℂ] F)
        _ _ _ _ _ _ _ (RingHom.id ℂ) _ _ (injectiveTensorTopology E F)
        injectiveTensor_withSeminorms.topologicalAddGroup
        (projectiveTensorTopology E F) projectiveTensor_withSeminorms LinearMap.id).mpr h
    simpa only [induced_id] using continuous_iff_le_induced.mp hc

/-- Arbitrary products of nuclear spaces are nuclear. This is the product
clause of Lemma C.2.4.10(2). -/
theorem nuclearLocallyConvex_pi {I : Type w} {X : I → Type u}
    [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)] [∀ i, TopologicalSpace (X i)]
    (hX : ∀ i, NuclearLocallyConvex.{v, u} (X i)) :
    NuclearLocallyConvex.{v, max u w} (∀ i, X i) := by
  classical
  letI : ∀ i, T2Space (X i) := fun i => (hX i).1
  letI : ∀ i, PolynormableSpace ℂ (X i) := fun i => (hX i).2.1
  refine ⟨inferInstance, inferInstance, fun F _ _ _ _ _ => ?_⟩
  let Z := ∀ i, X i
  let proj (i : I) : Z →L[ℂ] X i := ContinuousLinearMap.proj i
  let single (i : I) : X i →L[ℂ] Z := ContinuousLinearMap.single ℂ X i
  let idF := ContinuousLinearMap.id ℂ F
  let M (i : I) : (Z ⊗[ℂ] F) →ₗ[ℂ] Z ⊗[ℂ] F :=
    (TensorProduct.map (single i).toLinearMap idF.toLinearMap).comp
      (TensorProduct.map (proj i).toLinearMap idF.toLinearMap)
  have hM (i : I) : Continuous[injectiveTensorTopology Z F, projectiveTensorTopology Z F] (M i) := by
    have hc := projectiveTensor_map_continuous (single i) idF
    rw [(hX i).2.2 F] at hc
    exact @Continuous.comp _ _ _ (injectiveTensorTopology Z F)
      (injectiveTensorTopology (X i) F) (projectiveTensorTopology Z F) _ _
      hc (injectiveTensor_map_continuous (proj i) idF)
  apply tensorTopologies_equal_of_continuous_projectiveTests
  intro P
  obtain ⟨s, C, _, hs⟩ := Seminorm.bound_of_continuous
    (withSeminorms_pi fun i => PolynormableSpace.withSeminorms ℂ (X i))
    P.first P.first_continuous
  let t := s.image Sigma.fst
  have hqzero (x : Z) (hx : ∀ i ∈ t, x i = 0) : P.first x = 0 := by
    apply le_antisymm _ (apply_nonneg _ _)
    refine (hs x).trans ?_
    rw [smul_apply, ← smul_zero C]
    refine smul_le_smul_of_nonneg_left (Seminorm.finset_sup_apply_le (le_refl 0) ?_) zero_le
    intro j hj
    change j.2.val (x j.1) ≤ 0
    rw [hx _ (Finset.mem_image_of_mem _ hj), map_zero]
  let T := ∑ i ∈ t, M i
  letI : TopologicalSpace (Z ⊗[ℂ] F) := projectiveTensorTopology Z F
  letI : IsTopologicalAddGroup (Z ⊗[ℂ] F) := projectiveTensor_withSeminorms.topologicalAddGroup
  have hT : Continuous[injectiveTensorTopology Z F, projectiveTensorTopology Z F] T := by
    have hsum : Continuous[injectiveTensorTopology Z F, projectiveTensorTopology Z F]
        (fun z => ∑ i ∈ t, M i z) :=
      @continuous_finsetSum _ _ _ (injectiveTensorTopology Z F) (projectiveTensorTopology Z F)
        _ _ (fun i z => M i z) t (fun i _ => hM i)
    exact @Continuous.congr _ _ (injectiveTensorTopology Z F) (projectiveTensorTopology Z F)
      _ _ hsum (fun z => (LinearMap.sum_apply t M z).symm)
  let D := LinearMap.id - T
  have hD (z : Z ⊗[ℂ] F) : P.tensor (D z) = 0 := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
      change P.tensor (x ⊗ₜ[ℂ] y - T (x ⊗ₜ[ℂ] y)) = 0
      simp only [T, M, idF, LinearMap.sum_apply, LinearMap.comp_apply, TensorProduct.map_tmul,
        ContinuousLinearMap.coe_coe, ContinuousLinearMap.id_apply]
      rw [← TensorProduct.sum_tmul, ← TensorProduct.sub_tmul]
      apply le_antisymm ((P.bound _ _).trans_eq ?_) (apply_nonneg _ _)
      rw [hqzero, zero_mul]
      intro i hi
      rw [Pi.sub_apply, Finset.sum_apply, Finset.sum_eq_single_of_mem i hi]
      · change x i - Pi.single i (x i) i = 0
        rw [Pi.single_eq_same, sub_self]
      · intro j _ hji
        exact Pi.single_eq_of_ne hji.symm _
    | add z z' hz hz' =>
      rw [map_add]
      exact le_antisymm ((map_add_le_add P.tensor _ _).trans_eq (by rw [hz, hz', add_zero]))
        (apply_nonneg _ _)
  have hPT : Continuous[injectiveTensorTopology Z F, _] (fun z => P.tensor (T z)) :=
    @Continuous.comp _ _ ℝ (injectiveTensorTopology Z F) (projectiveTensorTopology Z F)
      _ _ _ (projectiveTensor_withSeminorms.continuous_seminorm P) hT
  letI : TopologicalSpace (Z ⊗[ℂ] F) := injectiveTensorTopology Z F
  letI : IsTopologicalAddGroup (Z ⊗[ℂ] F) := injectiveTensor_withSeminorms.topologicalAddGroup
  refine Seminorm.continuous_of_le (q := P.tensor.comp T)
    hPT fun z => ?_
  change P.tensor z ≤ P.tensor (T z)
  have h := map_add_le_add P.tensor (D z) (T z)
  rwa [hD z, zero_add, show D z + T z = z from sub_add_cancel z (T z)] at h

private def evaluationOnCompact {E K : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [TopologicalSpace K] [CompactSpace K]
    (φ : K → E →Lₚₜ[ℂ] ℂ) (hφ : Continuous φ)
    (he : EquicontinuousDualSet (range φ)) : E →L[ℂ] C(K, ℂ) := by
  let L : E →ₗ[ℂ] C(K, ℂ) :=
    { toFun := fun x => ⟨fun k => φ k x,
        (PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) ℂ x).continuous.comp hφ⟩
      map_add' := fun x y => ContinuousMap.ext fun k => by
        change φ k (x + y) = φ k x + φ k y
        exact (φ k).map_add x y
      map_smul' := fun a x => ContinuousMap.ext fun k => by
        change φ k (a • x) = a • φ k x
        exact (φ k).map_smul a x }
  refine ⟨L, continuous_of_tendsto_nhds_zero (G := E) (M := C(K, ℂ)) L.toAddMonoidHom ?_⟩
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [he (ε / 2) (half_pos hε)] with x hx
  rw [dist_zero_right]
  exact ((ContinuousMap.norm_le _ (half_pos hε).le).mpr
    (fun k => hx (φ k) ⟨k, rfl⟩)).trans_lt (half_lt_self hε)

set_option maxHeartbeats 800000 in
/-- Every continuous seminorm on a nuclear space is dominated by a continuous
Hilbert seminorm. The Hilbert space is the L² space of the Radon
measure representing the local Banach evaluation pairing. -/
theorem nuclearLocallyConvex_hilbert_domination {E : Type u}
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (hE : NuclearLocallyConvex.{max u v, u} E)
    (q : Seminorm ℂ E) (hq : Continuous q) :
    ∃ (H : Type (max u v)) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (_ : CompleteSpace H) (a : E →L[ℂ] H) (C : ℝ), 0 ≤ C ∧ ∀ x, q x ≤ C * ‖a x‖ := by
  letI : PolynormableSpace ℂ E := hE.2.1
  letI : IsTopologicalAddGroup E := (PolynormableSpace.withSeminorms ℂ E).topologicalAddGroup
  let Y := ULift.{v} (StrongDual ℂ (LocalBanach q))
  letI : PolynormableSpace ℂ Y := (norm_withSeminorms ℂ Y).toPolynormableSpace
  let j := localBanachMap q hq
  let b : E →ₗ[ℂ] Y →ₗ[ℂ] ℂ := LinearMap.mk₂ ℂ (fun x y => y.down (j x))
    (by intros; simp) (by intros; simp) (by intros; rfl) (by intros; rfl)
  have hb : Continuous (fun z : E × Y => b z.1 z.2) :=
    (ContinuousLinearMap.apply ℂ (E := LocalBanach q) ℂ).continuous₂.comp
      ((j.continuous.comp continuous_fst).prodMk (continuous_uliftDown.comp continuous_snd))
  let l := TensorProduct.lift b
  have hl := continuous_projectiveTensor_lift b hb
  rw [hE.2.2 Y] at hl
  obtain ⟨A, B, hA, hB, heA, heB, hrep⟩ :=
    (continuous_injectiveTensor_iff_radon_representation l).mp hl
  letI : CompactSpace A := isCompact_iff_compactSpace.mp hA
  letI : CompactSpace B := isCompact_iff_compactSpace.mp hB
  letI : MeasurableSpace (A × B) := borel (A × B)
  letI : BorelSpace (A × B) := ⟨rfl⟩
  obtain ⟨μ, _, hμ, hrep⟩ := hrep
  letI : IsFiniteMeasure μ := ⟨hμ.trans_lt ENNReal.one_lt_top⟩
  let J := ContinuousMap.toLp 2 μ ℂ (E := ℂ)
  let f : E →L[ℂ] C(A × B, ℂ) :=
    evaluationOnCompact (fun k => k.1.val) (continuous_subtype_val.comp continuous_fst)
      (fun ε hε => (heA ε hε).mono fun _ hx _ ⟨k, hk⟩ => hk ▸ hx _ k.1.property)
  let g : Y →L[ℂ] C(A × B, ℂ) :=
    evaluationOnCompact (fun k => k.2.val) (continuous_subtype_val.comp continuous_snd)
      (fun ε hε => (heB ε hε).mono fun _ hx _ ⟨k, hk⟩ => hk ▸ hx _ k.2.property)
  refine ⟨Lp ℂ 2 μ, inferInstance, inferInstance, inferInstance, J.comp f, ‖J‖ * ‖g‖,
    by positivity, fun x => ?_⟩
  obtain ⟨y, hy, hyx⟩ := exists_dual_vector'' ℂ (j x)
  let y' : Y := ULift.up y
  have hinner : inner ℂ (J (star (g y'))) (J (f x)) = b x y' := by
    rw [L2.inner_def]
    trans ∫ k : A × B, k.1.val x * k.2.val y' ∂μ
    · refine integral_congr_ae ?_
      filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) μ (star (g y')),
        ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) μ (f x)] with k hk₁ hk₂
      rw [hk₁, hk₂, RCLike.inner_apply, ContinuousMap.star_apply, starRingEnd_apply, star_star]
      dsimp only [f, g, evaluationOnCompact]
      rfl
    · exact (hrep x y').symm
  have hnorm : ‖J (star (g y'))‖ ≤ ‖J‖ * ‖g‖ := by
    have hy' : ‖y'‖ ≤ 1 := hy
    have hg : ‖g y'‖ ≤ ‖g‖ :=
      (g.le_opNorm y').trans (mul_le_of_le_one_right (norm_nonneg g) hy')
    calc
      _ ≤ ‖J‖ * ‖star (g y')‖ := J.le_opNorm _
      _ = ‖J‖ * ‖g y'‖ := by rw [norm_star]
      _ ≤ ‖J‖ * ‖g‖ := mul_le_mul_of_nonneg_left hg (norm_nonneg J)
  have heq : b x y' = (‖j x‖ : ℂ) := hyx
  calc
    q x = ‖b x y'‖ := by
      rw [heq, Complex.norm_of_nonneg (norm_nonneg _)]
      exact (norm_localBanachDenseMap q x).symm
    _ = ‖inner ℂ (J (star (g y'))) (J (f x))‖ := congrArg norm hinner.symm
    _ ≤ ‖J (star (g y'))‖ * ‖J (f x)‖ := norm_inner_le_norm _ _
    _ ≤ _ := mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)

/-- A bilinear map bounded by a product of seminorms extends in its second
variable to that seminorm's local Banach space, with the same bound. -/
theorem extendBilinearSecond {S F V : Type*} [AddCommGroup S] [Module ℂ S]
    [AddCommGroup F] [Module ℂ F] [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
    (p : Seminorm ℂ S) (q : Seminorm ℂ F) (B : S →ₗ[ℂ] F →ₗ[ℂ] V)
    (hB : ∀ x y, ‖B x y‖ ≤ p x * q y) :
    ∃ d : S →ₗ[ℂ] (LocalBanach q →L[ℂ] V),
      (∀ x y, d x (localBanachDenseMap q y) = B x y) ∧ ∀ x, ‖d x‖ ≤ p x := by
  let j := localBanachDenseMap q
  have hd : DenseRange j := localBanachDenseMap_dense q
  have hnorm (x : S) (y : F) : ‖B x y‖ ≤ p x * ‖j y‖ := by
    simpa only [j, norm_localBanachDenseMap] using hB x y
  let L (x : S) := (B x).extendOfNorm j
  have hL (x : S) (y : F) : L x (j y) = B x y :=
    LinearMap.extendOfNorm_eq hd ⟨p x, hnorm x⟩ y
  refine ⟨{
    toFun := L
    map_add' := fun x y => ?_
    map_smul' := fun c x => ?_ }, hL, fun x => ?_⟩
  · apply DFunLike.coe_injective
    apply (L (x + y)).continuous.ext_on hd (L x + L y).continuous
    rintro _ ⟨z, rfl⟩
    rw [hL, add_apply, hL, hL, map_add, LinearMap.add_apply]
  · apply DFunLike.coe_injective
    apply (L (c • x)).continuous.ext_on hd (c • L x).continuous
    rintro _ ⟨z, rfl⟩
    rw [hL, smul_apply, hL, map_smul, LinearMap.smul_apply]
  · exact (L x).opNorm_le_bound (apply_nonneg _ _)
      (LinearMap.norm_extendOfNorm_apply_le hd (p x) (hnorm x))

set_option maxHeartbeats 800000 in
/-- Linear subspaces of nuclear locally convex spaces are nuclear with the
induced topology, including subspaces which are not closed. -/
theorem nuclearLocallyConvex_submodule {E : Type u}
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (hE : NuclearLocallyConvex.{max u v, u} E) (S : Submodule ℂ E) :
    NuclearLocallyConvex.{max u v, u} S := by
  letI : T2Space E := hE.1
  letI : PolynormableSpace ℂ E := hE.2.1
  refine ⟨inferInstance, inferInstance, fun F _ _ _ _ _ => ?_⟩
  apply tensorTopologies_equal_of_continuous_projectiveTests
  intro P
  obtain ⟨q, hq, hqP⟩ := Seminorm.exists_le_comp_of_isInducing
    P.first_continuous (f := S.subtype) .subtypeVal
  obtain ⟨H, nh, ih, ch, a, C, _, ha⟩ := nuclearLocallyConvex_hilbert_domination hE q hq
  letI : NormedAddCommGroup H := nh
  letI : InnerProductSpace ℂ H := ih
  letI : CompleteSpace H := ch
  let i : S →L[ℂ] E := ⟨S.subtype, continuous_subtype_val⟩
  let aS := a.toLinearMap.comp S.subtype
  let K := aS.range.topologicalClosure
  let aK := (Submodule.inclusion aS.range.le_topologicalClosure).comp aS.rangeRestrict
  have hd : DenseRange aK :=
    ((denseRange_inclusion_iff aS.range.le_topologicalClosure).mpr subset_rfl).comp
      aS.surjective_rangeRestrict.denseRange (continuous_inclusion _)
  letI : CompleteSpace K := aS.range.isClosed_topologicalClosure.completeSpace_coe
  let κ := localBanachDenseMap P.tensor
  let B : S →ₗ[ℂ] F →ₗ[ℂ] LocalBanach P.tensor := (TensorProduct.mk ℂ S F).compr₂ κ
  obtain ⟨d, hdcoe, hdn⟩ := extendBilinearSecond P.first P.second B (fun x y => by
    change ‖localBanachDenseMap P.tensor (x ⊗ₜ[ℂ] y)‖ ≤ _
    exact (norm_localBanachDenseMap _ _).le.trans (P.bound x y))
  have hda (x : S) : ‖d x‖ ≤ C * ‖aK x‖ :=
    (hdn x).trans ((hqP x).trans (ha x))
  let dK := d.extendOfNorm aK
  let A := (dK.comp K.orthogonalProjectionOnto).comp a
  have hA (x : S) : A (i x) = d x := by
    change dK (K.orthogonalProjectionOnto (a x)) = d x
    rw [show K.orthogonalProjectionOnto (a x) = aK x from
      K.orthogonalProjectionOnto_mem_subspace_eq_self (aK x)]
    exact LinearMap.extendOfNorm_eq hd ⟨C, hda⟩ x
  letI : IsTopologicalAddGroup F := (PolynormableSpace.withSeminorms ℂ F).topologicalAddGroup
  let j := localBanachMap P.second P.second_continuous
  let b : E →ₗ[ℂ] F →ₗ[ℂ] LocalBanach P.tensor := LinearMap.mk₂ ℂ (fun x y => A x (j y))
    (by intros; simp) (by intros; simp) (by intros; simp) (by intros; simp)
  have hb : Continuous (fun z : E × F => b z.1 z.2) :=
    (A.continuous.comp continuous_fst).clm_apply (j.continuous.comp continuous_snd)
  have hl := continuous_projectiveTensor_lift b hb
  rw [hE.2.2 F] at hl
  let M := TensorProduct.map i.toLinearMap (ContinuousLinearMap.id ℂ F).toLinearMap
  have hκ : (TensorProduct.lift b).comp M = κ := by
    apply TensorProduct.ext'
    intro x y
    change (TensorProduct.lift b) (TensorProduct.map S.subtype LinearMap.id (x ⊗ₜ[ℂ] y)) = _
    rw [TensorProduct.map_tmul, TensorProduct.lift.tmul, LinearMap.id_apply]
    change A (i x) (j y) = κ (x ⊗ₜ[ℂ] y)
    rw [hA, show j y = localBanachDenseMap P.second y from rfl, hdcoe]
    rfl
  have hm := injectiveTensor_map_continuous i (ContinuousLinearMap.id ℂ F)
  have hln : Continuous[injectiveTensorTopology E F, _] (fun x => ‖TensorProduct.lift b x‖) := by
    letI : TopologicalSpace (E ⊗[ℂ] F) := injectiveTensorTopology E F
    exact hl.norm
  have hc : Continuous[injectiveTensorTopology S F, _] (fun x => ‖TensorProduct.lift b (M x)‖) :=
    @Continuous.comp _ _ _ (injectiveTensorTopology S F) (injectiveTensorTopology E F)
      _ _ _ hln hm
  exact (@Continuous.congr _ _ (injectiveTensorTopology S F) _ _ _ hc fun z => by
    change ‖((TensorProduct.lift b).comp M) z‖ = P.tensor z
    rw [hκ]
    exact norm_localBanachDenseMap _ _)

/-- The projective limit is the subspace of compatible families with its
induced topology. Nuclearity holds even on every subspace of the product,
so the conclusion needs no continuity hypothesis on the transition maps. -/
theorem nuclearLocallyConvex_projectiveLimit {I : Type w} [Preorder I] {X : I → Type u}
    [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)] [∀ i, TopologicalSpace (X i)]
    (f : ∀ i j, i ≤ j → X j →ₗ[ℂ] X i)
    (hX : ∀ i, NuclearLocallyConvex.{max u v w, u} (X i)) :
    let L : Submodule ℂ (∀ i, X i) :=
      ⨅ i, ⨅ j, ⨅ h : i ≤ j, LinearMap.ker (LinearMap.proj i - (f i j h).comp (LinearMap.proj j))
    NuclearLocallyConvex.{max u v w, max u w} L := by
  intro L
  exact nuclearLocallyConvex_submodule.{max u w, v} (nuclearLocallyConvex_pi hX) L

/-- The quotient of a complex polynormable space is polynormable. -/
theorem polynormableSpace_complex_quotient {E : Type*}
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [PolynormableSpace ℂ E]
    (S : Submodule ℂ E) : PolynormableSpace ℂ (E ⧸ S) := by
  let hW := PolynormableSpace.withSeminorms ℂ E
  letI : IsTopologicalAddGroup E := hW.topologicalAddGroup
  letI : ContinuousSMul ℂ E := hW.continuousSMul
  letI : Module ℝ E := Module.restrictScalars ℝ ℂ E
  letI : Module ℝ (E ⧸ S) := Module.restrictScalars ℝ ℂ (E ⧸ S)
  letI : IsScalarTower ℝ ℂ E := IsScalarTower.restrictScalars ℝ ℂ E
  letI : IsScalarTower ℝ ℂ (E ⧸ S) := IsScalarTower.restrictScalars ℝ ℂ (E ⧸ S)
  letI : LocallyConvexSpace ℝ E := hW.toLocallyConvexSpace
  letI : LocallyConvexSpace ℂ (E ⧸ S) := by
    apply LocallyConvexSpace.ofBasisZero ℂ (E ⧸ S) (fun s : Set E => S.mkQ '' s)
      (fun s => s ∈ 𝓝 0 ∧ Convex ℝ s)
    · rw [← show Filter.map S.mkQ (𝓝 (0 : E)) = 𝓝 0 by
        simpa only [map_zero] using S.isOpenQuotientMap_mkQ.map_nhds_eq 0]
      exact (LocallyConvexSpace.convex_basis_zero ℝ E).map S.mkQ
    · intro s hs
      exact convex_of_nonneg_surjective_algebraMap ℂ
        (fun _ hz => RCLike.nonneg_iff_exists_ofReal.mp hz)
        (hs.2.linear_image (S.mkQ.restrictScalars ℝ))
  letI : ContinuousSMul ℝ (E ⧸ S) := IsScalarTower.continuousSMul ℂ
  infer_instance

private theorem quotientTensorSeminorm_le_projection {E H F : Type*}
    [AddCommGroup E] [Module ℂ E]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] [PolynormableSpace ℂ F]
    (S : Submodule ℂ E) (a : E →ₗ[ℂ] H) (r : Seminorm ℂ ((E ⧸ S) ⊗[ℂ] F))
    (W : InjectiveDualTest H) (V : InjectiveDualTest F)
    (h : ∀ z, r (TensorProduct.map S.mkQ LinearMap.id z) ≤
      injectiveTensorSeminorm (W, V) (TensorProduct.map a LinearMap.id z)) :
    let K := (S.map a).topologicalClosure
    letI : CompleteSpace K := (S.map a).isClosed_topologicalClosure.completeSpace_coe
    ∀ z, r (TensorProduct.map S.mkQ LinearMap.id z) ≤ injectiveTensorSeminorm (W, V)
        (TensorProduct.map (Kᗮ.starProjection.toLinearMap.comp a) LinearMap.id z) := by
  intro K z
  letI : CompleteSpace K := (S.map a).isClosed_topologicalClosure.completeSpace_coe
  letI : PolynormableSpace ℂ H := (norm_withSeminorms ℂ H).toPolynormableSpace
  letI : IsTopologicalAddGroup F := (PolynormableSpace.withSeminorms ℂ F).topologicalAddGroup
  let T : E ⊗[ℂ] F →ₗ[ℂ] (E ⧸ S) ⊗[ℂ] F := TensorProduct.map S.mkQ LinearMap.id
  let A : E ⊗[ℂ] F →ₗ[ℂ] H ⊗[ℂ] F := TensorProduct.map a LinearMap.id
  let P : E ⊗[ℂ] F →ₗ[ℂ] H ⊗[ℂ] F :=
    TensorProduct.map (Kᗮ.starProjection.toLinearMap.comp a) LinearMap.id
  letI : TopologicalSpace (H ⊗[ℂ] F) := projectiveTensorTopology H F
  letI : IsTopologicalAddGroup (H ⊗[ℂ] F) := projectiveTensor_withSeminorms.topologicalAddGroup
  have hlift (z : E ⊗[ℂ] F) : ∃ z' : ℕ → E ⊗[ℂ] F,
      (∀ n, T (z' n) = T z) ∧ Tendsto (fun n => A (z' n)) atTop (𝓝 (P z)) := by
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨fun _ => 0, fun _ => rfl, tendsto_const_nhds⟩
    | tmul x y =>
      have hx : K.starProjection (a x) ∈ closure (S.map a : Set H) :=
        K.starProjection_apply_mem _
      obtain ⟨s, hs, hlim⟩ := mem_closure_iff_seq_limit.mp hx
      choose t ht ht' using hs
      refine ⟨fun n => (x - t n) ⊗ₜ[ℂ] y, fun n => ?_, ?_⟩
      · have hn : S.mkQ (t n) = 0 := (Submodule.Quotient.mk_eq_zero S).mpr (ht n)
        simp only [T, TensorProduct.map_tmul, LinearMap.id_apply, map_sub, hn, sub_zero]
      · have hsub : Tendsto (fun n => a x - s n) atTop (𝓝 (Kᗮ.starProjection (a x))) := by
          rw [Submodule.starProjection_orthogonal_val]
          exact tendsto_const_nhds.sub hlim
        have hA (n : ℕ) : A ((x - t n) ⊗ₜ[ℂ] y) = (a x - s n) ⊗ₜ[ℂ] y := by
          simp only [A, TensorProduct.map_tmul, LinearMap.id_apply, map_sub, ht']
        have hP : P (x ⊗ₜ[ℂ] y) = Kᗮ.starProjection (a x) ⊗ₜ[ℂ] y := by
          simp only [P, TensorProduct.map_tmul, LinearMap.id_apply]
          rfl
        simp only [hA, hP]
        exact ((continuous_projectiveTensor_tmul (E := H) (F := F)).comp
          (continuous_id.prodMk continuous_const)).continuousAt.tendsto.comp hsub
    | add x y hx hy =>
      obtain ⟨x', hx', hxlim⟩ := hx
      obtain ⟨y', hy', hylim⟩ := hy
      exact ⟨fun n => x' n + y' n, fun n => by simp only [map_add, hx', hy'], by
        simpa only [map_add] using hxlim.add hylim⟩
  obtain ⟨z', hz', hzlim⟩ := hlift z
  have hc : Continuous (injectiveTensorSeminorm (W, V)) :=
    projectiveTensor_withSeminorms.continuous_seminorm (injectiveAsProjectiveTest (W, V))
  change r (T z) ≤ injectiveTensorSeminorm (W, V) (P z)
  exact le_of_tendsto_of_tendsto' tendsto_const_nhds (hc.continuousAt.tendsto.comp hzlim) fun n => by
    rw [← hz' n]
    exact h (z' n)

set_option maxHeartbeats 1000000 in
/-- Every Hausdorff quotient of a nuclear locally convex space is nuclear. -/
theorem nuclearLocallyConvex_quotient {E : Type u}
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (hE : NuclearLocallyConvex.{max u v, u} E)
    (S : Submodule ℂ E) (hS : IsClosed (S : Set E)) :
    NuclearLocallyConvex.{max u v, u} (E ⧸ S) := by
  letI : T2Space E := hE.1
  letI : PolynormableSpace ℂ E := hE.2.1
  let hW := PolynormableSpace.withSeminorms ℂ E
  letI : IsTopologicalAddGroup E := hW.topologicalAddGroup
  letI : ContinuousSMul ℂ E := hW.continuousSMul
  letI : IsClosed (S : Set E) := hS
  let Q := E ⧸ S
  letI : PolynormableSpace ℂ Q := polynormableSpace_complex_quotient S
  refine ⟨inferInstance, inferInstance, fun F _ _ _ _ _ => ?_⟩
  apply tensorTopologies_equal_of_continuous_projectiveTests
  intro P
  let idF := ContinuousLinearMap.id ℂ F
  let T : E ⊗[ℂ] F →ₗ[ℂ] Q ⊗[ℂ] F := TensorProduct.map S.mkQ LinearMap.id
  have hPc : Continuous[projectiveTensorTopology Q F, _] P.tensor := by
    letI : TopologicalSpace (Q ⊗[ℂ] F) := projectiveTensorTopology Q F
    exact projectiveTensor_withSeminorms.continuous_seminorm P
  have hR : Continuous[projectiveTensorTopology E F, _] (P.tensor.comp T) :=
    @Continuous.comp _ _ _ (projectiveTensorTopology E F) (projectiveTensorTopology Q F)
      _ _ _ hPc (projectiveTensor_map_continuous S.mkQL idF)
  rw [hE.2.2 F] at hR
  obtain ⟨I, hI⟩ := continuous_injectiveTensor_seminorm_domination _ hR
  let U := injectiveAsProjectiveTest I
  obtain ⟨H, nh, ih, ch, a, C, hC, ha⟩ :=
    nuclearLocallyConvex_hilbert_domination hE U.first U.first_continuous
  letI : NormedAddCommGroup H := nh
  letI : InnerProductSpace ℂ H := ih
  letI : CompleteSpace H := ch
  letI : PolynormableSpace ℂ H := (norm_withSeminorms ℂ H).toPolynormableSpace
  let L := a.toLinearMap.range.topologicalClosure
  let aL := (Submodule.inclusion a.toLinearMap.range.le_topologicalClosure).comp
    a.toLinearMap.rangeRestrict
  have hd : DenseRange aL :=
    ((denseRange_inclusion_iff a.toLinearMap.range.le_topologicalClosure).mpr subset_rfl).comp
      a.toLinearMap.surjective_rangeRestrict.denseRange (continuous_inclusion _)
  letI : CompleteSpace L := a.toLinearMap.range.isClosed_topologicalClosure.completeSpace_coe
  let c : ℝ≥0 := ⟨C, hC⟩
  let q : Seminorm ℂ H := c • normSeminorm ℂ H
  let W := seminormPolarTest q (continuous_const.mul continuous_norm)
  have hfactor (φ : I.1.forms) :
      ∃ ψ ∈ W.forms, pullDual a ψ = φ.val := by
    have hb (x : E) : ‖φ.val x‖ ≤ C * ‖aL x‖ :=
      (dualTestSeminorm_dom I.1 φ x).trans (ha x)
    let d := φ.val.toLinearMap.extendOfNorm aL
    let ψ := d.comp L.orthogonalProjectionOnto
    refine ⟨ψ, ?_, ?_⟩
    · intro x
      change ‖d (L.orthogonalProjectionOnto x)‖ ≤ C * ‖x‖
      exact (LinearMap.norm_extendOfNorm_apply_le hd C hb _).trans
        (mul_le_mul_of_nonneg_left (L.norm_orthogonalProjectionOnto_apply_le x) hC)
    · ext x
      change d (L.orthogonalProjectionOnto (a x)) = φ.val x
      rw [show L.orthogonalProjectionOnto (a x) = aL x from
        L.orthogonalProjectionOnto_mem_subspace_eq_self (aL x)]
      exact LinearMap.extendOfNorm_eq hd ⟨C, hb⟩ x
  have hbound (z : E ⊗[ℂ] F) : P.tensor (T z) ≤
      injectiveTensorSeminorm (W, I.2) (TensorProduct.map a.toLinearMap LinearMap.id z) := by
    refine (hI z).trans ?_
    apply injectiveTensorSeminorm_le _ _ _ (apply_nonneg _ _)
    intro φ hφ η hη
    obtain ⟨ψ, hψ, hβα⟩ := hfactor ⟨φ, hφ⟩
    have hηid : pullDual idF η = η := by ext x; rfl
    have hψbound := norm_dualPair_le W I.2
      (TensorProduct.map a.toLinearMap idF.toLinearMap z) hψ hη
    rw [dualPair_tensorMap, hβα, hηid] at hψbound
    exact hψbound
  let K := (S.map a.toLinearMap).topologicalClosure
  letI : CompleteSpace K := (S.map a.toLinearMap).isClosed_topologicalClosure.completeSpace_coe
  let a' := Kᗮ.starProjection.comp a
  have hker : S ≤ a'.ker := fun x hx =>
    K.starProjection_orthogonal_apply_eq_zero
      (Submodule.le_topologicalClosure _ ⟨x, hx, rfl⟩)
  let b := S.liftQL a' hker
  let M := TensorProduct.map b.toLinearMap idF.toLinearMap
  have hMT : M.comp T = TensorProduct.map a'.toLinearMap LinearMap.id := by
    apply TensorProduct.ext'
    intro x y
    dsimp only [M, T, LinearMap.comp_apply]
    rw [TensorProduct.map_tmul, TensorProduct.map_tmul, TensorProduct.map_tmul]
    rfl
  have hM := injectiveTensor_map_continuous b idF
  let r := (injectiveTensorSeminorm (W, I.2)).comp M
  have hrc : Continuous[injectiveTensorTopology H F, _] (injectiveTensorSeminorm (W, I.2)) := by
    letI : TopologicalSpace (H ⊗[ℂ] F) := injectiveTensorTopology H F
    exact injectiveTensor_withSeminorms.continuous_seminorm (W, I.2)
  have hr : Continuous[injectiveTensorTopology Q F, _] r :=
    @Continuous.comp _ _ _ (injectiveTensorTopology Q F) (injectiveTensorTopology H F) _ _ _
      hrc hM
  letI : TopologicalSpace (Q ⊗[ℂ] F) := injectiveTensorTopology Q F
  letI : IsTopologicalAddGroup (Q ⊗[ℂ] F) := injectiveTensor_withSeminorms.topologicalAddGroup
  refine Seminorm.continuous_of_le hr fun z => ?_
  have hT : Surjective T := TensorProduct.map_surjective S.mkQ_surjective surjective_id
  obtain ⟨z, rfl⟩ := hT z
  change P.tensor (T z) ≤ injectiveTensorSeminorm (W, I.2) ((M.comp T) z)
  rw [hMT]
  exact quotientTensorSeminorm_le_projection S a.toLinearMap P.tensor W I.2 hbound z

private theorem directSumFinal_component_continuous {I : Type*} [DecidableEq I] {X : I → Type*}
    [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)] [∀ i, TopologicalSpace (X i)]
    [∀ i, IsTopologicalAddGroup (X i)] [∀ i, PolynormableSpace ℂ (X i)] (i : I) :
    letI : TopologicalSpace (⨁ i, X i) := locallyConvexFinalTopology (DirectSum.lof ℂ I X)
    Continuous (DirectSum.component ℂ I X i) := by
  let j := DirectSum.lof ℂ I X
  letI : TopologicalSpace (⨁ i, X i) := locallyConvexFinalTopology j
  apply (locallyConvexFinal_continuous_iff j _).mpr
  intro l
  by_cases h : l = i
  · subst l
    rw [show (DirectSum.component ℂ I X i).comp (j i) = LinearMap.id from
      LinearMap.ext fun _ => DFinsupp.single_eq_same]
    exact continuous_id
  · rw [show (DirectSum.component ℂ I X i).comp (j l) = 0 from
      LinearMap.ext fun _ => DFinsupp.single_eq_of_ne (Ne.symm h)]
    exact continuous_const

set_option maxHeartbeats 1000000 in
private theorem directSum_tensor_eq_normed {I : Type w} [DecidableEq I] {X : I → Type u}
    [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)] [∀ i, TopologicalSpace (X i)]
    [∀ i, PolynormableSpace ℂ (X i)] (k : I ↪ ℕ)
    {F : Type v} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (hX : ∀ i, projectiveTensorTopology (X i) F = injectiveTensorTopology (X i) F) :
    letI : TopologicalSpace (⨁ i, X i) := locallyConvexFinalTopology (DirectSum.lof ℂ I X)
    projectiveTensorTopology (⨁ i, X i) F = injectiveTensorTopology (⨁ i, X i) F := by
  classical
  let D := ⨁ i, X i
  let j := DirectSum.lof ℂ I X
  letI : TopologicalSpace D := locallyConvexFinalTopology j
  letI : ∀ i, IsTopologicalAddGroup (X i) :=
    fun i => (PolynormableSpace.withSeminorms ℂ (X i)).topologicalAddGroup
  letI : PolynormableSpace ℂ D := (locallyConvexFinal_withSeminorms j).toPolynormableSpace
  letI : PolynormableSpace ℂ F := (norm_withSeminorms ℂ F).toPolynormableSpace
  let jL (i : I) : X i →L[ℂ] D := ⟨j i, locallyConvexFinal_stage_continuous j i⟩
  let pr := DirectSum.component ℂ I X
  apply tensorTopologies_equal_of_continuous_projectiveTests
  intro P
  let r (i : I) := P.tensor.comp ((j i).rTensor F)
  have hp : Continuous[projectiveTensorTopology D F, _] P.tensor := by
    letI : TopologicalSpace (D ⊗[ℂ] F) := projectiveTensorTopology D F
    exact projectiveTensor_withSeminorms.continuous_seminorm P
  have hr (i : I) : Continuous[injectiveTensorTopology (X i) F, _] (r i) := by
    rw [← hX i]
    exact @Continuous.comp _ _ _ (projectiveTensorTopology (X i) F)
      (projectiveTensorTopology D F) _ _ _
      hp (projectiveTensor_map_continuous (jL i) (ContinuousLinearMap.id ℂ F))
  choose A hA using fun i => continuous_injectiveTensor_seminorm_domination (r i) (hr i)
  let U (i : I) := injectiveAsProjectiveTest (A i)
  have hnorm (i : I) : ∃ C : ℝ≥0, 0 < C ∧ ∀ y : F, (U i).second y ≤ (C : ℝ) * ‖y‖ := by
    obtain ⟨s, C, hC, h⟩ := Seminorm.bound_of_continuous (norm_withSeminorms ℂ F)
      (U i).second (U i).second_continuous
    refine ⟨C, pos_iff_ne_zero.mpr hC, fun y => (h y).trans ?_⟩
    exact mul_le_mul_of_nonneg_left
      (show (s.sup (fun _ => normSeminorm ℂ F)) y ≤ ‖y‖ from
        (Finset.sup_le (fun _ _ => le_rfl : ∀ a ∈ s, normSeminorm ℂ F ≤ normSeminorm ℂ F)) y)
      C.coe_nonneg
  choose C hC hnorm using hnorm
  let w (i : I) : ℝ≥0 := (1 / 2 : ℝ≥0) ^ k i
  have hw (i : I) : 0 < w i := by dsimp [w]; positivity
  let q (i : I) := (C i / w i) • (U i).first
  let Q := directSumSeminorm q
  have hQ : Continuous Q := locallyConvexFinal_seminorm_continuous j Q fun i => by
    have hq : Continuous (q i) := continuous_const.mul (U i).first_continuous
    exact hq.congr fun x => (directSumSeminorm_lof q i x).symm
  let S := seminormPolarTest Q hQ
  let T := seminormPolarTest (normSeminorm ℂ F) continuous_norm
  have hcast (a : ℝ≥0) : ‖(a : ℂ)‖ = (a : ℝ) := by
    rw [Complex.norm_real, Real.norm_of_nonneg a.coe_nonneg]
  have hstage (i : I) (z : D ⊗[ℂ] F) :
      r i ((pr i).rTensor F z) ≤ (w i : ℝ) * injectiveTensorSeminorm (S, T) z := by
    refine (hA i _).trans ?_
    apply injectiveTensorSeminorm_le _ _ _ (by positivity)
    intro φ hφ ψ hψ
    let prL (i : I) : D →L[ℂ] X i := ⟨pr i, directSumFinal_component_continuous i⟩
    let φ' : D →Lₚₜ[ℂ] ℂ := ((C i / w i : ℝ≥0) : ℂ) • pullDual (prL i) φ
    let ψ' : F →Lₚₜ[ℂ] ℂ := (((C i)⁻¹ : ℝ≥0) : ℂ) • ψ
    have hφ' : φ' ∈ S.forms := by
      intro x
      change ‖((↑(C i / w i) : ℂ) • φ ((pr i) x))‖ ≤ Q x
      rw [norm_smul, hcast]
      calc
        _ ≤ q i (x i) :=
          mul_le_mul_of_nonneg_left (dualTestSeminorm_dom (A i).1 ⟨φ, hφ⟩ (x i))
            (NNReal.coe_nonneg _)
        _ ≤ _ := by
          simpa only [Finset.sum_singleton] using sum_le_directSumSeminorm q x {i}
    have hψ' : ψ' ∈ T.forms := by
      intro y
      change ‖((↑((C i)⁻¹) : ℂ) • ψ y)‖ ≤ ‖y‖
      rw [norm_smul, hcast ((C i)⁻¹), NNReal.coe_inv]
      have hb := (dualTestSeminorm_dom (A i).2 ⟨ψ, hψ⟩ y).trans (hnorm i y)
      simpa only [inv_mul_cancel_left₀
        (show (C i : ℝ) ≠ 0 from (NNReal.coe_pos.mpr (hC i)).ne')] using
          mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr (C i).coe_nonneg)
    have he : dualPair φ ψ ((pr i).rTensor F z) = (↑(w i) : ℂ) * dualPair φ' ψ' z := by
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul x y =>
        simp only [LinearMap.rTensor_tmul, dualPair_tmul]
        change φ (x i) * ψ y =
          (↑(w i) : ℂ) * (((↑(C i / w i) : ℂ) * φ (x i)) * ((↑((C i)⁻¹) : ℂ) * ψ y))
        push_cast
        field_simp [show (↑(w i) : ℂ) ≠ 0 by exact_mod_cast (hw i).ne',
          show (↑(C i) : ℂ) ≠ 0 by exact_mod_cast (hC i).ne']
      | add x y hx hy => simp only [map_add, hx, hy, mul_add]
    rw [he, norm_mul, hcast]
    exact mul_le_mul_of_nonneg_left (norm_dualPair_le S T z hφ' hψ') (NNReal.coe_nonneg _)
  let e := TensorProduct.directSumLeft ℂ ℂ X F
  have he (i : I) (z : D ⊗[ℂ] F) : e z i = (pr i).rTensor F z := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => rw [LinearMap.rTensor_tmul]; exact TensorProduct.directSumLeft_tmul ℂ ℂ x y i
    | add x y hx hy =>
      rw [map_add, map_add]
      change (e x) i + (e y) i = _
      rw [hx, hy]
  have hbound (z : D ⊗[ℂ] F) : P.tensor z ≤ 2 * injectiveTensorSeminorm (S, T) z := by
    let s := (e z).support
    have hsum : (∑ i ∈ s, (j i).rTensor F ((pr i).rTensor F z)) = z := by
      have hstep (i : I) : e.symm (DirectSum.of (fun i => X i ⊗[ℂ] F) i (e z i)) =
          (j i).rTensor F ((pr i).rTensor F z) := by
        rw [← he]
        generalize e z i = x
        change e.symm (DirectSum.lof ℂ I _ i x) = _
        induction x using TensorProduct.induction_on with
        | zero => simp
        | tmul x y =>
          exact TensorProduct.directSumLeft_symm_lof_tmul ℂ ℂ i x y
        | add x y hx hy => simp only [map_add, hx, hy]
      simpa only [map_sum, LinearEquiv.symm_apply_apply, hstep] using
        congrArg e.symm (DirectSum.sum_support_of (e z))
    calc
      _ = P.tensor (∑ i ∈ s, (j i).rTensor F ((pr i).rTensor F z)) := congrArg P.tensor hsum.symm
      _ ≤ ∑ i ∈ s, r i ((pr i).rTensor F z) :=
        Finset.le_sum_of_subadditive P.tensor (map_zero P.tensor).le (map_add_le_add P.tensor) _ _
      _ ≤ ∑ i ∈ s, (w i : ℝ) * injectiveTensorSeminorm (S, T) z :=
        Finset.sum_le_sum fun i _ => hstage i z
      _ ≤ _ := by
        rw [← Finset.sum_mul]
        apply mul_le_mul_of_nonneg_right _ (apply_nonneg _ _)
        rw [show (∑ i ∈ s, (w i : ℝ)) = ∑ n ∈ s.map k, (1 / 2 : ℝ) ^ n by norm_num [w]]
        calc
          _ ≤ ∑' n : ℕ, (1 / 2 : ℝ) ^ n :=
            summable_geometric_two.sum_le_tsum _ (fun n _ => by positivity)
          _ = 2 := tsum_geometric_two
  letI : TopologicalSpace (D ⊗[ℂ] F) := injectiveTensorTopology D F
  letI : IsTopologicalAddGroup (D ⊗[ℂ] F) := injectiveTensor_withSeminorms.topologicalAddGroup
  exact Seminorm.continuous_of_le (q := (2 : ℝ≥0) • injectiveTensorSeminorm (S, T))
    (continuous_const.mul (injectiveTensor_withSeminorms.continuous_seminorm (S, T))) hbound

set_option maxHeartbeats 900000 in
/-- The locally convex direct sum of a countable family of nuclear spaces is
nuclear for the final locally convex topology of the summand inclusions. -/
theorem nuclearLocallyConvex_directSum {I : Type w} [DecidableEq I] {X : I → Type u}
    [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)] [∀ i, TopologicalSpace (X i)]
    (k : I ↪ ℕ) (hX : ∀ i, NuclearLocallyConvex.{max u v w, u} (X i)) :
    letI : TopologicalSpace (⨁ i, X i) := locallyConvexFinalTopology (DirectSum.lof ℂ I X)
    NuclearLocallyConvex.{max u v w, max u w} (⨁ i, X i) := by
  classical
  let D := ⨁ i, X i
  let j := DirectSum.lof ℂ I X
  letI : TopologicalSpace D := locallyConvexFinalTopology j
  let hD := locallyConvexFinal_withSeminorms j
  letI : PolynormableSpace ℂ D := hD.toPolynormableSpace
  letI : IsTopologicalAddGroup D := hD.topologicalAddGroup
  letI : ∀ i, PolynormableSpace ℂ (X i) := fun i => (hX i).2.1
  letI : ∀ i, T2Space (X i) := fun i => (hX i).1
  letI : ∀ i, IsTopologicalAddGroup (X i) :=
    fun i => (PolynormableSpace.withSeminorms ℂ (X i)).topologicalAddGroup
  letI : T2Space D := T2Space.of_injective_continuous (f := fun x i => x i)
    (fun _ _ e => DFinsupp.ext (congrFun e)) (continuous_pi directSumFinal_component_continuous)
  refine ⟨inferInstance, inferInstance, fun F _ _ _ _ _ => ?_⟩
  apply tensorTopologies_equal_of_continuous_projectiveTests
  intro P
  let Z := LocalBanach P.second
  letI : PolynormableSpace ℂ Z := (norm_withSeminorms ℂ Z).toPolynormableSpace
  let V := LocalBanach P.tensor
  let κ := localBanachDenseMap P.tensor
  let B : D →ₗ[ℂ] F →ₗ[ℂ] V := (TensorProduct.mk ℂ D F).compr₂ κ
  obtain ⟨d, hdcoe, hdn⟩ := extendBilinearSecond P.first P.second B (fun x y => by
    change ‖localBanachDenseMap P.tensor (x ⊗ₜ[ℂ] y)‖ ≤ _
    exact (norm_localBanachDenseMap _ _).le.trans (P.bound x y))
  let dL : D →L[ℂ] (Z →L[ℂ] V) := ⟨d, by
    apply continuous_of_tendsto_nhds_zero (G := D) (M := Z →L[ℂ] V) d.toAddMonoidHom
    rw [Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [(P.first_continuous.tendsto' 0 0 (map_zero P.first)).eventually
      (Iio_mem_nhds hε)] with x hx
    rw [dist_zero_right]
    exact (hdn x).trans_lt hx⟩
  let b : D →ₗ[ℂ] Z →ₗ[ℂ] V := LinearMap.mk₂ ℂ (fun x y => dL x y)
    (by intros; simp) (by intros; simp) (by intros; simp) (by intros; simp)
  have hb : Continuous (fun z : D × Z => b z.1 z.2) :=
    (dL.continuous.comp continuous_fst).clm_apply continuous_snd
  have hl := continuous_projectiveTensor_lift b hb
  rw [directSum_tensor_eq_normed k (fun i => (hX i).2.2 Z)] at hl
  letI : IsTopologicalAddGroup F := (PolynormableSpace.withSeminorms ℂ F).topologicalAddGroup
  let J := localBanachMap P.second P.second_continuous
  let M := TensorProduct.map (ContinuousLinearMap.id ℂ D).toLinearMap J.toLinearMap
  have hκ : (TensorProduct.lift b).comp M = κ := by
    apply TensorProduct.ext'
    intro x y
    change (TensorProduct.lift b) (TensorProduct.map LinearMap.id J.toLinearMap (x ⊗ₜ[ℂ] y)) = _
    rw [TensorProduct.map_tmul, TensorProduct.lift.tmul, LinearMap.id_apply]
    exact hdcoe x y
  have hln : Continuous[injectiveTensorTopology D Z, _] (fun x => ‖TensorProduct.lift b x‖) := by
    letI : TopologicalSpace (D ⊗[ℂ] Z) := injectiveTensorTopology D Z
    exact hl.norm
  have hc : Continuous[injectiveTensorTopology D F, _] (fun x => ‖TensorProduct.lift b (M x)‖) :=
    @Continuous.comp _ _ _ (injectiveTensorTopology D F) (injectiveTensorTopology D Z) _ _ _
      hln (injectiveTensor_map_continuous (ContinuousLinearMap.id ℂ D) J)
  exact (@Continuous.congr _ _ (injectiveTensorTopology D F) _ _ _ hc fun z => by
    change ‖((TensorProduct.lift b).comp M) z‖ = P.tensor z
    rw [hκ]
    exact norm_localBanachDenseMap _ _)

/-- A continuous linear equivalence transports nuclearity. -/
theorem nuclearLocallyConvex_of_equiv {E : Type u} {F : Type w}
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
    (e : E ≃L[ℂ] F) (hE : NuclearLocallyConvex.{v, u} E) :
    NuclearLocallyConvex.{v, w} F := by
  letI : T2Space E := hE.1
  letI : T2Space F := e.toHomeomorph.t2Space
  letI : PolynormableSpace ℂ E := hE.2.1
  letI : PolynormableSpace ℂ F := (e.symm.toHomeomorph.isInducing.withSeminorms
    (f := e.symm.toLinearMap) (PolynormableSpace.withSeminorms ℂ E)).toPolynormableSpace
  refine ⟨inferInstance, inferInstance, fun Z _ _ _ _ _ => ?_⟩
  apply tensorTopologies_equal_of_continuous_projectiveTests
  intro P
  let j := ContinuousLinearMap.id ℂ Z
  let M := TensorProduct.map e.toContinuousLinearMap.toLinearMap j.toLinearMap
  let N := TensorProduct.map e.symm.toContinuousLinearMap.toLinearMap j.toLinearMap
  have hm : Continuous[projectiveTensorTopology E Z, projectiveTensorTopology F Z] M :=
    projectiveTensor_map_continuous e.toContinuousLinearMap j
  rw [hE.2.2 Z] at hm
  have hn : Continuous[injectiveTensorTopology F Z, injectiveTensorTopology E Z] N :=
    injectiveTensor_map_continuous e.symm.toContinuousLinearMap j
  have hp : Continuous[projectiveTensorTopology F Z, _] P.tensor := by
    letI : TopologicalSpace (F ⊗[ℂ] Z) := projectiveTensorTopology F Z
    exact projectiveTensor_withSeminorms.continuous_seminorm P
  have hpm : Continuous[injectiveTensorTopology E Z, _] (fun x => P.tensor (M x)) :=
    @Continuous.comp _ _ _ (injectiveTensorTopology E Z) (projectiveTensorTopology F Z) _ _ _ hp hm
  have hc : Continuous[injectiveTensorTopology F Z, _] (fun x => P.tensor (M (N x))) :=
    @Continuous.comp _ _ _ (injectiveTensorTopology F Z) (injectiveTensorTopology E Z) _ _ _ hpm hn
  exact @Continuous.congr _ _ (injectiveTensorTopology F Z) _ _ _ hc fun x => by
    have he : M.comp N = LinearMap.id := by
      apply TensorProduct.ext'
      intro x y
      simp only [M, N, j, LinearMap.comp_apply, TensorProduct.map_tmul,
        ContinuousLinearMap.coe_coe, ContinuousLinearMap.id_apply, LinearMap.id_apply,
        ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply]
    rw [show M (N x) = x from LinearMap.congr_fun he x]

set_option maxHeartbeats 900000 in
/-- The Hausdorff locally convex inductive limit of a sequence of nuclear
spaces is nuclear, with no injectivity requirement on the transition maps.
Together with the projective limit theorem this proves Lemma C.2.4.12. -/
theorem nuclearLocallyConvex_directLimit {X : ℕ → Type u}
    [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)] [∀ i, TopologicalSpace (X i)]
    (f : ∀ i j, i ≤ j → X i →ₗ[ℂ] X j)
    [DirectedSystem X (fun {i j} h => f i j h)]
    (hX : ∀ i, NuclearLocallyConvex.{max u v, u} (X i)) :
    letI : TopologicalSpace (Module.DirectLimit X f) :=
      locallyConvexFinalTopology (Module.DirectLimit.of ℂ ℕ X f)
    T2Space (Module.DirectLimit X f) →
    NuclearLocallyConvex.{max u v, u} (Module.DirectLimit X f) := by
  let D := ⨁ i, X i
  let L := Module.DirectLimit X f
  let j := DirectSum.lof ℂ ℕ X
  let stage := Module.DirectLimit.of ℂ ℕ X f
  letI : TopologicalSpace D := locallyConvexFinalTopology j
  letI : TopologicalSpace L := locallyConvexFinalTopology stage
  intro h
  letI : T2Space L := h
  letI : ∀ i, PolynormableSpace ℂ (X i) := fun i => (hX i).2.1
  letI : ∀ i, IsTopologicalAddGroup (X i) :=
    fun i => (PolynormableSpace.withSeminorms ℂ (X i)).topologicalAddGroup
  letI : PolynormableSpace ℂ D := (locallyConvexFinal_withSeminorms j).toPolynormableSpace
  letI : IsTopologicalAddGroup D := (locallyConvexFinal_withSeminorms j).topologicalAddGroup
  letI : ContinuousSMul ℂ D := (locallyConvexFinal_withSeminorms j).continuousSMul
  letI : PolynormableSpace ℂ L := (locallyConvexFinal_withSeminorms stage).toPolynormableSpace
  have hN : NuclearLocallyConvex.{max u v, u} D :=
    nuclearLocallyConvex_directSum.{u, v, 0} (Function.Embedding.refl ℕ) hX
  let q : D →ₗ[ℂ] L := DirectSum.toModule ℂ ℕ L stage
  have hqj (i : ℕ) (x : X i) : q (j i x) = stage i x := DirectSum.toModule_lof ℂ i x
  have hqs : Surjective q := by
    intro z
    obtain ⟨i, x, rfl⟩ := Module.DirectLimit.exists_of z
    exact ⟨j i x, hqj i x⟩
  have hqc : Continuous q := by
    apply (locallyConvexFinal_continuous_iff j q).mpr
    intro i
    exact (locallyConvexFinal_stage_continuous stage i).congr fun x => (hqj i x).symm
  let K := q.ker
  letI : PolynormableSpace ℂ (D ⧸ K) := polynormableSpace_complex_quotient K
  have hK : IsClosed (K : Set D) := isClosed_singleton.preimage hqc
  let e := q.quotKerEquivOfSurjective hqs
  have he : Continuous e := by
    apply K.isOpenQuotientMap_mkQ.isQuotientMap.continuous_iff.mpr
    exact hqc
  have hes : Continuous e.symm := by
    apply (locallyConvexFinal_continuous_iff stage e.symm.toLinearMap).mpr
    intro i
    refine (K.mkQL.continuous.comp (locallyConvexFinal_stage_continuous j i)).congr fun x => ?_
    change K.mkQ (j i x) = e.symm (stage i x)
    rw [← hqj]
    exact (q.quotKerEquivOfSurjective_symm_apply hqs (j i x)).symm
  let eL : (D ⧸ K) ≃L[ℂ] L := ⟨e, he, hes⟩
  exact nuclearLocallyConvex_of_equiv eL (nuclearLocallyConvex_quotient.{u, v} hN K hK)

end
end Masullo
