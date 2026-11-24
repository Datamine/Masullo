import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.LocallyConvex.Barrelled
import Mathlib.Analysis.LocallyConvex.StrongTopology
import Mathlib.Analysis.LocallyConvex.PointwiseConvergence
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
import Mathlib.Topology.UniformSpace.Ascoli
import Mathlib.Topology.Algebra.Module.Spaces.CompactConvergenceCLM
import Mathlib.Topology.Algebra.Module.Spaces.PointwiseConvergenceCLM

open Bornology Filter Function Set Topology TopologicalSpace UniformConvergence
open scoped Uniformity Topology UniformConvergence UniformConvergenceCLM CompactConvergenceCLM

namespace Masullo

section QuasiComplete

variable {E F : Type*} [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E]
  [ContinuousSMul ℂ E] [BarrelledSpace ℂ E]
  [AddCommGroup F] [Module ℂ F] [UniformSpace F] [IsUniformAddGroup F]
  [ContinuousSMul ℂ F] [T2Space F] [PolynormableSpace ℂ F] [QuasiCompleteSpace ℂ F]

/-- Lemma C.2.1.7. A bounded Cauchy filter of continuous linear maps has
a pointwise limit by quasi-completeness, and barrelledness makes the limit continuous. -/
theorem mappingSpace_quasiComplete (S : Set (Set E)) (hcover : ⋃₀ S = univ) :
    QuasiCompleteSpace ℂ (E →Lᵤ[ℂ, S] F) := by
  classical
  let M := E →Lᵤ[ℂ, S] F
  refine ⟨fun {B} hB hBcl => ?_⟩
  intro l hl hls
  letI : l.NeBot := hl.1
  have hBmem : ∀ᶠ f in l, f ∈ B := hls (mem_principal_self B)
  have hbound (x : E) : IsVonNBounded ℂ ((fun f : M => f x) '' B) := by
    obtain ⟨T, hT, hx⟩ := mem_sUnion.mp (hcover.symm ▸ mem_univ x)
    refine (UniformConvergenceCLM.isVonNBounded_image2_apply hB hT).subset ?_
    rintro _ ⟨f, hf, rfl⟩
    exact mem_image2_of_mem hf hx
  have evalUc (x : E) : UniformContinuous (fun f : M => f x) :=
    (UniformOnFun.uniformContinuous_eval (β := F) hcover x).comp
      (UniformConvergenceCLM.isUniformInducing_coeFn (RingHom.id ℂ) F S).uniformContinuous
  have hlim (x : E) : ∃ y : F, Tendsto (fun f : M => f x) l (𝓝 y) := by
    let C := closure ((fun f : M => f x) '' B)
    have hC : IsComplete C := QuasiCompleteSpace.quasiComplete (hbound x).closure isClosed_closure
    have hmap : map (fun f : M => f x) l ≤ 𝓟 C := le_principal_iff.mpr <|
      hBmem.mono fun f hf => subset_closure (mem_image_of_mem (fun f : M => f x) hf)
    obtain ⟨y, _, hy⟩ := hC _ (hl.map (evalUc x)) hmap
    exact ⟨y, hy⟩
  choose g hg using hlim
  let C (f : M) : E →L[ℂ] F := if f ∈ B then f else 0
  have hCb (x : E) : IsVonNBounded ℂ (range fun f => C f x) := by
    refine (isVonNBounded_singleton (𝕜 := ℂ) (0 : F)).union (hbound x) |>.subset ?_
    rintro _ ⟨f, rfl⟩
    by_cases hf : f ∈ B
    · apply mem_union_right
      have he : C f = (f : E →L[ℂ] F) := ite_eq_left hf
      change C f x ∈ (fun f : M => f x) '' B
      rw [he]
      exact mem_image_of_mem (fun k : M => k x) hf
    · have he : C f = 0 := ite_eq_right hf
      apply mem_union_left
      change C f x ∈ ({0} : Set F)
      simp [he]
  have hpt : Tendsto (fun f x => C f x) l (𝓝 g) := tendsto_pi_nhds.mpr fun x =>
    (hg x).congr' (hBmem.mono fun f hf => by
      change f x = (C f) x
      have he : C f = (f : E →L[ℂ] F) := ite_eq_left hf
      exact (DFunLike.congr_fun he x).symm)
  let A : E →L[ℂ] F := ⟨linearMapOfTendsto g (fun f => (C f).toLinearMap) hpt,
    hpt.continuous_of_equicontinuous (PolynormableSpace.banach_steinhaus (𝓕 := C) hCb).equicontinuous⟩
  let A' : M := A
  have hcauchy : Cauchy (map (fun f : M => UniformOnFun.ofFun S (fun x => f x)) l) :=
    hl.map (UniformConvergenceCLM.isUniformInducing_coeFn (RingHom.id ℂ) F S).uniformContinuous
  have hA : Tendsto (id : M → M) l (𝓝 A') := by
    apply (UniformConvergenceCLM.tendsto_iff_tendstoUniformlyOn (RingHom.id ℂ) F S).mpr
    intro T hT U hU
    obtain ⟨V, ⟨hV, hVcl⟩, hVU⟩ := uniformity_hasBasis_closed.mem_iff.mp hU
    obtain ⟨W, hW, hWV⟩ := (cauchy_iff.mp hcauchy).2 _ (UniformOnFun.gen_mem_uniformity F S hT hV)
    have hW' : ∀ᶠ f in l, UniformOnFun.ofFun S (fun x => f x) ∈ W := hW
    filter_upwards [hW'] with f hf x hx
    apply hVU
    have hlimx : Tendsto (fun k : M => (k x, f x)) l (𝓝 (A' x, f x)) :=
      (hg x).prodMk_nhds tendsto_const_nhds
    refine hVcl.mem_of_tendsto hlimx ?_
    filter_upwards [hW'] with k hk
    have hw : (UniformOnFun.ofFun S (fun x => k x), UniformOnFun.ofFun S (fun x => f x)) ∈ W ×ˢ W :=
      ⟨hk, hf⟩
    exact hWV hw x hx
  exact ⟨A', hBcl.mem_of_tendsto hA hBmem, hA⟩

end QuasiComplete

section LocallyConvex

variable {X F : Type*} [UniformSpace F] [AddCommGroup F] [IsUniformAddGroup F]
  [Module ℝ F] [LocallyConvexSpace ℝ F]

private theorem uniformOn_locallyConvex_directed (S : Set (Set X)) (hn : S.Nonempty)
    (hd : DirectedOn (· ⊆ ·) S) : LocallyConvexSpace ℝ (X →ᵤ[S] F) := by
  apply LocallyConvexSpace.ofBasisZero _ _ _ _
    (UniformOnFun.hasBasis_nhds_zero_of_basis S hn hd (LocallyConvexSpace.convex_basis_zero ℝ F))
  rintro ⟨T, V⟩ ⟨_, _, hV⟩ f hf g hg a b ha hb hab x hx
  exact hV (hf x hx) (hg x hx) ha hb hab

private theorem uniformOn_locallyConvex (S : Set (Set X)) : LocallyConvexSpace ℝ (X →ᵤ[S] F) := by
  let D : Set (Set X) := {U | ∃ T ⊆ S, T.Finite ∧ U = ⋃₀ T}
  have hn : D.Nonempty := ⟨∅, ∅, empty_subset _, finite_empty, by simp⟩
  have hd : DirectedOn (· ⊆ ·) D := by
    rintro a ⟨A, hA, hAf, rfl⟩ b ⟨B, hB, hBf, rfl⟩
    refine ⟨⋃₀ (A ∪ B), ⟨A ∪ B, union_subset hA hB, hAf.union hBf, rfl⟩, ?_, ?_⟩
    · exact sUnion_mono subset_union_left
    · exact sUnion_mono subset_union_right
  have hs : S ⊆ D := fun a ha => ⟨{a}, singleton_subset_iff.mpr ha, finite_singleton _, by simp⟩
  have fwd : Continuous (UniformOnFun.ofFun D ∘ UniformOnFun.toFun S : (X →ᵤ[S] F) → X →ᵤ[D] F) :=
    (UniformOnFun.uniformContinuous_ofFun_toFun F D S (by
      rintro _ ⟨T, hTS, hTf, rfl⟩
      exact ⟨T, hTS, hTf, Subset.rfl⟩)).continuous
  have bwd : Continuous (UniformOnFun.ofFun S ∘ UniformOnFun.toFun D : (X →ᵤ[D] F) → X →ᵤ[S] F) :=
    (UniformOnFun.uniformContinuous_ofFun_toFun_of_subset F S D hs).continuous
  have he : UniformOnFun.topologicalSpace X F S = UniformOnFun.topologicalSpace X F D :=
    le_antisymm (continuous_id_iff_le.mp fwd) (continuous_id_iff_le.mp bwd)
  exact he.symm ▸ (uniformOn_locallyConvex_directed (F := F) D hn hd)

/-- Lemma C.2.1.1. A space of continuous functions separates its points
on the dense union of the test sets. -/
theorem mappingSubmodule_locallyConvex [TopologicalSpace X] [T2Space F] [Module ℂ F]
    [IsScalarTower ℝ ℂ F] [ContinuousSMul ℂ F] (S : Set (Set X))
    (L : Submodule ℂ (X →ᵤ[S] F)) (hd : Dense (⋃₀ S))
    (hcont : ∀ f ∈ L, Continuous (UniformOnFun.toFun S f))
    (hb : ∀ f ∈ L, ∀ T ∈ S, IsVonNBounded ℂ (UniformOnFun.toFun S f '' T)) :
    T2Space L ∧ IsTopologicalAddGroup L ∧ ContinuousSMul ℂ L ∧ LocallyConvexSpace ℝ L := by
  let ev (f : L) (x : ⋃₀ S) : F := UniformOnFun.toFun S f.val x
  have hev : Continuous ev := continuous_pi fun x =>
    ((UniformOnFun.uniformContinuous_eval_of_mem_sUnion F S x.property).continuous).comp continuous_subtype_val
  have heinj : Injective ev := by
    intro f g hfg
    apply Subtype.ext
    apply (UniformOnFun.toFun S).injective
    exact Continuous.ext_on hd (hcont f.val f.property) (hcont g.val g.property)
      (fun x hx => congrFun hfg ⟨x, hx⟩)
  letI := uniformOn_locallyConvex (F := F) S
  exact ⟨T2Space.of_injective_continuous heinj hev, inferInstance,
    UniformOnFun.continuousSMul_submodule_of_image_bounded ℂ X F L hb,
    LocallyConvexSpace.induced (L.restrictScalars ℝ).subtype⟩

/-- Lemma C.2.1.2. Uniform convergence on bounded tests with dense linear
span gives a Hausdorff locally convex topology on continuous linear maps. -/
theorem linearMappingSpace_locallyConvex {E : Type*} [TopologicalSpace E]
    [AddCommGroup E] [Module ℂ E] [Module ℂ F] [IsScalarTower ℝ ℂ F]
    [ContinuousSMul ℂ F] [ContinuousConstSMul ℝ F] [T2Space F] (S : Set (Set E))
    (hb : ∀ T ∈ S, IsVonNBounded ℂ T)
    (hd : Dense (Submodule.span ℂ (⋃₀ S) : Set E)) :
    T2Space (E →Lᵤ[ℂ, S] F) ∧ IsTopologicalAddGroup (E →Lᵤ[ℂ, S] F) ∧
    ContinuousSMul ℂ (E →Lᵤ[ℂ, S] F) ∧ LocallyConvexSpace ℝ (E →Lᵤ[ℂ, S] F) := by
  let M := E →Lᵤ[ℂ, S] F
  let ev (f : M) (x : ⋃₀ S) : F := f x
  have hEmbed := UniformConvergenceCLM.isUniformEmbedding_coeFn (RingHom.id ℂ) F S
  have hev : Continuous ev := continuous_pi fun x =>
    ((UniformOnFun.uniformContinuous_eval_of_mem_sUnion F S x.property).continuous).comp
      hEmbed.isEmbedding.continuous
  have heinj : Injective ev := fun f g hfg =>
    ContinuousLinearMap.ext_on hd (fun x hx => congrFun hfg ⟨x, hx⟩)
  letI := uniformOn_locallyConvex (F := F) S
  let incl : M →ₗ[ℝ] (E →ᵤ[S] F) := {
    toFun := fun f => UniformOnFun.ofFun S f
    map_add' := fun _ _ => rfl
    map_smul' := by
      intro c f
      apply (UniformOnFun.toFun S).injective
      funext x
      change (c • f) x = c • f x
      exact smul_apply f c x }
  refine ⟨T2Space.of_injective_continuous heinj hev, inferInstance,
    UniformConvergenceCLM.continuousSMul (RingHom.id ℂ) F S hb, ?_⟩
  have he : (inferInstance : TopologicalSpace M) = TopologicalSpace.induced incl inferInstance :=
    hEmbed.isEmbedding.isInducing.eq_induced
  change @LocallyConvexSpace ℝ M _ _ _ _ (inferInstance : TopologicalSpace M)
  rw [he]
  exact LocallyConvexSpace.induced incl

end LocallyConvex

section Equicontinuous

variable {E F : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
  [AddCommGroup F] [Module ℂ F] [UniformSpace F] [IsUniformAddGroup F] [ContinuousSMul ℂ F]

/-- Lemma C.2.1.9(1). Equicontinuity controls every bounded test set. -/
theorem equicontinuous_mappingSpace_bounded (H : Set (E →L[ℂ] F))
    (he : Equicontinuous fun f : H => (f.val : E → F)) (S : Set (Set E))
    (hb : ∀ T ∈ S, IsVonNBounded ℂ T) :
    IsVonNBounded ℂ (E := E →Lᵤ[ℂ, S] F) H := by
  let H' : Set (E →Lᵤ[ℂ, S] F) := H
  change IsVonNBounded ℂ H'
  apply (UniformConvergenceCLM.isVonNBounded_iff (σ := RingHom.id ℂ) (S := H')).mpr
  intro T hT V hV
  have hUV : {z : F × F | z.2 - z.1 ∈ V} ∈ 𝓤 F := by
    rw [uniformity_eq_comap_nhds_zero F]
    exact preimage_mem_comap hV
  have hU : {x : E | ∀ f : H, f.val x ∈ V} ∈ 𝓝 0 := by
    filter_upwards [he 0 _ hUV] with x hx f
    simpa only [mem_ofPred_eq, map_zero, sub_zero] using hx f
  filter_upwards [(hb T hT) hU] with c hc
  rintro _ ⟨f, hf, x, hx, rfl⟩
  obtain ⟨y, hy, rfl⟩ := hc hx
  exact ⟨f y, hy ⟨f, hf⟩, (map_smul f c y).symm⟩

omit [ContinuousSMul ℂ F] in
/-- Lemma C.2.1.9(2). The induced pointwise and compact-convergence
topologies coincide on an equicontinuous family. -/
theorem equicontinuous_mappingSpace_topology (H : Set (E →L[ℂ] F))
    (he : Equicontinuous fun f : H => (f.val : E → F)) :
    TopologicalSpace.induced (fun f : H => (f.val : E →L_c[ℂ] F))
      (UniformConvergenceCLM.instTopologicalSpace (RingHom.id ℂ) F {s | IsCompact s}) =
    TopologicalSpace.induced (fun f : H => (f.val : E →Lₚₜ[ℂ] F))
      (UniformConvergenceCLM.instTopologicalSpace (RingHom.id ℂ) F {s | s.Finite}) := by
  let ff : H → E → F := fun f => f.val
  let S : Set (Set E) := {s | IsCompact s}
  have hC := (UniformConvergenceCLM.isEmbedding_coeFn (RingHom.id ℂ) F S).isInducing.eq_induced
  have hP := (PointwiseConvergenceCLM.isEmbedding_coeFn (RingHom.id ℂ) E F).isInducing.eq_induced
  have h := EquicontinuousOn.comap_uniformOnFun_eq (𝔖 := S) (F := ff) (fun _ hs => hs)
    (fun s _ => he.equicontinuousOn s)
  have hCover : ⋃₀ S = univ := sUnion_isCompact_eq_univ
  let e : ((⋃₀ S) → F) ≃ᵤ (E → F) := UniformEquiv.piCongrLeft (β := fun _ => F)
    (Equiv.subtypeUnivEquiv (eq_univ_iff_forall.mp hCover))
  have hE : IsUniformInducing ((⋃₀ S).domRestrict : (E → F) → ((⋃₀ S) → F)) := e.symm.isUniformInducing
  have h' := congrArg (fun t : UniformSpace H => @UniformSpace.toTopologicalSpace H t) h
  calc
    _ = (UniformOnFun.uniformSpace E F S |>.comap ff).toTopologicalSpace := by
      have hh := congrArg (TopologicalSpace.induced (fun f : H => (f.val : E →L_c[ℂ] F))) hC
      exact hh.trans induced_compose
    _ = _ := h'
    _ = TopologicalSpace.induced ff (Pi.topologicalSpace : TopologicalSpace (E → F)) := by
      change TopologicalSpace.induced ((⋃₀ S).domRestrict ∘ ff) inferInstance = _
      exact induced_compose.symm.trans
        (congrArg (TopologicalSpace.induced ff) hE.isInducing.eq_induced.symm)
    _ = _ := by
      have hh := congrArg (TopologicalSpace.induced (fun f : H => (f.val : E →Lₚₜ[ℂ] F))) hP
      exact (hh.trans induced_compose).symm

end Equicontinuous

section StrongOperator

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

private abbrev normedOperator (f : E →Lₚₜ[ℂ] F) : E →L[ℂ] F := f

private theorem strongOperator_normBound (B : Set (E →Lₚₜ[ℂ] F)) (hb : IsVonNBounded ℂ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : B, ‖normedOperator f.val‖ ≤ C := by
  let g (f : B) : E →L[ℂ] F := f.val
  have h (x : E) : ∃ C, ∀ f : B, ‖g f x‖ ≤ C := by
    let e := PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) F x
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp (NormedSpace.isVonNBounded_iff ℂ |>.mp (hb.image e))
    exact ⟨C, fun f => hC _ (mem_image_of_mem e f.property)⟩
  obtain ⟨C, hC⟩ := banach_steinhaus h
  exact ⟨max 1 C, lt_of_lt_of_le zero_lt_one (le_max_left _ _), fun f => (hC f).trans (le_max_right _ _)⟩

/-- Lemma C.3.3.1(1). On a bounded set of operators, evaluations on a
countable dense subset determine the strong operator topology. -/
theorem strongOperator_bounded_metrizable [SeparableSpace E]
    (B : Set (E →Lₚₜ[ℂ] F)) (hb : IsVonNBounded ℂ B) : MetrizableSpace B := by
  obtain ⟨D, hDc, hD⟩ := TopologicalSpace.exists_countable_dense E
  letI : Countable D := hDc.to_subtype
  obtain ⟨C, hC, hnorm⟩ := strongOperator_normBound B hb
  let ev (f : B) (x : D) : F := f.val x
  have h_cont : Continuous ev := continuous_pi fun x =>
    (PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) F (x : E)).continuous.comp continuous_subtype_val
  have h_inj : Injective ev := by
    intro f g hfg
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro x
    exact congrFun (Continuous.ext_on hD f.val.continuous g.val.continuous (fun y hy => congrFun hfg ⟨y, hy⟩)) x
  let t₀ : TopologicalSpace B := inferInstance
  let t₁ := TopologicalSpace.induced ev inferInstance
  have hle : t₀ ≤ t₁ := continuous_iff_le_induced.mp h_cont
  have hle' : t₁ ≤ t₀ := by
    letI : TopologicalSpace B := t₁
    have hpoint (x : E) : Continuous (fun f : B => f.val x) := by
      apply continuous_iff_continuousAt.mpr
      intro f
      apply Metric.tendsto_nhds.mpr
      intro ε hε
      obtain ⟨y, hy, hxy⟩ := hD.exists_dist_lt x (show 0 < ε / (3 * C) by positivity)
      have hCxy : C * dist x y < ε / 3 := by
        have h := (lt_div_iff₀ (show 0 < 3 * C by positivity)).mp hxy
        linarith
      have hey : Continuous (fun g : B => g.val y) :=
        (continuous_apply (⟨y, hy⟩ : D)).comp (continuous_induced_dom : Continuous ev)
      filter_upwards [Metric.tendsto_nhds.mp (hey.continuousAt (x := f)).tendsto
        (ε / 3) (by positivity)] with g hg
      have hdist (a : B) : dist (a.val x) (a.val y) < ε / 3 := by
        calc
          dist (a.val x) (a.val y) = ‖a.val (x - y)‖ := by rw [dist_eq_norm, map_sub]
          _ ≤ ‖normedOperator a.val‖ * dist x y := by
            rw [dist_eq_norm]
            exact (normedOperator a.val).le_opNorm _
          _ ≤ C * dist x y := mul_le_mul_of_nonneg_right (hnorm a) dist_nonneg
          _ < ε / 3 := hCxy
      have h := dist_triangle (g.val x) (g.val y) (f.val x)
      have h' := dist_triangle (g.val y) (f.val y) (f.val x)
      rw [dist_comm (f.val y) (f.val x)] at h'
      linarith [hdist f, hdist g]
    have hincl : Continuous (fun f : B => (f.val : E →Lₚₜ[ℂ] F)) :=
      PointwiseConvergenceCLM.continuous_of_continuous_eval hpoint
    exact continuous_iff_le_induced.mp hincl
  have heq : t₀ = t₁ := le_antisymm hle hle'
  letI : TopologicalSpace B := t₀
  have hemp : @IsEmbedding B (D → F) t₀ Pi.topologicalSpace ev := ⟨⟨heq⟩, h_inj⟩
  exact hemp.metrizableSpace

/-- Lemma C.3.3.1(2), with arbitrary Banach source and target. -/
theorem strongOperator_quasiComplete [CompleteSpace F] :
    T2Space (E →Lₚₜ[ℂ] F) ∧ LocallyConvexSpace ℝ (E →Lₚₜ[ℂ] F) ∧
      QuasiCompleteSpace ℂ (E →Lₚₜ[ℂ] F) := by
  letI : Module ℝ F := Module.restrictScalars ℝ ℂ F
  haveI : IsScalarTower ℝ ℂ F := IsScalarTower.restrictScalars ℝ ℂ F
  letI : NormedSpace ℝ F := NormedSpace.restrictScalars ℝ ℂ F
  exact ⟨inferInstance, inferInstance,
    mappingSpace_quasiComplete (E := E) (F := F) {s | s.Finite} Set.sUnion_finite_eq_univ⟩

end StrongOperator

end Masullo
