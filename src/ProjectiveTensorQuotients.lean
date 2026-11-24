import InductiveTensorTopology
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Topology.Algebra.IsUniformGroup.Basic
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

open Filter Function Set Topology UniformSpace
open scoped ComplexOrder Pointwise TensorProduct Uniformity

namespace Masullo

noncomputable section

variable {E F E' F' : Type*}
variable [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [PolynormableSpace ℂ E]
variable [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] [PolynormableSpace ℂ F]
variable [AddCommGroup E'] [Module ℂ E'] [TopologicalSpace E'] [PolynormableSpace ℂ E']
variable [AddCommGroup F'] [Module ℂ F'] [TopologicalSpace F'] [PolynormableSpace ℂ F']

private theorem absConvexHull_image_linear {X Y : Type*}
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (f : X →ₗ[ℂ] Y) (s : Set X) :
    f '' absConvexHull ℂ s = absConvexHull ℂ (f '' s) := by
  apply Subset.antisymm
  · exact image_subset_iff.mpr (absConvexHull_min
      (fun x hx => subset_absConvexHull (mem_image_of_mem f hx))
      ⟨(balanced_absConvexHull (𝕜 := ℂ)).mulActionHom_preimage f.toMulActionHom,
        (convex_absConvexHull (𝕜 := ℂ)).linear_preimage f⟩)
  · apply absConvexHull_min (image_mono subset_absConvexHull)
    refine ⟨balanced_iff_smul_mem.mpr ?_, (convex_absConvexHull (𝕜 := ℂ)).linear_image f⟩
    rintro c hc _ ⟨x, hx, rfl⟩
    exact ⟨c • x, balanced_iff_smul_mem.mp (balanced_absConvexHull (𝕜 := ℂ)) hc hx, f.map_smul c x⟩

private def elementaryTensorHull' (U : Set E) (V : Set F) : Set (E ⊗[ℂ] F) :=
  absConvexHull ℂ (image2 (TensorProduct.tmul ℂ) U V)

private theorem elementaryTensorHull_absorbent {U : Set E} {V : Set F}
    (hU : U ∈ 𝓝 0) (hV : V ∈ 𝓝 0) : Absorbent ℝ (elementaryTensorHull' U V) := by
  letI : ContinuousSMul ℂ E := (PolynormableSpace.withSeminorms ℂ E).continuousSMul
  letI : ContinuousSMul ℂ F := (PolynormableSpace.withSeminorms ℂ F).continuousSMul
  letI : ContinuousSMul ℝ E := IsScalarTower.continuousSMul ℂ
  letI : ContinuousSMul ℝ F := IsScalarTower.continuousSMul ℂ
  have hC : Convex ℝ (elementaryTensorHull' U V) := (convex_absConvexHull (𝕜 := ℂ)).lift ℝ
  have h0 : 0 ∈ elementaryTensorHull' U V := by
    exact subset_absConvexHull ⟨0, mem_of_mem_nhds hU, 0, mem_of_mem_nhds hV, by simp⟩
  apply absorbent_iff_eventually_nhdsNE_zero.mpr
  intro z
  suffices h : ∀ᶠ c : ℝ in 𝓝 0, c • z ∈ elementaryTensorHull' U V from
    h.filter_mono nhdsWithin_le_nhds
  induction z using TensorProduct.induction_on with
  | zero =>
    exact Eventually.of_forall fun c => by
      change (c : ℂ) • (0 : E ⊗[ℂ] F) ∈ elementaryTensorHull' U V
      rwa [smul_zero]
  | tmul x y =>
    obtain ⟨r, hr, hy⟩ := ((absorbent_nhds_zero (𝕜 := ℝ) hV).eventually_nhdsNE_zero y).and
      self_mem_nhdsWithin |>.exists
    -- First choose a fixed nonzero scaling of the second factor.
    have hr₀ : r ≠ 0 := hy
    have h := ((continuous_id.mul (continuous_const (y := r⁻¹))).smul
      (continuous_const (y := x))).tendsto' (0 : ℝ) 0 (by simp)
    filter_upwards [h hU] with c hc
    apply subset_absConvexHull
    refine ⟨(c * r⁻¹) • x, hc, r • y, hr, ?_⟩
    rw [TensorProduct.tmul_smul, ← TensorProduct.smul_tmul']
    apply congrArg (fun u : E => u ⊗ₜ[ℂ] y)
    change (r : ℂ) • (↑(c * r⁻¹) : ℂ) • x = (c : ℂ) • x
    rw [smul_smul, ← Complex.ofReal_mul, show r * (c * r⁻¹) = c by field_simp]
  | add x y hx hy =>
    have hd := (continuous_const.mul continuous_id).tendsto' (0 : ℝ) 0 (mul_zero (2 : ℝ))
    filter_upwards [hd.eventually hx, hd.eventually hy] with c hc hc'
    have h := hC hc hc' (show (0 : ℝ) ≤ 1 / 2 by norm_num)
      (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (1 : ℝ) / 2 + 1 / 2 = 1 by norm_num)
    change ((↑(1 / 2 : ℝ) : ℂ) • ((↑(2 * c) : ℂ) • x) +
      (↑(1 / 2 : ℝ) : ℂ) • ((↑(2 * c) : ℂ) • y)) ∈ elementaryTensorHull' U V at h
    change (c : ℂ) • (x + y) ∈ elementaryTensorHull' U V
    rw [smul_add]
    simpa only [smul_smul, ← Complex.ofReal_mul,
      show (1 / 2 : ℝ) * (2 * c) = c by ring] using h

private theorem elementaryTensorHull_mem_nhds {U : Set E} {V : Set F}
    (hU : U ∈ 𝓝 0) (hV : V ∈ 𝓝 0) :
    elementaryTensorHull' U V ∈ @nhds (E ⊗[ℂ] F) (projectiveTensorTopology E F) 0 := by
  letI : TopologicalSpace (E ⊗[ℂ] F) := projectiveTensorTopology E F
  let S := elementaryTensorHull' U V
  change S ∈ 𝓝 0
  have hA := elementaryTensorHull_absorbent hU hV
  have hC : Convex ℝ S := (convex_absConvexHull (𝕜 := ℂ)).lift ℝ
  let q : Seminorm ℂ (E ⊗[ℂ] F) := gaugeSeminorm balanced_absConvexHull hC hA
  obtain ⟨p, r, hp, hr, hb⟩ := bilinear_bound_of_nhds (TensorProduct.mk ℂ E F) q (by
    rw [nhds_prod_eq]
    refine Filter.mem_prod_iff.mpr ⟨U, hU, V, hV, ?_⟩
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    exact gauge_le_one_of_mem (subset_absConvexHull ⟨x, hx, y, hy, rfl⟩))
  let P : ProjectiveTensorTest E F := ⟨q, p, r, hp, hr, hb⟩
  exact mem_of_superset ((projectiveTensor_withSeminorms.continuous_seminorm P).continuousAt.tendsto
      (Iio_mem_nhds (show (P.tensor 0) < 1 by simp)))
    (fun _ hx => setOfPred_gauge_lt_one_subset_self hC hA.zero_mem hA hx)

/-- Absolute convex hulls of elementary tensors give a zero-neighborhood basis. -/
theorem elementaryTensorHull_basis {ι κ : Type*} {p : ι → Prop} {r : κ → Prop}
    {U : ι → Set E} {V : κ → Set F}
    (hU : (𝓝 0).HasBasis p U) (hV : (𝓝 0).HasBasis r V) :
    (@nhds (E ⊗[ℂ] F) (projectiveTensorTopology E F) 0).HasBasis
      (fun ij : ι × κ => p ij.1 ∧ r ij.2) (fun ij => elementaryTensorHull' (U ij.1) (V ij.2)) := by
  letI : TopologicalSpace (E ⊗[ℂ] F) := projectiveTensorTopology E F
  apply Filter.hasBasis_iff.mpr
  intro W
  constructor
  · intro hW
    letI : IsTopologicalAddGroup E := (PolynormableSpace.withSeminorms ℂ E).topologicalAddGroup
    letI : IsTopologicalAddGroup F := (PolynormableSpace.withSeminorms ℂ F).topologicalAddGroup
    letI : IsTopologicalAddGroup (E ⊗[ℂ] F) := projectiveTensor_withSeminorms.topologicalAddGroup
    obtain ⟨⟨I, ε⟩, hε, hAW⟩ := projectiveTensor_withSeminorms.hasBasis_zero_ball.mem_iff.mp hW
    let q := I.sup (ProjectiveTensorTest.tensor (E := E) (F := F))
    have hA : q.ball 0 ε ∈ 𝓝 (0 : E ⊗[ℂ] F) :=
      projectiveTensor_withSeminorms.hasBasis_zero_ball.mem_of_mem (i := (I, ε)) hε
    have hAc : AbsConvex ℂ (q.ball 0 ε) :=
      ⟨q.balanced_ball_zero _, convex_of_nonneg_surjective_algebraMap ℂ
        (fun _ => (RCLike.nonneg_iff_exists_ofReal (K := ℂ)).mp) (q.convex_ball _ _)⟩
    have h := continuous_projectiveTensor_tmul.tendsto' (0, 0) 0 (by simp) hA
    rw [nhds_prod_eq] at h
    obtain ⟨U', hU', V', hV', hUV⟩ := Filter.mem_prod_iff.mp h
    obtain ⟨i, hi, hUi⟩ := hU.mem_iff.mp hU'
    obtain ⟨j, hj, hVj⟩ := hV.mem_iff.mp hV'
    refine ⟨(i, j), ⟨hi, hj⟩, (absConvexHull_min ?_ hAc).trans hAW⟩
    rintro _ ⟨x, hx, y, hy, rfl⟩
    exact hUV (show (x, y) ∈ U' ×ˢ V' from ⟨hUi hx, hVj hy⟩)
  · rintro ⟨⟨i, j⟩, ⟨hi, hj⟩, h⟩
    exact mem_of_superset (elementaryTensorHull_mem_nhds (hU.mem_of_mem hi) (hV.mem_of_mem hj)) h

/-- Tensoring two linear quotient maps gives an open surjection for the algebraic
projective tensor topologies. -/
theorem projectiveTensor_map_openQuotient (f : E →L[ℂ] E') (g : F →L[ℂ] F')
    (hf : IsQuotientMap f) (hg : IsQuotientMap g) :
    @IsOpenQuotientMap (E ⊗[ℂ] F) (E' ⊗[ℂ] F')
      (projectiveTensorTopology E F) (projectiveTensorTopology E' F')
      (TensorProduct.map f.toLinearMap g.toLinearMap) := by
  letI : TopologicalSpace (E ⊗[ℂ] F) := projectiveTensorTopology E F
  letI : TopologicalSpace (E' ⊗[ℂ] F') := projectiveTensorTopology E' F'
  letI : IsTopologicalAddGroup E := (PolynormableSpace.withSeminorms ℂ E).topologicalAddGroup
  letI : IsTopologicalAddGroup F := (PolynormableSpace.withSeminorms ℂ F).topologicalAddGroup
  letI : IsTopologicalAddGroup E' := (PolynormableSpace.withSeminorms ℂ E').topologicalAddGroup
  letI : IsTopologicalAddGroup F' := (PolynormableSpace.withSeminorms ℂ F').topologicalAddGroup
  letI : IsTopologicalAddGroup (E ⊗[ℂ] F) := projectiveTensor_withSeminorms.topologicalAddGroup
  letI : IsTopologicalAddGroup (E' ⊗[ℂ] F') := projectiveTensor_withSeminorms.topologicalAddGroup
  let L := TensorProduct.map f.toLinearMap g.toLinearMap
  refine ⟨TensorProduct.map_surjective hf.surjective hg.surjective,
    projectiveTensor_map_continuous f g, ?_⟩
  apply (IsTopologicalAddGroup.isOpenMap_iff_nhds_zero (f := L.toAddMonoidHom)).mpr
  intro W hW
  obtain ⟨⟨U, V⟩, ⟨hU, hV⟩, hsub⟩ := (elementaryTensorHull_basis
    ((𝓝 (0 : E)).basis_sets) ((𝓝 (0 : F)).basis_sets)).mem_iff.mp (mem_map.mp hW)
  have hfU : f '' U ∈ 𝓝 0 := by
    rw [← f.map_zero]
    exact (AddMonoidHom.isOpenQuotientMap_of_isQuotientMap
      (φ := f.toAddMonoidHom) hf).isOpenMap
      |>.image_mem_nhds hU
  have hgV : g '' V ∈ 𝓝 0 := by
    rw [← g.map_zero]
    exact (AddMonoidHom.isOpenQuotientMap_of_isQuotientMap
      (φ := g.toAddMonoidHom) hg).isOpenMap
      |>.image_mem_nhds hV
  refine mem_of_superset (elementaryTensorHull_mem_nhds hfU hgV) ?_
  intro z hz
  have he : L '' elementaryTensorHull' U V = elementaryTensorHull' (f '' U) (g '' V) := by
    unfold elementaryTensorHull'
    rw [absConvexHull_image_linear]
    congr 1
    ext w
    constructor
    · rintro ⟨_, ⟨x, hx, y, hy, rfl⟩, rfl⟩
      exact ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, (TensorProduct.map_tmul _ _ _ _).symm⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨_, ⟨x, hx, y, hy, rfl⟩, TensorProduct.map_tmul _ _ _ _⟩
  obtain ⟨x, hx, rfl⟩ := he ▸ hz
  exact hsub hx

section CompletionQuotient

variable {X Y : Type*} [AddCommGroup X] [UniformSpace X] [IsUniformAddGroup X]
variable [AddCommGroup Y] [UniformSpace Y] [IsUniformAddGroup Y]

/-- An open homomorphism stays open onto its image after additive completion. -/
private theorem completion_isOpenQuotient_range (f : X →+ Y) (hf : Continuous f)
    (hopen : IsOpenMap f) :
    IsOpenQuotientMap (f.completion hf).rangeRestrict := by
  let F := f.completion hf
  let L := F.rangeRestrict
  have hF : Continuous F := Completion.continuous_map
  refine ⟨F.rangeRestrict_surjective, hF.subtype_mk _, ?_⟩
  apply (IsTopologicalAddGroup.isOpenMap_iff_nhds_zero (f := L)).mpr
  intro W hW
  obtain ⟨U, hUo, hU₀, hUW⟩ := exists_open_nhds_zero_add_subset (mem_map.mp hW)
  let A := f '' (Completion.coe' ⁻¹' U)
  have hAo : IsOpen A := hopen _ (hUo.preimage (Completion.continuous_coe X))
  have hA₀ : (0 : Y) ∈ A := ⟨0, by rw [mem_preimage, Completion.coe_zero]; exact hU₀, f.map_zero⟩
  have hcoe : IsInducing (Completion.coe' : Y → Completion Y) :=
    (Completion.isUniformInducing_coe Y).isInducing
  have hAn : A ∈ 𝓝 (0 : Y) := hAo.mem_nhds hA₀
  rw [hcoe.nhds_eq_comap 0, Completion.coe_zero] at hAn
  obtain ⟨V, hVn, hVA⟩ := mem_comap.mp hAn
  obtain ⟨V', hV'V, hV'o, hV'₀⟩ := _root_.mem_nhds_iff.mp hVn
  have hpre : (Subtype.val : F.range → Completion Y) ⁻¹' V' ∈ 𝓝 (0 : F.range) :=
    (hV'o.preimage continuous_subtype_val).mem_nhds hV'₀
  refine mem_of_superset hpre ?_
  rintro ⟨y, x, rfl⟩ hxy
  have hx : x ∈ {u : Completion X | x - u ∈ U} ∩ F ⁻¹' V' := by
    exact ⟨show x - x ∈ U by rwa [sub_self], hxy⟩
  have hO : IsOpen ({u : Completion X | x - u ∈ U} ∩ F ⁻¹' V') :=
    (hUo.preimage (continuous_const.sub continuous_id)).inter (hV'o.preimage hF)
  obtain ⟨a, haU, haV⟩ := Completion.denseRange_coe.exists_mem_open hO ⟨x, hx⟩
  have hfa : (f a : Completion Y) = F (a : Completion X) :=
    (AddMonoidHom.completion_coe f hf a).symm
  change F (a : Completion X) ∈ V' at haV
  have haA : f a ∈ A := hVA (hV'V (hfa.symm ▸ haV))
  obtain ⟨b, hbU, hba⟩ := haA
  let x' := x - (a : Completion X) + (b : Completion X)
  have hx' : x' ∈ L ⁻¹' W := hUW (Set.add_mem_add haU hbU)
  have he : L x' = ⟨F x, x, rfl⟩ := by
    apply Subtype.ext
    change F (x - (a : Completion X) + (b : Completion X)) = F x
    rw [map_add, map_sub]
    have ha := AddMonoidHom.completion_coe f hf a
    have hb := AddMonoidHom.completion_coe f hf b
    rw [show F (a : Completion X) = f a from ha, show F (b : Completion X) = f b from hb]
    rw [hba, sub_add_cancel]
  simpa only [mem_preimage, he] using hx'

/-- Countability of the zero-neighborhood filter passes to the completion. -/
private theorem completion_firstCountable [(𝓝 (0 : X)).IsCountablyGenerated] :
    FirstCountableTopology (Completion X) := by
  let ι : X → Completion X := Completion.coe'
  have hi := (Completion.isUniformInducing_coe X).isInducing
  obtain ⟨B, hB, -⟩ := (𝓝 (0 : X)).exists_antitone_basis
  have hlift (n : ℕ) : ∃ U : Set (Completion X), IsOpen U ∧ 0 ∈ U ∧ ι ⁻¹' U ⊆ B n := by
    have hb := hB.mem_of_mem (i := n) trivial
    rw [hi.nhds_eq_comap 0, Completion.coe_zero] at hb
    obtain ⟨U, hU, hUB⟩ := mem_comap.mp hb
    obtain ⟨V, hVU, hVo, hV₀⟩ := _root_.mem_nhds_iff.mp hU
    exact ⟨V, hVo, hV₀, (preimage_mono hVU).trans hUB⟩
  choose U hUo hU₀ hUB using hlift
  have hU : (𝓝 (0 : Completion X)).HasBasis (fun _ : ℕ => True) U := by
    apply Filter.hasBasis_iff.mpr
    intro W
    constructor
    · intro hW
      obtain ⟨C, ⟨hC, hc⟩, hCW⟩ := (closed_nhds_basis (0 : Completion X)).mem_iff.mp hW
      have hpC : ι ⁻¹' C ∈ 𝓝 (0 : X) := by
        rw [hi.nhds_eq_comap 0, Completion.coe_zero]
        exact preimage_mem_comap hC
      obtain ⟨n, -, hb⟩ := hB.mem_iff.mp hpC
      refine ⟨n, trivial, fun x hx => hCW ?_⟩
      have hr := (hUo n).inter_closure (t := range ι)
      have hd : closure (range ι) = univ := Completion.denseRange_coe.closure_range
      rw [hd, inter_univ] at hr
      refine closure_minimal ?_ hc (hr hx)
      rintro _ ⟨h₁, y, rfl⟩
      exact hb (hUB n h₁)
    · rintro ⟨n, -, hn⟩
      exact mem_of_superset ((hUo n).mem_nhds (hU₀ n)) hn
  letI : (𝓝 (0 : Completion X)).IsCountablyGenerated := hU.isCountablyGenerated
  letI : (𝓤 (Completion X)).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  infer_instance

private theorem completion_surjective_of_openQuotient (f : X →+ Y) (hf : IsOpenQuotientMap f)
    [(𝓝 (0 : X)).IsCountablyGenerated] :
    Surjective (f.completion hf.continuous) := by
  letI : FirstCountableTopology (Completion X) := completion_firstCountable
  let F := f.completion hf.continuous
  let e := QuotientAddGroup.quotientKerEquivRange F
  letI : UniformSpace (Completion X ⧸ F.ker) := IsTopologicalAddGroup.rightUniformSpace _
  letI : IsUniformAddGroup (Completion X ⧸ F.ker) :=
    isUniformAddGroup_of_addCommGroup
  letI : CompleteSpace (Completion X ⧸ F.ker) :=
    QuotientAddGroup.completeSpace_right (Completion X) F.ker
  have hL := completion_isOpenQuotient_range f hf.continuous hf.isOpenMap
  let q := QuotientAddGroup.mk' F.ker
  have he : (e : (Completion X ⧸ F.ker) → F.range) ∘ q = F.rangeRestrict := rfl
  have hcont : Continuous e := (QuotientAddGroup.isQuotientMap_mk F.ker).continuous_iff.mpr
    (he.symm ▸ hL.continuous)
  have hopen : IsOpenMap e := by
    intro V hV
    rw [← image_preimage_eq V (QuotientAddGroup.mk'_surjective F.ker), image_image]
    change IsOpen (((e : (Completion X ⧸ F.ker) → F.range) ∘ q) '' (q ⁻¹' V))
    rw [he]
    exact hL.isOpenMap _ (hV.preimage QuotientAddGroup.continuous_mk)
  have hunif : IsUniformInducing e := AddMonoidHom.isUniformInducing_of_isInducing
    ((IsOpenEmbedding.of_continuous_injective_isOpenMap hcont e.injective hopen).isInducing)
  have hcomplete : IsComplete (range (F : Completion X → Completion Y)) := by
    have h := (isUniformEmbedding_subtype_val (p := (· ∈ (F.range : Set (Completion Y))))).isUniformInducing
    have hr := (h.comp hunif).isComplete_range
    change IsComplete (range ((Subtype.val : F.range → Completion Y) ∘ e)) at hr
    rw [range_comp, e.surjective.range_eq, image_univ, Subtype.range_coe] at hr
    exact hr
  have hdense : DenseRange (F : Completion X → Completion Y) := by
    apply Completion.denseRange_coe.mono
    rintro _ ⟨y, rfl⟩
    obtain ⟨x, rfl⟩ := hf.surjective y
    exact ⟨(x : Completion X), AddMonoidHom.completion_coe f hf.continuous x⟩
  exact range_eq_univ.mp (hdense.closure_range ▸ hcomplete.isClosed.closure_eq.symm)

end CompletionQuotient

/-- The canonical tensor map on the actual separated projective completions. -/
def completedProjectiveTensorMap (f : E →L[ℂ] E') (g : F →L[ℂ] F') :
    (projectiveTensorModuleStructure E F).Completed →L[ℂ] (projectiveTensorModuleStructure E' F').Completed := by
  let X := projectiveTensorModuleStructure E F
  let Y := projectiveTensorModuleStructure E' F'
  letI : UniformSpace (E ⊗[ℂ] F) := X.uniformSpace
  letI : IsUniformAddGroup (E ⊗[ℂ] F) := X.uniformGroup
  letI : UniformContinuousConstSMul ℂ (E ⊗[ℂ] F) := X.uniformConstSmul
  letI : UniformSpace (E' ⊗[ℂ] F') := Y.uniformSpace
  letI : IsUniformAddGroup (E' ⊗[ℂ] F') := Y.uniformGroup
  letI : UniformContinuousConstSMul ℂ (E' ⊗[ℂ] F') := Y.uniformConstSmul
  let L : (E ⊗[ℂ] F) →L[ℂ] (E' ⊗[ℂ] F') :=
    ⟨TensorProduct.map f.toLinearMap g.toLinearMap, projectiveTensor_map_continuous f g⟩
  exact L.completion

/-- C.2.3.7. The completed tensor map of two quotient maps is open onto its
range with the subspace topology. -/
theorem completedProjectiveTensorMap_isOpenQuotient_range
    (f : E →L[ℂ] E') (g : F →L[ℂ] F') (hf : IsQuotientMap f) (hg : IsQuotientMap g) :
    IsOpenQuotientMap (Set.rangeFactorization (completedProjectiveTensorMap f g)) := by
  letI : UniformSpace (E ⊗[ℂ] F) := (projectiveTensorModuleStructure E F).uniformSpace
  letI : IsUniformAddGroup (E ⊗[ℂ] F) := (projectiveTensorModuleStructure E F).uniformGroup
  letI : UniformSpace (E' ⊗[ℂ] F') := (projectiveTensorModuleStructure E' F').uniformSpace
  letI : IsUniformAddGroup (E' ⊗[ℂ] F') := (projectiveTensorModuleStructure E' F').uniformGroup
  exact completion_isOpenQuotient_range
    (TensorProduct.map f.toLinearMap g.toLinearMap).toAddMonoidHom
    (projectiveTensor_map_continuous f g) (projectiveTensor_map_openQuotient f g hf hg).isOpenMap

/-- C.2.3.7. Metrizability of the two source factors gives surjectivity on
the completed projective tensor product. -/
theorem completedProjectiveTensorMap_surjective
    [FirstCountableTopology E] [FirstCountableTopology F]
    (f : E →L[ℂ] E') (g : F →L[ℂ] F') (hf : IsQuotientMap f) (hg : IsQuotientMap g) :
    Surjective (completedProjectiveTensorMap f g) := by
  letI : UniformSpace (E ⊗[ℂ] F) := (projectiveTensorModuleStructure E F).uniformSpace
  letI : IsUniformAddGroup (E ⊗[ℂ] F) := (projectiveTensorModuleStructure E F).uniformGroup
  letI : UniformSpace (E' ⊗[ℂ] F') := (projectiveTensorModuleStructure E' F').uniformSpace
  letI : IsUniformAddGroup (E' ⊗[ℂ] F') := (projectiveTensorModuleStructure E' F').uniformGroup
  obtain ⟨U, hU, -⟩ := (𝓝 (0 : E)).exists_antitone_basis
  obtain ⟨V, hV, -⟩ := (𝓝 (0 : F)).exists_antitone_basis
  letI : (𝓝 (0 : E ⊗[ℂ] F)).IsCountablyGenerated :=
    (elementaryTensorHull_basis hU hV).isCountablyGenerated
  exact completion_surjective_of_openQuotient
    (TensorProduct.map f.toLinearMap g.toLinearMap).toAddMonoidHom
    (projectiveTensor_map_openQuotient f g hf hg)

end

end Masullo
