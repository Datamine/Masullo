import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.LocallyConvex.Barrelled
import Mathlib.Analysis.Convex.Hull
import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.Topology.Algebra.MulAction

open Filter Set Topology
open scoped Topology Uniformity TensorProduct

namespace Masullo

private theorem continuous_action_of_continuousAt_zero_and_orbits
    {H E : Type*} [Monoid H] [TopologicalSpace H] [AddCommGroup E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [DistribMulAction H E]
    (hz : ∀ h : H, ContinuousAt (fun p : H × E => p.1 • p.2) (h, 0))
    (ho : ∀ x : E, Continuous (fun h : H => h • x)) :
    Continuous (fun p : H × E => p.1 • p.2) := by
  apply continuous_iff_continuousAt.mpr
  rintro ⟨h, x⟩
  have hc : Continuous (fun p : H × E => (p.1, p.2 - x)) :=
    continuous_fst.prodMk (continuous_snd.sub continuous_const)
  have hshift : Tendsto (fun p : H × E => (p.1, p.2 - x)) (𝓝 (h, x)) (𝓝 (h, 0)) := by
    simpa only [sub_self] using (hc.continuousAt (x := (h, x))).tendsto
  have hlim : Tendsto (fun p : H × E => p.1 • (p.2 - x)) (𝓝 (h, x)) (𝓝 (0 : E)) := by
    simpa only [Function.comp_def, smul_zero] using (hz h).tendsto.comp hshift
  have ht : Tendsto (fun p : H × E => p.1 • x) (𝓝 (h, x)) (𝓝 (h • x)) :=
    ((ho x).comp continuous_fst).continuousAt
  simpa only [ContinuousAt, smul_sub, sub_add_cancel, zero_add] using hlim.add ht

/-- D.1.9.1. The strict inductive limit realizes its stages as subspaces.
The locally convex final topology tests continuity of a seminorm on all
the stages. A compatible continuous action on the stages is jointly
continuous on the limit. -/
theorem continuous_action_of_strict_stages
    {H E : Type*} [Group H] [TopologicalSpace H] [LocallyCompactSpace H]
    [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E]
    [ContinuousSMul ℂ E] [PolynormableSpace ℂ E]
    [DistribMulAction H E] [SMulCommClass H ℂ E]
    (U : ℕ → Subgroup H) (S : ℕ → Submodule ℂ E)
    (hU : ∀ n, IsOpen (U n : Set H)) (hUm : Monotone U) (hSm : Monotone S)
    (hUcov : ⋃ n, (U n : Set H) = univ) (hScov : ⋃ n, (S n : Set E) = univ)
    [hbar : ∀ n, BarrelledSpace ℂ (S n)]
    (hfinal : ∀ p : Seminorm ℂ E, (∀ n, ContinuousOn p (S n : Set E)) → Continuous p)
    (hstage : ∀ n, ContinuousOn (fun p : H × E => p.1 • p.2)
      ((U n : Set H) ×ˢ (S n : Set E))) :
    Continuous (fun p : H × E => p.1 • p.2) := by
  have hUex (h : H) : ∃ n, h ∈ U n := mem_iUnion.mp (hUcov.symm ▸ mem_univ h)
  have hSex (x : E) : ∃ n, x ∈ S n := mem_iUnion.mp (hScov.symm ▸ mem_univ x)
  let A (h : H) : E →ₗ[ℂ] E :=
    { toFun := (h • ·)
      map_add' := smul_add h
      map_smul' := fun c x => smul_comm h c x }
  have hOrbit (x : E) : Continuous (fun h : H => h • x) := by
    apply continuous_iff_continuousAt.mpr
    intro h
    obtain ⟨i, hi⟩ := hUex h
    obtain ⟨j, hj⟩ := hSex x
    let n := max i j
    have hhn : h ∈ U n := hUm (le_max_left _ _) hi
    have hxn : x ∈ S n := hSm (le_max_right _ _) hj
    have hc : ContinuousOn (fun k : H => k • x) (U n : Set H) :=
      (hstage n).comp (continuous_id.prodMk continuous_const).continuousOn
        (fun k hk => ⟨hk, hxn⟩)
    exact (hc h hhn).continuousAt ((hU n).mem_nhds hhn)
  have hConst (h : H) : Continuous (A h) := by
    apply (PolynormableSpace.withSeminorms ℂ E).continuous_of_continuous_comp
    intro p
    apply hfinal
    intro j
    obtain ⟨i, hi⟩ := hUex h
    let n := max i j
    exact p.property.comp_continuousOn ((hstage n).comp
      (continuous_const.prodMk continuous_id).continuousOn
      (fun x hx => ⟨hUm (le_max_left _ _) hi, hSm (le_max_right _ _) hx⟩))
  letI : BarrelledSpace ℂ E := ⟨fun p hp => hfinal p fun n =>
    continuousOn_iff_continuous_domRestrict.mpr
      ((p.comp (S n).subtype).continuous_of_lowerSemicontinuous
        (hp.comp continuous_subtype_val))⟩
  let B (h : H) : E →L[ℂ] E := ⟨A h, hConst h⟩
  apply continuous_action_of_continuousAt_zero_and_orbits _ hOrbit
  intro h
  obtain ⟨K, hK, hKh⟩ := exists_compact_mem_nhds h
  have hbound (x : E) : Bornology.IsVonNBounded ℂ (range fun g : K => B g.val x) := by
    rw [show (range fun g : K => B g.val x) = (fun g : H => g • x) '' K from by
      ext v
      exact ⟨fun ⟨g, hg⟩ => ⟨g.val, g.property, hg⟩, fun ⟨g, hg, hv⟩ => ⟨⟨g, hg⟩, hv⟩⟩]
    exact ((hK.image (hOrbit x)).totallyBounded).isVonNBounded ℂ
  have he := (PolynormableSpace.banach_steinhaus (𝓕 := fun g : K => B g.val) hbound).equicontinuous
  rw [ContinuousAt]
  change Tendsto (fun p : H × E => p.1 • p.2) (𝓝 (h, 0)) (𝓝 (h • (0 : E)))
  rw [smul_zero]
  intro V hV
  change ∀ᶠ p : H × E in 𝓝 (h, 0), p.1 • p.2 ∈ V
  have hUV : {z : E × E | z.2 - z.1 ∈ V} ∈ 𝓤 E := by
    rw [uniformity_eq_comap_nhds_zero E]
    exact preimage_mem_comap hV
  have hy : ∀ᶠ p : H × E in 𝓝 (h, 0), ∀ g : K, g.val • p.2 ∈ V := by
    have hh := he 0 _ hUV
    have hT : Tendsto (Prod.snd : H × E → E) (𝓝 (h, 0)) (𝓝 0) :=
      continuous_snd.continuousAt
    filter_upwards [hT hh] with p hp g
    have hp' : g.val • p.2 - g.val • (0 : E) ∈ V := hp g
    simpa only [smul_zero, sub_zero] using hp'
  have hg : ∀ᶠ p : H × E in 𝓝 (h, 0), p.1 ∈ K := continuous_fst.continuousAt.tendsto hKh
  filter_upwards [hy, hg] with p hp hk
  exact hp ⟨p.1, hk⟩

/-- D.1.9.3, in the stronger form of a dense additive subgroup of a regular
topological vector space. Individual continuity on the ambient space
extends the uniform neighborhood estimate from the dense subgroup. -/
theorem continuous_action_of_dense_subgroup
    {H E : Type*} [Monoid H] [TopologicalSpace H]
    [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E] [RegularSpace E]
    [DistribMulAction H E]
    (S : AddSubgroup E) (hS : Dense (S : Set E))
    (hconst : ∀ h : H, Continuous (fun x : E => h • x))
    (hsmall : Continuous (fun p : H × S => p.1 • (p.2 : E))) :
    Continuous (fun p : H × E => p.1 • p.2) := by
  have hcontrol (h : H) (V : Set E) (hV : V ∈ 𝓝 (0 : E)) :
      ∃ W ∈ 𝓝 h, ∃ O ∈ 𝓝 (0 : E), ∀ g ∈ W, ∀ y ∈ O, g • y ∈ V := by
    obtain ⟨F, hF, hFc, hFV⟩ := exists_mem_nhds_isClosed_subset hV
    have hP : {p : H × S | p.1 • (p.2 : E) ∈ F} ∈ 𝓝 (h, (0 : S)) := by
      apply (hsmall.continuousAt (x := (h, (0 : S)))).tendsto
      change F ∈ 𝓝 (h • (0 : E))
      simpa only [smul_zero] using hF
    rw [nhds_prod_eq] at hP
    obtain ⟨W, hW, D, hD, hWD⟩ := Filter.mem_prod_iff.mp hP
    have hi : IsInducing (Subtype.val : S → E) := ⟨rfl⟩
    rw [hi.nhds_eq_comap] at hD
    obtain ⟨T, hT, hTD⟩ := mem_comap.mp hD
    obtain ⟨O, hOT, hOo, hO0⟩ := mem_nhds_iff.mp hT
    refine ⟨W, hW, O, hOo.mem_nhds hO0, fun g hg y hy => hFV ?_⟩
    have hclosed : IsClosed ((fun z : E => g • z) ⁻¹' F) := hFc.preimage (hconst g)
    have hsub : O ∩ (S : Set E) ⊆ (fun z : E => g • z) ⁻¹' F := by
      intro z hz
      let u : S := ⟨z, hz.2⟩
      have hu : u ∈ D := hTD (show u.val ∈ T from hOT hz.1)
      exact hWD (show (g, u) ∈ W ×ˢ D from ⟨hg, hu⟩)
    exact closure_minimal hsub hclosed (hS.open_subset_closure_inter hOo hy)
  have hz (h : H) : ContinuousAt (fun p : H × E => p.1 • p.2) (h, 0) := by
    rw [ContinuousAt]
    change Tendsto (fun p : H × E => p.1 • p.2) (𝓝 (h, 0)) (𝓝 (h • (0 : E)))
    rw [smul_zero]
    intro V hV
    obtain ⟨W, hW, O, hO, hWOV⟩ := hcontrol h V hV
    change ∀ᶠ p : H × E in 𝓝 (h, 0), p.1 • p.2 ∈ V
    filter_upwards [continuous_fst.continuousAt.tendsto hW, continuous_snd.continuousAt.tendsto hO]
      with p hpW hpO using hWOV p.1 hpW p.2 hpO
  apply continuous_action_of_continuousAt_zero_and_orbits hz
  intro x
  apply continuous_iff_continuousAt.mpr
  intro h
  have hdiff : Tendsto (fun g : H => g • x - h • x) (𝓝 h) (𝓝 (0 : E)) := by
    intro U hU
    let F : E × E × E → E := fun p => p.1 + p.2.1 - p.2.2
    have hFc : Continuous F :=
      (continuous_fst.add (continuous_fst.comp continuous_snd)).sub (continuous_snd.comp continuous_snd)
    have hpre : F ⁻¹' U ∈ 𝓝 ((0 : E), (0 : E), (0 : E)) := by
      apply (hFc.continuousAt (x := ((0 : E), (0 : E), (0 : E)))).tendsto
      simpa [F] using hU
    rw [nhds_prod_eq] at hpre
    obtain ⟨V₁, hV₁, L, hL, hVL⟩ := Filter.mem_prod_iff.mp hpre
    rw [nhds_prod_eq] at hL
    obtain ⟨V₂, hV₂, V₃, hV₃, hLsub⟩ := Filter.mem_prod_iff.mp hL
    obtain ⟨W, hW, O, hO, hWOV⟩ := hcontrol h V₁ hV₁
    have ht : O ∩ (fun z : E => h • z) ⁻¹' V₃ ∈ 𝓝 (0 : E) :=
      inter_mem hO ((hconst h).continuousAt.tendsto (by simpa only [smul_zero] using hV₃))
    have hcx : Continuous (fun y : E => x - y) := continuous_const.sub continuous_id
    have hT : (fun y : E => x - y) ⁻¹' (O ∩ (fun z : E => h • z) ⁻¹' V₃) ∈ 𝓝 x :=
      hcx.continuousAt.tendsto (by simpa only [sub_self] using ht)
    obtain ⟨y, hyT, hyS⟩ := mem_closure_iff_nhds.mp (hS x) _ hT
    have hyO : x - y ∈ O := hyT.1
    have hy₃ : h • (x - y) ∈ V₃ := hyT.2
    have hc : Continuous (fun g : H => g • y - h • y) :=
      (hsmall.comp (continuous_id.prodMk (continuous_const (y := (⟨y, hyS⟩ : S))))).sub
        continuous_const
    have hVact : ∀ᶠ g in 𝓝 h, g • y - h • y ∈ V₂ :=
      hc.continuousAt.tendsto (by simpa only [sub_self] using hV₂)
    change ∀ᶠ g in 𝓝 h, g • x - h • x ∈ U
    filter_upwards [hW, hVact] with g hg hgy
    have hmem := hVL (show (g • (x - y), g • y - h • y, h • (x - y)) ∈ V₁ ×ˢ L from
      ⟨hWOV g hg _ hyO, hLsub ⟨hgy, hy₃⟩⟩)
    change g • (x - y) + (g • y - h • y) - h • (x - y) ∈ U at hmem
    convert hmem using 1
    simp only [smul_sub]
    abel
  simpa only [ContinuousAt, sub_add_cancel, zero_add] using
    hdiff.add (tendsto_const_nhds (x := h • x))

section ProjectiveTensor

variable {H E F : Type*} [Monoid H]
  [AddCommGroup E] [Module ℂ E] [DistribMulAction H E] [SMulCommClass H ℂ E]
  [AddCommGroup F] [Module ℂ F] [DistribMulAction H F] [SMulCommClass H ℂ F]

private def linearAction {V : Type*} [AddCommGroup V] [Module ℂ V]
    [DistribMulAction H V] [SMulCommClass H ℂ V] (h : H) : V →ₗ[ℂ] V where
  toFun := (h • ·)
  map_add' := smul_add h
  map_smul' := fun c x => smul_comm h c x

/-- The diagonal action on the algebraic tensor product. -/
@[instance_reducible]
def diagonalTensorAction : DistribMulAction H (E ⊗[ℂ] F) where
  smul h := TensorProduct.map (linearAction h) (linearAction h)
  one_smul x := by
    have he : TensorProduct.map (linearAction (1 : H) : E →ₗ[ℂ] E)
        (linearAction (1 : H) : F →ₗ[ℂ] F) = LinearMap.id := by
      apply TensorProduct.ext'
      intro e f
      simp [linearAction]
    exact DFunLike.congr_fun he x
  mul_smul g h x := by
    have he : TensorProduct.map (linearAction (g * h) : E →ₗ[ℂ] E)
        (linearAction (g * h) : F →ₗ[ℂ] F) =
        (TensorProduct.map (linearAction g) (linearAction g)).comp
          (TensorProduct.map (linearAction h) (linearAction h)) := by
      apply TensorProduct.ext'
      intro e f
      simp [linearAction, mul_smul]
    exact DFunLike.congr_fun he x
  smul_zero h := map_zero (TensorProduct.map (linearAction h) (linearAction h))
  smul_add h := map_add (TensorProduct.map (linearAction h) (linearAction h))

/-- The elementary tensors from a pair of subsets. -/
def tensorRectangle (V : Set E) (W : Set F) : Set (E ⊗[ℂ] F) :=
  (fun p : E × F => p.1 ⊗ₜ[ℂ] p.2) '' (V ×ˢ W)

variable [TopologicalSpace H] [TopologicalSpace E] [TopologicalSpace F]
  [TopologicalSpace (E ⊗[ℂ] F)] [IsTopologicalAddGroup (E ⊗[ℂ] F)]

/-- D.1.9.4. The diagonal action is continuous for the projective tensor
topology, expressed by its convex hulls of tensor rectangles at zero and
the continuous canonical bilinear map. -/
theorem continuous_diagonalTensorAction
    (hE : Continuous (fun p : H × E => p.1 • p.2))
    (hF : Continuous (fun p : H × F => p.1 • p.2))
    (htmul : Continuous (fun p : E × F => p.1 ⊗ₜ[ℂ] p.2))
    (hbase : letI : Module ℝ (E ⊗[ℂ] F) := Module.restrictScalars ℝ ℂ _
      (𝓝 (0 : E ⊗[ℂ] F)).HasBasis
      (fun p : Set E × Set F => p.1 ∈ 𝓝 (0 : E) ∧ p.2 ∈ 𝓝 (0 : F))
      (fun p => convexHull ℝ (tensorRectangle p.1 p.2))) :
    letI : DistribMulAction H (E ⊗[ℂ] F) := diagonalTensorAction
    Continuous (fun p : H × (E ⊗[ℂ] F) => p.1 • p.2) := by
  letI : DistribMulAction H (E ⊗[ℂ] F) := diagonalTensorAction
  letI : Module ℝ (E ⊗[ℂ] F) := Module.restrictScalars ℝ ℂ _
  letI : IsScalarTower ℝ ℂ (E ⊗[ℂ] F) := IsScalarTower.restrictScalars ℝ ℂ _
  let L (g : H) : E ⊗[ℂ] F →ₗ[ℂ] E ⊗[ℂ] F :=
    TensorProduct.map (linearAction g) (linearAction g)
  have hmul (g : H) (e : E) (f : F) : g • (e ⊗ₜ[ℂ] f) = (g • e) ⊗ₜ[ℂ] (g • f) :=
    TensorProduct.map_tmul _ _ _ _
  have ho (x : E ⊗[ℂ] F) : Continuous (fun g : H => g • x) := by
    induction x using TensorProduct.induction_on with
    | zero => simpa only [smul_zero] using continuous_const (y := (0 : E ⊗[ℂ] F))
    | tmul e f =>
      simp only [hmul]
      exact htmul.comp ((hE.comp (continuous_id.prodMk continuous_const)).prodMk
        (hF.comp (continuous_id.prodMk continuous_const)))
    | add x y hx hy =>
      simp only [smul_add]
      exact hx.add hy
  apply continuous_action_of_continuousAt_zero_and_orbits _ ho
  intro h
  rw [ContinuousAt]
  change Tendsto (fun p : H × (E ⊗[ℂ] F) => p.1 • p.2) (𝓝 (h, 0))
    (𝓝 (h • (0 : E ⊗[ℂ] F)))
  rw [smul_zero]
  intro U hU
  obtain ⟨⟨V, W⟩, ⟨hV, hW⟩, hrect⟩ := hbase.mem_iff.mp hU
  have hE' : {p : H × E | p.1 • p.2 ∈ V} ∈ 𝓝 (h, (0 : E)) :=
    hE.continuousAt.tendsto (by simpa only [smul_zero] using hV)
  have hF' : {p : H × F | p.1 • p.2 ∈ W} ∈ 𝓝 (h, (0 : F)) :=
    hF.continuousAt.tendsto (by simpa only [smul_zero] using hW)
  rw [nhds_prod_eq] at hE' hF'
  obtain ⟨H₁, hH₁, V₀, hV₀, hEV⟩ := Filter.mem_prod_iff.mp hE'
  obtain ⟨H₂, hH₂, W₀, hW₀, hFW⟩ := Filter.mem_prod_iff.mp hF'
  have hZ : convexHull ℝ (tensorRectangle V₀ W₀) ∈ 𝓝 (0 : E ⊗[ℂ] F) :=
    hbase.mem_iff.mpr ⟨(V₀, W₀), ⟨hV₀, hW₀⟩, Subset.rfl⟩
  change ∀ᶠ p : H × (E ⊗[ℂ] F) in 𝓝 (h, 0), p.1 • p.2 ∈ U
  filter_upwards [continuous_fst.continuousAt.tendsto (inter_mem hH₁ hH₂),
    continuous_snd.continuousAt.tendsto hZ] with p hp hp'
  apply hrect
  change L p.1 p.2 ∈ convexHull ℝ (tensorRectangle V W)
  let M : E ⊗[ℂ] F →ₗ[ℝ] E ⊗[ℂ] F := (L p.1).restrictScalars ℝ
  refine convexHull_min ?_
    ((convex_convexHull ℝ _).linear_preimage M) hp'
  rintro _ ⟨⟨e, f⟩, ⟨he, hf⟩, rfl⟩
  apply subset_convexHull ℝ
  have he' : p.1 • e ∈ V := hEV (show (p.1, e) ∈ H₁ ×ˢ V₀ from ⟨hp.1, he⟩)
  have hf' : p.1 • f ∈ W := hFW (show (p.1, f) ∈ H₂ ×ˢ W₀ from ⟨hp.2, hf⟩)
  exact ⟨(p.1 • e, p.1 • f), ⟨he', hf'⟩, (hmul _ _ _).symm⟩

end ProjectiveTensor

end Masullo
