import MappingSpaces
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Topology.Algebra.InfiniteSum.UniformOn

open Bornology Filter Function Set Topology
open scoped Pointwise

namespace Masullo

noncomputable section

/-- Unconditional summability gives a totally bounded set of all finite subsums. -/
theorem totallyBounded_range_finite_subsums
    {Y ι : Type*} [AddCommGroup Y] [UniformSpace Y] [IsUniformAddGroup Y]
    (v : ι → Y) (h : Summable v) :
    TotallyBounded (range fun s : Finset ι => ∑ i ∈ s, v i) := by
  classical
  obtain ⟨y,hy⟩ := h
  have hc : CauchySeq (fun s : Finset ι => ∑ i ∈ s, v i) := hy.cauchySeq
  apply totallyBounded_iff_subset_finite_iUnion_nhds_zero.mpr
  intro U hU
  obtain ⟨s,hs⟩ := cauchySeq_finset_iff_sum_vanishing.mp hc U hU
  let f (a : Finset ι) := ∑ i ∈ a, v i
  let P : Finset Y := s.powerset.image f
  refine ⟨P, P.finite_toSet, ?_⟩
  rintro _ ⟨a, rfl⟩
  have hmem : f (a ∩ s) ∈ P :=
    Finset.mem_image_of_mem f (Finset.mem_powerset.mpr Finset.inter_subset_right)
  refine mem_iUnion.mpr ⟨f (a ∩ s), mem_iUnion.mpr ⟨hmem, ?_⟩⟩
  change f a ∈ f (a ∩ s) +ᵥ U
  have hd : Disjoint (a \ s) s := Finset.disjoint_sdiff.symm
  have he : f (a \ s) + f (a ∩ s) = f a := by
    have hEq : a \ (a ∩ s) = a \ s := by
      ext i
      simp only [Finset.mem_sdiff, Finset.mem_inter]
      tauto
    exact hEq ▸ Finset.sum_sdiff Finset.inter_subset_left
  exact ⟨f (a \ s), hs (a \ s) hd, (add_comm _ _).trans he⟩

/-- On a barrelled domain, a pointwise summable family of continuous linear
maps has a continuous linear sum. -/
theorem exists_continuousLinearMap_hasSum_pointwise
    {X Y ι : Type*} [AddCommGroup X] [Module ℂ X] [UniformSpace X]
    [IsUniformAddGroup X] [ContinuousSMul ℂ X] [BarrelledSpace ℂ X]
    [AddCommGroup Y] [Module ℂ Y] [UniformSpace Y] [IsUniformAddGroup Y]
    [ContinuousSMul ℂ Y] [PolynormableSpace ℂ Y] [T2Space Y]
    (L : ι → X →L[ℂ] Y) (h : ∀ x, Summable fun i => L i x) :
    ∃ R : X →L[ℂ] Y, ∀ x, HasSum (fun i => L i x) (R x) := by
  classical
  let P (s : Finset ι) : X →L[ℂ] Y := ∑ i ∈ s, L i
  have hbounded (x : X) : IsVonNBounded ℂ (range fun s => P s x) := by
    have ht := (totallyBounded_range_finite_subsums (fun i => L i x) (h x)).isVonNBounded ℂ
    simpa only [P, sum_apply] using ht
  choose y hy using h
  have hlim : Tendsto (fun s x => P s x) atTop (𝓝 y) := tendsto_pi_nhds.mpr fun x => by
    simpa only [HasSum, SummationFilter.unconditional_filter, P, sum_apply] using hy x
  have he : Equicontinuous (fun s x => P s x) :=
    (PolynormableSpace.banach_steinhaus (𝓕 := P) hbounded).equicontinuous
  let R : X →L[ℂ] Y := ⟨linearMapOfTendsto y (fun s => (P s).toLinearMap) hlim,
    hlim.continuous_of_equicontinuous he⟩
  exact ⟨R, hy⟩

/-- Pointwise sums of continuous linear functionals on a barrelled space
converge uniformly on every totally bounded set. -/
theorem hasSumUniformlyOn_of_linear_pointwise
    {X ι : Type*} [AddCommGroup X] [Module ℂ X] [UniformSpace X]
    [IsUniformAddGroup X] [ContinuousSMul ℂ X] [BarrelledSpace ℂ X]
    (L : ι → X →L[ℂ] ℂ) (R : X →L[ℂ] ℂ) (h : ∀ x, HasSum (fun i ↦ L i x) (R x))
    {B : Set X} (hB : TotallyBounded B) :
    HasSumUniformlyOn (fun i x ↦ L i x) (fun x ↦ R x) B := by
  classical
  let P (s : Finset ι) : X →L[ℂ] ℂ := ∑ i ∈ s, L i
  let A (s : Finset ι) : X →L[ℂ] ℂ := P s - R
  have hb (x : X) : IsVonNBounded ℂ (range fun s ↦ A s x) := by
    have hP : IsVonNBounded ℂ (range fun s ↦ P s x) := by
      simpa only [P, sum_apply] using
        (totallyBounded_range_finite_subsums (fun i ↦ L i x) (h x).summable).isVonNBounded ℂ
    apply (hP.sub (Set.finite_singleton (R x)).isVonNBounded).subset
    rintro _ ⟨s,rfl⟩
    exact ⟨P s x,mem_range_self _,R x,mem_singleton _,rfl⟩
  have he := (PolynormableSpace.banach_steinhaus (𝓕 := A) hb).equicontinuous (0 : X)
  apply hasSumUniformlyOn_iff_tendstoUniformlyOn.mpr
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  have hhalf : 0 < ε/2 := half_pos hε
  let U : Set X := {x | ∀ s, ‖A s x‖ < ε/2}
  have hU : U ∈ 𝓝 (0 : X) := by
    filter_upwards [(Metric.equicontinuousAt_iff_right.mp he) (ε/2) hhalf] with x hx
    intro s
    have h := hx s
    change dist (A s 0) (A s x) < ε/2 at h
    simpa only [map_zero,dist_zero_left] using h
  obtain ⟨D,hD,hcover⟩ := totallyBounded_iff_subset_finite_iUnion_nhds_zero.mp hB U hU
  have hlim (z : X) : Tendsto (fun s ↦ P s z) atTop (𝓝 (R z)) := by
    simpa only [HasSum, SummationFilter.unconditional_filter, P, sum_apply] using h z
  have hsmall (z : X) : ∀ᶠ s in atTop, ‖A s z‖ < ε/2 := by
    filter_upwards [(hlim z).eventually (Metric.ball_mem_nhds _ hhalf)] with s hs
    simpa only [Metric.mem_ball,dist_eq_norm,A,sub_apply] using hs
  filter_upwards [hD.eventually_all.mpr (fun z _ ↦ hsmall z)] with s hs x hx
  obtain ⟨z,hz,w,hw,rfl⟩ : ∃ z ∈ D, ∃ w ∈ U, z + w = x := by
    have ht := hcover hx
    simp only [mem_iUnion] at ht
    obtain ⟨z,hz,hw⟩ := ht
    exact ⟨z,hz,hw⟩
  have hsum : ‖A s (z+w)‖ < ε := by
    rw [map_add]
    exact (norm_add_le _ _).trans_lt (by linarith [hs z hz, hw s])
  simpa only [P, A, sum_apply, sub_apply, dist_eq_norm, norm_sub_rev] using hsum

/-- Scalar evaluation identifies a synthesis followed by its forward map
with the identity when the evaluations separate the target. -/
theorem continuousLinearMap_comp_eq_id_of_scalar_sums
    {X Y Ω J : Type*} [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]
    (F : X →L[ℂ] Y) (S : Y →L[ℂ] X) (ev : J → Y →L[ℂ] ℂ)
    (hinj : Injective (fun y : Y => fun j => ev j y))
    (t : Y → Ω → X) (hs : ∀ y, HasSum (t y) (S y))
    (hF : ∀ y j, HasSum (fun θ => ev j (F (t y θ))) (ev j y)) :
    F.comp S = ContinuousLinearMap.id ℂ Y := by
  apply ContinuousLinearMap.ext
  intro y
  apply hinj
  funext j
  exact ((hs y).mapL ((ev j).comp F)).unique (hF y j)

end

end Masullo
