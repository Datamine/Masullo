import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.LocallyConvex.Barrelled
import Mathlib.Topology.Baire.CompleteMetrizable

open Filter Function Set Topology TopologicalSpace

namespace Masullo

noncomputable section

/-- A Fréchet space is a metrizable locally convex space complete for its
additive uniformity. -/
def IsFrechetTVS (E : Type*) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] : Prop :=
  ∃ h : IsTopologicalAddGroup E, letI := h
    PolynormableSpace ℂ E ∧ MetrizableSpace E ∧
      @CompleteSpace E (IsTopologicalAddGroup.rightUniformSpace E)

/-- A complex Fréchet space is barrelled by the Baire category theorem. -/
theorem isFrechetTVS_barrelled {X : Type*} [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    (hX : IsFrechetTVS X) : BarrelledSpace ℂ X := by
  obtain ⟨hadd, hpoly, hmetric, hcomplete⟩ := hX
  let : UniformSpace X := IsTopologicalAddGroup.rightUniformSpace X
  have : IsUniformAddGroup X := isUniformAddGroup_of_addCommGroup
  have : CompleteSpace X := hcomplete
  have : ContinuousSMul ℂ X := (PolynormableSpace.withSeminorms ℂ X).continuousSMul
  have : (uniformity X).IsCountablyGenerated := by
    rw [uniformity_eq_comap_nhds_zero X]
    infer_instance
  have : BaireSpace X := BaireSpace.of_completelyPseudoMetrizable
  infer_instance

variable {I X : Type*} {A : I → Type*}
variable [AddCommGroup X] [Module ℂ X]
variable [∀ i, AddCommGroup (A i)] [∀ i, Module ℂ (A i)] [∀ i, TopologicalSpace (A i)]

/-- The seminorms of the final locally convex topology along linear maps. -/
def FinalSeminorm (j : ∀ i, A i →ₗ[ℂ] X) :=
  {p : Seminorm ℂ X // ∀ i, Continuous (p.comp (j i))}

abbrev locallyConvexFinalTopology (j : ∀ i, A i →ₗ[ℂ] X) : TopologicalSpace X :=
  (SeminormFamily.moduleFilterBasis (fun p : FinalSeminorm j => p.val)).topology

theorem locallyConvexFinal_withSeminorms (j : ∀ i, A i →ₗ[ℂ] X) :
    letI : TopologicalSpace X := locallyConvexFinalTopology j
    WithSeminorms (fun p : FinalSeminorm j => p.val) := by
  letI : TopologicalSpace X := locallyConvexFinalTopology j
  exact ⟨rfl⟩

theorem locallyConvexFinal_stage_continuous [∀ i, IsTopologicalAddGroup (A i)]
    (j : ∀ i, A i →ₗ[ℂ] X) (i : I) :
    Continuous[inferInstance, locallyConvexFinalTopology j] (j i) := by
  letI : TopologicalSpace X := locallyConvexFinalTopology j
  exact ((locallyConvexFinal_withSeminorms j).continuous_iff_continuous_comp (j i)).mpr
    fun p => p.property i

theorem locallyConvexFinal_seminorm_continuous (j : ∀ i, A i →ₗ[ℂ] X) (p : Seminorm ℂ X)
    (hp : ∀ i, Continuous (p.comp (j i))) :
    Continuous[locallyConvexFinalTopology j, inferInstance] p := by
  letI : TopologicalSpace X := locallyConvexFinalTopology j
  exact (locallyConvexFinal_withSeminorms j).continuous_seminorm ⟨p, hp⟩

/-- The universal mapping property of a locally convex final topology. -/
theorem locallyConvexFinal_continuous_iff [∀ i, IsTopologicalAddGroup (A i)]
    {Y : Type*} [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y] [PolynormableSpace ℂ Y]
    (j : ∀ i, A i →ₗ[ℂ] X) (L : X →ₗ[ℂ] Y) :
    Continuous[locallyConvexFinalTopology j, inferInstance] L ↔ ∀ i, Continuous (L.comp (j i)) := by
  letI : TopologicalSpace X := locallyConvexFinalTopology j
  letI : IsTopologicalAddGroup X := (locallyConvexFinal_withSeminorms j).topologicalAddGroup
  constructor
  · intro h i
    exact h.comp (locallyConvexFinal_stage_continuous j i)
  · intro h
    let W := PolynormableSpace.withSeminorms ℂ Y
    apply (W.continuous_iff_continuous_comp L).mpr
    intro q
    exact locallyConvexFinal_seminorm_continuous j _ fun i => q.property.comp (h i)

set_option maxHeartbeats 900000 in
/-- Joint continuity of a linear family on a locally convex final space
can be tested on its stages when the parameter is locally compact.
On a compact parameter neighborhood, the supremum of the pulled-back
seminorms is continuous on each stage by the tube lemma. -/
theorem locallyConvexFinal_continuous_family
    [∀ i, IsTopologicalAddGroup (A i)] {H : Type*} [TopologicalSpace H] [LocallyCompactSpace H]
    (j : ∀ i, A i →ₗ[ℂ] X) (L : H → X →ₗ[ℂ] X)
    (hex : ∀ x : X, ∃ i u, j i u = x)
    (hstage : ∀ i, Continuous[inferInstance, locallyConvexFinalTopology j]
      (fun z : H × A i => L z.1 (j i z.2))) :
    letI : TopologicalSpace X := locallyConvexFinalTopology j
    Continuous (fun z : H × X => L z.1 z.2) := by
  letI : TopologicalSpace X := locallyConvexFinalTopology j
  let W := locallyConvexFinal_withSeminorms j
  letI : IsTopologicalAddGroup X := W.topologicalAddGroup
  have hOrbit (x : X) : Continuous (fun g => L g x) := by
    obtain ⟨i, u, rfl⟩ := hex x
    exact (hstage i).comp (continuous_id.prodMk continuous_const)
  apply continuous_iff_continuousAt.mpr
  rintro ⟨h, x⟩
  obtain ⟨K, hK, hKh⟩ := exists_compact_mem_nhds h
  change Tendsto (fun z : H × X => L z.1 z.2) (𝓝 (h, x)) (𝓝 (L h x))
  apply (W.tendsto_nhds _ _).mpr
  intro i ε hε
  let p := i.val
  let S (g : K) := p.comp (L g.val)
  have hp : Continuous p := W.continuous_seminorm i
  have hbound (y : X) : BddAbove (range fun g : K => S g y) := by
    rw [show (range fun g : K => S g y) = (fun g => p (L g y)) '' K from by
      ext r
      exact ⟨fun ⟨g, he⟩ => ⟨g.val, g.property, he⟩, fun ⟨g, hg, he⟩ => ⟨⟨g, hg⟩, he⟩⟩]
    exact hK.bddAbove_image (hp.comp (hOrbit y)).continuousOn
  have hb : BddAbove (range S) := Seminorm.bddAbove_range_iff.mpr hbound
  let q : Seminorm ℂ X := ⨆ g : K, S g
  have hq_apply (y : X) : q y = ⨆ g : K, S g y := Seminorm.iSup_apply hb
  have hq : Continuous q := by
    apply locallyConvexFinal_seminorm_continuous j
    intro k
    apply Seminorm.continuous_of_forall
    intro δ hδ
    let V : Set (H × A k) := {z | p (L z.1 (j k z.2)) < δ / 2}
    have hV : IsOpen V := isOpen_lt (hp.comp (hstage k)) continuous_const
    have hsub : K ×ˢ ({0} : Set (A k)) ⊆ V := by
      rintro ⟨g,u⟩ ⟨_, hu⟩
      change u = 0 at hu
      simp [V, hu, half_pos hδ]
    obtain ⟨U, B, hUo, hBo, hKU, hB₀, hUB⟩ :=
      generalized_tube_lemma hK isCompact_singleton hV hsub
    apply Filter.mem_of_superset (hBo.mem_nhds (hB₀ (mem_singleton 0)))
    intro u hu
    rw [Seminorm.ball_zero_eq]
    change q (j k u) < δ
    rw [hq_apply]
    have hsmall (g : K) : S g (j k u) ≤ δ / 2 := by
      have hw : (g.val, u) ∈ V := hUB (show (g.val, u) ∈ U ×ˢ B from ⟨hKU g.property, hu⟩)
      exact (show p (L g.val (j k u)) < δ / 2 from hw).le
    exact (Real.iSup_le hsmall (by positivity)).trans_lt (half_lt_self hδ)
  have hnear : ∀ᶠ z : H × X in 𝓝 (h, x), q (z.2 - x) < ε / 2 := by
    have hc : Continuous (fun z : H × X => q (z.2 - x)) :=
      hq.comp (continuous_snd.sub continuous_const)
    have ht := hc.tendsto' (h, x) 0 (by simp)
    exact ht (Iio_mem_nhds (half_pos hε))
  have horbit : ∀ᶠ z : H × X in 𝓝 (h, x), p (L z.1 x - L h x) < ε / 2 := by
    have hc : Continuous (fun z : H × X => p (L z.1 x - L h x)) :=
      hp.comp (((hOrbit x).comp continuous_fst).sub continuous_const)
    have ht := hc.tendsto' (h, x) 0 (by simp)
    exact ht (Iio_mem_nhds (half_pos hε))
  filter_upwards [continuous_fst.continuousAt hKh, hnear, horbit] with z hz hz₀ hz₁
  change p (L z.1 z.2 - L h x) < ε
  have he : L z.1 z.2 - L h x = L z.1 (z.2 - x) + (L z.1 x - L h x) := by rw [map_sub]; abel
  have hs : p (L z.1 (z.2 - x)) ≤ q (z.2 - x) := by
    rw [hq_apply]
    exact le_ciSup (hbound (z.2 - x)) ⟨z.1, hz⟩
  rw [he]
  refine ((map_add_le_add p _ _).trans (add_le_add hs le_rfl)).trans_lt ?_
  simpa only [add_halves] using add_lt_add hz₀ hz₁

end

end Masullo
