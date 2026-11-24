import AdelicOrbitBoundary
import Mathlib.Topology.LocallyFinite

open Filter Function IsDedekindDomain NumberField Set Topology
open scoped Classical NumberField RestrictedProduct

noncomputable section

namespace Masullo

variable (F : Type*) [Field F] [NumberField F]

private abbrev Place := HeightOneSpectrum (𝓞 F)

/-- The norm-one orbit of the adele with one coordinate zero. -/
def adelicNormOneCoordinateOrbit (v : InfinitePlace F ⊕ Place F) : Set (Adeles F) :=
  Set.range (fun g : (ideleNorm F).ker ↦ g.val.val * adelicCoordinatePoint F v)

/-- The global norm-one orbit space (D_F^1) has the topology inherited from the adeles. -/
def adelicNormOneOrbitSpace : Set (Adeles F) :=
  Set.range (fun g : (ideleNorm F).ker ↦ g.val.val) ∪
    ⋃ v, adelicNormOneCoordinateOrbit F v

private def finiteCoordinatePointInNormOneSpace (v : Place F) : adelicNormOneOrbitSpace F :=
  ⟨adelicCoordinatePoint F (.inr v), Or.inr (Set.mem_iUnion.mpr
    ⟨Sum.inr v, Set.mem_range.mpr ⟨1, by simp⟩⟩)⟩

private def oneInNormOneSpace : adelicNormOneOrbitSpace F :=
  ⟨1, Or.inl (Set.mem_range.mpr ⟨1, rfl⟩)⟩

/-- Letting the exceptional finite place escape, its coordinate point tends to the unit adele. -/
theorem adelic_finite_coordinate_points_tendsto_one :
    Tendsto (fun v : Place F ↦ adelicCoordinatePoint F (.inr v)) cofinite (𝓝 1) := by
  let P := Πʳ w : Place F, [w.adicCompletion F, w.adicCompletionIntegers F]_[⊤]
  let a' (v : Place F) : P :=
    ⟨fun w ↦ if w = v then 0 else 1, Eventually.of_forall fun w ↦ by
      change (if w = v then 0 else 1) ∈ w.adicCompletionIntegers F
      by_cases h : w = v <;> simp [h]⟩
  let inc : P → FiniteAdeleRing (𝓞 F) F :=
    RestrictedProduct.inclusion _ _ le_top
  have hA : Tendsto a' cofinite (𝓝 (1 : P)) := by
    apply RestrictedProduct.isEmbedding_coe_of_top.tendsto_nhds_iff.mpr
    apply tendsto_pi_nhds.mpr
    intro w
    apply tendsto_const_nhds.congr'
    have hw : ∀ᶠ v : Place F in cofinite, w ≠ v := by
      simp [eventually_cofinite]
    filter_upwards [hw] with v hv
    change (1 : w.adicCompletion F) = (if w = v then 0 else 1)
    rw [ite_eq_right hv]
  have hinc : Continuous inc := RestrictedProduct.continuous_inclusion le_top
  have hf := (hinc.tendsto (1 : P)).comp hA
  exact tendsto_const_nhds.prodMk_nhds hf

/-- The finite-place norm-one orbits are not locally finite in the source orbit space.
In particular the locally finite closed-cover argument in Lemma 8.2.0.3(2) cannot apply. -/
theorem adelic_finite_normOne_orbits_not_locallyFinite :
    ¬ LocallyFinite (fun v : Place F ↦
      (Subtype.val ⁻¹' adelicNormOneCoordinateOrbit F (.inr v) : Set (adelicNormOneOrbitSpace F))) := by
  letI := finitePlaces_infinite F
  intro h
  obtain ⟨U, hU, hfin⟩ := h (oneInNormOneSpace F)
  have hconv : Tendsto (finiteCoordinatePointInNormOneSpace F) cofinite (𝓝 (oneInNormOneSpace F)) :=
    tendsto_subtype_rng.mpr (adelic_finite_coordinate_points_tendsto_one F)
  have hev : ∀ᶠ v : Place F in cofinite, finiteCoordinatePointInNormOneSpace F v ∈ U :=
    hconv.eventually hU
  have hc : ∀ᶠ v : Place F in cofinite,
      ¬ (Subtype.val ⁻¹' adelicNormOneCoordinateOrbit F (.inr v) ∩ U).Nonempty :=
    eventually_cofinite.mpr (by simpa only [not_not] using hfin)
  obtain ⟨v, hv, hn⟩ := (hev.and hc).exists
  refine hn ⟨finiteCoordinatePointInNormOneSpace F v, ?_, hv⟩
  change adelicCoordinatePoint F (.inr v) ∈ adelicNormOneCoordinateOrbit F (.inr v)
  exact Set.mem_range.mpr ⟨1, by simp⟩

end Masullo
