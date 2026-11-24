import SLocalStageDirections
import BruhatCompactSubgroupDirections
import BruhatSplitRadialSeminorms
import IdelicCutoffKernel

open Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped ENNReal NumberField

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]
  (S : Finset (HeightOneSpectrum (𝓞 F)))

local notation "C" => SIdeleClass F S
local notation "Arch" => mixedEmbedding.mixedSpace F

local instance : LocallyCompactSpace (IdeleClass F) := ideleClasses_locallyCompact
local instance : T2Space (IdeleClass F) := ideleClasses_hausdorff
local instance : SecondCountableTopology (IdeleClass F) := ideleClass_secondCountable F
local instance : LocallyCompactSpace C :=
  (sIdeleClassInclusion_openEmbedding F S).locallyCompactSpace
local instance : T2Space C :=
  (sIdeleClassInclusion_openEmbedding F S).isEmbedding.t2Space
local instance : SecondCountableTopology C :=
  (sIdeleClassInclusion_openEmbedding F S).isEmbedding.secondCountableTopology
local instance : MeasurableSpace C := borel _
local instance : BorelSpace C := ⟨rfl⟩

private theorem sIdeleClassStage_hasSplitRadialSeminorms
    (P : WholeBruhatStage C) (τ : Multiplicative ℝ →ₜ* C)
    (hτ : RightInverse τ (sIdeleClassLogModulation F S))
    (ν : Measure (sNormOneClass F S)) [ν.IsHaarMeasure]
    {d : ℕ} (γ : Fin d → Multiplicative ℝ →ₜ* C)
    (B : Module.Basis (Fin d) ℝ
      (EuclideanSpace ℝ (Fin P.val.2.realDim) × EuclideanSpace ℝ (Fin P.val.2.torusDim)))
    (hγ : ∀ i, P.coordinates.comp (γ i) = elementaryOneParameter (B i))
    (p : ℝ) (hp : 1 ≤ p) :
    P.HasSplitRadialSeminorms τ ν (ENNReal.ofReal p) γ := by
  letI : CompactSpace (sNormOneClass F S) := (sNormOneClass_compact_hausdorff F S).1
  letI : IsFiniteMeasure ν := CompactSpace.isFiniteMeasure
  letI : MeasurableSpace P.val.2.finiteFactor := borel _
  letI : BorelSpace P.val.2.finiteFactor := ⟨rfl⟩
  letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp⟩
  exact @WholeBruhatStage.withSeminorms_fixed_splitRadialLp C _ _ _ _ _ _ _ _
    P _ _ (sIdeleClassLogModulation F S) (sIdeleClassLogModulation_proper F S) τ hτ
    (sNormOneClass F S) (sIdeleClassLogModulation_ker F S) ν _ _
    _ B γ hγ (ENNReal.ofReal p) _ ENNReal.ofReal_ne_top

set_option maxHeartbeats 7000000 in
/-- Proposition D.1.10.10. Each S-local idele class group has a common
family of norm-one directions giving all three split-Haar seminorm
topologies on its sufficiently fine invariant Schwartz–Bruhat stages. -/
theorem sIdeleClass_exists_splitRadialSeminorms
    (τ : Multiplicative ℝ →ₜ* C) (hτ : RightInverse τ (sIdeleClassLogModulation F S)) :
    let d := InfinitePlace.nrRealPlaces F + 2 * InfinitePlace.nrComplexPlaces F - 1
    ∃ K₀ : Subgroup C, IsCompact (K₀ : Set C) ∧
      IsOpen (lcaAnnihilator (G := C) K₀ : Set (PontryaginDual C)) ∧
      IsCompactlyGeneratedGroup (lcaAnnihilator (G := C) K₀) ∧
    ∃ γ : Fin (d + 1) → Multiplicative ℝ →ₜ* C,
      γ 0 = τ ∧ (∀ (i : Fin d) t, γ i.succ t ∈ sNormOneClass F S) ∧
      ∀ K : Subgroup C, K ≤ K₀ → IsCompact (K : Set C) →
        IsCompactlyGeneratedGroup (lcaAnnihilator (G := C) K) →
        ∃ P : WholeBruhatStage C, P.val.1.kernel = K ∧
          ∀ (p : ℝ), 1 ≤ p → ∀ (ν : Measure (sNormOneClass F S)), ν.IsHaarMeasure →
            P.HasSplitRadialSeminorms τ ν (ENNReal.ofReal p) γ := by
  dsimp only
  rw [InfinitePlace.card_add_two_mul_card_eq_rank]
  obtain ⟨e, _, he, hf⟩ := exists_sIdeleClass_directionParametrization F S
  have hd : Module.finrank ℝ Arch = Module.finrank ℚ F - 1 + 1 := by
    rw [mixedEmbedding.finrank]
    have hpos : 0 < Module.finrank ℚ F := Module.finrank_pos
    omega
  have hdata := @exists_compactSubgroup_radial_basis_directions C Arch
    inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance inferInstance
    (sIdeleClassLogModulation F S) (sIdeleClassLogModulation_proper F S) τ hτ e he hf _ hd
  obtain ⟨K₀, hk₀, ho, hg, γ, hγ₀, hγ₁, hγ⟩ := hdata
  refine ⟨K₀, hk₀, ho, hg, γ, hγ₀, ?_, fun K hK hKc hKg => ?_⟩
  · intro j t
    rw [← sIdeleClassLogModulation_ker F S]
    exact hγ₁ j t
  · obtain ⟨P, hP, B, hB⟩ := hγ K hK hKc hKg
    refine ⟨P, hP, fun p hp ν hν => ?_⟩
    letI : ν.IsHaarMeasure := hν
    exact sIdeleClassStage_hasSplitRadialSeminorms F S P τ hτ ν γ B hB p hp

end
end Masullo
