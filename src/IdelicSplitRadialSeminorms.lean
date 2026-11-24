import IdelicStageCofinalBasis
import BruhatSplitRadialSeminorms
import BruhatSupportedWindow
import IdelicCutoffKernel

open Function MeasureTheory NumberField Set Topology
open scoped ENNReal

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

local instance : LocallyCompactSpace (IdeleClass F) := ideleClasses_locallyCompact
local instance : T2Space (IdeleClass F) := ideleClasses_hausdorff
local instance : SecondCountableTopology (IdeleClass F) := ideleClass_secondCountable F
local instance : MeasurableSpace (IdeleClass F) := borel _
local instance : BorelSpace (IdeleClass F) := ⟨rfl⟩

private theorem ideleClassStage_hasSplitRadialSeminorms
    (P : WholeBruhatStage (IdeleClass F)) (τ : Multiplicative ℝ →ₜ* IdeleClass F)
    (hτ : RightInverse τ (ideleClassLogNorm F))
    (ν : Measure (normOneIdeleClass F)) [ν.IsHaarMeasure]
    {d : ℕ} (γ : Fin d → Multiplicative ℝ →ₜ* IdeleClass F)
    (B : Module.Basis (Fin d) ℝ
      (EuclideanSpace ℝ (Fin P.val.2.realDim) × EuclideanSpace ℝ (Fin P.val.2.torusDim)))
    (hγ : ∀ i, P.coordinates.comp (γ i) = elementaryOneParameter (B i))
    (p : ℝ) (hp : 1 ≤ p) :
    P.HasSplitRadialSeminorms τ ν (ENNReal.ofReal p) γ := by
  letI : CompactSpace (normOneIdeleClass F) := normOneIdeleClass_compact F
  letI : IsFiniteMeasure ν := CompactSpace.isFiniteMeasure
  letI : MeasurableSpace P.val.2.finiteFactor := borel _
  letI : BorelSpace P.val.2.finiteFactor := ⟨rfl⟩
  letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp⟩
  let m : IdeleClass F →ₜ* Multiplicative ℝ :=
    ⟨ideleClassLogNorm F, ideleClassLogNorm_continuous F⟩
  have hm : IsProperMap m :=
    isProperMap_snd_of_compactSpace.comp (ideleClassSplitHomeomorph F).isProperMap
  have hK : m.toMonoidHom.ker = normOneIdeleClass F := ideleClassLogNorm_ker_eq_normOne F
  exact P.withSeminorms_fixed_splitRadialLp m hm τ hτ (normOneIdeleClass F) hK ν
    B γ hγ (ENNReal.ofReal p) ENNReal.ofReal_ne_top

set_option maxHeartbeats 7000000 in
/-- Proposition D.1.10.9. For all sufficiently small good compact subgroups,
the three weighted integrals in positive radial coordinates define the
inherited topology on the invariant Schwartz–Bruhat space. The directions
are common to all such subgroups and to all finite exponents and Haar
normalizations. -/
theorem ideleClass_exists_splitRadialSeminorms
    (τ : Multiplicative ℝ →ₜ* IdeleClass F)
    (hτ : RightInverse τ (ideleClassLogNorm F)) :
    let d := InfinitePlace.nrRealPlaces F + 2 * InfinitePlace.nrComplexPlaces F - 1
    ∃ K₀ : Subgroup (IdeleClass F), IsCompact (K₀ : Set (IdeleClass F)) ∧
      IsOpen (lcaAnnihilator (G := IdeleClass F) K₀ : Set (PontryaginDual (IdeleClass F))) ∧
      IsCompactlyGeneratedGroup (lcaAnnihilator (G := IdeleClass F) K₀) ∧
    ∃ γ : Fin (d + 1) → Multiplicative ℝ →ₜ* IdeleClass F,
      γ 0 = τ ∧ (∀ (i : Fin d) t, γ i.succ t ∈ normOneIdeleClass F) ∧
      ∀ K : Subgroup (IdeleClass F), K ≤ K₀ → IsCompact (K : Set (IdeleClass F)) →
        IsCompactlyGeneratedGroup (lcaAnnihilator (G := IdeleClass F) K) →
        ∃ P : WholeBruhatStage (IdeleClass F), P.val.1.kernel = K ∧
          ∀ (p : ℝ), 1 ≤ p → ∀ (ν : Measure (normOneIdeleClass F)), ν.IsHaarMeasure →
            P.HasSplitRadialSeminorms τ ν (ENNReal.ofReal p) γ := by
  dsimp only
  rw [InfinitePlace.card_add_two_mul_card_eq_rank]
  obtain ⟨P₀, γ, hγ₀, hγ₁, hγ⟩ := exists_ideleClass_cofinal_basis_directions F τ hτ
  let K₀ := P₀.val.1.kernel
  have hk₀ : IsCompact (K₀ : Set (IdeleClass F)) := by
    rw [← lcaDualAnnihilator_annihilator K₀ P₀.val.1.kernel_closed]
    exact isCompact_lcaDualAnnihilator_of_isOpen _ P₀.val.1.annihilator_open
  refine ⟨K₀, hk₀, P₀.val.1.annihilator_open, P₀.val.1.annihilator_compactlyGenerated,
    γ, hγ₀, ?_, fun K hK hKc hKg => ?_⟩
  · intro i t
    rw [← ideleClassLogNorm_ker_eq_normOne F]
    exact hγ₁ i t
  · letI : CompactSpace (normOneIdeleClass F) := normOneIdeleClass_compact F
    let m : IdeleClass F →ₜ* Multiplicative ℝ :=
      ⟨ideleClassLogNorm F, ideleClassLogNorm_continuous F⟩
    have hm : IsProperMap m :=
      isProperMap_snd_of_compactSpace.comp (ideleClassSplitHomeomorph F).isProperMap
    have hs : Surjective m := hτ.surjective
    have hstage := @exists_wholeBruhatStage_kernel (IdeleClass F)
      inferInstance inferInstance inferInstance inferInstance inferInstance m hm hs K hKc hKg
    obtain ⟨P, hP⟩ := hstage
    have hle : P.val.1.kernel ≤ P₀.val.1.kernel := hP.symm ▸ hK
    obtain ⟨B, hB⟩ := hγ P hle
    refine ⟨P, hP, fun p hp ν hν => ?_⟩
    letI : ν.IsHaarMeasure := hν
    exact ideleClassStage_hasSplitRadialSeminorms F P τ hτ ν γ B hB p hp

end
end Masullo
