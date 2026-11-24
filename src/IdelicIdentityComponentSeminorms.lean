import IdelicSubgroupDirections
import IdelicStageCofinalBasis
import IdelicCutoffKernel
import BruhatCompactSubgroupDirections
import BruhatQuotientSupremum

open Function MeasureTheory NumberField Set Topology

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

/-- The identity component of the idele class group with its subspace topology. -/
abbrev ideleClassIdentityComponent : Subgroup (IdeleClass F) :=
  Subgroup.connectedComponentOfOne (IdeleClass F)

local notation "C₀" => ideleClassIdentityComponent F
local notation "Arch" => mixedEmbedding.mixedSpace F

local instance : LocallyCompactSpace (IdeleClass F) := ideleClasses_locallyCompact
local instance : T2Space (IdeleClass F) := ideleClasses_hausdorff
local instance : SecondCountableTopology (IdeleClass F) := ideleClass_secondCountable F
local instance : LocallyCompactSpace C₀ := by
  have h : IsClosed (C₀ : Set (IdeleClass F)) := isClosed_connectedComponent
  exact h.isClosedEmbedding_subtypeVal.locallyCompactSpace
local instance : SecondCountableTopology C₀ :=
  (show IsEmbedding (Subtype.val : C₀ → IdeleClass F) from IsEmbedding.subtypeVal).secondCountableTopology
local instance : MeasurableSpace C₀ := borel _
local instance : BorelSpace C₀ := ⟨rfl⟩

private def classLogModulation : IdeleClass F →ₜ* Multiplicative ℝ :=
  ⟨ideleClassLogNorm F, ideleClassLogNorm_continuous F⟩

/-- The inclusion of the identity component into the idele class group. -/
def ideleClassIdentityInclusion : C₀ →ₜ* IdeleClass F :=
  ⟨(ideleClassIdentityComponent F).subtype, continuous_subtype_val⟩

private theorem ideleClassIdentityInclusion_closedEmbedding :
    IsClosedEmbedding (ideleClassIdentityInclusion F) := by
  have h : IsClosed (C₀ : Set (IdeleClass F)) := isClosed_connectedComponent
  exact h.isClosedEmbedding_subtypeVal

/-- The logarithmic modulus restricted to the identity component. -/
def ideleClassIdentityLogModulation : C₀ →ₜ* Multiplicative ℝ :=
  (classLogModulation F).comp (ideleClassIdentityInclusion F)

theorem ideleClassIdentityLogModulation_proper :
    IsProperMap (ideleClassIdentityLogModulation F) := by
  letI : CompactSpace (normOneIdeleClass F) := normOneIdeleClass_compact F
  have hm : IsProperMap (classLogModulation F) :=
    isProperMap_snd_of_compactSpace.comp (ideleClassSplitHomeomorph F).isProperMap
  exact hm.comp (ideleClassIdentityInclusion_closedEmbedding F).isProperMap

/-- The identity component is large enough to contain the faithful
archimedean parametrization of directions. -/
theorem exists_ideleClassIdentity_directionParametrization :
    ∃ e : Multiplicative Arch →ₜ* C₀,
      (∀ x, (e x).val = archimedeanClassExponential F x) ∧
      (∀ c : Multiplicative ℝ →ₜ* C₀, ∃ x : Arch, ∀ t : ℝ,
        c (Multiplicative.ofAdd t) = e (Multiplicative.ofAdd (t • x))) ∧
      (∀ x : Arch, (∀ t : ℝ, e (Multiplicative.ofAdd (t • x)) = 1) → x = 0) := by
  have hmem (x : Multiplicative Arch) : archimedeanClassExponential F x ∈ C₀ :=
    archimedeanClassExponential_mem_identityComponent F x
  exact exists_idelic_subgroupDirectionParametrization F (ideleClassIdentityInclusion F)
    (ideleClassIdentityInclusion_closedEmbedding F).isEmbedding
    (fun x => ⟨(⟨_, hmem x⟩ : C₀), rfl⟩)

/-- The norm-one part of the identity component is the identity component
of the norm-one group, viewed in the full idele class group. -/
theorem ideleClassIdentity_normOne_eq_component
    (τ : Multiplicative ℝ →ₜ* IdeleClass F) (hτ : RightInverse τ (ideleClassLogNorm F)) :
    Subtype.val '' connectedComponent (1 : normOneIdeleClass F) =
      (C₀ : Set (IdeleClass F)) ∩ (normOneIdeleClass F : Set (IdeleClass F)) := by
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hc : Continuous (Subtype.val : normOneIdeleClass F → IdeleClass F) :=
      continuous_subtype_val
    have h := hc.mapsTo_connectedComponent (1 : normOneIdeleClass F)
    exact ⟨h hx, x.property⟩
  · rintro ⟨hg₀, hg₁⟩
    let m := classLogModulation F
    have hmem (x : IdeleClass F) : x / τ (m x) ∈ normOneIdeleClass F := by
      rw [← ideleClassLogNorm_ker_eq_normOne F]
      change m (x / τ (m x)) = 1
      rw [map_div, show m (τ (m x)) = m x from hτ _, div_self']
    let r (x : IdeleClass F) : normOneIdeleClass F := ⟨_, hmem x⟩
    have hr : Continuous r :=
      (continuous_id.div' (τ.continuous.comp m.continuous)).subtype_mk _
    have hr₁ : r 1 = 1 := by
      apply Subtype.ext
      change (1 : IdeleClass F) / τ (m 1) = 1
      rw [map_one m, map_one τ]
      exact div_one (1 : IdeleClass F)
    have h := hr.mapsTo_connectedComponent (1 : IdeleClass F)
    rw [hr₁] at h
    refine ⟨r g, h hg₀, ?_⟩
    change g / τ (m g) = g
    have hmg : m g = 1 := by
      change g ∈ (ideleClassLogNorm F).ker
      rw [ideleClassLogNorm_ker_eq_normOne]
      exact hg₁
    rw [hmg, map_one τ]
    exact div_one g

set_option maxHeartbeats 7000000 in
/-- Proposition D.1.10.7. The common radial and norm-one angular directions
give the weighted pointwise supremum topology on sufficiently fine
Schwartz–Bruhat stages of the actual identity component. -/
theorem ideleClassIdentity_exists_weightedSupSeminorms
    (τ : Multiplicative ℝ →ₜ* IdeleClass F)
    (hτ : RightInverse τ (ideleClassLogNorm F)) :
    let d := InfinitePlace.nrRealPlaces F + 2 * InfinitePlace.nrComplexPlaces F - 1
    ∃ K₀ : Subgroup C₀, IsCompact (K₀ : Set C₀) ∧
      IsOpen (lcaAnnihilator (G := C₀) K₀ : Set (PontryaginDual C₀)) ∧
      IsCompactlyGeneratedGroup (lcaAnnihilator (G := C₀) K₀) ∧
      ∃ γ : Fin (d + 1) → Multiplicative ℝ →ₜ* C₀,
        (∀ t, (γ 0 t).val = τ t) ∧
        (∀ (i : Fin d) t, (γ i.succ t).val ∈ normOneIdeleClass F) ∧
        ∀ K : Subgroup C₀, K ≤ K₀ → IsCompact (K : Set C₀) →
          IsCompactlyGeneratedGroup (lcaAnnihilator (G := C₀) K) →
          ∃ P : WholeBruhatStage C₀, P.val.1.kernel = K ∧
            P.HasLogWeightedQuotientSup (ideleClassIdentityLogModulation F) γ := by
  dsimp only
  rw [InfinitePlace.card_add_two_mul_card_eq_rank]
  let i := ideleClassIdentityInclusion F
  let m := ideleClassIdentityLogModulation F
  have hm : IsProperMap m := ideleClassIdentityLogModulation_proper F
  have hτimage (t : Multiplicative ℝ) : τ t ∈ range i :=
    ⟨(⟨τ t, oneParameter_mem_identityComponent τ t⟩ : C₀), rfl⟩
  have hfactors := @exists_continuousHom_factor_embedding (Multiplicative ℝ) C₀ (IdeleClass F)
    _ _ _ _ _ _ i (ideleClassIdentityInclusion_closedEmbedding F).isEmbedding τ hτimage
  obtain ⟨σ, hσ⟩ := hfactors
  have hσm : RightInverse σ m := by
    intro t
    change ideleClassLogNorm F (i (σ t)) = t
    rw [hσ, hτ]
  obtain ⟨e, _, he, hf⟩ := exists_ideleClassIdentity_directionParametrization F
  have hd : Module.finrank ℝ Arch = Module.finrank ℚ F - 1 + 1 := by
    rw [mixedEmbedding.finrank]
    have hpos : 0 < Module.finrank ℚ F := Module.finrank_pos
    omega
  have hdata := @exists_compactSubgroup_radial_basis_directions C₀ Arch
    inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance inferInstance
    m hm σ hσm e he hf _ hd
  obtain ⟨K₀, hk₀, ho, hg, γ, hγ₀, hγ₁, hγ⟩ := hdata
  refine ⟨K₀, hk₀, ho, hg, γ, ?_, ?_, fun K hK hKc hKg => ?_⟩
  · intro t
    rw [hγ₀]
    exact hσ t
  · intro j t
    rw [← ideleClassLogNorm_ker_eq_normOne F]
    exact hγ₁ j t
  · obtain ⟨P, hP, B, hB⟩ := hγ K hK hKc hKg
    letI : MeasurableSpace P.val.2.finiteFactor := borel _
    letI : BorelSpace P.val.2.finiteFactor := ⟨rfl⟩
    let μ : Measure C₀ := Measure.haar
    have hU := @WholeBruhatStage.withSeminorms_fixed_logWeightedQuotientSup C₀
      _ _ _ _ _ _ _ _ P _ _ μ _ m hm hσm.surjective _ B γ hB
    exact ⟨P, hP, hU⟩

end
end Masullo
