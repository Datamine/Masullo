import SLocalPaleyWienerPrincipalValue

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical NumberField

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]
attribute [local instance] sLocalZetaUnfolding_classMeasurable sLocalZetaUnfolding_classBorel

variable {S T : Finset (HeightOneSpectrum (𝓞 F))}
variable (ν : Measure (SLocalThetaNormOne F T)) [ν.IsHaarMeasure]
variable (ω : PontryaginDual (SLocalThetaNormOne F T))

private abbrev H := sLocalPaleyWienerMomentImage F ν ω

/-- The range of the principal-value operator on the ambient two-moment space. -/
def sLocalPaleyWienerOrbitalRange (R : Finset T) : Submodule ℂ (H F ν ω) :=
  ((sLocalPaleyWienerPrincipalValues F ν ω R).restrict
    (sLocalPaleyWienerPrincipalValues_mapsTo_momentImage F ν ω R)).range

private abbrev A := sLocalPaleyWienerOrbitalRange F ν ω

private abbrev momentLevel (hST : S ⊆ T) (K : Set (SAdeles F S)) :=
  sLocalPaleyWienerThetaLevel F T ν ω hST K (sLocalPaleyWienerMomentKernel F T)

local notation "Level" => momentLevel F ν ω

/-- A fixed level included in the ambient homogeneous two-moment space. -/
def sLocalPaleyWienerMomentLevelInclusion (hST : S ⊆ T) (K : Set (SAdeles F S)) :
    Level hST K →L[ℂ] H F ν ω :=
  (Level hST K).subtypeL.codRestrict _
    (fun x ↦ sLocalPaleyWienerThetaLevel_le_momentImage F S ν ω hST K x.property)

private abbrev L (hST : S ⊆ T) (K : Set (SAdeles F S)) :=
  sLocalPaleyWienerMomentLevelInclusion F ν ω hST K

/-- The canonical map for the intersection denominator in (7.3.3.18)–(19). -/
def sLocalPaleyWienerOrbitalComparison (R : Finset T) (hST : S ⊆ T)
    (K : Set (SAdeles F S)) :
    (Level hST K ⧸ (A F ν ω R).comap (L F ν ω hST K).toLinearMap) →L[ℂ]
      (H F ν ω ⧸ A F ν ω R) :=
  ((A F ν ω R).comap (L F ν ω hST K).toLinearMap).liftQL
    ((A F ν ω R).mkQL.comp (L F ν ω hST K))
    (fun _ hx ↦ (Submodule.Quotient.mk_eq_zero _).mpr hx)

theorem sLocalPaleyWienerOrbitalComparison_injective (R : Finset T) (hST : S ⊆ T)
    (K : Set (SAdeles F S)) :
    Injective (sLocalPaleyWienerOrbitalComparison F ν ω R hST K) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  obtain ⟨f, rfl⟩ := Submodule.mkQ_surjective _ x
  change (A F ν ω R).mkQ (L F ν ω hST K f) = 0 at hx
  have hf : L F ν ω hST K f ∈ A F ν ω R :=
    (Submodule.Quotient.mk_eq_zero (A F ν ω R)).mp hx
  exact (Submodule.Quotient.mk_eq_zero _).mpr hf

/-- A principal-value image coming from a smaller region is contained in the
intersection denominator whenever the operator maps into the target level. -/
theorem sLocalPaleyWienerLevelRange_le_intersection (R : Finset T) (hST : S ⊆ T)
    (K₀ K : Set (SAdeles F S))
    (h : MapsTo (sLocalPaleyWienerPrincipalValues F ν ω R)
      (Level hST K₀) (Level hST K)) :
    (sLocalPrincipalValueLevelRestriction F ν ω _ h).range ≤
      (A F ν ω R).comap (L F ν ω hST K).toLinearMap := by
  rintro _ ⟨x, rfl⟩
  exact ⟨L F ν ω hST K₀ x, Subtype.ext rfl⟩

section WeilRange

local instance : MeasurableSpace (SAdeles F T)ˣ := borel _
local instance : BorelSpace (SAdeles F T)ˣ := ⟨rfl⟩

variable (μ : Measure (SAdeles F T)ˣ) [μ.IsHaarMeasure]
variable (hν : IsWeilQuotientMeasure (sUnitImage F T) μ Measure.count (sLocalClassHaar F T ν))

include hν in
/-- On an unramified component the denominator is exactly the homogeneous
image of Weil principal values applied to test representatives with zero moments. -/
theorem sLocalPaleyWienerOrbitalRange_image (R : Finset T)
    (hR : ∀ v ∈ R, finiteZetaUnramified F v.val (sLocalFiniteZetaPhases F T ω v)) :
    let M := sLocalHomogeneousThetaKernel F T ν ω
    let D := sLocalPaleyWienerMomentKernel F T
    (H F ν ω).subtype '' (A F ν ω R : Set (H F ν ω)) =
      range (fun g : D ↦ M.mkQ (sLocalWeilPrincipalValues F T R g.val)) := by
  let W := sLocalPaleyWienerPrincipalValues F ν ω R
  let M := sLocalHomogeneousThetaKernel F T ν ω
  let D := sLocalPaleyWienerMomentKernel F T
  ext q
  constructor
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    obtain ⟨f, hf, he⟩ := Submodule.mem_map.mp x.property
    refine ⟨⟨f, hf⟩, ?_⟩
    change M.mkQ (sLocalWeilPrincipalValues F T R f) = W x.val
    rw [← sLocalPaleyWienerPrincipalValues_mkQ F ν ω μ hν R hR, he]
  · rintro ⟨f, rfl⟩
    let x : H F ν ω := ⟨M.mkQ f.val, Submodule.mem_map.mpr ⟨f.val, f.property, rfl⟩⟩
    refine ⟨_, ⟨x, rfl⟩, ?_⟩
    exact sLocalPaleyWienerPrincipalValues_mkQ F ν ω μ hν R hR f.val

end WeilRange

local instance : MeasurableSpace (Idele F) := borel _
local instance : BorelSpace (Idele F) := ⟨rfl⟩
local instance : MeasurableSpace (normOneIdeleClass F) := borel _
local instance : BorelSpace (normOneIdeleClass F) := ⟨rfl⟩
local instance : MeasurableSpace (IdeleClass F) := borel _
local instance : BorelSpace (IdeleClass F) := ⟨rfl⟩

/-- For either family of regions, the union of the images of the intersection
quotients is dense in the ambient orbital quotient. -/
theorem sLocalPaleyWienerOrbitalComparison_dense (hST : S ⊆ T)
    (hs : Surjective (sIdeleClassInclusion F S))
    (ωG : PontryaginDual (normOneIdeleClass F))
    (hu : globalNormOneCharacter F ωG ∈ (sUnramified F S : Set (QuasiCharacter (IdeleClass F))))
    (η : Measure (Idele F)) [η.IsHaarMeasure]
    (νG : Measure (normOneIdeleClass F)) [νG.IsHaarMeasure]
    (hν : IsWeilQuotientMeasure (principalIdeles F) η Measure.count (globalClassMeasure F νG))
    (R : Finset T) :
    let ωT := sLocalNormOneCharacterOfGlobal F ωG T
      (sIdeleClassInclusion_surjective_mono F hST hs) (sUnramified_mono F hST hu)
    ∀ region ∈ ({sLocalPaleyWienerBox F S, sLocalPaleyWienerRegion F S} : Set (ℝ → Set (SAdeles F S))),
      Dense (⋃ X > 0, range (sLocalPaleyWienerOrbitalComparison F ν ωT R hST (region X))) := by
  dsimp only
  intro region hregion q
  let ωT := sLocalNormOneCharacterOfGlobal F ωG T
    (sIdeleClassInclusion_surjective_mono F hST hs) (sUnramified_mono F hST hu)
  let W := A F ν ωT R
  obtain ⟨f, rfl⟩ := W.mkQ_surjective q
  obtain ⟨g, hg, hlim⟩ := sLocalPaleyWienerThetaLevel_sequentialDensity F T ν hST hs ωG hu
    η νG hν (sLocalPaleyWienerMomentKernel F T) (Or.inr rfl) region hregion f.val f.property
  choose X hX hmem using hg
  let u (n : ℕ) : H F ν ωT := L F ν ωT hST (region (X n)) ⟨g n, hmem n⟩
  have huLim : Tendsto u atTop (𝓝 f) := tendsto_subtype_rng.mpr hlim
  refine mem_closure_of_tendsto (W.mkQL.continuous.continuousAt.tendsto.comp huLim)
    (Eventually.of_forall fun n ↦ ?_)
  refine mem_iUnion.mpr ⟨X n, mem_iUnion.mpr ⟨hX n, ?_⟩⟩
  exact ⟨Submodule.Quotient.mk ⟨g n, hmem n⟩, rfl⟩

end

end Masullo
