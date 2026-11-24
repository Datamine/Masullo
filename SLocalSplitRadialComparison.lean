import SLocalSplitRadialSeminorms
import BruhatSplitRadialComparison
import BruhatEquivPullback

open Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped ENNReal NumberField

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]
  (S : Finset (HeightOneSpectrum (𝓞 F)))

local notation "C" => SIdeleClass F S

local instance : LocallyCompactSpace (IdeleClass F) := ideleClasses_locallyCompact
local instance : T2Space (IdeleClass F) := ideleClasses_hausdorff
local instance : LocallyCompactSpace C :=
  (sIdeleClassInclusion_openEmbedding F S).locallyCompactSpace
local instance : T2Space C :=
  (sIdeleClassInclusion_openEmbedding F S).isEmbedding.t2Space
local instance : MeasurableSpace (IdeleClass F) := borel _
local instance : BorelSpace (IdeleClass F) := ⟨rfl⟩
local instance : MeasurableSpace C := borel _
local instance : BorelSpace C := ⟨rfl⟩

/-- The restriction of the S-local inclusion to the norm-one subgroups. -/
def sIdeleNormOneContinuousInclusion : sNormOneClass F S →ₜ* normOneIdeleClass F :=
  { toMonoidHom :=
      ((sIdeleClassInclusion F S).comp (sNormOneClass F S).subtype).codRestrict
        (normOneIdeleClass F) (fun x => x.property)
    continuous_toFun :=
      ((sIdeleClassInclusion_openEmbedding F S).continuous.comp continuous_subtype_val).subtype_mk _ }

@[simp] theorem sIdeleNormOneContinuousInclusion_val (x : sNormOneClass F S) :
    (sIdeleNormOneContinuousInclusion F S x).val = sIdeleClassInclusion F S x.val := rfl

private theorem sIdeleNormOneContinuousInclusion_embedding :
    IsEmbedding (sIdeleNormOneContinuousInclusion F S) := by
  let j := sIdeleNormOneContinuousInclusion F S
  have hval : IsEmbedding (Subtype.val : normOneIdeleClass F → IdeleClass F) :=
    IsEmbedding.subtypeVal
  apply (hval.of_comp_iff (f := j)).mp
  exact (sIdeleClassInclusion_openEmbedding F S).isEmbedding.comp IsEmbedding.subtypeVal

/-- For sufficiently large S, the comparison is an isomorphism on
the norm-one groups as well as on the whole class groups. -/
def sIdeleNormOneContinuousEquiv (hs : Surjective (sIdeleClassInclusion F S)) :
    sNormOneClass F S ≃ₜ* normOneIdeleClass F :=
  let j := sIdeleNormOneContinuousInclusion F S
  have hsurj : Surjective j := by
    intro y
    obtain ⟨x, hx⟩ := hs y.val
    have hx₁ : x ∈ sNormOneClass F S := by
      change ideleClassNorm F (sIdeleClassInclusion F S x) = 1
      rw [hx]
      exact y.property
    exact ⟨⟨x, hx₁⟩, Subtype.ext hx⟩
  ContinuousMulEquiv.mk'
    ((sIdeleNormOneContinuousInclusion_embedding F S).toHomeomorphOfSurjective hsurj)
    (map_mul j)

@[simp] theorem sIdeleNormOneContinuousEquiv_apply
    (hs : Surjective (sIdeleClassInclusion F S)) (x : sNormOneClass F S) :
    sIdeleNormOneContinuousEquiv F S hs x = sIdeleNormOneContinuousInclusion F S x := rfl

/-- The image of a chosen S-local norm-one Haar normalization is a global
Haar normalization under the eventual identification. -/
theorem sIdeleNormOne_map_isHaarMeasure (hs : Surjective (sIdeleClassInclusion F S))
    (ν : Measure (sNormOneClass F S)) [ν.IsHaarMeasure] :
    (Measure.map (sIdeleNormOneContinuousInclusion F S) ν).IsHaarMeasure :=
  (sIdeleNormOneContinuousEquiv F S hs).isHaarMeasure_map ν

/-- Any fixed global norm-one Haar normalization induces a compatible
S-local normalization whenever the inclusion is onto. -/
theorem exists_sIdeleNormOneHaar_map_eq_global
    (hs : Surjective (sIdeleClassInclusion F S))
    (ν : Measure (normOneIdeleClass F)) [ν.IsHaarMeasure] :
    ∃ ρ : Measure (sNormOneClass F S), ρ.IsHaarMeasure ∧
      Measure.map (sIdeleNormOneContinuousInclusion F S) ρ = ν := by
  let e := sIdeleNormOneContinuousEquiv F S hs
  let ρ := Measure.map e.symm ν
  refine ⟨ρ, e.symm.isHaarMeasure_map ν, ?_⟩
  change Measure.map (e : sNormOneClass F S → normOneIdeleClass F) (Measure.map e.symm ν) = ν
  have hme : Measurable (e : sNormOneClass F S → normOneIdeleClass F) := e.continuous.measurable
  have hmes : Measurable (e.symm : normOneIdeleClass F → sNormOneClass F S) :=
    e.symm.continuous.measurable
  rw [Measure.map_map hme hmes]
  have he : (e : sNormOneClass F S → normOneIdeleClass F) ∘ e.symm = id :=
    funext e.apply_symm_apply
  rw [he, Measure.map_id]

/-- Exact numerical comparison of all three S-local seminorm families with
the corresponding global families. The section, directions, and Haar measure
are carried by the inclusion. This formula also holds for any polynomial in
the absolute log norm and any invariant derivative word. -/
theorem sIdeleClass_splitRadialNorm_eq_global
    (σ : Multiplicative ℝ →ₜ* C) (ν : Measure (sNormOneClass F S))
    (p : ℝ≥0∞) (Q : Polynomial ℂ) (cs : List (Multiplicative ℝ →ₜ* C))
    (u : BruhatSchwartz C) (v : BruhatSchwartz (IdeleClass F))
    (huv : ∀ x : C, u.val x = v.val (sIdeleClassInclusion F S x)) :
    bruhatSplitRadialNorm σ ν p Q (WholeBruhatStage.bruhatDerivativeWord cs u) =
      bruhatSplitRadialNorm ((sIdeleClassContinuousInclusion F S).comp σ)
        (Measure.map (sIdeleNormOneContinuousInclusion F S) ν) p Q
        (WholeBruhatStage.bruhatDerivativeWord
          (cs.map fun c => (sIdeleClassContinuousInclusion F S).comp c) v) := by
  let i := sIdeleClassContinuousInclusion F S
  let j := sIdeleNormOneContinuousInclusion F S
  have h := bruhatDerivativeWord_comp_hom i cs u v huv
  exact @bruhatSplitRadialNorm_map_normOne C (IdeleClass F)
    _ _ _ _ _ _ _ _ _ _ _ _ _ _
    i (sNormOneClass F S) (normOneIdeleClass F) j (fun _ => rfl) σ ν p Q _ _ h

set_option maxHeartbeats 5000000 in
/-- Once the inclusion is onto, every global test has an actual S-local
pullback, and all printed split-radial values agree with the transported
global section, directions, and norm-one Haar measure. -/
theorem sIdeleClass_splitRadial_transport
    (hs : Surjective (sIdeleClassInclusion F S))
    (σ : Multiplicative ℝ →ₜ* C) (hσ : RightInverse σ (sIdeleClassLogModulation F S))
    (ν : Measure (sNormOneClass F S)) [ν.IsHaarMeasure] :
    let i := sIdeleClassContinuousInclusion F S
    let j := sIdeleNormOneContinuousInclusion F S
    (Measure.map j ν).IsHaarMeasure ∧
    RightInverse (i.comp σ) (ideleClassLogNorm F) ∧
    ∀ v : BruhatSchwartz (IdeleClass F), ∃ u : BruhatSchwartz C,
      (∀ x : C, u.val x = v.val (i x)) ∧
      ∀ (p : ℝ≥0∞) (Q : Polynomial ℂ) (cs : List (Multiplicative ℝ →ₜ* C)),
        bruhatSplitRadialNorm σ ν p Q (WholeBruhatStage.bruhatDerivativeWord cs u) =
          bruhatSplitRadialNorm (i.comp σ) (Measure.map j ν) p Q
            (WholeBruhatStage.bruhatDerivativeWord (cs.map fun c => i.comp c) v) := by
  dsimp only
  refine ⟨sIdeleNormOne_map_isHaarMeasure F S hs ν, fun t => hσ t, fun v => ?_⟩
  letI : CompactSpace (normOneIdeleClass F) := normOneIdeleClass_compact F
  let m : IdeleClass F →ₜ* Multiplicative ℝ :=
    ⟨ideleClassLogNorm F, ideleClassLogNorm_continuous F⟩
  have hm : IsProperMap m :=
    isProperMap_snd_of_compactSpace.comp (ideleClassSplitHomeomorph F).isProperMap
  have hms : Surjective m := fun t => ⟨ideleClassExpSection F t, ideleClassLogNorm_expSection F t⟩
  let e := sIdeleClassContinuousEquiv F S hs
  have h := @exists_bruhatSchwartz_pullback_equiv C (IdeleClass F)
    _ _ _ _ _ _ _ _ _ _ m hm hms e v
  obtain ⟨u, hu⟩ := h
  refine ⟨u, hu, fun p Q cs => ?_⟩
  exact sIdeleClass_splitRadialNorm_eq_global F S σ ν p Q cs u v hu

/-- Under the eventual group identification every S-local test also comes
from a global test. -/
theorem sIdeleClass_exists_globalBruhat
    (hs : Surjective (sIdeleClassInclusion F S))
    (hms : Surjective (sIdeleClassLogModulation F S))
    (u : BruhatSchwartz C) :
    ∃ v : BruhatSchwartz (IdeleClass F),
      ∀ x : C, u.val x = v.val (sIdeleClassInclusion F S x) := by
  let e := sIdeleClassContinuousEquiv F S hs
  have h := @exists_bruhatSchwartz_pullback_equiv (IdeleClass F) C
    _ _ _ _ _ _ _ _ _ _
    (sIdeleClassLogModulation F S) (sIdeleClassLogModulation_proper F S) hms e.symm u
  obtain ⟨v, hv⟩ := h
  refine ⟨v, fun x => ?_⟩
  have hx := hv (e x)
  rw [e.symm_apply_apply] at hx
  exact hx.symm

/-- For every sufficiently large S, all global tests admit S-local
representatives with identical numerical seminorms for the transported data. -/
theorem exists_sIdeleClass_eventualSplitRadialNormMatch :
    ∃ S₀ : Finset (HeightOneSpectrum (𝓞 F)), ∀ T, S₀ ⊆ T →
      ∀ (σ : Multiplicative ℝ →ₜ* SIdeleClass F T),
        RightInverse σ (sIdeleClassLogModulation F T) →
        ∀ (ν : Measure (sNormOneClass F T)), ν.IsHaarMeasure →
          let i := sIdeleClassContinuousInclusion F T
          let j := sIdeleNormOneContinuousInclusion F T
          (Measure.map j ν).IsHaarMeasure ∧
          RightInverse (i.comp σ) (ideleClassLogNorm F) ∧
          ∀ v : BruhatSchwartz (IdeleClass F), ∃ u : BruhatSchwartz (SIdeleClass F T),
            (∀ x : SIdeleClass F T, u.val x = v.val (i x)) ∧
            ∀ (p : ℝ≥0∞) (Q : Polynomial ℂ) (cs : List (Multiplicative ℝ →ₜ* SIdeleClass F T)),
              bruhatSplitRadialNorm σ ν p Q (WholeBruhatStage.bruhatDerivativeWord cs u) =
                bruhatSplitRadialNorm (i.comp σ) (Measure.map j ν) p Q
                  (WholeBruhatStage.bruhatDerivativeWord (cs.map fun c => i.comp c) v) := by
  obtain ⟨S₀, hS₀⟩ := sIdeleClass_eventually_surjective F
  refine ⟨S₀, fun T hT σ hσ ν hν => ?_⟩
  letI : ν.IsHaarMeasure := hν
  exact sIdeleClass_splitRadial_transport F T (hS₀ T hT) σ hσ ν

end
end Masullo
