import SLocalFourierPairing
import UnitHaarDensity
import ArchimedeanOrbitalProducts
import Mathlib.MeasureTheory.Measure.Haar.Basic

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped ENNReal NNReal NumberField Pointwise

namespace Masullo

noncomputable section

private theorem measure_openCoordinate_zero
    {A L : Type*} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
    [LocallyCompactSpace A] [MeasurableSpace A] [BorelSpace A]
    [NontriviallyNormedField L] (μ : Measure A) [μ.IsAddHaarMeasure] [μ.InnerRegular]
    (p : A →+ L) (hc : Continuous p) (ho : IsOpenMap p) :
    μ (p ⁻¹' {0}) = 0 := by
  by_contra h
  let E := p ⁻¹' ({0} : Set L)
  have hE : MeasurableSet E := (isClosed_singleton.preimage hc).measurableSet
  have hn : E - E ∈ 𝓝 (0 : A) :=
    Measure.sub_mem_nhds_zero_of_addHaar_pos μ E hE (pos_iff_ne_zero.mpr h)
  have hp : p '' (E - E) ⊆ ({0} : Set L) := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_sub.mp hx
    change p a = 0 at ha
    change p b = 0 at hb
    change p (a-b) = 0
    rw [map_sub, ha, hb, sub_zero]
  have ht := mem_of_superset (ho.image_mem_nhds hn) hp
  rw [map_zero] at ht
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp ht
  obtain ⟨x, hx, hxr⟩ := NormedField.exists_norm_lt L hr
  have hx0 : x = 0 := hball (by simpa only [Metric.mem_ball, dist_zero_right] using hxr)
  simp [hx0] at hx

variable (F : Type*) [Field F] [NumberField F]
variable (S : Finset (HeightOneSpectrum (𝓞 F)))

private abbrev A := SAdeles F S
private abbrev G := (A F S)ˣ

attribute [local instance] sLocalZetaUnfolding_idelesMeasurable sLocalZetaUnfolding_idelesBorel

variable [MeasurableSpace (InfiniteAdeleRing F)] [BorelSpace (InfiniteAdeleRing F)]
  [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)]

local instance : SecondCountableTopology (InfiniteAdeleRing F) :=
  (infiniteAdeleMixedHomeomorph F).isEmbedding.secondCountableTopology

local instance (v : HeightOneSpectrum (𝓞 F)) : SecondCountableTopology (v.adicCompletion F) :=
  finitePlace_secondCountable F v

local instance (v : HeightOneSpectrum (𝓞 F)) : LocallyCompactSpace (v.adicCompletion F) :=
  finitePlace_locallyCompact F v

local instance : BorelSpace (A F S) := by
  dsimp only [A, SAdeles]
  infer_instance

local instance : T2Space (A F S) := by
  letI : T2Space (InfiniteAdeleRing F) :=
    (infiniteAdeleMixedHomeomorph F).isEmbedding.t2Space
  dsimp only [A, SAdeles]
  infer_instance

private abbrev η := sLocalAdditiveProduct F S (fun v ↦ additiveHaarDifferent F v.val)

/-- The selected additive Tamagawa measure is Haar. -/
theorem sLocalSelectedAdditive_isHaar : (η F S).IsAddHaarMeasure := by
  let d := sLocalFourierTailVolume F S
  have hp : 0 < d.toReal := sLocalFourierTailVolume_pos F S
  have hn : d ≠ 0 := fun h ↦ by rw [h, ENNReal.toReal_zero] at hp; exact (lt_irrefl _) hp
  have ht : d ≠ ∞ := fun h ↦ by rw [h, ENNReal.toReal_top] at hp; exact (lt_irrefl _) hp
  letI : (d • η F S).IsAddHaarMeasure := sLocalDifferentProduct_tail_isHaar F S
  have h := Measure.IsAddHaarMeasure.smul (d • η F S)
    (ENNReal.inv_ne_zero.mpr ht) (ENNReal.inv_ne_top.mpr hn)
  simpa only [smul_smul, ENNReal.inv_mul_cancel hn ht, one_smul] using h

omit [MeasurableSpace (InfiniteAdeleRing F)] [BorelSpace (InfiniteAdeleRing F)]
  [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)] in
/-- The local multiplicative coordinates embed as the open unit locus. -/
theorem sLocalUnits_openEmbedding : IsOpenEmbedding (Units.val : G F S → A F S) := by
  let V := (v : S) → v.val.adicCompletion F
  let e : G F S ≃ₜ (InfiniteAdeleRing F)ˣ × Vˣ := Homeomorph.prodUnits
  have hV : IsOpenEmbedding (Units.val : Vˣ → V) := by
    let p := (ContinuousMulEquiv.piUnits (M := fun v : S ↦ v.val.adicCompletion F)).toHomeomorph
    have h : IsOpenEmbedding (fun u : (v : S) → (v.val.adicCompletion F)ˣ ↦
        fun v ↦ (u v).val) := IsOpenEmbedding.piMap fun _ ↦ IsOpenUnits.isOpenEmbedding_unitsVal
    exact h.comp p.isOpenEmbedding
  exact ((infiniteIdele_value_openEmbedding F).prodMap hV).comp e.isOpenEmbedding

/-- Coordinate hyperplanes have zero additive Haar measure. Their finite
union is the complement of the S-ideles. -/
theorem sLocalSelectedAdditive_ae_unit :
    ∀ᵐ x ∂η F S, x ∈ range (Units.val : G F S → A F S) := by
  letI : (η F S).IsAddHaarMeasure := sLocalSelectedAdditive_isHaar F S
  letI : SecondCountableTopology (A F S) := inferInstanceAs
    (SecondCountableTopology (InfiniteAdeleRing F × ((v : S) → v.val.adicCompletion F)))
  letI : LocallyCompactSpace (A F S) := inferInstanceAs
    (LocallyCompactSpace (InfiniteAdeleRing F × ((v : S) → v.val.adicCompletion F)))
  letI : (η F S).Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _
  have hArch (v : InfinitePlace F) : ∀ᵐ x ∂η F S, x.1 v ≠ 0 := by
    have htwo : 1 < ‖(2 : v.Completion)‖ := by
      rw [← (InfinitePlace.Completion.isometry_extensionEmbedding v).norm_map_of_map_zero
        (map_zero _) (2 : v.Completion), map_ofNat]
      norm_num
    letI : NontriviallyNormedField v.Completion := ⟨⟨2, htwo⟩⟩
    let p : A F S →+ v.Completion :=
      (Pi.evalAddMonoidHom _ v).comp (AddMonoidHom.fst _ _)
    have ho : IsOpenMap p := (isOpenMap_eval v).comp isOpenMap_fst
    have h := measure_openCoordinate_zero (A := A F S) (L := v.Completion)
      (η F S) p ((continuous_apply v).comp continuous_fst) ho
    change η F S {x | x.1 v = 0} = 0 at h
    exact ae_iff.mpr (by simpa only [not_ne_iff] using h)
  have hFin (v : S) : ∀ᵐ x ∂η F S, x.2 v ≠ 0 := by
    let π := chosenFiniteUniformizer F v.val
    have hπ := norm_finiteUniformizer F v.val _ (chosenFiniteUniformizer_spec F v.val)
    have hq : 1 < (v.val.asIdeal.absNorm : ℝ) := by
      exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v.val
    letI : NontriviallyNormedField (v.val.adicCompletion F) :=
      ⟨⟨((π : v.val.adicCompletion F)⁻¹), by rw [norm_inv, hπ, inv_inv]; exact hq⟩⟩
    let p : A F S →+ v.val.adicCompletion F :=
      (Pi.evalAddMonoidHom _ v).comp (AddMonoidHom.snd _ _)
    have ho : IsOpenMap p := (isOpenMap_eval v).comp isOpenMap_snd
    have h := measure_openCoordinate_zero (A := A F S) (L := v.val.adicCompletion F)
      (η F S) p ((continuous_apply v).comp continuous_snd) ho
    change η F S {x | x.2 v = 0} = 0 at h
    exact ae_iff.mpr (by simpa only [not_ne_iff] using h)
  filter_upwards [ae_all_iff.mpr hArch, ae_all_iff.mpr hFin] with x hx hy
  have hu : IsUnit x := Prod.isUnit_iff.mpr
    ⟨Pi.isUnit_iff.mpr (fun v ↦ isUnit_iff_ne_zero.mpr (hx v)),
      Pi.isUnit_iff.mpr (fun v ↦ isUnit_iff_ne_zero.mpr (hy v))⟩
  exact hu

/-- The selected additive measure is proportional to multiplicative Haar
weighted by the actual S-idelic modulus, including at the omitted stages. -/
theorem sLocalSelectedAdditive_density (μ : Measure (G F S)) [μ.IsHaarMeasure] :
    ∃ c : ℝ≥0, c ≠ 0 ∧
      Measure.map (Units.val : G F S → A F S)
        (μ.withDensity (fun x ↦ ENNReal.ofReal (sLocalIdeleNorm F S x))) = c • η F S := by
  letI := sLocalIdeles_locallyCompact F S
  letI := sLocalIdeles_secondCountable F S
  letI : (η F S).IsAddHaarMeasure := sLocalSelectedAdditive_isHaar F S
  have hm : η F S ≠ 0 := fun hz ↦ isOpen_univ.measure_ne_zero (η F S) univ_nonempty
    (by simp [hz])
  exact additiveMeasure_eq_weighted_unitHaar (η F S) hm μ (sLocalUnits_openEmbedding F S)
    (sLocalSelectedAdditive_ae_unit F S) (sLocalIdeleNorm F S) (sLocalIdeleNorm_continuous F S)
    (sLocalIdeleNorm_positive F S) (sLocalAdditiveProduct_map_mul F S)

end

end Masullo
