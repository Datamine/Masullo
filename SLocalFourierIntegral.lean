import SLocalFourierStage
import AdelicTamagawaProduct

open Filter IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical ENNReal NumberField

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]
variable (S : Finset (HeightOneSpectrum (𝓞 F)))

private abbrev A := Adeles F
private abbrev E := sLocalBruhatImage F S

private theorem sLocalBruhatPad_continuous :
    Continuous (sLocalBruhatPad F S) := by
  apply continuous_fst.prodMk
  exact (finiteCoordinateSplit F S).continuous.comp (continuous_snd.prodMk continuous_const)

/-- Compression of the adelic Fourier operator by the projection onto
the S-local test space. -/
def sLocalFourierCompression : E F S →L[ℂ] E F S :=
  (sLocalBruhatCorestrict F S).comp
    ((GlobalBruhat.fourier F).comp (sLocalBruhatImage F S).subtypeL)

theorem sLocalStageFourier_eq_compression
    (hS : ∀ f ∈ E F S, GlobalBruhat.fourier F f ∈ E F S) :
    sLocalStageFourier F S hS = sLocalFourierCompression F S := by
  apply ContinuousLinearMap.ext
  intro f
  apply Subtype.ext
  change GlobalBruhat.fourier F f.val =
    sLocalBruhatProjection F S (GlobalBruhat.fourier F f.val)
  exact (sLocalBruhatProjection_fixes F S _ (hS f.val f.property)).symm

local instance : MeasurableSpace (A F) := borel _
local instance : BorelSpace (A F) := ⟨rfl⟩

variable [MeasurableSpace (InfiniteAdeleRing F)] [BorelSpace (InfiniteAdeleRing F)]
variable [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)]

local instance : BorelSpace (SAdeles F S) := by
  letI : SecondCountableTopology (InfiniteAdeleRing F) :=
    (infiniteAdeleMixedHomeomorph F).isEmbedding.secondCountableTopology
  letI (v : HeightOneSpectrum (𝓞 F)) :
      SecondCountableTopology (v.adicCompletion F) := finitePlace_secondCountable F v
  infer_instance

/-- The selected additive Tamagawa factors and the volume contribution of
the omitted integral places. -/
def sLocalFourierCompressionMeasure : Measure (SAdeles F S) :=
  (∏ᶠ v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S}, differentPrimeMass F v.val) •
    sLocalAdditiveProduct F S (fun v => additiveHaarDifferent F v.val)

theorem sLocalFourierCompressionMeasure_eq_map :
    sLocalFourierCompressionMeasure F S =
      ((adelicHaarUnitDomain F).restrict (globalIntegralBlock F S : Set (A F))).map
        (sAdelesProjection F S) := by
  ext T hT
  rw [Measure.map_apply (sAdelesProjection_continuous F S).measurable hT,
    Measure.restrict_apply ((sAdelesProjection_continuous F S).measurable hT)]
  rw [sLocalFourierCompressionMeasure, Measure.smul_apply, smul_eq_mul, ←
    adelicHaarUnitDomain_restrictedProduct F S T hT]
  congr 1
  ext a
  exact and_comm

set_option maxHeartbeats 600000 in
/-- The compressed operator is the genuine Fourier integral in the
S-local coordinates with its explicit tail-volume normalization. -/
theorem sLocalFourierCompression_restrict (f : E F S) (ξ : SAdeles F S) :
    sLocalBruhatRestriction F S (sLocalFourierCompression F S f).val ξ =
      ∫ x : SAdeles F S, sLocalBruhatRestriction F S f.val x *
        ((standardAdelicCharacter F (sLocalBruhatPad F S (x * ξ))).toMul : ℂ)
        ∂sLocalFourierCompressionMeasure F S := by
  let j := sAdelesProjection F S
  let ψ := standardAdelicCharacter F
  let U : Set (A F) := globalIntegralBlock F S
  let g (x : SAdeles F S) := sLocalBruhatRestriction F S f.val x *
        ((ψ (sLocalBruhatPad F S (x * ξ))).toMul : ℂ)
  have hg : Continuous g :=
    (sLocalBruhatRestriction_continuous F S f.val).mul
      (continuous_subtype_val.comp (continuous_toMul.comp
        ((standardAdelicCharacter_continuous F).comp
          ((sLocalBruhatPad_continuous F S).comp (continuous_id.mul continuous_const)))))
  change sLocalBruhatRestriction F S
      (sLocalBruhatCorestrict F S (GlobalBruhat.fourier F f.val)).val ξ =
    ∫ x, g x ∂sLocalFourierCompressionMeasure F S
  rw [sLocalBruhatCorestrict_restrict, sLocalFourierCompressionMeasure_eq_map]
  have hj : Measurable j := (sAdelesProjection_continuous F S).measurable
  rw [integral_map hj.aemeasurable hg.aestronglyMeasurable]
  have hU : MeasurableSet U := (globalIntegralBlock_open F S).measurableSet
  rw [← integral_indicator hU]
  change (GlobalBruhat.algebraicEquiv F (GlobalBruhat.fourier F f.val)).val
    (sLocalBruhatPad F S ξ) = _
  rw [GlobalBruhat.fourier_apply, adelicFourierIntegral]
  refine integral_congr_ae (G := ℂ) (μ := adelicHaarUnitDomain F)
    (f := fun a => GlobalBruhat.evaluation F a f.val * ((ψ (a * sLocalBruhatPad F S ξ)).toMul : ℂ))
    (g := U.indicator (g ∘ j)) (.of_forall fun a => ?_)
  change GlobalBruhat.evaluation F a f.val * ((ψ (a * sLocalBruhatPad F S ξ)).toMul : ℂ) =
    U.indicator (g ∘ j) a
  rw [sLocalBruhatRestriction_reconstruct, ← sLocalBruhatPad_mul_project]
  by_cases ha : a ∈ U
  · rw [indicator_of_mem ha]
    change ∀ v ∉ S, a.2 v ∈ v.adicCompletionIntegers F at ha
    rw [ite_eq_left ha, mul_one]
    rfl
  · rw [indicator_of_notMem ha]
    change ¬ ∀ v ∉ S, a.2 v ∈ v.adicCompletionIntegers F at ha
    rw [ite_eq_right ha, mul_zero, zero_mul]

/-- A stage containing the different has the selected Tamagawa Fourier
integral as its restriction of the global transform. -/
theorem sLocalFourier_tamagawa_of_different
    (hS : ∀ v : HeightOneSpectrum (𝓞 F), v.asIdeal ∣ differentIdeal ℤ (𝓞 F) → v ∈ S)
    (f : E F S) (ξ : SAdeles F S) :
    sLocalBruhatRestriction F S
        (sLocalStageFourier F S (sLocalFourier_preserves_stage_of_different F S hS) f).val ξ =
      ∫ x : SAdeles F S, sLocalBruhatRestriction F S f.val x *
        ((standardAdelicCharacter F (sLocalBruhatPad F S (x * ξ))).toMul : ℂ)
        ∂sLocalAdditiveProduct F S (fun v => additiveHaarDifferent F v.val) := by
  have hmass (v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S}) :
      differentPrimeMass F v.val = 1 := by
    have hv : ¬ v.val.asIdeal ∣ differentIdeal ℤ (𝓞 F) := fun h ↦ v.property (hS v.val h)
    simp [differentPrimeMass, multiplicity_eq_zero.mpr hv]
  rw [sLocalStageFourier_eq_compression, sLocalFourierCompression_restrict,
    sLocalFourierCompressionMeasure, finprod_eq_one_of_forall_eq_one hmass, one_smul]

/-- On all sufficiently large stages, the genuine local Fourier integral
with the selected Tamagawa measures is the restriction of global Fourier. -/
theorem exists_finset_sLocalFourier_tamagawa_stages :
    ∃ S₀ : Finset (HeightOneSpectrum (𝓞 F)), ∀ S, S₀ ⊆ S →
      ∃ hS : ∀ f ∈ E F S, GlobalBruhat.fourier F f ∈ E F S,
        ∀ (f : E F S) (ξ : SAdeles F S),
          sLocalBruhatRestriction F S (sLocalStageFourier F S hS f).val ξ =
            ∫ x : SAdeles F S, sLocalBruhatRestriction F S f.val x *
              ((standardAdelicCharacter F (sLocalBruhatPad F S (x * ξ))).toMul : ℂ)
              ∂sLocalAdditiveProduct F S (fun v => additiveHaarDifferent F v.val) := by
  let D := (Ideal.finite_factors (differentIdeal_ne_bot (A := ℤ) (B := 𝓞 F))).toFinset
  refine ⟨D, fun S hDS ↦ ?_⟩
  have hS : ∀ v : HeightOneSpectrum (𝓞 F), v.asIdeal ∣ differentIdeal ℤ (𝓞 F) → v ∈ S :=
    fun v hv ↦ hDS (by simpa [D] using hv)
  exact ⟨sLocalFourier_preserves_stage_of_different F S hS,
    sLocalFourier_tamagawa_of_different F S hS⟩

end
end Masullo
