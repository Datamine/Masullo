import SLocalPairedMellin
import IdelicDoublingTransfer
import Mathlib.MeasureTheory.Integral.Prod

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical ENNReal NumberField Pointwise

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]
variable (S : Finset (HeightOneSpectrum (𝓞 F)))

private abbrev E := sLocalBruhatImage F S
private abbrev A := Adeles F

local instance : MeasurableSpace (A F) := borel _
local instance : BorelSpace (A F) := ⟨rfl⟩

variable [MeasurableSpace (InfiniteAdeleRing F)] [BorelSpace (InfiniteAdeleRing F)]
  [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)]

local instance : SecondCountableTopology (SAdeles F S) := by
  letI : SecondCountableTopology (InfiniteAdeleRing F) :=
    (infiniteAdeleMixedHomeomorph F).isEmbedding.secondCountableTopology
  letI (v : HeightOneSpectrum (𝓞 F)) :
      SecondCountableTopology (v.adicCompletion F) := finitePlace_secondCountable F v
  infer_instance

local instance : BorelSpace (SAdeles F S) := by
  letI : SecondCountableTopology (InfiniteAdeleRing F) :=
    (infiniteAdeleMixedHomeomorph F).isEmbedding.secondCountableTopology
  letI (v : HeightOneSpectrum (𝓞 F)) :
      SecondCountableTopology (v.adicCompletion F) := finitePlace_secondCountable F v
  infer_instance

private abbrev localAddHaar :=
  sLocalAdditiveProduct F S (fun v ↦ additiveHaarDifferent F v.val)

/-- The restriction of every stage test is integrable for the selected
additive Tamagawa measure. -/
theorem sLocalBruhatRestriction_integrable_additive (f : E F S) :
    Integrable (sLocalBruhatRestriction F S f.val) (localAddHaar F S) := by
  let η := adelicHaarUnitDomain F
  let D : Set (A F) := globalIntegralBlock F S
  let j := sAdelesProjection F S
  let R := sLocalBruhatRestriction F S f.val
  have hR : Continuous R := sLocalBruhatRestriction_continuous F S f.val
  have hj : Continuous j := sAdelesProjection_continuous F S
  let u := (GlobalBruhat.algebraicEquiv F f.val).val
  have hu : Integrable u η := by
    have h := bruhat_dilate_integrable F (GlobalBruhat.algebraicEquiv F f.val).property (1 : Idele F)
    change Integrable (fun x : A F ↦ u (1*x)) η at h
    simpa only [one_mul] using h
  have hh : Integrable (R ∘ j) (η.restrict D) := by
    apply hu.integrableOn.congr
    filter_upwards [ae_restrict_mem (globalIntegralBlock_open F S).measurableSet] with x hx
    change GlobalBruhat.evaluation F x f.val = R (j x)
    rw [sLocalBruhatRestriction_reconstruct]
    change (R (j x) * (if ∀ v ∉ S, x.2 v ∈ v.adicCompletionIntegers F then 1 else 0)) = _
    change ∀ v ∉ S, x.2 v ∈ v.adicCompletionIntegers F at hx
    rw [ite_eq_left hx, mul_one]
  have hC : Integrable R (sLocalFourierCompressionMeasure F S) := by
    rw [sLocalFourierCompressionMeasure_eq_map]
    exact (integrable_map_measure hR.aestronglyMeasurable hj.measurable.aemeasurable).2 hh
  have hn : sLocalFourierTailVolume F S ≠ 0 := by
    intro hz
    have h := sLocalFourierTailVolume_pos F S
    rw [hz, ENNReal.toReal_zero] at h
    exact lt_irrefl _ h
  have ht : sLocalFourierTailVolume F S ≠ ∞ := by
    intro hz
    have h := sLocalFourierTailVolume_pos F S
    rw [hz, ENNReal.toReal_top] at h
    exact lt_irrefl _ h
  rw [sLocalFourierCompressionMeasure] at hC
  exact (integrable_smul_measure hn ht).mp hC

/-- The scaled local additive Fourier pairing is symmetric for all
Schwartz–Bruhat tests at every finite stage. -/
theorem sLocalSelectedFourier_pairing (f g : E F S) (u : SAdeles F S)
    [SFinite (localAddHaar F S)] :
    (∫ x, sLocalBruhatRestriction F S f.val x *
      sLocalBruhatRestriction F S (sLocalSelectedFourier F S g).val (u * x) ∂localAddHaar F S) =
    ∫ x, sLocalBruhatRestriction F S g.val x *
      sLocalBruhatRestriction F S (sLocalSelectedFourier F S f).val (u * x) ∂localAddHaar F S := by
  let η := localAddHaar F S
  let f₀ := sLocalBruhatRestriction F S f.val
  let g₀ := sLocalBruhatRestriction F S g.val
  let B (p : SAdeles F S × SAdeles F S) : ℂ :=
    ((standardAdelicCharacter F (sLocalBruhatPad F S (p.2 * (u * p.1)))).toMul : ℂ)
  let H (p : SAdeles F S × SAdeles F S) : ℂ := f₀ p.1 * g₀ p.2 * B p
  have hf : Integrable f₀ η := sLocalBruhatRestriction_integrable_additive F S f
  have hg : Integrable g₀ η := sLocalBruhatRestriction_integrable_additive F S g
  have hPad : Continuous (sLocalBruhatPad F S) := by
    apply continuous_fst.prodMk
    exact (finiteCoordinateSplit F S).continuous.comp (continuous_snd.prodMk continuous_const)
  have hPhase : Continuous B :=
    (continuous_subtype_val.comp (continuous_toMul.comp
      ((standardAdelicCharacter_continuous F).comp hPad))).comp
        (continuous_snd.mul (continuous_const.mul continuous_fst))
  have hMeas : Continuous H :=
    (((sLocalBruhatRestriction_continuous F S f.val).comp continuous_fst).mul
      ((sLocalBruhatRestriction_continuous F S g.val).comp continuous_snd)).mul
        hPhase
  have hH : Integrable H (η.prod η) := by
    refine (hf.mul_prod hg).mono hMeas.aestronglyMeasurable (.of_forall fun p ↦ ?_)
    change ‖f₀ p.1 * g₀ p.2 * B p‖ ≤ ‖f₀ p.1 * g₀ p.2‖
    rw [norm_mul, show ‖B p‖ = 1 from Circle.norm_coe _, mul_one]
  simp_rw [sLocalSelectedFourier_restrict]
  calc
    _ = ∫ x, ∫ y, H (x,y) ∂η ∂η := by
      congr 1
      funext x
      dsimp [H, B, f₀, g₀]
      rw [← integral_const_mul]
      simp only [mul_assoc, η]
    _ = ∫ y, ∫ x, H (x,y) ∂η ∂η := integral_integral_swap hH
    _ = _ := by
      congr 1
      funext y
      rw [← integral_const_mul]
      apply integral_congr_ae
      refine .of_forall fun x ↦ ?_
      dsimp [H, B, f₀, g₀]
      have he : y * (u * x) = x * (u * y) := by ac_rfl
      rw [he, mul_comm (sLocalBruhatRestriction F S f.val x),
        mul_assoc]

/-- Multiplication by a unit changes the selected additive measure by the
inverse of its normalized S-idelic modulus under pushforward. -/
theorem sLocalAdditiveProduct_map_mul (u : (SAdeles F S)ˣ) :
    (localAddHaar F S).map (fun x ↦ u.val * x) =
      (ENNReal.ofReal (sLocalIdeleNorm F S u))⁻¹ • localAddHaar F S := by
  let μ := adelicHaarUnitDomain F
  letI : μ.IsAddHaarMeasure := adelicHaarUnitDomain_isHaar F
  let D : Set (A F) := globalIntegralBlock F S
  let b := (sLocalEmbed F S u).val
  let j := sAdelesProjection F S
  let m (x : SAdeles F S) := u.val * x
  let c := ENNReal.ofReal ((sLocalIdeleNorm F S u)⁻¹)
  have hm : Measurable m := (continuous_const.mul continuous_id).measurable
  have hj : Measurable j := (sAdelesProjection_continuous F S).measurable
  have hD : MeasurableSet D := (globalIntegralBlock_open F S).measurableSet
  have hpres (x : A F) : b.val * x ∈ D ↔ x ∈ D := by
    change (∀ v ∉ S, (b.val * x).2 v ∈ v.adicCompletionIntegers F) ↔
      ∀ v ∉ S, x.2 v ∈ v.adicCompletionIntegers F
    apply forall_congr'
    intro v
    apply imp_congr_right
    intro hv
    change b.val.2 v * x.2 v ∈ v.adicCompletionIntegers F ↔ _
    rw [show b.val.2 v = 1 from sLocalEmbed_outside_one F S u v hv, one_mul]
  have hscale : (sLocalFourierCompressionMeasure F S).map m =
      c • sLocalFourierCompressionMeasure F S := by
    ext T hT
    rw [sLocalFourierCompressionMeasure_eq_map, Measure.map_apply hm hT,
      Measure.map_apply hj (hm hT), Measure.smul_apply, Measure.map_apply hj hT,
      Measure.restrict_apply (hj (hm hT)), Measure.restrict_apply (hj hT), smul_eq_mul]
    have he : j ⁻¹' (m ⁻¹' T) ∩ D = b⁻¹ • (j ⁻¹' T ∩ D) := by
      ext x
      rw [mem_smul_set_iff_inv_smul_mem, inv_inv]
      have hjm : j (b.val * x) = m (j x) := by
        change sAdelesProjection F S (b.val*x) = _
        rw [map_mul, sLocalEmbed_project F S u]
      change (m (j x) ∈ T ∧ x ∈ D) ↔ j (b.val * x) ∈ T ∧ b.val * x ∈ D
      rw [hjm, hpres]
    rw [he, adelicHaar_smul F b⁻¹ μ, map_inv (ideleNorm F)]
    rfl
  let d := sLocalFourierTailVolume F S
  have hd0 : d ≠ 0 := by
    intro h
    have hp : 0 < d.toReal := sLocalFourierTailVolume_pos F S
    rw [h, ENNReal.toReal_zero] at hp
    exact (lt_irrefl _) hp
  have hdt : d ≠ ∞ := by
    intro h
    have hp : 0 < d.toReal := sLocalFourierTailVolume_pos F S
    rw [h, ENNReal.toReal_top] at hp
    exact (lt_irrefl _) hp
  change (d • localAddHaar F S).map m = c • (d • localAddHaar F S) at hscale
  rw [Measure.map_smul, smul_comm c d] at hscale
  have he := congrArg (fun η : Measure (SAdeles F S) ↦ d⁻¹ • η) hscale
  simp only [smul_smul, ← mul_assoc, ENNReal.inv_mul_cancel hd0 hdt, one_mul, one_smul] at he
  change _ = (ENNReal.ofReal (sLocalIdeleNorm F S u))⁻¹ • localAddHaar F S
  have hc : c = (ENNReal.ofReal (sLocalIdeleNorm F S u))⁻¹ := ENNReal.ofReal_inv_of_pos
    (sLocalIdeleNorm_positive F S u)
  rw [hc] at he
  exact he

end

end Masullo
