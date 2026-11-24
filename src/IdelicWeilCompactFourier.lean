import IdelicWeilLogProfile
import IdelicHeckeFrequencyBoxes
import CompactBruhatFourierSynthesis
import ElementarySchwartzRefinement
import IdelicStageCofinalBasis
import IdelicCutoffKernel

open Bornology Filter Function MeasureTheory NumberField Set Topology
open scoped Classical NumberField

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]
private abbrev K := normOneIdeleClass F

local instance weilFourierNormOneCompact : CompactSpace (K F) := normOneIdeleClass_compact F
local instance weilFourierNormOneLocallyCompact : LocallyCompactSpace (K F) := inferInstance
local instance weilFourierNormOneMeasurable : MeasurableSpace (K F) := borel _
local instance weilFourierNormOneBorel : BorelSpace (K F) := ⟨rfl⟩
local instance weilFourierClassLocallyCompact : LocallyCompactSpace (IdeleClass F) := ideleClasses_locallyCompact
local instance weilFourierClassT2 : T2Space (IdeleClass F) := ideleClasses_hausdorff
local instance weilFourierClassSecondCountable : SecondCountableTopology (IdeleClass F) := ideleClass_secondCountable F
local instance weilFourierNormOneSecondCountable : SecondCountableTopology (K F) := IsInducing.subtypeVal.secondCountableTopology

private def normOneInclusion : K F →ₜ* IdeleClass F :=
  ⟨(K F).subtype, continuous_subtype_val⟩

private theorem normOne_stage_kernel_map (Q : WholeBruhatStage (IdeleClass F)) :
    (Q.val.1.kernel.comap (K F).subtype).map (K F).subtype = Q.val.1.kernel := by
  have hle : Q.val.1.kernel ≤ K F := by
    change Q.val.1.kernel ≤ normOneIdeleClass F
    rw [← ideleClassLogNorm_ker_eq_normOne F]
    intro x hx
    exact Q.val.1.modulation_eq_one_on_kernel (mellinClassModulus F) ⟨x, hx⟩
  ext x
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact hk
  · intro hx
    exact ⟨⟨x, hle hx⟩, hx, rfl⟩

set_option maxHeartbeats 950000 in
/-- A translate of an idelic Bruhat test restricts to a Schwartz–Bruhat
test on the compact norm-one classes. -/
theorem exists_normOneBruhat_slice (f : BruhatCompactTest (IdeleClass F)) (g : IdeleClass F) :
    ∃ u : BruhatSchwartz (K F), ∀ k : K F, u.val k = f.val.val (k.val * g) := by
  let m := mellinClassModulus F
  have hm : IsProperMap m :=
    isProperMap_snd_of_compactSpace.comp (ideleClassSplitHomeomorph F).isProperMap
  have hms : Surjective m :=
    fun t => ⟨ideleClassExpSection F t, ideleClassLogNorm_expSection F t⟩
  obtain ⟨R, u, hu⟩ := f.val.property
  obtain ⟨Q, hRQ⟩ := exists_wholeBruhatStage_refinement m hm hms R
  let w := R.transition Q.val hRQ u
  have hw : Q.val.realize w = f.val.val :=
    (congrArg Subtype.val (R.inclusion_transition Q.val hRQ u)).trans hu
  let j := normOneInclusion F
  let H := Q.val.1.kernel.comap (K F).subtype
  have hH : IsCompact (H : Set (K F)) :=
    (Q.val.1.kernel_closed.preimage continuous_subtype_val).isCompact
  have hgen : IsCompactlyGeneratedGroup (lcaAnnihilator (G := IdeleClass F) (H.map (K F).subtype)) :=
    normOne_stage_kernel_map F Q ▸ Q.val.1.annihilator_compactlyGenerated
  obtain ⟨P, hP⟩ := exists_normOneWholeBruhatStage F H hH hgen
  have hker : P.val.1.kernel ≤ Q.val.1.kernel.comap j.toMonoidHom := hP.le
  let A := P.coordinateModel
  let B := Q.coordinateModel
  let q := P.coordinateMap Q j hker
  let ϕ : A →+ B := q.toMonoidHom.toAdditive
  have hc : Continuous ϕ := continuous_toAdd.comp (q.continuous.comp continuous_ofAdd)
  have hs : Surjective (fun x : K F => (P.coordinates x).toAdd) :=
    Multiplicative.toAdd.surjective.comp P.coordinates_surjective
  letI : CompactSpace A := hs.compactSpace (continuous_toAdd.comp P.coordinates.continuous)
  have hp : IsProperMap ϕ := hc.isProperMap
  let w' := elementarySchwartz_translate (Q.coordinates g).toAdd w
  let v := elementarySchwartz_properPullback ϕ hp w'
  refine ⟨P.val.inclusion v, fun k => ?_⟩
  have harg : ϕ (P.coordinates k).toAdd = (Q.coordinates k.val).toAdd :=
    congrArg Multiplicative.toAdd (P.coordinateMap_coordinates Q j hker k)
  calc
    _ = w'.val (ϕ (P.coordinates k).toAdd) := P.realize_eq_coordinates v k
    _ = w'.val (Q.coordinates k.val).toAdd := congrArg w'.val harg
    _ = w.val ((Q.coordinates (k.val * g)).toAdd) := by
      change w.val ((Q.coordinates k.val).toAdd + (Q.coordinates g).toAdd) = _
      exact congrArg (fun y : Multiplicative B => w.val y.toAdd) (map_mul Q.coordinates k.val g).symm
    _ = f.val.val (k.val * g) :=
      (Q.realize_eq_coordinates w _).symm.trans (congrFun hw _)

variable (ν : Measure (K F)) [ν.IsHaarMeasure]

set_option maxHeartbeats 750000 in
/-- Norm-one Fourier synthesis reconstructs an idelic test from the
normalized coefficients of its compact norm-one slice. -/
theorem hasSum_idelicWeil_compactCoefficients (f : BruhatCompactTest (IdeleClass F))
    (g : IdeleClass F) (k : K F) :
    HasSum (fun χ : PontryaginDual (K F) =>
      ((ν.real univ : ℂ)⁻¹ * ∫ a : K F, (χ a : ℂ) * f.val.val (a.val * g) ∂ν) *
        (((χ k)⁻¹ : Circle) : ℂ)) (f.val.val (k.val * g)) := by
  letI : IsFiniteMeasure ν := ⟨isCompact_univ.measure_lt_top⟩
  letI : Measure.Regular ν := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure ν
  obtain ⟨u, hu⟩ := exists_normOneBruhat_slice F f g
  let ev : BruhatSchwartz (K F) →L[ℂ] ℂ :=
    ⟨(LinearMap.proj k).comp (bruhatSchwartzSubmodule (G := K F)).subtype,
      bruhatSchwartz_continuous_eval k⟩
  have hsum := (hasSum_compactBruhatFourierSeries ν u).mapL ev
  have he : ev u = f.val.val (k.val * g) := hu k
  rw [he] at hsum
  refine hsum.congr_fun fun χ => ?_
  change ((ν.real univ : ℂ)⁻¹ * ∫ a : K F, (χ a : ℂ) * f.val.val (a.val * g) ∂ν) *
      (((χ k)⁻¹ : Circle) : ℂ) =
    ev (compactBruhatFourierCoeff ν χ u • compactBruhatCharacter χ⁻¹)
  rw [map_smul, smul_eq_mul, compactBruhatFourierCoeff_apply]
  have hi : (∫ a : K F, (χ a : ℂ) * f.val.val (a.val * g) ∂ν) =
      ∫ a : K F, u.val a * (χ a : ℂ) ∂ν := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun a => by
      change (χ a : ℂ) * f.val.val (a.val * g) = u.val a * (χ a : ℂ)
      rw [hu, mul_comm]
  rw [hi]
  rfl

/-- The normalized logarithmic Fourier profiles reconstruct the value on the norm section. -/
theorem hasSum_idelicWeilLogProfile (f : BruhatCompactTest (IdeleClass F)) (t : ℝ) :
    HasSum (fun χ : PontryaginDual (K F) =>
      (ν.real univ : ℂ)⁻¹ * idelicWeilLogProfile F ν χ f t)
      (f.val.val (ideleClassExpSection F (Multiplicative.ofAdd t))) := by
  let g := ideleClassExpSection F (Multiplicative.ofAdd t)
  have h := hasSum_idelicWeil_compactCoefficients F ν f g (1 : K F)
  have he : (1 : K F).val * g = g := @one_mul (IdeleClass F) inferInstance g
  rw [he] at h
  refine h.congr_fun fun χ => ?_
  change _ = ((ν.real univ : ℂ)⁻¹ * idelicWeilLogProfile F ν χ f t) *
    (((χ (1 : K F))⁻¹ : Circle) : ℂ)
  rw [map_one, inv_one, Circle.coe_one, mul_one]

/-- The discriminant part of the characterwise contact terms reconstructs
the single global discriminant contact term in the idelic formula. -/
theorem idelicWeil_discriminantContact_hasSum (f : BruhatCompactTest (IdeleClass F)) :
    HasSum (fun χ : PontryaginDual (K F) => (ν.real univ : ℂ)⁻¹ *
      ((Real.log ((discr F).natAbs : ℝ) : ℂ) * (idelicWeilCenteredTest F ν χ f).val 0))
      ((Real.log ((discr F).natAbs : ℝ) : ℂ) * f.val.val 1) := by
  have h := (hasSum_idelicWeilLogProfile F ν f 0).mul_left (Real.log ((discr F).natAbs : ℝ) : ℂ)
  rw [show ideleClassExpSection F (Multiplicative.ofAdd (0 : ℝ)) = 1 from map_one _] at h
  refine h.congr_fun fun χ => ?_
  change _ * (_ * idelicWeilLogProfile F ν χ f 0) = _ * (_ * idelicWeilLogProfile F ν χ f 0)
  ring

set_option maxHeartbeats 850000 in
/-- Fourier synthesis may be integrated against any finite measure on
a norm-one slice. -/
theorem hasSum_idelicWeil_compactIntegral {J : Type*} [MeasurableSpace J]
    (μ : Measure J) [IsFiniteMeasure μ] (j : J → K F) (hj : Measurable j)
    (f : BruhatCompactTest (IdeleClass F)) (g : IdeleClass F) :
    HasSum (fun χ : PontryaginDual (K F) =>
      ((ν.real univ : ℂ)⁻¹ * ∫ a : K F, (χ a : ℂ) * f.val.val (a.val * g) ∂ν) *
        (∫ u, (((χ (j u))⁻¹ : Circle) : ℂ) ∂μ))
      (∫ u, f.val.val ((j u).val * g) ∂μ) := by
  by_cases hz : μ = 0
  · simp only [hz, integral_zero_measure, mul_zero]
    exact hasSum_zero
  letI : IsFiniteMeasure ν := ⟨isCompact_univ.measure_lt_top⟩
  letI : Measure.Regular ν := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure ν
  obtain ⟨w, hw⟩ := exists_normOneBruhat_slice F f g
  let τ : Measure (K F) := Measure.map j μ
  letI : IsFiniteMeasure τ := Measure.isFiniteMeasure_map μ j
  let ev := (τ.real univ : ℂ) • compactBruhatFourierCoeff τ (1 : PontryaginDual (K F))
  have hτ : (τ.real univ : ℂ) ≠ 0 := by
    apply Complex.ofReal_ne_zero.mpr
    exact ENNReal.toReal_ne_zero.mpr
      ⟨by
        change (Measure.map j μ) univ ≠ 0
        rw [Measure.map_apply hj MeasurableSet.univ, preimage_univ]
        exact fun h => hz (Measure.measure_univ_eq_zero.mp h),
        measure_ne_top _ _⟩
  have he (u : BruhatSchwartz (K F)) : ev u = ∫ x, u.val (j x) ∂μ := by
    change (τ.real univ : ℂ) * compactBruhatFourierCoeff τ (1 : PontryaginDual (K F)) u = _
    rw [compactBruhatFourierCoeff_apply, ← mul_assoc, mul_inv_cancel₀ hτ, one_mul]
    change (∫ a : K F, u.val a * (1 : ℂ) ∂τ) = _
    simp only [mul_one]
    exact integral_map hj.aemeasurable (bruhatSchwartz_continuous u).aestronglyMeasurable
  have hwEval : ev w = ∫ u, f.val.val ((j u).val * g) ∂μ := by
    rw [he]
    exact integral_congr_ae (Eventually.of_forall fun x => hw (j x))
  have h := (hasSum_compactBruhatFourierSeries ν w).mapL ev
  rw [hwEval] at h
  refine h.congr_fun fun χ => ?_
  change _ = ev (compactBruhatFourierCoeff ν χ w • compactBruhatCharacter χ⁻¹)
  rw [map_smul, smul_eq_mul, compactBruhatFourierCoeff_apply, he]
  have hi : (∫ a : K F, (χ a : ℂ) * f.val.val (a.val * g) ∂ν) =
      ∫ a : K F, w.val a * (χ a : ℂ) ∂ν := by
    apply integral_congr_ae
    exact Eventually.of_forall fun a => by
      change (χ a : ℂ) * f.val.val (a.val * g) = w.val a * (χ a : ℂ)
      rw [hw, mul_comm]
  rw [hi]
  rfl

/-- In particular, Fourier synthesis commutes with probability averages
over a norm-one slice. -/
theorem hasSum_idelicWeil_compactAverage {J : Type*} [MeasurableSpace J]
    (μ : Measure J) [IsProbabilityMeasure μ] (j : J → K F) (hj : Measurable j)
    (f : BruhatCompactTest (IdeleClass F)) (g : IdeleClass F) :
    HasSum (fun χ : PontryaginDual (K F) =>
      ((ν.real univ : ℂ)⁻¹ * ∫ a : K F, (χ a : ℂ) * f.val.val (a.val * g) ∂ν) *
        (∫ u, (((χ (j u))⁻¹ : Circle) : ℂ) ∂μ))
      (∫ u, f.val.val ((j u).val * g) ∂μ) :=
  hasSum_idelicWeil_compactIntegral F ν μ j hj f g

end
end Masullo
