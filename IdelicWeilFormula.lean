import FiniteIdeleTamagawa
import IdelicWeilComplexComparison
import IdelicWeilFiniteComparison
import IdelicWeilGeometric
import IdelicWeilRealComparison

open Bornology Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical NumberField

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

private abbrev K := normOneIdeleClass F
private abbrev Place := HeightOneSpectrum (𝓞 F)
private abbrev Charts := ∀ w : PontryaginDual (K F), CompletedHeckeChart F w
private abbrev R := {v : InfinitePlace F // v.IsReal}
private abbrev C := {v : InfinitePlace F // v.IsComplex}
private abbrev χ (w : PontryaginDual (K F)) := heckeOrdinateCharacter F w 0

local instance weilFormulaClassLC : LocallyCompactSpace (IdeleClass F) := ideleClasses_locallyCompact
local instance weilFormulaClassT2 : T2Space (IdeleClass F) := ideleClasses_hausdorff
local instance weilFormulaNormOneMeasurable : MeasurableSpace (K F) := borel _
local instance weilFormulaNormOneBorel : BorelSpace (K F) := ⟨rfl⟩
local instance weilFormulaIdeleMeasurable : MeasurableSpace (Idele F) := borel _
local instance weilFormulaIdeleBorel : BorelSpace (Idele F) := ⟨rfl⟩
local instance weilFormulaCompletionMeasurable (v : Place F) : MeasurableSpace (v.adicCompletion F) := borel _
local instance weilFormulaCompletionBorel (v : Place F) : BorelSpace (v.adicCompletion F) := ⟨rfl⟩

private theorem idelicWeil_archSplit (f : BruhatCompactTest (IdeleClass F)) :
    (∑ v : R F, realPlaceIdelicWeilTerm F f v.val v.property) +
      (∑ v : C F, complexPlaceIdelicWeilTerm F f v.val v.property) =
      ∑ v : InfinitePlace F, infinitePlaceIdelicWeilDual F v f := by
  let d (v : InfinitePlace F) := infinitePlaceIdelicWeilDual F v f
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun v : InfinitePlace F => v.IsReal) d]
  congr 1
  · rw [Finset.sum_subtype (p := fun v : InfinitePlace F => v.IsReal) _ (by simp) d]
    exact Finset.sum_congr rfl (fun v _ => (infinitePlaceIdelicWeilDual_apply_real F v.val v.property f).symm)
  · rw [Finset.sum_subtype (p := fun v : InfinitePlace F => v.IsComplex) _
      (fun v => by simp [InfinitePlace.not_isReal_iff_isComplex]) d]
    exact Finset.sum_congr rfl (fun v _ => (infinitePlaceIdelicWeilDual_apply_complex F v.val v.property f).symm)

variable (ν : Measure (K F)) [ν.IsHaarMeasure] (E : Charts F)
  (T : PontryaginDual (K F) → Finset (Place F))
  (hT : ∀ w, Surjective (sIdeleClassInclusion F (T w)))
  (huT : ∀ w, globalNormOneCharacter F (heckeNormOneRestriction F (χ F w)⁻¹) ∈
    (sUnramified F (T w) : Set (QuasiCharacter (IdeleClass F))))

private theorem formulaForward_unramified (w : PontryaginDual (K F)) :
    globalNormOneCharacter F (heckeNormOneRestriction F (χ F w)) ∈
      (sUnramified F (E w).stage : Set (QuasiCharacter (IdeleClass F))) := by
  rw [heckeNormOneRestriction_ordinateCharacter]
  exact (E w).unramified

/-- The characterwise archimedean terms sum to the signed geometric
archimedean distribution. -/
theorem idelicWeil_archComparison_hasSum (f : BruhatCompactTest (IdeleClass F)) :
    HasSum (fun w : PontryaginDual (K F) =>
      (ν.real univ : ℂ)⁻¹ * heckeCenteredArchTerm F (χ F w) (E w).stage (E w).surj
        (formulaForward_unramified F E w) (T w) (hT w) (huT w) 0
        (idelicWeilCenteredTest F ν w f))
      (-(∑ v : InfinitePlace F, infinitePlaceIdelicWeilDual F v f)) := by
  let r (v : R F) (w : PontryaginDual (K F)) := (ν.real univ : ℂ)⁻¹ *
    heckeCenteredGammaTerm (idelicWeilCenteredTest F ν w f) (1 / 2) Real.pi
      (manuscriptHeckeRealGammaShift F (χ F w) (E w).stage (E w).surj
        (formulaForward_unramified F E w) 0 v)
      (manuscriptHeckeRealGammaShift F (χ F w)⁻¹ (T w) (hT w) (huT w) 0 v)
  let c (v : C F) (w : PontryaginDual (K F)) := (ν.real univ : ℂ)⁻¹ *
    heckeCenteredGammaTerm (idelicWeilCenteredTest F ν w f) 1 (2 * Real.pi)
      (manuscriptHeckeComplexGammaShift F (χ F w) (E w).stage (E w).surj
        (formulaForward_unramified F E w) 0 v)
      (manuscriptHeckeComplexGammaShift F (χ F w)⁻¹ (T w) (hT w) (huT w) 0 v)
  have hr (v : R F) : HasSum (r v) (-realPlaceIdelicWeilTerm F f v.val v.property) :=
    idelicWeil_realComparison_hasSum F ν E T hT huT f v
  have hc (v : C F) : HasSum (c v) (-complexPlaceIdelicWeilTerm F f v.val v.property) :=
    idelicWeil_complexComparison_hasSum F ν E T hT huT f v
  have h := (hasSum_sum (s := Finset.univ) (fun v _ => hr v)).add
    (hasSum_sum (s := Finset.univ) (fun v _ => hc v))
  rw [Finset.sum_neg_distrib, Finset.sum_neg_distrib, ← neg_add, idelicWeil_archSplit F f] at h
  refine h.congr_fun fun w => ?_
  simp only [heckeCenteredArchTerm, r, c, neg_zero, mul_add, Finset.mul_sum]

variable (η : Measure (Idele F)) [η.IsHaarMeasure]
  [∀ v : Place F, MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : Place F, BorelSpace (v.adicCompletion F)ˣ]
  (μ : ∀ v : Place F, Measure (v.adicCompletion F)ˣ)
  [∀ v : Place F, (μ v).IsHaarMeasure] [∀ v : Place F, SigmaFinite (μ v)]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]
  (hν : IsWeilQuotientMeasure (principalIdeles F) η Measure.count (globalClassMeasure F ν))
  (hμ : ∀ v, μ v (finitePlaceIntegralUnits F v) =
    additiveHaarDifferent F v (v.adicCompletionIntegers F : Set (v.adicCompletion F)))

set_option maxHeartbeats 1200000 in
include hν hμ in
/-- The pointwise idelic explicit formula with multiplicities and the
normalized additive and multiplicative local finite parts. -/
theorem idelicWeil_explicitFormula_apply (f : BruhatCompactTest (IdeleClass F)) :
    (ν.real univ : ℂ)⁻¹ *
        (∑' p : CompletedHeckeZeros F E, completedHeckeZeroDistribution F ν E (-1 / 2) p f) =
      idelicWeilPolarDual F ν f - (∑ v : InfinitePlace F, infinitePlaceIdelicWeilDual F v f) -
        (∑' v : Place F, bruhatFiniteWeilTerm F μ v f) := by
  obtain ⟨A, hA, hsum⟩ := idelicWeil_characterGeometry_hasSum F ν η μ hν E f
  choose T hT huT hA using hA
  have hi := idelicWeil_archComparison_hasSum F ν E T hT huT f
  have hf := idelicWeil_finiteComparison_hasSum F μ ν hμ f
  have hg : HasSum A (-(∑' v : Place F, bruhatFiniteWeilTerm F μ v f) +
      -(∑ v : InfinitePlace F, infinitePlaceIdelicWeilDual F v f)) := by
    refine (hf.add hi).congr_fun fun w => ?_
    rw [hA w, mul_add]
  have he := hsum.unique hg
  linear_combination he

set_option maxHeartbeats 1200000 in
include hν hμ in
/-- The corrected idelic explicit formula (B.4.4.7). Both sums converge in the
strong dual to the same functional on compact Bruhat tests. -/
theorem idelicWeil_explicitFormula :
    ∃ L : StrongDual ℂ (BruhatCompactTest (IdeleClass F)),
      HasSum (fun p : (univ : Set (CompletedHeckeZeros F E)) =>
        (ν.real univ : ℂ)⁻¹ • completedHeckeZeroDistribution F ν E (-1 / 2) p.val) L ∧
      Tendsto (idelicWeilGeometricPartial F μ ν) atTop (𝓝 L) ∧
      ∀ f,
        Summable (fun p : (univ : Set (CompletedHeckeZeros F E)) =>
          ‖(ν.real univ : ℂ)⁻¹ * completedHeckeZeroDistribution F ν E (-1 / 2) p.val f‖) ∧
        (fun v : Place F => finitePlaceIdelicWeilTerm F μ f.val.val f.property
          (bruhatCompactTest_locallyConstantAtFinite F f) v).HasFiniteSupport ∧
        L f = idelicWeilPolarDual F ν f -
          (∑ v : InfinitePlace F, infinitePlaceIdelicWeilDual F v f) -
          (∑' v : Place F, finitePlaceIdelicWeilTerm F μ f.val.val f.property
            (bruhatCompactTest_locallyConstantAtFinite F f) v) := by
  obtain ⟨S, hS, hs⟩ := completedHeckeZeros_strongDual_hasSum F ν E η μ hν
    (-1 / 2) univ
  obtain ⟨G, hG, hg⟩ := idelicWeilGeometric_tendsto F μ ν
  let c : ℂ := (ν.real univ : ℂ)⁻¹
  have he : c • S = G := by
    apply UniformConvergenceCLM.ext (RingHom.id ℂ) ℂ
      (𝔖 := {s : Set (BruhatCompactTest (IdeleClass F)) | IsVonNBounded ℂ s})
    intro f
    change c * S f = G f
    rw [hs, tsum_univ (fun p => completedHeckeZeroDistribution F ν E (-1 / 2) p f), hg]
    simpa only [bruhatFiniteWeilTerm_apply] using idelicWeil_explicitFormula_apply F ν E η μ hν hμ f
  refine ⟨G, ?_, hG, fun f => ⟨?_, ?_, hg f⟩⟩
  · rw [← he]
    exact hS.const_smul c
  · have hnorm := completedHeckeZeros_mellin_summable F ν η μ hν E f (-1 / 2) univ
    refine (hnorm.mul_left ‖c‖).congr fun p => ?_
    change _ = ‖c * completedHeckeZeroDistribution F ν E (-1 / 2) p.val f‖
    rw [completedHeckeZeroDistribution_apply, norm_mul, norm_mul, Complex.norm_natCast]
  · exact (finitePlaceIdelicWeilTerm_tsum F μ hμ
      f.val.val f.property (bruhatCompactTest_locallyConstantAtFinite F f)).1

include η in
/-- The common strong-dual limit with canonical finite Tamagawa factors
and completed Hecke charts chosen from the compatible Haar data. -/
theorem idelicWeil_explicitFormula_tamagawa :
    ∃ (ν : Measure (K F)) (_ : ν.IsHaarMeasure) (E : Charts F)
      (L : StrongDual ℂ (BruhatCompactTest (IdeleClass F))),
      IsWeilQuotientMeasure (principalIdeles F) η Measure.count (globalClassMeasure F ν) ∧
      HasSum (fun p : (univ : Set (CompletedHeckeZeros F E)) =>
        (ν.real univ : ℂ)⁻¹ • completedHeckeZeroDistribution F ν E (-1 / 2) p.val) L ∧
      Tendsto (idelicWeilGeometricPartial F (finitePlaceMultiplicativeTamagawa F) ν) atTop (𝓝 L) := by
  obtain ⟨ν₀, hν₀, hweil⟩ := globalClassMeasure_exists_weil F η
  letI := hν₀
  let μ₀ := finitePlaceMultiplicativeTamagawa F
  letI (v : Place F) : LocallyCompactSpace (v.adicCompletion F) := finitePlace_locallyCompact F v
  letI (v : Place F) : LocallyCompactSpace (v.adicCompletion F)ˣ :=
    IsOpenUnits.isOpenEmbedding_unitsVal.locallyCompactSpace
  letI (v : Place F) : SecondCountableTopology (v.adicCompletion F) := finitePlace_secondCountable F v
  letI (v : Place F) : SecondCountableTopology (v.adicCompletion F)ˣ :=
    Units.isEmbedding_val₀.secondCountableTopology
  letI (v : Place F) : (μ₀ v).IsHaarMeasure := finitePlaceMultiplicativeTamagawa_isHaar F v
  letI (v : Place F) : SigmaFinite (μ₀ v) := inferInstance
  let E₀ (w : PontryaginDual (K F)) :=
    Classical.choice (completedHeckeChart_nonempty F ν₀ η μ₀ hweil w)
  have hmass (v : Place F) : μ₀ v (finitePlaceIntegralUnits F v) =
      additiveHaarDifferent F v (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
    rw [finitePlaceMultiplicativeTamagawa_units, additiveHaarDifferent_integers]
  obtain ⟨L, hs, hg, _⟩ := idelicWeil_explicitFormula F ν₀ E₀ η μ₀ hweil hmass
  exact ⟨ν₀, hν₀, E₀, L, hweil, hs, hg⟩

end
end Masullo
