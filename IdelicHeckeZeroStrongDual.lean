import IdelicHeckeZeroSummability
import ThetaStrongDualCompleteness
import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn

open Bornology Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology TopologicalSpace
open scoped Classical NumberField UniformConvergence UniformConvergenceCLM

namespace Masullo

noncomputable section

/-- Continuous scalar forms on compact Bruhat tests are complete for
uniform convergence on bounded sets. -/
theorem bruhatCompactTest_strongDual_complete {G : Type*}
    [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] :
    CompleteSpace (StrongDual ℂ (BruhatCompactTest G)) := by
  obtain ⟨b, D, _, _, h⟩ := bruhatCompactTest_strict (CompactExhaustion.choice G)
  let X (n : ℕ) := (b n).Space
  letI (n : ℕ) : IsTopologicalAddGroup (X n) := (h n).choose
  letI (n : ℕ) : PolynormableSpace ℂ (X n) := (h n).choose_spec.1
  letI (n : ℕ) : MetrizableSpace (X n) := (h n).choose_spec.2.1
  letI (n : ℕ) : ContinuousSMul ℂ (X n) :=
    (PolynormableSpace.withSeminorms ℂ (X n)).continuousSMul
  letI : ContinuousSMul ℂ (BruhatCompactTest G) :=
    (PolynormableSpace.withSeminorms ℂ (BruhatCompactTest G)).continuousSMul
  exact strongDual_complete_of_sequentialSlices D.incl fun L hL => (D.continuous_limit L).mpr hL

variable (F : Type*) [Field F] [NumberField F]

private abbrev K := normOneIdeleClass F
private abbrev Place := HeightOneSpectrum (𝓞 F)

local instance : CompactSpace (K F) := normOneIdeleClass_compact F
local instance : MeasurableSpace (K F) := borel _
local instance : BorelSpace (K F) := ⟨rfl⟩
local instance : MeasurableSpace (Idele F) := borel _
local instance : BorelSpace (Idele F) := ⟨rfl⟩
local instance (v : Place F) : MeasurableSpace (v.adicCompletion F) := borel _
local instance (v : Place F) : BorelSpace (v.adicCompletion F) := ⟨rfl⟩
local instance : MeasurableSpace (IdeleClass F) := borel _
local instance : BorelSpace (IdeleClass F) := ⟨rfl⟩
local instance : LocallyCompactSpace (IdeleClass F) := ideleClasses_locallyCompact
local instance : T2Space (IdeleClass F) := ideleClasses_hausdorff
local instance : SecondCountableTopology (IdeleClass F) := ideleClass_secondCountable F

variable (ν : Measure (K F)) [ν.IsHaarMeasure]
variable (E : ∀ ω : PontryaginDual (K F), CompletedHeckeChart F ω)

private theorem mellinClassModulus_proper : IsProperMap (mellinClassModulus F) :=
  isProperMap_snd_of_compactSpace.comp (ideleClassSplitHomeomorph F).isProperMap

private theorem mellinClassModulus_surjective : Surjective (mellinClassModulus F) :=
  fun t => ⟨ideleClassExpSection F t, ideleClassLogNorm_expSection F t⟩

/-- One completed zero contributes its multiplicity times its Mellin evaluation. -/
def completedHeckeZeroDistribution (r : ℝ) (p : CompletedHeckeZeros F E) :
    StrongDual ℂ (BruhatCompactTest (IdeleClass F)) :=
  letI := globalClassMeasure_isHaar F ν
  (completedZeroMultiplicity F E p : ℂ) •
    bruhatCompactMellinCLM (globalClassMeasure F ν) (mellinClassModulus F)
      (mellinClassModulus_proper F) (mellinClassModulus_surjective F)
      (p.2.val.re + r) (completedZeroCharacter F E p)

theorem completedHeckeZeroDistribution_apply (r : ℝ) (p : CompletedHeckeZeros F E)
    (f : BruhatCompactTest (IdeleClass F)) :
    completedHeckeZeroDistribution F ν E r p f =
      (completedZeroMultiplicity F E p : ℂ) *
        (∫ g, f.val.val g * (Real.exp ((p.2.val.re + r) * (ideleClassLogNorm F g).toAdd) : ℂ) *
          (completedZeroCharacter F E p g : ℂ) ∂(globalClassMeasure F ν)) := by
  letI := globalClassMeasure_isHaar F ν
  rw [completedHeckeZeroDistribution, smul_apply, bruhatCompactMellinCLM_apply,
    smul_eq_mul]
  apply congrArg ((completedZeroMultiplicity F E p : ℂ) * ·)
  apply integral_congr_ae
  exact Eventually.of_forall fun g => by
    change (_ * f.val.val g) * _ = (f.val.val g * _) * _
    rw [mul_comm _ (f.val.val g)]
    rfl

variable (η : Measure (Idele F)) [η.IsHaarMeasure]
variable [∀ v : Place F, MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : Place F, BorelSpace (v.adicCompletion F)ˣ]
  (μ : ∀ v : Place F, Measure (v.adicCompletion F)ˣ)
  [∀ v : Place F, (μ v).IsHaarMeasure] [∀ v : Place F, SigmaFinite (μ v)]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]
variable (hν : IsWeilQuotientMeasure (principalIdeles F) η Measure.count (globalClassMeasure F ν))

set_option maxHeartbeats 950000 in
include μ hν in
/-- The completed-zero series converges unconditionally in the strong dual,
for every real twist and every subset of zeros. Its limit is the pointwise sum. -/
theorem completedHeckeZeros_strongDual_hasSum (r : ℝ) (S : Set (CompletedHeckeZeros F E)) :
    ∃ L : StrongDual ℂ (BruhatCompactTest (IdeleClass F)),
      HasSum (fun p : S => completedHeckeZeroDistribution F ν E r p.val) L ∧
      ∀ f, L f = ∑' p : S, completedHeckeZeroDistribution F ν E r p.val f := by
  let X := BruhatCompactTest (IdeleClass F)
  letI : ContinuousSMul ℂ X := (PolynormableSpace.withSeminorms ℂ X).continuousSMul
  letI : CompleteSpace (StrongDual ℂ X) := bruhatCompactTest_strongDual_complete
  let B := {V : Set X | IsVonNBounded ℂ V}
  letI : T2Space (X →ᵤ[B] ℂ) := UniformOnFun.t2Space_of_covering sUnion_isVonNBounded_eq_univ
  let j : StrongDual ℂ X → (X →ᵤ[B] ℂ) := UniformOnFun.ofFun B ∘ DFunLike.coe
  have hj : IsUniformInducing j := UniformConvergenceCLM.isUniformInducing_coeFn (RingHom.id ℂ) ℂ B
  let v (p : S) := completedHeckeZeroDistribution F ν E r p.val
  let g (f : X) := ∑' p : S, v p f
  have ht : Tendsto (fun s : Finset S => j (∑ p ∈ s, v p)) atTop (𝓝 (UniformOnFun.ofFun B g)) := by
    apply UniformOnFun.tendsto_iff_tendstoUniformlyOn.mpr
    intro V hV
    obtain ⟨u, hu, h⟩ := completedHeckeZeros_mellin_majorant F ν η μ hν E V hV r S
    have hUniform : HasSumUniformlyOn (fun p : S => (v p : X → ℂ)) g V :=
      HasSumUniformlyOn.of_norm_le_summable hu fun p f hf => by
        change ‖completedHeckeZeroDistribution F ν E r p.val f‖ ≤ u p
        rw [completedHeckeZeroDistribution_apply, norm_mul, Complex.norm_natCast]
        exact h f hf p
    refine (hasSumUniformlyOn_iff_tendstoUniformlyOn.mp hUniform).congr
      (Eventually.of_forall fun s f _ => ?_)
    change (∑ p ∈ s, v p f) = (∑ p ∈ s, v p) f
    exact (sum_apply s v f).symm
  obtain ⟨L, hL⟩ := hj.isComplete_range.isClosed.mem_of_tendsto ht
    (Eventually.of_forall fun s => mem_range_self _)
  rw [← hL] at ht
  refine ⟨L, hj.isInducing.tendsto_nhds_iff.mpr ht, fun f => ?_⟩
  exact congrArg (fun J : X →ᵤ[B] ℂ => UniformOnFun.toFun B J f) hL

end
end Masullo
