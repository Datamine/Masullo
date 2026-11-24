import IdelicWeilInfinite
import IdelicCutoffKernel
import FrechetFactorization
import SchwartzComplete

open Function MeasureTheory NumberField Set Topology
open scoped Classical ContDiff NumberField SchwartzMap

namespace Masullo

noncomputable section

private theorem frechet_schwartz_continuous_of_evaluations {X K : Type*}
    [AddCommGroup X] [Module ℂ X] [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup K] [NormedSpace ℝ K] (hX : IsFrechetTVS X)
    (L : X →ₗ[ℂ] 𝓢(K, ℂ))
    (hL : ∀ x, Continuous (fun u => L u x)) : Continuous L := by
  obtain ⟨ha, hp, hm, hc⟩ := hX
  letI : IsTopologicalAddGroup X := ha
  letI : UniformSpace X := IsTopologicalAddGroup.rightUniformSpace X
  letI : IsUniformAddGroup X := isUniformAddGroup_of_addCommGroup
  letI : CompleteSpace X := hc
  letI : TopologicalSpace.MetrizableSpace X := hm
  letI : PolynormableSpace ℂ X := hp
  letI : ContinuousSMul ℂ X := (PolynormableSpace.withSeminorms ℂ X).continuousSMul
  letI : CompleteSpace 𝓢(K, ℂ) := completeSpace_schwartzMap
  letI : FirstCountableTopology 𝓢(K, ℂ) := (schwartz_withSeminorms ℂ K ℂ).firstCountableTopology
  apply frechet_continuous_of_closed_graph L
  let E (x : K) : Set (X × 𝓢(K, ℂ)) := {z | z.2 x = L z.1 x}
  have he : (L.graph : Set (X × 𝓢(K, ℂ))) = ⋂ x, E x := by
    ext z
    change z.2 = L z.1 ↔ z ∈ ⋂ x, E x
    rw [mem_iInter]
    exact ⟨fun h x => congrArg (fun w : 𝓢(K, ℂ) => w x) h, SchwartzMap.ext⟩
  rw [he]
  refine isClosed_iInter fun x => isClosed_eq (?_ : Continuous (fun z : X × 𝓢(K, ℂ) => z.2 x))
    ((hL x).comp continuous_fst)
  exact ((BoundedContinuousFunction.lipschitz_eval_const x).continuous.comp
    (SchwartzMap.toBoundedContinuousFunctionCLM ℂ K ℂ).continuous).comp continuous_snd

variable (F : Type*) [Field F] [NumberField F]

local instance : LocallyCompactSpace (IdeleClass F) := ideleClasses_locallyCompact
local instance : T2Space (IdeleClass F) := ideleClasses_hausdorff
local instance : SecondCountableTopology (IdeleClass F) := ideleClass_secondCountable F

private theorem bruhatCompactTest_schwartz_functional_continuous {K : Type*}
    [NormedAddCommGroup K] [NormedSpace ℝ K]
    (T : BruhatCompactTest (IdeleClass F) →ₗ[ℂ] 𝓢(K, ℂ))
    (hT : ∀ x, Continuous (fun u => T u x)) (J : 𝓢(K, ℂ) →L[ℂ] ℂ) :
    Continuous (J.toLinearMap.comp T) := by
  letI : T2Space (BruhatCompactTest (IdeleClass F)) := bruhatCompactTest_t2
  obtain ⟨b, D, _, hEmb, hFr⟩ := bruhatCompactTest_strict (CompactExhaustion.choice (IdeleClass F))
  apply (D.continuous_limit (J.toLinearMap.comp T)).mpr
  intro n
  letI : T2Space (b n).Space := (hEmb n).t2Space
  let L := T.comp (D.incl n).toLinearMap
  exact J.continuous.comp (frechet_schwartz_continuous_of_evaluations (hFr n) L
    (fun x => (hT x).comp (D.incl n).continuous))

variable {K : Type*} [RCLike K]

/-- The shifted and weighted local test depends linearly on the idelic test. -/
def idelicArchWeilShiftedLinear (n : ℕ) (i : Kˣ →ₜ* IdeleClass F)
    (hc : ∀ f : BruhatCompactTest (IdeleClass F), HasCompactSupport (f.val.val ∘ i))
    (hs : ∀ f : BruhatCompactTest (IdeleClass F),
      ContDiffOn ℝ ∞ (archWeilZeroExtension (f.val.val ∘ i)) ({0} : Set K)ᶜ) :
    BruhatCompactTest (IdeleClass F) →ₗ[ℂ] 𝓢(K, ℂ) where
  toFun f := archWeilShiftedTest n (f.val.val ∘ i) (hc f) (hs f)
  map_add' f g := by
    apply SchwartzMap.ext
    intro x
    simp only [add_apply, archWeilShiftedTest_apply, archWeilZeroExtension]
    split
    · simp
    · change _ • (f.val.val _ + g.val.val _) = _
      exact smul_add _ _ _
  map_smul' c f := by
    apply SchwartzMap.ext
    intro x
    simp only [smul_apply, archWeilShiftedTest_apply, archWeilZeroExtension, RingHom.id_apply]
    split
    · simp
    · change _ • (c • f.val.val _) = c • (_ • f.val.val _)
      exact smul_comm _ _ _

private theorem idelicArchWeilShiftedLinear_eval_continuous (n : ℕ) (i : Kˣ →ₜ* IdeleClass F)
    (hc : ∀ f : BruhatCompactTest (IdeleClass F), HasCompactSupport (f.val.val ∘ i))
    (hs : ∀ f : BruhatCompactTest (IdeleClass F),
      ContDiffOn ℝ ∞ (archWeilZeroExtension (f.val.val ∘ i)) ({0} : Set K)ᶜ) (x : K) :
    Continuous (fun f => idelicArchWeilShiftedLinear F n i hc hs f x) := by
  by_cases hx : 1 - x = 0
  · simp only [idelicArchWeilShiftedLinear, LinearMap.coe_mk, AddHom.coe_mk,
      archWeilShiftedTest_apply, archWeilZeroExtension, hx, dite_eq_left, smul_zero]
    exact continuous_const
  · let g := i (Units.mk0 (1 - x) hx)
    have he : Continuous (fun f : BruhatCompactTest (IdeleClass F) => f.val.val g) :=
      (bruhatSchwartz_continuous_eval g).comp bruhatCompactTest_toSchwartz.continuous
    refine (he.const_smul (‖1 - x‖ ^ (-(n : ℝ) / 2))).congr (fun f => ?_)
    change ‖1 - x‖ ^ (-(n : ℝ) / 2) • f.val.val g =
      archWeilShiftedTest n (f.val.val ∘ i) (hc f) (hs f) x
    rw [archWeilShiftedTest_apply, archWeilZeroExtension, dite_eq_right hx]
    rfl

private def idelicArchWeilDual (n : ℕ) (i : Kˣ →ₜ* IdeleClass F)
    (hc : ∀ f : BruhatCompactTest (IdeleClass F), HasCompactSupport (f.val.val ∘ i))
    (hs : ∀ f : BruhatCompactTest (IdeleClass F),
      ContDiffOn ℝ ∞ (archWeilZeroExtension (f.val.val ∘ i)) ({0} : Set K)ᶜ)
    (J : 𝓢(K, ℂ) →L[ℂ] ℂ) : StrongDual ℂ (BruhatCompactTest (IdeleClass F)) :=
  ⟨J.toLinearMap.comp (idelicArchWeilShiftedLinear F n i hc hs),
    bruhatCompactTest_schwartz_functional_continuous F _
      (idelicArchWeilShiftedLinear_eval_continuous F n i hc hs) J⟩

/-- The normalized real-place geometric term as a continuous linear functional. -/
def realPlaceIdelicWeilDual (v : InfinitePlace F) (hv : v.IsReal) :
    StrongDual ℂ (BruhatCompactTest (IdeleClass F)) :=
  idelicArchWeilDual F 1 (realPlaceWeilInsertion F v hv)
    (fun f => realPlaceWeilTest_hasCompactSupport F f v hv)
    (fun f => realPlaceWeilTest_smooth F f v hv) (-realLogFourierDistribution)

@[simp] theorem realPlaceIdelicWeilDual_apply (v : InfinitePlace F) (hv : v.IsReal)
    (f : BruhatCompactTest (IdeleClass F)) :
    realPlaceIdelicWeilDual F v hv f = realPlaceIdelicWeilTerm F f v hv := rfl

/-- The normalized complex-place geometric term as a continuous linear functional. -/
def complexPlaceIdelicWeilDual (v : InfinitePlace F) (hv : v.IsComplex) :
    StrongDual ℂ (BruhatCompactTest (IdeleClass F)) :=
  idelicArchWeilDual F 2 (complexPlaceWeilInsertion F v hv)
    (fun f => complexPlaceWeilTest_hasCompactSupport F f v hv)
    (fun f => complexPlaceWeilTest_smooth F f v hv) (-complexTraceLogFourierDistribution)

@[simp] theorem complexPlaceIdelicWeilDual_apply (v : InfinitePlace F) (hv : v.IsComplex)
    (f : BruhatCompactTest (IdeleClass F)) :
    complexPlaceIdelicWeilDual F v hv f = complexPlaceIdelicWeilTerm F f v hv := rfl

/-- The normalized local term at an arbitrary infinite place. -/
def infinitePlaceIdelicWeilDual (v : InfinitePlace F) :
    StrongDual ℂ (BruhatCompactTest (IdeleClass F)) :=
  if hv : v.IsReal then realPlaceIdelicWeilDual F v hv
  else complexPlaceIdelicWeilDual F v (InfinitePlace.not_isReal_iff_isComplex.mp hv)

theorem infinitePlaceIdelicWeilDual_apply_real (v : InfinitePlace F) (hv : v.IsReal)
    (f : BruhatCompactTest (IdeleClass F)) :
    infinitePlaceIdelicWeilDual F v f = realPlaceIdelicWeilTerm F f v hv := by
  simp only [infinitePlaceIdelicWeilDual, dite_eq_left hv, realPlaceIdelicWeilDual_apply]

theorem infinitePlaceIdelicWeilDual_apply_complex (v : InfinitePlace F) (hv : v.IsComplex)
    (f : BruhatCompactTest (IdeleClass F)) :
    infinitePlaceIdelicWeilDual F v f = complexPlaceIdelicWeilTerm F f v hv := by
  simp only [infinitePlaceIdelicWeilDual, dite_eq_right (InfinitePlace.not_isReal_iff_isComplex.mpr hv),
    complexPlaceIdelicWeilDual_apply]

/-- The finite sum of the normalized infinite-place geometric terms. -/
def infinitePlaceIdelicWeilSum : StrongDual ℂ (BruhatCompactTest (IdeleClass F)) :=
  ∑ v : InfinitePlace F, infinitePlaceIdelicWeilDual F v

theorem infinitePlaceIdelicWeilSum_apply (f : BruhatCompactTest (IdeleClass F)) :
    infinitePlaceIdelicWeilSum F f = ∑ v : InfinitePlace F, infinitePlaceIdelicWeilDual F v f :=
  sum_apply _ _ _

local instance : MeasurableSpace (normOneIdeleClass F) := borel _
local instance : BorelSpace (normOneIdeleClass F) := ⟨rfl⟩
local instance : MeasurableSpace (IdeleClass F) := borel _
local instance : BorelSpace (IdeleClass F) := ⟨rfl⟩

/-- The two global pole terms, with the reciprocal mass of the norm-one classes. -/
def idelicWeilPolarDual (ν : Measure (normOneIdeleClass F)) [ν.IsHaarMeasure] :
    StrongDual ℂ (BruhatCompactTest (IdeleClass F)) :=
  letI : CompactSpace (normOneIdeleClass F) := normOneIdeleClass_compact F
  letI := globalClassMeasure_isHaar F ν
  let m := mellinClassModulus F
  let hm : IsProperMap m :=
    isProperMap_snd_of_compactSpace.comp (ideleClassSplitHomeomorph F).isProperMap
  let hs : Surjective m := fun t => ⟨ideleClassExpSection F t, ideleClassLogNorm_expSection F t⟩
  ((ν.real univ : ℂ)⁻¹) •
    (bruhatCompactMellinCLM (globalClassMeasure F ν) m hm hs (-1 / 2) 1 +
      bruhatCompactMellinCLM (globalClassMeasure F ν) m hm hs (1 / 2) 1)

theorem idelicWeilPolarDual_apply (ν : Measure (normOneIdeleClass F)) [ν.IsHaarMeasure]
    (f : BruhatCompactTest (IdeleClass F)) :
    idelicWeilPolarDual F ν f = (ν.real univ : ℂ)⁻¹ *
      ((∫ g, (Real.exp ((-1 / 2 : ℝ) * (ideleClassLogNorm F g).toAdd) : ℂ) *
        f.val.val g ∂globalClassMeasure F ν) +
       (∫ g, (Real.exp ((1 / 2 : ℝ) * (ideleClassLogNorm F g).toAdd) : ℂ) *
        f.val.val g ∂globalClassMeasure F ν)) := by
  change (ν.real univ : ℂ)⁻¹ *
      (modulatedMellinIntegral (globalClassMeasure F ν) (mellinClassModulus F) f.val.val (-1 / 2) 1 +
        modulatedMellinIntegral (globalClassMeasure F ν) (mellinClassModulus F) f.val.val (1 / 2) 1) = _
  have he (a : ℝ) :
      modulatedMellinIntegral (globalClassMeasure F ν) (mellinClassModulus F) f.val.val a 1 =
        ∫ g, (Real.exp (a * (ideleClassLogNorm F g).toAdd) : ℂ) * f.val.val g
          ∂globalClassMeasure F ν := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun g => by
      change ((Real.exp (a * (ideleClassLogNorm F g).toAdd) : ℂ) * f.val.val g) * (1 : ℂ) = _
      exact mul_one _
  rw [he, he]

end
end Masullo
