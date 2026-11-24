import HomogeneousThetaPlaceLimit
import AdelicMellinCompact
import SLocalMellinDivisor

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical NumberField

namespace Masullo

noncomputable section

set_option maxHeartbeats 1800000

private theorem continuous_of_compact_restrict {V D : Type*} [TopologicalSpace V]
    [TopologicalSpace D] (f : V → C(D, ℂ))
    (h : ∀ K : Set D, IsCompact K → Continuous (fun v ↦ (f v).restrict K)) :
    Continuous f := by
  apply continuous_iff_continuousAt.mpr
  intro x
  rw [ContinuousAt, ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn]
  intro K hK
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hx := (h K hK).continuousAt (x := x)
  rw [ContinuousAt, ContinuousMap.tendsto_iff_tendstoUniformly] at hx
  exact tendstoUniformlyOn_iff_restrict.mpr hx

/-- Meromorphic functions with a prescribed lower bound on their orders,
represented by restriction to the domain off the allowed poles. -/
def boundedPoleMellinSpace (D : Set ℂ) (lowerOrder : ℂ → WithTop ℤ) :
    Submodule ℂ C(D, ℂ) where
  carrier := {f | ∃ g : ℂ → ℂ, Meromorphic g ∧ (∀ z : D, f z = g z.val) ∧
    ∀ z, lowerOrder z ≤ meromorphicOrderAt g z}
  zero_mem' := ⟨0, Meromorphic.const 0, fun _ ↦ rfl, fun z ↦ by
    rw [meromorphicOrderAt_eq_top_iff.mpr (EventuallyEq.rfl : (0 : ℂ → ℂ) =ᶠ[𝓝[≠] z] 0)]
    exact le_top⟩
  add_mem' := by
    rintro f h ⟨g, hg, hfg, hOrder⟩ ⟨j, hj, hhj, hOrder'⟩
    exact ⟨g + j, hg.add hj, fun z ↦ by change f z + h z = _; rw [hfg, hhj]; rfl,
      fun z ↦ (le_min (hOrder z) (hOrder' z)).trans (meromorphicOrderAt_add (hg z) (hj z))⟩
  smul_mem' := by
    intro a f hf
    obtain ⟨g, hg, hfg, hOrder⟩ := hf
    by_cases ha : a = 0
    · subst a
      exact ⟨0, Meromorphic.const 0, fun z ↦ by simp, fun z ↦ by
        rw [meromorphicOrderAt_eq_top_iff.mpr (EventuallyEq.rfl : (0 : ℂ → ℂ) =ᶠ[𝓝[≠] z] 0)]
        exact le_top⟩
    refine ⟨(fun _ : ℂ ↦ a) • g, hg.const_smul a, fun z ↦ by change a • f z = _; rw [hfg]; rfl, ?_⟩
    intro z
    rw [meromorphicOrderAt_smul (MeromorphicAt.const a z) (hg z),
      meromorphicOrderAt_const, ite_eq_right ha, zero_add]
    exact hOrder z

/-- On a nonempty open domain, equality of restrictions is equality of
the underlying meromorphic functions as punctured germs. -/
theorem boundedPoleMellinSpace_unique_germs {D : Set ℂ} (hD : IsOpen D) (hne : D.Nonempty)
    {g j : ℂ → ℂ} (hg : Meromorphic g) (hj : Meromorphic j) (he : EqOn g j D) :
    ∀ z : ℂ, g =ᶠ[𝓝[≠] z] j := by
  obtain ⟨p, hp⟩ := hne
  let d := g - j
  have hdp : d =ᶠ[𝓝[≠] p] 0 := by
    filter_upwards [(eventually_mem_set.mpr (hD.mem_nhds hp)).filter_mono nhdsWithin_le_nhds]
      with t ht
    exact sub_eq_zero.mpr (he ht)
  intro z
  have hdz : meromorphicOrderAt d z = ⊤ := by
    by_contra hz
    exact ((hg.sub hj).meromorphicOn (s := (univ : Set ℂ))).meromorphicOrderAt_ne_top_of_isPreconnected
      isPreconnected_univ (mem_univ z) (mem_univ p) hz
      (meromorphicOrderAt_eq_top_iff.mpr hdp)
  filter_upwards [meromorphicOrderAt_eq_top_iff.mp hdz] with t ht
  exact sub_eq_zero.mp ht

variable (F : Type*) [Field F] [NumberField F]

private abbrev G := Idele F
private abbrev KG := normOneIdeleClass F
private abbrev EG := GlobalBruhat F

local instance : MeasurableSpace (G F) := borel _
local instance : BorelSpace (G F) := ⟨rfl⟩
local instance : MeasurableSpace (KG F) := borel _
local instance : BorelSpace (KG F) := ⟨rfl⟩
local instance : MeasurableSpace (IdeleClass F) := borel _
local instance : BorelSpace (IdeleClass F) := ⟨rfl⟩

/-- Regular parameters of the fixed global character component. -/
def globalThetaMellinDomain (ω : PontryaginDual (KG F)) : Set ℂ :=
  {z | (ω, z) ∈ globalMellinRegularSet F}

/-- The continued global Mellin transform in the compact-open topology
of the regular parameters of a single character. -/
def globalContinuedMellinComponent (ν : Measure (KG F)) [ν.IsHaarMeasure]
    (ω : PontryaginDual (KG F)) :
    EG F →L[ℂ] C(globalThetaMellinDomain F ω, ℂ) := by
  let L : EG F →ₗ[ℂ] C(globalThetaMellinDomain F ω, ℂ) := {
    toFun f := ⟨fun z ↦ globalContinuedMellinEval F ν ω z.val f,
      continuous_iff_continuousAt.mpr fun z ↦ by
        have hz : ContinuousAt (fun t : ℂ ↦ globalContinuedMellinEval F ν ω t f) z.val :=
          (globalContinuedMellinEval_regular_analytic F ν f (ω, z.val) z.property).continuousAt
        exact hz.comp' (f := Subtype.val) continuous_subtype_val.continuousAt⟩
    map_add' f g := ContinuousMap.ext fun z ↦ map_add (globalContinuedMellinEval F ν ω z.val) f g
    map_smul' c f := ContinuousMap.ext fun z ↦ map_smul (globalContinuedMellinEval F ν ω z.val) c f }
  refine ⟨L, continuous_of_compact_restrict L fun K hK ↦ ?_⟩
  let j : globalThetaMellinDomain F ω → PontryaginDual (KG F) × ℂ := fun z ↦ (ω, z.val)
  have hj : Continuous j := continuous_const.prodMk continuous_subtype_val
  let D := j '' K
  have hD : IsCompact D := hK.image hj
  have hreg : D ⊆ globalMellinRegularSet F := by
    rintro _ ⟨z, -, rfl⟩
    exact z.property
  let ι : C(K, D) := ⟨fun z ↦ ⟨j z.val, mem_image_of_mem _ z.property⟩,
    (hj.comp continuous_subtype_val).subtype_mk _⟩
  exact (ContinuousMap.continuous_precomp ι).comp
    (globalContinuedMellinOnCompact F ν D hD hreg).continuous

@[simp] theorem globalContinuedMellinComponent_apply (ν : Measure (KG F)) [ν.IsHaarMeasure]
    (ω : PontryaginDual (KG F)) (f : EG F) (z : globalThetaMellinDomain F ω) :
    globalContinuedMellinComponent F ν ω f z = globalContinuedMellinEval F ν ω z.val f := rfl

private theorem globalContinuedMellinComponent_ker (μ : Measure (G F)) [μ.IsHaarMeasure]
    (ν : Measure (KG F)) [ν.IsHaarMeasure]
    (hν : IsWeilQuotientMeasure (principalIdeles F) μ Measure.count (globalClassMeasure F ν))
    (ω : PontryaginDual (KG F)) :
    (globalContinuedMellinComponent F ν ω).ker = globalIdelicZetaComponentKernel F μ ω := by
  ext f
  rw [LinearMap.mem_ker, mem_globalIdelicZetaComponentKernel F μ ν hν]
  constructor
  · intro h
    apply (adelicHomogeneousTheta_zero_iff_continuedZeta F ν f ω).mp
    apply (adelicHomogeneousTheta_zero_iff_verticalZeta F ν f ω 2 (by norm_num)).mpr
    intro y
    let z := (2 : ℂ) + (y : ℂ) * Complex.I
    have hz : z ∈ globalThetaMellinDomain F ω := by
      change ω = 1 → z ≠ 0 ∧ z ≠ 1
      intro _
      have hre : z.re = 2 := by simp [z]
      constructor <;> intro he <;> rw [he] at hre <;> norm_num at hre
    change globalContinuedMellinComponent F ν ω f = 0 at h
    have he := congrArg (fun m : C(globalThetaMellinDomain F ω, ℂ) ↦ m ⟨z, hz⟩) h
    rw [globalContinuedMellinComponent_apply, ContinuousMap.zero_apply,
      globalContinuedMellinEval_apply] at he
    exact he
  · intro h
    change globalContinuedMellinComponent F ν ω f = 0
    apply ContinuousMap.ext
    intro z
    rw [globalContinuedMellinComponent_apply, globalContinuedMellinEval_apply, ContinuousMap.zero_apply]
    exact h z.val

/-- The actual continued global Mellin transform on the character quotient. -/
def globalHomogeneousContinuedMellin (μ : Measure (G F)) [μ.IsHaarMeasure]
    (ν : Measure (KG F)) [ν.IsHaarMeasure]
    (hν : IsWeilQuotientMeasure (principalIdeles F) μ Measure.count (globalClassMeasure F ν))
    (ω : PontryaginDual (KG F)) :
    (EG F ⧸ globalIdelicZetaComponentKernel F μ ω) →L[ℂ] C(globalThetaMellinDomain F ω, ℂ) :=
  (globalIdelicZetaComponentKernel F μ ω).liftQL (globalContinuedMellinComponent F ν ω)
    (globalContinuedMellinComponent_ker F μ ν hν ω).ge

theorem globalHomogeneousContinuedMellin_injective (μ : Measure (G F)) [μ.IsHaarMeasure]
    (ν : Measure (KG F)) [ν.IsHaarMeasure]
    (hν : IsWeilQuotientMeasure (principalIdeles F) μ Measure.count (globalClassMeasure F ν))
    (ω : PontryaginDual (KG F)) :
    Injective (globalHomogeneousContinuedMellin F μ ν hν ω) := by
  apply LinearMap.ker_eq_bot.mp
  exact Submodule.ker_liftQ_eq_bot' _ _ (globalContinuedMellinComponent_ker F μ ν hν ω).symm

/-- The global meromorphic character space has at most simple poles at the
two exceptional parameters of the trivial character. -/
def globalThetaMellinPoleBound (ω : PontryaginDual (KG F)) (z : ℂ) : WithTop ℤ :=
  if ω = 1 ∧ (z = 0 ∨ z = 1) then (-1 : ℤ) else 0

private theorem globalContinuedMellinComponent_order (ν : Measure (KG F)) [ν.IsHaarMeasure]
    (ω : PontryaginDual (KG F)) (f : EG F) (z : ℂ) :
    globalThetaMellinPoleBound F ω z ≤
      meromorphicOrderAt (fun t ↦ globalContinuedMellinEval F ν ω t f) z := by
  by_cases hz : z ∈ globalThetaMellinDomain F ω
  · change ω = 1 → z ≠ 0 ∧ z ≠ 1 at hz
    have hn : ¬(ω = 1 ∧ (z = 0 ∨ z = 1)) := fun h ↦ h.2.elim (hz h.1).1 (hz h.1).2
    simpa only [globalThetaMellinPoleBound, ite_eq_right hn] using
      (globalContinuedMellinEval_regular_analytic F ν f (ω, z) hz).meromorphicOrderAt_nonneg
  change ¬ (ω = 1 → z ≠ 0 ∧ z ≠ 1) at hz
  have hw : ω = 1 := by by_contra h; exact hz (fun he ↦ (h he).elim)
  have hp : z = 0 ∨ z = 1 := by
    by_contra h
    exact hz (fun _ ↦ ⟨fun he ↦ h (Or.inl he), fun he ↦ h (Or.inr he)⟩)
  rw [globalThetaMellinPoleBound, ite_eq_left ⟨hw, hp⟩]
  simp only [globalContinuedMellinEval_apply]
  let χ := compactIdeleClassCharacter F ω
  have hχ := compactIdeleClassCharacter_unitary F ω
  obtain ⟨h₀, h₁⟩ := globalZetaContinued_pole_order F ν f χ hχ 0
  simp only [neg_zero] at h₀
  simp only [sub_zero] at h₁
  rcases hp with rfl | rfl
  · split_ifs at h₀
    · exact (WithTop.coe_le_coe.mpr (by decide : (-1 : ℤ) ≤ 0)).trans h₀.meromorphicOrderAt_nonneg
    · rw [h₀]
  · split_ifs at h₁
    · exact (WithTop.coe_le_coe.mpr (by decide : (-1 : ℤ) ≤ 0)).trans h₁.meromorphicOrderAt_nonneg
    · rw [h₁]

/-- The global homogeneous continuation with the manuscript's actual pole bound. -/
def globalHomogeneousMeromorphicMellin (μ : Measure (G F)) [μ.IsHaarMeasure]
    (ν : Measure (KG F)) [ν.IsHaarMeasure]
    (hν : IsWeilQuotientMeasure (principalIdeles F) μ Measure.count (globalClassMeasure F ν))
    (ω : PontryaginDual (KG F)) :
    (EG F ⧸ globalIdelicZetaComponentKernel F μ ω) →L[ℂ]
      boundedPoleMellinSpace (globalThetaMellinDomain F ω) (globalThetaMellinPoleBound F ω) :=
  (globalHomogeneousContinuedMellin F μ ν hν ω).codRestrict _ (fun q ↦ by
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    exact ⟨fun z ↦ globalContinuedMellinEval F ν ω z f,
      fun z ↦ by
        simp only [globalContinuedMellinEval_apply]
        exact globalZetaContinued_meromorphic F ν f _ (compactIdeleClassCharacter_unitary F ω) 0 z
          (mem_univ z),
      fun _ ↦ rfl, globalContinuedMellinComponent_order F ν ω f⟩)

theorem globalHomogeneousMeromorphicMellin_injective (μ : Measure (G F)) [μ.IsHaarMeasure]
    (ν : Measure (KG F)) [ν.IsHaarMeasure]
    (hν : IsWeilQuotientMeasure (principalIdeles F) μ Measure.count (globalClassMeasure F ν))
    (ω : PontryaginDual (KG F)) :
    Injective (globalHomogeneousMeromorphicMellin F μ ν hν ω) :=
  fun _ _ h ↦ globalHomogeneousContinuedMellin_injective F μ ν hν ω (congrArg Subtype.val h)

/-- The global transform after the product decomposition by unitary character. -/
def globalThetaMeromorphicMellin (μ : Measure (G F)) [μ.IsHaarMeasure]
    (ν : Measure (KG F)) [ν.IsHaarMeasure]
    (hν : IsWeilQuotientMeasure (principalIdeles F) μ Measure.count (globalClassMeasure F ν)) :
    GlobalThetaQuotient F →L[ℂ] (∀ ω : PontryaginDual (KG F),
      boundedPoleMellinSpace (globalThetaMellinDomain F ω) (globalThetaMellinPoleBound F ω)) :=
  ContinuousLinearMap.pi fun ω ↦ (globalHomogeneousMeromorphicMellin F μ ν hν ω).comp
    (globalThetaToComponent F μ ω)

@[simp] theorem globalThetaMeromorphicMellin_apply_mk (μ : Measure (G F)) [μ.IsHaarMeasure]
    (ν : Measure (KG F)) [ν.IsHaarMeasure]
    (hν : IsWeilQuotientMeasure (principalIdeles F) μ Measure.count (globalClassMeasure F ν))
    (f : EG F) (ω : PontryaginDual (KG F)) (z : globalThetaMellinDomain F ω) :
    (globalThetaMeromorphicMellin F μ ν hν (Submodule.Quotient.mk f) ω).val z =
      globalContinuedMellinEval F ν ω z.val f := rfl

variable (S : Finset (HeightOneSpectrum (𝓞 F)))

private abbrev KL := SLocalThetaNormOne F S
private abbrev EL := sLocalBruhatImage F S
private abbrev ArchUnits := (InfiniteAdeleRing F)ˣ

attribute [local instance] sLocalZetaUnfolding_classMeasurable sLocalZetaUnfolding_classBorel
  sLocalZetaUnfolding_idelesMeasurable

variable [∀ v : S, MeasurableSpace (v.val.adicCompletion F)ˣ]
  [∀ v : S, BorelSpace (v.val.adicCompletion F)ˣ]
  (μL : ∀ v : S, Measure (v.val.adicCompletion F)ˣ)
  [∀ v : S, (μL v).IsHaarMeasure] [∀ v : S, SigmaFinite (μL v)]

private abbrev sLocalZetaValue (ω : PontryaginDual (KL F S)) (f : EL F S) :=
  sLocalProductZetaContinued F S μL ω (sLocalRealArchParameters F S ω)
    (sLocalComplexArchParameters F S ω) f

/-- The continued S-local Mellin transform in the compact-open topology of
the complement of the Euler poles of a single character. -/
def sLocalContinuedMellinComponent (ω : PontryaginDual (KL F S)) :
    EL F S →L[ℂ] C(sLocalMellinRegularSet F S ω, ℂ) := by
  let L : EL F S →ₗ[ℂ] C(sLocalMellinRegularSet F S ω, ℂ) := {
    toFun f := ⟨fun z ↦ sLocalZetaValue F S μL ω f z.val,
      continuousOn_iff_continuous_domRestrict.mp
        (sLocalProductZetaContinued_continuousOn_regular F S μL ω f)⟩
    map_add' f g := ContinuousMap.ext fun z ↦ by
      change sLocalZetaValue F S μL ω (f + g) z.val =
        sLocalZetaValue F S μL ω f z.val + sLocalZetaValue F S μL ω g z.val
      simp only [sLocalZetaValue, sLocalProductZetaContinued, map_add]
    map_smul' c f := ContinuousMap.ext fun z ↦ by
      change sLocalZetaValue F S μL ω (c • f) z.val = c • sLocalZetaValue F S μL ω f z.val
      simp only [sLocalZetaValue, sLocalProductZetaContinued, map_smul] }
  refine ⟨L, continuous_of_compact_restrict L fun K hK ↦ ?_⟩
  let D : Set ℂ := Subtype.val '' K
  have hD : IsCompact D := hK.image continuous_subtype_val
  have hreg : D ⊆ sLocalMellinRegularSet F S ω := by
    rintro _ ⟨z, -, rfl⟩
    exact z.property
  let ι : C(K, D) := ⟨fun z ↦ ⟨z.val.val, mem_image_of_mem _ z.property⟩,
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩
  exact (ContinuousMap.continuous_precomp ι).comp
    (sLocalMellinCompact F S μL ω D hD hreg).continuous

@[simp] theorem sLocalContinuedMellinComponent_apply (ω : PontryaginDual (KL F S))
    (f : EL F S) (z : sLocalMellinRegularSet F S ω) :
    sLocalContinuedMellinComponent F S μL ω f z = sLocalZetaValue F S μL ω f z.val := rfl

variable [MeasurableSpace (ArchUnits F)] [BorelSpace (ArchUnits F)]
  (νL : Measure (KL F S)) [νL.IsHaarMeasure]

private abbrev productHaar :=
  sLocalZetaProductMeasure F S μL (archimedeanMultiplicativeHaar F)

private theorem sLocalContinuedMellinComponent_ker
    (hν : IsWeilQuotientMeasure (sUnitImage F S) (productHaar F S μL) Measure.count
      (sLocalClassHaar F S νL)) (ω : PontryaginDual (KL F S)) :
    (sLocalContinuedMellinComponent F S μL ω).ker = sLocalHomogeneousThetaKernel F S νL ω := by
  ext f
  rw [LinearMap.mem_ker]
  have htest : f ∈ sLocalHomogeneousThetaKernel F S νL ω ↔
      ∀ q, sLocalHomogeneousTheta F S νL ω f.val q = 0 := by
    simp only [sLocalHomogeneousThetaKernel, Submodule.mem_iInf, LinearMap.mem_ker]
    exact (sLocalHomogeneousTheta_zero_iff_verticalZeta F S νL ω f 1 zero_lt_one).symm
  rw [htest]
  constructor
  · intro h
    apply (sLocalHomogeneousTheta_zero_iff_verticalZeta F S νL ω f 1 zero_lt_one).mpr
    intro y
    let z := (1 : ℂ) + (y : ℂ) * Complex.I
    have hz : 0 < z.re := by simp [z]
    have hreg : z ∈ sLocalMellinRegularSet F S ω := by
      rw [sLocalMellinRegularSet_iff_noEulerPole, ← not_lt, sLocalEulerFactor_order_lt_zero_iff]
      exact sLocalEulerDenominator_ne_zero_of_pos F S ω hz
    change sLocalContinuedMellinComponent F S μL ω f = 0 at h
    have he := congrArg (fun m : C(sLocalMellinRegularSet F S ω, ℂ) ↦ m ⟨z, hreg⟩) h
    rw [sLocalContinuedMellinComponent_apply, ContinuousMap.zero_apply] at he
    exact (sLocalContinuedZeta_eq_theta F S μL νL hν ω f hz).symm.trans he
  · intro h
    have hg := (sLocalHomogeneousTheta_zero_iff_meromorphicZeta F S μL νL hν ω f).mp h
    change zeroMeromorphicGerms.mkQ
      ⟨sLocalZetaValue F S μL ω f, sLocalProductZetaContinued_meromorphic F S μL ω _ _ f⟩ = 0 at hg
    have he := (Submodule.Quotient.mk_eq_zero zeroMeromorphicGerms).mp hg
    change sLocalContinuedMellinComponent F S μL ω f = 0
    apply ContinuousMap.ext
    intro z
    rw [sLocalContinuedMellinComponent_apply, ContinuousMap.zero_apply]
    have hc := (sLocalProductZetaContinued_continuousOn_regular F S μL ω f z.val z.property)
    have hc' := hc.continuousAt ((sLocalMellinRegularSet_isOpen F S ω).mem_nhds z.property)
    exact tendsto_nhds_unique (hc'.tendsto.mono_left nhdsWithin_le_nhds)
      (tendsto_const_nhds.congr' (he z.val).symm)

/-- The actual continued S-local Mellin transform on the character quotient. -/
def sLocalHomogeneousContinuedMellin
    (hν : IsWeilQuotientMeasure (sUnitImage F S) (productHaar F S μL) Measure.count
      (sLocalClassHaar F S νL)) (ω : PontryaginDual (KL F S)) :
    SLocalHomogeneousThetaQuotient F S νL ω →L[ℂ] C(sLocalMellinRegularSet F S ω, ℂ) :=
  (sLocalHomogeneousThetaKernel F S νL ω).liftQL (sLocalContinuedMellinComponent F S μL ω)
    (sLocalContinuedMellinComponent_ker F S μL νL hν ω).ge

theorem sLocalHomogeneousContinuedMellin_injective
    (hν : IsWeilQuotientMeasure (sUnitImage F S) (productHaar F S μL) Measure.count
      (sLocalClassHaar F S νL)) (ω : PontryaginDual (KL F S)) :
    Injective (sLocalHomogeneousContinuedMellin F S μL νL hν ω) := by
  apply LinearMap.ker_eq_bot.mp
  exact Submodule.ker_liftQ_eq_bot' _ _ (sLocalContinuedMellinComponent_ker F S μL νL hν ω).symm

/-- The local homogeneous continuation takes values in the meromorphic
space with poles bounded by the actual S-local Euler divisor. -/
def sLocalHomogeneousMeromorphicMellin
    (hν : IsWeilQuotientMeasure (sUnitImage F S) (productHaar F S μL) Measure.count
      (sLocalClassHaar F S νL)) (ω : PontryaginDual (KL F S)) :
    SLocalHomogeneousThetaQuotient F S νL ω →L[ℂ]
      boundedPoleMellinSpace (sLocalMellinRegularSet F S ω)
        (fun z ↦ min (meromorphicOrderAt (sLocalEulerFactor F S ω) z) 0) :=
  (sLocalHomogeneousContinuedMellin F S μL νL hν ω).codRestrict _ (fun q ↦ by
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    exact ⟨sLocalZetaValue F S μL ω f,
      sLocalProductZetaContinued_meromorphic F S μL ω _ _ f, fun _ ↦ rfl,
      fun z ↦ (min_le_left _ _).trans (sLocalZeta_poleOrder_le_euler F S μL ω f z)⟩)

theorem sLocalHomogeneousMeromorphicMellin_injective
    (hν : IsWeilQuotientMeasure (sUnitImage F S) (productHaar F S μL) Measure.count
      (sLocalClassHaar F S νL)) (ω : PontryaginDual (KL F S)) :
    Injective (sLocalHomogeneousMeromorphicMellin F S μL νL hν ω) :=
  fun _ _ h ↦ sLocalHomogeneousContinuedMellin_injective F S μL νL hν ω (congrArg Subtype.val h)

/-- The local Mellin transform after the product decomposition by unitary character. -/
def sLocalThetaMeromorphicMellin
    (hν : IsWeilQuotientMeasure (sUnitImage F S) (productHaar F S μL) Measure.count
      (sLocalClassHaar F S νL)) :
    SLocalThetaQuotient F S →L[ℂ] (∀ ω : PontryaginDual (KL F S),
      boundedPoleMellinSpace (sLocalMellinRegularSet F S ω)
        (fun z ↦ min (meromorphicOrderAt (sLocalEulerFactor F S ω) z) 0)) :=
  ContinuousLinearMap.pi fun ω ↦ (sLocalHomogeneousMeromorphicMellin F S μL νL hν ω).comp
    (sLocalThetaToComponent F S νL ω)

@[simp] theorem sLocalThetaMeromorphicMellin_apply_mk
    (hν : IsWeilQuotientMeasure (sUnitImage F S) (productHaar F S μL) Measure.count
      (sLocalClassHaar F S νL)) (f : EL F S) (ω : PontryaginDual (KL F S))
    (z : sLocalMellinRegularSet F S ω) :
    (sLocalThetaMeromorphicMellin F S μL νL hν (Submodule.Quotient.mk f) ω).val z =
      sLocalZetaValue F S μL ω f z.val := rfl

end

end Masullo
