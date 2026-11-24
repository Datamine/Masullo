import AdelicThetaKernels
import SLocalThetaKernels
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd

open Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped NNReal NumberField

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

private abbrev G := Idele F
private abbrev Q := IdeleClass F
private abbrev K := normOneIdeleClass F

local instance thetaMellinQuotient_ideleMeasurable : MeasurableSpace (G F) := borel _
local instance thetaMellinQuotient_normOneMeasurable : MeasurableSpace (K F) := borel _
local instance thetaMellinQuotient_normOneBorel : BorelSpace (K F) := ⟨rfl⟩

/-- The ordinary theta operator on the actual global test space. -/
def globalThetaOperator : GlobalBruhat F →ₗ[ℂ] (Q F → ℂ) where
  toFun f := adelicTheta F (GlobalBruhat.algebraicEquiv F f).val
  map_add' f g := by
    let u := GlobalBruhat.algebraicEquiv F
    have hs (h : GlobalBruhat F) : thetaSummable F (u h).val := fun x =>
      (adelicThetaNorm_summable F (u h).property x).of_norm
    change adelicTheta F (u (f + g)).val = adelicTheta F (u f).val + adelicTheta F (u g).val
    rw [map_add, Submodule.coe_add]
    exact adelicTheta_add F (hs f) (hs g)
  map_smul' c f := by
    funext q
    obtain ⟨g, rfl⟩ := ideleClassMap_surjective F q
    let u := GlobalBruhat.algebraicEquiv F
    change thetaOnIdeles F (u (c • f)).val g = c * thetaOnIdeles F (u f).val g
    simp only [map_smul, Submodule.coe_smul_of_tower, thetaOnIdeles, thetaSummand,
      Pi.smul_apply, smul_eq_mul, tsum_mul_left]

private abbrev GlobalInitialParameter :=
  PontryaginDual (K F) × {s : ℂ // 1 < s.re}

/-- The ordinary global Mellin transform on its initial holomorphic domain,
with the topology of pointwise evaluation on that domain. -/
def globalInitialMellin (μ : Measure (G F)) [μ.IsHaarMeasure] :
    GlobalBruhat F →L[ℂ] (GlobalInitialParameter F → ℂ) :=
  ContinuousLinearMap.pi fun p => idelicZetaCLM F μ (compactIdeleClassCharacter F p.1)
    (compactIdeleClassCharacter_unitary F p.1) p.2 p.2.property

/-- The kernel of global Mellin on its initial domain is already the full
ordinary theta kernel. -/
theorem globalInitialMellin_ker (μ : Measure (G F)) [μ.IsHaarMeasure] :
    (globalInitialMellin F μ).ker = (globalThetaOperator F).ker := by
  obtain ⟨ν, hν, hW⟩ := globalClassMeasure_exists_weil F μ
  letI := hν
  ext f
  have hθ :
      (∀ ω : PontryaginDual (K F), ∀ z : ℂ,
        globalZetaContinued F ν f (compactIdeleClassCharacter F ω) 0 z = 0) ↔
        (globalThetaOperator F) f = 0 := by
    rw [funext_iff]
    exact (adelicTheta_zero_iff_continuedZeta F ν f).symm
  have he (p : GlobalInitialParameter F) :
      globalZetaContinued F ν f (compactIdeleClassCharacter F p.1) 0 p.2 =
        globalInitialMellin F μ f p := by
    rw [globalInitialMellin, ContinuousLinearMap.pi_apply, idelicZetaCLM_apply]
    exact globalZetaContinued_eq_idelic F μ ν hW f _ (compactIdeleClassCharacter_unitary F p.1)
      Complex.zero_re (fun t => by simp) _ p.2.property
  simp only [LinearMap.mem_ker]
  constructor
  · intro h
    apply hθ.mp
    intro ω
    apply globalZetaContinued_zero_of_halfPlane F ν f ω
    intro z hz
    exact (he (ω, ⟨z, hz⟩)).trans (congrFun h (ω, ⟨z, hz⟩))
  · intro h
    funext p
    exact (he p).symm.trans (hθ.mpr h p.1 p.2)

variable (S : Finset (HeightOneSpectrum (𝓞 F)))

private abbrev SK := SLocalThetaNormOne F S
private abbrev SQ := SIdeleQuotient F S
private abbrev E := sLocalBruhatImage F S
private abbrev SLocalInitialParameter :=
  PontryaginDual (SK F S) × {s : ℂ // 0 < s.re}

local instance thetaMellinQuotient_sClassMeasurable : MeasurableSpace (SQ F S) := borel _
local instance thetaMellinQuotient_sClassBorel : BorelSpace (SQ F S) := ⟨rfl⟩

private theorem sLocalNormOneHaar_regular (ν : Measure (SK F S)) [ν.IsHaarMeasure] :
    ν.Regular := by
  letI : SecondCountableTopology ((SAdeles F S)ˣ) := sLocalIdeles_secondCountable F S
  letI : T1Space (SQ F S) := QuotientGroup.t1Space_iff.mpr (sUnitImage_closed F S)
  letI : SecondCountableTopology (SQ F S) := TopologicalSpace.Quotient.secondCountableTopology
    (QuotientGroup.isOpenMap_coe (N := sUnitImage F S))
  letI : SecondCountableTopology (SK F S) := IsEmbedding.subtypeVal.secondCountableTopology
  letI : T2Space (SK F S) := inferInstance
  letI := sLocalThetaNormOne_compact F S
  exact Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure ν

/-- The S-local initial Mellin transform in the actual character charts. -/
def sLocalInitialMellin (ν : Measure (SK F S)) [ν.IsHaarMeasure] :
    E F S →L[ℂ] (SLocalInitialParameter F S → ℂ) :=
  ContinuousLinearMap.pi fun p => sLocalThetaZetaCLM F S ν p.1 p.2 p.2.property

/-- The S-local theta kernel is detected by the initial Mellin transform. -/
theorem sLocalInitialMellin_ker (ν : Measure (SK F S)) [ν.IsHaarMeasure] :
    (sLocalInitialMellin F S ν).ker = (sLocalThetaOperator F S).ker := by
  letI : T1Space (SQ F S) := QuotientGroup.t1Space_iff.mpr (sUnitImage_closed F S)
  letI : T2Space (SK F S) := inferInstance
  letI : ν.Regular := sLocalNormOneHaar_regular F S ν
  ext f
  simp only [LinearMap.mem_ker]
  constructor
  · intro h
    apply (sLocalTheta_zero_iff_verticalZeta F S ν f 1 zero_lt_one).mpr
    intro ω y
    have hz : 0 < ((1 : ℂ) + (y : ℂ) * Complex.I).re := by simp
    exact congrFun h (ω, ⟨_, hz⟩)
  · intro h
    funext p
    have hh := (sLocalTheta_zero_iff_homogeneous_zero F S ν f).mp h p.1
    change sLocalThetaZetaIntegral F S ν p.1 f p.2 = 0
    rw [(sLocalThetaZeta_integrable_eq_radial F S ν p.1 f p.2 p.2.property).2]
    simp [sLocalRadialMellin, hh]

/-- The ordinary global theta quotient with its quotient topology. -/
abbrev GlobalThetaQuotient (F : Type*) [Field F] [NumberField F] :=
  GlobalBruhat F ⧸ (globalThetaOperator F).ker

/-- The global initial Mellin transform descends to the theta quotient. -/
def globalQuotientMellin (μ : Measure (G F)) [μ.IsHaarMeasure] :
    GlobalThetaQuotient F →L[ℂ] (GlobalInitialParameter F → ℂ) :=
  Submodule.liftQL _ (globalInitialMellin F μ) (globalInitialMellin_ker F μ).ge

/-- The S-local initial Mellin transform descends to the theta quotient. -/
def sLocalQuotientMellin (ν : Measure (SK F S)) [ν.IsHaarMeasure] :
    SLocalThetaQuotient F S →L[ℂ] (SLocalInitialParameter F S → ℂ) :=
  Submodule.liftQL _ (sLocalInitialMellin F S ν) (sLocalInitialMellin_ker F S ν).ge

theorem globalQuotientMellin_injective (μ : Measure (G F)) [μ.IsHaarMeasure] :
    Injective (globalQuotientMellin F μ) :=
  LinearMap.ker_eq_bot.mp (Submodule.ker_liftQ_eq_bot' _ _ (globalInitialMellin_ker F μ).symm)

theorem sLocalQuotientMellin_injective (ν : Measure (SK F S)) [ν.IsHaarMeasure] :
    Injective (sLocalQuotientMellin F S ν) :=
  LinearMap.ker_eq_bot.mp (Submodule.ker_liftQ_eq_bot' _ _ (sLocalInitialMellin_ker F S ν).symm)

local instance thetaMellinQuotient_sIdeleMeasurable : MeasurableSpace ((SAdeles F S)ˣ) := borel _

/-- With compatible Haar measures the quotient coordinates are the original idelic integrals. -/
theorem sLocalQuotientMellin_mk_eq_idelic (μ : Measure ((SAdeles F S)ˣ)) [μ.IsHaarMeasure]
    (ν : Measure (SK F S)) [ν.IsHaarMeasure]
    (hν : IsWeilQuotientMeasure (sUnitImage F S) μ Measure.count (sLocalClassHaar F S ν))
    (f : E F S) (p : SLocalInitialParameter F S) :
    sLocalQuotientMellin F S ν (Submodule.Quotient.mk f) p =
      sLocalIdelicZetaIntegral F S μ p.1 f p.2 := by
  change sLocalThetaZetaIntegral F S ν p.1 f p.2 = _
  exact (sLocalIdelicZeta_integrable_eq_theta F S μ ν hν p.1 f p.2 p.2.property).2.symm

/-- Every continuation agreeing with the initial S-local Mellin integral is injective. -/
theorem sLocalContinuedMellin_injective_of_agrees (ν : Measure (SK F S)) [ν.IsHaarMeasure]
    (M : SLocalThetaQuotient F S → (PontryaginDual (SK F S) × ℂ → ℂ))
    (hM : ∀ q (p : SLocalInitialParameter F S), M q (p.1, p.2) = sLocalQuotientMellin F S ν q p) :
    Injective M := by
  intro q r h
  apply sLocalQuotientMellin_injective F S ν
  funext p
  rw [← hM q p, ← hM r p, h]

/-- Both ordinary theta kernels are closed. -/
theorem thetaOperator_closedKernels (μ : Measure (G F)) [μ.IsHaarMeasure]
    (ν : Measure (SK F S)) [ν.IsHaarMeasure] :
    IsClosed ((globalThetaOperator F).ker : Set (GlobalBruhat F)) ∧
      IsClosed ((sLocalThetaOperator F S).ker : Set (E F S)) := by
  rw [← globalInitialMellin_ker F μ, ← sLocalInitialMellin_ker F S ν]
  exact ⟨(globalInitialMellin F μ).isClosed_ker, (sLocalInitialMellin F S ν).isClosed_ker⟩

/-- The global homogeneous kernel is a closed linear subspace. -/
theorem globalHomogeneousTheta_closedKernel (μ : Measure (G F)) [μ.IsHaarMeasure]
    (ν : Measure (K F)) [ν.IsHaarMeasure]
    (hν : IsWeilQuotientMeasure (principalIdeles F) μ Measure.count (globalClassMeasure F ν))
    (ω : PontryaginDual (K F)) :
    ∃ P : Submodule ℂ (GlobalBruhat F), IsClosed (P : Set (GlobalBruhat F)) ∧
      ∀ f, f ∈ P ↔ ∀ q, adelicHomogeneousTheta F ν ω (GlobalBruhat.algebraicEquiv F f).val q = 0 := by
  refine ⟨globalIdelicZetaComponentKernel F μ ω, ?_, fun f =>
    (globalIdelicZetaKernels_eq_theta F μ ν hν f).2 ω⟩
  rw [globalIdelicZetaComponentKernel, Submodule.coe_iInf]
  exact isClosed_iInter fun y => (idelicZetaCLM F μ _ _ _ (by norm_num)).isClosed_ker

/-- The S-local homogeneous kernel is a closed linear subspace. -/
theorem sLocalHomogeneousTheta_closedKernel (ν : Measure (SK F S)) [ν.IsHaarMeasure]
    (ω : PontryaginDual (SK F S)) :
    ∃ P : Submodule ℂ (E F S), IsClosed (P : Set (E F S)) ∧
      ∀ f, f ∈ P ↔ ∀ q, sLocalHomogeneousTheta F S ν ω f.val q = 0 := by
  have hz (y : ℝ) : 0 < ((1 : ℂ) + (y : ℂ) * Complex.I).re := by simp
  let M := fun y : ℝ => sLocalThetaZetaCLM F S ν ω _ (hz y)
  refine ⟨⨅ y, (M y).ker, ?_, fun f => ?_⟩
  · rw [Submodule.coe_iInf]
    exact isClosed_iInter fun y => (M y).isClosed_ker
  · simp only [Submodule.mem_iInf, LinearMap.mem_ker]
    exact (sLocalHomogeneousTheta_zero_iff_verticalZeta F S ν ω f 1 zero_lt_one).symm

private theorem globalTheta_fourier_mem_ker {f : GlobalBruhat F}
    (hf : f ∈ (globalThetaOperator F).ker) :
    GlobalBruhat.fourier F f ∈ (globalThetaOperator F).ker := by
  letI : T1Space (Q F) := QuotientGroup.t1Space_iff.mpr principalIdeles_closed
  letI : T2Space (K F) := inferInstance
  letI := normOneIdeleClass_compact F
  let ν : Measure (K F) := Measure.haar
  letI : ν.IsHaarMeasure := inferInstanceAs (Measure.haar : Measure (K F)).IsHaarMeasure
  have hθ : ∀ q, adelicTheta F (GlobalBruhat.algebraicEquiv F f).val q = 0 :=
    fun q => congrFun (LinearMap.mem_ker.mp hf) q
  have hZ := (adelicTheta_zero_iff_continuedZeta F ν f).mp hθ
  apply LinearMap.mem_ker.mpr
  funext q
  apply (adelicTheta_zero_iff_continuedZeta F ν _).mpr _ q
  intro ω z
  have h := globalZetaContinued_compact_functionalEquation F ν f ω⁻¹ (1 - z)
  have hω : ω⁻¹⁻¹ = ω := inv_inv ω
  rw [hZ ω⁻¹, hω, show 1 - (1 - z) = z by ring] at h
  exact h.symm

/-- The global Fourier transform descends continuously to ordinary theta. -/
def globalThetaFourier : GlobalThetaQuotient F →L[ℂ] GlobalThetaQuotient F := by
  let P := (globalThetaOperator F).ker
  refine P.liftQL (P.mkQL.comp (GlobalBruhat.fourier F)) ?_
  intro f hf
  change (Submodule.Quotient.mk (GlobalBruhat.fourier F f) : GlobalThetaQuotient F) = 0
  exact (Submodule.Quotient.mk_eq_zero _).mpr (globalTheta_fourier_mem_ker F hf)

@[simp] theorem globalThetaFourier_mk (f : GlobalBruhat F) :
    globalThetaFourier F (Submodule.Quotient.mk f) =
      Submodule.Quotient.mk (GlobalBruhat.fourier F f) := rfl

/-- Fourier squared is the identity on the global theta quotient. -/
theorem globalThetaFourier_involutive : Involutive (globalThetaFourier F) := by
  intro q
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rw [globalThetaFourier_mk, globalThetaFourier_mk, Submodule.Quotient.eq]
  let w := GlobalBruhat.fourier F (GlobalBruhat.fourier F f)
  have he : globalThetaOperator F w = globalThetaOperator F f :=
    (adelicTheta_fourier_fourier F f).2
  change globalThetaOperator F (w - f) = 0
  rw [map_sub, he, sub_self]

/-- The global descent in Theorem 5.2.4.1(2) is a linear homeomorphism. -/
def globalThetaFourierEquiv : GlobalThetaQuotient F ≃L[ℂ] GlobalThetaQuotient F :=
  ContinuousLinearEquiv.equivOfInverse (globalThetaFourier F) (globalThetaFourier F)
    (globalThetaFourier_involutive F) (globalThetaFourier_involutive F)

theorem globalThetaFourier_unique (T : GlobalThetaQuotient F →L[ℂ] GlobalThetaQuotient F)
    (hT : ∀ f : GlobalBruhat F,
      T (Submodule.Quotient.mk f) = Submodule.Quotient.mk (GlobalBruhat.fourier F f)) :
    T = globalThetaFourier F := by
  ext q
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  exact hT f

private def upperThetaMellinLinear (ν : Measure (K F)) [ν.IsHaarMeasure]
    (χ : IdeleQuasiCharacter F) (hχ : IsUnitary F χ) (z : ℂ) :
    GlobalBruhat F →ₗ[ℂ] ℂ := by
  let D := {q : Q F | 1 ≤ ideleClassNorm F q}
  let M (f : GlobalBruhat F) (q : Q F) := globalThetaOperator F f q * (ideleNormTwist F χ z q : ℂ)
  have hI (f : GlobalBruhat F) : IntegrableOn (M f) D (globalClassMeasure F ν) :=
    (thetaZetaUpper_integrable_analytic F ν f χ hχ).1 z
  exact
    { toFun := fun f => thetaZetaUpper F ν f χ z
      map_add' := fun f g => by
        change (∫ q in D, M (f + g) q ∂globalClassMeasure F ν) =
          (∫ q in D, M f q ∂globalClassMeasure F ν) + ∫ q in D, M g q ∂globalClassMeasure F ν
        have he : M (f + g) = fun q => M f q + M g q := by
          funext q
          simp only [M, map_add, Pi.add_apply, add_mul]
        rw [he, integral_add (hI f) (hI g)]
      map_smul' := fun c f => by
        change (∫ q in D, M (c • f) q ∂globalClassMeasure F ν) =
          c • ∫ q in D, M f q ∂globalClassMeasure F ν
        have he : M (c • f) = fun q => c • M f q := by
          funext q
          simp only [M, map_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]
        rw [he, integral_smul] }

/-- Evaluation of the continued zeta transform is linear in the test,
also with Lean's total convention at the possible pole coordinates. -/
def globalContinuedMellinEval (ν : Measure (K F)) [ν.IsHaarMeasure]
    (ω : PontryaginDual (K F)) (z : ℂ) : GlobalBruhat F →ₗ[ℂ] ℂ :=
  let χ := compactIdeleClassCharacter F ω
  let a := ∫ k : K F, (χ k.val : ℂ) ∂ν
  let Fourier := (GlobalBruhat.fourier F).toLinearMap
  (upperThetaMellinLinear F ν χ (compactIdeleClassCharacter_unitary F ω) z) +
    (upperThetaMellinLinear F ν (compactIdeleClassCharacter F ω⁻¹)
      (compactIdeleClassCharacter_unitary F ω⁻¹) (1 - z)).comp Fourier +
    (a / (z - 1)) • (GlobalBruhat.evaluation F 0).comp Fourier -
    (a / z) • GlobalBruhat.evaluation F 0

@[simp] theorem globalContinuedMellinEval_apply (ν : Measure (K F)) [ν.IsHaarMeasure]
    (ω : PontryaginDual (K F)) (z : ℂ) (f : GlobalBruhat F) :
    globalContinuedMellinEval F ν ω z f =
      globalZetaContinued F ν f (compactIdeleClassCharacter F ω) 0 z := by
  let χ := compactIdeleClassCharacter F ω
  let a := ∫ k : K F, (χ k.val : ℂ) ∂ν
  let v := (GlobalBruhat.algebraicEquiv F (GlobalBruhat.fourier F f)).val 0
  let u := (GlobalBruhat.algebraicEquiv F f).val 0
  change thetaZetaUpper F ν f χ z +
      thetaZetaUpper F ν (GlobalBruhat.fourier F f) (compactIdeleClassCharacter F ω⁻¹) (1 - z) +
      (a / (z - 1)) * v - (a / z) * u =
    thetaZetaUpper F ν f χ z + thetaZetaUpper F ν (GlobalBruhat.fourier F f) χ⁻¹ (1 - z) +
      a * v / (z + 0 - 1) - a * u / (z + 0)
  rw [compactIdeleClassCharacter_inv]
  simp only [add_zero, div_eq_mul_inv, χ]
  ring

/-- The continued transform on the global theta quotient is the full
character-component operator. Its kernel is zero. -/
def globalQuotientContinuedMellin (ν : Measure (K F)) [ν.IsHaarMeasure] :
    GlobalThetaQuotient F →ₗ[ℂ] ((PontryaginDual (K F) × ℂ) → ℂ) := by
  let Z := LinearMap.pi (fun p : PontryaginDual (K F) × ℂ => globalContinuedMellinEval F ν p.1 p.2)
  refine Submodule.liftQ _ Z fun f hf => ?_
  apply LinearMap.mem_ker.mpr
  funext p
  have h := (adelicTheta_zero_iff_continuedZeta F ν f).mp
    (fun q => congrFun (LinearMap.mem_ker.mp hf) q)
  exact (globalContinuedMellinEval_apply F ν p.1 p.2 f).trans (h p.1 p.2)

theorem globalQuotientContinuedMellin_injective (ν : Measure (K F)) [ν.IsHaarMeasure] :
    Injective (globalQuotientContinuedMellin F ν) := by
  apply LinearMap.ker_eq_bot.mp
  apply Submodule.ker_liftQ_eq_bot
  intro f hf
  apply LinearMap.mem_ker.mpr
  funext q
  apply (adelicTheta_zero_iff_continuedZeta F ν f).mpr _ q
  intro ω z
  have h := congrFun (LinearMap.mem_ker.mp hf) (ω, z)
  exact (globalContinuedMellinEval_apply F ν ω z f).symm.trans h

/-- On a compact subset disjoint from the possible poles, the continued
zeta transform is bounded by a continuous seminorm of the test. -/
theorem globalContinuedMellin_seminorm_bound (ν : Measure (K F)) [ν.IsHaarMeasure]
    (ω : PontryaginDual (K F)) {T : Set ℂ} (hT : IsCompact T)
    (h₀ : ∀ z ∈ T, z ≠ 0) (h₁ : ∀ z ∈ T, z ≠ 1) :
    ∃ p : Seminorm ℂ (GlobalBruhat F), Continuous p ∧
      ∀ f : GlobalBruhat F, ∀ z ∈ T, ‖globalZetaContinued F ν f
        (compactIdeleClassCharacter F ω) 0 z‖ ≤ p f := by
  let χ := compactIdeleClassCharacter F ω
  let χ' := compactIdeleClassCharacter F ω⁻¹
  let a := ∫ k : K F, (χ k.val : ℂ) ∂ν
  let Fourier := GlobalBruhat.fourier F
  obtain ⟨B, hB⟩ := hT.exists_bound_of_continuousOn Complex.continuous_re.continuousOn
  obtain ⟨p, hp, hP⟩ := thetaZetaUpper_seminorm_bound F ν χ
    (compactIdeleClassCharacter_unitary F ω) B
  obtain ⟨r, hr, hR⟩ := thetaZetaUpper_seminorm_bound F ν χ'
    (compactIdeleClassCharacter_unitary F ω⁻¹) (1 + B)
  have hr₀ : ContinuousOn (fun z : ℂ => a / z) T :=
    continuousOn_const.div continuousOn_id h₀
  have hr₁ : ContinuousOn (fun z : ℂ => a / (z - 1)) T :=
    continuousOn_const.div (continuousOn_id.sub continuousOn_const) (fun z hz => sub_ne_zero.mpr (h₁ z hz))
  obtain ⟨A₀, hA₀⟩ := hT.exists_bound_of_continuousOn hr₀
  obtain ⟨A₁, hA₁⟩ := hT.exists_bound_of_continuousOn hr₁
  let C₀ : ℝ≥0 := ⟨max A₀ 0, le_max_right ..⟩
  let C₁ : ℝ≥0 := ⟨max A₁ 0, le_max_right ..⟩
  let e := (normSeminorm ℂ ℂ).comp (GlobalBruhat.evaluation F 0)
  have he : Continuous e := continuous_norm.comp (GlobalBruhat.evaluation_continuous F 0)
  let P : Seminorm ℂ (GlobalBruhat F) :=
    (p + r.comp Fourier.toLinearMap + C₁ • e.comp Fourier.toLinearMap) + C₀ • e
  have hPC : Continuous P :=
    ((hp.add (hr.comp Fourier.continuous)).add
      (continuous_const.mul (he.comp Fourier.continuous))).add (continuous_const.mul he)
  refine ⟨P, hPC, fun f z hz => ?_⟩
  have hb₀ : z.re ≤ B := (le_abs_self _).trans (hB z hz)
  have hb₁ : (1 - z).re ≤ 1 + B := by
    rw [Complex.sub_re, Complex.one_re, sub_eq_add_neg]
    exact add_le_add_right ((neg_le_abs _).trans (hB z hz)) _
  have hc₀ : ‖a / z‖ ≤ C₀ := (hA₀ z hz).trans (le_max_left _ _)
  have hc₁ : ‖a / (z - 1)‖ ≤ C₁ := (hA₁ z hz).trans (le_max_left _ _)
  let Z₀ := upperThetaMellinLinear F ν χ (compactIdeleClassCharacter_unitary F ω) z f
  let Z₁ := upperThetaMellinLinear F ν χ' (compactIdeleClassCharacter_unitary F ω⁻¹)
    (1 - z) (Fourier f)
  let u := GlobalBruhat.evaluation F 0 f
  let v := GlobalBruhat.evaluation F 0 (Fourier f)
  rw [← globalContinuedMellinEval_apply]
  change ‖Z₀ + Z₁ + (a / (z - 1)) * v - (a / z) * u‖ ≤
    p f + r (Fourier f) + C₁ * ‖v‖ + C₀ * ‖u‖
  have hZ₀ : ‖Z₀‖ ≤ p f := hP f z hb₀
  have hZ₁ : ‖Z₁‖ ≤ r (Fourier f) := hR (Fourier f) (1 - z) hb₁
  have hZ₂ : ‖(a / (z - 1)) * v‖ ≤ C₁ * ‖v‖ := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right hc₁ (norm_nonneg _)
  have hZ₃ : ‖(a / z) * u‖ ≤ C₀ * ‖u‖ := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right hc₀ (norm_nonneg _)
  exact (norm_sub_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add hZ₀ hZ₁)) hZ₂)) hZ₃)

end

end Masullo
