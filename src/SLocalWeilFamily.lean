import GlobalThetaWeilEigen
import SLocalTateProduct

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical NumberField SchwartzMap

namespace Masullo

noncomputable section

universe u

variable (F : Type u) [Field F] [NumberField F]

private abbrev Place := HeightOneSpectrum (𝓞 F)
private abbrev L (v : Place F) := v.adicCompletion F
private abbrev R := {v : InfinitePlace F // v.IsReal}
private abbrev C := {v : InfinitePlace F // v.IsComplex}
private abbrev Arch := 𝓢(mixedEmbedding.mixedSpace F, ℂ)
private abbrev E (S : Finset (Place F)) := sLocalBruhatImage F S
private abbrev Test (S : Finset (Place F)) := locallyConstantTests (∀ w : S, L F w.val)
private abbrev Characters (S : Finset (Place F)) := PontryaginDual (SLocalThetaNormOne F S)

local instance (v : Place F) : MeasurableSpace (L F v) := borel _
local instance (v : Place F) : BorelSpace (L F v) := ⟨rfl⟩
local instance (v : Place F) : MeasurableSpace (L F v)ˣ := borel _
local instance (v : Place F) : BorelSpace (L F v)ˣ := ⟨rfl⟩
local instance : MeasurableSpace (InfiniteAdeleRing F)ˣ := borel _
local instance : BorelSpace (InfiniteAdeleRing F)ˣ := ⟨rfl⟩
local instance (v : Place F) : LocallyCompactSpace (L F v) := finitePlace_locallyCompact F v
local instance (v : Place F) : SecondCountableTopology (L F v) := finitePlace_secondCountable F v
local instance (v : Place F) : LocallyCompactSpace (L F v)ˣ :=
  IsOpenUnits.isOpenEmbedding_unitsVal.locallyCompactSpace
local instance (v : Place F) : SecondCountableTopology (L F v)ˣ :=
  Units.isEmbedding_val₀.secondCountableTopology
private abbrev μ (v : Place F) := finitePlaceMultiplicativeTamagawa F v
local instance (v : Place F) : (μ F v).IsHaarMeasure := finitePlaceMultiplicativeTamagawa_isHaar F v
local instance (v : Place F) : SigmaFinite (μ F v) := inferInstance

variable (S : Finset (Place F)) (ω : Characters F S)

local instance : TopologicalSpace (Test F S) := finestLocallyConvexTopology _
local instance : ContinuousSMul ℂ (E F S) :=
  (PolynormableSpace.withSeminorms ℂ (E F S)).continuousSMul
local instance : MeasurableSpace (SAdeles F S)ˣ := borel _
local instance : BorelSpace (SAdeles F S)ˣ := ⟨rfl⟩
local instance : MeasurableSpace (SIdeleQuotient F S) := borel _
local instance : BorelSpace (SIdeleQuotient F S) := ⟨rfl⟩
local instance : MeasurableSpace (SLocalThetaNormOne F S) := borel _
local instance : BorelSpace (SLocalThetaNormOne F S) := ⟨rfl⟩

private abbrev a := sLocalRealArchParameters F S ω
private abbrev j := sLocalComplexArchParameters F S ω
private abbrev χ := sLocalFiniteZetaPhases F S ω
private abbrev N := sLocalEulerNormalizedMellin F S (fun v => μ F v.val) ω
private abbrev P := sLocalFiniteZetaCleared F S (fun v => μ F v.val) (χ F S ω)

private def archGerm (c : ℂ) :=
  (archimedeanNumberFieldZeta_denominator_analyticOperatorGerm F (a F S ω) (j F S ω) c).choose

private theorem archGerm_eq (c : ℂ) :
    (fun z => archimedeanNumberFieldZetaDenominator F (a F S ω) (j F S ω) z •
      archimedeanNumberFieldZeta F complexTamagawaAngularMeasure (a F S ω) (j F S ω) z)
      =ᶠ[𝓝[≠] c] archGerm F S ω c :=
  (archimedeanNumberFieldZeta_denominator_analyticOperatorGerm F (a F S ω) (j F S ω) c).choose_spec.1

private theorem archGerm_continuousAt (c : ℂ) (φ : Arch F) :
    ContinuousAt (fun z => archGerm F S ω c z φ) c := by
  have h := (archimedeanNumberFieldZeta_denominator_analyticOperatorGerm F (a F S ω) (j F S ω) c).choose_spec.2
  obtain ⟨D, hD⟩ := mem_of_mem_nhds h
  exact (hD.hasDerivAt φ).continuousAt

private theorem localEulerEventual (c : ℂ) :
    ∀ᶠ z in 𝓝[≠] c, sLocalFiniteZetaDenominator F S (χ F S ω) z ≠ 0 := by
  let D := sLocalFiniteZetaDenominator F S (χ F S ω)
  have hA : AnalyticOnNhd ℂ D univ := sLocalFiniteZetaDenominator_analytic F S (χ F S ω)
  have hn : D 1 ≠ 0 := sLocalFiniteZetaDenominator_ne_zero_of_pos F S _ 1 (by norm_num)
  rcases (hA c trivial).eventually_eq_zero_or_eventually_ne_zero with he | he
  · exact (hn (hA.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
      (mem_univ c) he (mem_univ 1))).elim
  · exact he

/-- The reciprocal Euler product times the actual local zeta family, with
the exceptional values represented by continuous linear functionals. -/
def sLocalEulerClearedWeil (c : ℂ) : StrongDual ℂ (E F S) :=
  (archGerm F S ω c c).comp (sLocalBruhatContractFinite F S (P F S ω c).toLinearMap)

theorem sLocalEulerClearedWeil_apply (c : ℂ) (f : E F S) :
    sLocalEulerClearedWeil F S ω c f = N F S ω f c := by
  let G (z : ℂ) : StrongDual ℂ (E F S) :=
    (archGerm F S ω c z).comp (sLocalBruhatContractFinite F S (P F S ω z).toLinearMap)
  have hf : f ∈ Submodule.span ℂ {g : E F S |
      ∃ (φ : Arch F) (ψ : Test F S), sLocalBruhatPure F S φ ψ = g} := by
    rw [sLocalBruhatPure_span]
    trivial
  have hc : ContinuousAt (fun z => G z f) c := by
    induction hf using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨φ, ψ, rfl⟩ := hg
      have he (z : ℂ) : G z (sLocalBruhatPure F S φ ψ) =
          P F S ω z ψ * archGerm F S ω c z φ := by
        simp [G, sLocalBruhatContractFinite_pure, smul_eq_mul]
      simp_rw [he]
      exact ((sLocalFiniteZetaCleared_analytic F S (fun v => μ F v.val) (χ F S ω) ψ c
        trivial).continuousAt).mul (archGerm_continuousAt F S ω c φ)
    | zero =>
      simp only [map_zero]
      exact continuousAt_const
    | add x y _ _ hx hy =>
      simp_rw [map_add]
      exact hx.add hy
    | smul b x _ hx =>
      simp_rw [map_smul, smul_eq_mul]
      exact continuousAt_const.mul hx
  have heq : (fun z => G z f) =ᶠ[𝓝[≠] c] N F S ω f := by
    filter_upwards [archGerm_eq F S ω c, localEulerEventual F S ω c,
      sLocalEulerNormalizedMellin_eq_germ F S (fun v => μ F v.val) ω f c] with z hz hn hN
    change N F S ω f z = sLocalEulerDenominator F S ω z * sLocalContinuedMellinEval F S
      (fun v => μ F v.val) ω z f at hN
    rw [hN]
    have hh : G z = sLocalEulerDenominator F S ω z • sLocalContinuedMellinEval F S
        (fun v => μ F v.val) ω z := by
      apply ContinuousLinearMap.ext
      intro x
      have hx : x ∈ Submodule.span ℂ {g : E F S |
          ∃ (φ : Arch F) (ψ : Test F S), sLocalBruhatPure F S φ ψ = g} := by
        rw [sLocalBruhatPure_span]
        trivial
      induction hx using Submodule.span_induction with
      | mem g hg =>
        obtain ⟨φ, ψ, rfl⟩ := hg
        change archGerm F S ω c z (sLocalBruhatContractFinite F S (P F S ω z).toLinearMap
          (sLocalBruhatPure F S φ ψ)) = _
        unfold sLocalContinuedMellinEval sLocalFiniteZetaSchwartzTest
        simp only [sLocalBruhatContractFinite_pure, map_smul, smul_eq_mul]
        rw [← hz]
        unfold sLocalEulerDenominator sLocalFiniteZetaContinued
        simp only [ContinuousLinearMap.comp_apply, sLocalBruhatContractFinite_pure, map_smul,
          smul_apply, smul_eq_mul, ContinuousLinearMap.toLinearMap_smul, LinearMap.smul_apply]
        field_simp [hn]
      | zero => simp
      | add x y _ _ hx hy => rw [map_add, map_add, hx, hy]
      | smul b x _ hx => rw [map_smul, map_smul, hx]
    exact DFunLike.congr_fun hh f
  have hlim : Tendsto (N F S ω f) (𝓝 c) (𝓝 (N F S ω f c)) :=
    (sLocalEulerNormalizedMellin_entire F S (fun v => μ F v.val) ω f c trivial).continuousAt
  exact tendsto_nhds_unique (hc.tendsto.mono_left nhdsWithin_le_nhds)
    ((hlim.mono_left nhdsWithin_le_nhds).congr' heq.symm)

/-- The cleared local zeta operator is entire for the strong topology on the actual S-local dual. -/
theorem sLocalEulerClearedWeil_holomorphic :
    Differentiable ℂ (sLocalEulerClearedWeil F S ω) := by
  let D := StrongDual ℂ (E F S)
  letI : IsTopologicalAddGroup D := ContinuousLinearMap.topologicalAddGroup
    (E := E F S) (F := ℂ) (σ := RingHom.id ℂ)
  letI : TopologicalSpace (StrongDual ℂ D) := ContinuousLinearMap.topologicalSpace
    (E := D) (F := ℂ) (σ := RingHom.id ℂ)
  letI : UniformSpace (E F S) := IsTopologicalAddGroup.rightUniformSpace _
  letI : IsUniformAddGroup (E F S) := isUniformAddGroup_of_addCommGroup
  letI : CompleteSpace (E F S) := sLocalBruhat_complete F S
  letI : BarrelledSpace ℂ (E F S) := sLocalBruhat_barrelled F S
  letI : PolynormableSpace ℂ (E F S) := (sLocalBruhat_nuclear F S).2.1
  letI : CompleteSpace D := sLocalBruhat_strongDual_complete F S
  letI : PolynormableSpace ℂ D := strongDual_withBoundedSeminorms.toPolynormableSpace
  obtain ⟨e, he⟩ := strongBidual_equiv_of_nuclear (sLocalBruhat_nuclear F S)
  apply differentiableOn_univ.mp
  apply differentiableOn_of_weaklyHolomorphicOn (E := D) (f := sLocalEulerClearedWeil F S ω) isOpen_univ
  intro φ
  obtain ⟨f, rfl⟩ := e.surjective φ
  exact (sLocalEulerNormalizedMellin_entire F S (fun v => μ F v.val) ω f).differentiableOn.congr
    fun z _ => (he f (sLocalEulerClearedWeil F S ω z)).trans (sLocalEulerClearedWeil_apply F S ω z f)

private theorem sLocalEulerClearedWeil_translate (g : (SAdeles F S)ˣ) (f : E F S) (c : ℂ) :
    sLocalEulerClearedWeil F S ω c (sLocalBruhatLeftTranslate F S g f) =
      sLocalZetaWeight F S ω c (QuotientGroup.mk g) * sLocalEulerClearedWeil F S ω c f := by
  let f' := sLocalBruhatLeftTranslate F S g f
  let Q (z : ℂ) := sLocalZetaWeight F S ω z (QuotientGroup.mk g)
  let D := sLocalEulerDenominator F S ω
  simp only [sLocalEulerClearedWeil_apply]
  have hA (x : E F S) : AnalyticOnNhd ℂ (N F S ω x) univ :=
    sLocalEulerNormalizedMellin_entire F S _ ω x
  have hQ : AnalyticOnNhd ℂ Q univ := by
    intro z _
    unfold Q sLocalZetaWeight
    exact ((analyticAt_id.mul analyticAt_const).cexp).mul analyticAt_const
  have hp0 : ∀ᶠ z : ℂ in 𝓝 (1 : ℂ), 0 < z.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  have hp : ∀ᶠ z : ℂ in 𝓝[≠] (1 : ℂ), 0 < z.re := hp0.filter_mono nhdsWithin_le_nhds
  have he : N F S ω f' =ᶠ[𝓝[≠] (1 : ℂ)] fun z => Q z * N F S ω f z := by
    filter_upwards [hp, sLocalEulerNormalizedMellin_eq_germ F S (fun v => μ F v.val) ω f' 1,
      sLocalEulerNormalizedMellin_eq_germ F S (fun v => μ F v.val) ω f 1] with z hz hf' hf
    change N F S ω f' z = D z * sLocalContinuedMellinEval F S (fun v => μ F v.val) ω z f' at hf'
    change N F S ω f z = D z * sLocalContinuedMellinEval F S (fun v => μ F v.val) ω z f at hf
    rw [hf', hf]
    have hh := sLocalProductZetaContinued_leftTranslate_right F S (fun v => μ F v.val) ω g f hz
    change sLocalContinuedMellinEval F S (fun v => μ F v.val) ω z f' =
      Q z * sLocalContinuedMellinEval F S (fun v => μ F v.val) ω z f at hh
    rw [hh, mul_left_comm]
  have h := (hA f').eqOn_of_preconnected_of_frequently_eq (hQ.mul (hA f))
    isPreconnected_univ (mem_univ (1 : ℂ)) he.frequently
  exact h (mem_univ c)

private def finiteUnitMassProduct : ℂ :=
  ∏ v : S, (μ F v.val).real (finitePlaceIntegralUnits F v.val)

private theorem finiteUnitMassProduct_ne_zero : finiteUnitMassProduct F S ≠ 0 := by
  unfold finiteUnitMassProduct
  exact Finset.prod_ne_zero_iff.mpr fun v _ =>
    Complex.ofReal_ne_zero.mpr (finiteZetaUnitMass_pos F v.val (μ F v.val)).ne'

/-- The scalar taking the Euler-cleared Mellin distribution to the
Gaussian-normalized tensor distribution. -/
def sLocalWeilScale : ℂ := ((2 : ℂ) ^ Fintype.card (C F)) / finiteUnitMassProduct F S

/-- The entire S-local tensor distribution with the corrected reference normalization. -/
def sLocalNormalizedWeil (z : ℂ) : StrongDual ℂ (E F S) :=
  sLocalWeilScale F S • sLocalEulerClearedWeil F S ω z

theorem sLocalNormalizedWeil_holomorphic :
    Differentiable ℂ (sLocalNormalizedWeil F S ω) := by
  letI : PolynormableSpace ℂ (StrongDual ℂ (E F S)) := strongDual_withBoundedSeminorms.toPolynormableSpace
  let M := sLocalWeilScale F S • ContinuousLinearMap.id ℂ (StrongDual ℂ (E F S))
  change Differentiable ℂ (M ∘ sLocalEulerClearedWeil F S ω)
  intro z
  obtain ⟨D, hD⟩ := sLocalEulerClearedWeil_holomorphic F S ω z
  refine ⟨M.comp D, HasFDerivAt.of_isLittleOTVS ?_⟩
  simpa only [Function.comp_def, ContinuousLinearMap.comp_apply, map_sub]
    using (ContinuousLinearMap.isBigOTVS_comp (𝕜 := ℂ) (E := StrongDual ℂ (E F S))
      (F := StrongDual ℂ (E F S)) M).trans_isLittleOTVS hD.isLittleOTVS

theorem sLocalNormalizedWeil_translate (z : ℂ) (g : (SAdeles F S)ˣ) (f : E F S) :
    sLocalNormalizedWeil F S ω z (sLocalBruhatLeftTranslate F S g f) =
      sLocalZetaWeight F S ω z (QuotientGroup.mk g) * sLocalNormalizedWeil F S ω z f := by
  change sLocalWeilScale F S * sLocalEulerClearedWeil F S ω z (sLocalBruhatLeftTranslate F S g f) =
    sLocalZetaWeight F S ω z (QuotientGroup.mk g) * (sLocalWeilScale F S * sLocalEulerClearedWeil F S ω z f)
  rw [sLocalEulerClearedWeil_translate, mul_left_comm]

/-- Its values on separated tests are exactly the products of the
Gaussian-normalized distributions at the selected places. -/
theorem sLocalNormalizedWeil_separated (z : ℂ)
    (f : R F → 𝓢(ℝ, ℂ)) (g : C F → 𝓢(ℂ, ℂ))
    (k : ∀ v : S, locallyConstantTests (L F v.val)) :
    sLocalNormalizedWeil F S ω z
      (sLocalBruhatPure F S (mixedWeilTest F f g) (locallyConstantTestPiProduct k)) =
      ((∏ v, realWeilNormalizedFamily (a F S ω v).2 (z + (a F S ω v).1) (f v)) *
        ∏ v, correctedComplexWeilNormalizedFamily (j F S ω v).2 (z + (j F S ω v).1) (g v)) *
        ∏ v, finiteWeilNormalizedDistribution F v.val (μ F v.val) (χ F S ω v) z (k v) := by
  let X := ∏ v : R F, realWeilNormalizedFamily (a F S ω v).2 (z + (a F S ω v).1) (f v)
  let Y (v : C F) : ℂ := complexWeilNormalizedFamily (j F S ω v).2 (z + (j F S ω v).1) (g v)
  let W (v : S) : ℂ := ((μ F v.val).real (finitePlaceIntegralUnits F v.val) : ℂ)
  let Z (v : S) : ℂ := finiteWeilNormalizedDistribution F v.val (μ F v.val) (χ F S ω v) z (k v)
  change sLocalWeilScale F S * sLocalEulerClearedWeil F S ω z _ = _
  rw [sLocalEulerClearedWeil_apply]
  have h := sLocalEulerNormalizedMellin_separated_eval F S ω (μ F) _ _ _
    (mixedWeilTest_apply F f g) k z
  change N F S ω (sLocalBruhatPure F S (mixedWeilTest F f g) (locallyConstantTestPiProduct k)) z = _ at h
  rw [h]
  change sLocalWeilScale F S * ((X * ∏ v, Y v) * ∏ v, W v * Z v) =
    (X * ∏ v, (2 : ℂ) * Y v) * ∏ v, Z v
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  unfold sLocalWeilScale
  change (_ / finiteUnitMassProduct F S) * ((X * ∏ v, Y v) *
    (finiteUnitMassProduct F S * ∏ v, Z v)) = _
  field_simp [finiteUnitMassProduct_ne_zero F S]

/-- The normalized family annihilates the ordinary S-local theta kernel at
every exponent, including each exceptional exponent of the Euler factor. -/
theorem sLocalNormalizedWeil_vanishes (z : ℂ) (f : E F S)
    (hf : f ∈ (sLocalThetaOperator F S).ker) :
    sLocalNormalizedWeil F S ω z f = 0 := by
  let η := sLocalZetaProductMeasure F S (fun v => μ F v.val) (archimedeanMultiplicativeHaar F)
  letI : η.IsHaarMeasure := sLocalZetaProductMeasure_isHaar F S _ _
  obtain ⟨ν, hν, hW⟩ := sLocalClassHaar_exists_weil F S η
  letI := hν
  have h0 (q : SIdeleQuotient F S) : sLocalThetaOperator F S f q = 0 :=
    congrFun (LinearMap.mem_ker.mp hf) q
  have hp0 : ∀ᶠ w : ℂ in 𝓝 (1 : ℂ), 0 < w.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  have hp : ∀ᶠ w : ℂ in 𝓝[≠] (1 : ℂ), 0 < w.re := hp0.filter_mono nhdsWithin_le_nhds
  have he : N F S ω f =ᶠ[𝓝[≠] (1 : ℂ)] 0 := by
    filter_upwards [hp, sLocalEulerNormalizedMellin_eq_germ F S (fun v => μ F v.val) ω f 1] with w hw hn
    have hz := (sLocalIdelicZeta_meromorphic_continuation F S (fun v => μ F v.val) ω f).2 hw
    have hθ := (sLocalIdelicZeta_integrable_eq_theta F S η ν hW ω f w hw).2
    have ht : sLocalThetaZetaIntegral F S ν ω f w = 0 := by
      change ∫ q, sLocalZetaWeight F S ω w q * sLocalThetaOperator F S f q
        ∂sLocalClassHaar F S ν = 0
      simp only [h0, mul_zero, integral_zero]
    rw [hθ, ht] at hz
    change N F S ω f w = _ at hn
    rw [hn]
    change sLocalEulerDenominator F S ω w * sLocalProductZetaContinued F S
      (fun v => μ F v.val) ω (a F S ω) (j F S ω) f w = 0
    rw [hz, mul_zero]
  have ha := sLocalEulerNormalizedMellin_entire F S (fun v => μ F v.val) ω f
  have h := ha.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ
    (mem_univ (1 : ℂ)) he.frequently (mem_univ z)
  change sLocalWeilScale F S * sLocalEulerClearedWeil F S ω z f = 0
  change N F S ω f z = 0 at h
  rw [sLocalEulerClearedWeil_apply, h, mul_zero]

/-- The product of the local reference Gaussians with the corrected angular conjugation. -/
def sLocalWeilReference : E F S :=
  sLocalBruhatPure F S
    (mixedWeilTest F (mixedWeilRealReference F (a F S ω))
      (fun v => correctedComplexWeilReference (j F S ω v).2))
    (locallyConstantTestPiProduct (fun v => finiteWeilNormalizedTest F v.val (χ F S ω v)))

theorem sLocalNormalizedWeil_reference (z : ℂ) :
    sLocalNormalizedWeil F S ω z (sLocalWeilReference F S ω) = 1 := by
  rw [sLocalWeilReference, sLocalNormalizedWeil_separated]
  have hR (v : R F) : realWeilNormalizedFamily (a F S ω v).2 (z + (a F S ω v).1)
      (mixedWeilRealReference F (a F S ω) v) = 1 :=
    (realGammaNormalized_distribution (a F S ω v).2).choose_spec.choose_spec.2.2.1 _
  simp only [hR, correctedComplexWeilNormalizedFamily_reference,
    finiteWeilNormalizedDistribution_reference, Finset.prod_const_one, mul_one]

private abbrev Θ := SLocalThetaQuotient F S
private abbrev M := (sLocalThetaOperator F S).ker

/-- The normalized distribution on the ordinary S-local theta quotient. -/
def sLocalThetaWeil (z : ℂ) : StrongDual ℂ (Θ F S) :=
  (M F S).liftQL (sLocalNormalizedWeil F S ω z) (sLocalNormalizedWeil_vanishes F S ω z)

theorem sLocalThetaWeil_transpose (z : ℂ) :
    sLocalThetaTranspose F S (sLocalThetaWeil F S ω z) = sLocalNormalizedWeil F S ω z := by
  ext f
  rfl

theorem sLocalThetaWeil_translate (z : ℂ) (q : SIdeleQuotient F S) (f : Θ F S) :
    sLocalThetaWeil F S ω z (sLocalThetaTranslate F S q f) =
      sLocalZetaWeight F S ω z q * sLocalThetaWeil F S ω z f := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨x, rfl⟩ := (M F S).mkQ_surjective f
  change sLocalThetaWeil F S ω z (sLocalThetaTranslateIdeles F S g (Submodule.Quotient.mk x)) = _
  rw [sLocalThetaTranslateIdeles_mk]
  exact sLocalNormalizedWeil_translate F S ω z g x

/-- The kernel lift gives an entire family in the strong theta dual. -/
theorem sLocalThetaWeil_holomorphic : Differentiable ℂ (sLocalThetaWeil F S ω) := by
  let D := StrongDual ℂ (Θ F S)
  letI : T2Space (Θ F S) := sLocalThetaQuotient_t2Space F S
  letI : UniformSpace (Θ F S) := IsTopologicalAddGroup.rightUniformSpace _
  letI : IsUniformAddGroup (Θ F S) := isUniformAddGroup_of_addCommGroup
  letI : CompleteSpace (Θ F S) := sLocalThetaQuotient_complete F S
  letI : BarrelledSpace ℂ (Θ F S) := sLocalThetaQuotient_barrelled F S
  letI : PolynormableSpace ℂ (Θ F S) := (sLocalThetaQuotient_nuclear F S).2.1
  letI : CompleteSpace D := sLocalThetaQuotient_strongDual_complete F S
  letI : PolynormableSpace ℂ D := strongDual_withBoundedSeminorms.toPolynormableSpace
  obtain ⟨e, he⟩ := strongBidual_equiv_of_nuclear (sLocalThetaQuotient_nuclear F S)
  apply differentiableOn_univ.mp
  apply differentiableOn_of_weaklyHolomorphicOn isOpen_univ
  intro φ
  obtain ⟨q, rfl⟩ := e.surjective φ
  obtain ⟨f, rfl⟩ := (M F S).mkQ_surjective q
  have hf : Differentiable ℂ (fun z => sLocalNormalizedWeil F S ω z f) := by
    intro z
    have hz := (vectorHolomorphic_hasDerivAt_comp (f := sLocalNormalizedWeil F S ω)
      (sLocalNormalizedWeil_holomorphic F S ω).differentiableOn isOpen_univ
      (strongBidualEvaluation f) ⟨z, mem_univ z⟩).differentiableAt
    exact hz
  exact hf.differentiableOn.congr fun z _ =>
    (he ((M F S).mkQ f) (sLocalThetaWeil F S ω z)).trans (by rfl)

/-- Reflected Laurent coefficients with the actual eigendistribution
of Theorem 5.5.1.2 and the explicit local Tate epsilon product. -/
theorem sLocalPrincipalParts_thetaWeil (c : ℂ) (hc : sLocalEulerPoleLattices F S ω c) :
    ∃ (ε : S → ℂ → ℂ) (V : ℂ → ℂ),
      (∀ v, IsFiniteTateMultiplier F S (fun w ↦ μ F w.val) (χ F S ω) v (ε v)) ∧
      AnalyticAt ℂ V c ∧
      let m := sLocalPoleCount F S ω c
      let D := sLocalEulerLeadingDenominator F S ω c
      let P := sLocalTateEpsilonProduct F S ω ε
      let ρ := sLocalExplicitTateFactor F S ω P
      meromorphicOrderAt ρ c = -(m : WithTop ℤ) ∧
      ((fun z ↦ (z - c)^m * ρ z) =ᶠ[𝓝[≠] c] V) ∧
      V c = P c * sLocalEulerDenominator F S ω⁻¹ (1-c) / D ∧
      (∀ f : E F S, sLocalLaurentCoeff F S (fun w ↦ μ F w.val) ω c m f =
        D⁻¹ * (P c / sLocalWeilScale F S) *
          sLocalThetaTranspose F S (sLocalThetaWeil F S ω⁻¹ (1-c))
            (sLocalSelectedFourier F S f)) ∧
      (sLocalLaurentCoeff F S (fun w ↦ μ F w.val) ω c m ≠ 0) ∧
      (∀ (u : (SAdeles F S)ˣ) (f : E F S),
        sLocalLaurentCoeff F S (fun w ↦ μ F w.val) ω c m (sLocalBruhatLeftTranslate F S u f) =
          sLocalZetaWeight F S ω c (QuotientGroup.mk u) *
            sLocalLaurentCoeff F S (fun w ↦ μ F w.val) ω c m f) ∧
      (∀ (f : E F S) (k : ℕ), k ≤ m →
        sLocalLaurentCoeff F S (fun w ↦ μ F w.val) ω c k f =
          ∑ j ∈ Finset.range (m - k + 1), taylorCoeff V c j *
            taylorCoeff (fun z ↦ sLocalProductZetaContinued F S (fun w ↦ μ F w.val) ω⁻¹
              (a F S ω⁻¹) (sLocalComplexArchParameters F S ω⁻¹) (sLocalSelectedFourier F S f) (1-z))
              c (m - k - j)) := by
  letI : MeasurableSpace (InfiniteAdeleRing F) := borel _
  letI : BorelSpace (InfiniteAdeleRing F) := ⟨rfl⟩
  obtain ⟨ε,hε,_,_,_,hAll⟩ :=
    exists_sLocalTateProduct_fourier F S (fun w ↦ μ F w.val) ω
  obtain ⟨e,V,_,_,hNorm,hV,horder,hgerm,hVc,hEq,hne,_,hlead,hrest⟩ :=
    sLocalPrincipalParts_reflected F S (fun w ↦ μ F w.val) ω c hc
  let P := sLocalTateEpsilonProduct F S ω ε
  have hεeq : e = P := by
    obtain ⟨g,B,hB,hg⟩ := exists_sLocalEulerNormalizedMellin_constant F S (fun w ↦ μ F w.val) ω⁻¹
    obtain ⟨f,hf⟩ := sLocalSelectedFourier_surjective F S g
    funext z
    have h := hAll f z
    have h' := hNorm f z
    change N F S ω f z = P z * N F S ω⁻¹ (sLocalSelectedFourier F S f) (1-z) at h
    change N F S ω f z = e z * N F S ω⁻¹ (sLocalSelectedFourier F S f) (1-z) at h'
    have hBz : N F S ω⁻¹ g (1-z) = B := congrFun hg (1-z)
    rw [hf, hBz] at h h'
    exact mul_right_cancel₀ hB (h'.symm.trans h)
  subst e
  refine ⟨ε,V,hε,hV,horder,hgerm,hVc,?_,?_,?_,hrest⟩
  · intro f
    rw [hlead f, hEq f, sLocalThetaWeil_transpose]
    change _ = _ * _ * (sLocalWeilScale F S * sLocalEulerClearedWeil F S ω⁻¹ (1-c)
      (sLocalSelectedFourier F S f))
    rw [sLocalEulerClearedWeil_apply]
    have hs : sLocalWeilScale F S ≠ 0 :=
      div_ne_zero (pow_ne_zero _ (by norm_num : (2 : ℂ) ≠ 0)) (finiteUnitMassProduct_ne_zero F S)
    dsimp only [P]
    field_simp [hs]
  · intro h
    apply hne
    ext f
    change sLocalEulerLeadingDenominator F S ω c *
      sLocalLaurentCoeff F S (fun w ↦ μ F w.val) ω c (sLocalPoleCount F S ω c) f = 0
    rw [h]
    simp
  · intro u f
    rw [show sLocalPoleCount F S ω c = sLocalAllowedPoleOrder F S ω c from
      (sLocalAllowedPoleOrder_eq_count F S ω c).symm, sLocalLaurentCoeff_top_translate]

end
end Masullo
