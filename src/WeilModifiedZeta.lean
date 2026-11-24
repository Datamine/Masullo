import IdelicTamagawaLocalComparison
import GlobalHeckeEulerComparison

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical ENNReal NumberField SchwartzMap

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

private abbrev Place := HeightOneSpectrum (𝓞 F)
private abbrev Local (v : Place F) := v.adicCompletion F
private abbrev Phase (v : Place F) := (Local F v)ˣ →ₜ* Circle
private abbrev Tests (v : Place F) := locallyConstantTests (Local F v)

local instance (v : Place F) : MeasurableSpace (Local F v) := borel _
local instance (v : Place F) : BorelSpace (Local F v) := ⟨rfl⟩
local instance (v : Place F) : MeasurableSpace (Local F v)ˣ := borel _
local instance (v : Place F) : BorelSpace (Local F v)ˣ := ⟨rfl⟩
local instance (v : Place F) : LocallyCompactSpace (Local F v) := finitePlace_locallyCompact F v
local instance (v : Place F) : SecondCountableTopology (Local F v) := finitePlace_secondCountable F v
local instance (v : Place F) : LocallyCompactSpace (Local F v)ˣ :=
  IsOpenUnits.isOpenEmbedding_unitsVal.locallyCompactSpace
local instance (v : Place F) : SecondCountableTopology (Local F v)ˣ :=
  Units.isEmbedding_val₀.secondCountableTopology
local instance (v : Place F) : (finitePlaceMultiplicativeTamagawa F v).IsHaarMeasure :=
  finitePlaceMultiplicativeTamagawa_isHaar F v
local instance (v : Place F) : SigmaFinite (finitePlaceMultiplicativeTamagawa F v) := inferInstance

variable (v : Place F)

/-- The modified finite factor in (3.4.1.3)–(3.4.1.4). The unramified
factor uses a uniformizer difference, and the ramified factor is unchanged. -/
def weilModifiedFiniteZeta (χ : Phase F v) (f : Tests F v) (z : ℂ) : ℂ :=
  finiteZetaIntegral F v (finitePlaceMultiplicativeTamagawa F v) χ
    (if finiteZetaUnramified F v χ then finitePrincipalValue (chosenFiniteUniformizer F v) f
      else f) z

theorem weilModifiedFiniteZeta_integerRing (χ : Phase F v)
    (hχ : finiteZetaUnramified F v χ) (z : ℂ) :
    weilModifiedFiniteZeta F v χ (finiteCompletionIntegerRingTest F v) z =
      ((differentPrimeMass F v).toReal : ℂ) := by
  rw [weilModifiedFiniteZeta, ite_eq_left hχ,
    finiteZetaIntegral_principalValue_integerRing F v _ χ hχ _ (chosenFiniteUniformizer_spec F v),
    measureReal_def, finitePlaceMultiplicativeTamagawa_units]

theorem weilModifiedFiniteZeta_analytic (χ : Phase F v) (f : Tests F v) :
    AnalyticOnNhd ℂ (weilModifiedFiniteZeta F v χ f) {z | 0 < z.re} := by
  let g := if finiteZetaUnramified F v χ then finitePrincipalValue (chosenFiniteUniformizer F v) f
    else f
  let μ := finitePlaceMultiplicativeTamagawa F v
  letI : μ.IsHaarMeasure := finitePlaceMultiplicativeTamagawa_isHaar F v
  intro z hz
  have ha := (finiteZetaContinuation_poles F v μ χ g z).2 (fun h =>
    finiteZetaDenominator_ne_zero_of_pos F v χ z hz (by simp [finiteZetaDenominator, h.2.2]))
  apply ha.congr
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz] with w hw
  exact (finiteZetaContinuation_eq_integral F v μ χ g w hw).2.symm

/-- The unramified uniformizer difference cancels the corresponding
ordinary Euler denominator. The calculation works for any uniformizer. -/
theorem finiteZetaIntegral_uniformizerDifference
    (χ : Phase F v) (hχ : finiteZetaUnramified F v χ)
    (π : (Local F v)ˣ) (hπ : Valued.v.IsUniformizer π.val) (f : Tests F v)
    (z : ℂ) (hz : 0 < z.re) :
    finiteZetaIntegral F v (finitePlaceMultiplicativeTamagawa F v) χ (finitePrincipalValue π f) z =
      finiteZetaDenominator F v χ z *
        finiteZetaIntegral F v (finitePlaceMultiplicativeTamagawa F v) χ f z := by
  let μ := finitePlaceMultiplicativeTamagawa F v
  letI : μ.IsHaarMeasure := finitePlaceMultiplicativeTamagawa_isHaar F v
  let q := chosenFiniteUniformizer F v
  have hπq : (χ π : ℂ) = (χ q : ℂ) := by
    have hq : (v.asIdeal.absNorm : ℝ) ≠ 0 := by
      exact_mod_cast (zero_lt_one.trans (HeightOneSpectrum.one_lt_absNorm v)).ne'
    have hr : ‖(π / q : (Local F v)ˣ).val‖ = 1 := by
      rw [Units.val_div_eq_div_val, norm_div, norm_finiteUniformizer F v π hπ,
        norm_finiteUniformizer F v q (chosenFiniteUniformizer_spec F v),
        div_self (inv_ne_zero hq)]
    have hu := hχ (π / q) (by
      change π / q ∈ finitePlaceIntegralUnits F v
      rw [← finiteZetaShell_zero]
      change ‖(π / q : (Local F v)ˣ).val‖ = (v.asIdeal.absNorm : ℝ) ^ (-(0 : ℤ))
      rw [hr, neg_zero, zpow_zero])
    rw [map_div, div_eq_one] at hu
    exact congrArg Subtype.val hu
  have hweight : (χ π : ℂ) * finiteZetaWeight F v z π = finiteZetaRatio F v χ z := by
    unfold finiteZetaWeight finiteZetaRatio
    rw [hπq, norm_finiteUniformizer F v π hπ, Real.log_inv, Complex.ofReal_neg, mul_neg, neg_mul]
  let L : Tests F v →ₗ[ℂ] ℂ :=
    { toFun := fun f => finiteZetaIntegral F v μ χ f z
      map_add' := fun f g => finiteZetaIntegral_add F v μ χ f g z hz
      map_smul' := fun c f => finiteZetaIntegral_smul F v μ χ c f z }
  change L (f - locallyConstantTestTranslate (Local F v) π f) = finiteZetaDenominator F v χ z * L f
  rw [map_sub]
  change finiteZetaIntegral F v μ χ f z -
    finiteZetaIntegral F v μ χ (locallyConstantTestTranslate (Local F v) π f) z = _
  rw [finiteZetaIntegral_translate, hweight, finiteZetaDenominator, sub_mul, one_mul]
  rfl

theorem weilModifiedFiniteZeta_eq_multiplier (χ : Phase F v) (f : Tests F v)
    (z : ℂ) (hz : 0 < z.re) :
    weilModifiedFiniteZeta F v χ f z = finiteZetaWeilMultiplier F v χ z *
      finiteZetaIntegral F v (finitePlaceMultiplicativeTamagawa F v) χ f z := by
  by_cases h : finiteZetaUnramified F v χ
  · simpa only [weilModifiedFiniteZeta, finiteZetaWeilMultiplier, ite_eq_left h, finiteZetaDenominator] using
      finiteZetaIntegral_uniformizerDifference F v χ h _ (chosenFiniteUniformizer_spec F v) f z hz
  · simp only [weilModifiedFiniteZeta, finiteZetaWeilMultiplier, ite_eq_right h, one_mul]

/-- The finite factors of (3.4.1.1), including the finite Tamagawa scalars. -/
def weilModifiedFiniteProduct (χ : ∀ v : Place F, Phase F v) (f : ∀ v : Place F, Tests F v)
    (z : ℂ) : ℂ :=
  ∏' v, weilModifiedFiniteZeta F v (χ v) (f v) z

variable {v}
  (χ : ∀ v : Place F, Phase F v) (f : ∀ v : Place F, Tests F v) (S : Finset (Place F))
  (hS : ∀ v ∉ S, finiteZetaUnramified F v (χ v) ∧ f v = finiteCompletionIntegerRingTest F v)

include hS

private theorem weilModifiedFiniteProduct_outside (v : Place F) (hv : v ∉ S) (z : ℂ) :
    weilModifiedFiniteZeta F v (χ v) (f v) z = ((differentPrimeMass F v).toReal : ℂ) := by
  rw [(hS v hv).2, weilModifiedFiniteZeta_integerRing F v (χ v) (hS v hv).1]

set_option maxHeartbeats 1500000 in
/-- Cutting the modified product at any stage containing the exceptional
tests and ramification leaves the mass of the omitted integral units. -/
theorem weilModifiedFiniteProduct_eq_stage (z : ℂ) :
    weilModifiedFiniteProduct F χ f z =
      ((integralIdeleTailMass F S).toReal : ℂ) *
        ∏ v ∈ S, weilModifiedFiniteZeta F v (χ v) (f v) z := by
  let m : ℝ≥0∞ →* ℂ := Complex.ofRealHom.toMonoidHom.comp ENNReal.toRealHom.toMonoidHom
  let d (v : {v : Place F // v ∉ S}) := differentPrimeMass F v.val
  have hd : d.HasFiniteMulSupport :=
    (differentPrimeMass_finite F).preimage Subtype.val_injective.injOn
  have hm : (m ∘ d).HasFiniteMulSupport :=
    hd.subset fun _ h h₁ => h (by simp [Function.comp_apply, h₁])
  have hmprod : HasProd (m ∘ d) (((integralIdeleTailMass F S).toReal : ℝ) : ℂ) := by
    have h : HasProd (m ∘ d) (∏' a, (m ∘ d) a) :=
      (multipliable_of_hasFiniteMulSupport hm).hasProd
    rw [tprod_eq_finprod hm] at h
    change HasProd (m ∘ d) (∏ᶠ a, m (d a)) at h
    rw [← map_finprod m hd] at h
    exact h
  let b (v : Place F) := weilModifiedFiniteZeta F v (χ v) (f v) z
  have heq : (fun v : {v : Place F // v ∉ S} => b v.val) = m ∘ d :=
    funext fun v => weilModifiedFiniteProduct_outside F χ f S hS v.val v.property z
  have hout : HasProd (fun v : {v : Place F // v ∉ S} => b v.val)
      (((integralIdeleTailMass F S).toReal : ℝ) : ℂ) := by
    rw [heq]
    exact hmprod
  have hfull := (Finset.hasProd S b).mul_compl hout
  change (∏' v, b v) = (((integralIdeleTailMass F S).toReal : ℂ) * ∏ v ∈ S, b v)
  exact hfull.tprod_eq.trans (mul_comm _ _)

/-- The modified finite factors are identically one outside a common
finite set, so the product is absolutely convergent and stabilizes uniformly
throughout the component. -/
theorem weilModifiedFiniteProduct_stabilizes :
    ∃ T : Finset (Place F), S ⊆ T ∧
      (∀ v ∉ T, ∀ z, weilModifiedFiniteZeta F v (χ v) (f v) z = 1) ∧
      (∀ U : Finset (Place F), T ⊆ U → ∀ z,
        (∏ v ∈ U, weilModifiedFiniteZeta F v (χ v) (f v) z) =
          weilModifiedFiniteProduct F χ f z) := by
  let D := (differentPrimeMass_finite F).toFinset
  let T := S ∪ D
  have he (v : Place F) (hv : v ∉ T) (z : ℂ) :
      weilModifiedFiniteZeta F v (χ v) (f v) z = 1 := by
    rw [weilModifiedFiniteProduct_outside F χ f S hS v (fun hs => hv (Finset.mem_union_left D hs))]
    have hd : differentPrimeMass F v = 1 := by
      by_contra h
      exact hv (Finset.mem_union_right S ((Set.Finite.mem_toFinset _).mpr h))
    simp [hd]
  refine ⟨T, Finset.subset_union_left, he, fun U hU z => ?_⟩
  exact (tprod_eq_prod fun v hv => he v (fun ht => hv (hU ht)) z).symm

theorem weilModifiedFiniteProduct_analytic :
    AnalyticOnNhd ℂ (weilModifiedFiniteProduct F χ f) {z | 0 < z.re} := by
  intro z hz
  obtain ⟨T, _, _, hT⟩ := weilModifiedFiniteProduct_stabilizes F χ f S hS
  rw [← funext (hT T subset_rfl)]
  exact Finset.analyticAt_fun_prod T fun v _ => weilModifiedFiniteZeta_analytic F v (χ v) (f v) z hz

omit hS in
/-- Uniform convergence follows from equality at every stage above one
finite threshold, even for families with common exceptional places. -/
theorem weilModifiedFiniteProduct_tendstoUniformly
    {X : Type*} (χX : X → ∀ v : Place F, Phase F v) (zX : X → ℂ)
    (hX : ∀ x v, v ∉ S → finiteZetaUnramified F v (χX x v) ∧
      f v = finiteCompletionIntegerRingTest F v) :
    TendstoUniformly (fun U : Finset (Place F) => fun x =>
      ∏ v ∈ U, weilModifiedFiniteZeta F v (χX x v) (f v) (zX x))
      (fun x => weilModifiedFiniteProduct F (χX x) f (zX x)) atTop := by
  let D := (differentPrimeMass_finite F).toFinset
  intro W hW
  filter_upwards [eventually_ge_atTop (S ∪ D)] with U hU x
  have he (v : Place F) (hv : v ∉ U) :
      weilModifiedFiniteZeta F v (χX x v) (f v) (zX x) = 1 := by
    have hvS : v ∉ S := fun h => hv (hU (Finset.mem_union_left D h))
    have hd : differentPrimeMass F v = 1 := by
      by_contra h
      exact hv (hU (Finset.mem_union_right S ((Set.Finite.mem_toFinset _).mpr h)))
    rw [(hX x v hvS).2, weilModifiedFiniteZeta_integerRing F v _ (hX x v hvS).1, hd]
    simp
  have ht : weilModifiedFiniteProduct F (χX x) f (zX x) =
      ∏ v ∈ U, weilModifiedFiniteZeta F v (χX x v) (f v) (zX x) := tprod_eq_prod he
  rw [ht]
  exact refl_mem_uniformity hW

omit hS in
/-- A compact family of global quasi-characters has a common finite
set outside which all its characters are unramified. -/
theorem exists_common_unramified_stage_of_isCompact
    (K : Set (QuasiCharacter (IdeleClass F))) (hK : IsCompact K) :
    ∃ T : Finset (Place F), K ⊆ (sUnramified F T : Set (QuasiCharacter (IdeleClass F))) := by
  have hc : K ⊆ ⋃ T : Finset (Place F), (sUnramified F T : Set (QuasiCharacter (IdeleClass F))) := by
    intro c _
    obtain ⟨T, hT⟩ := exists_sUnramified F c
    exact mem_iUnion.mpr ⟨T, hT⟩
  obtain ⟨R, hR⟩ := hK.elim_finite_subcover
    (fun T : Finset (Place F) => (sUnramified F T : Set (QuasiCharacter (IdeleClass F))))
    (fun T => (sUnramified F T).isOpen) hc
  refine ⟨R.biUnion id, fun c hc => ?_⟩
  obtain ⟨T, hT, hu⟩ := mem_iUnion₂.mp (hR hc)
  apply (mem_sUnramified_iff F _ c).mpr
  intro v hv a
  exact (mem_sUnramified_iff F T c).mp hu v
    (fun h => hv (Finset.mem_biUnion.mpr ⟨T, hT, h⟩)) a

private abbrev Arch := (InfiniteAdeleRing F)ˣ
local instance : MeasurableSpace (Arch F) := borel _
local instance : BorelSpace (Arch F) := ⟨rfl⟩
local instance : MeasurableSpace (SAdeles F S)ˣ := borel _
local instance : BorelSpace (SAdeles F S)ˣ := ⟨rfl⟩

variable (ω : PontryaginDual (SLocalThetaNormOne F S))
  (hω : ∀ v : S, sLocalFiniteZetaPhases F S ω v = χ v.val)
  (φ : 𝓢(mixedEmbedding.mixedSpace F, ℂ))

omit hS in
/-- The modified zeta product on a component, with its actual
archimedean integral and all finite factors. -/
def weilModifiedZeta : ℂ → ℂ :=
  fun z => sLocalArchZetaIntegral F S (archimedeanMultiplicativeHaar F) ω φ z *
    weilModifiedFiniteProduct F χ f z

include hω in
/-- The modified global product is a local zeta integral with modified
selected tests, times the omitted integral-unit mass. -/
theorem weilModifiedZeta_eq_sLocal (z : ℂ) (hz : 0 < z.re) :
    weilModifiedZeta F χ f S ω φ z =
      ((integralIdeleTailMass F S).toReal : ℂ) *
        sLocalIdelicZetaIntegral F S (sLocalMultiplicativeTamagawa F S) ω
          (sLocalBruhatPure F S φ (locallyConstantTestPiProduct fun v : S =>
            if finiteZetaUnramified F v.val (χ v.val) then
              finitePrincipalValue (chosenFiniteUniformizer F v.val) (f v.val)
            else f v.val)) z := by
  let μ (v : S) := finitePlaceMultiplicativeTamagawa F v.val
  haveI (v : S) : (μ v).IsHaarMeasure := finitePlaceMultiplicativeTamagawa_isHaar F v.val
  haveI (v : S) : SigmaFinite (μ v) := inferInstanceAs (SigmaFinite (finitePlaceMultiplicativeTamagawa F v.val))
  unfold weilModifiedZeta
  rw [weilModifiedFiniteProduct_eq_stage F χ f S hS z,
    show sLocalMultiplicativeTamagawa F S = sLocalZetaProductMeasure F S μ
      (archimedeanMultiplicativeHaar F) from rfl,
    sLocalIdelicZetaIntegral_pure_product F S μ _ ω _ _ z hz]
  rw [Finset.prod_subtype S (fun _ => Iff.rfl)]
  simp only [hω, weilModifiedFiniteZeta, μ]
  ring

include hω in
theorem weilModifiedZeta_analytic :
    AnalyticOnNhd ℂ (weilModifiedZeta F χ f S ω φ) {z | 0 < z.re} := by
  let μ := sLocalMultiplicativeTamagawa F S
  letI : μ.IsHaarMeasure := sLocalMultiplicativeTamagawa_isHaar F S
  let g := sLocalBruhatPure F S φ (locallyConstantTestPiProduct fun v : S =>
    if finiteZetaUnramified F v.val (χ v.val) then
      finitePrincipalValue (chosenFiniteUniformizer F v.val) (f v.val)
    else f v.val)
  intro z hz
  apply (analyticAt_const.mul (sLocalIdelicZeta_analytic F S μ ω g z hz)).congr
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz] with w hw
  exact (weilModifiedZeta_eq_sLocal F χ f S hS ω hω φ w hw).symm

omit hS

local instance : MeasurableSpace (Idele F) := borel _
local instance : BorelSpace (Idele F) := ⟨rfl⟩
local instance (T : Finset (Place F)) : MeasurableSpace (SAdeles F T)ˣ := borel _
local instance (T : Finset (Place F)) : BorelSpace (SAdeles F T)ˣ := ⟨rfl⟩

private abbrev localMeasure := finitePlaceMultiplicativeTamagawa F
private abbrev heckeFactor (ξ : PontryaginDual (normOneIdeleClass F)) :=
  heckeEulerFactor F (heckeEulerCoefficient F (normOneEulerCharacter F ξ) (chosenFiniteUniformizer F))

/-- The incomplete Hecke product omits all finite places of the chosen
stage, including its ramified places. -/
def weilIncompleteHeckeEuler (ξ : PontryaginDual (normOneIdeleClass F))
    (U : Finset (Place F)) (z : ℂ) : ℂ :=
  ∏' v : {v : Place F // v ∉ U}, heckeFactor F ξ v.val z

private theorem heckeFactor_hasProd (ξ : PontryaginDual (normOneIdeleClass F))
    (z : ℂ) (hz : 1 < z.re) :
    HasProd (fun v => heckeFactor F ξ v z) (globalFiniteHeckeEuler F ξ z) := by
  exact (heckeEulerProduct_hasProdUniformlyOn F _
    (norm_heckeEulerCoefficient_le_one F _ _) {z} isCompact_singleton
    (fun w hw => (mem_singleton_iff.mp hw).symm ▸ hz)).hasProd (mem_singleton z)

set_option maxHeartbeats 700000 in
theorem weilIncompleteHeckeEuler_eq_div (ξ : PontryaginDual (normOneIdeleClass F))
    (U : Finset (Place F)) (z : ℂ) (hz : 1 < z.re) :
    weilIncompleteHeckeEuler F ξ U z =
      globalFiniteHeckeEuler F ξ z / ∏ v ∈ U, heckeFactor F ξ v z := by
  let e (v : Place F) := heckeFactor F ξ v z
  have hs : Summable fun v : Place F => ‖e v - 1‖ :=
    (heckeEulerFactor_summableUniformlyOn F _ (norm_heckeEulerCoefficient_le_one F _ _)
      {z} isCompact_singleton (fun w hw => (mem_singleton_iff.mp hw).symm ▸ hz)).summable (mem_singleton z)
  have hm : Multipliable (fun v : {v : Place F // v ∉ U} => e v.val) := by
    simpa only [add_comm (1 : ℂ), sub_add_cancel] using
      multipliable_one_add_of_summable (hs.comp_injective
        (Subtype.val_injective (p := fun v : Place F => v ∉ U)))
  have hf := (Finset.hasProd U e).mul_compl hm.hasProd
  have he : (∏ v ∈ U, e v) * weilIncompleteHeckeEuler F ξ U z = globalFiniteHeckeEuler F ξ z :=
    hf.unique (heckeFactor_hasProd F ξ z hz)
  have hn : (∏ v ∈ U, e v) ≠ 0 := by
    intro h
    rw [h, zero_mul] at he
    exact (heckeEulerProduct_ne_zero F _ (norm_heckeEulerCoefficient_le_one F _ _) hz) he.symm
  exact (eq_div_iff hn).mpr ((mul_comm _ _).trans he)

private theorem selectedMass_mul_tail (U : Finset (Place F)) :
    (∏ v ∈ U, differentPrimeMass F v) * integralIdeleTailMass F U =
      (NNReal.sqrt ‖discr F‖₊ : ℝ≥0∞)⁻¹ := by
  rw [Finset.prod_subtype U (fun _ => Iff.rfl)]
  exact differentPrimeMass_split F U

private theorem paddingMass_eq_tail (U V : Finset (Place F)) (hUV : U ⊆ V)
    (hV : integralIdeleTailMass F V = 1) :
    sLocalMellinPaddingHaarMass F (localMeasure F) U V =
      ((integralIdeleTailMass F U).toReal : ℂ) := by
  let m : ℝ≥0∞ →* ℂ := Complex.ofRealHom.toMonoidHom.comp ENNReal.toRealHom.toMonoidHom
  have he : (∏ v ∈ U, differentPrimeMass F v) * (∏ v ∈ V \ U, differentPrimeMass F v) =
      (∏ v ∈ U, differentPrimeMass F v) * integralIdeleTailMass F U := by
    rw [mul_comm, Finset.prod_sdiff hUV, selectedMass_mul_tail F U,
      ← selectedMass_mul_tail F V, hV, mul_one]
  have hm := congrArg m he
  simp only [map_mul] at hm
  have hn : m (∏ v ∈ U, differentPrimeMass F v) ≠ 0 := by
    rw [map_prod]
    exact Finset.prod_ne_zero_iff.mpr fun v _ =>
      Complex.ofReal_ne_zero.mpr (ENNReal.toReal_ne_zero.mpr
        ⟨differentPrimeMass_ne_zero F v, differentPrimeMass_ne_top F v⟩)
  have ht := mul_left_cancel₀ hn hm
  rw [map_prod] at ht
  let e : {v : V // v.val ∉ U} ≃ (↑(V \ U) : Set (Place F)) :=
    { toFun := fun v => ⟨v.val.val, Finset.mem_sdiff.mpr ⟨v.val.property, v.property⟩⟩
      invFun := fun v => ⟨⟨v.val, (Finset.mem_sdiff.mp v.property).1⟩,
        (Finset.mem_sdiff.mp v.property).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  unfold sLocalMellinPaddingHaarMass
  change (∏ v : {v : V // v.val ∉ U}, ((localMeasure F v.val.val).real
    (finitePlaceIntegralUnits F v.val.val) : ℂ)) = m (integralIdeleTailMass F U)
  rw [← ht, Finset.prod_subtype (V \ U) (fun _ => Iff.rfl)]
  apply Fintype.prod_equiv e
  intro v
  rw [measureReal_def, localMeasure, finitePlaceMultiplicativeTamagawa_units]
  rfl

section OrdinaryZeta

variable (ξ : PontryaginDual (normOneIdeleClass F))
  (U : Finset (Place F)) (hU : Surjective (sIdeleClassInclusion F U))
  (hu : globalNormOneCharacter F ξ ∈ (sUnramified F U : Set (QuasiCharacter (IdeleClass F))))

private abbrev stageCharacter (V : Finset (Place F))
    (hV : Surjective (sIdeleClassInclusion F V))
    (hv : globalNormOneCharacter F ξ ∈ (sUnramified F V : Set (QuasiCharacter (IdeleClass F)))) :=
  sLocalNormOneCharacterOfGlobal F ξ V hV hv

private abbrev StageZeta (V : Finset (Place F)) (τ : PontryaginDual (SLocalThetaNormOne F V)) :=
  sLocalIdelicZetaIntegral F V (sLocalMultiplicativeTamagawa F V) τ

set_option maxHeartbeats 2400000 in
include hU hu in
/-- The ordinary global zeta integral is the ordinary selected-place
integral times the incomplete Hecke Euler product and the omitted Haar mass. -/
theorem weilOrdinaryGlobalZeta_eq_sLocal_mul_incomplete
    (g : sLocalBruhatImage F U) (z : ℂ) (hz : 1 < z.re) :
    (∫ a, globalMellinIntegrand F ξ g.val z a ∂globalIdeleTamagawa F) =
      ((integralIdeleTailMass F U).toReal : ℂ) *
      StageZeta F U (stageCharacter F ξ U hU hu) g z * weilIncompleteHeckeEuler F ξ U z := by
  let η := globalIdeleTamagawa F
  letI : η.IsHaarMeasure := globalIdeleTamagawa_isHaar F
  let Z := StageZeta F U (stageCharacter F ξ U hU hu) g z
  let a := ((integralIdeleTailMass F U).toReal : ℂ)
  have hp : 0 < z.re := zero_lt_one.trans hz
  have hint : Integrable (globalMellinIntegrand F ξ g.val z) η :=
    idelicZeta_integrable F η g.val _ (compactIdeleClassCharacter_unitary F ξ) z hz
  have hlim := globalIdeleTamagawa_integral_tendsto_blocks F hint
  obtain ⟨D, hD⟩ := globalIdeleTamagawa_eventually_noTailScale F
  have hblocks : (fun V : Finset (Place F) =>
      ∫ b in (sIdeleBlock F V : Set (Idele F)), globalMellinIntegrand F ξ g.val z b ∂η)
      =ᶠ[atTop] fun V => (a * Z) * ∏ v ∈ V \ U, heckeFactor F ξ v z := by
    filter_upwards [eventually_ge_atTop (U ∪ D)] with V hV
    have hUV : U ⊆ V := Finset.subset_union_left.trans hV
    have htail := (hD V (Finset.subset_union_right.trans hV)).2
    have hVsur := (hD V (Finset.subset_union_right.trans hV)).1
    have hv : globalNormOneCharacter F ξ ∈ (sUnramified F V : Set (QuasiCharacter (IdeleClass F))) :=
      (mem_sUnramified_iff F V _).mpr fun v h u =>
        (mem_sUnramified_iff F U _).mp hu v (fun h' => h (hUV h')) u
    let τ := stageCharacter F ξ V hVsur hv
    let gV := sLocalBruhatTransition F hUV g
    have hb := globalIdeleTamagawa_block_integral F V
      (globalMellinIntegrand F ξ g.val z) (sLocalIdelicZetaIntegrand F V τ z gV)
      (globalMellinIntegrand_on_block F ξ V hVsur hv gV z)
    have hL := sLocalProductZetaContinued_global_pad_right F ξ U hU hu (localMeasure F)
      hUV hVsur hv g z hp
    let κ := stageCharacter F ξ U hU hu
    change sLocalMellinPaddingDenominator F U (sLocalFiniteZetaPhases F V τ) z *
      sLocalProductZetaContinued F V (fun v => localMeasure F v.val) τ
        (sLocalRealArchParameters F V τ) (sLocalComplexArchParameters F V τ) gV z =
      sLocalMellinPaddingHaarMass F (localMeasure F) U V *
      sLocalProductZetaContinued F U (fun v => localMeasure F v.val) κ
        (sLocalRealArchParameters F U κ) (sLocalComplexArchParameters F U κ) g z at hL
    rw [(sLocalIdelicZeta_meromorphic_continuation F V (fun v => localMeasure F v.val) τ gV).2 hp,
      (sLocalIdelicZeta_meromorphic_continuation F U (fun v => localMeasure F v.val) κ g).2 hp,
      sLocalMellinPaddingDenominator_eq_heckeProduct F ξ U hu hVsur hv,
      paddingMass_eq_tail F U V hUV htail] at hL
    change (∏ v ∈ V \ U, heckeFactor F ξ v z)⁻¹ * StageZeta F V τ gV z = a * Z at hL
    have hne : (∏ v ∈ V \ U, heckeFactor F ξ v z) ≠ 0 := by
      intro he
      have hd : sLocalMellinPaddingDenominator F U (sLocalFiniteZetaPhases F V τ) z ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr fun v _ => finiteZetaDenominator_ne_zero_of_pos F
          v.val.val (sLocalFiniteZetaPhases F V τ v.val) z hp
      exact hd (by rw [sLocalMellinPaddingDenominator_eq_heckeProduct F ξ U hu hVsur hv, he, inv_zero])
    change _ = (integralIdeleTailMass F V).toReal • StageZeta F V τ gV z at hb
    rw [hb, htail, ENNReal.toReal_one, one_smul, ← hL]
    rw [mul_comm _ (∏ v ∈ V \ U, heckeFactor F ξ v z), ← mul_assoc, mul_inv_cancel₀ hne, one_mul]
  have hUe : (∏ v ∈ U, heckeFactor F ξ v z) ≠ 0 := by
    intro he
    have hc := sLocalFiniteZetaDenominator_eq_heckeProduct F ξ U hU hu z
    have hd : sLocalFiniteZetaDenominator F U
        (sLocalFiniteZetaPhases F U (stageCharacter F ξ U hU hu)) z ≠ 0 := by
      unfold sLocalFiniteZetaDenominator
      exact Finset.prod_ne_zero_iff.mpr fun v _ => by
        split_ifs
        · exact finiteZetaDenominator_ne_zero_of_pos F v.val _ z hp
        · exact one_ne_zero
    apply hd
    rw [hc, he, inv_zero]
  have hprod : Tendsto (fun V : Finset (Place F) => ∏ v ∈ V \ U, heckeFactor F ξ v z)
      atTop (𝓝 (weilIncompleteHeckeEuler F ξ U z)) := by
    rw [weilIncompleteHeckeEuler_eq_div F ξ U z hz]
    refine ((heckeFactor_hasProd F ξ z hz).div_const _).congr' ?_
    filter_upwards [eventually_ge_atTop U] with V hUV
    rw [div_eq_iff hUe, Finset.prod_sdiff hUV]
  exact tendsto_nhds_unique hlim ((tendsto_const_nhds.mul hprod).congr' hblocks.symm)

/-- The actual finite-place component of the global unitary character. -/
def globalWeilFinitePhase (v : Place F) : Phase F v :=
  (normOneEulerCharacter F ξ).comp (finitePlaceInsertion F v)

/-- The actual global character obtained by twisting the canonical unitary lift. -/
def weilTwistedGlobalCharacter (z : ℂ) : QuasiCharacter (IdeleClass F) where
  toFun q := (ideleNormTwist F (compactIdeleClassCharacter F ξ) z q : ℂ)
  map_one' := by simp
  map_mul' q r := by rw [map_mul]; rfl
  continuous_toFun := Units.continuous_val.comp
    (ideleNormTwist F (compactIdeleClassCharacter F ξ) z).continuous

theorem weilTwistedGlobalCharacter_unramified_iff (z : ℂ) :
    weilTwistedGlobalCharacter F ξ z ∈ (sUnramified F U : Set (QuasiCharacter (IdeleClass F))) ↔
      globalNormOneCharacter F ξ ∈ (sUnramified F U : Set (QuasiCharacter (IdeleClass F))) := by
  rw [mem_sUnramified_iff, mem_sUnramified_iff]
  apply forall_congr' fun v => imp_congr_right fun _ => forall_congr' fun a => ?_
  let b := Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom a
  have hb : b ∈ finitePlaceIntegralUnits F v := ⟨a.val.property, a.inv.property⟩
  have hb' : ‖b.val‖ = 1 := by
    rw [← finiteZetaShell_zero] at hb
    change ‖b.val‖ = (v.asIdeal.absNorm : ℝ) ^ (-(0 : ℤ)) at hb
    simpa only [neg_zero, zpow_zero] using hb
  let q := ideleClassMap F (singleFiniteIdele F v b)
  have hq : ideleClassNorm F q = 1 := by
    rw [show q = ideleClassMap F (singleFiniteIdele F v b) from rfl,
      ideleClassNorm_mk, singleFiniteIdele_norm, hb']
  change (globalNormOneCharacter F ξ q * ideleNormPower F z q = 1) ↔
    globalNormOneCharacter F ξ q = 1
  simp [ideleNormPower, hq]

include hu in
theorem globalWeilFinitePhase_unramified (v : Place F) (hv : v ∉ U) :
    finiteZetaUnramified F v (globalWeilFinitePhase F ξ v) := by
  intro a ha
  change a ∈ finitePlaceIntegralUnits F v at ha
  let x : (v.adicCompletionIntegers F)ˣ :=
    ⟨⟨a.val, ha.1⟩, ⟨a.inv, ha.2⟩, Subtype.ext a.val_inv, Subtype.ext a.inv_val⟩
  have hx : Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom x = a := Units.ext rfl
  apply Circle.ext
  change (normOneEulerCharacter F ξ (finitePlaceInsertion F v a) : ℂ) = 1
  rw [finitePlaceInsertion_apply, ← hx]
  exact (mem_sUnramified_iff F U (globalNormOneCharacter F ξ)).mp hu v hv x

omit ξ U in
/-- On compact families in the actual global quasi-character space, one
finite threshold works for every modified Euler product in the family. -/
theorem weilModifiedFiniteProduct_tendstoUniformly_compact
    {X : Type*} (ξX : X → PontryaginDual (normOneIdeleClass F)) (zX : X → ℂ)
    (hX : IsCompact (range fun x => weilTwistedGlobalCharacter F (ξX x) (zX x)))
    (k : ∀ v : Place F, Tests F v) (S₀ : Finset (Place F))
    (hk : ∀ v ∉ S₀, k v = finiteCompletionIntegerRingTest F v) :
    TendstoUniformly (fun U : Finset (Place F) => fun x =>
      ∏ v ∈ U, weilModifiedFiniteZeta F v (globalWeilFinitePhase F (ξX x) v) (k v) (zX x))
      (fun x => weilModifiedFiniteProduct F (globalWeilFinitePhase F (ξX x)) k (zX x)) atTop := by
  obtain ⟨R, hR⟩ := exists_common_unramified_stage_of_isCompact F _ hX
  apply weilModifiedFiniteProduct_tendstoUniformly F k (S₀ ∪ R)
  intro x v hv
  have hu := (weilTwistedGlobalCharacter_unramified_iff F (ξX x) R (zX x)).mp (hR (mem_range_self x))
  exact ⟨globalWeilFinitePhase_unramified F (ξX x) R hu v
    (fun h => hv (Finset.mem_union_right S₀ h)),
    hk v (fun h => hv (Finset.mem_union_left R h))⟩

theorem globalWeilFinitePhase_eq_stage (v : U) :
    sLocalFiniteZetaPhases F U (sLocalRestrictedNormOneCharacter F ξ U hu) v =
      globalWeilFinitePhase F ξ v.val := by
  ext a
  change (sLocalFiniteZetaPhases F U (sLocalRestrictedNormOneCharacter F ξ U hu) v a : ℂ) =
    (normOneEulerCharacter F ξ (finitePlaceInsertion F v.val a) : ℂ)
  rw [sLocalFiniteZetaPhases_of_global_restricted F U ξ hu v a, finitePlaceInsertion_apply]
  rfl

include hu in
theorem exists_exact_ramified_stage :
    ∃ R : Finset (Place F), R ⊆ U ∧
      globalNormOneCharacter F ξ ∈ (sUnramified F R : Set (QuasiCharacter (IdeleClass F))) ∧
      (∀ v ∈ R, ¬finiteZetaUnramified F v (globalWeilFinitePhase F ξ v)) := by
  let R := U.filter fun v => ¬finiteZetaUnramified F v (globalWeilFinitePhase F ξ v)
  refine ⟨R, Finset.filter_subset _ _, (mem_sUnramified_iff F R _).mpr ?_,
    fun v hv => (Finset.mem_filter.mp hv).2⟩
  intro v hv a
  have h : finiteZetaUnramified F v (globalWeilFinitePhase F ξ v) := by
    by_cases hvU : v ∈ U
    · by_contra hn
      exact hv (Finset.mem_filter.mpr ⟨hvU, hn⟩)
    · exact globalWeilFinitePhase_unramified F ξ U hu v hvU
  let b := Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom a
  have hb : b ∈ finitePlaceIntegralUnits F v := ⟨a.val.property, a.inv.property⟩
  have he : (globalWeilFinitePhase F ξ v b : ℂ) = 1 :=
    congrArg Subtype.val (h b hb)
  change (normOneEulerCharacter F ξ (finitePlaceInsertion F v b) : ℂ) = 1 at he
  rw [finitePlaceInsertion_apply] at he
  exact he

/-- Omitting ramified places from the Euler product does not change its
value, since their finite Euler factors are already one. -/
theorem weilIncompleteHeckeEuler_eq_full_of_ramified (R : Finset (Place F))
    (hram : ∀ v ∈ R, ¬finiteZetaUnramified F v (globalWeilFinitePhase F ξ v))
    (z : ℂ) (hz : 1 < z.re) :
    weilIncompleteHeckeEuler F ξ R z = globalFiniteHeckeEuler F ξ z := by
  rw [weilIncompleteHeckeEuler_eq_div F ξ R z hz]
  have he : (∏ v ∈ R, heckeFactor F ξ v z) = 1 := by
    apply Finset.prod_eq_one
    intro v hv
    have hn : ¬unramifiedFiniteCharacter F (normOneEulerCharacter F ξ) v := by
      intro h
      apply hram v hv
      intro u hu
      change u ∈ finitePlaceIntegralUnits F v at hu
      rw [← finiteZetaShell_zero] at hu
      have hu₁ : ‖u.val‖ = 1 := by
        change ‖u.val‖ = (v.asIdeal.absNorm : ℝ) ^ (-(0 : ℤ)) at hu
        simpa only [neg_zero, zpow_zero] using hu
      change normOneEulerCharacter F ξ (finitePlaceInsertion F v u) = 1
      rw [finitePlaceInsertion_apply]
      exact h u hu₁
    simp [heckeEulerFactor, heckeEulerCoefficient, hn]
  rw [he, div_one]

variable (j : ∀ v : Place F, Tests F v)
  (hj : ∀ v ∉ U, j v = finiteCompletionIntegerRingTest F v)
  (ψ : 𝓢(mixedEmbedding.mixedSpace F, ℂ))

set_option maxHeartbeats 1200000 in
include hu hj in
/-- Corrected (3.4.1.5). A stage that consists of the ramified finite
places contributes its ordinary S-local zeta factor. Every selected place
outside that stage contributes its modified factor. -/
theorem weilModifiedZeta_eq_ramified_stage
    (R : Finset (Place F)) (hRU : R ⊆ U)
    (hR : globalNormOneCharacter F ξ ∈ (sUnramified F R : Set (QuasiCharacter (IdeleClass F))))
    (hram : ∀ v ∈ R, ¬finiteZetaUnramified F v (globalWeilFinitePhase F ξ v))
    (z : ℂ) (hz : 0 < z.re) :
    weilModifiedZeta F (globalWeilFinitePhase F ξ) j U
      (sLocalRestrictedNormOneCharacter F ξ U hu) ψ z =
      ((integralIdeleTailMass F U).toReal : ℂ) *
        StageZeta F R (sLocalRestrictedNormOneCharacter F ξ R hR)
          (sLocalBruhatPure F R ψ (locallyConstantTestPiProduct fun v : R => j v.val)) z *
        ∏ v ∈ U \ R, weilModifiedFiniteZeta F v (globalWeilFinitePhase F ξ v) (j v) z := by
  let τU := sLocalRestrictedNormOneCharacter F ξ U hu
  let τR := sLocalRestrictedNormOneCharacter F ξ R hR
  let μ (v : R) := localMeasure F v.val
  haveI (v : R) : (μ v).IsHaarMeasure := finitePlaceMultiplicativeTamagawa_isHaar F v.val
  haveI (v : R) : SigmaFinite (μ v) := inferInstanceAs (SigmaFinite (localMeasure F v.val))
  let A V (τ : PontryaginDual (SLocalThetaNormOne F V)) :=
    sLocalArchZetaIntegral F V (archimedeanMultiplicativeHaar F) τ ψ z
  have hA : A U τU = A R τR := by
    unfold A sLocalArchZetaIntegral
    apply integral_congr_ae
    exact .of_forall fun a => by
      change sLocalZetaWeight F U (sLocalRestrictedNormOneCharacter F ξ U hu) z
        (QuotientGroup.mk (sLocalArchZetaInsert F U a)) *
        ψ (InfiniteAdeleRing.ringEquiv_mixedSpace F a.val) =
        sLocalZetaWeight F R (sLocalRestrictedNormOneCharacter F ξ R hR) z
          (QuotientGroup.mk (sLocalArchZetaInsert F R a)) *
          ψ (InfiniteAdeleRing.ringEquiv_mixedSpace F a.val)
      rw [sLocalZetaWeight_restricted_global_arch_apply F U ξ hu a z,
        sLocalZetaWeight_restricted_global_arch_apply F R ξ hR a z]
  let b v := weilModifiedFiniteZeta F v (globalWeilFinitePhase F ξ v) (j v) z
  have hRprod : (∏ v ∈ R, b v) =
      ∏ v : R, finiteZetaIntegral F v.val (μ v) (sLocalFiniteZetaPhases F R τR v) (j v.val) z := by
    rw [Finset.prod_subtype R (fun _ => Iff.rfl)]
    apply Finset.prod_congr rfl
    intro v _
    unfold b weilModifiedFiniteZeta
    rw [ite_eq_right (hram v.val v.property), globalWeilFinitePhase_eq_stage F ξ R hR v]
  change A U τU * weilModifiedFiniteProduct F (globalWeilFinitePhase F ξ) j z = _
  rw [hA, weilModifiedFiniteProduct_eq_stage F (globalWeilFinitePhase F ξ) j U
    (fun v hv => ⟨globalWeilFinitePhase_unramified F ξ U hu v hv, hj v hv⟩) z]
  change A R τR * (((integralIdeleTailMass F U).toReal : ℂ) * ∏ v ∈ U, b v) = _
  rw [← Finset.prod_sdiff hRU, hRprod]
  have hZ := sLocalIdelicZetaIntegral_pure_product F R μ (archimedeanMultiplicativeHaar F)
    τR ψ (fun v : R => j v.val) z hz
  change StageZeta F R τR _ z = A R τR * _ at hZ
  rw [hZ]
  ring

include hj in
/-- Corrected Weil identity. The modified product times the complete
finite Euler product recovers the ordinary global integral on its
absolute-convergence half-plane. -/
theorem weilModifiedZeta_mul_finiteHeckeEuler
    (z : ℂ) (hz : 1 < z.re) :
    weilModifiedZeta F (globalWeilFinitePhase F ξ) j U (stageCharacter F ξ U hU hu) ψ z *
      globalFiniteHeckeEuler F ξ z =
      ∫ a, globalMellinIntegrand F ξ
        (sLocalBruhatPure F U ψ (locallyConstantTestPiProduct fun v : U => j v.val)).val z a
        ∂globalIdeleTamagawa F := by
  let τ := stageCharacter F ξ U hU hu
  let μ (v : U) := localMeasure F v.val
  haveI (v : U) : (μ v).IsHaarMeasure :=
    finitePlaceMultiplicativeTamagawa_isHaar F v.val
  haveI (v : U) : SigmaFinite (μ v) := inferInstanceAs (SigmaFinite (localMeasure F v.val))
  let g := sLocalBruhatPure F U ψ (locallyConstantTestPiProduct fun v : U => j v.val)
  let P := ∏ v ∈ U, heckeFactor F ξ v z
  let d := sLocalFiniteZetaDenominator F U (sLocalFiniteZetaPhases F U τ) z
  have hp : 0 < z.re := zero_lt_one.trans hz
  have hd : d = P⁻¹ := sLocalFiniteZetaDenominator_eq_heckeProduct F ξ U hU hu z
  have he (v : U) : sLocalFiniteZetaPhases F U τ v = globalWeilFinitePhase F ξ v.val :=
    globalWeilFinitePhase_eq_stage F ξ U hu v
  have ht : ∀ v ∉ U, finiteZetaUnramified F v (globalWeilFinitePhase F ξ v) ∧
      j v = finiteCompletionIntegerRingTest F v :=
    fun v hv => ⟨globalWeilFinitePhase_unramified F ξ U hu v hv, hj v hv⟩
  change _ = ∫ a, globalMellinIntegrand F ξ g.val z a ∂globalIdeleTamagawa F
  rw [weilOrdinaryGlobalZeta_eq_sLocal_mul_incomplete F ξ U hU hu g z hz,
    weilIncompleteHeckeEuler_eq_div F ξ U z hz]
  unfold weilModifiedZeta
  rw [weilModifiedFiniteProduct_eq_stage F (globalWeilFinitePhase F ξ) j U ht z,
    Finset.prod_subtype U (fun _ => Iff.rfl)]
  simp only [← he, weilModifiedFiniteZeta_eq_multiplier F _ _ _ z hp, Finset.prod_mul_distrib]
  have hM : (∏ v : U, finiteZetaWeilMultiplier F v.val (sLocalFiniteZetaPhases F U τ v) z) = d := by
    unfold d sLocalFiniteZetaDenominator
    rfl
  rw [hM, hd]
  have hStage := sLocalIdelicZetaIntegral_pure_product F U μ (archimedeanMultiplicativeHaar F)
    τ ψ (fun v : U => j v.val) z hp
  change StageZeta F U τ g z = _ at hStage
  rw [hStage, div_eq_mul_inv]
  dsimp only [P, μ, localMeasure]
  ring

local instance : MeasurableSpace (normOneIdeleClass F) := borel _

set_option maxHeartbeats 1800000 in
include hj in
/-- The corrected factorization continues as a meromorphic germ. In the
positive half-plane the modified factor is given by its holomorphic integral
product, including at the pole of the trivial Hecke character. -/
theorem weilModifiedZeta_mul_finiteHeckeEuler_germ
    (ν : Measure (normOneIdeleClass F)) [ν.IsHaarMeasure]
    (hν : IsWeilQuotientMeasure (principalIdeles F) (globalIdeleTamagawa F)
      Measure.count (globalClassMeasure F ν))
    (L : ℂ → ℂ) (hL : MeromorphicOn L univ)
    (hLe : EqOn L (globalFiniteHeckeEuler F ξ) {z | 1 < z.re})
    (c : ℂ) (hc : 0 < c.re) :
    (fun z => weilModifiedZeta F (globalWeilFinitePhase F ξ) j U
      (stageCharacter F ξ U hU hu) ψ z * L z) =ᶠ[𝓝[≠] c]
      globalZetaContinued F ν
        (sLocalBruhatPure F U ψ (locallyConstantTestPiProduct fun v : U => j v.val)).val
        (compactIdeleClassCharacter F ξ) 0 := by
  let τ := stageCharacter F ξ U hU hu
  let g := sLocalBruhatPure F U ψ (locallyConstantTestPiProduct fun v : U => j v.val)
  let q := sLocalBruhatPure F U ψ (locallyConstantTestPiProduct fun v : U =>
    if finiteZetaUnramified F v.val (globalWeilFinitePhase F ξ v.val) then
      finitePrincipalValue (chosenFiniteUniformizer F v.val) (j v.val)
    else j v.val)
  let a := ((integralIdeleTailMass F U).toReal : ℂ)
  let Z := sLocalProductZetaContinued F U (fun v : U => localMeasure F v.val) τ
    (sLocalRealArchParameters F U τ) (sLocalComplexArchParameters F U τ) q
  let W : ℂ → ℂ := a • Z
  let G := globalZetaContinued F ν g.val (compactIdeleClassCharacter F ξ) 0
  let I (z : ℂ) := ∫ x, globalMellinIntegrand F ξ g.val z x ∂globalIdeleTamagawa F
  letI : (globalIdeleTamagawa F).IsHaarMeasure := globalIdeleTamagawa_isHaar F
  have hW : Meromorphic W :=
    (sLocalIdelicZeta_meromorphic_continuation F U (fun v : U => localMeasure F v.val) τ q).1.const_smul a
  have hEq (z : ℂ) (hz : 0 < z.re) :
      W z = weilModifiedZeta F (globalWeilFinitePhase F ξ) j U τ ψ z := by
    change a * Z z = _
    have hZ : Z z = StageZeta F U τ q z :=
      (sLocalIdelicZeta_meromorphic_continuation F U (fun v : U => localMeasure F v.val) τ q).2 hz
    rw [hZ]
    exact (weilModifiedZeta_eq_sLocal F (globalWeilFinitePhase F ξ) j U
      (fun v hv => ⟨globalWeilFinitePhase_unramified F ξ U hu v hv, hj v hv⟩)
      τ (globalWeilFinitePhase_eq_stage F ξ U hu) ψ z hz).symm
  have hG : MeromorphicOn G univ :=
    globalZetaContinued_meromorphic F ν g.val _ (compactIdeleClassCharacter_unitary F ξ) 0
  have hGI : EqOn G I {z | 1 < z.re} := by
    intro z hz
    exact globalZetaContinued_eq_idelic F (globalIdeleTamagawa F) ν hν g.val
      (compactIdeleClassCharacter F ξ) (compactIdeleClassCharacter_unitary F ξ)
      (κ := 0) Complex.zero_re (fun t => by simp) z hz
  have hWL : EqOn (W * L) I {z | 1 < z.re} := by
    intro z hz
    change W z * L z = I z
    rw [hEq z (zero_lt_one.trans hz), hLe hz]
    exact weilModifiedZeta_mul_finiteHeckeEuler F ξ U hU hu j hj ψ z hz
  have hg := globalHeckeContinuation_unique_germ (hW.meromorphicOn.mul hL) hG hWL hGI c
  have hn₀ : ∀ᶠ z : ℂ in 𝓝 c, 0 < z.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hc
  have hn : ∀ᶠ z : ℂ in 𝓝[≠] c, 0 < z.re := hn₀.filter_mono nhdsWithin_le_nhds
  filter_upwards [hg, hn] with z hg hz
  change W z * L z = G z at hg
  rw [hEq z hz] at hg
  exact hg

end OrdinaryZeta
end
end Masullo
