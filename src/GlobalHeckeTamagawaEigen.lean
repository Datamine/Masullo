import HeckeTensorFactors
import WeilModifiedZeta

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical ENNReal NNReal NumberField SchwartzMap

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

private abbrev Place := HeightOneSpectrum (𝓞 F)
private abbrev Local (v : Place F) := v.adicCompletion F
private abbrev K := normOneIdeleClass F
private abbrev Arch := (InfiniteAdeleRing F)ˣ

local instance : MeasurableSpace (Idele F) := borel _
local instance : BorelSpace (Idele F) := ⟨rfl⟩
local instance : MeasurableSpace (K F) := borel _
local instance : MeasurableSpace (Arch F) := borel _
local instance : BorelSpace (Arch F) := ⟨rfl⟩
local instance (v : Place F) : MeasurableSpace (Local F v) := borel _
local instance (v : Place F) : BorelSpace (Local F v) := ⟨rfl⟩
local instance (v : Place F) : MeasurableSpace (Local F v)ˣ := borel _
local instance (v : Place F) : BorelSpace (Local F v)ˣ := ⟨rfl⟩
private abbrev μ (v : Place F) := finitePlaceMultiplicativeTamagawa F v
local instance (v : Place F) : LocallyCompactSpace (Local F v) := finitePlace_locallyCompact F v
local instance (v : Place F) : SecondCountableTopology (Local F v) := finitePlace_secondCountable F v
local instance (v : Place F) : LocallyCompactSpace (Local F v)ˣ :=
  IsOpenUnits.isOpenEmbedding_unitsVal.locallyCompactSpace
local instance (v : Place F) : SecondCountableTopology (Local F v)ˣ :=
  Units.isEmbedding_val₀.secondCountableTopology
local instance (v : Place F) : (μ F v).IsHaarMeasure := finitePlaceMultiplicativeTamagawa_isHaar F v
local instance (v : Place F) : SigmaFinite (μ F v) := inferInstance
local instance (S : Finset (Place F)) : MeasurableSpace (SAdeles F S)ˣ := borel _
local instance (S : Finset (Place F)) : BorelSpace (SAdeles F S)ˣ := ⟨rfl⟩
local instance : (globalIdeleTamagawa F).IsHaarMeasure := globalIdeleTamagawa_isHaar F

/-- The product of all the finite integral-unit masses, expressed as a
complex scalar for the normalized Mellin distributions. -/
def globalWeilTamagawaScale : ℂ := ((↑(NNReal.sqrt ‖discr F‖₊) : ℂ))⁻¹

theorem globalWeilTamagawaScale_ne_zero : globalWeilTamagawaScale F ≠ 0 := by
  apply inv_ne_zero
  exact Complex.ofReal_ne_zero.mpr (by
    rw [Real.coe_sqrt, coe_nnnorm]
    exact (Real.sqrt_pos.2 (norm_pos_iff.mpr (discr_ne_zero F))).ne')

private def selectedUnitMass (S : Finset (Place F)) : ℂ :=
  ∏ v : S, ((μ F v.val).real (finitePlaceIntegralUnits F v.val) : ℂ)

private theorem tail_mul_selectedUnitMass (S : Finset (Place F)) :
    ((integralIdeleTailMass F S).toReal : ℂ) * selectedUnitMass F S = globalWeilTamagawaScale F := by
  let m : ℝ≥0∞ →* ℂ := Complex.ofRealHom.toMonoidHom.comp ENNReal.toRealHom.toMonoidHom
  have h := congrArg m (differentPrimeMass_split F S)
  change m ((∏ v : S, differentPrimeMass F v.val) * integralIdeleTailMass F S) = _ at h
  simp only [map_mul, map_prod] at h
  have he (v : S) :
      m (differentPrimeMass F v.val) = ((μ F v.val).real (finitePlaceIntegralUnits F v.val) : ℂ) := by
    rw [measureReal_def, μ, finitePlaceMultiplicativeTamagawa_units]
    rfl
  unfold selectedUnitMass
  rw [← mul_comm]
  simp_rw [← he]
  apply h.trans
  change (((((↑(NNReal.sqrt ‖discr F‖₊) : ℝ≥0∞)⁻¹).toReal : ℝ) : ℂ)) = _
  rw [ENNReal.toReal_inv, ENNReal.coe_toReal, Complex.ofReal_inv]
  rfl

variable (ω : PontryaginDual (K F)) (S : Finset (Place F))
  (hs : Surjective (sIdeleClassInclusion F S))
  (hu : globalNormOneCharacter F ω ∈ (sUnramified F S : Set (QuasiCharacter (IdeleClass F))))

private abbrev τ := sLocalNormOneCharacterOfGlobal F ω S hs hu

set_option maxHeartbeats 1800000 in
/-- On the convergence half-plane the ordinary global zeta integral gives
the exact Tamagawa factor multiplying the unit-normalized stage numerator. -/
theorem globalWeilTamagawa_integral_eq_normalizedStage
    (f : sLocalBruhatImage F S) (z : ℂ) (hz : 1 < z.re) :
    (∫ a, globalMellinIntegrand F ω f.val z a ∂globalIdeleTamagawa F) =
      globalCompletedHeckeEuler F ω S hs hu z *
        (globalWeilTamagawaScale F * normalizedStageWeilMellin F (μ F) ω S hs hu f z) := by
  let σ := τ F ω S hs hu
  let P := ∏ v ∈ S, heckeEulerFactor F
    (heckeEulerCoefficient F (normOneEulerCharacter F ω) (chosenFiniteUniformizer F)) v z
  let A := archimedeanNumberFieldZetaDenominator F
    (sLocalRealArchParameters F S σ) (sLocalComplexArchParameters F S σ) z
  let Z := sLocalIdelicZetaIntegral F S (sLocalMultiplicativeTamagawa F S) σ f
  let M := selectedUnitMass F S
  let t := ((integralIdeleTailMass F S).toReal : ℂ)
  let D := sLocalEulerDenominator F S σ
  let N := sLocalEulerNormalizedMellin F S (fun v : S => μ F v.val) σ f
  let Zc := sLocalProductZetaContinued F S (fun v : S => μ F v.val) σ
    (sLocalRealArchParameters F S σ) (sLocalComplexArchParameters F S σ) f
  have hp : 0 < z.re := zero_lt_one.trans hz
  have hDe : D z = A * P⁻¹ := by
    unfold D sLocalEulerDenominator
    rw [sLocalFiniteZetaDenominator_eq_heckeProduct F ω S hs hu z]
  have hD := sLocalEulerDenominator_ne_zero_of_pos F S σ hp
  have hA : A ≠ 0 := fun h =>
    hD (by change D z = 0; rw [hDe, h, zero_mul])
  have hN : N z = D z * Z z := by
    have hcont : ContinuousAt (fun w => D w * Zc w) z :=
      (sLocalEulerDenominator_analytic F S σ z).continuousAt.mul
        (sLocalProductZetaContinued_continuousAt_pos F (μ F) S σ f z hp)
    have he := sLocalEulerNormalizedMellin_eq_germ F S (fun v : S => μ F v.val) σ f z
    change N =ᶠ[𝓝[≠] z] fun w => D w * Zc w at he
    have hnc : ContinuousAt N z :=
      (sLocalEulerNormalizedMellin_entire F S (fun v : S => μ F v.val) σ f z trivial).continuousAt
    have hh := ((hnc.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE hcont).mp he).eq_of_nhds
    have hZ : Zc z = Z z :=
      (sLocalIdelicZeta_meromorphic_continuation F S (fun v : S => μ F v.val) σ f).2 hp
    change N z = D z * Zc z at hh
    rwa [hZ] at hh
  have htM : t * M = globalWeilTamagawaScale F := tail_mul_selectedUnitMass F S
  have hM : M ≠ 0 := fun h => globalWeilTamagawaScale_ne_zero F (htM.symm.trans (by rw [h, mul_zero]))
  rw [weilOrdinaryGlobalZeta_eq_sLocal_mul_incomplete F ω S hs hu f z hz,
    weilIncompleteHeckeEuler_eq_div F ω S z hz]
  change t * Z z * (globalFiniteHeckeEuler F ω z / P) =
    (A⁻¹ * globalFiniteHeckeEuler F ω z) * (globalWeilTamagawaScale F * (M⁻¹ * N z))
  rw [hN, hDe, ← htM, div_eq_mul_inv]
  field_simp

/-- The common scalar of Theorem 3.4.3.3 is the reciprocal square root of
the absolute discriminant with the prescribed Tamagawa measures. -/
theorem globalNormalizedHeckeFamily_tamagawa_stages
    (ν : Measure (K F)) [ν.IsHaarMeasure]
    (hν : IsWeilQuotientMeasure (principalIdeles F) (globalIdeleTamagawa F) Measure.count
      (globalClassMeasure F ν))
    (L : ℂ → ℂ) (hL : MeromorphicOn L univ)
    (hEq : EqOn L (globalCompletedHeckeEuler F ω S hs hu) {z | 1 < z.re})
    (Δ : ℂ → StrongDual ℂ (GlobalBruhat F)) (hΔ : Continuous Δ)
    (hfac : ∀ c, globalContinuedMellinEval F ν ω =ᶠ[𝓝[≠] c] fun z => L z • Δ z) :
    ∀ (T : Finset (Place F)) (ht : Surjective (sIdeleClassInclusion F T))
      (huT : globalNormOneCharacter F ω ∈ (sUnramified F T : Set (QuasiCharacter (IdeleClass F))))
      (f : sLocalBruhatImage F T) (z : ℂ),
      Δ z f.val = globalWeilTamagawaScale F * normalizedStageWeilMellin F (μ F) ω T ht huT f z := by
  obtain ⟨B, _, hB⟩ := globalNormalizedHeckeFamily_compatible_stages F S (μ F)
    (globalIdeleTamagawa F) ν hν ω hs hu L hL hEq Δ hΔ hfac
  obtain ⟨r, C, hC, hr, _, _⟩ := exists_globalMellin_order_reference F
    (globalIdeleTamagawa F) ω S hs hu (μ F) ν hν
  have hn (z : ℂ) : normalizedStageWeilMellin F (μ F) ω S hs hu r z ≠ 0 := by
    unfold normalizedStageWeilMellin
    change (selectedUnitMass F S)⁻¹ *
      sLocalEulerNormalizedMellin F S (fun v : S => μ F v.val) (τ F ω S hs hu) r z ≠ 0
    have hr' : sLocalEulerNormalizedMellin F S (fun v : S => μ F v.val)
      (τ F ω S hs hu) r z = C := congrFun hr z
    rw [hr']
    have hM : selectedUnitMass F S ≠ 0 := by
      intro h
      have he := tail_mul_selectedUnitMass F S
      rw [h, mul_zero] at he
      exact globalWeilTamagawaScale_ne_zero F he.symm
    exact mul_ne_zero (inv_ne_zero hM) hC
  have hpos : ∀ᶠ z : ℂ in 𝓝 (2 : ℂ), 1 < z.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  have he : ∀ᶠ z : ℂ in 𝓝[≠] (2 : ℂ), B = globalWeilTamagawaScale F := by
    filter_upwards [hpos.filter_mono nhdsWithin_le_nhds, hfac 2] with z hz hg
    have hzeta := globalZetaContinued_eq_idelic F (globalIdeleTamagawa F) ν hν r.val
      (compactIdeleClassCharacter F ω) (compactIdeleClassCharacter_unitary F ω)
      (κ := 0) Complex.zero_re (fun _ => by simp) z hz
    change globalZetaContinued F ν r.val (compactIdeleClassCharacter F ω) 0 z =
      (∫ a, globalMellinIntegrand F ω r.val z a ∂globalIdeleTamagawa F) at hzeta
    have hval := (globalContinuedMellinEval_apply F ν ω z r.val).symm.trans
      (DFunLike.congr_fun hg r.val)
    change globalZetaContinued F ν r.val (compactIdeleClassCharacter F ω) 0 z = L z * Δ z r.val at hval
    rw [hzeta, globalWeilTamagawa_integral_eq_normalizedStage F ω S hs hu r z hz,
      hEq hz, hB S hs hu r z] at hval
    exact (mul_right_cancel₀ (hn z)
      (mul_left_cancel₀ (globalCompletedHeckeEuler_ne_zero F ω S hs hu hz) hval)).symm
  rw [← he.exists.choose_spec]
  exact hB

/-- On a separated adelic test the global distribution is the product of
the normalized local evaluations with the exact Tamagawa scalar. -/
theorem globalNormalizedHeckeFamily_tamagawa_tensor
    (ν : Measure (K F)) [ν.IsHaarMeasure]
    (hν : IsWeilQuotientMeasure (principalIdeles F) (globalIdeleTamagawa F) Measure.count
      (globalClassMeasure F ν))
    (L : ℂ → ℂ) (hL : MeromorphicOn L univ)
    (hEq : EqOn L (globalCompletedHeckeEuler F ω S hs hu) {z | 1 < z.re})
    (Δ : ℂ → StrongDual ℂ (GlobalBruhat F)) (hΔ : Continuous Δ)
    (hfac : ∀ c, globalContinuedMellinEval F ν ω =ᶠ[𝓝[≠] c] fun z => L z • Δ z)
    (T : Finset (Place F)) (ht : Surjective (sIdeleClassInclusion F T))
    (huT : globalNormOneCharacter F ω ∈ (sUnramified F T : Set (QuasiCharacter (IdeleClass F))))
    (φ : 𝓢(mixedEmbedding.mixedSpace F, ℂ))
    (f : {v : InfinitePlace F // v.IsReal} → 𝓢(ℝ, ℂ))
    (g : {v : InfinitePlace F // v.IsComplex} → 𝓢(ℂ, ℂ))
    (hφ : ∀ x : mixedEmbedding.mixedSpace F, φ x = (∏ v, f v (x.1 v)) * ∏ v, g v (x.2 v))
    (k : ∀ v : T, locallyConstantTests (v.val.adicCompletion F)) (z : ℂ) :
    let σ := sLocalNormOneCharacterOfGlobal F ω T ht huT
    Δ z (sLocalBruhatPure F T φ (locallyConstantTestPiProduct k)).val =
      globalWeilTamagawaScale F * (sLocalNormalizedArchWeilTensor F T σ f g z *
        ∏ v : T, finiteWeilNormalizedDistribution F v.val (μ F v.val)
          (sLocalFiniteZetaPhases F T σ v) z (k v)) := by
  intro σ
  rw [globalNormalizedHeckeFamily_tamagawa_stages F ω S hs hu ν hν L hL hEq Δ hΔ hfac T ht huT,
    normalizedStageWeilMellin_separated_eval F T (μ F) ω ht huT φ f g hφ k z]

set_option maxHeartbeats 2200000 in
/-- With the discriminant included in the completed Euler function, the
normalized global distribution has exactly the unit-normalized local
values. This is the normalization by the global reference test. -/
theorem exists_globalWeilTamagawa_eigenfamily
    (ν : Measure (K F)) [ν.IsHaarMeasure]
    (hν : IsWeilQuotientMeasure (principalIdeles F) (globalIdeleTamagawa F) Measure.count
      (globalClassMeasure F ν)) :
    ∃ (r : GlobalBruhat F) (L : ℂ → ℂ) (Δ : ℂ → StrongDual ℂ (GlobalBruhat F)),
      EqOn L (fun z => globalWeilTamagawaScale F * globalCompletedHeckeEuler F ω S hs hu z)
        {z | 1 < z.re} ∧
      MeromorphicOn L univ ∧ Differentiable ℂ Δ ∧
      (∀ z, Δ z r = 1) ∧
      (∀ z, globalContinuedMellinEval F ν ω =ᶠ[𝓝[≠] z] fun w => L w • Δ w) ∧
      (∀ z, globalZetaContinued F ν r (compactIdeleClassCharacter F ω) 0 =ᶠ[𝓝[≠] z] L) ∧
      (∀ (g : Idele F) (f : GlobalBruhat F) (z : ℂ),
        Δ z (GlobalBruhat.leftTranslate F g f) =
          (ideleNormTwist F (compactIdeleClassCharacter F ω) z (ideleClassMap F g) : ℂ) * Δ z f) ∧
      ∀ (T : Finset (Place F)) (ht : Surjective (sIdeleClassInclusion F T))
        (huT : globalNormOneCharacter F ω ∈ (sUnramified F T : Set (QuasiCharacter (IdeleClass F))))
        (f : sLocalBruhatImage F T) (z : ℂ),
        Δ z f.val = normalizedStageWeilMellin F (μ F) ω T ht huT f z := by
  obtain ⟨r, L, Δ, hEq, hL, hΔ, hr, hfac, hcov⟩ :=
    exists_globalNormalizedHeckeFamily F ν ω (globalIdeleTamagawa F) (μ F) hν S hs hu
  let b := globalWeilTamagawaScale F
  let r' := b • r
  let L' (z : ℂ) := b * L z
  let Δ' (z : ℂ) := b⁻¹ • Δ z
  have hb : b ≠ 0 := globalWeilTamagawaScale_ne_zero F
  have hstage := globalNormalizedHeckeFamily_tamagawa_stages F ω S hs hu
    ν hν L hL hEq Δ hΔ.continuous hfac
  have hr' (z : ℂ) : Δ' z r' = 1 := by
    change b⁻¹ * Δ z (b • r) = 1
    rw [map_smul, smul_eq_mul, hr, mul_one, inv_mul_cancel₀ hb]
  have hfac' (z : ℂ) :
      globalContinuedMellinEval F ν ω =ᶠ[𝓝[≠] z] fun w => L' w • Δ' w := by
    filter_upwards [hfac z] with w hw
    rw [hw]
    apply LinearMap.ext
    intro f
    change L w * Δ w f = (b * L w) * (b⁻¹ * Δ w f)
    rw [mul_comm b, mul_assoc, ← mul_assoc b b⁻¹, mul_inv_cancel₀ hb, one_mul]
  have hΔ' : Differentiable ℂ Δ' := by
    let M := b⁻¹ • ContinuousLinearMap.id ℂ (StrongDual ℂ (GlobalBruhat F))
    change Differentiable ℂ (M ∘ Δ)
    intro z
    obtain ⟨D, hD⟩ := hΔ z
    refine ⟨M.comp D, HasFDerivAt.of_isLittleOTVS ?_⟩
    simpa only [Function.comp_def, ContinuousLinearMap.comp_apply, map_sub]
      using M.isBigOTVS_comp.trans_isLittleOTVS hD.isLittleOTVS
  refine ⟨r', L', Δ', fun z hz => congrArg (b * ·) (hEq hz),
    fun z hz => (MeromorphicAt.const b z).mul (hL z hz),
    hΔ', hr', hfac', ?_, ?_, ?_⟩
  · intro z
    filter_upwards [hfac' z] with w hw
    have he := DFunLike.congr_fun hw r'
    change globalContinuedMellinEval F ν ω w r' = L' w * Δ' w r' at he
    rw [hr', mul_one] at he
    exact (globalContinuedMellinEval_apply F ν ω w r').symm.trans he
  · intro g f z
    change b⁻¹ * Δ z (GlobalBruhat.leftTranslate F g f) = _
    rw [hcov]
    change b⁻¹ * (_ * Δ z f) = _ * (b⁻¹ * Δ z f)
    rw [mul_left_comm]
  · intro T ht huT f z
    change b⁻¹ * Δ z f.val = _
    rw [hstage T ht huT f z, ← mul_assoc, inv_mul_cancel₀ hb, one_mul]

end
end Masullo
