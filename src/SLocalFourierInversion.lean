import SLocalFourierTail
import FiniteLogFourierHaar
import LocallyConstantProduct

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical ENNReal NNReal NumberField RestrictedProduct SchwartzMap

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]
variable (S : Finset (HeightOneSpectrum (𝓞 F)))

private abbrev E := sLocalBruhatImage F S
private abbrev X := mixedEmbedding.mixedSpace F
private abbrev K (v : S) := v.val.adicCompletion F

private theorem sLocalBruhatPad_eq_arch_add_sum (x ξ : SAdeles F S) :
    sLocalBruhatPad F S (x * ξ) =
      archAdele F (infiniteAdeleMixedHomeomorph F x.1) * sLocalBruhatPad F S ξ +
        ∑ v : S, finitePlaceAdditiveInsert F v.val (x.2 v * ξ.2 v) := by
  let arch : Adeles F →+* InfiniteAdeleRing F := RingHom.fst _ _
  let fin : Adeles F →+* FiniteAdeleRing (𝓞 F) F := RingHom.snd _ _
  apply Prod.ext
  · change x.1 * ξ.1 = arch (_ + _)
    rw [map_add arch, map_sum arch]
    have he (v : S) : arch (finitePlaceAdditiveInsert F v.val (x.2 v * ξ.2 v)) = 0 := rfl
    simp only [he, Finset.sum_const_zero, add_zero]
    change x.1 * ξ.1 =
      (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm
        ((InfiniteAdeleRing.ringEquiv_mixedSpace F) x.1) * ξ.1
    rw [RingEquiv.symm_apply_apply]
  · apply RestrictedProduct.ext
    intro w
    let ev := (RestrictedProduct.evalRingHom (fun v : HeightOneSpectrum (𝓞 F) ↦
      v.adicCompletion F) w).comp fin
    change _ = ev (_ + _)
    rw [map_add ev, map_sum ev]
    change (sLocalBruhatPad F S (x * ξ)).2 w = 0 * (sLocalBruhatPad F S ξ).2 w + _
    rw [zero_mul, zero_add]
    by_cases hw : w ∈ S
    · let u : S := ⟨w, hw⟩
      rw [Finset.sum_eq_single_of_mem u (Finset.mem_univ u)]
      · exact (sLocalBruhatPad_finite F S (x * ξ) u).trans
          (finitePlaceAdditiveInsert_finite_apply_self F u.val _).symm
      · intro v _ hv
        exact finitePlaceAdditiveInsert_finite_apply_ne F v.val
          (fun h ↦ hv (Subtype.ext h.symm)) _
    · have he (v : S) : ev (finitePlaceAdditiveInsert F v.val (x.2 v * ξ.2 v)) = 0 :=
        finitePlaceAdditiveInsert_finite_apply_ne F v.val
          (fun h : w = v.val ↦ hw (by rw [h]; exact v.property)) _
      simp only [he, Finset.sum_const_zero]
      change (finiteCoordinateSplit F S ((x * ξ).2, 0)) w = 0
      rw [finiteCoordinateSplit_apply, dite_eq_right hw]
      rfl

theorem sLocalFourier_phase_factor (x ξ : SAdeles F S) :
    ((standardAdelicCharacter F (sLocalBruhatPad F S (x * ξ))).toMul : ℂ) =
      ((standardAdelicCharacter F
        (archAdele F (infiniteAdeleMixedHomeomorph F x.1) * sLocalBruhatPad F S ξ)).toMul : ℂ) *
      ∏ v : S, ((finitePlaceTraceCharacter F v.val (x.2 v * ξ.2 v)).toMul : ℂ) := by
  rw [sLocalBruhatPad_eq_arch_add_sum, map_add, map_sum, toMul_add, toMul_sum, Circle.coe_mul]
  exact congrArg (_ * ·) (map_prod Circle.coeHom _ Finset.univ)

local instance : MeasurableSpace (InfiniteAdeleRing F) := borel _
local instance : BorelSpace (InfiniteAdeleRing F) := ⟨rfl⟩
local instance (v : HeightOneSpectrum (𝓞 F)) : MeasurableSpace (v.adicCompletion F) := borel _
local instance (v : HeightOneSpectrum (𝓞 F)) : BorelSpace (v.adicCompletion F) := ⟨rfl⟩
local instance (v : HeightOneSpectrum (𝓞 F)) : (additiveHaarDifferent F v).IsAddHaarMeasure :=
  additiveHaarDifferent_isHaar F v

set_option maxHeartbeats 900000 in
/-- On a separated tensor the compressed Fourier integral is the product
of the actual local transforms, times a fixed nonzero Haar scalar. -/
theorem exists_sLocalFourierCompression_pure_factor :
    ∃ (c : ℂ) (T : 𝓢(X F, ℂ) →L[ℂ] 𝓢(X F, ℂ)), c ≠ 0 ∧ IsHomeomorph T ∧
      ∀ (φ : 𝓢(X F, ℂ)) (g : ∀ v : S, locallyConstantTests (K F S v)) (ξ : SAdeles F S),
        sLocalBruhatRestriction F S
          (sLocalFourierCompression F S (sLocalBruhatPure F S φ (locallyConstantTestPiProduct g))).val ξ =
          c * (T φ (infiniteAdeleMixedHomeomorph F ξ.1) *
            ∏ v : S, (finitePlaceFourierTest F v.val (additiveHaarDifferent F v.val) (g v)).val (ξ.2 v)) := by
  obtain ⟨T, hT, hEval⟩ := exists_archAdelicFourier_homeomorph F
  let μ (v : S) := additiveHaarDifferent F v.val
  letI (v : S) : (μ v).IsAddHaarMeasure := additiveHaarDifferent_isHaar F v.val
  letI (v : S) : SigmaFinite (μ v) := by
    letI : SecondCountableTopology (K F S v) := finitePlace_secondCountable F v.val
    letI : LocallyCompactSpace (K F S v) := finitePlace_locallyCompact F v.val
    infer_instance
  let e := (infiniteAdeleMixedHomeomorph F).symm
  letI : SecondCountableTopology (InfiniteAdeleRing F) := e.symm.isEmbedding.secondCountableTopology
  let eM := e.toMeasurableEquiv
  letI : SFinite (archAdditiveTamagawa F) := by
    unfold archAdditiveTamagawa
    infer_instance
  let m (v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S}) := differentPrimeMass F v.val
  let tailMass : ℝ≥0∞ := ∏ᶠ v, m v
  let b : ℝ≥0 := 2 ^ InfinitePlace.nrComplexPlaces F
  have hfin : m.HasFiniteMulSupport :=
    (differentPrimeMass_finite F).preimage Subtype.val_injective.injOn
  have hTail : 0 < tailMass.toReal := ENNReal.toReal_pos
    (finprod_ne_zero fun v ↦ differentPrimeMass_ne_zero F v.val)
    (by rw [show tailMass = _ from finprod_eq_prod m hfin]
        exact ENNReal.prod_ne_top fun v _ ↦ differentPrimeMass_ne_top F v.val)
  have hb : (0 : ℝ) < b := by
    dsimp [b]
    positivity
  refine ⟨(tailMass.toReal : ℂ) * (b : ℝ), T,
    mul_ne_zero (Complex.ofReal_ne_zero.mpr hTail.ne') (Complex.ofReal_ne_zero.mpr hb.ne'), hT,
    fun φ g ξ ↦ ?_⟩
  let W (x : InfiniteAdeleRing F) := φ (e.symm x) *
    ((standardAdelicCharacter F (archAdele F (e.symm x) * sLocalBruhatPad F S ξ)).toMul : ℂ)
  let U (v : S) (x : K F S v) := (g v).val x *
    ((finitePlaceTraceCharacter F v.val (x * ξ.2 v)).toMul : ℂ)
  rw [sLocalFourierCompression_restrict, sLocalFourierCompressionMeasure, integral_smul_measure,
    sLocalAdditiveProduct]
  have hSplit (x : SAdeles F S) :
      sLocalBruhatRestriction F S (sLocalBruhatPure F S φ (locallyConstantTestPiProduct g)).val x *
        ((standardAdelicCharacter F (sLocalBruhatPad F S (x * ξ))).toMul : ℂ) =
        W x.1 * ∏ v : S, U v (x.2 v) := by
    rw [sLocalBruhatPure_restrict, locallyConstantTestPiProduct_apply, sLocalFourier_phase_factor]
    change (_ * _) * (_ * _) = _ * ∏ v : S, (g v).val (x.2 v) * _
    rw [Finset.prod_mul_distrib]
    unfold W
    ac_rfl
  simp_rw [hSplit]
  have hFubini := integral_prod_mul (μ := Measure.map e (archAdditiveTamagawa F))
    (ν := Measure.pi μ) W (fun x ↦ ∏ v : S, U v (x v))
  erw [hFubini, integral_fintype_prod_eq_prod]
  have hArch : (∫ x, W x ∂Measure.map e (archAdditiveTamagawa F)) =
      (b : ℝ) • T φ (e.symm ξ.1) := by
    change (∫ x, W x ∂Measure.map eM (archAdditiveTamagawa F)) = _
    rw [integral_map_equiv, archAdditiveTamagawa, integral_smul_nnreal_measure]
    change (b : ℝ) • (∫ x : X F, W (e x)) = (b : ℝ) • T φ (e.symm ξ.1)
    simp only [W, Homeomorph.symm_apply_apply]
    exact congrArg ((b : ℝ) • ·) (hEval φ (sLocalBruhatPad F S ξ))
  change tailMass.toReal • ((∫ x, W x ∂Measure.map e (archAdditiveTamagawa F)) *
      ∏ v : S, ∫ x, U v x ∂μ v) = _
  rw [hArch, Complex.real_smul, Complex.real_smul]
  change _ = _ * (T φ (e.symm ξ.1) * ∏ v : S, ∫ x, U v x ∂μ v)
  ring

private theorem sLocalBruhat_ext_of_restrict {f g : E F S}
    (h : ∀ x, sLocalBruhatRestriction F S f.val x = sLocalBruhatRestriction F S g.val x) :
    f = g := by
  apply Subtype.ext
  apply (GlobalBruhat.algebraicEquiv F).injective
  apply Subtype.ext
  funext x
  change GlobalBruhat.evaluation F x f.val = GlobalBruhat.evaluation F x g.val
  rw [sLocalBruhatRestriction_reconstruct F S f, sLocalBruhatRestriction_reconstruct F S g, h]

/-- The compressed Fourier integral has exact test-level preimages on
every finite stage, including stages omitting part of the different. -/
theorem sLocalFourierCompression_surjective : Surjective (sLocalFourierCompression F S) := by
  let C := sLocalFourierCompression F S
  obtain ⟨c, T, hc, hT, hFact⟩ := exists_sLocalFourierCompression_pure_factor F S
  have hp (φ : 𝓢(X F, ℂ)) (g : ∀ v : S, locallyConstantTests (K F S v)) :
      sLocalBruhatPure F S φ (locallyConstantTestPiProduct g) ∈ C.range := by
    choose u hu using fun v : S ↦ finitePlaceFourierTest_tamagawa_surjective F v.val (g v)
    obtain ⟨φ₀, hφ⟩ := hT.surjective (c⁻¹ • φ)
    refine ⟨sLocalBruhatPure F S φ₀ (locallyConstantTestPiProduct u), ?_⟩
    apply sLocalBruhat_ext_of_restrict F S
    intro ξ
    change sLocalBruhatRestriction F S
      (sLocalFourierCompression F S (sLocalBruhatPure F S φ₀ (locallyConstantTestPiProduct u))).val ξ = _
    rw [hFact, sLocalBruhatPure_restrict, locallyConstantTestPiProduct_apply, hφ]
    simp_rw [hu]
    change c * ((c⁻¹ * φ (infiniteAdeleMixedHomeomorph F ξ.1)) * _) = _
    rw [← mul_assoc c, ← mul_assoc c, mul_inv_cancel₀ hc, one_mul]
    rfl
  have hPure (φ : 𝓢(X F, ℂ)) (g : locallyConstantTests (∀ v : S, K F S v)) :
      sLocalBruhatPure F S φ g ∈ C.range := by
    change g ∈ C.range.comap (sLocalBruhatPure F S φ)
    apply (show (⊤ : Submodule ℂ (locallyConstantTests (∀ v : S, K F S v))) ≤ _ from ?_) trivial
    rw [← locallyConstantTest_span_piProduct]
    apply Submodule.span_le.mpr
    rintro _ ⟨u, rfl⟩
    exact hp φ u
  have hall : E F S ≤ C.range.map (E F S).subtype := by
    apply Submodule.span_le.mpr
    rintro _ ⟨g, φ, rfl⟩
    exact Submodule.mem_map.mpr ⟨sLocalBruhatPure F S φ g, hPure φ g, rfl⟩
  intro f
  obtain ⟨g, hg, he⟩ := Submodule.mem_map.mp (hall f.property)
  obtain ⟨x, rfl⟩ := hg
  exact ⟨x, Subtype.ext he⟩

end

end Masullo
