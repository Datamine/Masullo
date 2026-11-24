import SLocalPaleyWienerLevels
import SLocalFourierInversion
import SLocalFlatComponents
import SLocalThetaDualGeneration
import SchwartzCyclicMoment

open Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical NumberField SchwartzMap

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]
variable (S : Finset (HeightOneSpectrum (𝓞 F)))

private abbrev E := sLocalBruhatImage F

/-- Compact additive support transfers to exact Fourier support under a
preimage of the compressed Fourier integral. Its theta class and both
evaluation moments are controlled by the prescribed transform. -/
theorem exists_sLocalPaleyWienerTest_fourier_preimage (K : Set (SAdeles F S))
    (hK : IsCompact K) (g : E F S)
    (hg : tsupport (sLocalBruhatRestriction F S g.val) ⊆ K) :
    ∃ f : E F S, f ∈ sLocalPaleyWienerTests F S K ∧ sLocalFourierCompression F S f = g ∧
      (GlobalBruhat.polarEvaluation F f.val = 0 ↔ GlobalBruhat.polarEvaluation F g.val = 0) ∧
      sLocalThetaOperator F S f = (ideleNorm F (sLocalCodifferentTailIdele F S) : ℂ) •
        sLocalThetaOperator F S (sLocalFourierCompression F S g) := by
  obtain ⟨f, hf⟩ := sLocalFourierCompression_surjective F S g
  refine ⟨f, (mem_sLocalPaleyWienerTests_iff F S K f).mpr ?_, hf, ?_, ?_⟩
  · rw [hf]
    exact ⟨hK.of_isClosed_subset isClosed_closure hg, hg⟩
  · rw [← hf]
    exact (sLocalFourierCompression_polarEvaluation_eq_zero_iff F S f).symm
  · have h := sLocalFourierCompression_double_theta F S f
    rw [hf] at h
    exact h.symm

attribute [local instance] sLocalZetaUnfolding_classMeasurable sLocalZetaUnfolding_classBorel

/-- Each compact interval of profiles in a fixed component gives an exact
Fourier preimage at one base-stage radius. The lifted tests with zero
moments enter the corresponding closed zero-moment level on every
enlarged stage. -/
theorem exists_sLocalPaleyWienerStage_fourier_preimages
    (ν : Measure (SLocalThetaNormOne F S)) [ν.IsHaarMeasure]
    (ω : PontryaginDual (SLocalThetaNormOne F S)) (a b : ℝ) :
    ∃ (L : PositiveRealExponentialDecay univ →L[ℂ] sLocalPolarFreeTestSubspace F S)
      (X : ℝ), 0 < X ∧
      (∀ φ t, sLocalHomogeneousTheta F S ν ω (L φ).val.val (sLocalLogNormRay F S t) = φ.val t) ∧
      ∀ φ, support φ.val ⊆ Icc a b →
        ∃ f : E F S, sLocalFourierCompression F S f = (L φ).val ∧
          f ∈ sLocalPaleyWienerTests F S (sLocalPaleyWienerBox F S X) ∧
          ∀ {T : Finset (HeightOneSpectrum (𝓞 F))} (hST : S ⊆ T),
            GlobalBruhat.polarEvaluation F (L φ).val.val = 0 →
            sLocalBruhatTransition F hST f ∈
              sLocalPaleyWienerStageTests F S hST (sLocalPaleyWienerBox F S X) ⊓
                sLocalPaleyWienerMomentKernel F T := by
  obtain ⟨L, hL, hSupport⟩ :=
    exists_sLocalHomogeneousTheta_polarFreeCLM_fixedSupport F S ν ω
  obtain ⟨K, hK, hKL⟩ := hSupport a b
  obtain ⟨X, hX, hXK⟩ := exists_sLocalPaleyWienerBox_of_isCompact F S hK
  refine ⟨L, X, hX, hL, fun φ hφ ↦ ?_⟩
  obtain ⟨f, hf, hFourier, hMoment, _⟩ :=
    exists_sLocalPaleyWienerTest_fourier_preimage F S K hK (L φ).val (hKL φ hφ)
  have hbox := sLocalPaleyWienerTests_mono F S hXK hf
  refine ⟨f, hFourier, hbox, fun hST hm ↦ ⟨?_, ?_⟩⟩
  · exact Submodule.mem_map.mpr ⟨f, hbox, rfl⟩
  · exact hMoment.mpr hm

/-- For a nontrivial component the same fixed-radius construction realizes
every compact profile with both evaluation moments zero. -/
theorem exists_sLocalPaleyWienerTest_nontrivial_fourier_profiles
    (ν : Measure (SLocalThetaNormOne F S)) [ν.IsHaarMeasure]
    (ω : PontryaginDual (SLocalThetaNormOne F S)) (hω : ω ≠ 1) (a b : ℝ) :
    ∃ X > 0, ∀ φ : PositiveRealExponentialDecay univ, support φ.val ⊆ Icc a b →
      ∃ f : E F S, f ∈ sLocalPaleyWienerTests F S (sLocalPaleyWienerBox F S X) ∧
        GlobalBruhat.polarEvaluation F f.val = 0 ∧
        ∀ t, sLocalHomogeneousTheta F S ν ω (sLocalFourierCompression F S f).val
          (sLocalLogNormRay F S t) = φ.val t := by
  obtain ⟨L, hL, hSupport⟩ :=
    exists_sLocalHomogeneousTheta_polarFreeCLM_fixedSupport F S ν ω
  obtain ⟨K, hK, hKL⟩ := hSupport a b
  obtain ⟨k, hk⟩ : ∃ k, ω k ≠ 1 := by
    by_contra! h
    exact hω (ContinuousMonoidHom.ext h)
  obtain ⟨u, hu⟩ := QuotientGroup.mk_surjective k.val
  have hnorm : sLocalIdeleNorm F S u = 1 := by
    rw [← sLocalClassModulus_mk, hu]
    have hk₀ : sQuotientNorm F S k.val = 1 := k.property
    simp [sLocalClassModulus, hk₀]
  have hd : (ω k : ℂ) - 1 ≠ 0 := by
    intro he
    exact hk (Circle.coe_injective ((sub_eq_zero.mp he).trans Circle.coe_one.symm))
  let D : Set (SAdeles F S) := ((fun x ↦ u.val * x) '' K) ∪ K
  have hD : IsCompact D := (hK.image (continuous_const.mul continuous_id)).union hK
  letI : T2Space (InfiniteAdeleRing F) := (infiniteAdeleMixedHomeomorph F).isEmbedding.t2Space
  obtain ⟨X, hX, hDX⟩ := exists_sLocalPaleyWienerBox_of_isCompact F S hD
  refine ⟨X, hX, fun φ hφ ↦ ?_⟩
  let g₀ := (L φ).val
  let g₁ := sLocalBruhatLeftTranslate F S u g₀
  let g : E F S := ((ω k : ℂ) - 1)⁻¹ • (g₁ - g₀)
  have hm₁ : GlobalBruhat.polarEvaluation F g₁.val = GlobalBruhat.polarEvaluation F g₀.val := by
    change GlobalBruhat.polarEvaluation F (GlobalBruhat.leftTranslate F (sLocalEmbed F S u).val g₀.val) = _
    rw [polarEvaluation_leftTranslate, show ideleNorm F (sLocalEmbed F S u).val = 1 from hnorm, one_smul]
  have hm : GlobalBruhat.polarEvaluation F g.val = 0 := by
    change GlobalBruhat.polarEvaluation F (((ω k : ℂ) - 1)⁻¹ • (g₁.val - g₀.val)) = 0
    rw [map_smul, map_sub, hm₁, sub_self, smul_zero]
  have hSupp : tsupport (sLocalBruhatRestriction F S g.val) ⊆ D := by
    apply closure_minimal _ hD.isClosed
    intro x hx
    by_contra h
    have hx₀ : sLocalBruhatRestriction F S g₀.val x = 0 :=
      notMem_support.mp fun he ↦ h (Or.inr (hKL φ hφ (subset_closure he)))
    have hx₁ : sLocalBruhatRestriction F S g₁.val x = 0 := by
      rw [sLocalBruhatLeftTranslate_restrict]
      apply notMem_support.mp
      intro he
      apply h
      refine Or.inl ⟨u.inv * x, hKL φ hφ (subset_closure he), ?_⟩
      change u.val * (u.inv * x) = x
      rw [← mul_assoc, u.val_inv, one_mul]
    have he : sLocalBruhatRestriction F S g.val x = 0 := by
      change (sLocalBruhatRestriction F S) (((ω k : ℂ) - 1)⁻¹ • (g₁.val - g₀.val)) x = 0
      rw [map_smul, map_sub, Pi.smul_apply, Pi.sub_apply, hx₁, hx₀, sub_self, smul_zero]
    exact hx he
  obtain ⟨f, hf, hFourier, hMoment, _⟩ :=
    exists_sLocalPaleyWienerTest_fourier_preimage F S D hD g hSupp
  refine ⟨f, sLocalPaleyWienerTests_mono F S hDX hf, hMoment.mpr hm, fun t ↦ ?_⟩
  rw [hFourier]
  let ev := sLocalHomogeneousThetaEvalLinear F S ν ω (sLocalLogNormRay F S t)
  change ev g = φ.val t
  have he : ev g₁ = (ω k : ℂ) * ev g₀ :=
    sLocalHomogeneousTheta_leftTranslate_normOne F S ν ω k u hu g₀ _
  have he₀ : ev g₀ = φ.val t := hL φ t
  change ev (((ω k : ℂ) - 1)⁻¹ • (g₁ - g₀)) = _
  rw [map_smul, map_sub, smul_eq_mul, he, ← sub_one_mul, ← mul_assoc, inv_mul_cancel₀ hd, one_mul, he₀]

/-- For the trivial component a single radius realizes all profiles
of fixed log support whose exponential moment vanishes. -/
theorem exists_sLocalPaleyWienerTest_trivial_fourier_profiles
    (ν : Measure (SLocalThetaNormOne F S)) [ν.IsHaarMeasure] (a b : ℝ) :
    ∃ X > 0, ∀ φ : PositiveRealExponentialDecay univ, support φ.val ⊆ Icc a b →
      logProfileExponentialMoment φ.val = 0 →
      ∃ f : E F S, f ∈ sLocalPaleyWienerTests F S (sLocalPaleyWienerBox F S X) ∧
        GlobalBruhat.polarEvaluation F f.val = 0 ∧
        ∀ t, sLocalHomogeneousTheta F S ν 1 (sLocalFourierCompression F S f).val
          (sLocalLogNormRay F S t) = φ.val t := by
  obtain ⟨L, hL, hSupport, hMoments⟩ :=
    exists_sLocalHomogeneousTheta_trivial_polarFreeCLM_fixedSupport F S ν
  obtain ⟨K, hK, hKL⟩ := hSupport a b
  obtain ⟨X, hX, hXK⟩ := exists_sLocalPaleyWienerBox_of_isCompact F S hK
  refine ⟨X, hX, fun φ hφ hm ↦ ?_⟩
  obtain ⟨f, hf, hFourier, hEval, _⟩ :=
    exists_sLocalPaleyWienerTest_fourier_preimage F S K hK (L φ).val (hKL φ hφ)
  refine ⟨f, sLocalPaleyWienerTests_mono F S hXK hf, hEval.mpr (hMoments φ hm), fun t ↦ ?_⟩
  rw [hFourier, hL]
  change φ.val (Real.log (sLocalIdeleNorm F S (sLocalExpSection F S (Multiplicative.ofAdd t)))) = _
  rw [sLocalIdeleNorm_expSection, Real.log_exp]

/-- One Fourier radius suffices to represent every scalar cyclic quotient
class by the Fourier profile of a base-stage test with both moments zero. -/
theorem exists_sLocalPaleyWienerTest_cyclicRepresentatives
    (ν : Measure (SLocalThetaNormOne F S)) [ν.IsHaarMeasure]
    (ω : PontryaginDual (SLocalThetaNormOne F S))
    (gs : List (ℝ × Circle)) (hgs : ∀ g ∈ gs, 0 < g.1) :
    ∃ (X : ℝ) (A : 𝓢(ℝ, ℂ) →L[ℂ] PositiveRealExponentialDecay univ), 0 < X ∧
      (∀ f, f - positiveRealExponentialDecay_zeroInclusion univ (mem_univ 0) (A f) ∈
        (schwartzCyclicDifferenceProduct gs).range) ∧
      ∀ f, ∃ g : E F S,
        g ∈ sLocalPaleyWienerTests F S (sLocalPaleyWienerBox F S X) ∧
        GlobalBruhat.polarEvaluation F g.val = 0 ∧
        ∀ t, sLocalHomogeneousTheta F S ν ω (sLocalFourierCompression F S g).val
          (sLocalLogNormRay F S t) = (A f).val t := by
  obtain ⟨a, b, A, hA, hSupp, hMoment⟩ :=
    schwartzCyclicDifferenceProduct_zeroMoment_representatives gs hgs
  by_cases hω : ω = 1
  · subst ω
    obtain ⟨X, hX, h⟩ := exists_sLocalPaleyWienerTest_trivial_fourier_profiles F S ν a b
    exact ⟨X, A, hX, hA, fun f ↦ h (A f) (hSupp f) (hMoment f)⟩
  · obtain ⟨X, hX, h⟩ := exists_sLocalPaleyWienerTest_nontrivial_fourier_profiles F S ν ω hω a b
    exact ⟨X, A, hX, hA, fun f ↦ h (A f) (hSupp f)⟩

end

end Masullo
