import GlobalPaleyWienerDensity
import GlobalSpectralQuotientTrace
import TraceClassRightCutoffs

open Filter Function MeasureTheory NumberField Set Topology
open scoped CompactlySupported NumberField

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

private abbrev K := normOneIdeleClass F
private abbrev Place := IsDedekindDomain.HeightOneSpectrum (𝓞 F)

local instance globalPaleyWienerTraceIdeleMeasurableSpace : MeasurableSpace (Idele F) := borel _
local instance globalPaleyWienerTraceIdeleBorelSpace : BorelSpace (Idele F) := ⟨rfl⟩
local instance globalPaleyWienerTraceIdeleClassMeasurableSpace : MeasurableSpace (IdeleClass F) := borel _
local instance globalPaleyWienerTraceIdeleClassBorelSpace : BorelSpace (IdeleClass F) := ⟨rfl⟩
local instance globalPaleyWienerTraceIdeleClassT2Space : T2Space (IdeleClass F) := ideleClasses_hausdorff
local instance globalPaleyWienerTraceIdeleClassLocallyCompactSpace : LocallyCompactSpace (IdeleClass F) := ideleClasses_locallyCompact
local instance globalPaleyWienerTraceIdeleClassSecondCountableTopology : SecondCountableTopology (IdeleClass F) := ideleClass_secondCountable F
local instance globalPaleyWienerTraceNormOneMeasurableSpace : MeasurableSpace (K F) := borel _
local instance globalPaleyWienerTraceNormOneBorelSpace : BorelSpace (K F) := ⟨rfl⟩

/-- All auxiliary Haar choices for the Paley–Wiener comparison exist. -/
theorem globalPaleyWiener_Haar_choices :
    ∃ (η : Measure (Idele F)) (ν τ : Measure (K F)),
      η.IsHaarMeasure ∧ ν.IsHaarMeasure ∧ τ.IsHaarMeasure ∧ IsProbabilityMeasure τ ∧
        IsWeilQuotientMeasure (principalIdeles F) η Measure.count (globalClassMeasure F ν) := by
  letI : LocallyCompactSpace (Idele F) := ideles_locallyCompact
  let η : Measure (Idele F) := Measure.haar
  letI : η.IsHaarMeasure := inferInstance
  obtain ⟨ν, hν, hw⟩ := globalClassMeasure_exists_weil F η
  letI : CompactSpace (K F) := normOneIdeleClass_compact F
  let τ : Measure (K F) := Measure.haarMeasure ⊤
  exact ⟨η, ν, τ, inferInstance, hν, Measure.isHaarMeasure_haarMeasure ⊤,
    ⟨Measure.haarMeasure_self (K₀ := ⊤)⟩, hw⟩

variable (η : Measure (Idele F)) [η.IsHaarMeasure]
variable (ν : Measure (K F)) [ν.IsHaarMeasure]
variable (hν : IsWeilQuotientMeasure (principalIdeles F) η Measure.count (globalClassMeasure F ν))
variable (ω : PontryaginDual (K F))
variable (μ : Measure (IdeleClass F)) [μ.IsHaarMeasure]
variable (a l r s : ℝ) (hs : 0 ≤ s) (S : Finset (Place F))

private abbrev N := globalThetaSobolevCompletion F μ a l r s hs

local instance : IsClosed (N F μ a l r s hs : Set (Lp ℂ 2 μ)) :=
  globalThetaSobolevCompletion_isClosed F μ a l r s hs

set_option maxHeartbeats 2000000 in
include hν in
/-- Fixed-cutoff condensation along either Paley–Wiener family converges in
trace norm and in scalar trace to convolution compressed on the right to the
geometric isotype. The finite operators are the geometric truncations in the
manuscript, represented in the ambient Hilbert space by the same projections. -/
theorem globalPaleyWiener_cutoff_condensation
    (τ : Measure (K F)) [τ.IsHaarMeasure] [IsProbabilityMeasure τ]
    (hsur : Surjective (sIdeleClassInclusion F S))
    (hu : globalNormOneCharacter F ω ∈ (sUnramified F S : Set (QuasiCharacter (IdeleClass F))))
    (region : ℝ → Set (SAdeles F S))
    (hr : region = sLocalPaleyWienerBox F S ∨ region = sLocalPaleyWienerRegion F S)
    (φ : BruhatSchwartz (IdeleClass F)) (hφ : HasCompactSupport φ.val)
    (w : IdeleClass F → ℝ) (hw : Measurable w) (hwc : HasCompactSupport w)
    (hw₀ : ∀ x, 0 ≤ w x) (hw₁ : ∀ x, w x ≤ 1) :
    let ψ : C_c(IdeleClass F, ℂ) := ⟨⟨φ.val, bruhatSchwartz_continuous φ⟩, hφ⟩
    let A := globalHardySobolevConvolution F μ l r s hs ψ
    let C := cutoffOperator (μ := μ) w hw hw₀ hw₁
    let P := fun R : ℝ ↦ globalPaleyWienerLevelProjection F ω μ a l r s hs S (region R)
    let G := globalGeometricIsotypeProjection F ω μ a l r s hs
    ∃ (T : TraceClass (Lp ℂ 2 μ)) (T₁ : ℝ → TraceClass (Lp ℂ 2 μ)),
      T.toOperator = C.comp (A.comp G) ∧
      (∀ R, (T₁ R).toOperator =
        C.comp ((N F μ a l r s hs).starProjection.comp (A.comp (P R)))) ∧
      Tendsto T₁ atTop (𝓝 T) ∧
      Tendsto (fun R ↦ (T₁ R).traceValue) atTop (𝓝 T.traceValue) := by
  intro ψ A C P G
  obtain ⟨T₀, hT₀⟩ := globalHardySobolev_cutoff_traceClass F μ l r s hs φ hφ
    w hw hwc hw₀ hw₁
  let T := T₀.rightCompose G
  let T₁ (R : ℝ) := T₀.rightCompose (P R)
  have hP (R : ℝ) (x : Lp ℂ 2 μ) : P R x ∈ N F μ a l r s hs :=
    globalPaleyWienerLevelProjection_mem_theta F ω μ a l r s hs S (region R) x
  have ht : Tendsto T₁ atTop (𝓝 T) := by
    apply TraceClass.rightCompose_tendsto T₀ P G (C := 1)
    · exact fun R ↦ globalPaleyWienerLevelProjection_norm F ω μ a l r s hs S (region R)
    · intro x
      change Tendsto (fun R ↦ (P R).adjoint x) atTop (𝓝 (G.adjoint x))
      simp only [P, G, globalGeometricIsotypeProjection_adjoint, globalPaleyWienerLevelProjection_adjoint]
      exact globalPaleyWienerLevelProjection_tendsto F η ν hν ω μ a l r s hs S τ hsur hu region hr x
  refine ⟨T, T₁, ?_, ?_, ht, (TraceClass.traceCLM.continuous.tendsto T).comp ht⟩
  · change T₀.toOperator.comp G = _
    rw [hT₀, ContinuousLinearMap.comp_assoc]
  · intro R
    change T₀.toOperator.comp (P R) = _
    rw [hT₀]
    ext x
    simp only [ContinuousLinearMap.comp_apply]
    have he : A (P R x) ∈ N F μ a l r s hs :=
      globalHardySobolevConvolution_preserves_theta F μ a l r s hs ψ (hP R x)
    rw [Submodule.starProjection_eq_self_iff.mpr he]


private abbrev W := globalAmbientSobolevIsotype F ω μ l r s hs
private abbrev translate (g : IdeleClass F) :=
  hardySobolevMulTranslation μ (ideleClassLogNorm F) (ideleClassLogNorm_continuous F) l r s hs g

/-- Abelian convolution preserves the norm-one translation isotype. -/
theorem globalHardySobolevConvolution_preserves_isotype (φ : C_c(IdeleClass F, ℂ)) :
    MapsTo (globalHardySobolevConvolution F μ l r s hs φ)
      (W F ω μ l r s hs) (W F ω μ l r s hs) := by
  intro u hu
  letI : μ.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure μ
  have hu' : ∀ k : K F, translate F μ l r s hs k.val u = (ω k : ℂ) • u :=
    (mem_thetaCharacterSubspace _ _ _).mp hu
  apply (mem_thetaCharacterSubspace _ _ _).mpr
  intro k
  let B := translate F μ l r s hs k.val
  let T := translate F μ l r s hs
  change B (∫ g, φ g • T g u ∂μ) = (ω k : ℂ) • ∫ g, φ g • T g u ∂μ
  rw [← B.integral_comp_comm (integrable_hardySobolev_convolution_orbit μ (ideleClassLogNorm F)
    (ideleClassLogNorm_continuous F) l r s hs φ u), ← integral_smul]
  apply integral_congr_ae
  exact Eventually.of_forall fun g ↦ by
    change T k.val (φ g • T g u) = (ω k : ℂ) • (φ g • T g u)
    rw [map_smul, ← hardySobolevMulTranslation_mul, mul_comm k.val g,
      hardySobolevMulTranslation_mul, hu' k, map_smul, smul_comm]

/-- Multiplication by the manuscript's norm-one invariant cutoff acts directly
on the isotype. -/
theorem globalRadialCutoff_preserves_isotype
    (w : IdeleClass F → ℝ) (hw : Measurable w) (hw₀ : ∀ x, 0 ≤ w x) (hw₁ : ∀ x, w x ≤ 1)
    (hrad : ∀ (k : K F) x, w (k.val⁻¹ * x) = w x) :
    MapsTo (cutoffOperator (μ := μ) w hw hw₀ hw₁)
      (W F ω μ l r s hs) (W F ω μ l r s hs) := by
  intro u hu
  let C := cutoffOperator (μ := μ) w hw hw₀ hw₁
  have hu' : ∀ k : K F, translate F μ l r s hs k.val u = (ω k : ℂ) • u :=
    (mem_thetaCharacterSubspace _ _ _).mp hu
  apply (mem_thetaCharacterSubspace _ _ _).mpr
  intro k
  let B := translate F μ l r s hs k.val
  change B (C u) = (ω k : ℂ) • C u
  rw [← C.map_smul, ← hu' k]
  apply Lp.ext
  filter_upwards [hardySobolevMulTranslation_ae μ (ideleClassLogNorm F)
    (ideleClassLogNorm_continuous F) l r s hs k.val (C u),
    hardySobolevMulTranslation_ae μ (ideleClassLogNorm F)
      (ideleClassLogNorm_continuous F) l r s hs k.val u,
    cutoffOperator_ae w hw hw₀ hw₁ (B u),
    (measurePreserving_mul_left μ k.val⁻¹).quasiMeasurePreserving.ae
      (cutoffOperator_ae w hw hw₀ hw₁ u)] with x h₁ h₂ h₃ h₄
  rw [h₁, h₃, h₂, h₄, hrad k x, mul_left_comm]

local instance : CompleteSpace (W F ω μ l r s hs) :=
  (globalAmbientSobolevIsotype_isClosed F ω μ l r s hs).completeSpace_coe

/-- Geometric projection restricted to the ambient norm-one isotype. -/
def globalIsotypicGeometricProjection : W F ω μ l r s hs →L[ℂ] W F ω μ l r s hs :=
  ((globalGeometricIsotypeProjection F ω μ a l r s hs).comp (W F ω μ l r s hs).subtypeL).codRestrict
    _ fun x ↦ globalGeometricIsotypeProjection_mapsTo_ambient F ω μ a l r s hs x.property

/-- The Paley–Wiener projection restricted to the ambient norm-one isotype. -/
def globalIsotypicPaleyWienerProjection (B : Set (SAdeles F S)) :
    W F ω μ l r s hs →L[ℂ] W F ω μ l r s hs :=
  ((globalPaleyWienerLevelProjection F ω μ a l r s hs S B).comp
    (W F ω μ l r s hs).subtypeL).codRestrict
      _ fun x ↦ globalPaleyWienerLevelProjection_mapsTo_ambient F ω μ a l r s hs S B x.property

include hν in
/-- Theorems 11.2.1.2(1) and 11.2.1.4(1). The absolute and invariant
projections converge strongly on the ambient norm-one isotype. -/
theorem globalIsotypicPaleyWienerProjection_tendsto
    (τ : Measure (K F)) [τ.IsHaarMeasure] [IsProbabilityMeasure τ]
    (hsur : Surjective (sIdeleClassInclusion F S))
    (hu : globalNormOneCharacter F ω ∈ (sUnramified F S : Set (QuasiCharacter (IdeleClass F))))
    (region : ℝ → Set (SAdeles F S))
    (hr : region = sLocalPaleyWienerBox F S ∨ region = sLocalPaleyWienerRegion F S)
    (x : W F ω μ l r s hs) :
    Tendsto (fun R ↦ globalIsotypicPaleyWienerProjection F ω μ a l r s hs S (region R) x)
      atTop (𝓝 (globalIsotypicGeometricProjection F ω μ a l r s hs x)) :=
  tendsto_subtype_rng.mpr
    (globalPaleyWienerLevelProjection_tendsto F η ν hν ω μ a l r s hs S τ hsur hu region hr x.val)

set_option maxHeartbeats 2600000 in
include hν in
/-- Corrected Theorems 11.2.1.2(2) and 11.2.1.4(2). Both finite
condensations have their trace limits on the ambient isotype. The limit
retains right compression to the geometric subspace at the fixed cutoff. -/
theorem globalIsotypicPaleyWiener_cutoff_condensation
    (τ : Measure (K F)) [τ.IsHaarMeasure] [IsProbabilityMeasure τ]
    (hsur : Surjective (sIdeleClassInclusion F S))
    (hu : globalNormOneCharacter F ω ∈ (sUnramified F S : Set (QuasiCharacter (IdeleClass F))))
    (region : ℝ → Set (SAdeles F S))
    (hr : region = sLocalPaleyWienerBox F S ∨ region = sLocalPaleyWienerRegion F S)
    (φ : BruhatSchwartz (IdeleClass F)) (hφ : HasCompactSupport φ.val)
    (w : IdeleClass F → ℝ) (hw : Measurable w) (hwc : HasCompactSupport w)
    (hw₀ : ∀ x, 0 ≤ w x) (hw₁ : ∀ x, w x ≤ 1) :
    let ψ : C_c(IdeleClass F, ℂ) := ⟨⟨φ.val, bruhatSchwartz_continuous φ⟩, hφ⟩
    let A := globalHardySobolevConvolution F μ l r s hs ψ
    let C := cutoffOperator (μ := μ) w hw hw₀ hw₁
    let P := fun R : ℝ ↦ globalPaleyWienerLevelProjection F ω μ a l r s hs S (region R)
    let G := globalGeometricIsotypeProjection F ω μ a l r s hs
    let V := W F ω μ l r s hs
    let J := V.subtypeL
    let Q := V.orthogonalProjectionOnto
    ∃ (T : TraceClass V) (T₁ : ℝ → TraceClass V),
      T.toOperator = Q.comp ((C.comp (A.comp G)).comp J) ∧
      (∀ R, (T₁ R).toOperator = Q.comp
        ((C.comp ((N F μ a l r s hs).starProjection.comp (A.comp (P R)))).comp J)) ∧
      Tendsto T₁ atTop (𝓝 T) ∧
      Tendsto (fun R ↦ (T₁ R).traceValue) atTop (𝓝 T.traceValue) := by
  intro ψ A C P G V J Q
  letI : CompleteSpace V := (globalAmbientSobolevIsotype_isClosed F ω μ l r s hs).completeSpace_coe
  obtain ⟨T, T₁, hT, hT₁, hnorm, htrace⟩ :=
    globalPaleyWiener_cutoff_condensation F η ν hν ω μ a l r s hs S τ hsur hu region hr
      φ hφ w hw hwc hw₀ hw₁
  let j := V.subtypeₗᵢ
  let B := globalAmbientSobolevIsotypeProjection F ω μ l r s hs
  have hj : j.toContinuousLinearMap.adjoint = Q := V.adjoint_subtypeL
  have hB : j.toContinuousLinearMap.comp j.toContinuousLinearMap.adjoint = B := by
    rw [hj]
    rfl
  have hTG : T.toOperator.comp B = T.toOperator := by
    rw [hT, ContinuousLinearMap.comp_assoc, ContinuousLinearMap.comp_assoc]
    rw [globalGeometricIsotypeProjection_comp_ambient]
  have hT₁G (R : ℝ) : (T₁ R).toOperator.comp B = (T₁ R).toOperator := by
    rw [hT₁ R, ContinuousLinearMap.comp_assoc, ContinuousLinearMap.comp_assoc,
      ContinuousLinearMap.comp_assoc, globalPaleyWienerLevelProjection_comp_ambient]
  let A₁ := TraceClass.compress j
  refine ⟨A₁ T, fun R ↦ A₁ (T₁ R), ?_, ?_, (A₁.continuous.tendsto T).comp hnorm, ?_⟩
  · change (TraceClass.compress j T).toOperator = _
    rw [TraceClass.compress_toOperator, hj, hT]
    rfl
  · intro R
    change (TraceClass.compress j (T₁ R)).toOperator = _
    rw [TraceClass.compress_toOperator, hj, hT₁ R]
    rfl
  have ht₀ : (A₁ T).traceValue = T.traceValue :=
    TraceClass.compress_traceValue j T (hB.symm ▸ hTG)
  have ht₁ (R : ℝ) : (A₁ (T₁ R)).traceValue = (T₁ R).traceValue :=
    TraceClass.compress_traceValue j (T₁ R) (hB.symm ▸ hT₁G R)
  simpa only [ht₀, ht₁] using htrace

set_option maxHeartbeats 1200000 in
include hν in
/-- For the radial cutoffs of Definition 9.3.3.1 the operator formulas hold
directly in the isotype, using radial band support to get compactness. -/
theorem globalIsotypicPaleyWiener_radial_condensation
    (τ : Measure (K F)) [τ.IsHaarMeasure] [IsProbabilityMeasure τ]
    (hsur : Surjective (sIdeleClassInclusion F S))
    (hu : globalNormOneCharacter F ω ∈ (sUnramified F S : Set (QuasiCharacter (IdeleClass F))))
    (region : ℝ → Set (SAdeles F S))
    (hr : region = sLocalPaleyWienerBox F S ∨ region = sLocalPaleyWienerRegion F S)
    (φ : BruhatSchwartz (IdeleClass F)) (hφ : HasCompactSupport φ.val)
    (w : IdeleClass F → ℝ) (hw : Measurable w) (hw₀ : ∀ x, 0 ≤ w x) (hw₁ : ∀ x, w x ≤ 1)
    (hrad : ∀ (k : K F) x, w (k.val⁻¹ * x) = w x)
    (L : ℝ) (hL : 0 < L) (hsupp : ∀ x, ideleClassNorm F x ∉ Icc L⁻¹ L → w x = 0) :
    let ψ : C_c(IdeleClass F, ℂ) := ⟨⟨φ.val, bruhatSchwartz_continuous φ⟩, hφ⟩
    let A := globalHardySobolevConvolution F μ l r s hs ψ
    let C := cutoffOperator (μ := μ) w hw hw₀ hw₁
    let P := fun R : ℝ ↦ globalPaleyWienerLevelProjection F ω μ a l r s hs S (region R)
    let G := globalGeometricIsotypeProjection F ω μ a l r s hs
    let V := W F ω μ l r s hs
    ∃ (T : TraceClass V) (T₁ : ℝ → TraceClass V),
      (∀ x : V, ((T.toOperator x : V) : Lp ℂ 2 μ) = C (A (G x.val))) ∧
      (∀ (R : ℝ) (x : V), (((T₁ R).toOperator x : V) : Lp ℂ 2 μ) =
        C ((N F μ a l r s hs).starProjection (A (P R x.val)))) ∧
      Tendsto T₁ atTop (𝓝 T) ∧
      Tendsto (fun R ↦ (T₁ R).traceValue) atTop (𝓝 T.traceValue) := by
  intro ψ A C P G V
  obtain ⟨T, T₁, hT, hT₁, hnorm, htrace⟩ :=
    globalIsotypicPaleyWiener_cutoff_condensation F η ν hν ω μ a l r s hs S τ hsur hu region hr
      φ hφ w hw (ideleClass_radialCutoff_hasCompactSupport F L hL w hsupp) hw₀ hw₁
  have hA := globalHardySobolevConvolution_preserves_isotype F ω μ l r s hs ψ
  have hC := globalRadialCutoff_preserves_isotype F ω μ l r s hs w hw hw₀ hw₁ hrad
  refine ⟨T, T₁, ?_, ?_, hnorm, htrace⟩
  · intro x
    rw [hT]
    change V.starProjection (C (A (G x.val))) = _
    exact Submodule.starProjection_eq_self_iff.mpr (hC (hA
      (globalGeometricIsotypeProjection_mapsTo_ambient F ω μ a l r s hs x.property)))
  · intro R x
    rw [hT₁ R]
    change V.starProjection (C ((N F μ a l r s hs).starProjection (A (P R x.val)))) = _
    have hx : A (P R x.val) ∈ N F μ a l r s hs :=
      globalHardySobolevConvolution_preserves_theta F μ a l r s hs ψ
        (globalPaleyWienerLevelProjection_mem_theta F ω μ a l r s hs S (region R) x.val)
    rw [Submodule.starProjection_eq_self_iff.mpr hx]
    exact Submodule.starProjection_eq_self_iff.mpr (hC (hA
      (globalPaleyWienerLevelProjection_mapsTo_ambient F ω μ a l r s hs S (region R) x.property)))

end
end Masullo
