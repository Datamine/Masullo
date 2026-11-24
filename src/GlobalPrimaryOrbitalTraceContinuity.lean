import GlobalPrimaryOrbitalTrace

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical CompactlySupported InnerProductSpace NNReal NumberField SchwartzMap

namespace Masullo
noncomputable section

variable (F : Type*) [Field F] [NumberField F]
private abbrev Q := IdeleClass F
private abbrev K := normOneIdeleClass F
private abbrev Place := HeightOneSpectrum (𝓞 F)
private abbrev zAt (ξ : ℝ) : ℂ := (↑(-2 * Real.pi * ξ) : ℂ) * Complex.I

local instance primaryTraceContinuityQMeasure : MeasurableSpace (Q F) := borel _
local instance primaryTraceContinuityQBorel : BorelSpace (Q F) := ⟨rfl⟩
local instance primaryTraceContinuityQT2 : T2Space (Q F) := ideleClasses_hausdorff
local instance primaryTraceContinuityQLC : LocallyCompactSpace (Q F) := ideleClasses_locallyCompact
local instance primaryTraceContinuityQSecondCountable : SecondCountableTopology (Q F) := ideleClass_secondCountable F

variable (μ : Measure (Q F)) [μ.IsHaarMeasure] (s : ℝ) (hs : 0 ≤ s)

private abbrev H (ω : PontryaginDual (K F)) := globalOrbitalSobolevIsotype F μ s hs ω
private abbrev R (A : Finset (Place F)) (ω : PontryaginDual (K F)) :=
  globalWeilIsotypeClosedRange F μ s hs A ω
private abbrev I (A : Finset (Place F)) (ω : PontryaginDual (K F)) :=
  globalWeilMomentIndices F A ω

local instance primaryTraceContinuityHComplete (ω : PontryaginDual (K F)) : CompleteSpace (H F μ s hs ω) :=
  (globalOrbitalSobolevIsotype_isClosed F μ s hs ω).completeSpace_coe
local instance primaryTraceContinuityRClosed (A : Finset (Place F)) (ω : PontryaginDual (K F)) :
    IsClosed (R F μ s hs A ω : Set (H F μ s hs ω)) :=
  Submodule.isClosed_topologicalClosure _

private def integralOperatorLM {G E : Type*} [MeasurableSpace G] [TopologicalSpace G]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] (η : Measure G)
    (T : G → E → E) (A : C_c(G, ℂ) → E →L[ℂ] E)
    (hA : ∀ f u, A f u = ∫ g, f g • T g u ∂η)
    (hI : ∀ (f : C_c(G, ℂ)) u, Integrable (fun g ↦ f g • T g u) η) :
    C_c(G, ℂ) →ₗ[ℂ] (E →L[ℂ] E) where
  toFun := A
  map_add' := fun f g ↦ ContinuousLinearMap.ext fun u ↦ by
    rw [hA, add_apply, hA, hA]
    simp only [CompactlySupportedContinuousMap.add_apply, add_smul]
    exact integral_add (hI f u) (hI g u)
  map_smul' := fun c f ↦ ContinuousLinearMap.ext fun u ↦ by
    rw [hA, _root_.smul_apply, hA]
    simp only [RingHom.id_apply, CompactlySupportedContinuousMap.smul_apply,
      smul_eq_mul, mul_smul, integral_smul]

set_option maxHeartbeats 900000 in
private def primaryOrbitalBruhatCompressionLM (A : Finset (Place F)) (ω : PontryaginDual (K F)) :
    BruhatCompactTest (Q F) →ₗ[ℂ] ((R F μ s hs A ω)ᗮ →L[ℂ] (R F μ s hs A ω)ᗮ) := by
  letI : μ.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure μ
  let W := R F μ s hs A ω
  let v := (H F μ s hs ω).subtypeL.comp Wᗮ.subtypeL
  let J := Wᗮ.orthogonalProjectionOnto
  let T (g : Q F) (u : Lp ℂ 2 μ) : Lp ℂ 2 μ :=
    hardySobolevMulTranslation μ (ideleClassLogNorm F) (ideleClassLogNorm_continuous F) 0 0 s hs g u
  have hI (f : C_c(Q F, ℂ)) (u : Lp ℂ 2 μ) : Integrable (fun g ↦ f g • T g u) μ := by
    have h := integrable_hardySobolev_convolution_orbit (G := Q F) μ (ideleClassLogNorm F)
      (ideleClassLogNorm_continuous F) 0 0 s hs f u
    change Integrable (fun g ↦ f g • T g u) μ at h
    exact h
  let B : C_c(Q F, ℂ) →ₗ[ℂ] (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) :=
    integralOperatorLM (G := Q F) (E := Lp ℂ 2 μ) μ T
      (globalHardySobolevConvolution F μ 0 0 s hs) (fun _ _ ↦ rfl) hI
  refine { toFun := fun f ↦ primaryOrbitalCompressedConvolution F μ s hs A ω (primaryOrbitalBruhatDensity F f)
           map_add' := ?_, map_smul' := ?_ }
  · intro f g
    apply ContinuousLinearMap.ext
    intro u
    let D := primaryOrbitalBruhatDensity F
    let C := globalIsotypicOrbitalConvolution F μ s hs ω
    have hD : D (f+g) = D f + D g := by
      ext x
      rfl
    change J (C (D (f+g)) u.val) = J (C (D f) u.val) + J (C (D g) u.val)
    rw [hD, ← map_add J]
    apply congrArg J
    apply Subtype.ext
    change B (D f + D g) (v u) = B (D f) (v u) + B (D g) (v u)
    rw [map_add, add_apply]
  · intro c f
    apply ContinuousLinearMap.ext
    intro u
    let D := primaryOrbitalBruhatDensity F
    let C := globalIsotypicOrbitalConvolution F μ s hs ω
    have hD : D (c • f) = c • D f := by
      ext x
      rfl
    change J (C (D (c • f)) u.val) = c • J (C (D f) u.val)
    rw [hD, ← map_smul J]
    apply congrArg J
    apply Subtype.ext
    change B (c • D f) (v u) = c • B (D f) (v u)
    rw [map_smul, _root_.smul_apply]

set_option maxHeartbeats 1800000 in
/-- The untruncated orbital convolution is a continuous linear family in trace norm. -/
theorem exists_primaryOrbitalBruhat_traceClassCLM (A : Finset (Place F))
    {p : ℕ} (hp : p.Prime)
    (hA : ∀ v ∈ A, v.asIdeal.under ℤ = Ideal.span {(p : ℤ)})
    (hdeg : 2 * (A.card : ℝ) ≤ s) (hs' : 1 < s) (ω : PontryaginDual (K F)) :
    ∃ L : BruhatCompactTest (Q F) →L[ℂ] TraceClass ((R F μ s hs A ω)ᗮ),
      ∀ φ : BruhatCompactTest (Q F),
        (L φ).toOperator = primaryOrbitalCompressedConvolution F μ s hs A ω
          (primaryOrbitalBruhatDensity F φ) ∧
        Summable (fun i : I F A ω ↦ ‖orbitalConvolutionCoefficient F μ φ.val.val
          (normOneEulerCharacter F ω) (zAt i.val.1) 0‖) ∧
        (L φ).traceValue = ∑' i : I F A ω, orbitalConvolutionCoefficient F μ φ.val.val
          (normOneEulerCharacter F ω) (zAt i.val.1) 0 := by
  obtain ⟨P,hP,hT⟩ := primaryOrbitalBruhat_trace F μ s hs A hp hA hdeg hs' ω
  let W := (R F μ s hs A ω)ᗮ
  letI : CompleteSpace W := (R F μ s hs A ω).isClosed_orthogonal.completeSpace_coe
  let B : BruhatCompactTest (Q F) →ₗ[ℂ] (W →L[ℂ] W) :=
    primaryOrbitalBruhatCompressionLM F μ s hs A ω
  have hB (φ : BruhatCompactTest (Q F)) :
      ∃ T : TraceClass ((R F μ s hs A ω)ᗮ), T.toOperator = B φ ∧ ‖T‖ ≤ P φ := by
    obtain ⟨T,h₁,h₂,_,_⟩ := hT φ
    exact ⟨T,h₁,h₂⟩
  have hLift : ∃ L : BruhatCompactTest (Q F) →L[ℂ] TraceClass W,
      ∀ φ, (L φ).toOperator = B φ := by
    refine exists_continuous_traceClass_lift (H := W) B P hP ?_
    exact hB
  obtain ⟨L,hL⟩ := hLift
  refine ⟨L,fun φ ↦ ?_⟩
  obtain ⟨T,h₁,_,h₂,h₃⟩ := hT φ
  have he : L φ = T := TraceClass.toOperator_injective ((hL φ).trans h₁.symm)
  exact ⟨hL φ, h₂, by rw [he]; exact h₃⟩

end
end Masullo
