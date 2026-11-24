import OrbitalPoissonSampling
import SpectralQuotientTrace
import NuclearKernelDiagonal

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped CompactlySupported InnerProductSpace NNReal NumberField Pointwise

namespace Masullo
noncomputable section

section Kernels

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
variable (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]

/-- A trace-class operator on the Haar (L^2) chart has an actual kernel and
an integrable diagonal represented by the regularized kernel values. -/
theorem TraceClass.exists_haarKernel_diagonal
    (T : TraceClass (Lp ℂ 2 μ)) :
    ∃ k : Lp ℂ 2 (μ.prod μ), ∃ d : G → ℂ,
      kernelIntegralOperator k = T.toOperator ∧ Measurable d ∧ Integrable d μ ∧
      (∫ x, d x ∂μ) = T.traceValue ∧
      ∀ (U : ℕ → Set G), DoublingSequence μ U → CofinalAtOne U →
        IsCompact (closure (U 0)) → ∀ C : ℝ≥0, 0 < C →
        (∀ n, μ (U n * (U n)⁻¹) < C * μ (U n)) →
        ∀ᵐ x ∂μ, Tendsto (fun n ↦ translatedAverage (μ.prod μ) (U n ×ˢ U n)
          (k : G × G → ℂ) (x,x)) atTop (𝓝 (d x)) := by
  obtain ⟨R,hR⟩ := T.toOperator_mem
  obtain ⟨k,hk,_⟩ := R.exists_hilbertSchmidtKernel μ
  let d (x : G) : ℂ := ∑' n, R.image n x * star (R.functional n x)
  have hd : Measurable d := Measurable.tsum fun n ↦
    (Lp.stronglyMeasurable (R.image n)).measurable.mul
      (continuous_star.measurable.comp (Lp.stronglyMeasurable (R.functional n)).measurable)
  refine ⟨k,d,hk.trans hR,hd,(R.diagonal_series_trace μ).1,?_,?_⟩
  · exact (R.diagonal_series_trace μ).2.trans (T.traceValue_eq_of_operator R hR).symm
  · intro U hU hcof hcompact C hC hDiff
    apply R.kernel_diagonal_tendsto_series μ hU hcof hcompact hC hDiff (Lp.memLp k)
    rw [Lp.toLp_coeFn]
    exact hk

end Kernels

variable (F : Type*) [Field F] [NumberField F]
private abbrev Q := IdeleClass F
private abbrev K := normOneIdeleClass F
private abbrev Place := HeightOneSpectrum (𝓞 F)

local instance primaryKernelQMeasurable : MeasurableSpace (Q F) := borel _
local instance primaryKernelQBorel : BorelSpace (Q F) := ⟨rfl⟩
local instance primaryKernelQT2 : T2Space (Q F) := ideleClasses_hausdorff
local instance primaryKernelQLC : LocallyCompactSpace (Q F) := ideleClasses_locallyCompact
local instance primaryKernelQSecondCountable : SecondCountableTopology (Q F) := ideleClass_secondCountable F
local instance primaryKernelKMeasurable : MeasurableSpace (K F) := borel _
local instance primaryKernelKBorel : BorelSpace (K F) := ⟨rfl⟩
local instance primaryKernelKCompact : CompactSpace (K F) := normOneIdeleClass_compact F

variable (ν : Measure (K F)) [ν.IsHaarMeasure]
private abbrev μ := globalClassMeasure F ν
local instance primaryKernelHaar : (μ F ν).IsHaarMeasure := globalClassMeasure_isHaar F ν
local instance primaryKernelRegular : (μ F ν).Regular :=
  Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _
private abbrev H (s : ℝ) (hs : 0 ≤ s) (ω : PontryaginDual (K F)) :=
  globalOrbitalSobolevIsotype F (μ F ν) s hs ω
local instance primaryKernelHComplete (s : ℝ) (hs : 0 ≤ s) (ω : PontryaginDual (K F)) :
    CompleteSpace (H F ν s hs ω) :=
  (globalOrbitalSobolevIsotype_isClosed F (μ F ν) s hs ω).completeSpace_coe

variable (s : ℝ) (hs : 0 ≤ s) (A : Finset (Place F)) (χ : PontryaginDual (Q F))
private abbrev ω := heckeNormOneRestriction F χ
private abbrev R := globalWeilIsotypeClosedRange F (μ F ν) s hs A (ω F χ)

/-- Embed the completed primary orbital quotient by its orthogonal
representatives in the ambient amplitude chart. -/
def primaryOrbitalKernelEmbedding :
    (R F ν s hs A χ)ᗮ →ₗᵢ[ℂ] Lp ℂ 2 (μ F ν) :=
  (H F ν s hs (ω F χ)).subtypeₗᵢ.comp (R F ν s hs A χ)ᗮ.subtypeₗᵢ

private def primaryOrbitalKernelProjection :
    Lp ℂ 2 (μ F ν) →L[ℂ] (R F ν s hs A χ)ᗮ :=
  (R F ν s hs A χ)ᗮ.orthogonalProjectionOnto.comp
    (H F ν s hs (ω F χ)).orthogonalProjectionOnto

/-- The ambient operator represented by the primary quotient, extended
by zero on the orthogonal complement. -/
def primaryOrbitalKernelOperator (φ : BruhatCompactTest (Q F)) :
    Lp ℂ 2 (μ F ν) →L[ℂ] Lp ℂ 2 (μ F ν) :=
  let j : (R F ν s hs A χ)ᗮ →L[ℂ] Lp ℂ 2 (μ F ν) :=
    (primaryOrbitalKernelEmbedding F ν s hs A χ).toContinuousLinearMap
  j.comp ((primaryOrbitalCompressedConvolution F (μ F ν) s hs A (ω F χ)
    (primaryOrbitalBruhatDensity F φ)).comp (primaryOrbitalKernelProjection F ν s hs A χ))

set_option maxHeartbeats 1600000 in
/-- The half-shifted Poisson trace is a kernel diagonal of the extended
primary orbital compression, in the original idele-class Haar chart. -/
theorem exists_primaryOrbitalPoissonKernel
    {p : ℕ} (hp : p.Prime) (hA : ∀ v ∈ A, v.asIdeal.under ℤ = Ideal.span {(p : ℤ)})
    (hDegree : 2 * (Module.finrank ℚ F : ℝ) ≤ s) (hs' : 1 < s)
    (hχ : ∀ v ∈ A, unramifiedFiniteCharacter F χ v)
    (b : ℝ) (φ : BruhatCompactTest (Q F)) :
    ∃ k : Lp ℂ 2 ((μ F ν).prod (μ F ν)), ∃ d : Q F → ℂ,
      kernelIntegralOperator k =
        primaryOrbitalKernelOperator F ν s hs A χ (orbitalShiftedBruhatTest F b φ) ∧
      Measurable d ∧ Integrable d (μ F ν) ∧
      (∫ x, d x ∂μ F ν) = (∑ v ∈ A, ∑' n : ℤ, orbitalPlacePoissonSample F ν χ φ v b n) ∧
      ∀ (U : ℕ → Set (Q F)), DoublingSequence (μ F ν) U → CofinalAtOne U →
        IsCompact (closure (U 0)) → ∀ C : ℝ≥0, 0 < C →
        (∀ n, μ F ν (U n * (U n)⁻¹) < C * μ F ν (U n)) →
        ∀ᵐ x ∂μ F ν, Tendsto (fun n ↦ translatedAverage ((μ F ν).prod (μ F ν)) (U n ×ˢ U n)
          (k : Q F × Q F → ℂ) (x,x)) atTop (𝓝 (d x)) := by
  obtain ⟨L,hL,hTrace⟩ := exists_primaryOrbitalTrace_poisson F ν A hp hA s hs hDegree hs' χ hχ
  let ψ := orbitalShiftedBruhatTest F b φ
  let J := primaryOrbitalKernelEmbedding F ν s hs A χ
  let j : (R F ν s hs A χ)ᗮ →L[ℂ] Lp ℂ 2 (μ F ν) := J.toContinuousLinearMap
  let q := primaryOrbitalKernelProjection F ν s hs A χ
  have hleft (x : (R F ν s hs A χ)ᗮ) : q (j x) = x := by
    change (R F ν s hs A χ)ᗮ.orthogonalProjectionOnto
      ((H F ν s hs (ω F χ)).orthogonalProjectionOnto (x.val.val)) = x
    rw [(H F ν s hs (ω F χ)).orthogonalProjectionOnto_mem_subspace_eq_self x.val]
    exact (R F ν s hs A χ)ᗮ.orthogonalProjectionOnto_mem_subspace_eq_self x
  obtain ⟨T,hT,hval⟩ := traceClass_transport j q hleft (L ψ)
  obtain ⟨k,d,hk,hm,hdi,hd,hw⟩ := T.exists_haarKernel_diagonal (μ F ν)
  refine ⟨k,d,?_,hm,hdi,hd.trans (hval.trans (hTrace b φ)),hw⟩
  exact hk.trans (hT.trans (congrArg (fun T ↦ j.comp (T.comp q)) (hL ψ)))

end
end Masullo
