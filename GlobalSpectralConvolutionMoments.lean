import SpectralConvolutionMoments
import SpectralStripNorms
import GlobalSpectralQuotientTrace

open Filter Function MeasureTheory NumberField Set Topology
open scoped CompactlySupported ENNReal NumberField

namespace Masullo

noncomputable section

section Global

variable (F : Type*) [Field F] [NumberField F]

local instance : MeasurableSpace (IdeleClass F) := borel _
local instance : BorelSpace (IdeleClass F) := ⟨rfl⟩
local instance : LocallyCompactSpace (IdeleClass F) := ideleClasses_locallyCompact
local instance : T2Space (IdeleClass F) := ideleClasses_hausdorff
local instance : SecondCountableTopology (IdeleClass F) := ideleClass_secondCountable F

variable (μ : Measure (IdeleClass F)) [μ.IsHaarMeasure]

abbrev globalComplexCharacter (χ : PontryaginDual (IdeleClass F)) : IdeleClass F →* ℂ :=
  Circle.coeHom.comp (show IdeleClass F →ₜ* Circle from χ).toMonoidHom

omit [μ.IsHaarMeasure] in
/-- The global Mellin moment paired against an element of the ambient Hilbert chart. -/
abbrev globalSpectralMomentFunctional (χ : PontryaginDual (IdeleClass F))
    (z : ℂ) (α s : ℝ) (n : ℕ)
    (h : MemLp (spectralChartMoment (ideleClassLogNorm F)
      (globalComplexCharacter F χ) z (-α) α s n) 2 μ) : StrongDual ℂ (Lp ℂ 2 μ) :=
  spectralMomentFunctional μ (ideleClassLogNorm F) (globalComplexCharacter F χ) z (-α) α s n h

theorem globalSpectralChartMoment_memLp_iff (χ : PontryaginDual (IdeleClass F))
    {α s b : ℝ} (hs : 0 ≤ s) (hb : b ∈ Icc (-α) α) (t : ℝ) (m : ℕ) :
    MemLp (spectralChartMoment (ideleClassLogNorm F) (globalComplexCharacter F χ)
      ((b : ℂ) + (t : ℂ) * Complex.I) (-α) α s m) 2 μ ↔
      b ∈ Ioo (-α) α ∨ (m : ℝ) < (s - 1) / 2 := by
  have hα : -α ≤ α := hb.1.trans hb.2
  have ha (x : ℝ) : hardySobolevAmplitude (-α) α s x = stripSobolevAmplitude (-α) α s x := by
    rw [hardySobolevAmplitude, ← stripSobolevAmplitude_sq hα, Real.sqrt_sq
      (stripSobolevAmplitude_pos _ _ _ _).le]
  have hr (x : ℝ) : stripSobolevAmplitude α (-α) (-s) x =
      (stripSobolevAmplitude (-α) α s x)⁻¹ := by
    simpa only [neg_neg] using stripSobolevAmplitude_neg (-α) α s x
  have he : spectralChartMoment (ideleClassLogNorm F) (globalComplexCharacter F χ)
      ((b : ℂ) + (t : ℂ) * Complex.I) (-α) α s m = spectralStripMoment F χ α s
      ((b : ℂ) + (t : ℂ) * Complex.I) m := by
    funext x
    unfold spectralChartMoment spectralHaarMoment spectralStripMoment
    rw [ha, hr, Complex.real_smul, Complex.ofReal_inv, div_eq_mul_inv]
    exact mul_comm _ _
  rw [he]
  exact spectralStripMoment_memLp_iff F μ χ hs hb t m

local instance spectralMomentThetaClosed (a α s : ℝ) (hs : 0 ≤ s) :
    IsClosed (globalThetaSobolevCompletion F μ a (-α) α s hs : Set (Lp ℂ 2 μ)) :=
  globalThetaSobolevCompletion_isClosed F μ a (-α) α s hs

/-- Left translation descends through the closed polar-free theta subspace. -/
def globalSpectralTranslation (a α s : ℝ) (hs : 0 ≤ s) (g : IdeleClass F) :
    let N := globalThetaSobolevCompletion F μ a (-α) α s hs
    (Lp ℂ 2 μ ⧸ N) →L[ℂ] (Lp ℂ 2 μ ⧸ N) := by
  intro N
  let T := hardySobolevMulTranslation μ (ideleClassLogNorm F) (ideleClassLogNorm_continuous F)
    (-α) α s hs g
  exact N.liftQL (N.mkQL.comp T) (fun u hu =>
    (Submodule.Quotient.mk_eq_zero N).mpr
      (globalThetaSobolevCompletion_mapsTo F μ a (-α) α s hs g hu))

set_option maxHeartbeats 900000 in
/-- The actual quotient convolution of a homogeneous test takes values in
the associated norm-one isotype. -/
theorem globalSpectralConvolution_homogeneous_image (a α s : ℝ) (hs : 0 ≤ s)
    (φ : C_c(IdeleClass F, ℂ)) (ω : PontryaginDual (normOneIdeleClass F))
    (hφ : ∀ (k : normOneIdeleClass F) g, φ (k.val⁻¹ * g) = (ω k : ℂ) * φ g) :
    let N := globalThetaSobolevCompletion F μ a (-α) α s hs
    let Q := globalSpectralConvolution F μ a (-α) α s hs φ
    ∀ (k : normOneIdeleClass F) (u : Lp ℂ 2 μ ⧸ N),
      globalSpectralTranslation F μ a α s hs k.val (Q u) = (ω k : ℂ) • Q u := by
  intro N Q k u
  letI : IsClosed (N : Set (Lp ℂ 2 μ)) := spectralMomentThetaClosed F μ a α s hs
  letI : μ.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure μ
  obtain ⟨x, rfl⟩ := N.mkQ_surjective u
  let T := hardySobolevMulTranslation μ (ideleClassLogNorm F) (ideleClassLogNorm_continuous F)
    (-α) α s hs k.val
  let A := globalHardySobolevConvolution F μ (-α) α s hs φ
  change N.mkQL (T (A x)) = (ω k : ℂ) • N.mkQL (A x)
  rw [← map_smul]
  have ht := hardySobolevConvolution_homogeneous_image μ (ideleClassLogNorm F) (-α) α s
    (ideleClassLogNorm_continuous F) hs φ k.val (ω k : ℂ) (hφ k) x
  change T (A x) = (ω k : ℂ) • A x at ht
  exact congrArg N.mkQL ht

end Global

end

end Masullo
