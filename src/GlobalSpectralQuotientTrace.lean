import GlobalThetaSobolev
import HardySobolevCutoffAction
import IdelicCutoffKernel

open Filter MeasureTheory NumberField Set Topology
open scoped CompactlySupported InnerProductSpace NumberField

namespace Masullo

noncomputable section

set_option maxHeartbeats 1200000

variable (F : Type*) [Field F] [NumberField F]

local instance : MeasurableSpace (IdeleClass F) := borel _
local instance : BorelSpace (IdeleClass F) := ⟨rfl⟩
local instance : LocallyCompactSpace (IdeleClass F) := ideleClasses_locallyCompact

local instance : T2Space (IdeleClass F) := ideleClasses_hausdorff
local instance : SecondCountableTopology (IdeleClass F) := ideleClass_secondCountable F

variable (μ : Measure (IdeleClass F)) [μ.IsHaarMeasure]

local instance thetaClosed (a l r s : ℝ) (hs : 0 ≤ s) :
    IsClosed (globalThetaSobolevCompletion F μ a l r s hs : Set (Lp ℂ 2 μ)) :=
  globalThetaSobolevCompletion_isClosed F μ a l r s hs

private abbrev translate (l r s : ℝ) (hs : 0 ≤ s) (g : IdeleClass F) :=
  hardySobolevMulTranslation μ (ideleClassLogNorm F) (ideleClassLogNorm_continuous F) l r s hs g

/-- Haar convolution on the ambient global Hardy–Sobolev space in amplitude
coordinates. -/
def globalHardySobolevConvolution (l r s : ℝ) (hs : 0 ≤ s)
    (φ : C_c(IdeleClass F, ℂ)) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ := by
  letI : μ.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure μ
  exact hardySobolevConvolution μ (ideleClassLogNorm F) (ideleClassLogNorm_continuous F)
    l r s hs φ

theorem globalHardySobolevConvolution_preserves_theta (a l r s : ℝ)
    (hs : 0 ≤ s) (φ : C_c(IdeleClass F, ℂ)) :
    MapsTo (globalHardySobolevConvolution F μ l r s hs φ)
      (globalThetaSobolevCompletion F μ a l r s hs)
      (globalThetaSobolevCompletion F μ a l r s hs) := by
  intro f hf
  letI : μ.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure μ
  let N := globalThetaSobolevCompletion F μ a l r s hs
  letI : IsClosed (N : Set (Lp ℂ 2 μ)) := globalThetaSobolevCompletion_isClosed F μ a l r s hs
  apply (Submodule.Quotient.mk_eq_zero N).mp
  change N.mkQL (∫ g, φ g • translate F μ l r s hs g f ∂μ) = 0
  rw [← N.mkQL.integral_comp_comm (integrable_hardySobolev_convolution_orbit μ (ideleClassLogNorm F)
    (ideleClassLogNorm_continuous F) l r s hs φ f)]
  have hz (g : IdeleClass F) : N.mkQL (φ g • translate F μ l r s hs g f) = 0 :=
    (Submodule.Quotient.mk_eq_zero N).mpr (N.smul_mem _ (
      globalThetaSobolevCompletion_mapsTo F μ a l r s hs g hf))
  simp [hz]

/-- The spectral convolution on the actual Hilbert quotient by the
closed polar-free theta space. -/
def globalSpectralConvolution (a l r s : ℝ) (hs : 0 ≤ s)
    (φ : C_c(IdeleClass F, ℂ)) :
    let N := globalThetaSobolevCompletion F μ a l r s hs
    (Lp ℂ 2 μ ⧸ N) →L[ℂ] (Lp ℂ 2 μ ⧸ N) := by
  intro N
  exact N.liftQL (N.mkQL.comp (globalHardySobolevConvolution F μ l r s hs φ))
    (fun f hf => (Submodule.Quotient.mk_eq_zero N).mpr
      (globalHardySobolevConvolution_preserves_theta F μ a l r s hs φ hf))

omit [μ.IsHaarMeasure] in
/-- The radial support condition of Definition 9.3.3.1 gives compact
support on the global idele classes. -/
theorem ideleClass_radialCutoff_hasCompactSupport (R : ℝ) (hR : 0 < R)
    (ρ : IdeleClass F → ℝ) (hsupp : ∀ x, ideleClassNorm F x ∉ Icc R⁻¹ R → ρ x = 0) :
    HasCompactSupport ρ := by
  have hK := ideleClass_logNormBand_compact F (Real.log R⁻¹) (Real.log R)
  apply hK.of_isClosed_subset isClosed_closure
  apply closure_minimal _ hK.isClosed
  intro x hx
  have hband : ideleClassNorm F x ∈ Icc R⁻¹ R := by
    by_contra hn
    exact hx (hsupp x hn)
  exact ⟨(Real.log_le_log_iff (inv_pos.mpr hR) (ideleClassNorm_pos F x)).mpr hband.1,
    (Real.log_le_log_iff (ideleClassNorm_pos F x) hR).mpr hband.2⟩

/-- Total cutoff convolution is trace class for the full global compact
Schwartz–Bruhat test class, including cutoffs with jumps. -/
theorem globalHardySobolev_cutoff_traceClass (l r s : ℝ) (hs : 0 ≤ s)
    (φ : BruhatSchwartz (IdeleClass F)) (hφc : HasCompactSupport φ.val)
    (ρ : IdeleClass F → ℝ) (hρ : Measurable ρ) (hρc : HasCompactSupport ρ)
    (hρ₀ : ∀ x, 0 ≤ ρ x) (hρ₁ : ∀ x, ρ x ≤ 1) :
    let ψ : C_c(IdeleClass F, ℂ) := ⟨⟨φ.val, bruhatSchwartz_continuous φ⟩, hφc⟩
    ∃ U : TraceClass (Lp ℂ 2 μ), U.toOperator =
      (cutoffOperator ρ hρ hρ₀ hρ₁).comp (globalHardySobolevConvolution F μ l r s hs ψ) := by
  intro ψ
  letI : CompactSpace (normOneIdeleClass F) := normOneIdeleClass_compact F
  let m : IdeleClass F →ₜ* Multiplicative ℝ :=
    ⟨ideleClassLogNorm F, ideleClassLogNorm_continuous F⟩
  have hm : IsProperMap m :=
    isProperMap_snd_of_compactSpace.comp (ideleClassSplitHomeomorph F).isProperMap
  have hms : Function.Surjective m :=
    fun t => ⟨ideleClassExpSection F t, ideleClassLogNorm_expSection F t⟩
  obtain ⟨U, hU⟩ := bruhatHardySobolev_cutoff_traceClass μ m hm hms l r s hs φ hφc
    ρ hρ hρc hρ₀ hρ₁
  exact ⟨U, hU⟩

/-- Every finite cutoff in the convolution-after-projection order of
Theorem 10.4.2.8 is already trace class. -/
theorem globalConvolutionAfterProjection_cutoff_nuclear (a l r s : ℝ) (hs : 0 ≤ s)
    (φ : BruhatSchwartz (IdeleClass F)) (hφc : HasCompactSupport φ.val)
    (ρ : IdeleClass F → ℝ) (hρ : Measurable ρ) (hρc : HasCompactSupport ρ)
    (hρ₀ : ∀ x, 0 ≤ ρ x) (hρ₁ : ∀ x, ρ x ≤ 1) :
    let N := globalThetaSobolevCompletion F μ a l r s hs
    let ψ : C_c(IdeleClass F, ℂ) := ⟨⟨φ.val, bruhatSchwartz_continuous φ⟩, hφc⟩
    let A := globalHardySobolevConvolution F μ l r s hs ψ
    let M := cutoffOperator (μ := μ) ρ hρ hρ₀ hρ₁
    M.comp (A.comp Nᗮ.starProjection) ∈ nuclearOperators (Lp ℂ 2 μ) := by
  intro N ψ A M
  letI : IsClosed (N : Set (Lp ℂ 2 μ)) := thetaClosed F μ a l r s hs
  obtain ⟨U, hU⟩ := globalHardySobolev_cutoff_traceClass F μ l r s hs φ hφc ρ hρ hρc hρ₀ hρ₁
  change U.toOperator = M.comp A at hU
  rw [← ContinuousLinearMap.comp_assoc, ← hU]
  exact nuclearOperators_comp_right _ U.toOperator_mem

/-- Corrected Theorem 10.4.2.1. For the actual polar-free theta quotient,
trace-class spectral convolution gives the geometric and spectral trace
split for every compactly supported measurable cutoff in the unit interval. -/
theorem globalSpectralProjection_cutoff_trace_split (a l r s : ℝ) (hs : 0 ≤ s)
    (φ : BruhatSchwartz (IdeleClass F)) (hφc : HasCompactSupport φ.val)
    (ρ : IdeleClass F → ℝ) (hρ : Measurable ρ) (hρc : HasCompactSupport ρ)
    (hρ₀ : ∀ x, 0 ≤ ρ x) (hρ₁ : ∀ x, ρ x ≤ 1) :
    let N := globalThetaSobolevCompletion F μ a l r s hs
    let ψ : C_c(IdeleClass F, ℂ) := ⟨⟨φ.val, bruhatSchwartz_continuous φ⟩, hφc⟩
    let A := globalHardySobolevConvolution F μ l r s hs ψ
    let M := cutoffOperator (μ := μ) ρ hρ hρ₀ hρ₁
    ∀ Q : TraceClass (Lp ℂ 2 μ ⧸ N),
      Q.toOperator = globalSpectralConvolution F μ a l r s hs ψ →
      ∃ U T G S : TraceClass (Lp ℂ 2 μ),
        U.toOperator = M.comp A ∧ T.toOperator = Nᗮ.starProjection.comp A ∧
        G.toOperator = M.comp (N.starProjection.comp A) ∧
        S.toOperator = M.comp (Nᗮ.starProjection.comp A) ∧
        U.traceValue = G.traceValue + S.traceValue := by
  intro N ψ A M Q hQ
  letI : IsClosed (N : Set (Lp ℂ 2 μ)) := thetaClosed F μ a l r s hs
  obtain ⟨U, hU⟩ := globalHardySobolev_cutoff_traceClass F μ l r s hs φ hφc ρ hρ hρc hρ₀ hρ₁
  have hintertwine : N.mkQL.comp A = Q.toOperator.comp N.mkQL := by
    rw [hQ]
    rfl
  obtain ⟨T, G, S, hT, hG, hS, htrace⟩ :=
    spectralProjection_cutoff_trace_split N A M Q hintertwine U hU
  exact ⟨U, T, G, S, hU, hT, hG, hS, htrace⟩

/-- Corrected Proposition 10.4.2.4 for the actual global theta quotient.
The equality holds whenever spectral convolution is trace class. -/
theorem globalSpectralProjection_convolution_trace (a l r s : ℝ) (hs : 0 ≤ s)
    (φ : C_c(IdeleClass F, ℂ)) :
    let N := globalThetaSobolevCompletion F μ a l r s hs
    ∀ Q : TraceClass (Lp ℂ 2 μ ⧸ N),
      Q.toOperator = globalSpectralConvolution F μ a l r s hs φ →
      ∃ T : TraceClass (Lp ℂ 2 μ),
        T.toOperator = Nᗮ.starProjection.comp (globalHardySobolevConvolution F μ l r s hs φ) ∧
        T.traceValue = Q.traceValue := by
  intro N Q hQ
  letI : IsClosed (N : Set (Lp ℂ 2 μ)) := thetaClosed F μ a l r s hs
  apply spectralProjection_trace_of_quotient N _ Q
  rw [hQ]
  rfl

omit [μ.IsHaarMeasure] in
/-- The radial multiplier in the amplitude chart is conjugate to
multiplication on the actual weighted ambient Hilbert space. -/
theorem globalHardySobolevIso_cutoffOperator (l r s : ℝ)
    (ρ : IdeleClass F → ℝ) (hρ : Measurable ρ)
    (hρ₀ : ∀ x, 0 ≤ ρ x) (hρ₁ : ∀ x, ρ x ≤ 1)
    (f : Lp ℂ 2 (globalHardySobolevMeasure F μ l r s)) :
    globalHardySobolevIso F μ l r s (cutoffOperator ρ hρ hρ₀ hρ₁ f) =
      cutoffOperator ρ hρ hρ₀ hρ₁ (globalHardySobolevIso F μ l r s f) := by
  unfold globalHardySobolevIso
  exact amplitudeL2Iso_cutoffOperator μ _ _ _ ρ hρ hρ₀ hρ₁ f

/-- Corrected Theorem 10.4.2.2 for the actual global theta quotient. The
cutoffs are the manuscript's radial multipliers in amplitude coordinates. -/
theorem globalSpectralProjection_cutoff_trace_tendsto {ι : Type*} {l₀ : Filter ι}
    [l₀.IsCountablyGenerated] (a l r s : ℝ) (hs : 0 ≤ s)
    (φ : C_c(IdeleClass F, ℂ)) (radius margin : ι → ℝ)
    (hRadius : Tendsto radius l₀ atTop)
    (hMargin : Tendsto (fun i => margin i * radius i) l₀ (𝓝 0))
    (ρ : ι → IdeleClass F → ℝ) (hρ : ∀ i, Measurable (ρ i))
    (hρ₀ : ∀ i x, 0 ≤ ρ i x) (hρ₁ : ∀ i x, ρ i x ≤ 1)
    (hplateau : ∀ i x, (radius i)⁻¹ + margin i ≤ ideleClassNorm F x →
      ideleClassNorm F x ≤ radius i - margin i → ρ i x = 1) :
    let N := globalThetaSobolevCompletion F μ a l r s hs
    let A := globalHardySobolevConvolution F μ l r s hs φ
    ∀ Q : TraceClass (Lp ℂ 2 μ ⧸ N),
      Q.toOperator = globalSpectralConvolution F μ a l r s hs φ →
      ∃ T : TraceClass (Lp ℂ 2 μ), ∃ S : ι → TraceClass (Lp ℂ 2 μ),
        T.toOperator = Nᗮ.starProjection.comp A ∧
        (∀ i, (S i).toOperator =
          (cutoffOperator (ρ i) (hρ i) (hρ₀ i) (hρ₁ i)).comp (Nᗮ.starProjection.comp A)) ∧
        Tendsto S l₀ (𝓝 T) ∧ Tendsto (fun i => (S i).traceValue) l₀ (𝓝 Q.traceValue) := by
  intro N A Q hQ
  letI : IsClosed (N : Set (Lp ℂ 2 μ)) := thetaClosed F μ a l r s hs
  refine spectralProjection_cutoff_trace_tendsto μ N A Q ?_ ρ hρ hρ₀ hρ₁ ?_
  · rw [hQ]
    rfl
  · exact cutoff_eventually_eq_one radius margin hRadius hMargin ρ _
      (ideleClassNorm_pos F) hplateau

end

end Masullo
