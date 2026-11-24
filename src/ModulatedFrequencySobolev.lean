import ExponentialSchwartzCutoffs
import SobolevRadialApproximation
import CompactCharacterApproximation
import ModulatedBruhatStages
import ModulatedSobolevTests
import ModulatedCharacters
import ModulationSection
import LCAFourierIntegral
import LCAPlancherel
import LCAConvolution
import PontryaginSeparation
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Topology.Algebra.Module.Spaces.PointwiseConvergenceCLM
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

open Filter Function MeasureTheory Set Topology
open scoped Classical ContDiff ENNReal FourierTransform SchwartzMap TensorProduct

namespace Masullo

noncomputable section

/-- The canonical continuous inclusion of the real Schwartz space in the
zero-abscissa weighted logarithmic L² space. -/
def radialSchwartzSobolev (s : ℝ) : 𝓢(ℝ, ℂ) →L[ℂ] StripSobolev 0 0 s :=
  let I := amplitudeL2Iso (volume : Measure ℝ) (stripSobolevAmplitude 0 0 s)
    (stripSobolevAmplitude_continuous 0 0 s).measurable (stripSobolevAmplitude_pos 0 0 s)
  I.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp (weightedSchwartzL2 s)

theorem radialSchwartzSobolev_ae (s : ℝ) (f : 𝓢(ℝ, ℂ)) :
    (radialSchwartzSobolev s f : ℝ → ℂ) =ᵐ[stripMeasure 0 0 s] f := by
  let a := stripSobolevAmplitude 0 0 s
  have ha := (stripSobolevAmplitude_continuous 0 0 s).measurable
  have hp := stripSobolevAmplitude_pos 0 0 s
  let I := amplitudeL2Iso (volume : Measure ℝ) a ha hp
  change (I.symm (weightedSchwartzL2 s f) : ℝ → ℂ) =ᵐ[stripMeasure 0 0 s] f
  filter_upwards [amplitudeL2Iso_symm_ae volume a ha hp (weightedSchwartzL2 s f),
    (amplitudeMeasure_absolutelyContinuous volume a).ae_le (weightedSchwartzL2_ae s f)] with x hx hy
  rw [hx, hy]
  rw [smul_smul, show (1 + x ^ 2) ^ (s / 4) = a x by simp [a, stripSobolevAmplitude],
    inv_mul_cancel₀ (hp x).ne', one_smul]

section Group

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G]
  (m : G →ₜ* Multiplicative ℝ) [CompactSpace m.toMonoidHom.ker]
  (τ : Multiplicative ℝ →ₜ* G) (hτ : RightInverse τ m)

local notation "K" => m.toMonoidHom.ker

variable (ν : Measure m.toMonoidHom.ker) [IsFiniteMeasure ν]

private def splitSchwartzWindow (χ : PontryaginDual K) (p : 𝓢(ℝ, ℂ)) (g : G) : ℂ :=
  let q := (modulatedLogSplit m τ hτ).symm g
  (χ q.2 : ℂ) * p q.1

private def lpTwoProductCLM {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν] (u : Lp ℂ 2 μ) :
    Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 (μ.prod ν) :=
  ((lpTwoTensorIsometry (μ := μ) (ν := ν)).toLinearMap.comp
    (TensorProduct.mk ℂ (Lp ℂ 2 μ) (Lp ℂ 2 ν) u)).mkContinuous ‖u‖ (fun v => by
      change ‖lpTwoTensorIsometry (u ⊗ₜ[ℂ] v)‖ ≤ _
      rw [LinearIsometry.norm_map, TensorProduct.norm_tmul])

private def splitSchwartzWindowLp (s : ℝ) (χ : PontryaginDual K) :
    𝓢(ℝ, ℂ) →L[ℂ] Lp ℂ 2 (modulatedSobolevMeasure m τ hτ ν 0 s) :=
  (modulatedSobolevGroupEquiv m τ hτ ν 0 s).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((lpTwoProductCLM (compactCharacterLp ν χ)).comp (radialSchwartzSobolev s))

private theorem splitSchwartzWindowLp_ae (s : ℝ) (χ : PontryaginDual K) (p : 𝓢(ℝ, ℂ)) :
    (splitSchwartzWindowLp m τ hτ ν s χ p : G → ℂ) =ᵐ[modulatedSobolevMeasure m τ hτ ν 0 s]
      splitSchwartzWindow m τ hτ χ p := by
  let E := modulatedLogSplit m τ hτ
  let e := ((Homeomorph.prodComm K ℝ).trans E).toMeasurableEquiv
  have h : MeasurePreserving e (ν.prod (stripMeasure 0 0 s))
      (modulatedSobolevMeasure m τ hτ ν 0 s) :=
    (show MeasurePreserving E ((stripMeasure 0 0 s).prod ν)
      (Measure.map E ((stripMeasure 0 0 s).prod ν)) from
      ⟨E.continuous.measurable, rfl⟩).comp Measure.measurePreserving_swap
  let u := splitSchwartzWindowLp m τ hτ ν s χ p
  let v := lpTwoProduct (compactCharacterLp ν χ) (radialSchwartzSobolev s p)
  have he : (fun q => u (e q)) =ᵐ[ν.prod (stripMeasure 0 0 s)] v := by
    have he := (modulatedSobolevGroupEquiv_ae m τ hτ ν 0 s u).symm
    change (fun q => u (e q)) =ᵐ[ν.prod (stripMeasure 0 0 s)] (modulatedSobolevGroupEquiv m τ hτ ν 0 s u : K × ℝ → ℂ) at he
    exact he.trans (.of_forall fun q => by
      change modulatedSobolevGroupEquiv m τ hτ ν 0 s
        ((modulatedSobolevGroupEquiv m τ hτ ν 0 s).symm v) q = v q
      rw [LinearIsometryEquiv.apply_symm_apply])
  have hv : (v : K × ℝ → ℂ) =ᵐ[ν.prod (stripMeasure 0 0 s)] fun q =>
      (χ q.1 : ℂ) * p q.2 := by
    filter_upwards [lpTwoProduct_ae (compactCharacterLp ν χ) (radialSchwartzSobolev s p),
      Measure.quasiMeasurePreserving_fst.ae_eq_comp (compactCharacterLp_ae ν χ),
      Measure.quasiMeasurePreserving_snd.ae_eq_comp (radialSchwartzSobolev_ae s p)] with q hv hχ hp
    rw [hv]
    change compactCharacterLp ν χ q.1 * radialSchwartzSobolev s p q.2 = _
    rw [show compactCharacterLp ν χ q.1 = (χ q.1 : ℂ) from hχ,
      show radialSchwartzSobolev s p q.2 = p q.2 from hp]
  have hw (q : K × ℝ) : splitSchwartzWindow m τ hτ χ p (e q) = (χ q.1 : ℂ) * p q.2 := by
    change (χ ((modulatedLogSplit m τ hτ).symm
      ((modulatedLogSplit m τ hτ) (q.2, q.1))).2 : ℂ) *
      p ((modulatedLogSplit m τ hτ).symm ((modulatedLogSplit m τ hτ) (q.2, q.1))).1 = _
    rw [Homeomorph.symm_apply_apply]
  have hh := (he.trans hv).trans (.of_forall fun q => (hw q).symm)
  have hout := (h.symm e).quasiMeasurePreserving.ae_eq_comp hh
  filter_upwards [hout] with g hg
  change u (e (e.symm g)) = splitSchwartzWindow m τ hτ χ p (e (e.symm g)) at hg
  simpa only [MeasurableEquiv.apply_symm_apply] using hg

variable [ν.IsMulLeftInvariant]

private def radialFrequency (ψ : PontryaginDual G) : ℝ :=
  Multiplicative.toAdd (characterSlope τ ψ) / (2 * Real.pi)

private theorem splitSchwartzWindow_integrable (χ : PontryaginDual K) (p : 𝓢(ℝ, ℂ)) :
    Integrable (splitSchwartzWindow m τ hτ χ p) (modulatedLogMeasure m τ hτ ν) := by
  let e := (modulatedLogSplit m τ hτ).toMeasurableEquiv
  change Integrable _ (Measure.map e (volume.prod ν))
  rw [integrable_map_equiv]
  have he : splitSchwartzWindow m τ hτ χ p ∘ e =
      fun q : ℝ × K => p q.1 * (χ q.2 : ℂ) := by
    funext q
    change (χ ((modulatedLogSplit m τ hτ).symm ((modulatedLogSplit m τ hτ) q)).2 : ℂ) *
      p ((modulatedLogSplit m τ hτ).symm ((modulatedLogSplit m τ hτ) q)).1 = _
    rw [Homeomorph.symm_apply_apply, mul_comm]
  rw [he]
  have hχ : Integrable (fun k : K => (χ k : ℂ)) ν :=
    (continuous_subtype_val.comp χ.continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  exact p.integrable.mul_prod hχ

private theorem splitSchwartzWindow_fourier (χ : PontryaginDual K) (p : 𝓢(ℝ, ℂ))
    (ψ : PontryaginDual G) :
    lcaFourier (modulatedLogMeasure m τ hτ ν) (splitSchwartzWindow m τ hτ χ p) ψ =
      (𝓕 p) (radialFrequency τ ψ) *
        (if (show PontryaginDual K from (show CircleCharacter G from ψ).comp
          (modulatedKernelInclusion m)) = χ then (ν.real univ : ℂ) else 0) := by
  classical
  let e := (modulatedLogSplit m τ hτ).toMeasurableEquiv
  let η : PontryaginDual K := (show CircleCharacter G from ψ).comp (modulatedKernelInclusion m)
  unfold lcaFourier
  change (∫ g, splitSchwartzWindow m τ hτ χ p g * star (ψ g : ℂ)
      ∂Measure.map e (volume.prod ν)) = _
  rw [integral_map_equiv]
  have he : (fun q : ℝ × K => splitSchwartzWindow m τ hτ χ p (e q) * star (ψ (e q) : ℂ)) =
      fun q => (p q.1 * star (ψ (τ (Multiplicative.ofAdd q.1)) : ℂ)) *
        (star (η q.2 : ℂ) * (χ q.2 : ℂ)) := by
    funext q
    have he' : ψ (e q) = ψ (τ (Multiplicative.ofAdd q.1)) * η q.2 :=
      map_mul ψ _ _
    simp only [he', Circle.coe_mul, star_mul]
    have hW : splitSchwartzWindow m τ hτ χ p (e q) = (χ q.2 : ℂ) * p q.1 := by
      change (χ ((modulatedLogSplit m τ hτ).symm ((modulatedLogSplit m τ hτ) q)).2 : ℂ) *
        p ((modulatedLogSplit m τ hτ).symm ((modulatedLogSplit m τ hτ) q)).1 = _
      rw [Homeomorph.symm_apply_apply]
    rw [hW]
    ring
  rw [he]
  let F (x : ℝ) : ℂ := p x * star (ψ (τ (Multiplicative.ofAdd x)) : ℂ)
  let H (k : K) : ℂ := star (η k : ℂ) * (χ k : ℂ)
  change (∫ q : ℝ × K, F q.1 * H q.2 ∂volume.prod ν) = _
  rw [integral_prod_mul]
  have hH := integral_character_pair ν η χ
  change (∫ k, H k ∂ν) = _ at hH
  rw [hH]
  congr 1
  rw [SchwartzMap.fourier_coe, Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  refine .of_forall fun x => ?_
  have hψ : (ψ (τ (Multiplicative.ofAdd x)) : ℂ) =
      Complex.exp ((↑((Multiplicative.toAdd (characterSlope τ ψ) : ℝ) * x) : ℂ) * Complex.I) := by
    rw [← Circle.coe_exp]
    exact congrArg ((↑) : Circle → ℂ) (characterSlope_eq_exp τ ψ x)
  dsimp only [F]
  rw [hψ, Complex.star_def, ← Complex.exp_conj, smul_eq_mul, mul_comm (p x)]
  congr 3
  simp [radialFrequency]
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp [hπ, (Complex.ofReal_ne_zero.mpr hπ : (Real.pi : ℂ) ≠ 0)]


private def restrictToKernel (ψ : PontryaginDual G) : PontryaginDual K :=
  (show CircleCharacter G from ψ).comp (modulatedKernelInclusion m)

private theorem restrict_mul_modulus (ψ : PontryaginDual G) (t : ℝ) :
    restrictToKernel m (ψ * (show PontryaginDual G from modulusCharacter m t)) =
      restrictToKernel m ψ := by
  apply PontryaginDual.ext
  intro k
  change ψ k.val * Circle.exp (t * Multiplicative.toAdd (m k.val)) = ψ k.val
  rw [show m k.val = 1 from k.property]
  simp

include hτ in
private theorem frequency_mul_modulus (ψ : PontryaginDual G) (t : ℝ) :
    radialFrequency τ (ψ * (show PontryaginDual G from modulusCharacter m t)) =
      radialFrequency τ ψ + t / (2 * Real.pi) := by
  have hs : Multiplicative.toAdd (characterSlope τ (modulusCharacter m t)) = t := by
    apply characterSlope_unique
    intro x
    change Circle.exp (t * Multiplicative.toAdd (m (τ (Multiplicative.ofAdd x)))) = _
    rw [hτ]
    rfl
  change Multiplicative.toAdd (characterSlope τ
    ((show CircleCharacter G from ψ) * modulusCharacter m t)) / (2 * Real.pi) = _
  rw [map_mul]
  change (Multiplicative.toAdd (characterSlope τ ψ) +
    Multiplicative.toAdd (characterSlope τ (modulusCharacter m t))) / (2 * Real.pi) = _
  rw [hs, add_div]
  rfl

private theorem splitSchwartzWindow_fourier_support (χ : PontryaginDual G) (p : 𝓢(ℝ, ℂ))
    {α β : ℝ}
    (hp : tsupport ((𝓕 p : 𝓢(ℝ, ℂ)) : ℝ → ℂ) ⊆ Icc (radialFrequency τ χ + α / (2 * Real.pi))
      (radialFrequency τ χ + β / (2 * Real.pi))) :
    tsupport (lcaFourier (modulatedLogMeasure m τ hτ ν)
      (splitSchwartzWindow m τ hτ (restrictToKernel m χ) p)) ⊆
      modulatedFrequencyBand m (show CircleCharacter G from χ) α β := by
  apply closure_minimal _ (isCompact_modulatedFrequencyBand m χ α β).isClosed
  intro ψ hψ
  have hF := splitSchwartzWindow_fourier m τ hτ ν (restrictToKernel m χ) p ψ
  change lcaFourier (modulatedLogMeasure m τ hτ ν)
    (splitSchwartzWindow m τ hτ (restrictToKernel m χ) p) ψ =
      (𝓕 p) (radialFrequency τ ψ) *
        (if restrictToKernel m ψ = restrictToKernel m χ then (ν.real univ : ℂ) else 0) at hF
  have hne : lcaFourier (modulatedLogMeasure m τ hτ ν)
    (splitSchwartzWindow m τ hτ (restrictToKernel m χ) p) ψ ≠ 0 := hψ
  have hres : restrictToKernel m ψ = restrictToKernel m χ := by
    by_contra h
    apply hne
    rw [hF, ite_eq_right h, mul_zero]
  have hx : radialFrequency τ ψ ∈ tsupport ((𝓕 p : 𝓢(ℝ, ℂ)) : ℝ → ℂ) := by
    apply subset_closure
    intro h
    apply hne
    rw [hF, show (𝓕 p : 𝓢(ℝ, ℂ)) (radialFrequency τ ψ) = 0 from h, zero_mul]
  obtain ⟨t, ht⟩ := modulatedCharacter_eq_mul_modulus m τ hτ χ ψ hres
  have ht' : ψ = χ * (show PontryaginDual G from modulusCharacter m t) := ht
  have hbounds := hp hx
  rw [ht', frequency_mul_modulus m τ hτ] at hbounds
  have hπ : 0 < 2 * Real.pi := Real.two_pi_pos
  refine ⟨t, ⟨?_, ?_⟩, ht.symm⟩
  · exact (div_le_div_iff_of_pos_right hπ).mp ((add_le_add_iff_left _).mp hbounds.1)
  · exact (div_le_div_iff_of_pos_right hπ).mp ((add_le_add_iff_left _).mp hbounds.2)

private theorem splitSchwartzWindow_hasCompactSpectrum (χ : PontryaginDual K)
    (f : 𝓢(ℝ, ℂ)) (hc : HasCompactSupport ((𝓕 f : 𝓢(ℝ, ℂ)) : ℝ → ℂ)) :
    HasCompactSupport (lcaFourier (modulatedLogMeasure m τ hτ ν)
      (splitSchwartzWindow m τ hτ χ f)) := by
  obtain ⟨a, ha⟩ := hc.isCompact.bddBelow
  obtain ⟨b, hb⟩ := hc.isCompact.bddAbove
  let ψ : PontryaginDual G := extendModulatedCharacter m τ hτ χ
  have hψ : restrictToKernel m ψ = χ := extendModulatedCharacter_restrict m τ hτ χ
  let α := (a - radialFrequency τ ψ) * (2 * Real.pi)
  let β := (b - radialFrequency τ ψ) * (2 * Real.pi)
  have hπ : 2 * Real.pi ≠ 0 := Real.two_pi_pos.ne'
  have ha' : radialFrequency τ ψ + α / (2 * Real.pi) = a := by
    dsimp [α]
    rw [mul_div_cancel_right₀ _ hπ]
    ring
  have hb' : radialFrequency τ ψ + β / (2 * Real.pi) = b := by
    dsimp [β]
    rw [mul_div_cancel_right₀ _ hπ]
    ring
  apply (isCompact_modulatedFrequencyBand m ψ α β).of_isClosed_subset isClosed_closure
  rw [← hψ]
  apply splitSchwartzWindow_fourier_support m τ hτ ν ψ f
  rw [ha', hb']
  exact fun _ hx => ⟨ha hx, hb hx⟩


/-- The physical Sobolev classes represented by an integrable function
whose Fourier integral has compact support. -/
def compactSpectrumSobolevSubmodule (s : ℝ) :
    Submodule ℂ (Lp ℂ 2 (modulatedSobolevMeasure m τ hτ ν 0 s)) where
  carrier := {u | ∃ f : G → ℂ, Integrable f (modulatedLogMeasure m τ hτ ν) ∧
    HasCompactSupport (lcaFourier (modulatedLogMeasure m τ hτ ν) f) ∧
    (u : G → ℂ) =ᵐ[modulatedSobolevMeasure m τ hτ ν 0 s] f}
  zero_mem' := by
    have hF : lcaFourier (modulatedLogMeasure m τ hτ ν) (0 : G → ℂ) = 0 := by
      funext ψ
      simp [lcaFourier]
    exact ⟨0, integrable_zero .., hF ▸ HasCompactSupport.zero, Lp.coeFn_zero ..⟩
  add_mem' := by
    rintro u v ⟨f, hf, hcf, hef⟩ ⟨g, hg, hcg, heg⟩
    let μ := modulatedLogMeasure m τ hτ ν
    have hF : lcaFourier μ (f + g) = lcaFourier μ f + lcaFourier μ g := by
      funext ψ
      unfold lcaFourier
      simp_rw [Pi.add_apply, add_mul]
      exact integral_add (integrable_fourierIntegrand μ hf ψ) (integrable_fourierIntegrand μ hg ψ)
    refine ⟨f + g, hf.add hg, hF ▸ hcf.add hcg, ?_⟩
    exact (Lp.coeFn_add u v).trans (hef.add heg)
  smul_mem' := by
    rintro c u ⟨f, hf, hcf, hef⟩
    let μ := modulatedLogMeasure m τ hτ ν
    have hF : lcaFourier μ (c • f) = c • lcaFourier μ f := by
      funext ψ
      simp only [lcaFourier, Pi.smul_apply, smul_mul_assoc, integral_smul]
    refine ⟨c • f, hf.smul c, hF ▸ hcf.smul_left, ?_⟩
    exact (Lp.coeFn_smul c u).trans (hef.const_smul c)

/-- Corollary 9.3.2.3(2). Compact frequency support is dense for the
zero-abscissa Sobolev norm. Each separated test is approximated in that
norm by Fourier truncations of its radial Schwartz profile. -/
theorem dense_compactSpectrumSobolev [ν.WeaklyRegular] (s : ℝ) :
    Dense (compactSpectrumSobolevSubmodule m τ hτ ν s :
      Set (Lp ℂ 2 (modulatedSobolevMeasure m τ hτ ν 0 s))) := by
  let W := compactSpectrumSobolevSubmodule m τ hτ ν s
  let V := modulatedGroupCutoff m τ hτ ν 0 s univ
  let j : V →L[ℂ] Lp ℂ 2 (modulatedSobolevMeasure m τ hτ ν 0 s) := V.subtypeL
  have hs : Surjective j := by
    intro u
    exact ⟨⟨u, (modulatedGroupCutoff_mem_iff m τ hτ ν 0 s univ u).mpr
      (.of_forall fun _ h => (h (mem_univ _)).elim)⟩, rfl⟩
  let T (p : PontryaginDual K × compactRadialTests (univ : Set ℝ)) : V :=
    modulatedGroupSeparatedTest m τ hτ ν 0 s isOpen_univ p.1 p.2
  have hd := hs.denseRange.topologicalClosure_map_submodule (f := j)
    (modulatedGroupSeparatedTest_dense m τ hτ ν 0 s (U := univ) isOpen_univ)
  change ((Submodule.span ℂ (range T)).map j.toLinearMap).topologicalClosure = ⊤ at hd
  rw [Submodule.map_span, ← range_comp] at hd
  have hχ (χ : PontryaginDual K) (f : compactRadialTests (univ : Set ℝ)) :
      j (T (χ, f)) ∈ W.topologicalClosure := by
    let p := logExponentialDecayTwist univ ⟨0, mem_univ 0⟩ f.val
    have hp (x : ℝ) : p x = f.val.val x := by
      simpa [p] using logExponentialDecayTwist_apply univ ⟨0, mem_univ 0⟩ f.val x
    let J := splitSchwartzWindowLp m τ hτ ν s χ
    have he : J p = j (T (χ, f)) := by
      apply (modulatedSobolevGroupEquiv m τ hτ ν 0 s).injective
      apply Lp.ext
      have h₁ := modulatedSobolevGroupEquiv_ae m τ hτ ν 0 s (J p)
      have h₂ := modulatedSobolevGroupEquiv_ae m τ hτ ν 0 s (j (T (χ, f)))
      let E := modulatedLogSplit m τ hτ
      let e := ((Homeomorph.prodComm K ℝ).trans E).toMeasurableEquiv
      have h : MeasurePreserving e (ν.prod (stripMeasure 0 0 s))
          (modulatedSobolevMeasure m τ hτ ν 0 s) :=
        (show MeasurePreserving E ((stripMeasure 0 0 s).prod ν)
          (Measure.map E ((stripMeasure 0 0 s).prod ν)) from
          ⟨E.continuous.measurable, rfl⟩).comp Measure.measurePreserving_swap
      filter_upwards [h₁, h₂, h.quasiMeasurePreserving.ae_eq_comp
        (splitSchwartzWindowLp_ae m τ hτ ν s χ p),
        modulatedGroupSeparatedTest_ae m τ hτ ν 0 s isOpen_univ χ f] with q hJ hT hJ' hT'
      change (modulatedSobolevGroupEquiv m τ hτ ν 0 s (J p)) q =
        (modulatedSobolevGroupEquiv m τ hτ ν 0 s (j (T (χ, f)))) q
      rw [hJ, hT]
      change (J p) (e q) = (j (T (χ, f))) (e q)
      change (J p) (e q) = splitSchwartzWindow m τ hτ χ p (e q) at hJ'
      rw [hJ']
      change (χ (E.symm (E (q.2, q.1))).2 : ℂ) * p (E.symm (E (q.2, q.1))).1 =
        (modulatedGroupSeparatedTest m τ hτ ν 0 s isOpen_univ χ f).val (e q)
      rw [Homeomorph.symm_apply_apply, hp]
      exact hT'.symm
    rw [← he]
    apply mem_closure_of_tendsto (J.continuous.continuousAt.tendsto.comp (fourierWindow_tendsto p))
    exact .of_forall fun n => ⟨_, splitSchwartzWindow_integrable m τ hτ ν χ (fourierWindow p n),
      splitSchwartzWindow_hasCompactSpectrum m τ hτ ν χ _ (fourierWindow_hasCompactSpectrum p n),
      splitSchwartzWindowLp_ae m τ hτ ν s χ (fourierWindow p n)⟩
  have hle : Submodule.span ℂ (range (j ∘ T)) ≤ W.topologicalClosure := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨χ, f⟩, rfl⟩
    exact hχ χ f
  have htop := Submodule.topologicalClosure_minimal _ hle W.isClosed_topologicalClosure
  change (Submodule.span ℂ (range (j.toLinearMap ∘ T))).topologicalClosure ≤ W.topologicalClosure at htop
  rw [hd] at htop
  exact dense_iff_closure_eq.mpr (by rw [← Submodule.topologicalClosure_coe, top_le_iff.mp htop,
    Submodule.top_coe])

/-- Corollary 9.3.2.3(1). The smooth frequency cutoff is the Fourier
transform of an actual weighted Sobolev class for every real degree.
The scalar normalization uses the total mass of kernel Haar. -/
theorem exists_sobolev_frequencyBand_cutoff (hν : ν.real univ ≠ 0) (s : ℝ)
    (χ : PontryaginDual G) {α β ε : ℝ} (hε : 0 < ε) (hwidth : α + ε < β - ε) :
    ∃ (u : Lp ℂ 2 (modulatedSobolevMeasure m τ hτ ν 0 s)) (f : G → ℂ),
      (u : G → ℂ) =ᵐ[modulatedSobolevMeasure m τ hτ ν 0 s] f ∧
      Integrable f (modulatedLogMeasure m τ hτ ν) ∧
      let F := lcaFourier (modulatedLogMeasure m τ hτ ν) f
      tsupport F ⊆ modulatedFrequencyBand m (show CircleCharacter G from χ) α β ∧
      HasCompactSupport F ∧
      EqOn F 1 (modulatedFrequencyBand m (show CircleCharacter G from χ) (α + ε) (β - ε)) ∧
      ∀ ψ : PontryaginDual G, ContDiff ℝ ∞
        (fun t => F (ψ * (show PontryaginDual G from modulusCharacter m t))) := by
  let q := 2 * Real.pi
  have hq : 0 < q := Real.two_pi_pos
  let a := radialFrequency τ χ + α / q
  let b := radialFrequency τ χ + β / q
  let δ := ε / q
  have hδ : 0 < δ := div_pos hε hq
  have hab : a + δ < b - δ := by
    dsimp [a, b, δ]
    rw [add_assoc, ← add_div, add_sub_assoc, ← sub_div, add_lt_add_iff_left]
    exact (div_lt_div_iff_of_pos_right hq).mpr hwidth
  let center := (a + b) / 2
  let radius := (b - a) / 2
  let bump : ContDiffBump center := ⟨radius - δ, radius,
    by dsimp [radius]; linarith, by linarith⟩
  let B : 𝓢(ℝ, ℂ) :=
    (bump.hasCompactSupport.comp_left Complex.ofReal_zero).toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp bump.contDiff)
  have hB (x : ℝ) : B x = (bump x : ℂ) := rfl
  have hbc : tsupport (B : ℝ → ℂ) ⊆ Icc a b := by
    apply closure_minimal _ isClosed_Icc
    intro x hx
    have hxe : bump x ≠ 0 := by
      intro h
      exact hx (by rw [hB, h, Complex.ofReal_zero])
    have hm : x ∈ Metric.ball center radius := by
      rw [← bump.support_eq]
      exact hxe
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hm
    dsimp [center, radius] at hm
    exact ⟨by linarith [hm.1], by linarith [hm.2]⟩
  have hplateau (x : ℝ) (hx : x ∈ Icc (a + δ) (b - δ)) : B x = 1 := by
    rw [hB, bump.one_of_mem_closedBall, Complex.ofReal_one]
    rw [Metric.mem_closedBall, Real.dist_eq, abs_le]
    change -(radius - δ) ≤ x - center ∧ x - center ≤ radius - δ
    dsimp [center, radius]
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  let p : 𝓢(ℝ, ℂ) := 𝓕⁻ B
  have hF : 𝓕 p = B := FourierTransform.fourier_fourierInv_eq B
  let kernelChar := restrictToKernel m χ
  let c : ℂ := ν.real univ
  have hc : c ≠ 0 := Complex.ofReal_ne_zero.mpr hν
  let u := c⁻¹ • splitSchwartzWindowLp m τ hτ ν s kernelChar p
  let f := c⁻¹ • splitSchwartzWindow m τ hτ kernelChar p
  refine ⟨u, f, (Lp.coeFn_smul _ _).trans
    ((splitSchwartzWindowLp_ae m τ hτ ν s kernelChar p).const_smul _),
    (splitSchwartzWindow_integrable m τ hτ ν kernelChar p).smul _, ?_⟩
  let μ := modulatedLogMeasure m τ hτ ν
  have hscale : lcaFourier μ f = c⁻¹ • lcaFourier μ (splitSchwartzWindow m τ hτ kernelChar p) := by
    funext ψ
    simp only [lcaFourier, f, Pi.smul_apply, smul_mul_assoc, integral_smul]
  have hsupport : tsupport (lcaFourier μ f) ⊆ modulatedFrequencyBand m (show CircleCharacter G from χ) α β := by
    rw [hscale]
    exact (tsupport_smul_subset_right (fun _ : PontryaginDual G => c⁻¹) _).trans
      (splitSchwartzWindow_fourier_support m τ hτ ν χ p (by rw [hF]; exact hbc))
  have hpoint (ψ : PontryaginDual G) :
      lcaFourier μ f ψ = if restrictToKernel m ψ = kernelChar then B (radialFrequency τ ψ) else 0 := by
    rw [hscale, Pi.smul_apply, splitSchwartzWindow_fourier, hF]
    change c⁻¹ * (B (radialFrequency τ ψ) * (if restrictToKernel m ψ = kernelChar then c else 0)) = _
    split
    · rw [mul_comm (B _), ← mul_assoc, inv_mul_cancel₀ hc, one_mul]
    · simp
  refine ⟨hsupport, (isCompact_modulatedFrequencyBand m χ α β).of_isClosed_subset isClosed_closure
    hsupport, ?_, ?_⟩
  · rintro _ ⟨t, ht, rfl⟩
    change lcaFourier μ f (χ * (show PontryaginDual G from modulusCharacter m t)) = 1
    rw [hpoint, restrict_mul_modulus, ite_eq_left rfl, frequency_mul_modulus m τ hτ]
    apply hplateau
    constructor
    · have h := (div_le_div_iff_of_pos_right hq).mpr ht.1
      dsimp [a, δ]
      rw [add_div] at h
      linarith
    · have h := (div_le_div_iff_of_pos_right hq).mpr ht.2
      dsimp [b, δ]
      rw [sub_div] at h
      linarith
  · intro ψ
    have he : (fun t => lcaFourier μ f (ψ *
        (show PontryaginDual G from modulusCharacter m t))) =
        fun t => if restrictToKernel m ψ = kernelChar then
          B (radialFrequency τ ψ + t / (2 * Real.pi)) else 0 := by
      funext t
      rw [hpoint, restrict_mul_modulus, frequency_mul_modulus m τ hτ]
    rw [he]
    by_cases h : restrictToKernel m ψ = kernelChar
    · simp only [ite_eq_left h]
      exact (B.smooth ⊤).comp (by fun_prop)
    · simp only [ite_eq_right h]
      exact contDiff_const

private theorem splitCharacterSum_hasCompactSpectrum
    (c : PontryaginDual K →₀ ℂ) (p : 𝓢(ℝ, ℂ))
    (hp : HasCompactSupport ((𝓕 p : 𝓢(ℝ, ℂ)) : ℝ → ℂ)) :
    HasCompactSupport (lcaFourier (modulatedLogMeasure m τ hτ ν)
      (fun x => c.sum fun χ a => a * splitSchwartzWindow m τ hτ χ p x)) := by
  classical
  let μ := modulatedLogMeasure m τ hτ ν
  let F (χ : PontryaginDual K) := lcaFourier μ (splitSchwartzWindow m τ hτ χ p)
  have hcts (S : Finset (PontryaginDual K)) : HasCompactSupport (∑ χ ∈ S, c χ • F χ) := by
    induction S using Finset.induction_on with
    | empty => rw [Finset.sum_empty]; exact HasCompactSupport.zero
    | insert χ S hn ih =>
      rw [Finset.sum_insert hn]
      exact ((splitSchwartzWindow_hasCompactSpectrum m τ hτ ν χ p hp).smul_left).add ih
  convert hcts c.support using 1
  funext ψ
  change (∫ x, (∑ χ ∈ c.support, c χ * splitSchwartzWindow m τ hτ χ p x) * star (ψ x : ℂ) ∂μ) = _
  simp_rw [Finset.sum_mul]
  rw [integral_finsetSum]
  · simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, F, lcaFourier, ← integral_const_mul, mul_assoc]
  · intro χ _
    have h := integrable_fourierIntegrand μ (splitSchwartzWindow_integrable m τ hτ ν χ p) ψ
    simpa only [mul_assoc] using h.const_mul (c χ)

private theorem splitCharacterSum_mem_bruhatSchwartz [LocallyCompactSpace G] (hm : IsProperMap m)
    (c : PontryaginDual K →₀ ℂ) (p : 𝓢(ℝ, ℂ)) :
    (fun x => c.sum fun χ a => a * splitSchwartzWindow m τ hτ χ p x) ∈ bruhatSchwartzSubmodule (G := G) := by
  classical
  let E := bruhatSchwartzSubmodule (G := G)
  have hχ (χ : PontryaginDual K) : splitSchwartzWindow m τ hτ χ p ∈ E := by
    let ψ : PontryaginDual G := extendModulatedCharacter m τ hτ χ
    have he (g : G) : splitSchwartzWindow m τ hτ χ p g = p (m g).toAdd * (ψ g : ℂ) := by
      change (ψ g : ℂ) * p (m g).toAdd = _
      exact mul_comm _ _
    simp_rw [show splitSchwartzWindow m τ hτ χ p = fun g => p (m g).toAdd * (ψ g : ℂ) from funext he]
    exact modulatedBruhat_radialCharacter_mem m hm hτ.surjective ψ p
  have he : (fun x => c.sum (fun χ a => a * splitSchwartzWindow m τ hτ χ p x)) =
      ∑ χ ∈ c.support, c χ • splitSchwartzWindow m τ hτ χ p := by
    funext x
    simp only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [he]
  exact E.sum_mem (fun χ _ => E.smul_mem _ (hχ χ))

omit [T2Space G] [ν.IsMulLeftInvariant] in
private theorem log_split_apply (q : ℝ × K) : modulatedLog m (modulatedLogSplit m τ hτ q) = q.1 := by
  change (m (τ (Multiplicative.ofAdd q.1) * q.2.val)).toAdd = q.1
  rw [map_mul, hτ, show m q.2.val = 1 from q.2.property, mul_one]
  rfl

/-- Split Haar groups admit kernels with finite character support in the
compact coordinate and compact Fourier support in the real coordinate. -/
theorem exists_splitSobolev_approximate_kernel [LocallyCompactSpace G] [IsProbabilityMeasure ν] [ν.IsOpenPosMeasure]
    (hm : IsProperMap m) (s : ℝ) (hs : 0 ≤ s) {U : Set G} (hU : IsOpen U) (h1 : (1 : G) ∈ U)
    {ε : ℝ} (hε : 0 < ε) :
    let μ := modulatedLogMeasure m τ hτ ν
    ∃ f : G → ℂ, Continuous f ∧ f ∈ bruhatSchwartzSubmodule (G := G) ∧ Integrable f μ ∧
      Integrable (fun g => ‖f g‖ * radialSobolevTailWeight s (modulatedLog m g)) μ ∧
      HasCompactSupport (lcaFourier μ f) ∧ (∫ g, f g ∂μ) = 1 ∧ (∫ g, ‖f g‖ ∂μ) < 1 + ε ∧
      (∫ g in Uᶜ, ‖f g‖ * radialSobolevTailWeight s (modulatedLog m g) ∂μ) < ε := by
  classical
  let μ := modulatedLogMeasure m τ hτ ν
  let e := (modulatedLogSplit m τ hτ).toMeasurableEquiv
  have he1 : e (0, 1) = 1 := by
    change τ (Multiplicative.ofAdd 0) * ((1 : K) : G) = 1
    change τ 1 * 1 = 1
    simp
  have hopen : IsOpen (e ⁻¹' U) := hU.preimage (modulatedLogSplit m τ hτ).continuous
  have hn := hopen.mem_nhds (show (0, 1) ∈ e ⁻¹' U by change e (0, 1) ∈ U; rwa [he1])
  rw [nhds_prod_eq] at hn
  obtain ⟨A, hA, W, hW, hAW⟩ := Filter.mem_prod_iff.mp hn
  obtain ⟨δ, hδ, hV⟩ := Metric.mem_nhds_iff.mp hA
  obtain ⟨Z, hZW, hZo, hZ1⟩ := mem_nhds_iff.mp hW
  let V := Metric.ball (0 : ℝ) δ
  have hVZ : V ×ˢ Z ⊆ e ⁻¹' U := (Set.prod_mono hV hZW).trans hAW
  let η := min 1 (ε / 8)
  have hη : 0 < η := lt_min zero_lt_one (by positivity)
  have hη1 : η ≤ 1 := min_le_left _ _
  have hηε : η ≤ ε / 8 := min_le_right _ _
  obtain ⟨p, hpF, hpm, hpn, hpt⟩ := exists_bandlimited_radialSobolev_kernel s hs hδ hη
  let a (t : ℝ) := ‖p t‖ * radialSobolevTailWeight s t
  have ha : Integrable a volume := integrable_radialSobolevTailWeight s hs p
  have ha0 (t : ℝ) : 0 ≤ a t := by dsimp [a, radialSobolevTailWeight]; positivity
  let L := ∫ t, a t
  have hL : 0 ≤ L := integral_nonneg ha0
  let ζ := η / (L + 1)
  have hζ : 0 < ζ := div_pos hη (by positivity)
  have hζle : ζ ≤ η := (div_le_iff₀ (by positivity : 0 < L + 1)).mpr (by nlinarith)
  have hζL : ζ * L ≤ η := by
    calc
      ζ * L ≤ ζ * (L + 1) := mul_le_mul_of_nonneg_left (by linarith) hζ.le
      _ = η := div_mul_cancel₀ _ (by positivity : L + 1 ≠ 0)
  obtain ⟨c, hqm, hqn, hqt⟩ := exists_kernelCharacter_approximation ν hZo hZ1 hζ
  let q (x : K) := c.sum fun χ b => b * (χ x : ℂ)
  change (∫ x, q x ∂ν) = 1 at hqm
  change (∫ x, ‖q x‖ ∂ν) < 1 + ζ at hqn
  change (∫ x in Zᶜ, ‖q x‖ ∂ν) < ζ at hqt
  have hqc : Continuous q := by
    unfold q Finsupp.sum
    exact continuous_finsetSum _ fun χ _ => continuous_const.mul (continuous_subtype_val.comp χ.continuous)
  have hqi : Integrable q ν := hqc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let f (x : G) := p (e.symm x).1 * q (e.symm x).2
  have hfc : Continuous f := (p.continuous.comp (continuous_fst.comp (modulatedLogSplit m τ hτ).symm.continuous)).mul
    (hqc.comp (continuous_snd.comp (modulatedLogSplit m τ hτ).symm.continuous))
  have hfe (z : ℝ × K) : f (e z) = p z.1 * q z.2 := by
    change p (e.symm (e z)).1 * q (e.symm (e z)).2 = _
    rw [e.symm_apply_apply]
  have hmeasure : MeasurePreserving e ((volume : Measure ℝ).prod ν) μ := ⟨e.measurable, rfl⟩
  have hWgt (z : ℝ × K) : ‖f (e z)‖ * radialSobolevTailWeight s (modulatedLog m (e z)) = a z.1 * ‖q z.2‖ := by
    rw [hfe, norm_mul, show modulatedLog m (e z) = z.1 from log_split_apply m τ hτ z]
    dsimp [a]
    ring
  have hi : Integrable f μ := by
    rw [← hmeasure.map_eq, integrable_map_equiv]
    exact (p.integrable.mul_prod hqi).congr (.of_forall fun z => (hfe z).symm)
  have hiW : Integrable (fun g => ‖f g‖ * radialSobolevTailWeight s (modulatedLog m g)) μ := by
    rw [← hmeasure.map_eq, integrable_map_equiv]
    exact (ha.mul_prod hqi.norm).congr (.of_forall fun z => (hWgt z).symm)
  have hf : f = fun x => c.sum fun χ b => b * splitSchwartzWindow m τ hτ χ p x := by
      funext x
      change p (e.symm x).1 * _ = _
      unfold q Finsupp.sum
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro χ _
      change p (e.symm x).1 * (c χ * (χ (e.symm x).2 : ℂ)) =
        c χ * ((χ (e.symm x).2 : ℂ) * p (e.symm x).1)
      ring
  refine ⟨f, hfc, hf ▸ splitCharacterSum_mem_bruhatSchwartz m τ hτ hm c p, hi, hiW, ?_, ?_, ?_, ?_⟩
  · rw [hf]
    exact splitCharacterSum_hasCompactSpectrum m τ hτ ν c p hpF
  · change (∫ g, f g ∂μ) = 1
    rw [← hmeasure.map_eq, integral_map_equiv]
    simp_rw [hfe]
    rw [integral_prod_mul, hpm, hqm, one_mul]
  · change (∫ g, ‖f g‖ ∂μ) < 1 + ε
    rw [← hmeasure.map_eq, integral_map_equiv]
    simp_rw [hfe, norm_mul]
    rw [integral_prod_mul (fun t : ℝ => ‖p t‖) (fun x : K => ‖q x‖)]
    have hq0 : 0 ≤ ∫ x, ‖q x‖ ∂ν := integral_nonneg (fun x => norm_nonneg (q x))
    have hpn' : (∫ t, ‖p t‖) ≤ 1 + η := hpn.le
    have hqn' : (∫ x, ‖q x‖ ∂ν) ≤ 1 + η := hqn.le.trans (by linarith)
    calc
      _ ≤ (1 + η) * (1 + η) := mul_le_mul hpn' hqn' hq0 (by positivity)
      _ < 1 + ε := by nlinarith [mul_le_mul_of_nonneg_left hη1 hη.le]
  · change (∫ g in Uᶜ, ‖f g‖ * radialSobolevTailWeight s (modulatedLog m g) ∂μ) < ε
    rw [← hmeasure.map_eq, setIntegral_map_equiv e]
    simp_rw [hWgt, preimage_compl]
    let R := (e ⁻¹' U)ᶜ
    have hR : MeasurableSet R := hopen.measurableSet.compl
    let P := (volume : Measure ℝ).prod ν
    let F (z : ℝ × K) := a z.1 * ‖q z.2‖
    let a' := Vᶜ.indicator a
    let b' := Zᶜ.indicator (fun x => ‖q x‖)
    have ha' : Integrable a' volume := ha.indicator Metric.isOpen_ball.measurableSet.compl
    have hb' : Integrable b' ν := hqi.norm.indicator hZo.measurableSet.compl
    have hFi : Integrable F P := ha.mul_prod hqi.norm
    rw [← integral_indicator hR]
    calc
      _ ≤ ∫ z, a' z.1 * ‖q z.2‖ + a z.1 * b' z.2 ∂P := by
        apply integral_mono (hFi.indicator hR) ((ha'.mul_prod hqi.norm).add (ha.mul_prod hb'))
        intro z
        change R.indicator F z ≤ a' z.1 * ‖q z.2‖ + a z.1 * b' z.2
        have ha0' : 0 ≤ a' z.1 := indicator_nonneg (fun x _ => ha0 x) _
        have hb0' : 0 ≤ b' z.2 := indicator_nonneg (fun _ _ => norm_nonneg _) _
        by_cases hz : z ∈ R
        · rw [indicator_of_mem hz]
          change a z.1 * ‖q z.2‖ ≤ _
          by_cases hx : z.1 ∈ V
          · have hnot : z.2 ∉ Z := fun hy => hz (hVZ ⟨hx, hy⟩)
            rw [show b' z.2 = ‖q z.2‖ from indicator_of_mem hnot _]
            exact le_add_of_nonneg_left (mul_nonneg ha0' (norm_nonneg _))
          · rw [show a' z.1 = a z.1 from indicator_of_mem hx _]
            exact le_add_of_nonneg_right (mul_nonneg (ha0 _) hb0')
        · rw [indicator_of_notMem hz]
          exact add_nonneg (mul_nonneg ha0' (norm_nonneg _)) (mul_nonneg (ha0 _) hb0')
      _ = (∫ t in Vᶜ, a t) * (∫ x, ‖q x‖ ∂ν) + L * (∫ x in Zᶜ, ‖q x‖ ∂ν) := by
        rw [integral_add (ha'.mul_prod hqi.norm) (ha.mul_prod hb')]
        rw [integral_prod_mul a b', integral_prod_mul a' (fun x : K => ‖q x‖),
          integral_indicator Metric.isOpen_ball.measurableSet.compl, integral_indicator hZo.measurableSet.compl]
      _ < ε := by
        have hq0 : 0 ≤ ∫ x, ‖q x‖ ∂ν := integral_nonneg (fun x => norm_nonneg (q x))
        have hq2 : (∫ x, ‖q x‖ ∂ν) ≤ 2 := hqn.le.trans (by linarith)
        have hleft := mul_le_mul hpt.le hq2 hq0 hη.le
        have hright := mul_le_mul_of_nonneg_left hqt.le hL
        nlinarith

end Group

section Haar

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
  (m : G →ₜ* Multiplicative ℝ)
  (μ : Measure G) [μ.IsHaarMeasure]

private theorem exists_modulatedLogMeasure_eq_smul [CompactSpace m.toMonoidHom.ker]
    (τ : Multiplicative ℝ →ₜ* G) (hτ : RightInverse τ m) :
    ∃ κ : Measure m.toMonoidHom.ker,
      κ.IsHaarMeasure ∧ IsProbabilityMeasure κ ∧
      ∃ c : NNReal, c ≠ 0 ∧ μ = c • modulatedLogMeasure m τ hτ κ := by
  let K₀ : TopologicalSpace.PositiveCompacts (↥m.toMonoidHom.ker) :=
    ⟨⟨univ, isCompact_univ⟩, by rw [interior_univ]; exact univ_nonempty⟩
  let κ₀ := Measure.haarMeasure K₀
  haveI : IsProbabilityMeasure κ₀ := ⟨Measure.haarMeasure_self (K₀ := K₀)⟩
  let ρ := modulatedLogMeasure m τ hτ κ₀
  haveI : ρ.IsHaarMeasure := modulatedLogMeasure_isHaar m τ hτ κ₀
  let c := Measure.haarScalarFactor μ ρ
  have hc : c ≠ 0 := (Measure.haarScalarFactor_pos_of_isHaarMeasure μ ρ).ne'
  exact ⟨κ₀, inferInstance, inferInstance, c, hc, Measure.isMulLeftInvariant_eq_smul μ ρ⟩

private theorem exists_modulatedLogMeasure_eq_haar [CompactSpace m.toMonoidHom.ker]
    (τ : Multiplicative ℝ →ₜ* G) (hτ : RightInverse τ m) :
    ∃ κ : Measure m.toMonoidHom.ker,
      κ.IsHaarMeasure ∧ modulatedLogMeasure m τ hτ κ = μ := by
  obtain ⟨κ, hκ, hprob, c, hc, he⟩ := exists_modulatedLogMeasure_eq_smul m μ τ hτ
  letI := hκ
  refine ⟨c • κ, Measure.IsHaarMeasure.nnreal_smul κ hc, ?_⟩
  calc
    modulatedLogMeasure m τ hτ (c • κ) = c • modulatedLogMeasure m τ hτ κ := by
      unfold modulatedLogMeasure
      rw [Measure.prod_smul_right, Measure.map_smul]
    _ = μ := he.symm

/-- The logarithmic pushforward of any Haar measure is a positive multiple
of Lebesgue measure. -/
theorem exists_modulatedLog_pushforward_eq_smul (hm : IsProperMap m) (hms : Surjective m) :
    ∃ c : NNReal, c ≠ 0 ∧ Measure.map (modulatedLog m) μ = c • (volume : Measure ℝ) := by
  letI := compactSpace_realModulation_ker m hm
  obtain ⟨τ, hτ⟩ := exists_realModulation_section m hm hms
  obtain ⟨κ, _, hκprob, c, hc, he⟩ := exists_modulatedLogMeasure_eq_smul m μ τ hτ
  letI := hκprob
  exact ⟨c, hc, by rw [he, Measure.map_smul, modulatedLogMeasure_log_pushforward m τ hτ κ]⟩

/-- The combined character and radial kernels work with the prescribed
Haar measure on every second-countable positive-real modulated group. -/
theorem exists_haarSobolev_approximate_kernel (hm : IsProperMap m) (hms : Surjective m)
    (s : ℝ) (hs : 0 ≤ s) {U : Set G} (hU : IsOpen U) (h1 : (1 : G) ∈ U)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ f : G → ℂ, Continuous f ∧ f ∈ bruhatSchwartzSubmodule (G := G) ∧ Integrable f μ ∧
      Integrable (fun g => ‖f g‖ * radialSobolevTailWeight s (modulatedLog m g)) μ ∧
      HasCompactSupport (lcaFourier μ f) ∧ (∫ g, f g ∂μ) = 1 ∧ (∫ g, ‖f g‖ ∂μ) < 1 + ε ∧
      (∫ g in Uᶜ, ‖f g‖ * radialSobolevTailWeight s (modulatedLog m g) ∂μ) < ε := by
  letI := compactSpace_realModulation_ker m hm
  obtain ⟨τ, hτ⟩ := exists_realModulation_section m hm hms
  obtain ⟨κ, hκ, hprob, c, hc, he⟩ := exists_modulatedLogMeasure_eq_smul m μ τ hτ
  letI := hκ
  letI := hprob
  let ρ := modulatedLogMeasure m τ hτ κ
  let d : ℝ := c
  have hd : 0 < d := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hc)
  have hμ : μ = (c : ℝ≥0∞) • ρ := he
  obtain ⟨g, hgc, hgB, hgi, hgw, hgF, hgm, hgn, hgt⟩ :=
    exists_splitSobolev_approximate_kernel m τ hτ κ hm s hs hU h1 hε
  let f (x : G) := d⁻¹ • g x
  let w (x : G) := radialSobolevTailWeight s (modulatedLog m x)
  have hn (x : G) : ‖f x‖ = d⁻¹ * ‖g x‖ := by
    rw [show f x = d⁻¹ • g x from rfl, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hd.le)]
  have hIntegral {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : G → E) :
      (∫ x, d⁻¹ • F x ∂μ) = ∫ x, F x ∂ρ := by
    rw [hμ, integral_smul_measure, integral_smul, ENNReal.coe_toReal]
    change d • (d⁻¹ • (∫ x, F x ∂ρ)) = _
    rw [smul_smul, mul_inv_cancel₀ hd.ne', one_smul]
  have hFourier : lcaFourier μ f = lcaFourier ρ g := by
    funext ψ
    change (∫ x, (d⁻¹ • g x) * star (ψ x : ℂ) ∂μ) = _
    simp_rw [smul_mul_assoc]
    exact hIntegral (fun x => g x * star (ψ x : ℂ))
  have hW (x : G) : ‖f x‖ * w x = d⁻¹ * (‖g x‖ * w x) := by rw [hn, mul_assoc]
  have hfB : f ∈ bruhatSchwartzSubmodule (G := G) := by
    have h := (bruhatSchwartzSubmodule (G := G)).smul_mem ((d⁻¹ : ℝ) : ℂ) hgB
    convert h using 1
    funext x
    exact Complex.real_smul
  refine ⟨f, hgc.const_smul d⁻¹, hfB, ?_, ?_, by rw [hFourier]; exact hgF, ?_, ?_, ?_⟩
  · rw [hμ]
    exact (hgi.smul d⁻¹).smul_measure ENNReal.coe_ne_top
  · change Integrable (fun x => ‖f x‖ * w x) μ
    simp_rw [hW, hμ]
    exact (hgw.const_mul d⁻¹).smul_measure ENNReal.coe_ne_top
  · exact (hIntegral g).trans hgm
  · simp_rw [hn]
    refine (hIntegral (fun x => ‖g x‖)).trans_lt hgn
  · change (∫ x in Uᶜ, ‖f x‖ * w x ∂μ) < ε
    simp_rw [hW, hμ, Measure.restrict_smul, integral_smul_measure, integral_const_mul, ENNReal.coe_toReal]
    change d * (d⁻¹ * (∫ x in Uᶜ, ‖g x‖ * w x ∂ρ)) < ε
    rwa [← mul_assoc, mul_inv_cancel₀ hd.ne', one_mul]

/-- The unweighted L² representative of a physical Sobolev class exists
at every nonnegative order. -/
theorem memLp_of_ae_eq_groupSobolev {s : ℝ} (hs : 0 ≤ s) {f : G → ℂ}
    {u : Lp ℂ 2 (hardySobolevMeasure μ (modulatedLog m) 0 0 s)}
    (hu : (u : G → ℂ) =ᵐ[hardySobolevMeasure μ (modulatedLog m) 0 0 s] f) :
    MemLp f 2 μ := by
  refine ((memLp_congr_ae hu).mp (Lp.memLp u)).mono_measure ?_
  conv_lhs => rw [← withDensity_one (μ := μ)]
  change μ.withDensity 1 ≤ μ.withDensity _
  apply withDensity_mono
  refine .of_forall fun g => ?_
  change (1 : ℝ≥0∞) ≤ ENNReal.ofReal (hardySobolevWeight 0 0 s (modulatedLog m g))
  rw [← ENNReal.ofReal_one]
  apply ENNReal.ofReal_le_ofReal
  simpa [hardySobolevWeight] using
    Real.one_le_rpow (by linarith [sq_nonneg (modulatedLog m g)]) (div_nonneg hs (by norm_num))

/-- On the integrable Sobolev representatives the pointwise Fourier
integral represents the L² transform. -/
theorem groupSobolev_fourierPlancherel_ae [MeasurableSpace (PontryaginDual G)]
    [BorelSpace (PontryaginDual G)] {ν : Measure (PontryaginDual G)}
    {U : Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 ν} (hU : IsFourierPlancherel μ ν U)
    {s : ℝ} (hs : 0 ≤ s) {f : G → ℂ}
    {u : Lp ℂ 2 (hardySobolevMeasure μ (modulatedLog m) 0 0 s)}
    (hu : (u : G → ℂ) =ᵐ[hardySobolevMeasure μ (modulatedLog m) 0 0 s] f)
    (hf : Integrable f μ) :
    (U ((memLp_of_ae_eq_groupSobolev m μ hs hu).toLp f) : PontryaginDual G → ℂ)
      =ᵐ[ν] lcaFourier μ f := hU f hf _

/-- Corollary 9.3.2.3(1) for the originally chosen group Haar measure. -/
theorem exists_haarSobolev_frequencyBand_cutoff (s : ℝ) (χ : PontryaginDual G)
    (hm : IsProperMap m) (hs : Surjective m)
    {α β ε : ℝ} (hε : 0 < ε) (hwidth : α + ε < β - ε) :
    ∃ (u : Lp ℂ 2 (hardySobolevMeasure μ (modulatedLog m) 0 0 s)) (f : G → ℂ),
      (u : G → ℂ) =ᵐ[hardySobolevMeasure μ (modulatedLog m) 0 0 s] f ∧
      Integrable f μ ∧
      let F := lcaFourier μ f
      Continuous F ∧ tsupport F ⊆ modulatedFrequencyBand m (show CircleCharacter G from χ) α β ∧
      HasCompactSupport F ∧
      EqOn F 1 (modulatedFrequencyBand m (show CircleCharacter G from χ) (α + ε) (β - ε)) ∧
      ∀ ψ : PontryaginDual G, ContDiff ℝ ∞
        (fun t => F (ψ * (show PontryaginDual G from modulusCharacter m t))) := by
  letI := compactSpace_realModulation_ker m hm
  obtain ⟨τ, hτ⟩ := exists_realModulation_section m hm hs
  obtain ⟨κ, hκ, he⟩ := exists_modulatedLogMeasure_eq_haar m μ τ hτ
  letI := hκ
  have hκ₀ : κ.real univ ≠ 0 := ENNReal.toReal_ne_zero.mpr
    ⟨isOpen_univ.measure_ne_zero κ univ_nonempty, (measure_lt_top κ univ).ne⟩
  have h := exists_sobolev_frequencyBand_cutoff m τ hτ κ hκ₀ s χ hε hwidth
  rw [modulatedSobolevMeasure_eq_weighted m τ hτ κ, he] at h
  obtain ⟨u, f, hu, hf, hF⟩ := h
  exact ⟨u, f, hu, hf, continuous_lcaFourier μ hf, hF⟩

/-- Corollary 9.3.2.3(2) for the originally chosen group Haar measure. -/
theorem dense_haarSobolev_compactSpectrum (s : ℝ)
    (hm : IsProperMap m) (hs : Surjective m) :
    Dense {u : Lp ℂ 2 (hardySobolevMeasure μ (modulatedLog m) 0 0 s) |
      ∃ f : G → ℂ, Integrable f μ ∧ HasCompactSupport (lcaFourier μ f) ∧
        (u : G → ℂ) =ᵐ[hardySobolevMeasure μ (modulatedLog m) 0 0 s] f} := by
  letI := compactSpace_realModulation_ker m hm
  obtain ⟨τ, hτ⟩ := exists_realModulation_section m hm hs
  obtain ⟨κ, hκ, he⟩ := exists_modulatedLogMeasure_eq_haar m μ τ hτ
  letI := hκ
  rw [← he, ← modulatedSobolevMeasure_eq_weighted m τ hτ κ]
  exact dense_compactSpectrumSobolev m τ hτ κ s

private theorem lcaConvolution_eq_zero_of_distinct_kernel_characters
    {f g : G → ℂ} {χ ψ : PontryaginDual m.toMonoidHom.ker} (hne : χ ≠ ψ)
    (hf : ∀ (k : m.toMonoidHom.ker) y, f (k.val * y) = (χ k : ℂ) * f y)
    (hg : ∀ (k : m.toMonoidHom.ker) y, g (k.val * y) = (ψ k : ℂ) * g y) :
    lcaConvolution μ f g = 0 := by
  classical
  obtain ⟨k, hk⟩ : ∃ k, χ k ≠ ψ k := by
    by_contra! h
    exact hne (PontryaginDual.ext h)
  have hne' : (χ k : ℂ) ≠ (ψ k : ℂ) := fun h => hk (Circle.ext h)
  funext x
  change (∫ y, f y * g (y⁻¹ * x) ∂μ) = 0
  apply (mul_eq_zero.mp ?_).resolve_left (sub_ne_zero.mpr hne')
  rw [sub_mul, sub_eq_zero]
  calc
    (χ k : ℂ) * (∫ y, f y * g (y⁻¹ * x) ∂μ) =
        ∫ y, f (k.val * y) * g (y⁻¹ * x) ∂μ := by
      rw [← integral_const_mul]
      congr 1
      funext y
      rw [hf, mul_assoc]
    _ = ∫ y, (ψ k : ℂ) * (f (k.val * y) * g ((k.val * y)⁻¹ * x)) ∂μ := by
      congr 1
      funext y
      have he : k.val * ((k.val * y)⁻¹ * x) = y⁻¹ * x := by
        rw [mul_comm k.val y, mul_inv_rev, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul]
      conv_lhs => rw [← he, hg]
      ring
    _ = (ψ k : ℂ) * (∫ y, f y * g (y⁻¹ * x) ∂μ) := by
      rw [integral_const_mul]
      exact congrArg ((ψ k : ℂ) * ·) (integral_mul_left_eq_self
        (μ := μ) (fun y => f y * g (y⁻¹ * x)) k.val)

private theorem splitSchwartzWindow_homogeneous [CompactSpace m.toMonoidHom.ker]
    (τ : Multiplicative ℝ →ₜ* G) (hτ : RightInverse τ m)
    (χ : PontryaginDual m.toMonoidHom.ker) (p : 𝓢(ℝ, ℂ))
    (k : m.toMonoidHom.ker) (y : G) :
    splitSchwartzWindow m τ hτ χ p (k.val * y) = (χ k : ℂ) * splitSchwartzWindow m τ hτ χ p y := by
  let e := modulatedLogSplit m τ hτ
  let q := e.symm y
  have he : e (q.1, k * q.2) = k.val * y := by
    rw [← e.apply_symm_apply y]
    change τ (Multiplicative.ofAdd q.1) * (k.val * q.2.val) =
      k.val * (τ (Multiplicative.ofAdd q.1) * q.2.val)
    ac_rfl
  change (χ (e.symm (k.val * y)).2 : ℂ) * p (e.symm (k.val * y)).1 =
    (χ k : ℂ) * ((χ q.2 : ℂ) * p q.1)
  rw [← he, e.symm_apply_apply, map_mul, Circle.coe_mul, mul_assoc]

private theorem chosenHaar_absolutelyContinuous_groupSobolev (s : ℝ) :
    μ ≪ hardySobolevMeasure μ (modulatedLog m) 0 0 s := by
  apply withDensity_absolutelyContinuous'
  · exact ((continuous_hardySobolevWeight 0 0 s).measurable.comp
      (continuous_toAdd.comp m.continuous).measurable).ennreal_ofReal.aemeasurable
  · refine .of_forall fun g => ENNReal.ofReal_ne_zero_iff.mpr ?_
    have hpow : 0 < (1 + modulatedLog m g ^ 2) ^ (s / 2) := Real.rpow_pos_of_pos (by positivity) _
    simpa [hardySobolevWeight] using hpow

/-- Lemma 9.3.2.1(4) fails whenever the norm-one kernel is nontrivial.
The identity lies outside the strong operator closure of all convolution
operators represented by a kernel homogeneous for a single character. -/
theorem identity_not_mem_closure_singleCharacter_convolutions (s : ℝ)
    (hm : IsProperMap m) (hs : Surjective m) [Nontrivial m.toMonoidHom.ker] :
    let W := hardySobolevMeasure μ (modulatedLog m) 0 0 s
    let H := Lp ℂ 2 W
    (ContinuousLinearMap.id ℂ H : H →Lₚₜ[ℂ] H) ∉ closure
      {T : H →Lₚₜ[ℂ] H | ∃ (f : G → ℂ) (χ : PontryaginDual m.toMonoidHom.ker),
        (∀ (k : m.toMonoidHom.ker) x, f (k.val * x) = (χ k : ℂ) * f x) ∧
        ∀ (u : H) (g : G → ℂ), Continuous g → Integrable g μ →
          (u : G → ℂ) =ᵐ[W] g → (T u : G → ℂ) =ᵐ[W] lcaConvolution μ f g} := by
  classical
  letI := compactSpace_realModulation_ker m hm
  obtain ⟨τ, hτ⟩ := exists_realModulation_section m hm hs
  obtain ⟨κ, hκ, he⟩ := exists_modulatedLogMeasure_eq_haar m μ τ hτ
  letI := hκ
  let K := m.toMonoidHom.ker
  let e := modulatedLogSplit m τ hτ
  let W := hardySobolevMeasure μ (modulatedLog m) 0 0 s
  let H := Lp ℂ 2 W
  let bump : ContDiffBump (0 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩
  let p : 𝓢(ℝ, ℂ) := (bump.hasCompactSupport.comp_left Complex.ofReal_zero).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp bump.contDiff)
  have hp : p 0 = 1 := by
    change (bump 0 : ℂ) = 1
    rw [bump.one_of_mem_closedBall, Complex.ofReal_one]
    exact Metric.mem_closedBall_self bump.rIn_pos.le
  let g (χ : PontryaginDual K) := splitSchwartzWindow m τ hτ χ p
  have hW : modulatedSobolevMeasure m τ hτ κ 0 s = W := by
    rw [modulatedSobolevMeasure_eq_weighted, he]
  have hgLp (χ : PontryaginDual K) : MemLp (g χ) 2 W := by
    rw [← hW]
    exact (memLp_congr_ae (splitSchwartzWindowLp_ae m τ hτ κ s χ p)).mp (Lp.memLp _)
  let u (χ : PontryaginDual K) : H := (hgLp χ).toLp (g χ)
  have hu (χ : PontryaginDual K) : (u χ : G → ℂ) =ᵐ[W] g χ := (hgLp χ).coeFn_toLp
  have hg (χ : PontryaginDual K) : Continuous (g χ) :=
    ((continuous_subtype_val.comp χ.continuous).comp (continuous_snd.comp e.symm.continuous)).mul
      (p.continuous.comp (continuous_fst.comp e.symm.continuous))
  have hi (χ : PontryaginDual K) : Integrable (g χ) μ :=
    he ▸ splitSchwartzWindow_integrable m τ hτ κ χ p
  have hz (χ : PontryaginDual K) : u χ ≠ 0 := by
    intro hz
    have hzero := (hu χ).symm.trans (hz ▸ Lp.coeFn_zero ℂ 2 W)
    have heq := Measure.eq_of_ae_eq
      ((chosenHaar_absolutelyContinuous_groupSobolev m μ s).ae_eq hzero) (hg χ) continuous_zero
    have htest : g χ (e (0, 1)) = 1 := by
      change (χ (e.symm (e (0, 1))).2 : ℂ) * p (e.symm (e (0, 1))).1 = 1
      rw [e.symm_apply_apply, hp]
      simp
    exact one_ne_zero (htest.symm.trans (congrFun heq (e (0, 1))))
  obtain ⟨k, hk⟩ := exists_ne (1 : K)
  obtain ⟨ψ, hψ⟩ := exists_pontryaginDual_apply_ne_one hk
  have hψ' : ψ ≠ (1 : PontryaginDual K) := fun h => hψ (by simp [h])
  let S (χ : PontryaginDual K) : Set (H →Lₚₜ[ℂ] H) := {T | T (u χ) = 0}
  have hclosed (χ : PontryaginDual K) : IsClosed (S χ) :=
    isClosed_eq (PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) H (u χ)).continuous continuous_const
  dsimp only
  intro hid
  have hmem : (ContinuousLinearMap.id ℂ H : H →Lₚₜ[ℂ] H) ∈ S 1 ∪ S ψ := by
    apply closure_minimal ?_ ((hclosed 1).union (hclosed ψ)) hid
    rintro T ⟨f, χ, hf, hT⟩
    have hkill (η : PontryaginDual K) (hn : χ ≠ η) : T (u η) = 0 := by
      apply Lp.ext
      exact ((hT (u η) (g η) (hg η) (hi η) (hu η)).trans
        (.of_forall fun x => congrFun (lcaConvolution_eq_zero_of_distinct_kernel_characters
          m μ hn hf (splitSchwartzWindow_homogeneous m τ hτ η p)) x)).trans
        (Lp.coeFn_zero ℂ 2 W).symm
    by_cases hc : χ = 1
    · exact Or.inr (hkill ψ (hc ▸ hψ'.symm))
    · exact Or.inl (hkill 1 hc)
  exact hmem.elim (hz 1) (hz ψ)

end Haar

end

end Masullo
