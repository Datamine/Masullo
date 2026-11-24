import HardySobolevTranslations
import SpectralQuotientTrace
import BruhatCutoffNuclear
import Mathlib.MeasureTheory.Integral.Prod

open Filter Function InnerProductSpace MeasureTheory Set
open scoped CompactlySupported InnerProductSpace

namespace Masullo

noncomputable section

private theorem integral_norm_L2_pair_le {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (u v : Lp ℂ 2 μ) :
    (∫ x, ‖star (u x) * v x‖ ∂μ) ≤ ‖u‖ * ‖v‖ := by
  have hnorm (f : Lp ℂ 2 μ) : (∫ x, ‖f x‖ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) = ‖f‖ := by
    rw [Lp.norm_def, (Lp.memLp f).eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
    norm_num
    exact (ENNReal.toReal_ofReal (by positivity)).symm
  have h := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
    (by simpa using Lp.memLp u) (by simpa using Lp.memLp v)
  rw [hnorm u, hnorm v] at h
  simpa only [norm_mul, starRingEnd_apply, norm_star] using h

section

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [R1Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsMulLeftInvariant] [μ.InnerRegularCompactLTTop] [IsLocallyFiniteMeasure μ] [SigmaFinite μ]
  (m : G →* Multiplicative ℝ) (hm : Continuous m)

variable (l r s : ℝ)
local notation "amp" => (fun x : G => hardySobolevAmplitude l r s (Multiplicative.toAdd (m x)))

/-- Fubini identifies cutoff multiplication of Bochner convolution with its
pointwise formula in the amplitude chart. -/
private theorem hardySobolevCutoff_eq_of_kernel_action
    (hs : 0 ≤ s) (φ : C_c(G, ℂ))
    (ρ : G → ℝ) (hρ : Measurable ρ) (hρ₀ : ∀ x, 0 ≤ ρ x) (hρ₁ : ∀ x, ρ x ≤ 1)
    (v : Lp ℂ 2 (amplitudeMeasure μ amp)) (u w : Lp ℂ 2 μ)
    (hu : (u : G → ℂ) =ᵐ[μ] fun x => (amp x : ℂ) * v x)
    (hp : ∀ x, 0 < amp x)
    (hw : (w : G → ℂ) =ᵐ[μ] fun x => (ρ x : ℂ) * (amp x : ℂ) *
      ∫ g, φ g * v (g⁻¹ * x) ∂μ) :
    cutoffOperator ρ hρ hρ₀ hρ₁ (hardySobolevConvolution μ m hm l r s hs φ u) = w := by
  let M := cutoffOperator (μ := μ) ρ hρ hρ₀ hρ₁
  let T g := hardySobolevMulTranslation μ m hm l r s hs g
  let f (g : G) : Lp ℂ 2 μ := M (φ g • T g u)
  have hvMeas : Measurable (v : G → ℂ) := (Lp.stronglyMeasurable v).measurable
  have ha : Continuous amp := (Real.continuous_sqrt.comp
    (continuous_hardySobolevWeight l r s)).comp (continuous_toAdd.comp hm)
  have hf (g : G) : (f g : G → ℂ) =ᵐ[μ]
      fun x => (ρ x : ℂ) * (amp x : ℂ) * (φ g * v (g⁻¹ * x)) := by
    filter_upwards [cutoffOperator_ae ρ hρ hρ₀ hρ₁ (φ g • T g u),
      Lp.coeFn_smul (φ g) (T g u), hardySobolevMulTranslation_ae μ m hm l r s hs g u,
      (measurePreserving_mul_left μ g⁻¹).quasiMeasurePreserving.ae hu] with x h₁ h₂ h₃ h₄
    rw [h₁, h₂]
    change (ρ x : ℂ) * (φ g * T g u x) = _
    rw [h₃, h₄, Complex.ofReal_div]
    have hn : (amp (g⁻¹ * x) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hp _).ne'
    field_simp
  have hfInt : Integrable f μ :=
    M.integrable_comp (integrable_hardySobolev_convolution_orbit μ m hm l r s hs φ u)
  refine (ext_iff_inner_left (𝕜 := ℂ)).mpr fun h => ?_
  let L := (innerSL ℂ h).comp M
  let K (z : G × G) : ℂ :=
    (starRingEnd ℂ) (h z.2) * ((ρ z.2 : ℂ) * (amp z.2 : ℂ) * (φ z.1 * v (z.1⁻¹ * z.2)))
  have hKMeas : AEStronglyMeasurable K (μ.prod μ) := by
    have hfst : Measurable (Prod.fst : G × G → G) := measurable_fst
    have hsnd : Measurable (Prod.snd : G × G → G) := measurable_snd
    have hdual := Complex.continuous_conj.measurable.comp
      ((Lp.stronglyMeasurable h).measurable.comp hsnd)
    have hcut := Complex.continuous_ofReal.measurable.comp (hρ.comp hsnd)
    have hamp := Complex.continuous_ofReal.measurable.comp (ha.measurable.comp hsnd)
    have hsymbol := φ.continuous.measurable.comp hfst
    have hvalue := hvMeas.comp (hfst.inv.mul hsnd)
    exact (hdual.mul ((hcut.mul hamp).mul (hsymbol.mul hvalue))).aestronglyMeasurable
  have hPair (g : G) : (fun x => K (g, x)) =ᵐ[μ] fun x => (starRingEnd ℂ) (h x) * f g x :=
    (hf g).mono fun x hx => congrArg ((starRingEnd ℂ) (h x) * ·) hx.symm
  have hK : Integrable K (μ.prod μ) := by
    apply (integrable_prod_iff hKMeas).mpr
    refine ⟨Eventually.of_forall fun g => ?_, ?_⟩
    · apply Integrable.congr (L2.integrable_inner (𝕜 := ℂ) h (f g)) _
      simpa only [RCLike.inner_apply, mul_comm] using (hPair g).symm
    · refine (hfInt.norm.mul_const ‖h‖).mono'
        hKMeas.norm.integral_prod_right' (Eventually.of_forall fun g => ?_)
      rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      calc
        _ = ∫ x, ‖(starRingEnd ℂ) (h x) * f g x‖ ∂μ :=
          integral_congr_ae ((hPair g).mono fun _ hx => congrArg norm hx)
        _ ≤ ‖h‖ * ‖f g‖ := integral_norm_L2_pair_le h (f g)
        _ = _ := mul_comm _ _
  change L (∫ g, φ g • T g u ∂μ) = ⟪h, w⟫_ℂ
  rw [← L.integral_comp_comm (integrable_hardySobolev_convolution_orbit μ m hm l r s hs φ u)]
  calc
    _ = ∫ g, ∫ x, K (g, x) ∂μ ∂μ := by
      apply integral_congr_ae
      refine Eventually.of_forall fun g => ?_
      change ⟪h, f g⟫_ℂ = _
      rw [L2.inner_def]
      apply integral_congr_ae
      simpa only [RCLike.inner_apply, mul_comm] using (hPair g).symm
    _ = ∫ x, ∫ g, K (g, x) ∂μ ∂μ := (integral_prod K hK).symm.trans (integral_prod_symm K hK)
    _ = ⟪h, w⟫_ℂ := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hw] with x hx
      simp only [K, RCLike.inner_apply, hx, mul_assoc]
      simp only [integral_const_mul]
      ring

end

section BruhatCutoff

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
  (m : G →ₜ* Multiplicative ℝ) (hm : IsProperMap m) (hms : Surjective m)

/-- The charted convolution has the pointwise Haar formula on the region
where a compact measurable cutoff is one. -/
theorem hardySobolevConvolution_ae_on_cutoff
    (l r s : ℝ) (hs : 0 ≤ s) (φ : C_c(G, ℂ))
    (ρ : G → ℝ) (hρ : Measurable ρ) (hρc : HasCompactSupport ρ)
    (hρ₀ : ∀ x, 0 ≤ ρ x) (hρ₁ : ∀ x, ρ x ≤ 1) :
    let w := hardySobolevWeight l r s ∘ modulatedLog m
    let a := Real.sqrt ∘ w
    let ha : Measurable a := (Real.continuous_sqrt.comp
      ((continuous_hardySobolevWeight l r s).comp (continuous_toAdd.comp m.continuous))).measurable
    let hp : ∀ x, 0 < a x := fun x => Real.sqrt_pos.2 (by
      unfold w Function.comp hardySobolevWeight
      exact mul_pos ((Real.exp_pos _).trans_le (le_max_left _ _))
        (Real.rpow_pos_of_pos (by positivity) _))
    let e := amplitudeL2Iso μ a ha hp
    letI : μ.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure μ
    ∀ v : Lp ℂ 2 (amplitudeMeasure μ a), ∀ᵐ x ∂μ, ρ x = 1 →
      hardySobolevConvolution μ m.toMonoidHom m.continuous l r s hs φ (e v) x =
        (a x : ℂ) * ∫ g, φ g * v (g⁻¹ * x) ∂μ := by
  intro w a ha hp e
  letI : μ.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure μ
  intro v
  have hw : Continuous w := (continuous_hardySobolevWeight l r s).comp
    (continuous_toAdd.comp m.continuous)
  have hw₀ (x : G) : 0 < w x := Real.sqrt_pos.mp (hp x)
  let ν := μ.withDensity (fun x => ENNReal.ofReal (w x))
  have hν : ν = amplitudeMeasure μ a := by
    unfold ν amplitudeMeasure
    congr 1
    funext x
    exact congrArg ENNReal.ofReal (Real.sq_sqrt (hw₀ x).le).symm
  have hρℂ := Complex.continuous_ofReal.measurable.comp hρ
  have hρcℂ : HasCompactSupport (fun x => (ρ x : ℂ)) := hρc.comp_left Complex.ofReal_zero
  have hb : ∃ C : ℝ, ∀ x, ‖(ρ x : ℂ)‖ ≤ C := ⟨1, fun x => by
    rw [Complex.norm_real, Real.norm_of_nonneg (hρ₀ x)]
    exact hρ₁ x⟩
  let k := cutoffConvolutionKernel w (fun x => (ρ x : ℂ)) φ
  have hk : MemLp k 2 (ν.prod ν) :=
    cutoffConvolutionKernel_memLp_of_measurable_cutoff μ hw hw₀ hρℂ
      φ.continuous.measurable.aemeasurable hb
      (φ.hasCompactSupport.exists_bound_of_continuous φ.continuous) hρcℂ φ.hasCompactSupport
  have hkernel : ∃ B : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν, ∀ u : Lp ℂ 2 ν, ∀ᵐ x ∂μ,
      B u x = (ρ x : ℂ) * ∫ g, φ g * u (g⁻¹ * x) ∂μ :=
    ⟨kernelIntegralOperator (hk.toLp k), fun u =>
      cutoffConvolutionKernel_apply_of_measurable_cutoff μ hw hw₀ hρℂ
        φ.continuous.measurable.aemeasurable hb
        (φ.hasCompactSupport.exists_bound_of_continuous φ.continuous) hρcℂ φ.hasCompactSupport u⟩
  rw [hν] at hkernel
  obtain ⟨B, hB⟩ := hkernel
  have hv : ((e v) : G → ℂ) =ᵐ[μ] fun x => (a x : ℂ) * v x := by
    simpa only [Complex.real_smul] using amplitudeL2Iso_ae μ a ha hp v
  have hBv : ((e (B v)) : G → ℂ) =ᵐ[μ] fun x => (ρ x : ℂ) * (a x : ℂ) *
      ∫ g, φ g * v (g⁻¹ * x) ∂μ := by
    filter_upwards [amplitudeL2Iso_ae μ a ha hp (B v), hB v] with x hx hy
    rw [hx, hy, Complex.real_smul, ← mul_assoc, mul_comm (a x : ℂ)]
  have he := hardySobolevCutoff_eq_of_kernel_action μ m.toMonoidHom m.continuous l r s hs φ
    ρ hρ hρ₀ hρ₁ v (e v) (e (B v)) hv hp hBv
  let u := hardySobolevConvolution μ m.toMonoidHom m.continuous l r s hs φ (e v)
  filter_upwards [cutoffOperator_ae ρ hρ hρ₀ hρ₁ u, hBv] with x hx hy h1
  change u x = _
  rw [← he, hx, h1, Complex.ofReal_one, one_mul, one_mul] at hy
  exact hy

include hm hms in
private theorem bruhatHardySobolev_continuousCutoff_traceClass
    (l r s : ℝ) (hs : 0 ≤ s) (φ : BruhatSchwartz G) (hφc : HasCompactSupport φ.val)
    (ρ : G → ℝ) (hρ : Continuous ρ) (hρc : HasCompactSupport ρ)
    (hρ₀ : ∀ x, 0 ≤ ρ x) (hρ₁ : ∀ x, ρ x ≤ 1) :
    letI : μ.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure μ
    let ψ : C_c(G, ℂ) := ⟨⟨φ.val, bruhatSchwartz_continuous φ⟩, hφc⟩
    ∃ T : TraceClass (Lp ℂ 2 μ), T.toOperator =
        (cutoffOperator ρ hρ.measurable hρ₀ hρ₁).comp
          (hardySobolevConvolution μ m.toMonoidHom m.continuous l r s hs ψ) ∧
      T.traceValue = (∫ x, (ρ x : ℂ) ∂μ) * φ.val 1 := by
  letI : μ.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure μ
  intro ψ
  let w (x : G) := hardySobolevWeight l r s (modulatedLog m x)
  let a (x : G) := hardySobolevAmplitude l r s (modulatedLog m x)
  have hw : Continuous w := (continuous_hardySobolevWeight l r s).comp
    (continuous_toAdd.comp m.continuous)
  have hw₀ (x : G) : 0 < w x := by
    dsimp [w, hardySobolevWeight]
    exact mul_pos ((Real.exp_pos _).trans_le (le_max_left _ _))
      (Real.rpow_pos_of_pos (by positivity) _)
  have ha : Measurable a := (Real.continuous_sqrt.comp hw).measurable
  have ha₀ (x : G) : 0 < a x := Real.sqrt_pos.2 (hw₀ x)
  have hν : hardySobolevMeasure μ (modulatedLog m) l r s = amplitudeMeasure μ a := by
    unfold hardySobolevMeasure amplitudeMeasure
    congr 1
    funext x
    exact congrArg ENNReal.ofReal (Real.sq_sqrt (hw₀ x).le).symm
  have hρℂ : Continuous (fun x => (ρ x : ℂ)) := Complex.continuous_ofReal.comp hρ
  have hρcℂ : HasCompactSupport (fun x => (ρ x : ℂ)) :=
    hρc.comp_left Complex.ofReal_zero
  have hkernel := bruhatCompactBaseCutoff_traceClass m hm hms μ l r s hρℂ hρcℂ φ hφc
  dsimp only at hkernel
  rw [hν] at hkernel
  obtain ⟨U, hU, htrace⟩ := hkernel
  let e := amplitudeL2Iso μ a ha ha₀
  obtain ⟨T, hT, hTtrace⟩ := traceClass_transport e.toLinearIsometry.toContinuousLinearMap
    e.symm.toLinearIsometry.toContinuousLinearMap e.symm_apply_apply U
  refine ⟨T, ?_, hTtrace.trans htrace⟩
  rw [hT]
  apply ContinuousLinearMap.ext
  intro u
  let v := e.symm u
  change e (U.toOperator v) =
    cutoffOperator ρ hρ.measurable hρ₀ hρ₁
      (hardySobolevConvolution μ m.toMonoidHom m.continuous l r s hs ψ u)
  have hinput : (u : G → ℂ) =ᵐ[μ] fun x => (a x : ℂ) * v x := by
    have h := amplitudeL2Iso_ae μ a ha ha₀ v
    change ((e (e.symm u)) : G → ℂ) =ᵐ[μ] (fun x => a x • v x) at h
    rw [e.apply_symm_apply] at h
    simpa only [Complex.real_smul] using h
  have houtput : (e (U.toOperator v) : G → ℂ) =ᵐ[μ] fun x => (ρ x : ℂ) * (a x : ℂ) *
      ∫ g, φ.val g * v (g⁻¹ * x) ∂μ := by
    filter_upwards [amplitudeL2Iso_ae μ a ha ha₀ (U.toOperator v), hU v] with x hx hy
    rw [hx, hy, Complex.real_smul, ← mul_assoc, mul_comm (a x : ℂ)]
  exact (hardySobolevCutoff_eq_of_kernel_action μ m.toMonoidHom m.continuous l r s hs ψ
    ρ hρ.measurable hρ₀ hρ₁ v u _ hinput ha₀ houtput).symm

include hm hms in
/-- The compact cutoff of actual Hardy–Sobolev convolution is trace class.
A continuous bump can be used before multiplication by a cutoff with jumps. -/
theorem bruhatHardySobolev_cutoff_traceClass
    (l r s : ℝ) (hs : 0 ≤ s) (φ : BruhatSchwartz G) (hφc : HasCompactSupport φ.val)
    (ρ : G → ℝ) (hρ : Measurable ρ) (hρc : HasCompactSupport ρ)
    (hρ₀ : ∀ x, 0 ≤ ρ x) (hρ₁ : ∀ x, ρ x ≤ 1) :
    letI : μ.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure μ
    let ψ : C_c(G, ℂ) := ⟨⟨φ.val, bruhatSchwartz_continuous φ⟩, hφc⟩
    ∃ T : TraceClass (Lp ℂ 2 μ), T.toOperator =
        (cutoffOperator ρ hρ hρ₀ hρ₁).comp
          (hardySobolevConvolution μ m.toMonoidHom m.continuous l r s hs ψ) := by
  letI : μ.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure μ
  intro ψ
  obtain ⟨b, hb, _, hbc, hb01⟩ :=
    exists_continuous_one_zero_of_isCompact hρc isClosed_empty (disjoint_empty _)
  obtain ⟨U, hU, _⟩ := bruhatHardySobolev_continuousCutoff_traceClass μ m hm hms
    l r s hs φ hφc b b.continuous hbc (fun x => (hb01 x).1) (fun x => (hb01 x).2)
  let M := cutoffOperator (μ := μ) ρ hρ hρ₀ hρ₁
  refine ⟨TraceClass.leftCompose M U, ?_⟩
  rw [TraceClass.leftCompose_toOperator, hU]
  apply ContinuousLinearMap.ext
  intro f
  let u := hardySobolevConvolution μ m.toMonoidHom m.continuous l r s hs ψ f
  let B := cutoffOperator (μ := μ) b b.continuous.measurable
    (fun x => (hb01 x).1) (fun x => (hb01 x).2)
  change M (B u) = M u
  apply Lp.ext
  filter_upwards [cutoffOperator_ae ρ hρ hρ₀ hρ₁ (B u),
    cutoffOperator_ae b b.continuous.measurable (fun x => (hb01 x).1) (fun x => (hb01 x).2) u,
    cutoffOperator_ae ρ hρ hρ₀ hρ₁ u] with x hx hy hz
  rw [hx, hy, hz]
  by_cases h : x ∈ tsupport ρ
  · rw [hb h]
    simp
  · rw [image_eq_zero_of_notMem_tsupport h]
    simp

end BruhatCutoff

end

end Masullo
