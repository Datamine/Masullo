import GlobalThetaSobolevConvolution
import GlobalHeckeZeroLine
import ModulatedFrequencySobolev

open Filter Function MeasureTheory NumberField Set Topology
open scoped ContDiff ENNReal FourierTransform NumberField SchwartzMap TensorProduct

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

private abbrev Q := IdeleClass F
private abbrev K := normOneIdeleClass F
private abbrev r (q : Q F) : ℝ := (ideleClassLogNorm F q).toAdd
private abbrev ray (t : ℝ) := ideleClassExpSection F (Multiplicative.ofAdd t)

local instance zeroLineDensityMeasurable : MeasurableSpace (Q F) := borel _
local instance zeroLineDensityBorel : BorelSpace (Q F) := ⟨rfl⟩
local instance zeroLineDensityT2 : T2Space (Q F) := ideleClasses_hausdorff
local instance zeroLineDensityLocallyCompact : LocallyCompactSpace (Q F) := ideleClasses_locallyCompact
local instance zeroLineDensitySecondCountable : SecondCountableTopology (Q F) := ideleClass_secondCountable F
local instance zeroLineDensityNormOneMeasurable : MeasurableSpace (K F) := borel _
local instance zeroLineDensityNormOneBorel : BorelSpace (K F) := ⟨rfl⟩
local instance zeroLineDensityNormOneCompact : CompactSpace (K F) := normOneIdeleClass_compact F

variable (ν : Measure (K F)) [ν.IsHaarMeasure]

local instance zeroLineDensityNormOneFinite : IsFiniteMeasure ν := ⟨isCompact_univ.measure_lt_top⟩
local instance zeroLineDensityHaar : (globalClassMeasure F ν).IsHaarMeasure := globalClassMeasure_isHaar F ν

private abbrev μ := globalClassMeasure F ν
private abbrev amp (s : ℝ) (q : Q F) := hardySobolevAmplitude 0 0 s (r F q)

private abbrev e := (ideleClassLogCoordinates F).toMeasurableEquiv

omit [ν.IsHaarMeasure] in
private theorem e_preserving : MeasurePreserving (e F) (volume.prod ν) (μ F ν) :=
  ⟨(e F).measurable, rfl⟩

private theorem amp_eq (s : ℝ) (q : Q F) :
    amp F s q = (1 + (r F q)^2) ^ (s / 4) := by
  simp only [amp, hardySobolevAmplitude, hardySobolevWeight, mul_zero, zero_mul, Real.exp_zero,
    max_self, one_mul, Real.sqrt_eq_rpow]
  rw [← Real.rpow_mul (by positivity)]
  congr 1
  ring

private def profile (χ : PontryaginDual (K F)) (p : 𝓢(ℝ, ℂ)) (q : Q F) : ℂ :=
  (χ (ideleClassNormOnePart F q) : ℂ) * p (r F q)

private theorem profile_continuous (χ : PontryaginDual (K F)) (p : 𝓢(ℝ, ℂ)) :
    Continuous (profile F χ p) := by
  exact (continuous_subtype_val.comp (χ.continuous.comp (ideleClassSplitHomeomorph F).continuous.fst)).mul
    (p.continuous.comp (continuous_toAdd.comp (ideleClassLogNorm_continuous F)))

/-- The separated Schwartz profile in the actual global zero-line chart. -/
def globalZeroLineSchwartzIsotype (s : ℝ) (χ : PontryaginDual (K F)) :
    𝓢(ℝ, ℂ) →L[ℂ] Lp ℂ 2 (μ F ν) := by
  let v := compactCharacterLp ν χ
  let L : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume.prod ν) :=
    ((lpTwoTensorIsometry (μ := (volume : Measure ℝ)) (ν := ν)).toLinearMap.comp
      ((TensorProduct.mk ℂ (Lp ℂ 2 (volume : Measure ℝ)) (Lp ℂ 2 ν)).flip v)).mkContinuous
      ‖v‖ (fun u ↦ by
        change ‖lpTwoTensorIsometry (u ⊗ₜ[ℂ] v)‖ ≤ ‖v‖ * ‖u‖
        rw [LinearIsometry.norm_map, TensorProduct.norm_tmul, mul_comm])
  exact (Lp.compMeasurePreservingₗᵢ ℂ (e F).symm
    ((e_preserving F ν).symm (e F))).toContinuousLinearMap.comp (L.comp (weightedSchwartzL2 s))

private theorem globalZeroLineSchwartzIsotype_ae (s : ℝ) (χ : PontryaginDual (K F))
    (p : 𝓢(ℝ, ℂ)) :
    (globalZeroLineSchwartzIsotype F ν s χ p : Q F → ℂ) =ᵐ[μ F ν] fun q ↦
      (amp F s q : ℂ) * profile F χ p q := by
  let u := weightedSchwartzL2 s p
  let v := compactCharacterLp ν χ
  let h := (e_preserving F ν).symm (e F)
  filter_upwards [Lp.coeFn_compMeasurePreserving (lpTwoProduct u v) h,
    h.quasiMeasurePreserving.ae_eq_comp (lpTwoProduct_ae u v),
    h.quasiMeasurePreserving.ae_eq_comp ((Measure.quasiMeasurePreserving_fst
      (μ := (volume : Measure ℝ)) (ν := ν)).ae_eq_comp (weightedSchwartzL2_ae s p)),
    h.quasiMeasurePreserving.ae_eq_comp ((Measure.quasiMeasurePreserving_snd
      (μ := (volume : Measure ℝ)) (ν := ν)).ae_eq_comp (compactCharacterLp_ae ν χ))]
      with q h₁ h₂ h₃ h₄
  change globalZeroLineSchwartzIsotype F ν s χ p q = lpTwoProduct u v ((e F).symm q) at h₁
  change lpTwoProduct u v ((e F).symm q) = u (r F q) * v (ideleClassNormOnePart F q) at h₂
  change u (r F q) = (1 + (r F q)^2) ^ (s / 4) • p (r F q) at h₃
  change v (ideleClassNormOnePart F q) = (χ (ideleClassNormOnePart F q) : ℂ) at h₄
  rw [h₁, h₂, h₃, h₄, amp_eq, Complex.real_smul, profile]
  ring

private theorem thetaProfile_homogeneous (χ : PontryaginDual (K F))
    (f : GlobalBruhat F) (hf : GlobalBruhat.polarEvaluation F f = 0) (q : Q F) :
    profile F χ⁻¹ (polarFreeThetaRadialSchwartz F ν χ f hf) q =
      adelicHomogeneousTheta F ν χ (GlobalBruhat.algebraicEquiv F f).val q := by
  let a := ideleClassNormOnePart F q
  have h := adelicHomogeneousTheta_twisted_radialSchwartz F ν χ f
    (Or.inr ⟨congrArg Prod.fst hf, congrArg Prod.snd hf⟩) q
  change (χ a : ℂ) * adelicHomogeneousTheta F ν χ (GlobalBruhat.algebraicEquiv F f).val q =
    polarFreeThetaRadialSchwartz F ν χ f hf (r F q) at h
  change ((χ a : Circle)⁻¹ : ℂ) * polarFreeThetaRadialSchwartz F ν χ f hf (r F q) = _
  calc
    _ = (χ a : ℂ)⁻¹ * ((χ a : ℂ) * adelicHomogeneousTheta F ν χ (GlobalBruhat.algebraicEquiv F f).val q) :=
      congrArg ((χ a : ℂ)⁻¹ * ·) h.symm
    _ = _ := inv_mul_cancel_left₀ (Circle.coe_ne_zero _) _

private theorem thetaRadialEmbed_mem (s : ℝ) (hs : 0 ≤ s)
    (χ : PontryaginDual (K F)) (f : GlobalBruhat F) (hf : GlobalBruhat.polarEvaluation F f = 0) :
    globalZeroLineSchwartzIsotype F ν s χ⁻¹ (polarFreeThetaRadialSchwartz F ν χ f hf) ∈
      globalThetaSobolevCompletion F (μ F ν) 0 0 0 s hs := by
  apply globalThetaSobolevCompletion_homogeneous_mem F (μ F ν) ν χ s hs f hf
  filter_upwards [globalZeroLineSchwartzIsotype_ae F ν s χ⁻¹ (polarFreeThetaRadialSchwartz F ν χ f hf)]
    with q hq
  exact hq.trans (congrArg ((amp F s q : ℂ) * ·) (thetaProfile_homogeneous F ν χ f hf q))

private theorem normOnePart_ray (t : ℝ) : ideleClassNormOnePart F (ray F t) = 1 := by
  apply Subtype.ext
  change ray F t / ideleClassExpSection F (ideleClassLogNorm F (ray F t)) = 1
  rw [ideleClassLogNorm_expSection, div_self']

private theorem profile_rayShift (χ : PontryaginDual (K F)) (p : 𝓢(ℝ, ℂ))
    (q : Q F) (t : ℝ) :
    profile F χ p ((ray F t)⁻¹ * q) =
      (χ (ideleClassNormOnePart F q) : ℂ) * p (r F q - t) := by
  let A := MonoidHom.fst (K F) (Multiplicative ℝ) |>.comp (ideleClassSplit F).toMonoidHom
  have hA : ideleClassNormOnePart F ((ray F t)⁻¹ * q) = ideleClassNormOnePart F q := by
    change A ((ray F t)⁻¹ * q) = A q
    rw [map_mul, map_inv]
    change (ideleClassNormOnePart F (ray F t))⁻¹ * A q = A q
    rw [normOnePart_ray, inv_one, one_mul]
  have hr : r F ((ray F t)⁻¹ * q) = r F q - t := by
    unfold r
    rw [map_mul, map_inv, ideleClassLogNorm_expSection]
    change -t + r F q = r F q - t
    ring
  rw [profile, hA, hr]

/-- In the separated Sobolev chart, a global translation is a radial
shift times the inverse compact character of its translating class. -/
theorem globalZeroLineSchwartzIsotype_translate (s : ℝ) (hs : 0 ≤ s)
    (χ : PontryaginDual (K F)) (p : 𝓢(ℝ, ℂ)) (g : Q F) :
    hardySobolevMulTranslation (μ F ν) (ideleClassLogNorm F) (ideleClassLogNorm_continuous F)
      0 0 s hs g (globalZeroLineSchwartzIsotype F ν s χ p) =
      (χ (ideleClassNormOnePart F g) : ℂ)⁻¹ •
        globalZeroLineSchwartzIsotype F ν s χ (p.compSubConstCLM ℂ (r F g)) := by
  let u := globalZeroLineSchwartzIsotype F ν s χ p
  let v := globalZeroLineSchwartzIsotype F ν s χ (p.compSubConstCLM ℂ (r F g))
  let a : ℂ := (χ (ideleClassNormOnePart F g) : ℂ)⁻¹
  let T := hardySobolevMulTranslation (μ F ν) (ideleClassLogNorm F)
    (ideleClassLogNorm_continuous F) 0 0 s hs g
  change T u = a • v
  apply Lp.ext
  filter_upwards [hardySobolevMulTranslation_ae (μ F ν) (ideleClassLogNorm F)
    (ideleClassLogNorm_continuous F) 0 0 s hs g u,
    (measurePreserving_mul_left (μ F ν) g⁻¹).quasiMeasurePreserving.ae_eq_comp
      (globalZeroLineSchwartzIsotype_ae F ν s χ p),
    globalZeroLineSchwartzIsotype_ae F ν s χ (p.compSubConstCLM ℂ (r F g)),
    Lp.coeFn_smul a v] with q h₁ h₂ h₃ h₄
  let x := g⁻¹ * q
  change T u q = ((amp F s q / amp F s x : ℝ) : ℂ) * u x at h₁
  change u x = (amp F s x : ℂ) * profile F χ p x at h₂
  change v q = (amp F s q : ℂ) * profile F χ (p.compSubConstCLM ℂ (r F g)) q at h₃
  change (a • v : Lp ℂ 2 (μ F ν)) q = a * v q at h₄
  have he : profile F χ p x = a * profile F χ (p.compSubConstCLM ℂ (r F g)) q := by
    let A := MonoidHom.fst (K F) (Multiplicative ℝ) |>.comp (ideleClassSplit F).toMonoidHom
    have hA : ideleClassNormOnePart F x = (ideleClassNormOnePart F g)⁻¹ * ideleClassNormOnePart F q := by
      change A (g⁻¹ * q) = (A g)⁻¹ * A q
      rw [map_mul, map_inv]
    have hr : r F x = r F q - r F g := by
      change (ideleClassLogNorm F (g⁻¹ * q)).toAdd = _
      rw [map_mul, map_inv]
      change -r F g + r F q = r F q - r F g
      ring
    unfold profile
    rw [hA, hr, SchwartzMap.compSubConstCLM_apply, map_mul, map_inv, Circle.coe_mul, Circle.coe_inv]
    exact mul_assoc _ _ _
  have hpos : 0 < amp F s x := by
    rw [amp_eq]
    exact Real.rpow_pos_of_pos (by positivity) _
  change T u q = (a • v : Lp ℂ 2 (μ F ν)) q
  rw [h₁, h₂, h₄, h₃, Complex.ofReal_div, ← mul_assoc,
    div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr hpos.ne'), he]
  ring

/-- On the compact norm-one subgroup the separated chart transforms by
the inverse of the character used in its pointwise profile. -/
theorem globalZeroLineSchwartzIsotype_translate_normOne (s : ℝ) (hs : 0 ≤ s)
    (χ : PontryaginDual (K F)) (p : 𝓢(ℝ, ℂ)) (k : K F) :
    hardySobolevMulTranslation (μ F ν) (ideleClassLogNorm F) (ideleClassLogNorm_continuous F)
      0 0 s hs k.val (globalZeroLineSchwartzIsotype F ν s χ p) =
      (χ k : ℂ)⁻¹ • globalZeroLineSchwartzIsotype F ν s χ p := by
  have hk : ideleClassLogNorm F k.val = 1 := by
    change Multiplicative.ofAdd (Real.log (ideleClassNorm F k.val)) = Multiplicative.ofAdd 0
    rw [show ideleClassNorm F k.val = 1 from k.property, Real.log_one]
  have hN : ideleClassNormOnePart F k.val = k := by
    apply Subtype.ext
    change k.val / ideleClassExpSection F (ideleClassLogNorm F k.val) = k.val
    rw [hk, map_one, div_one]
  rw [globalZeroLineSchwartzIsotype_translate F ν s hs χ p k.val, hN]
  change (χ k : ℂ)⁻¹ • globalZeroLineSchwartzIsotype F ν s χ
    (p.compSubConstCLM ℂ (r F k.val)) = _
  simp [r, hk]

/-- The pointwise amplitude formula for the separated Schwartz chart. -/
theorem globalZeroLineSchwartzIsotype_ae_formula (s : ℝ) (χ : PontryaginDual (K F))
    (p : 𝓢(ℝ, ℂ)) :
    (globalZeroLineSchwartzIsotype F ν s χ p : Q F → ℂ) =ᵐ[μ F ν] fun q ↦
      (amp F s q : ℂ) * ((χ (ideleClassNormOnePart F q) : ℂ) * p (r F q)) :=
  globalZeroLineSchwartzIsotype_ae F ν s χ p

private abbrev B := ContinuousLinearMap.mul ℂ ℂ

private theorem complexMul_flip : B.flip = B := by
  apply ContinuousLinearMap.ext
  intro z
  apply ContinuousLinearMap.ext
  intro w
  exact mul_comm w z

private theorem convolution_profile (χ : PontryaginDual (K F)) (p c : 𝓢(ℝ, ℂ)) (q : Q F) :
    profile F χ (SchwartzMap.convolution B p c) q =
      ∫ t : ℝ, c t * profile F χ p ((ray F t)⁻¹ * q) := by
  have h : SchwartzMap.convolution B p c = SchwartzMap.convolution B c p := by
    rw [← SchwartzMap.convolution_flip B]
    exact congrArg (fun M ↦ SchwartzMap.convolution M c p) complexMul_flip
  rw [h, profile, SchwartzMap.convolution_apply, MeasureTheory.convolution_def, ← integral_const_mul]
  apply integral_congr_ae
  exact .of_forall fun t ↦ by
    let z : ℂ := (χ (ideleClassNormOnePart F q) : ℂ)
    change z * (c t * p (r F q - t)) = c t * profile F χ p ((ray F t)⁻¹ * q)
    calc
      _ = c t * (z * p (r F q - t)) := mul_left_comm _ _ _
      _ = _ := congrArg (c t * ·) (profile_rayShift F χ p q t).symm

private theorem radialConvolution_mem (s : ℝ) (hs : 0 ≤ s)
    (χ : PontryaginDual (K F)) (p c : 𝓢(ℝ, ℂ))
    (hp : globalZeroLineSchwartzIsotype F ν s χ p ∈ globalThetaSobolevCompletion F (μ F ν) 0 0 0 s hs) :
    globalZeroLineSchwartzIsotype F ν s χ (SchwartzMap.convolution B p c) ∈
      globalThetaSobolevCompletion F (μ F ν) 0 0 0 s hs := by
  apply globalThetaSobolevCompletion_radial_convolution_mem F (μ F ν) s hs c
    (globalZeroLineSchwartzIsotype F ν s χ p) _ (profile F χ p)
    (profile_continuous F χ p).measurable hp (globalZeroLineSchwartzIsotype_ae F ν s χ p)
  filter_upwards [globalZeroLineSchwartzIsotype_ae F ν s χ (SchwartzMap.convolution B p c)] with q hq
  exact hq.trans (congrArg ((amp F s q : ℂ) * ·) (convolution_profile F χ p c q))

local instance zeroLineDensityIdeleMeasurable : MeasurableSpace (Idele F) := borel _
local instance zeroLineDensityIdeleBorel : BorelSpace (Idele F) := ⟨rfl⟩

variable (η : Measure (Idele F)) [η.IsHaarMeasure]
variable [∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)ˣ]
  (mf : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), Measure (v.adicCompletion F)ˣ)
  [∀ v, (mf v).IsHaarMeasure] [∀ v, SigmaFinite (mf v)]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]
variable (hν : IsWeilQuotientMeasure (principalIdeles F) η Measure.count (μ F ν))

include mf hν in
/-- Each band-limited separated isotype profile belongs to the closed
global theta image. Its finite convolution formula uses actual adelic tests. -/
theorem globalZeroLineSchwartzIsotype_bandlimited_mem (s : ℝ) (hs : 0 ≤ s)
    (χ : PontryaginDual (K F)) (p : 𝓢(ℝ, ℂ))
    (hp : HasCompactSupport (𝓕 p : 𝓢(ℝ, ℂ))) :
    globalZeroLineSchwartzIsotype F ν s χ p ∈ globalThetaSobolevCompletion F (μ F ν) 0 0 0 s hs := by
  obtain ⟨J, c, _, he⟩ := exists_polarFreeThetaRadialSchwartz_finite_convolution F η ν mf hν χ⁻¹ p hp
  rw [← he, map_sum]
  apply Submodule.sum_mem
  intro f _
  let g := polarFreeThetaRadialSchwartz F ν χ⁻¹ f.val f.property
  have hg := thetaRadialEmbed_mem F ν s hs χ⁻¹ f.val f.property
  rw [inv_inv] at hg
  exact radialConvolution_mem F ν s hs χ g (c f) hg

include mf hν in
/-- The polar-free theta closure contains every separated Schwartz isotype. -/
theorem globalZeroLineSchwartzIsotype_mem (s : ℝ) (hs : 0 ≤ s)
    (χ : PontryaginDual (K F)) (p : 𝓢(ℝ, ℂ)) :
    globalZeroLineSchwartzIsotype F ν s χ p ∈ globalThetaSobolevCompletion F (μ F ν) 0 0 0 s hs := by
  apply (globalThetaSobolevCompletion_isClosed F (μ F ν) 0 0 0 s hs).mem_of_tendsto
    ((globalZeroLineSchwartzIsotype F ν s χ).continuous.continuousAt.tendsto.comp
      (fourierWindow_tendsto p))
  exact .of_forall fun j ↦ globalZeroLineSchwartzIsotype_bandlimited_mem F ν η mf hν s hs χ
    (fourierWindow p j) (fourierWindow_hasCompactSpectrum p j)

private theorem weightedSchwartz_dense (s : ℝ) : DenseRange (weightedSchwartzL2 s) := by
  have hd : DenseRange (SchwartzMap.toLpCLM ℝ ℂ 2 (volume : Measure ℝ)) :=
    SchwartzMap.denseRange_toLpCLM (by norm_num)
  apply hd.mono
  rintro u ⟨p, rfl⟩
  let w (t : ℝ) : ℂ := (((1 + t^2) ^ (-s / 4) : ℝ) : ℂ)
  have hw : w.HasTemperateGrowth := Complex.hasTemperateGrowth_ofReal.comp (by
    simpa only [Real.norm_eq_abs, sq_abs] using
      Function.hasTemperateGrowth_one_add_norm_sq_rpow ℝ (-s / 4))
  let q := SchwartzMap.smulLeftCLM ℂ w p
  refine ⟨q, Lp.ext ?_⟩
  filter_upwards [weightedSchwartzL2_ae s q, SchwartzMap.coeFn_toLp p 2 (volume : Measure ℝ)] with t h₁ h₂
  rw [h₁]
  rw [show q t = w t • p t from SchwartzMap.smulLeftCLM_apply_apply hw p t,
    Complex.real_smul, smul_eq_mul, ← mul_assoc, ← Complex.ofReal_mul]
  rw [show (1 + t^2 : ℝ) ^ (s / 4) * (1 + t^2) ^ (-s / 4) = 1 by
    rw [← Real.rpow_add (by positivity), show s / 4 + (-s / 4) = 0 by ring, Real.rpow_zero]]
  simp only [Complex.ofReal_one, one_mul]
  change p t = (p.toLp 2 (volume : Measure ℝ)) t
  exact h₂.symm

omit [∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ] in
set_option maxHeartbeats 1500000 in
/-- Separated Schwartz isotypes span a dense subspace of the global
zero-line Sobolev chart. -/
theorem globalZeroLineSchwartzIsotypes_span_dense (s : ℝ) :
    Dense (Submodule.span ℂ (range fun p : PontryaginDual (K F) × 𝓢(ℝ, ℂ) ↦
      globalZeroLineSchwartzIsotype F ν s p.1 p.2) : Set (Lp ℂ 2 (μ F ν))) := by
  letI : SecondCountableTopology (K F) := IsEmbedding.subtypeVal.secondCountableTopology
  letI : ν.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure ν
  let A := range (weightedSchwartzL2 s)
  let D := Submodule.span ℂ ((fun p : Lp ℂ 2 (volume : Measure ℝ) × Lp ℂ 2 ν ↦
    p.1 ⊗ₜ[ℂ] p.2) '' (A ×ˢ range (compactCharacterLp ν)))
  let T := (lpTwoTensorIsometry (μ := (volume : Measure ℝ)) (ν := ν)).toContinuousLinearMap
  let h := e_preserving F ν
  let P : Lp ℂ 2 (volume.prod ν) →L[ℂ] Lp ℂ 2 (μ F ν) :=
    (Lp.compMeasurePreservingₗᵢ ℂ (e F).symm (h.symm (e F))).toContinuousLinearMap
  have hP : Surjective P := by
    intro u
    let v := Lp.compMeasurePreserving (e F) h u
    refine ⟨v, Lp.ext ?_⟩
    filter_upwards [Lp.coeFn_compMeasurePreserving v (h.symm (e F)),
      (h.symm (e F)).quasiMeasurePreserving.ae_eq_comp (Lp.coeFn_compMeasurePreserving u h)]
      with q h₁ h₂
    exact h₁.trans (h₂.trans (congrArg u ((e F).apply_symm_apply q)))
  let L := P.comp T
  have hA : (Submodule.span ℂ A).topologicalClosure = ⊤ := by
    apply eq_top_iff.mpr
    intro v _
    exact closure_mono Submodule.subset_span (weightedSchwartz_dense s v)
  have hD : D.topologicalClosure = ⊤ := by
    have h : Dense (D : Set (Lp ℂ 2 (volume : Measure ℝ) ⊗[ℂ] Lp ℂ 2 ν)) :=
      dense_span_tmul hA (dense_span_compactCharacterLp ν)
    apply SetLike.coe_injective
    rw [Submodule.topologicalClosure_coe, Submodule.top_coe]
    exact dense_iff_closure_eq.mp h
  have hL : DenseRange L := hP.denseRange.comp denseRange_lpTwoTensorIsometry P.continuous
  have hLD := hL.topologicalClosure_map_submodule hD
  let C := Submodule.span ℂ (range fun p : PontryaginDual (K F) × 𝓢(ℝ, ℂ) ↦
    globalZeroLineSchwartzIsotype F ν s p.1 p.2)
  have hsub : D.map L.toLinearMap ≤ C := by
    change (Submodule.span ℂ _).map L.toLinearMap ≤ C
    rw [Submodule.map_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨_, ⟨⟨_, _⟩, ⟨⟨p, rfl⟩, ⟨χ, rfl⟩⟩, rfl⟩, rfl⟩
    exact Submodule.subset_span ⟨(χ,p), rfl⟩
  intro v
  apply closure_mono (show (D.map L.toLinearMap : Set (Lp ℂ 2 (μ F ν))) ⊆ C from hsub)
  change v ∈ (D.map L.toLinearMap).topologicalClosure
  rw [hLD]
  exact Submodule.mem_top

include mf hν in
set_option maxHeartbeats 1500000 in
/-- The polar-free global adelic theta tests are dense in the ambient
zero-line Sobolev chart for every nonnegative degree. -/
theorem globalThetaSobolevMap_zeroLine_dense (s : ℝ) (hs : 0 ≤ s) :
    DenseRange (globalThetaSobolevMap F (μ F ν) 0 0 0 s hs) := by
  let C := Submodule.span ℂ (range fun p : PontryaginDual (K F) × 𝓢(ℝ, ℂ) ↦
    globalZeroLineSchwartzIsotype F ν s p.1 p.2)
  have hC : C ≤ globalThetaSobolevCompletion F (μ F ν) 0 0 0 s hs := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨χ,p⟩, rfl⟩
    exact globalZeroLineSchwartzIsotype_mem F ν η mf hν s hs χ p
  intro v
  exact (closure_minimal hC (globalThetaSobolevCompletion_isClosed F (μ F ν) 0 0 0 s hs))
    (globalZeroLineSchwartzIsotypes_span_dense F ν s v)

omit [ν.IsHaarMeasure]
  [∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ] in
/-- Zero-line ambient theta density holds for every Haar normalization
on the idele classes. The compatible idelic and local measures exist. -/
theorem globalThetaSobolevMap_zeroLine_dense_of_haar
    (ρ : Measure (Q F)) [ρ.IsHaarMeasure] (s : ℝ) (hs : 0 ≤ s) :
    DenseRange (globalThetaSobolevMap F ρ 0 0 0 s hs) := by
  letI : LocallyCompactSpace (Idele F) := ideles_locallyCompact
  let η₀ : Measure (Idele F) := Measure.haar
  letI : η₀.IsHaarMeasure := inferInstance
  obtain ⟨ν₀, hν₀, hWeil⟩ := globalClassMeasure_exists_weil F η₀
  letI : ν₀.IsHaarMeasure := hν₀
  let ρ₀ := globalClassMeasure F ν₀
  letI : ρ₀.IsHaarMeasure := globalClassMeasure_isHaar F ν₀
  letI : ρ₀.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure ρ₀
  letI : ρ.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure ρ
  let c := Measure.haarScalarFactor ρ ρ₀
  have hc : c ≠ 0 := (Measure.haarScalarFactor_pos_of_isHaarMeasure ρ ρ₀).ne'
  have he : ρ = c • ρ₀ := Measure.isMulLeftInvariant_eq_smul_of_regular ρ ρ₀
  let ν₁ := c • ν₀
  let η₁ := c • η₀
  letI : ν₁.IsHaarMeasure := Measure.IsHaarMeasure.nnreal_smul _ hc
  letI : η₁.IsHaarMeasure := Measure.IsHaarMeasure.nnreal_smul _ hc
  have hmap : globalClassMeasure F ν₁ = ρ := by
    rw [he]
    unfold globalClassMeasure ν₁ ρ₀
    rw [Measure.prod_smul_right, Measure.map_smul]
    rfl
  have hWeilρ : IsWeilQuotientMeasure (principalIdeles F) η₁ Measure.count ρ := by
    refine ⟨inferInstance, inferInstance, fun f hf ↦ ?_⟩
    change (∫ x, f x ∂(c • η₀)) = _
    rw [integral_smul_nnreal_measure, hWeil.2.2 f hf, he, integral_smul_nnreal_measure]
  have hWeil₁ : IsWeilQuotientMeasure (principalIdeles F) η₁ Measure.count (globalClassMeasure F ν₁) :=
    hmap.symm ▸ hWeilρ
  letI (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) : LocallyCompactSpace (v.adicCompletion F) :=
    finitePlace_locallyCompact F v
  letI (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) : SecondCountableTopology (v.adicCompletion F) :=
    finitePlace_secondCountable F v
  letI (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) : SecondCountableTopology (v.adicCompletion F)ˣ :=
    Units.isEmbedding_val₀.secondCountableTopology
  letI (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) : MeasurableSpace (v.adicCompletion F)ˣ := borel _
  letI (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) : BorelSpace (v.adicCompletion F)ˣ := ⟨rfl⟩
  let mf₀ (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) : Measure (v.adicCompletion F)ˣ := Measure.haar
  letI (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) : (mf₀ v).IsHaarMeasure := inferInstance
  letI (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) : SigmaFinite (mf₀ v) := inferInstance
  letI : MeasurableSpace (InfiniteAdeleRing F)ˣ := borel _
  letI : BorelSpace (InfiniteAdeleRing F)ˣ := ⟨rfl⟩
  have hd := globalThetaSobolevMap_zeroLine_dense F ν₁ η₁ mf₀ hWeil₁ s hs
  have htransport (σ : Measure (Q F)) [σ.IsHaarMeasure] (hσ : σ = ρ)
      (hD : DenseRange (globalThetaSobolevMap F σ 0 0 0 s hs)) :
      DenseRange (globalThetaSobolevMap F ρ 0 0 0 s hs) := by
    subst σ
    exact hD
  exact htransport (globalClassMeasure F ν₁) hmap hd

omit [∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ] in
/-- Radial convolution on the separated Schwartz chart is represented by
the actual Bochner integral in the global Sobolev norm. -/
theorem globalZeroLineSchwartzIsotype_convolution (s : ℝ) (hs : 0 ≤ s)
    (χ : PontryaginDual (K F)) (p c : 𝓢(ℝ, ℂ))
    (hI : Integrable (fun t : ℝ ↦ c t • hardySobolevMulTranslation (μ F ν)
      (ideleClassLogNorm F) (ideleClassLogNorm_continuous F) 0 0 s hs (ray F t)
      (globalZeroLineSchwartzIsotype F ν s χ p))) :
    (∫ t : ℝ, c t • hardySobolevMulTranslation (μ F ν)
      (ideleClassLogNorm F) (ideleClassLogNorm_continuous F) 0 0 s hs (ray F t)
      (globalZeroLineSchwartzIsotype F ν s χ p)) =
      globalZeroLineSchwartzIsotype F ν s χ (SchwartzMap.convolution B p c) := by
  have hg : Continuous (ray F) := (ideleClassExpSection_continuous F).comp continuous_ofAdd
  apply globalZeroLine_integral_translate_eq F (μ F ν) volume s hs (ray F) hg.measurable
    c c.continuous.measurable _ _ (profile F χ p) (profile_continuous F χ p).measurable
    (globalZeroLineSchwartzIsotype_ae F ν s χ p) _ hI
  filter_upwards [globalZeroLineSchwartzIsotype_ae F ν s χ (SchwartzMap.convolution B p c)] with q hq
  exact hq.trans (congrArg ((amp F s q : ℂ) * ·) (convolution_profile F χ p c q))

end
end Masullo
