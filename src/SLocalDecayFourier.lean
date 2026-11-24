import SLocalCech
import SLocalFlatComponents
import ExponentialSchwartzCutoffs
import Mathlib.Analysis.Fourier.LpSpace
import L2HilbertTensorProduct

open Complex Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical NumberField SchwartzMap FourierTransform

namespace Masullo

noncomputable section

private abbrev Overlap := Ioo (0 : ℝ) 1
private abbrev RightStrip := Ioi (0 : ℝ)

/-- The exponent interval after Tate reflection. -/
def sLocalReflectedExponents (I : Set ℝ) : Set ℝ := (fun x : ℝ ↦ 1-x) ⁻¹' I

private theorem reflectedInterval {I : Set ℝ} (hI : IsOpen I) (hIo : OrdConnected I)
    (hIn : I.Nonempty) (hsub : I ⊆ Overlap) :
    let J := sLocalReflectedExponents I
    IsOpen J ∧ OrdConnected J ∧ J.Nonempty ∧ J ⊆ Overlap := by
  intro J
  refine ⟨hI.preimage (continuous_const.sub continuous_id),
    hIo.preimage_anti (fun _ _ h ↦ sub_le_sub_left h 1), ?_, ?_⟩
  · obtain ⟨x,hx⟩ := hIn
    refine ⟨1-x, ?_⟩
    change 1-(1-x) ∈ I
    rwa [sub_sub_cancel]
  · intro x hx
    have h : 1-x ∈ Overlap := hsub hx
    exact ⟨by linarith [h.2], by linarith [h.1]⟩

private theorem ext_on_strip {I : Set ℝ} {f g : SchwartzBergman I}
    (h : ∀ z : ℂ, z.re ∈ I → f.val z = g.val z) : f = g := by
  apply Subtype.ext
  funext z
  by_cases hz : z.re ∈ I
  · exact h z hz
  · exact (f.property.1 hz).trans (g.property.1 hz).symm

private abbrev HolomorphicOnOverlap (r : ℂ → ℂ) := AnalyticOnNhd ℂ r (Complex.re ⁻¹' Overlap)
private abbrev StripBound (r : ℂ → ℂ) :=
  ∀ l b : ℝ, 0 < l → b < 1 →
    ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧ ∀ z : ℂ, z.re ∈ Icc l b → ‖r z‖ ≤ C * (1 + |z.im|)^k

/-- Tate reflection, with the reciprocal multiplier on the incoming strip. -/
private theorem exists_tateReflection {I : Set ℝ} (hI : IsOpen I) (hIo : OrdConnected I)
    (hIn : I.Nonempty) (hsub : I ⊆ Overlap)
    (ρ : ℂ → ℂ) (hρ : HolomorphicOnOverlap ρ) (hb : StripBound ρ)
    (hinv : HolomorphicOnOverlap (fun z ↦ (ρ z)⁻¹)) (hib : StripBound (fun z ↦ (ρ z)⁻¹))
    (hn : ∀ z, z.re ∈ Overlap → ρ z ≠ 0) :
    ∃ A : SchwartzBergman I ≃L[ℂ] SchwartzBergman (sLocalReflectedExponents I),
      ∀ f z, z.re ∈ sLocalReflectedExponents I → (A f).val z = (ρ (1-z))⁻¹ * f.val (1-z) := by
  let J := sLocalReflectedExponents I
  obtain ⟨hj,hjo,hjn,_⟩ := reflectedInterval hI hIo hIn hsub
  have hpol {r : ℂ → ℂ} (h : StripBound r) (l b : ℝ) (hlb : l ≤ b) (hs : Icc l b ⊆ I) :=
    h l b (hsub (hs ⟨le_rfl,hlb⟩)).1 (hsub (hs ⟨hlb,le_rfl⟩)).2
  let M := schwartzBergmanRestrictMul hI hIo hIn hI hIo hIn (Subset.rfl) ρ
    (fun z hz ↦ hρ z (hsub hz)) (hpol hb)
  let N := schwartzBergmanRestrictMul hI hIo hIn hI hIo hIn (Subset.rfl) (fun z ↦ (ρ z)⁻¹)
    (fun z hz ↦ hinv z (hsub hz)) (hpol hib)
  have hM (f : SchwartzBergman I) (z : ℂ) (hz : z.re ∈ I) :
      (M f).val z = ρ z * f.val z := schwartzBergmanRestrictMul_apply _ _ _ _ _ _ _ _ _ _ _ z hz
  have hN (f : SchwartzBergman I) (z : ℂ) (hz : z.re ∈ I) :
      (N f).val z = (ρ z)⁻¹ * f.val z := schwartzBergmanRestrictMul_apply _ _ _ _ _ _ _ _ _ _ _ z hz
  let L := ContinuousLinearEquiv.equivOfInverse N M
    (fun f ↦ ext_on_strip (fun z hz ↦ by
      rw [hM _ _ hz, hN _ _ hz, ← mul_assoc, mul_inv_cancel₀ (hn z (hsub hz)), one_mul]))
    (fun f ↦ ext_on_strip (fun z hz ↦ by
      rw [hN _ _ hz, hM _ _ hz, ← mul_assoc, inv_mul_cancel₀ (hn z (hsub hz)), one_mul]))
  let R := schwartzBergmanReflectEquiv hI hIo hIn hj hjo hjn (fun _ ↦ Iff.rfl)
  refine ⟨L.trans R, fun f z hz ↦ ?_⟩
  have hz' : (1-z).re ∈ I := by
    change 1-z.re ∈ I at hz
    simpa only [Complex.sub_re, Complex.one_re] using hz
  exact (schwartzBergmanReflectEquiv_apply hI hIo hIn hj hjo hjn
    (fun _ ↦ Iff.rfl) (L f) z).trans (hN f (1-z) hz')

/-- Compact truncations in the entire decay space converge in all the
weighted Schwartz seminorms of the indicated interval. -/
private theorem exists_entireTruncations {I : Set ℝ} (hIn : I.Nonempty)
    (p : PositiveRealExponentialDecay I) :
    ∃ (v : ℕ → PositiveRealExponentialDecay univ) (u : ℕ → PositiveRealExponentialDecay I),
      (∀ n, (u n).val = (v n).val) ∧ Tendsto u atTop (𝓝 p) := by
  obtain ⟨a,ha⟩ := hIn
  let g := logExponentialDecayTwist I ⟨a,ha⟩ p
  let w (n : ℕ) (x : ℝ) := (Real.exp (-a*x) : ℂ) * truncateSchwartz n g x
  have htruncate (n : ℕ) (f : 𝓢(ℝ,ℂ)) (x : ℝ) :
      truncateSchwartz n f x = truncationMultiplier n x * f x :=
    SchwartzMap.smulLeftCLM_apply_apply (truncationMultiplier_growth n) f x
  have hw (n : ℕ) (x : ℝ) : w n x = truncationMultiplier n x * p.val x := by
    change (Real.exp (-a*x) : ℂ) * truncateSchwartz n g x = _
    rw [htruncate]
    have he : g x = (Real.exp (a*x) : ℂ) * p.val x := logExponentialDecayTwist_apply I ⟨a,ha⟩ p x
    rw [he, ← mul_assoc, mul_comm _ (truncationMultiplier n x), mul_assoc,
      ← mul_assoc ((Real.exp (-a*x) : ℂ)), ← Complex.ofReal_mul, ← Real.exp_add,
      neg_mul, neg_add_cancel, Real.exp_zero, Complex.ofReal_one, one_mul]
  let v (n : ℕ) : PositiveRealExponentialDecay univ :=
    ⟨w n, mem_logExponentialDecaySubmodule_of_hasCompactSupport univ
      (truncateSchwartz_hasCompactSupport n g).mul_left
      ((Complex.ofRealCLM.contDiff.comp (Real.contDiff_exp.comp
        (contDiff_const.mul contDiff_id))).mul ((truncateSchwartz n g).smooth ⊤))⟩
  let u (n : ℕ) : PositiveRealExponentialDecay I := ⟨(v n).val,
    (Submodule.mem_iInf _).mpr fun b ↦ (Submodule.mem_iInf _).mp (v n).property ⟨b.val,mem_univ _⟩⟩
  refine ⟨v,u,fun _ ↦ rfl,?_⟩
  apply (positiveRealExponentialDecay_isEmbedding I ⟨a,ha⟩).isInducing.tendsto_nhds_iff.mpr
  apply tendsto_pi_nhds.mpr
  intro b
  have he (n : ℕ) : logExponentialDecayTwist I b (u n) = truncateSchwartz n (logExponentialDecayTwist I b p) := by
    ext x
    calc
      _ = (Real.exp (b.val*x) : ℂ) * w n x := logExponentialDecayTwist_apply I b (u n) x
      _ = truncationMultiplier n x * ((Real.exp (b.val*x) : ℂ) * p.val x) := by rw [hw]; ring
      _ = _ := ((htruncate n (logExponentialDecayTwist I b p) x).trans
        (congrArg (truncationMultiplier n x * ·) (logExponentialDecayTwist_apply I b p x))).symm
  simpa only [Function.comp_apply,he] using truncateSchwartz_tendsto (logExponentialDecayTwist I b p)

/-- The central Hilbert realization of a logarithmic profile multiplies
by the square root of the original multiplicative modulus. -/
def sLocalDecayCentralTrace {I : Set ℝ} (hhalf : (1/2 : ℝ) ∈ I) :
    PositiveRealExponentialDecay I →L[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  (SchwartzMap.toLpCLM ℂ ℂ 2 volume).comp
    ⟨logExponentialDecayTwist I ⟨1/2,hhalf⟩,
      (continuous_apply (⟨1/2,hhalf⟩ : I)).comp
        (positiveRealExponentialDecay_isEmbedding I ⟨_,hhalf⟩).continuous⟩

theorem sLocalDecayCentralTrace_ae {I : Set ℝ} (hhalf : (1/2 : ℝ) ∈ I)
    (p : PositiveRealExponentialDecay I) :
    (sLocalDecayCentralTrace hhalf p : ℝ → ℂ) =ᵐ[volume]
      fun t ↦ (Real.exp (t/2) : ℂ) * p.val t := by
  exact ((logExponentialDecayTwist I ⟨1/2,hhalf⟩ p).coeFn_toLp 2 volume).trans
    (Eventually.of_forall fun t ↦ (logExponentialDecayTwist_apply I ⟨1/2,hhalf⟩ p t).trans (by
      rw [show (1/2 : ℝ) * t = t/2 by ring]))

theorem sLocalDecayCentralTrace_injective {I : Set ℝ} (hhalf : (1/2 : ℝ) ∈ I) :
    Injective (sLocalDecayCentralTrace hhalf) := by
  intro p q h
  have he := SchwartzMap.injective_toLp (F := ℂ) 2 (volume : Measure ℝ) h
  apply Subtype.ext
  funext t
  have ht := (logExponentialDecayTwist_apply I ⟨1/2,hhalf⟩ p t).symm.trans
    ((congrArg (fun g : 𝓢(ℝ,ℂ) ↦ g t) he).trans
      (logExponentialDecayTwist_apply I ⟨1/2,hhalf⟩ q t))
  exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne') ht

/-- Compactly supported smooth profiles already give a dense central
trace in the scalar Hilbert space. -/
theorem sLocalDecayCentralTrace_dense {I : Set ℝ} (h : (1/2 : ℝ) ∈ I) :
    DenseRange (sLocalDecayCentralTrace h) := by
  let T := SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure ℝ)
  have hT : DenseRange T := SchwartzMap.denseRange_toLpCLM (μ := (volume : Measure ℝ)) (by norm_num)
  intro f
  refine closure_minimal ?_ isClosed_closure (hT f)
  rintro _ ⟨g,rfl⟩
  let p (n : ℕ) : PositiveRealExponentialDecay I :=
    ⟨fun t ↦ (Real.exp (-(t/2)) : ℂ) * truncateSchwartz n g t,
      mem_logExponentialDecaySubmodule_of_hasCompactSupport I
        (truncateSchwartz_hasCompactSupport n g).mul_left
        ((Complex.ofRealCLM.contDiff.comp (Real.contDiff_exp.comp (by fun_prop))).mul
          ((truncateSchwartz n g).smooth ⊤))⟩
  have he (n : ℕ) : logExponentialDecayTwist I ⟨1/2,h⟩ (p n) = truncateSchwartz n g := by
    ext t
    calc
      _ = (Real.exp ((1/2 : ℝ)*t) : ℂ) * ((Real.exp (-(t/2)) : ℂ) * truncateSchwartz n g t) :=
        logExponentialDecayTwist_apply I ⟨1/2,h⟩ (p n) t
      _ = _ := by
        rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add,
          show (1/2 : ℝ)*t + -(t/2) = 0 by ring, Real.exp_zero,Complex.ofReal_one,one_mul]
  have ht : Tendsto (fun n ↦ T (truncateSchwartz n g)) atTop (𝓝 (T g)) :=
    (T.continuous.tendsto g).comp (truncateSchwartz_tendsto g)
  exact mem_closure_of_tendsto ht (Eventually.of_forall fun n ↦
    ⟨p n, congrArg T (he n)⟩)

set_option maxHeartbeats 900000 in
/-- An isomorphism of decay profiles that preserves the central norm
extends to a unitary operator on the central scalar Hilbert space. -/
theorem exists_sLocalDecayCentralTrace_unitary {I J : Set ℝ} (h : (1/2 : ℝ) ∈ I) (h' : (1/2 : ℝ) ∈ J)
    (A : PositiveRealExponentialDecay I ≃L[ℂ] PositiveRealExponentialDecay J)
    (hA : ∀ p, ‖sLocalDecayCentralTrace h' (A p)‖ = ‖sLocalDecayCentralTrace h p‖) :
    ∃ U : Lp ℂ 2 (volume : Measure ℝ) ≃ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure ℝ),
      ∀ p, U (sLocalDecayCentralTrace h p) = sLocalDecayCentralTrace h' (A p) := by
  let C := (sLocalDecayCentralTrace h).toLinearMap
  let D := (sLocalDecayCentralTrace h').toLinearMap
  let R := C.range
  let e : PositiveRealExponentialDecay I ≃ₗ[ℂ] R :=
    LinearEquiv.ofInjective C (sLocalDecayCentralTrace_injective h)
  let i := R.subtypeₗᵢ
  let j : R →ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
    { toLinearMap := D.comp (A.toLinearMap.comp e.symm.toLinearMap)
      norm_map' := by
        intro u
        change ‖sLocalDecayCentralTrace h' (A (e.symm u))‖ = ‖u.val‖
        have he : C (e.symm u) = u.val := congrArg Subtype.val (e.apply_symm_apply u)
        exact (hA (e.symm u)).trans (congrArg norm he) }
  have hi : DenseRange i := by
    apply (sLocalDecayCentralTrace_dense h).mono
    rintro _ ⟨p,rfl⟩
    exact ⟨e p,rfl⟩
  have hj : DenseRange j := by
    apply (sLocalDecayCentralTrace_dense h').mono
    rintro _ ⟨q,rfl⟩
    obtain ⟨p,rfl⟩ := A.surjective q
    exact ⟨e p,congrArg (fun w ↦ D (A w)) (e.symm_apply_apply p)⟩
  let a := completionLinearIsometryEquiv i hi
  let b := completionLinearIsometryEquiv j hj
  refine ⟨a.symm.trans b,fun p ↦ ?_⟩
  have he : a (e p : UniformSpace.Completion R) = C p :=
    completionLinearIsometryEquiv_coe i hi (e p)
  rw [← show C p = sLocalDecayCentralTrace h p from rfl, ← he]
  change b (a.symm (a (e p : UniformSpace.Completion R))) = D (A p)
  rw [a.symm_apply_apply]
  exact (completionLinearIsometryEquiv_coe j hj (e p)).trans
    (congrArg (fun w ↦ D (A w)) (e.symm_apply_apply p))

private def centralLine (y : ℝ) : ℂ := (1/2 : ℂ) + ((2 * Real.pi * y : ℝ) : ℂ) * Complex.I

private theorem centralLine_re (y : ℝ) : (centralLine y).re = 1/2 := by
  simp [centralLine]

private theorem centralLine_reflect (y : ℝ) : 1 - centralLine y = centralLine (-y) := by
  simp only [centralLine, mul_neg, Complex.ofReal_neg]
  ring

private def centralSchwartz {I : Set ℝ} (h : (1/2 : ℝ) ∈ I) (p : PositiveRealExponentialDecay I) :
    𝓢(ℝ,ℂ) :=
  schwartzChangeVariable ℂ (LinearIsometryEquiv.neg ℝ : ℝ ≃ₗᵢ[ℝ] ℝ).toContinuousLinearEquiv
    (logExponentialDecayTwist I ⟨1/2,h⟩ p)

private theorem central_mellin_fourier {I : Set ℝ} (hI : IsOpen I) (hIo : OrdConnected I)
    (hIn : I.Nonempty) (h : (1/2 : ℝ) ∈ I) (p : PositiveRealExponentialDecay I) (y : ℝ) :
    (positiveRealFourierMellin I hI hIo hIn p).val (centralLine y) =
      (𝓕 (centralSchwartz h p)) y := by
  have hre := centralLine_re y
  rw [positiveRealFourierMellin_apply _ hI hIo hIn p _ (hre ▸ h), mellin_eq_fourier,
    SchwartzMap.fourier_coe]
  have him : (centralLine y).im = 2 * Real.pi * y := by
    simp [centralLine]
  have hy : (centralLine y).im / (2 * Real.pi) = y := by
    rw [him, mul_comm, mul_div_cancel_right₀ _ (mul_ne_zero two_ne_zero Real.pi_ne_zero)]
  rw [hy]
  apply congrArg (fun g : ℝ → ℂ ↦ 𝓕 g y)
  funext x
  refine (Eq.trans ?_ (logExponentialDecayTwist_apply I ⟨1/2,h⟩ p (-x)).symm)
  simp only [hre, Real.log_exp, Complex.real_smul, mul_neg, neg_mul]

private theorem centralSchwartz_norm {I : Set ℝ} (h : (1/2 : ℝ) ∈ I)
    (p : PositiveRealExponentialDecay I) :
    ‖(𝓕 (centralSchwartz h p)).toLp 2 (volume : Measure ℝ)‖ = ‖sLocalDecayCentralTrace h p‖ := by
  rw [← SchwartzMap.toLp_fourier_eq, MeasureTheory.Lp.norm_fourier_eq]
  change ‖(centralSchwartz h p).toLp 2 (volume : Measure ℝ)‖ =
    ‖(logExponentialDecayTwist I ⟨1/2,h⟩ p).toLp 2 (volume : Measure ℝ)‖
  rw [SchwartzMap.norm_toLp, SchwartzMap.norm_toLp]
  exact congrArg ENNReal.toReal (eLpNorm_comp_measurePreserving
    (logExponentialDecayTwist I ⟨1/2,h⟩ p).continuous.aestronglyMeasurable
    (Measure.measurePreserving_neg (volume : Measure ℝ)))

section Actual

variable (F : Type*) [Field F] [NumberField F]
variable (S : Finset (HeightOneSpectrum (𝓞 F)))
local instance : LocallyCompactSpace (SAdeles F S)ˣ := sLocalIdeles_locallyCompact F S
local instance : LocallyCompactSpace (SIdeleQuotient F S) :=
  QuotientGroup.isOpenQuotientMap_mk.locallyCompactSpace
local instance : T2Space (SIdeleQuotient F S) := by
  letI : T1Space (SIdeleQuotient F S) := QuotientGroup.t1Space_iff.mpr (sUnitImage_closed F S)
  exact inferInstance

private abbrev K := SLocalThetaNormOne F S
private abbrev V (v : S) := v.val.adicCompletion F
private abbrev E := sLocalBruhatImage F S

attribute [local instance] sLocalZetaUnfolding_classMeasurable sLocalZetaUnfolding_classBorel
  sLocalZetaUnfolding_idelesMeasurable sLocalZetaUnfolding_idelesBorel

variable [∀ v : S, MeasurableSpace (V F S v)ˣ] [∀ v : S, BorelSpace (V F S v)ˣ]
  (μ : ∀ v : S, Measure (V F S v)ˣ)
  [∀ v : S, (μ v).IsHaarMeasure] [∀ v : S, SigmaFinite (μ v)]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]

private abbrev μprod := sLocalZetaProductMeasure F S μ (archimedeanMultiplicativeHaar F)

variable (ν : Measure (K F S)) [ν.IsHaarMeasure]
  (hν : IsWeilQuotientMeasure (sUnitImage F S) (μprod F S μ) Measure.count
    (sLocalClassHaar F S ν))
  [MeasurableSpace (InfiniteAdeleRing F)] [BorelSpace (InfiniteAdeleRing F)]

private abbrev θ (ω : PontryaginDual (K F S)) (f : E F S) (t : ℝ) :=
  sLocalHomogeneousTheta F S ν ω f.val
    (QuotientGroup.mk (sLocalExpSection F S (Multiplicative.ofAdd t)))

private def thetaProfile {I : Set ℝ} (hI : I ⊆ RightStrip)
    (ω : PontryaginDual (K F S)) (f : E F S) : PositiveRealExponentialDecay I :=
  let p := (positiveRealFourierMellin RightStrip isOpen_Ioi ordConnected_Ioi nonempty_Ioi).symm
    (sLocalRightBergmanMellin F S ν ω (Submodule.Quotient.mk f))
  ⟨p.val, (Submodule.mem_iInf _).mpr fun a ↦
    (Submodule.mem_iInf _).mp p.property ⟨a.val,hI a.property⟩⟩

omit [∀ v : S, BorelSpace (V F S v)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)] [BorelSpace (InfiniteAdeleRing F)] in
private theorem thetaProfile_apply {I : Set ℝ} (hI : I ⊆ RightStrip)
    (ω : PontryaginDual (K F S)) (f : E F S) (t : ℝ) :
    (thetaProfile F S ν hI ω f).val t = θ F S ν ω f t :=
  sLocalRightBergmanMellin_inverse_apply F S ν ω f t

include hν in
private theorem thetaProfile_mellin {I : Set ℝ} (hI : IsOpen I) (hIo : OrdConnected I)
    (hIn : I.Nonempty) (hsub : I ⊆ RightStrip)
    (ω : PontryaginDual (K F S)) (f : E F S) (z : ℂ) (hz : z.re ∈ I) :
    (positiveRealFourierMellin I hI hIo hIn (thetaProfile F S ν hsub ω f)).val z =
      sLocalIdelicZetaIntegral F S (μprod F S μ) ω f z := by
  letI : (μprod F S μ).IsHaarMeasure :=
    sLocalZetaProductMeasure_isHaar F S μ (archimedeanMultiplicativeHaar F)
  have hp : 0 < z.re := hsub hz
  rw [positiveRealFourierMellin_apply _ hI hIo hIn _ _ hz, mellin_eq_log_integral]
  simp only [Real.log_exp, thetaProfile_apply]
  exact ((sLocalThetaZeta_integrable_eq_radial F S ν ω f z hp).2).symm.trans
    ((sLocalIdelicZeta_integrable_eq_theta F S (μprod F S μ) ν hν ω f z hp).2).symm

set_option maxHeartbeats 1600000 in
include hν in
/-- The S-local Fourier operator extends continuously and invertibly on
logarithmic profiles for every open subinterval of the overlap. -/
theorem exists_sLocalDecayFourier_profiles (ω : PontryaginDual (K F S))
    (I : Set ℝ) (hI : IsOpen I) (hIo : OrdConnected I) (hIn : I.Nonempty) (hsub : I ⊆ Overlap) :
    ∃ A : PositiveRealExponentialDecay I ≃L[ℂ] PositiveRealExponentialDecay (sLocalReflectedExponents I),
      (∀ (f : E F S),
        ∃ p : PositiveRealExponentialDecay I,
          (∀ t, p.val t = θ F S ν ω f t) ∧
          ∀ t, (A p).val t = θ F S ν ω⁻¹ (sLocalSelectedFourier F S f) t) ∧
      (∀ (h : (1/2 : ℝ) ∈ I) (h' : (1/2 : ℝ) ∈ sLocalReflectedExponents I)
        (p : PositiveRealExponentialDecay I),
        ‖sLocalDecayCentralTrace h' (A p)‖ = ‖sLocalDecayCentralTrace h p‖) := by
  let J := sLocalReflectedExponents I
  obtain ⟨hj,hjo,hjn,hjs⟩ := reflectedInterval hI hIo hIn hsub
  have hIpos : I ⊆ RightStrip := fun _ h ↦ (hsub h).1
  have hJpos : J ⊆ RightStrip := fun _ h ↦ (hjs h).1
  obtain ⟨ε,hε,_,_,_,_,hFE,_,_,_⟩ := exists_sLocalTateProduct_functionalEquation F S μ ω
  let ρ := sLocalExplicitTateFactor F S ω (sLocalTateEpsilonProduct F S ω ε)
  obtain ⟨hA,hB⟩ := sLocalTateRatio_overlap_growth F S μ ω ε hε
  obtain ⟨hi,hib⟩ := sLocalTateRatio_inverse_overlap_growth F S μ ω ε hε
  obtain ⟨T,hT⟩ := exists_tateReflection hI hIo hIn hsub ρ
    (fun z hz ↦ hA z hz.1 hz.2) hB
    (fun z hz ↦ (hi z hz.1 hz.2).2) hib (fun z hz ↦ (hi z hz.1 hz.2).1)
  let M := positiveRealFourierMellin I hI hIo hIn
  let N := positiveRealFourierMellin J hj hjo hjn
  let A := M.trans (T.trans N.symm)
  refine ⟨A, ?_, ?_⟩
  swap
  · intro h h' p
    let G := 𝓕 (centralSchwartz h p)
    let H := 𝓕 (centralSchwartz h' (A p))
    have hnorm (y : ℝ) : ‖H y‖ = ‖G (-y)‖ := by
      have hz : (centralLine y).re ∈ J := centralLine_re y ▸ h'
      have hNp : N (A p) = T (M p) := N.apply_symm_apply _
      have h₁ := central_mellin_fourier hj hjo hjn h' (A p) y
      have h₂ := central_mellin_fourier hI hIo hIn h p (-y)
      have he : H y = (ρ (1-centralLine y))⁻¹ * G (-y) :=
        h₁.symm.trans ((congrArg (fun g : SchwartzBergman J ↦ g.val (centralLine y)) hNp).trans
          ((hT (M p) _ hz).trans (congrArg ((ρ (1-centralLine y))⁻¹ * ·)
            ((congrArg (M p).val (centralLine_reflect y)).trans h₂))))
      have hc : (1-centralLine y).re = 1/2 := (congrArg Complex.re (centralLine_reflect y)).trans
        (centralLine_re (-y))
      rw [he,norm_mul,norm_inv,sLocalTateRatio_norm_critical F S μ ω ε hε _ hc,inv_one,one_mul]
    have hLp : ‖H.toLp 2 (volume : Measure ℝ)‖ = ‖G.toLp 2 (volume : Measure ℝ)‖ := by
      rw [SchwartzMap.norm_toLp,SchwartzMap.norm_toLp]
      apply congrArg ENNReal.toReal
      exact (eLpNorm_congr_norm_ae (Eventually.of_forall hnorm)).trans
        (eLpNorm_comp_measurePreserving G.continuous.aestronglyMeasurable
          (Measure.measurePreserving_neg (volume : Measure ℝ)))
    exact (centralSchwartz_norm h' (A p)).symm.trans (hLp.trans (centralSchwartz_norm h p))
  intro f
  let p := thetaProfile F S ν hIpos ω f
  let q := thetaProfile F S ν hJpos ω⁻¹ (sLocalSelectedFourier F S f)
  have he : T (M p) = N q := by
    apply ext_on_strip
    intro z hz
    have hz' : (1-z).re ∈ I := by
      change 1-z.re ∈ I at hz
      simpa only [Complex.sub_re, Complex.one_re] using hz
    have h := hsub hz'
    have hM := thetaProfile_mellin F S μ ν hν hI hIo hIn hIpos ω f (1-z) hz'
    have hN := thetaProfile_mellin F S μ ν hν hj hjo hjn hJpos ω⁻¹
      (sLocalSelectedFourier F S f) z hz
    have hF := hFE f (1-z) h.1 h.2
    rw [sub_sub_cancel] at hF
    calc
      _ = (ρ (1-z))⁻¹ * (M p).val (1-z) := hT _ _ hz
      _ = (ρ (1-z))⁻¹ * (ρ (1-z) * (N q).val z) :=
        congrArg ((ρ (1-z))⁻¹ * ·) (hM.trans (hF.trans (congrArg (ρ (1-z) * ·) hN.symm)))
      _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ (hi _ h.1 h.2).1, one_mul]
  refine ⟨p, thetaProfile_apply F S ν hIpos ω f, fun t ↦ ?_⟩
  have hap : A p = q := by
    change N.symm (T (M p)) = q
    rw [he,N.symm_apply_apply]
  exact (congrArg (fun g : PositiveRealExponentialDecay J ↦ g.val t) hap).trans
    (thetaProfile_apply F S ν hJpos ω⁻¹ _ t)

set_option maxHeartbeats 2400000 in
include hν in
/-- Proposition 5.4.2.1(1), with the inverse norm-one character on the
Fourier side. The isotypes carry the actual weighted inductive topology. -/
theorem exists_sLocalDecayFourier (ω : PontryaginDual (K F S))
    (I : Set ℝ) (hI : IsOpen I) (hIo : OrdConnected I) (hIn : I.Nonempty) (hsub : I ⊆ Overlap) :
    ∃ A : sLocalCechDecayIsotype F S ω I ≃L[ℂ]
        sLocalCechDecayIsotype F S ω⁻¹ (sLocalReflectedExponents I),
      ∀ (f : E F S), ∃ u : sLocalCechDecayIsotype F S ω I,
        (∀ g : SIdeleQuotient F S, u.val.val g = sLocalHomogeneousTheta F S ν ω f.val g) ∧
        ∀ g : SIdeleQuotient F S, (A u).val.val g =
          sLocalHomogeneousTheta F S ν ω⁻¹ (sLocalSelectedFourier F S f).val g := by
  let J := sLocalReflectedExponents I
  obtain ⟨_,_,hJn,_⟩ := reflectedInterval hI hIo hIn hsub
  let τ : Multiplicative ℝ →* SIdeleQuotient F S :=
    (QuotientGroup.mk' (sUnitImage F S)).comp (sLocalExpSection F S)
  have hτ : Continuous τ := QuotientGroup.continuous_mk.comp (sLocalExpSection_continuous F S)
  have hmod (t : ℝ) : sLocalClassModulus F S (τ (Multiplicative.ofAdd t)) = Real.exp t :=
    sLocalIdeleNorm_expSection F S t
  obtain ⟨e,he⟩ := exists_sLocalCechRadialIsotype F S ω I hIn τ hτ hmod
  obtain ⟨e',he'⟩ := exists_sLocalCechRadialIsotype F S ω⁻¹ J hJn τ hτ hmod
  obtain ⟨T,hT,_⟩ := exists_sLocalDecayFourier_profiles F S μ ν hν ω I hI hIo hIn hsub
  let A := e.symm.trans (T.trans e')
  refine ⟨A,fun f ↦ ?_⟩
  obtain ⟨p,hp,hq⟩ := hT f
  refine ⟨e p,?_,?_⟩
  · exact sLocalCechIsotype_eq_theta_of_section F S ν ω τ hmod f (e p) (fun t ↦
      (he (e p) t).symm.trans
        ((congrArg (fun v : PositiveRealExponentialDecay I ↦ v.val t) (e.symm_apply_apply p)).trans
          (hp t)))
  · have ha : A (e p) = e' (T p) := congrArg (fun v ↦ e' (T v)) (e.symm_apply_apply p)
    rw [ha]
    exact sLocalCechIsotype_eq_theta_of_section F S ν ω⁻¹ τ hmod
      (sLocalSelectedFourier F S f) (e' (T p)) (fun t ↦
        (he' (e' (T p)) t).symm.trans
          ((congrArg (fun v : PositiveRealExponentialDecay J ↦ v.val t)
            (e'.symm_apply_apply (T p))).trans (hq t)))

omit [∀ v : S, BorelSpace (V F S v)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)] [BorelSpace (InfiniteAdeleRing F)] in
/-- The dense domain consists of actual homogeneous theta functions. -/
theorem dense_sLocalDecayTheta (ω : PontryaginDual (K F S)) (I : Set ℝ) (hIn : I.Nonempty) :
    Dense {u : sLocalCechDecayIsotype F S ω I |
      ∃ f : E F S, ∀ g : SIdeleQuotient F S, u.val.val g = sLocalHomogeneousTheta F S ν ω f.val g} := by
  let τ : Multiplicative ℝ →* SIdeleQuotient F S :=
    (QuotientGroup.mk' (sUnitImage F S)).comp (sLocalExpSection F S)
  have hτ : Continuous τ := QuotientGroup.continuous_mk.comp (sLocalExpSection_continuous F S)
  have hmod (t : ℝ) : sLocalClassModulus F S (τ (Multiplicative.ofAdd t)) = Real.exp t :=
    sLocalIdeleNorm_expSection F S t
  obtain ⟨e,he⟩ := exists_sLocalCechRadialIsotype F S ω I hIn τ hτ hmod
  intro u
  obtain ⟨v,p,hp,ht⟩ := exists_entireTruncations hIn (e.symm u)
  have hmem (n : ℕ) : ∃ f : E F S, ∀ g : SIdeleQuotient F S,
      (e (p n)).val.val g = sLocalHomogeneousTheta F S ν ω f.val g := by
    obtain ⟨f,hf⟩ := exists_sLocalHomogeneousTheta_polarFree_of_profile F S ν ω (v n)
    refine ⟨f.val,sLocalCechIsotype_eq_theta_of_section F S ν ω τ hmod f.val (e (p n)) ?_⟩
    intro t
    exact (he (e (p n)) t).symm.trans
      ((congrArg (fun z : PositiveRealExponentialDecay I ↦ z.val t) (e.symm_apply_apply (p n))).trans
        ((congrFun (hp n) t).trans (hf t).symm))
  have hu : Tendsto (fun n ↦ e (p n)) atTop (𝓝 u) :=
    e.apply_symm_apply u ▸ (e.continuous.tendsto (e.symm u)).comp ht
  exact mem_closure_of_tendsto hu (Eventually.of_forall hmem)

set_option maxHeartbeats 3500000 in
include hν in
/-- The extension in Proposition 5.4.2.1(1) is uniquely determined by the
selected-place Fourier transform on its dense theta domain. -/
theorem existsUnique_sLocalDecayFourier (ω : PontryaginDual (K F S))
    (I : Set ℝ) (hI : IsOpen I) (hIo : OrdConnected I) (hIn : I.Nonempty) (hsub : I ⊆ Overlap) :
    ∃! A : sLocalCechDecayIsotype F S ω I ≃L[ℂ]
        sLocalCechDecayIsotype F S ω⁻¹ (sLocalReflectedExponents I),
      ∀ (f : E F S), ∃ u : sLocalCechDecayIsotype F S ω I,
        (∀ g : SIdeleQuotient F S, u.val.val g = sLocalHomogeneousTheta F S ν ω f.val g) ∧
        ∀ g : SIdeleQuotient F S, (A u).val.val g =
          sLocalHomogeneousTheta F S ν ω⁻¹ (sLocalSelectedFourier F S f).val g := by
  obtain ⟨A,hA⟩ := exists_sLocalDecayFourier F S μ ν hν ω I hI hIo hIn hsub
  refine ⟨A,hA,fun B hB ↦ ?_⟩
  have he : EqOn B A {u : sLocalCechDecayIsotype F S ω I |
      ∃ f : E F S, ∀ g : SIdeleQuotient F S, u.val.val g = sLocalHomogeneousTheta F S ν ω f.val g} := by
    rintro u ⟨f,hf⟩
    obtain ⟨uA,h₁,h₂⟩ := hA f
    obtain ⟨uB,h₃,h₄⟩ := hB f
    have he₁ : uA = u := Subtype.ext (ModulatedExponentialInductive.algebraicEquiv.injective
      (Subtype.ext (funext fun g ↦ (h₁ g).trans (hf g).symm)))
    have he₂ : uB = u := Subtype.ext (ModulatedExponentialInductive.algebraicEquiv.injective
      (Subtype.ext (funext fun g ↦ (h₃ g).trans (hf g).symm)))
    have hAB : B uB = A uA := Subtype.ext (ModulatedExponentialInductive.algebraicEquiv.injective
      (Subtype.ext (funext fun g ↦ (h₄ g).trans (h₂ g).symm)))
    exact (congrArg B he₂.symm).trans (hAB.trans (congrArg A he₁))
  letI : T2Space (PositiveRealExponentialDecay I) :=
    (positiveRealExponentialDecay_isEmbedding I hIn).t2Space
  let τ : Multiplicative ℝ →* SIdeleQuotient F S :=
    (QuotientGroup.mk' (sUnitImage F S)).comp (sLocalExpSection F S)
  have hτ : Continuous τ := QuotientGroup.continuous_mk.comp (sLocalExpSection_continuous F S)
  have hmod (t : ℝ) : sLocalClassModulus F S (τ (Multiplicative.ofAdd t)) = Real.exp t :=
    sLocalIdeleNorm_expSection F S t
  obtain ⟨e,_⟩ := exists_sLocalCechRadialIsotype F S ω I hIn τ hτ hmod
  letI : T2Space (sLocalCechDecayIsotype F S ω⁻¹ (sLocalReflectedExponents I)) :=
    (e.trans A).symm.toHomeomorph.isEmbedding.t2Space
  exact ContinuousLinearEquiv.ext (funext fun p ↦
    closure_minimal he (isClosed_eq B.continuous A.continuous)
      (dense_sLocalDecayTheta F S ν ω I hIn p))

omit [∀ v : S, BorelSpace (V F S v)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)] [BorelSpace (InfiniteAdeleRing F)] in
/-- A nonzero Fourier theta profile cannot have the original character
when that character differs from its inverse. -/
theorem sLocalDecayFourier_character_obstruction (ω : PontryaginDual (K F S))
    (hω : ω ≠ ω⁻¹) (f : E F S) (q : SIdeleQuotient F S)
    (hn : sLocalHomogeneousTheta F S ν ω⁻¹ (sLocalSelectedFourier F S f).val q ≠ 0) :
    ¬ ∀ (k : K F S) (g : SIdeleQuotient F S),
      sLocalHomogeneousTheta F S ν ω⁻¹ (sLocalSelectedFourier F S f).val (k.val * g) =
        (ω k : ℂ)⁻¹ * sLocalHomogeneousTheta F S ν ω⁻¹ (sLocalSelectedFourier F S f).val g := by
  intro h
  apply hω
  apply ContinuousMonoidHom.ext
  intro k
  apply Subtype.ext
  have he := sLocalHomogeneousTheta_translate F S ν ω⁻¹ (sLocalSelectedFourier F S f).val k q
  exact (inv_injective (mul_right_cancel₀ hn (he.symm.trans (h k q)))).symm

end Actual

end

end Masullo
