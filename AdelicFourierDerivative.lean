import AdelicFourierClosure
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.LinearAlgebra.Isomorphisms

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical NumberField RestrictedProduct SchwartzMap

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

private abbrev A := Adeles F
private abbrev V := mixedEmbedding.mixedSpace F
private abbrev K := FiniteAdeleRing (𝓞 F) F

local instance adelicFourierDerivativeMeasurable : MeasurableSpace (A F) := borel _
local instance adelicFourierDerivativeBorel : BorelSpace (A F) := ⟨rfl⟩

local notation "FourierIntegral" => adelicFourierIntegral F (adelicHaarUnitDomain F)
  (standardAdelicCharacter F)

/-- The logarithmic slope of the idele modulus along a one-parameter subgroup. -/
def ideleFlowExponent (γ : Multiplicative ℝ →* Idele F) : ℝ :=
  Real.log (ideleNorm F (γ (Multiplicative.ofAdd 1)))

theorem ideleNorm_flow (γ : Multiplicative ℝ →* Idele F) (hγ : Continuous γ) (t : ℝ) :
    ideleNorm F (γ (Multiplicative.ofAdd t)) = Real.exp (t * ideleFlowExponent F γ) := by
  obtain ⟨α, hα⟩ := idele_oneParameter_logNorm F γ hγ
  have he : ideleFlowExponent F γ = α := by simpa only [ideleFlowExponent, one_mul] using hα 1
  rw [he, ← hα t, Real.exp_log (ideleNorm_pos F _)]

/-- In the positive parameter of the manuscript the modulus is a power. -/
theorem ideleNorm_positive_flow (γ : Multiplicative ℝ →* Idele F) (hγ : Continuous γ)
    {t : ℝ} (ht : 0 < t) :
    ideleNorm F (γ (Multiplicative.ofAdd (Real.log t))) = t ^ ideleFlowExponent F γ := by
  rw [ideleNorm_flow F γ hγ, Real.rpow_def_of_pos ht]

/-- The archimedean velocity at one agrees with the logarithmic velocity
at zero, since the derivative of the logarithm at one is one. -/
theorem mixedIdeleFlow_positive_hasDerivAt (γ : Multiplicative ℝ →* Idele F)
    (hγ : Continuous γ) :
    HasDerivAt (fun t : ℝ => mixedIdeleFlow F γ (Real.log t))
      (deriv (mixedIdeleFlow F γ) 0) 1 := by
  obtain ⟨v, hv⟩ := mixedIdeleFlow_hasDerivAt F γ hγ
  have hv' : HasDerivAt (mixedIdeleFlow F γ) v (Real.log 1) := by simpa only [Real.log_one] using hv
  have hl : HasDerivAt Real.log 1 1 := by simpa using Real.hasDerivAt_log (one_ne_zero (α := ℝ))
  simpa only [Function.comp_def, one_smul, hv.deriv] using hv'.scomp 1 hl

/-- The weighted reciprocal dilation has the Fourier transform of the
directional derivative as its derivative at the identity. -/
theorem adelicFourier_weighted_inverse_hasDerivAt
    (γ : Multiplicative ℝ →* Idele F) (hγ : Continuous γ)
    (f : bruhatSubmodule F) (ξ : A F) :
    HasDerivAt (fun t : ℝ => (ideleNorm F (γ (Multiplicative.ofAdd (Real.log t))))⁻¹ •
      FourierIntegral f.val ((γ (Multiplicative.ofAdd (Real.log t))).inv * ξ))
      (FourierIntegral (algebraicBruhatDeriv F γ hγ f).val ξ) 1 := by
  let g (t : ℝ) := γ (Multiplicative.ofAdd t)
  let D := algebraicBruhatDeriv F γ hγ f
  letI : (adelicHaarUnitDomain F).IsAddHaarMeasure := adelicHaarUnitDomain_isHaar F
  have h : HasDerivAt (fun t : ℝ => FourierIntegral (fun a => f.val ((g t).val * a)) ξ)
      (FourierIntegral D.val ξ) 0 := by
    have hd := adelicFourier_log_hasDerivAt F γ hγ f ξ 0
    have hg : g 0 = 1 := map_one γ
    change HasDerivAt _ (FourierIntegral (fun a => D.val ((g 0).val * a)) ξ) 0 at hd
    simpa only [hg, Units.val_one, one_mul] using hd
  have hc (t : ℝ) := adelicFourier_mul_argument F (adelicHaarUnitDomain F) (standardAdelicCharacter F)
    (standardAdelicCharacter_continuous F) f.val (bruhat_continuous F f.property).measurable (g t) ξ
  simp_rw [hc] at h
  have hl : HasDerivAt Real.log 1 1 := by simpa using Real.hasDerivAt_log (one_ne_zero (α := ℝ))
  have h' : HasDerivAt (fun t : ℝ => (ideleNorm F (g t))⁻¹ • FourierIntegral f.val ((g t).inv * ξ))
      (FourierIntegral D.val ξ) (Real.log 1) := by rw [Real.log_one]; exact h
  simpa only [Function.comp_def, one_smul, g] using h'.scomp 1 hl

/-- Fourier conjugates the adelic directional derivative to the negative
directional derivative plus the scalar from the change of Haar measure. -/
theorem adelicFourier_derivative_identity
    (γ : Multiplicative ℝ →* Idele F) (hγ : Continuous γ) (f : bruhatSubmodule F) :
    let D := algebraicBruhatDeriv F γ hγ
    let fhat : bruhatSubmodule F := ⟨FourierIntegral f.val, adelicFourier_mem_bruhat F f.property⟩
    FourierIntegral (D f).val =
      (-ideleFlowExponent F γ) • fhat.val - (D fhat).val := by
  let D := algebraicBruhatDeriv F γ hγ
  let fhat : bruhatSubmodule F := ⟨FourierIntegral f.val, adelicFourier_mem_bruhat F f.property⟩
  let α := ideleFlowExponent F γ
  let g (t : ℝ) := γ (Multiplicative.ofAdd t)
  funext ξ
  letI : (adelicHaarUnitDomain F).IsAddHaarMeasure := adelicHaarUnitDomain_isHaar F
  have hg₀ : g 0 = 1 := map_one γ
  have hD := adelicFourier_log_hasDerivAt F γ hγ f ξ 0
  change HasDerivAt (fun t : ℝ => FourierIntegral (fun a => f.val ((g t).val * a)) ξ)
    (FourierIntegral (fun a => (D f).val ((g 0).val * a)) ξ) 0 at hD
  simp only [hg₀, Units.val_one, one_mul] at hD
  have he (t : ℝ) : FourierIntegral (fun a => f.val ((g t).val * a)) ξ =
      Real.exp (t * (-α)) • fhat.val ((g (-t)).val * ξ) := by
    have hc := adelicFourier_mul_argument F (adelicHaarUnitDomain F) (standardAdelicCharacter F)
      (standardAdelicCharacter_continuous F) f.val (bruhat_continuous F f.property).measurable
      (g t) ξ
    have hg : g (-t) = (g t)⁻¹ := map_inv γ (Multiplicative.ofAdd t)
    rw [hg]
    change _ = Real.exp (t * (-α)) • FourierIntegral f.val ((g t).inv * ξ)
    simpa only [g, ideleNorm_flow F γ hγ, ← Real.exp_neg, ← mul_neg] using hc
  rw [funext he] at hD
  have hexp : HasDerivAt (fun t : ℝ => Real.exp (t * (-α))) (-α) 0 := by
    have hlin : HasDerivAt (fun t : ℝ => t * (-α)) (-α) 0 := by
      simpa using (hasDerivAt_id (𝕜 := ℝ) 0).mul_const (-α)
    simpa only [Function.comp_def, zero_mul, Real.exp_zero, one_mul] using
      (Real.hasDerivAt_exp (0 * (-α))).comp 0 hlin
  have hneg : HasDerivAt (fun t : ℝ => fhat.val ((g (-t)).val * ξ))
      (-(D fhat).val ξ) 0 := by
    have h := algebraicBruhat_log_orbit_hasDerivAt F γ hγ fhat ξ 0
    change HasDerivAt (fun t : ℝ => fhat.val ((g t).val * ξ))
      ((D fhat).val ((g 0).val * ξ)) 0 at h
    simp only [hg₀, Units.val_one, one_mul] at h
    have hu : HasDerivAt (fun t : ℝ => -t) (-1) 0 := (hasDerivAt_id (𝕜 := ℝ) 0).neg
    have h' : HasDerivAt (fun t : ℝ => fhat.val ((g t).val * ξ)) ((D fhat).val ξ) (-(0 : ℝ)) := by
      simpa only [neg_zero] using h
    simpa only [Function.comp_def, neg_smul, one_smul] using h'.scomp 0 hu
  have h := hD.unique (hexp.smul hneg)
  change FourierIntegral (D f).val ξ = (-α) • fhat.val ξ - (D fhat).val ξ
  rw [sub_eq_add_neg, add_comm]
  simpa only [hg₀, Units.val_one, one_mul, neg_zero, zero_mul, Real.exp_zero, one_smul] using h


private theorem standardCharacter_split (a : A F) :
    ((standardAdelicCharacter F a).toMul : ℂ) =
      (Real.fourierChar (adelicArchTrace F (mixedArch a)) : ℂ) *
        ((standardAdelicCharacter F (finiteAdelicTranslation F a.2)).toMul : ℂ) := by
  have h : archAdele F (mixedArch a) + finiteAdelicTranslation F a.2 = a := by
    apply Prod.ext
    · change (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm
        ((InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1) + 0 = a.1
      rw [RingEquiv.symm_apply_apply, add_zero]
    · exact zero_add _
  have he := (standardAdelicCharacter F).map_add (archAdele F (mixedArch a))
    (finiteAdelicTranslation F a.2)
  rw [h] at he
  have hh := congrArg (fun z : Additive Circle => (z.toMul : ℂ)) he
  change _ = ((standardAdelicCharacter F (archAdele F (mixedArch a))).toMul *
    (standardAdelicCharacter F (finiteAdelicTranslation F a.2)).toMul : Circle).val at hh
  rw [Circle.coe_mul, standardAdelicCharacter_arch, ← Real.fourierChar_apply'] at hh
  exact hh

/-- The explicit integral in the corrected equation (2.2.4.30). The
reciprocal dilation contributes a minus sign to the trace term. -/
theorem adelicFourier_derivative_integral
    (γ : Multiplicative ℝ →* Idele F) (hγ : Continuous γ)
    (f : bruhatSubmodule F) (ξ : A F) :
    FourierIntegral (algebraicBruhatDeriv F γ hγ f).val ξ =
      ∫ a : A F, f.val a * ((standardAdelicCharacter F (a * ξ)).toMul : ℂ) *
        (-(ideleFlowExponent F γ : ℂ) - (2 * Real.pi : ℝ) * Complex.I *
          (adelicArchTrace F (deriv (mixedIdeleFlow F γ) 0 * mixedArch (a * ξ)) : ℂ))
        ∂adelicHaarUnitDomain F := by
  let α := ideleFlowExponent F γ
  let g (t : ℝ) := γ (Multiplicative.ofAdd t)
  let u (t : ℝ) := mixedIdeleFlow F γ (-t)
  let v := deriv (mixedIdeleFlow F γ) 0
  let η (t : ℝ) := v * u t
  let c (a : A F) : ℂ := (standardAdelicCharacter F (finiteAdelicTranslation F (a * ξ).2)).toMul
  let L (t : ℝ) (a : A F) := adelicArchTrace F (η t * mixedArch (a * ξ))
  let P (t : ℝ) (a : A F) := (Real.fourierChar (adelicArchTrace F (u t * mixedArch (a * ξ))) : ℂ)
  let M (t : ℝ) := Real.exp (t * (-α))
  let w (t : ℝ) (a : A F) : ℂ := (M t : ℂ) * (f.val a * P t a * c a)
  let D (t : ℝ) (a : A F) : ℂ := w t a * (-(α : ℂ) -
    (2 * Real.pi : ℝ) * Complex.I * (L t a : ℂ))
  let μ := adelicHaarUnitDomain F
  letI : μ.IsAddHaarMeasure := adelicHaarUnitDomain_isHaar F
  have hbind (t : ℝ) : (∫ a, w t a ∂μ) =
      FourierIntegral (fun a => f.val ((g t).val * a)) ξ := by
    have hg : g (-t) = (g t)⁻¹ := map_inv γ (Multiplicative.ofAdd t)
    have hf : (g (-t)).val.2 = 1 := finite_component_eq_one_of_mem_infinitePlaceIdeles F
      ((idele_oneParameter_structure F γ hγ).1 (Multiplicative.ofAdd (-t)))
    have hc := adelicFourier_mul_argument F μ (standardAdelicCharacter F)
      (standardAdelicCharacter_continuous F) f.val (bruhat_continuous F f.property).measurable (g t) ξ
    rw [hc]
    change (∫ a, w t a ∂μ) =
      (ideleNorm F (g t))⁻¹ • FourierIntegral f.val (((g t)⁻¹).val * ξ)
    rw [← hg, show ideleNorm F (g t) = Real.exp (t * α) from ideleNorm_flow F γ hγ t,
      ← Real.exp_neg, ← mul_neg, Complex.real_smul, adelicFourierIntegral, ← integral_const_mul]
    apply integral_congr_ae
    refine Eventually.of_forall fun a => ?_
    have he : a * ((g (-t)).val * ξ) = (g (-t)).val * (a * ξ) := mul_left_comm _ _ _
    change w t a = (M t : ℂ) * (f.val a *
      ((standardAdelicCharacter F (a * ((g (-t)).val * ξ))).toMul : ℂ))
    rw [he, standardCharacter_split F, map_mul]
    change (M t : ℂ) * (f.val a * P t a * c a) = (M t : ℂ) * (f.val a * (P t a *
      ((standardAdelicCharacter F (finiteAdelicTranslation F ((g (-t)).val.2 * (a * ξ).2))).toMul : ℂ)))
    rw [hf, one_mul]
    simp only [c, mul_assoc]
  have hM (t : ℝ) : HasDerivAt M ((-α) * M t) t := by
    have hl := ((hasDerivAt_id (𝕜 := ℝ) t).mul_const (-α)).exp
    simpa only [M, id_eq, one_mul, mul_one, mul_comm] using hl
  have hu (t : ℝ) : HasDerivAt u (-η t) t := by
    have h := mixedIdeleFlow_log_hasDerivAt F γ hγ (-t)
    have hn : HasDerivAt (fun r : ℝ => -r) (-1) t := (hasDerivAt_id (𝕜 := ℝ) t).neg
    simpa only [u, η, v, Function.comp_def, neg_smul, one_smul] using h.scomp t hn
  have hP (t : ℝ) (a : A F) : HasDerivAt (P · a)
      (P t a * ((2 * Real.pi : ℝ) * Complex.I * (-(L t a) : ℝ))) t := by
    have h := (adelicArchTrace F).hasFDerivAt.comp_hasDerivAt t
      ((hu t).mul_const (mixedArch (a * ξ)))
    have hl : HasDerivAt (fun r : ℝ => adelicArchTrace F (u r * mixedArch (a * ξ)))
        (-(L t a)) t := by simpa only [L, neg_mul, map_neg, Function.comp_def] using h
    have hp := (((hl.const_mul (2 * Real.pi)).ofReal_comp).mul_const Complex.I).cexp
    convert hp using 1
    · funext r
      dsimp only [P]
      rw [Real.fourierChar_apply]
    · dsimp only [P]
      rw [Real.fourierChar_apply]
      push_cast
      ring
  have hderiv (t : ℝ) (a : A F) : HasDerivAt (w · a) (D t a) t := by
    have hd := (hM t).ofReal_comp.mul (((hP t a).const_mul (f.val a)).mul_const (c a))
    have hd' : HasDerivAt (w · a)
        ((((-α) * M t : ℝ) : ℂ) * (f.val a * P t a * c a) +
          (M t : ℂ) * (f.val a *
            (P t a * ((2 * Real.pi : ℝ) * Complex.I * (-(L t a) : ℝ))) * c a)) t := hd
    refine hd'.congr_deriv ?_
    dsimp only [D, w]
    push_cast
    ring
  have hcont : Continuous (fun t : ℝ => (M t, η t)) :=
    (Real.continuous_exp.comp (continuous_id.mul continuous_const)).prodMk
      (continuous_const.mul ((mixedIdeleFlow_continuous F γ hγ).comp continuous_neg))
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).exists_bound_of_continuousOn hcont.continuousOn
  have hB₀ : 0 ≤ B := (norm_nonneg _).trans (hB 0 (by norm_num))
  let C : ℝ := (2 * Real.pi) * (‖adelicArchTrace F‖ * (B * ‖mixedArch ξ‖))
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hbound (t : ℝ) (ht : t ∈ Ioo (-1 : ℝ) 1) (a : A F) :
      ‖D t a‖ ≤ B * (‖α‖ * ‖f.val a‖ + C * (‖mixedArch a‖ * ‖f.val a‖)) := by
    have hR := hB t (Ioo_subset_Icc_self ht)
    have hm : ‖M t‖ ≤ B := (le_max_left _ (‖η t‖)).trans hR
    have hη : ‖η t‖ ≤ B := (le_max_right (‖M t‖) _).trans hR
    have hL : ‖L t a‖ ≤ ‖adelicArchTrace F‖ * (B * (‖mixedArch a‖ * ‖mixedArch ξ‖)) := by
      apply ((adelicArchTrace F).le_opNorm _).trans
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact (norm_mul_le _ _).trans (mul_le_mul hη
        (by rw [map_mul]; exact norm_mul_le _ _) (norm_nonneg _) hB₀)
    have hW : ‖w t a‖ ≤ B * ‖f.val a‖ := by
      simp only [w, norm_mul, Complex.norm_real, P, c, Circle.norm_coe, mul_one]
      exact mul_le_mul_of_nonneg_right hm (norm_nonneg _)
    have hZ : ‖-(α : ℂ) - (2 * Real.pi : ℝ) * Complex.I * (L t a : ℂ)‖ ≤
        ‖α‖ + C * ‖mixedArch a‖ := by
      refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_neg, Complex.norm_real]
      · simp only [norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
          Real.norm_of_nonneg (by positivity : 0 ≤ 2 * Real.pi)]
        apply (mul_le_mul_of_nonneg_left hL (by positivity : 0 ≤ 2 * Real.pi)).trans_eq
        dsimp [C]
        ring
    refine (norm_mul _ _).le.trans ?_
    apply (mul_le_mul hW hZ (norm_nonneg _) (mul_nonneg hB₀ (norm_nonneg _))).trans_eq
    ring
  have hf : Integrable f.val μ := by
    have h := bruhat_dilate_integrable F f.property (1 : Idele F)
    change Integrable (fun a : A F => f.val (1 * a)) μ at h
    simpa only [one_mul] using h
  have hint : Integrable (fun a : A F =>
      B * (‖α‖ * ‖f.val a‖ + C * (‖mixedArch a‖ * ‖f.val a‖))) μ :=
    ((hf.norm.const_mul _).add ((bruhat_mixedArch_norm_integrable F f.property).const_mul _)).const_mul _
  have hW (t : ℝ) : Continuous (w t) := by
    have hA : Continuous (mixedArch (F := F)) :=
      (infiniteAdele_toMixed_continuous F).comp continuous_fst
    have hχ : Continuous fun a : A F => ((standardAdelicCharacter F a).toMul : ℂ) :=
      continuous_subtype_val.comp (continuous_toMul.comp (standardAdelicCharacter_continuous F))
    have hP' : Continuous (P t) := continuous_subtype_val.comp
      (Real.continuous_fourierChar.comp ((adelicArchTrace F).continuous.comp
        (continuous_const.mul (hA.comp (continuous_id.mul continuous_const)))))
    have hc : Continuous c := hχ.comp ((continuous_const.prodMk continuous_id).comp
      (continuous_snd.comp (continuous_id.mul continuous_const)))
    exact continuous_const.mul (((bruhat_continuous F f.property).mul hP').mul hc)
  have hDi : AEStronglyMeasurable (D 0) μ := by
    have hA : Continuous (mixedArch (F := F)) :=
      (infiniteAdele_toMixed_continuous F).comp continuous_fst
    have hL : Continuous (L 0) := (adelicArchTrace F).continuous.comp
      (continuous_const.mul (hA.comp (continuous_id.mul continuous_const)))
    exact ((hW 0).mul (continuous_const.sub
      (continuous_const.mul (Complex.continuous_ofReal.comp hL)))).aestronglyMeasurable
  have hWi : Integrable (w 0) μ := hf.mono (hW 0).aestronglyMeasurable
    (.of_forall fun a => by simp [w, M, P, c, Circle.norm_coe])
  have hN : Ioo (-1 : ℝ) 1 ∈ 𝓝 (0 : ℝ) := Ioo_mem_nhds (by norm_num) (by norm_num)
  have hi := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := w) (F' := D) hN
    (.of_forall fun t => (hW t).aestronglyMeasurable) hWi hDi
    (.of_forall fun a t ht => hbound t ht a) hint (.of_forall fun a t _ => hderiv t a)).2
  have hd := adelicFourier_log_hasDerivAt F γ hγ f ξ 0
  have hg₀ : g 0 = 1 := map_one γ
  change HasDerivAt (fun t : ℝ => FourierIntegral (fun a => f.val ((g t).val * a)) ξ)
    (FourierIntegral (fun a => (algebraicBruhatDeriv F γ hγ f).val ((g 0).val * a)) ξ) 0 at hd
  simp only [hg₀, Units.val_one, one_mul] at hd
  simp_rw [hbind] at hi
  rw [hd.unique hi]
  apply integral_congr_ae
  refine .of_forall fun a => ?_
  have hu₀ : u 0 = 1 := by dsimp only [u]; rw [neg_zero, mixedIdeleFlow_zero]
  simp only [D, w, M, P, c, η, L, α, hu₀, zero_mul, Real.exp_zero, Complex.ofReal_one,
    one_mul, mul_one]
  rw [standardCharacter_split F (a * ξ)]
  ring

/-- Evaluation at zero before and after Fourier transformation. -/
def GlobalBruhat.polarEvaluation : GlobalBruhat F →L[ℂ] ℂ × ℂ :=
  let e : GlobalBruhat F →L[ℂ] ℂ :=
    ⟨GlobalBruhat.evaluation F 0, GlobalBruhat.evaluation_continuous F 0⟩
  e.prod (e.comp (GlobalBruhat.fourier F))

/-- The common polar kernel, the closed subspace of tests with both zero
terms vanishing. -/
def GlobalBruhat.polarKernel : Submodule ℂ (GlobalBruhat F) :=
  (GlobalBruhat.polarEvaluation F).toLinearMap.ker

theorem GlobalBruhat.polarKernel_isClosed :
    IsClosed (GlobalBruhat.polarKernel F : Set (GlobalBruhat F)) := by
  change IsClosed {f : GlobalBruhat F | GlobalBruhat.polarEvaluation F f = 0}
  exact isClosed_eq (GlobalBruhat.polarEvaluation F).continuous continuous_const

private theorem exists_globalBruhat_bump {c : V F} (b : ContDiffBump c) :
    ∃ f : GlobalBruhat F,
      let u := (GlobalBruhat.algebraicEquiv F f).val
      u (archAdele F c) = 1 ∧ u 0 = (b (0 : V F) : ℂ) ∧
        0 < (FourierIntegral u 0).re := by
  let W := (finiteIntegralAdeles F : Set (K F))
  have hW : IsCompact W := isCompact_finiteIntegralAdeles F
  have hOpen : IsOpen W := by
    change IsOpen {x : K F | x ∈ finiteIntegralAdeles F}
    simp only [mem_finiteIntegralAdeles_iff]
    exact RestrictedProduct.isOpen_forall_mem
      (fun v => Valued.isOpen_valuationSubring (v.adicCompletion F))
  haveI : T2Space (K F) :=
    inferInstanceAs (T2Space (Πʳ v : HeightOneSpectrum (𝓞 F),
      [v.adicCompletion F, v.adicCompletionIntegers F]))
  let ψ : LocallyConstant (K F) ℂ :=
    (LocallyConstant.const _ 1).indicator (U := W) ⟨hW.isClosed, hOpen⟩
  have hψ (x : K F) : ψ x = if x ∈ W then 1 else 0 :=
    LocallyConstant.indicator_apply_eq_if _ _ _
  have hψc : HasCompactSupport ψ := by
    apply hW.of_isClosed_subset isClosed_closure
    apply closure_minimal _ hW.isClosed
    intro x hx
    by_contra hn
    exact hx (by simp [hψ, hn])
  let φ₀ : V F → ℂ := fun x => (b x : ℂ)
  have hφc : HasCompactSupport φ₀ := by
    exact b.hasCompactSupport.comp_left Complex.ofReal_zero
  let φ := hφc.toSchwartzMap (Complex.ofRealCLM.contDiff.comp b.contDiff)
  let f := GlobalBruhat.pure F ⟨ψ, hψc⟩ φ
  let u := (GlobalBruhat.algebraicEquiv F f)
  have hψ₀ : ψ 0 = 1 := by rw [hψ]; exact ite_eq_left (finiteIntegralAdeles F).zero_mem
  have hu (x : A F) : u.val x = (b (mixedArch x) : ℂ) * ψ x.2 := rfl
  have hu₁ : u.val (archAdele F c) = 1 := by
    rw [hu]
    have hc : mixedArch (archAdele F c) = c :=
      (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply c
    change (b (mixedArch (archAdele F c)) : ℂ) * ψ 0 = 1
    rw [hc, hψ₀, mul_one, b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le)]
    exact Complex.ofReal_one
  have hu₂ : u.val 0 = (b (0 : V F) : ℂ) := by
    rw [hu, map_zero]
    change _ * ψ 0 = _
    rw [hψ₀, mul_one]
  letI : (adelicHaarUnitDomain F).IsAddHaarMeasure := adelicHaarUnitDomain_isHaar F
  have hInt : Integrable u.val (adelicHaarUnitDomain F) := by
    have h := bruhat_dilate_integrable F u.property 1
    change Integrable (fun x : A F => u.val (1 * x)) (adelicHaarUnitDomain F) at h
    simpa only [one_mul] using h
  have hp : 0 < ∫ x : A F, (u.val x).re ∂adelicHaarUnitDomain F := by
    apply integral_pos_of_integrable_nonneg_nonzero (x := archAdele F c)
      (Complex.continuous_re.comp (bruhat_continuous F u.property)) hInt.re
    · intro x
      change 0 ≤ (u.val x).re
      rw [hu, hψ]
      split_ifs <;> simp [b.nonneg]
    · change (u.val (archAdele F c)).re ≠ 0
      rw [hu₁, Complex.one_re]
      exact one_ne_zero
  have hF : FourierIntegral u.val 0 = ∫ x : A F, u.val x ∂adelicHaarUnitDomain F := by
    simp [adelicFourierIntegral, mul_zero, map_zero]
  refine ⟨f, hu₁, hu₂, ?_⟩
  rw [hF]
  have he := integral_re hInt
  change (∫ x : A F, (u.val x).re ∂adelicHaarUnitDomain F) =
    (∫ x : A F, u.val x ∂adelicHaarUnitDomain F).re at he
  exact he ▸ hp

/-- The two polar evaluations are independent. -/
theorem GlobalBruhat.polarEvaluation_surjective : Surjective (GlobalBruhat.polarEvaluation F) := by
  let b₁ : ContDiffBump (0 : V F) := ⟨1, 2, by norm_num, by norm_num⟩
  obtain ⟨u, -, hu, -⟩ := exists_globalBruhat_bump F b₁
  have hu' : (GlobalBruhat.polarEvaluation F u).1 = 1 := by
    change (GlobalBruhat.algebraicEquiv F u).val 0 = 1
    rw [hu, b₁.one_of_mem_closedBall (Metric.mem_closedBall_self b₁.rIn_pos.le)]
    exact Complex.ofReal_one
  let c := mixedEmbedding F (1 : F)
  have hc : 0 ≠ c := fun h => zero_ne_one ((mixedEmbedding_injective F)
    ((mixedEmbedding F).map_zero.trans h))
  have hd : 0 < dist (0 : V F) c := dist_pos.mpr hc
  let b₂ : ContDiffBump c := ⟨dist 0 c / 4, dist 0 c / 2, by linarith, by linarith⟩
  obtain ⟨v, -, hv, hvF⟩ := exists_globalBruhat_bump F b₂
  have hv₀ : (GlobalBruhat.polarEvaluation F v).1 = 0 := by
    change (GlobalBruhat.algebraicEquiv F v).val 0 = 0
    rw [hv, b₂.zero_of_le_dist (show dist 0 c / 2 ≤ dist 0 c by linarith)]
    exact Complex.ofReal_zero
  have hv₁ : (GlobalBruhat.polarEvaluation F v).2 ≠ 0 := by
    change FourierIntegral (GlobalBruhat.algebraicEquiv F v).val 0 ≠ 0
    intro h
    rw [h, Complex.zero_re] at hvF
    exact (lt_irrefl 0) hvF
  let T := GlobalBruhat.polarEvaluation F
  intro z
  refine ⟨z.1 • u + ((z.2 - z.1 * (T u).2) / (T v).2) • v, ?_⟩
  rw [map_add, map_smul, map_smul]
  apply Prod.ext
  · change z.1 * (T u).1 + ((z.2 - z.1 * (T u).2) / (T v).2) * (T v).1 = z.1
    rw [show (T u).1 = 1 from hu', show (T v).1 = 0 from hv₀, mul_zero, add_zero, mul_one]
  · change z.1 * (T u).2 + ((z.2 - z.1 * (T u).2) / (T v).2) * (T v).2 = z.2
    rw [div_mul_cancel₀ _ hv₁]
    ring

/-- The two evaluations identify the polar quotient with `ℂ × ℂ`. -/
def GlobalBruhat.polarQuotientEquiv :
    (GlobalBruhat F ⧸ GlobalBruhat.polarKernel F) ≃ₗ[ℂ] ℂ × ℂ :=
  (GlobalBruhat.polarEvaluation F).toLinearMap.quotKerEquivOfSurjective
    (GlobalBruhat.polarEvaluation_surjective F)

/-- The derivative acts on the pair of polar evaluations by
`diag(0, −α)`. This also proves invariance of the common kernel. -/
theorem GlobalBruhat.polarEvaluation_derivative
    (γ : Multiplicative ℝ →* Idele F) (hγ : Continuous γ) (f : GlobalBruhat F) :
    GlobalBruhat.polarEvaluation F (GlobalBruhat.derivative F γ hγ f) =
      (0, (-ideleFlowExponent F γ) • (GlobalBruhat.polarEvaluation F f).2) := by
  let u := GlobalBruhat.algebraicEquiv F f
  have hD : GlobalBruhat.algebraicEquiv F (GlobalBruhat.derivative F γ hγ f) =
      algebraicBruhatDeriv F γ hγ u := (GlobalBruhat.algebraicEquiv F).apply_symm_apply _
  apply Prod.ext
  · change (GlobalBruhat.algebraicEquiv F (GlobalBruhat.derivative F γ hγ f)).val 0 = 0
    rw [hD]
    exact (algebraicBruhatDeriv_zero_terms F γ hγ _ (ideleNorm_flow F γ hγ) u).1
  · change (GlobalBruhat.algebraicEquiv F (GlobalBruhat.fourier F
      (GlobalBruhat.derivative F γ hγ f))).val 0 =
        (-ideleFlowExponent F γ) • (GlobalBruhat.algebraicEquiv F (GlobalBruhat.fourier F f)).val 0
    rw [GlobalBruhat.fourier_apply, GlobalBruhat.fourier_apply, hD]
    exact (algebraicBruhatDeriv_zero_terms F γ hγ _ (ideleNorm_flow F γ hγ) u).2

theorem GlobalBruhat.derivative_preserves_polarKernel
    (γ : Multiplicative ℝ →* Idele F) (hγ : Continuous γ) {f : GlobalBruhat F}
    (hf : f ∈ GlobalBruhat.polarKernel F) :
    GlobalBruhat.derivative F γ hγ f ∈ GlobalBruhat.polarKernel F := by
  change GlobalBruhat.polarEvaluation F f = 0 at hf
  change GlobalBruhat.polarEvaluation F (GlobalBruhat.derivative F γ hγ f) = 0
  rw [GlobalBruhat.polarEvaluation_derivative F γ hγ f, hf]
  simp

/-- The induced endomorphism on the quotient by the common polar kernel. -/
def GlobalBruhat.polarQuotientDerivative
    (γ : Multiplicative ℝ →* Idele F) (hγ : Continuous γ) :
    (GlobalBruhat F ⧸ GlobalBruhat.polarKernel F) →ₗ[ℂ]
      (GlobalBruhat F ⧸ GlobalBruhat.polarKernel F) :=
  (GlobalBruhat.polarKernel F).mapQ (GlobalBruhat.polarKernel F)
    (GlobalBruhat.derivative F γ hγ).toLinearMap
    (fun _ hf => GlobalBruhat.derivative_preserves_polarKernel F γ hγ hf)

/-- The quotient matrix in the evaluation coordinates is `diag(0, −α)`. -/
theorem GlobalBruhat.polarQuotientDerivative_matrix
    (γ : Multiplicative ℝ →* Idele F) (hγ : Continuous γ)
    (z : GlobalBruhat F ⧸ GlobalBruhat.polarKernel F) :
    GlobalBruhat.polarQuotientEquiv F (GlobalBruhat.polarQuotientDerivative F γ hγ z) =
      (0, (-ideleFlowExponent F γ) • (GlobalBruhat.polarQuotientEquiv F z).2) := by
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  change GlobalBruhat.polarEvaluation F (GlobalBruhat.derivative F γ hγ f) = _
  exact GlobalBruhat.polarEvaluation_derivative F γ hγ f

end

end Masullo
