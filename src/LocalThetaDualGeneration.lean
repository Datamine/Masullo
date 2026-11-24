import SLocalThetaDualGeneration
import ArchimedeanProductZeta
import HardySobolevPaleyConverse
import CompactGroupAveraging
import CompactCharacterCompleteness
import Mathlib.Analysis.Complex.Isometry
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

open Filter Function MeasureTheory Set
open scoped SchwartzMap Topology

namespace Masullo

noncomputable section

set_option maxHeartbeats 800000

private abbrev mellinLine (y : ℝ) : ℂ := 1 + (y : ℂ) * Complex.I

private theorem mellinLine_re (y : ℝ) : (mellinLine y).re = 1 := by simp [Complex.mul_re]

/-- The Mellin values on the line of real part one separate the positive restrictions
of Schwartz functions on the real line. -/
theorem realSchwartz_mellinLine_zero_iff (f : 𝓢(ℝ, ℂ)) :
    (∀ y : ℝ, mellin (f : ℝ → ℂ) (mellinLine y) = 0) ↔ ∀ t > 0, f t = 0 := by
  have hpos : Real.exp '' (univ : Set ℝ) = Ioi 0 := by
    rw [image_univ, Real.range_exp]
  have hderiv (x : ℝ) (hx : x ∈ (univ : Set ℝ)) :
      HasDerivWithinAt Real.exp (Real.exp x) univ x := (Real.hasDerivAt_exp x).hasDerivWithinAt
  have hinj : InjOn Real.exp (univ : Set ℝ) := Real.exp_injective.injOn
  let g (x : ℝ) : ℂ := (Real.exp x : ℂ) * f (Real.exp x)
  have hg : Integrable g := by
    have h := (integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ
      hderiv hinj (f : ℝ → ℂ)).mp (by rw [hpos]; exact f.integrable.integrableOn)
    simpa only [abs_of_pos (Real.exp_pos _), integrableOn_univ, Complex.real_smul] using h
  constructor
  · intro h
    have hzero : g =ᵐ[volume] 0 := by
      apply integrable_logFourier_ae_zero hg
      intro y
      have hh := h y
      unfold mellin at hh
      rw [← hpos, integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ hderiv hinj,
        setIntegral_univ] at hh
      refine (integral_congr_ae (.of_forall fun x ↦ ?_)).trans hh
      change Complex.exp ((y : ℂ) * Complex.I * (x : ℂ)) * g x =
        |Real.exp x| • ((Real.exp x : ℂ) ^ (mellinLine y - 1) • f (Real.exp x))
      rw [abs_of_pos (Real.exp_pos x), Complex.real_smul, smul_eq_mul]
      rw [show mellinLine y - 1 = (y : ℂ) * Complex.I by ring,
        Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_ne_zero x))]
      rw [← Complex.ofReal_log (Real.exp_pos x).le, Real.log_exp, mul_comm (x : ℂ)]
      dsimp only [g]
      ring
    have hgcont : Continuous g :=
      (Complex.continuous_ofReal.comp Real.continuous_exp).mul (f.continuous.comp Real.continuous_exp)
    have he := Measure.eq_of_ae_eq hzero hgcont continuous_const
    intro t ht
    have H := congrFun he (Real.log t)
    change (Real.exp (Real.log t) : ℂ) * f (Real.exp (Real.log t)) = 0 at H
    rw [Real.exp_log ht] at H
    exact (mul_eq_zero.mp H).resolve_left (Complex.ofReal_ne_zero.mpr ht.ne')
  · intro h y
    unfold mellin
    refine (setIntegral_congr_fun measurableSet_Ioi (g := fun _ : ℝ ↦ (0 : ℂ)) ?_).trans (by simp)
    intro t ht
    change (t : ℂ) ^ (mellinLine y - 1) • f t = 0
    rw [h t ht, smul_zero]

private abbrev R := 𝓢(ℝ, ℂ)

/-- Mellin evaluation on the line of real part one, in the given real parity. -/
def realLocalLineEval (a : ℕ) (y : ℝ) : StrongDual ℂ R :=
  realArchimedeanZetaContinuedCLM a (mellinLine y)

private theorem realLocalLineEval_kernel (a : ℕ) (f : R) :
    (∀ y, realLocalLineEval a y f = 0) ↔ ∀ t > 0, f t + (-1 : ℂ) ^ a * f (-t) = 0 := by
  have he : (∀ y, realLocalLineEval a y f = 0) ↔
      ∀ y, mellin (realZetaProfile a f : ℝ → ℂ) (mellinLine y) = 0 :=
    forall_congr' fun y ↦ by
      rw [realLocalLineEval, realArchimedeanZetaContinuedCLM_apply, realArchimedeanZetaContinued]
      exact Iff.of_eq (congrArg (· = 0) (mellinTaylorContinued_eq_mellin
        (realZetaProfile a f).smooth' (schwartz_radial_rapid _) (s := mellinLine y)
        (by rw [mellinLine_re]; norm_num)).2.symm)
  simpa only [realZetaProfile_apply] using
    he.trans (realSchwartz_mellinLine_zero_iff (realZetaProfile a f))

/-- The action of the negative unit on real Schwartz tests. -/
def realLocalReflection : R →L[ℂ] R :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (LinearIsometryEquiv.neg ℝ).toContinuousLinearEquiv

private theorem realLocalReflection_apply (f : R) (x : ℝ) :
    realLocalReflection f x = f (-x) := rfl

private theorem realLocalLineEval_kernel' (a : ℕ) (f : R) :
    (∀ y, realLocalLineEval a y f = 0) ↔ f + ((-1 : ℂ) ^ a) • realLocalReflection f = 0 := by
  rw [realLocalLineEval_kernel]
  constructor
  · intro h
    have hneg : ((-1 : ℂ) ^ a) * ((-1 : ℂ) ^ a) = 1 := by
      rw [← mul_pow]; simp
    have hall (t : ℝ) : f t + (-1 : ℂ) ^ a * f (-t) = 0 := by
      rcases lt_trichotomy t 0 with ht | rfl | ht
      · have H := congrArg (((-1 : ℂ) ^ a) * ·) (h (-t) (neg_pos.mpr ht))
        simp only [neg_neg, mul_add, ← mul_assoc, hneg, one_mul, mul_zero] at H
        simpa only [add_comm] using H
      · have H : f 0 + (-1 : ℂ) ^ a * f (-0) = 0 := by
          have he : Continuous (fun t : ℝ ↦ f t + (-1 : ℂ) ^ a * f (-t)) :=
            f.continuous.add (continuous_const.mul (f.continuous.comp continuous_neg))
          exact (isClosed_eq he continuous_const).closure_subset_iff.mpr
            (show Ioi 0 ⊆ {t : ℝ | f t + (-1 : ℂ) ^ a * f (-t) = 0} from fun t ht ↦ h t ht)
            (show (0 : ℝ) ∈ closure (Ioi (0 : ℝ)) from by simp [closure_Ioi])
        exact H
      · exact h t ht
    ext t
    exact hall t
  · intro h t ht
    exact congrArg (fun k : R ↦ k t) h

/-- A fixed real-place parity is generated in the strong dual by one Mellin line. -/
theorem realLocalMellin_homogeneous_strongSpan (a : ℕ) (d : ℝ → ℂ) (hd : ∀ y, d y ≠ 0) :
    closure (Submodule.span ℂ (range fun y ↦ d y • realLocalLineEval a y) :
      Set (StrongDual ℂ R)) =
      {T : StrongDual ℂ R | ∀ f, T (realLocalReflection f) = (-1 : ℂ) ^ a * T f} := by
  let e₀ : R →L[ℂ] R := ContinuousLinearMap.id ℂ R + ((-1 : ℂ) ^ a) • realLocalReflection
  let l (y : ℝ) := d y • realLocalLineEval a y
  obtain ⟨e, he⟩ := classicalSchwartz_reflexive ℝ
  rw [show (fun y ↦ d y • realLocalLineEval a y) = l from rfl,
    strongDual_closure_span_eq_annihilator e he l e₀.ker]
  · have hs : ((-1 : ℂ) ^ a) * ((-1 : ℂ) ^ a) = 1 := by rw [← mul_pow]; simp
    ext T
    change (∀ f ∈ e₀.ker, T f = 0) ↔ ∀ f, T (realLocalReflection f) = (-1 : ℂ) ^ a * T f
    constructor
    · intro h f
      have hk : realLocalReflection f - ((-1 : ℂ) ^ a) • f ∈ e₀.ker := by
        change e₀ _ = 0
        ext x
        simp only [e₀, add_apply, ContinuousLinearMap.id_apply, smul_apply, smul_eq_mul,
          realLocalReflection_apply, sub_apply, neg_neg, zero_apply]
        rw [mul_sub, ← mul_assoc, hs, one_mul]
        ring
      have hT := h _ hk
      rwa [map_sub, map_smul, smul_eq_mul, sub_eq_zero] at hT
    · intro h f hf
      have h₀ : f + ((-1 : ℂ) ^ a) • realLocalReflection f = 0 := hf
      have H := congrArg T h₀
      rw [map_add, map_smul, smul_eq_mul, h, ← mul_assoc, hs, one_mul, map_zero,
        ← two_mul] at H
      exact (mul_eq_zero.mp H).resolve_left (by norm_num)
  · intro f
    change f + ((-1 : ℂ) ^ a) • realLocalReflection f = 0 ↔
      ∀ y, d y * realLocalLineEval a y f = 0
    rw [← realLocalLineEval_kernel']
    exact forall_congr' fun y ↦ ⟨fun h ↦ by rw [h, mul_zero],
      fun h ↦ (mul_eq_zero.mp h).resolve_left (hd y)⟩

/-- The even and odd real-place Mellin lines together generate the full strong dual. -/
theorem realLocalMellin_strongSpan (d : Fin 2 × ℝ → ℂ) (hd : ∀ i, d i ≠ 0) :
    closure (Submodule.span ℂ (range fun i : Fin 2 × ℝ ↦
      d i • realLocalLineEval i.1.val i.2) : Set (StrongDual ℂ R)) = univ := by
  let l (i : Fin 2 × ℝ) := d i • realLocalLineEval i.1.val i.2
  obtain ⟨e, he⟩ := classicalSchwartz_reflexive ℝ
  change closure (Submodule.span ℂ (range l) : Set (StrongDual ℂ R)) = univ
  rw [strongDual_closure_span_eq_annihilator e he l ⊥]
  · ext T
    simp
  · intro f
    simp only [Submodule.mem_bot]
    refine ⟨fun h i ↦ by simp [h, l], fun h ↦ ?_⟩
    have h₀ := (realLocalLineEval_kernel' 0 f).mp fun y ↦
      (mul_eq_zero.mp (h (0, y))).resolve_left (hd (0, y))
    have h₁ := (realLocalLineEval_kernel' 1 f).mp fun y ↦
      (mul_eq_zero.mp (h (1, y))).resolve_left (hd (1, y))
    ext t
    have ha : f t + f (-t) = 0 := by
      simpa [realLocalReflection_apply] using congrArg (fun g : R ↦ g t) h₀
    have hb : f t + (-1 : ℂ) * f (-t) = 0 := by
      simpa only [add_apply, smul_apply, smul_eq_mul, pow_one,
        realLocalReflection_apply, zero_apply] using congrArg (fun g : R ↦ g t) h₁
    have h₂ : 2 * f t = 0 := by linear_combination ha + hb
    exact (mul_eq_zero.mp h₂).resolve_left (by norm_num)

section ComplexPlace

private abbrev C := 𝓢(ℂ, ℂ)

attribute [local instance] complexZeta_circleMeasurable complexZeta_circleBorel

variable (ν : Measure Circle) [ν.IsHaarMeasure] [IsFiniteMeasure ν]

/-- Complex angular dilations, using pullback by multiplication by the circle element. -/
def complexLocalRotation : Circle →* (C →L[ℂ] C) where
  toFun u :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (rotation u).toContinuousLinearEquiv
  map_one' := by
    ext f x
    change f ((1 : Circle) * (x : ℂ)) = f x
    simp
  map_mul' u v := by
    ext f x
    change f (((u * v : Circle) : ℂ) * x) = f ((v : ℂ) * ((u : ℂ) * x))
    rw [Circle.coe_mul]
    ring_nf

@[simp] theorem complexLocalRotation_apply (u : Circle) (f : C) (x : ℂ) :
    complexLocalRotation u f x = f ((u : ℂ) * x) := rfl

private theorem complexLocalRotation_continuous :
    Continuous (fun z : Circle × C ↦ complexLocalRotation z.1 z.2) := by
  letI : PolynormableSpace ℂ C := (classicalSchwartz_nuclear.{0, 0} ℂ).2.1
  letI : BarrelledSpace ℂ C := isFrechetTVS_barrelled (classicalSchwartz_isFrechet ℂ)
  apply continuous_joint_of_barrelled
  intro f
  let A (u : Circle) := (rotation u).toContinuousLinearEquiv
  have h (u : Circle) : (A u).toContinuousLinearMap =
      ((ContinuousLinearMap.mul ℂ ℂ) u.val).restrictScalars ℝ := by
    ext x
    rfl
  have hA : Continuous (fun u ↦ (A u).toContinuousLinearMap) := by
    simp only [h]
    exact (ContinuousLinearMap.continuous_restrictScalars ℝ).comp
      ((ContinuousLinearMap.mul ℂ ℂ).continuous.comp continuous_subtype_val)
  have hA' : Continuous (fun u ↦ (A u).symm.toContinuousLinearMap) := by
    apply (hA.comp continuous_inv).congr
    intro u
    exact congrArg (fun e : ℂ ≃ₗᵢ[ℝ] ℂ ↦ e.toContinuousLinearEquiv.toContinuousLinearMap)
      (rotation_symm u).symm
  exact continuous_schwartz_linearPullback A hA hA' f

/-- Mellin evaluation on the line of real part one half, in the given angular component. -/
def complexLineEval (ν : Measure Circle) [IsFiniteMeasure ν] (m : ℤ) (y : ℝ) :
    StrongDual ℂ C :=
  complexArchimedeanZetaContinuedCLM ν m (mellinLine y / 2)

omit [ν.IsHaarMeasure] in
private theorem complexLineEval_kernel (m : ℤ) (f : C) :
    (∀ y, complexLineEval ν m y f = 0) ↔ ∀ t > 0, complexZetaProfile ν m f t = 0 := by
  have h (y : ℝ) : complexLineEval ν m y f =
      mellin (complexZetaProfile ν m f) (mellinLine y) := by
    rw [complexLineEval, complexArchimedeanZetaContinuedCLM_apply]
    have he := (complexArchimedeanZetaContinued_eq_radial ν m f
      (s := mellinLine y / 2) (by simp [Complex.div_ofNat_re])).2
    rw [show 2 * (mellinLine y / 2) = mellinLine y by ring] at he
    exact he.symm
  simp only [h]
  exact realSchwartz_mellinLine_zero_iff (complexZetaRadialSchwartz ν m f)

private theorem complexMellin_annihilator (m : ℤ) :
    ∃ P : C →L[ℂ] C,
      (∀ f, P f = 0 ↔ ∀ y, complexLineEval ν m y f = 0) ∧
      {T : StrongDual ℂ C | ∀ f ∈ P.ker, T f = 0} =
        {T : StrongDual ℂ C | ∀ (u : Circle) f, T (complexLocalRotation u f) = (u : ℂ) ^ (-m) * T f} := by
  letI : CompleteSpace C := completeSpace_schwartzMap
  letI : PolynormableSpace ℂ C := (classicalSchwartz_nuclear.{0, 0} ℂ).2.1
  let ω : Circle →* Circle := zpowGroupHom (-m)
  have hω : Continuous ω := continuous_id.zpow _
  obtain ⟨hFixed, P, hP, hRange, _, _, _, hker⟩ :=
    compactGroupIsotypicAverage complexLocalRotation complexLocalRotation_continuous ω hω ν
  have hPval (f : C) (x : ℂ) : P f x = ∫ u : Circle, (u : ℂ) ^ m * f ((u : ℂ) * x) ∂ν := by
    let L : StrongDual ℂ C := (BoundedContinuousFunction.evalCLM ℂ x).comp
      (SchwartzMap.toBoundedContinuousFunctionCLM ℂ ℂ ℂ)
    refine ((hP f L).2).trans ?_
    apply integral_congr_ae
    refine .of_forall fun u ↦ ?_
    change (((ω u)⁻¹ : Circle) : ℂ) * f ((u : ℂ) * x) = _
    simp [ω, zpowGroupHom, zpow_neg]
  refine ⟨P, fun f ↦ ?_, ?_⟩
  · rw [complexLineEval_kernel]
    have hrad (t : ℝ) : P f (t : ℂ) = complexZetaProfile ν m f t := by
      rw [hPval, complexZetaProfile]
      apply integral_congr_ae
      refine .of_forall fun u ↦ ?_
      change (u : ℂ) ^ m * f ((u : ℂ) * (t : ℂ)) =
        (u : ℂ) ^ m * f (t • (u : ℂ))
      rw [Complex.real_smul, mul_comm (u : ℂ)]
    constructor
    · intro h t ht
      rw [← hrad, h, zero_apply]
    · intro h
      have h₀ : P f 0 = 0 := by
        let Q : ℝ → ℂ := fun t ↦ P f (t : ℂ)
        have hclosed : IsClosed {t | Q t = 0} :=
          isClosed_eq ((P f).continuous.comp Complex.continuous_ofReal) continuous_const
        exact hclosed.closure_subset_iff.mpr
          (show Ioi (0 : ℝ) ⊆ {t | Q t = 0} from fun t ht ↦ (hrad t).trans (h t ht))
          (show (0 : ℝ) ∈ closure (Ioi (0 : ℝ)) from by simp [closure_Ioi])
      ext x
      by_cases hx : x = 0
      · simpa [hx] using h₀
      let t := ‖x‖
      have ht : 0 < t := norm_pos_iff.mpr hx
      let v : Circle := ⟨(t : ℂ)⁻¹ * x, by
        change dist ((t : ℂ)⁻¹ * x) 0 = 1
        rw [dist_zero_right]
        rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg ht.le, inv_mul_cancel₀ ht.ne']⟩
      have hv : (v : ℂ) * (t : ℂ) = x := by
        change (t : ℂ)⁻¹ * x * (t : ℂ) = x
        rw [mul_right_comm, inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr ht.ne'), one_mul]
      have hPf : P f ∈ fixedSubmodule (twistedCircleAction ω complexLocalRotation) := by
        have hmem := mem_range_self (f := P) f
        rwa [hRange] at hmem
      have hval : P f x = (ω v : ℂ) * P f (t : ℂ) := by
        have he := congrArg (fun f : C ↦ f (t : ℂ)) ((hFixed (P f)).mp hPf v)
        simpa only [complexLocalRotation_apply, hv, smul_apply, smul_eq_mul] using he
      rw [hval, hrad, h _ ht, mul_zero, zero_apply]
  · ext T
    change (∀ f ∈ P.ker, T f = 0) ↔
      ∀ (u : Circle) f, T (complexLocalRotation u f) = (u : ℂ) ^ (-m) * T f
    rw [hker]
    change (actionDifferenceSpan (twistedCircleAction ω complexLocalRotation)).topologicalClosure ≤ T.ker ↔ _
    let S := actionDifferenceSpan (twistedCircleAction ω complexLocalRotation)
    rw [show S.topologicalClosure ≤ T.ker ↔ S ≤ T.ker from
      ⟨S.le_topologicalClosure.trans, fun h ↦ S.topologicalClosure_minimal h T.isClosed_ker⟩]
    change Submodule.span ℂ _ ≤ T.ker ↔ _
    rw [Submodule.span_le]
    constructor
    · intro h u f
      have hh := h (mem_range_self (u, f))
      change T (f - (((ω u)⁻¹ : Circle) : ℂ) • complexLocalRotation u f) = 0 at hh
      rw [map_sub, map_smul, smul_eq_mul, sub_eq_zero, Circle.coe_inv] at hh
      have hu : (ω u : ℂ) ≠ 0 := (ω u).coe_ne_zero
      have he := congrArg ((ω u : ℂ) * ·) hh
      change (ω u : ℂ) * T f =
        (ω u : ℂ) * ((ω u : ℂ)⁻¹ * T (complexLocalRotation u f)) at he
      rw [← mul_assoc, mul_inv_cancel₀ hu, one_mul] at he
      simpa [ω, zpowGroupHom, Circle.coe_zpow] using he.symm
    · intro h _ hf
      obtain ⟨⟨u, f⟩, rfl⟩ := hf
      change T (f - (((ω u)⁻¹ : Circle) : ℂ) • complexLocalRotation u f) = 0
      rw [map_sub, map_smul, smul_eq_mul, h, Circle.coe_inv]
      change T f - (↑(u ^ (-m) : Circle) : ℂ)⁻¹ * ((u : ℂ) ^ (-m) * T f) = 0
      rw [Circle.coe_zpow, ← mul_assoc, inv_mul_cancel₀ (zpow_ne_zero _ u.coe_ne_zero),
        one_mul, sub_self]

/-- A fixed complex angular weight is generated by a single Mellin line. -/
theorem complexLocalMellin_homogeneous_strongSpan (m : ℤ) (d : ℝ → ℂ) (hd : ∀ y, d y ≠ 0) :
    closure (Submodule.span ℂ (range fun y ↦ d y • complexLineEval ν m y) :
      Set (StrongDual ℂ C)) =
      {T : StrongDual ℂ C | ∀ (u : Circle) f, T (complexLocalRotation u f) = (u : ℂ) ^ (-m) * T f} := by
  obtain ⟨P, hP, hT⟩ := complexMellin_annihilator ν m
  obtain ⟨e, he⟩ := classicalSchwartz_reflexive ℂ
  rw [← hT, strongDual_closure_span_eq_annihilator e he _ P.ker]
  intro f
  change P f = 0 ↔ ∀ y, d y * complexLineEval ν m y f = 0
  rw [hP]
  exact forall_congr' fun y ↦ ⟨fun h ↦ by rw [h, mul_zero],
    fun h ↦ (mul_eq_zero.mp h).resolve_left (hd y)⟩

/-- Taking all integer angular weights generates the full complex strong dual. -/
theorem complexLocalMellin_strongSpan (d : ℤ × ℝ → ℂ) (hd : ∀ i, d i ≠ 0) :
    closure (Submodule.span ℂ (range fun i : ℤ × ℝ ↦ d i • complexLineEval ν i.1 i.2) :
      Set (StrongDual ℂ C)) = univ := by
  obtain ⟨e, he⟩ := classicalSchwartz_reflexive ℂ
  rw [strongDual_closure_span_eq_annihilator e he _ ⊥]
  · ext T
    simp
  · intro f
    simp only [Submodule.mem_bot]
    refine ⟨fun h i ↦ by simp [h], fun h ↦ ?_⟩
    have hrad (t : ℝ) (ht : 0 < t) : ∀ u : Circle, f (t • (u : ℂ)) = 0 := by
      let U (u : Circle) := f (t • (u : ℂ))
      have hU : Continuous U := f.continuous.comp (continuous_subtype_val.const_smul t)
      have hLp : MemLp U 2 ν := hU.memLp_of_hasCompactSupport
        (isCompact_univ.of_isClosed_subset isClosed_closure (subset_univ _))
      have hzero : U =ᵐ[ν] 0 := by
        apply ae_eq_zero_of_character_integral_eq_zero ν hLp
        intro χ
        obtain ⟨n, hn, _⟩ := existsUnique_circleCharacter_zpow
          ({ toFun := fun u ↦ (χ u : ℂ)
             map_one' := by simp
             map_mul' := by simp [Circle.coe_mul]
             continuous_toFun := continuous_subtype_val.comp χ.continuous } : Circle →ₜ* ℂ)
        have hmode := (complexLineEval_kernel ν (-n) f).mp
          (fun y ↦ (mul_eq_zero.mp (h (-n, y))).resolve_left (hd (-n, y))) t ht
        rw [← hmode, complexZetaProfile]
        apply integral_congr_ae
        refine .of_forall fun u ↦ ?_
        have hχ : (χ u : ℂ) = (u : ℂ) ^ n := hn u
        change star (χ u : ℂ) * f (t • (u : ℂ)) = (u : ℂ) ^ (-n) * f (t • (u : ℂ))
        have hstar : star (χ u : ℂ) = ((χ u)⁻¹ : Circle) := (Circle.coe_inv_eq_conj _).symm
        rw [hstar, Circle.coe_inv, hχ, zpow_neg]
      exact congrFun (Measure.eq_of_ae_eq hzero hU continuous_const)
    have hnonzero (x : ℂ) (hx : x ≠ 0) : f x = 0 := by
      let t := ‖x‖
      have ht : 0 < t := norm_pos_iff.mpr hx
      let u : Circle := ⟨(t : ℂ)⁻¹ * x, by
        change dist ((t : ℂ)⁻¹ * x) 0 = 1
        rw [dist_zero_right]
        rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg ht.le, inv_mul_cancel₀ ht.ne']⟩
      have hu : t • (u : ℂ) = x := by
        rw [Complex.real_smul]
        change (t : ℂ) * ((t : ℂ)⁻¹ * x) = x
        rw [← mul_assoc, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr ht.ne'), one_mul]
      exact hu ▸ hrad t ht u
    ext x
    have hclosed : IsClosed {x : ℂ | f x = 0} := isClosed_eq f.continuous continuous_const
    exact hclosed.closure_subset_iff.mpr (show ({0} : Set ℂ)ᶜ ⊆ _ from fun x hx ↦
      hnonzero x (by simpa using hx)) (by simp)

end ComplexPlace

section ArchimedeanCovariance

local instance : MeasurableSpace ℝˣ := borel _
local instance : BorelSpace ℝˣ := ⟨rfl⟩
local instance : MeasurableSpace ℂˣ := borel _
local instance : BorelSpace ℂˣ := ⟨rfl⟩

/-- Pullback by multiplication by the inverse local scalar. -/
def archLocalDilation (k : Type*) [RCLike k] (g : kˣ) : 𝓢(k, ℂ) →L[ℂ] 𝓢(k, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    ((ContinuousLinearEquiv.smulLeft (R₁ := k) (M₁ := k) g⁻¹).restrictScalars ℝ)

@[simp] theorem archLocalDilation_apply {k : Type*} [RCLike k] (g : kˣ)
    (f : 𝓢(k, ℂ)) (x : k) : archLocalDilation k g f x = f ((g⁻¹ : kˣ).val * x) := rfl

private theorem localHaar_weighted_dilation {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul G] (μ : Measure G) [μ.IsMulLeftInvariant] (c : G → ℂ)
    (hc : ∀ a b, c (a * b) = c a * c b) (g : G) (f : G → ℂ) :
    (∫ u, c u * f (g⁻¹ * u) ∂μ) = c g * ∫ u, c u * f u ∂μ := by
  conv_lhs => rw [← integral_mul_left_eq_self _ g]
  rw [← integral_const_mul]
  apply integral_congr_ae
  refine .of_forall fun u ↦ ?_
  change c (g * u) * f (g⁻¹ * (g * u)) = c g * (c u * f u)
  rw [hc, inv_mul_cancel_left, mul_assoc]

private def realLocalWeight (a : ℕ) (s : ℂ) (g : ℝˣ) : ℂ :=
  ((|(g : ℝ)| : ℝ) : ℂ) ^ s * (if (g : ℝ) < 0 then (-1 : ℂ) ^ a else 1)

private theorem realLocalWeight_mul (a : ℕ) (s : ℂ) (g h : ℝˣ) :
    realLocalWeight a s (g * h) = realLocalWeight a s g * realLocalWeight a s h := by
  simp only [realLocalWeight, Units.val_mul, abs_mul, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (abs_nonneg _) (abs_nonneg _)]
  have hg : (g : ℝ) ≠ 0 := g.ne_zero
  have hh : (h : ℝ) ≠ 0 := h.ne_zero
  have H : (if (g : ℝ) * (h : ℝ) < 0 then (-1 : ℂ) ^ a else 1) =
      (if (g : ℝ) < 0 then (-1 : ℂ) ^ a else 1) * (if (h : ℝ) < 0 then (-1 : ℂ) ^ a else 1) := by
    rcases lt_or_gt_of_ne hg with hgn | hgp <;> rcases lt_or_gt_of_ne hh with hhn | hhp
    · simp [hgn, hhn, (mul_pos_of_neg_of_neg hgn hhn).not_gt, ← mul_pow]
    · simp [hgn, hhp.not_gt, mul_neg_of_neg_of_pos hgn hhp]
    · simp [hgp.not_gt, hhn, mul_neg_of_pos_of_neg hgp hhn]
    · simp [hgp.not_gt, hhp.not_gt, (mul_pos hgp hhp).not_gt]
  rw [H]
  ring

/-- Real local Mellin values satisfy the full multiplicative eigenlaw. -/
theorem realLocalLineEval_translate (a : ℕ) (y : ℝ) (g : ℝˣ) (f : R) :
    realLocalLineEval a y (archLocalDilation ℝ g f) =
      realLocalWeight a (mellinLine y) g * realLocalLineEval a y f := by
  have hs : 0 < (mellinLine y).re := by rw [mellinLine_re]; norm_num
  simp only [realLocalLineEval, realArchimedeanZetaContinuedCLM_apply,
    (realArchimedeanZetaContinued_eq_unitIntegral a _ hs).2]
  change (∫ u : ℝˣ, realLocalWeight a (mellinLine y) u *
      f ((g⁻¹ : ℝˣ).val * u.val) ∂realArchMultiplicativeHaar) = _
  exact localHaar_weighted_dilation realArchMultiplicativeHaar _
    (realLocalWeight_mul a (mellinLine y)) g (fun u => f u.val)

private def complexLocalWeight (m : ℤ) (s : ℂ) (g : ℂˣ) : ℂ :=
  ((‖(g : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ s * ((g : ℂ) / (‖(g : ℂ)‖ : ℂ)) ^ m

private theorem complexLocalWeight_mul (m : ℤ) (s : ℂ) (g h : ℂˣ) :
    complexLocalWeight m s (g * h) = complexLocalWeight m s g * complexLocalWeight m s h := by
  simp only [complexLocalWeight, Units.val_mul, norm_mul, mul_pow, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (sq_nonneg _) (sq_nonneg _), mul_div_mul_comm, mul_zpow]
  ring

/-- Complex local Mellin values satisfy the full multiplicative eigenlaw. -/
theorem complexLocalLineEval_translate (m : ℤ) (y : ℝ) (g : ℂˣ) (f : C) :
    letI := complexTamagawaAngularMeasure_isHaar
    complexLineEval complexTamagawaAngularMeasure m y (archLocalDilation ℂ g f) =
      complexLocalWeight m (mellinLine y / 2) g * complexLineEval complexTamagawaAngularMeasure m y f := by
  have hs : 0 < (mellinLine y / 2).re := by simp [Complex.div_ofNat_re]
  simp only [complexLineEval, complexArchimedeanZetaContinuedCLM_apply,
    (complexArchimedeanZetaContinued_eq_unitIntegral m _ hs).2]
  change (∫ u : ℂˣ, complexLocalWeight m (mellinLine y / 2) u *
      f ((g⁻¹ : ℂˣ).val * u.val) ∂complexArchMultiplicativeHaar) = _
  exact localHaar_weighted_dilation complexArchMultiplicativeHaar _
    (complexLocalWeight_mul m (mellinLine y / 2)) g (fun u => f u.val)

end ArchimedeanCovariance

section NormalizedGeneration

attribute [local instance] complexZeta_circleMeasurable complexZeta_circleBorel

private theorem realArchZetaDenominator_line_ne_zero (a : ℕ) (y : ℝ) :
    realArchZetaDenominator a (mellinLine y) ≠ 0 := by
  apply inv_ne_zero
  apply Complex.Gammaℝ_ne_zero_of_re_pos
  simp [Complex.add_re, Complex.mul_re, Complex.natCast_re]
  exact add_pos_of_pos_of_nonneg zero_lt_one (Nat.cast_nonneg _)

private theorem complexArchZetaDenominator_line_ne_zero (m : ℤ) (y : ℝ) :
    complexArchZetaDenominator m (mellinLine y / 2) ≠ 0 := by
  apply inv_ne_zero
  let z : ℂ := mellinLine y / 2 + (m.natAbs : ℂ) / 2
  change Complex.Gammaℂ z ≠ 0
  rw [Complex.Gammaℂ_def]
  refine mul_ne_zero (mul_ne_zero (by norm_num) (Complex.cpow_ne_zero_iff.mpr (.inl ?_)))
    (Complex.Gamma_ne_zero_of_re_pos (s := z) ?_)
  · exact mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  · have hz : z.re = 1 / 2 + (m.natAbs : ℝ) / 2 := by
      simp [z, Complex.add_re, Complex.div_ofNat_re, Complex.mul_re]
    rw [hz]
    positivity

/-- The two Gamma-normalized real Mellin lines generate the full strong dual,
and each individual line generates its tempered parity component. -/
theorem realLocalNormalizedMellin_strongGeneration :
    (closure (Submodule.span ℂ (range fun i : Fin 2 × ℝ ↦
      realArchZetaDenominator i.1.val (mellinLine i.2) • realLocalLineEval i.1.val i.2) :
      Set (StrongDual ℂ R)) = univ) ∧
    ∀ a : Fin 2, closure (Submodule.span ℂ (range fun y ↦
      realArchZetaDenominator a.val (mellinLine y) • realLocalLineEval a.val y) :
      Set (StrongDual ℂ R)) =
      {T : StrongDual ℂ R | ∀ f, T (realLocalReflection f) = (-1 : ℂ) ^ a.val * T f} := by
  exact ⟨realLocalMellin_strongSpan _ (fun i ↦ realArchZetaDenominator_line_ne_zero i.1.val i.2),
    fun a ↦ realLocalMellin_homogeneous_strongSpan a.val _ (realArchZetaDenominator_line_ne_zero a.val)⟩

/-- The Gamma-normalized complex Mellin lines generate the full strong dual,
and each individual line generates its tempered angular component. -/
theorem complexLocalNormalizedMellin_strongGeneration :
    (closure (Submodule.span ℂ (range fun i : ℤ × ℝ ↦
      complexArchZetaDenominator i.1 (mellinLine i.2 / 2) •
        complexLineEval complexTamagawaAngularMeasure i.1 i.2) : Set (StrongDual ℂ C)) = univ) ∧
    ∀ m : ℤ, closure (Submodule.span ℂ (range fun y ↦
      complexArchZetaDenominator m (mellinLine y / 2) •
        complexLineEval complexTamagawaAngularMeasure m y) : Set (StrongDual ℂ C)) =
        {T : StrongDual ℂ C | ∀ (u : Circle) f, T (complexLocalRotation u f) = (u : ℂ) ^ (-m) * T f} := by
  letI := complexTamagawaAngularMeasure_isHaar
  exact ⟨complexLocalMellin_strongSpan complexTamagawaAngularMeasure _
    (fun i ↦ complexArchZetaDenominator_line_ne_zero i.1 i.2),
    fun m ↦ complexLocalMellin_homogeneous_strongSpan complexTamagawaAngularMeasure m _
      (complexArchZetaDenominator_line_ne_zero m)⟩

end NormalizedGeneration

end
end Masullo
