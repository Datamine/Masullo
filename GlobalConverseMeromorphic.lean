import GlobalConverseTopology
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.RemovableSingularity

/-! The periodic strip division proof is adapted from the Apache-2.0
RiemannMasullo project at cc4b472, ForMathlib/Analysis/Complex/PeriodicStrip.lean
and Ch05_ThetaZSpaces/Sec3b.lean. -/

open Complex Filter Function IsDedekindDomain MeasureTheory Metric NumberField Set Topology
open scoped Classical NumberField

namespace Masullo

/-- A nonzero entire function stays away from zero on some enclosing circle of prescribed minimum radius. -/
private theorem exists_sphere_norm_pos {D : ℂ → ℂ} (hD : Differentiable ℂ D) (hne : ∃ z, D z ≠ 0)
    (r : ℝ) (hr : 0 < r) : ∃ R > r, ∃ d > 0, ∀ z ∈ sphere (0 : ℂ) R, d ≤ ‖D z‖ := by
  classical
  obtain ⟨z₀, hz₀⟩ := hne
  have ha : AnalyticOnNhd ℂ D univ := fun z _ ↦ hD.analyticAt z
  have hdisc := (ha.eqOn_zero_or_eventually_ne_zero_of_preconnected isPreconnected_univ).resolve_left
    (fun h ↦ hz₀ (h (mem_univ z₀)))
  let K := closedBall (0 : ℂ) (r+1)
  have hK : IsCompact K := isCompact_closedBall _ _
  have hfin := hK.finite_sdiff_of_mem_codiscreteWithin
    (s := {z | D z ≠ 0}) ((Filter.codiscreteWithin_mono (subset_univ K)) hdisc)
  have hrad := hfin.image (fun z : ℂ ↦ ‖z‖)
  obtain ⟨R, hR, hout⟩ := (Ioo_infinite (show r < r+1 by linarith)).exists_notMem_finset hrad.toFinset
  have hRpos := hr.trans hR.1
  have hz (z : ℂ) (hs : z ∈ sphere 0 R) : D z ≠ 0 := by
    intro he
    have hn : ‖z‖ = R := mem_sphere_zero_iff_norm.mp hs
    apply hout
    exact hrad.mem_toFinset.mpr ⟨z, ⟨mem_closedBall_zero_iff.mpr (hn ▸ hR.2.le), fun h ↦ h he⟩, hn⟩
  obtain ⟨w, hw, hmin⟩ := (isCompact_sphere (0 : ℂ) R).exists_isMinOn
    (NormedSpace.sphere_nonempty.mpr hRpos.le) hD.continuous.norm.continuousOn
  exact ⟨R, hR.1, ‖D w‖, norm_pos_iff.mpr (hz w hw), fun z hs ↦ hmin hs⟩

/-- Division by a nonzero entire function with a purely imaginary period preserves
boundedness on every closed vertical strip provided the quotient is entire. -/
theorem bddAbove_strip_of_periodic_mul {D G : ℂ → ℂ} (hD : Differentiable ℂ D)
    (hne : ∃ z, D z ≠ 0) {T : ℝ} (hT : 0 < T) (hper : Function.Periodic D ((T : ℂ) * I))
    (hG : Differentiable ℂ G)
    (h : ∀ a b : ℝ, a ≤ b → BddAbove ((fun z : ℂ ↦ ‖D z * G z‖) '' (re ⁻¹' Icc a b)))
    (a b : ℝ) : BddAbove ((fun z : ℂ ↦ ‖G z‖) '' (re ⁻¹' Icc a b)) := by
  let r := |a| + |b| + T + 1
  have hr : 0 < r := by dsimp [r]; positivity
  obtain ⟨R, hR, d, hd, hDlow⟩ := exists_sphere_norm_pos hD hne r hr
  have hRp := hr.trans hR
  obtain ⟨B, hB⟩ := h (-R) R (by linarith)
  refine ⟨B/d, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  change a ≤ z.re ∧ z.re ≤ b at hz
  let n : ℤ := ⌊z.im / T⌋
  let c : ℂ := (n : ℂ) * ((T : ℂ) * I)
  have hc : c.re = 0 ∧ c.im = (n : ℝ) * T := by simp [c]
  have h0 : (n : ℝ) * T ≤ z.im := (le_div_iff₀ hT).mp (Int.floor_le _)
  have h1 : z.im < ((n : ℝ)+1) * T := (div_lt_iff₀ hT).mp (Int.lt_floor_add_one _)
  have hin : z - c ∈ ball 0 R := by
    rw [mem_ball_zero_iff]
    apply (norm_le_abs_re_add_abs_im _).trans_lt
    rw [sub_re, sub_im, hc.1, hc.2, sub_zero, abs_of_nonneg (sub_nonneg.mpr h0)]
    have hre : |z.re| ≤ |a|+|b| := abs_le.mpr ⟨by linarith [neg_abs_le a, abs_nonneg b, hz.1],
      by linarith [le_abs_self b, abs_nonneg a, hz.2]⟩
    dsimp [r] at hR
    linarith
  let g (w : ℂ) := G (w + c)
  have hg : Differentiable ℂ g := hG.comp (differentiable_id.add_const c)
  have hgB : ‖g (z - c)‖ ≤ B / d := by
    apply Complex.norm_le_of_forall_mem_frontier_norm_le (isBounded_ball : Bornology.IsBounded (ball (0 : ℂ) R))
      hg.diffContOnCl _ (subset_closure hin)
    intro w hw
    rw [frontier_ball _ hRp.ne'] at hw
    have hwn := mem_sphere_zero_iff_norm.mp hw
    have hwre := abs_le.mp ((abs_re_le_norm w).trans_eq hwn)
    have hstrip : (w + c).re ∈ Icc (-R) R := by rwa [add_re, hc.1, add_zero]
    have hprod := hB (mem_image_of_mem (fun v : ℂ ↦ ‖D v * G v‖) hstrip)
    rw [norm_mul, hper.int_mul n w] at hprod
    exact (le_div_iff₀' hd).mpr ((mul_le_mul_of_nonneg_right (hDlow w hw) (norm_nonneg _)).trans hprod)
  simpa [g] using hgB

/-- Entire division by a periodic factor preserves every polynomial weight on vertical strips. -/
theorem schwartzBergman_of_periodic_mul {D G : ℂ → ℂ} (hD : Differentiable ℂ D)
    (hne : ∃ z, D z ≠ 0) {T : ℝ} (hT : 0 < T) (hper : Function.Periodic D ((T : ℂ) * I))
    (hG : Differentiable ℂ G) (h : (fun z ↦ D z * G z) ∈ schwartzBergmanSubmodule univ) :
    G ∈ schwartzBergmanSubmodule univ := by
  refine ⟨fun z hz ↦ (hz (mem_univ _)).elim, hG.differentiableOn, ?_⟩
  intro a b _ _ N
  apply bddAbove_strip_of_periodic_mul hD hne hT hper ((differentiable_id.pow N).mul hG) _ a b
  intro u v huv
  simpa only [Pi.pow_apply, Pi.mul_apply, id_eq, mul_left_comm] using h.2.2 u v huv (subset_univ _) N

private theorem schwartzBergman_mul_linearFactor (f : ℂ → ℂ) (a : ℂ)
    (hf : f ∈ schwartzBergmanSubmodule univ) :
    (fun z ↦ (z - a) * f z) ∈ schwartzBergmanSubmodule univ := by
  have hz : (fun z ↦ z * f z) ∈ schwartzBergmanSubmodule univ := by
    refine ⟨fun z hz ↦ (hz (mem_univ _)).elim, differentiable_id.differentiableOn.mul hf.2.1,
      fun l r hlr hI n ↦ ?_⟩
    simpa only [pow_succ, mul_assoc] using hf.2.2 l r hlr hI (n + 1)
  convert (schwartzBergmanSubmodule univ).sub_mem hz
    ((schwartzBergmanSubmodule univ).smul_mem a hf) using 1
  ext z
  exact sub_mul z a (f z)

private theorem schwartzBergman_of_mul_linearFactor (f : ℂ → ℂ) (a : ℂ)
    (hf : Differentiable ℂ f) (h : (fun z ↦ (z - a) * f z) ∈ schwartzBergmanSubmodule univ) :
    f ∈ schwartzBergmanSubmodule univ := by
  refine ⟨fun z hz ↦ (hz (mem_univ _)).elim, hf.differentiableOn, fun l r hlr hI n ↦ ?_⟩
  obtain ⟨A, hA⟩ := h.2.2 l r hlr hI n
  obtain ⟨C, hC⟩ := (isCompact_closedBall a 1).bddAbove_image
    ((continuous_pow n).mul hf.continuous).norm.continuousOn
  refine ⟨max A C, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  by_cases hb : z ∈ closedBall a 1
  · exact (hC (mem_image_of_mem _ hb)).trans (le_max_right _ _)
  · have h₁ : 1 ≤ ‖z - a‖ :=
      (lt_of_not_ge (by simpa [mem_closedBall, dist_eq_norm] using hb)).le
    have hbound := hA ⟨z, hz, rfl⟩
    change ‖z ^ n * ((z - a) * f z)‖ ≤ A at hbound
    rw [mul_left_comm, norm_mul] at hbound
    exact (le_mul_of_one_le_left (norm_nonneg _) h₁).trans (hbound.trans (le_max_left _ _))

private theorem entire_zero_zero_one_division (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (h₀ : f 0 = 0) (h₁ : f 1 = 0) :
    ∃ q : ℂ → ℂ, Differentiable ℂ q ∧ ∀ z, f z = z * (1 - z) * q z := by
  let v := dslope f 0
  have hv : Differentiable ℂ v := differentiableOn_univ.mp
    ((Complex.differentiableOn_dslope (univ_mem : (univ : Set ℂ) ∈ 𝓝 0)).mpr hf.differentiableOn)
  have he (z : ℂ) : z * v z = f z := by
    simpa only [sub_zero, smul_eq_mul] using sub_smul_dslope_of_zero h₀ z
  have hv₁ : v 1 = 0 := by simpa only [one_mul] using (he 1).trans h₁
  have hw : Differentiable ℂ (dslope v 1) := differentiableOn_univ.mp
    ((Complex.differentiableOn_dslope (univ_mem : (univ : Set ℂ) ∈ 𝓝 1)).mpr hv.differentiableOn)
  refine ⟨-dslope v 1, hw.neg, fun z ↦ ?_⟩
  have hx : (z - 1) * dslope v 1 z = v z := sub_smul_dslope_of_zero hv₁ z
  rw [← he, ← hx]
  change _ = _ * -_
  ring

private theorem continuous_eq_of_off_zero_one {g f : ℂ → ℂ} (hg : Continuous g)
    (hf : Continuous f) (he : ∀ z : ℂ, z ≠ 0 → z ≠ 1 → g z = f z) : g = f := by
  funext z
  apply ((hg.continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE hf.continuousAt).mp ?_).eq_of_nhds
  have hne (w : ℂ) : ∀ᶠ t in 𝓝[≠] z, t ≠ w := by
    rcases eq_or_ne z w with rfl | h
    · exact self_mem_nhdsWithin
    · exact eventually_ne_nhdsWithin h
  filter_upwards [hne 0, hne 1] with w hw₀ hw₁ using he w hw₀ hw₁

noncomputable section

variable (F : Type*) [Field F] [NumberField F]
private abbrev K := normOneIdeleClass F
local instance : MeasurableSpace (K F) := borel _
local instance : BorelSpace (K F) := ⟨rfl⟩
local instance : MeasurableSpace (Idele F) := borel _
local instance : BorelSpace (Idele F) := ⟨rfl⟩

variable (ν : Measure (K F)) [ν.IsHaarMeasure]
variable (η : Measure (Idele F)) [η.IsHaarMeasure]
variable (hν : IsWeilQuotientMeasure (principalIdeles F) η Measure.count (globalClassMeasure F ν))
private abbrev χ := compactIdeleClassCharacter F (1 : PontryaginDual (K F))
private abbrev Z (f : GlobalBruhat F) := globalZetaContinued F ν f (χ F) 0

include hν in
/-- Clearing the two possible poles of a trivial-component adelic Mellin
transform gives an entire Schwartz–Bergman function. Two radial translations
clear the residues, and periodic division transfers the strip estimates back. -/
theorem globalTrivialClearedZeta_mem_schwartzBergman (f : GlobalBruhat F) :
    globalHeckeClearedZeta F ν 1 f ∈ schwartzBergmanSubmodule univ := by
  let c : ℂ := Real.exp 1
  let G := globalHeckeClearedZeta F ν 1 f
  let D : ℂ → ℂ := fun z ↦ (Complex.exp z - 1) * (Complex.exp z - c)
  have hG : Differentiable ℂ G := fun z ↦ (globalHeckeClearedZeta_analytic F ν 1 f z).differentiableAt
  have hExp : Differentiable ℂ Complex.exp := differentiable_id.cexp
  have hD : Differentiable ℂ D := (hExp.sub_const _).mul (hExp.sub_const _)
  have hD₂ : D 2 ≠ 0 := by
    change (Complex.exp 2 - 1) * (Complex.exp 2 - (Real.exp 1 : ℂ)) ≠ 0
    rw [← Complex.ofReal_ofNat, ← Complex.ofReal_exp, ← Complex.ofReal_one,
      ← Complex.ofReal_sub, ← Complex.ofReal_sub]
    exact mul_ne_zero
      (Complex.ofReal_ne_zero.mpr (sub_ne_zero.mpr (Real.one_lt_exp_iff.mpr (by norm_num)).ne'))
      (Complex.ofReal_ne_zero.mpr (sub_ne_zero.mpr (Real.exp_injective.ne (by norm_num))))
  have hper : Periodic D (((2 * Real.pi : ℝ) : ℂ) * Complex.I) := by
    intro z
    push_cast
    exact congrArg (fun w : ℂ ↦ (w - 1) * (w - c)) (Complex.exp_periodic z)
  obtain ⟨a, ha⟩ := ideleClassMap_surjective F (ideleClassExpSection F (Multiplicative.ofAdd 1))
  have hNorm : ideleNorm F a = Real.exp 1 := by
    change ideleClassNorm F (ideleClassMap F a) = _
    rw [ha, ideleClassNorm_expSection]
    rfl
  have hTrans (u : GlobalBruhat F) (z : ℂ) (hz₀ : z ≠ 0) (hz₁ : z ≠ 1) :
      Z F ν (GlobalBruhat.leftTranslate F a u) z = Complex.exp z * Z F ν u z := by
    have ht := globalZetaContinued_leftTranslate F η ν hν a u 1 z (fun _ ↦ ⟨hz₀, hz₁⟩)
    change Z F ν (GlobalBruhat.leftTranslate F a u) z =
      (ideleNormTwist F (χ F) z (ideleClassMap F a) : ℂ) * Z F ν u z at ht
    rw [ht]
    congr 1
    change (χ F (ideleClassMap F a) : ℂ) * ideleNormPower F z (ideleClassMap F a) = _
    rw [ha, compactIdeleClassCharacter_apply_ray F 1 1, one_mul,
      ideleNormPower, ideleClassNorm_expSection, Real.log_exp]
    change Complex.exp (z * ((1 : ℝ) : ℂ)) = Complex.exp z
    rw [Complex.ofReal_one, mul_one]
  let u := GlobalBruhat.leftTranslate F a f - f
  let v := GlobalBruhat.leftTranslate F a u - c • u
  have hu₀ : (GlobalBruhat.polarEvaluation F u).1 = 0 := by
    simp only [u, map_sub, polarEvaluation_leftTranslate, Prod.fst_sub, sub_self]
  have hv : GlobalBruhat.polarEvaluation F v = 0 := by
    rw [map_sub, polarEvaluation_leftTranslate, map_smul, hu₀]
    apply sub_eq_zero.mpr
    apply Prod.ext
    · simp [hu₀]
    · simp [Complex.real_smul, c, hNorm]
  have hvPole : globalZetaPolarVanishes F v (χ F) :=
    (globalZetaPolarVanishes_compact_iff F v 1).mpr
      (Or.inr ⟨congrArg Prod.fst hv, congrArg Prod.snd hv⟩)
  have hvB := globalZetaContinued_mem_schwartzBergman F ν 1 v hvPole
  have hprod : (fun z ↦ z * (1 - z) * Z F ν v z) ∈ schwartzBergmanSubmodule univ := by
    have h := (schwartzBergmanSubmodule univ).neg_mem
      (schwartzBergman_mul_linearFactor _ 0 (schwartzBergman_mul_linearFactor _ 1 hvB))
    convert h using 1
    ext z
    change z * (1 - z) * Z F ν v z = -((z - 0) * ((z - 1) * Z F ν v z))
    ring
  apply schwartzBergman_of_periodic_mul hD ⟨2, hD₂⟩ (mul_pos (by norm_num) Real.pi_pos)
    hper hG
  suffices he : (fun z ↦ D z * G z) = fun z ↦ z * (1 - z) * Z F ν v z from he ▸ hprod
  have hZv : Differentiable ℂ (Z F ν v) := by
    simpa only [preimage_univ, differentiableOn_univ] using hvB.2.1
  have hc₁ : Continuous (fun z ↦ D z * G z) := hD.continuous.mul hG.continuous
  have hc₂ : Continuous (fun z ↦ z * (1 - z) * Z F ν v z) :=
    (continuous_id.mul (continuous_const.sub continuous_id)).mul hZv.continuous
  funext z
  apply ((hc₁.continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE hc₂.continuousAt).mp ?_).eq_of_nhds
  have hne (w : ℂ) : ∀ᶠ t in 𝓝[≠] z, t ≠ w := by
    rcases eq_or_ne z w with rfl | h
    · exact self_mem_nhdsWithin
    · exact eventually_ne_nhdsWithin h
  filter_upwards [hne 0, hne 1] with w hw₀ hw₁
  have hSub (g k : GlobalBruhat F) : Z F ν (g-k) w = Z F ν g w - Z F ν k w := by
    simp only [Z, ← globalContinuedMellinEval_apply, map_sub]
  have hSMul (k : GlobalBruhat F) : Z F ν (c • k) w = c * Z F ν k w := by
    simp only [Z, ← globalContinuedMellinEval_apply, map_smul, smul_eq_mul]
  change D w * G w = w * (1 - w) * Z F ν v w
  dsimp only [G, v]
  rw [globalHeckeClearedZeta_eq F ν 1 f w hw₀ hw₁, hSub, hSMul, hTrans u w hw₀ hw₁]
  have hu : Z F ν u w = Complex.exp w * Z F ν f w - Z F ν f w := by
    change Z F ν (GlobalBruhat.leftTranslate F a f - f) w = _
    rw [hSub, hTrans f w hw₀ hw₁]
  rw [hu]
  simp only [globalHeckePoleFactor, ite_true, D]
  change _ * (_ * Z F ν f w) = _
  ring

private theorem ideleNormTwist_iterated (χ₀ : IdeleQuasiCharacter F) (d z : ℂ) :
    ideleNormTwist F (ideleNormTwist F χ₀ d) z = ideleNormTwist F χ₀ (z + d) := by
  ext q
  change ((χ₀ q : ℂ) * ideleNormPower F d q) * ideleNormPower F z q =
    (χ₀ q : ℂ) * ideleNormPower F (z + d) q
  simp only [ideleNormPower, add_mul, Complex.exp_add]
  ring

private theorem ideleNormTwist_character_inv (χ₀ : IdeleQuasiCharacter F) (d : ℂ) :
    (ideleNormTwist F χ₀ d)⁻¹ = ideleNormTwist F χ₀⁻¹ (-d) := by
  ext q
  change (↑((ideleNormTwist F χ₀ d q)⁻¹ : ℂˣ) : ℂ) =
    (↑((χ₀ q)⁻¹ : ℂˣ) : ℂ) * ideleNormPower F (-d) q
  rw [Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val]
  change (((χ₀ q : ℂ) * ideleNormPower F d q)⁻¹) =
    ((χ₀ q : ℂ)⁻¹) * ideleNormPower F (-d) q
  rw [mul_inv_rev]
  simp only [ideleNormPower, neg_mul, Complex.exp_neg]
  ring

omit [ν.IsHaarMeasure] in
/-- The continued transform for a norm twist is the actual continuation in
the translated canonical chart, including its specified values at the poles. -/
theorem globalZetaContinued_compact_twist (ω : PontryaginDual (K F))
    (f : GlobalBruhat F) (d z : ℂ) :
    globalZetaContinued F ν f (ideleNormTwist F (compactIdeleClassCharacter F ω) d) d z =
      globalZetaContinued F ν f (compactIdeleClassCharacter F ω) 0 (z + d) := by
  let χ₀ := compactIdeleClassCharacter F ω
  have hC :
      (fun k : K F ↦ (ideleNormTwist F χ₀ d k.val : ℂ)) =
        fun k : K F ↦ (χ₀ k.val : ℂ) := by
    funext k
    exact congrArg Units.val
      (DFunLike.congr_fun (restrictToNormOne_twist F χ₀ d) k)
  have hU (g : GlobalBruhat F) (ψ : IdeleQuasiCharacter F) (a b : ℂ) :
      thetaZetaUpper F ν g (ideleNormTwist F ψ a) b =
        thetaZetaUpper F ν g ψ (b + a) := by
    unfold thetaZetaUpper
    simp only [ideleNormTwist_iterated]
  unfold globalZetaContinued
  change thetaZetaUpper F ν f (ideleNormTwist F χ₀ d) z +
      thetaZetaUpper F ν (GlobalBruhat.fourier F f) (ideleNormTwist F χ₀ d)⁻¹ (1-z) +
      (∫ k : K F, (ideleNormTwist F χ₀ d k.val : ℂ) ∂ν) *
        (GlobalBruhat.algebraicEquiv F (GlobalBruhat.fourier F f)).val 0 / (z+d-1) -
      (∫ k : K F, (ideleNormTwist F χ₀ d k.val : ℂ) ∂ν) *
        (GlobalBruhat.algebraicEquiv F f).val 0 / (z+d) = _
  rw [hC, hU, ideleNormTwist_character_inv, hU]
  rw [show (1 - z : ℂ) + -d = 1 - (z + d) by ring]
  simp only [add_zero, χ₀]

/-- The Mellin map in a translated chart is the integral of the actual
homogeneous theta profile wherever that integral converges in the converse. -/
theorem globalConverse_shiftedMellin_eq_radial (ω : PontryaginDual (K F))
    (f : GlobalBruhat F) (d z : ℂ)
    (hz : 1 < (z + d).re ∨ ω ≠ 1 ∨ GlobalBruhat.polarEvaluation F f = 0) :
    globalZetaContinued F ν f (ideleNormTwist F (compactIdeleClassCharacter F ω) d) d z =
      ∫ t : ℝ, Complex.exp ((z + d) * (t : ℂ)) *
        adelicHomogeneousTheta F ν ω (GlobalBruhat.algebraicEquiv F f).val
          (ideleClassExpSection F (Multiplicative.ofAdd t)) := by
  rw [globalZetaContinued_compact_twist]
  let χ₀ := compactIdeleClassCharacter F ω
  have hC := compactIdeleClassCharacter_unitary F ω
  have hv : 1 < (z + d).re ∨ globalZetaPolarVanishes F f χ₀ := by
    refine hz.imp id ?_
    intro h
    apply (globalZetaPolarVanishes_compact_iff F f ω).mpr
    exact h.imp id (fun hp ↦ ⟨congrArg Prod.fst hp, congrArg Prod.snd hp⟩)
  rw [← globalRadialZeta_eq_continued F ν f χ₀ hC (κ := 0) Complex.zero_re
    (fun t ↦ by simp [χ₀]) (ideleClassExpSection F) (fun t ↦ ideleClassNorm_expSection F _)
    (z + d) hv]
  apply integral_congr_ae (.of_forall fun t ↦ ?_)
  rw [globalRadialZetaIntegrand_canonical, compactIdeleClassCharacter_apply_ray,
    normOnePontryaginCharacter_compactIdeleClassCharacter, one_mul]

omit [ν.IsHaarMeasure] in
/-- The spectral translation attached to a unitary idelic character is
uniquely specified by a real frequency and the compact restriction. -/
theorem ideleUnitaryCharacter_existsUnique_compact_frequency
    (ψ : IdeleQuasiCharacter F) (hψ : IsUnitary F ψ) :
    ∃! p : PontryaginDual (K F) × ℝ,
      ψ = ideleNormTwist F (compactIdeleClassCharacter F p.1) ((p.2 : ℂ) * Complex.I) := by
  obtain ⟨ω, d, hd, huniq⟩ := ideleClassCharacter_existsUnique_compact_twist F ψ
  let u := ideleClassExpSection F (Multiplicative.ofAdd (1 : ℝ))
  have hu : ideleClassNorm F u = Real.exp 1 := by
    rw [ideleClassNorm_expSection]
    rfl
  have hnorm := norm_ideleNormTwist F (compactIdeleClassCharacter F ω)
    (compactIdeleClassCharacter_unitary F ω) d u
  rw [← hd, hψ, hu, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp, one_mul] at hnorm
  have hre : d.re = 0 := Real.exp_injective (hnorm.symm.trans Real.exp_zero.symm)
  have hD : (d.im : ℂ) * Complex.I = d := by
    apply Complex.ext <;> simp [hre]
  refine ⟨(ω, d.im), by simpa only [hD] using hd, ?_⟩
  rintro ⟨ω', t⟩ h
  have hw : ω' = ω := ideleClassCharacter_compact_twist_injective F ω' ω _ _ (h.symm.trans hd)
  subst ω'
  have he := huniq _ h
  exact Prod.ext rfl (by simpa using congrArg Complex.im he)

private abbrev B := SchwartzBergman (univ : Set ℝ)
private abbrev G (f : GlobalBruhat F) := globalHeckeClearedZeta F ν 1 f

include hν in
/-- For a minimal Hecke reference, clearing the two possible poles of the
actual trivial homogeneous component gives exactly the entire divisor ideal. -/
theorem globalTrivialClearedZeta_range_of_min (r : GlobalBruhat F)
    (hr : ∀ z, meromorphicOrderAt (Z F ν r) z ≠ ⊤)
    (hmin : ∀ (f : GlobalBruhat F) (z : ℂ),
      meromorphicOrderAt (Z F ν r) z ≤ meromorphicOrderAt (Z F ν f) z)
    (hlift : ∀ b : B, b ∈ bergmanDivisorSubmodule (G F ν r) →
      ∃ f : GlobalBruhat F, GlobalBruhat.polarEvaluation F f = 0 ∧ Z F ν f = b.val) :
    ∀ b : B, b ∈ bergmanDivisorSubmodule (G F ν r) ↔
      ∃ f : GlobalBruhat F, G F ν f = b.val := by
  have hG (f : GlobalBruhat F) : Differentiable ℂ (G F ν f) :=
    fun z ↦ (globalHeckeClearedZeta_analytic F ν 1 f z).differentiableAt
  have hFin := globalHeckeClearedZeta_order_ne_top F ν 1 r hr
  have hne := trivial_reference_regularized_nonzero F ν r hmin
  have hd (b : B) : Differentiable ℂ b.val := by
    simpa only [preimage_univ, differentiableOn_univ] using b.property.2.1
  let cleared (f : GlobalBruhat F) : B :=
    ⟨G F ν f, globalTrivialClearedZeta_mem_schwartzBergman F ν η hν f⟩
  have hforward (f : GlobalBruhat F) :
      cleared f ∈ bergmanDivisorSubmodule (G F ν r) := by
    apply (bergmanDivisorSubmodule_mem_iff (hG r) _).mpr
    apply (entire_divisibility_iff_orders (hG r) (hG f)).mpr
    intro z
    apply analyticOrder_le_of_meromorphicOrder_le ((hG r).analyticAt z) ((hG f).analyticAt z) (hFin z)
    change meromorphicOrderAt (globalHeckeClearedZeta F ν 1 r) z ≤
      meromorphicOrderAt (globalHeckeClearedZeta F ν 1 f) z
    rw [globalHeckeClearedZeta_meromorphicOrder, globalHeckeClearedZeta_meromorphicOrder]
    exact add_le_add le_rfl (hmin f z)
  intro b
  constructor
  · intro hb
    letI := normOneIdeleClass_compact F
    letI : IsFiniteMeasure ν := ⟨isCompact_univ.measure_lt_top⟩
    let c : ℂ := -(ν.real univ : ℂ)
    have hc : c ≠ 0 := neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr
      (measureReal_univ_pos (μ := ν)).ne')
    obtain ⟨f₀, hf₀⟩ := GlobalBruhat.polarEvaluation_surjective F (b.val 0 / c, b.val 1 / c)
    have h₀ : G F ν f₀ 0 = b.val 0 := by
      have h : (GlobalBruhat.algebraicEquiv F f₀).val 0 = b.val 0 / c := congrArg Prod.fst hf₀
      rw [G, globalHeckeClearedZeta_trivial_zero, h, ← neg_mul]
      change c * (b.val _ / c) = _
      field_simp
    have h₁ : G F ν f₀ 1 = b.val 1 := by
      have h : (GlobalBruhat.algebraicEquiv F (GlobalBruhat.fourier F f₀)).val 0 = b.val 1 / c :=
        congrArg Prod.snd hf₀
      rw [G, globalHeckeClearedZeta_trivial_one, h, ← neg_mul]
      change c * (b.val _ / c) = _
      field_simp
    obtain ⟨k, hk, hbk⟩ := (bergmanDivisorSubmodule_mem_iff (hG r) b).mp hb
    obtain ⟨j, hj, hfj⟩ := (bergmanDivisorSubmodule_mem_iff (hG r) (cleared f₀)).mp (hforward f₀)
    have hK (z : ℂ) (hz : G F ν r z ≠ 0) (he : G F ν f₀ z = b.val z) : (k-j) z = 0 := by
      apply (mul_eq_zero.mp ?_).resolve_left hz
      change G F ν r z * (k z - j z) = 0
      rw [mul_sub, ← hbk z, ← hfj z]
      exact sub_eq_zero.mpr he.symm
    obtain ⟨q, hq, hqeq⟩ := entire_zero_zero_one_division (k-j) (hk.sub hj)
      (hK 0 hne.1 h₀) (hK 1 hne.2 h₁)
    let Q : ℂ → ℂ := fun z ↦ G F ν r z * q z
    have hQ : Differentiable ℂ Q := (hG r).mul hq
    have he (z : ℂ) : b.val z - G F ν f₀ z = z * (1 - z) * Q z := by
      change b.val z - (cleared f₀).val z = _
      rw [hbk z, hfj z, ← mul_sub]
      change G F ν r z * ((k-j) z) = _
      rw [hqeq z]
      dsimp [Q]
      ring
    have hTwo : (fun z ↦ (z - 0) * ((z - 1) * Q z)) ∈ schwartzBergmanSubmodule univ := by
      have hEq : (fun z ↦ (z - 0) * ((z - 1) * Q z)) = -(b - cleared f₀).val := by
        funext z
        change _ = -(b.val z - G F ν f₀ z)
        rw [he]
        ring
      rw [hEq]
      exact (schwartzBergmanSubmodule univ).neg_mem (b - cleared f₀).property
    have hQB := schwartzBergman_of_mul_linearFactor Q 1 hQ
      (schwartzBergman_of_mul_linearFactor _ 0 ((differentiable_id.sub_const 1).mul hQ) hTwo)
    obtain ⟨u, _, hu⟩ := hlift ⟨Q, hQB⟩
      ((bergmanDivisorSubmodule_mem_iff (hG r) _).mpr ⟨q, hq, fun _ ↦ rfl⟩)
    refine ⟨u + f₀, continuous_eq_of_off_zero_one (hG _).continuous (hd b).continuous ?_⟩
    intro z hz₀ hz₁
    rw [G, globalHeckeClearedZeta_eq F ν 1 _ z hz₀ hz₁]
    have hZ : Z F ν (u + f₀) z = Z F ν u z + Z F ν f₀ z := by
      simp only [Z, ← globalContinuedMellinEval_apply, map_add]
    change globalHeckePoleFactor F 1 z * Z F ν (u + f₀) z = _
    rw [hZ, hu, mul_add, ← globalHeckeClearedZeta_eq F ν 1 f₀ z hz₀ hz₁]
    simp only [globalHeckePoleFactor, ite_true]
    change z * (1 - z) * Q z + G F ν f₀ z = _
    rw [← he, sub_add_cancel]
  · rintro ⟨f, hf⟩
    have he : cleared f = b := Subtype.ext hf
    exact he ▸ hforward f

include hν in
/-- The meromorphic Mellin image in a shifted chart is exactly the functions
whose pole-polynomial multiple extends to the shifted entire divisor ideal. -/
theorem globalTrivialMellin_regular_range_of_cleared_range
    (r : GlobalBruhat F)
    (hCanon : ∀ b : B, b ∈ bergmanDivisorSubmodule (G F ν r) ↔
      ∃ f : GlobalBruhat F, G F ν f = b.val) (d : ℂ) :
    let M := globalRegularMellin F ν η hν 1 d
    ∀ u : globalShiftedMellinRegularSet d → ℂ, u ∈ M.range ↔
      ∃ b : B, b ∈ bergmanDivisorSubmodule (fun z ↦ G F ν r (z + d)) ∧
        ∀ z : globalShiftedMellinRegularSet d,
          b.val z.val = (z.val + d) * (1 - z.val - d) * u z := by
  intro M u
  let H := globalIdelicZetaComponentKernel F η (1 : PontryaginDual (K F))
  let E := schwartzBergmanEntireShift d
  have hG : Differentiable ℂ (G F ν r) :=
    fun z ↦ (globalHeckeClearedZeta_analytic F ν 1 r z).differentiableAt
  have hshift (b : B) :
      E b ∈ bergmanDivisorSubmodule (fun z ↦ G F ν r (z + d)) ↔
        b ∈ bergmanDivisorSubmodule (G F ν r) := bergmanDivisorSubmodule_shift_mem_iff hG d b
  have hTest (f : GlobalBruhat F) (z : globalShiftedMellinRegularSet d) :
      G F ν f (z.val + d) = (z.val + d) * (1 - z.val - d) * M (H.mkQ f) z := by
    change globalHeckeClearedZeta F ν 1 f (z.val + d) = _
    rw [globalHeckeClearedZeta_eq F ν 1 f _ z.property.1 z.property.2]
    change _ = _ * globalRegularMellin F ν η hν 1 d (H.mkQ f) z
    rw [globalRegularMellin_mk_apply]
    simp only [globalHeckePoleFactor, ite_true]
    ring
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨f, rfl⟩ := H.mkQ_surjective x
    let b : B := ⟨G F ν f, globalTrivialClearedZeta_mem_schwartzBergman F ν η hν f⟩
    refine ⟨E b, (hshift b).mpr ((hCanon b).mpr ⟨f, rfl⟩), fun z ↦ ?_⟩
    change (schwartzBergmanEntireShift d b).val z.val = _
    rw [schwartzBergmanEntireShift_apply]
    exact hTest f z
  · rintro ⟨b, hb, he⟩
    let b₀ := E.symm b
    have hE : E b₀ = b := E.apply_symm_apply b
    have hb₀ : b₀ ∈ bergmanDivisorSubmodule (G F ν r) :=
      (hshift b₀).mp (hE.symm ▸ hb)
    obtain ⟨f, hf⟩ := (hCanon b₀).mp hb₀
    refine ⟨H.mkQ f, funext fun z ↦ ?_⟩
    have h₀ : z.val + d ≠ 0 := z.property.1
    have h₁ : 1 - z.val - d ≠ 0 := by
      rw [← sub_add_eq_sub_sub]
      exact sub_ne_zero.mpr z.property.2.symm
    apply mul_left_cancel₀ (mul_ne_zero h₀ h₁)
    rw [← hTest, hf, ← he, ← hE, schwartzBergmanEntireShift_apply]

variable [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)ˣ]
  (μ : ∀ v : HeightOneSpectrum (𝓞 F), Measure (v.adicCompletion F)ˣ)
  [∀ v : HeightOneSpectrum (𝓞 F), (μ v).IsHaarMeasure]
  [∀ v : HeightOneSpectrum (𝓞 F), SigmaFinite (μ v)]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]

private abbrev Zω (ω : PontryaginDual (K F)) (f : GlobalBruhat F) :=
    globalZetaContinued F ν f (compactIdeleClassCharacter F ω) 0

include μ hν in
/-- The reference used for the converse can be normalized to the completed
Euler product by one nonzero scalar on the convergence half-plane. -/
theorem exists_globalConverse_eulerReference (ω : PontryaginDual (K F)) :
    ∃ (S : Finset (HeightOneSpectrum (𝓞 F))) (hS : Surjective (sIdeleClassInclusion F S))
      (hω : globalNormOneCharacter F ω ∈ (sUnramified F S : Set (QuasiCharacter (IdeleClass F))))
      (r : GlobalBruhat F) (C : ℂ), C ≠ 0 ∧
      (∀ z, meromorphicOrderAt (Zω F ν ω r) z ≠ ⊤) ∧
      (∀ f : GlobalBruhat F, ∀ z, meromorphicOrderAt (Zω F ν ω r) z ≤ meromorphicOrderAt (Zω F ν ω f) z) ∧
      EqOn (Zω F ν ω r) (fun z ↦ C * globalCompletedHeckeEuler F ω S hS hω z) {z | 1 < z.re} := by
  obtain ⟨S, hS, hω, _, _⟩ := exists_globalHeckeTateStage F ω
  obtain ⟨r, C, hC, hN, hFinite, _⟩ := exists_globalMellin_order_reference F η ω S hS hω μ ν hν
  obtain ⟨A, hA, hEq⟩ := globalZetaContinued_reference_eq_completedEuler F ω S hS hω η ν μ hν
    r C hN (hFinite 2)
  exact ⟨S, hS, hω, r.val, A, hA, hFinite, globalHeckeOrderReference_min F η ν ω μ S hS hω hν
    r C hC hN, hEq⟩

include μ hν in
theorem globalConverse_polarFree_range_of_min (ω : PontryaginDual (K F)) (r : GlobalBruhat F)
    (hr : ∀ z, meromorphicOrderAt (Zω F ν ω r) z ≠ ⊤)
    (hmin : ∀ f : GlobalBruhat F, ∀ z, meromorphicOrderAt (Zω F ν ω r) z ≤ meromorphicOrderAt (Zω F ν ω f) z) :
    ∀ b : B, b ∈ bergmanDivisorSubmodule (globalHeckeClearedZeta F ν ω r) ↔
      ∃ f : GlobalBruhat F, GlobalBruhat.polarEvaluation F f = 0 ∧ Zω F ν ω f = b.val := by
  obtain ⟨T, hT⟩ := globalHeckeDivisor_realized F ν η μ hν ω r
  intro b
  constructor
  · intro hb
    obtain ⟨f, hf, he⟩ := hT b hb
    exact ⟨f.val, hf, he⟩
  · rintro ⟨f, hf, he⟩
    have hp : globalZetaPolarVanishes F f (compactIdeleClassCharacter F ω) :=
      (globalZetaPolarVanishes_compact_iff F f ω).mpr
        (Or.inr ⟨congrArg Prod.fst hf, congrArg Prod.snd hf⟩)
    have hb : globalPoleFreeZetaBergman F ν ω f hp = b := Subtype.ext he
    exact hb ▸ globalPoleFreeZetaBergman_mem_divisor_of_min F ν ω r hr hmin f hp

include μ hν in
/-- For a nontrivial compact character the full homogeneous theta quotient
is the closed shifted divisor ideal, with its Schwartz–Bergman topology. -/
theorem exists_globalNontrivialMellin_shift_converse
    (ω : PontryaginDual (K F)) (hω : ω ≠ 1) (d : ℂ) :
    let H := globalIdelicZetaComponentKernel F η ω
    let E := GlobalBruhat F ⧸ H
    ∃ (S : Finset (HeightOneSpectrum (𝓞 F))) (hS : Surjective (sIdeleClassInclusion F S))
      (hu : globalNormOneCharacter F ω ∈ (sUnramified F S : Set (QuasiCharacter (IdeleClass F))))
      (r : GlobalBruhat F) (C : ℂ), C ≠ 0 ∧
      EqOn (Zω F ν ω r) (fun z ↦ C * globalCompletedHeckeEuler F ω S hS hu z) {z | 1 < z.re} ∧
      ∃ e : E ≃L[ℂ] bergmanDivisorSubmodule (fun z ↦ globalHeckeClearedZeta F ν ω r (z + d)),
        ∀ f : GlobalBruhat F, ∀ z : ℂ,
          (e (H.mkQ f)).val.val z = Zω F ν ω f (z+d) := by
  intro H E
  let P := (GlobalBruhat.polarEvaluation F).ker
  let X := P.map H.mkQ
  have htop : X = ⊤ := by
    have hk : globalIdelicZetaComponentKernel F η ω =
        (globalHomogeneousThetaOperator F ν ω).ker :=
      globalIdelicZetaComponentKernel_eq_homogeneous F ν η hν ω
    have ht := globalPolarFree_image_eq_top_of_ne_one F ν ω hω
    rw [← hk] at ht
    exact ht
  let j : X ≃ₗ[ℂ] E := (LinearEquiv.ofEq _ _ htop).trans Submodule.topEquiv
  let J : X ≃L[ℂ] E := ⟨j, continuous_subtype_val, continuous_id.subtype_mk _⟩
  obtain ⟨S, hS, hu, r, C, hC, hr, hmin, hEuler⟩ :=
    exists_globalConverse_eulerReference F ν η hν μ ω
  obtain ⟨a, ha⟩ := globalPolarFreeMellin_equiv_of_range F ν η hν ω r
    (globalConverse_polarFree_range_of_min F ν η hν μ ω r hr hmin)
  obtain ⟨b, hb⟩ := globalPolarFreeMellin_shift_equiv_of_equiv F ν η hν ω r a ha d
  refine ⟨S, hS, hu, r, C, hC, hEuler, J.symm.trans b, fun f z ↦ ?_⟩
  let x := J.symm (H.mkQ f)
  obtain ⟨g, hg, hgf⟩ := Submodule.mem_map.mp x.property
  have hq : H.mkQ g = H.mkQ f := hgf
  let g₀ : P := ⟨g, hg⟩
  have he : x = globalPolarFreeTestClass F η ω g₀ := Subtype.ext hgf.symm
  change (b x).val.val z = _
  rw [he, hb]
  exact congrFun (globalMellin_eq_of_mkQ_eq F η ω ν hν hq) (z+d)

include μ hν in
/-- A single minimal Hecke reference gives both the pole-free topological
equivalence and the exact meromorphic ideal in every shifted trivial chart. -/
theorem exists_globalTrivialMellin_shift_converse (d : ℂ) :
    let H := globalIdelicZetaComponentKernel F η (1 : PontryaginDual (K F))
    let P := (GlobalBruhat.polarEvaluation F).ker
    let X := P.map H.mkQ
    let M := globalRegularMellin F ν η hν 1 d
    ∃ (S : Finset (HeightOneSpectrum (𝓞 F))) (hS : Surjective (sIdeleClassInclusion F S))
      (hu : globalNormOneCharacter F (1 : PontryaginDual (K F)) ∈
        (sUnramified F S : Set (QuasiCharacter (IdeleClass F))))
      (r : GlobalBruhat F) (C : ℂ), C ≠ 0 ∧
      EqOn (Z F ν r) (fun z ↦ C * globalCompletedHeckeEuler F 1 S hS hu z) {z | 1 < z.re} ∧
      (∀ z, meromorphicOrderAt (Z F ν r) z ≠ ⊤) ∧
      (∀ f : GlobalBruhat F, ∀ z, meromorphicOrderAt (Z F ν r) z ≤ meromorphicOrderAt (Z F ν f) z) ∧
      let D := bergmanDivisorSubmodule (fun z ↦ G F ν r (z + d))
      (∃ e : X ≃L[ℂ] D, ∀ f : P, ∀ z : ℂ,
        (e (globalPolarFreeTestClass F η 1 f)).val.val z = Z F ν f.val (z + d)) ∧
      ∀ u : globalShiftedMellinRegularSet d → ℂ, u ∈ M.range ↔
        ∃ b : B, b ∈ D ∧ ∀ z : globalShiftedMellinRegularSet d,
          b.val z.val = (z.val + d) * (1 - z.val - d) * u z := by
  intro H P X M
  obtain ⟨S, hS, hu, r, C, hC, hr, hmin, hEuler⟩ :=
    exists_globalConverse_eulerReference F ν η hν μ 1
  have hPolar := globalConverse_polarFree_range_of_min F ν η hν μ 1 r hr hmin
  obtain ⟨e, he⟩ := globalPolarFreeMellin_equiv_of_range F ν η hν 1 r hPolar
  refine ⟨S, hS, hu, r, C, hC, hEuler, hr, hmin, globalPolarFreeMellin_shift_equiv_of_equiv F ν η hν 1 r e he d, ?_⟩
  exact globalTrivialMellin_regular_range_of_cleared_range F ν η hν r
    (globalTrivialClearedZeta_range_of_min F ν η hν r hr hmin (fun b ↦ (hPolar b).mp)) d

#print axioms schwartzBergman_of_periodic_mul
#print axioms globalTrivialClearedZeta_mem_schwartzBergman
#print axioms globalTrivialClearedZeta_range_of_min
#print axioms exists_globalNontrivialMellin_shift_converse
#print axioms exists_globalTrivialMellin_shift_converse
#print axioms globalZetaContinued_compact_twist
#print axioms globalConverse_shiftedMellin_eq_radial
#print axioms ideleUnitaryCharacter_existsUnique_compact_frequency

end

end Masullo
