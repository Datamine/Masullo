import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Topology.Algebra.InfiniteSum.Group

open Filter MeasureTheory Set Topology
open scoped Classical ENat ContDiff

namespace Masullo

/-- The critical-strip assertion for a family of continued L-functions. -/
def CriticalStripGRH {Character : Type*} (L : Character → ℂ → ℂ) : Prop :=
  ∀ χ z, L χ z = 0 → 0 < z.re → z.re < 1 → z.re = 1 / 2

/-- Mathlib's continued Dirichlet L-functions give a concrete formulation over ℚ. -/
def DirichletGRH : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
    ∀ z : ℂ, χ.LFunction z = 0 → 0 < z.re → z.re < 1 → z.re = 1 / 2

/-- A norm-variable test, smooth and compactly supported away from zero.
This describes the positive-real factor in the character-by-character calculation. -/
structure NormTest where
  toFun : ℝ → ℂ
  smooth : ContDiff ℝ ∞ toFun
  compact : HasCompactSupport toFun
  support_positive : tsupport toFun ⊆ Ioi 0

noncomputable def NormTest.shiftedMellin (φ : NormTest) (z : ℂ) : ℂ :=
  mellin φ.toFun (z - 1 / 2)

/-- The norm-variable version of the admissibility condition in Chapter 12. -/
def NormTest.vanishesOnNormOne (φ : NormTest) : Prop := φ.toFun 1 = 0

/-- The Mellin-jet condition in Chapter 13, with the center expressed
in the chosen character coordinate. -/
def NormTest.vanishingMellinJet (φ : NormTest) (degree : ℕ) (center : ℂ) : Prop :=
  ∀ k < degree, iteratedDeriv k (mellin φ.toFun) center = 0

/-- Over the trivial character, vanishing on the norm-one subgroup does
not imply the first Mellin-jet condition in Chapter 13. -/
theorem normOne_vanishing_not_mellin_jet :
    ∃ φ : NormTest, φ.vanishesOnNormOne ∧ ¬φ.vanishingMellinJet 1 0 := by
  let f (x : ℝ) := Real.smoothTransition (x - 2) * Real.smoothTransition (5 - x)
  have hsmooth : ContDiff ℝ ∞ f := by
    have h₁ : ContDiff ℝ ∞ (fun x : ℝ => x - 2) := by fun_prop
    have h₂ : ContDiff ℝ ∞ (fun x : ℝ => 5 - x) := by fun_prop
    exact (Real.smoothTransition.contDiff.comp h₁).mul (Real.smoothTransition.contDiff.comp h₂)
  have hl (x : ℝ) (hx : x ≤ 2) : f x = 0 := by
    simp [f, Real.smoothTransition.zero_of_nonpos (sub_nonpos.mpr hx)]
  have hr (x : ℝ) (hx : 5 ≤ x) : f x = 0 := by
    simp [f, Real.smoothTransition.zero_of_nonpos (sub_nonpos.mpr hx)]
  have hsupp : tsupport (fun x => (f x : ℂ)) ⊆ Icc 2 5 := by
    apply closure_minimal _ isClosed_Icc
    intro x hx
    by_contra h
    have hf : f x = 0 := by
      rcases le_or_gt x 2 with hx' | hx'
      · exact hl x hx'
      · exact hr x (le_of_lt (lt_of_not_ge (fun hu => h ⟨hx'.le, hu⟩)))
    exact hx (by simp [hf])
  let φ : NormTest :=
    { toFun := fun x => (f x : ℂ)
      smooth := Complex.ofRealCLM.contDiff.comp hsmooth
      compact := isCompact_Icc.of_isClosed_subset isClosed_closure hsupp
      support_positive := fun _ hx => zero_lt_two.trans_le (hsupp hx).1 }
  refine ⟨φ, ?_, ?_⟩
  · change (f 1 : ℂ) = 0
    simp [hl 1 (by norm_num)]
  · intro hjet
    have hval := hjet 0 zero_lt_one
    rw [iteratedDeriv_zero] at hval
    let p (x : ℝ) := x⁻¹ * f x
    have hp : Continuous p := by
      apply continuous_iff_continuousAt.mpr
      intro x
      by_cases hx : x = 0
      · subst x
        have he : p =ᶠ[𝓝 (0 : ℝ)] fun _ => 0 := by
          filter_upwards [gt_mem_nhds (show (0 : ℝ) < 2 by norm_num)] with x hx
          simp [p, hl x hx.le]
        exact he.continuousAt
      · exact (continuousAt_inv₀ hx).mul hsmooth.continuous.continuousAt
    have hps : tsupport p ⊆ Icc (2 : ℝ) 5 := by
      apply closure_minimal _ isClosed_Icc
      intro x hx
      by_contra h
      have hf : f x = 0 := by
        rcases le_or_gt x 2 with h₁ | h₁
        · exact hl x h₁
        · exact hr x (le_of_lt (lt_of_not_ge (fun h₂ => h ⟨h₁.le, h₂⟩)))
      exact hx (by simp [p, hf])
    have hpcompact : HasCompactSupport p :=
      isCompact_Icc.of_isClosed_subset isClosed_closure hps
    let μ := volume.restrict (Ioi (0 : ℝ))
    have hpi : Integrable p μ := (hp.integrable_of_hasCompactSupport hpcompact).integrableOn
    have hpos : 0 ≤ᵐ[μ] p := by
      filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with x hx
      exact mul_nonneg (inv_nonneg.mpr hx.le) (mul_nonneg
        (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _))
    have hpositive : 0 < ∫ x, p x ∂μ := by
      apply (integral_pos_iff_support_of_nonneg_ae hpos hpi).mpr
      have hsubset : Ioo (3 : ℝ) 4 ⊆ Function.support p := by
        intro x hx
        have he : f x = 1 := by
          simp [f, Real.smoothTransition.one_of_one_le (by linarith [hx.1] : 1 ≤ x - 2),
            Real.smoothTransition.one_of_one_le (by linarith [hx.2] : 1 ≤ 5 - x)]
        exact mul_ne_zero (inv_ne_zero (by linarith [hx.1])) (he ▸ one_ne_zero)
      have hvol : 0 < μ (Ioo 3 4) := by
        change 0 < volume.restrict (Ioi (0 : ℝ)) (Ioo 3 4)
        rw [Measure.restrict_apply measurableSet_Ioo, inter_eq_left.mpr (by
          intro x hx
          exact zero_lt_three.trans hx.1)]
        rw [Real.volume_Ioo]
        norm_num
      exact hvol.trans_le (measure_mono hsubset)
    have he : mellin φ.toFun 0 = ((∫ x, p x ∂μ : ℝ) : ℂ) := by
      unfold mellin
      simp only [zero_sub, Complex.cpow_neg_one, smul_eq_mul]
      change (∫ x, (x : ℂ)⁻¹ * (f x : ℂ) ∂μ) = _
      simp_rw [← Complex.ofReal_inv, ← Complex.ofReal_mul]
      exact integral_complex_ofReal
    exact (Complex.ofReal_ne_zero.mpr hpositive.ne') (he.symm.trans hval)

/-- Multiplicity of an isolated zero of an analytic representative of an L-function. -/
noncomputable def zeroMultiplicity (L : ℂ → ℂ) (z : ℂ) : ℕ :=
  (analyticOrderAt L z).toNat

/-- Spectral data for one character component. The transform includes the Mellin
shift and Haar normalization. The geometric side combines pole and local terms. -/
structure TraceData (Test : Type*) where
  L : ℂ → ℂ
  transform : Test → ℂ → ℂ
  geometricSide : Test → ℂ

abbrev TraceData.Zero {Test : Type*} (D : TraceData Test) := {z : ℂ // D.L z = 0}

def centeredStrip (a : ℝ) (z : ℂ) : Prop := |z.re - 1 / 2| < a

def onCriticalLine (z : ℂ) : Prop := z.re = 1 / 2

noncomputable def TraceData.spectralTerm {Test : Type*} (D : TraceData Test)
    (weight : D.Zero → ℕ) (region : ℂ → Prop) (φ : Test) (z : D.Zero) : ℂ := by
  classical
  exact if region z.val then (weight z : ℂ) * D.transform φ z.val else 0

/-- One-character spectral identity. HasSum makes convergence part of the assertion. -/
def TraceIdentity {Test : Type*} (D : TraceData Test) (admissible : Test → Prop)
    (weight : D.Zero → ℕ) (region : ℂ → Prop) : Prop :=
  ∀ φ, admissible φ → HasSum (D.spectralTerm weight region φ) (D.geometricSide φ)

/-- Equation (12.5.1.3), with full multiplicities and a specified open strip. -/
def Chapter12Trace {Test : Type*} (D : TraceData Test) (admissible : Test → Prop)
    (a : ℝ) : Prop :=
  TraceIdentity D admissible (fun z => zeroMultiplicity D.L z.val) (centeredStrip a)

/-- Equations (13.3.1.3)–(13.3.1.5), as printed with clipped multiplicities. -/
def Chapter13Trace {Test : Type*} (D : TraceData Test) (admissible : Test → Prop)
    (degree : ℕ) : Prop :=
  TraceIdentity D admissible (fun z => min (zeroMultiplicity D.L z.val) degree) onCriticalLine

/-- The Appendix B zero sum, with the convention for repeated zeros made explicit. -/
def FullExplicitFormula {Test : Type*} (D : TraceData Test) (weight : D.Zero → ℕ) : Prop :=
  TraceIdentity D (fun _ => True) weight (fun _ => True)

/-- Comparing two identities on common tests gives vanishing of their difference. -/
theorem compare_traces {Test : Type*} (D : TraceData Test)
    {admissible₁ admissible₂ : Test → Prop} {weight₁ weight₂ : D.Zero → ℕ}
    {region₁ region₂ : ℂ → Prop}
    (h₁ : TraceIdentity D admissible₁ weight₁ region₁)
    (h₂ : TraceIdentity D admissible₂ weight₂ region₂)
    {φ : Test} (hφ₁ : admissible₁ φ) (hφ₂ : admissible₂ φ) :
    HasSum (fun z => D.spectralTerm weight₁ region₁ φ z -
      D.spectralTerm weight₂ region₂ φ z) 0 := by
  simpa using (h₁ φ hφ₁).sub (h₂ φ hφ₂)

/-- Injectivity of the spectral transform on the admissible tests would identify
the divisors. This hypothesis concerns the actual test space and infinite sums. -/
theorem identify_divisors {Test : Type*} (D : TraceData Test) {admissible : Test → Prop}
    {weight₁ weight₂ : D.Zero → ℕ} {region₁ region₂ : ℂ → Prop}
    (h₁ : TraceIdentity D admissible weight₁ region₁)
    (h₂ : TraceIdentity D admissible weight₂ region₂)
    (separates : ∀ z : D.Zero,
      (∀ φ, admissible φ → HasSum (fun w => D.spectralTerm weight₁ region₁ φ w -
        D.spectralTerm weight₂ region₂ φ w) 0) →
      (if region₁ z.val then weight₁ z else 0) = (if region₂ z.val then weight₂ z else 0)) :
    ∀ z : D.Zero,
      (if region₁ z.val then weight₁ z else 0) = (if region₂ z.val then weight₂ z else 0) := by
  classical
  exact fun z => separates z (fun _ hφ => compare_traces D h₁ h₂ hφ hφ)

/-- Zero exclusion on each shifted half-plane gives zero exclusion to the right
of the critical line. Reflection may change the character. -/
theorem grh_of_right_half_planes {Character : Type*} {L : Character → ℂ → ℂ}
    (dual : Character → Character)
    (reflect : ∀ χ z, L χ z = 0 → 0 < z.re → z.re < 1 → L (dual χ) (1 - z) = 0)
    (right : ∀ a : ℝ, 0 < a → ∀ χ z, 1 / 2 + a < z.re → z.re < 1 → L χ z ≠ 0) :
    CriticalStripGRH L := by
  intro χ z hz h₀ h₁
  by_contra h
  rcases lt_or_gt_of_ne h with hleft | hright
  · have hre : (1 - z).re = 1 - z.re := by simp
    have ha : 0 < (1 / 2 - z.re) / 2 := by linarith
    exact right _ ha (dual χ) (1 - z) (by linarith) (by linarith) (reflect χ z hz h₀ h₁)
  · have ha : 0 < (z.re - 1 / 2) / 2 := by linarith
    exact right _ ha χ z (by linarith) h₁ hz

/-- The reflection required above follows from Mathlib's functional equation for
primitive Dirichlet characters. The gamma factor is nonzero in the open strip. -/
theorem dirichlet_zero_reflection {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) {z : ℂ} (hz : χ.LFunction z = 0)
    (h₀ : 0 < z.re) (h₁ : z.re < 1) : (χ⁻¹).LFunction (1 - z) = 0 := by
  have hz₀ : z ≠ 0 := by
    intro h
    simp [h] at h₀
  have hr : 0 < (1 - z).re := by simp; linarith
  have hr₀ : 1 - z ≠ 0 := by
    intro h
    simp [h] at hr
  have hγ : DirichletCharacter.gammaFactor χ z ≠ 0 := by
    rcases χ.even_or_odd with h | h
    · rw [h.gammaFactor_def]
      exact Complex.Gammaℝ_ne_zero_of_re_pos h₀
    · rw [h.gammaFactor_def]
      apply Complex.Gammaℝ_ne_zero_of_re_pos
      simp
      linarith
  have hcompleted : χ.completedLFunction z = 0 := by
    rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ z (.inl hz₀),
      div_eq_zero_iff] at hz
    exact hz.resolve_right hγ
  have hinv : (χ⁻¹).IsPrimitive := by
    simpa only [DirichletCharacter.IsPrimitive, DirichletCharacter.conductor_inv] using hχ
  rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor _ _ (.inl hr₀),
    hinv.completedLFunction_one_sub, inv_inv, hcompleted, mul_zero, zero_div]

/-- Over ℚ, the remaining zero-location step can be expressed as right-half-plane
exclusion for primitive characters, with the reflection discharged. -/
theorem dirichletGRH_of_right_half_planes
    (right : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
      ∀ a : ℝ, 0 < a → ∀ z : ℂ, 1 / 2 + a < z.re → z.re < 1 → χ.LFunction z ≠ 0) :
    DirichletGRH := by
  intro q hq χ hχ z hz h₀ h₁
  let Primitive := {ψ : DirichletCharacter ℂ q // ψ.IsPrimitive}
  let dual (ψ : Primitive) : Primitive :=
    ⟨ψ.val⁻¹, by
      simpa only [DirichletCharacter.IsPrimitive, DirichletCharacter.conductor_inv] using ψ.property⟩
  exact grh_of_right_half_planes (L := fun ψ : Primitive => ψ.val.LFunction) dual
    (fun ψ _ => dirichlet_zero_reflection ψ.property)
    (fun a ha ψ => right q ψ.val ψ.property a ha) ⟨χ, hχ⟩ z hz h₀ h₁

/-- A logarithmic derivative has a simple pole at a zero of finite positive order.
A regularized continuation holomorphic there would contradict this local identity. -/
theorem log_derivative_order_at_zero {L : ℂ → ℂ} {z : ℂ} {n : ℕ}
    (hL : AnalyticAt ℂ L z) (horder : analyticOrderAt L z = n + 1) :
    meromorphicOrderAt (fun w => deriv L w / L w) z = (-1 : ℤ) := by
  change meromorphicOrderAt (deriv L / L) z = _
  rw [meromorphicOrderAt_div hL.deriv.meromorphicAt hL.meromorphicAt,
      hL.deriv.meromorphicOrderAt_eq, hL.meromorphicOrderAt_eq,
      analyticOrderAt_deriv_of_pos hL horder, horder]
  have hn : (n : ℕ∞) + 1 = ((n + 1 : ℕ) : ℕ∞) := by simp
  rw [hn]
  simp only [ENat.map_natCast]
  change ((n : ℤ) : WithTop ℤ) - ((↑(n + 1) : ℤ) : WithTop ℤ) = (-1 : ℤ)
  change (((n : ℤ) - (↑(n + 1) : ℤ) : ℤ) : WithTop ℤ) = (-1 : ℤ)
  rw [WithTop.coe_eq_coe]
  omega

theorem no_holomorphic_log_derivative_at_zero {L G : ℂ → ℂ} {z : ℂ} {n : ℕ}
    (hL : AnalyticAt ℂ L z) (horder : analyticOrderAt L z = n + 1)
    (agree : (fun w => deriv L w / L w) =ᶠ[𝓝[≠] z] G) :
    ¬ AnalyticAt ℂ G z := by
  intro hG
  have h := hG.meromorphicOrderAt_nonneg
  rw [← meromorphicOrderAt_congr agree, log_derivative_order_at_zero hL horder] at h
  exact (show ¬ (0 : WithTop ℤ) ≤ (-1 : ℤ) from by decide) h

/-- The interior of the degenerate strip is empty. An on-line spectral sum
requires a different limiting or projection statement. -/
theorem degenerate_open_strip (z : ℂ) : ¬ centeredStrip 0 z :=
  not_lt.mpr (abs_nonneg _)

/-- A literal zero-width reading of Chapter 12 makes its geometric side vanish
on every admitted test. -/
theorem geometric_zero_of_degenerate_trace {Test : Type*} (D : TraceData Test)
    {admissible : Test → Prop} (h : Chapter12Trace D admissible 0)
    {φ : Test} (hφ : admissible φ) :
    D.geometricSide φ = 0 := by
  have hs := h φ hφ
  change HasSum (D.spectralTerm _ (centeredStrip 0) φ) _ at hs
  have hterm : D.spectralTerm (fun z => zeroMultiplicity D.L z.val)
      (centeredStrip 0) φ = fun _ => 0 := by
    funext z
    simp [TraceData.spectralTerm, degenerate_open_strip]
  rw [hterm] at hs
  exact hs.unique hasSum_zero

end Masullo
