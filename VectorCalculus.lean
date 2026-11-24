import PettisBounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open Filter MeasureTheory Set
open scoped Topology

namespace Masullo

section VectorChainRule

variable {𝕜 V W E : Type*} [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 ℂ]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [NormedAddCommGroup W] [NormedSpace 𝕜 W]
  [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]

/-- C.5.1.17(1). Weak differentiability is preserved by precomposition
with a differentiable map of the domains. -/
theorem weaklyDifferentiableOn_comp {U : Set V} {S : Set W}
    {f : W → E} {φ : V → W} (hφS : MapsTo φ U S) (hφ : DifferentiableOn 𝕜 φ U)
    (hf : ∀ ℓ : StrongDual ℂ E, DifferentiableOn 𝕜 (ℓ ∘ f) S) :
    ∀ ℓ : StrongDual ℂ E, DifferentiableOn 𝕜 (ℓ ∘ (f ∘ φ)) U :=
  fun ℓ => (hf ℓ).comp hφ hφS

/-- Corrected C.5.1.17(2). The chain rule gives a continuous vector
differential when the inner map has a continuous differential. -/
theorem continuousVectorDifferential_comp {U : Set V} {S : Set W}
    (f : W → E) (φ : V → W) (A : W → W → E) (B : V → V →L[𝕜] W)
    (D : StrongDual ℂ E → W → W →L[𝕜] ℂ)
    (hφS : MapsTo φ U S) (hφ : ∀ x ∈ U, HasFDerivAt φ (B x) x)
    (hB : ContinuousOn (fun p : V × V => B p.1 p.2) (U ×ˢ univ))
    (hA : ContinuousOn (fun p : W × W => A p.1 p.2) (S ×ˢ univ))
    (hD : ∀ ℓ : StrongDual ℂ E, ∀ x ∈ S, HasFDerivAt (ℓ ∘ f) (D ℓ x) x)
    (hAD : ∀ (ℓ : StrongDual ℂ E) (x : W), x ∈ S → ∀ w, D ℓ x w = ℓ (A x w)) :
    ContinuousOn (fun p : V × V => A (φ p.1) (B p.1 p.2)) (U ×ˢ univ) ∧
      ∀ (ℓ : StrongDual ℂ E) (x : V), x ∈ U →
        HasFDerivAt (ℓ ∘ (f ∘ φ)) ((D ℓ (φ x)).comp (B x)) x ∧
        ∀ v, ((D ℓ (φ x)).comp (B x)) v = ℓ (A (φ x) (B x v)) := by
  have hφc : ContinuousOn φ U := fun x hx => (hφ x hx).continuousAt.continuousWithinAt
  refine ⟨hA.comp ((hφc.comp continuous_fst.continuousOn (fun p hp => hp.1)).prodMk hB)
    (fun p hp => ⟨hφS hp.1, mem_univ _⟩), ?_⟩
  intro ℓ x hx
  exact ⟨(hD ℓ _ (hφS hx)).comp x (hφ x hx), fun v => hAD ℓ _ (hφS hx) (B x v)⟩

end VectorChainRule

section FundamentalTheorem

variable {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]

/-- Corrected C.5.1.19. The path has a continuous derivative on the interval.
Scalar evaluations identify the differential, give the chain rule, and
prove that the interval integral is represented by the endpoint difference. -/
theorem pettis_fundamentalTheorem_alongPath
    {a b : ℝ} (hab : a ≤ b) {U : Set V} (f : V → E) (A : V → V → E)
    (γ γ' : ℝ → V) (hpath : MapsTo γ (Icc a b) U)
    (hγ : ∀ t ∈ Icc a b, HasDerivAt γ (γ' t) t) (hγ' : ContinuousOn γ' (Icc a b))
    (hA : ContinuousOn (fun p : V × V => A p.1 p.2) (U ×ˢ univ))
    (D : (E →L[ℂ] ℂ) → V → V →L[ℝ] ℂ)
    (hD : ∀ ℓ : E →L[ℂ] ℂ, ∀ x ∈ U, HasFDerivAt (ℓ ∘ f) (D ℓ x) x)
    (hAD : ∀ (ℓ : E →L[ℂ] ℂ) (x : V), x ∈ U → ∀ v, D ℓ x v = ℓ (A x v)) :
    ContinuousOn (fun t => A (γ t) (γ' t)) (Icc a b) ∧
    HasPositivePettisIntegral (volume.restrict (Icc a b))
      (fun t => A (γ t) (γ' t)) (f (γ b) - f (γ a)) := by
  have hcont : ContinuousOn (fun t => A (γ t) (γ' t)) (Icc a b) :=
    hA.comp ((HasDerivAt.continuousOn hγ).prodMk hγ') (fun t ht => ⟨hpath ht, mem_univ _⟩)
  refine ⟨hcont, fun ℓ => ?_⟩
  have hc : ContinuousOn (fun t => ℓ (A (γ t) (γ' t))) (Icc a b) :=
    ℓ.continuous.comp_continuousOn hcont
  have hi := hc.intervalIntegrable_of_Icc (μ := volume) hab
  refine ⟨(intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp hi, ?_⟩
  have hderiv (t : ℝ) (ht : t ∈ Icc a b) :
      HasDerivAt ((ℓ ∘ f) ∘ γ) (ℓ (A (γ t) (γ' t))) t := by
    rw [← hAD ℓ _ (hpath ht)]
    exact (hD ℓ _ (hpath ht)).comp_hasDerivAt t (hγ t ht)
  have hderiv' (t : ℝ) (ht : t ∈ uIcc a b) :
      HasDerivAt ((ℓ ∘ f) ∘ γ) (ℓ (A (γ t) (γ' t))) t :=
    hderiv t (uIcc_of_le hab ▸ ht)
  rw [map_sub, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
  exact (intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv' hi).symm

end FundamentalTheorem

/-- A once-differentiable path in one real coordinate need not have a
continuous derivative on the interval in C.5.1.19. -/
theorem pettis_path_derivative_obstruction :
    let γ : ℝ → ℝ := fun t => t ^ 2 * Real.sin t⁻¹
    Differentiable ℝ γ ∧ ¬ ContinuousOn (deriv γ) (Icc (-1) 1) := by
  let γ : ℝ → ℝ := fun t => t ^ 2 * Real.sin t⁻¹
  change Differentiable ℝ γ ∧ ¬ ContinuousOn (deriv γ) (Icc (-1) 1)
  have hzero : HasDerivAt γ 0 0 := by
    apply hasDerivAt_iff_tendsto_slope.mpr
    have hb : Tendsto (fun t : ℝ => ‖t‖) (𝓝[≠] 0) (𝓝 0) := by
      have hc : ContinuousAt (fun t : ℝ => ‖t‖) 0 := continuous_norm.continuousAt
      simpa only [norm_zero] using hc.tendsto.mono_left
        (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℝ) ≤ 𝓝 0)
    refine squeeze_zero_norm' ?_ hb
    have hev : ∀ᶠ t : ℝ in 𝓝[≠] 0, t ≠ 0 := self_mem_nhdsWithin
    filter_upwards [hev] with t ht'
    have he : slope γ 0 t = t * Real.sin t⁻¹ := by
      simp [slope_def_field, γ]
      field_simp
    rw [he, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (Real.abs_sin_le_one _)
  have hd (t : ℝ) (ht : t ≠ 0) :
      HasDerivAt γ (2 * t * Real.sin t⁻¹ - Real.cos t⁻¹) t := by
    have hsin := (Real.hasDerivAt_sin t⁻¹).comp t (hasDerivAt_inv ht)
    have hp := ((hasDerivAt_id' t).pow 2).mul hsin
    have he : 2 * t * Real.sin t⁻¹ - Real.cos t⁻¹ =
        2 * t ^ (2 - 1 : ℕ) * 1 * Real.sin t⁻¹ + t ^ 2 * (Real.cos t⁻¹ * -(t ^ 2)⁻¹) := by
      norm_num
      field_simp
      ring
    rw [he]
    exact hp
  refine ⟨fun t => ?_, fun hcont => ?_⟩
  · by_cases ht : t = 0
    · exact ht ▸ hzero.differentiableAt
    · exact (hd t ht).differentiableAt
  · let s (n : ℕ) := (((n + 1 : ℕ) : ℝ) * (2 * Real.pi))⁻¹
    have hs : Tendsto s atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp <| (tendsto_natCast_atTop_atTop.comp
        (tendsto_add_atTop_nat 1)).atTop_mul_const (by positivity)
    have hsm : ∀ᶠ n in atTop, s n ∈ Icc (-1 : ℝ) 1 :=
      hs (Icc_mem_nhds (by norm_num) (by norm_num))
    have hsz : Tendsto s atTop (𝓝[Icc (-1 : ℝ) 1] 0) :=
      tendsto_nhdsWithin_iff.mpr ⟨hs, hsm⟩
    have hd0 : Tendsto (fun n => deriv γ (s n)) atTop (𝓝 0) := by
      have h := (hcont 0 (show (0 : ℝ) ∈ Icc (-1) 1 by norm_num)).tendsto.comp hsz
      rwa [hzero.deriv] at h
    have he (n : ℕ) : deriv γ (s n) = -1 := by
      rw [(hd _ (by dsimp [s]; positivity)).deriv]
      have hh : Real.sin (((n + 1 : ℕ) : ℝ) * (2 * Real.pi)) = 0 := by
        simpa using Real.sin_nat_mul_two_pi_sub 0 (n + 1)
      simp only [s, inv_inv, hh, Real.cos_nat_mul_two_pi, mul_zero, zero_sub]
    exact (by norm_num : (0 : ℝ) ≠ -1) <|
      tendsto_nhds_unique hd0 (tendsto_const_nhds.congr fun n => (he n).symm)

end Masullo
