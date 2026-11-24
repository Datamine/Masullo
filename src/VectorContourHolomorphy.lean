import ComplexContours

/-!
The weak contour criteria of Appendix C. Adapted from Apache-2.0
RiemannMasullo commit 4f78774 using the local weak Pettis integral.
-/

open Filter Function Set Topology

namespace Masullo

noncomputable section

variable {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
variable {U : Set ℂ} {f : ℂ → E}

/-- Theorem C.5.2.4(1–2). A weakly continuous function is weakly holomorphic
exactly when its weak contour integrals vanish. -/
theorem weaklyHolomorphicOn_iff_contourIntegral_eq_zero (hU : IsOpen U) :
    (∀ ℓ : StrongDual ℂ E, DifferentiableOn ℂ (ℓ ∘ f) U) ↔
      (∀ ℓ : StrongDual ℂ E, ContinuousOn (ℓ ∘ f) U) ∧
      ∀ γ : PositiveSimpleContour, γ.val.trace ⊆ U → γ.interior ⊆ U →
        ∃ h : ∀ ℓ : StrongDual ℂ E, γ.val.measure.Integrable (ℓ ∘ f),
          weakPettisIntegral γ.val.measure f h = 0 := by
  constructor
  · intro hf
    have hc (ℓ : StrongDual ℂ E) := (hf ℓ).continuousOn
    refine ⟨hc, fun γ htr hint ↦ ?_⟩
    have hscalar (ℓ : StrongDual ℂ E) :=
      γ.val.scalarIntegral_eq_intervalIntegral ((hc ℓ).mono htr)
    refine ⟨fun ℓ ↦ (hscalar ℓ).1, LinearMap.ext fun ℓ ↦ ?_⟩
    change complexMeasureIntegral γ.val.measure (ℓ ∘ f) = 0
    have hindex (z : ℂ) (hz : z ∉ U) : γ.val.index z = 0 := by
      have hzt : z ∉ γ.val.trace := fun h ↦ hz (htr h)
      exact (γ.property.2 z hzt).resolve_right fun h ↦ hz (hint ⟨hzt, h⟩)
    simpa using sum_scalarIntegral_eq_zero ({γ} : Finset PositiveSimpleContour) id
      (fun _ ↦ 1) hU (by simpa using htr) (by simpa using hindex) (hf ℓ)
  · rintro ⟨hc, hzero⟩ ℓ
    apply differentiableOn_of_scalarIntegral_eq_zero hU (hc ℓ)
    intro γ htr hint
    obtain ⟨_, he⟩ := hzero γ htr hint
    exact congrArg (fun D : Module.Dual ℂ (StrongDual ℂ E) ↦ D ℓ) he

/-- Theorem C.5.2.4(1,3). The weak Cauchy formula is equivalent to weak
holomorphy for a weakly continuous function. Its values are in the algebraic
dual of the continuous dual. -/
theorem weaklyHolomorphicOn_iff_weak_cauchyIntegral (hU : IsOpen U) :
    (∀ ℓ : StrongDual ℂ E, DifferentiableOn ℂ (ℓ ∘ f) U) ↔
      (∀ ℓ : StrongDual ℂ E, ContinuousOn (ℓ ∘ f) U) ∧
      ∀ γ : PositiveSimpleContour, γ.val.trace ⊆ U → γ.interior ⊆ U →
        ∀ z ∈ γ.interior, ∃ h : ∀ ℓ : StrongDual ℂ E,
          γ.val.measure.Integrable (ℓ ∘ fun w ↦ (w - z)⁻¹ • f w),
          (weakBidualEval E (f z) : Module.Dual ℂ (StrongDual ℂ E)) =
            (2 * (Real.pi : ℂ) * Complex.I)⁻¹ •
              weakPettisIntegral γ.val.measure (fun w ↦ (w - z)⁻¹ • f w) h := by
  constructor
  · intro hf
    refine ⟨fun ℓ ↦ (hf ℓ).continuousOn, ?_⟩
    intro γ htr hint z hz
    have hi (ℓ : StrongDual ℂ E) :
        γ.val.measure.Integrable (ℓ ∘ fun w ↦ (w - z)⁻¹ • f w) := by
      simp only [Function.comp_def, map_smul, smul_eq_mul]
      exact (γ.val.scalarIntegral_eq_intervalIntegral
        ((γ.val.continuousOn_inv_sub hz.1).mul ((hf ℓ).continuousOn.mono htr))).1
    refine ⟨hi, LinearMap.ext fun ℓ ↦ ?_⟩
    change ℓ (f z) = _ * complexMeasureIntegral γ.val.measure
      (fun w ↦ ℓ ((w - z)⁻¹ • f w))
    simp only [map_smul, smul_eq_mul]
    exact γ.scalar_cauchy hU htr hint (hf ℓ) hz
  · rintro ⟨hc, hformula⟩ ℓ x hx
    obtain ⟨γ, htr, hint, hnb⟩ := exists_positiveSimpleContour_mem_nhds hU hx
    have hxtr : x ∉ γ.val.trace := (mem_of_mem_nhds hnb).1
    have hd := (γ.val.differentiableOn_cauchyTransform ((hc ℓ).mono htr)).differentiableAt
      ((isCompact_Icc.image γ.val.toContinuousMap.continuous).isClosed.isOpen_compl.mem_nhds hxtr)
    apply DifferentiableAt.differentiableWithinAt
    apply (hd.const_mul (2 * (Real.pi : ℂ) * Complex.I)⁻¹).congr_of_eventuallyEq
    filter_upwards [hnb] with z hz
    obtain ⟨_, he⟩ := hformula γ htr hint z hz
    have he' := congrArg (fun D : Module.Dual ℂ (StrongDual ℂ E) ↦ D ℓ) he
    change ℓ (f z) = _ * complexMeasureIntegral γ.val.measure
      (fun w ↦ ℓ ((w - z)⁻¹ • f w)) at he'
    simpa only [map_smul, smul_eq_mul, Function.comp_apply] using he'

end

end Masullo
