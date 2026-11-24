import ModulatedSobolevTensor

open Filter Function MeasureTheory Set Topology UniformSpace
open scoped TensorProduct ENNReal

namespace Masullo

noncomputable section

variable {K : Type*} [MeasurableSpace K] (μ : Measure K) [SFinite μ]

/-- An isometric change of Hilbert factors induces the same change after completion. -/
def completionCongrIsometry {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] (e : E ≃ₗᵢ[ℂ] F) :
    Completion E ≃ₗᵢ[ℂ] Completion F :=
  completionLinearIsometryEquiv (Completion.toComplₗᵢ.comp e.toLinearIsometry)
    (Completion.denseRange_coe.comp e.surjective.denseRange (Completion.continuous_coe F))

theorem completionCongrIsometry_coe {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] (e : E ≃ₗᵢ[ℂ] F) (x : E) :
    completionCongrIsometry e (x : Completion E) = ((e x : F) : Completion F) :=
  completionLinearIsometryEquiv_coe _ _ x

/-- The Mellin transform on the weighted product is the scalar line transform
in the radial variable, tensored with the identity on the norm-one factor. -/
def modulatedMellinLineEquiv (b : ℝ) (N : ℕ) :
    Lp ℂ 2 (μ.prod (stripMeasure b b (2 * (N : ℝ)))) ≃ₗᵢ[ℂ]
      Completion (Lp ℂ 2 μ ⊗[ℂ] MellinLineCompletion b N) :=
  completedLpTwoTensorEquiv.symm.trans
    (completionCongrIsometry (TensorProduct.congrIsometry (.refl ℂ _) (mellinLineEquiv b N)))

theorem modulatedMellinLineEquiv_tmul (b : ℝ) (N : ℕ)
    (u : Lp ℂ 2 μ) (v : StripSobolev b b (2 * (N : ℝ))) :
    modulatedMellinLineEquiv μ b N (lpTwoProduct u v) =
      ((u ⊗ₜ[ℂ] mellinLineEquiv b N v : Lp ℂ 2 μ ⊗[ℂ] MellinLineCompletion b N) :
        Completion (Lp ℂ 2 μ ⊗[ℂ] MellinLineCompletion b N)) := by
  let P : Completion (Lp ℂ 2 μ ⊗[ℂ] StripSobolev b b (2 * (N : ℝ))) ≃ₗᵢ[ℂ]
      Lp ℂ 2 (μ.prod (stripMeasure b b (2 * (N : ℝ)))) := completedLpTwoTensorEquiv
  have hp : P ((u ⊗ₜ[ℂ] v : Lp ℂ 2 μ ⊗[ℂ] StripSobolev b b (2 * (N : ℝ))) :
      Completion (Lp ℂ 2 μ ⊗[ℂ] StripSobolev b b (2 * (N : ℝ)))) = lpTwoProduct u v :=
    completedLpTwoTensorEquiv_tmul u v
  rw [← hp]
  change completionCongrIsometry _ (P.symm (P _)) = _
  rw [LinearIsometryEquiv.symm_apply_apply]
  exact completionCongrIsometry_coe _ _

/-- On a radial cutoff, the same Mellin isometry identifies the tensor with
the supported scalar line completion. -/
def modulatedSupportedMellinEquiv (b : ℝ) (N : ℕ) {U : Set ℝ} (hU : IsOpen U) :
    lpTwoRadialSupport μ (stripMeasure b b (2 * (N : ℝ))) U ≃ₗᵢ[ℂ]
      Completion (Lp ℂ 2 μ ⊗[ℂ] supportedMellinLineCompletion b N U) :=
  (modulatedSupportedTensorEquiv μ b (2 * (N : ℝ)) hU).symm.trans
    (completionCongrIsometry
      (TensorProduct.congrIsometry (.refl ℂ _) (supportedMellinLineEquiv b N U)))

theorem modulatedSupportedMellinEquiv_tmul (b : ℝ) (N : ℕ) {U : Set ℝ} (hU : IsOpen U)
    (v : Lp ℂ 2 μ) (u : supportedSobolevCompletion b b (2 * (N : ℝ)) U) :
    let C := modulatedSupportedTensorEquiv μ b (2 * (N : ℝ)) hU
    modulatedSupportedMellinEquiv μ b N hU (C
      ((v ⊗ₜ[ℂ] u : Lp ℂ 2 μ ⊗[ℂ] supportedSobolevCompletion b b (2 * (N : ℝ)) U) :
        Completion (Lp ℂ 2 μ ⊗[ℂ] supportedSobolevCompletion b b (2 * (N : ℝ)) U))) =
      ((v ⊗ₜ[ℂ] supportedMellinLineEquiv b N U u :
        Lp ℂ 2 μ ⊗[ℂ] supportedMellinLineCompletion b N U) :
        Completion (Lp ℂ 2 μ ⊗[ℂ] supportedMellinLineCompletion b N U)) := by
  intro C
  change completionCongrIsometry _ (C.symm (C _)) = _
  rw [C.symm_apply_apply]
  exact completionCongrIsometry_coe _ _

section Character

variable [TopologicalSpace K] [BorelSpace K] [CommGroup K] [IsFiniteMeasure μ]

/-- The unique continuous functional on the actual supported Mellin-line tensor
whose pullback is the iterated character and logarithmic Mellin integral. -/
theorem modulatedSupportedMellin_evaluation (b : ℝ) (N : ℕ) {c : ℝ} (hc : c ≤ 0)
    {z : ℂ} (hz : z.re < b) (k : ℕ) (χ : PontryaginDual K) :
    let E := lpTwoRadialSupport μ (stripMeasure b b (2 * (N : ℝ))) (Ioi c)
    let H := Completion (Lp ℂ 2 μ ⊗[ℂ] supportedMellinLineCompletion b N (Ioi c))
    let M := modulatedSupportedMellinEquiv μ b N (U := Ioi c) isOpen_Ioi
    ∃! L : StrongDual ℂ H, ∀ u : E,
      let F x := (∫ j, (χ j : ℂ) * u.val (j, x) ∂μ) * mellinEvaluationKernel k z x
      Integrable F ∧ L (M u) = ∫ x, F x := by
  intro E H M
  obtain ⟨L, hL, _⟩ := modulatedSobolev_mellinMoment (μ := μ) b (2 * (N : ℝ))
    hc (by positivity) hz k χ
  let Q : StrongDual ℂ H := L.comp M.symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hQ (u : E) :
      let F x := (∫ j, (χ j : ℂ) * u.val (j, x) ∂μ) * mellinEvaluationKernel k z x
      Integrable F ∧ Q (M u) = ∫ x, F x := by
    refine ⟨(hL u).1, ?_⟩
    change L (M.symm (M u)) = _
    rw [M.symm_apply_apply]
    exact (hL u).2
  refine ⟨Q, hQ, fun P hP => ?_⟩
  ext v
  obtain ⟨u, rfl⟩ := M.surjective v
  exact (hP u).2.trans (hQ u).2.symm

/-- The character slice of a lower-cutoff modulated Mellin transform is the
sum of the positive Hardy part and the entire bounded-interval part. -/
theorem modulatedSobolev_hardy_decomposition (b : ℝ) (N : ℕ) {c : ℝ} (hc : c < 0)
    (χ : PontryaginDual K) (u : lpTwoRadialSupport μ (stripMeasure b b (2 * (N : ℝ))) (Ioi c)) :
    let v := modulatedSobolevCoefficient μ b (2 * (N : ℝ)) (U := Ioi c) isOpen_Ioi χ u
    let F := cutoffMellinIntegral v.val 0
    DifferentiableOn ℂ F (Complex.re ⁻¹' Iio b) ∧
    (∀ r < b, ∀ k ≤ N, MemLp (fun y : ℝ => iteratedDeriv k F (⟨r, y⟩ : ℂ)) 2 volume) ∧
    (∀ z : ℂ, z.re < b →
      F z = ∫ x : ℝ, (∫ j, (χ j : ℂ) * u.val (j, x) ∂μ) * Complex.exp (z * (x : ℂ))) ∧
    ∃ (uPos : supportedSobolevCompletion b b (2 * (N : ℝ)) (Ioi 0))
      (uBand : supportedSobolevCompletion b b (2 * (N : ℝ)) (Ioo c 0)),
      (uPos.val : ℝ → ℂ) =ᵐ[volume] (Ioi 0).indicator (v.val : ℝ → ℂ) ∧
      (uBand.val : ℝ → ℂ) =ᵐ[volume] (Ioo c 0).indicator (v.val : ℝ → ℂ) ∧
      let F₁ := cutoffMellinIntegral uPos.val 0
      let F₂ := cutoffMellinIntegral uBand.val 0
      DifferentiableOn ℂ F₁ (Complex.re ⁻¹' Iio b) ∧ UniformMellinLineBound (Iio b) N F₁ ∧
      Differentiable ℂ F₂ ∧ UniformMellinLineBound (Ioi b) N F₂ ∧
      (∃ C : ℝ, ∀ z : ℂ,
        ‖F₂ z‖ ≤ C * Real.sqrt (∫ x in Icc c 0, Real.exp (2 * z.re * x))) ∧
      (∀ z : ℂ, z.re < b → F z = F₁ z + F₂ z) := by
  intro v F
  obtain ⟨hD, hLp, hparts⟩ := cutoffMellinIntegral_hardy_decomposition hc v
  refine ⟨hD, hLp, fun z _ => ?_, hparts⟩
  unfold F cutoffMellinIntegral mellinEvaluationKernel
  apply integral_congr_ae
  filter_upwards [modulatedSobolevCoefficient_ae b (2 * (N : ℝ)) isOpen_Ioi χ u] with x hx
  rw [hx.2, pow_zero, mul_one]

/-- The holomorphic function represented by one character of the supported
Mellin tensor. -/
def modulatedMellinCharacter (b : ℝ) (N : ℕ) (c : ℝ) (χ : PontryaginDual K)
    (v : Completion (Lp ℂ 2 μ ⊗[ℂ] supportedMellinLineCompletion b N (Ioi c))) : ℂ → ℂ :=
  let u := (modulatedSupportedMellinEquiv μ b N (U := Ioi c) isOpen_Ioi).symm v
  let f := modulatedSobolevCoefficient μ b (2 * (N : ℝ)) (U := Ioi c) isOpen_Ioi χ u
  cutoffMellinIntegral f.val 0

/-- Corrected analytic decomposition in Corollary 9.2.1.6 on the full supported
Mellin tensor. The entire term uses the continuous bounded-interval growth factor. -/
theorem modulatedMellinCharacter_decomposition (b : ℝ) (N : ℕ) {c : ℝ} (hc : c < 0)
    (χ : PontryaginDual K)
    (v : Completion (Lp ℂ 2 μ ⊗[ℂ] supportedMellinLineCompletion b N (Ioi c))) :
    let F := modulatedMellinCharacter μ b N c χ v
    DifferentiableOn ℂ F (Complex.re ⁻¹' Iio b) ∧
    (∀ r < b, ∀ k ≤ N, MemLp (fun y : ℝ => iteratedDeriv k F (⟨r, y⟩ : ℂ)) 2 volume) ∧
    ∃ F₁ F₂ : ℂ → ℂ,
      DifferentiableOn ℂ F₁ (Complex.re ⁻¹' Iio b) ∧ UniformMellinLineBound (Iio b) N F₁ ∧
      Differentiable ℂ F₂ ∧ UniformMellinLineBound (Ioi b) N F₂ ∧
      (∃ C : ℝ, ∀ z : ℂ,
        ‖F₂ z‖ ≤ C * Real.sqrt (∫ x in Icc c 0, Real.exp (2 * z.re * x))) ∧
      (∀ z : ℂ, z.re < b → F z = F₁ z + F₂ z) := by
  intro F
  let u := (modulatedSupportedMellinEquiv μ b N (U := Ioi c) isOpen_Ioi).symm v
  obtain ⟨hD, hLp, _, uPos, uBand, _, _, hparts⟩ :=
    modulatedSobolev_hardy_decomposition μ b N hc χ u
  exact ⟨hD, hLp, cutoffMellinIntegral uPos.val 0, cutoffMellinIntegral uBand.val 0, hparts⟩

theorem modulatedMellinCharacter_iteratedDeriv (b : ℝ) (N : ℕ) {c : ℝ} (hc : c ≤ 0)
    {z : ℂ} (hz : z.re < b) (k : ℕ) (χ : PontryaginDual K)
    (u : lpTwoRadialSupport μ (stripMeasure b b (2 * (N : ℝ))) (Ioi c)) :
    let M := modulatedSupportedMellinEquiv μ b N (U := Ioi c) isOpen_Ioi
    iteratedDeriv k (modulatedMellinCharacter μ b N c χ (M u)) z =
      ∫ x : ℝ, (∫ j, (χ j : ℂ) * u.val (j, x) ∂μ) * mellinEvaluationKernel k z x := by
  intro M
  have hfu : modulatedMellinCharacter μ b N c χ (M u) =
      cutoffMellinIntegral (modulatedSobolevCoefficient μ b (2 * (N : ℝ)) isOpen_Ioi χ u).val 0 := by
    unfold modulatedMellinCharacter
    change cutoffMellinIntegral
      (modulatedSobolevCoefficient μ b (2 * (N : ℝ)) isOpen_Ioi χ (M.symm (M u))).val 0 = _
    rw [M.symm_apply_apply]
  rw [hfu, iteratedDeriv_cutoffMellinIntegral hc (by positivity) _ k hz]
  unfold cutoffMellinIntegral
  apply integral_congr_ae
  filter_upwards [modulatedSobolevCoefficient_ae b (2 * (N : ℝ)) isOpen_Ioi χ u] with x hx
  rw [hx.2]

end Character

end

end Masullo
