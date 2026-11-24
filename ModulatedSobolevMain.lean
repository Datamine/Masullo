import ModulatedSobolevProfileCompletion
import ModulatedSobolevSequence

open Filter Function MeasureTheory Set Topology UniformSpace
open scoped ENNReal SchwartzMap TensorProduct

namespace Masullo

noncomputable section

private def hilbertTmul {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    [InnerProductSpace ℂ E] [InnerProductSpace ℂ F] (u : E) (v : F) :
    Completion (E ⊗[ℂ] F) := (u ⊗ₜ[ℂ] v : E ⊗[ℂ] F)

private def supportedScalarLineEmbedding (b : ℝ) (N : ℕ) (U : Set ℝ) :
    supportedMellinLineCompletion b N U →ₗᵢ[ℂ] MellinLineCompletion b N :=
  (mellinLineEquiv b N).toLinearIsometry.comp
    (((supportedSobolevCompletion b b (2 * (N : ℝ)) U).subtypeₗᵢ).comp
      (supportedMellinLineEquiv b N U).symm.toLinearIsometry)

variable {K : Type*} [MeasurableSpace K] (μ : Measure K) [SFinite μ]

/-- The supported Mellin tensor embeds isometrically in the full tensor. -/
def modulatedSupportedMellinEmbedding (b : ℝ) (N : ℕ) {U : Set ℝ} (hU : IsOpen U) :
    Completion (Lp ℂ 2 μ ⊗[ℂ] supportedMellinLineCompletion b N U) →ₗᵢ[ℂ]
      Completion (Lp ℂ 2 μ ⊗[ℂ] MellinLineCompletion b N) :=
  (modulatedMellinLineEquiv μ b N).toLinearIsometry.comp
    ((lpTwoRadialSupport μ (stripMeasure b b (2 * (N : ℝ))) U).subtypeₗᵢ.comp
      (modulatedSupportedMellinEquiv μ b N hU).symm.toLinearIsometry)

theorem modulatedSupportedMellinEmbedding_commutes (b : ℝ) (N : ℕ) {U : Set ℝ}
    (hU : IsOpen U) (u : lpTwoRadialSupport μ (stripMeasure b b (2 * (N : ℝ))) U) :
    modulatedSupportedMellinEmbedding μ b N hU (modulatedSupportedMellinEquiv μ b N hU u) =
      modulatedMellinLineEquiv μ b N u.val := by
  change modulatedMellinLineEquiv μ b N
    ((modulatedSupportedMellinEquiv μ b N hU).symm (modulatedSupportedMellinEquiv μ b N hU u)).val = _
  rw [LinearIsometryEquiv.symm_apply_apply]

private theorem fullMellin_onProduct (b : ℝ) (N : ℕ) (u : Lp ℂ 2 μ)
    (v : StripSobolev b b (2 * (N : ℝ))) :
    modulatedMellinLineEquiv μ b N (lpTwoProduct u v) =
      hilbertTmul u (mellinLineEquiv b N v) := by
  let E : Completion (Lp ℂ 2 μ ⊗[ℂ] StripSobolev b b (2 * (N : ℝ))) ≃ₗᵢ[ℂ]
    Lp ℂ 2 (μ.prod (stripMeasure b b (2 * (N : ℝ)))) := completedLpTwoTensorEquiv
  have he : E (hilbertTmul u v) = lpTwoProduct u v := completedLpTwoTensorEquiv_tmul u v
  rw [← he]
  change completionCongrIsometry _ (E.symm (E (hilbertTmul u v))) = _
  rw [E.symm_apply_apply]
  exact completionCongrIsometry_coe _ (u ⊗ₜ[ℂ] v)

/-- The supported embedding is the usual tensor of the scalar inclusion with
the identity, as checked on its dense pure tensors. -/
theorem modulatedSupportedMellinEmbedding_tmul (b : ℝ) (N : ℕ) {U : Set ℝ} (hU : IsOpen U)
    (u : Lp ℂ 2 μ) (v : supportedMellinLineCompletion b N U) :
    modulatedSupportedMellinEmbedding μ b N hU (hilbertTmul u v) =
      hilbertTmul u (supportedScalarLineEmbedding b N U v) := by
  let E := supportedMellinLineEquiv b N U
  obtain ⟨w, rfl⟩ := E.surjective v
  let T := modulatedSupportedTensorEquiv μ b (2 * (N : ℝ)) hU
  have hM : modulatedSupportedMellinEquiv μ b N hU (T (hilbertTmul u w)) =
    hilbertTmul u (E w) := modulatedSupportedMellinEquiv_tmul μ b N hU u w
  have hT : (T (hilbertTmul u w)).val = lpTwoProduct u w.val :=
    modulatedSupportedTensorEquiv_tmul μ b (2 * (N : ℝ)) hU u w
  rw [← hM, modulatedSupportedMellinEmbedding_commutes, hT, fullMellin_onProduct]
  have he : supportedScalarLineEmbedding b N U (E w) = mellinLineEquiv b N w.val := by
    change mellinLineEquiv b N (E.symm (E w)).val = _
    rw [E.symm_apply_apply]
  rw [he]

section Closure

variable [TopologicalSpace K] [T2Space K] [CompactSpace K] [BorelSpace K]
  [CommGroup K] [IsTopologicalGroup K] [IsFiniteMeasure μ] [μ.WeaklyRegular]

/-- The supported Mellin tensor is exactly the closure of the strict-support
tests in the full analytic Hilbert tensor. -/
theorem modulatedMellin_supportedClosure (b : ℝ) (N : ℕ) {U : Set ℝ} (hU : IsOpen U) :
    closure (range (fun f : modulatedExponentialProfileCutoff (K := K) U =>
      modulatedMellinLineEquiv μ b N (modulatedExponentialProfile_inclusion μ b N f.val))) =
    range (modulatedSupportedMellinEmbedding μ b N hU) := by
  let I := modulatedExponentialProfile_cutoffInclusion μ b N U
  let M := modulatedSupportedMellinEquiv μ b N hU
  let J := modulatedSupportedMellinEmbedding μ b N hU
  let F := modulatedMellinLineEquiv μ b N
  have hcomp (f : modulatedExponentialProfileCutoff (K := K) U) :
      F (modulatedExponentialProfile_inclusion μ b N f.val) = J (M (I f)) :=
    (modulatedSupportedMellinEmbedding_commutes μ b N hU (I f)).symm
  rw [show (fun f : modulatedExponentialProfileCutoff (K := K) U =>
      modulatedMellinLineEquiv μ b N (modulatedExponentialProfile_inclusion μ b N f.val)) =
      J ∘ (M ∘ I) from funext hcomp, range_comp, J.isometry.isClosedEmbedding.closure_image_eq]
  have hd : DenseRange (M ∘ I) :=
    M.surjective.denseRange.comp (modulatedExponentialProfile_cutoff_dense μ b N hU) M.continuous
  rw [hd.closure_range, Set.image_univ]

end Closure

end
end Masullo
