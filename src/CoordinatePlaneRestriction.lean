import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Topology.Maps.Proper.Basic

open Function Set TopologicalSpace Topology WithSeminorms
open scoped Distributions SchwartzMap ContDiff

namespace Masullo

noncomputable section

variable {D E : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Restrict a Schwartz function along an isometric linear inclusion. This
includes restriction to every coordinate plane in Theorem 5.3.2.3(1). -/
def schwartzRestrictLinearIsometry (j : D →ₗᵢ[ℝ] E) :
    𝓢(E, ℂ) →L[ℂ] 𝓢(D, ℂ) :=
  SchwartzMap.compCLMOfAntilipschitz ℂ j.toContinuousLinearMap.hasTemperateGrowth
    j.isometry.antilipschitz

@[simp] theorem schwartzRestrictLinearIsometry_apply (j : D →ₗᵢ[ℝ] E) (f : 𝓢(E, ℂ)) (x : D) :
    schwartzRestrictLinearIsometry j f x = f (j x) := rfl

variable [CompleteSpace D]

private def planeSupport (j : D →ₗᵢ[ℝ] E) (K : Compacts E) : Compacts D :=
  ⟨j ⁻¹' (K : Set E), j.isometry.isClosedEmbedding.isProperMap.isCompact_preimage K.isCompact⟩

private def restrictSupported (j : D →ₗᵢ[ℝ] E) (K : Compacts E) :
    𝓓_{K}(E, ℂ) →ₗ[ℂ] 𝓓_{planeSupport j K}(D, ℂ) where
  toFun f := ContDiffMapSupportedIn.of_support_subset
    (f.contDiff.comp j.toContinuousLinearMap.contDiff) fun x hx ↦ f.support_subset hx
  map_add' _ _ := by ext; rfl
  map_smul' _ _ := by ext; rfl

private lemma restrictSupported_continuous (j : D →ₗᵢ[ℝ] E) (K : Compacts E) :
    Continuous (restrictSupported j K) := by
  refine continuous_of_isBounded (ContDiffMapSupportedIn.withSeminorms ..)
    (ContDiffMapSupportedIn.withSeminorms ..) _ (fun i ↦ ⟨{i}, 1, fun f ↦ ?_⟩)
  simp only [Finset.sup_singleton, one_smul, Seminorm.comp_apply]
  rw [ContDiffMapSupportedIn.seminorm_top_le_iff ℂ (apply_nonneg ..)]
  intro x _
  change ‖iteratedFDeriv ℝ i (f ∘ j.toContinuousLinearMap) x‖ ≤ _
  rw [j.toContinuousLinearMap.iteratedFDeriv_comp_right f.contDiff x
    (by exact_mod_cast (le_top : (i : ℕ∞) ≤ ⊤))]
  have hj : ‖j.toContinuousLinearMap‖ ≤ 1 :=
    j.toContinuousLinearMap.opNorm_le_bound zero_le_one (fun x ↦ by simp)
  calc
    _ ≤ ‖iteratedFDeriv ℝ i f (j x)‖ * ∏ _ : Fin i, ‖j.toContinuousLinearMap‖ :=
      ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ ‖iteratedFDeriv ℝ i f (j x)‖ := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hj)
    _ ≤ _ := ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm_top ℂ

/-- Restriction of compactly supported smooth functions to a coordinate plane
is continuous for the actual LF test-function topology. -/
def testRestrictLinearIsometry (j : D →ₗᵢ[ℝ] E) :
    𝓓((⊤ : Opens E), ℂ) →L[ℂ] 𝓓((⊤ : Opens D), ℂ) :=
  TestFunction.limitCLM ℂ
    (fun f ↦ ⟨f ∘ j, f.contDiff.comp j.toContinuousLinearMap.contDiff,
      (restrictSupported j ⟨tsupport f, f.hasCompactSupport⟩
        (ContDiffMapSupportedIn.of_support_subset f.contDiff subset_closure)).hasCompactSupport,
      subset_univ _⟩)
    (fun K _ ↦ (TestFunction.ofSupportedInCLM ℂ (Ω := ⊤) (K := planeSupport j K) (subset_univ _)).comp
      ⟨restrictSupported j K, restrictSupported_continuous j K⟩)
    (fun _ _ _ ↦ by ext; rfl)

@[simp] theorem testRestrictLinearIsometry_apply (j : D →ₗᵢ[ℝ] E)
    (f : 𝓓((⊤ : Opens E), ℂ)) (x : D) :
    testRestrictLinearIsometry j f x = f (j x) := rfl

end
end Masullo
