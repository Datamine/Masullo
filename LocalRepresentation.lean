import PettisBounds
import Mathlib.Analysis.LocallyConvex.WeakDual
import Mathlib.Topology.Algebra.Module.Spaces.PointwiseConvergenceCLM

open Function MeasureTheory Set Topology
open scoped PointwiseConvergenceCLM

namespace Masullo

noncomputable section

variable {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [T2Space E]

/-- Evaluation at a vector, as a continuous linear form on the weak dual. -/
abbrev weakDualEvaluation (x : E) : StrongDual ℂ (E →Lₚₜ[ℂ] ℂ) :=
  PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) ℂ x

/-- A point in the closed convex hull of a compact set is represented
against the continuous dual by a Radon probability on the compact set. -/
theorem compact_hull_local_representation [Module ℝ E] [IsScalarTower ℝ ℂ E]
    (K : Set E) (hK : IsCompact K) {x : E} (hx : x ∈ closure (convexHull ℝ K)) :
    letI : MeasurableSpace K := borel K
    ∃ μ : Measure K, μ.Regular ∧ μ Set.univ = 1 ∧
      HasPositivePettisIntegral μ (fun y : K => weakBidualEval E y.val) (weakBidualEval E x) ∧
      ∀ ℓ : E →Lₚₜ[ℂ] ℂ, weakDualEvaluation x ℓ = ∫ y : K, weakDualEvaluation y.val ℓ ∂μ := by
  classical
  letI : MeasurableSpace K := borel K
  letI : BorelSpace K := ⟨rfl⟩
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hR := (regularProbabilityPettisIntegral_range_eq
    (f := (Subtype.val : K → E)) continuous_subtype_val).1
  have hx' : weakBidualEval E x ∈ closure (weakBidualEval E '' convexHull ℝ (range (Subtype.val : K → E))) := by
    rw [Subtype.range_coe_subtype, ofPred_mem_eq]
    exact image_closure_subset_closure_image (weakBidualEval_continuous E) ⟨x, hx, rfl⟩
  rw [← hR] at hx'
  obtain ⟨μ, hμ, hrep⟩ := hx'
  have he (ℓ : StrongDual ℂ E) : ℓ x = ∫ y : K, ℓ y.val ∂(μ : Measure K) :=
    (congrArg (fun w : WeakAlgebraicBidual E => (show Module.Dual ℂ (StrongDual ℂ E) from w) ℓ) hrep).symm
  refine ⟨(μ : Measure K), hμ, measure_univ, ?_, fun ℓ => he ℓ⟩
  intro φ
  let B : Module.Dual ℂ (StrongDual ℂ E) →ₗ[ℂ] (StrongDual ℂ E) →ₗ[ℂ] ℂ := LinearMap.id
  obtain ⟨ℓ, rfl⟩ := LinearMap.dualEmbedding_surjective B φ
  exact ⟨(ℓ.continuous.comp continuous_subtype_val).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _), he ℓ⟩

end

end Masullo
