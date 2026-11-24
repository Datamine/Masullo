import HardySobolevLine

open Filter Function MeasureTheory Set Topology
open scoped InnerProductSpace

namespace Masullo

noncomputable section

local notation "Tests" => PositiveRealExponentialDecay (univ : Set ℝ)

private def compactTests (U : Set ℝ) : Submodule ℂ Tests where
  carrier := {f | HasCompactSupport f.val ∧ tsupport f.val ⊆ U}
  zero_mem' := by
    change HasCompactSupport (0 : ℝ → ℂ) ∧ tsupport (0 : ℝ → ℂ) ⊆ U
    exact ⟨HasCompactSupport.zero, by simp⟩
  add_mem' {f g} hf hg :=
    ⟨hf.1.add hg.1, (tsupport_add f.val g.val).trans (union_subset hf.2 hg.2)⟩
  smul_mem' d f hf :=
    ⟨hf.1.of_isClosed_subset (isClosed_tsupport _) (tsupport_smul_subset_right (fun _ : ℝ => d) f.val), (tsupport_smul_subset_right (fun _ : ℝ => d) f.val).trans hf.2⟩

/-- Smooth tests of compact support strictly inside the open cutoff are dense
in the supported weighted completion. -/
theorem supportedSobolevCompletion_eq_closure_of_compactTests (a b s : ℝ) {U : Set ℝ}
    (hU : IsOpen U) :
    (supportedSobolevCompletion a b s U : Set (StripSobolev a b s)) =
      closure {u | ∃ f : Tests, HasCompactSupport f.val ∧ tsupport f.val ⊆ U ∧
        stripSobolevTest univ ⟨a, mem_univ a⟩ ⟨b, mem_univ b⟩ s f = u} := by
  let j := stripSobolevTest univ ⟨a, mem_univ a⟩ ⟨b, mem_univ b⟩ s
  let T := (compactTests U).map j.toLinearMap
  have he : (T : Set (StripSobolev a b s)) = {u | ∃ f : Tests, HasCompactSupport f.val ∧
      tsupport f.val ⊆ U ∧ j f = u} := by
    ext u
    change (∃ f : Tests, (HasCompactSupport f.val ∧ tsupport f.val ⊆ U) ∧ j f = u) ↔ _
    constructor
    · rintro ⟨f, ⟨hf, hU'⟩, rfl⟩
      exact ⟨f, hf, hU', rfl⟩
    · rintro ⟨f, hf, hU', rfl⟩
      exact ⟨f, ⟨hf, hU'⟩, rfl⟩
  change ((supportedSobolevCompletion a b s U : Submodule ℂ (StripSobolev a b s)) : Set _) =
    closure {u | ∃ f : Tests, HasCompactSupport f.val ∧ tsupport f.val ⊆ U ∧ j f = u}
  rw [← he]
  change _ = (T.topologicalClosure : Set (StripSobolev a b s))
  suffices h : supportedSobolevCompletion a b s U = T.topologicalClosure by rw [h]
  apply le_antisymm
  · intro u hu
    have hup := (mem_supportedSobolevCompletion_iff a b s hU u).mp hu
    rw [← T.topologicalClosure.orthogonal_orthogonal]
    apply (Submodule.mem_orthogonal T.topologicalClosureᗮ u).mpr
    intro v hv
    let L := InnerProductSpace.toDual ℂ (StripSobolev a b s) v
    let g := (stripSobolevDuality a b s).symm L
    have hzero : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ U → g x = 0 := by
      apply stripDual_rep_eq_on_support_of_compactTestPairing a b s (K := fun _ => (0 : ℂ))
        continuous_const hU L
      intro f hfC hfU
      have ht : j f ∈ T := ⟨f, ⟨hfC, hfU⟩, rfl⟩
      simp only [mul_zero, integral_zero]
      exact Submodule.inner_left_of_mem_orthogonal (Submodule.le_topologicalClosure _ ht) hv
    have hprod : (fun x : ℝ => u x * g x) =ᵐ[volume] 0 := by
      filter_upwards [hup, hzero] with x hx hg
      by_cases hxU : x ∈ U
      · simp [hg hxU]
      · simp [hx hxU]
    change L u = 0
    rw [← (stripSobolevDuality a b s).apply_symm_apply L, stripSobolevDuality_apply]
    exact (integral_congr_ae hprod).trans (by simp)
  · apply Submodule.topologicalClosure_minimal _ ?_ (Submodule.isClosed_topologicalClosure _)
    rintro _ ⟨f, hf, rfl⟩
    exact (supportedSobolevTest a b s U f
      (fun x hx => image_eq_zero_of_notMem_tsupport (fun h => hx (hf.2 h)))).property

/-- The normalized analytic line completion is the closure of the Mellin
traces of compact smooth tests with support strictly inside the cutoff. -/
theorem supportedMellinLineCompletion_eq_closure_of_compactTests
    (b : ℝ) (N : ℕ) {U : Set ℝ} (hU : IsOpen U) :
    (supportedMellinLineCompletion b N U : Set (MellinTraceHilbert N)) =
      closure {T | ∃ f : Tests, HasCompactSupport f.val ∧ tsupport f.val ⊆ U ∧
        mellinLineTest b N f = T} := by
  let V := mellinLineIsometry b N
  let s := 2 * (N : ℝ)
  let E : Set (StripSobolev b b s) := {u | ∃ f : Tests, HasCompactSupport f.val ∧
    tsupport f.val ⊆ U ∧ weightedLineTest b N f = u}
  have he : (supportedSobolevCompletion b b s U : Set _) = closure E :=
    supportedSobolevCompletion_eq_closure_of_compactTests b b s hU
  have hV : IsClosedEmbedding V := V.isometry.isClosedEmbedding
  change V '' (supportedSobolevCompletion b b s U : Set _) = _
  rw [he, ← hV.closure_image_eq]
  congr 1
  ext z
  constructor
  · rintro ⟨x, ⟨f, hf, hU', rfl⟩, rfl⟩
    exact ⟨f, hf, hU', (mellinLineIsometry_onTest b N f).symm⟩
  · rintro ⟨f, hf, hU', rfl⟩
    exact ⟨weightedLineTest b N f, ⟨f, hf, hU', rfl⟩, mellinLineIsometry_onTest b N f⟩

end
end Masullo
