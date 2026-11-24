import BruhatStageDirections

open Function Topology

namespace Masullo.WholeBruhatStage

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G]

/-- Whole-group Bruhat stages have a common refinement whose kernel
is contained in both of the original kernels. -/
theorem exists_common_kernel_refinement (P Q : WholeBruhatStage G) :
    ∃ R : WholeBruhatStage G, R.val.1.kernel ≤ P.val.1.kernel ∧
      R.val.1.kernel ≤ Q.val.1.kernel := by
  letI := (lcaStructuralPairs_filtered (G := G)).2
  obtain ⟨R, hPR, hQR⟩ := exists_ge_ge P.val.1 Q.val.1
  obtain ⟨e⟩ := R.quotient_elementary
  exact ⟨⟨⟨R, e⟩, top_unique (P.property ▸ hPR.1)⟩, hPR.2, hQR.2⟩

/-- The whole-group elementary stages of a proper modulation distinguish
points, since any continuous character factors through such a stage. -/
theorem eq_one_of_coordinates_eq_one (m : G →ₜ* Multiplicative ℝ)
    (hm : IsProperMap m) (hs : Surjective m) (x : G)
    (hx : ∀ P : WholeBruhatStage G, P.coordinates x = 1) : x = 1 := by
  apply (pontryaginBidualEval_isClosedEmbedding (G := G)).injective
  apply PontryaginDual.ext
  intro χ
  obtain ⟨R, hR, hχ⟩ := exists_modulatedBruhat_character_stage m hm hs χ
  obtain ⟨e⟩ := R.quotient_elementary
  let P : WholeBruhatStage G := ⟨⟨R, e⟩, hR⟩
  have hmeme : x ∈ P.coordinates.toMonoidHom.ker := hx P
  rw [P.coordinates_ker] at hmeme
  change χ x = χ 1
  rw [map_one]
  exact hχ ⟨x, hmeme⟩

theorem exists_trivial_velocity_kernel {I V : Type*} [Nonempty I] [AddCommGroup V]
    [Module ℝ V] [Module.Finite ℝ V] (K : I → Submodule ℝ V)
    (hdir : Directed (· ≥ ·) K) (hsep : ∀ x, (∀ i, x ∈ K i) → x = 0) :
    ∃ i, K i = ⊥ := by
  classical
  have hex : ∃ n : ℕ, ∃ i : I, Module.finrank ℝ (K i) = n :=
    ⟨_, Classical.arbitrary I, rfl⟩
  obtain ⟨i, hi⟩ := Nat.find_spec hex
  refine ⟨i, le_antisymm ?_ bot_le⟩
  intro x hx
  apply hsep x
  intro j
  obtain ⟨k, hki, hkj⟩ := hdir i j
  have hmin : Module.finrank ℝ (K i) ≤ Module.finrank ℝ (K k) :=
    hi.symm ▸ Nat.find_min' hex ⟨k, rfl⟩
  have heq : K k = K i := by
    by_contra hne
    exact (not_lt_of_ge hmin) (Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne hki hne))
  exact hkj (heq.symm ▸ hx)

end Masullo.WholeBruhatStage
