import BruhatCofinalDirections
import BruhatSupportedWindow

open Function Module Set Topology

namespace Masullo

noncomputable section

variable {G V : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G]
  [AddCommGroup V] [Module ℝ V] [Module.Finite ℝ V] [TopologicalSpace V] [ContinuousSMul ℝ V]

/-- A fixed radial and angular family works for every sufficiently small
compact subgroup with compactly generated annihilator. -/
theorem exists_compactSubgroup_radial_basis_directions
    (m : G →ₜ* Multiplicative ℝ) (hm : IsProperMap m)
    (τ : Multiplicative ℝ →ₜ* G) (hτ : RightInverse τ m)
    (e : Multiplicative V →ₜ* G)
    (he : ∀ c : Multiplicative ℝ →ₜ* G, ∃ x : V, ∀ t : ℝ,
      c (Multiplicative.ofAdd t) = e (Multiplicative.ofAdd (t • x)))
    (hf : ∀ x : V, (∀ t : ℝ, e (Multiplicative.ofAdd (t • x)) = 1) → x = 0)
    {d : ℕ} (hd : Module.finrank ℝ V = d + 1) :
    ∃ K₀ : Subgroup G, IsCompact (K₀ : Set G) ∧
      IsOpen (lcaAnnihilator K₀ : Set (PontryaginDual G)) ∧
      IsCompactlyGeneratedGroup (lcaAnnihilator K₀) ∧
      ∃ γ : Fin (d + 1) → Multiplicative ℝ →ₜ* G,
        γ 0 = τ ∧ (∀ (i : Fin d) t, m (γ i.succ t) = 1) ∧
        ∀ K : Subgroup G, K ≤ K₀ → IsCompact (K : Set G) →
          IsCompactlyGeneratedGroup (lcaAnnihilator K) →
          ∃ P : WholeBruhatStage G, P.val.1.kernel = K ∧
            ∃ B : Basis (Fin (d + 1)) ℝ
              (EuclideanSpace ℝ (Fin P.val.2.realDim) × EuclideanSpace ℝ (Fin P.val.2.torusDim)),
              ∀ i, P.coordinates.comp (γ i) = elementaryOneParameter (B i) := by
  obtain ⟨P₀, γ, hγ₀, hγ₁, hγ⟩ :=
    WholeBruhatStage.exists_cofinal_radial_basis_directions m hm τ hτ e he hf hd
  let K₀ := P₀.val.1.kernel
  have hk₀ : IsCompact (K₀ : Set G) := by
    rw [← lcaDualAnnihilator_annihilator K₀ P₀.val.1.kernel_closed]
    exact isCompact_lcaDualAnnihilator_of_isOpen _ P₀.val.1.annihilator_open
  refine ⟨K₀, hk₀, P₀.val.1.annihilator_open, P₀.val.1.annihilator_compactlyGenerated,
    γ, hγ₀, hγ₁, fun K hK hKc hKg => ?_⟩
  obtain ⟨P, hP⟩ := exists_wholeBruhatStage_kernel m hm hτ.surjective K hKc hKg
  exact ⟨P, hP, hγ P (hP.symm ▸ hK)⟩

end
end Masullo
