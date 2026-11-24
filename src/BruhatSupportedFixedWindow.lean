import BruhatSupportedWindow
import ModulatedCompactQuotient
import ElementaryFixedSupportTopology

open Function Set Topology

namespace Masullo

noncomputable section

set_option maxHeartbeats 2500000

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
variable (m : G →ₜ* Multiplicative ℝ) (hm : IsProperMap m)
variable (τ : Multiplicative ℝ →ₜ* G) (hτ : ∀ t, m (τ t) = t)
variable (K : Subgroup G) (hK : IsCompact (K : Set G)) (hKm : K ≤ m.toMonoidHom.ker)
variable (hgen : IsCompactlyGeneratedGroup (lcaAnnihilator (K.comap m.toMonoidHom.ker.subtype)))

local notation "logModulus" => (fun x : G ↦ Multiplicative.toAdd (m x))
local notation "E" => ModulatedExponentialInductive m univ

include hm hτ hK hKm hgen in
/-- Proposition 4.5.2.1(1). Supported invariant tests form a closed
subspace in the entire-decay topology. The identified stage carries the
Fréchet topology of uniform convergence of all mixed derivatives. -/
theorem bruhatSupportedInvariant_fixedWindow (W : Set ℝ) (hW : IsCompact W) :
    let U := bruhatSupportedInvariant m K (logModulus ⁻¹' W)
    IsClosed (U : Set E) ∧
      ∃ P : WholeBruhatStage G, P.val.1.kernel = K ∧
        IsFrechetTVS (P.val.compactTests (logModulus ⁻¹' W)) ∧
        WithSeminorms (fun i : (Fin P.val.2.realDim → ℕ) × (Fin P.val.2.torusDim → ℕ) =>
          (elementarySchwartzSeminorm (0, i.1, i.2, 0)).comp
            (P.val.compactTests (logModulus ⁻¹' W)).subtype) ∧
        ∃ e : P.val.compactTests (logModulus ⁻¹' W) ≃L[ℂ] U,
          ∀ u, (e u).val.val = P.val.realize u.val := by
  dsimp only
  let C : Set G := logModulus ⁻¹' W
  have hC : IsCompact C := hm.isCompact_preimage
    (show IsCompact (Multiplicative.toAdd ⁻¹' W) from hW)
  have hms : Surjective m := fun t ↦ ⟨τ t, hτ t⟩
  have hGen : IsCompactlyGeneratedGroup (lcaAnnihilator K) :=
    modulatedAnnihilator_compactlyGenerated m τ hτ K hK hKm hgen
  have hStage : ∃ P : WholeBruhatStage G, P.val.1.kernel = K :=
    exists_wholeBruhatStage_kernel m hm hms K hK hGen
  obtain ⟨P, hP⟩ := hStage
  refine ⟨bruhatCyclicInvariantCompact_isClosed m K W, P, hP, ?_, ?_, ?_⟩
  · exact P.val.compactTests_isFrechet C
  · exact P.compactTests_withUniformSeminorms C hC
  · have hEq := bruhatSupportedInvariant_stageEquiv m P C hm hms hC
    exact hP ▸ hEq

end

end Masullo
