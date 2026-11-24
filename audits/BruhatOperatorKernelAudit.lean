import RiemannMasullo.AppC_LCTVS.Sec3a
import RiemannMasullo.AppD_SchwartzBruhat.Sec1b

/-! Run with `lake env lean` in original revision
`553ef728d88838327946035310ffdef2589e3844` on Lean 4.36.0. -/

open Bornology UniformSpace RiemannMasullo
open scoped TensorProduct UniformConvergence UniformConvergenceCLM

namespace Masullo

attribute [local instance] uniformContinuousConstSMul_of_continuousConstSMul

local notation:25 X " →Lᵦ " Y =>
  X →Lᵤ[ℂ, Set.ofPred (fun s : Set X ↦ IsVonNBounded ℂ s)] Y

variable {G H : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H]
  [T2Space H] [LocallyCompactSpace H] [SecondCountableTopology H]

/-- Theorem C.2.4.19, equation (C.2.4.10). The canonical completed
tensor map represents all continuous operators with their bounded-convergence
topology. -/
theorem bruhat_strongDual_kernel_operators :
    let X := SchwartzBruhat G
    let Y := SchwartzBruhat H
    ∃ E : Completion (ProjectiveTensor (StrongDual ℂ X) Y) ≃L[ℂ] (X →Lᵦ Y),
      ∀ (S : StrongDual ℂ X) (g : Y) (f : X),
        E (Completion.coe' (α := ProjectiveTensor (StrongDual ℂ X) Y) (S ⊗ₜ[ℂ] g)) f =
          S f • g := by
  intro X Y
  let : T2Space X := schwartzBruhat_t2 (G := G)
  let : T2Space Y := schwartzBruhat_t2 (G := H)
  let : CompleteSpace X := schwartzBruhat_complete (G := G)
  let : CompleteSpace Y := schwartzBruhat_complete (G := H)
  let : BarrelledSpace ℂ X := schwartzBruhat_barrelled (G := G)
  let : CompleteSpace (StrongDual ℂ X) := schwartzBruhat_strongDual_complete (G := G)
  have hn : IsNuclearTVS.{0} (StrongDual ℂ X) := schwartzBruhat_strongDual_nuclear (G := G)
  obtain ⟨E, hE⟩ := (completedProjectiveTensorToOperators_equiv (E := X) (F := Y) hn).2
  refine ⟨E, fun S g f ↦ ?_⟩
  exact (congrArg (fun T : X →Lᵦ Y ↦ T f) (hE (S ⊗ₜ[ℂ] g))).trans
    (projectiveTensorToOperators_tmul S g f)

#print axioms bruhat_strongDual_kernel_operators

end Masullo
