import RiemannMasullo.AppD_SchwartzBruhat.Sec1c

/-! Run with `lake env lean` in original revision
`cb3e092484c0e94d115634ce9f202433bdbd17be` on Lean 4.36.0. -/

open UniformSpace
open scoped TensorProduct

namespace Masullo

open RiemannMasullo

attribute [local instance] uniformContinuousConstSMul_of_continuousConstSMul

variable {G H : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H]
  [T2Space H] [LocallyCompactSpace H] [SecondCountableTopology H]

/-- Lemma D.1.8.1, p. 778. The test and distribution identifications use the
same canonical elementary tensor map. -/
theorem bruhat_kernel_tests_and_distributions :
    let X := SchwartzBruhat G
    let Y := SchwartzBruhat H
    let Z := SchwartzBruhat (G × H)
    ∃ (e : Completion (InductiveTensor X Y) ≃L[ℂ] Z)
      (d : Completion (ProjectiveTensor (StrongDual ℂ X) (StrongDual ℂ Y)) ≃L[ℂ]
        StrongDual ℂ Z),
      (∀ (f : X) (g : Y) (x : G) (y : H),
        e (Completion.coe' (α := InductiveTensor X Y) (f ⊗ₜ[ℂ] g)) (x, y) = f x * g y) ∧
      ∀ (S : StrongDual ℂ X) (T : StrongDual ℂ Y) (f : X) (g : Y),
        d (Completion.coe' (α := ProjectiveTensor (StrongDual ℂ X) (StrongDual ℂ Y))
          (S ⊗ₜ[ℂ] T)) (e (Completion.coe' (α := InductiveTensor X Y) (f ⊗ₜ[ℂ] g))) =
          S f * T g := by
  obtain ⟨e, he⟩ := schwartzBruhat_kernel_equiv (G := G) (H := H)
  obtain ⟨d, hd⟩ := schwartzBruhat_strongDual_kernel_equiv e he
  exact ⟨e, d, he, hd⟩

#print axioms bruhat_kernel_tests_and_distributions
#print axioms RiemannMasullo.schwartzBruhat_strongDual_nuclear

end Masullo
