import ModulatedDecayTensorDiagram
import ModulatedDecayMellinTensor
import ModulationSection

set_option Elab.async false
set_option maxHeartbeats 1500000

open Function MeasureTheory Set Topology
open scoped TensorProduct

namespace Masullo
noncomputable section

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
  (m : G →ₜ* Multiplicative ℝ)

local notation "K" => m.toMonoidHom.ker

variable [LocallyCompactSpace m.toMonoidHom.ker]

/-- The tensor product of the angular Fourier and radial Mellin equivalences
computes the Haar integral on the entire completed tensor. -/
theorem exists_decayMellin_completedTensorEquiv_of_stages
    (hm : IsProperMap m) (hms : Surjective m)
    (μ : Measure G) [μ.IsHaarMeasure] (ν : Measure K) [ν.IsHaarMeasure]
    (I : Set ℝ) (hI : IsOpen I) (hInt : OrdConnected I) (hne : I.Nonempty)
    (hLoc : ∀ (τ : Multiplicative ℝ →ₜ* G) (hτ : RightInverse τ m)
      (p : WholeBruhatStage K) (q : WholeBruhatStage G),
      q.val.1.kernel = p.val.1.kernel.map m.toMonoidHom.ker.subtype →
      ∃ L : (projectiveTensorModuleStructure p.val.Space (PositiveRealExponentialDecay I)).Completed
          ≃L[ℂ] WholeBruhatDecayStage m I q,
        ∀ (a : p.val.Space) (r : PositiveRealExponentialDecay I) (g : G),
          (L ((projectiveTensorModuleStructure p.val.Space (PositiveRealExponentialDecay I)).incl
            (a ⊗ₜ[ℂ] r))).val g =
            p.val.realize a (modulatedKernelProjection m τ hτ g) * r.val (m g).toAdd) :
    ∃ (τ : Multiplicative ℝ →ₜ* G) (hτ : RightInverse τ m),
      let B := BruhatSchwartz (PontryaginDual K)
      let Q := SchwartzBergman I
      let P := inductiveTensorModuleStructure B Q
      let A := BruhatSchwartz K
      let R := PositiveRealExponentialDecay I
      let D := inductiveTensorModuleStructure A R
      ∃ L : D.Completed ≃L[ℂ] ModulatedExponentialInductive m I,
        (∀ (a : A) (r : R) (g : G),
          (L (D.incl (a ⊗ₜ[ℂ] r))).val g =
            a.val (modulatedKernelProjection m τ hτ g) * r.val (modulatedLog m g)) ∧
        ∃ F : BruhatSchwartz K ≃L[ℂ] B,
          (∀ a ω, (F a).val ω = lcaFourier ν a.val ω⁻¹) ∧
          ∃ (c : ℝ) (_ : 0 < c) (T : ModulatedExponentialInductive m I ≃L[ℂ] P.Completed),
            (∀ a r, T (L ((inductiveTensorModuleStructure (BruhatSchwartz K) (PositiveRealExponentialDecay I)).incl
              (a ⊗ₜ[ℂ] r))) = P.incl (F a ⊗ₜ[ℂ] positiveRealFourierMellin I hI hInt hne r)) ∧
            ∃ V : PontryaginDual K → {z : ℂ // z.re ∈ I} → P.Completed →L[ℂ] ℂ,
              (∀ ω z b q, V ω z (P.incl (b ⊗ₜ[ℂ] q)) = b.val ω * q.val z.val) ∧
              (∀ ω z f, decayMellinEvaluation μ m (ω.comp (modulatedKernelProjection m τ hτ)) z.val z.property f =
                c • V ω z (T f)) ∧
              Injective (fun w ω z => V ω z w) := by
  obtain ⟨τ,hτ⟩ := exists_realModulation_section m hm hms
  refine ⟨τ,hτ,?_⟩
  dsimp only
  letI : CompactSpace K := isCompact_iff_compactSpace.mp
    (hm.isCompact_preimage (isCompact_singleton (x := (1 : Multiplicative ℝ))))
  obtain ⟨L,hL⟩ := exists_splitGlobal_completedTensorEquiv_of_stages m τ hτ hm I hne hInt (hLoc τ hτ)
  exact ⟨L, hL, exists_decayMellin_completedTensorEquiv_of_multiplication
    m τ hτ hm μ ν I hI hInt hne L hL⟩

end
end Masullo
