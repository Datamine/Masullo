import BruhatStagePolynomialSeminorms

open Function MeasureTheory Topology

namespace Masullo.WholeBruhatStage

noncomputable section

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]

/-- The weighted supremum topology expressed in coordinates of the quotient. -/
def HasLogWeightedQuotientSup (P : WholeBruhatStage G)
    (m : G →ₜ* Multiplicative ℝ) {d : ℕ}
    (γ : Fin d → Multiplicative ℝ →ₜ* G) : Prop :=
    ∃ U : SeminormFamily ℂ P.fixedSubmodule ((Fin d → ℕ) × ℕ), WithSeminorms U ∧
      ∀ a n f, ∃ V : P.ElementaryCoordinates → ℂ,
        (∀ g : G, V (P.coordinates g).toAdd = (1 + (↑|modulatedLog m g| : ℂ) ^ n) *
          (bruhatDerivativeWord ((invariantBasisWord a).map γ) f.val).val g) ∧
        U (a, n) f = ⨆ y, ‖V y‖

set_option maxHeartbeats 1500000 in
/-- The weighted supremum can be computed on the quotient itself. The
elementary coordinates present that quotient and the weighted derivative
profile descends along the quotient projection. -/
theorem withSeminorms_fixed_logWeightedQuotientSup (P : WholeBruhatStage G)
    [MeasurableSpace P.val.2.finiteFactor] [BorelSpace P.val.2.finiteFactor]
    (μ : Measure G) [μ.IsHaarMeasure]
    (m : G →ₜ* Multiplicative ℝ) (hm : IsProperMap m) (hms : Surjective m)
    {d : ℕ} (B : Module.Basis (Fin d) ℝ
      (EuclideanSpace ℝ (Fin P.val.2.realDim) × EuclideanSpace ℝ (Fin P.val.2.torusDim)))
    (γ : Fin d → Multiplicative ℝ →ₜ* G)
    (hγ : ∀ j, P.coordinates.comp (γ j) = elementaryOneParameter (B j)) :
    P.HasLogWeightedQuotientSup m γ := by
  unfold HasLogWeightedQuotientSup
  obtain ⟨U, hU, hUnorm⟩ := P.withSeminorms_fixed_logWeightedSup μ m hm hms B γ hγ
  refine ⟨U, hU, fun a n f => ?_⟩
  let cs := (invariantBasisWord a).map γ
  let e := P.equivFixedSubmodule
  let u := e.symm f
  let v := elementarySchwartz_derivativeWord (cs.map fun c => P.coordinates.comp c) u
  have hu : P.val.inclusionCLM u = f.val := congrArg Subtype.val (e.apply_symm_apply f)
  have hv := P.realize_derivativeWord cs u
  rw [hu] at hv
  let V (y : P.ElementaryCoordinates) := (1 + (↑|P.logCoordinate m y| : ℂ) ^ n) * v y
  have hV (g : G) : V (P.coordinates g).toAdd =
      (1 + (↑|modulatedLog m g| : ℂ) ^ n) * (bruhatDerivativeWord cs f.val).val g := by
    have hvg := congrArg (fun u : BruhatSchwartz G => u.val g) hv
    change _ = P.val.realize v g at hvg
    rw [P.realize_eq_coordinates] at hvg
    simp only [V, P.logCoordinate_coordinates, ← hvg, modulatedLog]
  refine ⟨V, hV, ?_⟩
  rw [hUnorm]
  change (⨆ g : G, ‖(1 + (↑|modulatedLog m g| : ℂ) ^ n) *
      (bruhatDerivativeWord cs f.val).val g‖) = ⨆ y, ‖V y‖
  have heq : (fun g : G => ‖(1 + (↑|modulatedLog m g| : ℂ) ^ n) *
      (bruhatDerivativeWord cs f.val).val g‖) =
        fun g : G => ‖V (P.coordinates g).toAdd‖ := funext fun g =>
    congrArg norm (hV g).symm
  rw [heq]
  have hs : Surjective (fun g : G => (P.coordinates g).toAdd) :=
    Multiplicative.toAdd.surjective.comp P.coordinates_surjective
  change sSup (Set.range ((fun y => ‖V y‖) ∘ (fun g => (P.coordinates g).toAdd))) =
    sSup (Set.range fun y => ‖V y‖)
  apply congrArg sSup
  rw [Set.range_comp, hs.range_eq, Set.image_univ]

end
end Masullo.WholeBruhatStage
