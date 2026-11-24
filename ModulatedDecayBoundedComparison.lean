import ModulatedDecayTensorBoundedLifts
import ModulatedDecayTensorComparisonCriteria
import ModulatedDecayInductiveTensorCoverage

open Bornology Function Set Topology
open scoped TensorProduct

namespace Masullo

noncomputable section

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  (m : G →ₜ* Multiplicative ℝ)

local notation "K" => m.toMonoidHom.ker

set_option maxHeartbeats 3000000 in
/-- The radial-first comparison in (D.3.3.6) is bijective and identifies bounded sets. -/
theorem splitDecay_completedTensorComparison_bijective_bounded
    (hm : IsProperMap m) (I : Set ℝ) (hI : I.Nonempty) (hInt : OrdConnected I) :
    letI : LocallyCompactSpace K :=
      (isClosed_singleton.preimage m.continuous : IsClosed (K : Set G)).locallyCompactSpace
    let A := BruhatSchwartz K
    let R := PositiveRealExponentialDecay I
    letI : IsTopologicalAddGroup A := (PolynormableSpace.withSeminorms ℂ A).topologicalAddGroup
    letI : IsTopologicalAddGroup R := (PolynormableSpace.withSeminorms ℂ R).topologicalAddGroup
    let C := completedInductiveTensorComparison (E := R) (F := A)
    Bijective C ∧ ∀ B : Set (inductiveTensorModuleStructure R A).Completed,
      IsVonNBounded ℂ (C '' B) ↔ IsVonNBounded ℂ B := by
  dsimp only
  letI : LocallyCompactSpace K :=
    (isClosed_singleton.preimage m.continuous : IsClosed (K : Set G)).locallyCompactSpace
  letI : CompactSpace K := isCompact_iff_compactSpace.mp
    (hm.isCompact_preimage (isCompact_singleton (x := (1 : Multiplicative ℝ))))
  letI : SecondCountableTopology K := IsInducing.subtypeVal.secondCountableTopology
  have hcov := inductiveDecayTensorStageCoverage_of_strict (H := K) I hI hInt
  exact comparison_radialFirst_of_angularFirst (H := K) I
    (comparison_bijective_bounded_of_stageCoverage I hcov
      (comparison_boundedLift (H := K) I hI hInt))

end
end Masullo
