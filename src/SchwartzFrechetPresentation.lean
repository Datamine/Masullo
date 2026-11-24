import PeriodicBanachCoordinates
import Mathlib.Order.Filter.CountablyGenerated

open Filter Set Topology UniformSpace
open scoped SchwartzMap

namespace Masullo

noncomputable section

variable {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]

/-- A first-countable locally convex space has a sequence of defining seminorms. -/
theorem exists_countable_withSeminorms [FirstCountableTopology E] [PolynormableSpace ℂ E] :
    ∃ q : SeminormFamily ℂ E ℕ, WithSeminorms q := by
  classical
  let hp := PolynormableSpace.withSeminorms ℂ E
  letI : IsTopologicalAddGroup E := hp.topologicalAddGroup
  obtain ⟨S, hS⟩ := (𝓝 (0 : E)).exists_antitone_basis
  have hb (i : ℕ) := (hp.mem_nhds_iff 0 (S i)).mp (hS.mem i)
  choose s r hr hs using hb
  let q (i : ℕ) := (s i).sup (fun p : {p : Seminorm ℂ E // Continuous p} => p.val)
  refine ⟨q, (SeminormFamily.withSeminorms_iff_nhds_eq_iInf q).mpr ?_⟩
  apply le_antisymm
  · apply le_iInf
    intro i
    have hc : Continuous (q i) := Seminorm.continuous_finsetSup fun j _ => j.property
    exact (hc.tendsto' 0 0 (map_zero (q i))).le_comap
  · apply Filter.le_def.mpr
    intro U hU
    obtain ⟨i, -, hi⟩ := hS.1.mem_iff.mp hU
    have hball : (q i).ball 0 (r i) ∈ Filter.comap (q i) (𝓝 0) := by
      rw [Seminorm.ball_zero_eq_preimage_ball]
      exact Filter.preimage_mem_comap (Metric.ball_mem_nhds 0 (hr i))
    have hle : (⨅ j, Filter.comap (q j) (𝓝 (0 : ℝ))) ≤ Filter.comap (q i) (𝓝 0) :=
      iInf_le _ i
    exact Filter.mem_of_superset (Filter.le_def.mp hle _ hball) ((hs i).trans hi)

/-- A Fréchet target admits a single countable presentation in which the
corrected Euclidean and torus Schwartz spaces are both Fréchet. -/
theorem exists_schwartz_and_torus_frechet (hE : IsFrechetTVS E) (d : ℕ) :
    ∃ (q : SeminormFamily ℂ E ℕ) (hq : WithSeminorms q),
      IsFrechetTVS (localBanachSchwartz (X := EuclideanSpace ℝ (Fin d)) hq) ∧
      IsFrechetTVS (localBanachPeriodic (euclideanTorusLocalization d) hq) := by
  obtain ⟨hadd, hpoly, hmetric, hcomplete⟩ := hE
  letI : IsTopologicalAddGroup E := hadd
  letI : PolynormableSpace ℂ E := hpoly
  letI : TopologicalSpace.MetrizableSpace E := hmetric
  obtain ⟨q, hq⟩ := exists_countable_withSeminorms (E := E)
  exact ⟨q, hq, localBanachSchwartz_frechet hq hcomplete,
    localBanachPeriodic_frechet (euclideanTorusLocalization d) hq hcomplete⟩


end
end Masullo
