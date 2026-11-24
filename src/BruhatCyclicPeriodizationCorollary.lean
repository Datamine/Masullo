import BruhatCyclicPeriodization
import BruhatCyclicPeriodizationExact

open Function Set

namespace Masullo

noncomputable section

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G]
variable (m : G →ₜ* Multiplicative ℝ) (hm : IsProperMap m) (hms : Surjective m)
  (γ : G) (hγ : 0 < (m γ).toAdd)

local notation "Γ" => Subgroup.zpowers γ
local notation "H" => G ⧸ Γ

include hγ in
omit [LocallyCompactSpace G] in
/-- Positive logarithmic period makes the cyclic subgroup closed. In
particular the quotient used in Corollary 4.5.3.1 is canonically Hausdorff. -/
theorem modulatedCyclicSubgroup_isClosed : IsClosed (Γ : Set G) := by
  letI : DiscreteTopology Γ := modulatedCyclicSubgroup_discrete m γ hγ
  exact (Subgroup.zpowers γ).isClosed_of_discrete

/-- Corollary 4.5.3.1, pp. 208–209, in logarithmic modulus coordinates.
The three domain spaces carry their Schwartz–Bruhat or exponential-decay
inductive topologies. Both asserted difference ranges are already closed. -/
theorem bruhatCyclicPeriodization_corollary (I : Set ℝ) (h0 : (0 : ℝ) ∈ I) :
    letI : IsClosed (Γ : Set G) := modulatedCyclicSubgroup_isClosed m γ hγ
    ∃ (P : BruhatSchwartz G →L[ℂ] BruhatSchwartz H)
      (T : ModulatedExponentialInductive m I →L[ℂ] BruhatSchwartz H)
      (E : ModulatedExponentialInductive m univ →L[ℂ] BruhatSchwartz H),
      Surjective P ∧ IsOpenMap P ∧ Surjective T ∧ Surjective E ∧
      (∀ f x, HasSum (fun n : ℤ ↦ f.val (γ ^ n * x)) ((P f).val (QuotientGroup.mk x))) ∧
      Injective (modulatedDecay_zeroInclusion m I h0) ∧
      (∀ f, T f = P (modulatedDecay_zeroInclusion m I h0 f)) ∧
      (∀ f, E f = P (modulatedDecay_zeroInclusion m univ (mem_univ 0) f)) ∧
      (∀ f, T (modulatedDecay_restrict m (subset_univ I) f) = E f) ∧
      (∀ T' : ModulatedExponentialInductive m I →L[ℂ] BruhatSchwartz H,
        (∀ f, T' (modulatedDecay_restrict m (subset_univ I) f) = E f) → T' = T) ∧
      P.ker = (bruhatSchwartzDifference γ).range ∧
      T.ker = (modulatedDecay_cyclicDifference m hm hms γ I h0).range ∧
      IsClosed ((bruhatSchwartzDifference γ).range : Set (BruhatSchwartz G)) ∧
      IsClosed ((modulatedDecay_cyclicDifference m hm hms γ I h0).range :
        Set (ModulatedExponentialInductive m I)) := by
  letI : IsClosed (Γ : Set G) := modulatedCyclicSubgroup_isClosed m γ hγ
  let P := bruhatCyclicPeriodization m hm γ hγ hms
  have hP := bruhatCyclicPeriodization_apply m hm γ hγ hms
  obtain ⟨S, hS⟩ := exists_bruhatCyclicPeriodization_section m hm γ hγ hms
  obtain ⟨T, E, hT, hE, hTval, hEval, hfactor, huniq⟩ :=
    exists_weightedCyclicPeriodization_factorization m hm hms γ hγ P hP I h0
  have hTo (f : ModulatedExponentialInductive m I) (x : G) :
      (T f).val (QuotientGroup.mk x) =
        bruhatSchwartz_cyclicOrbitSum m γ hγ x (modulatedDecay_zeroInclusion m I h0 f) :=
    (congrArg (fun g : BruhatSchwartz H ↦ g.val (QuotientGroup.mk x)) (hTval f)).trans (hP _ x)
  have hTk := modulatedDecay_periodization_ker m hm hms γ hγ I h0 T hTo
  refine ⟨P, T, E, fun g ↦ ⟨S g, hS g⟩,
    bruhatCyclicPeriodization_isOpenMap m hm γ hγ hms, hT, hE, ?_, ?_,
    hTval, hEval, hfactor, huniq, bruhatCyclicPeriodization_ker m hm hms γ hγ P hP, hTk,
    bruhatSchwartzDifference_isClosed_range m hm hms γ hγ, ?_⟩
  · intro f x
    rw [show (P f).val (QuotientGroup.mk x) = _ from hP f x,
      bruhatSchwartz_cyclicOrbitSum_apply]
    exact (bruhatSchwartz_cyclicOrbit_summable_norm m γ hγ f x).of_norm.hasSum
  · intro f g h
    exact ModulatedExponentialInductive.algebraicEquiv.injective
      (Subtype.ext (congrArg (fun u : BruhatSchwartz G ↦ u.val) h))
  · letI : T2Space (BruhatSchwartz H) := bruhatSchwartz_t2
    rw [← hTk]
    exact T.isClosed_ker

end

end Masullo
