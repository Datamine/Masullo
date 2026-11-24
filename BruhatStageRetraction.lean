import BruhatFixedStages
import BruhatIsotypeComparison
import Mathlib.MeasureTheory.Group.Integral

open Function MeasureTheory Set Topology

namespace Masullo

noncomputable section

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]

set_option maxHeartbeats 950000 in
/-- Normalized Haar averaging over the structural kernel retracts the full
Schwartz--Bruhat space continuously to the prescribed quotient stage. -/
theorem exists_bruhatSchwartzStage_retraction (p : WholeBruhatStage G) :
    ∃ R : BruhatSchwartz G →L[ℂ] p.val.Space, LeftInverse R p.val.inclusionCLM := by
  let K := p.val.1.kernel
  let E := BruhatSchwartz G
  have hK : IsCompact (K : Set G) := by
    change IsCompact (p.val.1.kernel : Set G)
    rw [← lcaDualAnnihilator_annihilator p.val.1.kernel p.val.1.kernel_closed]
    exact isCompact_lcaDualAnnihilator_of_isOpen _ p.val.1.annihilator_open
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  letI : LocallyCompactSpace K := p.val.1.kernel_closed.locallyCompactSpace
  letI : MeasurableSpace K := borel K
  letI : BorelSpace K := ⟨rfl⟩
  let ν : Measure K := Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts K)
  letI : ν.IsHaarMeasure := inferInstanceAs
    (Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts K)).IsHaarMeasure
  letI : IsProbabilityMeasure ν := ⟨by
    simpa only [ν, TopologicalSpace.PositiveCompacts.coe_top] using
      (Measure.haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts K)))⟩
  obtain ⟨A, hA⟩ := exists_bruhatSchwartz_compactAverage K ν (1 : PontryaginDual K)
  let ev (x : G) : StrongDual ℂ E :=
    ⟨{ toFun := fun f => f.val x, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl },
      bruhatSchwartz_continuous_eval x⟩
  have havg (f : E) (x : G) : (A f).val x = ∫ k : K, f.val ((k : G)⁻¹ * x) ∂ν := by
    have he := (hA f (ev x)).2
    change (A f).val x = ∫ k : K,
      ((((1 : PontryaginDual K) k)⁻¹ : Circle) : ℂ) *
      (bruhatSchwartz_translate (k : G) f).val x ∂ν at he
    simpa only [PontryaginDual.one_apply, inv_one, Circle.coe_one, one_mul, bruhatSchwartz_translate_apply] using he
  have hfixed (f : E) : A f ∈ p.fixedSubmodule := by
    intro u x
    rw [havg f (u.val * x), havg f x]
    let g (k : K) := f.val ((k : G)⁻¹ * x)
    have he (k : K) : f.val ((k : G)⁻¹ * (u.val * x)) = g (u⁻¹ * k) := by
      change f.val ((k : G)⁻¹ * (u.val * x)) = f.val (((u.val⁻¹ * k.val)⁻¹) * x)
      rw [mul_inv_rev, inv_inv, mul_assoc]
    exact (integral_congr_ae (.of_forall he)).trans (integral_mul_left_eq_self g u⁻¹)
  let B : E →L[ℂ] p.fixedSubmodule :=
    ⟨A.toLinearMap.codRestrict p.fixedSubmodule hfixed, A.continuous.subtype_mk _⟩
  let e := p.equivFixedSubmodule
  refine ⟨e.symm.toContinuousLinearMap.comp B, fun a => ?_⟩
  apply e.injective
  change e (e.symm (B (p.val.inclusionCLM a))) = e a
  rw [e.apply_symm_apply]
  apply Subtype.ext
  change A (p.val.inclusionCLM a) = p.val.inclusionCLM a
  apply Subtype.ext
  funext x
  have h (k : K) : (p.val.inclusionCLM a).val ((k : G)⁻¹ * x) = (p.val.inclusionCLM a).val x := by
    have ha : p.val.inclusionCLM a ∈ p.fixedSubmodule :=
      p.inclusion_range_eq_fixedSubmodule ▸ LinearMap.mem_range_self _ a
    exact ha k⁻¹ x
  exact (havg (p.val.inclusionCLM a) x).trans
    ((integral_congr_ae (.of_forall h)).trans (by simp))

end
end Masullo
