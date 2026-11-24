import WeilQuotientIntegral
import Mathlib.Topology.Metrizable.Urysohn
import QuotientIndentation

open Filter Function MeasureTheory Set Topology TopologicalSpace
open scoped ENNReal

namespace Masullo

noncomputable section

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
variable (H : Subgroup G) (hH : IsClosed (H : Set G))
variable (μ : Measure H) [μ.IsHaarMeasure] [μ.Regular]

local instance : MeasurableSpace (G ⧸ H) := borel _
local instance : BorelSpace (G ⧸ H) := ⟨rfl⟩

/-- Lift a quotient measure by integrating translated subgroup Haar measures. -/
def quotientLiftedMeasure (ν : Measure (G ⧸ H)) : Measure G :=
  ν.bind (quotientCosetMeasure H μ)

include hH in
theorem lintegral_quotientLiftedMeasure_compact (ν : Measure (G ⧸ H))
    (g : CompactlySupportedContinuousMap G ℝ) (hg : ∀ x, 0 ≤ g x) :
    let S := TopologicalGroup.IsSES.ofClosedSubgroup H hH
    (∫⁻ x, ENNReal.ofReal (g x) ∂(quotientLiftedMeasure H μ ν)) =
      ∫⁻ q, ENNReal.ofReal (S.pushforward μ g q) ∂ν := by
  intro S
  have hκ := quotientCosetMeasure_measurable H hH μ
  have hmeas : Measurable (fun x => ENNReal.ofReal (g x)) :=
    (ENNReal.continuous_ofReal.comp g.continuous).measurable
  rw [quotientLiftedMeasure, Measure.lintegral_bind hκ.aemeasurable hmeas.aemeasurable]
  apply lintegral_congr
  intro q
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  have htr : Measurable (fun h : H => x * (h : G)) :=
    (continuous_const.mul continuous_subtype_val).measurable
  rw [quotientCosetMeasure_mk, lintegral_map hmeas htr]
  change _ = ENNReal.ofReal (S.pushforward μ g (QuotientGroup.mk' H x))
  rw [S.pushforward_apply_apply]
  exact (ofReal_integral_eq_lintegral_ofReal (S.pullback g x).integrable
    (.of_forall fun h => hg (x * (h : G)))).symm

include hH in
/-- The lifted measure is finite on compact sets whenever the quotient measure is. -/
theorem quotientLiftedMeasure_finiteOnCompacts (ν : Measure (G ⧸ H))
    [IsFiniteMeasureOnCompacts ν] : IsFiniteMeasureOnCompacts (quotientLiftedMeasure H μ ν) := by
  let S := TopologicalGroup.IsSES.ofClosedSubgroup H hH
  refine ⟨fun K hK => ?_⟩
  obtain ⟨g, hgK, hgc, _, hg⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen
    hK isOpen_univ (subset_univ K)
  let g' : CompactlySupportedContinuousMap G ℝ := ⟨g, hgc⟩
  have hnonneg (q : G ⧸ H) : 0 ≤ S.pushforward μ g' q := by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    change 0 ≤ S.pushforward μ g' (QuotientGroup.mk' H x)
    rw [S.pushforward_apply_apply]
    exact integral_nonneg fun h => (hg (x * (h : G))).1
  calc
    quotientLiftedMeasure H μ ν K = ∫⁻ x, K.indicator 1 x ∂(quotientLiftedMeasure H μ ν) :=
      (lintegral_indicator_one hK.measurableSet).symm
    _ ≤ ∫⁻ x, ENNReal.ofReal (g' x) ∂(quotientLiftedMeasure H μ ν) := by
      apply lintegral_mono
      intro x
      change K.indicator 1 x ≤ ENNReal.ofReal (g x)
      by_cases hx : x ∈ K
      · simp [hx, hgK hx]
      · simp [hx]
    _ = ∫⁻ q, ENNReal.ofReal (S.pushforward μ g' q) ∂ν :=
      lintegral_quotientLiftedMeasure_compact H hH μ ν g' fun x => (hg x).1
    _ < ⊤ := by
      rw [← ofReal_integral_eq_lintegral_ofReal (S.pushforward μ g').integrable
        (.of_forall hnonneg)]
      exact ENNReal.ofReal_lt_top


include hH in
/-- Compactly supported functions satisfy the lifted integral identity. -/
theorem quotientLiftedMeasure_integral_compact (ν : Measure (G ⧸ H))
    [IsFiniteMeasureOnCompacts ν]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : CompactlySupportedContinuousMap G E) :
    let S := TopologicalGroup.IsSES.ofClosedSubgroup H hH
    Integrable g (quotientLiftedMeasure H μ ν) ∧
      (∫ x, g x ∂(quotientLiftedMeasure H μ ν)) = ∫ q, S.pushforward μ g q ∂ν := by
  intro S
  let ρ := quotientLiftedMeasure H μ ν
  letI : IsFiniteMeasureOnCompacts ρ := quotientLiftedMeasure_finiteOnCompacts H hH μ ν
  refine ⟨g.integrable, ?_⟩
  let κ : ProbabilityTheory.Kernel (G ⧸ H) G :=
    ⟨quotientCosetMeasure H μ, quotientCosetMeasure_measurable H hH μ⟩
  have hcomp := Measure.comp_eq_comp_const_apply (κ := κ) (μ := ν)
  change ν.bind (quotientCosetMeasure H μ) = _ at hcomp
  have hI : Integrable g ((κ.comp (ProbabilityTheory.Kernel.const Unit ν)) ()) := by
    rw [← hcomp]
    change Integrable g ρ
    exact g.integrable
  calc
    (∫ x, g x ∂(quotientLiftedMeasure H μ ν)) = ∫ q, ∫ x, g x ∂κ q ∂ν := by
      rw [quotientLiftedMeasure, hcomp]
      simpa only [ProbabilityTheory.Kernel.const_apply] using ProbabilityTheory.Kernel.integral_comp hI
    _ = ∫ q, S.pushforward μ g q ∂ν := by
      congr with q
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
      change (∫ y, g y ∂(quotientCosetMeasure H μ (QuotientGroup.mk x))) =
        S.pushforward μ g (QuotientGroup.mk' H x)
      rw [quotientCosetMeasure_mk, S.pushforward_apply_apply]
      have hf : Measurable (fun h : H => x * (h : G)) :=
        (continuous_const.mul continuous_subtype_val).measurable
      exact integral_map hf.aemeasurable g.continuous.aestronglyMeasurable

include hH in
/-- The lifted measure is invariant under translating by elements of the subgroup. -/
theorem quotientLiftedMeasure_invariant (ν : Measure (G ⧸ H)) (h : H) :
    (quotientLiftedMeasure H μ ν).map (((h : G) * ·) : G → G) =
      quotientLiftedMeasure H μ ν := by
  let κ := quotientCosetMeasure H μ
  have hκ : Measurable κ := quotientCosetMeasure_measurable H hH μ
  let t : G → G := ((h : G) * ·)
  have ht : Measurable t := (continuous_const.mul continuous_id).measurable
  have hc (q : G ⧸ H) : (κ q).map t = κ q := by
    let f : H → G := fun a => q.out * (a : G)
    have hf : Measurable f := (continuous_const.mul continuous_subtype_val).measurable
    have he : t ∘ f = f ∘ (h * ·) := by
      funext a
      change (h : G) * (q.out * (a : G)) = q.out * ((h * a : H) : G)
      rw [Subgroup.coe_mul, mul_left_comm]
    change (μ.map f).map t = μ.map f
    rw [Measure.map_map ht hf, he, ← Measure.map_map hf
      (measurePreserving_mul_left μ h).measurable, (measurePreserving_mul_left μ h).map_eq]
  ext B hB
  change (ν.bind κ).map t B = ν.bind κ B
  rw [Measure.map_apply ht hB, Measure.bind_apply (ht hB) hκ.aemeasurable,
    Measure.bind_apply hB hκ.aemeasurable]
  apply lintegral_congr
  intro q
  rw [← Measure.map_apply ht hB, hc]


include hH in
/-- A measure whose compact-test integrals exist and have the prescribed
coset normalization equals the lifted measure. -/
theorem quotientLiftedMeasure_unique (ν : Measure (G ⧸ H))
    [IsFiniteMeasureOnCompacts ν] (ρ : Measure G)
    (hnorm : ∀ g : CompactlySupportedContinuousMap G ℝ,
      Integrable g ρ ∧ (∫ x, g x ∂ρ) =
        ∫ q, (TopologicalGroup.IsSES.ofClosedSubgroup H hH).pushforward μ g q ∂ν) :
    ρ = quotientLiftedMeasure H μ ν := by
  letI : IsFiniteMeasureOnCompacts ρ := ⟨by
    intro K hK
    obtain ⟨g, hgK, hgc, _, hg⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen
      hK isOpen_univ (subset_univ K)
    let g' : CompactlySupportedContinuousMap G ℝ := ⟨g, hgc⟩
    calc
      ρ K = ∫⁻ x, K.indicator 1 x ∂ρ := (lintegral_indicator_one hK.measurableSet).symm
      _ ≤ ∫⁻ x, ENNReal.ofReal (g x) ∂ρ := by
        apply lintegral_mono
        intro x
        by_cases hx : x ∈ K
        · simp [hx, hgK hx]
        · simp [hx]
      _ < ⊤ := by
        change (∫⁻ x, ENNReal.ofReal (g' x) ∂ρ) < ⊤
        rw [← ofReal_integral_eq_lintegral_ofReal (hnorm g').1
          (.of_forall fun x => (hg x).1)]
        exact ENNReal.ofReal_lt_top⟩
  letI : PseudoMetrizableSpace G := PseudoMetrizableSpace.of_regularSpace_secondCountableTopology G
  letI : IsFiniteMeasureOnCompacts (quotientLiftedMeasure H μ ν) :=
    quotientLiftedMeasure_finiteOnCompacts H hH μ ν
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro g
  exact (hnorm g).2.trans (quotientLiftedMeasure_integral_compact H hH μ ν g).2.symm

end
end Masullo
