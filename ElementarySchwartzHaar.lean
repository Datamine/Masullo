import ElementarySchwartzLp
import Mathlib.MeasureTheory.Measure.Haar.Unique

open Function MeasureTheory Set Topology
open scoped ENNReal NNReal

namespace Masullo

noncomputable section

private theorem count_isAddHaarMeasure_of_discrete {A : Type*} [AddGroup A]
    [TopologicalSpace A] [DiscreteTopology A] [MeasurableSpace A] [BorelSpace A] :
    (Measure.count : Measure A).IsAddHaarMeasure where
  lt_top_of_isCompact := fun {_} h => (Measure.count_apply_lt_top).2 h.finite_of_discrete
  map_add_left_eq_self a := by
    have hf : Measurable (a + · : A → A) := continuous_of_discreteTopology.measurable
    have hi : Injective (a + · : A → A) := fun _ _ h => add_left_cancel h
    have hs : Surjective (a + · : A → A) := fun x => ⟨-a + x, by simp⟩
    ext s h
    rw [Measure.map_apply hf h, Measure.count_apply (h.preimage hf), Measure.count_apply h,
      ← hi.encard_image, hs.image_preimage]
  open_pos s _ h := by
    obtain ⟨x, hx⟩ := h
    have hle := measure_mono (μ := (Measure.count : Measure A)) (singleton_subset_iff.mpr hx)
    rw [Measure.count_singleton] at hle
    exact (zero_lt_one.trans_le hle).ne'

variable {m n r : ℕ} {F : Type*} [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F]
  [Finite F] [MeasurableSpace F] [BorelSpace F]

local notation "A" => ElementaryLCAModel m n r F
local notation "E" => ElementarySchwartz m n r F
local notation "μ" => elementaryProductHaar m n r F
local notation "Directions" => List (Multiplicative ℝ →ₜ* Multiplicative A)
local notation "DualDirections" => List (Multiplicative ℝ →ₜ* PontryaginDual (Multiplicative A))
local notation "Operators" => List (ℂ × Directions)
local notation "DualOperators" => List (ℂ × DualDirections)

theorem elementaryProductHaar_isAddHaarMeasure : (μ : Measure A).IsAddHaarMeasure := by
  letI : BorelSpace ((Fin r → ℤ) × F) := Prod.borelSpace
  letI : BorelSpace ((Fin n → AddCircle (1 : ℝ)) × (Fin r → ℤ) × F) := Prod.borelSpace
  letI : MeasurableAdd ((Fin n → AddCircle (1 : ℝ)) × (Fin r → ℤ) × F) :=
    ContinuousAdd.measurableAdd
  letI : (Measure.count : Measure (Fin r → ℤ)).IsAddHaarMeasure :=
    count_isAddHaarMeasure_of_discrete
  letI : (Measure.count : Measure F).IsAddHaarMeasure :=
    count_isAddHaarMeasure_of_discrete
  let ν := (Measure.count : Measure (Fin r → ℤ)).prod (Measure.count : Measure F)
  letI : ν.IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  let τ := (volume : Measure (Fin n → AddCircle (1 : ℝ))).prod ν
  letI : τ.IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  exact Measure.prod.instIsAddHaarMeasure _ τ

/-- Any additive Haar normalization on the elementary product is a positive
multiple of the explicit coordinate measure. -/
theorem elementaryHaar_eq_smul (ν : Measure A) [ν.IsAddHaarMeasure] :
    ∃ c : ℝ≥0, 0 < c ∧ ν = c • μ := by
  letI : BorelSpace ((Fin r → ℤ) × F) := Prod.borelSpace
  letI : BorelSpace ((Fin n → AddCircle (1 : ℝ)) × (Fin r → ℤ) × F) := Prod.borelSpace
  letI : BorelSpace A := Prod.borelSpace
  letI : (μ : Measure A).IsAddHaarMeasure := elementaryProductHaar_isAddHaarMeasure
  exact ⟨Measure.addHaarScalarFactor ν μ, Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure ν μ,
    Measure.isAddLeftInvariant_eq_smul ν μ⟩

omit [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [Finite F]
  [MeasurableSpace F] [BorelSpace F] in
theorem elementarySchwartz_withSeminorms_const_smul {J : Type*}
    (q : J → Seminorm ℂ E) (h : WithSeminorms q) {c : ℝ≥0} (hc : 0 < c) :
    WithSeminorms (fun j => c • q j) := by
  classical
  refine h.congr ?_ ?_
  · intro j
    exact ⟨{j}, c, by rw [Finset.sup_singleton]; exact le_rfl⟩
  · intro j
    refine ⟨{j}, c⁻¹, ?_⟩
    rw [Finset.sup_singleton, smul_smul, inv_mul_cancel₀ hc.ne', one_smul]
    exact le_rfl

theorem elementarySchwartz_weightedOperator_memLp_haar
    (ν : Measure A) [ν.IsAddHaarMeasure] (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (P : Operators) (Q : DualOperators) (f : E) :
    MemLp (elementarySchwartz_weightedOperator P Q f) p ν := by
  obtain ⟨c, _, hν⟩ := elementaryHaar_eq_smul ν
  rw [hν]
  exact (elementarySchwartz_weightedOperator_memLp P Q p f).smul_measure ENNReal.coe_ne_top

/-- For every Haar measure the operator Lᵖ norms generate the elementary
Schwartz topology. The positive factor is independent of the operator. -/
theorem elementarySchwartz_withSeminorms_weightedOperatorLp_haar
    (ν : Measure A) [ν.IsAddHaarMeasure] (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    ∃ q : SeminormFamily ℂ E (Operators × DualOperators), WithSeminorms q ∧
      ∀ i f, q i f = lpNorm (elementarySchwartz_weightedOperator i.1 i.2 f) p ν := by
  obtain ⟨c, hc, hν⟩ := elementaryHaar_eq_smul ν
  let t : ℝ≥0 := c ^ p.toReal⁻¹
  let q (i : Operators × DualOperators) :=
    (normSeminorm ℂ (Lp ℂ p μ)).comp
      (elementarySchwartz_weightedOperatorLp i.1 i.2 p).toLinearMap
  have hq : WithSeminorms q := elementarySchwartz_withSeminorms_weightedOperatorLp p
  have ht : 0 < t := by dsimp [t]; positivity
  refine ⟨fun i => t • q i, elementarySchwartz_withSeminorms_const_smul q hq ht, fun i f => ?_⟩
  rw [hν, lpNorm_smul_measure_of_ne_zero hc.ne']
  change (t : ℝ) * ‖elementarySchwartz_weightedOperatorLp i.1 i.2 p f‖ =
    (t : ℝ) * lpNorm (elementarySchwartz_weightedOperator i.1 i.2 f) p μ
  rw [elementarySchwartz_weightedOperatorLp_norm]

end
end Masullo
