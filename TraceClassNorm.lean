import NuclearTrace
import Mathlib.Logic.Equiv.Nat
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension

open Set Filter Topology TopologicalSpace InnerProductSpace
open scoped InnerProductSpace BigOperators TensorProduct

namespace Masullo

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace RankOneSeries

def mass {ι : Type*} (T : RankOneSeries ι H) : ℝ :=
  ∑' i, ‖T.image i‖ * ‖T.functional i‖

omit [InnerProductSpace ℂ H] [CompleteSpace H] in
theorem mass_nonneg {ι : Type*} (T : RankOneSeries ι H) : 0 ≤ T.mass :=
  tsum_nonneg fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)

def zeroRepresentation : RankOneSeries ℕ H where
  image := 0
  functional := 0
  summableNorm := by simp

omit [CompleteSpace H] in
theorem zeroRepresentation_operator : (zeroRepresentation : RankOneSeries ℕ H).operator = 0 := by
  simp [zeroRepresentation, operator]

omit [InnerProductSpace ℂ H] [CompleteSpace H] in
theorem zeroRepresentation_mass : (zeroRepresentation : RankOneSeries ℕ H).mass = 0 := by
  simp [mass, zeroRepresentation]

def addRepresentation (T U : RankOneSeries ℕ H) : RankOneSeries ℕ H where
  image := Sum.elim T.image U.image ∘ Equiv.natSumNatEquivNat.symm
  functional := Sum.elim T.functional U.functional ∘ Equiv.natSumNatEquivNat.symm
  summableNorm := by
    let r (i : ℕ ⊕ ℕ) := ‖Sum.elim T.image U.image i‖ * ‖Sum.elim T.functional U.functional i‖
    change Summable (r ∘ Equiv.natSumNatEquivNat.symm)
    apply Equiv.natSumNatEquivNat.symm.summable_iff.mpr
    exact Summable.sum r T.summableNorm U.summableNorm

theorem addRepresentation_operator (T U : RankOneSeries ℕ H) :
    (addRepresentation T U).operator = T.operator + U.operator := by
  let r (i : ℕ ⊕ ℕ) := rankOne ℂ (Sum.elim T.image U.image i) (Sum.elim T.functional U.functional i)
  change (∑' i, (r ∘ Equiv.natSumNatEquivNat.symm) i) = _
  simp only [Function.comp_apply]
  rw [Equiv.natSumNatEquivNat.symm.tsum_eq r]
  exact Summable.tsum_sum T.operator_summable U.operator_summable

omit [InnerProductSpace ℂ H] [CompleteSpace H] in
theorem addRepresentation_mass (T U : RankOneSeries ℕ H) :
    (addRepresentation T U).mass = T.mass + U.mass := by
  let r (i : ℕ ⊕ ℕ) := ‖Sum.elim T.image U.image i‖ * ‖Sum.elim T.functional U.functional i‖
  change (∑' i, (r ∘ Equiv.natSumNatEquivNat.symm) i) = _
  simp only [Function.comp_apply]
  rw [Equiv.natSumNatEquivNat.symm.tsum_eq r]
  exact Summable.tsum_sum T.summableNorm U.summableNorm

omit [CompleteSpace H] in
theorem addRepresentation_trace (T U : RankOneSeries ℕ H) :
    (addRepresentation T U).trace = T.trace + U.trace := by
  let r (i : ℕ ⊕ ℕ) := ⟪Sum.elim T.functional U.functional i, Sum.elim T.image U.image i⟫_ℂ
  change (∑' i, (r ∘ Equiv.natSumNatEquivNat.symm) i) = _
  simp only [Function.comp_apply]
  rw [Equiv.natSumNatEquivNat.symm.tsum_eq r]
  exact Summable.tsum_sum T.trace_summable.of_norm U.trace_summable.of_norm

def smulRepresentation (c : ℂ) (T : RankOneSeries ℕ H) : RankOneSeries ℕ H where
  image i := c • T.image i
  functional := T.functional
  summableNorm := by simpa only [norm_smul, mul_assoc] using T.summableNorm.mul_left ‖c‖

theorem smulRepresentation_operator (c : ℂ) (T : RankOneSeries ℕ H) :
    (smulRepresentation c T).operator = c • T.operator := by
  let L : (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H) :=
    c • ContinuousLinearMap.id ℂ (H →L[ℂ] H)
  have he := (T.operator_summable.hasSum.mapL L).tsum_eq
  simpa [L, smulRepresentation, operator, map_smul] using he

omit [CompleteSpace H] in
theorem smulRepresentation_mass (c : ℂ) (T : RankOneSeries ℕ H) :
    (smulRepresentation c T).mass = ‖c‖ * T.mass := by
  simp only [mass, smulRepresentation, norm_smul, mul_assoc, tsum_mul_left]

omit [CompleteSpace H] in
theorem smulRepresentation_trace (c : ℂ) (T : RankOneSeries ℕ H) :
    (smulRepresentation c T).trace = c * T.trace := by
  simp only [trace, smulRepresentation, inner_smul_right, tsum_mul_left]

omit [CompleteSpace H] in
theorem operator_norm_le_mass {ι : Type*} (T : RankOneSeries ι H) : ‖T.operator‖ ≤ T.mass := by
  simpa [operator, mass] using norm_tsum_le_tsum_norm
    (f := fun i => rankOne ℂ (T.image i) (T.functional i))
    (by simpa using T.summableNorm)

omit [CompleteSpace H] in
theorem trace_norm_le_mass {ι : Type*} (T : RankOneSeries ι H) : ‖T.trace‖ ≤ T.mass :=
  (norm_tsum_le_tsum_norm T.trace_summable).trans
    (T.trace_summable.tsum_le_tsum
      (fun _ => (norm_inner_le_norm (𝕜 := ℂ) ..).trans_eq (mul_comm ..))
      T.summableNorm)

omit [CompleteSpace H] in
theorem leftComp_mass_le {ι : Type*} (T : RankOneSeries ι H) (A : H →L[ℂ] H) :
    (T.leftComp A).mass ≤ ‖A‖ * T.mass := by
  rw [mass, mass, ← tsum_mul_left]
  exact (T.leftComp A).summableNorm.tsum_le_tsum
    (fun i => by
      simpa only [leftComp, mul_assoc] using
        mul_le_mul_of_nonneg_right (A.le_opNorm (T.image i)) (norm_nonneg (T.functional i)))
    (T.summableNorm.mul_left ‖A‖)

theorem rightComp_mass_le {ι : Type*} (T : RankOneSeries ι H) (A : H →L[ℂ] H) :
    (T.rightComp A).mass ≤ ‖A‖ * T.mass := by
  rw [mass, mass, ← tsum_mul_left]
  exact (T.rightComp A).summableNorm.tsum_le_tsum
    (fun i => by
      have h := mul_le_mul_of_nonneg_left (A.adjoint.le_opNorm (T.functional i))
        (norm_nonneg (T.image i))
      rw [ContinuousLinearMap.adjoint.norm_map] at h
      simpa only [rightComp, mul_left_comm] using h)
    (T.summableNorm.mul_left ‖A‖)

def singleRepresentation (u v : H) : RankOneSeries ℕ H where
  image i := if i = 0 then u else 0
  functional _ := v
  summableNorm := by
    apply summable_of_ne_finset_zero (s := {0})
    intro i hi
    simp [show i ≠ 0 by simpa using hi]

omit [CompleteSpace H] in
theorem singleRepresentation_operator (u v : H) :
    (singleRepresentation u v).operator = rankOne ℂ u v := by
  unfold operator
  rw [tsum_eq_single 0]
  · simp [singleRepresentation]
  · intro i hi
    simp [singleRepresentation, hi]

omit [InnerProductSpace ℂ H] [CompleteSpace H] in
theorem singleRepresentation_mass (u v : H) :
    (singleRepresentation u v).mass = ‖u‖ * ‖v‖ := by
  unfold mass
  rw [tsum_eq_single 0]
  · simp [singleRepresentation]
  · intro i hi
    simp [singleRepresentation, hi]

def tailRepresentation (T : RankOneSeries ℕ H) (S : Finset ℕ) : RankOneSeries ℕ H :=
  { image := (↑S : Set ℕ)ᶜ.indicator T.image
    functional := T.functional
    summableNorm := by
      have heq : (fun i => ‖(↑S : Set ℕ)ᶜ.indicator T.image i‖ * ‖T.functional i‖) =
          (↑S : Set ℕ)ᶜ.indicator (fun i => ‖T.image i‖ * ‖T.functional i‖) := by
        funext i
        by_cases hi : i ∈ (↑S : Set ℕ)ᶜ <;> simp [indicator_of_mem, indicator_of_notMem, hi]
      rw [heq]
      exact T.summableNorm.indicator _ }

omit [InnerProductSpace ℂ H] [CompleteSpace H] in
theorem tailRepresentation_mass (T : RankOneSeries ℕ H) (S : Finset ℕ) :
    (T.tailRepresentation S).mass = ∑' i : {i // i ∉ (S : Set ℕ)}, ‖T.image i‖ * ‖T.functional i‖ := by
  let f (i : ℕ) := ‖T.image i‖ * ‖T.functional i‖
  calc
    _ = ∑' i : ℕ, (↑S : Set ℕ)ᶜ.indicator f i := by
      apply tsum_congr
      intro i
      by_cases hi : i ∈ (↑S : Set ℕ)ᶜ <;>
        simp [tailRepresentation, f, hi, indicator_of_mem, indicator_of_notMem]
    _ = _ := (tsum_subtype ((↑S : Set ℕ)ᶜ) f).symm

theorem tailRepresentation_operator (T : RankOneSeries ℕ H) (S : Finset ℕ) :
    (T.tailRepresentation S).operator = T.operator - ∑ i ∈ S, rankOne ℂ (T.image i) (T.functional i) := by
  let f (i : ℕ) := rankOne ℂ (T.image i) (T.functional i)
  have hh : (T.tailRepresentation S).operator = ∑' i : {i // i ∉ (S : Set ℕ)}, f i := by
    calc
      _ = ∑' i : ℕ, (↑S : Set ℕ)ᶜ.indicator f i := by
        apply tsum_congr
        intro i
        by_cases hi : i ∈ (↑S : Set ℕ)ᶜ <;>
          simp [tailRepresentation, f, hi, indicator_of_mem, indicator_of_notMem]
      _ = _ := (tsum_subtype ((↑S : Set ℕ)ᶜ) f).symm
  rw [hh]
  have hj := T.operator_summable.sum_add_tsum_subtype_compl S
  change (∑ i ∈ S, f i) + (∑' i : {i // i ∉ (S : Set ℕ)}, f i) = T.operator at hj
  rw [← hj]
  abel

end RankOneSeries

/-- The subspace of operators with a countable absolutely summable
rank-one representation. -/
def nuclearOperators (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] :
    Submodule ℂ (H →L[ℂ] H) where
  carrier := {A | ∃ T : RankOneSeries ℕ H, T.operator = A}
  zero_mem' := ⟨_, RankOneSeries.zeroRepresentation_operator⟩
  add_mem' := by
    rintro _ _ ⟨T, rfl⟩ ⟨U, rfl⟩
    exact ⟨_, T.addRepresentation_operator U⟩
  smul_mem' := by
    rintro c _ ⟨T, rfl⟩
    exact ⟨_, T.smulRepresentation_operator c⟩

theorem nuclearOperators_comp_left (A : H →L[ℂ] H) {T : H →L[ℂ] H}
    (hT : T ∈ nuclearOperators H) : A.comp T ∈ nuclearOperators H := by
  obtain ⟨R, rfl⟩ := hT
  exact ⟨_, R.operator_leftComp A⟩

theorem nuclearOperators_comp_right (A : H →L[ℂ] H) {T : H →L[ℂ] H}
    (hT : T ∈ nuclearOperators H) : T.comp A ∈ nuclearOperators H := by
  obtain ⟨R, rfl⟩ := hT
  exact ⟨_, R.operator_rightComp A⟩

omit [CompleteSpace H] in
private theorem nuclearTraceNorm_zero : nuclearTraceNorm (0 : H →L[ℂ] H) = 0 := by
  apply le_antisymm _ (nuclearTraceNorm_nonneg _)
  let R : RankOneSeries ℕ H := RankOneSeries.zeroRepresentation
  have h : nuclearTraceNorm R.operator ≤ R.mass := nuclearTraceNorm_le_representation R
  simpa only [R, RankOneSeries.zeroRepresentation_operator, RankOneSeries.zeroRepresentation_mass] using h

private theorem exists_representation_mass_lt {T : H →L[ℂ] H} (hT : T ∈ nuclearOperators H)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ R : RankOneSeries ℕ H, R.operator = T ∧ R.mass < nuclearTraceNorm T + ε := by
  obtain ⟨R, hR⟩ := hT
  obtain ⟨m, ⟨S, hS, hm⟩, hlt⟩ := exists_lt_of_csInf_lt
    (s := {m | ∃ R : RankOneSeries ℕ H, R.operator = T ∧ m = R.mass})
    ⟨R.mass, R, hR, rfl⟩ (lt_add_of_pos_right (nuclearTraceNorm T) hε)
  exact ⟨S, hS, hm ▸ hlt⟩

theorem opNorm_le_nuclearTraceNorm {T : H →L[ℂ] H} (hT : T ∈ nuclearOperators H) :
    ‖T‖ ≤ nuclearTraceNorm T := by
  unfold nuclearTraceNorm
  apply le_csInf
  · obtain ⟨R, hR⟩ := hT
    exact ⟨R.mass, R, hR, rfl⟩
  · rintro _ ⟨R, rfl, rfl⟩
    exact R.operator_norm_le_mass

private theorem nuclearTraceNorm_add_le {T U : H →L[ℂ] H}
    (hT : T ∈ nuclearOperators H) (hU : U ∈ nuclearOperators H) :
    nuclearTraceNorm (T + U) ≤ nuclearTraceNorm T + nuclearTraceNorm U := by
  by_contra! h
  let ε := (nuclearTraceNorm (T + U) - (nuclearTraceNorm T + nuclearTraceNorm U)) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  obtain ⟨A, hA, hAM⟩ := exists_representation_mass_lt hT hε
  obtain ⟨B, hB, hBM⟩ := exists_representation_mass_lt hU hε
  have he := nuclearTraceNorm_le_representation (A.addRepresentation B)
  change nuclearTraceNorm (A.addRepresentation B).operator ≤ (A.addRepresentation B).mass at he
  rw [RankOneSeries.addRepresentation_operator, hA, hB, RankOneSeries.addRepresentation_mass] at he
  dsimp [ε] at hAM hBM
  linarith

private theorem nuclearTraceNorm_bound_by_scaled_mass {T U : H →L[ℂ] H}
    (hT : T ∈ nuclearOperators H) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ R : RankOneSeries ℕ H, R.operator = T → nuclearTraceNorm U ≤ C * R.mass) :
    nuclearTraceNorm U ≤ C * nuclearTraceNorm T := by
  by_cases hz : C = 0
  · obtain ⟨R, hR⟩ := hT
    simpa [hz] using h R hR
  · have hp : 0 < C := lt_of_le_of_ne hC (Ne.symm hz)
    by_contra! hlt
    let ε := (nuclearTraceNorm U - C * nuclearTraceNorm T) / C
    have hε : 0 < ε := div_pos (sub_pos.mpr hlt) hp
    obtain ⟨R, hR, hmass⟩ := exists_representation_mass_lt hT hε
    have hk := (h R hR).trans_lt (mul_lt_mul_of_pos_left hmass hp)
    dsimp [ε] at hk
    rw [mul_add, mul_div_cancel₀ _ hz] at hk
    linarith

theorem nuclearTraceNorm_comp_left_le (A : H →L[ℂ] H) {T : H →L[ℂ] H}
    (hT : T ∈ nuclearOperators H) :
    nuclearTraceNorm (A.comp T) ≤ ‖A‖ * nuclearTraceNorm T := by
  apply nuclearTraceNorm_bound_by_scaled_mass hT _ (norm_nonneg _)
  rintro R rfl
  rw [← R.operator_leftComp A]
  exact (nuclearTraceNorm_le_representation _).trans (R.leftComp_mass_le A)

theorem nuclearTraceNorm_comp_right_le (A : H →L[ℂ] H) {T : H →L[ℂ] H}
    (hT : T ∈ nuclearOperators H) :
    nuclearTraceNorm (T.comp A) ≤ ‖A‖ * nuclearTraceNorm T := by
  apply nuclearTraceNorm_bound_by_scaled_mass hT _ (norm_nonneg _)
  rintro R rfl
  rw [← R.operator_rightComp A]
  exact (nuclearTraceNorm_le_representation _).trans (R.rightComp_mass_le A)

private theorem nuclearTraceNorm_smul_le (c : ℂ) {T : H →L[ℂ] H}
    (hT : T ∈ nuclearOperators H) :
    nuclearTraceNorm (c • T) ≤ ‖c‖ * nuclearTraceNorm T := by
  apply nuclearTraceNorm_bound_by_scaled_mass hT _ (norm_nonneg _)
  rintro R rfl
  rw [← R.smulRepresentation_operator c, ← R.smulRepresentation_mass c]
  exact nuclearTraceNorm_le_representation _

private theorem nuclearTraceNorm_smul (c : ℂ) {T : H →L[ℂ] H}
    (hT : T ∈ nuclearOperators H) :
    nuclearTraceNorm (c • T) = ‖c‖ * nuclearTraceNorm T := by
  apply le_antisymm (nuclearTraceNorm_smul_le c hT)
  by_cases hc : c = 0
  · rw [hc, zero_smul, norm_zero, zero_mul, nuclearTraceNorm_zero]
  · have h := nuclearTraceNorm_smul_le c⁻¹ ((nuclearOperators H).smul_mem c hT)
    rw [smul_smul, inv_mul_cancel₀ hc, one_smul, norm_inv, ← div_eq_inv_mul] at h
    simpa [mul_comm] using (le_div_iff₀ (norm_pos_iff.mpr hc)).mp h

/-- The nuclear operators with their own norm topology. -/
def TraceClass (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] :=
  ↥(nuclearOperators H)

namespace TraceClass

instance : AddCommGroup (TraceClass H) :=
  inferInstanceAs (AddCommGroup ↥(nuclearOperators H))

instance : Module ℂ (TraceClass H) :=
  inferInstanceAs (Module ℂ ↥(nuclearOperators H))

def toOperator (T : TraceClass H) : H →L[ℂ] H :=
  (show ↥(nuclearOperators H) from T).val

theorem toOperator_mem (T : TraceClass H) : T.toOperator ∈ nuclearOperators H :=
  (show ↥(nuclearOperators H) from T).property

theorem toOperator_injective : Function.Injective (toOperator (H := H)) :=
  Subtype.val_injective

def ofSeries (T : RankOneSeries ℕ H) : TraceClass H :=
  (⟨T.operator, T, rfl⟩ : ↥(nuclearOperators H))

instance : Norm (TraceClass H) := ⟨fun T => nuclearTraceNorm T.toOperator⟩

private theorem normedSpaceCore : NormedSpace.Core ℂ (TraceClass H) where
  norm_nonneg T := nuclearTraceNorm_nonneg T.toOperator
  norm_smul c T := nuclearTraceNorm_smul c T.toOperator_mem
  norm_triangle T U := nuclearTraceNorm_add_le T.toOperator_mem U.toOperator_mem
  norm_eq_zero_iff T := by
    constructor
    · intro h
      apply toOperator_injective
      change T.toOperator = 0
      have hn := opNorm_le_nuclearTraceNorm T.toOperator_mem
      change nuclearTraceNorm T.toOperator = 0 at h
      rw [h] at hn
      exact norm_le_zero_iff.mp hn
    · rintro rfl
      exact nuclearTraceNorm_zero

instance : NormedAddCommGroup (TraceClass H) := .ofCore normedSpaceCore

instance : NormedSpace ℂ (TraceClass H) := .ofCore normedSpaceCore

theorem norm_ofSeries_le (T : RankOneSeries ℕ H) : ‖ofSeries T‖ ≤ T.mass :=
  nuclearTraceNorm_le_representation T

private def representation (T : TraceClass H) : RankOneSeries ℕ H :=
  Classical.choose T.toOperator_mem

private theorem representation_operator (T : TraceClass H) : T.representation.operator = T.toOperator :=
  Classical.choose_spec T.toOperator_mem

/-- The scalar trace is independent of the representation. -/
def traceValue (T : TraceClass H) : ℂ := T.representation.trace

theorem traceValue_eq_of_operator (T : TraceClass H) (S : RankOneSeries ℕ H)
    (h : S.operator = T.toOperator) : T.traceValue = S.trace :=
  RankOneSeries.trace_eq_of_operator_eq ((representation_operator T).trans h.symm)

theorem traceValue_ofSeries (S : RankOneSeries ℕ H) : (ofSeries S).traceValue = S.trace :=
  traceValue_eq_of_operator _ S rfl

theorem norm_traceValue_le (T : TraceClass H) : ‖T.traceValue‖ ≤ ‖T‖ := by
  change ‖T.traceValue‖ ≤ nuclearTraceNorm T.toOperator
  unfold nuclearTraceNorm
  apply le_csInf
  · exact ⟨T.representation.mass, T.representation, representation_operator T, rfl⟩
  · rintro _ ⟨S, hS, rfl⟩
    rw [traceValue_eq_of_operator _ S hS]
    exact S.trace_norm_le_mass

def traceCLM : TraceClass H →L[ℂ] ℂ := by
  let ℓ : TraceClass H →ₗ[ℂ] ℂ :=
    { toFun := traceValue
      map_add' := by
        intro T U
        have he : (T.representation.addRepresentation U.representation).operator = (T + U).toOperator := by
          rw [RankOneSeries.addRepresentation_operator, representation_operator, representation_operator]
          rfl
        rw [traceValue_eq_of_operator _ _ he, RankOneSeries.addRepresentation_trace]
        rfl
      map_smul' := by
        intro c T
        have he : (T.representation.smulRepresentation c).operator = (c • T).toOperator := by
          rw [RankOneSeries.smulRepresentation_operator, representation_operator]
          rfl
        rw [traceValue_eq_of_operator _ _ he, RankOneSeries.smulRepresentation_trace]
        rfl }
  exact ℓ.mkContinuous 1 (fun T => by
    change ‖T.traceValue‖ ≤ 1 * ‖T‖
    simpa only [one_mul] using norm_traceValue_le T)

theorem traceCLM_apply (T : TraceClass H) : traceCLM T = T.traceValue := rfl

/-- Rank-one operators as trace-class operators. -/
def rankOneOperator (u v : H) : TraceClass H := ofSeries (RankOneSeries.singleRepresentation u v)

theorem rankOneOperator_toOperator (u v : H) :
    (rankOneOperator u v).toOperator = rankOne ℂ u v :=
  RankOneSeries.singleRepresentation_operator u v

theorem norm_rankOneOperator_le (u v : H) : ‖rankOneOperator u v‖ ≤ ‖u‖ * ‖v‖ :=
  (norm_ofSeries_le _).trans_eq (RankOneSeries.singleRepresentation_mass u v)

private theorem rankOneOperator_add_left (u u' v : H) :
    rankOneOperator (u + u') v = rankOneOperator u v + rankOneOperator u' v := by
  apply toOperator_injective
  show (rankOneOperator (u + u') v).toOperator =
    (rankOneOperator u v).toOperator + (rankOneOperator u' v).toOperator
  simp [rankOneOperator_toOperator, map_add]

private theorem rankOneOperator_add_right (u v v' : H) :
    rankOneOperator u (v + v') = rankOneOperator u v + rankOneOperator u v' := by
  apply toOperator_injective
  show (rankOneOperator u (v + v')).toOperator =
    (rankOneOperator u v).toOperator + (rankOneOperator u v').toOperator
  simp [rankOneOperator_toOperator, map_add]

theorem continuous_rankOneOperator :
    Continuous (fun p : H × H => rankOneOperator p.1 p.2) := by
  refine continuous_iff_continuousAt.mpr fun p => ?_
  have hr : ∀ q : H × H, dist (rankOneOperator q.1 q.2) (rankOneOperator p.1 p.2) ≤
      ‖q.1 - p.1‖ * ‖q.2‖ + ‖p.1‖ * ‖q.2 - p.2‖ := by
    intro q
    rw [dist_eq_norm]
    have h : rankOneOperator q.1 q.2 - rankOneOperator p.1 p.2 =
        rankOneOperator (q.1 - p.1) q.2 + rankOneOperator p.1 (q.2 - p.2) := by
      have h₁ := rankOneOperator_add_left (q.1 - p.1) p.1 q.2
      have h₂ := rankOneOperator_add_right p.1 (q.2 - p.2) p.2
      rw [sub_add_cancel] at h₁ h₂
      rw [h₁, h₂]
      abel
    rw [h]
    exact (norm_add_le _ _).trans (add_le_add (norm_rankOneOperator_le ..) (norm_rankOneOperator_le ..))
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero (fun _ => dist_nonneg) hr
  have hc : Continuous (fun q : H × H =>
      ‖q.1 - p.1‖ * ‖q.2‖ + ‖p.1‖ * ‖q.2 - p.2‖) := by fun_prop
  simpa using hc.continuousAt (x := p) |>.tendsto

theorem dense_finite_rank_sums :
    Dense {T : TraceClass H | ∃ (S : Finset ℕ) (u v : ℕ → H),
      T = ∑ i ∈ S, rankOneOperator (u i) (v i)} := by
  rw [Metric.dense_iff]
  intro T ε hε
  let R := T.representation
  have he := (tendsto_order.mp (tendsto_tsum_compl_atTop_zero (fun i => ‖R.image i‖ * ‖R.functional i‖))).2 ε hε
  obtain ⟨S, hS⟩ := he.exists
  let F : TraceClass H := ∑ i ∈ S, rankOneOperator (R.image i) (R.functional i)
  refine ⟨F, ?_, ⟨S, R.image, R.functional, rfl⟩⟩
  rw [Metric.mem_ball, dist_comm, dist_eq_norm]
  have hh : T - F = ofSeries (R.tailRepresentation S) := by
    apply toOperator_injective
    have hsum : F.toOperator = ∑ i ∈ S, rankOne ℂ (R.image i) (R.functional i) := by
      let j : TraceClass H →+ (H →L[ℂ] H) := ⟨⟨toOperator, rfl⟩, fun _ _ => rfl⟩
      change j (∑ i ∈ S, rankOneOperator (R.image i) (R.functional i)) = _
      rw [map_sum]
      exact Finset.sum_congr rfl fun _ _ => rankOneOperator_toOperator _ _
    change T.toOperator - F.toOperator = (R.tailRepresentation S).operator
    rw [RankOneSeries.tailRepresentation_operator, hsum, representation_operator T]
  rw [hh]
  exact (norm_ofSeries_le _).trans_lt (by rw [RankOneSeries.tailRepresentation_mass]; exact hS)

private def finiteRankStage (n : ℕ) (v : Fin n → H × H) : TraceClass H :=
  ∑ i, rankOneOperator (v i).1 (v i).2

private theorem dense_iUnion_finiteRankStage :
    Dense (⋃ n : ℕ, range (finiteRankStage (H := H) n)) := by
  apply dense_finite_rank_sums.mono
  rintro T ⟨S, u, v, rfl⟩
  classical
  let e := S.equivFin.symm
  let b (i : Fin S.card) : H × H := (u (e i), v (e i))
  apply mem_iUnion.mpr
  refine ⟨S.card, b, ?_⟩
  change (∑ i : Fin S.card, rankOneOperator (u (e i)) (v (e i))) = _
  rw [Equiv.sum_comp e (fun i : S => rankOneOperator (u i) (v i))]
  exact Finset.sum_attach S (fun i => rankOneOperator (u i) (v i))

theorem separableSpace_of_separable [SeparableSpace H] : SeparableSpace (TraceClass H) := by
  have hs (n : ℕ) : IsSeparable (range (finiteRankStage (H := H) n)) := by
    apply isSeparable_range
    unfold finiteRankStage
    apply continuous_finsetSum
    intro i hi
    exact continuous_rankOneOperator.comp (continuous_apply i)
  have hS := IsSeparable.iUnion hs
  obtain ⟨D, hcD, hcl⟩ := hS
  exact ⟨D, hcD, dense_iff_closure_eq.mpr (eq_univ_of_forall fun x => 
    have he : x ∈ closure (⋃ n : ℕ, range (finiteRankStage (H := H) n)) :=
      dense_iUnion_finiteRankStage x
    (closure_minimal hcl isClosed_closure) he)⟩

/-- Left composition, as a linear operation on the nuclear ideal. -/
def leftCompose (A : H →L[ℂ] H) : TraceClass H →ₗ[ℂ] TraceClass H where
  toFun T := (⟨A.comp T.toOperator, nuclearOperators_comp_left A T.toOperator_mem⟩ : ↥(nuclearOperators H))
  map_add' T U := by
    apply toOperator_injective
    change A.comp (T.toOperator + U.toOperator) = A.comp T.toOperator + A.comp U.toOperator
    exact ContinuousLinearMap.comp_add A _ _
  map_smul' c T := by
    apply toOperator_injective
    change A.comp (c • T.toOperator) = c • A.comp T.toOperator
    exact ContinuousLinearMap.comp_smul A c _

theorem leftCompose_toOperator (A : H →L[ℂ] H) (T : TraceClass H) :
    (leftCompose A T).toOperator = A.comp T.toOperator := rfl

theorem norm_leftCompose_le (A : H →L[ℂ] H) (T : TraceClass H) :
    ‖leftCompose A T‖ ≤ ‖A‖ * ‖T‖ :=
  nuclearTraceNorm_comp_left_le A T.toOperator_mem

theorem leftCompose_rankOneOperator (A : H →L[ℂ] H) (u v : H) :
    leftCompose A (rankOneOperator u v) = rankOneOperator (A u) v := by
  apply toOperator_injective
  rw [leftCompose_toOperator, rankOneOperator_toOperator, rankOneOperator_toOperator, comp_rankOne]

theorem finiteRank_operator_decomposition (A : H →L[ℂ] H)
    [FiniteDimensional ℂ (LinearMap.range A.toLinearMap)] :
    ∃ n : ℕ, ∃ u v : Fin n → H, A = ∑ i, rankOne ℂ (u i) (v i) := by
  let R := LinearMap.range A.toLinearMap
  let b := stdOrthonormalBasis ℂ R
  let u (i : Fin (Module.finrank ℂ R)) := (b i : H)
  let v (i : Fin (Module.finrank ℂ R)) := A.adjoint (u i)
  refine ⟨Module.finrank ℂ R, u, v, ?_⟩
  ext x
  let y : R := ⟨A x, x, rfl⟩
  have hcoord (i : Fin (Module.finrank ℂ R)) : (b.repr y).ofLp i = ⟪v i, x⟫_ℂ := by
    rw [b.repr_apply_apply]
    change ⟪u i, A x⟫_ℂ = ⟪A.adjoint (u i), x⟫_ℂ
    exact (A.adjoint_inner_left x (u i)).symm
  have hsum := congrArg (fun z : R => (z : H)) (b.sum_repr y)
  simp only [Submodule.coe_sum, Submodule.coe_smul, hcoord] at hsum
  simpa [y, u, v, sum_apply, rankOne_apply] using hsum.symm

/-- Strong convergence to zero after left composition with a finite-rank
operator gives convergence in trace norm. The index is an arbitrary filter. -/
theorem tendsto_leftCompose_finiteRank {ι : Type*} {l : Filter ι}
    (A : ι → H →L[ℂ] H) (F : TraceClass H)
    [FiniteDimensional ℂ (LinearMap.range F.toOperator.toLinearMap)]
    (hA : ∀ x, Tendsto (fun i => A i x) l (𝓝 0)) :
    Tendsto (fun i => leftCompose (A i) F) l (𝓝 0) := by
  obtain ⟨n, u, v, hF⟩ := finiteRank_operator_decomposition F.toOperator
  classical
  have hsum : F = ∑ j, rankOneOperator (u j) (v j) := by
    apply toOperator_injective
    rw [hF]
    let j : TraceClass H →+ (H →L[ℂ] H) := ⟨⟨toOperator, rfl⟩, fun _ _ => rfl⟩
    change _ = j (∑ j, rankOneOperator (u j) (v j))
    rw [map_sum]
    exact Finset.sum_congr rfl fun _ _ => (rankOneOperator_toOperator _ _).symm
  have hterm (j : Fin n) :
      Tendsto (fun i => rankOneOperator (A i (u j)) (v j)) l (𝓝 0) := by
    have hn : Tendsto (fun i => ‖rankOneOperator (A i (u j)) (v j)‖) l (𝓝 0) :=
      squeeze_zero (fun _ => norm_nonneg _) (fun _ => norm_rankOneOperator_le _ _)
        (by simpa using (hA (u j)).norm.mul_const ‖v j‖)
    exact tendsto_zero_iff_norm_tendsto_zero.mpr hn
  have hlim := tendsto_finsetSum Finset.univ (fun j _ => hterm j)
  simpa [hsum, map_sum, leftCompose_rankOneOperator] using hlim

private def dualRankOne (ℓ : StrongDual ℂ H) (u : H) : TraceClass H :=
  rankOneOperator u ((InnerProductSpace.toDual ℂ H).symm ℓ)

private theorem dualRankOne_toOperator (ℓ : StrongDual ℂ H) (u : H) :
    (dualRankOne ℓ u).toOperator = ℓ.smulRight u := by
  rw [dualRankOne, rankOneOperator_toOperator]
  ext x
  have h := DFunLike.congr_fun ((InnerProductSpace.toDual ℂ H).apply_symm_apply ℓ) x
  rw [InnerProductSpace.toDual_apply_apply] at h
  rw [rankOne_apply, h]
  rfl

/-- The canonical map from the algebraic tensor product of the continuous
dual and the Hilbert space. Its elementary tensors are rank-one operators. -/
def tensorToTraceClass : StrongDual ℂ H ⊗[ℂ] H →ₗ[ℂ] TraceClass H :=
  TensorProduct.lift (LinearMap.mk₂ ℂ dualRankOne
    (fun a b u => by
      apply toOperator_injective
      change (dualRankOne (a + b) u).toOperator =
        (dualRankOne a u).toOperator + (dualRankOne b u).toOperator
      simp only [dualRankOne_toOperator]
      ext x
      simp [add_smul])
    (fun c ℓ u => by
      apply toOperator_injective
      change (dualRankOne (c • ℓ) u).toOperator = c • (dualRankOne ℓ u).toOperator
      simp only [dualRankOne_toOperator]
      ext x
      simp [smul_smul])
    (fun ℓ u v => by
      apply toOperator_injective
      change (dualRankOne ℓ (u + v)).toOperator =
        (dualRankOne ℓ u).toOperator + (dualRankOne ℓ v).toOperator
      simp only [dualRankOne_toOperator]
      ext x
      simp [smul_add])
    (fun c ℓ u => by
      apply toOperator_injective
      change (dualRankOne ℓ (c • u)).toOperator = c • (dualRankOne ℓ u).toOperator
      simp only [dualRankOne_toOperator]
      ext x
      simp [smul_comm c]))

theorem tensorToTraceClass_tmul (ℓ : StrongDual ℂ H) (u : H) :
    (tensorToTraceClass (ℓ ⊗ₜ[ℂ] u)).toOperator = ℓ.smulRight u := by
  rw [tensorToTraceClass, TensorProduct.lift.tmul, LinearMap.mk₂_apply]
  exact dualRankOne_toOperator ℓ u

theorem denseRange_tensorToTraceClass : DenseRange (tensorToTraceClass (H := H)) := by
  apply dense_finite_rank_sums.mono
  rintro T ⟨S, u, v, rfl⟩
  refine ⟨∑ i ∈ S, InnerProductSpace.toDual ℂ H (v i) ⊗ₜ[ℂ] u i, ?_⟩
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply toOperator_injective
  rw [tensorToTraceClass_tmul, rankOneOperator_toOperator]
  rfl

end TraceClass

/-- The equality of the two trace norms printed in C.3.4.4(2) already
fails for rank-one operators on a two-dimensional Hilbert space. -/
theorem nuclearTraceNorm_composition_inequality_obstruction :
    ∃ A T : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2),
      T ∈ nuclearOperators (EuclideanSpace ℂ (Fin 2)) ∧
      nuclearTraceNorm (A.comp T) ≠ nuclearTraceNorm (T.comp A) := by
  let H := EuclideanSpace ℂ (Fin 2)
  let b := EuclideanSpace.basisFun (Fin 2) ℂ
  let u : H := b 0
  let v : H := b 1
  let A : H →L[ℂ] H := rankOne ℂ u v
  let T : H →L[ℂ] H := rankOne ℂ u u
  have hu : ‖u‖ = 1 := b.orthonormal.norm_eq_one 0
  have hv : ‖v‖ = 1 := b.orthonormal.norm_eq_one 1
  have horth : ⟪v, u⟫_ℂ = 0 := b.orthonormal.inner_eq_zero (by decide : (1 : Fin 2) ≠ 0)
  have hself : ⟪u, u⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K, hu]; norm_num
  have hAT : A.comp T = 0 := by
    change rankOne ℂ u v ∘L rankOne ℂ u u = 0
    rw [rankOne_comp_rankOne, horth, zero_smul]
  have hTA : T.comp A = A := by
    change rankOne ℂ u u ∘L rankOne ℂ u v = A
    rw [rankOne_comp_rankOne, hself, one_smul]
  have hA : A ∈ nuclearOperators H := ⟨_, RankOneSeries.singleRepresentation_operator u v⟩
  have hT : T ∈ nuclearOperators H := ⟨_, RankOneSeries.singleRepresentation_operator u u⟩
  have hpos : 0 < nuclearTraceNorm A := by
    have hn : ‖A‖ = 1 := by change ‖rankOne ℂ u v‖ = 1; simp [hu, hv]
    exact lt_of_lt_of_le (hn ▸ zero_lt_one) (opNorm_le_nuclearTraceNorm hA)
  exact ⟨A, T, hT, by rw [hAT, hTA, nuclearTraceNorm_zero]; exact hpos.ne⟩


end

end Masullo
