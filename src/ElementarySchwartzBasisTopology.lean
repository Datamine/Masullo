import ElementaryInvariantBases
import ElementarySchwartzHaar
import PolynomialLpSeminorms

open Function MeasureTheory Module Set Topology
open scoped ENNReal NNReal

namespace Masullo

noncomputable section

variable {m n r : ℕ} {F : Type*} [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F]
  [Finite F]

local notation "A" => ElementaryLCAModel m n r F
local notation "E" => ElementarySchwartz m n r F
local notation "X" => EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)
local notation "Directions" => List (Multiplicative ℝ →ₜ* Multiplicative A)
local notation "DualDirections" => List (Multiplicative ℝ →ₜ* PontryaginDual (Multiplicative A))
local notation "Operators" => List (ℂ × Directions)
local notation "DualOperators" => List (ℂ × DualDirections)

private theorem exists_linearCombination_of_list {J K Y : Type*}
    (u : J → Y → ℂ) (v : K → Y → ℂ)
    (h : ∀ j, ∃ L : List (ℂ × K), ∀ y, u j y = (L.map fun (c, k) => c * v k y).sum)
    (P : List (ℂ × J)) :
    ∃ L : List (ℂ × K), ∀ y,
      (P.map fun (c, j) => c * u j y).sum = (L.map fun (c, k) => c * v k y).sum := by
  induction P with
  | nil => exact ⟨[], fun _ => rfl⟩
  | cons p P ih =>
    rcases p with ⟨c, j⟩
    obtain ⟨T, hT⟩ := h j
    obtain ⟨L, hL⟩ := ih
    refine ⟨T.map (fun (c', k) => (c * c', k)) ++ L, fun y => ?_⟩
    simp only [List.map_cons, List.sum_cons, hT, hL, List.map_append, List.sum_append,
      List.map_map, ← List.sum_map_mul_left, Function.comp_def]
    congr 2
    apply List.map_congr_left
    rintro ⟨c', k⟩ _
    exact (mul_assoc _ _ _).symm

private theorem exists_elementarySchwartz_weightedOperator_basisExpansion
    {d e : ℕ} (B : Basis (Fin d) ℝ X) (C : Basis (Fin e) ℝ ((Fin m ⊕ Fin r) → ℝ))
    (P : Operators) (Q : DualOperators) :
    ∃ (P' : List (ℂ × (Fin d → ℕ))) (Q' : List (ℂ × (Fin e → ℕ))),
      elementarySchwartz_weightedOperator P Q =
        elementarySchwartz_weightedOperator
          (P'.map fun (z, a) => (z, (invariantBasisWord a).map
            (fun j => elementaryOneParameter (B j))))
          (Q'.map fun (z, a) => (z, (invariantBasisWord a).map (elementaryDualBasisDirections C))) := by
  let D (a : Fin d → ℕ) : Directions :=
    (invariantBasisWord a).map (fun j => elementaryOneParameter (B j))
  let S (b : Fin e → ℕ) : DualDirections :=
    (invariantBasisWord b).map (elementaryDualBasisDirections C)
  obtain ⟨P', hP⟩ := exists_linearCombination_of_list
    (fun cs (y : E × A) => elementaryOrbitWord cs y.1 y.2)
    (fun a (y : E × A) => elementaryOrbitWord (D a) y.1 y.2)
    (fun cs => by
      obtain ⟨T, hT⟩ := elementaryOrbitWord_exists_basisMonomials B cs
      exact ⟨T, fun y => hT y.1 y.2⟩) P
  obtain ⟨Q', hQ⟩ := exists_linearCombination_of_list
    (fun ds (g : A) => elementaryDualWord ds g)
    (fun b (g : A) => elementaryDualWord (S b) g)
    (elementaryDualWord_exists_basisMonomials C) Q
  refine ⟨P', Q', ?_⟩
  ext f g
  rw [elementarySchwartz_weightedOperator_apply, elementarySchwartz_weightedOperator_apply,
    hP (f, g), hQ g, List.map_map, List.map_map]
  rfl

omit [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [Finite F] in
private theorem linearCombination_mem_span {J K V : Type*}
    [AddCommGroup V] [Module ℂ V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [ContinuousSMul ℂ V] (T : J → K → E →L[ℂ] V)
    (P : List (ℂ × J)) (Q : List (ℂ × K)) :
    ((Q.map fun (d, k) => d • (P.map fun (c, j) => c • T j k).sum).sum :
      E →L[ℂ] V).toLinearMap ∈
      Submodule.span ℂ (Set.range fun i : J × K => (T i.1 i.2).toLinearMap) := by
  let W := Submodule.span ℂ (Set.range fun i : J × K => (T i.1 i.2).toLinearMap)
  have hP (k : K) : ((P.map fun (c, j) => c • T j k).sum : E →L[ℂ] V).toLinearMap ∈ W := by
    induction P with
    | nil => exact W.zero_mem
    | cons x P ih =>
      rcases x with ⟨c, j⟩
      exact W.add_mem (W.smul_mem c (Submodule.subset_span (mem_range_self (j, k)))) ih
  induction Q with
  | nil => exact W.zero_mem
  | cons x Q ih =>
    rcases x with ⟨d, k⟩
    exact W.add_mem (W.smul_mem d (hP k)) ih

/-- Proposition D.1.10.6(3). Supremum norms of the ordered monomials of
arbitrary bases on the group and the dual give the original topology. -/
theorem elementarySchwartz_withSeminorms_basisWords
    {d e : ℕ} (B : Basis (Fin d) ℝ X) (C : Basis (Fin e) ℝ ((Fin m ⊕ Fin r) → ℝ)) :
    WithSeminorms (fun i : (Fin d → ℕ) × (Fin e → ℕ) =>
      (normSeminorm ℂ (BoundedContinuousFunction A ℂ)).comp
        (elementarySchwartz_weightedWord
          ((invariantBasisWord i.1).map (fun j => elementaryOneParameter (B j)))
          ((invariantBasisWord i.2).map (elementaryDualBasisDirections C))).toLinearMap) := by
  let D (a : Fin d → ℕ) : Directions :=
    (invariantBasisWord a).map (fun j => elementaryOneParameter (B j))
  let S (b : Fin e → ℕ) : DualDirections :=
    (invariantBasisWord b).map (elementaryDualBasisDirections C)
  let U (i : Operators × DualOperators) := (elementarySchwartz_weightedOperator i.1 i.2).toLinearMap
  let V (i : (Fin d → ℕ) × (Fin e → ℕ)) :=
    (elementarySchwartz_weightedWord (D i.1) (S i.2)).toLinearMap
  have hspan : Submodule.span ℂ (range U) = Submodule.span ℂ (range V) := by
    apply le_antisymm <;> apply Submodule.span_le.mpr <;> rintro _ ⟨i, rfl⟩
    · obtain ⟨P, Q, h⟩ := exists_elementarySchwartz_weightedOperator_basisExpansion B C i.1 i.2
      change (elementarySchwartz_weightedOperator i.1 i.2).toLinearMap ∈ _
      rw [h]
      change _ ∈ Submodule.span ℂ (range V)
      simp only [elementarySchwartz_weightedOperator, List.map_map, Function.comp_def]
      exact linearCombination_mem_span (fun a b => elementarySchwartz_weightedWord (D a) (S b)) P Q
    · apply Submodule.subset_span
      refine ⟨([(1, D i.1)], [(1, S i.2)]), ?_⟩
      simp [U, V, elementarySchwartz_weightedOperator]
  exact (withNormSeminorms_iff_of_span_eq U V hspan).mp
    elementarySchwartz_withSeminorms_weightedOperator

variable [MeasurableSpace F] [BorelSpace F]

local notation "μ" => elementaryProductHaar m n r F

private theorem weightedOperatorLp_eq_of_weightedOperator_eq
    {P P' : Operators} {Q Q' : DualOperators}
    (h : elementarySchwartz_weightedOperator P Q = elementarySchwartz_weightedOperator P' Q')
    (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    elementarySchwartz_weightedOperatorLp P Q p = elementarySchwartz_weightedOperatorLp P' Q' p := by
  ext f
  have h₁ := elementarySchwartz_weightedOperatorLp_ae P Q p f
  rw [h] at h₁
  exact h₁.trans (elementarySchwartz_weightedOperatorLp_ae P' Q' p f).symm

private theorem elementarySchwartz_withSeminorms_basisWordsLp
    {d e : ℕ} (B : Basis (Fin d) ℝ X) (C : Basis (Fin e) ℝ ((Fin m ⊕ Fin r) → ℝ))
    (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    WithSeminorms (fun i : (Fin d → ℕ) × (Fin e → ℕ) =>
      (normSeminorm ℂ (Lp ℂ p μ)).comp
        (elementarySchwartz_weightedWordLp
          ((invariantBasisWord i.1).map (fun j => elementaryOneParameter (B j)))
          ((invariantBasisWord i.2).map (elementaryDualBasisDirections C)) p).toLinearMap) := by
  let D (a : Fin d → ℕ) : Directions :=
    (invariantBasisWord a).map (fun j => elementaryOneParameter (B j))
  let S (b : Fin e → ℕ) : DualDirections :=
    (invariantBasisWord b).map (elementaryDualBasisDirections C)
  let U (i : Operators × DualOperators) := (elementarySchwartz_weightedOperatorLp i.1 i.2 p).toLinearMap
  let V (i : (Fin d → ℕ) × (Fin e → ℕ)) :=
    (elementarySchwartz_weightedWordLp (D i.1) (S i.2) p).toLinearMap
  have hspan : Submodule.span ℂ (range U) = Submodule.span ℂ (range V) := by
    apply le_antisymm <;> apply Submodule.span_le.mpr <;> rintro _ ⟨i, rfl⟩
    · obtain ⟨P, Q, h⟩ := exists_elementarySchwartz_weightedOperator_basisExpansion B C i.1 i.2
      change (elementarySchwartz_weightedOperatorLp i.1 i.2 p).toLinearMap ∈ _
      rw [weightedOperatorLp_eq_of_weightedOperator_eq h p]
      change _ ∈ Submodule.span ℂ (range V)
      simp only [elementarySchwartz_weightedOperatorLp, List.map_map, Function.comp_def]
      exact linearCombination_mem_span (fun a b => elementarySchwartz_weightedWordLp (D a) (S b) p) P Q
    · apply Submodule.subset_span
      refine ⟨([(1, D i.1)], [(1, S i.2)]), ?_⟩
      simp [U, V, elementarySchwartz_weightedOperatorLp]
  exact (withNormSeminorms_iff_of_span_eq U V hspan).mp
    (elementarySchwartz_withSeminorms_weightedOperatorLp p)

/-- Proposition D.1.10.6(4). The weighted Lᵖ seminorms of the ordered
monomials for arbitrary bases generate the topology, for every Haar measure. -/
theorem elementarySchwartz_withSeminorms_basisWordsLp_haar
    {d e : ℕ} (B : Basis (Fin d) ℝ X) (C : Basis (Fin e) ℝ ((Fin m ⊕ Fin r) → ℝ))
    (ν : Measure A) [ν.IsAddHaarMeasure] (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    ∃ q : SeminormFamily ℂ E ((Fin d → ℕ) × (Fin e → ℕ)), WithSeminorms q ∧
      ∀ i f, q i f = lpNorm (elementarySchwartz_weightedWord
        ((invariantBasisWord i.1).map (fun j => elementaryOneParameter (B j)))
        ((invariantBasisWord i.2).map (elementaryDualBasisDirections C)) f) p ν := by
  obtain ⟨c, hc, hν⟩ := elementaryHaar_eq_smul ν
  let t : ℝ≥0 := c ^ p.toReal⁻¹
  let D (a : Fin d → ℕ) : Directions :=
    (invariantBasisWord a).map (fun j => elementaryOneParameter (B j))
  let S (b : Fin e → ℕ) : DualDirections :=
    (invariantBasisWord b).map (elementaryDualBasisDirections C)
  let q (i : (Fin d → ℕ) × (Fin e → ℕ)) :=
    (normSeminorm ℂ (Lp ℂ p μ)).comp
      (elementarySchwartz_weightedWordLp (D i.1) (S i.2) p).toLinearMap
  have hq : WithSeminorms q := elementarySchwartz_withSeminorms_basisWordsLp B C p
  have ht : 0 < t := by dsimp [t]; positivity
  refine ⟨fun i => t • q i, elementarySchwartz_withSeminorms_const_smul q hq ht, fun i f => ?_⟩
  rw [hν, lpNorm_smul_measure_of_ne_zero hc.ne']
  change (t : ℝ) * ‖elementarySchwartz_weightedWordLp (D i.1) (S i.2) p f‖ =
    (t : ℝ) * lpNorm (elementarySchwartz_weightedWord (D i.1) (S i.2) f) p μ
  rw [elementarySchwartz_weightedWordLp_norm]


end
end Masullo
