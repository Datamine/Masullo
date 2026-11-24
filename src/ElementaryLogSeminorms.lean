import ElementaryRadialSchwartz
import ElementarySchwartzBasisTopology

open Filter Function MeasureTheory Module Set Topology
open scoped ENNReal NNReal

namespace Masullo

noncomputable section

variable {m n r : ℕ} {F : Type*} [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F]
  [Finite F]

local notation "A" => ElementaryLCAModel m n r F
local notation "E" => ElementarySchwartz m n r F
local notation "X" => EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)
local notation "Directions" => List (Multiplicative ℝ →ₜ* Multiplicative A)
local notation "Dual" => PontryaginDual (Multiplicative A)

omit [TopologicalSpace F] [DiscreteTopology F] [Finite F] in
private theorem norm_elementaryGrowthVariables (g : A) (i : Fin m ⊕ Fin r) :
    ‖elementaryGrowthVariables g i‖ = |elementaryGrowth g i| := by
  cases i with
  | inl i => rw [show elementaryGrowthVariables g (.inl i) = (g.1 i : ℂ) from rfl,
      Complex.norm_real, Real.norm_eq_abs]; rfl
  | inr i => rw [show elementaryGrowthVariables g (.inr i) =
      (((g.2.2.1 i : ℤ) : ℝ) : ℂ) from (Complex.ofReal_intCast _).symm,
      Complex.norm_real, Real.norm_eq_abs]; rfl

private theorem exists_elementaryDualSymbol_le_log (l : A →+ ℝ) (hl : IsProperMap l)
    (c : Multiplicative ℝ →ₜ* Dual) :
    ∃ K : ℝ≥0, ∀ g : A, ‖elementaryDualSymbol c g‖ ≤ K * |l g| := by
  obtain ⟨C, hC, hbound⟩ := exists_elementaryGrowth_le_properLog l hl
  obtain ⟨v, hv⟩ := elementaryDualSymbol_exists_realCoefficients c
  let K := (∑ i, ‖v i‖) * C
  have hK : 0 ≤ K := mul_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _) hC
  refine ⟨⟨K, hK⟩, fun g => ?_⟩
  rw [hv, norm_mul, Complex.norm_I, one_mul]
  calc
    _ ≤ ∑ i, ‖(v i : ℂ) * elementaryGrowthVariables g i‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖v i‖ * (C * |l g|) := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_mul, Complex.norm_real, norm_elementaryGrowthVariables]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      rw [← Real.norm_eq_abs]
      exact (norm_le_pi_norm (elementaryGrowth g) i).trans (hbound g)
    _ = _ := by rw [← Finset.sum_mul, ← mul_assoc]; rfl

private theorem exists_elementaryDualWord_le_logPower (l : A →+ ℝ) (hl : IsProperMap l)
    (cs : List (Multiplicative ℝ →ₜ* Dual)) :
    ∃ K : ℝ≥0, ∀ g : A, ‖elementaryDualWord cs g‖ ≤ K * |l g| ^ cs.length := by
  induction cs with
  | nil => exact ⟨1, by simp [elementaryDualWord]⟩
  | cons c cs ih =>
    obtain ⟨K, hK⟩ := ih
    obtain ⟨C, hC⟩ := exists_elementaryDualSymbol_le_log l hl c
    refine ⟨C * K, fun g => ?_⟩
    change ‖elementaryDualSymbol c g * elementaryDualWord cs g‖ ≤ _
    rw [norm_mul]
    calc
      _ ≤ ((C : ℝ) * |l g|) * ((K : ℝ) * |l g| ^ cs.length) :=
        mul_le_mul (hC g) (hK g) (norm_nonneg _) (by positivity)
      _ = _ := by simp only [List.length_cons, NNReal.coe_mul, pow_succ]; ring

/-- The logarithmically weighted invariant derivative on an elementary chart. -/
def elementaryLogWeightedWord (l : A →+ ℝ) (cs : Directions) (N : ℕ) (f : E) (g : A) : ℂ :=
  ((|l g| : ℝ) : ℂ) ^ N * elementaryOrbitWord cs f g

theorem elementaryLogWeightedWord_continuous (l : A →+ ℝ) (hl : Continuous l)
    (cs : Directions) (N : ℕ) (f : E) : Continuous (elementaryLogWeightedWord l cs N f) := by
  have he : (elementarySchwartz_weightedWord cs [] f : A → ℂ) =
      (fun g => elementaryOrbitWord cs f g) := by
    funext g
    simp [elementaryDualWord]
  have h : Continuous (fun g => elementaryOrbitWord cs f g) := he ▸
    (elementarySchwartz_weightedWord cs [] f).continuous
  exact ((Complex.continuous_ofReal.comp hl.abs).pow N).mul h

private theorem norm_elementaryLogWeightedWord_eq (l : A →+ ℝ)
    (c : Multiplicative ℝ →ₜ* Dual) (hc : ∀ g, elementaryDualSymbol c g = Complex.I * (l g : ℂ))
    (cs : Directions) (N : ℕ) (f : E) (g : A) :
    ‖elementaryLogWeightedWord l cs N f g‖ =
      ‖elementarySchwartz_weightedWord cs (List.replicate N c) f g‖ := by
  simp only [elementaryLogWeightedWord, elementarySchwartz_weightedWord_apply, elementaryDualWord,
    List.map_replicate, List.prod_replicate, norm_mul, norm_pow, hc, Complex.norm_I, one_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_abs]

variable [MeasurableSpace F] [BorelSpace F]

private theorem weightedWord_memLp_haar (ν : Measure A) [ν.IsAddHaarMeasure]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (cs : Directions) (ds : List (Multiplicative ℝ →ₜ* Dual)) (f : E) :
    MemLp (elementarySchwartz_weightedWord cs ds f) p ν := by
  simpa [elementarySchwartz_weightedOperator] using
    elementarySchwartz_weightedOperator_memLp_haar ν p [(1, cs)] [(1, ds)] f

/-- Powers of the absolute value of a proper logarithm, times the invariant
monomials of any tangent basis, give the elementary Schwartz topology. -/
theorem elementarySchwartz_withSeminorms_logWeightedLp
    (l : A →+ ℝ) (hl : IsProperMap l) {d : ℕ} (B : Basis (Fin d) ℝ X)
    (ν : Measure A) [ν.IsAddHaarMeasure] (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    ∃ q : SeminormFamily ℂ E ((Fin d → ℕ) × ℕ), WithSeminorms q ∧
      ∀ i f, q i f = lpNorm
        (elementaryLogWeightedWord l ((invariantBasisWord i.1).map
          (fun j => elementaryOneParameter (B j))) i.2 f) p ν := by
  classical
  let D (a : Fin d → ℕ) : Directions :=
    (invariantBasisWord a).map (fun j => elementaryOneParameter (B j))
  let C := Module.finBasis ℝ ((Fin m ⊕ Fin r) → ℝ)
  let S (a : Fin (Module.finrank ℝ ((Fin m ⊕ Fin r) → ℝ)) → ℕ) :=
    (invariantBasisWord a).map (elementaryDualBasisDirections (n := n) (F := F) C)
  obtain ⟨s, hs, hs_norm⟩ := elementarySchwartz_withSeminorms_basisWordsLp_haar B C ν p
  obtain ⟨c, hc⟩ := continuousRealForm_elementaryDualSymbol l hl.continuous
  obtain ⟨u, hu, hu_norm⟩ := elementarySchwartz_withSeminorms_weightedOperatorLp_haar ν p
  let q (i : (Fin d → ℕ) × ℕ) := u ([(1, D i.1)], [(1, List.replicate i.2 c)])
  have hq i f : q i f = lpNorm (elementarySchwartz_weightedWord (D i.1)
      (List.replicate i.2 c) f) p ν := by
    simpa [q, elementarySchwartz_weightedOperator] using
      hu_norm ([(1, D i.1)], [(1, List.replicate i.2 c)]) f
  have hq_norm i f : q i f = lpNorm (elementaryLogWeightedWord l (D i.1) i.2 f) p ν := by
    have h₀ := (elementarySchwartz_weightedWord (D i.1) (List.replicate i.2 c) f).continuous
    have h₁ := elementaryLogWeightedWord_continuous l hl.continuous (D i.1) i.2 f
    rw [hq, ← toReal_eLpNorm h₀.aestronglyMeasurable, ← toReal_eLpNorm h₁.aestronglyMeasurable]
    exact congrArg ENNReal.toReal (eLpNorm_congr_norm_ae
      (Eventually.of_forall fun g => (norm_elementaryLogWeightedWord_eq l c hc _ _ f g).symm))
  refine ⟨q, hs.congr (Seminorm.IsBounded.of_real (f := LinearMap.id) ?_)
    (Seminorm.IsBounded.of_real (f := LinearMap.id) ?_), hq_norm⟩
  · intro i
    have hqi : Continuous (q i) := hu.continuous_seminorm _
    obtain ⟨s', K, _, hK⟩ := Seminorm.bound_of_continuous hs (q i) hqi
    exact ⟨s', K, fun f => hK f⟩
  · intro i
    obtain ⟨K, hK⟩ := exists_elementaryDualWord_le_logPower l hl (S i.2)
    let j := (i.1, (S i.2).length)
    refine ⟨{j}, K, fun f => ?_⟩
    rw [Finset.sup_singleton]
    change s i f ≤ (K : ℝ) * q j f
    rw [hs_norm, hq]
    let g := elementarySchwartz_weightedWord (D j.1) (List.replicate j.2 c) f
    have hg : MemLp g p ν := weightedWord_memLp_haar ν p _ _ f
    have hgn := hg.norm.const_smul (K : ℝ)
    have he (x : A) : ‖elementarySchwartz_weightedWord (D i.1) (S i.2) f x‖ ≤
        (K : ℝ) * ‖g x‖ := by
      have hx := (norm_elementaryLogWeightedWord_eq l c hc (D j.1) j.2 f x)
      rw [← hx]
      simp only [elementarySchwartz_weightedWord_apply, elementaryLogWeightedWord, norm_mul,
        norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_abs]
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right (hK x) (norm_nonneg _)
    calc
      _ ≤ lpNorm ((K : ℝ) • (fun x => ‖g x‖)) p ν := lpNorm_mono_real hgn he
      _ = _ := by
        rw [lpNorm_const_smul, lpNorm_norm hg.aestronglyMeasurable]
        change ‖(K : ℝ)‖ * lpNorm g p ν = (K : ℝ) * lpNorm g p ν
        rw [Real.norm_of_nonneg K.coe_nonneg]
end
end Masullo
