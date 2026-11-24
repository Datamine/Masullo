import ModulatedDecayAngularBounds

open Function MeasureTheory Set Topology
open scoped SchwartzMap

namespace Masullo

noncomputable section

private theorem continuousSeminorm_weightedBound
    {X ι Ω : Type*} [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    (p : SeminormFamily ℂ X ι) (hp : WithSeminorms p)
    (q : Seminorm ℂ X) (hq : Continuous q) (x : Ω → X) (w : Ω → ℝ) (hw : ∀ a, 0 < w a)
    (h : ∀ j, ∃ C : ℝ, 0 ≤ C ∧ ∀ a, w a * p j (x a) ≤ C) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a, w a * q (x a) ≤ C := by
  obtain ⟨J, A, _, hA⟩ := Seminorm.bound_of_continuous hp q hq
  choose M hM hB using h
  let B := ∑ j ∈ J, M j
  have hB₀ : 0 ≤ B := Finset.sum_nonneg fun j _ => hM j
  refine ⟨(A : ℝ) * B, mul_nonneg A.coe_nonneg hB₀, fun a => ?_⟩
  have hs : w a * J.sup p (x a) ≤ B := by
    rw [mul_comm, ← le_div_iff₀ (hw a)]
    apply Seminorm.finset_sup_apply_le (div_nonneg hB₀ (hw a).le)
    intro j hj
    rw [le_div_iff₀ (hw a), mul_comm]
    exact (hB j a).trans (Finset.single_le_sum (fun l _ => hM l) hj)
  calc
    _ ≤ w a * ((A : ℝ) * J.sup p (x a)) := mul_le_mul_of_nonneg_left (hA _) (hw a).le
    _ = (A : ℝ) * (w a * J.sup p (x a)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hs A.coe_nonneg

variable {n : ℕ} {T : Type*} [AddCommGroup T] [TopologicalSpace T] [DiscreteTopology T] [Finite T]

local notation "A" => ElementaryLCAModel 0 n 0 T
local notation "E" => ElementarySchwartz 0 n 0 T
local notation "Ω" => PontryaginDual (Multiplicative A)

private theorem frequencyWeight_ge_one (θ : Ω) : 1 ≤ compactElementaryFrequencyWeight θ :=
  le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => norm_nonneg _)

private theorem inverseCharacter_continuousSeminorm_growth [CompactSpace A]
    (p : Seminorm ℂ E) (hp : Continuous p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ d : ℕ, ∀ θ : Ω,
      p (compactElementaryInverseCharacterTest θ) ≤ C * compactElementaryFrequencyWeight θ ^ d := by
  obtain ⟨J, a, _, ha⟩ := Seminorm.bound_of_continuous elementarySchwartz_withSeminorms p hp
  choose C hC d hd using fun j : ElementarySchwartzIndex 0 n 0 =>
    compactElementaryInverseCharacterTest_seminorm_le (F := T) j
  let D := ∑ j ∈ J, d j
  let B := ∑ j ∈ J, C j
  have hB : 0 ≤ B := Finset.sum_nonneg fun j _ => hC j
  refine ⟨(a : ℝ) * B, mul_nonneg a.coe_nonneg hB, D, fun θ => ?_⟩
  let w := compactElementaryFrequencyWeight θ
  have hw : 1 ≤ w := frequencyWeight_ge_one θ
  have hn : 0 ≤ w ^ D := pow_nonneg (zero_le_one.trans hw) _
  calc
    _ ≤ (a : ℝ) * (J.sup elementarySchwartzSeminorm) (compactElementaryInverseCharacterTest θ) := ha _
    _ ≤ (a : ℝ) * (B * w ^ D) := by
      apply mul_le_mul_of_nonneg_left _ a.coe_nonneg
      apply Seminorm.finset_sup_apply_le (mul_nonneg hB hn)
      intro j hj
      refine (hd j θ).trans ?_
      apply mul_le_mul
      · exact Finset.single_le_sum (fun i _ => hC i) hj
      · exact pow_le_pow_right₀ hw (Finset.single_le_sum (fun i _ => Nat.zero_le (d i)) hj)
      · exact pow_nonneg (zero_le_one.trans hw) _
      · exact hB
    _ = _ := by ring

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  (m : G →ₜ* Multiplicative ℝ) [CompactSpace m.toMonoidHom.ker]
  (τ : Multiplicative ℝ →ₜ* G) (hτ : RightInverse τ m)

local notation "K" => m.toMonoidHom.ker

variable [MeasurableSpace m.toMonoidHom.ker] [BorelSpace m.toMonoidHom.ker]
  (ν : Measure m.toMonoidHom.ker) [ν.IsHaarMeasure]

include hτ in
set_option maxHeartbeats 4500000 in
/-- On a compact elementary angular quotient, the products of the two
factor seminorms of the Fourier terms are absolutely summable. -/
theorem summable_splitAngularCoefficient_factorSeminorms
    [LocallyCompactSpace K] [CompactSpace A] (φ : K →ₜ* Multiplicative A) (hφ : Surjective φ)
    (hm : IsProperMap m) (I : Set ℝ) (hI : I.Nonempty) (f : ModulatedExponentialInductive m I)
    (pa : Seminorm ℂ E) (pr : Seminorm ℂ (PositiveRealExponentialDecay I))
    (ha : Continuous pa) (hr : Continuous pr) :
    Summable (fun θ : Ω => pa (compactElementaryInverseCharacterTest θ) *
      pr (modulatedDecayAngularCoefficient m τ hτ ν (θ.comp φ) I hI hm f)) := by
  obtain ⟨C, hC, d, hc⟩ := inverseCharacter_continuousSeminorm_growth pa ha
  let r (θ : Ω) := modulatedDecayAngularCoefficient m τ hτ ν (θ.comp φ) I hI hm f
  let w (θ : Ω) := compactElementaryFrequencyWeight θ
  have hw (θ : Ω) : 1 ≤ w θ := frequencyWeight_ge_one θ
  let p : SeminormFamily ℂ (PositiveRealExponentialDecay I) (I × ℕ × ℕ) := fun i =>
    (SchwartzMap.seminorm ℂ i.2.1 i.2.2).comp (logExponentialDecayTwist I i.1)
  let weight (θ : Ω) := w θ ^ (d + 2*n + 1)
  have hweight (θ : Ω) : 0 < weight θ := pow_pos (zero_lt_one.trans_le (hw θ)) _
  have hDef (i : I × ℕ × ℕ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ θ : Ω, weight θ * p i (r θ) ≤ B :=
    splitAngularCoefficient_rapid_decay m τ hτ ν φ hφ hm I i.1 f i.2.1 i.2.2 (d+2*n)
  have hTopology := withGeneratingSeminorms_spec (logExponentialDecaySubmodule I)
    (fun i : I × ℕ × ℕ =>
      (SchwartzMap.seminorm ℂ i.2.1 i.2.2).comp (logExponentialDecayTwist I i.1))
  have hAll : ∃ B : ℝ, 0 ≤ B ∧ ∀ θ : Ω, weight θ * pr (r θ) ≤ B :=
    continuousSeminorm_weightedBound p hTopology pr hr r weight hweight hDef
  obtain ⟨B, hB, hb⟩ := hAll
  let a (θ : Ω) (j : Fin n) := 1 + ‖(compactElementaryCharacter_frequency θ j : ℝ)‖
  let L (θ : Ω) := ∏ j, a θ j ^ 2
  have hterm (θ : Ω) : 0 < L θ := by dsimp [L,a]; positivity
  have hL (θ : Ω) : L θ ≤ w θ ^ (2*n) := by
    calc
      _ ≤ ∏ _j : Fin n, w θ ^ 2 := by
        apply Finset.prod_le_prod (fun j _ => by dsimp [a]; positivity)
        intro j _
        apply pow_le_pow_left₀ (by dsimp [a]; positivity)
        exact add_le_add le_rfl (Finset.single_le_sum
          (fun l _ => norm_nonneg (compactElementaryCharacter_frequency θ l : ℝ)) (Finset.mem_univ j))
      _ = _ := by simp [pow_mul]
  have he (θ : Ω) : (∏ j : Fin n, (1 / (1 + ‖(compactElementaryCharacter_frequency θ j : ℝ)‖) ^ 2)) =
      1 / L θ := by simp [L,a,one_div,Finset.prod_inv_distrib]
  refine ((summable_compactElementary_character_majorant (F := T) (n := n)).mul_left (C * B)).of_nonneg_of_le
    (fun θ => mul_nonneg (apply_nonneg _ _) (apply_nonneg _ _)) fun θ => ?_
  rw [he, ← div_eq_mul_one_div, le_div_iff₀ (hterm θ)]
  have hp := hc θ
  change pa (compactElementaryInverseCharacterTest θ) ≤ C * w θ ^ d at hp
  calc
    _ ≤ ((C * w θ ^ d) * pr (r θ)) * w θ ^ (2*n) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_right hp (apply_nonneg _ _))
        (hL θ) (hterm θ).le (mul_nonneg (mul_nonneg hC (pow_nonneg (zero_le_one.trans (hw θ)) _))
          (apply_nonneg _ _))
    _ = C * (w θ ^ (d + 2*n) * pr (r θ)) := by rw [pow_add]; ring
    _ ≤ C * (w θ ^ (d + 2*n + 1) * pr (r θ)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (hw θ) (Nat.le_succ _)) (apply_nonneg _ _)) hC
    _ ≤ _ := mul_le_mul_of_nonneg_left (hb θ) hC

end

end Masullo
