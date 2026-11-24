import CompactBruhatFourierStages
import CompactBruhatCharacterBounds
import CompactElementaryCharacterIndex
import ElementarySchwartzComplete
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.PSeries

open Filter MeasureTheory Set
open scoped BigOperators

namespace Masullo

noncomputable section

variable {n : ℕ} {F : Type*} [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [Finite F]

local notation "A" => ElementaryLCAModel 0 n 0 F
local notation "E" => ElementarySchwartz 0 n 0 F
local notation "X" => EuclideanSpace ℝ (Fin 0) × EuclideanSpace ℝ (Fin n)

/-- A lattice weight for all the torus frequencies of a compact elementary
character. The finite component contributes only finitely many indices. -/
def compactElementaryFrequencyWeight (χ : PontryaginDual (Multiplicative A)) : ℝ :=
  1 + ∑ i : Fin n, ‖(compactElementaryCharacter_frequency χ i : ℝ)‖

/-- The frequency lattice weight controls the norm of the lifted phase. -/
theorem norm_compactElementaryCharacterPhase_le (χ : PontryaginDual (Multiplicative A)) :
    ‖compactElementaryCharacterPhase χ‖ ≤ 2 * Real.pi * compactElementaryFrequencyWeight χ := by
  let L := compactElementaryCharacterPhase χ
  apply L.opNorm_le_bound
  · unfold compactElementaryFrequencyWeight
    positivity
  intro u
  have hpos : 0 ≤ 2 * Real.pi := by positivity
  calc
    ‖L u‖ = ‖∑ i : Fin n, u.2 i • L (elementaryTorusVelocity i)‖ := by
      conv_lhs => rw [← sum_elementaryTorusVelocity u, map_sum]
      simp only [map_smul]
    _ ≤ ∑ i : Fin n, ‖u.2 i • L (elementaryTorusVelocity i)‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin n, (2 * Real.pi) * ‖(compactElementaryCharacter_frequency χ i : ℝ)‖ * ‖u‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul, show L (elementaryTorusVelocity i) = _ from
        compactElementaryCharacter_frequency_spec χ i, norm_mul, Real.norm_of_nonneg hpos, mul_comm]
      exact mul_le_mul_of_nonneg_left ((PiLp.norm_apply_le u.2 i).trans (norm_snd_le u)) (by positivity)
    _ ≤ 2 * Real.pi * compactElementaryFrequencyWeight χ * ‖u‖ := by
      rw [← Finset.sum_mul, ← Finset.mul_sum]
      unfold compactElementaryFrequencyWeight
      gcongr
      linarith

/-- The inverse character viewed as an elementary Schwartz test. -/
def compactElementaryInverseCharacterTest {m r : ℕ} [CompactSpace (ElementaryLCAModel m n r F)]
    (χ : PontryaginDual (Multiplicative (ElementaryLCAModel m n r F))) : ElementarySchwartz m n r F :=
  ⟨fun x ↦ (χ⁻¹ (Multiplicative.ofAdd x) : ℂ),
    elementarySchwartz_mem_of_compactSupport _ (HasCompactSupport.of_compactSpace _)
      (elementaryCharacter_smooth χ⁻¹)⟩

/-- Seminorm growth of the inverse characters is polynomial in the same
frequency weight used for the coefficient estimates. -/
theorem compactElementaryInverseCharacterTest_seminorm_le [CompactSpace A]
    (i : ElementarySchwartzIndex 0 n 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ d : ℕ, ∀ χ : PontryaginDual (Multiplicative A),
      elementarySchwartzSeminorm i (compactElementaryInverseCharacterTest χ) ≤
        C * compactElementaryFrequencyWeight χ ^ d := by
  obtain ⟨C, hC, d, h⟩ := elementaryCharacter_bound_of_phase (F := F) i
  refine ⟨C * (2 * Real.pi) ^ d, by positivity, d, fun χ ↦ ?_⟩
  have hphase (x : X) : χ⁻¹ (Multiplicative.ofAdd (elementaryCoverHom x)) =
      Circle.exp ((-compactElementaryCharacterPhase χ) x) := by
    change (χ (Multiplicative.ofAdd (elementaryCoverHom x)))⁻¹ = _
    rw [compactElementaryCharacterPhase_spec, neg_apply, Circle.exp_neg]
  have hb := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (h χ⁻¹ (-compactElementaryCharacterPhase χ) hphase)
  rw [ENNReal.toReal_ofReal (by positivity), norm_neg] at hb
  refine hb.trans ?_
  rw [mul_assoc, ← mul_pow]
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) (norm_compactElementaryCharacterPhase_le χ) _) hC

/-- Every positive power of the lattice weight is absorbed by a finite sum
of differentiated test seminorms. The bound is uniform in the character. -/
theorem compactElementaryFourierPairing_rapid_decay [CompactSpace (Multiplicative A)]
    [MeasurableSpace (Multiplicative A)] [BorelSpace (Multiplicative A)]
    (μ : Measure (Multiplicative A)) [μ.IsHaarMeasure]
    (χ : PontryaginDual (Multiplicative A)) (f : E) (k : ℕ) :
    compactElementaryFrequencyWeight χ ^ (k + 1) * ‖elementaryFourierPairing μ χ f‖ ≤
      ((n : ℝ) + 1) ^ k * (elementarySchwartzSeminorm (0, 0, 0, 0) f +
        ∑ i : Fin n, elementarySchwartzSeminorm (0, 0, 0, 0)
          ((elementarySchwartz_derivative (elementaryOneParameter (elementaryTorusVelocity i)))^[k + 1] f)) *
        μ.real univ := by
  let q := ‖elementaryFourierPairing μ χ f‖
  let a (i : Fin n) := ‖(compactElementaryCharacter_frequency χ i : ℝ)‖
  let w : Fin (n + 1) → ℝ := Fin.cons 1 a
  have hw : (∑ i, w i) = compactElementaryFrequencyWeight χ := by
    simp [w, Fin.sum_univ_succ, compactElementaryFrequencyWeight, a]
  have hp : compactElementaryFrequencyWeight χ ^ (k + 1) ≤
      ((n : ℝ) + 1) ^ k * (1 + ∑ i, a i ^ (k + 1)) := by
    have hw₀ (i : Fin (n + 1)) : 0 ≤ w i := by
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · simp [w]
      · exact norm_nonneg (compactElementaryCharacter_frequency χ j : ℝ)
    rw [← hw]
    simpa [w, Fin.sum_univ_succ, Fin.cons_succ] using
      (pow_sum_le_card_mul_sum_pow (s := Finset.univ) (f := w)
        (fun i _ ↦ hw₀ i) k)
  have ha (i : Fin n) : a i ^ (k + 1) * q ≤
      elementarySchwartzSeminorm (0, 0, 0, 0)
        ((elementarySchwartz_derivative (elementaryOneParameter (elementaryTorusVelocity i)))^[k + 1] f) *
        μ.real univ := by
    have hi := elementaryFourierPairing_frequency_bound μ (elementaryTorusVelocity i)
      χ (compactElementaryCharacterPhase χ) (compactElementaryCharacterPhase_spec χ) f (k + 1)
    rw [compactElementaryCharacter_frequency_spec, norm_mul, Real.norm_eq_abs (2 * Real.pi),
      abs_of_pos (by positivity)] at hi
    refine le_trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) ?_ _) (norm_nonneg _)) hi
    exact le_mul_of_one_le_left (norm_nonneg _) (by linarith [Real.pi_gt_three])
  calc
    _ ≤ (((n : ℝ) + 1) ^ k * (1 + ∑ i, a i ^ (k + 1))) * q :=
      mul_le_mul_of_nonneg_right hp (norm_nonneg _)
    _ = ((n : ℝ) + 1) ^ k * (q + ∑ i, a i ^ (k + 1) * q) := by
      rw [mul_assoc, add_mul, one_mul, Finset.sum_mul]
    _ ≤ _ := by
      rw [mul_assoc, add_mul, Finset.sum_mul]
      exact mul_le_mul_of_nonneg_left
        (add_le_add (norm_elementaryFourierPairing_le μ χ f) (Finset.sum_le_sum fun i _ ↦ ha i))
        (by positivity)

private theorem summable_mul_separate {U V : Type*} {u : U → ℝ} {v : V → ℝ}
    (hu : Summable u) (hv : Summable v) (hu₀ : 0 ≤ u) (hv₀ : 0 ≤ v) :
    Summable (fun p : U × V ↦ u p.1 * v p.2) :=
  (summable_prod_of_nonneg fun p ↦ mul_nonneg (hu₀ p.1) (hv₀ p.2)).2
    ⟨fun x ↦ hv.mul_left (u x), by simp only [tsum_mul_left]; exact hu.mul_right _⟩

private theorem summable_torus_product (g : ℤ → ℝ) (hg : Summable g) (hg₀ : 0 ≤ g) :
    ∀ n : ℕ, Summable (fun p : Fin n → ℤ ↦ ∏ i, g (p i))
  | 0 => Summable.of_finite
  | n + 1 => by
      let split (p : Fin (n + 1) → ℤ) : ℤ × (Fin n → ℤ) := (p 0, fun i ↦ p i.succ)
      have hs : Function.Injective split := by
        intro p q h
        funext i
        refine Fin.cases (congrArg Prod.fst h) (fun j ↦ congrFun (congrArg Prod.snd h) j) i
      have h := summable_mul_separate hg (summable_torus_product g hg hg₀ n)
        hg₀ (fun _ ↦ Finset.prod_nonneg fun _ _ ↦ hg₀ _)
      exact (h.comp_injective hs).congr fun p ↦ (Fin.prod_univ_succ (fun i ↦ g (p i))).symm

/-- The reciprocal square product in the lattice coordinates is summable
over all compact elementary characters, including the finite characters. -/
theorem summable_compactElementary_character_majorant :
    Summable (fun χ : PontryaginDual (Multiplicative A) ↦
      ∏ i : Fin n, (1 / (1 + ‖(compactElementaryCharacter_frequency χ i : ℝ)‖) ^ 2)) := by
  let g (j : ℤ) : ℝ := 1 / (1 + ‖(j : ℝ)‖) ^ 2
  have hg : Summable g := by
    have h := (Real.summable_one_div_nat_add_rpow 1 2).2 (by norm_num)
    have hn : Summable (fun j : ℕ ↦ g (j : ℤ)) := by
      convert h using 1
      funext j
      simp [g, abs_of_nonneg (show 0 ≤ (j : ℝ) + 1 by positivity), add_comm]
    exact summable_int_iff_summable_nat_and_neg.mpr ⟨hn, hn.congr fun j ↦ by simp [g]⟩
  have hg₀ : 0 ≤ g := fun _ ↦ by dsimp [g]; positivity
  letI : Finite (Multiplicative F) := Finite.of_equiv F Multiplicative.ofAdd
  letI : CompactSpace (Multiplicative F) := Finite.compactSpace
  have h₁ : Summable (fun _ : PontryaginDual (Multiplicative F) ↦ (1 : ℝ)) := Summable.of_finite
  have hs := summable_mul_separate (summable_torus_product g hg hg₀ n) h₁
    (fun _ ↦ Finset.prod_nonneg fun _ _ ↦ hg₀ _) (fun _ ↦ zero_le_one)
  simpa [g, Function.comp_def] using hs.comp_injective compactElementaryCharacter_index_injective

/-- Fourier coefficients on a compact elementary stage are absolutely
summable with every polynomial lattice weight. -/
theorem summable_compactElementaryFourierPairing [CompactSpace (Multiplicative A)]
    [MeasurableSpace (Multiplicative A)] [BorelSpace (Multiplicative A)]
    (μ : Measure (Multiplicative A)) [μ.IsHaarMeasure] (f : E) (d : ℕ) :
    Summable (fun χ : PontryaginDual (Multiplicative A) ↦
      compactElementaryFrequencyWeight χ ^ d * ‖elementaryFourierPairing μ χ f‖) := by
  let k := d + 2 * n
  let C := ((n : ℝ) + 1) ^ k * (elementarySchwartzSeminorm (0, 0, 0, 0) f +
    ∑ i : Fin n, elementarySchwartzSeminorm (0, 0, 0, 0)
      ((elementarySchwartz_derivative (elementaryOneParameter (elementaryTorusVelocity i)))^[k + 1] f)) *
    μ.real univ
  refine (summable_compactElementary_character_majorant (F := F) (n := n)).mul_left C
    |>.of_nonneg_of_le ?_ ?_
  · intro χ
    unfold compactElementaryFrequencyWeight
    positivity
  intro χ
  let W := compactElementaryFrequencyWeight χ
  let b (i : Fin n) := 1 + ‖(compactElementaryCharacter_frequency χ i : ℝ)‖
  let B := ∏ i : Fin n, b i ^ 2
  have hW : 1 ≤ W := le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)
  have hb (i : Fin n) : b i ≤ W := by
    exact add_le_add (le_refl 1) (Finset.single_le_sum
      (f := fun j : Fin n ↦ ‖(compactElementaryCharacter_frequency χ j : ℝ)‖)
      (fun j _ ↦ norm_nonneg (compactElementaryCharacter_frequency χ j : ℝ)) (Finset.mem_univ i))
  have hB : B ≤ W ^ (2 * n) := by
    calc
      _ ≤ ∏ _i : Fin n, W ^ 2 :=
        Finset.prod_le_prod (fun _ _ ↦ by dsimp [b]; positivity)
          (fun i _ ↦ pow_le_pow_left₀ (by dsimp [b]; positivity) (hb i) 2)
      _ = _ := by simp [pow_mul]
  have hB₀ : 0 < B := by dsimp [B, b]; positivity
  have hprod : (∏ i : Fin n, (1 / (1 + ‖(compactElementaryCharacter_frequency χ i : ℝ)‖) ^ 2)) =
      1 / B := by simp [B, b, one_div, Finset.prod_inv_distrib]
  change W ^ d * _ ≤ C * _
  rw [hprod, ← div_eq_mul_one_div, le_div_iff₀ hB₀]
  calc
    _ ≤ W ^ d * ‖elementaryFourierPairing μ χ f‖ * W ^ (2 * n) :=
      mul_le_mul_of_nonneg_left hB (by positivity : 0 ≤ W ^ d * _)
    _ = W ^ k * ‖elementaryFourierPairing μ χ f‖ := by rw [pow_add]; ring
    _ ≤ W ^ (k + 1) * ‖elementaryFourierPairing μ χ f‖ :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hW (Nat.le_succ k)) (norm_nonneg _)
    _ ≤ C := compactElementaryFourierPairing_rapid_decay μ χ f k

/-- Absolute summability of the inverse character series in each defining
Schwartz seminorm. -/
theorem summable_compactElementaryFourierSeries_seminorm [CompactSpace A]
    [CompactSpace (Multiplicative A)] [MeasurableSpace (Multiplicative A)]
    [BorelSpace (Multiplicative A)] (μ : Measure (Multiplicative A)) [μ.IsHaarMeasure]
    (f : E) (i : ElementarySchwartzIndex 0 n 0) :
    Summable (fun χ : PontryaginDual (Multiplicative A) ↦
      elementarySchwartzSeminorm i (elementaryFourierPairing μ χ f • compactElementaryInverseCharacterTest χ)) := by
  obtain ⟨C, hC, d, h⟩ := compactElementaryInverseCharacterTest_seminorm_le (F := F) i
  refine ((summable_compactElementaryFourierPairing μ f d).mul_left C).of_nonneg_of_le
    (fun _ ↦ apply_nonneg _ _) (fun χ ↦ ?_)
  calc
    _ = ‖elementaryFourierPairing μ χ f‖ * elementarySchwartzSeminorm i (compactElementaryInverseCharacterTest χ) :=
      map_smul_eq_mul (elementarySchwartzSeminorm i) _ _
    _ ≤ ‖elementaryFourierPairing μ χ f‖ * (C * compactElementaryFrequencyWeight χ ^ d) :=
      mul_le_mul_of_nonneg_left (h χ) (norm_nonneg _)
    _ = _ := by ring

/-- The elementary inverse character series converges in the Schwartz
topology, with sums taken over finite subsets of the character group. -/
theorem summable_compactElementaryFourierSeries [CompactSpace A]
    [CompactSpace (Multiplicative A)] [MeasurableSpace (Multiplicative A)]
    [BorelSpace (Multiplicative A)] (μ : Measure (Multiplicative A)) [μ.IsHaarMeasure] (f : E) :
    Summable (fun χ : PontryaginDual (Multiplicative A) ↦
      elementaryFourierPairing μ χ f • compactElementaryInverseCharacterTest χ) := by
  classical
  letI := completeSpace_elementarySchwartz (m := 0) (n := n) (r := 0) (F := F)
  let g (χ : PontryaginDual (Multiplicative A)) : E :=
    elementaryFourierPairing μ χ f • compactElementaryInverseCharacterTest χ
  apply summable_iff_cauchySeq_finset.mpr
  refine cauchySeq_finset_iff_sum_vanishing.mpr fun U hU ↦ ?_
  let p : ElementarySchwartzIndex 0 n 0 → Seminorm ℂ E := elementarySchwartzSeminorm
  obtain ⟨⟨J, ε⟩, hε, hJ⟩ := elementarySchwartz_withSeminorms.hasBasis_zero_ball.mem_iff.mp hU
  let R (χ : PontryaginDual (Multiplicative A)) := ∑ j ∈ J, p j (g χ)
  have hR : Summable R := by
    have hs (K : Finset (ElementarySchwartzIndex 0 n 0)) :
        Summable (fun χ ↦ ∑ j ∈ K, p j (g χ)) := by
      induction K using Finset.induction_on with
      | empty => simp
      | @insert j K hj h =>
        simp only [Finset.sum_insert hj]
        exact (summable_compactElementaryFourierSeries_seminorm μ f j).add h
    exact hs J
  obtain ⟨s, hs⟩ := cauchySeq_finset_iff_sum_vanishing.mp (summable_iff_cauchySeq_finset.mp hR)
    (Iio ε) (Iio_mem_nhds hε)
  refine ⟨s, fun u hu ↦ hJ ((J.sup p).mem_ball_zero.mpr ?_)⟩
  have huε : (∑ χ ∈ u, R χ) < ε := hs u hu
  refine lt_of_le_of_lt ?_ huε
  refine Seminorm.finset_sup_apply_le (Finset.sum_nonneg fun χ _ ↦
    Finset.sum_nonneg fun j _ ↦ apply_nonneg (p j) (g χ)) fun j hj ↦ ?_
  calc
    p j (∑ χ ∈ u, g χ) ≤ ∑ χ ∈ u, p j (g χ) :=
      Finset.le_sum_of_subadditive (p j) (map_zero _).le (map_add_le_add _) _ _
    _ ≤ ∑ χ ∈ u, R χ :=
      Finset.sum_le_sum fun χ _ ↦ Finset.single_le_sum (fun l _ ↦ apply_nonneg (p l) (g χ)) hj

theorem summable_elementaryFourierSeries_of_compact {m r : ℕ}
    [CompactSpace (ElementaryLCAModel m n r F)] [CompactSpace (Multiplicative (ElementaryLCAModel m n r F))]
    [MeasurableSpace (Multiplicative (ElementaryLCAModel m n r F))]
    [BorelSpace (Multiplicative (ElementaryLCAModel m n r F))]
    (μ : Measure (Multiplicative (ElementaryLCAModel m n r F))) [μ.IsHaarMeasure]
    (f : ElementarySchwartz m n r F) :
    Summable (fun χ : PontryaginDual (Multiplicative (ElementaryLCAModel m n r F)) ↦
      elementaryFourierPairing μ χ f • compactElementaryInverseCharacterTest χ) := by
  obtain ⟨rfl, rfl⟩ := elementaryLCAModel_compact_dimensions (m := m) (n := n) (r := r) (F := F)
  exact summable_compactElementaryFourierSeries μ f

end

end Masullo
