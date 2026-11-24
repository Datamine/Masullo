import FiniteEulerRecurrence
import HeckeEulerProducts

open Filter IsDedekindDomain NumberField Set
open scoped NumberField

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

private theorem nat_cpow_neg_eq_exp (q : ℕ) (hq : 0 < q) (s : ℂ) :
    (q : ℂ) ^ (-s) = Complex.exp (-(Real.log q : ℂ) * s) := by
  have hq₀ : 0 < (q : ℝ) := by exact_mod_cast hq
  rw [Complex.cpow_def_of_ne_zero (show (q : ℂ) ≠ 0 by exact_mod_cast hq.ne')]
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_log hq₀.le]
  congr 1
  ring

/-- The exponential denominator used for recurrence is the product of the
denominators of the finite Hecke Euler factors. -/
theorem finiteHeckeEulerDenominator_eq (S : Finset (HeightOneSpectrum (𝓞 F)))
    (c : HeightOneSpectrum (𝓞 F) → ℂ) (s : ℂ) :
    reciprocalEuler (fun v : S => c v.val) (fun v : S => v.val.asIdeal.absNorm) s =
      ∏ v : S, (heckeEulerFactor F c v.val s)⁻¹ := by
  unfold reciprocalEuler
  apply Finset.prod_congr rfl
  intro v _
  have hq := zero_lt_one.trans (NumberField.HeightOneSpectrum.one_lt_absNorm v.val)
  rw [heckeEulerFactor, inv_inv, nat_cpow_neg_eq_exp _ hq]

/-- Corrected Lemma 7.1.1.1 on the actual finite Euler factors. In the
unramified case the coefficient is the character value on the uniformizer;
a zero coefficient gives the factor one. The finite bound holds across the
whole closed strip at each chosen ordinate. -/
theorem finiteHeckeEuler_bounded_strip_sequence
    (S : Finset (HeightOneSpectrum (𝓞 F))) (c : HeightOneSpectrum (𝓞 F) → ℂ)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ (N : ℝ) (T : ℤ → ℝ), 0 < N ∧ StrictMono T ∧
      (∀ k, 0 < k → 0 < T k) ∧ (∀ k, k < 0 → T k < 0) ∧
      Tendsto T atTop atTop ∧ Tendsto T atBot atBot ∧
      ∀ k σ, σ ∈ Icc (-δ) (1 + δ) →
        let s := (σ : ℂ) + (T k : ℂ) * Complex.I
        (∀ v : S, (heckeEulerFactor F c v.val s)⁻¹ ≠ 0) ∧
          (∏ v : S, ‖heckeEulerFactor F c v.val s‖) ≤ N := by
  obtain ⟨N, T, hN, hT, hp, hn, htop, hbot, hbound⟩ :=
    reciprocalEuler_bounded_inverse_strip_sequence (fun v : S => c v.val)
      (fun v : S => v.val.asIdeal.absNorm)
      (fun v => NumberField.HeightOneSpectrum.one_lt_absNorm v.val)
      (α := -δ) (β := 1 + δ) (by linarith)
  refine ⟨N, T, hN, hT, hp, hn, htop, hbot, fun k σ hσ => ?_⟩
  let s := (σ : ℂ) + (T k : ℂ) * Complex.I
  obtain ⟨hne, hsmall⟩ := hbound k σ hσ
  rw [finiteHeckeEulerDenominator_eq F S c] at hne hsmall
  refine ⟨fun v => Finset.prod_ne_zero_iff.mp hne v (Finset.mem_univ v), ?_⟩
  rw [Finset.prod_inv_distrib, inv_inv, norm_prod] at hsmall
  exact hsmall

/-- The actual finite Euler denominator at the central ordinate vanishes
for the trivial unramified coefficient selected by the printed signs. -/
theorem finiteHeckeEuler_printed_signs_obstruction
    (S : Finset (HeightOneSpectrum (𝓞 F))) {v : HeightOneSpectrum (𝓞 F)} (hv : v ∈ S)
    (T : ℤ → ℝ) (hp : ∀ k, 0 ≤ k → 0 ≤ T k) (hn : ∀ k, k ≤ 0 → T k ≤ 0) :
    (∏ w : S, (heckeEulerFactor F (fun _ => 1) w.val ((T 0 : ℂ) * Complex.I))⁻¹) = 0 := by
  have h0 : T 0 = 0 := le_antisymm (hn 0 le_rfl) (hp 0 le_rfl)
  apply Finset.prod_eq_zero (Finset.mem_univ (⟨v, hv⟩ : S))
  simp [h0, heckeEulerFactor]

/-- Under the printed signs, the central strip has no finite upper bound
even at strictly positive real parts, where all factors are defined. -/
theorem finiteHeckeEuler_printed_strip_unbounded
    (S : Finset (HeightOneSpectrum (𝓞 F))) {v : HeightOneSpectrum (𝓞 F)} (hv : v ∈ S)
    (T : ℤ → ℝ) (hp : ∀ k, 0 ≤ k → 0 ≤ T k) (hn : ∀ k, k ≤ 0 → T k ≤ 0)
    {δ N : ℝ} (hδ : 0 < δ) (hN : 0 < N) :
    ∃ σ ∈ Icc (-δ) (1 + δ), 0 < σ ∧
      N < ∏ w : S,
        ‖heckeEulerFactor F (fun _ => 1) w.val ((σ : ℂ) + (T 0 : ℂ) * Complex.I)‖ := by
  let d (w : HeightOneSpectrum (𝓞 F)) (σ : ℝ) :=
    1 - Real.exp (-(Real.log (w.asIdeal.absNorm)) * σ)
  have hd (w : HeightOneSpectrum (𝓞 F)) {σ : ℝ} (hσ : 0 < σ) :
      0 < d w σ ∧ d w σ ≤ 1 := by
    have hlog : 0 < Real.log (w.asIdeal.absNorm) :=
      Real.log_pos (by exact_mod_cast (NumberField.HeightOneSpectrum.one_lt_absNorm w))
    change 0 < 1 - Real.exp (-Real.log (w.asIdeal.absNorm) * σ) ∧
      1 - Real.exp (-Real.log (w.asIdeal.absNorm) * σ) ≤ 1
    exact ⟨sub_pos.mpr (Real.exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos (neg_neg_of_pos hlog) hσ)),
      sub_le_self _ (Real.exp_nonneg _)⟩
  have hval (w : HeightOneSpectrum (𝓞 F)) {σ : ℝ} (hσ : 0 < σ) :
      ‖heckeEulerFactor F (fun _ => 1) w (σ : ℂ)‖ = (d w σ)⁻¹ := by
    have hq := zero_lt_one.trans (NumberField.HeightOneSpectrum.one_lt_absNorm w)
    rw [heckeEulerFactor, one_mul, nat_cpow_neg_eq_exp _ hq]
    have he : (-(Real.log (w.asIdeal.absNorm) : ℂ) * (σ : ℂ)) =
        ((-Real.log (w.asIdeal.absNorm) * σ : ℝ) : ℂ) := by push_cast; rfl
    rw [he, ← Complex.ofReal_exp, ← Complex.ofReal_one, ← Complex.ofReal_sub, norm_inv,
      Complex.norm_real, Real.norm_of_nonneg (hd w hσ).1.le]
  have hc : Continuous (d v) := by unfold d; fun_prop
  obtain ⟨ε, hε, hsmall⟩ := Metric.continuousAt_iff.mp (hc.continuousAt (x := 0))
    N⁻¹ (inv_pos.mpr hN)
  let σ := min ε 1 / 2
  have hσ : 0 < σ := half_pos (lt_min hε zero_lt_one)
  have hσε : σ < ε := (half_lt_self (lt_min hε zero_lt_one)).trans_le (min_le_left _ _)
  have hσ₁ : σ ≤ 1 := (half_lt_self (lt_min hε zero_lt_one)).le.trans (min_le_right _ _)
  have hdsmall : d v σ < N⁻¹ := by
    have h := hsmall (show dist σ 0 < ε by rwa [Real.dist_eq, sub_zero, abs_of_pos hσ])
    have hz : d v 0 = 0 := by simp [d]
    rwa [hz, Real.dist_eq, sub_zero, abs_of_pos (hd v hσ).1] at h
  have hlarge : N < (d v σ)⁻¹ := by
    simpa only [inv_inv] using (inv_lt_inv₀ (inv_pos.mpr hN) (hd v hσ).1).mpr hdsmall
  have h0 : T 0 = 0 := le_antisymm (hn 0 le_rfl) (hp 0 le_rfl)
  let A (w : S) := ‖heckeEulerFactor F (fun _ => 1) w.val (σ : ℂ)‖
  let w₀ : S := ⟨v, hv⟩
  have hA (w : S) : 1 ≤ A w := by
    change 1 ≤ ‖heckeEulerFactor F (fun _ => 1) w.val (σ : ℂ)‖
    rw [hval w.val hσ]
    simpa only [inv_one] using inv_anti₀ (hd w.val hσ).1 (hd w.val hσ).2
  have hprod : A w₀ ≤ ∏ w : S, A w := by
    have h := Finset.prod_le_prod_of_subset_of_one_le (f := A)
      (Finset.subset_univ ({w₀} : Finset S)) (fun w _ => zero_le_one.trans (hA w))
      (fun w _ _ => hA w)
    simpa only [Finset.prod_singleton] using h
  have hvlarge : N < A w₀ := by
    change N < ‖heckeEulerFactor F (fun _ => 1) v (σ : ℂ)‖
    rwa [hval v hσ]
  refine ⟨σ, ⟨(neg_nonpos.mpr hδ.le).trans hσ.le, hσ₁.trans (le_add_of_nonneg_right hδ.le)⟩, hσ, ?_⟩
  simp only [h0, Complex.ofReal_zero, zero_mul, add_zero]
  exact hvlarge.trans_le hprod

end

end Masullo
