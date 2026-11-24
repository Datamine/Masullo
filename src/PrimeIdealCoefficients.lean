import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.Data.Nat.Prime.Int
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.Ideal.Int
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic

open scoped NumberField BigOperators
open Ideal IsDedekindDomain Set

namespace Masullo

variable (F : Type*) [Field F] [NumberField F]

private abbrev PrimeIdeal := HeightOneSpectrum (𝓞 F)

private def normPowerPairs (m : ℕ) : Set (PrimeIdeal F × ℕ) :=
  {a | 0 < a.2 ∧ Ideal.absNorm a.1.asIdeal ^ a.2 = m}

theorem primeIdeal_norm_isPrimePower (P : PrimeIdeal F) :
    ∃ (p d : ℕ), Nat.Prime p ∧ 0 < d ∧
      P.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) ∧ Ideal.absNorm P.asIdeal = p ^ d := by
  have hP : P.asIdeal.IsMaximal := P.isPrime.isMaximal P.ne_bot
  letI := hP
  obtain ⟨p, d, hd, hmem, hp, hnorm⟩ := Ideal.exists_prime_and_absNorm_eq_pow P.asIdeal
  letI : Fact (p.Prime) := ⟨hp⟩
  have hspan : (Ideal.span {(p : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime p
  have hle : Ideal.span {(p : ℤ)} ≤ P.asIdeal.under ℤ := Ideal.span_le.mpr (by
    intro z hz
    rw [mem_singleton_iff.mp hz]
    simpa [Ideal.under] using hmem)
  letI : P.asIdeal.IsPrime := P.isPrime
  have hp' : (P.asIdeal.under ℤ).IsPrime := Ideal.IsPrime.comap (algebraMap ℤ (𝓞 F))
  have hproper : P.asIdeal.under ℤ ≠ ⊤ := hp'.ne_top
  exact ⟨p, d, hp, hd, ⟨hspan.eq_of_le hproper hle⟩, hnorm⟩

private theorem primeIdeal_one_lt_norm (P : PrimeIdeal F) : 1 < Ideal.absNorm P.asIdeal := by
  obtain ⟨p, d, hp, hd, _, h⟩ := primeIdeal_norm_isPrimePower F P
  rw [h]
  exact Nat.one_lt_pow hd.ne' hp.one_lt

private theorem normPowerPairs_injOn (m : ℕ) :
    InjOn (fun a : PrimeIdeal F × ℕ => a.1.asIdeal) (normPowerPairs F m) := by
  rintro ⟨P, k⟩ hPk ⟨Q, l⟩ hQl hpq
  have he : P = Q := HeightOneSpectrum.asIdeal_injective hpq
  subst Q
  have hk : Ideal.absNorm P.asIdeal ^ k = m := hPk.2
  have hl : Ideal.absNorm P.asIdeal ^ l = m := hQl.2
  have hkl : k = l := Nat.pow_right_injective (primeIdeal_one_lt_norm F P) (hk.trans hl.symm)
  rw [hkl]

private theorem normPowerPairs_finiteCard (m : ℕ) :
    ∃ h : (normPowerPairs F m).Finite,
      h.toFinset.card ≤ Module.finrank ℚ F := by
  classical
  by_cases hne : (normPowerPairs F m).Nonempty
  · obtain ⟨⟨P, k⟩, hPk⟩ := hne
    have hk : 0 < k := hPk.1
    obtain ⟨p, d, hp, hd, _, hn⟩ := primeIdeal_norm_isPrimePower F P
    let pZ : Ideal ℤ := Ideal.span {(p : ℤ)}
    letI : Fact p.Prime := ⟨hp⟩
    letI : pZ.IsMaximal := Int.ideal_span_isMaximal_of_prime p
    have hpZ : pZ ≠ ⊥ := by
      change Ideal.span {(p : ℤ)} ≠ ⊥
      simpa using hp.ne_zero
    let A := IsDedekindDomain.primesOverFinset pZ (𝓞 F)
    have hm : p ^ (d * k) = m := by rw [pow_mul, ← hn]; exact hPk.2
    have hmaps : MapsTo (fun a : PrimeIdeal F × ℕ => a.1.asIdeal) (normPowerPairs F m) (A : Set (Ideal (𝓞 F))) := by
      rintro ⟨Q,l⟩ hQl
      have hl : 0 < l := hQl.1
      obtain ⟨q, e, hq, he, hlie, hN⟩ := primeIdeal_norm_isPrimePower F Q
      have hml : q ^ (e * l) = m := by rw [pow_mul, ← hN]; exact hQl.2
      have hpq := (Nat.Prime.pow_inj' hp hq (Nat.mul_ne_zero hd.ne' hk.ne')
        (Nat.mul_ne_zero he.ne' hl.ne') (hm.trans hml.symm)).1
      subst q
      exact (IsDedekindDomain.mem_primesOverFinset_iff hpZ (𝓞 F)).mpr ⟨Q.isPrime, hlie⟩
    have hfin : (normPowerPairs F m).Finite :=
      (A.finite_toSet.subset hmaps.image_subset).of_finite_image (normPowerPairs_injOn F m)
    refine ⟨hfin, ?_⟩
    have hcard : hfin.toFinset.card ≤ A.card := by
      apply Finset.card_le_card_of_injOn (fun a => a.1.asIdeal)
      · simpa using hmaps
      · simpa using normPowerPairs_injOn F m
    exact hcard.trans (Ideal.card_primesOverFinset_le_finrank (𝓞 F) ℚ F hpZ)
  · have hEmpty := Set.not_nonempty_iff_eq_empty.mp hne
    have hfin : (normPowerPairs F m).Finite := hEmpty ▸ Set.finite_empty
    refine ⟨hfin, ?_⟩
    have he : hfin.toFinset = ∅ := by
      ext a
      simp [hEmpty]
    rw [he]
    simp

private theorem normPowerPairs_idealPower_injOn (m : ℕ) :
    InjOn (fun a : PrimeIdeal F × ℕ => a.1.asIdeal ^ a.2) (normPowerPairs F m) := by
  rintro ⟨P, k⟩ hP ⟨Q, l⟩ hQ h
  have hpow : P.asIdeal ^ k = Q.asIdeal ^ l := h
  have hk : 0 < k := hP.1
  have hl : 0 < l := hQ.1
  have hLe : P.asIdeal ≤ Q.asIdeal := by
    intro z hz
    have hzP : z ^ k ∈ P.asIdeal ^ k := Ideal.pow_mem_pow hz k
    rw [hpow] at hzP
    exact (Q.isPrime.pow_mem_iff_mem k hk).mp (Ideal.pow_le_self hl.ne' hzP)
  have hPMax : P.asIdeal.IsMaximal := P.isPrime.isMaximal P.ne_bot
  exact normPowerPairs_injOn F m hP hQ (hPMax.eq_of_le Q.isPrime.ne_top hLe)

private theorem normPowerPairs_idealPower_norm {m : ℕ} {a : PrimeIdeal F × ℕ}
    (ha : a ∈ normPowerPairs F m) : Ideal.absNorm (a.1.asIdeal ^ a.2) = m := by
  rw [map_pow]
  exact ha.2

/-- At most `[F : ℚ]` positive prime-power presentations can have a fixed norm. -/
theorem card_positivePrimePowers_of_norm (A : Finset (PrimeIdeal F × ℕ)) (m : ℕ)
    (hA : ∀ a ∈ A, 0 < a.2 ∧ Ideal.absNorm (a.1.asIdeal ^ a.2) = m) :
    A.card ≤ Module.finrank ℚ F := by
  obtain ⟨hfin, hcard⟩ := normPowerPairs_finiteCard F m
  refine (Finset.card_le_card (show A ⊆ hfin.toFinset from ?_)).trans hcard
  intro a ha
  obtain ⟨hk, hn⟩ := hA a ha
  exact (Set.Finite.mem_toFinset hfin).mpr ⟨hk, (map_pow Ideal.absNorm _ _).symm.trans hn⟩

/-- The grouped coefficient (B.6.1.14), as a finite sum over the contributing
prime-power presentations. The sum over all other ideals has zero summands. -/
noncomputable def groupedPrimePowerCoefficient (χ : Ideal (𝓞 F) → ℂ) (m : ℕ) : ℂ :=
  ∑ a ∈ (Classical.choose (normPowerPairs_finiteCard F m)).toFinset,
    χ (a.1.asIdeal ^ a.2) * Real.log (Ideal.absNorm a.1.asIdeal : ℝ)

/-- The contributing ideal powers have norm m and occur with no duplicates,
so the prime-power sum reindexes the von Mangoldt coefficient. -/
theorem groupedPrimePowerCoefficient_ideal_index (m : ℕ) :
    let A := (Classical.choose (normPowerPairs_finiteCard F m)).toFinset
    (∀ a ∈ A, Ideal.absNorm (a.1.asIdeal ^ a.2) = m) ∧
    InjOn (fun a : PrimeIdeal F × ℕ => a.1.asIdeal ^ a.2) (A : Set (PrimeIdeal F × ℕ)) := by
  dsimp
  constructor
  · intro a ha
    exact normPowerPairs_idealPower_norm F (by simpa using ha)
  · simpa using normPowerPairs_idealPower_injOn F m

/-- Lemma B.6.1.4. The coefficient bound is uniform in the character.
Every nonzero summand is indexed by a prime above the same rational prime,
and its logarithm is at most `log m`. -/
theorem groupedPrimePowerCoefficient_norm_le (χ : Ideal (𝓞 F) → ℂ)
    (hχ : ∀ I, ‖χ I‖ ≤ 1) {m : ℕ} (hm : 0 < m) :
    ‖groupedPrimePowerCoefficient F χ m‖ ≤ (Module.finrank ℚ F : ℝ) * Real.log m := by
  classical
  let h := Classical.choose (normPowerPairs_finiteCard F m)
  let A := h.toFinset
  have hA : A.card ≤ Module.finrank ℚ F := Classical.choose_spec (normPowerPairs_finiteCard F m)
  unfold groupedPrimePowerCoefficient
  change ‖∑ a ∈ A, χ (a.1.asIdeal ^ a.2) * Real.log (Ideal.absNorm a.1.asIdeal : ℝ)‖ ≤ _
  calc
    _ ≤ ∑ a ∈ A, ‖χ (a.1.asIdeal ^ a.2) * Real.log (Ideal.absNorm a.1.asIdeal : ℝ)‖ := norm_sum_le _ _
    _ ≤ ∑ _a ∈ A, Real.log m := by
      apply Finset.sum_le_sum
      intro a ha
      have hs : a ∈ normPowerPairs F m := by simpa [A] using ha
      have hlog : 0 ≤ Real.log (Ideal.absNorm a.1.asIdeal : ℝ) :=
        Real.log_nonneg (by exact_mod_cast (primeIdeal_one_lt_norm F a.1).le)
      have hle : Ideal.absNorm a.1.asIdeal ≤ m := hs.2 ▸ Nat.le_pow hs.1
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hlog]
      exact (mul_le_of_le_one_left hlog (hχ _)).trans
        (Real.log_le_log (by exact_mod_cast (primeIdeal_one_lt_norm F a.1).pos) (by exact_mod_cast hle))
    _ ≤ _ := by
      rw [Finset.sum_const, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hA) (Real.log_nonneg (by exact_mod_cast hm))

end Masullo
