import HeckePerronCoefficients
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.NumberTheory.Harmonic.Bounds

open Filter NumberField Ideal IsDedekindDomain Set MeasureTheory
open scoped Classical Interval NumberField Topology

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

local notation "Place" => HeightOneSpectrum (𝓞 F)

private theorem tsum_nat_rpow_le {t : ℝ} (ht : 0 < t) :
    ∑' n : ℕ, (n : ℝ) ^ (-1 - t) ≤ 1 + t⁻¹ := by
  let a : ℝ := -1 - t
  have ha : a < -1 := by dsimp [a]; linarith
  have han : a < 0 := ha.trans (by norm_num)
  have hanti : AntitoneOn (fun r : ℝ ↦ r ^ a) (Ici (1 : ℝ)) := by
    intro x hx y _ hxy
    exact Real.rpow_le_rpow_of_nonpos (zero_lt_one.trans_le hx) hxy han.le
  have hi := integrableOn_Ioi_rpow_of_lt ha zero_lt_one
  have hnon (r : ℝ) (hr : r ∈ Ioi (1 : ℝ)) : 0 ≤ r ^ a :=
    Real.rpow_nonneg (zero_le_one.trans hr.le) _
  have hs := AntitoneOn.summable_of_integrableOn_Ioi (N := 1) (by simpa using hanti)
    (by simpa using hi) (by simpa using hnon)
  have hb := AntitoneOn.tsum_comp_add_le_integral (N := 1) (by simpa using hanti)
    (by simpa using hi) (by simpa using hnon)
  norm_cast at hb
  rw [integral_Ioi_rpow_of_lt ha zero_lt_one, Real.one_rpow,
    show a + 1 = -t by dsimp [a]; ring, div_neg, neg_div, neg_neg, one_div] at hb
  change (∑' n : ℕ, (n : ℝ) ^ a) ≤ 1 + t⁻¹
  rw [← hs.sum_add_tsum_nat_add 2]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.cast_zero,
    Nat.cast_one, Real.zero_rpow han.ne, Real.one_rpow]
  have hb' : (∑' n : ℕ, ((n + 2 : ℕ) : ℝ) ^ a) ≤ t⁻¹ := by
    simpa [Nat.cast_add, add_assoc, one_add_one_eq_two] using hb
  simpa using add_le_add_left hb' (1 : ℝ)

/-- On a real shift of the one-line the absolute Dirichlet series of the
grouped von Mangoldt coefficients is bounded quadratically in the inverse shift. -/
theorem tsum_norm_term_heckeVonMangoldtCoefficient_le (c : Place → ℂ)
    (hc : ∀ v, ‖c v‖ ≤ 1) {s : ℂ} (hs : s.re = 1) {κ : ℝ} (hκ : 0 < κ) (hκ₁ : κ ≤ 1) :
    ∑' n : ℕ, ‖LSeries.term (heckeVonMangoldtCoefficient F c) (s + (κ : ℂ)) n‖ ≤
      6 * (Module.finrank ℚ F : ℝ) / κ ^ 2 := by
  let t : ℝ := κ / 2
  let D : ℝ := Module.finrank ℚ F
  have ht : 0 < t := half_pos hκ
  have hs' : (s + (κ : ℂ)).re = 1 + κ := by simp [Complex.add_re, hs]
  have hsum := summable_norm_term_heckeVonMangoldtCoefficient F c hc (show
    1 < (s + (κ : ℂ)).re by rw [hs']; linarith)
  have hpow : Summable (fun n : ℕ ↦ (n : ℝ) ^ (-1 - t)) :=
    (Real.summable_nat_rpow).mpr (by linarith)
  have hD : 0 ≤ D := by positivity
  have hterm (n : ℕ) : ‖LSeries.term (heckeVonMangoldtCoefficient F c) (s + (κ : ℂ)) n‖ ≤
      (D / t) * (n : ℝ) ^ (-1 - t) := by
    by_cases hn : n = 0
    · subst n
      simp only [LSeries.term_zero, norm_zero]
      exact mul_nonneg (div_nonneg hD ht.le) (Real.rpow_nonneg (by positivity) _)
    have hn' : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    rw [LSeries.term_of_ne_zero hn, norm_div, Complex.norm_natCast_cpow_of_pos
      (Nat.pos_of_ne_zero hn), hs']
    calc
      _ ≤ (D * Real.log n) / (n : ℝ) ^ (1 + κ) := by
        gcongr
        exact norm_heckeVonMangoldtCoefficient_le F c hc n
      _ ≤ (D * ((n : ℝ) ^ t / t)) / (n : ℝ) ^ (1 + κ) := by
        gcongr
        exact Real.log_le_rpow_div hn'.le ht
      _ = _ := by
        rw [show (D * ((n : ℝ) ^ t / t)) / (n : ℝ) ^ (1 + κ) =
          (D / t) * ((n : ℝ) ^ t / (n : ℝ) ^ (1 + κ)) by ring,
          ← Real.rpow_sub hn', show t - (1 + κ) = -1 - t by dsimp [t]; ring]
  calc
    _ ≤ ∑' n : ℕ, (D / t) * (n : ℝ) ^ (-1 - t) :=
      hsum.tsum_le_tsum hterm (hpow.mul_left _)
    _ ≤ (D / t) * (1 + t⁻¹) := by
      rw [hpow.tsum_mul_left]
      exact mul_le_mul_of_nonneg_left (tsum_nat_rpow_le ht) (by positivity)
    _ ≤ _ := by
      dsimp [t]
      rw [show D / (κ / 2) * (1 + (κ / 2)⁻¹) = (2 * D * (κ + 2)) / κ ^ 2 by
        field_simp]
      exact div_le_div_of_nonneg_right (by nlinarith) (sq_nonneg _)

private theorem sum_inv_cutoff_distances_le {x b : ℝ} (hx : 1 ≤ x) (hb : 0 < b)
    (S : Finset ℕ) (hS : ∀ n ∈ S, (n : ℝ) ≤ 2 * x ∧ b ≤ |x - (n : ℝ)|) :
    ∑ n ∈ S, |x - (n : ℝ)|⁻¹ ≤ 2 * (b⁻¹ + 1 + Real.log (2 * x)) := by
  let d (n : ℕ) := |x - (n : ℝ)|
  let k (n : ℕ) := ⌊d n⌋₊
  let N := ⌊2 * x⌋₊
  let w (i : ℕ) := if i = 0 then b⁻¹ else (i : ℝ)⁻¹
  have hstep (A : Finset ℕ) (hA : A ⊆ S) (hinj : Set.InjOn k (A : Set ℕ)) :
      ∑ n ∈ A, (d n)⁻¹ ≤ b⁻¹ + 1 + Real.log (2 * x) := by
    calc
      _ ≤ ∑ n ∈ A, w (k n) := by
        apply Finset.sum_le_sum
        intro n hn
        by_cases hz : k n = 0
        · rw [show w (k n) = b⁻¹ by simp [w, hz] ]
          exact inv_anti₀ hb (hS n (hA hn)).2
        · rw [show w (k n) = (k n : ℝ)⁻¹ by simp [w, hz] ]
          exact inv_anti₀ (by exact_mod_cast Nat.pos_of_ne_zero hz) (Nat.floor_le (abs_nonneg _))
      _ = ∑ i ∈ A.image k, w i := (Finset.sum_image hinj).symm
      _ ≤ ∑ i ∈ Finset.range (N + 1), w i := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro i hi
          obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hi
          apply Finset.mem_range.mpr
          apply Nat.lt_succ_of_le
          apply Nat.floor_mono
          have hh := (hS n (hA hn)).1
          dsimp [d]
          rw [abs_le]
          constructor <;> linarith [Nat.cast_nonneg (α := ℝ) n]
        · intro i _ _
          simp only [w]
          split_ifs <;> positivity
      _ = b⁻¹ + (harmonic N : ℝ) := by
        rw [Finset.sum_range_succ', add_comm]
        simp only [w, ite_eq_left rfl, Nat.add_one_ne_zero, ite_false, harmonic,
          Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
      _ ≤ _ := by
        linarith [harmonic_floor_le_one_add_log (2 * x) (by linarith)]
  have hinj (n m : ℕ) (he : k n = k m)
      (hside : ((n : ℝ) ≤ x ∧ (m : ℝ) ≤ x) ∨ (x ≤ (n : ℝ) ∧ x ≤ (m : ℝ))) :
      n = m := by
    have hn₁ : (k n : ℝ) ≤ d n := Nat.floor_le (abs_nonneg _)
    have hm₁ : (k m : ℝ) ≤ d m := Nat.floor_le (abs_nonneg _)
    have hn₂ : d n < (k n : ℝ) + 1 := Nat.lt_floor_add_one _
    have hm₂ : d m < (k m : ℝ) + 1 := Nat.lt_floor_add_one _
    rw [he] at hn₁ hn₂
    have hdist₁ : d n < d m + 1 := by linarith
    have hdist₂ : d m < d n + 1 := by linarith
    have hboth : (n : ℝ) < (m : ℝ) + 1 ∧ (m : ℝ) < (n : ℝ) + 1 := by
      dsimp [d] at hdist₁ hdist₂
      rcases hside with ⟨hn, hm⟩ | ⟨hn, hm⟩
      · simp only [abs_of_nonneg (sub_nonneg.mpr hn), abs_of_nonneg (sub_nonneg.mpr hm)] at hdist₁ hdist₂
        constructor <;> linarith
      · simp only [abs_of_nonpos (sub_nonpos.mpr hn), abs_of_nonpos (sub_nonpos.mpr hm)] at hdist₁ hdist₂
        constructor <;> linarith
    exact le_antisymm (Nat.le_of_lt_succ (by exact_mod_cast hboth.1))
      (Nat.le_of_lt_succ (by exact_mod_cast hboth.2))
  rw [← Finset.sum_filter_add_sum_filter_not S (fun n : ℕ ↦ (n : ℝ) ≤ x)]
  refine (add_le_add
    (hstep _ (Finset.filter_subset _ _) ?_)
    (hstep _ (Finset.filter_subset _ _) ?_)).trans_eq (by ring)
  · intro n hn m hm he
    exact hinj n m he (.inl ⟨(Finset.mem_filter.mp hn).2, (Finset.mem_filter.mp hm).2⟩)
  · intro n hn m hm he
    exact hinj n m he (.inr ⟨le_of_not_ge (Finset.mem_filter.mp hn).2,
      le_of_not_ge (Finset.mem_filter.mp hm).2⟩)

/-- On the one-line the full prime-power cutoff is approximated by the
right-edge Perron integral with explicit far, near and diagonal bounds.
For an integer cutoff one may use `b = 1`; for a noninteger cutoff any
positive separation from the integers may serve as `b`. -/
theorem heckeEulerProduct_truncatedPerron_full_le (c : Place → ℂ) (hc : ∀ v, ‖c v‖ ≤ 1)
    {s : ℂ} (hs : s.re = 1) {x κ T b : ℝ} (hx : 1 ≤ x)
    (hκ : 0 < κ) (hκ₁ : κ ≤ 1) (hT : 0 < T) (hb : 0 < b)
    (hsep : ∀ n : ℕ, x ≠ (n : ℝ) → b ≤ |x - (n : ℝ)|) :
    let z (y : ℝ) : ℂ := (κ : ℂ) + (y : ℂ) * Complex.I
    let D : ℝ := Module.finrank ℚ F
    ‖((∫ y in -T..T,
        -logDeriv (fun w ↦ ∏' v, heckeEulerFactor F c v w) (s + z y) *
          (Complex.exp ((Real.log x : ℂ) * z y) / z y)) / (2 * (Real.pi : ℂ))) -
        heckePerronFullSum F c s x‖ ≤
      Real.exp (Real.log x * κ) / (Real.pi * T * Real.log 2) * (6 * D / κ ^ 2) +
      (2 * (D * Real.log (2 * x)) * Real.exp (Real.log 2 * κ) / (Real.pi * T)) *
        (2 * (b⁻¹ + 1 + Real.log (2 * x))) +
      (if (⌈x⌉₊ : ℝ) = x then D * Real.log x / (2 * x) +
        D * Real.log x / x * (κ / (Real.pi * T)) else 0) := by
  intro z D
  let a := heckeVonMangoldtCoefficient F c
  let E (n : ℕ) := ‖LSeries.term a s n‖ * perronError (Real.log x - Real.log (n : ℝ)) κ T
  let isFar (n : ℕ) := (n : ℝ) ≤ x / 2 ∨ 2 * x ≤ (n : ℝ)
  let far (n : ℕ) := if isFar n then E n else 0
  let near (n : ℕ) := if ¬isFar n ∧ x ≠ (n : ℝ) then E n else 0
  let diag (n : ℕ) := if x = (n : ℝ) then E n else 0
  let M := 2 * (D * Real.log (2 * x)) * Real.exp (Real.log 2 * κ) / (Real.pi * T)
  let A := Real.exp (Real.log x * κ) / (Real.pi * T * Real.log 2) * (6 * D / κ ^ 2)
  let B := M * (2 * (b⁻¹ + 1 + Real.log (2 * x)))
  let C := if (⌈x⌉₊ : ℝ) = x then D * Real.log x / x * (κ / (Real.pi * T)) else 0
  let H := if (⌈x⌉₊ : ℝ) = x then D * Real.log x / (2 * x) else 0
  have hx₀ := zero_lt_one.trans_le hx
  have hline : 1 < s.re + κ := by linarith
  have hs' : 1 < (s + (κ : ℂ)).re := by simpa [Complex.add_re] using hline
  obtain ⟨hE, hperron⟩ := heckeEulerProduct_truncatedPerron F c hc s hx₀ hκ hT hline
  have hnon (n : ℕ) : 0 ≤ E n :=
    mul_nonneg (norm_nonneg _) (perronError_nonneg _ hκ hT)
  have hsplit (n : ℕ) : E n = far n + near n + diag n := by
    by_cases he : x = (n : ℝ)
    · have hf : ¬isFar n := by dsimp [isFar]; rw [← he]; simp only [not_or]; constructor <;> linarith
      simp [far, near, diag, he, hf]
    · by_cases hf : isFar n <;> simp [far, near, diag, he, hf]
  have hsumPart (p : ℕ → Prop) [DecidablePred p] :
      Summable (fun n ↦ if p n then E n else 0) := by
    refine hE.of_nonneg_of_le (fun n ↦ ?_) (fun n ↦ ?_)
    · split_ifs <;> first | exact hnon n | exact le_rfl
    · split_ifs <;> first | exact le_rfl | exact hnon n
  have sf : Summable far := hsumPart isFar
  have sn : Summable near := hsumPart (fun n ↦ ¬isFar n ∧ x ≠ (n : ℝ))
  have sd : Summable diag := hsumPart (fun n ↦ x = (n : ℝ))
  have ha : ∑' n, far n ≤ A := by
    refine (tsum_perronError_far_le a s hx₀ hκ hT
      (summable_norm_term_heckeVonMangoldtCoefficient F c hc hs')).trans ?_
    have hh := tsum_norm_term_heckeVonMangoldtCoefficient_le F c hc hs hκ hκ₁
    dsimp only [A]
    apply mul_le_mul_of_nonneg_left hh
    positivity
  have hB : ∑' n, near n ≤ B := by
    let S := (Finset.range (⌈2 * x⌉₊ + 1)).filter fun n ↦ ¬isFar n ∧ x ≠ (n : ℝ)
    have hS (n : ℕ) (hn : n ∈ S) : ¬isFar n ∧ x ≠ (n : ℝ) := (Finset.mem_filter.mp hn).2
    rw [tsum_eq_sum (s := S)]
    · calc
        _ ≤ ∑ n ∈ S, M * |x - (n : ℝ)|⁻¹ := by
          apply Finset.sum_le_sum
          intro n hn
          have hn' := hS n hn
          have hv : x / 2 < (n : ℝ) ∧ (n : ℝ) < 2 * x := by
            simpa [isFar] using hn'.1
          rw [show near n = E n by simp [near, hn'] ]
          exact (heckePerronError_near_le F c hc hs hx₀ hκ hT hv.1.le hv.2.le hn'.2).trans_eq
            (by dsimp only [M]; ring)
        _ ≤ B := by
          rw [← Finset.mul_sum]
          apply mul_le_mul_of_nonneg_left (sum_inv_cutoff_distances_le hx hb S ?_) (by
            have : 0 ≤ Real.log (2 * x) := Real.log_nonneg (by linarith)
            dsimp only [M, D]; positivity)
          intro n hn
          have hn' := hS n hn
          have hv : (n : ℝ) < 2 * x := lt_of_not_ge fun hz ↦ hn'.1 (.inr hz)
          exact ⟨hv.le, hsep n hn'.2⟩
    · intro n hn
      by_contra he
      have hh : ¬isFar n ∧ x ≠ (n : ℝ) := by
        by_contra hz
        exact he (by simp [near, hz])
      apply hn
      apply Finset.mem_filter.mpr
      have hl : (n : ℝ) < 2 * x := lt_of_not_ge fun hz ↦ hh.1 (.inr hz)
      exact ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.lt_ceil.mpr hl).le), hh⟩
  have hd : ∑' n, diag n ≤ C := by
    rw [tsum_eq_sum (s := {⌈x⌉₊})]
    · rw [Finset.sum_singleton]
      by_cases he : (⌈x⌉₊ : ℝ) = x
      · simp only [diag, he, ite_true, C, E, sub_self, perronError]
        apply mul_le_mul_of_nonneg_right
          (by simpa [he] using norm_term_heckeVonMangoldtCoefficient_le F c hc hs ⌈x⌉₊)
          (by positivity)
      · simp [diag, C, he, Ne.symm he]
    · intro n hn
      by_cases he : x = (n : ℝ)
      · exfalso
        apply hn
        rw [he, Nat.ceil_natCast, Finset.mem_singleton]
      · simp [diag, he]
  have hsum : ∑' n, E n ≤ A + B + C := calc
    _ = (∑' n, far n) + (∑' n, near n) + ∑' n, diag n := by
      simp_rw [hsplit]
      rw [(sf.add sn).tsum_add sd, sf.tsum_add sn]
    _ ≤ _ := add_le_add (add_le_add ha hB) hd
  have hcut := norm_heckePerronFullSum_sub_halfSum_le F c hc hs x
  let I := ((∫ y in -T..T,
    -logDeriv (fun w ↦ ∏' v, heckeEulerFactor F c v w) (s + z y) *
      (Complex.exp ((Real.log x : ℂ) * z y) / z y)) / (2 * (Real.pi : ℂ)))
  change ‖I - heckePerronFullSum F c s x‖ ≤ _
  calc
    _ ≤ ‖I - heckePerronHalfSum F c s x‖ +
        ‖heckePerronFullSum F c s x - heckePerronHalfSum F c s x‖ := by
      rw [← norm_neg (heckePerronFullSum F c s x - _), neg_sub]
      exact norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ (A + B + C) + H := add_le_add (hperron.trans hsum) hcut
    _ = _ := by
      dsimp only [A, B, C, H, M]
      split_ifs <;> ring

theorem perronIntegerSeparation (m n : ℤ) (h : (m : ℝ) ≠ (n : ℝ)) :
    1 ≤ |(m : ℝ) - (n : ℝ)| := by
  have hn : m - n ≠ 0 := by
    intro he
    have he' := sub_eq_zero.mp he
    apply h
    exact_mod_cast he'
  exact_mod_cast Int.one_le_abs hn

/-- The two kinds of cutoffs in the manuscript's `J_b` have a common
separation bound for all off-diagonal terms. -/
theorem perronAdmissibleCutoff_separation {x b : ℝ}
    (hx : (∃ m : ℤ, x = (m : ℝ)) ∨ ∀ m : ℤ, b ≤ |x - (m : ℝ)|)
    (n : ℕ) (hn : x ≠ (n : ℝ)) : min b 1 ≤ |x - (n : ℝ)| := by
  rcases hx with ⟨m, rfl⟩ | h
  · exact (min_le_right _ _).trans (by
      simpa using perronIntegerSeparation m (n : ℤ) (by simpa using hn))
  · exact (min_le_left _ _).trans (by simpa using h (n : ℤ))

/-- With the manuscript's contour parameters, the right-edge truncation
error tends to zero uniformly on the one-line and over cutoffs separated
from all unequal integers by a common positive distance. -/
theorem heckeContinuation_truncatedPerron_full_eventually (c : Place → ℂ)
    (hc : ∀ v, ‖c v‖ ≤ 1) (L : ℂ → ℂ)
    (hL : EqOn L (fun w ↦ ∏' v, heckeEulerFactor F c v w) {w | 1 < w.re})
    {b : ℝ} (hb : 0 < b) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, (∀ n : ℕ, x ≠ (n : ℝ) → b ≤ |x - (n : ℝ)|) →
      ∀ s : ℂ, s.re = 1 →
        let z (y : ℝ) : ℂ := (((Real.log x)⁻¹ : ℝ) : ℂ) + (y : ℂ) * Complex.I
        let T := Real.log x ^ 3
        ‖((∫ y in -T..T,
          -logDeriv L (s + z y) *
            (Complex.exp ((Real.log x : ℂ) * z y) / z y)) / (2 * (Real.pi : ℂ))) -
          heckePerronFullSum F c s x‖ < ε := by
  let D : ℝ := Module.finrank ℚ F
  let C₁ := Real.exp 1 * (6 * D) / (Real.pi * Real.log 2) +
    (16 * D / Real.pi) * (b⁻¹ + 3)
  let C₂ := D * ((1 / 2 : ℝ) + Real.pi⁻¹)
  have ht : Tendsto (fun x : ℝ ↦ C₁ * (Real.log x)⁻¹ + C₂ * (Real.log x / x)) atTop (𝓝 0) := by
    have hlog : Tendsto (fun x : ℝ ↦ Real.log x / x) atTop (𝓝 0) := by
      simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
    simpa using ((tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop).const_mul C₁).add
      (hlog.const_mul C₂)
  filter_upwards [ht.eventually (gt_mem_nhds hε), eventually_ge_atTop (2 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop 1] with x herr hx₂ hlog₁ hsep s hs
  let ℓ := Real.log x
  have hℓ : 1 ≤ ℓ := hlog₁
  have hℓ₀ : 0 < ℓ := zero_lt_one.trans_le hℓ
  have hx₀ : 0 < x := by linarith
  have hκ₁ : ℓ⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hℓ
  have hκ : 0 < ℓ⁻¹ := inv_pos.mpr hℓ₀
  have hT : 0 < ℓ ^ 3 := pow_pos hℓ₀ _
  have hD : 0 ≤ D := by positivity
  have hlog₂ : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog_le : Real.log (2 * x) ≤ 2 * ℓ := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hx₀.ne']
    linarith [Real.log_le_log (by norm_num : 0 < (2 : ℝ)) hx₂]
  have hlog₂x : 0 ≤ Real.log (2 * x) := Real.log_nonneg (by linarith)
  have hπ := Real.pi_pos
  have hB₀ : 0 ≤ b⁻¹ + 3 := by positivity
  have hfar :
      Real.exp (ℓ * ℓ⁻¹) / (Real.pi * ℓ ^ 3 * Real.log 2) * (6 * D / (ℓ⁻¹) ^ 2) =
        (Real.exp 1 * (6 * D) / (Real.pi * Real.log 2)) * ℓ⁻¹ := by
    rw [mul_inv_cancel₀ hℓ₀.ne']
    field_simp
  have hbnd : b⁻¹ + 1 + Real.log (2 * x) ≤ (b⁻¹ + 3) * ℓ := by
    nlinarith [mul_nonneg (inv_nonneg.mpr hb.le) (sub_nonneg.mpr hℓ)]
  have hexp : Real.exp (Real.log 2 * ℓ⁻¹) ≤ 2 := by
    calc
      _ ≤ Real.exp (Real.log 2) := Real.exp_le_exp.mpr (mul_le_of_le_one_right hlog₂.le hκ₁)
      _ = _ := Real.exp_log (by norm_num)
  have hnear :
      (2 * (D * Real.log (2 * x)) * Real.exp (Real.log 2 * ℓ⁻¹) / (Real.pi * ℓ ^ 3)) *
        (2 * (b⁻¹ + 1 + Real.log (2 * x))) ≤ ((16 * D / Real.pi) * (b⁻¹ + 3)) * ℓ⁻¹ := by
    calc
      _ ≤ (2 * (D * (2 * ℓ)) * 2 / (Real.pi * ℓ ^ 3)) * (2 * ((b⁻¹ + 3) * ℓ)) := by
        gcongr
      _ = _ := by field_simp; ring
  have hpow : 1 ≤ ℓ ^ 3 := one_le_pow₀ hℓ
  have hdiag :
      (if (⌈x⌉₊ : ℝ) = x then D * Real.log x / (2 * x) +
          D * Real.log x / x * (ℓ⁻¹ / (Real.pi * ℓ ^ 3)) else 0) ≤ C₂ * (ℓ / x) := by
    split_ifs
    · calc
        _ ≤ D * ℓ / (2 * x) + D * ℓ / x * (1 / (Real.pi * 1)) := by
          gcongr
        _ = _ := by dsimp only [C₂]; ring
    · dsimp only [C₂]; positivity
  intro z T
  have hcontour :
      (∫ y in -T..T, -logDeriv L (s + z y) *
          (Complex.exp ((Real.log x : ℂ) * z y) / z y)) =
        (∫ y in -T..T, -logDeriv (fun w ↦ ∏' v, heckeEulerFactor F c v w) (s + z y) *
          (Complex.exp ((Real.log x : ℂ) * z y) / z y)) := by
    apply intervalIntegral.integral_congr
    intro y _
    have hRight : 1 < (s + z y).re := by
      simpa [z, hs, Complex.add_re, Complex.mul_re] using hℓ₀
    have hopen : IsOpen {w : ℂ | 1 < w.re} := isOpen_lt continuous_const Complex.continuous_re
    have he : L =ᶠ[𝓝 (s + z y)] (fun w ↦ ∏' v, heckeEulerFactor F c v w) :=
      Filter.Eventually.mono (hopen.mem_nhds hRight) (fun _ hw ↦ hL hw)
    simp only [logDeriv, Pi.div_apply]
    rw [he.deriv_eq, hL hRight]
  rw [hcontour]
  refine (heckeEulerProduct_truncatedPerron_full_le F c hc hs (by linarith) hκ hκ₁ hT hb hsep).trans_lt ?_
  apply lt_of_le_of_lt (add_le_add (add_le_add hfar.le hnear) hdiag)
  change C₁ * ℓ⁻¹ + C₂ * (ℓ / x) < ε at herr
  simpa only [C₁, add_mul] using herr

end

end Masullo
