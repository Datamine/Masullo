import SLocalLaurentFormula
import CompactPeriodizationSection
import Mathlib.NumberTheory.RamificationInertia.Inertia

open Function IsDedekindDomain NumberField Set
open scoped Classical NumberField

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]
variable (S : Finset (HeightOneSpectrum (𝓞 F)))

private abbrev K := SLocalThetaNormOne F S

/-- The places of this stage lying over the positive rational prime p. -/
def sLocalPrimaryPlaces (p : ℕ) : Finset S :=
  Finset.univ.filter fun v ↦ v.val.asIdeal.under ℤ = Ideal.span {(p : ℤ)}

private abbrev inertia (p : ℕ) (v : S) :=
  (Ideal.span {(p : ℤ)}).inertiaDeg' v.val.asIdeal

/-- The periods of all local factors above one rational prime divide this period. -/
def sLocalPrimaryEulerPeriod (p : ℕ) : ℝ :=
  2 * Real.pi / Real.log (p : ℝ)

theorem sLocalPrimaryEulerPeriod_pos {p : ℕ} (hp : p.Prime) :
    0 < sLocalPrimaryEulerPeriod p :=
  div_pos (mul_pos (by norm_num) Real.pi_pos) (Real.log_pos (by exact_mod_cast hp.one_lt))

private theorem absNorm_eq_primary_power {p : ℕ} (hp : p.Prime) {v : S}
    (hv : v ∈ sLocalPrimaryPlaces F S p) :
    v.val.asIdeal.absNorm = p ^ inertia F S p v := by
  have h := (Finset.mem_filter.mp hv).2
  letI : v.val.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) := ⟨h.symm⟩
  exact Ideal.absNorm_eq_pow_inertiaDeg' v.val.asIdeal hp

private theorem primary_inertia_pos {p : ℕ} (hp : p.Prime) {v : S}
    (hv : v ∈ sLocalPrimaryPlaces F S p) : 0 < inertia F S p v := by
  have h := absNorm_eq_primary_power F S hp hv
  by_contra! hn
  rw [Nat.eq_zero_of_le_zero hn, pow_zero] at h
  exact (NumberField.HeightOneSpectrum.one_lt_absNorm v.val).ne h.symm

private theorem primary_period_eq_local_mul {p : ℕ} (hp : p.Prime) {v : S}
    (hv : v ∈ sLocalPrimaryPlaces F S p) :
    sLocalPrimaryEulerPeriod p =
      (inertia F S p v : ℝ) * (2 * Real.pi / Real.log (v.val.asIdeal.absNorm : ℝ)) := by
  have h := absNorm_eq_primary_power F S hp hv
  have hf : (inertia F S p v : ℝ) ≠ 0 := by
    exact_mod_cast (primary_inertia_pos F S hp hv).ne'
  have hp0 := (Real.log_pos (show 1 < (p : ℝ) by exact_mod_cast hp.one_lt)).ne'
  rw [sLocalPrimaryEulerPeriod, h, Nat.cast_pow, Real.log_pow]
  field_simp

/-- The exact Euler multipliers over a fixed rational prime share a
vertical period, even when the residue degrees and phases differ. -/
theorem sLocalPrimaryEulerMultiplier_periodic (ω : PontryaginDual (K F S))
    {p : ℕ} (hp : p.Prime) {v : S} (hv : v ∈ sLocalPrimaryPlaces F S p) (z : ℂ) (m : ℤ) :
    finiteZetaWeilMultiplier F v.val (sLocalFiniteZetaPhases F S ω v)
        (z + ((m : ℝ) * sLocalPrimaryEulerPeriod p : ℝ) * Complex.I) =
      finiteZetaWeilMultiplier F v.val (sLocalFiniteZetaPhases F S ω v) z := by
  let L := Real.log (v.val.asIdeal.absNorm : ℝ)
  let f := inertia F S p v
  let q := sLocalFiniteZetaPhases F S ω v
  have hL : L ≠ 0 := (Real.log_pos (by
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v.val)).ne'
  have hτ : sLocalPrimaryEulerPeriod p * L = (f : ℝ) * (2 * Real.pi) := by
    rw [primary_period_eq_local_mul F S hp hv, mul_assoc, div_mul_cancel₀ _ hL]
  by_cases hq : finiteZetaUnramified F v.val q
  · change finiteZetaWeilMultiplier F v.val q _ = finiteZetaWeilMultiplier F v.val q z
    simp only [finiteZetaWeilMultiplier, ite_eq_left hq, finiteZetaRatio]
    congr 2
    have he : -(z + ((m : ℝ) * sLocalPrimaryEulerPeriod p : ℝ) * Complex.I) * (L : ℂ) =
        -z * (L : ℂ) + (-m * (f : ℤ) : ℤ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      have hc : ((sLocalPrimaryEulerPeriod p : ℝ) : ℂ) * (L : ℂ) =
          (f : ℂ) * (2 * (Real.pi : ℂ)) := by exact_mod_cast hτ
      push_cast
      linear_combination -((m : ℂ) * Complex.I) * hc
    rw [he, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  · simp [finiteZetaWeilMultiplier, q, hq]

/-- The selected product and its actual pole count repeat together. -/
theorem sLocalPrimaryEulerProduct_periodic (ω : PontryaginDual (K F S))
    {p : ℕ} (hp : p.Prime) {W : Finset S} (hW : W ⊆ sLocalPrimaryPlaces F S p)
    (z : ℂ) (m : ℤ) :
    let u := z + ((m : ℝ) * sLocalPrimaryEulerPeriod p : ℝ) * Complex.I
    sLocalSelectedEulerMultiplier F S ω W u = sLocalSelectedEulerMultiplier F S ω W z ∧
      sLocalSelectedFinitePoleCount F S ω W u = sLocalSelectedFinitePoleCount F S ω W z := by
  refine ⟨Finset.prod_congr rfl (fun v hv ↦ ?_), ?_⟩
  · exact sLocalPrimaryEulerMultiplier_periodic F S ω hp (hW hv) z m
  · unfold sLocalSelectedFinitePoleCount
    congr 1
    ext v
    by_cases hv : v ∈ W
    · simp only [Finset.mem_filter, hv, true_and]
      rw [sLocalPrimaryEulerMultiplier_periodic F S ω hp (hW hv) z m]
    · simp [hv]

private abbrev localPeriod (v : S) := 2 * Real.pi / Real.log (v.val.asIdeal.absNorm : ℝ)

private theorem localPeriod_pos (v : S) : 0 < localPeriod F S v :=
  div_pos (mul_pos (by norm_num) Real.pi_pos)
    (Real.log_pos (by exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v.val))

private theorem selectedFinitePole_lattice
    (ω : PontryaginDual (K F S)) {W : Finset S} {z : ℂ}
    (hz : 0 < sLocalSelectedFinitePoleCount F S ω W z) :
    ∃ v ∈ W, ∃ n : ℤ,
      z = (((n : ℝ) * localPeriod F S v - finitePolePhase F S ω v : ℝ) : ℂ) * Complex.I := by
  have h' : 0 < (W.filter fun v ↦ finiteZetaWeilMultiplier F v.val
      (sLocalFiniteZetaPhases F S ω v) z = 0).card := hz
  obtain ⟨v, hv⟩ := Finset.card_pos.mp h'
  obtain ⟨hvW, hv⟩ := Finset.mem_filter.mp hv
  let χ := sLocalFiniteZetaPhases F S ω v
  by_cases hu : finiteZetaUnramified F v.val χ
  · change finiteZetaWeilMultiplier F v.val χ z = 0 at hv
    rw [finiteZetaWeilMultiplier, ite_eq_left hu] at hv
    change finiteZetaDenominator F v.val χ z = 0 at hv
    obtain ⟨n, hn⟩ := (finiteZetaDenominator_eq_zero_iff_lattice F v.val χ _
      (finitePolePhase_spec F S ω v).2.1 z).mp hv
    refine ⟨v, hvW, n, ?_⟩
    change z = ((n : ℂ) * (2 * (Real.pi : ℂ) /
      (Real.log (v.val.asIdeal.absNorm : ℝ) : ℂ)) - (finitePolePhase F S ω v : ℂ)) * Complex.I at hn
    simpa only [localPeriod, Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_intCast,
      Complex.ofReal_div, Complex.ofReal_ofNat] using hn
  · change finiteZetaWeilMultiplier F v.val χ z = 0 at hv
    simp [finiteZetaWeilMultiplier, hu] at hv

/-- The distinct centers in one half-open common period. The initial
finite enumeration records all residue degrees and all places in the selection. -/
def sLocalPrimaryEulerCell (ω : PontryaginDual (K F S)) (p : ℕ) (W : Finset S) : Finset ℝ :=
  ((W.biUnion fun v ↦ (Finset.Icc (0 : ℤ) (inertia F S p v : ℤ)).image fun n : ℤ ↦
      (n : ℝ) * localPeriod F S v - finitePolePhase F S ω v).filter fun x ↦
    x ∈ Ico 0 (sLocalPrimaryEulerPeriod p) ∧
      0 < sLocalSelectedFinitePoleCount F S ω W ((x : ℂ) * Complex.I))

theorem mem_sLocalPrimaryEulerCell_iff (ω : PontryaginDual (K F S))
    {p : ℕ} (hp : p.Prime) {W : Finset S} (hW : W ⊆ sLocalPrimaryPlaces F S p)
    (x : ℝ) :
    x ∈ sLocalPrimaryEulerCell F S ω p W ↔ x ∈ Ico 0 (sLocalPrimaryEulerPeriod p) ∧
      0 < sLocalSelectedFinitePoleCount F S ω W ((x : ℂ) * Complex.I) := by
  rw [sLocalPrimaryEulerCell, Finset.mem_filter]
  refine ⟨fun h ↦ h.2, fun h ↦ ⟨?_, h⟩⟩
  obtain ⟨v, hv, n, hn⟩ := selectedFinitePole_lattice F S ω h.2
  have hx : x = (n : ℝ) * localPeriod F S v - finitePolePhase F S ω v := by
    have he := congrArg Complex.im hn
    simpa only [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      mul_one, mul_zero, add_zero] using he
  let d := localPeriod F S v
  let t := finitePolePhase F S ω v
  let f := inertia F S p v
  have hd : 0 < d := localPeriod_pos F S v
  have ht : 0 ≤ t ∧ t < d := (finitePolePhase_spec F S ω v).1
  have hτ : sLocalPrimaryEulerPeriod p = (f : ℝ) * d := primary_period_eq_local_mul F S hp (hW hv)
  change x = (n : ℝ) * d - t at hx
  have hn₀ : (0 : ℝ) ≤ n := by
    by_contra! hneg
    have hh := mul_neg_of_neg_of_pos hneg hd
    linarith [h.1.1, ht.1]
  have hn₁ : n ≤ (f : ℤ) := by
    by_contra! hlt
    have hh : ((f : ℝ) + 1) ≤ (n : ℝ) := by exact_mod_cast (show (f : ℤ) + 1 ≤ n by omega)
    have hb := mul_le_mul_of_nonneg_right hh hd.le
    have hx' := h.1.2
    rw [hτ] at hx'
    linarith [ht.2, mul_add d (f : ℝ) 1, add_mul (f : ℝ) 1 d]
  exact Finset.mem_biUnion.mpr ⟨v, hv, Finset.mem_image.mpr
    ⟨n, Finset.mem_Icc.mpr ⟨by exact_mod_cast hn₀, hn₁⟩, hx.symm⟩⟩

/-- An actual selected pole is a translate of a center in the common
cell, with exactly the pole count of that center. -/
theorem sLocalPrimaryEulerCell_represents (ω : PontryaginDual (K F S))
    {p : ℕ} (hp : p.Prime) {W : Finset S} (hW : W ⊆ sLocalPrimaryPlaces F S p)
    {z : ℂ} (hz : 0 < sLocalSelectedFinitePoleCount F S ω W z) :
    ∃ x ∈ sLocalPrimaryEulerCell F S ω p W, ∃ m : ℤ,
      z = (((x + (m : ℝ) * sLocalPrimaryEulerPeriod p : ℝ) : ℂ) * Complex.I) ∧
      sLocalSelectedFinitePoleCount F S ω W z =
        sLocalSelectedFinitePoleCount F S ω W ((x : ℂ) * Complex.I) := by
  obtain ⟨v, _, n, hn⟩ := selectedFinitePole_lattice F S ω hz
  have hre : z.re = 0 := by
    rw [hn]
    simp only [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im, mul_zero, zero_mul, sub_zero]
  let d := sLocalPrimaryEulerPeriod p
  obtain ⟨m, hm⟩ := exists_integerTranslate_mem_Ico 0 (sLocalPrimaryEulerPeriod_pos hp) z.im
  let x := z.im + (m : ℝ) * d
  have hx : x ∈ Ico 0 d := by simpa [x, mul_comm] using hm
  have hzx : z + ((m : ℝ) * d : ℝ) * Complex.I = (x : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [x, hre]
  have ht := (sLocalPrimaryEulerProduct_periodic F S ω hp hW z m).2
  change sLocalSelectedFinitePoleCount F S ω W (z + ((m : ℝ) * d : ℝ) * Complex.I) =
    sLocalSelectedFinitePoleCount F S ω W z at ht
  rw [hzx] at ht
  refine ⟨x, (mem_sLocalPrimaryEulerCell_iff F S ω hp hW x).mpr ⟨hx, ht.symm ▸ hz⟩, -m, ?_, ht.symm⟩
  apply Complex.ext
  · simp [hre]
  · simp [x, d]


/-- The half-open cell and integer shift uniquely label each primary center. -/
theorem sLocalPrimaryEulerCell_representation_unique (ω : PontryaginDual (K F S))
    {p : ℕ} (hp : p.Prime) {W : Finset S} {x y : ℝ}
    (hx : x ∈ sLocalPrimaryEulerCell F S ω p W) (hy : y ∈ sLocalPrimaryEulerCell F S ω p W)
    (m n : ℤ)
    (he : x + (m : ℝ) * sLocalPrimaryEulerPeriod p =
      y + (n : ℝ) * sLocalPrimaryEulerPeriod p) : x = y ∧ m = n := by
  let d := sLocalPrimaryEulerPeriod p
  have hd : 0 < d := sLocalPrimaryEulerPeriod_pos hp
  have hx' : x ∈ Ico 0 d := (Finset.mem_filter.mp hx).2.1
  have hy' : y ∈ Ico 0 d := (Finset.mem_filter.mp hy).2.1
  have hl (a b : ℝ) (ha : a < d) (hb : 0 ≤ b) (j k : ℤ) (h : j < k) :
      a + (j : ℝ) * d < b + (k : ℝ) * d := by
    have hj : (j : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast (show j + 1 ≤ k by omega)
    have hmul := mul_le_mul_of_nonneg_right hj hd.le
    rw [add_mul, one_mul] at hmul
    linarith
  have hmn : m = n := by
    rcases lt_trichotomy m n with h | h | h
    · exact (ne_of_lt (hl x y hx'.2 hy'.1 m n h) he).elim
    · exact h
    · exact (ne_of_lt (hl y x hy'.2 hx'.1 n m h) he.symm).elim
  exact ⟨add_right_cancel (hmn ▸ he), hmn⟩

/-- The finite Euler divisor is entire and its analytic order is the
selected multiplicity at every center, including center collisions. -/
theorem sLocalSelectedEulerMultiplier_analytic_order (ω : PontryaginDual (K F S))
    (W : Finset S) (c : ℂ) :
    AnalyticAt ℂ (sLocalSelectedEulerMultiplier F S ω W) c ∧
      analyticOrderAt (sLocalSelectedEulerMultiplier F S ω W) c =
        sLocalSelectedFinitePoleCount F S ω W c := by
  have ha : AnalyticAt ℂ (sLocalSelectedEulerMultiplier F S ω W) c := by
    apply Finset.analyticAt_fun_prod
    intro v hv
    let χ := sLocalFiniteZetaPhases F S ω v
    by_cases hχ : finiteZetaUnramified F v.val χ
    · have he : finiteZetaWeilMultiplier F v.val χ = finiteZetaDenominator F v.val χ :=
        funext fun _ ↦ ite_eq_left hχ
      exact he ▸ finiteZetaDenominator_analytic F v.val χ c
    · have he : finiteZetaWeilMultiplier F v.val χ = fun _ ↦ (1 : ℂ) :=
        funext fun _ ↦ ite_eq_right hχ
      rw [show finiteZetaWeilMultiplier F v.val (sLocalFiniteZetaPhases F S ω v) = _ from he]
      exact analyticAt_const
  refine ⟨ha, ?_⟩
  letI (v : S) : MeasurableSpace (v.val.adicCompletion F)ˣ := borel _
  have h := sLocalSelectedEulerMultiplier_order F S ω W c
  rw [ha.meromorphicOrderAt_eq] at h
  cases hOrd : analyticOrderAt (sLocalSelectedEulerMultiplier F S ω W) c with
  | top => simp [hOrd] at h
  | coe n =>
    rw [hOrd, ENat.map_natCast] at h
    have he : n = sLocalSelectedFinitePoleCount F S ω W c := by
      change ((n : ℤ) : WithTop ℤ) =
        ((sLocalSelectedFinitePoleCount F S ω W c : ℤ) : WithTop ℤ) at h
      exact_mod_cast h
    simp [he]

/-- Finite Euler polynomials are bounded on every closed vertical strip. -/
theorem sLocalSelectedEulerMultiplier_stripBound (ω : PontryaginDual (K F S)) (W : Finset S)
    (a b : ℝ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, z.re ∈ Icc a b →
      ‖sLocalSelectedEulerMultiplier F S ω W z‖ ≤ C := by
  let L (v : S) := Real.log (v.val.asIdeal.absNorm : ℝ)
  let B (v : S) := 1 + Real.exp (-a * L v)
  have hB (v : S) : 0 ≤ B v := by dsimp [B]; positivity
  refine ⟨∏ v ∈ W, B v, Finset.prod_nonneg (fun v _ ↦ hB v), fun z hz ↦ ?_⟩
  rw [sLocalSelectedEulerMultiplier, norm_prod]
  apply Finset.prod_le_prod (fun _ _ ↦ norm_nonneg _)
  intro v hv
  let χ := sLocalFiniteZetaPhases F S ω v
  have hL : 0 ≤ L v :=
    (Real.log_pos (by exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v.val)).le
  change ‖finiteZetaWeilMultiplier F v.val χ z‖ ≤ B v
  by_cases hχ : finiteZetaUnramified F v.val χ
  · rw [finiteZetaWeilMultiplier, ite_eq_left hχ]
    calc
      _ ≤ ‖(1 : ℂ)‖ + ‖finiteZetaRatio F v.val χ z‖ := norm_sub_le _ _
      _ ≤ B v := by
        simp only [finiteZetaRatio, norm_one, norm_mul, Circle.norm_coe, one_mul,
          Complex.norm_exp, Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im,
          mul_zero, sub_zero, B]
        exact add_le_add_right (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
          (neg_le_neg hz.1) hL)) _
  · rw [finiteZetaWeilMultiplier, ite_eq_right hχ, norm_one]
    exact le_add_of_nonneg_right (Real.exp_pos _).le


end

end Masullo
