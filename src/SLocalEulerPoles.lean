import SLocalMellinDivisor
import ModulatedCharacters
import PrimeIdealCoefficients
import Mathlib.Data.Finset.Powerset
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
import Mathlib.NumberTheory.Padics.PadicVal.Basic

open Filter Function IsDedekindDomain NumberField Set Topology
open scoped Classical NumberField

namespace Masullo

noncomputable section

/-- The real reciprocal Gamma factor vanishes at the nonpositive integers
with the parity of the real character. -/
theorem realArchZetaDenominator_eq_zero_iff (a : ℕ) (z : ℂ) :
    realArchZetaDenominator a z = 0 ↔
      ∃ n : ℕ, z = -(a % 2 : ℕ) - 2 * (n : ℂ) := by
  rw [realArchZetaDenominator, inv_eq_zero, Complex.Gammaℝ_eq_zero_iff]
  apply exists_congr
  intro n
  constructor <;> intro h <;> linear_combination h

/-- A real sign character already contributes an odd negative Gamma pole. -/
theorem realArchZetaDenominator_odd_at_neg_one : realArchZetaDenominator 1 (-1) = 0 :=
  (realArchZetaDenominator_eq_zero_iff 1 (-1)).mpr ⟨0, by norm_num⟩

/-- The angular mode shifts the complex reciprocal Gamma zeros to the left. -/
theorem complexArchZetaDenominator_eq_zero_iff (k : ℤ) (z : ℂ) :
    complexArchZetaDenominator k z = 0 ↔
      ∃ n : ℕ, z = -(k.natAbs : ℂ) / 2 - (n : ℂ) := by
  have hπ : (2 * (Real.pi : ℂ)) ≠ 0 := by
    exact mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hp : (2 * (2 * (Real.pi : ℂ)) ^ (-(z + (k.natAbs : ℂ) / 2))) ≠ 0 :=
    mul_ne_zero two_ne_zero (by rw [Complex.cpow_def_of_ne_zero hπ]; exact Complex.exp_ne_zero _)
  rw [complexArchZetaDenominator, inv_eq_zero, Complex.Gammaℂ_def,
    mul_eq_zero, or_iff_right hp, Complex.Gamma_eq_zero_iff]
  apply exists_congr
  intro n
  constructor <;> intro h <;> linear_combination h

private def reciprocalGamma (s : ℂ) : ℂ := (Complex.Gamma s)⁻¹

private theorem reciprocalGamma_analytic (s : ℂ) : AnalyticAt ℂ reciprocalGamma s := by
  have h : Differentiable ℂ reciprocalGamma := by
    unfold reciprocalGamma
    exact Complex.differentiable_one_div_Gamma
  exact h.analyticAt s

private theorem reciprocalGamma_simple_neg_nat (n : ℕ) :
    analyticOrderAt reciprocalGamma (-(n : ℂ)) = 1 := by
  have hrec : reciprocalGamma = id * (reciprocalGamma ∘ (fun s : ℂ => s + 1)) := by
    funext s
    change (Complex.Gamma s)⁻¹ = s * (Complex.Gamma (s + 1))⁻¹
    by_cases hs : s = 0
    · simp [hs, Complex.Gamma_zero]
    · rw [Complex.Gamma_add_one s hs, mul_inv, ← mul_assoc, mul_inv_cancel₀ hs, one_mul]
  have hstep (s : ℂ) : analyticOrderAt reciprocalGamma s =
      analyticOrderAt (id : ℂ → ℂ) s + analyticOrderAt reciprocalGamma (s + 1) := by
    have ha : AnalyticAt ℂ (fun z : ℂ => z + 1) s := analyticAt_id.add analyticAt_const
    have hda : deriv (fun z : ℂ => z + 1) s ≠ 0 := by
      have hd : HasDerivAt (fun z : ℂ => z + 1) 1 s := (hasDerivAt_id s).add_const 1
      rw [hd.deriv]
      exact one_ne_zero
    calc
      _ = analyticOrderAt (id * (reciprocalGamma ∘ (fun z : ℂ => z + 1))) s :=
        congrArg (fun f : ℂ → ℂ => analyticOrderAt f s) hrec
      _ = _ := by
        have hc : AnalyticAt ℂ (reciprocalGamma ∘ (fun z : ℂ => z + 1)) s :=
          (reciprocalGamma_analytic (s + 1)).comp (f := fun z : ℂ => z + 1) (x := s) ha
        rw [analyticOrderAt_mul analyticAt_id hc,
          analyticOrderAt_comp_of_deriv_ne_zero ha hda]
  induction n with
  | zero =>
    rw [Nat.cast_zero, neg_zero, hstep, analyticOrderAt_id, zero_add]
    rw [(reciprocalGamma_analytic 1).analyticOrderAt_eq_zero.mpr (by simp [reciprocalGamma]), add_zero]
  | succ n ih =>
    rw [Nat.cast_succ, hstep, show -((n : ℂ) + 1) + 1 = -(n : ℂ) by ring, ih,
      (analyticAt_id (𝕜 := ℂ)).analyticOrderAt_eq_zero.mpr (neg_ne_zero.mpr (by exact_mod_cast n.succ_ne_zero)),
      zero_add]

private theorem analyticOrderAt_gammaProduct_inv_of_zero
    {p g : ℂ → ℂ} {s : ℂ} (hp : AnalyticAt ℂ p s) (hp₀ : p s ≠ 0)
    (hg : AnalyticAt ℂ g s) (hg' : deriv g s ≠ 0)
    (hz : (p s * Complex.Gamma (g s))⁻¹ = 0) :
    analyticOrderAt (fun z => (p z * Complex.Gamma (g z))⁻¹) s = 1 := by
  rw [inv_eq_zero, mul_eq_zero, or_iff_right hp₀, Complex.Gamma_eq_zero_iff] at hz
  obtain ⟨n, hn⟩ := hz
  simp_rw [mul_inv]
  change analyticOrderAt (p⁻¹ * (reciprocalGamma ∘ g)) s = _
  rw [analyticOrderAt_mul (hp.inv hp₀) ((reciprocalGamma_analytic (g s)).comp hg),
    (hp.inv hp₀).analyticOrderAt_eq_zero.mpr (inv_ne_zero hp₀), zero_add,
    analyticOrderAt_comp_of_deriv_ne_zero hg hg', hn, reciprocalGamma_simple_neg_nat]

/-- Each zero of the real reciprocal local Gamma factor is simple. -/
theorem realArchZetaDenominator_simple_zero (a : ℕ) (s : ℂ)
    (hz : realArchZetaDenominator a s = 0) :
    analyticOrderAt (realArchZetaDenominator a) s = 1 := by
  let g (z : ℂ) := (z + ((a % 2 : ℕ) : ℂ)) / 2
  have hg : AnalyticAt ℂ g s := (analyticAt_id.add analyticAt_const).div_const
  have hg' : deriv g s ≠ 0 := by
    have hd : HasDerivAt g (1 / (2 : ℂ)) s :=
      ((hasDerivAt_id s).add_const ((a % 2 : ℕ) : ℂ)).div_const 2
    rw [hd.deriv]
    norm_num
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  let p (z : ℂ) := (Real.pi : ℂ) ^ (-g z)
  have hp : AnalyticAt ℂ p s := by
    have h : p = fun z => Complex.exp (Complex.log (Real.pi : ℂ) * (-g z)) :=
      funext fun z => Complex.cpow_def_of_ne_zero hpi _
    rw [h]
    exact (analyticAt_const.mul hg.neg).cexp
  have hp₀ : p s ≠ 0 := by
    dsimp [p]
    rw [Complex.cpow_def_of_ne_zero hpi]
    exact Complex.exp_ne_zero _
  have heq : realArchZetaDenominator a = fun z => (p z * Complex.Gamma (g z))⁻¹ := by
    funext z
    simp only [realArchZetaDenominator, Complex.Gammaℝ_def, p, g, neg_div]
  rw [heq] at hz ⊢
  exact analyticOrderAt_gammaProduct_inv_of_zero hp hp₀ hg hg' hz

/-- Each zero of the complex reciprocal local Gamma factor is simple. -/
theorem complexArchZetaDenominator_simple_zero (k : ℤ) (s : ℂ)
    (hz : complexArchZetaDenominator k s = 0) :
    analyticOrderAt (complexArchZetaDenominator k) s = 1 := by
  let g (z : ℂ) := z + (k.natAbs : ℂ) / 2
  have hg : AnalyticAt ℂ g s := analyticAt_id.add analyticAt_const
  have hg' : deriv g s ≠ 0 := by
    have hd : HasDerivAt g 1 s := (hasDerivAt_id s).add_const ((k.natAbs : ℂ) / 2)
    rw [hd.deriv]
    exact one_ne_zero
  have hpi : (2 * (Real.pi : ℂ)) ≠ 0 :=
    mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  let p (z : ℂ) := 2 * (2 * (Real.pi : ℂ)) ^ (-g z)
  have hp : AnalyticAt ℂ p s := by
    have h : p = fun z => 2 * Complex.exp (Complex.log (2 * (Real.pi : ℂ)) * (-g z)) := by
      funext z
      change 2 * (2 * (Real.pi : ℂ)) ^ (-g z) = _
      rw [Complex.cpow_def_of_ne_zero hpi]
    rw [h]
    exact analyticAt_const.mul (analyticAt_const.mul hg.neg).cexp
  have hp₀ : p s ≠ 0 := by
    dsimp [p]
    rw [Complex.cpow_def_of_ne_zero hpi]
    exact mul_ne_zero two_ne_zero (Complex.exp_ne_zero _)
  rw [show complexArchZetaDenominator k = fun z => (p z * Complex.Gamma (g z))⁻¹ from rfl] at hz ⊢
  exact analyticOrderAt_gammaProduct_inv_of_zero hp hp₀ hg hg' hz

variable (F : Type*) [Field F] [NumberField F]

private abbrev Place := HeightOneSpectrum (𝓞 F)
private abbrev logQ (v : Place F) : ℝ := Real.log (v.asIdeal.absNorm : ℝ)

private theorem logQ_pos (v : Place F) : 0 < logQ F v :=
  Real.log_pos (by exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v)

/-- The finite Euler poles form one vertical arithmetic progression.
The sign of the phase uses the normalized uniformizer absolute value. -/
theorem finiteZetaDenominator_eq_zero_iff_lattice (v : Place F)
    (χ : (v.adicCompletion F)ˣ →ₜ* Circle) (t : ℝ)
    (ht : Circle.exp (t * logQ F v) = (χ (chosenFiniteUniformizer F v))⁻¹) (z : ℂ) :
    finiteZetaDenominator F v χ z = 0 ↔
      ∃ m : ℤ, z = ((m : ℂ) * (2 * Real.pi / logQ F v) - t) * Complex.I := by
  let L := logQ F v
  let a := χ (chosenFiniteUniformizer F v)
  have ha : (a : ℂ) ≠ 0 := Circle.coe_ne_zero a
  have hL : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (logQ_pos F v).ne'
  have he : Complex.exp (((t * L : ℝ) : ℂ) * Complex.I) = (a : ℂ)⁻¹ := by
    simpa only [Circle.coe_exp, Circle.coe_inv] using congrArg (fun x : Circle => (x : ℂ)) ht
  have hiff : finiteZetaDenominator F v χ z = 0 ↔
      Complex.exp (-z * (L : ℂ)) = Complex.exp (((t * L : ℝ) : ℂ) * Complex.I) := by
    rw [he]
    change 1 - (a : ℂ) * Complex.exp (-z * (L : ℂ)) = 0 ↔ _
    rw [sub_eq_zero, eq_comm]
    constructor
    · intro h
      apply mul_left_cancel₀ ha
      simpa only [mul_inv_cancel₀ ha] using h
    · intro h
      rw [h, mul_inv_cancel₀ ha]
  change finiteZetaDenominator F v χ z = 0 ↔
    ∃ m : ℤ, z = ((m : ℂ) * (2 * Real.pi / (L : ℂ)) - t) * Complex.I
  have hmul (m : ℤ) :
      (((m : ℂ) * (2 * Real.pi / (L : ℂ)) - t) * Complex.I) * L =
        (m : ℂ) * (2 * Real.pi * Complex.I) - (t : ℂ) * L * Complex.I := by
    field_simp [hL]
  rw [hiff, Complex.exp_eq_exp_iff_exists_int]
  simp only [Complex.ofReal_mul]
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨-m, mul_right_cancel₀ hL ?_⟩
    rw [hmul, Int.cast_neg]
    linear_combination -hm
  · rintro ⟨m, hm⟩
    refine ⟨-m, ?_⟩
    rw [neg_mul, hm, hmul, Int.cast_neg]
    ring

/-- For an unramified character the normalized phase gives the modulus
power on the multiplicative group of the local field. -/
theorem finiteZetaUnramified_eq_normTwist (v : Place F)
    (χ : (v.adicCompletion F)ˣ →ₜ* Circle) (hχ : finiteZetaUnramified F v χ)
    (t : ℝ) (ht : Circle.exp (t * logQ F v) = (χ (chosenFiniteUniformizer F v))⁻¹)
    (u : (v.adicCompletion F)ˣ) :
    (χ u : ℂ) = finiteZetaWeight F v ((t : ℂ) * Complex.I) u := by
  have hu : u ∈ ⋃ n : ℤ, finiteZetaShell F v n := by rw [finiteZetaShell_iUnion]; exact mem_univ u
  obtain ⟨n, hn⟩ := mem_iUnion.mp hu
  let π := chosenFiniteUniformizer F v
  let a := π ^ (-n) * u
  have hdecomp : π ^ n * a = u := by
    dsimp [a]
    rw [← mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, one_mul]
  have ha : a ∈ finitePlaceIntegralUnits F v := by
    rw [← finiteZetaShell_preimage F v π (chosenFiniteUniformizer_spec F v) n]
    change π ^ n * a ∈ finiteZetaShell F v n
    rwa [hdecomp]
  have hπ : (χ π : ℂ) = Complex.exp (-(t : ℂ) * (logQ F v : ℂ) * Complex.I) := by
    have he := congrArg (fun x : Circle => (x : ℂ)⁻¹) ht
    rw [Circle.coe_exp, Circle.coe_inv, inv_inv, ← Complex.exp_neg] at he
    simpa only [Complex.ofReal_mul, neg_mul, ← mul_assoc] using he.symm
  conv_lhs => rw [← hdecomp, map_mul, hχ a ha, mul_one, map_zpow, Circle.coe_zpow, hπ,
    ← Complex.exp_int_mul]
  change ‖u.val‖ = (v.asIdeal.absNorm : ℝ) ^ (-n) at hn
  rw [finiteZetaWeight, hn, Real.log_zpow]
  simp only [Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_intCast, Int.cast_neg]
  congr 1
  ring

/-- Positive powers of distinct primes have logarithms with no nonzero
integer linear relation between them. -/
private theorem primePower_log_cross_eq_zero {p q e f : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (he : 0 < e) (hf : 0 < f) {m n : ℤ}
    (h : (m : ℝ) * Real.log ((p ^ e : ℕ) : ℝ) = (n : ℝ) * Real.log ((q ^ f : ℕ) : ℝ)) :
    m = 0 ∧ n = 0 := by
  have hp₁ : 1 < ((p ^ e : ℕ) : ℝ) := by
    exact_mod_cast (one_lt_pow₀ hp.one_lt he.ne' : 1 < p ^ e)
  have hq₁ : 1 < ((q ^ f : ℕ) : ℝ) := by
    exact_mod_cast (one_lt_pow₀ hq.one_lt hf.ne' : 1 < q ^ f)
  have ha := congrArg abs h
  have hmabs : |(m : ℝ)| = (m.natAbs : ℝ) := by rw [Nat.cast_natAbs, Int.cast_abs]
  have hnabs : |(n : ℝ)| = (n.natAbs : ℝ) := by rw [Nat.cast_natAbs, Int.cast_abs]
  rw [abs_mul, abs_mul, abs_of_pos (Real.log_pos hp₁), abs_of_pos (Real.log_pos hq₁),
    hmabs, hnabs] at ha
  have hpow := congrArg Real.exp ha
  rw [Real.exp_nat_mul, Real.exp_nat_mul,
    Real.exp_log (zero_lt_one.trans hp₁), Real.exp_log (zero_lt_one.trans hq₁)] at hpow
  have hnPow : (p ^ e) ^ m.natAbs = (q ^ f) ^ n.natAbs := by exact_mod_cast hpow
  rw [← pow_mul, ← pow_mul] at hnPow
  have hm : m = 0 := by
    by_contra hm
    have hpos : e * m.natAbs ≠ 0 := mul_ne_zero he.ne' (by simpa using hm)
    exact hpq (Nat.prime_eq_prime_of_dvd_pow hp hq (hnPow ▸ dvd_pow_self p hpos))
  have hn : n = 0 := by
    rw [hm, Int.cast_zero, zero_mul, eq_comm, mul_eq_zero] at h
    exact_mod_cast h.resolve_right (Real.log_pos hq₁).ne'
  exact ⟨hm, hn⟩

/-- Schanuel's conjecture in its finite-generator formulation. A rationally
linearly independent n-tuple and its exponentials together contain an
algebraically independent n-tuple. -/
def SchanuelConjecture : Prop :=
  ∀ (n : ℕ) (z : Fin n → ℂ), LinearIndependent ℚ z →
    ∃ w : Fin n → ℂ, AlgebraicIndependent ℚ w ∧
      ∀ i, w i ∈ range z ∪ range (Complex.exp ∘ z)

private theorem schanuel_algebraic_exponentials (hS : SchanuelConjecture)
    {n : ℕ} {z : Fin n → ℂ} (hz : LinearIndependent ℚ z)
    (hexp : ∀ i, IsAlgebraic ℚ (Complex.exp (z i))) :
    AlgebraicIndependent ℚ z := by
  obtain ⟨w, hw, hi⟩ := hS n z hz
  have h (i : Fin n) : ∃ j, z j = w i := by
    rcases hi i with h | ⟨j, hj⟩
    · exact h
    · exact (hw.transcendental i (hj ▸ hexp j)).elim
  choose j hj using h
  have hinj : Injective j := fun i k he ↦ hw.injective (by rw [← hj i, ← hj k, he])
  let e := Equiv.ofBijective j ⟨hinj, Finite.surjective_of_injective hinj⟩
  have he : w ∘ e.symm = z := by
    funext i
    change w (e.symm i) = z i
    rw [← hj (e.symm i)]
    exact congrArg z (e.apply_symm_apply i)
  rw [← he]
  exact hw.comp e.symm e.symm.injective

private theorem primePower_logs_rat_relation {p q e f : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (he : 0 < e) (hf : 0 < f)
    {a b : ℚ} (h : (a : ℝ) * Real.log ((p ^ e : ℕ) : ℝ) +
      (b : ℝ) * Real.log ((q ^ f : ℕ) : ℝ) = 0) : a = 0 ∧ b = 0 := by
  have ha : (a.den : ℝ) ≠ 0 := by exact_mod_cast a.den_ne_zero
  have hb : (b.den : ℝ) ≠ 0 := by exact_mod_cast b.den_ne_zero
  rw [Rat.cast_def, Rat.cast_def] at h
  field_simp [ha, hb] at h
  have h' : ((a.num * (b.den : ℤ) : ℤ) : ℝ) * Real.log ((p ^ e : ℕ) : ℝ) =
      ((-(b.num * (a.den : ℤ)) : ℤ) : ℝ) * Real.log ((q ^ f : ℕ) : ℝ) := by
    simp only [Int.cast_mul, Int.cast_natCast, Int.cast_neg]
    linear_combination h
  rcases primePower_log_cross_eq_zero hp hq hpq he hf h' with ⟨h₁, h₂⟩
  have hA : a.num = 0 := (mul_eq_zero.mp h₁).resolve_right (by exact_mod_cast b.den_ne_zero)
  have hB : b.num = 0 := (mul_eq_zero.mp (neg_eq_zero.mp h₂)).resolve_right
    (by exact_mod_cast a.den_ne_zero)
  exact ⟨Rat.num_eq_zero.mp hA, Rat.num_eq_zero.mp hB⟩

/-- Under Schanuel's conjecture, a nonreal common exponent cannot give
algebraic powers of the sizes of two finite residue fields over distinct primes. -/
theorem primePower_exponents_im_eq_zero_of_schanuel (hS : SchanuelConjecture)
    {p q e f : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (he : 0 < e) (hf : 0 < f)
    {s : ℂ} (hP : IsAlgebraic ℚ (((p ^ e : ℕ) : ℂ) ^ s))
    (hQ : IsAlgebraic ℚ (((q ^ f : ℕ) : ℂ) ^ s)) : s.im = 0 := by
  by_contra hs
  let x := Real.log ((p ^ e : ℕ) : ℝ)
  let y := Real.log ((q ^ f : ℕ) : ℝ)
  let z : Fin 4 → ℂ := ![(x : ℂ), (y : ℂ), (x : ℂ) * s, (y : ℂ) * s]
  have hz : LinearIndependent ℚ z := by
    rw [Fintype.linearIndependent_iff]
    intro a ha i
    have hsum : (a 0 : ℂ) * x + ((a 1 : ℂ) * y +
        ((a 2 : ℂ) * ((x : ℂ) * s) + (a 3 : ℂ) * ((y : ℂ) * s))) = 0 := by
      simpa [Fin.sum_univ_succ, z, Rat.smul_def] using ha
    have him := congrArg Complex.im hsum
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re,
      Complex.ratCast_im, Complex.ratCast_re, Complex.zero_im, mul_zero, zero_mul, zero_add,
      add_zero] at him
    have him' : (a 2 : ℝ) * x + (a 3 : ℝ) * y = 0 := by
      apply (mul_eq_zero.mp (_ : ((a 2 : ℝ) * x + (a 3 : ℝ) * y) * s.im = 0)).resolve_right hs
      linear_combination him
    obtain ⟨ha₂, ha₃⟩ := primePower_logs_rat_relation hp hq hpq he hf him'
    norm_num [ha₂, ha₃] at hsum
    have hre := congrArg Complex.re hsum
    simp only [Complex.add_re, Complex.mul_re, Complex.ratCast_re, Complex.ratCast_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.zero_re, zero_mul, sub_zero] at hre
    obtain ⟨ha₀, ha₁⟩ := primePower_logs_rat_relation hp hq hpq he hf hre
    fin_cases i <;> assumption
  have hp₀ : (0 : ℝ) < ((p ^ e : ℕ) : ℝ) := by exact_mod_cast pow_pos hp.pos e
  have hq₀ : (0 : ℝ) < ((q ^ f : ℕ) : ℝ) := by exact_mod_cast pow_pos hq.pos f
  have hExp (n : ℕ) (hn : (0 : ℝ) < (n : ℝ)) :
      Complex.exp ((Real.log (n : ℝ) : ℂ) * s) = (n : ℂ) ^ s := by
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hn.ne' : (n : ℂ) ≠ 0)]
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_log hn.le]
  have ha : ∀ i, IsAlgebraic ℚ (Complex.exp (z i)) := by
    intro i
    fin_cases i
    · change IsAlgebraic ℚ (Complex.exp (x : ℂ))
      rw [← Complex.ofReal_exp, Real.exp_log hp₀, Complex.ofReal_natCast]
      exact isAlgebraic_natCast _
    · change IsAlgebraic ℚ (Complex.exp (y : ℂ))
      rw [← Complex.ofReal_exp, Real.exp_log hq₀, Complex.ofReal_natCast]
      exact isAlgebraic_natCast _
    · exact (hExp _ hp₀).symm ▸ hP
    · exact (hExp _ hq₀).symm ▸ hQ
  let P : MvPolynomial (Fin 4) ℚ :=
    MvPolynomial.X 0 * MvPolynomial.X 3 - MvPolynomial.X 1 * MvPolynomial.X 2
  have hPz : MvPolynomial.aeval z P = 0 := by
    simp [P, z]
    ring
  have hPne : P ≠ 0 := by
    intro h
    have hn := congrArg (MvPolynomial.eval (![1, 0, 0, 1] : Fin 4 → ℚ)) h
    norm_num [P, Matrix.cons_val_succ] at hn
    exact one_ne_zero (show (1 : ℚ) = 0 from hn)
  exact hPne ((schanuel_algebraic_exponentials hS hz ha).eq_zero_of_aeval_eq_zero P hPz)

/-- The classical Six Exponentials Theorem, stated as a proposition so that
applications can be checked separately from its transcendence proof. -/
def SixExponentialsTheorem : Prop :=
  ∀ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ), LinearIndependent ℚ x → LinearIndependent ℚ y →
    ∃ i j, Transcendental ℚ (Complex.exp (x i * y j))

private theorem primePower_logs_linearIndependent {ι : Type*} [Fintype ι]
    (p e : ι → ℕ) (hp : ∀ i, (p i).Prime) (he : ∀ i, 0 < e i) (hpinj : Injective p) :
    LinearIndependent ℚ (fun i ↦ (Real.log ((p i ^ e i : ℕ) : ℝ) : ℂ)) := by
  rw [Fintype.linearIndependent_iff]
  intro a ha i
  let D : ℕ := ∏ j, (a j).den
  let c (j : ι) : ℤ := (a j).num * ((∏ k ∈ Finset.univ.erase j, (a k).den : ℕ) : ℤ)
  have hscale (j : ι) : (c j : ℝ) = (D : ℝ) * (a j : ℝ) := by
    have hd : ((a j).den : ℝ) ≠ 0 := by exact_mod_cast (a j).den_ne_zero
    have hD : D = (a j).den * ∏ k ∈ Finset.univ.erase j, (a k).den :=
      (Finset.mul_prod_erase Finset.univ (fun k ↦ (a k).den) (Finset.mem_univ j)).symm
    simp only [c, hD, Int.cast_mul, Int.cast_natCast, Nat.cast_mul]
    rw [Rat.cast_def]
    field_simp
  have hsum : ∑ j, (a j : ℝ) * Real.log ((p j ^ e j : ℕ) : ℝ) = 0 := by
    simpa only [Complex.re_sum, Rat.smul_def, Complex.mul_re, Complex.ratCast_re,
      Complex.ratCast_im, Complex.ofReal_im, Complex.ofReal_re, Complex.zero_re, mul_zero,
      sub_zero] using congrArg Complex.re ha
  have hsum' : ∑ j, (c j : ℝ) * Real.log ((p j ^ e j : ℕ) : ℝ) = 0 := by
    simp_rw [hscale, mul_assoc]
    rw [← Finset.mul_sum, hsum, mul_zero]
  have hterm (j : ι) :
      Real.exp ((c j : ℝ) * Real.log ((p j ^ e j : ℕ) : ℝ)) =
        (p j : ℝ) ^ (c j * (e j : ℤ)) := by
    have hpos : (0 : ℝ) < (p j : ℝ) := by exact_mod_cast (hp j).pos
    rw [Nat.cast_pow, Real.log_pow,
      show (c j : ℝ) * ((e j : ℝ) * Real.log (p j : ℝ)) =
        ((c j * (e j : ℤ) : ℤ) : ℝ) * Real.log (p j : ℝ) by
          push_cast; ring,
      mul_comm _ (Real.log (p j : ℝ)), Real.exp_mul, Real.exp_log hpos, Real.rpow_intCast]
  let P (j : ι) : ℚ := (p j : ℚ) ^ (c j * (e j : ℤ))
  have hprod : ∏ j, P j = 1 := by
    have hh := congrArg Real.exp hsum'
    rw [Real.exp_sum, Real.exp_zero] at hh
    simp only [hterm] at hh
    apply (Rat.cast_injective (α := ℝ))
    change ((∏ j, (p j : ℚ) ^ (c j * (e j : ℤ)) : ℚ) : ℝ) = ((1 : ℚ) : ℝ)
    push_cast
    exact hh
  letI : Fact (p i).Prime := ⟨hp i⟩
  have hprodval (A : Finset ι) :
      padicValRat (p i) (∏ j ∈ A, P j) = ∑ j ∈ A, padicValRat (p i) (P j) := by
    induction A using Finset.induction_on with
    | empty => simp
    | @insert j A hj ih =>
      have hne (k : ι) : P k ≠ 0 := zpow_ne_zero _ (by exact_mod_cast (hp k).ne_zero)
      rw [Finset.prod_insert hj, Finset.sum_insert hj,
        padicValRat.mul (hne j) (Finset.prod_ne_zero_iff.mpr (fun k _ ↦ hne k)), ih]
  have hvals : ∑ j, padicValRat (p i) (P j) = 0 := by
    rw [← hprodval, hprod, padicValRat.one]
  have hci : c i * (e i : ℤ) = 0 := by
    rw [Finset.sum_eq_single i] at hvals
    · simpa [P, padicValRat.self (hp i).one_lt] using hvals
    · intro j _ hj
      have hd : ¬ p i ∣ p j := fun h ↦ hj (hpinj (((hp j).dvd_iff_eq (hp i).ne_one).mp h))
      simp [P, padicValNat.eq_zero_of_not_dvd hd]
    · simp
  have hc : c i = 0 := (mul_eq_zero.mp hci).resolve_right (by exact_mod_cast (he i).ne')
  have hD : (D : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.prod_ne_zero_iff.mpr (fun j _ ↦ (a j).den_ne_zero) :
      (∏ j, (a j).den) ≠ 0)
  have hz : (D : ℝ) * (a i : ℝ) = 0 := by rw [← hscale, hc, Int.cast_zero]
  exact_mod_cast (mul_eq_zero.mp hz).resolve_left hD

/-- The prime-power specialization of Six Exponentials needed for three
distinct residue characteristics. -/
theorem primePower_exponents_im_eq_zero_of_sixExponentials (hSix : SixExponentialsTheorem)
    (p e : Fin 3 → ℕ) (hp : ∀ i, (p i).Prime) (he : ∀ i, 0 < e i) (hpinj : Injective p)
    {s : ℂ} (halg : ∀ i, IsAlgebraic ℚ (((p i ^ e i : ℕ) : ℂ) ^ s)) : s.im = 0 := by
  by_contra hs
  let x : Fin 2 → ℂ := ![1, s]
  let y : Fin 3 → ℂ := fun i ↦ (Real.log ((p i ^ e i : ℕ) : ℝ) : ℂ)
  have hx : LinearIndependent ℚ x := by
    rw [Fintype.linearIndependent_iff]
    intro a ha i
    have hsum : (a 0 : ℂ) + (a 1 : ℂ) * s = 0 := by
      simpa [Fin.sum_univ_succ, x, Rat.smul_def] using ha
    have him : (a 1 : ℝ) * s.im = 0 := by
      simpa [Complex.add_im, Complex.mul_im] using congrArg Complex.im hsum
    have ha₁ : a 1 = 0 := by exact_mod_cast (mul_eq_zero.mp him).resolve_right hs
    have ha₀ : a 0 = 0 := by exact_mod_cast (by simpa [ha₁] using hsum : (a 0 : ℂ) = 0)
    fin_cases i <;> assumption
  obtain ⟨i, j, hij⟩ := hSix x y hx (primePower_logs_linearIndependent p e hp he hpinj)
  apply hij
  have hj : (0 : ℝ) < ((p j ^ e j : ℕ) : ℝ) := by exact_mod_cast pow_pos (hp j).pos (e j)
  fin_cases i
  · change IsAlgebraic ℚ (Complex.exp (1 * y j))
    rw [one_mul, show y j = ((Real.log ((p j ^ e j : ℕ) : ℝ)) : ℂ) from rfl,
      ← Complex.ofReal_exp, Real.exp_log hj, Complex.ofReal_natCast]
    exact isAlgebraic_natCast _
  · change IsAlgebraic ℚ (Complex.exp (s * y j))
    rw [show Complex.exp (s * y j) = ((p j ^ e j : ℕ) : ℂ) ^ s by
      rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hj.ne'),
        ← Complex.ofReal_natCast, ← Complex.ofReal_log hj.le, mul_comm]]
    exact halg j

/-- Theorem 7.1.3.2(1). Local Euler poles at finite places over distinct
rational primes can coincide at most once, regardless of the two phases. -/
theorem finiteZetaDenominator_common_zeros_subsingleton
    (v w : Place F) (χv : (v.adicCompletion F)ˣ →ₜ* Circle)
    (χw : (w.adicCompletion F)ˣ →ₜ* Circle)
    {p q e f : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (he : 0 < e) (hf : 0 < f) (hv : v.asIdeal.absNorm = p ^ e) (hw : w.asIdeal.absNorm = q ^ f) :
    ({z : ℂ | finiteZetaDenominator F v χv z = 0 ∧ finiteZetaDenominator F w χw z = 0} :
      Set ℂ).Subsingleton := by
  let Ll := logQ F v
  let Lr := logQ F w
  have hl : (Ll : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (logQ_pos F v).ne'
  have hr : (Lr : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (logQ_pos F w).ne'
  obtain ⟨tl, -, htl⟩ := (existsUnique_circle_log_period (logQ_pos F v)
    (χv (chosenFiniteUniformizer F v))⁻¹).exists
  obtain ⟨tr, -, htr⟩ := (existsUnique_circle_log_period (logQ_pos F w)
    (χw (chosenFiniteUniformizer F w))⁻¹).exists
  intro x hx y hy
  obtain ⟨xl, hxl⟩ := (finiteZetaDenominator_eq_zero_iff_lattice F _ _ _ htl x).mp hx.1
  obtain ⟨yl, hyl⟩ := (finiteZetaDenominator_eq_zero_iff_lattice F _ _ _ htl y).mp hy.1
  obtain ⟨xr, hxr⟩ := (finiteZetaDenominator_eq_zero_iff_lattice F _ _ _ htr x).mp hx.2
  obtain ⟨yr, hyr⟩ := (finiteZetaDenominator_eq_zero_iff_lattice F _ _ _ htr y).mp hy.2
  have hdl : x - y = ((xl - yl : ℤ) : ℂ) * (2 * Real.pi / (Ll : ℂ)) * Complex.I := by
    rw [hxl, hyl, Int.cast_sub]
    ring
  have hdr : x - y = ((xr - yr : ℤ) : ℂ) * (2 * Real.pi / (Lr : ℂ)) * Complex.I := by
    rw [hxr, hyr, Int.cast_sub]
    ring
  have hh := mul_right_cancel₀ Complex.I_ne_zero (hdl.symm.trans hdr)
  have hc : ((((xl - yl : ℤ) : ℂ) * (Lr : ℂ))) = (((xr - yr : ℤ) : ℂ) * (Ll : ℂ)) := by
    field_simp [hl, hr] at hh
    linear_combination hh
  have hreal : (↑(xr - yr) : ℝ) * Real.log ((p ^ e : ℕ) : ℝ) =
      (↑(xl - yl) : ℝ) * Real.log ((q ^ f : ℕ) : ℝ) := by
    have h' : (↑(xr - yr) : ℝ) * Ll = (↑(xl - yl) : ℝ) * Lr := by exact_mod_cast hc.symm
    change (↑(xr - yr) : ℝ) * Real.log (v.asIdeal.absNorm : ℝ) =
      (↑(xl - yl) : ℝ) * Real.log (w.asIdeal.absNorm : ℝ) at h'
    rwa [hv, hw] at h'
  have hzero := (primePower_log_cross_eq_zero hp hq hpq he hf hreal).2
  simpa only [hzero, Int.cast_zero, zero_mul, sub_eq_zero] using hdl

private theorem finiteZetaDenominator_trivial_pow_zero (v : Place F)
    (χ : (v.adicCompletion F)ˣ →ₜ* Circle) (N : ℕ)
    (hχ : χ (chosenFiniteUniformizer F v) ^ N = 1) {z : ℂ}
    (hz : finiteZetaDenominator F v χ z = 0) :
    finiteZetaDenominator F v 1 ((N : ℂ) * z) = 0 := by
  have hunit : ((χ (chosenFiniteUniformizer F v) : Circle) : ℂ) ^ N = 1 := by
    simpa only [Circle.coe_pow, Circle.coe_one] using congrArg (fun a : Circle => (a : ℂ)) hχ
  have he := congrArg (fun a : ℂ => a ^ N) (sub_eq_zero.mp hz).symm
  unfold finiteZetaRatio at he
  rw [mul_pow, hunit, one_mul, one_pow, ← Complex.exp_nat_mul] at he
  have harg : -((N : ℂ) * z) * (logQ F v : ℂ) = (N : ℂ) * (-z * (logQ F v : ℂ)) := by
    ring
  simp only [finiteZetaDenominator, finiteZetaRatio, harg, he]
  simp

/-- For finite-order local phases, common poles over distinct rational
primes occur only at zero in the unshifted unitary chart. -/
theorem finiteZetaDenominator_common_zero_of_finite_order
    (v w : Place F) (χv : (v.adicCompletion F)ˣ →ₜ* Circle)
    (χw : (w.adicCompletion F)ˣ →ₜ* Circle)
    {p q e f N : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (he : 0 < e) (hf : 0 < f) (hv : v.asIdeal.absNorm = p ^ e) (hw : w.asIdeal.absNorm = q ^ f)
    (hN : 0 < N) (hχv : χv (chosenFiniteUniformizer F v) ^ N = 1)
    (hχw : χw (chosenFiniteUniformizer F w) ^ N = 1) {z : ℂ}
    (hzv : finiteZetaDenominator F v χv z = 0) (hzw : finiteZetaDenominator F w χw z = 0) :
    z = 0 := by
  have h := finiteZetaDenominator_common_zeros_subsingleton F v w 1 1 hp hq hpq he hf hv hw
  have hz : (N : ℂ) * z = 0 := h
    ⟨finiteZetaDenominator_trivial_pow_zero F v χv N hχv hzv,
      finiteZetaDenominator_trivial_pow_zero F w χw N hχw hzw⟩
    ⟨by simp [finiteZetaDenominator, finiteZetaRatio], by simp [finiteZetaDenominator, finiteZetaRatio]⟩
  exact (mul_eq_zero.mp hz).resolve_left (by exact_mod_cast hN.ne')

variable (S : Finset (Place F))

private abbrev Characters := PontryaginDual (SLocalThetaNormOne F S)
private abbrev RealPlaces := {v : InfinitePlace F // v.IsReal}
private abbrev ComplexPlaces := {v : InfinitePlace F // v.IsComplex}

def finitePolePhase (ω : Characters F S) (v : S) : ℝ :=
  (existsUnique_circle_log_period (logQ_pos F v.val)
    (sLocalFiniteZetaPhases F S ω v (chosenFiniteUniformizer F v.val))⁻¹).exists.choose

/-- The finite character shift is uniquely normalized to its half-open period. -/
theorem finitePolePhase_spec (ω : Characters F S) (v : S) :
    let t := finitePolePhase F S ω v
    t ∈ Ico 0 (2 * Real.pi / logQ F v.val) ∧
      Circle.exp (t * logQ F v.val) =
        (sLocalFiniteZetaPhases F S ω v (chosenFiniteUniformizer F v.val))⁻¹ ∧
      ∀ u ∈ Ico 0 (2 * Real.pi / logQ F v.val),
        Circle.exp (u * logQ F v.val) =
          (sLocalFiniteZetaPhases F S ω v (chosenFiniteUniformizer F v.val))⁻¹ → u = t := by
  let P (u : ℝ) := u ∈ Ico 0 (2 * Real.pi / logQ F v.val) ∧
    Circle.exp (u * logQ F v.val) =
      (sLocalFiniteZetaPhases F S ω v (chosenFiniteUniformizer F v.val))⁻¹
  have h : ∃! u, P u := existsUnique_circle_log_period (logQ_pos F v.val) _
  exact ⟨h.exists.choose_spec.1, h.exists.choose_spec.2,
    fun u hu hexp => h.unique ⟨hu, hexp⟩ h.exists.choose_spec⟩


/-- At an unramified finite place the modulus exponent is uniquely
determined in one period by the character on the whole multiplicative group. -/
theorem finitePolePhase_normTwist_unique (ω : Characters F S) (v : S)
    (h : finiteZetaUnramified F v.val (sLocalFiniteZetaPhases F S ω v)) :
    ∃! t : ℝ, t ∈ Ico 0 (2 * Real.pi / logQ F v.val) ∧
      ∀ u : (v.val.adicCompletion F)ˣ,
        (sLocalFiniteZetaPhases F S ω v u : ℂ) =
          finiteZetaWeight F v.val ((t : ℂ) * Complex.I) u := by
  let χ := sLocalFiniteZetaPhases F S ω v
  let π := chosenFiniteUniformizer F v.val
  let L := logQ F v.val
  let t := finitePolePhase F S ω v
  have hphase := finitePolePhase_spec F S ω v
  refine ⟨t, ⟨hphase.1, finiteZetaUnramified_eq_normTwist F v.val χ h t hphase.2.1⟩,
    fun u hu => hphase.2.2 u hu.1 ?_⟩
  have hπ := hu.2 π
  rw [finiteZetaWeight, norm_finiteUniformizer F v.val π.val (chosenFiniteUniformizer_spec F v.val),
    Real.log_inv] at hπ
  apply Subtype.ext
  rw [Circle.coe_exp, Circle.coe_inv, hπ, ← Complex.exp_neg]
  simp only [Complex.ofReal_mul, Complex.ofReal_neg]
  congr 1
  ring

/-- Real, complex and unramified finite lattices on the actual S-local character component. -/
def sLocalEulerPoleLattices (ω : Characters F S) (z : ℂ) : Prop :=
    (∃ v : RealPlaces F, ∃ n : ℕ,
      z = -(sLocalRealArchParameters F S ω v).1 -
        ((sLocalRealArchParameters F S ω v).2 % 2 : ℕ) - 2 * (n : ℂ)) ∨
    (∃ v : ComplexPlaces F, ∃ n : ℕ,
      z = -(sLocalComplexArchParameters F S ω v).1 -
        ((sLocalComplexArchParameters F S ω v).2.natAbs : ℂ) / 2 - (n : ℂ)) ∨
    (∃ v : S, finiteZetaUnramified F v.val (sLocalFiniteZetaPhases F S ω v) ∧
      ∃ m : ℤ,
        z = ((m : ℂ) * (2 * Real.pi / logQ F v.val) - finitePolePhase F S ω v) * Complex.I)

/-- The denominator vanishes precisely on the union of the local lattices. -/
theorem sLocalEulerDenominator_eq_zero_iff_lattices (ω : Characters F S) (z : ℂ) :
    sLocalEulerDenominator F S ω z = 0 ↔ sLocalEulerPoleLattices F S ω z := by
  have hreal (v : RealPlaces F) :
      realArchZetaDenominator (sLocalRealArchParameters F S ω v).2
        (z + (sLocalRealArchParameters F S ω v).1) = 0 ↔
        ∃ n : ℕ, z = -(sLocalRealArchParameters F S ω v).1 -
          ((sLocalRealArchParameters F S ω v).2 % 2 : ℕ) - 2 * (n : ℂ) := by
    rw [realArchZetaDenominator_eq_zero_iff]
    exact exists_congr fun n => ⟨fun h => by linear_combination h, fun h => by linear_combination h⟩
  have hcomplex (v : ComplexPlaces F) :
      complexArchZetaDenominator (sLocalComplexArchParameters F S ω v).2
        (z + (sLocalComplexArchParameters F S ω v).1) = 0 ↔
        ∃ n : ℕ, z = -(sLocalComplexArchParameters F S ω v).1 -
          ((sLocalComplexArchParameters F S ω v).2.natAbs : ℂ) / 2 - (n : ℂ) := by
    rw [complexArchZetaDenominator_eq_zero_iff]
    exact exists_congr fun n => ⟨fun h => by linear_combination h, fun h => by linear_combination h⟩
  have hfinite (v : S) :
      (if finiteZetaUnramified F v.val (sLocalFiniteZetaPhases F S ω v) then
        finiteZetaDenominator F v.val (sLocalFiniteZetaPhases F S ω v) z else 1) = 0 ↔
      finiteZetaUnramified F v.val (sLocalFiniteZetaPhases F S ω v) ∧
        ∃ m : ℤ, z = ((m : ℂ) * (2 * Real.pi / logQ F v.val) -
          finitePolePhase F S ω v) * Complex.I := by
    by_cases h : finiteZetaUnramified F v.val (sLocalFiniteZetaPhases F S ω v)
    · simp only [h, ite_true, true_and]
      exact finiteZetaDenominator_eq_zero_iff_lattice F _ _ _ (finitePolePhase_spec F S ω v).2.1 z
    · simp [h]
  unfold sLocalEulerDenominator archimedeanNumberFieldZetaDenominator
    sLocalFiniteZetaDenominator sLocalEulerPoleLattices
  simp only [mul_eq_zero, Finset.prod_eq_zero_iff, Finset.mem_univ, true_and,
    hreal, hcomplex, hfinite, or_assoc]

/-- The explicit Tate factor on a chart, with the nonvanishing entire
normalizing factor kept as a parameter. The reflected character is the inverse
norm-one character and the reflected exponent is one minus the exponent. -/
def sLocalExplicitTateFactor (ω : Characters F S) (ε : ℂ → ℂ) (z : ℂ) : ℂ :=
  ε z * sLocalEulerFactor F S ω z * sLocalEulerDenominator F S ω⁻¹ (1 - z)

theorem sLocalExplicitTateFactor_meromorphic (ω : Characters F S) (ε : ℂ → ℂ)
    (hε : ∀ z, AnalyticAt ℂ ε z) : Meromorphic (sLocalExplicitTateFactor F S ω ε) := by
  intro z
  have h := (sLocalEulerDenominator_analytic F S ω⁻¹ (1 - z)).comp
    (f := fun s : ℂ => 1 - s) (x := z) (analyticAt_const.sub analyticAt_id)
  exact ((hε z).meromorphicAt.mul (sLocalEulerFactor_meromorphic F S ω z)).mul h.meromorphicAt

/-- Corrected Lemma 7.1.2.2 for the explicit local-factor product. In the complex
case the angular shift of the pole lattice is negative. -/
theorem sLocalExplicitTateFactor_poles (ω : Characters F S) (ε : ℂ → ℂ)
    (hε : ∀ z, AnalyticAt ℂ ε z) (hε₀ : ∀ z, ε z ≠ 0) (z : ℂ) :
    meromorphicOrderAt (sLocalExplicitTateFactor F S ω ε) z < 0 ↔ sLocalEulerPoleLattices F S ω z := by
  have h := sLocalEulerRatio_negativeDivisor F S ω ω⁻¹ hε hε₀ z
  change min (meromorphicOrderAt (sLocalExplicitTateFactor F S ω ε) z) 0 =
    min (meromorphicOrderAt (sLocalEulerFactor F S ω) z) 0 at h
  rw [← sLocalEulerDenominator_eq_zero_iff_lattices,
    ← sLocalEulerFactor_order_lt_zero_iff]
  simpa only [min_lt_iff, lt_irrefl, or_false] using
    (congrArg (· < (0 : WithTop ℤ)) h).to_iff


/-- At any listed point, the pole order of the explicit factor is the sum
of the orders contributed by all local denominators. -/
theorem sLocalExplicitTateFactor_order_at_pole (ω : Characters F S) (ε : ℂ → ℂ)
    (hε : ∀ z, AnalyticAt ℂ ε z) (hε₀ : ∀ z, ε z ≠ 0) {z : ℂ}
    (hz : sLocalEulerPoleLattices F S ω z) :
    let R (v : RealPlaces F) (s : ℂ) :=
      realArchZetaDenominator (sLocalRealArchParameters F S ω v).2
        (s + (sLocalRealArchParameters F S ω v).1)
    let C (v : ComplexPlaces F) (s : ℂ) :=
      complexArchZetaDenominator (sLocalComplexArchParameters F S ω v).2
        (s + (sLocalComplexArchParameters F S ω v).1)
    let P (v : S) (s : ℂ) :=
      if finiteZetaUnramified F v.val (sLocalFiniteZetaPhases F S ω v) then
        finiteZetaDenominator F v.val (sLocalFiniteZetaPhases F S ω v) s else 1
    meromorphicOrderAt (sLocalExplicitTateFactor F S ω ε) z =
      -((∑ v, meromorphicOrderAt (R v) z) +
        (∑ v, meromorphicOrderAt (C v) z) +
        (∑ v, meromorphicOrderAt (P v) z)) := by
  intro R C P
  have h₁ := (sLocalExplicitTateFactor_poles F S ω ε hε hε₀ z).mpr hz
  have h₂ := (sLocalEulerFactor_order_lt_zero_iff F S ω z).mpr
    ((sLocalEulerDenominator_eq_zero_iff_lattices F S ω z).mpr hz)
  have hEq := sLocalEulerRatio_negativeDivisor F S ω ω⁻¹ hε hε₀ z
  change min (meromorphicOrderAt (sLocalExplicitTateFactor F S ω ε) z) 0 =
    min (meromorphicOrderAt (sLocalEulerFactor F S ω) z) 0 at hEq
  rw [min_eq_left h₁.le, min_eq_left h₂.le] at hEq
  rw [hEq]
  have hR (v : RealPlaces F) : MeromorphicAt (R v) z :=
    ((realArchZetaDenominator_analytic (sLocalRealArchParameters F S ω v).2 _).comp
      (f := fun s : ℂ => s + (sLocalRealArchParameters F S ω v).1) (x := z)
      (analyticAt_id.add analyticAt_const)).meromorphicAt
  have hC (v : ComplexPlaces F) : MeromorphicAt (C v) z :=
    ((complexArchZetaDenominator_analytic (sLocalComplexArchParameters F S ω v).2 _).comp
      (f := fun s : ℂ => s + (sLocalComplexArchParameters F S ω v).1) (x := z)
      (analyticAt_id.add analyticAt_const)).meromorphicAt
  have hP (v : S) : MeromorphicAt (P v) z := by
    by_cases hv : finiteZetaUnramified F v.val (sLocalFiniteZetaPhases F S ω v)
    · simpa only [P, ite_eq_left hv] using
        (finiteZetaDenominator_analytic F v.val (sLocalFiniteZetaPhases F S ω v) z).meromorphicAt
    · simpa only [P, ite_eq_right hv] using (MeromorphicAt.const (1 : ℂ) z)
  let A (s : ℂ) := ∏ v, R v s
  let B (s : ℂ) := ∏ v, C v s
  let D (s : ℂ) := ∏ v, P v s
  have hA : MeromorphicAt A z := MeromorphicAt.fun_prod fun v _ => hR v
  have hB : MeromorphicAt B z := MeromorphicAt.fun_prod fun v _ => hC v
  have hD : MeromorphicAt D z := MeromorphicAt.fun_prod fun v _ => hP v
  change meromorphicOrderAt ((A * B * D)⁻¹) z = _
  rw [meromorphicOrderAt_inv, meromorphicOrderAt_mul (hA.mul hB) hD,
    meromorphicOrderAt_mul hA hB, meromorphicOrderAt_fun_prod (fun v _ => hR v),
    meromorphicOrderAt_fun_prod (fun v _ => hC v), meromorphicOrderAt_fun_prod (fun v _ => hP v)]


private def localRealDenominator (ω : Characters F S) (v : RealPlaces F) (z : ℂ) : ℂ :=
  realArchZetaDenominator (sLocalRealArchParameters F S ω v).2
    (z + (sLocalRealArchParameters F S ω v).1)

private def localComplexDenominator (ω : Characters F S) (v : ComplexPlaces F) (z : ℂ) : ℂ :=
  complexArchZetaDenominator (sLocalComplexArchParameters F S ω v).2
    (z + (sLocalComplexArchParameters F S ω v).1)

private def localFiniteDenominator (ω : Characters F S) (v : S) (z : ℂ) : ℂ :=
  if finiteZetaUnramified F v.val (sLocalFiniteZetaPhases F S ω v) then
    finiteZetaDenominator F v.val (sLocalFiniteZetaPhases F S ω v) z else 1

/-- The contributing finite places at a specified spectral point. -/
def sLocalFinitePolesAt (ω : Characters F S) (z : ℂ) : Finset S :=
  Finset.univ.filter fun v => localFiniteDenominator F S ω v z = 0

/-- The contributing infinite places at a specified spectral point. -/
def sLocalArchPoleCount (ω : Characters F S) (z : ℂ) : ℕ :=
  (Finset.univ.filter fun v => localRealDenominator F S ω v z = 0).card +
  (Finset.univ.filter fun v => localComplexDenominator F S ω v z = 0).card

/-- Number of contributing places on the actual S-local component. -/
def sLocalPoleCount (ω : Characters F S) (z : ℂ) : ℕ :=
  sLocalArchPoleCount F S ω z + (sLocalFinitePolesAt F S ω z).card

/-- A local Euler denominator contributes its value when regular and
its derivative when it has a simple zero. -/
def localEulerLeadingDenominator (D : ℂ → ℂ) (c : ℂ) : ℂ :=
  if D c = 0 then deriv D c else D c

private theorem analytic_exists_factor_simple_or_regular {D : ℂ → ℂ} {c : ℂ}
    (hD : AnalyticAt ℂ D c) (hs : D c = 0 → analyticOrderAt D c = 1) :
    ∃ U : ℂ → ℂ, AnalyticAt ℂ U c ∧ U c ≠ 0 ∧
      (D =ᶠ[𝓝 c] fun z => (z - c) ^ (if D c = 0 then 1 else 0 : ℕ) * U z) ∧
      U c = localEulerLeadingDenominator D c := by
  by_cases h : D c = 0
  · have ho : analyticOrderAt D c = (1 : ℕ) := hs h
    obtain ⟨U, hU, hUnz, he⟩ := hD.analyticOrderAt_eq_natCast.mp ho
    have he' : D =ᶠ[𝓝 c] fun z => (z - c) * U z := by
      filter_upwards [he] with z hz
      simpa only [pow_one, smul_eq_mul] using hz
    have hd : HasDerivAt (fun z : ℂ => (z - c) * U z) (U c) c := by
      simpa using ((hasDerivAt_id c).sub_const c).fun_mul hU.differentiableAt.hasDerivAt
    exact ⟨U, hU, hUnz, by simpa only [ite_eq_left h, pow_one] using he',
      by rw [localEulerLeadingDenominator, ite_eq_left h, he'.deriv_eq, hd.deriv]⟩
  · exact ⟨D, hD, h, by simp [h], by simp [localEulerLeadingDenominator, h]⟩

/-- Factoring out the simple local zeros commutes with a finite product. -/
theorem analytic_finset_prod_factor_simpleZeros {ι : Type*} (I : Finset ι)
    (D : ι → ℂ → ℂ) (c : ℂ)
    (hD : ∀ i ∈ I, AnalyticAt ℂ (D i) c)
    (hs : ∀ i ∈ I, D i c = 0 → analyticOrderAt (D i) c = 1) :
    ∃ U : ℂ → ℂ, AnalyticAt ℂ U c ∧ U c ≠ 0 ∧
      ((fun z => ∏ i ∈ I, D i z) =ᶠ[𝓝 c]
        fun z => (z - c) ^ (I.filter fun i => D i c = 0).card * U z) ∧
      U c = ∏ i ∈ I, localEulerLeadingDenominator (D i) c := by
  classical
  induction I using Finset.induction_on with
  | empty =>
    exact ⟨1, analyticAt_const, one_ne_zero, by simp, by simp⟩
  | insert i I hi hI =>
    obtain ⟨A, hA, hAnz, hea, ha⟩ :=
      analytic_exists_factor_simple_or_regular (hD i (Finset.mem_insert_self _ _))
        (hs i (Finset.mem_insert_self _ _))
    obtain ⟨B, hB, hBnz, heb, hb⟩ := hI
      (fun j hj => hD j (Finset.mem_insert_of_mem hj))
      (fun j hj => hs j (Finset.mem_insert_of_mem hj))
    refine ⟨fun z ↦ A z * B z, hA.mul hB, mul_ne_zero hAnz hBnz, ?_, ?_⟩
    · filter_upwards [hea, heb] with z hza hzb
      have hc : ((insert i I).filter fun j => D j c = 0).card =
          (if D i c = 0 then 1 else 0 : ℕ) + (I.filter fun j => D j c = 0).card := by
        rw [Finset.filter_insert]
        by_cases h : D i c = 0
        · have hn : i ∉ I.filter (fun j => D j c = 0) := fun hj => hi (Finset.mem_filter.mp hj).1
          simp [h, hn, Nat.add_comm]
        · simp [h]
      rw [Finset.prod_insert hi, hza, hzb, hc, pow_add]
      ring
    · simp [Finset.prod_insert hi, ha, hb]

/-- Product of the first nonzero Taylor terms of each local denominator. -/
def sLocalEulerLeadingDenominator (ω : Characters F S) (c : ℂ) : ℂ :=
  (∏ v : RealPlaces F, localEulerLeadingDenominator (localRealDenominator F S ω v) c) *
    (∏ v : ComplexPlaces F, localEulerLeadingDenominator (localComplexDenominator F S ω v) c) *
    ∏ v : S, localEulerLeadingDenominator (localFiniteDenominator F S ω v) c

/-- The leading Taylor term of the S-local denominator is the product of
the local leading terms, and the multiplicity is the number of contributing places. -/
theorem sLocalEulerDenominator_exists_leadingFactor
    (ω : Characters F S) (c : ℂ) :
    ∃ U : ℂ → ℂ, AnalyticAt ℂ U c ∧ U c ≠ 0 ∧
      (sLocalEulerDenominator F S ω =ᶠ[𝓝 c]
        fun z => (z - c) ^ sLocalPoleCount F S ω c * U z) ∧
      U c = sLocalEulerLeadingDenominator F S ω c := by
  let R := localRealDenominator F S ω
  let C := localComplexDenominator F S ω
  let P := localFiniteDenominator F S ω
  have hR (v : RealPlaces F) : AnalyticAt ℂ (R v) c :=
    (realArchZetaDenominator_analytic (sLocalRealArchParameters F S ω v).2 _).comp
      (f := fun s => s + (sLocalRealArchParameters F S ω v).1) (x := c)
      (analyticAt_id.add analyticAt_const)
  have hRs (v : RealPlaces F) (hv : R v c = 0) : analyticOrderAt (R v) c = 1 := by
    let a := sLocalRealArchParameters F S ω v
    let g (s : ℂ) := s + a.1
    have hd : HasDerivAt g 1 c := (hasDerivAt_id c).add_const a.1
    change analyticOrderAt (realArchZetaDenominator a.2 ∘ g) c = _
    have hg : AnalyticAt ℂ g c := analyticAt_id.add analyticAt_const
    rw [analyticOrderAt_comp_of_deriv_ne_zero hg (by rw [hd.deriv]; exact one_ne_zero)]
    exact realArchZetaDenominator_simple_zero a.2 _ hv
  have hC (v : ComplexPlaces F) : AnalyticAt ℂ (C v) c :=
    (complexArchZetaDenominator_analytic (sLocalComplexArchParameters F S ω v).2 _).comp
      (f := fun s => s + (sLocalComplexArchParameters F S ω v).1) (x := c)
      (analyticAt_id.add analyticAt_const)
  have hCs (v : ComplexPlaces F) (hv : C v c = 0) : analyticOrderAt (C v) c = 1 := by
    let a := sLocalComplexArchParameters F S ω v
    let g (s : ℂ) := s + a.1
    have hd : HasDerivAt g 1 c := (hasDerivAt_id c).add_const a.1
    change analyticOrderAt (complexArchZetaDenominator a.2 ∘ g) c = _
    have hg : AnalyticAt ℂ g c := analyticAt_id.add analyticAt_const
    rw [analyticOrderAt_comp_of_deriv_ne_zero hg (by rw [hd.deriv]; exact one_ne_zero)]
    exact complexArchZetaDenominator_simple_zero a.2 _ hv
  have hP (v : S) : AnalyticAt ℂ (P v) c := by
    unfold P localFiniteDenominator
    split_ifs
    · exact finiteZetaDenominator_analytic F v.val (sLocalFiniteZetaPhases F S ω v) c
    · exact analyticAt_const
  have hPs (v : S) (hv : P v c = 0) : analyticOrderAt (P v) c = 1 := by
    unfold P localFiniteDenominator at hv ⊢
    split_ifs at hv ⊢
    · exact finiteZetaDenominator_simple_zero F v.val (sLocalFiniteZetaPhases F S ω v) c hv
    · exact (one_ne_zero hv).elim
  obtain ⟨a, ha, haz, hea, hva⟩ :=
    analytic_finset_prod_factor_simpleZeros Finset.univ R c (fun v _ ↦ hR v) (fun v _ ↦ hRs v)
  obtain ⟨b, hb, hbz, heb, hvb⟩ :=
    analytic_finset_prod_factor_simpleZeros Finset.univ C c (fun v _ ↦ hC v) (fun v _ ↦ hCs v)
  obtain ⟨d, hd, hdz, hed, hvd⟩ :=
    analytic_finset_prod_factor_simpleZeros Finset.univ P c (fun v _ ↦ hP v) (fun v _ ↦ hPs v)
  refine ⟨fun z ↦ a z * b z * d z, (ha.mul hb).mul hd, mul_ne_zero (mul_ne_zero haz hbz) hdz,
    ?_, ?_⟩
  swap
  · change a c * b c * d c = sLocalEulerLeadingDenominator F S ω c
    rw [hva, hvb, hvd]
    rfl
  filter_upwards [hea, heb, hed] with z hza hzb hzd
  change (∏ v, R v z) * (∏ v, C v z) * (∏ v, P v z) = _
  rw [hza, hzb, hzd, sLocalPoleCount, sLocalArchPoleCount, sLocalFinitePolesAt, pow_add, pow_add]
  ring

/-- Every contributing place counts once in the pole order. -/
theorem sLocalExplicitTateFactor_order_eq_neg_count
    (ω : Characters F S) (ε : ℂ → ℂ) (hε : ∀ z, AnalyticAt ℂ ε z)
    (hε₀ : ∀ z, ε z ≠ 0) {z : ℂ} (hz : sLocalEulerPoleLattices F S ω z) :
    meromorphicOrderAt (sLocalExplicitTateFactor F S ω ε) z =
      -(sLocalPoleCount F S ω z : WithTop ℤ) := by
  obtain ⟨U, hU, hUne, he, _⟩ := sLocalEulerDenominator_exists_leadingFactor F S ω z
  have hD := sLocalEulerDenominator_analytic F S ω z
  have hOrd := hD.analyticOrderAt_eq_natCast.mpr ⟨U, hU, hUne, he⟩
  have hEuler : meromorphicOrderAt (sLocalEulerFactor F S ω) z =
      -(sLocalPoleCount F S ω z : WithTop ℤ) := by
    change meromorphicOrderAt (sLocalEulerDenominator F S ω)⁻¹ z = _
    rw [meromorphicOrderAt_inv, hD.meromorphicOrderAt_eq, hOrd, ENat.map_natCast]
    rfl
  have hA := (sLocalExplicitTateFactor_poles F S ω ε hε hε₀ z).mpr hz
  have hB := (sLocalEulerFactor_order_lt_zero_iff F S ω z).mpr
    ((sLocalEulerDenominator_eq_zero_iff_lattices F S ω z).mpr hz)
  have h := sLocalEulerRatio_negativeDivisor F S ω ω⁻¹ hε hε₀ z
  change min (meromorphicOrderAt (sLocalExplicitTateFactor F S ω ε) z) 0 =
    min (meromorphicOrderAt (sLocalEulerFactor F S ω) z) 0 at h
  rw [min_eq_left hA.le, min_eq_left hB.le] at h
  exact h.trans hEuler

/-- The total multiplicity is bounded by the number of places in the product. -/
theorem sLocalPoleCount_le_places (ω : Characters F S) (z : ℂ) :
    sLocalPoleCount F S ω z ≤ Fintype.card (InfinitePlace F) + S.card := by
  rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces]
  exact Nat.add_le_add (Nat.add_le_add (Finset.card_le_univ _) (Finset.card_le_univ _))
    (by simpa only [Fintype.card_coe] using
      Finset.card_le_univ (sLocalFinitePolesAt F S ω z))

private theorem sLocalFinitePolesAt_empty_of_re_neg (ω : Characters F S) {z : ℂ}
    (hz : z.re < 0) : sLocalFinitePolesAt F S ω z = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro v hv
  have hv' := (Finset.mem_filter.mp hv).2
  by_cases h : finiteZetaUnramified F v.val (sLocalFiniteZetaPhases F S ω v)
  · simp only [localFiniteDenominator, ite_eq_left h] at hv'
    obtain ⟨m, hm⟩ := (finiteZetaDenominator_eq_zero_iff_lattice F _ _ _
      (finitePolePhase_spec F S ω v).2.1 z).mp hv'
    have hre := congrArg Complex.re hm
    simp only [Complex.mul_re, Complex.sub_im, Complex.ofReal_im, Complex.intCast_im,
      Complex.div_im, Complex.mul_im, show (2 : ℂ).im = 0 by norm_num, Complex.I_re, Complex.I_im,
      zero_mul, mul_zero, sub_zero, zero_div, add_zero, mul_one] at hre
    exact (ne_of_lt hz) hre
  · simp [localFiniteDenominator, h] at hv'

/-- Only archimedean places contribute strictly to the left of the imaginary axis. -/
theorem sLocalPoleCount_le_infinitePlaces (ω : Characters F S) {z : ℂ} (hz : z.re < 0) :
    sLocalPoleCount F S ω z ≤ Fintype.card (InfinitePlace F) := by
  rw [sLocalPoleCount, sLocalFinitePolesAt_empty_of_re_neg F S ω hz, Finset.card_empty, add_zero,
    InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces]
  exact Nat.add_le_add (Finset.card_le_univ _) (Finset.card_le_univ _)

/-- At a negative odd abscissa real sign factors can contribute alongside
the complex factors. Real places of even parity contribute nothing there. -/
theorem sLocalPoleCount_le_of_re_neg_odd (ω : Characters F S) (k : ℕ) {z : ℂ}
    (hz : z.re = -((2 * k + 1 : ℕ) : ℝ)) :
    sLocalPoleCount F S ω z ≤ InfinitePlace.nrComplexPlaces F +
      (Finset.univ.filter fun v : RealPlaces F =>
        (sLocalRealArchParameters F S ω v).2 % 2 = 1).card := by
  have hzneg : z.re < 0 := by
    rw [hz, neg_lt_zero]
    positivity
  rw [sLocalPoleCount, sLocalFinitePolesAt_empty_of_re_neg F S ω hzneg,
    Finset.card_empty, add_zero, sLocalArchPoleCount, add_comm]
  apply add_le_add (Finset.card_le_univ _)
  apply Finset.card_le_card
  intro v hv
  have hzero := (Finset.mem_filter.mp hv).2
  obtain ⟨n, hn⟩ := (realArchZetaDenominator_eq_zero_iff _ _).mp hzero
  have h := congrArg Complex.re hn
  simp [hz, Complex.mul_re, sLocalRealArchParameters_re] at h
  have hnat : 2 * k + 1 = (sLocalRealArchParameters F S ω v).2 % 2 + 2 * n := by
    exact_mod_cast (by linarith [h] :
      (2 : ℝ) * k + 1 = ((sLocalRealArchParameters F S ω v).2 % 2 : ℕ) + 2 * n)
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩

/-- In the open left half-plane the pole order is bounded by the field degree. -/
theorem sLocalPoleCount_le_degree_of_re_neg (ω : Characters F S) {z : ℂ} (hz : z.re < 0) :
    sLocalPoleCount F S ω z ≤ Module.finrank ℚ F := by
  apply (sLocalPoleCount_le_infinitePlaces F S ω hz).trans
  rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    ← InfinitePlace.card_add_two_mul_card_eq_rank F]
  omega

private theorem finitePlaces_card_le_degree_of_liesOver (A : Finset S)
    {p : Ideal ℤ} [p.IsMaximal] (hp : p ≠ ⊥)
    (h : ∀ v ∈ A, v.val.asIdeal.LiesOver p) :
    A.card ≤ Module.finrank ℚ F := by
  apply (Finset.card_le_card_of_injOn (fun v : S => v.val.asIdeal)
    (t := IsDedekindDomain.primesOverFinset p (𝓞 F)) ?_ ?_).trans
    (Ideal.card_primesOverFinset_le_finrank (𝓞 F) ℚ F hp)
  · intro v hv
    exact (IsDedekindDomain.mem_primesOverFinset_iff hp (𝓞 F)).mpr ⟨v.val.isPrime, h v hv⟩
  · exact (HeightOneSpectrum.asIdeal_injective.comp Subtype.val_injective).injOn

/-- A family of contributing places over one residue prime has at most the
field degree many elements. -/
theorem sLocalFinitePolesAt_card_le_degree_of_liesOver (ω : Characters F S) (z : ℂ)
    {p : Ideal ℤ} [p.IsMaximal] (hp : p ≠ ⊥)
    (h : ∀ v ∈ sLocalFinitePolesAt F S ω z, v.val.asIdeal.LiesOver p) :
    (sLocalFinitePolesAt F S ω z).card ≤ Module.finrank ℚ F :=
  finitePlaces_card_le_degree_of_liesOver F S _ hp h

private theorem sLocalPoleCount_eq_zero_iff (ω : Characters F S) (z : ℂ) :
    sLocalPoleCount F S ω z = 0 ↔ sLocalEulerDenominator F S ω z ≠ 0 := by
  change _ ↔ (∏ v : RealPlaces F, localRealDenominator F S ω v z) *
      (∏ v : ComplexPlaces F, localComplexDenominator F S ω v z) *
      (∏ v : S, localFiniteDenominator F S ω v z) ≠ 0
  simp only [sLocalPoleCount, sLocalArchPoleCount, sLocalFinitePolesAt, Nat.add_eq_zero_iff,
    Finset.card_filter_eq_zero_iff, ne_eq, mul_eq_zero, Finset.prod_eq_zero_iff,
    Finset.mem_univ, true_and, true_implies]
  push Not
  rfl

/-- The place count detects every threshold for the order of a pole. -/
theorem sLocalExplicitTateFactor_order_lt_neg_iff
    (ω : Characters F S) (ε : ℂ → ℂ) (hε : ∀ z, AnalyticAt ℂ ε z)
    (hε₀ : ∀ z, ε z ≠ 0) (z : ℂ) (n : ℕ) :
    meromorphicOrderAt (sLocalExplicitTateFactor F S ω ε) z < -(n : WithTop ℤ) ↔
      n < sLocalPoleCount F S ω z := by
  by_cases hz : sLocalEulerPoleLattices F S ω z
  · rw [sLocalExplicitTateFactor_order_eq_neg_count F S ω ε hε hε₀ hz]
    change ((-(sLocalPoleCount F S ω z : ℤ) : ℤ) : WithTop ℤ) < ((-(n : ℤ) : ℤ) : WithTop ℤ) ↔ _
    rw [WithTop.coe_lt_coe]
    omega
  · have hn : sLocalEulerDenominator F S ω z ≠ 0 :=
      fun h => hz ((sLocalEulerDenominator_eq_zero_iff_lattices F S ω z).mp h)
    have hnonneg := not_lt.mp (fun h =>
      hz ((sLocalExplicitTateFactor_poles F S ω ε hε hε₀ z).mp h))
    rw [(sLocalPoleCount_eq_zero_iff F S ω z).mpr hn]
    have hneg : -(n : WithTop ℤ) ≤ 0 := by
      change ((-(n : ℤ) : ℤ) : WithTop ℤ) ≤ ((0 : ℤ) : WithTop ℤ)
      exact WithTop.coe_le_coe.mpr (by omega)
    simp [not_lt_of_ge (hneg.trans hnonneg)]

/-- A pole order above the field degree is possible only on the imaginary axis. -/
theorem sLocalPoleCount_excess_on_axis (ω : Characters F S) {z : ℂ}
    (hdegree : Module.finrank ℚ F < sLocalPoleCount F S ω z) : z.re = 0 := by
  rcases lt_trichotomy z.re 0 with hneg | hzero | hpos
  · exact ((sLocalPoleCount_le_degree_of_re_neg F S ω hneg).not_gt hdegree).elim
  · exact hzero
  · have hn := sLocalEulerDenominator_ne_zero_of_pos F S ω hpos
    have hz := (sLocalPoleCount_eq_zero_iff F S ω z).mpr hn
    omega

/-- The rational residue prime below a finite place of the number field. -/
def finiteResiduePrime (v : Place F) : ℕ :=
  (primeIdeal_norm_isPrimePower F v).choose

theorem finiteResiduePrime_spec (v : Place F) :
    ∃ d : ℕ, (finiteResiduePrime F v).Prime ∧ 0 < d ∧
      v.asIdeal.LiesOver (Ideal.span {(finiteResiduePrime F v : ℤ)}) ∧
      v.asIdeal.absNorm = finiteResiduePrime F v ^ d :=
  (primeIdeal_norm_isPrimePower F v).choose_spec

/-- The places whose actual local finite Hecke Euler denominator vanishes
at the specified parameter. The coefficient is zero at ramified places. -/
def globalFiniteHeckeEulerPoles (χ : PontryaginDual (IdeleClass F)) (s : ℂ) : Set (Place F) :=
  {v | (heckeEulerFactor F (heckeEulerCoefficient F χ (chosenFiniteUniformizer F)) v s)⁻¹ = 0}

private theorem globalFiniteEulerFactor_eq (χ : PontryaginDual (IdeleClass F))
    (v : Place F) (hu : unramifiedFiniteCharacter F χ v) :
    heckeEulerFactor F (heckeEulerCoefficient F χ (chosenFiniteUniformizer F)) v =
      fun s ↦ (finiteZetaDenominator F v (χ.comp (finitePlaceInsertion F v)) s)⁻¹ := by
  funext s
  have hq : (0 : ℝ) < (v.asIdeal.absNorm : ℝ) :=
    zero_lt_one.trans (by exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v)
  have he : (v.asIdeal.absNorm : ℂ) ^ (-s) =
      Complex.exp (-s * (Real.log (v.asIdeal.absNorm : ℝ) : ℂ)) := by
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hq.ne' : (v.asIdeal.absNorm : ℂ) ≠ 0),
      ← Complex.ofReal_natCast, ← Complex.ofReal_log hq.le, mul_comm]
  have hχ : ((χ.comp (finitePlaceInsertion F v)) (chosenFiniteUniformizer F v) : ℂ) =
      (χ (ideleClassMap F (singleFiniteIdele F v (chosenFiniteUniformizer F v))) : ℂ) := by
    change (χ (finitePlaceInsertion F v (chosenFiniteUniformizer F v)) : ℂ) = _
    rw [finitePlaceInsertion_apply]
  rw [heckeEulerFactor, heckeEulerCoefficient, ite_eq_left hu, he, finiteZetaDenominator,
    finiteZetaRatio, hχ]

private theorem globalFiniteEulerPole_iff (χ : PontryaginDual (IdeleClass F))
    (v : Place F) (s : ℂ) :
    v ∈ globalFiniteHeckeEulerPoles F χ s ↔
      unramifiedFiniteCharacter F χ v ∧
      finiteZetaDenominator F v (χ.comp (finitePlaceInsertion F v)) s = 0 := by
  by_cases hu : unramifiedFiniteCharacter F χ v
  · simp [globalFiniteHeckeEulerPoles, globalFiniteEulerFactor_eq F χ v hu, hu]
  · simp [globalFiniteHeckeEulerPoles, heckeEulerFactor, heckeEulerCoefficient, hu]

/-- An unramified finite Hecke factor has infinitely many distinct pole parameters. -/
theorem globalFiniteHeckeEuler_poleParameters_infinite (χ : PontryaginDual (IdeleClass F))
    (v : Place F) (hu : unramifiedFiniteCharacter F χ v) :
    {z : ℂ | v ∈ globalFiniteHeckeEulerPoles F χ z}.Infinite := by
  let ψ := χ.comp (finitePlaceInsertion F v)
  obtain ⟨t, _, ht⟩ := (existsUnique_circle_log_period (logQ_pos F v)
    (ψ (chosenFiniteUniformizer F v))⁻¹).exists
  let d : ℂ := 2 * Real.pi / logQ F v
  have hd : d ≠ 0 := div_ne_zero
    (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
    (Complex.ofReal_ne_zero.mpr (logQ_pos F v).ne')
  let z (m : ℤ) : ℂ := ((m : ℂ) * d - t) * Complex.I
  have hi : Injective z := by
    intro a b hab
    have h := mul_right_cancel₀ Complex.I_ne_zero hab
    change (a : ℂ) * d - t = (b : ℂ) * d - t at h
    have he : (a : ℂ) = (b : ℂ) := mul_right_cancel₀ hd (sub_left_inj.mp h)
    exact_mod_cast he
  apply (infinite_range_of_injective hi).mono
  rintro _ ⟨m, rfl⟩
  apply (globalFiniteEulerPole_iff F χ v (z m)).mpr
  exact ⟨hu, (finiteZetaDenominator_eq_zero_iff_lattice F v ψ t ht (z m)).mpr ⟨m, rfl⟩⟩

/-- The denominator criterion describes precisely the simple meromorphic poles
of the actual local finite Euler factor. -/
theorem globalFiniteHeckeEulerPoles_iff_order (χ : PontryaginDual (IdeleClass F))
    (v : Place F) (s : ℂ) :
    v ∈ globalFiniteHeckeEulerPoles F χ s ↔
      meromorphicOrderAt (heckeEulerFactor F (heckeEulerCoefficient F χ
        (chosenFiniteUniformizer F)) v) s = (-1 : ℤ) := by
  rw [globalFiniteEulerPole_iff]
  by_cases hu : unramifiedFiniteCharacter F χ v
  · rw [globalFiniteEulerFactor_eq F χ v hu, and_iff_right hu]
    let ψ := χ.comp (finitePlaceInsertion F v)
    let D := finiteZetaDenominator F v ψ
    change D s = 0 ↔ meromorphicOrderAt D⁻¹ s = (-1 : ℤ)
    rw [meromorphicOrderAt_inv]
    have ha := finiteZetaDenominator_analytic F v ψ s
    by_cases hz : finiteZetaDenominator F v ψ s = 0
    · have ho := finiteZetaDenominator_simple_zero F v ψ s hz
      change finiteZetaDenominator F v ψ s = 0 ↔
        -meromorphicOrderAt (finiteZetaDenominator F v ψ) s = (-1 : ℤ)
      rw [ha.meromorphicOrderAt_eq, ho]
      simp [hz]
    · have ho := ha.analyticOrderAt_eq_zero.mpr hz
      change finiteZetaDenominator F v ψ s = 0 ↔
        -meromorphicOrderAt (finiteZetaDenominator F v ψ) s = (-1 : ℤ)
      rw [ha.meromorphicOrderAt_eq, ho]
      simp [hz]
  · have he : heckeEulerFactor F (heckeEulerCoefficient F χ (chosenFiniteUniformizer F)) v =
        fun _ ↦ (1 : ℂ) := by
      funext z
      simp [heckeEulerFactor, heckeEulerCoefficient, hu]
    norm_num [hu, he, meromorphicOrderAt_const]

private theorem globalFiniteEulerPole_normPower (χ : PontryaginDual (IdeleClass F))
    {v : Place F} {s : ℂ} (h : v ∈ globalFiniteHeckeEulerPoles F χ s) :
    (v.asIdeal.absNorm : ℂ) ^ s = heckeEulerCoefficient F χ (chosenFiniteUniformizer F) v := by
  have hqn : v.asIdeal.absNorm ≠ 0 := (zero_lt_one.trans (NumberField.HeightOneSpectrum.one_lt_absNorm v)).ne'
  have hq : (v.asIdeal.absNorm : ℂ) ≠ 0 := by exact_mod_cast hqn
  change (1 - heckeEulerCoefficient F χ (chosenFiniteUniformizer F) v *
    (v.asIdeal.absNorm : ℂ) ^ (-s))⁻¹⁻¹ = 0 at h
  rw [inv_inv, sub_eq_zero, Complex.cpow_neg] at h
  have hqs : (v.asIdeal.absNorm : ℂ) ^ s ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl hq)
  simpa only [one_mul] using (eq_mul_inv_iff_mul_eq₀ hqs).mp h

private theorem exists_distinct_prime_globalEulerPoles (χ : PontryaginDual (IdeleClass F))
    {s : ℂ} (h : (globalFiniteHeckeEulerPoles F χ s).Infinite) :
    ∃ v ∈ globalFiniteHeckeEulerPoles F χ s, ∃ w ∈ globalFiniteHeckeEulerPoles F χ s,
      finiteResiduePrime F v ≠ finiteResiduePrime F w := by
  obtain ⟨v, hv⟩ := h.nonempty
  by_contra! hn
  let p := finiteResiduePrime F v
  obtain ⟨_, hp, _, _, _⟩ := finiteResiduePrime_spec F v
  letI : Fact p.Prime := ⟨hp⟩
  letI : (Ideal.span {(p : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime p
  have hp₀ : Ideal.span {(p : ℤ)} ≠ ⊥ := by simpa using hp.ne_zero
  let A := IsDedekindDomain.primesOverFinset (Ideal.span {(p : ℤ)}) (𝓞 F)
  have hmap : MapsTo (fun w : Place F ↦ w.asIdeal) (globalFiniteHeckeEulerPoles F χ s) A := by
    intro w hw
    obtain ⟨_, _, _, hlie, _⟩ := finiteResiduePrime_spec F w
    rw [← hn v hv w hw] at hlie
    exact (IsDedekindDomain.mem_primesOverFinset_iff hp₀ (𝓞 F)).mpr ⟨w.isPrime, hlie⟩
  exact h ((A.finite_toSet.subset hmap.image_subset).of_finite_image
    HeightOneSpectrum.asIdeal_injective.injOn)

private theorem globalFiniteEulerPole_re (χ : PontryaginDual (IdeleClass F))
    {v : Place F} {s : ℂ} (h : v ∈ globalFiniteHeckeEulerPoles F χ s) : s.re = 0 := by
  let ψ := χ.comp (finitePlaceInsertion F v)
  have hw := ((globalFiniteEulerPole_iff F χ v s).mp h).2
  obtain ⟨t, _, ht⟩ := (existsUnique_circle_log_period (logQ_pos F v)
    (ψ (chosenFiniteUniformizer F v))⁻¹).exists
  obtain ⟨m, hm⟩ := (finiteZetaDenominator_eq_zero_iff_lattice F v ψ t ht s).mp hw
  rw [hm]
  simp only [Complex.mul_re, Complex.sub_im, Complex.ofReal_im, Complex.intCast_im,
    Complex.div_im, Complex.mul_im, show (2 : ℂ).im = 0 by norm_num, Complex.I_re,
    Complex.I_im, zero_mul, mul_zero, sub_zero, zero_div, add_zero, mul_one]

/-- The finite-place pole comparison of Theorem 1.7.1.1(1) for the
actual global Hecke coefficients. -/
theorem globalFiniteHeckeEuler_commonPoles (χ : PontryaginDual (IdeleClass F))
    (v w : Place F) (hvw : finiteResiduePrime F v ≠ finiteResiduePrime F w) :
    {s : ℂ | v ∈ globalFiniteHeckeEulerPoles F χ s ∧
      w ∈ globalFiniteHeckeEulerPoles F χ s}.Subsingleton := by
  obtain ⟨e, hp, he, _, hv⟩ := finiteResiduePrime_spec F v
  obtain ⟨f, hq, hf, _, hw⟩ := finiteResiduePrime_spec F w
  have h := finiteZetaDenominator_common_zeros_subsingleton F v w
    (χ.comp (finitePlaceInsertion F v)) (χ.comp (finitePlaceInsertion F w))
    hp hq hvw he hf hv hw
  intro s hs t ht
  exact h ⟨((globalFiniteEulerPole_iff F χ v s).mp hs.1).2,
      ((globalFiniteEulerPole_iff F χ w s).mp hs.2).2⟩
    ⟨((globalFiniteEulerPole_iff F χ v t).mp ht.1).2,
      ((globalFiniteEulerPole_iff F χ w t).mp ht.2).2⟩

/-- Theorem 1.7.1.1(2). For a unitary Hecke character expressed as an
algebraic character times a complex norm power, an infinite set of local
finite poles can occur only at the indicated imaginary translate.
Algebraicity is used at the unramified uniformizers of the untwisted character. -/
theorem globalFiniteHeckeEuler_infinitePoles_of_schanuel (hS : SchanuelConjecture)
    (χ : PontryaginDual (IdeleClass F)) (χ₀ : IdeleClass F → ℂ) (s₀ : ℂ)
    (htwist : ∀ g, (χ g : ℂ) = χ₀ g * (ideleClassNorm F g : ℂ) ^ s₀)
    (hA : ∀ v, unramifiedFiniteCharacter F χ v →
      IsAlgebraic ℚ (χ₀ (ideleClassMap F (singleFiniteIdele F v (chosenFiniteUniformizer F v)))))
    {s : ℂ} (hs : (globalFiniteHeckeEulerPoles F χ s).Infinite) :
    s = -(s₀.im : ℂ) * Complex.I := by
  obtain ⟨v, hv, w, hw, hvw⟩ := exists_distinct_prime_globalEulerPoles F χ hs
  have halg (u : Place F) (hu : u ∈ globalFiniteHeckeEulerPoles F χ s) :
      IsAlgebraic ℚ ((u.asIdeal.absNorm : ℂ) ^ (s + s₀)) := by
    let g := ideleClassMap F (singleFiniteIdele F u (chosenFiniteUniformizer F u))
    have hun := ((globalFiniteEulerPole_iff F χ u s).mp hu).1
    have h := globalFiniteEulerPole_normPower F χ hu
    have he : (ideleClassNorm F g : ℂ) = (u.asIdeal.absNorm : ℂ)⁻¹ := by
      rw [show g = ideleClassMap F (singleFiniteIdele F u (chosenFiniteUniformizer F u)) by rfl,
        ideleClassNorm_mk, singleFiniteIdele_norm,
        norm_finiteUniformizer F u _ (chosenFiniteUniformizer_spec F u),
        Complex.ofReal_inv, Complex.ofReal_natCast]
    have hq : (u.asIdeal.absNorm : ℂ) ≠ 0 := by
      exact_mod_cast (zero_lt_one.trans (NumberField.HeightOneSpectrum.one_lt_absNorm u)).ne'
    have hqs : (u.asIdeal.absNorm : ℂ) ^ s₀ ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hq)
    rw [heckeEulerCoefficient, ite_eq_left hun] at h
    change (u.asIdeal.absNorm : ℂ) ^ s = (χ g : ℂ) at h
    have hInv : ((u.asIdeal.absNorm : ℂ)⁻¹) ^ s₀ =
        ((u.asIdeal.absNorm : ℂ) ^ s₀)⁻¹ := by
      simpa only [Complex.ofReal_natCast] using
        Complex.inv_cpow_ofReal_nonneg (Nat.cast_nonneg (u.asIdeal.absNorm) : 0 ≤ (_ : ℝ)) s₀
    rw [htwist g, he, hInv] at h
    rw [Complex.cpow_add _ _ hq, h, mul_assoc, inv_mul_cancel₀ hqs, mul_one]
    exact hA u hun
  obtain ⟨e, hp, he, _, hNv⟩ := finiteResiduePrime_spec F v
  obtain ⟨f, hq, hf, _, hNw⟩ := finiteResiduePrime_spec F w
  have hi := primePower_exponents_im_eq_zero_of_schanuel hS hp hq hvw he hf
    (hNv ▸ halg v hv) (hNw ▸ halg w hw)
  have hr := globalFiniteEulerPole_re F χ hv
  apply Complex.ext
  · simpa [Complex.mul_re] using hr
  · simp only [Complex.add_im] at hi
    simpa [Complex.mul_im] using eq_neg_of_add_eq_zero_left hi

/-- Theorem 1.7.1.1(3). For a finite-order Hecke character only zero
can be a pole of infinitely many local finite Euler factors. -/
theorem globalFiniteHeckeEuler_infinitePoles_finiteOrder
    (χ : PontryaginDual (IdeleClass F)) {N : ℕ} (hN : 0 < N) (hχ : χ ^ N = 1)
    {s : ℂ} (hs : (globalFiniteHeckeEulerPoles F χ s).Infinite) : s = 0 := by
  obtain ⟨v, hv, w, hw, hvw⟩ := exists_distinct_prime_globalEulerPoles F χ hs
  obtain ⟨e, hp, he, _, hNv⟩ := finiteResiduePrime_spec F v
  obtain ⟨f, hq, hf, _, hNw⟩ := finiteResiduePrime_spec F w
  have hpow (u : Place F) :
      ((χ.comp (finitePlaceInsertion F u)) (chosenFiniteUniformizer F u)) ^ N = 1 := by
    let g := finitePlaceInsertion F u (chosenFiniteUniformizer F u)
    change χ g ^ N = 1
    have hh : ((χ : IdeleClass F →ₜ* Circle) ^ N) g = 1 := DFunLike.congr_fun hχ g
    exact (ContinuousMonoidHom.pow_apply (χ : IdeleClass F →ₜ* Circle) N g).symm.trans hh
  exact finiteZetaDenominator_common_zero_of_finite_order F v w
    (χ.comp (finitePlaceInsertion F v)) (χ.comp (finitePlaceInsertion F w))
    hp hq hvw he hf hNv hNw hN (hpow v) (hpow w)
    ((globalFiniteEulerPole_iff F χ v s).mp hv).2
    ((globalFiniteEulerPole_iff F χ w s).mp hw).2

private theorem sLocalFinitePolesAt_subset_unramified (ω : Characters F S) (z : ℂ) :
    sLocalFinitePolesAt F S ω z ⊆
      Finset.univ.filter (fun v => finiteZetaUnramified F v.val (sLocalFiniteZetaPhases F S ω v)) := by
  intro v hv
  have h := (Finset.mem_filter.mp hv).2
  by_cases hv' : finiteZetaUnramified F v.val (sLocalFiniteZetaPhases F S ω v)
  · simp [hv']
  · simp [localFiniteDenominator, hv'] at h

private theorem finiteDenominator_eq_zero_of_mem (ω : Characters F S) {v : S} {z : ℂ}
    (h : v ∈ sLocalFinitePolesAt F S ω z) :
    finiteZetaDenominator F v.val (sLocalFiniteZetaPhases F S ω v) z = 0 := by
  have hu := (Finset.mem_filter.mp (sLocalFinitePolesAt_subset_unramified F S ω z h)).2
  simpa only [localFiniteDenominator, ite_eq_left hu] using (Finset.mem_filter.mp h).2

/-- The number of contributing finite places is at most the field degree
times the number of their distinct rational residue primes. -/
theorem sLocalFinitePolesAt_card_le_residuePrimes_mul_degree (ω : Characters F S) (z : ℂ) :
    (sLocalFinitePolesAt F S ω z).card ≤
      ((sLocalFinitePolesAt F S ω z).image (fun v ↦ finiteResiduePrime F v.val)).card *
        Module.finrank ℚ F := by
  let A := sLocalFinitePolesAt F S ω z
  let f (v : S) := finiteResiduePrime F v.val
  have hsum := Finset.sum_card_fiberwise_eq_card_filter A (A.image f) f
  rw [Finset.filter_true_of_mem (fun v hv ↦ Finset.mem_image_of_mem f hv)] at hsum
  change A.card ≤ (A.image f).card * Module.finrank ℚ F
  rw [← hsum, ← Finset.sum_const_nat (f := fun _ ↦ Module.finrank ℚ F) (fun _ _ ↦ rfl)]
  apply Finset.sum_le_sum
  intro p hp
  obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨_, hv, _, _, _⟩ := finiteResiduePrime_spec F v.val
  letI : Fact (f v).Prime := ⟨hv⟩
  letI : (Ideal.span {(f v : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime (f v)
  apply finitePlaces_card_le_degree_of_liesOver F S _ (p := Ideal.span {(f v : ℤ)})
    (by simpa using hv.ne_zero)
  intro w hw
  obtain ⟨_, _, _, hlie, _⟩ := finiteResiduePrime_spec F w.val
  have he : finiteResiduePrime F w.val = finiteResiduePrime F v.val := (Finset.mem_filter.mp hw).2
  simpa only [he] using hlie

private theorem sLocalFinitePoleCount_residuePrimes_gt (ω : Characters F S) (z : ℂ) (n : ℕ)
    (hfin : n * Module.finrank ℚ F < (sLocalFinitePolesAt F S ω z).card) :
    n < ((sLocalFinitePolesAt F S ω z).image (fun v ↦ finiteResiduePrime F v.val)).card :=
  lt_of_not_ge fun h ↦
    (not_le_of_gt hfin) ((sLocalFinitePolesAt_card_le_residuePrimes_mul_degree F S ω z).trans
      (Nat.mul_le_mul_right _ h))

/-- An excess above the degree with no archimedean contribution requires
two finite places over distinct rational primes. -/
private theorem sLocalPoleCount_excess_two_residue_primes (ω : Characters F S) {z : ℂ}
    (hdegree : Module.finrank ℚ F < sLocalPoleCount F S ω z)
    (harch : sLocalArchPoleCount F S ω z = 0) :
    ∃ v ∈ sLocalFinitePolesAt F S ω z, ∃ w ∈ sLocalFinitePolesAt F S ω z,
      finiteResiduePrime F v.val ≠ finiteResiduePrime F w.val := by
  have hfin : 1 * Module.finrank ℚ F < (sLocalFinitePolesAt F S ω z).card := by
    simpa [sLocalPoleCount, harch] using hdegree
  obtain ⟨p, hp, q, hq, hpq⟩ :=
    Finset.one_lt_card.mp (sLocalFinitePoleCount_residuePrimes_gt F S ω z 1 hfin)
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hq
  exact ⟨v, hv, w, hw, hpq⟩

/-- Above twice the degree, when no infinite place contributes, there must
be three contributing finite places over distinct rational primes. -/
theorem sLocalPoleCount_excess_three_residue_primes (ω : Characters F S) {z : ℂ}
    (hdegree : 2 * Module.finrank ℚ F < sLocalPoleCount F S ω z)
    (harch : sLocalArchPoleCount F S ω z = 0) :
    ∃ v ∈ sLocalFinitePolesAt F S ω z, ∃ w ∈ sLocalFinitePolesAt F S ω z,
      ∃ u ∈ sLocalFinitePolesAt F S ω z,
        finiteResiduePrime F v.val ≠ finiteResiduePrime F w.val ∧
        finiteResiduePrime F v.val ≠ finiteResiduePrime F u.val ∧
        finiteResiduePrime F w.val ≠ finiteResiduePrime F u.val := by
  have hfin : 2 * Module.finrank ℚ F < (sLocalFinitePolesAt F S ω z).card := by
    simpa [sLocalPoleCount, harch] using hdegree
  obtain ⟨p, hp, q, hq, r, hr, hpq, hpr, hqr⟩ :=
    Finset.two_lt_card.mp (sLocalFinitePoleCount_residuePrimes_gt F S ω z 2 hfin)
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hq
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hr
  exact ⟨v, hv, w, hw, u, hu, hpq, hpr, hqr⟩

private theorem sLocalFinitePolesAt_common_subsingleton (ω : Characters F S) (v w : S)
    (hp : finiteResiduePrime F v.val ≠ finiteResiduePrime F w.val) :
    {z | v ∈ sLocalFinitePolesAt F S ω z ∧ w ∈ sLocalFinitePolesAt F S ω z}.Subsingleton := by
  obtain ⟨e, hpv, he, _, hv⟩ := finiteResiduePrime_spec F v.val
  obtain ⟨f, hpw, hf, _, hw⟩ := finiteResiduePrime_spec F w.val
  apply (finiteZetaDenominator_common_zeros_subsingleton F v.val w.val
    (sLocalFiniteZetaPhases F S ω v) (sLocalFiniteZetaPhases F S ω w)
    hpv hpw hp he hf hv hw).anti
  exact fun _ hz => ⟨finiteDenominator_eq_zero_of_mem F S ω hz.1,
    finiteDenominator_eq_zero_of_mem F S ω hz.2⟩

private theorem sLocalRealPole_on_axis (ω : Characters F S) (v : RealPlaces F) {z : ℂ}
    (hre : z.re = 0) (hz : localRealDenominator F S ω v z = 0) :
    z = -(sLocalRealArchParameters F S ω v).1 := by
  obtain ⟨n, hn⟩ := (realArchZetaDenominator_eq_zero_iff _ _).mp hz
  apply Complex.ext
  · simp [hre, sLocalRealArchParameters_re]
  · have h := congrArg Complex.im hn
    simp [Complex.mul_im] at h ⊢
    linarith

private theorem sLocalComplexPole_on_axis (ω : Characters F S) (v : ComplexPlaces F) {z : ℂ}
    (hre : z.re = 0) (hz : localComplexDenominator F S ω v z = 0) :
    z = -(sLocalComplexArchParameters F S ω v).1 := by
  obtain ⟨n, hn⟩ := (complexArchZetaDenominator_eq_zero_iff _ _).mp hz
  apply Complex.ext
  · simp [hre, sLocalComplexArchParameters_re]
  · have h := congrArg Complex.im hn
    simp at h ⊢
    linarith

/-- The exceptional-point bound of Theorem 7.1.3.2(3) on the imaginary axis.
Each archimedean place and each unordered pair of unramified finite places
can supply at most one exceptional point. -/
theorem sLocalPoleCount_exceptional_bound (ω : Characters F S) :
    let U : Finset S := Finset.univ.filter
      (fun v => finiteZetaUnramified F v.val (sLocalFiniteZetaPhases F S ω v))
    ∃ T : Finset ℂ, T.card ≤ Fintype.card (InfinitePlace F) + U.card.choose 2 ∧
      ∀ z : ℂ, Module.finrank ℚ F < sLocalPoleCount F S ω z → z ∈ T := by
  intro U
  let R : Finset ℂ := Finset.univ.image (fun v : RealPlaces F =>
    -(sLocalRealArchParameters F S ω v).1)
  let C : Finset ℂ := Finset.univ.image (fun v : ComplexPlaces F =>
    -(sLocalComplexArchParameters F S ω v).1)
  let candidates (P : Finset S) : Set ℂ := {z | ∃ v ∈ P, ∃ w ∈ P,
    finiteResiduePrime F v.val ≠ finiteResiduePrime F w.val ∧
      v ∈ sLocalFinitePolesAt F S ω z ∧ w ∈ sLocalFinitePolesAt F S ω z}
  let points (P : Finset S) : Finset ℂ :=
    if h : (candidates P).Nonempty then {h.choose} else ∅
  have hpoints (P : Finset S) : (points P).card ≤ 1 := by
    unfold points
    split <;> simp
  have hsub (P : Finset S) (hP : P.card = 2) : (candidates P).Subsingleton := by
    obtain ⟨v, w, hvw, rfl⟩ := Finset.card_eq_two.mp hP
    have hm {z : ℂ} (hz : z ∈ candidates {v, w}) :
        finiteResiduePrime F v.val ≠ finiteResiduePrime F w.val ∧
          v ∈ sLocalFinitePolesAt F S ω z ∧ w ∈ sLocalFinitePolesAt F S ω z := by
      obtain ⟨a, ha, b, hb, hab, haz, hbz⟩ := hz
      have ha' : a = v ∨ a = w := by
        simpa only [Finset.mem_insert, Finset.mem_singleton] using ha
      have hb' : b = v ∨ b = w := by
        simpa only [Finset.mem_insert, Finset.mem_singleton] using hb
      rcases ha' with ha' | ha' <;> rcases hb' with hb' | hb' <;>
        simp only [ha', hb'] at hab haz hbz
      · exact (hab rfl).elim
      · exact ⟨hab, haz, hbz⟩
      · exact ⟨Ne.symm hab, hbz, haz⟩
      · exact (hab rfl).elim
    exact fun _ hx _ hy =>
      sLocalFinitePolesAt_common_subsingleton F S ω v w (hm hx).1 (hm hx).2 (hm hy).2
  let B := (U.powersetCard 2).biUnion points
  refine ⟨(R ∪ C) ∪ B, ?_, ?_⟩
  · have hR : R.card ≤ InfinitePlace.nrRealPlaces F := Finset.card_image_le
    have hC : C.card ≤ InfinitePlace.nrComplexPlaces F := Finset.card_image_le
    have hB : B.card ≤ U.card.choose 2 := by
      simpa [Finset.card_powersetCard] using
        (Finset.card_biUnion_le_card_mul (U.powersetCard 2) points 1 fun P _ => hpoints P)
    rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces]
    exact (Finset.card_union_le _ _).trans
      (add_le_add ((Finset.card_union_le _ _).trans (add_le_add hR hC)) hB)
  · intro z hdegree
    have hz := sLocalPoleCount_excess_on_axis F S ω hdegree
    by_cases hR : ∃ v, localRealDenominator F S ω v z = 0
    · obtain ⟨v, hv⟩ := hR
      exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_image.mpr ⟨v, Finset.mem_univ _, (sLocalRealPole_on_axis F S ω v hz hv).symm⟩))
    by_cases hC : ∃ v, localComplexDenominator F S ω v z = 0
    · obtain ⟨v, hv⟩ := hC
      exact Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨v, Finset.mem_univ _, (sLocalComplexPole_on_axis F S ω v hz hv).symm⟩))
    have harch : sLocalArchPoleCount F S ω z = 0 := by
      classical
      push Not at hR hC
      simp [sLocalArchPoleCount, hR, hC]
    obtain ⟨v, hv, w, hw, hne⟩ := sLocalPoleCount_excess_two_residue_primes F S ω hdegree harch
    let P : Finset S := {v, w}
    have hP : P ∈ U.powersetCard 2 := by
      apply Finset.mem_powersetCard.mpr
      refine ⟨?_, Finset.card_eq_two.mpr ⟨v, w, fun h => hne (congrArg (fun u : S => finiteResiduePrime F u.val) h), rfl⟩⟩
      intro a ha
      rcases Finset.mem_insert.mp ha with rfl | ha
      · exact sLocalFinitePolesAt_subset_unramified F S ω z hv
      · rw [Finset.mem_singleton.mp ha]
        exact sLocalFinitePolesAt_subset_unramified F S ω z hw
    have hzP : z ∈ candidates P := ⟨v, by simp [P], w, by simp [P], hne, hv, hw⟩
    let hnonempty : (candidates P).Nonempty := ⟨z, hzP⟩
    have hz' := hsub P (Finset.mem_powersetCard.mp hP).2 hzP hnonempty.choose_spec
    apply Finset.mem_union_right _
    apply Finset.mem_biUnion.mpr
    refine ⟨P, hP, ?_⟩
    simpa only [points, dite_eq_left hnonempty, Finset.mem_singleton] using hz'

private theorem sLocalZetaWeight_pow_eq_one (ω : Characters F S) {N : ℕ}
    (hω : ω ^ N = 1) (q : SIdeleQuotient F S) :
    sLocalZetaWeight F S ω 0 q ^ N = 1 := by
  let k := ((sLocalZetaSplit F S).symm q).2
  let c : SLocalThetaNormOne F S →ₜ* Circle := ω
  have h := congrArg (fun χ : Characters F S => ((χ k : Circle) : ℂ)) hω
  change ((((c ^ N) k : Circle) : ℂ)) = 1 at h
  rw [ContinuousMonoidHom.pow_apply, Circle.coe_pow] at h
  rw [sLocalZetaWeight, zero_mul, Complex.exp_zero, one_mul]
  change ((c k : Circle) : ℂ) ^ N = 1
  exact h

private theorem exponent_eq_zero_of_exp_pow {a : ℂ} (ha : a.re = 0) {N : ℕ} (hN : 0 < N)
    (h : ∀ t : ℝ, Complex.exp ((t : ℂ) * a) ^ N = 1) : a = 0 := by
  by_contra hne
  have hi : a.im ≠ 0 := fun hz => hne (Complex.ext (by simpa using ha) (by simpa using hz))
  let t : ℝ := Real.pi / ((N : ℝ) * a.im)
  have ht : (N : ℂ) * ((t : ℂ) * a) = Real.pi * Complex.I := by
    apply Complex.ext
    · simp [Complex.mul_re, ha]
    · simp [Complex.mul_im]
      dsimp [t]
      field_simp [hi, (show (N : ℝ) ≠ 0 by positivity)]
  have hh := h t
  rw [← Complex.exp_nat_mul, ht, Complex.exp_pi_mul_I] at hh
  exact (by norm_num : (-1 : ℂ) ≠ 1) hh

/-- Insert a unit at one real place, with every other coordinate equal to one. -/
def sLocalRealUnitIdele (v : RealPlaces F) (u : ℝˣ) : (SAdeles F S)ˣ :=
  sLocalArchZetaInsert F S ((infiniteAdeleUnitsCoordinates F).symm (Pi.mulSingle v u, 1))

/-- A single positive real coordinate of normalized modulus `exp t`. -/
def sLocalRealPositiveIdele (v : RealPlaces F) (t : ℝ) : (SAdeles F S)ˣ :=
  sLocalRealUnitIdele F S v (Units.mk0 (Real.exp t) (Real.exp_pos t).ne')

/-- Evaluation of the S-local character on a single positive real coordinate. -/
theorem sLocalZetaWeight_realPositiveIdele (ω : Characters F S) (v : RealPlaces F)
    (t : ℝ) (z : ℂ) :
    sLocalZetaWeight F S ω z (QuotientGroup.mk (sLocalRealPositiveIdele F S v t)) =
      Complex.exp ((t : ℂ) * (z + (sLocalRealArchParameters F S ω v).1)) := by
  let u : ℝˣ := Units.mk0 (Real.exp t) (Real.exp_pos t).ne'
  let p : (RealPlaces F → ℝˣ) × (ComplexPlaces F → ℂˣ) := (Pi.mulSingle v u, 1)
  let a := (infiniteAdeleUnitsCoordinates F).symm p
  have hprod := sLocalArchZetaWeight_eq_product F S ω z a
  dsimp only at hprod
  rw [ContinuousMulEquiv.apply_symm_apply] at hprod
  have hR : ∏ w : RealPlaces F, sLocalRealArchWeight F S ω w z (p.1 w) =
      sLocalRealArchWeight F S ω v z u := by
    rw [Finset.prod_eq_single v]
    · simp [p]
    · intro w _ hw
      simp [p, Pi.mulSingle_eq_of_ne hw, sLocalRealArchWeight]
    · simp
  rw [hR, show (∏ w : ComplexPlaces F, sLocalComplexArchWeight F S ω w z (p.2 w)) = 1 by
    simp [p, sLocalComplexArchWeight], mul_one] at hprod
  change sLocalZetaWeight F S ω z (QuotientGroup.mk (sLocalArchZetaInsert F S a)) = _
  rw [hprod, sLocalRealArchWeight,
    show ‖(u : ℝ)‖ = Real.exp t by exact Real.norm_of_nonneg (Real.exp_pos t).le,
    ite_eq_right (show ¬ (u : ℝ) < 0 from (Real.exp_pos t).le.not_gt), mul_one,
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos t).ne'),
    ← Complex.ofReal_log (Real.exp_pos t).le, Real.log_exp]

/-- Insert a unit at one complex place, with every other coordinate equal to one. -/
def sLocalComplexUnitIdele (v : ComplexPlaces F) (u : ℂˣ) : (SAdeles F S)ˣ :=
  sLocalArchZetaInsert F S ((infiniteAdeleUnitsCoordinates F).symm (1, Pi.mulSingle v u))

/-- A single positive complex coordinate of normalized modulus `exp t`. -/
def sLocalComplexPositiveIdele (v : ComplexPlaces F) (t : ℝ) : (SAdeles F S)ˣ :=
  sLocalComplexUnitIdele F S v
    (Units.mk0 (Real.exp (t / 2) : ℂ) (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'))

/-- Evaluation of the S-local character on a single positive complex coordinate. -/
theorem sLocalZetaWeight_complexPositiveIdele (ω : Characters F S) (v : ComplexPlaces F)
    (t : ℝ) (z : ℂ) :
    sLocalZetaWeight F S ω z (QuotientGroup.mk (sLocalComplexPositiveIdele F S v t)) =
      Complex.exp ((t : ℂ) * (z + (sLocalComplexArchParameters F S ω v).1)) := by
  have ht : 0 < Real.exp (t / 2) := Real.exp_pos _
  let u : ℂˣ := Units.mk0 (Real.exp (t / 2) : ℂ) (Complex.ofReal_ne_zero.mpr ht.ne')
  let p : (RealPlaces F → ℝˣ) × (ComplexPlaces F → ℂˣ) := (1, Pi.mulSingle v u)
  let a := (infiniteAdeleUnitsCoordinates F).symm p
  have hprod := sLocalArchZetaWeight_eq_product F S ω z a
  dsimp only at hprod
  rw [ContinuousMulEquiv.apply_symm_apply] at hprod
  have hC : ∏ w : ComplexPlaces F, sLocalComplexArchWeight F S ω w z (p.2 w) =
      sLocalComplexArchWeight F S ω v z u := by
    rw [Finset.prod_eq_single v]
    · simp [p]
    · intro w _ hw
      simp [p, Pi.mulSingle_eq_of_ne hw, sLocalComplexArchWeight]
    · simp
  rw [hC, show (∏ w : RealPlaces F, sLocalRealArchWeight F S ω w z (p.1 w)) = 1 by
    simp [p, sLocalRealArchWeight], one_mul] at hprod
  have hu : ‖(u : ℂ)‖ = Real.exp (t / 2) := by
    change ‖(Real.exp (t / 2) : ℂ)‖ = _
    rw [Complex.norm_real, Real.norm_of_nonneg ht.le]
  have hu₂ : ‖(u : ℂ)‖ ^ 2 = Real.exp t := by
    rw [hu, pow_two, ← Real.exp_add]
    ring_nf
  have hangle : (u : ℂ) / (‖(u : ℂ)‖ : ℂ) = 1 := by
    rw [hu]
    exact div_self (Complex.ofReal_ne_zero.mpr ht.ne')
  change sLocalZetaWeight F S ω z (QuotientGroup.mk (sLocalArchZetaInsert F S a)) = _
  rw [hprod, sLocalComplexArchWeight, hangle, one_zpow, mul_one, hu₂,
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos t).ne'),
    ← Complex.ofReal_log (Real.exp_pos t).le, Real.log_exp]

private theorem sLocalRealArchParameters_finiteOrder_shift (ω : Characters F S) {N : ℕ}
    (hN : 0 < N) (hω : ω ^ N = 1) (v : RealPlaces F) :
    (sLocalRealArchParameters F S ω v).1 = 0 := by
  apply exponent_eq_zero_of_exp_pow (sLocalRealArchParameters_re F S ω v) hN
  intro t
  simpa only [sLocalZetaWeight_realPositiveIdele, zero_add] using
    sLocalZetaWeight_pow_eq_one F S ω hω (QuotientGroup.mk (sLocalRealPositiveIdele F S v t))

private theorem sLocalComplexArchParameters_finiteOrder_shift (ω : Characters F S) {N : ℕ}
    (hN : 0 < N) (hω : ω ^ N = 1) (v : ComplexPlaces F) :
    (sLocalComplexArchParameters F S ω v).1 = 0 := by
  apply exponent_eq_zero_of_exp_pow (sLocalComplexArchParameters_re F S ω v) hN
  intro t
  simpa only [sLocalZetaWeight_complexPositiveIdele, zero_add] using
    sLocalZetaWeight_pow_eq_one F S ω hω (QuotientGroup.mk (sLocalComplexPositiveIdele F S v t))

private theorem sLocalFiniteDenominator_normPower (ω : Characters F S) {v : S} {z : ℂ}
    (hv : v ∈ sLocalFinitePolesAt F S ω z) :
    (v.val.asIdeal.absNorm : ℂ) ^ z =
      (sLocalFiniteZetaPhases F S ω v (chosenFiniteUniformizer F v.val) : ℂ) := by
  let q := v.val.asIdeal.absNorm
  have hq : (0 : ℝ) < (q : ℝ) := zero_lt_one.trans
    (by exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v.val)
  have hn : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have he : (q : ℂ) ^ (-z) = Complex.exp (-z * (Real.log (q : ℝ) : ℂ)) := by
    rw [Complex.cpow_def_of_ne_zero hn, ← Complex.ofReal_natCast,
      ← Complex.ofReal_log hq.le, mul_comm]
  have h := sub_eq_zero.mp (finiteDenominator_eq_zero_of_mem F S ω hv)
  change 1 = _ * Complex.exp (-z * (Real.log (q : ℝ) : ℂ)) at h
  rw [← he, Complex.cpow_neg] at h
  have hne : (q : ℂ) ^ z ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hn)
  simpa only [one_mul] using (eq_mul_inv_iff_mul_eq₀ hne).mp h

/-- The finite algebraic data of a norm twist are the coefficients on the
unramified local uniformizers after removing that twist. -/
def sLocalAlgebraicUniformizerValues (ω : Characters F S) (s₀ : ℂ) : Prop :=
  ∀ v : S, finiteZetaUnramified F v.val (sLocalFiniteZetaPhases F S ω v) →
    IsAlgebraic ℚ ((sLocalFiniteZetaPhases F S ω v (chosenFiniteUniformizer F v.val) : ℂ) *
      (v.val.asIdeal.absNorm : ℂ) ^ s₀)

/-- The norm-twist factorization on the S-local quotient supplies the
algebraic uniformizer values required for the pole bounds. -/
theorem sLocalAlgebraicUniformizerValues_of_normTwist (ω : Characters F S) (s₀ : ℂ)
    (χ₀ : SIdeleQuotient F S → ℂ)
    (htwist : ∀ g, sLocalZetaWeight F S ω 0 g = χ₀ g * (sLocalClassModulus F S g : ℂ) ^ s₀)
    (hA : ∀ v : S, finiteZetaUnramified F v.val (sLocalFiniteZetaPhases F S ω v) →
      IsAlgebraic ℚ (χ₀ (QuotientGroup.mk (sLocalFiniteZetaInsert F S v
        (chosenFiniteUniformizer F v.val))))) :
    sLocalAlgebraicUniformizerValues F S ω s₀ := by
  intro v hv
  let g : SIdeleQuotient F S := QuotientGroup.mk
    (sLocalFiniteZetaInsert F S v (chosenFiniteUniformizer F v.val))
  let q := v.val.asIdeal.absNorm
  have hq : (q : ℂ) ≠ 0 := by
    exact_mod_cast (zero_lt_one.trans (NumberField.HeightOneSpectrum.one_lt_absNorm v.val)).ne'
  have hpow : (q : ℂ) ^ s₀ ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hq)
  have hn : sLocalClassModulus F S g = (q : ℝ)⁻¹ := by
    rw [show g = QuotientGroup.mk (sLocalFiniteZetaInsert F S v
      (chosenFiniteUniformizer F v.val)) from rfl, sLocalClassModulus_mk,
      sLocalFiniteZetaInsert_norm, norm_finiteUniformizer F v.val _
        (chosenFiniteUniformizer_spec F v.val)]
  change IsAlgebraic ℚ (sLocalZetaWeight F S ω 0 g * (q : ℂ) ^ s₀)
  rw [htwist g, hn, Complex.ofReal_inv, Complex.inv_cpow_ofReal_nonneg (Nat.cast_nonneg q),
    Complex.ofReal_natCast, mul_assoc, inv_mul_cancel₀ hpow, mul_one]
  exact hA v hv

private theorem positiveIdele_modulus_of_weight (ω : Characters F S)
    (g : (SAdeles F S)ˣ) {t : ℝ} {a : ℂ} (ha : a.re = 0)
    (h : ∀ z, sLocalZetaWeight F S ω z (QuotientGroup.mk g) =
      Complex.exp ((t : ℂ) * (z + a))) :
    sLocalClassModulus F S (QuotientGroup.mk g) = Real.exp t := by
  let q : SIdeleQuotient F S := QuotientGroup.mk g
  have he := norm_sLocalZetaWeight_mk F S ω (1 : ℂ) g
  rw [← sLocalClassModulus_mk F S g, Complex.one_re, one_mul,
    Real.exp_log (sLocalClassModulus_pos F S q), h 1, Complex.norm_exp] at he
  change Real.exp _ = sLocalClassModulus F S q at he
  change sLocalClassModulus F S q = Real.exp t
  simpa only [Complex.mul_re, Complex.ofReal_re, Complex.add_re, Complex.one_re, ha,
    add_zero, Complex.ofReal_im, zero_mul, sub_zero, mul_one] using he.symm

theorem sLocalRealPositiveIdele_modulus (ω : Characters F S) (v : RealPlaces F) (t : ℝ) :
    sLocalClassModulus F S (QuotientGroup.mk (sLocalRealPositiveIdele F S v t)) = Real.exp t :=
  positiveIdele_modulus_of_weight F S ω _ (sLocalRealArchParameters_re F S ω v)
    (sLocalZetaWeight_realPositiveIdele F S ω v t)

theorem sLocalComplexPositiveIdele_modulus (ω : Characters F S) (v : ComplexPlaces F) (t : ℝ) :
    sLocalClassModulus F S (QuotientGroup.mk (sLocalComplexPositiveIdele F S v t)) = Real.exp t :=
  positiveIdele_modulus_of_weight F S ω _ (sLocalComplexArchParameters_re F S ω v)
    (sLocalZetaWeight_complexPositiveIdele F S ω v t)

/-- The radial part of an integral infinity type. At a complex place the
positive scalar is `exp (t/2)` because the local modulus is the square of
the complex norm. The two angular exponents therefore add and are halved. -/
def sLocalIntegralRadialInfinityType (χ₀ : SIdeleQuotient F S → ℂ) : Prop :=
  (∀ v : RealPlaces F, ∃ m : ℤ, ∀ t : ℝ,
    χ₀ (QuotientGroup.mk (sLocalRealPositiveIdele F S v t)) =
      Complex.exp ((t : ℂ) * (m : ℂ))) ∧
  (∀ v : ComplexPlaces F, ∃ m n : ℤ, ∀ t : ℝ,
    χ₀ (QuotientGroup.mk (sLocalComplexPositiveIdele F S v t)) =
      Complex.exp ((t : ℂ) * (((m + n : ℤ) : ℂ) / 2)))

/-- Integral monomials for the infinity type of an S-local character. The
real place can also carry a sign character. -/
def sLocalIntegralInfinityType (χ₀ : SIdeleQuotient F S → ℂ) : Prop :=
  (∀ v : RealPlaces F, ∃ (m : ℤ) (ε : ℕ), ∀ u : ℝˣ,
    χ₀ (QuotientGroup.mk (sLocalRealUnitIdele F S v u)) =
      ((|(u : ℝ)| : ℝ) : ℂ) ^ m * (if (u : ℝ) < 0 then (-1 : ℂ) ^ ε else 1)) ∧
  (∀ v : ComplexPlaces F, ∃ m n : ℤ, ∀ u : ℂˣ,
    χ₀ (QuotientGroup.mk (sLocalComplexUnitIdele F S v u)) =
      (u : ℂ) ^ m * (star (u : ℂ)) ^ n)

theorem sLocalIntegralInfinityType_radial {χ₀ : SIdeleQuotient F S → ℂ}
    (h : sLocalIntegralInfinityType F S χ₀) : sLocalIntegralRadialInfinityType F S χ₀ := by
  have hExp (t : ℝ) (m : ℤ) : (Real.exp t : ℂ) ^ m = Complex.exp ((t : ℂ) * (m : ℂ)) := by
    rw [Complex.ofReal_exp, mul_comm, Complex.exp_int_mul]
  constructor
  · intro v
    obtain ⟨m, ε, hg⟩ := h.1 v
    refine ⟨m, fun t ↦ ?_⟩
    rw [sLocalRealPositiveIdele, hg]
    change ((|Real.exp t| : ℝ) : ℂ) ^ m * (if Real.exp t < 0 then (-1 : ℂ) ^ ε else 1) = _
    rw [abs_of_pos (Real.exp_pos t), ite_eq_right (Real.exp_pos t).le.not_gt, mul_one, hExp]
  · intro v
    obtain ⟨m, n, hg⟩ := h.2 v
    refine ⟨m, n, fun t ↦ ?_⟩
    rw [sLocalComplexPositiveIdele, hg]
    change (Real.exp (t / 2) : ℂ) ^ m * (star (Real.exp (t / 2) : ℂ)) ^ n = _
    rw [Complex.star_def, Complex.conj_ofReal, hExp, hExp, ← Complex.exp_add]
    congr 1
    push_cast
    ring

private theorem complex_exponent_eq_of_exp {a b : ℂ}
    (h : ∀ t : ℝ, Complex.exp ((t : ℂ) * a) = Complex.exp ((t : ℂ) * b)) : a = b := by
  have hd (s : ℂ) : HasDerivAt (fun t : ℝ ↦ Complex.exp ((t : ℂ) * s)) s 0 := by
    simpa using ((Complex.ofRealCLM.hasFDerivAt (x := (0 : ℝ))).hasDerivAt.mul_const s).cexp
  exact (hd a).unique ((funext h).symm ▸ hd b)

private theorem positiveIdele_exponent_of_normTwist (ω : Characters F S)
    (χ₀ : SIdeleQuotient F S → ℂ) {s₀ a b : ℂ} (g : ℝ → SIdeleQuotient F S)
    (htwist : ∀ q, sLocalZetaWeight F S ω 0 q =
      χ₀ q * (sLocalClassModulus F S q : ℂ) ^ s₀)
    (hmod : ∀ t, sLocalClassModulus F S (g t) = Real.exp t)
    (hbase : ∀ t, sLocalZetaWeight F S ω 0 (g t) = Complex.exp ((t : ℂ) * a))
    (halg : ∀ t, χ₀ (g t) = Complex.exp ((t : ℂ) * b)) :
    a = b + s₀ := by
  apply complex_exponent_eq_of_exp
  intro t
  have he := htwist (g t)
  rw [hbase, halg, hmod, Complex.cpow_def_of_ne_zero
      (Complex.ofReal_ne_zero.mpr (Real.exp_pos t).ne'), ← Complex.ofReal_log (Real.exp_pos t).le,
    Real.log_exp, ← Complex.exp_add] at he
  rwa [← mul_add] at he

/-- In a norm twist of a character with integral infinity type, each
archimedean exponent has the twist's imaginary part. -/
theorem sLocalArchParameters_im_of_integralRadialInfinityType (ω : Characters F S)
    (χ₀ : SIdeleQuotient F S → ℂ) (s₀ : ℂ)
    (htwist : ∀ q, sLocalZetaWeight F S ω 0 q =
      χ₀ q * (sLocalClassModulus F S q : ℂ) ^ s₀)
    (hinfty : sLocalIntegralRadialInfinityType F S χ₀) :
    (∀ v, (sLocalRealArchParameters F S ω v).1.im = s₀.im) ∧
    (∀ v, (sLocalComplexArchParameters F S ω v).1.im = s₀.im) := by
  constructor
  · intro v
    obtain ⟨m, hm⟩ := hinfty.1 v
    have ha := positiveIdele_exponent_of_normTwist F S ω χ₀
      (fun t ↦ QuotientGroup.mk (sLocalRealPositiveIdele F S v t)) htwist
      (sLocalRealPositiveIdele_modulus F S ω v)
      (fun t ↦ by simpa only [zero_add] using sLocalZetaWeight_realPositiveIdele F S ω v t 0) hm
    simpa using congrArg Complex.im ha
  · intro v
    obtain ⟨m, n, hmn⟩ := hinfty.2 v
    have ha := positiveIdele_exponent_of_normTwist F S ω χ₀
      (fun t ↦ QuotientGroup.mk (sLocalComplexPositiveIdele F S v t)) htwist
      (sLocalComplexPositiveIdele_modulus F S ω v)
      (fun t ↦ by simpa only [zero_add] using sLocalZetaWeight_complexPositiveIdele F S ω v t 0) hmn
    simpa [Complex.div_ofNat_im] using congrArg Complex.im ha

private theorem sLocalFinitePole_normPower_algebraic (ω : Characters F S) {s₀ z : ℂ}
    (hA : sLocalAlgebraicUniformizerValues F S ω s₀)
    {v : S} (hv : v ∈ sLocalFinitePolesAt F S ω z) :
    IsAlgebraic ℚ ((v.val.asIdeal.absNorm : ℂ) ^ (z + s₀)) := by
  have hq : (v.val.asIdeal.absNorm : ℂ) ≠ 0 := by
    exact_mod_cast (zero_lt_one.trans (NumberField.HeightOneSpectrum.one_lt_absNorm v.val)).ne'
  have hU := (Finset.mem_filter.mp (sLocalFinitePolesAt_subset_unramified F S ω z hv)).2
  rw [Complex.cpow_add _ _ hq, sLocalFiniteDenominator_normPower F S ω hv]
  exact hA v hU

private theorem spectralParameter_eq_neg_imaginary_twist {z s₀ : ℂ}
    (hre : z.re = 0) (him : (z + s₀).im = 0) : z = -(s₀.im : ℂ) * Complex.I := by
  apply Complex.ext
  · simpa [Complex.mul_re] using hre
  · simpa [Complex.add_im, Complex.mul_im] using eq_neg_of_add_eq_zero_left him

/-- The Schanuel clause of Theorem 7.1.3.2(3)(b) on the actual S-local
component. Excess order can occur only at the translated center or an
archimedean pole on the imaginary axis. -/
theorem sLocalPoleCount_excess_of_schanuel (hS : SchanuelConjecture)
    (ω : Characters F S) (s₀ : ℂ) (hA : sLocalAlgebraicUniformizerValues F S ω s₀)
    {z : ℂ} (hdegree : Module.finrank ℚ F < sLocalPoleCount F S ω z) :
    z.re = 0 ∧ (0 < sLocalArchPoleCount F S ω z ∨ z = -(s₀.im : ℂ) * Complex.I) := by
  have hre := sLocalPoleCount_excess_on_axis F S ω hdegree
  refine ⟨hre, ?_⟩
  by_cases harch : sLocalArchPoleCount F S ω z = 0
  · right
    obtain ⟨v, hv, w, hw, hne⟩ := sLocalPoleCount_excess_two_residue_primes F S ω hdegree harch
    obtain ⟨e, hp, he, _, hNv⟩ := finiteResiduePrime_spec F v.val
    obtain ⟨f, hq, hf, _, hNw⟩ := finiteResiduePrime_spec F w.val
    apply spectralParameter_eq_neg_imaginary_twist hre
    exact primePower_exponents_im_eq_zero_of_schanuel hS hp hq hne he hf
      (hNv ▸ sLocalFinitePole_normPower_algebraic F S ω hA hv)
      (hNw ▸ sLocalFinitePole_normPower_algebraic F S ω hA hw)
  · exact Or.inl (Nat.pos_of_ne_zero harch)

/-- The reduction of the twice-degree bound to the classical Six Exponentials
Theorem. The common imaginary shift of the archimedean parameters ensures that
all their possible axis poles are at the designated center. -/
theorem sLocalPoleCount_excess_of_sixExponentials (hSix : SixExponentialsTheorem)
    (ω : Characters F S) (s₀ : ℂ) (hA : sLocalAlgebraicUniformizerValues F S ω s₀)
    (hR : ∀ v, (sLocalRealArchParameters F S ω v).1.im = s₀.im)
    (hC : ∀ v, (sLocalComplexArchParameters F S ω v).1.im = s₀.im)
    {z : ℂ} (hdegree : 2 * Module.finrank ℚ F < sLocalPoleCount F S ω z) :
    z = -(s₀.im : ℂ) * Complex.I := by
  have hre := sLocalPoleCount_excess_on_axis F S ω (z := z) (by omega)
  by_contra hz
  have hreal (v : RealPlaces F) : localRealDenominator F S ω v z ≠ 0 := by
    intro h
    apply hz
    apply spectralParameter_eq_neg_imaginary_twist hre
    simp [sLocalRealPole_on_axis F S ω v hre h, hR]
  have hcomplex (v : ComplexPlaces F) : localComplexDenominator F S ω v z ≠ 0 := by
    intro h
    apply hz
    apply spectralParameter_eq_neg_imaginary_twist hre
    simp [sLocalComplexPole_on_axis F S ω v hre h, hC]
  have harch : sLocalArchPoleCount F S ω z = 0 := by
    simp [sLocalArchPoleCount, hreal, hcomplex]
  obtain ⟨v, hv, w, hw, u, hu, hvw, hvu, hwu⟩ :=
    sLocalPoleCount_excess_three_residue_primes F S ω hdegree harch
  let V : Fin 3 → S := ![v, w, u]
  let p (i : Fin 3) := finiteResiduePrime F (V i).val
  have hinj : Injective p := by
    intro i j h
    fin_cases i <;> fin_cases j <;>
      simp_all [p, V]
  have hmem (i : Fin 3) : V i ∈ sLocalFinitePolesAt F S ω z := by
    fin_cases i
    · exact hv
    · exact hw
    · exact hu
  choose e hspec using fun i : Fin 3 ↦ finiteResiduePrime_spec F (V i).val
  apply hz
  apply spectralParameter_eq_neg_imaginary_twist hre
  apply primePower_exponents_im_eq_zero_of_sixExponentials hSix p e
    (fun i ↦ (hspec i).1) (fun i ↦ (hspec i).2.1) hinj
  intro i
  rw [← (hspec i).2.2.2]
  exact sLocalFinitePole_normPower_algebraic F S ω hA (hmem i)

/-- The Schanuel bound for the meromorphic S-local Tate ratio. -/
theorem sLocalExplicitTateFactor_excess_of_schanuel (hS : SchanuelConjecture)
    (ω : Characters F S) (s₀ : ℂ) (hA : sLocalAlgebraicUniformizerValues F S ω s₀)
    (ε : ℂ → ℂ) (hε : ∀ z, AnalyticAt ℂ ε z) (hε₀ : ∀ z, ε z ≠ 0)
    {z : ℂ} (horder : meromorphicOrderAt (sLocalExplicitTateFactor F S ω ε) z <
      -(Module.finrank ℚ F : WithTop ℤ)) :
    z.re = 0 ∧ (0 < sLocalArchPoleCount F S ω z ∨ z = -(s₀.im : ℂ) * Complex.I) :=
  sLocalPoleCount_excess_of_schanuel F S hS ω s₀ hA
    ((sLocalExplicitTateFactor_order_lt_neg_iff F S ω ε hε hε₀ z
      (Module.finrank ℚ F)).mp horder)

/-- The twice-degree bound for the meromorphic S-local Tate ratio, reduced
to the classical Six Exponentials Theorem. -/
theorem sLocalExplicitTateFactor_excess_of_sixExponentials (hSix : SixExponentialsTheorem)
    (ω : Characters F S) (s₀ : ℂ) (hA : sLocalAlgebraicUniformizerValues F S ω s₀)
    (hR : ∀ v, (sLocalRealArchParameters F S ω v).1.im = s₀.im)
    (hC : ∀ v, (sLocalComplexArchParameters F S ω v).1.im = s₀.im)
    (ε : ℂ → ℂ) (hε : ∀ z, AnalyticAt ℂ ε z) (hε₀ : ∀ z, ε z ≠ 0)
    {z : ℂ} (horder : meromorphicOrderAt (sLocalExplicitTateFactor F S ω ε) z <
      -((2 * Module.finrank ℚ F : ℕ) : WithTop ℤ)) :
    z = -(s₀.im : ℂ) * Complex.I :=
  sLocalPoleCount_excess_of_sixExponentials F S hSix ω s₀ hA hR hC
    ((sLocalExplicitTateFactor_order_lt_neg_iff F S ω ε hε hε₀ z
      (2 * Module.finrank ℚ F)).mp horder)

/-- Both algebraic-character bounds for the meromorphic Tate ratio in
Theorem 7.1.3.2(3)(b) in the S-local norm-twist chart. The ordinary local
monomials determine the common archimedean shift. -/
theorem sLocalExplicitTateFactor_algebraicNormTwist_bounds
    (ω : Characters F S) (χ₀ : SIdeleQuotient F S → ℂ) (s₀ : ℂ)
    (htwist : ∀ g, sLocalZetaWeight F S ω 0 g = χ₀ g * (sLocalClassModulus F S g : ℂ) ^ s₀)
    (hinfty : sLocalIntegralInfinityType F S χ₀)
    (hfinite : ∀ v : S, finiteZetaUnramified F v.val (sLocalFiniteZetaPhases F S ω v) →
      IsAlgebraic ℚ (χ₀ (QuotientGroup.mk (sLocalFiniteZetaInsert F S v
        (chosenFiniteUniformizer F v.val)))))
    (ε : ℂ → ℂ) (hε : ∀ z, AnalyticAt ℂ ε z) (hε₀ : ∀ z, ε z ≠ 0) :
    (SchanuelConjecture → ∀ z,
      meromorphicOrderAt (sLocalExplicitTateFactor F S ω ε) z <
        -(Module.finrank ℚ F : WithTop ℤ) →
      z.re = 0 ∧ (0 < sLocalArchPoleCount F S ω z ∨ z = -(s₀.im : ℂ) * Complex.I)) ∧
    (SixExponentialsTheorem → ∀ z,
      meromorphicOrderAt (sLocalExplicitTateFactor F S ω ε) z <
        -((2 * Module.finrank ℚ F : ℕ) : WithTop ℤ) →
      z = -(s₀.im : ℂ) * Complex.I) := by
  have hA := sLocalAlgebraicUniformizerValues_of_normTwist F S ω s₀ χ₀ htwist hfinite
  obtain ⟨hR, hC⟩ := sLocalArchParameters_im_of_integralRadialInfinityType F S ω χ₀ s₀
    htwist (sLocalIntegralInfinityType_radial F S hinfty)
  constructor
  · intro hS z hz
    exact sLocalExplicitTateFactor_excess_of_schanuel F S hS ω s₀ hA ε hε hε₀ hz
  · intro hSix z hz
    exact sLocalExplicitTateFactor_excess_of_sixExponentials F S hSix ω s₀ hA hR hC ε hε hε₀ hz

/-- For a finite-order unitary base character an excess over the field degree
on the imaginary axis is possible only at zero. -/
theorem sLocalPoleCount_excess_finiteOrder (ω : Characters F S) {N : ℕ}
    (hN : 0 < N) (hω : ω ^ N = 1) {z : ℂ}
    (hdegree : Module.finrank ℚ F < sLocalPoleCount F S ω z) : z = 0 := by
  have hz := sLocalPoleCount_excess_on_axis F S ω hdegree
  by_cases hR : ∃ v, localRealDenominator F S ω v z = 0
  · obtain ⟨v, hv⟩ := hR
    simpa [sLocalRealArchParameters_finiteOrder_shift F S ω hN hω v] using
      sLocalRealPole_on_axis F S ω v hz hv
  by_cases hC : ∃ v, localComplexDenominator F S ω v z = 0
  · obtain ⟨v, hv⟩ := hC
    simpa [sLocalComplexArchParameters_finiteOrder_shift F S ω hN hω v] using
      sLocalComplexPole_on_axis F S ω v hz hv
  have harch : sLocalArchPoleCount F S ω z = 0 := by
    push Not at hR hC
    simp [sLocalArchPoleCount, hR, hC]
  obtain ⟨v, hv, w, hw, hpq⟩ := sLocalPoleCount_excess_two_residue_primes F S ω hdegree harch
  obtain ⟨e, hp, he, _, hvnorm⟩ := finiteResiduePrime_spec F v.val
  obtain ⟨f, hq, hf, _, hwnorm⟩ := finiteResiduePrime_spec F w.val
  have hpow (a : S) : (sLocalFiniteZetaPhases F S ω a (chosenFiniteUniformizer F a.val)) ^ N = 1 := by
    apply Subtype.ext
    change (sLocalZetaWeight F S ω 0
      (QuotientGroup.mk (sLocalFiniteZetaInsert F S a (chosenFiniteUniformizer F a.val)))) ^ N = 1
    exact sLocalZetaWeight_pow_eq_one F S ω hω _
  exact finiteZetaDenominator_common_zero_of_finite_order F v.val w.val
    (sLocalFiniteZetaPhases F S ω v) (sLocalFiniteZetaPhases F S ω w)
    hp hq hpq he hf hvnorm hwnorm hN (hpow v) (hpow w)
    (finiteDenominator_eq_zero_of_mem F S ω hv) (finiteDenominator_eq_zero_of_mem F S ω hw)

/-- In a chart translated by an imaginary norm twist, the unique possible
excess for a finite-order base moves by the negative of that twist. -/
theorem sLocalPoleCount_excess_finiteOrder_translate (ω : Characters F S) {N : ℕ}
    (hN : 0 < N) (hω : ω ^ N = 1) (x : ℝ) {z : ℂ}
    (hdegree : Module.finrank ℚ F < sLocalPoleCount F S ω (z + (x : ℂ) * Complex.I)) :
    z = -((x : ℂ) * Complex.I) :=
  eq_neg_of_add_eq_zero_left (sLocalPoleCount_excess_finiteOrder F S ω hN hω hdegree)

/-- The angular mode two already refutes the printed plus sign at the
nonpositive candidate zero, since its actual pole lattice starts at minus one. -/
theorem printed_complexEulerPole_zero_obstruction :
    complexArchZetaDenominator 2 0 ≠ 0 := by
  intro h
  obtain ⟨n, hn⟩ := (complexArchZetaDenominator_eq_zero_iff 2 0).mp h
  have hre := congrArg Complex.re hn
  norm_num [Complex.sub_re, Complex.neg_re, Complex.div_ofNat_re] at hre
  linarith [Nat.cast_nonneg (α := ℝ) n]

end

end Masullo
