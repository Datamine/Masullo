import GlobalHeckeEulerComparison
import SLocalEulerPoles
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Analysis.Complex.LocallyUniformLimit

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical NumberField

namespace Masullo

noncomputable section

private theorem exp_neg_log_one_sub {u : ℂ} (hu : ‖u‖ < 1) :
    Complex.exp (-Complex.log (1-u)) = (1-u)⁻¹ := by
  have hn : 1 - u ≠ 0 := by
    intro he
    rw [← sub_eq_zero.mp he, norm_one] at hu
    exact (lt_irrefl _ hu)
  rw [Complex.exp_neg, Complex.exp_log hn]

-- This Taylor-series argument uses the local positivity calculation in
-- Mathlib.NumberTheory.LSeries.Nonvanishing.
private def radialEulerLog (a : ℝ) (z w : ℂ) : ℝ :=
  3 * (-Complex.log (1 - a)).re + 4 * (-Complex.log (1 - a * z)).re +
    (-Complex.log (1 - a * w)).re

private theorem radialEulerLog_hasSum {a : ℝ} (ha₀ : 0 ≤ a) (ha₁ : a < 1)
    {z w : ℂ} (hz : ‖z‖ ≤ 1) (hw : ‖w‖ ≤ 1) :
    HasSum (fun n : ℕ ↦ a ^ n * (3 + 4 * (z ^ n).re + (w ^ n).re) / n)
      (radialEulerLog a z w) := by
  open Complex in
  have hac : ‖(a : ℂ)‖ < 1 := by simpa only [Complex.norm_of_nonneg ha₀] using ha₁
  have hmul (u : ℂ) (hu : ‖u‖ ≤ 1) : ‖(a : ℂ) * u‖ < 1 := by
    rw [norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) hu).trans_lt hac
  refine (((Complex.hasSum_re (Complex.hasSum_taylorSeries_neg_log hac)).mul_left 3).add
    ((Complex.hasSum_re (Complex.hasSum_taylorSeries_neg_log (hmul z hz))).mul_left 4) |>.add
    (Complex.hasSum_re (Complex.hasSum_taylorSeries_neg_log (hmul w hw)))).congr_fun ?_
  intro n
  simp only [← Complex.ofReal_pow, mul_pow, Complex.div_natCast_re, Complex.ofReal_re,
    Complex.mul_re, Complex.ofReal_im, zero_mul, sub_zero]
  ring

private theorem radialEuler_coefficient_nonneg {z w : ℂ} (hw : ‖w‖ ≤ 1)
    (h : z = 0 ∨ ‖z‖ = 1 ∧ w = z ^ 2) {n : ℕ} (hn : 0 < n) :
    0 ≤ 3 + 4 * (z ^ n).re + (w ^ n).re := by
  rcases h with rfl | ⟨hz, rfl⟩
  · simp only [zero_pow hn.ne', Complex.zero_re, mul_zero, add_zero]
    have h := (neg_le_abs (w ^ n).re).trans (Complex.abs_re_le_norm (w ^ n))
    rw [norm_pow] at h
    linarith [pow_le_one₀ (norm_nonneg w) hw (n := n)]
  · have hnorm : ‖z ^ n‖ = 1 := by rw [norm_pow, hz, one_pow]
    rw [pow_right_comm, sq, Complex.mul_re, ← sq, ← sq, ← Complex.sq_norm_sub_sq_re, hnorm]
    nlinarith [sq_nonneg ((z ^ n).re + 1)]

private theorem norm_radialEuler_eq_exp {a : ℝ} (ha₀ : 0 ≤ a) (ha₁ : a < 1) (z w : ℂ)
    (hz : ‖z‖ ≤ 1) (hw : ‖w‖ ≤ 1) :
    ‖((1 - a : ℂ)⁻¹)^3 * ((1 - a*z)⁻¹)^4 * (1 - a*w)⁻¹‖ =
      Real.exp (radialEulerLog a z w) := by
  have hac : ‖(a : ℂ)‖ < 1 := by simpa only [Complex.norm_of_nonneg ha₀] using ha₁
  have hmul (u : ℂ) (hu : ‖u‖ ≤ 1) : ‖(a : ℂ) * u‖ < 1 := by
    rw [norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) hu).trans_lt hac
  rw [← exp_neg_log_one_sub hac, ← exp_neg_log_one_sub (hmul z hz), ← exp_neg_log_one_sub (hmul w hw),
    ← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add, ← Complex.exp_add,
    Complex.norm_exp]
  simp [radialEulerLog, Complex.mul_re, Complex.add_re]

private theorem norm_radialEuler_mono {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b < 1)
    {z w : ℂ} (hw : ‖w‖ ≤ 1) (h : z = 0 ∨ ‖z‖ = 1 ∧ w = z ^ 2) :
    ‖((1 - a : ℂ)⁻¹)^3 * ((1 - a*z)⁻¹)^4 * (1 - a*w)⁻¹‖ ≤
      ‖((1 - b : ℂ)⁻¹)^3 * ((1 - b*z)⁻¹)^4 * (1 - b*w)⁻¹‖ := by
  have hz : ‖z‖ ≤ 1 := by rcases h with rfl | ⟨hz, _⟩ <;> simp [*]
  rw [norm_radialEuler_eq_exp ha (hab.trans_lt hb) z w hz hw,
    norm_radialEuler_eq_exp (ha.trans hab) hb z w hz hw]
  apply Real.exp_le_exp.mpr
  have h₁ := radialEulerLog_hasSum ha (hab.trans_lt hb) hz hw
  have h₂ := radialEulerLog_hasSum (ha.trans hab) hb hz hw
  rw [← h₁.tsum_eq, ← h₂.tsum_eq]
  refine h₁.summable.tsum_le_tsum (fun n ↦ ?_) h₂.summable
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  · exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha hab n) (radialEuler_coefficient_nonneg hw h hn))
      (Nat.cast_nonneg n)

private theorem norm_euler_factor_combination {a : ℝ} (ha₀ : 0 ≤ a) (ha₁ : a < 1)
    (z w : ℂ) (hw : ‖w‖ ≤ 1)
    (h : z = 0 ∨ ‖z‖ = 1 ∧ w = z ^ 2) :
    1 ≤ ‖((1 - a : ℂ)⁻¹)^3 * ((1 - a*z)⁻¹)^4 * (1 - a*w)⁻¹‖ := by
  simpa only [Complex.ofReal_zero, zero_mul, sub_zero, inv_one, one_pow, one_mul, norm_one] using
    norm_radialEuler_mono (a := 0) le_rfl ha₀ ha₁ hw h

variable (F : Type*) [Field F] [NumberField F]

private abbrev K := normOneIdeleClass F
private abbrev Place := HeightOneSpectrum (𝓞 F)
private abbrev coeff (ω : PontryaginDual (K F)) :=
  heckeEulerCoefficient F (normOneEulerCharacter F ω) (chosenFiniteUniformizer F)
private abbrev factor (ω : PontryaginDual (K F)) := heckeEulerFactor F (coeff F ω)

private theorem normOneEulerCharacter_sq_apply (ω : PontryaginDual (K F)) (g : IdeleClass F) :
    normOneEulerCharacter F (ω ^ 2) g = normOneEulerCharacter F ω g ^ 2 := by
  let k := (ideleClassSplit F g).1
  change (((ω : K F →ₜ* Circle) ^ 2) k) = ((ω : K F →ₜ* Circle) k) ^ 2
  exact ContinuousMonoidHom.pow_apply _ _ _

private theorem coeff_one (v : Place F) : coeff F 1 v = 1 := by
  have h (g : IdeleClass F) : normOneEulerCharacter F 1 g = 1 := rfl
  have hu : unramifiedFiniteCharacter F (normOneEulerCharacter F 1) v :=
    fun u _ ↦ h _
  simp only [coeff, heckeEulerCoefficient, ite_eq_left hu, h, Circle.coe_one]

private theorem quadratic_coeff_cases (ω : PontryaginDual (K F)) (hω : ω ^ 2 = 1)
    (v : Place F) : coeff F ω v = 0 ∨ coeff F ω v = 1 ∨ coeff F ω v = -1 := by
  by_cases hu : unramifiedFiniteCharacter F (normOneEulerCharacter F ω) v
  · right
    let g := ideleClassMap F (singleFiniteIdele F v (chosenFiniteUniformizer F v))
    have h : ((normOneEulerCharacter F ω g : Circle) : ℂ) ^ 2 = 1 := by
      rw [← Circle.coe_pow, ← normOneEulerCharacter_sq_apply, hω]
      rfl
    have he := (sq_eq_sq_iff_eq_or_eq_neg).mp (h.trans (one_pow 2).symm)
    simpa only [coeff, heckeEulerCoefficient, ite_eq_left hu, g] using he
  · exact Or.inl (by simp [coeff, heckeEulerCoefficient, hu])

open scoped ComplexOrder in
private theorem exists_sparsePowerSeries (q : ℕ) (hq : 1 < q) (a : ℕ → ℂ)
    (ha : ∀ n, 0 ≤ a n) (ha₁ : a 0 = 1) :
    ∃ b : ArithmeticFunction ℂ, (∀ n, 0 ≤ b n) ∧ b 1 = 1 ∧
      ∀ (s z : ℂ), HasSum (fun k : ℕ ↦ a k * ((q : ℂ) ^ (-s)) ^ k) z →
        LSeriesHasSum b s z := by
  let g : ℕ → ℕ := fun k ↦ q ^ k
  have hg : Injective g := Nat.pow_right_injective hq
  have hz : ∀ k, g k ≠ 0 := fun k ↦ pow_ne_zero _ (by omega)
  let b : ArithmeticFunction ℂ := ⟨Function.extend g a 0, by
    exact Function.extend_apply' a (0 : ℕ → ℂ) 0 (fun ⟨k, hk⟩ ↦ hz k hk)⟩
  have hb (k : ℕ) : b (g k) = a k := hg.extend_apply a 0 k
  have hb' (n : ℕ) (hn : n ∉ range g) : b n = 0 :=
    Function.extend_apply' a (0 : ℕ → ℂ) n hn
  refine ⟨b, fun n ↦ ?_, (hb 0).trans ha₁, fun s z hs ↦ ?_⟩
  · by_cases hn : n ∈ range g
    · obtain ⟨k, rfl⟩ := hn
      rw [hb]
      exact ha k
    · rw [hb' n hn]
  · apply (hg.hasSum_iff (f := LSeries.term b s) fun n hn ↦ by
      simp [LSeries.term_def, hb' n hn]).mp
    suffices (LSeries.term b s) ∘ g = (fun k ↦ a k * ((q : ℂ) ^ (-s)) ^ k) by
      rwa [this]
    funext k
    change LSeries.term b s (g k) = a k * ((q : ℂ) ^ (-s)) ^ k
    rw [LSeries.term_of_ne_zero (hz k), hb, div_eq_mul_inv, ← Complex.cpow_neg]
    simp only [g, Nat.cast_pow]
    rw [← Complex.natCast_cpow_natCast_mul, Complex.cpow_nat_mul]

open scoped ComplexOrder in
/-- The product of the trivial Euler factor and a quadratic Euler factor
has a Dirichlet expansion with nonnegative coefficients and constant term one. -/
theorem exists_quadraticEulerPair_localSeries (ω : PontryaginDual (K F)) (hω : ω ^ 2 = 1)
    (v : Place F) :
    ∃ b : ArithmeticFunction ℂ, (∀ n, 0 ≤ b n) ∧ b 1 = 1 ∧
      ∀ s : ℂ, 0 < s.re → LSeriesHasSum b s (factor F 1 v s * factor F ω v s) := by
  let q := v.asIdeal.absNorm
  have hq : 1 < q := NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hnorm (s : ℂ) (hs : 0 < s.re) : ‖(q : ℂ) ^ (-s)‖ < 1 := by
    have h : (1 : ℝ) < q := by exact_mod_cast hq
    rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans h)]
    exact Real.rpow_lt_one_of_one_lt_of_neg h (by simpa using neg_lt_zero.mpr hs)
  rcases quadratic_coeff_cases F ω hω v with h | h | h
  · obtain ⟨b, hb, hb₁, ht⟩ := exists_sparsePowerSeries q hq (fun _ ↦ 1) (by simp) rfl
    refine ⟨b, hb, hb₁, fun s hs ↦ ht s _ ?_⟩
    simpa only [factor, heckeEulerFactor, ← show q = v.asIdeal.absNorm from rfl, coeff_one, h,
      one_mul, zero_mul, sub_zero, inv_one, mul_one] using
      hasSum_geometric_of_norm_lt_one (hnorm s hs)
  · obtain ⟨b, hb, hb₁, ht⟩ := exists_sparsePowerSeries q hq
      (fun k ↦ ((k + 1 : ℕ) : ℂ)) (fun _ ↦ Complex.zero_le_real.mpr (Nat.cast_nonneg _)) (by simp)
    refine ⟨b, hb, hb₁, fun s hs ↦ ht s _ ?_⟩
    simpa only [factor, heckeEulerFactor, ← show q = v.asIdeal.absNorm from rfl, coeff_one, h,
      one_mul, Nat.choose_one_right, one_div, Nat.reduceAdd, pow_two, mul_inv_rev] using
      hasSum_choose_mul_geometric_of_norm_lt_one 1 (hnorm s hs)
  · obtain ⟨b, hb, hb₁, ht⟩ := exists_sparsePowerSeries (q ^ 2) (by nlinarith) (fun _ ↦ 1)
      (by simp) rfl
    refine ⟨b, hb, hb₁, fun s hs ↦ ht s _ ?_⟩
    have he : ((q ^ 2 : ℕ) : ℂ) ^ (-s) = ((q : ℂ) ^ (-s)) ^ 2 := by
      rw [Nat.cast_pow, ← Complex.natCast_cpow_natCast_mul, Complex.cpow_nat_mul]
    rw [he]
    have he' (x : ℂ) : (1 - x ^ 2)⁻¹ = (1 - x)⁻¹ * (1 - -x)⁻¹ := by
      rw [← mul_inv, show (1 - x) * (1 - -x) = 1 - x ^ 2 by ring]
    simpa only [factor, heckeEulerFactor, ← show q = v.asIdeal.absNorm from rfl, coeff_one, h,
      one_mul, neg_one_mul, ← he'] using
      hasSum_geometric_of_norm_lt_one (ξ := ((q : ℂ) ^ (-s)) ^ 2) (by
        rw [norm_pow]
        exact pow_lt_one₀ (norm_nonneg _) (hnorm s hs) (by decide))

private def quadraticEulerPartialProduct (ω : PontryaginDual (K F)) (A : Finset (Place F))
    (s : ℂ) : ℂ :=
  ∏ v ∈ A, (factor F 1 v s * factor F ω v s)

open scoped ComplexOrder in
private theorem exists_quadraticEulerPair_partialSeries (ω : PontryaginDual (K F))
    (hω : ω ^ 2 = 1) (A : Finset (Place F)) :
    ∃ b : ArithmeticFunction ℂ, (∀ n, 0 ≤ b n) ∧ b 1 = 1 ∧
      ∀ s : ℂ, 0 < s.re → LSeriesHasSum b s (quadraticEulerPartialProduct F ω A s) := by
  induction A using Finset.induction_on with
  | empty =>
    refine ⟨1, fun n ↦ ?_, by simp, fun s _ ↦ ?_⟩
    · rw [ArithmeticFunction.one_apply]
      split_ifs
      · exact zero_le_one
      · rfl
    · simp only [quadraticEulerPartialProduct, Finset.prod_empty]
      change HasSum (LSeries.term ((1 : ArithmeticFunction ℂ) ·) s) 1
      have h₁ : LSeries.term ((1 : ArithmeticFunction ℂ) ·) s 1 = 1 := by
        simp [LSeries.term_of_ne_zero]
      rw [← h₁]
      apply hasSum_single 1
      intro n hn
      simp [LSeries.term_def, ArithmeticFunction.one_apply, hn]
  | insert v A hv ih =>
    obtain ⟨b, hb, hb₁, hbs⟩ := ih
    obtain ⟨c, hc, hc₁, hcs⟩ := exists_quadraticEulerPair_localSeries F ω hω v
    refine ⟨c * b, fun n ↦ ?_, by simp [hb₁, hc₁], fun s hs ↦ ?_⟩
    · rw [ArithmeticFunction.mul_apply]
      exact Finset.sum_nonneg fun i _ ↦ mul_nonneg (hc i.1) (hb i.2)
    · simpa only [quadraticEulerPartialProduct, Finset.prod_insert hv] using
        ArithmeticFunction.LSeriesHasSum_mul (hcs s hs) (hbs s hs)

private theorem quadraticEulerPartialProduct_analytic (ω : PontryaginDual (K F))
    (hω : ω ^ 2 = 1) (A : Finset (Place F)) {s : ℂ} (hs : 0 < s.re) :
    AnalyticAt ℂ (quadraticEulerPartialProduct F ω A) s := by
  obtain ⟨b, _, _, hb⟩ := exists_quadraticEulerPair_partialSeries F ω hω A
  have hbd : LSeries.abscissaOfAbsConv b ≤ (0 : ℝ) :=
    LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun x hx ↦
      (hb x (by simpa using hx)).LSeriesSummable
  apply (LSeries_analyticOnNhd b s (hbd.trans_lt (by exact_mod_cast hs))).congr
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).eventually_mem hs] with z hz
  exact (hb z hz).LSeries_eq

private theorem quadraticEulerPartialProduct_tendsto (ω : PontryaginDual (K F))
    {G : ℂ → ℂ}
    (he : EqOn G (globalFiniteHeckeEuler F 1 * globalFiniteHeckeEuler F ω) {z | 1 < z.re}) :
    TendstoLocallyUniformlyOn (quadraticEulerPartialProduct F ω) G atTop {z | 1 < z.re} := by
  let U : Set ℂ := {z | 1 < z.re}
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hprod (ψ : PontryaginDual (K F)) :
      TendstoLocallyUniformlyOn (fun A : Finset (Place F) ↦ fun z ↦ ∏ v ∈ A, factor F ψ v z)
        (globalFiniteHeckeEuler F ψ) atTop U := by
    apply (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).mpr
    intro C hC hcompact
    exact hasProdUniformlyOn_iff_tendstoUniformlyOn.mp
      (heckeEulerProduct_hasProdUniformlyOn F (coeff F ψ)
        (norm_heckeEulerCoefficient_le_one F _ _) C hcompact fun z hz ↦ hC hz)
  have hcontinuous (ψ : PontryaginDual (K F)) :
      ContinuousOn (globalFiniteHeckeEuler F ψ) U := by
    apply (hprod ψ).continuousOn (Eventually.of_forall (fun A ↦ ?_)).frequently
    apply continuousOn_finsetProd
    intro v _
    have hn : (v.asIdeal.absNorm : ℂ) ≠ 0 := by
      exact_mod_cast (zero_lt_one.trans (NumberField.HeightOneSpectrum.one_lt_absNorm v)).ne'
    letI : NeZero (v.asIdeal.absNorm : ℂ) := ⟨hn⟩
    have hpow : Continuous (fun z : ℂ ↦ (v.asIdeal.absNorm : ℂ) ^ (-z)) :=
      (differentiable_const_cpow_of_neZero _).continuous.comp continuous_neg
    unfold factor heckeEulerFactor
    apply (continuousOn_const.sub (continuous_const.mul hpow).continuousOn).inv₀
    intro z hz
    have hq : (1 : ℝ) < v.asIdeal.absNorm := by
      exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
    have hnrm : ‖(coeff F ψ v) * (v.asIdeal.absNorm : ℂ) ^ (-z)‖ < 1 := by
      rw [norm_mul, ← Complex.ofReal_natCast,
        Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans hq), Complex.neg_re]
      exact (mul_le_of_le_one_left (Real.rpow_nonneg (zero_lt_one.trans hq).le _)
        (norm_heckeEulerCoefficient_le_one F _ _ _)).trans_lt
        (Real.rpow_lt_one_of_one_lt_of_neg hq (neg_lt_zero.mpr (zero_lt_one.trans hz)))
    apply sub_ne_zero.mpr
    intro heq
    change (1 : ℂ) = coeff F ψ v * (v.asIdeal.absNorm : ℂ) ^ (-z) at heq
    exact hnrm.not_ge (by rw [← heq, norm_one])
  have ht := (hprod 1).fun_mul₀ (hprod ω) (hcontinuous 1) (hcontinuous ω)
  unfold quadraticEulerPartialProduct
  simp_rw [Finset.prod_mul_distrib]
  exact ht.congr_right he.symm

open scoped ComplexOrder in
/-- Any entire continuation of the product of the two finite Euler products
is positive on the real axis. The proof takes locally uniform limits of the
alternating derivative inequalities for the finite products. -/
theorem quadraticEulerPair_entire_positive (ω : PontryaginDual (K F)) (hω : ω ^ 2 = 1)
    {G : ℂ → ℂ} (hG : Differentiable ℂ G)
    (he : EqOn G (globalFiniteHeckeEuler F 1 * globalFiniteHeckeEuler F ω) {z | 1 < z.re})
    (y : ℝ) : 0 < G y := by
  let U : Set ℂ := {z | 1 < z.re}
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  let x := max y 1 + 1
  have hx : 1 < x := (le_max_right y 1).trans_lt (lt_add_one _)
  have hxU : (x : ℂ) ∈ U := by simpa [U] using hx
  let P := quadraticEulerPartialProduct F ω
  have hP : ∀ n (A : Finset (Place F)) (z : ℂ), z ∈ U →
      AnalyticAt ℂ (iteratedDeriv n (P A)) z := by
    intro n A z hz
    induction n with
    | zero =>
      simpa only [iteratedDeriv_zero] using
        quadraticEulerPartialProduct_analytic F ω hω A (zero_lt_one.trans hz)
    | succ n ih => rw [iteratedDeriv_succ]; exact ih.deriv
  have hlim (n : ℕ) :
      TendstoLocallyUniformlyOn (fun A ↦ iteratedDeriv n (P A)) (iteratedDeriv n G) atTop U := by
    induction n with
    | zero =>
      simpa only [iteratedDeriv_zero] using quadraticEulerPartialProduct_tendsto F ω he
    | succ n ih =>
      simpa only [iteratedDeriv_succ, Function.comp_def] using
        ih.deriv (Eventually.of_forall fun A z hz ↦ (hP n A z hz).differentiableAt.differentiableWithinAt) hU
  have hpartial (A : Finset (Place F)) : 1 ≤ P A x ∧
      ∀ n, 0 ≤ (-1 : ℂ) ^ n * iteratedDeriv n (P A) x := by
    obtain ⟨b, hb, hb₁, hbs⟩ := exists_quadraticEulerPair_partialSeries F ω hω A
    have hbd : LSeries.abscissaOfAbsConv b ≤ (0 : ℝ) :=
      LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun r hr ↦
        (hbs r (by simpa using hr)).LSeriesSummable
    have hx₀ : 0 < x := zero_lt_one.trans hx
    have hE : LSeries.abscissaOfAbsConv b < (x : EReal) := hbd.trans_lt (by exact_mod_cast hx₀)
    have hpos : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    have heq : LSeries b =ᶠ[𝓝 (x : ℂ)] P A := by
      filter_upwards [hpos.eventually_mem (show 0 < ((x : ℂ)).re by simpa using hx₀)] with z hz
      exact (hbs z hz).LSeries_eq
    refine ⟨?_, fun n ↦ ?_⟩
    · change 1 ≤ quadraticEulerPartialProduct F ω A x
      rw [← (hbs x (by simpa using hx₀)).LSeries_eq]
      change 1 ≤ ∑' n, LSeries.term b x n
      have ht₁ : LSeries.term b x 1 = 1 := by simp [LSeries.term_of_ne_zero, hb₁]
      rw [← ht₁]
      exact (hbs x (by simpa using hx₀)).LSeriesSummable.le_tsum 1
        (fun n _ ↦ LSeries.term_nonneg (hb n) x)
    · rw [← heq.iteratedDeriv_eq n]
      exact LSeries.iteratedDeriv_alternating hb hE n
  have hbase : (1 : ℂ) ≤ G x := by
    apply le_of_tendsto_of_tendsto tendsto_const_nhds
      (by simpa only [iteratedDeriv_zero] using (hlim 0).tendsto_at hxU)
    exact Eventually.of_forall fun A ↦ (hpartial A).1
  have halternating (n : ℕ) : 0 ≤ (-1 : ℂ) ^ n * iteratedDeriv n G x :=
    le_of_tendsto_of_tendsto tendsto_const_nhds
      ((hlim n).tendsto_at hxU |>.const_mul _) (Eventually.of_forall fun A ↦ (hpartial A).2 n)
  have hyx : (y : ℂ) ≤ (x : ℂ) := by
    exact_mod_cast (le_max_left y 1).trans (lt_add_one _).le
  exact (zero_lt_one.trans_le hbase).trans_le
    (hG.apply_le_of_iteratedDeriv_alternating (fun n _ ↦ halternating n) hyx)

open scoped ComplexOrder in
/-- If the trivial continuation has no other pole and has a trivial zero,
an entire quadratic continuation cannot cancel its pole at one. -/
theorem quadraticEuler_order_le_zero_one_of_trivial_zero (ω : PontryaginDual (K F))
    (hω : ω ^ 2 = 1) {f₀ f₁ : ℂ → ℂ}
    (hm₀ : MeromorphicOn f₀ univ) (hm₁ : MeromorphicOn f₁ univ)
    (he₀ : EqOn f₀ (globalFiniteHeckeEuler F 1) {z | 1 < z.re})
    (he₁ : EqOn f₁ (globalFiniteHeckeEuler F ω) {z | 1 < z.re})
    (hpole : meromorphicOrderAt f₀ 1 = (-1 : ℤ))
    (hreg₀ : ∀ z, z ≠ 1 → 0 ≤ meromorphicOrderAt f₀ z)
    (hreg₁ : ∀ z, 0 ≤ meromorphicOrderAt f₁ z)
    {y : ℝ} (hzero : 0 < meromorphicOrderAt f₀ y) :
    meromorphicOrderAt f₁ 1 ≤ 0 := by
  by_contra! hbad
  let P : ℂ → ℂ := f₀ * f₁
  have hm : MeromorphicOn P univ := hm₀.mul hm₁
  have hord (z : ℂ) : meromorphicOrderAt P z =
      meromorphicOrderAt f₀ z + meromorphicOrderAt f₁ z :=
    meromorphicOrderAt_mul (hm₀ z (mem_univ z)) (hm₁ z (mem_univ z))
  have hnonneg (z : ℂ) : 0 ≤ meromorphicOrderAt P z := by
    rw [hord]
    by_cases hz : z = 1
    · subst z
      rw [hpole]
      have h1 : (1 : WithTop ℤ) ≤ meromorphicOrderAt f₁ 1 := by
        cases h : meromorphicOrderAt f₁ 1 with
        | top => simp
        | coe n =>
          rw [h] at hbad
          exact WithTop.coe_le_coe.mpr (by have := WithTop.coe_lt_coe.mp hbad; omega : (1 : ℤ) ≤ n)
      have hle := add_le_add (le_refl (((-1 : ℤ) : WithTop ℤ))) h1
      exact (show (0 : WithTop ℤ) = ((-1 : ℤ) : WithTop ℤ) + 1 by decide) ▸ hle
    · exact add_nonneg (hreg₀ z hz) (hreg₁ z)
  let G := toMeromorphicNFOn P univ
  have hnf : MeromorphicNFOn G univ := meromorphicNFOn_toMeromorphicNFOn P univ
  have horder (z : ℂ) : meromorphicOrderAt G z = meromorphicOrderAt P z :=
    meromorphicOrderAt_toMeromorphicNFOn hm (mem_univ z)
  have han (z : ℂ) : AnalyticAt ℂ G z :=
    (hnf (mem_univ z)).meromorphicOrderAt_nonneg_iff_analyticAt.mp
      (by rw [horder]; exact hnonneg z)
  have hpEuler : EqOn P (globalFiniteHeckeEuler F 1 * globalFiniteHeckeEuler F ω)
      {z | 1 < z.re} := fun z hz ↦ by
    change f₀ z * f₁ z = globalFiniteHeckeEuler F 1 z * globalFiniteHeckeEuler F ω z
    rw [he₀ hz, he₁ hz]
  have he : EqOn G (globalFiniteHeckeEuler F 1 * globalFiniteHeckeEuler F ω) {z | 1 < z.re} := by
    intro z hz
    let E := globalFiniteHeckeEuler F 1 * globalFiniteHeckeEuler F ω
    have hU : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    have hpE : P =ᶠ[𝓝[≠] z] E := by
      filter_upwards [(hU.eventually_mem hz).filter_mono nhdsWithin_le_nhds] with w hw
      exact hpEuler hw
    have hgE : G =ᶠ[𝓝[≠] z] E :=
      (hm.toMeromorphicNFOn_eq_self_on_nhdsNE (mem_univ z)).trans hpE
    have hcts : ContinuousOn E {z | 1 < z.re} :=
      (quadraticEulerPartialProduct_tendsto F ω (G := E) (fun _ _ ↦ rfl)).continuousOn
        (Eventually.of_forall fun A w hw ↦
          (quadraticEulerPartialProduct_analytic F ω hω A
            (zero_lt_one.trans hw)).continuousAt.continuousWithinAt).frequently
    exact tendsto_nhds_unique
      (((han z).continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' hgE)
      (((hcts z hz).continuousAt (hU.mem_nhds hz)).tendsto.mono_left nhdsWithin_le_nhds)
  have hp := quadraticEulerPair_entire_positive F ω hω (fun z ↦ (han z).differentiableAt) he y
  have hzG : 0 < meromorphicOrderAt G y := by
    rw [horder, hord]
    exact add_pos_of_pos_of_nonneg hzero (hreg₁ y)
  have hnG := (hnf (mem_univ (y : ℂ))).meromorphicOrderAt_eq_zero_iff.mpr hp.ne'
  exact hzG.ne' hnG

private theorem factor_product_radial_form (ω : PontryaginDual (K F)) (v : Place F) (t : ℝ) :
    ∃ z w : ℂ, ‖w‖ ≤ 1 ∧ (z = 0 ∨ ‖z‖ = 1 ∧ w = z ^ 2) ∧
      ∀ σ : ℝ,
        factor F 1 v σ ^ 3 * factor F ω v ((σ : ℂ) + (t : ℂ) * Complex.I) ^ 4 *
          factor F (ω ^ 2) v ((σ : ℂ) + 2 * ((t : ℂ) * Complex.I)) =
        let a : ℝ := (v.asIdeal.absNorm : ℝ) ^ (-σ)
        ((1 - a : ℂ)⁻¹)^3 * ((1 - a*z)⁻¹)^4 * (1 - a*w)⁻¹ := by
  let q := v.asIdeal.absNorm
  let d : ℂ := (t : ℂ) * Complex.I
  let u : ℂ := (q : ℂ) ^ (-d)
  have hq : (1 : ℝ) < (q : ℝ) := by
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hq₀ : 0 < (q : ℝ) := zero_lt_one.trans hq
  have hqn : (q : ℂ) ≠ 0 := by exact_mod_cast hq₀.ne'
  have h1 : ‖u‖ = 1 := by
    dsimp only [u]
    rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hq₀]
    simp [d, Complex.mul_re]
  let z := coeff F ω v * u
  let w := coeff F (ω ^ 2) v * u ^ 2
  have hw : ‖w‖ ≤ 1 := by
    dsimp [w]
    rw [norm_mul, norm_pow, h1, one_pow, mul_one]
    exact norm_heckeEulerCoefficient_le_one F _ _ _
  have hz : z = 0 ∨ ‖z‖ = 1 ∧ w = z ^ 2 := by
    by_cases hu : unramifiedFiniteCharacter F (normOneEulerCharacter F ω) v
    · have hu₂ : unramifiedFiniteCharacter F (normOneEulerCharacter F (ω ^ 2)) v := by
        intro a ha
        rw [normOneEulerCharacter_sq_apply, hu a ha, one_pow]
      right
      dsimp only [z, w, coeff]
      rw [heckeEulerCoefficient, ite_eq_left hu, heckeEulerCoefficient, ite_eq_left hu₂,
        normOneEulerCharacter_sq_apply, Circle.coe_pow, mul_pow, norm_mul, Circle.norm_coe, h1,
        one_mul]
      exact ⟨rfl, rfl⟩
    · left
      simp [z, coeff, heckeEulerCoefficient, hu]
  refine ⟨z, w, hw, hz, fun σ ↦ ?_⟩
  let a : ℝ := (q : ℝ) ^ (-σ)
  have haC : ((q : ℂ) ^ (-(σ : ℂ))) = (a : ℂ) := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_neg, ← Complex.ofReal_cpow hq₀.le]
  have hd1 : (q : ℂ) ^ (-((σ : ℂ) + d)) = (a : ℂ) * u := by
    rw [neg_add, Complex.cpow_add _ _ hqn, haC]
  have hd2 : (q : ℂ) ^ (-((σ : ℂ) + 2 * d)) = (a : ℂ) * u ^ 2 := by
    rw [neg_add, Complex.cpow_add _ _ hqn, haC,
      show -(2*d) = (2 : ℕ) * (-d) by ring, Complex.cpow_nat_mul]
  change factor F 1 v σ ^ 3 * factor F ω v ((σ : ℂ) + d) ^ 4 *
    factor F (ω ^ 2) v ((σ : ℂ) + 2*d) = _
  simp only [factor, heckeEulerFactor, show v.asIdeal.absNorm = q from rfl, coeff_one, haC,
    hd1, hd2, one_mul]
  simp only [a, z, w, mul_left_comm]

private theorem factor_product_norm_ge_one (ω : PontryaginDual (K F)) (v : Place F)
    {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    1 ≤ ‖factor F 1 v σ ^ 3 * factor F ω v ((σ : ℂ) + (t : ℂ) * Complex.I) ^ 4 *
      factor F (ω ^ 2) v ((σ : ℂ) + 2 * ((t : ℂ) * Complex.I))‖ := by
  obtain ⟨z, w, hw, hz, e⟩ := factor_product_radial_form F ω v t
  have hq : (1 : ℝ) < (v.asIdeal.absNorm : ℝ) := by
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  rw [e σ]
  exact norm_euler_factor_combination (Real.rpow_nonneg (zero_lt_one.trans hq).le _)
    (Real.rpow_lt_one_of_one_lt_of_neg hq (by linarith)) z w hw hz

private theorem factor_product_norm_antitone (ω : PontryaginDual (K F)) (v : Place F) (t : ℝ) :
    AntitoneOn (fun σ : ℝ ↦ ‖factor F 1 v σ ^ 3 * factor F ω v ((σ : ℂ) + (t : ℂ) * Complex.I) ^ 4 *
      factor F (ω ^ 2) v ((σ : ℂ) + 2 * ((t : ℂ) * Complex.I))‖) (Ioi 1) := by
  intro σ hσ τ _ hστ
  obtain ⟨z, w, hw, hz, e⟩ := factor_product_radial_form F ω v t
  simp only [e]
  have hq : (1 : ℝ) < (v.asIdeal.absNorm : ℝ) := by
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  exact norm_radialEuler_mono (Real.rpow_nonneg (zero_lt_one.trans hq).le _)
    (Real.rpow_le_rpow_of_exponent_le hq.le (neg_le_neg hστ))
    (Real.rpow_lt_one_of_one_lt_of_neg hq (neg_lt_zero.mpr (zero_lt_one.trans hσ))) hw hz

/-- The classical three-factor Euler-product inequality for the actual finite
Hecke Euler products. Ramified primes are included with their prescribed
constant-one factors, including when squaring lowers the conductor. -/
theorem globalFiniteHeckeEuler_product_norm_ge_one (ω : PontryaginDual (K F))
    {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    1 ≤ ‖globalFiniteHeckeEuler F 1 σ ^ 3 *
      globalFiniteHeckeEuler F ω ((σ : ℂ) + (t : ℂ) * Complex.I) ^ 4 *
      globalFiniteHeckeEuler F (ω ^ 2) ((σ : ℂ) + 2 * ((t : ℂ) * Complex.I))‖ := by
  have hprod (ω : PontryaginDual (K F)) (s : ℂ) (hs : 1 < s.re) :
      HasProd (fun v ↦ factor F ω v s) (globalFiniteHeckeEuler F ω s) :=
    (heckeEulerProduct_hasProdUniformlyOn F (coeff F ω) (norm_heckeEulerCoefficient_le_one F _ _)
      {s} isCompact_singleton (by simpa using hs)).hasProd (mem_singleton s)
  have h₀ := hprod 1 σ (by simpa using hσ)
  have h₁ := hprod ω ((σ : ℂ) + (t : ℂ) * Complex.I) (by simpa [Complex.mul_re] using hσ)
  have h₂ := hprod (ω ^ 2) ((σ : ℂ) + 2 * ((t : ℂ) * Complex.I))
    (by simpa [Complex.mul_re, Complex.mul_im] using hσ)
  apply le_of_tendsto_of_tendsto tendsto_const_nhds ((h₀.pow 3).mul (h₁.pow 4) |>.mul h₂).norm
  exact Filter.Eventually.of_forall fun A ↦ Finset.one_le_prod fun v _ ↦
    factor_product_norm_ge_one F ω v hσ t

/-- The three-factor Euler product has nonincreasing norm in the real
parameter beyond one. This retains the factor at the doubled height. -/
theorem globalFiniteHeckeEuler_product_norm_antitone (ω : PontryaginDual (K F)) (t : ℝ) :
    AntitoneOn (fun σ : ℝ ↦ ‖globalFiniteHeckeEuler F 1 σ ^ 3 *
      globalFiniteHeckeEuler F ω ((σ : ℂ) + (t : ℂ) * Complex.I) ^ 4 *
      globalFiniteHeckeEuler F (ω ^ 2) ((σ : ℂ) + 2 * ((t : ℂ) * Complex.I))‖) (Ioi 1) := by
  have hprod (ω : PontryaginDual (K F)) (s : ℂ) (hs : 1 < s.re) :
      HasProd (fun v ↦ factor F ω v s) (globalFiniteHeckeEuler F ω s) :=
    (heckeEulerProduct_hasProdUniformlyOn F (coeff F ω) (norm_heckeEulerCoefficient_le_one F _ _)
      {s} isCompact_singleton (by simpa using hs)).hasProd (mem_singleton s)
  have h (σ : ℝ) (hσ : 1 < σ) :=
    (((hprod 1 σ (by simpa using hσ)).pow 3).mul
      ((hprod ω ((σ : ℂ) + (t : ℂ) * Complex.I) (by simpa [Complex.mul_re] using hσ)).pow 4) |>.mul
      (hprod (ω ^ 2) ((σ : ℂ) + 2 * ((t : ℂ) * Complex.I))
        (by simpa [Complex.mul_re, Complex.mul_im] using hσ))).norm
  intro σ hσ τ hτ hστ
  apply le_of_tendsto_of_tendsto (h τ hτ) (h σ hσ)
  exact Filter.Eventually.of_forall fun A ↦ Finset.prod_le_prod (fun _ _ ↦ norm_nonneg _)
    (fun v _ ↦ factor_product_norm_antitone F ω v t hσ hτ hστ)

/-- The Euler-product inequality excludes a zero on the line of real part
one provided the squared-character continuation has no pole at the doubled
height. Only meromorphic orders enter the argument. -/
theorem globalFiniteHecke_order_le_zero_one_line_of_square_regular
    (ω : PontryaginDual (K F)) (t : ℝ) {f₀ f₁ f₂ : ℂ → ℂ}
    (hm₀ : MeromorphicOn f₀ univ) (hm₁ : MeromorphicOn f₁ univ) (hm₂ : MeromorphicOn f₂ univ)
    (he₀ : EqOn f₀ (globalFiniteHeckeEuler F 1) {z | 1 < z.re})
    (he₁ : EqOn f₁ (globalFiniteHeckeEuler F ω) {z | 1 < z.re})
    (he₂ : EqOn f₂ (globalFiniteHeckeEuler F (ω ^ 2)) {z | 1 < z.re})
    (h₀ : (-1 : ℤ) ≤ meromorphicOrderAt f₀ 1)
    (h₂ : 0 ≤ meromorphicOrderAt f₂ (1 + 2 * ((t : ℂ) * Complex.I))) :
    meromorphicOrderAt f₁ (1 + (t : ℂ) * Complex.I) ≤ 0 := by
  let d := (t : ℂ) * Complex.I
  let g₁ := f₁ ∘ fun z : ℂ ↦ z + d
  let g₂ := f₂ ∘ fun z : ℂ ↦ z + 2*d
  let P := f₀ ^ 3 * g₁ ^ 4 * g₂
  have han (a : ℂ) : AnalyticAt ℂ (fun z : ℂ ↦ z + a) 1 := analyticAt_id.add analyticAt_const
  have horder (f : ℂ → ℂ) (a : ℂ) :
      meromorphicOrderAt (f ∘ fun z : ℂ ↦ z + a) 1 = meromorphicOrderAt f (1+a) :=
    meromorphicOrderAt_comp_of_deriv_ne_zero (f := f) (han a) (by
      have hd : HasDerivAt (fun z : ℂ ↦ z+a) 1 1 := (hasDerivAt_id _).add_const a
      rw [hd.deriv]
      exact one_ne_zero)
  have hpm₁ : MeromorphicAt g₁ 1 :=
    (hm₁ (1+d) (mem_univ _)).comp_analyticAt (g := fun z : ℂ ↦ z+d) (han d)
  have hpm₂ : MeromorphicAt g₂ 1 :=
    (hm₂ (1+2*d) (mem_univ _)).comp_analyticAt (g := fun z : ℂ ↦ z+2*d) (han (2*d))
  have hpm₀ := hm₀ 1 (mem_univ (1 : ℂ))
  by_contra! hn
  have h₁ : 1 ≤ meromorphicOrderAt f₁ (1+d) := by
    cases h : meromorphicOrderAt f₁ (1+d) with
    | top => simp
    | coe n =>
      change 0 < meromorphicOrderAt f₁ (1+d) at hn
      rw [h] at hn
      have hn' : (0 : ℤ) < n := WithTop.coe_lt_coe.mp hn
      exact WithTop.coe_le_coe.mpr (by omega : (1 : ℤ) ≤ n)
  have hpos : 0 < meromorphicOrderAt P 1 := by
    dsimp only [P]
    rw [meromorphicOrderAt_mul ((hpm₀.pow 3).mul (hpm₁.pow 4)) hpm₂,
      meromorphicOrderAt_mul (hpm₀.pow 3) (hpm₁.pow 4), meromorphicOrderAt_pow hpm₀,
      meromorphicOrderAt_pow hpm₁, horder f₁ d, horder f₂ (2*d)]
    have ha := add_le_add
      (add_le_add (nsmul_le_nsmul_right h₀ 3) (nsmul_le_nsmul_right h₁ 4)) h₂
    have hb : (0 : WithTop ℤ) < (3 : ℕ) • ((-1 : ℤ) : WithTop ℤ) +
        (4 : ℕ) • (1 : WithTop ℤ) + 0 := by
      change ((0 : ℤ) : WithTop ℤ) < (3 : ℕ) • ((-1 : ℤ) : WithTop ℤ) +
        (4 : ℕ) • ((1 : ℤ) : WithTop ℤ) + ((0 : ℤ) : WithTop ℤ)
      simp only [← WithTop.coe_nsmul, ← WithTop.coe_add, WithTop.coe_lt_coe]
      norm_num
    have hmul (n : ℕ) (k : WithTop ℤ) : n • k = (n : WithTop ℤ) * k := by
      cases k with
      | top =>
        cases n with
        | zero => simp
        | succ n =>
          have hn : (↑(n + 1) : WithTop ℤ) ≠ 0 := by
            exact_mod_cast Nat.succ_ne_zero n
          rw [WithTop.mul_top hn]
          simp [succ_nsmul]
      | coe k => rw [← WithTop.coe_nsmul, nsmul_eq_mul, WithTop.coe_mul, WithTop.coe_natCast]
    exact lt_of_lt_of_le hb (by simpa only [hmul] using ha)
  have ht : Tendsto (fun s : ℝ ↦ (s : ℂ)) (𝓝[>] (1 : ℝ)) (𝓝[≠] (1 : ℂ)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · simpa only [Complex.ofReal_one] using
        (Complex.continuous_ofReal.continuousAt (x := (1 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      change (s : ℂ) ≠ 1
      exact_mod_cast (show s ≠ 1 from (show 1 < s from hs).ne')
  have hlim := (tendsto_zero_of_meromorphicOrderAt_pos hpos).comp ht
  have hbad : (1 : ℝ) ≤ 0 := by
    apply le_of_tendsto_of_tendsto tendsto_const_nhds (by simpa only [norm_zero] using hlim.norm)
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs' : 1 < s := hs
    have hd : d.re = 0 := by simp [d, Complex.mul_re]
    have hz₀ : (s : ℂ) ∈ {z : ℂ | 1 < z.re} := by simpa using hs'
    have hz₁ : (s : ℂ) + d ∈ {z : ℂ | 1 < z.re} := by simpa [Complex.add_re, hd] using hs'
    have hz₂ : (s : ℂ) + 2*d ∈ {z : ℂ | 1 < z.re} := by
      simpa [Complex.add_re, Complex.mul_re, hd] using hs'
    change 1 ≤ ‖f₀ s ^ 3 * f₁ ((s : ℂ)+d) ^ 4 * f₂ ((s : ℂ)+2*d)‖
    rw [he₀ hz₀, he₁ hz₁, he₂ hz₂]
    exact globalFiniteHeckeEuler_product_norm_ge_one F ω hs' t
  exact (by norm_num : ¬ (1 : ℝ) ≤ 0) hbad

local instance eulerNonvanishingIdeleMeasurable : MeasurableSpace (Idele F) := borel _
local instance eulerNonvanishingIdeleBorel : BorelSpace (Idele F) := ⟨rfl⟩
local instance eulerNonvanishingNormOneMeasurable : MeasurableSpace (K F) := borel _
local instance eulerNonvanishingNormOneBorel : BorelSpace (K F) := ⟨rfl⟩

private abbrev reciprocalArch (ω : PontryaginDual (K F))
    (S : Finset (Place F)) (hs : Surjective (sIdeleClassInclusion F S))
    (hu : globalNormOneCharacter F ω ∈
      (sUnramified F S : Set (QuasiCharacter (IdeleClass F)))) :=
  archimedeanNumberFieldZetaDenominator F
    (sLocalRealArchParameters F S (sLocalNormOneCharacterOfGlobal F ω S hs hu))
    (sLocalComplexArchParameters F S (sLocalNormOneCharacterOfGlobal F ω S hs hu))

theorem sLocalNormOneCharacterOfGlobal_trivial
    (S : Finset (Place F)) (hs : Surjective (sIdeleClassInclusion F S))
    (hu : globalNormOneCharacter F 1 ∈
      (sUnramified F S : Set (QuasiCharacter (IdeleClass F)))) :
    sLocalNormOneCharacterOfGlobal F 1 S hs hu = 1 := by
  ext k
  obtain ⟨q, rfl⟩ := globalNormOneToSLocal_surjective F S hs k
  rw [sLocalNormOneCharacterOfGlobal_match]
  rfl

private theorem reciprocalArch_trivial_even_zero
    (S : Finset (Place F)) (hs : Surjective (sIdeleClassInclusion F S))
    (hu : globalNormOneCharacter F 1 ∈
      (sUnramified F S : Set (QuasiCharacter (IdeleClass F)))) (n : ℕ) :
    reciprocalArch F 1 S hs hu (-2 * (n : ℂ)) = 0 := by
  unfold reciprocalArch archimedeanNumberFieldZetaDenominator
  rw [sLocalNormOneCharacterOfGlobal_trivial]
  let v : InfinitePlace F := Classical.choice inferInstance
  by_cases hv : v.IsReal
  · let i : {w : InfinitePlace F // w.IsReal} := ⟨v, hv⟩
    have ha := sLocalRealArchParameters_one F S i
    apply mul_eq_zero.mpr
    left
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    rw [ha.1, add_zero, realArchZetaDenominator_eq_zero_iff]
    exact ⟨n, by rw [ha.2]; push_cast; ring⟩
  · let i : {w : InfinitePlace F // w.IsComplex} := ⟨v, InfinitePlace.not_isReal_iff_isComplex.mp hv⟩
    have ha := sLocalComplexArchParameters_one F S i
    apply mul_eq_zero.mpr
    right
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    rw [ha]
    apply (complexArchZetaDenominator_eq_zero_iff _ _).mpr
    exact ⟨2 * n, by push_cast; simp⟩

private theorem one_le_order_of_pos {a : WithTop ℤ} (ha : 0 < a) : 1 ≤ a := by
  cases a with
  | top => simp
  | coe a =>
    exact WithTop.coe_le_coe.mpr (by have := WithTop.coe_lt_coe.mp ha; omega : (1 : ℤ) ≤ a)

variable (η : Measure (Idele F)) [η.IsHaarMeasure]
variable (ν : Measure (K F)) [ν.IsHaarMeasure]
variable [∀ v : Place F, MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : Place F, BorelSpace (v.adicCompletion F)ˣ]
  (μ : ∀ v : Place F, Measure (v.adicCompletion F)ˣ)
  [∀ v : Place F, (μ v).IsHaarMeasure] [∀ v : Place F, SigmaFinite (μ v)]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]
variable (hν : IsWeilQuotientMeasure (principalIdeles F) η Measure.count (globalClassMeasure F ν))

include μ hν in
/-- The actual finite Euler continuation has no poles on nontrivial components.
On the trivial component its only pole is a simple pole at one, and it
vanishes at minus two. -/
theorem globalFiniteHecke_pole_and_trivial_zero (ω : PontryaginDual (K F))
    {f : ℂ → ℂ} (hf : MeromorphicOn f univ)
    (he : EqOn f (globalFiniteHeckeEuler F ω) {z | 1 < z.re}) :
    (ω ≠ 1 → ∀ z, 0 ≤ meromorphicOrderAt f z) ∧
    (ω = 1 → meromorphicOrderAt f 1 = (-1 : ℤ) ∧
      (∀ z, z ≠ 1 → 0 ≤ meromorphicOrderAt f z) ∧ 0 < meromorphicOrderAt f (-2)) := by
  obtain ⟨S, hS⟩ := exists_homogeneousThetaPlaceBase F ω
  obtain ⟨hs, hu⟩ := hS S Subset.rfl
  obtain ⟨L, hm, hEq, hreg, hpoles⟩ :=
    exists_globalCompletedHecke_analytic_or_simple_poles F ω S hs hu η ν μ hν
  let D := reciprocalArch F ω S hs hu
  have hD (z : ℂ) : AnalyticAt ℂ D z :=
    archimedeanNumberFieldZetaDenominator_analytic _ _ _ z
  have ho (z : ℂ) : meromorphicOrderAt f z = meromorphicOrderAt D z + meromorphicOrderAt L z :=
    (meromorphicOrderAt_congr (globalFiniteHeckeContinuation_germ F ω S hs hu hm hf hEq he z)).trans
      (meromorphicOrderAt_mul (hD z).meromorphicAt (hm z (mem_univ z)))
  refine ⟨fun hω z ↦ ho z ▸ add_nonneg (hD z).meromorphicOrderAt_nonneg
    (hreg hω z (mem_univ z)).meromorphicOrderAt_nonneg, ?_⟩
  intro hω
  subst ω
  have hzero (n : ℕ) : 0 < meromorphicOrderAt D (-2 * (n : ℂ)) := by
    let z : ℂ := -2 * (n : ℂ)
    refine lt_of_le_of_ne (hD z).meromorphicOrderAt_nonneg fun h ↦ ?_
    exact ((hD z).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mp h.symm)
      (reciprocalArch_trivial_even_zero F S hs hu n)
  have hnonneg (z : ℂ) (hz₀ : z ≠ 0) (hz₁ : z ≠ 1) :=
    ((hpoles rfl).2.2 z hz₀ hz₁).meromorphicOrderAt_nonneg
  refine ⟨(globalFiniteHeckeContinuation_order_of_re_pos F 1 S hs hu hm hf hEq he (by simp)).trans
    (hpoles rfl).2.1, ?_, ?_⟩
  · intro z hz₁
    rw [ho]
    rcases eq_or_ne z 0 with rfl | hz₀
    · rw [(hpoles rfl).1]
      have hn : (1 : WithTop ℤ) ≤ meromorphicOrderAt D 0 := one_le_order_of_pos
        (by simpa using hzero 0)
      have hadd := add_le_add hn (le_refl (((-1 : ℤ) : WithTop ℤ)))
      exact (show (0 : WithTop ℤ) = 1 + ((-1 : ℤ) : WithTop ℤ) by decide) ▸ hadd
    · exact add_nonneg (hD z).meromorphicOrderAt_nonneg (hnonneg z hz₀ hz₁)
  · rw [ho]
    exact add_pos_of_pos_of_nonneg (by simpa using hzero 1)
      (hnonneg (-2) (by norm_num) (by norm_num))

include μ hν in
/-- The right-half-plane pole profile holds for any meromorphic continuation
of the actual finite Euler product. -/
theorem globalFiniteHecke_positive_pole_profile (ω : PontryaginDual (K F))
    {f : ℂ → ℂ} (hf : MeromorphicOn f univ)
    (he : EqOn f (globalFiniteHeckeEuler F ω) {z | 1 < z.re}) :
    (ω = 1 → meromorphicOrderAt f 1 = (-1 : ℤ)) ∧
      ∀ z, 0 < z.re → (ω ≠ 1 ∨ z ≠ 1) → 0 ≤ meromorphicOrderAt f z := by
  obtain ⟨hreg, htrivial⟩ := globalFiniteHecke_pole_and_trivial_zero F η ν μ hν ω hf he
  refine ⟨fun hω ↦ (htrivial hω).1, fun z _ h ↦ ?_⟩
  rcases eq_or_ne ω 1 with hω | hω
  · exact (htrivial hω).2.1 z (h.resolve_left (not_not.mpr hω))
  · exact hreg hω z

include μ hν in
private theorem exists_finiteContinuation (ψ : PontryaginDual (K F)) :
    ∃ g : ℂ → ℂ, MeromorphicOn g univ ∧ EqOn g (globalFiniteHeckeEuler F ψ) {z | 1 < z.re} := by
  obtain ⟨S, hS⟩ := exists_homogeneousThetaPlaceBase F ψ
  obtain ⟨hs, hu⟩ := hS S Subset.rfl
  obtain ⟨g, hgm, hge, _⟩ := exists_globalFiniteHeckeContinuation F ψ S hs hu η ν μ hν
  exact ⟨g, hgm, hge⟩

include μ hν in
private theorem globalFiniteHecke_order_le_zero_one_line_of_regular_square
    (ω : PontryaginDual (K F)) (t : ℝ) {f : ℂ → ℂ}
    (hf : MeromorphicOn f univ)
    (he : EqOn f (globalFiniteHeckeEuler F ω) {z | 1 < z.re})
    (hcase : ω ^ 2 ≠ 1 ∨ t ≠ 0) :
    meromorphicOrderAt f (1 + (t : ℂ) * Complex.I) ≤ 0 := by
  obtain ⟨f₀, hm₀, he₀⟩ := exists_finiteContinuation F η ν μ hν 1
  obtain ⟨f₂, hm₂, he₂⟩ := exists_finiteContinuation F η ν μ hν (ω ^ 2)
  have h₀ := (globalFiniteHecke_positive_pole_profile F η ν μ hν 1 hm₀ he₀).1 rfl
  let z : ℂ := 1 + 2 * ((t : ℂ) * Complex.I)
  have hz : 0 < z.re := by simp [z, Complex.mul_re, Complex.mul_im]
  have hz₂ : ω ^ 2 ≠ 1 ∨ z ≠ 1 := hcase.imp_right fun ht heq ↦ by
    have him := congrArg Complex.im heq
    simp [z, Complex.mul_re, Complex.mul_im] at him
    exact ht (by linarith)
  have h₂ := (globalFiniteHecke_positive_pole_profile F η ν μ hν (ω ^ 2) hm₂ he₂).2 z hz hz₂
  exact globalFiniteHecke_order_le_zero_one_line_of_square_regular F ω t hm₀ hf hm₂ he₀ he he₂
    (le_of_eq h₀.symm) h₂

include μ hν in
/-- Every continuation of the actual finite Hecke Euler product has
no positive meromorphic order on the line of real part one. -/
theorem globalFiniteHecke_order_le_zero_one_line (ω : PontryaginDual (K F)) (t : ℝ)
    {f : ℂ → ℂ} (hf : MeromorphicOn f univ)
    (he : EqOn f (globalFiniteHeckeEuler F ω) {z | 1 < z.re}) :
    meromorphicOrderAt f (1 + (t : ℂ) * Complex.I) ≤ 0 := by
  by_cases hcase : ω ^ 2 ≠ 1 ∨ t ≠ 0
  · exact globalFiniteHecke_order_le_zero_one_line_of_regular_square F η ν μ hν ω t hf he hcase
  push Not at hcase
  rw [hcase.2, Complex.ofReal_zero, zero_mul, add_zero]
  rcases eq_or_ne ω 1 with rfl | hω
  · rw [(globalFiniteHecke_positive_pole_profile F η ν μ hν 1 hf he).1 rfl]
    change ((-1 : ℤ) : WithTop ℤ) ≤ ((0 : ℤ) : WithTop ℤ)
    exact WithTop.coe_le_coe.mpr (by norm_num)
  · obtain ⟨f₀, hm₀, he₀⟩ := exists_finiteContinuation F η ν μ hν 1
    obtain ⟨hp, hr, hz⟩ := (globalFiniteHecke_pole_and_trivial_zero F η ν μ hν 1 hm₀ he₀).2 rfl
    have hχ := (globalFiniteHecke_pole_and_trivial_zero F η ν μ hν ω hf he).1 hω
    exact quadraticEuler_order_le_zero_one_of_trivial_zero F ω hcase.1 hm₀ hf he₀ he hp hr hχ
      (y := -2) (by simpa using hz)

include μ hν in
/-- The completed Euler continuation is nonvanishing on the line of real
part one, with the trivial character's simple pole at height zero. -/
theorem globalCompletedHecke_order_eq_zero_one_line (ω : PontryaginDual (K F))
    (S : Finset (Place F)) (hs : Surjective (sIdeleClassInclusion F S))
    (hu : globalNormOneCharacter F ω ∈
      (sUnramified F S : Set (QuasiCharacter (IdeleClass F))))
    (t : ℝ) {L : ℂ → ℂ} (hL : MeromorphicOn L univ)
    (he : EqOn L (globalCompletedHeckeEuler F ω S hs hu) {z | 1 < z.re})
    (hcase : ω ≠ 1 ∨ t ≠ 0) :
    meromorphicOrderAt L (1 + (t : ℂ) * Complex.I) = 0 := by
  obtain ⟨f, hf, hfe, _⟩ := exists_globalFiniteHeckeContinuation F ω S hs hu η ν μ hν
  let z : ℂ := 1 + (t : ℂ) * Complex.I
  have hz : 0 < z.re := by simp [z, Complex.mul_re]
  have hregular : ω ≠ 1 ∨ z ≠ 1 := hcase.imp_right
    (fun ht heq ↦ ht (by simpa [z, Complex.mul_im] using congrArg Complex.im heq))
  change meromorphicOrderAt L z = 0
  rw [← globalFiniteHeckeContinuation_order_of_re_pos F ω S hs hu hL hf he hfe hz]
  exact le_antisymm
    (globalFiniteHecke_order_le_zero_one_line F η ν μ hν ω t hf hfe)
    ((globalFiniteHecke_positive_pole_profile F η ν μ hν ω hf hfe).2 z hz hregular)

include μ hν in
/-- Clause (4) of Proposition 3.2.1.3 for the canonical norm-one chart.
Every regular point with real part at least one is nonvanishing. -/
theorem globalCompletedHecke_ne_zero_of_one_le_re (ω : PontryaginDual (K F))
    (S : Finset (Place F)) (hs : Surjective (sIdeleClassInclusion F S))
    (hu : globalNormOneCharacter F ω ∈
      (sUnramified F S : Set (QuasiCharacter (IdeleClass F))))
    {L : ℂ → ℂ} (hL : MeromorphicOn L univ)
    (he : EqOn L (globalCompletedHeckeEuler F ω S hs hu) {z | 1 < z.re})
    {z : ℂ} (hz : 1 ≤ z.re) (ha : AnalyticAt ℂ L z) : L z ≠ 0 := by
  rcases hz.eq_or_lt with hre | hre
  · have hcase : ω ≠ 1 ∨ z.im ≠ 0 := by
      by_contra! h
      have hz₁ : z = 1 := Complex.ext (by simpa using hre.symm) (by simpa using h.2)
      subst z
      obtain ⟨f, hf, hfe, _⟩ := exists_globalFiniteHeckeContinuation F ω S hs hu η ν μ hν
      have hp := (globalFiniteHecke_positive_pole_profile F η ν μ hν ω hf hfe).1 h.1
      have ho := globalFiniteHeckeContinuation_order_of_re_pos F ω S hs hu
        hL hf he hfe (z := 1) (by simp)
      have hn := ha.meromorphicOrderAt_nonneg
      rw [← ho, hp] at hn
      change ((0 : ℤ) : WithTop ℤ) ≤ ((-1 : ℤ) : WithTop ℤ) at hn
      exact (by norm_num : ¬ (0 : ℤ) ≤ -1) (WithTop.coe_le_coe.mp hn)
    have hparam : z = 1 + (z.im : ℂ) * Complex.I := by
      apply Complex.ext <;> simp [hre.symm, Complex.mul_re, Complex.mul_im]
    have ho := globalCompletedHecke_order_eq_zero_one_line F η ν μ hν ω S hs hu z.im hL he hcase
    rw [← hparam] at ho
    exact ha.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mp ho
  · rw [he hre]
    exact globalCompletedHeckeEuler_ne_zero F ω S hs hu hre

end

end Masullo
