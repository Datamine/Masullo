import SchwartzBergman
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.Polynomial

open Filter Function Set Topology

namespace Masullo

noncomputable section

private abbrev StripBound (P : ℂ → ℂ) :=
  ∀ a b : ℝ, ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, z.re ∈ Icc a b → ‖P z‖ ≤ C

private theorem stripBound_shift (P : ℂ → ℂ) (hP : StripBound P) (c : ℂ) :
    StripBound (fun z ↦ P (z+c)) := by
  intro a b
  obtain ⟨C, hC, h⟩ := hP (a+c.re) (b+c.re)
  exact ⟨C, hC, fun z hz ↦ h (z+c) (by
    rw [Complex.add_re]
    exact ⟨add_le_add_left hz.1 _, add_le_add_left hz.2 _⟩)⟩

/-- Removing a finite-order zero of a strip-bounded entire function
preserves boundedness on each closed vertical strip. -/
private theorem exists_entire_divide_zero (P : ℂ → ℂ) (hP : ∀ z, AnalyticAt ℂ P z)
    (hbound : StripBound P) (n : ℕ) (hn : analyticOrderAt P 0 = n) :
    ∃ U : ℂ → ℂ, (∀ z, AnalyticAt ℂ U z) ∧ U 0 ≠ 0 ∧
      (∀ z, P z = z ^ n * U z) ∧ StripBound U := by
  obtain ⟨u, hu, hu₀, he⟩ := (hP 0).analyticOrderAt_eq_natCast.mp hn
  let U (z : ℂ) := if z = 0 then u 0 else P z / z ^ n
  have hU : U =ᶠ[𝓝 0] u := by
    filter_upwards [he] with z hz
    by_cases h : z = 0
    · simp [U, h]
    · change P z = (z - 0) ^ n * u z at hz
      simp only [sub_zero] at hz
      dsimp only [U]
      rw [ite_eq_right h, hz, mul_comm, mul_div_cancel_right₀ _ (pow_ne_zero _ h)]
  have hUa (z : ℂ) : AnalyticAt ℂ U z := by
    by_cases hz : z = 0
    · subst z
      exact hu.congr hU.symm
    · apply ((hP z).div (analyticAt_id.pow n) (pow_ne_zero _ hz)).congr
      filter_upwards [isOpen_ne.mem_nhds hz] with w hw
      change P w / w ^ n = if w = 0 then u 0 else P w / w ^ n
      rw [ite_eq_right hw]
  refine ⟨U, hUa, by simpa [U] using hu₀, ?_, ?_⟩
  · intro z
    by_cases hz : z = 0
    · subst z
      change P =ᶠ[𝓝 0] (fun z ↦ (z - 0) ^ n • u z) at he
      have hh := he.eq_of_nhds
      simpa [U, smul_eq_mul] using hh
    · dsimp only [U]
      rw [ite_eq_right hz, mul_div_cancel₀ _ (pow_ne_zero _ hz)]
  · intro a b
    obtain ⟨C, hC, h⟩ := hbound a b
    have hc : Continuous U := continuous_iff_continuousAt.mpr fun z ↦ (hUa z).continuousAt
    obtain ⟨M, hM⟩ := ((isCompact_closedBall (0 : ℂ) 1).image hc.norm).bddAbove
    refine ⟨max C M, hC.trans (le_max_left _ _), fun z hz ↦ ?_⟩
    by_cases hsmall : ‖z‖ ≤ 1
    · exact (hM (mem_image_of_mem _ (by simpa using hsmall))).trans (le_max_right _ _)
    · have hlarge : 1 < ‖z‖ := lt_of_not_ge hsmall
      have hne : z ≠ 0 := norm_pos_iff.mp (zero_lt_one.trans hlarge)
      dsimp only [U]
      rw [ite_eq_right hne, norm_div, norm_pow]
      refine (div_le_self (norm_nonneg _) (one_le_pow₀ hlarge.le)).trans ?_
      exact (h z hz).trans (le_max_left _ _)

private theorem gaussian_poly_weight_bound (a b : ℝ) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, z.re ∈ Icc a b →
      ‖z‖ ^ N * ‖Complex.exp (z ^ 2)‖ ≤ C := by
  by_cases hab : a ≤ b
  swap
  · exact ⟨0, le_rfl, fun z hz ↦ (hab (hz.1.trans hz.2)).elim⟩
  have h := gaussian_mem_schwartzBergmanSubmodule (univ : Set ℝ) isOpen_univ
  obtain ⟨C, hC⟩ := h.2.2 a b hab (subset_univ _) N
  refine ⟨max C 0, le_max_right _ _, fun z hz ↦ ?_⟩
  have hz' := hC (mem_image_of_mem _ hz)
  simpa [norm_mul, norm_pow] using hz'.trans (le_max_left C 0)

private theorem polynomial_gaussian_strip_bound (a b : ℝ) (N : ℕ) (p : Polynomial ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, z.re ∈ Icc a b →
      ‖z‖ ^ N * ‖p.eval z * Complex.exp (z^2)‖ ≤ C := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨C, hC, hp⟩ := hp
    obtain ⟨D, hD, hq⟩ := hq
    refine ⟨C+D, add_nonneg hC hD, fun z hz ↦ ?_⟩
    rw [Polynomial.eval_add, add_mul]
    calc
      _ ≤ ‖z‖ ^ N * (‖p.eval z * Complex.exp (z^2)‖ +
          ‖q.eval z * Complex.exp (z^2)‖) := by gcongr; exact norm_add_le _ _
      _ ≤ C+D := by rw [mul_add]; exact add_le_add (hp z hz) (hq z hz)
  | monomial i c =>
    obtain ⟨C, hC, h⟩ := gaussian_poly_weight_bound a b (N+i)
    refine ⟨‖c‖ * C, mul_nonneg (norm_nonneg _) hC, fun z hz ↦ ?_⟩
    rw [Polynomial.eval_monomial, norm_mul, norm_mul, norm_pow]
    calc
      _ = ‖c‖ * (‖z‖ ^ (N+i) * ‖Complex.exp (z^2)‖) := by rw [pow_add]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (h z hz) (norm_nonneg _)

private theorem analyticOrderAt_pow_id_zero (n : ℕ) :
    analyticOrderAt (fun w : ℂ ↦ w ^ n) 0 = n := by
  change analyticOrderAt ((id : ℂ → ℂ) ^ n) 0 = n
  rw [analyticOrderAt_pow analyticAt_id, analyticOrderAt_id]
  simp

/-- A strip-bounded entire divisor yields an entire Schwartz test
interpolating one jet at a selected zero. At every other point the
test retains the vanishing order of the original divisor. -/
theorem exists_verticalStrip_cardinalJet (P : ℂ → ℂ) (hP : ∀ z, AnalyticAt ℂ P z)
    (hbound : ∀ a b : ℝ, ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, z.re ∈ Icc a b → ‖P z‖ ≤ C)
    (c : ℂ) (n k : ℕ) (hn : analyticOrderAt P c = n) :
    ∃ g : ℂ → ℂ, (∀ z, AnalyticAt ℂ g z) ∧
      g ∈ schwartzBergmanSubmodule (univ : Set ℝ) ∧
      (∀ j < n, iteratedDeriv j g c = if j = k then 1 else 0) ∧
      ∀ z ≠ c, analyticOrderAt P z ≤ analyticOrderAt g z := by
  let p (z : ℂ) := P (z+c)
  have hp (z : ℂ) : AnalyticAt ℂ p z := (hP (z+c)).comp
    (f := fun w : ℂ ↦ w+c) (x := z) (analyticAt_id.add analyticAt_const)
  have hpn : analyticOrderAt p 0 = n := by
    have ha : AnalyticAt ℂ (fun z : ℂ ↦ z+c) 0 := analyticAt_id.add analyticAt_const
    have hder : HasDerivAt (fun z : ℂ ↦ z+c) 1 0 := (hasDerivAt_id 0).add_const c
    have he := (hP (0+c)).analyticOrderAt_comp (g := fun z : ℂ ↦ z+c) (z₀ := (0 : ℂ)) ha
    have hh := ha.analyticOrderAt_sub_eq_one_of_deriv_ne_zero (hder.deriv ▸ one_ne_zero)
    change analyticOrderAt p 0 = _ at he
    rw [hh, mul_one, zero_add, hn] at he
    exact he
  obtain ⟨U, hU, hU₀, hPe, hUb⟩ := exists_entire_divide_zero p hp (stripBound_shift P hbound c) n hpn
  let V (z : ℂ) := U z * Complex.exp (z^2)
  have hVa (z : ℂ) : AnalyticAt ℂ V z := (hU z).mul ((analyticAt_id.pow 2).cexp)
  have hV₀ : V 0 ≠ 0 := mul_ne_zero hU₀ (Complex.exp_ne_zero _)
  let H (z : ℂ) := (z^k / (k.factorial : ℂ)) / V z
  have hHa : AnalyticAt ℂ H 0 :=
    ((analyticAt_id.pow _).div analyticAt_const (by exact_mod_cast Nat.factorial_ne_zero k)).div (hVa _) hV₀
  obtain ⟨R, hR, hTaylor⟩ := hHa.exists_eventuallyEq_sum_add_pow_mul n
  let q : Polynomial ℂ :=
    ∑ j ∈ Finset.range n, Polynomial.monomial j (iteratedDeriv j H 0 / (j.factorial : ℂ))
  let g₀ (z : ℂ) := q.eval z * V z
  let g (z : ℂ) := g₀ (z-c)
  have hq (z : ℂ) : AnalyticAt ℂ (fun z ↦ q.eval z) z :=
    (AnalyticOnNhd.eval_polynomial (𝕜 := ℂ) q) z (mem_univ _)
  have hg₀ (z : ℂ) : AnalyticAt ℂ g₀ z := (hq z).mul (hVa z)
  have hg (z : ℂ) : AnalyticAt ℂ g z := (hg₀ (z-c)).comp
    (f := fun w : ℂ ↦ w-c) (x := z) (analyticAt_id.sub analyticAt_const)
  have hErr : (fun z : ℂ ↦ z^k / (k.factorial : ℂ) - g₀ z) =ᶠ[𝓝 0]
      (fun z ↦ z^n * (R z * V z)) := by
    filter_upwards [hTaylor, (hVa 0).continuousAt.eventually_ne hV₀] with z hz hv
    have hqz : (∑ j ∈ Finset.range n, (z ^ j / (j.factorial : ℂ)) • iteratedDeriv j H 0) = q.eval z := by
      simp [q, Polynomial.eval_finsetSum, Polynomial.eval_monomial, smul_eq_mul,
        div_eq_mul_inv, mul_assoc, mul_comm]
    rw [hqz] at hz
    have he := congrArg (· * V z) hz
    change ((z^k / (k.factorial : ℂ)) / V z) * V z = (q.eval z + z^n * R z) * V z at he
    rw [div_mul_cancel₀ _ hv, add_mul, mul_assoc] at he
    change z^k / (k.factorial : ℂ) - q.eval z * V z = _
    rw [he, add_sub_cancel_left]
  refine ⟨g, hg, ?_, ?_, ?_⟩
  · have hd : Differentiable ℂ g := fun z ↦ (hg z).differentiableAt
    refine ⟨by simp, hd.differentiableOn, ?_⟩
    intro a b hab _ N
    obtain ⟨B, hB, hUbnd⟩ := hUb (a-c.re) (b-c.re)
    obtain ⟨C, hC, hpoly⟩ := polynomial_gaussian_strip_bound (a-c.re) (b-c.re) N q
    obtain ⟨D, hD, hpoly₀⟩ := polynomial_gaussian_strip_bound (a-c.re) (b-c.re) 0 q
    refine ⟨2^N * max C (‖c‖^N * D) * B, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    let w := z-c
    have hw : w.re ∈ Icc (a-c.re) (b-c.re) := by
      change z.re - c.re ∈ _
      exact ⟨sub_le_sub_right hz.1 _, sub_le_sub_right hz.2 _⟩
    have hpot := hpoly w hw
    have hpot₀ : ‖q.eval w * Complex.exp (w^2)‖ ≤ D := by simpa using hpoly₀ w hw
    have hnorm : ‖z‖ ≤ 2 * max ‖w‖ ‖c‖ := by
      have he := norm_add_le w c
      rw [show w+c = z by dsimp [w]; abel] at he
      linarith [le_max_left ‖w‖ ‖c‖, le_max_right ‖w‖ ‖c‖]
    have hval : ‖g z‖ = ‖q.eval w * Complex.exp (w^2)‖ * ‖U w‖ := by
      change ‖q.eval w * (U w * _)‖ = _
      rw [mul_comm (U w), ← mul_assoc, norm_mul]
    change ‖z ^ N * g z‖ ≤ _
    rw [norm_mul, norm_pow, hval, ← mul_assoc]
    apply mul_le_mul _ (hUbnd w hw) (norm_nonneg _) (by positivity)
    calc
      _ ≤ (2 * max ‖w‖ ‖c‖)^N * ‖q.eval w * Complex.exp (w^2)‖ := by gcongr
      _ ≤ _ := by
        rw [mul_pow, mul_assoc]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rcases le_total ‖w‖ ‖c‖ with h | h
        · rw [max_eq_right h]
          exact (mul_le_mul_of_nonneg_left hpot₀ (by positivity)).trans (le_max_right _ _)
        · rw [max_eq_left h]
          exact hpot.trans (le_max_left _ _)
  · intro j hj
    have hdiff : AnalyticAt ℂ (fun z : ℂ ↦ z^k / (k.factorial : ℂ) - g₀ z) 0 :=
      ((analyticAt_id.pow _).div analyticAt_const (by exact_mod_cast Nat.factorial_ne_zero k)).sub (hg₀ _)
    have hO : (n : ℕ∞) ≤ analyticOrderAt (fun z : ℂ ↦ z^k / (k.factorial : ℂ) - g₀ z) 0 := by
      exact (natCast_le_analyticOrderAt hdiff).mpr ⟨_, hR.mul (hVa 0), by
        filter_upwards [hErr] with z hz
        simpa only [sub_zero, smul_eq_mul, Pi.mul_apply] using hz⟩
    have he := (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hdiff).mp hO j hj
    rw [iteratedDeriv_fun_sub (by fun_prop) (hg₀ _).contDiffAt,
      iteratedDeriv_div_const, iteratedDeriv_fun_pow_zero, sub_eq_zero] at he
    rw [iteratedDeriv_comp_sub_const]
    change iteratedDeriv j g₀ (c-c) = _
    rw [sub_self, ← he]
    split_ifs with h
    · subst j
      exact div_self (by exact_mod_cast Nat.factorial_ne_zero k)
    · simp
  · intro z hz
    let w := z-c
    have hw : w ≠ 0 := sub_ne_zero.mpr hz
    have hP' : P =ᶠ[𝓝 z] fun u ↦ (u-c)^n * U (u-c) := by
      refine .of_forall fun u ↦ ?_
      have h := hPe (u-c)
      change P (u-c+c) = _ at h
      rwa [sub_add_cancel] at h
    have hU' : AnalyticAt ℂ (fun u : ℂ ↦ U (u-c)) z := (hU w).comp
      (f := fun u : ℂ ↦ u-c) (x := z) (analyticAt_id.sub analyticAt_const)
    have hw' : AnalyticAt ℂ (fun u : ℂ ↦ (u-c)^n) z := (analyticAt_id.sub analyticAt_const).pow n
    have hW := hw'.analyticOrderAt_eq_zero.mpr (pow_ne_zero _ hw)
    have hp' : analyticOrderAt P z = analyticOrderAt (fun u : ℂ ↦ U (u-c)) z := by
      rw [analyticOrderAt_congr hP']
      change analyticOrderAt ((fun u : ℂ ↦ (u-c)^n) * fun u ↦ U (u-c)) z = _
      rw [analyticOrderAt_mul hw' hU', hW, zero_add]
    let B (u : ℂ) := q.eval (u-c) * Complex.exp ((u-c)^2)
    have hB : AnalyticAt ℂ B z := ((hq w).comp (f := fun u : ℂ ↦ u-c) (x := z)
      (analyticAt_id.sub analyticAt_const)).mul (((analyticAt_id.sub analyticAt_const).pow 2).cexp)
    have hprod : g = (fun u : ℂ ↦ U (u-c)) * B := by funext u; dsimp [g, g₀, V, B]; ring
    rw [hp', hprod, analyticOrderAt_mul hU' hB]
    exact le_add_of_nonneg_right bot_le

/-- A vertical translation costs at most a polynomial in the height in
each weighted strip norm. -/
theorem verticalStrip_heightTranslate_bound (g : ℂ → ℂ)
    (hg : g ∈ schwartzBergmanSubmodule (univ : Set ℝ)) (a b : ℝ) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (y : ℝ) (z : ℂ), z.re ∈ Icc a b →
      ‖z‖^N * ‖g (z - (y : ℂ) * Complex.I)‖ ≤ C * (1 + |y|)^N := by
  by_cases hab : a ≤ b
  swap
  · exact ⟨0, le_rfl, fun y z hz ↦ (hab (hz.1.trans hz.2)).elim⟩
  obtain ⟨D, hD⟩ := hg.2.2 a b hab (subset_univ _) N
  obtain ⟨E, hE⟩ := hg.2.2 a b hab (subset_univ _) 0
  let M := max 0 (max D E)
  have hM : 0 ≤ M := le_max_left _ _
  refine ⟨2^N * M, mul_nonneg (by positivity) hM, fun y z hz ↦ ?_⟩
  let w := z - (y : ℂ) * Complex.I
  have hwr : w.re = z.re := by simp [w]
  have hw : w.re ∈ Icc a b := hwr ▸ hz
  have hn := norm_add_le w ((y : ℂ) * Complex.I)
  rw [show w + (y : ℂ) * Complex.I = z by dsimp [w]; abel,
    norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs] at hn
  have hbound : ‖z‖ ≤ (1+|y|) * (2 * max 1 ‖w‖) := by
    have h1 : ‖w‖ ≤ max 1 ‖w‖ := le_max_right _ _
    have h2 : 1 ≤ max 1 ‖w‖ := le_max_left _ _
    calc
      _ ≤ ‖w‖ + |y| := hn
      _ ≤ max 1 ‖w‖ + |y| := add_le_add_left h1 _
      _ ≤ max 1 ‖w‖ + |y| * max 1 ‖w‖ := by
        exact add_le_add_right (le_mul_of_one_le_right (abs_nonneg _) h2) _
      _ = (1+|y|) * max 1 ‖w‖ := by ring
      _ ≤ _ := by
        exact mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (by positivity) (by norm_num))
          (by positivity)
  have hwN : ‖w‖^N * ‖g w‖ ≤ D := by
    simpa only [norm_mul, norm_pow] using hD (mem_image_of_mem _ hw)
  have hw₀ : ‖g w‖ ≤ E := by
    simpa only [pow_zero, one_mul] using hE (mem_image_of_mem _ hw)
  have hmax : (max 1 ‖w‖)^N * ‖g w‖ ≤ M := by
    rcases le_total ‖w‖ 1 with hlo | hhi
    · rw [max_eq_left hlo, one_pow, one_mul]
      exact hw₀.trans ((le_max_right D E).trans (le_max_right 0 _))
    · rw [max_eq_right hhi]
      exact hwN.trans ((le_max_left D E).trans (le_max_right 0 _))
  change ‖z‖^N * ‖g w‖ ≤ _
  calc
    _ ≤ ((1+|y|) * (2 * max 1 ‖w‖))^N * ‖g w‖ := by gcongr
    _ = (2^N * ((max 1 ‖w‖)^N * ‖g w‖)) * (1+|y|)^N := by simp only [mul_pow]; ring
    _ ≤ _ := by gcongr


/-- Reflection about one half preserves the whole-plane
Schwartz–Bergman test space. -/
theorem schwartzBergmanSubmodule_reflect_one (H : ℂ → ℂ)
    (hH : H ∈ schwartzBergmanSubmodule (univ : Set ℝ)) :
    (fun z : ℂ ↦ H (1-z)) ∈ schwartzBergmanSubmodule (univ : Set ℝ) := by
  have hd : Differentiable ℂ H := differentiableOn_univ.mp (by simpa only [preimage_univ] using hH.2.1)
  refine ⟨by simp, (hd.comp (by fun_prop : Differentiable ℂ (fun z : ℂ ↦ 1-z))).differentiableOn, ?_⟩
  intro a b hab _ N
  obtain ⟨M, hM⟩ := hH.2.2 (1-b) (1-a) (by linarith) (subset_univ _) N
  obtain ⟨B, hB⟩ := hH.2.2 (1-b) (1-a) (by linarith) (subset_univ _) 0
  refine ⟨2^N * max M B, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  let w := 1-z
  have hw : w.re ∈ Icc (1-b) (1-a) := by
    change z.re ∈ Icc a b at hz
    simp only [w, Complex.sub_re, Complex.one_re]
    constructor <;> linarith [hz.1, hz.2]
  have hn := norm_sub_le (1 : ℂ) w
  rw [show (1 : ℂ)-w=z by simp [w], norm_one] at hn
  have hle : ‖z‖ ≤ 2 * max 1 ‖w‖ :=
    hn.trans (by linarith [le_max_left (1 : ℝ) ‖w‖, le_max_right (1 : ℝ) ‖w‖])
  change ‖z^N * H w‖ ≤ _
  rw [norm_mul, norm_pow]
  calc
    _ ≤ (2 * max 1 ‖w‖)^N * ‖H w‖ := by gcongr
    _ = 2^N * ((max 1 ‖w‖)^N * ‖H w‖) := by rw [mul_pow, mul_assoc]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rcases le_total ‖w‖ 1 with h | h
      · rw [max_eq_left h, one_pow, one_mul]
        exact (by simpa only [pow_zero, one_mul] using hB (mem_image_of_mem _ hw) :
          ‖H w‖ ≤ B).trans (le_max_right _ _)
      · rw [max_eq_right h]
        exact (by simpa only [norm_mul, norm_pow] using hM (mem_image_of_mem _ hw) :
          ‖w‖^N * ‖H w‖ ≤ M).trans (le_max_left _ _)


end

end Masullo
