/-
The scalar estimate for the reciprocal adapts the Appendix B proof in
the Apache-2.0 RiemannMasullo project. See External/PROVENANCE.md.
-/
import FiniteHeckeGrowth
import GlobalHeckeResidues
import Mathlib.Analysis.Calculus.MeanValue

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical NumberField

namespace Masullo

noncomputable section

private abbrev absHeight := Filter.comap (abs : ℝ → ℝ) atTop

private theorem reciprocal_lower_bound {V Z X Y Q : ℝ}
    (hV : 3 ≤ V) (hZ : 0 ≤ Z) (hX : 0 ≤ X) (hQ : 0 ≤ Q)
    (hzeta : Z ≤ V ^ 13) (hsq : Q ≤ V) (hdiff : X ≤ Y + (V ^ 11)⁻¹)
    (hprod : 1 ≤ Z ^ 3 * X ^ 4 * Q) : (V ^ 11)⁻¹ ≤ Y := by
  by_contra! hy
  have hv : 0 < V := by linarith
  have hx : X ≤ 2 / V ^ 11 := by rw [div_eq_mul_inv]; linarith
  have hp : 1 ≤ 16 / V ^ 4 := calc
    1 ≤ Z ^ 3 * X ^ 4 * Q := hprod
    _ ≤ (V ^ 13) ^ 3 * (2 / V ^ 11) ^ 4 * V := by gcongr
    _ = 16 / V ^ 4 := by field_simp; ring
  have hh : (3 : ℝ) ^ 4 ≤ V ^ 4 := pow_le_pow_left₀ (by norm_num) hV _
  have h := (le_div_iff₀ (pow_pos hv 4)).mp hp
  norm_num at hh
  linarith

variable (F : Type*) [Field F] [NumberField F]

private abbrev Place := HeightOneSpectrum (𝓞 F)
private abbrev K := normOneIdeleClass F

local instance reciprocalNormOneMeasurable : MeasurableSpace (K F) := borel _
local instance reciprocalNormOneBorel : BorelSpace (K F) := ⟨rfl⟩
local instance reciprocalIdeleMeasurable : MeasurableSpace (Idele F) := borel _
local instance reciprocalIdeleBorel : BorelSpace (Idele F) := ⟨rfl⟩

/-- A common positive lower bound for the canonical finite Euler products
on the vertical line of real part two. -/
theorem globalFiniteHeckeEuler_norm_ge_two :
    ∃ c : ℝ, 0 < c ∧ ∀ (ω : PontryaginDual (K F)) (y : ℝ),
      c ≤ ‖globalFiniteHeckeEuler F ω ⟨2, y⟩‖ := by
  let H := max 1 ‖globalFiniteHeckeEuler F 1 (2 : ℂ)‖
  have hH : 0 < H := zero_lt_one.trans_le (le_max_left _ _)
  refine ⟨H⁻¹, inv_pos.mpr hH, fun ω y ↦ ?_⟩
  let z : ℂ := (2 : ℂ) + (y : ℂ) * Complex.I
  let w : ℂ := (2 : ℂ) + 2 * ((y : ℂ) * Complex.I)
  have hz : (⟨2, y⟩ : ℂ) = z := by
    apply Complex.ext <;> simp [z, Complex.mul_re, Complex.mul_im]
  rw [hz]
  have hprod := globalFiniteHeckeEuler_product_norm_ge_one F ω (by norm_num : (1 : ℝ) < 2) y
  change 1 ≤ ‖globalFiniteHeckeEuler F 1 2 ^ 3 * globalFiniteHeckeEuler F ω z ^ 4 *
    globalFiniteHeckeEuler F (ω ^ 2) w‖ at hprod
  rw [norm_mul, norm_mul, norm_pow, norm_pow] at hprod
  have hzeta : ‖globalFiniteHeckeEuler F 1 2‖ ≤ H := le_max_right _ _
  have htwo : ‖globalFiniteHeckeEuler F (ω ^ 2) w‖ ≤ H :=
    (globalFiniteHeckeEuler_bounded_right F (ω ^ 2) (by norm_num : (1 : ℝ) < 2)
      (by simp [w, Complex.mul_re, Complex.mul_im])).trans (le_max_right _ _)
  have hfour : 1 ≤ (H * ‖globalFiniteHeckeEuler F ω z‖) ^ 4 := calc
    _ ≤ _ := hprod
    _ ≤ H ^ 3 * ‖globalFiniteHeckeEuler F ω z‖ ^ 4 * H := by gcongr
    _ = _ := by ring
  apply (inv_le_iff_one_le_mul₀' hH).2
  by_contra! hbad
  exact (pow_lt_pow_left₀ hbad (by positivity) (by decide : (4 : ℕ) ≠ 0)).not_ge
    (by simpa using hfour)

/-- The finite Euler products have a common positive lower bound on the
vertical line of real part two. The same bound applies after a norm twist. -/
theorem manuscriptFiniteHecke_norm_ge_two :
    ∃ c : ℝ, 0 < c ∧ ∀ (χ : PontryaginDual (IdeleClass F)) (y : ℝ),
      c ≤ ‖manuscriptFiniteHeckeEuler F χ ⟨2, y⟩‖ := by
  obtain ⟨c, hc, hC⟩ := globalFiniteHeckeEuler_norm_ge_two F
  refine ⟨c, hc, fun χ y ↦ ?_⟩
  obtain ⟨t, ht, _⟩ := existsUnique_heckeHeight F χ
  have hz : (⟨2, y⟩ : ℂ) - (t : ℂ) * Complex.I = ⟨2, y - t⟩ := by
    apply Complex.ext <;> simp [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im]
  rw [manuscriptFiniteHeckeEuler_shift F χ ht, hz]
  exact hC _ _

variable (ν : Measure (K F)) [ν.IsHaarMeasure]
variable (η : Measure (Idele F)) [η.IsHaarMeasure]
variable [∀ v : Place F, MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : Place F, BorelSpace (v.adicCompletion F)ˣ]
  (μ : ∀ v : Place F, Measure (v.adicCompletion F)ˣ)
  [∀ v : Place F, (μ v).IsHaarMeasure] [∀ v : Place F, SigmaFinite (μ v)]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]
variable (hν : IsWeilQuotientMeasure (principalIdeles F) η Measure.count (globalClassMeasure F ν))

include μ hν in
theorem exists_globalFiniteHecke_oneLine_lower_bound (ω : PontryaginDual (K F)) :
    ∃ (L : ℂ → ℂ) (N : ℕ), 0 < N ∧ MeromorphicOn L univ ∧
      EqOn L (globalFiniteHeckeEuler F ω) {z | 1 < z.re} ∧
      (∀ z, z ≠ 0 → z ≠ 1 → AnalyticAt ℂ L z) ∧
      (∀ a b : ℝ, a < b → ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧
        ∀ z : ℂ, z.re ∈ Icc a b → 1 ≤ |z.im| → ‖L z‖ ≤ C * (1 + |z.im|) ^ N) ∧
      ∀ᶠ y : ℝ in absHeight, 1 ≤ |y| ∧ (|y| ^ N)⁻¹ ≤ ‖L ⟨1, y⟩‖ := by
  obtain ⟨L, hm, he, ha, hp, _⟩ := exists_globalFiniteHecke_polynomial_strips F ω ν η μ hν
  obtain ⟨L₂, _, he₂, _, hp₂, _⟩ :=
    exists_globalFiniteHecke_polynomial_strips F (ω ^ 2) ν η μ hν
  have hAnalytic (z : ℂ) (hz : 1 ≤ |z.im|) : AnalyticAt ℂ L z :=
    ha z (by intro e; norm_num [e] at hz) (by intro e; norm_num [e] at hz)
  obtain ⟨A, n, hA, hd⟩ := iteratedDeriv_polynomial_strip
    hAnalytic (hp (1 - 1) (2 + 1) (by norm_num)) 1
  obtain ⟨B, k, hB, htwo⟩ := hp₂ 1 2 one_lt_two
  let m := n + k + 1
  have hm₀ : 0 < m := by dsimp [m]; omega
  let V (y : ℝ) := |y| ^ m
  let step (y : ℝ) := (V y ^ 12)⁻¹
  have ht : Tendsto (abs : ℝ → ℝ) absHeight atTop := tendsto_comap
  have hV : Tendsto V absHeight atTop := (tendsto_pow_atTop hm₀.ne').comp ht
  have hStep : Tendsto step absHeight (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp ((tendsto_pow_atTop (by decide : (12 : ℕ) ≠ 0)).comp hV)
  have hZeta : Tendsto (fun y ↦ 1 + step y) absHeight (𝓝[>] (1 : ℝ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨by simpa using hStep.const_add 1, ?_⟩
    filter_upwards [hV.eventually_gt_atTop 0] with y hy
    exact lt_add_of_pos_right _ (inv_pos.mpr (pow_pos hy 12))
  obtain ⟨C, hC⟩ :=
    ((NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT F).norm.comp hZeta).isBoundedUnder_le.eventually_le
  refine ⟨L, m * 11, Nat.mul_pos hm₀ (by decide), hm, he, ha, hp, ?_⟩
  filter_upwards [hC, hV.eventually_ge_atTop C, hV.eventually_ge_atTop 3,
    hStep.eventually_le_const zero_lt_one, ht.eventually_ge_atTop 2,
    ht.eventually_ge_atTop (A * 2 ^ n), ht.eventually_ge_atTop (B * 3 ^ k)]
      with y hζ hCV hVy hsMax hy hyA hyB
  have hy₁ : 1 ≤ |y| := (by norm_num : (1 : ℝ) ≤ 2).trans hy
  have hv : 0 < V y := by linarith
  have hstep : 0 < step y := inv_pos.mpr (pow_pos hv 12)
  let x := 1 + step y
  have hx : 1 < x := lt_add_of_pos_right _ hstep
  have hx₂ : x ≤ 2 := by dsimp [x]; linarith
  have hDz (u : ℝ) (hu : u ∈ Icc (1 : ℝ) 2) : ‖deriv L ⟨u, y⟩‖ ≤ V y := by
    have hd' := hd ⟨u, y⟩ hu ((by norm_num : (1 : ℝ) + 1 ≤ 2).trans hy)
    rw [show (1 : ℕ) = 0 + 1 by rfl, iteratedDeriv_succ, iteratedDeriv_zero] at hd'
    calc
      _ ≤ A * (1 + |y|) ^ n := hd'
      _ ≤ A * (2 * |y|) ^ n := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) (by linarith) _) hA
      _ ≤ |y| ^ (n + 1) := by
        rw [mul_pow, ← mul_assoc, pow_succ, mul_comm (|y| ^ n)]
        exact mul_le_mul_of_nonneg_right hyA (pow_nonneg (abs_nonneg _) _)
      _ ≤ V y := pow_le_pow_right₀ hy₁ (by dsimp [m]; omega)
  have hDeriv (u : ℝ) :
      HasDerivAt (fun v : ℝ ↦ L ⟨v, y⟩) (deriv L ⟨u, y⟩) u := by
    have hEq (v : ℝ) : (v : ℂ) + (⟨0, y⟩ : ℂ) = ⟨v, y⟩ := by
      apply Complex.ext <;> simp
    have h := ((hAnalytic ⟨u, y⟩ hy₁).differentiableAt.hasDerivAt.comp_of_eq (x := (u : ℂ))
      ((hasDerivAt_id (u : ℂ)).add_const (⟨0, y⟩ : ℂ)) (hEq u).symm).comp_ofReal
    simpa only [hEq, mul_one, id_eq, Function.comp_def] using h
  have hDiff : ‖L ⟨x, y⟩ - L ⟨1, y⟩‖ ≤ V y * step y := by
    have h := norm_image_sub_le_of_norm_deriv_le_segment' (a := (1 : ℝ)) (b := 2)
      (fun u _ ↦ (hDeriv u).hasDerivWithinAt)
      (fun u hu ↦ hDz u (Ico_subset_Icc_self hu)) x ⟨hx.le, hx₂⟩
    simpa [x, Real.norm_eq_abs, abs_of_nonneg hstep.le] using h
  have hsquare : ‖globalFiniteHeckeEuler F (ω ^ 2) ⟨x, 2 * y⟩‖ ≤ V y := by
    rw [← he₂ (show 1 < (⟨x, 2 * y⟩ : ℂ).re from hx)]
    have hheight : 1 ≤ |2 * y| := by rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]; linarith
    calc
      _ ≤ B * (1 + |2 * y|) ^ k := htwo _ ⟨hx.le, hx₂⟩ hheight
      _ ≤ B * (3 * |y|) ^ k := by
        apply mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ?_ _) hB
        rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        linarith
      _ ≤ |y| ^ (k + 1) := by
        rw [mul_pow, ← mul_assoc, pow_succ, mul_comm (|y| ^ k)]
        exact mul_le_mul_of_nonneg_right hyB (pow_nonneg (abs_nonneg _) _)
      _ ≤ V y := pow_le_pow_right₀ hy₁ (by dsimp [m]; omega)
  have hζnorm : step y * ‖dedekindZeta F (x : ℂ)‖ ≤ C := by
    simpa [Function.comp_def, x, norm_mul, Real.norm_of_nonneg hstep.le] using hζ
  have hzeta : ‖dedekindZeta F (x : ℂ)‖ ≤ V y ^ 13 := by
    have hz := (le_div_iff₀ hstep).mpr (by simpa only [mul_comm (step y)] using hζnorm.trans hCV)
    exact hz.trans_eq (by dsimp only [step]; rw [div_inv_eq_mul, pow_succ (V y) 12, mul_comm])
  have hprod := globalFiniteHeckeEuler_product_norm_ge_one F ω hx y
  have hmiddle : ((x : ℂ) + (y : ℂ) * Complex.I) = ⟨x, y⟩ := by
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
  have hright : ((x : ℂ) + 2 * ((y : ℂ) * Complex.I)) = ⟨x, 2 * y⟩ := by
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
  rw [hmiddle, hright, ← he (show 1 < (⟨x, y⟩ : ℂ).re from hx),
    globalFiniteHeckeEuler_trivial_eq_dedekindZeta F (by simpa using hx),
    norm_mul, norm_mul, norm_pow, norm_pow] at hprod
  have htriangle : ‖L ⟨x, y⟩‖ ≤ ‖L ⟨1, y⟩‖ + (V y ^ 11)⁻¹ := by
    calc
      _ ≤ ‖L ⟨1, y⟩‖ + ‖L ⟨x, y⟩ - L ⟨1, y⟩‖ := by
        linarith [norm_sub_norm_le (L ⟨x, y⟩) (L ⟨1, y⟩)]
      _ ≤ ‖L ⟨1, y⟩‖ + V y * step y := add_le_add_right hDiff _
      _ = _ := by dsimp [step]; field_simp
  refine ⟨hy₁, ?_⟩
  rw [pow_mul]
  exact reciprocal_lower_bound hVy (norm_nonneg _) (norm_nonneg _)
    (norm_nonneg _) hzeta hsquare htriangle hprod

include μ hν in
/-- Theorem B.6.1.6. The finite continuation is nonzero on the line of real
part one at large absolute heights, and its reciprocal grows polynomially. -/
theorem exists_manuscriptFiniteHecke_inv_polynomial_oneLine (χ : PontryaginDual (IdeleClass F)) :
    ∃ (L : ℂ → ℂ) (N : ℕ) (C T : ℝ), 0 < N ∧ 0 < C ∧ MeromorphicOn L univ ∧
      EqOn L (manuscriptFiniteHeckeEuler F χ) {z | 1 < z.re} ∧
      ∀ y : ℝ, T ≤ |y| → L ⟨1, y⟩ ≠ 0 ∧ ‖(L ⟨1, y⟩)⁻¹‖ ≤ C * |y| ^ N := by
  obtain ⟨t, ht, _⟩ := existsUnique_heckeHeight F χ
  obtain ⟨f, N, hN, hm, he, _, _, hb⟩ :=
    exists_globalFiniteHecke_oneLine_lower_bound F ν η μ hν (heckeNormOneRestriction F χ)
  obtain ⟨R, hR⟩ := eventually_atTop.mp (eventually_comap.mp hb)
  let q (z : ℂ) := z - (t : ℂ) * Complex.I
  have hre (z : ℂ) : (q z).re = z.re := by simp [q, Complex.sub_re, Complex.mul_re]
  refine ⟨f ∘ q, N, (1 + |t|) ^ N, max R 1 + |t|, hN, by positivity,
    fun z _ ↦ (hm (q z) (mem_univ _)).comp_analyticAt (g := q) (analyticAt_id.sub analyticAt_const),
    ?_, ?_⟩
  · intro z hz
    rw [manuscriptFiniteHeckeEuler_shift F χ ht]
    exact he (show 1 < (q z).re by rwa [hre])
  · intro y hy
    have ht₀ : 1 ≤ |y| := by linarith [le_max_right R (1 : ℝ), abs_nonneg t]
    have hR' : R ≤ |y - t| := by linarith [le_max_left R (1 : ℝ), abs_sub_abs_le_abs_sub y t]
    obtain ⟨h₁, h⟩ := hR _ hR' (y - t) rfl
    have hq : q ⟨1, y⟩ = ⟨1, y - t⟩ := by
      apply Complex.ext <;> simp [q, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im]
    have h₀ : 0 < |y - t| ^ N := pow_pos (zero_lt_one.trans_le h₁) _
    have hf : 0 < ‖f ⟨1, y - t⟩‖ := (inv_pos.mpr h₀).trans_le h
    change f (q ⟨1, y⟩) ≠ 0 ∧ ‖(f (q ⟨1, y⟩))⁻¹‖ ≤ (1 + |t|) ^ N * |y| ^ N
    rw [hq, norm_inv]
    refine ⟨norm_pos_iff.mp hf, ((inv_le_comm₀ hf h₀).mpr h).trans ?_⟩
    rw [← mul_pow]
    apply pow_le_pow_left₀ (abs_nonneg _) _ _
    nlinarith [abs_sub y t, mul_nonneg (abs_nonneg t) (sub_nonneg.mpr ht₀)]

end

end Masullo
