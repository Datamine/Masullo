import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Pi

open Filter MeasureTheory Set
open scoped BigOperators

namespace Masullo

noncomputable section

private theorem integrable_exp_neg_abs (a : ℝ) (ha : 0 < a) :
    Integrable (fun x : ℝ => Real.exp (-a * |x|)) ∧
      (∫ x : ℝ, Real.exp (-a * |x|)) = 2 / a := by
  let f (x : ℝ) := Real.exp (-a * |x|)
  have hleft (x : ℝ) (hx : x ∈ Iic 0) : Real.exp (a * x) = f x := by
    change _ = Real.exp (-a * |x|)
    rw [abs_of_nonpos (mem_Iic.mp hx), neg_mul_neg]
  have hright (x : ℝ) (hx : x ∈ Ioi 0) : Real.exp (-a * x) = f x := by
    change _ = Real.exp (-a * |x|)
    rw [abs_of_pos (mem_Ioi.mp hx)]
  have hi := (integrableOn_exp_mul_Iic ha 0).congr_fun hleft measurableSet_Iic
  have hj := (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr ha) 0).congr_fun hright measurableSet_Ioi
  have hu : Iic (0 : ℝ) ∪ Ioi 0 = univ := Iic_union_Ioi
  have hd : Disjoint (Iic (0 : ℝ)) (Ioi 0) := disjoint_left.mpr fun _ h₁ h₂ => (mem_Ioi.mp h₂).not_ge (mem_Iic.mp h₁)
  constructor
  · rw [← integrableOn_univ, ← hu]
    exact hi.union hj
  · change (∫ x : ℝ, f x) = _
    rw [← setIntegral_univ, ← hu, setIntegral_union hd measurableSet_Ioi hi hj,
      setIntegral_congr_fun measurableSet_Iic (fun x hx => (hleft x hx).symm),
      setIntegral_congr_fun measurableSet_Ioi (fun x hx => (hright x hx).symm),
      integral_exp_mul_Iic ha, integral_exp_mul_Ioi (neg_lt_zero.mpr ha)]
    simp only [mul_zero, Real.exp_zero, neg_div_neg_eq]
    ring

private theorem min_one_exp (x : ℝ) :
    min 1 (Real.exp x) = Real.exp (-max 0 (-x)) := by
  rcases le_total 0 x with hx | hx
  · rw [min_eq_left (Real.one_le_exp hx), max_eq_left (neg_nonpos.mpr hx), neg_zero, Real.exp_zero]
  · rw [min_eq_right (Real.exp_le_one_iff.mpr hx), max_eq_right (neg_nonneg.mpr hx), neg_neg]

/-- Logarithmic kernel for a product of Schwartz estimates on a fixed-norm
archimedean fibre, with one logarithmic coordinate eliminated. -/
def archimedeanLogFibreKernel {ι : Type*} [Fintype ι] (T : ℝ) (u : ι → ℝ) : ℝ :=
  min 1 (Real.exp (T + ∑ i, u i)) * ∏ i, min 1 (Real.exp (-u i))

/-- The fibre kernel is integrable with a bound of degree the number of free
logarithmic coordinates. The estimate includes dimension zero. -/
theorem archimedeanLogFibreKernel_integral_le (ι : Type*) [Fintype ι] (T : ℝ) (hT : 0 ≤ T) :
    Integrable (archimedeanLogFibreKernel (ι := ι) T) ∧
      (∫ u : ι → ℝ, archimedeanLogFibreKernel T u) ≤
        Real.exp 1 * (2 * (Fintype.card ι + 1 : ℝ)) ^ Fintype.card ι * (1 + T) ^ Fintype.card ι := by
  classical
  let n := Fintype.card ι
  let b : ℝ := (n + 1 : ℝ) * (1 + T)
  have hb : 0 < b := by dsimp [b]; positivity
  let P (u : ι → ℝ) := max 0 (-(T + ∑ i, u i)) + ∑ i, max 0 (u i)
  have hP0 (u : ι → ℝ) : 0 ≤ P u :=
    add_nonneg (le_max_left _ _) (Finset.sum_nonneg fun _ _ => le_max_left _ _)
  have hk (u : ι → ℝ) : archimedeanLogFibreKernel T u = Real.exp (-P u) := by
    simp only [archimedeanLogFibreKernel, min_one_exp, neg_neg]
    rw [← Real.exp_sum, ← Real.exp_add, Finset.sum_neg_distrib]
    congr 1
    simp only [P, neg_add]
  have hcoord (u : ι → ℝ) (i : ι) : |u i| ≤ T + P u := by
    have hpos : max 0 (u i) ≤ ∑ j, max 0 (u j) :=
      Finset.single_le_sum (fun j _ => le_max_left 0 (u j)) (Finset.mem_univ i)
    have hsum : ∑ j, u j ≤ u i + ∑ j, max 0 (u j) := by
      have h : ∀ j : ι, u j ≤ (if j = i then u i else 0) + max 0 (u j) := by
        intro j
        split_ifs with hj
        · subst j
          exact le_add_of_nonneg_right (le_max_left _ _)
        · simpa only [zero_add] using le_max_right 0 (u j)
      simpa [Finset.sum_add_distrib] using Finset.sum_le_sum (s := Finset.univ) (fun j _ => h j)
    have hmax : -(T + ∑ j, u j) ≤ max 0 (-(T + ∑ j, u j)) := le_max_right _ _
    have hz : 0 ≤ max 0 (-(T + ∑ j, u j)) := le_max_left _ _
    have hu : u i ≤ max 0 (u i) := le_max_right _ _
    exact abs_le.mpr ⟨by dsimp [P]; linarith, by dsimp [P]; linarith⟩
  let φ (x : ℝ) := Real.exp (-b⁻¹ * |x|)
  obtain ⟨hi, hφ⟩ := integrable_exp_neg_abs b⁻¹ (inv_pos.mpr hb)
  have hiProd : Integrable (fun u : ι → ℝ => ∏ i, φ (u i)) :=
    Integrable.fintype_prod (f := fun _ => φ) (fun _ => hi)
  let M (u : ι → ℝ) := Real.exp 1 * ∏ i, φ (u i)
  have hiM : Integrable M := hiProd.const_mul _
  have hbound (u : ι → ℝ) : archimedeanLogFibreKernel T u ≤ M u := by
    have hs : ∑ i, |u i| ≤ n * (T + P u) := by
      simpa only [n, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hcoord u i)
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
    have ht : T + P u ≤ (1 + T) * (1 + P u) := by
      nlinarith only [mul_nonneg hT (hP0 u)]
    have hs' : ∑ i, |u i| ≤ b * (1 + P u) := by
      dsimp [b]
      calc
        _ ≤ n * (T + P u) := hs
        _ ≤ n * ((1 + T) * (1 + P u)) := mul_le_mul_of_nonneg_left ht hn
        _ ≤ (n + 1 : ℝ) * (1 + T) * (1 + P u) := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_right (by linarith) (by positivity [hP0 u])
    have hexp : -P u ≤ 1 + ∑ i, -b⁻¹ * |u i| := by
      rw [← Finset.mul_sum]
      have hdiv : (∑ i, |u i|) / b ≤ 1 + P u :=
        (div_le_iff₀ hb).mpr (by rwa [mul_comm])
      rw [div_eq_mul_inv] at hdiv
      linarith
    change archimedeanLogFibreKernel T u ≤ Real.exp 1 * ∏ i, Real.exp (-b⁻¹ * |u i|)
    rw [hk, ← Real.exp_sum, ← Real.exp_add]
    exact Real.exp_le_exp.mpr hexp
  have hc : Continuous (archimedeanLogFibreKernel (ι := ι) T) := by
    unfold archimedeanLogFibreKernel
    fun_prop
  have hiK : Integrable (archimedeanLogFibreKernel (ι := ι) T) :=
    hiM.mono' hc.aestronglyMeasurable (.of_forall fun u => by
      rw [hk, Real.norm_of_nonneg (Real.exp_nonneg _)]
      exact (hk u) ▸ hbound u)
  refine ⟨hiK, (integral_mono hiK hiM hbound).trans_eq ?_⟩
  change (∫ u : ι → ℝ, Real.exp 1 * ∏ i, φ (u i)) = _
  rw [integral_const_mul, integral_fintype_prod_volume_eq_prod (fun _ => φ),
    Finset.prod_const, Finset.card_univ, show (∫ x, φ x) = 2 / b⁻¹ from hφ]
  rw [div_eq_mul_inv, inv_inv]
  simp only [b, n, mul_assoc, mul_pow]

end
end Masullo
