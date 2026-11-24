import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open Filter MeasureTheory Set Topology
open scoped ENNReal

namespace Masullo

/-- After setting x = t - 1, the real local term in §1.8.4.3 has an
inverse-distance singularity. -/
theorem inverse_lintegral_infinite :
    (∫⁻ x in Ioo (0 : ℝ) 1, ENNReal.ofReal x⁻¹) = ∞ := by
  by_contra h
  have hmeas : Measurable (fun x : ℝ => x⁻¹) := by fun_prop
  have hpos : 0 ≤ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] (fun x : ℝ => x⁻¹) := by
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioo] with x hx
    exact inv_nonneg.mpr hx.1.le
  have hi := (lintegral_ofReal_ne_top_iff_integrable hmeas.aestronglyMeasurable hpos).mp h
  have hr : IntegrableOn (fun x : ℝ => x ^ (-1 : ℝ)) (Ioo 0 1) := by
    simpa only [Real.rpow_neg_one, IntegrableOn] using hi
  have := (intervalIntegral.integrableOn_Ioo_rpow_iff (show (0 : ℝ) < 1 by norm_num)).mp hr
  exact (lt_irrefl (-1 : ℝ)) this

/-- Trivial character and z = 3/2. The density relative to dt tends to
1 / (t² (t - 1)) on t > 1. The factor 1/2 is omitted.
The numerator is the regularized test at 1+x divided by √(1+x). -/
theorem no_uniform_real_place_bound
    (numerator : ℕ → ℝ → ℝ) (hmeas : ∀ n, Measurable (numerator n))
    (hlimit : ∀ x ∈ Ioo (0 : ℝ) 1,
      Tendsto (fun n => numerator n x) atTop (𝓝 ((1 + x) ^ 2)⁻¹)) :
    ¬ ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ n,
      (∫⁻ x in Ioo (0 : ℝ) 1, ENNReal.ofReal (numerator n x / x)) ≤ C := by
  rintro ⟨C, hC, hbound⟩
  let μ := volume.restrict (Ioo (0 : ℝ) 1)
  let f (n : ℕ) (x : ℝ) := ENNReal.ofReal (numerator n x / x)
  have hf : ∀ n, Measurable (f n) := fun n => ((hmeas n).div measurable_id).ennreal_ofReal
  have hfatou := lintegral_liminf_le (u := atTop) (μ := μ) hf
  have hliminf : liminf (fun n => ∫⁻ x, f n x ∂μ) atTop ≤ C :=
    liminf_le_of_le (by isBoundedDefault) fun b hb => by
      obtain ⟨n, hn⟩ := hb.exists
      exact hn.trans (hbound n)
  have hlower : (∫⁻ x, ENNReal.ofReal ((1 / 4 : ℝ) * x⁻¹) ∂μ) ≤
      ∫⁻ x, liminf (fun n => f n x) atTop ∂μ := by
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioo] with x hx
    have hconv : Tendsto (fun n => f n x) atTop
        (𝓝 (ENNReal.ofReal (((1 + x) ^ 2)⁻¹ / x))) :=
      (ENNReal.continuous_ofReal.tendsto _).comp ((hlimit x hx).div_const x)
    rw [hconv.liminf_eq]
    apply ENNReal.ofReal_le_ofReal
    rw [div_eq_mul_inv]
    apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr hx.1.le)
    have hsq : (1 + x) ^ 2 ≤ (4 : ℝ) := by nlinarith [hx.1, hx.2, sq_nonneg (1 - x)]
    calc
      (1 / 4 : ℝ) = (4 : ℝ)⁻¹ := by norm_num
      _ ≤ ((1 + x) ^ 2)⁻¹ := inv_anti₀ (pow_pos (by linarith [hx.1]) 2) hsq
  have hinf : (∫⁻ x, ENNReal.ofReal ((1 / 4 : ℝ) * x⁻¹) ∂μ) = ∞ := by
    simp_rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 4)]
    rw [lintegral_const_mul _ (by fun_prop), inverse_lintegral_infinite]
    exact ENNReal.mul_top (by norm_num)
  exact (not_le.mpr hC) (hinf ▸ hlower.trans (hfatou.trans hliminf))

/-- The obstruction applies to ordinary real integrals for nonnegative cutoff
tests, each individually integrable. This writes their actual Haar density in
the variable x = t - 1. -/
theorem no_uniform_cutoff_integral_bound
    (test : ℕ → ℝ → ℝ)
    (hmeas : ∀ n, Measurable (test n))
    (hnonneg : ∀ n x, 0 ≤ test n x)
    (hlimit : ∀ x ∈ Ioo (0 : ℝ) 1,
      Tendsto (fun n => test n (1 + x)) atTop (𝓝 ((1 + x) ^ (-3 / 2 : ℝ))))
    (hint : ∀ n, IntegrableOn
      (fun x => test n (1 + x) * (1 + x) ^ (-1 / 2 : ℝ) / x) (Ioo 0 1)) :
    ¬ ∃ C : ℝ, ∀ n,
      (∫ x in Ioo (0 : ℝ) 1, test n (1 + x) * (1 + x) ^ (-1 / 2 : ℝ) / x) ≤ C := by
  rintro ⟨C, hC⟩
  let numerator (n : ℕ) (x : ℝ) := test n (1 + x) * (1 + x) ^ (-1 / 2 : ℝ)
  have hm : ∀ n, Measurable (numerator n) := by
    intro n
    unfold numerator
    fun_prop
  have hl : ∀ x ∈ Ioo (0 : ℝ) 1,
      Tendsto (fun n => numerator n x) atTop (𝓝 ((1 + x) ^ 2)⁻¹) := by
    intro x hx
    have hx' : 0 < 1 + x := by linarith [hx.1]
    have heq : (1 + x) ^ (-3 / 2 : ℝ) * (1 + x) ^ (-1 / 2 : ℝ) = ((1 + x) ^ 2)⁻¹ := by
      rw [← Real.rpow_add hx', show (-3 / 2 : ℝ) + -1 / 2 = -2 by norm_num,
        Real.rpow_neg hx'.le, Real.rpow_ofNat]
    exact heq ▸ (hlimit x hx).mul_const _
  apply no_uniform_real_place_bound numerator hm hl
  refine ⟨ENNReal.ofReal C, ENNReal.ofReal_lt_top, fun n => ?_⟩
  have hpos : 0 ≤ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] (fun x => numerator n x / x) := by
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioo] with x hx
    exact div_nonneg (mul_nonneg (hnonneg _ _) (Real.rpow_nonneg (by linarith [hx.1]) _)) hx.1.le
  rw [← ofReal_integral_eq_lintegral_ofReal (hint n) hpos]
  exact ENNReal.ofReal_le_ofReal (hC n)

end Masullo
