import IdelicWeilGammaParameters
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical NumberField

namespace Masullo

noncomputable section

private theorem ofReal_exp_cpow (x : ℝ) (z : ℂ) :
    (Real.exp x : ℂ) ^ z = Complex.exp (z * (x : ℂ)) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero x)),
    ← Complex.ofReal_log (Real.exp_pos x).le, Real.log_exp, mul_comm]

private theorem centeredLogWeight_apply (f : ℝ → ℂ) (x : ℝ) :
    mellinWeight (f ∘ Real.log) (-(1 / 2)) (Real.exp x) =
      Complex.exp (-((x : ℂ) / 2)) * f x := by
  rw [mellinWeight, ofReal_exp_cpow, Function.comp_apply, Real.log_exp, smul_eq_mul]
  push_cast
  congr 2
  ring

/-- At positive and negative log norms the half-modulus in the centered
Mellin test adds one half to each of the two gamma shifts. -/
theorem localGammaExplicitKernel_centered_log (k : ℝ) (b b' : ℂ) (f : ℝ → ℂ) (t : ℝ) :
    localGammaExplicitKernel k b b' (mellinWeight (f ∘ Real.log) (-(1 / 2))) t =
      (k : ℂ) * ((2 * f 0 * Complex.exp (-(t : ℂ)) -
        Complex.exp (-(b + 1 / 2) * ((k * t : ℝ) : ℂ)) * f (k * t) -
        Complex.exp (-(b' + 1 / 2) * ((k * t : ℝ) : ℂ)) * f (-(k * t))) /
        (1 - Complex.exp (-(t : ℂ)))) := by
  unfold localGammaExplicitKernel
  have h₀ : mellinWeight (f ∘ Real.log) (-(1 / 2)) 1 = f 0 := by
    simp [mellinWeight]
  rw [h₀, centeredLogWeight_apply f (k * t), centeredLogWeight_apply f (-(k * t)),
    ← mul_assoc, ← Complex.exp_add, ← mul_assoc, ← Complex.exp_add]
  push_cast
  have h₁ : -b * ((k : ℂ) * (t : ℂ)) - ((k : ℂ) * (t : ℂ)) / 2 =
      -(b + 1 / 2) * ((k : ℂ) * (t : ℂ)) := by ring
  have h₂ : -(b' + 1) * ((k : ℂ) * (t : ℂ)) - (-((k : ℂ) * (t : ℂ))) / 2 =
      -(b' + 1 / 2) * ((k : ℂ) * (t : ℂ)) := by ring
  simp only [← sub_eq_add_neg]
  rw [h₁, h₂]

private theorem one_sub_exp_neg_deriv (x : ℝ) :
    HasDerivAt (fun y : ℝ => 1 - Real.exp (-y)) (Real.exp (-x)) x := by
  have hn := (Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)
  have h := (hasDerivAt_const x (1 : ℝ)).sub hn
  change HasDerivAt (fun y : ℝ => 1 - Real.exp (-y)) (0 - Real.exp (-x) * (-1)) x at h
  simpa only [mul_neg, mul_one, zero_sub, neg_neg] using h

private theorem radialCounterterm_data {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun t : ℝ => Real.exp (-t) / (1 - Real.exp (-t))) (Ioi ε) ∧
      (∫ t in Ioi ε, Real.exp (-t) / (1 - Real.exp (-t))) =
        -Real.log (1 - Real.exp (-ε)) := by
  have hpos (t : ℝ) (ht : 0 < t) : 0 < 1 - Real.exp (-t) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos ht))
  have hd (t : ℝ) (ht : t ∈ Ici ε) :
      HasDerivAt (fun x : ℝ => Real.log (1 - Real.exp (-x)))
        (Real.exp (-t) / (1 - Real.exp (-t))) t :=
    (one_sub_exp_neg_deriv t).log (hpos t (hε.trans_le ht)).ne'
  have ht : Tendsto (fun t : ℝ => Real.log (1 - Real.exp (-t))) atTop (𝓝 0) := by
    have he := Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
    have h := tendsto_const_nhds.sub he (a := (1 : ℝ))
    rw [sub_zero] at h
    have hl := (Real.continuousAt_log (x := 1) one_ne_zero).tendsto.comp h
    rw [Real.log_one] at hl
    exact hl
  have hnonneg (t : ℝ) (h : t ∈ Ioi ε) :
      0 ≤ Real.exp (-t) / (1 - Real.exp (-t)) :=
    div_nonneg (Real.exp_pos _).le (hpos t (hε.trans h)).le
  exact ⟨integrableOn_Ioi_deriv_of_nonneg' hd hnonneg ht, by
    rw [integral_Ioi_of_hasDerivAt_of_nonneg' hd hnonneg ht, zero_sub]⟩

/-- Integrating the compensating radial term above a positive cutoff
gives the exact logarithmic counterterm. -/
theorem idelicWeil_radialCounterterm_integral {ε : ℝ} (hε : 0 < ε) :
    (∫ t in Ioi ε, Real.exp (-t) / (1 - Real.exp (-t))) =
      -Real.log (1 - Real.exp (-ε)) :=
  (radialCounterterm_data hε).2

/-- At zero the logarithmic radial counterterm differs from the usual
logarithmic cutoff by a term tending to zero. -/
theorem idelicWeil_radialCounterterm_logLimit :
    Tendsto (fun t : ℝ => Real.log (1 - Real.exp (-t)) - Real.log t) (𝓝[>] 0) (𝓝 0) := by
  have hd : HasDerivAt (fun t : ℝ => 1 - Real.exp (-t)) 1 0 := by
    simpa only [neg_zero, Real.exp_zero] using one_sub_exp_neg_deriv 0
  have hs := hd.tendsto_slope.mono_left
    (nhdsWithin_mono (0 : ℝ) (show Ioi 0 ⊆ ({0} : Set ℝ)ᶜ from
      fun t ht => show t ≠ 0 from ht.ne'))
  simp only [slope_fun_def_field, neg_zero, Real.exp_zero, sub_self, sub_zero] at hs
  have hlog := (Real.continuousAt_log (x := 1) one_ne_zero).tendsto.comp hs
  rw [Real.log_one] at hlog
  refine hlog.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  change Real.log ((1 - Real.exp (-t)) / t) = _
  have hp : 0 < t := ht
  exact Real.log_div (sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos hp))).ne' hp.ne'

/-- An integrable compensated radial kernel is the finite part of the
unsubtracted kernel at the logarithmic cutoff. -/
theorem idelicWeil_radialFinitePart_tendsto (f : ℝ → ℂ) (c : ℂ)
    (hf : IntegrableOn (fun t : ℝ => f t -
      (Real.exp (-t) / (1 - Real.exp (-t))) • c) (Ioi 0)) :
    Tendsto (fun ε : ℝ => (∫ t in Ioi ε, f t) + Real.log ε • c) (𝓝[>] 0)
      (𝓝 (∫ t in Ioi (0 : ℝ), f t - (Real.exp (-t) / (1 - Real.exp (-t))) • c)) := by
  let d (t : ℝ) := Real.exp (-t) / (1 - Real.exp (-t))
  let g (t : ℝ) := f t - d t • c
  let μ := (volume : Measure ℝ).restrict (Ioi 0)
  have hg : Integrable g μ := hf
  have hlim : Tendsto (fun ε : ℝ => ∫ t, (Ioi ε).indicator g t ∂μ) (𝓝[>] 0)
      (𝓝 (∫ t, g t ∂μ)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun t => ‖g t‖)
      (.of_forall fun ε => hg.aestronglyMeasurable.indicator measurableSet_Ioi)
      (.of_forall fun ε => .of_forall fun t => ?_) hg.norm ?_
    · by_cases ht : t ∈ Ioi ε
      · rw [indicator_of_mem ht]
      · rw [indicator_of_notMem ht, norm_zero]
        exact norm_nonneg _
    · filter_upwards [ae_restrict_mem (μ := volume) (s := Ioi (0 : ℝ)) measurableSet_Ioi] with t ht
      apply tendsto_const_nhds.congr'
      have he := (show ∀ᶠ ε : ℝ in 𝓝 0, ε < t from Iio_mem_nhds ht).filter_mono
        (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
      filter_upwards [he] with ε he
      exact (indicator_of_mem (show t ∈ Ioi ε from he) g).symm
  have hc := (idelicWeil_radialCounterterm_logLimit.neg.smul_const c)
  rw [neg_zero, zero_smul] at hc
  have h := hlim.add hc
  rw [add_zero] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε' : 0 < ε := hε
  rw [integral_indicator measurableSet_Ioi, show μ.restrict (Ioi ε) = (volume : Measure ℝ).restrict (Ioi ε) by
    rw [Measure.restrict_restrict measurableSet_Ioi, inter_eq_left.mpr (Ioi_subset_Ioi hε'.le)]]
  have hd : IntegrableOn d (Ioi ε) := (radialCounterterm_data hε').1
  have hdc : IntegrableOn (fun t => d t • c) (Ioi ε) :=
    Integrable.smul_const hd c
  have hgi : IntegrableOn g (Ioi ε) := hf.mono_set (Ioi_subset_Ioi hε'.le)
  have hfi : IntegrableOn f (Ioi ε) := (hgi.add hdc).congr_fun
    (fun t _ => sub_add_cancel (f t) (d t • c)) measurableSet_Ioi
  change (∫ t in Ioi ε, f t - d t • c) + -(Real.log (1 - Real.exp (-ε)) - Real.log ε) • c = _
  rw [integral_sub hfi hdc, integral_smul_const, show (∫ t in Ioi ε, d t) =
    -Real.log (1 - Real.exp (-ε)) from idelicWeil_radialCounterterm_integral hε']
  simp only [neg_smul, sub_neg_eq_add, neg_sub, sub_smul]
  abel

/-- A positive rescaling of the radial cutoff contributes the exact
logarithm of the scale to its contact term. -/
theorem idelicWeil_radialFinitePart_scaled_tendsto (f : ℝ → ℂ) (c : ℂ) {a : ℝ} (ha : 0 < a)
    (hf : IntegrableOn (fun t : ℝ => f t -
      (Real.exp (-t) / (1 - Real.exp (-t))) • c) (Ioi 0)) :
    Tendsto (fun ε : ℝ => (∫ t in Ioi (a * ε), f t) + Real.log ε • c) (𝓝[>] 0)
      (𝓝 ((∫ t in Ioi (0 : ℝ), f t - (Real.exp (-t) / (1 - Real.exp (-t))) • c) -
        Real.log a • c)) := by
  have hε : Tendsto (fun ε : ℝ => a * ε) (𝓝[>] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have h : ContinuousAt (fun ε : ℝ => a * ε) 0 :=
        ((continuous_const (y := a)).mul continuous_id).continuousAt
      simpa only [mul_zero] using h.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      exact mul_pos ha (show 0 < ε from hε)
  refine (((idelicWeil_radialFinitePart_tendsto f c hf).comp hε).sub_const (Real.log a • c)).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  change (((∫ t in Ioi (a * ε), f t) + Real.log (a * ε) • c) - Real.log a • c) = _
  rw [Real.log_mul ha.ne' (show 0 < ε from hε).ne', add_smul]
  abel

end
end Masullo
