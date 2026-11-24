import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

open Filter MeasureTheory
open scoped ENNReal

namespace Masullo

noncomputable section

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)
variable (r : X → ℝ)

/-- The density for a real multiplication amplitude on L². -/
def amplitudeMeasure : Measure X := μ.withDensity (fun x => ENNReal.ofReal (r x ^ 2))

private theorem amplitude_density_measurable (hr : Measurable r) :
    Measurable (fun x => ENNReal.ofReal (r x ^ 2)) := (hr.pow_const 2).ennreal_ofReal

theorem absolutelyContinuous_amplitudeMeasure (hr : Measurable r) (hp : ∀ x, 0 < r x) :
    μ ≪ amplitudeMeasure μ r :=
  withDensity_absolutelyContinuous' (amplitude_density_measurable r hr).aemeasurable
    (.of_forall fun x => ENNReal.ofReal_ne_zero_iff.mpr (sq_pos_of_pos (hp x)))

theorem amplitudeMeasure_absolutelyContinuous :
    amplitudeMeasure μ r ≪ μ := withDensity_absolutelyContinuous _ _

theorem memLp_amplitudeMeasure_iff (hr : Measurable r) {f : X → ℂ}
    (hf : AEStronglyMeasurable f μ) :
    MemLp f 2 (amplitudeMeasure μ r) ↔ MemLp (fun x => r x • f x) 2 μ := by
  rw [memLp_two_iff_integrable_sq_norm (hf.mono_ac (amplitudeMeasure_absolutelyContinuous μ r)),
    memLp_two_iff_integrable_sq_norm
      (show AEStronglyMeasurable (fun x => r x • f x) μ from hr.aestronglyMeasurable.smul hf)]
  unfold amplitudeMeasure
  rw [integrable_withDensity_iff_integrable_smul' (amplitude_density_measurable r hr)
    (.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (sq_nonneg _), smul_eq_mul, norm_smul, mul_pow,
    Real.norm_eq_abs, sq_abs]

private def multiplyAmplitude (hr : Measurable r) (hp : ∀ x, 0 < r x)
    (f : Lp ℂ 2 (amplitudeMeasure μ r)) : Lp ℂ 2 μ :=
  ((memLp_amplitudeMeasure_iff μ r hr
    (Lp.aestronglyMeasurable f |>.mono_ac (absolutelyContinuous_amplitudeMeasure μ r hr hp))).mp
    (Lp.memLp f)).toLp _

private theorem multiplyAmplitude_ae (hr : Measurable r) (hp : ∀ x, 0 < r x)
    (f : Lp ℂ 2 (amplitudeMeasure μ r)) :
    (multiplyAmplitude μ r hr hp f : X → ℂ) =ᵐ[μ] fun x => r x • f x :=
  MemLp.coeFn_toLp _

private def divideAmplitude (hr : Measurable r) (hp : ∀ x, 0 < r x)
    (f : Lp ℂ 2 μ) : Lp ℂ 2 (amplitudeMeasure μ r) :=
  ((memLp_amplitudeMeasure_iff μ r hr (hr.inv.aestronglyMeasurable.smul
    (Lp.aestronglyMeasurable f))).mpr (by
      refine (memLp_congr_ae (g := (f : X → ℂ)) (.of_forall fun x => ?_)).2 (Lp.memLp f)
      change r x • ((r x)⁻¹ • f x) = f x
      rw [smul_smul, mul_inv_cancel₀ (hp x).ne', one_smul])).toLp _

private theorem divideAmplitude_ae (hr : Measurable r) (hp : ∀ x, 0 < r x)
    (f : Lp ℂ 2 μ) :
    (divideAmplitude μ r hr hp f : X → ℂ) =ᵐ[amplitudeMeasure μ r]
      fun x => (r x)⁻¹ • f x :=
  MemLp.coeFn_toLp _

private theorem eLpNorm_amplitude (hr : Measurable r) (hp : ∀ x, 0 < r x)
    {f : X → ℂ} (hf : AEStronglyMeasurable f μ) :
    eLpNorm (fun x => r x • f x) 2 μ = eLpNorm f 2 (amplitudeMeasure μ r) := by
  simp only [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by simp : (2 : ℝ≥0∞) ≠ ∞)]
  unfold amplitudeMeasure
  rw [lintegral_withDensity_eq_lintegral_mul₀ (amplitude_density_measurable r hr).aemeasurable]
  · congr 1
    apply lintegral_congr
    intro x
    simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two, enorm_smul, Pi.mul_apply]
    rw [Real.enorm_eq_ofReal (hp x).le, ENNReal.ofReal_pow (hp x).le, mul_pow]
  · simpa using (hf.aemeasurable.enorm.pow_const (2 : ℕ))

/-- Multiplication by the amplitude identifies the weighted and unweighted
Hilbert spaces, with division by the amplitude as inverse. -/
def amplitudeL2Iso (hr : Measurable r) (hp : ∀ x, 0 < r x) :
    Lp ℂ 2 (amplitudeMeasure μ r) ≃ₗᵢ[ℂ] Lp ℂ 2 μ where
  toFun := multiplyAmplitude μ r hr hp
  invFun := divideAmplitude μ r hr hp
  left_inv f := Lp.ext (by
    filter_upwards [divideAmplitude_ae μ r hr hp (multiplyAmplitude μ r hr hp f),
      (amplitudeMeasure_absolutelyContinuous μ r).ae_le (multiplyAmplitude_ae μ r hr hp f)]
      with x hx hy
    rw [hx, hy, smul_smul, inv_mul_cancel₀ (hp x).ne', one_smul])
  right_inv f := Lp.ext (by
    filter_upwards [multiplyAmplitude_ae μ r hr hp (divideAmplitude μ r hr hp f),
      (absolutelyContinuous_amplitudeMeasure μ r hr hp).ae_le (divideAmplitude_ae μ r hr hp f)]
      with x hx hy
    rw [hx, hy, smul_smul, mul_inv_cancel₀ (hp x).ne', one_smul])
  map_add' f g := Lp.ext (by
    filter_upwards [multiplyAmplitude_ae μ r hr hp (f + g),
      multiplyAmplitude_ae μ r hr hp f, multiplyAmplitude_ae μ r hr hp g,
      (absolutelyContinuous_amplitudeMeasure μ r hr hp).ae_le (Lp.coeFn_add f g),
      Lp.coeFn_add (multiplyAmplitude μ r hr hp f) (multiplyAmplitude μ r hr hp g)]
      with x hfg hf hg hs ht
    simp only [Pi.add_apply] at hs ht
    rw [hfg, ht, hs, hf, hg, smul_add])
  map_smul' c f := Lp.ext (by
    filter_upwards [multiplyAmplitude_ae μ r hr hp (c • f), multiplyAmplitude_ae μ r hr hp f,
      (absolutelyContinuous_amplitudeMeasure μ r hr hp).ae_le (Lp.coeFn_smul c f),
      Lp.coeFn_smul c (multiplyAmplitude μ r hr hp f)] with x hcf hf hs ht
    simp only [Pi.smul_apply] at hs ht
    rw [RingHom.id_apply, hcf, ht, hs, hf, smul_comm])
  norm_map' f := by
    change ‖multiplyAmplitude μ r hr hp f‖ = ‖f‖
    rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (multiplyAmplitude_ae μ r hr hp f)]
    rw [eLpNorm_amplitude μ r hr hp
      (Lp.aestronglyMeasurable f |>.mono_ac (absolutelyContinuous_amplitudeMeasure μ r hr hp))]

theorem amplitudeL2Iso_ae (hr : Measurable r) (hp : ∀ x, 0 < r x)
    (f : Lp ℂ 2 (amplitudeMeasure μ r)) :
    (amplitudeL2Iso μ r hr hp f : X → ℂ) =ᵐ[μ] fun x => r x • f x :=
  multiplyAmplitude_ae μ r hr hp f

theorem amplitudeL2Iso_symm_ae (hr : Measurable r) (hp : ∀ x, 0 < r x)
    (f : Lp ℂ 2 μ) :
    ((amplitudeL2Iso μ r hr hp).symm f : X → ℂ) =ᵐ[amplitudeMeasure μ r]
      fun x => (r x)⁻¹ • f x :=
  divideAmplitude_ae μ r hr hp f

end
end Masullo
