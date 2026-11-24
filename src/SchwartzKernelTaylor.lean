import OperatorTaylorEstimate
import SchwartzPartialIntegral
import Mathlib.Analysis.Complex.Exponential

open Filter MeasureTheory
open scoped NNReal SchwartzMap Topology

namespace Masullo

noncomputable section

variable {X Y T : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [MeasurableSpace T]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  {μ : Measure T} {γ : T → X}

omit [NormedSpace ℝ X] [SecondCountableTopology X] in
private theorem kernelMajorant_aestronglyMeasurable (hγ : Measurable γ)
    {w : T → ℂ} (hw : AEStronglyMeasurable w μ) (m : ℕ) :
    AEStronglyMeasurable (schwartzKernelMajorant γ w m) μ := by
  unfold schwartzKernelMajorant
  exact (hw.norm.aemeasurable.div ((measurable_const.max (hγ.norm.pow_const m)).aemeasurable)).aestronglyMeasurable

omit [NormedSpace ℝ X] [MeasurableSpace T] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] in
private theorem kernelMajorant_nonneg (w : T → ℂ) (m : ℕ) (t : T) :
    0 ≤ schwartzKernelMajorant γ w m t := by
  unfold schwartzKernelMajorant
  positivity

/-- An integrated quadratic bound for the kernel yields a quadratic bound
in every continuous Schwartz seminorm on the resulting operators. -/
theorem schwartzKernel_hasOperatorTaylorEstimate
    (hγ : Measurable γ) (m : ℕ) {c : ℂ}
    {A : ℂ → 𝓢(X × Y, ℂ) →L[ℂ] 𝓢(Y, ℂ)} {w : ℂ → T → ℂ} {d : T → ℂ}
    (hw : ∀ z, AEStronglyMeasurable (w z) μ) (hd : AEStronglyMeasurable d μ)
    (h0 : Integrable (schwartzKernelMajorant γ (w c) m) μ)
    (hD : Integrable (schwartzKernelMajorant γ d m) μ)
    (hI : ∀ᶠ h : ℂ in 𝓝 0, Integrable (schwartzKernelMajorant γ (w (c + h)) m) μ)
    (hA : ∀ᶠ h : ℂ in 𝓝 0, ∀ (f : 𝓢(X × Y, ℂ)) y,
      A (c + h) f y = ∫ t, w (c + h) t * f (γ t, y) ∂μ)
    {H : T → ℝ} (hH : Integrable H μ) (hH₀ : ∀ᵐ t ∂μ, 0 ≤ H t)
    (hR : ∀ᶠ h : ℂ in 𝓝 0, ∀ᵐ t ∂μ,
      schwartzKernelMajorant γ (fun t => w (c + h) t - w c t - h * d t) m t ≤ ‖h‖ ^ 2 * H t) :
    HasOperatorTaylorEstimate A c (schwartzPartialIntegralCLM hγ hd hD) := by
  have hAc (f : 𝓢(X × Y, ℂ)) (y : Y) : A c f y = ∫ t, w c t * f (γ t, y) ∂μ := by
    simpa only [add_zero] using hA.self_of_nhds f y
  apply HasOperatorTaylorEstimate.of_seminormFamily (schwartz_withSeminorms ℂ Y ℂ)
  rintro ⟨k, n⟩
  let J : Finset (ℕ × ℕ) := {(k, n), (k + m, n)}
  let p := J.sup (schwartzSeminormFamily ℂ (X × Y) ℂ)
  let C : ℝ≥0 := ⟨∫ t, H t ∂μ, integral_nonneg_of_ae hH₀⟩
  have hp : Continuous p := Seminorm.continuous_finsetSup
    (fun i _ => (schwartz_withSeminorms ℂ (X × Y) ℂ).continuous_seminorm i)
  refine ⟨C • p, hp.const_smul C, ?_⟩
  filter_upwards [hI, hA, hR] with h hi ha hr f
  let R : T → ℂ := fun t => w (c + h) t - w c t - h * d t
  have hRm : AEStronglyMeasurable R μ := ((hw (c + h)).sub (hw c)).sub (hd.const_mul h)
  have hRI : Integrable (schwartzKernelMajorant γ R m) μ :=
    (hH.const_mul (‖h‖ ^ 2)).mono_nonneg (kernelMajorant_aestronglyMeasurable hγ hRm m)
      (.of_forall (kernelMajorant_nonneg R m)) hr
  have hEq : A (c + h) f - A c f - h • schwartzPartialIntegralCLM hγ hd hD f =
      schwartzPartialIntegralCLM hγ hRm hRI f := by
    ext y
    simp only [sub_apply, smul_apply, schwartzPartialIntegralCLM_apply, ha f y, hAc f y, smul_eq_mul]
    have i1 := schwartzPartialIntegral_integrable hγ (hw (c + h)) hi f y
    have i0 := schwartzPartialIntegral_integrable hγ (hw c) h0 f y
    have iD := schwartzPartialIntegral_integrable hγ hd hD f y
    have isub : Integrable (fun t => w (c + h) t * f (γ t, y) - w c t * f (γ t, y)) μ := i1.sub i0
    rw [← integral_const_mul, ← integral_sub i1 i0, ← integral_sub isub (iD.const_mul h)]
    apply integral_congr_ae
    exact .of_forall fun t => by dsimp [R]; ring
  rw [hEq]
  apply (schwartzPartialIntegralCLM_seminorm_le hγ hRm hRI f k n).trans
  change (∫ t, schwartzKernelMajorant γ R m t ∂μ) * p f ≤ ‖h‖ ^ 2 * (C • p) f
  simp only [smul_apply, NNReal.smul_def, smul_eq_mul]
  rw [← mul_assoc]
  apply mul_le_mul_of_nonneg_right _ (apply_nonneg p f)
  change _ ≤ ‖h‖ ^ 2 * ∫ t, H t ∂μ
  rw [← integral_const_mul]
  exact integral_mono_ae hRI (hH.const_mul _) hr

private theorem norm_exp_sub_one_sub_le (z : ℂ) :
    ‖Complex.exp z - 1 - z‖ ≤ 3 * ‖z‖ ^ 2 * Real.exp ‖z‖ := by
  have h₀ := norm_nonneg z
  have he := Real.one_le_exp h₀
  by_cases hz : ‖z‖ ≤ 1
  · exact (Complex.norm_exp_sub_one_sub_id_le hz).trans (by nlinarith [sq_nonneg ‖z‖])
  · have h₁ : ‖z‖ ≤ Real.exp ‖z‖ := by linarith [Real.add_one_le_exp ‖z‖]
    have h₂ : 1 ≤ ‖z‖ ^ 2 := by nlinarith [le_of_not_ge hz]
    calc
      _ ≤ (‖Complex.exp z‖ + 1) + ‖z‖ := by
        exact (norm_sub_le _ _).trans (add_le_add (by simpa using norm_sub_le (Complex.exp z) 1) le_rfl)
      _ ≤ 3 * Real.exp ‖z‖ := by linarith [Complex.norm_exp_le_exp_norm z]
      _ ≤ _ := by nlinarith [Real.exp_nonneg ‖z‖]

/-- Exponential kernels with a spare exponential moment admit an operator
Taylor estimate. The derivative inserts the logarithmic coordinate. -/
theorem schwartzKernel_exp_hasOperatorTaylorEstimate
    (hγ : Measurable γ) (m : ℕ) {c : ℂ}
    {A : ℂ → 𝓢(X × Y, ℂ) →L[ℂ] 𝓢(Y, ℂ)} {w : ℂ → T → ℂ} {ell : T → ℝ}
    (hw : ∀ z, AEStronglyMeasurable (w z) μ) (hell : Measurable ell)
    (h0 : Integrable (schwartzKernelMajorant γ (w c) m) μ)
    (hI : ∀ᶠ h : ℂ in 𝓝 0, Integrable (schwartzKernelMajorant γ (w (c + h)) m) μ)
    (hA : ∀ᶠ h : ℂ in 𝓝 0, ∀ (f : 𝓢(X × Y, ℂ)) y,
      A (c + h) f y = ∫ t, w (c + h) t * f (γ t, y) ∂μ)
    (hpow : ∀ᶠ h : ℂ in 𝓝 0, ∀ᵐ t ∂μ, w (c + h) t = w c t * Complex.exp (h * (ell t : ℂ)))
    {ρ : ℝ} (hρ : 0 < ρ)
    (hM : Integrable (fun t => schwartzKernelMajorant γ (w c) m t *
      Real.exp ((2 * ρ) * |ell t|)) μ) :
    ∃ D, HasOperatorTaylorEstimate A c D := by
  let B (t : T) := schwartzKernelMajorant γ (w c) m t * Real.exp ((2 * ρ) * |ell t|)
  let d (t : T) := w c t * (ell t : ℂ)
  have hB₀ (t : T) : 0 ≤ B t := mul_nonneg (kernelMajorant_nonneg _ _ _) (Real.exp_nonneg _)
  have hdm : AEStronglyMeasurable d μ :=
    (hw c).mul (Complex.continuous_ofReal.measurable.comp hell).aestronglyMeasurable
  have hdi : Integrable (schwartzKernelMajorant γ d m) μ := by
    apply (hM.const_mul (2 * ρ)⁻¹).mono_nonneg (kernelMajorant_aestronglyMeasurable hγ hdm m)
      (.of_forall (kernelMajorant_nonneg d m))
    apply Eventually.of_forall
    intro t
    have h := Real.add_one_le_exp ((2 * ρ) * |ell t|)
    have hle : |ell t| ≤ (2 * ρ)⁻¹ * Real.exp ((2 * ρ) * |ell t|) := by
      rw [← div_eq_inv_mul]
      exact (le_div_iff₀ (by positivity)).mpr (by linarith)
    change schwartzKernelMajorant γ d m t ≤ (2 * ρ)⁻¹ * B t
    have he : schwartzKernelMajorant γ d m t =
        |ell t| * schwartzKernelMajorant γ (w c) m t := by
      unfold schwartzKernelMajorant
      dsimp only [d]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      ring
    rw [he]
    calc
      _ ≤ ((2 * ρ)⁻¹ * Real.exp ((2 * ρ) * |ell t|)) *
          schwartzKernelMajorant γ (w c) m t :=
        mul_le_mul_of_nonneg_right hle (kernelMajorant_nonneg _ _ _)
      _ = _ := by dsimp [B]; ring
  let H (t : T) := (6 / ρ ^ 2) * B t
  have hHI : Integrable H μ := hM.const_mul _
  have hH₀ : ∀ᵐ t ∂μ, 0 ≤ H t :=
    .of_forall fun t => mul_nonneg (by positivity) (hB₀ t)
  refine ⟨schwartzPartialIntegralCLM hγ hdm hdi,
    schwartzKernel_hasOperatorTaylorEstimate hγ m hw hdm h0 hdi hI hA hHI hH₀ ?_⟩
  filter_upwards [hpow, Metric.ball_mem_nhds (0 : ℂ) hρ] with h hh hball
  filter_upwards [hh] with t ht
  let u := |ell t|
  have hu : 0 ≤ u := abs_nonneg _
  have hsmall : ‖h‖ ≤ ρ := by
    exact (by simpa only [Metric.mem_ball, dist_zero_right] using hball : ‖h‖ < ρ).le
  have hnorm : ‖h * (ell t : ℂ)‖ = ‖h‖ * u := by simp [u, Real.norm_eq_abs]
  have hex : Real.exp (‖h‖ * u) ≤ Real.exp (ρ * u) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hsmall hu)
  have hquad : u ^ 2 ≤ (2 / ρ ^ 2) * Real.exp (ρ * u) := by
    have h := Real.quadratic_le_exp_of_nonneg (show 0 ≤ ρ * u by positivity)
    rw [div_mul_eq_mul_div, le_div_iff₀ (sq_pos_of_pos hρ)]
    nlinarith
  have he : w (c + h) t - w c t - h * d t =
      w c t * (Complex.exp (h * (ell t : ℂ)) - 1 - h * (ell t : ℂ)) := by rw [ht]; dsimp [d]; ring
  have hR : ‖Complex.exp (h * (ell t : ℂ)) - 1 - h * (ell t : ℂ)‖ ≤
      ‖h‖ ^ 2 * ((6 / ρ ^ 2) * Real.exp ((2 * ρ) * u)) := by
    calc
      _ ≤ 3 * (‖h‖ * u) ^ 2 * Real.exp (‖h‖ * u) := by
        simpa only [hnorm] using norm_exp_sub_one_sub_le (h * (ell t : ℂ))
      _ ≤ 3 * (‖h‖ * u) ^ 2 * Real.exp (ρ * u) := mul_le_mul_of_nonneg_left hex (by positivity)
      _ = (3 * ‖h‖ ^ 2 * u ^ 2) * Real.exp (ρ * u) := by ring
      _ ≤ (3 * ‖h‖ ^ 2 * ((2 / ρ ^ 2) * Real.exp (ρ * u))) * Real.exp (ρ * u) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hquad (by positivity)) (Real.exp_nonneg _)
      _ = _ := by rw [show (2 * ρ) * u = ρ * u + ρ * u by ring, Real.exp_add]; ring
  change ‖w (c + h) t - w c t - h * d t‖ / max 1 (‖γ t‖ ^ m) ≤ ‖h‖ ^ 2 * H t
  rw [he, norm_mul]
  calc
    _ = schwartzKernelMajorant γ (w c) m t *
        ‖Complex.exp (h * (ell t : ℂ)) - 1 - h * (ell t : ℂ)‖ := by unfold schwartzKernelMajorant; ring
    _ ≤ _ := (mul_le_mul_of_nonneg_left hR (kernelMajorant_nonneg _ _ _)).trans_eq (by
      dsimp [H, B, u]
      ring)


end

end Masullo
