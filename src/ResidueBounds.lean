import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Complex.Basic

open Complex Filter MeasureTheory Set
open scoped Topology

namespace Masullo

private theorem tendsto_horizontal_normIntegral {ι : Type*} {l : Filter ι}
    {F Φ : ℂ → ℂ} {a b A C : ℝ} {m : ℕ} {T : ι → ℝ}
    (hA : 0 ≤ A)
    (hT : Tendsto (fun i => |T i|) l atTop)
    (hF : ∀ᶠ i in l, ∀ x ∈ Ioo a b, ‖F ⟨x, T i⟩‖ ≤ A * |T i| ^ m)
    (hΦ : ∀ᶠ i in l, ∀ x ∈ Ioo a b, |T i| ^ (m + 1) * ‖Φ ⟨x, T i⟩‖ ≤ C)
    (hcont : ∀ᶠ i in l, ContinuousOn (fun x => F ⟨x, T i⟩ * Φ ⟨x, T i⟩) (Ioo a b)) :
    Tendsto (fun i => ∫ x in Ioo a b, ‖F ⟨x, T i⟩ * Φ ⟨x, T i⟩‖) l (𝓝 0) := by
  have hlim : Tendsto (fun i => (volume.real (Ioo a b)) * (A * C / |T i|)) l (𝓝 0) := by
    have h := ((tendsto_inv_atTop_zero.comp hT).const_mul (A * C)).const_mul
      (volume.real (Ioo a b))
    simpa only [mul_zero, div_eq_mul_inv, Function.comp_apply] using h
  apply squeeze_zero' (Eventually.of_forall fun _ => integral_nonneg fun _ => norm_nonneg _) _ hlim
  filter_upwards [hF, hΦ, hT.eventually (eventually_gt_atTop 0), hcont] with i hfi hφi hi hci
  have hbound (x : ℝ) (hx : x ∈ Ioo a b) :
      ‖F ⟨x, T i⟩ * Φ ⟨x, T i⟩‖ ≤ A * C / |T i| := by
    rw [norm_mul, le_div_iff₀ hi]
    calc
      ‖F ⟨x, T i⟩‖ * ‖Φ ⟨x, T i⟩‖ * |T i|
          ≤ (A * |T i| ^ m) * ‖Φ ⟨x, T i⟩‖ * |T i| :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (hfi x hx) (norm_nonneg _)) hi.le
      _ = A * (|T i| ^ (m + 1) * ‖Φ ⟨x, T i⟩‖) := by rw [pow_succ]; ring
      _ ≤ A * C := mul_le_mul_of_nonneg_left (hφi x hx) hA
  let μ := volume.restrict (Ioo a b)
  haveI : IsFiniteMeasure μ := ⟨by simp [μ]⟩
  have hi' : Integrable (fun _ : ℝ => A * C / |T i|) μ := integrable_const _
  have hae : ∀ᵐ x ∂μ, x ∈ Ioo a b := ae_restrict_mem measurableSet_Ioo
  have hmeas : AEStronglyMeasurable (fun x => ‖F ⟨x, T i⟩ * Φ ⟨x, T i⟩‖) μ :=
    hci.norm.aestronglyMeasurable measurableSet_Ioo
  have hint := hi'.mono' hmeas (hae.mono fun x hx => by
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    exact hbound x hx)
  have hmain := integral_mono_ae hint hi' (hae.mono hbound)
  change (∫ x in Ioo a b, ‖F ⟨x, T i⟩ * Φ ⟨x, T i⟩‖) ≤
      (∫ _ in Ioo a b, A * C / |T i|) at hmain
  simpa only [setIntegral_const, smul_eq_mul] using hmain

/-- Corrected B.3.1.2. Polynomial growth is measured in the actual height,
and the estimates are required on both the top and bottom contours. -/
theorem asymptotic_residue_horizontal_edges {ι : Type*} {l : Filter ι}
    {F Φ : ℂ → ℂ} {a b A C : ℝ} {m : ℕ} {T : ι → ℝ}
    (hA : 0 ≤ A)
    (hT : Tendsto (fun i => |T i|) l atTop)
    (hF : ∀ᶠ i in l, ∀ x ∈ Ioo a b,
      ‖F ⟨x, T i⟩‖ ≤ A * |T i| ^ m ∧ ‖F ⟨x, -T i⟩‖ ≤ A * |T i| ^ m)
    (hΦ : ∀ᶠ i in l, ∀ x ∈ Ioo a b,
      |T i| ^ (m + 1) * ‖Φ ⟨x, T i⟩‖ ≤ C ∧
      |T i| ^ (m + 1) * ‖Φ ⟨x, -T i⟩‖ ≤ C)
    (hcont : ∀ᶠ i in l,
      ContinuousOn (fun x => F ⟨x, T i⟩ * Φ ⟨x, T i⟩) (Ioo a b) ∧
      ContinuousOn (fun x => F ⟨x, -T i⟩ * Φ ⟨x, -T i⟩) (Ioo a b)) :
    Tendsto (fun i => ∫ x in Ioo a b, ‖F ⟨x, -T i⟩ * Φ ⟨x, -T i⟩‖) l (𝓝 0) ∧
    Tendsto (fun i => ∫ x in Ioo a b, ‖F ⟨x, T i⟩ * Φ ⟨x, T i⟩‖) l (𝓝 0) := by
  refine ⟨tendsto_horizontal_normIntegral (T := fun i => -T i) (C := C) (m := m) hA ?_ ?_ ?_ (hcont.mono fun _ hi => hi.2),
    tendsto_horizontal_normIntegral hA hT
      (hF.mono fun _ hi x hx => (hi x hx).1)
      (hΦ.mono fun _ hi x hx => (hi x hx).1)
      (hcont.mono fun _ hi => hi.1)⟩
  · simpa only [abs_neg] using hT
  · simpa only [abs_neg] using hF.mono fun _ hi x hx => (hi x hx).2
  · simpa only [abs_neg] using hΦ.mono fun _ hi x hx => (hi x hx).2

end Masullo
