import Mathlib.Analysis.Fourier.Convolution

open Complex Filter Function Set Topology
open scoped ContDiff FourierTransform SchwartzMap

namespace Masullo

noncomputable section

/-- A smooth compactly supported frequency profile is a finite sum of
multiples of any family of smooth profiles having no common real zero.
Each multiplier is Schwartz and supported in the support of the target. -/
theorem compactSpectrum_finite_division {ι : Type*}
    (a : ι → ℝ → ℂ) (ha : ∀ i, ContDiff ℝ ∞ (a i))
    (hcover : ∀ x, ∃ i, a i x ≠ 0)
    (b : 𝓢(ℝ, ℂ)) (hb : HasCompactSupport b) :
    ∃ (J : Finset ι) (c : ι → 𝓢(ℝ, ℂ)),
      (∀ i, tsupport (c i : ℝ → ℂ) ⊆ tsupport (b : ℝ → ℂ)) ∧
      ∀ x, (∑ i ∈ J, a i x * c i x) = b x := by
  classical
  let U (i : ι) : Set ℝ := {x | a i x ≠ 0}
  obtain ⟨J, hJ⟩ := hb.elim_finite_subcover U
    (fun i ↦ isOpen_ne_fun (ha i).continuous continuous_const)
    (fun x _ ↦ mem_iUnion.mpr (hcover x))
  let d (x : ℝ) := ∑ i ∈ J, a i x * star (a i x)
  have hd (x : ℝ) (hx : x ∈ tsupport (b : ℝ → ℂ)) : d x ≠ 0 := by
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hJ hx)
    obtain ⟨hiJ, hix⟩ := mem_iUnion.mp hi
    have hpos : 0 < ∑ j ∈ J, Complex.normSq (a j x) :=
      Finset.sum_pos' (fun j _ ↦ Complex.normSq_nonneg (a j x))
        ⟨i, hiJ, Complex.normSq_pos.mpr hix⟩
    change (∑ j ∈ J, a j x * star (a j x)) ≠ 0
    simp_rw [Complex.star_def, Complex.mul_conj]
    rw [← Complex.ofReal_sum]
    exact Complex.ofReal_ne_zero.mpr hpos.ne'
  have haStar (i : ι) : ContDiff ℝ ∞ (fun y ↦ star (a i y)) := by
    change ContDiff ℝ ∞ (Complex.conjCLE ∘ a i)
    exact Complex.conjCLE.contDiff.comp (ha i)
  have hdSmooth : ContDiff ℝ ∞ d :=
    ContDiff.sum fun i _ ↦ (ha i).mul (haStar i)
  let v (i : ι) (x : ℝ) := b x * star (a i x) / d x
  have hvSupp (i : ι) : tsupport (v i) ⊆ tsupport (b : ℝ → ℂ) := by
    apply closure_mono
    intro x hx
    by_contra hn
    have hz : b x = 0 := notMem_support.mp hn
    exact (mem_support.mp hx) (by simp [v, hz])
  have hvDiff (i : ι) : ContDiff ℝ ∞ (v i) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ tsupport (b : ℝ → ℂ)
    · have hs : ContDiffAt ℝ ∞ (b : ℝ → ℂ) x := (b.smooth ⊤).contDiffAt
      have hi : ContDiffAt ℝ ∞ (fun y ↦ (d y)⁻¹) x := hdSmooth.contDiffAt.inv (hd x hx)
      unfold v
      simp only [div_eq_mul_inv]
      exact (hs.mul (haStar i).contDiffAt).mul hi
    · apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
      exact notMem_tsupport_iff_eventuallyEq.mp (fun hm ↦ hx (hvSupp i hm))
  let c (i : ι) : 𝓢(ℝ, ℂ) :=
    HasCompactSupport.toSchwartzMap (f := v i)
      (hb.of_isClosed_subset isClosed_closure (hvSupp i)) (hvDiff i)
  refine ⟨J, c, hvSupp, fun x ↦ ?_⟩
  by_cases hx : x ∈ tsupport (b : ℝ → ℂ)
  · change (∑ i ∈ J, a i x * (b x * star (a i x) / d x)) = b x
    calc
      _ = ∑ i ∈ J, b x / d x * (a i x * star (a i x)) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = b x := by
        rw [← Finset.mul_sum, div_mul_eq_mul_div, mul_div_cancel_right₀ _ (hd x hx)]
  · have hz : b x = 0 := notMem_support.mp (fun hm ↦ hx (subset_closure hm))
    change (∑ i ∈ J, a i x * (b x * star (a i x) / d x)) = b x
    simp [hz]

/-- Every band-limited Schwartz profile is a finite sum of convolutions
of members of a family whose Fourier transforms have no common zero. -/
theorem compactSpectrum_finite_convolution {ι : Type*} (a : ι → 𝓢(ℝ, ℂ))
    (hcover : ∀ x, ∃ i, 𝓕 (a i) x ≠ 0)
    (b : 𝓢(ℝ, ℂ)) (hb : HasCompactSupport (𝓕 b : 𝓢(ℝ, ℂ))) :
    ∃ (J : Finset ι) (c : ι → 𝓢(ℝ, ℂ)),
      (∀ i, HasCompactSupport (𝓕 (c i) : 𝓢(ℝ, ℂ))) ∧
      (∑ i ∈ J, SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) (a i) (c i)) = b := by
  obtain ⟨J, c, hc, he⟩ := compactSpectrum_finite_division
    (fun i ↦ (𝓕 (a i) : 𝓢(ℝ, ℂ))) (fun i ↦ (𝓕 (a i)).smooth ⊤) hcover (𝓕 b) hb
  refine ⟨J, fun i ↦ 𝓕⁻ (c i), ?_, ?_⟩
  · intro i
    rw [FourierTransform.fourier_fourierInv_eq]
    exact hb.of_isClosed_subset isClosed_closure (hc i)
  · apply (FourierTransform.fourierCLE ℂ 𝓢(ℝ, ℂ)).injective
    change 𝓕 (∑ i ∈ J, SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) (a i) (𝓕⁻ (c i))) =
      𝓕 b
    ext x
    rw [FourierTransform.fourier_sum]
    simpa only [_root_.sum_apply, SchwartzMap.fourier_convolution,
      SchwartzMap.pairing_apply_apply, FourierTransform.fourier_fourierInv_eq,
      ContinuousLinearMap.mul_apply'] using he x

end
end Masullo
