import HardySobolevHalfline
import Mathlib.Analysis.Convolution

open Function MeasureTheory Set
open scoped ENNReal ContDiff Convolution

namespace Masullo

noncomputable section

/-- Even smooth compactly supported convolution symbols can move a profile
off the finite-norm right-half-line domain. Multiplication by a cutoff
that equals one at the escaped point does not repair the domain. -/
theorem scalarHalfLine_cutoffConvolution_escapes :
    ∃ (φ : ℝ → ℝ) (f : PositiveRealExponentialDecay (univ : Set ℝ)),
      ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ HasCompactSupport f.val ∧
      (∀ a s : ℝ, hardySobolevIntervalENorm volume id (Ici a) s f.val ≠ ⊤) ∧
      ∀ (ρ : ℝ → ℂ), Continuous ρ → ρ 1 = 1 → ∀ a s : ℝ,
        hardySobolevIntervalENorm volume id (Ici a) s
          (fun x => ρ x * ∫ y : ℝ, (φ y : ℂ) * f.val (x - y)) = ⊤ := by
  let b : ContDiffBump (0 : ℝ) := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩
  let e₁ := Homeomorph.addRight (-2 : ℝ)
  let e₂ := Homeomorph.addRight (1 : ℝ)
  let φ (x : ℝ) := b (e₁ x)
  let g (x : ℝ) := b (e₂ x)
  have hφ : ContDiff ℝ ∞ φ := b.contDiff.comp (by change ContDiff ℝ ∞ (fun x : ℝ => x + -2); fun_prop)
  have hg : ContDiff ℝ ∞ g := b.contDiff.comp (by change ContDiff ℝ ∞ (fun x : ℝ => x + 1); fun_prop)
  have hφc : HasCompactSupport φ := b.hasCompactSupport.comp_homeomorph e₁
  have hgc : HasCompactSupport g := b.hasCompactSupport.comp_homeomorph e₂
  have hfc : HasCompactSupport (fun x => (g x : ℂ)) := hgc.comp_left Complex.ofReal_zero
  let f : PositiveRealExponentialDecay (univ : Set ℝ) := ⟨fun x => (g x : ℂ),
    mem_logExponentialDecaySubmodule_of_hasCompactSupport univ hfc (Complex.ofRealCLM.contDiff.comp hg)⟩
  refine ⟨φ, f, hφ, hφc, hfc, ?_, ?_⟩
  · intro a s
    apply (scalarHardySobolev_Ici_finite_iff univ ⟨a, mem_univ a⟩ s f).mpr
    intro x hx
    have hz : g x = 0 := by
      apply b.zero_of_le_dist
      change 1 / 2 ≤ dist (x + 1) 0
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (by linarith)]
      linarith
    change (g x : ℂ) = 0
    simp [hz]
  · intro ρ hρ hρone a s
    let F (x : ℝ) := ∫ y : ℝ, φ y * g (x - y)
    have hF : Continuous F := by
      have he : F = φ ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] g :=
        funext fun _ => convolution_mul.symm
      rw [he]
      exact hgc.continuous_convolution_right (ContinuousLinearMap.mul ℝ ℝ)
        (hφ.continuous.integrable_of_hasCompactSupport hφc).locallyIntegrable hg.continuous
    have hFI (x : ℝ) : Integrable (fun y => φ y * g (x - y)) := by
      have hc : Continuous (fun y => φ y * g (x - y)) :=
        hφ.continuous.mul (hg.continuous.comp (continuous_const.sub continuous_id))
      have hs : HasCompactSupport (φ * fun y => g (x - y)) := hφc.mul_right
      exact hc.integrable_of_hasCompactSupport hs
    have hpos : 0 < F 1 := by
      apply integral_pos_of_integrable_nonneg_nonzero (x := (2 : ℝ))
        (hφ.continuous.mul (hg.continuous.comp (continuous_const.sub continuous_id)))
        (hFI 1) (fun y => mul_nonneg b.nonneg b.nonneg)
      have hone : b 0 = 1 := b.one_of_mem_closedBall (Metric.mem_closedBall_self (by norm_num [b]))
      change b (2 + -2) * b (1 - 2 + 1) ≠ 0
      rw [show (2 : ℝ) + -2 = 0 by norm_num, show (1 : ℝ) - 2 + 1 = 0 by norm_num, hone]
      norm_num
    let D (x : ℝ) := ρ x * (F x : ℂ)
    have hD : Continuous D := hρ.mul (Complex.continuous_ofReal.comp hF)
    have h1 : D 1 ≠ 0 := by
      change ρ 1 * (F 1 : ℂ) ≠ 0
      rw [hρone, one_mul, Complex.ofReal_ne_zero]
      exact hpos.ne'
    have hbad : (volume : Measure ℝ) {x | 0 < id x ∧ D x ≠ 0} ≠ 0 :=
      (isOpen_Ioi.inter (isOpen_ne_fun hD continuous_const)).measure_ne_zero volume
        ⟨1, by norm_num, h1⟩
    have he (x : ℝ) : (ρ x * ∫ y : ℝ, (φ y : ℂ) * f.val (x - y)) = D x := by
      change ρ x * (∫ y : ℝ, (φ y : ℂ) * (g (x - y) : ℂ)) = ρ x * (F x : ℂ)
      simp_rw [← Complex.ofReal_mul, integral_complex_ofReal, F]
    simp_rw [he]
    exact hardySobolevIntervalENorm_Ici_eq_top volume measurable_id hD.measurable hbad a s

end
end Masullo
