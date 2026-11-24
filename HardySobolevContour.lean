import HardySobolevMellin
import MellinPolynomialInversion

open Filter Function MeasureTheory Set Topology
open scoped ContDiff ENNReal FourierTransform

namespace Masullo

noncomputable section

local notation "planePoint" =>
  (fun (x y : ℝ) => (x : ℂ) + (y : ℂ) * Complex.I)

private theorem exists_small_integrable_above {f : ℝ → ℝ} (hf : Integrable f)
    (R : ℝ) {ε : ℝ} (hε : 0 < ε) : ∃ y > R, f y < ε := by
  by_contra! h
  let μ := (volume : Measure ℝ).restrict (Ioi R)
  have hi : Integrable (fun _ : ℝ => ε) μ := by
    refine hf.integrableOn.mono' aestronglyMeasurable_const ?_
    filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ioi] with y hy
    simpa only [Real.norm_of_nonneg hε.le] using h y hy
  have hfin := (integrable_const_iff_isFiniteMeasure hε.ne').mp hi
  apply hfin.measure_univ_lt_top.ne
  change (volume.restrict (Ioi R)) univ = (⊤ : ℝ≥0∞)
  rw [Measure.restrict_apply_univ, Real.volume_Ioi]

/-- A holomorphic integrand which is absolutely integrable on the strip and
on its two vertical edges has the same integral on those edges. -/
theorem verticalTrace_integral_eq_of_strip_integrable {K : ℂ → ℂ} {c d : ℝ} (hcd : c ≤ d)
    (hK : DifferentiableOn ℂ K (Complex.re ⁻¹' Icc c d))
    (hc : Complex.VerticalIntegrable K c) (hd : Complex.VerticalIntegrable K d)
    (hStrip : Integrable (fun p : ℝ × ℝ => K (planePoint p.1 p.2))
      (((volume : Measure ℝ).restrict (Ioc c d)).prod volume)) :
    (∫ y : ℝ, K (planePoint d y)) = ∫ y : ℝ, K (planePoint c y) := by
  let p (y : ℝ) := ∫ x in Ioc c d, ‖K (planePoint x y)‖
  have hp : Integrable p := hStrip.norm.integral_prod_right
  let ε (n : ℕ) := 1 / ((n : ℝ) + 1)
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  choose hi hhi hhi' using fun n : ℕ => exists_small_integrable_above hp n (hε n)
  have hneg : Integrable (fun y : ℝ => p (-y)) :=
    (Measure.measurePreserving_neg (volume : Measure ℝ)).integrable_comp_of_integrable hp
  choose low hlo hlo' using fun n : ℕ => exists_small_integrable_above hneg n (hε n)
  have hhiTop : Tendsto hi atTop atTop :=
    tendsto_atTop_mono (fun n => (hhi n).le) tendsto_natCast_atTop_atTop
  have hlowTop : Tendsto low atTop atTop :=
    tendsto_atTop_mono (fun n => (hlo n).le) tendsto_natCast_atTop_atTop
  have hloBot : Tendsto (fun n => -low n) atTop atBot :=
    tendsto_neg_atTop_atBot.comp hlowTop
  have hbound (y : ℝ) : ‖∫ x in c..d, K (planePoint x y)‖ ≤ p y := by
    rw [intervalIntegral.integral_of_le hcd]
    exact norm_integral_le_integral_norm _
  have hlim {f : ℕ → ℝ} (h : ∀ n, p (f n) < ε n) :
      Tendsto (fun n => ∫ x in c..d, K (planePoint x (f n))) atTop (𝓝 0) :=
    squeeze_zero_norm' (.of_forall fun n => (hbound (f n)).trans (h n).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  exact verticalTrace_integral_eq_of_contour_limits hcd hK hc hd hloBot hhiTop (hlim hlo') (hlim hhi')

private theorem vertical_product_integrable {F G : ℂ → ℂ} {r : ℝ}
    (hF : MemLp (fun y => F (planePoint r y)) 2 volume)
    (hG : MemLp (fun y => G (planePoint r y)) 2 volume) :
    Integrable (fun y => F (planePoint r y) * G (planePoint r y)) := by
  exact hF.integrable_mul hG

/-- A product of functions with bounded L² norms on the vertical slices of
a finite strip has a contour-independent vertical integral. -/
theorem verticalTrace_integral_mul_eq_of_uniformL2 {F G : ℂ → ℂ} {c d A B : ℝ} (hcd : c ≤ d)
    (hF : DifferentiableOn ℂ F (Complex.re ⁻¹' Icc c d))
    (hG : DifferentiableOn ℂ G (Complex.re ⁻¹' Icc c d))
    (hFL : ∀ r ∈ Icc c d, MemLp (fun y => F (planePoint r y)) 2 volume ∧
      (∫ y, ‖F (planePoint r y)‖ ^ 2) ≤ A)
    (hGL : ∀ r ∈ Icc c d, MemLp (fun y => G (planePoint r y)) 2 volume ∧
      (∫ y, ‖G (planePoint r y)‖ ^ 2) ≤ B) :
    (∫ y : ℝ, F (planePoint d y) * G (planePoint d y)) =
      ∫ y : ℝ, F (planePoint c y) * G (planePoint c y) := by
  let K (z : ℂ) := F z * G z
  let μ := (volume : Measure ℝ).restrict (Ioc c d)
  let P (x : ℝ × ℝ) := K (planePoint x.1 x.2)
  have hK : DifferentiableOn ℂ K (Complex.re ⁻¹' Icc c d) := hF.mul hG
  change (∫ y : ℝ, K (planePoint d y)) = ∫ y : ℝ, K (planePoint c y)
  have hr (x y : ℝ) : (planePoint x y).re = x := by
    simp [Complex.mul_re]
  have atLine (r : ℝ) (h : r ∈ Icc c d) : Integrable fun y => K (planePoint r y) :=
    vertical_product_integrable (hFL r h).1 (hGL r h).1
  apply verticalTrace_integral_eq_of_strip_integrable hcd hK
    (atLine c ⟨le_rfl, hcd⟩) (atLine d ⟨hcd, le_rfl⟩)
  have hP : AEStronglyMeasurable P (μ.prod volume) := by
    have hcomp : ContinuousOn P ((Ioc c d) ×ˢ (univ : Set ℝ)) :=
      hK.continuousOn.comp (by fun_prop) (fun x hx => by
        change (planePoint x.1 x.2).re ∈ Icc c d
        rw [hr]
        exact Ioc_subset_Icc_self hx.1)
    rw [show μ = (volume : Measure ℝ).restrict (Ioc c d) from rfl, Measure.restrict_prod_eq_prod_univ]
    exact hcomp.aestronglyMeasurable (measurableSet_Ioc.prod MeasurableSet.univ)
  have hAE : ∀ᵐ x ∂μ, x ∈ Icc c d :=
    (ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ioc).mono
      fun _ hx => Ioc_subset_Icc_self hx
  change Integrable P (μ.prod volume)
  refine (integrable_prod_iff hP).mpr ⟨hAE.mono atLine, ?_⟩
  haveI : IsFiniteMeasure μ :=
    ⟨by
      change ((volume : Measure ℝ).restrict (Ioc c d)) univ < (⊤ : ℝ≥0∞)
      rw [Measure.restrict_apply_univ, Real.volume_Ioc]
      exact ENNReal.ofReal_lt_top⟩
  refine (integrable_const (A + B)).mono' hP.norm.integral_prod_right' ?_
  filter_upwards [hAE] with x hx
  let f := fun y => F (planePoint x y)
  let g := fun y => G (planePoint x y)
  have hf := (memLp_two_iff_integrable_sq_norm (hFL x hx).1.aestronglyMeasurable).mp (hFL x hx).1
  have hg := (memLp_two_iff_integrable_sq_norm (hGL x hx).1.aestronglyMeasurable).mp (hGL x hx).1
  change ‖∫ y : ℝ, ‖f y * g y‖‖ ≤ A + B
  rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
  calc
    _ ≤ ∫ y : ℝ, (‖f y‖ ^ 2 + ‖g y‖ ^ 2) := by
      apply integral_mono (atLine x hx).norm (hf.add hg)
      intro y
      change ‖f y * g y‖ ≤ ‖f y‖ ^ 2 + ‖g y‖ ^ 2
      rw [norm_mul]
      nlinarith [sq_nonneg (‖f y‖ - ‖g y‖), mul_nonneg (norm_nonneg (f y)) (norm_nonneg (g y))]
    _ ≤ _ := by
      rw [integral_add hf hg]
      exact add_le_add (hFL x hx).2 (hGL x hx).2

/-- Pairing a holomorphic function with the reflected Mellin transform of a
compactly supported smooth logarithmic probe is independent of the line,
whenever the function has uniformly bounded L² traces on the intervening strip. -/
theorem verticalTrace_pairing_eq_of_uniformL2 {F : ℂ → ℂ} {c d A : ℝ} (hcd : c ≤ d)
    (hF : DifferentiableOn ℂ F (Complex.re ⁻¹' Icc c d))
    (hFL : ∀ r ∈ Icc c d, MemLp (fun y => F (planePoint r y)) 2 volume ∧
      (∫ y, ‖F (planePoint r y)‖ ^ 2) ≤ A)
    {ψ : ℝ → ℂ} (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) :
    let G (z : ℂ) := mellin (fun t => ψ (Real.log t)) (-z)
    (∫ y : ℝ, F (planePoint d y) * G (planePoint d y)) =
      ∫ y : ℝ, F (planePoint c y) * G (planePoint c y) := by
  intro G
  let f : PositiveRealExponentialDecay univ :=
    ⟨ψ, mem_logExponentialDecaySubmodule_of_hasCompactSupport univ hcψ hψ⟩
  have hw (r : ℝ) : MellinSchwartzAt (fun t => ψ (Real.log t)) r := by
    apply mellinSchwartzAt_iff_positive_log.mpr
    refine ⟨logExponentialDecayTwist univ ⟨r, mem_univ r⟩ f, ?_⟩
    funext x
    rw [logExponentialDecayTwist_apply, Complex.real_smul, Real.log_exp]
  have hG : Differentiable ℂ G := (mellin_exponential_decay hw).2.1.comp differentiable_neg
  obtain ⟨R, hR⟩ := hcψ.isBounded.exists_norm_le
  let C := Real.exp (2 * max |c| |d| * R)
  have hC (r : ℝ) (hr : r ∈ Icc c d) (x : ℝ) (hx : x ∈ tsupport ψ) :
      Real.exp (2 * (-r) * x) ≤ C := by
    apply Real.exp_le_exp.mpr
    have hrb : |r| ≤ max |c| |d| := abs_le.mpr
      ⟨(neg_le_neg (le_max_left ..)).trans ((neg_abs_le c).trans hr.1),
        hr.2.trans ((le_abs_self d).trans (le_max_right ..))⟩
    calc
      2 * (-r) * x ≤ |2 * (-r) * x| := le_abs_self _
      _ = 2 * |r| * ‖x‖ := by simp [abs_mul, Real.norm_eq_abs]
      _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left hrb (by norm_num)) (hR x hx)
        (norm_nonneg _) (by positivity)
  have hGL (r : ℝ) (hr : r ∈ Icc c d) :
      MemLp (fun y => G (planePoint r y)) 2 volume ∧
        (∫ y, ‖G (planePoint r y)‖ ^ 2) ≤ (2 * Real.pi) * (C * ∫ x, ‖ψ x‖ ^ 2) := by
    have h := mellin_iteratedDeriv_line_energy f 0 (-r)
    let T (y : ℝ) := mellin (fun t => ψ (Real.log t)) (⟨-r, y⟩ : ℂ)
    have hTm : MemLp T 2 volume := h.1
    have hTq : (∫ y, ‖T y‖ ^ 2) =
        (2 * Real.pi) * ∫ x, ‖ψ x‖ ^ 2 * Real.exp (2 * (-r) * x) := by
      simpa only [T, iteratedDeriv_zero, pow_zero, mul_one] using h.2
    have heq : (fun y => G (planePoint r y)) = fun y => T (-y) := by
      funext y
      have hp : -(planePoint r y) = (⟨-r, -y⟩ : ℂ) := by
        apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
      change mellin (fun t => ψ (Real.log t)) (-(planePoint r y)) = _
      rw [hp]
    refine ⟨?_, ?_⟩
    · rw [heq]
      exact hTm.comp_measurePreserving (Measure.measurePreserving_neg (volume : Measure ℝ))
    have hpt (y : ℝ) : G (planePoint r y) = T (-y) := congrFun heq y
    simp_rw [hpt]
    rw [integral_neg_eq_self (fun y : ℝ => ‖T y‖ ^ 2) volume, hTq]
    have hsupport : HasCompactSupport (fun x : ℝ => ‖ψ x‖ ^ 2) := hcψ.comp_left (g := fun z : ℂ => ‖z‖ ^ 2) (by simp)
    have hsq : Integrable (fun x => ‖ψ x‖ ^ 2) := (hψ.continuous.norm.pow 2).integrable_of_hasCompactSupport hsupport
    gcongr
    rw [← integral_const_mul]
    apply integral_mono_of_nonneg (.of_forall fun _ => by positivity) (hsq.const_mul C)
    refine .of_forall fun x => ?_
    change ‖ψ x‖ ^ 2 * Real.exp (2 * (-r) * x) ≤ C * ‖ψ x‖ ^ 2
    by_cases hx : x ∈ tsupport ψ
    · rw [mul_comm C]
      exact mul_le_mul_of_nonneg_left (hC r hr x hx) (sq_nonneg _)
    · simp [image_eq_zero_of_notMem_tsupport hx]
  exact verticalTrace_integral_mul_eq_of_uniformL2 hcd hF hG.differentiableOn hFL hGL

end
end Masullo
