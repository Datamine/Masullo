import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open Filter MeasureTheory MeasureTheory.Measure Set Topology
open scoped ENNReal

noncomputable section

namespace Masullo

/-- The density of the weighted Hilbert space in Remark 9.3.3.2, in log coordinates. -/
def hardySobolevWeight (a b s x : ℝ) : ℝ :=
  max (Real.exp (2 * a * x)) (Real.exp (2 * b * x)) * (1 + x ^ 2) ^ (s / 2)

theorem hardySobolevWeight_nonneg (a b s x : ℝ) : 0 ≤ hardySobolevWeight a b s x := by
  unfold hardySobolevWeight
  exact mul_nonneg ((Real.exp_pos _).le.trans (le_max_left _ _))
    (Real.rpow_nonneg (by positivity) _)

theorem continuous_hardySobolevWeight (a b s : ℝ) :
    Continuous (hardySobolevWeight a b s) := by
  unfold hardySobolevWeight
  exact (by fun_prop : Continuous fun x : ℝ => max (Real.exp (2 * a * x))
    (Real.exp (2 * b * x))).mul
    ((by fun_prop : Continuous fun x : ℝ => 1 + x ^ 2).rpow_const
      fun x => Or.inl (by positivity))

/-- The measure whose L² norm is the manuscript's weighted norm. -/
def hardySobolevMeasure {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (logNorm : X → ℝ) (a b s : ℝ) : Measure X :=
  μ.withDensity (fun x => ENNReal.ofReal (hardySobolevWeight a b s (logNorm x)))

/-- Expanding the interval increases its Hardy–Sobolev density. -/
theorem hardySobolevWeight_mono_interval {a b c d : ℝ}
    (hac : a ≤ c) (hcb : c ≤ b) (had : a ≤ d) (hdb : d ≤ b) (s x : ℝ) :
    hardySobolevWeight c d s x ≤ hardySobolevWeight a b s x := by
  have h (r : ℝ) (har : a ≤ r) (hrb : r ≤ b) :
      Real.exp (2 * r * x) ≤ max (Real.exp (2 * a * x)) (Real.exp (2 * b * x)) := by
    rcases le_total 0 x with hx | hx
    · exact (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_right (by linarith) hx)).trans (le_max_right _ _)
    · exact (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonpos_right (by linarith) hx)).trans (le_max_left _ _)
  exact mul_le_mul_of_nonneg_right (max_le (h c hac hcb) (h d had hdb)) (by positivity)

/-- The extended norm is the supremum of the weighted L² norms over the
compact subintervals. An unbounded interval can give the value infinity. -/
def hardySobolevIntervalENorm {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (logNorm : X → ℝ) (I : Set ℝ) (s : ℝ) (f : X → ℂ) : ℝ≥0∞ :=
  ⨆ (a : I) (b : I), eLpNorm f 2 (hardySobolevMeasure μ logNorm a b s)

private theorem hardySobolevENorm_mono_interval {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (logNorm : X → ℝ) (f : X → ℂ)
    {a b c d : ℝ} (hac : a ≤ c) (hcb : c ≤ b) (had : a ≤ d) (hdb : d ≤ b) (s : ℝ) :
    eLpNorm f 2 (hardySobolevMeasure μ logNorm c d s) ≤
      eLpNorm f 2 (hardySobolevMeasure μ logNorm a b s) :=
  eLpNorm_mono_measure _ (withDensity_mono (.of_forall fun x =>
    ENNReal.ofReal_le_ofReal (hardySobolevWeight_mono_interval hac hcb had hdb s (logNorm x))))

/-- On a compact base the supremum is attained at its two endpoints. -/
theorem hardySobolevIntervalENorm_Icc {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (logNorm : X → ℝ) {a b : ℝ} (hab : a ≤ b) (s : ℝ) (f : X → ℂ) :
    hardySobolevIntervalENorm μ logNorm (Icc a b) s f =
      eLpNorm f 2 (hardySobolevMeasure μ logNorm a b s) := by
  exact le_antisymm (iSup₂_le fun c d =>
    hardySobolevENorm_mono_interval μ logNorm f c.2.1 c.2.2 d.2.1 d.2.2 s)
    (le_iSup₂_of_le ⟨a, left_mem_Icc.mpr hab⟩ ⟨b, right_mem_Icc.mpr hab⟩ le_rfl)

/-- The right half-line norm can be computed with the left endpoint fixed.
Adapted from Apache-2.0 RiemannMasullo commit 7ef9ea9 for 9.2.2.2(3) and 9.2.2.10(3). -/
theorem hardySobolevIntervalENorm_Ici {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (logNorm : X → ℝ) (a s : ℝ) (f : X → ℂ) :
    hardySobolevIntervalENorm μ logNorm (Ici a) s f =
      ⨆ b : Ici a, eLpNorm f 2 (hardySobolevMeasure μ logNorm a b s) := by
  refine le_antisymm (iSup₂_le fun c d => ?_)
    (iSup_le fun b => le_iSup₂_of_le ⟨a, self_mem_Ici⟩ b le_rfl)
  exact le_iSup_of_le (⟨max c d, (show a ≤ (c : ℝ) from c.2).trans (le_max_left _ _)⟩ : Ici a)
    (hardySobolevENorm_mono_interval μ logNorm f c.2 (le_max_left _ _)
      d.2 (le_max_right _ _) s)

/-- The left half-line norm can be computed with the right endpoint fixed.
Adapted from Apache-2.0 RiemannMasullo commit 7ef9ea9. -/
theorem hardySobolevIntervalENorm_Iic {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (logNorm : X → ℝ) (b s : ℝ) (f : X → ℂ) :
    hardySobolevIntervalENorm μ logNorm (Iic b) s f =
      ⨆ a : Iic b, eLpNorm f 2 (hardySobolevMeasure μ logNorm a b s) := by
  refine le_antisymm (iSup₂_le fun c d => ?_)
    (iSup_le fun a => le_iSup₂_of_le a ⟨b, self_mem_Iic⟩ le_rfl)
  exact le_iSup_of_le (⟨min c d, (min_le_left (c : ℝ) (d : ℝ)).trans (show (c : ℝ) ≤ b from c.2)⟩ : Iic b)
    (hardySobolevENorm_mono_interval μ logNorm f (min_le_left _ _) c.2
      (min_le_right _ _) d.2 s)


theorem hardySobolevMeasure_energy {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (logNorm : X → ℝ) (hlog : Measurable logNorm) (a b s : ℝ) (f : X → ℂ) (hf : Measurable f) :
    (∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2) ∂hardySobolevMeasure μ logNorm a b s) =
      ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2 * hardySobolevWeight a b s (logNorm x)) ∂μ := by
  have hw := (continuous_hardySobolevWeight a b s).measurable.comp hlog
  rw [hardySobolevMeasure, lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (by fun_prop)]
  apply lintegral_congr
  intro x
  simp only [Pi.mul_apply, ENNReal.ofReal_mul (sq_nonneg _)]
  exact mul_comm _ _

/-- The constant term in the polynomial weight is necessary at the identity. -/
theorem no_unshifted_translation_bound {s : ℝ} (hs : 0 < s) (C : ℝ) :
    ¬ 1 ≤ C * (0 : ℝ) ^ (s / 2) := by
  rw [Real.zero_rpow (by positivity : s / 2 ≠ 0), mul_zero]
  norm_num

/-- A corrected translation estimate for the squared norm density. -/
theorem hardySobolevWeight_add_le (a b : ℝ) {s : ℝ} (hs : 0 ≤ s) (x y : ℝ) :
    hardySobolevWeight a b s (x + y) ≤
      hardySobolevWeight a b s x * (2 : ℝ) ^ (s / 2) * hardySobolevWeight a b s y := by
  have hpoly : 1 + (x + y) ^ 2 ≤ 2 * (1 + x ^ 2) * (1 + y ^ 2) := by
    nlinarith [sq_nonneg (x - y), mul_nonneg (sq_nonneg x) (sq_nonneg y)]
  have hp := Real.rpow_le_rpow (by positivity : 0 ≤ 1 + (x + y) ^ 2) hpoly
    (div_nonneg hs (by norm_num : 0 ≤ (2 : ℝ)))
  rw [Real.mul_rpow (by positivity : 0 ≤ 2 * (1 + x ^ 2))
    (by positivity : 0 ≤ 1 + y ^ 2), Real.mul_rpow (by norm_num : 0 ≤ (2 : ℝ))
    (by positivity : 0 ≤ 1 + x ^ 2)] at hp
  have hexp (c : ℝ) :
      Real.exp (2 * c * (x + y)) = Real.exp (2 * c * x) * Real.exp (2 * c * y) := by
    rw [mul_add, Real.exp_add]
  have hm : max (Real.exp (2 * a * (x + y))) (Real.exp (2 * b * (x + y))) ≤
      max (Real.exp (2 * a * x)) (Real.exp (2 * b * x)) *
        max (Real.exp (2 * a * y)) (Real.exp (2 * b * y)) := by
    rw [hexp a, hexp b]
    exact max_le (mul_le_mul (le_max_left _ _) (le_max_left _ _)
      (Real.exp_pos _).le ((Real.exp_pos _).le.trans (le_max_left _ _)))
      (mul_le_mul (le_max_right _ _) (le_max_right _ _)
        (Real.exp_pos _).le ((Real.exp_pos _).le.trans (le_max_right _ _)))
  unfold hardySobolevWeight
  exact (mul_le_mul hm hp (Real.rpow_nonneg (by positivity) _)
    (mul_nonneg ((Real.exp_pos _).le.trans (le_max_left _ _))
      ((Real.exp_pos _).le.trans (le_max_left _ _)))).trans_eq (by ring)

section Translation

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]

/-- Integrating the corrected weight estimate against left Haar measure bounds
the squared weighted L² norm of the translated function. -/
theorem hardySobolev_lintegral_translate_le (μ : Measure G) [IsMulLeftInvariant μ]
    (logNorm : G → ℝ) (hlog : Measurable logNorm)
    (hadd : ∀ g y, logNorm (g * y) = logNorm g + logNorm y)
    (a b : ℝ) {s : ℝ} (hs : 0 ≤ s) (g : G) (f : G → ℂ) (hf : Measurable f) :
    (∫⁻ x, ENNReal.ofReal (‖f (g⁻¹ * x)‖ ^ 2 * hardySobolevWeight a b s (logNorm x)) ∂μ) ≤
      ENNReal.ofReal (hardySobolevWeight a b s (logNorm g) * (2 : ℝ) ^ (s / 2)) *
        (∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2 * hardySobolevWeight a b s (logNorm x)) ∂μ) := by
  have hw := (continuous_hardySobolevWeight a b s).measurable.comp hlog
  let E : G → ℝ≥0∞ := fun x => ENNReal.ofReal
    (‖f (g⁻¹ * x)‖ ^ 2 * hardySobolevWeight a b s (logNorm x))
  have hE : Measurable E := by
    dsimp [E]
    fun_prop
  change (∫⁻ x, E x ∂μ) ≤ _
  rw [← (measurePreserving_mul_left μ g).lintegral_comp hE]
  rw [← lintegral_const_mul _ (by fun_prop)]
  apply lintegral_mono
  intro y
  dsimp [E]
  rw [inv_mul_cancel_left, hadd, ← ENNReal.ofReal_mul
    (mul_nonneg (hardySobolevWeight_nonneg ..) (by positivity))]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ ‖f y‖ ^ 2 * (hardySobolevWeight a b s (logNorm g) * (2 : ℝ) ^ (s / 2) *
        hardySobolevWeight a b s (logNorm y)) :=
      mul_le_mul_of_nonneg_left (hardySobolevWeight_add_le a b hs _ _) (sq_nonneg _)
    _ = _ := by ring

end Translation

section Cutoff

variable {X ι : Type*}

/-- The intervals on which a manuscript cutoff equals one eventually contain
each fixed positive value of the group norm. -/
theorem cutoff_eventually_eq_one {l : Filter ι} (radius margin : ι → ℝ)
    (hRadius : Tendsto radius l atTop) (hMargin : Tendsto (fun i => margin i * radius i) l (𝓝 0))
    (ρ : ι → X → ℝ) (groupNorm : X → ℝ) (hpos : ∀ x, 0 < groupNorm x)
    (hplateau : ∀ i x, (radius i)⁻¹ + margin i ≤ groupNorm x →
      groupNorm x ≤ radius i - margin i → ρ i x = 1) (x : X) :
    ∀ᶠ i in l, ρ i x = 1 := by
  have hinv := (tendsto_inv_atTop_zero : Tendsto (fun r : ℝ => r⁻¹) atTop (𝓝 0)).comp hRadius
  have hm : Tendsto margin l (𝓝 0) := by
    have hprod := hMargin.mul hinv
    simp only [mul_zero] at hprod
    apply hprod.congr'
    filter_upwards [hRadius.eventually_ge_atTop 1] with i hi
    exact mul_inv_cancel_right₀ (by linarith : radius i ≠ 0) _
  have hl := (hinv.add hm)
  rw [zero_add] at hl
  have hu : Tendsto (fun i => groupNorm x + margin i) l (𝓝 (groupNorm x + 0)) :=
    tendsto_const_nhds.add hm
  have hsmall := (tendsto_order.mp hl).2 _ (hpos x)
  have hbounded := (tendsto_order.mp hu).2 (groupNorm x + 1) (by linarith)
  filter_upwards [hsmall, hbounded, hRadius.eventually_ge_atTop (groupNorm x + 1)] with i hi hj hk
  exact hplateau i x hi.le (by linarith)

variable [MeasurableSpace X]

/-- Multiplication by a cutoff in [0,1] contracts the squared weighted norm. -/
theorem weightedL2_cutoff_energy_le (μ : Measure X) (weight : X → ℝ)
    (hw₀ : ∀ x, 0 ≤ weight x) (f : X → ℂ) (ρ : X → ℝ)
    (hρ₀ : ∀ x, 0 ≤ ρ x) (hρ₁ : ∀ x, ρ x ≤ 1) :
    (∫⁻ x, ENNReal.ofReal ((ρ x ^ 2 * ‖f x‖ ^ 2) * weight x) ∂μ) ≤
      ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2 * weight x) ∂μ := by
  apply lintegral_mono
  intro x
  apply ENNReal.ofReal_le_ofReal
  have hle : ρ x ^ 2 ≤ 1 := by nlinarith [hρ₀ x, hρ₁ x]
  simpa only [one_mul] using
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hle (sq_nonneg _)) (hw₀ x)

/-- The strong cutoff estimate in squared weighted L² norm for each vector. -/
theorem weightedL2_cutoff_error_tendsto (μ : Measure X) {l : Filter ι} [l.IsCountablyGenerated]
    (weight : X → ℝ) (hw : Measurable weight) (hw₀ : ∀ x, 0 ≤ weight x)
    (f : X → ℂ) (hf : Measurable f)
    (hfin : (∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2 * weight x) ∂μ) ≠ ∞)
    (ρ : ι → X → ℝ) (hρ : ∀ i, Measurable (ρ i))
    (hρ₀ : ∀ i x, 0 ≤ ρ i x) (hρ₁ : ∀ i x, ρ i x ≤ 1)
    (hevent : ∀ x, ∀ᶠ i in l, ρ i x = 1) :
    Tendsto (fun i => ∫⁻ x, ENNReal.ofReal (((1 - ρ i x) ^ 2 * ‖f x‖ ^ 2) * weight x) ∂μ)
      l (𝓝 0) := by
  have h := tendsto_lintegral_filter_of_dominated_convergence
    (μ := μ) (l := l) (F := fun i x => ENNReal.ofReal (((1 - ρ i x) ^ 2 * ‖f x‖ ^ 2) * weight x))
    (f := fun _ => 0) (fun x => ENNReal.ofReal (‖f x‖ ^ 2 * weight x))
    (.of_forall fun i => by have := hρ i; fun_prop) ?_ hfin ?_
  · simpa only [lintegral_zero] using h
  · refine .of_forall fun i => ae_of_all μ fun x => ENNReal.ofReal_le_ofReal ?_
    have hle : (1 - ρ i x) ^ 2 ≤ 1 := by nlinarith [hρ₀ i x, hρ₁ i x]
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hle (sq_nonneg _)) (hw₀ x)
  · refine ae_of_all μ fun x => tendsto_const_nhds.congr' ?_
    filter_upwards [hevent x] with i hi
    simp [hi]

end Cutoff

section CutoffOperator

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

private theorem cutoff_mul_norm_le {r : ℝ} (hr₀ : 0 ≤ r) (hr₁ : r ≤ 1) (z : ℂ) :
    ‖(r : ℂ) * z‖ ≤ ‖z‖ := by
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr₀]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hr₁ (norm_nonneg z)

private theorem cutoff_mul_memLp {ρ : X → ℝ} (hρ : Measurable ρ)
    (hρ₀ : ∀ x, 0 ≤ ρ x) (hρ₁ : ∀ x, ρ x ≤ 1) (f : Lp ℂ 2 μ) :
    MemLp (fun x => (ρ x : ℂ) * f x) 2 μ := by
  have hm : Measurable (fun x => (ρ x : ℂ) * f x) := by
    have hf := (Lp.stronglyMeasurable f).measurable
    exact (Complex.continuous_ofReal.measurable.comp hρ).mul hf
  exact ⟨hm.aestronglyMeasurable, (eLpNorm_mono fun x =>
    cutoff_mul_norm_le (hρ₀ x) (hρ₁ x) (f x)).trans_lt (Lp.eLpNorm_lt_top f)⟩

private def cutoffLinear (ρ : X → ℝ) (hρ : Measurable ρ)
    (hρ₀ : ∀ x, 0 ≤ ρ x) (hρ₁ : ∀ x, ρ x ≤ 1) : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ where
  toFun f := (cutoff_mul_memLp hρ hρ₀ hρ₁ f).toLp _
  map_add' f g := by
    apply Lp.ext
    filter_upwards [(cutoff_mul_memLp hρ hρ₀ hρ₁ (f + g)).coeFn_toLp,
      Lp.coeFn_add ((cutoff_mul_memLp hρ hρ₀ hρ₁ f).toLp _)
        ((cutoff_mul_memLp hρ hρ₀ hρ₁ g).toLp _),
      (cutoff_mul_memLp hρ hρ₀ hρ₁ f).coeFn_toLp,
      (cutoff_mul_memLp hρ hρ₀ hρ₁ g).coeFn_toLp, Lp.coeFn_add f g] with x h₁ h₂ h₃ h₄ h₅
    simp only [Pi.add_apply] at h₂ h₅
    rw [h₁, h₂, h₃, h₄, h₅, mul_add]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [(cutoff_mul_memLp hρ hρ₀ hρ₁ (c • f)).coeFn_toLp,
      Lp.coeFn_smul c ((cutoff_mul_memLp hρ hρ₀ hρ₁ f).toLp _),
      (cutoff_mul_memLp hρ hρ₀ hρ₁ f).coeFn_toLp, Lp.coeFn_smul c f] with x h₁ h₂ h₃ h₄
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply] at h₂ h₄ ⊢
    rw [h₁, h₂, h₃, h₄, mul_left_comm]

private theorem cutoffLinear_bound (ρ : X → ℝ) (hρ : Measurable ρ)
    (hρ₀ : ∀ x, 0 ≤ ρ x) (hρ₁ : ∀ x, ρ x ≤ 1) (f : Lp ℂ 2 μ) :
    ‖cutoffLinear ρ hρ hρ₀ hρ₁ f‖ ≤ ‖f‖ := by
  change ‖(cutoff_mul_memLp hρ hρ₀ hρ₁ f).toLp _‖ ≤ ‖f‖
  rw [Lp.norm_toLp, Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top f)
    (eLpNorm_mono fun x => cutoff_mul_norm_le (hρ₀ x) (hρ₁ x) (f x))

/-- Multiplication by a measurable cutoff in [0,1] on L². The measure may
carry the Hardy–Sobolev weight. -/
def cutoffOperator (ρ : X → ℝ) (hρ : Measurable ρ)
    (hρ₀ : ∀ x, 0 ≤ ρ x) (hρ₁ : ∀ x, ρ x ≤ 1) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  (cutoffLinear ρ hρ hρ₀ hρ₁).mkContinuous 1 (by simpa only [one_mul] using cutoffLinear_bound ρ hρ hρ₀ hρ₁)

theorem cutoffOperator_ae (ρ : X → ℝ) (hρ : Measurable ρ)
    (hρ₀ : ∀ x, 0 ≤ ρ x) (hρ₁ : ∀ x, ρ x ≤ 1) (f : Lp ℂ 2 μ) :
    (cutoffOperator ρ hρ hρ₀ hρ₁ f : X → ℂ) =ᵐ[μ] fun x => (ρ x : ℂ) * f x :=
  (cutoff_mul_memLp hρ hρ₀ hρ₁ f).coeFn_toLp

theorem norm_cutoffOperator_le (ρ : X → ℝ) (hρ : Measurable ρ)
    (hρ₀ : ∀ x, 0 ≤ ρ x) (hρ₁ : ∀ x, ρ x ≤ 1) :
    ‖cutoffOperator (μ := μ) ρ hρ hρ₀ hρ₁‖ ≤ 1 :=
  (cutoffOperator ρ hρ hρ₀ hρ₁).opNorm_le_bound zero_le_one
    (fun f => by
      change ‖cutoffLinear ρ hρ hρ₀ hρ₁ f‖ ≤ 1 * ‖f‖
      simpa only [one_mul] using cutoffLinear_bound ρ hρ hρ₀ hρ₁ f)

/-- The (L^2) multiplier norm is the essential supremum of the cutoff.
The lower estimate tests on a finite-measure subset of a strict superlevel set,
adapting the argument from the parallel RiemannMasullo formalization. -/
theorem norm_cutoffOperator_eq [SigmaFinite μ] (ρ : X → ℝ) (hρ : Measurable ρ)
    (hρ₀ : ∀ x, 0 ≤ ρ x) (hρ₁ : ∀ x, ρ x ≤ 1) :
    ‖cutoffOperator (μ := μ) ρ hρ hρ₀ hρ₁‖ = (eLpNorm ρ ∞ μ).toReal := by
  let T := cutoffOperator (μ := μ) ρ hρ hρ₀ hρ₁
  change ‖T‖ = _
  have hmul (u : Lp ℂ 2 μ) : ∀ᵐ x ∂μ, ‖(T u) x‖ = ‖ρ x‖ * ‖u x‖ := by
    have h := (cutoff_mul_memLp hρ hρ₀ hρ₁ u).coeFn_toLp
    filter_upwards [h] with x hx
    change ‖((cutoff_mul_memLp hρ hρ₀ hρ₁ u).toLp _) x‖ = _
    rw [hx, norm_mul, Complex.norm_real]
  have htop : MemLp ρ ∞ μ :=
    memLp_top_of_bound hρ.aestronglyMeasurable 1
      (.of_forall fun x => by simpa only [Real.norm_of_nonneg (hρ₀ x)] using hρ₁ x)
  apply le_antisymm
  · apply T.opNorm_le_bound ENNReal.toReal_nonneg
    intro u
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [hmul u, ae_le_lpNorm_exponent_top htop] with x hTu hx
    rw [← toReal_eLpNorm htop.aestronglyMeasurable] at hx
    exact hTu.trans_le (mul_le_mul_of_nonneg_right hx (norm_nonneg _))
  · refine le_of_forall_gt_imp_ge_of_dense fun c hc => ?_
    have hc₀ : 0 ≤ c := (norm_nonneg T).trans hc.le
    apply ENNReal.toReal_le_of_le_ofReal hc₀
    rw [eLpNorm_exponent_top]
    apply eLpNormEssSup_le_of_ae_bound
    rw [ae_iff]
    simp only [not_le]
    by_contra hnonzero
    obtain ⟨s, hs, hsub, hpos, hfin⟩ := Measure.exists_subset_measure_lt_top
      (measurableSet_lt measurable_const hρ.norm) (pos_iff_ne_zero.mpr hnonzero)
    let u : Lp ℂ 2 μ := indicatorConstLp 2 hs hfin.ne 1
    have hu : 0 < ‖u‖ := by
      dsimp only [u]
      rw [norm_indicatorConstLp (by norm_num) (by norm_num), norm_one, one_mul]
      exact Real.rpow_pos_of_pos (ENNReal.toReal_pos hpos.ne' hfin.ne) _
    have hlow : c * ‖u‖ ≤ ‖T u‖ := by
      rw [← Real.norm_of_nonneg hc₀, ← norm_smul]
      apply Lp.norm_le_norm_of_ae_le
      have hout : ∀ᵐ x ∂μ, x ∉ s → u x = 0 := indicatorConstLp_coeFn_notMem
      filter_upwards [Lp.coeFn_smul c u, hmul u, hout] with x hcu hTu hxout
      rw [hcu, Pi.smul_apply, norm_smul, Real.norm_of_nonneg hc₀, hTu]
      by_cases hx : x ∈ s
      · exact mul_le_mul_of_nonneg_right (hsub hx).le (norm_nonneg _)
      · simp [hxout hx]
    exact (mul_lt_mul_of_pos_right hc hu).not_ge (hlow.trans (T.le_opNorm u))

private def cutoffAtIdentity : ℝ → ℝ := ({0} : Set ℝ).indicator (fun _ => 1)

/-- On the positive-real group in log coordinates, a cutoff with empty
plateau can attain one at the identity and induce the zero operator. -/
theorem cutoff_operatorNorm_one_fails :
    ∃ ρ : ℝ → ℝ, ∃ hρ : Measurable ρ, ∃ h₀ : ∀ x, 0 ≤ ρ x, ∃ h₁ : ∀ x, ρ x ≤ 1,
      ρ 0 = 1 ∧ (∀ x, ρ (-x) = ρ x) ∧
      ContDiffOn ℝ ⊤ ρ ({0}ᶜ) ∧
      (∀ x, ρ x ≠ 0 → Real.exp x ∈ Icc ((5 / 4 : ℝ)⁻¹) (5 / 4)) ∧
      Icc ((5 / 4 : ℝ)⁻¹ + 1 / 2) (5 / 4 - 1 / 2) = ∅ ∧
      ‖cutoffOperator (μ := volume) ρ hρ h₀ h₁‖ = 0 := by
  refine ⟨cutoffAtIdentity, measurable_const.indicator (measurableSet_singleton 0),
    fun x => by by_cases hx : x = 0 <;> simp [cutoffAtIdentity, hx],
    fun x => by by_cases hx : x = 0 <;> simp [cutoffAtIdentity, hx],
    by simp [cutoffAtIdentity], ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    by_cases hx : x = 0 <;> simp [cutoffAtIdentity, hx]
  · apply (contDiffOn_const (c := (0 : ℝ))).congr
    intro x hx
    simp only [mem_compl_iff, mem_singleton_iff] at hx
    simp [cutoffAtIdentity, hx]
  · intro x hx
    have hx₀ : x = 0 := by
      by_contra h
      exact hx (by simp [cutoffAtIdentity, h])
    subst x
    rw [Real.exp_zero]
    constructor <;> norm_num
  · apply Icc_eq_empty_of_lt
    norm_num
  · have hzero : cutoffAtIdentity =ᵐ[(volume : Measure ℝ)] (0 : ℝ → ℝ) := by
      change ∀ᵐ x ∂(volume : Measure ℝ), cutoffAtIdentity x = 0
      rw [ae_iff]
      apply measure_mono_null (t := {0}) _ (measure_singleton 0)
      intro x hx
      by_contra h
      exact hx (by simp [cutoffAtIdentity, h])
    have hnorm : (eLpNorm cutoffAtIdentity ∞ volume).toReal = 0 := by
      rw [eLpNorm_congr_ae hzero, eLpNorm_zero, ENNReal.toReal_zero]
    exact (norm_cutoffOperator_eq (μ := (volume : Measure ℝ)) _ _ _ _).trans hnorm

/-- A cutoff profile smooth off finitely many positive radii is measurable after
pullback by the group modulus, even when values at the breakpoints are arbitrary.
Adapted from RiemannMasullo's proof for Definition 9.3.3.1. -/
theorem modulatedCutoff_measurable {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y]
    [BorelSpace Y] {modulus : Y → ℝ} (hm : Continuous modulus)
    (hm_pos : ∀ x, 0 < modulus x) {q : ℝ → ℝ} (breaks : Finset ℝ)
    (hq : ContDiffOn ℝ ⊤ q (Ioi 0 \ (breaks : Set ℝ))) :
    Measurable (fun x => q (modulus x)) := by
  let positiveModulus (x : Y) : Ioi (0 : ℝ) := ⟨modulus x, hm_pos x⟩
  have hprofile : Measurable (fun t : Ioi (0 : ℝ) => q t.val) := by
    apply ContinuousOn.measurable_of_countable_compl
      (s := (Subtype.val ⁻¹' (breaks : Set ℝ))ᶜ)
    · exact hq.continuousOn.comp continuous_subtype_val.continuousOn
        (fun t ht => ⟨t.property, ht⟩)
    · rw [compl_compl]
      exact breaks.finite_toSet.countable.preimage Subtype.val_injective
  exact hprofile.comp (hm.subtype_mk hm_pos).measurable

/-- The piecewise smooth symbols in Definition 9.3.3.1 act by contractions
for every Hardy–Sobolev density. -/
theorem modulatedCutoff_weighted_contraction {Y : Type*} [TopologicalSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] (μ : Measure Y) {modulus : Y → ℝ}
    (hm : Continuous modulus) (hm_pos : ∀ x, 0 < modulus x) {q : ℝ → ℝ}
    (breaks : Finset ℝ) (hq : ContDiffOn ℝ ⊤ q (Ioi 0 \ (breaks : Set ℝ)))
    (h₀ : ∀ x, 0 ≤ q (modulus x)) (h₁ : ∀ x, q (modulus x) ≤ 1)
    (a b s : ℝ) :
    let ν := hardySobolevMeasure μ (fun x => Real.log (modulus x)) a b s
    ∃ T : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν, ‖T‖ ≤ 1 ∧
      ∀ f, (T f : Y → ℂ) =ᵐ[ν] fun x => (q (modulus x) : ℂ) * f x := by
  let ρ := fun x => q (modulus x)
  let hρ := modulatedCutoff_measurable hm hm_pos breaks hq
  exact ⟨cutoffOperator ρ hρ h₀ h₁, norm_cutoffOperator_le ρ hρ h₀ h₁,
    fun f => (cutoff_mul_memLp hρ h₀ h₁ f).coeFn_toLp⟩

private theorem eLpNorm_two_energy (f : X → ℂ) :
    eLpNorm f 2 μ = (∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2) ∂μ) ^ (1 / 2 : ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by simp)]
  norm_num only [ENNReal.toReal_ofNat]
  congr 1
  apply lintegral_congr
  intro x
  change ‖f x‖ₑ ^ ((2 : ℕ) : ℝ) = ENNReal.ofReal (‖f x‖ ^ 2)
  rw [ENNReal.rpow_natCast, ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

/-- Strong convergence of the actual L² cutoff operators, also for a weighted measure. -/
theorem cutoffOperator_tendsto {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    (ρ : ι → X → ℝ) (hρ : ∀ i, Measurable (ρ i))
    (hρ₀ : ∀ i x, 0 ≤ ρ i x) (hρ₁ : ∀ i x, ρ i x ≤ 1)
    (hevent : ∀ x, ∀ᶠ i in l, ρ i x = 1) (f : Lp ℂ 2 μ) :
    Tendsto (fun i => cutoffOperator (ρ i) (hρ i) (hρ₀ i) (hρ₁ i) f) l (𝓝 f) := by
  have hfin : (∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2) ∂μ) ≠ ∞ := by
    intro h
    have hf := Lp.eLpNorm_ne_top f
    rw [eLpNorm_two_energy, h, ENNReal.top_rpow_of_pos (by norm_num)] at hf
    exact hf rfl
  have henergy := weightedL2_cutoff_error_tendsto μ (fun _ => 1) measurable_const
    (fun _ => zero_le_one) f (Lp.stronglyMeasurable f).measurable
    (by simpa only [mul_one] using hfin) ρ hρ hρ₀ hρ₁ hevent
  have hsqrt := (ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ)).tendsto 0).comp henergy
  rw [ENNReal.zero_rpow_of_pos (by norm_num)] at hsqrt
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ f).mpr
  apply hsqrt.congr
  intro i
  change (∫⁻ x, ENNReal.ofReal (((1 - ρ i x) ^ 2 * ‖f x‖ ^ 2) * 1) ∂μ) ^ (1 / 2 : ℝ) = _
  rw [eLpNorm_two_energy]
  congr 1
  apply lintegral_congr_ae
  filter_upwards [(cutoff_mul_memLp (hρ i) (hρ₀ i) (hρ₁ i) f).coeFn_toLp] with x hx
  change cutoffOperator (ρ i) (hρ i) (hρ₀ i) (hρ₁ i) f x = (ρ i x : ℂ) * f x at hx
  have hz : (ρ i x : ℂ) * f x - f x = ((ρ i x : ℂ) - 1) * f x := by
    rw [sub_mul, one_mul]
  simp only [Pi.sub_apply]
  rw [hx, hz, ← Complex.ofReal_one, ← Complex.ofReal_sub,
    norm_mul, Complex.norm_real, mul_pow, mul_one]
  simp only [Real.norm_eq_abs, sq_abs]
  congr 1
  ring

/-- The operators associated with a family of piecewise smooth radial cutoffs
converge strongly as the plateaus exhaust the positive modulus. -/
theorem modulatedCutoff_weighted_tendsto {Y : Type*} [TopologicalSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] (μ : Measure Y) {modulus : Y → ℝ}
    (hm : Continuous modulus) (hm_pos : ∀ x, 0 < modulus x)
    {l : Filter ι} [l.IsCountablyGenerated] (radius margin : ι → ℝ)
    (hRadius : Tendsto radius l atTop)
    (hMargin : Tendsto (fun i => margin i * radius i) l (𝓝 0))
    (q : ι → ℝ → ℝ) (breaks : ι → Finset ℝ)
    (hq : ∀ i, ContDiffOn ℝ ⊤ (q i) (Ioi 0 \ (breaks i : Set ℝ)))
    (h₀ : ∀ i x, 0 ≤ q i (modulus x)) (h₁ : ∀ i x, q i (modulus x) ≤ 1)
    (hplateau : ∀ i x, (radius i)⁻¹ + margin i ≤ modulus x →
      modulus x ≤ radius i - margin i → q i (modulus x) = 1)
    (a b s : ℝ) (f : Lp ℂ 2 (hardySobolevMeasure μ (fun x => Real.log (modulus x)) a b s)) :
    Tendsto (fun i => cutoffOperator (fun x => q i (modulus x))
      (modulatedCutoff_measurable hm hm_pos (breaks i) (hq i)) (h₀ i) (h₁ i) f) l (𝓝 f) :=
  cutoffOperator_tendsto _ (fun i => modulatedCutoff_measurable hm hm_pos (breaks i) (hq i))
    h₀ h₁ (cutoff_eventually_eq_one radius margin hRadius hMargin _ modulus hm_pos hplateau) f

end CutoffOperator

end Masullo
