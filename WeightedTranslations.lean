import SobolevDuality
import L2Multipliers
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open Filter Function MeasureTheory Set Topology
open scoped ENNReal NNReal

namespace Masullo

section Multipliers

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {r : X → ℝ} {C : ℝ}

private theorem realMultiplier_ae_bound (hC : ∀ x, |r x| ≤ C) :
    ∀ᵐ x ∂μ, ‖(r x : ℂ)‖ ≤ C := .of_forall fun x => by
  simpa only [Complex.norm_real, Real.norm_eq_abs] using hC x

private theorem memLp_mul_of_realBound (hr : Measurable r) (hC : ∀ x, |r x| ≤ C)
    (f : Lp ℂ 2 μ) : MemLp (fun x => (r x : ℂ) * f x) 2 μ :=
  memLp_bounded_complex_mul (Complex.continuous_ofReal.measurable.comp hr).aestronglyMeasurable
    (realMultiplier_ae_bound hC) (Lp.memLp f)

/-- Bounded real measurable multiplication on complex L². -/
noncomputable def lpTwoRealMultiplier (hr : Measurable r) (hC : ∀ x, |r x| ≤ C) :
    Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  lpTwoComplexMultiplier (Complex.continuous_ofReal.measurable.comp hr).aestronglyMeasurable
    (realMultiplier_ae_bound hC)

theorem lpTwoRealMultiplier_ae (hr : Measurable r) (hC : ∀ x, |r x| ≤ C) (f : Lp ℂ 2 μ) :
    (lpTwoRealMultiplier hr hC f : X → ℂ) =ᵐ[μ] fun x => (r x : ℂ) * f x :=
  lpTwoComplexMultiplier_ae _ _ f

theorem lpTwoRealMultiplier_norm_le (hr : Measurable r) (hC : ∀ x, |r x| ≤ C) (hC₀ : 0 ≤ C) :
    ‖lpTwoRealMultiplier (μ := μ) hr hC‖ ≤ C :=
  lpTwoComplexMultiplier_norm_le _ _ hC₀

private theorem lpTwo_norm_eq_sqrt_integral {f : X → ℂ} (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖ = Real.sqrt (∫ x, ‖f x‖ ^ 2 ∂μ) := by
  rw [Lp.norm_toLp, toReal_eLpNorm hf.aestronglyMeasurable,
    lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num) hf.aestronglyMeasurable,
    Real.sqrt_eq_rpow]
  norm_num [Real.rpow_natCast, inv_eq_one_div]

/-- Joint strong continuity of multipliers bounded uniformly by one,
with a real parameter and pointwise continuous coefficients. -/
theorem continuous_lpTwoRealMultipliers (r : ℝ → X → ℝ)
    (hm : ∀ t, Measurable (r t)) (hc : ∀ x, Continuous (fun t => r t x))
    (hB : ∀ t x, |r t x| ≤ 1) :
    Continuous (fun p : Lp ℂ 2 μ × ℝ => lpTwoRealMultiplier (hm p.2) (hB p.2) p.1) := by
  let M (t : ℝ) := lpTwoRealMultiplier (μ := μ) (hm t) (hB t)
  apply continuous_prod_of_continuous_lipschitzWith _ 1
  · intro f
    apply continuous_iff_continuousAt.mpr
    intro t₀
    apply (tendsto_iff_dist_tendsto_zero).mpr
    let F (t : ℝ) (x : X) : ℂ := ((r t x - r t₀ x : ℝ) : ℂ) * f x
    have hmF (t : ℝ) : MemLp (F t) 2 μ := by
      apply memLp_mul_of_realBound ((hm t).sub (hm t₀)) _ f (C := 2)
      intro x
      exact (abs_sub _ _).trans (by linarith [hB t x, hB t₀ x])
    have hrep (t : ℝ) : M t f - M t₀ f = (hmF t).toLp (F t) := by
      apply Lp.ext
      filter_upwards [lpTwoRealMultiplier_ae (hm t) (hB t) f,
        lpTwoRealMultiplier_ae (hm t₀) (hB t₀) f, Lp.coeFn_sub (M t f) (M t₀ f),
        (hmF t).coeFn_toLp] with x h₀ h₁ h₂ h₃
      change (M t f - M t₀ f) x = (hmF t).toLp (F t) x
      simp only [Pi.sub_apply] at h₂
      rw [h₂, h₀, h₁, h₃]
      simp only [F, Complex.ofReal_sub, sub_mul]
    have hI (t : ℝ) : dist (M t f) (M t₀ f) = Real.sqrt (∫ x, ‖F t x‖ ^ 2 ∂μ) := by
      rw [dist_eq_norm, hrep, lpTwo_norm_eq_sqrt_integral]
    have hIlim : Tendsto (fun t => ∫ x, ‖F t x‖ ^ 2 ∂μ) (𝓝 t₀) (𝓝 0) := by
      let b (x : X) := 4 * ‖f x‖ ^ 2
      have hb : Integrable b μ :=
        ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp (Lp.memLp f)).const_mul 4
      have hbound (t : ℝ) (x : X) : ‖‖F t x‖ ^ 2‖ ≤ b x := by
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        have hrx : |r t x - r t₀ x| ≤ 2 := (abs_sub _ _).trans (by linarith [hB t x, hB t₀ x])
        have hf : ‖F t x‖ ≤ 2 * ‖f x‖ := by
          rw [show ‖F t x‖ = |r t x - r t₀ x| * ‖f x‖ by
            dsimp only [F]
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]]
          exact mul_le_mul_of_nonneg_right hrx (norm_nonneg _)
        exact (pow_le_pow_left₀ (norm_nonneg _) hf 2).trans_eq (by dsimp [b]; ring)
      have hlim (x : X) : Tendsto (fun t => ‖F t x‖ ^ 2) (𝓝 t₀) (𝓝 (0 : ℝ)) := by
        have hcont : Continuous (fun t => ‖F t x‖ ^ 2) :=
          (((Complex.continuous_ofReal.comp ((hc x).sub continuous_const)).mul continuous_const).norm.pow 2)
        simpa [F] using hcont.tendsto t₀
      simpa using tendsto_integral_filter_of_dominated_convergence b
        (.of_forall fun t => (hmF t).aestronglyMeasurable.norm.pow 2)
        (.of_forall fun t => .of_forall fun x => hbound t x) hb (.of_forall hlim)
    have hlim := (Real.continuous_sqrt.tendsto 0).comp hIlim
    change Tendsto (fun t => dist (M t f) (M t₀ f)) (𝓝 t₀) (𝓝 0)
    simpa only [Function.comp_def, Real.sqrt_zero, hI] using hlim
  · intro t f g
    have hn : ‖M t‖₊ ≤ 1 := by
      exact_mod_cast lpTwoRealMultiplier_norm_le (μ := μ) (hm t) (hB t) zero_le_one
    exact ((M t).lipschitz f g).trans (by gcongr)

end Multipliers

section LogarithmicWeight

noncomputable def logSobolevAmplitude (s x : ℝ) : ℝ := (1 + x ^ 2) ^ (s / 4)

theorem logSobolevAmplitude_pos (s x : ℝ) : 0 < logSobolevAmplitude s x :=
  Real.rpow_pos_of_pos (by positivity) _

theorem continuous_logSobolevAmplitude (s : ℝ) : Continuous (logSobolevAmplitude s) :=
  ((by fun_prop : Continuous fun x : ℝ => 1 + x ^ 2)).rpow_const fun _ => Or.inl (by positivity)

theorem logSobolevAmplitude_neg (s x : ℝ) : logSobolevAmplitude (-s) x = (logSobolevAmplitude s x)⁻¹ := by
  rw [logSobolevAmplitude, show -s / 4 = -(s / 4) by ring, Real.rpow_neg (by positivity)]
  rfl

private noncomputable def logSobolevShiftBound (s t : ℝ) : ℝ := (2 * (1 + t ^ 2)) ^ (|s| / 4)

private theorem logSobolevShiftBound_pos (s t : ℝ) : 0 < logSobolevShiftBound s t :=
  Real.rpow_pos_of_pos (by positivity) _

private theorem continuous_logSobolevShiftBound (s : ℝ) : Continuous (logSobolevShiftBound s) :=
  ((by fun_prop : Continuous fun t : ℝ => 2 * (1 + t ^ 2))).rpow_const fun _ => Or.inl (by positivity)

private theorem logSobolevAmplitude_add_le {s : ℝ} (hs : 0 ≤ s) (x t : ℝ) :
    logSobolevAmplitude s (x + t) ≤ logSobolevShiftBound s t * logSobolevAmplitude s x := by
  have hquad : 1 + (x + t) ^ 2 ≤ (2 * (1 + t ^ 2)) * (1 + x ^ 2) := by
    nlinarith [sq_nonneg (x - t), mul_nonneg (sq_nonneg x) (sq_nonneg t)]
  unfold logSobolevAmplitude logSobolevShiftBound
  rw [abs_of_nonneg hs, ← Real.mul_rpow (by positivity) (by positivity)]
  exact Real.rpow_le_rpow (by positivity) hquad (by positivity)

private theorem logSobolevRatio_le_of_nonneg {s : ℝ} (hs : 0 ≤ s) (t x : ℝ) :
    logSobolevAmplitude s x / logSobolevAmplitude s (x+t) ≤ logSobolevShiftBound s t := by
  apply (div_le_iff₀ (logSobolevAmplitude_pos _ _)).mpr
  simpa only [add_neg_cancel_right, logSobolevShiftBound, neg_sq] using
    logSobolevAmplitude_add_le hs (x+t) (-t)

private theorem logSobolevRatio_le (s t x : ℝ) :
    logSobolevAmplitude s x / logSobolevAmplitude s (x+t) ≤ logSobolevShiftBound s t := by
  by_cases hs : 0 ≤ s
  · exact logSobolevRatio_le_of_nonneg hs t x
  · have hs' : 0 ≤ -s := neg_nonneg.mpr (le_of_not_ge hs)
    have h := logSobolevRatio_le_of_nonneg hs' (-t) (x+t)
    simpa only [add_neg_cancel_right, logSobolevAmplitude_neg, inv_div_inv, logSobolevShiftBound,
      abs_neg, neg_sq] using h

private noncomputable def normalizedLogSobolevRatio (s t x : ℝ) : ℝ :=
  logSobolevAmplitude s x / logSobolevAmplitude s (x+t) / logSobolevShiftBound s t

private theorem normalizedLogSobolevRatio_bound (s t x : ℝ) : |normalizedLogSobolevRatio s t x| ≤ 1 := by
  rw [normalizedLogSobolevRatio, abs_of_nonneg (by
    exact div_nonneg (div_nonneg (logSobolevAmplitude_pos _ _).le (logSobolevAmplitude_pos _ _).le)
      (logSobolevShiftBound_pos _ _).le), div_le_iff₀ (logSobolevShiftBound_pos _ _), one_mul]
  exact logSobolevRatio_le s t x

private theorem normalizedLogSobolevRatio_continuous_left (s x : ℝ) :
    Continuous (fun t => normalizedLogSobolevRatio s t x) := by
  have hw := continuous_logSobolevAmplitude s
  exact (continuous_const.div (hw.comp (continuous_const.add continuous_id))
    (fun _ => (logSobolevAmplitude_pos _ _).ne')).div (continuous_logSobolevShiftBound s)
      (fun _ => (logSobolevShiftBound_pos _ _).ne')

private theorem normalizedLogSobolevRatio_continuous_right (s t : ℝ) :
    Continuous (normalizedLogSobolevRatio s t) := by
  have hw := continuous_logSobolevAmplitude s
  exact (hw.div (hw.comp (continuous_id.add continuous_const))
    (fun _ => (logSobolevAmplitude_pos _ _).ne')).div_const _

end LogarithmicWeight

section TranslationAction

variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsAddLeftInvariant]
  (logNorm : G →+ ℝ) (hc : Continuous logNorm)

noncomputable def unweightedShift (g : G) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  (Lp.compMeasurePreservingₗᵢ ℂ (· + g) (measurePreserving_add_right μ g)).toContinuousLinearMap

theorem unweightedShift_ae (g : G) (f : Lp ℂ 2 μ) :
    (unweightedShift μ g f : G → ℂ) =ᵐ[μ] fun x => f (x+g) :=
  Lp.coeFn_compMeasurePreserving f (measurePreserving_add_right μ g)

/-- Translation by `g` in the L² coordinate obtained by multiplying
the function by its Sobolev amplitude. -/
noncomputable def logSobolevTranslation (s : ℝ) (g : G) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  let t := logNorm g
  ((logSobolevShiftBound s t : ℝ) : ℂ) •
    ((lpTwoRealMultiplier ((normalizedLogSobolevRatio_continuous_right s t).measurable.comp hc.measurable)
      (fun x => normalizedLogSobolevRatio_bound s t (logNorm x))).comp (unweightedShift μ g))

theorem logSobolevTranslation_ae (s : ℝ) (g : G) (f : Lp ℂ 2 μ) :
    (logSobolevTranslation μ logNorm hc s g f : G → ℂ) =ᵐ[μ]
      fun x => ((logSobolevAmplitude s (logNorm x) / logSobolevAmplitude s (logNorm (x+g)) : ℝ) : ℂ) *
        f (x+g) := by
  let t := logNorm g
  let M := lpTwoRealMultiplier (μ := μ)
    ((normalizedLogSobolevRatio_continuous_right s t).measurable.comp hc.measurable)
    (fun x => normalizedLogSobolevRatio_bound s t (logNorm x))
  let c : ℂ := (logSobolevShiftBound s t : ℝ)
  let u := unweightedShift μ g f
  change ((c • M u : Lp ℂ 2 μ) : G → ℂ) =ᵐ[μ] _
  filter_upwards [Lp.coeFn_smul c (M u),
    lpTwoRealMultiplier_ae ((normalizedLogSobolevRatio_continuous_right s t).measurable.comp hc.measurable)
      (fun x => normalizedLogSobolevRatio_bound s t (logNorm x)) u,
    unweightedShift_ae μ g f] with x h₀ h₁ h₂
  simp only [Pi.smul_apply, smul_eq_mul] at h₀
  rw [h₀, h₁, h₂, ← mul_assoc, ← Complex.ofReal_mul, map_add]
  congr 2
  dsimp only [normalizedLogSobolevRatio, c, t]
  exact mul_div_cancel₀ _ (logSobolevShiftBound_pos _ _).ne'

theorem logSobolevTranslation_zero (s : ℝ) : logSobolevTranslation μ logNorm hc s 0 =
    ContinuousLinearMap.id ℂ (Lp ℂ 2 μ) := by
  ext1 f
  apply Lp.ext
  filter_upwards [logSobolevTranslation_ae μ logNorm hc s 0 f] with x hx
  rw [hx, add_zero, div_self (logSobolevAmplitude_pos _ _).ne', Complex.ofReal_one, one_mul,
    ContinuousLinearMap.id_apply]

theorem logSobolevTranslation_add (s : ℝ) (g h : G) :
    logSobolevTranslation μ logNorm hc s (g+h) =
      (logSobolevTranslation μ logNorm hc s g).comp (logSobolevTranslation μ logNorm hc s h) := by
  ext1 f
  apply Lp.ext
  have hshift := (measurePreserving_add_right μ g).quasiMeasurePreserving.ae_eq_comp
    (logSobolevTranslation_ae μ logNorm hc s h f)
  filter_upwards [logSobolevTranslation_ae μ logNorm hc s (g+h) f,
    logSobolevTranslation_ae μ logNorm hc s g (logSobolevTranslation μ logNorm hc s h f), hshift]
    with x h₀ h₁ h₂
  simp only [Function.comp_apply] at h₂
  change logSobolevTranslation μ logNorm hc s (g+h) f x =
    logSobolevTranslation μ logNorm hc s g (logSobolevTranslation μ logNorm hc s h f) x
  rw [h₀, h₁, h₂, ← add_assoc, ← mul_assoc, ← Complex.ofReal_mul]
  congr 2
  field_simp [(logSobolevAmplitude_pos _ _).ne']

theorem continuous_logSobolevTranslation [R1Space G] [μ.InnerRegularCompactLTTop]
    [IsLocallyFiniteMeasure μ] (s : ℝ) :
    Continuous (fun p : G × Lp ℂ 2 μ => logSobolevTranslation μ logNorm hc s p.1 p.2) := by
  let shift (g : G) : C(G, G) := ⟨(· + g), continuous_id.add continuous_const⟩
  have hshift : Continuous shift := ContinuousMap.continuous_of_continuous_uncurry _
    (continuous_snd.add continuous_fst)
  have hu : Continuous (fun p : G × Lp ℂ 2 μ => unweightedShift μ p.1 p.2) := by
    exact continuous_snd.compMeasurePreservingLp (hshift.comp continuous_fst)
      (fun p => measurePreserving_add_right μ p.1) (by norm_num)
  let r (t : ℝ) (x : G) := normalizedLogSobolevRatio s t (logNorm x)
  have hm (t : ℝ) : Measurable (r t) :=
    (normalizedLogSobolevRatio_continuous_right s t).measurable.comp hc.measurable
  have hr (x : G) : Continuous (fun t => r t x) := normalizedLogSobolevRatio_continuous_left s (logNorm x)
  have hb (t : ℝ) (x : G) : |r t x| ≤ 1 := normalizedLogSobolevRatio_bound s t (logNorm x)
  have hx := (continuous_lpTwoRealMultipliers (μ := μ) r hm hr hb).comp
    (hu.prodMk (hc.comp continuous_fst))
  have hc' := Complex.continuous_ofReal.comp ((continuous_logSobolevShiftBound s).comp (hc.comp
    (continuous_fst : Continuous (Prod.fst : G × Lp ℂ 2 μ → G))))
  exact hc'.smul hx

theorem logSobolevTranslation_norm_le (s : ℝ) (g : G) :
    ‖logSobolevTranslation μ logNorm hc s g‖ ≤ (2 * (1 + (logNorm g) ^ 2)) ^ (|s| / 4) := by
  let t := logNorm g
  let C := logSobolevShiftBound s t
  have hC := (logSobolevShiftBound_pos s t).le
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro f
  let M := lpTwoRealMultiplier (μ := μ)
    ((normalizedLogSobolevRatio_continuous_right s t).measurable.comp hc.measurable)
    (fun x => normalizedLogSobolevRatio_bound s t (logNorm x))
  have hM : ‖M‖ ≤ 1 := lpTwoRealMultiplier_norm_le _ _ zero_le_one
  let u := unweightedShift μ g f
  have hu : ‖u‖ = ‖f‖ := Lp.norm_compMeasurePreserving f (measurePreserving_add_right μ g)
  change ‖(C : ℂ) • M u‖ ≤ C * ‖f‖
  rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hC]
  exact mul_le_mul_of_nonneg_left ((M.le_opNorm u).trans (by rw [hu]; nlinarith [norm_nonneg f])) hC

/-- The integral pairing intertwines right translation on the negative
weighted space with the adjoint of left translation on the positive space. -/
theorem logSobolevTranslation_dual_pairing (s : ℝ) (g : G) (v : Lp ℂ 2 μ) :
    sobolevBilinearDual μ (logSobolevTranslation μ logNorm hc (-s) g v) =
      (sobolevBilinearDual μ v).comp (logSobolevTranslation μ logNorm hc s (-g)) := by
  ext1 u
  simp only [ContinuousLinearMap.comp_apply, sobolevBilinearDual_apply]
  let a (x : G) := logSobolevAmplitude s (logNorm x)
  let F (x : G) : ℂ := (((a x / a (x + -g)) : ℝ) : ℂ) * u (x + -g) * v x
  have hᵣ : (∫ x, logSobolevTranslation μ logNorm hc s (-g) u x * v x ∂μ) = ∫ x, F x ∂μ := by
    apply integral_congr_ae
    filter_upwards [logSobolevTranslation_ae μ logNorm hc s (-g) u] with x hx
    rw [hx]
  rw [hᵣ, ← integral_add_right_eq_self F g]
  apply integral_congr_ae
  filter_upwards [logSobolevTranslation_ae μ logNorm hc (-s) g v] with x hx
  rw [hx, logSobolevAmplitude_neg, logSobolevAmplitude_neg, inv_div_inv]
  dsimp [F, a]
  rw [add_neg_cancel_right]
  ring

/-- Equivariance of the dual isometry in Proposition 9.1.2.5. -/
theorem logSobolevDuality_intertwines (s : ℝ) (g : G) (l : StrongDual ℂ (Lp ℂ 2 μ)) :
    (sobolevBilinearDual μ).symm (l.comp (logSobolevTranslation μ logNorm hc s (-g))) =
      logSobolevTranslation μ logNorm hc (-s) g ((sobolevBilinearDual μ).symm l) := by
  apply (sobolevBilinearDual μ).injective
  rw [LinearIsometryEquiv.apply_symm_apply, logSobolevTranslation_dual_pairing,
    LinearIsometryEquiv.apply_symm_apply]

end TranslationAction

end Masullo
