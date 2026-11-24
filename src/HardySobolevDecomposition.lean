import HardySobolevHolomorphic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

open Filter Function MeasureTheory Set Topology
open scoped ENNReal

namespace Masullo

noncomputable section

theorem stripMeasure_neg_preserving (b s : ℝ) :
    MeasurePreserving (fun x : ℝ => -x) (stripMeasure (-b) (-b) s) (stripMeasure b b s) := by
  have hμ := Measure.measurePreserving_neg (volume : Measure ℝ)
  refine ⟨measurable_neg, ?_⟩
  ext S hS
  unfold stripMeasure amplitudeMeasure
  rw [Measure.map_apply measurable_neg hS, withDensity_apply _ (measurable_neg hS),
    withDensity_apply _ hS]
  conv_rhs => rw [← hμ.map_eq, setLIntegral_map hS
    (((stripSobolevAmplitude_continuous b b s).measurable.pow_const 2).ennreal_ofReal)
    measurable_neg]
  apply lintegral_congr
  intro x
  simp only [stripSobolevAmplitude, ite_self, mul_neg, neg_mul, neg_sq]

theorem exists_reflectedCompactClass {b s c : ℝ}
    (v : supportedSobolevCompletion b b s (Ioo c 0)) :
    ∃ w : supportedSobolevCompletion (-b) (-b) s (Ioi 0),
      (w.val : ℝ → ℂ) =ᵐ[volume] (fun x => v.val (-x)) ∧ ‖w‖ = ‖v‖ := by
  let h := stripMeasure_neg_preserving b s
  let w := Lp.compMeasurePreserving (fun x : ℝ => -x) h v.val
  have hac := absolutelyContinuous_amplitudeMeasure (volume : Measure ℝ) _
    (stripSobolevAmplitude_continuous (-b) (-b) s).measurable (stripSobolevAmplitude_pos (-b) (-b) s)
  have hEq : (w : ℝ → ℂ) =ᵐ[volume] (fun x => v.val (-x)) :=
    hac.ae_le (Lp.coeFn_compMeasurePreserving v.val h)
  have hv := (mem_supportedSobolevCompletion_iff b b s isOpen_Ioo v.val).mp v.property
  have hv' := (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae
    (p := fun x : ℝ => x ∉ Ioo c 0 → v.val x = 0) hv
  have hw : w ∈ supportedSobolevCompletion (-b) (-b) s (Ioi 0) := by
    apply (mem_supportedSobolevCompletion_iff (-b) (-b) s isOpen_Ioi w).mpr
    filter_upwards [hEq, hv'] with x hx hvx hxn
    rw [hx]
    exact hvx (fun hm => hxn (neg_lt_zero.mp hm.2))
  exact ⟨⟨w, hw⟩, hEq, Lp.norm_compMeasurePreserving v.val h⟩

theorem reflectedMellinIntegral_eq {f g : ℝ → ℂ}
    (h : g =ᵐ[volume] fun x => f (-x)) :
    cutoffMellinIntegral f 0 = (fun z : ℂ => cutoffMellinIntegral g 0 (-z)) := by
  funext z
  unfold cutoffMellinIntegral
  simp only [mellinEvaluationKernel, pow_zero, mul_one]
  rw [← integral_neg_eq_self (fun x : ℝ => f x * Complex.exp (z * (x : ℂ)))]
  apply integral_congr_ae
  filter_upwards [h] with x hx
  rw [hx, Complex.ofReal_neg, mul_neg, neg_mul]

/-- The bounded-support Mellin transform has uniformly square-integrable
derivatives on the right half-plane. The same right endpoint appears in the
original weight and in the half-plane bound. -/
theorem compactCutoffMellinIntegral_right_bound {b c : ℝ} {N k : ℕ} (hk : k ≤ N)
    (v : supportedSobolevCompletion b b (2 * (N : ℝ)) (Ioo c 0)) {r : ℝ} (hr : b < r) :
    let T (y : ℝ) := iteratedDeriv k (cutoffMellinIntegral v.val 0) (⟨r, y⟩ : ℂ)
    MemLp T 2 volume ∧ (∫ y, ‖T y‖ ^ 2) ≤ 2 * Real.pi * ‖v‖ ^ 2 := by
  obtain ⟨w, hw, hnorm⟩ := exists_reflectedCompactClass v
  obtain ⟨hLp, hBound⟩ := cutoffMellinIntegral_line_bound (a := -b) (b := -b) le_rfl
    le_rfl (neg_lt_neg hr) hk w
  let S (y : ℝ) := cutoffMellinIntegral w.val k (⟨-r, y⟩ : ℂ)
  change MemLp S 2 volume at hLp
  change (∫ y, ‖S y‖ ^ 2) ≤ _ at hBound
  have hS (y : ℝ) : iteratedDeriv k (cutoffMellinIntegral v.val 0) (⟨r, y⟩ : ℂ) =
      ((-1 : ℂ) ^ k) • S (-y) := by
    rw [reflectedMellinIntegral_eq hw, iteratedDeriv_comp_neg]
    have hpt : -(⟨r, y⟩ : ℂ) = ⟨-r, -y⟩ := rfl
    rw [hpt, iteratedDeriv_cutoffMellinIntegral le_rfl (by positivity) w k (neg_lt_neg hr)]
  intro T
  have hT : T = fun y => ((-1 : ℂ) ^ k) • S (-y) := funext hS
  refine ⟨?_, ?_⟩
  · rw [hT]
    exact (hLp.comp_measurePreserving (Measure.measurePreserving_neg (volume : Measure ℝ))).const_smul ((-1 : ℂ) ^ k)
  · calc
      (∫ y, ‖T y‖ ^ 2) = ∫ y, ‖S (-y)‖ ^ 2 := by simp [hT]
      _ = ∫ y, ‖S y‖ ^ 2 := integral_neg_eq_self (fun y : ℝ => ‖S y‖ ^ 2) volume
      _ ≤ 2 * Real.pi * ‖v‖ ^ 2 := by simpa [hnorm] using hBound

private theorem exists_supportedCutoff_split {a b s c : ℝ} (hc : c ≤ 0)
    (u : supportedSobolevCompletion a b s (Ioi c)) :
    ∃ (v : supportedSobolevCompletion a b s (Ioi 0))
      (w : supportedSobolevCompletion a b s (Ioo c 0)),
      (v.val : ℝ → ℂ) =ᵐ[volume] (Ioi 0).indicator (u.val : ℝ → ℂ) ∧
      (w.val : ℝ → ℂ) =ᵐ[volume] (Ioo c 0).indicator (u.val : ℝ → ℂ) ∧
      u.val = v.val + w.val := by
  obtain ⟨_, p, _, hp, _, _, _, _, _⟩ := stripSobolev_cutoff_exact a b s c hc
  let v := p u
  have hv := (mem_supportedSobolevCompletion_iff a b s isOpen_Ioi v.val).mp v.property
  have huv := (mem_supportedSobolevCompletion_iff a b s isOpen_Ioi u.val).mp u.property
  have hwvol : ∀ᵐ x ∂(volume : Measure ℝ), x ∉ Ioo c 0 → u.val x = v.val x := by
    have hz : ∀ᵐ x : ℝ ∂volume, x ≠ 0 := by
      rw [ae_iff]
      simp
    filter_upwards [hp u, huv, hz] with x hx hux hx0 hxw
    change v.val x = (Ioi 0).indicator (u.val : ℝ → ℂ) x at hx
    by_cases hxpos : x ∈ Ioi (0 : ℝ)
    · rw [indicator_of_mem hxpos] at hx
      exact hx.symm
    · rw [hx, indicator_of_notMem hxpos]
      exact hux (fun hxc => hxw ⟨hxc, lt_of_le_of_ne (le_of_not_gt hxpos) hx0⟩)
  have hac := absolutelyContinuous_amplitudeMeasure (volume : Measure ℝ) _
      (stripSobolevAmplitude_continuous a b s).measurable (stripSobolevAmplitude_pos a b s)
  have hsub := hac.ae_le (Lp.coeFn_sub u.val v.val)
  let w' := u.val - v.val
  have hw : w' ∈ supportedSobolevCompletion a b s (Ioo c 0) := by
    apply (mem_supportedSobolevCompletion_iff a b s isOpen_Ioo w').mpr
    filter_upwards [hsub, hwvol] with x h₁ h₂ hx
    change w' x = u.val x - v.val x at h₁
    rw [h₁, h₂ hx, sub_self]
  let w : supportedSobolevCompletion a b s (Ioo c 0) := ⟨w', hw⟩
  refine ⟨v, w, hp u, ?_, ?_⟩
  · filter_upwards [hsub, hwvol, hv] with x h₁ h₂ h₃
    change w.val x = u.val x - v.val x at h₁
    rw [h₁]
    by_cases hx : x ∈ Ioo c (0 : ℝ)
    · rw [indicator_of_mem hx, h₃ (fun hy => (not_lt_of_gt hx.2) hy), sub_zero]
    · rw [indicator_of_notMem hx, h₂ hx, sub_self]
  · change u.val = v.val + (u.val - v.val)
    abel

/-- Uniform squared vertical norms through order N on the specified half-plane. -/
def UniformMellinLineBound (D : Set ℝ) (N : ℕ) (F : ℂ → ℂ) : Prop :=
  ∀ k ≤ N, ∃ C : ℝ, ∀ r ∈ D,
    let T := fun y : ℝ => iteratedDeriv k F (⟨r, y⟩ : ℂ)
    MemLp T 2 volume ∧ (∫ y, ‖T y‖ ^ 2) ≤ C

/-- Corrected Corollary 9.2.1.3. The lower cutoff in the source is required.
The two holomorphic summands are the Mellin integrals of the canonical
support projections. -/
theorem cutoffMellinIntegral_hardy_decomposition {b c : ℝ} (hc : c < 0) {N : ℕ}
    (u : supportedSobolevCompletion b b (2 * (N : ℝ)) (Ioi c)) :
    let F := cutoffMellinIntegral u.val 0
    DifferentiableOn ℂ F (Complex.re ⁻¹' Iio b) ∧
      (∀ r < b, ∀ k ≤ N, MemLp (fun y : ℝ => iteratedDeriv k F (⟨r, y⟩ : ℂ)) 2 volume) ∧
      ∃ (v : supportedSobolevCompletion b b (2 * (N : ℝ)) (Ioi 0))
        (w : supportedSobolevCompletion b b (2 * (N : ℝ)) (Ioo c 0)),
        (v.val : ℝ → ℂ) =ᵐ[volume] (Ioi 0).indicator (u.val : ℝ → ℂ) ∧
        (w.val : ℝ → ℂ) =ᵐ[volume] (Ioo c 0).indicator (u.val : ℝ → ℂ) ∧
        let F₁ := cutoffMellinIntegral v.val 0
        let F₂ := cutoffMellinIntegral w.val 0
        DifferentiableOn ℂ F₁ (Complex.re ⁻¹' Iio b) ∧ UniformMellinLineBound (Iio b) N F₁ ∧
        Differentiable ℂ F₂ ∧ UniformMellinLineBound (Ioi b) N F₂ ∧
        (∃ C : ℝ, ∀ z : ℂ, ‖F₂ z‖ ≤ C * Real.sqrt (∫ x in Icc c 0, Real.exp (2 * z.re * x))) ∧
        (∀ z : ℂ, z.re < b → F z = F₁ z + F₂ z) := by
  intro F
  have hs : 0 ≤ 2 * (N : ℝ) := by positivity
  refine ⟨cutoffMellinIntegral_differentiableOn hc.le hs u, ?_, ?_⟩
  · intro r hr k hk
    have h (y : ℝ) : iteratedDeriv k F (⟨r, y⟩ : ℂ) =
        cutoffMellinIntegral u.val k (⟨r, y⟩ : ℂ) :=
      iteratedDeriv_cutoffMellinIntegral hc.le hs u k hr
    simpa only [h] using (cutoffMellinIntegral_line_bound le_rfl hc.le hr hk u).1
  obtain ⟨v, w, hv, hw, huv⟩ := exists_supportedCutoff_split hc.le u
  obtain ⟨hInt, hDiff, hGrowth⟩ := boundedStripSobolev_mellin_entire_bound b b _ c w
  have he (g : ℝ → ℂ) (z : ℂ) :
      cutoffMellinIntegral g 0 z = ∫ x, compactMellinKernel g z x := by
    simp only [cutoffMellinIntegral, mellinEvaluationKernel, compactMellinKernel, pow_zero, mul_one]
  refine ⟨v, w, hv, hw, cutoffMellinIntegral_differentiableOn le_rfl hs v, ?_, ?_, ?_, ?_, ?_⟩
  · intro k hk
    refine ⟨2 * Real.pi * ‖v‖ ^ 2, fun r hr => ?_⟩
    have hr' : r < b := hr
    have h (y : ℝ) : iteratedDeriv k (cutoffMellinIntegral v.val 0) (⟨r, y⟩ : ℂ) =
        cutoffMellinIntegral v.val k (⟨r, y⟩ : ℂ) :=
      iteratedDeriv_cutoffMellinIntegral le_rfl hs v k hr'
    simpa only [h, mul_zero, Real.exp_zero, mul_one] using
      cutoffMellinIntegral_line_bound le_rfl le_rfl hr' hk v
  · exact (funext (he w.val)).symm ▸ hDiff
  · exact fun k hk => ⟨_, fun r hr => compactCutoffMellinIntegral_right_bound hk w hr⟩
  · refine ⟨Real.sqrt (∫ x in Icc c 0, ‖w.val x‖ ^ 2), fun z => ?_⟩
    rw [he]
    exact hGrowth z
  · intro z hz
    have hI := cutoffSobolev_mellinMoment_integrable le_rfl hs v hz 0
    have hJ : Integrable (fun x => w.val x * mellinEvaluationKernel 0 z x) := by
      have hEq : (fun x => w.val x * mellinEvaluationKernel 0 z x) = compactMellinKernel w.val z := by
        funext x
        simp only [mellinEvaluationKernel, compactMellinKernel, pow_zero, mul_one]
      rw [hEq]
      exact hInt z
    change cutoffMellinIntegral u.val 0 z =
      cutoffMellinIntegral v.val 0 z + cutoffMellinIntegral w.val 0 z
    unfold cutoffMellinIntegral
    rw [← integral_add hI hJ]
    apply integral_congr_ae
    have hac := absolutelyContinuous_amplitudeMeasure (volume : Measure ℝ) _
      (stripSobolevAmplitude_continuous b b (2 * (N : ℝ))).measurable
      (stripSobolevAmplitude_pos b b (2 * (N : ℝ)))
    filter_upwards [hac.ae_le (Lp.coeFn_add v.val w.val)] with x hx
    have heq : u.val x = v.val x + w.val x := by simpa only [Pi.add_apply, ← huv] using hx
    rw [heq, add_mul]

/-- The unrestricted source claimed in Corollary 9.2.1.3 can have a
divergent Mellin integral strictly to the left of the weight line. -/
theorem unrestrictedSobolev_mellin_not_integrable :
    ∃ u : StripSobolev 0 0 2,
      ¬ Integrable (fun x : ℝ => u x * Complex.exp (-(x : ℂ))) := by
  let q (x : ℝ) := 1 + x ^ 2
  let g (x : ℝ) : ℂ := ((q x)⁻¹ : ℝ)
  let f := (Iio (0 : ℝ)).indicator g
  have hq (x : ℝ) : 0 < q x := by dsimp [q]; positivity
  have hg : Continuous g := Complex.continuous_ofReal.comp
    ((by dsimp [q]; fun_prop : Continuous q).inv₀ fun x => (hq x).ne')
  have hf : Measurable f := hg.measurable.indicator measurableSet_Iio
  have hAmp := (stripSobolevAmplitude_continuous 0 0 2).measurable
  have hMem : MemLp f 2 (stripMeasure 0 0 2) := by
    apply (memLp_amplitudeMeasure_iff volume _ hAmp hf.aestronglyMeasurable).mpr
    have hm : AEStronglyMeasurable (fun x => stripSobolevAmplitude 0 0 2 x • f x) volume :=
      hAmp.aestronglyMeasurable.smul hf.aestronglyMeasurable
    apply (memLp_two_iff_integrable_sq_norm hm).mpr
    have hSquare (x : ℝ) :
        ‖stripSobolevAmplitude 0 0 2 x • f x‖ ^ 2 =
          (Iio (0 : ℝ)).indicator (fun y => (q y)⁻¹) x := by
      by_cases hx : x ∈ Iio (0 : ℝ)
      · rw [show f x = g x from indicator_of_mem hx _ , indicator_of_mem hx]
        rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, stripSobolevAmplitude_sq le_rfl]
        simp only [hardySobolevWeight, zero_mul, mul_zero, Real.exp_zero, max_self, one_mul, g,
          Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr (hq x).le)]
        rw [show (2 : ℝ) / 2 = 1 by norm_num, Real.rpow_one]
        change q x * ((q x)⁻¹) ^ 2 = (q x)⁻¹
        field_simp [(hq x).ne']
      · simp [f, indicator_of_notMem hx]
    simpa only [hSquare] using (integrable_inv_one_add_sq.indicator measurableSet_Iio)
  let u := hMem.toLp f
  refine ⟨u, ?_⟩
  intro hu
  have hac := absolutelyContinuous_amplitudeMeasure (volume : Measure ℝ) _
    hAmp (stripSobolevAmplitude_pos 0 0 2)
  have he : (u : ℝ → ℂ) =ᵐ[volume] f := hac.ae_le hMem.coeFn_toLp
  let μ := (volume : Measure ℝ).restrict (Iio 0)
  have hI : Integrable (fun x : ℝ => f x * Complex.exp (-(x : ℂ))) μ :=
    (hu.congr (he.mono fun x hx => congrArg (fun t => t * Complex.exp (-(x : ℂ))) hx)).integrableOn
  have hLower : Integrable (fun _ : ℝ => (1 / 2 : ℝ)) μ := by
    apply hI.norm.mono' aestronglyMeasurable_const
    filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Iio] with x hx
    have hx' : 0 ≤ -x := neg_nonneg.mpr (show x < 0 from hx).le
    simp only [f, indicator_of_mem hx, g, norm_mul, Complex.norm_real, Real.norm_of_nonneg
      (inv_nonneg.mpr (hq x).le), Complex.norm_exp, Complex.neg_re, Complex.ofReal_re]
    rw [inv_mul_eq_div]
    apply (le_div_iff₀ (hq x)).mpr
    have hquad := Real.quadratic_le_exp_of_nonneg hx'
    dsimp [q]
    nlinarith
  have hFinite := (integrable_const_iff_isFiniteMeasure (by norm_num : (1 / 2 : ℝ) ≠ 0)).mp hLower
  have hMass : μ univ = ∞ := by
    dsimp [μ]
    rw [Measure.restrict_apply_univ, Real.volume_Iio]
  exact hFinite.measure_univ_lt_top.ne hMass

end
end Masullo
