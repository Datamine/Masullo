import WeightedTrace
import WeightedTranslations
import Mathlib.Topology.Algebra.Module.Spaces.PointwiseConvergenceCLM

open Filter MeasureTheory Set Topology
open scoped CompactlySupported ENNReal NNReal

namespace Masullo

section OperatorSeminorm

variable {E Y : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]

/-- The operator norm of a strongly continuous family is Borel measurable.
Its sublevel sets are intersections of the closed evaluation sublevel sets. -/
theorem measurable_opNorm_of_continuous_eval {T : Y → E →L[ℂ] E}
    (hT : ∀ f, Continuous (fun y => T y f)) :
    Measurable (fun y => ‖T y‖) := by
  apply measurable_of_Iic
  intro r
  by_cases hr : 0 ≤ r
  · have he : (fun y => ‖T y‖) ⁻¹' Iic r =
        ⋂ f : E, {y | ‖T y f‖ ≤ r * ‖f‖} := by
      ext y
      simp only [mem_preimage, mem_Iic, mem_iInter, mem_ofPred_eq]
      exact ContinuousLinearMap.opNorm_le_iff hr
    rw [he]
    exact (isClosed_iInter fun f => isClosed_le (hT f).norm continuous_const).measurableSet
  · have he : (fun y => ‖T y‖) ⁻¹' Iic r = ∅ :=
      eq_empty_iff_forall_notMem.mpr fun y hy => hr ((norm_nonneg _).trans hy)
    rw [he]
    exact MeasurableSet.empty

omit [MeasurableSpace Y] [BorelSpace Y] in
/-- A seminorm continuous in the pointwise convergence topology gives a
continuous scalar function on every strongly continuous family. -/
theorem continuous_pointwise_seminorm_of_continuous_eval {T : Y → E →L[ℂ] E}
    (hT : ∀ f, Continuous (fun y => T y f))
    (p : Seminorm ℂ (E →Lₚₜ[ℂ] E)) (hp : Continuous p) :
    Continuous (fun y => p (T y)) :=
  hp.comp (PointwiseConvergenceCLM.continuous_of_continuous_eval hT)

end OperatorSeminorm

private theorem exists_seminorm_bound_by_norm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (p : Seminorm ℂ E) (hp : Continuous p) :
    ∃ C : ℝ, 0 < C ∧ ∀ x, p x ≤ C * ‖x‖ := by
  have hn : p ⁻¹' Iio 1 ∈ 𝓝 (0 : E) :=
    hp.continuousAt.preimage_mem_nhds (Iio_mem_nhds (by simp))
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hn
  refine ⟨2 / ε, by positivity, fun x => ?_⟩
  by_cases hx : x = 0
  · simp [hx]
  have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  let c : ℝ := ε / (2 * ‖x‖)
  have hc : 0 < c := by dsimp [c]; positivity
  have hcn : c * ‖x‖ = ε / 2 := by
    dsimp [c]
    field_simp
  have hcx : (c : ℂ) • x ∈ Metric.ball (0 : E) ε := by
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hc, hcn]
    exact half_lt_self hε
  have hpc : p ((c : ℂ) • x) < 1 := hball hcx
  rw [map_smul_eq_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc] at hpc
  have hmul : c * (2 / ε * ‖x‖) = 1 := by
    dsimp [c]
    field_simp
  apply le_of_lt
  exact lt_of_mul_lt_mul_left (hpc.trans_eq hmul.symm) hc.le

section Weight

/-- Positive square root of the endpoint weight in Definition 9.2.2.9. -/
noncomputable def hardySobolevAmplitude (a b s x : ℝ) : ℝ :=
  Real.sqrt (hardySobolevWeight a b s x)

private theorem hardySobolevWeight_pos (a b s x : ℝ) : 0 < hardySobolevWeight a b s x := by
  unfold hardySobolevWeight
  exact mul_pos ((Real.exp_pos _).trans_le (le_max_left _ _)) (Real.rpow_pos_of_pos (by positivity) _)

private theorem hardySobolevAmplitude_pos (a b s x : ℝ) : 0 < hardySobolevAmplitude a b s x :=
  Real.sqrt_pos.2 (hardySobolevWeight_pos a b s x)

private theorem continuous_hardySobolevAmplitude (a b s : ℝ) :
    Continuous (hardySobolevAmplitude a b s) :=
  Real.continuous_sqrt.comp (continuous_hardySobolevWeight a b s)

private noncomputable def hardySobolevBound (a b s t : ℝ) : ℝ :=
  Real.sqrt ((2 : ℝ) ^ (s / 2) * hardySobolevWeight a b s t)

private theorem hardySobolevBound_pos (a b s t : ℝ) : 0 < hardySobolevBound a b s t :=
  Real.sqrt_pos.2 (mul_pos (Real.rpow_pos_of_pos (by norm_num) _) (hardySobolevWeight_pos a b s t))

private theorem continuous_hardySobolevBound (a b s : ℝ) :
    Continuous (hardySobolevBound a b s) :=
  Real.continuous_sqrt.comp (continuous_const.mul (continuous_hardySobolevWeight a b s))

private theorem hardySobolevAmplitude_ratio_le (a b s : ℝ) (hs : 0 ≤ s) (t x : ℝ) :
    hardySobolevAmplitude a b s x / hardySobolevAmplitude a b s (x - t) ≤
      hardySobolevBound a b s t := by
  apply (div_le_iff₀ (hardySobolevAmplitude_pos ..)).2
  unfold hardySobolevAmplitude hardySobolevBound
  rw [← Real.sqrt_mul ((mul_pos (Real.rpow_pos_of_pos (by norm_num) _) (hardySobolevWeight_pos a b s t)).le)]
  apply Real.sqrt_le_sqrt
  convert hardySobolevWeight_add_le a b hs t (x - t) using 1
  · congr 1
    ring
  · ring

end Weight

section Translation

variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsAddLeftInvariant]
  (logNorm : G →+ ℝ) (hc : Continuous logNorm) (a b s : ℝ) (hs : 0 ≤ s)

private noncomputable def hardyRatio (t x : ℝ) : ℝ :=
  (hardySobolevAmplitude a b s x / hardySobolevAmplitude a b s (x - t)) / hardySobolevBound a b s t

private theorem hardyRatio_abs_le (hs : 0 ≤ s) (t x : ℝ) : |hardyRatio a b s t x| ≤ 1 := by
  unfold hardyRatio
  rw [abs_of_pos (div_pos (div_pos (hardySobolevAmplitude_pos ..)
    (hardySobolevAmplitude_pos ..)) (hardySobolevBound_pos ..))]
  exact (div_le_one (hardySobolevBound_pos ..)).2 (hardySobolevAmplitude_ratio_le a b s hs t x)

private theorem continuous_hardyRatio_left (x : ℝ) : Continuous (fun t => hardyRatio a b s t x) :=
  (continuous_const.div ((continuous_hardySobolevAmplitude a b s).comp
    (continuous_const.sub continuous_id)) (fun _ => (hardySobolevAmplitude_pos ..).ne')).div
    (continuous_hardySobolevBound a b s) (fun _ => (hardySobolevBound_pos ..).ne')

private theorem continuous_hardyRatio_right (t : ℝ) : Continuous (hardyRatio a b s t) :=
  ((continuous_hardySobolevAmplitude a b s).div ((continuous_hardySobolevAmplitude a b s).comp
    (continuous_id.sub continuous_const)) (fun _ => (hardySobolevAmplitude_pos ..).ne')).div_const _

/-- Left translation in the Hardy–Sobolev chart given by multiplication by the
positive square root of the endpoint weight. -/
noncomputable def hardySobolevTranslation (g : G) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  ((hardySobolevBound a b s (logNorm g) : ℝ) : ℂ) •
    (lpTwoRealMultiplier ((continuous_hardyRatio_right a b s (logNorm g)).measurable.comp hc.measurable)
      (fun x => hardyRatio_abs_le a b s hs (logNorm g) (logNorm x))).comp (unweightedShift μ (-g))


theorem hardySobolevTranslation_ae (g : G) (f : Lp ℂ 2 μ) :
    (hardySobolevTranslation μ logNorm hc a b s hs g f : G → ℂ) =ᵐ[μ]
      fun x => ((hardySobolevAmplitude a b s (logNorm x) /
        hardySobolevAmplitude a b s (logNorm (x - g)) : ℝ) : ℂ) * f (x - g) := by
  let t := logNorm g
  let M := lpTwoRealMultiplier (μ := μ)
    ((continuous_hardyRatio_right a b s t).measurable.comp hc.measurable)
    (fun x => hardyRatio_abs_le a b s hs t (logNorm x))
  let c : ℂ := (hardySobolevBound a b s t : ℝ)
  let u := unweightedShift μ (-g) f
  change ((c • M u : Lp ℂ 2 μ) : G → ℂ) =ᵐ[μ] _
  filter_upwards [Lp.coeFn_smul c (M u),
    lpTwoRealMultiplier_ae ((continuous_hardyRatio_right a b s t).measurable.comp hc.measurable)
      (fun x => hardyRatio_abs_le a b s hs t (logNorm x)) u,
    unweightedShift_ae μ (-g) f] with x h₀ h₁ h₂
  simp only [Pi.smul_apply, smul_eq_mul] at h₀
  rw [h₀, h₁, h₂, ← sub_eq_add_neg, ← mul_assoc, ← Complex.ofReal_mul, map_sub]
  congr 2
  dsimp only [hardyRatio, c, t]
  exact mul_div_cancel₀ _ (hardySobolevBound_pos ..).ne'

theorem hardySobolevTranslation_opNorm_le (g : G) :
    ‖hardySobolevTranslation μ logNorm hc a b s hs g‖ ≤
      Real.sqrt ((2 : ℝ) ^ (s / 2) * hardySobolevWeight a b s (logNorm g)) := by
  let t := logNorm g
  let C := hardySobolevBound a b s t
  have hC := (hardySobolevBound_pos a b s t).le
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro f
  let M := lpTwoRealMultiplier (μ := μ)
    ((continuous_hardyRatio_right a b s t).measurable.comp hc.measurable)
    (fun x => hardyRatio_abs_le a b s hs t (logNorm x))
  have hM : ‖M‖ ≤ 1 := lpTwoRealMultiplier_norm_le _ _ zero_le_one
  let u := unweightedShift μ (-g) f
  have hu : ‖u‖ = ‖f‖ := Lp.norm_compMeasurePreserving f (measurePreserving_add_right μ (-g))
  change ‖(C : ℂ) • M u‖ ≤ C * ‖f‖
  rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hC]
  exact mul_le_mul_of_nonneg_left ((M.le_opNorm u).trans (by rw [hu]; nlinarith [norm_nonneg f])) hC

theorem continuous_hardySobolevTranslation [R1Space G] [μ.InnerRegularCompactLTTop]
    [IsLocallyFiniteMeasure μ] :
    Continuous (fun p : G × Lp ℂ 2 μ => hardySobolevTranslation μ logNorm hc a b s hs p.1 p.2) := by
  let shift (g : G) : C(G, G) := ⟨(· + -g), continuous_id.add continuous_const⟩
  have hshift : Continuous shift := ContinuousMap.continuous_of_continuous_uncurry _
    (continuous_snd.add continuous_fst.neg)
  have hu : Continuous (fun p : G × Lp ℂ 2 μ => unweightedShift μ (-p.1) p.2) := by
    exact continuous_snd.compMeasurePreservingLp (hshift.comp continuous_fst)
      (fun p => measurePreserving_add_right μ (-p.1)) (by norm_num)
  let r (t : ℝ) (x : G) := hardyRatio a b s t (logNorm x)
  have hm (t : ℝ) : Measurable (r t) := (continuous_hardyRatio_right a b s t).measurable.comp hc.measurable
  have hr (x : G) : Continuous (fun t => r t x) := continuous_hardyRatio_left a b s (logNorm x)
  have hb (t : ℝ) (x : G) : |r t x| ≤ 1 := hardyRatio_abs_le a b s hs t (logNorm x)
  have hx := (continuous_lpTwoRealMultipliers (μ := μ) r hm hr hb).comp
    (hu.prodMk (hc.comp continuous_fst))
  have hc' := Complex.continuous_ofReal.comp ((continuous_hardySobolevBound a b s).comp (hc.comp
    (continuous_fst : Continuous (Prod.fst : G × Lp ℂ 2 μ → G))))
  exact hc'.smul hx

theorem hardySobolevTranslation_seminorm_bound
    (p : Seminorm ℂ (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)) (hp : Continuous p) :
    ∃ C : ℝ, 0 < C ∧ ∀ g, p (hardySobolevTranslation μ logNorm hc a b s hs g) ≤
      C * Real.sqrt ((2 : ℝ) ^ (s / 2) * hardySobolevWeight a b s (logNorm g)) := by
  obtain ⟨C, hC, hCp⟩ := exists_seminorm_bound_by_norm p hp
  refine ⟨C, hC, fun g => (hCp _).trans ?_⟩
  exact mul_le_mul_of_nonneg_left (hardySobolevTranslation_opNorm_le μ logNorm hc a b s hs g) hC.le

theorem continuous_hardySobolevTranslation_eval [R1Space G] [μ.InnerRegularCompactLTTop]
    [IsLocallyFiniteMeasure μ] (f : Lp ℂ 2 μ) :
    Continuous (fun g => hardySobolevTranslation μ logNorm hc a b s hs g f) := by
  let F : G × Lp ℂ 2 μ → Lp ℂ 2 μ := fun p =>
    hardySobolevTranslation μ logNorm hc a b s hs p.1 p.2
  have hF : Continuous F := continuous_hardySobolevTranslation μ logNorm hc a b s hs
  have hgraph : Continuous (fun g : G => (g, f)) := continuous_id.prodMk continuous_const
  change Continuous (F ∘ fun g : G => (g, f))
  exact hF.comp hgraph

theorem measurable_hardySobolevTranslation_opNorm [R1Space G] [μ.InnerRegularCompactLTTop]
    [IsLocallyFiniteMeasure μ] :
    Measurable (fun g => ‖hardySobolevTranslation μ logNorm hc a b s hs g‖) :=
  measurable_opNorm_of_continuous_eval (T := hardySobolevTranslation μ logNorm hc a b s hs)
    (continuous_hardySobolevTranslation_eval μ logNorm hc a b s hs)

theorem continuous_hardySobolevTranslation_pointwise_seminorm [R1Space G] [μ.InnerRegularCompactLTTop]
    [IsLocallyFiniteMeasure μ] (p : Seminorm ℂ (Lp ℂ 2 μ →Lₚₜ[ℂ] Lp ℂ 2 μ)) (hp : Continuous p) :
    Continuous (fun g => p (hardySobolevTranslation μ logNorm hc a b s hs g)) :=
  continuous_pointwise_seminorm_of_continuous_eval
    (T := hardySobolevTranslation μ logNorm hc a b s hs)
    (continuous_hardySobolevTranslation_eval μ logNorm hc a b s hs) p hp

/-- For a single endpoint, the operator norm has polynomial growth in
the modulus and its reciprocal. -/
theorem hardySobolevTranslation_singleton_polynomial (g : G) :
    ‖hardySobolevTranslation μ logNorm hc b b s hs g‖ ≤
      (Real.sqrt ((2 : ℝ) ^ (s / 2))) *
        Real.exp ((|b| + s / 2) * |logNorm g|) := by
  let t := logNorm g
  have hp : 1 + t ^ 2 ≤ Real.exp (2 * |t|) := by
    rw [two_mul, Real.exp_add, ← sq, ← sq_abs t]
    have h := Real.add_one_le_exp |t|
    have hsq : (|t| + 1) ^ 2 ≤ Real.exp |t| ^ 2 :=
      pow_le_pow_left₀ (by positivity) h 2
    nlinarith [abs_nonneg t]
  have hp' : (1 + t ^ 2) ^ (s / 2) ≤ Real.exp (s * |t|) := by
    calc
      _ ≤ (Real.exp (2 * |t|)) ^ (s / 2) :=
        Real.rpow_le_rpow (by positivity) hp (by positivity)
      _ = _ := by rw [← Real.exp_mul]; congr 1; ring
  have hx : b * t ≤ |b| * |t| := by rw [← abs_mul]; exact le_abs_self _
  have hw : hardySobolevWeight b b s t ≤ Real.exp ((2 * |b| + s) * |t|) := by
    unfold hardySobolevWeight
    rw [max_self, add_mul, Real.exp_add]
    exact mul_le_mul (Real.exp_le_exp.mpr (by linarith)) hp'
      (Real.rpow_nonneg (by positivity) _) (Real.exp_pos _).le
  refine (hardySobolevTranslation_opNorm_le μ logNorm hc b b s hs g).trans ?_
  change Real.sqrt ((2 : ℝ) ^ (s / 2) * hardySobolevWeight b b s t) ≤ _
  calc
    _ ≤ Real.sqrt ((2 : ℝ) ^ (s / 2) * Real.exp ((2 * |b| + s) * |t|)) :=
      Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hw (Real.rpow_nonneg (by norm_num) _))
    _ = _ := by
      rw [Real.sqrt_mul (Real.rpow_nonneg (by norm_num) _), Real.sqrt_eq_rpow (Real.exp _),
        ← Real.exp_mul]
      congr 2
      ring

/-- Multiplication by the square root of the endpoint weight realizes the
Hardy–Sobolev norm in ordinary Haar L². -/
noncomputable def hardySobolevChartAmplitude : C(G, ℂ) :=
  ⟨fun x => hardySobolevAmplitude a b s (logNorm x),
    Complex.continuous_ofReal.comp ((continuous_hardySobolevAmplitude a b s).comp hc)⟩

omit [IsTopologicalAddGroup G] [μ.IsAddLeftInvariant] in
theorem hardySobolev_chart_norm_sq [IsFiniteMeasureOnCompacts μ] (f : C_c(G, ℂ)) :
    ‖sobolevWeightedTest μ (hardySobolevChartAmplitude logNorm hc a b s) f‖ ^ 2 =
      ∫ x, ‖f x‖ ^ 2 * hardySobolevWeight a b s (logNorm x) ∂μ := by
  rw [sobolevWeightedTest_norm_sq]
  apply integral_congr_ae
  filter_upwards with x
  change ‖f x‖ ^ 2 * ‖(hardySobolevAmplitude a b s (logNorm x) : ℂ)‖ ^ 2 = _
  rw [Complex.norm_real, Real.norm_of_nonneg (hardySobolevAmplitude_pos ..).le]
  unfold hardySobolevAmplitude
  rw [Real.sq_sqrt (hardySobolevWeight_nonneg ..)]

omit [IsTopologicalAddGroup G] [μ.IsAddLeftInvariant] in
theorem denseRange_hardySobolevChart [T2Space G] [LocallyCompactSpace G] [μ.Regular] :
    DenseRange (sobolevWeightedTest μ (hardySobolevChartAmplitude logNorm hc a b s)) := by
  apply denseRange_sobolevWeightedTest
  intro x
  exact Complex.ofReal_ne_zero.mpr (hardySobolevAmplitude_pos ..).ne'

theorem hardySobolevTranslation_chart_ae [IsFiniteMeasureOnCompacts μ] (g : G) (f : C_c(G, ℂ)) :
    (hardySobolevTranslation μ logNorm hc a b s hs g
      (sobolevWeightedTest μ (hardySobolevChartAmplitude logNorm hc a b s) f) : G → ℂ)
      =ᵐ[μ] fun x => (hardySobolevAmplitude a b s (logNorm x) : ℂ) * f (x - g) := by
  let v := sobolevWeightedTest μ (hardySobolevChartAmplitude logNorm hc a b s) f
  have hv := (measurePreserving_add_right μ (-g)).quasiMeasurePreserving.ae_eq_comp
    (sobolevWeightedTest_ae μ (hardySobolevChartAmplitude logNorm hc a b s) f)
  have ht := hardySobolevTranslation_ae μ logNorm hc a b s hs g v
  filter_upwards [ht, hv] with x htx hvx
  rw [htx]
  have hx : v (x - g) =
      (hardySobolevAmplitude a b s (logNorm (x - g)) : ℂ) * f (x - g) := by
    rw [sub_eq_add_neg]
    exact hvx
  rw [hx, Complex.ofReal_div, ← mul_assoc, div_mul_cancel₀]
  exact Complex.ofReal_ne_zero.mpr (hardySobolevAmplitude_pos ..).ne'

/-- Scalar evaluations of compactly supported continuous regularizations are
integrable for continuous linear functionals in the pointwise topology. -/
theorem integrable_hardySobolevTranslation_pointwise_scalar
    [R1Space G] [μ.InnerRegularCompactLTTop] [IsLocallyFiniteMeasure μ]
    (φ : C_c(G, ℂ)) (ℓ : (Lp ℂ 2 μ →Lₚₜ[ℂ] Lp ℂ 2 μ) →L[ℂ] ℂ) :
    Integrable (fun g => ℓ (φ g • hardySobolevTranslation μ logNorm hc a b s hs g)) μ := by
  let T : G → (Lp ℂ 2 μ →Lₚₜ[ℂ] Lp ℂ 2 μ) := hardySobolevTranslation μ logNorm hc a b s hs
  have hT : Continuous T := PointwiseConvergenceCLM.continuous_of_continuous_eval
    (continuous_hardySobolevTranslation_eval μ logNorm hc a b s hs)
  change Integrable (fun g => ℓ (φ g • T g)) μ
  have hφT : Continuous (fun g => φ g • T g) := by
    apply PointwiseConvergenceCLM.continuous_of_continuous_eval
    intro f
    have hTf := continuous_hardySobolevTranslation_eval μ logNorm hc a b s hs f
    exact φ.continuous.smul hTf
  apply Continuous.integrable_of_hasCompactSupport (ℓ.continuous.comp hφT)
  apply φ.hasCompactSupport.mono
  intro g hg hφ
  exact hg (by simp [hφ])

end Translation

section Multiplicative

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant]
  (logNorm : G →* Multiplicative ℝ) (hc : Continuous logNorm) (a b s : ℝ) (hs : 0 ≤ s)

private noncomputable def unweightedMulLeftShift (g : G) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  (Lp.compMeasurePreservingₗᵢ ℂ (g⁻¹ * ·)
    (measurePreserving_mul_left μ g⁻¹)).toContinuousLinearMap

/-- Left translation in the positive-amplitude chart of the weighted Hilbert
space of a multiplicative group. -/
noncomputable def hardySobolevMulTranslation (g : G) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  let t := (logNorm g).toAdd
  let l (x : G) := (logNorm x).toAdd
  have hl : Continuous l := hc
  ((hardySobolevBound a b s t : ℝ) : ℂ) •
    (lpTwoRealMultiplier ((continuous_hardyRatio_right a b s t).measurable.comp hl.measurable)
      (fun x => hardyRatio_abs_le a b s hs t (l x))).comp (unweightedMulLeftShift μ g)

/-- The weighted translation is bounded by the endpoint weight at its shift. -/
theorem hardySobolevMulTranslation_opNorm_le (g : G) :
    ‖hardySobolevMulTranslation μ logNorm hc a b s hs g‖ ≤
      Real.sqrt ((2 : ℝ) ^ (s / 2) * hardySobolevWeight a b s (logNorm g).toAdd) := by
  let t := (logNorm g).toAdd
  let l (x : G) : ℝ := (logNorm x).toAdd
  have hl : Continuous l := hc
  let M := lpTwoRealMultiplier (μ := μ)
    ((continuous_hardyRatio_right a b s t).measurable.comp hl.measurable)
    (fun x => hardyRatio_abs_le a b s hs t (logNorm x).toAdd)
  have hm : ‖M‖ ≤ 1 := lpTwoRealMultiplier_norm_le _ _ zero_le_one
  have hu : ‖unweightedMulLeftShift μ g‖ ≤ 1 :=
    LinearIsometry.norm_toContinuousLinearMap_le _
  change ‖(hardySobolevBound a b s t : ℂ) • M.comp (unweightedMulLeftShift μ g)‖ ≤ _
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (hardySobolevBound_pos ..)]
  apply (mul_le_mul_of_nonneg_left
    ((M.opNorm_comp_le _).trans (mul_le_one₀ hm (norm_nonneg _) hu))
    (hardySobolevBound_pos ..).le).trans_eq
  rw [mul_one]
  rfl

theorem hardySobolevMulTranslation_ae (g : G) (f : Lp ℂ 2 μ) :
    (hardySobolevMulTranslation μ logNorm hc a b s hs g f : G → ℂ) =ᵐ[μ]
      fun x => ((hardySobolevAmplitude a b s (logNorm x).toAdd /
        hardySobolevAmplitude a b s (logNorm (g⁻¹ * x)).toAdd : ℝ) : ℂ) * f (g⁻¹ * x) := by
  let t := (logNorm g).toAdd
  let l (x : G) := (logNorm x).toAdd
  have hlc : Continuous l := hc
  let M := lpTwoRealMultiplier (μ := μ)
    ((continuous_hardyRatio_right a b s t).measurable.comp hlc.measurable)
    (fun x => hardyRatio_abs_le a b s hs t (l x))
  let c : ℂ := (hardySobolevBound a b s t : ℝ)
  let u := unweightedMulLeftShift μ g f
  have hu : (u : G → ℂ) =ᵐ[μ] fun x => f (g⁻¹ * x) :=
    Lp.coeFn_compMeasurePreserving f (measurePreserving_mul_left μ g⁻¹)
  change ((c • M u : Lp ℂ 2 μ) : G → ℂ) =ᵐ[μ] _
  filter_upwards [Lp.coeFn_smul c (M u),
    lpTwoRealMultiplier_ae ((continuous_hardyRatio_right a b s t).measurable.comp hlc.measurable)
      (fun x => hardyRatio_abs_le a b s hs t (l x)) u, hu] with x h₀ h₁ h₂
  simp only [Pi.smul_apply, smul_eq_mul] at h₀
  rw [h₀, h₁, h₂, ← mul_assoc, ← Complex.ofReal_mul]
  have hl : (logNorm (g⁻¹ * x)).toAdd = l x - t := by
    rw [map_mul, map_inv]
    change -t + l x = l x - t
    abel
  rw [hl]
  congr 2
  dsimp only [hardyRatio, c, t]
  exact mul_div_cancel₀ _ (hardySobolevBound_pos ..).ne'

private theorem sqrt_logWeight_translate_le (t x : ℝ) :
    Real.sqrt (1 + x ^ 2) ≤ (1 + |t|) * Real.sqrt (1 + (x - t) ^ 2) := by
  let r := Real.sqrt (1 + (x - t) ^ 2)
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hr1 : 1 ≤ r := by
    simpa [r] using Real.sqrt_le_sqrt (show 1 ≤ 1 + (x - t) ^ 2 by nlinarith)
  have hrsq : r ^ 2 = 1 + (x - t) ^ 2 := Real.sq_sqrt (by positivity)
  have hau : |x - t| ≤ r := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by linarith)
  have hcross : (x - t) * t ≤ r * |t| := by
    calc
      _ ≤ |(x - t) * t| := le_abs_self _
      _ = |x - t| * |t| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right hau (abs_nonneg _)
  calc
    Real.sqrt (1 + x ^ 2) ≤ r + |t| := Real.sqrt_le_iff.mpr
      ⟨add_nonneg hr (abs_nonneg _), by nlinarith [sq_abs t]⟩
    _ ≤ (1 + |t|) * r := by
      rw [add_mul, one_mul]
      exact add_le_add_right (le_mul_of_one_le_right (abs_nonneg _) hr1) _

private theorem hardySobolevAmplitude_singleton (b s x : ℝ) :
    hardySobolevAmplitude b b s x = Real.exp (b * x) * (Real.sqrt (1 + x ^ 2)) ^ (s / 2) := by
  have h : 0 ≤ 1 + x ^ 2 := by positivity
  have hr : Real.sqrt ((1 + x ^ 2) ^ (s / 2)) = (Real.sqrt (1 + x ^ 2)) ^ (s / 2) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul h, ← Real.rpow_mul h]
    congr 1
    ring
  rw [hardySobolevAmplitude, hardySobolevWeight, max_self, Real.sqrt_mul (Real.exp_pos _).le, hr]
  congr 1
  rw [show 2 * b * x = b * x + b * x by ring, Real.exp_add, ← sq, Real.sqrt_sq (Real.exp_pos _).le]

private theorem hardySobolevAmplitude_singleton_ratio_le (b s : ℝ) (hs : 0 ≤ s) (t x : ℝ) :
    hardySobolevAmplitude b b s x / hardySobolevAmplitude b b s (x - t) ≤
      Real.exp (b * t) * (1 + |t|) ^ (s / 2) := by
  apply (div_le_iff₀ (hardySobolevAmplitude_pos ..)).mpr
  have hm := Real.rpow_le_rpow (Real.sqrt_nonneg (1 + x ^ 2))
    (sqrt_logWeight_translate_le t x) (div_nonneg hs (by norm_num : (0 : ℝ) ≤ 2))
  rw [Real.mul_rpow (by positivity) (Real.sqrt_nonneg _)] at hm
  rw [hardySobolevAmplitude_singleton, hardySobolevAmplitude_singleton]
  calc
    _ ≤ Real.exp (b * x) * ((1 + |t|) ^ (s / 2) * Real.sqrt (1 + (x - t) ^ 2) ^ (s / 2)) :=
      mul_le_mul_of_nonneg_left hm (Real.exp_pos _).le
    _ = _ := by
      conv_lhs => rw [show b * x = b * t + b * (x - t) by ring, Real.exp_add]
      ring

/-- The bound for a singleton strip tends to one as the logarithmic shift
tends to zero. It retains the exact exponential twist. -/
theorem hardySobolevMulTranslation_singleton_opNorm_le (g : G) :
    ‖hardySobolevMulTranslation μ logNorm hc b b s hs g‖ ≤
      Real.exp (b * (logNorm g).toAdd) * (1 + |(logNorm g).toAdd|) ^ (s / 2) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro f
  let v := unweightedMulLeftShift μ g f
  have hv : ‖v‖ = ‖f‖ := Lp.norm_compMeasurePreserving f (measurePreserving_mul_left μ g⁻¹)
  rw [← hv]
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [hardySobolevMulTranslation_ae μ logNorm hc b b s hs g f,
    Lp.coeFn_compMeasurePreserving f (measurePreserving_mul_left μ g⁻¹)] with x hx hvx
  have hlog : (logNorm (g⁻¹ * x)).toAdd = (logNorm x).toAdd - (logNorm g).toAdd := by
    rw [map_mul, map_inv]
    change -(logNorm g).toAdd + (logNorm x).toAdd = _
    abel
  change v x = f (g⁻¹ * x) at hvx
  rw [hx, hvx, hlog, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (div_nonneg (hardySobolevAmplitude_pos ..).le (hardySobolevAmplitude_pos ..).le)]
  exact mul_le_mul_of_nonneg_right (hardySobolevAmplitude_singleton_ratio_le b s hs _ _) (norm_nonneg _)

/-- Conjugating by the abscissa twist multiplies each translation by the
corresponding positive character in the unweighted Hilbert chart. -/
theorem hardySobolevMulTranslation_singleton_eq_zeroLine (g : G) :
    hardySobolevMulTranslation μ logNorm hc b b s hs g =
      Real.exp (b * (logNorm g).toAdd) • hardySobolevMulTranslation μ logNorm hc 0 0 s hs g := by
  ext f : 1
  apply Lp.ext
  let c := Real.exp (b * (logNorm g).toAdd)
  filter_upwards [hardySobolevMulTranslation_ae μ logNorm hc b b s hs g f,
    hardySobolevMulTranslation_ae μ logNorm hc 0 0 s hs g f,
    Lp.coeFn_smul c (hardySobolevMulTranslation μ logNorm hc 0 0 s hs g f)] with x hx h0 hc'
  change (hardySobolevMulTranslation μ logNorm hc b b s hs g f) x =
    (c • hardySobolevMulTranslation μ logNorm hc 0 0 s hs g f) x
  have hratio : hardySobolevAmplitude b b s (logNorm x).toAdd /
      hardySobolevAmplitude b b s (logNorm (g⁻¹ * x)).toAdd =
      c * (hardySobolevAmplitude 0 0 s (logNorm x).toAdd /
        hardySobolevAmplitude 0 0 s (logNorm (g⁻¹ * x)).toAdd) := by
    have hlog : (logNorm x).toAdd = (logNorm g).toAdd + (logNorm (g⁻¹ * x)).toAdd := by
      rw [map_mul, map_inv]
      change (logNorm x).toAdd = (logNorm g).toAdd + (-(logNorm g).toAdd + (logNorm x).toAdd)
      abel
    simp only [hardySobolevAmplitude_singleton, zero_mul, Real.exp_zero, one_mul]
    have he : Real.exp (b * (logNorm x).toAdd) = c * Real.exp (b * (logNorm (g⁻¹ * x)).toAdd) := by
      conv_lhs => rw [hlog, mul_add, Real.exp_add]
    rw [he, mul_assoc, mul_div_assoc, mul_div_mul_left _ _ (Real.exp_pos _).ne']
  rw [hx, show (c • hardySobolevMulTranslation μ logNorm hc 0 0 s hs g f) x =
      c • (hardySobolevMulTranslation μ logNorm hc 0 0 s hs g f) x from hc', h0, hratio,
    Complex.real_smul, Complex.ofReal_mul, mul_assoc]

theorem continuous_hardySobolevMulTranslation [R1Space G] [μ.InnerRegularCompactLTTop]
    [IsLocallyFiniteMeasure μ] :
    Continuous (fun p : G × Lp ℂ 2 μ => hardySobolevMulTranslation μ logNorm hc a b s hs p.1 p.2) := by
  let l (g : G) := (logNorm g).toAdd
  let shift (g : G) : C(G, G) := ⟨(g⁻¹ * ·), continuous_const.mul continuous_id⟩
  have hshift : Continuous shift := ContinuousMap.continuous_of_continuous_uncurry _
    (continuous_fst.inv.mul continuous_snd)
  have hu : Continuous (fun p : G × Lp ℂ 2 μ => unweightedMulLeftShift μ p.1 p.2) := by
    exact continuous_snd.compMeasurePreservingLp (hshift.comp continuous_fst)
      (fun p => measurePreserving_mul_left μ p.1⁻¹) (by norm_num)
  let r (t : ℝ) (x : G) := hardyRatio a b s t (l x)
  have hl : Continuous l := hc
  have hm (t : ℝ) : Measurable (r t) := (continuous_hardyRatio_right a b s t).measurable.comp hl.measurable
  have hr (x : G) : Continuous (fun t => r t x) := continuous_hardyRatio_left a b s (l x)
  have hb (t : ℝ) (x : G) : |r t x| ≤ 1 := hardyRatio_abs_le a b s hs t (l x)
  have hx := (continuous_lpTwoRealMultipliers (μ := μ) r hm hr hb).comp
    (hu.prodMk (hl.comp continuous_fst))
  have hc' := Complex.continuous_ofReal.comp ((continuous_hardySobolevBound a b s).comp
    (hl.comp (continuous_fst : Continuous (Prod.fst : G × Lp ℂ 2 μ → G))))
  exact hc'.smul hx

theorem hardySobolevMulTranslation_one (f : Lp ℂ 2 μ) :
    hardySobolevMulTranslation μ logNorm hc a b s hs 1 f = f := by
  apply Lp.ext
  filter_upwards [hardySobolevMulTranslation_ae μ logNorm hc a b s hs 1 f] with x hx
  simpa [(hardySobolevAmplitude_pos a b s (logNorm x).toAdd).ne'] using hx

theorem hardySobolevMulTranslation_mul (g h : G) (f : Lp ℂ 2 μ) :
    hardySobolevMulTranslation μ logNorm hc a b s hs (g * h) f =
      hardySobolevMulTranslation μ logNorm hc a b s hs g
        (hardySobolevMulTranslation μ logNorm hc a b s hs h f) := by
  let T := hardySobolevMulTranslation μ logNorm hc a b s hs
  change T (g * h) f = T g (T h f)
  apply Lp.ext
  filter_upwards [hardySobolevMulTranslation_ae μ logNorm hc a b s hs (g * h) f,
    hardySobolevMulTranslation_ae μ logNorm hc a b s hs g (T h f),
    (measurePreserving_mul_left μ g⁻¹).quasiMeasurePreserving.ae
      (hardySobolevMulTranslation_ae μ logNorm hc a b s hs h f)] with x hgh hg hh
  have hpoint : (g * h)⁻¹ * x = h⁻¹ * (g⁻¹ * x) := by rw [mul_inv_rev, mul_assoc]
  rw [hgh, hg, hh, hpoint]
  simp only [← mul_assoc, ← Complex.ofReal_mul,
    div_mul_div_cancel₀ (hardySobolevAmplitude_pos ..).ne']

end Multiplicative

section Convolution

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [R1Space G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsMulLeftInvariant] [μ.InnerRegularCompactLTTop] [IsLocallyFiniteMeasure μ]
  (m : G →* Multiplicative ℝ) (hm : Continuous m)

theorem integrable_hardySobolev_convolution_orbit (l r s : ℝ) (hs : 0 ≤ s)
    (φ : C_c(G, ℂ)) (f : Lp ℂ 2 μ) :
    Integrable (fun g => φ g • (hardySobolevMulTranslation μ m hm l r s hs g) f) μ := by
  let T (p : G × Lp ℂ 2 μ) : Lp ℂ 2 μ :=
    hardySobolevMulTranslation μ m hm l r s hs p.1 p.2
  have hT : Continuous T := continuous_hardySobolevMulTranslation μ m hm l r s hs
  have hpair : Continuous (fun g : G => (g, f)) := continuous_id.prodMk continuous_const
  have hc : Continuous (T ∘ fun g : G => (g, f)) := hT.comp hpair
  exact (φ.continuous.smul hc).integrable_of_hasCompactSupport φ.hasCompactSupport.smul_right

/-- Haar convolution on the ambient Hardy–Sobolev space, written in
amplitude coordinates. It is the integral of the left-translation action. -/
noncomputable def hardySobolevConvolution (l r s : ℝ) (hs : 0 ≤ s)
    (φ : C_c(G, ℂ)) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ := by
  let A : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ :=
    { toFun := fun f => ∫ g, φ g • (hardySobolevMulTranslation μ m hm l r s hs g) f ∂μ
      map_add' := fun f h => by
        simp only [map_add, smul_add]
        exact integral_add (integrable_hardySobolev_convolution_orbit μ m hm l r s hs φ f)
          (integrable_hardySobolev_convolution_orbit μ m hm l r s hs φ h)
      map_smul' := fun c f => by
        simp only [RingHom.id_apply, map_smul, smul_comm (φ _) c, integral_smul] }
  let b (g : G) := Real.sqrt
    ((2 : ℝ) ^ (s / 2) * hardySobolevWeight l r s ((m g).toAdd))
  have hb : Continuous b := Real.continuous_sqrt.comp (continuous_const.mul
    ((continuous_hardySobolevWeight l r s).comp (continuous_toAdd.comp hm)))
  have hi : Integrable (fun g => ‖φ g‖ * b g) μ :=
    (φ.continuous.norm.mul hb).integrable_of_hasCompactSupport
      (φ.hasCompactSupport.norm.mul_right)
  refine A.mkContinuous (∫ g, ‖φ g‖ * b g ∂μ) (fun f => ?_)
  refine (norm_integral_le_integral_norm _).trans ?_
  rw [← integral_mul_const]
  refine integral_mono (integrable_hardySobolev_convolution_orbit μ m hm l r s hs φ f).norm
    (hi.mul_const _) (fun g => ?_)
  rw [norm_smul, mul_assoc]
  exact mul_le_mul_of_nonneg_left
    (((hardySobolevMulTranslation μ m hm l r s hs g).le_opNorm f).trans
      (mul_le_mul_of_nonneg_right
        (hardySobolevMulTranslation_opNorm_le μ m hm l r s hs g) (norm_nonneg _))) (norm_nonneg _)

end Convolution

end Masullo
