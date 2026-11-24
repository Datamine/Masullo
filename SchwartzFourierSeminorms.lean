import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open MeasureTheory Set Filter Topology
open scoped SchwartzMap FourierTransform ENNReal NNReal LineDeriv

namespace Masullo

noncomputable section

private abbrev RealSchwartz := 𝓢(ℝ, ℂ)

private def realSchwartzDerivative : RealSchwartz →L[ℂ] RealSchwartz :=
  SchwartzMap.derivCLM ℂ ℂ

private def schwartzMultiplyX : RealSchwartz →L[ℂ] RealSchwartz :=
  SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => (x : ℂ))

private theorem schwartzMultiplyX_apply (f : RealSchwartz) (x : ℝ) :
    schwartzMultiplyX f x = (x : ℂ) * f x :=
  SchwartzMap.smulLeftCLM_apply_apply (Complex.ofRealCLM.hasTemperateGrowth) f x

private def realSchwartzDerivativeIter : ℕ → RealSchwartz →L[ℂ] RealSchwartz
  | 0 => ContinuousLinearMap.id ℂ RealSchwartz
  | n + 1 => realSchwartzDerivative.comp (realSchwartzDerivativeIter n)

private def schwartzMultiplyXIter : ℕ → RealSchwartz →L[ℂ] RealSchwartz
  | 0 => ContinuousLinearMap.id ℂ RealSchwartz
  | n + 1 => schwartzMultiplyX.comp (schwartzMultiplyXIter n)

private theorem realSchwartzDerivativeIter_apply (n : ℕ) (f : RealSchwartz) (x : ℝ) :
    realSchwartzDerivativeIter n f x = iteratedDeriv n f x := by
  induction n generalizing x with
  | zero => simp [realSchwartzDerivativeIter]
  | succ n ih =>
    change deriv (realSchwartzDerivativeIter n f) x = _
    rw [iteratedDeriv_succ]
    exact congrFun (congrArg deriv (funext ih)) x

private theorem schwartzMultiplyXIter_apply (n : ℕ) (f : RealSchwartz) (x : ℝ) :
    schwartzMultiplyXIter n f x = (x : ℂ) ^ n * f x := by
  induction n with
  | zero => simp [schwartzMultiplyXIter]
  | succ n ih =>
    change schwartzMultiplyX (schwartzMultiplyXIter n f) x = _
    rw [schwartzMultiplyX_apply, ih, pow_succ']
    ring

private def schwartzL2Norm (f : RealSchwartz) : ℝ :=
  ‖f.toLp 2 (volume : Measure ℝ)‖

private theorem integral_norm_unitInterval_le_L2 (f : RealSchwartz) (x : ℝ) :
    (∫ y in Ioc x (x + 1), ‖f y‖) ≤ schwartzL2Norm f := by
  let μ := (volume : Measure ℝ).restrict (Ioc x (x + 1))
  letI : IsProbabilityMeasure μ := ⟨by
    change volume.restrict (Ioc x (x + 1)) univ = _
    rw [Measure.restrict_apply_univ, Real.volume_Ioc]
    simp⟩
  have h := eLpNorm_le_eLpNorm_of_exponent_le (μ := μ) (f := fun y => f y)
    (show (1 : ℝ≥0∞) ≤ 2 by norm_num)
    (f.continuous.aestronglyMeasurable (μ := μ))
  have h' := h.trans (eLpNorm_mono_measure (fun y => f y) Measure.restrict_le_self)
  rw [eLpNorm_one_eq_lintegral_enorm] at h'
  have hfin := (f.memLp 2 (volume : Measure ℝ)).eLpNorm_ne_top
  have he := ENNReal.toReal_mono hfin h'
  rw [← ofReal_integral_norm_eq_lintegral_enorm
    (f.integrable.restrict (s := Ioc x (x + 1))),
    ENNReal.toReal_ofReal (integral_nonneg fun _ => norm_nonneg _)] at he
  exact he.trans_eq (SchwartzMap.norm_toLp.symm)

private theorem schwartz_sup_le_L2_and_derivative (f : RealSchwartz) (x : ℝ) :
    ‖f x‖ ≤ schwartzL2Norm f + schwartzL2Norm (realSchwartzDerivative f) := by
  let D := realSchwartzDerivative f
  let I := Ioc x (x + 1)
  have hd (y : ℝ) (hy : y ∈ I) : ‖f x - f y‖ ≤ schwartzL2Norm D := by
    have hv : ∫ t in x..y, D t = f y - f x :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => f.hasDerivAt t)
        (D.continuous.intervalIntegrable x y)
    rw [norm_sub_rev, ← hv, intervalIntegral.integral_of_le hy.1.le]
    exact (norm_integral_le_integral_norm _).trans
      ((setIntegral_mono_set ((D.integrable (μ := (volume : Measure ℝ))).norm.integrableOn) (Eventually.of_forall fun _ => norm_nonneg _)
        (Eventually.of_forall fun t ht => Ioc_subset_Ioc_right hy.2 ht)).trans
        (integral_norm_unitInterval_le_L2 D x))
  have hpoint (y : ℝ) (hy : y ∈ I) : ‖f x‖ ≤ ‖f y‖ + schwartzL2Norm D := by
    have h := norm_add_le (f x - f y) (f y)
    rw [sub_add_cancel] at h
    exact h.trans (by linarith [hd y hy])
  have hm : (volume : Measure ℝ).real I = 1 := by
    simp [I, measureReal_def, Real.volume_Ioc]
  letI : IsFiniteMeasure ((volume : Measure ℝ).restrict I) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact (by dsimp [I]; rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top)⟩
  have hle := integral_mono_ae (μ := (volume : Measure ℝ).restrict I)
    (integrable_const ‖f x‖) (f.integrable.restrict.norm.add (integrable_const (schwartzL2Norm D)))
    (by
      filter_upwards [self_mem_ae_restrict (measurableSet_Ioc : MeasurableSet I)] with y hy
      exact hpoint y hy)
  have he : ((volume : Measure ℝ).restrict I).real univ = 1 := by
    simpa only [measureReal_def, Measure.restrict_apply_univ] using hm
  simp only [Pi.add_apply] at hle
  rw [integral_add f.integrable.restrict.norm (integrable_const (schwartzL2Norm D)),
    integral_const, integral_const, he, one_smul, one_smul] at hle
  exact hle.trans (add_le_add (integral_norm_unitInterval_le_L2 f x) le_rfl)


private def fourierSlopeConstant : ℂ := -(2 * (Real.pi : ℂ) * Complex.I)

private theorem fourierSlopeConstant_ne_zero : fourierSlopeConstant ≠ 0 := by
  unfold fourierSlopeConstant
  exact neg_ne_zero.mpr (mul_ne_zero
    (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_pos.ne')) Complex.I_ne_zero)

private theorem realSchwartzDerivative_fourier (f : RealSchwartz) :
    realSchwartzDerivative (𝓕 f) = 𝓕 (fourierSlopeConstant • schwartzMultiplyX f) := by
  have h := SchwartzMap.lineDerivOp_fourier_eq f (1 : ℝ)
  have h₁ : ∂_{(1 : ℝ)} (𝓕 f) = realSchwartzDerivative (𝓕 f) := by
    ext x
    rw [SchwartzMap.lineDerivOp_apply_eq_fderiv, realSchwartzDerivative, SchwartzMap.derivCLM_apply]
    exact (hasDerivAt_iff_hasFDerivAt.mp ((𝓕 f).hasDerivAt x)).unique
      ((𝓕 f).hasFDerivAt x) |> fun h => (congrFun (congrArg DFunLike.coe h) 1).symm.trans (by simp)
  rw [h₁] at h
  rw [h]
  congr 2
  ext x
  have hg : (fun x : ℝ => inner ℝ x 1).HasTemperateGrowth :=
    ((innerSL ℝ).flip (1 : ℝ)).hasTemperateGrowth
  rw [schwartzMultiplyX_apply, SchwartzMap.smulLeftCLM_apply_apply hg]
  simp

private theorem fourier_derivativeIter_eq (m : ℕ) (f : RealSchwartz) :
    realSchwartzDerivativeIter m (𝓕 f) = 𝓕 (fourierSlopeConstant ^ m • schwartzMultiplyXIter m f) := by
  induction m with
  | zero => simp [realSchwartzDerivativeIter, schwartzMultiplyXIter]
  | succ m ih =>
    change realSchwartzDerivative (realSchwartzDerivativeIter m (𝓕 f)) = _
    rw [ih, realSchwartzDerivative_fourier]
    congr 1
    change fourierSlopeConstant • schwartzMultiplyX
      (fourierSlopeConstant ^ m • schwartzMultiplyXIter m f) =
      fourierSlopeConstant ^ (m + 1) • schwartzMultiplyX (schwartzMultiplyXIter m f)
    rw [map_smul, smul_smul, pow_succ']

private theorem schwartzL2Norm_fourier (f : RealSchwartz) : schwartzL2Norm (𝓕 f) = schwartzL2Norm f := by
  unfold schwartzL2Norm
  rw [← SchwartzMap.toLp_fourier_eq, MeasureTheory.Lp.norm_fourier_eq]

/-- The seminorms in (D.1.10.3). -/
def schwartzFourierL2Seminorms : SeminormFamily ℂ RealSchwartz (ℕ × ℕ) :=
  fun p => (normSeminorm ℂ (Lp ℂ 2 (volume : Measure ℝ))).comp
    ((SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure ℝ)).toLinearMap.comp
      ((realSchwartzDerivativeIter p.1).toLinearMap.comp
        ((SchwartzMap.fourierTransformCLM ℂ).toLinearMap.comp
          (realSchwartzDerivativeIter p.2).toLinearMap)))

private theorem schwartzFourierL2Seminorms_eq (m n : ℕ) (f : RealSchwartz) :
    schwartzFourierL2Seminorms (m, n) f =
      ‖fourierSlopeConstant‖ ^ m *
        schwartzL2Norm (schwartzMultiplyXIter m (realSchwartzDerivativeIter n f)) := by
  change schwartzL2Norm (realSchwartzDerivativeIter m (𝓕 (realSchwartzDerivativeIter n f))) = _
  rw [fourier_derivativeIter_eq, schwartzL2Norm_fourier]
  change ‖SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure ℝ)
    (fourierSlopeConstant ^ m • schwartzMultiplyXIter m (realSchwartzDerivativeIter n f))‖ = _
  rw [map_smul, norm_smul, norm_pow]
  rfl

private theorem schwartzDerivative_weight_succ (m : ℕ) (f : RealSchwartz) :
    realSchwartzDerivative (schwartzMultiplyXIter (m + 1) f) =
      ((m + 1 : ℕ) : ℂ) • schwartzMultiplyXIter m f +
        schwartzMultiplyXIter (m + 1) (realSchwartzDerivative f) := by
  ext x
  change deriv (schwartzMultiplyXIter (m + 1) f) x = _
  have he : (fun y => schwartzMultiplyXIter (m + 1) f y) = fun y : ℝ => (y : ℂ) ^ (m + 1) * f y := by
    funext y
    exact schwartzMultiplyXIter_apply _ _ _
  have h := (((hasDerivAt_id x).ofReal_comp).pow (m + 1)).mul (f.hasDerivAt x)
  change deriv (fun y => schwartzMultiplyXIter (m + 1) f y) x = _
  rw [he]
  have ht := h.deriv
  simpa [schwartzMultiplyXIter_apply, realSchwartzDerivative, SchwartzMap.derivCLM_apply,
    mul_assoc, smul_eq_mul, add_comm, Pi.mul_def, Pi.pow_def] using ht

private theorem schwartzL2Norm_add_le (f g : RealSchwartz) :
    schwartzL2Norm (f + g) ≤ schwartzL2Norm f + schwartzL2Norm g := by
  change ‖SchwartzMap.toLpCLM ℂ ℂ 2 volume (f + g)‖ ≤
    ‖SchwartzMap.toLpCLM ℂ ℂ 2 volume f‖ + ‖SchwartzMap.toLpCLM ℂ ℂ 2 volume g‖
  rw [map_add]
  exact norm_add_le _ _

private theorem schwartzL2Norm_smul (c : ℂ) (f : RealSchwartz) :
    schwartzL2Norm (c • f) = ‖c‖ * schwartzL2Norm f := by
  change ‖SchwartzMap.toLpCLM ℂ ℂ 2 volume (c • f)‖ = ‖c‖ * ‖SchwartzMap.toLpCLM ℂ ℂ 2 volume f‖
  rw [map_smul, norm_smul]

private theorem schwartz_seminorm_le_weighted_L2 (m n : ℕ) (f : RealSchwartz) :
    SchwartzMap.seminorm ℂ m n f ≤
      schwartzL2Norm (schwartzMultiplyXIter m (realSchwartzDerivativeIter n f)) +
        (m : ℝ) * schwartzL2Norm (schwartzMultiplyXIter (m - 1) (realSchwartzDerivativeIter n f)) +
        schwartzL2Norm (schwartzMultiplyXIter m (realSchwartzDerivativeIter (n + 1) f)) := by
  apply SchwartzMap.seminorm_le_bound' _ _ _ _ (by
    exact add_nonneg (add_nonneg (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)))
      (norm_nonneg _))
  intro x
  let g := realSchwartzDerivativeIter n f
  have hpoint : |x| ^ m * ‖iteratedDeriv n f x‖ = ‖schwartzMultiplyXIter m g x‖ := by
    rw [schwartzMultiplyXIter_apply, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      realSchwartzDerivativeIter_apply]
  rw [hpoint]
  refine (schwartz_sup_le_L2_and_derivative (schwartzMultiplyXIter m g) x).trans ?_
  cases m with
  | zero => simp [schwartzMultiplyXIter, g, realSchwartzDerivativeIter]
  | succ m =>
    rw [schwartzDerivative_weight_succ]
    refine (add_le_add le_rfl (schwartzL2Norm_add_le _ _)).trans_eq ?_
    rw [schwartzL2Norm_smul, Complex.norm_natCast, Nat.add_sub_cancel]
    exact (add_assoc _ _ _).symm

/-- The weighted derivative L² seminorms give an explicit estimate on each Schwartz seminorm. -/
theorem schwartz_seminorm_le_derivativeLp (m n : ℕ) (f : 𝓢(ℝ, ℂ)) :
    SchwartzMap.seminorm ℂ m n f ≤
      lpNorm (fun x : ℝ => (x : ℂ) ^ m * iteratedDeriv n f x) 2 volume +
        (m : ℝ) * lpNorm (fun x : ℝ => (x : ℂ) ^ (m - 1) * iteratedDeriv n f x) 2 volume +
        lpNorm (fun x : ℝ => (x : ℂ) ^ m * iteratedDeriv (n + 1) f x) 2 volume := by
  have h (k j : ℕ) :
      schwartzL2Norm (schwartzMultiplyXIter k (realSchwartzDerivativeIter j f)) =
        lpNorm (fun x : ℝ => (x : ℂ) ^ k * iteratedDeriv j f x) 2 volume := by
    let g := schwartzMultiplyXIter k (realSchwartzDerivativeIter j f)
    change schwartzL2Norm g = _
    have hg : ⇑g = fun x : ℝ => (x : ℂ) ^ k * iteratedDeriv j f x :=
      funext fun x => by simp only [g, schwartzMultiplyXIter_apply, realSchwartzDerivativeIter_apply]
    rw [← hg, schwartzL2Norm, SchwartzMap.norm_toLp, toReal_eLpNorm g.continuous.aestronglyMeasurable]
  simpa only [h] using schwartz_seminorm_le_weighted_L2 m n f


private def scaledFourierSeminorm (m n : ℕ) : Seminorm ℂ RealSchwartz :=
  ((‖fourierSlopeConstant‖₊ ^ m)⁻¹ : ℝ≥0) • schwartzFourierL2Seminorms (m, n)

private theorem scaledFourierSeminorm_eq_L2 (m n : ℕ) (f : RealSchwartz) :
    scaledFourierSeminorm m n f =
      schwartzL2Norm (schwartzMultiplyXIter m (realSchwartzDerivativeIter n f)) := by
  rw [scaledFourierSeminorm, smul_apply, NNReal.smul_def, smul_eq_mul,
    NNReal.coe_inv, NNReal.coe_pow, coe_nnnorm, schwartzFourierL2Seminorms_eq]
  rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ (norm_ne_zero_iff.mpr fourierSlopeConstant_ne_zero)),
    one_mul]

private theorem schwartz_fourierL2_dominates (m n : ℕ) :
    SchwartzMap.seminorm ℂ m n ≤
      scaledFourierSeminorm m n + (m : ℝ≥0) • scaledFourierSeminorm (m - 1) n +
        scaledFourierSeminorm m (n + 1) := by
  intro f
  simp only [add_apply, smul_apply, NNReal.smul_def, smul_eq_mul, NNReal.coe_natCast,
    scaledFourierSeminorm_eq_L2]
  exact schwartz_seminorm_le_weighted_L2 m n f

private theorem schwartzFourierL2Seminorms_continuous (p : ℕ × ℕ) :
    Continuous (schwartzFourierL2Seminorms p) := by
  exact continuous_norm.comp
    (((SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure ℝ)).continuous).comp
      (((realSchwartzDerivativeIter p.1).continuous).comp
        (((SchwartzMap.fourierTransformCLM ℂ).continuous).comp
          (realSchwartzDerivativeIter p.2).continuous)))

/-- Proposition D.1.10.2. The mixed Fourier L² seminorms induce the usual
Schwartz topology on the real line. -/
theorem schwartz_withFourierL2Seminorms : WithSeminorms schwartzFourierL2Seminorms := by
  let p := schwartzSeminormFamily ℂ ℝ ℂ
  let q := schwartzFourierL2Seminorms
  let t := q.moduleFilterBasis.topology
  let t₀ : TopologicalSpace RealSchwartz := SchwartzMap.instTopologicalSpace ℝ ℂ
  have hp : WithSeminorms (topology := t₀) p := schwartz_withSeminorms ℂ ℝ ℂ
  have hq : @WithSeminorms ℂ RealSchwartz (ℕ × ℕ) _ _ _ q t := by
    letI : TopologicalSpace RealSchwartz := t
    exact ⟨rfl⟩
  have hgroup : @IsTopologicalAddGroup RealSchwartz t _ := by
    letI : TopologicalSpace RealSchwartz := t
    exact hq.topologicalAddGroup
  have hqeq : @nhds RealSchwartz t 0 = ⨅ i, (𝓝 (0 : ℝ)).comap (q i) := by
    letI : TopologicalSpace RealSchwartz := t
    letI := hgroup
    exact q.withSeminorms_iff_nhds_eq_iInf.mp hq
  have hpeq : @nhds RealSchwartz t₀ 0 = ⨅ i, (𝓝 (0 : ℝ)).comap (p i) :=
    p.withSeminorms_iff_nhds_eq_iInf.mp hp
  have hpcont (i : ℕ × ℕ) : @Continuous RealSchwartz ℝ t _ (p i) := by
    letI : TopologicalSpace RealSchwartz := t
    letI := hgroup
    have hscaled (m n : ℕ) : Continuous (scaledFourierSeminorm m n) :=
      (hq.continuous_seminorm (m, n)).const_smul _
    apply Seminorm.continuous_of_le _ (schwartz_fourierL2_dominates i.1 i.2)
    exact ((hscaled i.1 i.2).add ((hscaled (i.1 - 1) i.2).const_smul (i.1 : ℝ≥0))).add
      (hscaled i.1 (i.2 + 1))
  apply (q.withSeminorms_iff_nhds_eq_iInf).mpr
  apply le_antisymm
  · refine le_iInf fun i => Filter.map_le_iff_le_comap.mp ?_
    show Tendsto (q i) (𝓝 (0 : RealSchwartz)) (𝓝 (0 : ℝ))
    have h := (schwartzFourierL2Seminorms_continuous i).continuousAt (x := (0 : RealSchwartz))
    simpa only [q, map_zero] using h.tendsto
  · change (⨅ i, (𝓝 (0 : ℝ)).comap (q i)) ≤ @nhds RealSchwartz t₀ 0
    rw [← hqeq, hpeq]
    refine le_iInf fun i => Filter.map_le_iff_le_comap.mp ?_
    change Tendsto (p i) (@nhds RealSchwartz t 0) (𝓝 (0 : ℝ))
    have h := (@Continuous.continuousAt RealSchwartz ℝ t _ (p i) 0 (hpcont i))
    have hh : Tendsto (p i) (@nhds RealSchwartz t 0) (𝓝 ((p i) 0)) := h
    rwa [map_zero] at hh

theorem schwartz_isVonNBounded_iff_fourierL2 {S : Set RealSchwartz} :
    Bornology.IsVonNBounded ℂ S ↔ ∀ p, BddAbove (schwartzFourierL2Seminorms p '' S) :=
  schwartz_withFourierL2Seminorms.isVonNBounded_iff_seminorm_bddAbove

end

end Masullo
