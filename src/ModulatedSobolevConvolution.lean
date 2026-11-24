import HardySobolevTranslations
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

open Filter MeasureTheory Set Topology
open scoped ENNReal

namespace Masullo

noncomputable section

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [R1Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsMulLeftInvariant] [μ.InnerRegularCompactLTTop] [IsLocallyFiniteMeasure μ]
  (m : G →ₜ* Multiplicative ℝ) (b s : ℝ) (hs : 0 ≤ s)

/-- Weight for the convolution kernel on a singleton strip, expressed in
the logarithmic norm coordinate. -/
def singletonSobolevKernelWeight (b s t : ℝ) : ℝ :=
  Real.exp (b * t) * (1 + |t|) ^ (s / 2)

local notation "T" => hardySobolevMulTranslation μ m.toMonoidHom m.continuous b b s hs
local notation "B" => (fun x : G => singletonSobolevKernelWeight b s (Multiplicative.toAdd (m x)))

private theorem continuous_singletonSobolev_eval (u : Lp ℂ 2 μ) :
    Continuous (fun g : G => T g u) := by
  let F (p : G × Lp ℂ 2 μ) := T p.1 p.2
  have hF : Continuous F :=
    continuous_hardySobolevMulTranslation μ m.toMonoidHom m.continuous b b s hs
  have hu : Continuous (fun g : G => (g, u)) := continuous_id.prodMk continuous_const
  change Continuous (F ∘ fun g : G => (g, u))
  exact hF.comp hu

private theorem singletonSobolev_eval_norm_le (g : G) (u : Lp ℂ 2 μ) :
    ‖T g u‖ ≤ B g * ‖u‖ :=
  (T g).le_opNorm u |>.trans (mul_le_mul_of_nonneg_right
    (hardySobolevMulTranslation_singleton_opNorm_le μ m.toMonoidHom m.continuous b s hs g)
    (norm_nonneg _))

private theorem singletonSobolev_kernel_norm_le (φ : G → ℂ) (g : G) (u : Lp ℂ 2 μ) :
    ‖φ g • T g u‖ ≤ ‖φ g‖ * B g * ‖u‖ := by
  rw [norm_smul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (singletonSobolev_eval_norm_le μ m b s hs g u) (norm_nonneg _)

theorem integrable_singletonSobolev_kernel_eval {φ : G → ℂ}
    (hφ : AEStronglyMeasurable φ μ) (hw : Integrable (fun g => ‖φ g‖ * B g) μ)
    (u : Lp ℂ 2 μ) : Integrable (fun g => φ g • T g u) μ := by
  exact (hw.mul_const ‖u‖).mono'
    (hφ.smul (continuous_singletonSobolev_eval μ m b s hs u).aestronglyMeasurable)
    (.of_forall fun g => singletonSobolev_kernel_norm_le μ m b s hs φ g u)

private theorem norm_integral_singletonSobolev_kernel_eval {φ : G → ℂ}
    (hw : Integrable (fun g => ‖φ g‖ * B g) μ) (u : Lp ℂ 2 μ) :
    ‖∫ g, φ g • T g u ∂μ‖ ≤ (∫ g, ‖φ g‖ * B g ∂μ) * ‖u‖ := by
  rw [← integral_mul_const]
  exact norm_integral_le_of_norm_le (hw.mul_const ‖u‖)
    (.of_forall fun g => singletonSobolev_kernel_norm_le μ m b s hs φ g u)

/-- Bochner integration of the actual weighted translations in the
positive-amplitude chart. This is the operator in (9.3.2.2). -/
def singletonSobolevConvolution {φ : G → ℂ}
    (hφ : AEStronglyMeasurable φ μ) (hw : Integrable (fun g => ‖φ g‖ * B g) μ) :
    Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  let hI := integrable_singletonSobolev_kernel_eval μ m b s hs hφ hw
  ({ toFun := fun u => ∫ g, φ g • T g u ∂μ
     map_add' := fun u v => by
       simp_rw [map_add, smul_add]
       exact integral_add (hI u) (hI v)
     map_smul' := fun c u => by
       simp_rw [map_smul, smul_comm (φ _) c, integral_smul, RingHom.id_apply] } : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ).mkContinuous
    (∫ g, ‖φ g‖ * B g ∂μ) (norm_integral_singletonSobolev_kernel_eval μ m b s hs hw)

theorem singletonSobolevConvolution_apply {φ : G → ℂ}
    (hφ : AEStronglyMeasurable φ μ) (hw : Integrable (fun g => ‖φ g‖ * B g) μ)
    (u : Lp ℂ 2 μ) :
    singletonSobolevConvolution μ m b s hs hφ hw u = ∫ g, φ g • T g u ∂μ := rfl

theorem singletonSobolevConvolution_opNorm_le {φ : G → ℂ}
    (hφ : AEStronglyMeasurable φ μ) (hw : Integrable (fun g => ‖φ g‖ * B g) μ) :
    ‖singletonSobolevConvolution μ m b s hs hφ hw‖ ≤ ∫ g, ‖φ g‖ * B g ∂μ := by
  apply ContinuousLinearMap.opNorm_le_bound
  · exact integral_nonneg (fun g => mul_nonneg (norm_nonneg _) (mul_nonneg (Real.exp_pos _).le
      (Real.rpow_nonneg (by positivity) _)))
  · exact norm_integral_singletonSobolev_kernel_eval μ m b s hs hw

/-- Concentrated kernels of bounded mass have convolution norms eventually
below every constant strictly larger than that mass. -/
theorem eventually_singletonSobolevConvolution_opNorm_le {ι : Type*} (l : Filter ι)
    (φ : ι → G → ℂ) (hφ : ∀ i, Integrable (φ i) μ)
    (hw : ∀ i, Integrable (fun g => ‖φ i g‖ * B g) μ) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ i, ∫ g, ‖φ i g‖ ∂μ ≤ C)
    (htail : ∀ U : Set G, IsOpen U → (1 : G) ∈ U →
      Tendsto (fun i => ∫ g in Uᶜ, ‖φ i g‖ * B g ∂μ) l (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ i in l, ‖singletonSobolevConvolution μ m b s hs
      (hφ i).aestronglyMeasurable (hw i)‖ ≤ C + ε := by
  let δ := ε / (2 * (C + 1))
  have hδ : 0 < δ := div_pos hε (by positivity)
  let U := {g : G | B g < 1 + δ}
  have hl : Continuous (fun g : G => (m g).toAdd) := continuous_toAdd.comp m.continuous
  have hbase : Continuous (fun g : G => (1 : ℝ) + |(m g).toAdd|) := continuous_const.add hl.abs
  have hpow : Continuous (fun g : G => (1 + |(m g).toAdd|) ^ (s / 2)) :=
    hbase.rpow_const (fun g => Or.inl (show 1 + |(m g).toAdd| ≠ 0 by positivity))
  have hB : Continuous B := (Real.continuous_exp.comp (continuous_const.mul hl)).mul hpow
  have hU : IsOpen U := isOpen_lt hB continuous_const
  have h1 : (1 : G) ∈ U := by
    change singletonSobolevKernelWeight b s (m 1).toAdd < 1 + δ
    rw [map_one]
    simpa [singletonSobolevKernelWeight] using hδ
  have ht := htail U hU h1
  rw [Metric.tendsto_nhds] at ht
  filter_upwards [ht (ε / 2) (by positivity)] with i hi
  have hI : (∫ g in U, ‖φ i g‖ * B g ∂μ) ≤ (1 + δ) * (∫ g, ‖φ i g‖ ∂μ) := by
    rw [← integral_const_mul]
    apply le_trans (integral_mono_ae (hw i).restrict ((hφ i).norm.const_mul _).restrict ?_)
    · exact setIntegral_le_integral ((hφ i).norm.const_mul _) (.of_forall fun _ => by positivity)
    · filter_upwards [ae_restrict_mem hU.measurableSet] with g hg
      exact (mul_le_mul_of_nonneg_left (le_of_lt hg) (norm_nonneg _)).trans_eq (mul_comm _ _)
  have hJ : (∫ g in Uᶜ, ‖φ i g‖ * B g ∂μ) < ε / 2 :=
    (le_abs_self _).trans_lt (by simpa [Real.dist_eq] using hi)
  have hδC : δ * C ≤ ε / 2 := by
    calc
      δ * C ≤ δ * (C + 1) := mul_le_mul_of_nonneg_left (by linarith) hδ.le
      _ = ε / 2 := by dsimp [δ]; field_simp
  have hmul := mul_le_mul_of_nonneg_left (hbound i) (show 0 ≤ 1 + δ by positivity)
  apply (singletonSobolevConvolution_opNorm_le μ m b s hs _ _).trans
  rw [← integral_add_compl hU.measurableSet (hw i)]
  nlinarith

set_option maxHeartbeats 800000 in
/-- A normalized family whose weighted L¹ tails vanish is a strong
approximate identity on the full singleton-strip Sobolev space. -/
theorem tendsto_singletonSobolevConvolution {ι : Type*} (l : Filter ι)
    (φ : ι → G → ℂ) (hφ : ∀ i, Integrable (φ i) μ)
    (hw : ∀ i, Integrable (fun g => ‖φ i g‖ * B g) μ)
    (hmass : ∀ i, ∫ g, φ i g ∂μ = 1) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ i, ∫ g, ‖φ i g‖ ∂μ ≤ C)
    (htail : ∀ U : Set G, IsOpen U → (1 : G) ∈ U →
      Tendsto (fun i => ∫ g in Uᶜ, ‖φ i g‖ * (B g + 1) ∂μ) l (𝓝 0)) :
    let A (i : ι) : Lp ℂ 2 μ →Lₚₜ[ℂ] Lp ℂ 2 μ :=
      singletonSobolevConvolution μ m b s hs (hφ i).aestronglyMeasurable (hw i)
    let I : Lp ℂ 2 μ →Lₚₜ[ℂ] Lp ℂ 2 μ := ContinuousLinearMap.id ℂ _
    Tendsto A l (𝓝 I) := by
  intro A I
  apply PointwiseConvergenceCLM.tendsto_iff_forall_tendsto.mpr
  intro u
  change Tendsto (fun i => singletonSobolevConvolution μ m b s hs
    (hφ i).aestronglyMeasurable (hw i) u) l (𝓝 u)
  rw [Metric.tendsto_nhds]
  intro ε hε
  let δ := ε / (2 * (C + 1))
  have hδ : 0 < δ := div_pos hε (by positivity)
  let U := {g : G | ‖T g u - u‖ < δ}
  have hc := continuous_singletonSobolev_eval μ m b s hs u
  have hU : IsOpen U := isOpen_lt ((hc.sub continuous_const).norm) continuous_const
  have h1 : (1 : G) ∈ U := by
    change ‖T 1 u - u‖ < δ
    rw [hardySobolevMulTranslation_one, sub_self, norm_zero]
    exact hδ
  have ht := (htail U hU h1).const_mul ‖u‖
  rw [mul_zero, Metric.tendsto_nhds] at ht
  filter_upwards [ht (ε / 2) (by positivity)] with i hi
  have hI := integrable_singletonSobolev_kernel_eval μ m b s hs
    (hφ i).aestronglyMeasurable (hw i) u
  have hconst := (hφ i).smul_const u
  let η (g : G) := ‖φ i g‖ * (B g + 1)
  have hη : Integrable η μ := by
    simpa only [η, mul_add, mul_one, Pi.add_def] using (hw i).add (hφ i).norm
  have hmajor : Integrable (fun g => δ * ‖φ i g‖ + Uᶜ.indicator (fun g => ‖u‖ * η g) g) μ :=
    ((hφ i).norm.const_mul δ).add ((hη.const_mul ‖u‖).indicator hU.measurableSet.compl)
  rw [dist_eq_norm, singletonSobolevConvolution_apply]
  have hsub : (∫ g, φ i g • T g u ∂μ) - u = ∫ g, φ i g • (T g u - u) ∂μ := by
    simp_rw [smul_sub]
    rw [integral_sub hI hconst, integral_smul_const, hmass, one_smul]
  rw [hsub]
  calc
    _ ≤ ∫ g, δ * ‖φ i g‖ + Uᶜ.indicator (fun g => ‖u‖ * η g) g ∂μ := by
      apply norm_integral_le_of_norm_le hmajor
      refine .of_forall fun g => ?_
      by_cases hg : g ∈ U
      · have hgu : ‖T g u - u‖ ≤ δ := le_of_lt hg
        rw [norm_smul, indicator_of_notMem (show g ∉ Uᶜ from fun hn => hn hg), add_zero, mul_comm δ]
        exact mul_le_mul_of_nonneg_left hgu (norm_nonneg _)
      · rw [norm_smul, indicator_of_mem hg]
        have hb := singletonSobolev_eval_norm_le μ m b s hs g u
        have hdiff : ‖T g u - u‖ ≤ (B g + 1) * ‖u‖ := by
          rw [add_mul, one_mul]
          exact (norm_sub_le _ _).trans (add_le_add_left hb _)
        have he := mul_le_mul_of_nonneg_left hdiff (norm_nonneg (φ i g))
        have hη' : ‖φ i g‖ * ((B g + 1) * ‖u‖) = ‖u‖ * η g := by dsimp [η]; ring
        rw [hη'] at he
        exact he.trans (le_add_of_nonneg_left (mul_nonneg hδ.le (norm_nonneg _)))
    _ = δ * (∫ g, ‖φ i g‖ ∂μ) + ‖u‖ * (∫ g in Uᶜ, η g ∂μ) := by
      rw [integral_add ((hφ i).norm.const_mul δ)
        ((hη.const_mul ‖u‖).indicator hU.measurableSet.compl), integral_const_mul,
        integral_indicator hU.measurableSet.compl, integral_const_mul]
    _ < ε := by
      have hA := mul_le_mul_of_nonneg_left (hbound i) hδ.le
      have hB : δ * C ≤ ε / 2 := by
        calc
          δ * C ≤ δ * (C + 1) := mul_le_mul_of_nonneg_left (by linarith) hδ.le
          _ = ε / 2 := by dsimp [δ]; field_simp
      have htail' : ‖u‖ * (∫ g in Uᶜ, η g ∂μ) < ε / 2 :=
        (le_abs_self _).trans_lt (by simpa [Real.dist_eq, η] using hi)
      linarith

end

end Masullo
