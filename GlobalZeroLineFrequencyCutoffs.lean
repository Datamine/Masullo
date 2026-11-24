import GlobalThetaZeroLineDensity
import OrbitalSobolevMomentCovariance

open Filter Function MeasureTheory NumberField Set Topology
open scoped FourierTransform NumberField SchwartzMap

namespace Masullo
noncomputable section

variable (F : Type*) [Field F] [NumberField F]

private abbrev Q := IdeleClass F
private abbrev K := normOneIdeleClass F
private abbrev ray (t : ℝ) := ideleClassExpSection F (Multiplicative.ofAdd t)

local instance zeroLineCutoffMeasurable : MeasurableSpace (Q F) := borel _
local instance zeroLineCutoffBorel : BorelSpace (Q F) := ⟨rfl⟩
local instance zeroLineCutoffT2 : T2Space (Q F) := ideleClasses_hausdorff
local instance zeroLineCutoffLocallyCompact : LocallyCompactSpace (Q F) := ideleClasses_locallyCompact
local instance zeroLineCutoffSecondCountable : SecondCountableTopology (Q F) := ideleClass_secondCountable F

variable (μ : Measure (Q F)) [μ.IsHaarMeasure] (s : ℝ) (hs : 0 ≤ s)

private abbrev T (t : ℝ) := hardySobolevMulTranslation μ (ideleClassLogNorm F)
  (ideleClassLogNorm_continuous F) 0 0 s hs (ray F t)
private abbrev B (t : ℝ) := (1 + |t|) ^ (s / 2)

private theorem B_continuous : Continuous (B s) :=
  (continuous_const.add continuous_abs).rpow_const fun x ↦
    Or.inl (add_pos_of_pos_of_nonneg zero_lt_one (abs_nonneg x)).ne'

private theorem translate_norm_le (t : ℝ) (u : Lp ℂ 2 μ) : ‖T F μ s hs t u‖ ≤ B s t * ‖u‖ := by
  apply ((T F μ s hs t).le_opNorm u).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  have h := hardySobolevMulTranslation_singleton_opNorm_le μ (ideleClassLogNorm F)
    (ideleClassLogNorm_continuous F) 0 s hs (ray F t)
  rw [ideleClassLogNorm_expSection, zero_mul, Real.exp_zero, one_mul] at h
  exact h

private theorem continuous_translate (u : Lp ℂ 2 μ) : Continuous (fun t ↦ T F μ s hs t u) := by
  let N := globalThetaSobolevCompletion F μ 0 0 0 s hs
  let v : N := ⟨u, globalThetaSobolevMap_zeroLine_dense_of_haar F μ s hs u⟩
  exact continuous_subtype_val.comp ((continuous_globalThetaSobolevCompletion_translate F μ 0 0 0 s hs).comp
    (((ideleClassExpSection_continuous F).comp continuous_ofAdd).prodMk (continuous_const (y := v))))

include hs in
private theorem kernel_norm_integrable (φ : 𝓢(ℝ, ℂ)) :
    Integrable (fun t ↦ ‖φ t‖ * B s t) := by
  apply (integrable_radialSobolevTailWeight s hs φ).mono'
    (φ.continuous.norm.mul (B_continuous s)).aestronglyMeasurable
  apply Eventually.of_forall
  intro t
  change ‖‖φ t‖ * B s t‖ ≤ _
  rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (by positivity) _))]
  exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) (norm_nonneg _)

theorem integrable_globalZeroLineRadialKernel (φ : 𝓢(ℝ, ℂ)) (u : Lp ℂ 2 μ) :
    Integrable (fun t ↦ φ t • T F μ s hs t u) := by
  apply integrable_globalZeroLine_translate F μ volume s hs (ray F)
    ((ideleClassExpSection_continuous F).comp continuous_ofAdd)
    φ φ.continuous.aestronglyMeasurable u (globalThetaSobolevMap_zeroLine_dense_of_haar F μ s hs u)
  simp only [ray, ideleClassLogNorm_expSection]
  exact kernel_norm_integrable s hs φ

/-- Convolution by a radial Schwartz kernel in the ambient zero-line Sobolev chart. -/
def globalZeroLineRadialCutoff (φ : 𝓢(ℝ, ℂ)) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  ({ toFun := fun u ↦ ∫ t, φ t • T F μ s hs t u
     map_add' := fun u v ↦ by
       simp_rw [map_add, smul_add]
       exact integral_add (integrable_globalZeroLineRadialKernel F μ s hs φ u)
         (integrable_globalZeroLineRadialKernel F μ s hs φ v)
     map_smul' := fun a u ↦ by
       simp_rw [map_smul, smul_comm (φ _) a, integral_smul, RingHom.id_apply] } : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ).mkContinuous
    (∫ t, ‖φ t‖ * B s t) (fun u ↦ by
      rw [← integral_mul_const]
      apply norm_integral_le_of_norm_le ((kernel_norm_integrable s hs φ).mul_const _)
      apply Eventually.of_forall
      intro t
      rw [norm_smul, mul_assoc]
      exact mul_le_mul_of_nonneg_left (translate_norm_le F μ s hs t u) (norm_nonneg _))

theorem globalZeroLineRadialCutoff_apply (φ : 𝓢(ℝ, ℂ)) (u : Lp ℂ 2 μ) :
    globalZeroLineRadialCutoff F μ s hs φ u = ∫ t, φ t • T F μ s hs t u := rfl

/-- The radial band-limited convolution kernels approximate each vector
in the ambient zero-line Sobolev norm. -/
theorem exists_bandlimited_globalZeroLineRadialCutoff_near
    (u : Lp ℂ 2 μ) {ε : ℝ} (hε : 0 < ε) :
    ∃ φ : 𝓢(ℝ, ℂ), HasCompactSupport (𝓕 φ : 𝓢(ℝ, ℂ)) ∧
      ‖globalZeroLineRadialCutoff F μ s hs φ u - u‖ < ε := by
  have hT₀ : T F μ s hs 0 u = u := by
    unfold T ray
    rw [show Multiplicative.ofAdd (0 : ℝ) = 1 from rfl, map_one, hardySobolevMulTranslation_one]
  have hc := (continuous_translate F μ s hs u).continuousAt (x := 0)
  rw [Metric.continuousAt_iff] at hc
  obtain ⟨δ, hδ, hδT⟩ := hc (ε / 4) (by positivity)
  let τ := min 1 (ε / (4 * (‖u‖ + 1)))
  have hτ : 0 < τ := lt_min one_pos (by positivity)
  obtain ⟨φ, hφ, hmass, hnorm, htail⟩ := exists_bandlimited_radialSobolev_kernel s hs hδ hτ
  refine ⟨φ, hφ, ?_⟩
  let U := Metric.ball (0 : ℝ) δ
  have hU : MeasurableSet U := Metric.isOpen_ball.measurableSet
  let W (t : ℝ) := ‖φ t‖ * radialSobolevTailWeight s t
  let f (t : ℝ) := φ t • (T F μ s hs t u - u)
  have he : globalZeroLineRadialCutoff F μ s hs φ u - u = ∫ t, f t := by
    rw [globalZeroLineRadialCutoff_apply]
    simp only [f, smul_sub]
    rw [integral_sub (integrable_globalZeroLineRadialKernel F μ s hs φ u) (φ.integrable.smul_const u),
      integral_smul_const, hmass, one_smul]
  have hW : Integrable W := integrable_radialSobolevTailWeight s hs φ
  have hmajor : Integrable (fun t ↦ (ε/4) * ‖φ t‖ + Uᶜ.indicator (fun t ↦ ‖u‖ * W t) t) :=
    (φ.integrable.norm.const_mul _).add ((hW.const_mul _).indicator hU.compl)
  rw [he]
  calc
    _ ≤ ∫ t, (ε/4) * ‖φ t‖ + Uᶜ.indicator (fun t ↦ ‖u‖ * W t) t := by
      apply norm_integral_le_of_norm_le hmajor
      apply Eventually.of_forall
      intro t
      by_cases ht : t ∈ U
      · have ht' : ‖T F μ s hs t u - u‖ < ε/4 := by
          simpa only [dist_eq_norm, hT₀] using hδT (Metric.mem_ball.mp ht)
        rw [show f t = φ t • (T F μ s hs t u - u) from rfl, norm_smul, indicator_of_notMem
          (show t ∉ Uᶜ from fun h ↦ h ht), add_zero, mul_comm (ε/4)]
        exact mul_le_mul_of_nonneg_left ht'.le (norm_nonneg _)
      · have hb : ‖T F μ s hs t u - u‖ ≤ (B s t + 1) * ‖u‖ := by
          rw [add_mul, one_mul]
          exact (norm_sub_le _ _).trans (add_le_add_left (translate_norm_le F μ s hs t u) _)
        calc
          ‖f t‖ ≤ ‖u‖ * W t := by
            change ‖φ t • (T F μ s hs t u - u)‖ ≤ _
            rw [norm_smul]
            exact (mul_le_mul_of_nonneg_left hb (norm_nonneg _)).trans_eq (by
              change ‖φ t‖ * ((B s t + 1) * ‖u‖) = ‖u‖ * (‖φ t‖ * (B s t + 1))
              ring)
          _ ≤ _ := by
            rw [indicator_of_mem (show t ∈ Uᶜ from ht)]
            exact le_add_of_nonneg_left (mul_nonneg (by positivity) (norm_nonneg _))
    _ = (ε/4) * (∫ t, ‖φ t‖) + ‖u‖ * (∫ t in Uᶜ, W t) := by
      rw [integral_add (φ.integrable.norm.const_mul _) ((hW.const_mul _).indicator hU.compl),
        integral_const_mul, integral_indicator hU.compl, integral_const_mul]
    _ < ε := by
      have hτ₁ : τ ≤ 1 := min_le_left _ _
      have hτ₂ : τ * (‖u‖ + 1) ≤ ε/4 := by
        apply (le_div_iff₀ (by positivity)).mp
        rw [div_div]
        exact min_le_right _ _
      have hA := mul_le_mul_of_nonneg_left hnorm.le (by positivity : 0 ≤ ε/4)
      have hB := mul_le_mul_of_nonneg_left htail.le (norm_nonneg u)
      change ‖u‖ * (∫ t in Uᶜ, W t) ≤ _ at hB
      nlinarith

/-- Convolution preserves vanishing of each entire initial block of
admissible moments at a given frequency. -/
theorem globalZeroLineRadialCutoff_moment_zero (φ : 𝓢(ℝ, ℂ))
    (χ : PontryaginDual (Q F)) (z : ℂ) (hz : z.re = 0)
    (m : ℕ) (hm : (m : ℝ) < (s - 1) / 2) (u : Lp ℂ 2 μ)
    (hzero : ∀ j ≤ m, (∫ q, u q * orbitalSobolevMoment F χ s z j q ∂μ) = 0) :
    orbitalSobolevMomentCLM F μ s hs χ z hz m hm (globalZeroLineRadialCutoff F μ s hs φ u) = 0 := by
  let A := orbitalSobolevMomentCLM F μ s hs χ z hz m hm
  change A (globalZeroLineRadialCutoff F μ s hs φ u) = 0
  rw [globalZeroLineRadialCutoff_apply, ← A.integral_comp_comm (integrable_globalZeroLineRadialKernel F μ s hs φ u)]
  calc
    _ = ∫ _ : ℝ, (0 : ℂ) := by
      apply integral_congr_ae
      apply Eventually.of_forall
      intro t
      change A (φ t • T F μ s hs t u) = 0
      rw [map_smul, orbitalSobolevMomentCLM_translate F μ s hs χ z hz m hm (ray F t) u]
      have he : (∑ j ∈ Finset.range (m + 1), (m.choose j : ℂ) *
          ((ideleClassLogNorm F (ray F t)).toAdd : ℂ) ^ (m-j) *
            ∫ q, u q * orbitalSobolevMoment F χ s z j q ∂μ) = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        rw [hzero j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)), mul_zero]
      rw [he, mul_zero, smul_zero]
    _ = 0 := by simp

local instance zeroLineCutoffNormOneMeasurable : MeasurableSpace (K F) := borel _
local instance zeroLineCutoffNormOneBorel : BorelSpace (K F) := ⟨rfl⟩

variable (ν : Measure (K F)) [ν.IsHaarMeasure]

local instance zeroLineCutoffClassHaar : (globalClassMeasure F ν).IsHaarMeasure :=
  globalClassMeasure_isHaar F ν

/-- On separated Schwartz vectors the actual Sobolev cutoff is ordinary
radial Schwartz convolution. -/
theorem globalZeroLineRadialCutoff_on_Schwartz (φ : 𝓢(ℝ, ℂ))
    (χ : PontryaginDual (K F)) (p : 𝓢(ℝ, ℂ)) :
    globalZeroLineRadialCutoff F (globalClassMeasure F ν) s hs φ
      (globalZeroLineSchwartzIsotype F ν s χ p) =
    globalZeroLineSchwartzIsotype F ν s χ (SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) p φ) :=
  globalZeroLineSchwartzIsotype_convolution F ν s hs χ p φ
    (integrable_globalZeroLineRadialKernel F (globalClassMeasure F ν) s hs φ
      (globalZeroLineSchwartzIsotype F ν s χ p))

end
end Masullo
