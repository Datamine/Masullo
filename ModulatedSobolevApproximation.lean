import ModulatedFrequencySobolev
import ModulatedSobolevConvolution
import SobolevRadialApproximation

open Filter Function MeasureTheory Set Topology
open scoped ENNReal

namespace Masullo

noncomputable section

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
  (m : G →ₜ* Multiplicative ℝ)

/-- The full zero-line Sobolev space has a strong approximate identity
given by uniformly bounded, compact-spectrum convolution kernels. -/
theorem exists_zeroLineSobolev_approximation (hm : IsProperMap m) (hms : Surjective m)
    (s : ℝ) (hs : 0 ≤ s) :
    ∃ φ : ℕ → G → ℂ, (∀ n, Continuous (φ n)) ∧
      (∀ n, φ n ∈ bruhatSchwartzSubmodule (G := G)) ∧
      (∀ n, HasCompactSupport (lcaFourier μ (φ n))) ∧ (∀ n, (∫ g, φ n g ∂μ) = 1) ∧
      ∃ (hi : ∀ n, Integrable (φ n) μ)
        (hw : ∀ n, Integrable (fun g => ‖φ n g‖ * singletonSobolevKernelWeight 0 s (m g).toAdd) μ),
      let A n := singletonSobolevConvolution μ m 0 s hs (hi n).aestronglyMeasurable (hw n)
      (∀ n, ‖A n‖ ≤ 2) ∧ ∀ u, Tendsto (fun n => A n u) atTop (𝓝 u) := by
  classical
  obtain ⟨U, hU, hbase⟩ := (nhds_basis_opens (1 : G)).exists_antitone_subbasis
  let ε (n : ℕ) : ℝ := 1 / ((n : ℝ) + 2)
  have hε (n : ℕ) : 0 < ε n := one_div_pos.mpr (by positivity)
  have hεle (n : ℕ) : ε n ≤ 1 / 2 := by
    exact one_div_le_one_div_of_le (by norm_num) (le_add_of_nonneg_left (Nat.cast_nonneg n))
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 1)
    convert h using 1
    funext n
    rw [Function.comp_apply]
    push_cast
    ring
  let w (g : G) := radialSobolevTailWeight s (modulatedLog m g)
  let B (g : G) := singletonSobolevKernelWeight 0 s (m g).toAdd
  have hwB (g : G) : w g = B g + 1 := by
    simp [w, B, radialSobolevTailWeight, singletonSobolevKernelWeight, modulatedLog]
  have hB0 (g : G) : 0 ≤ B g := by dsimp [B, singletonSobolevKernelWeight]; positivity
  have hw0 (g : G) : 0 ≤ w g := by rw [hwB]; exact add_nonneg (hB0 _) zero_le_one
  choose φ hc hB hi hwF hF hmass hn ht using fun n =>
    exists_haarSobolev_approximate_kernel m μ hm hms s hs (hU n).2 (hU n).1 (hε n)
  have hw (n : ℕ) : Integrable (fun g => ‖φ n g‖ * B g) μ := by
    have h := (hwF n).sub (hi n).norm
    convert h using 1
    funext g
    change ‖φ n g‖ * B g = ‖φ n g‖ * w g - ‖φ n g‖
    rw [hwB]
    ring
  have hbound (n : ℕ) : (∫ g, ‖φ n g‖ ∂μ) ≤ 3 / 2 := (hn n).le.trans (by linarith [hεle n])
  have htail (V : Set G) (hVo : IsOpen V) (hV1 : (1 : G) ∈ V) :
      Tendsto (fun n => ∫ g in Vᶜ, ‖φ n g‖ * w g ∂μ) atTop (𝓝 0) := by
    obtain ⟨N, -, hNV⟩ := hbase.1.mem_iff.mp (hVo.mem_nhds hV1)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hεlim
      (.of_forall fun n => integral_nonneg (fun g => mul_nonneg (norm_nonneg _) (hw0 g))) ?_
    filter_upwards [eventually_ge_atTop N] with n hnN
    have hUV : U n ⊆ V := (hbase.2 hnN).trans hNV
    exact (setIntegral_mono_set (hwF n).integrableOn
      (.of_forall fun g => mul_nonneg (norm_nonneg _) (hw0 g)) (compl_subset_compl.mpr hUV).eventuallyLE).trans (ht n).le
  have htailB (V : Set G) (hVo : IsOpen V) (hV1 : (1 : G) ∈ V) :
      Tendsto (fun n => ∫ g in Vᶜ, ‖φ n g‖ * B g ∂μ) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (htail V hVo hV1)
      (.of_forall fun n => integral_nonneg (fun g => mul_nonneg (norm_nonneg _) (hB0 g))) ?_
    exact .of_forall fun n => integral_mono (hw n).restrict (hwF n).restrict
      (fun g => mul_le_mul_of_nonneg_left (by rw [hwB]; linarith) (norm_nonneg _))
  have ht' (V : Set G) (hVo : IsOpen V) (hV1 : (1 : G) ∈ V) :
      Tendsto (fun n => ∫ g in Vᶜ, ‖φ n g‖ * (B g + 1) ∂μ) atTop (𝓝 0) := by
    simpa only [← hwB] using htail V hVo hV1
  let A n := singletonSobolevConvolution μ m 0 s hs (hi n).aestronglyMeasurable (hw n)
  have hA := tendsto_singletonSobolevConvolution μ m 0 s hs atTop φ hi hw hmass
    (by norm_num : (0 : ℝ) ≤ 3 / 2) hbound ht'
  have hpoint := PointwiseConvergenceCLM.tendsto_iff_forall_tendsto.mp hA
  have hnorm := eventually_singletonSobolevConvolution_opNorm_le μ m 0 s hs atTop φ hi hw
    (by norm_num : (0 : ℝ) ≤ 3 / 2) hbound htailB (by norm_num : (0 : ℝ) < 1 / 2)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hnorm
  refine ⟨fun n => φ (n + N), fun n => hc _, fun n => hB _, fun n => hF _, fun n => hmass _,
    fun n => hi _, fun n => hw _, ?_, ?_⟩
  · intro n
    have h := hN (n + N) (by omega)
    norm_num at h
    exact h
  · intro u
    exact (hpoint u).comp (tendsto_add_atTop_nat N)

/-- A sequence of actual convolution operators on every singleton strip
has norm at most two and converges strongly to the identity. After the
abscissa twist its kernels have compact Fourier spectrum. -/
theorem exists_singletonSobolev_approximation (hm : IsProperMap m) (hms : Surjective m)
    (b s : ℝ) (hs : 0 ≤ s) :
    ∃ (φ : ℕ → G → ℂ) (hc : ∀ n, Continuous (φ n)),
      (∀ n, (fun g => Real.exp (b * (m g).toAdd) • φ n g) ∈ bruhatSchwartzSubmodule (G := G)) ∧
      (∀ n, HasCompactSupport (lcaFourier μ (fun g => Real.exp (b * (m g).toAdd) • φ n g))) ∧
      (∀ n, (∫ g, Real.exp (b * (m g).toAdd) • φ n g ∂μ) = 1) ∧
      ∃ (hw : ∀ n, Integrable (fun g => ‖φ n g‖ * singletonSobolevKernelWeight b s (m g).toAdd) μ),
      let A n := singletonSobolevConvolution μ m b s hs (hc n).aestronglyMeasurable (hw n)
      (∀ n, ‖A n‖ ≤ 2) ∧ ∀ u, Tendsto (fun n => A n u) atTop (𝓝 u) := by
  obtain ⟨ψ, hψc, hψB, hψF, hψm, hψI, hψW, hnorm, ht⟩ := exists_zeroLineSobolev_approximation μ m hm hms s hs
  let e (g : G) := Real.exp (b * (m g).toAdd)
  have hpos (g : G) : 0 < e g := Real.exp_pos _
  have hec : Continuous e := Real.continuous_exp.comp
    (continuous_const.mul (continuous_toAdd.comp m.continuous))
  let φ (n : ℕ) (g : G) := (e g)⁻¹ • ψ n g
  have hc (n : ℕ) : Continuous (φ n) := (hec.inv₀ fun g => (hpos g).ne').smul (hψc n)
  have htΦ (n : ℕ) (g : G) : e g • φ n g = ψ n g := by
    change e g • ((e g)⁻¹ • ψ n g) = _
    rw [smul_smul, mul_inv_cancel₀ (hpos g).ne', one_smul]
  have hw (n : ℕ) : Integrable (fun g => ‖φ n g‖ * singletonSobolevKernelWeight b s (m g).toAdd) μ := by
    apply (hψW n).congr
    refine .of_forall fun g => ?_
    change ‖ψ n g‖ * singletonSobolevKernelWeight 0 s (m g).toAdd =
      ‖(e g)⁻¹ • ψ n g‖ * singletonSobolevKernelWeight b s (m g).toAdd
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (hpos g).le)]
    simp only [singletonSobolevKernelWeight, zero_mul, Real.exp_zero, one_mul]
    change ‖ψ n g‖ * _ = (e g)⁻¹ * ‖ψ n g‖ * (e g * _)
    field_simp [(hpos g).ne']
  have hA (n : ℕ) : singletonSobolevConvolution μ m b s hs (hc n).aestronglyMeasurable (hw n) =
      singletonSobolevConvolution μ m 0 s hs (hψI n).aestronglyMeasurable (hψW n) := by
    ext u : 1
    rw [singletonSobolevConvolution_apply, singletonSobolevConvolution_apply]
    apply integral_congr_ae
    refine .of_forall fun g => ?_
    let v := hardySobolevMulTranslation μ m.toMonoidHom m.continuous 0 0 s hs g u
    change φ n g • (hardySobolevMulTranslation μ m.toMonoidHom m.continuous b b s hs g u) = ψ n g • v
    rw [hardySobolevMulTranslation_singleton_eq_zeroLine]
    change φ n g • (e g • v) = ψ n g • v
    calc
      φ n g • (e g • v) = e g • (φ n g • v) := smul_comm _ _ _
      _ = (e g • φ n g) • v := (smul_assoc _ _ _).symm
      _ = ψ n g • v := congrArg (fun z : ℂ => z • v) (htΦ n g)
  refine ⟨φ, hc, ?_, ?_, ?_, hw, ?_, ?_⟩
  · intro n
    simp_rw [show ∀ g, Real.exp (b * (m g).toAdd) • φ n g = ψ n g from htΦ n]
    exact hψB n
  · intro n
    simp_rw [show ∀ g, Real.exp (b * (m g).toAdd) • φ n g = ψ n g from htΦ n]
    exact hψF n
  · intro n
    simp_rw [show ∀ g, Real.exp (b * (m g).toAdd) • φ n g = ψ n g from htΦ n]
    exact hψm n
  · intro n
    simpa only [hA n] using hnorm n
  · intro u
    simpa only [hA] using ht u

end

end Masullo
