import HilbertSchmidtFactorization
import LCAFourierInversion

open Filter Function MeasureTheory Set Topology
open scoped ENNReal Pointwise

namespace Masullo

noncomputable section

private theorem spectralKernel_memLp {X D : Type*} [MeasurableSpace X] [MeasurableSpace D]
    {μ : Measure X} {η : Measure D} [SFinite η] {u : X → ℂ} {v : D → ℂ}
    (hu : MemLp u 2 μ) (hv : MemLp v 2 η)
    {χ : X × D → ℂ} (hχ : Measurable χ) (hb : ∀ p, ‖χ p‖ ≤ 1) :
    MemLp (fun p : X × D => u p.1 * χ p * v p.2) 2 (μ.prod η) := by
  have hmajor := (memLp_rankOneKernel hu hv.star).1
  apply hmajor.of_le
    ((hu.aestronglyMeasurable.comp_fst.mul hχ.aestronglyMeasurable).mul
      hv.aestronglyMeasurable.comp_snd)
  refine .of_forall fun p => ?_
  simp only [Pi.mul_apply, norm_mul, Pi.star_apply, norm_star]
  exact mul_le_mul_of_nonneg_right
    ((mul_le_mul_of_nonneg_left (hb p) (norm_nonneg (u p.1))).trans_eq (mul_one _)) (norm_nonneg (v p.2))

theorem exists_L2_spectral_factors {D : Type*} [MeasurableSpace D]
    {η : Measure D} {g : D → ℂ} (hg : Integrable g η) :
    ∃ q r : D → ℂ, MemLp q 2 η ∧ MemLp r 2 η ∧ ∀ x, q x * star (r x) = g x := by
  let r (x : D) : ℂ := (Real.sqrt ‖g x‖ : ℂ)
  let q (x : D) : ℂ := g x / r x
  have hr : AEStronglyMeasurable r η :=
    (Complex.continuous_ofReal.comp Real.continuous_sqrt).comp_aestronglyMeasurable hg.aestronglyMeasurable.norm
  have hreal (x : D) : ‖r x‖ = Real.sqrt ‖g x‖ := by
    exact (Complex.norm_real (Real.sqrt ‖g x‖)).trans (abs_of_nonneg (Real.sqrt_nonneg _))
  have hs (x : D) : ‖r x‖ ^ 2 = ‖g x‖ := by
    rw [hreal, Real.sq_sqrt (norm_nonneg _)]
  have hq (x : D) : ‖q x‖ ^ 2 = ‖g x‖ := by
    rw [show ‖q x‖ = ‖g x‖ / ‖r x‖ from norm_div _ _, div_pow, hs]
    by_cases hx : ‖g x‖ = 0
    · simp [hx]
    · exact (div_eq_iff hx).mpr (pow_two _)
  refine ⟨q, r, (memLp_two_iff_integrable_sq_norm (hg.aemeasurable.div hr.aemeasurable).aestronglyMeasurable).mpr
    (hg.norm.congr (.of_forall fun x => (hq x).symm)),
    (memLp_two_iff_integrable_sq_norm hr).mpr (hg.norm.congr (.of_forall fun x => (hs x).symm)), ?_⟩
  intro x
  have hstar : star (r x) = r x := Complex.conj_ofReal _
  rw [hstar]
  by_cases hx : g x = 0
  · simp [q, hx]
  · exact div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 (norm_pos_iff.mpr hx)).ne')

section Group

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]

/-- A compactly supported symbol with a square-factor spectral representation
has a trace-class weighted cutoff. Input localization uses the support of the
symbol and cutoff and does not modify the resulting operator. -/
theorem cutoffConvolution_traceClass_of_spectral_factors
    {D : Type*} [MeasurableSpace D] (η : Measure D) [SFinite η] [MeasureTheory.IsSeparable η]
    {w : G → ℝ} (hw : Continuous w) (hpos : ∀ x, 0 < w x)
    {ρ φ : G → ℂ} (hρ : Continuous ρ) (hρc : HasCompactSupport ρ)
    (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (χ : G × D → ℂ) (hχ : Measurable χ) (hb : ∀ p, ‖χ p‖ ≤ 1)
    (q r : D → ℂ) (hq : MemLp q 2 η) (hr : MemLp r 2 η)
    (hRep : ∀ x ∈ tsupport ρ, ∀ y ∈ (tsupport φ)⁻¹ * tsupport ρ,
      φ (x * y⁻¹) = ∫ ξ, χ (x, ξ) * star (χ (y, ξ)) * (q ξ * star (r ξ)) ∂η) :
    let μw := μ.withDensity (fun x => ENNReal.ofReal (w x))
    letI : IsLocallyFiniteMeasure μw := IsLocallyFiniteMeasure.withDensity_ofReal hw
    let k := cutoffConvolutionKernel w ρ φ
    ∃ (hk : MemLp k 2 (μw.prod μw)) (T : TraceClass (Lp ℂ 2 μw)),
      T.toOperator = kernelIntegralOperator (hk.toLp k) ∧
      T.traceValue = (∫ x, ρ x ∂μ) * φ 1 := by
  intro μw k
  letI : IsLocallyFiniteMeasure μw := IsLocallyFiniteMeasure.withDensity_ofReal hw
  let L := (tsupport φ)⁻¹ * tsupport ρ
  have hL : IsCompact L := hφc.inv.mul hρc
  let d : G → ℂ := L.indicator (fun y => (w y : ℂ)⁻¹)
  have hd : MemLp d 2 μw := by
    apply (memLp_indicator_iff_restrict hL.measurableSet).mpr
    letI : IsFiniteMeasure (μw.restrict L) := ⟨by
      rw [Measure.restrict_apply_univ]
      exact hL.measure_lt_top⟩
    have h : Continuous (fun y => (w y : ℂ)⁻¹) :=
      (Complex.continuous_ofReal.comp hw).inv₀ fun y => Complex.ofReal_ne_zero.mpr (hpos y).ne'
    obtain ⟨C, hC⟩ := hL.exists_bound_of_continuousOn h.continuousOn
    exact MemLp.of_bound h.aestronglyMeasurable C ((ae_restrict_mem hL.measurableSet).mono hC)
  have hρ₂ : MemLp ρ 2 μw := hρ.memLp_of_hasCompactSupport hρc
  let a (p : G × D) := ρ p.1 * χ p * q p.2
  let b' (p : G × D) := d p.1 * star (χ p) * star (r p.2)
  let b (p : D × G) := b' p.swap
  have ha : MemLp a 2 (μw.prod η) := spectralKernel_memLp hρ₂ hq hχ hb
  have hb' : MemLp b' 2 (μw.prod η) :=
    spectralKernel_memLp hd hr.star (continuous_star.measurable.comp hχ) (fun p => by simpa only [norm_star] using hb p)
  have hB : MemLp b 2 (η.prod μw) := hb'.comp_measurePreserving Measure.measurePreserving_swap
  have hk : MemLp k 2 (μw.prod μw) := cutoffConvolutionKernel_memLp μ hw hpos hρ hφ hρc hφc
  have hcomp (p : G × G) : k p = ∫ ξ, a (p.1, ξ) * b (ξ, p.2) ∂η := by
    by_cases hx : ρ p.1 = 0
    · simp [k, cutoffConvolutionKernel, a, hx]
    by_cases hy : p.2 ∈ L
    · have he : (∫ ξ, a (p.1, ξ) * b (ξ, p.2) ∂η) = ρ p.1 * d p.2 * φ (p.1 * p.2⁻¹) := by
        rw [hRep p.1 (subset_closure hx) p.2 hy, ← integral_const_mul]
        apply integral_congr_ae
        refine .of_forall fun ξ => ?_
        dsimp [a, b, b']
        ring
      rw [he, show d p.2 = (w p.2 : ℂ)⁻¹ from indicator_of_mem hy _, show k p =
        ρ p.1 * φ (p.1 * p.2⁻¹) / (w p.2 : ℂ) from rfl, div_eq_mul_inv]
      ring
    · have hd0 : d p.2 = 0 := indicator_of_notMem hy _
      have hz : φ (p.1 * p.2⁻¹) = 0 := by
        by_contra hn
        have hS : p.1 * p.2⁻¹ ∈ tsupport φ := subset_closure (show p.1 * p.2⁻¹ ∈ support φ from hn)
        exact hy ⟨(p.1 * p.2⁻¹)⁻¹, by simpa only [Set.mem_inv, inv_inv] using hS,
          p.1, subset_closure hx, by simp [mul_inv_rev, mul_assoc]⟩
      simp [k, cutoffConvolutionKernel, b, b', hd0, hz]
  obtain ⟨S, hS⟩ := exists_kernelComposite_rankOneSeries hk ha hB (.of_forall hcomp)
  refine ⟨hk, TraceClass.ofSeries S, hS, ?_⟩
  rw [TraceClass.traceValue_ofSeries]
  exact cutoffConvolutionKernel_trace_of_series μ hw hpos hρ hρc hφ.continuousAt S hk hS.symm

set_option linter.overlappingInstances false in
/-- Integrability of the Plancherel transform is sufficient for nuclearity
of the actual weighted cutoff convolution and for its diagonal trace. -/
theorem cutoffConvolution_traceClass_of_fourier_integrable [μ.Regular]
    [MeasurableSpace (PontryaginDual G)] [BorelSpace (PontryaginDual G)]
    (η : Measure (PontryaginDual G)) [SFinite η] [MeasureTheory.IsSeparable η]
    (hη : IsLCAPlancherelMeasure μ η)
    {w : G → ℝ} (hw : Continuous w) (hpos : ∀ x, 0 < w x)
    {ρ φ : G → ℂ} (hρ : Continuous ρ) (hρc : HasCompactSupport ρ)
    (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hF : Integrable (lcaFourier μ φ) η) :
    let μw := μ.withDensity (fun x => ENNReal.ofReal (w x))
    letI : IsLocallyFiniteMeasure μw := IsLocallyFiniteMeasure.withDensity_ofReal hw
    let k := cutoffConvolutionKernel w ρ φ
    ∃ (hk : MemLp k 2 (μw.prod μw)) (T : TraceClass (Lp ℂ 2 μw)),
      T.toOperator = kernelIntegralOperator (hk.toLp k) ∧
      T.traceValue = (∫ x, ρ x ∂μ) * φ 1 := by
  obtain ⟨F, hFφ, hInv⟩ := lcaFourier_plancherel_inversion μ η hη
    (hφ.integrable_of_hasCompactSupport hφc) hF
  have he : (F : G → ℂ) = φ := Measure.eq_of_ae_eq hFφ F.continuous hφ
  obtain ⟨q, r, hq, hr, hRep⟩ := exists_L2_spectral_factors hF
  let χ (p : G × PontryaginDual G) : ℂ := (p.2 p.1 : ℂ)
  have hc : Continuous χ :=
    continuous_subtype_val.comp ((continuous_eval (F := C(G, Circle))).comp
      (((ContinuousMonoidHom.isInducing_toContinuousMap G Circle).continuous.comp
        continuous_snd).prodMk continuous_fst))
  refine cutoffConvolution_traceClass_of_spectral_factors μ η hw hpos hρ hρc hφ hφc χ
    hc.measurable (fun p => (Circle.norm_coe _).le) q r hq hr ?_
  intro x _ y _
  rw [← he, hInv]
  apply integral_congr_ae
  refine .of_forall fun ξ => ?_
  change lcaFourier μ φ ξ * (ξ (x * y⁻¹) : ℂ) =
    (ξ x : ℂ) * star (ξ y : ℂ) * (q ξ * star (r ξ))
  rw [hRep ξ]
  rw [map_mul, map_inv, Circle.coe_mul, Circle.coe_inv_eq_conj]
  exact mul_comm _ _


end Group
end
end Masullo
