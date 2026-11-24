import SLocalThetaLargeNorm
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

open Bornology Filter IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped NumberField

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]
variable (S : Finset (HeightOneSpectrum (𝓞 F)))
variable [MeasurableSpace (SLocalThetaNormOne F S)] [BorelSpace (SLocalThetaNormOne F S)]

omit [MeasurableSpace (SLocalThetaNormOne F S)] [BorelSpace (SLocalThetaNormOne F S)] in
private def expSectionInSBlock : Multiplicative ℝ →* sIdeleBlock F S :=
  (ideleExpSection F).codRestrict _ (fun t => by
    apply (sIdeleBlock_mem_iff F S _).mpr
    intro v _
    apply (ideleOrder_eq_zero_iff F _ v).mpr
    rw [(ideleExpSection_components F t).2]
    change Valued.v (1 : v.adicCompletion F) = 1
    exact map_one _)

omit [MeasurableSpace (SLocalThetaNormOne F S)] [BorelSpace (SLocalThetaNormOne F S)] in
/-- The canonical positive norm section descends from the global section
with unit finite coordinates. -/
def sLocalExpSection : Multiplicative ℝ →* (SAdeles F S)ˣ :=
  (MonoidHom.fst _ _).comp ((sBlockUnitProduct F S).toMonoidHom.comp (expSectionInSBlock F S))

omit [MeasurableSpace (SLocalThetaNormOne F S)] [BorelSpace (SLocalThetaNormOne F S)] in
theorem sLocalExpSection_continuous : Continuous (sLocalExpSection F S) :=
  continuous_fst.comp ((sBlockUnitProduct F S).continuous.comp
    ((ideleExpSection_continuous F).subtype_mk _))

omit [MeasurableSpace (SLocalThetaNormOne F S)] [BorelSpace (SLocalThetaNormOne F S)] in
theorem sLocalIdeleNorm_expSection (t : ℝ) :
    sLocalIdeleNorm F S (sLocalExpSection F S (Multiplicative.ofAdd t)) = Real.exp t :=
  (sBlock_norm_eq F S (expSectionInSBlock F S (Multiplicative.ofAdd t))).trans
    (ideleNorm_expSection F (Multiplicative.ofAdd t))

/-- The radial homogeneous theta integral in the logarithmic coordinate
of a section of the S-idelic modulus. -/
def sLocalRadialMellin (τ : Multiplicative ℝ →* (SAdeles F S)ˣ)
    (μ : Measure (SLocalThetaNormOne F S)) (ω : PontryaginDual (SLocalThetaNormOne F S))
    (f : sLocalBruhatImage F S) (z : ℂ) : ℂ :=
  ∫ t : ℝ, Complex.exp (z * (t : ℂ)) *
    sLocalHomogeneousTheta F S μ ω f.val (QuotientGroup.mk (τ (Multiplicative.ofAdd t)))

theorem integrable_exp_abs_envelope (c : ℝ) (hc : 0 < c) :
    Integrable (fun t : ℝ => Real.exp (-c * |t|)) := by
  have h₁ : IntegrableOn (fun t : ℝ => Real.exp (-c * |t|)) (Iic 0) := by
    apply (integrableOn_exp_mul_Iic hc 0).congr_fun _ measurableSet_Iic
    intro t ht
    change Real.exp (c * t) = Real.exp (-c * |t|)
    rw [abs_of_nonpos (mem_Iic.mp ht), neg_mul_neg]
  have h₂ : IntegrableOn (fun t : ℝ => Real.exp (-c * |t|)) (Ioi 0) := by
    apply (integrableOn_exp_mul_Ioi (neg_neg_of_pos hc) 0).congr_fun _ measurableSet_Ioi
    intro t ht
    change Real.exp (-c * t) = Real.exp (-c * |t|)
    rw [abs_of_pos (mem_Ioi.mp ht)]
  have h := h₁.union h₂
  rwa [Iic_union_Ioi, integrableOn_univ] at h

omit [BorelSpace (SLocalThetaNormOne F S)] in
/-- On every closed strip in the right half-plane, the radial Mellin kernels
have one integrable majorant, uniform also on bounded sets of test functions. -/
theorem sLocalRadialMellin_strip_majorant
    (τ : Multiplicative ℝ →* (SAdeles F S)ˣ)
    (hτnorm : ∀ t : ℝ, sLocalIdeleNorm F S (τ (Multiplicative.ofAdd t)) = Real.exp t)
    (μ : Measure (SLocalThetaNormOne F S)) [μ.IsHaarMeasure]
    (ω : PontryaginDual (SLocalThetaNormOne F S)) (B : Set (sLocalBruhatImage F S))
    (hB : IsVonNBounded ℂ B) (a b : ℝ) (ha : 0 < a) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ Integrable (fun t : ℝ => C * Real.exp (-c * |t|)) ∧
      ∀ f ∈ B, ∀ z : ℂ, a ≤ z.re → z.re ≤ b → ∀ t : ℝ,
        ‖Complex.exp (z * (t : ℂ)) *
          sLocalHomogeneousTheta F S μ ω f.val (QuotientGroup.mk (τ (Multiplicative.ofAdd t)))‖ ≤
            C * Real.exp (-c * |t|) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (b + 1)
  have hhalf : 0 < a / 2 := half_pos ha
  obtain ⟨A, hA, hsmall⟩ := sLocalTheta_smallNorm_bounded F S μ ω B hB (a / 2) hhalf
  obtain ⟨D, hD, hlarge⟩ := sLocalHomogeneousTheta_largeNorm_bounded F S μ ω B hB N
  let c := min (a / 2) 1
  have hc : 0 < c := lt_min hhalf zero_lt_one
  refine ⟨c, A + D, hc, add_pos hA hD, (integrable_exp_abs_envelope c hc).const_mul _, ?_⟩
  intro f hf z hz₁ hz₂ t
  let q : SIdeleQuotient F S := QuotientGroup.mk (τ (Multiplicative.ofAdd t))
  let θ := sLocalHomogeneousTheta F S μ ω f.val q
  have hm : sLocalClassModulus F S q = Real.exp t :=
    (sLocalClassModulus_mk F S _).trans (hτnorm t)
  change ‖Complex.exp (z * (t : ℂ)) * θ‖ ≤ _
  rw [norm_mul, Complex.norm_exp, show (z * (t : ℂ)).re = z.re * t by simp [Complex.mul_re]]
  by_cases ht : t < 0
  · have hs := (hsmall f hf q (hm ▸ Real.exp_lt_one_iff.mpr ht)).2
    rw [hm, ← Real.exp_mul] at hs
    have hexp : (z.re - a / 2) * t ≤ -c * |t| := by
      rw [abs_of_neg ht, neg_mul_neg]
      exact mul_le_mul_of_nonpos_right (by dsimp [c]; linarith [min_le_left (a / 2) 1]) ht.le
    calc
      _ = (‖θ‖ * Real.exp (t * (a / 2))) * Real.exp ((z.re - a / 2) * t) := by
        rw [mul_assoc, ← Real.exp_add, mul_comm ‖θ‖]
        congr 2
        ring
      _ ≤ A * Real.exp (-c * |t|) :=
        mul_le_mul hs (Real.exp_le_exp.mpr hexp) (Real.exp_nonneg _) hA.le
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hD.le) (Real.exp_nonneg _)
  · have h₀ : 0 ≤ t := le_of_not_gt ht
    have hs := hlarge f hf q (hm ▸ Real.one_le_exp_iff.mpr h₀)
    rw [hm, ← Real.exp_nat_mul, ← Real.exp_neg] at hs
    have hexp : (z.re - (N : ℝ)) * t ≤ -c * |t| := by
      rw [abs_of_nonneg h₀]
      exact mul_le_mul_of_nonneg_right (by dsimp [c]; linarith [min_le_right (a / 2) 1]) h₀
    calc
      _ ≤ Real.exp (z.re * t) * (D * Real.exp (-((N : ℝ) * t))) :=
        mul_le_mul_of_nonneg_left hs (Real.exp_nonneg _)
      _ = D * Real.exp ((z.re - (N : ℝ)) * t) := by
        rw [mul_left_comm, ← Real.exp_add]
        congr 2
        ring
      _ ≤ D * Real.exp (-c * |t|) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) hD.le
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hA.le) (Real.exp_nonneg _)

/-- Absolute convergence of the actual radial integral in (3.3.1.5). -/
theorem sLocalRadialMellin_integrable
    (τ : Multiplicative ℝ →* (SAdeles F S)ˣ) (hτ : Continuous τ)
    (hτnorm : ∀ t : ℝ, sLocalIdeleNorm F S (τ (Multiplicative.ofAdd t)) = Real.exp t)
    (μ : Measure (SLocalThetaNormOne F S)) [μ.IsHaarMeasure]
    (ω : PontryaginDual (SLocalThetaNormOne F S)) (f : sLocalBruhatImage F S) (z : ℂ)
    (hz : 0 < z.re) :
    Integrable (fun t : ℝ => Complex.exp (z * (t : ℂ)) *
      sLocalHomogeneousTheta F S μ ω f.val (QuotientGroup.mk (τ (Multiplicative.ofAdd t)))) := by
  obtain ⟨c, C, _, _, hint, hmaj⟩ := sLocalRadialMellin_strip_majorant F S τ hτnorm μ ω
    {f} (isVonNBounded_singleton (𝕜 := ℂ) f) z.re z.re hz
  have hp : Continuous (fun t : ℝ =>
      (QuotientGroup.mk (τ (Multiplicative.ofAdd t)) : SIdeleQuotient F S)) :=
    QuotientGroup.continuous_mk.comp (hτ.comp continuous_ofAdd)
  have hθ := (sLocalHomogeneousTheta_continuous F S μ ω f.val).comp hp
  have he : Continuous (fun t : ℝ => Complex.exp (z * (t : ℂ))) := by fun_prop
  exact hint.mono' (he.mul hθ).aestronglyMeasurable
    (Eventually.of_forall (hmaj f (by simp) z le_rfl le_rfl))

private theorem integrable_radial_moment (c C : ℝ) (hc : 0 < c) (hC : 0 ≤ C) :
    Integrable (fun t : ℝ => |t| * (C * Real.exp (-c * |t|))) := by
  let d := c / 2
  have hd : 0 < d := half_pos hc
  apply ((integrable_exp_abs_envelope d hd).const_mul (C / d)).mono'
  · exact (by fun_prop : Continuous (fun t : ℝ => |t| * (C * Real.exp (-c * |t|)))).aestronglyMeasurable
  refine Eventually.of_forall fun t => ?_
  rw [Real.norm_of_nonneg (by positivity)]
  have he : |t| ≤ (Real.exp (d * |t|)) / d :=
    (le_div_iff₀ hd).mpr (by linarith [Real.add_one_le_exp (d * |t|)])
  calc
    _ ≤ (Real.exp (d * |t|) / d) * (C * Real.exp (-c * |t|)) :=
      mul_le_mul_of_nonneg_right he (by positivity)
    _ = C / d * (Real.exp (d * |t|) * Real.exp (-c * |t|)) := by ring
    _ = C / d * Real.exp (-d * |t|) := by
      rw [← Real.exp_add]
      congr 2
      dsimp [d]
      ring

/-- The radial Mellin integral is holomorphic on the positive half-plane. -/
theorem sLocalRadialMellin_analytic (τ : Multiplicative ℝ →* (SAdeles F S)ˣ)
    (hτ : Continuous τ)
    (hτnorm : ∀ t : ℝ, sLocalIdeleNorm F S (τ (Multiplicative.ofAdd t)) = Real.exp t)
    (μ : Measure (SLocalThetaNormOne F S)) [μ.IsHaarMeasure]
    (ω : PontryaginDual (SLocalThetaNormOne F S)) (f : sLocalBruhatImage F S) :
    AnalyticOnNhd ℂ (sLocalRadialMellin F S τ μ ω f) {z | 0 < z.re} := by
  have ho : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  apply DifferentiableOn.analyticOnNhd _ ho
  intro z hz
  let θ (t : ℝ) := sLocalHomogeneousTheta F S μ ω f.val (QuotientGroup.mk (τ (Multiplicative.ofAdd t)))
  have hp : Continuous (fun t : ℝ =>
      (QuotientGroup.mk (τ (Multiplicative.ofAdd t)) : SIdeleQuotient F S)) :=
    QuotientGroup.continuous_mk.comp (hτ.comp continuous_ofAdd)
  have hθ : Continuous θ := (sLocalHomogeneousTheta_continuous F S μ ω f.val).comp hp
  let kernel (w : ℂ) (t : ℝ) := Complex.exp (w * (t : ℂ)) * θ t
  have hk (w : ℂ) : Continuous (kernel w) := by
    unfold kernel
    fun_prop
  have hz' : 0 < z.re := hz
  let a := z.re / 2
  let b := z.re + 1
  have ha : 0 < a := half_pos hz'
  obtain ⟨c, C, hc, hC, _, hm⟩ := sLocalRadialMellin_strip_majorant F S τ hτnorm μ ω
    {f} (isVonNBounded_singleton (𝕜 := ℂ) f) a b ha
  have hn : Complex.re ⁻¹' Ioo a b ∈ 𝓝 z :=
    (isOpen_Ioo.preimage Complex.continuous_re).mem_nhds ⟨by dsimp [a]; linarith, by dsimp [b]; linarith⟩
  have hd (w : ℂ) (t : ℝ) : HasDerivAt (fun q => kernel q t) ((t : ℂ) * kernel w t) w := by
    simpa only [kernel, id_eq, one_mul, mul_assoc, mul_left_comm] using
      ((((hasDerivAt_id w).mul_const (t : ℂ)).cexp).mul_const (θ t))
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := kernel) (F' := fun w t => (t : ℂ) * kernel w t)
    (bound := fun t => |t| * (C * Real.exp (-c * |t|))) hn
    (Eventually.of_forall fun w => (hk w).aestronglyMeasurable)
    (sLocalRadialMellin_integrable F S τ hτ hτnorm μ ω f z hz')
    ((Complex.continuous_ofReal.mul (hk z)).aestronglyMeasurable)
    (Eventually.of_forall fun t w hw => by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hm f (by simp) w hw.1.le hw.2.le t) (abs_nonneg _))
    (integrable_radial_moment c C hc hC.le)
    (Eventually.of_forall fun t w _ => hd w t)
  exact h.2.differentiableAt.differentiableWithinAt

/-- The manuscript's modulus truncations converge uniformly on closed strips
in the positive half-plane in logarithmic coordinates. -/
theorem sLocalRadialMellin_truncation (τ : Multiplicative ℝ →* (SAdeles F S)ˣ)
    (hτ : Continuous τ)
    (hτnorm : ∀ t : ℝ, sLocalIdeleNorm F S (τ (Multiplicative.ofAdd t)) = Real.exp t)
    (μ : Measure (SLocalThetaNormOne F S)) [μ.IsHaarMeasure]
    (ω : PontryaginDual (SLocalThetaNormOne F S)) (f : sLocalBruhatImage F S)
    (a b : ℝ) (ha : 0 < a) :
    TendstoUniformlyOn (fun (n : ℕ) (z : ℂ) => ∫ t : ℝ in Icc (-Real.log n) (Real.log n),
      Complex.exp (z * (t : ℂ)) *
        sLocalHomogeneousTheta F S μ ω f.val (QuotientGroup.mk (τ (Multiplicative.ofAdd t))))
      (sLocalRadialMellin F S τ μ ω f) atTop (Complex.re ⁻¹' Icc a b) := by
  obtain ⟨c, C, _, hC, hM, hm⟩ := sLocalRadialMellin_strip_majorant F S τ hτnorm μ ω
    {f} (isVonNBounded_singleton (𝕜 := ℂ) f) a b ha
  let M (t : ℝ) := C * Real.exp (-c * |t|)
  let J (n : ℕ) := Icc (-Real.log n) (Real.log n)
  have hj (n : ℕ) : MeasurableSet (J n) := measurableSet_Icc
  have ht : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have htmem (t : ℝ) : ∀ᶠ n in atTop, t ∈ J n := by
    filter_upwards [ht.eventually_ge_atTop |t|] with n hn
    exact ⟨by linarith [neg_le_abs t], (le_abs_self t).trans hn⟩
  have htail : Tendsto (fun n : ℕ => ∫ t in (J n)ᶜ, M t) atTop (𝓝 0) := by
    simp_rw [← integral_indicator (hj _).compl]
    have h := tendsto_integral_filter_of_dominated_convergence (bound := M)
      (F := fun n : ℕ => (J n)ᶜ.indicator M) (f := fun _ : ℝ => (0 : ℝ))
      (Eventually.of_forall fun n => hM.aestronglyMeasurable.indicator (hj n).compl)
      (Eventually.of_forall fun n => Eventually.of_forall fun t => by
        by_cases hh : t ∈ J n
        · rw [indicator_of_notMem (notMem_compl_iff.mpr hh), norm_zero]
          dsimp [M]
          positivity
        · rw [indicator_of_mem (mem_compl hh), Real.norm_of_nonneg (by dsimp [M]; positivity)])
      hM (Eventually.of_forall fun t => tendsto_const_nhds.congr'
        ((htmem t).mono fun n hn => (indicator_of_notMem (notMem_compl_iff.mpr hn) M).symm))
    simpa only [integral_zero] using h
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [htail.eventually (Iio_mem_nhds hε)] with n hn z hz
  let K (t : ℝ) := Complex.exp (z * (t : ℂ)) *
    sLocalHomogeneousTheta F S μ ω f.val (QuotientGroup.mk (τ (Multiplicative.ofAdd t)))
  have hk : Integrable K := sLocalRadialMellin_integrable F S τ hτ hτnorm μ ω f z (ha.trans_le hz.1)
  change dist (∫ t, K t) (∫ t in J n, K t) < ε
  rw [dist_eq_norm, ← integral_add_compl (hj n) hk, add_sub_cancel_left]
  exact (norm_integral_le_of_norm_le hM.integrableOn
    (Eventually.of_forall (hm f (by simp) z hz.1 hz.2))).trans_lt hn

end

end Masullo
