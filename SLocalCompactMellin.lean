import SLocalArchSimultaneousInterpolation

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical NumberField

namespace Masullo

noncomputable section

/-- A Laplace integral of a continuous, compactly supported test has an
entire transform for any continuous real-valued spectral coordinate. -/
theorem analyticAt_integral_exp_mul_of_hasCompactSupport
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    (η : Measure X) [IsFiniteMeasureOnCompacts η]
    {l : X → ℝ} (hl : Continuous l) {f : X → ℂ} (hf : Continuous f)
    (hc : HasCompactSupport f) (z : ℂ) :
    AnalyticAt ℂ (fun w : ℂ ↦ ∫ x, Complex.exp (w * (l x : ℂ)) * f x ∂η) z := by
  apply Differentiable.analyticAt
  intro w
  let C := tsupport f
  have hC : IsCompact C := hc
  obtain ⟨M, hM⟩ := hC.bddAbove_image hl.norm.continuousOn
  obtain ⟨N, hN⟩ := hC.bddAbove_image hf.norm.continuousOn
  let R := |M| + 1
  let A := |N| + 1
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  let G (w : ℂ) (x : X) := Complex.exp (w * (l x : ℂ)) * f x
  let G' (w : ℂ) (x : X) := (Complex.exp (w * (l x : ℂ)) * (l x : ℂ)) * f x
  have hg (w : ℂ) : Continuous (G w) := by
    exact (Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp hl))).mul hf
  have hg' (w : ℂ) : Continuous (G' w) := by
    exact ((Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp hl))).mul
      (Complex.continuous_ofReal.comp hl)).mul hf
  let D : ℝ := Real.exp ((‖w‖ + 1) * R) * R * A
  have hD0 : IntegrableOn (fun _ : X ↦ D) C η := integrableOn_const hC.measure_lt_top.ne
  have hD : Integrable (C.indicator (fun _ ↦ D)) η :=
    (integrable_indicator_iff (isClosed_closure : IsClosed C).measurableSet).mpr hD0
  have hI : Integrable (G w) η := (hg w).integrable_of_hasCompactSupport hc.mul_left
  have hbound (v : ℂ) (hv : v ∈ Metric.ball w 1) (x : X) :
      ‖G' v x‖ ≤ C.indicator (fun _ ↦ D) x := by
    by_cases hx : x ∈ C
    · have hlx : |l x| ≤ R := by
        have hm : ‖l x‖ ≤ M := hM ⟨x, hx, rfl⟩
        exact hm.trans ((le_abs_self M).trans (by dsimp [R]; linarith))
      have hfx : ‖f x‖ ≤ A := (hN ⟨x, hx, rfl⟩).trans
        ((le_abs_self N).trans (by dsimp [A]; linarith))
      have hvw : ‖v‖ ≤ ‖w‖ + 1 := by
        have hh : ‖v - w‖ < 1 := by simpa only [Metric.mem_ball, dist_eq_norm] using hv
        linarith [norm_le_insert' v w]
      have hvl : (v * (l x : ℂ)).re ≤ (‖w‖ + 1)*R := by
        calc
          _ ≤ ‖v * (l x : ℂ)‖ := Complex.re_le_norm _
          _ = ‖v‖ * |l x| := by rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          _ ≤ _ := mul_le_mul hvw hlx (abs_nonneg _) (by positivity)
      rw [indicator_of_mem hx]
      change ‖(Complex.exp (v * (l x : ℂ)) * (l x : ℂ)) * f x‖ ≤ D
      rw [norm_mul, norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul (mul_le_mul (Real.exp_le_exp.mpr hvl) hlx (abs_nonneg _) (by positivity))
        hfx (norm_nonneg _) (by positivity)
    · have hz : f x = 0 := image_eq_zero_of_notMem_tsupport hx
      simp [G', indicator_of_notMem hx, hz]
  have hd (v : ℂ) (x : X) : HasDerivAt (fun p ↦ G p x) (G' v x) v := by
    simpa [G, G'] using (((hasDerivAt_id v).mul_const (l x : ℂ)).cexp).mul_const (f x)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Metric.ball w 1) (Metric.ball_mem_nhds _ zero_lt_one)
    (.of_forall fun v ↦ (hg v).aestronglyMeasurable) hI
    (hg' w).aestronglyMeasurable
    (.of_forall fun x v hv ↦ hbound v hv x) hD
    (.of_forall fun x v _ ↦ hd v x)).2.differentiableAt

variable (F : Type*) [Field F] [NumberField F]
variable (S : Finset (HeightOneSpectrum (𝓞 F)))

private abbrev G := (SAdeles F S)ˣ
private abbrev L (v : S) := v.val.adicCompletion F

attribute [local instance] sLocalZetaUnfolding_classMeasurable sLocalZetaUnfolding_classBorel
  sLocalZetaUnfolding_idelesMeasurable sLocalZetaUnfolding_idelesBorel

/-- If the restriction of an additive test to the multiplicative
S-adeles has compact support there, the actual idelic integral is entire. -/
theorem sLocalIdelicZeta_analyticAt_of_hasCompactSupport
    (η : Measure (G F S)) [IsFiniteMeasureOnCompacts η]
    (ω : PontryaginDual (SLocalThetaNormOne F S)) (f : sLocalBruhatImage F S)
    (hf : HasCompactSupport (fun g : G F S ↦ sLocalBruhatRestriction F S f.val g.val))
    (z : ℂ) : AnalyticAt ℂ (sLocalIdelicZetaIntegral F S η ω f) z := by
  let q : G F S → SIdeleQuotient F S := QuotientGroup.mk
  let D := (sLocalZetaSplit F S).symm ∘ q
  let a (g : G F S) : ℝ := (D g).1
  let p (g : G F S) : ℂ := (ω (D g).2 : Circle)
  let b (g : G F S) := sLocalBruhatRestriction F S f.val g.val
  have hD : Continuous D := (sLocalZetaSplit F S).symm.continuous.comp QuotientGroup.continuous_mk
  have ha : Continuous a := continuous_fst.comp hD
  have hp : Continuous p := continuous_subtype_val.comp (ω.continuous.comp (continuous_snd.comp hD))
  have hb : Continuous b := (sLocalBruhatRestriction_continuous F S f.val).comp Units.continuous_val
  have h := analyticAt_integral_exp_mul_of_hasCompactSupport η ha (hp.mul hb) (hf.mul_left (f := p)) z
  change AnalyticAt ℂ (fun w : ℂ ↦ ∫ g, Complex.exp (w * (a g : ℂ)) * (p g * b g) ∂η) z at h
  simp only [a, p, b, D, q, Function.comp_apply, ← mul_assoc] at h
  exact h

variable [∀ v : S, MeasurableSpace (L F S v)ˣ] [∀ v : S, BorelSpace (L F S v)ˣ]
variable (μ : ∀ v : S, Measure (L F S v)ˣ)
  [∀ v : S, (μ v).IsHaarMeasure] [∀ v : S, SigmaFinite (μ v)]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]

/-- The continued product Mellin transform has no poles when the
restriction of the test to the multiplicative group has compact support. -/
theorem sLocalProductZetaContinued_order_nonneg_of_hasCompactSupport
    (ω : PontryaginDual (SLocalThetaNormOne F S)) (f : sLocalBruhatImage F S)
    (hf : HasCompactSupport (fun g : G F S ↦ sLocalBruhatRestriction F S f.val g.val))
    (z : ℂ) :
    0 ≤ meromorphicOrderAt (sLocalProductZetaContinued F S μ ω (sLocalRealArchParameters F S ω)
      (sLocalComplexArchParameters F S ω) f) z := by
  let η := sLocalZetaProductMeasure F S μ (archimedeanMultiplicativeHaar F)
  letI : η.IsHaarMeasure := sLocalZetaProductMeasure_isHaar F S μ (archimedeanMultiplicativeHaar F)
  have hA (w : ℂ) := sLocalIdelicZeta_analyticAt_of_hasCompactSupport F S η ω f hf w
  have h := sLocalIdelicZeta_meromorphic_continuation F S μ ω f
  have he := boundedPoleMellinSpace_unique_germs
    (isOpen_lt (continuous_const (y := (0 : ℝ))) Complex.continuous_re) ⟨1, by simp⟩
    h.1 (fun w ↦ (hA w).meromorphicAt) h.2 z
  rw [meromorphicOrderAt_congr he]
  exact (hA z).meromorphicOrderAt_nonneg

variable (ν : Measure (SLocalThetaNormOne F S)) [ν.IsHaarMeasure]
variable (hν : IsWeilQuotientMeasure (sUnitImage F S)
  (sLocalZetaProductMeasure F S μ (archimedeanMultiplicativeHaar F))
  Measure.count (sLocalClassHaar F S ν))

include hν in
/-- Tests in the finite principal-value range with compact multiplicative
support represent classes in the entire-Mellin kernel. -/
theorem sLocalArchPolarKernel_mk_of_hasCompactSupport
    (ω : PontryaginDual (SLocalThetaNormOne F S)) (f : sLocalBruhatImage F S)
    (hr : f ∈ sLocalFiniteNonzeroTestSubspace F S Finset.univ)
    (hf : HasCompactSupport (fun g : G F S ↦ sLocalBruhatRestriction F S f.val g.val)) :
    (⟨(sLocalHomogeneousThetaKernel F S ν ω).mkQ f, ⟨f, hr, rfl⟩⟩ :
      sLocalArchPolarImage F S ν ω) ∈ sLocalArchPolarKernel F S μ ν hν ω := by
  change (Submodule.Quotient.mk f : SLocalHomogeneousThetaQuotient F S ν ω) ∈
    sLocalThetaPoleBound F S μ ν hν ω (fun _ ↦ 0)
  apply (mem_sLocalThetaPoleBound_mk F S μ ν hν ω (fun _ ↦ 0) f).mpr
  intro c
  change 0 ≤ _
  exact sLocalProductZetaContinued_order_nonneg_of_hasCompactSupport F S μ ω f hf c

end

end Masullo
