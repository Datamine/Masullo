import ModulatedSobolevCoefficients
import ModulatedSobolevTensor

open Filter Function MeasureTheory Set Topology
open scoped ENNReal TensorProduct InnerProductSpace

namespace Masullo

noncomputable section

variable {K : Type*} [TopologicalSpace K] [MeasurableSpace K] [BorelSpace K] [CommGroup K]
  (μ : Measure K) [IsFiniteMeasure μ]

omit [TopologicalSpace K] [BorelSpace K] [CommGroup K] [IsFiniteMeasure μ] in
private theorem stripMeasure_prod_amplitude (a b s : ℝ) :
    μ.prod (stripMeasure a b s) =
      amplitudeMeasure (μ.prod (volume : Measure ℝ))
        (fun p : K × ℝ => stripSobolevAmplitude a b s p.2) := by
  unfold stripMeasure amplitudeMeasure
  exact prod_withDensity_right (μ := μ) (ν := (volume : Measure ℝ))
    (g := fun x => ENNReal.ofReal (stripSobolevAmplitude a b s x ^ 2))
    ((stripSobolevAmplitude_continuous a b s).measurable.pow_const 2).ennreal_ofReal

private theorem radial_measure_ac (a b s : ℝ) : (volume : Measure ℝ) ≪ stripMeasure a b s :=
  absolutelyContinuous_amplitudeMeasure volume _
    (stripSobolevAmplitude_continuous a b s).measurable (stripSobolevAmplitude_pos a b s)

omit [TopologicalSpace K] [BorelSpace K] [CommGroup K] [IsFiniteMeasure μ] in
private theorem weightedProd_measure_ac (a b s : ℝ) :
    μ.prod (volume : Measure ℝ) ≪ μ.prod (stripMeasure a b s) :=
  Measure.AbsolutelyContinuous.rfl.prod (radial_measure_ac a b s)

/-- Project onto the scalar cutoff by the actual compact character integral. -/
def modulatedIntervalCoefficient (a b s : ℝ) {U : Set ℝ} (hU : IsOpen U)
    (χ : PontryaginDual K) :
    lpTwoRadialSupport μ (stripMeasure a b s) U →L[ℂ] supportedSobolevCompletion a b s U := by
  let L := lpTwoCharacterCoefficient (μ := μ) (ν := stripMeasure a b s) χ
  refine (L.comp (lpTwoRadialSupport μ (stripMeasure a b s) U).subtypeL).codRestrict _ ?_
  intro u
  apply (mem_supportedSobolevCompletion_iff a b s hU _).mpr
  have h : ∀ᵐ x ∂(stripMeasure a b s), x ∉ U → L u.val x = 0 :=
    lpTwoFirstCoefficient_radialSupport _ u
  exact (radial_measure_ac a b s).ae_le h

theorem modulatedIntervalCoefficient_ae (a b s : ℝ) {U : Set ℝ} (hU : IsOpen U)
    (χ : PontryaginDual K) (u : lpTwoRadialSupport μ (stripMeasure a b s) U) :
    ∀ᵐ x ∂(volume : Measure ℝ),
      (modulatedIntervalCoefficient μ a b s hU χ u).val x =
        ∫ j, (χ j : ℂ) * u.val (j, x) ∂μ :=
  (radial_measure_ac a b s).ae_le ((lpTwoCharacterCoefficient_ae χ u.val).mono fun _ h => h.2)

local notation "RadialHaar" => (volume : Measure ℝ)

private theorem productMoment_integrable (a b s : ℝ) {U : Set ℝ} (hU : MeasurableSet U)
    (χ : PontryaginDual K) (k : ℕ) (z : ℂ)
    (hg : MemLp (U.indicator (mellinEvaluationKernel k z)) 2 (stripMeasure (-a) (-b) (-s)))
    (u : lpTwoRadialSupport μ (stripMeasure a b s) U) :
    Integrable (fun p : K × ℝ => (χ p.1 : ℂ) * u.val p * mellinEvaluationKernel k z p.2)
      (μ.prod RadialHaar) := by
  let R := stripSobolevAmplitude a b s
  let W := stripSobolevAmplitude (-a) (-b) (-s)
  let F (p : K × ℝ) := R p.2 • u.val p
  let g := U.indicator (mellinEvaluationKernel k z)
  let H (x : ℝ) := W x • g x
  let v : K × ℝ → ℂ := u.val
  have hu : MemLp v 2 (μ.prod (stripMeasure a b s)) := Lp.memLp u.val
  rw [stripMeasure_prod_amplitude] at hu
  have hF : MemLp F 2 (μ.prod RadialHaar) := (memLp_amplitudeMeasure_iff _ _
    ((stripSobolevAmplitude_continuous a b s).measurable.comp measurable_snd)
    ((Lp.aestronglyMeasurable u.val).mono_ac (weightedProd_measure_ac μ a b s))).mp hu
  have hg' : Measurable g := (show Continuous (mellinEvaluationKernel k z) by
    unfold mellinEvaluationKernel
    fun_prop).measurable.indicator hU
  have hH : MemLp H 2 RadialHaar := (memLp_amplitudeMeasure_iff _ _
    (stripSobolevAmplitude_continuous (-a) (-b) (-s)).measurable hg'.aestronglyMeasurable).mp hg
  have hχ : MemLp (fun j : K => (χ j : ℂ)) 2 μ := MemLp.of_bound
    (continuous_subtype_val.comp χ.continuous).aestronglyMeasurable 1
    (.of_forall fun j => (Circle.norm_coe (χ j)).le)
  let V := lpTwoProduct (hχ.toLp _) (hH.toLp _)
  have hV : (V : K × ℝ → ℂ) =ᵐ[μ.prod RadialHaar] fun p => (χ p.1 : ℂ) * H p.2 := by
    filter_upwards [lpTwoProduct_ae (hχ.toLp _) (hH.toLp _),
      ((Measure.quasiMeasurePreserving_fst (μ := μ) (ν := RadialHaar)).ae hχ.coeFn_toLp),
      ((Measure.quasiMeasurePreserving_snd (μ := μ) (ν := RadialHaar)).ae hH.coeFn_toLp)] with p hp h1 h2
    exact hp.trans (congrArg₂ (· * ·) h1 h2)
  have hi := (hF.integrable_mul (p := 2) (q := 2) (Lp.memLp V)).congr
    (hV.mono fun p hp => congrArg (F p * ·) hp)
  apply hi.congr
  filter_upwards [(weightedProd_measure_ac μ a b s).ae_le
    (show ∀ᵐ p ∂μ.prod (stripMeasure a b s), p.2 ∉ U → u.val p = 0 from u.property)] with p hp
  by_cases h : p.2 ∈ U
  · simp only [F, H, g, indicator_of_mem h, W, stripSobolevAmplitude_neg, Complex.real_smul]
    have he : (R p.2 : ℂ) * ((R p.2)⁻¹ : ℝ) = 1 := by
      rw [← Complex.ofReal_mul, mul_inv_cancel₀ (stripSobolevAmplitude_pos a b s p.2).ne',
        Complex.ofReal_one]
    calc
      _ = ((R p.2 : ℂ) * ((R p.2)⁻¹ : ℝ)) *
          ((χ p.1 : ℂ) * u.val p * mellinEvaluationKernel k z p.2) := by
        change ((R p.2 : ℂ) * u.val p) *
          ((χ p.1 : ℂ) * (((R p.2)⁻¹ : ℝ) * mellinEvaluationKernel k z p.2)) = _
        ring
      _ = _ := by rw [he, one_mul]
  · simp [F, hp h]

/-- Bounded character evaluation on a supported interval Hilbert space,
represented by the absolutely integrable group moment in split Haar coordinates. -/
theorem modulatedInterval_mellinMoment_of_kernel (a b s : ℝ) {U : Set ℝ} (hU : IsOpen U)
    (χ : PontryaginDual K) (k : ℕ) (z : ℂ)
    (hg : MemLp (U.indicator (mellinEvaluationKernel k z)) 2 (stripMeasure (-a) (-b) (-s))) :
    ∃! L : StrongDual ℂ (lpTwoRadialSupport μ (stripMeasure a b s) U),
      ∀ u : lpTwoRadialSupport μ (stripMeasure a b s) U,
        let F (p : K × ℝ) := (χ p.1 : ℂ) * u.val p * mellinEvaluationKernel k z p.2
        Integrable F (μ.prod RadialHaar) ∧ L u = ∫ p, F p ∂μ.prod RadialHaar := by
  let A := modulatedIntervalCoefficient μ a b s hU χ
  let g := hg.toLp _
  let L := (stripSobolevDuality a b s g).comp
    ((supportedSobolevCompletion a b s U).subtypeL.comp A)
  have hL (u : lpTwoRadialSupport μ (stripMeasure a b s) U) :
      let F (p : K × ℝ) := (χ p.1 : ℂ) * u.val p * mellinEvaluationKernel k z p.2
      Integrable F (μ.prod RadialHaar) ∧ L u = ∫ p, F p ∂μ.prod RadialHaar := by
    dsimp only
    let F (p : K × ℝ) := (χ p.1 : ℂ) * u.val p * mellinEvaluationKernel k z p.2
    have hi := productMoment_integrable μ a b s hU.measurableSet χ k z hg u
    refine ⟨hi, ?_⟩
    change stripSobolevDuality a b s g (A u).val = ∫ p, F p ∂μ.prod RadialHaar
    rw [stripSobolevDuality_apply, integral_prod_symm F hi]
    apply integral_congr_ae
    filter_upwards [modulatedIntervalCoefficient_ae μ a b s hU χ u,
      (radial_measure_ac (-a) (-b) (-s)).ae_le hg.coeFn_toLp,
      (mem_supportedSobolevCompletion_iff a b s hU (A u).val).mp (A u).property]
      with x hx hK hu
    change (A u).val x * g x = ∫ j, F (j, x) ∂μ
    rw [show (∫ j, F (j, x) ∂μ) =
      (∫ j, (χ j : ℂ) * u.val (j, x) ∂μ) * mellinEvaluationKernel k z x from
      by dsimp only [F]; exact integral_mul_const _ _]
    change (A u).val x = _ at hx
    rw [← hx, hK]
    by_cases h : x ∈ U
    · rw [indicator_of_mem h]
    · simp [hu h]
  refine ⟨L, hL, fun Q hQ => ?_⟩
  ext u
  exact (hQ u).2.trans (hL u).2.symm

/-- The actual supported Mellin moments in split Haar coordinates. -/
def modulatedIntervalMoment (a b s : ℝ) {U : Set ℝ}
    (χ : PontryaginDual K) (u : lpTwoRadialSupport μ (stripMeasure a b s) U)
    (k : ℕ) (z : ℂ) : ℂ :=
  ∫ p : K × ℝ, (χ p.1 : ℂ) * u.val p * mellinEvaluationKernel k z p.2 ∂μ.prod RadialHaar

private theorem modulatedIntervalMoment_hasDerivAt_of_open (a b s : ℝ) {U : Set ℝ}
    (hU : IsOpen U) (χ : PontryaginDual K)
    (u : lpTwoRadialSupport μ (stripMeasure a b s) U) {J : Set ℝ} (hJ : IsOpen J)
    (hKer : ∀ w : ℂ, w.re ∈ J → ∀ k : ℕ,
      MemLp (U.indicator (mellinEvaluationKernel k w)) 2 (stripMeasure (-a) (-b) (-s)))
    (k : ℕ) {z : ℂ} (hz : z.re ∈ J) :
    HasDerivAt (modulatedIntervalMoment μ a b s χ u k)
      (modulatedIntervalMoment μ a b s χ u (k + 1) z) z := by
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (hJ.mem_nhds hz)
  let l := z.re - δ / 2
  let r := z.re + δ / 2
  have hl : l < z.re := by dsimp [l]; linarith
  have hr : z.re < r := by dsimp [r]; linarith
  have hsub : Icc l r ⊆ J := by
    intro x hx
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    exact ⟨by linarith [show z.re - δ / 2 ≤ x from hx.1],
      by linarith [show x ≤ z.re + δ / 2 from hx.2]⟩
  let V := Complex.re ⁻¹' Ioo l r
  have hV : V ∈ 𝓝 z := (isOpen_Ioo.preimage Complex.continuous_re).mem_nhds ⟨hl, hr⟩
  let F (n : ℕ) (w : ℂ) (p : K × ℝ) := (χ p.1 : ℂ) * u.val p * mellinEvaluationKernel n w p.2
  have hI (n : ℕ) (w : ℂ) (hw : w.re ∈ J) :
      Integrable (F n w) (μ.prod RadialHaar) :=
    productMoment_integrable μ a b s hU.measurableSet χ n w (hKer w hw n) u
  have hD (w : ℂ) (p : K × ℝ) :
      HasDerivAt (fun ζ => F k ζ p) (F (k + 1) w p) w := by
    have hd := (((hasDerivAt_id' w).mul_const (p.2 : ℂ)).cexp.mul_const
      ((p.2 : ℂ) ^ k)).const_mul ((χ p.1 : ℂ) * u.val p)
    convert hd using 1
    all_goals first | rfl | (simp only [F, mellinEvaluationKernel, pow_succ]; ring)
  let M (p : K × ℝ) := ‖F (k + 1) (l : ℂ) p‖ + ‖F (k + 1) (r : ℂ) p‖
  have hMl : Integrable (F (k + 1) (l : ℂ)) (μ.prod RadialHaar) := hI _ _ (by simpa using hsub (left_mem_Icc.mpr (hl.le.trans hr.le)))
  have hMr : Integrable (F (k + 1) (r : ℂ)) (μ.prod RadialHaar) := hI _ _ (by simpa using hsub (right_mem_Icc.mpr (hl.le.trans hr.le)))
  have hM : Integrable M (μ.prod RadialHaar) := hMl.norm.add hMr.norm
  have hbound (p : K × ℝ) (w : ℂ) (hw : w ∈ V) : ‖F (k + 1) w p‖ ≤ M p := by
    have hwl : l ≤ w.re := (show l < w.re from hw.1).le
    have hwr : w.re ≤ r := (show w.re < r from hw.2).le
    simp only [F, M, norm_mul, mellinEvaluationKernel_norm, Complex.ofReal_re]
    by_cases h : 0 ≤ p.2
    · have he := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hwr h)
      exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right he (by positivity))
        (by positivity)).trans (le_add_of_nonneg_left (by positivity))
    · have he := Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_right hwl (le_of_not_ge h))
      exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right he (by positivity))
        (by positivity)).trans (le_add_of_nonneg_right (by positivity))
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le hV
    ((show ∀ᶠ w in 𝓝 z, w ∈ V from hV).mono fun w hw => (hI _ w
      (hsub (Ioo_subset_Icc_self (show w.re ∈ Ioo l r from hw)))).aestronglyMeasurable)
    (hI _ _ hz) (hI _ _ hz).aestronglyMeasurable
    (.of_forall fun p w hw => hbound p w hw) hM (.of_forall fun p w _ => hD w p)).2

/-- In the open region where all moments exist, the zeroth moment is
holomorphic and its complex derivatives are the corresponding moments. -/
theorem modulatedIntervalMoment_analyticOnAbscissae (a b s : ℝ) {U : Set ℝ}
    (hU : IsOpen U) (χ : PontryaginDual K)
    (u : lpTwoRadialSupport μ (stripMeasure a b s) U) {J : Set ℝ} (hJ : IsOpen J)
    (hKer : ∀ w : ℂ, w.re ∈ J → ∀ k : ℕ,
      MemLp (U.indicator (mellinEvaluationKernel k w)) 2 (stripMeasure (-a) (-b) (-s)))
    (k : ℕ) {z : ℂ} (hz : z.re ∈ J) :
    AnalyticAt ℂ (modulatedIntervalMoment μ a b s χ u 0) z ∧
      iteratedDeriv k (modulatedIntervalMoment μ a b s χ u 0) z =
        modulatedIntervalMoment μ a b s χ u k z := by
  let D := Complex.re ⁻¹' J
  have hD : IsOpen D := hJ.preimage Complex.continuous_re
  have hv (n : ℕ) (w : ℂ) (hw : w ∈ D) :=
    modulatedIntervalMoment_hasDerivAt_of_open μ a b s hU χ u hJ hKer n hw
  have hdiff : DifferentiableOn ℂ (modulatedIntervalMoment μ a b s χ u 0) D :=
    fun w hw => (hv 0 w hw).differentiableAt.differentiableWithinAt
  refine ⟨hdiff.analyticAt (hD.mem_nhds hz), ?_⟩
  induction k generalizing z with
  | zero => rfl
  | succ k ih =>
    rw [iteratedDeriv_succ]
    have he : iteratedDeriv k (modulatedIntervalMoment μ a b s χ u 0) =ᶠ[𝓝 z]
        modulatedIntervalMoment μ a b s χ u k := ((show ∀ᶠ w in 𝓝 z, w ∈ D from hD.mem_nhds hz)).mono fun _ hw => ih hw
    rw [he.deriv_eq]
    exact (hv k z hz).deriv

/-- In the open region where all moments exist, the zeroth moment is
holomorphic and its complex derivatives are the corresponding moments. -/
theorem modulatedIntervalMoment_analytic (a b s : ℝ) {U : Set ℝ}
    (hU : IsOpen U) (χ : PontryaginDual K)
    (u : lpTwoRadialSupport μ (stripMeasure a b s) U) (B : WithTop ℝ)
    (hKer : ∀ w : ℂ, (w.re : WithTop ℝ) < B → ∀ k : ℕ,
      MemLp (U.indicator (mellinEvaluationKernel k w)) 2 (stripMeasure (-a) (-b) (-s)))
    (k : ℕ) {z : ℂ} (hz : (z.re : WithTop ℝ) < B) :
    AnalyticAt ℂ (modulatedIntervalMoment μ a b s χ u 0) z ∧
      iteratedDeriv k (modulatedIntervalMoment μ a b s χ u 0) z =
        modulatedIntervalMoment μ a b s χ u k z := by
  let J : Set ℝ := {t | (t : WithTop ℝ) < B}
  have hJ : IsOpen J := by
    cases B with
    | top => simp [J]
    | coe B =>
      rw [show J = Iio B from Set.ext fun _ => WithTop.coe_lt_coe]
      exact isOpen_Iio
  exact modulatedIntervalMoment_analyticOnAbscissae μ a b s hU χ u hJ hKer k hz

/-- Every compact-interval weighted class has a holomorphic character Mellin
transform on the open strip, with the logarithmic moments as its derivatives. -/
theorem modulatedInterval_fullMellin_analytic (a b s : ℝ) (hs : 0 ≤ s)
    (χ : PontryaginDual K) (f : Lp ℂ 2 (μ.prod (stripMeasure a b s)))
    (k : ℕ) {z : ℂ} (hz : z.re ∈ Ioo a b) :
    let u : lpTwoRadialSupport μ (stripMeasure a b s) univ :=
      ⟨f, by change (∀ᵐ p ∂μ.prod (stripMeasure a b s), p.2 ∉ univ → f p = 0); simp⟩
    AnalyticAt ℂ (modulatedIntervalMoment μ a b s χ u 0) z ∧
      iteratedDeriv k (modulatedIntervalMoment μ a b s χ u 0) z =
        modulatedIntervalMoment μ a b s χ u k z := by
  dsimp only
  refine modulatedIntervalMoment_analyticOnAbscissae μ a b s isOpen_univ χ _
    isOpen_Ioo (fun w hw n => ?_) k hz
  rw [indicator_univ]
  exact (mellinEvaluationKernel_memLp_iff hw.1.le hw.2.le hs n).mpr (Or.inl hw)

/-- The bounded evaluation as a functional on the completed Hilbert tensor
of the radial analytic completion and the compact angular factor. -/
theorem modulatedIntervalTensor_mellinMoment (a b s : ℝ) {U : Set ℝ} (hU : IsOpen U)
    (χ : PontryaginDual K) (k : ℕ) (z : ℂ)
    (hg : MemLp (U.indicator (mellinEvaluationKernel k z)) 2 (stripMeasure (-a) (-b) (-s))) :
    ∃! L : StrongDual ℂ (UniformSpace.Completion
      (Lp ℂ 2 μ ⊗[ℂ] supportedSobolevCompletion a b s U)),
      ∀ v,
        let u := modulatedIntervalTensorEquiv μ a b s hU v
        let F (p : K × ℝ) := (χ p.1 : ℂ) * u.val p * mellinEvaluationKernel k z p.2
        Integrable F (μ.prod RadialHaar) ∧ L v = modulatedIntervalMoment μ a b s χ u k z := by
  obtain ⟨Λ, hΛ, _⟩ := modulatedInterval_mellinMoment_of_kernel μ a b s hU χ k z hg
  let T := modulatedIntervalTensorEquiv μ a b s hU
  refine ⟨Λ.comp T.toContinuousLinearEquiv.toContinuousLinearMap, fun v => hΛ (T v), ?_⟩
  intro Q hQ
  ext v
  exact (hQ v).2.trans (hΛ (T v)).2.symm

private theorem compactInterval_evaluationKernel {a b s c : ℝ} (hc : c ≤ 0) (hs : 0 ≤ s)
    (k : ℕ) {z : ℂ} (hz : z.re ≤ b) (h : z.re < b ∨ 2 * (k : ℝ) + 1 < s) :
    MemLp ((Ioi c).indicator (mellinEvaluationKernel k z)) 2 (stripMeasure (-a) (-b) (-s)) :=
  (supportedMellinEvaluation_memLp_iff a b s isOpen_Ioi k z).mp
    ((hardySobolev_cutoff_mellinEvaluation_exists_iff hc hz hs k).mpr h)

private theorem rightInterval_evaluationKernel (a s c : ℝ) (k : ℕ) (z : ℂ) :
    MemLp ((Ioo c 0).indicator (mellinEvaluationKernel k z)) 2 (stripMeasure (-a) (-a) (-s)) :=
  (supportedMellinEvaluation_memLp_iff a a s isOpen_Ioo k z).mp
    (hardySobolev_right_cutoff_mellinEvaluation a s c k z)

/-- The finite upper-endpoint cases of Corollary 9.2.2.12. A compact base
uses its given two endpoints and cutoff. A left half-line uses the singleton
endpoint weight with cutoff zero. At a distinct lower endpoint all orders
remain bounded, while the upper endpoint requires the strict condition. -/
theorem modulatedInterval_upperEndpoint_evaluation {a b s c : ℝ}
    (hc : c ≤ 0) (hs : 0 ≤ s) (χ : PontryaginDual K) (k : ℕ) {z : ℂ} (hz : z.re ≤ b)
    (h : z.re < b ∨ 2 * (k : ℝ) + 1 < s) :
    (∃! L : StrongDual ℂ (UniformSpace.Completion
      (Lp ℂ 2 μ ⊗[ℂ] supportedSobolevCompletion a b s (Ioi c))),
      ∀ v,
        let u := modulatedIntervalTensorEquiv μ a b s isOpen_Ioi v
        let F (p : K × ℝ) := (χ p.1 : ℂ) * u.val p * mellinEvaluationKernel k z p.2
        Integrable F (μ.prod RadialHaar) ∧ L v = modulatedIntervalMoment μ a b s χ u k z) ∧
    (z.re < b → ∀ u : lpTwoRadialSupport μ (stripMeasure a b s) (Ioi c),
      AnalyticAt ℂ (modulatedIntervalMoment μ a b s χ u 0) z ∧
      iteratedDeriv k (modulatedIntervalMoment μ a b s χ u 0) z =
        modulatedIntervalMoment μ a b s χ u k z) := by
  refine ⟨modulatedIntervalTensor_mellinMoment μ a b s isOpen_Ioi χ k z
    (compactInterval_evaluationKernel hc hs k hz h), ?_⟩
  intro hz' u
  exact modulatedIntervalMoment_analytic μ a b s isOpen_Ioi χ u b
    (fun w hw n => compactInterval_evaluationKernel hc hs n
      (WithTop.coe_lt_coe.mp hw).le (Or.inl (WithTop.coe_lt_coe.mp hw))) k
    (WithTop.coe_lt_coe.mpr hz')

/-- A finite lower cutoff makes the right half-line case of 9.2.2.12
bounded in logarithmic coordinates. Every moment is a bounded functional
on the stated Hilbert tensor, and the zeroth moment is entire. -/
theorem modulatedInterval_rightHalfLine_evaluation (a s c : ℝ) (χ : PontryaginDual K)
    (k : ℕ) (z : ℂ) :
    (∃! L : StrongDual ℂ (UniformSpace.Completion
      (Lp ℂ 2 μ ⊗[ℂ] supportedSobolevCompletion a a s (Ioo c 0))),
      ∀ v,
        let u := modulatedIntervalTensorEquiv μ a a s isOpen_Ioo v
        let F (p : K × ℝ) := (χ p.1 : ℂ) * u.val p * mellinEvaluationKernel k z p.2
        Integrable F (μ.prod RadialHaar) ∧ L v = modulatedIntervalMoment μ a a s χ u k z) ∧
    (∀ u : lpTwoRadialSupport μ (stripMeasure a a s) (Ioo c 0),
      AnalyticAt ℂ (modulatedIntervalMoment μ a a s χ u 0) z ∧
      iteratedDeriv k (modulatedIntervalMoment μ a a s χ u 0) z =
        modulatedIntervalMoment μ a a s χ u k z) := by
  refine ⟨modulatedIntervalTensor_mellinMoment μ a a s isOpen_Ioo χ k z
    (rightInterval_evaluationKernel a s c k z), fun u => ?_⟩
  exact modulatedIntervalMoment_analytic μ a a s isOpen_Ioo χ u ⊤
    (fun w _ n => rightInterval_evaluationKernel a s c n w) k (WithTop.coe_lt_top _)


omit [BorelSpace K] in
private theorem modulatedIntervalMoment_onProductTest (a b s : ℝ) {U : Set ℝ}
    (χ : PontryaginDual K) (k : ℕ) (z : ℂ) (v : Lp ℂ 2 μ)
    (f : PositiveRealExponentialDecay univ) (hf : ∀ x ∉ U, f.val x = 0)
    (u : lpTwoRadialSupport μ (stripMeasure a b s) U)
    (hu : u.val = lpTwoProduct v (supportedSobolevTest a b s U f hf).val) :
    modulatedIntervalMoment μ a b s χ u k z =
      (∫ j, (χ j : ℂ) * v j ∂μ) * iteratedDeriv k (mellin fun t => f.val (Real.log t)) z := by
  let w := supportedSobolevTest a b s U f hf
  have hProd : (u.val : K × ℝ → ℂ) =ᵐ[μ.prod RadialHaar] fun p => v p.1 * w.val p.2 :=
    (weightedProd_measure_ac μ a b s).ae_le (hu.symm ▸ lpTwoProduct_ae v w.val)
  have hRadial : (w.val : ℝ → ℂ) =ᵐ[RadialHaar] f.val :=
    (radial_measure_ac a b s).ae_le (stripSobolevTest_ae univ ⟨a, mem_univ a⟩ ⟨b, mem_univ b⟩ s f)
  have hRaw : (fun p : K × ℝ => (χ p.1 : ℂ) * u.val p * mellinEvaluationKernel k z p.2)
      =ᵐ[μ.prod RadialHaar]
        fun p => ((χ p.1 : ℂ) * v p.1) * (f.val p.2 * mellinEvaluationKernel k z p.2) := by
    filter_upwards [hProd,
      (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := RadialHaar)).ae hRadial] with p hp hx
    change w.val p.2 = f.val p.2 at hx
    rw [hp, hx]
    ring
  rw [modulatedIntervalMoment, integral_congr_ae hRaw,
    integral_prod_mul (fun j => (χ j : ℂ) * v j) (fun x => f.val x * mellinEvaluationKernel k z x),
    mellinEvaluation_test_integral]

omit [BorelSpace K] in
/-- On a separated test, the functional's moment is the angular character
coefficient times the actual derivative of the scalar test's Mellin transform. -/
theorem modulatedIntervalTensorMoment_onSeparated (a b s : ℝ) {U : Set ℝ}
    (hU : IsOpen U) (χ : PontryaginDual K) (k : ℕ) (z : ℂ)
    (v : Lp ℂ 2 μ) (f : PositiveRealExponentialDecay univ) (hf : ∀ x ∉ U, f.val x = 0) :
    let W := Lp ℂ 2 μ ⊗[ℂ] supportedSobolevCompletion a b s U
    let t : UniformSpace.Completion W := (v ⊗ₜ[ℂ] supportedSobolevTest a b s U f hf : W)
    modulatedIntervalMoment μ a b s χ (modulatedIntervalTensorEquiv μ a b s hU t) k z =
      (∫ j, (χ j : ℂ) * v j ∂μ) * iteratedDeriv k (mellin fun t => f.val (Real.log t)) z := by
  intro W t
  exact modulatedIntervalMoment_onProductTest μ a b s χ k z v f hf _
    (modulatedIntervalTensorEquiv_tmul μ a b s hU v _)

private theorem exists_unitCharacterTest [IsProbabilityMeasure μ] (χ : PontryaginDual K) :
    ∃ v : Lp ℂ 2 μ, (∫ j, (χ j : ℂ) * v j ∂μ) = 1 := by
  let ψ (j : K) : ℂ := ((χ j)⁻¹ : Circle)
  have hψ : MemLp ψ 2 μ := by
    have hψcont : Continuous ψ :=
      continuous_subtype_val.comp (χ⁻¹).continuous
    exact MemLp.of_bound hψcont.aestronglyMeasurable 1
      (.of_forall fun j => (Circle.norm_coe ((χ j)⁻¹)).le)
  let v := hψ.toLp ψ
  refine ⟨v, ?_⟩
  have he : (fun j => (χ j : ℂ) * v j) =ᵐ[μ] fun _ => (1 : ℂ) := by
    filter_upwards [hψ.coeFn_toLp] with j hj
    change v j = ψ j at hj
    rw [hj, show ψ j = (((χ j)⁻¹ : Circle) : ℂ) from rfl,
      ← Circle.coe_mul, mul_inv_cancel, Circle.coe_one]
  rw [integral_congr_ae he]
  simp

/-- The character-moment representation on the product exists exactly when
the scalar reciprocal-weight kernel is square integrable. The reverse
direction tests a pure tensor with the inverse of that same character. -/
theorem modulatedInterval_mellinMoment_iff [IsProbabilityMeasure μ] (a b s : ℝ)
    {U : Set ℝ} (hU : IsOpen U) (χ : PontryaginDual K) (k : ℕ) (z : ℂ) :
    (∃ L : StrongDual ℂ (lpTwoRadialSupport μ (stripMeasure a b s) U),
      ∀ u : lpTwoRadialSupport μ (stripMeasure a b s) U,
        L u = modulatedIntervalMoment μ a b s χ u k z) ↔
    MemLp (U.indicator (mellinEvaluationKernel k z)) 2 (stripMeasure (-a) (-b) (-s)) := by
  refine ⟨?_, fun h => ?_⟩
  · rintro ⟨L, hL⟩
    apply (supportedMellinEvaluation_memLp_iff a b s hU k z).mp
    obtain ⟨v, hχv⟩ := exists_unitCharacterTest μ χ
    let J := (modulatedIntervalTensorEmbedding μ a b s hU).toContinuousLinearMap.comp
      (TensorProduct.mkL ℂ (Lp ℂ 2 μ) (supportedSobolevCompletion a b s U) v)
    refine ⟨L.comp J, fun f hf => ?_⟩
    let w := supportedSobolevTest a b s U f hf
    rw [show (L.comp J) w = L (J w) from rfl, hL]
    have hw : (J w).val = lpTwoProduct v w.val := modulatedIntervalTensorEmbedding_tmul μ a b s hU v w
    rw [modulatedIntervalMoment_onProductTest μ a b s χ k z v f hf (J w) hw, hχv, one_mul]
  · obtain ⟨L, hL, _⟩ := modulatedInterval_mellinMoment_of_kernel μ a b s hU χ k z h
    exact ⟨L, fun u => (hL u).2⟩


/-- Test-level sharpness on the Hilbert tensor. Agreement on separated
analytic tests alone forces the reciprocal-weight criterion. -/
theorem modulatedIntervalTensor_analyticEvaluation_iff [IsProbabilityMeasure μ] (a b s : ℝ)
    {U : Set ℝ} (hU : IsOpen U) (χ : PontryaginDual K) (k : ℕ) (z : ℂ) :
    let W := Lp ℂ 2 μ ⊗[ℂ] supportedSobolevCompletion a b s U
    (∃ L : StrongDual ℂ (UniformSpace.Completion W),
      ∀ (v : Lp ℂ 2 μ) (f : PositiveRealExponentialDecay univ) (hf : ∀ x ∉ U, f.val x = 0),
        L ((v ⊗ₜ[ℂ] supportedSobolevTest a b s U f hf : W) : UniformSpace.Completion W) =
          (∫ j, (χ j : ℂ) * v j ∂μ) * iteratedDeriv k (mellin fun t => f.val (Real.log t)) z) ↔
    MemLp (U.indicator (mellinEvaluationKernel k z)) 2 (stripMeasure (-a) (-b) (-s)) := by
  intro W
  constructor
  · rintro ⟨L, hL⟩
    apply (supportedMellinEvaluation_memLp_iff a b s hU k z).mp
    obtain ⟨v, hv⟩ := exists_unitCharacterTest μ χ
    let J : supportedSobolevCompletion a b s U →L[ℂ] UniformSpace.Completion W :=
      UniformSpace.Completion.toComplL.comp
        (TensorProduct.mkL ℂ (Lp ℂ 2 μ) (supportedSobolevCompletion a b s U) v)
    refine ⟨L.comp J, fun f hf => ?_⟩
    change L ((v ⊗ₜ[ℂ] supportedSobolevTest a b s U f hf : W) : UniformSpace.Completion W) = _
    simpa only [hv, one_mul] using hL v f hf
  · intro h
    obtain ⟨L, hL, _⟩ := modulatedIntervalTensor_mellinMoment μ a b s hU χ k z h
    refine ⟨L, fun v f hf => ?_⟩
    exact ((hL _).2).trans (modulatedIntervalTensorMoment_onSeparated μ a b s hU χ k z v f hf)

/-- At a finite upper endpoint, each compact character has exactly the
strict range of derivative orders, in the actual integral representation. -/
theorem modulatedInterval_upperEndpoint_iff [IsProbabilityMeasure μ] {a b s c : ℝ}
    (hc : c ≤ 0) (hs : 0 ≤ s) (χ : PontryaginDual K) (k : ℕ) {z : ℂ} (hz : z.re ≤ b) :
    (∃ L : StrongDual ℂ (lpTwoRadialSupport μ (stripMeasure a b s) (Ioi c)),
      ∀ u : lpTwoRadialSupport μ (stripMeasure a b s) (Ioi c),
        L u = modulatedIntervalMoment μ a b s χ u k z) ↔
    z.re < b ∨ 2 * (k : ℝ) + 1 < s := by
  rw [modulatedInterval_mellinMoment_iff μ a b s isOpen_Ioi χ k z,
    ← supportedMellinEvaluation_memLp_iff a b s isOpen_Ioi k z,
    hardySobolev_cutoff_mellinEvaluation_exists_iff hc hz hs k]

/-- A nonempty closed interval of real numbers is compact, one of the two
closed rays, or the whole line. -/
theorem closedRealInterval_cases {I : Set ℝ} (hne : I.Nonempty)
    (hc : IsClosed I) (hI : I.OrdConnected) :
    (∃ a b : ℝ, a ≤ b ∧ I = Icc a b) ∨
      (∃ a : ℝ, I = Ici a) ∨ (∃ b : ℝ, I = Iic b) ∨ I = univ := by
  by_cases hl : BddBelow I
  · have ha := hc.csInf_mem hne hl
    by_cases hr : BddAbove I
    · have hb := hc.csSup_mem hne hr
      exact Or.inl ⟨sInf I, sSup I, csInf_le hl hb,
        subset_antisymm (subset_Icc_csInf_csSup hl hr) (hI.out ha hb)⟩
    · refine Or.inr (Or.inl ⟨sInf I, subset_antisymm (fun x hx => csInf_le hl hx) ?_⟩)
      intro x hx
      obtain ⟨y, hy, hxy⟩ := not_bddAbove_iff.mp hr x
      exact hI.out ha hy ⟨hx, hxy.le⟩
  · by_cases hr : BddAbove I
    · have hb := hc.csSup_mem hne hr
      refine Or.inr (Or.inr (Or.inl ⟨sSup I, subset_antisymm (fun x hx => le_csSup hr hx) ?_⟩))
      intro x hx
      obtain ⟨y, hy, hyx⟩ := not_bddBelow_iff.mp hl x
      exact hI.out hy hb ⟨hyx.le, hx⟩
    · refine Or.inr (Or.inr (Or.inr (eq_univ_of_forall ?_)))
      intro x
      obtain ⟨y, hy, hyx⟩ := not_bddBelow_iff.mp hl x
      obtain ⟨z, hz, hxz⟩ := not_bddAbove_iff.mp hr x
      exact hI.out hy hz ⟨hyx.le, hxz.le⟩

omit [TopologicalSpace K] [BorelSpace K] [CommGroup K] [IsFiniteMeasure μ] in
/-- For the whole-real base the finite-norm domain is zero in split Haar
coordinates, since the two half-line conditions remove opposite rays. -/
theorem modulatedInterval_univ_finite_iff (s : ℝ) {f : K × ℝ → ℂ}
    (hf : Measurable f) :
    hardySobolevIntervalENorm (μ.prod RadialHaar) Prod.snd (univ : Set ℝ) s f ≠ ⊤ ↔
      f =ᵐ[μ.prod RadialHaar] (0 : K × ℝ → ℂ) := by
  constructor
  · intro hn
    have hm (S : Set ℝ) : hardySobolevIntervalENorm (μ.prod RadialHaar) Prod.snd S s f ≤
        hardySobolevIntervalENorm (μ.prod RadialHaar) Prod.snd (univ : Set ℝ) s f :=
      iSup₂_le fun b c => le_iSup₂_of_le
        ⟨(b : ℝ), mem_univ (b : ℝ)⟩ ⟨(c : ℝ), mem_univ (c : ℝ)⟩ le_rfl
    have hleft : ∀ᵐ p ∂μ.prod RadialHaar, p.2 < 0 → f p = 0 := by
      by_contra h
      have hbad : μ.prod RadialHaar {p : K × ℝ | p.2 < 0 ∧ f p ≠ 0} ≠ 0 := by
        simpa only [ae_iff, Set.compl_ofPred, Classical.not_imp] using h
      exact (ne_top_of_le_ne_top hn (hm (Iic 0)))
        (hardySobolevIntervalENorm_Iic_eq_top (μ.prod RadialHaar) measurable_snd hf hbad 0 s)
    have hright : ∀ᵐ p ∂μ.prod RadialHaar, 0 < p.2 → f p = 0 := by
      by_contra h
      have hbad : μ.prod RadialHaar {p : K × ℝ | 0 < p.2 ∧ f p ≠ 0} ≠ 0 := by
        simpa only [ae_iff, Set.compl_ofPred, Classical.not_imp] using h
      exact (ne_top_of_le_ne_top hn (hm (Ici 0)))
        (hardySobolevIntervalENorm_Ici_eq_top (μ.prod RadialHaar) measurable_snd hf hbad 0 s)
    have hne := (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := RadialHaar)).ae
      ((volume : Measure ℝ).ae_ne (0 : ℝ))
    filter_upwards [hleft, hright, hne] with p hl hr hp
    exact (lt_or_gt_of_ne hp).elim hl hr
  · intro h
    have he (a b : ℝ) : eLpNorm f 2 (hardySobolevMeasure (μ.prod RadialHaar) Prod.snd a b s) = 0 := by
      unfold hardySobolevMeasure
      have h' : f =ᵐ[(μ.prod RadialHaar).withDensity
          (fun p : K × ℝ => ENNReal.ofReal (hardySobolevWeight a b s p.2))] (0 : K × ℝ → ℂ) :=
        (withDensity_absolutelyContinuous (μ.prod RadialHaar) _).ae_le h
      exact (eLpNorm_congr_ae h').trans eLpNorm_zero
    simp [hardySobolevIntervalENorm, he]

/-- The bounded moments at integrable upper-endpoint orders are the actual
limits from the analytic region. -/
theorem modulatedIntervalMoment_continuousOn_closedHalfPlane {a b s c : ℝ}
    (hc : c ≤ 0) (hs : 0 ≤ s) {k : ℕ} (hk : 2 * (k : ℝ) + 1 < s)
    (χ : PontryaginDual K) (u : lpTwoRadialSupport μ (stripMeasure a b s) (Ioi c)) :
    ContinuousOn (modulatedIntervalMoment μ a b s χ u k) (Complex.re ⁻¹' Iic b) := by
  let v := modulatedIntervalCoefficient μ a b s isOpen_Ioi χ u
  apply (cutoffMellinIntegral_continuousOn_closedHalfPlane hc hs hk v).congr
  intro z hz
  let F (p : K × ℝ) := (χ p.1 : ℂ) * u.val p * mellinEvaluationKernel k z p.2
  have hi := productMoment_integrable μ a b s measurableSet_Ioi χ k z
    (compactInterval_evaluationKernel hc hs k hz (Or.inr hk)) u
  change (∫ p, F p ∂μ.prod RadialHaar) = ∫ x, v.val x * mellinEvaluationKernel k z x
  rw [integral_prod_symm F hi]
  apply integral_congr_ae
  filter_upwards [modulatedIntervalCoefficient_ae μ a b s isOpen_Ioi χ u] with x hu
  change v.val x = _ at hu
  rw [show (∫ j, F (j, x) ∂μ) =
    (∫ j, (χ j : ℂ) * u.val (j, x) ∂μ) * mellinEvaluationKernel k z x from
    by dsimp only [F]; exact integral_mul_const _ _, ← hu]

omit [TopologicalSpace K] [BorelSpace K] [CommGroup K] [IsFiniteMeasure μ] in
theorem modulatedInterval_prod_weightedMeasure {a b s : ℝ} (hab : a ≤ b) :
    μ.prod (stripMeasure a b s) = hardySobolevMeasure (μ.prod RadialHaar)
      (Prod.snd : K × ℝ → ℝ) a b s := by
  rw [stripMeasure_prod_amplitude, amplitudeMeasure, hardySobolevMeasure]
  simp only [stripSobolevAmplitude_sq hab]

omit [TopologicalSpace K] [BorelSpace K] [CommGroup K] [IsFiniteMeasure μ] in
/-- On each unbounded half-line, finiteness forces the stated half-line
support and on that support the norm is exactly the finite-endpoint norm. -/
theorem modulatedInterval_halfLine_finite_iff (b s : ℝ) {f : K × ℝ → ℂ} (hf : Measurable f) :
    (hardySobolevIntervalENorm (μ.prod RadialHaar) Prod.snd (Ici b) s f ≠ ⊤ ↔
      (∀ᵐ p ∂μ.prod RadialHaar, 0 < p.2 → f p = 0) ∧ MemLp f 2 (μ.prod (stripMeasure b b s))) ∧
    (hardySobolevIntervalENorm (μ.prod RadialHaar) Prod.snd (Iic b) s f ≠ ⊤ ↔
      (∀ᵐ p ∂μ.prod RadialHaar, p.2 < 0 → f p = 0) ∧ MemLp f 2 (μ.prod (stripMeasure b b s))) := by
  have he : μ.prod (stripMeasure b b s) = hardySobolevMeasure (μ.prod RadialHaar) Prod.snd b b s :=
    modulatedInterval_prod_weightedMeasure μ le_rfl
  let W := μ.prod (stripMeasure b b s)
  have hmem : MemLp f 2 W ↔ eLpNorm f 2 W ≠ ⊤ :=
    ⟨fun h => h.eLpNorm_lt_top.ne, fun h => ⟨hf.aestronglyMeasurable, h.lt_top⟩⟩
  constructor
  · constructor
    · intro h
      have hz : ∀ᵐ p ∂μ.prod RadialHaar, 0 < p.2 → f p = 0 := by
        by_contra hn
        exact h (hardySobolevIntervalENorm_Ici_eq_top (μ.prod RadialHaar) measurable_snd hf
          (by simpa only [ae_iff, Set.compl_ofPred, Classical.not_imp] using hn) b s)
      exact ⟨hz, hmem.mpr (by rwa [show W = _ from he,
        ← hardySobolevIntervalENorm_Ici_of_ae (μ.prod RadialHaar) measurable_snd hf hz b s])⟩
    · rintro ⟨hz, h⟩
      rw [hardySobolevIntervalENorm_Ici_of_ae (μ.prod RadialHaar) measurable_snd hf hz b s, ← he]
      exact (hmem.mp h)
  · constructor
    · intro h
      have hz : ∀ᵐ p ∂μ.prod RadialHaar, p.2 < 0 → f p = 0 := by
        by_contra hn
        exact h (hardySobolevIntervalENorm_Iic_eq_top (μ.prod RadialHaar) measurable_snd hf
          (by simpa only [ae_iff, Set.compl_ofPred, Classical.not_imp] using hn) b s)
      exact ⟨hz, hmem.mpr (by rwa [show W = _ from he,
        ← hardySobolevIntervalENorm_Iic_of_ae (μ.prod RadialHaar) measurable_snd hf hz b s])⟩
    · rintro ⟨hz, h⟩
      rw [hardySobolevIntervalENorm_Iic_of_ae (μ.prod RadialHaar) measurable_snd hf hz b s, ← he]
      exact (hmem.mp h)

end
end Masullo
