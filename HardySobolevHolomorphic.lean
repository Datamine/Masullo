import HardySobolevPaleyConverse

open Filter Function MeasureTheory Set Topology
open scoped ENNReal

namespace Masullo

noncomputable section

/-- The logarithmic Mellin integral of a weighted cutoff class. -/
def cutoffMellinIntegral (f : ℝ → ℂ) (k : ℕ) (z : ℂ) : ℂ :=
  ∫ x : ℝ, f x * mellinEvaluationKernel k z x

theorem mellinEvaluationKernel_norm (k : ℕ) (z : ℂ) (x : ℝ) :
    ‖mellinEvaluationKernel k z x‖ = Real.exp (z.re * x) * ‖x‖ ^ k := by
  rw [mellinEvaluationKernel, norm_mul, norm_pow, Complex.norm_real, Complex.norm_exp,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]

/-- Differentiate the actual Mellin integral on the open half-plane using
the integrable endpoint moments on a bracket around the point. -/
theorem cutoffMellinIntegral_hasDerivAt {a b s c : ℝ} (hc : c ≤ 0) (hs : 0 ≤ s)
    (u : supportedSobolevCompletion a b s (Ioi c)) (k : ℕ) {z : ℂ} (hz : z.re < b) :
    HasDerivAt (cutoffMellinIntegral u.val k) (cutoffMellinIntegral u.val (k + 1) z) z := by
  let l := z.re - 1
  let r := (z.re + b) / 2
  let U := Complex.re ⁻¹' Ioo l r
  have hl : l < z.re := by dsimp [l]; linarith
  have hr : z.re < r := by dsimp [r]; linarith
  have hrb : r < b := by dsimp [r]; linarith
  have hlb : l < b := hl.trans hz
  have hU : U ∈ 𝓝 z := (isOpen_Ioo.preimage Complex.continuous_re).mem_nhds ⟨hl, hr⟩
  let K (n : ℕ) (w : ℂ) (x : ℝ) := u.val x * mellinEvaluationKernel n w x
  have hI (n : ℕ) (w : ℂ) (hw : w.re < b) : Integrable (K n w) :=
    cutoffSobolev_mellinMoment_integrable hc hs u hw n
  have hD (w : ℂ) (x : ℝ) :
      HasDerivAt (fun ζ => K k ζ x) (K (k + 1) w x) w := by
    have hd := (((hasDerivAt_id' w).mul_const (x : ℂ)).cexp.mul_const ((x : ℂ) ^ k)).const_mul (u.val x)
    convert hd using 1
    all_goals first | rfl | (simp only [K, mellinEvaluationKernel, pow_succ]; ring)
  let B (x : ℝ) := ‖K (k + 1) (l : ℂ) x‖ + ‖K (k + 1) (r : ℂ) x‖
  have hB : Integrable B := ((hI _ _ hlb).norm).add ((hI _ _ hrb).norm)
  have hbound (x : ℝ) (w : ℂ) (hw : w ∈ U) : ‖K (k + 1) w x‖ ≤ B x := by
    have hwl : l ≤ w.re := (show l < w.re from hw.1).le
    have hwr : w.re ≤ r := (show w.re < r from hw.2).le
    simp only [K, B, norm_mul, mellinEvaluationKernel_norm, Complex.ofReal_re]
    by_cases hx : 0 ≤ x
    · have he : Real.exp (w.re * x) ≤ Real.exp (r * x) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hwr hx)
      exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right he (by positivity))
        (norm_nonneg _)).trans (le_add_of_nonneg_left (by positivity))
    · have he : Real.exp (w.re * x) ≤ Real.exp (l * x) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_right hwl (le_of_not_ge hx))
      exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right he (by positivity))
        (norm_nonneg _)).trans (le_add_of_nonneg_right (by positivity))
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le hU
    ((show ∀ᶠ w in 𝓝 z, w ∈ U from hU).mono fun w hw =>
      (hI _ w ((show w.re < r from hw.2).trans hrb)).aestronglyMeasurable)
    (hI _ _ hz) (hI _ _ hz).aestronglyMeasurable
    (.of_forall fun x w hw => hbound x w hw) hB (.of_forall fun x w _ => hD w x)).2

theorem cutoffMellinIntegral_differentiableOn {a b s c : ℝ} (hc : c ≤ 0) (hs : 0 ≤ s)
    (u : supportedSobolevCompletion a b s (Ioi c)) :
    DifferentiableOn ℂ (cutoffMellinIntegral u.val 0) (Complex.re ⁻¹' Iio b) :=
  fun _ hz => (cutoffMellinIntegral_hasDerivAt hc hs u 0 hz).differentiableAt.differentiableWithinAt

theorem iteratedDeriv_cutoffMellinIntegral {a b s c : ℝ} (hc : c ≤ 0) (hs : 0 ≤ s)
    (u : supportedSobolevCompletion a b s (Ioi c)) (k : ℕ) {z : ℂ} (hz : z.re < b) :
    iteratedDeriv k (cutoffMellinIntegral u.val 0) z = cutoffMellinIntegral u.val k z := by
  induction k generalizing z with
  | zero => rfl
  | succ k ih =>
    rw [iteratedDeriv_succ]
    have hn : ∀ᶠ w in 𝓝 z, w.re < b :=
      (isOpen_Iio.preimage Complex.continuous_re).mem_nhds hz
    have hEq : iteratedDeriv k (cutoffMellinIntegral u.val 0) =ᶠ[𝓝 z]
        cutoffMellinIntegral u.val k := hn.mono fun _ hw => ih hw
    rw [hEq.deriv_eq]
    exact (cutoffMellinIntegral_hasDerivAt hc hs u k hz).deriv


/-- At integrable endpoint orders, the actual Mellin integral extends
continuously to the entire closed half-plane. -/
theorem cutoffMellinIntegral_continuousOn_closedHalfPlane {a b s c : ℝ} (hc : c ≤ 0)
    (hs : 0 ≤ s) {k : ℕ} (hk : 2 * (k : ℝ) + 1 < s)
    (u : supportedSobolevCompletion a b s (Ioi c)) :
    ContinuousOn (cutoffMellinIntegral u.val k) (Complex.re ⁻¹' Iic b) := by
  intro z hz
  let D := Complex.re ⁻¹' Iic b
  let K (w : ℂ) (x : ℝ) := u.val x * mellinEvaluationKernel k w x
  let r := z.re - 1
  have hrz : r < z.re := by dsimp [r]; linarith
  have hzb : z.re ≤ b := hz
  have hrb := hrz.trans_le hzb
  let B (x : ℝ) := ‖K (r : ℂ) x‖ + ‖K (b : ℂ) x‖
  have hi (w : ℂ) (hw : w.re ≤ b) : Integrable (K w) :=
    ((cutoffSobolev_mellinMoment_functional_of_le hc hs hw k (Or.inr hk)).choose_spec u).1
  have hB : Integrable B := (hi (r : ℂ) hrb.le).norm.add (hi (b : ℂ) le_rfl).norm
  have hre : ∀ᶠ w in 𝓝[D] z, r < w.re :=
    mem_nhdsWithin_of_mem_nhds ((isOpen_Ioi.preimage Complex.continuous_re).mem_nhds hrz)
  change Tendsto (fun w : ℂ => ∫ x, K w x) (𝓝[D] z) (𝓝 (∫ x, K z x))
  apply MeasureTheory.tendsto_integral_filter_of_dominated_convergence B
  · exact (show ∀ᶠ w in 𝓝[D] z, w ∈ D from self_mem_nhdsWithin).mono
      fun w hw => (hi w hw).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin (s := D) (a := z), hre] with w hwb hwr
    apply Eventually.of_forall
    intro x
    simp only [K, B, norm_mul, mellinEvaluationKernel_norm, Complex.ofReal_re]
    by_cases hx : 0 ≤ x
    · have hle : Real.exp (w.re * x) ≤ Real.exp (b * x) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hwb hx)
      have h := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hle
        (pow_nonneg (norm_nonneg x) k)) (norm_nonneg (u.val x))
      exact h.trans (le_add_of_nonneg_left (by positivity))
    · have hle : Real.exp (w.re * x) ≤ Real.exp (r * x) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_right hwr.le (le_of_not_ge hx))
      have h := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hle
        (pow_nonneg (norm_nonneg x) k)) (norm_nonneg (u.val x))
      exact h.trans (le_add_of_nonneg_right (by positivity))
  · exact hB
  · exact .of_forall fun x =>
      (show Continuous (K · x) by dsimp [K, mellinEvaluationKernel]; fun_prop).continuousAt.continuousWithinAt

private theorem supportedLineEnergy_le {a b c r : ℝ} (hab : a ≤ b) (hr : r ≤ b) {N k : ℕ} (hk : k ≤ N)
    (f : PositiveRealExponentialDecay univ) (hf : ∀ x ∉ Ioi c, f.val x = 0) :
    mellinLineEnergy f k r ≤ (2 * Real.pi * Real.exp (2 * (r - b) * c)) *
      ‖supportedSobolevTest a b (2 * (N : ℝ)) (Ioi c) f hf‖ ^ 2 := by
  let J := (univ : Set ℝ)
  let s := 2 * (N : ℝ)
  let E (x : ℝ) := ‖f.val x‖ ^ 2 * hardySobolevWeight a b s x
  let Q (x : ℝ) := ‖f.val x‖ ^ 2 * (Real.exp (2 * r * x) * (x ^ 2) ^ k)
  have hbpow {x : ℝ} (hx : c ≤ x) :
      Real.exp (2 * r * x) ≤ Real.exp (2 * (r - b) * c) * Real.exp (2 * b * x) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonpos_left hx (show 2 * (r - b) ≤ 0 by linarith)
    linarith
  have hkpow (x : ℝ) : (x ^ 2) ^ k ≤ (1 + x ^ 2) ^ N :=
    (pow_le_pow_left₀ (sq_nonneg _) (le_add_of_nonneg_left zero_le_one) k).trans
      (pow_le_pow_right₀ (le_add_of_nonneg_right (sq_nonneg _)) hk)
  have hcompare (x : ℝ) : Q x ≤ Real.exp (2 * (r - b) * c) * E x := by
    by_cases hx : x ∈ Ioi c
    · have hx' : c ≤ x := (show c < x from hx).le
      dsimp only [Q, E, s, hardySobolevWeight]
      have hN : 2 * (N : ℝ) / 2 = (N : ℝ) := by ring
      rw [hN, Real.rpow_natCast]
      calc
        _ ≤ ‖f.val x‖ ^ 2 * ((Real.exp (2 * (r - b) * c) * Real.exp (2 * b * x)) *
            (1 + x ^ 2) ^ N) := by
          exact mul_le_mul_of_nonneg_left (mul_le_mul (hbpow hx') (hkpow x)
            (by positivity) (by positivity)) (sq_nonneg _)
        _ = Real.exp (2 * (r - b) * c) * (‖f.val x‖ ^ 2 *
            (Real.exp (2 * b * x) * (1 + x ^ 2) ^ N)) := by ring
        _ ≤ _ := by gcongr; exact le_max_right _ _
    · simp [Q, E, hf x hx]
  have hE := stripSobolevTest_energy J ⟨a, mem_univ a⟩ ⟨b, mem_univ b⟩ hab s f
  have hNorm := stripSobolevTest_norm J ⟨a, mem_univ a⟩ ⟨b, mem_univ b⟩ hab s f
  have henergy : ‖supportedSobolevTest a b s (Ioi c) f hf‖ ^ 2 = ∫ x, E x := by
    change ‖stripSobolevTest J ⟨a, mem_univ a⟩ ⟨b, mem_univ b⟩ s f‖ ^ 2 = _
    rw [← hNorm, hE.2, ENNReal.toReal_ofReal (Real.sqrt_nonneg _), Real.sq_sqrt]
    exact integral_nonneg fun x => mul_nonneg (sq_nonneg _) (hardySobolevWeight_nonneg ..)
  rw [henergy]
  have he : mellinLineEnergy f k r = (2 * Real.pi) * ∫ x, Q x :=
    (mellin_iteratedDeriv_line_energy f k r).2
  rw [he]
  have hi : (∫ x, Q x) ≤ Real.exp (2 * (r - b) * c) * ∫ x, E x := by
    rw [← integral_const_mul]
    exact integral_mono_of_nonneg (.of_forall fun _ => by dsimp [Q]; positivity)
      (hE.1.const_mul _) (.of_forall hcompare)
  exact (mul_le_mul_of_nonneg_left hi (show 0 ≤ 2 * Real.pi from by positivity)).trans_eq
    (mul_assoc _ _ _).symm


/-- Vertical traces of the actual holomorphic Mellin representative belong to
(L^2), with a bound in the completed source norm. -/
theorem cutoffMellinIntegral_line_bound_of_le {a b c r : ℝ} (hab : a ≤ b) (hc : c ≤ 0)
    (hr : r ≤ b) {N k : ℕ} (hk : k ≤ N) (hEval : r < b ∨ 2 * (k : ℝ) + 1 < 2 * (N : ℝ))
    (u : supportedSobolevCompletion a b (2 * (N : ℝ)) (Ioi c)) :
    let T (y : ℝ) := cutoffMellinIntegral u.val k (⟨r, y⟩ : ℂ)
    MemLp T 2 volume ∧
      (∫ y, ‖T y‖ ^ 2) ≤ (2 * Real.pi * Real.exp (2 * (r - b) * c)) * ‖u‖ ^ 2 := by
  intro T
  let s := 2 * (N : ℝ)
  let S := supportedSobolevCompletion a b s (Ioi c)
  let j (f : {f : PositiveRealExponentialDecay univ // ∀ x ∉ Ioi c, f.val x = 0}) : S :=
    supportedSobolevTest a b s (Ioi c) f.val f.property
  have hd : DenseRange j := supportedSobolevTest_denseRange a b s (Ioi c)
  obtain ⟨v, hv, hlim⟩ := mem_closure_iff_seq_limit.mp (hd u)
  choose f hf using hv
  let K := 2 * Real.pi * Real.exp (2 * (r - b) * c)
  let Tn (n : ℕ) (y : ℝ) := cutoffMellinIntegral (v n).val k (⟨r, y⟩ : ℂ)
  have hline : Continuous (fun y : ℝ => (⟨r, y⟩ : ℂ)) := by
    have he : (fun y : ℝ => (⟨r, y⟩ : ℂ)) = fun y : ℝ => (r : ℂ) + (y : ℂ) * Complex.I := by
      funext y
      apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
    rw [he]
    fun_prop
  have hcont (w : S) : Continuous fun y : ℝ => cutoffMellinIntegral w.val k (⟨r, y⟩ : ℂ) := by
    rcases hEval with hlt | horder
    · apply continuous_iff_continuousAt.mpr
      intro y
      exact ((cutoffMellinIntegral_hasDerivAt hc (by dsimp [s]; positivity) w k
        (z := (⟨r, y⟩ : ℂ)) hlt).continuousAt).comp hline.continuousAt
    · exact ((cutoffMellinIntegral_continuousOn_closedHalfPlane hc (by positivity)
        horder w).comp_continuous hline (fun _ => hr))
  have hTn (n : ℕ) (y : ℝ) : Tn n y =
      iteratedDeriv k (mellin fun t => (f n).val.val (Real.log t)) (⟨r, y⟩ : ℂ) := by
    rw [mellinEvaluation_test_integral]
    change (∫ x, (v n).val x * mellinEvaluationKernel k ⟨r, y⟩ x) = _
    rw [← hf n]
    have he := stripSobolevTest_ae univ ⟨a, mem_univ a⟩ ⟨b, mem_univ b⟩ s (f n).val
    have hac := absolutelyContinuous_amplitudeMeasure volume (stripSobolevAmplitude a b s)
      (stripSobolevAmplitude_continuous a b s).measurable (stripSobolevAmplitude_pos a b s)
    apply integral_congr_ae
    filter_upwards [hac.ae_le he] with x hx
    change (j (f n)).val x = (f n).val.val x at hx
    rw [hx]
  have hmem (n : ℕ) : MemLp (Tn n) 2 volume :=
    ((mellin_iteratedDeriv_line_energy (f n).val k r).1).ae_eq
      (.of_forall fun y => (hTn n y).symm)
  have hsq (n : ℕ) : Integrable (fun y => ‖Tn n y‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm (hmem n).aestronglyMeasurable).mp (hmem n)
  have hend (n : ℕ) : (∫ y, ‖Tn n y‖ ^ 2) ≤ K * ‖v n‖ ^ 2 := by
    simp_rw [hTn]
    rw [← hf n]
    exact supportedLineEnergy_le hab hr hk (f n).val (f n).property
  have ht (y : ℝ) : Tendsto (fun n => Tn n y) atTop (𝓝 (T y)) := by
    obtain ⟨L, hL⟩ := cutoffSobolev_mellinMoment_functional_of_le (a := a) (c := c)
      (s := s) hc (by dsimp [s]; positivity) (z := (⟨r, y⟩ : ℂ)) hr k hEval
    have h := L.continuous.continuousAt.tendsto.comp hlim
    simpa only [Function.comp_def, (hL _).2, Tn, T, cutoffMellinIntegral] using h
  have hFatou : (∫⁻ y, ENNReal.ofReal (‖T y‖ ^ 2)) ≤ ENNReal.ofReal (K * ‖u‖ ^ 2) := by
    have he (n : ℕ) : (∫⁻ y, ENNReal.ofReal (‖Tn n y‖ ^ 2)) ≤
        ENNReal.ofReal (K * ‖v n‖ ^ 2) := by
      rw [← ofReal_integral_eq_lintegral_ofReal (hsq n) (.of_forall fun _ => sq_nonneg _)]
      exact ENNReal.ofReal_le_ofReal (hend n)
    have hh : Tendsto (fun n => ENNReal.ofReal (K * ‖v n‖ ^ 2)) atTop
        (𝓝 (ENNReal.ofReal (K * ‖u‖ ^ 2))) :=
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp ((hlim.norm.pow 2).const_mul K)
    calc
      _ = ∫⁻ y, liminf (fun n => ENNReal.ofReal (‖Tn n y‖ ^ 2)) atTop := by
        apply lintegral_congr
        intro y
        exact (ENNReal.continuous_ofReal.continuousAt.tendsto.comp ((ht y).norm.pow 2)).liminf_eq.symm
      _ ≤ liminf (fun n => ∫⁻ y, ENNReal.ofReal (‖Tn n y‖ ^ 2)) atTop :=
        lintegral_liminf_le fun n => ((hcont (v n)).norm.pow 2).measurable.ennreal_ofReal
      _ ≤ _ := (liminf_le_liminf (.of_forall he)).trans_eq hh.liminf_eq
  have hI : Integrable (fun y => ‖T y‖ ^ 2) := by
    refine ⟨((hcont u).norm.pow 2).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (.of_forall fun _ => sq_nonneg _)]
    exact hFatou.trans_lt ENNReal.ofReal_lt_top
  refine ⟨(memLp_two_iff_integrable_sq_norm (hcont u).aestronglyMeasurable).mpr hI, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hI (.of_forall fun _ => sq_nonneg _)] at hFatou
  exact (ENNReal.ofReal_le_ofReal_iff (by dsimp [K]; positivity)).mp hFatou


/-- Every interior line has the completed Sobolev bound through order N. -/
theorem cutoffMellinIntegral_line_bound {a b c r : ℝ} (hab : a ≤ b) (hc : c ≤ 0)
    (hr : r < b) {N k : ℕ} (hk : k ≤ N)
    (u : supportedSobolevCompletion a b (2 * (N : ℝ)) (Ioi c)) :
    let T (y : ℝ) := cutoffMellinIntegral u.val k (⟨r, y⟩ : ℂ)
    MemLp T 2 volume ∧
      (∫ y, ‖T y‖ ^ 2) ≤ (2 * Real.pi * Real.exp (2 * (r - b) * c)) * ‖u‖ ^ 2 :=
  cutoffMellinIntegral_line_bound_of_le hab hc hr.le hk (Or.inl hr) u

/-- Endpoint moments of order strictly below N have square-integrable
representatives with the same estimate as the limiting interior lines. -/
theorem cutoffMellinIntegral_endpoint_line_bound {a b c : ℝ} (hab : a ≤ b) (hc : c ≤ 0)
    {N k : ℕ} (hk : k < N)
    (u : supportedSobolevCompletion a b (2 * (N : ℝ)) (Ioi c)) :
    let T (y : ℝ) := cutoffMellinIntegral u.val k (⟨b, y⟩ : ℂ)
    MemLp T 2 volume ∧ (∫ y, ‖T y‖ ^ 2) ≤ 2 * Real.pi * ‖u‖ ^ 2 := by
  have h : (k : ℝ) + 1 ≤ N := by exact_mod_cast (Nat.succ_le_of_lt hk)
  simpa only [sub_self, mul_zero, zero_mul, Real.exp_zero, mul_one] using
    cutoffMellinIntegral_line_bound_of_le hab hc le_rfl hk.le (Or.inr (by linarith)) u


/-- A vertical line in the open half-plane determines the weighted cutoff class. -/
theorem cutoffMellinIntegral_line_injective {a b s c r : ℝ} (hc : c ≤ 0)
    (hs : 0 ≤ s) (hr : r < b) :
    Function.Injective (fun u : supportedSobolevCompletion a b s (Ioi c) =>
      fun y : ℝ => cutoffMellinIntegral u.val 0 ((r : ℂ) + (y : ℂ) * Complex.I)) := by
  intro u v huv
  suffices h : u - v = 0 by exact sub_eq_zero.mp h
  let w := u - v
  let f (x : ℝ) := w.val x * Complex.exp ((r : ℂ) * (x : ℂ))
  have hf : Integrable f := by
    simpa only [f, mellinEvaluationKernel, pow_zero, mul_one] using
      cutoffSobolev_mellinMoment_integrable hc hs w (z := (r : ℂ)) hr 0
  have hFourier : f =ᵐ[volume] 0 := by
    apply integrable_logFourier_ae_zero hf
    intro y
    let z : ℂ := (r : ℂ) + (y : ℂ) * Complex.I
    have hz : z.re < b := by simpa [z, Complex.add_re, Complex.mul_re] using hr
    obtain ⟨L, hL⟩ := cutoffSobolev_mellinMoment_functional (a := a) (c := c) hc hs hz 0
    have hEq : L u = L v := by
      rw [(hL u).2, (hL v).2]
      exact congrFun huv y
    have hw : L w = 0 := by
      change L (u - v) = 0
      rw [map_sub, hEq, sub_self]
    rw [(hL w).2] at hw
    refine (integral_congr_ae (.of_forall fun x => ?_)).trans hw
    simp only [f, z, mellinEvaluationKernel, pow_zero, mul_one, add_mul, Complex.exp_add]
    ring
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [(amplitudeMeasure_absolutelyContinuous (volume : Measure ℝ)
    (stripSobolevAmplitude a b s)).ae_le hFourier, Lp.coeFn_zero (μ := stripMeasure a b s)
      (p := 2) (E := ℂ)] with x hx hz
  change w.val x = (0 : StripSobolev a b s) x
  rw [hz]
  change w.val x * Complex.exp ((r : ℂ) * (x : ℂ)) = 0 at hx
  exact (mul_eq_zero.mp hx).resolve_right (Complex.exp_ne_zero _)


/-- Interior vertical traces converge pointwise to the actual endpoint moment
at every height, whenever the endpoint moment is integrable. -/
theorem cutoffMellinIntegral_boundary_tendsto {a b s c : ℝ} (hc : c ≤ 0)
    (hs : 0 ≤ s) {k : ℕ} (hk : 2 * (k : ℝ) + 1 < s)
    (u : supportedSobolevCompletion a b s (Ioi c)) (y : ℝ) :
    Tendsto (fun r : ℝ => iteratedDeriv k (cutoffMellinIntegral u.val 0) ((r : ℂ) + (y : ℂ) * Complex.I))
      (𝓝[<] b) (𝓝 (cutoffMellinIntegral u.val k ((b : ℂ) + (y : ℂ) * Complex.I))) := by
  let p (r : ℝ) : ℂ := (r : ℂ) + (y : ℂ) * Complex.I
  have hpre (r : ℝ) : (p r).re = r := by simp [p, Complex.add_re, Complex.mul_re]
  have hp : Tendsto p (𝓝[<] b) (𝓝[Complex.re ⁻¹' Iic b] (p b)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within p
      ((show Continuous p by dsimp [p]; fun_prop).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
      ((show ∀ᶠ r : ℝ in 𝓝[<] b, r < b from self_mem_nhdsWithin).mono
        fun r hr => show (p r).re ≤ b by rw [hpre]; exact hr.le)
  have hb : (p b).re ≤ b := by rw [hpre]
  have hCont : Tendsto (cutoffMellinIntegral u.val k) (𝓝[Complex.re ⁻¹' Iic b] (p b))
      (𝓝 (cutoffMellinIntegral u.val k (p b))) :=
    cutoffMellinIntegral_continuousOn_closedHalfPlane hc hs hk u (p b) hb
  apply (hCont.comp hp).congr'
  exact (show ∀ᶠ r : ℝ in 𝓝[<] b, r < b from self_mem_nhdsWithin).mono fun r hr =>
    (iteratedDeriv_cutoffMellinIntegral hc hs u k (z := p r) ((hpre r).symm ▸ hr)).symm

/-- The bounded-interval term of the cutoff completion is characterized by the
entire extension and its logarithmic interval growth factor. -/
theorem cutoffMellinIntegral_paleyWiener_iff {a b s c : ℝ}
    (hc : c ≤ 0) (hs : 0 ≤ s) (u : supportedSobolevCompletion a b s (Ioi c)) :
    u.val ∈ supportedSobolevCompletion a b s (Ioo c 0) ↔
      ∃ F : ℂ → ℂ, Differentiable ℂ F ∧
        (∀ z : ℂ, z.re < b → F z = cutoffMellinIntegral u.val 0 z) ∧
        ∃ C : ℝ, 0 ≤ C ∧
          ∀ z : ℂ, ‖F z‖ ≤ C * Real.sqrt (∫ x in Icc c 0, Real.exp (2 * z.re * x)) := by
  constructor
  · intro hu
    obtain ⟨_, hF, hbound⟩ := boundedStripSobolev_mellin_entire_bound a b s c ⟨u.val, hu⟩
    let C := Real.sqrt (∫ x in Icc c 0, ‖u.val x‖ ^ 2)
    refine ⟨cutoffMellinIntegral u.val 0, ?_, fun _ _ => rfl, C, Real.sqrt_nonneg _, ?_⟩
    · have hEq : cutoffMellinIntegral u.val 0 =
          fun z : ℂ => ∫ x : ℝ, compactMellinKernel u.val z x := by
        funext z
        simp only [cutoffMellinIntegral, mellinEvaluationKernel, compactMellinKernel, pow_zero, mul_one]
      exact hEq.symm ▸ hF
    · intro z
      simpa only [cutoffMellinIntegral, mellinEvaluationKernel, compactMellinKernel, C, pow_zero, mul_one] using hbound z
  · rintro ⟨F, hF, hExt, C, hC, hbound⟩
    let r := b - 1
    have hr : r < b := by dsimp [r]; linarith
    apply cutoffSobolev_mem_bounded_of_mellin_growth hc hs hr u F hF _ hC hbound
    intro y
    let z : ℂ := (r : ℂ) + (y : ℂ) * Complex.I
    change F z = ∫ x : ℝ, u.val x * Complex.exp (z * (x : ℂ))
    rw [hExt z (by simpa [z, Complex.add_re, Complex.mul_re] using hr)]
    simp only [cutoffMellinIntegral, mellinEvaluationKernel, pow_zero, mul_one]

end
end Masullo
