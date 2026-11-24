import HardySobolevMellin
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

open Filter Function MeasureTheory Set Topology
open scoped ContDiff ENNReal NNReal

namespace Masullo

noncomputable section

variable {X : Type*} [MeasurableSpace X]

private theorem eLpNorm_two_sq (μ : Measure X) (f : X → ℂ) :
    eLpNorm f 2 μ ^ (2 : ℕ) = ∫⁻ x, ‖f x‖ₑ ^ (2 : ℕ) ∂μ := by
  simpa only [ENNReal.rpow_ofNat, NNReal.coe_ofNat, ENNReal.coe_ofNat] using
    (eLpNorm_nnreal_pow_eq_lintegral (μ := μ) (f := f) (p := (2 : ℝ≥0)) (by norm_num))

private theorem measure_hardySobolev_lintegral (μ : Measure X) {logNorm : X → ℝ}
    (hl : Measurable logNorm) {f : X → ℂ} (hf : Measurable f) (a b s : ℝ) :
    eLpNorm f 2 (hardySobolevMeasure μ logNorm a b s) ^ (2 : ℕ) =
      ∫⁻ x, ENNReal.ofReal (hardySobolevWeight a b s (logNorm x)) * ‖f x‖ₑ ^ (2 : ℕ) ∂μ := by
  rw [eLpNorm_two_sq, hardySobolevMeasure]
  have hm : Measurable (fun x => ENNReal.ofReal (hardySobolevWeight a b s (logNorm x))) :=
    ((continuous_hardySobolevWeight a b s).measurable.comp hl).ennreal_ofReal
  exact lintegral_withDensity_eq_lintegral_mul μ hm (hf.enorm.pow_const 2)

private theorem hardySobolev_right_endpoint (a b s x : ℝ) (hab : a ≤ b) (hx : x ≤ 0) :
    hardySobolevWeight a b s x = hardySobolevWeight a a s x := by
  have h : Real.exp (2 * b * x) ≤ Real.exp (2 * a * x) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_right (by linarith) hx)
  unfold hardySobolevWeight
  rw [max_eq_left h, max_self]

/-- The right half-line has only the endpoint norm for tests supported in the
nonpositive logarithmic ray. The support condition can hold almost everywhere. -/
theorem hardySobolevIntervalENorm_Ici_of_ae (μ : Measure X) {logNorm : X → ℝ}
    (hl : Measurable logNorm) {f : X → ℂ} (hf : Measurable f)
    (hsupp : ∀ᵐ x ∂μ, 0 < logNorm x → f x = 0) (a s : ℝ) :
    hardySobolevIntervalENorm μ logNorm (Ici a) s f =
      eLpNorm f 2 (hardySobolevMeasure μ logNorm a a s) := by
  rw [hardySobolevIntervalENorm_Ici]
  have he (b : Ici a) : eLpNorm f 2 (hardySobolevMeasure μ logNorm a b s) =
      eLpNorm f 2 (hardySobolevMeasure μ logNorm a a s) := by
    apply (ENNReal.pow_right_strictMono (n := 2) (by decide)).injective
    dsimp only
    rw [measure_hardySobolev_lintegral μ hl hf, measure_hardySobolev_lintegral μ hl hf]
    apply lintegral_congr_ae
    filter_upwards [hsupp] with x hx
    by_cases h : 0 < logNorm x
    · simp [hx h]
    · rw [hardySobolev_right_endpoint a b s (logNorm x) b.2 (le_of_not_gt h)]
  simp_rw [he]
  exact iSup_const

/-- Positive mass where the logarithmic modulus is positive and the test is
nonzero forces the right half-line norm to be infinite. -/
theorem hardySobolevIntervalENorm_Ici_eq_top (μ : Measure X) {logNorm : X → ℝ}
    (hl : Measurable logNorm) {f : X → ℂ} (hf : Measurable f)
    (hbad : μ {x | 0 < logNorm x ∧ f x ≠ 0} ≠ 0) (a s : ℝ) :
    hardySobolevIntervalENorm μ logNorm (Ici a) s f = (∞ : ℝ≥0∞) := by
  let b (n : ℕ) : ℝ := a + n
  let H (n : ℕ) (x : X) := ENNReal.ofReal (hardySobolevWeight a (b n) s (logNorm x)) * ‖f x‖ₑ ^ (2 : ℕ)
  have hb (n : ℕ) : a ≤ b n := le_add_of_nonneg_right (Nat.cast_nonneg _)
  have hmeas (n : ℕ) : Measurable (H n) :=
    (((continuous_hardySobolevWeight a (b n) s).measurable.comp hl).ennreal_ofReal).mul
      (hf.enorm.pow_const _)
  have hmono : Monotone H := by
    intro m n hmn x
    have hbn : b m ≤ b n := by dsimp [b]; exact add_le_add_right (Nat.cast_le.mpr hmn) a
    exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal
      (hardySobolevWeight_mono_interval le_rfl (hb n) (hb m) hbn s (logNorm x))) bot_le
  have hi (x : X) (hx : 0 < logNorm x ∧ f x ≠ 0) : (⨆ n, H n x) = (∞ : ℝ≥0∞) := by
    let C : ℝ := (1 + logNorm x ^ 2) ^ (s / 2) * ‖f x‖ ^ (2 : ℕ)
    have hC : 0 < C := mul_pos (Real.rpow_pos_of_pos (by positivity) _)
      (pow_pos (norm_pos_iff.mpr hx.2) _)
    have hlin : Tendsto (fun n : ℕ => 2 * b n * logNorm x) atTop atTop := by
      have ht : Tendsto b atTop atTop :=
        tendsto_atTop_add_const_left _ a tendsto_natCast_atTop_atTop
      exact (ht.const_mul_atTop (by norm_num)).atTop_mul_const hx.1
    have ht : Tendsto (fun n : ℕ => ENNReal.ofReal (Real.exp (2 * b n * logNorm x) * C))
        atTop (𝓝 (∞ : ℝ≥0∞)) :=
      ENNReal.tendsto_ofReal_atTop.comp ((Real.tendsto_exp_atTop.comp hlin).atTop_mul_const hC)
    have hle (n : ℕ) : ENNReal.ofReal (Real.exp (2 * b n * logNorm x) * C) ≤ H n x := by
      dsimp [H, C]
      rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _),
        ← ENNReal.ofReal_mul (hardySobolevWeight_nonneg ..), mul_assoc]
      apply ENNReal.ofReal_le_ofReal
      unfold hardySobolevWeight
      rw [mul_assoc]
      gcongr
      simpa only [mul_assoc] using
        (le_max_right (Real.exp (2 * a * logNorm x)) (Real.exp (2 * b n * logNorm x)))
    exact top_unique (le_of_tendsto ht (.of_forall fun n => (hle n).trans (le_iSup (fun j => H j x) n)))
  let S : Set X := {x | 0 < logNorm x ∧ f x ≠ 0}
  have hS : MeasurableSet S := (measurableSet_lt measurable_const hl).inter
    (measurableSet_eq_fun hf measurable_const).compl
  have htop : (∫⁻ x, ⨆ n, H n x ∂μ) = (∞ : ℝ≥0∞) := by
    apply top_unique
    calc
      (∞ : ℝ≥0∞) = ∫⁻ x in S, (∞ : ℝ≥0∞) ∂μ := by
        rw [setLIntegral_const, ENNReal.top_mul hbad]
      _ ≤ ∫⁻ x in S, ⨆ n, H n x ∂μ := by
        apply lintegral_mono_ae
        exact (ae_restrict_mem hS).mono fun x hx => (hi x hx).ge
      _ ≤ _ := lintegral_mono' Measure.restrict_le_self le_rfl
  rw [lintegral_iSup hmeas hmono] at htop
  let A := hardySobolevIntervalENorm μ logNorm (Ici a) s f
  have hA (n : ℕ) : (∫⁻ x, H n x ∂μ) ≤ A ^ (2 : ℕ) := by
    rw [← measure_hardySobolev_lintegral μ hl hf]
    apply pow_le_pow_left'
    rw [show A = hardySobolevIntervalENorm μ logNorm (Ici a) s f from rfl,
      hardySobolevIntervalENorm_Ici]
    exact le_iSup (fun t : Ici a => eLpNorm f 2 (hardySobolevMeasure μ logNorm a t s)) ⟨b n, hb n⟩
  have hA_top : A ^ (2 : ℕ) = (∞ : ℝ≥0∞) := top_unique (htop ▸ iSup_le hA)
  exact ENNReal.pow_eq_top_iff.mp hA_top |>.1


private theorem hardySobolevMeasure_reflect (μ : Measure X) (l : X → ℝ) (a b s : ℝ) :
    hardySobolevMeasure μ (fun x => -l x) (-a) (-b) s =
      hardySobolevMeasure μ l b a s := by
  unfold hardySobolevMeasure hardySobolevWeight
  congr 1
  funext x
  rw [neg_sq, show 2 * -a * -l x = 2 * a * l x by ring,
    show 2 * -b * -l x = 2 * b * l x by ring, max_comm]

private theorem hardySobolevIntervalENorm_reflect_Iic (μ : Measure X) (l : X → ℝ)
    (b s : ℝ) (f : X → ℂ) :
    hardySobolevIntervalENorm μ (fun x => -l x) (Ici (-b)) s f =
      hardySobolevIntervalENorm μ l (Iic b) s f := by
  rw [hardySobolevIntervalENorm_Ici, hardySobolevIntervalENorm_Iic]
  let e : Iic b ≃ Ici (-b) :=
    { toFun := fun a => ⟨-(a : ℝ), show -b ≤ -(a : ℝ) from neg_le_neg (show (a : ℝ) ≤ b from a.2)⟩
      invFun := fun a => ⟨-(a : ℝ), show -(a : ℝ) ≤ b from by have ha : -b ≤ (a : ℝ) := a.2; linarith⟩
      left_inv := fun _ => Subtype.ext (neg_neg _)
      right_inv := fun _ => Subtype.ext (neg_neg _) }
  rw [← e.iSup_comp]
  congr 1
  funext a
  change eLpNorm f 2 (hardySobolevMeasure μ (fun x => -l x) (-b) (-(a : ℝ)) s) = _
  rw [hardySobolevMeasure_reflect]

/-- The left half-line has only the endpoint norm for tests supported in the
nonnegative logarithmic ray. -/
theorem hardySobolevIntervalENorm_Iic_of_ae (μ : Measure X) {logNorm : X → ℝ}
    (hl : Measurable logNorm) {f : X → ℂ} (hf : Measurable f)
    (hsupp : ∀ᵐ x ∂μ, logNorm x < 0 → f x = 0) (b s : ℝ) :
    hardySobolevIntervalENorm μ logNorm (Iic b) s f =
      eLpNorm f 2 (hardySobolevMeasure μ logNorm b b s) := by
  rw [← hardySobolevIntervalENorm_reflect_Iic, hardySobolevIntervalENorm_Ici_of_ae μ (logNorm := fun x => -logNorm x) hl.neg hf
    (hsupp.mono fun _ hx hs => hx (neg_pos.mp hs)), hardySobolevMeasure_reflect]

/-- Positive mass on the negative logarithmic ray where the test is nonzero
forces the left half-line norm to be infinite. -/
theorem hardySobolevIntervalENorm_Iic_eq_top (μ : Measure X) {logNorm : X → ℝ}
    (hl : Measurable logNorm) {f : X → ℂ} (hf : Measurable f)
    (hbad : μ {x | logNorm x < 0 ∧ f x ≠ 0} ≠ 0) (b s : ℝ) :
    hardySobolevIntervalENorm μ logNorm (Iic b) s f = (∞ : ℝ≥0∞) := by
  rw [← hardySobolevIntervalENorm_reflect_Iic]
  apply hardySobolevIntervalENorm_Ici_eq_top μ (logNorm := fun x => -logNorm x) hl.neg hf _ (-b) s
  simpa only [neg_pos] using hbad


theorem smooth_exponentialProfile (J : Set ℝ) (a : J)
    (f : PositiveRealExponentialDecay J) : ContDiff ℝ ∞ f.val := by
  let g := logExponentialDecayTwist J a f
  have hu : ContDiff ℝ ∞ (fun x : ℝ => (Real.exp (-((a : ℝ) * x)) : ℂ) * g x) := by
    apply ContDiff.mul _ g.smooth'
    exact Complex.ofRealCLM.contDiff.comp ((contDiff_const.mul contDiff_id).neg.exp)
  convert hu using 1
  funext x
  rw [show g x = _ from logExponentialDecayTwist_apply J a f x, ← mul_assoc,
    ← Complex.ofReal_mul, ← Real.exp_add, neg_add_cancel, Real.exp_zero, Complex.ofReal_one, one_mul]

private theorem exists_smoothCompact_approx_preserving_zeros
    (a s : ℝ) {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hm : MemLp f 2 (stripMeasure a a s)) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℝ → ℂ, HasCompactSupport g ∧ ContDiff ℝ ∞ g ∧
      (∀ x, f x = 0 → g x = 0) ∧ eLpNorm (f - g) 2 (stripMeasure a a s) ≤ ENNReal.ofReal ε := by
  obtain ⟨q, hq, _, hap⟩ := hm.exist_eLpNorm_sub_le (by norm_num) (by norm_num) hε
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).mp hq.isBounded
  let b : ContDiffBump (0 : ℝ) := ⟨max 1 R, max 1 R + 1,
    zero_lt_one.trans_le (le_max_left _ _), by linarith⟩
  let g (x : ℝ) := (b x : ℂ) * f x
  have hbg : HasCompactSupport (fun x : ℝ => (b x : ℂ)) :=
    b.hasCompactSupport.comp_left Complex.ofReal_zero
  refine ⟨g, hbg.mul_right, (Complex.ofRealCLM.contDiff.comp b.contDiff).mul hf,
    fun x hx => by simp [g, hx], ?_⟩
  apply le_trans (eLpNorm_mono fun x => ?_) hap
  have hbq : (b x : ℂ) * q x = q x := by
    by_cases hx : q x = 0
    · simp [hx]
    · have hdist := hR (subset_tsupport q (show x ∈ Function.support q from hx))
      have hbr : b x = 1 :=
        b.one_of_mem_closedBall (Metric.closedBall_subset_closedBall (le_max_right 1 R) hdist)
      simp [hbr]
  have he : f x - g x = (↑(1 - b x) : ℂ) * (f x - q x) := by
    push_cast
    dsimp [g]
    linear_combination -hbq
  change ‖f x - g x‖ ≤ ‖f x - q x‖
  rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr b.le_one)]
  exact mul_le_of_le_one_left (norm_nonneg _) (sub_le_self _ b.nonneg)

/-- The completion of the tests constrained to vanish off a given set depends
only on the endpoint norm. Compactly supported smooth tests preserve the imposed
zeros in the approximation. -/
theorem supportedStripTest_closure_eq (J K : Set ℝ) (a : ℝ) (haJ : a ∈ J) (haK : a ∈ K)
    (s : ℝ) (U : Set ℝ) :
    closure {u : StripSobolev a a s | ∃ f : PositiveRealExponentialDecay J,
      (∀ x ∉ U, f.val x = 0) ∧ stripSobolevTest J ⟨a, haJ⟩ ⟨a, haJ⟩ s f = u} =
      closure {u : StripSobolev a a s | ∃ f : PositiveRealExponentialDecay K,
        (∀ x ∉ U, f.val x = 0) ∧ stripSobolevTest K ⟨a, haK⟩ ⟨a, haK⟩ s f = u} := by
  have approx (L M : Set ℝ) (c : ℝ) (hcL : c ∈ L) (hcM : c ∈ M) :
      {u : StripSobolev c c s | ∃ f : PositiveRealExponentialDecay L,
        (∀ x ∉ U, f.val x = 0) ∧ stripSobolevTest L ⟨c, hcL⟩ ⟨c, hcL⟩ s f = u} ⊆
      closure {u : StripSobolev c c s | ∃ f : PositiveRealExponentialDecay M,
        (∀ x ∉ U, f.val x = 0) ∧ stripSobolevTest M ⟨c, hcM⟩ ⟨c, hcM⟩ s f = u} := by
    rintro _ ⟨f, hf, rfl⟩
    let j := stripSobolevTest L ⟨c, hcL⟩ ⟨c, hcL⟩ s
    have hj := stripSobolevTest_ae L ⟨c, hcL⟩ ⟨c, hcL⟩ s f
    have hm := (Lp.memLp (j f)).ae_eq hj
    apply (mem_closure_iff_nhds_basis Metric.nhds_basis_closedBall).2
    intro ε hε
    obtain ⟨g, hgc, hgs, hgz, hg⟩ := exists_smoothCompact_approx_preserving_zeros c s
      (smooth_exponentialProfile L ⟨c, hcL⟩ f) hm hε
    let v : PositiveRealExponentialDecay M :=
      ⟨g, mem_logExponentialDecaySubmodule_of_hasCompactSupport M hgc hgs⟩
    let k := stripSobolevTest M ⟨c, hcM⟩ ⟨c, hcM⟩ s
    have hk := stripSobolevTest_ae M ⟨c, hcM⟩ ⟨c, hcM⟩ s v
    refine ⟨k v, ⟨v, fun x hx => hgz x (hf x hx), rfl⟩, ?_⟩
    change dist (k v) (j f) ≤ ε
    rw [dist_comm, Lp.dist_def, eLpNorm_congr_ae (hj.sub hk)]
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hg).trans_eq (ENNReal.toReal_ofReal hε.le)
  exact le_antisymm (closure_minimal (approx J K a haJ haK) isClosed_closure)
    (closure_minimal (approx K J a haK haJ) isClosed_closure)


private theorem endpointNorm_ne_top (J : Set ℝ) (a : J) (s : ℝ)
    (f : PositiveRealExponentialDecay J) :
    eLpNorm f.val 2 (hardySobolevMeasure volume id a a s) ≠ (∞ : ℝ≥0∞) := by
  rw [← stripMeasure_eq _ _ _ le_rfl]
  exact ((Lp.memLp (stripSobolevTest J a a s f)).ae_eq (stripSobolevTest_ae J a a s f)).eLpNorm_ne_top

/-- On the scalar tests the finite right half-line domain is exactly the tests
vanishing on the positive logarithmic ray. -/
theorem scalarHardySobolev_Ici_finite_iff (J : Set ℝ) (a : J) (s : ℝ)
    (f : PositiveRealExponentialDecay J) :
    hardySobolevIntervalENorm volume id (Ici (a : ℝ)) s f.val ≠ (∞ : ℝ≥0∞) ↔
      ∀ x : ℝ, 0 < x → f.val x = 0 := by
  have hf := (smooth_exponentialProfile J a f).continuous
  refine ⟨fun h x hx => ?_, fun h => ?_⟩
  · by_contra hfx
    have hm : 0 < (volume : Measure ℝ) {y | 0 < y ∧ f.val y ≠ 0} :=
      (isOpen_Ioi.inter (isOpen_ne_fun hf continuous_const)).measure_pos volume ⟨x, hx, hfx⟩
    exact h (hardySobolevIntervalENorm_Ici_eq_top volume measurable_id hf.measurable hm.ne' a s)
  · rw [hardySobolevIntervalENorm_Ici_of_ae volume measurable_id hf.measurable (.of_forall h)]
    exact endpointNorm_ne_top J a s f

/-- On the scalar tests the finite left half-line domain is exactly the tests
vanishing on the negative logarithmic ray. -/
theorem scalarHardySobolev_Iic_finite_iff (J : Set ℝ) (b : J) (s : ℝ)
    (f : PositiveRealExponentialDecay J) :
    hardySobolevIntervalENorm volume id (Iic (b : ℝ)) s f.val ≠ (∞ : ℝ≥0∞) ↔
      ∀ x : ℝ, x < 0 → f.val x = 0 := by
  have hf := (smooth_exponentialProfile J b f).continuous
  refine ⟨fun h x hx => ?_, fun h => ?_⟩
  · by_contra hfx
    have hm : 0 < (volume : Measure ℝ) {y | y < 0 ∧ f.val y ≠ 0} :=
      (isOpen_Iio.inter (isOpen_ne_fun hf continuous_const)).measure_pos volume ⟨x, hx, hfx⟩
    exact h (hardySobolevIntervalENorm_Iic_eq_top volume measurable_id hf.measurable hm.ne' b s)
  · rw [hardySobolevIntervalENorm_Iic_of_ae volume measurable_id hf.measurable (.of_forall h)]
    exact endpointNorm_ne_top J b s f

/-- For a finite-norm family on a half-line, any collection of abscissae that
contains the finite endpoint measures the same convergence as the weighted norm. -/
theorem hardySobolev_endpoint_traces_tendsto_iff {ι : Type*} {l : Filter ι}
    {I A : Set ℝ} (hAI : A ⊆ I) {a : ℝ} (ha : a ∈ A)
    (N : ℕ) (f : ι → logExponentialDecaySubmodule (univ : Set ℝ))
    (hendpoint : ∀ i,
      hardySobolevIntervalENorm volume id I (2 * (N : ℝ)) (f i).val =
        eLpNorm (f i).val 2 (hardySobolevMeasure volume id a a (2 * (N : ℝ)))) :
    Tendsto (fun i =>
        (hardySobolevIntervalENorm volume id I (2 * (N : ℝ)) (f i).val).toReal) l (𝓝 0) ↔
      ∀ σ ∈ A, ∀ k ≤ N, Tendsto (fun i => mellinLineEnergy (f i) k σ) l (𝓝 0) := by
  apply hardySobolev_finite_traces_tendsto_iff hAI ha ha N f
  · intro i
    rw [hendpoint i]
    exact endpointNorm_ne_top univ ⟨a, mem_univ a⟩ _ (f i)
  · intro i
    rw [hendpoint i, hardySobolev_singleton_mellin_energy]
    apply Finset.sum_le_sum
    intro k _
    exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (mellinLineEnergy_nonneg (f i) k a))
      (Nat.cast_nonneg _)

/-- Compact interval weighted norm convergence is exactly convergence of the
finitely many Mellin derivative traces at its two endpoints. -/
theorem hardySobolev_compact_traces_tendsto_iff {ι : Type*} {l : Filter ι}
    {a b : ℝ} (hab : a ≤ b) (N : ℕ) (f : ι → logExponentialDecaySubmodule (univ : Set ℝ)) :
    Tendsto (fun i =>
        (hardySobolevIntervalENorm volume id (Icc a b) (2 * (N : ℝ)) (f i).val).toReal) l (𝓝 0) ↔
      ∀ σ ∈ ({a, b} : Set ℝ), ∀ k ≤ N,
        Tendsto (fun i => mellinLineEnergy (f i) k σ) l (𝓝 0) := by
  refine hardySobolev_finite_traces_tendsto_iff ?_ (by simp : a ∈ ({a, b} : Set ℝ))
    (by simp : b ∈ ({a, b} : Set ℝ)) N f ?_
    (fun i => (hardySobolev_compact_mellin_energy_bounds a b hab N (f i)).1)
  · intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl | h
    · exact left_mem_Icc.mpr hab
    · rw [Set.mem_singleton_iff.mp h]
      exact right_mem_Icc.mpr hab
  · intro i
    rw [(stripSobolevTest_energy univ ⟨a, mem_univ a⟩ ⟨b, mem_univ b⟩ hab
      (2 * (N : ℝ)) (f i)).2]
    exact ENNReal.ofReal_ne_top


/-- A strip test embedding with at least one abscissa identifies the original
function uniquely. -/
theorem stripSobolevTest_injective (J : Set ℝ) (a b : J) (s : ℝ) :
    Injective (stripSobolevTest J a b s) := by
  intro f g h
  apply Subtype.ext
  have hfg := (stripSobolevTest_ae J a b s f).symm.trans
    (h ▸ stripSobolevTest_ae J a b s g)
  have hac := absolutelyContinuous_amplitudeMeasure (volume : Measure ℝ) (stripSobolevAmplitude a b s)
    (stripSobolevAmplitude_continuous a b s).measurable (stripSobolevAmplitude_pos a b s)
  exact Measure.eq_of_ae_eq (hac.ae_le hfg) (smooth_exponentialProfile J a f).continuous
    (smooth_exponentialProfile J a g).continuous

/-- An interval unbounded in both directions has finite norm only on the
zero scalar test. -/
theorem scalarHardySobolev_univ_finite_iff (s : ℝ) (J : Set ℝ) (a : J)
    (f : PositiveRealExponentialDecay J) :
    hardySobolevIntervalENorm volume id (univ : Set ℝ) s f.val ≠ (∞ : ℝ≥0∞) ↔ f = 0 := by
  constructor
  · intro h
    have hm (S : Set ℝ) : hardySobolevIntervalENorm volume id S s f.val ≤
        hardySobolevIntervalENorm volume id (univ : Set ℝ) s f.val :=
      iSup₂_le fun b c => le_iSup₂_of_le
        ⟨(b : ℝ), mem_univ (b : ℝ)⟩ ⟨(c : ℝ), mem_univ (c : ℝ)⟩ le_rfl
    have hr := (scalarHardySobolev_Ici_finite_iff J a s f).mp (ne_top_of_le_ne_top h (hm (Ici (a : ℝ))))
    have hl := (scalarHardySobolev_Iic_finite_iff J a s f).mp (ne_top_of_le_ne_top h (hm (Iic (a : ℝ))))
    have hne : ∀ᵐ x : ℝ ∂(volume : Measure ℝ), x ≠ 0 := by simp [ae_iff, measure_singleton]
    apply Subtype.ext
    change f.val = (fun _ : ℝ => (0 : ℂ))
    apply Measure.eq_of_ae_eq (μ := (volume : Measure ℝ)) _ (smooth_exponentialProfile J a f).continuous continuous_const
    exact hne.mono fun x hx => (lt_or_gt_of_ne hx).elim (hl x) (hr x)
  · rintro rfl
    change hardySobolevIntervalENorm volume id (univ : Set ℝ) s (0 : ℝ → ℂ) ≠ (∞ : ℝ≥0∞)
    simp [hardySobolevIntervalENorm]

/-- Right half-line trace topology on the corrected support domain. -/
theorem hardySobolev_right_traces_tendsto_iff {ι : Type*} {l : Filter ι} {a : ℝ}
    {A : Set ℝ} (hA : A ⊆ Ici a) (ha : a ∈ A) (N : ℕ)
    (f : ι → logExponentialDecaySubmodule (univ : Set ℝ))
    (hsupp : ∀ i x, 0 < x → (f i).val x = 0) :
    Tendsto (fun i => (hardySobolevIntervalENorm volume id (Ici a) (2 * (N : ℝ))
      (f i).val).toReal) l (𝓝 0) ↔
      ∀ σ ∈ A, ∀ k ≤ N, Tendsto (fun i => mellinLineEnergy (f i) k σ) l (𝓝 0) := by
  apply hardySobolev_endpoint_traces_tendsto_iff hA ha N f
  intro i
  exact hardySobolevIntervalENorm_Ici_of_ae volume measurable_id
    (smooth_exponentialProfile univ ⟨a, mem_univ a⟩ (f i)).continuous.measurable
    (.of_forall (hsupp i)) _ _

/-- Left half-line trace topology on the corrected support domain. -/
theorem hardySobolev_left_traces_tendsto_iff {ι : Type*} {l : Filter ι} {b : ℝ}
    {A : Set ℝ} (hA : A ⊆ Iic b) (hb : b ∈ A) (N : ℕ)
    (f : ι → logExponentialDecaySubmodule (univ : Set ℝ))
    (hsupp : ∀ i x, x < 0 → (f i).val x = 0) :
    Tendsto (fun i => (hardySobolevIntervalENorm volume id (Iic b) (2 * (N : ℝ))
      (f i).val).toReal) l (𝓝 0) ↔
      ∀ σ ∈ A, ∀ k ≤ N, Tendsto (fun i => mellinLineEnergy (f i) k σ) l (𝓝 0) := by
  apply hardySobolev_endpoint_traces_tendsto_iff hA hb N f
  intro i
  exact hardySobolevIntervalENorm_Iic_of_ae volume measurable_id
    (smooth_exponentialProfile univ ⟨b, mem_univ b⟩ (f i)).continuous.measurable
    (.of_forall (hsupp i)) _ _

/-- An explicit smooth compactly supported test refutes finiteness on the
unrestricted right half-line test space. -/
theorem scalarHardySobolev_right_counterexample (a s : ℝ) :
    ∃ f : PositiveRealExponentialDecay univ, HasCompactSupport f.val ∧
      hardySobolevIntervalENorm volume id (Ici a) s f.val = (∞ : ℝ≥0∞) := by
  let b : ContDiffBump (1 : ℝ) := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩
  let g (x : ℝ) := (b x : ℂ)
  have hg : HasCompactSupport g := b.hasCompactSupport.comp_left Complex.ofReal_zero
  let f : PositiveRealExponentialDecay univ :=
    ⟨g, mem_logExponentialDecaySubmodule_of_hasCompactSupport univ hg
      (Complex.ofRealCLM.contDiff.comp b.contDiff)⟩
  refine ⟨f, hg, by_contra fun h => ?_⟩
  have hz := (scalarHardySobolev_Ici_finite_iff univ ⟨a, mem_univ a⟩ s f).mp h 1 one_pos
  have h1 : b 1 = 1 := b.one_of_mem_closedBall (Metric.mem_closedBall_self (by norm_num [b]))
  change (b 1 : ℂ) = 0 at hz
  simp [h1] at hz


/-- A logarithmic translation can take a finite-norm test outside the
right half-line domain. In multiplicative coordinates the shift is by `exp 2`. -/
theorem scalarHardySobolev_right_translation_counterexample (a s : ℝ) :
    ∃ f : PositiveRealExponentialDecay univ, HasCompactSupport f.val ∧
      hardySobolevIntervalENorm volume id (Ici a) s f.val ≠ (∞ : ℝ≥0∞) ∧
      hardySobolevIntervalENorm volume id (Ici a) s (fun x ↦ f.val (x - 2)) = (∞ : ℝ≥0∞) := by
  let b : ContDiffBump (-1 : ℝ) := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩
  let g (x : ℝ) := (b x : ℂ)
  have hg : HasCompactSupport g := b.hasCompactSupport.comp_left Complex.ofReal_zero
  have hgd : ContDiff ℝ ∞ g := Complex.ofRealCLM.contDiff.comp b.contDiff
  let f : PositiveRealExponentialDecay univ :=
    ⟨g, mem_logExponentialDecaySubmodule_of_hasCompactSupport univ hg hgd⟩
  have hs (x : ℝ) (hx : 0 < x) : f.val x = 0 := by
    have h : x ∉ Function.support b := by
      rw [b.support_eq, Metric.mem_ball, Real.dist_eq, abs_of_pos (by linarith : 0 < x - -1)]
      change ¬ x - -1 < 1 / 2
      linarith
    change (b x : ℂ) = 0
    exact Complex.ofReal_eq_zero.mpr (notMem_support.mp h)
  let k (x : ℝ) := g (x - 2)
  have hk : HasCompactSupport k := by
    have h := hg.comp_homeomorph (Homeomorph.addRight (-2 : ℝ))
    change HasCompactSupport (fun x : ℝ ↦ g (x + -2)) at h
    simpa only [k, sub_eq_add_neg] using h
  let H : PositiveRealExponentialDecay univ :=
    ⟨k, mem_logExponentialDecaySubmodule_of_hasCompactSupport univ hk
      (hgd.comp (contDiff_id.sub contDiff_const))⟩
  refine ⟨f, hg, (scalarHardySobolev_Ici_finite_iff univ ⟨a, mem_univ a⟩ s f).mpr hs, ?_⟩
  by_contra h
  have hz := (scalarHardySobolev_Ici_finite_iff univ ⟨a, mem_univ a⟩ s H).mp h 1 one_pos
  have h₁ : b (-1) = 1 := b.one_of_mem_closedBall (Metric.mem_closedBall_self (by norm_num [b]))
  change (b (1 - 2) : ℂ) = 0 at hz
  norm_num [h₁] at hz

private theorem stripSobolevTest_endpoint_norm (J : Set ℝ) (a : J) (s : ℝ)
    (f : PositiveRealExponentialDecay J) :
    (eLpNorm f.val 2 (hardySobolevMeasure volume id a a s)).toReal =
      ‖stripSobolevTest J a a s f‖ := by
  rw [← stripMeasure_eq _ _ _ le_rfl, Lp.norm_def, eLpNorm_congr_ae (stripSobolevTest_ae J a a s f)]

/-- The corrected half-line norms are continuous on their finite-norm
subspaces for every exponential test topology containing the endpoint. -/
theorem scalarHardySobolev_halfline_continuousOn (J : Set ℝ) (a : J) (s : ℝ) :
    ContinuousOn (fun f : PositiveRealExponentialDecay J =>
      (hardySobolevIntervalENorm volume id (Ici (a : ℝ)) s f.val).toReal)
        {f | ∀ x : ℝ, 0 < x → f.val x = 0} ∧
    ContinuousOn (fun f : PositiveRealExponentialDecay J =>
      (hardySobolevIntervalENorm volume id (Iic (a : ℝ)) s f.val).toReal)
        {f | ∀ x : ℝ, x < 0 → f.val x = 0} := by
  have hc : Continuous (fun f => ‖stripSobolevTest J a a s f‖) :=
    (stripSobolevTest J a a s).continuous.norm
  constructor
  · refine hc.continuousOn.congr fun f hf => ?_
    rw [hardySobolevIntervalENorm_Ici_of_ae volume measurable_id
      (smooth_exponentialProfile J a f).continuous.measurable (.of_forall hf),
      stripSobolevTest_endpoint_norm]
  · refine hc.continuousOn.congr fun f hf => ?_
    rw [hardySobolevIntervalENorm_Iic_of_ae volume measurable_id
      (smooth_exponentialProfile J a f).continuous.measurable (.of_forall hf),
      stripSobolevTest_endpoint_norm]

end
end Masullo
