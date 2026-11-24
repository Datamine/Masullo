import RealSchwartzEulerCovariance
import RealPuncturedDerivatives
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

open Filter Function Set TopologicalSpace Topology MeasureTheory
open scoped Classical ContDiff Distributions SchwartzMap

namespace Masullo

noncomputable section

private abbrev Tests := 𝓓(puncturedOpens ℝ, ℂ)
private abbrev Schwartz := 𝓢(ℝ, ℂ)

/-- View a smooth compact test supported off zero as an ordinary Schwartz test. -/
def realPuncturedToSchwartz : Tests →L[ℂ] Schwartz :=
  smoothTestToSchwartz.comp (TestFunction.monoCLM ℂ)

@[simp] theorem realPuncturedToSchwartz_apply (f : Tests) (x : ℝ) :
    realPuncturedToSchwartz f x = f x := by
  rw [realPuncturedToSchwartz, ContinuousLinearMap.comp_apply, smoothTestToSchwartz_apply]
  have h := TestFunction.monoCLM_apply (𝕜 := ℂ) (Ω₂ := (⊤ : Opens ℝ)) (n₂ := ⊤) f
  rw [ite_eq_left ⟨le_rfl, le_top⟩] at h
  exact congrFun h x

private def untwist (z : ℂ) (x : ℝ) : ℂ :=
  Complex.exp (-z * (Real.log x : ℂ))

private theorem untwist_contDiffOn (z : ℂ) :
    ContDiffOn ℝ ∞ (untwist z) (puncturedOpens ℝ : Set ℝ) := by
  intro x hx
  have hlog : ContDiffAt ℝ ∞ Real.log x := Real.contDiffAt_log.mpr hx
  exact (Complex.contDiff_exp.contDiffAt.comp x
    (contDiffAt_const.mul (Complex.ofRealCLM.contDiff.contDiffAt.comp x hlog))).contDiffWithinAt

private theorem hasDerivAt_untwist (z : ℂ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (untwist z) (untwist z x * (-z * (x : ℂ)⁻¹)) x := by
  have hlog := (Real.hasDerivAt_log hx).ofReal_comp
  simpa only [untwist, Complex.ofReal_inv] using! (hlog.const_mul (-z)).cexp

private def puncturedUntwist (z : ℂ) : Tests →L[ℂ] Tests :=
  openTestMultiplier _ (untwist z) (untwist_contDiffOn z)

/-- Multiplication by the reciprocal Mellin density on the punctured line.
Conjugation by this multiplier reduces the dilation equation to an ordinary
derivative on compact tests. -/
def realPuncturedWeilMultiplier (z : ℂ) : Tests →L[ℂ] Tests :=
  openTestMultiplier _ (fun x : ℝ => (x : ℂ) * untwist z x)
    (Complex.ofRealCLM.contDiff.contDiffOn.mul (untwist_contDiffOn z))

@[simp] theorem realPuncturedWeilMultiplier_apply (z : ℂ) (g : Tests) (x : ℝ) :
    realPuncturedWeilMultiplier z g x = ((x : ℂ) * untwist z x) * g x := rfl

private theorem realPuncturedWeilMultiplier_ne_zero (z : ℂ) (x : ℝ)
    (hx : x ∈ (puncturedOpens ℝ : Set ℝ)) : (x : ℂ) * untwist z x ≠ 0 :=
  mul_ne_zero (Complex.ofReal_ne_zero.mpr hx) (Complex.exp_ne_zero _)

private theorem conjugated_deriv (z : ℂ) (g : Tests) :
    realPuncturedToSchwartz (realPuncturedWeilMultiplier z (realPuncturedTestDeriv g)) =
      realSchwartzEuler (realPuncturedToSchwartz (puncturedUntwist z g)) +
        z • realPuncturedToSchwartz (puncturedUntwist z g) := by
  ext x
  simp only [realPuncturedToSchwartz_apply, realSchwartzEuler_apply, add_apply, smul_apply, smul_eq_mul,
    puncturedUntwist, realPuncturedWeilMultiplier_apply, openTestMultiplier_apply, realPuncturedTestDeriv_apply]
  by_cases hx : x = 0
  · subst x
    have hg : g 0 = 0 := image_eq_zero_of_notMem_tsupport (fun hg => g.tsupport_subset hg rfl)
    simp [hg]
  · have hc : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx
    have he : (realPuncturedToSchwartz (openTestMultiplier (puncturedOpens ℝ) (untwist z)
        (untwist_contDiffOn z) g) : ℝ → ℂ) = fun x => untwist z x * g x := by
      funext x
      simp
    rw [he]
    have hh := ((hasDerivAt_untwist z hx).fun_mul
      (g.contDiff.differentiable (by simp) x).hasDerivAt).deriv
    rw [hh]
    field_simp
    ring

/-- A real dilation eigendistribution annihilates the conjugates of
derivatives of every compact test supported off zero. -/
theorem realWeilEigen_punctured_deriv (T : StrongDual ℂ Schwartz) (a : ℕ) (z : ℂ)
    (hcov : ∀ u f, T (archSchwartzDilation u f) = realArchUnitWeight a z u * T f)
    (g : Tests) :
    T (realPuncturedToSchwartz (realPuncturedWeilMultiplier z (realPuncturedTestDeriv g))) = 0 := by
  let f := realPuncturedToSchwartz (puncturedUntwist z g)
  have hf : HasCompactSupport f := by
    change HasCompactSupport (fun x => f x)
    simpa only [f, realPuncturedToSchwartz_apply] using (puncturedUntwist z g).hasCompactSupport
  rw [conjugated_deriv, map_add, map_smul, smul_eq_mul,
    realWeilEigen_Euler_compact T a z hcov f hf, neg_mul, neg_add_cancel]

/-- On the punctured line the weighted restriction of every real
eigendistribution depends only on the two half-line integrals. -/
theorem realWeilEigen_punctured_of_halfLine_integrals_zero
    (T : StrongDual ℂ Schwartz) (a : ℕ) (z : ℂ)
    (hcov : ∀ u f, T (archSchwartzDilation u f) = realArchUnitWeight a z u * T f)
    (g : Tests) (hpos : (∫ x in Ioi (0 : ℝ), g x) = 0)
    (hneg : (∫ x in Iio (0 : ℝ), g x) = 0) :
    T (realPuncturedToSchwartz (realPuncturedWeilMultiplier z g)) = 0 := by
  have hg : g ∈ range realPuncturedTestDeriv := by
    rw [realPuncturedTestDeriv_range]
    exact ⟨LinearMap.mem_ker.mpr (by simpa using hpos),
      LinearMap.mem_ker.mpr (by simpa using hneg)⟩
  obtain ⟨f, rfl⟩ := hg
  exact realWeilEigen_punctured_deriv T a z hcov f

private def reflectTest (f : Tests) : Tests :=
  ⟨fun x => f (-x), f.contDiff.comp contDiff_neg,
    f.hasCompactSupport.comp_homeomorph (Homeomorph.neg ℝ), by
      change tsupport ((f : ℝ → ℂ) ∘ Homeomorph.neg ℝ) ⊆ _
      rw [tsupport_comp_eq_preimage]
      intro x hx
      exact fun h => f.tsupport_subset hx (by simpa using h)⟩

private theorem reflectTest_Ioi (f : Tests) :
    (∫ x in Ioi (0 : ℝ), reflectTest f x) = ∫ x in Iio (0 : ℝ), f x := by
  have he := (Measure.measurePreserving_neg (volume : Measure ℝ)).setIntegral_preimage_emb
    (Homeomorph.neg ℝ).measurableEmbedding (f : ℝ → ℂ) (Iio (0 : ℝ))
  have hp : (fun x : ℝ => -x) ⁻¹' Iio 0 = Ioi 0 := by ext x; simp
  rw [hp] at he
  exact he

private theorem reflectTest_Iio (f : Tests) :
    (∫ x in Iio (0 : ℝ), reflectTest f x) = ∫ x in Ioi (0 : ℝ), f x := by
  have he := (Measure.measurePreserving_neg (volume : Measure ℝ)).setIntegral_preimage_emb
    (Homeomorph.neg ℝ).measurableEmbedding (f : ℝ → ℂ) (Ioi (0 : ℝ))
  have hp : (fun x : ℝ => -x) ⁻¹' Ioi 0 = Iio 0 := by ext x; simp
  rw [hp] at he
  exact he

private theorem exists_positive_punctured_reference :
    ∃ p : Tests, (∫ x in Ioi (0 : ℝ), p x) = 1 ∧
      (∫ x in Iio (0 : ℝ), p x) = 0 := by
  let b : ContDiffBump (1 : ℝ) := ⟨1/4, 1/2, by norm_num, by norm_num⟩
  let B : ℝ → ℂ := fun x => (b x : ℂ)
  have hBc : HasCompactSupport B := b.hasCompactSupport.comp_left Complex.ofReal_zero
  have hBpos : tsupport B ⊆ Ioi (0 : ℝ) := by
    apply (tsupport_comp_subset Complex.ofReal_zero b).trans
    rw [b.tsupport_eq, Real.closedBall_eq_Icc]
    intro x hx
    change 0 < x
    have he := hx.1
    dsimp [b] at he
    linarith
  let p : Tests := ⟨B, Complex.ofRealCLM.contDiff.comp b.contDiff, hBc,
    hBpos.trans fun x hx => fun h => hx.ne' h⟩
  let m := ∫ x, b x
  have hm : 0 < m := b.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    b.hasCompactSupport (fun _ => b.nonneg)
    (by rw [b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le)]; norm_num)
  have hmC : (m : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hm.ne'
  refine ⟨(m : ℂ)⁻¹ • p, ?_, ?_⟩
  · change (∫ x in Ioi (0 : ℝ), (m : ℂ)⁻¹ * B x) = 1
    rw [integral_const_mul, setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun x hx => image_eq_zero_of_notMem_tsupport (fun h => hx (hBpos h)))]
    rw [show (∫ x, B x) = (m : ℂ) from integral_complex_ofReal, inv_mul_cancel₀ hmC]
  · apply setIntegral_eq_zero_of_forall_eq_zero
    intro x hx
    change (m : ℂ)⁻¹ * B x = 0
    have hx' : x < 0 := hx
    rw [image_eq_zero_of_notMem_tsupport (fun h => lt_asymm hx' (hBpos h)), mul_zero]

private theorem multiplier_reflect (z : ℂ) (g : Tests) :
    realPuncturedToSchwartz (realPuncturedWeilMultiplier z (reflectTest g)) =
      -archSchwartzDilation (-1 : ℝˣ) (realPuncturedToSchwartz (realPuncturedWeilMultiplier z g)) := by
  ext x
  simp only [realPuncturedToSchwartz_apply, realPuncturedWeilMultiplier_apply, reflectTest,
    neg_apply, archSchwartzDilation_apply, inv_neg, inv_one, Units.val_neg, Units.val_one, mul_neg,
    mul_one, Complex.ofReal_neg, untwist, Real.log_neg_eq_log, neg_mul, neg_neg]
  rfl

/-- Including covariance under the sign unit leaves a single functional
on the punctured real line, determined by one positive-half-line sample. -/
theorem realWeilEigen_punctured_halfLine_formula (T : StrongDual ℂ Schwartz) (a : ℕ) (z : ℂ)
    (hcov : ∀ u f, T (archSchwartzDilation u f) = realArchUnitWeight a z u * T f) :
    ∃ c : ℂ, ∀ g : Tests,
      T (realPuncturedToSchwartz (realPuncturedWeilMultiplier z g)) =
        c * ((∫ x in Ioi (0 : ℝ), g x) - (-1 : ℂ) ^ a * ∫ x in Iio (0 : ℝ), g x) := by
  obtain ⟨p, hp_pos, hp_neg⟩ := exists_positive_punctured_reference
  let L := T.comp (realPuncturedToSchwartz.comp (realPuncturedWeilMultiplier z))
  have hm (g : Tests) : L (reflectTest g) = -((-1 : ℂ) ^ a * L g) := by
    change T (realPuncturedToSchwartz (realPuncturedWeilMultiplier z (reflectTest g))) = _
    rw [multiplier_reflect, map_neg, hcov]
    have hw : realArchUnitWeight a z (-1 : ℝˣ) = (-1 : ℂ) ^ a := by norm_num [realArchUnitWeight]
    rw [hw]
    rfl
  refine ⟨L p, fun g => ?_⟩
  let pos := realPuncturedTestIntegral (Ioi (0 : ℝ))
  let neg := realPuncturedTestIntegral (Iio (0 : ℝ))
  let q := g - pos g • p - neg g • reflectTest p
  have ho : pos q = 0 := by
    simp only [q, map_sub, map_smul, smul_eq_mul, pos, neg, realPuncturedTestIntegral_apply]
    rw [hp_pos, reflectTest_Ioi, hp_neg, mul_one, mul_zero, sub_self, sub_zero]
  have hi : neg q = 0 := by
    simp only [q, map_sub, map_smul, smul_eq_mul, pos, neg, realPuncturedTestIntegral_apply]
    rw [hp_neg, reflectTest_Iio, hp_pos, mul_zero, mul_one, sub_zero, sub_self]
  have hq : L q = 0 := realWeilEigen_punctured_of_halfLine_integrals_zero T a z hcov q
    (by simpa [pos] using ho) (by simpa [neg] using hi)
  simp only [q, map_sub, map_smul, smul_eq_mul, hm] at hq
  rw [← realPuncturedTestIntegral_apply, ← realPuncturedTestIntegral_apply]
  change L g = L p * (pos g - (-1 : ℂ) ^ a * neg g)
  linear_combination hq

private theorem realPuncturedWeilMultiplier_surjective (z : ℂ) :
    Surjective (realPuncturedWeilMultiplier z) :=
  (openTestMultiplierEquiv (puncturedOpens ℝ) (fun x : ℝ => (x : ℂ) * untwist z x)
    (Complex.ofRealCLM.contDiff.contDiffOn.mul (untwist_contDiffOn z))
    (realPuncturedWeilMultiplier_ne_zero z)).surjective

private theorem supported_at_zero_of_punctured_vanishing
    (T : StrongDual ℂ Schwartz) (z : ℂ)
    (h : ∀ g : Tests, T (realPuncturedToSchwartz (realPuncturedWeilMultiplier z g)) = 0) :
    Distribution.dsupport (⇑T) ⊆ {0} := by
  have hv : Distribution.IsVanishingOn (⇑T) ({0} : Set ℝ)ᶜ := by
    intro f hf
    obtain ⟨g, hg, hlim⟩ := exists_schwartz_compactSupport_sequence_subset f
    have hz (n : ℕ) : T (g n) = 0 := by
      let q : Tests := ⟨g n, (g n).smooth', (hg n).1, (hg n).2.trans hf⟩
      obtain ⟨r, hr⟩ := realPuncturedWeilMultiplier_surjective z q
      have hq : realPuncturedToSchwartz q = g n := by ext x; simp [q]
      simpa only [hr, hq] using h r
    have ht : Tendsto (fun n => T (g n)) atTop (𝓝 (T f)) := T.continuous.continuousAt.tendsto.comp hlim
    exact tendsto_nhds_unique ht (tendsto_const_nhds.congr (fun n => (hz n).symm))
  exact Set.subset_compl_iff_disjoint_left.mpr
    (hv.disjoint_dsupport isClosed_singleton.isOpen_compl) |>.trans (by simp)

/-- At every nonexceptional weight, the punctured-line formula and the
origin-supported classification together give the full real eigenspace. -/
theorem realWeilEigen_eq_normalized_of_nonexceptional
    (T : StrongDual ℂ Schwartz) (a : ℕ) (z : ℂ)
    (hreg : ¬ ∃ n : ℕ, z = -(n : ℂ) ∧ (-1 : ℂ) ^ a = (-1 : ℂ) ^ n)
    (hcov : ∀ u f, T (archSchwartzDilation u f) = realArchUnitWeight a z u * T f) :
    ∃ c : ℂ, T = c • realWeilNormalizedFamily a z := by
  let N := realWeilNormalizedFamily a z
  have hNcov : ∀ u f, N (archSchwartzDilation u f) = realArchUnitWeight a z u * N f :=
    fun u f => realWeilNormalizedFamily_dilate a u f z
  have hN : N ≠ 0 := by
    intro h
    have he : N (realGammaNormalized_distribution a).choose = 1 :=
      (realGammaNormalized_distribution a).choose_spec.choose_spec.2.2.1 z
    rw [h, zero_apply] at he
    exact zero_ne_one he
  obtain ⟨c, hc⟩ := realWeilEigen_punctured_halfLine_formula T a z hcov
  obtain ⟨d, hd⟩ := realWeilEigen_punctured_halfLine_formula N a z hNcov
  have hd₀ : d ≠ 0 := by
    intro he
    have hvan := supported_at_zero_of_punctured_vanishing N z (fun g => by rw [hd, he, zero_mul])
    obtain ⟨n, _, _, hz, hn, _⟩ := realSupportedWeilEigen_eq_jet N hvan hN a z hNcov
    exact hreg ⟨n, hz, hn⟩
  let U := T - (c / d) • N
  have hUcov : ∀ u f, U (archSchwartzDilation u f) = realArchUnitWeight a z u * U f := by
    intro u f
    change T (archSchwartzDilation u f) - (c / d) * N (archSchwartzDilation u f) =
      realArchUnitWeight a z u * (T f - (c / d) * N f)
    rw [hcov, hNcov]
    ring
  have hUvan := supported_at_zero_of_punctured_vanishing U z (fun g => by
    change T _ - (c / d) * N _ = 0
    rw [hc g, hd g, ← mul_assoc, div_mul_cancel₀ c hd₀, sub_self])
  have hU : U = 0 := by
    by_contra he
    obtain ⟨n, _, _, hz, hn, _⟩ := realSupportedWeilEigen_eq_jet U hUvan he a z hUcov
    exact hreg ⟨n, hz, hn⟩
  exact ⟨c / d, sub_eq_zero.mp hU⟩

private def signPower (n : ℕ) (x : ℝ) : ℂ :=
  if 0 < x then 1 else (-1 : ℂ) ^ n

private theorem signPower_smooth (n : ℕ) :
    ContDiffOn ℝ ∞ (signPower n) (puncturedOpens ℝ : Set ℝ) := by
  intro x hx
  have hx' : x ≠ 0 := hx
  rcases lt_or_gt_of_ne hx' with h | h
  · apply ContDiffAt.contDiffWithinAt
    apply (contDiffAt_const (c := (-1 : ℂ) ^ n)).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds h] with y hy
    simp [signPower, not_lt.mpr (show y ≤ 0 from (show y < 0 from hy).le)]
  · apply ContDiffAt.contDiffWithinAt
    apply (contDiffAt_const (c := (1 : ℂ))).congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds h] with y hy
    simp [signPower, show 0 < y from hy]

private theorem exceptional_multiplier (n : ℕ) {x : ℝ} (hx : x ≠ 0) :
    ((x : ℂ) * untwist (-(n : ℂ)) x) * signPower n x = (x : ℂ) ^ (n + 1) := by
  have he : untwist (-(n : ℂ)) x = ((|x| : ℝ) : ℂ) ^ n := by
    rw [untwist, neg_neg, ← Real.log_abs, Complex.exp_nat_mul, ← Complex.ofReal_exp,
      Real.exp_log (abs_pos.mpr hx)]
  rw [he, pow_succ]
  rcases lt_or_gt_of_ne hx with h | h
  · rw [signPower, ite_eq_right (not_lt.mpr h.le), abs_of_neg h, Complex.ofReal_neg]
    calc
      _ = (x : ℂ) * ((-(x : ℂ)) ^ n * (-1 : ℂ) ^ n) := by ring
      _ = _ := by rw [← mul_pow, mul_neg_one, neg_neg, mul_comm]
  · rw [signPower, ite_eq_left h, abs_of_pos h, mul_one, mul_comm]

private theorem exceptional_sample
    (T : StrongDual ℂ Schwartz) (a n : ℕ) (hp : (-1 : ℂ) ^ a = (-1 : ℂ) ^ n)
    (hcov : ∀ u f, T (archSchwartzDilation u f) =
      realArchUnitWeight a (-(n : ℂ)) u * T f) :
    Distribution.dsupport (⇑T) ⊆ {0} := by
  obtain ⟨c, hc⟩ := realWeilEigen_punctured_halfLine_formula T a (-(n : ℂ)) hcov
  let b : ContDiffBump (0 : ℝ) := ⟨1/2, 1, by norm_num, by norm_num⟩
  let Bf : ℝ → ℂ := fun x => (b x : ℂ)
  have hBc : HasCompactSupport Bf := b.hasCompactSupport.comp_left Complex.ofReal_zero
  let B : Schwartz := hBc.toSchwartzMap (Complex.ofRealCLM.contDiff.comp b.contDiff)
  have hB (x : ℝ) : B x = Bf x := rfl
  have hB1 : B 0 = 1 := by
    rw [hB, show Bf 0 = ((b 0 : ℝ) : ℂ) from rfl,
      b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le), Complex.ofReal_one]
  have hBc' : HasCompactSupport B := hBc
  let D := SchwartzMap.derivCLM ℂ ℂ B
  have hD (x : ℝ) : D x = deriv (B : ℝ → ℂ) x := SchwartzMap.derivCLM_apply ℂ B x
  have hDc : HasCompactSupport D := hBc'.deriv
  have hD0 : (0 : ℝ) ∉ tsupport D := by
    apply notMem_tsupport_iff_eventuallyEq.mpr
    have hb : (B : ℝ → ℂ) =ᶠ[𝓝 0] fun _ => 1 := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) b.rIn_pos] with x hx
      rw [hB, show Bf x = ((b x : ℝ) : ℂ) from rfl,
        b.one_of_mem_closedBall (Metric.ball_subset_closedBall hx), Complex.ofReal_one]
    filter_upwards [hb.eventuallyEq_nhds] with x hx
    rw [hD, hx.deriv_eq, deriv_const]
    rfl
  let d : Tests := ⟨D, D.smooth', hDc, fun x hx h => hD0 (by simpa only [mem_singleton_iff.mp h] using hx)⟩
  let g := openTestMultiplier (puncturedOpens ℝ) (signPower n) (signPower_smooth n) d
  have hg (x : ℝ) : g x = signPower n x * deriv (B : ℝ → ℂ) x :=
    congrArg (signPower n x * ·) (hD x)
  have hi_pos : (∫ x in Ioi (0 : ℝ), g x) = -1 := by
    rw [← hB1, ← HasCompactSupport.integral_Ioi_deriv_eq (B.smooth 1) hBc']
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    rw [hg, signPower, ite_eq_left (show 0 < x from hx), one_mul]
  have hi_neg : (∫ x in Iio (0 : ℝ), g x) = (-1 : ℂ) ^ n := by
    calc
      _ = ∫ x in Iio (0 : ℝ), (-1 : ℂ) ^ n * deriv (B : ℝ → ℂ) x := by
        apply setIntegral_congr_fun measurableSet_Iio
        intro x hx
        rw [hg, signPower, ite_eq_right (show ¬0 < x from not_lt_of_ge hx.le)]
      _ = _ := by
        rw [integral_const_mul, setIntegral_congr_set Iio_ae_eq_Iic,
          HasCompactSupport.integral_Iic_deriv_eq (B.smooth 1) hBc', hB1, mul_one]
  let f := SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => (x : ℂ) ^ n) B
  have hf (x : ℝ) : f x = (x : ℂ) ^ n * B x := by
    have hh : Function.HasTemperateGrowth (fun x : ℝ => (x : ℂ) ^ n) :=
      Complex.hasTemperateGrowth_ofReal.pow n
    unfold f
    rw [SchwartzMap.smulLeftCLM_apply_apply hh, smul_eq_mul]
  have hfc : HasCompactSupport f := by
    rw [funext hf]
    change HasCompactSupport ((fun x : ℝ => (x : ℂ) ^ n) * (B : ℝ → ℂ))
    exact hBc'.mul_left
  have hEuler : realSchwartzEuler f - (n : ℂ) • f =
      realPuncturedToSchwartz (realPuncturedWeilMultiplier (-(n : ℂ)) g) := by
    ext x
    simp only [sub_apply, smul_apply, smul_eq_mul, realSchwartzEuler_apply, realPuncturedToSchwartz_apply,
      realPuncturedWeilMultiplier_apply, hf, hg]
    have hb : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 x := by simpa using (hasDerivAt_id x).ofReal_comp
    rw [funext hf, ((hb.fun_pow n).fun_mul (B.differentiableAt.hasDerivAt)).deriv]
    by_cases hx : x = 0
    · subst x
      cases n <;> simp
    · rw [← mul_assoc ((x : ℂ) * untwist (-(n : ℂ)) x), exceptional_multiplier n hx]
      cases n with
      | zero => simp
      | succ n => simp only [Nat.succ_sub_one, pow_succ]; ring
  have ht : T (realPuncturedToSchwartz (realPuncturedWeilMultiplier (-(n : ℂ)) g)) = 0 := by
    rw [← hEuler, map_sub, map_smul, smul_eq_mul,
      realWeilEigen_Euler_compact T a _ hcov f hfc, neg_neg, sub_self]
  rw [hc g, hi_pos, hi_neg, hp, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow] at ht
  have hc₀ : c = 0 := (mul_eq_zero.mp ht).resolve_right (by norm_num)
  exact supported_at_zero_of_punctured_vanishing T (-(n : ℂ)) (fun x => by rw [hc, hc₀, zero_mul])

/-- Every real eigendistribution is a multiple of the normalized family,
including at exceptional parameters where only its point jet survives. -/
theorem realWeilEigen_eq_normalized
    (T : StrongDual ℂ Schwartz) (a : ℕ) (z : ℂ)
    (hcov : ∀ u f, T (archSchwartzDilation u f) = realArchUnitWeight a z u * T f) :
    ∃ c : ℂ, T = c • realWeilNormalizedFamily a z := by
  by_cases he : ∃ n : ℕ, z = -(n : ℂ) ∧ (-1 : ℂ) ^ a = (-1 : ℂ) ^ n
  · obtain ⟨n, rfl, hp⟩ := he
    by_cases hT : T = 0
    · exact ⟨0, hT.trans (zero_smul ℂ (realWeilNormalizedFamily a (-(n : ℂ)))).symm⟩
    obtain ⟨c, _, hc⟩ := realSupportedWeilEigen_eq_normalized T
      (exceptional_sample T a n hp hcov) hT a _ hcov
    exact ⟨c, hc⟩
  · exact realWeilEigen_eq_normalized_of_nonexceptional T a z he hcov

/-- The real local zeta eigenspace at a sign character and a spectral parameter. -/
def realWeilEigenspace (a : ℕ) (z : ℂ) : Submodule ℂ (StrongDual ℂ Schwartz) where
  carrier := {T | ∀ u f, T (archSchwartzDilation u f) = realArchUnitWeight a z u * T f}
  zero_mem' := by intro u f; simp
  add_mem' {T U} hT hU := by
    intro u f
    change T (archSchwartzDilation u f) + U (archSchwartzDilation u f) =
      realArchUnitWeight a z u * (T f + U f)
    rw [hT u f, hU u f, mul_add]
  smul_mem' c T hT := by
    intro u f
    change c * T (archSchwartzDilation u f) = realArchUnitWeight a z u * (c * T f)
    rw [hT u f, mul_left_comm]

/-- Evaluation on the Gaussian reference is a linear coordinate at every
real local parameter, including the exceptional jets. -/
def realWeilEigenspace_equiv (a : ℕ) (z : ℂ) : realWeilEigenspace a z ≃ₗ[ℂ] ℂ := by
  let f₀ := (realGammaNormalized_distribution a).choose
  let N : realWeilEigenspace a z :=
    ⟨realWeilNormalizedFamily a z, fun u f => realWeilNormalizedFamily_dilate a u f z⟩
  have hN : N.val f₀ = 1 :=
    (realGammaNormalized_distribution a).choose_spec.choose_spec.2.2.1 z
  refine
    { toFun := fun T => T.val f₀
      invFun := fun c => c • N
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := ?_
      right_inv := ?_ }
  · intro T
    obtain ⟨c, hc⟩ := realWeilEigen_eq_normalized T.val a z T.property
    apply Subtype.ext
    change T.val f₀ • N.val = T.val
    have he : T.val f₀ = c := by
      rw [hc]
      change c * N.val f₀ = c
      rw [hN, mul_one]
    rw [he]
    exact hc.symm
  · intro c
    change c * N.val f₀ = c
    rw [hN, mul_one]

theorem realWeilEigenspace_finrank (a : ℕ) (z : ℂ) :
    Module.finrank ℂ (realWeilEigenspace a z) = 1 :=
  (realWeilEigenspace_equiv a z).finrank_eq.trans (Module.finrank_self ℂ)

end
end Masullo
