import PuncturedTestMultipliers
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

open Filter Function Set TopologicalSpace Topology MeasureTheory
open scoped ContDiff Distributions

namespace Masullo

noncomputable section

private abbrev Tests := 𝓓(puncturedOpens ℝ, ℂ)

/-- Ordinary differentiation on the real punctured compact-test space. -/
def realPuncturedTestDeriv : Tests →L[ℂ] Tests := TestFunction.lineDerivCLM ℂ 1

@[simp] theorem realPuncturedTestDeriv_apply (f : Tests) (x : ℝ) :
    realPuncturedTestDeriv f x = deriv (f : ℝ → ℂ) x := by
  rw [realPuncturedTestDeriv, TestFunction.lineDerivCLM_eq_fderivCLM,
    TestFunction.fderivCLM_apply, ite_eq_left le_top, deriv]

/-- The bundled derivative powers evaluate to ordinary iterated derivatives. -/
theorem realPuncturedTestDeriv_pow_apply (m : ℕ) (f : Tests) (x : ℝ) :
    (realPuncturedTestDeriv ^ m : Tests →L[ℂ] Tests) f x =
      iteratedDeriv m (f : ℝ → ℂ) x := by
  induction m generalizing f with
  | zero => simp [iteratedDeriv_zero]
  | succ m ih =>
    rw [pow_succ, ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply, ih,
      iteratedDeriv_succ']
    congr 1

private theorem puncturedTest_zero (f : Tests) (x : ℝ)
    (hx : x ∉ tsupport f) : f x = 0 :=
  image_eq_zero_of_notMem_tsupport hx

private theorem puncturedTest_zero_at_origin (f : Tests) : f 0 = 0 :=
  puncturedTest_zero f 0 (fun h ↦ f.tsupport_subset h rfl)

/-- Integration over a fixed measurable region, bundled on compact tests. -/
def realPuncturedTestIntegral (s : Set ℝ) : Tests →L[ℂ] ℂ :=
  TestFunction.integralAgainstBilinCLM (ContinuousLinearMap.mul ℂ ℂ)
    (volume.restrict s) (fun _ ↦ (1 : ℂ))

@[simp] theorem realPuncturedTestIntegral_apply (s : Set ℝ) (f : Tests) :
    realPuncturedTestIntegral s f = ∫ x in s, f x := by
  rw [realPuncturedTestIntegral, TestFunction.integralAgainstBilinCLM_eq_integral
    (locallyIntegrableOn_const (1 : ℂ))]
  simp

private theorem puncturedPrimitive_tsupport (f : Tests) (hpos : (∫ x in Ioi 0, f x) = 0)
    (hneg : (∫ x in Iio 0, f x) = 0) :
    let g : ℝ → ℂ := fun y ↦ ∫ x in (0 : ℝ)..y, f x
    HasCompactSupport g ∧ tsupport g ⊆ (puncturedOpens ℝ : Set ℝ) := by
  let g : ℝ → ℂ := fun y ↦ ∫ x in (0 : ℝ)..y, f x
  have h0 : (0 : ℝ) ∉ tsupport f := fun h ↦ f.tsupport_subset h rfl
  obtain ⟨ε, hε, hεf⟩ := Metric.mem_nhds_iff.mp ((isClosed_tsupport _).isOpen_compl.mem_nhds h0)
  have hg0 : g =ᶠ[𝓝 0] 0 := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hε] with y hy
    change (∫ x in (0 : ℝ)..y, f x) = 0
    refine (intervalIntegral.integral_congr (g := fun _ ↦ (0 : ℂ)) ?_).trans
      intervalIntegral.integral_zero
    intro x hx
    apply puncturedTest_zero f x
    apply hεf
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hy ⊢
    rw [mem_uIcc] at hx
    rw [abs_lt] at hy ⊢
    rcases hx with hx | hx <;> constructor <;> linarith [hx.1, hx.2]
  have hgs : tsupport g ⊆ (puncturedOpens ℝ : Set ℝ) := by
    intro x hx hx'
    have he : x = 0 := hx'
    subst x
    exact (notMem_tsupport_iff_eventuallyEq.mpr hg0) hx
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_ball (0 : ℝ)).mp f.hasCompactSupport.isBounded
  let r := max R 1
  have hr : 0 < r := zero_lt_one.trans_le (le_max_right _ _)
  have hs : tsupport f ⊆ Metric.ball (0 : ℝ) r := hR.trans (Metric.ball_subset_ball (le_max_left _ _))
  have hz (x : ℝ) (hx : r ≤ |x|) : f x = 0 := puncturedTest_zero f x fun h ↦ by
    have hl := hs h
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hl
    exact (not_lt_of_ge hx) hl
  refine ⟨(isCompact_Icc (a := -r) (b := r)).of_isClosed_subset (isClosed_tsupport _)
    (closure_minimal ?_ isClosed_Icc), hgs⟩
  intro y hy
  by_contra! hn
  rcases not_and_or.mp hn with hl | hh
  · have hy' : y ≤ 0 := by linarith [hr]
    have hset : (∫ x in Iio 0, f x) = ∫ x in Ioo y 0, f x :=
      setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Iio
        (fun _ hx ↦ hx.2) (fun x hx ↦ hz x (by
          have hxy : x ≤ y := le_of_not_gt (fun hxy ↦ hx.2 ⟨hxy,hx.1⟩)
          rw [abs_of_nonpos (le_of_lt hx.1)]
          linarith))
    apply hy
    change (∫ x in (0 : ℝ)..y, f x) = 0
    rw [intervalIntegral.integral_of_ge hy', ← setIntegral_congr_set Ioo_ae_eq_Ioc, ← hset, hneg, neg_zero]
  · have hy' : 0 ≤ y := by linarith [hr]
    have hset : (∫ x in Ioi 0, f x) = ∫ x in Ioc 0 y, f x :=
      setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
        (fun _ hx ↦ hx.1) (fun x hx ↦ hz x (by
          have hyx : y < x := lt_of_not_ge (fun hyx ↦ hx.2 ⟨hx.1,hyx⟩)
          rw [abs_of_pos hx.1]
          linarith))
    apply hy
    change (∫ x in (0 : ℝ)..y, f x) = 0
    rw [intervalIntegral.integral_of_le hy', ← hset, hpos]

private theorem exists_realPuncturedPrimitive (f : Tests)
    (hpos : (∫ x in Ioi 0, f x) = 0) (hneg : (∫ x in Iio 0, f x) = 0) :
    ∃ g : Tests, realPuncturedTestDeriv g = f := by
  let g : ℝ → ℂ := fun y ↦ ∫ x in (0 : ℝ)..y, f x
  have hd (x : ℝ) : HasDerivAt g (f x) x :=
    intervalIntegral.integral_hasDerivAt_right (f.continuous.intervalIntegrable _ _)
      f.continuous.aestronglyMeasurable.stronglyMeasurableAtFilter f.continuous.continuousAt
  have he : deriv g = (f : ℝ → ℂ) := funext fun x ↦ (hd x).deriv
  have hc : ContDiff ℝ ∞ g := contDiff_infty_iff_deriv.mpr
    ⟨fun x ↦ (hd x).differentiableAt, he.symm ▸ f.contDiff⟩
  obtain ⟨hgc, hgΩ⟩ := puncturedPrimitive_tsupport f hpos hneg
  refine ⟨⟨g, hc, hgc, hgΩ⟩, ?_⟩
  ext x
  rw [realPuncturedTestDeriv_apply]
  exact (hd x).deriv

/-- The real derivative image on punctured compact tests consists
exactly of tests of integral zero on each of the two half-lines. -/
theorem realPuncturedTestDeriv_range :
    range realPuncturedTestDeriv =
      ((realPuncturedTestIntegral (Ioi 0)).ker : Set Tests) ∩ ((realPuncturedTestIntegral (Iio 0)).ker : Set Tests) := by
  ext f
  constructor
  · rintro ⟨g, rfl⟩
    let h := realPuncturedTestDeriv g
    have hzero (x : ℝ) (hx : x ∉ tsupport g) : h x = 0 := by
      have he := notMem_tsupport_iff_eventuallyEq.mp hx
      rw [realPuncturedTestDeriv_apply, he.deriv_eq, deriv_zero]
      rfl
    obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_ball (0 : ℝ)).mp g.hasCompactSupport.isBounded
    let R := max r 1
    have hR : 0 < R := zero_lt_one.trans_le (le_max_right _ _)
    have hgs : tsupport g ⊆ Metric.ball (0 : ℝ) R := hr.trans (Metric.ball_subset_ball (le_max_left _ _))
    have hn (x : ℝ) (hx : R ≤ |x|) : x ∉ tsupport g := fun h' ↦ by
      have ht := hgs h'
      rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at ht
      exact (not_lt_of_ge hx) ht
    have hder (a b : ℝ) : (∫ x in a..b, h x) = g b - g a := by
      apply intervalIntegral.integral_deriv_eq_sub' (g : ℝ → ℂ)
        (funext fun x ↦ (realPuncturedTestDeriv_apply g x).symm)
      · exact fun x _ ↦ (g.contDiff.differentiable (by simp)).differentiableAt
      · exact h.continuous.continuousOn
    constructor
    · change realPuncturedTestIntegral (Ioi 0) h = 0
      rw [realPuncturedTestIntegral_apply,
        setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
          (show Ioc 0 R ⊆ Ioi 0 from Ioc_subset_Ioi_self) (fun x hx ↦ hzero x (hn x (by
          rw [abs_of_pos hx.1]
          exact le_of_lt (lt_of_not_ge fun hxR ↦ hx.2 ⟨hx.1,hxR⟩)))),
        ← intervalIntegral.integral_of_le hR.le, hder,
        puncturedTest_zero g R (hn _ (by rw [abs_of_pos hR])), puncturedTest_zero_at_origin, sub_self]
    · change realPuncturedTestIntegral (Iio 0) h = 0
      rw [realPuncturedTestIntegral_apply,
        setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Iio
          (show Ioo (-R) 0 ⊆ Iio 0 from Ioo_subset_Iio_self) (fun x hx ↦ hzero x (hn x (by
          rw [abs_of_neg hx.1]
          have hxR : x ≤ -R := le_of_not_gt fun hxR ↦ hx.2 ⟨hxR,hx.1⟩
          linarith))),
        setIntegral_congr_set Ioo_ae_eq_Ioc, ← intervalIntegral.integral_of_le (by linarith : -R ≤ 0),
        hder, puncturedTest_zero_at_origin,
        puncturedTest_zero g (-R) (hn _ (by rw [abs_neg, abs_of_pos hR])), sub_self]
  · rintro ⟨hpos, hneg⟩
    apply exists_realPuncturedPrimitive f
    · rw [← realPuncturedTestIntegral_apply]
      exact LinearMap.mem_ker.mp hpos
    · rw [← realPuncturedTestIntegral_apply]
      exact LinearMap.mem_ker.mp hneg

theorem realPuncturedTestDeriv_isClosed_range : IsClosed (range realPuncturedTestDeriv) := by
  rw [realPuncturedTestDeriv_range]
  exact (realPuncturedTestIntegral _).isClosed_ker.inter (realPuncturedTestIntegral _).isClosed_ker

private def puncturedPowerMul (n : ℕ) : Tests →L[ℂ] Tests :=
  openTestMultiplier _ (fun x ↦ (x : ℂ) ^ n)
    (Complex.ofRealCLM.contDiff.pow n).contDiffOn

/-- The degree-n moment of a compact test on a half-line, as a continuous
linear functional for the LF topology. -/
def realPuncturedTestMoment (s : Set ℝ) (n : ℕ) : Tests →L[ℂ] ℂ :=
  (realPuncturedTestIntegral s).comp (puncturedPowerMul n)

@[simp] theorem realPuncturedTestMoment_apply (s : Set ℝ) (n : ℕ) (f : Tests) :
    realPuncturedTestMoment s n f = ∫ x in s, (x : ℂ) ^ n * f x := by
  rw [realPuncturedTestMoment, ContinuousLinearMap.comp_apply, realPuncturedTestIntegral_apply]
  rfl

private theorem realPuncturedTestMoment_zero (s : Set ℝ) (f : Tests) :
    realPuncturedTestMoment s 0 f = realPuncturedTestIntegral s f := by
  simp [realPuncturedTestIntegral_apply]

private theorem realPuncturedTestIntegral_deriv (s : Set ℝ) (hs : s = Ioi 0 ∨ s = Iio 0) (g : Tests) :
    realPuncturedTestIntegral s (realPuncturedTestDeriv g) = 0 := by
  have hg : realPuncturedTestDeriv g ∈ range realPuncturedTestDeriv := mem_range_self g
  rw [realPuncturedTestDeriv_range] at hg
  rcases hs with rfl | rfl
  · exact LinearMap.mem_ker.mp hg.1
  · exact LinearMap.mem_ker.mp hg.2

private theorem realPuncturedTestMoment_deriv_succ (s : Set ℝ) (hs : s = Ioi 0 ∨ s = Iio 0)
    (n : ℕ) (g : Tests) :
    realPuncturedTestMoment s (n+1) (realPuncturedTestDeriv g) =
      -((n : ℂ) + 1) * realPuncturedTestMoment s n g := by
  have hd : realPuncturedTestDeriv (puncturedPowerMul (n+1) g) =
      ((n : ℂ) + 1) • puncturedPowerMul n g + puncturedPowerMul (n+1) (realPuncturedTestDeriv g) := by
    ext x
    have hcastF : HasFDerivAt (fun y : ℝ ↦ (y : ℂ)) Complex.ofRealCLM x :=
      Complex.ofRealCLM.hasFDerivAt
    have hcast : HasDerivAt (fun y : ℝ ↦ (y : ℂ)) 1 x := by simpa using hcastF.hasDerivAt
    have hpow : HasDerivAt (fun y : ℝ ↦ (y : ℂ) ^ (n+1))
        (((n : ℂ) + 1) * (x : ℂ) ^ n) x := by
      simpa using (hcast.fun_pow (n+1))
    have he := (hpow.mul ((g.contDiff.differentiable (by simp)).differentiableAt.hasDerivAt)).deriv
    change realPuncturedTestDeriv (puncturedPowerMul (n+1) g) x =
      ((n : ℂ) + 1) * ((x : ℂ) ^ n * g x) + (x : ℂ) ^ (n+1) * realPuncturedTestDeriv g x
    rw [realPuncturedTestDeriv_apply, realPuncturedTestDeriv_apply]
    change deriv (fun y : ℝ ↦ (y : ℂ) ^ (n+1) * g y) x = _
    exact he.trans (by ring)
  have hz := realPuncturedTestIntegral_deriv s hs (puncturedPowerMul (n+1) g)
  rw [hd, map_add, map_smul, smul_eq_mul] at hz
  change (n + 1 : ℂ) * realPuncturedTestMoment s n g +
      realPuncturedTestMoment s (n+1) (realPuncturedTestDeriv g) = 0 at hz
  linear_combination hz

/-- The m-th derivative range is the common kernel of the first m moments
on each half-line. The statement includes m=0. -/
theorem realPuncturedTestDeriv_pow_range (m : ℕ) :
    range (realPuncturedTestDeriv ^ m : Tests →L[ℂ] Tests) =
      {f | ∀ s : Set ℝ, (s = Ioi 0 ∨ s = Iio 0) →
        ∀ j < m, realPuncturedTestMoment s j f = 0} := by
  induction m with
  | zero =>
    ext f
    simp
  | succ m ih =>
    ext f
    rw [pow_succ', ContinuousLinearMap.mul_def, ContinuousLinearMap.coe_comp, range_comp, ih]
    constructor
    · rintro ⟨g, hg, rfl⟩
      change ∀ s : Set ℝ, (s = Ioi 0 ∨ s = Iio 0) →
        ∀ j < m+1, realPuncturedTestMoment s j (realPuncturedTestDeriv g) = 0
      intro s hs j hj
      cases j with
      | zero => rw [realPuncturedTestMoment_zero]; exact realPuncturedTestIntegral_deriv s hs g
      | succ j =>
        rw [realPuncturedTestMoment_deriv_succ s hs, hg s hs j (by omega), mul_zero]
    · intro hf
      have hz (s : Set ℝ) (hs : s = Ioi 0 ∨ s = Iio 0) : (∫ x in s, f x) = 0 := by
        rw [← realPuncturedTestIntegral_apply, ← realPuncturedTestMoment_zero]
        exact hf s hs 0 (by omega)
      obtain ⟨g, rfl⟩ := exists_realPuncturedPrimitive f (hz _ (Or.inl rfl)) (hz _ (Or.inr rfl))
      refine ⟨g, ?_, rfl⟩
      intro s hs j hj
      have he := hf s hs (j+1) (by omega)
      rw [realPuncturedTestMoment_deriv_succ s hs] at he
      have hj' : (j : ℂ) + 1 ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero j)
      exact (mul_eq_zero.mp he).resolve_left (neg_ne_zero.mpr hj')

/-- Every ordinary derivative power has closed range on the punctured
real compact-test space. -/
theorem realPuncturedTestDeriv_pow_isClosed_range (m : ℕ) :
    IsClosed (range (realPuncturedTestDeriv ^ m : Tests →L[ℂ] Tests)) := by
  rw [realPuncturedTestDeriv_pow_range]
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun s ↦ isClosed_iInter fun _ ↦ isClosed_iInter fun j ↦
    isClosed_iInter fun _ ↦ isClosed_eq (realPuncturedTestMoment s j).continuous continuous_const

end
end Masullo
