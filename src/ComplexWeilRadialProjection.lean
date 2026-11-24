import ArchimedeanMellinMonomials
import ComplexWeilAngularProjection
import Mathlib.MeasureTheory.Group.Integral

open Function MeasureTheory Set Topology
open scoped Classical ENat SchwartzMap

namespace Masullo

noncomputable section

private abbrev ComplexTests := 𝓢(ℂ, ℂ)
private abbrev RealTests := 𝓢(ℝ, ℂ)

attribute [local instance] complexZeta_circleMeasurable complexZeta_circleBorel

private theorem normSq_temperate : (Complex.normSq : ℂ → ℝ).HasTemperateGrowth := by
  have h : Complex.normSq = fun x => Complex.reCLM x ^ 2 + Complex.imCLM x ^ 2 := by
    funext x
    simp [Complex.normSq_apply, pow_two]
  rw [h]
  exact
    (Complex.reCLM.hasTemperateGrowth.pow 2).add (Complex.imCLM.hasTemperateGrowth.pow 2)

private theorem normSq_growth : ∃ (k : ℕ) (C : ℝ),
    ∀ x : ℂ, ‖x‖ ≤ C * (1 + ‖Complex.normSq x‖) ^ k := by
  refine ⟨1, 1, fun x => ?_⟩
  rw [one_mul, pow_one, Real.norm_eq_abs, abs_of_nonneg (Complex.normSq_nonneg x),
    ← Complex.sq_norm]
  nlinarith [sq_nonneg (‖x‖ - 1)]

/-- Lift a squared-radius profile into the angular mode selected by the character. -/
def complexWeilRadialLift (m : ℤ) : RealTests →L[ℂ] ComplexTests :=
  (complexMellinMonomial (-m).toNat m.toNat).comp
    (SchwartzMap.compCLM ℂ normSq_temperate normSq_growth)

@[simp] theorem complexWeilRadialLift_apply (m : ℤ) (f : RealTests) (x : ℂ) :
    complexWeilRadialLift m f x =
      (x ^ (-m).toNat * star x ^ m.toNat) * f (Complex.normSq x) := by
  exact complexMellinMonomial_apply _ _ _ _

/-- Left invariance gives the angular transformation law at every radius. -/
theorem complexAngularAverage_rotate (μ : Measure Circle) [μ.IsMulLeftInvariant]
    (m : ℤ) (f : ComplexTests) (x : ℂ) (w : Circle) :
    (∫ u : Circle, (u : ℂ) ^ m * f ((x * (w : ℂ)) * (u : ℂ)) ∂μ) =
      (w : ℂ) ^ (-m) * ∫ u : Circle, (u : ℂ) ^ m * f (x * (u : ℂ)) ∂μ := by
  rw [← integral_const_mul]
  rw [← integral_mul_left_eq_self (fun u : Circle =>
    (w : ℂ) ^ (-m) * ((u : ℂ) ^ m * f (x * (u : ℂ)))) w]
  congr 1
  funext u
  simp only [Circle.coe_mul, mul_zpow, ← mul_assoc, ← zpow_add₀ (Circle.coe_ne_zero w),
    neg_add_cancel, zpow_zero, one_mul]

private theorem radialMonomial (m : ℤ) (r : ℝ) (w : Circle) :
    ((r : ℂ) * (w : ℂ)) ^ (-m).toNat * star ((r : ℂ) * (w : ℂ)) ^ m.toNat =
      (r : ℂ) ^ m.natAbs * (w : ℂ) ^ (-m) := by
  rw [star_mul', Complex.star_def, Complex.conj_ofReal, ← Circle.coe_inv_eq_conj, Circle.coe_inv]
  cases m with
  | ofNat n =>
    simp [mul_pow, inv_pow, zpow_neg]
  | negSucc n =>
    have hz : (w : ℂ) ^ ((n : ℤ) + 1) = (w : ℂ) ^ (n + 1 : ℕ) := by
      rw [← Int.natCast_succ, zpow_natCast]
    simp [mul_pow, hz]

private theorem angularAverage_eq_zero_of_norm (μ : Measure Circle) (m : ℤ)
    (f : ComplexTests) (x : ℂ) (hf : ∀ y : ℂ, ‖y‖ = ‖x‖ → f y = 0) :
    (∫ u : Circle, (u : ℂ) ^ m * f (x * (u : ℂ)) ∂μ) = 0 := by
  have h : (fun u : Circle => (u : ℂ) ^ m * f (x * (u : ℂ))) = 0 := by
    funext u
    rw [hf _ (by rw [norm_mul, Circle.norm_coe, mul_one]), mul_zero]
    rfl
  rw [h, integral_zero']

private theorem exists_squaredRadiusProfile (m : ℤ) (g : ComplexTests)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hzero : ∀ x : ℂ, ‖x‖ < a ∨ b < ‖x‖ → g x = 0)
    (hrotate : ∀ x (w : Circle), g (x * (w : ℂ)) = (w : ℂ) ^ (-m) * g x) :
    ∃ h : RealTests, HasCompactSupport h ∧ tsupport h ⊆ Ioi 0 ∧
      complexWeilRadialLift m h = g := by
  let root : ℝ → ℂ := fun t => (Real.sqrt t : ℂ)
  let profile : ℝ → ℂ := fun t => g (root t) * (root t)⁻¹ ^ m.natAbs
  have hnorm (t : ℝ) : ‖root t‖ = Real.sqrt t := by
    dsimp [root]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg t)]
  have hsmall (t : ℝ) (ht : t < a ^ 2) : profile t = 0 := by
    dsimp only [profile]
    rw [hzero _ (.inl (by rw [hnorm]; exact (Real.sqrt_lt' ha).2 ht)), zero_mul]
  have hlarge (t : ℝ) (ht : b ^ 2 < t) : profile t = 0 := by
    dsimp only [profile]
    have hh : b < ‖root t‖ := by
      rw [hnorm]
      exact lt_of_not_ge (fun h => ht.not_ge ((Real.sqrt_le_left hb.le).1 h))
    rw [hzero _ (.inr hh), zero_mul]
  have hsubset : tsupport profile ⊆ Icc (a ^ 2) (b ^ 2) := by
    apply closure_minimal _ isClosed_Icc
    intro t ht
    exact ⟨le_of_not_gt (fun h => ht (hsmall t h)), le_of_not_gt (fun h => ht (hlarge t h))⟩
  have hcompact : HasCompactSupport profile :=
    isCompact_Icc.of_isClosed_subset isClosed_closure hsubset
  have hsmooth : ContDiff ℝ (⊤ : ℕ∞) profile := by
    apply contDiff_iff_contDiffAt.mpr
    intro t
    by_cases ht : 0 < t
    · have hr : ContDiffAt ℝ (⊤ : ℕ∞) root t :=
        Complex.ofRealCLM.contDiff.contDiffAt.comp t (Real.contDiffAt_sqrt ht.ne')
      have hrne : root t ≠ 0 := by
        simpa [root] using (Real.sqrt_pos.2 ht).ne'
      exact (g.smooth'.contDiffAt.comp t hr).mul ((hr.inv hrne).pow _)
    · apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
      filter_upwards [Iio_mem_nhds (lt_of_le_of_lt (le_of_not_gt ht) (sq_pos_of_pos ha))]
        with u hu
      exact hsmall u hu
  let h : RealTests := hcompact.toSchwartzMap hsmooth
  refine ⟨h, hcompact, fun t ht => lt_of_lt_of_le (sq_pos_of_pos ha) (hsubset ht).1, ?_⟩
  ext x
  by_cases hx : x = 0
  · subst x
    rw [complexWeilRadialLift_apply, Complex.normSq_zero,
      show h 0 = 0 from hsmall 0 (sq_pos_of_pos ha), mul_zero]
    exact (hzero 0 (.inl (by simpa using ha))).symm
  · let r := ‖x‖
    have hr : 0 < r := norm_pos_iff.mpr hx
    have hrne : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    let w : Circle := ⟨x / (r : ℂ), mem_sphere_zero_iff_norm.mpr (by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, div_self hr.ne'])⟩
    have hw : (r : ℂ) * (w : ℂ) = x := by
      change (r : ℂ) * (x / (r : ℂ)) = x
      field_simp
    have hroot : root (Complex.normSq x) = (r : ℂ) := by
      dsimp only [root]
      rw [← Complex.sq_norm, Real.sqrt_sq (norm_nonneg x)]
    rw [complexWeilRadialLift_apply, show h (Complex.normSq x) = profile (Complex.normSq x) from rfl]
    dsimp only [profile]
    rw [hroot, ← hw, radialMonomial, hrotate, inv_pow]
    have hpow : (r : ℂ) ^ m.natAbs ≠ 0 := pow_ne_zero _ hrne
    field_simp

/-- Angular projection of a compact test away from zero has a compact
squared-radius profile supported in the positive half-line. -/
theorem exists_complexSchwartz_radialAngularAverage (μ : Measure Circle)
    [IsFiniteMeasure μ] [μ.IsMulLeftInvariant] (m : ℤ) (f : ComplexTests)
    (hf : HasCompactSupport f) (h0 : (0 : ℂ) ∉ tsupport f) :
    ∃ h : RealTests, HasCompactSupport h ∧ tsupport h ⊆ Ioi 0 ∧
      ∀ x, complexWeilRadialLift m h x = ∫ u : Circle, (u : ℂ) ^ m * f (x * (u : ℂ)) ∂μ := by
  obtain ⟨a, ha, ha'⟩ := Metric.isOpen_iff.mp isClosed_closure.isOpen_compl 0 h0
  obtain ⟨b, hb, hb'⟩ := hf.isBounded.exists_pos_norm_le
  obtain ⟨g, hg, _⟩ := exists_complexSchwartz_angularAverage μ m f
  have hz (x : ℂ) (hx : ‖x‖ < a ∨ b < ‖x‖) : g x = 0 := by
    rw [hg]
    apply angularAverage_eq_zero_of_norm
    intro y hy
    apply image_eq_zero_of_notMem_tsupport
    rcases hx with hx | hx
    · exact ha' (mem_ball_zero_iff.mpr (hy ▸ hx))
    · exact fun h => (hy.symm ▸ hx).not_ge (hb' y h)
  obtain ⟨h, hc, hp, he⟩ := exists_squaredRadiusProfile m g ha hb hz (by
    intro x w
    rw [hg, hg]
    exact complexAngularAverage_rotate μ m f x w)
  exact ⟨h, hc, hp, fun x => he ▸ hg x⟩

private theorem radialLift_dilation (m : ℤ) (f : RealTests) (v : ℝˣ) (r : ℝ)
    (hr : 0 < r) (hvr : (v : ℝ) = r ^ 2) :
    complexWeilRadialLift m (archSchwartzDilation v f) =
      (r : ℂ) ^ m.natAbs • archSchwartzDilation
        (Units.mk0 (r : ℂ) (by exact_mod_cast hr.ne')) (complexWeilRadialLift m f) := by
  have hrne : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hn : (-m).toNat + m.toNat = m.natAbs := by omega
  ext x
  simp only [complexWeilRadialLift_apply, archSchwartzDilation_apply, Units.val_inv_eq_inv_val,
    Units.val_mk0, smul_apply, smul_eq_mul, Complex.normSq_mul, Complex.normSq_inv,
    Complex.normSq_ofReal, ← pow_two, ← hvr, star_mul', star_inv₀]
  rw [show star (r : ℂ) = (r : ℂ) from Complex.conj_ofReal r]
  simp only [mul_pow, inv_pow]
  rw [← hn]
  simp only [pow_add]
  field_simp

/-- The radial lift intertwines the positive dilation actions, with the
spectral shift accounting for the degree of the angular monomial. -/
theorem complexWeilEigen_radialLift_positive
    (T : StrongDual ℂ ComplexTests) (m : ℤ) (z : ℂ)
    (hT : ∀ u f, T (archSchwartzDilation u f) = complexArchUnitWeight m z u * T f)
    (v : ℝˣ) (hv : 0 < (v : ℝ)) (f : RealTests) :
    T (complexWeilRadialLift m (archSchwartzDilation v f)) =
      (v.val : ℂ) ^ (z + (m.natAbs : ℂ) / 2) * T (complexWeilRadialLift m f) := by
  let r := Real.sqrt (v : ℝ)
  have hr : 0 < r := Real.sqrt_pos.2 hv
  have hrne : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hvr : (v : ℝ) = r ^ 2 := (Real.sq_sqrt hv.le).symm
  let u := Units.mk0 (r : ℂ) hrne
  have hw : complexArchUnitWeight m z u = (v.val : ℂ) ^ z := by
    change ((‖(r : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ z * ((r : ℂ) / (‖(r : ℂ)‖ : ℂ)) ^ m = _
    rw [Complex.norm_of_nonneg hr.le, div_self hrne, one_zpow, mul_one, ← hvr]
  have hvne : (v.val : ℂ) ≠ 0 := by exact_mod_cast v.ne_zero
  have hp : (v.val : ℂ) ^ ((m.natAbs : ℂ) / 2) = (r : ℂ) ^ m.natAbs := by
    rw [hvr, Complex.ofReal_pow, ← Complex.cpow_ofNat_mul', show
      (2 : ℂ) * ((m.natAbs : ℂ) / 2) = (m.natAbs : ℂ) by ring,
      Complex.cpow_natCast]
    · simpa [Complex.arg_ofReal_of_nonneg hr.le] using Real.pi_pos
    · simpa [Complex.arg_ofReal_of_nonneg hr.le] using Real.pi_pos.le
  rw [radialLift_dilation m f v r hr hvr, map_smul, hT, hw, smul_eq_mul,
    Complex.cpow_add _ _ hvne, hp]
  ring

end
end Masullo
