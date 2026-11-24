import MellinTaylorContinuation
import ArchimedeanCharacters
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Complex.Circle
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

open Asymptotics Filter MeasureTheory Set
open scoped ContDiff SchwartzMap Topology

namespace Masullo

noncomputable section

private abbrev Tests := 𝓢(ℂ, ℂ)

local instance complexZeta_circleMeasurable : MeasurableSpace Circle :=
  inferInstanceAs (MeasurableSpace (↥(Submonoid.unitSphere ℂ)))
local instance complexZeta_circleBorel : BorelSpace Circle :=
  inferInstanceAs (BorelSpace (↥(Submonoid.unitSphere ℂ)))

private def angularJet (m : ℤ) (f : Tests) (n : ℕ) (t : ℝ) (u : Circle) : ℂ :=
  (u : ℂ) ^ m * iteratedFDeriv ℝ n f (t • (u : ℂ)) (fun _ => (u : ℂ))

private theorem angularJet_continuous (m : ℤ) (f : Tests) (n : ℕ) :
    Continuous (fun p : ℝ × Circle => angularJet m f n p.1 p.2) := by
  have hu : Continuous (fun p : ℝ × Circle => (p.2 : ℂ)) :=
    continuous_subtype_val.comp continuous_snd
  have hx : Continuous (fun p : ℝ × Circle => p.1 • (p.2 : ℂ)) := continuous_fst.smul hu
  have hF := (f.smooth n).continuous_iteratedFDeriv'.comp hx
  have hargs : Continuous (fun p : ℝ × Circle => (fun _ : Fin n => (p.2 : ℂ))) :=
    continuous_pi (fun _ => hu)
  let M := ContinuousMultilinearMap ℝ (fun _ : Fin n => ℂ) ℂ
  have he := (ContinuousLinearMap.id ℝ M).continuous_uncurry_of_multilinear
  exact (hu.zpow₀ m fun p => Or.inl (Circle.coe_ne_zero p.2)).mul (he.comp (hF.prodMk hargs))

private theorem angularJet_deriv (m : ℤ) (f : Tests) (n : ℕ) (t : ℝ) (u : Circle) :
    HasDerivAt (fun x => angularJet m f n x u) (angularJet m f (n + 1) t u) t := by
  let z := (u : ℂ)
  let v : Fin n → ℂ := fun _ => z
  let D := fun x : ℂ => iteratedFDeriv ℝ n f x
  have hD : DifferentiableAt ℝ D (t • z) :=
    ((f.smooth (n + 1)).differentiable_iteratedFDeriv (by exact_mod_cast Nat.lt_succ_self n)).differentiableAt
  have hpath : HasDerivAt (fun x : ℝ => x • z) z t := by
    simpa using (hasDerivAt_id t).smul_const z
  have hG := (hD.continuousMultilinear_apply_const v).hasFDerivAt.comp_hasDerivAt t hpath
  have he : fderiv ℝ (fun x => D x v) (t • z) z =
      iteratedFDeriv ℝ (n + 1) f (t • z) (fun _ => z) := by
    symm
    exact hD.iteratedFDeriv_succ_apply_left'
  rw [he] at hG
  exact hG.const_mul _

private theorem angularJet_norm_bound (m : ℤ) (f : Tests) (n : ℕ) :
    ∃ B : ℝ, ∀ t : ℝ, ∀ u : Circle, ‖angularJet m f n t u‖ ≤ B := by
  obtain ⟨B, _, hB⟩ := f.decay 0 n
  refine ⟨B, fun t u => ?_⟩
  have ha := (iteratedFDeriv ℝ n f (t • (u : ℂ))).le_opNorm (fun _ => (u : ℂ))
  simp only [Circle.norm_coe, Finset.prod_const_one, mul_one] at ha
  simp only [angularJet, norm_mul, norm_zpow, Circle.norm_coe, one_zpow, one_mul]
  exact ha.trans (by simpa using hB (t • (u : ℂ)))

/-- The circular character component, as a smooth function of the signed
radial coordinate. The Haar normalization is supplied by the caller. -/
def complexZetaProfile (ν : Measure Circle) (m : ℤ) (f : Tests) (t : ℝ) : ℂ :=
  ∫ u, (u : ℂ) ^ m * f (t • (u : ℂ)) ∂ν

private theorem angularIntegral_deriv (ν : Measure Circle) [IsFiniteMeasure ν]
    (m : ℤ) (f : Tests) (n : ℕ) (t : ℝ) :
    HasDerivAt (fun x => ∫ u, angularJet m f n x u ∂ν)
      (∫ u, angularJet m f (n + 1) t u ∂ν) t := by
  have hC (k : ℕ) (x : ℝ) : Continuous (fun u => angularJet m f k x u) :=
    (angularJet_continuous m f k).comp (continuous_const.prodMk continuous_id)
  obtain ⟨B, hB⟩ := angularJet_norm_bound m f (n + 1)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := univ) (μ := ν) (F := angularJet m f n) (F' := angularJet m f (n + 1))
    (bound := fun _ => B) univ_mem (.of_forall fun x => (hC n x).aestronglyMeasurable)
    ((hC n t).integrable_of_hasCompactSupport
      (isCompact_univ.of_isClosed_subset isClosed_closure (subset_univ _)))
    (hC (n + 1) t).aestronglyMeasurable (.of_forall fun u x _ => hB x u)
    (integrable_const _) (.of_forall fun u x _ => angularJet_deriv m f n x u)).2

/-- All radial derivatives commute with the compact angular integral. -/
theorem complexZetaProfile_iteratedDeriv (ν : Measure Circle) [IsFiniteMeasure ν]
    (m : ℤ) (f : Tests) (n : ℕ) :
    iteratedDeriv n (complexZetaProfile ν m f) = fun x => ∫ u, angularJet m f n x u ∂ν := by
  induction n with
  | zero =>
    funext t
    simp [complexZetaProfile, angularJet]
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    exact (angularIntegral_deriv ν m f n t).deriv

theorem complexZetaProfile_smooth (ν : Measure Circle) [IsFiniteMeasure ν] (m : ℤ) (f : Tests) :
    ContDiff ℝ ∞ (complexZetaProfile ν m f) := by
  apply contDiff_of_differentiable_iteratedDeriv
  intro n _
  rw [complexZetaProfile_iteratedDeriv ν m f n]
  intro t
  exact (angularIntegral_deriv ν m f n t).differentiableAt

/-- Angular projection with the signed real radius as a continuous map of Schwartz spaces. -/
def complexZetaRadialSchwartz (ν : Measure Circle) [IsFiniteMeasure ν] (m : ℤ) :
    Tests →L[ℂ] 𝓢(ℝ, ℂ) :=
  SchwartzMap.mkCLM (complexZetaProfile ν m)
    (fun f g t => by
      have hint (h : Tests) :
          Integrable (fun u : Circle => (u : ℂ) ^ m * h (t • (u : ℂ))) ν := by
        have hc := (angularJet_continuous m h 0).comp ((continuous_const (y := t)).prodMk continuous_id)
        apply (show Continuous (fun u : Circle => (u : ℂ) ^ m * h (t • (u : ℂ))) by
          simpa [angularJet, Function.comp_def] using hc).integrable_of_hasCompactSupport
        exact isCompact_univ.of_isClosed_subset isClosed_closure (subset_univ _)
      simpa [complexZetaProfile, mul_add] using integral_add (hint f) (hint g))
    (fun c f t => by
      simpa [complexZetaProfile, smul_eq_mul, mul_left_comm] using
        integral_const_mul c (fun u : Circle => (u : ℂ) ^ m * f (t • (u : ℂ))))
    (complexZetaProfile_smooth ν m)
    (fun ⟨k, n⟩ => ⟨{(k, n)}, ν.real univ, measureReal_nonneg, fun f t => by
      rw [Finset.sup_singleton, norm_iteratedFDeriv_eq_norm_iteratedDeriv,
        complexZetaProfile_iteratedDeriv]
      change ‖t‖ ^ k * ‖∫ u, angularJet m f n t u ∂ν‖ ≤
        ν.real univ * SchwartzMap.seminorm ℂ k n f
      rw [← Real.norm_of_nonneg (pow_nonneg (norm_nonneg t) k), ← norm_smul, ← integral_smul]
      rw [mul_comm (ν.real univ)]
      apply norm_integral_le_of_norm_le_const
      apply Filter.Eventually.of_forall
      intro u
      have h := (iteratedFDeriv ℝ n f (t • (u : ℂ))).le_opNorm (fun _ => (u : ℂ))
      simp only [Circle.norm_coe, Finset.prod_const_one, mul_one] at h
      simp only [norm_smul, Real.norm_of_nonneg (pow_nonneg (norm_nonneg t) k),
        angularJet, norm_mul, norm_zpow, Circle.norm_coe, one_zpow, one_mul]
      exact (mul_le_mul_of_nonneg_left h (by positivity)).trans (by
        simpa only [norm_smul, Circle.norm_coe, mul_one] using
          SchwartzMap.le_seminorm ℂ k n f (t • (u : ℂ)))⟩)

private theorem complexZetaProfile_rapid (ν : Measure Circle) [IsFiniteMeasure ν]
    (m : ℤ) (f : Tests) (a : ℝ) :
    complexZetaProfile ν m f =O[atTop] (fun t => t ^ (-a)) :=
  schwartz_radial_rapid (complexZetaRadialSchwartz ν m f) a

/-- The complex radial Mellin integral uses the exponent `2s`, since the
normalized local absolute value is squared Euclidean length. -/
def complexArchimedeanZetaContinued (ν : Measure Circle) (m : ℤ) (f : Tests) (s : ℂ) : ℂ :=
  mellinTaylorContinued (complexZetaProfile ν m f) (2 * s)

/-- The complex-place continuation evaluated at a fixed parameter is a tempered distribution. -/
def complexArchimedeanZetaContinuedCLM (ν : Measure Circle) [IsFiniteMeasure ν]
    (m : ℤ) (s : ℂ) : Tests →L[ℂ] ℂ :=
  (schwartzMellinContinuedCLM (2 * s)).comp (complexZetaRadialSchwartz ν m)

@[simp] theorem complexArchimedeanZetaContinuedCLM_apply (ν : Measure Circle) [IsFiniteMeasure ν]
    (m : ℤ) (s : ℂ) (f : Tests) :
    complexArchimedeanZetaContinuedCLM ν m s f = complexArchimedeanZetaContinued ν m f s :=
  schwartzMellinContinuedCLM_apply (2 * s) (complexZetaRadialSchwartz ν m f)

/-- On the positive half-plane the continued complex radial value is its
absolutely convergent Mellin integral. -/
theorem complexArchimedeanZetaContinued_eq_radial (ν : Measure Circle) [IsFiniteMeasure ν]
    (m : ℤ) (f : Tests) {s : ℂ} (hs : 0 < s.re) :
    HasMellin (complexZetaProfile ν m f) (2 * s) (complexArchimedeanZetaContinued ν m f s) := by
  apply mellinTaylorContinued_eq_mellin
    (complexZetaProfile_smooth ν m f) (complexZetaProfile_rapid ν m f)
  simpa using mul_pos (by norm_num : 0 < (2 : ℝ)) hs

theorem complexArchimedeanZetaContinued_meromorphic (ν : Measure Circle) [IsFiniteMeasure ν]
    (m : ℤ) (f : Tests) : Meromorphic (complexArchimedeanZetaContinued ν m f) := by
  intro s
  have hm := mellinTaylorContinued_meromorphic (complexZetaProfile_smooth ν m f)
    (complexZetaProfile_rapid ν m f) (2 * s)
  exact hm.comp_analyticAt (analyticAt_const.mul analyticAt_id)

theorem complexArchimedeanZetaContinued_analyticAt (ν : Measure Circle) [IsFiniteMeasure ν]
    (m : ℤ) (f : Tests) {s : ℂ} (hs : ∀ k : ℕ, 2 * s + k ≠ 0) :
    AnalyticAt ℂ (complexArchimedeanZetaContinued ν m f) s := by
  have ha := mellinTaylorContinued_analyticAt (complexZetaProfile_smooth ν m f)
    (complexZetaProfile_rapid ν m f) hs
  exact ha.comp (analyticAt_const.mul analyticAt_id)



/-- The complex local zeta integrand in positive radial and circle coordinates.
The factor `dt / t` is absorbed into the radial power. -/
def complexArchimedeanZetaPolarIntegrand (m : ℤ) (f : Tests) (s : ℂ) (p : ℝ × Circle) : ℂ :=
  (p.1 : ℂ) ^ (2 * s - 1) * ((p.2 : ℂ) ^ m * f (p.1 • (p.2 : ℂ)))

private theorem complexArchimedeanZetaPolarIntegrand_measurable (m : ℤ) (f : Tests) (s : ℂ) :
    Measurable (complexArchimedeanZetaPolarIntegrand m f s) := by
  have hr : Measurable (fun t : ℝ => (t : ℂ) ^ (2 * s - 1)) := by
    apply measurable_of_measurable_on_compl_singleton 0
    apply Continuous.measurable
    apply continuous_iff_continuousAt.mpr
    intro t
    exact ContinuousAt.comp' (f := Subtype.val) (x := t)
      (Complex.continuousAt_ofReal_cpow_const t.val _ (Or.inr t.property))
      continuous_subtype_val.continuousAt
  have hphase : Continuous (fun u : Circle => (u : ℂ) ^ m) :=
    continuous_subtype_val.zpow₀ m (fun u => Or.inl (Circle.coe_ne_zero u))
  have hu : Measurable (fun u : Circle => (u : ℂ)) := measurable_subtype_coe
  have hf : Measurable (fun p : ℝ × Circle => f (p.1 • (p.2 : ℂ))) :=
    f.continuous.measurable.comp (measurable_fst.smul (hu.comp measurable_snd))
  exact (hr.comp measurable_fst).mul ((hphase.measurable.comp measurable_snd).mul hf)

/-- The positive-half-plane complex integral converges absolutely as a product
integral. Fubini recovers the continued value from this full integrand. -/
theorem complexArchimedeanZetaContinued_eq_polarIntegral (ν : Measure Circle) [IsFiniteMeasure ν]
    (m : ℤ) (f : Tests) {s : ℂ} (hs : 0 < s.re) :
    let μ := (volume : Measure ℝ).restrict (Ioi (0 : ℝ))
    Integrable (complexArchimedeanZetaPolarIntegrand m f s) (μ.prod ν) ∧
      complexArchimedeanZetaContinued ν m f s =
        ∫ p, complexArchimedeanZetaPolarIntegrand m f s p ∂μ.prod ν := by
  let μ := (volume : Measure ℝ).restrict (Ioi (0 : ℝ))
  let b := 2 * s.re - 1
  let F := complexArchimedeanZetaPolarIntegrand m f s
  obtain ⟨k, hk⟩ := exists_nat_gt (2 * s.re)
  obtain ⟨A, hA₀, hA⟩ := f.decay 0 0
  obtain ⟨B, hB₀, hB⟩ := f.decay k 0
  let H (t : ℝ) := if t ≤ 1 then A * t ^ b else B * t ^ (b - k)
  have h₀ : IntegrableOn H (Ioc (0 : ℝ) 1) := by
    have he : -1 < b := by dsimp only [b]; linarith
    have h := (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
      (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) he)
    have hh : IntegrableOn (fun t : ℝ => A * t ^ b) (Ioc 0 1) := h.const_mul A
    exact hh.congr_fun (fun t ht => (ite_eq_left ht.2).symm) measurableSet_Ioc
  have h₁ : IntegrableOn H (Ioi 1) := by
    have he : b - (k : ℝ) < -1 := by dsimp only [b]; linarith
    have hh : IntegrableOn (fun t : ℝ => B * t ^ (b - k)) (Ioi 1) :=
      (integrableOn_Ioi_rpow_of_lt he zero_lt_one).const_mul B
    exact hh.congr_fun (fun t ht => (ite_eq_right (not_le_of_gt ht)).symm) measurableSet_Ioi
  have hH : Integrable H μ := by
    have h := h₀.union h₁
    rwa [Ioc_union_Ioi_eq_Ioi zero_le_one] at h
  have hmeas : Measurable F := complexArchimedeanZetaPolarIntegrand_measurable m f s
  have hI : Integrable F (μ.prod ν) := by
    apply (hH.comp_fst ν).mono' hmeas.aestronglyMeasurable
    have hpos : ∀ᵐ p : ℝ × Circle ∂μ.prod ν, 0 < p.1 := by
      have h : ∀ᵐ t ∂μ, t ∈ Ioi (0 : ℝ) := ae_restrict_mem measurableSet_Ioi
      exact (Measure.ae_prod_iff_ae_ae (measurableSet_Ioi.preimage measurable_fst)).mpr
        (h.mono fun t ht => .of_forall fun _ => ht)
    filter_upwards [hpos] with p hp
    change ‖F p‖ ≤ H p.1
    have hnorm : ‖F p‖ = p.1 ^ b * ‖f (p.1 • (p.2 : ℂ))‖ := by
      have hr : (2 * s - 1).re = b := by simp [b, Complex.mul_re]
      simp only [F, complexArchimedeanZetaPolarIntegrand, norm_mul, norm_zpow,
        Circle.norm_coe, one_zpow, one_mul, Complex.norm_cpow_eq_rpow_re_of_pos hp, hr]
    rw [hnorm]
    by_cases ht : p.1 ≤ 1
    · rw [show H p.1 = A * p.1 ^ b from ite_eq_left ht, mul_comm A]
      exact mul_le_mul_of_nonneg_left (by simpa using hA (p.1 • (p.2 : ℂ))) (Real.rpow_nonneg hp.le _)
    · rw [show H p.1 = B * p.1 ^ (b - k) from ite_eq_right ht]
      have hb := hB (p.1 • (p.2 : ℂ))
      rw [norm_iteratedFDeriv_zero, norm_smul, Circle.norm_coe, mul_one, Real.norm_of_nonneg hp.le] at hb
      have hP : p.1 ^ (b - (k : ℝ)) = p.1 ^ b / p.1 ^ k := by
        rw [Real.rpow_sub hp, Real.rpow_natCast]
      rw [hP, ← mul_div_assoc, le_div_iff₀ (pow_pos hp _)]
      calc
        p.1 ^ b * ‖f (p.1 • (p.2 : ℂ))‖ * p.1 ^ k =
            p.1 ^ b * (p.1 ^ k * ‖f (p.1 • (p.2 : ℂ))‖) := by ac_rfl
        _ ≤ p.1 ^ b * B := mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hp.le _)
        _ = _ := mul_comm _ _
  refine ⟨hI, ?_⟩
  rw [integral_prod _ hI, ← (complexArchimedeanZetaContinued_eq_radial ν m f hs).2]
  unfold mellin
  apply integral_congr_ae (.of_forall fun t => ?_)
  change (t : ℂ) ^ (2 * s - 1) * complexZetaProfile ν m f t = ∫ u, F (t, u) ∂ν
  rw [complexZetaProfile, ← integral_const_mul]
  rfl

open scoped ENNReal

private local instance : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

private theorem angularExponential_measurable : Measurable AddCircle.homeomorphCircle' :=
  AddCircle.homeomorphCircle'.continuous.measurable

/-- The angular measure of the complex Tamagawa density. The additive differential
form has absolute value twice planar Lebesgue measure. -/
def complexTamagawaAngularMeasure : Measure Circle :=
  (2 : ℝ≥0∞) • (volume : Measure (AddCircle (2 * Real.pi))).map AddCircle.homeomorphCircle'

instance complexTamagawaAngularMeasure_finite : IsFiniteMeasure complexTamagawaAngularMeasure :=
  Measure.smul_finite _ (by simp)

instance complexTamagawaAngularMeasure_invariant : complexTamagawaAngularMeasure.IsMulLeftInvariant := by
  let μ : Measure (AddCircle (2 * Real.pi)) := volume
  let e := AddCircle.homeomorphCircle'
  haveI : (μ.map e).IsMulLeftInvariant := by
    constructor
    intro w
    obtain ⟨θ, rfl⟩ := e.surjective w
    rw [Measure.map_map (measurable_const_mul _) angularExponential_measurable]
    conv_rhs => rw [← map_add_left_eq_self μ θ]
    rw [Measure.map_map angularExponential_measurable (measurable_const_add _)]
    congr 1
    funext y
    exact (Real.Angle.toCircle_add θ y).symm
  exact isMulLeftInvariant_smul _

@[simp] theorem complexTamagawaAngularMeasure_mass :
    complexTamagawaAngularMeasure.real univ = 4 * Real.pi := by
  rw [measureReal_def, complexTamagawaAngularMeasure, Measure.smul_apply,
    Measure.map_apply angularExponential_measurable MeasurableSet.univ, preimage_univ]
  change ((2 : ℝ≥0∞) * (volume : Measure (AddCircle (2 * Real.pi))) univ).toReal = _
  rw [AddCircle.measure_univ, ENNReal.toReal_mul, ENNReal.toReal_ofReal (le_of_lt Real.two_pi_pos)]
  norm_num
  ring

private theorem complexTamagawaAngularMeasure_eq_map :
    complexTamagawaAngularMeasure = (2 : ℝ≥0∞) •
      (volume.restrict (Ioo (-Real.pi) Real.pi)).map Circle.exp := by
  unfold complexTamagawaAngularMeasure
  congr 1
  have h := (AddCircle.measurePreserving_mk (2 * Real.pi) (-Real.pi)).map_eq
  rw [show -Real.pi + 2 * Real.pi = Real.pi by ring, ← restrict_Ioo_eq_restrict_Ioc] at h
  rw [← h, Measure.map_map angularExponential_measurable AddCircle.measurable_mk']
  rfl

private def complexTamagawaDensity (z : ℂ) : ℝ := 2 / ‖z‖ ^ 2

/-- Multiplicative complex-place measure in the ambient planar coordinate. The
formula defines its extension by zero across the origin. -/
def complexTamagawaMultiplicativeMeasure : Measure ℂ :=
  volume.withDensity (fun z => ENNReal.ofReal (complexTamagawaDensity z))

private theorem complexTamagawaDensity_measurable : Measurable complexTamagawaDensity := by
  unfold complexTamagawaDensity
  fun_prop

private def complexZetaCartIntegrand (m : ℤ) (f : Tests) (s : ℂ) (z : ℂ) : ℂ :=
  ((‖z‖ ^ 2 : ℝ) : ℂ) ^ s * ((z / (‖z‖ : ℂ)) ^ m * f z)

/-- The polar continuation extends the zeta integral with the actual complex
Tamagawa density against planar Lebesgue measure. -/
theorem complexArchimedeanZetaContinued_eq_tamagawaIntegral (m : ℤ) (f : Tests) {s : ℂ}
    (hs : 0 < s.re) :
    Integrable (complexZetaCartIntegrand m f s) complexTamagawaMultiplicativeMeasure ∧
      complexArchimedeanZetaContinued complexTamagawaAngularMeasure m f s =
        ∫ z, complexZetaCartIntegrand m f s z ∂complexTamagawaMultiplicativeMeasure := by
  let H := complexZetaCartIntegrand m f s
  let F := complexArchimedeanZetaPolarIntegrand m f s
  let μ := (volume : Measure ℝ).restrict (Ioi (0 : ℝ))
  let η := (volume : Measure ℝ).restrict (Ioo (-Real.pi) Real.pi)
  let P : ℝ × ℝ → ℝ × Circle := Prod.map id Circle.exp
  have hΦ : Measurable P := measurable_id.prodMap Circle.exp.continuous.measurable
  have hProd : μ.prod complexTamagawaAngularMeasure = (2 : ℝ≥0∞) • (μ.prod η).map P := by
    rw [complexTamagawaAngularMeasure_eq_map, Measure.prod_smul_right]
    congr 1
    simpa only [Measure.map_id] using Measure.map_prod_map μ η measurable_id Circle.exp.continuous.measurable
  have hF : Measurable F := complexArchimedeanZetaPolarIntegrand_measurable m f s
  have hPolar := Complex.integral_comp_polarCoord_symm (fun z => complexTamagawaDensity z • H z)
  change (∫ p in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
    p.1 • (complexTamagawaDensity (Complex.polarCoord.symm p) • H (Complex.polarCoord.symm p))) =
    ∫ z, complexTamagawaDensity z • H z at hPolar
  have hRestrict : (volume : Measure (ℝ × ℝ)).restrict (Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi) =
      μ.prod η := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
  have ht : ∀ᵐ p : ℝ × ℝ ∂ μ.prod η, 0 < p.1 := by
    exact (Measure.ae_prod_iff_ae_ae (measurableSet_Ioi.preimage measurable_fst)).mpr
      ((ae_restrict_mem measurableSet_Ioi).mono fun t ht => .of_forall fun _ => ht)
  have hpoint (p : ℝ × ℝ) (hp : 0 < p.1) :
      (2 : ℝ) • F (P p) =
        p.1 • (complexTamagawaDensity (Complex.polarCoord.symm p) • H (Complex.polarCoord.symm p)) := by
    have hz : Complex.polarCoord.symm p = p.1 • (Circle.exp p.2 : ℂ) := by
      rw [Complex.polarCoord_symm_apply, Circle.coe_exp, Complex.exp_mul_I, Complex.real_smul,
        Complex.ofReal_cos, Complex.ofReal_sin]
    have hr : ‖Complex.polarCoord.symm p‖ = p.1 := by rw [Complex.norm_polarCoord_symm, abs_of_pos hp]
    have hp' : (p.1 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hp.ne'
    have hphase : Complex.polarCoord.symm p / (‖Complex.polarCoord.symm p‖ : ℂ) = (Circle.exp p.2 : ℂ) := by
      rw [hr, hz, Complex.real_smul, mul_comm, mul_div_cancel_right₀ _ hp']
    have hpow : (((p.1 ^ 2 : ℝ) : ℂ) ^ s) = (p.1 : ℂ) ^ (2 * s) := by
      rw [Complex.ofReal_pow, ← Complex.cpow_ofNat_mul' (by simp [Complex.arg_ofReal_of_nonneg hp.le, Real.pi_pos])
        (by simp [Complex.arg_ofReal_of_nonneg hp.le, Real.pi_pos.le])]
    change (2 : ℝ) • F (P p) =
      p.1 • (complexTamagawaDensity (Complex.polarCoord.symm p) • H (Complex.polarCoord.symm p))
    unfold F P H complexZetaCartIntegrand complexArchimedeanZetaPolarIntegrand complexTamagawaDensity
    rw [hphase, hr, hpow, hz]
    have hP : Prod.map id Circle.exp p = (p.1, Circle.exp p.2) := rfl
    rw [hP]
    simp only [Complex.real_smul, Complex.ofReal_div, Complex.ofReal_ofNat, Complex.ofReal_pow]
    rw [Complex.cpow_sub _ _ hp', Complex.cpow_one]
    field_simp
  constructor
  · have hH : Measurable H := by
      apply measurable_of_measurable_on_compl_singleton 0
      apply Continuous.measurable
      apply continuous_iff_continuousAt.mpr
      intro z
      have hz : (z : ℂ) ≠ 0 := z.property
      have hN : 0 < ‖(z : ℂ)‖ := norm_pos_iff.mpr hz
      have hNb : 0 < ‖(z : ℂ)‖ ^ 2 := by positivity
      have hnorm : Continuous (fun w : ℂ => ‖w‖ ^ (2 : ℕ)) := continuous_norm.pow 2
      have hr : ContinuousAt (fun w : ℂ => ((‖w‖ ^ 2 : ℝ) : ℂ) ^ s) (z : ℂ) :=
        ContinuousAt.comp' (f := fun w : ℂ => ‖w‖ ^ (2 : ℕ)) (x := (z : ℂ))
          (Complex.continuousAt_ofReal_cpow_const (‖(z : ℂ)‖ ^ 2) s (Or.inr hNb.ne'))
          hnorm.continuousAt
      have hd : ContinuousAt (fun w : ℂ => w / (‖w‖ : ℂ)) (z : ℂ) :=
        continuous_id.continuousAt.div (Complex.continuous_ofReal.comp continuous_norm).continuousAt
          (Complex.ofReal_ne_zero.mpr hN.ne')
      have hd' : ((z : ℂ) / (‖(z : ℂ)‖ : ℂ)) ≠ 0 :=
        div_ne_zero hz (Complex.ofReal_ne_zero.mpr hN.ne')
      exact ContinuousAt.comp' (f := Subtype.val) (x := z) (hr.mul ((hd.zpow₀ m (Or.inl hd')).mul f.continuous.continuousAt))
        continuous_subtype_val.continuousAt
    refine ⟨hH.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm, complexTamagawaMultiplicativeMeasure,
      lintegral_withDensity_eq_lintegral_mul _ complexTamagawaDensity_measurable.ennreal_ofReal hH.enorm]
    have hPol := Complex.lintegral_comp_polarCoord_symm
      (fun z => ENNReal.ofReal (complexTamagawaDensity z) * ‖H z‖ₑ)
    change (∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
      ENNReal.ofReal p.1 * (ENNReal.ofReal (complexTamagawaDensity (Complex.polarCoord.symm p)) *
        ‖H (Complex.polarCoord.symm p)‖ₑ)) =
      ∫⁻ z, ENNReal.ofReal (complexTamagawaDensity z) * ‖H z‖ₑ at hPol
    change (∫⁻ z, ENNReal.ofReal (complexTamagawaDensity z) * ‖H z‖ₑ) < (⊤ : ℝ≥0∞)
    rw [← hPol, hRestrict]
    have hInt := (complexArchimedeanZetaContinued_eq_polarIntegral
      complexTamagawaAngularMeasure m f hs).1.hasFiniteIntegral
    rw [hasFiniteIntegral_iff_enorm, hProd, lintegral_smul_measure, lintegral_map hF.enorm hΦ] at hInt
    change (2 : ℝ≥0∞) * (∫⁻ p, ‖F (P p)‖ₑ ∂μ.prod η) < (⊤ : ℝ≥0∞) at hInt
    have hscale : (∫⁻ p, (2 : ℝ≥0∞) * ‖F (P p)‖ₑ ∂μ.prod η) =
        (2 : ℝ≥0∞) * (∫⁻ p, ‖F (P p)‖ₑ ∂μ.prod η) :=
      lintegral_const_mul _ (hF.enorm.comp hΦ)
    refine lt_of_eq_of_lt ((lintegral_congr_ae ?_).trans hscale) hInt
    filter_upwards [ht] with p hp
    have hN : 0 ≤ complexTamagawaDensity (Complex.polarCoord.symm p) := by
      unfold complexTamagawaDensity
      positivity
    calc
      _ = ‖p.1 • (complexTamagawaDensity (Complex.polarCoord.symm p) •
          H (Complex.polarCoord.symm p))‖ₑ := by
        rw [enorm_smul, enorm_smul, ← ofReal_norm p.1,
          ← ofReal_norm (complexTamagawaDensity (Complex.polarCoord.symm p)),
          Real.norm_of_nonneg hp.le, Real.norm_of_nonneg hN]
      _ = ‖(2 : ℝ) • F (P p)‖ₑ := congrArg (fun v : ℂ => ‖v‖ₑ) (hpoint p hp).symm
      _ = _ := by rw [enorm_smul, ← ofReal_norm (2 : ℝ)]; norm_num
  · rw [complexTamagawaMultiplicativeMeasure, integral_withDensity_eq_integral_toReal_smul
      complexTamagawaDensity_measurable.ennreal_ofReal (.of_forall fun _ => ENNReal.ofReal_lt_top)]
    have hD (z : ℂ) : (ENNReal.ofReal (complexTamagawaDensity z)).toReal = complexTamagawaDensity z :=
      ENNReal.toReal_ofReal (by unfold complexTamagawaDensity; positivity)
    simp_rw [hD]
    rw [← hPolar, hRestrict, (complexArchimedeanZetaContinued_eq_polarIntegral
      complexTamagawaAngularMeasure m f hs).2, hProd, integral_smul_measure,
      integral_map hΦ.aemeasurable (hF.aestronglyMeasurable), ← integral_smul]
    exact integral_congr_ae (ht.mono hpoint)


/-- At every candidate half-integer pole, the residue is one half the
angular average of the corresponding real Taylor coefficient. -/
theorem complexArchimedeanZetaContinued_residue (ν : Measure Circle) [IsFiniteMeasure ν]
    (m : ℤ) (f : Tests) (k : ℕ) :
    Tendsto (fun z => (z + (k : ℂ) / 2) * complexArchimedeanZetaContinued ν m f z)
      (𝓝[≠] (-(k : ℂ) / 2))
      (𝓝 (((k.factorial : ℂ)⁻¹ *
        ∫ u, (u : ℂ) ^ m * iteratedFDeriv ℝ k f 0 (fun _ => (u : ℂ)) ∂ν) / 2)) := by
  let g := complexZetaProfile ν m f
  let p : ℂ := -(k : ℂ) / 2
  let c := mellinTaylorCoeff g k
  have hc : c = (k.factorial : ℂ)⁻¹ *
      ∫ u, (u : ℂ) ^ m * iteratedFDeriv ℝ k f 0 (fun _ => (u : ℂ)) ∂ν := by
    change (k.factorial : ℂ)⁻¹ * iteratedDeriv k (complexZetaProfile ν m f) 0 = _
    rw [complexZetaProfile_iteratedDeriv]
    simp only [angularJet, zero_smul]
  have hscale : (2 : ℂ) * p = -(k : ℂ) := by
    dsimp only [p]
    ring
  obtain ⟨A, hA, hpart⟩ := mellinTaylorContinued_principalPart
    (complexZetaProfile_smooth ν m f) (complexZetaProfile_rapid ν m f) k
  have hmap : ContinuousAt (fun z : ℂ => 2 * z) p := continuous_const.mul continuous_id |>.continuousAt
  have hnear : ∀ᶠ z in 𝓝 p, mellinTaylorContinued g (2 * z) = A (2 * z) + c / (2 * z + k) := by
    rw [← hscale] at hpart
    exact hmap.eventually hpart
  have hA' : ContinuousAt (fun z : ℂ => A (2 * z)) p :=
    ContinuousAt.comp' (f := fun z : ℂ => 2 * z) (x := p)
      (by simpa only [hscale] using hA.continuousAt) hmap
  have hlim : Tendsto (fun z : ℂ => (z + k / 2) * A (2 * z) + c / 2) (𝓝[≠] p) (𝓝 (c / 2)) := by
    have h : ContinuousAt (fun z : ℂ => (z + (k : ℂ) / 2) * A (2 * z) + c / 2) p :=
      ((continuousAt_id.add continuousAt_const).mul hA').add continuousAt_const
    have hp : p + (k : ℂ) / 2 = 0 := by dsimp only [p]; ring
    simpa only [hp, zero_mul, zero_add] using h.tendsto.mono_left nhdsWithin_le_nhds
  rw [← hc]
  apply hlim.congr'
  filter_upwards [hnear.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin (s := {p}ᶜ)]
    with z hz hz'
  change (z + (k : ℂ) / 2) * A (2 * z) + c / 2 =
    (z + (k : ℂ) / 2) * mellinTaylorContinued g (2 * z)
  have hm : z + (k : ℂ) / 2 ≠ 0 := by
    intro he
    apply hz'
    apply mem_singleton_iff.mpr
    dsimp only [p]
    linear_combination he
  have hden : 2 * z + (k : ℂ) = 2 * (z + (k : ℂ) / 2) := by ring
  rw [hz, hden, mul_add]
  congr 1
  rw [← mul_div_assoc, mul_comm (z + (k : ℂ) / 2) c, mul_div_mul_right c 2 hm]


/-- A candidate half-integer is removable when its averaged Taylor coefficient
vanishes. Otherwise the complex radial transform has a simple pole there. -/
theorem complexArchimedeanZetaContinued_order (ν : Measure Circle) [IsFiniteMeasure ν]
    (m : ℤ) (f : Tests) (k : ℕ) :
    if mellinTaylorCoeff (complexZetaProfile ν m f) k = 0 then
      AnalyticAt ℂ (complexArchimedeanZetaContinued ν m f) (-(k : ℂ) / 2)
    else meromorphicOrderAt (complexArchimedeanZetaContinued ν m f) (-(k : ℂ) / 2) = (-1 : ℤ) := by
  let g := complexZetaProfile ν m f
  let p : ℂ := -(k : ℂ) / 2
  let d : ℂ → ℂ := fun z => 2 * z
  have hd : AnalyticAt ℂ d p := analyticAt_const.mul analyticAt_id
  have hd' : deriv d p ≠ 0 := by
    have hh : HasDerivAt d (2 : ℂ) p := by simpa using (hasDerivAt_id p).const_mul (2 : ℂ)
    rw [hh.deriv]
    norm_num
  have hdp : d p = -(k : ℂ) := by dsimp only [d, p]; ring
  have h := mellinTaylorContinued_order (complexZetaProfile_smooth ν m f)
    (complexZetaProfile_rapid ν m f) k
  by_cases hzero : mellinTaylorCoeff g k = 0
  · rw [ite_eq_left hzero] at h ⊢
    have ha : AnalyticAt ℂ (mellinTaylorContinued g) (d p) := hdp ▸ h
    exact ha.comp hd
  · rw [ite_eq_right hzero] at h ⊢
    change meromorphicOrderAt (mellinTaylorContinued g ∘ d) p = _
    rwa [meromorphicOrderAt_comp_of_deriv_ne_zero hd hd', hdp]


/-- Integrating opposite points of the circle cancels a Taylor coefficient
when angular frequency and derivative order have opposite parity. -/
theorem complexZetaProfile_taylorCoeff_oppositeParity (ν : Measure Circle)
    [IsFiniteMeasure ν] [ν.IsMulLeftInvariant] (m : ℤ) (f : Tests) (k : ℕ)
    (hodd : Odd (m + (k : ℤ))) :
    mellinTaylorCoeff (complexZetaProfile ν m f) k = 0 := by
  let J := fun u : Circle => angularJet m f k 0 u
  let D := iteratedFDeriv ℝ k f (0 : ℂ)
  have hphase : (-1 : ℂ) ^ m * (-1 : ℂ) ^ k = -1 := by
    rw [← zpow_natCast, ← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), hodd.neg_one_zpow]
  have he (u : Circle) : J ((-1 : Circle) * u) = -J u := by
    have hu : (((-1 : Circle) * u : Circle) : ℂ) = -(u : ℂ) := by
      simp
    have hd : D (fun _ => -(u : ℂ)) = (-1 : ℂ) ^ k * D (fun _ => (u : ℂ)) := by
      have h := D.map_smul_univ (fun _ => (-1 : ℝ)) (fun _ => (u : ℂ))
      simpa [Finset.prod_const, Complex.real_smul] using h
    simp only [J, angularJet, zero_smul]
    change (((-1 : Circle) * u : Circle) : ℂ) ^ m *
        D (fun _ => (((-1 : Circle) * u : Circle) : ℂ)) =
      -((u : ℂ) ^ m * D (fun _ => (u : ℂ)))
    rw [hu, hd, ← neg_one_mul (u : ℂ), mul_zpow]
    calc
      _ = (((-1 : ℂ) ^ m) * (-1 : ℂ) ^ k) * ((u : ℂ) ^ m * D (fun _ => (u : ℂ))) := by ring
      _ = _ := by rw [hphase, neg_one_mul]
  have hent : (∫ u, J u ∂ν) = 0 := by
    have h := integral_mul_left_eq_self (μ := ν) J (-1)
    simp_rw [he, integral_neg] at h
    exact neg_eq_self.mp h
  rw [mellinTaylorCoeff, complexZetaProfile_iteratedDeriv ν m f k]
  change (k.factorial : ℂ)⁻¹ * (∫ u, J u ∂ν) = 0
  rw [hent, mul_zero]

/-- The complex transform is analytic at half-integers excluded by parity. -/
theorem complexArchimedeanZetaContinued_oppositeParity (ν : Measure Circle)
    [IsFiniteMeasure ν] [ν.IsMulLeftInvariant] (m : ℤ) (f : Tests) (k : ℕ)
    (hodd : Odd (m + (k : ℤ))) :
    AnalyticAt ℂ (complexArchimedeanZetaContinued ν m f) (-(k : ℂ) / 2) := by
  have h := complexArchimedeanZetaContinued_order ν m f k
  rwa [ite_eq_left (complexZetaProfile_taylorCoeff_oppositeParity ν m f k hodd)] at h


private abbrev AngularJetMap (k : ℕ) := ContinuousMultilinearMap ℝ (fun _ : Fin k => ℂ) ℂ

private def angularLast {k : ℕ} (D : AngularJetMap (k+1)) (v : ℂ) : AngularJetMap k :=
  (ContinuousLinearMap.apply ℝ ℂ v).compContinuousMultilinearMap D.curryRight

open Polynomial in
/-- Encoding a real multilinear jet on the circle as a polynomial in the
square of the circle coordinate, after removing the lowest negative power. -/
def complexAngularPolynomial : (k : ℕ) → AngularJetMap k → ℂ[X]
  | 0, D => C (D (fun _ => 1))
  | k + 1, D =>
    C (1 / 2) * ((X + 1) * complexAngularPolynomial k (angularLast D 1) -
      C Complex.I * ((X - 1) * complexAngularPolynomial k (angularLast D Complex.I)))

@[simp] theorem complexAngularPolynomial_zero (k : ℕ) :
    complexAngularPolynomial k 0 = 0 := by
  induction k with
  | zero => simp [complexAngularPolynomial]
  | succ k ih =>
    have hz (v : ℂ) : angularLast (0 : AngularJetMap (k+1)) v = 0 := by ext w; rfl
    simp [complexAngularPolynomial, hz, ih]

open Polynomial in
theorem complexAngularPolynomial_natDegree (k : ℕ) (D : AngularJetMap k) :
    (complexAngularPolynomial k D).natDegree ≤ k := by
  induction k with
  | zero => simp [complexAngularPolynomial]
  | succ k ih =>
    rw [complexAngularPolynomial]
    apply (natDegree_C_mul_le _ _).trans
    refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
    · apply natDegree_mul_le.trans
      have hX : (X + (1 : ℂ[X])).natDegree ≤ 1 := by
        rw [← C_1, natDegree_X_add_C]
      exact (add_le_add hX (ih _)).trans_eq (by omega)
    · apply (natDegree_C_mul_le _ _).trans
      apply natDegree_mul_le.trans
      have hX : (X - (1 : ℂ[X])).natDegree ≤ 1 := by
        rw [← C_1, natDegree_X_sub_C]
      exact (add_le_add hX (ih _)).trans_eq (by omega)

private theorem circle_coordinate_formulas (u : Circle) :
    (2 : ℂ) * (u : ℂ) * (u : ℂ).re = (u : ℂ)^2 + 1 ∧
      (2 : ℂ) * (u : ℂ) * (u : ℂ).im = -Complex.I * ((u : ℂ)^2 - 1) := by
  let z := (u : ℂ)
  have hz : z * (starRingEnd ℂ) z = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Circle.norm_coe]
    norm_num
  have hre := Complex.add_conj z
  have him := Complex.sub_conj z
  push_cast at hre him
  change (2 : ℂ) * z * z.re = z^2 + 1 ∧ (2 : ℂ) * z * z.im = -Complex.I * (z^2 - 1)
  constructor
  · linear_combination -z * hre + hz
  · have he : z^2 - 1 = (2 * z * (z.im : ℂ)) * Complex.I := by
      linear_combination z * him + hz
    rw [he]
    calc
      _ = -(Complex.I * Complex.I) * (2 * z * (z.im : ℂ)) := by rw [Complex.I_mul_I, neg_neg, one_mul]
      _ = _ := by ring

open Polynomial in
theorem complexAngularPolynomial_eval (k : ℕ) (D : AngularJetMap k) (u : Circle) :
    (complexAngularPolynomial k D).eval ((u : ℂ)^2) =
      (u : ℂ)^k * D (fun _ => (u : ℂ)) := by
  let z := (u : ℂ)
  induction k with
  | zero =>
    rw [complexAngularPolynomial, eval_C, pow_zero, one_mul]
    congr 1
    funext i
    exact Fin.elim0 i
  | succ k ih =>
    rw [complexAngularPolynomial]
    simp only [eval_mul, eval_sub, eval_add, eval_C, eval_X, eval_one]
    rw [ih, ih]
    have hvec : z = z.re • (1 : ℂ) + z.im • Complex.I := by
      simp [Complex.real_smul, Complex.re_add_im]
    let A := angularLast D 1 (fun _ => z)
    let B := angularLast D Complex.I (fun _ => z)
    have hD : D (fun _ => z) = (z.re : ℂ) * A + (z.im : ℂ) * B := by
      have he : D (fun _ => z) = D.curryRight (fun _ => z) z := by
        rw [ContinuousMultilinearMap.curryRight_apply]
        exact congrArg D (Fin.snoc_init_self (fun _ => z)).symm
      rw [he]
      nth_rw 2 [hvec]
      rw [map_add, map_smul, map_smul]
      rfl
    have ⟨hr, hi⟩ := circle_coordinate_formulas u
    change (1 / 2 : ℂ) * ((z^2 + 1) * (z^k * A) -
      Complex.I * ((z^2 - 1) * (z^k * B))) = z^(k+1) * D (fun _ => z)
    rw [hD, pow_succ]
    calc
      _ = (1 / 2 : ℂ) * (((z^2 + 1) : ℂ) * (z^k * A) +
        (-Complex.I * (z^2 - 1)) * (z^k * B)) := by ring
      _ = _ := by
        change 2 * z * (z.re : ℂ) = z^2 + 1 at hr
        change 2 * z * (z.im : ℂ) = -Complex.I * (z^2 - 1) at hi
        rw [← hr, ← hi]
        ring


private theorem circle_integral_zpow (ν : Measure Circle) [ν.IsMulLeftInvariant]
    (m : ℤ) : (∫ u : Circle, (u : ℂ)^m ∂ν) = if m = 0 then (ν.real univ : ℂ) else 0 := by
  by_cases hm : m = 0
  · simp [hm, Complex.real_smul]
  rw [ite_eq_right hm]
  obtain ⟨a, ha⟩ : ∃ a : Circle, (a : ℂ)^m ≠ 1 := by
    by_contra! h
    obtain ⟨k, _, hk⟩ := existsUnique_circleCharacter_zpow (1 : Circle →ₜ* ℂ)
    exact hm ((hk m (fun a => (h a).symm)).trans (hk 0 (fun a => by simp)).symm)
  have hl := integral_mul_left_eq_self (μ := ν) (fun u : Circle => (u : ℂ)^m) a
  simp only [Circle.coe_mul, mul_zpow, integral_const_mul] at hl
  have h : ((a : ℂ)^m - 1) * (∫ u : Circle, (u : ℂ)^m ∂ν) = 0 := by
    rw [sub_mul, hl, one_mul, sub_self]
  exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr ha)

private theorem circle_pow_term_integrable (ν : Measure Circle) [IsFiniteMeasure ν]
    (c : ℂ) (m : ℤ) : Integrable (fun u : Circle => c * (u : ℂ)^m) ν := by
  have hc : Continuous (fun u : Circle => c * (u : ℂ)^m) :=
    continuous_const.mul (continuous_subtype_val.zpow₀ m (fun u => Or.inl (Circle.coe_ne_zero u)))
  exact hc.integrable_of_hasCompactSupport
    (isCompact_univ.of_isClosed_subset isClosed_closure (subset_univ _))

open Polynomial in
/-- Haar averaging selects the coefficient whose angular weight cancels the
character. In degree `k`, every possible frequency is `2*j-k` for `0 ≤ j ≤ k`. -/
theorem complexAngularJet_integral (ν : Measure Circle) [IsFiniteMeasure ν]
    [ν.IsMulLeftInvariant] (m : ℤ) (k : ℕ) (D : AngularJetMap k) :
    (∫ u : Circle, (u : ℂ)^m * D (fun _ => (u : ℂ)) ∂ν) =
      ∑ j ∈ Finset.range (k + 1),
        if m + 2 * (j : ℤ) = k then (ν.real univ : ℂ) * (complexAngularPolynomial k D).coeff j else 0 := by
  let P := complexAngularPolynomial k D
  have hP : P.natDegree < k + 1 := Nat.lt_succ_of_le (complexAngularPolynomial_natDegree k D)
  have hE (u : Circle) : (u : ℂ)^m * D (fun _ => (u : ℂ)) =
      ∑ j ∈ Finset.range (k + 1), P.coeff j * (u : ℂ) ^ (m + 2 * (j : ℤ) - k) := by
    let z := (u : ℂ)
    have hn : z ≠ 0 := Circle.coe_ne_zero u
    have h := complexAngularPolynomial_eval k D u
    have hD : D (fun _ => z) = z ^ (-(k : ℤ)) * P.eval (z^2) := by
      change P.eval (z^2) = z^k * D (fun _ => z) at h
      rw [h, ← mul_assoc, ← zpow_natCast, zpow_neg_mul_zpow_self _ hn, one_mul]
    change z ^ m * D (fun _ => z) = _
    rw [hD, eval_eq_sum_range' hP, ← mul_assoc, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [show m + 2 * (j : ℤ) - k = (m + -(k : ℤ)) + 2 * (j : ℤ) by ring,
      zpow_add₀ hn, zpow_add₀ hn, zpow_mul]
    simp only [zpow_natCast]
    ac_rfl
  simp_rw [hE]
  rw [integral_finsetSum _ (fun j _ => circle_pow_term_integrable ν _ _)]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_const_mul, circle_integral_zpow]
  by_cases hj : m + 2 * (j : ℤ) = k
  · rw [ite_eq_left (sub_eq_zero.mpr hj), ite_eq_left hj, mul_comm]
  · rw [ite_eq_right (sub_ne_zero.mpr hj), ite_eq_right hj, mul_zero]

open Polynomial in
/-- The exact angular coefficient formula for the complex Mellin poles. -/
theorem complexZetaProfile_taylorCoeff (ν : Measure Circle) [IsFiniteMeasure ν]
    [ν.IsMulLeftInvariant] (m : ℤ) (f : Tests) (k : ℕ) :
    mellinTaylorCoeff (complexZetaProfile ν m f) k =
      (k.factorial : ℂ)⁻¹ * ∑ j ∈ Finset.range (k + 1),
        if m + 2 * (j : ℤ) = k then
          (ν.real univ : ℂ) * (complexAngularPolynomial k (iteratedFDeriv ℝ k f 0)).coeff j
        else 0 := by
  rw [mellinTaylorCoeff, complexZetaProfile_iteratedDeriv]
  simp only [angularJet, zero_smul]
  rw [complexAngularJet_integral]

/-- A candidate is removable whenever there is no angular monomial of the
required weight in that degree. -/
theorem complexArchimedeanZetaContinued_analyticAt_of_noAngularIndex (ν : Measure Circle)
    [IsFiniteMeasure ν] [ν.IsMulLeftInvariant] (m : ℤ) (f : Tests) (k : ℕ)
    (hk : ¬ ∃ j : ℕ, j ≤ k ∧ m + 2 * (j : ℤ) = k) :
    AnalyticAt ℂ (complexArchimedeanZetaContinued ν m f) (-(k : ℂ) / 2) := by
  have hz : mellinTaylorCoeff (complexZetaProfile ν m f) k = 0 := by
    rw [complexZetaProfile_taylorCoeff]
    suffices h : (∑ j ∈ Finset.range (k + 1), if m + 2 * (j : ℤ) = k then
        (ν.real univ : ℂ) * (complexAngularPolynomial k (iteratedFDeriv ℝ k f 0)).coeff j
      else 0) = 0 by rw [h, mul_zero]
    apply Finset.sum_eq_zero
    intro j hj
    exact ite_eq_right (fun he => hk ⟨j, Nat.le_of_lt_succ (Finset.mem_range.mp hj), he⟩)
  simpa only [hz, ite_true] using complexArchimedeanZetaContinued_order ν m f k


private theorem circle_conj_eq_inv (u : Circle) :
    (starRingEnd ℂ) (u : ℂ) = (u : ℂ)⁻¹ := by
  have h : (u : ℂ) * (starRingEnd ℂ) (u : ℂ) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Circle.norm_coe]
    norm_num
  exact mul_left_cancel₀ (Circle.coe_ne_zero u)
    (h.trans (mul_inv_cancel₀ (Circle.coe_ne_zero u)).symm)

/-- Equations (3.3.2.4) and (3.3.2.5) in the polar coordinates (z=t u).
Positive frequency gives the negative power of the conjugate coordinate. -/
theorem complex_tamagawa_poleCharacters (t : ℝ) (ht : 0 < t) (u : Circle) (r n : ℕ) :
    let z := t • (u : ℂ)
    let N := ((t ^ 2 : ℝ) : ℂ)
    let s := -((r + 2*n : ℕ) : ℂ)/2
    (N ^ s * (u : ℂ) ^ (r : ℤ) = (starRingEnd ℂ z) ^ (-(r : ℤ)) * N ^ (-(n : ℂ))) ∧
    (N ^ s * (u : ℂ) ^ (-(r : ℤ)) = z ^ (-(r : ℤ)) * N ^ (-(n : ℂ))) := by
  dsimp only
  let N : ℂ := ((t ^ 2 : ℝ) : ℂ)
  have hN : N ≠ 0 := Complex.ofReal_ne_zero.mpr (pow_ne_zero _ ht.ne')
  have hsquare (s : ℂ) : N ^ s = (t : ℂ) ^ (2 * s) := by
    simpa only [N, pow_two, Complex.ofReal_mul, Complex.cpow_ofNat_mul] using
      Complex.mul_cpow_ofReal_nonneg ht.le ht.le s
  have hsplit : -((r + 2*n : ℕ) : ℂ)/2 = -(r : ℂ)/2 + -(n : ℂ) := by push_cast; ring
  have hrad : N ^ (-((r + 2*n : ℕ) : ℂ)/2) =
      (t : ℂ) ^ (-(r : ℤ)) * N ^ (-(n : ℂ)) := by
    rw [hsplit, Complex.cpow_add _ _ hN, hsquare (-(r : ℂ)/2)]
    rw [show (2 : ℂ) * (-(r : ℂ)/2) = -(r : ℂ) by ring, ← Int.cast_natCast,
      ← Int.cast_neg, Complex.cpow_intCast]
  change (N ^ (-((r + 2*n : ℕ) : ℂ)/2) * (u : ℂ) ^ (r : ℤ) = _) ∧
    (N ^ (-((r + 2*n : ℕ) : ℂ)/2) * (u : ℂ) ^ (-(r : ℤ)) = _)
  rw [hrad, Complex.real_smul, map_mul, Complex.conj_ofReal, circle_conj_eq_inv, mul_zpow, mul_zpow,
    inv_zpow, ← zpow_neg, neg_neg]
  constructor <;> ring

/-- A cutoff of `z^j * conj z^(k-j)` realizes every allowed complex pole.
Its averaged Taylor coefficient is the circle Haar mass. -/
theorem complexArchimedeanZetaContinued_hasPole (ν : Measure Circle) [IsFiniteMeasure ν]
    [NeZero ν] (m : ℤ) (k j : ℕ) (hj : j ≤ k) (hm : m + 2 * (j : ℤ) = k) :
    ∃ f : Tests, mellinTaylorCoeff (complexZetaProfile ν m f) k = (ν.real univ : ℂ) ∧
      meromorphicOrderAt (complexArchimedeanZetaContinued ν m f) (-(k : ℂ) / 2) = (-1 : ℤ) := by
  let d := k - j
  have hjd : j + d = k := Nat.add_sub_of_le hj
  let b : ContDiffBump (0 : ℂ) := ⟨1, 2, by positivity, by norm_num⟩
  let g (z : ℂ) := (b z : ℂ) * (z^j * ((starRingEnd ℂ) z)^d)
  have hgc : HasCompactSupport g :=
    (b.hasCompactSupport.comp_left Complex.ofReal_zero).mul_right
  have hconj : ContDiff ℝ ∞ (starRingEnd ℂ : ℂ → ℂ) := Complex.conjCLE.contDiff
  have hg : ContDiff ℝ ∞ g :=
    (Complex.ofRealCLM.contDiff.comp b.contDiff).mul ((contDiff_id.pow j).mul (hconj.pow d))
  let f := hgc.toSchwartzMap hg
  have he : complexZetaProfile ν m f =ᶠ[𝓝 0] (fun t : ℝ => (ν.real univ : ℂ) * (t : ℂ)^k) := by
    have hball : Metric.ball (0 : ℝ) 1 ∈ 𝓝 0 := Metric.ball_mem_nhds _ zero_lt_one
    filter_upwards [hball] with t ht
    unfold complexZetaProfile
    have hpoint (u : Circle) : (u : ℂ)^m * f (t • (u : ℂ)) = (t : ℂ)^k := by
      have hbt : b (t • (u : ℂ)) = 1 := by
        apply b.one_of_mem_closedBall
        rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Circle.norm_coe, mul_one]
        exact (by simpa [Metric.mem_ball, dist_zero_right] using ht : ‖t‖ < 1).le
      let z := (u : ℂ)
      have hz : z ≠ 0 := Circle.coe_ne_zero u
      change z^m * g (t • z) = _
      dsimp only [g]
      rw [hbt, Complex.ofReal_one, one_mul, Complex.real_smul, map_mul, Complex.conj_ofReal,
        circle_conj_eq_inv, mul_pow, mul_pow]
      have hh : z^m * (z^j * (z⁻¹)^d) = 1 := by
        rw [← zpow_natCast, inv_pow, ← zpow_natCast, ← zpow_neg, ← zpow_add₀ hz, ← zpow_add₀ hz]
        have hzero : m + ((j : ℤ) + -(d : ℤ)) = 0 := by
          have hjd' : (j : ℤ) + d = k := by exact_mod_cast hjd
          omega
        rw [hzero, zpow_zero]
      calc
        _ = ((t : ℂ)^j * (t : ℂ)^d) * (z^m * (z^j * (z⁻¹)^d)) := by ring
        _ = _ := by rw [hh, mul_one, ← pow_add, hjd]
    simp_rw [hpoint]
    simp [Complex.real_smul]
  have hcoef : mellinTaylorCoeff (complexZetaProfile ν m f) k = (ν.real univ : ℂ) := by
    rw [mellinTaylorCoeff, he.iteratedDeriv_eq k]
    change (k.factorial : ℂ)⁻¹ * iteratedDeriv k
      (fun t : ℝ => (ν.real univ : ℂ) • ((t : ℂ)^k)) 0 = _
    rw [iteratedDeriv_fun_const_smul_field]
    simp only [← Complex.ofReal_pow]
    rw [iteratedDeriv_complex_ofReal k (h := fun x : ℝ => x ^ k) (contDiff_id.pow _)]
    simp only [iteratedDeriv_fun_pow_zero, ite_true, Complex.ofReal_natCast, smul_eq_mul]
    have hk : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
    field_simp [hk]
  have hmass : (ν.real (univ : Set Circle) : ℂ) ≠ 0 := by
    exact_mod_cast (measureReal_univ_pos (μ := ν)).ne'
  refine ⟨f, hcoef, ?_⟩
  simpa only [hcoef, ite_eq_right hmass] using complexArchimedeanZetaContinued_order ν m f k


private theorem angularLast_add {k : ℕ} (A B : AngularJetMap (k+1)) (v : ℂ) :
    angularLast (A + B) v = angularLast A v + angularLast B v := by
  ext u
  rfl

private theorem angularLast_smul {k : ℕ} (c : ℂ) (A : AngularJetMap (k+1)) (v : ℂ) :
    angularLast (c • A) v = c • angularLast A v := by
  ext u
  rfl

open Polynomial in
private theorem complexAngularPolynomial_add (k : ℕ) (A B : AngularJetMap k) :
    complexAngularPolynomial k (A + B) =
      complexAngularPolynomial k A + complexAngularPolynomial k B := by
  induction k with
  | zero => simp [complexAngularPolynomial]
  | succ k ih =>
    simp only [complexAngularPolynomial, angularLast_add, ih]
    ring

open Polynomial in
private theorem complexAngularPolynomial_smul (k : ℕ) (c : ℂ) (A : AngularJetMap k) :
    complexAngularPolynomial k (c • A) = C c * complexAngularPolynomial k A := by
  induction k with
  | zero => simp [complexAngularPolynomial, smul_eq_mul]
  | succ k ih =>
    simp only [complexAngularPolynomial, angularLast_smul, ih]
    ring

/-- Real directional differentiation on complex Schwartz tests. -/
def complexPartial (v : ℂ) : Tests →L[ℂ] Tests :=
  (SchwartzMap.evalCLM ℂ ℂ ℂ v).comp (SchwartzMap.fderivCLM ℂ ℂ ℂ)

/-- The ordinary unscaled Wirtinger derivatives on Schwartz tests. -/
def complexWirtingerZ : Tests →L[ℂ] Tests :=
  (1 / 2 : ℂ) • (complexPartial 1 - Complex.I • complexPartial Complex.I)

def complexWirtingerBar : Tests →L[ℂ] Tests :=
  (1 / 2 : ℂ) • (complexPartial 1 + Complex.I • complexPartial Complex.I)

private theorem angularLast_iteratedFDeriv (k : ℕ) (f : Tests) (x v : ℂ) :
    angularLast (iteratedFDeriv ℝ (k+1) f x) v =
      iteratedFDeriv ℝ k (complexPartial v f) x := by
  let L : (ℂ →L[ℝ] ℂ) →L[ℝ] ℂ := ContinuousLinearMap.apply ℝ ℂ v
  have hf := (f.smooth (k + 1)).fderiv_right (m := (k : ℕ∞ω)) (by exact_mod_cast le_rfl)
  change angularLast (iteratedFDeriv ℝ (k+1) f x) v =
    iteratedFDeriv ℝ k (L ∘ (fun y => fderiv ℝ f y)) x
  rw [L.iteratedFDeriv_comp_left hf.contDiffAt le_rfl]
  ext w
  change (iteratedFDeriv ℝ (k+1) f x).curryRight w v =
    iteratedFDeriv ℝ k (fun y => fderiv ℝ f y) x w v
  rw [ContinuousMultilinearMap.curryRight_apply, iteratedFDeriv_succ_apply_right]
  simp

/-- The last slot of a real Fréchet jet gives the corresponding directional
derivative of the preceding jet. -/
theorem iteratedFDeriv_complexPartial (k : ℕ) (f : Tests) (x v : ℂ) (w : Fin k → ℂ) :
    iteratedFDeriv ℝ k (complexPartial v f) x w =
      iteratedFDeriv ℝ (k+1) f x (Fin.snoc w v) := by
  rw [← angularLast_iteratedFDeriv]
  rfl

open Polynomial in
private theorem angularPolynomial_smul_add_deriv (k : ℕ) (x : ℂ) (f g : Tests) (c : ℂ) :
    complexAngularPolynomial k (iteratedFDeriv ℝ k (f + c • g : Tests) x) =
      complexAngularPolynomial k (iteratedFDeriv ℝ k f x) +
        C c * complexAngularPolynomial k (iteratedFDeriv ℝ k g x) := by
  have hf := (f.smooth k).contDiffAt (x := x)
  have hg := (g.smooth k).contDiffAt (x := x)
  change complexAngularPolynomial k (iteratedFDeriv ℝ k ((f : ℂ → ℂ) + c • (g : ℂ → ℂ)) x) = _
  have hg' : ContDiffAt ℝ (k : ℕ∞ω) (c • (g : ℂ → ℂ)) x := hg.const_smul c
  rw [iteratedFDeriv_add_apply hf hg', iteratedFDeriv_const_smul_apply hg,
    complexAngularPolynomial_add, complexAngularPolynomial_smul]

open Polynomial in
private theorem angularPolynomial_smul_deriv (k : ℕ) (x : ℂ) (f : Tests) (c : ℂ) :
    complexAngularPolynomial k (iteratedFDeriv ℝ k (c • f : Tests) x) =
      C c * complexAngularPolynomial k (iteratedFDeriv ℝ k f x) := by
  change complexAngularPolynomial k (iteratedFDeriv ℝ k (c • (f : ℂ → ℂ)) x) = _
  rw [iteratedFDeriv_const_smul_apply (f.smooth k).contDiffAt, complexAngularPolynomial_smul]

open Polynomial in
private theorem complexAngularPolynomial_wirtinger_recurrence (k : ℕ) (f : Tests) (x : ℂ) :
    complexAngularPolynomial (k+1) (iteratedFDeriv ℝ (k+1) f x) =
      X * complexAngularPolynomial k (iteratedFDeriv ℝ k (complexWirtingerZ f) x) +
        complexAngularPolynomial k (iteratedFDeriv ℝ k (complexWirtingerBar f) x) := by
  rw [complexAngularPolynomial, angularLast_iteratedFDeriv, angularLast_iteratedFDeriv]
  have hZ : complexWirtingerZ f =
      (1/2 : ℂ) • (complexPartial 1 f + (-Complex.I) • complexPartial Complex.I f) := by
    simp [complexWirtingerZ, sub_eq_add_neg, neg_smul]
  have hB : complexWirtingerBar f =
      (1/2 : ℂ) • (complexPartial 1 f + Complex.I • complexPartial Complex.I f) := by
    simp [complexWirtingerBar]
  rw [hZ, hB]
  simp only [angularPolynomial_smul_deriv, angularPolynomial_smul_add_deriv, map_neg]
  ring


private theorem complexPartial_commute (u v : ℂ) : Commute (complexPartial u) (complexPartial v) := by
  apply ContinuousLinearMap.ext
  intro f
  apply SchwartzMap.ext
  intro x
  have h₁ := congrArg (fun D : AngularJetMap 1 => D ![u]) (angularLast_iteratedFDeriv 1 f x v)
  have h₂ := congrArg (fun D : AngularJetMap 1 => D ![v]) (angularLast_iteratedFDeriv 1 f x u)
  have huv : Fin.snoc ![u] v = ![u, v] := by
    funext i
    fin_cases i <;> rfl
  have hvu : Fin.snoc ![v] u = ![v, u] := by
    funext i
    fin_cases i <;> rfl
  have hs := (f.smooth 2).contDiffAt.isSymmSndFDerivAt
    (x := x) (by simp : minSmoothness ℝ 2 ≤ (2 : ℕ∞ω))
  have hsym := hs.iteratedFDeriv_cons (v := u) (w := v)
  change complexPartial u (complexPartial v f) x = complexPartial v (complexPartial u f) x
  change fderiv ℝ (complexPartial v f) x u = fderiv ℝ (complexPartial u f) x v
  change (iteratedFDeriv ℝ 2 f x).curryRight ![u] v =
    iteratedFDeriv ℝ 1 (complexPartial v f) x ![u] at h₁
  change (iteratedFDeriv ℝ 2 f x).curryRight ![v] u =
    iteratedFDeriv ℝ 1 (complexPartial u f) x ![v] at h₂
  rw [ContinuousMultilinearMap.curryRight_apply, huv, iteratedFDeriv_one_apply] at h₁
  rw [ContinuousMultilinearMap.curryRight_apply, hvu, iteratedFDeriv_one_apply] at h₂
  exact h₁.symm.trans (hsym.trans h₂)

theorem complexWirtinger_commute : Commute complexWirtingerZ complexWirtingerBar := by
  let A := complexPartial 1
  let B := Complex.I • complexPartial Complex.I
  have h : Commute A B := (complexPartial_commute 1 Complex.I).smul_right _
  have he : Commute (A - B) (A + B) :=
    ((Commute.refl A).add_right h).sub_left (h.symm.add_right (Commute.refl B))
  exact (he.smul_left (1/2 : ℂ)).smul_right (1/2 : ℂ)

open Polynomial in
/-- The selected coefficient is the mixed unscaled Wirtinger derivative, with
the binomial factor coming from the slots of the symmetric Taylor jet. -/
theorem complexAngularPolynomial_coeff_wirtinger (k j : ℕ) (hj : j ≤ k) (f : Tests) (x : ℂ) :
    (complexAngularPolynomial k (iteratedFDeriv ℝ k f x)).coeff j =
      (k.choose j : ℂ) * (((complexWirtingerZ ^ j) * (complexWirtingerBar ^ (k-j))) f) x := by
  induction k generalizing j f with
  | zero =>
    have hj0 : j = 0 := Nat.eq_zero_of_le_zero hj
    subst j
    simp [complexAngularPolynomial]
  | succ k ih =>
    rw [complexAngularPolynomial_wirtinger_recurrence, coeff_add]
    cases j with
    | zero =>
      rw [coeff_X_mul_zero, zero_add, ih 0 (Nat.zero_le k)]
      simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, pow_zero, Nat.sub_zero]
      rw [pow_succ]
      rfl
    | succ j =>
      rw [coeff_X_mul]
      have hjk : j ≤ k := Nat.le_of_succ_le_succ hj
      rw [ih j hjk]
      by_cases h : j < k
      · rw [ih (j+1) (Nat.succ_le_of_lt h), Nat.choose_succ_succ, Nat.cast_add]
        have he : (complexWirtingerZ ^ j * complexWirtingerBar ^ (k-j)) * complexWirtingerZ =
            complexWirtingerZ ^ (j+1) * complexWirtingerBar ^ (k-j) := by
          rw [mul_assoc, (complexWirtinger_commute.pow_right (k-j)).eq.symm, ← mul_assoc, ← pow_succ]
        have he' : (complexWirtingerZ ^ (j+1) * complexWirtingerBar ^ (k-(j+1))) * complexWirtingerBar =
            complexWirtingerZ ^ (j+1) * complexWirtingerBar ^ (k-j) := by
          rw [mul_assoc, ← pow_succ]
          congr 2
          omega
        have h₁ : ((complexWirtingerZ ^ j * complexWirtingerBar ^ (k-j))
            (complexWirtingerZ f)) x =
              ((complexWirtingerZ ^ (j+1) * complexWirtingerBar ^ (k-j)) f) x := by
          exact congrArg (fun D : Tests →L[ℂ] Tests => D f x) he
        have h₂ : ((complexWirtingerZ ^ (j+1) * complexWirtingerBar ^ (k-(j+1)))
            (complexWirtingerBar f)) x =
              ((complexWirtingerZ ^ (j+1) * complexWirtingerBar ^ (k-j)) f) x := by
          exact congrArg (fun D : Tests →L[ℂ] Tests => D f x) he'
        rw [h₁, h₂, show k+1-(j+1) = k-j from Nat.succ_sub_succ_eq_sub _ _, add_mul]
      · have hj' : j = k := by omega
        subst j
        rw [coeff_eq_zero_of_natDegree_lt
          ((complexAngularPolynomial_natDegree k _).trans_lt (Nat.lt_succ_self k)), add_zero]
        simp only [Nat.choose_self, Nat.cast_one, one_mul, Nat.sub_self, pow_zero, mul_one]
        rw [pow_succ]
        rfl


/-- The exact angular criterion is equivalent to the usual pole lattice
`k = |m| + 2*n` of the character of frequency `m`. -/
theorem complexZeta_angularIndex_iff (m : ℤ) (k : ℕ) :
    (∃ j : ℕ, j ≤ k ∧ m + 2 * (j : ℤ) = k) ↔ ∃ n : ℕ, k = m.natAbs + 2*n := by
  by_cases hm : 0 ≤ m
  · have ha : (m.natAbs : ℤ) = m := Int.natAbs_of_nonneg hm
    constructor
    · rintro ⟨j, _, h⟩
      exact ⟨j, by omega⟩
    · rintro ⟨n, hn⟩
      exact ⟨n, by omega, by omega⟩
  · have ha : (m.natAbs : ℤ) = -m := Int.ofNat_natAbs_of_nonpos (by omega)
    constructor
    · rintro ⟨j, hj, h⟩
      exact ⟨k - j, by omega⟩
    · rintro ⟨n, hn⟩
      exact ⟨m.natAbs + n, by omega, by omega⟩

private def complexMixedDeltaJet (k j : ℕ) : Tests →L[ℂ] ℂ :=
  ((BoundedContinuousFunction.evalCLM ℂ (0 : ℂ)).comp
    (SchwartzMap.toBoundedContinuousFunctionCLM ℂ ℂ ℂ)).comp
    ((complexWirtingerZ ^ j) * (complexWirtingerBar ^ (k-j)))

/-- The mixed jet, with the polar measure factor, as a tempered distribution. -/
def complexArchimedeanZetaResidue (ν : Measure Circle) (k j : ℕ) : Tests →L[ℂ] ℂ :=
  (((ν.real univ : ℂ) / 2) / ((j.factorial : ℂ) * ((k-j).factorial : ℂ))) •
    complexMixedDeltaJet k j

/-- The normalized mixed derivative of the Dirac distribution, with (j)
derivatives in (z) and (k-j) in the conjugate variable. -/
def complexZetaDeltaDerivative (k j : ℕ) : Tests →L[ℂ] ℂ :=
  archimedeanDeltaDerivativeScale k • complexMixedDeltaJet k j

/-- The coefficient (A_{v,r,n}) in (3.3.2.10). -/
def complexZetaPrintedResidueConstant (r n : ℕ) : ℂ :=
  (-Complex.I) ^ r * (2 * (Real.pi : ℂ)) ^ (1 + r + 2 * n) *
    ((-1 : ℂ) ^ n / (Complex.Gamma ((1 : ℂ) + r + n) * (n.factorial : ℂ)))

private theorem complexZetaPrintedResidueConstant_scaled (r n : ℕ) :
    complexZetaPrintedResidueConstant r n * archimedeanDeltaDerivativeScale (r + 2 * n) =
      (2 * (Real.pi : ℂ)) / (((r + n).factorial : ℂ) * (n.factorial : ℂ)) := by
  let C : ℂ := 2 * (Real.pi : ℂ)
  let k := r + 2 * n
  have hgamma : Complex.Gamma ((1 : ℂ) + r + n) = ((r + n).factorial : ℂ) := by
    have he : (1 : ℂ) + r + n = ((r + n : ℕ) : ℂ) + 1 := by push_cast; ring
    rw [he, Complex.Gamma_nat_eq_factorial]
  have hp : (-Complex.I) ^ r * (-1 : ℂ) ^ n = (-Complex.I) ^ k := by
    rw [show k = r + 2 * n from rfl, pow_add, archimedean_negativeI_even]
  have hC : C ^ (1 + r + 2 * n) = C * C ^ k := by
    rw [show 1 + r + 2 * n = 1 + k by dsimp [k]; omega, pow_add, pow_one]
  unfold complexZetaPrintedResidueConstant
  rw [hgamma, show (2 * (Real.pi : ℂ)) = C from rfl, hC, div_eq_mul_inv]
  calc
    _ = C * (((r + n).factorial : ℂ) * (n.factorial : ℂ))⁻¹ *
        (C ^ k * ((-Complex.I) ^ r * (-1 : ℂ) ^ n) * archimedeanDeltaDerivativeScale k) := by ring
    _ = _ := by rw [hp, archimedeanDeltaDerivativeScale_cancel k, mul_one, div_eq_mul_inv]

/-- Printed residues (3.3.2.8) and (3.3.2.9), for the angular characters
of frequencies (r) and (-r) respectively. -/
theorem complexArchimedeanZetaResidue_printed (r n : ℕ) :
    complexArchimedeanZetaResidue complexTamagawaAngularMeasure (r + 2 * n) n =
      complexZetaPrintedResidueConstant r n • complexZetaDeltaDerivative (r + 2 * n) n ∧
    complexArchimedeanZetaResidue complexTamagawaAngularMeasure (r + 2 * n) (r + n) =
      complexZetaPrintedResidueConstant r n • complexZetaDeltaDerivative (r + 2 * n) (r + n) := by
  have h₀ : r + 2 * n - n = r + n := by omega
  have h₁ : r + 2 * n - (r + n) = n := by omega
  have hmass : ((complexTamagawaAngularMeasure.real univ : ℝ) : ℂ) / 2 = 2 * (Real.pi : ℂ) := by
    rw [complexTamagawaAngularMeasure_mass]
    push_cast
    ring
  constructor
  · unfold complexArchimedeanZetaResidue complexZetaDeltaDerivative
    rw [smul_smul, complexZetaPrintedResidueConstant_scaled, hmass, h₀, mul_comm (n.factorial : ℂ)]
  · unfold complexArchimedeanZetaResidue complexZetaDeltaDerivative
    rw [smul_smul, complexZetaPrintedResidueConstant_scaled, hmass, h₁]

/-- In the allowed lattice the residue equals the mixed Wirtinger jet
divided by the two factorials, times half the measure of the angular circle. -/
theorem complexArchimedeanZetaContinued_wirtinger_residue (ν : Measure Circle)
    [IsFiniteMeasure ν] [ν.IsMulLeftInvariant] (m : ℤ) (f : Tests)
    (k j : ℕ) (hj : j ≤ k) (hm : m + 2 * (j : ℤ) = k) :
    Tendsto (fun z => (z + (k : ℂ) / 2) * complexArchimedeanZetaContinued ν m f z)
      (𝓝[≠] (-(k : ℂ) / 2)) (𝓝 (((ν.real univ : ℂ) / 2 /
        ((j.factorial : ℂ) * ((k-j).factorial : ℂ))) *
        (((complexWirtingerZ ^ j) * (complexWirtingerBar ^ (k-j))) f) 0)) := by
  have h := complexArchimedeanZetaContinued_residue ν m f k
  rw [complexAngularJet_integral ν m k (iteratedFDeriv ℝ k f 0),
    Finset.sum_eq_single_of_mem j (Finset.mem_range_succ_iff.mpr hj),
    ite_eq_left hm, complexAngularPolynomial_coeff_wirtinger k j hj f 0] at h
  · convert h using 2
    have he : (k.choose j : ℂ) * (j.factorial : ℂ) * ((k-j).factorial : ℂ) =
        (k.factorial : ℂ) := by
      exact_mod_cast Nat.choose_mul_factorial_mul_factorial hj
    have h₀ : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    have h₁ : (j.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    have h₂ : ((k-j).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    field_simp [h₀, h₁, h₂]
    linear_combination -((ν.real univ : ℂ) * (((complexWirtingerZ ^ j) *
      (complexWirtingerBar ^ (k-j))) f) 0) * he
  · intro i _ hij
    apply ite_eq_right
    intro hi
    apply hij
    exact_mod_cast (show (i : ℤ) = (j : ℤ) by omega)

/-- Evaluation on any Schwartz test recovers the residue distribution in the allowed lattice. -/
theorem complexArchimedeanZetaContinued_residue_distribution (ν : Measure Circle)
    [IsFiniteMeasure ν] [ν.IsMulLeftInvariant] (m : ℤ) (f : Tests)
    (k j : ℕ) (hj : j ≤ k) (hm : m + 2 * (j : ℤ) = k) :
    Tendsto (fun z => (z + (k : ℂ) / 2) * complexArchimedeanZetaContinued ν m f z)
      (𝓝[≠] (-(k : ℂ) / 2)) (𝓝 (complexArchimedeanZetaResidue ν k j f)) :=
  complexArchimedeanZetaContinued_wirtinger_residue ν m f k j hj hm


instance complexTamagawaAngularMeasure_neZero : NeZero complexTamagawaAngularMeasure := by
  constructor
  intro h
  have hz : complexTamagawaAngularMeasure.real univ = 0 := by simp [h, measureReal_def]
  exact (ne_of_gt (mul_pos (by norm_num) Real.pi_pos))
    (complexTamagawaAngularMeasure_mass.symm.trans hz)

/-- In the Tamagawa normalization the complex poles are precisely the
half-integers indexed by the angular frequency, with a witness at each pole. -/
theorem complexTamagawaZetaContinued_hasPole_iff (m : ℤ) (c : ℂ) :
    (∃ f : Tests, meromorphicOrderAt
      (complexArchimedeanZetaContinued complexTamagawaAngularMeasure m f) c = (-1 : ℤ)) ↔
      ∃ n : ℕ, c = -((m.natAbs + 2*n : ℕ) : ℂ)/2 := by
  constructor
  · rintro ⟨f, hf⟩
    have hn : ¬ AnalyticAt ℂ (complexArchimedeanZetaContinued complexTamagawaAngularMeasure m f) c := by
      intro ha
      have h := ha.meromorphicOrderAt_nonneg
      rw [hf] at h
      change ((0 : ℤ) : WithTop ℤ) ≤ ((-1 : ℤ) : WithTop ℤ) at h
      have h' : (0 : ℤ) ≤ -1 := WithTop.coe_le_coe.mp h
      omega
    have h := mt (complexArchimedeanZetaContinued_analyticAt
      complexTamagawaAngularMeasure m f (s := c)) hn
    push Not at h
    obtain ⟨k, hk⟩ := h
    have hc : c = -(k : ℂ)/2 := by linear_combination hk / 2
    have hj : ∃ j : ℕ, j ≤ k ∧ m + 2*(j : ℤ) = k := by
      by_contra hj
      exact hn (hc ▸ complexArchimedeanZetaContinued_analyticAt_of_noAngularIndex
        complexTamagawaAngularMeasure m f k hj)
    obtain ⟨n, hn'⟩ := (complexZeta_angularIndex_iff m k).mp hj
    exact ⟨n, by simpa only [hn'] using hc⟩
  · rintro ⟨n, rfl⟩
    obtain ⟨j, hj, he⟩ := (complexZeta_angularIndex_iff m (m.natAbs + 2*n)).mpr ⟨n, rfl⟩
    obtain ⟨f, _, hf⟩ := complexArchimedeanZetaContinued_hasPole complexTamagawaAngularMeasure m _ j hj he
    exact ⟨f, hf⟩

/-- The two complex residues in the printed character coordinates. -/
theorem complexArchimedeanZetaContinued_printedResidue (r n : ℕ) (f : Tests) :
    let k := r + 2 * n
    Tendsto (fun z => (z + (k : ℂ)/2) *
        complexArchimedeanZetaContinued complexTamagawaAngularMeasure (r : ℤ) f z)
      (𝓝[≠] (-(k : ℂ)/2))
      (𝓝 ((complexZetaPrintedResidueConstant r n • complexZetaDeltaDerivative k n) f)) ∧
    Tendsto (fun z => (z + (k : ℂ)/2) *
        complexArchimedeanZetaContinued complexTamagawaAngularMeasure (-(r : ℤ)) f z)
      (𝓝[≠] (-(k : ℂ)/2))
      (𝓝 ((complexZetaPrintedResidueConstant r n • complexZetaDeltaDerivative k (r+n)) f)) := by
  dsimp only
  rw [← (complexArchimedeanZetaResidue_printed r n).1, ← (complexArchimedeanZetaResidue_printed r n).2]
  constructor
  · exact complexArchimedeanZetaContinued_residue_distribution complexTamagawaAngularMeasure
      (r : ℤ) f (r + 2 * n) n (by omega) (by push_cast; ring)
  · exact complexArchimedeanZetaContinued_residue_distribution complexTamagawaAngularMeasure
      (-(r : ℤ)) f (r + 2 * n) (r+n) (by omega) (by push_cast; ring)

/-- The complex-place Laurent expansion converges in the strong dual of
Schwartz space. Rescaling the Mellin parameter divides the polar coefficient
by two. -/
theorem complexArchimedeanZetaContinued_strongPrincipalPart (ν : Measure Circle) [IsFiniteMeasure ν]
    (m : ℤ) (c : ℂ) :
    ∃ (R : ℝ) (Z : ℂ → Tests →L[ℂ] ℂ) (P : Tests →L[ℂ] ℂ),
      0 < R ∧ StrongDualTaylorOnBall Z c R ∧
      (∀ z ∈ Metric.closedBall c R, complexArchimedeanZetaContinuedCLM ν m z = Z z + (z-c)⁻¹ • P) ∧
      (∀ k : ℕ, c = -(k : ℂ)/2 → ∀ f, P f = mellinTaylorCoeff (complexZetaProfile ν m f) k / 2) ∧
      ((∀ k : ℕ, c ≠ -(k : ℂ)/2) → P = 0) := by
  obtain ⟨R, Z, P, hR, hZ, heq, hP, hzero⟩ := schwartzMellinContinued_strongPrincipalPart (2*c)
  let L := complexZetaRadialSchwartz ν m
  have hT := hZ.reparametrize (d := (2 : ℂ)) (by norm_num) L
  refine ⟨R/2, fun z => (Z (2*z)).comp L, (2 : ℂ)⁻¹ • P.comp L, by positivity, ?_, ?_, ?_, ?_⟩
  · simpa only [Complex.norm_ofNat] using hT
  · intro z hz
    have hz' : 2*z ∈ Metric.closedBall (2*c) R := by
      rw [Metric.mem_closedBall, dist_eq_norm, ← mul_sub, norm_mul, Complex.norm_ofNat]
      have h : ‖z-c‖ ≤ R/2 := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hz
      linarith
    apply ContinuousLinearMap.ext
    intro f
    change schwartzMellinContinuedCLM (2*z) (L f) =
      Z (2*z) (L f) + (z-c)⁻¹ * ((2 : ℂ)⁻¹ * P (L f))
    rw [heq _ hz']
    change Z (2*z) (L f) + (2*z - 2*c)⁻¹ * P (L f) = _
    rw [← mul_sub, mul_inv_rev, mul_assoc]
  · intro k hk f
    have hc : 2*c = -(k : ℂ) := by rw [hk]; ring
    change (2 : ℂ)⁻¹ * P (L f) = _
    rw [hP k hc (L f)]
    change (2 : ℂ)⁻¹ * mellinTaylorCoeff (complexZetaProfile ν m f) k = _
    rw [div_eq_mul_inv, mul_comm]
  · intro hc
    have h : ∀ k : ℕ, 2*c ≠ -(k : ℂ) := by
      intro k hk
      exact hc k (by linear_combination hk / 2)
    apply ContinuousLinearMap.ext
    intro f
    change (2 : ℂ)⁻¹ * P (L f) = 0
    rw [hzero h, zero_apply, mul_zero]


end

end Masullo
