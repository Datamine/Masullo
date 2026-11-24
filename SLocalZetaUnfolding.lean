import SLocalThetaMellin
import OneParameterFlows
import FilteredQuotientIndentation
import WeilQuotientIntegral
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.Prod

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical ENNReal NNReal NumberField SchwartzMap TensorProduct

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]
variable (S : Finset (HeightOneSpectrum (𝓞 F)))

private abbrev Q := SIdeleQuotient F S
private abbrev K := SLocalThetaNormOne F S
private abbrev G := (SAdeles F S)ˣ
private abbrev U := Additive (sIntegerRing F S)ˣ

local instance sLocalZetaUnfolding_classMeasurable : MeasurableSpace (Q F S) := borel _
local instance sLocalZetaUnfolding_classBorel : BorelSpace (Q F S) := ⟨rfl⟩

private def ray : Multiplicative ℝ →* Q F S :=
  (QuotientGroup.mk' (sUnitImage F S)).comp (sLocalExpSection F S)

private theorem ray_continuous : Continuous (ray F S) :=
  QuotientGroup.continuous_mk.comp (sLocalExpSection_continuous F S)

private theorem modulus_ray (t : Multiplicative ℝ) :
    sLocalClassModulus F S (ray F S t) = Real.exp t.toAdd :=
  sLocalIdeleNorm_expSection F S t.toAdd

private theorem modulus_mul (x y : Q F S) :
    sLocalClassModulus F S (x * y) = sLocalClassModulus F S x * sLocalClassModulus F S y := by
  unfold sLocalClassModulus
  rw [map_mul]
  rfl

private def logModulus (q : Q F S) : ℝ := Real.log (sLocalClassModulus F S q)

private theorem logModulus_continuous : Continuous (logModulus F S) :=
  ((NNReal.continuous_coe.comp Units.continuous_val).comp
    (sQuotientNorm_proper F S).continuous).log
      (fun q => (sLocalClassModulus_pos F S q).ne')

private theorem logModulus_ray_mul (t : ℝ) (k : K F S) :
    logModulus F S (ray F S (Multiplicative.ofAdd t) * k.val) = t := by
  unfold logModulus
  rw [mul_comm (ray F S (Multiplicative.ofAdd t)) k.val, sLocalClassModulus_normOne_mul,
    modulus_ray, toAdd_ofAdd, Real.log_exp]

private theorem rayPart_mem (q : Q F S) :
    q / ray F S (Multiplicative.ofAdd (logModulus F S q)) ∈ (sQuotientNorm F S).ker := by
  change sQuotientNorm F S (q / ray F S (Multiplicative.ofAdd (logModulus F S q))) = 1
  rw [map_div, div_eq_one]
  apply Units.ext
  apply NNReal.eq
  change sLocalClassModulus F S q =
    sLocalClassModulus F S (ray F S (Multiplicative.ofAdd (logModulus F S q)))
  rw [modulus_ray, toAdd_ofAdd, logModulus, Real.exp_log (sLocalClassModulus_pos F S q)]

/-- The analytic radial coordinate and the norm-one class factor form a
topological product for the canonical S-idelic section. -/
def sLocalZetaSplit : ℝ × K F S ≃ₜ Q F S where
  toFun p := ray F S (Multiplicative.ofAdd p.1) * p.2.val
  invFun q := (logModulus F S q, ⟨q / ray F S (Multiplicative.ofAdd (logModulus F S q)),
    rayPart_mem F S q⟩)
  left_inv := by
    rintro ⟨t, k⟩
    apply Prod.ext (logModulus_ray_mul F S t k)
    apply Subtype.ext
    change (ray F S (Multiplicative.ofAdd t) * k.val) /
      ray F S (Multiplicative.ofAdd (logModulus F S (ray F S (Multiplicative.ofAdd t) * k.val))) = k.val
    rw [logModulus_ray_mul]
    exact mul_div_cancel_left (ray F S (Multiplicative.ofAdd t)) k.val
  right_inv := by
    intro q
    change ray F S (Multiplicative.ofAdd (logModulus F S q)) *
      (q / ray F S (Multiplicative.ofAdd (logModulus F S q))) = q
    exact mul_div_cancel (ray F S (Multiplicative.ofAdd (logModulus F S q))) q
  continuous_toFun := ((ray_continuous F S).comp (continuous_ofAdd.comp continuous_fst)).mul
    (continuous_subtype_val.comp continuous_snd)
  continuous_invFun := (logModulus_continuous F S).prodMk
    ((continuous_id.div' ((ray_continuous F S).comp (continuous_ofAdd.comp (logModulus_continuous F S)))).subtype_mk _)

/-- The first coordinate of the radial splitting is the logarithmic modulus. -/
theorem sLocalZetaSplit_logModulus (p : ℝ × K F S) :
    Real.log (sLocalClassModulus F S (sLocalZetaSplit F S p)) = p.1 :=
  logModulus_ray_mul F S p.1 p.2

/-- Quotient Haar normalized by the chosen norm-one Haar measure and
Lebesgue measure in the logarithmic coordinate. -/
def sLocalClassHaar (ν : Measure (K F S)) : Measure (Q F S) :=
  Measure.map (sLocalZetaSplit F S) (volume.prod ν)

theorem sLocalClassHaar_isHaar (ν : Measure (K F S)) [ν.IsHaarMeasure] :
    (sLocalClassHaar F S ν).IsHaarMeasure := by
  letI := sLocalThetaNormOne_compact F S
  letI : IsFiniteMeasure ν := ⟨isCompact_univ.measure_lt_top⟩
  let e := sLocalZetaSplit F S
  let μ : Measure (ℝ × K F S) := volume.prod ν
  have hμ : IsFiniteMeasureOnCompacts (Measure.map e μ) := Measure.IsFiniteMeasureOnCompacts.map μ e
  have hpos : Measure.IsOpenPosMeasure (Measure.map e μ) :=
    e.continuous.isOpenPosMeasure_map e.surjective
  change (Measure.map e μ).IsHaarMeasure
  refine {
    lt_top_of_isCompact := hμ.lt_top_of_isCompact
    open_pos := hpos.open_pos
    map_mul_left_eq_self := ?_ }
  intro g
  let p := e.symm g
  let A : (ℝ × K F S) → (ℝ × K F S) := Prod.map (p.1 + ·) (p.2 * ·)
  have hf : Measurable ((p.1 + ·) : ℝ → ℝ) := measurable_const.add measurable_id
  have hg : Measurable ((p.2 * ·) : K F S → K F S) :=
    (continuous_const.mul continuous_id).measurable
  have hmap : Measure.map A μ = μ := by
    change Measure.map (Prod.map _ _) (volume.prod ν) = _
    rw [← Measure.map_prod_map volume ν hf hg, map_add_left_eq_self, map_mul_left_eq_self]
  have hcomp : (g * ·) ∘ e = e ∘ A := by
    funext q
    rw [Function.comp_apply, Function.comp_apply, ← e.apply_symm_apply g]
    change (ray F S (Multiplicative.ofAdd p.1) * p.2.val) *
        (ray F S (Multiplicative.ofAdd q.1) * q.2.val) =
      ray F S (Multiplicative.ofAdd (p.1 + q.1)) * (p.2.val * q.2.val)
    rw [show Multiplicative.ofAdd (p.1 + q.1) =
      Multiplicative.ofAdd p.1 * Multiplicative.ofAdd q.1 from rfl, map_mul]
    exact mul_mul_mul_comm (ray F S (Multiplicative.ofAdd p.1)) p.2.val
      (ray F S (Multiplicative.ofAdd q.1)) q.2.val
  have hmul : Measurable ((g * ·) : Q F S → Q F S) :=
    ((continuous_const (y := g)).mul continuous_id).measurable
  rw [Measure.map_map hmul e.continuous.measurable, hcomp,
    ← Measure.map_map e.continuous.measurable (hf.prodMap hg), hmap]

/-- The complex character with prescribed unitary norm-one restriction and
spectral exponent in the canonical radial coordinate. -/
def sLocalZetaWeight (ω : PontryaginDual (K F S)) (z : ℂ) (q : Q F S) : ℂ :=
  let p := (sLocalZetaSplit F S).symm q
  Complex.exp (z * (p.1 : ℂ)) * ((ω p.2 : Circle) : ℂ)

theorem sLocalZetaWeight_continuous (ω : PontryaginDual (K F S)) (z : ℂ) :
    Continuous (sLocalZetaWeight F S ω z) := by
  let e := (sLocalZetaSplit F S).symm
  have h₁ : Continuous (fun q : Q F S => Complex.exp (z * ((e q).1 : ℂ))) := by
    exact (continuous_const.mul (Complex.continuous_ofReal.comp
      (continuous_fst.comp e.continuous))).cexp
  have h₂ : Continuous (fun q : Q F S => ((ω (e q).2 : Circle) : ℂ)) :=
    (continuous_subtype_val.comp ω.continuous).comp (continuous_snd.comp e.continuous)
  exact h₁.mul h₂

@[simp] theorem sLocalZetaWeight_split (ω : PontryaginDual (K F S)) (z : ℂ)
    (p : ℝ × K F S) :
    sLocalZetaWeight F S ω z (sLocalZetaSplit F S p) =
      Complex.exp (z * (p.1 : ℂ)) * ((ω p.2 : Circle) : ℂ) := by
  simp [sLocalZetaWeight]

/-- The separated coordinates realize the spectral weight as a multiplicative character. -/
theorem sLocalZetaWeight_mul (ω : PontryaginDual (K F S)) (z : ℂ) (q r : Q F S) :
    sLocalZetaWeight F S ω z (q * r) =
      sLocalZetaWeight F S ω z q * sLocalZetaWeight F S ω z r := by
  let e := sLocalZetaSplit F S
  obtain ⟨⟨t,k⟩, rfl⟩ := e.surjective q
  obtain ⟨⟨u,l⟩, rfl⟩ := e.surjective r
  have he : e (t,k) * e (u,l) = e (t+u,k*l) := by
    change (ray F S (Multiplicative.ofAdd t) * k.val) *
      (ray F S (Multiplicative.ofAdd u) * l.val) =
      ray F S (Multiplicative.ofAdd (t+u)) * (k.val * l.val)
    rw [show Multiplicative.ofAdd (t+u) = Multiplicative.ofAdd t * Multiplicative.ofAdd u from rfl,
      map_mul]
    exact mul_mul_mul_comm (ray F S (Multiplicative.ofAdd t)) k.val
      (ray F S (Multiplicative.ofAdd u)) l.val
  rw [he]
  change sLocalZetaWeight F S ω z (sLocalZetaSplit F S (t+u,k*l)) = _
  simp only [e, sLocalZetaWeight_split, Complex.ofReal_add, mul_add, Complex.exp_add, map_mul,
    Circle.coe_mul]
  ac_rfl

private theorem norm_sLocalZetaWeight (ω : PontryaginDual (K F S)) (z : ℂ) (q : Q F S) :
    ‖sLocalZetaWeight F S ω z q‖ = Real.exp (z.re * logModulus F S q) := by
  change ‖Complex.exp (z * (logModulus F S q : ℂ)) * _‖ = _
  rw [norm_mul, Circle.norm_coe, mul_one, Complex.norm_exp]
  simp [Complex.mul_re]

/-- On the idele group the absolute value is the modulus to the real part
of the exponent. -/
theorem norm_sLocalZetaWeight_mk (ω : PontryaginDual (K F S)) (z : ℂ) (g : G F S) :
    ‖sLocalZetaWeight F S ω z (QuotientGroup.mk g)‖ =
      Real.exp (z.re * Real.log (sLocalIdeleNorm F S g)) :=
  norm_sLocalZetaWeight F S ω z _

/-- Logarithmic growth at zero and power decay at infinity give a common
exponential bound on a positive vertical strip. -/
theorem sLocalTheta_orbit_exp_bound (T : G F S → ℝ) (A L D a b : ℝ) (N : ℕ)
    (ha : 0 < a) (hN : b + 1 < (N : ℝ)) (hA : 0 ≤ A) (hL : 0 ≤ L) (hD : 0 ≤ D)
    (hsmall : ∀ r : ℝ, 0 < r → r < 1 →
      |Real.log r| ^ (Fintype.card (SLogIndex F S) - 1) * r ^ (a / 2) ≤ D)
    (hlog : ∀ g, T g ≤ A * (1 + |Real.log (sLocalIdeleNorm F S g)|) ^
      (Fintype.card (SLogIndex F S) - 1))
    (hlarge : ∀ g, 1 ≤ sLocalIdeleNorm F S g → sLocalIdeleNorm F S g ^ N * T g ≤ L) :
    ∀ (g : G F S) (z : ℂ), a ≤ z.re → z.re ≤ b →
      let t := Real.log (sLocalIdeleNorm F S g)
      Real.exp (z.re * t) * T g ≤
        (A * 2 ^ (Fintype.card (SLogIndex F S) - 1 - 1) * (1 + D) + L) *
          Real.exp (-(min (a / 2) 1) * |t|) := by
  let d := Fintype.card (SLogIndex F S) - 1
  let c := min (a / 2) 1
  let B := A * 2 ^ (d - 1) * (1 + D)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  intro g z hz₁ hz₂
  let r := sLocalIdeleNorm F S g
  let t := Real.log r
  let V := T g
  change Real.exp (z.re * t) * V ≤ _
  have hr : 0 < r := ideleNorm_pos F (sLocalEmbed F S g).val
  have hrt : Real.exp t = r := Real.exp_log hr
  by_cases h : r < 1
  · have ht : t < 0 := Real.log_neg hr h
    have hpow : (1 + |t|) ^ d * r ^ (a / 2) ≤ 2 ^ (d - 1) * (1 + D) := calc
      _ ≤ (2 ^ (d - 1) * (1 ^ d + |t| ^ d)) * r ^ (a / 2) :=
        mul_le_mul_of_nonneg_right (add_pow_le zero_le_one (abs_nonneg _) _) (Real.rpow_nonneg hr.le _)
      _ = 2 ^ (d - 1) * (r ^ (a / 2) + |t| ^ d * r ^ (a / 2)) := by rw [one_pow]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add
        (Real.rpow_le_one hr.le h.le (half_pos ha).le) (hsmall r hr h)) (by positivity)
    have hT : V * r ^ (a / 2) ≤ B := calc
      _ ≤ (A * (1 + |t|) ^ d) * r ^ (a / 2) :=
        mul_le_mul_of_nonneg_right (hlog g) (Real.rpow_nonneg hr.le _)
      _ = A * ((1 + |t|) ^ d * r ^ (a / 2)) := by ring
      _ ≤ B := by dsimp [B]; rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hpow hA
    have he : (z.re - a / 2) * t ≤ -c * |t| := by
      rw [abs_of_neg ht, neg_mul_neg]
      apply mul_le_mul_of_nonpos_right _ ht.le
      dsimp [c]
      linarith [min_le_left (a / 2) 1]
    calc
      _ = (V * r ^ (a / 2)) * Real.exp ((z.re - a / 2) * t) := by
        rw [← hrt, ← Real.exp_mul, mul_assoc, ← Real.exp_add, mul_comm V]
        congr 2
        ring
      _ ≤ B * Real.exp (-c * |t|) :=
        mul_le_mul hT (Real.exp_le_exp.mpr he) (Real.exp_nonneg _) hB
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hL) (Real.exp_nonneg _)
  · have hr₁ : 1 ≤ r := le_of_not_gt h
    have ht : 0 ≤ t := Real.log_nonneg hr₁
    have he : (z.re - (N : ℝ)) * t ≤ -c * |t| := by
      rw [abs_of_nonneg ht]
      apply mul_le_mul_of_nonneg_right _ ht
      dsimp [c]
      linarith [min_le_right (a / 2) 1]
    calc
      _ = (r ^ N * V) * Real.exp ((z.re - (N : ℝ)) * t) := by
        rw [← hrt, ← Real.exp_nat_mul, mul_right_comm, ← Real.exp_add]
        congr 2
        ring
      _ ≤ L * Real.exp (-c * |t|) :=
        mul_le_mul (hlarge g hr₁) (Real.exp_le_exp.mpr he) (Real.exp_nonneg _) hL
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hB) (Real.exp_nonneg _)


private theorem absoluteOrbit_exp_majorant (f : GlobalBruhat F) (a b : ℝ) (ha : 0 < a) :
    ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧ Integrable (fun t : ℝ => C * Real.exp (-c * |t|)) ∧
      ∀ (g : G F S) (z : ℂ), a ≤ z.re → z.re ≤ b →
        let t := Real.log (sLocalIdeleNorm F S g)
        Real.exp (z.re * t) * (∑' u : U F S, ‖sLocalBruhatRestriction F S f
          (sIntegerDiagonal F S u.toMul.val * g.val)‖) ≤ C * Real.exp (-c * |t|) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (b + 1)
  obtain ⟨A, hA, hlog⟩ := sLocalTheta_absolute_log_bound F S f
  obtain ⟨L, hL, hlarge⟩ := sLocalTheta_absolute_large_bound F S f N
  obtain ⟨D, hD, hsmall⟩ := logPower_mul_rpow_bounded
    (Fintype.card (SLogIndex F S) - 1) (a / 2) (half_pos ha)
  let c := min (a / 2) 1
  let C := A * 2 ^ (Fintype.card (SLogIndex F S) - 1 - 1) * (1 + D) + L
  have hc : 0 < c := lt_min (half_pos ha) zero_lt_one
  exact ⟨c, C, hc, by dsimp [C]; positivity, (integrable_exp_abs_envelope c hc).const_mul _,
    sLocalTheta_orbit_exp_bound F S _ A L D a b N ha hN hA hL hD.le hsmall hlog hlarge⟩

/-- The class-group theta Mellin integral with its product Haar normalization. -/
def sLocalThetaZetaIntegral (ν : Measure (K F S)) (ω : PontryaginDual (K F S))
    (f : sLocalBruhatImage F S) (z : ℂ) : ℂ :=
  ∫ q, sLocalZetaWeight F S ω z q * sLocalTheta F S (sLocalBruhatRestriction F S f.val) q
    ∂sLocalClassHaar F S ν

private theorem logModulus_mk (g : G F S) :
    logModulus F S (QuotientGroup.mk g) = Real.log (sLocalIdeleNorm F S g) := rfl

/-- The absolute majorant for the orbit sum proves integrability before
applying Fubini, so the radial integral is the quotient integral itself. -/
theorem sLocalThetaZeta_integrable_eq_radial (ν : Measure (K F S)) [ν.IsHaarMeasure]
    (ω : PontryaginDual (K F S)) (f : sLocalBruhatImage F S) (z : ℂ) (hz : 0 < z.re) :
    Integrable (fun q => sLocalZetaWeight F S ω z q *
      sLocalTheta F S (sLocalBruhatRestriction F S f.val) q) (sLocalClassHaar F S ν) ∧
    sLocalThetaZetaIntegral F S ν ω f z = sLocalRadialMellin F S (sLocalExpSection F S) ν ω f z := by
  letI := sLocalThetaNormOne_compact F S
  letI : IsFiniteMeasure ν := ⟨isCompact_univ.measure_lt_top⟩
  let v (q : Q F S) := sLocalZetaWeight F S ω z q *
    sLocalTheta F S (sLocalBruhatRestriction F S f.val) q
  have hv : Continuous v :=
    (sLocalZetaWeight_continuous F S ω z).mul (sLocalTheta_continuous F S f.val)
  obtain ⟨c, C, _, _, hM, hm⟩ := absoluteOrbit_exp_majorant F S f.val z.re z.re hz
  have hpt (q : Q F S) : ‖v q‖ ≤ C * Real.exp (-c * |logModulus F S q|) := by
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    let t := Real.log (sLocalIdeleNorm F S g)
    change ‖sLocalZetaWeight F S ω z (QuotientGroup.mk g) *
      sLocalTheta F S (sLocalBruhatRestriction F S f.val) (QuotientGroup.mk g)‖ ≤ _
    rw [norm_mul, norm_sLocalZetaWeight, logModulus_mk, sLocalTheta_mk]
    exact (mul_le_mul_of_nonneg_left
      (norm_tsum_le_tsum_norm (sLocalTheta_restriction_summable F S f.val g))
      (Real.exp_nonneg _)).trans (hm g z le_rfl le_rfl)
  let e := sLocalZetaSplit F S
  have hprod : Integrable (v ∘ e) (volume.prod ν) := by
    apply (hM.comp_fst (ν := ν)).mono' (hv.comp e.continuous).aestronglyMeasurable
    refine Eventually.of_forall fun p => ?_
    have he : logModulus F S (e p) = p.1 := logModulus_ray_mul F S p.1 p.2
    simpa only [Function.comp_apply, he] using hpt (e p)
  refine ⟨(e.toMeasurableEquiv.measurableEmbedding.integrable_map_iff).mpr hprod, ?_⟩
  change (∫ q, v q ∂Measure.map e.toMeasurableEquiv (volume.prod ν)) = _
  rw [integral_map_equiv]
  change (∫ p, (v ∘ e) p ∂volume.prod ν) = _
  rw [integral_prod _ hprod]
  apply integral_congr_ae
  refine Eventually.of_forall fun t => ?_
  change (∫ k : K F S, v (e (t, k)) ∂ν) =
    Complex.exp (z * (t : ℂ)) *
      sLocalHomogeneousTheta F S ν ω f.val (QuotientGroup.mk (sLocalExpSection F S (Multiplicative.ofAdd t)))
  rw [sLocalHomogeneousTheta, ← integral_const_mul]
  apply integral_congr_ae
  refine Eventually.of_forall fun k => ?_
  have he : e (t, k) =
      k.val * QuotientGroup.mk (sLocalExpSection F S (Multiplicative.ofAdd t)) :=
    mul_comm (ray F S (Multiplicative.ofAdd t)) k.val
  let θ := sLocalTheta F S (sLocalBruhatRestriction F S f.val)
  change sLocalZetaWeight F S ω z (e (t, k)) * θ (e (t, k)) =
    Complex.exp (z * (t : ℂ)) * (((ω k : Circle) : ℂ) *
      θ (k.val * QuotientGroup.mk (sLocalExpSection F S (Multiplicative.ofAdd t))))
  calc
    _ = (Complex.exp (z * (t : ℂ)) * ((ω k : Circle) : ℂ)) * θ (e (t, k)) :=
      congrArg (· * θ (e (t, k))) (sLocalZetaWeight_split F S ω z (t, k))
    _ = _ := by rw [mul_assoc, he]

/-- Holomorphy of the quotient theta Mellin integral follows under the actual
product Haar normalization. -/
theorem sLocalThetaZeta_analytic (ν : Measure (K F S)) [ν.IsHaarMeasure]
    (ω : PontryaginDual (K F S)) (f : sLocalBruhatImage F S) :
    AnalyticOnNhd ℂ (sLocalThetaZetaIntegral F S ν ω f) {z | 0 < z.re} := by
  let V : Set ℂ := {z | 0 < z.re}
  have ho : IsOpen V := isOpen_lt continuous_const Complex.continuous_re
  intro z hz
  have hl := sLocalRadialMellin_analytic F S (sLocalExpSection F S)
    (sLocalExpSection_continuous F S) (sLocalIdeleNorm_expSection F S) ν ω f z hz
  apply hl.congr
  filter_upwards [ho.mem_nhds hz] with w hw
  exact (sLocalThetaZeta_integrable_eq_radial F S ν ω f w hw).2.symm



/-- The radial integral uses the quasi-character on the chosen section.
A change of section multiplies the quasi-character and homogeneous theta
by inverse factors, leaving the integrand unchanged. -/
theorem sLocalRadialMellin_section_independent (τ : Multiplicative ℝ →* G F S)
    (hτ : ∀ t : ℝ, sLocalIdeleNorm F S (τ (Multiplicative.ofAdd t)) = Real.exp t)
    (ν : Measure (K F S)) [ν.IsHaarMeasure]
    (ω : PontryaginDual (K F S)) (f : sLocalBruhatImage F S) (z : ℂ) :
    (∫ t : ℝ, let q : Q F S := QuotientGroup.mk (τ (Multiplicative.ofAdd t))
      sLocalZetaWeight F S ω z q * sLocalHomogeneousTheta F S ν ω f.val q) =
      sLocalRadialMellin F S (sLocalExpSection F S) ν ω f z := by
  unfold sLocalRadialMellin
  apply integral_congr_ae
  refine Eventually.of_forall fun t => ?_
  let q : Q F S := QuotientGroup.mk (τ (Multiplicative.ofAdd t))
  let e := sLocalZetaSplit F S
  have ht : (e.symm q).1 = t := by
    change logModulus F S q = t
    rw [logModulus_mk, hτ, Real.log_exp]
  let k := (e.symm q).2
  have heq : e (t, k) = q := by
    have hp : (t, k) = e.symm q := Prod.ext ht.symm rfl
    exact (congrArg e hp).trans (e.apply_symm_apply q)
  have hprod : q = k.val * ray F S (Multiplicative.ofAdd t) :=
    heq.symm.trans (mul_comm (ray F S (Multiplicative.ofAdd t)) k.val)
  change sLocalZetaWeight F S ω z q * sLocalHomogeneousTheta F S ν ω f.val q =
    Complex.exp (z * (t : ℂ)) * sLocalHomogeneousTheta F S ν ω f.val
      (ray F S (Multiplicative.ofAdd t))
  have hw := (congrArg (sLocalZetaWeight F S ω z) heq.symm).trans
    (sLocalZetaWeight_split F S ω z (t, k))
  have hθ := (congrArg (sLocalHomogeneousTheta F S ν ω f.val) hprod).trans
    (sLocalHomogeneousTheta_translate F S ν ω f.val k (ray F S (Multiplicative.ofAdd t)))
  rw [hw, hθ, mul_assoc, ← mul_assoc ((ω k : Circle) : ℂ),
    mul_inv_cancel₀ (Circle.coe_ne_zero _), one_mul]

private abbrev H := sUnitImage F S

local instance sLocalZetaUnfolding_idelesMeasurable : MeasurableSpace (G F S) := borel _
local instance sLocalZetaUnfolding_idelesBorel : BorelSpace (G F S) := ⟨rfl⟩

private theorem sLocalForgetTail_isOpenQuotient :
    IsOpenQuotientMap (fun g : sIdeleBlock F S => (sBlockUnitProduct F S g).1) := by
  let e := sBlockUnitProduct F S
  refine ⟨fun x => ⟨e.symm (x, 1), ?_⟩, continuous_fst.comp e.continuous,
    isOpenMap_fst.comp e.toHomeomorph.isOpenMap⟩
  exact congrArg Prod.fst (e.apply_symm_apply (x, 1))

theorem sLocalIdeles_locallyCompact : LocallyCompactSpace (G F S) := by
  letI := (sIdeleBlock_locallyCompact_hausdorff F S).1
  exact (sLocalForgetTail_isOpenQuotient F S).locallyCompactSpace

local instance sLocalZetaUnfolding_idelesLocallyCompact : LocallyCompactSpace (G F S) := sLocalIdeles_locallyCompact F S

local instance sLocalZetaUnfolding_idelesT2 : T2Space (G F S) := by
  letI := (sIdeleBlock_locallyCompact_hausdorff F S).2
  exact ((sBlockUnitProduct F S).symm.toHomeomorph.isEmbedding.comp
    (isEmbedding_prodMkLeft (X := G F S) (1 : (SIntegralTail F S)ˣ))).t2Space

theorem sLocalIdeles_secondCountable : SecondCountableTopology (G F S) := by
  letI : SecondCountableTopology (Adeles F) := adeles_secondCountable F
  letI : SecondCountableTopology (Adeles F)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  letI : SecondCountableTopology (Idele F) := Units.isEmbedding_embedProduct.secondCountableTopology
  letI : SecondCountableTopology (sIdeleBlock F S) :=
    (sIdeleBlock_open F S).isOpenEmbedding_subtypeVal.isEmbedding.secondCountableTopology
  have h := sLocalForgetTail_isOpenQuotient F S
  exact h.isQuotientMap.secondCountableTopology h.isOpenMap

local instance sLocalZetaUnfolding_idelesSecondCountable : SecondCountableTopology (G F S) := sLocalIdeles_secondCountable F S

local instance sLocalZetaUnfolding_unitsDiscrete : DiscreteTopology (H F S) := sThetaUnitImage_discrete F S

local instance sLocalZetaUnfolding_countingHaar : (Measure.count : Measure (H F S)).IsHaarMeasure :=
  subgroup_count_isHaarMeasure (H F S)

local instance sLocalZetaUnfolding_countingRegular : Measure.Regular (Measure.count : Measure (H F S)) := by
  letI : LocallyCompactSpace (H F S) := (sUnitImage_closed F S).locallyCompactSpace
  exact Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _

/-- The quasi-character weighted test on the multiplicative S-adeles. -/
def sLocalIdelicZetaIntegrand (ω : PontryaginDual (K F S)) (z : ℂ)
    (f : sLocalBruhatImage F S) (g : G F S) : ℂ :=
  sLocalZetaWeight F S ω z (QuotientGroup.mk g) * sLocalBruhatRestriction F S f.val g.val

/-- The idelic Mellin integral on the multiplicative S-adeles. -/
def sLocalIdelicZetaIntegral (μ : Measure (G F S)) (ω : PontryaginDual (K F S))
    (f : sLocalBruhatImage F S) (z : ℂ) : ℂ :=
  ∫ g, sLocalIdelicZetaIntegrand F S ω z f g ∂μ

private theorem orbit_integrand (ω : PontryaginDual (K F S)) (z : ℂ)
    (f : sLocalBruhatImage F S) (g : G F S) (u : U F S) :
    sLocalIdelicZetaIntegrand F S ω z f (g * (sUnitOrbitEquiv F S u).val) =
      sLocalZetaWeight F S ω z (QuotientGroup.mk g) *
        sLocalBruhatRestriction F S f.val (sIntegerDiagonal F S u.toMul.val * g.val) := by
  unfold sLocalIdelicZetaIntegrand
  have hu := (sUnitOrbitEquiv F S u).property
  have hq : (QuotientGroup.mk (g * (sUnitOrbitEquiv F S u).val) : Q F S) = QuotientGroup.mk g := by
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).mpr hu]
    exact mul_one (QuotientGroup.mk g : Q F S)
  rw [hq, Units.val_mul, sUnitOrbitEquiv_val]
  exact congrArg (fun x => sLocalZetaWeight F S ω z (QuotientGroup.mk g) *
    sLocalBruhatRestriction F S f.val x) (mul_comm _ _)

private theorem fiber_norm_sum (ω : PontryaginDual (K F S)) (z : ℂ)
    (f : sLocalBruhatImage F S) (g : G F S) :
    Summable (fun h : H F S => ‖sLocalIdelicZetaIntegrand F S ω z f (g * h.val)‖) ∧
      (∑' h : H F S, ‖sLocalIdelicZetaIntegrand F S ω z f (g * h.val)‖) =
        Real.exp (z.re * Real.log (sLocalIdeleNorm F S g)) *
          (∑' u : U F S, ‖sLocalBruhatRestriction F S f.val
            (sIntegerDiagonal F S u.toMul.val * g.val)‖) := by
  let e := sUnitOrbitEquiv F S
  have hfun (u : U F S) :
      ‖sLocalIdelicZetaIntegrand F S ω z f (g * (e u).val)‖ =
        Real.exp (z.re * Real.log (sLocalIdeleNorm F S g)) *
          ‖sLocalBruhatRestriction F S f.val (sIntegerDiagonal F S u.toMul.val * g.val)‖ := by
    rw [orbit_integrand, norm_mul, norm_sLocalZetaWeight, logModulus_mk]
  refine ⟨e.summable_iff.mp (((sLocalTheta_restriction_summable F S f.val g).mul_left _).congr
    fun u => (hfun u).symm), ?_⟩
  rw [← e.tsum_eq (f := fun h => ‖sLocalIdelicZetaIntegrand F S ω z f (g * h.val)‖)]
  simp_rw [hfun, tsum_mul_left]

private theorem fiber_integral_eq (ω : PontryaginDual (K F S)) (z : ℂ)
    (f : sLocalBruhatImage F S) (g : G F S) :
    lcaCosetIntegral (H F S) Measure.count (sLocalIdelicZetaIntegrand F S ω z f)
      (QuotientGroup.mk g) =
    sLocalZetaWeight F S ω z (QuotientGroup.mk g) *
      sLocalTheta F S (sLocalBruhatRestriction F S f.val) (QuotientGroup.mk g) := by
  letI : Countable (H F S) := countable_of_Lindelof_of_discrete
  rw [lcaCosetIntegral_mk, integral_countable (integrable_count_iff.mpr (fiber_norm_sum F S ω z f g).1)]
  simp only [count_real_singleton, one_smul, sLocalTheta_mk]
  rw [← (sUnitOrbitEquiv F S).tsum_eq (f := fun h => sLocalIdelicZetaIntegrand F S ω z f (g * h.val))]
  simp_rw [orbit_integrand, tsum_mul_left]
  rfl

/-- Weil unfolding for a Haar measure and its quotient measure with counting
measure on the S-units. The idelic zeta integral is absolutely convergent
and equals the theta Mellin integral on the positive half-plane. -/
theorem sLocalIdelicZeta_integrable_eq_theta (μ : Measure (G F S)) [μ.IsHaarMeasure]
    (ν : Measure (K F S)) [ν.IsHaarMeasure]
    (hν : IsWeilQuotientMeasure (H F S) μ Measure.count (sLocalClassHaar F S ν))
    (ω : PontryaginDual (K F S)) (f : sLocalBruhatImage F S) (z : ℂ) (hz : 0 < z.re) :
    Integrable (sLocalIdelicZetaIntegrand F S ω z f) μ ∧
      sLocalIdelicZetaIntegral F S μ ω f z = sLocalThetaZetaIntegral F S ν ω f z := by
  letI : μ.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _
  letI := sLocalThetaNormOne_compact F S
  letI : IsFiniteMeasure ν := ⟨isCompact_univ.measure_lt_top⟩
  let w := sLocalIdelicZetaIntegrand F S ω z f
  have hw : Measurable w :=
    ((sLocalZetaWeight_continuous F S ω z).comp QuotientGroup.continuous_mk).measurable.mul
      ((sLocalBruhatRestriction_continuous F S f.val).comp Units.continuous_val).measurable
  obtain ⟨c, C, _, hC, hM, hmajor⟩ := absoluteOrbit_exp_majorant F S f.val z.re z.re hz
  let M (q : Q F S) : ℝ := C * Real.exp (-c * |logModulus F S q|)
  have hi : Integrable M (sLocalClassHaar F S ν) := by
    let e := sLocalZetaSplit F S
    apply (e.toMeasurableEquiv.measurableEmbedding.integrable_map_iff).mpr
    change Integrable (M ∘ e) (volume.prod ν)
    have he (p : ℝ × K F S) : (M ∘ e) p = C * Real.exp (-c * |p.1|) := by
      change C * Real.exp (-c * |logModulus F S (e p)|) = _
      rw [show logModulus F S (e p) = p.1 from logModulus_ray_mul F S p.1 p.2]
    simpa only [funext he] using hM.comp_fst (ν := ν)
  have hfin : (∫⁻ q, ∫⁻ h : H F S, ‖w (q.out * h.val)‖₊ ∂Measure.count
      ∂sLocalClassHaar F S ν) < ∞ := by
    have hMf : (∫⁻ q, ENNReal.ofReal (M q) ∂sLocalClassHaar F S ν) < ∞ := by
      rw [← ofReal_integral_eq_lintegral_ofReal hi
        (Eventually.of_forall fun _ => mul_nonneg hC (Real.exp_nonneg _))]
      exact ENNReal.ofReal_lt_top
    apply lt_of_le_of_lt (lintegral_mono (g := fun q => ENNReal.ofReal (M q)) ?_) hMf
    intro q
    change (∫⁻ h : H F S, ‖w (q.out * h.val)‖₊ ∂Measure.count) ≤ ENNReal.ofReal (M q)
    rw [lintegral_count]
    have hs := fiber_norm_sum F S ω z f q.out
    change (∑' h : H F S, (‖w (q.out * h.val)‖₊ : ℝ≥0∞)) ≤ _
    simp_rw [← enorm_eq_nnnorm, ← ofReal_norm]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) hs.1, hs.2]
    apply ENNReal.ofReal_le_ofReal
    have he : (QuotientGroup.mk q.out : Q F S) = q := Quotient.out_eq' q
    have hlog : logModulus F S q = Real.log (sLocalIdeleNorm F S q.out) :=
      (congrArg (logModulus F S) he.symm).trans (logModulus_mk F S q.out)
    simpa only [M, hlog] using hmajor q.out z le_rfl le_rfl
  obtain ⟨hwint, hEq⟩ := integrable_of_weilNormIntegral (H F S) (sUnitImage_closed F S)
    μ Measure.count (sLocalClassHaar F S ν) hν hw hfin
  refine ⟨hwint, hEq.trans ?_⟩
  apply integral_congr_ae
  refine Eventually.of_forall fun q => ?_
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  exact fiber_integral_eq F S ω z f g


/-- The given S-idelic Haar measure and counting measure on the diagonal
S-units determine the Haar normalization on the S-idele class group. -/
theorem sLocalQuotientHaar_existsUnique (μ : Measure (G F S)) [μ.IsHaarMeasure] :
    ∃! ν : Measure (Q F S), IsWeilQuotientMeasure (H F S) μ Measure.count ν := by
  letI : μ.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _
  exact weilQuotientMeasure_existsUnique (H F S) (sUnitImage_closed F S) μ Measure.count

/-- Every S-idelic Haar measure admits a compatible product normalization on
the class group, with Lebesgue measure in the logarithmic coordinate. -/
theorem sLocalClassHaar_exists_weil (μ : Measure (G F S)) [μ.IsHaarMeasure] :
    ∃ ν : Measure (K F S), ν.IsHaarMeasure ∧
      IsWeilQuotientMeasure (H F S) μ Measure.count (sLocalClassHaar F S ν) := by
  letI : IsClosed (H F S : Set (G F S)) := sUnitImage_closed F S
  letI : LocallyCompactSpace (Q F S) :=
    (QuotientGroup.isOpenQuotientMap_mk (N := H F S)).locallyCompactSpace
  letI : T1Space (Q F S) := QuotientGroup.t1Space_iff.mpr (sUnitImage_closed F S)
  letI : SecondCountableTopology (Q F S) :=
    QuotientGroup.isOpenQuotientMap_mk.isQuotientMap.secondCountableTopology
      QuotientGroup.isOpenQuotientMap_mk.isOpenMap
  letI := sLocalThetaNormOne_compact F S
  let ν₀ : Measure (K F S) := Measure.haar
  letI : ν₀.IsHaarMeasure := inferInstance
  letI : IsFiniteMeasure ν₀ := ⟨isCompact_univ.measure_lt_top⟩
  let ρ := sLocalClassHaar F S ν₀
  letI : ρ.IsHaarMeasure := sLocalClassHaar_isHaar F S ν₀
  letI : ρ.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _
  obtain ⟨η, hη, _⟩ := sLocalQuotientHaar_existsUnique F S μ
  letI := hη.1
  letI := hη.2.1
  let c := Measure.haarScalarFactor η ρ
  have hc : c ≠ 0 := (Measure.haarScalarFactor_pos_of_isHaarMeasure η ρ).ne'
  have heq : η = c • ρ := Measure.isMulLeftInvariant_eq_smul_of_regular η ρ
  refine ⟨c • ν₀, Measure.IsHaarMeasure.nnreal_smul ν₀ hc, ?_⟩
  have hmap : sLocalClassHaar F S (c • ν₀) = c • ρ := by
    unfold sLocalClassHaar ρ
    rw [Measure.prod_smul_right, Measure.map_smul]
    rfl
  rw [hmap, ← heq]
  exact hη

/-- Changing the continuous norm section preserves the split Haar measure.
Adapted from mccorvie/riemann-masullo, commit cae3d7f, under Apache-2.0. -/
theorem sLocalClassHaar_eq_map_section (ν : Measure (K F S)) [ν.IsHaarMeasure]
    (τ : Multiplicative ℝ →* G F S) (hτc : Continuous τ)
    (hτ : ∀ t : ℝ, sLocalIdeleNorm F S (τ (Multiplicative.ofAdd t)) = Real.exp t) :
    Measure.map (fun p : ℝ × K F S =>
      (QuotientGroup.mk (τ (Multiplicative.ofAdd p.1)) : Q F S) * p.2.val) (volume.prod ν) =
        sLocalClassHaar F S ν := by
  letI := sLocalThetaNormOne_compact F S
  letI : IsFiniteMeasure ν := ⟨isCompact_univ.measure_lt_top⟩
  let q (t : ℝ) : Q F S := QuotientGroup.mk (τ (Multiplicative.ofAdd t))
  have hq : Continuous q := QuotientGroup.continuous_mk.comp (hτc.comp continuous_ofAdd)
  have hlog (t : ℝ) : logModulus F S (q t) = t := by
    change Real.log (sLocalIdeleNorm F S (τ (Multiplicative.ofAdd t))) = t
    rw [hτ, Real.log_exp]
  let u (t : ℝ) : K F S := ⟨q t / ray F S (Multiplicative.ofAdd t), by
    simpa only [hlog] using rayPart_mem F S (q t)⟩
  have hu : Continuous u :=
    (hq.div' ((ray_continuous F S).comp continuous_ofAdd)).subtype_mk _
  let shear (p : ℝ × K F S) : ℝ × K F S := (p.1, u p.1 * p.2)
  have hs : Continuous shear := continuous_fst.prodMk ((hu.comp continuous_fst).mul continuous_snd)
  have hmap : Measure.map shear (volume.prod ν) = volume.prod ν := by
    ext A hA
    rw [Measure.map_apply hs.measurable hA, Measure.prod_apply (hs.measurable hA),
      Measure.prod_apply hA]
    apply lintegral_congr
    intro t
    have hm : Measurable ((u t * ·) : K F S → K F S) :=
      (continuous_const.mul continuous_id).measurable
    have hset : MeasurableSet (Prod.mk t ⁻¹' A) := measurable_prodMk_left hA
    change ν (((u t * ·) : K F S → K F S) ⁻¹' (Prod.mk t ⁻¹' A)) = ν (Prod.mk t ⁻¹' A)
    rw [← Measure.map_apply hm hset, map_mul_left_eq_self]
  have hcomp : (fun p : ℝ × K F S => q p.1 * p.2.val) = sLocalZetaSplit F S ∘ shear := by
    funext p
    change q p.1 * p.2.val = ray F S (Multiplicative.ofAdd p.1) *
      (q p.1 / ray F S (Multiplicative.ofAdd p.1) * p.2.val)
    rw [← mul_assoc, mul_comm (ray F S (Multiplicative.ofAdd p.1)), div_mul_cancel]
  change Measure.map (fun p : ℝ × K F S => q p.1 * p.2.val) (volume.prod ν) = _
  rw [hcomp, ← Measure.map_map (sLocalZetaSplit F S).continuous.measurable hs.measurable, hmap]
  rfl

private theorem sLocalClassHaar_injective (ν ρ : Measure (K F S))
    [SFinite ν] [SFinite ρ] (h : sLocalClassHaar F S ν = sLocalClassHaar F S ρ) : ν = ρ := by
  let e := (sLocalZetaSplit F S).toMeasurableEquiv
  have hprod : volume.prod ν = volume.prod ρ := e.map_measurableEquiv_injective h
  ext A _
  have hmass := congrArg (fun μ : Measure (ℝ × K F S) => μ (Icc (0 : ℝ) 1 ×ˢ A)) hprod
  simpa [Measure.prod_prod, Real.volume_Icc] using hmass

/-- The norm-one Haar measure in 3.3.1.1(3) is unique and yields the
Weil quotient normalization in every continuous norm section. -/
theorem sLocalNormOneQuotientHaar_existsUnique (μ : Measure (G F S)) [μ.IsHaarMeasure] :
    ∃! ν : Measure (K F S), ν.IsHaarMeasure ∧ ν.Regular ∧
      ∀ (τ : Multiplicative ℝ →* G F S), Continuous τ →
        (∀ t : ℝ, sLocalIdeleNorm F S (τ (Multiplicative.ofAdd t)) = Real.exp t) →
        IsWeilQuotientMeasure (H F S) μ Measure.count
          (Measure.map (fun p : ℝ × K F S =>
            (QuotientGroup.mk (τ (Multiplicative.ofAdd p.1)) : Q F S) * p.2.val) (volume.prod ν)) := by
  obtain ⟨ν, hν, hνweil⟩ := sLocalClassHaar_exists_weil F S μ
  letI := sLocalThetaNormOne_compact F S
  letI : IsClosed (H F S : Set (G F S)) := sUnitImage_closed F S
  letI : T1Space (Q F S) := QuotientGroup.t1Space_iff.mpr (sUnitImage_closed F S)
  letI : SecondCountableTopology (Q F S) :=
    QuotientGroup.isOpenQuotientMap_mk.isQuotientMap.secondCountableTopology
      QuotientGroup.isOpenQuotientMap_mk.isOpenMap
  letI : SecondCountableTopology (K F S) :=
    TopologicalSpace.Subtype.secondCountableTopology (K F S : Set (Q F S))
  letI := hν
  let ρ₀ : Measure (K F S) := Measure.haarMeasure ⟨⟨univ, isCompact_univ⟩, by simp⟩
  letI : ρ₀.Regular := Measure.regular_haarMeasure
  have hνreg : ν.Regular := by
    rw [Measure.isMulLeftInvariant_eq_smul ν ρ₀]
    infer_instance
  refine ⟨ν, ⟨hν, hνreg, ?_⟩, ?_⟩
  · intro τ hτc hτ
    rw [sLocalClassHaar_eq_map_section F S ν τ hτc hτ]
    exact hνweil
  · rintro ρ ⟨hρ, -, hρweil⟩
    letI := hρ
    letI : IsFiniteMeasure ν := ⟨isCompact_univ.measure_lt_top⟩
    letI : IsFiniteMeasure ρ := ⟨isCompact_univ.measure_lt_top⟩
    have h := hρweil (sLocalExpSection F S) (sLocalExpSection_continuous F S)
      (sLocalIdeleNorm_expSection F S)
    change IsWeilQuotientMeasure (H F S) μ Measure.count (sLocalClassHaar F S ρ) at h
    exact sLocalClassHaar_injective F S ρ ν
      ((sLocalQuotientHaar_existsUnique F S μ).unique h hνweil)

/-- The idelic integral equals the homogeneous theta Mellin integral
computed using any section of the modulus and the compatible Haar measure. -/
theorem sLocalIdelicZeta_eq_radial (μ : Measure (G F S)) [μ.IsHaarMeasure]
    (ν : Measure (K F S)) [ν.IsHaarMeasure]
    (hν : IsWeilQuotientMeasure (H F S) μ Measure.count (sLocalClassHaar F S ν))
    (τ : Multiplicative ℝ →* G F S)
    (hτ : ∀ t : ℝ, sLocalIdeleNorm F S (τ (Multiplicative.ofAdd t)) = Real.exp t)
    (ω : PontryaginDual (K F S)) (f : sLocalBruhatImage F S) (z : ℂ) (hz : 0 < z.re) :
    sLocalIdelicZetaIntegral F S μ ω f z =
      ∫ t : ℝ, let q : Q F S := QuotientGroup.mk (τ (Multiplicative.ofAdd t))
        sLocalZetaWeight F S ω z q * sLocalHomogeneousTheta F S ν ω f.val q := by
  calc
    _ = sLocalThetaZetaIntegral F S ν ω f z :=
      (sLocalIdelicZeta_integrable_eq_theta F S μ ν hν ω f z hz).2
    _ = sLocalRadialMellin F S (sLocalExpSection F S) ν ω f z :=
      (sLocalThetaZeta_integrable_eq_radial F S ν ω f z hz).2
    _ = _ := (sLocalRadialMellin_section_independent F S τ hτ ν ω f z).symm

/-- The two endpoint exponents give an integrable majorant on every closed
strip inside the domain of absolute convergence. -/
theorem sLocalIdelicZeta_strip_majorant (μ : Measure (G F S)) [μ.IsHaarMeasure]
    (ω : PontryaginDual (K F S)) (f : sLocalBruhatImage F S) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    ∃ M : G F S → ℝ, Integrable M μ ∧ ∀ (z : ℂ), a ≤ z.re → z.re ≤ b → ∀ g,
      ‖sLocalIdelicZetaIntegrand F S ω z f g‖ ≤ M g := by
  obtain ⟨ν, hhaar, hν⟩ := sLocalClassHaar_exists_weil F S μ
  letI := hhaar
  let L := sLocalIdelicZetaIntegrand F S ω (a : ℂ) f
  let R := sLocalIdelicZetaIntegrand F S ω (b : ℂ) f
  have hL : Integrable L μ :=
    (sLocalIdelicZeta_integrable_eq_theta F S μ ν hν ω f (a : ℂ) (by simpa using ha)).1
  have hR : Integrable R μ :=
    (sLocalIdelicZeta_integrable_eq_theta F S μ ν hν ω f (b : ℂ) (by simpa using ha.trans_le hab)).1
  refine ⟨fun g => ‖L g‖ + ‖R g‖, hL.norm.add hR.norm, fun z hza hzb g => ?_⟩
  let t := Real.log (sLocalIdeleNorm F S g)
  let v := ‖sLocalBruhatRestriction F S f.val g.val‖
  simp only [L, R, sLocalIdelicZetaIntegrand, norm_mul, norm_sLocalZetaWeight, logModulus_mk,
    Complex.ofReal_re]
  change Real.exp (z.re * t) * v ≤ Real.exp (a * t) * v + Real.exp (b * t) * v
  by_cases ht : 0 ≤ t
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hzb ht))
      (norm_nonneg _)).trans (le_add_of_nonneg_left (by positivity))
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_right hza
      (le_of_not_ge ht))) (norm_nonneg _)).trans (le_add_of_nonneg_right (by positivity))

/-- On an increasing measurable exhaustion, a common integrable majorant
controls the truncation error uniformly in the parameter. The tail argument
is adapted from the parallel RiemannMasullo formalization. -/
private theorem tendstoUniformlyOn_setIntegral_of_majorant
    {A P : Type*} [MeasurableSpace A] {μ : Measure A} {B : ℕ → Set A}
    (hB : ∀ n, MeasurableSet (B n)) (hmono : Monotone B) (hcover : ∀ x, ∃ n, x ∈ B n)
    {u : P → A → ℂ} {E : Set P} {M : A → ℝ} (hM : Integrable M μ)
    (hu : ∀ p ∈ E, Integrable (u p) μ) (hle : ∀ p ∈ E, ∀ x, ‖u p x‖ ≤ M x) :
    TendstoUniformlyOn (fun n p => ∫ x in B n, u p x ∂μ) (fun p => ∫ x, u p x ∂μ)
      atTop E := by
  have hempty : (⋂ n, (B n)ᶜ) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨n, hn⟩ := hcover x
    exact (mem_iInter.mp hx n) hn
  have hlim : Tendsto (fun n => ∫ x in (B n)ᶜ, M x ∂μ) atTop (𝓝 0) := by
    simpa only [hempty, setIntegral_empty] using
      (tendsto_setIntegral_of_antitone (μ := μ) (f := M) (fun n => (hB n).compl)
        (fun _ _ hij => compl_subset_compl.mpr (hmono hij)) ⟨0, hM.integrableOn⟩)
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [(tendsto_order.mp hlim).2 ε hε] with n hn p hp
  rw [dist_eq_norm, ← integral_add_compl (hB n) (hu p hp), add_sub_cancel_left]
  exact ((norm_integral_le_integral_norm _).trans
    (setIntegral_mono_on (hu p hp).norm.integrableOn hM.integrableOn (hB n).compl
      (fun x _ => hle p hp x))).trans_lt hn

/-- The band with lower modulus `1 / (n+1)` and upper modulus `n+1`,
written using the logarithmic modulus. -/
def sLocalZetaBand {A : Type*} (logNorm : A → ℝ) (n : ℕ) : Set A :=
  {x | |logNorm x| ≤ Real.log ((n : ℝ) + 1)}

theorem mem_sLocalZetaBand_log_iff {r : ℝ} (hr : 0 < r) (n : ℕ) :
    r ∈ sLocalZetaBand Real.log n ↔ (((n : ℝ) + 1)⁻¹ ≤ r ∧ r ≤ (n : ℝ) + 1) := by
  have hn : 0 < (n : ℝ) + 1 := by positivity
  change |Real.log r| ≤ Real.log ((n : ℝ) + 1) ↔ _
  rw [abs_le, ← Real.log_inv, Real.log_le_log_iff (inv_pos.mpr hn) hr,
    Real.log_le_log_iff hr hn]

private theorem tendstoUniformlyOn_sLocalZetaBand
    {A P : Type*} [MeasurableSpace A] {μ : Measure A} {logNorm : A → ℝ}
    (hl : Measurable logNorm) {u : P → A → ℂ} {E : Set P} {M : A → ℝ}
    (hM : Integrable M μ) (hu : ∀ p ∈ E, Integrable (u p) μ)
    (hle : ∀ p ∈ E, ∀ x, ‖u p x‖ ≤ M x) :
    TendstoUniformlyOn (fun n p => ∫ x in sLocalZetaBand logNorm n, u p x ∂μ)
      (fun p => ∫ x, u p x ∂μ) atTop E := by
  apply tendstoUniformlyOn_setIntegral_of_majorant (B := sLocalZetaBand logNorm)
      (fun n => measurableSet_le (continuous_abs.measurable.comp hl) measurable_const) ?_ ?_ hM hu hle
  · intro i j hij x hx
    change |logNorm x| ≤ Real.log ((i : ℝ) + 1) at hx
    change |logNorm x| ≤ Real.log ((j : ℝ) + 1)
    exact hx.trans (Real.log_le_log (by positivity)
      (add_le_add_left (Nat.cast_le.mpr hij) 1))
  · intro x
    obtain ⟨n, hn⟩ := exists_nat_gt (Real.exp |logNorm x|)
    refine ⟨n, ?_⟩
    change |logNorm x| ≤ Real.log ((n : ℝ) + 1)
    exact (Real.log_exp _).symm.le.trans
      (Real.log_le_log (Real.exp_pos _) (hn.le.trans (le_add_of_nonneg_right zero_le_one)))

/-- Modulus-band truncation of the actual idelic integral converges uniformly
on each positive closed strip, simultaneously in the unitary parameter.
This gives the compact convergence in clause (1) of Theorem 3.3.1.1. -/
theorem sLocalIdelicZeta_tendstoUniformlyOn_band (μ : Measure (G F S)) [μ.IsHaarMeasure]
    (f : sLocalBruhatImage F S) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    TendstoUniformlyOn
      (fun n (p : PontryaginDual (K F S) × ℂ) =>
        ∫ g in sLocalZetaBand (fun g : G F S => Real.log (sLocalIdeleNorm F S g)) n,
          sLocalIdelicZetaIntegrand F S p.1 p.2 f g ∂μ)
      (fun p => sLocalIdelicZetaIntegral F S μ p.1 f p.2) atTop
      {p | p.2.re ∈ Icc a b} := by
  obtain ⟨M, hM, hbound⟩ := sLocalIdelicZeta_strip_majorant F S μ 1 f a b ha hab
  obtain ⟨ν, hhaar, hν⟩ := sLocalClassHaar_exists_weil F S μ
  letI := hhaar
  have hl : Measurable (fun g : G F S => Real.log (sLocalIdeleNorm F S g)) :=
    (logModulus_continuous F S).measurable.comp QuotientGroup.continuous_mk.measurable
  apply tendstoUniformlyOn_sLocalZetaBand hl hM
  · intro p hp
    exact (sLocalIdelicZeta_integrable_eq_theta F S μ ν hν p.1 f p.2 (ha.trans_le hp.1)).1
  · intro p hp g
    calc
      ‖sLocalIdelicZetaIntegrand F S p.1 p.2 f g‖ =
          ‖sLocalIdelicZetaIntegrand F S 1 p.2 f g‖ := by
        simp only [sLocalIdelicZetaIntegrand, norm_mul, norm_sLocalZetaWeight]
      _ ≤ M g := hbound p.2 hp.1 hp.2 g

/-- Quotient theta integrals converge uniformly under modulus truncation
on positive closed strips, simultaneously in the unitary parameter. -/
theorem sLocalThetaZeta_tendstoUniformlyOn_band (ν : Measure (K F S)) [ν.IsHaarMeasure]
    (f : sLocalBruhatImage F S) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    TendstoUniformlyOn
      (fun n (p : PontryaginDual (K F S) × ℂ) =>
        ∫ q in sLocalZetaBand (logModulus F S) n,
          sLocalZetaWeight F S p.1 p.2 q * sLocalTheta F S (sLocalBruhatRestriction F S f.val) q
          ∂sLocalClassHaar F S ν)
      (fun p => sLocalThetaZetaIntegral F S ν p.1 f p.2) atTop
      {p | p.2.re ∈ Icc a b} := by
  let v (ω : PontryaginDual (K F S)) (z : ℂ) (q : Q F S) :=
    sLocalZetaWeight F S ω z q * sLocalTheta F S (sLocalBruhatRestriction F S f.val) q
  have hI (ω : PontryaginDual (K F S)) (z : ℂ) (hz : 0 < z.re) :
      Integrable (v ω z) (sLocalClassHaar F S ν) :=
    (sLocalThetaZeta_integrable_eq_radial F S ν ω f z hz).1
  have hL := hI 1 a (by simpa using ha)
  have hR := hI 1 b (by simpa using ha.trans_le hab)
  apply tendstoUniformlyOn_sLocalZetaBand (logModulus_continuous F S).measurable (hL.norm.add hR.norm)
  · intro p hp
    exact hI p.1 p.2 (ha.trans_le hp.1)
  · intro p hp q
    have hp' : p.2.re ∈ Icc a b := hp
    let t := logModulus F S q
    simp only [v, norm_mul, norm_sLocalZetaWeight, Complex.ofReal_re]
    by_cases ht : 0 ≤ t
    · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hp'.2 ht))
        (norm_nonneg _)).trans (le_add_of_nonneg_left (by positivity))
    · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_right hp'.1
        (le_of_not_ge ht))) (norm_nonneg _)).trans (le_add_of_nonneg_right (by positivity))

/-- The radial theta Mellin integral along any continuous norm section converges
uniformly under modulus truncation on positive closed strips. -/
theorem sLocalRadialMellin_tendstoUniformlyOn_band
    (τ : Multiplicative ℝ →* G F S) (hτ : Continuous τ)
    (hτnorm : ∀ t : ℝ, sLocalIdeleNorm F S (τ (Multiplicative.ofAdd t)) = Real.exp t)
    (ν : Measure (K F S)) [ν.IsHaarMeasure]
    (ω : PontryaginDual (K F S)) (f : sLocalBruhatImage F S) (a b : ℝ) (ha : 0 < a) :
    TendstoUniformlyOn
      (fun n (z : ℂ) => ∫ t in sLocalZetaBand id n, Complex.exp (z * (t : ℂ)) *
        sLocalHomogeneousTheta F S ν ω f.val (QuotientGroup.mk (τ (Multiplicative.ofAdd t))))
      (sLocalRadialMellin F S τ ν ω f) atTop {z | z.re ∈ Icc a b} := by
  obtain ⟨c, C, _, _, hM, hbound⟩ := sLocalRadialMellin_strip_majorant F S τ hτnorm ν ω
    {f} (Bornology.isVonNBounded_singleton (𝕜 := ℂ) f) a b ha
  apply tendstoUniformlyOn_sLocalZetaBand measurable_id hM
  · intro z hz
    exact sLocalRadialMellin_integrable F S τ hτ hτnorm ν ω f z (ha.trans_le hz.1)
  · intro z hz
    exact hbound f (mem_singleton f) z hz.1 hz.2

/-- The actual idelic zeta integral is holomorphic in the canonical
spectral coordinate on the positive half-plane. -/
theorem sLocalIdelicZeta_analytic (μ : Measure (G F S)) [μ.IsHaarMeasure]
    (ω : PontryaginDual (K F S)) (f : sLocalBruhatImage F S) :
    AnalyticOnNhd ℂ (sLocalIdelicZetaIntegral F S μ ω f) {z | 0 < z.re} := by
  obtain ⟨ν, hhaar, hν⟩ := sLocalClassHaar_exists_weil F S μ
  letI := hhaar
  intro z hz
  have ho : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  apply (sLocalThetaZeta_analytic F S ν ω f z hz).congr
  filter_upwards [ho.mem_nhds hz] with w hw
  exact (sLocalIdelicZeta_integrable_eq_theta F S μ ν hν ω f w hw).2.symm

private def zetaThetaIntegrand (ω : PontryaginDual (K F S)) (z : ℂ)
    (f : sLocalBruhatImage F S) (q : Q F S) : ℂ :=
  sLocalZetaWeight F S ω z q * sLocalTheta F S (sLocalBruhatRestriction F S f.val) q

/-- A fixed positive-half-plane zeta character gives a continuous linear
functional on the S-local Schwartz–Bruhat test space. -/
def sLocalThetaZetaCLM (ν : Measure (K F S)) [ν.IsHaarMeasure]
    (ω : PontryaginDual (K F S)) (z : ℂ) (hz : 0 < z.re) : sLocalBruhatImage F S →L[ℂ] ℂ := by
  let Z := zetaThetaIntegrand F S ω z
  have hI (f : sLocalBruhatImage F S) : Integrable (Z f) (sLocalClassHaar F S ν) :=
    (sLocalThetaZeta_integrable_eq_radial F S ν ω f z hz).1
  have hadd (f g : sLocalBruhatImage F S) (q : Q F S) : Z (f + g) q = Z f q + Z g q := by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    simp only [Z, zetaThetaIntegrand, sLocalTheta_mk]
    change sLocalZetaWeight F S ω z (QuotientGroup.mk x) * sLocalThetaEval F S x (f.val + g.val) = _
    rw [map_add, mul_add]
    rfl
  have hsmul (c : ℂ) (f : sLocalBruhatImage F S) (q : Q F S) : Z (c • f) q = c • Z f q := by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    simp only [Z, zetaThetaIntegrand, sLocalTheta_mk]
    change sLocalZetaWeight F S ω z (QuotientGroup.mk x) * sLocalThetaEval F S x (c • f.val) = _
    rw [map_smul]
    exact mul_left_comm _ _ _
  let L : sLocalBruhatImage F S →ₗ[ℂ] ℂ :=
    { toFun := fun f => ∫ q, Z f q ∂sLocalClassHaar F S ν
      map_add' := fun f g => by
        simp_rw [hadd]
        exact integral_add (hI f) (hI g)
      map_smul' := fun c f => by
        simp_rw [hsmul]
        exact integral_smul c (Z f) }
  refine ⟨L, ?_⟩
  obtain ⟨N, hN⟩ := exists_nat_gt (z.re + 1)
  obtain ⟨p, hp, hlog⟩ := sLocalTheta_log_seminorm F S
  obtain ⟨r, hr, hlarge⟩ := sLocalTheta_largeNorm_seminorm F S N
  obtain ⟨D, hD, hsmall⟩ := logPower_mul_rpow_bounded
    (Fintype.card (SLogIndex F S) - 1) (z.re / 2) (half_pos hz)
  let a : ℝ≥0 := ⟨2 ^ (Fintype.card (SLogIndex F S) - 1 - 1) * (1 + D), by positivity⟩
  let P : Seminorm ℂ (sLocalBruhatImage F S) := a • p + r
  have hP : Continuous P := (continuous_const.mul hp).add hr
  let c := min (z.re / 2) 1
  have hc : 0 < c := lt_min (half_pos hz) zero_lt_one
  let E (q : Q F S) := Real.exp (-c * |logModulus F S q|)
  letI := sLocalThetaNormOne_compact F S
  letI : IsFiniteMeasure ν := ⟨isCompact_univ.measure_lt_top⟩
  have hE : Integrable E (sLocalClassHaar F S ν) := by
    let e := sLocalZetaSplit F S
    apply (e.toMeasurableEquiv.measurableEmbedding.integrable_map_iff).mpr
    change Integrable (E ∘ e) (volume.prod ν)
    have he (x : ℝ × K F S) : (E ∘ e) x = Real.exp (-c * |x.1|) :=
      congrArg (fun t => Real.exp (-c * |t|)) (logModulus_ray_mul F S x.1 x.2)
    simpa only [funext he] using (integrable_exp_abs_envelope c hc).comp_fst (ν := ν)
  have hpt (f : sLocalBruhatImage F S) (q : Q F S) : ‖Z f q‖ ≤ P f * E q := by
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    simp only [Z, zetaThetaIntegrand, norm_mul, norm_sLocalZetaWeight, E,
      logModulus_mk, sLocalTheta_mk]
    have h := sLocalTheta_orbit_exp_bound F S
      (fun g => ‖sLocalThetaOnIdeles F S (sLocalBruhatRestriction F S f.val) g‖)
      (p f) (r f) D z.re z.re N hz hN (apply_nonneg _ _) (apply_nonneg _ _) hD.le hsmall
      (hlog f) (hlarge f) g z le_rfl le_rfl
    have hpval : P f = p f * 2 ^ (Fintype.card (SLogIndex F S) - 1 - 1) * (1 + D) + r f := by
      change (2 ^ (Fintype.card (SLogIndex F S) - 1 - 1) * (1 + D)) * p f + r f = _
      ring
    simpa only [hpval, c] using h
  let C : ℝ≥0 := ⟨∫ q, E q ∂sLocalClassHaar F S ν, integral_nonneg (fun _ => Real.exp_nonneg _)⟩
  have hb (f : sLocalBruhatImage F S) : ‖L f‖ ≤ C * P f := by
    calc
      _ ≤ ∫ q, ‖Z f q‖ ∂sLocalClassHaar F S ν := norm_integral_le_integral_norm _
      _ ≤ ∫ q, P f * E q ∂sLocalClassHaar F S ν :=
        integral_mono (hI f).norm (hE.const_mul _) (hpt f)
      _ = _ := by rw [integral_const_mul]; exact mul_comm _ _
  have hn : Continuous ((normSeminorm ℂ ℂ).comp L) :=
    Seminorm.continuous_of_le (q := C • P) (continuous_const.mul hP) hb
  apply continuous_of_continuousAt_zero L
  rw [ContinuousAt, map_zero, tendsto_zero_iff_norm_tendsto_zero]
  exact hn.tendsto' _ _ (map_zero _)

@[simp] theorem sLocalThetaZetaCLM_apply (ν : Measure (K F S)) [ν.IsHaarMeasure]
    (ω : PontryaginDual (K F S)) (z : ℂ) (hz : 0 < z.re) (f : sLocalBruhatImage F S) :
    sLocalThetaZetaCLM F S ν ω z hz f = sLocalThetaZetaIntegral F S ν ω f z := rfl

/-- Lemma 3.3.1.3 in the norm-one character and spectral exponent coordinates. -/
theorem sLocalIdelicZeta_continuous (μ : Measure (G F S)) [μ.IsHaarMeasure]
    (ω : PontryaginDual (K F S)) (z : ℂ) (hz : 0 < z.re) :
    Continuous (fun f => sLocalIdelicZetaIntegral F S μ ω f z) := by
  obtain ⟨ν, hhaar, hν⟩ := sLocalClassHaar_exists_weil F S μ
  letI := hhaar
  exact (sLocalThetaZetaCLM F S ν ω z hz).continuous.congr fun f =>
    (sLocalIdelicZeta_integrable_eq_theta F S μ ν hν ω f z hz).2.symm


/-- The canonical logarithmic coordinates parametrize all continuous
quasi-characters, including those in the positive half-plane. -/
theorem sLocalZetaWeight_represents (χ : QuasiCharacter (Q F S)) :
    ∃ (ω : PontryaginDual (K F S)) (z : ℂ), (∀ q, χ q = sLocalZetaWeight F S ω z q) ∧
      (0 < z.re ↔ 1 < ‖χ (ray F S (Multiplicative.ofAdd 1))‖) := by
  letI := sLocalThetaNormOne_compact F S
  have hc : Continuous (fun k : K F S => ‖χ k.val‖) :=
    (χ.continuous_toFun.comp continuous_subtype_val).norm
  obtain ⟨M, hM⟩ := (isCompact_univ.image hc).bddAbove
  have hle (k : K F S) : ‖χ k.val‖ ≤ 1 := by
    by_contra! hk
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt M hk
    apply hn.not_ge
    have hb := hM (mem_image_of_mem (fun k : K F S => ‖χ k.val‖) (mem_univ (k ^ n)))
    simpa only [Subgroup.coe_pow, map_pow, norm_pow] using hb
  have hn (k : K F S) : ‖χ k.val‖ = 1 := by
    refine (hle k).antisymm ?_
    have hinv := hle k⁻¹
    rw [Subgroup.coe_inv, map_inv, norm_inv] at hinv
    have hpos : 0 < ‖χ k.val‖ := norm_pos_iff.mpr (χ.toMonoidHom.toHomUnits k.val).ne_zero
    exact (inv_le_one₀ hpos).mp hinv
  have hSphere (k : K F S) : χ k.val ∈ Submonoid.unitSphere ℂ := by
    change dist (χ k.val) 0 = 1
    simpa only [dist_zero_right] using hn k
  let ω : PontryaginDual (K F S) :=
    { toFun := fun k => ⟨χ k.val, hSphere k⟩
      map_one' := Subtype.ext (map_one χ)
      map_mul' := fun x y => Subtype.ext (map_mul χ x.val y.val)
      continuous_toFun := (χ.continuous_toFun.comp continuous_subtype_val).subtype_mk hSphere }
  let θ := (χ.toMonoidHom.comp (ray F S)).toHomUnits
  have hθ : Continuous (fun t : ℝ => (θ (Multiplicative.ofAdd t) : ℂ)) :=
    χ.continuous_toFun.comp ((ray_continuous F S).comp continuous_ofAdd)
  obtain ⟨z, hz, _⟩ := complex_oneParameter_exp θ hθ
  have hRay (t : ℝ) : χ (ray F S (Multiplicative.ofAdd t)) = Complex.exp (z * (t : ℂ)) := hz t
  refine ⟨ω, z, ?_, ?_⟩
  · intro q
    obtain ⟨⟨t, k⟩, rfl⟩ := (sLocalZetaSplit F S).surjective q
    rw [sLocalZetaWeight_split]
    change χ (ray F S (Multiplicative.ofAdd t) * k.val) = Complex.exp (z * (t : ℂ)) * χ k.val
    rw [map_mul, hRay]
  · rw [hRay, Complex.ofReal_one, mul_one, Complex.norm_exp, ← Real.exp_zero, Real.exp_lt_exp]

/-- Lemma 3.3.1.3. The S-idelic zeta integral for any positive
quasi-character is a continuous functional of the Schwartz–Bruhat test. -/
theorem sLocalQuasiCharacter_zeta_continuous (μ : Measure (G F S)) [μ.IsHaarMeasure]
    (χ : QuasiCharacter (Q F S))
    (hχ : 1 < ‖χ (QuotientGroup.mk (sLocalExpSection F S (Multiplicative.ofAdd 1)))‖) :
    Continuous (fun f : sLocalBruhatImage F S =>
      ∫ g : G F S, χ (QuotientGroup.mk g) * sLocalBruhatRestriction F S f.val g.val ∂μ) := by
  obtain ⟨ω, z, he, hz⟩ := sLocalZetaWeight_represents F S χ
  have hz' : 0 < z.re := hz.mpr hχ
  simpa only [he, sLocalIdelicZetaIntegral, sLocalIdelicZetaIntegrand] using
    sLocalIdelicZeta_continuous F S μ ω z hz'


/-- The same continuity assertion in the canonical inductive tensor
presentation with a finite Schwartz–Bruhat factor. -/
theorem sLocalQuasiCharacter_zeta_tensor_continuous (μ : Measure (G F S)) [μ.IsHaarMeasure]
    (χ : QuasiCharacter (Q F S))
    (hχ : 1 < ‖χ (QuotientGroup.mk (sLocalExpSection F S (Multiplicative.ofAdd 1)))‖) :
    let A := 𝓢(mixedEmbedding.mixedSpace F, ℂ)
    let B := locallyConstantTests (∀ v : S, v.val.adicCompletion F)
    letI : TopologicalSpace B := finestLocallyConvexTopology B
    letI : TopologicalSpace (A ⊗[ℂ] B) := inductiveTensorTopology A B
    Continuous (fun f : A ⊗[ℂ] B =>
      ∫ g : G F S, χ (QuotientGroup.mk g) *
        sLocalBruhatRestriction F S (sLocalBruhatTensorEquiv F S f).val g.val ∂μ) := by
  let A := 𝓢(mixedEmbedding.mixedSpace F, ℂ)
  let B := locallyConstantTests (∀ v : S, v.val.adicCompletion F)
  letI : TopologicalSpace B := finestLocallyConvexTopology B
  letI : TopologicalSpace (A ⊗[ℂ] B) := inductiveTensorTopology A B
  let e : (A ⊗[ℂ] B) ≃L[ℂ] sLocalBruhatImage F S := sLocalBruhatTensorEquiv F S
  change Continuous (fun f : A ⊗[ℂ] B =>
    ∫ g : G F S, χ (QuotientGroup.mk g) * sLocalBruhatRestriction F S (e f).val g.val ∂μ)
  exact (sLocalQuasiCharacter_zeta_continuous F S μ χ hχ).comp e.continuous

end

end Masullo
