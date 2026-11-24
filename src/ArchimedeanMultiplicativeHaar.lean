import ArchimedeanLogarithms
import ComplexArchimedeanZeta
import RealArchimedeanZeta
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

open Filter Function MeasureTheory Metric Set
open scoped SchwartzMap Topology

namespace Masullo

noncomputable section

section Scalar

variable {K : Type*} [RCLike K]
variable [MeasurableSpace Kˣ] [BorelSpace Kˣ]
variable [MeasurableSpace (sphere (0 : K) 1)] [BorelSpace (sphere (0 : K) 1)]

def realLogPolarCoordinates : ℝ × sphere (0 : K) 1 ≃ₜ Kˣ :=
  (show ℝ × sphere (0 : K) 1 ≃ₜ Multiplicative ℝ × sphere (0 : K) 1 from
    { toFun := fun p => (Multiplicative.ofAdd p.1, p.2)
      invFun := fun p => (p.1.toAdd, p.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := (continuous_ofAdd.comp continuous_fst).prodMk continuous_snd
      continuous_invFun := (continuous_toAdd.comp continuous_fst).prodMk continuous_snd }).trans
    (scalarArchPolar (K := K)).toHomeomorph

omit [MeasurableSpace Kˣ] [BorelSpace Kˣ]
  [MeasurableSpace (sphere (0 : K) 1)] [BorelSpace (sphere (0 : K) 1)] in
@[simp] theorem realLogPolarCoordinates_val (p : ℝ × sphere (0 : K) 1) :
    ((realLogPolarCoordinates p : Kˣ) : K) = (Real.exp p.1 : K) * (p.2 : K) :=
  scalarArchPolar_val (Multiplicative.ofAdd p.1, p.2)

/-- Multiplicative Haar in logarithmic radius and unit-sphere angle. -/
def scalarLogPolarHaar (ν : Measure (sphere (0 : K) 1)) : Measure Kˣ :=
  (volume.prod ν).map realLogPolarCoordinates

theorem scalarLogPolarHaar_isHaar (ν : Measure (sphere (0 : K) 1)) [ν.IsHaarMeasure] :
    (scalarLogPolarHaar ν).IsHaarMeasure := by
  letI : IsFiniteMeasure ν := ⟨isCompact_univ.measure_lt_top⟩
  let e := realLogPolarCoordinates (K := K)
  let μ : Measure (ℝ × sphere (0 : K) 1) := volume.prod ν
  have hμ : IsFiniteMeasureOnCompacts (Measure.map e μ) := Measure.IsFiniteMeasureOnCompacts.map μ e
  have hpos : Measure.IsOpenPosMeasure (Measure.map e μ) :=
    e.continuous.isOpenPosMeasure_map e.surjective
  change (Measure.map e μ).IsHaarMeasure
  refine
    { lt_top_of_isCompact := hμ.lt_top_of_isCompact
      open_pos := hpos.open_pos
      map_mul_left_eq_self := ?_ }
  intro g
  let p := e.symm g
  let A : (ℝ × sphere (0 : K) 1) → (ℝ × sphere (0 : K) 1) :=
    Prod.map (p.1 + ·) (p.2 * ·)
  have hf : Measurable ((p.1 + ·) : ℝ → ℝ) := measurable_const.add measurable_id
  have hg : Measurable ((p.2 * ·) : sphere (0 : K) 1 → sphere (0 : K) 1) :=
    (continuous_const.mul continuous_id).measurable
  have hmap : Measure.map A μ = μ := by
    change Measure.map (Prod.map _ _) (volume.prod ν) = _
    rw [← Measure.map_prod_map volume ν hf hg, map_add_left_eq_self, map_mul_left_eq_self]
  have hcomp : (g * ·) ∘ e = e ∘ A := by
    funext q
    rw [Function.comp_apply, Function.comp_apply, ← e.apply_symm_apply g]
    change scalarArchPolar (Multiplicative.ofAdd p.1, p.2) *
        scalarArchPolar (Multiplicative.ofAdd q.1, q.2) =
      scalarArchPolar (Multiplicative.ofAdd (p.1 + q.1), p.2 * q.2)
    exact (map_mul (scalarArchPolar (K := K)) _ _).symm
  have hmul : Measurable ((g * ·) : Kˣ → Kˣ) :=
    ((continuous_const (y := g)).mul continuous_id).measurable
  rw [Measure.map_map hmul e.continuous.measurable, hcomp,
    ← Measure.map_map e.continuous.measurable (hf.prodMap hg), hmap]

theorem scalarLogPolarHaar_integral (ν : Measure (sphere (0 : K) 1)) (g : Kˣ → ℂ) :
    (∫ u, g u ∂scalarLogPolarHaar ν) =
      ∫ p : ℝ × sphere (0 : K) 1, g (realLogPolarCoordinates p) ∂volume.prod ν := by
  exact integral_map_equiv (realLogPolarCoordinates (K := K)).toMeasurableEquiv g

private theorem integral_exp_substitution {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (g : ℝ → E) :
    (∫ x : ℝ, Real.exp x • g (Real.exp x)) = ∫ t in Ioi (0 : ℝ), g t := by
  symm
  have h := integral_image_eq_integral_abs_deriv_smul (s := univ) (f := Real.exp)
    MeasurableSet.univ (fun t _ => (Real.hasDerivAt_exp t).hasDerivWithinAt)
    Real.exp_injective.injOn g
  simpa only [image_univ, Real.range_exp, Measure.restrict_univ, abs_of_pos (Real.exp_pos _)] using h

private theorem integrable_exp_substitution {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (g : ℝ → E) :
    Integrable (fun x : ℝ => Real.exp x • g (Real.exp x)) ↔ IntegrableOn g (Ioi 0) := by
  have h := integrableOn_image_iff_integrableOn_abs_deriv_smul (s := univ) (f := Real.exp)
    MeasurableSet.univ (fun t _ => (Real.hasDerivAt_exp t).hasDerivWithinAt)
    Real.exp_injective.injOn g
  simpa only [image_univ, Real.range_exp, integrableOn_univ, abs_of_pos (Real.exp_pos _)] using h.symm

/-- Change from the normalized Haar integral in logarithmic coordinates to
polar integration with the radial Jacobian included in the given integrand. -/
theorem scalarLogPolarHaar_eq_polarIntegral (ν : Measure (sphere (0 : K) 1)) [IsFiniteMeasure ν]
    {g : Kˣ → ℂ} (hg : Measurable g)
    {H : ℝ × sphere (0 : K) 1 → ℂ}
    (hH : Integrable H (((volume : Measure ℝ).restrict (Ioi 0)).prod ν))
    (he : ∀ (x : ℝ) (u : sphere (0 : K) 1),
      g (realLogPolarCoordinates (x, u)) = Real.exp x • H (Real.exp x, u)) :
    Integrable g (scalarLogPolarHaar ν) ∧
      (∫ u, g u ∂scalarLogPolarHaar ν) =
        ∫ p, H p ∂((volume : Measure ℝ).restrict (Ioi 0)).prod ν := by
  let e := realLogPolarCoordinates (K := K)
  let G (p : ℝ × sphere (0 : K) 1) := g (e p)
  have hGm : AEStronglyMeasurable G (volume.prod ν) :=
    (hg.comp e.continuous.measurable).aestronglyMeasurable
  have hEq (u : sphere (0 : K) 1) :
      (∫ x, G (x, u)) = ∫ r in Ioi (0 : ℝ), H (r, u) := by
    simp only [G, e, he]
    exact integral_exp_substitution (fun r => H (r, u))
  have hnEq (u : sphere (0 : K) 1) :
      (∫ x, ‖G (x, u)‖) = ∫ r in Ioi (0 : ℝ), ‖H (r, u)‖ := by
    simp only [G, e, he, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact integral_exp_substitution (fun r => ‖H (r, u)‖)
  have hG : Integrable G (volume.prod ν) := by
    apply (integrable_prod_iff' hGm).mpr
    refine ⟨?_, hH.integral_norm_prod_right.congr (.of_forall fun u => (hnEq u).symm)⟩
    filter_upwards [hH.prod_left_ae] with u hu
    simpa only [G, e, he] using (integrable_exp_substitution (fun r => H (r, u))).mpr hu
  refine ⟨(integrable_map_equiv e.toMeasurableEquiv g).mpr hG, ?_⟩
  rw [scalarLogPolarHaar_integral, integral_prod_symm _ hG, integral_prod_symm _ hH]
  apply integral_congr_ae
  exact .of_forall hEq

/-- A positive radial power divided by a sufficiently large polynomial
weight is integrable for the normalized logarithmic polar measure. -/
theorem scalarLogPolarHaar_integrable_majorant (ν : Measure (sphere (0 : K) 1))
    [IsFiniteMeasure ν] {b : ℝ} {m : ℕ} (hb : 0 < b) (hm : b < m) :
    Integrable (fun u : Kˣ => ‖(u : K)‖ ^ b / max 1 (‖(u : K)‖ ^ m))
      (scalarLogPolarHaar ν) := by
  let e := realLogPolarCoordinates (K := K)
  let w (x : ℝ) := if x ≤ 0 then Real.exp (b * x) else Real.exp ((b - m) * x)
  have h₁ : IntegrableOn w (Iic 0) := by
    apply (integrableOn_exp_mul_Iic hb 0).congr_fun _ measurableSet_Iic
    exact fun x hx => (ite_eq_left (mem_Iic.mp hx)).symm
  have h₂ : IntegrableOn w (Ioi 0) := by
    apply (integrableOn_exp_mul_Ioi (sub_neg.mpr hm) 0).congr_fun _ measurableSet_Ioi
    exact fun x hx => (ite_eq_right (not_le_of_gt (mem_Ioi.mp hx))).symm
  have h : Integrable w := by
    have hi := h₁.union h₂
    rwa [Iic_union_Ioi, integrableOn_univ] at hi
  apply (integrable_map_equiv e.toMeasurableEquiv _).2
  apply (h.comp_fst ν).congr
  exact .of_forall fun p => by
    change w p.1 = ‖(e p : K)‖ ^ b / max 1 (‖(e p : K)‖ ^ m)
    simp only [e, realLogPolarCoordinates_val, norm_mul, RCLike.norm_ofReal,
      abs_of_pos (Real.exp_pos _)]
    have hu : ‖(p.2 : K)‖ = 1 := mem_sphere_zero_iff_norm.mp p.2.property
    rw [hu, mul_one, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp, ← Real.exp_nat_mul]
    dsimp only [w]
    by_cases hp : p.1 ≤ 0
    · rw [ite_eq_left hp, max_eq_left (Real.exp_le_one_iff.mpr
        (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) hp)), div_one, mul_comm]
    · rw [ite_eq_right hp, max_eq_right (Real.one_le_exp_iff.mpr
        (mul_nonneg (Nat.cast_nonneg _) (le_of_not_ge hp))), ← Real.exp_sub]
      ring_nf

end Scalar

section Normalizations

attribute [local instance] complexZeta_circleMeasurable complexZeta_circleBorel

private def realSpherePoint (b : Bool) : sphere (0 : ℝ) 1 :=
  ⟨if b then 1 else -1, by cases b <;> norm_num [Metric.mem_sphere, Real.dist_eq]⟩

private theorem realSpherePoint_surjective : Surjective realSpherePoint := by
  intro u
  have hu : |(u : ℝ)| = 1 := by
    have h : ‖(u : ℝ)‖ = 1 := mem_sphere_zero_iff_norm.mp u.property
    rwa [Real.norm_eq_abs] at h
  rcases eq_or_eq_neg_of_abs_eq hu with h | h
  · exact ⟨true, Subtype.ext h.symm⟩
  · exact ⟨false, Subtype.ext h.symm⟩

local instance : Finite (sphere (0 : ℝ) 1) := Finite.of_surjective _ realSpherePoint_surjective

private theorem realSphereCounting_isHaar :
    (Measure.count : Measure (sphere (0 : ℝ) 1)).IsHaarMeasure where
  lt_top_of_isCompact U hU := by
    rw [Measure.count_apply (isOpen_discrete U).measurableSet]
    exact_mod_cast hU.finite_of_discrete.encard_lt_top
  open_pos U hU hne := by
    rw [Measure.count_apply hU.measurableSet]
    exact_mod_cast hne.encard_pos.ne'

theorem complexTamagawaAngularMeasure_isHaar : complexTamagawaAngularMeasure.IsHaarMeasure :=
  Measure.isHaarMeasure_of_isCompact_nonempty_interior complexTamagawaAngularMeasure univ
    isCompact_univ (by simp) (by
      intro h
      have hm := complexTamagawaAngularMeasure_mass
      rw [measureReal_def, h] at hm
      have := Real.pi_pos
      norm_num at hm) (measure_lt_top _ _).ne

/-- The real Tamagawa normalization is Lebesgue measure in log-radius on
each of the two signs. -/
def realArchMultiplicativeHaar [MeasurableSpace ℝˣ] : Measure ℝˣ :=
  scalarLogPolarHaar (Measure.count : Measure (sphere (0 : ℝ) 1))

/-- The complex Tamagawa normalization in logarithmic polar coordinates. -/
def complexArchMultiplicativeHaar [MeasurableSpace ℂˣ] : Measure ℂˣ :=
  scalarLogPolarHaar complexTamagawaAngularMeasure

instance realArchMultiplicativeHaar_isHaar [MeasurableSpace ℝˣ] [BorelSpace ℝˣ] :
    realArchMultiplicativeHaar.IsHaarMeasure := by
  letI := realSphereCounting_isHaar
  exact scalarLogPolarHaar_isHaar _

instance complexArchMultiplicativeHaar_isHaar [MeasurableSpace ℂˣ] [BorelSpace ℂˣ] :
    complexArchMultiplicativeHaar.IsHaarMeasure := by
  exact @scalarLogPolarHaar_isHaar ℂ _ _ _ complexZeta_circleMeasurable complexZeta_circleBorel
    complexTamagawaAngularMeasure complexTamagawaAngularMeasure_isHaar

/-- The positive interval has the prescribed Tamagawa mass `log (b/a)`.
This gives the real-place normalization test from original commit
cce2418eff71568d2b7ee2f5e30624030f8fdda0 in the local logarithmic coordinates. -/
theorem realArchMultiplicativeHaar_Icc [MeasurableSpace ℝˣ] [BorelSpace ℝˣ]
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    realArchMultiplicativeHaar (Units.val ⁻¹' Icc a b) =
      ENNReal.ofReal (Real.log (b / a)) := by
  let e := realLogPolarCoordinates (K := ℝ)
  let S : Set (sphere (0 : ℝ) 1) := {realSpherePoint true}
  have he : e ⁻¹' (Units.val ⁻¹' Icc a b) = Icc (Real.log a) (Real.log b) ×ˢ S := by
    ext ⟨r, u⟩
    change ((e (r, u) : ℝˣ) : ℝ) ∈ Icc a b ↔
      (r, u) ∈ Icc (Real.log a) (Real.log b) ×ˢ S
    rw [realLogPolarCoordinates_val]
    obtain ⟨v, rfl⟩ := realSpherePoint_surjective u
    cases v
    · have hrs : Real.exp r * (realSpherePoint false : ℝ) < a := by
        change Real.exp r * (-1) < a
        linarith [Real.exp_pos r]
      have hne : realSpherePoint false ≠ realSpherePoint true := by
        intro h
        have := congrArg Subtype.val h
        norm_num [realSpherePoint] at this
      simp [S, hne, hrs.not_ge]
    · change Real.exp r * 1 ∈ Icc a b ↔ _
      rw [mul_one, Set.mem_prod, Set.mem_Icc, Set.mem_Icc]
      simp only [S, Set.mem_singleton_iff, and_true]
      rw [← Real.exp_le_exp (x := Real.log a) (y := r),
        ← Real.exp_le_exp (x := r) (y := Real.log b),
        Real.exp_log ha, Real.exp_log (ha.trans_le hab)]
  rw [realArchMultiplicativeHaar, scalarLogPolarHaar,
    Measure.map_apply e.continuous.measurable (Units.continuous_val.measurable measurableSet_Icc),
    he, Measure.prod_prod, Measure.count_singleton, mul_one, Real.volume_Icc]
  rw [Real.log_div (ha.trans_le hab).ne' ha.ne']

theorem realArchMultiplicativeHaar_integrable_majorant [MeasurableSpace ℝˣ] [BorelSpace ℝˣ]
    {b : ℝ} {m : ℕ} (hb : 0 < b) (hm : b < m) :
    Integrable (fun u : ℝˣ => ‖(u : ℝ)‖ ^ b / max 1 (‖(u : ℝ)‖ ^ m))
      realArchMultiplicativeHaar :=
  scalarLogPolarHaar_integrable_majorant Measure.count hb hm

theorem complexArchMultiplicativeHaar_integrable_majorant [MeasurableSpace ℂˣ] [BorelSpace ℂˣ]
    {b : ℝ} {m : ℕ} (hb : 0 < b) (hm : b < m) :
    Integrable (fun u : ℂˣ => ‖(u : ℂ)‖ ^ b / max 1 (‖(u : ℂ)‖ ^ m))
      complexArchMultiplicativeHaar :=
  @scalarLogPolarHaar_integrable_majorant ℂ _ _ _ complexZeta_circleMeasurable complexZeta_circleBorel
    complexTamagawaAngularMeasure complexTamagawaAngularMeasure_finite b m hb hm

/-- The complex local zeta continuation agrees with the normalized
multiplicative Haar integral on the actual unit group. -/
theorem complexArchimedeanZetaContinued_eq_unitIntegral
    [MeasurableSpace ℂˣ] [BorelSpace ℂˣ] (j : ℤ) (f : 𝓢(ℂ, ℂ)) {s : ℂ}
    (hs : 0 < s.re) :
    let g (u : ℂˣ) :=
      ((‖(u : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ s * ((u : ℂ) / (‖(u : ℂ)‖ : ℂ)) ^ j * f (u : ℂ)
    Integrable g complexArchMultiplicativeHaar ∧
      complexArchimedeanZetaContinued complexTamagawaAngularMeasure j f s =
        ∫ u, g u ∂complexArchMultiplicativeHaar := by
  dsimp only
  let g (u : ℂˣ) :=
    ((‖(u : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ s * ((u : ℂ) / (‖(u : ℂ)‖ : ℂ)) ^ j * f (u : ℂ)
  have hn : Continuous (fun u : ℂˣ => ‖(u : ℂ)‖ ^ 2) := Units.continuous_val.norm.pow 2
  have hn₀ (u : ℂˣ) : ‖(u : ℂ)‖ ≠ 0 := norm_ne_zero_iff.mpr u.ne_zero
  have hc : Continuous (fun u : ℂˣ => ((‖(u : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ s) := by
    apply continuous_iff_continuousAt.mpr
    intro u
    exact (Complex.continuousAt_ofReal_cpow_const (‖(u : ℂ)‖ ^ 2) s
      (Or.inr (pow_ne_zero 2 (hn₀ u)))).comp (f := fun u : ℂˣ => ‖(u : ℂ)‖ ^ 2) hn.continuousAt
  have hd : Continuous (fun u : ℂˣ => (u : ℂ) / (‖(u : ℂ)‖ : ℂ)) :=
    Units.continuous_val.div (Complex.continuous_ofReal.comp Units.continuous_val.norm)
      (fun u => Complex.ofReal_ne_zero.mpr (hn₀ u))
  have hd₀ (u : ℂˣ) : (u : ℂ) / (‖(u : ℂ)‖ : ℂ) ≠ 0 :=
    div_ne_zero u.ne_zero (Complex.ofReal_ne_zero.mpr (hn₀ u))
  have hg : Measurable g :=
    ((hc.mul (hd.zpow₀ j fun u => Or.inl (hd₀ u))).mul (f.continuous.comp Units.continuous_val)).measurable
  have h0 := complexArchimedeanZetaContinued_eq_polarIntegral complexTamagawaAngularMeasure j f hs
  have he (x : ℝ) (u : Circle) :
      g (realLogPolarCoordinates (x, u)) =
        Real.exp x • complexArchimedeanZetaPolarIntegrand j f s (Real.exp x, u) := by
    let r := Real.exp x
    have hr : 0 < r := Real.exp_pos _
    have hr₀ : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
    have hr_arg : (r : ℂ).arg = 0 := Complex.arg_ofReal_of_nonneg hr.le
    have hpow : ((r ^ 2 : ℝ) : ℂ) ^ s = (r : ℂ) ^ (2 * s) := by
      rw [Complex.ofReal_pow]
      have h := Complex.cpow_nat_mul' (n := 2) (x := (r : ℂ))
        (by rw [hr_arg, mul_zero]; exact neg_lt_zero.mpr Real.pi_pos)
        (by rw [hr_arg, mul_zero]; exact Real.pi_pos.le) s
      simpa only [Nat.cast_ofNat] using h.symm
    have hshift : (r : ℂ) ^ (2 * s) = (r : ℂ) * (r : ℂ) ^ (2 * s - 1) := by
      calc
        _ = (r : ℂ) ^ (1 + (2 * s - 1)) := by congr 1; ring
        _ = _ := by rw [Complex.cpow_add _ _ hr₀, Complex.cpow_one]
    have hp : ‖(r : ℂ) * (u : ℂ)‖ = r := by
      rw [norm_mul, Circle.norm_coe, mul_one, Complex.norm_real, Real.norm_of_nonneg hr.le]
    have hangle : (r : ℂ) * (u : ℂ) / (r : ℂ) = (u : ℂ) := by
      rw [mul_comm, mul_div_cancel_right₀ _ hr₀]
    dsimp only [g]
    rw [realLogPolarCoordinates_val]
    change ((‖(r : ℂ) * (u : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ s *
      ((r : ℂ) * (u : ℂ) / (‖(r : ℂ) * (u : ℂ)‖ : ℂ)) ^ j * f ((r : ℂ) * (u : ℂ)) =
      (r : ℂ) * ((r : ℂ) ^ (2 * s - 1) * ((u : ℂ) ^ j * f ((r : ℂ) * (u : ℂ))))
    rw [hp, hpow, hshift, hangle]
    ring
  obtain ⟨hi, hEq⟩ := @scalarLogPolarHaar_eq_polarIntegral ℂ _ _ _
    complexZeta_circleMeasurable complexZeta_circleBorel complexTamagawaAngularMeasure
    complexTamagawaAngularMeasure_finite g hg _ h0.1 he
  exact ⟨hi, h0.2.trans hEq.symm⟩

/-- The real local zeta continuation agrees with the normalized
multiplicative Haar integral on the real unit group. -/
theorem realArchimedeanZetaContinued_eq_unitIntegral [MeasurableSpace ℝˣ] [BorelSpace ℝˣ]
    (a : ℕ) (f : 𝓢(ℝ, ℂ)) {s : ℂ} (hs : 0 < s.re) :
    let g (u : ℝˣ) :=
      ((|(u : ℝ)| : ℝ) : ℂ) ^ s * (if (u : ℝ) < 0 then (-1 : ℂ) ^ a else 1) * f (u : ℝ)
    Integrable g realArchMultiplicativeHaar ∧ realArchimedeanZetaContinued a f s =
      ∫ u, g u ∂realArchMultiplicativeHaar := by
  dsimp only
  let g (u : ℝˣ) :=
    ((|(u : ℝ)| : ℝ) : ℂ) ^ s * (if (u : ℝ) < 0 then (-1 : ℂ) ^ a else 1) * f (u : ℝ)
  let A := sphere (0 : ℝ) 1
  let μ := (volume : Measure ℝ).restrict (Ioi 0)
  let H (p : ℝ × A) := realArchimedeanZetaIntegrand a f s (p.1 * (p.2 : ℝ))
  have hpos (u : ℝˣ) : 0 < |(u : ℝ)| := abs_pos.mpr u.ne_zero
  have hc : Continuous (fun u : ℝˣ => ((|(u : ℝ)| : ℝ) : ℂ) ^ s) := by
    apply continuous_iff_continuousAt.mpr
    intro u
    exact (Complex.continuousAt_ofReal_cpow_const |(u : ℝ)| s (Or.inr (hpos u).ne')).comp
      (f := fun u : ℝˣ => |(u : ℝ)|) Units.continuous_val.abs.continuousAt
  have hsmeas : Measurable (fun u : ℝˣ => if (u : ℝ) < 0 then (-1 : ℂ) ^ a else 1) :=
    measurable_const.ite (measurableSet_lt Units.continuous_val.measurable measurable_const) measurable_const
  have hg : Measurable g := (hc.measurable.mul hsmeas).mul (f.continuous.comp Units.continuous_val).measurable
  have hf : Integrable (realArchimedeanZetaIntegrand a f s) :=
    (realArchimedeanZetaContinued_eq_integral a f hs).1
  have hneg : Integrable (fun t : ℝ => realArchimedeanZetaIntegrand a f s (-t)) :=
    (Measure.measurePreserving_neg (volume : Measure ℝ)).integrable_comp_of_integrable hf
  have hθ (u : A) : (u : ℝ) = 1 ∨ (u : ℝ) = -1 := by
    obtain ⟨b, rfl⟩ := realSpherePoint_surjective u
    cases b <;> simp [realSpherePoint]
  have hH₀ (u : A) : Integrable (fun t => H (t, u)) μ := by
    rcases hθ u with hu | hu
    · have h : Integrable (realArchimedeanZetaIntegrand a f s) μ := hf.integrableOn
      simpa only [H, hu, mul_one] using h
    · have h : Integrable (fun t : ℝ => realArchimedeanZetaIntegrand a f s (-t)) μ := hneg.integrableOn
      simpa only [H, hu, mul_neg_one] using h
  have he (t : ℝ) (u : A) :
      g (realLogPolarCoordinates (t, u)) = Real.exp t • H (Real.exp t, u) := by
    let r := Real.exp t
    have hr : 0 < r := Real.exp_pos _
    have hnorm : |(u : ℝ)| = 1 := by rcases hθ u with h | h <;> simp [h]
    have hAbs : |r * (u : ℝ)| = r := by rw [abs_mul, abs_of_pos hr, hnorm, mul_one]
    have hpow : (r : ℂ) ^ s = (r : ℂ) * (r : ℂ) ^ (s - 1) := by
      calc
        _ = (r : ℂ) ^ (1 + (s - 1)) := by congr 1; ring
        _ = _ := by rw [Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hr.ne'), Complex.cpow_one]
    dsimp only [g]
    rw [realLogPolarCoordinates_val]
    change ((|r * (u : ℝ)| : ℝ) : ℂ) ^ s * (if r * (u : ℝ) < 0 then (-1 : ℂ) ^ a else 1) *
      f (r * (u : ℝ)) = (r : ℂ) *
      (((|r * (u : ℝ)| : ℝ) : ℂ) ^ (s - 1) * (if r * (u : ℝ) < 0 then (-1 : ℂ) ^ a else 1) * f (r * (u : ℝ)))
    rw [hAbs, hpow]
    ring
  let ν : Measure A := Measure.count
  have hp : ∀ᵐ p : ℝ × A ∂μ.prod ν, 0 < p.1 :=
    (Measure.ae_prod_iff_ae_ae (measurableSet_Ioi.preimage measurable_fst)).mpr
      ((ae_restrict_mem (μ := volume) measurableSet_Ioi).mono fun _ hx => .of_forall fun _ => hx)
  let J (p : ℝ × A) := (p.1 : ℂ)⁻¹ * g (realLogPolarCoordinates (Real.log p.1, p.2))
  have hJ : Measurable J :=
    ((Complex.continuous_ofReal.measurable.comp measurable_fst).inv).mul
      (hg.comp ((realLogPolarCoordinates (K := ℝ)).continuous.measurable.comp
        ((Real.measurable_log.comp measurable_fst).prodMk measurable_snd)))
  have hHm : AEStronglyMeasurable H (μ.prod ν) := by
    apply hJ.aestronglyMeasurable.congr
    filter_upwards [hp] with p hp
    have h := he (Real.log p.1) p.2
    rw [Real.exp_log hp, Complex.real_smul] at h
    change (p.1 : ℂ)⁻¹ * g (realLogPolarCoordinates (Real.log p.1, p.2)) = H p
    rw [h, ← mul_assoc, inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hp.ne'), one_mul]
  have hH : Integrable H (μ.prod ν) :=
    (integrable_prod_iff' hHm).mpr
      ⟨.of_forall hH₀, integrable_count_iff.mpr Summable.of_finite⟩
  obtain ⟨hi, hEq⟩ := scalarLogPolarHaar_eq_polarIntegral (Measure.count : Measure A) hg hH he
  refine ⟨hi, ?_⟩
  change realArchimedeanZetaContinued a f s = ∫ u, g u ∂scalarLogPolarHaar ν
  rw [(realArchimedeanZetaContinued_eq_integral a f hs).2, hEq,
    realArchimedeanZetaIntegral, integral_prod_symm _ hH]
  letI : Fintype A := Fintype.ofFinite _
  have hi : Injective realSpherePoint := by
    intro x y h
    have he' := congrArg (fun u : A => (u : ℝ)) h
    cases x <;> cases y <;> first | rfl | norm_num [realSpherePoint] at he'
  let e : Bool ≃ A := Equiv.ofBijective realSpherePoint ⟨hi, realSpherePoint_surjective⟩
  rw [integral_count, ← e.sum_comp (fun u : A => ∫ t, H (t, u) ∂μ), Fintype.sum_bool]
  change _ = (∫ t, realArchimedeanZetaIntegrand a f s (t * 1) ∂μ) +
    ∫ t, realArchimedeanZetaIntegrand a f s (t * (-1)) ∂μ
  simp only [mul_neg_one, mul_one]
  rw [← integral_add_compl measurableSet_Ioi hf, compl_Ioi, ← integral_comp_neg_Ioi 0
    (realArchimedeanZetaIntegrand a f s), neg_zero]

end Normalizations


section NumberField

open NumberField
open scoped Classical NumberField

variable (F : Type*) [Field F] [NumberField F]

local instance realArchUnitsMeasurable : MeasurableSpace ℝˣ := borel _
local instance realArchUnitsBorel : BorelSpace ℝˣ := ⟨rfl⟩
local instance complexArchUnitsMeasurable : MeasurableSpace ℂˣ := borel _
local instance complexArchUnitsBorel : BorelSpace ℂˣ := ⟨rfl⟩

local instance realArchUnitsSecondCountable : SecondCountableTopology ℝˣ := Units.isEmbedding_embedProduct.secondCountableTopology
local instance complexArchUnitsSecondCountable : SecondCountableTopology ℂˣ := Units.isEmbedding_embedProduct.secondCountableTopology
local instance realArchUnitsSigmaCompact : SigmaCompactSpace ℝˣ := Units.isClosedEmbedding_embedProduct.sigmaCompactSpace
local instance complexArchUnitsSigmaCompact : SigmaCompactSpace ℂˣ := Units.isClosedEmbedding_embedProduct.sigmaCompactSpace

local instance : MeasurableMul ℝˣ :=
  ⟨fun a => ((continuous_const (y := a)).mul continuous_id).measurable,
    fun a => (continuous_id.mul (continuous_const (y := a))).measurable⟩

local instance : MeasurableMul ℂˣ :=
  ⟨fun a => ((continuous_const (y := a)).mul continuous_id).measurable,
    fun a => (continuous_id.mul (continuous_const (y := a))).measurable⟩

private abbrev RealPlaces := {v : InfinitePlace F // v.IsReal}
private abbrev ComplexPlaces := {v : InfinitePlace F // v.IsComplex}

/-- The product of the one-place measures in real and complex unit coordinates. -/
def archimedeanCoordinateMeasure :
    Measure ((RealPlaces F → ℝˣ) × (ComplexPlaces F → ℂˣ)) :=
  (Measure.pi (fun _ : RealPlaces F => realArchMultiplicativeHaar)).prod
    (Measure.pi (fun _ : ComplexPlaces F => complexArchMultiplicativeHaar))

variable [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]

/-- Product of the normalized real and complex Haar measures, transported
to the actual group of archimedean ideles. -/
def archimedeanMultiplicativeHaar : Measure (InfiniteAdeleRing F)ˣ :=
  (archimedeanCoordinateMeasure F).map (infiniteAdeleUnitsCoordinates F).symm

instance archimedeanMultiplicativeHaar_isHaar : (archimedeanMultiplicativeHaar F).IsHaarMeasure := by
  unfold archimedeanMultiplicativeHaar
  letI : (archimedeanCoordinateMeasure F).IsHaarMeasure := by
    unfold archimedeanCoordinateMeasure
    infer_instance
  exact ContinuousMulEquiv.isHaarMeasure_map (μ := archimedeanCoordinateMeasure F)
    (infiniteAdeleUnitsCoordinates F).symm

instance archimedeanMultiplicativeHaar_sigmaFinite : SigmaFinite (archimedeanMultiplicativeHaar F) := by
  unfold archimedeanMultiplicativeHaar
  letI : SigmaFinite (archimedeanCoordinateMeasure F) := by
    unfold archimedeanCoordinateMeasure
    infer_instance
  exact (infiniteAdeleUnitsCoordinates F).symm.toHomeomorph.toMeasurableEquiv.sigmaFinite_map

theorem archimedeanMultiplicativeHaar_integral (g : (InfiniteAdeleRing F)ˣ → ℂ) :
    (∫ a, g a ∂archimedeanMultiplicativeHaar F) =
      ∫ p, g ((infiniteAdeleUnitsCoordinates F).symm p) ∂archimedeanCoordinateMeasure F :=
  integral_map_equiv (infiniteAdeleUnitsCoordinates F).symm.toHomeomorph.toMeasurableEquiv g

theorem archimedeanMultiplicativeHaar_integrable_iff (g : (InfiniteAdeleRing F)ˣ → ℂ) :
    Integrable g (archimedeanMultiplicativeHaar F) ↔
      Integrable (fun p => g ((infiniteAdeleUnitsCoordinates F).symm p))
        (archimedeanCoordinateMeasure F) :=
  integrable_map_equiv (infiniteAdeleUnitsCoordinates F).symm.toHomeomorph.toMeasurableEquiv g

end NumberField


end

end Masullo
