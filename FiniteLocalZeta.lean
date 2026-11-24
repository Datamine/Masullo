import WeilPrincipalValue
import AdelicTamagawaProduct
import FinestReflexivity
import LocalMultiplicativeHaar
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Meromorphic.TrailingCoefficient
import Mathlib.Analysis.Analytic.Uniqueness

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical NumberField ENNReal Topology WithZero

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]
variable (v : HeightOneSpectrum (𝓞 F))

private abbrev K := v.adicCompletion F

/-- The shell of a given integral exponent of the maximal ideal. -/
def finiteZetaShell (n : ℤ) : Set (K F v)ˣ :=
  {u | ‖u.val‖ = (v.asIdeal.absNorm : ℝ) ^ (-n)}

theorem finiteZetaShell_zero : finiteZetaShell F v 0 = finitePlaceIntegralUnits F v := by
  ext u
  change ‖u.val‖ = (v.asIdeal.absNorm : ℝ) ^ (-(0 : ℤ)) ↔
    u ∈ (v.adicCompletionIntegers F).toSubmonoid.units
  rw [neg_zero, zpow_zero, finiteCompletion_norm_eq_one_iff F,
    HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one]

theorem finiteZetaShell_closed (n : ℤ) : IsClosed (finiteZetaShell F v n) :=
  isClosed_eq (continuous_norm.comp Units.continuous_val) continuous_const

theorem finiteZetaShell_disjoint :
    Pairwise (Disjoint on finiteZetaShell F v) := by
  have hq : 1 < (v.asIdeal.absNorm : ℝ) := by
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  intro i j hij
  change Disjoint (finiteZetaShell F v i) (finiteZetaShell F v j)
  rw [Set.disjoint_left]
  intro u hi hj
  change ‖u.val‖ = (v.asIdeal.absNorm : ℝ) ^ (-i) at hi
  change ‖u.val‖ = (v.asIdeal.absNorm : ℝ) ^ (-j) at hj
  exact hij (neg_injective ((zpow_right_injective₀ (zero_lt_one.trans hq) hq.ne')
    (hi.symm.trans hj)))

theorem finiteZetaShell_iUnion : ⋃ n : ℤ, finiteZetaShell F v n = univ := by
  apply iUnion_eq_univ_iff.mpr
  intro u
  have hu : (Valued.v : Valuation (K F v) ℤᵐ⁰) u.val ≠ 0 :=
    Valuation.ne_zero_iff _ |>.mpr u.ne_zero
  refine ⟨-(WithZero.unzero hu).toAdd, ?_⟩
  change ‖u.val‖ = (v.asIdeal.absNorm : ℝ) ^ (-(-(WithZero.unzero hu).toAdd))
  rw [neg_neg, FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _ hu]
  exact NNReal.coe_zpow _ _

/-- Multiplication by a uniformizer power carries the unit shell to the
corresponding valuation shell. -/
theorem finiteZetaShell_preimage (π : (K F v)ˣ) (hπ : Valued.v.IsUniformizer π.val) (n : ℤ) :
    (fun u : (K F v)ˣ => π ^ n * u) ⁻¹' finiteZetaShell F v n = finitePlaceIntegralUnits F v := by
  rw [← finiteZetaShell_zero F v]
  ext u
  have hq : 0 < (v.asIdeal.absNorm : ℝ) := by
    exact_mod_cast (zero_lt_one.trans (NumberField.HeightOneSpectrum.one_lt_absNorm v))
  change ‖(π ^ n * u).val‖ = (v.asIdeal.absNorm : ℝ) ^ (-n) ↔
    ‖u.val‖ = (v.asIdeal.absNorm : ℝ) ^ (-(0 : ℤ))
  rw [Units.val_mul, Units.val_zpow_eq_zpow_val, norm_mul, norm_zpow,
    norm_finiteUniformizer F v π.val hπ, inv_zpow, ← zpow_neg, neg_zero, zpow_zero]
  conv_lhs => rhs; rw [← mul_one ((v.asIdeal.absNorm : ℝ) ^ (-n))]
  exact ⟨mul_left_cancel₀ (zpow_ne_zero _ hq.ne'), fun h => congrArg (_ * ·) h⟩

variable [MeasurableSpace (K F v)ˣ] [BorelSpace (K F v)ˣ]

/-- The multiplicative Haar mass of every shell is the mass of the unit group. -/
theorem finiteZetaShell_mass (μ : Measure (K F v)ˣ) [μ.IsMulLeftInvariant] (n : ℤ) :
    μ (finiteZetaShell F v n) = μ (finitePlaceIntegralUnits F v) := by
  let π := chosenFiniteUniformizer F v
  rw [← finiteZetaShell_preimage F v π (chosenFiniteUniformizer_spec F v) n,
    measure_preimage_mul μ]


/-- The spectral power of the normalized finite-place absolute value. -/
def finiteZetaWeight (z : ℂ) (u : (K F v)ˣ) : ℂ :=
  Complex.exp (z * (Real.log ‖u.val‖ : ℂ))

/-- The zeta integral of the unit-ball test under the unramified norm
twist. Each shell in the ball contributes its common Haar mass. -/
theorem finiteZeta_unitBall_integral (μ : Measure (K F v)ˣ) [μ.IsHaarMeasure]
    (z : ℂ) (hz : 0 < z.re) :
    let U : Set (K F v)ˣ := {u | ‖u.val‖ ≤ 1}
    IntegrableOn (finiteZetaWeight F v z) U μ ∧
      (∫ u in U, finiteZetaWeight F v z u ∂μ) =
        (μ.real (finitePlaceIntegralUnits F v) : ℂ) *
          (1 - Complex.exp (-z * (Real.log (v.asIdeal.absNorm : ℝ) : ℂ)))⁻¹ := by
  classical
  let q : ℝ := v.asIdeal.absNorm
  let r := Complex.exp (-z * (Real.log q : ℂ))
  let C := μ.real (finitePlaceIntegralUnits F v)
  let U : Set (K F v)ˣ := {u | ‖u.val‖ ≤ 1}
  let A (n : ℕ) := finiteZetaShell F v (n : ℤ)
  let w := finiteZetaWeight F v z
  have hq : 1 < q := by
    dsimp [q]
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hU : (⋃ n, A n) = U := by
    ext u
    rw [mem_iUnion]
    constructor
    · rintro ⟨n, hn⟩
      change ‖u.val‖ = q ^ (-(n : ℤ)) at hn
      change ‖u.val‖ ≤ 1
      rw [hn, zpow_le_one_iff_right₀ hq]
      simp
    · intro hu
      obtain ⟨n, hn⟩ := iUnion_eq_univ_iff.mp (finiteZetaShell_iUnion F v) u
      change ‖u.val‖ = q ^ (-n) at hn
      change ‖u.val‖ ≤ 1 at hu
      rw [hn, zpow_le_one_iff_right₀ hq, neg_nonpos] at hu
      refine ⟨n.toNat, ?_⟩
      change ‖u.val‖ = q ^ (-(n.toNat : ℤ))
      rw [Int.toNat_of_nonneg hu]
      exact hn
  have hmass (n : ℕ) : μ (A n) ≠ ∞ := by
    rw [show μ (A n) = μ (finitePlaceIntegralUnits F v) from finiteZetaShell_mass F v μ n]
    exact (Submonoid.units_isCompact (S := (v.adicCompletionIntegers F).toSubmonoid)
      (finitePlaceIntegral_compact F v)).measure_lt_top.ne
  have hmeas (n : ℕ) : MeasurableSet (A n) := (finiteZetaShell_closed F v n).measurableSet
  have hdisj : Pairwise (Disjoint on A) :=
    (finiteZetaShell_disjoint F v).comp_of_injective Nat.cast_injective
  have he (n : ℕ) (u : (K F v)ˣ) (hu : u ∈ A n) : w u = r ^ n := by
    change ‖u.val‖ = q ^ (-(n : ℤ)) at hu
    unfold w finiteZetaWeight r
    rw [hu, Real.log_zpow, ← Complex.exp_nat_mul]
    push_cast
    congr 1
    ring
  have hr : ‖r‖ < 1 := by
    change ‖Complex.exp (-z * (Real.log q : ℂ))‖ < 1
    rw [Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero, Complex.neg_re, ← Real.exp_zero, Real.exp_lt_exp]
    exact mul_neg_of_neg_of_pos (neg_lt_zero.mpr hz) (Real.log_pos hq)
  have hw (n : ℕ) : IntegrableOn w (A n) μ :=
    (integrableOn_const (C := r ^ n) (hmass n)).congr_fun (fun u hu => (he n u hu).symm) (hmeas n)
  have hnorm (n : ℕ) : (∫ u in A n, ‖w u‖ ∂μ) = C * ‖r‖ ^ n := by
    rw [setIntegral_congr_fun (hmeas n) (g := fun _ => ‖r ^ n‖)
        (fun u hu => congrArg norm (he n u hu)), setIntegral_const, norm_pow]
    simp only [Measure.real, smul_eq_mul, C, A, finiteZetaShell_mass F v μ]
  have hsum := (summable_geometric_of_lt_one (norm_nonneg r) hr).mul_left C
  have hi := integrableOn_iUnion_of_summable_integral_norm hw (hsum.congr fun n => (hnorm n).symm)
  have hterm (n : ℕ) : (∫ u in A n, w u ∂μ) = (C : ℂ) * r ^ n := by
    rw [setIntegral_congr_fun (hmeas n) (g := fun _ => r ^ n) (he n), setIntegral_const]
    simp only [Measure.real, Complex.real_smul, C, A, finiteZetaShell_mass F v μ]
  change IntegrableOn w U μ ∧ (∫ u in U, w u ∂μ) = (C : ℂ) * (1 - r)⁻¹
  rw [← hU]
  refine ⟨hi, ?_⟩
  rw [integral_iUnion hmeas hdisj hi]
  simp_rw [hterm, tsum_mul_left, tsum_geometric_of_norm_lt_one hr]


omit [BorelSpace (K F v)ˣ] in
/-- The residue of the continued unit-ball formula at the trivial character. -/
theorem finiteZeta_unitBall_residue (μ : Measure (K F v)ˣ) :
    let m : ℂ := μ.real (finitePlaceIntegralUnits F v)
    let d : ℂ := Real.log (v.asIdeal.absNorm : ℝ)
    Tendsto (fun z => z * (m * (1 - Complex.exp (-z * d))⁻¹)) (𝓝[≠] (0 : ℂ)) (𝓝 (m / d)) := by
  let m : ℂ := μ.real (finitePlaceIntegralUnits F v)
  let d : ℂ := Real.log (v.asIdeal.absNorm : ℝ)
  let den (z : ℂ) := 1 - Complex.exp (-z * d)
  have hq : 1 < (v.asIdeal.absNorm : ℝ) := by
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hdne : d ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.log_pos hq).ne'
  have hd : HasDerivAt den d 0 := by
    simpa [den] using (((hasDerivAt_id (0 : ℂ)).neg.mul_const d).cexp.const_sub (1 : ℂ))
  have hs : Tendsto (fun z => den z / z) (𝓝[≠] (0 : ℂ)) (𝓝 d) := by
    simpa [den, slope_fun_def_field, div_eq_mul_inv, mul_comm] using hd.tendsto_slope
  change Tendsto (fun z => z * (m * (den z)⁻¹)) _ (𝓝 (m / d))
  rw [div_eq_mul_inv]
  refine ((hs.inv₀ hdne).const_mul m).congr' (Eventually.of_forall fun z => ?_)
  rw [inv_div, div_eq_mul_inv]
  ring

omit [BorelSpace (K F v)ˣ] in
/-- With the unit mass of Definition A.3.2.2, the additional factor
`1 - q⁻¹` printed in (3.3.2.23) changes the unit-ball residue. -/
theorem finiteZeta_unitBall_residue_discrepancy (μ : Measure (K F v)ˣ) [μ.IsHaarMeasure] :
    let m := μ.real (finitePlaceIntegralUnits F v)
    let q : ℝ := v.asIdeal.absNorm
    m / Real.log q ≠ m * (1 - q⁻¹) / Real.log q := by
  let U := finitePlaceIntegralUnits F v
  let q : ℝ := v.asIdeal.absNorm
  have hq : 1 < q := by
    dsimp [q]
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hU : IsOpen U := by
    have hO := Valued.isOpen_valuationSubring (K F v)
    exact (hO.preimage Units.continuous_val).inter
      (hO.preimage (Units.continuous_val.comp continuous_inv))
  have hne : μ U ≠ 0 := hU.measure_ne_zero μ ⟨1, one_mem _⟩
  have hfinite : μ U ≠ ∞ :=
    (Submonoid.units_isCompact (S := (v.adicCompletionIntegers F).toSubmonoid)
      (finitePlaceIntegral_compact F v)).measure_lt_top.ne
  have hm : 0 < μ.real U := ENNReal.toReal_pos hne hfinite
  change μ.real U / Real.log q ≠ μ.real U * (1 - q⁻¹) / Real.log q
  apply ne_of_gt
  apply div_lt_div_of_pos_right _ (Real.log_pos hq)
  calc
    _ < μ.real U * 1 := mul_lt_mul_of_pos_left
      (sub_lt_self 1 (inv_pos.mpr (zero_lt_one.trans hq))) hm
    _ = _ := mul_one _


private abbrev U := finitePlaceIntegralUnits F v

omit [MeasurableSpace (K F v)ˣ] [BorelSpace (K F v)ˣ] in
private theorem finiteZetaShell_compact (n : ℤ) : IsCompact (finiteZetaShell F v n) := by
  let π := chosenFiniteUniformizer F v
  let e : (K F v)ˣ ≃ₜ (K F v)ˣ := Homeomorph.mulLeft (π ^ n)
  have he : e ⁻¹' finiteZetaShell F v n = U F v :=
    finiteZetaShell_preimage F v π (chosenFiniteUniformizer_spec F v) n
  have hU : IsCompact (U F v) :=
    Submonoid.units_isCompact (S := (v.adicCompletionIntegers F).toSubmonoid)
      (finitePlaceIntegral_compact F v)
  rw [← he] at hU
  simpa only [e.image_preimage] using hU.image e.continuous

omit [MeasurableSpace (K F v)ˣ] [BorelSpace (K F v)ˣ] in
/-- Compact support bounds the shells from below. Local constancy at zero
makes the test constant on every sufficiently deep shell. -/
theorem finiteZetaShell_test_bounds (f : locallyConstantTests (K F v)) :
    ∃ L : ℤ, ∃ N : ℕ, L ≤ N ∧
      ∀ n (u : (K F v)ˣ), u ∈ finiteZetaShell F v n →
        (n < L → f.val u.val = 0) ∧ ((N : ℤ) ≤ n → f.val u.val = f.val 0) := by
  let q : ℝ := v.asIdeal.absNorm
  have hq : 1 < q := by
    dsimp [q]
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  obtain ⟨R, hR⟩ := f.property.2.exists_bound_of_continuousOn continuous_id.continuousOn
  obtain ⟨M, hM⟩ := pow_unbounded_of_one_lt R hq
  obtain ⟨ε, hε, hnear⟩ := Metric.mem_nhds_iff.mp (f.property.1.eventually_eq 0)
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt ε⁻¹ hq
  refine ⟨-(M : ℤ), N, by omega, fun n u hu => ⟨fun hn => ?_, fun hn => ?_⟩⟩
  change ‖u.val‖ = q ^ (-n) at hu
  · by_contra hf
    have hle := hR u.val (subset_tsupport _ hf)
    change ‖u.val‖ ≤ R at hle
    rw [hu] at hle
    have hlt : q ^ (M : ℤ) < q ^ (-n) := (zpow_right_strictMono₀ hq) (by omega)
    rw [zpow_natCast] at hlt
    exact (hM.trans hlt).not_ge hle
  · apply hnear
    rw [Metric.mem_ball, dist_zero_right, hu]
    calc
      _ ≤ q ^ (-(N : ℤ)) := (zpow_right_mono₀ hq.le) (neg_le_neg hn)
      _ = (q ^ N)⁻¹ := by rw [zpow_neg, zpow_natCast]
      _ < ε := by
        have h := inv_lt_inv₀ (pow_pos (zero_lt_one.trans hq) N) (inv_pos.mpr hε)
        simpa only [inv_inv] using h.mpr hN

private abbrev LocalPhase := (K F v)ˣ →ₜ* Circle

/-- The local zeta integral for a unitary character twisted by the modulus. -/
def finiteZetaIntegral (μ : Measure (K F v)ˣ) (χ : LocalPhase F v)
    (f : locallyConstantTests (K F v)) (z : ℂ) : ℂ :=
  ∫ u, f.val u.val * (χ u : ℂ) * finiteZetaWeight F v z u ∂μ

/-- The value of the twisted character at the chosen uniformizer. -/
def finiteZetaRatio (χ : LocalPhase F v) (z : ℂ) : ℂ :=
  (χ (chosenFiniteUniformizer F v) : ℂ) *
    Complex.exp (-z * (Real.log (v.asIdeal.absNorm : ℝ) : ℂ))

private def finiteZetaCoeff (μ : Measure (K F v)ˣ) (χ : LocalPhase F v)
    (f : locallyConstantTests (K F v)) (n : ℤ) : ℂ :=
  ∫ u in U F v, f.val ((chosenFiniteUniformizer F v ^ n * u).val) * (χ u : ℂ) ∂μ

private def finiteZetaUnitAverage (μ : Measure (K F v)ˣ) (χ : LocalPhase F v) : ℂ :=
  ∫ u in U F v, (χ u : ℂ) ∂μ

omit [MeasurableSpace (K F v)ˣ] [BorelSpace (K F v)ˣ] in
private theorem finiteZetaWeight_onShell (z : ℂ) (n : ℤ) (u : (K F v)ˣ)
    (hu : u ∈ finiteZetaShell F v n) :
    finiteZetaWeight F v z u = Complex.exp (-z * (Real.log (v.asIdeal.absNorm : ℝ) : ℂ)) ^ n := by
  change ‖u.val‖ = (v.asIdeal.absNorm : ℝ) ^ (-n) at hu
  rw [finiteZetaWeight, hu, Real.log_zpow, ← Complex.exp_int_mul]
  push_cast
  congr 1
  ring

omit [MeasurableSpace (K F v)ˣ] [BorelSpace (K F v)ˣ] in
private theorem finiteZetaRatio_norm_lt_one (χ : LocalPhase F v) (z : ℂ) (hz : 0 < z.re) :
    ‖finiteZetaRatio F v χ z‖ < 1 := by
  have hq : 1 < (v.asIdeal.absNorm : ℝ) := by
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  rw [finiteZetaRatio, norm_mul, Circle.norm_coe, one_mul, Complex.norm_exp,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
    Complex.neg_re, ← Real.exp_zero, Real.exp_lt_exp]
  exact mul_neg_of_neg_of_pos (neg_lt_zero.mpr hz) (Real.log_pos hq)

/-- In the unramified case, the modified integer-ring integral in Theorem
3.4.1.1 has the mass of the integral units for every complex parameter. -/
theorem finiteZetaIntegral_principalValue_integerRing
    (μ : Measure (K F v)ˣ) (χ : LocalPhase F v)
    (hχ : ∀ u ∈ finitePlaceIntegralUnits F v, χ u = 1)
    (π : (K F v)ˣ) (hπ : Valued.v.IsUniformizer π.val) (z : ℂ) :
    finiteZetaIntegral F v μ χ
        (finitePrincipalValue π (finiteCompletionIntegerRingTest F v)) z =
      (μ.real (finitePlaceIntegralUnits F v) : ℂ) := by
  have hU (u : (K F v)ˣ) : u ∈ finitePlaceIntegralUnits F v ↔ ‖u.val‖ = 1 := by
    rw [← finiteZetaShell_zero F v]
    change ‖u.val‖ = (v.asIdeal.absNorm : ℝ) ^ (-(0 : ℤ)) ↔ _
    simp
  unfold finiteZetaIntegral
  have hfun : (fun u : (K F v)ˣ =>
      (finitePrincipalValue π (finiteCompletionIntegerRingTest F v)).val u.val *
        (χ u : ℂ) * finiteZetaWeight F v z u) =
        (finitePlaceIntegralUnits F v).indicator (fun _ => 1) := by
    funext u
    rw [finitePrincipalValue_integerRing_apply F v π hπ]
    by_cases hu : u ∈ finitePlaceIntegralUnits F v
    · have hs : u ∈ finiteZetaShell F v 0 := (finiteZetaShell_zero F v).symm ▸ hu
      simp [(hU u).mp hu, hχ u hu, finiteZetaWeight_onShell F v z 0 u hs, indicator_of_mem hu]
    · simp [(hU u).not.mp hu, indicator_of_notMem hu]
  rw [hfun, integral_indicator_const]
  · simp [Complex.real_smul]
  · rw [← finiteZetaShell_zero F v]
    exact (finiteZetaShell_closed F v 0).measurableSet


omit [MeasurableSpace (K F v)ˣ] [BorelSpace (K F v)ˣ] in
/-- The unramified integer-ring factors in Theorem 3.4.1.1 multiply to the
reciprocal square root of the discriminant when the Haar measures have the
local masses defined by the global different. The product reduction follows
mccorvie/riemann-masullo, commit fa05ac0 (Apache-2.0). -/
theorem finiteZetaIntegral_principalValue_integerRing_tprod
    [∀ w : HeightOneSpectrum (𝓞 F), MeasurableSpace (K F w)ˣ]
    [∀ w : HeightOneSpectrum (𝓞 F), BorelSpace (K F w)ˣ]
    (μ : ∀ w : HeightOneSpectrum (𝓞 F), Measure (K F w)ˣ)
    (hμ : ∀ w, μ w (finitePlaceIntegralUnits F w) = differentPrimeMass F w)
    (χ : ∀ w : HeightOneSpectrum (𝓞 F), LocalPhase F w)
    (hχ : ∀ w u, u ∈ finitePlaceIntegralUnits F w → χ w u = 1)
    (π : ∀ w : HeightOneSpectrum (𝓞 F), (K F w)ˣ)
    (hπ : ∀ w, Valued.v.IsUniformizer (π w).val) (z : ℂ) :
    (∏' w : HeightOneSpectrum (𝓞 F), finiteZetaIntegral F w (μ w) (χ w)
      (finitePrincipalValue (π w) (finiteCompletionIntegerRingTest F w)) z) =
      ((↑(NNReal.sqrt ‖discr F‖₊) : ℂ))⁻¹ := by
  let toComplex : ℝ≥0∞ →* ℂ :=
    Complex.ofRealHom.toMonoidHom.comp ENNReal.toRealHom.toMonoidHom
  have hf (w : HeightOneSpectrum (𝓞 F)) :
      finiteZetaIntegral F w (μ w) (χ w)
        (finitePrincipalValue (π w) (finiteCompletionIntegerRingTest F w)) z =
        toComplex (differentPrimeMass F w) := by
    rw [finiteZetaIntegral_principalValue_integerRing F w (μ w) (χ w) (hχ w) (π w) (hπ w),
      measureReal_def, hμ w]
    rfl
  rw [tprod_congr hf, tprod_eq_finprod, ← map_finprod toComplex (differentPrimeMass_finite F),
    differentPrimeMass_finprod]
  · change ((((↑(NNReal.sqrt ‖discr F‖₊) : ℝ≥0∞)⁻¹).toReal : ℝ) : ℂ) = _
    simp only [ENNReal.toReal_inv, ENNReal.coe_toReal, Complex.ofReal_inv]
  · exact (differentPrimeMass_finite F).subset fun w hw h ↦
      hw (show toComplex (differentPrimeMass F w) = 1 by rw [h, map_one])

private theorem finiteZeta_setIntegral_shell (μ : Measure (K F v)ˣ) [μ.IsHaarMeasure]
    (χ : LocalPhase F v) (f : locallyConstantTests (K F v)) (z : ℂ) (n : ℤ) :
    (∫ u in finiteZetaShell F v n, f.val u.val * (χ u : ℂ) * finiteZetaWeight F v z u ∂μ) =
      finiteZetaCoeff F v μ χ f n * finiteZetaRatio F v χ z ^ n := by
  let π := chosenFiniteUniformizer F v
  let e := MeasurableEquiv.mulLeft (π ^ n)
  let g (u : (K F v)ˣ) := f.val u.val * (χ u : ℂ) * finiteZetaWeight F v z u
  change (∫ u in finiteZetaShell F v n, g u ∂μ) = _
  rw [← (measurePreserving_mul_left μ (π ^ n)).setIntegral_preimage_emb
    e.measurableEmbedding g, finiteZetaShell_preimage F v π (chosenFiniteUniformizer_spec F v)]
  unfold finiteZetaCoeff
  rw [← integral_mul_const]
  apply setIntegral_congr_fun (finiteZetaShell_zero F v ▸ (finiteZetaShell_closed F v 0).measurableSet)
  intro u hu
  have hm : π ^ n * u ∈ finiteZetaShell F v n := by
    change u ∈ (fun a : (K F v)ˣ => π ^ n * a) ⁻¹' finiteZetaShell F v n
    rw [finiteZetaShell_preimage F v π (chosenFiniteUniformizer_spec F v)]
    exact hu
  change f.val (π ^ n * u).val * ((χ (π ^ n * u) : Circle) : ℂ) *
      finiteZetaWeight F v z (π ^ n * u) = _
  rw [finiteZetaWeight_onShell F v z n _ hm]
  change _ = f.val (π ^ n * u).val * ((χ u : Circle) : ℂ) * (finiteZetaRatio F v χ z) ^ n
  simp only [finiteZetaRatio, map_mul, map_zpow, Circle.coe_mul, Circle.coe_zpow, mul_zpow]
  change _ = f.val (π ^ n * u).val * ((χ u : Circle) : ℂ) *
    (((χ π : Circle) : ℂ) ^ n *
      Complex.exp (-z * (Real.log (v.asIdeal.absNorm : ℝ) : ℂ)) ^ n)
  ring

private def finiteZetaExpansion (μ : Measure (K F v)ˣ) (χ : LocalPhase F v)
    (f : locallyConstantTests (K F v)) (L : ℤ) (N : ℕ) (z : ℂ) : ℂ :=
  let r := finiteZetaRatio F v χ z
  (∑ n ∈ Finset.Ico L (N : ℤ), finiteZetaCoeff F v μ χ f n * r ^ n) +
    f.val 0 * finiteZetaUnitAverage F v μ χ * r ^ N * (1 - r)⁻¹

/-- The local integral is a finite sum over shells and a geometric tail
determined by the value of the test at zero and the unit average. -/
theorem finiteZeta_integral_expansion (μ : Measure (K F v)ˣ) [μ.IsHaarMeasure]
    (χ : LocalPhase F v) (f : locallyConstantTests (K F v))
    (L : ℤ) (N : ℕ)
    (hb : ∀ n (u : (K F v)ˣ), u ∈ finiteZetaShell F v n →
      (n < L → f.val u.val = 0) ∧ ((N : ℤ) ≤ n → f.val u.val = f.val 0))
    (z : ℂ) (hz : 0 < z.re) :
    Integrable (fun u : (K F v)ˣ => f.val u.val * (χ u : ℂ) * finiteZetaWeight F v z u) μ ∧
      finiteZetaIntegral F v μ χ f z = finiteZetaExpansion F v μ χ f L N z := by
  classical
  let I := Finset.Ico L (N : ℤ)
  let A (n : ℤ) := finiteZetaShell F v n
  let B := ⋃ n : I, A n.val
  let T := ⋃ k : ℕ, A ((N : ℤ) + k)
  let r := finiteZetaRatio F v χ z
  let g (u : (K F v)ˣ) := f.val u.val * (χ u : ℂ) * finiteZetaWeight F v z u
  have hmeas (n : ℤ) : MeasurableSet (A n) := (finiteZetaShell_closed F v n).measurableSet
  have hd := finiteZetaShell_disjoint F v
  have hsep (n m : ℤ) (hnm : n ≠ m) : Disjoint (A n) (A m) := hd hnm
  have hir (u : (K F v)ˣ) : 0 < ‖(u : K F v)‖ := norm_pos_iff.mpr u.ne_zero
  have hlog : Continuous (fun u : (K F v)ˣ => Real.log ‖(u : K F v)‖) :=
    (continuous_norm.comp Units.continuous_val).log (fun u => (hir u).ne')
  have hw : Continuous (finiteZetaWeight F v z) :=
    (continuous_const.mul (Complex.continuous_ofReal.comp hlog)).cexp
  have hg : Continuous g :=
    ((f.property.1.continuous.comp Units.continuous_val).mul
      (continuous_subtype_val.comp χ.continuous)).mul hw
  have hi (n) : IntegrableOn g (A n) μ :=
    hg.continuousOn.integrableOn_compact (finiteZetaShell_compact F v n)
  have hB : IntegrableOn g B μ :=
    integrableOn_iUnion_of_summable_integral_norm (fun n : I => hi n.val) Summable.of_finite
  have hBmeas : MeasurableSet B := MeasurableSet.iUnion (fun n : I => hmeas n.val)
  have hTmeas : MeasurableSet T := MeasurableSet.iUnion (fun k : ℕ => hmeas ((N : ℤ) + k))
  have hDT : Pairwise (Disjoint on fun k : ℕ => A ((N : ℤ) + k)) := by
    intro j k h
    exact hsep _ _ (by omega)
  have hDB : Pairwise (Disjoint on fun n : I => A n.val) := by
    intro i j hij
    exact hsep _ _ (fun he => hij (Subtype.ext he))
  have hBT : Disjoint B T := by
    rw [Set.disjoint_left]
    intro u hu ht
    obtain ⟨n, hn⟩ := mem_iUnion.mp hu
    obtain ⟨k, hk⟩ := mem_iUnion.mp ht
    have hN := (Finset.mem_Ico.mp n.property).2
    exact (Set.disjoint_left.mp (hsep _ _ (by omega))) hn hk
  have hzero : EqOn g (fun _ => 0) (B ∪ T)ᶜ := by
    intro u hu
    obtain ⟨n, hn⟩ := iUnion_eq_univ_iff.mp (finiteZetaShell_iUnion F v) u
    have hlt : n < L := by
      by_contra! hL
      by_cases hN : n < (N : ℤ)
      · exact hu (Or.inl (mem_iUnion.mpr ⟨⟨n, Finset.mem_Ico.mpr ⟨hL, hN⟩⟩, hn⟩))
      · have hEq : (N : ℤ) + ((n - N).toNat : ℤ) = n := by omega
        exact hu (Or.inr (mem_iUnion.mpr ⟨_, hEq.symm ▸ hn⟩))
    simp only [g, (hb n u hn).1 hlt, zero_mul]
  have htailnorm (k : ℕ) (u : (K F v)ˣ) (hu : u ∈ A ((N : ℤ) + k)) :
      ‖g u‖ = ‖f.val 0‖ * ‖r‖ ^ (N+k) := by
    have hn : (N : ℤ) ≤ (N : ℤ) + k := by omega
    rw [show g u = f.val u.val * (χ u : ℂ) * finiteZetaWeight F v z u from rfl,
      (hb _ u hu).2 hn, norm_mul, norm_mul, Circle.norm_coe, mul_one,
      finiteZetaWeight_onShell F v z _ u hu, norm_zpow, ← Nat.cast_add, zpow_natCast]
    simp [r, finiteZetaRatio, Circle.norm_coe]
  let m := μ.real (U F v)
  have htailintegralnorm (k : ℕ) :
      (∫ u in A ((N : ℤ) + k), ‖g u‖ ∂μ) = (m * ‖f.val 0‖ * ‖r‖ ^ N) * ‖r‖ ^ k := by
    rw [setIntegral_congr_fun (hmeas _) (g := fun _ => ‖f.val 0‖ * ‖r‖ ^ (N+k))
        (htailnorm k), setIntegral_const, pow_add, smul_eq_mul]
    simp only [m, Measure.real, A, finiteZetaShell_mass F v μ]
    ring
  have hr : ‖r‖ < 1 := finiteZetaRatio_norm_lt_one F v χ z hz
  have hsum := (summable_geometric_of_lt_one (norm_nonneg r) hr).mul_left
    (m * ‖f.val 0‖ * ‖r‖ ^ N)
  have hT : IntegrableOn g T μ := integrableOn_iUnion_of_summable_integral_norm
    (fun k => hi ((N : ℤ) + k)) (hsum.congr fun k => (htailintegralnorm k).symm)
  have hm := hBmeas.union hTmeas
  have hout : IntegrableOn g (B ∪ T)ᶜ μ :=
    integrableOn_zero.congr_fun hzero.symm hm.compl
  have hint : Integrable g μ := by
    simpa only [union_compl_self, integrableOn_univ] using (hB.union hT).union hout
  refine ⟨hint, ?_⟩
  have hmain := integral_add_compl hm hint
  have houtzero : (∫ u in (B ∪ T)ᶜ, g u ∂μ) = 0 := by
    rw [setIntegral_congr_fun hm.compl hzero, integral_zero]
  rw [houtzero, add_zero, setIntegral_union hBT hTmeas hB hT] at hmain
  have hmid : (∫ u in B, g u ∂μ) = ∑ n ∈ I, finiteZetaCoeff F v μ χ f n * r ^ n := by
    rw [integral_iUnion_fintype (fun (n : I) => hmeas n.val) hDB (fun n => hi n.val)]
    simp_rw [show ∀ n : I, (∫ u in A n.val, g u ∂μ) =
      finiteZetaCoeff F v μ χ f n.val * r ^ n.val from fun n =>
        finiteZeta_setIntegral_shell F v μ χ f z n.val]
    exact Finset.sum_coe_sort I (fun n : ℤ => finiteZetaCoeff F v μ χ f n * r ^ n)
  have hcoeffTail (k : ℕ) : finiteZetaCoeff F v μ χ f ((N : ℤ) + k) =
      f.val 0 * finiteZetaUnitAverage F v μ χ := by
    let n : ℤ := (N : ℤ) + k
    let π := chosenFiniteUniformizer F v
    have hπ := chosenFiniteUniformizer_spec F v
    unfold finiteZetaCoeff finiteZetaUnitAverage
    rw [← integral_const_mul]
    have hU : MeasurableSet (U F v) := by
      change MeasurableSet (finitePlaceIntegralUnits F v)
      rw [← finiteZetaShell_zero F v]
      exact hmeas 0
    apply setIntegral_congr_fun hU
    intro u hu
    have he : π ^ n * u ∈ A n := by
      change u ∈ (fun a : (K F v)ˣ => π ^ n * a) ⁻¹' finiteZetaShell F v n
      rw [finiteZetaShell_preimage F v π hπ n]
      exact hu
    change f.val (π ^ n * u).val * ((χ u : Circle) : ℂ) = f.val 0 * ((χ u : Circle) : ℂ)
    rw [(hb n (π ^ n * u) he).2 (by dsimp [n]; omega)]
  have hTail : (∫ u in T, g u ∂μ) =
      f.val 0 * finiteZetaUnitAverage F v μ χ * r ^ N * (1 - r)⁻¹ := by
    have hr' : r ≠ 0 := mul_ne_zero (Circle.coe_ne_zero _) (Complex.exp_ne_zero _)
    rw [integral_iUnion (fun k : ℕ => hmeas ((N : ℤ) + k)) hDT hT]
    have hterm (k : ℕ) : (∫ u in A ((N : ℤ) + k), g u ∂μ) =
        (f.val 0 * finiteZetaUnitAverage F v μ χ * r ^ N) * r ^ k := by
      change (∫ u in finiteZetaShell F v ((N : ℤ) + k), g u ∂μ) = _
      rw [finiteZeta_setIntegral_shell F v μ χ f z, hcoeffTail, zpow_add₀ hr',
        zpow_natCast, zpow_natCast]
      simp only [mul_assoc]
    simp_rw [hterm, tsum_mul_left, tsum_geometric_of_norm_lt_one hr]
  change (∫ u, g u ∂μ) = _
  rw [← hmain, hmid, hTail]
  rfl


/-- A finite-place phase is unramified when it is trivial on the integral units. -/
def finiteZetaUnramified (χ : LocalPhase F v) : Prop :=
  ∀ u ∈ U F v, χ u = 1

private theorem finiteZetaUnitAverage_eq (μ : Measure (K F v)ˣ) [μ.IsHaarMeasure]
    (χ : LocalPhase F v) :
    finiteZetaUnitAverage F v μ χ =
      if finiteZetaUnramified F v χ then (μ.real (U F v) : ℂ) else 0 := by
  classical
  let V := (v.adicCompletionIntegers F).toSubmonoid.units
  have hU : MeasurableSet (U F v) := by
    change MeasurableSet (finitePlaceIntegralUnits F v)
    rw [← finiteZetaShell_zero F v]
    exact (finiteZetaShell_closed F v 0).measurableSet
  by_cases h : finiteZetaUnramified F v χ
  · rw [ite_eq_left h]
    unfold finiteZetaUnitAverage
    rw [setIntegral_congr_fun hU (g := fun _ => (1 : ℂ)) (fun u hu => by rw [h u hu, Circle.coe_one]),
      setIntegral_const, Complex.real_smul, mul_one]
  · rw [ite_eq_right h]
    obtain ⟨b, hb, hχ⟩ := not_forall₂.mp h
    let e := MeasurableEquiv.mulLeft b
    have hpre : (fun u : (K F v)ˣ => b * u) ⁻¹' U F v = U F v := by
      ext u
      change b * u ∈ V ↔ u ∈ V
      exact ⟨fun hu => by simpa only [inv_mul_cancel_left] using V.mul_mem (V.inv_mem hb) hu,
        fun hu => V.mul_mem hb hu⟩
    have he := (measurePreserving_mul_left μ b).setIntegral_preimage_emb e.measurableEmbedding
      (fun u => ((χ u : Circle) : ℂ)) (U F v)
    rw [hpre] at he
    simp only [map_mul, Circle.coe_mul, integral_const_mul] at he
    change ((χ b : Circle) : ℂ) * finiteZetaUnitAverage F v μ χ =
      finiteZetaUnitAverage F v μ χ at he
    have hne : ((χ b : Circle) : ℂ) ≠ 1 := by
      intro heq
      exact hχ (Circle.ext (by simpa using heq))
    have hprod : (((χ b : Circle) : ℂ) - 1) * finiteZetaUnitAverage F v μ χ = 0 := by
      rw [sub_mul, one_mul, he, sub_self]
    exact (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hne)

omit [BorelSpace (K F v)ˣ] in
theorem finiteZetaUnitMass_pos (μ : Measure (K F v)ˣ) [μ.IsHaarMeasure] :
    0 < μ.real (U F v) := by
  have hU : IsOpen (U F v) :=
    ((Valued.isOpen_valuationSubring (K F v)).preimage Units.continuous_val).inter
      ((Valued.isOpen_valuationSubring (K F v)).preimage
        (Units.continuous_val.comp continuous_inv))
  have hμ := hU.measure_ne_zero μ ⟨1, one_mem _⟩
  have hf : μ (U F v) ≠ ∞ :=
    (finiteZetaShell_zero F v ▸ finiteZetaShell_compact F v 0).measure_lt_top.ne
  exact ENNReal.toReal_pos hμ hf

/-- An unramified integer-ring factor inserted at a new finite place
contributes its Euler factor and the Haar mass of the integral units. -/
theorem finiteZetaIntegral_integerRing_unramified
    (μ : Measure (K F v)ˣ) [μ.IsHaarMeasure] (χ : LocalPhase F v)
    (hχ : finiteZetaUnramified F v χ) (z : ℂ) (hz : 0 < z.re) :
    finiteZetaIntegral F v μ χ (finiteCompletionIntegerRingTest F v) z =
      (μ.real (finitePlaceIntegralUnits F v) : ℂ) * (1 - finiteZetaRatio F v χ z)⁻¹ := by
  let q : ℝ := v.asIdeal.absNorm
  have hq : 1 < q := by
    dsimp [q]
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  have htest (x : K F v) : (finiteCompletionIntegerRingTest F v).val x =
      if ‖x‖ ≤ 1 then 1 else 0 := by
    change (v.adicCompletionIntegers F : Set (K F v)).indicator (fun _ ↦ (1 : ℂ)) x = _
    rw [← finiteCompletion_closedBall F v]
    simp only [Set.indicator, Metric.mem_closedBall, dist_zero_right]
  have h0 : (finiteCompletionIntegerRingTest F v).val 0 = 1 := by simp [htest]
  have hb (n : ℤ) (u : (K F v)ˣ) (hu : u ∈ finiteZetaShell F v n) :
      (n < (0 : ℤ) → (finiteCompletionIntegerRingTest F v).val u.val = 0) ∧
        ((0 : ℤ) ≤ n → (finiteCompletionIntegerRingTest F v).val u.val =
          (finiteCompletionIntegerRingTest F v).val 0) := by
    change ‖u.val‖ = q ^ (-n) at hu
    rw [htest, hu, h0]
    constructor
    · intro hn
      have hp : 1 < q ^ (-n) := by
        simpa using (zpow_right_strictMono₀ hq) (show (0 : ℤ) < -n by omega)
      exact ite_eq_right (not_le.mpr hp)
    · intro hn
      have hp : q ^ (-n) ≤ 1 := by
        simpa using (zpow_right_mono₀ hq.le) (show -n ≤ (0 : ℤ) by omega)
      exact ite_eq_left hp
  rw [(finiteZeta_integral_expansion F v μ χ (finiteCompletionIntegerRingTest F v)
    0 0 (by simpa only [Nat.cast_zero] using hb) z hz).2]
  simp only [finiteZetaExpansion, Nat.cast_zero, Finset.Ico_self, Finset.sum_empty, h0, one_mul,
    pow_zero, mul_one, zero_add, finiteZetaUnitAverage_eq F v μ χ, ite_eq_left hχ]

private def finiteZetaLower (f : locallyConstantTests (K F v)) : ℤ :=
  (finiteZetaShell_test_bounds F v f).choose

private def finiteZetaTail (f : locallyConstantTests (K F v)) : ℕ :=
  (finiteZetaShell_test_bounds F v f).choose_spec.choose

omit [MeasurableSpace (K F v)ˣ] [BorelSpace (K F v)ˣ] in
private theorem finiteZetaCutoffs_spec (f : locallyConstantTests (K F v)) :
    ∀ n (u : (K F v)ˣ), u ∈ finiteZetaShell F v n →
      (n < finiteZetaLower F v f → f.val u.val = 0) ∧
      ((finiteZetaTail F v f : ℤ) ≤ n → f.val u.val = f.val 0) :=
  (finiteZetaShell_test_bounds F v f).choose_spec.choose_spec.2

/-- The continuation of the finite-place zeta integral in the twist exponent. -/
def finiteZetaContinuation (μ : Measure (K F v)ˣ) (χ : LocalPhase F v)
    (f : locallyConstantTests (K F v)) : ℂ → ℂ :=
  finiteZetaExpansion F v μ χ f (finiteZetaLower F v f) (finiteZetaTail F v f)

/-- The continuation agrees with the absolutely convergent local integral. -/
theorem finiteZetaContinuation_eq_integral (μ : Measure (K F v)ˣ) [μ.IsHaarMeasure]
    (χ : LocalPhase F v) (f : locallyConstantTests (K F v)) (z : ℂ) (hz : 0 < z.re) :
    Integrable (fun u : (K F v)ˣ => f.val u.val * (χ u : ℂ) * finiteZetaWeight F v z u) μ ∧
      finiteZetaIntegral F v μ χ f z = finiteZetaContinuation F v μ χ f z :=
  finiteZeta_integral_expansion F v μ χ f _ _ (finiteZetaCutoffs_spec F v f) z hz

omit [MeasurableSpace (K F v)ˣ] [BorelSpace (K F v)ˣ] in
/-- The uniformizer ratio is entire in the spectral parameter. -/
theorem finiteZetaRatio_analytic (χ : LocalPhase F v) (z : ℂ) :
    AnalyticAt ℂ (finiteZetaRatio F v χ) z := by
  unfold finiteZetaRatio
  fun_prop

omit [MeasurableSpace (K F v)ˣ] [BorelSpace (K F v)ˣ] in
/-- A twisted character never vanishes on the uniformizer. -/
theorem finiteZetaRatio_ne_zero (χ : LocalPhase F v) (z : ℂ) :
    finiteZetaRatio F v χ z ≠ 0 :=
  mul_ne_zero (Circle.coe_ne_zero _) (Complex.exp_ne_zero _)

private def finiteZetaRegularPart (μ : Measure (K F v)ˣ) (χ : LocalPhase F v)
    (f : locallyConstantTests (K F v)) (z : ℂ) : ℂ :=
  ∑ n ∈ Finset.Ico (finiteZetaLower F v f) (finiteZetaTail F v f : ℤ),
    finiteZetaCoeff F v μ χ f n * (finiteZetaRatio F v χ z) ^ n

private def finiteZetaNumerator (μ : Measure (K F v)ˣ) (χ : LocalPhase F v)
    (f : locallyConstantTests (K F v)) (z : ℂ) : ℂ :=
  f.val 0 * finiteZetaUnitAverage F v μ χ * (finiteZetaRatio F v χ z) ^ finiteZetaTail F v f

omit [BorelSpace (K F v)ˣ] in
private theorem finiteZetaRegularPart_analytic (μ : Measure (K F v)ˣ) (χ : LocalPhase F v)
    (f : locallyConstantTests (K F v)) (z : ℂ) :
    AnalyticAt ℂ (finiteZetaRegularPart F v μ χ f) z := by
  unfold finiteZetaRegularPart
  apply Finset.analyticAt_fun_sum
  intro n _
  exact analyticAt_const.mul ((finiteZetaRatio_analytic F v χ z).zpow
    (finiteZetaRatio_ne_zero F v χ z))

omit [BorelSpace (K F v)ˣ] in
private theorem finiteZetaNumerator_analytic (μ : Measure (K F v)ˣ) (χ : LocalPhase F v)
    (f : locallyConstantTests (K F v)) (z : ℂ) :
    AnalyticAt ℂ (finiteZetaNumerator F v μ χ f) z :=
  analyticAt_const.mul ((finiteZetaRatio_analytic F v χ z).pow _)

/-- The analytic denominator of the local finite zeta continuation. -/
def finiteZetaDenominator (χ : LocalPhase F v) (z : ℂ) : ℂ :=
  1 - finiteZetaRatio F v χ z

omit [MeasurableSpace (K F v)ˣ] [BorelSpace (K F v)ˣ] in
theorem finiteZetaDenominator_analytic (χ : LocalPhase F v) (z : ℂ) :
    AnalyticAt ℂ (finiteZetaDenominator F v χ) z :=
  analyticAt_const.sub (finiteZetaRatio_analytic F v χ z)

omit [MeasurableSpace (K F v)ˣ] [BorelSpace (K F v)ˣ] in
theorem finiteZetaDenominator_ne_zero_of_pos (χ : LocalPhase F v) (z : ℂ) (hz : 0 < z.re) :
    finiteZetaDenominator F v χ z ≠ 0 := by
  intro h
  have he : finiteZetaRatio F v χ z = 1 := (sub_eq_zero.mp h).symm
  simpa [he] using finiteZetaRatio_norm_lt_one F v χ z hz

omit [BorelSpace (K F v)ˣ] in
private theorem finiteZetaContinuation_decomp (μ : Measure (K F v)ˣ) (χ : LocalPhase F v)
    (f : locallyConstantTests (K F v)) :
    finiteZetaContinuation F v μ χ f =
      fun z => finiteZetaRegularPart F v μ χ f z +
        finiteZetaNumerator F v μ χ f z / finiteZetaDenominator F v χ z := by
  funext z
  rfl

omit [BorelSpace (K F v)ˣ] in
/-- Meromorphic continuation at every twist exponent. -/
theorem finiteZetaContinuation_meromorphic (μ : Measure (K F v)ˣ) (χ : LocalPhase F v)
    (f : locallyConstantTests (K F v)) : MeromorphicOn (finiteZetaContinuation F v μ χ f) univ := by
  intro z _
  rw [finiteZetaContinuation_decomp]
  exact (finiteZetaRegularPart_analytic F v μ χ f z).meromorphicAt.add
    ((finiteZetaNumerator_analytic F v μ χ f z).meromorphicAt.div
      (finiteZetaDenominator_analytic F v χ z).meromorphicAt)


private abbrev finiteZetaLogQ : ℂ := Real.log (v.asIdeal.absNorm : ℝ)

omit [MeasurableSpace (K F v)ˣ] [BorelSpace (K F v)ˣ] in
private theorem finiteZetaLogQ_ne_zero : finiteZetaLogQ F v ≠ 0 := by
  have hq : 1 < (v.asIdeal.absNorm : ℝ) := by
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  exact Complex.ofReal_ne_zero.mpr (Real.log_pos hq).ne'

omit [MeasurableSpace (K F v)ˣ] [BorelSpace (K F v)ˣ] in
private theorem finiteZetaDenominator_hasDerivAt (χ : LocalPhase F v) (z : ℂ) :
    HasDerivAt (finiteZetaDenominator F v χ)
      (finiteZetaLogQ F v * finiteZetaRatio F v χ z) z := by
  let d := finiteZetaLogQ F v
  let a := ((χ (chosenFiniteUniformizer F v) : Circle) : ℂ)
  have h := ((((hasDerivAt_id z).neg.mul_const d).cexp).const_mul a).const_sub (1 : ℂ)
  exact h.congr_deriv (by
    change -(a * (Complex.exp (-z * d) * (-1 * d))) = d * (a * Complex.exp (-z * d))
    ring)

omit [MeasurableSpace (K F v)ˣ] [BorelSpace (K F v)ˣ] in
/-- Each zero of the unramified Euler denominator is simple. -/
theorem finiteZetaDenominator_simple_zero (χ : LocalPhase F v) (z : ℂ)
    (hz : finiteZetaDenominator F v χ z = 0) :
    analyticOrderAt (finiteZetaDenominator F v χ) z = 1 := by
  have hratio : finiteZetaRatio F v χ z = 1 := (sub_eq_zero.mp hz).symm
  apply (finiteZetaDenominator_analytic F v χ z).analyticOrderAt_eq_one_of_zero_deriv_ne_zero hz
  rw [(finiteZetaDenominator_hasDerivAt F v χ z).deriv, hratio, mul_one]
  exact finiteZetaLogQ_ne_zero F v

/-- A pole is present precisely for a nonzero value at zero, an
unramified phase, and the trivial value at the uniformizer after twisting.
All other points of the continuation are analytic. -/
theorem finiteZetaContinuation_poles (μ : Measure (K F v)ˣ) [μ.IsHaarMeasure]
    (χ : LocalPhase F v) (f : locallyConstantTests (K F v)) (w : ℂ) :
    let P := f.val 0 ≠ 0 ∧ finiteZetaUnramified F v χ ∧ finiteZetaRatio F v χ w = 1
    (meromorphicOrderAt (finiteZetaContinuation F v μ χ f) w = (-1 : WithTop ℤ) ↔ P) ∧
      (¬P → AnalyticAt ℂ (finiteZetaContinuation F v μ χ f) w) := by
  classical
  let P := f.val 0 ≠ 0 ∧ finiteZetaUnramified F v χ ∧ finiteZetaRatio F v χ w = 1
  let E := finiteZetaRegularPart F v μ χ f
  let B := finiteZetaNumerator F v μ χ f
  let D := finiteZetaDenominator F v χ
  change (meromorphicOrderAt (finiteZetaContinuation F v μ χ f) w = -1 ↔ P) ∧
    (¬P → AnalyticAt ℂ (finiteZetaContinuation F v μ χ f) w)
  rw [finiteZetaContinuation_decomp]
  change (meromorphicOrderAt (fun z => E z + B z / D z) w = -1 ↔ P) ∧
    (¬P → AnalyticAt ℂ (fun z => E z + B z / D z) w)
  have hE : AnalyticAt ℂ E w := finiteZetaRegularPart_analytic F v μ χ f w
  have hB : AnalyticAt ℂ B w := finiteZetaNumerator_analytic F v μ χ f w
  have hD : AnalyticAt ℂ D w := finiteZetaDenominator_analytic F v χ w
  have han (hn : ¬P) : AnalyticAt ℂ (fun z => E z + B z / D z) w := by
    by_cases hr : finiteZetaRatio F v χ w = 1
    · have hzero : B = 0 := by
        funext z
        by_cases hf : f.val 0 = 0
        · simp [B, finiteZetaNumerator, hf]
        · have hc : ¬finiteZetaUnramified F v χ := fun hc => hn ⟨hf, hc, hr⟩
          simp [B, finiteZetaNumerator, finiteZetaUnitAverage_eq F v μ χ, hc]
      simpa only [hzero, Pi.zero_apply, zero_div, add_zero] using hE
    · exact hE.add (hB.div hD (sub_ne_zero.mpr (Ne.symm hr)))
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, han⟩
  · by_contra hn
    have ho := (han hn).meromorphicOrderAt_nonneg
    rw [h] at ho
    exact (by decide : ¬(0 : ℤ) ≤ -1) (WithTop.coe_le_coe.mp ho)
  · obtain ⟨hf, hχ, hr⟩ := h
    have hzero : D w = 0 := sub_eq_zero.mpr hr.symm
    have hd := finiteZetaDenominator_hasDerivAt F v χ w
    rw [hr, mul_one] at hd
    have hDo : meromorphicOrderAt D w = 1 := by
      rw [hD.meromorphicOrderAt_eq, hD.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hzero
        (hd.deriv ▸ finiteZetaLogQ_ne_zero F v)]
      rfl
    have hBw : B w ≠ 0 := by
      change f.val 0 * finiteZetaUnitAverage F v μ χ * finiteZetaRatio F v χ w ^
        finiteZetaTail F v f ≠ 0
      rw [finiteZetaUnitAverage_eq F v μ χ, ite_eq_left hχ, hr, one_pow, mul_one]
      exact mul_ne_zero hf (Complex.ofReal_ne_zero.mpr (finiteZetaUnitMass_pos F v μ).ne')
    have hBo : meromorphicOrderAt B w = 0 := by
      rw [hB.meromorphicOrderAt_eq, hB.analyticOrderAt_eq_zero.mpr hBw]
      rfl
    have hp : meromorphicOrderAt (B / D) w = -1 := by
      rw [meromorphicOrderAt_div hB.meromorphicAt hD.meromorphicAt, hBo, hDo]
      rfl
    rw [show (fun z => E z + B z / D z) = fun z => B z / D z + E z from
      funext (fun z => add_comm _ _)]
    change meromorphicOrderAt ((B / D) + E) w = -1
    rw [meromorphicOrderAt_add_eq_left_of_lt hE.meromorphicAt]
    · exact hp
    · rw [hp]
      exact (WithTop.coe_lt_coe.mpr (by decide : (-1 : ℤ) < 0)).trans_le hE.meromorphicOrderAt_nonneg


/-- At an unramified lift of the trivial quasi-character the residue is
the unit mass divided by the log residue cardinality, times evaluation at zero. -/
theorem finiteZetaContinuation_residue (μ : Measure (K F v)ˣ) [μ.IsHaarMeasure]
    (χ : LocalPhase F v) (f : locallyConstantTests (K F v)) (w : ℂ)
    (hχ : finiteZetaUnramified F v χ) (hw : finiteZetaRatio F v χ w = 1) :
    Tendsto (fun z => (z - w) * finiteZetaContinuation F v μ χ f z)
      (𝓝[≠] w) (𝓝 ((μ.real (U F v) : ℂ) / finiteZetaLogQ F v * f.val 0)) := by
  let E := finiteZetaRegularPart F v μ χ f
  let B := finiteZetaNumerator F v μ χ f
  let D := finiteZetaDenominator F v χ
  let d := finiteZetaLogQ F v
  have hDw : D w = 0 := sub_eq_zero.mpr hw.symm
  have hd := finiteZetaDenominator_hasDerivAt F v χ w
  rw [hw, mul_one] at hd
  have hSlope : Tendsto (fun z => D z / (z - w)) (𝓝[≠] w) (𝓝 d) := by
    have hs : Tendsto (slope D w) (𝓝[≠] w) (𝓝 d) := hd.tendsto_slope
    simpa only [slope_fun_def_field, hDw, sub_zero, div_eq_mul_inv, mul_comm] using hs
  have hE : Tendsto E (𝓝[≠] w) (𝓝 (E w)) :=
    (finiteZetaRegularPart_analytic F v μ χ f w).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hB : Tendsto B (𝓝[≠] w) (𝓝 (B w)) :=
    (finiteZetaNumerator_analytic F v μ χ f w).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hz : Tendsto (fun z : ℂ => z - w) (𝓝[≠] w) (𝓝 0) := by
    have hc : Continuous (fun z : ℂ => z - w) := continuous_id.sub continuous_const
    simpa only [sub_self] using
      (hc.tendsto w).mono_left (nhdsWithin_le_nhds (s := {w}ᶜ))
  have hmain := (hz.mul hE).add (hB.mul (hSlope.inv₀ (finiteZetaLogQ_ne_zero F v)))
  have hBw : B w = f.val 0 * (μ.real (U F v) : ℂ) := by
    change f.val 0 * finiteZetaUnitAverage F v μ χ * finiteZetaRatio F v χ w ^
      finiteZetaTail F v f = _
    rw [finiteZetaUnitAverage_eq F v μ χ, ite_eq_left hχ, hw, one_pow, mul_one]
  rw [zero_mul, zero_add, hBw,
    show f.val 0 * (μ.real (U F v) : ℂ) * d⁻¹ =
      (μ.real (U F v) : ℂ) / d * f.val 0 by rw [div_eq_mul_inv]; ring] at hmain
  change Tendsto _ _ (𝓝 ((μ.real (U F v) : ℂ) / d * f.val 0))
  refine hmain.congr' (Eventually.of_forall fun z => ?_)
  rw [finiteZetaContinuation_decomp, inv_div, div_eq_mul_inv]
  change (z - w) * E z + B z * ((z - w) * (D z)⁻¹) =
    (z - w) * (E z + B z / D z)
  rw [div_eq_mul_inv]
  ring

/-- At an actual simple pole, the Laurent coefficient of order minus
one is the same corrected residue. -/
theorem finiteZetaContinuation_trailingCoeff (μ : Measure (K F v)ˣ) [μ.IsHaarMeasure]
    (χ : LocalPhase F v) (f : locallyConstantTests (K F v)) (w : ℂ)
    (hf : f.val 0 ≠ 0) (hχ : finiteZetaUnramified F v χ) (hw : finiteZetaRatio F v χ w = 1) :
    meromorphicTrailingCoeffAt (finiteZetaContinuation F v μ χ f) w =
      (μ.real (U F v) : ℂ) / finiteZetaLogQ F v * f.val 0 := by
  have hm := finiteZetaContinuation_meromorphic F v μ χ f w (mem_univ w)
  have ho := (finiteZetaContinuation_poles F v μ χ f w).1.mpr ⟨hf, hχ, hw⟩
  have h := hm.tendsto_nhds_meromorphicTrailingCoeffAt
  rw [ho] at h
  have h' : Tendsto (fun z => (z - w) * finiteZetaContinuation F v μ χ f z)
      (𝓝[≠] w) (𝓝 (meromorphicTrailingCoeffAt (finiteZetaContinuation F v μ χ f) w)) := by
    change Tendsto ((fun z : ℂ => z - w) * finiteZetaContinuation F v μ χ f) _ _
    simpa only [show -(WithTop.untop₀ (-1 : WithTop ℤ)) = (1 : ℤ) from rfl, zpow_one, Pi.smul_apply,
      smul_eq_mul] using h
  exact tendsto_nhds_unique h' (finiteZetaContinuation_residue F v μ χ f w hχ hw)

/-- On a ramified component the finite-place continuation is entire. -/
theorem finiteZetaContinuation_analytic_of_ramified
    (μ : Measure (K F v)ˣ) [μ.IsHaarMeasure] (χ : LocalPhase F v)
    (hχ : ¬finiteZetaUnramified F v χ) (f : locallyConstantTests (K F v)) :
    AnalyticOnNhd ℂ (finiteZetaContinuation F v μ χ f) univ :=
  fun w _ => (finiteZetaContinuation_poles F v μ χ f w).2 (fun h => hχ h.2.1)

omit [MeasurableSpace (K F v)ˣ] [BorelSpace (K F v)ˣ] in
/-- Shell coordinates convert the twisted character to a unit phase and
an integer power of its value on the chosen uniformizer. -/
theorem finiteZetaTwist_shell (χ : LocalPhase F v) (z : ℂ) (n : ℤ)
    (u : (K F v)ˣ) (hu : u ∈ U F v) :
    let π := chosenFiniteUniformizer F v
    ((χ (π ^ n * u) : Circle) : ℂ) * finiteZetaWeight F v z (π ^ n * u) =
      (finiteZetaRatio F v χ z) ^ n * ((χ u : Circle) : ℂ) := by
  let π := chosenFiniteUniformizer F v
  have hm : π ^ n * u ∈ finiteZetaShell F v n := by
    change u ∈ (fun a : (K F v)ˣ => π ^ n * a) ⁻¹' finiteZetaShell F v n
    rw [finiteZetaShell_preimage F v π (chosenFiniteUniformizer_spec F v)]
    exact hu
  change ((χ (π ^ n * u) : Circle) : ℂ) * finiteZetaWeight F v z (π ^ n * u) = _
  rw [finiteZetaWeight_onShell F v z n _ hm]
  simp only [finiteZetaRatio, map_mul, map_zpow, Circle.coe_mul, Circle.coe_zpow, mul_zpow]
  change ((χ π : Circle) : ℂ) ^ n * ((χ u : Circle) : ℂ) *
      Complex.exp (-z * finiteZetaLogQ F v) ^ n =
    ((χ π : Circle) : ℂ) ^ n * Complex.exp (-z * finiteZetaLogQ F v) ^ n *
      ((χ u : Circle) : ℂ)
  ring

omit [MeasurableSpace (K F v)ˣ] [BorelSpace (K F v)ˣ] in
/-- The pole condition on phase and exponent means that the actual
twisted quasi-character is trivial on the entire local multiplicative group. -/
theorem finiteZetaTwist_trivial_iff (χ : LocalPhase F v) (z : ℂ) :
    (∀ u : (K F v)ˣ, ((χ u : Circle) : ℂ) * finiteZetaWeight F v z u = 1) ↔
      finiteZetaUnramified F v χ ∧ finiteZetaRatio F v χ z = 1 := by
  let π := chosenFiniteUniformizer F v
  constructor
  · intro h
    have hone : (1 : (K F v)ˣ) ∈ U F v := one_mem ((v.adicCompletionIntegers F).toSubmonoid.units)
    refine ⟨fun u hu => ?_, ?_⟩
    · have hu' : u ∈ finiteZetaShell F v 0 := by
        simpa only [finiteZetaShell_zero F v] using hu
      have he := h u
      rw [finiteZetaWeight_onShell F v z 0 u hu', zpow_zero, mul_one] at he
      apply Circle.ext
      simpa only [Circle.coe_one] using he
    · have he := finiteZetaTwist_shell F v χ z 1 1 hone
      change ((χ (π ^ (1 : ℤ) * 1) : Circle) : ℂ) * finiteZetaWeight F v z (π ^ (1 : ℤ) * 1) =
        finiteZetaRatio F v χ z ^ (1 : ℤ) * ((χ 1 : Circle) : ℂ) at he
      simp only [zpow_one, mul_one, map_one, Circle.coe_one] at he
      exact he.symm.trans (h π)
  · rintro ⟨hχ, hr⟩ g
    obtain ⟨n, hn⟩ := iUnion_eq_univ_iff.mp (finiteZetaShell_iUnion F v) g
    let w := (π ^ n)⁻¹ * g
    have he : π ^ n * w = g := by simp [w]
    have hw : w ∈ U F v := by
      change w ∈ finitePlaceIntegralUnits F v
      rw [← finiteZetaShell_preimage F v π (chosenFiniteUniformizer_spec F v) n]
      change π ^ n * w ∈ finiteZetaShell F v n
      rwa [he]
    have ht := finiteZetaTwist_shell F v χ z n w hw
    change ((χ (π ^ n * w) : Circle) : ℂ) * finiteZetaWeight F v z (π ^ n * w) =
      finiteZetaRatio F v χ z ^ n * ((χ w : Circle) : ℂ) at ht
    simpa only [he, hr, one_zpow, hχ w hw, Circle.coe_one, mul_one] using ht


omit [MeasurableSpace (K F v)ˣ] [BorelSpace (K F v)ˣ] in
theorem finiteZetaWeight_mul (z : ℂ) (g h : (K F v)ˣ) :
    finiteZetaWeight F v z (g * h) = finiteZetaWeight F v z g * finiteZetaWeight F v z h := by
  unfold finiteZetaWeight
  rw [Units.val_mul, norm_mul, Real.log_mul (norm_ne_zero_iff.mpr g.ne_zero)
    (norm_ne_zero_iff.mpr h.ne_zero), Complex.ofReal_add, mul_add, Complex.exp_add]

omit [MeasurableSpace (K F v)ˣ] [BorelSpace (K F v)ˣ] in
theorem finiteZetaShell_repr (g : (K F v)ˣ) :
    ∃ (n : ℤ) (u : (K F v)ˣ), u ∈ U F v ∧ chosenFiniteUniformizer F v ^ n * u = g := by
  let π := chosenFiniteUniformizer F v
  obtain ⟨n, hn⟩ := iUnion_eq_univ_iff.mp (finiteZetaShell_iUnion F v) g
  let u := (π ^ n)⁻¹ * g
  have he : π ^ n * u = g := by simp [u]
  refine ⟨n, u, ?_, he⟩
  change u ∈ finitePlaceIntegralUnits F v
  rw [← finiteZetaShell_preimage F v π (chosenFiniteUniformizer_spec F v) n]
  change π ^ n * u ∈ finiteZetaShell F v n
  rwa [he]

omit [MeasurableSpace (K F v)ˣ] [BorelSpace (K F v)ˣ] in
/-- Every finite-place quasi-character is a unitary phase trivial on the
chosen uniformizer times a complex norm twist. The norm of its value at
the uniformizer detects the positive half-plane. -/
theorem finiteZeta_represents_quasiCharacter (ψ : (K F v)ˣ →ₜ* ℂ) :
    ∃ (χ : LocalPhase F v) (z : ℂ), χ (chosenFiniteUniformizer F v) = 1 ∧
      (∀ g, ψ g = ((χ g : Circle) : ℂ) * finiteZetaWeight F v z g) ∧
      (0 < z.re ↔ ‖ψ (chosenFiniteUniformizer F v)‖ < 1) := by
  let V := (v.adicCompletionIntegers F).toSubmonoid.units
  let π := chosenFiniteUniformizer F v
  let d := finiteZetaLogQ F v
  have hd : d ≠ 0 := finiteZetaLogQ_ne_zero F v
  have ha : ψ π ≠ 0 := (ψ.toMonoidHom.toHomUnits π).ne_zero
  let z := -Complex.log (ψ π) / d
  have hz : -z * d = Complex.log (ψ π) := by
    dsimp [z]
    rw [neg_div, neg_neg, div_mul_cancel₀ _ hd]
  have hr : Complex.exp (-z * d) = ψ π := by rw [hz, Complex.exp_log ha]
  have hV : IsCompact (U F v) :=
    Submonoid.units_isCompact (S := (v.adicCompletionIntegers F).toSubmonoid)
      (finitePlaceIntegral_compact F v)
  obtain ⟨M, hM⟩ := (hV.image ψ.continuous.norm).bddAbove
  have hle (u : (K F v)ˣ) (hu : u ∈ U F v) : ‖ψ u‖ ≤ 1 := by
    by_contra! h
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt M h
    apply hn.not_ge
    have hb := hM (mem_image_of_mem (fun u => ‖ψ u‖) (show u ^ n ∈ U F v from V.pow_mem hu n))
    simpa only [map_pow, norm_pow] using hb
  have hunit (u : (K F v)ˣ) (hu : u ∈ U F v) : ‖ψ u‖ = 1 := by
    have h := hle u⁻¹ (V.inv_mem hu)
    rw [map_inv, norm_inv] at h
    exact (hle u hu).antisymm ((inv_le_one₀ (norm_pos_iff.mpr
      (ψ.toMonoidHom.toHomUnits u).ne_zero)).mp h)
  let W := finiteZetaWeight F v z
  let L (g : (K F v)ˣ) := ψ g / W g
  have hLnorm (g : (K F v)ˣ) : ‖L g‖ = 1 := by
    obtain ⟨n, u, hu, rfl⟩ := finiteZetaShell_repr F v g
    have hm : π ^ n * u ∈ finiteZetaShell F v n := by
      change u ∈ (fun a : (K F v)ˣ => π ^ n * a) ⁻¹' finiteZetaShell F v n
      rw [finiteZetaShell_preimage F v π (chosenFiniteUniformizer_spec F v)]
      exact hu
    change ‖ψ (π ^ n * u) / finiteZetaWeight F v z (π ^ n * u)‖ = 1
    rw [finiteZetaWeight_onShell F v z n _ hm, show
      Complex.exp (-z * finiteZetaLogQ F v) = ψ π from hr, map_mul, map_zpow, norm_div,
      norm_mul, hunit u hu, mul_one, div_self (norm_ne_zero_iff.mpr (zpow_ne_zero _ ha))]
  have hSphere (g : (K F v)ˣ) : L g ∈ Submonoid.unitSphere ℂ := by
    change dist (L g) 0 = 1
    rw [dist_zero_right, hLnorm]
  have hW : Continuous W :=
    (continuous_const.mul (Complex.continuous_ofReal.comp
      ((continuous_norm.comp Units.continuous_val).log
        (fun u : (K F v)ˣ => norm_ne_zero_iff.mpr u.ne_zero)))).cexp
  have hWne (g : (K F v)ˣ) : W g ≠ 0 := Complex.exp_ne_zero _
  let χ : LocalPhase F v :=
    { toFun := fun g => ⟨L g, hSphere g⟩
      map_one' := Subtype.ext (by simp [L, W, finiteZetaWeight])
      map_mul' := fun g h => Subtype.ext (by
        change L (g * h) = L g * L h
        unfold L W
        rw [map_mul, finiteZetaWeight_mul, mul_div_mul_comm])
      continuous_toFun := (ψ.continuous.div hW hWne).subtype_mk hSphere }
  have hwπ : W π = ψ π := by
    have hm : π ^ (1 : ℤ) * 1 ∈ finiteZetaShell F v 1 := by
      change (1 : (K F v)ˣ) ∈ (fun a : (K F v)ˣ => π ^ (1 : ℤ) * a) ⁻¹' finiteZetaShell F v 1
      rw [finiteZetaShell_preimage F v π (chosenFiniteUniformizer_spec F v)]
      exact one_mem V
    have h := finiteZetaWeight_onShell F v z 1 _ hm
    simp only [zpow_one, mul_one] at h
    exact h.trans hr
  refine ⟨χ, z, ?_, fun g => ?_, ?_⟩
  · apply Circle.ext
    change ψ π / W π = 1
    rw [hwπ, div_self ha]
  · change ψ g = (ψ g / W g) * W g
    rw [div_mul_cancel₀ _ (hWne g)]
  · change 0 < z.re ↔ ‖ψ π‖ < 1
    rw [← hr, Complex.norm_exp, Complex.mul_re, Complex.neg_re]
    have hq : 1 < (v.asIdeal.absNorm : ℝ) := by
      exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
    change 0 < z.re ↔ Real.exp ((-z.re) * Real.log (v.asIdeal.absNorm : ℝ) - (-z).im * 0) < 1
    rw [mul_zero, sub_zero, ← Real.exp_zero, Real.exp_lt_exp]
    constructor
    · intro h
      exact mul_neg_of_neg_of_pos (neg_lt_zero.mpr h) (Real.log_pos hq)
    · intro h
      have hn : -z.re < 0 := (mul_lt_mul_iff_left₀ (Real.log_pos hq)).mp (by simpa only [zero_mul] using h)
      exact neg_lt_zero.mp hn


omit [MeasurableSpace (K F v)ˣ] [BorelSpace (K F v)ˣ] in
/-- The two lifts of the same point on a fixed twist cylinder differ by
an integer multiple of the logarithmic period. -/
theorem finiteZetaRatio_eq_iff_period (χ : LocalPhase F v) (z w : ℂ) :
    finiteZetaRatio F v χ z = finiteZetaRatio F v χ w ↔
      ∃ n : ℤ, z = w + (n : ℂ) * (2 * Real.pi * Complex.I / finiteZetaLogQ F v) := by
  let d := finiteZetaLogQ F v
  have hd : d ≠ 0 := finiteZetaLogQ_ne_zero F v
  let a := ((χ (chosenFiniteUniformizer F v) : Circle) : ℂ)
  have ha : a ≠ 0 := Circle.coe_ne_zero _
  change a * Complex.exp (-z * d) = a * Complex.exp (-w * d) ↔
    ∃ n : ℤ, z = w + (n : ℂ) * (2 * Real.pi * Complex.I / d)
  have he : a * Complex.exp (-z * d) = a * Complex.exp (-w * d) ↔
      Complex.exp (-z * d) = Complex.exp (-w * d) :=
    ⟨mul_left_cancel₀ ha, fun h => congrArg (a * ·) h⟩
  rw [he, Complex.exp_eq_exp_iff_exists_int]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨-n, ?_⟩
    rw [Int.cast_neg]
    apply mul_right_cancel₀ hd
    have hx : z * d = -( -w * d + (n : ℂ) * (2 * Real.pi * Complex.I)) := by
      rw [← hn]
      ring
    rw [hx]
    field_simp [hd]
    ring
  · rintro ⟨n, hn⟩
    refine ⟨-n, ?_⟩
    rw [Int.cast_neg, hn]
    field_simp [hd]
    ring

/-- The meromorphic formula is intrinsic to the twisted quasi-character,
even if its phase and exponent are presented by different lifts. -/
theorem finiteZetaContinuation_eq_of_twist_eq (μ : Measure (K F v)ˣ)
    (χ ψ : LocalPhase F v) (f : locallyConstantTests (K F v)) (z w : ℂ)
    (he : ∀ u : (K F v)ˣ, ((χ u : Circle) : ℂ) * finiteZetaWeight F v z u =
      ((ψ u : Circle) : ℂ) * finiteZetaWeight F v w u) :
    finiteZetaContinuation F v μ χ f z = finiteZetaContinuation F v μ ψ f w := by
  let π := chosenFiniteUniformizer F v
  have hU : MeasurableSet (U F v) := by
    change MeasurableSet (finitePlaceIntegralUnits F v)
    rw [← finiteZetaShell_zero F v]
    exact (finiteZetaShell_closed F v 0).measurableSet
  have hPhase (u : (K F v)ˣ) (hu : u ∈ U F v) :
      ((χ u : Circle) : ℂ) = ((ψ u : Circle) : ℂ) := by
    have hm : u ∈ finiteZetaShell F v 0 := by simpa only [finiteZetaShell_zero F v] using hu
    simpa only [finiteZetaWeight_onShell F v z 0 u hm, finiteZetaWeight_onShell F v w 0 u hm,
      zpow_zero, mul_one] using he u
  have hπ : π ∈ finiteZetaShell F v 1 := by
    have hn : π ^ (1 : ℤ) * 1 ∈ finiteZetaShell F v 1 := by
      change (1 : (K F v)ˣ) ∈ (fun a : (K F v)ˣ => π ^ (1 : ℤ) * a) ⁻¹' finiteZetaShell F v 1
      rw [finiteZetaShell_preimage F v π (chosenFiniteUniformizer_spec F v)]
      exact one_mem ((v.adicCompletionIntegers F).toSubmonoid.units)
    simpa only [zpow_one, mul_one] using hn
  have hRatio : finiteZetaRatio F v χ z = finiteZetaRatio F v ψ w := by
    simpa only [finiteZetaRatio, finiteZetaWeight_onShell F v z 1 π hπ,
      finiteZetaWeight_onShell F v w 1 π hπ, zpow_one] using he π
  have hAve : finiteZetaUnitAverage F v μ χ = finiteZetaUnitAverage F v μ ψ :=
    setIntegral_congr_fun hU hPhase
  have hCoeff (n : ℤ) : finiteZetaCoeff F v μ χ f n = finiteZetaCoeff F v μ ψ f n :=
    setIntegral_congr_fun hU (fun u hu => congrArg
      (f.val (π ^ n * u).val * ·) (hPhase u hu))
  unfold finiteZetaContinuation finiteZetaExpansion
  simp_rw [hRatio, hAve, hCoeff]


private def finiteZetaCleared (μ : Measure (K F v)ˣ) (χ : LocalPhase F v)
    (f : locallyConstantTests (K F v)) (z : ℂ) : ℂ :=
  finiteZetaRegularPart F v μ χ f z * finiteZetaDenominator F v χ z +
    finiteZetaNumerator F v μ χ f z

omit [BorelSpace (K F v)ˣ] in
private theorem finiteZetaCleared_analytic (μ : Measure (K F v)ˣ) (χ : LocalPhase F v)
    (f : locallyConstantTests (K F v)) : AnalyticOnNhd ℂ (finiteZetaCleared F v μ χ f) univ :=
  fun z _ => ((finiteZetaRegularPart_analytic F v μ χ f z).mul
    (finiteZetaDenominator_analytic F v χ z)).add (finiteZetaNumerator_analytic F v μ χ f z)

private theorem finiteZetaCleared_eq (μ : Measure (K F v)ˣ) [μ.IsHaarMeasure]
    (χ : LocalPhase F v) (f : locallyConstantTests (K F v)) (z : ℂ) (hz : 0 < z.re) :
    finiteZetaCleared F v μ χ f z =
      finiteZetaIntegral F v μ χ f z * finiteZetaDenominator F v χ z := by
  have hd := finiteZetaDenominator_ne_zero_of_pos F v χ z hz
  rw [(finiteZetaContinuation_eq_integral F v μ χ f z hz).2, finiteZetaContinuation_decomp]
  change _ = (finiteZetaRegularPart F v μ χ f z +
    finiteZetaNumerator F v μ χ f z / finiteZetaDenominator F v χ z) *
      finiteZetaDenominator F v χ z
  rw [add_mul, div_mul_cancel₀ _ hd]
  rfl

/-- The convergent finite zeta integral is additive in the local test. -/
theorem finiteZetaIntegral_add (μ : Measure (K F v)ˣ) [μ.IsHaarMeasure]
    (χ : LocalPhase F v) (f g : locallyConstantTests (K F v)) (z : ℂ) (hz : 0 < z.re) :
    finiteZetaIntegral F v μ χ (f + g) z =
      finiteZetaIntegral F v μ χ f z + finiteZetaIntegral F v μ χ g z := by
  unfold finiteZetaIntegral
  rw [← integral_add (finiteZetaContinuation_eq_integral F v μ χ f z hz).1
    (finiteZetaContinuation_eq_integral F v μ χ g z hz).1]
  apply integral_congr_ae
  exact Eventually.of_forall fun _ => by simp only [Submodule.coe_add, Pi.add_apply, add_mul]

omit [BorelSpace (K F v)ˣ] in
/-- The finite zeta integral respects scalar multiplication of local tests. -/
theorem finiteZetaIntegral_smul (μ : Measure (K F v)ˣ)
    (χ : LocalPhase F v) (c : ℂ) (f : locallyConstantTests (K F v)) (z : ℂ) :
    finiteZetaIntegral F v μ χ (c • f) z = c * finiteZetaIntegral F v μ χ f z := by
  unfold finiteZetaIntegral
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall fun _ => by simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]

private theorem positiveRealPart_eventually : ∀ᶠ z : ℂ in 𝓝 (1 : ℂ), 0 < z.re :=
  (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by simp)

private theorem finiteZetaCleared_add (μ : Measure (K F v)ˣ) [μ.IsHaarMeasure]
    (χ : LocalPhase F v) (f g : locallyConstantTests (K F v)) :
    finiteZetaCleared F v μ χ (f + g) = finiteZetaCleared F v μ χ f + finiteZetaCleared F v μ χ g := by
  apply (finiteZetaCleared_analytic F v μ χ (f + g)).eq_of_eventuallyEq
    ((finiteZetaCleared_analytic F v μ χ f).add (finiteZetaCleared_analytic F v μ χ g))
  filter_upwards [positiveRealPart_eventually] with z hz
  change finiteZetaCleared F v μ χ (f + g) z =
    finiteZetaCleared F v μ χ f z + finiteZetaCleared F v μ χ g z
  rw [finiteZetaCleared_eq F v μ χ _ z hz, finiteZetaCleared_eq F v μ χ f z hz,
    finiteZetaCleared_eq F v μ χ g z hz, finiteZetaIntegral_add F v μ χ f g z hz, add_mul]

private theorem finiteZetaCleared_smul (μ : Measure (K F v)ˣ) [μ.IsHaarMeasure]
    (χ : LocalPhase F v) (c : ℂ) (f : locallyConstantTests (K F v)) :
    finiteZetaCleared F v μ χ (c • f) = fun z => c * finiteZetaCleared F v μ χ f z := by
  apply (finiteZetaCleared_analytic F v μ χ (c • f)).eq_of_eventuallyEq
    (analyticOnNhd_const.mul (finiteZetaCleared_analytic F v μ χ f))
  filter_upwards [positiveRealPart_eventually] with z hz
  change finiteZetaCleared F v μ χ (c • f) z = c * finiteZetaCleared F v μ χ f z
  rw [finiteZetaCleared_eq F v μ χ _ z hz, finiteZetaCleared_eq F v μ χ f z hz,
    finiteZetaIntegral_smul F v μ χ c f z, mul_assoc]

/-- Multiplying by the common analytic denominator gives an entire
distribution family, where analyticity is tested against Schwartz–Bruhat
functions. The dual consists of continuous linear functionals for the
finest locally convex topology of the local test space. -/
def finiteZetaClearedDistribution (μ : Measure (K F v)ˣ) [μ.IsHaarMeasure]
    (χ : LocalPhase F v) (z : ℂ) :
    letI : TopologicalSpace (locallyConstantTests (K F v)) := finestLocallyConvexTopology _
    locallyConstantTests (K F v) →L[ℂ] ℂ := by
  letI : TopologicalSpace (locallyConstantTests (K F v)) := finestLocallyConvexTopology _
  let L : locallyConstantTests (K F v) →ₗ[ℂ] ℂ :=
    { toFun := fun f => finiteZetaCleared F v μ χ f z
      map_add' := fun f g => congrFun (finiteZetaCleared_add F v μ χ f g) z
      map_smul' := fun c f => congrFun (finiteZetaCleared_smul F v μ χ c f) z }
  exact ⟨L, finest_linear_continuous L⟩

/-- The cleared local functional agrees with the denominator times the
original integral throughout its half-plane of absolute convergence. -/
theorem finiteZetaClearedDistribution_eq_mul_integral (μ : Measure (K F v)ˣ) [μ.IsHaarMeasure]
    (χ : LocalPhase F v) (f : locallyConstantTests (K F v)) (z : ℂ) (hz : 0 < z.re) :
    letI : TopologicalSpace (locallyConstantTests (K F v)) := finestLocallyConvexTopology _
    finiteZetaClearedDistribution F v μ χ z f =
      finiteZetaIntegral F v μ χ f z * finiteZetaDenominator F v χ z :=
  finiteZetaCleared_eq F v μ χ f z hz

/-- Clearing the denominator of an unramified padding factor gives the
same constant on the whole plane, including the Euler zeros. -/
theorem finiteZetaClearedDistribution_integerRing_unramified
    (μ : Measure (K F v)ˣ) [μ.IsHaarMeasure] (χ : LocalPhase F v)
    (hχ : finiteZetaUnramified F v χ) (z : ℂ) :
    letI : TopologicalSpace (locallyConstantTests (K F v)) := finestLocallyConvexTopology _
    finiteZetaClearedDistribution F v μ χ z (finiteCompletionIntegerRingTest F v) =
      (μ.real (finitePlaceIntegralUnits F v) : ℂ) := by
  let f := finiteCompletionIntegerRingTest F v
  let C : ℂ := μ.real (finitePlaceIntegralUnits F v)
  change finiteZetaCleared F v μ χ f z = C
  have he : finiteZetaCleared F v μ χ f = fun _ ↦ C := by
    apply (finiteZetaCleared_analytic F v μ χ f).eq_of_eventuallyEq
      analyticOnNhd_const (z₀ := (1 : ℂ))
    have hpos : ∀ᶠ w : ℂ in 𝓝 (1 : ℂ), 0 < w.re :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    filter_upwards [hpos] with w hw
    rw [finiteZetaCleared_eq F v μ χ f w hw,
      finiteZetaIntegral_integerRing_unramified F v μ χ hχ w hw]
    change (C * (finiteZetaDenominator F v χ w)⁻¹) * finiteZetaDenominator F v χ w = C
    rw [mul_assoc, inv_mul_cancel₀ (finiteZetaDenominator_ne_zero_of_pos F v χ w hw), mul_one]
  exact congrFun he z

/-- The real exponential multipliers used by radial translations in the
Mellin variable. -/
def mellinExponentialMonoid : Submonoid (ℂ → ℂ) where
  carrier := Set.range fun t : ℝ => fun z : ℂ => Complex.exp ((t : ℂ) * z)
  one_mem' := ⟨0, by ext z; simp⟩
  mul_mem' := by
    rintro _ _ ⟨s, rfl⟩ ⟨t, rfl⟩
    refine ⟨s + t, funext fun z => ?_⟩
    simp [add_mul, Complex.exp_add]

/-- Finite linear combinations of real exponential Mellin multipliers. -/
def mellinExponentialAlgebra : Subalgebra ℂ (ℂ → ℂ) :=
  Algebra.adjoin ℂ (mellinExponentialMonoid : Set (ℂ → ℂ))

theorem mellinExponentialAlgebra_toSubmodule :
    mellinExponentialAlgebra.toSubmodule =
      Submodule.span ℂ (mellinExponentialMonoid : Set (ℂ → ℂ)) := by
  rw [mellinExponentialAlgebra, Algebra.adjoin_eq_span, Submonoid.closure_eq]

omit [MeasurableSpace (K F v)ˣ] [BorelSpace (K F v)ˣ] in
private theorem finiteZetaRatio_zpow_mem_exponentialAlgebra (χ : LocalPhase F v) (n : ℤ) :
    (fun z => finiteZetaRatio F v χ z ^ n) ∈ mellinExponentialAlgebra := by
  let t : ℝ := -(n : ℝ) * Real.log (v.asIdeal.absNorm : ℝ)
  have hmem : (fun z : ℂ => Complex.exp ((t : ℂ) * z)) ∈ mellinExponentialAlgebra :=
    Algebra.subset_adjoin (⟨t, rfl⟩ : _ ∈ (mellinExponentialMonoid : Set (ℂ → ℂ)))
  have he : (fun z => finiteZetaRatio F v χ z ^ n) =
      ((χ (chosenFiniteUniformizer F v) : ℂ) ^ n) • (fun z : ℂ => Complex.exp ((t : ℂ) * z)) := by
    funext z
    rw [finiteZetaRatio, mul_zpow, ← Complex.exp_int_mul]
    change _ = _ * Complex.exp ((t : ℂ) * z)
    congr 2
    dsimp [t]
    push_cast
    ring
  rw [he]
  exact mellinExponentialAlgebra.smul_mem hmem _

/-- After the unramified Euler denominators are cleared, a finite-place
zeta test contributes a finite linear combination of real exponentials. -/
theorem finiteZeta_localCleared_mem_exponentialAlgebra (μ : Measure (K F v)ˣ) [μ.IsHaarMeasure]
    (χ : LocalPhase F v) (f : locallyConstantTests (K F v)) :
    (letI : TopologicalSpace (locallyConstantTests (K F v)) := finestLocallyConvexTopology _
     fun z => if finiteZetaUnramified F v χ then finiteZetaClearedDistribution F v μ χ z f
       else finiteZetaContinuation F v μ χ f z) ∈ mellinExponentialAlgebra := by
  let E := mellinExponentialAlgebra
  have hP : finiteZetaRegularPart F v μ χ f ∈ E := by
    have he : finiteZetaRegularPart F v μ χ f =
        ∑ n ∈ Finset.Ico (finiteZetaLower F v f) (finiteZetaTail F v f : ℤ),
          finiteZetaCoeff F v μ χ f n • (fun z => finiteZetaRatio F v χ z ^ n) := by
      funext z
      simp only [finiteZetaRegularPart, Finset.sum_apply]
      rfl
    rw [he]
    exact E.sum_mem fun n _ => E.smul_mem (finiteZetaRatio_zpow_mem_exponentialAlgebra F v χ n) _
  by_cases h : finiteZetaUnramified F v χ
  · simp only [ite_eq_left h]
    change finiteZetaRegularPart F v μ χ f * finiteZetaDenominator F v χ +
      finiteZetaNumerator F v μ χ f ∈ E
    have hD : finiteZetaDenominator F v χ ∈ E := by
      change 1 - (fun z => finiteZetaRatio F v χ z) ∈ E
      exact E.sub_mem E.one_mem (by simpa only [zpow_one] using
        finiteZetaRatio_zpow_mem_exponentialAlgebra F v χ 1)
    have hN : finiteZetaNumerator F v μ χ f ∈ E := by
      change (f.val 0 * finiteZetaUnitAverage F v μ χ) •
        (fun z => finiteZetaRatio F v χ z ^ finiteZetaTail F v f) ∈ E
      exact E.smul_mem (by simpa only [zpow_natCast] using
        finiteZetaRatio_zpow_mem_exponentialAlgebra F v χ (finiteZetaTail F v f : ℤ)) _
    exact E.add_mem (E.mul_mem hP hD) hN
  · have hzero : finiteZetaUnitAverage F v μ χ = 0 := by
      rw [finiteZetaUnitAverage_eq F v μ χ, ite_eq_right h]
    have he : finiteZetaContinuation F v μ χ f = finiteZetaRegularPart F v μ χ f := by
      funext z
      simp only [finiteZetaContinuation, finiteZetaExpansion, finiteZetaRegularPart,
        hzero, mul_zero, zero_mul, add_zero]
    simpa only [ite_eq_right h, he] using hP

/-- The finite Laurent polynomial remaining after clearing the unramified
Euler denominator is uniformly bounded on a closed vertical strip. -/
theorem finiteZeta_localCleared_norm_le_on_strip (μ : Measure (K F v)ˣ) [μ.IsHaarMeasure]
    (χ : LocalPhase F v) (f : locallyConstantTests (K F v)) (a b : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, z.re ∈ Icc a b →
      (letI : TopologicalSpace (locallyConstantTests (K F v)) := finestLocallyConvexTopology _
       ‖if finiteZetaUnramified F v χ then finiteZetaClearedDistribution F v μ χ z f
        else finiteZetaContinuation F v μ χ f z‖) ≤ C := by
  let ρ (t : ℝ) := Real.exp (-t * Real.log (v.asIdeal.absNorm : ℝ))
  let m := min (ρ a) (ρ b)
  let M := max (ρ a) (ρ b)
  let A : Set ℂ := norm ⁻¹' Icc m M
  have hm : 0 < m := lt_min (Real.exp_pos _) (Real.exp_pos _)
  have hA : IsCompact A := by
    have he : A = Metric.closedBall 0 M ∩ (Metric.ball 0 m)ᶜ := by
      ext w
      simp only [A, mem_preimage, mem_Icc, mem_inter_iff, Metric.mem_closedBall, dist_zero_right,
        mem_compl_iff, Metric.mem_ball, not_lt, and_comm]
    rw [he]
    exact (isCompact_closedBall _ _).inter_right Metric.isOpen_ball.isClosed_compl
  let P (w : ℂ) := ∑ n ∈ Finset.Ico (finiteZetaLower F v f) (finiteZetaTail F v f : ℤ),
    finiteZetaCoeff F v μ χ f n * w ^ n
  let N (w : ℂ) := f.val 0 * finiteZetaUnitAverage F v μ χ * w ^ finiteZetaTail F v f
  let Q (w : ℂ) := if finiteZetaUnramified F v χ then P w * (1 - w) + N w else P w
  have hP : ContinuousOn P A := by
    apply continuousOn_finsetSum _ fun n _ ↦ continuousOn_const.mul ?_
    apply continuousOn_id.zpow₀
    intro w hw
    left
    exact norm_pos_iff.mp (hm.trans_le hw.1)
  have hN : Continuous N := by dsimp [N]; fun_prop
  have hQ : ContinuousOn Q A := by
    by_cases h : finiteZetaUnramified F v χ
    · have hW : ContinuousOn (fun w : ℂ ↦ 1 - w) A :=
        (continuous_const.sub continuous_id).continuousOn
      simpa only [Q, ite_eq_left h] using (hP.fun_mul hW).fun_add hN.continuousOn
    · simpa only [Q, ite_eq_right h] using hP
  obtain ⟨B, hB⟩ := (hA.image_of_continuousOn hQ.norm).bddAbove
  refine ⟨max B 0, le_max_right _ _, fun z hz ↦ ?_⟩
  have hn : ‖finiteZetaRatio F v χ z‖ = ρ z.re := by
    simp only [finiteZetaRatio, ρ, norm_mul, Circle.norm_coe, one_mul, Complex.norm_exp,
      Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  have hzA : finiteZetaRatio F v χ z ∈ A := by
    change ‖finiteZetaRatio F v χ z‖ ∈ Icc m M
    rw [hn]
    have hx : -z.re * Real.log (v.asIdeal.absNorm : ℝ) ∈
        Icc (min (-a * Real.log (v.asIdeal.absNorm : ℝ)) (-b * Real.log (v.asIdeal.absNorm : ℝ)))
          (max (-a * Real.log (v.asIdeal.absNorm : ℝ)) (-b * Real.log (v.asIdeal.absNorm : ℝ))) := by
      rcases le_total (Real.log (v.asIdeal.absNorm : ℝ)) 0 with h | h
      · exact ⟨(min_le_left _ _).trans (mul_le_mul_of_nonpos_right (neg_le_neg hz.1) h),
          (mul_le_mul_of_nonpos_right (neg_le_neg hz.2) h).trans (le_max_right _ _)⟩
      · exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonneg_right (neg_le_neg hz.2) h),
          (mul_le_mul_of_nonneg_right (neg_le_neg hz.1) h).trans (le_max_left _ _)⟩
    exact ⟨by simpa only [m, ρ, Real.exp_monotone.map_min] using Real.exp_le_exp.mpr hx.1,
      by simpa only [M, ρ, Real.exp_monotone.map_max] using Real.exp_le_exp.mpr hx.2⟩
  have hbound : ‖Q (finiteZetaRatio F v χ z)‖ ≤ max B 0 :=
    (hB (mem_image_of_mem _ hzA)).trans (le_max_left _ _)
  by_cases h : finiteZetaUnramified F v χ
  · rw [ite_eq_left h]
    change ‖finiteZetaCleared F v μ χ f z‖ ≤ _
    simpa only [Q, P, N, ite_eq_left h, finiteZetaCleared, finiteZetaRegularPart,
      finiteZetaDenominator, finiteZetaNumerator] using hbound
  · have hzero : finiteZetaUnitAverage F v μ χ = 0 := by
      rw [finiteZetaUnitAverage_eq F v μ χ, ite_eq_right h]
    simpa only [Q, P, ite_eq_right h, finiteZetaContinuation, finiteZetaExpansion,
      hzero, mul_zero, zero_mul, add_zero] using hbound

theorem finiteZetaClearedDistribution_analytic (μ : Measure (K F v)ˣ) [μ.IsHaarMeasure]
    (χ : LocalPhase F v) (f : locallyConstantTests (K F v)) :
    letI : TopologicalSpace (locallyConstantTests (K F v)) := finestLocallyConvexTopology _
    AnalyticOnNhd ℂ (fun z => finiteZetaClearedDistribution F v μ χ z f) univ :=
  finiteZetaCleared_analytic F v μ χ f

set_option backward.isDefEq.respectTransparency false in
/-- Pole clearing gives weak holomorphy on the actual strong dual. Every continuous
linear functional on that dual is evaluation at a test. -/
theorem finiteZetaClearedDistribution_weak_analytic (μ : Measure (K F v)ˣ) [μ.IsHaarMeasure]
    (χ : LocalPhase F v) :
    letI : TopologicalSpace (locallyConstantTests (K F v)) := finestLocallyConvexTopology _
    ∀ ℓ : StrongDual ℂ (StrongDual ℂ (locallyConstantTests (K F v))),
      AnalyticOnNhd ℂ (fun z => ℓ (finiteZetaClearedDistribution F v μ χ z)) univ := by
  let E := ↥(locallyConstantTests (K F v))
  letI : TopologicalSpace E := finestLocallyConvexTopology E
  let W := finest_withSeminorms E
  letI : IsTopologicalAddGroup E := W.topologicalAddGroup
  letI : ContinuousSMul ℂ E := W.continuousSMul
  letI : PolynormableSpace ℂ E := W.toPolynormableSpace
  let D := StrongDual ℂ E
  letI : TopologicalSpace D :=
    ContinuousLinearMap.topologicalSpace (σ := RingHom.id ℂ) (E := E) (F := ℂ)
  letI : IsTopologicalAddGroup D :=
    ContinuousLinearMap.topologicalAddGroup (σ := RingHom.id ℂ) (E := E) (F := ℂ)
  letI : TopologicalSpace (StrongDual ℂ D) :=
    ContinuousLinearMap.topologicalSpace (σ := RingHom.id ℂ) (E := D) (F := ℂ)
  intro ℓ
  let b := Module.Free.chooseBasis ℂ E
  let e := finest_strongBidual b
  obtain ⟨f, hf⟩ := e.toLinearEquiv.surjective ℓ
  have he (z : ℂ) : ℓ (finiteZetaClearedDistribution F v μ χ z) =
      finiteZetaClearedDistribution F v μ χ z f := by
    rw [← hf]
    exact finest_strongBidual_apply b f _
  simpa only [he] using finiteZetaClearedDistribution_analytic F v μ χ f

/-- The hat on the test in (3.3.2.23) would give a nonzero residue for this
test. Its Fourier value at the trivial additive character is its additive
integral, whereas the test vanishes at zero and its zeta continuation is regular. -/
theorem finiteZetaContinuation_fourierValue_obstruction
    (μ : Measure (K F v)ˣ) [μ.IsHaarMeasure] [MeasurableSpace (K F v)] [BorelSpace (K F v)]
    (ν : Measure (K F v)) [ν.IsAddHaarMeasure] :
    ∃ f : locallyConstantTests (K F v),
      (∫ x, f.val x ∂ν) ≠ 0 ∧
      AnalyticAt ℂ (finiteZetaContinuation F v μ 1 f) 0 := by
  classical
  let B := Metric.ball (1 : K F v) 1
  have hO : IsCompact (Metric.closedBall (1 : K F v) 1) := by
    rw [IsUltrametricDist.closedBall_eq_of_mem
      (show (0 : K F v) ∈ Metric.closedBall (1 : K F v) 1 by simp),
      finiteCompletion_closedBall]
    exact finitePlaceIntegral_compact F v
  have hBc : IsCompact B := hO.of_isClosed_subset (IsUltrametricDist.isClosed_ball _ _)
    Metric.ball_subset_closedBall
  have hBo : IsOpen B := Metric.isOpen_ball
  let f := compactOpenIndicator (K F v) ⟨B, hBc, hBo⟩
  have h₀ : (0 : K F v) ∉ B := by simp [B]
  have hf₀ : f.val 0 = 0 := by
    change B.indicator (fun _ => (1 : ℂ)) 0 = 0
    exact Set.indicator_of_notMem h₀ _
  have hBpos : ν B ≠ 0 := hBo.measure_ne_zero ν ⟨1, Metric.mem_ball_self zero_lt_one⟩
  refine ⟨f, ?_, (finiteZetaContinuation_poles F v μ 1 f 0).2 (by simp [hf₀])⟩
  change (∫ x, B.indicator (fun _ => (1 : ℂ)) x ∂ν) ≠ 0
  rw [integral_indicator_const (μ := ν) _ hBo.measurableSet, Complex.real_smul, mul_one]
  exact Complex.ofReal_ne_zero.mpr (ENNReal.toReal_ne_zero.mpr ⟨hBpos, hBc.measure_ne_top⟩)


theorem finiteZetaClearedDistribution_recovers (μ : Measure (K F v)ˣ) [μ.IsHaarMeasure]
    (χ : LocalPhase F v) (z : ℂ) (hz : finiteZetaRatio F v χ z ≠ 1)
    (f : locallyConstantTests (K F v)) :
    letI : TopologicalSpace (locallyConstantTests (K F v)) := finestLocallyConvexTopology _
    finiteZetaClearedDistribution F v μ χ z f / (1 - finiteZetaRatio F v χ z) =
      finiteZetaContinuation F v μ χ f z := by
  change finiteZetaCleared F v μ χ f z / finiteZetaDenominator F v χ z = _
  have hd : finiteZetaDenominator F v χ z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz)
  rw [finiteZetaContinuation_decomp, finiteZetaCleared, add_div, mul_div_cancel_right₀ _ hd]

/-- Lemma 3.3.2.2, pole location and order. As a family of distributions,
the local zeta function has a simple pole at the trivial quasi-character.
The indicator of the integer ring witnesses that the pole is present. -/
theorem finiteZetaContinuation_distribution_pole_iff (μ : Measure (K F v)ˣ) [μ.IsHaarMeasure]
    (χ : LocalPhase F v) (z : ℂ) :
    (∃ f : locallyConstantTests (K F v),
      meromorphicOrderAt (finiteZetaContinuation F v μ χ f) z = (-1 : WithTop ℤ)) ↔
      ∀ u : (K F v)ˣ, ((χ u : Circle) : ℂ) * finiteZetaWeight F v z u = 1 := by
  rw [finiteZetaTwist_trivial_iff]
  constructor
  · rintro ⟨f, hf⟩
    exact ((finiteZetaContinuation_poles F v μ χ f z).1.mp hf).2
  · rintro ⟨hχ, hz⟩
    let O : Set (K F v) := v.adicCompletionIntegers F
    let f := compactOpenIndicator (K F v) ⟨O, finitePlaceIntegral_compact F v,
      Valued.isOpen_valuationSubring (K F v)⟩
    have h0 : f.val 0 = 1 := by
      change O.indicator (fun _ : K F v => (1 : ℂ)) 0 = 1
      exact Set.indicator_of_mem (show (0 : K F v) ∈ O from zero_mem (v.adicCompletionIntegers F)) _
    exact ⟨f, (finiteZetaContinuation_poles F v μ χ f z).1.mpr
      ⟨h0 ▸ one_ne_zero, hχ, hz⟩⟩


omit [BorelSpace (K F v)ˣ] in
/-- The finite zeta continuation as a function of the actual local
quasi-character. Its value is independent of the chosen lift. -/
def finiteZetaQuasiContinuation (μ : Measure (K F v)ˣ)
    (f : locallyConstantTests (K F v)) (ψ : (K F v)ˣ →ₜ* ℂ) : ℂ :=
  let h := finiteZeta_represents_quasiCharacter F v ψ
  finiteZetaContinuation F v μ h.choose f h.choose_spec.choose

theorem finiteZetaQuasiContinuation_of_twist (μ : Measure (K F v)ˣ)
    (f : locallyConstantTests (K F v)) (ψ : (K F v)ˣ →ₜ* ℂ)
    (χ : LocalPhase F v) (z : ℂ)
    (he : ∀ u, ψ u = ((χ u : Circle) : ℂ) * finiteZetaWeight F v z u) :
    finiteZetaQuasiContinuation F v μ f ψ = finiteZetaContinuation F v μ χ f z := by
  let h := finiteZeta_represents_quasiCharacter F v ψ
  exact finiteZetaContinuation_eq_of_twist_eq F v μ h.choose χ f h.choose_spec.choose z
    (fun u => ((h.choose_spec.choose_spec.2.1) u).symm.trans (he u))

/-- On the convergence half-plane of the actual quasi-character, the
continuation agrees with the absolutely convergent zeta integral. -/
theorem finiteZetaQuasiContinuation_eq_integral (μ : Measure (K F v)ˣ) [μ.IsHaarMeasure]
    (f : locallyConstantTests (K F v)) (ψ : (K F v)ˣ →ₜ* ℂ)
    (hψ : ‖ψ (chosenFiniteUniformizer F v)‖ < 1) :
    Integrable (fun u : (K F v)ˣ => f.val u.val * ψ u) μ ∧
      (∫ u, f.val u.val * ψ u ∂μ) = finiteZetaQuasiContinuation F v μ f ψ := by
  obtain ⟨χ, z, _, he, hz⟩ := finiteZeta_represents_quasiCharacter F v ψ
  have h := finiteZetaContinuation_eq_integral F v μ χ f z (hz.mpr hψ)
  rw [finiteZetaQuasiContinuation_of_twist F v μ f ψ χ z he]
  simp_rw [he, ← mul_assoc]
  exact h

theorem finiteZetaIntegral_translate (μ : Measure (K F v)ˣ) [μ.IsHaarMeasure]
    (χ : LocalPhase F v) (z : ℂ) (r : (K F v)ˣ) (f : locallyConstantTests (K F v)) :
    finiteZetaIntegral F v μ χ (locallyConstantTestTranslate (K F v) r f) z =
      ((χ r : ℂ) * finiteZetaWeight F v z r) * finiteZetaIntegral F v μ χ f z := by
  unfold finiteZetaIntegral
  rw [← integral_const_mul]
  conv_lhs => rw [← integral_mul_left_eq_self _ r]
  apply integral_congr_ae
  filter_upwards with u
  change f.val ((r⁻¹ * (r * u)).val) * (χ (r * u) : ℂ) * finiteZetaWeight F v z (r * u) =
    ((χ r : ℂ) * finiteZetaWeight F v z r) * (f.val u.val * (χ u : ℂ) * finiteZetaWeight F v z u)
  rw [inv_mul_cancel_left, map_mul, Circle.coe_mul, finiteZetaWeight_mul]
  ring

omit [MeasurableSpace (K F v)ˣ] [BorelSpace (K F v)ˣ] in
private theorem finiteZetaUnramified_iff_unit_twist (χ : LocalPhase F v) (z : ℂ) :
    (∀ a : principalIntegralUnits F v,
      (χ a.val : ℂ) * finiteZetaWeight F v z a.val = 1) ↔ finiteZetaUnramified F v χ := by
  have hnorm (a : principalIntegralUnits F v) : ‖a.val.val‖ = 1 := a.property
  have hmem (a : (K F v)ˣ) : a ∈ U F v ↔ a ∈ principalIntegralUnits F v := by
    change a ∈ finitePlaceIntegralUnits F v ↔ _
    rw [← finiteZetaShell_zero]
    change ‖a.val‖ = (v.asIdeal.absNorm : ℝ) ^ (-(0 : ℤ)) ↔ ‖a.val‖ = 1
    simp
  have hw (a : principalIntegralUnits F v) : finiteZetaWeight F v z a.val = 1 := by
    simp [finiteZetaWeight, hnorm a]
  constructor
  · intro h a ha
    let u : principalIntegralUnits F v := ⟨a, (hmem a).mp ha⟩
    have hu := h u
    rw [hw u, mul_one] at hu
    exact Circle.coe_injective (hu.trans Circle.coe_one.symm)
  · intro h a
    rw [hw a, mul_one, h _ ((hmem a.val).mpr a.property), Circle.coe_one]

/-- The local zeta factor contributed by Weil's principal-value operator. -/
noncomputable def finiteZetaWeilMultiplier (χ : LocalPhase F v) (z : ℂ) : ℂ :=
  if finiteZetaUnramified F v χ then 1 - finiteZetaRatio F v χ z else 1

/-- The local Euler factor in the proof of Lemma 5.3.1.5 follows by a change of
variables in the actual finite-place Tate integral. -/
theorem finiteZetaIntegral_weilPrincipalValue (μ : Measure (K F v)ˣ) [μ.IsHaarMeasure]
    (χ : LocalPhase F v) (f : locallyConstantTests (K F v)) (z : ℂ) (hz : 0 < z.re) :
    finiteZetaIntegral F v μ χ (weilPrincipalValue F v f) z =
      finiteZetaWeilMultiplier F v χ z * finiteZetaIntegral F v μ χ f z := by
  classical
  let L : locallyConstantTests (K F v) →ₗ[ℂ] ℂ :=
    { toFun := fun f => finiteZetaIntegral F v μ χ f z
      map_add' := fun f g => finiteZetaIntegral_add F v μ χ f g z hz
      map_smul' := fun c f => finiteZetaIntegral_smul F v μ χ c f z }
  let c (r : (K F v)ˣ) := (χ r : ℂ) * finiteZetaWeight F v z r
  have h := weilPrincipalValue_eigenfunctional F v L c
    (fun r f => finiteZetaIntegral_translate F v μ χ z r f) f
  have hr : c (chosenFiniteUniformizer F v) = finiteZetaRatio F v χ z := by
    let π := chosenFiniteUniformizer F v
    change (χ π : ℂ) * Complex.exp (z * (Real.log ‖π.val‖ : ℂ)) =
      (χ π : ℂ) * Complex.exp (-z * (Real.log (v.asIdeal.absNorm : ℝ) : ℂ))
    rw [norm_finiteUniformizer F v _ (chosenFiniteUniformizer_spec F v), Real.log_inv,
      Complex.ofReal_neg, mul_neg, neg_mul]
  change finiteZetaIntegral F v μ χ (weilPrincipalValue F v f) z =
    (if finiteZetaUnramified F v χ then 1 - finiteZetaRatio F v χ z else 1) *
      finiteZetaIntegral F v μ χ f z
  simpa only [L, LinearMap.coe_mk, AddHom.coe_mk, c, hr,
    finiteZetaUnramified_iff_unit_twist F v χ z] using h

omit [MeasurableSpace (K F v)ˣ] [BorelSpace (K F v)ˣ] in
/-- The local principal-value multiplier is entire. -/
theorem finiteZetaWeilMultiplier_analytic (χ : LocalPhase F v) :
    AnalyticOnNhd ℂ (finiteZetaWeilMultiplier F v χ) univ := by
  classical
  intro z _
  by_cases h : finiteZetaUnramified F v χ
  · have he : finiteZetaWeilMultiplier F v χ = finiteZetaDenominator F v χ := by
      funext w
      exact ite_eq_left h
    rw [he]
    exact finiteZetaDenominator_analytic F v χ z
  · have he : finiteZetaWeilMultiplier F v χ = fun _ => (1 : ℂ) := by
      funext w
      exact ite_eq_right h
    rw [he]
    exact analyticAt_const

private theorem finiteZetaCleared_weilPrincipalValue (μ : Measure (K F v)ˣ) [μ.IsHaarMeasure]
    (χ : LocalPhase F v) (f : locallyConstantTests (K F v)) :
    finiteZetaCleared F v μ χ (weilPrincipalValue F v f) =
      fun z => finiteZetaWeilMultiplier F v χ z * finiteZetaCleared F v μ χ f z := by
  apply (finiteZetaCleared_analytic F v μ χ _).eq_of_eventuallyEq
    ((finiteZetaWeilMultiplier_analytic F v χ).mul (finiteZetaCleared_analytic F v μ χ f))
  filter_upwards [positiveRealPart_eventually] with z hz
  change finiteZetaCleared F v μ χ (weilPrincipalValue F v f) z =
    finiteZetaWeilMultiplier F v χ z * finiteZetaCleared F v μ χ f z
  rw [finiteZetaCleared_eq F v μ χ _ z hz, finiteZetaCleared_eq F v μ χ f z hz,
    finiteZetaIntegral_weilPrincipalValue F v μ χ f z hz, mul_assoc]

/-- The factor identity extends to the local meromorphic continuation wherever
the common denominator is nonzero. -/
theorem finiteZetaContinuation_weilPrincipalValue (μ : Measure (K F v)ˣ) [μ.IsHaarMeasure]
    (χ : LocalPhase F v) (f : locallyConstantTests (K F v)) (z : ℂ)
    (hz : finiteZetaRatio F v χ z ≠ 1) :
    finiteZetaContinuation F v μ χ (weilPrincipalValue F v f) z =
      finiteZetaWeilMultiplier F v χ z * finiteZetaContinuation F v μ χ f z := by
  have hd : finiteZetaDenominator F v χ z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz)
  rw [← mul_left_inj' hd]
  have hmul (g : locallyConstantTests (K F v)) :
      finiteZetaContinuation F v μ χ g z * finiteZetaDenominator F v χ z =
        finiteZetaCleared F v μ χ g z := by
    rw [finiteZetaContinuation_decomp, finiteZetaCleared, add_mul, div_mul_cancel₀ _ hd]
  rw [hmul, mul_assoc, hmul, finiteZetaCleared_weilPrincipalValue]

/-- The multiplier formula holds as an equality of meromorphic functions,
including in punctured neighborhoods of the zeros of the local denominator. -/
theorem finiteZetaContinuation_weilPrincipalValue_meromorphic (μ : Measure (K F v)ˣ)
    [μ.IsHaarMeasure] (χ : LocalPhase F v) (f : locallyConstantTests (K F v)) :
    finiteZetaContinuation F v μ χ (weilPrincipalValue F v f) =ᶠ[Filter.codiscrete ℂ]
      fun z => finiteZetaWeilMultiplier F v χ z * finiteZetaContinuation F v μ χ f z := by
  have ha : AnalyticOnNhd ℂ (finiteZetaDenominator F v χ) univ :=
    fun z _ => finiteZetaDenominator_analytic F v χ z
  have hne : ¬ EqOn (finiteZetaDenominator F v χ) 0 univ := by
    intro h
    have hD : finiteZetaDenominator F v χ 1 = 0 := h (mem_univ 1)
    have hR : finiteZetaRatio F v χ 1 = 1 := (sub_eq_zero.mp hD).symm
    have hn := finiteZetaRatio_norm_lt_one F v χ 1 (by simp)
    simp [hR] at hn
  have hd := (ha.eqOn_zero_or_eventually_ne_zero_of_preconnected isPreconnected_univ).resolve_left hne
  filter_upwards [hd] with z hz
  exact finiteZetaContinuation_weilPrincipalValue F v μ χ f z
    (fun hr => hz (sub_eq_zero.mpr hr.symm))

/-- Applying the local principal-value operator removes the pole, since the
resulting test vanishes at the origin. -/
theorem finiteZetaContinuation_weilPrincipalValue_entire (μ : Measure (K F v)ˣ)
    [μ.IsHaarMeasure] (χ : LocalPhase F v) (f : locallyConstantTests (K F v)) :
    AnalyticOnNhd ℂ (finiteZetaContinuation F v μ χ (weilPrincipalValue F v f)) univ := by
  intro z _
  have h0 : weilPrincipalValue F v f ∈
      {g : locallyConstantTests (K F v) | g.val 0 = 0} := by
    rw [← weilPrincipalValue_range]
    exact mem_range_self f
  exact (finiteZetaContinuation_poles F v μ χ (weilPrincipalValue F v f) z).2
    (fun h => h.1 h0)


end

end Masullo
