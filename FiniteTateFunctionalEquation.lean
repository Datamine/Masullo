import FiniteLogFourierHaar
import FiniteLocalZeta
import FiniteMellinShellTest
import SLocalFiniteZeta
import UnitHaarDensity
import MellinFourierCrossProduct

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped ComplexConjugate ENNReal NNReal NumberField

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

private abbrev K := v.adicCompletion F
private abbrev E := locallyConstantTests (K F v)
private abbrev G := (K F v)ˣ

variable [∀ w : HeightOneSpectrum (𝓞 F), MeasurableSpace (w.adicCompletion F)]
  [∀ w : HeightOneSpectrum (𝓞 F), BorelSpace (w.adicCompletion F)]
  [MeasurableSpace (G F v)] [BorelSpace (G F v)]

private abbrev η := additiveHaarDifferent F v
local instance : (η F v).IsAddHaarMeasure := additiveHaarDifferent_isHaar F v
private abbrev T := finitePlaceFourierTest F v (η F v)

omit [MeasurableSpace (G F v)] [BorelSpace (G F v)] in
private theorem finiteTraceFourier_pairing (a : K F v) (f g : E F v) :
    (∫ x, f.val x * (T F v g).val (a * x) ∂η F v) =
      ∫ x, g.val x * (T F v f).val (a * x) ∂η F v := by
  letI : LocallyCompactSpace (K F v) := finitePlace_locallyCompact F v
  letI : SecondCountableTopology (K F v) := finitePlace_secondCountable F v
  letI : BorelSpace (K F v × K F v) := inferInstance
  let P (x y : K F v) := ((finitePlaceTraceCharacter F v (y * (a * x))).toMul : ℂ)
  let H (p : K F v × K F v) := f.val p.1 * g.val p.2 * P p.1 p.2
  have hP : Continuous (fun p : K F v × K F v ↦ P p.1 p.2) :=
    continuous_subtype_val.comp ((finitePlaceTraceCharacter_continuous F v).comp
      (continuous_snd.mul (continuous_const.mul continuous_fst)))
  have hC : Continuous H :=
    ((f.property.1.continuous.comp continuous_fst).mul
      (g.property.1.continuous.comp continuous_snd)).mul hP
  have hF : Integrable f.val (η F v) :=
    f.property.1.continuous.integrable_of_hasCompactSupport f.property.2
  have hG : Integrable g.val (η F v) :=
    g.property.1.continuous.integrable_of_hasCompactSupport g.property.2
  have hH : Integrable H ((η F v).prod (η F v)) := by
    apply (hF.norm.mul_prod hG.norm).mono' hC.aestronglyMeasurable
    exact .of_forall fun p ↦ by
      change ‖f.val p.1 * g.val p.2 * P p.1 p.2‖ ≤ ‖f.val p.1‖ * ‖g.val p.2‖
      rw [norm_mul, norm_mul, show ‖P p.1 p.2‖ = 1 from Circle.norm_coe _, mul_one]
  have he (x y : K F v) : P x y = P y x := by
    unfold P
    rw [show y * (a * x) = x * (a * y) by ring]
  calc
    _ = ∫ x, ∫ y, H (x,y) ∂η F v ∂η F v := by
      apply integral_congr_ae
      exact .of_forall fun x ↦ by
        change f.val x * (∫ y, g.val y * P x y ∂η F v) = ∫ y, H (x,y) ∂η F v
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact .of_forall fun y ↦ (mul_assoc _ _ _).symm
    _ = ∫ y, ∫ x, H (x,y) ∂η F v ∂η F v := integral_integral_swap hH
    _ = _ := by
      apply integral_congr_ae
      exact .of_forall fun y ↦ by
        change (∫ x, H (x,y) ∂η F v) = g.val y * (∫ x, f.val x * P y x ∂η F v)
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact .of_forall fun x ↦ by
          change f.val x * g.val y * P x y = g.val y * (f.val x * P y x)
          rw [he, mul_comm (f.val x), mul_assoc]

private theorem finiteWeightedUnitHaar (μ : Measure (G F v)) [μ.IsHaarMeasure] :
    ∃ c : ℝ≥0, c ≠ 0 ∧
      Measure.map (Units.val : G F v → K F v)
        (μ.withDensity (fun u ↦ ENNReal.ofReal ‖u.val‖)) = c • η F v := by
  let j : G F v → K F v := Units.val
  have hj : IsOpenEmbedding j := IsOpenUnits.isOpenEmbedding_unitsVal
  letI := finitePlace_locallyCompact F v
  letI := finitePlace_secondCountable F v
  letI := hj.locallyCompactSpace
  letI := hj.isEmbedding.secondCountableTopology
  let d : G F v →* ℝ := normHom.toMonoidHom.comp (Units.coeHom (K F v))
  have hfull : ∀ᵐ x ∂η F v, x ∈ range j := by
    apply ae_iff.mpr
    have hs : {x | ¬ x ∈ range j} = ({0} : Set (K F v)) := by
      ext x
      exact not_congr (show IsUnit x ↔ _ from isUnit_iff_ne_zero) |>.trans not_ne_iff
    rw [hs, finitePlace_measure_singleton_zero]
  have hn : η F v ≠ 0 := fun h ↦
    isOpen_univ.measure_ne_zero (η F v) univ_nonempty (by simp [h])
  refine additiveMeasure_eq_weighted_unitHaar (η F v) hn μ hj hfull d
    (continuous_norm.comp Units.continuous_val) (fun u ↦ norm_pos_iff.mpr u.ne_zero) ?_
  intro u
  rw [finitePlace_map_unit_mul F v (η F v) u, ← Measure.coe_nnreal_smul]
  congr 1
  rw [show d u = ‖u.val‖ from rfl, ← ENNReal.ofReal_inv_of_pos (norm_pos_iff.mpr u.ne_zero),
    ← norm_inv, ← Units.val_inv_eq_inv_val]
  exact (ofReal_norm _).symm

private theorem finite_integral_weightedUnits (μ : Measure (G F v)) (c : ℝ≥0)
    (hc : Measure.map (Units.val : G F v → K F v)
      (μ.withDensity (fun u ↦ ENNReal.ofReal ‖u.val‖)) = c • η F v)
    (h : K F v → ℂ) (hh : Measurable h) :
    (∫ u, (‖u.val‖ : ℂ) * h u.val ∂μ) = (c : ℝ) • ∫ x, h x ∂η F v := by
  change _ = c • ∫ x, h x ∂η F v
  rw [← integral_smul_nnreal_measure, ← hc, integral_map Units.continuous_val.measurable.aemeasurable
    hh.aestronglyMeasurable]
  have he : (fun u : G F v ↦ ENNReal.ofReal ‖u.val‖) =
      fun u ↦ (‖u.val‖₊ : ℝ≥0∞) := funext fun _ ↦ ofReal_norm _
  rw [he, integral_withDensity_eq_integral_smul
    (f := fun u : G F v ↦ ‖u.val‖₊) (continuous_nnnorm.comp Units.continuous_val).measurable]
  rfl

/-- The additive Fourier pairing determines a single local factor on the
critical strip for every finite unitary character. -/
theorem finiteZeta_fourier_crossProduct (μ : Measure (G F v)) [μ.IsHaarMeasure]
    (χ : G F v →ₜ* Circle) (z : ℂ) (hr : 0 < z.re) (hl : z.re < 1) (f g : E F v) :
    finiteZetaIntegral F v μ χ f z * finiteZetaIntegral F v μ χ⁻¹ (T F v g) (1 - z) =
      finiteZetaIntegral F v μ χ g z * finiteZetaIntegral F v μ χ⁻¹ (T F v f) (1 - z) := by
  letI := finitePlace_locallyCompact F v
  letI := finitePlace_secondCountable F v
  let j : G F v → K F v := Units.val
  have hj : IsOpenEmbedding j := IsOpenUnits.isOpenEmbedding_unitsVal
  letI := hj.locallyCompactSpace
  letI := hj.isEmbedding.secondCountableTopology
  let W : G F v →* ℂ :=
    { toFun := fun u ↦ (χ⁻¹ u : ℂ) * finiteZetaWeight F v (1 - z) u
      map_one' := by simp [finiteZetaWeight]
      map_mul' := fun a b ↦ by
        rw [map_mul, Circle.coe_mul, finiteZetaWeight_mul]
        ring }
  let r (a : E F v) (u : G F v) := (‖u.val‖ : ℂ) * a.val u.val
  let l (a : E F v) (u : G F v) := (T F v a).val u.val
  have hw (a : E F v) : (fun u ↦ ((W.toHomUnits u : ℂ)⁻¹) * r a u) =
      (fun u ↦ a.val u.val * (χ u : ℂ) * finiteZetaWeight F v z u) := by
    funext u
    change ((χ⁻¹ u : ℂ) * finiteZetaWeight F v (1 - z) u)⁻¹ *
      ((‖u.val‖ : ℂ) * a.val u.val) = _
    rw [mul_inv, finiteZetaWeight, finiteZetaWeight, ← Complex.exp_neg]
    rw [show (χ⁻¹ u : ℂ) = (χ u : ℂ)⁻¹ from Circle.coe_inv (χ u), inv_inv]
    have he : (‖u.val‖ : ℂ) = Complex.exp (Real.log ‖u.val‖ : ℂ) := by
      rw [← Complex.ofReal_exp, Real.exp_log (norm_pos_iff.mpr u.ne_zero)]
    rw [he]
    calc
      _ = a.val u.val * (χ u : ℂ) *
          (Complex.exp (-((1 - z) * (Real.log ‖u.val‖ : ℂ))) *
            Complex.exp (Real.log ‖u.val‖ : ℂ)) := by ring
      _ = _ := by rw [← Complex.exp_add]; congr 2; ring
  have hv (a : E F v) : (fun u ↦ (W.toHomUnits u : ℂ) * l a u) =
      (fun u ↦ (T F v a).val u.val * (χ⁻¹ u : ℂ) * finiteZetaWeight F v (1 - z) u) := by
    funext u
    change ((χ⁻¹ u : ℂ) * finiteZetaWeight F v (1 - z) u) * l a u = _
    rw [mul_comm, ← mul_assoc]
  have hs : 0 < (1 - z).re := by simpa [Complex.sub_re, sub_pos] using hl
  have hR (a : E F v) : Integrable (fun u ↦ ((W.toHomUnits u : ℂ)⁻¹) * r a u) μ := by
    rw [hw a]
    exact (finiteZetaContinuation_eq_integral F v μ χ a z hr).1
  have hL (a : E F v) : Integrable (fun u ↦ (W.toHomUnits u : ℂ) * l a u) μ := by
    rw [hv a]
    exact (finiteZetaContinuation_eq_integral F v μ χ⁻¹ (T F v a) (1 - z) hs).1
  obtain ⟨c, _, hc⟩ := finiteWeightedUnitHaar F v μ
  have hPair (y : G F v) (a b : E F v) :
      (∫ x, r a x * l b (y*x) ∂μ) =
        (c : ℝ) • ∫ t, a.val t * (T F v b).val (y.val * t) ∂η F v := by
    let h (t : K F v) := a.val t * (T F v b).val (y.val * t)
    have hh : Continuous h := a.property.1.continuous.mul
      ((T F v b).property.1.continuous.comp (continuous_const.mul continuous_id))
    calc
      _ = ∫ x, (‖x.val‖ : ℂ) * h x.val ∂μ :=
        integral_congr_ae (.of_forall fun x ↦ mul_assoc _ _ _)
      _ = _ := finite_integral_weightedUnits F v μ c hc h hh.measurable
  have hp (y : G F v) : (∫ x, r f x * l g (y*x) ∂μ) = ∫ x, r g x * l f (y*x) ∂μ := by
    rw [hPair, hPair, finiteTraceFourier_pairing]
  have h := mellin_fourier_crossProduct μ W.toHomUnits (r f) (r g) (l f) (l g)
    (hR f) (hR g) (hL f) (hL g) hp
  rw [hw f, hw g, hv f, hv g] at h
  exact h

/-- The finite unramified factor for the trivial unitary phase holds on
all locally constant compactly supported tests. -/
theorem finiteZeta_tamagawa_trivialPhase_fourier (μ : Measure (G F v)) [μ.IsHaarMeasure]
    (z : ℂ) (hr : 0 < z.re) (hl : z.re < 1) (f : E F v) :
    let d := multiplicity v.asIdeal (differentIdeal ℤ (𝓞 F))
    let q := (v.asIdeal.absNorm : ℝ)
    let e (w : ℂ) := 1 - Complex.exp (-w * (Real.log q : ℂ))
    e z * finiteZetaIntegral F v μ 1 f z =
      Complex.exp ((d : ℂ) * (z - 1 / 2) * (Real.log q : ℂ)) *
        (e (1 - z) * finiteZetaIntegral F v μ 1 (T F v f) (1 - z)) := by
  intro d q e
  let ε := Complex.exp ((d : ℂ) * (z - 1 / 2) * (Real.log q : ℂ))
  let φ := finiteCompletionIntegerRingTest F v
  let L (a : E F v) := e z * finiteZetaIntegral F v μ 1 a z
  let R (a : E F v) := e (1 - z) * finiteZetaIntegral F v μ 1 (T F v a) (1 - z)
  have hφ : L φ = ε * R φ := by
    simpa only [L, R, ε, φ, e, q, d, T, finitePlaceFourierTest, finiteZetaIntegral,
      show ∀ u : G F v, (1 : G F v →ₜ* Circle) u = 1 from fun _ ↦ rfl,
      Circle.coe_one, mul_one] using finitePlace_tamagawa_unramified_integerRing F v μ z hr hl
  have hL : L φ ≠ 0 := by
    change e z * finiteZetaIntegral F v μ 1 φ z ≠ 0
    rw [finiteZetaIntegral_integerRing_unramified F v μ 1 (fun _ _ ↦ rfl) z hr]
    have hD : e z = finiteZetaDenominator F v 1 z := by
      simp [e, q, finiteZetaDenominator, finiteZetaRatio]
    have hn := finiteZetaDenominator_ne_zero_of_pos F v 1 z hr
    change e z * ((μ.real (finitePlaceIntegralUnits F v) : ℂ) *
      (finiteZetaDenominator F v 1 z)⁻¹) ≠ 0
    rw [hD, mul_left_comm, mul_inv_cancel₀ hn, mul_one]
    exact Complex.ofReal_ne_zero.mpr (finiteZetaUnitMass_pos F v μ).ne'
  have hR : R φ ≠ 0 := fun he ↦ hL (by rw [hφ, he, mul_zero])
  have h := finiteZeta_fourier_crossProduct F v μ 1 z hr hl f φ
  simp only [inv_one] at h
  have hCross : L f * R φ = L φ * R f := by
    dsimp only [L, R]
    linear_combination (e z * e (1 - z)) * h
  change L f = ε * R f
  apply mul_right_cancel₀ hR
  rw [hCross, hφ]
  ring

omit [∀ w : HeightOneSpectrum (𝓞 F), MeasurableSpace (w.adicCompletion F)]
  [∀ w : HeightOneSpectrum (𝓞 F), BorelSpace (w.adicCompletion F)]
  [MeasurableSpace (G F v)] [BorelSpace (G F v)] in
/-- An unramified unitary phase is a purely imaginary shift of the
norm exponent. The reflected phase uses the opposite shift. -/
theorem finiteZetaUnramified_exists_shift (χ : G F v →ₜ* Circle)
    (hχ : finiteZetaUnramified F v χ) :
    ∃ a : ℂ, a.re = 0 ∧
      (∀ u : G F v, finiteZetaWeight F v a u = (χ u : ℂ)) ∧
      (∀ z : ℂ, finiteZetaDenominator F v χ z = finiteZetaDenominator F v 1 (z + a)) := by
  let π := chosenFiniteUniformizer F v
  let q : ℝ := v.asIdeal.absNorm
  let a : ℂ := -Complex.log (χ π : ℂ) / (Real.log q : ℂ)
  have hq : 1 < q := by dsimp [q]; exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hq₀ : (Real.log q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.log_pos hq).ne'
  have ha : a.re = 0 := by
    simp [a, Complex.div_ofReal_re, Complex.log_re, Circle.norm_coe]
  have he : Complex.exp (-a * (Real.log q : ℂ)) = (χ π : ℂ) := by
    rw [show -a * (Real.log q : ℂ) = Complex.log (χ π : ℂ) by
      dsimp [a]; rw [neg_div, neg_neg, div_mul_cancel₀ _ hq₀]]
    exact Complex.exp_log (Circle.coe_ne_zero _)
  refine ⟨a, ha, ?_, ?_⟩
  · intro g
    obtain ⟨n, u, hu, rfl⟩ := finiteZetaShell_repr F v g
    have hn : ‖u.val‖ = 1 := by
      change u ∈ finitePlaceIntegralUnits F v at hu
      have h := (finiteZetaShell_zero F v).symm ▸ hu
      change ‖u.val‖ = (v.asIdeal.absNorm : ℝ) ^ (-(0 : ℤ)) at h
      simpa using h
    rw [finiteZetaWeight_mul, map_mul, Circle.coe_mul, hχ u hu, Circle.coe_one, mul_one]
    change Complex.exp (a * (Real.log ‖(π ^ n).val‖ : ℂ)) *
      Complex.exp (a * (Real.log ‖u.val‖ : ℂ)) = _
    rw [hn, Real.log_one, Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one,
      finitePlaceUniformizer_norm_zpow F v n, Real.log_zpow, Complex.ofReal_mul,
      Complex.ofReal_intCast, Int.cast_neg]
    change Complex.exp (a * (-(n : ℂ) * (Real.log q : ℂ))) = (χ (π ^ n) : ℂ)
    rw [map_zpow, Circle.coe_zpow, ← he, ← Complex.exp_int_mul]
    congr 1
    ring
  · intro z
    unfold finiteZetaDenominator finiteZetaRatio
    change 1 - (χ π : ℂ) * Complex.exp (-z * (Real.log q : ℂ)) =
      1 - (1 : Circle) * Complex.exp (-(z + a) * (Real.log q : ℂ))
    rw [← he, ← Complex.exp_add, Circle.coe_one, one_mul]
    congr 2
    ring

omit [∀ w : HeightOneSpectrum (𝓞 F), MeasurableSpace (w.adicCompletion F)]
  [∀ w : HeightOneSpectrum (𝓞 F), BorelSpace (w.adicCompletion F)]
  [MeasurableSpace (G F v)] [BorelSpace (G F v)] in
private theorem finiteZetaWeight_add' (a b : ℂ) (u : G F v) :
    finiteZetaWeight F v (a + b) u = finiteZetaWeight F v a u * finiteZetaWeight F v b u := by
  simp only [finiteZetaWeight, add_mul, Complex.exp_add]

/-- Equation (3.3.1.29) on the full finite local test space, with the
spectral coordinate chosen to put the entire unramified character in
the norm exponent. -/
theorem finiteZeta_tamagawa_unramified_fourier (μ : Measure (G F v)) [μ.IsHaarMeasure]
    (χ : G F v →ₜ* Circle) (hχ : finiteZetaUnramified F v χ) :
    ∃ a : ℂ, a.re = 0 ∧ (∀ u : G F v, finiteZetaWeight F v a u = (χ u : ℂ)) ∧
      ∀ (z : ℂ) (_hr : 0 < z.re) (_hl : z.re < 1) (f : E F v),
        finiteZetaDenominator F v χ z * finiteZetaIntegral F v μ χ f z =
          Complex.exp ((multiplicity v.asIdeal (differentIdeal ℤ (𝓞 F)) : ℂ) *
            (z + a - 1 / 2) * (Real.log (v.asIdeal.absNorm : ℝ) : ℂ)) *
          (finiteZetaDenominator F v χ⁻¹ (1 - z) *
            finiteZetaIntegral F v μ χ⁻¹ (T F v f) (1 - z)) := by
  obtain ⟨a, ha, hw, hD⟩ := finiteZetaUnramified_exists_shift F v χ hχ
  have hinv (u : G F v) : finiteZetaWeight F v (-a) u = (χ⁻¹ u : ℂ) := by
    change finiteZetaWeight F v (-a) u = ((χ u)⁻¹ : Circle)
    rw [Circle.coe_inv, ← hw, finiteZetaWeight, finiteZetaWeight, ← Complex.exp_neg, neg_mul]
  have hI (w : ℂ) (f : E F v) :
      finiteZetaIntegral F v μ χ f w = finiteZetaIntegral F v μ 1 f (w + a) := by
    unfold finiteZetaIntegral
    apply integral_congr_ae
    exact .of_forall fun u ↦ by
      change f.val u.val * (χ u : ℂ) * finiteZetaWeight F v w u =
        f.val u.val * ((1 : G F v →ₜ* Circle) u : ℂ) * finiteZetaWeight F v (w + a) u
      rw [finiteZetaWeight_add', hw, show ((1 : G F v →ₜ* Circle) u : ℂ) = 1 from rfl, mul_one]
      ring
  have hJ (w : ℂ) (f : E F v) :
      finiteZetaIntegral F v μ χ⁻¹ f w = finiteZetaIntegral F v μ 1 f (w - a) := by
    unfold finiteZetaIntegral
    apply integral_congr_ae
    exact .of_forall fun u ↦ by
      change f.val u.val * (χ⁻¹ u : ℂ) * finiteZetaWeight F v w u =
        f.val u.val * ((1 : G F v →ₜ* Circle) u : ℂ) * finiteZetaWeight F v (w - a) u
      rw [sub_eq_add_neg, finiteZetaWeight_add', hinv,
        show ((1 : G F v →ₜ* Circle) u : ℂ) = 1 from rfl, mul_one]
      ring
  have hD' (w : ℂ) : finiteZetaDenominator F v χ⁻¹ w =
      finiteZetaDenominator F v 1 (w - a) := by
    let π := chosenFiniteUniformizer F v
    unfold finiteZetaDenominator finiteZetaRatio
    change 1 - (χ⁻¹ π : ℂ) * _ = 1 - (1 : ℂ) * _
    rw [← hinv, finiteZetaWeight, norm_finiteUniformizer F v _ (chosenFiniteUniformizer_spec F v),
      Real.log_inv, Complex.ofReal_neg, ← Complex.exp_add, one_mul]
    congr 2
    ring
  refine ⟨a, ha, hw, fun z hr hl f ↦ ?_⟩
  rw [hD, hI, hD', hJ, show 1 - z - a = 1 - (z + a) by ring]
  have he (w : ℂ) : finiteZetaDenominator F v 1 w =
      1 - Complex.exp (-w * (Real.log (v.asIdeal.absNorm : ℝ) : ℂ)) := by
    simp [finiteZetaDenominator, finiteZetaRatio]
  rw [he, he]
  exact finiteZeta_tamagawa_trivialPhase_fourier F v μ (z + a)
    (by simpa [ha] using hr) (by simpa [ha] using hl) f

/-- The unramified finite-place equation for the entire, Euler-cleared
local distributions, including at the Euler zeros. -/
theorem finiteZeta_tamagawa_unramified_fourier_entire (μ : Measure (G F v)) [μ.IsHaarMeasure]
    (χ : G F v →ₜ* Circle) (hχ : finiteZetaUnramified F v χ) :
    letI : TopologicalSpace (E F v) := finestLocallyConvexTopology _
    ∃ a : ℂ, a.re = 0 ∧ (∀ u : G F v, finiteZetaWeight F v a u = (χ u : ℂ)) ∧
      let ε (z : ℂ) := Complex.exp ((multiplicity v.asIdeal (differentIdeal ℤ (𝓞 F)) : ℂ) *
        (z + a - 1 / 2) * (Real.log (v.asIdeal.absNorm : ℝ) : ℂ))
      (∀ z : ℂ, ε z ≠ 0) ∧ (∀ z : ℂ, z.re = 1 / 2 → ‖ε z‖ = 1) ∧
      ∀ f : E F v, (fun z ↦ finiteZetaClearedDistribution F v μ χ z f) =
        fun z ↦ ε z * finiteZetaClearedDistribution F v μ χ⁻¹ (1 - z) (T F v f) := by
  letI : TopologicalSpace (E F v) := finestLocallyConvexTopology _
  obtain ⟨a, ha, hshift, hI⟩ := finiteZeta_tamagawa_unramified_fourier F v μ χ hχ
  let ε (z : ℂ) := Complex.exp ((multiplicity v.asIdeal (differentIdeal ℤ (𝓞 F)) : ℂ) *
    (z + a - 1 / 2) * (Real.log (v.asIdeal.absNorm : ℝ) : ℂ))
  refine ⟨a, ha, hshift, fun _ ↦ Complex.exp_ne_zero _, ?_, ?_⟩
  · intro z hz
    change ‖ε z‖ = 1
    rw [show ε z = finitePlaceUnramifiedEpsilon F v
      (-(multiplicity v.asIdeal (differentIdeal ℤ (𝓞 F)) : ℤ)) (z + a) by
        simp [ε, finitePlaceUnramifiedEpsilon]]
    exact (finitePlaceUnramifiedEpsilon_properties F v _).2.2 _ (by simpa [ha] using hz)
  · intro f
    have hε : AnalyticOnNhd ℂ ε univ := by
      intro z _
      dsimp only [ε]
      fun_prop
    have hR : AnalyticOnNhd ℂ
        (fun z ↦ finiteZetaClearedDistribution F v μ χ⁻¹ (1 - z) (T F v f)) univ := by
      intro z _
      exact (finiteZetaClearedDistribution_analytic F v μ χ⁻¹ (T F v f) (1 - z) trivial).comp
        (analyticAt_const.fun_sub analyticAt_id)
    apply (finiteZetaClearedDistribution_analytic F v μ χ f).eq_of_eventuallyEq
      (hε.mul hR) (z₀ := (1 / 2 : ℂ))
    let U := {z : ℂ | 0 < z.re ∧ z.re < 1}
    have hU : IsOpen U := (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
    have hU₀ : (1 / 2 : ℂ) ∈ U := by
      change 0 < (1 / 2 : ℂ).re ∧ (1 / 2 : ℂ).re < 1
      norm_num [Complex.div_ofNat_re]
    filter_upwards [hU.mem_nhds hU₀] with z hz
    have hr : 0 < (1 - z).re := by simpa [Complex.sub_re, sub_pos] using hz.2
    change finiteZetaClearedDistribution F v μ χ z f =
      ε z * finiteZetaClearedDistribution F v μ χ⁻¹ (1 - z) (T F v f)
    rw [finiteZetaClearedDistribution_eq_mul_integral F v μ χ f z hz.1,
      finiteZetaClearedDistribution_eq_mul_integral F v μ χ⁻¹ (T F v f) (1 - z) hr]
    simpa only [mul_comm (finiteZetaIntegral F v μ χ f z),
      mul_comm (finiteZetaIntegral F v μ χ⁻¹ (T F v f) (1 - z))] using hI z hz.1 hz.2 f

private def finiteTateConjTest (f : E F v) : E F v :=
  ⟨conj ∘ f.val, f.property.1.comp conj, f.property.2.comp_left (map_zero conj)⟩

omit [MeasurableSpace (G F v)] [BorelSpace (G F v)] in
private theorem finiteFourier_conj_fourier (f : E F v) :
    T F v (finiteTateConjTest F v (T F v f)) = finiteTateConjTest F v f := by
  apply Subtype.ext
  funext y
  have h (g : E F v) :
      (T F v (finiteTateConjTest F v g)).val y = conj ((T F v g).val (-y)) := by
    change (∫ x, conj (g.val x) * ((finitePlaceTraceCharacter F v (x * y)).toMul : ℂ) ∂η F v) =
      conj (∫ x, g.val x * ((finitePlaceTraceCharacter F v (x * -y)).toMul : ℂ) ∂η F v)
    rw [← integral_conj]
    apply integral_congr_ae
    exact .of_forall fun x ↦ by
      change conj (g.val x) * ((finitePlaceTraceCharacter F v (x * y)).toMul : ℂ) =
        conj (g.val x * ((finitePlaceTraceCharacter F v (x * -y)).toMul : ℂ))
      rw [map_mul conj, mul_neg, map_neg]
      change _ = conj (g.val x) *
        conj ((((finitePlaceTraceCharacter F v (x * y)).toMul)⁻¹ : Circle) : ℂ)
      rw [Circle.coe_inv_eq_conj, starRingEnd_self_apply]
  rw [h, show (T F v (T F v f)).val (-y) = f.val (- -y) from
    finitePlaceFourierTest_twice F v (η F v) (finitePlace_tamagawa_fourier_normalization F v) f (-y),
    neg_neg]
  rfl

omit [∀ w : HeightOneSpectrum (𝓞 F), MeasurableSpace (w.adicCompletion F)]
  [∀ w : HeightOneSpectrum (𝓞 F), BorelSpace (w.adicCompletion F)]
  [BorelSpace (G F v)] in
private theorem finiteZetaIntegral_conj_test (μ : Measure (G F v))
    (χ : G F v →ₜ* Circle) (f : E F v) (z : ℂ) :
    finiteZetaIntegral F v μ χ⁻¹ (finiteTateConjTest F v f) (conj z) =
      conj (finiteZetaIntegral F v μ χ f z) := by
  unfold finiteZetaIntegral
  rw [← integral_conj]
  apply integral_congr_ae
  exact .of_forall fun x ↦ by
    change conj (f.val x.val) * ((χ x)⁻¹ : Circle) * finiteZetaWeight F v (conj z) x =
      conj (f.val x.val * (χ x : ℂ) * finiteZetaWeight F v z x)
    rw [map_mul, map_mul, Circle.coe_inv_eq_conj, finiteZetaWeight, finiteZetaWeight,
      ← Complex.exp_conj, map_mul, Complex.conj_ofReal]

/-- On a ramified component the entire local zeta functions satisfy the
Fourier equation with one nowhere-vanishing entire factor. -/
theorem finiteZeta_tamagawa_ramified_fourier_entire (μ : Measure (G F v)) [μ.IsHaarMeasure]
    (χ : G F v →ₜ* Circle) (hχ : ¬finiteZetaUnramified F v χ) :
    ∃ ε : ℂ → ℂ, AnalyticOnNhd ℂ ε univ ∧ (∀ z, ε z ≠ 0) ∧
      (∀ z : ℂ, z.re = 1 / 2 → ‖ε z‖ = 1) ∧
      ∀ f : E F v, finiteZetaContinuation F v μ χ f =
        fun z ↦ ε z * finiteZetaContinuation F v μ χ⁻¹ (T F v f) (1 - z) := by
  have hχ' : ¬finiteZetaUnramified F v χ⁻¹ := by
    intro h
    apply hχ
    intro u hu
    have hu' := h u hu
    change (χ u)⁻¹ = 1 at hu'
    exact inv_eq_one.mp hu'
  let L (f : E F v) := finiteZetaContinuation F v μ χ f
  let R (f : E F v) (z : ℂ) := finiteZetaContinuation F v μ χ⁻¹ (T F v f) (1 - z)
  have hL (f : E F v) : AnalyticOnNhd ℂ (L f) univ :=
    finiteZetaContinuation_analytic_of_ramified F v μ χ hχ f
  have hR (f : E F v) : AnalyticOnNhd ℂ (R f) univ := fun z _ ↦
    (finiteZetaContinuation_analytic_of_ramified F v μ χ⁻¹ hχ' (T F v f) (1 - z) trivial).comp
      (analyticAt_const.fun_sub analyticAt_id)
  let U := {z : ℂ | 0 < z.re ∧ z.re < 1}
  have hU : IsOpen U := (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt Complex.continuous_re continuous_const)
  have hU₀ : (1 / 2 : ℂ) ∈ U := by
    change 0 < (1 / 2 : ℂ).re ∧ (1 / 2 : ℂ).re < 1
    norm_num [Complex.div_ofNat_re]
  have hRef (ξ : G F v →ₜ* Circle) (hξ : ¬finiteZetaUnramified F v ξ) :
      ∃ (g : E F v) (C : ℂ), C ≠ 0 ∧ finiteZetaContinuation F v μ ξ g = fun _ ↦ C := by
    obtain ⟨g, C, _, hC, hI, _⟩ := exists_finiteMellinUnitTest F v μ ξ
    refine ⟨g, C, hC, ?_⟩
    apply (finiteZetaContinuation_analytic_of_ramified F v μ ξ hξ g).eq_of_eventuallyEq
      analyticOnNhd_const (z₀ := (1 / 2 : ℂ))
    filter_upwards [hU.mem_nhds hU₀] with z hz
    exact (finiteZetaContinuation_eq_integral F v μ ξ g z hz.1).2.symm.trans (hI z hz.1)
  obtain ⟨b, B, hB, hb⟩ := hRef χ⁻¹ hχ'
  obtain ⟨g, hg⟩ := finitePlaceFourierTest_tamagawa_surjective F v b
  change T F v g = b at hg
  have hRg (z : ℂ) : R g z = B := by
    change finiteZetaContinuation F v μ χ⁻¹ (T F v g) (1 - z) = B
    rw [hg, hb]
  let ε (z : ℂ) := L g z * B⁻¹
  have hε : AnalyticOnNhd ℂ ε univ := (hL g).mul analyticOnNhd_const
  have hEq (f : E F v) : L f = fun z ↦ ε z * R f z := by
    apply (hL f).eq_of_eventuallyEq (hε.mul (hR f)) (z₀ := (1 / 2 : ℂ))
    filter_upwards [hU.mem_nhds hU₀] with z hz
    have hr : 0 < (1 - z).re := by simpa [Complex.sub_re, sub_pos] using hz.2
    have hCross : L f z * R g z = L g z * R f z := by
      change finiteZetaContinuation F v μ χ f z *
          finiteZetaContinuation F v μ χ⁻¹ (T F v g) (1 - z) =
        finiteZetaContinuation F v μ χ g z *
          finiteZetaContinuation F v μ χ⁻¹ (T F v f) (1 - z)
      rw [← (finiteZetaContinuation_eq_integral F v μ χ f z hz.1).2,
        ← (finiteZetaContinuation_eq_integral F v μ χ g z hz.1).2,
        ← (finiteZetaContinuation_eq_integral F v μ χ⁻¹ (T F v g) (1 - z) hr).2,
        ← (finiteZetaContinuation_eq_integral F v μ χ⁻¹ (T F v f) (1 - z) hr).2]
      exact finiteZeta_fourier_crossProduct F v μ χ z hz.1 hz.2 f g
    change L f z = (L g z * B⁻¹) * R f z
    rw [hRg] at hCross
    calc
      _ = (L f z * B) * B⁻¹ := by rw [mul_assoc, mul_inv_cancel₀ hB, mul_one]
      _ = _ := by rw [hCross]; ring
  obtain ⟨f, C, hC, hf⟩ := hRef χ hχ
  have hfC (z : ℂ) : L f z = C := congrFun hf z
  refine ⟨ε, hε, ?_, ?_, hEq⟩
  · intro z hz
    apply hC
    have h := congrFun (hEq f) z
    change L f z = ε z * R f z at h
    rw [hfC, hz, zero_mul] at h
    exact h
  · intro z hz
    have hz' : 1 - z = conj z := by
      apply Complex.ext
      · norm_num [Complex.sub_re, hz]
      · simp [Complex.sub_im]
    have hp : 0 < z.re := by rw [hz]; norm_num
    have hp' : 0 < (1 - z).re := by rw [hz']; simpa using hp
    let J := finiteTateConjTest F v (T F v f)
    have hBack : R J z = conj (L f z) := by
      change finiteZetaContinuation F v μ χ⁻¹ (T F v J) (1 - z) = _
      rw [show T F v J = finiteTateConjTest F v f from finiteFourier_conj_fourier F v f,
        ← (finiteZetaContinuation_eq_integral F v μ χ⁻¹ _ _ hp').2, hz',
        finiteZetaIntegral_conj_test F v μ χ f z]
      exact congrArg conj (finiteZetaContinuation_eq_integral F v μ χ f z hp).2
    have hFront : R f z = conj (L J z) := by
      have h := finiteZetaIntegral_conj_test F v μ χ⁻¹ (T F v f) (1 - z)
      rw [inv_inv, show conj (1 - z) = z by rw [hz', starRingEnd_self_apply],
        (finiteZetaContinuation_eq_integral F v μ χ J z hp).2,
        (finiteZetaContinuation_eq_integral F v μ χ⁻¹ (T F v f) (1 - z) hp').2] at h
      simpa only [starRingEnd_self_apply] using (congrArg conj h).symm
    have h1 : L f z = ε z * R f z := congrFun (hEq f) z
    have h2 : L J z = ε z * R J z := congrFun (hEq J) z
    rw [hFront, h2, hBack, map_mul, starRingEnd_self_apply, ← mul_assoc] at h1
    have he : ε z * conj (ε z) = 1 :=
      mul_right_cancel₀ (fun h ↦ hC ((hfC z).symm.trans h)) (by simpa using h1.symm)
    rw [Complex.mul_conj] at he
    have hsq : ‖ε z‖ ^ 2 = 1 := by
      rw [← Complex.normSq_eq_norm_sq]
      exact Complex.ofReal_injective (he.trans Complex.ofReal_one.symm)
    nlinarith [norm_nonneg (ε z)]

variable (S : Finset (HeightOneSpectrum (𝓞 F)))
  [∀ w : S, MeasurableSpace (K F w.val)ˣ] [∀ w : S, BorelSpace (K F w.val)ˣ]

omit [MeasurableSpace (G F v)] [BorelSpace (G F v)] in
/-- A finite Tate multiplier specified by its equation on all local
tests and by the explicit different factor in the unramified case. -/
def IsFiniteTateMultiplier
    (μ : ∀ w : S, Measure (K F w.val)ˣ) [∀ w : S, (μ w).IsHaarMeasure]
    (χ : ∀ w : S, (K F w.val)ˣ →ₜ* Circle) (w : S) (ε : ℂ → ℂ) : Prop :=
  AnalyticOnNhd ℂ ε univ ∧ (∀ z, ε z ≠ 0) ∧
    (∀ z : ℂ, z.re = 1 / 2 → ‖ε z‖ = 1) ∧
    (∀ (f : E F w.val) (z : ℂ), finiteProductClearedLocal F S μ χ w f z =
      ε z * finiteProductClearedLocal F S μ (fun t ↦ (χ t)⁻¹) w (T F w.val f) (1-z)) ∧
    (finiteZetaUnramified F w.val (χ w) →
      ∃ a : ℂ, a.re = 0 ∧
        (∀ u : (K F w.val)ˣ, finiteZetaWeight F w.val a u = (χ w u : ℂ)) ∧
        ∀ z, ε z = Complex.exp ((multiplicity w.val.asIdeal (differentIdeal ℤ (𝓞 F)) : ℂ) *
          (z + a - 1/2) * (Real.log (w.val.asIdeal.absNorm : ℝ) : ℂ)))

omit [MeasurableSpace (G F v)] [BorelSpace (G F v)] in
/-- The finite factors multiply on separated tests, with the same
normalization used in the continued S-local finite product. -/
theorem exists_sLocalFiniteZeta_fourier_product
    (μ : ∀ w : S, Measure (K F w.val)ˣ) [∀ w : S, (μ w).IsHaarMeasure]
    [∀ w : S, SigmaFinite (μ w)] (χ : ∀ w : S, (K F w.val)ˣ →ₜ* Circle) :
    letI : TopologicalSpace (locallyConstantTests (∀ w : S, K F w.val)) :=
      finestLocallyConvexTopology _
    ∃ ε : S → ℂ → ℂ,
      (∀ w, IsFiniteTateMultiplier F S μ χ w (ε w)) ∧
      ∀ (f : ∀ w : S, E F w.val) (z : ℂ),
        sLocalFiniteZetaCleared F S μ χ z (locallyConstantTestPiProduct f) =
          (∏ w : S, ε w z) *
            sLocalFiniteZetaCleared F S μ (fun w ↦ (χ w)⁻¹) (1 - z)
              (locallyConstantTestPiProduct fun w ↦ T F w.val (f w)) := by
  letI : TopologicalSpace (locallyConstantTests (∀ w : S, K F w.val)) :=
    finestLocallyConvexTopology _
  have h (w : S) : ∃ ε : ℂ → ℂ, IsFiniteTateMultiplier F S μ χ w ε := by
    have hInv : finiteZetaUnramified F w.val (χ w)⁻¹ ↔ finiteZetaUnramified F w.val (χ w) := by
      constructor
      · intro h u hu
        have hi := h u hu
        change (χ w u)⁻¹ = 1 at hi
        exact inv_eq_one.mp hi
      · intro h u hu
        change (χ w u)⁻¹ = 1
        rw [h u hu, inv_one]
    by_cases hχ : finiteZetaUnramified F w.val (χ w)
    · obtain ⟨a, haxis, hphase, hne, hunit, he⟩ :=
        finiteZeta_tamagawa_unramified_fourier_entire F w.val (μ w) (χ w) hχ
      let ε z := Complex.exp ((multiplicity w.val.asIdeal (differentIdeal ℤ (𝓞 F)) : ℂ) *
        (z + a - 1 / 2) * (Real.log (w.val.asIdeal.absNorm : ℝ) : ℂ))
      have ha : AnalyticOnNhd ℂ ε univ := by
        intro z _
        dsimp only [ε]
        fun_prop
      refine ⟨ε, ha, hne, hunit, (fun f z ↦ ?_), fun _ ↦ ⟨a, haxis, hphase, fun _ ↦ rfl⟩⟩
      rw [finiteProductClearedLocal, ite_eq_left hχ, finiteProductClearedLocal,
        ite_eq_left (hInv.mpr hχ)]
      exact congrFun (he f) z
    · obtain ⟨ε, ha, hne, hunit, he⟩ :=
        finiteZeta_tamagawa_ramified_fourier_entire F w.val (μ w) (χ w) hχ
      refine ⟨ε, ha, hne, hunit, (fun f z ↦ ?_), fun h ↦ (hχ h).elim⟩
      rw [finiteProductClearedLocal, ite_eq_right hχ, finiteProductClearedLocal,
        ite_eq_right (mt hInv.mp hχ)]
      exact congrFun (he f) z
  choose ε hε using h
  refine ⟨ε, hε, fun f z ↦ ?_⟩
  rw [sLocalFiniteZetaCleared_piProduct, sLocalFiniteZetaCleared_piProduct, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun w _ ↦ (hε w).2.2.2.1 (f w) z

end

end Masullo
