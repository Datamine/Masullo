import SobolevWeights
import AdelicZetaUnfolding
import CompactCharacterCompleteness
import HeckeEulerProducts
import Mathlib.Analysis.Analytic.Order
import Mathlib.NumberTheory.Padics.HeightOneSpectrum

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical NNReal NumberField

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

private abbrev G := IdeleClass F
private abbrev Place := HeightOneSpectrum (𝓞 F)
private abbrev logNorm (g : G F) : ℝ := (ideleClassLogNorm F g).toAdd

private theorem logNorm_surjective : Surjective (logNorm F) :=
  fun x => ⟨ideleClassExpSection F (Multiplicative.ofAdd x),
    congrArg Multiplicative.toAdd (ideleClassLogNorm_expSection F _)⟩

/-- The reciprocal of the finite Euler product in (11.2.0.5). -/
def orbitalEulerDenominator (S : Finset (Place F)) (χ : PontryaginDual (G F)) (z : ℂ) : ℂ :=
  ∏ v ∈ S, (1 -
    (χ (ideleClassMap F (singleFiniteIdele F v (chosenFiniteUniformizer F v))) : ℂ) *
      Complex.exp (-z * (Real.log (v.asIdeal.absNorm : ℝ) : ℂ)))

/-- On unramified places this is the product of the reciprocals of the
actual local Hecke factors. -/
theorem orbitalEulerDenominator_eq_hecke (S : Finset (Place F))
    (χ : PontryaginDual (G F)) (hχ : ∀ v ∈ S, unramifiedFiniteCharacter F χ v) (z : ℂ) :
    orbitalEulerDenominator F S χ z =
      ∏ v ∈ S, (heckeEulerFactor F
        (heckeEulerCoefficient F χ (chosenFiniteUniformizer F)) v z)⁻¹ := by
  apply Finset.prod_congr rfl
  intro v hv
  have hn : 0 < (v.asIdeal.absNorm : ℝ) := by
    have hn' : 1 < (v.asIdeal.absNorm : ℝ) := by
      exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
    linarith
  simp only [heckeEulerFactor, inv_inv, heckeEulerCoefficient,
    ite_eq_left (hχ v hv), ← Complex.ofReal_natCast,
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hn.ne'),
    ← Complex.ofReal_log hn.le, mul_comm (-z)]

theorem orbitalEulerDenominator_zero_re (S : Finset (Place F))
    (χ : PontryaginDual (G F)) {z : ℂ} (hz : orbitalEulerDenominator F S χ z = 0) : z.re = 0 := by
  obtain ⟨v, _, hv⟩ := Finset.prod_eq_zero_iff.mp hz
  have hv := sub_eq_zero.mp hv
  have hn := congrArg norm hv
  rw [norm_one, norm_mul, Circle.norm_coe, one_mul, Complex.norm_exp,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
    Complex.neg_re, ← Real.exp_zero] at hn
  have hq : 1 < (v.asIdeal.absNorm : ℝ) := by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
  have he := Real.exp_injective hn.symm
  linarith [(mul_eq_zero.mp he).resolve_right (Real.log_pos hq).ne']

private theorem orbitalEulerDenominator_analytic (S : Finset (Place F))
    (χ : PontryaginDual (G F)) (z : ℂ) :
    AnalyticAt ℂ (orbitalEulerDenominator F S χ) z := by
  induction S using Finset.induction_on with
  | empty =>
    have he : orbitalEulerDenominator F ∅ χ = fun _ => 1 :=
      funext fun w => by simp [orbitalEulerDenominator]
    rw [he]
    exact analyticAt_const
  | insert v S hv ih =>
    have he : orbitalEulerDenominator F (insert v S) χ = fun w =>
        (1 - (χ (ideleClassMap F (singleFiniteIdele F v (chosenFiniteUniformizer F v))) : ℂ) *
          Complex.exp (-w * (Real.log (v.asIdeal.absNorm : ℝ) : ℂ))) *
          orbitalEulerDenominator F S χ w :=
      funext fun w => by simp [orbitalEulerDenominator, Finset.prod_insert hv]
    rw [he]
    exact (analyticAt_const.sub (analyticAt_const.mul
      ((analyticAt_id.neg.mul analyticAt_const).cexp'))).mul ih

/-- Each nonempty finite Euler product has a zero of positive finite multiplicity. -/
theorem orbitalEulerDenominator_has_zero (S : Finset (Place F)) (hS : S.Nonempty)
    (χ : PontryaginDual (G F)) :
    ∃ z : ℂ, orbitalEulerDenominator F S χ z = 0 ∧
      0 < analyticOrderNatAt (orbitalEulerDenominator F S χ) z := by
  obtain ⟨v, hv⟩ := hS
  let a := χ (ideleClassMap F (singleFiniteIdele F v (chosenFiniteUniformizer F v)))
  let d : ℂ := Real.log (v.asIdeal.absNorm : ℝ)
  have hd : d ≠ 0 := by
    apply Complex.ofReal_ne_zero.mpr (Real.log_pos ?_).ne'
    exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
  let z := -Complex.log (a⁻¹ : Circle) / d
  have hz : orbitalEulerDenominator F S χ z = 0 := by
    apply Finset.prod_eq_zero hv
    change 1 - (a : ℂ) * Complex.exp (-z * d) = 0
    have he : -z * d = Complex.log (a⁻¹ : Circle) := by
      dsimp [z]
      rw [neg_div, neg_neg, div_mul_cancel₀ _ hd]
    rw [he, Complex.exp_log (Circle.coe_ne_zero _), Circle.coe_inv,
      mul_inv_cancel₀ (Circle.coe_ne_zero _), sub_self]
  have hnot : analyticOrderAt (orbitalEulerDenominator F S χ) z ≠ ⊤ := by
    intro htop
    have he := (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero z
      (orbitalEulerDenominator_analytic F S χ)).mp htop
    have h1 : orbitalEulerDenominator F S χ 1 = 0 := by
      simpa using congrFun he 1
    have h := orbitalEulerDenominator_zero_re F S χ h1
    norm_num at h
  exact ⟨z, hz, ENat.toNat_pos
    ((orbitalEulerDenominator_analytic F S χ z).analyticOrderAt_ne_zero.mpr hz) hnot⟩

/-- For any unitary character, a root of the finite Euler product counts
once for each selected place whose reciprocal factor vanishes there. -/
theorem orbitalEulerDenominator_order_eq_card (S : Finset (Place F))
    (χ : PontryaginDual (G F)) (z : ℂ) :
    let B (v : Place F) (w : ℂ) := 1 -
      (χ (ideleClassMap F (singleFiniteIdele F v (chosenFiniteUniformizer F v))) : ℂ) *
        Complex.exp (-w * (Real.log (v.asIdeal.absNorm : ℝ) : ℂ))
    analyticOrderAt (orbitalEulerDenominator F S χ) z =
      ((S.filter fun v ↦ B v z = 0).card : ℕ∞) := by
  classical
  intro B
  have hB (v : Place F) : AnalyticAt ℂ (B v) z ∧
      analyticOrderAt (B v) z = if B v z = 0 then 1 else 0 := by
    let d : ℂ := Real.log (v.asIdeal.absNorm : ℝ)
    let a : ℂ := χ (ideleClassMap F (singleFiniteIdele F v (chosenFiniteUniformizer F v)))
    have hq : 1 < (v.asIdeal.absNorm : ℝ) := by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
    have hd : d ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.log_pos hq).ne'
    have ha : AnalyticAt ℂ (B v) z :=
      analyticAt_const.sub (analyticAt_const.mul
        ((analyticAt_id.neg.mul analyticAt_const).cexp'))
    refine ⟨ha, ?_⟩
    by_cases hv : B v z = 0
    · rw [ite_eq_left hv]
      have hz : a * Complex.exp (-z * d) = 1 := (sub_eq_zero.mp hv).symm
      have hder : HasDerivAt (B v) d z := by
        apply (((((hasDerivAt_id z).neg.mul_const d).cexp).const_mul a).const_sub 1).congr_deriv
        simp only [Pi.neg_apply, id_eq, neg_mul, one_mul]
        calc
          _ = (a * Complex.exp (-z * d)) * d := by ring_nf
          _ = d := by rw [hz, one_mul]
      exact ha.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hv (hder.deriv ▸ hd)
    · rw [ite_eq_right hv]
      exact ha.analyticOrderAt_eq_zero.mpr hv
  induction S using Finset.induction_on with
  | empty =>
    rw [show orbitalEulerDenominator F ∅ χ = fun _ => 1 from
      funext fun w ↦ Finset.prod_empty, Finset.filter_empty, Finset.card_empty, Nat.cast_zero]
    exact
      (analyticAt_const (v := (1 : ℂ))).analyticOrderAt_eq_zero.mpr one_ne_zero
  | insert v S hv ih =>
    have he : orbitalEulerDenominator F (insert v S) χ =
        B v * orbitalEulerDenominator F S χ := by
      funext w
      exact Finset.prod_insert hv
    rw [he, analyticOrderAt_mul (hB v).1 (orbitalEulerDenominator_analytic F S χ z), ih,
      (hB v).2, Finset.filter_insert]
    split_ifs with hz
    · rw [Finset.card_insert_of_notMem (fun h ↦ hv (Finset.mem_filter.mp h).1), Nat.cast_add, Nat.cast_one,
        add_comm]
    · exact zero_add _

/-- At the trivial character the zero at the origin has one simple
contribution from every chosen finite place. -/
theorem orbitalEulerDenominator_trivial_order_at_zero (S : Finset (Place F)) :
    orbitalEulerDenominator F S 1 0 = 0 ∧
      analyticOrderNatAt (orbitalEulerDenominator F S 1) 0 = S.card ∨ S = ∅ := by
  let B (v : Place F) (z : ℂ) := 1 -
    Complex.exp (-z * (Real.log (v.asIdeal.absNorm : ℝ) : ℂ))
  have he (S : Finset (Place F)) : orbitalEulerDenominator F S 1 =
      fun z => ∏ v ∈ S, B v z := by
    funext z
    simp [orbitalEulerDenominator, B, Circle.coe_one]
  have hB (v : Place F) : AnalyticAt ℂ (B v) 0 ∧ analyticOrderAt (B v) 0 = 1 := by
    let d : ℂ := Real.log (v.asIdeal.absNorm : ℝ)
    have hq : 1 < (v.asIdeal.absNorm : ℝ) := by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
    have hd : d ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.log_pos hq).ne'
    have ha : AnalyticAt ℂ (B v) 0 :=
      analyticAt_const.sub ((analyticAt_id.neg.mul analyticAt_const).cexp')
    have hder : HasDerivAt (B v) d 0 := by
      apply ((((hasDerivAt_id (0 : ℂ)).neg.mul_const d).cexp).const_sub (1 : ℂ)).congr_deriv
      simp
    refine ⟨ha, ha.analyticOrderAt_eq_one_of_zero_deriv_ne_zero ?_ ?_⟩
    · simp [B]
    · rwa [hder.deriv]
  have hp (T : Finset (Place F)) :
      AnalyticAt ℂ (fun z => ∏ v ∈ T, B v z) 0 ∧
        analyticOrderAt (fun z => ∏ v ∈ T, B v z) 0 = T.card := by
    induction T using Finset.induction_on with
    | empty =>
      simpa using ⟨analyticAt_const (v := (1 : ℂ)),
        (analyticAt_const (v := (1 : ℂ))).analyticOrderAt_eq_zero.mpr one_ne_zero⟩
    | insert v T hv ih =>
      simp only [Finset.prod_insert hv, Finset.card_insert_of_notMem hv]
      exact ⟨(hB v).1.mul ih.1, by
        rw [show (fun z => B v z * ∏ w ∈ T, B w z) =
            B v * (fun z => ∏ w ∈ T, B w z) from rfl,
          analyticOrderAt_mul (hB v).1 ih.1, (hB v).2, ih.2, Nat.cast_add, Nat.cast_one, add_comm]⟩
  by_cases hS : S = ∅
  · exact Or.inr hS
  left
  obtain ⟨v, hv⟩ := Finset.nonempty_iff_ne_empty.mpr hS
  rw [he]
  exact ⟨Finset.prod_eq_zero hv (by simp [B]), by simp [analyticOrderNatAt, (hp S).2]⟩

/-- The function in (11.2.0.8) in the reciprocal-weight (L^2) coordinate. -/
def orbitalSobolevMoment (χ : PontryaginDual (G F)) (s : ℝ) (z : ℂ) (m : ℕ) (g : G F) : ℂ :=
  ((1 + ‖logNorm F g‖ ^ 2) ^ (-s / 4) : ℝ) *
    ((χ g : ℂ) * Complex.exp (z * (logNorm F g : ℂ))) * (logNorm F g : ℂ) ^ m

private theorem orbitalSobolevMoment_continuous (χ : PontryaginDual (G F))
    (s : ℝ) (z : ℂ) (m : ℕ) : Continuous (orbitalSobolevMoment F χ s z m) := by
  have hl : Continuous (logNorm F) := ideleClassLogNorm_continuous F
  have hw : Continuous (fun g : G F => (1 + ‖logNorm F g‖ ^ 2) ^ (-s / 4)) :=
    (continuous_const.add (hl.norm.pow 2)).rpow_const (fun g =>
      Or.inl (add_pos_of_pos_of_nonneg zero_lt_one (sq_nonneg ‖logNorm F g‖)).ne')
  exact ((Complex.continuous_ofReal.comp hw).mul
    ((continuous_subtype_val.comp χ.continuous).mul
      (Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp hl))))).mul
      ((Complex.continuous_ofReal.comp hl).pow m)

private theorem norm_orbitalSobolevMoment (χ : PontryaginDual (G F))
    (s : ℝ) {z : ℂ} (hz : z.re = 0) (m : ℕ) (g : G F) :
    ‖orbitalSobolevMoment F χ s z m g‖ =
      (1 + ‖logNorm F g‖ ^ 2) ^ (-s / 4) * ‖logNorm F g‖ ^ m := by
  have hw : 0 ≤ (1 + ‖logNorm F g‖ ^ 2) ^ (-s / 4) :=
    Real.rpow_nonneg (add_nonneg zero_le_one (sq_nonneg _)) _
  have hphase : ‖Complex.exp (z * (logNorm F g : ℂ))‖ = 1 := by
    simp [Complex.norm_exp, Complex.mul_re, hz]
  rw [orbitalSobolevMoment, norm_mul, norm_mul, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg hw, Circle.norm_coe, hphase, one_mul, mul_one, norm_pow, Complex.norm_real]

/-- Right translations by norm-one classes act on the moments by the restricted
character. The reciprocal density is invariant under these translations. -/
theorem orbitalSobolevMoment_isotypic (χ : PontryaginDual (G F))
    (s : ℝ) (z : ℂ) (m : ℕ) (g : G F) (h : normOneIdeleClass F) :
    orbitalSobolevMoment F χ s z m (g * h.val) =
      (χ h.val : ℂ) * orbitalSobolevMoment F χ s z m g := by
  have hh : ideleClassLogNorm F h.val = 1 := by
    change Multiplicative.ofAdd (Real.log (ideleClassNorm F h.val)) = Multiplicative.ofAdd 0
    rw [show ideleClassNorm F h.val = 1 from h.property, Real.log_one]
  have hl : logNorm F (g * h.val) = logNorm F g := by
    simp only [logNorm, map_mul, hh, mul_one]
  simp only [orbitalSobolevMoment, hl, map_mul, Circle.coe_mul]
  ring

local instance orbitalClassMeasurable : MeasurableSpace (G F) := borel _
local instance orbitalClassBorel : BorelSpace (G F) := ⟨rfl⟩
local instance orbitalNormOneMeasurable : MeasurableSpace (normOneIdeleClass F) := borel _
local instance orbitalNormOneBorel : BorelSpace (normOneIdeleClass F) := ⟨rfl⟩

variable (μ : Measure (G F)) [μ.IsHaarMeasure]

/-- Haar measure on the idele class group pushes forward to a positive
multiple of Lebesgue measure under the logarithmic modulus. -/
theorem ideleClassLogNorm_map_haar :
    ∃ c : ℝ≥0, 0 < c ∧ μ.map (logNorm F) = c • volume := by
  letI : CompactSpace (normOneIdeleClass F) := normOneIdeleClass_compact F
  letI : LocallyCompactSpace (G F) := ideleClasses_locallyCompact (F := F)
  letI : SecondCountableTopology (NumberField.AdeleRing (𝓞 F) F) := adeles_secondCountable F
  letI : SecondCountableTopology (NumberField.AdeleRing (𝓞 F) F)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  letI : SecondCountableTopology (Idele F) := Units.isEmbedding_embedProduct.secondCountableTopology
  letI : SecondCountableTopology (G F) := TopologicalSpace.Quotient.secondCountableTopology
    (QuotientGroup.isOpenMap_coe (N := principalIdeles F))
  let ν : Measure (normOneIdeleClass F) := Measure.haarMeasure ⊤
  letI : ν.IsHaarMeasure := Measure.isHaarMeasure_haarMeasure ⊤
  letI : IsProbabilityMeasure ν := ⟨Measure.haarMeasure_self (K₀ := ⊤)⟩
  let σ := globalClassMeasure F ν
  letI : σ.IsHaarMeasure := globalClassMeasure_isHaar F ν
  have hμ : μ = Measure.haarScalarFactor μ σ • σ := Measure.isMulLeftInvariant_eq_smul μ σ
  have hc := Measure.haarScalarFactor_pos_of_isHaarMeasure μ σ
  have hl : Measurable (logNorm F) :=
    (show Continuous (logNorm F) from ideleClassLogNorm_continuous F).measurable
  have hmap : σ.map (logNorm F) = volume := by
    have hcoord : logNorm F ∘ ideleClassLogCoordinates F = Prod.fst :=
      funext (log_norm_coordinates F)
    change Measure.map (logNorm F) (Measure.map (ideleClassLogCoordinates F) (volume.prod ν)) = _
    rw [Measure.map_map hl (ideleClassLogCoordinates F).continuous.measurable, hcoord,
      Measure.map_fst_prod, measure_univ, one_smul]
  refine ⟨_, hc, ?_⟩
  calc
    μ.map (logNorm F) = (Measure.haarScalarFactor μ σ • σ).map (logNorm F) :=
      congrArg (Measure.map (logNorm F)) hμ
    _ = _ := by rw [Measure.map_smul, hmap]

private theorem integrable_comp_ideleClassLogNorm_iff {w : ℝ → ℝ} (hw : Measurable w) :
    Integrable (w ∘ logNorm F) μ ↔ Integrable w volume := by
  obtain ⟨c, hc, hmap⟩ := ideleClassLogNorm_map_haar F μ
  have hl : Measurable (logNorm F) :=
    (show Continuous (logNorm F) from ideleClassLogNorm_continuous F).measurable
  rw [← integrable_map_measure hw.aestronglyMeasurable hl.aemeasurable, hmap]
  exact integrable_smul_measure (by exact_mod_cast hc.ne') ENNReal.coe_ne_top

/-- The admissible orders are exactly those satisfying the strict
integrability threshold, including at odd integer Sobolev exponents. -/
theorem orbitalSobolevMoment_memLp_iff (χ : PontryaginDual (G F))
    {s : ℝ} (hs : 0 ≤ s) {z : ℂ} (hz : z.re = 0) (m : ℕ) :
    MemLp (orbitalSobolevMoment F χ s z m) 2 μ ↔ (m : ℝ) < (s - 1) / 2 := by
  let w (x : ℝ) := ‖x‖ ^ (2 * m) * (1 + ‖x‖ ^ 2) ^ (-s / 2)
  have he (g : G F) : ‖orbitalSobolevMoment F χ s z m g‖ ^ 2 = w (logNorm F g) := by
    let q := 1 + ‖logNorm F g‖ ^ 2
    have hq : 0 ≤ q := add_nonneg zero_le_one (sq_nonneg _)
    have hw : (q ^ (-s / 4)) ^ (2 : ℕ) = q ^ (-s / 2) := by
      rw [← Real.rpow_natCast (q ^ (-s / 4)) 2, ← Real.rpow_mul hq]
      congr 1
      push_cast
      ring
    rw [norm_orbitalSobolevMoment F χ s hz, mul_pow, ← pow_mul, mul_comm m 2, mul_comm]
    change ‖logNorm F g‖ ^ (2 * m) * (q ^ (-s / 4)) ^ (2 : ℕ) =
      ‖logNorm F g‖ ^ (2 * m) * q ^ (-s / 2)
    rw [hw]
  rw [memLp_two_iff_integrable_sq_norm
      (orbitalSobolevMoment_continuous F χ s z m).measurable.aestronglyMeasurable]
  simp only [he]
  exact (integrable_comp_ideleClassLogNorm_iff F μ (w := w) (by dsimp [w]; fun_prop)).trans
    ((integrable_logSobolevMoment_real hs m).trans ⟨fun h => by linarith, fun h => by linarith⟩)

/-- The norm bounds are uniform over all unitary characters and imaginary frequencies.
Only the Sobolev exponent and Haar normalization enter the constant. -/
theorem imaginaryOrbitalSobolevMoments_uniform_norm {s : ℝ} (hs : 1 < s) :
    ∃ C : ℝ, 0 < C ∧ ∀ (χ : PontryaginDual (G F)) (z : ℂ) (_ : z.re = 0)
      (m : ℕ) (_ : (m : ℝ) < (s - 1) / 2),
      ∃ hLp : MemLp (orbitalSobolevMoment F χ s z m) 2 μ,
        C⁻¹ ≤ ‖hLp.toLp _‖ ∧ ‖hLp.toLp _‖ ≤ C := by
  let energy (m : ℕ) : ℝ := ∫ g, ((1 + ‖logNorm F g‖ ^ 2) ^ (-s / 4) *
    ‖logNorm F g‖ ^ m) ^ 2 ∂μ
  let c (m : ℕ) := Real.sqrt (energy m)
  let N := ⌈(s - 1) / 2⌉₊
  have hc (m : ℕ) : 0 ≤ c m := Real.sqrt_nonneg _
  let C : ℝ := 1 + ∑ j ∈ Finset.range N, (c j + (c j)⁻¹)
  have hsum (j : ℕ) : 0 ≤ c j + (c j)⁻¹ := add_nonneg (hc j) (inv_nonneg.mpr (hc j))
  have hC : 0 < C := add_pos_of_pos_of_nonneg zero_lt_one (Finset.sum_nonneg fun j _ => hsum j)
  refine ⟨C, hC, fun χ z hz' m hm => ?_⟩
  let f := orbitalSobolevMoment F χ s z m
  have hLp : MemLp f 2 μ :=
    (orbitalSobolevMoment_memLp_iff F μ χ (by linarith) hz' m).mpr hm
  have hnorm : ‖hLp.toLp f‖ = c m := by
    have he : ‖hLp.toLp f‖ ^ 2 = energy m := by
      rw [norm_sq_toLp_two hLp]
      simp only [energy, f, norm_orbitalSobolevMoment F χ s hz']
    exact (Real.sqrt_sq (norm_nonneg _)).symm.trans (congrArg Real.sqrt he)
  have hpositive : 0 < c m := by
    rw [← hnorm]
    by_contra hzero
    have hzero' : hLp.toLp f = 0 :=
      norm_eq_zero.mp (le_antisymm (le_of_not_gt hzero) (norm_nonneg _))
    have hae : f =ᵐ[μ] (0 : G F → ℂ) := by
      have h := hLp.coeFn_toLp
      rw [hzero'] at h
      exact h.symm.trans (Lp.coeFn_zero ℂ 2 μ)
    have hfun := ((orbitalSobolevMoment_continuous F χ s z m).ae_eq_iff_eq
      (μ := μ) continuous_const).mp hae
    obtain ⟨g, hg⟩ := logNorm_surjective F 1
    have hfzero : ‖orbitalSobolevMoment F χ s z m g‖ = 0 := by
      rw [congrFun hfun g]
      exact norm_zero
    rw [norm_orbitalSobolevMoment F χ s hz', hg] at hfzero
    simp only [norm_one, one_pow, mul_one] at hfzero
    exact (Real.rpow_pos_of_pos (by norm_num) _).ne' hfzero
  have hmN : m ∈ Finset.range N := Finset.mem_range.mpr ((Nat.lt_ceil).mpr hm)
  have hle : c m + (c m)⁻¹ ≤ C :=
    (Finset.single_le_sum (fun j _ => hsum j) hmN).trans (le_add_of_nonneg_left zero_le_one)
  refine ⟨hLp, ?_⟩
  change C⁻¹ ≤ ‖hLp.toLp f‖ ∧ ‖hLp.toLp f‖ ≤ C
  rw [hnorm]
  exact ⟨(inv_le_comm₀ hC hpositive).mpr
    ((le_add_of_nonneg_left (hc m)).trans hle),
    (le_add_of_nonneg_right (inv_nonneg.mpr (hc m))).trans hle⟩

/-- Corrected Proposition 11.2.0.4 for the finite Euler product. -/
theorem orbitalSobolevMoments_uniform_norm (S : Finset (Place F))
    (χ : PontryaginDual (G F)) {s : ℝ} (hs : 1 < s) :
    ∃ C : ℝ, 0 < C ∧ ∀ (z : ℂ) (_ : orbitalEulerDenominator F S χ z = 0)
      (m : ℕ) (_ : m < analyticOrderNatAt (orbitalEulerDenominator F S χ) z)
      (_ : (m : ℝ) < (s - 1) / 2),
      ∃ hLp : MemLp (orbitalSobolevMoment F χ s z m) 2 μ,
        C⁻¹ ≤ ‖hLp.toLp _‖ ∧ ‖hLp.toLp _‖ ≤ C := by
  obtain ⟨C, hC, hnorm⟩ := imaginaryOrbitalSobolevMoments_uniform_norm F μ hs
  exact ⟨C, hC, fun z hz m _ hm => hnorm χ z (orbitalEulerDenominator_zero_re F S χ hz) m hm⟩

/-- The Sobolev vectors in (10.2.1.11) associated to zeros of the supplied
Hecke functions on the line of real part a. The normalized character
base points are supplied by B. -/
def spectralOrbitalSobolevFamily (B : Set (PontryaginDual (G F)))
    (L : PontryaginDual (G F) → ℂ → ℂ) (a s : ℝ) : Set (Lp ℂ 2 μ) :=
  {u | ∃ (χ : PontryaginDual (G F)) (_ : χ ∈ B) (t : ℝ)
      (_ : L χ ((a : ℂ) + (t : ℂ) * Complex.I) = 0) (m : ℕ)
      (_ : m < analyticOrderNatAt (L χ) ((a : ℂ) + (t : ℂ) * Complex.I))
      (_ : (m : ℝ) < (s - 1) / 2)
      (hLp : MemLp (orbitalSobolevMoment F χ s ((t : ℂ) * Complex.I) m) 2 μ),
      u = hLp.toLp _}

/-- Corrected Proposition 10.2.1.3. A single norm collar works for the zeros
on every vertical line and all character components. The open-ball
conclusion applies when the spectral family is nonempty. -/
theorem spectralOrbitalSobolevFamily_uniform_norm (B : Set (PontryaginDual (G F)))
    (L : PontryaginDual (G F) → ℂ → ℂ) {s : ℝ} (hs : 1 < s) :
    ∃ C : ℝ, 0 < C ∧
      (∀ (a : ℝ) (χ : PontryaginDual (G F)), χ ∈ B → ∀ (t : ℝ),
        L χ ((a : ℂ) + (t : ℂ) * Complex.I) = 0 → ∀ (m : ℕ),
        m < analyticOrderNatAt (L χ) ((a : ℂ) + (t : ℂ) * Complex.I) →
        (m : ℝ) < (s - 1) / 2 →
        ∃ hLp : MemLp (orbitalSobolevMoment F χ s ((t : ℂ) * Complex.I) m) 2 μ,
          C⁻¹ ≤ ‖hLp.toLp _‖ ∧ ‖hLp.toLp _‖ ≤ C) ∧
      ∀ a : ℝ,
        (spectralOrbitalSobolevFamily F μ B L a s) ⊆ {u | C⁻¹ ≤ ‖u‖ ∧ ‖u‖ ≤ C} ∧
        (¬ spectralOrbitalSobolevFamily F μ B L a s ⊆ Metric.ball 0 C⁻¹ ↔
          (spectralOrbitalSobolevFamily F μ B L a s).Nonempty) := by
  obtain ⟨C, hC, hnorm⟩ := imaginaryOrbitalSobolevMoments_uniform_norm F μ hs
  have hi (t : ℝ) : ((t : ℂ) * Complex.I).re = 0 := by simp [Complex.mul_re]
  refine ⟨C, hC, fun a χ _ t _ m _ hm => hnorm χ _ (hi t) m hm, fun a => ?_⟩
  have hsubset : spectralOrbitalSobolevFamily F μ B L a s ⊆ {u | C⁻¹ ≤ ‖u‖ ∧ ‖u‖ ≤ C} := by
    rintro u ⟨χ, _, t, _, m, _, hm, hLp, rfl⟩
    obtain ⟨hLp', h⟩ := hnorm χ _ (hi t) m hm
    exact h
  refine ⟨hsubset, ⟨fun h => ?_, ?_⟩⟩
  · obtain ⟨u, hu, _⟩ := not_subset.mp h
    exact ⟨u, hu⟩
  · rintro ⟨u, hu⟩ hball
    have hu' := hball hu
    rw [Metric.mem_ball, dist_zero_right] at hu'
    exact (not_lt.mpr (hsubset hu).1) hu'

omit [μ.IsHaarMeasure] in
/-- On a line to the right of one the actual finite Euler product supplies
no spectral moments. A continued Hecke family agreeing there has the same
empty family on that line. -/
theorem spectralOrbitalSobolevFamily_euler_halfPlane_empty
    (B : Set (PontryaginDual (G F))) (L : PontryaginDual (G F) → ℂ → ℂ)
    (hL : ∀ χ ∈ B, ∀ z : ℂ, 1 < z.re → L χ z =
      ∏' v, heckeEulerFactor F (heckeEulerCoefficient F χ (chosenFiniteUniformizer F)) v z)
    {a : ℝ} (ha : 1 < a) (s : ℝ) :
    spectralOrbitalSobolevFamily F μ B L a s = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro u ⟨χ, hχ, t, hz, _⟩
  have h : 1 < ((a : ℂ) + (t : ℂ) * Complex.I).re := by
    simpa [Complex.add_re, Complex.mul_re] using ha
  rw [hL χ hχ _ h] at hz
  exact heckeEulerProduct_ne_zero F _ (norm_heckeEulerCoefficient_le_one F χ _) h hz

/-- For a nonempty set of finite places the family is nonempty, so the lower
bound from Proposition 11.2.0.4 excludes containment in the open ball. -/
theorem orbitalSobolevMoments_uniform_norm_not_in_open_ball (S : Finset (Place F))
    (hS : S.Nonempty) (χ : PontryaginDual (G F)) {s : ℝ} (hs : 1 < s) :
    ∃ C : ℝ, 0 < C ∧
      (∀ (z : ℂ), orbitalEulerDenominator F S χ z = 0 → ∀ (m : ℕ),
        m < analyticOrderNatAt (orbitalEulerDenominator F S χ) z → (m : ℝ) < (s - 1) / 2 →
        ∃ hLp : MemLp (orbitalSobolevMoment F χ s z m) 2 μ,
          C⁻¹ ≤ ‖hLp.toLp _‖ ∧ ‖hLp.toLp _‖ ≤ C) ∧
      ∃ (z : ℂ) (_ : orbitalEulerDenominator F S χ z = 0)
        (_ : 0 < analyticOrderNatAt (orbitalEulerDenominator F S χ) z)
        (hLp : MemLp (orbitalSobolevMoment F χ s z 0) 2 μ),
        hLp.toLp _ ∉ Metric.ball (0 : Lp ℂ 2 μ) C⁻¹ := by
  obtain ⟨C, hC, hnorm⟩ := orbitalSobolevMoments_uniform_norm F μ S χ hs
  refine ⟨C, hC, hnorm, ?_⟩
  obtain ⟨z, hz, hm⟩ := orbitalEulerDenominator_has_zero F S hS χ
  obtain ⟨hf, hbound, _⟩ := hnorm z hz 0 hm (by push_cast; linarith)
  refine ⟨z, hz, hm, hf, ?_⟩
  rw [Metric.mem_ball, dist_zero_right]
  exact not_lt.mpr hbound

/-- With two or more finite places, the printed cutoff at (s=3) admits
the first logarithmic moment at the trivial Euler zero. Its squared norm
has a divergent tail. -/
theorem orbitalSobolevMoment_printed_endpoint_fails (S : Finset (Place F)) (hS : 2 ≤ S.card) :
    orbitalEulerDenominator F S 1 0 = 0 ∧
      1 < analyticOrderNatAt (orbitalEulerDenominator F S 1) 0 ∧
      ¬ MemLp (orbitalSobolevMoment F 1 3 0 1) 2 μ := by
  have hne : S ≠ ∅ := by
    intro h
    simp [h] at hS
  obtain ⟨hz, horder⟩ := (orbitalEulerDenominator_trivial_order_at_zero F S).resolve_right hne
  refine ⟨hz, by omega, ?_⟩
  rw [orbitalSobolevMoment_memLp_iff F μ 1 (by norm_num) Complex.zero_re]
  norm_num

/-- The primes two and three over the rational field give a concrete
instance of the endpoint failure. -/
theorem orbitalSobolevMoment_rational_endpoint (ν : Measure (IdeleClass ℚ)) [ν.IsHaarMeasure] :
    ∃ S : Finset (Place ℚ), S.card = 2 ∧
      (∀ v ∈ S, unramifiedFiniteCharacter ℚ 1 v) ∧
      orbitalEulerDenominator ℚ S 1 0 = 0 ∧
      analyticOrderNatAt (orbitalEulerDenominator ℚ S 1) 0 = 2 ∧
      ¬ MemLp (orbitalSobolevMoment ℚ 1 3 0 1) 2 ν := by
  let e : Place ℚ ≃ Nat.Primes := Rat.HeightOneSpectrum.primesEquiv
  let p₂ : Nat.Primes := ⟨2, Nat.prime_two⟩
  let p₃ : Nat.Primes := ⟨3, Nat.prime_three⟩
  let v₂ := e.symm p₂
  let v₃ := e.symm p₃
  have hne : v₂ ≠ v₃ := by
    intro h
    have h' := e.symm.injective h
    exact (by decide : (2 : ℕ) ≠ 3) (congrArg Subtype.val h')
  have hc : ({v₂, v₃} : Finset (Place ℚ)).card = 2 := by simp [hne]
  have hn : ({v₂, v₃} : Finset (Place ℚ)) ≠ ∅ := by simp
  refine ⟨{v₂, v₃}, hc, fun v _ u _ => ?_, ?_⟩
  · simp
  · obtain ⟨hz, horder⟩ := (orbitalEulerDenominator_trivial_order_at_zero ℚ _).resolve_right hn
    exact ⟨hz, horder.trans hc, (orbitalSobolevMoment_printed_endpoint_fails ℚ ν _ hc.ge).2.2⟩

end

end Masullo
