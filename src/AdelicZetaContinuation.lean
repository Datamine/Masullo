import AdelicZetaUnfolding
import AdelicHomogeneousSmooth
import OneParameterFlows
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Meromorphic.Order

open Bornology Filter Function MeasureTheory NumberField Set Topology
open scoped Classical ENNReal NumberField

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

private abbrev K := normOneIdeleClass F
private abbrev Q := IdeleClass F
private abbrev G := Idele F

local instance : MeasurableSpace (K F) := borel _
local instance : BorelSpace (K F) := ⟨rfl⟩
local instance : MeasurableSpace (Q F) := borel _
local instance : BorelSpace (Q F) := ⟨rfl⟩
local instance : MeasurableSpace (G F) := borel _
local instance : BorelSpace (G F) := ⟨rfl⟩

private abbrev ray (t : ℝ) : Q F := ideleClassExpSection F (Multiplicative.ofAdd t)
private abbrev low : Set (Q F) := {q | ideleClassNorm F q < 1}
private abbrev high : Set (Q F) := {q | 1 ≤ ideleClassNorm F q}
private abbrev strictHigh : Set (Q F) := {q | 1 < ideleClassNorm F q}

private theorem measurable_low : MeasurableSet (low F) :=
  (isOpen_lt (ideleClassNorm_continuous F) continuous_const).measurableSet

private theorem measurable_high : MeasurableSet (high F) :=
  (isClosed_le continuous_const (ideleClassNorm_continuous F)).measurableSet

private theorem measurable_strictHigh : MeasurableSet (strictHigh F) :=
  (isOpen_lt continuous_const (ideleClassNorm_continuous F)).measurableSet

local instance : T1Space (Q F) := QuotientGroup.t1Space_iff.mpr principalIdeles_closed
local instance : LocallyCompactSpace (Q F) := by
  letI : LocallyCompactSpace (G F) := ideles_locallyCompact
  exact (QuotientGroup.isOpenQuotientMap_mk (N := principalIdeles F)).locallyCompactSpace
local instance : SecondCountableTopology (Q F) := by
  letI : SecondCountableTopology (Adeles F) := adeles_secondCountable F
  letI : SecondCountableTopology (Adeles F)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  letI : SecondCountableTopology (G F) := Units.isEmbedding_embedProduct.secondCountableTopology
  exact QuotientGroup.isOpenQuotientMap_mk.isQuotientMap.secondCountableTopology
    QuotientGroup.isOpenQuotientMap_mk.isOpenMap

/-- Haar measure on the compact norm-one class group is regular. -/
theorem normOneIdeleClass_haar_regular (ν : Measure (K F)) [ν.IsHaarMeasure] :
    ν.Regular := by
  letI := normOneIdeleClass_compact F
  letI : T2Space (K F) := inferInstance
  letI : SecondCountableTopology (K F) := IsEmbedding.subtypeVal.secondCountableTopology
  exact Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure ν

private theorem globalClassMeasure_modulus_one_null (ν : Measure (K F)) [ν.IsHaarMeasure] :
    (globalClassMeasure F ν) {q | ideleClassNorm F q = 1} = 0 := by
  letI := normOneIdeleClass_compact F
  letI : IsFiniteMeasure ν := ⟨isCompact_univ.measure_lt_top⟩
  let e := ideleClassLogCoordinates F
  have hs : MeasurableSet {q | ideleClassNorm F q = 1} :=
    (isClosed_eq (ideleClassNorm_continuous F) continuous_const).measurableSet
  change ((volume.prod ν).map e) _ = _
  rw [Measure.map_apply e.continuous.measurable hs]
  have he : e ⁻¹' {q | ideleClassNorm F q = 1} = ({0} : Set ℝ) ×ˢ (univ : Set (K F)) := by
    ext p
    change ideleClassNorm F (e p) = 1 ↔ p.1 = 0 ∧ p.2 ∈ (univ : Set (K F))
    simp only [mem_univ, and_true]
    rw [← log_norm_coordinates F p, Real.log_eq_zero]
    have hp := ideleClassNorm_pos F (e p)
    constructor
    · exact fun h => Or.inr (Or.inl h)
    · rintro (h | h | h)
      · exact (hp.ne' h).elim
      · exact h
      · linarith
  rw [he, Measure.prod_prod, measure_singleton, zero_mul]

private theorem class_restrict_high_eq_strict (ν : Measure (K F)) [ν.IsHaarMeasure] :
    (globalClassMeasure F ν).restrict (high F) =
      (globalClassMeasure F ν).restrict (strictHigh F) := by
  apply Measure.restrict_congr_set
  have he : ∀ᵐ q ∂globalClassMeasure F ν, ideleClassNorm F q ≠ 1 :=
    ae_iff.mpr (by simpa only [ne_eq, not_not] using globalClassMeasure_modulus_one_null F ν)
  filter_upwards [he] with q hq
  change (1 ≤ ideleClassNorm F q) = (1 < ideleClassNorm F q)
  exact propext ⟨fun h => lt_of_le_of_ne h (Ne.symm hq), le_of_lt⟩

private theorem class_inv_preimage_strictHigh :
    (Inv.inv : Q F → Q F) ⁻¹' strictHigh F = low F := by
  ext q
  change 1 < ideleClassNorm F q⁻¹ ↔ ideleClassNorm F q < 1
  rw [map_inv]
  exact one_lt_inv₀ (ideleClassNorm_pos F q)

private theorem class_setIntegral_inv_low (ν : Measure (K F)) [ν.IsHaarMeasure] (f : Q F → ℂ) :
    (∫ q in low F, f q⁻¹ ∂globalClassMeasure F ν) =
      ∫ q in high F, f q ∂globalClassMeasure F ν := by
  let μ := globalClassMeasure F ν
  letI : μ.IsHaarMeasure := globalClassMeasure_isHaar F ν
  letI : μ.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _
  rw [show μ.restrict (high F) = μ.restrict (strictHigh F) from
    class_restrict_high_eq_strict F ν]
  have he := (Measure.measurePreserving_inv μ).setIntegral_preimage_emb
    (MeasurableEquiv.inv (Q F)).measurableEmbedding f (strictHigh F)
  rw [class_inv_preimage_strictHigh F] at he
  exact he

/-- The imaginary frequency contributed by a unitary base character along the
canonical norm section. Its real part is zero. -/
theorem unitary_ideleClass_ray_frequency (χ : IdeleQuasiCharacter F) (hχ : IsUnitary F χ) :
    ∃ κ : ℂ, κ.re = 0 ∧ ∀ t : ℝ, (χ (ray F t) : ℂ) = Complex.exp (κ * (t : ℂ)) := by
  let γ := (restrictToNormRay F χ).toMonoidHom
  obtain ⟨κ, hκ, _⟩ := complex_oneParameter_exp γ
    (Units.continuous_val.comp ((map_continuous χ).comp
      ((ideleClassExpSection_continuous F).comp continuous_ofAdd)))
  refine ⟨κ, ?_, hκ⟩
  have h := hχ (ray F 1)
  change ‖(γ (Multiplicative.ofAdd 1) : ℂ)‖ = 1 at h
  rw [hκ, Complex.ofReal_one, mul_one, Complex.norm_exp, ← Real.exp_zero] at h
  exact Real.exp_injective h

/-- At the lower end, the Mellin integral of a pure quasi-character is
its compact-character integral times the reciprocal radial exponent. -/
theorem ideleNormTwist_lower_integral (ν : Measure (K F)) [ν.IsHaarMeasure]
    (χ : IdeleQuasiCharacter F) {κ : ℂ}
    (hκ : ∀ t : ℝ, (χ (ray F t) : ℂ) = Complex.exp (κ * (t : ℂ)))
    (s : ℂ) (hs : 0 < (s + κ).re) :
    IntegrableOn (fun q => (ideleNormTwist F χ s q : ℂ)) (low F) (globalClassMeasure F ν) ∧
      (∫ q in low F, (ideleNormTwist F χ s q : ℂ) ∂globalClassMeasure F ν) =
        (∫ k : K F, (χ k.val : ℂ) ∂ν) / (s + κ) := by
  letI := normOneIdeleClass_compact F
  letI : IsFiniteMeasure ν := ⟨isCompact_univ.measure_lt_top⟩
  let e := ideleClassLogCoordinates F
  let a (t : ℝ) := Complex.exp ((s + κ) * (t : ℂ))
  let b (k : K F) := (χ k.val : ℂ)
  let p (q : Q F) := (ideleNormTwist F χ s q : ℂ)
  have hp (x : ℝ × K F) : p (e x) = a x.1 * b x.2 := by
    change ((χ (e x) : ℂ) * Complex.exp (s * (Real.log (ideleClassNorm F (e x)) : ℂ))) = _
    rw [log_norm_coordinates F x]
    have hq : e x = x.2.val * ray F x.1 := rfl
    rw [hq, map_mul, Units.val_mul, hκ]
    dsimp only [a, b]
    rw [add_mul, Complex.exp_add]
    ring
  have he : e ⁻¹' low F = Iio (0 : ℝ) ×ˢ (univ : Set (K F)) := by
    ext x
    change ideleClassNorm F (e x) < 1 ↔ x.1 < 0 ∧ x.2 ∈ (univ : Set (K F))
    simp only [mem_univ, and_true]
    rw [← log_norm_coordinates F x, Real.log_neg_iff (ideleClassNorm_pos F (e x))]
  have ha : IntegrableOn a (Iio (0 : ℝ)) :=
    (integrableOn_exp_mul_complex_Iic hs 0).mono_set Iio_subset_Iic_self
  have hbC : Continuous b :=
    (Units.continuous_val.comp (map_continuous χ)).comp continuous_subtype_val
  have hb : Integrable b ν :=
    hbC.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hmap : ((volume.prod ν).map e).restrict (low F) =
      Measure.map e ((volume.restrict (Iio (0 : ℝ))).prod ν) := by
    rw [Measure.restrict_prod_eq_prod_univ, ← he, Measure.restrict_map e.continuous.measurable (measurable_low F)]
  constructor
  · change Integrable p (((volume.prod ν).map e).restrict (low F))
    rw [hmap]
    apply e.toMeasurableEquiv.measurableEmbedding.integrable_map_iff.mpr
    change Integrable (fun x => p (e x)) _
    simpa only [hp] using ha.mul_prod hb
  · change (∫ q, p q ∂((volume.prod ν).map e).restrict (low F)) = _
    rw [hmap]
    change (∫ q, p q ∂Measure.map e.toMeasurableEquiv _) = _
    rw [integral_map_equiv]
    change (∫ x, p (e x) ∂(volume.restrict (Iio (0 : ℝ))).prod ν) = _
    simp_rw [hp]
    rw [integral_prod_mul]
    have hA : (∫ t : ℝ in Iio 0, a t) = (s + κ)⁻¹ := by
      rw [setIntegral_congr_set Iio_ae_eq_Iic]
      simpa only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_div] using
        (integral_exp_mul_complex_Iic hs 0)
    rw [hA]
    rw [div_eq_mul_inv, mul_comm]


private theorem ideleNormTwist_shift_down (χ : IdeleQuasiCharacter F) (s : ℂ) (q : Q F) :
    (ideleNormTwist F χ (s - 1) q : ℂ) =
      ((ideleClassNorm F q : ℝ) : ℂ)⁻¹ * (ideleNormTwist F χ s q : ℂ) := by
  let m := ideleClassNorm F q
  let l := Real.log m
  have hm : 0 < m := ideleClassNorm_pos F q
  have he : ((m : ℂ)⁻¹) = Complex.exp (-(l : ℂ)) := by
    rw [Complex.exp_neg, ← Complex.ofReal_exp, show Real.exp l = m from Real.exp_log hm]
  change (χ q : ℂ) * Complex.exp ((s - 1) * (l : ℂ)) =
    (m : ℂ)⁻¹ * ((χ q : ℂ) * Complex.exp (s * (l : ℂ)))
  rw [he, sub_mul, one_mul, sub_eq_add_neg, Complex.exp_add]
  ring

private theorem ideleNormTwist_reflect (χ : IdeleQuasiCharacter F) (s : ℂ) (q : Q F) :
    (ideleNormTwist F χ⁻¹ (1 - s) q⁻¹ : ℂ) = (ideleNormTwist F χ (s - 1) q : ℂ) := by
  change ((χ q⁻¹)⁻¹ : ℂˣ).val * ideleNormPower F (1 - s) q⁻¹ =
    (χ q : ℂ) * ideleNormPower F (s - 1) q
  rw [map_inv χ, inv_inv]
  unfold ideleNormPower
  rw [map_inv (ideleClassNorm F), Real.log_inv, Complex.ofReal_neg]
  congr 2
  ring

private theorem upper_inv_integrable (ν : Measure (K F)) [ν.IsHaarMeasure]
    {f : Q F → ℂ} (hf : IntegrableOn f (high F) (globalClassMeasure F ν)) :
    IntegrableOn (fun q => f q⁻¹) (low F) (globalClassMeasure F ν) := by
  let μ := globalClassMeasure F ν
  letI : μ.IsHaarMeasure := globalClassMeasure_isHaar F ν
  letI : μ.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _
  change Integrable f (μ.restrict (high F)) at hf
  rw [show μ.restrict (high F) = μ.restrict (strictHigh F) from
    class_restrict_high_eq_strict F ν] at hf
  have he := (Measure.measurePreserving_inv μ).restrict_preimage_emb
    (MeasurableEquiv.inv (Q F)).measurableEmbedding (strictHigh F)
  rw [class_inv_preimage_strictHigh F] at he
  exact he.integrable_comp_of_integrable hf

/-- The split Tate formula. The upper theta integrals are entire. The two
rational terms arise from the zero evaluations in Riemann–Roch. -/
def globalZetaContinued (ν : Measure (K F)) (f : GlobalBruhat F)
    (χ : IdeleQuasiCharacter F) (κ s : ℂ) : ℂ :=
  let a := ∫ k : K F, (χ k.val : ℂ) ∂ν
  thetaZetaUpper F ν f χ s +
    thetaZetaUpper F ν (GlobalBruhat.fourier F f) χ⁻¹ (1 - s) +
    a * (GlobalBruhat.algebraicEquiv F (GlobalBruhat.fourier F f)).val 0 / (s + κ - 1) -
    a * (GlobalBruhat.algebraicEquiv F f).val 0 / (s + κ)

/-- The split formula agrees with the ordinary class integral on its initial
half-plane, for all number fields, test functions, and unitary components. -/
theorem globalZetaContinued_eq_theta (ν : Measure (K F)) [ν.IsHaarMeasure]
    (f : GlobalBruhat F) (χ : IdeleQuasiCharacter F) (hχ : IsUnitary F χ)
    {κ : ℂ} (hκ₀ : κ.re = 0)
    (hκ : ∀ t : ℝ, (χ (ray F t) : ℂ) = Complex.exp (κ * (t : ℂ)))
    (s : ℂ) (hs : 1 < s.re) :
    globalZetaContinued F ν f χ κ s =
      thetaZetaIntegral F (globalClassMeasure F ν) (GlobalBruhat.algebraicEquiv F f).val χ s := by
  let u := GlobalBruhat.algebraicEquiv F f
  let f' := GlobalBruhat.fourier F f
  let v := GlobalBruhat.algebraicEquiv F f'
  let μ := globalClassMeasure F ν
  let w (z : ℂ) (q : Q F) := (ideleNormTwist F χ z q : ℂ)
  let k (q : Q F) := adelicTheta F u.val q * w s q
  let k' (q : Q F) := adelicTheta F v.val q * (ideleNormTwist F χ⁻¹ (1 - s) q : ℂ)
  have hinv : IsUnitary F χ⁻¹ := fun q => by
    change ‖((χ q)⁻¹ : ℂˣ).val‖ = 1
    rw [Units.val_inv_eq_inv_val, norm_inv, hχ, inv_one]
  have hupper := (thetaZetaUpper_integrable_analytic F ν f' χ⁻¹ hinv).1 (1 - s)
  have hki : IntegrableOn (fun q => k' q⁻¹) (low F) μ := upper_inv_integrable F ν hupper
  have hsp : 0 < (s + κ).re := by rw [Complex.add_re, hκ₀, add_zero]; linarith
  have hsm : 0 < (s - 1 + κ).re := by
    simp only [Complex.add_re, Complex.sub_re, Complex.one_re, hκ₀, add_zero]
    linarith
  obtain ⟨h0I, h0⟩ := ideleNormTwist_lower_integral F ν χ hκ s hsp
  obtain ⟨h1I, h1⟩ := ideleNormTwist_lower_integral F ν χ hκ (s - 1) hsm
  have hlu (q : Q F) : k q = k' q⁻¹ + v.val 0 * w (s - 1) q - u.val 0 * w s q := by
    have hRR := congrFun (adelicTheta_riemannRoch F u.property).2 q
    rw [← GlobalBruhat.fourier_apply F f] at hRR
    change adelicTheta F u.val q =
      (ideleClassNorm F q)⁻¹ • adelicTheta F v.val q⁻¹ +
        (ideleClassNorm F q)⁻¹ • v.val 0 - u.val 0 at hRR
    dsimp only [k, k', w]
    rw [hRR, ideleNormTwist_reflect, ideleNormTwist_shift_down]
    simp only [Complex.real_smul, Complex.ofReal_inv]
    ring
  have hlu' : k = ((fun q => k' q⁻¹) + (fun q => v.val 0 * w (s - 1) q)) -
      (fun q => u.val 0 * w s q) := funext hlu
  have h1I' : IntegrableOn (fun q => v.val 0 * w (s - 1) q) (low F) μ := h1I.const_mul _
  have h0I' : IntegrableOn (fun q => u.val 0 * w s q) (low F) μ := h0I.const_mul _
  have hL : (∫ q in low F, k q ∂μ) =
      thetaZetaUpper F ν f' χ⁻¹ (1 - s) +
      v.val 0 * ((∫ k : K F, (χ k.val : ℂ) ∂ν) / (s - 1 + κ)) -
      u.val 0 * ((∫ k : K F, (χ k.val : ℂ) ∂ν) / (s + κ)) := by
    rw [hlu']
    calc
      _ = (∫ q in low F, k' q⁻¹ ∂μ) + (∫ q in low F, v.val 0 * w (s - 1) q ∂μ) -
          (∫ q in low F, u.val 0 * w s q ∂μ) :=
        (integral_sub (hki.add h1I') h0I').trans
          (congrArg (· - (∫ q in low F, u.val 0 * w s q ∂μ)) (integral_add hki h1I'))
      _ = _ := by
        simp only [integral_const_mul]
        have hupper' : (∫ q in low F, k' q⁻¹ ∂μ) =
            thetaZetaUpper F ν f' χ⁻¹ (1 - s) :=
          class_setIntegral_inv_low F ν k'
        rw [hupper']
        change thetaZetaUpper F ν f' χ⁻¹ (1 - s) +
          v.val 0 * (∫ q in low F, (ideleNormTwist F χ (s - 1) q : ℂ) ∂μ) -
          u.val 0 * (∫ q in low F, (ideleNormTwist F χ s q : ℂ) ∂μ) = _
        rw [h0, h1]
  have hhi : IntegrableOn k (high F) μ :=
    (thetaZetaUpper_integrable_analytic F ν f χ hχ).1 s
  have hli : IntegrableOn k (low F) μ := by
    rw [hlu']
    exact (hki.add h1I').sub h0I'
  have hcompl : (high F)ᶜ = low F := by
    ext q
    change (¬ 1 ≤ ideleClassNorm F q) ↔ ideleClassNorm F q < 1
    exact not_le
  have hk : Integrable k μ := integrableOn_univ.mp (by
    have hh := hhi.union hli
    rwa [← hcompl, union_compl_self] at hh)
  change globalZetaContinued F ν f χ κ s = ∫ q, k q ∂μ
  rw [← integral_add_compl (measurable_high F) hk, hcompl, hL]
  change _ = thetaZetaUpper F ν f χ s + _
  unfold globalZetaContinued
  rw [show s - 1 + κ = s + κ - 1 by ring]
  simp only [div_eq_mul_inv, f', u, v]
  ring

/-- The continuation agrees with the idelic integral on its convergence half-plane. -/
theorem globalZetaContinued_eq_idelic (μ : Measure (G F)) [μ.IsHaarMeasure]
    (ν : Measure (K F)) [ν.IsHaarMeasure]
    (hν : IsWeilQuotientMeasure (principalIdeles F) μ Measure.count (globalClassMeasure F ν))
    (f : GlobalBruhat F) (χ : IdeleQuasiCharacter F) (hχ : IsUnitary F χ)
    {κ : ℂ} (hκ₀ : κ.re = 0)
    (hκ : ∀ t : ℝ, (χ (ray F t) : ℂ) = Complex.exp (κ * (t : ℂ)))
    (s : ℂ) (hs : 1 < s.re) :
    globalZetaContinued F ν f χ κ s =
      idelicZetaIntegral F μ (GlobalBruhat.algebraicEquiv F f).val χ s :=
  (globalZetaContinued_eq_theta F ν f χ hχ hκ₀ hκ s hs).trans
    (idelicZeta_integrable_eq_theta F μ ν hν f χ hχ s hs).2.symm

private theorem unitary_inv (χ : IdeleQuasiCharacter F) (hχ : IsUnitary F χ) :
    IsUnitary F χ⁻¹ := fun q => by
  change ‖((χ q)⁻¹ : ℂˣ).val‖ = 1
  rw [Units.val_inv_eq_inv_val, norm_inv, hχ, inv_one]

private theorem globalZeta_entire_part (ν : Measure (K F)) [ν.IsHaarMeasure]
    (f : GlobalBruhat F) (χ : IdeleQuasiCharacter F) (hχ : IsUnitary F χ) (z : ℂ) :
    AnalyticAt ℂ (fun s => thetaZetaUpper F ν f χ s +
      thetaZetaUpper F ν (GlobalBruhat.fourier F f) χ⁻¹ (1 - s)) z := by
  have h₁ := (thetaZetaUpper_integrable_analytic F ν f χ hχ).2 z trivial
  have h₂ := (thetaZetaUpper_integrable_analytic F ν (GlobalBruhat.fourier F f)
    χ⁻¹ (unitary_inv F χ hχ)).2 (1 - z) trivial
  have ha : AnalyticAt ℂ (fun s : ℂ => 1 - s) z := analyticAt_const.sub analyticAt_id
  exact h₁.add (h₂.comp ha)

/-- The two rational terms give a meromorphic function on each component. -/
theorem globalZetaContinued_meromorphic (ν : Measure (K F)) [ν.IsHaarMeasure]
    (f : GlobalBruhat F) (χ : IdeleQuasiCharacter F) (hχ : IsUnitary F χ) (κ : ℂ) :
    MeromorphicOn (globalZetaContinued F ν f χ κ) univ := by
  intro z _
  let a := ∫ k : K F, (χ k.val : ℂ) ∂ν
  let u := (GlobalBruhat.algebraicEquiv F f).val
  let v := (GlobalBruhat.algebraicEquiv F (GlobalBruhat.fourier F f)).val
  have h₀ : MeromorphicAt (fun s : ℂ => s + κ) z := (MeromorphicAt.id z).add (.const _ z)
  have h₁ : MeromorphicAt (fun s : ℂ => s + κ - 1) z := h₀.sub (.const _ z)
  exact ((globalZeta_entire_part F ν f χ hχ z).meromorphicAt.add
    ((MeromorphicAt.const (a * v 0) z).div h₁)).sub ((MeromorphicAt.const (a * u 0) z).div h₀)

/-- The continuation is analytic away from its two possible poles. -/
theorem globalZetaContinued_analyticAt (ν : Measure (K F)) [ν.IsHaarMeasure]
    (f : GlobalBruhat F) (χ : IdeleQuasiCharacter F) (hχ : IsUnitary F χ)
    (κ z : ℂ) (h₀ : z + κ ≠ 0) (h₁ : z + κ - 1 ≠ 0) :
    AnalyticAt ℂ (globalZetaContinued F ν f χ κ) z := by
  have hz₀ : AnalyticAt ℂ (fun s : ℂ => s + κ) z := analyticAt_id.add analyticAt_const
  exact ((globalZeta_entire_part F ν f χ hχ z).add
    (analyticAt_const.div (hz₀.sub analyticAt_const) h₁)).sub (analyticAt_const.div hz₀ h₀)

private theorem compactCharacterIntegral_trivial (ν : Measure (K F))
    (χ : IdeleQuasiCharacter F) (h : ∀ k : K F, χ k.val = 1) :
    (∫ k : K F, (χ k.val : ℂ) ∂ν) = (ν.real univ : ℂ) := by
  simp only [h, Units.val_one, integral_const, Complex.real_smul, mul_one]

/-- Compact orthogonality removes both polar coefficients when the restriction
of the base character is nontrivial. -/
theorem compactCharacterIntegral_zero (ν : Measure (K F)) [ν.IsHaarMeasure]
    (χ : IdeleQuasiCharacter F) {k₀ : K F} (h : χ k₀.val ≠ 1) :
    (∫ k : K F, (χ k.val : ℂ) ∂ν) = 0 := by
  have hk : (χ k₀.val : ℂ) ≠ 1 := fun he => h (Units.ext he)
  have he := integral_mul_left_eq_self (μ := ν) (fun k : K F => (χ k.val : ℂ)) k₀
  simp only [Subgroup.coe_mul, map_mul, Units.val_mul, integral_const_mul] at he
  let a := ∫ k : K F, (χ k.val : ℂ) ∂ν
  have hzero : ((χ k₀.val : ℂ) - 1) * a = 0 := by
    change (χ k₀.val : ℂ) * a = a at he
    rw [sub_mul, one_mul, he, sub_self]
  exact (mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr hk)

private theorem compactCharacterIntegral_inv (ν : Measure (K F)) [ν.IsHaarMeasure]
    (χ : IdeleQuasiCharacter F) :
    (∫ k : K F, (χ⁻¹ k.val : ℂ) ∂ν) = ∫ k : K F, (χ k.val : ℂ) ∂ν := by
  by_cases h : ∀ k : K F, χ k.val = 1
  · rw [compactCharacterIntegral_trivial F ν χ h]
    apply compactCharacterIntegral_trivial F ν χ⁻¹
    intro k
    change (χ k.val)⁻¹ = 1
    rw [h k, inv_one]
  · obtain ⟨k, hk⟩ := not_forall.mp h
    have hk' : χ⁻¹ k.val ≠ 1 := by
      change (χ k.val)⁻¹ ≠ 1
      exact fun he => hk (inv_eq_one.mp he)
    rw [compactCharacterIntegral_zero F ν χ hk, compactCharacterIntegral_zero F ν χ⁻¹ hk']

/-- The continued functional equation under reflection of the spectral parameter. -/
theorem globalZetaContinued_functionalEquation (ν : Measure (K F)) [ν.IsHaarMeasure]
    (f : GlobalBruhat F) (χ : IdeleQuasiCharacter F) (κ s : ℂ) :
    globalZetaContinued F ν f χ κ s =
      globalZetaContinued F ν (GlobalBruhat.fourier F f) χ⁻¹ (-κ) (1 - s) := by
  have he := adelicTheta_fourier_fourier F f
  let f' := GlobalBruhat.fourier F f
  let f'' := GlobalBruhat.fourier F f'
  let u := (GlobalBruhat.algebraicEquiv F f).val
  let w := (GlobalBruhat.algebraicEquiv F f'').val
  have he₀ : w 0 = u 0 := he.1
  have heθ : adelicTheta F w = adelicTheta F u := he.2
  have hU : thetaZetaUpper F ν f'' χ s = thetaZetaUpper F ν f χ s := by
    unfold thetaZetaUpper
    change (∫ q in high F, adelicTheta F w q * (ideleNormTwist F χ s q : ℂ)
      ∂globalClassMeasure F ν) = _
    rw [heθ]
  unfold globalZetaContinued
  have h₁ : 1 - (1 - s) = s := by ring
  have h₂ : 1 - s + -κ - 1 = -(s + κ) := by ring
  have h₃ : 1 - s + -κ = -(s + κ - 1) := by ring
  have hχ : χ⁻¹⁻¹ = χ := inv_inv χ
  dsimp only
  rw [hχ, h₁, h₂, h₃, compactCharacterIntegral_inv F ν χ]
  change _ = _ + thetaZetaUpper F ν f'' χ s + _ * w 0 / _ - _
  rw [hU, he₀]
  simp only [div_eq_mul_inv, inv_neg, mul_neg]
  ring

private theorem tendsto_pole_sub_mul
    {f : ℂ → ℂ} {p a : ℂ} (hf : ContinuousAt f p) :
    Tendsto (fun z => (z - p) * (f z + a / (z - p))) (𝓝[≠] p) (𝓝 a) := by
  have h : ContinuousAt (fun z => (z - p) * f z + a) p :=
    ((continuousAt_id.sub continuousAt_const).mul hf).add continuousAt_const
  have ht : Tendsto (fun z => (z - p) * f z + a) (𝓝[≠] p) (𝓝 a) := by
    simpa only [sub_self, zero_mul, zero_add] using h.tendsto.mono_left nhdsWithin_le_nhds
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin (s := {p}ᶜ)] with z hz
  have hne : z - p ≠ 0 := sub_ne_zero.mpr (fun h => hz (mem_singleton_iff.mpr h))
  rw [mul_add, mul_div_cancel₀ _ hne]

/-- The punctured limits after multiplying by the local coordinate give the residues. -/
theorem globalZetaContinued_residue_limits (ν : Measure (K F)) [ν.IsHaarMeasure]
    (f : GlobalBruhat F) (χ : IdeleQuasiCharacter F) (hχ : IsUnitary F χ) (κ : ℂ) :
    let a := ∫ k : K F, (χ k.val : ℂ) ∂ν
    let u := (GlobalBruhat.algebraicEquiv F f).val
    let v := (GlobalBruhat.algebraicEquiv F (GlobalBruhat.fourier F f)).val
    Tendsto (fun z => (z - (-κ)) * globalZetaContinued F ν f χ κ z)
        (𝓝[≠] (-κ)) (𝓝 (-(a * u 0))) ∧
      Tendsto (fun z => (z - (1 - κ)) * globalZetaContinued F ν f χ κ z)
        (𝓝[≠] (1 - κ)) (𝓝 (a * v 0)) := by
  let a := ∫ k : K F, (χ k.val : ℂ) ∂ν
  let u := (GlobalBruhat.algebraicEquiv F f).val
  let v := (GlobalBruhat.algebraicEquiv F (GlobalBruhat.fourier F f)).val
  let E (s : ℂ) := thetaZetaUpper F ν f χ s +
    thetaZetaUpper F ν (GlobalBruhat.fourier F f) χ⁻¹ (1 - s)
  constructor
  · have h : ContinuousAt (fun z => E z + a * v 0 / (z + κ - 1)) (-κ) := by
      apply (globalZeta_entire_part F ν f χ hχ (-κ)).continuousAt.add
      exact continuousAt_const.div
        ((continuousAt_id.add continuousAt_const).sub continuousAt_const) (by simp)
    have hh := tendsto_pole_sub_mul h (a := -(a * u 0))
    refine hh.congr' (.of_forall fun z => ?_)
    unfold globalZetaContinued
    simp only [sub_neg_eq_add, neg_div, ← sub_eq_add_neg, E, a, u, v]
  · have h : ContinuousAt (fun z => E z - a * u 0 / (z + κ)) (1 - κ) := by
      apply (globalZeta_entire_part F ν f χ hχ (1 - κ)).continuousAt.sub
      exact continuousAt_const.div (continuousAt_id.add continuousAt_const) (by simp)
    have hh := tendsto_pole_sub_mul h (a := a * v 0)
    refine hh.congr' (.of_forall fun z => ?_)
    unfold globalZetaContinued
    rw [show z - (1 - κ) = z + κ - 1 by ring]
    simp only [E, a, u, v, div_eq_mul_inv]
    ring

/-- With no polar coefficients, the continued zeta function is the sum of
the two entire theta tails. This includes the nontrivial components. -/
theorem globalZetaContinued_entire_of_polar_zero (ν : Measure (K F)) [ν.IsHaarMeasure]
    (f : GlobalBruhat F) (χ : IdeleQuasiCharacter F) (hχ : IsUnitary F χ) (κ : ℂ)
    (h : (∫ k : K F, (χ k.val : ℂ) ∂ν) = 0 ∨
      ((GlobalBruhat.algebraicEquiv F f).val 0 = 0 ∧
        (GlobalBruhat.algebraicEquiv F (GlobalBruhat.fourier F f)).val 0 = 0)) :
    AnalyticOnNhd ℂ (globalZetaContinued F ν f χ κ) univ := by
  intro z _
  have he (s : ℂ) : globalZetaContinued F ν f χ κ s =
      thetaZetaUpper F ν f χ s + thetaZetaUpper F ν (GlobalBruhat.fourier F f) χ⁻¹ (1 - s) := by
    rcases h with h | ⟨h₀, h₁⟩
    · simp [globalZetaContinued, h]
    · simp [globalZetaContinued, h₀, h₁]
  exact (globalZeta_entire_part F ν f χ hχ z).congr (.of_forall fun s => (he s).symm)

/-- The boundary set in Proposition 3.4.2.1 in coordinates `(χ, κ, s)`.
The pure norm parameter is `s + κ` on the trivial compact component. -/
def globalZetaBoundary (χ : IdeleQuasiCharacter F) (κ : ℂ) (A : ℝ) : Set ℂ :=
  {s | s.re = 1 ∧ ((∃ k : K F, χ k.val ≠ 1) ∨ A ≤ |(s + κ).im|)}

private theorem globalZetaContinued_boundary_analyticAt (ν : Measure (K F)) [ν.IsHaarMeasure]
    (f : GlobalBruhat F) (χ : IdeleQuasiCharacter F) (hχ : IsUnitary F χ)
    {κ : ℂ} (hκ : κ.re = 0) {A : ℝ} (hA : 0 < A) {z : ℂ}
    (hz : z ∈ globalZetaBoundary F χ κ A) :
    AnalyticAt ℂ (globalZetaContinued F ν f χ κ) z := by
  rcases hz with ⟨hz, ⟨k, hk⟩ | hy⟩
  · exact globalZetaContinued_entire_of_polar_zero F ν f χ hχ κ
      (Or.inl (compactCharacterIntegral_zero F ν χ hk)) z trivial
  · apply globalZetaContinued_analyticAt F ν f χ hχ κ z
    · intro he
      have h := congrArg Complex.re he
      simp only [Complex.add_re, hz, hκ, add_zero, Complex.zero_re] at h
      exact one_ne_zero h
    · intro he
      have him := congrArg Complex.im he
      have hzero : (z + κ).im = 0 := by
        simpa only [Complex.sub_im, Complex.one_im, Complex.zero_im, sub_zero] using him
      rw [hzero, abs_zero] at hy
      exact hA.not_ge hy

/-- Corrected Proposition 3.4.2.1. The continued boundary value is finite
and continuous on the stated set, and is the Abel limit of the ordinary
idelic integrals from their half-plane of absolute convergence. -/
theorem globalZetaBoundary_abel (μ : Measure (G F)) [μ.IsHaarMeasure]
    (ν : Measure (K F)) [ν.IsHaarMeasure]
    (hν : IsWeilQuotientMeasure (principalIdeles F) μ Measure.count (globalClassMeasure F ν))
    (f : GlobalBruhat F) (χ : IdeleQuasiCharacter F) (hχ : IsUnitary F χ)
    {κ : ℂ} (hκ₀ : κ.re = 0)
    (hκ : ∀ t : ℝ, (χ (ray F t) : ℂ) = Complex.exp (κ * (t : ℂ)))
    {A : ℝ} (hA : 0 < A) :
    ContinuousOn (globalZetaContinued F ν f χ κ) (globalZetaBoundary F χ κ A) ∧
    ∀ z ∈ globalZetaBoundary F χ κ A,
      Tendsto (fun t : ℝ => idelicZetaIntegral F μ (GlobalBruhat.algebraicEquiv F f).val χ
        (z + (t : ℂ))) (𝓝[>] (0 : ℝ)) (𝓝 (globalZetaContinued F ν f χ κ z)) := by
  let Z := globalZetaContinued F ν f χ κ
  have h (z : ℂ) (hz : z ∈ globalZetaBoundary F χ κ A) : ContinuousAt Z z :=
    (globalZetaContinued_boundary_analyticAt F ν f χ hχ hκ₀ hA hz).continuousAt
  refine ⟨fun z hz => (h z hz).continuousWithinAt, fun z hz => ?_⟩
  have hmap : Tendsto (fun t : ℝ => z + (t : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 z) := by
    have hc : ContinuousAt (fun t : ℝ => z + (t : ℂ)) 0 :=
      continuousAt_const.add Complex.continuous_ofReal.continuousAt
    simpa only [Complex.ofReal_zero, add_zero] using hc.tendsto.mono_left nhdsWithin_le_nhds
  apply ((h z hz).tendsto.comp hmap).congr'
  filter_upwards [self_mem_nhdsWithin (s := Ioi (0 : ℝ))] with t ht
  have hz₁ : z.re = 1 := hz.1
  have ht' : 0 < t := ht
  have hr : 1 < (z + (t : ℂ)).re := by
    rw [Complex.add_re, hz₁, Complex.ofReal_re]
    linarith
  exact globalZetaContinued_eq_idelic F μ ν hν f χ hχ hκ₀ hκ _ hr

/-- Arbitrary idelic Haar measures have compatible norm-one Haar data for
the corrected boundary result. -/
theorem globalZetaBoundary_abel_exists (μ : Measure (G F)) [μ.IsHaarMeasure]
    (χ : IdeleQuasiCharacter F) (hχ : IsUnitary F χ) :
    ∃ (ν : Measure (K F)) (κ : ℂ), ν.IsHaarMeasure ∧ κ.re = 0 ∧
      ∀ (f : GlobalBruhat F) (A : ℝ), 0 < A →
        ContinuousOn (globalZetaContinued F ν f χ κ) (globalZetaBoundary F χ κ A) ∧
        ∀ z ∈ globalZetaBoundary F χ κ A,
          Tendsto (fun t : ℝ => idelicZetaIntegral F μ (GlobalBruhat.algebraicEquiv F f).val χ
            (z + (t : ℂ))) (𝓝[>] (0 : ℝ)) (𝓝 (globalZetaContinued F ν f χ κ z)) := by
  obtain ⟨ν, hν, hW⟩ := globalClassMeasure_exists_weil F μ
  obtain ⟨κ, hκ₀, hκ⟩ := unitary_ideleClass_ray_frequency F χ hχ
  letI := hν
  exact ⟨ν, κ, hν, hκ₀, fun f _ hA => globalZetaBoundary_abel F μ ν hW f χ hχ hκ₀ hκ hA⟩

/-- For a test with both polar evaluations zero, the ordinary class theta
integral is absolutely convergent at every exponent, equals the continuation,
and converges uniformly under modulus truncation on every closed strip. -/
theorem thetaZetaIntegral_of_polar_zero (ν : Measure (K F)) [ν.IsHaarMeasure]
    (f : GlobalBruhat F) (χ : IdeleQuasiCharacter F) (hχ : IsUnitary F χ) (κ : ℂ)
    (h₀ : (GlobalBruhat.algebraicEquiv F f).val 0 = 0)
    (h₁ : (GlobalBruhat.algebraicEquiv F (GlobalBruhat.fourier F f)).val 0 = 0) :
    let u := (GlobalBruhat.algebraicEquiv F f).val
    (∀ s, Integrable (fun q => adelicTheta F u q * (ideleNormTwist F χ s q : ℂ))
        (globalClassMeasure F ν) ∧
      thetaZetaIntegral F (globalClassMeasure F ν) u χ s = globalZetaContinued F ν f χ κ s) ∧
    AnalyticOnNhd ℂ (thetaZetaIntegral F (globalClassMeasure F ν) u χ) univ ∧
    ∀ (a b : ℝ), a ≤ b →
      TendstoUniformlyOn (fun (R : ℝ) (s : ℂ) =>
        ∫ q in (fun q : Q F => Real.log (ideleClassNorm F q)) ⁻¹' Icc (-Real.log R) (Real.log R),
          adelicTheta F u q * (ideleNormTwist F χ s q : ℂ) ∂globalClassMeasure F ν)
        (thetaZetaIntegral F (globalClassMeasure F ν) u χ) atTop (Complex.re ⁻¹' Icc a b) := by
  let u := GlobalBruhat.algebraicEquiv F f
  let f' := GlobalBruhat.fourier F f
  let v := GlobalBruhat.algebraicEquiv F f'
  let μ := globalClassMeasure F ν
  have hcompl : (high F)ᶜ = low F := by
    ext q
    change (¬ 1 ≤ ideleClassNorm F q) ↔ ideleClassNorm F q < 1
    exact not_le
  have hmain (s : ℂ) :
      Integrable (fun q => adelicTheta F u.val q * (ideleNormTwist F χ s q : ℂ)) μ ∧
        thetaZetaIntegral F μ u.val χ s = globalZetaContinued F ν f χ κ s := by
    let k (q : Q F) := adelicTheta F u.val q * (ideleNormTwist F χ s q : ℂ)
    let k' (q : Q F) := adelicTheta F v.val q * (ideleNormTwist F χ⁻¹ (1 - s) q : ℂ)
    have hhi : IntegrableOn k (high F) μ := (thetaZetaUpper_integrable_analytic F ν f χ hχ).1 s
    have hki : IntegrableOn (fun q => k' q⁻¹) (low F) μ :=
      upper_inv_integrable F ν ((thetaZetaUpper_integrable_analytic F ν f' χ⁻¹
        (unitary_inv F χ hχ)).1 (1 - s))
    have hlow (q : Q F) : k q = k' q⁻¹ := by
      have he := congrFun (adelicTheta_riemannRoch F u.property).2 q
      rw [← GlobalBruhat.fourier_apply F f, h₀, h₁, smul_zero, add_zero, sub_zero] at he
      dsimp only [k, k']
      rw [he, ideleNormTwist_reflect, ideleNormTwist_shift_down, Complex.real_smul, Complex.ofReal_inv]
      ring
    have hli : IntegrableOn k (low F) μ := (funext hlow).symm ▸ hki
    have hk : Integrable k μ := integrableOn_univ.mp (by
      have hh := hhi.union hli
      rwa [← hcompl, union_compl_self] at hh)
    refine ⟨hk, ?_⟩
    change (∫ q, k q ∂μ) = _
    rw [← integral_add_compl (measurable_high F) hk, hcompl]
    have hpart : (∫ q in low F, k q ∂μ) = thetaZetaUpper F ν f' χ⁻¹ (1 - s) := by
      have he : (∫ q in low F, k' q⁻¹ ∂μ) = thetaZetaUpper F ν f' χ⁻¹ (1 - s) :=
        class_setIntegral_inv_low F ν k'
      rw [show k = (fun q => k' q⁻¹) from funext hlow]
      exact he
    rw [hpart]
    simp [globalZetaContinued, h₀, h₁, thetaZetaUpper, k, u, f', μ]
  refine ⟨hmain, ?_, fun a b hab => ?_⟩
  · intro s _
    exact (globalZetaContinued_entire_of_polar_zero F ν f χ hχ κ (Or.inr ⟨h₀, h₁⟩)
      s trivial).congr (.of_forall fun z => (hmain z).2.symm)
  · exact thetaZetaIntegral_truncation_of_integrable F ν f χ hχ a b hab (fun s _ => (hmain s).1)

private theorem simple_polar_order {g : ℂ → ℂ} {p a : ℂ} (hg : AnalyticAt ℂ g p) :
    if a = 0 then AnalyticAt ℂ (fun z => g z + a / (z - p)) p
    else meromorphicOrderAt (fun z => g z + a / (z - p)) p = (-1 : ℤ) := by
  split_ifs with ha
  · simpa only [ha, zero_div, add_zero] using hg
  have hden : AnalyticAt ℂ (fun z : ℂ => z - p) p := analyticAt_id.sub analyticAt_const
  have hm : MeromorphicAt (fun z => g z + a / (z - p)) p :=
    hg.meromorphicAt.add ((MeromorphicAt.const a p).div hden.meromorphicAt)
  apply (meromorphicOrderAt_eq_int_iff hm).2
  refine ⟨fun z => (z - p) * g z + a, (hden.mul hg).add analyticAt_const, by simpa, ?_⟩
  filter_upwards [self_mem_nhdsWithin (s := {p}ᶜ)] with z hz
  have hn : z - p ≠ 0 := sub_ne_zero.mpr (fun h => hz (mem_singleton_iff.mpr h))
  rw [zpow_neg_one, smul_eq_mul, mul_add, ← mul_assoc, inv_mul_cancel₀ hn, one_mul,
    div_eq_mul_inv, mul_comm ((z - p)⁻¹) a]

/-- Each possible pole has order exactly minus one when its residue is
nonzero. A vanishing residue gives an analytic value at that point. -/
theorem globalZetaContinued_pole_order (ν : Measure (K F)) [ν.IsHaarMeasure]
    (f : GlobalBruhat F) (χ : IdeleQuasiCharacter F) (hχ : IsUnitary F χ) (κ : ℂ) :
    let a := ∫ k : K F, (χ k.val : ℂ) ∂ν
    let u := (GlobalBruhat.algebraicEquiv F f).val
    let v := (GlobalBruhat.algebraicEquiv F (GlobalBruhat.fourier F f)).val
    (if a * u 0 = 0 then AnalyticAt ℂ (globalZetaContinued F ν f χ κ) (-κ)
      else meromorphicOrderAt (globalZetaContinued F ν f χ κ) (-κ) = (-1 : ℤ)) ∧
    (if a * v 0 = 0 then AnalyticAt ℂ (globalZetaContinued F ν f χ κ) (1 - κ)
      else meromorphicOrderAt (globalZetaContinued F ν f χ κ) (1 - κ) = (-1 : ℤ)) := by
  let a := ∫ k : K F, (χ k.val : ℂ) ∂ν
  let u := (GlobalBruhat.algebraicEquiv F f).val
  let v := (GlobalBruhat.algebraicEquiv F (GlobalBruhat.fourier F f)).val
  let E (s : ℂ) := thetaZetaUpper F ν f χ s +
    thetaZetaUpper F ν (GlobalBruhat.fourier F f) χ⁻¹ (1 - s)
  have hz (p : ℂ) : AnalyticAt ℂ (fun z => z + κ) p := analyticAt_id.add analyticAt_const
  constructor
  · have hg : AnalyticAt ℂ (fun z => E z + a * v 0 / (z + κ - 1)) (-κ) :=
      (globalZeta_entire_part F ν f χ hχ (-κ)).add
        (analyticAt_const.div ((hz _).sub analyticAt_const) (by simp))
    have he : (fun z => E z + a * v 0 / (z + κ - 1) + (-(a * u 0)) / (z - (-κ))) =
        globalZetaContinued F ν f χ κ := by
      funext z
      simp only [globalZetaContinued, E, a, u, v, sub_neg_eq_add, neg_div, ← sub_eq_add_neg]
    simpa only [he, neg_eq_zero] using simple_polar_order (a := -(a * u 0)) hg
  · have hg : AnalyticAt ℂ (fun z => E z - a * u 0 / (z + κ)) (1 - κ) :=
      (globalZeta_entire_part F ν f χ hχ (1 - κ)).sub (analyticAt_const.div (hz _) (by simp))
    have he : (fun z => E z - a * u 0 / (z + κ) + (a * v 0) / (z - (1 - κ))) =
        globalZetaContinued F ν f χ κ := by
      funext z
      rw [show z - (1 - κ) = z + κ - 1 by ring]
      simp only [globalZetaContinued, E, a, u, v, div_eq_mul_inv]
      ring
    simpa only [he] using simple_polar_order (a := a * v 0) hg

/-- Restriction of a unitary idele class character to the compact
norm-one classes, now regarded as a Pontryagin character. -/
def normOnePontryaginCharacter (χ : IdeleQuasiCharacter F) (hχ : IsUnitary F χ) :
    PontryaginDual (K F) := by
  have hc (k : K F) : (χ k.val : ℂ) ∈ Submonoid.unitSphere ℂ := by
    change dist (χ k.val : ℂ) 0 = 1
    rw [dist_zero_right, hχ]
  exact
    { toFun := fun k => ⟨(χ k.val : ℂ), hc k⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by
        change (χ (a.val * b.val) : ℂ) = (χ a.val : ℂ) * (χ b.val : ℂ)
        rw [map_mul, Units.val_mul])
      continuous_toFun := ((Units.continuous_val.comp (map_continuous χ)).comp
        continuous_subtype_val).subtype_mk hc }

/-- The radial integrand in (3.2.2.4), in logarithmic coordinates and for
a section of the modulus on the idele class group. -/
def globalRadialZetaIntegrand (ν : Measure (K F)) (f : GlobalBruhat F)
    (χ : IdeleQuasiCharacter F) (hχ : IsUnitary F χ) (s : ℂ)
    (τ : Multiplicative ℝ →* Q F) (t : ℝ) : ℂ :=
  (ideleNormTwist F χ s (τ (Multiplicative.ofAdd t)) : ℂ) *
    adelicHomogeneousTheta F ν (normOnePontryaginCharacter F χ hχ)
      (GlobalBruhat.algebraicEquiv F f).val (τ (Multiplicative.ofAdd t))

/-- The character of the section and the homogeneous theta factor
transform by inverse scalars when the section is changed. -/
theorem globalRadialZetaIntegrand_section_independent
    (ν : Measure (K F)) [ν.IsHaarMeasure] (f : GlobalBruhat F)
    (χ : IdeleQuasiCharacter F) (hχ : IsUnitary F χ) (s : ℂ)
    (τ : Multiplicative ℝ →* Q F)
    (hτ : ∀ t : ℝ, ideleClassNorm F (τ (Multiplicative.ofAdd t)) = Real.exp t) :
    globalRadialZetaIntegrand F ν f χ hχ s τ =
      globalRadialZetaIntegrand F ν f χ hχ s (ideleClassExpSection F) := by
  funext t
  let q := τ (Multiplicative.ofAdd t)
  let r := ray F t
  let k := ideleClassNormOnePart F q
  have hk : k.val * r = q := by
    have ht : ideleClassLogNorm F q = Multiplicative.ofAdd t := by
      change Multiplicative.ofAdd (Real.log (ideleClassNorm F q)) = _
      rw [hτ t, Real.log_exp]
    have hh := (ideleClassSplit F).symm_apply_apply q
    change k.val * ideleClassExpSection F (ideleClassLogNorm F q) = q at hh
    rwa [ht] at hh
  let w := ideleNormTwist F χ s
  let ω := normOnePontryaginCharacter F χ hχ
  let u := (GlobalBruhat.algebraicEquiv F f).val
  let Θ := adelicHomogeneousTheta F ν ω u
  have hw : (w k.val : ℂ) = (ω k : ℂ) := by
    change (χ k.val : ℂ) * ideleNormPower F s k.val = (χ k.val : ℂ)
    have h1 : ideleClassNorm F k.val = 1 := k.property
    simp [ideleNormPower, h1]
  change (w q : ℂ) * Θ q = (w r : ℂ) * Θ r
  rw [← hk, map_mul, Units.val_mul, hw, show Θ (k.val * r) = (ω k : ℂ)⁻¹ * Θ r from
    adelicHomogeneousTheta_translate F ν ω u k r]
  let x : ℂ := ω k
  have hx : x ≠ 0 := Circle.coe_ne_zero _
  change x * (w r : ℂ) * (x⁻¹ * Θ r) = _
  calc
    _ = (x * x⁻¹) * ((w r : ℂ) * Θ r) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hx, one_mul]

/-- Fubini in log-modulus coordinates gives the radial Mellin integral
whenever the ordinary class integral is absolutely convergent. -/
theorem thetaZetaIntegral_eq_radial_of_integrable
    (ν : Measure (K F)) [ν.IsHaarMeasure] (f : GlobalBruhat F)
    (χ : IdeleQuasiCharacter F) (hχ : IsUnitary F χ) (s : ℂ)
    (τ : Multiplicative ℝ →* Q F)
    (hτ : ∀ t : ℝ, ideleClassNorm F (τ (Multiplicative.ofAdd t)) = Real.exp t)
    (hI : Integrable (fun q => adelicTheta F (GlobalBruhat.algebraicEquiv F f).val q *
      (ideleNormTwist F χ s q : ℂ)) (globalClassMeasure F ν)) :
    Integrable (globalRadialZetaIntegrand F ν f χ hχ s τ) ∧
      thetaZetaIntegral F (globalClassMeasure F ν) (GlobalBruhat.algebraicEquiv F f).val χ s =
        ∫ t : ℝ, globalRadialZetaIntegrand F ν f χ hχ s τ t := by
  rw [globalRadialZetaIntegrand_section_independent F ν f χ hχ s τ hτ]
  letI := normOneIdeleClass_compact F
  letI : IsFiniteMeasure ν := ⟨isCompact_univ.measure_lt_top⟩
  let e := ideleClassLogCoordinates F
  let u := (GlobalBruhat.algebraicEquiv F f).val
  let w := ideleNormTwist F χ s
  let ω := normOnePontryaginCharacter F χ hχ
  let QI (q : Q F) := adelicTheta F u q * (w q : ℂ)
  let PI (p : ℝ × K F) := QI (e p)
  have hP : Integrable PI (volume.prod ν) :=
    e.toMeasurableEquiv.measurableEmbedding.integrable_map_iff.mp hI
  have he (t : ℝ) : (∫ k, PI (t, k) ∂ν) =
      globalRadialZetaIntegrand F ν f χ hχ s (ideleClassExpSection F) t := by
    change (∫ k, PI (t, k) ∂ν) =
      (w (ray F t) : ℂ) * adelicHomogeneousTheta F ν ω u (ray F t)
    rw [adelicHomogeneousTheta, ← integral_const_mul]
    apply integral_congr_ae (.of_forall fun k => ?_)
    change adelicTheta F u (k.val * ray F t) * (w (k.val * ray F t) : ℂ) =
      (w (ray F t) : ℂ) * ((ω k : ℂ) * adelicTheta F u (k.val * ray F t))
    have hw : (w k.val : ℂ) = (ω k : ℂ) := by
      change (χ k.val : ℂ) * ideleNormPower F s k.val = (χ k.val : ℂ)
      have h1 : ideleClassNorm F k.val = 1 := k.property
      simp [ideleNormPower, h1]
    rw [map_mul, Units.val_mul, hw]
    ring
  refine ⟨(funext he) ▸ hP.integral_prod_left, ?_⟩
  change (∫ q, QI q ∂Measure.map e.toMeasurableEquiv (volume.prod ν)) = _
  rw [integral_map_equiv]
  change (∫ p, PI p ∂volume.prod ν) = _
  rw [integral_prod _ hP]
  simp_rw [he]

/-- The two polar terms cancel after compact averaging in these cases. -/
def globalZetaPolarVanishes (f : GlobalBruhat F) (χ : IdeleQuasiCharacter F) : Prop :=
  (∃ k : K F, χ k.val ≠ 1) ∨
    ((GlobalBruhat.algebraicEquiv F f).val 0 = 0 ∧
      (GlobalBruhat.algebraicEquiv F (GlobalBruhat.fourier F f)).val 0 = 0)

private theorem normOnePontryaginCharacter_ne_one (χ : IdeleQuasiCharacter F)
    (hχ : IsUnitary F χ) {k : K F} (hk : χ k.val ≠ 1) :
    normOnePontryaginCharacter F χ hχ ≠ 1 := by
  intro he
  apply hk
  apply Units.ext
  change (χ k.val : ℂ) = 1
  exact congrArg (fun ω : PontryaginDual (K F) => (ω k : ℂ)) he

theorem globalRadialZetaIntegrand_canonical (ν : Measure (K F)) (f : GlobalBruhat F)
    (χ : IdeleQuasiCharacter F) (hχ : IsUnitary F χ) (s : ℂ) (t : ℝ) :
    globalRadialZetaIntegrand F ν f χ hχ s (ideleClassExpSection F) t =
      Complex.exp (s * (t : ℂ)) * ((χ (ray F t) : ℂ) *
        adelicHomogeneousTheta F ν (normOnePontryaginCharacter F χ hχ)
          (GlobalBruhat.algebraicEquiv F f).val (ray F t)) := by
  unfold globalRadialZetaIntegrand
  change ((χ (ray F t) : ℂ) * ideleNormPower F s (ray F t)) * _ = _
  rw [ideleNormPower, ideleClassNorm_expSection, Real.log_exp]
  change (χ (ray F t) : ℂ) * Complex.exp (s * (t : ℂ)) * _ =
    Complex.exp (s * (t : ℂ)) * ((χ (ray F t) : ℂ) * _)
  ring

private theorem globalRadialZetaIntegrand_norm (ν : Measure (K F)) (f : GlobalBruhat F)
    (χ : IdeleQuasiCharacter F) (hχ : IsUnitary F χ) (s : ℂ) (t : ℝ) :
    ‖globalRadialZetaIntegrand F ν f χ hχ s (ideleClassExpSection F) t‖ =
      Real.exp (s.re * t) * ‖adelicHomogeneousTheta F ν (normOnePontryaginCharacter F χ hχ)
        (GlobalBruhat.algebraicEquiv F f).val (ray F t)‖ := by
  rw [globalRadialZetaIntegrand_canonical, norm_mul, norm_mul, hχ, one_mul, Complex.norm_exp]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]

private theorem globalRadialZetaIntegrand_continuous (ν : Measure (K F)) [ν.IsHaarMeasure]
    (f : GlobalBruhat F) (χ : IdeleQuasiCharacter F) (hχ : IsUnitary F χ) (s : ℂ) :
    Continuous (globalRadialZetaIntegrand F ν f χ hχ s (ideleClassExpSection F)) := by
  unfold globalRadialZetaIntegrand
  have hr : Continuous (ray F) := (ideleClassExpSection_continuous F).comp continuous_ofAdd
  exact ((Units.continuous_val.comp (map_continuous (ideleNormTwist F χ s))).comp hr).mul
    ((adelicHomogeneousTheta_continuous F ν (normOnePontryaginCharacter F χ hχ)
      (GlobalBruhat.algebraicEquiv F f).property).comp hr)

private theorem globalRadialZeta_decay (ν : Measure (K F)) [ν.IsHaarMeasure] (f : GlobalBruhat F)
    (χ : IdeleQuasiCharacter F) (hχ : IsUnitary F χ) (hvan : globalZetaPolarVanishes F f χ)
    (a b : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ∀ t : ℝ,
      ‖globalRadialZetaIntegrand F ν f χ hχ s (ideleClassExpSection F) t‖ ≤ C * Real.exp (-|t|) := by
  let ω := normOnePontryaginCharacter F χ hχ
  have hω : ω ≠ 1 ∨ ((GlobalBruhat.algebraicEquiv F f).val 0 = 0 ∧
      (GlobalBruhat.algebraicEquiv F (GlobalBruhat.fourier F f)).val 0 = 0) := by
    rcases hvan with ⟨k, hk⟩ | hp
    · exact Or.inl (normOnePontryaginCharacter_ne_one F χ hχ hk)
    · exact Or.inr hp
  obtain ⟨N, hN⟩ := exists_nat_gt (max (-a) b + 1)
  obtain ⟨C, hC, hD⟩ := adelicHomogeneousTheta_radial_derivative_decay F ν ω {f}
    (isVonNBounded_singleton (𝕜 := ℂ) f) 0 N
  refine ⟨C, hC, fun s ha hb t => ?_⟩
  rw [globalRadialZetaIntegrand_norm F ν f χ hχ]
  have ht := hD f (mem_singleton f) hω t
  simp only [iteratedDeriv_zero] at ht
  have hst : s.re * t ≤ ((N : ℝ) - 1) * |t| := by
    by_cases h : 0 ≤ t
    · rw [abs_of_nonneg h]
      exact mul_le_mul_of_nonneg_right (by linarith [le_max_right (-a) b]) h
    · rw [abs_of_nonpos (le_of_not_ge h), mul_neg, ← neg_mul]
      exact mul_le_mul_of_nonpos_right (by linarith [le_max_left (-a) b]) (le_of_not_ge h)
  calc
    _ ≤ Real.exp (s.re * t) * (C * Real.exp (-(N : ℝ) * |t|)) :=
      mul_le_mul_of_nonneg_left ht (Real.exp_nonneg _)
    _ = C * Real.exp (s.re * t - (N : ℝ) * |t|) := by
      rw [mul_left_comm, ← Real.exp_add]
      congr 2
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hC.le

private theorem integrable_radial_first_moment (C : ℝ) (hC : 0 ≤ C) :
    Integrable (fun t : ℝ => |t| * (C * Real.exp (-|t|))) := by
  refine (((integrable_exp_abs_envelope (1 / 2) (by norm_num)).const_mul (2 * C))).mono'
    (by fun_prop) (.of_forall fun t => ?_)
  rw [Real.norm_of_nonneg (by positivity)]
  have ht : |t| ≤ 2 * Real.exp (|t| / 2) := by linarith [Real.add_one_le_exp (|t| / 2)]
  calc
    _ ≤ (2 * Real.exp (|t| / 2)) * (C * Real.exp (-|t|)) :=
      mul_le_mul_of_nonneg_right ht (by positivity)
    _ = (2 * C) * Real.exp (-(1 / 2) * |t|) := by
      rw [show (2 * Real.exp (|t| / 2)) * (C * Real.exp (-|t|)) =
        (2 * C) * (Real.exp (|t| / 2) * Real.exp (-|t|)) by ring, ← Real.exp_add]
      congr 2
      ring

/-- The radial integral on its original convergence half-plane and on
every exponent when compact averaging cancels the polar terms. -/
theorem globalRadialZeta_integrable (ν : Measure (K F)) [ν.IsHaarMeasure]
    (f : GlobalBruhat F) (χ : IdeleQuasiCharacter F) (hχ : IsUnitary F χ) (s : ℂ)
    (τ : Multiplicative ℝ →* Q F)
    (hτ : ∀ t : ℝ, ideleClassNorm F (τ (Multiplicative.ofAdd t)) = Real.exp t)
    (hs : 1 < s.re ∨ globalZetaPolarVanishes F f χ) :
    Integrable (globalRadialZetaIntegrand F ν f χ hχ s τ) := by
  rcases hs with hs | hv
  · exact (thetaZetaIntegral_eq_radial_of_integrable F ν f χ hχ s τ hτ
      (thetaZetaIntegral_integrable F ν f χ hχ s hs)).1
  · rw [globalRadialZetaIntegrand_section_independent F ν f χ hχ s τ hτ]
    obtain ⟨C, _, hC⟩ := globalRadialZeta_decay F ν f χ hχ hv s.re s.re
    have hi : Integrable (fun t : ℝ => C * Real.exp (-|t|)) := by
      simpa only [neg_mul, one_mul] using (integrable_exp_abs_envelope 1 one_pos).const_mul C
    exact hi.mono' (globalRadialZetaIntegrand_continuous F ν f χ hχ s).aestronglyMeasurable
      (.of_forall (hC s le_rfl le_rfl))

/-- Modulus truncation of the homogeneous radial integral converges
uniformly on every closed strip in its domain of absolute convergence. -/
theorem globalRadialZeta_truncation (ν : Measure (K F)) [ν.IsHaarMeasure]
    (f : GlobalBruhat F) (χ : IdeleQuasiCharacter F) (hχ : IsUnitary F χ)
    (τ : Multiplicative ℝ →* Q F)
    (hτ : ∀ t : ℝ, ideleClassNorm F (τ (Multiplicative.ofAdd t)) = Real.exp t)
    (a b : ℝ) (hab : a ≤ b) (h : 1 < a ∨ globalZetaPolarVanishes F f χ) :
    TendstoUniformlyOn (fun (R : ℝ) (s : ℂ) => ∫ t : ℝ in Icc (-Real.log R) (Real.log R),
      globalRadialZetaIntegrand F ν f χ hχ s τ t)
      (fun s => ∫ t : ℝ, globalRadialZetaIntegrand F ν f χ hχ s τ t)
      atTop (Complex.re ⁻¹' Icc a b) := by
  let W := globalRadialZetaIntegrand F ν f χ hχ
  have he (s : ℂ) : W s τ = W s (ideleClassExpSection F) :=
    globalRadialZetaIntegrand_section_independent F ν f χ hχ s τ hτ
  have hi (s : ℂ) (hs : a ≤ s.re) : Integrable (W s τ) :=
    globalRadialZeta_integrable F ν f χ hχ s τ hτ (h.imp_left fun ha => ha.trans_le hs)
  have hI (s : ℂ) (hs : s ∈ Complex.re ⁻¹' Icc a b) : Integrable (W s τ) := hi s hs.1
  have ha : Integrable (W (a : ℂ) τ) := hi a (by simp)
  have hb : Integrable (W (b : ℂ) τ) := hi b (by simpa using hab)
  have hm : Integrable (fun t => ‖W (a : ℂ) τ t‖ + ‖W (b : ℂ) τ t‖) := ha.norm.add hb.norm
  exact uniformIntegral_logTruncation id measurable_id (fun s => W s τ) hI hm (by
    intro s hs t
    have hn (r : ℂ) := globalRadialZetaIntegrand_norm F ν f χ hχ r t
    have hnorm (r : ℂ) := (congrArg (fun g : ℝ → ℂ => ‖g t‖) (he r)).trans (hn r)
    change ‖W s τ t‖ ≤ ‖W (a : ℂ) τ t‖ + ‖W (b : ℂ) τ t‖
    rcases le_total t 0 with ht | ht
    · refine (show ‖W s τ t‖ ≤ ‖W (a : ℂ) τ t‖ by
        rw [hnorm, hnorm, Complex.ofReal_re]
        exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr
          (mul_le_mul_of_nonpos_right hs.1 ht)) (norm_nonneg _)).trans
          (le_add_of_nonneg_right (norm_nonneg _))
    · refine (show ‖W s τ t‖ ≤ ‖W (b : ℂ) τ t‖ by
        rw [hnorm, hnorm, Complex.ofReal_re]
        exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_right hs.2 ht)) (norm_nonneg _)).trans
          (le_add_of_nonneg_left (norm_nonneg _)))

/-- The homogeneous radial transform is entire in the polar-free cases. -/
theorem globalRadialZeta_analytic (ν : Measure (K F)) [ν.IsHaarMeasure]
    (f : GlobalBruhat F) (χ : IdeleQuasiCharacter F) (hχ : IsUnitary F χ)
    (τ : Multiplicative ℝ →* Q F)
    (hτ : ∀ t : ℝ, ideleClassNorm F (τ (Multiplicative.ofAdd t)) = Real.exp t)
    (hv : globalZetaPolarVanishes F f χ) :
    AnalyticOnNhd ℂ (fun s => ∫ t : ℝ, globalRadialZetaIntegrand F ν f χ hχ s τ t) univ := by
  simp_rw [globalRadialZetaIntegrand_section_independent F ν f χ hχ _ τ hτ]
  apply DifferentiableOn.analyticOnNhd _ isOpen_univ
  intro s _
  let W (z : ℂ) := globalRadialZetaIntegrand F ν f χ hχ z (ideleClassExpSection F)
  let a := s.re - 1
  let b := s.re + 1
  obtain ⟨C, hC, hD⟩ := globalRadialZeta_decay F ν f χ hχ hv a b
  have hn : Complex.re ⁻¹' Ioo a b ∈ 𝓝 s :=
    (isOpen_Ioo.preimage Complex.continuous_re).mem_nhds ⟨by dsimp [a]; linarith, by dsimp [b]; linarith⟩
  have hc (z : ℂ) : Continuous (W z) := globalRadialZetaIntegrand_continuous F ν f χ hχ z
  have hd (w : ℂ) (t : ℝ) : HasDerivAt (fun z => W z t) ((t : ℂ) * W w t) w := by
    simp only [W, globalRadialZetaIntegrand_canonical]
    simpa only [id_eq, one_mul, mul_assoc, mul_left_comm] using
      ((((hasDerivAt_id w).mul_const (t : ℂ)).cexp).mul_const
        ((χ (ray F t) : ℂ) * adelicHomogeneousTheta F ν (normOnePontryaginCharacter F χ hχ)
          (GlobalBruhat.algebraicEquiv F f).val (ray F t)))
  have hi : Integrable (W s) := globalRadialZeta_integrable F ν f χ hχ s (ideleClassExpSection F)
    (fun _ => ideleClassNorm_expSection F _) (Or.inr hv)
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := W) (F' := fun w t => (t : ℂ) * W w t) (bound := fun t => |t| * (C * Real.exp (-|t|))) hn
    (.of_forall fun w => (hc w).aestronglyMeasurable) hi
    ((Complex.continuous_ofReal.mul (hc s)).aestronglyMeasurable)
    (.of_forall fun t w hw => by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hD w hw.1.le hw.2.le t) (abs_nonneg _))
    (integrable_radial_first_moment C hC.le) (.of_forall fun t w _ => hd w t)
  exact h.2.differentiableAt.differentiableWithinAt

/-- With compact Haar averaging performed before the radial integration,
the integral gives the same global zeta function on its convergence domain.
In particular it gives the entire continuation on every nontrivial component. -/
theorem globalRadialZeta_eq_continued (ν : Measure (K F)) [ν.IsHaarMeasure]
    (f : GlobalBruhat F) (χ : IdeleQuasiCharacter F) (hχ : IsUnitary F χ)
    {κ : ℂ} (hκ₀ : κ.re = 0)
    (hκ : ∀ t : ℝ, (χ (ray F t) : ℂ) = Complex.exp (κ * (t : ℂ)))
    (τ : Multiplicative ℝ →* Q F)
    (hτ : ∀ t : ℝ, ideleClassNorm F (τ (Multiplicative.ofAdd t)) = Real.exp t)
    (s : ℂ) (hs : 1 < s.re ∨ globalZetaPolarVanishes F f χ) :
    (∫ t : ℝ, globalRadialZetaIntegrand F ν f χ hχ s τ t) =
      globalZetaContinued F ν f χ κ s := by
  have hmain (z : ℂ) (hz : 1 < z.re) :
      (∫ t : ℝ, globalRadialZetaIntegrand F ν f χ hχ z τ t) =
        globalZetaContinued F ν f χ κ z :=
    ((thetaZetaIntegral_eq_radial_of_integrable F ν f χ hχ z τ hτ
      (thetaZetaIntegral_integrable F ν f χ hχ z hz)).2.symm).trans
      (globalZetaContinued_eq_theta F ν f χ hχ hκ₀ hκ z hz).symm
  rcases hs with hs | hv
  · exact hmain s hs
  · have hv' : (∫ k : K F, (χ k.val : ℂ) ∂ν) = 0 ∨
        ((GlobalBruhat.algebraicEquiv F f).val 0 = 0 ∧
          (GlobalBruhat.algebraicEquiv F (GlobalBruhat.fourier F f)).val 0 = 0) := by
      rcases hv with ⟨k, hk⟩ | hp
      · exact Or.inl (compactCharacterIntegral_zero F ν χ hk)
      · exact Or.inr hp
    have hA := globalRadialZeta_analytic F ν f χ hχ τ hτ hv
    have hB := globalZetaContinued_entire_of_polar_zero F ν f χ hχ κ hv'
    have he : (fun z => ∫ t : ℝ, globalRadialZetaIntegrand F ν f χ hχ z τ t) =ᶠ[𝓝 (2 : ℂ)]
        globalZetaContinued F ν f χ κ := by
      filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
        (by norm_num : (2 : ℂ) ∈ {z : ℂ | 1 < z.re})] with z hz
      exact hmain z hz
    exact congrFun (hA.eq_of_eventuallyEq hB he) s

private def compactCharacterUnits (ω : PontryaginDual (K F)) : K F →ₜ* ℂˣ where
  toMonoidHom := Circle.toUnits.comp ω.toMonoidHom
  continuous_toFun := by
    apply Units.continuous_iff.mpr
    have h : Continuous (fun k : K F => (ω k : ℂ)) := continuous_subtype_val.comp ω.continuous
    refine ⟨h, ?_⟩
    simp only [Units.val_inv_eq_inv_val]
    change Continuous (fun k : K F => (ω k : ℂ)⁻¹)
    exact h.inv₀ (fun k => Circle.coe_ne_zero (ω k))

/-- The unitary lift of a compact norm-one character that is trivial on the
chosen radial section. It centers the complex coordinate on the component. -/
def compactIdeleClassCharacter (ω : PontryaginDual (K F)) : IdeleQuasiCharacter F :=
  extendFromNormOne F (compactCharacterUnits F ω)

theorem compactIdeleClassCharacter_unitary (ω : PontryaginDual (K F)) :
    IsUnitary F (compactIdeleClassCharacter F ω) := fun q =>
  Circle.norm_coe (ω (ideleClassNormOnePart F q))

@[simp] theorem compactIdeleClassCharacter_apply_normOne (ω : PontryaginDual (K F)) (k : K F) :
    (compactIdeleClassCharacter F ω k.val : ℂ) = (ω k : ℂ) :=
  congrArg Units.val (DFunLike.congr_fun (restrictToNormOne_extend F (compactCharacterUnits F ω)) k)

@[simp] theorem compactIdeleClassCharacter_apply_ray (ω : PontryaginDual (K F)) (t : ℝ) :
    (compactIdeleClassCharacter F ω (ray F t) : ℂ) = 1 := by
  change (ω (ideleClassNormOnePart F (ray F t)) : ℂ) = 1
  have hk : ideleClassNormOnePart F (ray F t) = 1 := by
    apply Subtype.ext
    change ray F t / ideleClassExpSection F (ideleClassLogNorm F (ray F t)) = 1
    rw [ideleClassLogNorm_expSection, div_self']
  rw [hk, map_one]
  rfl

@[simp] theorem normOnePontryaginCharacter_compactIdeleClassCharacter (ω : PontryaginDual (K F)) :
    normOnePontryaginCharacter F (compactIdeleClassCharacter F ω)
      (compactIdeleClassCharacter_unitary F ω) = ω := by
  ext k
  exact compactIdeleClassCharacter_apply_normOne F ω k

private theorem norm_ideleClassCharacter_apply_normOne (χ : IdeleQuasiCharacter F) (k : K F) :
    ‖(χ k.val : ℂ)‖ = 1 := by
  letI := normOneIdeleClass_compact F
  have hc : Continuous (fun k : K F => ‖(χ k.val : ℂ)‖) :=
    ((Units.continuous_val.comp (map_continuous χ)).comp continuous_subtype_val).norm
  obtain ⟨M, hM⟩ := (isCompact_univ.image hc).bddAbove
  have hle (k : K F) : ‖(χ k.val : ℂ)‖ ≤ 1 := by
    by_contra! hk
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt M hk
    apply hn.not_ge
    have hh := hM (mem_image_of_mem (fun k : K F => ‖(χ k.val : ℂ)‖) (mem_univ (k ^ n)))
    simpa only [Subgroup.coe_pow, map_pow, Units.val_pow_eq_pow_val, norm_pow] using hh
  have hi := hle k⁻¹
  rw [Subgroup.coe_inv, map_inv, Units.val_inv_eq_inv_val, norm_inv] at hi
  exact (hle k).antisymm ((inv_le_one₀ (norm_pos_iff.mpr (χ k.val).ne_zero)).mp hi)

/-- Every quasi-character belongs to a canonical complex chart, with its
unitary compact component and its unique radial exponent. -/
theorem ideleClassCharacter_existsUnique_compact_twist (χ : IdeleQuasiCharacter F) :
    ∃ ω : PontryaginDual (K F), ∃! s : ℂ,
      χ = ideleNormTwist F (compactIdeleClassCharacter F ω) s := by
  have hc (k : K F) : (χ k.val : ℂ) ∈ Submonoid.unitSphere ℂ := by
    change dist (χ k.val : ℂ) 0 = 1
    rw [dist_zero_right, norm_ideleClassCharacter_apply_normOne F χ]
  let ω : PontryaginDual (K F) :=
    { toFun := fun k => ⟨(χ k.val : ℂ), hc k⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by
        change (χ (a.val * b.val) : ℂ) = (χ a.val : ℂ) * (χ b.val : ℂ)
        rw [map_mul, Units.val_mul])
      continuous_toFun := ((Units.continuous_val.comp (map_continuous χ)).comp
        continuous_subtype_val).subtype_mk hc }
  let γ := (restrictToNormRay F χ).toMonoidHom
  obtain ⟨s, hs, huniq⟩ := complex_oneParameter_exp γ
    (Units.continuous_val.comp ((map_continuous χ).comp
      ((ideleClassExpSection_continuous F).comp continuous_ofAdd)))
  refine ⟨ω, s, ?_, ?_⟩
  · apply quasiCharacter_eq_of_restrictions F
    · rw [restrictToNormOne_twist]
      ext k
      change (ω k : ℂ) = (compactIdeleClassCharacter F ω k.val : ℂ)
      exact (compactIdeleClassCharacter_apply_normOne F ω k).symm
    · ext t
      have hh := hs t.toAdd
      change (χ (ray F t.toAdd) : ℂ) = (ideleNormTwist F (compactIdeleClassCharacter F ω) s
        (ray F t.toAdd) : ℂ)
      change (χ (ray F t.toAdd) : ℂ) = (compactIdeleClassCharacter F ω (ray F t.toAdd) : ℂ) *
        ideleNormPower F s (ray F t.toAdd)
      rw [compactIdeleClassCharacter_apply_ray, one_mul, ideleNormPower, ideleClassNorm_expSection,
        Real.log_exp]
      exact hh
  · intro z he
    apply huniq z
    intro t
    change (χ (ray F t) : ℂ) = _
    rw [he]
    change (compactIdeleClassCharacter F ω (ray F t) : ℂ) * ideleNormPower F z (ray F t) = _
    rw [compactIdeleClassCharacter_apply_ray, one_mul, ideleNormPower, ideleClassNorm_expSection, Real.log_exp]
    rfl

/-- The compact character is uniquely determined by the quasi-character,
regardless of the chosen radial exponent. -/
theorem ideleClassCharacter_compact_twist_injective (ω ψ : PontryaginDual (K F)) (s z : ℂ)
    (h : ideleNormTwist F (compactIdeleClassCharacter F ω) s =
      ideleNormTwist F (compactIdeleClassCharacter F ψ) z) : ω = ψ := by
  have hh := congrArg (restrictToNormOne F) h
  rw [restrictToNormOne_twist, restrictToNormOne_twist] at hh
  ext k
  have hk := congrArg Units.val (DFunLike.congr_fun hh k)
  change (compactIdeleClassCharacter F ω k.val : ℂ) =
    (compactIdeleClassCharacter F ψ k.val : ℂ) at hk
  simpa only [compactIdeleClassCharacter_apply_normOne] using hk

@[simp] theorem compactIdeleClassCharacter_inv (ω : PontryaginDual (K F)) :
    compactIdeleClassCharacter F ω⁻¹ = (compactIdeleClassCharacter F ω)⁻¹ := by
  ext q
  let k := ideleClassNormOnePart F q
  change (Circle.toUnits ((ω k)⁻¹) : ℂ) = ((Circle.toUnits (ω k))⁻¹ : ℂˣ).val
  exact congrArg Units.val (map_inv Circle.toUnits (ω k))

theorem compactIdeleClassCharacter_integral (ν : Measure (K F)) [ν.IsHaarMeasure]
    (ω : PontryaginDual (K F)) :
    (∫ k : K F, (compactIdeleClassCharacter F ω k.val : ℂ) ∂ν) =
      if ω = 1 then (ν.real univ : ℂ) else 0 := by
  by_cases hω : ω = 1
  · rw [ite_eq_left hω]
    simp only [compactIdeleClassCharacter_apply_normOne, hω, PontryaginDual.one_apply,
      Circle.coe_one, integral_const, Complex.real_smul, mul_one]
  · rw [ite_eq_right hω]
    have hk : ∃ k : K F, compactIdeleClassCharacter F ω k.val ≠ 1 := by
      by_contra! h
      apply hω
      ext k
      have he := congrArg Units.val (h k)
      change (compactIdeleClassCharacter F ω k.val : ℂ) = 1 at he
      simpa only [compactIdeleClassCharacter_apply_normOne, PontryaginDual.one_apply, Circle.coe_one] using he
    obtain ⟨k, hk⟩ := hk
    exact compactCharacterIntegral_zero F ν (compactIdeleClassCharacter F ω) hk

/-- In the canonical trivial-character chart the two residues have exactly
the coefficients of Theorem 3.2.2.1. -/
theorem globalZetaContinued_trivial_residues (ν : Measure (K F)) [ν.IsHaarMeasure]
    (f : GlobalBruhat F) :
    let χ := compactIdeleClassCharacter F (1 : PontryaginDual (K F))
    Tendsto (fun z => z * globalZetaContinued F ν f χ 0 z) (𝓝[≠] (0 : ℂ))
        (𝓝 (-((ν.real univ : ℂ) * (GlobalBruhat.algebraicEquiv F f).val 0))) ∧
      Tendsto (fun z => (z - 1) * globalZetaContinued F ν f χ 0 z) (𝓝[≠] (1 : ℂ))
        (𝓝 ((ν.real univ : ℂ) * (GlobalBruhat.algebraicEquiv F
          (GlobalBruhat.fourier F f)).val 0)) := by
  have h := globalZetaContinued_residue_limits F ν f (compactIdeleClassCharacter F 1)
    (compactIdeleClassCharacter_unitary F 1) 0
  simpa only [neg_zero, sub_zero, compactIdeleClassCharacter_integral, ite_true] using h

/-- The cancellation domain in the canonical chart agrees with the
nontrivial-character or two-vanishing-values condition of the manuscript. -/
theorem globalZetaPolarVanishes_compact_iff (f : GlobalBruhat F)
    (ω : PontryaginDual (K F)) :
    globalZetaPolarVanishes F f (compactIdeleClassCharacter F ω) ↔
      ω ≠ 1 ∨ ((GlobalBruhat.algebraicEquiv F f).val 0 = 0 ∧
        (GlobalBruhat.algebraicEquiv F (GlobalBruhat.fourier F f)).val 0 = 0) := by
  change ((∃ k : K F, compactIdeleClassCharacter F ω k.val ≠ 1) ∨ _) ↔ _
  apply or_congr_left
  constructor
  · rintro ⟨k, hk⟩
    have h := normOnePontryaginCharacter_ne_one F (compactIdeleClassCharacter F ω)
      (compactIdeleClassCharacter_unitary F ω) hk
    rwa [normOnePontryaginCharacter_compactIdeleClassCharacter] at h
  · intro hω
    by_contra h
    apply hω
    ext k
    have he := congrArg Units.val (not_not.mp (not_exists.mp h k))
    change (compactIdeleClassCharacter F ω k.val : ℂ) = 1 at he
    simpa only [compactIdeleClassCharacter_apply_normOne, PontryaginDual.one_apply,
      Circle.coe_one] using he

/-- The functional equation in the canonical charts of the quasi-character
space, with the reflected compact character and parameter. -/
theorem globalZetaContinued_compact_functionalEquation (ν : Measure (K F)) [ν.IsHaarMeasure]
    (f : GlobalBruhat F) (ω : PontryaginDual (K F)) (s : ℂ) :
    globalZetaContinued F ν f (compactIdeleClassCharacter F ω) 0 s =
      globalZetaContinued F ν (GlobalBruhat.fourier F f) (compactIdeleClassCharacter F ω⁻¹)
        0 (1 - s) := by
  rw [compactIdeleClassCharacter_inv]
  simpa only [neg_zero] using globalZetaContinued_functionalEquation F ν f
    (compactIdeleClassCharacter F ω) 0 s

/-- The logarithmic radial integral and the original positive-variable
integral against dt/t have the same convergence and value. -/
theorem radialIntegral_positive_changeOfVariables (g : ℝ → ℂ) :
    (IntegrableOn (fun r : ℝ => r⁻¹ • g (Real.log r)) (Ioi (0 : ℝ)) ↔ Integrable g) ∧
      (∫ r : ℝ in Ioi 0, r⁻¹ • g (Real.log r)) = ∫ t : ℝ, g t := by
  let v (r : ℝ) := r⁻¹ • g (Real.log r)
  have hd (x : ℝ) (_ : x ∈ (univ : Set ℝ)) :
      HasDerivWithinAt Real.exp (Real.exp x) univ x := (Real.hasDerivAt_exp x).hasDerivWithinAt
  have he (x : ℝ) : |Real.exp x| • v (Real.exp x) = g x := by
    simp only [v, Real.log_exp, abs_of_pos (Real.exp_pos x), smul_smul,
      mul_inv_cancel₀ (Real.exp_pos x).ne', one_smul]
  have hi := integrableOn_image_iff_integrableOn_abs_deriv_smul
    MeasurableSet.univ hd Real.exp_injective.injOn v
  have hJ := integral_image_eq_integral_abs_deriv_smul
    MeasurableSet.univ hd Real.exp_injective.injOn v
  have hset : Real.exp '' (univ : Set ℝ) = Ioi 0 := by rw [image_univ, Real.range_exp]
  simpa only [hset, he, integrableOn_univ, setIntegral_univ, v] using And.intro hi hJ

end

end Masullo
