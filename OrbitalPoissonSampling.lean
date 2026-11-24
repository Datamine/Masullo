import ManuscriptPrimaryOrbitalTrace
import RealLogFourier
import CompactPeriodization
import Mathlib.Analysis.Fourier.PoissonSummation
import ModulatedBruhatCompactCore

open Filter Function MeasureTheory NumberField IsDedekindDomain Set Topology
open scoped FourierTransform NumberField SchwartzMap

namespace Masullo
noncomputable section

private theorem scaledMellinPoisson (L : ℝ) (hL : 0 < L) (b : ℂ)
    (p : 𝓢(ℝ, ℂ)) (hp : HasCompactSupport p) :
    Summable (fun n : ℤ ↦ ‖∫ x : ℝ, p x * Complex.exp ((b -
      ((2 * Real.pi * (n : ℝ) / L : ℝ) : ℂ) * Complex.I) * (x : ℂ))‖) ∧
    HasSum (fun n : ℤ ↦ ∫ x : ℝ, p x * Complex.exp ((b -
      ((2 * Real.pi * (n : ℝ) / L : ℝ) : ℂ) * Complex.I) * (x : ℂ)))
      (∑' n : ℤ, (L : ℂ) * (p (L * n) * Complex.exp (b * ((L * n : ℝ) : ℂ)))) := by
  let g (x : ℝ) : ℂ := p x * Complex.exp (b * (x : ℂ))
  have hgc : HasCompactSupport g := hp.mul_right
  have hgs : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) g :=
    p.smooth'.mul (Complex.contDiff_exp.comp (contDiff_const.mul Complex.ofRealCLM.contDiff))
  let f := hgc.toSchwartzMap hgs
  let d := realSchwartzDilate L⁻¹ (inv_pos.mpr hL) f
  have hdf (n : ℤ) :
      (L : ℂ) * (𝓕 d) (n : ℝ) = ∫ x : ℝ, p x * Complex.exp ((b -
        ((2 * Real.pi * (n : ℝ) / L : ℝ) : ℂ) * Complex.I) * (x : ℂ)) := by
    rw [realFourier_dilate]
    have hscale (z : ℂ) : (L : ℂ) * (L⁻¹ • z) = z := by
      rw [Complex.real_smul, Complex.ofReal_inv, ← mul_assoc,
        mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hL.ne'), one_mul]
    rw [hscale, SchwartzMap.fourier_coe, Real.fourier_real_eq_integral_exp_smul]
    apply integral_congr_ae
    exact .of_forall fun x ↦ by
      change _ • (p x * Complex.exp (b * (x : ℂ))) = _
      rw [smul_eq_mul, mul_left_comm, ← Complex.exp_add]
      congr 2
      push_cast
      simp only [div_eq_mul_inv]
      ring
  obtain ⟨C, hC, hbound⟩ := schwartz_samples_periodic_bound (show (0 : ℝ) < 1 by norm_num)
  have hsum : Summable (fun n : ℤ ↦ ‖(𝓕 d) (n : ℝ)‖) := by
    simpa only [zero_add, mul_one] using
      (hbound 0 ⟨le_rfl,zero_lt_one⟩ (𝓕 d)).1
  refine ⟨?_,?_⟩
  · exact (hsum.mul_left ‖(L : ℂ)‖).congr (fun n ↦ (norm_mul _ _).symm.trans (congrArg norm (hdf n)))
  have hpoisson := SchwartzMap.tsum_eq_tsum_fourier d 0
  have hmode (n : ℤ) : fourier n ((0 : ℝ) : UnitAddCircle) = 1 :=
    fourier_eval_zero n
  simp only [zero_add,hmode,mul_one] at hpoisson
  have hv (n : ℤ) : d (n : ℝ) = p (L * n) * Complex.exp (b * ((L * n : ℝ) : ℂ)) := by
    rw [realSchwartzDilate_apply, inv_inv]
    rfl
  have hs := hsum.of_norm.hasSum.mul_left (L : ℂ)
  rw [← hpoisson, ← tsum_mul_left] at hs
  simpa only [hv] using hs.congr_fun (fun n ↦ (hdf n).symm)

section Angular

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  (m : G →ₜ* Multiplicative ℝ) (t : Multiplicative ℝ →ₜ* G) (ht : RightInverse t m)
  (U : Subgroup G) (hU : m.toMonoidHom.ker = U)
  [CompactSpace U] [MeasurableSpace U] [BorelSpace U]
  (η : Measure U) [η.IsHaarMeasure] (ψ : PontryaginDual U)

private def angularSchwartz : BruhatSchwartz G →L[ℂ] 𝓢(ℝ, ℂ) := by
  subst U
  exact bruhatAngularFourier m t ht η ψ

private theorem angularSchwartz_apply (f : BruhatSchwartz G) (x : ℝ) :
    angularSchwartz m t ht U hU η ψ f x =
      ∫ k : U, f.val (t (Multiplicative.ofAdd x) * k.val) * (ψ k : ℂ) ∂η := by
  subst U
  exact bruhatAngularFourier_apply m t ht η ψ f x

end Angular

variable (F : Type*) [Field F] [NumberField F]
private abbrev Q := IdeleClass F
private abbrev K := normOneIdeleClass F
private abbrev Place := HeightOneSpectrum (𝓞 F)

local instance : MeasurableSpace (Q F) := borel _
local instance : BorelSpace (Q F) := ⟨rfl⟩
local instance : T2Space (Q F) := ideleClasses_hausdorff
local instance : LocallyCompactSpace (Q F) := ideleClasses_locallyCompact
local instance : SecondCountableTopology (Q F) := ideleClass_secondCountable F
local instance : MeasurableSpace (K F) := borel _
local instance : BorelSpace (K F) := ⟨rfl⟩
local instance : CompactSpace (K F) := normOneIdeleClass_compact F

variable (ν : Measure (K F)) [ν.IsHaarMeasure]
private abbrev μ := globalClassMeasure F ν
private abbrev τ := ideleClassExpSection F
private abbrev r (g : Q F) := (ideleClassLogNorm F g).toAdd
private abbrev qlog (v : Place F) := Real.log (v.asIdeal.absNorm : ℝ)
private abbrev u (v : Place F) := globalUniformizerClass F v
private abbrev ω (χ : PontryaginDual (Q F)) := heckeNormOneRestriction F χ

private theorem qlog_pos (v : Place F) : 0 < qlog F v :=
  Real.log_pos (by exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v)

private theorem log_uniformizer (v : Place F) : r F (u F v) = -qlog F v := by
  change Real.log (ideleClassNorm F
    (ideleClassMap F (singleFiniteIdele F v (chosenFiniteUniformizer F v)))) = _
  rw [ideleClassNorm_mk, singleFiniteIdele_norm, norm_finiteUniformizer F v _
    (chosenFiniteUniformizer_spec F v), Real.log_inv]

private theorem log_inv_uniformizer_pow (v : Place F) (n : ℤ) : r F (u F v ^ (-n)) = qlog F v * n := by
  change ((ideleClassLogNorm F) (u F v ^ (-n))).toAdd = _
  rw [map_zpow, toAdd_zpow, zsmul_eq_mul]
  change ((-n : ℤ) : ℝ) * r F (u F v) = _
  rw [log_uniformizer, Int.cast_neg]
  ring

private abbrev PlaceZeros (χ : PontryaginDual (Q F)) (v : Place F) :=
  {z : ℂ // orbitalEulerDenominator F {v} χ z = 0}

private def placeZero (v : Place F) (a : ℝ) (n : ℤ) : ℂ :=
  ((((-2 * Real.pi * (n : ℝ) / qlog F v - a : ℝ) : ℂ)) * Complex.I)

private theorem exists_placeZeroEquiv (χ : PontryaginDual (Q F)) (v : Place F) :
    ∃ a : ℝ, Circle.exp (a * qlog F v) = (χ (u F v))⁻¹ ∧
      ∃ e : ℤ ≃ PlaceZeros F χ v, ∀ n, (e n).val = placeZero F v a n := by
  let ψ := χ.comp (finitePlaceInsertion F v)
  have huv : finitePlaceInsertion F v (chosenFiniteUniformizer F v) = u F v :=
    finitePlaceInsertion_apply F v _
  obtain ⟨a,_,ha⟩ := (existsUnique_circle_log_period (qlog_pos F v) (χ (u F v))⁻¹).exists
  have ha' : Circle.exp (a * qlog F v) = (ψ (chosenFiniteUniformizer F v))⁻¹ := by
    change _ = (χ (finitePlaceInsertion F v (chosenFiniteUniformizer F v)))⁻¹
    rwa [huv]
  have hz (z : ℂ) : orbitalEulerDenominator F {v} χ z = 0 ↔
      ∃ n : ℤ, z = placeZero F v a n := by
    have hd : orbitalEulerDenominator F {v} χ z = finiteZetaDenominator F v ψ z := by
      unfold orbitalEulerDenominator finiteZetaDenominator finiteZetaRatio
      rw [Finset.prod_singleton]
      change 1 - (χ (u F v) : ℂ) * _ =
        1 - (χ (finitePlaceInsertion F v (chosenFiniteUniformizer F v)) : ℂ) * _
      rw [huv]
    rw [hd, finiteZetaDenominator_eq_zero_iff_lattice F v ψ a ha']
    constructor
    · rintro ⟨n,rfl⟩
      refine ⟨-n, ?_⟩
      unfold placeZero qlog
      push_cast
      ring
    · rintro ⟨n,rfl⟩
      refine ⟨-n, ?_⟩
      unfold placeZero qlog
      push_cast
      ring
  let e (n : ℤ) : PlaceZeros F χ v := ⟨placeZero F v a n, (hz _).mpr ⟨n,rfl⟩⟩
  have he : Bijective e := by
    constructor
    · intro m n he
      have him := congrArg (fun z : PlaceZeros F χ v ↦ z.val.im) he
      change (placeZero F v a m).im = (placeZero F v a n).im at him
      simp only [placeZero, Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one,
        Complex.ofReal_im, Complex.I_re, mul_zero, add_zero] at him
      have hL := (qlog_pos F v).ne'
      have hp := Real.pi_pos
      apply Int.cast_injective (α := ℝ)
      have h := (div_left_inj' hL).mp (sub_left_inj.mp him)
      nlinarith
    · rintro ⟨z,h⟩
      obtain ⟨n,hn⟩ := (hz z).mp h
      exact ⟨n, Subtype.ext hn.symm⟩
  exact ⟨a,ha,Equiv.ofBijective e he,fun _ ↦ rfl⟩

private abbrev logHom : Q F →ₜ* Multiplicative ℝ :=
  ⟨ideleClassLogNorm F, ideleClassLogNorm_continuous F⟩
private abbrev rayHom : Multiplicative ℝ →ₜ* Q F :=
  ⟨τ F, ideleClassExpSection_continuous F⟩

private theorem rayRightInverse : RightInverse (rayHom F) (logHom F) :=
  ideleClassLogNorm_expSection F

private def angularProfile (χ : PontryaginDual (Q F)) (φ : BruhatCompactTest (Q F)) : 𝓢(ℝ, ℂ) :=
  angularSchwartz (logHom F) (rayHom F) (rayRightInverse F)
    (K F) (ideleClassLogNorm_ker_eq_normOne F) ν (ω F χ) φ.val

set_option maxHeartbeats 3500000 in
private theorem angularProfile_apply (χ : PontryaginDual (Q F)) (φ : BruhatCompactTest (Q F)) (x : ℝ) :
    angularProfile F ν χ φ x = ∫ k : K F,
      φ.val.val (τ F (Multiplicative.ofAdd x) * k.val) * (χ k.val : ℂ) ∂ν := by
  unfold angularProfile
  have h := angularSchwartz_apply (logHom F) (rayHom F) (rayRightInverse F)
    (K F) (ideleClassLogNorm_ker_eq_normOne F) ν (ω F χ) φ.val x
  refine h.trans ?_
  apply integral_congr_ae
  exact .of_forall fun k ↦ rfl

private theorem angularProfile_compact (χ : PontryaginDual (Q F)) (φ : BruhatCompactTest (Q F)) :
    HasCompactSupport (angularProfile F ν χ φ) := by
  let C := r F '' tsupport φ.val.val
  have hc : IsCompact C := (BruhatCompactTest.algebraicEquiv φ).property.image
    (continuous_toAdd.comp (ideleClassLogNorm_continuous F))
  apply hc.of_isClosed_subset isClosed_closure
  apply closure_minimal _ hc.isClosed
  intro x hx
  by_contra hn
  have hf (k : K F) : φ.val.val (τ F (Multiplicative.ofAdd x) * k.val) = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hk
    apply hn
    refine ⟨_, hk, ?_⟩
    change (ideleClassLogNorm F (τ F (Multiplicative.ofAdd x) * k.val)).toAdd = x
    have hw : ideleClassLogNorm F k.val = 1 := by
      change Multiplicative.ofAdd (Real.log (ideleClassNorm F k.val)) = _
      rw [k.property, Real.log_one]
      rfl
    rw [map_mul, ideleClassLogNorm_expSection, hw, mul_one]
    rfl
  change angularProfile F ν χ φ x ≠ 0 at hx
  exact hx ((angularProfile_apply F ν χ φ x).trans (by simp [hf]))

set_option maxHeartbeats 1400000 in
private theorem mellin_eq_radial (χ : PontryaginDual (Q F)) (φ : BruhatCompactTest (Q F))
    (h : ℝ) (hh : HasHeckeHeight F χ h) (z : ℂ) :
    orbitalConvolutionCoefficient F (μ F ν) φ.val.val χ z 0 =
      ∫ x : ℝ, angularProfile F ν χ φ x * Complex.exp ((z - (h : ℂ) * Complex.I) * (x : ℂ)) := by
  let e := (ideleClassLogCoordinates F).toMeasurableEquiv
  let g (q : Q F) := φ.val.val q * orbitalMomentPhase F χ z q * (r F q : ℂ)^0
  let b (y : ℝ × K F) : ℂ := Complex.exp ((z - (h : ℂ) * Complex.I) * (y.1 : ℂ)) *
    (φ.val.val (e y) * (χ y.2.val : ℂ))
  have hb : Integrable b (volume.prod ν) := by
    have hφ : HasCompactSupport φ.val.val := (BruhatCompactTest.algebraicEquiv φ).property
    have he : Continuous (fun y : ℝ × K F ↦ e y) := (ideleClassLogCoordinates F).continuous
    have ht : Continuous (fun y : ℝ × K F ↦ φ.val.val (e y)) :=
      (bruhatSchwartz_continuous φ.val).comp he
    have hχ : Continuous (fun y : ℝ × K F ↦ (χ y.2.val : ℂ)) :=
      (continuous_subtype_val.comp χ.continuous).comp (continuous_subtype_val.comp continuous_snd)
    have hex : Continuous (fun y : ℝ × K F ↦ Complex.exp ((z - (h : ℂ) * Complex.I) * (y.1 : ℂ))) :=
      Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp continuous_fst))
    exact (hex.mul (ht.mul hχ)).integrable_of_hasCompactSupport
      ((hφ.comp_homeomorph (ideleClassLogCoordinates F)).mul_right.mul_left)
  have hg (y : ℝ × K F) : g (e y) = b y := by
    have hL : r F (e y) = y.1 := congrArg Prod.fst ((ideleClassLogCoordinates F).symm_apply_apply y)
    have hK : ideleClassNormOnePart F (e y) = y.2 :=
      congrArg Prod.snd ((ideleClassLogCoordinates F).symm_apply_apply y)
    unfold g
    rw [orbitalMomentPhase_heckeHeight F χ h hh]
    change (φ.val.val (e y) * ((χ (ideleClassNormOnePart F (e y)).val : ℂ) *
      Complex.exp ((z - (h : ℂ) * Complex.I) * (r F (e y) : ℂ)))) * (r F (e y) : ℂ)^0 = b y
    rw [hL,hK,pow_zero,mul_one]
    unfold b
    ring
  change (∫ q, g q ∂Measure.map e (volume.prod ν)) = _
  rw [integral_map_equiv]
  simp_rw [hg]
  rw [integral_prod _ hb]
  apply integral_congr_ae
  refine .of_forall fun x ↦ ?_
  change (∫ k : K F, b (x,k) ∂ν) =
    angularProfile F ν χ φ x * Complex.exp ((z - (h : ℂ) * Complex.I) * (x : ℂ))
  let B := Complex.exp ((z - (h : ℂ) * Complex.I) * (x : ℂ))
  change (∫ k : K F, B * (φ.val.val (e (x,k)) * (χ k.val : ℂ)) ∂ν) =
    angularProfile F ν χ φ x * B
  rw [integral_const_mul, angularProfile_apply, mul_comm B]
  apply congrArg (· * B)
  apply integral_congr_ae
  exact .of_forall fun k ↦
    congrArg (fun q : Q F ↦ φ.val.val q * (χ k.val : ℂ))
      (mul_comm k.val (τ F (Multiplicative.ofAdd x)))

/-- The place contribution samples the norm-one character average on the
uniformizer coset. The exponent `n` labels the inverse uniformizer, which
has positive logarithmic norm. The real shift `b` supplies its norm weight. -/
def orbitalPlacePoissonSample (χ : PontryaginDual (Q F)) (φ : BruhatCompactTest (Q F))
    (v : Place F) (b : ℝ) (n : ℤ) : ℂ :=
  (qlog F v : ℂ) * ((Real.exp (b * (qlog F v * n))) : ℂ) *
    ∫ k : K F, φ.val.val (u F v ^ (-n) * k.val) * (χ k.val : ℂ) ∂ν

set_option maxHeartbeats 1800000 in
private theorem angularProfile_sample (χ : PontryaginDual (Q F))
    (φ : BruhatCompactTest (Q F)) (v : Place F) (h a : ℝ)
    (hh : HasHeckeHeight F χ h) (ha : Circle.exp (a * qlog F v) = (χ (u F v))⁻¹)
    (b : ℝ) (n : ℤ) :
    (qlog F v : ℂ) * (angularProfile F ν χ φ (qlog F v * n) *
      Complex.exp (((b : ℂ) - ((a : ℂ) + (h : ℂ)) * Complex.I) *
        ((qlog F v * n : ℝ) : ℂ))) =
      orbitalPlacePoissonSample F ν χ φ v b n := by
  let g := u F v ^ (-n)
  let x := qlog F v * n
  let k₀ := ideleClassNormOnePart F g
  have hx : r F g = x := log_inv_uniformizer_pow F v n
  have hg : g = τ F (Multiplicative.ofAdd x) * k₀.val := by
    change g = τ F (Multiplicative.ofAdd x) * (g / τ F (ideleClassLogNorm F g))
    rw [show ideleClassLogNorm F g = Multiplicative.ofAdd x from hx]
    exact ((mul_comm (τ F (Multiplicative.ofAdd x)) _).trans (div_mul_cancel _ _)).symm
  have hAng : angularProfile F ν χ φ x =
      (χ k₀.val : ℂ) * ∫ k : K F, φ.val.val (g * k.val) * (χ k.val : ℂ) ∂ν := by
    rw [angularProfile_apply, ← integral_const_mul]
    let I (k : K F) := φ.val.val (τ F (Multiplicative.ofAdd x) * k.val) * (χ k.val : ℂ)
    change (∫ k : K F, I k ∂ν) = _
    rw [← integral_mul_left_eq_self I k₀]
    apply integral_congr_ae
    exact .of_forall fun k ↦ by
      have he : τ F (Multiplicative.ofAdd x) * (k₀*k).val = g * k.val := by
        rw [Subgroup.coe_mul, ← mul_assoc, ← hg]
      change φ.val.val (τ F (Multiplicative.ofAdd x) * (k₀*k).val) * (χ (k₀.val * k.val) : ℂ) = _
      rw [he, map_mul, Circle.coe_mul]
      ring
  have ha' := congrArg (fun z : Circle ↦ (z : ℂ)) ha
  rw [Circle.coe_exp, Circle.coe_inv] at ha'
  have ha₀ : Complex.exp (-(a : ℂ) * Complex.I * (qlog F v : ℂ)) = (χ (u F v) : ℂ) := by
    rw [show -(a : ℂ) * Complex.I * (qlog F v : ℂ) =
        -((↑(a * qlog F v) : ℂ) * Complex.I) by push_cast; ring,
      Complex.exp_neg, ha', inv_inv]
  have ha₁ : Complex.exp (-(a : ℂ) * Complex.I * (x : ℂ)) = (χ g : ℂ)⁻¹ := by
    rw [show -(a : ℂ) * Complex.I * (x : ℂ) =
        ((n : ℂ) * (-(a : ℂ) * Complex.I * (qlog F v : ℂ))) by dsimp [x]; push_cast; ring,
      Complex.exp_int_mul, ha₀]
    change (χ (u F v) : ℂ)^n = (χ (u F v ^ (-n)) : ℂ)⁻¹
    rw [map_zpow, Circle.coe_zpow, zpow_neg, inv_inv]
  have hh₁ : (χ k₀.val : ℂ) * Complex.exp (-(h : ℂ) * Complex.I * (x : ℂ)) = (χ g : ℂ) := by
    have he := hh g
    change (χ g : ℂ) = (χ k₀.val : ℂ) * Complex.exp (-((h : ℂ) * Complex.I) * (r F g : ℂ)) at he
    simpa only [hx, neg_mul] using he.symm
  have hExp : Complex.exp (((b : ℂ) - ((a : ℂ) + (h : ℂ)) * Complex.I) * (x : ℂ)) =
      (Real.exp (b*x) : ℂ) * (Complex.exp (-(h : ℂ) * Complex.I * (x : ℂ)) * (χ g : ℂ)⁻¹) := by
    rw [show ((b : ℂ) - ((a : ℂ) + (h : ℂ)) * Complex.I) * (x : ℂ) =
        ((b*x : ℝ) : ℂ) + (-(h : ℂ) * Complex.I * (x : ℂ) + (-(a : ℂ) * Complex.I * (x : ℂ)))
        by push_cast; ring,
      Complex.exp_add, Complex.exp_add, ← Complex.ofReal_exp, ha₁]
  change (qlog F v : ℂ) * (angularProfile F ν χ φ x * _) = _
  rw [hAng, hExp]
  unfold orbitalPlacePoissonSample
  change _ = (qlog F v : ℂ) * (Real.exp (b*x) : ℂ) * _
  let A := ∫ k : K F, φ.val.val (g * k.val) * (χ k.val : ℂ) ∂ν
  calc
    _ = (qlog F v : ℂ) * (Real.exp (b*x) : ℂ) * A *
      (((χ k₀.val : ℂ) * Complex.exp (-(h : ℂ) * Complex.I * (x : ℂ))) * (χ g : ℂ)⁻¹) := by ring
    _ = _ := by rw [hh₁, mul_inv_cancel₀ (Circle.coe_ne_zero _), mul_one]

set_option maxHeartbeats 1400000 in
/-- At one finite place the shifted Mellin values on its Euler-zero lattice
sum to the weighted angular samples. The half-shift in §11.3 is `b = -1/2`. -/
theorem orbitalEulerPlacePoisson (χ : PontryaginDual (Q F))
    (φ : BruhatCompactTest (Q F)) (v : Place F) (b : ℝ) :
    Summable (fun z : PlaceZeros F χ v ↦ ‖orbitalConvolutionCoefficient F (μ F ν) φ.val.val χ
      (z.val + (b : ℂ)) 0‖) ∧
    HasSum (fun z : PlaceZeros F χ v ↦ orbitalConvolutionCoefficient F (μ F ν) φ.val.val χ
      (z.val + (b : ℂ)) 0)
      (∑' n : ℤ, orbitalPlacePoissonSample F ν χ φ v b n) := by
  obtain ⟨h,hh,_⟩ := existsUnique_heckeHeight F χ
  obtain ⟨a,ha,e,he⟩ := exists_placeZeroEquiv F χ v
  let p := angularProfile F ν χ φ
  let c : ℂ := (b : ℂ) - ((a : ℂ) + (h : ℂ)) * Complex.I
  obtain ⟨hAbs,hs⟩ := scaledMellinPoisson (qlog F v) (qlog_pos F v) c p
    (angularProfile_compact F ν χ φ)
  have hval (n : ℤ) := angularProfile_sample F ν χ φ v h a hh ha b n
  simp_rw [show ∀ n : ℤ, (qlog F v : ℂ) *
      (p (qlog F v * n) * Complex.exp (c * ((qlog F v*n : ℝ) : ℂ))) =
        orbitalPlacePoissonSample F ν χ φ v b n from hval] at hs
  have hInt (n : ℤ) : orbitalConvolutionCoefficient F (μ F ν) φ.val.val χ
      ((e n).val + (b : ℂ)) 0 =
      ∫ x : ℝ, p x * Complex.exp ((c - ((2 * Real.pi * (n : ℝ) / qlog F v : ℝ) : ℂ) *
        Complex.I) * (x : ℂ)) := by
    rw [mellin_eq_radial F ν χ φ h hh, he]
    have hex : c - ((2 * Real.pi * (n : ℝ) / qlog F v : ℝ) : ℂ) * Complex.I =
        placeZero F v a n + (b : ℂ) - (h : ℂ) * Complex.I := by
      unfold c placeZero
      push_cast
      ring
    rw [hex]
  exact ⟨e.summable_iff.mp (hAbs.congr (fun n ↦ congrArg norm (hInt n).symm)),
    e.hasSum_iff.mp (hs.congr_fun (fun n ↦ hInt n))⟩

private abbrev EulerZeros (A : Finset (Place F)) (χ : PontryaginDual (Q F)) :=
  {z : ℂ // orbitalEulerDenominator F A χ z = 0}

private theorem denominator_product_singletons (A : Finset (Place F)) (χ : PontryaginDual (Q F))
    (z : ℂ) : orbitalEulerDenominator F A χ z =
      ∏ v ∈ A, orbitalEulerDenominator F {v} χ z := by
  unfold orbitalEulerDenominator
  simp only [Finset.prod_singleton]

private def zerosByPlaceEquiv (A : Finset (Place F)) (χ : PontryaginDual (Q F)) :
    (Σ v : A, PlaceZeros F χ v.val) ≃
      (Σ z : EulerZeros F A χ, {v : A // orbitalEulerDenominator F {v.val} χ z.val = 0}) where
  toFun vz :=
    ⟨⟨vz.2.val, by
      rw [denominator_product_singletons]
      exact Finset.prod_eq_zero vz.1.property vz.2.property⟩, ⟨vz.1,vz.2.property⟩⟩
  invFun zv := ⟨zv.2.val, ⟨zv.1.val,zv.2.property⟩⟩
  left_inv := by rintro ⟨v,z⟩; rfl
  right_inv := by rintro ⟨z,v⟩; rfl

set_option maxHeartbeats 1500000 in
/-- Summing over all places counts a common Euler zero once for each
vanishing local factor. The analytic multiplicity is exactly that count. -/
theorem orbitalEulerPoisson_sum (A : Finset (Place F)) (χ : PontryaginDual (Q F))
    (φ : BruhatCompactTest (Q F)) (b : ℝ) :
    (∑' z : EulerZeros F A χ,
      ((analyticOrderAt (orbitalEulerDenominator F A χ) z.val).toNat : ℂ) *
        orbitalConvolutionCoefficient F (μ F ν) φ.val.val χ (z.val + (b : ℂ)) 0) =
      ∑ v ∈ A, ∑' n : ℤ, orbitalPlacePoissonSample F ν χ φ v b n := by
  classical
  let f (z : ℂ) := orbitalConvolutionCoefficient F (μ F ν) φ.val.val χ (z + (b : ℂ)) 0
  let G (vz : Σ v : A, PlaceZeros F χ v.val) := f vz.2.val
  have hG : Summable (fun vz ↦ ‖G vz‖) := by
    apply (summable_sigma_of_nonneg (fun _ ↦ norm_nonneg _)).mpr
    refine ⟨fun v ↦ (orbitalEulerPlacePoisson F ν χ φ v.val b).1, ?_⟩
    exact (hasSum_fintype _).summable
  let Z := EulerZeros F A χ
  let B (z : Z) := {v : A // orbitalEulerDenominator F {v.val} χ z.val = 0}
  let e := zerosByPlaceEquiv F A χ
  have hB : Summable (fun zv : Σ z : Z, B z ↦ ‖f zv.1.val‖) :=
    (e.summable_iff (f := fun zv : Σ z : Z, B z ↦ ‖f zv.1.val‖)).mp hG
  have hcard (z : Z) : Fintype.card (B z) = (analyticOrderAt (orbitalEulerDenominator F A χ) z.val).toNat := by
    let D := A.filter (fun v ↦ orbitalEulerDenominator F {v} χ z.val = 0)
    have hi : B z ≃ D :=
      { toFun := fun v ↦ ⟨v.val.val,Finset.mem_filter.mpr ⟨v.val.property,v.property⟩⟩
        invFun := fun v ↦ ⟨⟨v.val,(Finset.mem_filter.mp v.property).1⟩,(Finset.mem_filter.mp v.property).2⟩
        left_inv := by intro v; rfl
        right_inv := by intro v; rfl }
    rw [Fintype.card_congr hi, Fintype.card_coe, orbitalEulerDenominator_order_eq_card]
    simp [D, orbitalEulerDenominator]
  calc
    _ = ∑' z : Z, ∑' _ : B z, f z.val := by
      apply tsum_congr
      intro z
      rw [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
    _ = ∑' zv : Σ z : Z, B z, f zv.1.val := hB.of_norm.tsum_sigma.symm
    _ = ∑' vz, G vz := (e.tsum_eq (fun zv : Σ z : Z, B z ↦ f zv.1.val)).symm
    _ = _ := by
      rw [hG.of_norm.tsum_sigma, tsum_fintype]
      change (∑ v ∈ A.attach, ∑' z : PlaceZeros F χ v.val, f z.val) = _
      calc
        _ = ∑ v ∈ A.attach, ∑' (n : ℤ), orbitalPlacePoissonSample F ν χ φ v.val b n :=
          Finset.sum_congr rfl (fun v _ ↦ (orbitalEulerPlacePoisson F ν χ φ v.val b).2.tsum_eq)
        _ = _ := Finset.sum_attach A (fun v ↦ ∑' n : ℤ, orbitalPlacePoissonSample F ν χ φ v b n)

/-- The shifted Euler-zero side of (11.3.2.5) in the manuscript's
complex-power coordinate equals the weighted place sum. -/
theorem orbitalEulerHalfShiftPoisson (A : Finset (Place F)) (χ : PontryaginDual (Q F))
    (φ : BruhatCompactTest (Q F)) :
    (∑' z : EulerZeros F A χ,
      (analyticOrderNatAt (orbitalEulerDenominator F A χ) z.val : ℂ) *
        ∫ g, φ.val.val g * (χ g : ℂ) *
          (ideleClassNorm F g : ℂ)^(z.val - 1/2) ∂μ F ν) =
      ∑ v ∈ A, ∑' n : ℤ, orbitalPlacePoissonSample F ν χ φ v (-1/2) n := by
  have h := orbitalEulerPoisson_sum F ν A χ φ (-1/2)
  convert h using 1
  apply tsum_congr
  intro z
  change ((analyticOrderAt (orbitalEulerDenominator F A χ) z.val).toNat : ℂ) * _ = _ * _
  rw [orbitalConvolutionCoefficient_zero_eq_integral]
  norm_num [sub_eq_add_neg]

set_option maxHeartbeats 2400000 in
/-- A real norm twist of the convolution test, in its original Bruhat topology. -/
def orbitalShiftedBruhatTest (b : ℝ) (φ : BruhatCompactTest (Q F)) : BruhatCompactTest (Q F) := by
  let f (g : Q F) : ℂ := Real.exp (b * r F g) • φ.val.val g
  have hSmooth : f ∈ bruhatSmoothSubmodule (G := Q F) :=
    bruhatSmooth_realModulation_smul (logHom F) b (bruhatSchwartz_le_smooth φ.val.property)
  have hc : HasCompactSupport f := φ.property.mono fun g hg hzero ↦ hg (by simp [f,hzero])
  exact BruhatCompactTest.algebraicEquiv.symm ⟨⟨f,bruhatSchwartz_mem_of_smooth_compactSupport hSmooth hc⟩,hc⟩

omit [ν.IsHaarMeasure] in
set_option maxHeartbeats 2400000 in
private theorem orbitalShiftedBruhatTest_coefficient (b : ℝ)
    (φ : BruhatCompactTest (Q F)) (χ : PontryaginDual (Q F)) (z : ℂ) :
    orbitalConvolutionCoefficient F (μ F ν) (orbitalShiftedBruhatTest F b φ).val.val χ z 0 =
      orbitalConvolutionCoefficient F (μ F ν) φ.val.val χ (z + (b : ℂ)) 0 := by
  unfold orbitalConvolutionCoefficient
  apply integral_congr_ae
  exact .of_forall fun g ↦ by
    have hval : (orbitalShiftedBruhatTest F b φ).val.val g =
        (Real.exp (b * r F g) : ℂ) * φ.val.val g := by
      unfold orbitalShiftedBruhatTest BruhatCompactTest.val
      rw [LinearEquiv.apply_symm_apply]
      rfl
    simp only [hval,pow_zero,mul_one,orbitalMomentPhase]
    rw [add_mul, Complex.exp_add, Complex.ofReal_exp, Complex.ofReal_mul]
    ring

local instance : (μ F ν).IsHaarMeasure := globalClassMeasure_isHaar F ν
local instance (s : ℝ) (hs : 0 ≤ s) (ψ : PontryaginDual (K F)) :
    CompleteSpace (globalOrbitalSobolevIsotype F (μ F ν) s hs ψ) :=
  (globalOrbitalSobolevIsotype_isClosed F (μ F ν) s hs ψ).completeSpace_coe

set_option maxHeartbeats 1500000 in
/-- For a primary factor the trace of the actual completed orbital
compression with a shifted test has the corrected Poisson sampling formula.
The source's half-shift is `b = -1/2`. -/
theorem exists_primaryOrbitalTrace_poisson
    (A : Finset (Place F)) {p : ℕ} (hp : p.Prime)
    (hA : ∀ v ∈ A, v.asIdeal.under ℤ = Ideal.span {(p : ℤ)})
    (s : ℝ) (hs : 0 ≤ s) (hDegree : 2 * (Module.finrank ℚ F : ℝ) ≤ s) (hs' : 1 < s)
    (χ : PontryaginDual (Q F)) (hχ : ∀ v ∈ A, unramifiedFiniteCharacter F χ v) :
    let R := globalWeilIsotypeClosedRange F (μ F ν) s hs A (ω F χ)
    ∃ L : BruhatCompactTest (Q F) →L[ℂ] TraceClass (Rᗮ),
      (∀ φ : BruhatCompactTest (Q F), (L φ).toOperator =
        primaryOrbitalCompressedConvolution F (μ F ν) s hs A (ω F χ) (primaryOrbitalBruhatDensity F φ)) ∧
      ∀ (b : ℝ) (φ : BruhatCompactTest (Q F)), (L (orbitalShiftedBruhatTest F b φ)).traceValue =
        ∑ v ∈ A, ∑' n : ℤ, orbitalPlacePoissonSample F ν χ φ v b n := by
  obtain ⟨L,hL⟩ := exists_manuscriptPrimaryOrbitalTrace F (μ F ν) s hs A hp hA hDegree hs' χ hχ
  refine ⟨L,fun φ ↦ (hL φ).1,fun b φ ↦ ?_⟩
  have h := (hL (orbitalShiftedBruhatTest F b φ)).2.2
  rw [h]
  simp_rw [orbitalShiftedBruhatTest_coefficient F ν b φ χ]
  exact orbitalEulerPoisson_sum F ν A χ φ b

/-- A place contributes no Poisson sample if the test is supported at norms
strictly between one and that place's residue size. -/
theorem orbitalPlacePoissonSample_eq_zero_of_small_norm_support
    (χ : PontryaginDual (Q F)) (φ : BruhatCompactTest (Q F)) (v : Place F) (b : ℝ) (n : ℤ)
    (hφ : ∀ g ∈ tsupport φ.val.val, ideleClassNorm F g ∈ Ioo 1 (v.asIdeal.absNorm : ℝ)) :
    orbitalPlacePoissonSample F ν χ φ v b n = 0 := by
  have hz (k : K F) : φ.val.val (u F v ^ (-n) * k.val) = 0 := by
    by_contra hn
    let g := u F v ^ (-n) * k.val
    have hg := hφ g (subset_closure hn)
    have hk : ideleClassLogNorm F k.val = 1 := by
      change Multiplicative.ofAdd (Real.log (ideleClassNorm F k.val)) = _
      rw [k.property, Real.log_one]
      rfl
    have hlog : r F g = qlog F v * n := by
      change ((ideleClassLogNorm F) (u F v ^ (-n) * k.val)).toAdd = _
      rw [map_mul,hk,mul_one]
      exact log_inv_uniformizer_pow F v n
    have h₀ : 0 < r F g := (Real.log_pos_iff (ideleClassNorm_pos F g).le).mpr hg.1
    have hq : (0 : ℝ) < v.asIdeal.absNorm := zero_lt_one.trans
      (by exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v)
    have h₁ : r F g < qlog F v :=
      (Real.log_lt_log_iff (ideleClassNorm_pos F g) hq).mpr hg.2
    rw [hlog] at h₀ h₁
    have hp := qlog_pos F v
    have hn₀ : (0 : ℤ) < n := by exact_mod_cast (pos_of_mul_pos_right h₀ hp.le)
    have hn₁ : n < (1 : ℤ) := by
      have hh : (n : ℝ) < 1 := by
        by_contra hnot
        nlinarith [mul_nonneg hp.le (sub_nonneg.mpr (le_of_not_gt hnot))]
      exact_mod_cast hh
    omega
  simp [orbitalPlacePoissonSample,hz]

end
end Masullo
