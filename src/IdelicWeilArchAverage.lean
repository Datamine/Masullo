import IdelicWeilArchSamples
import IdelicWeilPrimeSamples

open Filter Function IsDedekindDomain MeasureTheory Metric NumberField Set Topology
open scoped Classical ENNReal NumberField

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

private abbrev K := normOneIdeleClass F
private abbrev R := {v : InfinitePlace F // v.IsReal}
private abbrev C := {v : InfinitePlace F // v.IsComplex}
private abbrev Place := HeightOneSpectrum (𝓞 F)

local instance weilArchAvgClassLC : LocallyCompactSpace (IdeleClass F) := ideleClasses_locallyCompact
local instance weilArchAvgClassT2 : T2Space (IdeleClass F) := ideleClasses_hausdorff
local instance weilArchAvgNormOneMeasurable : MeasurableSpace (K F) := borel _
local instance weilArchAvgNormOneBorel : BorelSpace (K F) := ⟨rfl⟩

set_option maxHeartbeats 900000

/-- The complex unit at positive radius and the specified angle. -/
def complexWeilCircleUnit (r : ℝ) (hr : 0 < r) (θ : ℝ) : ℂˣ :=
  Units.mk0 (circleMap 0 r θ) (norm_ne_zero_iff.mp (by
    rw [norm_circleMap_zero, abs_of_pos hr]
    exact hr.ne'))

private theorem complexWeilCircleUnit_continuous (r : ℝ) (hr : 0 < r) :
    Continuous (complexWeilCircleUnit r hr) := by
  apply Units.continuous_iff.mpr
  have h : Continuous (circleMap (0 : ℂ) r) := (continuous_circleMap 0 r)
  exact ⟨h, h.inv₀ fun θ => (complexWeilCircleUnit r hr θ).ne_zero⟩

/-- The squared-distance cutoff kernel restricted to a circle around zero. -/
def complexWeilCircleKernel (r θ : ℝ) : ℝ := (‖1 - circleMap 0 r θ‖ ^ 2)⁻¹

private theorem complexWeilCircleKernel_le (r : ℝ) (hr : 0 < r) (hne : r ≠ 1) (θ : ℝ) :
    complexWeilCircleKernel r θ ≤ (|1 - r| ^ 2)⁻¹ := by
  have h : |1 - r| ≤ ‖1 - circleMap 0 r θ‖ := by
    have h := abs_norm_sub_norm_le (1 : ℂ) (circleMap 0 r θ)
    rwa [norm_one, norm_circleMap_zero, abs_of_pos hr] at h
  exact inv_anti₀ (pow_pos (abs_pos.mpr (sub_ne_zero.mpr hne.symm)) _) (pow_le_pow_left₀ (abs_nonneg _) h _)

private theorem complexWeilCircleKernel_measurable (r : ℝ) :
    Measurable (complexWeilCircleKernel r) :=
  (((continuous_const.sub (continuous_circleMap (0 : ℂ) r)).norm.pow 2).measurable).inv

private def complexWeilCircleMeasure (r : ℝ) : Measure ℝ :=
  (volume.restrict (Ioc 0 (2 * Real.pi))).withDensity (fun θ =>
    ENNReal.ofReal (complexWeilCircleKernel r θ))

private theorem complexWeilCircleMeasure_finite (r : ℝ) (hr : 0 < r) (hne : r ≠ 1) :
    IsFiniteMeasure (complexWeilCircleMeasure r) := by
  let T := Ioc (0 : ℝ) (2 * Real.pi)
  letI : IsFiniteMeasure (volume.restrict T : Measure ℝ) := ⟨by rw [Measure.restrict_apply_univ, show T = _ from rfl, Real.volume_Ioc]; exact ENNReal.ofReal_lt_top⟩
  apply isFiniteMeasure_withDensity
  have hle :
      (∫⁻ θ in T, ENNReal.ofReal (complexWeilCircleKernel r θ)) ≤
        (∫⁻ _θ in T, ENNReal.ofReal (|1 - r| ^ 2)⁻¹) :=
    lintegral_mono fun θ => ENNReal.ofReal_le_ofReal (complexWeilCircleKernel_le r hr hne θ)
  refine (hle.trans_lt ?_).ne
  rw [lintegral_const]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)

private theorem complexWeilCircleMeasure_integral (r : ℝ) (g : ℝ → ℂ) :
    (∫ θ, g θ ∂complexWeilCircleMeasure r) =
      ∫ θ in (0 : ℝ)..2 * Real.pi, complexWeilCircleKernel r θ • g θ := by
  rw [complexWeilCircleMeasure, integral_withDensity_eq_integral_toReal_smul
    (complexWeilCircleKernel_measurable r).ennreal_ofReal (.of_forall fun _ => ENNReal.ofReal_lt_top),
    intervalIntegral.integral_of_le (by positivity)]
  have hnonneg (θ : ℝ) : 0 ≤ complexWeilCircleKernel r θ := inv_nonneg.mpr (sq_nonneg _)
  simp only [ENNReal.toReal_ofReal (hnonneg _)]

variable (ν : Measure (K F)) [ν.IsHaarMeasure]

/-- The complex-place weighted angular integral at each nonsingular radius
can be taken term by term in the norm-one Fourier expansion. -/
theorem idelicWeil_complexCircle_hasSum (f : BruhatCompactTest (IdeleClass F))
    (v : C F) (r : ℝ) (hr : 0 < r) (hne : r ≠ 1) :
    let A (θ : ℝ) := complexPlaceWeilInsertion F v.val v.property (complexWeilCircleUnit r hr θ)
    HasSum (fun ω : PontryaginDual (K F) =>
      ((ν.real univ : ℂ)⁻¹ * idelicWeilLogProfile F ν ω f (Real.log (r ^ 2))) *
        ((2 * Real.pi)⁻¹ • ∫ θ in (0 : ℝ)..2 * Real.pi,
          complexWeilCircleKernel r θ • (((normOneEulerCharacter F ω (A θ))⁻¹ : Circle) : ℂ)))
      ((2 * Real.pi)⁻¹ • ∫ θ in (0 : ℝ)..2 * Real.pi,
        complexWeilCircleKernel r θ • f.val.val (A θ)) := by
  let A (θ : ℝ) := complexPlaceWeilInsertion F v.val v.property (complexWeilCircleUnit r hr θ)
  let t := Multiplicative.ofAdd (Real.log (r ^ 2))
  let g := ideleClassExpSection F t
  let j (θ : ℝ) := ideleClassNormOnePart F (A θ)
  have hnorm (θ : ℝ) : ideleClassLogNorm F (A θ) = t := by
    change Multiplicative.ofAdd (Real.log (ideleClassNorm F (A θ))) = t
    dsimp only [A, t]
    rw [complexPlaceWeilInsertion_norm]
    change Multiplicative.ofAdd (Real.log (‖circleMap 0 r θ‖ ^ 2)) = _
    rw [norm_circleMap_zero, abs_of_pos hr]
  have hj (θ : ℝ) : (j θ).val * g = A θ := by
    have h := (ideleClassSplit F).left_inv (A θ)
    change (j θ).val * ideleClassExpSection F (ideleClassLogNorm F (A θ)) = A θ at h
    rwa [hnorm θ] at h
  have hA : Continuous A := (complexPlaceWeilInsertion F v.val v.property).continuous.comp
    (complexWeilCircleUnit_continuous r hr)
  have hcont : Continuous j := (continuous_fst.comp (ideleClassSplitHomeomorph F).continuous).comp hA
  letI : IsFiniteMeasure (complexWeilCircleMeasure r) := complexWeilCircleMeasure_finite r hr hne
  have h := hasSum_idelicWeil_compactIntegral F ν (complexWeilCircleMeasure r) j hcont.measurable f g
  simp_rw [hj] at h
  have he := h.const_smul ((2 * Real.pi : ℝ)⁻¹)
  rw [complexWeilCircleMeasure_integral] at he
  refine he.congr_fun fun ω => ?_
  change (_ * idelicWeilLogProfile F ν ω f (Real.log (r ^ 2))) * _ =
    (2 * Real.pi : ℝ)⁻¹ • ((_ * idelicWeilLogProfile F ν ω f (Real.log (r ^ 2))) * _)
  rw [complexWeilCircleMeasure_integral, Complex.real_smul, Complex.real_smul]
  have hθ (θ : ℝ) : ω (j θ) = normOneEulerCharacter F ω (A θ) := rfl
  simp_rw [hθ]
  ring

/-- The weighted average over the two signs at a fixed real radius
commutes with norm-one Fourier synthesis. -/
theorem idelicWeil_realSign_hasSum (f : BruhatCompactTest (IdeleClass F))
    (v : R F) (r : ℝ) (hr : 0 < r) :
    let u : ℝˣ := Units.mk0 r hr.ne'
    let A := realPlaceWeilInsertion F v.val v.property
    HasSum (fun ω : PontryaginDual (K F) =>
      ((ν.real univ : ℂ)⁻¹ * idelicWeilLogProfile F ν ω f (Real.log r)) *
        (((|1 - r|)⁻¹ • (normOneEulerCharacter F ω (A u) : ℂ)⁻¹ +
          (|1 + r|)⁻¹ • (normOneEulerCharacter F ω (A (-u)) : ℂ)⁻¹) / 2))
      (((|1 - r|)⁻¹ • f.val.val (A u) + (|1 + r|)⁻¹ • f.val.val (A (-u))) / 2) := by
  let u : ℝˣ := Units.mk0 r hr.ne'
  let A := realPlaceWeilInsertion F v.val v.property
  have hp : ‖u.val‖ = r := Real.norm_of_nonneg hr.le
  have hn : ‖(-u).val‖ = r := by change ‖-r‖ = r; rw [norm_neg, Real.norm_of_nonneg hr.le]
  have h₁ := idelicWeil_realSample_hasSum F ν f v u
  have h₂ := idelicWeil_realSample_hasSum F ν f v (-u)
  rw [hp] at h₁
  rw [hn] at h₂
  have h := ((((h₁.const_smul (|1 - r|)⁻¹).add (h₂.const_smul (|1 + r|)⁻¹))).div_const (2 : ℂ))
  refine h.congr_fun fun ω => ?_
  simp only [Circle.coe_inv, Complex.real_smul]
  ring

section LocalCharacter

variable (χ : PontryaginDual (IdeleClass F)) (S : Finset (Place F))
  (hs : Surjective (sIdeleClassInclusion F S))
  (hu : globalNormOneCharacter F (heckeNormOneRestriction F χ) ∈
    (sUnramified F S : Set (QuasiCharacter (IdeleClass F))))

private abbrev localPhase := sLocalNormOneCharacterOfGlobal F (heckeNormOneRestriction F χ) S hs hu

/-- The weighted complex angular mean of the inverse local Hecke character
is its inverse radial phase times the Poisson factor of its frequency. -/
theorem idelicWeil_complexCircle_inverseCharacter {t : ℝ} (ht : HasHeckeHeight F χ t)
    (v : C F) (r : ℝ) (hr : 0 < r) (hne : r ≠ 1) :
    let p := sLocalComplexArchParameters F S (localPhase F χ S hs hu) v
    (2 * Real.pi)⁻¹ •
      (∫ θ in (0 : ℝ)..2 * Real.pi, complexWeilCircleKernel r θ •
        (χ (complexPlaceWeilInsertion F v.val v.property (complexWeilCircleUnit r hr θ)) : ℂ)⁻¹) =
      ((r ^ 2 : ℝ) : ℂ) ^ (-p.1 + (t : ℂ) * Complex.I) *
        (if r < 1 then ((r : ℂ) ^ p.2.natAbs) / ((1 - r ^ 2 : ℝ) : ℂ)
          else (((r⁻¹ : ℝ) : ℂ) ^ p.2.natAbs) / ((r ^ 2 - 1 : ℝ) : ℂ)) := by
  let p := sLocalComplexArchParameters F S (localPhase F χ S hs hu) v
  let b : ℂ := ((r ^ 2 : ℝ) : ℂ) ^ (-p.1 + (t : ℂ) * Complex.I)
  let G (z : ℂ) : ℂ := (‖1 - z‖ ^ 2)⁻¹ • (z / (r : ℂ)) ^ (-p.2)
  have h (θ : ℝ) :
      complexWeilCircleKernel r θ •
        (χ (complexPlaceWeilInsertion F v.val v.property (complexWeilCircleUnit r hr θ)) : ℂ)⁻¹ =
        b * G (circleMap 0 r θ) := by
    rw [complexPlaceWeilInsertion_character F χ S hs hu ht]
    change complexWeilCircleKernel r θ •
        ((((‖circleMap 0 r θ‖ ^ 2 : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I + p.1)) *
          (circleMap 0 r θ / (‖circleMap 0 r θ‖ : ℂ)) ^ p.2)⁻¹ = _
    rw [norm_circleMap_zero, abs_of_pos hr, mul_inv_rev, ← zpow_neg, ← Complex.cpow_neg]
    have hb : -(-(t : ℂ) * Complex.I + p.1) = -p.1 + (t : ℂ) * Complex.I := by ring
    rw [hb]
    simp only [G, b, complexWeilCircleKernel, Complex.real_smul]
    ring
  dsimp only
  simp_rw [h]
  rw [intervalIntegral.integral_const_mul]
  have he : (2 * Real.pi : ℝ)⁻¹ •
      (b * ∫ θ in (0 : ℝ)..2 * Real.pi, G (circleMap 0 r θ)) =
        b * Real.circleAverage G 0 r := by
    rw [Real.circleAverage_def, Complex.real_smul, Complex.real_smul]
    ring
  rw [he]
  change b * Real.circleAverage G 0 r = _
  rw [show Real.circleAverage G 0 r = _ from complexWeil_angular_zpow hr hne (-p.2),
    Int.natAbs_neg]

/-- The angular factor of a real local Hecke character is the even or odd
sign of the actual real insertion. -/
theorem idelicWeil_realSign_inverseCharacter {t : ℝ} (ht : HasHeckeHeight F χ t)
    (v : R F) (r : ℝ) (hr : 0 < r) (hne : r ≠ 1) :
    let p := sLocalRealArchParameters F S (localPhase F χ S hs hu) v
    let u : ℝˣ := Units.mk0 r hr.ne'
    ((|1 - r|)⁻¹ • (χ (realPlaceWeilInsertion F v.val v.property u) : ℂ)⁻¹ +
      (|1 + r|)⁻¹ • (χ (realPlaceWeilInsertion F v.val v.property (-u)) : ℂ)⁻¹) / 2 =
      (r : ℂ) ^ (-p.1 + (t : ℂ) * Complex.I) *
        ((if r < 1 then r ^ (p.2 % 2) / (1 - r ^ 2)
          else r * r⁻¹ ^ (p.2 % 2) / (r ^ 2 - 1) : ℝ) : ℂ) := by
  let p := sLocalRealArchParameters F S (localPhase F χ S hs hu) v
  let u : ℝˣ := Units.mk0 r hr.ne'
  let b : ℂ := (r : ℂ) ^ (-p.1 + (t : ℂ) * Complex.I)
  have hb : -(-(t : ℂ) * Complex.I + p.1) = -p.1 + (t : ℂ) * Complex.I := by ring
  have hplus : (χ (realPlaceWeilInsertion F v.val v.property u) : ℂ)⁻¹ = b := by
    rw [realPlaceWeilInsertion_character F χ S hs hu ht]
    change (((‖r‖ : ℂ) ^ (-(t : ℂ) * Complex.I + p.1)) *
      (if r < 0 then (-1 : ℂ) ^ p.2 else 1))⁻¹ = b
    rw [Real.norm_of_nonneg hr.le, ite_eq_right hr.not_gt, mul_one, ← Complex.cpow_neg, hb]
  have hminus : (χ (realPlaceWeilInsertion F v.val v.property (-u)) : ℂ)⁻¹ =
      b * (-1 : ℂ) ^ (p.2 % 2) := by
    rw [realPlaceWeilInsertion_character F χ S hs hu ht]
    change (((‖-r‖ : ℂ) ^ (-(t : ℂ) * Complex.I + p.1)) *
      (if -r < 0 then (-1 : ℂ) ^ p.2 else 1))⁻¹ = _
    rw [norm_neg, Real.norm_of_nonneg hr.le, ite_eq_left (neg_neg_of_pos hr),
      mul_inv_rev, ← inv_pow, inv_neg, inv_one, ← Complex.cpow_neg, hb,
      neg_one_pow_eq_pow_mod_two, mul_comm]
  have hweight := realWeil_sign_average hr hne (p.2 % 2) (Nat.mod_lt _ (by norm_num))
  change ((|1 - r|)⁻¹ • (χ (realPlaceWeilInsertion F v.val v.property u) : ℂ)⁻¹ +
      (|1 + r|)⁻¹ • (χ (realPlaceWeilInsertion F v.val v.property (-u)) : ℂ)⁻¹) / 2 =
      b * _
  rw [hplus, hminus, ← hweight, Complex.real_smul, Complex.real_smul]
  push_cast
  ring

end LocalCharacter

end
end Masullo
