import IdelicWeilCompactFourier
import IdelicWeilFinite
import HeckeExplicitFormula

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical NumberField

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]
private abbrev K := normOneIdeleClass F
private abbrev Place := HeightOneSpectrum (𝓞 F)
private abbrev U (v : Place F) := principalIntegralUnits F v

local instance weilPrimeNormOneMeasurable : MeasurableSpace (K F) := borel _
local instance weilPrimeNormOneBorel : BorelSpace (K F) := ⟨rfl⟩
local instance weilPrimeClassLocallyCompact : LocallyCompactSpace (IdeleClass F) := ideleClasses_locallyCompact
local instance weilPrimeClassT2 : T2Space (IdeleClass F) := ideleClasses_hausdorff
local instance weilPrimeUnitsCompact (v : Place F) : CompactSpace (U F v) := principalIntegralUnits_compactSpace F v
local instance weilPrimeUnitsMeasurable (v : Place F) : MeasurableSpace (U F v) := borel _
local instance weilPrimeUnitsBorel (v : Place F) : BorelSpace (U F v) := ⟨rfl⟩

private theorem localInsertion_norm (v : Place F) (a : (v.adicCompletion F)ˣ) :
    ideleClassNorm F (finitePlaceInsertion F v a) = ‖a.val‖ := by
  rw [finitePlaceInsertion_apply, ideleClassNorm_mk, singleFiniteIdele_norm]

/-- The finite integral unit group mapped into the norm-one idele classes. -/
def idelicWeilLocalUnitInclusion (v : Place F) : U F v →ₜ* K F :=
  let a : U F v →* IdeleClass F := (finitePlaceInsertion F v).toMonoidHom.comp (U F v).subtype
  ⟨a.codRestrict (K F) (fun u => (localInsertion_norm F v u.val).trans u.property),
    ((finitePlaceInsertion F v).continuous.comp continuous_subtype_val).subtype_mk _⟩

private theorem normOnePart_on_kernel (k : K F) :
    ideleClassNormOnePart F k.val = k := by
  apply Subtype.ext
  change k.val / ideleClassExpSection F (ideleClassLogNorm F k.val) = k.val
  have hn : ideleClassLogNorm F k.val = 1 := by
    change Multiplicative.ofAdd (Real.log (ideleClassNorm F k.val)) = 1
    rw [show ideleClassNorm F k.val = 1 from k.property, Real.log_one]
    rfl
  rw [hn, map_one, div_one]

theorem normOneEulerCharacter_localUnit (ω : PontryaginDual (K F)) (v : Place F) (u : U F v) :
    normOneEulerCharacter F ω (finitePlaceInsertion F v u.val) = ω (idelicWeilLocalUnitInclusion F v u) := by
  change ω (ideleClassNormOnePart F (idelicWeilLocalUnitInclusion F v u).val) = ω (idelicWeilLocalUnitInclusion F v u)
  exact congrArg ω (normOnePart_on_kernel F (idelicWeilLocalUnitInclusion F v u))

private theorem integral_localUnit_character_inv (ω : PontryaginDual (K F)) (v : Place F) :
    ∫ u : U F v, (((ω (idelicWeilLocalUnitInclusion F v u))⁻¹ : Circle) : ℂ) ∂principalUnitHaar F v =
      if unramifiedFiniteCharacter F (normOneEulerCharacter F ω) v then 1 else 0 := by
  let θ : PontryaginDual (U F v) := ω.comp (idelicWeilLocalUnitInclusion F v)
  have hθ : θ = 1 ↔ unramifiedFiniteCharacter F (normOneEulerCharacter F ω) v := by
    constructor
    · intro h a ha
      have he := congrArg (fun s : PontryaginDual (U F v) => s ⟨a, ha⟩) h
      rw [← finitePlaceInsertion_apply, normOneEulerCharacter_localUnit F ω v ⟨a, ha⟩]
      exact he
    · intro h
      apply PontryaginDual.ext
      intro u
      have he := h u.val u.property
      rw [← finitePlaceInsertion_apply, normOneEulerCharacter_localUnit] at he
      exact he
  have hm : (principalUnitHaar F v).real univ = 1 := by
    rw [measureReal_def, principalUnitHaar_univ, ENNReal.toReal_one]
  have h := integral_character_pair (principalUnitHaar F v) θ 1
  simp only [hθ, hm, Complex.ofReal_one] at h
  refine (integral_congr_ae (Eventually.of_forall fun u => ?_)).trans h
  change (((ω (idelicWeilLocalUnitInclusion F v u))⁻¹ : Circle) : ℂ) =
    star (ω (idelicWeilLocalUnitInclusion F v u) : ℂ) * (1 : ℂ)
  rw [mul_one, Circle.coe_inv_eq_conj, ← Complex.star_def]

variable (ν : Measure (K F)) [ν.IsHaarMeasure]

set_option maxHeartbeats 850000 in
/-- Fourier reconstruction on an actual finite local shell. Unit averaging
keeps the unramified characters and gives their inverse phase at the shell representative. -/
theorem idelicWeil_localUnitAverage_hasSum (f : BruhatCompactTest (IdeleClass F))
    (v : Place F) (a : (v.adicCompletion F)ˣ) :
    let A := finitePlaceInsertion F v a
    let t := (ideleClassLogNorm F A).toAdd
    HasSum (fun ω : PontryaginDual (K F) =>
      ((ν.real univ : ℂ)⁻¹ * idelicWeilLogProfile F ν ω f t) *
        (if unramifiedFiniteCharacter F (normOneEulerCharacter F ω) v then
          (((normOneEulerCharacter F ω A)⁻¹ : Circle) : ℂ) else 0))
      (∫ u : U F v, f.val.val (finitePlaceInsertion F v (u.val * a)) ∂principalUnitHaar F v) := by
  let A := finitePlaceInsertion F v a
  let t := (ideleClassLogNorm F A).toAdd
  let g := ideleClassExpSection F (Multiplicative.ofAdd t)
  let k := ideleClassNormOnePart F A
  let j (u : U F v) := idelicWeilLocalUnitInclusion F v u * k
  letI : IsProbabilityMeasure (principalUnitHaar F v) := ⟨principalUnitHaar_univ F v⟩
  have hj : Continuous j := (idelicWeilLocalUnitInclusion F v).continuous.mul_const k
  have hk : k.val * g = A := (ideleClassSplit F).left_inv A
  have h := hasSum_idelicWeil_compactAverage F ν (principalUnitHaar F v) j hj.measurable f g
  have he : (∫ u : U F v, f.val.val ((j u).val * g) ∂principalUnitHaar F v) =
      ∫ u : U F v, f.val.val (finitePlaceInsertion F v (u.val * a)) ∂principalUnitHaar F v := by
    apply integral_congr_ae
    exact Eventually.of_forall fun u => by
      change f.val.val ((finitePlaceInsertion F v u.val * k.val) * g) =
        f.val.val (finitePlaceInsertion F v (u.val * a))
      exact congrArg f.val.val ((mul_assoc _ _ _).trans
        ((congrArg (finitePlaceInsertion F v u.val * ·) hk).trans
          (map_mul (finitePlaceInsertion F v) u.val a).symm))
  rw [he] at h
  refine h.congr_fun fun ω => ?_
  let θ := normOneEulerCharacter F ω
  have hi : (∫ u : U F v, (((ω (j u))⁻¹ : Circle) : ℂ) ∂principalUnitHaar F v) =
      (((θ A)⁻¹ : Circle) : ℂ) *
        (∫ u : U F v, (((ω (idelicWeilLocalUnitInclusion F v u))⁻¹ : Circle) : ℂ) ∂principalUnitHaar F v) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall fun u => by
      change (((ω (idelicWeilLocalUnitInclusion F v u * k))⁻¹ : Circle) : ℂ) =
        (((ω k)⁻¹ : Circle) : ℂ) * (((ω (idelicWeilLocalUnitInclusion F v u))⁻¹ : Circle) : ℂ)
      rw [map_mul, mul_inv_rev, Circle.coe_mul]
  change ((ν.real univ : ℂ)⁻¹ * idelicWeilLogProfile F ν ω f t) * _ =
    ((ν.real univ : ℂ)⁻¹ * idelicWeilLogProfile F ν ω f t) *
      (∫ u : U F v, (((ω (j u))⁻¹ : Circle) : ℂ) ∂principalUnitHaar F v)
  rw [hi, integral_localUnit_character_inv F]
  change _ * (if unramifiedFiniteCharacter F θ v then (((θ A)⁻¹ : Circle) : ℂ) else 0) =
    _ * ((((θ A)⁻¹ : Circle) : ℂ) * (if unramifiedFiniteCharacter F θ v then 1 else 0))
  by_cases hu : unramifiedFiniteCharacter F θ v <;>
    simp only [hu, ite_true, ite_false, mul_one, mul_zero]

private theorem unramified_inv_iff (χ : PontryaginDual (IdeleClass F)) (v : Place F) :
    unramifiedFiniteCharacter F χ⁻¹ v ↔ unramifiedFiniteCharacter F χ v := by
  constructor
  · intro h u hu
    have he := h u hu
    change (χ (ideleClassMap F (singleFiniteIdele F v u)))⁻¹ = 1 at he
    exact inv_eq_one.mp he
  · intro h u hu
    change (χ (ideleClassMap F (singleFiniteIdele F v u)))⁻¹ = 1
    rw [h u hu, inv_one]

theorem idelicWeil_ordinate_zero_eq (ω : PontryaginDual (K F)) :
    heckeOrdinateCharacter F ω 0 = normOneEulerCharacter F ω := by
  apply PontryaginDual.ext
  intro g
  change normOneEulerCharacter F ω g * Circle.exp (0 * (ideleClassLogNorm F g).toAdd) =
    normOneEulerCharacter F ω g
  rw [zero_mul, Circle.exp_zero, mul_one]

private theorem log_uniformizer_shell (v : Place F) (n : ℤ) :
    (ideleClassLogNorm F (finitePlaceInsertion F v (chosenFiniteUniformizer F v ^ n))).toAdd =
      -(n : ℝ) * Real.log (v.asIdeal.absNorm : ℝ) := by
  change Real.log (ideleClassNorm F (finitePlaceInsertion F v (chosenFiniteUniformizer F v ^ n))) = _
  rw [localInsertion_norm F, Units.val_zpow_eq_zpow_val, norm_zpow,
    norm_finiteUniformizer F v _ (chosenFiniteUniformizer_spec F v), Real.log_zpow, Real.log_inv]
  ring

/-- The normalized positive or negative shell mean in the finite local units. -/
def idelicWeilUnitShellAverage (f : BruhatCompactTest (IdeleClass F))
    (v : Place F) (n : ℤ) : ℂ :=
  ∫ u : U F v, f.val.val (finitePlaceInsertion F v
    (u.val * chosenFiniteUniformizer F v ^ n)) ∂principalUnitHaar F v

set_option maxHeartbeats 850000 in
private theorem hasSum_local_positive_shell (f : BruhatCompactTest (IdeleClass F))
    (v : Place F) (m : ℕ) (hm : m ≠ 0) :
    HasSum (fun ω : PontryaginDual (K F) =>
      ((ν.real univ : ℂ)⁻¹ * idelicWeilLogProfile F ν ω f (-(m : ℝ) * Real.log (v.asIdeal.absNorm : ℝ))) *
        heckeEulerCoefficient F (normOneEulerCharacter F ω)⁻¹ (chosenFiniteUniformizer F) v ^ m)
      (idelicWeilUnitShellAverage F f v (m : ℤ)) := by
  let π := chosenFiniteUniformizer F v
  let A := finitePlaceInsertion F v (π ^ (m : ℤ))
  have ht : (ideleClassLogNorm F A).toAdd = -(m : ℝ) * Real.log (v.asIdeal.absNorm : ℝ) := by
    simpa only [Int.cast_natCast] using log_uniformizer_shell F v (m : ℤ)
  have h := idelicWeil_localUnitAverage_hasSum F ν f v (π ^ (m : ℤ))
  change HasSum (fun ω : PontryaginDual (K F) =>
    ((ν.real univ : ℂ)⁻¹ * idelicWeilLogProfile F ν ω f (ideleClassLogNorm F A).toAdd) *
      (if unramifiedFiniteCharacter F (normOneEulerCharacter F ω) v then
        (((normOneEulerCharacter F ω A)⁻¹ : Circle) : ℂ) else 0)) _ at h
  rw [ht] at h
  refine h.congr_fun fun ω => ?_
  let χ := normOneEulerCharacter F ω
  have hphase : (((χ A)⁻¹ : Circle) : ℂ) =
      (χ⁻¹ (ideleClassMap F (singleFiniteIdele F v π)) : ℂ) ^ m := by
    change (((χ (finitePlaceInsertion F v (π ^ (m : ℤ))))⁻¹ : Circle) : ℂ) =
      (((χ (ideleClassMap F (singleFiniteIdele F v π)))⁻¹ : Circle) : ℂ) ^ m
    rw [zpow_natCast, map_pow (finitePlaceInsertion F v), map_pow χ, ← inv_pow,
      Circle.coe_pow, finitePlaceInsertion_apply]
  change _ * heckeEulerCoefficient F χ⁻¹ (chosenFiniteUniformizer F) v ^ m =
    _ * (if unramifiedFiniteCharacter F χ v then (((χ A)⁻¹ : Circle) : ℂ) else 0)
  rw [heckeEulerCoefficient, unramified_inv_iff F χ v]
  by_cases hc : unramifiedFiniteCharacter F χ v
  · rw [ite_eq_left hc, ite_eq_left hc, hphase]
  · rw [ite_eq_right hc, ite_eq_right hc, zero_pow hm]

set_option maxHeartbeats 850000 in
private theorem hasSum_local_negative_shell (f : BruhatCompactTest (IdeleClass F))
    (v : Place F) (m : ℕ) (hm : m ≠ 0) :
    HasSum (fun ω : PontryaginDual (K F) =>
      ((ν.real univ : ℂ)⁻¹ * idelicWeilLogProfile F ν ω f ((m : ℝ) * Real.log (v.asIdeal.absNorm : ℝ))) *
        heckeEulerCoefficient F (normOneEulerCharacter F ω) (chosenFiniteUniformizer F) v ^ m)
      (idelicWeilUnitShellAverage F f v (-(m : ℤ))) := by
  let π := chosenFiniteUniformizer F v
  let A := finitePlaceInsertion F v (π ^ (-(m : ℤ)))
  have ht : (ideleClassLogNorm F A).toAdd = (m : ℝ) * Real.log (v.asIdeal.absNorm : ℝ) := by
    simpa only [Int.cast_natCast, Int.cast_neg, neg_neg] using log_uniformizer_shell F v (-(m : ℤ))
  have h := idelicWeil_localUnitAverage_hasSum F ν f v (π ^ (-(m : ℤ)))
  change HasSum (fun ω : PontryaginDual (K F) =>
    ((ν.real univ : ℂ)⁻¹ * idelicWeilLogProfile F ν ω f (ideleClassLogNorm F A).toAdd) *
      (if unramifiedFiniteCharacter F (normOneEulerCharacter F ω) v then
        (((normOneEulerCharacter F ω A)⁻¹ : Circle) : ℂ) else 0)) _ at h
  rw [ht] at h
  refine h.congr_fun fun ω => ?_
  let χ := normOneEulerCharacter F ω
  have hphase : (((χ A)⁻¹ : Circle) : ℂ) =
      (χ (ideleClassMap F (singleFiniteIdele F v π)) : ℂ) ^ m := by
    change (((χ (finitePlaceInsertion F v (π ^ (-(m : ℤ)))))⁻¹ : Circle) : ℂ) = _
    rw [zpow_neg, zpow_natCast, map_inv (finitePlaceInsertion F v), map_inv χ, inv_inv,
      map_pow (finitePlaceInsertion F v), map_pow χ, Circle.coe_pow, finitePlaceInsertion_apply]
  change _ * heckeEulerCoefficient F χ (chosenFiniteUniformizer F) v ^ m =
    _ * (if unramifiedFiniteCharacter F χ v then (((χ A)⁻¹ : Circle) : ℂ) else 0)
  rw [heckeEulerCoefficient]
  by_cases hc : unramifiedFiniteCharacter F χ v
  · rw [ite_eq_left hc, ite_eq_left hc, hphase]
  · rw [ite_eq_right hc, ite_eq_right hc, zero_pow hm]

set_option maxHeartbeats 950000 in
/-- For each prime power, the normalized characterwise prime term sums to
the two actual local shell means with the centered explicit-formula weight. -/
theorem idelicWeil_primeSample_hasSum (f : BruhatCompactTest (IdeleClass F))
    (v : Place F) (n : ℕ) :
    HasSum (fun ω : PontryaginDual (K F) => (ν.real univ : ℂ)⁻¹ *
      heckeCenteredPrimeTerm F (heckeOrdinateCharacter F ω 0) (idelicWeilCenteredTest F ν ω f) (v, n))
      (Complex.exp (-((n + 1 : ℕ) : ℂ) * (Real.log (v.asIdeal.absNorm : ℝ) : ℂ) / 2) *
        (Real.log (v.asIdeal.absNorm : ℝ) : ℂ) *
        (idelicWeilUnitShellAverage F f v (-((n + 1 : ℕ) : ℤ)) +
          idelicWeilUnitShellAverage F f v ((n + 1 : ℕ) : ℤ))) := by
  let m := n + 1
  let x := (m : ℝ) * Real.log (v.asIdeal.absNorm : ℝ)
  let p : ℂ := Real.log (v.asIdeal.absNorm : ℝ)
  have hm : m ≠ 0 := Nat.succ_ne_zero n
  have h := ((hasSum_local_negative_shell F ν f v m hm).add
    (hasSum_local_positive_shell F ν f v m hm)).mul_left (Complex.exp (-(x : ℂ) / 2) * p)
  have hx : (x : ℂ) = (m : ℂ) * p := by
    dsimp only [x, p]
    push_cast
    rfl
  have hq : Real.log ((heckePrimePowerIdeal F (v, n)).absNorm : ℝ) = x := by
    rw [heckePrimePowerIdeal, map_pow, Nat.cast_pow, Real.log_pow]
  have ha : -(m : ℝ) * Real.log (v.asIdeal.absNorm : ℝ) = -x := by
    dsimp only [x]
    rw [neg_mul]
  have hc : Complex.exp (-(x : ℂ) / 2) = Complex.exp (-(m : ℂ) * p / 2) := by
    rw [hx, neg_mul]
  change HasSum _ (Complex.exp (-(m : ℂ) * p / 2) * p *
    (idelicWeilUnitShellAverage F f v (-(m : ℤ)) + idelicWeilUnitShellAverage F f v (m : ℤ)))
  rw [← hc]
  refine h.congr_fun fun ω => ?_
  rw [idelicWeil_ordinate_zero_eq, heckeCenteredPrimeTerm, hq, ha]
  change _ * (Complex.exp (-(x : ℂ) / 2) *
    (heckeEulerCoefficient F (normOneEulerCharacter F ω) (chosenFiniteUniformizer F) v ^ m *
        p * idelicWeilLogProfile F ν ω f x +
      heckeEulerCoefficient F (normOneEulerCharacter F ω)⁻¹ (chosenFiniteUniformizer F) v ^ m *
        p * idelicWeilLogProfile F ν ω f (-x))) = _
  ring

end
end Masullo
