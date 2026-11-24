import IdelicWeilGammaKernel

open Function IsDedekindDomain MeasureTheory NumberField Set
open scoped Classical NumberField

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

private abbrev K := normOneIdeleClass F
private abbrev R := {v : InfinitePlace F // v.IsReal}
private abbrev C := {v : InfinitePlace F // v.IsComplex}
private abbrev Place := HeightOneSpectrum (𝓞 F)

local instance weilArchRadialClassLC : LocallyCompactSpace (IdeleClass F) :=
  ideleClasses_locallyCompact
local instance weilArchRadialClassT2 : T2Space (IdeleClass F) := ideleClasses_hausdorff
local instance weilArchRadialNormOneMeasurable : MeasurableSpace (K F) := borel _
local instance weilArchRadialNormOneBorel : BorelSpace (K F) := ⟨rfl⟩

set_option maxHeartbeats 900000

/-- The weighted real sign average including the square root of the modulus. -/
def idelicWeilRealRadialSlice (f : BruhatCompactTest (IdeleClass F))
    (v : R F) (s : ℝ) (hs : 0 < s) : ℂ :=
  let u : ℝˣ := Units.mk0 s hs.ne'
  let A := realPlaceWeilInsertion F v.val v.property
  (s ^ (1 / 2 : ℝ) : ℝ) •
    (((|1 - s|)⁻¹ • f.val.val (A u) + (|1 + s|)⁻¹ • f.val.val (A (-u))) / 2)

/-- The weighted complex angular average including the square root of the squared modulus. -/
def idelicWeilComplexRadialSlice (f : BruhatCompactTest (IdeleClass F))
    (v : C F) (s : ℝ) (hs : 0 < s) : ℂ :=
  (s : ℂ) * ((2 * Real.pi)⁻¹ • ∫ θ in (0 : ℝ)..2 * Real.pi,
    complexWeilCircleKernel s θ •
      f.val.val (complexPlaceWeilInsertion F v.val v.property (complexWeilCircleUnit s hs θ)))

private abbrev χ₀ (ω : PontryaginDual (K F)) := heckeOrdinateCharacter F ω 0

private theorem χ₀_height (ω : PontryaginDual (K F)) : HasHeckeHeight F (χ₀ F ω) 0 := by
  simpa only [neg_zero] using heckeOrdinateCharacter_hasHeight F ω 0

variable (ν : Measure (K F)) [ν.IsHaarMeasure]
variable (E : ∀ ω : PontryaginDual (K F), CompletedHeckeChart F ω)

private theorem χ₀_unramified (ω : PontryaginDual (K F)) :
    globalNormOneCharacter F (heckeNormOneRestriction F (χ₀ F ω)) ∈
      (sUnramified F (E ω).stage : Set (QuasiCharacter (IdeleClass F))) := by
  rw [heckeNormOneRestriction_ordinateCharacter]
  exact (E ω).unramified

private abbrev chartLocalPhase (ω : PontryaginDual (K F)) :=
  sLocalNormOneCharacterOfGlobal F (heckeNormOneRestriction F (χ₀ F ω))
    (E ω).stage (E ω).surj (χ₀_unramified F E ω)

private theorem χ₀_apply (ω : PontryaginDual (K F)) (x : IdeleClass F) :
    (χ₀ F ω x : ℂ) = (normOneEulerCharacter F ω x : ℂ) := by
  exact congrArg (fun χ : PontryaginDual (IdeleClass F) => (χ x : ℂ))
    (idelicWeil_ordinate_zero_eq F ω)

private abbrev chartRealParams (ω : PontryaginDual (K F)) (v : R F) :=
  sLocalRealArchParameters F (E ω).stage (chartLocalPhase F E ω) v

private abbrev chartComplexParams (ω : PontryaginDual (K F)) (v : C F) :=
  sLocalComplexArchParameters F (E ω).stage (chartLocalPhase F E ω) v

private theorem centeredRadius_ne_one {r s : ℝ} (hr₀ : 0 < r) (hr : r < 1)
    (hsr : s ∈ ({r, r⁻¹} : Set ℝ)) : s ≠ 1 := by
  simp only [mem_insert_iff, mem_singleton_iff] at hsr
  rcases hsr with h | h
  · exact h.trans_ne hr.ne
  · exact h.trans_ne ((one_lt_inv₀ hr₀).mpr hr).ne'

/-- The real slice at either of two reciprocal radii has the centered
real radial weight with the inverse Hecke phase. -/
theorem idelicWeil_realRadial_hasSum (f : BruhatCompactTest (IdeleClass F)) (v : R F)
    {r s : ℝ} (hr₀ : 0 < r) (hr : r < 1) (hs : 0 < s) (hsr : s ∈ ({r, r⁻¹} : Set ℝ)) :
    HasSum (fun ω : PontryaginDual (K F) =>
      let p := chartRealParams F E ω v
      ((ν.real univ : ℂ)⁻¹ * idelicWeilLogProfile F ν ω f (Real.log s)) *
        ((s : ℂ) ^ (-p.1) *
          ((r ^ (1 / 2 : ℝ) * r ^ (p.2 % 2) / (1 - r ^ 2) : ℝ) : ℂ)))
      (idelicWeilRealRadialSlice F f v s hs) := by
  have hne := centeredRadius_ne_one hr₀ hr hsr
  let u : ℝˣ := Units.mk0 s hs.ne'
  let A := realPlaceWeilInsertion F v.val v.property
  let W := s ^ (1 / 2 : ℝ)
  have h := (idelicWeil_realSign_hasSum F ν f v s hs).const_smul W
  change HasSum _ (idelicWeilRealRadialSlice F f v s hs) at h
  refine h.congr_fun fun ω => ?_
  let p := chartRealParams F E ω v
  let B : ℂ := (|1 - s|)⁻¹ • (normOneEulerCharacter F ω (A u) : ℂ)⁻¹ +
    (|1 + s|)⁻¹ • (normOneEulerCharacter F ω (A (-u)) : ℂ)⁻¹
  let a := if s < 1 then s ^ (p.2 % 2) / (1 - s ^ 2)
    else s * s⁻¹ ^ (p.2 % 2) / (s ^ 2 - 1)
  have hB : B / 2 = (s : ℂ) ^ (-p.1) * (a : ℂ) := by
    have h₁ := idelicWeil_realSign_inverseCharacter F (χ₀ F ω) (E ω).stage (E ω).surj
      (χ₀_unramified F E ω) (χ₀_height F ω) v s hs hne
    simpa only [χ₀_apply F ω, Complex.ofReal_zero, zero_mul, add_zero, B, a] using h₁
  have hW : W * a = r ^ (1 / 2 : ℝ) * r ^ (p.2 % 2) / (1 - r ^ 2) := by
    dsimp only [W, a]
    rw [← realWeil_sign_average hs hne (p.2 % 2) (Nat.mod_lt _ (by norm_num))]
    exact realWeil_centeredSign_shells hr₀ hr (p.2 % 2) (Nat.mod_lt _ (by norm_num)) s hsr
  change _ * ((s : ℂ) ^ (-p.1) * ((r ^ (1 / 2 : ℝ) * r ^ (p.2 % 2) / (1 - r ^ 2) : ℝ) : ℂ)) =
    W • (_ * (B / 2))
  rw [← hW, Complex.ofReal_mul, hB, Complex.real_smul]
  ring

/-- The complex slice at either of two reciprocal radii has the centered
complex radial weight with the inverse Hecke phase. -/
theorem idelicWeil_complexRadial_hasSum (f : BruhatCompactTest (IdeleClass F)) (v : C F)
    {r s : ℝ} (hr₀ : 0 < r) (hr : r < 1) (hs : 0 < s) (hsr : s ∈ ({r, r⁻¹} : Set ℝ)) :
    HasSum (fun ω : PontryaginDual (K F) =>
      let p := chartComplexParams F E ω v
      ((ν.real univ : ℂ)⁻¹ * idelicWeilLogProfile F ν ω f (Real.log (s ^ 2))) *
        ((((s ^ 2 : ℝ) : ℂ) ^ (-p.1)) *
          (((r : ℂ) ^ (p.2.natAbs + 1)) / ((1 - r ^ 2 : ℝ) : ℂ))))
      (idelicWeilComplexRadialSlice F f v s hs) := by
  have hne := centeredRadius_ne_one hr₀ hr hsr
  let A (θ : ℝ) := complexPlaceWeilInsertion F v.val v.property (complexWeilCircleUnit s hs θ)
  have h := (idelicWeil_complexCircle_hasSum F ν f v s hs hne).mul_left (s : ℂ)
  change HasSum _ (idelicWeilComplexRadialSlice F f v s hs) at h
  refine h.congr_fun fun ω => ?_
  let p := chartComplexParams F E ω v
  let B : ℂ := (2 * Real.pi)⁻¹ • ∫ θ in (0 : ℝ)..2 * Real.pi,
    complexWeilCircleKernel s θ • (normOneEulerCharacter F ω (A θ) : ℂ)⁻¹
  let a : ℂ := if s < 1 then ((s : ℂ) ^ p.2.natAbs) / ((1 - s ^ 2 : ℝ) : ℂ)
    else (((s⁻¹ : ℝ) : ℂ) ^ p.2.natAbs) / ((s ^ 2 - 1 : ℝ) : ℂ)
  have hB : B = ((s ^ 2 : ℝ) : ℂ) ^ (-p.1) * a := by
    have h₁ := idelicWeil_complexCircle_inverseCharacter F (χ₀ F ω) (E ω).stage (E ω).surj
      (χ₀_unramified F E ω) (χ₀_height F ω) v s hs hne
    simpa only [χ₀_apply F ω, Complex.ofReal_zero, zero_mul, add_zero, B, a] using h₁
  have hW : (s : ℂ) * a = ((r : ℂ) ^ (p.2.natAbs + 1)) / ((1 - r ^ 2 : ℝ) : ℂ) := by
    rw [show a = _ from (complexWeil_angular_zpow hs hne p.2).symm]
    exact complexWeil_centeredAngular_shells hr₀ hr p.2 s hsr
  simp only [Circle.coe_inv]
  change _ * ((((s ^ 2 : ℝ) : ℂ) ^ (-p.1)) *
    (((r : ℂ) ^ (p.2.natAbs + 1)) / ((1 - r ^ 2 : ℝ) : ℂ))) = (s : ℂ) * (_ * B)
  rw [← hW, hB]
  ring

private theorem exp_cpow_log (x : ℝ) (z : ℂ) :
    (Real.exp x : ℂ) ^ z = Complex.exp (z * (x : ℂ)) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero x)),
    ← Complex.ofReal_log (Real.exp_pos x).le, Real.log_exp, mul_comm]

private theorem centered_exp_weight (p : ℂ) (a x y t : ℝ) :
    (Real.exp x : ℂ) ^ (-p) * ((Real.exp (-a * y) : ℂ) / ((1 - Real.exp (-t) : ℝ) : ℂ)) =
      Complex.exp (-p * (x : ℂ) - (a : ℂ) * (y : ℂ)) / (1 - Complex.exp (-(t : ℂ))) := by
  rw [exp_cpow_log, ← mul_div_assoc, Complex.ofReal_sub, Complex.ofReal_one,
    Complex.ofReal_exp, Complex.ofReal_exp, ← Complex.exp_add]
  push_cast
  rw [show -p * (x : ℂ) + -(a : ℂ) * (y : ℂ) = -p * (x : ℂ) - (a : ℂ) * (y : ℂ) by ring]

private abbrev centeredGammaSample (b : ℂ) (k t : ℝ) :=
  Complex.exp (-(b + 1 / 2) * ((k * t : ℝ) : ℂ)) / (1 - Complex.exp (-(t : ℂ)))

/-- At a fixed positive log radius, combining two Fourier expansions
and subtracting their common contact yields the compensated gamma kernel. -/
private theorem hasSum_compensatedGamma
    (f : BruhatCompactTest (IdeleClass F)) (k t : ℝ) (b b' : PontryaginDual (K F) → ℂ)
    (outer inner : ℂ)
    (ho : HasSum (fun ω : PontryaginDual (K F) =>
      ((ν.real univ : ℂ)⁻¹ * idelicWeilLogProfile F ν ω f (k * t)) * centeredGammaSample (b ω) k t) outer)
    (hi : HasSum (fun ω : PontryaginDual (K F) =>
      ((ν.real univ : ℂ)⁻¹ * idelicWeilLogProfile F ν ω f (-(k * t))) * centeredGammaSample (b' ω) k t) inner) :
    HasSum (fun ω : PontryaginDual (K F) => -(ν.real univ : ℂ)⁻¹ *
      localGammaExplicitKernel k (b ω) (b' ω)
        (mellinWeight (idelicWeilLogProfile F ν ω f ∘ Real.log) (-(1 / 2))) t)
      ((k : ℂ) * (outer + inner -
        (2 * Complex.exp (-(t : ℂ)) / (1 - Complex.exp (-(t : ℂ)))) * f.val.val 1)) := by
  have h₀ := hasSum_idelicWeilLogProfile F ν f 0
  rw [show ideleClassExpSection F (Multiplicative.ofAdd (0 : ℝ)) = 1 from map_one _] at h₀
  have h := ((ho.add hi).sub
    (h₀.mul_left (2 * Complex.exp (-(t : ℂ)) / (1 - Complex.exp (-(t : ℂ)))))).mul_left (k : ℂ)
  refine h.congr_fun fun ω => ?_
  rw [localGammaExplicitKernel_centered_log]
  unfold centeredGammaSample
  ring

section Reflected

variable (T : PontryaginDual (K F) → Finset (Place F))
  (hT : ∀ ω, Surjective (sIdeleClassInclusion F (T ω)))
  (huT : ∀ ω, globalNormOneCharacter F (heckeNormOneRestriction F (χ₀ F ω)⁻¹) ∈
    (sUnramified F (T ω) : Set (QuasiCharacter (IdeleClass F))))

private abbrev bR (v : R F) (ω : PontryaginDual (K F)) :=
  manuscriptHeckeRealGammaShift F (χ₀ F ω) (E ω).stage (E ω).surj (χ₀_unramified F E ω) 0 v

private abbrev bR' (v : R F) (ω : PontryaginDual (K F)) :=
  manuscriptHeckeRealGammaShift F (χ₀ F ω)⁻¹ (T ω) (hT ω) (huT ω) 0 v

private abbrev bC (v : C F) (ω : PontryaginDual (K F)) :=
  manuscriptHeckeComplexGammaShift F (χ₀ F ω) (E ω).stage (E ω).surj (χ₀_unramified F E ω) 0 v

private abbrev bC' (v : C F) (ω : PontryaginDual (K F)) :=
  manuscriptHeckeComplexGammaShift F (χ₀ F ω)⁻¹ (T ω) (hT ω) (huT ω) 0 v

/-- The real radial integrand with its common subtraction is the norm-one
sum of the corresponding signed, compensated gamma kernels at every positive radius. -/
theorem idelicWeil_realGammaKernel_hasSum (f : BruhatCompactTest (IdeleClass F))
    (v : R F) {t : ℝ} (ht : 0 < t) :
    HasSum (fun ω : PontryaginDual (K F) => -(ν.real univ : ℂ)⁻¹ *
      localGammaExplicitKernel (1 / 2) (bR F E v ω) (bR' F T hT huT v ω)
        (mellinWeight (idelicWeilLogProfile F ν ω f ∘ Real.log) (-(1 / 2))) t)
      ((1 / 2 : ℂ) *
        (idelicWeilRealRadialSlice F f v (Real.exp (t / 2)) (Real.exp_pos _) +
          idelicWeilRealRadialSlice F f v (Real.exp (-t / 2)) (Real.exp_pos _) -
          (2 * Complex.exp (-(t : ℂ)) / (1 - Complex.exp (-(t : ℂ)))) * f.val.val 1)) := by
  let r := Real.exp (-t / 2)
  have hr₀ : 0 < r := Real.exp_pos _
  have hr : r < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hoRad : Real.exp (t / 2) = r⁻¹ := by
    rw [← Real.exp_neg]
    congr 1
    ring
  have hm : Real.exp (t / 2) ∈ ({r, r⁻¹} : Set ℝ) := by simp [hoRad]
  have hi : r ∈ ({r, r⁻¹} : Set ℝ) := mem_insert ..
  have ho := idelicWeil_realRadial_hasSum F ν E f v hr₀ hr (Real.exp_pos (t / 2)) hm
  have hn := idelicWeil_realRadial_hasSum F ν E f v hr₀ hr hr₀ hi
  have he : (1 / 2 : ℝ) * t = t / 2 := by ring
  have he' : -((1 / 2 : ℝ) * t) = -t / 2 := by ring
  have hcast : (1 / 2 : ℂ) = (((1 / 2 : ℝ)) : ℂ) := by norm_num
  rw [hcast]
  apply hasSum_compensatedGamma
  · refine ho.congr_fun fun ω => ?_
    let p := chartRealParams F E ω v
    have hb : bR F E v ω = p.1 + ((p.2 % 2 : ℕ) : ℂ) := by
      change p.1 + ((p.2 % 2 : ℕ) : ℂ) - ((0 : ℝ) : ℂ) * Complex.I = _
      simp
    change (_ * idelicWeilLogProfile F ν ω f ((1 / 2 : ℝ) * t)) * centeredGammaSample _ _ _ =
      (_ * idelicWeilLogProfile F ν ω f (Real.log (Real.exp (t / 2)))) *
        ((Real.exp (t / 2) : ℂ) ^ (-p.1) *
          ((r ^ (1 / 2 : ℝ) * r ^ (p.2 % 2) / (1 - r ^ 2) : ℝ) : ℂ))
    rw [Real.log_exp, he]
    rw [show r ^ (1 / 2 : ℝ) * r ^ (p.2 % 2) / (1 - r ^ 2) = _ from realWeil_radialWeight_log t (p.2 % 2),
      Complex.ofReal_div, centered_exp_weight, show centeredGammaSample (bR F E v ω) (1 / 2) t =
        Complex.exp (-(bR F E v ω + 1 / 2) * (((1 / 2 : ℝ) * t : ℝ) : ℂ)) /
          (1 - Complex.exp (-(t : ℂ))) from rfl, hb, he]
    congr 3
    push_cast
    ring
  · refine hn.congr_fun fun ω => ?_
    let p := chartRealParams F E ω v
    have hb : bR' F T hT huT v ω = -p.1 + ((p.2 % 2 : ℕ) : ℂ) := by
      have h := idelicWeil_realGammaShift_inv F (χ₀ F ω) (E ω).stage (T ω)
        (E ω).surj (hT ω) (χ₀_unramified F E ω) (huT ω) 0 v
      simpa only [neg_zero, Complex.ofReal_zero, zero_mul, add_zero] using h
    change (_ * idelicWeilLogProfile F ν ω f (-((1 / 2 : ℝ) * t))) * centeredGammaSample _ _ _ =
      (_ * idelicWeilLogProfile F ν ω f (Real.log r)) *
        ((r : ℂ) ^ (-p.1) * ((r ^ (1 / 2 : ℝ) * r ^ (p.2 % 2) / (1 - r ^ 2) : ℝ) : ℂ))
    rw [show Real.log r = -t / 2 from Real.log_exp _, he']
    rw [show r ^ (1 / 2 : ℝ) * r ^ (p.2 % 2) / (1 - r ^ 2) = _ from realWeil_radialWeight_log t (p.2 % 2),
      Complex.ofReal_div]
    change _ = _ * ((Real.exp (-t / 2) : ℂ) ^ (-p.1) * _)
    rw [centered_exp_weight, show centeredGammaSample (bR' F T hT huT v ω) (1 / 2) t =
      Complex.exp (-(bR' F T hT huT v ω + 1 / 2) * (((1 / 2 : ℝ) * t : ℝ) : ℂ)) /
        (1 - Complex.exp (-(t : ℂ))) from rfl, hb, he]
    congr 3
    push_cast
    ring

/-- The complex radial integrand with its common subtraction is the norm-one
sum of the corresponding signed, compensated gamma kernels at every positive radius. -/
theorem idelicWeil_complexGammaKernel_hasSum (f : BruhatCompactTest (IdeleClass F))
    (v : C F) {t : ℝ} (ht : 0 < t) :
    HasSum (fun ω : PontryaginDual (K F) => -(ν.real univ : ℂ)⁻¹ *
      localGammaExplicitKernel 1 (bC F E v ω) (bC' F T hT huT v ω)
        (mellinWeight (idelicWeilLogProfile F ν ω f ∘ Real.log) (-(1 / 2))) t)
      (idelicWeilComplexRadialSlice F f v (Real.exp (t / 2)) (Real.exp_pos _) +
        idelicWeilComplexRadialSlice F f v (Real.exp (-t / 2)) (Real.exp_pos _) -
        (2 * Complex.exp (-(t : ℂ)) / (1 - Complex.exp (-(t : ℂ)))) * f.val.val 1) := by
  let r := Real.exp (-t / 2)
  have hr₀ : 0 < r := Real.exp_pos _
  have hr : r < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hoRad : Real.exp (t / 2) = r⁻¹ := by
    rw [← Real.exp_neg]
    congr 1
    ring
  have hm : Real.exp (t / 2) ∈ ({r, r⁻¹} : Set ℝ) := by simp [hoRad]
  have hi : r ∈ ({r, r⁻¹} : Set ℝ) := mem_insert ..
  have ho := idelicWeil_complexRadial_hasSum F ν E f v hr₀ hr (Real.exp_pos (t / 2)) hm
  have hn := idelicWeil_complexRadial_hasSum F ν E f v hr₀ hr hr₀ hi
  have hsq (x : ℝ) : Real.exp (x / 2) ^ 2 = Real.exp x := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have houter : (Real.exp (t / 2)) ^ 2 = Real.exp t := hsq t
  have hinner : r ^ 2 = Real.exp (-t) := hsq (-t)
  have hc (ω : PontryaginDual (K F)) :
      ((r : ℂ) ^ ((chartComplexParams F E ω v).2.natAbs + 1)) / ((1 - r ^ 2 : ℝ) : ℂ) =
        (Real.exp (-((((chartComplexParams F E ω v).2.natAbs : ℝ) + 1) / 2) * t) : ℂ) /
          ((1 - Real.exp (-t) : ℝ) : ℂ) := by
    exact complexWeil_radialWeight_log t (chartComplexParams F E ω v).2
  suffices h : HasSum (fun ω : PontryaginDual (K F) => -(ν.real univ : ℂ)⁻¹ *
      localGammaExplicitKernel 1 (bC F E v ω) (bC' F T hT huT v ω)
        (mellinWeight (idelicWeilLogProfile F ν ω f ∘ Real.log) (-(1 / 2))) t)
      (((1 : ℝ) : ℂ) *
        (idelicWeilComplexRadialSlice F f v (Real.exp (t / 2)) (Real.exp_pos _) +
          idelicWeilComplexRadialSlice F f v (Real.exp (-t / 2)) (Real.exp_pos _) -
          (2 * Complex.exp (-(t : ℂ)) / (1 - Complex.exp (-(t : ℂ)))) * f.val.val 1)) by
    simpa only [Complex.ofReal_one, one_mul] using h
  apply hasSum_compensatedGamma
  · refine ho.congr_fun fun ω => ?_
    let p := chartComplexParams F E ω v
    have hb : bC F E v ω = p.1 + (p.2.natAbs : ℂ) / 2 := by
      change p.1 + (p.2.natAbs : ℂ) / 2 - ((0 : ℝ) : ℂ) * Complex.I = _
      simp
    change (_ * idelicWeilLogProfile F ν ω f (1 * t)) * centeredGammaSample _ _ _ =
      (_ * idelicWeilLogProfile F ν ω f (Real.log ((Real.exp (t / 2)) ^ 2))) *
        (((((Real.exp (t / 2)) ^ 2 : ℝ) : ℂ) ^ (-p.1)) *
          (((r : ℂ) ^ (p.2.natAbs + 1)) / ((1 - r ^ 2 : ℝ) : ℂ)))
    rw [hc, houter, Real.log_exp, centered_exp_weight p.1 (((p.2.natAbs : ℝ) + 1) / 2) t t t]
    unfold centeredGammaSample
    rw [one_mul, hb]
    congr 3
    push_cast
    ring
  · refine hn.congr_fun fun ω => ?_
    let p := chartComplexParams F E ω v
    have hb : bC' F T hT huT v ω = -p.1 + (p.2.natAbs : ℂ) / 2 := by
      have h := idelicWeil_complexGammaShift_inv F (χ₀ F ω) (E ω).stage (T ω)
        (E ω).surj (hT ω) (χ₀_unramified F E ω) (huT ω) 0 v
      simpa only [neg_zero, Complex.ofReal_zero, zero_mul, add_zero] using h
    change (_ * idelicWeilLogProfile F ν ω f (-(1 * t))) * centeredGammaSample _ _ _ =
      (_ * idelicWeilLogProfile F ν ω f (Real.log (r ^ 2))) *
        (((((r ^ 2 : ℝ)) : ℂ) ^ (-p.1)) * (((r : ℂ) ^ (p.2.natAbs + 1)) / ((1 - r ^ 2 : ℝ) : ℂ)))
    rw [hc, hinner, Real.log_exp, centered_exp_weight p.1 (((p.2.natAbs : ℝ) + 1) / 2) (-t) t t]
    unfold centeredGammaSample
    rw [one_mul, hb]
    congr 3
    push_cast
    ring

end Reflected

end
end Masullo
