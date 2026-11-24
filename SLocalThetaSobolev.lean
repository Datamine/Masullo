import SLocalThetaKernels
import SLocalMellinCompact
import HardySobolevTranslations
import WeightedL2Coordinates
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.MeasureTheory.Function.L2Space

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical ENNReal NNReal NumberField

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]
variable (S : Finset (HeightOneSpectrum (𝓞 F)))

private abbrev G := (SAdeles F S)ˣ
private abbrev Q := SIdeleQuotient F S
private abbrev E := sLocalBruhatImage F S
private abbrev K := SLocalThetaNormOne F S

private def logNorm : Q F S →* Multiplicative ℝ :=
  (show ℝ≥0ˣ →* Multiplicative ℝ from
    { toFun := fun u => Multiplicative.ofAdd (Real.log (u.val : ℝ))
      map_one' := by simp
      map_mul' := fun u v => by
        change Multiplicative.ofAdd (Real.log ((u.val : ℝ) * (v.val : ℝ))) =
          Multiplicative.ofAdd (Real.log (u.val : ℝ) + Real.log (v.val : ℝ))
        rw [Real.log_mul (NNReal.coe_ne_zero.mpr u.ne_zero) (NNReal.coe_ne_zero.mpr v.ne_zero)] }).comp
    (sQuotientNorm F S)

private abbrev logModulus (q : Q F S) : ℝ := (logNorm F S q).toAdd

private theorem logModulus_continuous : Continuous (logModulus F S) :=
  ((NNReal.continuous_coe.comp Units.continuous_val).comp
    (sQuotientNorm_proper F S).continuous).log
      (fun q => (sLocalClassModulus_pos F S q).ne')

/-- Logarithmic modulus on the S-local class group. -/
abbrev sLocalThetaSobolevLogNorm := logNorm F S

theorem continuous_sLocalThetaSobolevLogNorm : Continuous (sLocalThetaSobolevLogNorm F S) :=
  logModulus_continuous F S

theorem sLocalThetaSobolevLogNorm_normOne (k : K F S) :
    sLocalThetaSobolevLogNorm F S k.val = 1 := by
  have hk : sQuotientNorm F S k.val = 1 := k.property
  unfold sLocalThetaSobolevLogNorm logNorm
  rw [MonoidHom.comp_apply, hk, map_one]

local instance sLocalThetaSobolev_idelesMeasurable : MeasurableSpace (G F S) := borel _
local instance sLocalThetaSobolev_idelesBorel : BorelSpace (G F S) := ⟨rfl⟩
local instance sLocalThetaSobolev_idelesLCompact : LocallyCompactSpace (G F S) :=
  sLocalIdeles_locallyCompact F S
local instance sLocalThetaSobolev_idelesSecondCountable : SecondCountableTopology (G F S) :=
  sLocalIdeles_secondCountable F S
local instance sLocalThetaSobolev_idelesT2 : T2Space (G F S) := by
  letI := (sIdeleBlock_locallyCompact_hausdorff F S).2
  exact ((sBlockUnitProduct F S).symm.toHomeomorph.isEmbedding.comp
    (isEmbedding_prodMkLeft (X := G F S) (1 : (SIntegralTail F S)ˣ))).t2Space

private abbrev ideleWeight (l r s : ℝ) (g : G F S) : ℝ :=
  hardySobolevWeight l r s (logModulus F S (QuotientGroup.mk g))

/-- The measure with the Hardy–Sobolev density on the S-ideles. -/
def sLocalHardySobolevMeasure (μ : Measure (G F S)) (l r s : ℝ) : Measure (G F S) :=
  μ.withDensity (fun g => ENNReal.ofReal (ideleWeight F S l r s g))

/-- The continuous density gives a regular Radon measure by local finiteness. -/
theorem sLocalHardySobolevMeasure_regular (μ : Measure (G F S)) [μ.IsHaarMeasure]
    (l r s : ℝ) :
    (sLocalHardySobolevMeasure F S μ l r s).Regular ∧
      IsFiniteMeasureOnCompacts (sLocalHardySobolevMeasure F S μ l r s) := by
  have h : Continuous (ideleWeight F S l r s) :=
    (continuous_hardySobolevWeight l r s).comp
      ((logModulus_continuous F S).comp QuotientGroup.continuous_mk)
  letI : IsLocallyFiniteMeasure (sLocalHardySobolevMeasure F S μ l r s) :=
    IsLocallyFiniteMeasure.withDensity_ofReal h
  exact ⟨inferInstance, inferInstance⟩

/-- S-units preserve the density and the underlying Haar measure. -/
theorem sLocalHardySobolevMeasure_invariant (μ : Measure (G F S)) [μ.IsHaarMeasure]
    (l r s : ℝ) (u : sUnitImage F S) :
    MeasurePreserving (fun g : G F S => u.val * g)
      (sLocalHardySobolevMeasure F S μ l r s)
      (sLocalHardySobolevMeasure F S μ l r s) := by
  let f : G F S → ℝ≥0∞ := fun g => ENNReal.ofReal (ideleWeight F S l r s g)
  have hf : Measurable f :=
    ((continuous_hardySobolevWeight l r s).comp
      ((logModulus_continuous F S).comp QuotientGroup.continuous_mk)).measurable.ennreal_ofReal
  have hmul : Measurable (fun g : G F S => u.val * g) :=
    (continuous_const.mul continuous_id).measurable
  have hinv (g : G F S) : f (u.val * g) = f g := by
    change ENNReal.ofReal (ideleWeight F S l r s (u.val * g)) =
      ENNReal.ofReal (ideleWeight F S l r s g)
    let π := QuotientGroup.mk' (sUnitImage F S)
    have hu : π u.val = 1 := (QuotientGroup.eq_one_iff _).mpr u.property
    have he : π (u.val * g) = π g := by
      rw [map_mul, hu]
      exact one_mul (π g)
    exact congrArg (fun q : Q F S => ENNReal.ofReal
      (hardySobolevWeight l r s (logModulus F S q))) he
  refine ⟨hmul, ?_⟩
  ext B hB
  change (Measure.map _ (μ.withDensity f)) B = (μ.withDensity f) B
  rw [Measure.map_apply hmul hB, withDensity_apply _ (hmul hB), withDensity_apply _ hB,
    ← lintegral_congr (fun g => hinv g) (μ := μ.restrict ((fun g : G F S => u.val * g) ⁻¹' B)),
    ← setLIntegral_map hB hf hmul, map_mul_left_eq_self]

/-- The vanishing-at-infinity assertion in the proof of Lemma 10.1.1.4(1)
fails on a positive interval. The positive logarithmic ray escapes every
compact set, and the Sobolev density stays at least one on that ray. -/
theorem sLocalHardySobolevDensity_not_vanishing (l r s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s) :
    ¬ Tendsto (ideleWeight F S l r s) (cocompact (G F S)) (𝓝 0) := by
  intro h
  obtain ⟨C, hC, hsmall⟩ := Filter.mem_cocompact.mp (h.eventually (Iio_mem_nhds zero_lt_one))
  have hc : Continuous (fun g : G F S => logModulus F S (QuotientGroup.mk g)) :=
    (logModulus_continuous F S).comp QuotientGroup.continuous_mk
  obtain ⟨M, hM⟩ := hC.bddAbove_image hc.continuousOn
  let t := max M 0 + 1
  let g := sLocalExpSection F S (Multiplicative.ofAdd t)
  have hlog : logModulus F S (QuotientGroup.mk g) = t := by
    change Real.log (sLocalIdeleNorm F S g) = t
    rw [show sLocalIdeleNorm F S g = Real.exp t from sLocalIdeleNorm_expSection F S t, Real.log_exp]
  have ht : 0 ≤ t := by dsimp [t]; linarith [le_max_right M (0 : ℝ)]
  have hgt : M < t := by dsimp [t]; linarith [le_max_left M (0 : ℝ)]
  have hg : g ∉ C := fun hg => hgt.not_ge (hlog ▸ hM ⟨g, hg, rfl⟩)
  have hw : 1 ≤ ideleWeight F S l r s g := by
    change 1 ≤ hardySobolevWeight l r s (logModulus F S (QuotientGroup.mk g))
    rw [hlog, hardySobolevWeight]
    apply one_le_mul_of_one_le_of_one_le
    · exact (Real.one_le_exp_iff.mpr (by positivity)).trans (le_max_right _ _)
    · exact Real.one_le_rpow (le_add_of_nonneg_right (sq_nonneg t)) (by positivity)
  exact hw.not_gt (hsmall hg)

private theorem sobolevPolynomial_bound (s c : ℝ) (hs : 0 ≤ s) (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, (1 + x ^ 2) ^ (s / 2) ≤ C * Real.exp (c * |x|) := by
  let d := min 1 (c / (s + 1))
  have hd : 0 < d := lt_min one_pos (div_pos hc (by positivity))
  have hd₁ : d ≤ 1 := min_le_left _ _
  have hdc : d * s ≤ c := by
    have h := (le_div_iff₀ (show 0 < s + 1 by positivity)).mp (min_le_right 1 (c / (s + 1)))
    change d * (s + 1) ≤ c at h
    linarith
  refine ⟨(d ^ 2)⁻¹ ^ (s / 2), Real.rpow_pos_of_pos (by positivity) _, fun x => ?_⟩
  have hdt : 0 ≤ d * |x| := by positivity
  have hh : d ^ 2 * (1 + x ^ 2) ≤ Real.exp (2 * (d * |x|)) := by
    calc
      _ ≤ (1 + d * |x|) ^ 2 := by
        have hd₂ := pow_le_pow_left₀ hd.le hd₁ 2
        rw [add_sq, mul_pow, sq_abs]
        nlinarith
      _ ≤ _ := by
        rw [mul_comm (2 : ℝ), Real.exp_mul, Real.rpow_two]
        exact pow_le_pow_left₀ (by positivity) (by simpa [add_comm] using Real.add_one_le_exp (d * |x|)) _
  have hbase : 1 + x ^ 2 ≤ (d ^ 2)⁻¹ * Real.exp (2 * (d * |x|)) :=
    (le_inv_mul_iff₀ (by positivity : 0 < d ^ 2)).mpr hh
  calc
    _ ≤ ((d ^ 2)⁻¹ * Real.exp (2 * (d * |x|))) ^ (s / 2) :=
      Real.rpow_le_rpow (by positivity) hbase (by positivity)
    _ = (d ^ 2)⁻¹ ^ (s / 2) * Real.exp (d * s * |x|) := by
      rw [Real.mul_rpow (by positivity) (Real.exp_nonneg _), ← Real.exp_mul]
      congr 2
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hdc (abs_nonneg _))) (by positivity)

local instance sLocalThetaSobolev_classMeasurable : MeasurableSpace (Q F S) := borel _
local instance sLocalThetaSobolev_classBorel : BorelSpace (Q F S) := ⟨rfl⟩
local instance sLocalThetaSobolev_classLC : LocallyCompactSpace (Q F S) :=
  (QuotientGroup.isOpenQuotientMap_mk (N := sUnitImage F S)).locallyCompactSpace
local instance sLocalThetaSobolev_classSecondCountable : SecondCountableTopology (Q F S) :=
  (QuotientGroup.isOpenQuotientMap_mk (N := sUnitImage F S)).isQuotientMap.secondCountableTopology
    QuotientGroup.isOpenQuotientMap_mk.isOpenMap
local instance sLocalThetaSobolev_classT1 : T1Space (Q F S) :=
  QuotientGroup.t1Space_iff.mpr (sUnitImage_closed F S)

variable (ν : Measure (K F S)) [ν.IsHaarMeasure]

private theorem logModulus_exp_integrable (c : ℝ) (hc : 0 < c) :
    Integrable (fun q => Real.exp (-c * |logModulus F S q|)) (sLocalClassHaar F S ν) := by
  letI := sLocalThetaNormOne_compact F S
  letI : IsFiniteMeasure ν := ⟨isCompact_univ.measure_lt_top⟩
  let e := sLocalZetaSplit F S
  apply (e.toMeasurableEquiv.measurableEmbedding.integrable_map_iff).mpr
  have he (p : ℝ × K F S) : logModulus F S (e p) = p.1 :=
    sLocalZetaSplit_logModulus F S p
  change Integrable (fun p => Real.exp (-c * |logModulus F S (e p)|)) (volume.prod ν)
  simpa only [he] using (integrable_exp_abs_envelope c hc).comp_fst (ν := ν)

private theorem weightedTheta_bound (a l r s : ℝ) (ha : 0 < a + l) (hlr : l ≤ r) (hs : 0 ≤ s) :
    ∃ p : Seminorm ℂ (E F S), Continuous p ∧
      ∃ w : Q F S → ℝ, Integrable w (sLocalClassHaar F S ν) ∧ (∀ q, 0 ≤ w q) ∧
      ∀ (f : E F S) (q : Q F S),
        ‖sLocalThetaOperator F S f q‖ ^ 2 *
          hardySobolevWeight (a + l) (a + r) s (logModulus F S q) ≤ p f ^ 2 * w q := by
  let k := Fintype.card (SLogIndex F S) - 1
  let c := min ((a + l) / 2) 1
  have hc : 0 < c := lt_min (half_pos ha) one_pos
  obtain ⟨N, hN⟩ := exists_nat_gt (a + r + 1)
  obtain ⟨p, hp, hlog⟩ := sLocalTheta_log_seminorm F S
  obtain ⟨t, ht, hlarge⟩ := sLocalTheta_largeNorm_seminorm F S N
  obtain ⟨D, hD, hsmall⟩ := logPower_mul_rpow_bounded k ((a + l) / 2) (half_pos ha)
  obtain ⟨C, hC, hpoly⟩ := sobolevPolynomial_bound s c hs hc
  let B : ℝ≥0 := ⟨2 ^ (k - 1) * (1 + D), by positivity⟩
  let P := B • p + t
  let w (q : Q F S) : ℝ := C * Real.exp (-c * |logModulus F S q|)
  refine ⟨P, (continuous_const.mul hp).add ht, w,
    (logModulus_exp_integrable F S ν c hc).const_mul C, fun q => by dsimp [w]; positivity,
    fun f q => ?_⟩
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  let x := logModulus F S (QuotientGroup.mk g)
  let V := ‖sLocalThetaOperator F S f (QuotientGroup.mk g)‖
  let y := if 0 ≤ x then a + r else a + l
  have hy₁ : a + l ≤ y := by dsimp [y]; split <;> linarith
  have hy₂ : y ≤ a + r := by dsimp [y]; split <;> linarith
  have he : Real.exp (y * x) * V ≤ P f * Real.exp (-c * |x|) := by
    have h := sLocalTheta_orbit_exp_bound F S
      (fun g => ‖sLocalThetaOnIdeles F S (sLocalBruhatRestriction F S f.val) g‖)
      (p f) (t f) D (a + l) (a + r) N ha hN (apply_nonneg _ _) (apply_nonneg _ _) hD.le
      hsmall (hlog f) (hlarge f) g (y : ℂ) (by simpa using hy₁) (by simpa using hy₂)
    have hP : P f = p f * 2 ^ (k - 1) * (1 + D) + t f := by
      change (2 ^ (k - 1) * (1 + D)) * p f + t f = _
      ring
    rw [hP]
    change Real.exp (y * Real.log (sLocalIdeleNorm F S g)) *
      ‖sLocalThetaOnIdeles F S (sLocalBruhatRestriction F S f.val) g‖ ≤
      _ * Real.exp (-c * |Real.log (sLocalIdeleNorm F S g)|)
    simpa only [Complex.ofReal_re] using h
  have hweight : hardySobolevWeight (a + l) (a + r) s x =
      (Real.exp (y * x)) ^ 2 * (1 + x ^ 2) ^ (s / 2) := by
    rw [← Real.exp_nat_mul]
    unfold hardySobolevWeight
    congr 1
    by_cases hx : 0 ≤ x
    · rw [max_eq_right (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by linarith) hx)),
        show y = a + r from ite_eq_left hx]
      congr 1
      push_cast
      ring
    · rw [max_eq_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_right (by linarith) (le_of_not_ge hx))),
        show y = a + l from ite_eq_right hx]
      congr 1
      push_cast
      ring
  change V ^ 2 * hardySobolevWeight (a + l) (a + r) s x ≤ P f ^ 2 * w _
  rw [hweight, ← mul_assoc, ← mul_pow, mul_comm V]
  calc
    _ ≤ (P f * Real.exp (-c * |x|)) ^ 2 * (C * Real.exp (c * |x|)) :=
      mul_le_mul (pow_le_pow_left₀ (by dsimp [V]; positivity) he _) (hpoly x)
        (by positivity) (by positivity)
    _ = _ := by
      change _ = P f ^ 2 * (C * Real.exp (-c * |x|))
      rw [mul_pow, ← Real.exp_nat_mul]
      calc
        _ = P f ^ 2 * (C * (Real.exp ((2 : ℕ) * (-c * |x|)) *
            Real.exp (c * |x|))) := by ring
        _ = _ := by rw [← Real.exp_add]; congr 3; push_cast; ring

private abbrev thetaKer := (sLocalThetaOperator F S).ker
private abbrev Theta := SLocalThetaQuotient F S

/-- Evaluation on the actual S-local theta quotient. -/
def sLocalThetaFunction : Theta F S →ₗ[ℂ] (Q F S → ℂ) :=
  (thetaKer F S).liftQ (sLocalThetaOperator F S) le_rfl

private theorem thetaFunction_continuous (u : Theta F S) :
    Continuous (sLocalThetaFunction F S u) := by
  obtain ⟨f, rfl⟩ := (thetaKer F S).mkQ_surjective u
  exact sLocalTheta_continuous F S f.val

private theorem amplitude_pos (l r s x : ℝ) : 0 < hardySobolevAmplitude l r s x := by
  apply Real.sqrt_pos.mpr
  unfold hardySobolevWeight
  exact mul_pos ((Real.exp_pos _).trans_le (le_max_left _ _))
    (Real.rpow_pos_of_pos (by positivity) _)

/-- The measure defining the ambient weighted Hilbert space on the S-idele quotient. -/
def sLocalClassHardySobolevMeasure (l r s : ℝ) : Measure (Q F S) :=
  (sLocalClassHaar F S ν).withDensity
    (fun q => ENNReal.ofReal (hardySobolevWeight l r s (logModulus F S q)))

/-- The amplitude coordinates are isometric to the space for the actual weighted measure. -/
def sLocalClassHardySobolevIso (l r s : ℝ) :
    Lp ℂ 2 (sLocalClassHardySobolevMeasure F S ν l r s) ≃ₗᵢ[ℂ]
      Lp ℂ 2 (sLocalClassHaar F S ν) := by
  let A (q : Q F S) := hardySobolevAmplitude l r s (logModulus F S q)
  have hA : Measurable A := ((Real.continuous_sqrt.comp (continuous_hardySobolevWeight l r s)).comp
    (logModulus_continuous F S)).measurable
  have hpos (q : Q F S) : 0 < A q := amplitude_pos l r s _
  have he : amplitudeMeasure (sLocalClassHaar F S ν) A =
      sLocalClassHardySobolevMeasure F S ν l r s := by
    unfold amplitudeMeasure sLocalClassHardySobolevMeasure
    congr 1
    funext q
    exact congrArg ENNReal.ofReal (Real.sq_sqrt (hardySobolevWeight_nonneg ..))
  rw [← he]
  exact amplitudeL2Iso (sLocalClassHaar F S ν) A hA hpos

private def profile (a l r s : ℝ) (u : Theta F S) (q : Q F S) : ℂ :=
  (hardySobolevAmplitude l r s (logModulus F S q) * Real.exp (a * logModulus F S q)) •
    sLocalThetaFunction F S u q

private theorem profile_continuous (a l r s : ℝ) (u : Theta F S) :
    Continuous (profile F S a l r s u) :=
  (((Real.continuous_sqrt.comp (continuous_hardySobolevWeight l r s)).mul
    (Real.continuous_exp.comp (continuous_const.mul continuous_id))).comp
      (logModulus_continuous F S)).smul (thetaFunction_continuous F S u)

private theorem profile_norm_sq (a l r s : ℝ) (u : Theta F S) (q : Q F S) :
    ‖profile F S a l r s u q‖ ^ 2 =
      ‖sLocalThetaFunction F S u q‖ ^ 2 *
        hardySobolevWeight (a + l) (a + r) s (logModulus F S q) := by
  let x := logModulus F S q
  have hw : hardySobolevWeight l r s x * Real.exp (2 * (a * x)) =
      hardySobolevWeight (a + l) (a + r) s x := by
    unfold hardySobolevWeight
    rw [mul_right_comm, max_mul_of_nonneg _ _ (Real.exp_pos _).le,
      ← Real.exp_add, ← Real.exp_add]
    have hleft : 2 * l * x + 2 * (a * x) = 2 * (a + l) * x := by ring
    have hright : 2 * r * x + 2 * (a * x) = 2 * (a + r) * x := by ring
    rw [hleft, hright]
  unfold profile
  rw [norm_smul, Real.norm_of_nonneg (mul_pos (amplitude_pos l r s x) (Real.exp_pos _)).le,
    mul_pow, mul_pow, hardySobolevAmplitude, Real.sq_sqrt (hardySobolevWeight_nonneg ..),
    ← Real.exp_nat_mul]
  change (hardySobolevWeight l r s x * Real.exp (2 * (a * x))) * _ = _
  rw [hw, mul_comm]

private theorem profile_memLp (a l r s : ℝ) (ha : 0 < a + l) (hlr : l ≤ r) (hs : 0 ≤ s)
    (u : Theta F S) : MemLp (profile F S a l r s u) 2 (sLocalClassHaar F S ν) := by
  have hcont := profile_continuous F S a l r s u
  obtain ⟨f, rfl⟩ := (thetaKer F S).mkQ_surjective u
  obtain ⟨p, _, w, hw, _, hbound⟩ := weightedTheta_bound F S ν a l r s ha hlr hs
  apply (memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable).mpr
  apply (hw.const_mul (p f ^ 2)).mono' (hcont.norm.pow 2).aestronglyMeasurable
  filter_upwards with q
  change ‖‖profile F S a l r s ((thetaKer F S).mkQ f) q‖ ^ 2‖ ≤ _
  rw [Real.norm_of_nonneg (sq_nonneg _), profile_norm_sq]
  exact hbound f q

/-- The S-local theta quotient embeds in the weighted Hilbert space,
using multiplication by the positive Sobolev amplitude to represent it in L². -/
def sLocalThetaSobolevMap (a l r s : ℝ) (ha : 0 < a + l) (hlr : l ≤ r) (hs : 0 ≤ s) :
    Theta F S →L[ℂ] Lp ℂ 2 (sLocalClassHaar F S ν) := by
  let h := profile_memLp F S ν a l r s ha hlr hs
  let L : Theta F S →ₗ[ℂ] Lp ℂ 2 (sLocalClassHaar F S ν) :=
    { toFun := fun u => (h u).toLp _
      map_add' u v := by
        rw [← MemLp.toLp_add (h u) (h v)]
        apply MemLp.toLp_congr
        refine Eventually.of_forall fun q => ?_
        change profile F S a l r s (u + v) q =
          profile F S a l r s u q + profile F S a l r s v q
        simp [profile, smul_add]
      map_smul' c u := by
        change (h (c • u)).toLp _ = c • (h u).toLp _
        rw [← MemLp.toLp_const_smul c (h u)]
        apply MemLp.toLp_congr
        refine Eventually.of_forall fun q => ?_
        change profile F S a l r s (c • u) q = c • profile F S a l r s u q
        simp [profile]
        ring }
  refine ⟨L, (thetaKer F S).isOpenQuotientMap_mkQL.continuous_comp_iff.mp ?_⟩
  obtain ⟨p, hp, w, hw, hn, hbound⟩ := weightedTheta_bound F S ν a l r s ha hlr hs
  let R := L.comp (thetaKer F S).mkQL.toLinearMap
  let C : ℝ≥0 := ⟨Real.sqrt (∫ q, w q ∂sLocalClassHaar F S ν), Real.sqrt_nonneg _⟩
  have hnorm (f : E F S) : ‖R f‖ ≤ (C • p) f := by
    change ‖(h ((thetaKer F S).mkQ f)).toLp _‖ ≤ (C : ℝ) * p f
    have he : ‖(h ((thetaKer F S).mkQ f)).toLp _‖ ^ 2 ≤
        (p f ^ 2) * ∫ q, w q ∂sLocalClassHaar F S ν := by
      rw [norm_sq_toLp_two, ← integral_const_mul]
      refine integral_mono ((memLp_two_iff_integrable_sq_norm
        (profile_continuous F S a l r s _).aestronglyMeasurable).mp (h _))
        (hw.const_mul _) (fun q => ?_)
      rw [profile_norm_sq]
      exact hbound f q
    have hC : (C : ℝ) ^ 2 = ∫ q, w q ∂sLocalClassHaar F S ν :=
      Real.sq_sqrt (integral_nonneg hn)
    apply le_of_pow_le_pow_left₀ (n := 2) (by positivity : 2 ≠ 0)
      (mul_nonneg C.coe_nonneg (apply_nonneg p _))
    rw [mul_pow, hC, mul_comm]
    exact he
  have hcont : Continuous ((normSeminorm ℂ (Lp ℂ 2 (sLocalClassHaar F S ν))).comp R) :=
    Seminorm.continuous_of_le (q := C • p) (continuous_const.mul hp) hnorm
  apply continuous_of_continuousAt_zero R
  rw [ContinuousAt, map_zero, tendsto_zero_iff_norm_tendsto_zero]
  exact hcont.tendsto' _ _ (map_zero _)

theorem sLocalThetaSobolevMap_ae (a l r s : ℝ) (ha : 0 < a + l) (hlr : l ≤ r) (hs : 0 ≤ s)
    (u : Theta F S) :
    sLocalThetaSobolevMap F S ν a l r s ha hlr hs u =ᵐ[sLocalClassHaar F S ν]
      profile F S a l r s u :=
  (profile_memLp F S ν a l r s ha hlr hs u).coeFn_toLp

/-- The norm in the completion restricts to (10.1.1.7). -/
theorem sLocalThetaSobolevMap_norm_sq (a l r s : ℝ) (ha : 0 < a + l) (hlr : l ≤ r) (hs : 0 ≤ s)
    (u : Theta F S) : ‖sLocalThetaSobolevMap F S ν a l r s ha hlr hs u‖ ^ 2 =
      ∫ q, ‖sLocalThetaFunction F S u q‖ ^ 2 *
        hardySobolevWeight (a + l) (a + r) s (logModulus F S q) ∂sLocalClassHaar F S ν := by
  change ‖(profile_memLp F S ν a l r s ha hlr hs u).toLp _‖ ^ 2 = _
  rw [norm_sq_toLp_two]
  exact integral_congr_ae (Eventually.of_forall (profile_norm_sq F S a l r s u))

local instance sLocalThetaSobolev_classHaar : (sLocalClassHaar F S ν).IsHaarMeasure :=
  sLocalClassHaar_isHaar F S ν

theorem sLocalThetaSobolevMap_injective (a l r s : ℝ) (ha : 0 < a + l) (hlr : l ≤ r) (hs : 0 ≤ s) :
    Injective (sLocalThetaSobolevMap F S ν a l r s ha hlr hs) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro u hu
  change sLocalThetaSobolevMap F S ν a l r s ha hlr hs u = 0 at hu
  have h := sLocalThetaSobolevMap_ae F S ν a l r s ha hlr hs u
  rw [hu] at h
  have hzero := ((profile_continuous F S a l r s u).ae_eq_iff_eq
    (μ := sLocalClassHaar F S ν) continuous_const).mp (h.symm.trans (Lp.coeFn_zero ℂ 2 _))
  obtain ⟨f, rfl⟩ := (thetaKer F S).mkQ_surjective u
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  apply LinearMap.mem_ker.mpr
  funext q
  have he := congrFun hzero q
  change (hardySobolevAmplitude l r s (logModulus F S q) * Real.exp (a * logModulus F S q)) •
    sLocalThetaOperator F S f q = 0 at he
  exact (smul_eq_zero.mp he).resolve_left ((mul_pos (amplitude_pos ..) (Real.exp_pos _)).ne')

private theorem thetaOperator_translate (g : G F S) (f : E F S) (q : Q F S) :
    sLocalThetaOperator F S (sLocalBruhatLeftTranslate F S g f) q =
      sLocalThetaOperator F S f ((QuotientGroup.mk g : Q F S)⁻¹ * q) := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  let π := QuotientGroup.mk' (sUnitImage F S)
  change sLocalThetaOperator F S (sLocalBruhatLeftTranslate F S g f) (π x) =
    sLocalThetaOperator F S f ((π g)⁻¹ * π x)
  rw [← map_inv, ← map_mul]
  change sLocalThetaOnIdeles F S
    (sLocalBruhatRestriction F S (sLocalBruhatLeftTranslate F S g f).val) x =
    sLocalThetaOnIdeles F S (sLocalBruhatRestriction F S f.val) (g⁻¹ * x)
  unfold sLocalThetaOnIdeles
  apply tsum_congr
  intro u
  rw [sLocalBruhatLeftTranslate_restrict, Units.val_mul]
  exact congrArg (sLocalBruhatRestriction F S f.val)
    (mul_left_comm g.inv ((sIntegerDiagonal F S) u.toMul) x.val)

/-- S-idelic translation on the theta quotient, induced by translation on the tests. -/
def sLocalSobolevThetaTranslateIdeles (g : G F S) : Theta F S →L[ℂ] Theta F S :=
  (thetaKer F S).liftQL ((thetaKer F S).mkQL.comp (sLocalBruhatLeftTranslate F S g)) (by
    intro f hf
    apply LinearMap.mem_ker.mpr
    change (thetaKer F S).mkQ (sLocalBruhatLeftTranslate F S g f) = 0
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    apply LinearMap.mem_ker.mpr
    funext q
    rw [thetaOperator_translate]
    exact congrFun (LinearMap.mem_ker.mp hf) _)

theorem sLocalThetaFunction_translate (g : G F S) (u : Theta F S) (q : Q F S) :
    sLocalThetaFunction F S (sLocalSobolevThetaTranslateIdeles F S g u) q =
      sLocalThetaFunction F S u ((QuotientGroup.mk g : Q F S)⁻¹ * q) := by
  obtain ⟨f, rfl⟩ := (thetaKer F S).mkQ_surjective u
  exact thetaOperator_translate F S g f q

private abbrev L2 := Lp ℂ 2 (sLocalClassHaar F S ν)

/-- Left translation in amplitude coordinates on the ambient weighted S-local Hilbert space. -/
def sLocalHardySobolevTranslation (l r s : ℝ) (hs : 0 ≤ s) :
    Q F S → L2 F S ν →L[ℂ] L2 F S ν :=
  hardySobolevMulTranslation (sLocalClassHaar F S ν) (logNorm F S)
    (logModulus_continuous F S) l r s hs

/-- The multiplier in the restricted action is exactly the inverse norm twist. -/
theorem sLocalThetaSobolevMap_translate (a l r s : ℝ) (ha : 0 < a + l) (hlr : l ≤ r) (hs : 0 ≤ s)
    (g : G F S) (u : Theta F S) :
    sLocalHardySobolevTranslation F S ν l r s hs (QuotientGroup.mk g) (sLocalThetaSobolevMap F S ν a l r s ha hlr hs u) =
      (Real.exp (-a * logModulus F S (QuotientGroup.mk g)) : ℂ) •
        sLocalThetaSobolevMap F S ν a l r s ha hlr hs (sLocalSobolevThetaTranslateIdeles F S g u) := by
  let j : Q F S := QuotientGroup.mk g
  let J := sLocalThetaSobolevMap F S ν a l r s ha hlr hs
  let c : ℂ := (Real.exp (-a * logModulus F S j) : ℝ)
  let v := sLocalSobolevThetaTranslateIdeles F S g u
  let μ := sLocalClassHaar F S ν
  apply Lp.ext
  filter_upwards [hardySobolevMulTranslation_ae μ (logNorm F S)
      (logModulus_continuous F S) l r s hs j (J u),
    (measurePreserving_mul_left μ j⁻¹).quasiMeasurePreserving.ae
      (sLocalThetaSobolevMap_ae F S ν a l r s ha hlr hs u),
    Lp.coeFn_smul c (J v), sLocalThetaSobolevMap_ae F S ν a l r s ha hlr hs v]
    with q h₁ h₂ h₃ h₄
  change (hardySobolevMulTranslation μ (logNorm F S) (logModulus_continuous F S)
    l r s hs j (J u)) q = (c • J v : L2 F S ν) q
  rw [h₁, h₂, h₃, Pi.smul_apply, h₄]
  simp only [profile, smul_eq_mul, Complex.real_smul, Complex.ofReal_mul]
  change _ = c * (_ * _ * sLocalThetaFunction F S (sLocalSobolevThetaTranslateIdeles F S g u) q)
  rw [sLocalThetaFunction_translate]
  let x := logModulus F S q
  let y := logModulus F S j
  have he : logModulus F S (j⁻¹ * q) = x - y := by
    change ((logNorm F S) (j⁻¹ * q)).toAdd = x - y
    rw [map_mul, map_inv]
    change -y + x = x - y
    abel
  have hE : Real.exp (a * logModulus F S (j⁻¹ * q)) =
      Real.exp (-a * y) * Real.exp (a * x) := by rw [he, ← Real.exp_add]; congr 1; ring
  let Aq := hardySobolevAmplitude l r s x
  let Agq := hardySobolevAmplitude l r s (logModulus F S (j⁻¹ * q))
  let Ex := Real.exp (a * x)
  let Ey := Real.exp (-a * y)
  let z := sLocalThetaFunction F S u (j⁻¹ * q)
  change ((Aq / Agq : ℝ) : ℂ) * ((Agq : ℂ) *
    (Real.exp (a * logModulus F S (j⁻¹ * q)) : ℂ) * z) =
    (Ey : ℂ) * ((Aq : ℂ) * (Ex : ℂ) * z)
  rw [hE]
  change ((Aq / Agq : ℝ) : ℂ) * ((Agq : ℂ) * ((Ey * Ex : ℝ) : ℂ) * z) = _
  have hA : (Agq : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (amplitude_pos ..).ne'
  rw [Complex.ofReal_div, Complex.ofReal_mul]
  field_simp [hA]

/-- The Hilbert closure of the norm-twisted S-local theta functions. -/
def sLocalThetaSobolevCompletion (a l r s : ℝ) (ha : 0 < a + l) (hlr : l ≤ r) (hs : 0 ≤ s) :
    Submodule ℂ (L2 F S ν) :=
  (sLocalThetaSobolevMap F S ν a l r s ha hlr hs).range.topologicalClosure

section Completion

variable (a l r s : ℝ) (ha : 0 < a + l) (hlr : l ≤ r) (hs : 0 ≤ s)

private abbrev CompletionSpace := sLocalThetaSobolevCompletion F S ν a l r s ha hlr hs

theorem sLocalThetaSobolevCompletion_dense :
    DenseRange ((sLocalThetaSobolevMap F S ν a l r s ha hlr hs).codRestrict
      (CompletionSpace F S ν a l r s ha hlr hs) (fun u => subset_closure ⟨u, rfl⟩)) := by
  rw [DenseRange, Subtype.dense_iff, ← range_comp]
  exact subset_rfl

theorem sLocalThetaSobolevCompletion_isClosed :
    IsClosed (CompletionSpace F S ν a l r s ha hlr hs : Set (L2 F S ν)) :=
  Submodule.isClosed_topologicalClosure _

theorem sLocalThetaSobolevCompletion_complete :
    CompleteSpace (CompletionSpace F S ν a l r s ha hlr hs) :=
  (sLocalThetaSobolevCompletion_isClosed F S ν a l r s ha hlr hs).completeSpace_coe

theorem sLocalThetaSobolevCompletion_separable :
    TopologicalSpace.SeparableSpace (CompletionSpace F S ν a l r s ha hlr hs) := by
  letI : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  letI : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  letI : SecondCountableTopology (L2 F S ν) := inferInstance
  infer_instance

theorem sLocalThetaSobolevCompletion_mapsTo (j : Q F S) :
    MapsTo (sLocalHardySobolevTranslation F S ν l r s hs j) (CompletionSpace F S ν a l r s ha hlr hs)
      (CompletionSpace F S ν a l r s ha hlr hs) := by
  let J := sLocalThetaSobolevMap F S ν a l r s ha hlr hs
  let T := sLocalHardySobolevTranslation F S ν l r s hs j
  have hm : MapsTo T (range J) (range J) := by
    rintro _ ⟨u, rfl⟩
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective j
    refine ⟨(Real.exp (-a * logModulus F S (QuotientGroup.mk g)) : ℂ) •
      sLocalSobolevThetaTranslateIdeles F S g u, ?_⟩
    rw [map_smul]
    exact (sLocalThetaSobolevMap_translate F S ν a l r s ha hlr hs g u).symm
  exact hm.closure T.continuous

/-- The S-idelic class action on the closed theta space. -/
def sLocalThetaSobolevCompletion_translate (j : Q F S) :
    CompletionSpace F S ν a l r s ha hlr hs →L[ℂ] CompletionSpace F S ν a l r s ha hlr hs :=
  ((sLocalHardySobolevTranslation F S ν l r s hs j).comp
    (CompletionSpace F S ν a l r s ha hlr hs).subtypeL).codRestrict _
      (fun u => sLocalThetaSobolevCompletion_mapsTo F S ν a l r s ha hlr hs j u.property)

/-- The continuous action of the S-idele quotient restricts to the Hilbert closure. -/
theorem continuous_sLocalThetaSobolevCompletion_translate :
    Continuous (fun p : Q F S × CompletionSpace F S ν a l r s ha hlr hs =>
      sLocalThetaSobolevCompletion_translate F S ν a l r s ha hlr hs p.1 p.2) := by
  letI : (sLocalClassHaar F S ν).Regular :=
    Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _
  have hp : Continuous (fun p : Q F S × CompletionSpace F S ν a l r s ha hlr hs =>
      (p.1, (p.2.val : L2 F S ν))) :=
    continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  have ht := continuous_hardySobolevMulTranslation (G := Q F S) (sLocalClassHaar F S ν)
    (logNorm F S) (logModulus_continuous F S) l r s hs
  exact (ht.comp hp).subtype_mk _

end Completion

end

end Masullo
