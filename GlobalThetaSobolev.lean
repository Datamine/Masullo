import AdelicPolarDistributions
import OrbitalSobolevNorms
import HardySobolevTranslations
import ThetaMellinQuotients
import WeightedL2Coordinates
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.Topology.LocalAtTarget

open Filter Function MeasureTheory NumberField Set Topology
open scoped Classical ENNReal NNReal NumberField

namespace Masullo

noncomputable section

set_option maxHeartbeats 1500000

/-- Inversion on the modulus coordinate reflects the interval of endpoint weights. -/
theorem hardySobolevWeight_reflect (l r s x : ℝ) :
    hardySobolevWeight l r s (-x) = hardySobolevWeight (-r) (-l) s x := by
  have hl : 2 * l * -x = 2 * (-l) * x := by ring
  have hr : 2 * r * -x = 2 * (-r) * x := by ring
  simp only [hardySobolevWeight, hl, hr, neg_sq]
  rw [max_comm]

/-- For an ordered interval the original weight is invariant under inversion
exactly when the interval is symmetric about zero. -/
theorem hardySobolevWeight_inversionInvariant_iff (l r s : ℝ) (hlr : l ≤ r) :
    (∀ x, hardySobolevWeight l r s (-x) = hardySobolevWeight l r s x) ↔ l = -r := by
  constructor
  · intro h
    have he := h 1
    rw [hardySobolevWeight_reflect, hardySobolevWeight, hardySobolevWeight,
      max_eq_right (Real.exp_le_exp.mpr (by linarith)),
      max_eq_right (Real.exp_le_exp.mpr (by linarith))] at he
    have hpos : 0 < (1 + (1 : ℝ) ^ 2) ^ (s / 2) :=
      Real.rpow_pos_of_pos (by positivity) _
    have hp := Real.exp_injective (mul_right_cancel₀ hpos.ne' he)
    linarith
  · intro h x
    have hr : -l = r := by linarith
    rw [hardySobolevWeight_reflect, ← h, hr]

variable (F : Type*) [Field F] [NumberField F]

private abbrev Q := IdeleClass F
private abbrev logModulus (q : Q F) : ℝ := (ideleClassLogNorm F q).toAdd
private abbrev polarTests := (GlobalBruhat.polarEvaluation F).ker

/-- The global theta space formed from tests whose two polar values vanish,
with the topology inherited from the ordinary theta quotient. -/
abbrev GlobalPolarTheta := (globalThetaPolarEvaluation F).ker

private def polarThetaMk : polarTests F →L[ℂ] GlobalPolarTheta F :=
  ((globalThetaOperator F).ker.mkQL.comp (polarTests F).subtypeL).codRestrict _
    (fun f => f.property)

private theorem polarThetaMk_isOpenQuotientMap : IsOpenQuotientMap (polarThetaMk F) :=
  (globalThetaOperator F).ker.isOpenQuotientMap_mkQL.restrictPreimage (GlobalPolarTheta F)

private theorem polarTheta_weighted_decay (N : ℕ) :
    ∃ p : Seminorm ℂ (polarTests F), Continuous p ∧ ∀ (f : polarTests F) (q : Q F),
      ‖globalThetaOperator F f.val q‖ ≤ p f * Real.exp (-(N : ℝ) * |logModulus F q|) := by
  let σ : ℝ := (N : ℝ) + 2
  have hσ : 1 < σ := by dsimp [σ]; linarith [Nat.cast_nonneg (α := ℝ) N]
  obtain ⟨P, hP, hbound⟩ := adelicTheta_power_seminorm F σ hσ
  let T := GlobalBruhat.fourier F
  let p := (P + P.comp T.toLinearMap).comp (polarTests F).subtype
  refine ⟨p, (hP.add (hP.comp T.continuous)).comp continuous_subtype_val, fun f q => ?_⟩
  let u := GlobalBruhat.algebraicEquiv F f.val
  let v := GlobalBruhat.algebraicEquiv F (T f.val)
  let m := ideleClassNorm F q
  have hm : 0 < m := ideleClassNorm_pos F q
  have hf : GlobalBruhat.polarEvaluation F f.val = 0 := f.property
  have h0 : u.val 0 = 0 := congrArg Prod.fst hf
  have h1 : v.val 0 = 0 := congrArg Prod.snd hf
  have hest (w : GlobalBruhat F) (r : Q F) (hr : 1 ≤ ideleClassNorm F r) (n : ℕ)
      (hn : (n : ℝ) ≤ σ) :
      ‖globalThetaOperator F w r‖ ≤ P w * (ideleClassNorm F r ^ n)⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ (pow_pos (ideleClassNorm_pos F r) _), mul_comm]
    have hle : ideleClassNorm F r ^ n ≤ ideleClassNorm F r ^ σ := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le hr hn
    exact ((mul_le_mul_of_nonneg_left (norm_adelicTheta_le_abs F
      (GlobalBruhat.algebraicEquiv F w).property r) (by positivity)).trans
      (mul_le_mul_of_nonneg_right hle (by
        obtain ⟨g, rfl⟩ := ideleClassMap_surjective F r
        unfold adelicThetaAbs
        exact tsum_nonneg fun _ => norm_nonneg _))).trans (hbound w r)
  change ‖adelicTheta F u.val q‖ ≤ (P f.val + P (T f.val)) * Real.exp (-(N : ℝ) * |Real.log m|)
  rcases le_total 1 m with hbig | hsmall
  · rw [abs_of_nonneg (Real.log_nonneg hbig), neg_mul, Real.exp_neg, Real.exp_nat_mul,
      Real.exp_log hm]
    exact (hest f.val q hbig N (by dsimp [σ]; linarith)).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (apply_nonneg P _)) (by positivity))
  · have hinv : 1 ≤ ideleClassNorm F q⁻¹ := by
      rw [map_inv]
      exact (one_le_inv₀ hm).mpr hsmall
    have htheta : adelicTheta F u.val q = m⁻¹ • adelicTheta F v.val q⁻¹ := by
      have he := congrFun (adelicTheta_riemannRoch F u.property).2 q
      rw [← GlobalBruhat.fourier_apply F f.val] at he
      change adelicTheta F u.val q = m⁻¹ • adelicTheta F v.val q⁻¹ +
        m⁻¹ • v.val 0 - u.val 0 at he
      simpa only [h0, h1, smul_zero, add_zero, sub_zero] using he
    have hb := hest (T f.val) q⁻¹ hinv (N + 1) (by push_cast; dsimp [σ]; linarith)
    rw [map_inv, inv_pow, inv_inv] at hb
    rw [htheta, norm_smul, Real.norm_of_nonneg (by positivity), abs_of_nonpos (Real.log_nonpos hm.le hsmall),
      neg_mul_neg, Real.exp_nat_mul, Real.exp_log hm]
    calc
      _ ≤ m⁻¹ * (P (T f.val) * m ^ (N + 1)) := mul_le_mul_of_nonneg_left hb (by positivity)
      _ = P (T f.val) * m ^ N := by rw [pow_succ]; field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_left (apply_nonneg P _)) (by positivity)

private theorem amplitude_pos (l r s x : ℝ) : 0 < hardySobolevAmplitude l r s x := by
  apply Real.sqrt_pos.mpr
  unfold hardySobolevWeight
  exact mul_pos ((Real.exp_pos _).trans_le (le_max_left _ _))
    (Real.rpow_pos_of_pos (by positivity) _)

private theorem weighted_exp_le (a l r s x : ℝ) (hs : 0 ≤ s) :
    hardySobolevWeight l r s x * Real.exp (2 * a * x) ≤
      Real.exp ((2 * max |l| |r| + 2 * |a| + s) * |x|) := by
  have hmul (y : ℝ) : y * x ≤ |y| * |x| := by
    rw [← abs_mul]
    exact le_abs_self _
  have hmax (y : ℝ) (hy : |y| ≤ max |l| |r|) :
      Real.exp (2 * y * x) ≤ Real.exp (2 * max |l| |r| * |x|) := by
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_right hy (abs_nonneg x)
    linarith [hmul y]
  have hpoly : (1 + x ^ 2) ^ (s / 2) ≤ Real.exp (s * |x|) := by
    have hbase : 1 + x ^ 2 ≤ Real.exp (2 * |x|) := by
      rw [mul_comm (2 : ℝ) |x|, Real.exp_mul, Real.rpow_two]
      calc
        _ ≤ (1 + |x|) ^ 2 := by rw [add_sq, sq_abs]; linarith [abs_nonneg x]
        _ ≤ _ := pow_le_pow_left₀ (by positivity) (by simpa only [add_comm] using Real.add_one_le_exp |x|) _
    calc
      _ ≤ (Real.exp (2 * |x|)) ^ (s / 2) := Real.rpow_le_rpow (by positivity) hbase (by positivity)
      _ = _ := by rw [← Real.exp_mul]; congr 1; ring
  have ha : Real.exp (2 * a * x) ≤ Real.exp (2 * |a| * |x|) := by
    apply Real.exp_le_exp.mpr
    linarith [hmul a]
  unfold hardySobolevWeight
  calc
    _ ≤ (Real.exp (2 * max |l| |r| * |x|) * Real.exp (s * |x|)) *
        Real.exp (2 * |a| * |x|) := by
      gcongr
      exact max_le (hmax l (le_max_left _ _)) (hmax r (le_max_right _ _))
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring

private def weightedTheta (a l r s : ℝ) (f : polarTests F) (q : Q F) : ℂ :=
  (hardySobolevAmplitude l r s (logModulus F q) * Real.exp (a * logModulus F q)) •
    globalThetaOperator F f.val q

private theorem weightedTheta_continuous (a l r s : ℝ) (f : polarTests F) :
    Continuous (weightedTheta F a l r s f) := by
  have hl : Continuous (logModulus F) := ideleClassLogNorm_continuous F
  have hw : Continuous (fun x : ℝ => hardySobolevAmplitude l r s x * Real.exp (a * x)) :=
    (Real.continuous_sqrt.comp (continuous_hardySobolevWeight l r s)).mul (by fun_prop)
  exact (hw.comp hl).smul (adelicTheta_continuous F
    (bruhat_theta_continuous_and_invariant (GlobalBruhat.algebraicEquiv F f.val).property).1)

local instance globalThetaSobolevMeasurable : MeasurableSpace (Q F) := borel _
local instance globalThetaSobolevBorel : BorelSpace (Q F) := ⟨rfl⟩

variable (μ : Measure (Q F)) [μ.IsHaarMeasure]

private theorem weightedTheta_controls (a l r s : ℝ) (hs : 0 ≤ s) :
    ∃ p : Seminorm ℂ (polarTests F), Continuous p ∧
      ∃ w : Q F → ℝ, Integrable w μ ∧ (∀ q, 0 ≤ w q) ∧
      ∀ (f : polarTests F) (q : Q F), ‖weightedTheta F a l r s f q‖ ^ 2 ≤ p f ^ 2 * w q := by
  let A := 2 * max |l| |r| + 2 * |a| + s
  obtain ⟨N, hN⟩ := exists_nat_gt ((A + 1) / 2)
  obtain ⟨p, hp, hdecay⟩ := polarTheta_weighted_decay F N
  let w₀ (x : ℝ) := Real.exp (-1 * |x|)
  let w := w₀ ∘ logModulus F
  have hl : Measurable (logModulus F) :=
    (show Continuous (logModulus F) from ideleClassLogNorm_continuous F).measurable
  obtain ⟨c, hc, hμ⟩ := ideleClassLogNorm_map_haar F μ
  have hw : Integrable w μ := by
    have hw₀ : Measurable w₀ := by dsimp [w₀]; fun_prop
    apply (integrable_map_measure hw₀.aestronglyMeasurable hl.aemeasurable).mp
    rw [hμ]
    exact (integrable_exp_abs_envelope 1 one_pos).smul_measure_nnreal
  refine ⟨p, hp, w, hw, fun _ => (Real.exp_pos _).le, fun f q => ?_⟩
  let x := logModulus F q
  have hdec : ‖globalThetaOperator F f.val q‖ ^ 2 ≤ p f ^ 2 * Real.exp (-(2 * (N : ℝ)) * |x|) := by
    calc
      _ ≤ (p f * Real.exp (-(N : ℝ) * |x|)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (hdecay f q) _
      _ = _ := by rw [mul_pow, ← Real.exp_nat_mul]; congr 2; ring
  unfold weightedTheta
  rw [norm_smul, Real.norm_of_nonneg (mul_nonneg (amplitude_pos ..).le (Real.exp_pos _).le),
    mul_pow, mul_pow, hardySobolevAmplitude, Real.sq_sqrt (hardySobolevWeight_nonneg ..),
    ← Real.exp_nat_mul, Nat.cast_ofNat]
  change (hardySobolevWeight l r s x * Real.exp (2 * (a * x))) *
    ‖globalThetaOperator F f.val q‖ ^ 2 ≤ _
  rw [← mul_assoc (2 : ℝ) a x]
  calc
    _ ≤ Real.exp (A * |x|) * (p f ^ 2 * Real.exp (-(2 * (N : ℝ)) * |x|)) :=
      mul_le_mul (weighted_exp_le a l r s x hs) hdec (sq_nonneg _) (Real.exp_pos _).le
    _ = p f ^ 2 * Real.exp ((A - 2 * (N : ℝ)) * |x|) := by
      rw [mul_left_comm, ← Real.exp_add]; congr 2; ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)

/-- Evaluation of a polar-free theta function on idele classes. -/
def globalPolarThetaFunction : GlobalPolarTheta F →ₗ[ℂ] (Q F → ℂ) :=
  ((globalThetaOperator F).ker.liftQ (globalThetaOperator F) le_rfl).comp
    (GlobalPolarTheta F).subtype

@[simp] private theorem globalPolarThetaFunction_mk (f : polarTests F) (q : Q F) :
    globalPolarThetaFunction F (polarThetaMk F f) q = globalThetaOperator F f.val q := rfl

private def thetaSobolevProfile (a l r s : ℝ) (u : GlobalPolarTheta F) (q : Q F) : ℂ :=
  (hardySobolevAmplitude l r s (logModulus F q) * Real.exp (a * logModulus F q)) •
    globalPolarThetaFunction F u q

private theorem thetaSobolevProfile_continuous (a l r s : ℝ) (u : GlobalPolarTheta F) :
    Continuous (thetaSobolevProfile F a l r s u) := by
  obtain ⟨f, rfl⟩ := (polarThetaMk_isOpenQuotientMap F).surjective u
  exact weightedTheta_continuous F a l r s f

private theorem thetaSobolevProfile_memLp (a l r s : ℝ) (hs : 0 ≤ s)
    (u : GlobalPolarTheta F) : MemLp (thetaSobolevProfile F a l r s u) 2 μ := by
  obtain ⟨f, rfl⟩ := (polarThetaMk_isOpenQuotientMap F).surjective u
  obtain ⟨p, _, w, hw, _, hbound⟩ := weightedTheta_controls F μ a l r s hs
  apply (memLp_two_iff_integrable_sq_norm
    (weightedTheta_continuous F a l r s f).aestronglyMeasurable).mpr
  apply (hw.const_mul (p f ^ 2)).mono'
    ((weightedTheta_continuous F a l r s f).norm.pow 2).aestronglyMeasurable
  filter_upwards with q
  change ‖‖weightedTheta F a l r s f q‖ ^ 2‖ ≤ p f ^ 2 * w q
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact hbound f q

/-- The norm-twisted polar-free theta quotient mapped continuously into
the weighted Hilbert space in its unweighted amplitude coordinates. -/
def globalThetaSobolevMap (a l r s : ℝ) (hs : 0 ≤ s) :
    GlobalPolarTheta F →L[ℂ] Lp ℂ 2 μ := by
  let h := thetaSobolevProfile_memLp F μ a l r s hs
  let L : GlobalPolarTheta F →ₗ[ℂ] Lp ℂ 2 μ :=
    { toFun := fun u => (h u).toLp _
      map_add' u v := by
        rw [← MemLp.toLp_add (h u) (h v)]
        apply MemLp.toLp_congr
        refine Eventually.of_forall fun q => ?_
        change thetaSobolevProfile F a l r s (u + v) q =
          thetaSobolevProfile F a l r s u q + thetaSobolevProfile F a l r s v q
        simp [thetaSobolevProfile, smul_add]
      map_smul' c u := by
        change (h (c • u)).toLp _ = c • (h u).toLp _
        rw [← MemLp.toLp_const_smul c (h u)]
        apply MemLp.toLp_congr
        refine Eventually.of_forall fun q => ?_
        change thetaSobolevProfile F a l r s (c • u) q = c • thetaSobolevProfile F a l r s u q
        simp [thetaSobolevProfile]
        ring }
  refine ⟨L, (polarThetaMk_isOpenQuotientMap F).continuous_comp_iff.mp ?_⟩
  obtain ⟨p, hp, w, hw, hn, hbound⟩ := weightedTheta_controls F μ a l r s hs
  let R := L.comp (polarThetaMk F).toLinearMap
  let C : ℝ≥0 := ⟨Real.sqrt (∫ q, w q ∂μ), Real.sqrt_nonneg _⟩
  have hnorm (f : polarTests F) : ‖R f‖ ≤ (C • p) f := by
    change ‖(h (polarThetaMk F f)).toLp _‖ ≤ (C : ℝ) * p f
    have he : ‖(h (polarThetaMk F f)).toLp _‖ ^ 2 ≤ (p f ^ 2) * ∫ q, w q ∂μ := by
      rw [norm_sq_toLp_two, ← integral_const_mul]
      exact integral_mono ((memLp_two_iff_integrable_sq_norm
        (weightedTheta_continuous F a l r s f).aestronglyMeasurable).mp (h (polarThetaMk F f)))
        (hw.const_mul _) (hbound f)
    have hC : (C : ℝ) ^ 2 = ∫ q, w q ∂μ := Real.sq_sqrt (integral_nonneg hn)
    apply le_of_pow_le_pow_left₀ (n := 2) (by positivity : 2 ≠ 0)
      (mul_nonneg C.coe_nonneg (apply_nonneg p _))
    rw [mul_pow, hC, mul_comm]
    exact he
  have hcont : Continuous ((normSeminorm ℂ (Lp ℂ 2 μ)).comp R) :=
    Seminorm.continuous_of_le (q := C • p) (continuous_const.mul hp) hnorm
  apply continuous_of_continuousAt_zero R
  rw [ContinuousAt, map_zero, tendsto_zero_iff_norm_tendsto_zero]
  exact hcont.tendsto' _ _ (map_zero _)

/-- The embedding sends a test to its weighted theta function almost everywhere. -/
theorem globalThetaSobolevMap_ae (a l r s : ℝ) (hs : 0 ≤ s) (u : GlobalPolarTheta F) :
    (globalThetaSobolevMap F μ a l r s hs u : Q F → ℂ) =ᵐ[μ]
      thetaSobolevProfile F a l r s u :=
  (thetaSobolevProfile_memLp F μ a l r s hs u).coeFn_toLp

theorem globalThetaSobolevMap_injective (a l r s : ℝ) (hs : 0 ≤ s) :
    Injective (globalThetaSobolevMap F μ a l r s hs) := by
  apply (globalThetaSobolevMap F μ a l r s hs).toLinearMap.ker_eq_bot.mp
  apply le_antisymm _ bot_le
  intro u hu
  change globalThetaSobolevMap F μ a l r s hs u = 0 at hu
  have hp := globalThetaSobolevMap_ae F μ a l r s hs u
  rw [hu] at hp
  have he := hp.symm.trans (Lp.coeFn_zero ℂ 2 μ)
  have hf := ((thetaSobolevProfile_continuous F a l r s u).ae_eq_iff_eq
    (μ := μ) continuous_const).mp he
  obtain ⟨f, rfl⟩ := (polarThetaMk_isOpenQuotientMap F).surjective u
  have hker : f.val ∈ (globalThetaOperator F).ker := by
    apply LinearMap.mem_ker.mpr
    funext q
    have hval := congrFun hf q
    change (hardySobolevAmplitude l r s (logModulus F q) * Real.exp (a * logModulus F q)) •
      globalThetaOperator F f.val q = 0 at hval
    exact (smul_eq_zero.mp hval).resolve_left ((mul_pos (amplitude_pos ..) (Real.exp_pos _)).ne')
  change polarThetaMk F f = 0
  apply Subtype.ext
  exact (Submodule.Quotient.mk_eq_zero _).mpr hker

private theorem thetaSobolevProfile_norm_sq (a l r s : ℝ) (u : GlobalPolarTheta F) (q : Q F) :
    ‖thetaSobolevProfile F a l r s u q‖ ^ 2 =
      ‖globalPolarThetaFunction F u q‖ ^ 2 *
        hardySobolevWeight (a + l) (a + r) s (logModulus F q) := by
  let x := logModulus F q
  have hp : 0 ≤ hardySobolevAmplitude l r s x * Real.exp (a * x) :=
    (mul_pos (amplitude_pos ..) (Real.exp_pos _)).le
  have hw : hardySobolevWeight l r s x * Real.exp (2 * (a * x)) =
      hardySobolevWeight (a + l) (a + r) s x := by
    unfold hardySobolevWeight
    rw [mul_right_comm, max_mul_of_nonneg _ _ (Real.exp_pos _).le,
      ← Real.exp_add, ← Real.exp_add]
    have hleft : 2 * l * x + 2 * (a * x) = 2 * (a + l) * x := by ring
    have hright : 2 * r * x + 2 * (a * x) = 2 * (a + r) * x := by ring
    rw [hleft, hright]
  unfold thetaSobolevProfile
  rw [norm_smul, Real.norm_of_nonneg hp, mul_pow, mul_pow,
    hardySobolevAmplitude, Real.sq_sqrt (hardySobolevWeight_nonneg ..), ← Real.exp_nat_mul]
  change (hardySobolevWeight l r s x * Real.exp (2 * (a * x))) * _ = _
  rw [hw, mul_comm]

/-- The Hilbert norm restricts to exactly (10.1.1.6) on the polar-free theta quotient. -/
theorem globalThetaSobolevMap_norm_sq (a l r s : ℝ) (hs : 0 ≤ s) (u : GlobalPolarTheta F) :
    ‖globalThetaSobolevMap F μ a l r s hs u‖ ^ 2 =
      ∫ q, ‖globalPolarThetaFunction F u q‖ ^ 2 *
        hardySobolevWeight (a + l) (a + r) s (logModulus F q) ∂μ := by
  change ‖(thetaSobolevProfile_memLp F μ a l r s hs u).toLp _‖ ^ 2 = _
  rw [norm_sq_toLp_two]
  exact integral_congr_ae (Eventually.of_forall (thetaSobolevProfile_norm_sq F a l r s u))

/-- The polar-free theta quotient is invariant under left translation. -/
def globalPolarThetaTranslate (g : Q F) : GlobalPolarTheta F →L[ℂ] GlobalPolarTheta F :=
  ((globalThetaTranslate F g).comp (GlobalPolarTheta F).subtypeL).codRestrict _ fun u => by
    change globalThetaPolarEvaluation F (globalThetaTranslate F g u.val) = 0
    rw [globalThetaPolarEvaluation_translate, show globalThetaPolarEvaluation F u.val = 0 from u.property]
    simp

theorem globalPolarThetaFunction_translate (g q : Q F) (u : GlobalPolarTheta F) :
    globalPolarThetaFunction F (globalPolarThetaTranslate F g u) q =
      globalPolarThetaFunction F u (g⁻¹ * q) := by
  obtain ⟨f, rfl⟩ := (polarThetaMk_isOpenQuotientMap F).surjective u
  obtain ⟨a, rfl⟩ := ideleClassMap_surjective F g
  exact globalThetaOperator_leftTranslate F a f.val q

/-- The weighted translation extends the action on the theta quotient
with exactly the factor from the norm twist in (10.1.1.2). -/
theorem globalThetaSobolevMap_translate (a l r s : ℝ) (hs : 0 ≤ s)
    (g : Q F) (u : GlobalPolarTheta F) :
    hardySobolevMulTranslation μ (ideleClassLogNorm F) (ideleClassLogNorm_continuous F)
      l r s hs g (globalThetaSobolevMap F μ a l r s hs u) =
        (Real.exp (-a * logModulus F g) : ℂ) •
          globalThetaSobolevMap F μ a l r s hs (globalPolarThetaTranslate F g u) := by
  let J := globalThetaSobolevMap F μ a l r s hs
  let c : ℂ := (Real.exp (-a * logModulus F g) : ℝ)
  let v := globalPolarThetaTranslate F g u
  apply Lp.ext
  filter_upwards [hardySobolevMulTranslation_ae μ (ideleClassLogNorm F)
      (ideleClassLogNorm_continuous F) l r s hs g (J u),
    (measurePreserving_mul_left μ g⁻¹).quasiMeasurePreserving.ae
      (globalThetaSobolevMap_ae F μ a l r s hs u),
    Lp.coeFn_smul c (J v), globalThetaSobolevMap_ae F μ a l r s hs v]
    with q h₁ h₂ h₃ h₄
  change _ = (c • J v : Lp ℂ 2 μ) q
  rw [h₁, h₂, h₃, Pi.smul_apply, h₄]
  simp only [thetaSobolevProfile, smul_eq_mul, Complex.real_smul, Complex.ofReal_mul]
  change _ = c * (_ * _ * globalPolarThetaFunction F (globalPolarThetaTranslate F g u) q)
  rw [globalPolarThetaFunction_translate]
  let x := logModulus F q
  let y := logModulus F g
  have he : logModulus F (g⁻¹ * q) = x - y := by
    unfold logModulus
    rw [map_mul, map_inv]
    change -y + x = x - y
    abel
  have hE : Real.exp (a * logModulus F (g⁻¹ * q)) =
      Real.exp (-a * y) * Real.exp (a * x) := by rw [he, ← Real.exp_add]; congr 1; ring
  let Aq := hardySobolevAmplitude l r s x
  let Agq := hardySobolevAmplitude l r s (logModulus F (g⁻¹ * q))
  let Ex := Real.exp (a * x)
  let Ey := Real.exp (-a * y)
  let z := globalPolarThetaFunction F u (g⁻¹ * q)
  change ((Aq / Agq : ℝ) : ℂ) * ((Agq : ℂ) *
    (Real.exp (a * logModulus F (g⁻¹ * q)) : ℂ) * z) =
    (Ey : ℂ) * ((Aq : ℂ) * (Ex : ℂ) * z)
  rw [hE]
  change ((Aq / Agq : ℝ) : ℂ) * ((Agq : ℂ) * ((Ey * Ex : ℝ) : ℂ) * z) = _
  have hA : (Agq : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (amplitude_pos ..).ne'
  rw [Complex.ofReal_div, Complex.ofReal_mul]
  field_simp [hA]

/-- The closure specified in Definition 10.1.1.1. -/
def globalThetaSobolevCompletion (a l r s : ℝ) (hs : 0 ≤ s) : Submodule ℂ (Lp ℂ 2 μ) :=
  (globalThetaSobolevMap F μ a l r s hs).range.topologicalClosure

/-- The polar-free theta tests are dense in their Hilbert completion. -/
theorem globalThetaSobolevCompletion_dense (a l r s : ℝ) (hs : 0 ≤ s) :
    DenseRange ((globalThetaSobolevMap F μ a l r s hs).codRestrict
      (globalThetaSobolevCompletion F μ a l r s hs)
      (fun u => subset_closure ⟨u, rfl⟩)) := by
  rw [DenseRange, Subtype.dense_iff, ← range_comp]
  change closure (range (globalThetaSobolevMap F μ a l r s hs)) ⊆
    closure (range (globalThetaSobolevMap F μ a l r s hs))
  exact subset_rfl

theorem globalThetaSobolevCompletion_isClosed (a l r s : ℝ) (hs : 0 ≤ s) :
    IsClosed (globalThetaSobolevCompletion F μ a l r s hs : Set (Lp ℂ 2 μ)) :=
  Submodule.isClosed_topologicalClosure _

theorem globalThetaSobolevCompletion_complete (a l r s : ℝ) (hs : 0 ≤ s) :
    CompleteSpace (globalThetaSobolevCompletion F μ a l r s hs) :=
  (globalThetaSobolevCompletion_isClosed F μ a l r s hs).completeSpace_coe

theorem globalThetaSobolevCompletion_separable (a l r s : ℝ) (hs : 0 ≤ s) :
    TopologicalSpace.SeparableSpace (globalThetaSobolevCompletion F μ a l r s hs) := by
  letI : SecondCountableTopology (NumberField.AdeleRing (𝓞 F) F) := adeles_secondCountable F
  letI : SecondCountableTopology (NumberField.AdeleRing (𝓞 F) F)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  letI : SecondCountableTopology (Idele F) := Units.isEmbedding_embedProduct.secondCountableTopology
  letI : SecondCountableTopology (Q F) := TopologicalSpace.Quotient.secondCountableTopology
    (QuotientGroup.isOpenMap_coe (N := principalIdeles F))
  letI : LocallyCompactSpace (Q F) := ideleClasses_locallyCompact
  letI : SigmaFinite μ := inferInstance
  letI : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  letI : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  letI : SecondCountableTopology (Lp ℂ 2 μ) := inferInstance
  infer_instance

theorem globalThetaSobolevCompletion_mapsTo (a l r s : ℝ) (hs : 0 ≤ s) (g : Q F) :
    MapsTo (hardySobolevMulTranslation μ (ideleClassLogNorm F) (ideleClassLogNorm_continuous F)
      l r s hs g) (globalThetaSobolevCompletion F μ a l r s hs)
      (globalThetaSobolevCompletion F μ a l r s hs) := by
  let J := globalThetaSobolevMap F μ a l r s hs
  let T := hardySobolevMulTranslation μ (ideleClassLogNorm F) (ideleClassLogNorm_continuous F)
    l r s hs g
  have hm : MapsTo T (range J) (range J) := by
    rintro _ ⟨u, rfl⟩
    refine ⟨(Real.exp (-a * logModulus F g) : ℂ) • globalPolarThetaTranslate F g u, ?_⟩
    rw [map_smul]
    exact (globalThetaSobolevMap_translate F μ a l r s hs g u).symm
  exact hm.closure T.continuous

set_option maxHeartbeats 5000000 in
/-- The continuous translation action restricts to the closed theta
completion of Lemma 10.1.1.3. -/
theorem continuous_globalThetaSobolevCompletion_translate (a l r s : ℝ) (hs : 0 ≤ s) :
    Continuous (fun p : Q F × globalThetaSobolevCompletion F μ a l r s hs =>
      (⟨hardySobolevMulTranslation μ (ideleClassLogNorm F) (ideleClassLogNorm_continuous F)
        l r s hs p.1 p.2.val, globalThetaSobolevCompletion_mapsTo F μ a l r s hs p.1 p.2.property⟩ :
        globalThetaSobolevCompletion F μ a l r s hs)) := by
  letI : LocallyCompactSpace (Q F) := ideleClasses_locallyCompact
  letI : T1Space (Q F) := QuotientGroup.t1Space_iff.mpr principalIdeles_closed
  letI : SecondCountableTopology (NumberField.AdeleRing (𝓞 F) F) := adeles_secondCountable F
  letI : SecondCountableTopology (NumberField.AdeleRing (𝓞 F) F)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  letI : SecondCountableTopology (Idele F) := Units.isEmbedding_embedProduct.secondCountableTopology
  letI : SecondCountableTopology (Q F) := TopologicalSpace.Quotient.secondCountableTopology
    (QuotientGroup.isOpenMap_coe (N := principalIdeles F))
  letI : μ.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure μ
  have hp : Continuous (fun p : Q F × globalThetaSobolevCompletion F μ a l r s hs =>
      (p.1, (p.2.val : Lp ℂ 2 μ))) :=
    continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  have ht := continuous_hardySobolevMulTranslation (G := Q F) μ (ideleClassLogNorm F)
    (ideleClassLogNorm_continuous F) l r s hs
  exact (ht.comp hp).subtype_mk _

/-- Fourier transformation preserves both vanishing polar conditions. -/
def globalPolarThetaFourier : GlobalPolarTheta F →L[ℂ] GlobalPolarTheta F :=
  ((globalThetaFourier F).comp (GlobalPolarTheta F).subtypeL).codRestrict _ (by
    intro u
    obtain ⟨f, rfl⟩ := (polarThetaMk_isOpenQuotientMap F).surjective u
    change GlobalBruhat.polarEvaluation F (GlobalBruhat.fourier F f.val) = 0
    have h : GlobalBruhat.polarEvaluation F f.val = 0 := f.property
    apply Prod.ext
    · exact congrArg Prod.snd h
    · exact (adelicTheta_fourier_fourier F f.val).1.trans (congrArg Prod.fst h))

theorem globalPolarThetaFourier_involutive : Involutive (globalPolarThetaFourier F) :=
  fun u => Subtype.ext (globalThetaFourier_involutive F u.val)

private theorem logModulus_inv (q : Q F) : logModulus F q⁻¹ = -logModulus F q := by
  change ((ideleClassLogNorm F) q⁻¹).toAdd = _
  rw [map_inv]
  rfl

private theorem logModulus_mul (p q : Q F) : logModulus F (p * q) =
    logModulus F p + logModulus F q := by
  change ((ideleClassLogNorm F) (p * q)).toAdd = _
  rw [map_mul]
  rfl

private theorem globalPolarThetaFourier_eval (u : GlobalPolarTheta F) (q : Q F) :
    globalPolarThetaFunction F (globalPolarThetaFourier F u) q =
      Real.exp (-logModulus F q) • globalPolarThetaFunction F u q⁻¹ := by
  obtain ⟨f, rfl⟩ := (polarThetaMk_isOpenQuotientMap F).surjective u
  let v := GlobalBruhat.algebraicEquiv F f.val
  let w := GlobalBruhat.algebraicEquiv F (GlobalBruhat.fourier F f.val)
  have h : GlobalBruhat.polarEvaluation F f.val = 0 := f.property
  have h₀ : v.val 0 = 0 := congrArg Prod.fst h
  have h₁ : w.val 0 = 0 := congrArg Prod.snd h
  have he := congrFun (adelicTheta_riemannRoch F v.property).2 q⁻¹
  rw [← GlobalBruhat.fourier_apply F f.val] at he
  change adelicTheta F v.val q⁻¹ = (ideleClassNorm F q⁻¹)⁻¹ • adelicTheta F w.val q⁻¹⁻¹ +
    (ideleClassNorm F q⁻¹)⁻¹ • w.val 0 - v.val 0 at he
  simp only [map_inv, inv_inv, h₀, h₁, smul_zero, add_zero, sub_zero] at he
  rw [show q⁻¹⁻¹ = q from inv_inv q] at he
  have hq : Real.exp (-logModulus F q) = (ideleClassNorm F q)⁻¹ := by
    rw [Real.exp_neg]
    exact congrArg Inv.inv (Real.exp_log (ideleClassNorm_pos F q))
  change adelicTheta F w.val q = Real.exp (-logModulus F q) • adelicTheta F v.val q⁻¹
  rw [hq, he, smul_smul, inv_mul_cancel₀ (ideleClassNorm_pos F q).ne', one_smul]

private theorem ideleClassHaar_regular : μ.Regular := by
  letI : SecondCountableTopology (NumberField.AdeleRing (𝓞 F) F) := adeles_secondCountable F
  letI : SecondCountableTopology (NumberField.AdeleRing (𝓞 F) F)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  letI : SecondCountableTopology (Idele F) := Units.isEmbedding_embedProduct.secondCountableTopology
  letI : SecondCountableTopology (Q F) := TopologicalSpace.Quotient.secondCountableTopology
    (QuotientGroup.isOpenMap_coe (N := principalIdeles F))
  letI : LocallyCompactSpace (Q F) := ideleClasses_locallyCompact
  letI : T1Space (Q F) := QuotientGroup.t1Space_iff.mpr principalIdeles_closed
  exact Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure μ

private theorem ideleClassHaar_inv : MeasurePreserving (Inv.inv : Q F → Q F) μ μ := by
  letI : LocallyCompactSpace (Q F) := ideleClasses_locallyCompact
  letI : μ.Regular := ideleClassHaar_regular F μ
  exact Measure.measurePreserving_inv μ

/-- In amplitude coordinates, inversion between the reflected intervals is the
Haar pullback. -/
def globalThetaSobolevReflection : Lp ℂ 2 μ →ₗᵢ[ℂ] Lp ℂ 2 μ :=
  Lp.compMeasurePreservingₗᵢ ℂ Inv.inv (ideleClassHaar_inv F μ)

private theorem globalThetaSobolevReflection_ae (u : Lp ℂ 2 μ) :
    (globalThetaSobolevReflection F μ u : Q F → ℂ) =ᵐ[μ] fun q => u q⁻¹ :=
  Lp.coeFn_compMeasurePreserving u (ideleClassHaar_inv F μ)

theorem globalThetaSobolevReflection_involutive : Involutive (globalThetaSobolevReflection F μ) := by
  intro u
  apply Lp.ext
  filter_upwards [globalThetaSobolevReflection_ae F μ (globalThetaSobolevReflection F μ u),
    (ideleClassHaar_inv F μ).quasiMeasurePreserving.ae (globalThetaSobolevReflection_ae F μ u)]
    with q h₁ h₂
  rw [h₁, h₂]
  exact congrArg (fun x : Q F => u x) (inv_inv q)

/-- The adelic Riemann–Roch formula identifies Fourier transformation of a
twisted theta test with inversion in the reflected interval. -/
theorem globalThetaSobolevReflection_fourier (a l r s : ℝ) (hs : 0 ≤ s) (u : GlobalPolarTheta F) :
    globalThetaSobolevReflection F μ (globalThetaSobolevMap F μ a l r s hs u) =
      globalThetaSobolevMap F μ (1 - a) (-r) (-l) s hs (globalPolarThetaFourier F u) := by
  apply Lp.ext
  filter_upwards [globalThetaSobolevReflection_ae F μ (globalThetaSobolevMap F μ a l r s hs u),
    (ideleClassHaar_inv F μ).quasiMeasurePreserving.ae (globalThetaSobolevMap_ae F μ a l r s hs u),
    globalThetaSobolevMap_ae F μ (1-a) (-r) (-l) s hs (globalPolarThetaFourier F u)]
    with q h₁ h₂ h₃
  rw [h₁, h₂, h₃]
  unfold thetaSobolevProfile
  rw [globalPolarThetaFourier_eval, logModulus_inv, smul_smul, mul_assoc, ← Real.exp_add]
  have hA : hardySobolevAmplitude l r s (-logModulus F q) =
      hardySobolevAmplitude (-r) (-l) s (logModulus F q) :=
    congrArg Real.sqrt (hardySobolevWeight_reflect l r s _)
  rw [hA]
  congr 3
  ring

private theorem globalThetaSobolevReflection_mapsTo (a l r s : ℝ) (hs : 0 ≤ s) :
    MapsTo (globalThetaSobolevReflection F μ)
      (globalThetaSobolevCompletion F μ a l r s hs)
      (globalThetaSobolevCompletion F μ (1-a) (-r) (-l) s hs) := by
  have h : MapsTo (globalThetaSobolevReflection F μ)
      (range (globalThetaSobolevMap F μ a l r s hs))
      (range (globalThetaSobolevMap F μ (1-a) (-r) (-l) s hs)) := by
    rintro _ ⟨u, rfl⟩
    exact ⟨globalPolarThetaFourier F u, (globalThetaSobolevReflection_fourier F μ a l r s hs u).symm⟩
  exact h.closure (globalThetaSobolevReflection F μ).continuous

/-- The inversion isometry of (10.1.2.1), with the ambient interval reflected. -/
def globalThetaSobolevFourierEquiv (a l r s : ℝ) (hs : 0 ≤ s) :
    globalThetaSobolevCompletion F μ a l r s hs ≃ₗᵢ[ℂ]
      globalThetaSobolevCompletion F μ (1-a) (-r) (-l) s hs where
  toFun u := ⟨globalThetaSobolevReflection F μ u.val,
    globalThetaSobolevReflection_mapsTo F μ a l r s hs u.property⟩
  invFun v := ⟨globalThetaSobolevReflection F μ v.val, by
    have h := globalThetaSobolevReflection_mapsTo F μ (1-a) (-r) (-l) s hs v.property
    change globalThetaSobolevReflection F μ v.val ∈
      (globalThetaSobolevCompletion F μ a l r s hs : Set (Lp ℂ 2 μ))
    simpa only [sub_sub_cancel, neg_neg] using h⟩
  left_inv u := Subtype.ext (globalThetaSobolevReflection_involutive F μ u.val)
  right_inv v := Subtype.ext (globalThetaSobolevReflection_involutive F μ v.val)
  map_add' u v := Subtype.ext (map_add (globalThetaSobolevReflection F μ) u.val v.val)
  map_smul' c u := Subtype.ext (map_smul (globalThetaSobolevReflection F μ) c u.val)
  norm_map' u := (globalThetaSobolevReflection F μ).norm_map u.val

private abbrev ordinaryTheta := (globalThetaOperator F).ker.liftQ (globalThetaOperator F) le_rfl

private theorem ordinaryTheta_translate (g : Q F) (u : GlobalThetaQuotient F) (q : Q F) :
    ordinaryTheta F (globalThetaTranslate F g u) q = ordinaryTheta F u (g⁻¹ * q) := by
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ u
  obtain ⟨b, rfl⟩ := ideleClassMap_surjective F g
  rw [globalThetaTranslate_class, globalThetaTranslateIdeles_mk]
  exact globalThetaOperator_leftTranslate F b f q

private abbrev ray (t : ℝ) := ideleClassExpSection F (Multiplicative.ofAdd t)

private theorem logModulus_ray (t : ℝ) : logModulus F (ray F t) = t :=
  congrArg Multiplicative.toAdd (ideleClassLogNorm_expSection F (Multiplicative.ofAdd t))

/-- A difference of two translated theta functions with polar values (1,0)
has both polar values zero. Some such difference is nonzero. -/
theorem exists_globalPolarTheta_eval_ne_zero :
    ∃ (u : GlobalPolarTheta F) (q : Q F), globalPolarThetaFunction F u q ≠ 0 := by
  obtain ⟨u, hu⟩ := globalThetaPolarEvaluation_surjective F (1, 0)
  let v (g : Q F) : GlobalPolarTheta F := ⟨globalThetaTranslate F g u - u, by
    change globalThetaPolarEvaluation F (globalThetaTranslate F g u - u) = 0
    rw [map_sub, globalThetaPolarEvaluation_translate, hu]
    simp⟩
  by_contra! h
  have he (g q : Q F) : ordinaryTheta F u (g⁻¹ * q) = ordinaryTheta F u q := by
    have hv := h (v g) q
    change ordinaryTheta F (globalThetaTranslate F g u - u) q = 0 at hv
    rw [map_sub, Pi.sub_apply, ordinaryTheta_translate] at hv
    exact sub_eq_zero.mp hv
  have hconst (p q : Q F) : ordinaryTheta F u p = ordinaryTheta F u q := by
    have hh : (q * p⁻¹)⁻¹ * q = p := by
      calc
        _ = (p⁻¹⁻¹ * q⁻¹) * q := congrArg (· * q) (mul_inv_rev q p⁻¹)
        _ = p * q⁻¹ * q := congrArg (fun k : Q F => k * q⁻¹ * q) (inv_inv p)
        _ = p := inv_mul_cancel_right p q
    simpa only [hh] using he (q * p⁻¹) q
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ u
  obtain ⟨C, hC, hb⟩ := (adelicTheta_decay F f 1).2
  have hz (q : Q F) : ordinaryTheta F (Submodule.Quotient.mk f) q = 0 := by
    have hlim : Tendsto (fun t : ℝ => C * (Real.exp t)⁻¹) atTop (𝓝 0) := by
      simpa only [Function.comp_def, mul_zero] using
        (tendsto_inv_atTop_zero.comp Real.tendsto_exp_atTop).const_mul C
    apply norm_eq_zero.mp
    apply le_antisymm _ (norm_nonneg _)
    apply ge_of_tendsto hlim
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    rw [hconst q (ray F t)]
    have hm : ideleClassNorm F (ray F t) = Real.exp t := ideleClassNorm_expSection F _
    have hge : 1 ≤ ideleClassNorm F (ray F t) := hm.symm ▸ Real.one_le_exp_iff.mpr ht
    have ht' := (hb (ray F t)).1 hge
    change ‖adelicTheta F (GlobalBruhat.algebraicEquiv F f).val (ray F t)‖ ≤ _
    simpa only [hm, pow_one] using ht'
  have hf : f ∈ (globalThetaOperator F).ker := LinearMap.mem_ker.mpr (funext hz)
  rw [show (Submodule.Quotient.mk f : GlobalThetaQuotient F) = 0 from
    (Submodule.Quotient.mk_eq_zero _).mpr hf, map_zero] at hu
  exact one_ne_zero (congrArg Prod.fst hu).symm

private theorem thetaEnergy_integrable (a b s : ℝ) (hs : 0 ≤ s) (u : GlobalPolarTheta F) :
    Integrable (fun q => ‖globalPolarThetaFunction F u q‖ ^ 2 *
      hardySobolevWeight a b s (logModulus F q)) μ := by
  have h := (memLp_two_iff_integrable_sq_norm
    (thetaSobolevProfile_continuous F 0 a b s u).aestronglyMeasurable).mp
    (thetaSobolevProfile_memLp F μ 0 a b s hs u)
  simpa only [thetaSobolevProfile_norm_sq, zero_add] using h

private theorem thetaEnergy_translate (a l r s : ℝ) (hs : 0 ≤ s) (u : GlobalPolarTheta F)
    (g : Q F) :
    let w (q : Q F) := ‖globalPolarThetaFunction F u q‖ ^ 2 *
      hardySobolevWeight (a+l) (a+r) s (logModulus F q + logModulus F g)
    Integrable w μ ∧ ‖globalThetaSobolevMap F μ a l r s hs (globalPolarThetaTranslate F g u)‖ ^ 2 =
      ∫ q, w q ∂μ := by
  let f (q : Q F) := ‖globalPolarThetaFunction F (globalPolarThetaTranslate F g u) q‖ ^ 2 *
    hardySobolevWeight (a+l) (a+r) s (logModulus F q)
  let e := (Homeomorph.mulLeft g).toMeasurableEquiv
  have hm : MeasurePreserving e μ μ := measurePreserving_mul_left μ g
  have he (q : Q F) : f (e q) = ‖globalPolarThetaFunction F u q‖ ^ 2 *
      hardySobolevWeight (a+l) (a+r) s (logModulus F q + logModulus F g) := by
    change ‖globalPolarThetaFunction F (globalPolarThetaTranslate F g u) (g * q)‖ ^ 2 *
      hardySobolevWeight (a+l) (a+r) s (logModulus F (g * q)) = _
    rw [globalPolarThetaFunction_translate, logModulus_mul, add_comm (logModulus F g)]
    exact congrArg (fun z : Q F => ‖globalPolarThetaFunction F u z‖ ^ 2 *
      hardySobolevWeight (a+l) (a+r) s (logModulus F q + logModulus F g)) (inv_mul_cancel_left g q)
  have hi := hm.integrable_comp_of_integrable (thetaEnergy_integrable F μ (a+l) (a+r) s hs
    (globalPolarThetaTranslate F g u))
  refine ⟨hi.congr (Eventually.of_forall he), ?_⟩
  rw [globalThetaSobolevMap_norm_sq]
  change (∫ q, f q ∂μ) = _
  rw [← hm.integral_comp' f]
  exact integral_congr_ae (Eventually.of_forall he)

private theorem thetaEnergy_positive_strip (u : GlobalPolarTheta F) (q₀ : Q F)
    (hu : globalPolarThetaFunction F u q₀ ≠ 0) :
    ∃ R > 0, 0 < ∫ q in {q : Q F | |logModulus F q| < R},
      ‖globalPolarThetaFunction F u q‖ ^ 2 ∂μ := by
  let R := |logModulus F q₀| + 1
  let D : Set (Q F) := {q | |logModulus F q| < R}
  let p (q : Q F) : ℝ := ‖globalPolarThetaFunction F u q‖ ^ 2
  have hp : Integrable p μ := by
    simpa [p, hardySobolevWeight] using thetaEnergy_integrable F μ 0 0 0 le_rfl u
  have hcont : Continuous p := by
    obtain ⟨f, rfl⟩ := (polarThetaMk_isOpenQuotientMap F).surjective u
    exact ((adelicTheta_continuous F
      (bruhat_theta_continuous_and_invariant (GlobalBruhat.algebraicEquiv F f.val).property).1).norm).pow 2
  have hlog : Continuous (logModulus F) := ideleClassLogNorm_continuous F
  have hD : IsOpen D := isOpen_lt hlog.abs continuous_const
  have hB : IsOpen (D ∩ {q | 0 < p q}) := hD.inter (isOpen_lt continuous_const hcont)
  have hq : q₀ ∈ D ∩ {q | 0 < p q} :=
    ⟨by change |logModulus F q₀| < R; dsimp [R]; linarith,
      pow_pos (norm_pos_iff.mpr hu) _⟩
  refine ⟨R, by dsimp [R]; positivity, ?_⟩
  apply (integral_pos_iff_support_of_nonneg (fun q => sq_nonneg _) hp.integrableOn).mpr
  have he := hB.measure_pos μ ⟨q₀, hq⟩
  have hsub : D ∩ {q | 0 < p q} ⊆ Function.support p :=
    fun q hq => hq.2.ne'
  apply he.trans_le
  calc
    μ (D ∩ {q | 0 < p q}) = (μ.restrict D) (D ∩ {q | 0 < p q}) := by
      rw [Measure.restrict_apply hB.measurableSet, inter_eq_left.mpr inter_subset_left]
    _ ≤ (μ.restrict D) (Function.support p) := measure_mono hsub

private theorem translatedTheta_norm_upper (a α s : ℝ) (hα : 0 ≤ α) (hs : 0 ≤ s)
    (u : GlobalPolarTheta F) (t : ℝ) (ht : 0 ≤ t) :
    ‖globalThetaSobolevMap F μ a (-α) α s hs (globalPolarThetaTranslate F (ray F t) u)‖ ^ 2 ≤
      ((2 : ℝ) ^ (s / 2) * ‖globalThetaSobolevMap F μ a (-α) α s hs u‖ ^ 2) *
        ((1 + t ^ 2) ^ (s / 2) * Real.exp (2 * (a + α) * t)) := by
  obtain ⟨hi, he⟩ := thetaEnergy_translate F μ a (-α) α s hs u (ray F t)
  dsimp only at hi he
  rw [logModulus_ray] at hi he
  let C := (2 : ℝ) ^ (s / 2) * hardySobolevWeight (a + -α) (a + α) s t
  have hfixed := thetaEnergy_integrable F μ (a + -α) (a + α) s hs u
  rw [he]
  calc
    _ ≤ ∫ q, C * (‖globalPolarThetaFunction F u q‖ ^ 2 *
        hardySobolevWeight (a + -α) (a + α) s (logModulus F q)) ∂μ := by
      apply integral_mono hi (hfixed.const_mul C)
      intro q
      calc
        _ ≤ ‖globalPolarThetaFunction F u q‖ ^ 2 *
            (hardySobolevWeight (a + -α) (a + α) s (logModulus F q) * C) := by
          apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
          simpa only [C, mul_assoc] using
            hardySobolevWeight_add_le (a + -α) (a + α) hs (logModulus F q) t
        _ = _ := by ring
    _ = _ := by
      rw [integral_const_mul, ← globalThetaSobolevMap_norm_sq F μ a (-α) α s hs u]
      dsimp only [C, hardySobolevWeight]
      rw [max_eq_right (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by linarith) ht))]
      ring

private theorem translatedTheta_norm_lower (b α s : ℝ) (hs : 0 ≤ s)
    (u : GlobalPolarTheta F) (R t : ℝ) :
    let D := {q : Q F | |logModulus F q| < R}
    let m := (∫ q in D, ‖globalPolarThetaFunction F u q‖ ^ 2 ∂μ)
    (m * Real.exp (-(2 * |b + α| * R))) * Real.exp (2 * (b + α) * t) ≤
      ‖globalThetaSobolevMap F μ b (-α) α s hs (globalPolarThetaTranslate F (ray F t) u)‖ ^ 2 := by
  intro D m
  let c := Real.exp (-(2 * |b + α| * R)) * Real.exp (2 * (b + α) * t)
  have hlog : Continuous (logModulus F) := ideleClassLogNorm_continuous F
  have hD : MeasurableSet D := (isOpen_lt hlog.abs (continuous_const (y := R))).measurableSet
  have hp : Integrable (fun q => ‖globalPolarThetaFunction F u q‖ ^ 2) μ := by
    simpa [hardySobolevWeight] using thetaEnergy_integrable F μ 0 0 0 le_rfl u
  obtain ⟨hi, he⟩ := thetaEnergy_translate F μ b (-α) α s hs u (ray F t)
  dsimp only at hi he
  rw [logModulus_ray] at hi he
  rw [he]
  calc
    _ = c * m := by dsimp only [c]; ring
    _ = ∫ q, D.indicator (fun q => c * ‖globalPolarThetaFunction F u q‖ ^ 2) q ∂μ := by
      rw [integral_indicator hD, integral_const_mul]
    _ ≤ _ := by
      apply integral_mono ((hp.const_mul c).indicator hD) hi
      intro q
      by_cases hq : q ∈ D
      · rw [indicator_of_mem hq, mul_comm c]
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        have hq' : |logModulus F q| < R := hq
        have hneg : -(2 * |b + α| * R) ≤ 2 * (b + α) * logModulus F q := by
          have hh := mul_le_mul_of_nonneg_left hq'.le (by positivity : 0 ≤ 2 * |b + α|)
          have ha := neg_abs_le (2 * (b + α) * logModulus F q)
          rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at ha
          linarith
        dsimp only [c]
        rw [← Real.exp_add]
        unfold hardySobolevWeight
        have hexp : Real.exp (-(2 * |b + α| * R) + 2 * (b + α) * t) ≤
            Real.exp (2 * (b + α) * (logModulus F q + t)) :=
          Real.exp_le_exp.mpr (by linarith [mul_add (2 * (b + α)) (logModulus F q) t])
        exact (hexp.trans (le_max_right _ _)).trans
          (le_mul_of_one_le_right (by positivity)
            (Real.one_le_rpow (le_add_of_nonneg_right (sq_nonneg _)) (by positivity)))
      · rw [indicator_of_notMem hq]
        exact mul_nonneg (sq_nonneg _) (hardySobolevWeight_nonneg ..)

/-- Domination between the genuine theta norms forces the upper endpoint of
the shifted interval to be ordered. The test translates detect the exponential
difference at large positive modulus. -/
theorem globalThetaSobolev_norm_domination_upper (a b α s : ℝ) (hα : 0 ≤ α) (hs : 0 ≤ s)
    (C : ℝ)
    (h : ∀ u : GlobalPolarTheta F, ‖globalThetaSobolevMap F μ b (-α) α s hs u‖ ≤
      C * ‖globalThetaSobolevMap F μ a (-α) α s hs u‖) : b ≤ a := by
  by_contra! hab
  obtain ⟨u, q₀, hu⟩ := exists_globalPolarTheta_eval_ne_zero F
  obtain ⟨R, hR, hmass⟩ := thetaEnergy_positive_strip F μ u q₀ hu
  let m := (∫ q in {q : Q F | |logModulus F q| < R},
    ‖globalPolarThetaFunction F u q‖ ^ 2 ∂μ) * Real.exp (-(2 * |b + α| * R))
  let N := C ^ 2 * ((2 : ℝ) ^ (s / 2) * ‖globalThetaSobolevMap F μ a (-α) α s hs u‖ ^ 2)
  let δ := 2 * (b - a)
  have hm : 0 < m := mul_pos hmass (Real.exp_pos _)
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hb (t : ℝ) (ht : 0 ≤ t) :
      m ≤ N * (1 + t ^ 2) ^ (s / 2) * Real.exp (-δ * t) := by
    let v := globalPolarThetaTranslate F (ray F t) u
    have hlo := translatedTheta_norm_lower F μ b α s hs u R t
    have hup := translatedTheta_norm_upper F μ a α s hα hs u t ht
    have hnorm := pow_le_pow_left₀ (norm_nonneg _) (h v) 2
    rw [mul_pow] at hnorm
    have hc := hlo.trans (hnorm.trans (mul_le_mul_of_nonneg_left hup (sq_nonneg C)))
    change m * Real.exp (2 * (b + α) * t) ≤ _ at hc
    have hp := mul_le_mul_of_nonneg_right hc (Real.exp_pos (-(2 * (b + α) * t))).le
    calc
      m = (m * Real.exp (2 * (b + α) * t)) * Real.exp (-(2 * (b + α) * t)) := by
        rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
      _ ≤ _ := hp
      _ = _ := by
        dsimp only [N]
        calc
          _ = (C ^ 2 * ((2 : ℝ) ^ (s / 2) *
                ‖globalThetaSobolevMap F μ a (-α) α s hs u‖ ^ 2)) *
              (1 + t ^ 2) ^ (s / 2) *
              (Real.exp (2 * (a + α) * t) * Real.exp (-(2 * (b + α) * t))) := by ring
          _ = _ := by rw [← Real.exp_add]; congr 2; dsimp [δ]; ring
  have hlim : Tendsto (fun t : ℝ => (N * (2 : ℝ) ^ (s/2)) *
      (t ^ s * Real.exp (-δ * t))) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero s δ hδ).const_mul (N * (2 : ℝ) ^ (s/2))
  have hzero : m ≤ 0 := by
    apply ge_of_tendsto hlim
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    have ht₀ : 0 ≤ t := zero_le_one.trans ht
    have hbase : 1 + t ^ 2 ≤ 2 * t ^ 2 := by nlinarith
    have hpoly := Real.rpow_le_rpow (by positivity : 0 ≤ 1 + t ^ 2) hbase
      (by positivity : 0 ≤ s / 2)
    rw [Real.mul_rpow (by norm_num : 0 ≤ (2 : ℝ)) (sq_nonneg t),
      ← Real.rpow_natCast t 2, ← Real.rpow_mul ht₀] at hpoly
    have he : (↑(2 : ℕ) : ℝ) * (s / 2) = s := by push_cast; ring
    rw [he, Real.rpow_natCast] at hpoly
    calc
      m ≤ _ := hb t ht₀
      _ ≤ (N * ((2 : ℝ) ^ (s/2) * t ^ s)) * Real.exp (-δ * t) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpoly hN) (Real.exp_nonneg _)
      _ = _ := by ring
  exact hm.not_ge hzero

/-- The dense map from polar-free theta functions into their Hilbert closure. -/
def globalThetaSobolevDenseMap (a l r s : ℝ) (hs : 0 ≤ s) :
    GlobalPolarTheta F →L[ℂ] globalThetaSobolevCompletion F μ a l r s hs :=
  (globalThetaSobolevMap F μ a l r s hs).codRestrict _
    (fun u => subset_closure ⟨u, rfl⟩)

theorem globalThetaSobolevFourierEquiv_commutes (a l r s : ℝ) (hs : 0 ≤ s)
    (u : GlobalPolarTheta F) :
    globalThetaSobolevFourierEquiv F μ a l r s hs (globalThetaSobolevDenseMap F μ a l r s hs u) =
      globalThetaSobolevDenseMap F μ (1-a) (-r) (-l) s hs (globalPolarThetaFourier F u) :=
  Subtype.ext (globalThetaSobolevReflection_fourier F μ a l r s hs u)

theorem globalThetaSobolev_fourier_bound_iff (a α s : ℝ) (hα : 0 ≤ α) (hs : 0 ≤ s) :
    (∃ C ≥ 0, ∀ u : GlobalPolarTheta F,
      ‖globalThetaSobolevMap F μ a (-α) α s hs (globalPolarThetaFourier F u)‖ ≤
        C * ‖globalThetaSobolevMap F μ a (-α) α s hs u‖) ↔ a = 1/2 := by
  have hnorm (u : GlobalPolarTheta F) :
      ‖globalThetaSobolevMap F μ a (-α) α s hs (globalPolarThetaFourier F u)‖ =
        ‖globalThetaSobolevMap F μ (1-a) (-α) α s hs u‖ := by
    have h := globalThetaSobolevReflection_fourier F μ (1-a) (-α) α s hs u
    simpa only [sub_sub_cancel, neg_neg, (globalThetaSobolevReflection F μ).norm_map] using
      (congrArg norm h).symm
  constructor
  · rintro ⟨C, _, h⟩
    have hforward (u : GlobalPolarTheta F) := hnorm u ▸ h u
    have hreverse (u : GlobalPolarTheta F) :
        ‖globalThetaSobolevMap F μ a (-α) α s hs u‖ ≤
          C * ‖globalThetaSobolevMap F μ (1-a) (-α) α s hs u‖ := by
      simpa only [globalPolarThetaFourier_involutive F u, hnorm u] using h (globalPolarThetaFourier F u)
    have h₁ := globalThetaSobolev_norm_domination_upper F μ a (1-a) α s hα hs C hforward
    have h₂ := globalThetaSobolev_norm_domination_upper F μ (1-a) a α s hα hs C hreverse
    linarith
  · intro ha
    have he : 1 - a = a := by linarith
    refine ⟨1, zero_le_one, fun u => ?_⟩
    rw [hnorm, he, one_mul]

private theorem globalThetaSobolevReflection_mapsTo_symmetric (a α s : ℝ) (ha : a = 1/2)
    (hs : 0 ≤ s) :
    MapsTo (globalThetaSobolevReflection F μ)
      (globalThetaSobolevCompletion F μ a (-α) α s hs)
      (globalThetaSobolevCompletion F μ a (-α) α s hs) := by
  have he : 1-a = a := by linarith
  simpa only [he, neg_neg] using globalThetaSobolevReflection_mapsTo F μ a (-α) α s hs

/-- At the central line inversion gives an isometric automorphism on a symmetric interval. -/
def globalThetaSobolevFourierSymmetric (a α s : ℝ) (ha : a = 1/2) (hs : 0 ≤ s) :
    globalThetaSobolevCompletion F μ a (-α) α s hs ≃ₗᵢ[ℂ]
      globalThetaSobolevCompletion F μ a (-α) α s hs where
  toFun u := ⟨globalThetaSobolevReflection F μ u.val,
    globalThetaSobolevReflection_mapsTo_symmetric F μ a α s ha hs u.property⟩
  invFun u := ⟨globalThetaSobolevReflection F μ u.val,
    globalThetaSobolevReflection_mapsTo_symmetric F μ a α s ha hs u.property⟩
  left_inv u := Subtype.ext (globalThetaSobolevReflection_involutive F μ u.val)
  right_inv u := Subtype.ext (globalThetaSobolevReflection_involutive F μ u.val)
  map_add' u v := Subtype.ext (map_add (globalThetaSobolevReflection F μ) u.val v.val)
  map_smul' c u := Subtype.ext (map_smul (globalThetaSobolevReflection F μ) c u.val)
  norm_map' u := (globalThetaSobolevReflection F μ).norm_map u.val

/-- On a symmetric interval Fourier has a unique continuous linear extension
as an automorphism of the actual theta completion exactly on the central line. -/
theorem globalThetaSobolev_fourier_extension_iff (a α s : ℝ) (hα : 0 ≤ α) (hs : 0 ≤ s) :
    (∃! L : globalThetaSobolevCompletion F μ a (-α) α s hs ≃L[ℂ]
        globalThetaSobolevCompletion F μ a (-α) α s hs,
      ∀ u : GlobalPolarTheta F,
        L (globalThetaSobolevDenseMap F μ a (-α) α s hs u) =
          globalThetaSobolevDenseMap F μ a (-α) α s hs (globalPolarThetaFourier F u)) ↔
      a = 1/2 := by
  let J := globalThetaSobolevDenseMap F μ a (-α) α s hs
  constructor
  · rintro ⟨L, hL, _⟩
    apply (globalThetaSobolev_fourier_bound_iff F μ a α s hα hs).mp
    let T := L.toContinuousLinearMap
    refine ⟨‖T‖, T.opNorm_nonneg, fun u => ?_⟩
    change ‖J (globalPolarThetaFourier F u)‖ ≤ ‖T‖ * ‖J u‖
    rw [← hL u]
    exact T.le_opNorm (J u)
  · intro ha
    let L := (globalThetaSobolevFourierSymmetric F μ a α s ha hs).toContinuousLinearEquiv
    have he : 1-a = a := by linarith
    have hL (u : GlobalPolarTheta F) : L (J u) = J (globalPolarThetaFourier F u) := by
      apply Subtype.ext
      change globalThetaSobolevReflection F μ (globalThetaSobolevMap F μ a (-α) α s hs u) =
        globalThetaSobolevMap F μ a (-α) α s hs (globalPolarThetaFourier F u)
      simpa only [he, neg_neg] using globalThetaSobolevReflection_fourier F μ a (-α) α s hs u
    refine ⟨L, hL, fun T hT => ?_⟩
    have hJ : DenseRange J := globalThetaSobolevCompletion_dense F μ a (-α) α s hs
    apply DFunLike.coe_injective
    exact hJ.equalizer T.continuous L.continuous (funext fun u => (hT u).trans (hL u).symm)

/-- Inversion conjugates the left-translation action to translation by the inverse,
with the amplitude taken at the reflected endpoints. -/
theorem globalThetaSobolevReflection_translate (l r s : ℝ) (hs : 0 ≤ s) (g : Q F)
    (f : Lp ℂ 2 μ) :
    globalThetaSobolevReflection F μ
        (hardySobolevMulTranslation μ (ideleClassLogNorm F) (ideleClassLogNorm_continuous F)
          l r s hs g f) =
      hardySobolevMulTranslation μ (ideleClassLogNorm F) (ideleClassLogNorm_continuous F)
        (-r) (-l) s hs g⁻¹ (globalThetaSobolevReflection F μ f) := by
  let T := hardySobolevMulTranslation μ (ideleClassLogNorm F)
    (ideleClassLogNorm_continuous F) l r s hs
  let U := hardySobolevMulTranslation μ (ideleClassLogNorm F)
    (ideleClassLogNorm_continuous F) (-r) (-l) s hs
  let J := globalThetaSobolevReflection F μ
  change J (T g f) = U g⁻¹ (J f)
  apply Lp.ext
  filter_upwards [globalThetaSobolevReflection_ae F μ (T g f),
    (ideleClassHaar_inv F μ).quasiMeasurePreserving.ae
      (hardySobolevMulTranslation_ae μ (ideleClassLogNorm F) (ideleClassLogNorm_continuous F)
        l r s hs g f),
    hardySobolevMulTranslation_ae μ (ideleClassLogNorm F) (ideleClassLogNorm_continuous F)
        (-r) (-l) s hs g⁻¹ (J f),
    (measurePreserving_mul_left μ (g⁻¹ : Q F)⁻¹).quasiMeasurePreserving.ae
      (globalThetaSobolevReflection_ae F μ f)] with q h₁ h₂ h₃ h₄
  rw [h₁, h₂, h₃, h₄]
  let p := (g⁻¹ : Q F)⁻¹ * q
  have hp : g⁻¹ * q⁻¹ = p⁻¹ := by
    have he : p = q * g := (congrArg (· * q) (inv_inv g)).trans (mul_comm g q)
    exact (mul_inv_rev q g).symm.trans (congrArg Inv.inv he.symm)
  have hA (x : Q F) : hardySobolevAmplitude l r s (logModulus F x⁻¹) =
      hardySobolevAmplitude (-r) (-l) s (logModulus F x) := by
    rw [logModulus_inv]
    exact congrArg Real.sqrt (hardySobolevWeight_reflect l r s _)
  change ((hardySobolevAmplitude l r s (logModulus F q⁻¹) /
      hardySobolevAmplitude l r s (logModulus F (g⁻¹ * q⁻¹)) : ℝ) : ℂ) * f (g⁻¹ * q⁻¹) =
    ((hardySobolevAmplitude (-r) (-l) s (logModulus F q) /
      hardySobolevAmplitude (-r) (-l) s (logModulus F p) : ℝ) : ℂ) * f p⁻¹
  rw [hp, hA, hA]

/-- The inversion isometry sends each norm-one character isotype to its inverse isotype. -/
theorem globalThetaSobolevFourierEquiv_isotype (a l r s : ℝ) (hs : 0 ≤ s)
    (ω : PontryaginDual (normOneIdeleClass F)) (u : globalThetaSobolevCompletion F μ a l r s hs)
    (hu : ∀ g : normOneIdeleClass F,
      hardySobolevMulTranslation μ (ideleClassLogNorm F) (ideleClassLogNorm_continuous F)
        l r s hs g.val u.val = ((ω g : Circle) : ℂ) • u.val) :
    ∀ g : normOneIdeleClass F,
      hardySobolevMulTranslation μ (ideleClassLogNorm F) (ideleClassLogNorm_continuous F)
        (-r) (-l) s hs g.val (globalThetaSobolevFourierEquiv F μ a l r s hs u).val =
      ((ω g⁻¹ : Circle) : ℂ) • (globalThetaSobolevFourierEquiv F μ a l r s hs u).val := by
  intro g
  have h := (globalThetaSobolevReflection_translate F μ l r s hs (g⁻¹).val u.val).symm
  rw [hu g⁻¹, map_smul] at h
  have hg : (g⁻¹ : normOneIdeleClass F).val⁻¹ = g.val := inv_inv g.val
  rwa [hg] at h

private abbrev globalAmplitude (l r s : ℝ) (q : Q F) :=
  hardySobolevAmplitude l r s (logModulus F q)

private theorem globalAmplitude_measurable (l r s : ℝ) : Measurable (globalAmplitude F l r s) :=
  ((Real.continuous_sqrt.comp (continuous_hardySobolevWeight l r s)).comp
    (ideleClassLogNorm_continuous F : Continuous (logModulus F))).measurable

/-- The weighted measure of the ambient space on the global idele classes. -/
def globalHardySobolevMeasure (l r s : ℝ) : Measure (Q F) :=
  amplitudeMeasure μ (globalAmplitude F l r s)

omit [μ.IsHaarMeasure] in
theorem globalHardySobolevMeasure_eq_withDensity (l r s : ℝ) :
    globalHardySobolevMeasure F μ l r s =
      μ.withDensity (fun q => ENNReal.ofReal (hardySobolevWeight l r s (logModulus F q))) := by
  unfold globalHardySobolevMeasure amplitudeMeasure
  congr 1
  funext q
  exact congrArg ENNReal.ofReal (Real.sq_sqrt (hardySobolevWeight_nonneg ..))

/-- Inversion takes the reflected Sobolev measure to the initial one. -/
theorem globalHardySobolevMeasure_inv (l r s : ℝ) :
    MeasurePreserving (Inv.inv : Q F → Q F) (globalHardySobolevMeasure F μ (-r) (-l) s)
      (globalHardySobolevMeasure F μ l r s) := by
  let w (a b : ℝ) (q : Q F) := ENNReal.ofReal (hardySobolevWeight a b s (logModulus F q))
  let h := ideleClassHaar_inv F μ
  have hw : Measurable (w l r) :=
    ((continuous_hardySobolevWeight l r s).comp
      (ideleClassLogNorm_continuous F : Continuous (logModulus F))).measurable.ennreal_ofReal
  have hreflect (q : Q F) : w l r q⁻¹ = w (-r) (-l) q := by
    change ENNReal.ofReal (hardySobolevWeight l r s (logModulus F q⁻¹)) =
      ENNReal.ofReal (hardySobolevWeight (-r) (-l) s (logModulus F q))
    rw [logModulus_inv, hardySobolevWeight_reflect]
  refine ⟨h.measurable, ?_⟩
  rw [globalHardySobolevMeasure_eq_withDensity, globalHardySobolevMeasure_eq_withDensity]
  ext U hU
  change (Measure.map Inv.inv (μ.withDensity (w (-r) (-l)))) U = (μ.withDensity (w l r)) U
  rw [Measure.map_apply h.measurable hU, withDensity_apply _ (h.measurable hU), withDensity_apply _ hU]
  rw [← lintegral_congr hreflect (μ := μ.restrict (Inv.inv ⁻¹' U))]
  rw [← setLIntegral_map hU hw h.measurable, h.map_eq]

/-- Amplitude multiplication is an isometric coordinate map on the actual weighted space. -/
def globalHardySobolevIso (l r s : ℝ) :
    Lp ℂ 2 (globalHardySobolevMeasure F μ l r s) ≃ₗᵢ[ℂ] Lp ℂ 2 μ :=
  amplitudeL2Iso μ (globalAmplitude F l r s) (globalAmplitude_measurable F l r s)
    (fun q => amplitude_pos l r s (logModulus F q))

/-- In amplitude coordinates the actual weighted pullback agrees with the
Haar pullback used on the theta closures. -/
theorem globalThetaSobolevReflection_eq_weighted_pullback (l r s : ℝ)
    (f : Lp ℂ 2 (globalHardySobolevMeasure F μ l r s)) :
    globalThetaSobolevReflection F μ (globalHardySobolevIso F μ l r s f) =
      globalHardySobolevIso F μ (-r) (-l) s
        (Lp.compMeasurePreserving Inv.inv (globalHardySobolevMeasure_inv F μ l r s) f) := by
  let h := globalHardySobolevMeasure_inv F μ l r s
  let g := Lp.compMeasurePreserving Inv.inv h f
  let A := globalAmplitude F l r s
  let B := globalAmplitude F (-r) (-l) s
  apply Lp.ext
  filter_upwards [globalThetaSobolevReflection_ae F μ (globalHardySobolevIso F μ l r s f),
    (ideleClassHaar_inv F μ).quasiMeasurePreserving.ae
      (amplitudeL2Iso_ae μ A (globalAmplitude_measurable F l r s)
        (fun q => amplitude_pos l r s (logModulus F q)) f),
    amplitudeL2Iso_ae μ B (globalAmplitude_measurable F (-r) (-l) s)
      (fun q => amplitude_pos (-r) (-l) s (logModulus F q)) g,
    (absolutelyContinuous_amplitudeMeasure μ B (globalAmplitude_measurable F (-r) (-l) s)
      (fun q => amplitude_pos (-r) (-l) s (logModulus F q))).ae_le
      (Lp.coeFn_compMeasurePreserving f h)] with q h₁ h₂ h₃ h₄
  have hg : (g : Q F → ℂ) q = (f : Q F → ℂ) q⁻¹ := h₄
  have hab : A q⁻¹ = B q := by
    change hardySobolevAmplitude l r s (logModulus F q⁻¹) = B q
    rw [logModulus_inv]
    exact congrArg Real.sqrt (hardySobolevWeight_reflect l r s _)
  exact h₁.trans (h₂.trans ((congrArg₂ (fun (r : ℝ) (z : ℂ) => r • z) hab hg.symm).trans h₃.symm))

end

end Masullo
