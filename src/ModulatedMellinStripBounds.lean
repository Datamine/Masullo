import BruhatSobolevConvolution
import ModulatedDecayIsotypes
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open Filter Function MeasureTheory Set Topology
open scoped ENNReal NNReal

namespace Masullo

noncomputable section

set_option maxHeartbeats 1200000

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
  (m : G →ₜ* Multiplicative ℝ)

private theorem bruhatSchwartz_integrable (hm : IsProperMap m) (hms : Surjective m)
    (f : BruhatSchwartz G) : Integrable f.val μ := by
  apply (integrable_norm_iff (bruhatSchwartz_continuous f).aestronglyMeasurable).mp
  simpa [singletonSobolevKernelWeight] using
    bruhatSchwartz_integrable_SobolevKernelWeight μ m hm hms 0 le_rfl f

private def bruhatL1Seminorm (hm : IsProperMap m) (hms : Surjective m) :
    Seminorm ℂ (BruhatSchwartz G) :=
  let hI := bruhatSchwartz_integrable μ m hm hms
  Seminorm.ofSMulLE (fun f ↦ ∫ g, ‖f.val g‖ ∂μ) (by simp)
    (fun f k ↦ by
      change (∫ g, ‖f.val g + k.val g‖ ∂μ) ≤ _
      rw [← integral_add (hI f).norm (hI k).norm]
      exact integral_mono (hI (f + k)).norm ((hI f).norm.add (hI k).norm)
        (fun _ ↦ norm_add_le _ _))
    (fun z f ↦ by
      change (∫ g, ‖z • f.val g‖ ∂μ) ≤ _
      simp_rw [norm_smul, integral_const_mul]
      rfl)

private theorem bruhatL1Seminorm_continuous (hm : IsProperMap m) (hms : Surjective m) :
    Continuous (bruhatL1Seminorm μ m hm hms) := by
  apply locallyConvexFinal_seminorm_continuous (fun P : BruhatSchwartzStage G ↦ P.inclusion)
  intro P
  obtain ⟨q, hq, hbound⟩ := exists_bruhatStage_SobolevKernel_seminorm μ m hm hms 0 le_rfl P
  apply Seminorm.continuous_of_le (q := q) hq
  intro f
  change (∫ g, ‖P.realize f g‖ ∂μ) ≤ q f
  simpa [singletonSobolevKernelWeight] using (hbound f).2

omit [T2Space G] in
private theorem orbitIntegral_derivative_zero (c : Multiplicative ℝ →ₜ* G)
    {H K : G → ℂ} (hH : Integrable H μ) (hK : Integrable K μ) (hKc : Continuous K)
    (hD : ∀ x t, HasDerivAt (fun u : ℝ ↦ H (x * c (Multiplicative.ofAdd u)))
      (K (x * c (Multiplicative.ofAdd t))) t) :
    (∫ x, K x ∂μ) = 0 := by
  let ν := (volume : Measure ℝ).restrict (Ioc 0 1)
  have hν : ν.real univ = 1 := by simp [ν, measureReal_def, Real.volume_Ioc]
  let k (p : ℝ × G) := K (p.2 * c (Multiplicative.ofAdd p.1))
  have hkc : Continuous k := hKc.comp (continuous_snd.mul
    (c.continuous.comp (continuous_ofAdd.comp continuous_fst)))
  have hki : Integrable k (ν.prod μ) := by
    apply (integrable_prod_iff hkc.aestronglyMeasurable).mpr
    refine ⟨.of_forall fun t ↦ ?_, ?_⟩
    · exact (measurePreserving_mul_right μ (c (Multiplicative.ofAdd t))).integrable_comp_of_integrable hK
    · simp only [k, integral_mul_right_eq_self (fun x ↦ ‖K x‖)]
      exact integrable_const _
  have hzero (x : G) :
      (∫ t, k (t, x) ∂ν) = H (x * c (Multiplicative.ofAdd (1 : ℝ))) - H x := by
    change (∫ t in Ioc 0 1, K (x * c (Multiplicative.ofAdd t))) = _
    rw [← intervalIntegral.integral_of_le zero_le_one,
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ hD x t)]
    · rw [show c (Multiplicative.ofAdd (0 : ℝ)) = 1 from map_one c, mul_one]
    · exact (hKc.comp (continuous_const.mul (c.continuous.comp continuous_ofAdd))).intervalIntegrable ..
  calc
    (∫ x, K x ∂μ) = ∫ t, (∫ x, k (t, x) ∂μ) ∂ν := by
      simp only [k, integral_mul_right_eq_self, integral_const, hν, one_smul]
    _ = ∫ x, (∫ t, k (t, x) ∂ν) ∂μ := (integral_integral_swap hki)
    _ = 0 := by
      simp_rw [hzero]
      have hcomp : Integrable (fun x ↦ H (x * c (Multiplicative.ofAdd (1 : ℝ)))) μ :=
        (measurePreserving_mul_right μ _).integrable_comp_of_integrable hH
      rw [integral_sub hcomp hH, integral_mul_right_eq_self, sub_self]

private theorem orbit_hasDerivAt (c : Multiplicative ℝ →ₜ* G)
    {f : G → ℂ} (hf : IsBruhatContDiff 1 f) (x : G) (t : ℝ) :
    HasDerivAt (fun u : ℝ ↦ f (x * c (Multiplicative.ofAdd u)))
      (bruhatOrbitDeriv c f (x * c (Multiplicative.ofAdd t))) t := by
  have h := (bruhatOrbitDeriv_regular c f (s := 0) hf).2 (x * c (Multiplicative.ofAdd t))
  have hshift : HasDerivAt (fun u : ℝ ↦ u - t) 1 t := (hasDerivAt_id t).sub_const _
  let v (u : ℝ) := f (x * c (Multiplicative.ofAdd t) * c (Multiplicative.ofAdd u))
  have he : v ∘ (fun u : ℝ ↦ u - t) = fun u ↦ f (x * c (Multiplicative.ofAdd u)) := by
    funext u
    change f (x * c (Multiplicative.ofAdd t) * c (Multiplicative.ofAdd (u - t))) =
      f (x * c (Multiplicative.ofAdd u))
    rw [mul_assoc, ← map_mul]
    exact congrArg (fun y : ℝ ↦ f (x * c (Multiplicative.ofAdd y))) (by change t + (u - t) = u; ring)
  have hcomp : HasDerivAt (v ∘ fun u : ℝ ↦ u - t)
      ((1 : ℝ) • bruhatOrbitDeriv c f (x * c (Multiplicative.ofAdd t))) t :=
    h.scomp_of_eq t (h := fun u : ℝ ↦ u - t) hshift (by simp)
  simpa only [he, one_smul] using hcomp

private def unitaryOrbitSlope (c : Multiplicative ℝ →ₜ* G) (χ : PontryaginDual G) : ℂ :=
  bruhatOrbitDeriv c (fun x ↦ (χ x : ℂ)) 1

private theorem character_orbit_hasDerivAt (c : Multiplicative ℝ →ₜ* G) (χ : PontryaginDual G)
    (x : G) (t : ℝ) :
    HasDerivAt (fun u : ℝ ↦ (χ (x * c (Multiplicative.ofAdd u)) : ℂ))
      (unitaryOrbitSlope c χ * (χ (x * c (Multiplicative.ofAdd t)) : ℂ)) t := by
  have hf : IsBruhatContDiff 1 (fun x ↦ (χ x : ℂ)) := pontryaginDual_mem_bruhatSmooth χ 1
  have hz := (bruhatOrbitDeriv_regular c _ (s := 0) hf).2 (1 : G)
  have he (y : G) : bruhatOrbitDeriv c (fun x ↦ (χ x : ℂ)) y =
      unitaryOrbitSlope c χ * (χ y : ℂ) := by
    have h := hz.const_mul (χ y : ℂ)
    simp only [one_mul] at h
    have h' : HasDerivAt (fun u : ℝ ↦ (χ (y * c (Multiplicative.ofAdd u)) : ℂ))
        (unitaryOrbitSlope c χ * (χ y : ℂ)) 0 := by
      simpa only [map_mul, Circle.coe_mul, unitaryOrbitSlope, mul_comm] using h
    exact h'.deriv
  simpa only [he] using orbit_hasDerivAt c hf x t

private theorem integral_derivative_mul_character (hm : IsProperMap m) (hms : Surjective m)
    (c : Multiplicative ℝ →ₜ* G) (χ : PontryaginDual G) (f : BruhatSchwartz G) :
    (∫ x, (bruhatSchwartz_derivative c f).val x * (χ x : ℂ) ∂μ) =
      -unitaryOrbitSlope c χ * (∫ x, f.val x * (χ x : ℂ) ∂μ) := by
  let D := bruhatSchwartz_derivative c f
  let v (x : G) : ℂ := χ x
  have hvc : Continuous v := continuous_subtype_val.comp χ.continuous
  have hInt (g : BruhatSchwartz G) : Integrable (fun x ↦ g.val x * v x) μ := by
    let hi := bruhatSchwartz_integrable μ m hm hms g
    refine hi.norm.mono' ((bruhatSchwartz_continuous g).mul hvc).aestronglyMeasurable ?_
    exact .of_forall fun x ↦ by rw [norm_mul, show ‖v x‖ = 1 from Circle.norm_coe (χ x), mul_one]
  have h :=
    orbitIntegral_derivative_zero μ c (hInt f)
      ((hInt D).add ((hInt f).const_mul (unitaryOrbitSlope c χ)))
      (((bruhatSchwartz_continuous D).mul hvc).add
        (continuous_const.mul ((bruhatSchwartz_continuous f).mul hvc))) (fun x t ↦ by
      have ht := (orbit_hasDerivAt c (bruhatSchwartz_le_smooth f.property 1) x t).mul
        (character_orbit_hasDerivAt c χ x t)
      have he (y : G) : bruhatOrbitDeriv c f.val y * v y +
          f.val y * (unitaryOrbitSlope c χ * v y) =
          D.val y * v y + unitaryOrbitSlope c χ * (f.val y * v y) := by
        change _ = bruhatOrbitDeriv c f.val y * v y + _
        ring
      exact ht.congr_deriv (he _))
  have he : (∫ x, D.val x * v x ∂μ) +
      unitaryOrbitSlope c χ * (∫ x, f.val x * v x ∂μ) = 0 := by
    rw [← integral_const_mul, ← integral_add (hInt D) ((hInt f).const_mul _)]
    exact h
  change (∫ x, D.val x * v x ∂μ) = _
  linear_combination he

private def logSlope (c : Multiplicative ℝ →ₜ* G) : ℝ :=
  modulatedLog m (c (Multiplicative.ofAdd (1 : ℝ)))

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] in
private theorem modulatedLog_orbit (c : Multiplicative ℝ →ₜ* G) (x : G) (t : ℝ) :
    modulatedLog m (x * c (Multiplicative.ofAdd t)) =
      modulatedLog m x + logSlope m c * t := by
  let L : ℝ →+ ℝ :=
    { toFun := fun t ↦ modulatedLog m (c (Multiplicative.ofAdd t))
      map_zero' := congrArg Multiplicative.toAdd ((m.comp c).map_one)
      map_add' := fun t u ↦ congrArg Multiplicative.toAdd
        ((m.comp c).map_mul (Multiplicative.ofAdd t) (Multiplicative.ofAdd u)) }
  have hLc : Continuous L := continuous_toAdd.comp
    (m.continuous.comp (c.continuous.comp continuous_ofAdd))
  have h := map_real_smul L hLc t (1 : ℝ)
  have ht : L t = t * L 1 := by simpa only [smul_eq_mul, mul_one] using h
  unfold modulatedLog
  rw [map_mul]
  change modulatedLog m x + L t = modulatedLog m x + logSlope m c * t
  rw [ht, mul_comm t]
  rfl

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] in
private theorem logWeight_orbit_hasDerivAt (c : Multiplicative ℝ →ₜ* G)
    (a : ℝ) (x : G) (t : ℝ) :
    HasDerivAt (fun u : ℝ ↦ Real.exp (a * modulatedLog m (x * c (Multiplicative.ofAdd u))))
      ((a * logSlope m c) * Real.exp (a * modulatedLog m (x * c (Multiplicative.ofAdd t)))) t := by
  simp only [modulatedLog_orbit]
  have h := ((hasDerivAt_id t).const_mul (logSlope m c)).const_add (modulatedLog m x)
  have he := (h.const_mul a).exp
  simpa only [id_eq, mul_one, mul_comm (Real.exp _)] using he

private abbrev shiftAdjointDerivative (a : ℝ) (c : Multiplicative ℝ →ₜ* G) :
    BruhatSchwartz G →L[ℂ] BruhatSchwartz G :=
  ((a * logSlope m c : ℝ) : ℂ) • ContinuousLinearMap.id ℂ _ - bruhatSchwartz_derivative c

local instance : ContinuousSMul ℂ (BruhatSchwartz G) :=
  (PolynormableSpace.withSeminorms ℂ (BruhatSchwartz G)).continuousSMul

private theorem weightedAdjointDerivative (a : ℝ) (c : Multiplicative ℝ →ₜ* G)
    (f : BruhatSchwartz G) (u : G → ℂ)
    (h : modulatedExponentialWeight m a u = f.val) :
    modulatedExponentialWeight m a (fun x ↦ -bruhatOrbitDeriv c u x) =
      (shiftAdjointDerivative m a c f).val := by
  have hu : u = modulatedExponentialWeight m (-a) f.val := by
    rw [← h, modulatedExponentialWeight_add, neg_add_cancel]
    funext x
    simp [modulatedExponentialWeight_apply]
  funext x
  rw [modulatedExponentialWeight_apply, hu]
  have hd := (logWeight_orbit_hasDerivAt m c (-a) x 0).ofReal_comp
  have hf := (bruhatOrbitDeriv_regular c _ (s := 0) (bruhatSchwartz_le_smooth f.property 1)).2 x
  have hp := hd.mul hf
  have hz : x * c (Multiplicative.ofAdd (0 : ℝ)) = x := by
    rw [show c (Multiplicative.ofAdd (0 : ℝ)) = 1 from map_one c, mul_one]
  simp only [hz] at hp
  unfold bruhatOrbitDeriv
  erw [hp.deriv]
  change Real.exp (a * modulatedLog m x) •
    -(((↑(-a * logSlope m c * Real.exp (-a * modulatedLog m x)) : ℂ) * f.val x) +
      (↑(Real.exp (-a * modulatedLog m x)) : ℂ) * (bruhatSchwartz_derivative c f).val x) =
    ((↑(a * logSlope m c) : ℂ) * f.val x) - (bruhatSchwartz_derivative c f).val x
  have hh : ((↑(Real.exp (a * modulatedLog m x)) : ℂ)) *
      (↑(Real.exp (-a * modulatedLog m x)) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.exp_add, neg_mul, add_neg_cancel, Real.exp_zero, Complex.ofReal_one]
  simp only [Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_neg]
  linear_combination
    (f.val x * (a : ℂ) * (logSlope m c : ℂ) - (bruhatSchwartz_derivative c f).val x) * hh

private def adjointDerivativeWord : List (Multiplicative ℝ →ₜ* G) → (G → ℂ) → G → ℂ :=
  fun cs u ↦ cs.foldr (fun c f x ↦ -bruhatOrbitDeriv c f x) u

private def shiftedAdjointWord (a : ℝ) (cs : List (Multiplicative ℝ →ₜ* G)) :
    BruhatSchwartz G →L[ℂ] BruhatSchwartz G :=
  cs.foldr (fun c F ↦ (shiftAdjointDerivative m a c).comp F) (ContinuousLinearMap.id ℂ _)

private theorem weightedAdjointWord (a : ℝ) (cs : List (Multiplicative ℝ →ₜ* G))
    (f : BruhatSchwartz G) (u : G → ℂ) (h : modulatedExponentialWeight m a u = f.val) :
    modulatedExponentialWeight m a (adjointDerivativeWord cs u) = (shiftedAdjointWord m a cs f).val := by
  induction cs with
  | nil => exact h
  | cons c cs ih => exact weightedAdjointDerivative m a c _ _ ih

/-- The symbol of one direction on the abscissa twist of a unitary character. -/
def mellinOrbitSlope (a : ℝ) (χ : PontryaginDual G) (c : Multiplicative ℝ →ₜ* G) : ℂ :=
  (a * logSlope m c : ℝ) + unitaryOrbitSlope c χ

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] in
/-- An exponential formula for the twisted character along a flow determines its Mellin symbol. -/
theorem mellinOrbitSlope_eq_of_orbit_exp (a : ℝ) (χ : PontryaginDual G)
    (c : Multiplicative ℝ →ₜ* G) (b : ℂ)
    (h : ∀ x : ℝ, (χ (c (Multiplicative.ofAdd x)) : ℂ) *
      Complex.exp ((a : ℂ) * (modulatedLog m (c (Multiplicative.ofAdd x)) : ℂ)) =
        Complex.exp (b * (x : ℂ))) :
    mellinOrbitSlope m a χ c = b := by
  have hl (x : ℝ) : modulatedLog m (c (Multiplicative.ofAdd x)) = logSlope m c * x := by
    have h0 : modulatedLog m 1 = 0 := congrArg Multiplicative.toAdd (map_one m)
    simpa only [one_mul, h0, zero_add] using modulatedLog_orbit m c 1 x
  have he (b : ℂ) : HasDerivAt (fun x : ℝ ↦ Complex.exp (b * (x : ℂ))) b 0 := by
    have hd : HasDerivAt (fun z : ℂ ↦ Complex.exp (b * z)) b (0 : ℂ) := by
      simpa using ((hasDerivAt_id' (0 : ℂ)).const_mul b).cexp
    exact hd.comp_ofReal
  let k : ℂ := (a * logSlope m c : ℝ)
  have hc (x : ℝ) : (χ (c (Multiplicative.ofAdd x)) : ℂ) = Complex.exp ((b - k) * (x : ℂ)) := by
    have hx := h x
    have hk : k = (a : ℂ) * (logSlope m c : ℂ) := Complex.ofReal_mul _ _
    simp only [hl, Complex.ofReal_mul, ← mul_assoc, ← hk] at hx
    refine (mul_right_cancel₀ (Complex.exp_ne_zero (k * (x : ℂ)))) (hx.trans ?_)
    rw [← Complex.exp_add]
    congr 1
    ring
  have hs : unitaryOrbitSlope c χ = b - k := by
    unfold unitaryOrbitSlope bruhatOrbitDeriv
    simp only [one_mul, hc]
    exact (he (b - k)).deriv
  rw [mellinOrbitSlope, hs]
  change k + (b - k) = b
  ring

private theorem integrate_shiftAdjointDerivative (hm : IsProperMap m) (hms : Surjective m)
    (a : ℝ) (χ : PontryaginDual G) (c : Multiplicative ℝ →ₜ* G) (f : BruhatSchwartz G) :
    (∫ x, (shiftAdjointDerivative m a c f).val x * (χ x : ℂ) ∂μ) =
      mellinOrbitSlope m a χ c * (∫ x, f.val x * (χ x : ℂ) ∂μ) := by
  have hi (g : BruhatSchwartz G) : Integrable (fun x ↦ g.val x * (χ x : ℂ)) μ := by
    refine (bruhatSchwartz_integrable μ m hm hms g).norm.mono'
      ((bruhatSchwartz_continuous g).mul (continuous_subtype_val.comp χ.continuous)).aestronglyMeasurable
      (.of_forall fun x ↦ by rw [norm_mul, Circle.norm_coe, mul_one])
  let b : ℂ := (a * logSlope m c : ℝ)
  simp only [show ∀ x, (shiftAdjointDerivative m a c f).val x =
    b * f.val x - (bruhatSchwartz_derivative c f).val x from fun _ ↦ rfl, sub_mul, mul_assoc]
  rw [integral_sub ((hi f).const_mul b) (hi (bruhatSchwartz_derivative c f)), integral_const_mul,
    integral_derivative_mul_character μ m hm hms]
  simp only [mellinOrbitSlope, b, neg_mul]
  ring

private theorem integrate_shiftedAdjointWord (hm : IsProperMap m) (hms : Surjective m)
    (a : ℝ) (χ : PontryaginDual G) (cs : List (Multiplicative ℝ →ₜ* G)) (f : BruhatSchwartz G) :
    (∫ x, (shiftedAdjointWord m a cs f).val x * (χ x : ℂ) ∂μ) =
      (cs.map (mellinOrbitSlope m a χ)).prod * (∫ x, f.val x * (χ x : ℂ) ∂μ) := by
  induction cs with
  | nil => simp [shiftedAdjointWord]
  | cons c cs ih =>
    change (∫ x, (shiftAdjointDerivative m a c (shiftedAdjointWord m a cs f)).val x * (χ x : ℂ) ∂μ) = _
    simp only [integrate_shiftAdjointDerivative μ m hm hms, ih, List.map_cons, List.prod_cons, mul_assoc]

/-- The Fourier–Mellin integral pairs the test with a unitary character and the real abscissa. -/
def modulatedMellinIntegral (u : G → ℂ) (a : ℝ) (χ : PontryaginDual G) : ℂ :=
  ∫ x, (modulatedExponentialWeight m a u) x * (χ x : ℂ) ∂μ

/-- Fourier–Mellin evaluation is a continuous linear functional on compact Bruhat tests. -/
def bruhatCompactMellinCLM (hm : IsProperMap m) (hms : Surjective m)
    (a : ℝ) (χ : PontryaginDual G) : BruhatCompactTest G →L[ℂ] ℂ := by
  let L : BruhatCompactTest G →L[ℂ] ModulatedExponentialInductive m univ :=
    ⟨bruhatCompactTest_toModulatedExponentialInductive m univ,
      bruhatCompactTest_continuous_inductiveDecay m univ hm hms⟩
  let A := (modulatedDecayTwistCLM m univ ⟨a, mem_univ a⟩).comp L
  have hI (f : BruhatCompactTest G) : Integrable (fun x => (A f).val x * (χ x : ℂ)) μ := by
    have hc : Continuous (fun x => (A f).val x * (χ x : ℂ)) :=
      (bruhatSchwartz_continuous (A f)).mul (continuous_subtype_val.comp χ.continuous)
    apply (integrable_norm_iff hc.aestronglyMeasurable).mp
    simpa only [norm_mul, Circle.norm_coe, mul_one] using
      (bruhatSchwartz_integrable μ m hm hms (A f)).norm
  let T : BruhatCompactTest G →ₗ[ℂ] ℂ :=
    { toFun := fun f => modulatedMellinIntegral μ m f.val a χ
      map_add' := fun f g => by
        change (∫ x, (A (f + g)).val x * (χ x : ℂ) ∂μ) =
          (∫ x, (A f).val x * (χ x : ℂ) ∂μ) + ∫ x, (A g).val x * (χ x : ℂ) ∂μ
        rw [map_add]
        simpa only [Submodule.coe_add, Pi.add_apply, add_mul] using integral_add (hI f) (hI g)
      map_smul' := fun c f => by
        change (∫ x, (A (c • f)).val x * (χ x : ℂ) ∂μ) =
          c • ∫ x, (A f).val x * (χ x : ℂ) ∂μ
        rw [map_smul]
        simp only [Submodule.coe_smul, Pi.smul_apply, smul_mul_assoc, integral_smul] }
  refine ⟨T, ?_⟩
  let q := (bruhatL1Seminorm μ m hm hms).comp A.toLinearMap
  have hn : Continuous (fun f => ‖T f‖) :=
    Seminorm.continuous_of_le (p := (normSeminorm ℂ ℂ).comp T) (q := q)
      ((bruhatL1Seminorm_continuous μ m hm hms).comp A.continuous) fun f => by
        change ‖∫ x, (A f).val x * (χ x : ℂ) ∂μ‖ ≤ ∫ x, ‖(A f).val x‖ ∂μ
        simpa only [norm_mul, Circle.norm_coe, mul_one] using
          norm_integral_le_integral_norm (fun x => (A f).val x * (χ x : ℂ))
  apply continuous_of_tendsto_nhds_zero T.toAddMonoidHom
  rw [Metric.tendsto_nhds]
  intro ε hε
  exact ((hn.tendsto' 0 0 (by simp)).eventually (Iio_mem_nhds hε)).mono fun x h => by
    change dist (T x) 0 < ε
    rw [dist_zero_right]
    exact h

@[simp] theorem bruhatCompactMellinCLM_apply (hm : IsProperMap m) (hms : Surjective m)
    (a : ℝ) (χ : PontryaginDual G) (f : BruhatCompactTest G) :
    bruhatCompactMellinCLM μ m hm hms a χ f = modulatedMellinIntegral μ m f.val a χ :=
  rfl

private theorem norm_mellinWord_mul_le (hm : IsProperMap m) (hms : Surjective m)
    {I : Set ℝ} (B : Set (ModulatedExponentialInductive m I)) (hB : Bornology.IsVonNBounded ℂ B)
    (α β : I) (cs : List (Multiplicative ℝ →ₜ* G)) :
    ∃ C > 0, ∀ f ∈ B, ∀ a : I, α.val ≤ a.val → a.val ≤ β.val → ∀ χ : PontryaginDual G,
      ‖(cs.map (mellinOrbitSlope m a χ)).prod * modulatedMellinIntegral μ m f.val a χ‖ ≤ C := by
  let X := ModulatedExponentialInductive m I
  let j (p : WholeBruhatStage G) := ModulatedExponentialInductive.stageMap (m := m) (I := I) p
  let q := bruhatL1Seminorm μ m hm hms
  let A (a : I) : X →L[ℂ] BruhatSchwartz G :=
    (shiftedAdjointWord m a cs).comp (modulatedDecayTwistCLM m I a)
  have hAb (a : I) : ∃ C > 0, ∀ f ∈ B, q (A a f) < C := by
    let s : Seminorm ℂ X := q.comp (A a).toLinearMap
    have hcont : Continuous s := (bruhatL1Seminorm_continuous μ m hm hms).comp (A a).continuous
    let i : FinalSeminorm j := ⟨s, fun p ↦ hcont.comp (ModulatedExponentialInductive.stageMap_continuous p)⟩
    exact (locallyConvexFinal_withSeminorms j).isVonNBounded_iff_seminorm_bounded.mp hB i
  obtain ⟨C, hC, hα⟩ := hAb α
  obtain ⟨D, hD, hβ⟩ := hAb β
  refine ⟨C + D, add_pos hC hD, fun f hf a ha hb χ ↦ ?_⟩
  have htwist (b : I) :
      modulatedExponentialWeight m b f.val = (modulatedDecayTwistCLM m I b f).val := rfl
  have hword (b : I) : modulatedExponentialWeight m b (adjointDerivativeWord cs f.val) =
      (A b f).val :=
    weightedAdjointWord m b cs _ _ (htwist b)
  have hmono (x : G) : ‖(A a f).val x‖ ≤ ‖(A α f).val x‖ + ‖(A β f).val x‖ := by
    have hpoint (b : I) : ‖(A b f).val x‖ = Real.exp (b.val * modulatedLog m x) *
        ‖adjointDerivativeWord cs f.val x‖ := by
      rw [← congrFun (hword b) x, modulatedExponentialWeight_apply, norm_smul,
        Real.norm_of_nonneg (Real.exp_nonneg _)]
      rfl
    rw [hpoint, hpoint, hpoint]
    by_cases hx : 0 ≤ modulatedLog m x
    · exact (mul_le_mul_of_nonneg_right
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hb hx)) (norm_nonneg _)).trans
        (le_add_of_nonneg_left (by positivity))
    · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonpos_right ha (le_of_not_ge hx))) (norm_nonneg _)).trans
        (le_add_of_nonneg_right (by positivity))
  have hin (b : I) := (bruhatSchwartz_integrable μ m hm hms (A b f)).norm
  have hIntegral : (∫ x, ‖(A a f).val x‖ ∂μ) ≤ q (A α f) + q (A β f) := by
    change _ ≤ (∫ x, ‖(A α f).val x‖ ∂μ) + ∫ x, ‖(A β f).val x‖ ∂μ
    rw [← integral_add (hin α) (hin β)]
    exact integral_mono (hin a) ((hin α).add (hin β)) hmono
  have hI : (∫ x, (A a f).val x * (χ x : ℂ) ∂μ) =
      (cs.map (mellinOrbitSlope m a χ)).prod * modulatedMellinIntegral μ m f.val a χ :=
    integrate_shiftedAdjointWord μ m hm hms a χ cs (modulatedDecayTwistCLM m I a f)
  rw [← hI]
  refine (norm_integral_le_integral_norm _).trans ?_
  simp only [norm_mul, Circle.norm_coe, mul_one]
  exact hIntegral.trans (add_le_add (hα f hf).le (hβ f hf).le)

/-- The symbol of a finite linear combination of invariant differential words. -/
def modulatedMellinSymbol (D : List (ℂ × List (Multiplicative ℝ →ₜ* G)))
    (a : ℝ) (χ : PontryaginDual G) : ℂ :=
  (D.map fun (b, cs) ↦ b * (cs.map (mellinOrbitSlope m a χ)).prod).sum

/-- Evaluating the differential operator on the quasi-character at the identity
gives the symbol used in the strip bound. -/
theorem modulatedMellinSymbol_eq_operator (D : List (ℂ × List (Multiplicative ℝ →ₜ* G)))
    (a : ℝ) (χ : PontryaginDual G) :
    modulatedMellinSymbol m D a χ = (D.map fun (b, cs) ↦
      b * (cs.foldr bruhatOrbitDeriv
        (modulatedExponentialWeight m a (fun x ↦ (χ x : ℂ)))) 1).sum := by
  let v := modulatedExponentialWeight m a (fun x ↦ (χ x : ℂ))
  have hv (c : Multiplicative ℝ →ₜ* G) (b : ℂ) (x : G) :
      bruhatOrbitDeriv c (fun y ↦ b * v y) x = b * mellinOrbitSlope m a χ c * v x := by
    have h := ((logWeight_orbit_hasDerivAt m c a x 0).ofReal_comp.mul
      (character_orbit_hasDerivAt c χ x 0)).const_mul b
    have hzero : x * c (Multiplicative.ofAdd (0 : ℝ)) = x := by
      rw [show c (Multiplicative.ofAdd (0 : ℝ)) = 1 from map_one c, mul_one]
    simp only [hzero] at h
    have he : b * (((↑(a * logSlope m c * Real.exp (a * modulatedLog m x)) : ℂ) *
        (χ x : ℂ)) + (↑(Real.exp (a * modulatedLog m x)) : ℂ) *
        (unitaryOrbitSlope c χ * (χ x : ℂ))) = b * mellinOrbitSlope m a χ c * v x := by
      change _ = b * (↑(a * logSlope m c) + unitaryOrbitSlope c χ) *
        ((↑(Real.exp (a * modulatedLog m x)) : ℂ) * (χ x : ℂ))
      push_cast
      ring
    exact (h.congr_deriv he).deriv
  have hword (cs : List (Multiplicative ℝ →ₜ* G)) :
      cs.foldr bruhatOrbitDeriv v =
        fun x ↦ (cs.map (mellinOrbitSlope m a χ)).prod * v x := by
    induction cs with
    | nil => simp
    | cons c cs ih =>
      rw [List.foldr_cons, ih, List.map_cons, List.prod_cons]
      funext x
      rw [hv, mul_comm ((cs.map (mellinOrbitSlope m a χ)).prod)]
  have h1 : v 1 = 1 := by simp [v, modulatedExponentialWeight_apply]
  unfold modulatedMellinSymbol
  change _ = (D.map fun (b, cs) ↦ b * (cs.foldr bruhatOrbitDeriv v) 1).sum
  simp only [hword, h1, mul_one]

/-- Corrected Theorem D.3.4.2. Each closed substrip whose endpoints belong to the
weight interval admits a uniform symbol-times-Mellin bound. The constant works
for all unitary characters, and no lower bound on the symbol is needed. -/
theorem modulatedMellin_symbol_norm_le_on_substrip (hm : IsProperMap m) (hms : Surjective m)
    {I : Set ℝ} (B : Set (ModulatedExponentialInductive m I)) (hB : Bornology.IsVonNBounded ℂ B)
    (α β : I) (D : List (ℂ × List (Multiplicative ℝ →ₜ* G))) :
    ∃ C > 0, ∀ f ∈ B, ∀ a : I, α.val ≤ a.val → a.val ≤ β.val → ∀ χ : PontryaginDual G,
      ‖modulatedMellinSymbol m D a χ * modulatedMellinIntegral μ m f.val a χ‖ ≤ C := by
  induction D with
  | nil =>
    exact ⟨1, zero_lt_one, by simp [modulatedMellinSymbol]⟩
  | cons p D ih =>
    obtain ⟨C, hC, hD⟩ := ih
    obtain ⟨A, hA, hW⟩ := norm_mellinWord_mul_le μ m hm hms B hB α β p.2
    refine ⟨‖p.1‖ * A + C, add_pos_of_nonneg_of_pos (by positivity) hC,
      fun f hf a hα hβ χ ↦ ?_⟩
    simp only [modulatedMellinSymbol, List.map_cons, List.sum_cons, add_mul, mul_assoc]
    exact (norm_add_le _ _).trans (add_le_add
      (by rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hW f hf a hα hβ χ) (norm_nonneg _))
      (hD f hf a hα hβ χ))

/-- The product estimate is the reciprocal-symbol bound whenever the symbol is nonzero. -/
theorem modulatedMellin_norm_le_div_symbol_on_substrip (hm : IsProperMap m) (hms : Surjective m)
    {I : Set ℝ} (B : Set (ModulatedExponentialInductive m I)) (hB : Bornology.IsVonNBounded ℂ B)
    (α β : I) (D : List (ℂ × List (Multiplicative ℝ →ₜ* G))) :
    ∃ C > 0, ∀ f ∈ B, ∀ a : I, α.val ≤ a.val → a.val ≤ β.val →
      ∀ χ : PontryaginDual G, modulatedMellinSymbol m D a χ ≠ 0 →
        ‖modulatedMellinIntegral μ m f.val a χ‖ ≤ C / ‖modulatedMellinSymbol m D a χ‖ := by
  obtain ⟨C, hC, h⟩ := modulatedMellin_symbol_norm_le_on_substrip μ m hm hms B hB α β D
  refine ⟨C, hC, fun f hf a ha hb χ hn ↦ (le_div_iff₀ (norm_pos_iff.mpr hn)).mpr ?_⟩
  rw [mul_comm, ← norm_mul]
  exact h f hf a ha hb χ

end

end Masullo
