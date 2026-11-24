import ModulatedSobolevNorm
import ModulatedCharacters
import LCAPlancherel
import SobolevDuality
import Mathlib.Analysis.Calculus.ParametricIntegral

open Filter Function MeasureTheory Set Topology
open scoped CompactlySupported ENNReal NNReal

namespace Masullo

noncomputable section

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) (m : G →ₜ* Multiplicative ℝ)

/-- The physical Sobolev space with density `(1 + (log |g|)^2)^N`. -/
abbrev ModulatedLogSobolev (N : ℕ) :=
  Lp ℂ 2 (hardySobolevMeasure μ (fun g => Multiplicative.toAdd (m g)) 0 0 (2 * (N : ℝ)))

omit [IsTopologicalGroup G] in
private theorem logSobolev_base_absolutelyContinuous (N : ℕ) :
    μ ≪ hardySobolevMeasure μ (fun g => Multiplicative.toAdd (m g)) 0 0 (2 * (N : ℝ)) := by
  apply withDensity_absolutelyContinuous'
  · exact (((continuous_hardySobolevWeight ..).comp
      (continuous_toAdd.comp m.continuous)).measurable.ennreal_ofReal).aemeasurable
  · exact .of_forall fun g => ENNReal.ofReal_ne_zero_iff.mpr (by
      unfold hardySobolevWeight
      positivity)

private abbrev logMoment (k : ℕ) (f : G → ℂ) (g : G) : ℂ :=
  ((Multiplicative.toAdd (m g) : ℝ) : ℂ) ^ k * f g

omit [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] in
private theorem logMoment_norm_sq (k : ℕ) (f : G → ℂ) (g : G) :
    ‖logMoment m k f g‖ ^ 2 = ‖f g‖ ^ 2 * (Multiplicative.toAdd (m g) ^ 2) ^ k := by
  simp only [logMoment, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  rw [mul_pow, mul_comm, ← pow_mul, mul_comm k 2, pow_mul, sq_abs]

omit [IsTopologicalGroup G] in
private theorem logMoment_memLp (N : ℕ) (k : Fin (N + 1)) (f : ModulatedLogSobolev μ m N) :
    MemLp (logMoment m (k : ℕ) f) 2 μ := by
  have hm : Measurable (fun g => Multiplicative.toAdd (m g)) :=
    (continuous_toAdd.comp m.continuous).measurable
  have hf : AEStronglyMeasurable (f : G → ℂ) μ :=
    (Lp.aestronglyMeasurable f).mono_ac (logSobolev_base_absolutelyContinuous μ m N)
  have hmul : AEStronglyMeasurable (logMoment m (k : ℕ) f) μ :=
    ((Complex.continuous_ofReal.measurable.comp hm).aestronglyMeasurable.pow _).mul hf
  apply (memLp_two_iff_integrable_sq_norm hmul).mpr
  simp_rw [logMoment_norm_sq]
  exact (hardySobolev_even_norm_sq μ hm 0 N (Lp.memLp f)).1 k
    (Nat.le_of_lt_succ k.isLt) |>.congr (.of_forall fun g => by simp)

omit [IsTopologicalGroup G] in
private theorem logMoment_norm_identity (N : ℕ) (f : ModulatedLogSobolev μ m N) :
    ‖f‖ ^ 2 = ∑ k : Fin (N + 1), (N.choose (k : ℕ) : ℝ) *
      ‖(logMoment_memLp μ m N k f).toLp (logMoment m (k : ℕ) f)‖ ^ 2 := by
  have hm : Measurable (fun g => Multiplicative.toAdd (m g)) :=
    (continuous_toAdd.comp m.continuous).measurable
  have h := (hardySobolev_even_norm_sq μ hm 0 N (Lp.memLp f)).2
  simp only [Lp.toLp_coeFn, mul_zero, zero_mul, Real.exp_zero, one_mul] at h
  rw [h, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k _
  rw [norm_sq_toLp_two]
  simp_rw [logMoment_norm_sq]

/-- Multiplication by a logarithmic power is bounded from the weighted
Sobolev space of even degree to ordinary Haar L². -/
def modulatedSobolevLogMoment (N : ℕ) (k : Fin (N + 1)) :
    ModulatedLogSobolev μ m N →L[ℂ] Lp ℂ 2 μ := by
  let T (f : ModulatedLogSobolev μ m N) :=
    (logMoment_memLp μ m N k f).toLp (logMoment m (k : ℕ) f)
  have hT (f : ModulatedLogSobolev μ m N) : (T f : G → ℂ) =ᵐ[μ] logMoment m (k : ℕ) f :=
    MemLp.coeFn_toLp _
  have hAC := logSobolev_base_absolutelyContinuous μ m N
  let L : ModulatedLogSobolev μ m N →ₗ[ℂ] Lp ℂ 2 μ :=
    { toFun := T
      map_add' := fun f g => by
        apply Lp.ext
        filter_upwards [hT (f + g), hT f, hT g, hAC.ae_le (Lp.coeFn_add f g),
          Lp.coeFn_add (T f) (T g)] with x hfg hf hg hadd hright
        change T (f + g) x = (T f + T g) x
        rw [hfg, hright]
        simp only [logMoment, Pi.add_apply] at *
        rw [hadd, hf, hg, mul_add]
      map_smul' := fun c f => by
        apply Lp.ext
        filter_upwards [hT (c • f), hT f, hAC.ae_le (Lp.coeFn_smul c f),
          Lp.coeFn_smul c (T f)] with x hcf hf hsmul hright
        change T (c • f) x = (c • T f) x
        rw [hcf, hright]
        simp only [logMoment, Pi.smul_apply, smul_eq_mul] at *
        rw [hsmul, hf, mul_left_comm] }
  apply L.mkContinuous 1
  intro f
  rw [one_mul]
  have hc : (1 : ℝ) ≤ N.choose (k : ℕ) := by
    exact_mod_cast Nat.choose_pos (Nat.le_of_lt_succ k.isLt)
  have h := logMoment_norm_identity μ m N f
  have h₁ : ‖T f‖ ^ 2 ≤ ‖f‖ ^ 2 := by
    rw [h]
    exact (le_mul_of_one_le_left (sq_nonneg _) hc).trans
      (Finset.single_le_sum (f := fun j : Fin (N + 1) =>
        (N.choose (j : ℕ) : ℝ) *
          ‖(logMoment_memLp μ m N j f).toLp (logMoment m (j : ℕ) f)‖ ^ 2)
        (fun j _ => by positivity) (Finset.mem_univ k))
  exact le_of_pow_le_pow_left₀ two_ne_zero (norm_nonneg _) h₁

omit [IsTopologicalGroup G] in
theorem modulatedSobolevLogMoment_ae (N : ℕ) (k : Fin (N + 1)) (f : ModulatedLogSobolev μ m N) :
    (modulatedSobolevLogMoment μ m N k f : G → ℂ) =ᵐ[μ] logMoment m (k : ℕ) f :=
  MemLp.coeFn_toLp (logMoment_memLp μ m N k f)

variable [MeasurableSpace (PontryaginDual G)]

/-- The Fourier image of the logarithmic moment is the normalized radial
derivative on Sobolev classes. Its classical formula on compact tests is
given below. -/
def modulatedSobolevFourierDerivative
    {ν : Measure (PontryaginDual G)} (U : Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 ν)
    (N : ℕ) (k : Fin (N + 1)) :
    ModulatedLogSobolev μ m N →L[ℂ] Lp ℂ 2 ν :=
  U.toContinuousLinearEquiv.toContinuousLinearMap.comp (modulatedSobolevLogMoment μ m N k)

omit [IsTopologicalGroup G] in
theorem modulatedSobolevFourierDerivative_norm_sq
    {ν : Measure (PontryaginDual G)} (U : Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 ν)
    (N : ℕ) (f : ModulatedLogSobolev μ m N) :
    ‖f‖ ^ 2 = ∑ k : Fin (N + 1), (N.choose (k : ℕ) : ℝ) *
      ‖modulatedSobolevFourierDerivative μ m U N k f‖ ^ 2 := by
  change ‖f‖ ^ 2 = ∑ k : Fin (N + 1), (N.choose (k : ℕ) : ℝ) *
    ‖U ((logMoment_memLp μ m N k f).toLp (logMoment m (k : ℕ) f))‖ ^ 2
  simp only [LinearIsometryEquiv.norm_map]
  exact logMoment_norm_identity μ m N f

omit [IsTopologicalGroup G] in
/-- The finite family of radial derivative norms generates the topology
of the log-weighted Sobolev space of degree two times N. -/
theorem modulatedSobolev_withFourierDerivativeSeminorms
    {ν : Measure (PontryaginDual G)} (U : Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 ν)
    (N : ℕ) :
    WithSeminorms (fun k : (_i : Fin (N + 1)) × Fin 1 =>
      (normSeminorm ℂ (Lp ℂ 2 ν)).comp
        (modulatedSobolevFourierDerivative μ m U N k.1).toLinearMap) := by
  let J := ContinuousLinearMap.pi (modulatedSobolevFourierDerivative μ m U N)
  let C : ℝ≥0 := 1 + ∑ k : Fin (N + 1), (N.choose (k : ℕ) : ℝ≥0)
  have hC : 1 ≤ (C : ℝ) := by
    simp [C]
    positivity
  have hC' : (∑ k : Fin (N + 1), (N.choose (k : ℕ) : ℝ)) ≤ (C : ℝ) ^ 2 := by
    have h := mul_le_mul_of_nonneg_right hC (show 0 ≤ (C : ℝ) by positivity)
    have h' : (∑ k : Fin (N + 1), (N.choose (k : ℕ) : ℝ)) ≤ (C : ℝ) := by
      simp [C]
    simpa [pow_two] using h'.trans (by simpa using h)
  have hbound (f : ModulatedLogSobolev μ m N) : ‖f‖ ≤ (C : ℝ) * ‖J f‖ := by
    apply le_of_pow_le_pow_left₀ two_ne_zero (by positivity)
    calc
      ‖f‖ ^ 2 = ∑ k : Fin (N + 1), (N.choose (k : ℕ) : ℝ) * ‖J f k‖ ^ 2 :=
        modulatedSobolevFourierDerivative_norm_sq μ m U N f
      _ ≤ ∑ k : Fin (N + 1), (N.choose (k : ℕ) : ℝ) * ‖J f‖ ^ 2 :=
        Finset.sum_le_sum fun k _ => by
          gcongr
          exact norm_le_pi_norm (J f) k
      _ ≤ ((C : ℝ) * ‖J f‖) ^ 2 := by
        rw [← Finset.sum_mul, mul_pow]
        exact mul_le_mul_of_nonneg_right hC' (sq_nonneg _)
  have hanti : AntilipschitzWith C J := by
    rw [antilipschitzWith_iff_le_mul_dist]
    intro f g
    simpa only [dist_eq_norm, map_sub] using hbound (f - g)
  have hJ : IsInducing J.toLinearMap := hanti.isInducing J.continuous
  exact hJ.withSeminorms (withSeminorms_pi (fun _ : Fin (N + 1) => norm_withSeminorms ℂ (Lp ℂ 2 ν)))


omit [IsTopologicalGroup G] in
/-- Rescaling the invariant first-order generator by a nonzero scalar
leaves the finite derivative-seminorm topology unchanged. -/
theorem modulatedSobolev_withScaledFourierDerivativeSeminorms
    {ν : Measure (PontryaginDual G)} (U : Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 ν)
    (N : ℕ) (c : ℂ) (hc : c ≠ 0) :
    WithSeminorms (fun k : (_i : Fin (N + 1)) × Fin 1 =>
      (normSeminorm ℂ (Lp ℂ 2 ν)).comp
        (c ^ (k.1 : ℕ) • modulatedSobolevFourierDerivative μ m U N k.1).toLinearMap) := by
  let p : SeminormFamily ℂ (ModulatedLogSobolev μ m N) ((_i : Fin (N + 1)) × Fin 1) :=
    fun k => (normSeminorm ℂ (Lp ℂ 2 ν)).comp
      (modulatedSobolevFourierDerivative μ m U N k.1).toLinearMap
  let q : SeminormFamily ℂ (ModulatedLogSobolev μ m N) ((_i : Fin (N + 1)) × Fin 1) :=
    fun k => (normSeminorm ℂ (Lp ℂ 2 ν)).comp
      (c ^ (k.1 : ℕ) • modulatedSobolevFourierDerivative μ m U N k.1).toLinearMap
  change WithSeminorms q
  rw [q.withSeminorms_iff_nhds_eq_iInf,
    p.withSeminorms_iff_nhds_eq_iInf.mp (modulatedSobolev_withFourierDerivativeSeminorms μ m U N)]
  congr 1
  funext k
  let a := ‖c‖ ^ (k.1 : ℕ)
  have hq : (q k : ModulatedLogSobolev μ m N → ℝ) = (a * ·) ∘ (p k) := by
    funext f
    change ‖c ^ (k.1 : ℕ) • modulatedSobolevFourierDerivative μ m U N k.1 f‖ =
      a * ‖modulatedSobolevFourierDerivative μ m U N k.1 f‖
    rw [norm_smul, norm_pow]
  have hhome : (𝓝 (0 : ℝ)).comap (a * ·) = 𝓝 0 := by
    simpa using (Homeomorph.mulLeft₀ a (pow_ne_zero _ (norm_ne_zero_iff.mpr hc))).comap_nhds_eq 0
  rw [hq, ← Filter.comap_comap, hhome]

private def fourierRadialSlope (x : ℝ) : ℂ := -(2 * Real.pi * Complex.I) * (x : ℂ)

private theorem norm_exp_radialSlope (x y : ℝ) :
    ‖Complex.exp (fourierRadialSlope x * (y : ℂ))‖ = 1 := by
  simp [fourierRadialSlope, Complex.norm_exp, Complex.mul_re, Complex.mul_im]

omit [CommGroup G] [IsTopologicalGroup G] [MeasurableSpace (PontryaginDual G)] in
private theorem radial_iteratedDeriv_integral [IsFiniteMeasureOnCompacts μ]
    (l : G → ℝ) (hl : Continuous l) (f : G → ℂ) (hf : Continuous f)
    (hK : HasCompactSupport f) (k : ℕ) :
    iteratedDeriv k (fun y : ℝ => ∫ g, f g *
      Complex.exp (fourierRadialSlope (l g) * (y : ℂ)) ∂μ) =
      fun y : ℝ => ∫ g, fourierRadialSlope (l g) ^ k * f g *
        Complex.exp (fourierRadialSlope (l g) * (y : ℂ)) ∂μ := by
  let a g := fourierRadialSlope (l g)
  have ha : Continuous a :=
    continuous_const.mul (Complex.continuous_ofReal.comp hl)
  let H (j : ℕ) (y : ℝ) (g : G) := a g ^ j * f g * Complex.exp (a g * (y : ℂ))
  have hc (j : ℕ) (y : ℝ) : Continuous (H j y) := by
    exact ((ha.pow j).mul hf).mul ((ha.mul continuous_const).cexp)
  have hk (j : ℕ) (y : ℝ) : HasCompactSupport (H j y) :=
    ((hK.mul_left (f := fun g => a g ^ j)).mul_right
      (f' := fun g => Complex.exp (a g * (y : ℂ))))
  have hnorm (j : ℕ) (y : ℝ) (g : G) :
      ‖H j y g‖ = ‖a g ^ j * f g‖ := by
    simp only [H, norm_mul, norm_exp_radialSlope, a, mul_one]
  have hD (j : ℕ) (y : ℝ) : HasDerivAt (fun t : ℝ => ∫ g, H j t g ∂μ)
      (∫ g, H (j + 1) y g ∂μ) y := by
    have hB : Integrable (fun g => ‖a g ^ (j + 1) * f g‖) μ :=
      (((ha.pow (j + 1)).mul hf).integrable_of_hasCompactSupport
        (hK.mul_left (f := fun g => a g ^ (j + 1)))).norm
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := H j)
      (F' := H (j + 1)) univ_mem
      (.of_forall fun t => (hc j t).aestronglyMeasurable)
      ((hc j y).integrable_of_hasCompactSupport (hk j y))
      ((hc (j + 1) y).aestronglyMeasurable)
      (.of_forall fun g t _ => (hnorm (j + 1) t g).le) hB ?_).2
    refine .of_forall fun g t _ => ?_
    have hcast : HasDerivAt (fun x : ℝ => (x : ℂ)) 1 t :=
      Complex.ofRealCLM.hasFDerivAt.hasDerivAt
    convert ((hcast.const_mul (a g)).cexp.const_mul (a g ^ j * f g)) using 1 <;>
      first | rfl | (simp [H, pow_succ]; ring)
  change iteratedDeriv k (fun y : ℝ => ∫ g, f g * Complex.exp (a g * (y : ℂ)) ∂μ) = _
  induction k with
  | zero => simp [a]
  | succ j ih =>
    rw [iteratedDeriv_succ, ih]
    exact funext (fun y => (hD j y).deriv)


variable [T2Space G] [LocallyCompactSpace G]
  [BorelSpace (PontryaginDual G)] [IsFiniteMeasureOnCompacts μ]

omit [IsTopologicalGroup G] [MeasurableSpace (PontryaginDual G)] [T2Space G]
  [LocallyCompactSpace G] [BorelSpace (PontryaginDual G)] in
private theorem logSobolev_memLp_compact (N : ℕ) (f : G → ℂ)
    (hf : Continuous f) (hK : HasCompactSupport f) :
    MemLp f 2 (hardySobolevMeasure μ (fun g => Multiplicative.toAdd (m g)) 0 0 (2 * (N : ℝ))) := by
  apply (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mpr
  let l (g : G) : ℝ := Multiplicative.toAdd (m g)
  let w (g : G) := hardySobolevWeight 0 0 (2 * (N : ℝ)) (l g)
  have hl : Continuous l := continuous_toAdd.comp m.continuous
  have hw : Continuous w := (continuous_hardySobolevWeight ..).comp hl
  apply (integrable_hardySobolev_sq_iff μ hl.measurable ..).mpr
  have hnorm : HasCompactSupport (fun g => ‖f g‖ ^ 2) :=
    hK.comp_left (g := fun a : ℂ => ‖a‖ ^ 2) (by simp)
  exact (hw.mul (hf.norm.pow 2)).integrable_of_hasCompactSupport
    (hnorm.mul_left (f := w))

omit [IsTopologicalGroup G] [MeasurableSpace (PontryaginDual G)] [T2Space G]
  [LocallyCompactSpace G] [BorelSpace (PontryaginDual G)] in
/-- The class of a continuous compactly supported test in the physical Sobolev space. -/
def modulatedLogSobolevCompactTest (N : ℕ) (f : C_c(G, ℂ)) : ModulatedLogSobolev μ m N :=
  (logSobolev_memLp_compact μ m N f f.continuous f.hasCompactSupport).toLp f

omit [IsTopologicalGroup G] [MeasurableSpace (PontryaginDual G)]
  [BorelSpace (PontryaginDual G)] in
/-- Compactly supported tests are dense for the log-weighted norm. -/
theorem denseRange_modulatedLogSobolevCompactTest [μ.Regular] (N : ℕ) :
    DenseRange (modulatedLogSobolevCompactTest μ m N) := by
  let r (x : G) := Real.sqrt (hardySobolevWeight 0 0 (2 * (N : ℝ)) (Multiplicative.toAdd (m x)))
  have hr : Continuous r := ((continuous_hardySobolevWeight ..).comp
    (continuous_toAdd.comp m.continuous)).sqrt
  have hpos (x : G) : 0 < r x := by
    apply Real.sqrt_pos_of_pos
    unfold hardySobolevWeight
    positivity
  have hm : hardySobolevMeasure μ (fun g => Multiplicative.toAdd (m g)) 0 0 (2 * (N : ℝ)) =
      amplitudeMeasure μ r := by
    unfold hardySobolevMeasure amplitudeMeasure
    congr 1
    funext g
    rw [show r g ^ 2 = hardySobolevWeight 0 0 (2 * (N : ℝ)) (Multiplicative.toAdd (m g)) from
      Real.sq_sqrt (hardySobolevWeight_nonneg ..)]
  suffices ∀ (hmem : ∀ f : C_c(G, ℂ),
      MemLp (f : G → ℂ) 2 (hardySobolevMeasure μ (fun g => Multiplicative.toAdd (m g))
        0 0 (2 * (N : ℝ)))), DenseRange (fun f => (hmem f).toLp (f : G → ℂ)) from
    this (fun f => logSobolev_memLp_compact μ m N f f.continuous f.hasCompactSupport)
  rw [hm]
  intro hmem
  let A : C(G, ℂ) := ⟨fun g => (r g : ℂ), Complex.continuous_ofReal.comp hr⟩
  let I := amplitudeL2Iso μ r hr.measurable hpos
  have he (f : C_c(G, ℂ)) : I ((hmem f).toLp f) = sobolevWeightedTest μ A f := by
    apply Lp.ext
    filter_upwards [amplitudeL2Iso_ae μ r hr.measurable hpos ((hmem f).toLp f),
      (absolutelyContinuous_amplitudeMeasure μ r hr.measurable hpos).ae_le (hmem f).coeFn_toLp,
      sobolevWeightedTest_ae μ A f] with x hx hf hA
    rw [hx, hf, hA]
    rfl
  have hd := (I.symm.surjective.denseRange).comp
    (denseRange_sobolevWeightedTest μ A (fun x => Complex.ofReal_ne_zero.mpr (hpos x).ne'))
    I.symm.continuous
  convert hd using 1
  funext f
  change _ = I.symm (sobolevWeightedTest μ A f)
  rw [← he, I.symm_apply_apply]


omit [IsTopologicalGroup G] [BorelSpace G] [MeasurableSpace (PontryaginDual G)] [T2Space G]
  [LocallyCompactSpace G] [BorelSpace (PontryaginDual G)] [IsFiniteMeasureOnCompacts μ] in
private theorem lcaFourier_radial_twist (f : G → ℂ) (χ : PontryaginDual G) (y : ℝ) :
    lcaFourier μ f (χ * (show PontryaginDual G from modulusCharacter m (2 * Real.pi * y))) =
      ∫ g, (f g * star (χ g : ℂ)) *
        Complex.exp (fourierRadialSlope (Multiplicative.toAdd (m g)) * (y : ℂ)) ∂μ := by
  unfold lcaFourier
  apply integral_congr_ae
  refine .of_forall fun g => ?_
  change f g * star (((χ g * Circle.exp
    (2 * Real.pi * y * Multiplicative.toAdd (m g))) : Circle) : ℂ) = _
  rw [Circle.coe_mul, star_mul, Circle.coe_exp]
  have he : star (Complex.exp
      ((↑(2 * Real.pi * y * Multiplicative.toAdd (m g)) : ℂ) * Complex.I)) =
        Complex.exp (fourierRadialSlope (Multiplicative.toAdd (m g)) * (y : ℂ)) := by
    rw [Complex.star_def, ← Complex.exp_conj]
    congr 1
    simp [fourierRadialSlope, map_ofNat]
    ring
  rw [he]
  ring

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [BorelSpace (PontryaginDual G)] in
/-- On compactly supported continuous tests the extended Fourier derivative
agrees almost everywhere with the normalized classical derivative along the
real frequency line through each dual character. -/
theorem modulatedSobolevFourierDerivative_onCompact
    {ν : Measure (PontryaginDual G)} (U : Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 ν)
    (hU : IsFourierPlancherel μ ν U) (N : ℕ) (k : Fin (N + 1))
    (f : G → ℂ) (hf : Continuous f) (hK : HasCompactSupport f) :
    let f₂ := (logSobolev_memLp_compact μ m N f hf hK).toLp f
    (modulatedSobolevFourierDerivative μ m U N k f₂ : PontryaginDual G → ℂ) =ᵐ[ν]
      fun χ => (-(2 * Real.pi * Complex.I))⁻¹ ^ (k : ℕ) *
        iteratedDeriv (k : ℕ)
          (fun y : ℝ => lcaFourier μ f (χ * (show PontryaginDual G from modulusCharacter m (2 * Real.pi * y)))) 0 := by
  intro f₂
  let g := logMoment m (k : ℕ) f
  have hg : Continuous g :=
    ((Complex.continuous_ofReal.comp (continuous_toAdd.comp m.continuous)).pow _).mul hf
  have hgK : HasCompactSupport g := hK.mul_left
  have hg₂ := hg.memLp_of_hasCompactSupport (p := 2) (μ := μ) hgK
  have hm := logSobolev_base_absolutelyContinuous μ m N
  have heq : modulatedSobolevLogMoment μ m N k f₂ = hg₂.toLp g := by
    apply Lp.ext
    filter_upwards [modulatedSobolevLogMoment_ae μ m N k f₂,
      hm.ae_le ((logSobolev_memLp_compact μ m N f hf hK).coeFn_toLp),
      hg₂.coeFn_toLp] with x hx hfx hgx
    rw [hx, hgx]
    change f₂ x = f x at hfx
    simp only [logMoment, hfx, g]
  change (U (modulatedSobolevLogMoment μ m N k f₂) : PontryaginDual G → ℂ) =ᵐ[ν] _
  rw [heq]
  apply (hU g (hg.integrable_of_hasCompactSupport hgK) hg₂).trans
  refine .of_forall fun χ => ?_
  simp_rw [lcaFourier_radial_twist]
  let p (x : G) : ℂ := f x * star (χ x : ℂ)
  let l (x : G) : ℝ := Multiplicative.toAdd (m x)
  have hp : Continuous p := hf.mul ((continuous_subtype_val.comp χ.continuous).star)
  have hclass := radial_iteratedDeriv_integral μ l (continuous_toAdd.comp m.continuous) p hp
    (hK.mul_right (f' := fun x => star (χ x : ℂ))) (k : ℕ)
  change lcaFourier μ g χ = (-(2 * Real.pi * Complex.I))⁻¹ ^ (k : ℕ) *
    iteratedDeriv (k : ℕ)
      (fun y : ℝ => ∫ x, p x * Complex.exp (fourierRadialSlope (l x) * (y : ℂ)) ∂μ) 0
  rw [hclass]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one]
  rw [← integral_const_mul]
  unfold lcaFourier
  apply integral_congr_ae
  refine .of_forall fun x => ?_
  have hc : -(2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    exact neg_ne_zero.mpr (mul_ne_zero
      (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero)
  dsimp [fourierRadialSlope, g, logMoment, l, p]
  let c : ℂ := -(2 * Real.pi * Complex.I)
  let t : ℂ := ((l x : ℝ) : ℂ)
  change t ^ (k : ℕ) * f x * star (χ x : ℂ) =
    c⁻¹ ^ (k : ℕ) * ((c * t) ^ (k : ℕ) * (f x * star (χ x : ℂ)))
  have hcancel : c⁻¹ ^ (k : ℕ) * c ^ (k : ℕ) = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hc, one_pow]
  rw [mul_pow]
  calc
    _ = (c⁻¹ ^ (k : ℕ) * c ^ (k : ℕ)) * (t ^ (k : ℕ) * (f x * star (χ x : ℂ))) := by
      rw [hcancel, one_mul, mul_assoc]
    _ = _ := by ring

/-- The normalized radial Fourier derivative of order k has a unique
continuous linear extension to the weighted Sobolev completion. -/
theorem existsUnique_modulatedSobolevFourierDerivative [μ.Regular]
    {ν : Measure (PontryaginDual G)} (U : Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 ν)
    (hU : IsFourierPlancherel μ ν U) (N : ℕ) (k : Fin (N + 1)) :
    ∃! L : ModulatedLogSobolev μ m N →L[ℂ] Lp ℂ 2 ν,
      ∀ f : C_c(G, ℂ),
        (L (modulatedLogSobolevCompactTest μ m N f) : PontryaginDual G → ℂ) =ᵐ[ν]
          fun χ => (-(2 * Real.pi * Complex.I))⁻¹ ^ (k : ℕ) *
            iteratedDeriv (k : ℕ) (fun y : ℝ => lcaFourier μ f
              (χ * (show PontryaginDual G from modulusCharacter m (2 * Real.pi * y)))) 0 := by
  let D := modulatedSobolevFourierDerivative μ m U N k
  have hD (f : C_c(G, ℂ)) :=
    modulatedSobolevFourierDerivative_onCompact μ m U hU N k f f.continuous f.hasCompactSupport
  refine ⟨D, hD, fun L hL => ?_⟩
  apply DFunLike.coe_injective
  refine Continuous.ext_on (denseRange_modulatedLogSobolevCompactTest μ m N)
    L.continuous D.continuous ?_
  rintro _ ⟨f, rfl⟩
  exact Lp.ext ((hL f).trans (hD f).symm)


end

end Masullo
