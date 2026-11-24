import BruhatSobolevConvolution
import BruhatFourierDerivative
import ModulatedDecayIsotypes
import Mathlib.Analysis.Calculus.ParametricIntegral

open Filter Function MeasureTheory Set Topology

namespace Masullo
noncomputable section

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure] (m : G →ₜ* Multiplicative ℝ) {I : Set ℝ}

/-- The Fourier–Mellin integrand in a chart with a unitary base character. -/
def decayMellinIntegrand (χ : PontryaginDual G) (f : ModulatedExponentialInductive m I)
    (z : ℂ) (g : G) : ℂ :=
  f.val g * (χ g : ℂ) * Complex.exp (z * (modulatedLog m g : ℂ))

omit [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] in
private theorem norm_decayMellinIntegrand (χ : PontryaginDual G)
    (f : ModulatedExponentialInductive m I) (z : ℂ) (g : G) :
    ‖decayMellinIntegrand m χ f z g‖ = ‖f.val g‖ * Real.exp (z.re * modulatedLog m g) := by
  simp [decayMellinIntegrand, Complex.norm_exp, Complex.mul_re, Circle.norm_coe]

omit [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] in
theorem continuous_decayMellinIntegrand (χ : PontryaginDual G)
    (f : ModulatedExponentialInductive m I) (z : ℂ) (hI : I.Nonempty) :
    Continuous (decayMellinIntegrand m χ f z) := by
  obtain ⟨a, ha⟩ := hI
  let L := modulatedDecayTwistCLM m I ⟨a, ha⟩ f
  have hlog : Continuous (modulatedLog m) := continuous_toAdd.comp m.continuous
  have hF : Continuous f.val := by
    have he (g : G) : Real.exp (-(a * modulatedLog m g)) • L.val g = f.val g := by
      change Real.exp (-(a * modulatedLog m g)) • (Real.exp (a * modulatedLog m g) • f.val g) = _
      rw [smul_smul, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_smul]
    exact (((continuous_const.mul hlog).neg.rexp).smul (bruhatSchwartz_continuous L)).congr he
  exact (hF.mul (continuous_subtype_val.comp χ.continuous)).mul
    ((continuous_const.mul (Complex.continuous_ofReal.comp hlog)).cexp)

omit [SecondCountableTopology G] in
/-- Absolute convergence of the Fourier–Mellin transform throughout the
relative strip, including its endpoints when they belong to the decay interval. -/
theorem decayMellinIntegrand_integrable (χ : PontryaginDual G)
    (f : ModulatedExponentialInductive m I) {z : ℂ} (hz : z.re ∈ I) :
    Integrable (decayMellinIntegrand m χ f z) μ := by
  let A := modulatedDecayTwistCLM m I ⟨z.re, hz⟩ f
  refine (bruhatSchwartz_integrable μ A).norm.mono'
    ((continuous_decayMellinIntegrand m χ f z ⟨_, hz⟩).aestronglyMeasurable) (.of_forall fun g => ?_)
  rw [norm_decayMellinIntegrand]
  change _ ≤ ‖Real.exp (z.re * modulatedLog m g) • f.val g‖
  rw [norm_smul, Real.norm_of_nonneg (Real.exp_nonneg _), mul_comm]

omit [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] in
private theorem decayMellinIntegrand_hasDerivAt (χ : PontryaginDual G)
    (f : ModulatedExponentialInductive m I) (z : ℂ) (g : G) :
    HasDerivAt (fun w => decayMellinIntegrand m χ f w g)
      ((modulatedLog m g : ℂ) * decayMellinIntegrand m χ f z g) z := by
  simpa [decayMellinIntegrand, mul_assoc, mul_left_comm, mul_comm] using
    (((hasDerivAt_id' z).mul_const (modulatedLog m g : ℂ)).cexp).const_mul
      (f.val g * (χ g : ℂ))

private theorem decayMellin_exp_le {a c b x : ℝ} (ha : a ≤ c) (hb : c ≤ b) :
    Real.exp (c * x) ≤ Real.exp (a * x) + Real.exp (b * x) := by
  rcases le_total 0 x with hx | hx
  · exact (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hb hx)).trans
      (le_add_of_nonneg_left (Real.exp_nonneg _))
  · exact (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_right ha hx)).trans
      (le_add_of_nonneg_right (Real.exp_nonneg _))

/-- On each unitary-character chart the Haar Fourier–Mellin integral is
holomorphic in the open strip, with the derivative given by the logarithmic moment. -/
theorem decayMellin_hasDerivAt (hm : IsProperMap m) (hms : Surjective m)
    (χ : PontryaginDual G) (f : ModulatedExponentialInductive m I)
    {z : ℂ} (hz : z.re ∈ interior I) :
    HasDerivAt (fun w => ∫ g, decayMellinIntegrand m χ f w g ∂μ)
      (∫ g, (modulatedLog m g : ℂ) * decayMellinIntegrand m χ f z g ∂μ) z := by
  have hzI : z.re ∈ I := interior_subset hz
  obtain ⟨a, b, hzab, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp (mem_interior_iff_mem_nhds.mp hz)
  obtain ⟨a', haa, haz⟩ := exists_between hzab.1
  obtain ⟨b', hzb, hbb⟩ := exists_between hzab.2
  let A := modulatedDecayTwistCLM m I ⟨a', hsub ⟨haa, haz.trans hzab.2⟩⟩ f
  let B := modulatedDecayTwistCLM m I ⟨b', hsub ⟨hzab.1.trans hzb, hbb⟩⟩ f
  let M (g : G) := (‖A.val g‖ + ‖B.val g‖) * (1 + |modulatedLog m g|)
  have hM : Integrable M μ := by
    have hA := bruhatSchwartz_integrable_SobolevKernelWeight μ m hm hms 2 (by norm_num) A
    have hB := bruhatSchwartz_integrable_SobolevKernelWeight μ m hm hms 2 (by norm_num) B
    simpa [M, singletonSobolevKernelWeight, add_mul, Pi.add_def] using hA.add hB
  let V := decayMellinIntegrand m χ f
  have hC (w : ℂ) : Continuous (V w) := continuous_decayMellinIntegrand m χ f w ⟨_, hzI⟩
  have hN : Complex.re ⁻¹' Ioo a' b' ∈ 𝓝 z :=
    (isOpen_Ioo.preimage Complex.continuous_re).mem_nhds ⟨haz, hzb⟩
  have hlog : Continuous (fun g => (modulatedLog m g : ℂ)) :=
    Complex.continuous_ofReal.comp (continuous_toAdd.comp m.continuous)
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := V)
    (F' := fun w g => (modulatedLog m g : ℂ) * V w g) (bound := M) hN
    (.of_forall fun w => (hC w).aestronglyMeasurable) (decayMellinIntegrand_integrable μ m χ f hzI)
    ((hlog.mul (hC z)).aestronglyMeasurable) (.of_forall fun g w hw => ?_) hM
    (.of_forall fun g w _ => decayMellinIntegrand_hasDerivAt m χ f w g)).2
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_decayMellinIntegrand]
  have hab : Real.exp (w.re * modulatedLog m g) ≤
      Real.exp (a' * modulatedLog m g) + Real.exp (b' * modulatedLog m g) :=
    decayMellin_exp_le hw.1.le hw.2.le
  have hbound : ‖f.val g‖ * Real.exp (w.re * modulatedLog m g) ≤ ‖A.val g‖ + ‖B.val g‖ := by
    change _ ≤ ‖Real.exp (a' * modulatedLog m g) • f.val g‖ +
      ‖Real.exp (b' * modulatedLog m g) • f.val g‖
    rw [norm_smul, norm_smul, Real.norm_of_nonneg (Real.exp_nonneg _),
      Real.norm_of_nonneg (Real.exp_nonneg _), ← add_mul, mul_comm ‖f.val g‖]
    exact mul_le_mul_of_nonneg_right hab (norm_nonneg _)
  rw [mul_comm |modulatedLog m g|]
  exact mul_le_mul hbound (by linarith) (abs_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))

/-- Fourier–Mellin evaluation is linear in the decay test. -/
def decayMellinEvaluation (χ : PontryaginDual G) (z : ℂ) (hz : z.re ∈ I) :
    ModulatedExponentialInductive m I →ₗ[ℂ] ℂ where
  toFun f := ∫ g, decayMellinIntegrand m χ f z g ∂μ
  map_add' f h := by
    have he (g : G) : decayMellinIntegrand m χ (f + h) z g =
        decayMellinIntegrand m χ f z g + decayMellinIntegrand m χ h z g := by
      change (f.val g + h.val g) * _ * _ = _
      simp only [decayMellinIntegrand, add_mul]
    simp only [he, integral_add (decayMellinIntegrand_integrable μ m χ f hz)
      (decayMellinIntegrand_integrable μ m χ h hz)]
  map_smul' c f := by
    have he (g : G) : decayMellinIntegrand m χ (c • f) z g =
        c * decayMellinIntegrand m χ f z g := by
      change (c * f.val g) * _ * _ = _
      simp only [decayMellinIntegrand, mul_assoc]
    simp only [he, integral_const_mul, RingHom.id_apply, smul_eq_mul]

omit [SecondCountableTopology G] in
/-- Left translation becomes multiplication by the chart's quasi-character. -/
theorem decayMellinEvaluation_translate (χ : PontryaginDual G) {z : ℂ} (hz : z.re ∈ I)
    (f : ModulatedExponentialInductive m I) (y : G) :
    decayMellinEvaluation μ m χ z hz (ModulatedExponentialInductive.translate m I y f) =
      ((χ y : ℂ) * Complex.exp (z * (modulatedLog m y : ℂ))) * decayMellinEvaluation μ m χ z hz f := by
  let v := decayMellinIntegrand m χ (ModulatedExponentialInductive.translate m I y f) z
  change (∫ g, v g ∂μ) = (χ y : ℂ) * _ * (∫ g, decayMellinIntegrand m χ f z g ∂μ)
  rw [← integral_mul_left_eq_self v y, ← integral_const_mul]
  apply integral_congr_ae
  exact .of_forall fun g => by
    have hlog : modulatedLog m (y * g) = modulatedLog m y + modulatedLog m g := by
      simp only [modulatedLog, map_mul, toAdd_mul]
    simp only [v, decayMellinIntegrand, ModulatedExponentialInductive.translate_apply,
      inv_mul_cancel_left, map_mul, Circle.coe_mul, hlog, Complex.ofReal_add, mul_add, Complex.exp_add]
    ring

end
end Masullo
