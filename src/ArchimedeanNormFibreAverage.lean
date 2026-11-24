import ArchimedeanNormFibreSchwartz
import ArchimedeanRegulatorHaar

open Filter Function MeasureTheory NumberField NumberField.Units.dirichletUnitTheorem Set Topology
open scoped SchwartzMap NumberField Classical NNReal

namespace Masullo
noncomputable section

variable (F : Type*) [Field F] [NumberField F]

/-- Pulling the fibre kernel back by the translated regulator projection
preserves its integral up to one positive Haar normalization. -/
theorem archNormOne_logFibreKernel_integral
    [MeasurableSpace (archNormOne F)] [BorelSpace (archNormOne F)]
    (μ : Measure (archNormOne F)) [μ.IsHaarMeasure] :
    ∃ c : ℝ≥0, 0 < c ∧ ∀ x : InfiniteIdeles F,
      let ι := {w : InfinitePlace F // w ≠ w₀}
      let K := archimedeanLogFibreKernel (ι := ι) (max 0 (-Real.log ‖x.val‖))
      let B := fun g : archNormOne F => K (fun w => fullArchLog F x w - (archRegulatorLog F g).toAdd w)
      Integrable B μ ∧ (∫ g, B g ∂μ) = (c : ℝ) * ∫ z, K z := by
  dsimp only
  let ι := {w : InfinitePlace F // w ≠ w₀}
  let ρ : Measure (ι → ℝ) := volume
  letI : ρ.IsAddHaarMeasure := isAddHaarMeasure_volume_pi ι
  let Λ (g : archNormOne F) := (archRegulatorLog F g).toAdd
  have hΛ : Measurable Λ := (continuous_toAdd.comp (archRegulatorLog_continuous F)).measurable
  obtain ⟨c, hc, hmap⟩ := archRegulatorLog_map_haar F μ
  have hρ : μ.map Λ = c • ρ := hmap
  refine ⟨c, hc, fun x => ?_⟩
  let T := max 0 (-Real.log ‖x.val‖)
  let K := archimedeanLogFibreKernel (ι := ι) T
  let y : ι → ℝ := fun w => fullArchLog F x w
  let B (z : ι → ℝ) := K (y - z)
  have hi := (archimedeanLogFibreKernel_integral_le ι T (le_max_left _ _)).1
  have hB : Integrable B ρ := by
    have hm := (measurePreserving_add_left ρ y).comp (Measure.measurePreserving_neg ρ)
    simpa only [B, Function.comp_def, sub_eq_add_neg] using hm.integrable_comp_of_integrable hi
  have hBm : Integrable B (μ.map Λ) := hρ.symm ▸ hB.smul_measure_nnreal
  have hBi : Integrable (B ∘ Λ) μ := (integrable_map_measure hBm.aestronglyMeasurable hΛ.aemeasurable).mp hBm
  have hIB : (∫ z, B z ∂ρ) = ∫ z, K z ∂ρ := by
    change (∫ z, K (y - z) ∂ρ) = _
    simp only [sub_eq_add_neg]
    rw [integral_neg_eq_self (fun z => K (y + z)) ρ, integral_add_left_eq_self]
  refine ⟨hBi, ?_⟩
  change (∫ g, B (Λ g) ∂μ) = (c : ℝ) * ∫ z, K z ∂ρ
  rw [← integral_map hΛ.aemeasurable hBm.aestronglyMeasurable, hρ,
    integral_smul_nnreal_measure, hIB]
  rfl

/-- Absolute convergence and the logarithmic bound for the integral over
the actual archimedean norm-one ideles. The omitted coordinate gives the
power of the logarithm. -/
theorem archNormOne_average_weighted_schwartz_bound
    [MeasurableSpace (archNormOne F)] [BorelSpace (archNormOne F)]
    (μ : Measure (archNormOne F)) [μ.IsHaarMeasure]
    (j : ℕ) (f : 𝓢(mixedEmbedding.mixedSpace F, ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : InfiniteIdeles F,
      let A (g : archNormOne F) := f (InfiniteAdeleRing.ringEquiv_mixedSpace F (g.val⁻¹ * x).val)
      let T := max 0 (-Real.log ‖x.val‖)
      Integrable A μ ∧ Real.exp ((j : ℝ) * max 0 (Real.log ‖x.val‖)) * (∫ g, ‖A g‖ ∂μ) ≤
        C * (1 + T) ^ Fintype.card {w : InfinitePlace F // w ≠ w₀} := by
  let ι := {w : InfinitePlace F // w ≠ w₀}
  obtain ⟨c, hc, hKernel⟩ := archNormOne_logFibreKernel_integral F μ
  obtain ⟨D, hD, hmajor⟩ := archSchwartz_logFibre_weighted_bound F j f
  let n := Fintype.card ι
  let k := Real.exp 1 * (2 * (n + 1 : ℝ)) ^ n
  refine ⟨D * c * k, by positivity, fun x => ?_⟩
  let T := max 0 (-Real.log ‖x.val‖)
  let K := archimedeanLogFibreKernel (ι := ι) T
  let B (g : archNormOne F) := K (fun w => fullArchLog F x w - (archRegulatorLog F g).toAdd w)
  let A (g : archNormOne F) := f (InfiniteAdeleRing.ringEquiv_mixedSpace F (g.val⁻¹ * x).val)
  let w := Real.exp ((j : ℝ) * max 0 (Real.log ‖x.val‖))
  have hw : 1 ≤ w := by dsimp [w]; exact Real.one_le_exp (by positivity)
  have hAb : ∀ g, w * ‖A g‖ ≤ D * B g := hmajor x
  have hk := (archimedeanLogFibreKernel_integral_le ι T (le_max_left _ _)).2
  have hBi : Integrable B μ := (hKernel x).1
  have hcE : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
    apply Continuous.prodMk <;> apply continuous_pi <;> intro w
    · exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal w.property).continuous.comp (continuous_apply w.val)
    · exact (InfinitePlace.Completion.isometry_extensionEmbedding w.val).continuous.comp (continuous_apply w.val)
  have hA : Continuous A := f.continuous.comp (hcE.comp (Units.continuous_val.comp
    (continuous_subtype_val.inv.mul continuous_const)))
  have hAi : Integrable A μ := (hBi.const_mul D).mono' hA.aestronglyMeasurable
    (.of_forall fun g => (le_mul_of_one_le_left (norm_nonneg _) hw).trans (hAb g))
  refine ⟨hAi, ?_⟩
  change w * (∫ g, ‖A g‖ ∂μ) ≤ D * c * k * (1 + T) ^ n
  calc
    _ = ∫ g, w * ‖A g‖ ∂μ := (integral_const_mul w _).symm
    _ ≤ ∫ g, D * B g ∂μ := integral_mono (hAi.norm.const_mul w) (hBi.const_mul D) hAb
    _ = (D * c) * ∫ z, K z := by
      rw [integral_const_mul, show (∫ g, B g ∂μ) = (c : ℝ) * ∫ z, K z from (hKernel x).2]
      ring
    _ ≤ _ := by
      rw [mul_assoc (D * c)]
      exact mul_le_mul_of_nonneg_left hk (mul_nonneg hD c.coe_nonneg)

/-- The unweighted norm-one integral has the logarithmic bound. -/
theorem archNormOne_average_schwartz_bound
    [MeasurableSpace (archNormOne F)] [BorelSpace (archNormOne F)]
    (μ : Measure (archNormOne F)) [μ.IsHaarMeasure]
    (f : 𝓢(mixedEmbedding.mixedSpace F, ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : InfiniteIdeles F,
      let A (g : archNormOne F) := f (InfiniteAdeleRing.ringEquiv_mixedSpace F (g.val⁻¹ * x).val)
      let T := max 0 (-Real.log ‖x.val‖)
      Integrable A μ ∧ (∫ g, ‖A g‖ ∂μ) ≤ C * (1 + T) ^ Fintype.card {w : InfinitePlace F // w ≠ w₀} := by
  simpa only [Nat.cast_zero, zero_mul, Real.exp_zero, one_mul] using
    archNormOne_average_weighted_schwartz_bound F μ 0 f

private theorem archLogModulus_sub (a x : InfiniteIdeles F) :
    Real.log ‖(a⁻¹ * x).val‖ = Real.log ‖x.val‖ - Real.log ‖a.val‖ := by
  have hlo (b d : InfiniteIdeles F) : Real.log ‖(b * d).val‖ = Real.log ‖b.val‖ + Real.log ‖d.val‖ := by
    rw [← fullArchLog_sum, fullArchLog_mul, show (∑ v, (fullArchLog F b + fullArchLog F d) v) =
      ∑ v, (fullArchLog F b v + fullArchLog F d v) from rfl,
      Finset.sum_add_distrib, fullArchLog_sum, fullArchLog_sum]
  have hh := hlo a⁻¹ a
  rw [inv_mul_cancel] at hh
  have hzero : Real.log ‖((1 : InfiniteIdeles F).val)‖ = 0 := by
    rw [← fullArchLog_sum]
    have h (w : InfinitePlace F) : fullArchLog F (1 : InfiniteIdeles F) w = 0 := by
      change (w.mult : ℝ) * Real.log ‖(1 : w.Completion)‖ = 0
      simp
    simp only [h, Finset.sum_const_zero]
  rw [hzero] at hh
  rw [hlo]
  linarith

/-- The finite sum of character-weighted norm-one integrals in (6.2.2.3)
is absolutely convergent and has the polynomial logarithmic majorant. -/
theorem archNormOne_standardAverage_logBound
    [MeasurableSpace (archNormOne F)] [BorelSpace (archNormOne F)]
    (μ : Measure (archNormOne F)) [μ.IsHaarMeasure]
    {J : Type*} [Fintype J] (r : J → InfiniteIdeles F)
    (χ : InfiniteIdeles F →ₜ* Circle) (f : 𝓢(mixedEmbedding.mixedSpace F, ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : InfiniteIdeles F,
      let A (j : J) (g : archNormOne F) :=
        f (InfiniteAdeleRing.ringEquiv_mixedSpace F ((r j * g.val)⁻¹ * x).val) * (χ (r j * g.val) : ℂ)
      (∀ j, Integrable (A j) μ) ∧
      ‖∑ j, ∫ g, A j g ∂μ‖ ≤
        C * (1 + |Real.log ‖x.val‖|) ^ (Fintype.card (InfinitePlace F) - 1) := by
  have hcard : Fintype.card {w : InfinitePlace F // w ≠ w₀} = Fintype.card (InfinitePlace F) - 1 := by
    simpa only [Fintype.card_subtype_eq] using Fintype.card_subtype_compl (fun w : InfinitePlace F => w = w₀)
  rw [← hcard]
  obtain ⟨D, hD, hA⟩ := archNormOne_average_schwartz_bound F μ f
  let n := Fintype.card {w : InfinitePlace F // w ≠ w₀}
  let R (j : J) := |Real.log ‖(r j).val‖|
  let C (j : J) := D * (1 + R j) ^ n
  have hC (j : J) : 0 ≤ C j := mul_nonneg hD (pow_nonneg (by positivity [R]) _)
  refine ⟨∑ j, C j, Finset.sum_nonneg (fun j _ => hC j), fun x => ?_⟩
  let A (j : J) (g : archNormOne F) :=
    f (InfiniteAdeleRing.ringEquiv_mixedSpace F ((r j * g.val)⁻¹ * x).val) * (χ (r j * g.val) : ℂ)
  let B (j : J) (g : archNormOne F) :=
    f (InfiniteAdeleRing.ringEquiv_mixedSpace F (g.val⁻¹ * ((r j)⁻¹ * x)).val)
  have hform (j : J) (g : archNormOne F) : A j g = B j g * (χ (r j * g.val) : ℂ) := by
    change f (InfiniteAdeleRing.ringEquiv_mixedSpace F ((r j * g.val)⁻¹ * x).val) * _ = _
    rw [mul_inv_rev, mul_assoc]
  have hn (j : J) (g : archNormOne F) : ‖A j g‖ = ‖B j g‖ := by
    rw [hform, norm_mul, Circle.norm_coe, mul_one]
  have hI (j : J) : Integrable (A j) μ := by
    have h := (hA ((r j)⁻¹ * x)).1
    have hc : Continuous (fun g : archNormOne F => (χ (r j * g.val) : ℂ)) :=
      (continuous_subtype_val.comp χ.continuous).comp (continuous_const.mul continuous_subtype_val)
    exact (h.mul_bdd (c := 1) hc.aestronglyMeasurable (.of_forall fun g => (Circle.norm_coe _).le)).congr
      (.of_forall fun g => (hform j g).symm)
  have hp (j : J) : ‖∫ g, A j g ∂μ‖ ≤ C j * (1 + |Real.log ‖x.val‖|) ^ n := by
    have hT : max 0 (-Real.log ‖((r j)⁻¹ * x).val‖) ≤ R j + |Real.log ‖x.val‖| := by
      rw [archLogModulus_sub F]
      apply max_le (by positivity [R])
      dsimp [R]
      linarith only [le_abs_self (Real.log ‖(r j).val‖), neg_abs_le (Real.log ‖x.val‖)]
    have hprod : 1 + max 0 (-Real.log ‖((r j)⁻¹ * x).val‖) ≤ (1 + R j) * (1 + |Real.log ‖x.val‖|) := by
      nlinarith only [hT, mul_nonneg (abs_nonneg (Real.log ‖(r j).val‖)) (abs_nonneg (Real.log ‖x.val‖))]
    calc
      _ ≤ ∫ g, ‖A j g‖ ∂μ := norm_integral_le_integral_norm _
      _ = ∫ g, ‖B j g‖ ∂μ := integral_congr_ae (.of_forall (hn j))
      _ ≤ D * (1 + max 0 (-Real.log ‖((r j)⁻¹ * x).val‖)) ^ n := (hA ((r j)⁻¹ * x)).2
      _ ≤ D * ((1 + R j) * (1 + |Real.log ‖x.val‖|)) ^ n := by
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hprod _) hD
      _ = _ := by rw [mul_pow, ← mul_assoc]
  refine ⟨hI, ?_⟩
  calc
    _ ≤ ∑ j, ‖∫ g, A j g ∂μ‖ := norm_sum_le _ _
    _ ≤ ∑ j, C j * (1 + |Real.log ‖x.val‖|) ^ n := Finset.sum_le_sum (fun j _ => hp j)
    _ = _ := Finset.sum_mul _ _ _ |>.symm

/-- Every power of the norm is absorbed by the Schwartz tail on the large
modulus side, including the translates and unitary character weights. -/
theorem archNormOne_standardAverage_forwardBound
    [MeasurableSpace (archNormOne F)] [BorelSpace (archNormOne F)]
    (μ : Measure (archNormOne F)) [μ.IsHaarMeasure]
    {J : Type*} [Fintype J] (r : J → InfiniteIdeles F)
    (χ : InfiniteIdeles F →ₜ* Circle) (f : 𝓢(mixedEmbedding.mixedSpace F, ℂ)) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : InfiniteIdeles F, 1 ≤ ‖x.val‖ →
      ‖∑ j, ∫ g : archNormOne F,
          f (InfiniteAdeleRing.ringEquiv_mixedSpace F ((r j * g.val)⁻¹ * x).val) * (χ (r j * g.val) : ℂ) ∂μ‖ ≤
        C * Real.exp (-(k : ℝ) * Real.log ‖x.val‖) := by
  obtain ⟨D, hD, hA⟩ := archNormOne_average_weighted_schwartz_bound F μ k f
  let n := Fintype.card {w : InfinitePlace F // w ≠ w₀}
  let R (j : J) := |Real.log ‖(r j).val‖|
  let C (j : J) := Real.exp ((k : ℝ) * R j) * (D * (1 + R j) ^ n)
  have hC (j : J) : 0 ≤ C j := by dsimp [C, R]; positivity
  refine ⟨∑ j, C j, Finset.sum_nonneg (fun j _ => hC j), fun x hx => ?_⟩
  let w := Real.exp ((k : ℝ) * Real.log ‖x.val‖)
  have hw : 0 < w := Real.exp_pos _
  have hlog : 0 ≤ Real.log ‖x.val‖ := Real.log_nonneg hx
  let A (j : J) (g : archNormOne F) :=
    f (InfiniteAdeleRing.ringEquiv_mixedSpace F ((r j * g.val)⁻¹ * x).val) * (χ (r j * g.val) : ℂ)
  have hp (j : J) : w * ‖∫ g, A j g ∂μ‖ ≤ C j := by
    let y := (r j)⁻¹ * x
    let B (g : archNormOne F) := f (InfiniteAdeleRing.ringEquiv_mixedSpace F (g.val⁻¹ * y).val)
    let v := Real.exp ((k : ℝ) * max 0 (Real.log ‖y.val‖))
    have hcut : max 0 (-Real.log ‖y.val‖) ≤ R j := by
      change max 0 (-Real.log ‖((r j)⁻¹ * x).val‖) ≤ _
      rw [archLogModulus_sub F]
      exact max_le (abs_nonneg _) (by dsimp [R]; linarith only [hlog, le_abs_self (Real.log ‖(r j).val‖)])
    have hweight : w ≤ Real.exp ((k : ℝ) * R j) * v := by
      change Real.exp ((k : ℝ) * Real.log ‖x.val‖) ≤
        Real.exp ((k : ℝ) * R j) * Real.exp ((k : ℝ) * max 0 (Real.log ‖y.val‖))
      rw [← Real.exp_add, ← mul_add]
      apply Real.exp_le_exp.mpr
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg k)
      have hl : Real.log ‖y.val‖ = Real.log ‖x.val‖ - Real.log ‖(r j).val‖ := archLogModulus_sub F _ _
      linarith only [hl, le_max_right 0 (Real.log ‖y.val‖), le_abs_self (Real.log ‖(r j).val‖)]
    have hnorm (g : archNormOne F) : ‖A j g‖ = ‖B g‖ := by
      change ‖f (InfiniteAdeleRing.ringEquiv_mixedSpace F ((r j * g.val)⁻¹ * x).val) *
        (χ (r j * g.val) : ℂ)‖ = _
      rw [norm_mul, Circle.norm_coe, mul_one, mul_inv_rev, mul_assoc]
    have hB : 0 ≤ ∫ g, ‖B g‖ ∂μ := integral_nonneg (fun _ => norm_nonneg _)
    have hpow : (1 + max 0 (-Real.log ‖y.val‖)) ^ n ≤ (1 + R j) ^ n :=
      pow_le_pow_left₀ (by positivity) (by linarith only [hcut]) _
    calc
      _ ≤ w * (∫ g, ‖A j g‖ ∂μ) := mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) hw.le
      _ = w * (∫ g, ‖B g‖ ∂μ) := congrArg (w * ·) (integral_congr_ae (.of_forall hnorm))
      _ ≤ (Real.exp ((k : ℝ) * R j) * v) * (∫ g, ‖B g‖ ∂μ) := mul_le_mul_of_nonneg_right hweight hB
      _ = Real.exp ((k : ℝ) * R j) * (v * ∫ g, ‖B g‖ ∂μ) := mul_assoc _ _ _
      _ ≤ Real.exp ((k : ℝ) * R j) * (D * (1 + max 0 (-Real.log ‖y.val‖)) ^ n) :=
        mul_le_mul_of_nonneg_left (hA y).2 (Real.exp_pos _).le
      _ ≤ C j := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow hD) (Real.exp_pos _).le
  change ‖∑ j, ∫ g, A j g ∂μ‖ ≤ _
  have hsum : w * ‖∑ j, ∫ g, A j g ∂μ‖ ≤ ∑ j, C j := by
    calc
      _ ≤ w * ∑ j, ‖∫ g, A j g ∂μ‖ := mul_le_mul_of_nonneg_left (norm_sum_le _ _) hw.le
      _ = ∑ j, w * ‖∫ g, A j g ∂μ‖ := Finset.mul_sum _ _ _
      _ ≤ _ := Finset.sum_le_sum (fun j _ => hp j)
  have he : w⁻¹ = Real.exp (-(k : ℝ) * Real.log ‖x.val‖) := by rw [neg_mul, Real.exp_neg]
  rw [← he, ← div_eq_mul_inv]
  exact (le_div_iff₀' hw).mpr hsum

end
end Masullo
