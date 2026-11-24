import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Count

open Filter Function MeasureTheory Set Topology
open scoped ENNReal

namespace Masullo

noncomputable section

private def logTrace (p : ℝ × ℝ) : ℝ := Real.log p.1

private def interval (r : ℝ) : Set ℝ := Ioo (-r) r

private abbrev planeMeasure := (volume : Measure ℝ).prod (volume : Measure ℝ)

private theorem logTrace_integrable_box (r : ℝ) (hr : 0 < r) :
    IntegrableOn logTrace (interval r ×ˢ interval r) planeMeasure := by
  have hlog : IntegrableOn Real.log (interval r) (volume : Measure ℝ) := by
    apply (integrableOn_Ioc_iff_integrableOn_Ioo).mp
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith : -r ≤ r)).mp
      intervalIntegral.intervalIntegrable_log'
  have hfin : (volume : Measure ℝ) (interval r) ≠ ∞ := by simp [interval, Real.volume_Ioo]
  have hone : Integrable (fun _ : ℝ => (1 : ℝ)) ((volume : Measure ℝ).restrict (interval r)) :=
    integrableOn_const hfin
  have hh := hlog.mul_prod hone
  change Integrable (fun z : ℝ × ℝ => Real.log z.1)
    (((volume : Measure ℝ).prod (volume : Measure ℝ)).restrict (interval r ×ˢ interval r))
  simpa only [Measure.prod_restrict, mul_one, IntegrableOn] using hh

/-- The locally integrable logarithm of the first coordinate has average
`log r - 1` on the square of radius `r`. -/
theorem logTrace_average_square (r : ℝ) (hr : 0 < r) :
    (⨍ p in interval r ×ˢ interval r, logTrace p ∂planeMeasure) = Real.log r - 1 := by
  have hvol : (volume : Measure ℝ).real (interval r) = 2 * r := by
    rw [measureReal_def, interval, Real.volume_Ioo, ENNReal.toReal_ofReal (by linarith)]
    ring
  have hi : (∫ x in interval r, Real.log x) = 2 * r * (Real.log r - 1) := by
    rw [interval, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le (by linarith : -r ≤ r), integral_log, Real.log_neg_eq_log]
    ring
  rw [setAverage_eq, setIntegral_prod _ (logTrace_integrable_box r hr)]
  have hinner (x : ℝ) : (∫ y in interval r, logTrace (x, y)) =
      (volume : Measure ℝ).real (interval r) * Real.log x := by
    rw [show (fun y : ℝ => logTrace (x, y)) = fun _ => Real.log x from rfl,
      setIntegral_const, smul_eq_mul]
  simp_rw [hinner]
  rw [integral_const_mul, hi]
  have hprod : planeMeasure.real (interval r ×ˢ interval r) = (2 * r) * (2 * r) := by
    rw [measureReal_def, Measure.prod_prod, ENNReal.toReal_mul]
    exact congrArg₂ (· * ·) hvol hvol
  rw [hprod, hvol, smul_eq_mul]
  field_simp

private theorem logTrace_locallyIntegrable : LocallyIntegrable logTrace planeMeasure := by
  apply locallyIntegrable_iff.mpr
  intro K hK
  obtain ⟨C, hC⟩ := hK.isBounded.exists_norm_le
  let r := max 1 C + 1
  have hr : 0 < r := by dsimp [r]; linarith [le_max_left (1 : ℝ) C]
  refine (logTrace_integrable_box r hr).mono_set ?_
  intro p hp
  have h := hC p hp
  have hpr : ‖p‖ < r := h.trans_lt (by dsimp [r]; linarith [le_max_right (1 : ℝ) C])
  exact ⟨abs_lt.mp ((norm_fst_le p).trans_lt hpr), abs_lt.mp ((norm_snd_le p).trans_lt hpr)⟩

/-- The origin is irregular for the square averages of the locally integrable
logarithm, for the open squares with radii `exp (-n)`. -/
theorem logTrace_nonregular :
    LocallyIntegrable logTrace planeMeasure ∧
      ¬ ∃ a : ℝ, Tendsto (fun n : ℕ =>
        ⨍ p in interval (Real.exp (-(n : ℝ))) ×ˢ interval (Real.exp (-(n : ℝ))),
          logTrace p ∂planeMeasure) atTop (𝓝 a) := by
  refine ⟨logTrace_locallyIntegrable, ?_⟩
  rintro ⟨a, ha⟩
  simp_rw [logTrace_average_square _ (Real.exp_pos _), Real.log_exp] at ha
  have hb : Tendsto (fun n : ℕ => -(n : ℝ) - 1) atTop atBot :=
    tendsto_atBot_add_const_right _ _ (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop)
  have h₁ := tendsto_order.mp ha |>.1 (a - 1) (sub_lt_self _ zero_lt_one)
  have h₂ := (tendsto_atBot.1 hb) (a - 1)
  obtain ⟨n, hn₁, hn₂⟩ := (h₁.and h₂).exists
  exact (not_lt_of_ge hn₂) hn₁


private def axisCutoff (p : ℤ × ℝ) : ℝ := if p.1 = 0 then 1 else 0

private def axisDiagonalCutoff (p q : ℤ × ℝ) : ℝ :=
  ∫ k : ℤ, axisCutoff (p.1 - k, p.2) * axisCutoff (q.1 - k, q.2) ∂Measure.count

private abbrev splitHaar := (Measure.count : Measure ℤ).prod (volume : Measure ℝ)

private def splitWindow (z : ℤ) (r : ℝ) : Set (ℤ × ℝ) :=
  ({z} : Set ℤ) ×ˢ interval r

private theorem axisCutoff_continuous : Continuous axisCutoff := by
  exact (continuous_of_discreteTopology (f := fun z : ℤ => if z = 0 then (1 : ℝ) else 0)).comp
    continuous_fst

private theorem axisCutoff_proper (K : Set ℝ) (hK : IsCompact K) :
    IsCompact (tsupport axisCutoff ∩ Prod.snd ⁻¹' K) := by
  have hs : support axisCutoff = ({0} : Set ℤ) ×ˢ (univ : Set ℝ) := by
    ext p
    by_cases hp : p.1 = 0 <;> simp [axisCutoff, hp]
  have hts : tsupport axisCutoff = ({0} : Set ℤ) ×ˢ (univ : Set ℝ) := by
    rw [tsupport, hs, (isClosed_singleton.prod isClosed_univ).closure_eq]
  rw [hts, show (({0} : Set ℤ) ×ˢ univ) ∩ Prod.snd ⁻¹' K = ({0} : Set ℤ) ×ˢ K by ext; simp]
  exact isCompact_singleton.prod hK

private theorem axisCutoff_normalized (p : ℤ × ℝ) :
    Integrable (fun k : ℤ => axisCutoff (p.1 - k, p.2)) Measure.count ∧
      (∫ k : ℤ, axisCutoff (p.1 - k, p.2) ∂Measure.count) = 1 := by
  have he : (fun k : ℤ => axisCutoff (p.1 - k, p.2)) = ({p.1} : Set ℤ).indicator 1 := by
    funext k
    by_cases h : k = p.1
    · subst k
      rw [indicator_of_mem (mem_singleton _) _]
      simp [axisCutoff]
    · rw [indicator_of_notMem (show k ∉ ({p.1} : Set ℤ) from h)]
      simp [axisCutoff, sub_eq_zero, Ne.symm h]
  rw [he]
  exact ⟨(integrable_indicator_iff (measurableSet_singleton p.1)).mpr
    (integrableOn_const (by simp)), by
      rw [integral_indicator (measurableSet_singleton p.1)]
      change (∫ _ : ℤ in {p.1}, (1 : ℝ) ∂Measure.count) = 1
      rw [setIntegral_const]
      simp [measureReal_def]⟩

private theorem axisDiagonalCutoff_zero {p q : ℤ × ℝ} (hne : p.1 ≠ q.1) :
    axisDiagonalCutoff p q = 0 := by
  unfold axisDiagonalCutoff
  have h (k : ℤ) : axisCutoff (p.1 - k, p.2) * axisCutoff (q.1 - k, q.2) = 0 := by
    by_cases hk : p.1 = k
    · have hk' : q.1 ≠ k := fun he => hne (hk.trans he.symm)
      simp [axisCutoff, sub_eq_zero, hk, hk']
    · simp [axisCutoff, sub_eq_zero, hk]
  simp [h]

/-- The converse regularity claim in 12.2.2.2(4) fails in the split quotient
of `ℤ × ℝ` by the integer axis. The cutoff is normalized on each fibre.
The lifted averages over boxes at `((0,0),(1,0))` vanish, while the quotient
averages at `(0,0)` have no finite limit. -/
theorem diagonalRegularity_split_obstruction :
    Continuous axisCutoff ∧
    (∀ K : Set ℝ, IsCompact K → IsCompact (tsupport axisCutoff ∩ Prod.snd ⁻¹' K)) ∧
    (∀ p : ℤ × ℝ, Integrable (fun k : ℤ => axisCutoff (p.1 - k, p.2)) Measure.count ∧
      (∫ k : ℤ, axisCutoff (p.1 - k, p.2) ∂Measure.count) = 1) ∧
    LocallyIntegrable logTrace planeMeasure ∧
    (∀ n : ℕ, let r := Real.exp (-(n : ℝ))
      (⨍ p in splitWindow 0 r ×ˢ splitWindow 1 r,
        axisDiagonalCutoff p.1 p.2 * logTrace (p.1.2, p.2.2) ∂splitHaar.prod splitHaar) = 0) ∧
    ¬ ∃ a : ℝ, Tendsto (fun n : ℕ =>
      ⨍ p in interval (Real.exp (-(n : ℝ))) ×ˢ interval (Real.exp (-(n : ℝ))),
        logTrace p ∂planeMeasure) atTop (𝓝 a) := by
  refine ⟨axisCutoff_continuous, axisCutoff_proper, axisCutoff_normalized,
    logTrace_locallyIntegrable, ?_, logTrace_nonregular.2⟩
  intro n r
  have hmeas : MeasurableSet (splitWindow 0 r ×ˢ splitWindow 1 r) :=
    ((measurableSet_singleton 0).prod measurableSet_Ioo).prod
      ((measurableSet_singleton 1).prod measurableSet_Ioo)
  calc
    _ = ⨍ _ in splitWindow 0 r ×ˢ splitWindow 1 r, (0 : ℝ) ∂splitHaar.prod splitHaar := ?_
    _ = _ := average_zero _
  apply average_congr
  filter_upwards [ae_restrict_mem hmeas] with p hp
  have hzero : p.1.1 = 0 := hp.1.1
  have hone : p.2.1 = 1 := hp.2.1
  rw [axisDiagonalCutoff_zero (by rw [hzero, hone]; decide), zero_mul]

end
end Masullo
