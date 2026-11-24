import ArchimedeanRadialLift
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

open Filter Function MeasureTheory NumberField Set Topology
open scoped Classical ENNReal NumberField SchwartzMap

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

private abbrev X := mixedEmbedding.mixedSpace F
private abbrev d := Module.finrank ℚ F

/-- The Mellin value at one written in logarithmic coordinates. -/
def logProfileExponentialMoment (f : ℝ → ℂ) : ℂ :=
  ∫ t : ℝ, (Real.exp t : ℂ) * f t

theorem archModulus_zero : archModulus F (0 : X F) = 0 := by
  have h := archModulus_smul_of_pos F 2 (by norm_num) (0 : X F)
  rw [smul_zero] at h
  have hp : 1 < (2 : ℝ) ^ d F := one_lt_pow₀ (by norm_num) (Nat.ne_of_gt Module.finrank_pos)
  nlinarith [archModulus_nonneg F 0]

/-- The additive integral of a radial lift with a fixed nonnegative
transverse cutoff is proportional to its profile's exponential moment. -/
theorem exists_archimedeanLogRadius_integral_eq_moment
    (ψ : 𝓢(X F, ℂ)) (hψ : HasCompactSupport ψ)
    (hK : tsupport ψ ⊆ {x | 0 < archModulus F x})
    (hpos : ∀ x, ∃ r : ℝ, 0 ≤ r ∧ ψ x = (r : ℂ)) :
    ∃ c : ℝ, ∀ f : ℝ → ℂ, Measurable f →
      (∫ x : X F, ψ ((archModulusRadius F x)⁻¹ • x) * f (Real.log (archModulus F x))) =
        c * logProfileExponentialMoment f := by
  let r := archModulusRadius F
  let normOne (x : X F) := (r x)⁻¹ • x
  let t (x : X F) := Real.log (archModulus F x)
  let w (x : X F) := ENNReal.ofReal (ψ (normOne x)).re
  let μ := (volume : Measure (X F)).withDensity w
  let η := μ.map t
  let c := η (Iic 0)
  have hd : (0 : ℝ) < d F := by exact_mod_cast Module.finrank_pos (R := ℚ) (M := F)
  have hw : Measurable w :=
    (Complex.continuous_re.comp ψ.continuous).measurable.comp
      (((archModulusRadius_continuous F).measurable.inv).smul measurable_id) |>.ennreal_ofReal
  have ht : Measurable t := Real.measurable_log.comp (archModulus_continuous F).measurable
  have hψ₀ : ψ 0 = 0 := notMem_support.mp fun h ↦ by
    have hh : 0 < archModulus F (0 : X F) := hK (subset_closure h)
    rw [archModulus_zero] at hh
    exact (lt_irrefl 0) hh
  have hw₀ (x : X F) (hx : ¬ 0 < archModulus F x) : w x = 0 := by
    have hR : r x = 0 := le_antisymm
      (le_of_not_gt (fun h ↦ hx ((archModulusRadius_pos_iff F x).mp h)))
      (archModulusRadius_nonneg F x)
    simp [w, normOne, hR, hψ₀]
  have hScale (s : ℝ) :
      let a := Real.exp (s / (d F : ℝ))
      η (Iic 0) = ENNReal.ofReal (Real.exp (-s)) * η (Iic s) := by
    dsimp only
    let a := Real.exp (s / (d F : ℝ))
    have ha : 0 < a := Real.exp_pos _
    have hap : a ^ d F = Real.exp s := by
      rw [← Real.exp_nat_mul]
      congr 1
      rw [mul_comm, div_mul_cancel₀ _ hd.ne']
    let e := Homeomorph.smul (Units.mk0 a ha.ne') (α := X F)
    have he (x : X F) : e x = a • x := rfl
    have hnorm (x : X F) : normOne (e x) = normOne x := by
      rw [he]
      unfold normOne r
      rw [archModulusRadius_smul F a ha, mul_inv_rev, smul_smul, mul_assoc, inv_mul_cancel₀ ha.ne', mul_one]
    have hmod (x : X F) : archModulus F (e x) = Real.exp s * archModulus F x := by
      rw [he, archModulus_smul_of_pos F a ha, hap]
    let J (b : ℝ) : X F → ℝ≥0∞ := (t ⁻¹' Iic b).indicator w
    have hJ (x : X F) : J s (e x) = J 0 x := by
      by_cases hx : 0 < archModulus F x
      · have htt : t (e x) = s + t x := by
          unfold t
          rw [hmod, Real.log_mul (Real.exp_ne_zero _) hx.ne', Real.log_exp]
        simp only [J, indicator_apply, mem_preimage, mem_Iic, htt, add_le_iff_nonpos_right,
          w, hnorm]
      · have hxe : ¬ 0 < archModulus F (e x) := by
          rw [hmod]
          exact not_lt.mpr (mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (not_lt.mp hx))
        simp [J, indicator_apply, hw₀ _ hx, hw₀ _ hxe]
    have hmap : Measure.map (e : X F → X F) volume =
        ENNReal.ofReal (Real.exp (-s)) • (volume : Measure (X F)) := by
      change Measure.map (a • ·) volume = _
      rw [Measure.map_addHaar_smul volume ha.ne', mixedEmbedding.finrank, hap, ← Real.exp_neg,
        abs_of_pos (Real.exp_pos _)]
    have hApply (b : ℝ) : η (Iic b) = ∫⁻ x, J b x := by
      rw [Measure.map_apply ht measurableSet_Iic]
      dsimp only [μ]
      rw [withDensity_apply w (ht measurableSet_Iic), ← lintegral_indicator (ht measurableSet_Iic)]
    rw [hApply 0, hApply s]
    calc
      (∫⁻ x, J 0 x) = ∫⁻ x, J s (e x) :=
        lintegral_congr (fun x ↦ (hJ x).symm)
      _ = ∫⁻ x, J s x ∂Measure.map e volume :=
        (lintegral_map (hw.indicator (ht measurableSet_Iic)) e.continuous.measurable).symm
      _ = _ := by rw [hmap, lintegral_smul_measure, smul_eq_mul]
  have hC : c ≠ ∞ := by
    let K := (fun p : ℝ × X F ↦ p.1 • p.2) '' (Icc 0 1 ×ˢ tsupport ψ)
    have hCompact : IsCompact K :=
      (isCompact_Icc.prod hψ.isCompact).image (continuous_fst.smul continuous_snd)
    obtain ⟨B, hB⟩ := (hψ.isCompact.image (Complex.continuous_re.comp ψ.continuous)).bddAbove
    have hBound (x : X F) : (t ⁻¹' Iic 0).indicator w x ≤
        K.indicator (fun _ ↦ ENNReal.ofReal B) x := by
      by_cases hx : (t ⁻¹' Iic 0).indicator w x = 0
      · simp [hx]
      have ht₀ : t x ≤ 0 := by
        by_contra h
        exact hx (indicator_of_notMem (show x ∉ t ⁻¹' Iic 0 from h) _)
      rw [indicator_of_mem (show x ∈ t ⁻¹' Iic 0 from ht₀)] at hx
      have hp : 0 < archModulus F x := by
        by_contra hn
        exact hx (hw₀ x hn)
      have hr : 0 < r x := (archModulusRadius_pos_iff F x).mpr hp
      have hn : normOne x ∈ tsupport ψ := subset_closure (show ψ (normOne x) ≠ 0 from
        fun hz ↦ hx (by simp [w, hz]))
      have hlog : Real.log (r x) ≤ 0 := by
        have he := archModulusRadius_log F x
        exact nonpos_of_mul_nonpos_right (he.trans_le ht₀) hd
      have hmem : x ∈ K := by
        refine ⟨⟨r x, normOne x⟩, ⟨⟨hr.le, (Real.log_nonpos_iff hr.le).mp hlog⟩, hn⟩, ?_⟩
        change r x • ((r x)⁻¹ • x) = x
        rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
      rw [indicator_of_mem (show x ∈ t ⁻¹' Iic 0 from ht₀), indicator_of_mem hmem]
      exact ENNReal.ofReal_le_ofReal (hB ⟨normOne x, hn, rfl⟩)
    change η (Iic 0) ≠ ∞
    rw [Measure.map_apply ht measurableSet_Iic]
    dsimp only [μ]
    rw [withDensity_apply w (ht measurableSet_Iic), ← lintegral_indicator (ht measurableSet_Iic)]
    refine ne_top_of_le_ne_top ?_ (lintegral_mono hBound)
    rw [lintegral_indicator hCompact.isClosed.measurableSet, lintegral_const, Measure.restrict_apply_univ]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hCompact.measure_lt_top.ne
  have hη (s : ℝ) : η (Iic s) = c * ENNReal.ofReal (Real.exp s) := by
    have he := hScale s
    have h : ENNReal.ofReal (Real.exp s) * ENNReal.ofReal (Real.exp (-s)) = 1 := by
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, add_neg_cancel,
        Real.exp_zero, ENNReal.ofReal_one]
    calc
      η (Iic s) = 1 * η (Iic s) := (one_mul _).symm
      _ = ENNReal.ofReal (Real.exp s) * c := by rw [← h, mul_assoc, ← he]
      _ = _ := mul_comm _ _
  let ξ := (volume : Measure ℝ).withDensity (fun t ↦ ENNReal.ofReal (Real.exp t))
  have hξ (s : ℝ) : ξ (Iic s) = ENNReal.ofReal (Real.exp s) := by
    dsimp only [ξ]
    rw [withDensity_apply _ measurableSet_Iic]
    rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_exp_Iic s)
      (.of_forall fun x ↦ (Real.exp_pos x).le), integral_exp_Iic]
  have hμeq : η = c • ξ := by
    apply Measure.ext_of_Ioc' _ _ (fun a b _ ↦
      ne_top_of_le_ne_top (by rw [hη]; exact ENNReal.mul_ne_top hC ENNReal.ofReal_ne_top)
        (measure_mono Ioc_subset_Iic_self))
    intro a b hab
    have he (s : ℝ) : (c • ξ) (Iic s) = η (Iic s) := by
      rw [Measure.smul_apply, smul_eq_mul, hξ, hη]
    have hn (s : ℝ) : η (Iic s) ≠ ∞ := by
      rw [hη]; exact ENNReal.mul_ne_top hC ENNReal.ofReal_ne_top
    rw [← Iic_sdiff_Iic, measure_sdiff (Iic_subset_Iic.mpr hab.le) nullMeasurableSet_Iic (hn a),
      measure_sdiff (Iic_subset_Iic.mpr hab.le) nullMeasurableSet_Iic (by rw [he]; exact hn a), he, he]
  refine ⟨c.toReal, fun f hf ↦ ?_⟩
  have hleft : (∫ x : X F, ψ (normOne x) * f (t x)) = ∫ s, f s ∂η := by
    dsimp only [η]
    rw [integral_map ht.aemeasurable]
    · dsimp only [μ]
      rw [integral_withDensity_eq_integral_toReal_smul hw (.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
      apply integral_congr_ae (.of_forall fun x ↦ ?_)
      obtain ⟨r, hr, he⟩ := hpos (normOne x)
      rw [he, Complex.real_smul]
      simp [w, he, ENNReal.toReal_ofReal hr]
    · exact hf.aestronglyMeasurable
  rw [hleft, hμeq, integral_smul_measure, logProfileExponentialMoment]
  dsimp only [ξ]
  rw [integral_withDensity_eq_integral_toReal_smul Real.continuous_exp.measurable.ennreal_ofReal
    (.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (Real.exp_pos _).le, Complex.real_smul]

end

end Masullo
