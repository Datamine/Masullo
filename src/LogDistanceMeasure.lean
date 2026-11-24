import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Topology.MetricSpace.Lipschitz

open Filter MeasureTheory Metric Set
open scoped Classical ENNReal

namespace Masullo

/-- The nonnegative part of the logarithmic loss near a zero ordinate.
The ordinate itself is handled by removing a finite set of measure zero. -/
noncomputable def logDistanceLoss (c t : ℝ) : ℝ := max 0 (-Real.log |t - c|)

private theorem logDistanceLoss_nonneg (c t : ℝ) : 0 ≤ logDistanceLoss c t := le_max_left _ _

private theorem logDistanceLoss_measurable (c : ℝ) : Measurable (logDistanceLoss c) :=
  measurable_const.max (Real.measurable_log.comp
    (continuous_abs.measurable.comp (measurable_id.sub_const c))).neg

private theorem logDistanceLoss_data (c : ℝ) :
    Integrable (logDistanceLoss c) volume ∧ ∫ t, logDistanceLoss c t = 2 := by
  let S := Icc (c - 1) (c + 1)
  have hcomp : ∀ t : ℝ, t ∈ S → logDistanceLoss c t = -Real.log (t - c) := by
    intro t ht
    have ht₀ : |t - c| ≤ 1 := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
    rw [logDistanceLoss, max_eq_right (neg_nonneg.mpr (Real.log_nonpos (abs_nonneg _) ht₀)),
      Real.log_abs]
  have hsupp : ∀ t : ℝ, t ∉ S → logDistanceLoss c t = 0 := by
    intro t ht
    have ht₀ : 1 ≤ |t - c| := by
      by_contra! h
      exact ht ⟨by linarith [(abs_lt.mp h).1], by linarith [(abs_lt.mp h).2]⟩
    exact max_eq_left (neg_nonpos.mpr (Real.log_nonneg ht₀))
  have hi : IntervalIntegrable (fun t : ℝ ↦ -Real.log (t - c)) volume (c - 1) (c + 1) := by
    have hl : IntervalIntegrable (fun t : ℝ ↦ -Real.log t) volume (-1) 1 :=
      (intervalIntegral.intervalIntegrable_log' (a := -1) (b := 1)).neg
    convert hl.comp_sub_right c using 1 <;> ring
  have hi' : IntegrableOn (fun t : ℝ ↦ -Real.log (t - c)) S volume :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith : c - 1 ≤ c + 1)).mp hi
  have hmeas : MeasurableSet S := measurableSet_Icc
  refine ⟨(integrableOn_iff_integrable_of_support_subset (fun t ht ↦ by
    by_contra hn; exact ht (hsupp t hn))).mp (hi'.congr_fun (fun t ht ↦ (hcomp t ht).symm) hmeas), ?_⟩
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hsupp]
  rw [setIntegral_congr_fun hmeas hcomp, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (show c - 1 ≤ c + 1 by linarith),
    intervalIntegral.integral_comp_sub_right (f := fun t ↦ -Real.log t)]
  have h₁ : c - 1 - c = -1 := by ring
  have h₂ : c + 1 - c = 1 := by ring
  rw [h₁, h₂, intervalIntegral.integral_neg, integral_log]
  norm_num

private theorem extend_exceptional_set {E : Set ℝ} {T v : ℝ}
    (hE : MeasurableSet E) (hsub : E ⊆ Icc T (T + 1))
    (hv : volume.real E ≤ v) (hv₁ : v ≤ 1) :
    ∃ D : Set ℝ, MeasurableSet D ∧ E ⊆ D ∧ D ⊆ Icc T (T + 1) ∧ volume D = ENNReal.ofReal v := by
  let I := Icc T (T + 1)
  let G (x : ℝ) := E ∪ (Iic x ∩ I)
  let g (x : ℝ) := volume.real (G x)
  have hG (x : ℝ) : G x ⊆ I := union_subset hsub inter_subset_right
  have hvol : volume I = 1 := by simp [I]
  have hGfin (x : ℝ) : volume (G x) < ∞ :=
    lt_of_le_of_lt (measure_mono (hG x)) (by simp [hvol])
  have hUpper (x y : ℝ) (hxy : y ≤ x) :
      g x ≤ g y + (x - y) := by
    have hs : G x ⊆ G y ∪ Ioc y x := by
      rintro z (he | ⟨hz, hI⟩)
      · exact Or.inl (Or.inl he)
      · by_cases hy : z ≤ y
        · exact Or.inl (Or.inr ⟨hy, hI⟩)
        · exact Or.inr ⟨lt_of_not_ge hy, hz⟩
    have hfin : volume (G y ∪ Ioc y x) ≠ ∞ :=
      (measure_union_lt_top (hGfin y) (by simp only [Real.volume_Ioc, ENNReal.ofReal_lt_top])).ne
    exact (measureReal_mono hs hfin).trans ((measureReal_union_le _ _).trans_eq
      (by rw [Real.volume_real_Ioc_of_le hxy]))
  have hmono : Monotone g := fun x y hxy ↦
    measureReal_mono (union_subset_union_right _ (inter_subset_inter_left _ (Iic_subset_Iic.mpr hxy)))
      (by have h := measure_mono (μ := volume) (hG y); rw [hvol] at h; exact ne_top_of_le_ne_top (by simp) h)
  have hg : Continuous g := (show LipschitzWith 1 g from LipschitzWith.of_le_add fun x y ↦ by
    by_cases hxy : y ≤ x
    · rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hxy)]
      exact hUpper x y hxy
    · exact (hmono (le_of_not_ge hxy)).trans (le_add_of_nonneg_right dist_nonneg)).continuous
  have hstart : g T ≤ v := by
    have hi : Iic T ∩ I = {T} := by
      ext x
      constructor
      · rintro ⟨hx, hx'⟩
        exact mem_singleton_iff.mpr (le_antisymm hx hx'.1)
      · intro hx
        obtain rfl := mem_singleton_iff.mp hx
        exact ⟨mem_Iic.mpr le_rfl, ⟨le_rfl, by linarith⟩⟩
    have hh := measureReal_union_le (μ := volume) E ({T} : Set ℝ)
    have hzero : volume.real ({T} : Set ℝ) = 0 := by simp [measureReal_def]
    rw [hzero, add_zero] at hh
    exact (show g T ≤ volume.real E by simpa only [g, G, hi] using hh).trans hv
  have hend : g (T + 1) = 1 := by
    have hi : Iic (T + 1) ∩ I = I := inter_eq_right.mpr fun x hx ↦ hx.2
    change volume.real (E ∪ (Iic (T + 1) ∩ I)) = 1
    rw [hi, union_eq_right.mpr hsub, measureReal_def, hvol, ENNReal.toReal_one]
  obtain ⟨x, _, hx⟩ := intermediate_value_Icc (show T ≤ T + 1 by linarith) hg.continuousOn
    (show v ∈ Icc (g T) (g (T + 1)) from ⟨hstart, by rw [hend]; exact hv₁⟩)
  refine ⟨G x, hE.union (measurableSet_Iic.inter measurableSet_Icc), subset_union_left, hG x, ?_⟩
  have hfin : volume (G x) ≠ ∞ := ne_top_of_le_ne_top (by simp [hvol]) (measure_mono (hG x))
  rw [← hx, show g x = (volume (G x)).toReal from rfl, ENNReal.ofReal_toReal hfin]

/-- The weighted sum of logarithmic losses is less than `2 M B` away
from a set of measure `1/B`, where `M` bounds the total multiplicity. -/
theorem logDistanceLoss_off_exception {ι : Type*} (Z : Finset ι) (γ : ι → ℝ) (m : ι → ℕ)
    {M B T : ℝ} (hM : 0 < M) (hcount : (∑ i ∈ Z, (m i : ℝ)) ≤ M) (hB : 1 < B) :
    ∃ E : Set ℝ, MeasurableSet E ∧ E ⊆ Icc T (T + 1) ∧ volume E = ENNReal.ofReal (1 / B) ∧
      ∀ t ∈ Icc T (T + 1) \ E, (∀ i ∈ Z, t ≠ γ i) ∧
        (∑ i ∈ Z, (m i : ℝ) * logDistanceLoss (γ i) t) < 2 * M * B := by
  let I := Icc T (T + 1)
  let p (t : ℝ) := ∑ i ∈ Z, (m i : ℝ) * logDistanceLoss (γ i) t
  let K := 2 * M * B
  have hK : 0 < K := by dsimp [K]; positivity
  let A := {t | K ≤ p t}
  let X := γ '' (Z : Set ι)
  let E₀ := (A ∪ X) ∩ I
  have hp : Integrable p volume := integrable_finsetSum _ fun i _ ↦ (logDistanceLoss_data (γ i)).1.const_mul _
  have hp₀ : ∀ t, 0 ≤ p t := fun t ↦ Finset.sum_nonneg fun i _ ↦
    mul_nonneg (Nat.cast_nonneg _) (logDistanceLoss_nonneg _ _)
  have hmeasP : Measurable p := Finset.measurable_sum _ fun i _ ↦ (logDistanceLoss_measurable _).const_mul _
  have hXm : X.Finite := Z.finite_toSet.image _
  have hX : volume X = 0 := hXm.measure_zero _
  have hi : ∫ t, p t = 2 * ∑ i ∈ Z, (m i : ℝ) := by
    dsimp only [p]
    rw [integral_finsetSum _ (fun i _ ↦ (logDistanceLoss_data (γ i)).1.const_mul _), Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [integral_const_mul, (logDistanceLoss_data (γ i)).2, mul_comm]
  let μ := volume.restrict I
  have hmeasA : MeasurableSet A := hmeasP measurableSet_Ici
  have hAX : MeasurableSet (A ∪ X) := hmeasA.union hXm.measurableSet
  have hi' : (∫ t, p t ∂μ) ≤ 2 * M :=
    (integral_mono_measure (Measure.restrict_le_self : μ ≤ volume) (ae_of_all _ hp₀) hp).trans
      (hi.trans_le (mul_le_mul_of_nonneg_left hcount (by norm_num)))
  have hA : μ.real A ≤ 1 / B := by
    have hmarkov := mul_meas_ge_le_integral_of_nonneg (ae_of_all μ hp₀) (hp.mono_measure Measure.restrict_le_self) K
    have h := hmarkov.trans hi'
    apply (le_div_iff₀ (zero_lt_one.trans hB)).2
    change (2 * M * B) * μ.real A ≤ 2 * M at h
    nlinarith
  have hX' : μ.real X = 0 := by
    have hm := (Measure.restrict_le_self : μ ≤ volume) X
    rw [hX, le_zero_iff] at hm
    change (μ X).toReal = 0
    rw [show μ X = 0 from hm, ENNReal.toReal_zero]
  have hVolE : volume.real E₀ ≤ 1 / B := by
    have h : μ.real (A ∪ X) = volume.real E₀ := by
      simp only [measureReal_def, μ, Measure.restrict_apply hAX, E₀]
    rw [← h]
    exact (measureReal_union_le _ _).trans (by simpa only [hX', add_zero] using hA)
  obtain ⟨E, hE, hE₀, hEI, hEV⟩ :=
    extend_exceptional_set ((hmeasP measurableSet_Ici).union hXm.measurableSet |>.inter measurableSet_Icc)
      (inter_subset_right : E₀ ⊆ I) hVolE (by simpa using one_div_le_one_div_of_le zero_lt_one hB.le)
  refine ⟨E, hE, hEI, hEV, fun t ht ↦ ?_⟩
  have hn : t ∉ A ∪ X := fun h ↦ ht.2 (hE₀ ⟨h, ht.1⟩)
  refine ⟨fun i hi he ↦ hn (Or.inr ⟨i, hi, he.symm⟩), lt_of_not_ge (fun h ↦ hn (Or.inl h))⟩

end Masullo
