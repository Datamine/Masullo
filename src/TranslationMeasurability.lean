import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.Seminorm
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Algebra.OpenSubgroup

open Filter MeasureTheory Set Topology
open scoped ENNReal Pointwise

namespace Masullo

/-- A rational linear complement of the rationals in the real line cannot be
measurable even in the completion of additive Haar measure. -/
theorem exists_nonNullMeasurable_ratSubmodule (μ : Measure ℝ) [μ.IsAddHaarMeasure] :
    ∃ H : Submodule ℚ ℝ, ¬NullMeasurableSet (H : Set ℝ) μ := by
  obtain ⟨H, hH⟩ := (Submodule.span ℚ {(1 : ℝ)}).exists_isCompl
  refine ⟨H, ?_⟩
  intro hm
  have hone : (1 : ℝ) ∉ H := fun h =>
    one_ne_zero (Submodule.disjoint_def.mp hH.disjoint 1
      (Submodule.mem_span_singleton_self 1) h)
  have hcover : (⋃ q : ℚ, (fun x : ℝ => x + q) ⁻¹' (H : Set ℝ)) = univ := by
    apply eq_univ_of_forall
    intro x
    have hx : x ∈ (Submodule.span ℚ {(1 : ℝ)}) ⊔ H := by rw [hH.sup_eq_top]; trivial
    obtain ⟨y, hy, z, hz, hsum⟩ := Submodule.mem_sup.mp hx
    obtain ⟨q, hq⟩ := Submodule.mem_span_singleton.mp hy
    have hq' : (q : ℝ) = y := by simpa [Rat.smul_def] using hq
    refine mem_iUnion.mpr ⟨-q, ?_⟩
    change x + ((-q : ℚ) : ℝ) ∈ H
    convert hz using 1
    rw [Rat.cast_neg, hq', ← hsum]
    ring
  have hpos : 0 < μ (H : Set ℝ) := by
    by_contra! h
    have hnull : μ (univ : Set ℝ) = 0 := by
      rw [← hcover]
      exact measure_iUnion_null fun q => by
        rw [measure_preimage_add_right μ (q : ℝ)]
        exact le_antisymm h bot_le
    exact (isOpen_univ.measure_pos μ univ_nonempty).ne' hnull
  obtain ⟨S, hSH, hS, hae⟩ := hm.exists_measurable_subset_ae_eq
  have hSpos : 0 < μ S := by rw [measure_congr hae]; exact hpos
  have hmem : (H : Set ℝ) ∈ 𝓝 (0 : ℝ) := by
    apply mem_of_superset (Measure.sub_mem_nhds_zero_of_addHaar_pos μ S hS hSpos)
    intro x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Set.mem_sub.mp hx
    exact H.sub_mem (hSH hy) (hSH hz)
  have hopen : IsOpen (H : Set ℝ) := H.toAddSubgroup.isOpen_of_mem_nhds hmem
  have hclopen : IsClopen (H : Set ℝ) :=
    ⟨H.toAddSubgroup.isClosed_of_isOpen hopen, hopen⟩
  have htop : (H : Set ℝ) = univ := hclopen.eq_univ ⟨0, H.zero_mem⟩
  apply hone
  change (1 : ℝ) ∈ (H : Set ℝ)
  rw [htop]
  trivial


open scoped BigOperators

private noncomputable abbrev RealL2 := Lp ℂ 2 (volume : Measure ℝ)
private noncomputable abbrev RealL2Operators := RealL2 →L[ℂ] RealL2

/-- Lebesgue-measure-preserving shift in log-modulus coordinates. -/
noncomputable def realL2Shift (t : ℝ) : RealL2Operators :=
  (Lp.compMeasurePreservingₗᵢ ℂ (· + t) (measurePreserving_add_right volume t)).toContinuousLinearMap

private theorem realL2Shift_norm_map (t : ℝ) (f : RealL2) :
    ‖realL2Shift t f‖ = ‖f‖ :=
  (Lp.compMeasurePreservingₗᵢ ℂ (· + t) (measurePreserving_add_right volume t)).norm_map f

private theorem realL2Shift_norm_le (t : ℝ) : ‖realL2Shift t‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun f => by rw [realL2Shift_norm_map, one_mul]

private theorem realL2Shift_ae (t : ℝ) (f : RealL2) :
    (fun x => realL2Shift t f x) =ᵐ[volume] fun x => f (x + t) :=
  Lp.coeFn_compMeasurePreserving f (measurePreserving_add_right volume t)

private theorem realL2Shift_ae_of (t : ℝ) (f : RealL2) (v : ℝ → ℂ)
    (h : (fun x => f x) =ᵐ[volume] v) :
    (fun x => realL2Shift t f x) =ᵐ[volume] fun x => v (x + t) :=
  (realL2Shift_ae t f).trans
    ((measurePreserving_add_right (volume : Measure ℝ) t).quasiMeasurePreserving.ae_eq_comp h)

private theorem realL2Shift_difference (t : ℝ) (S : Set ℝ)
    (ht : t ∉ S) (c : S →₀ ℂ) :
    1 ≤ ‖realL2Shift t - c.sum (fun i a => a • realL2Shift i)‖ := by
  classical
  let B : RealL2Operators := c.sum fun i a => a • realL2Shift i
  change 1 ≤ ‖realL2Shift t - B‖
  have hev : ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ i ∈ c.support, 2 * r < |t - (i : ℝ)| := by
    apply (eventually_all_finset c.support).mpr
    intro i hi
    have hne : t - (i : ℝ) ≠ 0 := sub_ne_zero.mpr fun h => ht (h ▸ i.property)
    have ho : IsOpen {r : ℝ | 2 * r < |t - (i : ℝ)|} :=
      isOpen_lt (continuous_const.mul continuous_id) continuous_const
    exact mem_nhdsWithin_of_mem_nhds (ho.mem_nhds (by simpa using abs_pos.mpr hne))
  obtain ⟨r, hr⟩ := (hev.and self_mem_nhdsWithin).exists
  have hrpos : 0 < r := hr.2
  let U := Metric.ball (0 : ℝ) r
  have hU : MeasurableSet U := Metric.isOpen_ball.measurableSet
  have hUvol : volume U = ENNReal.ofReal (2 * r) := Real.volume_ball 0 r
  have hUfin : volume U ≠ ∞ := hUvol.trans_ne ENNReal.ofReal_ne_top
  let f : RealL2 := indicatorConstLp 2 hU hUfin 1
  let v : ℝ → ℂ := U.indicator (fun _ => 1)
  have hf : (fun x => f x) =ᵐ[volume] v := indicatorConstLp_coeFn
  have hfpos : 0 < ‖f‖ := by
    rw [show f = indicatorConstLp 2 hU hUfin (1 : ℂ) from rfl,
      norm_indicatorConstLp (by norm_num) (by norm_num), norm_one, one_mul]
    apply Real.rpow_pos_of_pos
    rw [measureReal_def, hUvol, ENNReal.toReal_ofReal (by positivity)]
    positivity
  have hsum : (fun x => B f x) =ᵐ[volume]
      fun x => ∑ i ∈ c.support, c i • v (x + (i : ℝ)) := by
    have hB : B f = ∑ i ∈ c.support, c i • realL2Shift i f := by
      simp [B, Finsupp.sum]
    rw [hB]
    apply (Lp.coeFn_finsetSum _ _).trans
    have hparts : ∀ᶠ x in ae (volume : Measure ℝ), ∀ i ∈ c.support,
        (c i • realL2Shift (i : ℝ) f : RealL2) x = c i • v (x + (i : ℝ)) := by
      apply (eventually_all_finset c.support).mpr
      intro i hi
      exact (Lp.coeFn_smul _ _).trans ((realL2Shift_ae_of i f v hf).const_smul (c i))
    filter_upwards [hparts] with x hx
    simp only [Finset.sum_apply]
    exact Finset.sum_congr rfl hx
  have hsub := Lp.coeFn_sub (realL2Shift t f) (B f)
  have hle : ‖realL2Shift t f‖ ≤ ‖(realL2Shift t - B) f‖ := by
    apply Lp.norm_le_norm_of_ae_le
    change ∀ᵐ x ∂volume, ‖realL2Shift t f x‖ ≤ ‖(realL2Shift t f - B f : RealL2) x‖
    filter_upwards [hsub, hsum, realL2Shift_ae_of t f v hf] with x hxsub hxsum hxt
    simp only [Pi.sub_apply] at hxsub
    rw [hxsub, hxsum, hxt]
    by_cases hxtU : x + t ∈ U
    · have hxi (i : S) (hi : i ∈ c.support) : x + (i : ℝ) ∉ U := by
        intro hx
        have h1 : |x + t| < r := by simpa [U, Real.dist_eq] using hxtU
        have h2 : |x + (i : ℝ)| < r := by simpa [U, Real.dist_eq] using hx
        have hd : |t - (i : ℝ)| ≤ |x + t| + |x + (i : ℝ)| := by
          rw [show t - (i : ℝ) = (x + t) - (x + (i : ℝ)) from by ring]
          rw [sub_eq_add_neg]
          simpa only [abs_neg] using abs_add_le (x + t) (-(x + (i : ℝ)))
        linarith [hr.1 i hi]
      have hzero : (∑ i ∈ c.support, c i • v (x + (i : ℝ))) = 0 :=
        Finset.sum_eq_zero fun i hi => by simp [v, indicator_of_notMem (hxi i hi)]
      rw [hzero, sub_zero]
    · simp [v, indicator_of_notMem hxtU]
  have hop := hle.trans ((realL2Shift t - B).le_opNorm f)
  rw [realL2Shift_norm_map] at hop
  exact le_of_mul_le_mul_right (by simpa using hop) hfpos


/-- The distance to the span of the shifts indexed by `S` is a continuous operator
seminorm whose restriction to translations detects the complement of `S`. -/
theorem realL2Shift_seminorm_of_set (S : Set ℝ) :
    ∃ p : Seminorm ℂ RealL2Operators, Continuous p ∧
      (∀ t ∈ S, p (realL2Shift t) = 0) ∧ (∀ t ∉ S, p (realL2Shift t) = 1) := by
  let V : Submodule ℂ RealL2Operators := Submodule.span ℂ (range (fun t : S => realL2Shift t))
  let p : Seminorm ℂ RealL2Operators :=
    (normSeminorm ℂ (RealL2Operators ⧸ V)).comp V.mkQL.toLinearMap
  refine ⟨p, ?_, ?_, ?_⟩
  · apply p.continuous_of_forall
    intro r hr
    apply mem_of_superset (Metric.ball_mem_nhds (0 : RealL2Operators) hr)
    intro A hA
    rw [Metric.mem_ball, dist_zero_right] at hA
    change p (A - 0) < r
    rw [sub_zero]
    exact (Submodule.Quotient.norm_mk_le V A).trans_lt hA
  · intro t ht
    have htV : realL2Shift t ∈ V := Submodule.subset_span ⟨⟨t, ht⟩, rfl⟩
    change ‖((realL2Shift t : RealL2Operators) : RealL2Operators ⧸ V.toAddSubgroup)‖ = 0
    rw [QuotientAddGroup.norm_mk]
    exact (Metric.infDist_le_dist_of_mem htV).trans_eq (dist_self _)
      |>.antisymm Metric.infDist_nonneg
  · intro t ht
    change ‖(Submodule.Quotient.mk (realL2Shift t) : RealL2Operators ⧸ V)‖ = 1
    apply le_antisymm
    · exact (Submodule.Quotient.norm_mk_le V _).trans (realL2Shift_norm_le t)
    · change 1 ≤ ‖((realL2Shift t : RealL2Operators) : RealL2Operators ⧸ V.toAddSubgroup)‖
      rw [QuotientAddGroup.norm_mk]
      apply (Metric.le_infDist ⟨0, V.zero_mem⟩).mpr
      intro B hB
      obtain ⟨c, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp (show B ∈ V from hB)
      rw [dist_eq_norm]
      exact realL2Shift_difference t S ht c

/-- A continuous operator seminorm can fail Haar measurability on the translations
of (L^2(\mathbb R)), even when measurability is understood after completion. -/
theorem realL2Shift_continuous_seminorm_obstruction :
    ∃ p : Seminorm ℂ RealL2Operators, Continuous p ∧
      ¬AEMeasurable (fun t => p (realL2Shift t)) volume := by
  obtain ⟨H, hH⟩ := exists_nonNullMeasurable_ratSubmodule (volume : Measure ℝ)
  obtain ⟨p, hp, hzero, hone⟩ := realL2Shift_seminorm_of_set (H : Set ℝ)
  refine ⟨p, hp, fun hm => hH ?_⟩
  have heq : (fun t => p (realL2Shift t)) ⁻¹' ({0} : Set ℝ) = (H : Set ℝ) := by
    ext t
    constructor
    · intro ht
      by_contra h
      have hz : p (realL2Shift t) = 0 := ht
      rw [hone t h] at hz
      exact one_ne_zero hz
    · exact fun h => hzero t h
  rw [← heq]
  exact hm.nullMeasurableSet_preimage (measurableSet_singleton 0)

end Masullo
