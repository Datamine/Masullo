import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.Cone.Extension
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.Topology.ContinuousMap.Compact

open Function MeasureTheory Set Topology
open scoped ENNReal CompactlySupported

namespace Masullo

noncomputable section

variable {K D : Type*} [TopologicalSpace K] [T2Space K] [CompactSpace K] [Nonempty K]
variable [MeasurableSpace K] [BorelSpace K]
variable [AddCommGroup D] [Module ℝ D]

/-- A real functional dominated by the supremum of the associated real
continuous functions is represented by a Radon probability. -/
theorem probability_of_supremum_domination (A : D →ₗ[ℝ] C(K, ℝ)) (l : D →ₗ[ℝ] ℝ)
    (h : ∀ x, l x ≤ ⨆ k, A x k) :
    ∃ μ : Measure K, μ.Regular ∧ μ univ = 1 ∧ ∀ x, l x = ∫ k, A x k ∂μ := by
  let P (f : C(K, ℝ)) : ℝ := ⨆ k, f k
  have hbounded (f : C(K, ℝ)) : BddAbove (range f) :=
    (isCompact_range f.continuous).bddAbove
  have hone : P 1 = 1 := by simp [P]
  have hnegone : P (-1) = -1 := by simp [P]
  have hadd (f g : C(K, ℝ)) : P (f + g) ≤ P f + P g := by
    apply ciSup_le
    intro k
    exact add_le_add (le_ciSup (hbounded f) k) (le_ciSup (hbounded g) k)
  have hsmul (a : ℝ) (ha : 0 < a) (f : C(K, ℝ)) : P (a • f) = a • P f := by
    apply le_antisymm
    · apply ciSup_le
      intro k
      exact mul_le_mul_of_nonneg_left (le_ciSup (hbounded f) k) ha.le
    · change a * P f ≤ _
      apply (le_div_iff₀' ha).mp
      apply ciSup_le
      intro k
      apply (le_div_iff₀' ha).mpr
      exact le_ciSup (hbounded (a • f)) k
  have hker : A.ker ≤ l.ker := by
    intro x hx
    have hx' : A x = 0 := hx
    have ha := h x
    have hb := h (-x)
    rw [hx'] at ha
    rw [map_neg, map_neg, hx', neg_zero] at hb
    simp only [ContinuousMap.zero_apply, ciSup_const] at ha hb
    exact le_antisymm ha (by linarith)
  let Q := A.ker
  let R := A.range
  let g : R →ₗ[ℝ] ℝ := (Q.liftQ l hker).comp A.quotKerEquivRange.symm.toLinearMap
  have hg (x : D) : g ⟨A x, x, rfl⟩ = l x := by
    exact congrArg (Q.liftQ l hker)
      (A.quotKerEquivRange_symm_apply_image x (LinearMap.mem_range_self A x))
  have hdom (f : R) : g f ≤ P (f : C(K, ℝ)) := by
    obtain ⟨f, x, rfl⟩ := f
    rw [hg]
    exact h x
  obtain ⟨L, hL, hLP⟩ := exists_extension_of_le_sublinear ⟨R, g⟩ P hsmul hadd hdom
  have hL0 (f : C(K, ℝ)) (hf : 0 ≤ f) : 0 ≤ L f := by
    have hle : P (-f) ≤ 0 := by
      apply ciSup_le
      intro k
      exact neg_nonpos.mpr (hf k)
    have hbound := (hLP (-f)).trans hle
    rw [map_neg] at hbound
    exact neg_nonpos.mp hbound
  have hLone : L 1 = 1 := by
    apply le_antisymm ((hLP 1).trans_eq hone)
    have he := (hLP (-1)).trans_eq hnegone
    rw [map_neg] at he
    linarith
  let Λ : (K →C_c ℝ) →ₚ[ℝ] ℝ :=
    { toFun := fun f => L f.toContinuousMap
      map_add' := fun f g => L.map_add _ _
      map_smul' := fun c f => L.map_smul c f.toContinuousMap
      monotone' := fun f g hfg => by
        have hh := hL0 (g.toContinuousMap - f.toContinuousMap) (fun x => sub_nonneg.mpr (hfg x))
        rw [map_sub] at hh
        exact sub_nonneg.mp hh }
  let μ := RealRMK.rieszMeasure Λ
  refine ⟨μ, inferInstance, ?_, ?_⟩
  · let one : K →C_c ℝ := ⟨1, HasCompactSupport.of_compactSpace 1⟩
    have hmass := RealRMK.integral_rieszMeasure Λ one
    change (∫ _ : K, (1 : ℝ) ∂μ) = L 1 at hmass
    rw [integral_const, smul_eq_mul, mul_one, hLone, measureReal_def] at hmass
    exact (ENNReal.toReal_eq_one_iff _).mp hmass
  · intro x
    let f : K →C_c ℝ := ⟨A x, HasCompactSupport.of_compactSpace (A x)⟩
    have hf := RealRMK.integral_rieszMeasure Λ f
    change (∫ k, A x k ∂μ) = L (A x) at hf
    rw [hf]
    exact (hg x).symm.trans (hL ⟨A x, x, rfl⟩).symm

end

section ComplexRepresentation

abbrev ComplexUnitDisk := ↥(Metric.closedBall (0 : ℂ) 1)

private theorem exists_disk_rotation (z : ℂ) :
    ∃ a : ComplexUnitDisk, ((a : ℂ) * z).re = ‖z‖ := by
  by_cases hz : z = 0
  · exact ⟨⟨0, by simp [Metric.mem_closedBall]⟩, by simp [hz]⟩
  have hp : 0 < ‖z‖ := norm_pos_iff.mpr hz
  let a : ℂ := star z / (‖z‖ : ℂ)
  have ha : ‖a‖ = 1 := by
    dsimp [a]
    rw [norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp, div_self hp.ne']
  refine ⟨⟨a, by simp [Metric.mem_closedBall, dist_zero_right, ha]⟩, ?_⟩
  change (a * z).re = _
  have he : a * z = (‖z‖ : ℂ) := by
    change (star z / (‖z‖ : ℂ)) * z = _
    rw [div_mul_eq_mul_div]
    change (starRingEnd ℂ z * z) / (‖z‖ : ℂ) = _
    rw [Complex.conj_mul', pow_two, mul_div_cancel_right₀ _ (by exact_mod_cast hp.ne')]
  rw [he, Complex.ofReal_re]

variable {K D : Type*} [TopologicalSpace K] [T2Space K] [CompactSpace K] [Nonempty K]
variable [AddCommGroup D] [Module ℂ D]

/-- A complex functional dominated by a supremum norm admits a positive
Radon probability representation after adjoining phases in the unit disk. -/
theorem probability_with_disk_of_norm_domination (A : D →ₗ[ℂ] C(K, ℂ)) (l : D →ₗ[ℂ] ℂ)
    (h : ∀ x, ‖l x‖ ≤ ‖A x‖) :
    letI : MeasurableSpace (K × ComplexUnitDisk) := borel _
    ∃ μ : Measure (K × ComplexUnitDisk), μ.Regular ∧ μ univ = 1 ∧
      ∀ x, l x = ∫ k, (k.2 : ℂ) * A x k.1 ∂μ := by
  letI : MeasurableSpace (K × ComplexUnitDisk) := borel _
  letI : BorelSpace (K × ComplexUnitDisk) := ⟨rfl⟩
  letI : CompactSpace ComplexUnitDisk := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  letI : Nonempty ComplexUnitDisk := ⟨⟨0, by simp [Metric.mem_closedBall]⟩⟩
  let R : D →ₗ[ℝ] C(K × ComplexUnitDisk, ℝ) :=
    { toFun := fun x => ⟨fun k => ((k.2 : ℂ) * A x k.1).re,
        Complex.continuous_re.comp ((continuous_subtype_val.comp continuous_snd).mul
          ((A x).continuous.comp continuous_fst))⟩
      map_add' := fun x y => ContinuousMap.ext fun k => by simp [mul_add, Complex.add_re]
      map_smul' := fun c x => ContinuousMap.ext fun k => by
        change ((k.2 : ℂ) * A ((c : ℂ) • x) k.1).re = c * ((k.2 : ℂ) * A x k.1).re
        rw [map_smul]
        change ((k.2 : ℂ) * ((c : ℂ) * A x k.1)).re = _
        rw [mul_left_comm, Complex.re_ofReal_mul] }
  let m : D →ₗ[ℝ] ℝ := Complex.reLm.comp (l.restrictScalars ℝ)
  have hR (x : D) : m x ≤ ⨆ k, R x k := by
    refine (Complex.re_le_norm (l x)).trans ((h x).trans ?_)
    apply (ContinuousMap.norm_le_of_nonempty (A x)).mpr
    intro k
    obtain ⟨a, ha⟩ := exists_disk_rotation (A x k)
    rw [← ha]
    exact le_ciSup (isCompact_range (R x).continuous).bddAbove (k, a)
  obtain ⟨μ, hμ, hmass, hrepr⟩ := probability_of_supremum_domination R m hR
  letI : IsProbabilityMeasure μ := ⟨hmass⟩
  refine ⟨μ, hμ, hmass, fun x => ?_⟩
  have hc : Continuous (fun k : K × ComplexUnitDisk => (k.2 : ℂ) * A x k.1) :=
    (continuous_subtype_val.comp continuous_snd).mul ((A x).continuous.comp continuous_fst)
  have hint := hc.integrable_of_hasCompactSupport (μ := μ) (HasCompactSupport.of_compactSpace _)
  apply Complex.ext
  · exact (hrepr x).trans (integral_re hint)
  · have hi := hrepr (-Complex.I • x)
    change (l (-Complex.I • x)).re =
      ∫ k : K × ComplexUnitDisk, ((k.2 : ℂ) * A (-Complex.I • x) k.1).re ∂μ at hi
    have he (z : ℂ) : (-Complex.I * z).re = z.im := by simp [Complex.mul_re]
    have hi' : (l x).im = ∫ k : K × ComplexUnitDisk, ((k.2 : ℂ) * A x k.1).im ∂μ := by
      simpa only [map_smul, smul_eq_mul, ContinuousMap.smul_apply, mul_left_comm (b := -Complex.I), he] using hi
    exact hi'.trans (integral_im hint)

end ComplexRepresentation

end Masullo
