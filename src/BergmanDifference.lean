import ExponentialDecayStructure
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul

open Filter Function MeasureTheory Set Topology
open scoped ENNReal NNReal SchwartzMap

noncomputable section

namespace Masullo

local notation "B" => SchwartzBergman (Set.univ : Set ℝ)

private def nonzeroAbscissa (n : ℕ) : (Set.univ : Set ℝ) :=
  ⟨if Even n then (n : ℝ) + 1 else -((n : ℝ) + 1), mem_univ _⟩

private theorem nonzeroAbscissa_ne_zero (n : ℕ) : (nonzeroAbscissa n : ℝ) ≠ 0 := by
  change (if Even n then (n : ℝ) + 1 else -((n : ℝ) + 1)) ≠ 0
  split
  · positivity
  · exact neg_ne_zero.mpr (by positivity)

private theorem nonzeroAbscissa_brackets (x : (Set.univ : Set ℝ)) :
    (∃ n, (nonzeroAbscissa n : ℝ) < x.val) ∧ ∃ n, x.val < (nonzeroAbscissa n : ℝ) := by
  obtain ⟨N, hN⟩ := exists_nat_gt |x.val|
  have hE : Even (2 * N) := ⟨N, by omega⟩
  have hO : ¬ Even (2 * N + 1) := N.not_even_two_mul_add_one
  constructor
  · refine ⟨2 * N + 1, ?_⟩
    change (if Even (2 * N + 1) then _ else _) < x.val
    rw [ite_eq_right hO]
    push_cast
    linarith [neg_abs_le x.val]
  · refine ⟨2 * N, ?_⟩
    change x.val < (if Even (2 * N) then _ else _)
    rw [ite_eq_left hE]
    push_cast
    linarith [le_abs_self x.val]

/-- A continuous linear endomorphism of the entire Schwartz–Bergman space
is a closed embedding when multiplication on each noncentral vertical line
has an inverse bound uniform in height. -/
theorem bergman_isClosedEmbedding_of_vertical_lowerBound (D : B →L[ℂ] B)
    (hD : ∀ a : ℝ, a ≠ 0 → ∃ C : ℝ≥0, ∀ F : B, ∀ y : ℝ,
      ‖F.val ((a : ℂ) + (y : ℂ) * Complex.I)‖ ≤
        (C : ℝ) * ‖(D F).val ((a : ℂ) + (y : ℂ) * Complex.I)‖) :
    IsClosedEmbedding D := by
  have hN : (Set.univ : Set ℝ).Nonempty := ⟨0, mem_univ _⟩
  obtain ⟨_, P, hP, hval⟩ := schwartzBergman_lp_generates univ isOpen_univ
    ordConnected_univ hN nonzeroAbscissa nonzeroAbscissa_brackets 2 (by norm_num) (by norm_num)
  have hbound (i : ℕ × ℕ) : ∃ C : ℝ≥0, ∀ F : B, P i F ≤ C * P i (D F) := by
    obtain ⟨C, hC⟩ := hD (nonzeroAbscissa i.1) (nonzeroAbscissa_ne_zero i.1)
    refine ⟨C, fun F ↦ ?_⟩
    have hC₀ : 0 ≤ (C : ℝ) * P i (D F) := mul_nonneg C.coe_nonneg (apply_nonneg _ _)
    apply (ENNReal.ofReal_le_ofReal_iff hC₀).mp
    rw [ENNReal.ofReal_mul C.coe_nonneg, hval, hval]
    have hnorm (y : ℝ) :
        ‖weightedVerticalTrace (nonzeroAbscissa i.1) i.2 F.val y‖ ≤
          ‖(C : ℝ) • weightedVerticalTrace (nonzeroAbscissa i.1) i.2 (D F).val y‖ := by
      simp only [weightedVerticalTrace, norm_mul, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg C.coe_nonneg]
      simpa only [mul_left_comm (C : ℝ)] using
        mul_le_mul_of_nonneg_left (hC F y) (norm_nonneg _)
    refine (eLpNorm_mono hnorm).trans ?_
    let G : ℝ → ℂ := weightedVerticalTrace (nonzeroAbscissa i.1) i.2 (D F).val
    change eLpNorm ((C : ℝ) • G) 2 volume ≤ ENNReal.ofReal (C : ℝ) * eLpNorm G 2 volume
    rw [eLpNorm_const_smul, ← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg C.coe_nonneg]
  have hF := schwartzBergman_frechet univ isOpen_univ ordConnected_univ hN
  have hU := positiveRealExponentialDecay_isEmbedding (Set.univ : Set ℝ) hN
  let e := positiveRealFourierMellin univ isOpen_univ ordConnected_univ hN
  letI : T2Space (PositiveRealExponentialDecay univ) := hU.t2Space
  letI : T2Space B := e.symm.toHomeomorph.isEmbedding.t2Space
  letI : CompleteSpace B := hF.choose_spec.2.2
  have hi : Injective D := by
    intro F G h
    apply sub_eq_zero.mp
    by_contra hf
    obtain ⟨i, hi⟩ := hP.separating_of_T1 (F - G) hf
    obtain ⟨C, hC⟩ := hbound i
    have hh := hC (F - G)
    have hz : D (F - G) = 0 := by rw [map_sub, h, sub_self]
    rw [hz, map_zero, mul_zero] at hh
    exact hi (hh.antisymm (apply_nonneg _ _))
  let R := D.toLinearMap.range
  let E := LinearEquiv.ofInjective D.toLinearMap hi
  have hinv : Continuous E.symm := by
    apply hP.continuous_of_continuous_comp E.symm.toLinearMap
    intro i
    obtain ⟨C, hC⟩ := hbound i
    apply Seminorm.continuous_of_le
      (q := C • (P i).comp R.subtype)
      (((hP.continuous_seminorm i).comp continuous_subtype_val).const_smul C)
    intro x
    obtain ⟨F, rfl⟩ := E.surjective x
    change P i (E.symm (E F)) ≤ (C : ℝ) * P i (D F)
    rw [E.symm_apply_apply]
    exact hC F
  let E₁ : B ≃L[ℂ] R := ⟨E, D.continuous.subtype_mk _, hinv⟩
  have hE : IsEmbedding D := IsEmbedding.subtypeVal.comp E₁.toHomeomorph.isEmbedding
  exact (AddMonoidHom.isUniformEmbedding_of_isEmbedding
    (f := D.toLinearMap.toAddMonoidHom) hE).isClosedEmbedding

/-- On a noncentral line the cyclic Mellin multiplier is bounded away
from zero by the difference of the two moduli. -/
theorem bergman_cyclicMultiplier_lowerBound (d a : ℝ) (hd : 0 < d) (ha : a ≠ 0)
    (c : Circle) :
    ∃ C : ℝ≥0, ∀ y : ℝ, 1 ≤ (C : ℝ) *
      ‖1 - (c : ℂ) * Complex.exp (-((d : ℂ) * ((a : ℂ) + (y : ℂ) * Complex.I)))‖ := by
  let δ := |1 - Real.exp (-(d * a))|
  have hδ : 0 < δ := by
    apply abs_pos.mpr
    intro h
    have he : Real.exp (-(d * a)) = 1 := (sub_eq_zero.mp h).symm
    have hz := Real.exp_injective (he.trans Real.exp_zero.symm)
    exact (mul_ne_zero hd.ne' ha) (neg_eq_zero.mp hz)
  refine ⟨⟨δ⁻¹, inv_nonneg.mpr hδ.le⟩, fun y ↦ ?_⟩
  have hz : (-((d : ℂ) * ((a : ℂ) + (y : ℂ) * Complex.I))).re = -(d * a) := by
    simp [Complex.mul_re, Complex.add_re]
  have hb := abs_norm_sub_norm_le (1 : ℂ)
    ((c : ℂ) * Complex.exp (-((d : ℂ) * ((a : ℂ) + (y : ℂ) * Complex.I))))
  rw [norm_one, norm_mul, Circle.norm_coe, one_mul, Complex.norm_exp, hz] at hb
  exact (inv_mul_cancel₀ hδ.ne').ge.trans (mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hδ.le))


local notation "X" => PositiveRealExponentialDecay (Set.univ : Set ℝ)
local notation "U" => (Set.univ : Set ℝ)
local instance : ContinuousSMul ℂ X := (PolynormableSpace.withSeminorms ℂ X).continuousSMul
private theorem allReal_nonempty : (Set.univ : Set ℝ).Nonempty := ⟨0, mem_univ _⟩
private def entireMellin : X ≃L[ℂ] B :=
  positiveRealFourierMellin U isOpen_univ ordConnected_univ allReal_nonempty

/-- The entire Mellin transform on logarithmic profiles with all weights. -/
abbrev entireLogMellin : X ≃L[ℂ] B := entireMellin

/-- Logarithmic translation on the entire exponential Schwartz space. -/
def exponentialSchwartzTranslation (d : ℝ) : X →L[ℂ] X :=
  logExponentialDecayTranslation U allReal_nonempty d

@[simp] theorem exponentialSchwartzTranslation_apply (d : ℝ) (f : X) (x : ℝ) :
    (exponentialSchwartzTranslation d f).val x = f.val (x + d) := rfl

theorem entireMellin_translation (d : ℝ) (f : X) (z : ℂ) :
    (entireMellin (exponentialSchwartzTranslation d f)).val z =
      Complex.exp (-((d : ℂ) * z)) * (entireMellin f).val z := by
  unfold entireMellin
  rw [positiveRealFourierMellin_apply _ _ _ _ _ _ (mem_univ _),
    positiveRealFourierMellin_apply _ _ _ _ _ _ (mem_univ _),
    mellin_eq_log_integral, mellin_eq_log_integral, ← integral_const_mul]
  simp only [Real.log_exp, exponentialSchwartzTranslation_apply]
  rw [← integral_add_right_eq_self
    (fun x : ℝ ↦ Complex.exp (-((d : ℂ) * z)) * (Complex.exp (z * (x : ℂ)) * f.val x)) d]
  apply integral_congr_ae
  filter_upwards with x
  rw [← mul_assoc, ← Complex.exp_add]
  push_cast
  rw [show -((d : ℂ) * z) + z * ((x : ℂ) + d) = z * x by ring]

/-- A translation difference with a unitary phase has closed range and
is a topological embedding on the two-sided exponential Schwartz space. -/
theorem exponentialSchwartzDifference_isClosedEmbedding (d : ℝ) (hd : 0 < d) (c : Circle) :
    IsClosedEmbedding (ContinuousLinearMap.id ℂ X - (c : ℂ) • exponentialSchwartzTranslation d) := by
  let D := ContinuousLinearMap.id ℂ X - (c : ℂ) • exponentialSchwartzTranslation d
  let L := entireMellin.toContinuousLinearMap.comp (D.comp entireMellin.symm.toContinuousLinearMap)
  have hL (F : B) (z : ℂ) :
      (L F).val z = (1 - (c : ℂ) * Complex.exp (-((d : ℂ) * z))) * F.val z := by
    change (entireMellin (entireMellin.symm F - (c : ℂ) • exponentialSchwartzTranslation d
      (entireMellin.symm F))).val z = _
    rw [map_sub, map_smul, entireMellin.apply_symm_apply]
    change F.val z - (c : ℂ) * (entireMellin (exponentialSchwartzTranslation d (entireMellin.symm F))).val z = _
    rw [entireMellin_translation, entireMellin.apply_symm_apply]
    ring
  have hC : IsClosedEmbedding L := bergman_isClosedEmbedding_of_vertical_lowerBound L fun a ha ↦ by
    obtain ⟨C, hC⟩ := bergman_cyclicMultiplier_lowerBound d a hd ha c
    refine ⟨C, fun F y ↦ ?_⟩
    rw [hL, norm_mul, ← mul_assoc]
    exact (one_mul _).symm.trans_le (mul_le_mul_of_nonneg_right (hC y) (norm_nonneg _))
  have hEq : (D : X → X) = entireMellin.symm ∘ L ∘ entireMellin := by
    funext f
    change D f = entireMellin.symm (entireMellin (D (entireMellin.symm (entireMellin f))))
    rw [entireMellin.symm_apply_apply, entireMellin.symm_apply_apply]
  rw [show (ContinuousLinearMap.id ℂ X - (c : ℂ) • exponentialSchwartzTranslation d : X →L[ℂ] X) = D by rfl, hEq]
  exact entireMellin.symm.toHomeomorph.isClosedEmbedding.comp (hC.comp entireMellin.toHomeomorph.isClosedEmbedding)

end Masullo
