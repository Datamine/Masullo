import ExponentialPeriodization
import CompactPeriodicQuotient

open Bornology Filter Function Set Topology
open scoped ContDiff SchwartzMap

namespace Masullo

noncomputable section

variable (d : ℝ) [Fact (0 < d)]

section Transport

variable {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]

/-- Fourier coefficient functionals transported by a linear homeomorphism. -/
def transportedPeriodicMellinMode (e : E ≃L[ℂ] SmoothPeriodic d) (m : ℤ) : StrongDual ℂ E :=
  (d : ℂ) • (periodicFourierCoefficientCLM d m).comp e.toContinuousLinearMap

private def transportPeriodicDual (e : E ≃L[ℂ] SmoothPeriodic d) :
    StrongDual ℂ (SmoothPeriodic d) ≃L[ℂ] StrongDual ℂ E :=
  e.symm.arrowCongr (ContinuousLinearEquiv.refl ℂ ℂ)

private theorem transportPeriodicDual_apply (e : E ≃L[ℂ] SmoothPeriodic d)
    (L : StrongDual ℂ (SmoothPeriodic d)) :
    transportPeriodicDual d e L = L.comp e.toContinuousLinearMap := rfl

/-- The Mellin-normalized coefficients form an unconditional strong-dual basis
after transport by a linear homeomorphism. -/
theorem transportedPeriodicMellinMode_hasSum (e : E ≃L[ℂ] SmoothPeriodic d) (L : StrongDual ℂ E) :
    HasSum (fun m : ℤ => ((d : ℂ)⁻¹ * L (e.symm (periodicFourierMode d m))) •
      transportedPeriodicMellinMode d e m) L := by
  let T := transportPeriodicDual d e
  have hd : (d : ℂ) ≠ 0 := by exact_mod_cast (Fact.out : 0 < d).ne'
  have h := T.toContinuousLinearMap.hasSum (periodicFourierDual_hasSum d (T.symm L))
  rw [ContinuousLinearEquiv.coe_coe, T.apply_symm_apply] at h
  convert h using 1
  funext m
  rw [map_smul, transportedPeriodicMellinMode, smul_smul]
  have hs : (d : ℂ)⁻¹ * L (e.symm (periodicFourierMode d m)) * d =
      L (e.symm (periodicFourierMode d m)) := by field_simp
  rw [hs]
  rfl

/-- Absolute summability for every continuous seminorm is preserved by the
same transport and Mellin normalization. -/
theorem transportedPeriodicMellinMode_absolute (e : E ≃L[ℂ] SmoothPeriodic d) (L : StrongDual ℂ E)
    (q : Seminorm ℂ (StrongDual ℂ E)) (hq : Continuous q) :
    Summable (fun m : ℤ => q (((d : ℂ)⁻¹ * L (e.symm (periodicFourierMode d m))) •
      transportedPeriodicMellinMode d e m)) := by
  let T := transportPeriodicDual d e
  have hd : (d : ℂ) ≠ 0 := by exact_mod_cast (Fact.out : 0 < d).ne'
  have h := periodicFourierDual_absolute d (T.symm L)
    (q.comp T.toLinearEquiv.toLinearMap) (hq.comp T.continuous)
  convert h using 1
  funext m
  apply congrArg q
  show _ = T (T.symm L (periodicFourierMode d m) • periodicFourierCoefficientCLM d m)
  rw [map_smul, transportedPeriodicMellinMode, smul_smul]
  have hs : (d : ℂ)⁻¹ * L (e.symm (periodicFourierMode d m)) * d =
      L (e.symm (periodicFourierMode d m)) := by field_simp
  rw [hs]
  rfl

/-- Evaluation on the transported primal modes fixes each dual coefficient. -/
theorem transportedPeriodicMellinMode_unique [ContinuousSMul ℂ E]
    (e : E ≃L[ℂ] SmoothPeriodic d) (L : StrongDual ℂ E) (c : ℤ → ℂ)
    (h : HasSum (fun m => c m • transportedPeriodicMellinMode d e m) L) (n : ℤ) :
    c n = (d : ℂ)⁻¹ * L (e.symm (periodicFourierMode d n)) := by
  let A : StrongDual ℂ E →+ ℂ :=
    ⟨⟨fun K => K (e.symm (periodicFourierMode d n)), rfl⟩, fun _ _ => rfl⟩
  have hA : Continuous A := continuous_eval_const (e.symm (periodicFourierMode d n))
  have hs := h.map A hA
  have he (m : ℤ) : A (c m • transportedPeriodicMellinMode d e m) =
      c m * ((d : ℂ) * Pi.single (M := fun _ : ℤ => ℂ) n 1 m) := by
    change c m * ((d : ℂ) * periodicFourierCoefficientCLM d m (e (e.symm (periodicFourierMode d n)))) = _
    rw [e.apply_symm_apply, periodicFourierCoefficientCLM_mode]
  have hz (m : ℤ) (hm : m ≠ n) : A (c m • transportedPeriodicMellinMode d e m) = 0 := by
    simp [he, Pi.single_eq_of_ne hm]
  have hc : c n * (d : ℂ) = L (e.symm (periodicFourierMode d n)) := by
    simpa [he, A] using (hasSum_single n hz).unique hs
  have hd : (d : ℂ) ≠ 0 := by exact_mod_cast (Fact.out : 0 < d).ne'
  apply (mul_right_cancel₀ hd)
  rw [hc]
  field_simp

end Transport

/-- Mellin evaluations on the exponential Schwartz periodization quotient. -/
def exponentialQuotientMellinMode (m : ℤ) :
    StrongDual ℂ (ExpSchwartz ⧸ (exponentialPeriodization d).ker) :=
  transportedPeriodicMellinMode d (exponentialPeriodizationQuotient d) m

theorem exponentialQuotientMellinMode_apply (f : ExpSchwartz) (m : ℤ) :
    exponentialQuotientMellinMode d m ((exponentialPeriodization d).ker.mkQ f) =
      mellin (fun t => expSchwartzEvaluation 0 f (Real.log t)) (-periodicFrequency d m) := by
  change (d : ℂ) * periodicFourierCoefficient d
    (exponentialPeriodizationQuotient d ((exponentialPeriodization d).ker.mkQ f)) m = _
  rw [exponentialPeriodizationQuotient_mk, exponentialPeriodization_coefficient_mellin,
    Complex.real_smul, Complex.ofReal_inv, ← mul_assoc,
    mul_inv_cancel₀ (by exact_mod_cast (Fact.out : 0 < d).ne'), one_mul]

section CompactBasis

variable {K : Set ℝ} (hK : IsCompact K)
  (hcov : ∀ x : ℝ, ∃ n : ℤ, x + d * (n : ℝ) ∈ interior K)

include hcov in
/-- All primal modes have smooth lifts inside a common covering compact test space. -/
theorem fixedSupportPeriodization_modes :
    ∃ u : ℤ → LogFixedTest K, ∀ m, periodizationCLM d hK (u m) = periodicFourierMode d m := by
  obtain ⟨S, hS⟩ := exists_compactPeriodicSection d hK hcov
  exact ⟨fun m => S (periodicFourierMode d m), fun m => hS _⟩

/-- The lifted classes give the uniformly differentiated Fourier expansion in
the fixed-support quotient. -/
theorem fixedSupportPeriodization_hasSum (q : LogFixedTest K ⧸ (periodizationCLM d hK).ker) :
    let e := compactPeriodizationQuotient d hK hcov
    HasSum (fun m : ℤ => periodicFourierCoefficient d (e q) m • e.symm (periodicFourierMode d m)) q := by
  dsimp only
  let e := compactPeriodizationQuotient d hK hcov
  simpa only [map_smul, ContinuousLinearEquiv.coe_coe, e.symm_apply_apply] using
    e.symm.toContinuousLinearMap.hasSum (periodicFourierSeries_hasSum d (e q))

/-- A lift of a Fourier mode represents the corresponding quotient mode. -/
theorem fixedSupportPeriodization_class_eq (f : LogFixedTest K) (m : ℤ)
    (hf : periodizationCLM d hK f = periodicFourierMode d m) :
    (periodizationCLM d hK).ker.mkQ f =
      (compactPeriodizationQuotient d hK hcov).symm (periodicFourierMode d m) := by
  apply (compactPeriodizationQuotient d hK hcov).injective
  rw [compactPeriodizationQuotient_mk, ContinuousLinearEquiv.apply_symm_apply, hf]

theorem fixedSupportPeriodization_absolute (q : LogFixedTest K ⧸ (periodizationCLM d hK).ker)
    (p : Seminorm ℂ (LogFixedTest K ⧸ (periodizationCLM d hK).ker)) (hp : Continuous p) :
    let e := compactPeriodizationQuotient d hK hcov
    Summable (fun m : ℤ => p (periodicFourierCoefficient d (e q) m • e.symm (periodicFourierMode d m))) := by
  dsimp only
  let e := compactPeriodizationQuotient d hK hcov
  have hW := smoothPeriodic_withDerivativeSeminorms d
  obtain ⟨s, C, _, hbound⟩ := Seminorm.bound_of_continuous hW
    (p.comp e.symm.toLinearEquiv.toLinearMap) (hp.comp e.symm.continuous)
  let a (i : (_ : ℕ) × Fin 1) (m : ℤ) :=
    ‖periodicDerivativeLM d i.1
      (periodicFourierCoefficient d (e q) m • periodicFourierMode d m)‖
  have hs (t : Finset ((_: ℕ) × Fin 1)) : Summable (fun m => ∑ i ∈ t, a i m) := by
    classical
    induction t using Finset.induction_on with
    | empty => simp
    | insert i t hi ih =>
      simpa only [Finset.sum_insert hi] using (periodicFourierSeries_absolute d (e q) i.1).add ih
  apply ((hs s).mul_left (C : ℝ)).of_nonneg_of_le (fun _ => apply_nonneg _ _)
  intro m
  let y := periodicFourierCoefficient d (e q) m • periodicFourierMode d m
  have h := hbound y
  change p (e.symm y) ≤ _ at h
  rw [map_smul] at h
  refine h.trans (mul_le_mul_of_nonneg_left ?_ C.coe_nonneg)
  exact Seminorm.finset_sup_apply_le (Finset.sum_nonneg fun _ _ => norm_nonneg _)
      (fun i hi => Finset.single_le_sum (fun j _ => apply_nonneg _ _) hi)

theorem fixedSupportPeriodization_unique (q : LogFixedTest K ⧸ (periodizationCLM d hK).ker)
    (c : ℤ → ℂ)
    (h : HasSum (fun m : ℤ => c m • (compactPeriodizationQuotient d hK hcov).symm
      (periodicFourierMode d m)) q) (n : ℤ) :
    c n = periodicFourierCoefficient d (compactPeriodizationQuotient d hK hcov q) n := by
  let e := compactPeriodizationQuotient d hK hcov
  apply periodicFourierSeries_unique d (e q) c _ n
  change HasSum (fun m : ℤ => c m • e.symm (periodicFourierMode d m)) q at h
  simpa only [map_smul, ContinuousLinearEquiv.coe_coe, e.apply_symm_apply] using e.toContinuousLinearMap.hasSum h

/-- Each compact-support Mellin evaluation is the dual coefficient on its
own fixed-support quotient. -/
theorem fixedSupportPeriodization_mellinMode_apply (f : LogFixedTest K) (m : ℤ) :
    transportedPeriodicMellinMode d (compactPeriodizationQuotient d hK hcov) m
      ((periodizationCLM d hK).ker.mkQ f) =
      mellin (fun t => f.val (Real.log t)) (-periodicFrequency d m) := by
  let F : ExpSchwartz := (extendFixedExpSchwartz hK f).val
  have hF : exponentialPeriodization d F = periodizationCLM d hK f := by
    apply Subtype.ext
    funext x
    rw [exponentialPeriodization_apply]
    simp only [F, expSchwartzEvaluation_extendFixed_zero]
    rfl
  have h := exponentialQuotientMellinMode_apply d F m
  change (d : ℂ) * periodicFourierCoefficient d
    (exponentialPeriodizationQuotient d ((exponentialPeriodization d).ker.mkQ F)) m =
      mellin (fun t => expSchwartzEvaluation 0 F (Real.log t)) (-periodicFrequency d m) at h
  rw [exponentialPeriodizationQuotient_mk, hF] at h
  simp only [F, expSchwartzEvaluation_extendFixed_zero] at h
  change (d : ℂ) * periodicFourierCoefficient d
    (compactPeriodizationQuotient d hK hcov ((periodizationCLM d hK).ker.mkQ f)) m = _
  rw [compactPeriodizationQuotient_mk]
  exact h

end CompactBasis

end
end Masullo
