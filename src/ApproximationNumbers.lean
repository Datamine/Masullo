import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
import Mathlib.LinearAlgebra.Dimension.LinearMap
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.Normed.Group.Tannery

open Set Filter Topology

namespace Masullo

noncomputable section

universe u

variable {E F G : Type u}
variable [NormedAddCommGroup E] [NormedSpace ℂ E]
variable [NormedAddCommGroup F] [NormedSpace ℂ F]
variable [NormedAddCommGroup G] [NormedSpace ℂ G]

/-- Zero-based approximation numbers. Index `m` permits approximation by rank at most `m`. -/
def approximationNumber (m : ℕ) (A : E →L[ℂ] F) : ℝ :=
  sInf {d | ∃ R : E →L[ℂ] F, R.toLinearMap.rank ≤ (m : Cardinal) ∧ d = ‖A - R‖}

private theorem approximationSet_nonempty (m : ℕ) (A : E →L[ℂ] F) :
    {d | ∃ R : E →L[ℂ] F, R.toLinearMap.rank ≤ (m : Cardinal) ∧ d = ‖A - R‖}.Nonempty := by
  exact ⟨‖A - 0‖, 0, by simp, rfl⟩

theorem approximationNumber_nonneg (m : ℕ) (A : E →L[ℂ] F) : 0 ≤ approximationNumber m A := by
  apply le_csInf (approximationSet_nonempty m A)
  rintro _ ⟨R, _, rfl⟩
  exact norm_nonneg _

theorem approximationNumber_le {m : ℕ} (A R : E →L[ℂ] F)
    (hR : R.toLinearMap.rank ≤ (m : Cardinal)) : approximationNumber m A ≤ ‖A - R‖ := by
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro _ ⟨S, _, rfl⟩
    exact norm_nonneg _
  · exact ⟨R, hR, rfl⟩

theorem le_approximationNumber {m : ℕ} (A : E →L[ℂ] F) {a : ℝ}
    (ha : ∀ R : E →L[ℂ] F, R.toLinearMap.rank ≤ (m : Cardinal) → a ≤ ‖A - R‖) :
    a ≤ approximationNumber m A := by
  apply le_csInf (approximationSet_nonempty m A)
  rintro _ ⟨R, hR, rfl⟩
  exact ha R hR

theorem approximationNumber_le_norm (m : ℕ) (A : E →L[ℂ] F) :
    approximationNumber m A ≤ ‖A‖ := by
  simpa using approximationNumber_le A 0 (m := m) (by simp)

theorem approximationNumber_eq_zero_of_rank_le {m : ℕ} (A : E →L[ℂ] F)
    (hA : A.toLinearMap.rank ≤ (m : Cardinal)) : approximationNumber m A = 0 :=
  le_antisymm (by simpa using approximationNumber_le A A hA) (approximationNumber_nonneg m A)

theorem approximationNumber_zero (A : E →L[ℂ] F) : approximationNumber 0 A = ‖A‖ := by
  apply le_antisymm (approximationNumber_le_norm 0 A)
  apply le_approximationNumber
  intro R hR
  have hr : R.toLinearMap.rank = 0 := by simpa using hR
  have hzero : R = 0 := by
    ext x
    have he := rank_zero_iff_forall_zero.mp hr ⟨R x, LinearMap.mem_range_self _ x⟩
    exact congrArg Subtype.val he
  simp [hzero]

theorem approximationNumber_antitone (A : E →L[ℂ] F) : Antitone (fun m => approximationNumber m A) := by
  intro m n hmn
  apply le_approximationNumber
  intro R hR
  exact approximationNumber_le A R (hR.trans (by exact_mod_cast hmn))

theorem approximationNumber_add_le (A B : E →L[ℂ] F) (m n : ℕ) :
    approximationNumber (m + n) (A + B) ≤ approximationNumber m A + approximationNumber n B := by
  have hd (R S : E →L[ℂ] F) (hR : R.toLinearMap.rank ≤ (m : Cardinal))
      (hS : S.toLinearMap.rank ≤ (n : Cardinal)) :
      approximationNumber (m + n) (A + B) ≤ ‖A - R‖ + ‖B - S‖ := by
    have hrank : (R + S).toLinearMap.rank ≤ ((m + n : ℕ) : Cardinal) := by
      rw [Nat.cast_add]
      exact (LinearMap.rank_add_le R.toLinearMap S.toLinearMap).trans (add_le_add hR hS)
    exact (approximationNumber_le (A + B) (R + S) hrank).trans (by
      rw [show A + B - (R + S) = (A - R) + (B - S) by abel]
      exact norm_add_le _ _)
  rw [← sub_le_iff_le_add]
  apply le_approximationNumber A
  intro R hR
  have h : approximationNumber (m + n) (A + B) - ‖A - R‖ ≤ approximationNumber n B :=
    le_approximationNumber B fun S hS => sub_le_iff_le_add.mpr (by linarith [hd R S hR hS])
  linarith

theorem approximationNumber_le_add_dist (A B : E →L[ℂ] F) (m : ℕ) :
    approximationNumber m A ≤ approximationNumber m B + ‖A - B‖ := by
  rw [← sub_le_iff_le_add]
  apply le_approximationNumber B
  intro R hR
  apply sub_le_iff_le_add.mpr
  exact (approximationNumber_le A R hR).trans (by
    rw [show A - R = (B - R) + (A - B) by abel]
    exact norm_add_le _ _)

theorem approximationNumber_lipschitz (A B : E →L[ℂ] F) (m : ℕ) :
    |approximationNumber m A - approximationNumber m B| ≤ ‖A - B‖ := by
  have hAB := approximationNumber_le_add_dist A B m
  have hBA := approximationNumber_le_add_dist B A m
  rw [norm_sub_rev] at hBA
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Approximation numbers are continuous in the operator norm. -/
theorem approximationNumber_continuous (i : ℕ) :
    Continuous (fun T : E →L[ℂ] F => approximationNumber i T) :=
  (LipschitzWith.of_dist_le_mul (K := 1) fun A B => by
    simpa only [Real.dist_eq, dist_eq_norm, NNReal.coe_one, one_mul, Real.norm_eq_abs] using
      approximationNumber_lipschitz A B i).continuous

theorem approximationNumber_comp_left_le (A : F →L[ℂ] G) (B : E →L[ℂ] F) (n : ℕ) :
    approximationNumber n (A.comp B) ≤ ‖A‖ * approximationNumber n B := by
  have hb (R : E →L[ℂ] F) (hR : R.toLinearMap.rank ≤ (n : Cardinal)) :
      approximationNumber n (A.comp B) ≤ ‖A‖ * ‖B - R‖ := by
    have hc : (A.comp R).toLinearMap.rank ≤ (n : Cardinal) :=
      (LinearMap.rank_comp_le_right R.toLinearMap A.toLinearMap).trans hR
    exact (approximationNumber_le (A.comp B) (A.comp R) hc).trans (by
      rw [← ContinuousLinearMap.comp_sub]
      exact A.opNorm_comp_le _)
  by_cases ha : ‖A‖ = 0
  · simpa only [ha, zero_mul] using hb 0 (by simp)
  · have hp : 0 < ‖A‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm ha)
    rw [mul_comm, ← div_le_iff₀ hp]
    exact le_approximationNumber B fun R hR => (div_le_iff₀ hp).mpr (by rw [mul_comm]; exact hb R hR)

theorem approximationNumber_comp_right_le (A : F →L[ℂ] G) (B : E →L[ℂ] F) (m : ℕ) :
    approximationNumber m (A.comp B) ≤ approximationNumber m A * ‖B‖ := by
  have ha (R : F →L[ℂ] G) (hR : R.toLinearMap.rank ≤ (m : Cardinal)) :
      approximationNumber m (A.comp B) ≤ ‖A - R‖ * ‖B‖ := by
    have hc : (R.comp B).toLinearMap.rank ≤ (m : Cardinal) :=
      (LinearMap.rank_comp_le_left B.toLinearMap R.toLinearMap).trans hR
    exact (approximationNumber_le (A.comp B) (R.comp B) hc).trans (by
      rw [← ContinuousLinearMap.sub_comp]
      exact (A - R).opNorm_comp_le _)
  by_cases hb : ‖B‖ = 0
  · simpa only [hb, mul_zero] using ha 0 (by simp)
  · have hp : 0 < ‖B‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hb)
    rw [← div_le_iff₀ hp]
    exact le_approximationNumber A fun R hR => (div_le_iff₀ hp).mpr (ha R hR)

theorem approximationNumber_comp_le (A : F →L[ℂ] G) (B : E →L[ℂ] F) (m n : ℕ) :
    approximationNumber (m + n) (A.comp B) ≤ approximationNumber m A * approximationNumber n B := by
  let a := approximationNumber (m + n) (A.comp B)
  have hd (R : F →L[ℂ] G) (S : E →L[ℂ] F) (hR : R.toLinearMap.rank ≤ (m : Cardinal))
      (hS : S.toLinearMap.rank ≤ (n : Cardinal)) : a ≤ ‖A - R‖ * ‖B - S‖ := by
    let C := R.comp B + (A - R).comp S
    have hc : C.toLinearMap.rank ≤ ((m + n : ℕ) : Cardinal) := by
      rw [Nat.cast_add]
      exact (LinearMap.rank_add_le _ _).trans (add_le_add
        ((LinearMap.rank_comp_le_left B.toLinearMap R.toLinearMap).trans hR)
        ((LinearMap.rank_comp_le_right S.toLinearMap (A - R).toLinearMap).trans hS))
    have he : A.comp B - C = (A - R).comp (B - S) := by
      simp only [C, ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp]
      abel
    exact (approximationNumber_le _ C hc).trans (he ▸ (A - R).opNorm_comp_le (B - S))
  have hs (S : E →L[ℂ] F) (hS : S.toLinearMap.rank ≤ (n : Cardinal)) :
      a ≤ approximationNumber m A * ‖B - S‖ := by
    by_cases hz : ‖B - S‖ = 0
    · simpa only [hz, mul_zero] using hd 0 S (by simp) hS
    · have hp : 0 < ‖B - S‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
      rw [← div_le_iff₀ hp]
      exact le_approximationNumber A fun R hR => (div_le_iff₀ hp).mpr (hd R S hR hS)
  by_cases hz : approximationNumber m A = 0
  · simpa only [hz, zero_mul] using hs 0 (by simp)
  · have hp : 0 < approximationNumber m A :=
      lt_of_le_of_ne (approximationNumber_nonneg _ _) (Ne.symm hz)
    rw [mul_comm, ← div_le_iff₀ hp]
    exact le_approximationNumber B fun S hS =>
      (div_le_iff₀ hp).mpr ((mul_comm _ _).subst (hs S hS))

theorem exists_rank_approximation_lt {n : ℕ} {A : E →L[ℂ] F} {ε : ℝ}
    (h : approximationNumber n A < ε) :
    ∃ R : E →L[ℂ] F, R.toLinearMap.rank ≤ (n : Cardinal) ∧ ‖A - R‖ < ε := by
  obtain ⟨d, ⟨R, hR, rfl⟩, hd⟩ := exists_lt_of_csInf_lt (approximationSet_nonempty n A) h
  exact ⟨R, hR, hd⟩

theorem isCompactOperator_of_approximationNumber_tendsto_zero (A : E →L[ℂ] F)
    [CompleteSpace F] (hA : Tendsto (fun n => approximationNumber n A) atTop (𝓝 0)) :
    IsCompactOperator A := by
  let C := {T : E →L[ℂ] F | IsCompactOperator T}
  have hc : IsClosed C := isClosed_setOfPred_isCompactOperator
  apply show A ∈ C from hc.closure_eq ▸ (Metric.mem_closure_iff.mpr ?_)
  intro ε hε
  have he : ∀ᶠ n in atTop, approximationNumber n A < ε :=
    hA.eventually (gt_mem_nhds hε)
  obtain ⟨n, hn⟩ := he.exists
  obtain ⟨R, hR, hAR⟩ := exists_rank_approximation_lt hn
  refine ⟨R, ?_, by simpa only [dist_eq_norm] using hAR⟩
  have hr : Module.rank ℂ R.toLinearMap.range < Cardinal.aleph0 :=
    hR.trans_lt Cardinal.natCast_lt_aleph0
  letI : FiniteDimensional ℂ R.toLinearMap.range := Module.rank_lt_aleph0_iff.mp hr
  let W := R.toLinearMap.range
  let R₀ : E →L[ℂ] W := R.codRestrict W (fun x => LinearMap.mem_range_self _ x)
  exact (isCompactOperator_of_locallyCompactSpace_dom R₀).clm_comp W.subtypeL

section Hilbert

variable {U V : Type u}
variable [NormedAddCommGroup U] [InnerProductSpace ℂ U] [CompleteSpace U]
variable [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

private theorem rank_adjoint_le_of_rank_le (A : U →L[ℂ] V) {n : ℕ}
    (hA : A.toLinearMap.rank ≤ (n : Cardinal)) : A.adjoint.toLinearMap.rank ≤ (n : Cardinal) := by
  let W := A.toLinearMap.range
  letI : FiniteDimensional ℂ W :=
    Module.rank_lt_aleph0_iff.mp (hA.trans_lt Cardinal.natCast_lt_aleph0)
  letI : CompleteSpace W := FiniteDimensional.complete ℂ W
  let A₀ : U →L[ℂ] W := A.codRestrict W (fun x => LinearMap.mem_range_self _ x)
  have hA₀ : W.subtypeL.comp A₀ = A := by ext x; rfl
  rw [← hA₀, ContinuousLinearMap.adjoint_comp]
  exact (LinearMap.rank_comp_le_left _ _).trans
    ((LinearMap.rank_le_domain A₀.adjoint.toLinearMap).trans hA)

theorem approximationNumber_adjoint (A : U →L[ℂ] V) (n : ℕ) :
    approximationNumber n A.adjoint = approximationNumber n A := by
  have hle {U V : Type u} [NormedAddCommGroup U] [InnerProductSpace ℂ U] [CompleteSpace U]
      [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] (B : U →L[ℂ] V) :
      approximationNumber n B.adjoint ≤ approximationNumber n B := by
    apply le_approximationNumber B
    intro R hR
    have h := approximationNumber_le B.adjoint R.adjoint (rank_adjoint_le_of_rank_le R hR)
    rwa [← map_sub, ContinuousLinearMap.adjoint.norm_map] at h
  exact le_antisymm (hle A) (by simpa using hle A.adjoint)

end Hilbert

open InnerProductSpace

/-- The one-based inequality with the same index in all three terms of
C.3.6.3(1) fails at index two. -/
theorem approximationNumber_same_index_add_obstruction :
    ∃ A B : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2),
      approximationNumber 1 A + approximationNumber 1 B < approximationNumber 1 (A + B) := by
  let H := EuclideanSpace ℂ (Fin 2)
  let b := EuclideanSpace.basisFun (Fin 2) ℂ
  let u : H := b 0
  let v : H := b 1
  let A : H →L[ℂ] H := rankOne ℂ u u
  let B : H →L[ℂ] H := rankOne ℂ v v
  have hu : u ≠ 0 := norm_ne_zero_iff.mp (by simp [u, b.orthonormal.norm_eq_one])
  have hv : v ≠ 0 := norm_ne_zero_iff.mp (by simp [v, b.orthonormal.norm_eq_one])
  have ha : approximationNumber 1 A = 0 :=
    approximationNumber_eq_zero_of_rank_le A (by simp [A, rank_rankOne hu hu])
  have hb : approximationNumber 1 B = 0 :=
    approximationNumber_eq_zero_of_rank_le B (by simp [B, rank_rankOne hv hv])
  have he : A + B = ContinuousLinearMap.id ℂ H := by
    change rankOne ℂ (b 0) (b 0) + rankOne ℂ (b 1) (b 1) = _
    simpa [Fin.sum_univ_two] using b.sum_rankOne_eq_id
  refine ⟨A, B, ?_⟩
  rw [ha, hb, he, zero_add]
  refine lt_of_lt_of_le zero_lt_one (le_approximationNumber _ ?_)
  intro R hR
  have hker : R.toLinearMap.ker ≠ ⊥ := by
    intro h
    have hinj := LinearMap.ker_eq_bot.mp h
    have hdim : Module.rank ℂ H = 2 := by
      simpa only [Cardinal.lift_id, Cardinal.mk_fin, Nat.cast_ofNat] using b.toBasis.mk_eq_rank.symm
    have hr : R.toLinearMap.rank = 2 := (rank_range_of_injective _ hinj).trans hdim
    rw [hr] at hR
    norm_num at hR
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hRx : R x = 0 := hx
  have heval : ((ContinuousLinearMap.id ℂ H - R) x) = x := by simp [hRx]
  have hop := (ContinuousLinearMap.id ℂ H - R).le_opNorm x
  rw [heval] at hop
  exact le_of_mul_le_mul_right (show 1 * ‖x‖ ≤ _ by simpa only [one_mul] using hop)
    (norm_pos_iff.mpr hx0)

end

end Masullo
