import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
import Mathlib.Analysis.PSeries

open Filter Set Topology InnerProductSpace
open scoped InnerProductSpace

noncomputable section

namespace Masullo

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι κ : Type*}

/-- A Hilbert-space nuclear representation as an absolutely summable series
of rank-one operators. The indexing type and representation are explicit. -/
structure RankOneSeries (ι H : Type*) [NormedAddCommGroup H] where
  image : ι → H
  functional : ι → H
  summableNorm : Summable (fun i => ‖image i‖ * ‖functional i‖)

namespace RankOneSeries

def operator (T : RankOneSeries ι H) : H →L[ℂ] H :=
  ∑' i, rankOne ℂ (T.image i) (T.functional i)

def trace (T : RankOneSeries ι H) : ℂ :=
  ∑' i, ⟪T.functional i, T.image i⟫_ℂ

theorem operator_summable (T : RankOneSeries ι H) :
    Summable (fun i => rankOne ℂ (T.image i) (T.functional i)) :=
  T.summableNorm.of_norm_bounded (by simp)

theorem operator_apply (T : RankOneSeries ι H) (x : H) :
    T.operator x = ∑' i, ⟪T.functional i, x⟫_ℂ • T.image i := by
  have h := (T.operator_summable.hasSum.mapL (ContinuousLinearMap.apply ℂ H x)).tsum_eq
  change (∑' i, rankOne ℂ (T.image i) (T.functional i) x) = T.operator x at h
  simpa only [rankOne_apply] using h.symm

omit [CompleteSpace H] in
/-- A summable weighted error transfers a rank-one norm estimate between lifts. -/
theorem summable_norm_of_lift_approximation (A : H →L[ℂ] H) (v w u : ι → H)
    (hw : Summable (fun i => ‖A (w i)‖ * ‖u i‖))
    (herr : Summable (fun i => ‖v i - w i‖ * ‖u i‖)) :
    Summable (fun i => ‖A (v i)‖ * ‖u i‖) := by
  have hbound := hw.add (herr.mul_left ‖A‖)
  apply hbound.of_nonneg_of_le (fun i => mul_nonneg (norm_nonneg _) (norm_nonneg _))
  intro i
  have htriangle : ‖A (v i)‖ ≤ ‖A (w i)‖ + ‖A‖ * ‖v i - w i‖ := by
    calc
      ‖A (v i)‖ = ‖A (w i) + A (v i - w i)‖ := by rw [map_sub, add_sub_cancel]
      _ ≤ ‖A (w i)‖ + ‖A (v i - w i)‖ := norm_add_le _ _
      _ ≤ ‖A (w i)‖ + ‖A‖ * ‖v i - w i‖ := add_le_add_right (A.le_opNorm _) _
  simpa only [add_mul, mul_assoc] using mul_le_mul_of_nonneg_right htriangle (norm_nonneg (u i))

open scoped Classical in
/-- A summable series from biorthogonal vectors in the spectral subspace
represents convolution after projection, by equality on a dense span. -/
theorem operator_of_biorthogonal (A P : H →L[ℂ] H) (v u : ι → H)
    (hspan : ∀ x, P x ∈ closure (Submodule.span ℂ (range v) : Set H))
    (hbiorth : ∀ i j, ⟪u i, v j⟫_ℂ = if i = j then 1 else 0)
    (hfactor : ∀ i x, ⟪u i, P x⟫_ℂ = ⟪u i, x⟫_ℂ)
    (hsum : Summable (fun i => ‖A (v i)‖ * ‖u i‖)) :
    (⟨fun i => A (v i), u, hsum⟩ : RankOneSeries ι H).operator = A ∘L P := by
  let T : RankOneSeries ι H := ⟨fun i => A (v i), u, hsum⟩
  have honVectors (j : ι) : T.operator (v j) = A (v j) := by
    rw [operator_apply]
    change (∑' i, ⟪u i, v j⟫_ℂ • A (v i)) = A (v j)
    rw [tsum_eq_single j]
    · simp [hbiorth]
    · intro i hij
      simp [hbiorth, hij]
  let D := T.operator - A
  have hker : Submodule.span ℂ (range v) ≤ D.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    change T.operator (v j) - A (v j) = 0
    rw [honVectors, sub_self]
  ext x
  have hPx : P x ∈ D.ker := closure_minimal hker D.isClosed_ker (hspan x)
  change T.operator (P x) - A (P x) = 0 at hPx
  change T.operator x = A (P x)
  calc
    T.operator x = T.operator (P x) := by
      rw [operator_apply, operator_apply]
      exact tsum_congr fun i => congrArg (· • T.image i) (hfactor i x).symm
    _ = A (P x) := sub_eq_zero.mp hPx

omit [CompleteSpace H] in
theorem trace_summable (T : RankOneSeries ι H) :
    Summable (fun i => ‖⟪T.functional i, T.image i⟫_ℂ‖) :=
  T.summableNorm.of_nonneg_of_le (fun _ => norm_nonneg _) (fun i => by
    simpa [mul_comm] using norm_inner_le_norm (𝕜 := ℂ) (T.functional i) (T.image i))

omit [CompleteSpace H] in
/-- The absolute sum of the diagonal entries of a rank-one operator has the
bound supplied by Cauchy–Schwarz and Parseval. -/
private theorem rankOne_diag_norm (b : HilbertBasis κ ℂ H) (x y : H) :
    Summable (fun j => ‖⟪b j, rankOne ℂ x y (b j)⟫_ℂ‖) ∧
    (∑' j, ‖⟪b j, rankOne ℂ x y (b j)⟫_ℂ‖) ≤ ‖x‖ * ‖y‖ := by
  have h (s : Finset κ) :
      ∑ j ∈ s, ‖⟪b j, rankOne ℂ x y (b j)⟫_ℂ‖ ≤ ‖x‖ * ‖y‖ := by
    have hs (v : H) : (∑ j ∈ s, ‖b.repr v j‖ ^ 2) ≤ ‖v‖ ^ 2 := by
      simpa using lp.sum_rpow_le_norm_rpow (p := 2) (by norm_num) (b.repr v) s
    have hx : Real.sqrt (∑ j ∈ s, ‖b.repr x j‖ ^ 2) ≤ ‖x‖ :=
      (Real.sqrt_le_sqrt (hs x)).trans_eq (Real.sqrt_sq (norm_nonneg _))
    have hy : Real.sqrt (∑ j ∈ s, ‖b.repr y j‖ ^ 2) ≤ ‖y‖ :=
      (Real.sqrt_le_sqrt (hs y)).trans_eq (Real.sqrt_sq (norm_nonneg _))
    have hd (j : κ) : ‖⟪b j, rankOne ℂ x y (b j)⟫_ℂ‖ =
        ‖b.repr y j‖ * ‖b.repr x j‖ := by
      rw [inner_right_rankOne_apply, norm_mul, b.repr_apply_apply, b.repr_apply_apply,
        norm_inner_symm (𝕜 := ℂ) y, mul_comm]
    simp_rw [hd]
    exact (Real.sum_mul_le_sqrt_mul_sqrt s _ _).trans
      (mul_le_mul hy hx (Real.sqrt_nonneg _) (norm_nonneg _)) |>.trans_eq (mul_comm _ _)
  have hsum := summable_of_sum_le (fun _ => norm_nonneg _) h
  exact ⟨hsum, hsum.tsum_le_of_sum_le h⟩

/-- Corrected Lemma C.3.4.1. Every Hilbert basis gives an absolutely convergent
diagonal. Its signed sum is independent of the basis, and the sum of norms is
bounded by the mass of any rank-one representation. -/
theorem diagonal_summable_and_hasSum (T : RankOneSeries ι H) (b : HilbertBasis κ ℂ H) :
    Summable (fun j => ‖⟪b j, T.operator (b j)⟫_ℂ‖) ∧
    (∑' j, ‖⟪b j, T.operator (b j)⟫_ℂ‖) ≤ ∑' i, ‖T.image i‖ * ‖T.functional i‖ ∧
    HasSum (fun j => ⟪b j, T.operator (b j)⟫_ℂ) T.trace := by
  let d (i : ι) (j : κ) := ⟪b j, rankOne ℂ (T.image i) (T.functional i) (b j)⟫_ℂ
  have hprod : Summable (fun p : ι × κ => ‖d p.1 p.2‖) := by
    apply (summable_prod_of_nonneg (fun _ => norm_nonneg _)).mpr
    exact ⟨fun i => (rankOne_diag_norm b (T.image i) (T.functional i)).1,
      T.summableNorm.of_nonneg_of_le (fun _ => tsum_nonneg (fun _ => norm_nonneg _))
        (fun i => (rankOne_diag_norm b (T.image i) (T.functional i)).2)⟩
  have hd (j : κ) : ⟪b j, T.operator (b j)⟫_ℂ = ∑' i, d i j := by
    let e : (H →L[ℂ] H) →L[ℂ] ℂ :=
      (innerSL ℂ (b j)).comp (ContinuousLinearMap.apply ℂ H (b j))
    exact ((T.operator_summable.hasSum.mapL e).tsum_eq).symm
  have hrow (i : ι) : ∑' j, d i j = ⟪T.functional i, T.image i⟫_ℂ := by
    simpa [d, inner_smul_right] using b.tsum_inner_mul_inner (T.functional i) (T.image i)
  have hswap := hprod.of_norm
  have hsum : Summable (fun j => ∑' i, d i j) := hswap.prod_symm.prod
  have hle (j : κ) : ‖⟪b j, T.operator (b j)⟫_ℂ‖ ≤ ∑' i, ‖d i j‖ := by
    rw [hd]
    exact norm_tsum_le_tsum_norm (hprod.prod_symm.prod_factor j)
  have habs := hprod.prod_symm.prod.of_nonneg_of_le (fun _ => norm_nonneg _) hle
  have heq : (∑' j, ∑' i, d i j) = T.trace := by
    calc
      (∑' j, ∑' i, d i j) = (∑' i, ∑' j, d i j) :=
        Summable.tsum_comm (f := d) hswap
      _ = T.trace := tsum_congr hrow
  refine ⟨habs, ?_, ?_⟩
  · calc
      _ ≤ ∑' j, ∑' i, ‖d i j‖ := habs.tsum_le_tsum hle hprod.prod_symm.prod
      _ = ∑' i, ∑' j, ‖d i j‖ := Summable.tsum_comm (f := fun i j => ‖d i j‖) hprod
      _ ≤ _ := hprod.prod.tsum_le_tsum
        (fun i => (rankOne_diag_norm b (T.image i) (T.functional i)).2) T.summableNorm
  · rw [← heq, show (fun j => ⟪b j, T.operator (b j)⟫_ℂ) = (fun j => ∑' i, d i j) from funext hd]
    exact hsum.hasSum

theorem hasSum_diagonal (T : RankOneSeries ι H) (b : HilbertBasis κ ℂ H) :
    HasSum (fun j => ⟪b j, T.operator (b j)⟫_ℂ) T.trace :=
  (T.diagonal_summable_and_hasSum b).2.2

theorem trace_eq_of_operator_eq {T : RankOneSeries ι H} {S : RankOneSeries κ H}
    (h : T.operator = S.operator) : T.trace = S.trace := by
  obtain ⟨β, b, _⟩ := exists_hilbertBasis ℂ H
  exact (h ▸ T.hasSum_diagonal b).unique (S.hasSum_diagonal b)

/-- Left composition acts on the image vectors. -/
def leftComp (T : RankOneSeries ι H) (A : H →L[ℂ] H) : RankOneSeries ι H where
  image i := A (T.image i)
  functional := T.functional
  summableNorm := (T.summableNorm.mul_left ‖A‖).of_nonneg_of_le (fun _ => by positivity) fun i => by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (A.le_opNorm (T.image i)) (norm_nonneg _)

/-- Right composition acts on the vectors representing the functionals. -/
def rightComp (T : RankOneSeries ι H) (A : H →L[ℂ] H) : RankOneSeries ι H where
  image := T.image
  functional i := A.adjoint (T.functional i)
  summableNorm := (T.summableNorm.mul_left ‖A‖).of_nonneg_of_le (fun _ => by positivity) fun i => by
    have hh := mul_le_mul_of_nonneg_left (A.adjoint.le_opNorm (T.functional i))
      (norm_nonneg (T.image i))
    rw [ContinuousLinearMap.adjoint.norm_map] at hh
    simpa only [mul_left_comm] using hh

theorem operator_leftComp (T : RankOneSeries ι H) (A : H →L[ℂ] H) :
    (T.leftComp A).operator = A ∘L T.operator := by
  ext x
  let eqMap : (H →L[ℂ] H) →L[ℂ] H := ContinuousLinearMap.apply ℂ H x
  have h₁ := ((T.leftComp A).operator_summable.hasSum.mapL eqMap).tsum_eq
  have h₂ := (T.operator_summable.hasSum.mapL (A.comp eqMap)).tsum_eq
  change (∑' i, rankOne ℂ (A (T.image i)) (T.functional i) x) = (T.leftComp A).operator x at h₁
  change (∑' i, A (rankOne ℂ (T.image i) (T.functional i) x)) = A (T.operator x) at h₂
  simp only [ContinuousLinearMap.comp_apply]
  rw [← h₁, ← h₂]
  exact tsum_congr fun _ => by simp

theorem operator_rightComp (T : RankOneSeries ι H) (A : H →L[ℂ] H) :
    (T.rightComp A).operator = T.operator ∘L A := by
  ext x
  let L₁ : (H →L[ℂ] H) →L[ℂ] H := ContinuousLinearMap.apply ℂ H x
  let L₂ : (H →L[ℂ] H) →L[ℂ] H := ContinuousLinearMap.apply ℂ H (A x)
  have h₁ := ((T.rightComp A).operator_summable.hasSum.mapL L₁).tsum_eq
  have h₂ := (T.operator_summable.hasSum.mapL L₂).tsum_eq
  change (∑' i, rankOne ℂ (T.image i) (A.adjoint (T.functional i)) x) =
    (T.rightComp A).operator x at h₁
  change (∑' i, rankOne ℂ (T.image i) (T.functional i) (A x)) = T.operator (A x) at h₂
  simp only [ContinuousLinearMap.comp_apply]
  rw [← h₁, ← h₂]
  exact tsum_congr fun _ => by simp [rankOne_apply, ContinuousLinearMap.adjoint_inner_left]

theorem trace_comp_cyclic (T : RankOneSeries ι H) (A : H →L[ℂ] H) :
    (T.leftComp A).trace = (T.rightComp A).trace := by
  apply tsum_congr
  intro i
  exact (A.adjoint_inner_left (T.image i) (T.functional i)).symm

omit [CompleteSpace H] in
/-- Uniformly bounded strong cutoff convergence suffices for convergence of the
trace once a summable rank-one representation of the operator is available.
This checks the trace conclusion of C.3.5.5 for left compositions. -/
theorem trace_leftCutoff_tendsto (T : RankOneSeries ι H) (A : ℕ → H →L[ℂ] H) {C : ℝ}
    (hA : ∀ n, ‖A n‖ ≤ C) (hstrong : ∀ x, Tendsto (fun n => A n x) atTop (𝓝 x)) :
    Tendsto (fun n => (T.leftComp (A n)).trace) atTop (𝓝 T.trace) := by
  apply tendsto_tsum_of_dominated_convergence (T.summableNorm.mul_left C)
  · intro i
    exact ((innerSL ℂ (T.functional i)).continuous.tendsto _).comp
      (hstrong (T.image i))
  · exact Eventually.of_forall fun n i => by
      have hi := norm_inner_le_norm (𝕜 := ℂ) (T.functional i) (A n (T.image i))
      have hn := (A n).le_opNorm (T.image i)
      calc
        _ ≤ ‖T.functional i‖ * ‖A n (T.image i)‖ := hi
        _ ≤ ‖T.functional i‖ * (C * ‖T.image i‖) :=
          mul_le_mul_of_nonneg_left
            (hn.trans (mul_le_mul_of_nonneg_right (hA n) (norm_nonneg _))) (norm_nonneg _)
        _ = _ := by ring

theorem trace_rightCutoff_tendsto (T : RankOneSeries ι H) (A : ℕ → H →L[ℂ] H) {C : ℝ}
    (hA : ∀ n, ‖A n‖ ≤ C) (hstrong : ∀ x, Tendsto (fun n => A n x) atTop (𝓝 x)) :
    Tendsto (fun n => (T.rightComp (A n)).trace) atTop (𝓝 T.trace) := by
  simpa only [← trace_comp_cyclic] using T.trace_leftCutoff_tendsto A hA hstrong

open scoped Classical in
/-- The spectral cutoff trace follows from absolute summability using the
biorthogonal vectors in the range of the spectral projection. -/
theorem biorthogonal_cutoff_trace (A P : H →L[ℂ] H) (v u : ι → H)
    (hspan : ∀ x, P x ∈ closure (Submodule.span ℂ (range v) : Set H))
    (hbiorth : ∀ i j, ⟪u i, v j⟫_ℂ = if i = j then 1 else 0)
    (hfactor : ∀ i x, ⟪u i, P x⟫_ℂ = ⟪u i, x⟫_ℂ)
    (hcompress : P ∘L (A ∘L P) = P ∘L A)
    (hsum : Summable (fun i => ‖A (v i)‖ * ‖u i‖))
    (M : ℕ → H →L[ℂ] H) {C : ℝ} (hM : ∀ n, ‖M n‖ ≤ C)
    (hstrong : ∀ x, Tendsto (fun n => M n x) atTop (𝓝 x)) :
    ∃ T : RankOneSeries ι H, T.operator = A ∘L P ∧
      (T.leftComp P).operator = P ∘L A ∧
      (∀ n, (T.leftComp (M n)).operator = M n ∘L (A ∘L P)) ∧
      Tendsto (fun n => (T.leftComp (M n)).trace) atTop (𝓝 (T.leftComp P).trace) := by
  let T : RankOneSeries ι H := ⟨fun i => A (v i), u, hsum⟩
  have hop : T.operator = A ∘L P := operator_of_biorthogonal A P v u hspan hbiorth hfactor hsum
  refine ⟨T, hop, ?_, ?_, ?_⟩
  · rw [operator_leftComp, hop, hcompress]
  · intro n
    rw [operator_leftComp, hop]
  · have htrace : (T.leftComp P).trace = T.trace := by
      apply tsum_congr
      intro i
      exact hfactor i (A (v i))
    rw [htrace]
    exact T.trace_leftCutoff_tendsto M hM hstrong

omit [CompleteSpace H] in
/-- A fixed decomposition gives a summable norm bound for the left cutoff
error, stronger than convergence of its scalar trace. -/
theorem leftCutoff_representation_mass_tendsto (T : RankOneSeries ι H)
    (A : ℕ → H →L[ℂ] H) {C : ℝ} (hA : ∀ n, ‖A n‖ ≤ C)
    (hstrong : ∀ x, Tendsto (fun n => A n x) atTop (𝓝 x)) :
    Tendsto (fun n => ∑' i, ‖A n (T.image i) - T.image i‖ * ‖T.functional i‖)
      atTop (𝓝 0) := by
  have hz : (∑' _ : ι, (0 : ℝ)) = 0 := tsum_zero
  rw [← hz]
  apply tendsto_tsum_of_dominated_convergence (T.summableNorm.mul_left (C + 1))
  · intro i
    have hi := ((hstrong (T.image i)).sub_const (T.image i)).norm.mul_const ‖T.functional i‖
    simpa using hi
  · exact Eventually.of_forall fun n i => by
      rw [Real.norm_of_nonneg (by positivity)]
      have h := norm_sub_le (A n (T.image i)) (T.image i)
      have ha := ((A n).le_opNorm (T.image i)).trans
        (mul_le_mul_of_nonneg_right (hA n) (norm_nonneg _))
      calc
        _ ≤ (C * ‖T.image i‖ + ‖T.image i‖) * ‖T.functional i‖ :=
          mul_le_mul_of_nonneg_right (h.trans (add_le_add ha le_rfl)) (norm_nonneg _)
        _ = _ := by ring

/-- The same representation estimate applies on the right when the adjoints
also converge strongly, including for self-adjoint cutoffs. -/
theorem rightCutoff_representation_mass_tendsto (T : RankOneSeries ι H)
    (A : ℕ → H →L[ℂ] H) {C : ℝ} (hA : ∀ n, ‖A n‖ ≤ C)
    (hstrong : ∀ x, Tendsto (fun n => (A n).adjoint x) atTop (𝓝 x)) :
    Tendsto (fun n => ∑' i, ‖T.image i‖ * ‖(A n).adjoint (T.functional i) - T.functional i‖)
      atTop (𝓝 0) := by
  let S : RankOneSeries ι H :=
    ⟨T.functional, T.image, by simpa only [mul_comm] using T.summableNorm⟩
  have hh := S.leftCutoff_representation_mass_tendsto (fun n => (A n).adjoint)
      (C := C) (fun n => by rw [ContinuousLinearMap.adjoint.norm_map]; exact hA n) hstrong
  simpa only [S, mul_comm] using hh

end RankOneSeries

/-- The nuclear trace norm on represented operators, defined by taking the
infimum of the masses of their countable rank-one representations. -/
def nuclearTraceNorm (A : H →L[ℂ] H) : ℝ :=
  sInf {m | ∃ T : RankOneSeries ℕ H, T.operator = A ∧
    m = ∑' i, ‖T.image i‖ * ‖T.functional i‖}

omit [CompleteSpace H] in
theorem nuclearTraceNorm_le_representation (T : RankOneSeries ℕ H) :
    nuclearTraceNorm T.operator ≤ ∑' i, ‖T.image i‖ * ‖T.functional i‖ := by
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro _ ⟨U, _, rfl⟩
    exact tsum_nonneg fun i => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  · exact ⟨T, rfl, rfl⟩

omit [CompleteSpace H] in
theorem nuclearTraceNorm_nonneg (A : H →L[ℂ] H) : 0 ≤ nuclearTraceNorm A := by
  by_cases h : {m : ℝ | ∃ T : RankOneSeries ℕ H, T.operator = A ∧
      m = ∑' i, ‖T.image i‖ * ‖T.functional i‖}.Nonempty
  · apply le_csInf h
    rintro _ ⟨U, _, rfl⟩
    exact tsum_nonneg fun i => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  · unfold nuclearTraceNorm
    rw [Set.not_nonempty_iff_eq_empty.mp h, Real.sInf_empty]

omit [CompleteSpace H] in
theorem RankOneSeries.trace_leftComp_finsetSum (T : RankOneSeries ι H) (A : κ → H →L[ℂ] H)
    (K : Finset κ) :
    (T.leftComp (∑ i ∈ K, A i)).trace = ∑ i ∈ K, (T.leftComp (A i)).trace := by
  let f (i : κ) (j : ι) := ⟪T.functional j, A i (T.image j)⟫_ℂ
  have hs (i : κ) : Summable (f i) := (T.leftComp (A i)).trace_summable.of_norm
  simp only [RankOneSeries.trace, RankOneSeries.leftComp]
  have he (j : ι) : ⟪T.functional j, (∑ i ∈ K, A i) (T.image j)⟫_ℂ = ∑ i ∈ K, f i j := by
    simp [f, sum_apply, inner_sum]
  simp only [he]
  exact Summable.tsum_finsetSum fun i _ => hs i

/-- Proposition C.3.5.1. Cofinal bounded strong finite-stage cutoffs
converge in nuclear trace norm, and their finite traces converge to the trace. -/
theorem RankOneSeries.nuclearTraceNorm_cofinal_cutoff (T : RankOneSeries ℕ H)
    (P : κ → H →L[ℂ] H) (stages : ℕ → Finset κ) {C : ℝ}
    (hP : ∀ K : Finset κ, ‖∑ i ∈ K, P i‖ ≤ C)
    (hstrong : ∀ x, Tendsto (fun K : Finset κ => (∑ i ∈ K, P i) x) atTop (𝓝 x))
    (hcofinal : Tendsto stages atTop atTop) :
    Tendsto (fun n => nuclearTraceNorm (((∑ i ∈ stages n, P i) ∘L T.operator) - T.operator))
      atTop (𝓝 0) ∧
    Tendsto (fun n => ∑ i ∈ stages n, (T.leftComp (P i)).trace) atTop (𝓝 T.trace) := by
  let A (n : ℕ) := ∑ i ∈ stages n, P i
  have hA (n : ℕ) : ‖A n‖ ≤ C := hP (stages n)
  have hAct (x : H) : Tendsto (fun n => A n x) atTop (𝓝 x) := (hstrong x).comp hcofinal
  constructor
  · have hmass := T.leftCutoff_representation_mass_tendsto A hA hAct
    refine squeeze_zero (fun _ => nuclearTraceNorm_nonneg _) (fun n => ?_) hmass
    let R := T.leftComp (A n - ContinuousLinearMap.id ℂ H)
    have hR : R.operator = (A n ∘L T.operator) - T.operator := by
      rw [RankOneSeries.operator_leftComp]
      ext x
      rfl
    rw [← hR]
    exact nuclearTraceNorm_le_representation R
  · simpa only [A, RankOneSeries.trace_leftComp_finsetSum] using T.trace_leftCutoff_tendsto A hA hAct

/-- Lemma C.3.4.3. Strong convergence of a sequence becomes operator-norm
convergence after right composition with a compact operator. -/
theorem tendsto_norm_compact_right {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (A : E →L[ℂ] H) (Q : H →L[ℂ] H) (hA : IsCompactOperator A)
    (S : ℕ → H →L[ℂ] H) (hS : ∀ x, Tendsto (fun n => S n x) atTop (𝓝 (Q x))) :
    Tendsto (fun n => S n ∘L A) atTop (𝓝 (Q ∘L A)) := by
  let D := fun n => S n - Q
  have hD (x : H) : Tendsto (fun n => D n x) atTop (𝓝 0) := by
    simpa [D] using (hS x).sub (tendsto_const_nhds (x := Q x))
  obtain ⟨C, hC⟩ := banach_steinhaus (g := D) (fun x => by
    obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.mp (Metric.isBounded_range_of_tendsto _ (hD x))
    exact ⟨M, fun n => hM _ ⟨n, rfl⟩⟩)
  let B := max C 1
  have hB : 0 < B := zero_lt_one.trans_le (le_max_right _ _)
  have hDB (n : ℕ) : ‖D n‖ ≤ B := (hC n).trans (le_max_left _ _)
  have hAlin : IsCompactOperator A.toLinearMap := hA
  obtain ⟨K, hK, hAK⟩ := hAlin.image_closedBall_subset_compact 1
  rw [Metric.tendsto_nhds]
  intro ε hε
  let δ := ε / (4 * B)
  have hδ : 0 < δ := div_pos hε (by positivity)
  obtain ⟨t, ht, hcover⟩ := Metric.totallyBounded_iff.mp hK.totallyBounded δ hδ
  have hcenter : ∀ᶠ n in atTop, ∀ y ∈ ht.toFinset, ‖D n y‖ < ε / 4 := by
    apply ht.toFinset.eventually_all.mpr
    intro y _
    simpa only [dist_zero_right] using (Metric.tendsto_nhds.mp (hD y)) (ε / 4) (by positivity)
  filter_upwards [hcenter] with n hn
  have hbound : ‖D n ∘L A‖ ≤ ε / 2 := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
    intro x hx
    have hxK : A x ∈ K := hAK ⟨x, by simp [Metric.mem_closedBall, hx], rfl⟩
    obtain ⟨y, hyt, hy⟩ := Set.mem_iUnion₂.mp (hcover hxK)
    have hy' : ‖A x - y‖ < δ := by simpa only [Metric.mem_ball, dist_eq_norm] using hy
    have hdist : ‖D n (A x) - D n y‖ ≤ B * δ := by
      rw [← map_sub]
      exact ((D n).le_opNorm (A x - y)).trans (mul_le_mul (hDB n) hy'.le (norm_nonneg _) hB.le)
    have hδeq : B * δ = ε / 4 := by dsimp [δ]; field_simp [hB.ne']
    have hySmall := hn y (ht.mem_toFinset.mpr hyt)
    change ‖D n (A x)‖ ≤ ε / 2
    calc
      _ = ‖D n (A x) - D n y + D n y‖ := by rw [sub_add_cancel]
      _ ≤ ‖D n (A x) - D n y‖ + ‖D n y‖ := norm_add_le _ _
      _ ≤ ε / 2 := by rw [hδeq] at hdist; linarith
  rw [dist_eq_norm]
  have heq : S n ∘L A - Q ∘L A = D n ∘L A := by ext x; rfl
  rw [heq]
  exact hbound.trans_lt (by linarith)

/-- The absolute-diagonal sum in the printed Lemma C.3.4.1(2) depends on
the basis, even for a self-adjoint rank-two operator. -/
theorem absolute_diagonal_depends_on_basis :
    ∃ (T : RankOneSeries (Fin 2) (EuclideanSpace ℂ (Fin 2)))
      (b c : HilbertBasis (Fin 2) ℂ (EuclideanSpace ℂ (Fin 2))),
      (∑ i, ‖⟪b i, T.operator (b i)⟫_ℂ‖) ≠ (∑ i, ‖⟪c i, T.operator (c i)⟫_ℂ‖) := by
  let E := EuclideanSpace ℂ (Fin 2)
  let b := EuclideanSpace.basisFun (Fin 2) ℂ
  let s : ℝ := (Real.sqrt 2)⁻¹
  have hs : s * s + s * s = 1 := by
    dsimp [s]
    have hsqrt := Real.sq_sqrt (by norm_num : 0 ≤ (2 : ℝ))
    field_simp [show Real.sqrt 2 ≠ 0 by positivity]
    nlinarith
  let v : Fin 2 → E := ![WithLp.toLp 2 ![(s : ℂ), (s : ℂ)],
    WithLp.toLp 2 ![(s : ℂ), -(s : ℂ)]]
  have hinner (x y : E) : ⟪x, y⟫_ℂ = ∑ i : Fin 2, y i * star (x i) := by
    exact PiLp.inner_apply x y
  have horth : Orthonormal ℂ v := by
    rw [orthonormal_iff_ite]
    intro i j
    rw [hinner]
    fin_cases i <;> fin_cases j <;>
      simp [v, Fin.sum_univ_two, ← Complex.ofReal_mul, ← Complex.ofReal_add, hs]
  let c : OrthonormalBasis (Fin 2) ℂ E := OrthonormalBasis.mk horth
    (horth.linearIndependent.span_eq_top_of_card_eq_finrank (Module.finrank_eq_card_basis b.toBasis).symm).ge
  let T : RankOneSeries (Fin 2) E :=
    ⟨fun i => if i = 0 then b i else -b i, b, summable_of_hasFiniteSupport (Set.toFinite _)⟩
  have hc (i : Fin 2) : c.toHilbertBasis i = v i := by simp [c]
  have hb (i : Fin 2) : b.toHilbertBasis i = b i := by simp
  have hop (x : E) : T.operator x = ⟪b 0, x⟫_ℂ • b 0 - ⟪b 1, x⟫_ℂ • b 1 := by
    rw [T.operator_apply]
    simp [T, tsum_fintype, Fin.sum_univ_two, sub_eq_add_neg]
  have hb0 : ⟪b 0, T.operator (b 0)⟫_ℂ = 1 := by simp [hop]
  have hb1 : ⟪b 1, T.operator (b 1)⟫_ℂ = -1 := by simp [hop]
  have hleft (i : Fin 2) (x : E) : ⟪b i, x⟫_ℂ = x i := EuclideanSpace.basisFun_inner (Fin 2) ℂ x i
  have hright (i : Fin 2) (x : E) : ⟪x, b i⟫_ℂ = star (x i) := by
    rw [← inner_conj_symm, hleft]; rfl
  have hdiag (i : Fin 2) : ⟪v i, T.operator (v i)⟫_ℂ = 0 := by
    simp only [hop, inner_sub_right, inner_smul_right, hleft, hright]
    fin_cases i <;> simp [v]
  refine ⟨T, b.toHilbertBasis, c.toHilbertBasis, ?_⟩
  simp only [Fin.sum_univ_two, hb, hc, hb0, hb1, hdiag, norm_zero, norm_neg, norm_one, add_zero]
  norm_num

/-- Summability of squared norm bounds does not suffice for absolute summability. -/
theorem square_summable_not_summable :
    ∃ a : ℕ → ℝ, (∀ n, 0 ≤ a n) ∧ Summable (fun n => (a n) ^ 2) ∧ ¬ Summable a := by
  refine ⟨fun n => 1 / (n : ℝ), fun n => by positivity, ?_, Real.not_summable_one_div_natCast⟩
  simpa only [div_pow, one_pow] using (Real.summable_one_div_nat_pow (p := 2)).mpr (by decide)

omit [InnerProductSpace ℂ H] [CompleteSpace H] in
/-- Compactness of the product in the projection-first order cannot be
reversed using idempotence and continuity of the projection alone. -/
theorem projection_order_compactness_obstruction [NormedSpace ℂ H]
    (hInf : ¬FiniteDimensional ℂ H) :
    ∃ P A : (H × H) →L[ℂ] H × H,
      P ∘L P = P ∧ P ∘L A = 0 ∧ ¬IsCompactOperator (A ∘L P) := by
  let first := ContinuousLinearMap.fst ℂ H H
  let second := ContinuousLinearMap.snd ℂ H H
  let inFirst := ContinuousLinearMap.inl ℂ H H
  let inSecond := ContinuousLinearMap.inr ℂ H H
  let P := inFirst.comp first
  let A := inSecond.comp first
  refine ⟨P, A, ?_, ?_, ?_⟩
  · ext x <;> rfl
  · ext x <;> rfl
  · intro hc
    have hcompact := (hc.comp_clm inFirst).clm_comp second
    change IsCompactOperator (id : H → H) at hcompact
    exact hInf (FiniteDimensional.of_isCompactOperator_id hcompact)

end Masullo
