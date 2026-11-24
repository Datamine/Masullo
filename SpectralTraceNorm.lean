import TraceClassNorm
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Normed.Operator.Extend

open Set Filter Topology InnerProductSpace
open scoped InnerProductSpace

namespace Masullo

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*}

/-- The positive operator `(T* T)^(1/2)` defining the spectral trace norm. -/
def operatorAbs (T : H →L[ℂ] H) : H →L[ℂ] H := CFC.sqrt (star T * T)

theorem operatorAbs_nonneg (T : H →L[ℂ] H) : 0 ≤ operatorAbs T :=
  CFC.sqrt_nonneg _

theorem operatorAbs_apply_norm (T : H →L[ℂ] H) (x : H) :
    ‖operatorAbs T x‖ = ‖T x‖ := by
  let P := operatorAbs T
  have hP : star P = P := (IsSelfAdjoint.of_nonneg (operatorAbs_nonneg T)).star_eq
  have hs : P * P = star T * T := CFC.sqrt_mul_sqrt_self _ (star_mul_self_nonneg T)
  have heq : ‖P x‖ ^ 2 = ‖T x‖ ^ 2 := by
    rw [P.apply_norm_sq_eq_inner_adjoint_left, T.apply_norm_sq_eq_inner_adjoint_left]
    change RCLike.re ⟪(star P * P) x, x⟫_ℂ = RCLike.re ⟪(star T * T) x, x⟫_ℂ
    rw [hP, hs]
  nlinarith [norm_nonneg (P x), norm_nonneg (T x)]

/-- A norm domination on vectors gives a bounded factor through the closure of the range. -/
theorem exists_contraction_comp_of_norm_le (A B : H →L[ℂ] H)
    (hAB : ∀ x, ‖A x‖ ≤ ‖B x‖) :
    ∃ C : H →L[ℂ] H, ‖C‖ ≤ 1 ∧ C.comp B = A := by
  let K := B.toLinearMap.range.topologicalClosure
  let e : H →ₗ[ℂ] K := B.toLinearMap.codRestrict K (fun x =>
    B.toLinearMap.range.le_topologicalClosure (LinearMap.mem_range_self _ x))
  have he : DenseRange e := by
    intro y
    rw [closure_subtype]
    have hr : Subtype.val '' range e = range B := by
      ext z
      constructor
      · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
        exact ⟨x, rfl⟩
      · rintro ⟨x, rfl⟩
        exact ⟨e x, ⟨x, rfl⟩, rfl⟩
    rw [hr]
    exact y.2
  have hn : ∀ x, ‖A.toLinearMap x‖ ≤ 1 * ‖e x‖ := by
    intro x
    change ‖A x‖ ≤ 1 * ‖B x‖
    simpa only [one_mul] using hAB x
  letI : CompleteSpace K := (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  let D : K →L[ℂ] H := A.toLinearMap.extendOfNorm e
  refine ⟨D.comp K.orthogonalProjectionOnto, ?_, ?_⟩
  · calc
      ‖D.comp K.orthogonalProjectionOnto‖ ≤ ‖D‖ * ‖K.orthogonalProjectionOnto‖ :=
        D.opNorm_comp_le _
      _ ≤ 1 := mul_le_one₀ (LinearMap.opNorm_extendOfNorm_le he zero_le_one hn)
        (norm_nonneg K.orthogonalProjectionOnto) K.orthogonalProjectionOnto_norm_le
  · ext x
    change D (K.orthogonalProjectionOnto ((e x : K) : H)) = A x
    rw [K.orthogonalProjectionOnto_mem_subspace_eq_self]
    exact LinearMap.extendOfNorm_eq he ⟨1, hn⟩ x

theorem operatorAbs_mem_and_norm_eq {T : H →L[ℂ] H} (hT : T ∈ nuclearOperators H) :
    operatorAbs T ∈ nuclearOperators H ∧ nuclearTraceNorm (operatorAbs T) = nuclearTraceNorm T := by
  obtain ⟨U, hU, hUT⟩ := exists_contraction_comp_of_norm_le T (operatorAbs T)
    (fun x => (operatorAbs_apply_norm T x).ge)
  obtain ⟨V, hV, hVT⟩ := exists_contraction_comp_of_norm_le (operatorAbs T) T
    (fun x => (operatorAbs_apply_norm T x).le)
  have habs : operatorAbs T ∈ nuclearOperators H := hVT ▸ nuclearOperators_comp_left V hT
  refine ⟨habs, le_antisymm ?_ ?_⟩
  · calc
      nuclearTraceNorm (operatorAbs T) = nuclearTraceNorm (V.comp T) := by rw [hVT]
      _ ≤ ‖V‖ * nuclearTraceNorm T := nuclearTraceNorm_comp_left_le V hT
      _ ≤ nuclearTraceNorm T := mul_le_of_le_one_left (nuclearTraceNorm_nonneg T) hV
  · calc
      nuclearTraceNorm T = nuclearTraceNorm (U.comp (operatorAbs T)) := by rw [hUT]
      _ ≤ ‖U‖ * nuclearTraceNorm (operatorAbs T) := nuclearTraceNorm_comp_left_le U habs
      _ ≤ nuclearTraceNorm (operatorAbs T) :=
        mul_le_of_le_one_left (nuclearTraceNorm_nonneg _) hU

private theorem sqrt_diagonal (P : H →L[ℂ] H) (hP : 0 ≤ P) (x : H) :
    ⟪x, P x⟫_ℂ = (‖CFC.sqrt P x‖ ^ 2 : ℝ) := by
  let B := CFC.sqrt P
  have hB : B.adjoint = B := (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg P)).star_eq
  have hBP : B * B = P := CFC.sqrt_mul_sqrt_self _ hP
  change ⟪x, P x⟫_ℂ = ((‖B x‖ ^ 2 : ℝ) : ℂ)
  rw [← hBP]
  change ⟪x, B (B x)⟫_ℂ = _
  nth_rewrite 1 [← hB]
  rw [ContinuousLinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K]
  push_cast
  rfl

/-- The square-root frame has countable support even in a nonseparable Hilbert space. -/
private theorem exists_positive_representation (P : H →L[ℂ] H) (hP : 0 ≤ P)
    (b : HilbertBasis ι ℂ H) (hs : Summable (fun j => ‖CFC.sqrt P (b j)‖ ^ 2)) :
    ∃ S : RankOneSeries ℕ H, S.operator = P ∧ S.mass = ∑' j, ‖CFC.sqrt P (b j)‖ ^ 2 := by
  classical
  let B := CFC.sqrt P
  have hB : B.adjoint = B := (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg P)).star_eq
  have hBP : B * B = P := CFC.sqrt_mul_sqrt_self _ hP
  let v : ι → H := fun j => B (b j)
  let I := Function.support v
  have hI : I.Countable := by
    apply hs.countable_support.mono
    intro j hj
    change ‖B (b j)‖ ^ 2 ≠ 0
    exact pow_ne_zero _ (norm_ne_zero_iff.mpr hj)
  letI : Countable I := hI.to_subtype
  obtain ⟨e, he⟩ := Countable.exists_injective_nat I
  let w : ℕ → H := Function.extend e (v ∘ Subtype.val) 0
  have hw (j : I) : w (e j) = v j := Function.Injective.extend_apply he _ _ _
  have hw0 (n : ℕ) (hn : n ∉ range e) : w n = 0 :=
    Function.extend_apply' _ _ _ (by simpa only [Set.mem_range, not_exists] using hn)
  have hmassI : HasSum (fun j : I => ‖v j‖ ^ 2) (∑' j, ‖v j‖ ^ 2) := by
    apply (Subtype.val_injective.hasSum_iff ?_).mpr hs.hasSum
    intro j hj
    have hz : v j = 0 := by
      by_contra h
      exact hj ⟨⟨j, h⟩, rfl⟩
    change ‖v j‖ ^ 2 = 0
    simp [hz]
  have hmass : HasSum (fun n => ‖w n‖ * ‖w n‖) (∑' j, ‖v j‖ ^ 2) := by
    apply (he.hasSum_iff (fun n hn => by simp [hw0 n hn])).mp
    change HasSum (fun j : I => ‖w (e j)‖ * ‖w (e j)‖) _
    simpa only [hw, ← pow_two] using hmassI
  let S : RankOneSeries ℕ H := ⟨w, w, hmass.summable⟩
  have hS : S.operator = P := by
    ext x
    rw [S.operator_apply]
    have hexp : HasSum (fun j => ⟪v j, x⟫_ℂ • v j) (P x) := by
      have h := (b.hasSum_repr (B x)).mapL B
      simp only [map_smul, HilbertBasis.repr_apply_apply, ←
        ContinuousLinearMap.adjoint_inner_left B, hB] at h
      exact hBP ▸ h
    have hexpI : HasSum (fun j : I => ⟪v j, x⟫_ℂ • v j) (P x) := by
      apply (Subtype.val_injective.hasSum_iff ?_).mpr hexp
      intro j hj
      have hz : v j = 0 := by
        by_contra h
        exact hj ⟨⟨j, h⟩, rfl⟩
      simp [hz]
    have hexpN : HasSum (fun n => ⟪w n, x⟫_ℂ • w n) (P x) := by
      apply (he.hasSum_iff (fun n hn => by simp [hw0 n hn])).mp
      change HasSum (fun j : I => ⟪w (e j), x⟫_ℂ • w (e j)) _
      simpa only [hw] using hexpI
    exact hexpN.tsum_eq
  exact ⟨S, hS, hmass.tsum_eq⟩

/-- The diagonal trace norm agrees with the rank-one representation norm for positive operators. -/
theorem nuclearTraceNorm_eq_positive_diagonal (P : TraceClass H)
    (hP : 0 ≤ P.toOperator) (b : HilbertBasis ι ℂ H) :
    ‖P‖ = (∑' j, ⟪b j, P.toOperator (b j)⟫_ℂ).re := by
  obtain ⟨R, hR⟩ := P.toOperator_mem
  obtain ⟨hads, -, htr⟩ := R.diagonal_summable_and_hasSum b
  rw [hR] at hads htr
  rw [← P.traceValue_eq_of_operator R hR] at htr
  let v : ι → H := fun j => CFC.sqrt P.toOperator (b j)
  have hdiag (j : ι) : ⟪b j, P.toOperator (b j)⟫_ℂ = (‖v j‖ ^ 2 : ℝ) :=
    sqrt_diagonal P.toOperator hP (b j)
  have hs : Summable (fun j => ‖v j‖ ^ 2) := by
    convert hads using 1
    ext j
    rw [hdiag, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  obtain ⟨S, hS, hmass⟩ := exists_positive_representation P.toOperator hP b hs
  let m : ℝ := ∑' j, ‖v j‖ ^ 2
  have hm : 0 ≤ m := tsum_nonneg fun j => sq_nonneg _
  have htrm : P.traceValue = (m : ℂ) := by
    apply htr.unique
    rw [show (fun j => ⟪b j, P.toOperator (b j)⟫_ℂ) =
      (fun j => ((‖v j‖ ^ 2 : ℝ) : ℂ)) by exact funext hdiag]
    exact hs.hasSum.mapL Complex.ofRealCLM
  have hNorm : ‖P‖ = m := by
    refine le_antisymm ?_ ?_
    · have hPS : P = TraceClass.ofSeries S := P.toOperator_injective hS.symm
      rw [hPS]
      exact (TraceClass.norm_ofSeries_le S).trans_eq hmass
    · simpa only [htrm, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hm]
        using P.norm_traceValue_le
  rw [hNorm, htr.tsum_eq, htrm, Complex.ofReal_re]

/-- The norm of a represented operator is the diagonal trace of its absolute value,
computed in any Hilbert basis. -/
theorem nuclearTraceNorm_eq_spectral (T : H →L[ℂ] H) (hT : T ∈ nuclearOperators H)
    (b : HilbertBasis ι ℂ H) :
    nuclearTraceNorm T = (∑' j, ⟪b j, operatorAbs T (b j)⟫_ℂ).re := by
  obtain ⟨⟨R, hR⟩, heq⟩ := operatorAbs_mem_and_norm_eq hT
  have hP : (TraceClass.ofSeries R).toOperator = operatorAbs T := hR
  rw [← heq]
  have h := nuclearTraceNorm_eq_positive_diagonal
    (TraceClass.ofSeries R) (hP.symm ▸ operatorAbs_nonneg T) b
  change nuclearTraceNorm (TraceClass.ofSeries R).toOperator = _ at h
  simpa only [hP] using h

/-- Basis-independent characterization of trace class by a finite absolute-value diagonal. -/
theorem nuclearOperators_iff_summable_abs_diagonal (T : H →L[ℂ] H) (b : HilbertBasis ι ℂ H) :
    T ∈ nuclearOperators H ↔ Summable (fun j => ‖⟪b j, operatorAbs T (b j)⟫_ℂ‖) := by
  constructor
  · intro hT
    obtain ⟨⟨R, hR⟩, -⟩ := operatorAbs_mem_and_norm_eq hT
    rw [← hR]
    exact (R.diagonal_summable_and_hasSum b).1
  · intro hs
    have hp := operatorAbs_nonneg T
    have hs' : Summable (fun j => ‖CFC.sqrt (operatorAbs T) (b j)‖ ^ 2) := by
      convert hs using 1
      ext j
      rw [sqrt_diagonal _ hp, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    obtain ⟨R, hR, -⟩ := exists_positive_representation _ hp b hs'
    obtain ⟨U, -, hU⟩ := exists_contraction_comp_of_norm_le T (operatorAbs T)
      (fun x => (operatorAbs_apply_norm T x).ge)
    rw [← hU]
    exact nuclearOperators_comp_left U ⟨R, hR⟩

/-- The manuscript's trace norm, using its positive-square-root diagonal. -/
def spectralTraceNorm (b : HilbertBasis ι ℂ H) (T : H →L[ℂ] H) : ℝ :=
  (∑' j, ⟪b j, operatorAbs T (b j)⟫_ℂ).re

variable {κ : Type*}

theorem norm_sum_pairwise_orthogonal_projections_le_one (K : κ → Submodule ℂ H)
    [∀ i, (K i).HasOrthogonalProjection]
    (hK : Pairwise fun i j => K i ⟂ K j) (S : Finset κ) :
    ‖∑ i ∈ S, (K i).starProjection‖ ≤ 1 := by
  classical
  let P : H →L[ℂ] H := ∑ i ∈ S, (K i).starProjection
  have hz {i j : κ} (hij : i ≠ j) (x : H) :
      (K i).starProjection ((K j).starProjection x) = 0 := by
    apply (K i).starProjection_apply_eq_zero_iff.mpr
    intro y hy
    exact hK hij.symm ((K j).starProjection_apply_mem x) y hy
  have hi (x : H) : P (P x) = P x := by
    have hs (i : κ) (hiS : i ∈ S) : (K i).starProjection (P x) = (K i).starProjection x := by
      simp only [P, sum_apply, map_sum]
      rw [Finset.sum_eq_single i]
      · exact (K i).starProjection_eq_self_iff.mpr ((K i).starProjection_apply_mem x)
      · intro j _ hji
        exact hz hji.symm x
      · exact fun h => False.elim (h hiS)
    simpa only [P, sum_apply] using Finset.sum_congr rfl hs
  have hstar : P.adjoint = P := by
    simp only [P, map_sum]
    exact Finset.sum_congr rfl fun i _ => (isSelfAdjoint_starProjection (K i)).star_eq
  apply P.opNorm_le_bound zero_le_one
  intro x
  have h := P.apply_norm_sq_eq_inner_adjoint_left x
  rw [hstar] at h
  change ‖P x‖ ^ 2 = Complex.re ⟪P (P x), x⟫_ℂ at h
  rw [hi] at h
  have hx := (Complex.re_le_norm _).trans (norm_inner_le_norm (𝕜 := ℂ) (P x) x)
  rw [← h] at hx
  rw [one_mul]
  nlinarith [norm_nonneg (P x), norm_nonneg x]

/-- Proposition C.3.5.1 in the spectral trace norm. -/
theorem RankOneSeries.spectralTraceNorm_orthogonal_cutoff (T : RankOneSeries ℕ H)
    (b : HilbertBasis ι ℂ H) (K : κ → Submodule ℂ H) [∀ i, (K i).HasOrthogonalProjection]
    (hK : Pairwise fun i j => K i ⟂ K j) (stages : ℕ → Finset κ)
    (hstrong : ∀ x, Tendsto (fun S : Finset κ => (∑ i ∈ S, (K i).starProjection) x) atTop (𝓝 x))
    (hcofinal : Tendsto stages atTop atTop) :
    Tendsto (fun n => spectralTraceNorm b
      (((∑ i ∈ stages n, (K i).starProjection) ∘L T.operator) - T.operator)) atTop (𝓝 0) ∧
    Tendsto (fun n => ∑ i ∈ stages n, (T.leftComp (K i).starProjection).trace) atTop (𝓝 T.trace) := by
  have h := T.nuclearTraceNorm_cofinal_cutoff (fun i => (K i).starProjection) stages
    (norm_sum_pairwise_orthogonal_projections_le_one K hK) hstrong hcofinal
  refine ⟨?_, h.2⟩
  convert h.1 using 1
  ext n
  symm
  apply nuclearTraceNorm_eq_spectral _ _ b
  exact Submodule.sub_mem _ (nuclearOperators_comp_left _ ⟨T, rfl⟩) ⟨T, rfl⟩

omit [CompleteSpace H] in
theorem tendsto_exhausting_starProjection (K : ℕ → Submodule ℂ H)
    [∀ i, (K i).HasOrthogonalProjection] (hK : Monotone K)
    (hd : Dense (⋃ i, (K i : Set H))) (x : H) :
    Tendsto (fun n => (K n).starProjection x) atTop (𝓝 x) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨y, hy, hyx⟩ := Metric.mem_closure_iff.mp (hd x) (ε / 2) (by positivity)
  obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hy
  refine ⟨m, fun n hn => ?_⟩
  have hny : (K n).starProjection y = y :=
    (K n).starProjection_eq_self_iff.mpr (hK hn hm)
  rw [dist_eq_norm] at hyx ⊢
  have h₁ : ‖(K n).starProjection x - y‖ ≤ ‖x - y‖ := by
    conv_lhs => rw [← hny, ← map_sub]
    exact ((K n).starProjection.le_opNorm _).trans
      (mul_le_of_le_one_left (norm_nonneg _) (K n).starProjection_norm_le)
  have h₂ := dist_triangle ((K n).starProjection x) y x
  simp only [dist_eq_norm, norm_sub_rev y x] at h₂
  linarith

/-- Corollary C.3.5.5. Increasing dense filtrations converge strongly and converge
in spectral trace norm after composition on either side of a nuclear operator. -/
theorem RankOneSeries.spectralTraceNorm_exhausting_filtration (T : RankOneSeries ℕ H)
    (b : HilbertBasis ι ℂ H) (K : ℕ → Submodule ℂ H)
    [∀ i, (K i).HasOrthogonalProjection] (hK : Monotone K)
    (hd : Dense (⋃ i, (K i : Set H))) :
    (∀ x, Tendsto (fun n => (K n).starProjection x) atTop (𝓝 x)) ∧
    Tendsto (fun n => spectralTraceNorm b ((K n).starProjection.comp T.operator - T.operator))
      atTop (𝓝 0) ∧
    Tendsto (fun n => spectralTraceNorm b (T.operator.comp (K n).starProjection - T.operator))
      atTop (𝓝 0) ∧
    Tendsto (fun n => (T.leftComp (K n).starProjection).trace) atTop (𝓝 T.trace) ∧
    Tendsto (fun n => (T.rightComp (K n).starProjection).trace) atTop (𝓝 T.trace) := by
  let A (n : ℕ) := (K n).starProjection
  have hn (n : ℕ) : ‖A n‖ ≤ 1 := (K n).starProjection_norm_le
  have ha (x : H) : Tendsto (fun n => A n x) atTop (𝓝 x) :=
    tendsto_exhausting_starProjection K hK hd x
  have hj (n : ℕ) : (A n).adjoint = A n := (isSelfAdjoint_starProjection (K n)).star_eq
  refine ⟨ha, ?_, ?_, T.trace_leftCutoff_tendsto A hn ha, T.trace_rightCutoff_tendsto A hn ha⟩
  · have hm := T.leftCutoff_representation_mass_tendsto A hn ha
    let R (n : ℕ) := T.leftComp (A n - ContinuousLinearMap.id ℂ H)
    have hR (n : ℕ) : (R n).operator = (A n).comp T.operator - T.operator := by
      change (T.leftComp (A n - ContinuousLinearMap.id ℂ H)).operator = _
      rw [RankOneSeries.operator_leftComp]
      ext x
      rfl
    have hEq (n : ℕ) : spectralTraceNorm b ((A n).comp T.operator - T.operator) =
        nuclearTraceNorm (R n).operator := by
      rw [← hR n]
      exact (nuclearTraceNorm_eq_spectral _ ⟨R n, rfl⟩ b).symm
    change Tendsto (fun n => spectralTraceNorm b ((A n).comp T.operator - T.operator)) _ _
    simp_rw [hEq]
    exact squeeze_zero (fun _ => nuclearTraceNorm_nonneg _)
      (fun n => nuclearTraceNorm_le_representation (R n)) hm
  · have he (n : ℕ) : (A n - ContinuousLinearMap.id ℂ H).adjoint =
        (A n).adjoint - ContinuousLinearMap.id ℂ H := by
      rw [map_sub, ContinuousLinearMap.adjoint_id]
    have hm := T.rightCutoff_representation_mass_tendsto A hn (by simpa only [hj] using ha)
    let R (n : ℕ) := T.rightComp (A n - ContinuousLinearMap.id ℂ H)
    have hR (n : ℕ) : (R n).operator = T.operator.comp (A n) - T.operator := by
      change (T.rightComp (A n - ContinuousLinearMap.id ℂ H)).operator = _
      rw [RankOneSeries.operator_rightComp, ContinuousLinearMap.comp_sub,
        ContinuousLinearMap.comp_id]
    have hEq (n : ℕ) : spectralTraceNorm b (T.operator.comp (A n) - T.operator) =
        nuclearTraceNorm (R n).operator := by
      rw [← hR n]
      exact (nuclearTraceNorm_eq_spectral _ ⟨R n, rfl⟩ b).symm
    change Tendsto (fun n => spectralTraceNorm b (T.operator.comp (A n) - T.operator)) _ _
    simp_rw [hEq]
    refine squeeze_zero (fun _ => nuclearTraceNorm_nonneg _) (fun n => ?_) hm
    simpa only [R, RankOneSeries.rightComp, he, sub_apply,
      ContinuousLinearMap.id_apply] using nuclearTraceNorm_le_representation (R n)

end

end Masullo
