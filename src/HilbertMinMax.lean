/-
Adapted from the Apache-2.0 RiemannMasullo project, commit
cd84b23dd5e4f741037cf31aee06bc90161c6514.
Sources and license are recorded in External/PROVENANCE.md.
-/
import ApproximationNumbers
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative

open Set Filter Topology

namespace Masullo

noncomputable section

open scoped InnerProductSpace

/-- An infinite orthonormal sequence cannot be used in a finite-dimensional Hilbert space. -/
theorem finiteDimensional_no_orthonormal_sequence
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] :
    ¬ ∃ e : ℕ → E, Orthonormal ℂ e := by
  rintro ⟨e, he⟩
  exact Module.Finite.not_linearIndependent_of_infinite e he.linearIndependent

set_option maxHeartbeats 450000 in
/-- A compact operator on a nontrivial complex Hilbert space attains its norm at a
unit eigenvector of its adjoint composed with itself. -/
theorem exists_unit_norm_eq_opNorm_of_isCompactOperator
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [Nontrivial E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (T : E →L[ℂ] F) (hT : IsCompactOperator T) :
    ∃ x : E, ‖x‖ = 1 ∧ ‖T x‖ = ‖T‖ ∧
      T.adjoint (T x) = (↑‖T‖ ^ 2 : ℂ) • x := by
  by_cases hzero : T = 0
  · obtain ⟨x, hx⟩ := exists_ne (0 : E)
    refine ⟨(↑‖x‖ : ℂ)⁻¹ • x, norm_smul_inv_norm hx, ?_, ?_⟩ <;> simp [hzero]
  let B := T.adjoint ∘L T
  have hB : IsCompactOperator B := hT.clm_comp T.adjoint
  have hBnorm : ‖B‖ = ‖T‖ ^ 2 := by
    simpa only [B, pow_two] using T.norm_adjoint_comp_self
  have hBpos : 0 ≤ B := by
    rw [ContinuousLinearMap.le_def, sub_zero]
    exact T.isPositive_adjoint_comp_self
  have hspec : (↑‖B‖ : ℂ) ∈ spectrum ℂ B :=
    spectrum.algebraMap_mem ℂ (CStarAlgebra.norm_mem_spectrum_of_nonneg hBpos)
  have hμ : (↑‖B‖ : ℂ) ≠ 0 := by
    simp [hBnorm, hzero]
  obtain ⟨y, hy⟩ := ((hB.hasEigenvalue_iff_mem_spectrum hμ).mpr hspec).exists_hasEigenvector
  obtain ⟨hy, hy0⟩ := Module.End.hasEigenvector_iff.mp hy
  let x : E := (↑‖y‖ : ℂ)⁻¹ • y
  have hx : ‖x‖ = 1 := norm_smul_inv_norm hy0
  have heig : B x = (↑‖T‖ ^ 2 : ℂ) • x := by
    have hy' : B y = (↑‖B‖ : ℂ) • y := Module.End.mem_eigenspace_iff.mp hy
    dsimp only [x]
    rw [map_smul, hy', smul_comm, hBnorm, Complex.ofReal_pow]
  refine ⟨x, hx, ?_, heig⟩
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  have hinner : RCLike.re ⟪x, B x⟫_ℂ = ‖T x‖ ^ 2 := by
    change RCLike.re ⟪x, T.adjoint (T x)⟫_ℂ = _
    rw [T.adjoint_inner_right, ← norm_sq_eq_re_inner]
  rw [← hinner, heig, inner_smul_right, inner_self_eq_norm_sq_to_K (𝕜 := ℂ) x, hx]
  simp [← Complex.ofReal_pow]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Within any positive operator-norm distance of `A.adjoint` there is a compact operator.
The approximant is `A.adjoint` postcomposed with the orthogonal projection onto a
finite-dimensional subspace, so it factors through a locally compact space. -/
private theorem exists_isCompactOperator_norm_sub_adjoint_le (A : H →L[ℂ] H)
    (hA : IsCompactOperator A) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : H →L[ℂ] H, IsCompactOperator C ∧ ‖A.adjoint - C‖ ≤ ε := by
  obtain ⟨t, -, ht_fin, ht_cover⟩ :=
    (hA.isCompact_closure_image_closedBall 1).finite_cover_balls hε
  let U : Submodule ℂ H := Submodule.span ℂ t
  have : FiniteDimensional ℂ U := FiniteDimensional.span_of_finite ℂ ht_fin
  have : CompleteSpace U := FiniteDimensional.complete ℂ U
  have : U.HasOrthogonalProjection := inferInstance
  have hnorm : ‖A - U.starProjection ∘L A‖ ≤ ε := by
    refine ContinuousLinearMap.opNorm_le_bound _ hε.le fun x ↦ ?_
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · have hx0 : 0 < ‖x‖ := norm_pos_iff.mpr hx
      let u : H := (‖x‖⁻¹ : ℂ) • x
      have hu : ‖u‖ = 1 := by
        rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0,
          inv_mul_cancel₀ hx0.ne']
      have hBu : ‖(A - U.starProjection ∘L A) u‖ < ε := by
        have hu_ball : u ∈ Metric.closedBall (0 : H) 1 := by
          rw [Metric.mem_closedBall, dist_zero_right, hu]
        have hAu : A u ∈ closure (A '' Metric.closedBall (0 : H) 1) :=
          subset_closure ⟨u, hu_ball, rfl⟩
        obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (ht_cover hAu)
        rw [sub_apply, ContinuousLinearMap.comp_apply, U.starProjection_minimal]
        refine lt_of_le_of_lt ?_ (Metric.mem_ball.mp hxy)
        rw [dist_eq_norm]
        change _ ≤ ‖A u - (⟨y, Submodule.subset_span hy⟩ : U)‖
        exact ciInf_le ⟨0, Set.forall_mem_range.mpr fun _ => norm_nonneg _⟩ _
      have hxeq : (‖x‖ : ℂ) • u = x := by
        simp only [u, smul_smul, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hx0.ne'), one_smul]
      have hBx : ‖(A - U.starProjection ∘L A) x‖ =
          ‖x‖ * ‖(A - U.starProjection ∘L A) u‖ := by
        conv_lhs => rw [← hxeq]
        rw [(A - U.starProjection ∘L A).map_smul, norm_smul, Complex.norm_real,
          Real.norm_eq_abs, abs_of_nonneg hx0.le]
      rw [hBx]
      calc
        ‖x‖ * ‖(A - U.starProjection ∘L A) u‖ ≤ ‖x‖ * ε :=
          mul_le_mul_of_nonneg_left hBu.le hx0.le
        _ = ε * ‖x‖ := mul_comm _ _
  refine ⟨A.adjoint ∘L U.starProjection, ?_, ?_⟩
  · have : LocallyCompactSpace U :=
      LocallyCompactSpace.of_finiteDimensional_of_complete ℂ U
    have hfac : A.adjoint ∘L U.starProjection =
        (A.adjoint ∘L U.subtypeL) ∘L U.orthogonalProjectionOnto := rfl
    rw [hfac]
    exact (isCompactOperator_of_locallyCompactSpace_rng
      (A.adjoint ∘L U.subtypeL)).comp_clm U.orthogonalProjectionOnto
  · rw [← (isSelfAdjoint_starProjection U).adjoint_eq, ← ContinuousLinearMap.adjoint_comp,
      ← (ContinuousLinearMap.adjoint (E := H) (F := H)).map_sub,
      (ContinuousLinearMap.adjoint (E := H) (F := H)).norm_map]
    exact hnorm

/-- Paper: Lemma C.3.5.3(1), p. 700. The adjoint of a compact endomorphism is compact. -/
theorem isCompactOperator_adjoint_of_compact (A : H →L[ℂ] H)
    (hA : IsCompactOperator A) : IsCompactOperator A.adjoint := by
  have happrox : ∀ n : ℕ, ∃ C : H →L[ℂ] H,
      IsCompactOperator C ∧ ‖A.adjoint - C‖ ≤ 1 / (n + 1 : ℝ) := by
    intro n
    exact exists_isCompactOperator_norm_sub_adjoint_le A hA (by positivity)
  choose C hC hle using happrox
  refine isCompactOperator_of_tendsto (l := atTop) (F := C) ?_ (Eventually.of_forall hC)
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
  refine ⟨N, fun n hn ↦ ?_⟩
  rw [dist_eq_norm, norm_sub_rev]
  refine (hle n).trans_lt ?_
  have hbig : 1 / ε < (n : ℝ) + 1 :=
    lt_trans (lt_of_lt_of_le hN (Nat.cast_le.mpr hn)) (lt_add_one _)
  have hmul : 1 < ((n : ℝ) + 1) * ε := (div_lt_iff₀ hε).mp hbig
  rw [show (1 : ℝ) / (n + 1 : ℝ) = 1 / ((n : ℝ) + 1) by simp,
    div_lt_iff₀' (by positivity)]
  exact hmul

/-- The restriction of `A` to the orthogonal complement of a proper finite-dimensional
subspace has a maximizing unit vector. Its image is orthogonal to the images of all vectors
in the complement that are orthogonal to it. -/
private theorem exists_unit_maximizer_on_orthogonal (A : H →L[ℂ] H) (hA : IsCompactOperator A)
    {n : ℕ} (hn : (n : Cardinal) < Module.rank ℂ H)
    {V : Submodule ℂ H} (hV : Module.rank ℂ V = (n : Cardinal)) :
    ∃ e ∈ Vᗮ, ‖e‖ = 1 ∧ ‖A e‖ = ‖A.comp Vᗮ.subtypeL‖ ∧
      ∀ y ∈ Vᗮ, ⟪e, y⟫_ℂ = 0 → ⟪A e, A y⟫_ℂ = 0 := by
  have : FiniteDimensional ℂ V :=
    Module.rank_lt_aleph0_iff.mp (hV.trans_lt Cardinal.natCast_lt_aleph0)
  let : CompleteSpace V := inferInstance
  have hproper : V ≠ ⊤ := by
    intro h
    exact hn.ne (by rw [← hV, h, rank_top])
  have : Nontrivial Vᗮ := Submodule.nontrivial_iff_ne_bot.mpr
    (fun h ↦ hproper (V.orthogonal_eq_bot_iff.mp h))
  let T := A.comp Vᗮ.subtypeL
  obtain ⟨e, he, heA, heig⟩ :=
    exists_unit_norm_eq_opNorm_of_isCompactOperator T (hA.comp_clm Vᗮ.subtypeL)
  refine ⟨e, e.property, he, heA, fun y hy hinner ↦ ?_⟩
  let z : Vᗮ := ⟨y, hy⟩
  change ⟪T e, T z⟫_ℂ = 0
  rw [← T.adjoint_inner_left, heig, inner_smul_left]
  change (starRingEnd ℂ _) * ⟪(e : H), y⟫_ℂ = 0
  rw [hinner, mul_zero]

/-- Adjoin a maximizing line to a subspace whose image is orthogonal to the image of its
orthogonal complement. The enlarged subspace retains this property and has a lower
norm bound given by the old restriction norm. -/
private theorem exists_succ_rank_subspace_of_compact (A : H →L[ℂ] H)
    (hA : IsCompactOperator A) {n : ℕ} (hn : (n : Cardinal) < Module.rank ℂ H)
    {V : Submodule ℂ H} (hV : Module.rank ℂ V = (n : Cardinal))
    (horth : ∀ x ∈ V, ∀ y ∈ Vᗮ, ⟪A x, A y⟫_ℂ = 0)
    (hlower : ∀ x ∈ V, ‖A.comp Vᗮ.subtypeL‖ * ‖x‖ ≤ ‖A x‖) :
    ∃ U : Submodule ℂ H, V ≤ U ∧ Module.rank ℂ U = ((n + 1 : ℕ) : Cardinal) ∧
      (∀ x ∈ U, ∀ y ∈ Uᗮ, ⟪A x, A y⟫_ℂ = 0) ∧
      ∀ x ∈ U, ‖A.comp Vᗮ.subtypeL‖ * ‖x‖ ≤ ‖A x‖ := by
  obtain ⟨e, heV, he, heA, heorth⟩ := exists_unit_maximizer_on_orthogonal A hA hn hV
  let L : Submodule ℂ H := ℂ ∙ e
  have hL : L ≤ Vᗮ := Submodule.span_le.mpr (Set.singleton_subset_iff.mpr heV)
  have he0 : e ≠ 0 := by
    intro h
    simp [h] at he
  have hrankL : Module.rank ℂ L = 1 := by
    rw [← Module.finrank_eq_rank, finrank_span_singleton he0, Nat.cast_one]
  have hrank : Module.rank ℂ (V ⊔ L : Submodule ℂ H) = ((n + 1 : ℕ) : Cardinal) := by
    have hinf : V ⊓ L = ⊥ := (V.orthogonal_disjoint.mono_right hL).eq_bot
    have h := V.rank_sup_add_rank_inf_eq L
    rw [hinf, rank_bot, add_zero, hV, hrankL] at h
    simpa only [Nat.cast_add, Nat.cast_one] using h
  refine ⟨V ⊔ L, le_sup_left, hrank, ?_, ?_⟩
  · intro x hx y hy
    obtain ⟨v, hv, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hz
    have hyV : y ∈ Vᗮ := Submodule.orthogonal_le le_sup_left hy
    have hyL : y ∈ Lᗮ := Submodule.orthogonal_le le_sup_right hy
    rw [map_add, map_smul, inner_add_left, inner_smul_left, horth v hv y hyV,
      heorth y hyV (Submodule.mem_orthogonal_singleton_iff_inner_right.mp hyL), mul_zero,
      add_zero]
  · intro x hx
    obtain ⟨v, hv, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
    have hzV : z ∈ Vᗮ := hL hz
    let c := ‖A.comp Vᗮ.subtypeL‖
    have hz_eq : ‖A z‖ = c * ‖z‖ := by
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hz
      rw [map_smul, norm_smul, norm_smul, heA, he, mul_one, mul_comm]
    apply le_of_sq_le_sq _ (norm_nonneg _)
    change (c * ‖v + z‖) ^ 2 ≤ ‖A (v + z)‖ ^ 2
    calc
      (c * ‖v + z‖) ^ 2 = (c * ‖v‖) ^ 2 + (c * ‖z‖) ^ 2 := by
        rw [mul_pow, norm_add_sq (𝕜 := ℂ) v z, (V.mem_orthogonal z).mp hzV v hv]
        simp only [RCLike.zero_re, mul_zero, add_zero, mul_add, mul_pow]
      _ ≤ ‖A v‖ ^ 2 + ‖A z‖ ^ 2 := by
        rw [← hz_eq]
        exact add_le_add ((sq_le_sq₀ (by positivity) (norm_nonneg _)).mpr (hlower v hv)) le_rfl
      _ = ‖A (v + z)‖ ^ 2 := by
        rw [map_add, norm_add_sq (𝕜 := ℂ) (A v) (A z), horth v hv z hzV]
        simp

/-- There are `n` dimensions whose image is orthogonal to the image of the complement, with
norm bounded below by the norm of the operator on the complement. -/
private theorem exists_rank_subspace_of_compact (A : H →L[ℂ] H) (hA : IsCompactOperator A)
    (n : ℕ) (hn : (n : Cardinal) ≤ Module.rank ℂ H) :
    ∃ V : Submodule ℂ H, Module.rank ℂ V = (n : Cardinal) ∧
      (∀ x ∈ V, ∀ y ∈ Vᗮ, ⟪A x, A y⟫_ℂ = 0) ∧
      ∀ x ∈ V, ‖A.comp Vᗮ.subtypeL‖ * ‖x‖ ≤ ‖A x‖ := by
  induction n with
  | zero =>
    refine ⟨⊥, by simp, ?_, ?_⟩ <;> simp
  | succ n ih =>
    have hlt : (n : Cardinal) < Module.rank ℂ H :=
      (Nat.cast_lt.mpr (Nat.lt_succ_self n)).trans_le hn
    obtain ⟨V, hV, horth, hlower⟩ := ih hlt.le
    obtain ⟨U, hVU, hU, hUorth, hUlower⟩ :=
      exists_succ_rank_subspace_of_compact A hA hlt hV horth hlower
    refine ⟨U, hU, hUorth, fun x hx ↦ ?_⟩
    have hmono : ‖A.comp Uᗮ.subtypeL‖ ≤ ‖A.comp Vᗮ.subtypeL‖ := by
      refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg (A.comp Vᗮ.subtypeL)) fun y ↦ ?_
      exact (A.comp Vᗮ.subtypeL).le_opNorm ⟨y, Submodule.orthogonal_le hVU y.property⟩
    exact (mul_le_mul_of_nonneg_right hmono (norm_nonneg _)).trans (hUlower x hx)

/-- Paper: Lemma C.3.5.3(3), p. 700. The singular value is the smallest of
the attained maxima of the norm of A on the unit sphere of each orthogonal
complement of an n-dimensional subspace.
Deviation: The singular value has zero-based index n. -/
theorem approximationNumber_min_max (A : H →L[ℂ] H) (hA : IsCompactOperator A)
    (n : ℕ) (hn : (n : Cardinal) < Module.rank ℂ H) :
    ∃ maxima : {V : Submodule ℂ H // Module.rank ℂ V = (n : Cardinal)} → ℝ,
      (∀ V, IsGreatest {r | ∃ x ∈ Submodule.orthogonal (Subtype.val V), ‖x‖ = 1 ∧ r = ‖A x‖} (maxima V)) ∧
        IsLeast (Set.range maxima) (approximationNumber n A) := by
  let maxima (V : {V : Submodule ℂ H // Module.rank ℂ V = (n : Cardinal)}) :=
    ‖A.comp (Subtype.val V)ᗮ.subtypeL‖
  have hmax (V : {V : Submodule ℂ H // Module.rank ℂ V = (n : Cardinal)}) :
      IsGreatest {r | ∃ x ∈ (Subtype.val V)ᗮ, ‖x‖ = 1 ∧ r = ‖A x‖} (maxima V) := by
    obtain ⟨e, he, he1, heA, _⟩ := exists_unit_maximizer_on_orthogonal A hA hn V.property
    refine ⟨⟨e, he, he1, heA.symm⟩, ?_⟩
    rintro _ ⟨x, hx, hx1, rfl⟩
    simpa [maxima, hx1] using (A.comp V.valᗮ.subtypeL).le_opNorm ⟨x, hx⟩
  have hle (V : {V : Submodule ℂ H // Module.rank ℂ V = (n : Cardinal)}) :
      approximationNumber n A ≤ maxima V := by
    have : FiniteDimensional ℂ V.val :=
      Module.rank_lt_aleph0_iff.mp (V.property.trans_lt Cardinal.natCast_lt_aleph0)
    let : CompleteSpace V.val := inferInstance
    -- Projecting onto V gives an admissible rank-n approximation.
    let S := A.comp V.val.starProjection
    have hS : Module.rank ℂ S.toLinearMap.range ≤ (n : Cardinal) := by
      refine (LinearMap.rank_comp_le_right V.val.starProjection.toLinearMap A.toLinearMap).trans ?_
      change Module.rank ℂ V.val.starProjection.toLinearMap.range ≤ (n : Cardinal)
      rw [Submodule.range_starProjection, V.property]
    have hdiff : A - S = (A.comp V.valᗮ.subtypeL).comp V.valᗮ.orthogonalProjectionOnto := by
      change A - S = A.comp V.valᗮ.starProjection
      ext x
      simp [S, map_sub]
    refine (approximationNumber_le A S hS).trans ?_
    rw [hdiff]
    change _ ≤ ‖A.comp V.valᗮ.subtypeL‖
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg (A.comp V.valᗮ.subtypeL)) fun x ↦ ?_
    exact ((A.comp V.valᗮ.subtypeL).le_opNorm (V.valᗮ.orthogonalProjectionOnto x)).trans
      (mul_le_mul_of_nonneg_left (V.valᗮ.norm_orthogonalProjectionOnto_apply_le x) (norm_nonneg _))
  obtain ⟨V, hV, horth, hlower⟩ := exists_rank_subspace_of_compact A hA n hn.le
  obtain ⟨U, _, hU, _, hUlower⟩ := exists_succ_rank_subspace_of_compact A hA hn hV horth hlower
  let V₀ : {V : Submodule ℂ H // Module.rank ℂ V = (n : Cardinal)} := ⟨V, hV⟩
  have hge : maxima V₀ ≤ approximationNumber n A := by
    apply le_approximationNumber A
    intro S hS
    -- Every admissible approximant kills a nonzero vector in U.
    let R := S.toLinearMap.rangeRestrict.comp U.subtype
    have hker : R.ker ≠ ⊥ := by
      intro h
      have hr := (R.rank_le_of_injective (LinearMap.ker_eq_bot.mp h)).trans hS
      rw [hU] at hr
      exact (not_le_of_gt (Nat.cast_lt.mpr (Nat.lt_succ_self n))) hr
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
    have hSx : S (x : H) = 0 := congrArg Subtype.val (LinearMap.mem_ker.mp hx)
    have hnorm : 0 < ‖(x : H)‖ := norm_pos_iff.mpr fun h ↦ hx0 (Subtype.ext h)
    have hbound := (A - S).le_opNorm (x : H)
    rw [sub_apply, hSx, sub_zero] at hbound
    exact le_of_mul_le_mul_right ((hUlower x x.property).trans hbound) hnorm
  refine ⟨maxima, hmax, ⟨⟨V₀, le_antisymm hge (hle V₀)⟩, ?_⟩⟩
  rintro _ ⟨W, rfl⟩
  exact hle W

/-- Paper: Lemma C.3.5.3(3), p. 700. The singular value is the largest of
the attained minima of the norm of A on the unit sphere of each
(n + 1)-dimensional subspace.
Deviation: The singular value has zero-based index n. -/
theorem approximationNumber_max_min (A : H →L[ℂ] H) (hA : IsCompactOperator A)
    (n : ℕ) (hn : (n : Cardinal) < Module.rank ℂ H) :
    ∃ minima : {V : Submodule ℂ H // Module.rank ℂ V = ((n + 1 : ℕ) : Cardinal)} → ℝ,
      (∀ V, IsLeast {r | ∃ x ∈ Subtype.val V, ‖x‖ = 1 ∧ r = ‖A x‖} (minima V)) ∧
        IsGreatest (Set.range minima) (approximationNumber n A) := by
  classical
  have hmin (U : {V : Submodule ℂ H // Module.rank ℂ V = ((n + 1 : ℕ) : Cardinal)}) :
      ∃ m : ℝ, IsLeast {r | ∃ x ∈ U.val, ‖x‖ = 1 ∧ r = ‖A x‖} m := by
    have : FiniteDimensional ℂ U.val :=
      Module.rank_lt_aleph0_iff.mp (U.property.trans_lt Cardinal.natCast_lt_aleph0)
    have : Nontrivial U.val := Submodule.nontrivial_iff_ne_bot.mpr fun h ↦
      (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)) (U.property.symm.trans (Submodule.rank_eq_zero.mpr h))
    let : ProperSpace U.val := FiniteDimensional.proper ℂ U.val
    obtain ⟨x, hx, hxmin⟩ := (isCompact_sphere (0 : U.val) 1).exists_isMinOn
      (Set.nonempty_coe_sort.mp (NormedSpace.sphere_nonempty_rclike ℂ zero_le_one))
      (A.comp U.val.subtypeL).continuous.norm.continuousOn
    refine ⟨‖A x‖, ⟨x, x.property, mem_sphere_zero_iff_norm.mp hx, rfl⟩, ?_⟩
    rintro _ ⟨y, hy, hy1, rfl⟩
    exact isMinOn_iff.mp hxmin ⟨y, hy⟩ (mem_sphere_zero_iff_norm.mpr hy1)
  choose minima hminima using hmin
  obtain ⟨maxima, hmaxima, hleast⟩ := approximationNumber_min_max A hA n hn
  obtain ⟨W, hW⟩ := hleast.1
  -- Every (n + 1)-dimensional subspace contains a unit vector orthogonal to W.
  have hle (U : {V : Submodule ℂ H // Module.rank ℂ V = ((n + 1 : ℕ) : Cardinal)}) :
      minima U ≤ approximationNumber n A := by
    have : FiniteDimensional ℂ W.val :=
      Module.rank_lt_aleph0_iff.mp (W.property.trans_lt Cardinal.natCast_lt_aleph0)
    let : CompleteSpace W.val := inferInstance
    let R := W.val.orthogonalProjectionOnto.toLinearMap.comp U.val.subtype
    have hker : R.ker ≠ ⊥ := by
      intro h
      have hrank := R.rank_le_of_injective (LinearMap.ker_eq_bot.mp h)
      rw [U.property, W.property] at hrank
      exact (not_le_of_gt (Nat.cast_lt.mpr (Nat.lt_succ_self n))) hrank
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
    let y : U.val := (↑‖x‖ : ℂ)⁻¹ • x
    have hy1 : ‖y‖ = 1 := norm_smul_inv_norm hx0
    have hyker : y ∈ R.ker := R.ker.smul_mem _ hx
    have hyW : (y : H) ∈ W.valᗮ := by
      rw [← W.val.ker_orthogonalProjectionOnto]
      exact hyker
    rw [← hW]
    exact (hminima U).2 ⟨y, y.property, hy1, rfl⟩ |>.trans
      ((hmaxima W).2 ⟨y, hyW, hy1, rfl⟩)
  -- Enlarging V by a maximizing line bounds the new minimum from below.
  obtain ⟨V, hV, horth, hlower⟩ := exists_rank_subspace_of_compact A hA n hn.le
  obtain ⟨U, _, hU, _, hUlower⟩ := exists_succ_rank_subspace_of_compact A hA hn hV horth hlower
  let V₀ : {V : Submodule ℂ H // Module.rank ℂ V = (n : Cardinal)} := ⟨V, hV⟩
  let U₀ : {V : Submodule ℂ H // Module.rank ℂ V = ((n + 1 : ℕ) : Cardinal)} := ⟨U, hU⟩
  have hge : approximationNumber n A ≤ minima U₀ := by
    obtain ⟨v, hv, hv1, hvA⟩ := (hmaxima V₀).1
    obtain ⟨u, hu, hu1, huA⟩ := (hminima U₀).1
    calc
      approximationNumber n A ≤ maxima V₀ := hleast.2 ⟨V₀, rfl⟩
      _ ≤ ‖A.comp Vᗮ.subtypeL‖ := by
        rw [hvA]
        simpa [hv1] using (A.comp Vᗮ.subtypeL).le_opNorm ⟨v, hv⟩
      _ ≤ minima U₀ := by simpa [hu1, huA] using hUlower u hu
  refine ⟨minima, hminima, ⟨⟨U₀, le_antisymm (hle U₀) hge⟩, ?_⟩⟩
  rintro _ ⟨U, rfl⟩
  exact hle U

omit [CompleteSpace H] in
/-- A compact operator's products with a bounded operator are compact, and
both singular-value bounds use the same zero-based approximation index. -/
theorem compact_singularValue_compositions (A B : H →L[ℂ] H) (hA : IsCompactOperator A)
    (n : ℕ) :
    IsCompactOperator (A.comp B) ∧ IsCompactOperator (B.comp A) ∧
      approximationNumber n (A.comp B) ≤ approximationNumber n A * ‖B‖ ∧
      approximationNumber n (B.comp A) ≤ approximationNumber n A * ‖B‖ := by
  exact ⟨hA.comp_clm B, hA.clm_comp B, approximationNumber_comp_right_le A B n,
    mul_comm ‖B‖ (approximationNumber n A) ▸ approximationNumber_comp_left_le B A n⟩

end
end Masullo
