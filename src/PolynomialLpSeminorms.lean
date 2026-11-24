import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Analysis.Complex.Basic

namespace Masullo

open MeasureTheory
open scoped ENNReal BigOperators

section Span

variable {E V I J : Type*} [AddCommGroup E] [Module ℂ E]
  [SeminormedAddCommGroup V] [NormedSpace ℂ V]

private theorem normSeminorms_bounded_of_span_le
    (A : I → E →ₗ[ℂ] V) (B : J → E →ₗ[ℂ] V)
    (h : Submodule.span ℂ (Set.range B) ≤ Submodule.span ℂ (Set.range A)) :
    Seminorm.IsBounded (fun i ↦ (normSeminorm ℂ V).comp (A i))
      (fun j ↦ (normSeminorm ℂ V).comp (B j)) LinearMap.id := by
  classical
  apply Seminorm.IsBounded.of_real
  intro j
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp
    (h (Submodule.subset_span (Set.mem_range_self j)))
  refine ⟨c.support, ∑ i ∈ c.support, ‖c i‖, fun f ↦ ?_⟩
  change ‖B j f‖ ≤ _
  rw [← hc, Finsupp.sum, LinearMap.sum_apply]
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  rw [LinearMap.smul_apply, norm_smul]
  exact mul_le_mul_of_nonneg_left
    ((Finset.le_sup (f := fun i ↦ (normSeminorm ℂ V).comp (A i)) hi) f) (norm_nonneg _)

/-- Norm seminorms of linear operator families with the same span generate the same topology. -/
theorem withNormSeminorms_iff_of_span_eq [TopologicalSpace E]
    (A : I → E →ₗ[ℂ] V) (B : J → E →ₗ[ℂ] V)
    (h : Submodule.span ℂ (Set.range A) = Submodule.span ℂ (Set.range B)) :
    WithSeminorms (fun i ↦ (normSeminorm ℂ V).comp (A i)) ↔
      WithSeminorms (fun j ↦ (normSeminorm ℂ V).comp (B j)) := by
  have hAB := normSeminorms_bounded_of_span_le A B h.ge
  have hBA := normSeminorms_bounded_of_span_le B A h.le
  exact ⟨fun hA ↦ hA.congr hAB hBA, fun hB ↦ hB.congr hBA hAB⟩

end Span

section Polynomial

variable {E X I : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
  [MeasurableSpace X] {μ : Measure X} {p : ℝ≥0∞} [Fact (1 ≤ p)]
  (D : I → E →ₗ[ℂ] X → ℂ) (s : X → ℝ)
  (h : ∀ i n f, MemLp (fun x ↦ (s x : ℂ) ^ n * D i f x) p μ)

private noncomputable def powerWeightLp (i : I) (n : ℕ) : E →ₗ[ℂ] Lp ℂ p μ where
  toFun f := (h i n f).toLp _
  map_add' f g := by
    rw [← MemLp.toLp_add (h i n f) (h i n g)]
    exact (h i n (f + g)).toLp_congr _ (Filter.Eventually.of_forall fun x ↦ by
      simp [mul_add])
  map_smul' c f := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul c (h i n f)]
    exact (h i n (c • f)).toLp_congr _ (Filter.Eventually.of_forall fun x ↦ by
      simp [smul_eq_mul, mul_left_comm])

private noncomputable def polynomialWeightLp (i : I) (P : Polynomial ℂ) :
    E →ₗ[ℂ] Lp ℂ p μ :=
  ∑ n ∈ P.support, P.coeff n • powerWeightLp D s h i n

omit [TopologicalSpace E] [Fact (1 ≤ p)] in
private theorem polynomialWeightLp_ae (i : I) (P : Polynomial ℂ) (f : E) :
    ⇑(polynomialWeightLp D s h i P f) =ᵐ[μ] fun x ↦ P.eval (s x : ℂ) * D i f x := by
  classical
  simp only [polynomialWeightLp, LinearMap.sum_apply, LinearMap.smul_apply]
  refine (Lp.coeFn_finsetSum P.support _).trans ?_
  have each (n : ℕ) :
      ⇑(P.coeff n • powerWeightLp D s h i n f) =ᵐ[μ]
        fun x ↦ P.coeff n * ((s x : ℂ) ^ n * D i f x) := by
    refine (Lp.coeFn_smul _ _).trans ?_
    filter_upwards [(h i n f).coeFn_toLp] with x hx
    change P.coeff n * (h i n f).toLp _ x = _
    rw [hx]
  filter_upwards [(Filter.eventually_all_finset P.support).mpr (fun n _ ↦ each n)] with x hx
  simp only [Finset.sum_apply, Polynomial.eval_eq_sum, Polynomial.sum, Finset.sum_mul, mul_assoc]
  exact Finset.sum_congr rfl (fun n hn ↦ hx n hn)

local notation "S" => normSeminorm ℂ (Lp ℂ p μ)

include h in
/-- The three polynomial weight families in D.1.10.9 and D.1.10.10 generate the same
topology once the monomial-weighted profiles belong to Lᵖ. The coordinate can
be the absolute log modulus on either idele class group. -/
theorem polynomialLpSeminorms_same_topology :
    ∃ M U : SeminormFamily ℂ E (I × ℕ), ∃ P : SeminormFamily ℂ E (I × Polynomial ℂ),
      (∀ i n f, M (i, n) f = lpNorm (fun x ↦ (s x : ℂ) ^ n * D i f x) p μ) ∧
      (∀ i n f, U (i, n) f = lpNorm (fun x ↦ (1 + (s x : ℂ) ^ n) * D i f x) p μ) ∧
      (∀ i Q f, P (i, Q) f = lpNorm (fun x ↦ Q.eval (s x : ℂ) * D i f x) p μ) ∧
      (WithSeminorms M ↔ WithSeminorms U) ∧ (WithSeminorms M ↔ WithSeminorms P) := by
  classical
  let A (i : I × ℕ) := powerWeightLp D s h i.1 i.2
  let B (i : I × ℕ) := A (i.1, 0) + A i
  let C (i : I × Polynomial ℂ) := polynomialWeightLp D s h i.1 i.2
  have rep {u : Lp ℂ p μ} {F : X → ℂ} (hf : ⇑u =ᵐ[μ] F) : ‖u‖ = lpNorm F p μ := by
    have hm : MemLp F p μ := (Lp.memLp u).ae_eq hf
    calc
      ‖u‖ = ‖hm.toLp F‖ := congrArg norm
        ((Lp.toLp_coeFn u (Lp.memLp u)).symm.trans ((Lp.memLp u).toLp_congr hm hf))
      _ = lpNorm F p μ := (Lp.norm_toLp _ hm).trans (toReal_eLpNorm hm.aestronglyMeasurable)
  refine ⟨fun i ↦ (S).comp (A i), fun i ↦ (S).comp (B i), fun i ↦ (S).comp (C i), ?_, ?_, ?_, ?_, ?_⟩
  · intro i n f
    exact rep (h i n f).coeFn_toLp
  · intro i n f
    change ‖B (i,n) f‖ = _
    apply rep
    change ⇑(A (i,0) f + A (i,n) f) =ᵐ[μ] _
    refine (Lp.coeFn_add _ _).trans ?_
    filter_upwards [(h i 0 f).coeFn_toLp, (h i n f).coeFn_toLp] with x hx hy
    change (h i 0 f).toLp _ x + (h i n f).toLp _ x = _
    rw [hx, hy, add_mul, pow_zero]
  · intro i Q f
    exact rep (polynomialWeightLp_ae D s h i Q f)
  · apply withNormSeminorms_iff_of_span_eq
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨⟨i,n⟩, rfl⟩
      have h0 : A (i, 0) = (2 : ℂ)⁻¹ • B (i, 0) := by
        simp [B, ← two_smul ℂ, smul_smul]
      rw [show A (i,n) = B (i,n) - A (i,0) by simp [B, add_comm], h0]
      exact Submodule.sub_mem _ (Submodule.subset_span (Set.mem_range_self _))
        (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self _)))
    · apply Submodule.span_le.mpr
      rintro _ ⟨⟨i,n⟩, rfl⟩
      exact Submodule.add_mem _ (Submodule.subset_span (Set.mem_range_self _))
        (Submodule.subset_span (Set.mem_range_self _))
  · apply withNormSeminorms_iff_of_span_eq
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨⟨i,n⟩, rfl⟩
      have he : C (i, Polynomial.monomial n 1) = A (i,n) := by
        simp [C, A, polynomialWeightLp, Polynomial.support_monomial]
      exact he ▸ Submodule.subset_span (Set.mem_range_self _)
    · apply Submodule.span_le.mpr
      rintro _ ⟨⟨i,Q⟩, rfl⟩
      exact Submodule.sum_mem _ fun n _ ↦
        Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self (i,n)))

end Polynomial

end Masullo
