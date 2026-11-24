/-
The geometric majorant adapts the Apache-2.0 RiemannMasullo project,
commit a2122bbe45051e5ad120fe271e18a93b75ec473b. See External/PROVENANCE.md.
-/
import HeckeEulerProducts
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn

open Filter Topology Set NumberField IsDedekindDomain
open scoped SchwartzMap NumberField

namespace Masullo

noncomputable section

private def diracCombTerm (q σ : ℝ) (w : Circle) (n : ℕ) (f : 𝓢(ℝ, ℂ)) : ℂ :=
  ((w : ℂ) ^ (n + 1) * (q ^ ((n + 1 : ℕ) * σ) : ℝ)) * f (q ^ (n + 1))

/-- The geometric comparison on p. 611 uses exponent `-2(n+1)`
when the positive powers of the prime norm are indexed from zero. -/
theorem diracComb_geometric_majorant_sum {q : ℝ} (hq : 1 < q) (A : ℝ) :
    ∑' n : ℕ, A * q ^ (-2 * ((n + 1 : ℕ) : ℝ)) = A / (q ^ 2 - 1) := by
  have hpos : 0 < q := zero_lt_one.trans hq
  let r : ℝ := (q ^ 2)⁻¹
  have hr₀ : 0 ≤ r := by positivity
  have hq₂ : 1 < q ^ 2 := by nlinarith
  have hr₁ : r < 1 := inv_lt_one_of_one_lt₀ hq₂
  have he (n : ℕ) : q ^ (-2 * ((n + 1 : ℕ) : ℝ)) = r ^ (n + 1) := by
    rw [Real.rpow_mul_natCast hpos.le, Real.rpow_neg hpos.le]
    norm_num [r, Real.rpow_natCast]
  simp_rw [he, pow_succ]
  rw [tsum_mul_left, tsum_mul_right, tsum_geometric_of_lt_one hr₀ hr₁]
  dsimp only [r]
  field_simp [show q ≠ 0 from hpos.ne', show q ^ 2 - 1 ≠ 0 by linarith]

/-- A single Schwartz seminorm bounds the comb by a summable geometric sequence. -/
private theorem diracComb_majorant {q : ℝ} (hq : 1 < q) (σ : ℝ) (w : Circle) :
    ∃ (k : ℕ) (r : ℝ), (∀ n : ℕ, 0 ≤ r ^ (n + 1)) ∧
      Summable (fun n : ℕ => r ^ (n + 1)) ∧
      ∀ n f, ‖diracCombTerm q σ w n f‖ ≤ r ^ (n + 1) * SchwartzMap.seminorm ℂ k 0 f := by
  obtain ⟨k, hk⟩ := exists_nat_gt σ
  have hq₀ := zero_lt_one.trans hq
  let r : ℝ := q ^ (σ - k)
  have hr₀ : 0 ≤ r := Real.rpow_nonneg hq₀.le _
  have hr₁ : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg hq (sub_neg.mpr hk)
  have hfactor : r * q ^ k = q ^ σ := by
    dsimp only [r]
    rw [← Real.rpow_natCast q k, ← Real.rpow_add hq₀, sub_add_cancel]
  refine ⟨k, r, fun n => pow_nonneg hr₀ _, (summable_nat_add_iff 1).2
    (summable_geometric_of_lt_one hr₀ hr₁), fun n f => ?_⟩
  have hf := SchwartzMap.norm_pow_mul_le_seminorm ℂ f k (q ^ (n + 1))
  rw [Real.norm_of_nonneg (pow_nonneg hq₀.le _)] at hf
  unfold diracCombTerm
  rw [norm_mul, norm_mul, norm_pow, Circle.norm_coe, one_pow, one_mul,
    Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hq₀.le _),
    mul_comm ((n + 1 : ℕ) : ℝ) σ, Real.rpow_mul_natCast hq₀.le, ← hfactor, mul_pow,
    ← pow_mul, Nat.mul_comm k (n + 1), pow_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left hf (pow_nonneg hr₀ _)

private theorem diracComb_pointwise_summable {q : ℝ} (hq : 1 < q) (σ : ℝ) (w : Circle)
    (f : 𝓢(ℝ, ℂ)) : Summable (fun n => diracCombTerm q σ w n f) := by
  obtain ⟨k, r, _, hsum, hbound⟩ := diracComb_majorant hq σ w
  exact (hsum.mul_right (SchwartzMap.seminorm ℂ k 0 f)).of_norm_bounded (fun n => hbound n f)

/-- The weighted Dirac sum is a continuous linear functional on Schwartz tests. -/
def weightedDiracComb {q : ℝ} (hq : 1 < q) (σ : ℝ) (w : Circle) : 𝓢(ℝ, ℂ) →L[ℂ] ℂ :=
  SchwartzMap.mkCLMtoNormedSpace
    (fun f => ∑' n, diracCombTerm q σ w n f)
    (fun f g => by
      rw [← (diracComb_pointwise_summable hq σ w f).tsum_add
        (diracComb_pointwise_summable hq σ w g)]
      exact tsum_congr fun n => by simp [diracCombTerm, mul_add])
    (fun c f => by
      rw [RingHom.id_apply, ← (diracComb_pointwise_summable hq σ w f).tsum_const_smul c]
      exact tsum_congr fun n => by simp [diracCombTerm, smul_eq_mul, mul_left_comm])
    (by
      obtain ⟨k, r, hr, hsum, hbound⟩ := diracComb_majorant hq σ w
      refine ⟨{(k, 0)}, ∑' n : ℕ, r ^ (n + 1), tsum_nonneg hr, fun f => ?_⟩
      rw [Finset.sup_singleton]
      exact tsum_of_norm_bounded (hsum.hasSum.mul_right _) (fun n => hbound n f))

/-- Each summand is the specified weighted point evaluation. -/
def weightedDiracCombAtom (q σ : ℝ) (w : Circle) (n : ℕ) : 𝓢(ℝ, ℂ) →L[ℂ] ℂ :=
  SchwartzMap.mkCLMtoNormedSpace (diracCombTerm q σ w n)
    (fun f g => by simp [diracCombTerm, mul_add])
    (fun c f => by simp [diracCombTerm, smul_eq_mul, mul_left_comm])
    (by
      let a := (w : ℂ) ^ (n + 1) * (q ^ ((n + 1 : ℕ) * σ) : ℝ)
      refine ⟨{(0, 0)}, ‖a‖, norm_nonneg _, fun f => ?_⟩
      rw [Finset.sup_singleton]
      change ‖a * f (q ^ (n + 1))‖ ≤ _
      rw [norm_mul]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      simpa using SchwartzMap.norm_pow_mul_le_seminorm ℂ f 0 (q ^ (n + 1)))

/-- B.4.1.18 and the convergence claim in B.4.1.6. The sum converges in the
strong dual, meaning uniformly on every von Neumann bounded set of tests. -/
theorem hasSum_weightedDiracComb_strong {q : ℝ} (hq : 1 < q) (σ : ℝ) (w : Circle) :
    HasSum (weightedDiracCombAtom q σ w) (weightedDiracComb hq σ w) := by
  change Tendsto _ atTop (𝓝 _)
  apply (UniformConvergenceCLM.tendsto_iff_tendstoUniformlyOn (RingHom.id ℂ) ℂ
    {B : Set 𝓢(ℝ, ℂ) | Bornology.IsVonNBounded ℂ B}).mpr
  intro B hB
  obtain ⟨k, r, hr, hsum, hbound⟩ := diracComb_majorant hq σ w
  obtain ⟨M, _, hM⟩ := (schwartz_withSeminorms ℂ ℝ ℂ).isVonNBounded_iff_seminorm_bounded.mp
    hB (k, 0)
  have hU := HasSumUniformlyOn.of_norm_le_summable (s := B) (hsum.mul_right M)
    (fun n f hf => (hbound n f).trans (mul_le_mul_of_nonneg_left (hM f hf).le (hr n)))
  refine (hasSumUniformlyOn_iff_tendstoUniformlyOn.mp hU).congr
    (Eventually.of_forall fun s f _ => ?_)
  change (∑ n ∈ s, diracCombTerm q σ w n f) = (∑ n ∈ s, weightedDiracCombAtom q σ w n) f
  exact (sum_apply s (weightedDiracCombAtom q σ w) f).symm

/-- Evaluation recovers the absolutely convergent numerical series at each test. -/
theorem hasSum_weightedDiracComb_apply {q : ℝ} (hq : 1 < q) (σ : ℝ) (w : Circle)
    (f : 𝓢(ℝ, ℂ)) :
    HasSum (fun n : ℕ => ((w : ℂ) ^ (n + 1) * (q ^ ((n + 1 : ℕ) * σ) : ℝ)) *
      f (q ^ (n + 1))) (weightedDiracComb hq σ w f) :=
  (diracComb_pointwise_summable hq σ w f).hasSum

/-- The case of an unramified Hecke character at a finite place. Its value on a
uniformizer and the ideal norm give the phase and support in (B.4.1.18). -/
theorem hasSum_localHeckeDiracComb (F : Type*) [Field F] [NumberField F]
    (χ : PontryaginDual (IdeleClass F)) (v : HeightOneSpectrum (𝓞 F))
    (hχ : unramifiedFiniteCharacter F χ v)
    (π : (v.adicCompletion F)ˣ) (hπ : Valued.v.IsUniformizer (π : v.adicCompletion F))
    (σ : ℝ) :
    let q : ℝ := v.asIdeal.absNorm
    let hq : 1 < q := by
      dsimp only [q]
      exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
    let w := χ (ideleClassMap F (singleFiniteIdele F v π))
    HasSum (weightedDiracCombAtom q σ w) (weightedDiracComb hq σ w) ∧
      ∀ ϖ : (v.adicCompletion F)ˣ, Valued.v.IsUniformizer (ϖ : v.adicCompletion F) →
        χ (ideleClassMap F (singleFiniteIdele F v ϖ)) = w :=
  ⟨hasSum_weightedDiracComb_strong _ _ _, fun ϖ hϖ =>
    unramifiedFiniteCharacter_uniformizer_eq F χ v hχ ϖ π hϖ hπ⟩

end

end Masullo
