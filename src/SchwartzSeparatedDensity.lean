import SchwartzSeparatedProduct
import SchwartzCompactTranslation
import Mathlib.Analysis.Calculus.BumpFunction.Normed

open Filter Function MeasureTheory Set Topology
open scoped SchwartzMap

namespace Masullo

noncomputable section

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace V] [BorelSpace V]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ V] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace V] [BorelSpace V] in
private theorem translated_product (φ : 𝓢(E, ℂ)) (g : 𝓢(V, ℂ)) (a : E × V) :
    SchwartzMap.compSubConstCLM ℂ a (schwartzProductLeft φ g) =
      schwartzProductLeft (SchwartzMap.compSubConstCLM ℂ a.1 φ)
        (SchwartzMap.compSubConstCLM ℂ a.2 g) := by
  ext x
  rfl

private theorem schwartzFunctional_zero_compact_of_separated
    (μ : Measure E) [μ.IsAddHaarMeasure] (ν : Measure V) [ν.IsAddHaarMeasure]
    (T : StrongDual ℂ 𝓢(E × V, ℂ)) (hT : ∀ f g, T (schwartzProductLeft f g) = 0)
    (F : 𝓢(E × V, ℂ)) (hF : HasCompactSupport F) : T F = 0 := by
  by_contra hne
  let ε : ℝ := ‖T F‖ / 2
  have hε : 0 < ε := half_pos (norm_pos_iff.mpr hne)
  let t (a : E × V) := T (SchwartzMap.compSubConstCLM ℂ a F)
  have ht : Continuous t := T.continuous.comp
    (continuous_schwartz_compSubConst_of_hasCompactSupport F hF)
  obtain ⟨δ, hδ, hnear⟩ := Metric.continuousAt_iff.mp (ht.continuousAt (x := 0)) ε hε
  let b : ContDiffBump (0 : E) := ⟨δ / 2, δ, half_pos hδ, half_lt_self hδ⟩
  let d : ContDiffBump (0 : V) := ⟨δ / 2, δ, half_pos hδ, half_lt_self hδ⟩
  let f : 𝓢(E, ℂ) := (b.hasCompactSupport_normed (μ := μ)).comp_left Complex.ofReal_zero
    |>.toSchwartzMap (Complex.ofRealCLM.contDiff.comp b.contDiff_normed)
  let g : 𝓢(V, ℂ) := (d.hasCompactSupport_normed (μ := ν)).comp_left Complex.ofReal_zero
    |>.toSchwartzMap (Complex.ofRealCLM.contDiff.comp d.contDiff_normed)
  let ρ := schwartzProductLeft f g
  let p (x : E × V) := b.normed μ x.1 * d.normed ν x.2
  have hρeq (x : E × V) : ρ x = (p x : ℂ) := (Complex.ofReal_mul _ _).symm
  have hpc : HasCompactSupport p := by
    let K := tsupport (b.normed μ) ×ˢ tsupport (d.normed ν)
    have hK : IsCompact K := b.hasCompactSupport_normed.prod d.hasCompactSupport_normed
    apply hK.of_isClosed_subset (isClosed_tsupport p)
    apply closure_minimal _ ((isClosed_tsupport (b.normed μ)).prod (isClosed_tsupport (d.normed ν)))
    intro x hx
    obtain ⟨hx₁, hx₂⟩ := mul_ne_zero_iff.mp (show p x ≠ 0 from hx)
    exact ⟨subset_tsupport _ hx₁, subset_tsupport _ hx₂⟩
  have hρc : HasCompactSupport ρ := by
    have he : (ρ : E × V → ℂ) = fun x => (p x : ℂ) := funext hρeq
    rw [he]
    exact hpc.comp_left Complex.ofReal_zero
  have hp (x : E × V) : 0 ≤ p x := mul_nonneg (b.nonneg_normed _) (d.nonneg_normed _)
  have hpint : ∫ x, p x ∂μ.prod ν = 1 := by
    rw [integral_prod_mul (b.normed μ) (d.normed ν), b.integral_normed, d.integral_normed, mul_one]
  have hdist (x : E × V) (hx : p x ≠ 0) : dist x 0 < δ := by
    obtain ⟨hx₁, hx₂⟩ := mul_ne_zero_iff.mp hx
    have he : x.1 ∈ Metric.ball (0 : E) δ := by
      rw [show Metric.ball (0 : E) δ = support (b.normed μ) from b.support_normed_eq.symm]
      exact hx₁
    have hv : x.2 ∈ Metric.ball (0 : V) δ := by
      rw [show Metric.ball (0 : V) δ = support (d.normed ν) from d.support_normed_eq.symm]
      exact hx₂
    rw [Prod.dist_eq, max_lt_iff]
    exact ⟨he, hv⟩
  haveI : (μ.prod ν).IsNegInvariant := ⟨by
    change (μ.prod ν).map (Prod.map Neg.neg Neg.neg) = μ.prod ν
    rw [← Measure.map_prod_map _ _ measurable_neg measurable_neg, Measure.map_neg_eq_self, Measure.map_neg_eq_self]⟩
  obtain ⟨W, hW⟩ := exists_schwartz_compactConvolution (μ.prod ν) F ρ hF hρc
  have hW₀ : T W = 0 := by
    rw [(hW T).1]
    simp_rw [show ∀ x, SchwartzMap.compSubConstCLM ℂ x ρ =
      schwartzProductLeft (SchwartzMap.compSubConstCLM ℂ x.1 f)
        (SchwartzMap.compSubConstCLM ℂ x.2 g) from translated_product f g, hT, mul_zero]
    exact integral_zero _ _
  have hWt : ∫ x, p x • t x ∂μ.prod ν = 0 := by
    simpa only [t, hρeq, Complex.real_smul] using ((hW T).2.symm.trans hW₀)
  have hi : Integrable p (μ.prod ν) :=
    ((b.continuous_normed.comp continuous_fst).mul
      (d.continuous_normed.comp continuous_snd)).integrable_of_hasCompactSupport hpc
  have hit : Integrable (fun x => p x • t x) (μ.prod ν) :=
    (((b.continuous_normed.comp continuous_fst).mul
      (d.continuous_normed.comp continuous_snd)).smul ht).integrable_of_hasCompactSupport hpc.smul_right
  have he : (∫ x, p x • (T F - t x) ∂μ.prod ν) = T F := by
    simp_rw [smul_sub]
    rw [integral_sub (hi.smul_const _) hit, integral_smul_const, hpint, one_smul, hWt, sub_zero]
  have hn : ‖T F‖ ≤ ε := calc
    _ = ‖∫ x, p x • (T F - t x) ∂μ.prod ν‖ := congrArg norm he.symm
    _ ≤ ∫ x, p x * ε ∂μ.prod ν := by
      apply norm_integral_le_of_norm_le
      · exact hi.mul_const _
      · apply Eventually.of_forall
        intro x
        rw [norm_smul, Real.norm_of_nonneg (hp x)]
        by_cases hx : p x = 0
        · simp [hx]
        · apply mul_le_mul_of_nonneg_left _ (hp x)
          have hh := hnear (hdist x hx)
          rw [dist_eq_norm] at hh
          have ht0 : t 0 = T F := by simp [t]
          rw [ht0, norm_sub_rev] at hh
          exact hh.le
    _ = ε := by rw [integral_mul_const, hpint, one_mul]
  exact (half_lt_self (norm_pos_iff.mpr hne)).not_ge hn

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace V] [BorelSpace V] in
/-- A continuous Schwartz functional on a product is determined by its
values on separated tests. -/
theorem schwartzFunctional_eq_of_separated
    (T U : StrongDual ℂ 𝓢(E × V, ℂ))
    (he : ∀ f g, T (schwartzProductLeft f g) = U (schwartzProductLeft f g)) :
    T = U := by
  letI : MeasurableSpace E := borel E
  letI : BorelSpace E := ⟨rfl⟩
  letI : MeasurableSpace V := borel V
  letI : BorelSpace V := ⟨rfl⟩
  let μ := Measure.addHaar (G := E)
  let ν := Measure.addHaar (G := V)
  have hzero : ∀ f g, (T - U) (schwartzProductLeft f g) = 0 := fun f g => sub_eq_zero.mpr (he f g)
  ext F
  obtain ⟨G, hG, hlim⟩ := exists_schwartz_compactSupport_sequence F
  have h (n : ℕ) : T (G n) = U (G n) :=
    sub_eq_zero.mp (schwartzFunctional_zero_compact_of_separated μ ν (T - U) hzero (G n) (hG n))
  exact tendsto_nhds_unique (T.continuous.continuousAt.tendsto.comp hlim)
    ((U.continuous.continuousAt.tendsto.comp hlim).congr (fun n => (h n).symm))

end
end Masullo
