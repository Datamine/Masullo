import CutoffConvolutionTrace

open Filter Function MeasureTheory Set Topology
open scoped ENNReal NNReal InnerProductSpace

namespace Masullo

noncomputable section

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν]

/-- Transposition with conjugation represents the Hilbert-space adjoint
of a square-integrable kernel. -/
theorem kernelIntegralOperator_adjoint_of_memLp {k : X × Y → ℂ}
    (hk : MemLp k 2 (μ.prod ν))
    (ht : MemLp (fun p : Y × X => star (k (p.2, p.1))) 2 (ν.prod μ)) :
    kernelIntegralOperator (ht.toLp _) = (kernelIntegralOperator (hk.toLp k)).adjoint := by
  ext f : 1
  apply ext_inner_right ℂ
  intro g
  rw [ContinuousLinearMap.adjoint_inner_left, L2.inner_def, L2.inner_def]
  let F (p : X × Y) := star (f p.1) * k p * g p.2
  have hF : Integrable F (μ.prod ν) := by
    have hp := (memLp_rankOneKernel (Lp.memLp f).star (Lp.memLp g).star).1
    refine (hp.integrable_mul hk).congr (.of_forall fun p => ?_)
    change (star (f p.1) * star (star (g p.2))) * k p = F p
    rw [star_star]
    unfold F
    ring
  calc
    _ = ∫ y, ∫ x, F (x, y) ∂μ ∂ν := by
      apply integral_congr_ae
      filter_upwards [kernelIntegralOperator_apply_of_memLp ht f] with y hy
      rw [hy.2, RCLike.inner_apply, ← integral_conj, ← integral_const_mul]
      apply integral_congr_ae
      refine .of_forall fun x => ?_
      change g y * star (star (k (x, y)) * f x) = F (x, y)
      rw [star_mul, star_star]
      unfold F
      ring
    _ = ∫ p, F p ∂μ.prod ν := (integral_prod_symm F hF).symm
    _ = _ := by
      rw [integral_prod F hF]
      apply integral_congr_ae
      filter_upwards [kernelIntegralOperator_apply_of_memLp hk g] with x hx
      rw [RCLike.inner_apply, hx.2, ← integral_mul_const]
      apply integral_congr_ae
      exact .of_forall fun y => by unfold F; rw [starRingEnd_apply]; ring

/-- A represented composite of two square-integrable kernels is the
product of the corresponding operators. -/
theorem kernelIntegralOperator_comp_of_memLp {a b c : Type*}
    [MeasurableSpace a] [MeasurableSpace b] [MeasurableSpace c]
    {α : Measure a} {β : Measure b} {γ : Measure c} [SFinite β] [SFinite γ]
    {k : a × b → ℂ} {j : b × c → ℂ} {h : a × c → ℂ}
    (hk : MemLp k 2 (α.prod β)) (hj : MemLp j 2 (β.prod γ)) (hh : MemLp h 2 (α.prod γ))
    (he : ∀ᵐ p ∂α.prod γ, h p = ∫ y, k (p.1, y) * j (y, p.2) ∂β) :
    kernelIntegralOperator (hh.toLp h) =
      (kernelIntegralOperator (hk.toLp k)).comp (kernelIntegralOperator (hj.toLp j)) := by
  ext f : 1
  apply Lp.ext
  filter_upwards [kernelIntegralOperator_apply_of_memLp hh f,
    kernelIntegralOperator_apply_of_memLp hk (kernelIntegralOperator (hj.toLp j) f),
    memLp_kernelRows hk, Measure.ae_ae_of_ae_prod he] with x hx hy hrow hz
  rw [ContinuousLinearMap.comp_apply, hx.2, hy.2]
  let F (p : b × c) := k (x, p.1) * j p * f p.2
  have hF : Integrable F (β.prod γ) := by
    have hp := (memLp_rankOneKernel hrow (Lp.memLp f).star).1
    refine (hp.integrable_mul hj).congr (.of_forall fun p => ?_)
    change (k (x, p.1) * star (star (f p.2))) * j p = F p
    rw [star_star]
    unfold F
    ring
  calc
    _ = ∫ z, ∫ y, F (y, z) ∂β ∂γ := by
      apply integral_congr_ae
      filter_upwards [hz] with z hz
      rw [hz, ← integral_mul_const]
    _ = ∫ p, F p ∂β.prod γ := (integral_prod_symm F hF).symm
    _ = _ := by
      rw [integral_prod F hF]
      apply integral_congr_ae
      filter_upwards [kernelIntegralOperator_apply_of_memLp hj f] with y hy
      rw [hy.2, ← integral_const_mul]
      apply integral_congr_ae
      exact .of_forall fun z => by simp [F, mul_assoc]

/-- A countable nuclear series can be indexed by natural numbers, including
when the original Hilbert basis is finite. -/
theorem RankOneSeries.exists_nat_index {H ι : Type*} [Countable ι]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (T : RankOneSeries ι H) :
    ∃ S : RankOneSeries ℕ H, S.operator = T.operator := by
  classical
  obtain ⟨e, he⟩ := exists_injective_nat ι
  let u := Function.extend e T.image (0 : ℕ → H)
  let v := Function.extend e T.functional (0 : ℕ → H)
  have hsum : (fun n => ‖u n‖ * ‖v n‖) =
      Function.extend e (fun i => ‖T.image i‖ * ‖T.functional i‖) 0 := by
    funext n
    by_cases hn : ∃ i, e i = n
    · obtain ⟨i, rfl⟩ := hn
      simp only [u, v, he.extend_apply]
    · simp [u, v, Function.extend_apply', hn]
  let S : RankOneSeries ℕ H := ⟨u, v, by
    rw [hsum]
    exact ((hasSum_extend_zero he).mpr T.summableNorm.hasSum).summable⟩
  refine ⟨S, ?_⟩
  have hr : (fun n => InnerProductSpace.rankOne ℂ (u n) (v n)) =
      Function.extend e (fun i => InnerProductSpace.rankOne ℂ (T.image i) (T.functional i)) 0 := by
    funext n
    by_cases hn : ∃ i, e i = n
    · obtain ⟨i, rfl⟩ := hn
      simp only [u, v, he.extend_apply]
    · simp [u, v, Function.extend_apply', hn]
  change (∑' n, InnerProductSpace.rankOne ℂ (u n) (v n)) = T.operator
  rw [hr]
  exact ((hasSum_extend_zero he).mpr T.operator_summable.hasSum).tsum_eq

omit [SFinite μ] in
private theorem kernelIntegralOperator_has_basisEnergy {ι : Type*} [Countable ι]
    (b : HilbertBasis ι ℂ (Lp ℂ 2 ν)) (k : Lp ℂ 2 (μ.prod ν)) :
    Summable (fun i => ‖kernelIntegralOperator k (b i)‖ ^ 2) := by
  let F (i : ι) : ℝ≥0 := ‖kernelIntegralOperator k (b i)‖₊ ^ 2
  have hF : (∑' i, (F i : ℝ≥0∞)) ≠ ∞ := by
    simpa only [F, ENNReal.coe_pow, enorm, ENNReal.rpow_two] using
      ((kernelIntegralOperator_hilbertSchmidt_sq b k).trans_ne
        (ENNReal.rpow_ne_top_of_nonneg (by norm_num) enorm_ne_top))
  simpa only [F, NNReal.coe_pow, coe_nnnorm] using ENNReal.tsum_coe_ne_top_iff_summable_coe.mp hF

/-- The composite of two Hilbert–Schmidt kernels on separable weighted
L² spaces admits a countable nuclear representation. -/
theorem exists_kernelComposite_rankOneSeries [MeasureTheory.IsSeparable ν]
    {h : X × X → ℂ} {k : X × Y → ℂ} {j : Y × X → ℂ}
    (hh : MemLp h 2 (μ.prod μ)) (hk : MemLp k 2 (μ.prod ν)) (hj : MemLp j 2 (ν.prod μ))
    (he : ∀ᵐ p ∂μ.prod μ, h p = ∫ y, k (p.1, y) * j (y, p.2) ∂ν) :
    ∃ T : RankOneSeries ℕ (Lp ℂ 2 μ), T.operator = kernelIntegralOperator (hh.toLp h) := by
  obtain ⟨I, hI, ⟨b⟩⟩ := exists_countable_hilbertBasis_L2 (ν := ν)
  letI : Countable I := hI.to_subtype
  let t (p : X × Y) := star (j (p.2, p.1))
  have ht : MemLp t 2 (μ.prod ν) := hj.star.comp_measurePreserving Measure.measurePreserving_swap
  have hAdj : kernelIntegralOperator (ht.toLp t) = (kernelIntegralOperator (hj.toLp j)).adjoint :=
    kernelIntegralOperator_adjoint_of_memLp hj ht
  obtain ⟨T, hT⟩ := exists_cutoffTraceSeries_of_hilbertSchmidt_factors b
    (kernelIntegralOperator (hk.toLp k)) (kernelIntegralOperator (hj.toLp j))
    (kernelIntegralOperator_has_basisEnergy b (hk.toLp k))
    (by rw [← hAdj]; exact kernelIntegralOperator_has_basisEnergy b (ht.toLp t))
  obtain ⟨S, hS⟩ := T.exists_nat_index
  exact ⟨S, hS.trans (hT.trans (kernelIntegralOperator_comp_of_memLp hk hj hh he).symm)⟩

end
end Masullo
