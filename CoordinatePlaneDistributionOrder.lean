import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.Analysis.Distribution.Support
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Sym.NatCard

open Filter Function Set TopologicalSpace Topology
open scoped ContDiff Distributions

namespace Masullo

noncomputable section

private abbrev Tests (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  𝓓((⊤ : Opens E), ℂ)

/-- The order bound for a distribution, expressed on each compact support
stage using the derivatives through the specified order. -/
def testDistributionOrderLE {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : Tests E →L[ℂ] ℂ) (n : ℕ) : Prop :=
  ∀ K : Compacts E, ∃ C ≥ (0 : ℝ), ∀ f : Tests E, tsupport f ⊆ (K : Set E) →
    ∀ B ≥ (0 : ℝ), (∀ j ≤ n, ∀ x, ‖iteratedFDeriv ℝ j (f : E → ℂ) x‖ ≤ B) →
    ‖T f‖ ≤ C * B

private theorem testDistributionOrderLE_of_subsingleton
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Subsingleton E]
    (T : Tests E →L[ℂ] ℂ) : testDistributionOrderLE T 0 := by
  intro K
  let g : Tests E := ⟨fun _ ↦ 1, contDiff_const, (Set.toFinite _).isCompact, subset_univ _⟩
  refine ⟨‖T g‖, norm_nonneg _, fun f _ B _ hB ↦ ?_⟩
  have hf : f = f 0 • g := TestFunction.ext fun x ↦ by
    rw [Subsingleton.elim x 0]
    exact (mul_one _).symm
  have h := hB 0 le_rfl 0
  rw [norm_iteratedFDeriv_zero] at h
  rw [hf, map_smul, smul_eq_mul, norm_mul, mul_comm]
  exact mul_le_mul_of_nonneg_left h (norm_nonneg _)

private def derivativeAtZero : Tests ℝ →L[ℂ] ℂ :=
  (BoundedContinuousFunction.evalCLM ℂ 0).comp
    ((TestFunction.toBoundedContinuousFunctionCLM ℂ).comp
      (TestFunction.lineDerivCLM ℂ 1 : Tests ℝ →L[ℂ] Tests ℝ))

private theorem derivativeAtZero_apply (f : Tests ℝ) :
    derivativeAtZero f = fderiv ℝ (f : ℝ → ℂ) 0 1 := by
  change (TestFunction.lineDerivCLM ℂ 1 f : Tests ℝ) 0 = _
  rw [TestFunction.lineDerivCLM_eq_fderivCLM, TestFunction.fderivCLM_apply, ite_eq_left le_top]

private theorem derivativeAtZero_exactOrder :
    testDistributionOrderLE derivativeAtZero 1 ∧ ¬ testDistributionOrderLE derivativeAtZero 0 := by
  constructor
  · intro K
    refine ⟨1, zero_le_one, fun f _ B _ hB ↦ ?_⟩
    have h := hB 1 le_rfl 0
    rw [norm_iteratedFDeriv_one] at h
    rw [derivativeAtZero_apply, one_mul]
    exact (ContinuousLinearMap.le_opNorm _ _).trans (by simpa using h)
  · intro h
    obtain ⟨C, hC, hbound⟩ := h ⟨Metric.closedBall 0 1, isCompact_closedBall 0 1⟩
    let r : ℝ := 1 / (C + 1)
    have hr : 0 < r := by positivity
    have hr₁ : r ≤ 1 := by
      dsimp [r]
      rw [div_le_one (by positivity)]
      linarith
    let b : ContDiffBump (0 : ℝ) := ⟨r / 2, r, half_pos hr, by linarith⟩
    let f₀ : ℝ → ℂ := fun x ↦ (b x : ℂ) * (x : ℂ)
    have hc : ContDiff ℝ ∞ f₀ :=
      (Complex.ofRealCLM.contDiff.comp b.contDiff).mul Complex.ofRealCLM.contDiff
    have hs : tsupport f₀ ⊆ Metric.closedBall 0 r := by
      refine tsupport_mul_subset_left.trans ((tsupport_comp_subset Complex.ofReal_zero _).trans ?_)
      rw [b.tsupport_eq]
    let f : Tests ℝ := ⟨f₀, hc, (isCompact_closedBall 0 r).of_isClosed_subset
      (isClosed_tsupport _) hs, subset_univ _⟩
    have hloc : (f : ℝ → ℂ) =ᶠ[𝓝 0] Complex.ofRealCLM := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (half_pos hr)] with x hx
      change (b x : ℂ) * (x : ℂ) = x
      rw [b.one_of_mem_closedBall (Metric.ball_subset_closedBall hx), Complex.ofReal_one, one_mul]
    have ht : derivativeAtZero f = 1 := by
      rw [derivativeAtZero_apply, hloc.fderiv_eq, Complex.ofRealCLM.fderiv]
      rfl
    have hf (x : ℝ) : ‖f x‖ ≤ r := by
      change ‖(b x : ℂ) * (x : ℂ)‖ ≤ r
      rw [norm_mul, Complex.norm_real, Complex.norm_real]
      by_cases hx : x ∈ Metric.ball (0 : ℝ) r
      · have hb : ‖b x‖ ≤ 1 := by
          rw [Real.norm_eq_abs, abs_of_nonneg b.nonneg]
          exact b.le_one
        have hx' : ‖x‖ ≤ r := (by simpa only [Metric.mem_ball, dist_zero_right] using hx : ‖x‖ < r).le
        simpa only [one_mul] using mul_le_mul hb hx' (norm_nonneg x) zero_le_one
      · have hb : b x = 0 := by
          rw [← Function.notMem_support, b.support_eq]
          exact hx
        simp [hb, hr.le]
    have hfinal := hbound f (hs.trans (Metric.closedBall_subset_closedBall hr₁)) r hr.le
      (by
        intro j hj x
        obtain rfl : j = 0 := Nat.eq_zero_of_le_zero hj
        rw [norm_iteratedFDeriv_zero]
        exact hf x)
    rw [ht, norm_one] at hfinal
    have hsmall : C * r < 1 := by
      dsimp [r]
      rw [mul_one_div, div_lt_one (by positivity)]
      linarith
    exact hsmall.not_ge hfinal

/-- The order-one distribution differentiating at the origin is supported
at that point, but no zero-index coefficient on the point can have exact
order one as demanded by Theorem 5.3.2.3(2). -/
theorem exactCoordinatePlaneCoefficientOrder_counterexample :
    ∃ T : Tests ℝ →L[ℂ] ℂ, testDistributionOrderLE T 1 ∧
      ¬ testDistributionOrderLE T 0 ∧ Distribution.dsupport (⇑T) ⊆ {0} ∧
      ¬ ∃ A : Tests (Fin 0 → ℝ) →L[ℂ] ℂ,
        testDistributionOrderLE A 1 ∧ ¬ testDistributionOrderLE A 0 := by
  refine ⟨derivativeAtZero, derivativeAtZero_exactOrder.1, derivativeAtZero_exactOrder.2, ?_, ?_⟩
  · intro x hx
    by_contra hx₀
    refine (Distribution.notMem_dsupport_iff x).2
      ⟨{0}ᶜ, fun f hf ↦ ?_, isOpen_compl_singleton, hx₀⟩ hx
    have hz : (f : ℝ → ℂ) =ᶠ[𝓝 0] 0 :=
      notMem_tsupport_iff_eventuallyEq.1 (fun h ↦ hf h rfl)
    rw [derivativeAtZero_apply, hz.fderiv_eq, fderiv_zero]
    rfl
  · rintro ⟨A, _, hA⟩
    letI : Subsingleton (Fin 0 → ℝ) := ⟨fun f g ↦ funext fun i ↦ Fin.elim0 i⟩
    exact hA (testDistributionOrderLE_of_subsingleton A)

/-- The multi-indices in (5.3.2.4) have total degree at most `N`.
The unused degree is the multiplicity of one extra symbol. -/
theorem coordinatePlaneJetIndex_card {ι : Type*} [Fintype ι] (N : ℕ) :
    Nat.card {a : ι → Fin (N + 1) // ∑ i, (a i : ℕ) ≤ N} =
      (Fintype.card ι + N).choose (Fintype.card ι) := by
  classical
  let J := {b : Option ι → ℕ // ∑ i, b i = N}
  let I := {a : ι → Fin (N + 1) // ∑ i, (a i : ℕ) ≤ N}
  have hsum (b : J) : b.val none + (∑ i : ι, b.val (some i)) = N := by
    have h := b.property
    rwa [Fintype.sum_option] at h
  let e : I ≃ J :=
    { toFun := fun a => ⟨fun j => j.elim (N - ∑ i, (a.val i : ℕ)) (fun i => (a.val i : ℕ)),
        by
          rw [Fintype.sum_option]
          exact Nat.sub_add_cancel a.property⟩
      invFun := fun b => ⟨fun i => ⟨b.val (some i), by
        have h := Finset.single_le_sum (f := fun j : ι => b.val (some j))
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
        have hb := hsum b
        omega⟩, by
          have hb := hsum b
          change (∑ i : ι, b.val (some i)) ≤ N
          omega⟩
      left_inv := fun a => Subtype.ext (funext fun i => Fin.ext rfl)
      right_inv := fun b => Subtype.ext (funext fun i => by
        cases i with
        | none =>
          change N - (∑ j : ι, b.val (some j)) = b.val none
          have hb := hsum b
          omega
        | some i => rfl) }
  calc
    Nat.card I = Nat.card (Sym (Option ι) N) :=
      Nat.card_congr (e.trans (Sym.equivNatSumOfFintype (Option ι) N).symm)
    _ = (Fintype.card ι + N).choose (Fintype.card ι) := by
      rw [Sym.natCard_sym_eq_choose, Nat.card_eq_fintype_card, Fintype.card_option,
        show Fintype.card ι + 1 + N - 1 = Fintype.card ι + N by omega,
        Nat.choose_symm_add]

end
end Masullo
