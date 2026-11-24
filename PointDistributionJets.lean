import CoordinatePlaneJetKernel
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

open Filter Function Set TopologicalSpace Topology
open scoped ContDiff Distributions

namespace Masullo

noncomputable section

private abbrev Tests := 𝓓((⊤ : Opens ℝ), ℂ)

private def monomialJetTest (n : ℕ) : Tests := by
  let b : ContDiffBump (0 : ℝ) := ⟨1 / 2, 1, by norm_num, by norm_num⟩
  let f : ℝ → ℂ := fun x ↦ (b x : ℂ) * ((x ^ n : ℝ) : ℂ)
  have h : tsupport f ⊆ Metric.closedBall 0 1 :=
    tsupport_mul_subset_left.trans
      ((tsupport_comp_subset Complex.ofReal_zero b).trans (by rw [b.tsupport_eq]))
  exact ⟨f, (Complex.ofRealCLM.contDiff.comp b.contDiff).mul
      (Complex.ofRealCLM.contDiff.comp (contDiff_id.pow n)),
    (isCompact_closedBall 0 1).of_isClosed_subset (isClosed_tsupport _) h, subset_univ _⟩

private theorem monomialJetTest_iteratedDeriv (n k : ℕ) :
    iteratedDeriv k (monomialJetTest n : ℝ → ℂ) 0 =
      if k = n then (n.factorial : ℂ) else 0 := by
  let b : ContDiffBump (0 : ℝ) := ⟨1 / 2, 1, by norm_num, by norm_num⟩
  have hloc : (monomialJetTest n : ℝ → ℂ) =ᶠ[𝓝 0]
      Complex.ofRealCLM ∘ (fun x : ℝ ↦ x ^ n) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (by norm_num : 0 < (1 / 2 : ℝ))]
      with x hx
    change (b x : ℂ) * ((x ^ n : ℝ) : ℂ) = ((x ^ n : ℝ) : ℂ)
    rw [b.one_of_mem_closedBall (Metric.ball_subset_closedBall hx), Complex.ofReal_one, one_mul]
  rw [hloc.iteratedDeriv_eq k]
  have h :
      iteratedDeriv k (Complex.ofRealCLM ∘ (fun x : ℝ ↦ x ^ n)) 0 =
        ((iteratedDeriv k (fun x : ℝ ↦ x ^ n) 0 : ℝ) : ℂ) := by
    simp only [iteratedDeriv_eq_iteratedFDeriv]
    have hd : ContDiffAt ℝ (k : ℕ∞ω) (fun x : ℝ ↦ x ^ n) 0 :=
      (contDiff_id.pow n).contDiffAt
    rw [Complex.ofRealCLM.iteratedFDeriv_comp_left hd le_rfl]
    rfl
  rw [h, iteratedDeriv_fun_pow_zero]
  split_ifs <;> simp

/-- There is a compactly supported smooth test for each individual
derivative coordinate at the origin. -/
theorem exists_smoothTest_single_jet (n : ℕ) :
    ∃ f : Tests, ∀ k, iteratedDeriv k (f : ℝ → ℂ) 0 = if k = n then 1 else 0 := by
  refine ⟨(n.factorial : ℂ)⁻¹ • monomialJetTest n, fun k ↦ ?_⟩
  have htop : (k : ℕ∞ω) ≤ ∞ := by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤)
  change iteratedDeriv k ((n.factorial : ℂ)⁻¹ • (monomialJetTest n : ℝ → ℂ)) 0 = _
  rw [iteratedDeriv_const_smul ((monomialJetTest n).contDiff.of_le htop).contDiffAt,
    monomialJetTest_iteratedDeriv]
  split_ifs
  · exact inv_mul_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero n)
  · exact smul_zero _

/-- On compactly supported tests, a distribution of order at most N
carried by the origin on the line is a linear combination of derivative
evaluations through order N. -/
theorem pointTestDistribution_eq_sum_derivative_eval
    (T : Tests →L[ℂ] ℂ) (N : ℕ) (hT : testDistributionOrderLE T N)
    (hvan : Distribution.IsVanishingOn (⇑T) ({0} : Set ℝ)ᶜ) :
    ∃ c : Fin (N + 1) → ℂ, ∀ f : Tests,
      T f = ∑ j : Fin (N + 1), c j * iteratedDeriv j.val (f : ℝ → ℂ) 0 := by
  classical
  refine ⟨fun j ↦ T (monomialJetTest j.val) / (j.val.factorial : ℂ), fun f ↦ ?_⟩
  let a (j : Fin (N+1)) : ℂ := iteratedDeriv j.val (f : ℝ → ℂ) 0 / (j.val.factorial : ℂ)
  let g : Tests := ∑ j : Fin (N + 1), a j • monomialJetTest j.val
  have hg (k : ℕ) (hk : k ≤ N) :
      iteratedDeriv k (g : ℝ → ℂ) 0 = iteratedDeriv k (f : ℝ → ℂ) 0 := by
    let k' : Fin (N+1) := ⟨k, by omega⟩
    have hgs : (g : ℝ → ℂ) = fun x ↦ ∑ j : Fin (N+1), a j • monomialJetTest j.val x := by
      change (FunLike.coeAddMonoidHom Tests ℝ ℂ) (∑ j : Fin (N+1), a j • monomialJetTest j.val) = _
      rw [map_sum]
      funext x
      simp [Finset.sum_apply]
    have htop : (k : ℕ∞ω) ≤ ∞ := by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤)
    rw [hgs, iteratedDeriv_fun_sum (fun j _ ↦
      (((monomialJetTest j.val).contDiff.of_le htop).const_smul (a j)).contDiffAt)]
    simp_rw [iteratedDeriv_fun_const_smul ((monomialJetTest _).contDiff.of_le htop).contDiffAt,
      monomialJetTest_iteratedDeriv]
    rw [Finset.sum_eq_single k']
    · change a k' * (if k = k then (k.factorial : ℂ) else 0) = _
      rw [ite_eq_left rfl]
      exact div_mul_cancel₀ _ (by exact_mod_cast Nat.factorial_ne_zero k)
    · intro j _ hj
      have hkj : k ≠ j.val := fun e ↦ hj (Fin.ext e.symm)
      simp [hkj]
    · simp
  have heq : T f = T g := by
    let p := ContinuousLinearMap.id ℝ ℝ
    have hplane : {y : ℝ | p y = 0} = {0} := by ext y; simp [p]
    apply coordinatePlane_distribution_eq_of_normal_jets p p (fun _ ↦ rfl)
      (ContinuousLinearMap.norm_id_le) (ContinuousLinearMap.norm_id_le) T N hT
      (hplane.symm ▸ hvan) f g
    intro y hy k hk m
    have hy0 : y = 0 := hy
    subst y
    rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod,
      iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, hg k hk]
  rw [heq]
  simp only [g, map_sum, map_smul, smul_eq_mul, a]
  apply Finset.sum_congr rfl
  intro j _
  ring

end
end Masullo
