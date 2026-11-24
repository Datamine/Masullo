import SchwartzBanachCoordinates
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

open Filter Function Set Topology UniformSpace
open scoped ContDiff SchwartzMap

namespace Masullo

noncomputable section

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]

private def smoothExhaustionBump (n : ℕ) : ContDiffBump (0 : X) :=
  ⟨(n : ℝ) + 1, (n : ℝ) + 2, by positivity, by linarith⟩

/-- A compact smooth cutoff equal to one on the closed ball of radius `n + 1`. -/
def smoothExhaustionCutoff (n : ℕ) (x : X) : ℂ :=
  Complex.ofReal ((smoothExhaustionBump (X := X) n : X → ℝ) x)

theorem smoothExhaustionCutoff_smooth (n : ℕ) :
    ContDiff ℝ ∞ (smoothExhaustionCutoff (X := X) n) :=
  Complex.ofRealCLM.contDiff.comp (smoothExhaustionBump (X := X) n).contDiff

theorem smoothExhaustionCutoff_compact (n : ℕ) :
    HasCompactSupport (smoothExhaustionCutoff (X := X) n) :=
  (smoothExhaustionBump (X := X) n).hasCompactSupport.comp_left (g := Complex.ofReal) Complex.ofReal_zero

theorem smoothExhaustionCutoff_eq_one (n : ℕ) (x : X) (h : ‖x‖ ≤ (n : ℝ) + 1) :
    smoothExhaustionCutoff n x = 1 := by
  have hh : x ∈ Metric.closedBall 0 (smoothExhaustionBump (X := X) n).rIn :=
    Metric.mem_closedBall.mpr (by rw [dist_zero_right]; exact h)
  simp only [smoothExhaustionCutoff, (smoothExhaustionBump (X := X) n).one_of_mem_closedBall hh,
    Complex.ofReal_one]

theorem smoothExhaustionCutoff_nonzero_eq_one {m n : ℕ} (hmn : m < n) (x : X)
    (hx : smoothExhaustionCutoff m x ≠ 0) : smoothExhaustionCutoff n x = 1 := by
  apply smoothExhaustionCutoff_eq_one
  have h : ‖x‖ < (m : ℝ) + 2 := by
    by_contra! he
    have hz : ((smoothExhaustionBump (X := X) m : X → ℝ) x) = 0 :=
      (smoothExhaustionBump (X := X) m).zero_of_le_dist (by
        rw [dist_zero_right]
        exact he)
    exact hx (by simp only [smoothExhaustionCutoff, hz, Complex.ofReal_zero])
  have hn : (m : ℝ) + 1 ≤ n := by exact_mod_cast (Nat.succ_le_of_lt hmn)
  linarith

/-- A compatible family of compactly localized smooth functions. -/
def smoothExhaustionSpace : Submodule ℂ (ℕ → 𝓢(X, ℂ)) where
  carrier := {f | ∀ m n, m < n → ∀ x, f m x = smoothExhaustionCutoff m x • f n x}
  zero_mem' := fun m n h x => by simp
  add_mem' := by
    intro f g hf hg m n h x
    change f m x + g m x = smoothExhaustionCutoff m x • (f n x + g n x)
    rw [hf m n h x, hg m n h x, smul_add]
  smul_mem' := fun c f hf m n h x => by
    change c • f m x = smoothExhaustionCutoff m x • (c • f n x)
    rw [hf m n h x, smul_comm]

/-- A jointly smooth function gives a compatible Schwartz family by localization. -/
def smoothExhaustionPack (f : X → ℂ) (hf : ContDiff ℝ ∞ f) :
    smoothExhaustionSpace (X := X) := by
  let F (n : ℕ) := ((smoothExhaustionCutoff_compact (X := X) n).smul_right (f' := f)).toSchwartzMap
    ((smoothExhaustionCutoff_smooth n).smul hf)
  refine ⟨F, fun m n h x => ?_⟩
  change smoothExhaustionCutoff m x • f x =
    smoothExhaustionCutoff m x • (smoothExhaustionCutoff n x • f x)
  by_cases hx : smoothExhaustionCutoff m x = 0
  · rw [hx, zero_smul, zero_smul]
  · rw [smoothExhaustionCutoff_nonzero_eq_one h x hx, one_smul]

/-- Any compatible family comes from a unique smooth function on the whole space. -/
theorem exists_smoothExhaustion_unlocalized
    (f : smoothExhaustionSpace (X := X)) :
    ∃! u : X → ℂ, ContDiff ℝ ∞ u ∧
      ∀ n x, f.val n x = smoothExhaustionCutoff n x • u x := by
  classical
  have hs (x : X) : ∃ n : ℕ, ‖x‖ < (n : ℝ) := exists_nat_gt ‖x‖
  let N (x : X) := (hs x).choose
  let u (x : X) := f.val (N x) x
  have hN (x : X) : smoothExhaustionCutoff (N x) x = 1 :=
    smoothExhaustionCutoff_eq_one _ _ (by linarith [(hs x).choose_spec])
  have hu (x : X) (n : ℕ) (hn : smoothExhaustionCutoff n x = 1) : u x = f.val n x := by
    let k := max n (N x) + 1
    have hnk : n < k := Nat.lt_succ_of_le (le_max_left _ _)
    have hNk : N x < k := Nat.lt_succ_of_le (le_max_right _ _)
    have e₁ := f.property (N x) k hNk x
    have e₂ := f.property n k hnk x
    rw [hN, one_smul] at e₁
    rw [hn, one_smul] at e₂
    exact e₁.trans e₂.symm
  have hloc (m : ℕ) (x : X) : f.val m x = smoothExhaustionCutoff m x • u x := by
    let k := max m (N x) + 1
    have hmk : m < k := Nat.lt_succ_of_le (le_max_left _ _)
    have hNk : N x < k := Nat.lt_succ_of_le (le_max_right _ _)
    have h := f.property (N x) k hNk x
    rw [hN, one_smul] at h
    exact (f.property m k hmk x).trans (congrArg (smoothExhaustionCutoff m x • ·) h.symm)
  refine ⟨u, ⟨?_, hloc⟩, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    let n := N x
    have hb : x ∈ Metric.ball 0 ((n : ℝ) + 1) :=
      Metric.mem_ball.mpr (by simpa only [dist_zero_right] using
        (show ‖x‖ < (n : ℝ) + 1 from by linarith [(hs x).choose_spec]))
    apply ((f.val n).smooth').contDiffAt.congr_of_eventuallyEq
    filter_upwards [Metric.isOpen_ball.mem_nhds hb] with y hy
    exact hu y n (smoothExhaustionCutoff_eq_one n y (by
      have h := Metric.mem_ball.mp hy
      simpa only [dist_zero_right] using h.le))
  · intro v hv
    funext x
    have h := hv.2 (N x) x
    rw [hN, one_smul] at h
    exact h.symm


/-- The localization compatibility is closed in the product of the Schwartz spaces. -/
theorem isClosed_smoothExhaustionSpace :
    IsClosed (smoothExhaustionSpace (X := X) : Set (ℕ → 𝓢(X, ℂ))) := by
  let A := ℕ → 𝓢(X, ℂ)
  have he : (smoothExhaustionSpace (X := X) : Set A) =
      ⋂ m : ℕ, ⋂ n : ℕ, ⋂ _ : m < n, ⋂ x : X,
        {f : A | f m x = smoothExhaustionCutoff m x * f n x} := by
    ext f
    change (∀ m n, m < n → ∀ x, f m x = smoothExhaustionCutoff m x • f n x) ↔ _
    simp only [mem_iInter, mem_ofPred_eq, smul_eq_mul]
  rw [he]
  refine isClosed_iInter fun m => isClosed_iInter fun n =>
    isClosed_iInter fun _ => isClosed_iInter fun x => ?_
  have heval : Continuous (fun g : 𝓢(X, ℂ) => g x) :=
    ((BoundedContinuousFunction.evalCLM ℂ x).comp
      (SchwartzMap.toBoundedContinuousFunctionCLM ℂ X ℂ)).continuous
  have h (n : ℕ) : Continuous (fun f : A => f n x) := heval.comp (continuous_apply n)
  have h' : Continuous (fun f : A => smoothExhaustionCutoff m x * f n x) :=
    continuous_const.mul (h n)
  exact isClosed_eq (h m) h'

/-- The compact cutoff model for smooth functions is Fréchet. -/
theorem smoothExhaustionSpace_frechet : IsFrechetTVS (smoothExhaustionSpace (X := X)) := by
  let A := ℕ → 𝓢(X, ℂ)
  letI : CompleteSpace 𝓢(X, ℂ) := completeSpace_schwartzMap
  letI : (uniformity 𝓢(X, ℂ)).IsCountablyGenerated :=
    IsUniformAddGroup.uniformity_countably_generated
  letI : (uniformity A).IsCountablyGenerated :=
    inferInstanceAs ((uniformity (ℕ → 𝓢(X, ℂ))).IsCountablyGenerated)
  have hA : IsFrechetTVS A := by
    refine ⟨inferInstance, (withSeminorms_pi (fun _ : ℕ => schwartz_withSeminorms ℂ X ℂ)).toPolynormableSpace,
      UniformSpace.metrizableSpace, ?_⟩
    rw [IsUniformAddGroup.rightUniformSpace_eq]
    infer_instance
  exact isFrechetTVS_closedSubmodule hA _ isClosed_smoothExhaustionSpace


/-- On any compact ball strictly inside the cutoff, the localized seminorm
controls the derivative of the original smooth function. -/
theorem smoothExhaustion_derivative_le (f : X → ℂ) (hf : ContDiff ℝ ∞ f)
    (m n : ℕ) (x : X) (hx : ‖x‖ < (m : ℝ) + 1) :
    ‖iteratedFDeriv ℝ n f x‖ ≤
      SchwartzMap.seminorm ℂ 0 n ((smoothExhaustionPack f hf).val m) := by
  let g := (smoothExhaustionPack f hf).val m
  have hb : x ∈ Metric.ball 0 ((m : ℝ)+1) :=
    Metric.mem_ball.mpr (by rwa [dist_zero_right])
  have h : (g : X → ℂ) =ᶠ[𝓝 x] f := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hb] with y hy
    change smoothExhaustionCutoff m y • f y = f y
    have h' : ‖y‖ ≤ (m : ℝ)+1 :=
      by simpa only [dist_zero_right] using (Metric.mem_ball.mp hy).le
    rw [smoothExhaustionCutoff_eq_one m y h', one_smul]
  rw [← (h.iteratedFDeriv ℝ n).eq_of_nhds]
  exact SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ g n x

/-- Each cutoff seminorm is controlled by finitely many derivative bounds
on the compact ball containing the support of that cutoff. -/
theorem smoothExhaustion_seminorm_le (f : X → ℂ) (hf : ContDiff ℝ ∞ f)
    (m k n : ℕ) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ i ≤ n, ∀ x, ‖x‖ ≤ (m : ℝ)+2 → ‖iteratedFDeriv ℝ i f x‖ ≤ M) :
    SchwartzMap.seminorm ℂ k n ((smoothExhaustionPack f hf).val m) ≤
        (∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) * SchwartzMap.seminorm ℂ k i
          ((smoothExhaustionCutoff_compact (X := X) m).toSchwartzMap (smoothExhaustionCutoff_smooth m))) * M := by
  let w := smoothExhaustionCutoff (X := X) m
  let W := (smoothExhaustionCutoff_compact (X := X) m).toSchwartzMap (smoothExhaustionCutoff_smooth m)
  let g := (smoothExhaustionPack f hf).val m
  apply SchwartzMap.seminorm_le_bound ℂ k n g
    (mul_nonneg (Finset.sum_nonneg (fun _ _ => by positivity)) hM)
  intro x
  by_cases hx : ‖x‖ ≤ (m : ℝ)+2
  · change ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun y => w y • f y) x‖ ≤ _
    calc
      _ ≤ ‖x‖ ^ k * (∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i w x‖ * ‖iteratedFDeriv ℝ (n-i) f x‖) :=
        mul_le_mul_of_nonneg_left
          (norm_iteratedFDeriv_smul_le (smoothExhaustionCutoff_smooth m) hf x
            (WithTop.coe_le_coe.mpr le_top)) (by positivity)
      _ = ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) *
          (‖x‖ ^ k * ‖iteratedFDeriv ℝ i w x‖) * ‖iteratedFDeriv ℝ (n-i) f x‖ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ ≤ _ := by
        rw [Finset.sum_mul]
        apply Finset.sum_le_sum
        intro i _
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left (SchwartzMap.le_seminorm ℂ k i W x) (by positivity)
        · exact hbound _ (Nat.sub_le n i) x hx
        · positivity
        · positivity
  · have he : (g : X → ℂ) =ᶠ[𝓝 x] (fun _ => 0) := by
      let S := {y : X | (m : ℝ)+2 < ‖y‖}
      have hS : IsOpen S := isOpen_lt continuous_const continuous_norm
      filter_upwards [hS.mem_nhds (show x ∈ S from lt_of_not_ge hx)] with y hy
      change w y • f y = 0
      have hz : ((smoothExhaustionBump (X := X) m : X → ℝ) y) = 0 :=
        (smoothExhaustionBump (X := X) m).zero_of_le_dist (by
          rw [dist_zero_right]
          exact (show (m : ℝ)+2 < ‖y‖ from hy).le)
      simp [w, smoothExhaustionCutoff, hz]
    rw [(he.iteratedFDeriv ℝ n).eq_of_nhds]
    simp only [iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero, mul_zero]
    positivity

/-- Point evaluation is continuous in the compact-open derivative topology. -/
def smoothExhaustionEval (x : X) : smoothExhaustionSpace (X := X) →L[ℂ] ℂ := by
  let n := (exists_nat_gt ‖x‖).choose
  exact ((BoundedContinuousFunction.evalCLM ℂ x).comp
    (SchwartzMap.toBoundedContinuousFunctionCLM ℂ X ℂ)).comp
    ((ContinuousLinearMap.proj n).comp (smoothExhaustionSpace (X := X)).subtypeL)

theorem smoothExhaustionEval_eq_of_localizations
    (f : smoothExhaustionSpace (X := X)) (u : X → ℂ)
    (hu : ∀ n x, f.val n x = smoothExhaustionCutoff n x • u x) (x : X) :
    smoothExhaustionEval x f = u x := by
  let n := (exists_nat_gt ‖x‖).choose
  change f.val n x = u x
  rw [hu, smoothExhaustionCutoff_eq_one, one_smul]
  linarith [(exists_nat_gt ‖x‖).choose_spec]

theorem smoothExhaustionEval_contDiff (f : smoothExhaustionSpace (X := X)) :
    ContDiff ℝ ∞ (fun x => smoothExhaustionEval x f) := by
  obtain ⟨u, hu, -⟩ := exists_smoothExhaustion_unlocalized f
  exact (funext (smoothExhaustionEval_eq_of_localizations f u hu.2)).symm ▸ hu.1

theorem smoothExhaustion_localization_eval
    (f : smoothExhaustionSpace (X := X)) (n : ℕ) (x : X) :
    f.val n x = smoothExhaustionCutoff n x • smoothExhaustionEval x f := by
  obtain ⟨u, hu, -⟩ := exists_smoothExhaustion_unlocalized f
  rw [smoothExhaustionEval_eq_of_localizations f u hu.2]
  exact hu.2 n x

@[simp] theorem smoothExhaustionEval_pack (u : X → ℂ) (hu : ContDiff ℝ ∞ u) (x : X) :
    smoothExhaustionEval x (smoothExhaustionPack u hu) = u x :=
  smoothExhaustionEval_eq_of_localizations _ u (fun _ _ => rfl) x

end
end Masullo
