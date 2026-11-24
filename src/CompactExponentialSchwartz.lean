import PeriodicSmoothTopology
import Mathlib.Analysis.Distribution.ContDiffMapSupportedIn
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

open Function Set Topology TopologicalSpace
open scoped ContDiff SchwartzMap Distributions

namespace Masullo

noncomputable section

/-- The exponential Schwartz space on the positive ray, in its logarithmic
coordinate. Each coordinate carries the standard Schwartz topology. -/
def expSchwartzGraph : Submodule ℂ (ℝ → 𝓢(ℝ, ℂ)) where
  carrier := { f | ∀ s x : ℝ, f s x = (Real.exp (s * x) : ℂ) * f 0 x }
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg s x
    change f s x + g s x = _ * (f 0 x + g 0 x)
    rw [hf s x, hg s x, mul_add]
  smul_mem' := by
    intro c f hf s x
    change c * f s x = _ * (c * f 0 x)
    rw [hf s x]
    ring

abbrev ExpSchwartz := ↥expSchwartzGraph

def expSchwartzEvaluation (s : ℝ) : ExpSchwartz →L[ℂ] 𝓢(ℝ, ℂ) where
  toFun f := (f : ℝ → 𝓢(ℝ, ℂ)) s
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := (continuous_apply s).comp continuous_subtype_val

def ExpSchwartzFixed (K : Set ℝ) : Submodule ℂ ExpSchwartz :=
  (fixedSupportSchwartz K).comap (expSchwartzEvaluation 0).toLinearMap

private theorem continuous_schwartz_eval (x : ℝ) :
    Continuous (fun f : 𝓢(ℝ, ℂ) => f x) :=
  ((BoundedContinuousFunction.lipschitz_eval_const x).continuous).comp
    (SchwartzMap.toBoundedContinuousFunctionCLM ℂ ℝ ℂ).continuous

/-- The specified fixed-support subspace is closed in the full exponential
Schwartz space. -/
theorem isClosed_expSchwartzFixed (K : Set ℝ) :
    IsClosed (ExpSchwartzFixed K : Set ExpSchwartz) := by
  have heq : (ExpSchwartzFixed K : Set ExpSchwartz) =
      ⋂ x : ↥(Kᶜ), {f : ExpSchwartz | expSchwartzEvaluation 0 f x = 0} := by
    ext f
    change (support (expSchwartzEvaluation 0 f) ⊆ K) ↔ _
    simp only [mem_iInter, mem_ofPred_eq]
    constructor
    · intro h x
      by_contra hh
      exact x.property (h hh)
    · intro h x hx
      by_contra hh
      exact hx (h ⟨x, hh⟩)
  rw [heq]
  exact isClosed_iInter fun x =>
    isClosed_eq ((continuous_schwartz_eval x).comp (expSchwartzEvaluation 0).continuous)
      continuous_const

private theorem exists_expMultiplier (K : Set ℝ) (hK : IsCompact K) (s : ℝ) :
    ∃ g : 𝓢(ℝ, ℂ), ∀ x ∈ K, g x = (Real.exp (s * x) : ℂ) := by
  obtain ⟨M, hM⟩ := (hK.bddAbove_image (continuous_norm.continuousOn)).exists_ge 1
  let b : ContDiffBump (0 : ℝ) := ⟨M, M + 1, zero_lt_one.trans_le hM.1, by linarith⟩
  let g (x : ℝ) : ℂ := (b x * Real.exp (s * x) : ℝ)
  have hgC : ContDiff ℝ ∞ g := Complex.ofRealCLM.contDiff.comp
    (b.contDiff.mul (Real.contDiff_exp.comp (by fun_prop)))
  have hg : HasCompactSupport g :=
    HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) (M + 1)) fun x hx => by
      have hbz : b x = 0 := by
        by_contra hh
        have he : x ∈ Metric.ball (0 : ℝ) b.rOut := by
          rw [← b.support_eq]
          exact hh
        exact hx (Metric.ball_subset_closedBall he)
      simp [g, hbz]
  refine ⟨hg.toSchwartzMap hgC, fun x hx => ?_⟩
  change g x = _
  have hmem : ‖x‖ ∈ (fun y : ℝ => ‖y‖) '' K := ⟨x, hx, rfl⟩
  have hx' : ‖x‖ ≤ M := hM.2 _ hmem
  have hb : b x = 1 := b.one_of_mem_closedBall (by simpa [Metric.mem_closedBall, dist_zero_right])
  simp [g, hb]

def fixedExpSchwartzCoordinate {K : Set ℝ} (hK : IsCompact K) (s : ℝ) :
    LogFixedTest K →L[ℂ] 𝓢(ℝ, ℂ) :=
  (SchwartzMap.smulLeftCLM ℂ ((exists_expMultiplier K hK s).choose : ℝ → ℂ)).comp
    (fixedSupportSchwartz K).subtypeL

theorem fixedExpSchwartzCoordinate_apply {K : Set ℝ} (hK : IsCompact K) (s : ℝ)
    (f : LogFixedTest K) (x : ℝ) :
    fixedExpSchwartzCoordinate hK s f x = (Real.exp (s * x) : ℂ) * (f : 𝓢(ℝ, ℂ)) x := by
  let g := (exists_expMultiplier K hK s).choose
  change (SchwartzMap.smulLeftCLM ℂ g (f : 𝓢(ℝ, ℂ))) x = _
  rw [SchwartzMap.smulLeftCLM_apply_apply g.hasTemperateGrowth, smul_eq_mul]
  by_cases hx : x ∈ K
  · rw [(exists_expMultiplier K hK s).choose_spec x hx]
  · have hz : (f : 𝓢(ℝ, ℂ)) x = 0 := notMem_support.mp (fun h => hx (f.property h))
    simp [hz]

def extendFixedExpSchwartz {K : Set ℝ} (hK : IsCompact K) :
    LogFixedTest K →L[ℂ] ↥(ExpSchwartzFixed K) where
  toFun f := ⟨⟨fun s => fixedExpSchwartzCoordinate hK s f, fun s x => by
    rw [fixedExpSchwartzCoordinate_apply, fixedExpSchwartzCoordinate_apply (s := 0)]
    simp⟩, fun x hx => f.property (by
      change fixedExpSchwartzCoordinate hK 0 f x ≠ 0 at hx
      simpa [fixedExpSchwartzCoordinate_apply] using hx)⟩
  map_add' f g := by
    apply Subtype.ext
    apply Subtype.ext
    funext s
    exact map_add (fixedExpSchwartzCoordinate hK s) f g
  map_smul' c f := by
    apply Subtype.ext
    apply Subtype.ext
    funext s
    exact map_smul (fixedExpSchwartzCoordinate hK s) c f
  cont := (continuous_pi fun s => (fixedExpSchwartzCoordinate hK s).continuous
    ).subtype_mk _ |>.subtype_mk _

def restrictFixedExpSchwartz (K : Set ℝ) :
    ↥(ExpSchwartzFixed K) →L[ℂ] LogFixedTest K where
  toLinearMap := ((expSchwartzEvaluation 0).comp (ExpSchwartzFixed K).subtypeL).toLinearMap
    |>.codRestrict (fixedSupportSchwartz K) (fun f => f.property)
  cont := ((expSchwartzEvaluation 0).continuous.comp continuous_subtype_val).subtype_mk _

/-- On a compact support every exponential Schwartz seminorm is continuous
for the single unweighted Schwartz topology. -/
def fixedExpSchwartzEquiv {K : Set ℝ} (hK : IsCompact K) :
    ↥(ExpSchwartzFixed K) ≃L[ℂ] LogFixedTest K where
  toLinearEquiv := LinearEquiv.ofLinear (restrictFixedExpSchwartz K).toLinearMap
    (extendFixedExpSchwartz hK).toLinearMap
    (LinearMap.ext fun f => by
      apply Subtype.ext
      ext x
      change fixedExpSchwartzCoordinate hK 0 f x = _
      simp [fixedExpSchwartzCoordinate_apply])
    (LinearMap.ext fun f => by
      apply Subtype.ext
      apply Subtype.ext
      funext s
      ext x
      change fixedExpSchwartzCoordinate hK s (restrictFixedExpSchwartz K f) x =
        (f.1 : ℝ → 𝓢(ℝ, ℂ)) s x
      rw [fixedExpSchwartzCoordinate_apply]
      exact (f.1.property s x).symm)
  continuous_toFun := (restrictFixedExpSchwartz K).continuous
  continuous_invFun := (extendFixedExpSchwartz hK).continuous

abbrev FixedSmoothTest (K : Compacts ℝ) := 𝓓_{K}(ℝ, ℂ)

private def forgetFixedSchwartz (K : Compacts ℝ) :
    LogFixedTest (K : Set ℝ) →ₗ[ℂ] FixedSmoothTest K where
  toFun f := ContDiffMapSupportedIn.of_support_subset
    ((f : 𝓢(ℝ, ℂ)).smooth ⊤) f.property
  map_add' _ _ := by ext x; rfl
  map_smul' _ _ := by ext x; rfl

private def fixedTestToSchwartz (K : Compacts ℝ) :
    FixedSmoothTest K →ₗ[ℂ] LogFixedTest (K : Set ℝ) where
  toFun f := ⟨f.hasCompactSupport.toSchwartzMap (f.contDiff), f.support_subset⟩
  map_add' _ _ := by apply Subtype.ext; ext x; rfl
  map_smul' _ _ := by apply Subtype.ext; ext x; rfl

private theorem continuous_forgetFixedSchwartz (K : Compacts ℝ) :
    Continuous (forgetFixedSchwartz K) := by
  classical
  have hq := ContDiffMapSupportedIn.withSeminorms ℂ ℝ ℂ (n := ⊤) (K := K)
  have hp := (fixedSupportSchwartz K).subtype.withSeminorms_induced
    (schwartz_withSeminorms ℂ ℝ ℂ)
  refine WithSeminorms.continuous_of_isBounded hp hq (forgetFixedSchwartz K)
    (Seminorm.IsBounded.of_real fun n => ⟨{(0,n)}, 1, fun f => ?_⟩)
  simp only [Finset.sup_singleton, one_mul, SeminormFamily.comp_apply,
]
  apply (ContDiffMapSupportedIn.seminorm_top_le_iff ℂ (apply_nonneg _ _) n _).mpr
  intro x _
  exact SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ (f : 𝓢(ℝ, ℂ)) n x

private theorem continuous_fixedTestToSchwartz (K : Compacts ℝ) :
    Continuous (fixedTestToSchwartz K) := by
  classical
  apply continuous_induced_rng.mpr
  have hp := ContDiffMapSupportedIn.withSeminorms ℂ ℝ ℂ (n := ⊤) (K := K)
  obtain ⟨M, hM⟩ := (K.isCompact.bddAbove_image continuous_norm.continuousOn).exists_ge 1
  refine WithSeminorms.continuous_of_isBounded hp (schwartz_withSeminorms ℂ ℝ ℂ)
    ((fixedSupportSchwartz K).subtype.comp (fixedTestToSchwartz K))
    (Seminorm.IsBounded.of_real fun ⟨k,n⟩ => ⟨{n}, M ^ k, fun f => ?_⟩)
  simp only [Finset.sup_singleton]
  have hpow : 0 ≤ M ^ k := pow_nonneg (zero_le_one.trans hM.1) _
  apply SchwartzMap.seminorm_le_bound ℂ _ _ _ (mul_nonneg hpow (apply_nonneg _ _))
  intro x
  change ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (f : ℝ → ℂ) x‖ ≤
    M ^ k * ContDiffMapSupportedIn.seminorm ℂ ℝ ℂ ⊤ K n f
  by_cases hx : x ∈ (K : Set ℝ)
  · have hmem : ‖x‖ ∈ (fun y : ℝ => ‖y‖) '' (K : Set ℝ) := ⟨x, hx, rfl⟩
    exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (hM.2 _ hmem) _)
      (ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm_top ℂ)
      (norm_nonneg _) hpow
  · simp only [f.iteratedFDeriv_zero_on_compl hx, Pi.zero_apply, norm_zero, mul_zero]
    exact mul_nonneg hpow (apply_nonneg _ _)

/-- On a compact set the Schwartz subspace topology is exactly uniform
convergence of the function and all its derivatives. -/
def fixedSchwartzSmoothEquiv (K : Compacts ℝ) :
    LogFixedTest (K : Set ℝ) ≃L[ℂ] FixedSmoothTest K where
  toLinearEquiv := LinearEquiv.ofLinear (forgetFixedSchwartz K) (fixedTestToSchwartz K)
    (LinearMap.ext fun f => by ext x; rfl)
    (LinearMap.ext fun f => by apply Subtype.ext; ext x; rfl)
  continuous_toFun := continuous_forgetFixedSchwartz K
  continuous_invFun := continuous_fixedTestToSchwartz K

def fixedExpSchwartzSmoothEquiv (K : Compacts ℝ) :
    ↥(ExpSchwartzFixed (K : Set ℝ)) ≃L[ℂ] FixedSmoothTest K :=
  (fixedExpSchwartzEquiv K.isCompact).trans (fixedSchwartzSmoothEquiv K)

end
end Masullo
