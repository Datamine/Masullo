import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.Analysis.Distribution.Support
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

open Filter Function Set TopologicalSpace Topology WithSeminorms
open scoped Distributions SchwartzMap ContDiff

namespace Masullo

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

private def supportedSchwartzToTest (K : Compacts E)
    (χ : E → ℂ) (hχ : χ.HasTemperateGrowth) (hs : support χ ⊆ K) :
    𝓢(E, ℂ) →L[ℂ] 𝓓_{K}(E, ℂ) := by
  let M := SchwartzMap.smulLeftCLM ℂ χ
  have hM (f : 𝓢(E, ℂ)) (x : E) : M f x = χ x * f x :=
    SchwartzMap.smulLeftCLM_apply_apply hχ f x
  let L : 𝓢(E, ℂ) →ₗ[ℂ] 𝓓_{K}(E, ℂ) :=
    { toFun := fun f ↦ ContDiffMapSupportedIn.of_support_subset (M f).smooth'
        (fun x hx ↦ hs (fun hz ↦ hx (by
          change M f x = 0
          rw [hM f x, hz, zero_mul])))
      map_add' := fun f g ↦ by ext x; exact congrFun (congrArg DFunLike.coe (map_add M f g)) x
      map_smul' := fun a f ↦ by ext x; exact congrFun (congrArg DFunLike.coe (map_smul M a f)) x }
  refine ⟨L, continuous_of_continuous_comp (ContDiffMapSupportedIn.withSeminorms ..) L ?_⟩
  intro i
  have he : (ContDiffMapSupportedIn.seminorm ℂ E ℂ ⊤ K i).comp L =
      (SchwartzMap.seminorm ℂ 0 i).comp M.toLinearMap := by
    ext f
    apply le_antisymm
    · change ContDiffMapSupportedIn.seminorm ℂ E ℂ ⊤ K i (L f) ≤
        SchwartzMap.seminorm ℂ 0 i (M f)
      rw [ContDiffMapSupportedIn.seminorm_top_le_iff ℂ (apply_nonneg ..)]
      intro x _
      exact SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ (M f) i x
    · change SchwartzMap.seminorm ℂ 0 i (M f) ≤
        ContDiffMapSupportedIn.seminorm ℂ E ℂ ⊤ K i (L f)
      apply SchwartzMap.seminorm_le_bound ℂ 0 i (M f) (apply_nonneg ..)
      intro x
      rw [pow_zero, one_mul]
      change ‖iteratedFDeriv ℝ i (⇑(L f)) x‖ ≤ _
      exact ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm_top ℂ
  rw [he]
  exact ((schwartz_withSeminorms ℂ E ℂ).continuous_seminorm (0, i)).comp M.continuous

/-- A distribution that vanishes on tests supported outside a compact set
extends to a tempered distribution. The extension uses a smooth cutoff
identically one on a neighborhood of that compact set. -/
theorem exists_temperedExtension_of_compactSupport
    (T : 𝓓((⊤ : Opens E), ℂ) →L[ℂ] ℂ)
    (K : Compacts E) (hT : Distribution.IsVanishingOn (⇑T) (K : Set E)ᶜ) :
    ∃ A : 𝓢(E, ℂ) →L[ℂ] ℂ, ∀ f : 𝓓((⊤ : Opens E), ℂ),
      A (f.hasCompactSupport.toSchwartzMap f.contDiff) = T f := by
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_ball (0 : E)).mp K.isCompact.isBounded
  let R := max r 1
  have hR : 0 < R := zero_lt_one.trans_le (le_max_right _ _)
  have hK : (K : Set E) ⊆ Metric.ball 0 R := hr.trans (Metric.ball_subset_ball (le_max_left _ _))
  let b : ContDiffBump (0 : E) := ⟨R, R + 1, hR, lt_add_one R⟩
  let χ : E → ℂ := fun x ↦ (b x : ℂ)
  have hc : ContDiff ℝ ∞ χ := Complex.ofRealCLM.contDiff.comp b.contDiff
  have hs : support χ ⊆ Metric.closedBall 0 (R + 1) := by
    apply subset_closure.trans
    exact (tsupport_comp_subset Complex.ofReal_zero b).trans (by rw [b.tsupport_eq])
  let L : Compacts E := ⟨Metric.closedBall 0 (R + 1), isCompact_closedBall _ _⟩
  have hχ : χ.HasTemperateGrowth := HasCompactSupport.hasTemperateGrowth
    (L.isCompact.of_isClosed_subset (isClosed_tsupport _)
      (closure_minimal hs Metric.isClosed_closedBall)) hc
  let M := supportedSchwartzToTest L χ hχ hs
  let j : 𝓓_{L}(E, ℂ) →L[ℂ] 𝓓((⊤ : Opens E), ℂ) :=
    TestFunction.ofSupportedInCLM ℂ (subset_univ _)
  refine ⟨T.comp (j.comp M), fun f ↦ ?_⟩
  let g := j (M (f.hasCompactSupport.toSchwartzMap f.contDiff))
  have hg (x : E) : g x = χ x * f x := SchwartzMap.smulLeftCLM_apply_apply hχ _ x
  have hd : tsupport (g - f) ⊆ (K : Set E)ᶜ := by
    intro x hx hxK
    have he : ((g - f : 𝓓((⊤ : Opens E), ℂ)) : E → ℂ) =ᶠ[𝓝 x] 0 := by
      filter_upwards [Metric.isOpen_ball.mem_nhds (hK hxK)] with y hy
      change g y - f y = 0
      rw [hg, show χ y = 1 by
        change ((b y : ℝ) : ℂ) = 1
        rw [b.one_of_mem_closedBall (Metric.ball_subset_closedBall hy), Complex.ofReal_one],
        one_mul, sub_self]
    exact (notMem_tsupport_iff_eventuallyEq.mpr he) hx
  change T g = T f
  exact sub_eq_zero.mp (by simpa only [map_sub] using hT (g - f) hd)

end
end Masullo
