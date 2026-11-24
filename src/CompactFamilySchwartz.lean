import ModulatedSobolevProfiles
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv

open Filter Function Set Topology
open scoped SchwartzMap

namespace Masullo

noncomputable section

private theorem schwartz_derivPow_apply {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℂ F] [NormedSpace ℝ F] [SMulCommClass ℝ ℂ F]
    (f : 𝓢(ℝ, F)) (n : ℕ) :
    ⇑((SchwartzMap.derivCLM ℂ F ^ n) f) = iteratedDeriv n f := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', iteratedDeriv_succ]
    change deriv (⇑((SchwartzMap.derivCLM ℂ F ^ n) f)) = _
    rw [ih]

variable {K : Type*} [TopologicalSpace K] [CompactSpace K] [T2Space K]

/-- A continuous compact family of scalar Schwartz functions is a single
Schwartz function with values in the compact supremum norm. -/
theorem exists_compactFamilySchwartz (f : K → 𝓢(ℝ, ℂ)) (hf : Continuous f) :
    ∃ F : 𝓢(ℝ, C(K, ℂ)), ∀ x k, F x k = f k x := by
  letI : MeasurableSpace K := borel K
  letI : BorelSpace K := ⟨rfl⟩
  apply HasUniformRadialSchwartzDerivatives.toUniformProfile (f := fun p : ℝ × K ↦ f p.2 p.1)
  let D (n : ℕ) (p : ℝ × K) := ((SchwartzMap.derivCLM ℂ ℂ ^ n) (f p.2)) p.1
  have hD (n : ℕ) (p : ℝ × K) : D n p = iteratedDeriv n (f p.2) p.1 :=
    congrFun (schwartz_derivPow_apply (f p.2) n) p.1
  refine ⟨D, rfl, ?_, ?_, ?_⟩
  · intro n
    let B := SchwartzMap.toBoundedContinuousFunctionCLM ℂ ℝ ℂ
    exact ((B.continuous.comp ((SchwartzMap.derivCLM ℂ ℂ ^ n).continuous.comp hf)).comp
      continuous_snd).eval continuous_fst
  · intro n x k
    have h := ((SchwartzMap.derivCLM ℂ ℂ ^ n) (f k)).differentiableAt (x := x)
    refine h.hasDerivAt.congr_deriv ?_
    rw [show D (n + 1) (x, k) = (SchwartzMap.derivCLM ℂ ℂ)
      ((SchwartzMap.derivCLM ℂ ℂ ^ n) (f k)) x by dsimp only [D]; rw [pow_succ']; rfl]
    exact (SchwartzMap.derivCLM_apply ℂ _ _).symm
  · intro p n
    have hc := ((schwartz_withSeminorms ℂ ℝ ℂ).continuous_seminorm (p, n)).comp hf
    obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hc.continuousOn
    refine ⟨max 0 C, le_max_left _ _, fun x k ↦ ?_⟩
    rw [hD, Real.norm_eq_abs]
    exact (SchwartzMap.le_seminorm' ℂ p n (f k) x).trans
      ((le_abs_self _).trans ((hC k (mem_univ k)).trans (le_max_right _ _)))

omit [T2Space K] in
private theorem iteratedDeriv_compactEval (F : 𝓢(ℝ, C(K, ℂ))) (k : K) (n : ℕ) :
    iteratedDeriv n (fun x ↦ F x k) = fun x ↦ iteratedDeriv n F x k := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iteratedDeriv_succ, iteratedDeriv_succ, ih]
    funext x
    let P := (SchwartzMap.derivCLM ℂ C(K, ℂ) ^ n) F
    have he : ⇑P = iteratedDeriv n F := schwartz_derivPow_apply F n
    rw [← he]
    let L : C(K, ℂ) →L[ℝ] ℂ := ContinuousMap.evalCLM ℝ k
    have h := L.hasFDerivAt.comp_hasDerivAt x (P.differentiableAt (x := x)).hasDerivAt
    exact h.deriv

omit [T2Space K] in
/-- The pointwise bounds on a compact family also bound the corresponding
sup-norm-valued Schwartz seminorm. -/
theorem compactFamilySchwartz_seminorm_le (F : 𝓢(ℝ, C(K, ℂ))) (f : K → 𝓢(ℝ, ℂ))
    (he : ∀ x k, F x k = f k x) (p n : ℕ) {M : ℝ} (hM : 0 ≤ M)
    (hf : ∀ k, SchwartzMap.seminorm ℂ p n (f k) ≤ M) :
    SchwartzMap.seminorm ℂ p n F ≤ M := by
  apply SchwartzMap.seminorm_le_bound' ℂ p n F hM
  intro x
  have h : ‖(|x| ^ p : ℝ) • iteratedDeriv n F x‖ ≤ M := by
    apply (ContinuousMap.norm_le _ hM).mpr
    intro k
    rw [ContinuousMap.smul_apply, norm_smul, Real.norm_of_nonneg (by positivity)]
    have eq : iteratedDeriv n F x k = iteratedDeriv n (f k) x :=
      (congrFun (iteratedDeriv_compactEval F k n) x).symm.trans
        (congrFun (congrArg (iteratedDeriv n) (funext fun y ↦ he y k)) x)
    rw [eq]
    exact (SchwartzMap.le_seminorm' ℂ p n (f k) x).trans (hf k)
  rwa [norm_smul, Real.norm_of_nonneg (by positivity)] at h


set_option maxHeartbeats 900000 in
private theorem continuous_supNormSchwartzMap {E : Type*}
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    (A : K → E →ₗ[ℂ] 𝓢(ℝ, ℂ))
    (hA : Continuous fun z : K × E ↦ A z.1 z.2)
    (L : E →ₗ[ℂ] 𝓢(ℝ, C(K, ℂ))) (hL : ∀ f x k, L f x k = A k f x) :
    Continuous L := by
  apply (schwartz_withSeminorms ℂ ℝ C(K, ℂ)).continuous_of_continuous_comp L
  rintro ⟨p, n⟩
  let q := SchwartzMap.seminorm ℂ p n (E := ℝ) (F := ℂ)
  let Q := (SchwartzMap.seminorm ℂ p n (E := ℝ) (F := C(K, ℂ))).comp L
  change Continuous Q
  apply Seminorm.continuous_of_continuousAt_zero
  rw [ContinuousAt, map_zero]
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let U : Set (K × E) := {z | q (A z.1 z.2) < ε / 2}
  have hU : IsOpen U :=
    isOpen_lt (((schwartz_withSeminorms ℂ ℝ ℂ).continuous_seminorm (p, n)).comp hA) continuous_const
  have hsub : (univ : Set K) ×ˢ ({0} : Set E) ⊆ U := by
    rintro ⟨k, f⟩ ⟨_, rfl : f = 0⟩
    change q (A k 0) < ε / 2
    simpa only [map_zero] using half_pos hε
  obtain ⟨V, W, _, hW, hV, h0, hVW⟩ :=
    generalized_tube_lemma isCompact_univ isCompact_singleton hU hsub
  filter_upwards [hW.mem_nhds (h0 (mem_singleton 0))] with f hf
  have hb (k : K) : SchwartzMap.seminorm ℂ p n (A k f) ≤ ε / 2 := by
    have hz : (k, f) ∈ U := hVW (show (k, f) ∈ V ×ˢ W from ⟨hV (mem_univ k), hf⟩)
    change q (A k f) < ε / 2 at hz
    exact hz.le
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (apply_nonneg _ _)]
  exact (compactFamilySchwartz_seminorm_le (L f) (fun k ↦ A k f)
    (hL f) p n (half_pos hε).le hb).trans_lt (half_lt_self hε)


set_option maxHeartbeats 900000 in
/-- A jointly continuous linear family on a compact parameter gives a
continuous linear map to Schwartz profiles in the compact supremum norm. -/
theorem exists_continuous_compactFamilySchwartz {E : Type*}
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    (A : K → E →ₗ[ℂ] 𝓢(ℝ, ℂ))
    (hA : Continuous fun z : K × E ↦ A z.1 z.2) :
    ∃ L : E →L[ℂ] 𝓢(ℝ, C(K, ℂ)), ∀ f x k, L f x k = A k f x := by
  have h (f : E) := exists_compactFamilySchwartz (fun k ↦ A k f)
    (hA.comp (continuous_id.prodMk continuous_const))
  let L : E →ₗ[ℂ] 𝓢(ℝ, C(K, ℂ)) := {
    toFun f := (h f).choose
    map_add' f g := SchwartzMap.ext fun x ↦ ContinuousMap.ext fun k ↦ by
      change (h (f + g)).choose x k = (h f).choose x k + (h g).choose x k
      rw [(h (f + g)).choose_spec, (h f).choose_spec, (h g).choose_spec, map_add]
      rfl
    map_smul' c f := SchwartzMap.ext fun x ↦ ContinuousMap.ext fun k ↦ by
      change (h (c • f)).choose x k = c • (h f).choose x k
      rw [(h (c • f)).choose_spec, (h f).choose_spec, map_smul]
      rfl }
  have hL (f : E) (x : ℝ) (k : K) : L f x k = A k f x := (h f).choose_spec x k
  exact ⟨⟨L, continuous_supNormSchwartzMap A hA L hL⟩, hL⟩

end
end Masullo
