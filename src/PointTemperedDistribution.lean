import PointDistributionJets
import SchwartzCompactApproximation

open Filter Function Set TopologicalSpace Topology WithSeminorms
open scoped ContDiff Distributions SchwartzMap

namespace Masullo

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private abbrev Tests (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] :=
  𝓓((⊤ : Opens V), ℂ)

private def supportedTestToSchwartz (K : Compacts E) : 𝓓_{K}(E, ℂ) →L[ℂ] 𝓢(E, ℂ) := by
  let L : 𝓓_{K}(E, ℂ) →ₗ[ℂ] 𝓢(E, ℂ) :=
    { toFun := fun f ↦ f.hasCompactSupport.toSchwartzMap f.contDiff
      map_add' := fun f g ↦ by ext; rfl
      map_smul' := fun c f ↦ by ext; rfl }
  refine ⟨L, continuous_of_isBounded (ContDiffMapSupportedIn.withSeminorms ..)
    (schwartz_withSeminorms ℂ E ℂ) L ?_⟩
  obtain ⟨r, hkr⟩ := (Metric.isBounded_iff_subset_ball (0 : E)).mp K.isCompact.isBounded
  let R := max 1 r
  have hR : 0 ≤ R := zero_le_one.trans (le_max_left _ _)
  rintro ⟨k, j⟩
  refine ⟨{j}, ‖R‖₊ ^ k, fun f ↦ ?_⟩
  simp only [Finset.sup_singleton, Seminorm.comp_apply, smul_apply,
    NNReal.smul_def, smul_eq_mul, NNReal.coe_pow, coe_nnnorm, Real.norm_of_nonneg hR]
  apply SchwartzMap.seminorm_le_bound ℂ k j (L f) (by positivity)
  intro x
  change ‖x‖ ^ k * ‖iteratedFDeriv ℝ j (f : E → ℂ) x‖ ≤ _
  by_cases hx : x ∈ (K : Set E)
  · have hxr : ‖x‖ ≤ R :=
      (show ‖x‖ < r by simpa only [Metric.mem_ball, dist_zero_right] using hkr hx).le.trans
        (le_max_right _ _)
    exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hxr _)
      (ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm_top ℂ)
      (norm_nonneg _) (by positivity)
  · have hx' : x ∉ tsupport (iteratedFDeriv ℝ j (f : E → ℂ)) :=
      fun h ↦ hx (f.tsupport_subset (tsupport_iteratedFDeriv_subset j h))
    rw [image_eq_zero_of_notMem_tsupport hx', norm_zero, mul_zero]
    positivity

/-- The canonical inclusion of compactly supported smooth tests in the
Schwartz space is continuous for the LF topology. -/
def smoothTestToSchwartz : Tests E →L[ℂ] 𝓢(E, ℂ) :=
  TestFunction.limitCLM ℂ (fun f ↦ f.hasCompactSupport.toSchwartzMap f.contDiff)
    (fun K _ ↦ supportedTestToSchwartz K) (fun _ _ _ ↦ by ext; rfl)

@[simp] theorem smoothTestToSchwartz_apply (f : Tests E) (x : E) :
    smoothTestToSchwartz f x = f x := rfl

/-- Restricting a tempered distribution to compactly supported tests gives
one derivative order valid on all compact support stages. -/
theorem exists_order_tempered_on_smoothTests (T : 𝓢(E, ℂ) →L[ℂ] ℂ) :
    ∃ N, testDistributionOrderLE (T.comp smoothTestToSchwartz) N := by
  let q := (normSeminorm ℂ ℂ).comp T.toLinearMap
  have hq : Continuous q := T.continuous.norm
  obtain ⟨S, C, _, hC⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ E ℂ) q hq
  let N := S.sup Prod.snd
  let M := S.sup Prod.fst
  refine ⟨N, fun K ↦ ?_⟩
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_ball (0 : E)).mp K.isCompact.isBounded
  let R := max 1 r
  have hR : 1 ≤ R := le_max_left _ _
  refine ⟨(C : ℝ) * R ^ M, by positivity, fun f hf B hB hjet ↦ ?_⟩
  have hs (a : ℕ × ℕ) (ha : a ∈ S) :
      SchwartzMap.seminorm ℂ a.1 a.2 (smoothTestToSchwartz f) ≤ R ^ M * B := by
    apply SchwartzMap.seminorm_le_bound ℂ _ _ _ (by positivity)
    intro x
    change ‖x‖ ^ a.1 * ‖iteratedFDeriv ℝ a.2 (f : E → ℂ) x‖ ≤ _
    by_cases hx : x ∈ (K : Set E)
    · have hxr : ‖x‖ ≤ R :=
        (show ‖x‖ < r by simpa only [Metric.mem_ball, dist_zero_right] using hr hx).le.trans
          (le_max_right _ _)
      exact mul_le_mul ((pow_le_pow_left₀ (norm_nonneg _) hxr _).trans
        (pow_le_pow_right₀ hR (Finset.le_sup ha))) (hjet a.2 (Finset.le_sup ha) x)
        (norm_nonneg _) (by positivity)
    · have hx' : x ∉ tsupport (iteratedFDeriv ℝ a.2 (f : E → ℂ)) :=
        fun h ↦ hx (hf (tsupport_iteratedFDeriv_subset _ h))
      rw [image_eq_zero_of_notMem_tsupport hx', norm_zero, mul_zero]
      positivity
  have he : (S.sup (schwartzSeminormFamily ℂ E ℂ)) (smoothTestToSchwartz f) ≤ R ^ M * B :=
    Seminorm.finset_sup_apply_le (by positivity) hs
  calc
    ‖(T.comp smoothTestToSchwartz) f‖ ≤ (C : ℝ) *
        (S.sup (schwartzSeminormFamily ℂ E ℂ)) (smoothTestToSchwartz f) := hC _
    _ ≤ (C : ℝ) * (R ^ M * B) := mul_le_mul_of_nonneg_left he C.coe_nonneg
    _ = _ := by ring

/-- Evaluation of an iterated derivative at zero is a continuous linear
functional on the real Schwartz space. -/
def realSchwartzJet (k : ℕ) : 𝓢(ℝ, ℂ) →L[ℂ] ℂ := by
  have htop : (k : ℕ∞ω) ≤ ∞ := by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤)
  let L : 𝓢(ℝ, ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun f ↦ iteratedDeriv k (f : ℝ → ℂ) 0
      map_add' := fun f g ↦ iteratedDeriv_add (f.smooth'.of_le htop).contDiffAt
        (g.smooth'.of_le htop).contDiffAt
      map_smul' := fun a f ↦ iteratedDeriv_const_smul (f.smooth'.of_le htop).contDiffAt a }
  refine ⟨L, continuous_of_isBounded (schwartz_withSeminorms ℂ ℝ ℂ)
    (norm_withSeminorms ℂ ℂ) L (fun _ ↦ ⟨{(0,k)}, 1, fun f ↦ ?_⟩)⟩
  simp only [Finset.sup_singleton, one_smul]
  change ‖iteratedDeriv k (f : ℝ → ℂ) 0‖ ≤ SchwartzMap.seminorm ℂ 0 k f
  rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  exact SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ f k 0

@[simp] theorem realSchwartzJet_apply (k : ℕ) (f : 𝓢(ℝ, ℂ)) :
    realSchwartzJet k f = iteratedDeriv k (f : ℝ → ℂ) 0 := rfl

/-- The finite derivative expansion of a tempered distribution carried by
the origin on the real line. The compact-test expansion extends by density
in the full Schwartz topology. -/
theorem pointTemperedDistribution_eq_sum_derivative_eval
    (T : 𝓢(ℝ, ℂ) →L[ℂ] ℂ) (hvan : Distribution.IsVanishingOn (⇑T) ({0} : Set ℝ)ᶜ) :
    ∃ N, ∃ c : Fin (N + 1) → ℂ, ∀ f : 𝓢(ℝ, ℂ),
      T f = ∑ j : Fin (N + 1), c j * iteratedDeriv j.val (f : ℝ → ℂ) 0 := by
  obtain ⟨N, hN⟩ := exists_order_tempered_on_smoothTests T
  obtain ⟨c, hc⟩ := pointTestDistribution_eq_sum_derivative_eval
    (T.comp smoothTestToSchwartz) N hN (fun f hf ↦ hvan (smoothTestToSchwartz f) hf)
  refine ⟨N, c, fun f ↦ ?_⟩
  have hg (g : 𝓢(ℝ, ℂ)) (h : HasCompactSupport g) :
      T g = ∑ j : Fin (N + 1), c j * iteratedDeriv j.val (g : ℝ → ℂ) 0 := by
    let g' : Tests ℝ := ⟨g, g.smooth', h, subset_univ _⟩
    have he : smoothTestToSchwartz g' = g := by ext; rfl
    have h' := hc g'
    change T (smoothTestToSchwartz g') = _ at h'
    rw [he] at h'
    exact h'
  obtain ⟨g, hgc, hgf⟩ := exists_schwartz_compactSupport_sequence f
  have hL := T.continuous.continuousAt.tendsto.comp hgf
  have hR : Continuous (fun g : 𝓢(ℝ, ℂ) ↦
      ∑ j : Fin (N + 1), c j * iteratedDeriv j.val (g : ℝ → ℂ) 0) := by
    apply continuous_finsetSum
    intro j _
    apply continuous_const.mul
    exact (realSchwartzJet j.val).continuous
  exact tendsto_nhds_unique hL ((hR.continuousAt.tendsto.comp hgf).congr
    (fun n ↦ (hg (g n) (hgc n)).symm))

private theorem tempered_eq_zero_of_compact_tsupport_disjoint
    [FiniteDimensional ℝ E]
    (T : 𝓢(E, ℂ) →L[ℂ] ℂ) (f : 𝓢(E, ℂ)) (hC : HasCompactSupport f)
    (hdis : tsupport f ⊆ (Distribution.dsupport (⇑T))ᶜ) : T f = 0 := by
  classical
  let I := tsupport f
  have hl (x : I) := (Distribution.notMem_dsupport_iff x.val).mp (hdis x.property)
  choose U hUvan hUopen hxU using hl
  choose r hr hball using fun x : I ↦ Metric.isOpen_iff.mp (hUopen x) x.val (hxU x)
  let b (x : I) : ContDiffBump x.val := ⟨r x / 3, r x / 2, by linarith [hr x], by linarith [hr x]⟩
  let χ (x : I) (y : E) : ℂ := (b x y : ℂ)
  have hχ (x : I) : (χ x).HasTemperateGrowth :=
    ((b x).hasCompactSupport.comp_left Complex.ofReal_zero).hasTemperateGrowth
      (Complex.ofRealCLM.contDiff.comp (b x).contDiff)
  have hχU (x : I) : tsupport (χ x) ⊆ U x := by
    apply (tsupport_comp_subset Complex.ofReal_zero (b x)).trans
    rw [(b x).tsupport_eq]
    exact (Metric.closedBall_subset_ball (by
      change r x / 2 < r x
      linarith [hr x])).trans (hball x)
  let V (x : I) := Metric.ball x.val (r x / 3)
  have hfV : tsupport f ⊆ ⋃ x : I, V x := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, Metric.mem_ball_self (by linarith [hr ⟨x,hx⟩])⟩
  obtain ⟨J, hJ⟩ := hC.elim_finite_subcover V (fun _ ↦ Metric.isOpen_ball) hfV
  have hk (J : Finset I) (g : 𝓢(E, ℂ)) (hg : tsupport g ⊆ ⋃ x ∈ J, V x) :
      T g = 0 := by
    induction J using Finset.induction_on generalizing g with
    | empty =>
      have hz : g = 0 := by
        ext x
        exact image_eq_zero_of_notMem_tsupport (fun hx ↦ by simpa using hg hx)
      rw [hz, map_zero]
    | insert x J hx ih =>
      let m := SchwartzMap.smulLeftCLM ℂ (χ x) g
      have hTm : T m = 0 :=
        hUvan x m ((SchwartzMap.tsupport_smulLeftCLM_subset _ _).trans
          (inter_subset_right.trans (hχU x)))
      let d := g - m
      have hds : tsupport d ⊆ tsupport g :=
        (tsupport_sub _ _).trans (union_subset Subset.rfl
          ((SchwartzMap.tsupport_smulLeftCLM_subset _ _).trans inter_subset_left))
      have hdV : tsupport d ⊆ ⋃ y ∈ J, V y := by
        intro y hy
        have hu : y ∈ V x ∪ ⋃ z ∈ J, V z := by
          simpa only [Finset.mem_insert, iUnion_iUnion_eq_or_left] using hg (hds hy)
        refine hu.resolve_left (fun hxy ↦ ?_)
        have hloc : (d : E → ℂ) =ᶠ[𝓝 y] 0 := by
          filter_upwards [Metric.isOpen_ball.mem_nhds hxy] with z hz
          change g z - m z = 0
          rw [show m z = χ x z * g z from SchwartzMap.smulLeftCLM_apply_apply (hχ x) _ _]
          have hχ1 : χ x z = 1 := by
            change ((b x z : ℝ) : ℂ) = 1
            rw [(b x).one_of_mem_closedBall (Metric.ball_subset_closedBall hz), Complex.ofReal_one]
          rw [hχ1, one_mul, sub_self]
        exact (notMem_tsupport_iff_eventuallyEq.mpr hloc) hy
      have hz := ih d hdV
      change T (g - m) = 0 at hz
      rw [map_sub, hTm, sub_zero] at hz
      exact hz
  exact hk J f hJ

/-- On a finite-dimensional real Schwartz space, distributional support contained in a closed
set implies vanishing on tests supported in its complement. A finite
smooth cutoff cover handles the compact case and density handles the tail. -/
theorem temperedDistribution_isVanishingOn_compl_of_dsupport_subset
    [FiniteDimensional ℝ E]
    (T : 𝓢(E, ℂ) →L[ℂ] ℂ) {K : Set E} (hK : Distribution.dsupport (⇑T) ⊆ K) :
    Distribution.IsVanishingOn (⇑T) Kᶜ := by
  intro f hf
  obtain ⟨g, hg, hlim⟩ := exists_schwartz_compactSupport_sequence_subset f
  have hzero (n : ℕ) : T (g n) = 0 :=
    tempered_eq_zero_of_compact_tsupport_disjoint T (g n) (hg n).1
      ((hg n).2.trans (hf.trans (compl_subset_compl.mpr hK)))
  have h := T.continuous.continuousAt.tendsto.comp hlim
  exact tendsto_nhds_unique h (tendsto_const_nhds.congr (fun n ↦ (hzero n).symm))

theorem realTemperedDistribution_isVanishingOn_compl_of_dsupport_subset
    (T : 𝓢(ℝ, ℂ) →L[ℂ] ℂ) {K : Set ℝ} (hK : Distribution.dsupport (⇑T) ⊆ K) :
    Distribution.IsVanishingOn (⇑T) Kᶜ :=
  temperedDistribution_isVanishingOn_compl_of_dsupport_subset T hK

/-- The point-support hypothesis expressed by distributional support
implies the full Schwartz derivative expansion. -/
theorem pointTemperedDistribution_eq_sum_of_dsupport
    (T : 𝓢(ℝ, ℂ) →L[ℂ] ℂ) (hT : Distribution.dsupport (⇑T) ⊆ {0}) :
    ∃ N, ∃ c : Fin (N + 1) → ℂ, ∀ f : 𝓢(ℝ, ℂ),
      T f = ∑ j : Fin (N + 1), c j * realSchwartzJet j.val f :=
  pointTemperedDistribution_eq_sum_derivative_eval T
    (realTemperedDistribution_isVanishingOn_compl_of_dsupport_subset T hT)

/-- A finite derivative expansion has order at most M precisely when
every coefficient above M vanishes. In particular, for a nonzero
expansion the largest nonzero index is its exact distribution order. -/
theorem pointTemperedDistribution_order_iff
    (T : 𝓢(ℝ, ℂ) →L[ℂ] ℂ) (N M : ℕ) (c : Fin (N+1) → ℂ)
    (hT : ∀ f : 𝓢(ℝ, ℂ), T f = ∑ j : Fin (N+1), c j * realSchwartzJet j.val f) :
    testDistributionOrderLE (T.comp smoothTestToSchwartz) M ↔
      ∀ j : Fin (N+1), M < j.val → c j = 0 := by
  classical
  constructor
  · intro hM j hj
    have hvan : Distribution.IsVanishingOn (⇑(T.comp smoothTestToSchwartz)) ({0} : Set ℝ)ᶜ := by
      intro f hf
      have hloc : (f : ℝ → ℂ) =ᶠ[𝓝 0] 0 :=
        notMem_tsupport_iff_eventuallyEq.mp (fun h ↦ hf h rfl)
      change T (smoothTestToSchwartz f) = 0
      rw [hT]
      apply Finset.sum_eq_zero
      intro k _
      change c k * iteratedDeriv k.val (f : ℝ → ℂ) 0 = 0
      rw [hloc.iteratedDeriv_eq k.val, iteratedDeriv_eq_iteratedFDeriv]
      change c k * iteratedFDeriv ℝ k.val (fun _ : ℝ ↦ (0 : ℂ)) 0 _ = 0
      rw [iteratedFDeriv_fun_zero]
      exact mul_zero _
    obtain ⟨d, hd⟩ := pointTestDistribution_eq_sum_derivative_eval
      (T.comp smoothTestToSchwartz) M hM hvan
    obtain ⟨f, hf⟩ := exists_smoothTest_single_jet j.val
    have hz := hd f
    have hz' : (T.comp smoothTestToSchwartz) f = 0 := by
      rw [hz]
      apply Finset.sum_eq_zero
      intro k _
      rw [hf, ite_eq_right (by omega : k.val ≠ j.val), mul_zero]
    change T (smoothTestToSchwartz f) = 0 at hz'
    rw [hT] at hz'
    rw [Finset.sum_eq_single j] at hz'
    · change c j * iteratedDeriv j.val (f : ℝ → ℂ) 0 = 0 at hz'
      simpa [hf] using hz'
    · intro k _ hkj
      change c k * iteratedDeriv k.val (f : ℝ → ℂ) 0 = 0
      rw [hf, ite_eq_right (fun e ↦ hkj (Fin.ext e)), mul_zero]
    · simp
  · intro hM K
    refine ⟨∑ j, ‖c j‖, by positivity, fun f _ B hB hjet ↦ ?_⟩
    change ‖T (smoothTestToSchwartz f)‖ ≤ _
    rw [hT, Finset.sum_mul]
    apply (norm_sum_le _ _).trans (Finset.sum_le_sum (fun j _ ↦ ?_))
    by_cases hj : j.val ≤ M
    · rw [norm_mul]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      change ‖iteratedDeriv j.val (f : ℝ → ℂ) 0‖ ≤ B
      rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
      exact hjet j.val hj 0
    · simp [hM j (lt_of_not_ge hj)]

end
end Masullo
