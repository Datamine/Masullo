/-
Adapted from the Apache-2.0 RiemannMasullo project, commit
cd84b23dd5e4f741037cf31aee06bc90161c6514.
See External/PROVENANCE.md and External/RiemannMasullo.LICENSE.
-/
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.UniformLimitsDeriv

/-! # Completeness of the Schwartz space -/

noncomputable section

open Filter Set Topology
open scoped SchwartzMap ContDiff Uniformity

namespace Masullo

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem schwartz_iteratedFDeriv_sub (f g : 𝓢(E, F)) (n : ℕ) (x : E) :
    iteratedFDeriv ℝ n (f - g : 𝓢(E, F)) x =
      iteratedFDeriv ℝ n f x - iteratedFDeriv ℝ n g x :=
  iteratedFDeriv_sub_apply (f.smooth n).contDiffAt (g.smooth n).contDiffAt

/-- A Cauchy sequence of Schwartz maps has uniformly small weighted derivative differences. -/
private theorem schwartz_cauchy_tail {u : ℕ → 𝓢(E, F)} (hu : CauchySeq u) (k n : ℕ)
    {ε : ℝ} (hε : 0 < ε) : ∃ N, ∀ i ≥ N, ∀ j ≥ N, ∀ x : E,
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (u i) x - iteratedFDeriv ℝ n (u j) x‖ < ε := by
  let p : Seminorm ℝ 𝓢(E, F) := SchwartzMap.seminorm ℝ k n
  have hp : Continuous p := (schwartz_withSeminorms ℝ E F).continuous_seminorm (k, n)
  have hU : {z : 𝓢(E, F) × 𝓢(E, F) | p (z.1 - z.2) < ε} ∈ 𝓤 𝓢(E, F) := by
    rw [uniformity_eq_comap_nhds_zero_swapped]
    have hV : {f | p f < ε} ∈ 𝓝 (0 : 𝓢(E, F)) :=
      hp.continuousAt (x := 0) (Iio_mem_nhds (by simpa using hε))
    exact preimage_mem_comap hV
  obtain ⟨N, hN⟩ := cauchySeq_iff.mp hu _ hU
  refine ⟨N, fun i hi j hj x ↦ ?_⟩
  simpa only [schwartz_iteratedFDeriv_sub] using
    ((u i - u j).le_seminorm ℝ k n x).trans_lt (hN i hi j hj)

/-- Uniform limits of all iterated derivatives form the Taylor series of their zeroth term. -/
private theorem schwartz_limit_taylor {u : ℕ → 𝓢(E, F)}
    {p : (n : ℕ) → E → E [×n]→L[ℝ] F}
    (huni : ∀ n, TendstoUniformly (fun j ↦ iteratedFDeriv ℝ n (u j)) (p n) atTop) :
    HasFTaylorSeriesUpTo ∞ (fun x ↦ (p 0 x).curry0) (fun x n ↦ p n x) := by
  refine ⟨fun _ ↦ rfl, ?_, ?_⟩
  · intro n hn x
    refine hasFDerivAt_of_tendstoUniformly
      (f' := fun j x ↦ (iteratedFDeriv ℝ (n + 1) (u j) x).curryLeft)
      (g' := fun x ↦ (p (n + 1) x).curryLeft) ?_ ?_ (huni n).tendsto_at x
    · let curry := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) ↦ E) F
      exact curry.isometry.uniformContinuous.comp_tendstoUniformly (huni (n + 1))
    · intro j y
      exact (u j).smooth'.ftaylorSeries.fderiv n hn y
  · intro n hn
    exact (huni n).continuous
      (Eventually.of_forall (fun j ↦ (u j).smooth'.ftaylorSeries.cont n hn)).frequently

variable [CompleteSpace F]

/-- The unweighted derivatives of each order have uniform limits. -/
private theorem schwartz_uniform_limits {u : ℕ → 𝓢(E, F)} (hu : CauchySeq u) :
    ∃ p : (n : ℕ) → E → E [×n]→L[ℝ] F,
      ∀ n, TendstoUniformly (fun j ↦ iteratedFDeriv ℝ n (u j)) (p n) atTop := by
  let d (j n : ℕ) := iteratedFDeriv ℝ n (u j)
  have hc (n : ℕ) : UniformCauchySeqOn (fun j ↦ d j n) atTop univ := by
    apply Metric.uniformCauchySeqOn_iff.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := schwartz_cauchy_tail hu 0 n hε
    exact ⟨N, fun i hi j hj x _ ↦ by simpa [d, dist_eq_norm] using hN i hi j hj x⟩
  choose p hp using fun (n : ℕ) (x : E) ↦
    cauchySeq_tendsto_of_complete ((hc n).cauchySeq (mem_univ x))
  have huni (n : ℕ) : TendstoUniformly (fun j ↦ d j n) (p n) atTop :=
    tendstoUniformlyOn_univ.mp ((hc n).tendstoUniformlyOn_of_tendsto fun x _ ↦ hp n x)
  exact ⟨p, huni⟩

/-- Schwartz maps into a complete normed space are complete for the Schwartz seminorms. -/
theorem completeSpace_schwartzMap : CompleteSpace 𝓢(E, F) := by
  have : (𝓤 𝓢(E, F)).IsCountablyGenerated := by
    rw [uniformity_eq_comap_nhds_zero 𝓢(E, F)]
    infer_instance
  apply UniformSpace.complete_of_cauchySeq_tendsto
  intro u hu
  let d (j n : ℕ) := iteratedFDeriv ℝ n (u j)
  obtain ⟨p, huni⟩ := schwartz_uniform_limits hu
  let g (x : E) := (p 0 x).curry0
  have hseries := schwartz_limit_taylor huni
  have heq (n : ℕ) (x : E) : p n x = iteratedFDeriv ℝ n g x :=
    hseries.eq_iteratedFDeriv (by exact_mod_cast le_top) x
  -- Pass the tail estimates to the pointwise limit with the first index fixed.
  have hclose (k n : ℕ) {ε : ℝ} (hε : 0 < ε) : ∃ N, ∀ i ≥ N, ∀ x : E,
      ‖x‖ ^ k * ‖d i n x - p n x‖ ≤ ε := by
    obtain ⟨N, hN⟩ := schwartz_cauchy_tail hu k n hε
    refine ⟨N, fun i hi x ↦ le_of_tendsto
      (tendsto_const_nhds.mul (tendsto_const_nhds.sub ((huni n).tendsto_at x)).norm) ?_⟩
    exact (eventually_ge_atTop N).mono fun j hj ↦ (hN i hi j hj x).le
  let f : 𝓢(E, F) := {
    toFun := g
    smooth' := hseries.contDiff
    decay' := by
      intro k n
      obtain ⟨N, hN⟩ := hclose k n zero_lt_one
      refine ⟨SchwartzMap.seminorm ℝ k n (u N) + 1, fun x ↦ ?_⟩
      rw [← heq]
      calc
        ‖x‖ ^ k * ‖p n x‖ ≤ ‖x‖ ^ k * (‖d N n x‖ + ‖d N n x - p n x‖) :=
          mul_le_mul_of_nonneg_left (norm_le_norm_add_norm_sub (d N n x) (p n x)) (by positivity)
        _ ≤ _ := by
          rw [mul_add]
          exact add_le_add ((u N).le_seminorm ℝ k n x) (hN N le_rfl x) }
  refine ⟨f, ((schwartz_withSeminorms ℝ E F).tendsto_nhds_atTop _ _).mpr ?_⟩
  rintro ⟨k, n⟩ ε hε
  obtain ⟨N, hN⟩ := hclose k n (half_pos hε)
  refine ⟨N, fun i hi ↦ lt_of_le_of_lt
    (SchwartzMap.seminorm_le_bound ℝ k n _ (half_pos hε).le ?_) (half_lt_self hε)⟩
  intro x
  rw [schwartz_iteratedFDeriv_sub]
  change ‖x‖ ^ k * ‖d i n x - iteratedFDeriv ℝ n g x‖ ≤ ε / 2
  rw [← heq]
  exact hN i hi x

/-- A Schwartz series converges when the series of each defining seminorm converges. -/
theorem schwartz_tendsto_partialSums {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℕ → 𝓢(E, ℂ))
    (hs : ∀ k n, Summable (fun i ↦ SchwartzMap.seminorm ℂ k n (f i))) :
    ∃ h : 𝓢(E, ℂ), Tendsto (fun n ↦ ∑ i ∈ Finset.range n, f i) atTop (𝓝 h) := by
  letI : CompleteSpace 𝓢(E, ℂ) := completeSpace_schwartzMap
  apply cauchySeq_tendsto_of_complete
  rw [cauchySeq_iff_tendsto, uniformity_eq_comap_nhds_zero, tendsto_comap_iff]
  apply ((schwartz_withSeminorms ℂ E ℂ).tendsto_nhds _ _).mpr
  intro i ε hε
  let p : Seminorm ℂ 𝓢(E, ℂ) := SchwartzMap.seminorm ℂ i.1 i.2
  let u (n : ℕ) := ∑ j ∈ Finset.range n, f j
  let v (n : ℕ) := ∑ j ∈ Finset.range n, p (f j)
  have hc : CauchySeq v := (hs i.1 i.2).hasSum.tendsto_sum_nat.cauchySeq
  have hd := (cauchySeq_iff_tendsto_dist_atTop_0.mp hc).eventually (gt_mem_nhds hε)
  have hsum (T : Finset ℕ) : p (∑ j ∈ T, f j) ≤ ∑ j ∈ T, p (f j) := by
    induction T using Finset.induction_on with
    | empty => simp
    | insert j T hj ih =>
      rw [Finset.sum_insert hj, Finset.sum_insert hj]
      exact (map_add_le_add p _ _).trans (add_le_add le_rfl ih)
  have hle (a b : ℕ) (hab : a ≤ b) : p (u b - u a) ≤ dist (v a) (v b) := by
    change p ((∑ j ∈ Finset.range b, f j) - ∑ j ∈ Finset.range a, f j) ≤ dist (v a) (v b)
    rw [← Finset.sum_Ico_eq_sub f hab, dist_comm, Real.dist_eq]
    calc
      _ ≤ ∑ j ∈ Finset.Ico a b, p (f j) := hsum _
      _ = v b - v a := Finset.sum_Ico_eq_sub (fun j ↦ p (f j)) hab
      _ ≤ _ := le_abs_self _
  filter_upwards [hd] with z hz
  change p (u z.2 - u z.1 - 0) < ε
  rw [sub_zero]
  rcases le_total z.1 z.2 with h | h
  · exact (hle _ _ h).trans_lt hz
  · rw [map_sub_rev p]
    apply (hle _ _ h).trans_lt
    exact lt_of_le_of_lt (le_of_eq (dist_comm _ _)) hz

end Masullo

end
