import BruhatSobolevCompletion
import PhysicalMellinCutoffDiagram

open Filter Function MeasureTheory Set Topology UniformSpace
open scoped ENNReal TensorProduct

namespace Masullo

noncomputable section

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
  (m : G →ₜ* Multiplicative ℝ) [CompactSpace m.toMonoidHom.ker]
  (τ : Multiplicative ℝ →ₜ* G) (hτ : RightInverse τ m)
  (ν : Measure m.toMonoidHom.ker) [IsFiniteMeasure ν]

set_option maxHeartbeats 1400000 in
/-- Formula (9.2.1.19) for actual decay tests. The binomial sum of the
squared moments gives the chosen Hilbert norm. -/
theorem bruhatSobolevTest_norm_sq (b : ℝ) (N : ℕ) (f : ModulatedExponentialInductive m univ) :
    let μ := modulatedLogMeasure m τ hτ ν
    let moment (k : ℕ) g := ‖f.val g‖ ^ 2 *
      (Real.exp (2 * b * modulatedLog m g) * (modulatedLog m g ^ 2) ^ k)
    (∀ k ≤ N, Integrable (moment k) μ) ∧
    ‖bruhatSobolevInclusion m τ hτ ν b N f‖ ^ 2 =
      ∑ k ∈ Finset.range (N + 1), (N.choose k : ℝ) * ∫ g, moment k g ∂μ := by
  intro μ moment
  let W := modulatedSobolevMeasure m τ hτ ν b (2 * (N : ℝ))
  let U := bruhatSobolevInclusion m τ hτ ν b N f
  have hae : (U : G → ℂ) =ᵐ[W] f.val := bruhatSobolevInclusion_ae m τ hτ ν b N f
  have hf : MemLp f.val 2 W := (Lp.memLp U).ae_eq hae
  have hw : W = hardySobolevMeasure μ (modulatedLog m) b b (2 * (N : ℝ)) :=
    modulatedSobolevMeasure_eq_weighted m τ hτ ν b _
  have hF : MemLp f.val 2 (hardySobolevMeasure μ (modulatedLog m) b b (2 * (N : ℝ))) :=
    hw ▸ hf
  obtain ⟨hi, he⟩ := hardySobolev_even_norm_sq μ (l := modulatedLog m)
    ((continuous_toAdd.comp m.continuous).measurable : Measurable (modulatedLog m)) b N hF
  refine ⟨hi, ?_⟩
  change ‖U‖ ^ 2 = _
  refine Eq.trans (congrArg (fun r : ℝ ↦ r ^ 2) ?_) he
  rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae hae,
    eLpNorm_congr_ae hF.coeFn_toLp, hw]

set_option maxHeartbeats 1500000 in
/-- The weighted norm and the finite family of original moment norms
give exactly the same convergence on differences of tests. -/
theorem bruhatSobolevTest_moments_tendsto_iff (b : ℝ) (N : ℕ)
    {ι : Type*} {l : Filter ι} (f : ι → ModulatedExponentialInductive m univ) :
    let μ := modulatedLogMeasure m τ hτ ν
    let M (k : ℕ) (i : ι) := ∫ g, ‖(f i).val g‖ ^ 2 *
      (Real.exp (2 * b * modulatedLog m g) * (modulatedLog m g ^ 2) ^ k) ∂μ
    Tendsto (fun i ↦ ‖bruhatSobolevInclusion m τ hτ ν b N (f i)‖) l (𝓝 0) ↔
      ∀ k ≤ N, Tendsto (M k) l (𝓝 0) := by
  intro μ M
  let W (i : ι) := ‖bruhatSobolevInclusion m τ hτ ν b N (f i)‖
  have hnon (k : ℕ) (i : ι) : 0 ≤ M k i := integral_nonneg fun _ ↦ by positivity
  have hsum (i : ι) : W i ^ 2 = ∑ k ∈ Finset.range (N + 1), (N.choose k : ℝ) * M k i :=
    (bruhatSobolevTest_norm_sq m τ hτ ν b N (f i)).2
  change Tendsto W l (𝓝 0) ↔ _
  constructor
  · intro h k hk
    have hpow : Tendsto (fun i ↦ W i ^ 2) l (𝓝 0) := by simpa using h.pow 2
    refine squeeze_zero (hnon k) (fun i ↦ ?_) hpow
    rw [hsum]
    have hPos : (1 : ℝ) ≤ (N.choose k : ℝ) := by exact_mod_cast Nat.choose_pos hk
    exact (le_mul_of_one_le_left (hnon k i) hPos).trans
      (Finset.single_le_sum
        (fun j _ ↦ mul_nonneg (Nat.cast_nonneg _) (hnon j i))
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hk)))
  · intro h
    have hs : Tendsto (fun i ↦ ∑ k ∈ Finset.range (N + 1), (N.choose k : ℝ) * M k i)
        l (𝓝 0) := by
      have he := tendsto_finsetSum (Finset.range (N + 1))
        (fun k hk ↦ (h k (Nat.le_of_lt_succ (Finset.mem_range.mp hk))).const_mul (N.choose k : ℝ))
      simpa only [mul_zero, Finset.sum_const_zero] using he
    have hsqrt := hs.sqrt
    have hroot (i : ι) : Real.sqrt (W i ^ 2) = W i := Real.sqrt_sq (norm_nonneg _)
    simpa only [← hsum, hroot, Real.sqrt_zero] using hsqrt

set_option maxHeartbeats 1600000 in
/-- The supported Mellin tensor in Theorem 9.2.1.5(3) is exactly the
closure of the transformed original strict-support tests. -/
theorem bruhatSobolevMellin_cutoffClosure [ν.WeaklyRegular] (hm : IsProperMap m)
    (b : ℝ) (N : ℕ) {U : Set ℝ} (hU : IsOpen U) :
    closure (range (fun f : bruhatSobolevCutoffTests m U ↦
      modulatedGroupFullMellin m τ hτ ν b N (bruhatSobolevInclusion m τ hτ ν b N f.val))) =
      range (modulatedSupportedMellinEmbedding ν b N hU) := by
  let F := modulatedGroupFullMellin m τ hτ ν b N
  let M := modulatedGroupMellinEquiv m τ hτ ν b N hU
  let J := modulatedSupportedMellinEmbedding ν b N hU
  let I := bruhatSobolevCutoffInclusion m τ hτ ν b N U
  have hcomp (f : bruhatSobolevCutoffTests m U) :
      F (bruhatSobolevInclusion m τ hτ ν b N f.val) = J (M (I f)) :=
    (modulatedSupportedMellinEmbedding_commutes ν b N hU
      (modulatedGroupCutoffEquiv m τ hτ ν b (2 * (N : ℝ)) U (I f))).symm
  change closure (range (fun f : bruhatSobolevCutoffTests m U ↦ F
    (bruhatSobolevInclusion m τ hτ ν b N f.val))) = range J
  rw [show (fun f : bruhatSobolevCutoffTests m U ↦ F (bruhatSobolevInclusion m τ hτ ν b N f.val)) =
      J ∘ (M ∘ I) from funext hcomp, range_comp, J.isometry.isClosedEmbedding.closure_image_eq]
  have hd : DenseRange (M ∘ I) :=
    M.surjective.denseRange.comp (bruhatSobolevCutoff_dense m τ hτ ν hm b N hU) M.continuous
  rw [hd.closure_range, Set.image_univ]

end
end Masullo
