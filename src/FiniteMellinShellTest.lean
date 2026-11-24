import SLocalPrincipalValueImage

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical NumberField

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]
variable (v : HeightOneSpectrum (𝓞 F))

private abbrev L := v.adicCompletion F

/-- Every finite unitary twist has an additive Schwartz–Bruhat test
supported on the unit shell whose continued Mellin transform is a
nonzero constant. -/
theorem exists_finiteMellinUnitTest
    [MeasurableSpace (L F v)ˣ] [BorelSpace (L F v)ˣ]
    (ν : Measure (L F v)ˣ) [ν.IsHaarMeasure] (χ : (L F v)ˣ →ₜ* Circle) :
    ∃ (f : locallyConstantTests (L F v)) (A : ℂ), f.val 0 = 0 ∧ A ≠ 0 ∧
      (∀ z : ℂ, 0 < z.re → finiteZetaIntegral F v ν χ f z = A) ∧
      ∀ c : ℂ, finiteZetaContinuation F v ν χ f =ᶠ[𝓝[≠] c] fun _ ↦ A := by
  let j : (L F v)ˣ → L F v := Units.val
  have hj : IsOpenEmbedding j := IsOpenUnits.isOpenEmbedding_unitsVal
  let O : Set (L F v)ˣ := {u | (1/2 : ℝ) < ((χ u : Circle) : ℂ).re}
  have hO : IsOpen O :=
    isOpen_lt continuous_const (Complex.continuous_re.comp (continuous_subtype_val.comp χ.continuous))
  have h1 : (1 : L F v) ∈ j '' O := by
    refine ⟨1, ?_, rfl⟩
    change (1/2 : ℝ) < ((χ 1 : Circle) : ℂ).re
    simp
    norm_num
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp ((hj.isOpenMap _ hO).mem_nhds h1)
  let t := min r 1
  have ht : 0 < t := lt_min hr zero_lt_one
  let B := Metric.ball (1 : L F v) t
  have hBA : B ⊆ j '' O := (Metric.ball_subset_ball (min_le_left _ _)).trans hsub
  have hB1 : B ⊆ Metric.ball (1 : L F v) 1 := Metric.ball_subset_ball (min_le_right _ _)
  have hK : IsCompact (Metric.closedBall (1 : L F v) 1) := by
    rw [IsUltrametricDist.closedBall_eq_of_mem
      (show (0 : L F v) ∈ Metric.closedBall (1 : L F v) 1 by simp), finiteCompletion_closedBall]
    exact finitePlaceIntegral_compact F v
  have hB : IsCompact B := hK.of_isClosed_subset (IsUltrametricDist.isClosed_ball _ _)
    (hB1.trans Metric.ball_subset_closedBall)
  have hB0 : (0 : L F v) ∉ B := fun h ↦ (by simp : (0 : L F v) ∉ Metric.ball 1 1) (hB1 h)
  let f := compactOpenIndicator (L F v) ⟨B, hB, Metric.isOpen_ball⟩
  let U := j ⁻¹' B
  have hUo : IsOpen U := Metric.isOpen_ball.preimage hj.continuous
  have hUk : IsCompact U := by
    apply hj.isEmbedding.isCompact_iff.mpr
    rw [image_preimage_eq_inter_range, inter_eq_left.mpr (hBA.trans (image_subset_range _ _))]
    exact hB
  have hU1 : (1 : (L F v)ˣ) ∈ U := Metric.mem_ball_self ht
  have hnorm (u : (L F v)ˣ) (hu : u ∈ U) : ‖u.val‖ = 1 := by
    have hsmall : dist u.val 1 < 1 := hB1 hu
    have hdist : dist (1 : L F v) 0 = 1 := by simp
    rw [← dist_zero_right, IsUltrametricDist.dist_eq_max_of_dist_ne_dist u.val 1 0
      (hsmall.ne.trans_eq hdist.symm), hdist, max_eq_right hsmall.le]
  let A := ∫ u in U, (χ u : ℂ) ∂ν
  have hint : IntegrableOn (fun u ↦ (χ u : ℂ)) U ν :=
    (continuous_subtype_val.comp χ.continuous).continuousOn.integrableOn_compact hUk
  have hRe : (ν.real U) / 2 ≤ A.re := by
    change _ ≤ (∫ u in U, (χ u : ℂ) ∂ν).re
    have hre : (∫ u in U, ((χ u : Circle) : ℂ).re ∂ν) = A.re := integral_re hint
    change _ ≤ A.re
    rw [← hre]
    have hc : IntegrableOn (fun _ : (L F v)ˣ ↦ (1/2 : ℝ)) U ν :=
      integrableOn_const (hUk.measure_lt_top.ne)
    have hiRe : IntegrableOn (fun u ↦ ((χ u : Circle) : ℂ).re) U ν := hint.re
    have hm := setIntegral_mono_on hc hiRe hUo.measurableSet (fun u hu ↦ by
      obtain ⟨w, hw, he⟩ := hBA hu
      have heq : w = u := hj.injective he
      exact le_of_lt (heq ▸ hw))
    rw [setIntegral_const] at hm
    simpa only [smul_eq_mul, div_eq_mul_inv, one_mul] using hm
  have hMass : 0 < ν.real U :=
    ENNReal.toReal_pos (hUo.measure_ne_zero ν ⟨1, hU1⟩) hUk.measure_lt_top.ne
  have hA : A ≠ 0 := fun ha ↦
    (div_pos hMass (by norm_num : (0 : ℝ) < 2)).not_ge (by simpa [ha] using hRe)
  have hf : f.val 0 = 0 := by
    change B.indicator (fun _ ↦ (1 : ℂ)) 0 = 0
    exact indicator_of_notMem hB0 _
  have hI (z : ℂ) : finiteZetaIntegral F v ν χ f z = A := by
    unfold finiteZetaIntegral
    have he (u : (L F v)ˣ) :
        f.val u.val * (χ u : ℂ) * finiteZetaWeight F v z u = U.indicator (fun w ↦ (χ w : ℂ)) u := by
      change B.indicator (fun _ ↦ (1 : ℂ)) u.val * (χ u : ℂ) * finiteZetaWeight F v z u =
        U.indicator (fun w ↦ (χ w : ℂ)) u
      by_cases hu : u ∈ U
      · have h := hnorm u hu
        rw [indicator_of_mem (show u.val ∈ B from hu), indicator_of_mem hu]
        simp [finiteZetaWeight, h]
      · rw [indicator_of_notMem (show u.val ∉ B from hu), indicator_of_notMem hu, zero_mul, zero_mul]
    simp_rw [he]
    exact integral_indicator hUo.measurableSet
  refine ⟨f, A, hf, hA, fun z _ ↦ hI z, fun c ↦ boundedPoleMellinSpace_unique_germs
    (isOpen_lt (continuous_const (y := (0 : ℝ))) Complex.continuous_re)
    ⟨1, by simp⟩ (meromorphicOn_univ.mp (finiteZetaContinuation_meromorphic F v ν χ f))
    (Meromorphic.const A) ?_ c⟩
  exact fun z hz ↦ (finiteZetaContinuation_eq_integral F v ν χ f z hz).2.symm.trans (hI z)

end

end Masullo
