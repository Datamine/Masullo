import CompactCharacterCompleteness

open Filter Function MeasureTheory Set Topology

namespace Masullo

noncomputable section

variable {K : Type*} [CommGroup K] [TopologicalSpace K] [IsTopologicalGroup K]
  [T2Space K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]

private def continuousKernelCharacter : PontryaginDual K →* C(K, ℂ) where
  toFun χ := ⟨fun k => (χ k : ℂ), continuous_subtype_val.comp χ.continuous⟩
  map_one' := by ext k; simp
  map_mul' χ ψ := by ext k; exact Circle.coe_mul _ _

/-- Compact-group approximate identities can be chosen as finite character
sums with exact mass one and arbitrarily small L¹ error relative to a
nonnegative unit-mass test supported in a prescribed neighborhood. -/
theorem exists_kernelCharacter_approximation (κ : Measure K) [IsProbabilityMeasure κ]
    [κ.IsOpenPosMeasure] {U : Set K} (hU : IsOpen U) (h1 : (1 : K) ∈ U)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ c : PontryaginDual K →₀ ℂ,
      let q (x : K) := c.sum (fun χ a => a * (χ x : ℂ))
      (∫ x, q x ∂κ) = 1 ∧ (∫ x, ‖q x‖ ∂κ) < 1 + ε ∧
      (∫ x in Uᶜ, ‖q x‖ ∂κ) < ε := by
  classical
  obtain ⟨bump, hb1, hb0, hbK, hb⟩ := exists_continuous_one_zero_of_isCompact
    (s := ({1} : Set K)) isCompact_singleton hU.isClosed_compl
    (disjoint_compl_right_iff_subset.mpr (singleton_subset_iff.mpr h1))
  let a := ∫ x, bump x ∂κ
  have ha : 0 < a := bump.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    hbK (fun x => (hb x).1) (show bump 1 ≠ 0 by rw [hb1 (mem_singleton _)]; norm_num)
  let f : C(K, ℂ) := ⟨fun x => ((a⁻¹ * bump x : ℝ) : ℂ),
    Complex.continuous_ofReal.comp (continuous_const.mul bump.continuous)⟩
  have hfI : (∫ x, a⁻¹ * bump x ∂κ) = 1 := by rw [integral_const_mul, inv_mul_cancel₀ ha.ne']
  have hfm : (∫ x, f x ∂κ) = 1 := by
    change (∫ x, ((a⁻¹ * bump x : ℝ) : ℂ) ∂κ) = 1
    rw [integral_complex_ofReal, hfI, Complex.ofReal_one]
  have hfn : (∫ x, ‖f x‖ ∂κ) = 1 := by
    change (∫ x, ‖((a⁻¹ * bump x : ℝ) : ℂ)‖ ∂κ) = 1
    simpa only [Complex.norm_real, Real.norm_of_nonneg (mul_nonneg (inv_nonneg.mpr ha.le) (hb _).1)] using hfI
  let r : PontryaginDual K →* C(K, ℂ) := continuousKernelCharacter
  let W := Submodule.span ℂ (range r)
  have hd : f ∈ closure (W : Set C(K, ℂ)) := by
    rw [← Submodule.topologicalClosure_coe, dense_span_pontryaginDual r (fun _ _ => rfl)]
    exact Submodule.mem_top
  obtain ⟨p, hp, hpd⟩ := Metric.mem_closure_iff.mp hd (ε / 3) (by positivity)
  have hpoint (x : K) : ‖p x - f x‖ ≤ ε / 3 := by
    rw [← dist_eq_norm]
    rw [dist_comm] at hpd
    exact (ContinuousMap.dist_apply_le_dist (f := p) (g := f) x).trans_lt hpd |>.le
  have hInt (g : C(K, ℂ)) : Integrable g κ :=
    g.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let d := 1 - ∫ x, p x ∂κ
  have hdn : ‖d‖ ≤ ε / 3 := by
    rw [show d = ∫ x, f x - p x ∂κ by rw [integral_sub (hInt f) (hInt p), hfm]]
    simpa [Measure.real] using (norm_integral_le_of_norm_le_const (μ := κ)
      (f := fun x => f x - p x) (.of_forall fun x => by rw [norm_sub_rev]; exact hpoint x))
  let q : C(K, ℂ) := p + d • 1
  have hqW : q ∈ W := W.add_mem hp (W.smul_mem d (Submodule.subset_span ⟨1, map_one r⟩))
  have hq (x : K) : q x = p x + d := by simp [q, smul_eq_mul]
  have hqm : (∫ x, q x ∂κ) = 1 := by
    simp_rw [hq]
    rw [integral_add (hInt p) (integrable_const _), integral_const]
    simp [d, Measure.real]
  have hqdiff (x : K) : ‖q x - f x‖ ≤ 2 * (ε / 3) := by
    rw [hq]
    rw [show p x + d - f x = (p x - f x) + d by ring, two_mul]
    exact (norm_add_le _ _).trans (add_le_add (hpoint x) hdn)
  have hqnorm : (∫ x, ‖q x‖ ∂κ) < 1 + ε := by
    calc
      (∫ x, ‖q x‖ ∂κ) ≤ ∫ x, 2 * (ε / 3) + ‖f x‖ ∂κ := by
        apply integral_mono (hInt q).norm ((integrable_const _).add (hInt f).norm)
        intro x
        have h := (norm_add_le (q x - f x) (f x)).trans (add_le_add_left (hqdiff x) _)
        rwa [sub_add_cancel] at h
      _ = 2 * (ε / 3) + 1 := by
        rw [integral_add (integrable_const _) (hInt f).norm, hfn, integral_const]
        simp [Measure.real]
      _ < _ := by linarith
  have hqtail : (∫ x in Uᶜ, ‖q x‖ ∂κ) < ε := by
    have hle : (∫ x in Uᶜ, ‖q x‖ ∂κ) ≤ ∫ _x in Uᶜ, 2 * (ε / 3) ∂κ := by
      apply integral_mono_ae (hInt q).norm.restrict (integrable_const _)
      filter_upwards [ae_restrict_mem hU.measurableSet.compl] with x hx
      simpa [show f x = 0 by change ((a⁻¹ * bump x : ℝ) : ℂ) = 0; rw [hb0 hx]; simp] using hqdiff x
    refine hle.trans_lt ((setIntegral_le_integral (integrable_const _) (.of_forall fun _ => by positivity)).trans_lt ?_)
    rw [integral_const]
    simp only [Measure.real, measure_univ, ENNReal.toReal_one, one_smul]
    linarith
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hqW
  have he (x : K) : q x = c.sum (fun χ a => a * (χ x : ℂ)) := by
    rw [← hc]
    simp only [Finsupp.sum, ContinuousMap.sum_apply, ContinuousMap.smul_apply, smul_eq_mul]
    rfl
  exact ⟨c, by simpa only [← he] using And.intro hqm (And.intro hqnorm hqtail)⟩

end

end Masullo
