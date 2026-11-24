import VectorContourHolomorphy
import RemovableWeakSingularities
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
Strong complex differentiation and contour integrals in quasi-complete spaces.
Adapted from Apache-2.0 RiemannMasullo commit 4f78774.
-/

open Bornology Filter Function Set Topology
open scoped ContDiff ENNReal

namespace Masullo

noncomputable section

variable {E : Type*} [AddCommGroup E] [Module ℂ E] [UniformSpace E]
  [IsUniformAddGroup E] [ContinuousSMul ℂ E]
variable {U : Set ℂ} {f : ℂ → E}

abbrev WeaklyHolomorphicOn (f : ℂ → E) (U : Set ℂ) : Prop :=
  ∀ ℓ : StrongDual ℂ E, DifferentiableOn ℂ (ℓ ∘ f) U

omit [IsUniformAddGroup E] in
/-- Paper: (C.5.2.1), p. 737. On an open set, holomorphy means the complex
difference quotients have a limit in the target at every point. -/
theorem vectorHolomorphicOn_iff_tendsto (hU : IsOpen U) [IsTopologicalAddGroup E]
    (f : ℂ → E) :
    DifferentiableOn ℂ f U ↔ ∀ z ∈ U, ∃ v : E,
      Tendsto (fun w ↦ (w - z)⁻¹ • (f w - f z)) (𝓝[≠] z) (𝓝 v) := by
  have slope_iff (z : ℂ) (v : E) : HasDerivAt f v z ↔
      Tendsto (fun w ↦ (w - z)⁻¹ • (f w - f z)) (𝓝[≠] z) (𝓝 v) := by
    rw [hasDerivAt_iff_hasFDerivAt, ← hasFDerivWithinAt_univ,
      ← hasFDerivWithinAt_sdiff_singleton_self, ← Set.compl_eq_univ_sdiff,
      hasFDerivWithinAt_iff_isLittleOTVS]
    change (fun w ↦ f w - f z - (w - z) • v) =o[ℂ; 𝓝[≠] z] (fun w ↦ w - z) ↔ _
    rw [Asymptotics.isLittleOTVS_iff_tendsto_inv_smul (by
      filter_upwards with w hw
      simp [sub_eq_zero.mp hw])]
    conv_rhs => rw [← tendsto_sub_nhds_zero_iff]
    apply tendsto_congr'
    filter_upwards [eventually_mem_nhdsWithin] with w hw
    simp [smul_sub, inv_smul_smul₀ (sub_ne_zero.mpr hw)]
  constructor
  · intro hf z hz
    obtain ⟨L, hL⟩ := hf z hz
    exact ⟨L 1, (slope_iff z _).mp (hL.hasFDerivAt (hU.mem_nhds hz)).hasDerivAt⟩
  · intro hf z hz
    obtain ⟨v, hv⟩ := hf z hz
    exact ⟨_, ((slope_iff z v).mpr hv).hasFDerivAt.hasFDerivWithinAt⟩

omit [IsUniformAddGroup E] [ContinuousSMul ℂ E] in
/-- A continuous linear map sends the derivative of a vector-valued holomorphic
function to the derivative of the composite. -/
theorem vectorHolomorphic_hasDerivAt_comp
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] {f : ℂ → E}
    (hf : DifferentiableOn ℂ f U) (hU : IsOpen U) (j : E →L[ℂ] F) (x : U) :
    HasDerivAt (j ∘ f) (j (deriv f x)) (x : ℂ) := by
  have h := hf.hasFDerivAt (hU.mem_nhds x.property)
  have hj : HasFDerivAt (j ∘ f) (j.comp (fderiv ℂ f x)) (x : ℂ) := by
    apply HasFDerivAt.of_isLittleOTVS
    simpa only [Function.comp_def, ContinuousLinearMap.comp_apply, map_sub]
      using j.isBigOTVS_comp.trans_isLittleOTVS h.isLittleOTVS
  exact hj.hasDerivAt

variable [T2Space E] [PolynormableSpace ℂ E] [QuasiCompleteSpace ℂ E]

/-- The scalar holomorphy tests give strong complex differentiability in a
Hausdorff quasi-complete locally convex space. -/
theorem differentiableOn_of_weaklyHolomorphicOn (hU : IsOpen U)
    (hf : WeaklyHolomorphicOn f U) : DifferentiableOn ℂ f U := by
  letI : Module ℝ E := Module.restrictScalars ℝ ℂ E
  letI : IsScalarTower ℝ ℂ E := IsScalarTower.restrictScalars ℝ ℂ E
  apply (vectorHolomorphicOn_iff_tendsto hU f).mpr
  intro z hz
  let q := slope f z
  let g (ℓ : StrongDual ℂ E) := dslope (ℓ ∘ f) z
  have hg (ℓ : StrongDual ℂ E) : DifferentiableOn ℂ (g ℓ) U :=
    (Complex.differentiableOn_dslope (hU.mem_nhds hz)).mpr (hf ℓ)
  have hcompare (ℓ : StrongDual ℂ E) : EqOn (fun w ↦ ℓ (q w)) (g ℓ) (U \ {z}) := by
    intro w hw
    dsimp [g]
    rw [dslope_of_ne _ hw.2]
    exact (ℓ.toLinearMap.slope_comp f z w).symm
  obtain ⟨Q, hQ, hEq, _, _, _, _⟩ := removable_weak_singularity hU hz q g
    (fun ℓ ↦ deriv (g ℓ)) hcompare
    (fun ℓ w hw ↦ ((hg ℓ).differentiableAt (hU.mem_nhds hw)).hasDerivAt)
    (fun ℓ ↦ ((hg ℓ).deriv hU).continuousOn)
  refine ⟨Q z, ?_⟩
  have hlim := (hQ.continuousAt (hU.mem_nhds hz)).tendsto.mono_left
    (show 𝓝[≠] z ≤ 𝓝 z from nhdsWithin_le_nhds)
  apply hlim.congr'
  filter_upwards [mem_nhdsWithin_of_mem_nhds (hU.mem_nhds hz), self_mem_nhdsWithin]
    with w hw hwne
  exact hEq ⟨hw, hwne⟩

/-- Paper: Theorem C.5.2.6(1,3), p. 738. Weak holomorphy is equivalent to the
existence of complex derivatives in the original target of every order. -/
theorem weaklyHolomorphicOn_iff_all_derivatives (hU : IsOpen U) :
    WeaklyHolomorphicOn f U ↔ ∀ k : ℕ, DifferentiableOn ℂ (deriv^[k] f) U := by
  constructor
  · intro hf k
    apply differentiableOn_of_weaklyHolomorphicOn hU
    induction k with
    | zero => exact hf
    | succ k ih =>
        rw [Function.iterate_succ_apply']
        intro φ
        refine ((ih φ).deriv hU).congr fun z hz ↦ ?_
        exact (vectorHolomorphic_hasDerivAt_comp
          (differentiableOn_of_weaklyHolomorphicOn hU ih) hU φ ⟨z, hz⟩).deriv.symm
  · intro hf φ z hz
    exact (vectorHolomorphic_hasDerivAt_comp (f := f) (hf 0) hU φ
      ⟨z, hz⟩).differentiableAt.differentiableWithinAt

omit [T2Space E] [PolynormableSpace ℂ E] [QuasiCompleteSpace ℂ E] in
theorem eval_iteratedDeriv_eq (hU : IsOpen U)
    (hf : ∀ k : ℕ, DifferentiableOn ℂ (deriv^[k] f) U) (φ : StrongDual ℂ E) (n : ℕ) :
      EqOn (iteratedDeriv n (φ ∘ f)) (φ ∘ deriv^[n] f) U := by
  induction n with
  | zero => exact fun _ _ ↦ rfl
  | succ n ih =>
    intro w hw
    rw [iteratedDeriv_succ, (ih.eventuallyEq_of_mem (hU.mem_nhds hw)).deriv_eq]
    simpa only [Function.comp_apply, Function.iterate_succ_apply'] using
      (vectorHolomorphic_hasDerivAt_comp (hf n) hU φ ⟨w, hw⟩).deriv

/-- Paper: (C.5.2.4), p. 738. The higher derivatives are given by Pettis
contour integrals with the Cauchy kernel and the factorial factor. -/
theorem hasPettisIntegral_cauchy_derivative (hU : IsOpen U)
    (hf : ∀ k : ℕ, DifferentiableOn ℂ (deriv^[k] f) U)
    (γ : PositiveSimpleContour) (htrace : γ.val.trace ⊆ U) (hinterior : γ.interior ⊆ U)
    {z : ℂ} (hz : z ∈ γ.interior) (k : ℕ) :
    HasPettisIntegral γ.val.measure (fun w ↦ ((w - z) ^ (k + 1))⁻¹ • f w)
      ((2 * (Real.pi : ℂ) * Complex.I / (k.factorial : ℂ)) • (deriv^[k] f) z) := by
  have hhol (φ : StrongDual ℂ E) : DifferentiableOn ℂ (φ ∘ f) U := fun w hw ↦
    (vectorHolomorphic_hasDerivAt_comp (hf 0) hU φ ⟨w, hw⟩).differentiableAt.differentiableWithinAt
  have hscalar (φ : StrongDual ℂ E) :=
    γ.scalarIntegral_cauchy_derivative hU htrace hinterior (hhol φ) hz k
  intro φ
  refine ⟨?_, ?_⟩
  · change MeasureTheory.Integrable (fun w ↦ φ (((w - z) ^ (k + 1))⁻¹ • f w))
      γ.val.measure.variation
    simpa only [map_smul, smul_eq_mul, Function.comp_apply] using (hscalar φ).1
  · change φ ((2 * (Real.pi : ℂ) * Complex.I / (k.factorial : ℂ)) • (deriv^[k] f) z) =
      complexMeasureIntegral γ.val.measure
        (fun w ↦ φ (((w - z) ^ (k + 1))⁻¹ • f w))
    simp only [map_smul, smul_eq_mul]
    have h := (hscalar φ).2
    rw [eval_iteratedDeriv_eq hU hf φ k (hinterior hz)] at h
    exact h.symm

omit [ContinuousSMul ℂ E] [T2Space E] [QuasiCompleteSpace ℂ E] in
/-- Uniform convergence in a polynormable space is seminorm-smallness of the difference. -/
theorem tendstoUniformlyOn_of_forall_continuous_seminorm
    {ι : Type*} {l : Filter ι} {F : ι → ℂ → E} {g : ℂ → E} {s : Set ℂ}
    (h : ∀ q : Seminorm ℂ E, Continuous q → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ i in l, ∀ x ∈ s, q (F i x - g x) < ε) :
    TendstoUniformlyOn F g l s := by
  have hbasis := (PolynormableSpace.withSeminorms ℂ E).hasBasis_zero_ball.uniformity_of_nhds_zero
  rw [hbasis.tendstoUniformlyOn_iff_of_uniformity]
  intro p hp
  let q : Seminorm ℂ E := p.1.sup (fun i : {p : Seminorm ℂ E // Continuous p} ↦ i.val)
  have hq : Continuous q := Seminorm.continuous_finsetSup fun i _ ↦ i.property
  filter_upwards [h q hq p.2 hp] with i hi x hx
  simpa [Seminorm.mem_ball_zero, q] using hi x hx

omit [IsUniformAddGroup E] [ContinuousSMul ℂ E] [T2Space E] [QuasiCompleteSpace ℂ E] in
/-- The Taylor errors on a closed subdisc remain bounded even after multiplication
by the truncation index: this can be tested on each functional separately. -/
private theorem bounded_taylorErrors (hU : IsOpen U) (hf : WeaklyHolomorphicOn f U)
    {z : ℂ} {a : ℕ → E}
    (ha : ∀ (φ : StrongDual ℂ E) k, φ (a k) = iteratedDeriv k (φ ∘ f) z / k.factorial)
    {r : ℝ} (hr : 0 < r) (hs : Metric.closedBall z r ⊆ U) :
    IsVonNBounded ℂ (range fun x : ℕ × Metric.closedBall z r ↦ (x.1 : ℂ) •
      ((∑ k ∈ Finset.range x.1, ((x.2 : ℂ) - z) ^ k • a k) - f x.2)) := by
  obtain ⟨δ, hδ, hlarge⟩ := (isCompact_closedBall z r).exists_cthickening_subset_open hU hs
  rw [cthickening_closedBall hδ.le hr.le] at hlarge
  let R : NNReal := ⟨δ + r, by positivity⟩
  let ρ : NNReal := ⟨δ / 2 + r, by positivity⟩
  have hρ : ρ < R := by change δ / 2 + r < δ + r; linarith
  apply (isVonNBounded_iff_dual_images _).mpr
  intro φ
  apply isBounded_iff_forall_norm_le.mpr
  have hd : DifferentiableOn ℂ (φ ∘ f) (Metric.closedBall z R) := (hf φ).mono hlarge
  have hps := hd.hasFPowerSeriesOnBall (show 0 < R by change 0 < δ + r; positivity)
  rw [hps.hasFPowerSeriesAt.eq_formalMultilinearSeries hps.analyticAt.hasFPowerSeriesAt] at hps
  obtain ⟨t, ht, C, hC, hest⟩ := hps.uniform_geometric_approx (ENNReal.coe_lt_coe.mpr hρ)
  obtain ⟨M, hM⟩ := (tendsto_self_mul_const_pow_of_lt_one ht.1.le ht.2).bddAbove_range
  refine ⟨C * M, ?_⟩
  rintro _ ⟨_, ⟨⟨n, w⟩, rfl⟩, rfl⟩
  have hw : (w : ℂ) - z ∈ Metric.ball 0 ρ := by
    rw [Metric.mem_ball, dist_zero_right]
    have hle := Metric.mem_closedBall.mp w.property
    rw [dist_eq_norm] at hle
    change _ < δ / 2 + r
    linarith
  have he := hest _ hw n
  simp only [add_sub_cancel, FormalMultilinearSeries.partialSum,
    FormalMultilinearSeries.ofScalars_apply_eq, comp_apply, smul_eq_mul] at he
  simp only [map_smul, map_sub, map_sum, ha, smul_eq_mul, norm_mul, Complex.norm_natCast]
  rw [norm_sub_rev]
  calc
    _ ≤ (n : ℝ) * (C * t ^ n) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg n)
      simpa only [mul_comm] using he
    _ = C * ((n : ℝ) * t ^ n) := by ring
    _ ≤ C * M := mul_le_mul_of_nonneg_left (hM (mem_range_self n)) hC.le

omit [IsUniformAddGroup E] [ContinuousSMul ℂ E] [T2Space E]
  [PolynormableSpace ℂ E] [QuasiCompleteSpace ℂ E] in
/-- Theorem C.5.2.6(1–2). Weak holomorphy is equivalent to scalar complex
differentiability of all iterated derivatives. -/
theorem weaklyHolomorphicOn_iff_all_scalar_derivatives (hU : IsOpen U) :
    WeaklyHolomorphicOn f U ↔ ∀ (ℓ : StrongDual ℂ E) (k : ℕ),
      DifferentiableOn ℂ (iteratedDeriv k (ℓ ∘ f)) U := by
  constructor
  · intro hf ℓ k
    induction k with
    | zero => simpa using hf ℓ
    | succ k ih => rw [iteratedDeriv_succ]; exact ih.deriv hU
  · intro h ℓ
    simpa using h ℓ 0

/-- Theorem C.5.2.6(4). The Taylor series with the actual vector derivatives
as factorial-normalized coefficients converges uniformly on each closed
disc about its center contained in the domain. -/
theorem tendstoUniformlyOn_taylor_of_weaklyHolomorphic (hU : IsOpen U)
    (hf : WeaklyHolomorphicOn f U) {z : ℂ} (hz : z ∈ U)
    {r : ℝ} (hr : 0 < r) (hs : Metric.closedBall z r ⊆ U) :
    TendstoUniformlyOn
      (fun n w ↦ ∑ k ∈ Finset.range n, (w - z) ^ k •
        ((k.factorial : ℂ)⁻¹ • (deriv^[k] f) z)) f atTop (Metric.closedBall z r) := by
  let a (k : ℕ) : E := (k.factorial : ℂ)⁻¹ • (deriv^[k] f) z
  change TendstoUniformlyOn
    (fun n w ↦ ∑ k ∈ Finset.range n, (w - z) ^ k • a k) f atTop (Metric.closedBall z r)
  have hderiv := (weaklyHolomorphicOn_iff_all_derivatives hU).mp hf
  have ha (φ : StrongDual ℂ E) (k : ℕ) : φ (a k) = iteratedDeriv k (φ ∘ f) z / k.factorial := by
    simp only [a, map_smul, smul_eq_mul, div_eq_inv_mul]
    exact congrArg ((k.factorial : ℂ)⁻¹ * ·) (eval_iteratedDeriv_eq hU hderiv φ k hz).symm
  have hb := bounded_taylorErrors hU hf ha hr hs
  apply tendstoUniformlyOn_of_forall_continuous_seminorm
  intro q hq ε hε
  obtain ⟨M, hM⟩ := (PolynormableSpace.withSeminorms ℂ E).isVonNBounded_iff_seminorm_bddAbove.mp
    hb ⟨q, hq⟩
  filter_upwards [tendsto_natCast_atTop_atTop.eventually_gt_atTop (M / ε),
    eventually_gt_atTop 0] with n hn hn₀ w hw
  have h := hM (mem_image_of_mem _ (mem_range_self (n, ⟨w, hw⟩)))
  change q ((n : ℂ) • _) ≤ M at h
  rw [map_smul_eq_mul, Complex.norm_natCast] at h
  exact lt_of_mul_lt_mul_left (h.trans_lt ((div_lt_iff₀ hε).mp hn)) (by positivity)

/-- Paper: Theorem C.5.2.6(1,4), p. 738. Weak holomorphy is equivalent to a
power series at every center that converges uniformly to the function on each closed
disc about that center contained in the domain. -/
theorem weaklyHolomorphicOn_iff_taylor (hU : IsOpen U) :
    WeaklyHolomorphicOn f U ↔ ∀ z ∈ U, ∃ a : ℕ → E,
      ∀ r : ℝ, 0 < r → Metric.closedBall z r ⊆ U →
        TendstoUniformlyOn (fun n w ↦ ∑ k ∈ Finset.range n, (w - z) ^ k • a k)
          f atTop (Metric.closedBall z r) := by
  classical
  constructor
  · intro hf z hz
    exact ⟨fun k ↦ (k.factorial : ℂ)⁻¹ • (deriv^[k] f) z,
      fun _ hr hs ↦ tendstoUniformlyOn_taylor_of_weaklyHolomorphic hU hf hz hr hs⟩
  · intro h φ z hz
    obtain ⟨a, ha⟩ := h z hz
    obtain ⟨r, hr, hs⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hz)
    have hlim : TendstoUniformlyOn
        (fun n w ↦ ∑ k ∈ Finset.range n, (w - z) ^ k * φ (a k)) (φ ∘ f) atTop
        (Metric.closedBall z r) := by
      have hseries n :
          φ ∘ (fun w ↦ ∑ k ∈ Finset.range n, (w - z) ^ k • a k) =
            (fun w ↦ ∑ k ∈ Finset.range n, (w - z) ^ k * φ (a k)) := by
        funext w
        simp only [Function.comp_apply, map_sum, map_smul, smul_eq_mul]
      simpa only [hseries] using φ.uniformContinuous.comp_tendstoUniformlyOn (ha r hr hs)
    have hd := (hlim.mono Metric.ball_subset_closedBall).tendstoLocallyUniformlyOn.differentiableOn
      (Eventually.of_forall fun n ↦ (Differentiable.fun_sum fun i _ ↦
        ((differentiable_id.sub_const z).pow i).mul_const (φ (a i))).differentiableOn) Metric.isOpen_ball
    exact (hd.differentiableAt (Metric.ball_mem_nhds z hr)).differentiableWithinAt

end

end Masullo
