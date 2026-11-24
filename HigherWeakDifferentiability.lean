import RemovableWeakSingularities
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open Bornology Filter Function MeasureTheory Set Topology
open scoped ContDiff Interval ENat

namespace Masullo

noncomputable section

section ScalarSlopes

variable {𝕜 : Type*} [RCLike 𝕜] [NormedSpace 𝕜 ℂ]
  [IsScalarTower ℝ 𝕜 ℂ] [IsScalarTower 𝕜 ℂ ℂ]

omit [NormedSpace 𝕜 ℂ] [IsScalarTower ℝ 𝕜 ℂ] [IsScalarTower 𝕜 ℂ ℂ] in
private theorem norm_real_smul_mem_closedBall {r : ℝ} {h : 𝕜}
    (hh : h ∈ Metric.closedBall (0 : 𝕜) r) {t : ℝ} (ht : t ∈ Icc 0 1) :
    t • h ∈ Metric.closedBall (0 : 𝕜) r := by
  rw [Metric.mem_closedBall, dist_zero_right] at hh ⊢
  rw [norm_smul, Real.norm_of_nonneg ht.1]
  exact (mul_le_of_le_one_left (norm_nonneg h) ht.2).trans hh

omit [IsScalarTower 𝕜 ℂ ℂ] in
private theorem scalar_slope_eq_integral {u d : 𝕜 → ℂ} {r : ℝ}
    (hD : ∀ t ∈ Metric.closedBall (0 : 𝕜) r, HasDerivAt u (d t) t)
    (hd : ContinuousOn d (Metric.closedBall (0 : 𝕜) r))
    {h : 𝕜} (hh : h ∈ Metric.closedBall (0 : 𝕜) r) (hne : h ≠ 0) :
    h⁻¹ • (u h - u 0) = ∫ t in (0 : ℝ)..1, d (t • h) := by
  let q : ℝ →L[ℝ] 𝕜 := (ContinuousLinearMap.id ℝ ℝ).smulRight h
  have hq (t : ℝ) : q t = t • h := rfl
  have hdc : ContinuousOn (fun t : ℝ => d (t • h)) (Icc 0 1) :=
    hd.comp q.continuous.continuousOn (fun t ht => norm_real_smul_mem_closedBall hh ht)
  have hderiv (t : ℝ) (ht : t ∈ [[(0 : ℝ), 1]]) :
      HasDerivAt (fun t : ℝ => u (t • h)) (h • d (t • h)) t := by
    have ht' : t ∈ Icc 0 1 := by simpa only [uIcc_of_le zero_le_one] using ht
    have he := ((hD _ (norm_real_smul_mem_closedBall hh ht')).hasFDerivAt.restrictScalars ℝ)
    simpa [hq, Function.comp_def, ContinuousLinearMap.smulRight_apply, smul_eq_mul] using
      (he.comp t q.hasFDerivAt).hasDerivAt
  have hdI : IntervalIntegrable (fun t : ℝ => d (t • h)) volume 0 1 :=
    ContinuousOn.intervalIntegrable (by rwa [uIcc_of_le zero_le_one])
  have heI : IntervalIntegrable (fun t : ℝ => h • d (t • h)) volume 0 1 := hdI.smul h
  have H := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv heI
  rw [one_smul, zero_smul, intervalIntegral.integral_smul] at H
  rw [← H, smul_smul, inv_mul_cancel₀ hne, one_smul]

omit [IsScalarTower 𝕜 ℂ ℂ] in
private theorem scalar_slopes_lipschitz {u : 𝕜 → ℂ} {U : Set 𝕜} (hU : IsOpen U)
    (hu : ContDiffOn 𝕜 2 u U) {r : ℝ} (hK : Metric.closedBall (0 : 𝕜) r ⊆ U) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Metric.closedBall (0 : 𝕜) r, x ≠ 0 →
      ∀ y ∈ Metric.closedBall (0 : 𝕜) r, y ≠ 0 →
      ‖y⁻¹ • (u y - u 0) - x⁻¹ • (u x - u 0)‖ ≤ C * ‖y - x‖ := by
  let K := Metric.closedBall (0 : 𝕜) r
  let d := deriv u
  have hd : ContDiffOn 𝕜 1 d U := hu.deriv_of_isOpen hU le_rfl
  have hdd : ContinuousOn (deriv d) U :=
    (hd.deriv_of_isOpen (m := 0) hU le_rfl).continuousOn
  have hdu (x : 𝕜) (hx : x ∈ K) : HasDerivAt u (d x) x :=
    ((hu.differentiableOn (by decide) x (hK hx)).differentiableAt
      (hU.mem_nhds (hK hx))).hasDerivAt
  have hderiv (x : 𝕜) (hx : x ∈ K) : HasDerivAt d (deriv d x) x :=
    ((hd.differentiableOn (by decide) x (hK hx)).differentiableAt
      (hU.mem_nhds (hK hx))).hasDerivAt
  obtain ⟨M, hM⟩ := ((isCompact_closedBall (0 : 𝕜) r).image_of_continuousOn
    (hdd.mono hK)).exists_bound_of_continuousOn continuousOn_id
  let C := max M 0
  have hC : 0 ≤ C := le_max_right _ _
  have hLip (x : 𝕜) (hx : x ∈ K) (y : 𝕜) (hy : y ∈ K) : ‖d y - d x‖ ≤ C * ‖y - x‖ :=
    (convex_closedBall (0 : 𝕜) r).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun z hz => (hderiv z hz).hasDerivWithinAt)
      (fun z hz => (hM _ (mem_image_of_mem _ hz)).trans (le_max_left _ _)) hx hy
  refine ⟨C, hC, fun x hx hxn y hy hyn => ?_⟩
  have hcont := hd.continuousOn.mono hK
  rw [scalar_slope_eq_integral hdu hcont hx hxn, scalar_slope_eq_integral hdu hcont hy hyn]
  have hint (h : 𝕜) (hh : h ∈ K) :
      IntervalIntegrable (fun t : ℝ => d (t • h)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le zero_le_one]
    exact hcont.comp (continuous_id.smul continuous_const).continuousOn
      (fun t ht => norm_real_smul_mem_closedBall hh ht)
  rw [← intervalIntegral.integral_sub (hint y hy) (hint x hx)]
  have hbound (t : ℝ) (ht : t ∈ Ι (0 : ℝ) 1) :
      ‖d (t • y) - d (t • x)‖ ≤ C * ‖y - x‖ := by
    have ht' : t ∈ Icc 0 1 := by
      rw [uIoc_of_le zero_le_one] at ht
      exact Ioc_subset_Icc_self ht
    refine (hLip _ (norm_real_smul_mem_closedBall hx ht') _
      (norm_real_smul_mem_closedBall hy ht')).trans ?_
    rw [← smul_sub, norm_smul, Real.norm_of_nonneg ht'.1]
    exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_left (norm_nonneg _) ht'.2) hC
  simpa using intervalIntegral.norm_integral_le_of_norm_le_const hbound

end ScalarSlopes

section VectorSlopes

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedSpace 𝕜 ℂ]
  [IsScalarTower ℝ 𝕜 ℂ] [IsScalarTower 𝕜 ℂ ℂ]
  [AddCommGroup E] [Module ℂ E] [Module ℝ E] [IsScalarTower ℝ ℂ E]
  [Module 𝕜 E] [IsScalarTower 𝕜 ℂ E]
  [UniformSpace E] [IsUniformAddGroup E] [T2Space E] [ContinuousSMul ℂ E]
  [PolynormableSpace ℂ E] [QuasiCompleteSpace ℂ E]

private theorem weakly_C2_slope_limit {U : Set 𝕜} (hU : IsOpen U) (h0 : 0 ∈ U)
    (f : 𝕜 → E) (hf : ∀ ℓ : StrongDual ℂ E, ContDiffOn 𝕜 2 (fun t => ℓ (f t)) U) :
    ∃ d : E, ∀ ℓ : StrongDual ℂ E, HasDerivAt (fun t => ℓ (f t)) (ℓ d) 0 := by
  obtain ⟨r, hr, hK⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds h0)
  let K := Metric.closedBall (0 : 𝕜) r
  let S := K \ {0}
  let F (t : 𝕜) := t⁻¹ • (f t - f 0)
  have hEval (ℓ : StrongDual ℂ E) (t : 𝕜) : ℓ (F t) = t⁻¹ • (ℓ (f t) - ℓ (f 0)) := by
    change (ℓ.restrictScalars 𝕜) (t⁻¹ • (f t - f 0)) = _
    rw [map_smul, map_sub]
    rfl
  have hscalar (ℓ : StrongDual ℂ E) :
      ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ S, ∀ y ∈ S, ‖ℓ (F y) - ℓ (F x)‖ ≤ C * ‖y - x‖ := by
    obtain ⟨C, hC, h⟩ := scalar_slopes_lipschitz hU (hf ℓ) hK
    refine ⟨C, hC, fun x hx y hy => ?_⟩
    have hne (z : 𝕜) (hz : z ∈ S) : z ≠ 0 := fun h => hz.2 (mem_singleton_iff.mpr h)
    simpa only [hEval] using h x hx.1 (hne x hx) y hy.1
      (hne y hy)
  have hR : IsVonNBounded ℂ
      {w : E | ∃ x ∈ S, ∃ y ∈ S, w = ‖y - x‖⁻¹ • (F y - F x)} := by
    apply (isVonNBounded_iff_dual_images _).mpr
    intro ℓ
    obtain ⟨C, hC, h⟩ := hscalar ℓ
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨C, ?_⟩
    rintro z ⟨_, ⟨x, hx, y, hy, rfl⟩, rfl⟩
    have hl := h x hx y hy
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ), map_smul, map_sub, norm_smul,
      RCLike.norm_ofReal, abs_of_nonneg (by positivity)]
    by_cases he : y - x = 0
    · simpa [he] using hC
    · exact (mul_le_mul_of_nonneg_left hl (by positivity)).trans_eq (by
        rw [mul_comm C, ← mul_assoc, inv_mul_cancel₀ (norm_ne_zero_iff.mpr he), one_mul])
  have hC := cauchy_map_of_local_bounded_slopes F 0 hr hR
  have hB : IsVonNBounded ℂ (F '' S) := by
    apply (isVonNBounded_iff_dual_images _).mpr
    intro ℓ
    obtain ⟨C, hC, h⟩ := hscalar ℓ
    apply isBounded_iff_forall_norm_le.mpr
    by_cases hs : S.Nonempty
    · obtain ⟨x, hx⟩ := hs
      refine ⟨‖ℓ (F x)‖ + C * (2 * r), ?_⟩
      rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      have hx' : ‖x‖ ≤ r := by simpa only [K, Metric.mem_closedBall, dist_zero_right] using hx.1
      have hy' : ‖y‖ ≤ r := by simpa only [K, Metric.mem_closedBall, dist_zero_right] using hy.1
      have hdist : ‖y - x‖ ≤ 2 * r := (norm_sub_le _ _).trans (by linarith)
      calc
        ‖ℓ (F y)‖ ≤ ‖ℓ (F y) - ℓ (F x)‖ + ‖ℓ (F x)‖ := by
          simpa only [sub_add_cancel] using norm_add_le (ℓ (F y) - ℓ (F x)) (ℓ (F x))
        _ ≤ _ := by linarith [h x hx y hy, mul_le_mul_of_nonneg_left hdist hC]
    · rw [not_nonempty_iff_eq_empty.mp hs, image_empty, image_empty]
      exact ⟨0, by simp⟩
  have hS : ∀ᶠ t in 𝓝[≠] (0 : 𝕜), t ∈ S := by
    have hKevent : ∀ᶠ t in 𝓝[≠] (0 : 𝕜), t ∈ K :=
      mem_nhdsWithin_of_mem_nhds (Metric.closedBall_mem_nhds _ hr)
    exact hKevent.and self_mem_nhdsWithin
  have hComplete : IsComplete (closure (F '' S)) :=
    QuasiCompleteSpace.quasiComplete hB.closure isClosed_closure
  obtain ⟨d, _, hd⟩ := hComplete _ hC
    (le_principal_iff.mpr (hS.mono fun t ht => subset_closure (mem_image_of_mem F ht)))
  refine ⟨d, fun ℓ => ?_⟩
  have hlim := ℓ.continuous.continuousAt.tendsto.comp hd
  apply hasDerivAt_iff_tendsto_slope_zero.mpr
  simpa only [Function.comp_def, hEval, zero_add] using hlim

end VectorSlopes

section VectorOrders

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedSpace 𝕜 ℂ]
  [IsScalarTower ℝ 𝕜 ℂ] [IsScalarTower 𝕜 ℂ ℂ]
  [AddCommGroup E] [Module ℂ E] [Module ℝ E] [IsScalarTower ℝ ℂ E]
  [Module 𝕜 E] [IsScalarTower 𝕜 ℂ E]
  [UniformSpace E] [IsUniformAddGroup E] [T2Space E]
  [ContinuousSMul ℂ E] [PolynormableSpace ℂ E]
  {n : ℕ}

private abbrev Coord := Fin n → 𝕜

/-- The corrected order-zero condition, with bounded difference ratios
on a closed ball about each point of the domain. -/
def LocallyBoundedVectorRatios (f : Coord (n := n) (𝕜 := 𝕜) → E) (U : Set (Fin n → 𝕜)) : Prop :=
  ∀ x ∈ U, ∃ r > 0, Metric.closedBall x r ⊆ U ∧
    IsVonNBounded ℂ {z : E | ∃ a ∈ Metric.closedBall x r, ∃ b ∈ Metric.closedBall x r,
      z = ‖b - a‖⁻¹ • (f b - f a)}

/-- Definition C.5.1.23 with the local order-zero condition. The coordinate
limits are specified by their scalar tests, which determine them uniquely. -/
def LocalVectorContDiff : ℕ → ((Fin n → 𝕜) → E) → Set (Fin n → 𝕜) → Prop
  | 0, f, U => ContinuousOn f U ∧ LocallyBoundedVectorRatios f U
  | m + 1, f, U => ∃ d : Fin n → (Fin n → 𝕜) → E,
    (∀ i, LocalVectorContDiff m (d i) U) ∧
    ∀ i, ∀ x ∈ U, ∀ ℓ : StrongDual ℂ E,
      HasDerivAt (fun t : 𝕜 => ℓ (f (x + t • Pi.single i 1))) (ℓ (d i x)) 0

omit [IsScalarTower ℝ 𝕜 ℂ] [IsScalarTower 𝕜 ℂ ℂ] [Module 𝕜 E] [IsScalarTower 𝕜 ℂ E]
  [IsUniformAddGroup E] [T2Space E] [ContinuousSMul ℂ E] in
private theorem weakly_C1_locally_bounded_ratios {U : Set (Fin n → 𝕜)} (hU : IsOpen U)
    (f : (Fin n → 𝕜) → E)
    (hf : ∀ ℓ : StrongDual ℂ E, ContDiffOn 𝕜 1 (fun t => ℓ (f t)) U) :
    ContinuousOn f U ∧ LocallyBoundedVectorRatios f U := by
  let D (ℓ : StrongDual ℂ E) := fderiv 𝕜 (fun t => ℓ (f t))
  have hD (ℓ : StrongDual ℂ E) (x : Fin n → 𝕜) (hx : x ∈ U) :
      HasFDerivAt (fun t => ℓ (f t)) (D ℓ x) x :=
    (((hf ℓ).differentiableOn (by decide)) x hx).differentiableAt
      (hU.mem_nhds hx) |>.hasFDerivAt
  have hcont (ℓ : StrongDual ℂ E) :
      ContinuousOn (fun p : (Fin n → 𝕜) × (Fin n → 𝕜) => D ℓ p.1 p.2) (U ×ˢ univ) := by
    have h₁ : ContinuousOn (fun p : (Fin n → 𝕜) × (Fin n → 𝕜) => D ℓ p.1) (U ×ˢ univ) :=
      ((hf ℓ).continuousOn_fderiv_of_isOpen hU le_rfl).comp
        continuous_fst.continuousOn (fun p hp => hp.1)
    exact h₁.clm_apply continuous_snd.continuousOn
  refine ⟨continuousOn_of_continuous_weakDifferential hU f D hD hcont, fun x hx => ?_⟩
  obtain ⟨r, hr, hK⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hx)
  exact ⟨r, hr, hK, weakDifferential_bounded_ratios (isCompact_closedBall x r)
    (convex_closedBall x r) f D (fun ℓ y hy => hD ℓ y (hK hy))
    (fun ℓ => (hcont ℓ).mono (prod_mono_left hK))⟩

variable [QuasiCompleteSpace ℂ E]

/-- For a weakly twice differentiable map into a quasi-complete space, the
scalar directional derivatives are represented by one vector of the target. -/
theorem weak_coordinate_derivative {U : Set (Fin n → 𝕜)} (hU : IsOpen U)
    (f : (Fin n → 𝕜) → E)
    (hf : ∀ ℓ : StrongDual ℂ E, ContDiffOn 𝕜 2 (fun t => ℓ (f t)) U)
    (x : Fin n → 𝕜) (hx : x ∈ U) (v : Fin n → 𝕜) :
    ∃ d : E, ∀ ℓ : StrongDual ℂ E, HasDerivAt (fun t : 𝕜 => ℓ (f (x + t • v))) (ℓ d) 0 := by
  let p : 𝕜 → Fin n → 𝕜 := fun t => x + t • v
  let W := p ⁻¹' U
  have hp : ContDiff 𝕜 2 p := contDiff_const.add
    ((ContinuousLinearMap.id 𝕜 𝕜).smulRight v).contDiff
  have hW : IsOpen W := hU.preimage hp.continuous
  have hw : 0 ∈ W := by simpa [W, p] using hx
  exact weakly_C2_slope_limit hW hw (f ∘ p)
    (fun ℓ => (hf ℓ).comp hp.contDiffOn (mapsTo_preimage _ _))

omit [IsScalarTower ℝ 𝕜 ℂ] [IsScalarTower 𝕜 ℂ ℂ] in
private theorem scalar_line_deriv_eq {U : Set (Fin n → 𝕜)} (hU : IsOpen U)
    {u : (Fin n → 𝕜) → ℂ} (hu : DifferentiableOn 𝕜 u U)
    {x : Fin n → 𝕜} (hx : x ∈ U) (v : Fin n → 𝕜) :
    HasDerivAt (fun t : 𝕜 => u (x + t • v)) (fderiv 𝕜 u x v) 0 := by
  let L := (ContinuousLinearMap.id 𝕜 𝕜).smulRight v
  have hL : HasFDerivAt (fun t : 𝕜 => x + t • v) L 0 := L.hasFDerivAt.const_add x
  have h := ((hu x hx).differentiableAt (hU.mem_nhds hx)).hasFDerivAt
  have hf : HasFDerivAt u (fderiv 𝕜 u x) (x + (0 : 𝕜) • v) := by
    simpa only [zero_smul, add_zero] using h
  simpa [Function.comp_def, L] using (hf.comp 0 hL).hasDerivAt

/-- Corrected Theorem C.5.1.24. Quasi-completeness gives one fewer order
of differentiability in the original topology than in scalar tests. -/
theorem localVectorContDiff_of_weak {U : Set (Fin n → 𝕜)} (hU : IsOpen U)
    (m : ℕ) (f : (Fin n → 𝕜) → E)
    (hf : ∀ ℓ : StrongDual ℂ E, ContDiffOn 𝕜 ((m : ℕ∞ω) + 1) (fun t => ℓ (f t)) U) :
    LocalVectorContDiff m f U := by
  induction m generalizing f with
  | zero =>
    exact weakly_C1_locally_bounded_ratios hU f (fun ℓ => by simpa using hf ℓ)
  | succ m ih =>
    classical
    have h2 (ℓ : StrongDual ℂ E) : ContDiffOn 𝕜 2 (fun t => ℓ (f t)) U :=
      (hf ℓ).of_le (by
        have h : (2 : ℕ∞ω) ≤ (m : ℕ∞ω) + 2 := le_add_of_nonneg_left (by positivity)
        simpa only [Nat.cast_succ, add_assoc, one_add_one_eq_two] using h)
    let d (i : Fin n) (x : Fin n → 𝕜) : E :=
      if hx : x ∈ U then Classical.choose
        (weak_coordinate_derivative hU f h2 x hx (Pi.single i 1)) else 0
    have hDer (i : Fin n) (x : Fin n → 𝕜) (hx : x ∈ U) (ℓ : StrongDual ℂ E) :
        HasDerivAt (fun t : 𝕜 => ℓ (f (x + t • Pi.single i 1))) (ℓ (d i x)) 0 := by
      simpa only [d, dite_eq_left hx] using
        Classical.choose_spec (weak_coordinate_derivative hU f h2 x hx (Pi.single i 1)) ℓ
    refine ⟨d, fun i => ih (d i) (fun ℓ => ?_), hDer⟩
    have hh : ContDiffOn 𝕜 ((m : ℕ∞ω) + 1) (fderiv 𝕜 (fun t => ℓ (f t))) U :=
      (hf ℓ).fderiv_of_isOpen hU (by push_cast; rfl)
    have hc := hh.clm_apply (g := fun _ => Pi.single i (1 : 𝕜)) contDiffOn_const
    apply hc.congr
    intro x hx
    exact (hDer i x hx ℓ).deriv.symm.trans
      (scalar_line_deriv_eq hU ((h2 ℓ).differentiableOn (by decide)) hx (Pi.single i 1)).deriv

omit [QuasiCompleteSpace ℂ E] [IsScalarTower ℝ 𝕜 ℂ] [IsScalarTower 𝕜 ℂ ℂ]
  [Module 𝕜 E] [IsScalarTower 𝕜 ℂ E] [IsUniformAddGroup E] [T2Space E] [ContinuousSMul ℂ E] in
private theorem localVectorContDiff_scalar {U : Set (Fin n → 𝕜)} (hU : IsOpen U)
    (m : ℕ) (f : (Fin n → 𝕜) → E) (hf : LocalVectorContDiff m f U) :
    ContinuousOn f U ∧ ∀ ℓ : StrongDual ℂ E, ContDiffOn 𝕜 m (fun t => ℓ (f t)) U := by
  induction m generalizing f with
  | zero =>
    exact ⟨hf.1, fun ℓ => contDiffOn_zero.mpr (ℓ.continuous.comp_continuousOn hf.1)⟩
  | succ m ih =>
    obtain ⟨d, hd, hDer⟩ := hf
    have hrec (i : Fin n) := ih (d i) (hd i)
    have hh (ℓ : StrongDual ℂ E) : ContDiffOn 𝕜 ((m : ℕ∞ω) + 1) (fun t => ℓ (f t)) U := by
      let u : (Fin n → 𝕜) → ℂ := fun x => ℓ (f x)
      let D (i : Fin n) (x : Fin n → 𝕜) := ℓ (d i x)
      have hF (x : Fin n → 𝕜) (hx : x ∈ U) :
          HasFDerivAt u (coordinateDifferential fun i => D i x) x :=
        hasFDerivAt_of_continuous_coordinate_derivatives hU u D
          (fun i z hz => hDer i z hz ℓ) (fun i => ℓ.continuous.comp_continuousOn (hrec i).1) hx
      apply (contDiffOn_succ_iff_fderiv_apply hU.uniqueDiffOn).mpr
      refine ⟨fun x hx => (hF x hx).differentiableAt.differentiableWithinAt, by simp, fun v => ?_⟩
      have hS : ContDiffOn 𝕜 (m : ℕ∞ω) (fun x => ∑ i, v i • D i x) U :=
        ContDiffOn.sum fun i _ => contDiffOn_const.smul ((hrec i).2 ℓ)
      apply hS.congr
      intro x hx
      rw [(hF x hx).hasFDerivWithinAt.fderivWithin (hU.uniqueDiffOn x hx),
        coordinateDifferential_apply]
    have h₁ : (1 : ℕ∞ω) ≤ (m : ℕ∞ω) + 1 := le_add_of_nonneg_left (by positivity)
    exact ⟨(weakly_C1_locally_bounded_ratios hU f fun ℓ => (hh ℓ).of_le h₁).1,
      fun ℓ => by simpa only [Nat.cast_succ] using hh ℓ⟩

/-- Corollary C.5.1.25. In a quasi-complete space the two notions of
infinite differentiability agree, with the corrected local order-zero clause. -/
theorem localVectorSmooth_iff_weak {U : Set (Fin n → 𝕜)} (hU : IsOpen U)
    (f : (Fin n → 𝕜) → E) :
    (∀ m : ℕ, LocalVectorContDiff m f U) ↔
      ∀ ℓ : StrongDual ℂ E, ContDiffOn 𝕜 ∞ (fun t => ℓ (f t)) U := by
  constructor
  · intro h ℓ
    exact contDiffOn_infty.mpr fun m => (localVectorContDiff_scalar hU m f (h m)).2 ℓ
  · intro h m
    apply localVectorContDiff_of_weak hU m f
    intro ℓ
    exact (h ℓ).of_le (by
      simpa only [Nat.cast_succ] using
        (show ((m + 1 : ℕ) : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top))

end VectorOrders

/-- The one-variable complex specialization of C.5.1.25. Scalar holomorphy
is equivalent to smoothness in the corrected vector-valued sense. -/
theorem localVectorSmooth_one_iff_weakHolomorphic {E : Type*}
    [AddCommGroup E] [Module ℂ E] [Module ℝ E] [IsScalarTower ℝ ℂ E]
    [UniformSpace E] [IsUniformAddGroup E] [T2Space E] [ContinuousSMul ℂ E]
    [PolynormableSpace ℂ E] [QuasiCompleteSpace ℂ E] {U : Set (Fin 1 → ℂ)} (hU : IsOpen U)
    (f : (Fin 1 → ℂ) → E) :
    (∀ m : ℕ, LocalVectorContDiff m f U) ↔
      ∀ ℓ : StrongDual ℂ E, DifferentiableOn ℂ (fun x => ℓ (f x)) U := by
  rw [localVectorSmooth_iff_weak hU]
  let L : (Fin 1 → ℂ) →L[ℂ] ℂ := ContinuousLinearMap.proj 0
  let R : ℂ →L[ℂ] (Fin 1 → ℂ) := ContinuousLinearMap.pi fun _ => ContinuousLinearMap.id ℂ ℂ
  have hLR (x : Fin 1 → ℂ) : R (L x) = x := by
    ext i
    fin_cases i
    rfl
  constructor
  · intro h ℓ
    exact (h ℓ).differentiableOn (by decide)
  · intro h ℓ
    let g := fun z => ℓ (f (R z))
    let V := R ⁻¹' U
    have hg : DifferentiableOn ℂ g V :=
      (h ℓ).comp R.differentiable.differentiableOn (mapsTo_preimage _ _)
    have hs : ContDiffOn ℂ ∞ g V := hg.contDiffOn (hU.preimage R.continuous)
    have hmaps : MapsTo L U V := by
      intro x hx
      change R (L x) ∈ U
      rwa [hLR]
    apply (hs.comp L.contDiff.contDiffOn hmaps).congr
    intro x _
    change ℓ (f x) = ℓ (f (R (L x)))
    rw [hLR]

end

end Masullo
