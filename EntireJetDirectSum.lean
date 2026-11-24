import EntireBergmanRestriction
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! Disc division and the finite jet span adapt the Apache-2.0
RiemannMasullo proof in Ch07_SchauderBasesZeta/Sec1b.lean at 3897f94. -/

open Bornology Filter Function Metric Set Topology
open scoped NNReal

namespace Masullo

noncomputable section

set_option maxHeartbeats 1200000

@[reducible] local instance : TopologicalSpace (StrongDual ℂ CompactOpenEntire) :=
  ContinuousLinearMap.topologicalSpace (σ := RingHom.id ℂ) (E := CompactOpenEntire) (F := ℂ)

@[reducible] local instance : AddCommGroup (StrongDual ℂ CompactOpenEntire) :=
  ContinuousLinearMap.addCommGroup (σ₁₂ := RingHom.id ℂ) (M := CompactOpenEntire) (M₂ := ℂ)

private def entireMul (f g : CompactOpenEntire) : CompactOpenEntire :=
  ⟨f.val * g.val, (show Differentiable ℂ (f.val : ℂ → ℂ) from f.property).mul g.property⟩

@[simp] theorem compactOpenEntireJet_apply (z : ℂ) (m : ℕ) (f : CompactOpenEntire) :
    compactOpenEntireJet z m f = iteratedDeriv m (f.val : ℂ → ℂ) z := rfl

private theorem entire_analyticOrderAt_ne_top (G : ℂ → ℂ) (hG : Differentiable ℂ G)
    (hG0 : ∃ z, G z ≠ 0) (z : ℂ) : analyticOrderAt G z ≠ ⊤ := by
  obtain ⟨z₀, h⟩ := hG0
  have hA : AnalyticOnNhd ℂ G univ := fun x _ ↦ hG.analyticAt x
  exact hA.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ (mem_univ z₀) (mem_univ z)
    (by simp [analyticOrderAt_eq_zero.mpr (Or.inr h)])

/-- (D) A nonzero entire function has finitely many jet indices in a disc. -/
private theorem entire_jetIndices_finite (g : CompactOpenEntire) (hg : ∃ z, g.val z ≠ 0) (R : ℝ) :
    {p : ℂ × ℕ | (p.2 : ℕ∞) < analyticOrderAt (g.val : ℂ → ℂ) p.1 ∧ ‖p.1‖ ≤ R}.Finite := by
  have hd : Differentiable ℂ (g.val : ℂ → ℂ) := g.property
  have hZ : (Metric.closedBall (0 : ℂ) R \ {z | g.val z ≠ 0}).Finite := by
    apply (isCompact_closedBall (0 : ℂ) R).finite_sdiff_of_mem_codiscreteWithin
    have hA : AnalyticOnNhd ℂ (g.val : ℂ → ℂ) univ := fun x _ ↦ hd.analyticAt x
    rcases hA.eqOn_zero_or_eventually_ne_zero_of_preconnected isPreconnected_univ with h1 | h1
    · obtain ⟨z, hz⟩ := hg
      exact absurd (h1 (mem_univ z)) hz
    · exact Filter.codiscreteWithin_mono (subset_univ _) h1
  refine (hZ.prod (hZ.biUnion fun z _ ↦
    Set.finite_Iio (analyticOrderAt (g.val : ℂ → ℂ) z).toNat)).subset ?_
  rintro ⟨z, k⟩ ⟨hk, hz⟩
  have hne := entire_analyticOrderAt_ne_top _ hd hg z
  have hz0 : g.val z = 0 := by
    by_contra h0
    rw [analyticOrderAt_eq_zero.mpr (Or.inr h0)] at hk
    exact (not_lt_zero hk).elim
  have hmem : z ∈ Metric.closedBall (0 : ℂ) R \ {z | g.val z ≠ 0} :=
    ⟨mem_closedBall_zero_iff.mpr hz, by simpa using hz0⟩
  refine ⟨hmem, mem_biUnion hmem ?_⟩
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hne
  simp only at hk ⊢
  rw [← hn] at hk ⊢
  simpa using hk

/-- Division of entire functions where the orders allow it: the quotient is analytic. -/
private theorem entire_div_of_order_le (G F : ℂ → ℂ) (hG : Differentiable ℂ G)
    (hF : Differentiable ℂ F) (hG0 : ∃ z, G z ≠ 0) (U : Set ℂ)
    (h : ∀ z ∈ U, analyticOrderAt G z ≤ analyticOrderAt F z) :
    ∃ w : ℂ → ℂ, (∀ z ∈ U, AnalyticAt ℂ w z) ∧ ∀ z ∈ U, F z = G z * w z := by
  have hmero : MeromorphicOn (F / G) univ := fun z _ ↦
    (hF.analyticAt z).meromorphicAt.div (hG.analyticAt z).meromorphicAt
  have hw : ∀ z ∈ U, AnalyticAt ℂ (toMeromorphicNFOn (F / G) univ) z := by
    intro z hz
    have hNF := meromorphicNFOn_toMeromorphicNFOn (F / G) univ (mem_univ z)
    rw [← hNF.meromorphicOrderAt_nonneg_iff_analyticAt,
      meromorphicOrderAt_toMeromorphicNFOn hmero (mem_univ z),
      meromorphicOrderAt_div (hF.analyticAt z).meromorphicAt (hG.analyticAt z).meromorphicAt,
      (hF.analyticAt z).meromorphicOrderAt_eq, (hG.analyticAt z).meromorphicOrderAt_eq]
    have hz' := h z hz
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (entire_analyticOrderAt_ne_top G hG hG0 z)
    rw [← hn] at hz' ⊢
    by_cases hFt : analyticOrderAt F z = ⊤
    · rw [hFt]
      simp
    · obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hFt
      rw [← hm] at hz' ⊢
      have hnm : n ≤ m := by exact_mod_cast hz'
      simp only [ENat.map_natCast]
      have h0 : (0 : ℤ) ≤ (m : ℤ) - n := by omega
      show (0 : WithTop ℤ) ≤ (((m : ℤ) - n : ℤ) : WithTop ℤ)
      exact WithTop.coe_le_coe.mpr h0
  refine ⟨toMeromorphicNFOn (F / G) univ, hw, fun z hz ↦ ?_⟩
  have hne : ∀ᶠ y in 𝓝[≠] z, G y ≠ 0 :=
    ((hG.analyticAt z).eventually_eq_zero_or_eventually_ne_zero).resolve_left
      (fun h' ↦ entire_analyticOrderAt_ne_top G hG hG0 z (analyticOrderAt_eq_top.mpr h'))
  have heq := hmero.toMeromorphicNFOn_eq_self_on_nhdsNE (mem_univ z)
  have h1 : F =ᶠ[𝓝[≠] z] fun y ↦ G y * toMeromorphicNFOn (F / G) univ y := by
    filter_upwards [hne, heq] with y hy hy'
    rw [hy', Pi.div_apply]
    field_simp
  exact (((hF.continuous.continuousAt).eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
    ((hG.continuous.continuousAt).mul (hw z hz).continuousAt)).mp h1).eq_of_nhds

/-- (L1) Division plus Taylor approximation on a disc. -/
private theorem entire_approx_of_order_le (g f : CompactOpenEntire) (hg : ∃ z, g.val z ≠ 0) {r r' : ℝ}
    (hr : r' < r)
    (h : ∀ z ∈ Metric.ball (0 : ℂ) r,
      analyticOrderAt (g.val : ℂ → ℂ) z ≤ analyticOrderAt (f.val : ℂ → ℂ) z)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ P : CompactOpenEntire, ∀ z ∈ Metric.closedBall (0 : ℂ) r', ‖f.val z - g.val z * P.val z‖ ≤ ε := by
  have hgd : Differentiable ℂ (g.val : ℂ → ℂ) := g.property
  have hfd : Differentiable ℂ (f.val : ℂ → ℂ) := f.property
  rcases lt_or_ge r' 0 with hr0 | hr0
  · exact ⟨0, fun z hz ↦ absurd (Metric.nonempty_closedBall.mp ⟨z, hz⟩) (not_le.mpr hr0)⟩
  obtain ⟨w, hwa, hw⟩ := entire_div_of_order_le _ _ hgd hfd hg (Metric.ball 0 r) h
  have hR0 : 0 < (r' + r) / 2 := by linarith
  let Rn : ℝ≥0 := ⟨(r' + r) / 2, hR0.le⟩
  have hd : DifferentiableOn ℂ w (Metric.closedBall 0 (Rn : ℝ)) := fun z hz ↦
    (hwa z (Metric.closedBall_subset_ball (show (Rn : ℝ) < r by
      change (r' + r) / 2 < r; linarith) hz)).differentiableAt.differentiableWithinAt
  have hps := hd.hasFPowerSeriesOnBall (show (0 : ℝ≥0) < Rn from hR0)
  let Rm : ℝ≥0 := ⟨(r' + (r' + r) / 2) / 2, by linarith⟩
  have hu := hps.tendstoUniformlyOn (r' := Rm)
    (ENNReal.coe_lt_coe.mpr (show Rm < Rn by change (r' + (r' + r) / 2) / 2 < (r' + r) / 2; linarith))
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) r').exists_bound_of_continuousOn
    hgd.continuous.continuousOn
  have hδ : 0 < ε / (|C| + 1) := by positivity
  obtain ⟨n, hn⟩ := (Metric.tendstoUniformlyOn_iff.mp hu _ hδ).exists
  set p := cauchyPowerSeries w 0 Rn
  have hpart : ∀ y, p.partialSum n y = ∑ k ∈ Finset.range n, y ^ k * p.coeff k := by
    intro y
    simp [FormalMultilinearSeries.partialSum]
  have hPd : Differentiable ℂ fun y : ℂ ↦ ∑ k ∈ Finset.range n, y ^ k * p.coeff k := by fun_prop
  refine ⟨⟨⟨fun y ↦ ∑ k ∈ Finset.range n, y ^ k * p.coeff k, hPd.continuous⟩, hPd⟩,
    fun z hz ↦ ?_⟩
  have hz' : ‖z‖ ≤ r' := mem_closedBall_zero_iff.mp hz
  have hzm : z ∈ Metric.ball (0 : ℂ) Rm := mem_ball_zero_iff.mpr (by
    change ‖z‖ < (r' + (r' + r) / 2) / 2; linarith)
  have hzr : z ∈ Metric.ball (0 : ℂ) r := mem_ball_zero_iff.mpr (by linarith)
  rw [hw z hzr]
  change ‖g.val z * w z - g.val z * (∑ k ∈ Finset.range n, z ^ k * p.coeff k)‖ ≤ ε
  rw [← mul_sub, norm_mul]
  have h1 := hn z hzm
  rw [zero_add, dist_eq_norm, hpart] at h1
  calc ‖g.val z‖ * ‖w z - ∑ k ∈ Finset.range n, z ^ k * p.coeff k‖
      ≤ |C| * (ε / (|C| + 1)) :=
        mul_le_mul ((hC z hz).trans (le_abs_self C)) h1.le (norm_nonneg _) (abs_nonneg _)
    _ ≤ ε := by
        rw [mul_div_assoc', div_le_iff₀ (by positivity)]
        nlinarith [abs_nonneg C]
/-- A continuous functional on entire functions is controlled by a sup norm on a compact set. -/
private theorem entire_strongDual_bound (ℓ : StrongDual ℂ CompactOpenEntire) :
    ∃ K : Set ℂ, IsCompact K ∧ ∃ δ > 0, ∀ f : CompactOpenEntire,
      (∀ x ∈ K, ‖f.val x‖ < δ) → ‖ℓ f‖ < 1 := by
  have h0 : ℓ ⁻¹' Metric.ball 0 1 ∈ 𝓝 (0 : CompactOpenEntire) :=
    ℓ.continuous.continuousAt.preimage_mem_nhds (by
      rw [map_zero]
      exact Metric.ball_mem_nhds 0 one_pos)
  rw [nhds_subtype, mem_comap] at h0
  obtain ⟨t, ht, hts⟩ := h0
  rw [nhds_eq_comap_uniformity, mem_comap] at ht
  obtain ⟨X, hX, hXt⟩ := ht
  obtain ⟨⟨K, ε⟩, ⟨hK, hε⟩, hKX⟩ :=
    (Metric.uniformity_basis_dist.compactConvergenceUniformity (α := ℂ)).mem_iff.mp hX
  refine ⟨K, hK, ε, hε, fun f hf ↦ ?_⟩
  have hf' : f ∈ (Subtype.val ⁻¹' t : Set CompactOpenEntire) := hXt (hKX fun x hx ↦ by
    have := hf x hx
    simpa [dist_eq_norm] using this)
  have hh := hts hf'
  exact mem_ball_zero_iff.mp hh

private theorem continuousDual_mem_span_of_kernel {E ι : Type*}
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [Finite ι]
    (L : ι → StrongDual ℂ E) (l : StrongDual ℂ E)
    (h : ∀ x, (∀ i, L i x = 0) → l x = 0) :
    l ∈ Submodule.span ℂ (range L) := by
  let c : StrongDual ℂ E →ₗ[ℂ] (E →ₗ[ℂ] ℂ) := ContinuousLinearMap.coeLM ℂ
  let L₀ (i : ι) := c (L i)
  have hle : (⨅ i : ι, (L₀ i).ker) ≤ (c l).ker := by
    intro x hx
    apply LinearMap.mem_ker.mpr
    apply h x
    intro i
    have hm : L₀ i x = 0 := LinearMap.mem_ker.mp ((Submodule.mem_iInf _).mp hx i)
    exact hm
  have hspan : c l ∈ Submodule.span ℂ (range L₀) :=
    mem_span_of_iInf_ker_le_ker (𝕜 := ℂ) (E := E) (ι := ι) (L := L₀) (K := c l) hle
  have hmap : Submodule.span ℂ (range L₀) ≤ (Submodule.span ℂ (range L)).map c := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact Submodule.mem_map.mpr ⟨L i, Submodule.subset_span (mem_range_self i), rfl⟩
  obtain ⟨y, hy, hyl⟩ := Submodule.mem_map.mp (hmap hspan)
  have he : y = l := ContinuousLinearMap.coe_injective hyl
  exact he ▸ hy

/-- (C) Every functional killing `g · H(ℂ)` is a finite combination of jets. -/
theorem compactOpenEntireAnnihilator_le_span_jets (g : CompactOpenEntire) (hg : ∃ z, g.val z ≠ 0)
    (ℓ : StrongDual ℂ CompactOpenEntire) (hℓ : ℓ ∈ compactOpenEntireAnnihilator g.val) :
    ∃ s : Finset (ℂ × ℕ), (∀ j ∈ s, (j.2 : ℕ∞) < analyticOrderAt (g.val : ℂ → ℂ) j.1) ∧
      ℓ ∈ Submodule.span ℂ ((fun j : ℂ × ℕ ↦ compactOpenEntireJet j.1 j.2) '' (s : Set (ℂ × ℕ))) := by
  obtain ⟨K, hK, δ, hδ, hKδ⟩ := entire_strongDual_bound ℓ
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
  have hfin := entire_jetIndices_finite g hg (R + 1)
  refine ⟨hfin.toFinset, fun j hj ↦ (hfin.mem_toFinset.mp hj).1, ?_⟩
  have hℓ' (w : CompactOpenEntire) (hw : w ∈ compactOpenEntireDivisor g.val) : ℓ w = 0 :=
    (Submodule.mem_dualAnnihilator ℓ.toLinearMap).mp hℓ w hw
  have hker : ∀ f : CompactOpenEntire, (∀ j ∈ hfin.toFinset, compactOpenEntireJet j.1 j.2 f = 0) → ℓ f = 0 := by
    intro f hf
    have hord : ∀ z ∈ Metric.ball (0 : ℂ) (R + 1),
        analyticOrderAt (g.val : ℂ → ℂ) z ≤ analyticOrderAt (f.val : ℂ → ℂ) z := by
      intro z hz
      obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp
        (entire_analyticOrderAt_ne_top _ g.property hg z)
      rw [← hn, natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero ((show Differentiable ℂ (f.val : ℂ → ℂ) from f.property).analyticAt z)]
      intro i hi
      have h1 := hf (z, i) (hfin.mem_toFinset.mpr
        ⟨by rw [← hn]; exact_mod_cast hi, (mem_ball_zero_iff.mp hz).le⟩)
      rwa [compactOpenEntireJet_apply] at h1
    refine norm_le_zero_iff.mp (le_of_forall_pos_lt_add fun η hη ↦ ?_)
    obtain ⟨P, hP⟩ := entire_approx_of_order_le g f hg (r := R + 1) (r' := R) (by linarith)
      hord (ε := η * δ / 2) (by positivity)
    let Q := entireMul P g
    have hgd : Differentiable ℂ (g.val : ℂ → ℂ) := g.property
    have hgP : ℓ Q = 0 := hℓ' Q ((compactOpenEntireDivisor_mem_iff hgd Q).mpr
      ⟨P.val, P.property, fun z ↦ mul_comm _ _⟩)
    have hh : ∀ x ∈ K, ‖(((η : ℂ)⁻¹) • (f - Q)).val x‖ < δ := by
      intro x hx
      have h1 := hP x (hR hx)
      change ‖(η : ℂ)⁻¹ * (f.val x - P.val x * g.val x)‖ < δ
      rw [norm_mul, norm_inv, Complex.norm_of_nonneg hη.le, mul_comm (P.val x)]
      calc η⁻¹ * ‖f.val x - g.val x * P.val x‖ ≤ η⁻¹ * (η * δ / 2) :=
            mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hη.le)
        _ < δ := by
            rw [show η⁻¹ * (η * δ / 2) = δ / 2 by field_simp]
            linarith
    have h1 := hKδ _ hh
    have hsub : ℓ (f - Q) = ℓ f - ℓ Q := ℓ.toLinearMap.map_sub f Q
    rw [map_smul, hsub, hgP, sub_zero, smul_eq_mul, norm_mul, norm_inv,
      Complex.norm_of_nonneg hη.le, inv_mul_lt_iff₀ hη, mul_one] at h1
    rwa [zero_add]
  let I := ↥hfin.toFinset
  let L (j : I) : StrongDual ℂ CompactOpenEntire := compactOpenEntireJet j.val.1 j.val.2
  have hker' (f : CompactOpenEntire) (hf : ∀ i : I, L i f = 0) : ℓ f = 0 := by
    apply hker f
    intro j hj
    exact hf (⟨j, hj⟩ : I)
  letI : Finite I := Finite.of_fintype _
  have hspan : ℓ ∈ Submodule.span ℂ (range L) :=
    @continuousDual_mem_span_of_kernel CompactOpenEntire I
      (Submodule.addCommGroup compactOpenEntireSubmodule) (Submodule.module compactOpenEntireSubmodule)
      _ inferInstance L ℓ hker'
  have hsub : range L ⊆
      (fun j : ℂ × ℕ ↦ compactOpenEntireJet j.1 j.2) '' (hfin.toFinset : Set (ℂ × ℕ)) := by
    rintro _ ⟨i, rfl⟩
    exact ⟨i.val, i.property, rfl⟩
  exact Submodule.span_mono hsub hspan

/-- Basic neighbourhoods of zero for the compact-open topology on entire functions. -/
private theorem entire_nhds_zero (V : Set CompactOpenEntire) (hV : V ∈ 𝓝 (0 : CompactOpenEntire)) :
    ∃ K : Set ℂ, IsCompact K ∧ ∃ ε > 0, ∀ f : CompactOpenEntire, (∀ x ∈ K, ‖f.val x‖ < ε) → f ∈ V := by
  rw [nhds_subtype, mem_comap] at hV
  obtain ⟨t, ht, hts⟩ := hV
  rw [nhds_eq_comap_uniformity, mem_comap] at ht
  obtain ⟨X, hX, hXt⟩ := ht
  obtain ⟨⟨K, ε⟩, ⟨hK, hε⟩, hKX⟩ :=
    (Metric.uniformity_basis_dist.compactConvergenceUniformity (α := ℂ)).mem_iff.mp hX
  refine ⟨K, hK, ε, hε, fun f hf ↦ ?_⟩
  have hf' : f ∈ (Subtype.val ⁻¹' t : Set CompactOpenEntire) := hXt (hKX fun x hx ↦ by
    have := hf x hx
    simpa [dist_eq_norm] using this)
  exact hts hf'

/-- Locally uniformly bounded families of entire functions are von Neumann bounded. -/
private theorem entire_isVonNBounded (S : Set CompactOpenEntire)
    (hS : ∀ R : ℝ, ∃ M : ℝ, ∀ f ∈ S, ∀ z ∈ Metric.closedBall (0 : ℂ) R, ‖f.val z‖ ≤ M) :
    Bornology.IsVonNBounded ℂ S := by
  intro V hV
  obtain ⟨K, hK, ε, hε, hKV⟩ := entire_nhds_zero V hV
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
  obtain ⟨M, hM⟩ := hS R
  rw [absorbs_iff_norm]
  refine ⟨(|M| + 1) / ε, fun c hc f hf ↦ ?_⟩
  have hc0 : 0 < ‖c‖ := lt_of_lt_of_le (by positivity) hc
  have hc0' : c ≠ 0 := norm_pos_iff.mp hc0
  refine ⟨c⁻¹ • f, hKV _ fun x hx ↦ ?_, smul_inv_smul₀ hc0' f⟩
  have hfx := hM f hf x (hR hx)
  have e : ‖(c⁻¹ • f).val x‖ = ‖f.val x‖ / ‖c‖ := by
    rw [show (c⁻¹ • f).val x = c⁻¹ * f.val x from rfl, norm_mul, norm_inv]; ring
  rw [e, div_lt_iff₀ hc0]
  calc ‖f.val x‖ ≤ |M| := hfx.trans (le_abs_self M)
    _ < |M| + 1 := by linarith
    _ = ε * ((|M| + 1) / ε) := by field_simp
    _ ≤ ε * ‖c‖ := by gcongr

private theorem sum_half_pow_succ_le_one {ι : Type*} (s : Finset ι) (ν : ι → ℕ)
    (hν : Injective ν) : ∑ i ∈ s, (1 / 2 : ℝ) ^ (ν i + 1) ≤ 1 := by
  classical
  rw [← Finset.sum_image (f := fun k ↦ (1 / 2 : ℝ) ^ (k + 1)) hν.injOn]
  obtain ⟨N, hN⟩ := Finset.exists_nat_subset_range (s.image ν)
  calc ∑ k ∈ s.image ν, (1 / 2 : ℝ) ^ (k + 1) ≤ ∑ k ∈ Finset.range N, (1 / 2 : ℝ) ^ (k + 1) :=
        Finset.sum_le_sum_of_subset_of_nonneg hN fun _ _ _ ↦ by positivity
    _ = (∑ k ∈ Finset.range N, (1 / 2 : ℝ) ^ k) * (1 / 2) := by
        rw [Finset.sum_mul]; simp only [pow_succ]
    _ ≤ 2 * (1 / 2) := by gcongr; exact sum_geometric_two_le N
    _ = 1 := by norm_num
abbrev JetIndex (g : CompactOpenEntire) :=
  {i : ℂ × ℕ // (i.2 : ℕ∞) < analyticOrderAt (g.val : ℂ → ℂ) i.1}

private abbrev jet (g : CompactOpenEntire) (i : JetIndex g) := compactOpenEntireJet i.val.1 i.val.2

private theorem jet_annihilates (g : CompactOpenEntire) (i : JetIndex g) :
    jet g i ∈ compactOpenEntireAnnihilator g.val := by
  apply (Submodule.mem_dualAnnihilator _).mpr
  intro f hf
  simp only [compactOpenEntireDivisor, Submodule.mem_iInf, LinearMap.mem_ker,
    ContinuousLinearMap.coe_coe] at hf
  exact hf i

private theorem jet_biorthogonal_small (g : CompactOpenEntire) (hg : ∃ z, g.val z ≠ 0)
    (i : JetIndex g) (V : CompactOpenEntire)
    (hVjet : ∀ j : JetIndex g, jet g j V = if j = i then 1 else 0)
    (c : ℝ) (hc : 0 < c) :
    ∃ f : CompactOpenEntire,
      (∀ j : JetIndex g, jet g j f = if j = i then 1 else 0) ∧
      ∀ z : ℂ, ‖z‖ < ‖i.val.1‖ / 2 → c * ‖f.val z‖ ≤ 1 := by
  classical
  have hgd : Differentiable ℂ (g.val : ℂ → ℂ) := g.property
  have hVd : Differentiable ℂ (V.val : ℂ → ℂ) := V.property
  have hV (z : ℂ) (hz : z ≠ i.val.1) :
      analyticOrderAt (g.val : ℂ → ℂ) z ≤ analyticOrderAt (V.val : ℂ → ℂ) z := by
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (entire_analyticOrderAt_ne_top _ hgd hg z)
    rw [← hn, natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hVd.analyticAt z)]
    intro m hm
    let j : JetIndex g := ⟨(z, m), by rw [← hn]; exact_mod_cast hm⟩
    have hn' : j ≠ i := fun h ↦ hz (congrArg (fun v : JetIndex g ↦ v.val.1) h)
    simpa only [ite_eq_right hn', compactOpenEntireJet_apply] using hVjet j
  rcases eq_or_ne i.val.1 0 with h0 | h0
  · refine ⟨V, hVjet, fun z hz ↦ ?_⟩
    rw [h0, norm_zero, zero_div] at hz
    exact (not_lt_of_ge (norm_nonneg z) hz).elim
  have hpos := norm_pos_iff.mpr h0
  obtain ⟨P, hP⟩ := entire_approx_of_order_le g V hg (r := ‖i.val.1‖) (r' := ‖i.val.1‖ / 2)
    (by linarith) (fun z hz ↦ hV z (fun h ↦ by rw [h, mem_ball_zero_iff] at hz; exact lt_irrefl _ hz))
    (ε := c⁻¹) (inv_pos.mpr hc)
  let Q := entireMul g P
  have hQ : Q ∈ compactOpenEntireDivisor g.val :=
    (compactOpenEntireDivisor_mem_iff hgd Q).mpr ⟨P.val, P.property, fun _ ↦ rfl⟩
  refine ⟨V - Q, fun j ↦ ?_, fun z hz ↦ ?_⟩
  · have hzero : jet g j Q = 0 :=
      (Submodule.mem_dualAnnihilator _).mp (jet_annihilates g j) Q hQ
    exact ((jet g j).map_sub V Q).trans (by rw [hVjet, hzero, sub_zero])
  · have hbound := hP z (mem_closedBall_zero_iff.mpr hz.le)
    change c * ‖V.val z - g.val z * P.val z‖ ≤ 1
    exact (mul_le_mul_of_nonneg_left hbound hc.le).trans_eq (mul_inv_cancel₀ hc.ne')

open Classical in
/-- The compact-open entire annihilator has the finest locally convex
topology on finitely supported individual derivative coordinates. Grouping
the coordinates at each zero gives the finite-dimensional jet summands. -/
theorem compactOpenEntireAnnihilator_finiteSupportEquiv (g : CompactOpenEntire)
    (hg : ∃ z, g.val z ≠ 0)
    (hV : ∀ i : JetIndex g, ∃ f : CompactOpenEntire,
      ∀ j : JetIndex g, jet g j f = if j = i then 1 else 0) :
    letI : TopologicalSpace (JetIndex g →₀ ℂ) := finestLocallyConvexTopology _
    ∃ e : (JetIndex g →₀ ℂ) ≃L[ℂ] compactOpenEntireAnnihilator g.val,
      ∀ i, (e (Finsupp.single i 1)).val = jet g i := by
  classical
  let I := JetIndex g
  let A := compactOpenEntireAnnihilator g.val
  let D := I →₀ ℂ
  letI : AddCommGroup A := Submodule.addCommGroup A
  letI : TopologicalSpace D := finestLocallyConvexTopology D
  let w (i : I) : A := ⟨jet g i, jet_annihilates g i⟩
  let T : D →ₗ[ℂ] A := Finsupp.linearCombination ℂ w
  have hEval (v : I → CompactOpenEntire)
      (hv : ∀ i j : I, jet g j (v i) = if j = i then 1 else 0)
      (x : D) (i : I) : (T x).val (v i) = x i := by
    let ev : A →ₗ[ℂ] ℂ :=
      { toFun := fun y ↦ y.val (v i)
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl }
    change ev (T x) = x i
    rw [show T x = ∑ j ∈ x.support, x j • w j from Finsupp.linearCombination_apply _ _]
    simp only [map_sum, map_smul, smul_eq_mul]
    change (∑ j ∈ x.support, x j * jet g j (v i)) = x i
    simp only [hv, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [hji]
    · intro hi
      simp [Finsupp.notMem_support_iff.mp hi]
  choose v hv using hV
  have hInject : Injective T := fun x y h ↦ Finsupp.ext fun i ↦ by
    rw [← hEval v hv x i, ← hEval v hv y i, h]
  let L : D →ₗ[ℂ] StrongDual ℂ CompactOpenEntire := A.subtype.comp T
  have hL : L = Finsupp.linearCombination ℂ (jet g) := by
    ext i
    simp [L, T, w]
  have hSurj : Surjective T := by
    intro l
    obtain ⟨s, hs, hl⟩ := compactOpenEntireAnnihilator_le_span_jets g hg l.val l.property
    have hsub : (fun j : ℂ × ℕ ↦ compactOpenEntireJet j.1 j.2) '' (s : Set (ℂ × ℕ)) ⊆
        range (jet g) := by
      rintro _ ⟨i, hi, rfl⟩
      exact ⟨⟨i, hs i hi⟩, rfl⟩
    have hmem : l.val ∈ LinearMap.range L := by
      rw [hL, Finsupp.range_linearCombination]
      exact Submodule.span_mono hsub hl
    obtain ⟨x, hx⟩ := hmem
    exact ⟨x, Subtype.ext hx⟩
  let e := LinearEquiv.ofBijective T ⟨hInject, hSurj⟩
  have hForward : Continuous e := by
    change Continuous (fun x : D ↦ T x)
    apply continuous_induced_rng.2
    letI : PolynormableSpace ℂ (StrongDual ℂ CompactOpenEntire) :=
      (strongDual_withBoundedSeminorms (E := CompactOpenEntire)).toPolynormableSpace
    exact finest_linear_continuous L
  have hfinite (R : ℝ) : {i : I | ‖i.val.1‖ ≤ R}.Finite := by
    apply ((entire_jetIndices_finite g hg R).preimage Subtype.val_injective.injOn).subset
    exact fun i hi ↦ ⟨i.property, hi⟩
  have hCount : Countable I := by
    have he : (univ : Set I) = ⋃ n : ℕ, {i : I | ‖i.val.1‖ ≤ n} := by
      ext i
      simp only [mem_univ, mem_iUnion, mem_ofPred_eq, true_iff]
      exact ⟨⌈‖i.val.1‖⌉₊, Nat.le_ceil _⟩
    exact Set.countable_univ_iff.mp (he ▸ (Set.countable_iUnion fun n : ℕ ↦ (hfinite n).countable))
  obtain ⟨ν, hν⟩ := exists_injective_nat I
  letI : IsTopologicalAddGroup (StrongDual ℂ CompactOpenEntire) :=
    (strongDual_withBoundedSeminorms (E := CompactOpenEntire)).topologicalAddGroup
  have hInverse : Continuous e.symm := by
    apply WithSeminorms.continuous_of_continuous_comp (finest_withSeminorms D) e.symm.toLinearMap
    intro p
    let c (i : I) : ℝ := 2 ^ (ν i + 1) * (p (Finsupp.single i 1) + 1)
    have hc (i : I) : 0 < c i := by
      dsimp [c]
      positivity
    choose f hf hSmall using fun i ↦ jet_biorthogonal_small g hg i (v i) (hv i) (c i) (hc i)
    let b (i : I) := (c i : ℂ) • f i
    have hb : IsVonNBounded ℂ (range b) := by
      apply entire_isVonNBounded
      intro R
      let S := (hfinite (2 * R)).toFinset
      choose M hM using fun i : I ↦ (isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn
        (b i).val.continuous.continuousOn
      refine ⟨1 + ∑ i ∈ S, |M i|, ?_⟩
      rintro _ ⟨i, rfl⟩ z hz
      by_cases hi : ‖i.val.1‖ ≤ 2 * R
      · have hiS : i ∈ S := (hfinite (2 * R)).mem_toFinset.mpr hi
        have hM' := Finset.single_le_sum (f := fun j ↦ |M j|) (fun j _ ↦ abs_nonneg (M j)) hiS
        exact (hM i z hz).trans ((le_abs_self _).trans (by linarith))
      · have hz' : ‖z‖ < ‖i.val.1‖ / 2 := by
          have hzR := mem_closedBall_zero_iff.mp hz
          linarith [not_le.mp hi]
        have he : (b i).val z = (c i : ℂ) * (f i).val z := rfl
        rw [he, norm_mul, Complex.norm_of_nonneg (hc i).le]
        exact (hSmall i z hz').trans (by
          have hsum := Finset.sum_nonneg (s := S) (fun j _ ↦ abs_nonneg (M j))
          linarith)
    let q := strongDualBoundedSeminorm ⟨range b, hb⟩
    have hq : Continuous q := strongDual_withBoundedSeminorms.continuous_seminorm _
    let qA : Seminorm ℂ A := q.comp A.subtype
    have hqA : Continuous qA := by
      change Continuous (q ∘ (Subtype.val : A → StrongDual ℂ CompactOpenEntire))
      exact hq.comp continuous_subtype_val
    apply Seminorm.continuous_of_le hqA
    intro l
    let x := e.symm l
    have hRep : x = ∑ i ∈ x.support, x i • (Finsupp.single i 1 : D) := by
      conv_lhs => rw [← Finsupp.sum_single x]
      simp only [Finsupp.sum]
      apply Finset.sum_congr rfl
      intro i hi
      simp
    have hBound (i : I) : c i * ‖x i‖ ≤ q l.val := by
      have hTx : T x = l := e.apply_symm_apply l
      have hfi : l.val (f i) = x i := hTx ▸ hEval f hf x i
      have hbi : l.val (b i) = (c i : ℂ) * x i := by
        change l.val ((c i : ℂ) • f i) = _
        rw [map_smul, hfi, smul_eq_mul]
      have hq' := strongDualBoundedSeminorm_dom ⟨range b, hb⟩ l.val (mem_range_self i)
      rw [hbi, norm_mul, Complex.norm_of_nonneg (hc i).le] at hq'
      exact hq'
    have hweight (i : I) : ‖x i‖ * p (Finsupp.single i 1) ≤
        q l.val * (1 / 2 : ℝ) ^ (ν i + 1) := by
      have h2 : (0 : ℝ) < 2 ^ (ν i + 1) := by positivity
      calc
        ‖x i‖ * p (Finsupp.single i 1) ≤ ‖x i‖ * (p (Finsupp.single i 1) + 1) := by gcongr; linarith
        _ = (c i * ‖x i‖) / 2 ^ (ν i + 1) := by dsimp [c]; field_simp
        _ ≤ q l.val / 2 ^ (ν i + 1) := by gcongr; exact hBound i
        _ = q l.val * (1 / 2 : ℝ) ^ (ν i + 1) := by rw [one_div_pow, div_eq_mul_inv, one_div]
    change p x ≤ q l.val
    calc
      p x ≤ ∑ i ∈ x.support, ‖x i‖ * p (Finsupp.single i 1) := by
        conv_lhs => rw [hRep]
        apply (Finset.le_sum_of_subadditive p (map_zero p).le (map_add_le_add p) _ _).trans
        exact le_of_eq (Finset.sum_congr rfl fun i _ ↦ map_smul_eq_mul _ _ _)
      _ ≤ ∑ i ∈ x.support, q l.val * (1 / 2 : ℝ) ^ (ν i + 1) := Finset.sum_le_sum fun i _ ↦ hweight i
      _ = q l.val * ∑ i ∈ x.support, (1 / 2 : ℝ) ^ (ν i + 1) := (Finset.mul_sum _ _ _).symm
      _ ≤ q l.val * 1 := mul_le_mul_of_nonneg_left (sum_half_pow_succ_le_one x.support ν hν)
        (apply_nonneg q _)
      _ = q l.val := mul_one _
  refine ⟨⟨e, hForward, hInverse⟩, fun i ↦ ?_⟩
  change (T (Finsupp.single i 1)).val = _
  have he : T (Finsupp.single i 1) = w i :=
    (Finsupp.linearCombination_single ℂ (v := w) 1 i).trans (one_smul ℂ _)
  exact congrArg Subtype.val he

open Classical in
/-- A Schwartz–Bergman representative with the same divisor supplies
compact-open representatives of the raw derivative coordinates. -/
theorem compactOpenEntireAnnihilator_finiteSupportEquiv_of_bergman
    (g : CompactOpenEntire) (hfinite : ∀ z, analyticOrderAt (g.val : ℂ → ℂ) z ≠ ⊤)
    (b : SchwartzBergman (univ : Set ℝ))
    (hb : ∀ z, analyticOrderAt b.val z = analyticOrderAt (g.val : ℂ → ℂ) z) :
    letI : TopologicalSpace (JetIndex g →₀ ℂ) := finestLocallyConvexTopology _
    ∃ e : (JetIndex g →₀ ℂ) ≃L[ℂ] compactOpenEntireAnnihilator g.val,
      ∀ i, (e (Finsupp.single i 1)).val = compactOpenEntireJet i.val.1 i.val.2 := by
  have hg : ∃ z, g.val z ≠ 0 := by
    by_contra! h
    exact hfinite 0 (analyticOrderAt_eq_top.mpr (Eventually.of_forall h))
  apply compactOpenEntireAnnihilator_finiteSupportEquiv g hg
  intro i
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (hfinite i.val.1)
  obtain ⟨f, hf⟩ := bergmanDivisor_normalizedJet_biorthogonal b i.val.1 n i.val.2
    ((hb i.val.1).trans hn.symm)
  refine ⟨(i.val.2.factorial : ℂ)⁻¹ • bergmanToCompactOpenEntire f, fun j ↦ ?_⟩
  have hj := hf j.val.1 j.val.2 (by rw [hb]; exact j.property)
  have hEq : (j.val.1 = i.val.1 ∧ j.val.2 = i.val.2) ↔ j = i := by
    rw [Subtype.ext_iff, Prod.ext_iff]
  have hj' : (j.val.2.factorial : ℂ)⁻¹ * iteratedDeriv j.val.2 f.val j.val.1 =
      if j = i then 1 else 0 := by
    simpa only [hEq, bergmanNormalizedJet_apply] using hj
  have hfn (k : ℕ) : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  have hfun : ((bergmanToCompactOpenEntire f).val : ℂ → ℂ) = f.val := funext
    (bergmanToCompactOpenEntire_apply f)
  change (compactOpenEntireJet j.val.1 j.val.2) (_ • _) = _
  rw [map_smul, smul_eq_mul, compactOpenEntireJet_apply, hfun]
  by_cases he : j = i
  · subst j
    exact hj'
  · rw [ite_eq_right he] at hj' ⊢
    rw [(mul_eq_zero.mp hj').resolve_left (inv_ne_zero (hfn _)), mul_zero]

#print axioms compactOpenEntireAnnihilator_le_span_jets
#print axioms compactOpenEntireAnnihilator_finiteSupportEquiv
#print axioms compactOpenEntireAnnihilator_finiteSupportEquiv_of_bergman

end

end Masullo
