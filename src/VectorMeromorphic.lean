import RemovableWeakSingularities
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Topology.DiscreteSubset

open Filter Function Set Topology
open scoped BigOperators

namespace Masullo

noncomputable section

variable {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]

/-- C.5.2.6, equation (C.5.2.6). Scalar derivatives of a weakly
holomorphic function define a unique element of the algebraic dual of its
continuous dual. Adapted from the Apache-2.0 RiemannMasullo proof at 077b53b. -/
theorem weaklyHolomorphic_existsUnique_weakDerivative {f : ℂ → E} {U : Set ℂ}
    (hU : IsOpen U) (hf : ∀ ℓ : StrongDual ℂ E, DifferentiableOn ℂ (ℓ ∘ f) U)
    {z : ℂ} (hz : z ∈ U) (k : ℕ) :
    ∃! D : Module.Dual ℂ (StrongDual ℂ E), ∀ ℓ : StrongDual ℂ E,
      D ℓ = iteratedDeriv k (ℓ ∘ f) z := by
  have hs (ℓ : StrongDual ℂ E) : ContDiffAt ℂ k (ℓ ∘ f) z :=
    ((hf ℓ).contDiffOn hU).contDiffAt (hU.mem_nhds hz)
  let D : Module.Dual ℂ (StrongDual ℂ E) :=
    { toFun := fun ℓ => iteratedDeriv k (ℓ ∘ f) z
      map_add' := fun ℓ m => by
        change iteratedDeriv k ((ℓ ∘ f) + (m ∘ f)) z = _
        exact iteratedDeriv_add (hs ℓ) (hs m)
      map_smul' := fun c ℓ => by
        change iteratedDeriv k (c • (ℓ ∘ f)) z = _
        exact iteratedDeriv_const_smul_field c (ℓ ∘ f) }
  exact ⟨D, fun _ => rfl, fun D' hD' => LinearMap.ext hD'⟩

/-- On any closed disc contained in the domain, scalar evaluations of the
weak derivative in C.5.2.6 are given by Cauchy's integral formula.
Adapted from the Apache-2.0 RiemannMasullo proof at 4f78774. -/
theorem weaklyHolomorphic_existsUnique_weakDerivative_circle {f : ℂ → E}
    {U : Set ℂ} (hU : IsOpen U) (hf : ∀ ℓ : StrongDual ℂ E,
      DifferentiableOn ℂ (ℓ ∘ f) U) {z : ℂ} {R : ℝ} (hR : 0 < R)
    (hball : Metric.closedBall z R ⊆ U) (k : ℕ) :
    ∃ D : Module.Dual ℂ (StrongDual ℂ E),
      ∀ ℓ : StrongDual ℂ E,
        D ℓ = iteratedDeriv k (ℓ ∘ f) z ∧
        circleIntegral (fun w ↦ (1 / (w - z) ^ (k + 1)) * ℓ (f w)) z R =
          (2 * (Real.pi : ℂ) * Complex.I / k.factorial) * D ℓ := by
  obtain ⟨D, hD, _⟩ := weaklyHolomorphic_existsUnique_weakDerivative hU hf
    (hball (Metric.mem_closedBall_self hR.le)) k
  refine ⟨D, fun ℓ ↦ ⟨hD ℓ, ?_⟩⟩
  simpa only [hD, smul_eq_mul, Function.comp_apply] using
    (hf ℓ).mono hball |>.circleIntegral_one_div_sub_center_pow_smul hR k

/-- The finite-pole condition of Definition C.5.3.1 in its pole-clearing
form. The extension is tested by all continuous scalar evaluations. -/
def WeakVectorMeromorphic (f : ℂ → E) (U D : Set ℂ) : Prop :=
  IsOpen (U \ D) ∧
    (∀ ℓ : StrongDual ℂ E, DifferentiableOn ℂ (fun z => ℓ (f z)) (U \ D)) ∧
    ∀ x ∈ U ∩ D, ∃ (N : ℕ) (g : ℂ → E),
      (∀ ℓ : StrongDual ℂ E, AnalyticAt ℂ (fun z => ℓ (g z)) x) ∧
      (fun z => (z - x) ^ N • f z) =ᶠ[𝓝[≠] x] g

private theorem WeakVectorMeromorphic.scalar_meromorphicOn {f : ℂ → E} {U D : Set ℂ}
    (hf : WeakVectorMeromorphic f U D) (ℓ : StrongDual ℂ E) :
    MeromorphicOn (fun z => ℓ (f z)) U := by
  intro x hx
  by_cases hD : x ∈ D
  · obtain ⟨N, g, hg, hEq⟩ := hf.2.2 x ⟨hx, hD⟩
    apply MeromorphicAt.iff_eventuallyEq_zpow_smul_analyticAt.mpr
    refine ⟨-(N : ℤ), fun z => ℓ (g z), hg ℓ, ?_⟩
    filter_upwards [hEq, self_mem_nhdsWithin] with z hz hne
    have hzx : z - x ≠ 0 := sub_ne_zero.mpr (fun he => hne (mem_singleton_iff.mpr he))
    rw [← hz, map_smul, smul_smul, zpow_neg, zpow_natCast, inv_mul_cancel₀ (pow_ne_zero _ hzx), one_smul]
  · exact ((hf.2.1 ℓ).analyticOnNhd hf.1 x ⟨hx, hD⟩).meromorphicAt

/-- Lemma C.5.4.3. The vector-valued identity theorem follows by applying
the scalar meromorphic identity theorem throughout the connected domain. -/
theorem vector_meromorphic_eqOn_of_open_disc [T2Space E] [PolynormableSpace ℂ E]
    {f g : ℂ → E} {U D₁ D₂ B : Set ℂ}
    (hU : IsPreconnected U) (hf : WeakVectorMeromorphic f U D₁)
    (hg : WeakVectorMeromorphic g U D₂)
    (hB : IsOpen B) (hBne : B.Nonempty) (hBU : B ⊆ U \ (D₁ ∪ D₂)) (heq : EqOn f g B) :
    EqOn f g (U \ (D₁ ∪ D₂)) := by
  obtain ⟨b, hb⟩ := hBne
  intro x hx
  apply (weakBidualEval_isEmbedding E).injective
  change (weakBidualEval E (f x) : Module.Dual ℂ (StrongDual ℂ E)) =
    (weakBidualEval E (g x) : Module.Dual ℂ (StrongDual ℂ E))
  refine DFunLike.ext (F := Module.Dual ℂ (StrongDual ℂ E)) _ _ fun ℓ => ?_
  change ℓ (f x) = ℓ (g x)
  let q (z : ℂ) := ℓ (f z) - ℓ (g z)
  have hq : MeromorphicOn q U := (hf.scalar_meromorphicOn ℓ).sub (hg.scalar_meromorphicOn ℓ)
  have hzero : meromorphicOrderAt q b = ⊤ := by
    apply meromorphicOrderAt_eq_top_iff.mpr
    filter_upwards [mem_nhdsWithin_of_mem_nhds (hB.mem_nhds hb)] with z hz
    simp only [q, heq hz, sub_self]
  have horder : meromorphicOrderAt q x = ⊤ := by
    by_contra hn
    exact (hq.meromorphicOrderAt_ne_top_of_isPreconnected hU hx.1 (hBU hb).1 hn) hzero
  have hc : ContinuousAt q x := by
    have h₁ : x ∈ U \ D₁ := ⟨hx.1, fun h => hx.2 (Or.inl h)⟩
    have h₂ : x ∈ U \ D₂ := ⟨hx.1, fun h => hx.2 (Or.inr h)⟩
    exact ((hf.2.1 ℓ x h₁).differentiableAt (hf.1.mem_nhds h₁)).continuousAt.sub
      ((hg.2.1 ℓ x h₂).differentiableAt (hg.1.mem_nhds h₂)).continuousAt
  have hl : q =ᶠ[𝓝[≠] x] (fun _ => 0) := meromorphicOrderAt_eq_top_iff.mp horder
  have hloc := (hc.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE continuousAt_const).mp hl
  exact sub_eq_zero.mp hloc.eq_of_nhds

/-- A pole of order two where the limit in (C.5.3.8) fails to exist. -/
theorem printed_double_pole_residue_limit_fails :
    let f : ℂ → ℂ := fun z => (z ^ 2)⁻¹ + z⁻¹
    meromorphicOrderAt f 0 = (-2 : ℤ) ∧
      ¬ ∃ c : ℂ, Tendsto (deriv (fun z => z * f z)) (𝓝[≠] 0) (𝓝 c) := by
  dsimp only
  let f : ℂ → ℂ := fun z => (z ^ 2)⁻¹ + z⁻¹
  let g : ℂ → ℂ := fun z => 1 + z
  have hg : AnalyticAt ℂ g 0 := by fun_prop
  have hEq : f =ᶠ[𝓝[≠] (0 : ℂ)] (fun z => (z - 0) ^ (-2 : ℤ) • g z) := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hn : z ≠ 0 := fun h => hz (mem_singleton_iff.mpr h)
    simp only [f, g, sub_zero, show (-2 : ℤ) = -(↑(2 : ℕ) : ℤ) by norm_num,
      zpow_neg, zpow_natCast, smul_eq_mul]
    field_simp [hn]
  have hm : MeromorphicAt f 0 :=
    MeromorphicAt.iff_eventuallyEq_zpow_smul_analyticAt.mpr ⟨-2, g, hg, hEq⟩
  refine ⟨(meromorphicOrderAt_eq_int_iff hm).mpr ⟨g, hg, by simp [g], hEq⟩, ?_⟩
  rintro ⟨c, hc⟩
  have hform (z : ℂ) (hz : z ≠ 0) : deriv (fun w => w * f w) z = -(z ^ 2)⁻¹ := by
    apply HasDerivAt.deriv
    have hL := (hasDerivAt_inv hz).add_const 1
    apply hL.congr_of_eventuallyEq
    filter_upwards [eventually_ne_nhds hz] with w hw
    dsimp [f]
    field_simp [hw]
  have hZ : Tendsto (fun z : ℂ => z ^ 2) (𝓝[≠] 0) (𝓝 0) := by
    have h : Continuous (fun z : ℂ => z ^ 2) := by fun_prop
    simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0)] using
      (h.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
  have h := hZ.mul hc
  rw [zero_mul] at h
  have he : (fun _ : ℂ => (-1 : ℂ)) =ᶠ[𝓝[≠] (0 : ℂ)]
      (fun z => z ^ 2 * deriv (fun w => w * f w) z) := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hn : z ≠ 0 := fun hz' => hz (mem_singleton_iff.mpr hz')
    rw [hform z hn, mul_neg, mul_inv_cancel₀ (pow_ne_zero _ hn)]
  have hf : Tendsto (fun z => z ^ 2 * deriv (fun w => w * f w) z)
      (𝓝[≠] 0) (𝓝 (-1 : ℂ)) := tendsto_const_nhds.congr' he
  exact (by norm_num : (0 : ℂ) ≠ -1) (tendsto_nhds_unique h hf)

section Laurent

variable {F : Type*} [AddCommGroup F] [Module ℂ F] [UniformSpace F] [IsUniformAddGroup F]

/-- A local Laurent expansion (C.5.3.2) converges uniformly on compact
subsets of a punctured disc. Its signed lower bound is as in (C.5.3.4). -/
def HasVectorLaurentSeriesAt (f : ℂ → F) (z : ℂ) (a : ℤ → F) : Prop :=
  ∃ (N : ℤ) (r : ℝ), 0 < r ∧ (∀ k < N, a k = 0) ∧
    ∀ K : Set ℂ, K ⊆ Metric.ball z r \ {z} → IsCompact K →
      TendstoUniformlyOn
        (fun n w ↦ ∑ j ∈ Finset.range n, (w - z) ^ (N + (j : ℤ)) • a (N + (j : ℤ)))
        f atTop K

/-- On a circle in the punctured disc, integrating a scalar evaluation of the
Laurent expansion against the local coordinate to the power `-k - 1` gives
`2πi` times the scalar evaluation of the coefficient at `k`. -/
private theorem circleIntegral_of_laurent_convergence {f : ℂ → F} {z : ℂ} {a : ℤ → F}
    {N : ℤ} {r R : ℝ} (hR : 0 < R) (hRr : R < r) (hzero : ∀ k < N, a k = 0)
    (hconv : ∀ K : Set ℂ, K ⊆ Metric.ball z r \ {z} → IsCompact K →
      TendstoUniformlyOn
        (fun n w ↦ ∑ j ∈ Finset.range n, (w - z) ^ (N + (j : ℤ)) • a (N + (j : ℤ)))
        f atTop K)
    (φ : StrongDual ℂ F) (k : ℤ) :
    circleIntegral (fun w ↦ (w - z) ^ (-k - 1) * φ (f w)) z R =
      (2 * (Real.pi : ℂ) * Complex.I) * φ (a k) := by
  have hne (w : ℂ) (hw : w ∈ Metric.sphere z R) : w - z ≠ 0 :=
    sub_ne_zero.mpr (Metric.ne_of_mem_sphere hw hR.ne')
  have hsub : Metric.sphere z R ⊆ Metric.ball z r \ {z} := by
    intro w hw
    exact ⟨Metric.mem_ball.mpr ((Metric.mem_sphere.mp hw).trans_lt hRr),
      sub_ne_zero.mp (hne w hw)⟩
  have hscalar := φ.uniformContinuous.comp_tendstoUniformlyOn
    (hconv _ hsub (isCompact_sphere z R))
  let term (j : ℕ) (w : ℂ) := (w - z) ^ (N + (j : ℤ) - k - 1) • φ (a (N + (j : ℤ)))
  have hterm (j : ℕ) : ContinuousOn (term j) (Metric.sphere z R) :=
    ((continuousOn_id.sub continuousOn_const).zpow₀ _ fun w hw ↦ Or.inl (hne w hw)).smul
      continuousOn_const
  have hweighted : TendstoUniformlyOn (fun n w ↦ ∑ j ∈ Finset.range n, term j w)
      (fun w ↦ (w - z) ^ (-k - 1) * φ (f w)) atTop (Metric.sphere z R) := by
    rw [Metric.tendstoUniformlyOn_iff] at hscalar ⊢
    intro ε hε
    have hbound : 0 < R ^ (-k - 1) := zpow_pos hR _
    filter_upwards [hscalar (ε / R ^ (-k - 1)) (div_pos hε hbound)] with n hn w hw
    have hsum :
        ∑ j ∈ Finset.range n, term j w =
          (w - z) ^ (-k - 1) * φ (∑ j ∈ Finset.range n,
            (w - z) ^ (N + (j : ℤ)) • a (N + (j : ℤ))) := by
      rw [map_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      have hexp : N + (j : ℤ) - k - 1 = (-k - 1) + (N + (j : ℤ)) := by omega
      simp [term, hexp, zpow_add₀ (hne w hw), smul_eq_mul, mul_assoc]
    have hnorm : ‖w - z‖ = R := by simpa only [dist_eq_norm] using Metric.mem_sphere.mp hw
    rw [hsum, dist_eq_norm, ← mul_sub, norm_mul, norm_zpow, hnorm, ← dist_eq_norm,
      ← lt_div_iff₀' hbound]
    exact hn w hw
  have hlim := hweighted.tendsto_circleIntegral_of_continuousOn hR.le
    (Eventually.of_forall fun n ↦ continuousOn_finsetSum _ fun j _ ↦ hterm j)
  have hintegral (j : ℕ) : circleIntegral (term j) z R =
      if N + (j : ℤ) = k then (2 * (Real.pi : ℂ) * Complex.I) * φ (a k) else 0 := by
    dsimp only [term]
    rw [circleIntegral.integral_smul_const]
    split_ifs with hj
    · rw [hj, show k - k - 1 = (-1 : ℤ) by omega]
      simp only [zpow_neg_one, circleIntegral.integral_sub_center_inv z hR.ne', smul_eq_mul]
    · have hpow : N + (j : ℤ) - k - 1 ≠ -1 := by omega
      rw [circleIntegral.integral_sub_zpow_of_ne hpow z z R, zero_smul]
  -- Only the summand whose exponent is shifted to minus one contributes.
  have heventual : ∀ᶠ n : ℕ in atTop, circleIntegral (fun w ↦ ∑ j ∈ Finset.range n, term j w)
      z R = (2 * (Real.pi : ℂ) * Complex.I) * φ (a k) := by
    filter_upwards [eventually_gt_atTop (k - N).toNat] with n hn
    rw [circleIntegral.integral_fun_sum fun j _ ↦ ContinuousOn.circleIntegrable hR.le (hterm j)]
    simp only [hintegral]
    by_cases hk : N ≤ k
    · have hj : N + ((k - N).toNat : ℤ) = k := by omega
      rw [Finset.sum_eq_single (k - N).toNat]
      · rw [ite_eq_left hj]
      · intro j _ hj'
        have : N + (j : ℤ) ≠ k := by omega
        simp [this]
      · exact fun h ↦ (h (Finset.mem_range.mpr hn)).elim
    · have hak : a k = 0 := hzero k (lt_of_not_ge hk)
      have hj (j : ℕ) : N + (j : ℤ) ≠ k := by omega
      simp [hj, hak]
  exact tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (heventual.mono fun _ hn ↦ hn.symm))

/-- The scalar evaluations of the coefficient in (C.5.3.3) agree with the
normalized circle integral on every sufficiently small circle. The proof
adapts RiemannMasullo commit 423083a (Apache-2.0). -/
theorem HasVectorLaurentSeriesAt.eventually_circleIntegral_coeff {f : ℂ → F} {z : ℂ}
    {a : ℤ → F} (ha : HasVectorLaurentSeriesAt f z a) :
    ∃ r > 0, ∀ R, 0 < R → R < r → ∀ (φ : StrongDual ℂ F) (k : ℤ),
      circleIntegral (fun w => (w - z) ^ (-k - 1) * φ (f w)) z R =
        (2 * (Real.pi : ℂ) * Complex.I) * φ (a k) := by
  obtain ⟨N, r, hr, hzero, hconv⟩ := ha
  exact ⟨r, hr, fun _ hR hRr => circleIntegral_of_laurent_convergence hR hRr hzero hconv⟩

/-- The local Laurent expansion uniquely determines its vector coefficients. -/
theorem HasVectorLaurentSeriesAt.coeff_unique [T2Space F] [PolynormableSpace ℂ F]
    {f : ℂ → F} {z : ℂ} {a b : ℤ → F} (ha : HasVectorLaurentSeriesAt f z a)
    (hb : HasVectorLaurentSeriesAt f z b) : a = b := by
  obtain ⟨r, hr, hca⟩ := ha.eventually_circleIntegral_coeff
  obtain ⟨s, hs, hcb⟩ := hb.eventually_circleIntegral_coeff
  let R := min r s / 2
  have hR : 0 < R := half_pos (lt_min hr hs)
  have hRmin : R < min r s := half_lt_self (lt_min hr hs)
  have hfactor : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
  funext k
  apply (weakBidualEval_isEmbedding F).injective
  change (weakBidualEval F (a k) : Module.Dual ℂ (StrongDual ℂ F)) =
    (weakBidualEval F (b k) : Module.Dual ℂ (StrongDual ℂ F))
  refine DFunLike.ext (F := Module.Dual ℂ (StrongDual ℂ F)) _ _ fun φ => ?_
  exact mul_left_cancel₀ hfactor
    ((hca R hR (hRmin.trans_le (min_le_left r s)) φ k).symm.trans
      (hcb R hR (hRmin.trans_le (min_le_right r s)) φ k))

/-- A continuous linear map sends the coefficients of a locally uniformly
convergent vector Laurent expansion to those of the composed function.
This proves the coefficient identity used for residues in C.5.3.3(4).
Adapted from the Apache-2.0 RiemannMasullo proof at 4f78774. -/
theorem HasVectorLaurentSeriesAt.continuousLinearMap_comp
    {H : Type*} [AddCommGroup H] [Module ℂ H] [UniformSpace H] [IsUniformAddGroup H]
    {f : ℂ → F} {z : ℂ} {a : ℤ → F} (ha : HasVectorLaurentSeriesAt f z a)
    (T : F →L[ℂ] H) : HasVectorLaurentSeriesAt (T ∘ f) z (T ∘ a) := by
  obtain ⟨N, r, hr, hzero, hconv⟩ := ha
  refine ⟨N, r, hr, fun k hk ↦ ?_, fun K hK hc ↦ ?_⟩
  · simp [hzero k hk]
  · have hseries n :
        T ∘ (fun w ↦ ∑ j ∈ Finset.range n, (w - z) ^ (N + (j : ℤ)) • a (N + (j : ℤ))) =
          (fun w ↦ ∑ j ∈ Finset.range n, (w - z) ^ (N + (j : ℤ)) • T (a (N + (j : ℤ)))) := by
      funext w
      simp only [Function.comp_apply, map_sum, map_smul]
    simpa only [hseries, Function.comp_apply] using
      T.uniformContinuous.comp_tendstoUniformlyOn (hconv K hK hc)

/-- The denominator in the Taylor kernel accounts for the power used to clear the pole. -/
theorem laurentKernel_mul_pow {x : ℂ} (hx : x ≠ 0) (n j : ℕ) :
    (x ^ (j + 1))⁻¹ * x ^ n = x ^ (-((j : ℤ) - n) - 1) := by
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_neg, ← zpow_add₀ hx]
  congr 1
  omega

/-- Clearing a pole shifts the Laurent exponent `j - n` to the Taylor exponent `j`. -/
theorem HasVectorLaurentSeriesAt.coeff_eq_derivative_of_cleared
    {f : ℂ → F} {z : ℂ} {a : ℤ → F}
    (ha : HasVectorLaurentSeriesAt f z a) (φ : StrongDual ℂ F) (n j : ℕ)
    {q : ℂ → ℂ} {s : ℝ} (hs : 0 < s) (hq : DifferentiableOn ℂ q (Metric.ball z s))
    (heq : EqOn q (fun w ↦ (w - z) ^ n * φ (f w)) (Metric.ball z s \ {z})) :
    φ (a ((j : ℤ) - n)) = iteratedDeriv j q z / (j.factorial : ℂ) := by
  obtain ⟨r, hr, hlocal⟩ := ha.eventually_circleIntegral_coeff
  let R := min r s / 2
  have hR : 0 < R := half_pos (lt_min hr hs)
  have hRr : R < r := (half_lt_self (lt_min hr hs)).trans_le (min_le_left _ _)
  have hRs : R < s := (half_lt_self (lt_min hr hs)).trans_le (min_le_right _ _)
  have hcauchy := DifferentiableOn.circleIntegral_one_div_sub_center_pow_smul hR j
    (hq.mono (Metric.closedBall_subset_ball hRs))
  have hlocal := hlocal R hR hRr φ ((j : ℤ) - n)
  have hkernel := circleIntegral.integral_congr (c := z) hR.le
    (f := fun w ↦ (w - z) ^ (-((j : ℤ) - n) - 1) * φ (f w))
    (g := fun w ↦ (1 / (w - z) ^ (j + 1)) • q w) (by
      intro w hw
      have hwz := Metric.ne_of_mem_sphere hw hR.ne'
      dsimp only
      rw [smul_eq_mul, one_div, heq ⟨Metric.mem_ball.mpr ((Metric.mem_sphere.mp hw).trans_lt hRs), hwz⟩]
      dsimp only
      rw [← mul_assoc, laurentKernel_mul_pow (sub_ne_zero.mpr hwz)])
  rw [← hkernel, hlocal, smul_eq_mul, div_mul_eq_mul_div, mul_div_assoc] at hcauchy
  exact mul_left_cancel₀
    (mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero) hcauchy

end Laurent

section VectorRemoval

open Bornology

variable {F : Type*} [AddCommGroup F] [Module ℂ F] [Module ℝ F] [IsScalarTower ℝ ℂ F]
  [UniformSpace F] [IsUniformAddGroup F] [T2Space F] [ContinuousSMul ℂ F]
  [PolynormableSpace ℂ F] [QuasiCompleteSpace ℂ F]

private theorem vector_removable_disk (f : ℂ → F) {U : Set ℂ} (hU : IsOpen U)
    {x : ℂ} (hx : x ∈ U)
    (holo : ∀ ℓ : StrongDual ℂ F, DifferentiableOn ℂ (fun z => ℓ (f z)) (U \ {x}))
    (hbounded : IsVonNBounded ℂ (f '' (U \ {x}))) :
    ∃ H : ℂ → F, EqOn H f (U \ {x}) ∧ ContinuousOn H U ∧
      ∀ ℓ : StrongDual ℂ F, DifferentiableOn ℂ (fun z => ℓ (H z)) U := by
  classical
  let g (ℓ : StrongDual ℂ F) :=
    Function.update (fun z => ℓ (f z)) x (limUnder (𝓝[≠] x) (fun z => ℓ (f z)))
  have hg (ℓ : StrongDual ℂ F) : DifferentiableOn ℂ (g ℓ) U := by
    apply Complex.differentiableOn_update_limUnder_of_bddAbove (hU.mem_nhds hx) (holo ℓ)
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp
      ((isVonNBounded_iff_dual_images _).mp hbounded ℓ)
    refine ⟨C, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    exact hC _ ⟨f z, mem_image_of_mem f hz, rfl⟩
  have hderiv (ℓ : StrongDual ℂ F) (z : ℂ) (hz : z ∈ U) :
      HasDerivAt (g ℓ) (deriv (g ℓ) z) z :=
    ((hg ℓ z hz).differentiableAt (hU.mem_nhds hz)).hasDerivAt
  have hd (ℓ : StrongDual ℂ F) : ContinuousOn (deriv (g ℓ)) U :=
    ((hg ℓ).contDiffOn (n := 2) hU |>.deriv_of_isOpen (m := 1) hU le_rfl).continuousOn
  obtain ⟨H, hH, hEq, _, hD, _, _⟩ := removable_weak_singularity hU hx f g
    (fun ℓ => deriv (g ℓ))
    (fun ℓ z hz => by
      change ℓ (f z) = g ℓ z
      dsimp only [g]
      rw [Function.update_of_ne (fun h => hz.2 (mem_singleton_iff.mpr h))]) hderiv hd
  exact ⟨H, hEq, hH, fun ℓ z hz => ((hD ℓ).2 z hz).differentiableAt.differentiableWithinAt⟩

/-- Lemma C.5.4.2. Locally bounded vector-valued holomorphic functions
extend uniquely across a relatively closed discrete omitted set. -/
theorem vector_removable_discrete (f : ℂ → F) {U D : Set ℂ}
    (hU : IsOpen U) (hreg : IsOpen (U \ D)) (hD : IsDiscrete D)
    (holo : ∀ ℓ : StrongDual ℂ F, DifferentiableOn ℂ (fun z => ℓ (f z)) (U \ D))
    (hbound : ∀ x ∈ U, ∃ W : Set ℂ, IsOpen W ∧ x ∈ W ∧ W ⊆ U ∧
      IsVonNBounded ℂ (f '' (W \ D))) :
    ∃! H : U → F, (∀ z : U, z.val ∉ D → H z = f z) ∧
      ∃ G : ℂ → F, (∀ z : U, H z = G z) ∧ ContinuousOn G U ∧
        ∀ ℓ : StrongDual ℂ F, DifferentiableOn ℂ (fun z => ℓ (G z)) U := by
  classical
  have hlocal (x : ℂ) (hx : x ∈ U ∩ D) :
      ∃ (V : Set ℂ) (G : ℂ → F), IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧
        V ∩ D = {x} ∧ EqOn G f (V \ D) ∧
        ∀ ℓ : StrongDual ℂ F, DifferentiableOn ℂ (fun z => ℓ (G z)) V := by
    obtain ⟨O, hO, hOD⟩ := isDiscrete_iff_forall_mem_exists_isOpen.mp hD x hx.2
    obtain ⟨W, hW, hxW, hWU, hWbdd⟩ := hbound x hx.1
    let V := O ∩ W
    have hxO : x ∈ O := (show x ∈ O ∩ D by rw [hOD]; exact mem_singleton x).1
    have hV : IsOpen V := hO.inter hW
    have hxV : x ∈ V := ⟨hxO, hxW⟩
    have hVD : V ∩ D = {x} := by
      ext z
      refine ⟨fun hz => hOD ▸ (show z ∈ O ∩ D from ⟨hz.1.1, hz.2⟩), fun hz => ?_⟩
      obtain rfl := mem_singleton_iff.mp hz
      exact ⟨hxV, hx.2⟩
    have he : V \ {x} = V \ D := by
      ext z
      exact ⟨fun hz => ⟨hz.1, fun hzD => hz.2 (hVD ▸ (show z ∈ V ∩ D from ⟨hz.1,hzD⟩))⟩,
        fun hz => ⟨hz.1, fun hzx => hz.2 ((show z ∈ V ∩ D from hVD.symm ▸ hzx).2)⟩⟩
    have hs : V \ D ⊆ W \ D := fun _ hz => ⟨hz.1.2, hz.2⟩
    obtain ⟨G, hG, _, hdiff⟩ := vector_removable_disk f hV hxV
      (fun ℓ => by rw [he]; exact (holo ℓ).mono (fun _ hz => ⟨hWU hz.1.2, hz.2⟩))
      (by rw [he]; exact hWbdd.subset (image_mono hs))
    exact ⟨V, G, hV, hxV, inter_subset_right.trans hWU, hVD, he ▸ hG, hdiff⟩
  choose V G hV hxV hVU hVD hEq hhol using hlocal
  let H (z : ℂ) := if hz : z ∈ U ∩ D then G z hz z else f z
  have hH (z : ℂ) (hz : z ∉ D) : H z = f z :=
    dite_eq_right (fun h : z ∈ U ∩ D => hz h.2)
  have hloc (x : ℂ) (hx : x ∈ U ∩ D) : EqOn H (G x hx) (V x hx) := by
    intro y hy
    by_cases hyD : y ∈ D
    · have hyx : y = x := mem_singleton_iff.mp (hVD x hx ▸ (show y ∈ V x hx ∩ D from ⟨hy,hyD⟩))
      subst y
      exact dite_eq_left hx
    · exact (hH _ hyD).trans (hEq x hx ⟨hy, hyD⟩).symm
  have hHol (ℓ : StrongDual ℂ F) : DifferentiableOn ℂ (fun z => ℓ (H z)) U := by
    intro x hx
    apply DifferentiableAt.differentiableWithinAt
    by_cases hxD : x ∈ D
    · have hxUD : x ∈ U ∩ D := ⟨hx, hxD⟩
      have hN := (hV x hxUD).mem_nhds (hxV x hxUD)
      exact ((hhol x hxUD ℓ x (hxV x hxUD)).differentiableAt hN).congr_of_eventuallyEq <|
        (eventually_mem_set.mpr hN).mono (fun y hy => congrArg ℓ (hloc x hxUD hy))
    · have hN := hreg.mem_nhds (show x ∈ U \ D from ⟨hx, hxD⟩)
      exact ((holo ℓ x ⟨hx, hxD⟩).differentiableAt hN).congr_of_eventuallyEq <|
        (eventually_mem_set.mpr hN).mono (fun y hy => congrArg ℓ (hH y hy.2))
  have hd (ℓ : StrongDual ℂ F) : ContinuousOn (fderiv ℂ (fun z => ℓ (H z))) U :=
    (hHol ℓ).contDiffOn (n := 1) hU |>.continuousOn_fderiv_of_isOpen hU le_rfl
  have hC : ContinuousOn H U := continuousOn_of_continuous_weakDifferential hU H
    (fun ℓ => fderiv ℂ (fun z => ℓ (H z)))
    (fun ℓ z hz => ((hHol ℓ z hz).differentiableAt (hU.mem_nhds hz)).hasFDerivAt)
    (fun ℓ => ((hd ℓ).comp continuous_fst.continuousOn (fun _ h => h.1)).clm_apply
      continuous_snd.continuousOn)
  refine ⟨fun z => H z, ⟨fun z => hH z, H, fun _ => rfl, hC, hHol⟩, ?_⟩
  rintro H' ⟨hH', G', hHG', hG', _⟩
  funext z
  rw [hHG' z]
  by_cases hz : z.val ∈ D
  · let x := z.val
    have hx : x ∈ U ∩ D := ⟨z.property, hz⟩
    have hN : V x hx ∈ 𝓝 x := (hV x hx).mem_nhds (hxV x hx)
    have he : G' =ᶠ[𝓝[≠] x] H := by
      filter_upwards [mem_nhdsWithin_of_mem_nhds hN, self_mem_nhdsWithin] with y hyV hyx
      have hyD : y ∉ D := fun hyD => hyx (hVD x hx ▸ (show y ∈ V x hx ∩ D from ⟨hyV, hyD⟩))
      let yU : U := ⟨y, hVU x hx hyV⟩
      exact (hHG' yU).symm.trans ((hH' yU hyD).trans (hH y hyD).symm)
    have h₁ := ((hU.continuousOn_iff.mp hG') z.property).tendsto.mono_left
      (nhdsWithin_le_nhds (s := {x}ᶜ))
    have h₂ := ((hU.continuousOn_iff.mp hC) z.property).tendsto.mono_left
      (nhdsWithin_le_nhds (s := {x}ᶜ))
    exact tendsto_nhds_unique (h₁.congr' he) h₂
  · exact (hHG' z).symm.trans ((hH' z hz).trans (hH z hz).symm)

end VectorRemoval

end

end Masullo
