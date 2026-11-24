import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.LocallyConvex.WeakDual
import Mathlib.Analysis.LocallyConvex.Barrelled
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import Mathlib.Analysis.LocallyConvex.StrongTopology
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.MetricSpace.Equicontinuity

/-!
# Duality of absolute Schauder bases

Adapted from `RiemannMasullo/Ch04_PeriodicSchauderBases/Sec1.lean` at
cd84b23dd5e4f741037cf31aee06bc90161c6514 under Apache-2.0.
-/

open Bornology Filter Function Set Topology ContinuousLinearMap
open scoped Classical Pointwise

namespace Masullo

noncomputable section

/-- A point outside a closed submodule is detected by a continuous functional
that vanishes on the submodule. -/
theorem exists_dual_eq_zero_on_submodule_of_notMem {𝕜 E : Type*} [RCLike 𝕜] [AddCommGroup E]
    [Module ℝ E] [Module 𝕜 E] [IsScalarTower ℝ 𝕜 E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [LocallyConvexSpace ℝ E]
    (S : Submodule 𝕜 E) (hS : IsClosed (S : Set E)) {x : E} (hx : x ∉ S) :
    ∃ φ : StrongDual 𝕜 E, φ x ≠ 0 ∧ ∀ y ∈ S, φ y = 0 := by
  obtain ⟨φ, r, hl, hr⟩ := RCLike.geometric_hahn_banach_closed_point (𝕜 := 𝕜)
    (S.restrictScalars ℝ).convex hS hx
  have hne : φ x ≠ 0 := by
    intro h
    simpa [h] using (hl 0 S.zero_mem).trans hr
  refine ⟨φ, hne, fun y hy ↦ ?_⟩
  by_contra h
  have hlt := (hl _ (S.smul_mem (φ x / φ y) hy)).trans hr
  simp [map_smul, smul_eq_mul, h] at hlt

open scoped Pointwise in
/-- The weak-dual polar of a zero-neighborhood in a topological vector space over a
proper normed field is compact. -/
private theorem isCompact_weakDual_polar {𝕜 X : Type*} [NontriviallyNormedField 𝕜] [ProperSpace 𝕜]
    [AddCommGroup X] [Module 𝕜 X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    [ContinuousSMul 𝕜 X] {U : Set X} (hU : U ∈ 𝓝 (0 : X)) :
    IsCompact (WeakDual.polar 𝕜 U) := by
  let ev : WeakDual 𝕜 X → X → 𝕜 := fun φ x ↦ φ x
  have hev : IsEmbedding ev := ⟨⟨rfl⟩, DFunLike.coe_injective⟩
  rw [hev.isCompact_iff]
  have himage : ev '' WeakDual.polar 𝕜 U =
      range (fun l : X →ₗ[𝕜] 𝕜 ↦ (l : X → 𝕜)) ∩ ⋂ x ∈ U, {f | ‖f x‖ ≤ 1} := by
    ext f
    constructor
    · rintro ⟨φ, hφ, rfl⟩
      exact ⟨⟨φ.toStrongDual.toLinearMap, rfl⟩, mem_iInter₂.mpr hφ⟩
    · rintro ⟨⟨l, rfl⟩, h⟩
      have hl : ∀ x ∈ U, ‖l x‖ ≤ 1 := fun x hx =>
        (mem_iInter₂.mp h x hx : (l : X → 𝕜) ∈ {f | ‖f x‖ ≤ 1})
      have hc : Continuous l := by
        apply continuous_of_continuousAt_zero l
        rw [ContinuousAt, map_zero, Metric.tendsto_nhds]
        intro ε hε
        obtain ⟨a, ha, haε⟩ := NormedField.exists_norm_lt 𝕜 hε
        have hnear : a • U ∈ 𝓝 (0 : X) := by
          simpa using smul_mem_nhds_smul₀ (norm_pos_iff.mp ha) hU
        filter_upwards [hnear] with x hx
        obtain ⟨y, hy, rfl⟩ := hx
        rw [dist_zero_right, map_smul, norm_smul]
        exact (mul_le_of_le_one_right ha.le (hl y hy)).trans_lt haε
      exact ⟨StrongDual.toWeakDual ⟨l, hc⟩, hl, rfl⟩
  have hclosed : IsClosed (ev '' WeakDual.polar 𝕜 U) := by
    rw [himage]
    exact (LinearMap.isClosed_range_coe X 𝕜 (RingHom.id 𝕜)).inter
      (isClosed_iInter fun x ↦ isClosed_iInter fun _ ↦
        isClosed_le (continuous_apply x).norm continuous_const)
  choose a ha using fun x : X ↦ (absorbent_nhds_zero (𝕜 := 𝕜) hU x).exists
  refine (isCompact_pi_infinite (fun x : X ↦ isCompact_closedBall (0 : 𝕜) ‖a x‖))
    |>.of_isClosed_subset hclosed ?_
  rintro _ ⟨φ, hφ, rfl⟩ x
  obtain ⟨y, hy, hxy⟩ := ha x (mem_singleton x)
  change φ x ∈ Metric.closedBall (0 : 𝕜) ‖a x‖
  rw [Metric.mem_closedBall, dist_zero_right,
    ← congrArg (fun z ↦ φ z) hxy, map_smul, norm_smul]
  exact mul_le_of_le_one_right (norm_nonneg _) (hφ y hy)

variable {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]

/-- Ordered Schauder expansion with its biorthogonal continuous coefficients. -/
def IsSchauderBasis (x : ℕ → E) (f : ℕ → StrongDual ℂ E) : Prop :=
  (∀ m n, f m (x n) = if m = n then 1 else 0) ∧
    ∀ u, HasSum (fun m ↦ f m u • x m) u (SummationFilter.conditional ℕ)

/-- Unconditional expansions converge over the net of finite partial sums. -/
def IsUnconditional (x : ℕ → E) (f : ℕ → StrongDual ℂ E) : Prop :=
  ∀ u, HasSum (fun m ↦ f m u • x m) u

/-- Absoluteness in the locally convex topology. -/
def IsAbsolute (x : ℕ → E) (f : ℕ → StrongDual ℂ E) : Prop :=
  ∀ q : Seminorm ℂ E, Continuous q → ∃ q' : Seminorm ℂ E, Continuous q' ∧
    ∀ u, Summable (fun m ↦ q (f m u • x m)) ∧
      (∑' m, q (f m u • x m)) ≤ q' u

/-- Ordered expansions converge whenever their partial sums are von Neumann bounded. -/
def IsBoundedlyComplete (x : ℕ → E) : Prop :=
  ∀ a : ℕ → ℂ, IsVonNBounded ℂ (range fun k : ℕ ↦ ∑ m ∈ Finset.Iic k, a m • x m) →
    Summable (fun m ↦ a m • x m) (SummationFilter.conditional ℕ)

/-- Canonical evaluation into the strong bidual. -/
def strongBidualEvaluation [ContinuousSMul ℂ E] : E →ₗ[ℂ] StrongDual ℂ (StrongDual ℂ E) where
  toFun x := ⟨⟨⟨fun ℓ => ℓ x, fun _ _ => rfl⟩, fun _ _ => rfl⟩, continuous_eval_const x⟩
  map_add' x y := ContinuousLinearMap.ext fun ℓ => ℓ.map_add x y
  map_smul' a x := ContinuousLinearMap.ext fun ℓ => ℓ.map_smul a x

@[simp] theorem strongBidualEvaluation_apply [ContinuousSMul ℂ E] (x : E) (g : StrongDual ℂ E) :
    strongBidualEvaluation x g = g x := rfl

/-- A basis is shrinking if its coefficient functionals form a Schauder basis
of the strong dual, with the canonical evaluation coordinates. -/
def IsShrinking [ContinuousSMul ℂ E] (x : ℕ → E) (f : ℕ → StrongDual ℂ E) : Prop :=
  IsSchauderBasis f (fun m ↦ strongBidualEvaluation (x m))

variable [IsTopologicalAddGroup E] [ContinuousSMul ℂ E]
variable [PolynormableSpace ℂ E] [T2Space E] [BarrelledSpace ℂ E]
variable {x : ℕ → E} {f : ℕ → StrongDual ℂ E}
variable (hReflexive : IsHomeomorph (strongBidualEvaluation (E := E)))
  (hb : IsSchauderBasis x f) (ha : IsAbsolute x f)

omit [IsTopologicalAddGroup E] [BarrelledSpace ℂ E] in
include hb ha hReflexive in
/-- Paper: Lemma 4.1.2.4, p. 159. The coefficient basis of the strong dual is
unconditional, with coefficients given by evaluation at the original basis vectors. -/
theorem strongDual_isUnconditional_of_isAbsolute :
    IsUnconditional f (fun m ↦ strongBidualEvaluation (x m)) := by
  intro g
  have horth (m n : ℕ) : f m (x n) = if m = n then 1 else 0 := hb.1 m n
  -- A continuous functional vanishing on the coefficient span is evaluation at zero.
  let S := Submodule.span ℂ (range f)
  have hdense : Dense (S : Set (StrongDual ℂ E)) := by
    intro g
    by_contra hg
    obtain ⟨φ, hφ, hvanish⟩ := exists_dual_eq_zero_on_submodule_of_notMem
      S.topologicalClosure S.isClosed_topologicalClosure hg
    obtain ⟨u, rfl⟩ := hReflexive.surjective φ
    have hzero (m : ℕ) : f m u = 0 :=
      hvanish (f m) (S.le_topologicalClosure (Submodule.subset_span (mem_range_self m)))
    have hsum : HasSum (fun _ : ℕ ↦ (0 : E)) u (SummationFilter.conditional ℕ) := by
      simpa only [ContinuousLinearMap.coe_coe, hzero, zero_smul] using hb.2 u
    have hu : u = 0 := hsum.unique (by simp)
    apply hφ
    change g u = 0
    rw [hu, map_zero]
  let P (s : Finset ℕ) (u : E) := ∑ m ∈ s, f m u • x m
  let Q (s : Finset ℕ) : StrongDual ℂ E := ∑ m ∈ s, g (x m) • f m
  have heval (s : Finset ℕ) (u : E) : (Q s - g) u = g (P s u - u) := by
    simp only [P, Q, sub_apply, sum_apply, smul_apply, map_sub, map_sum, map_smul, smul_eq_mul,
      mul_comm]
  have hvanish (ψ : StrongDual ℂ E) (hψ : ψ ∈ S) :
      ∀ᶠ s : Finset ℕ in atTop, ∀ u, ψ (P s u - u) = 0 := by
    induction hψ using Submodule.span_induction with
    | mem ψ hψ =>
      obtain ⟨m, rfl⟩ := hψ
      filter_upwards [eventually_ge_atTop ({m} : Finset ℕ)] with s hs u
      have hm := Finset.singleton_subset_iff.mp hs
      simp only [P, map_sub, map_sum, map_smul, horth, smul_eq_mul, mul_ite, mul_one,
        mul_zero, Finset.sum_ite_eq, hm, ite_true, sub_self]
    | zero => simp
    | add ψ χ _ _ hψ hχ =>
      filter_upwards [hψ, hχ] with s hs ht u
      simp [hs u, ht u]
    | smul c ψ _ hψ =>
      filter_upwards [hψ] with s hs u
      simp [hs u]
  change Tendsto Q atTop (𝓝 g)
  apply tendsto_sub_nhds_zero_iff.mp
  apply (ContinuousLinearMap.hasBasis_nhds_zero_of_basis Metric.nhds_basis_ball).tendsto_right_iff.mpr
  rintro ⟨B, ε⟩ ⟨hB, hε⟩
  -- Absoluteness bounds all truncation errors on a bounded set by continuous seminorms.
  let T := {v : E | ∃ (s : Finset ℕ) (u : E), u ∈ B ∧ P s u - u = v}
  have hT : IsVonNBounded ℂ T := by
    let hp := PolynormableSpace.withSeminorms ℂ E
    apply hp.isVonNBounded_iff_seminorm_bounded.mpr
    rintro ⟨q, hq⟩
    obtain ⟨q', hq', habs⟩ := ha q hq
    obtain ⟨C, hC, hqB⟩ := hp.isVonNBounded_iff_seminorm_bounded.mp hB ⟨q, hq⟩
    obtain ⟨C', hC', hq'B⟩ := hp.isVonNBounded_iff_seminorm_bounded.mp hB ⟨q', hq'⟩
    refine ⟨C' + C, add_pos hC' hC, ?_⟩
    rintro _ ⟨s, u, hu, rfl⟩
    have hP : q (P s u) ≤ q' u := calc
      q (P s u) ≤ ∑ m ∈ s, q (f m u • x m) :=
        Finset.le_sum_of_subadditive q (map_zero q).le (map_add_le_add q) _ _
      _ ≤ ∑' m, q (f m u • x m) :=
        (habs u).1.sum_le_tsum s (fun _ _ ↦ apply_nonneg _ _)
      _ ≤ q' u := (habs u).2
    exact (map_sub_le_add q _ _).trans_lt (add_lt_add (hP.trans_lt (hq'B u hu)) (hqB u hu))
  -- Approximate g on the entire error set by a finite linear combination of coefficients.
  have hnear : ∀ᶠ ψ : StrongDual ℂ E in 𝓝 g, MapsTo (ψ - g) T (Metric.ball 0 ε) := by
    have ht : Tendsto (fun ψ ↦ ψ - g) (𝓝 g) (𝓝 0) :=
      tendsto_sub_nhds_zero_iff.mpr tendsto_id
    exact ht.eventually (ContinuousLinearMap.eventually_nhds_zero_mapsTo hT
      (Metric.ball_mem_nhds _ hε))
  obtain ⟨ψ, hψ, hclose⟩ := ((mem_closure_iff_frequently.mp (hdense g)).and_eventually hnear).exists
  filter_upwards [hvanish ψ hψ] with s hs u hu
  have h := hclose (show P s u - u ∈ T from ⟨s, u, hu, rfl⟩)
  change (Q s - g) u ∈ Metric.ball 0 ε
  rw [heval]
  simpa only [Metric.mem_ball, dist_zero_right, sub_apply, hs u, zero_sub, norm_neg] using h

omit [IsTopologicalAddGroup E] [BarrelledSpace ℂ E] in
include hb ha hReflexive in
/-- Paper: Lemma 4.1.2.4, p. 159. An absolute Schauder basis of a complete
barrelled reflexive space is shrinking. -/
theorem isShrinking_of_isAbsolute : IsShrinking x f := by
  have horth (m n : ℕ) : f m (x n) = if m = n then 1 else 0 := hb.1 m n
  refine ⟨fun m n ↦ ?_, fun g ↦ ?_⟩
  · change f n (x m) = _
    by_cases h : m = n
    · simp [horth, h]
    · simp [horth, h, Ne.symm h]
  · exact Tendsto.mono_left (strongDual_isUnconditional_of_isAbsolute hReflexive hb ha g)
      (SummationFilter.conditional ℕ).le_atTop

-- Retain the section hypotheses in the theorem's signature.
omit [IsTopologicalAddGroup E] [PolynormableSpace ℂ E] [T2Space E] [BarrelledSpace ℂ E] in
include hb hReflexive in
/-- Paper: Lemma 4.1.2.4, p. 159. An absolute Schauder basis of a complete
barrelled reflexive space is boundedly complete. -/
theorem isBoundedlyComplete_of_isAbsolute : IsBoundedlyComplete x := by
  intro a haBounded
  let s (k : ℕ) : E := ∑ m ∈ Finset.Iic k, a m • x m
  let S : ℕ → WeakDual ℂ (StrongDual ℂ E) := fun k ↦
    StrongDual.toWeakDual (strongBidualEvaluation (s k))
  -- Boundedness puts the evaluated partial sums in a weak-star compact polar.
  let U : Set (StrongDual ℂ E) := {g | MapsTo g (range s) (Metric.ball 0 1)}
  have hU : U ∈ 𝓝 (0 : StrongDual ℂ E) :=
    ContinuousLinearMap.eventually_nhds_zero_mapsTo haBounded (Metric.ball_mem_nhds _ zero_lt_one)
  have hS (k : ℕ) : S k ∈ WeakDual.polar ℂ U := fun g hg ↦
    (mem_ball_zero_iff.mp (hg (mem_range_self k))).le
  have hfilter : Filter.map S atTop ≤ 𝓟 (WeakDual.polar ℂ U) := by
    rw [Filter.le_principal_iff, Filter.mem_map]
    exact Eventually.of_forall hS
  obtain ⟨φ, _, hφ⟩ := (isCompact_weakDual_polar hU).exists_mapClusterPt hfilter
  obtain ⟨u, hu⟩ := hReflexive.surjective φ.toStrongDual
  -- Each coordinate stabilizes, so the vector representing the cluster point has coefficients a.
  have hcoeff (m : ℕ) : f m u = a m := by
    have hcl := hφ.continuousAt_comp (WeakDual.eval_continuous (f m)).continuousAt
    have heq : ∀ᶠ k : ℕ in atTop, S k (f m) = a m := by
      filter_upwards [eventually_ge_atTop m] with k hk
      change f m (s k) = a m
      have horth (n : ℕ) : f m (x n) = if m = n then 1 else 0 := hb.1 m n
      simp [s, map_sum, map_smul, horth, smul_eq_mul, mul_ite, Finset.mem_Iic, hk]
    have hval : φ (f m) ∈ ({a m} : Set ℂ) :=
      isClosed_singleton.mem_of_mapClusterPt hcl heq
    exact (congrArg (fun g : StrongDual ℂ (StrongDual ℂ E) ↦ g (f m)) hu).trans hval
  exact ⟨u, by simpa only [ContinuousLinearMap.coe_coe, hcoeff] using hb.2 u⟩

include hb ha hReflexive in
/-- The strong-dual coefficient basis is boundedly complete. The barrelled
hypothesis turns pointwise bounds on partial sums into a common polar. -/
theorem strongDual_isBoundedlyComplete_of_isAbsolute : IsBoundedlyComplete f := by
  intro a haBounded
  let s (k : ℕ) : StrongDual ℂ E := ∑ m ∈ Finset.Iic k, a m • f m
  letI : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  letI : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  have hbdd (x : E) : IsVonNBounded ℂ (range fun k => s k x) := by
    refine (haBounded.image (strongBidualEvaluation x)).subset ?_
    rintro _ ⟨k, rfl⟩
    exact ⟨s k, mem_range_self k, rfl⟩
  have hequi := (PolynormableSpace.banach_steinhaus (𝓕 := s) hbdd).equicontinuous (0 : E)
  have hnear := (Metric.equicontinuousAt_iff_right.mp hequi) 1 zero_lt_one
  let U : Set E := {x | ∀ k, ‖s k x‖ ≤ 1}
  have hU : U ∈ 𝓝 (0 : E) := by
    filter_upwards [hnear] with x hx k
    have h := hx k
    change dist (s k 0) (s k x) < 1 at h
    simpa only [map_zero, dist_zero_left] using h.le
  let S (k : ℕ) : WeakDual ℂ E := StrongDual.toWeakDual (s k)
  have hp (k : ℕ) : S k ∈ WeakDual.polar ℂ U := fun x hx => hx k
  have hfilter : Filter.map S atTop ≤ 𝓟 (WeakDual.polar ℂ U) :=
    by
      rw [Filter.le_principal_iff, Filter.mem_map]
      exact Eventually.of_forall hp
  obtain ⟨φ, -, hφ⟩ := (isCompact_weakDual_polar hU).exists_mapClusterPt hfilter
  have hcoeff (m : ℕ) : φ (x m) = a m := by
    have hcl := hφ.continuousAt_comp (WeakDual.eval_continuous (x m)).continuousAt
    have heq : ∀ᶠ k : ℕ in atTop, S k (x m) = a m := by
      filter_upwards [eventually_ge_atTop m] with k hk
      change s k (x m) = a m
      simp [s, sum_apply, smul_apply, hb.1, Finset.sum_ite_eq', hk]
    exact isClosed_singleton.mem_of_mapClusterPt hcl heq
  refine ⟨φ.toStrongDual, ?_⟩
  have h : HasSum (fun m => φ (x m) • f m) φ.toStrongDual :=
    strongDual_isUnconditional_of_isAbsolute hReflexive hb ha φ.toStrongDual
  have hs : HasSum (fun m => φ (x m) • f m) φ.toStrongDual (SummationFilter.conditional ℕ) :=
    Tendsto.mono_left h (SummationFilter.conditional ℕ).le_atTop
  simpa only [hcoeff] using hs

omit [IsTopologicalAddGroup E] [PolynormableSpace ℂ E] [T2Space E] [BarrelledSpace ℂ E] in
include hb hReflexive in
/-- The original Schauder expansion transports to the strong bidual.
Reflexivity already gives this shrinking conclusion for the dual basis. -/
theorem strongDual_isShrinking_of_isAbsolute :
    IsShrinking f (fun m => strongBidualEvaluation (x m)) := by
  refine ⟨fun m n => hb.1 m n, fun φ => ?_⟩
  obtain ⟨x₀, rfl⟩ := hReflexive.surjective φ
  let e : E →L[ℂ] StrongDual ℂ (StrongDual ℂ E) :=
    ⟨strongBidualEvaluation, hReflexive.continuous⟩
  have h := (hb.2 x₀).map e.toAddMonoidHom e.continuous
  change HasSum (fun m => strongBidualEvaluation (f m x₀ • x m))
    (strongBidualEvaluation x₀) (SummationFilter.conditional ℕ) at h
  simpa only [map_smul, strongBidualEvaluation_apply] using h

include hb ha hReflexive in
/-- Lemma 4.1.2.4, with the final shrinking assertion for the dual basis
proved under the hypotheses of the first assertion. -/
theorem absoluteBasis_duality :
    IsShrinking x f ∧ IsBoundedlyComplete x ∧
      IsUnconditional f (fun m => strongBidualEvaluation (x m)) ∧
      IsBoundedlyComplete f ∧ IsShrinking f (fun m => strongBidualEvaluation (x m)) :=
  ⟨isShrinking_of_isAbsolute hReflexive hb ha,
    isBoundedlyComplete_of_isAbsolute hReflexive hb,
    strongDual_isUnconditional_of_isAbsolute hReflexive hb ha,
    strongDual_isBoundedlyComplete_of_isAbsolute hReflexive hb ha,
    strongDual_isShrinking_of_isAbsolute hReflexive hb⟩

end

end Masullo
