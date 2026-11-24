import Mathlib.Analysis.LocallyConvex.BalancedCoreHull
import Mathlib.Analysis.LocallyConvex.Polar
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.LocallyConvex.WeakDual
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Module.Convex

open Filter Set Topology
open scoped Pointwise

namespace Masullo

section ComplexDualPair

variable {E F : Type*} [AddCommGroup E] [Module ℂ E] [Module ℝ E] [IsScalarTower ℝ ℂ E]
  [AddCommGroup F] [Module ℂ F] (B : E →ₗ[ℂ] F →ₗ[ℂ] ℂ)

omit [Module ℝ E] [IsScalarTower ℝ ℂ E] in
private theorem absolutePolar_closed (S : Set F) : IsClosed (X := WeakBilin B) (B.flip.polar S) := by
  have heq : (B.flip.polar S : Set (WeakBilin B)) = ⋂ y ∈ S, {x | ‖B x y‖ ≤ 1} := by
    ext x
    simp [LinearMap.polar_mem_iff]
  rw [heq]
  exact isClosed_biInter fun y _ => isClosed_le (WeakBilin.eval B y).continuous.norm continuous_const

private theorem absolutePolar_convex (S : Set F) : Convex ℝ (B.flip.polar S) := by
  have heq : (B.flip.polar S : Set E) = ⋂ y ∈ S,
      ((B.flip y).restrictScalars ℝ) ⁻¹' Metric.closedBall (0 : ℂ) 1 := by
    ext x
    simp [LinearMap.polar_mem_iff, Metric.mem_closedBall, dist_zero_right]
  rw [heq]
  exact convex_iInter fun y => convex_iInter fun _ => (convex_closedBall (0 : ℂ) 1).linear_preimage _

omit [Module ℝ E] [IsScalarTower ℝ ℂ E] in
private theorem absolutePolar_balanced (S : Set F) : Balanced ℂ (B.flip.polar S) := by
  intro t ht x hx
  obtain ⟨z, hz, rfl⟩ := hx
  intro y hy
  simpa only [LinearMap.flip_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, norm_mul] using
    mul_le_one₀ ht (norm_nonneg _) (hz y hy)

private theorem balanced_real_convexHull {S : Set E} (hS : Balanced ℂ S) :
    Balanced ℂ (convexHull ℝ S) := by
  intro c hc
  let L : E →ₗ[ℝ] E := (LinearMap.lsmul ℂ E c).restrictScalars ℝ
  change L '' convexHull ℝ S ⊆ convexHull ℝ S
  rw [L.image_convexHull]
  exact convexHull_mono (hS c hc)

private theorem norm_lt_of_re_lt_on_balanced {X : Type*} [AddCommGroup X] [Module ℂ X]
    [TopologicalSpace X] {S : Set X} (hS : Balanced ℂ S) (f : StrongDual ℂ X) {u : ℝ} (hu : 0 < u)
    (h : ∀ z ∈ S, (f z).re < u) {z : X} (hz : z ∈ S) : ‖f z‖ < u := by
  by_cases hf : f z = 0
  · simpa [hf] using hu
  let c : ℂ := (‖f z‖ : ℂ) / f z
  have hc : ‖c‖ ≤ 1 := by
    simp [c, Complex.norm_real, norm_ne_zero_iff.mpr hf]
  have hz' : c • z ∈ S := hS c hc (smul_mem_smul_set hz)
  have he : f (c • z) = (‖f z‖ : ℂ) := by
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hf]
  simpa [he] using h (c • z) hz'

/-- The absolute bipolar theorem C.2.2.1, in the weak topology of a
complex bilinear pairing. The real convex hull of the balanced hull is
the convex circled hull. -/
theorem complex_bipolar_eq_weak_closure (A : Set E) :
    (B.flip.polar (B.polar A) : Set (WeakBilin B)) =
      @closure (WeakBilin B) _ (convexHull ℝ (balancedHull ℂ (insert 0 A))) := by
  letI : ContinuousSMul ℝ (WeakBilin B) := IsScalarTower.continuousSMul (M := ℝ) (α := WeakBilin B) ℂ
  let A' : Set (WeakBilin B) := A
  let K : Set (WeakBilin B) := convexHull ℝ (balancedHull ℂ (insert 0 A'))
  let S : Set (WeakBilin B) := closure K
  let D : Set (WeakBilin B) := B.flip.polar (B.polar A)
  have hA : A' ⊆ K := by
    intro x hx
    exact subset_convexHull ℝ _ (subset_balancedHull ℂ (mem_insert_of_mem 0 hx))
  have h0 : (0 : WeakBilin B) ∈ S := subset_closure
    (subset_convexHull ℝ _ (subset_balancedHull ℂ (mem_insert 0 A')))
  have hconv : Convex ℝ S := (convex_convexHull ℝ _).closure
  have hbal : Balanced ℂ S := (balanced_real_convexHull (E := WeakBilin B) (balancedHull.balanced _)).closure
  change D = S
  apply Subset.antisymm _ (closure_minimal ?_ (absolutePolar_closed B (B.polar A)))
  · intro x hx
    by_contra hxs
    obtain ⟨f, u, hfu, hux⟩ := RCLike.geometric_hahn_banach_closed_point (𝕜 := ℂ) hconv isClosed_closure hxs
    have hu : 0 < u := by simpa using hfu 0 h0
    obtain ⟨y, hy⟩ := B.dualEmbedding_surjective f
    have hyx (z : WeakBilin B) : B z y = f z := DFunLike.congr_fun hy z
    let y' : F := ((u : ℂ)⁻¹) • y
    have hnorm (z : WeakBilin B) : ‖B z y'‖ = u⁻¹ * ‖f z‖ := by
      simp only [y', map_smul, smul_eq_mul, norm_mul, norm_inv, Complex.norm_real,
        Real.norm_of_nonneg hu.le, hyx]
    have hy' : y' ∈ B.polar A := by
      intro z hz
      rw [hnorm z, inv_mul_le_iff₀ hu, mul_one]
      exact (norm_lt_of_re_lt_on_balanced hbal f hu hfu (subset_closure (hA hz))).le
    have hbound : ‖B x y'‖ ≤ 1 := hx y' hy'
    rw [hnorm, inv_mul_le_iff₀ hu, mul_one] at hbound
    exact (hux.trans_le ((Complex.re_le_norm _).trans hbound)).false
  · have hDv : Convex ℝ D := absolutePolar_convex B (B.polar A)
    have hDb : Balanced ℂ D := absolutePolar_balanced B (B.polar A)
    apply convexHull_min _ hDv
    apply hDb.balancedHull_subset_of_subset
    exact insert_subset_iff.mpr ⟨B.flip.zero_mem_polar _, B.subset_bipolar A⟩

end ComplexDualPair

section PolarNeighborhoods

variable {X : Type*} [AddCommGroup X] [Module ℂ X] [Module ℝ X] [IsScalarTower ℝ ℂ X]
  [TopologicalSpace X]

/-- Evaluation pairs the continuous dual with the original vector space. -/
noncomputable def continuousDualPair : StrongDual ℂ X →ₗ[ℂ] X →ₗ[ℂ] ℂ := ContinuousLinearMap.coeLM ℂ

private theorem closed_convex_balanced_eq_dual_bipolar [IsTopologicalAddGroup X]
    [ContinuousSMul ℂ X] [LocallyConvexSpace ℝ X] {V : Set X}
    (hV0 : 0 ∈ V) (hVc : IsClosed V) (hVv : Convex ℝ V) (hVb : Balanced ℂ V) :
    (continuousDualPair (X := X)).polar ((continuousDualPair (X := X)).flip.polar V) = V := by
  let ev := continuousDualPair (X := X)
  refine Subset.antisymm (fun x hx => ?_) (ev.flip.subset_bipolar V)
  by_contra hnot
  obtain ⟨f, r, hf, hx'⟩ := RCLike.geometric_hahn_banach_closed_point (𝕜 := ℂ) hVv hVc hnot
  have hr : 0 < r := by simpa using hf 0 hV0
  let f' : StrongDual ℂ X := ((r : ℂ)⁻¹) • f
  have hnorm (y : X) : ‖f' y‖ = r⁻¹ * ‖f y‖ := by
    simp only [f', smul_apply, norm_smul, norm_inv, Complex.norm_real,
      Real.norm_of_nonneg hr.le]
  have hf' : f' ∈ ev.flip.polar V := by
    intro y hy
    change ‖f' y‖ ≤ 1
    rw [hnorm, inv_mul_le_iff₀ hr, mul_one]
    exact (norm_lt_of_re_lt_on_balanced hVb f hr hf hy).le
  have hle : ‖f' x‖ ≤ 1 := hx f' hf'
  rw [hnorm, inv_mul_le_iff₀ hr, mul_one] at hle
  exact (hx'.trans_le ((Complex.re_le_norm _).trans hle)).false

/-- Lemma C.2.2.2. The polars of weakly closed, convex, balanced and
equicontinuous subsets of the continuous dual are a zero-neighborhood basis. -/
theorem polar_neighborhood_basis [PolynormableSpace ℂ X] :
    (𝓝 (0 : X)).HasBasis
      (fun S : Set (StrongDual ℂ X) =>
        EquicontinuousAt (fun f : S => (f.val : X → ℂ)) 0 ∧
          Convex ℝ S ∧ Balanced ℂ S ∧ IsClosed (X := WeakBilin (continuousDualPair (X := X))) S)
      (continuousDualPair (X := X)).polar := by
  let ev := continuousDualPair (X := X)
  let hp := PolynormableSpace.withSeminorms ℂ X
  letI : IsTopologicalAddGroup X := hp.topologicalAddGroup
  letI : ContinuousSMul ℂ X := hp.continuousSMul
  letI : LocallyConvexSpace ℝ X := hp.toLocallyConvexSpace
  refine ⟨fun U => ⟨fun hU => ?_, ?_⟩⟩
  · obtain ⟨⟨I, r⟩, hr, hsub⟩ := hp.hasBasis_zero_ball.mem_iff.mp hU
    let p := I.sup (fun p : {p : Seminorm ℂ X // Continuous p} => p.val)
    have hpc : Continuous p := Seminorm.continuous_finsetSup fun i _ => i.property
    let V := p.closedBall 0 (r / 2)
    have hV0 : 0 ∈ V := p.mem_closedBall_zero.mpr (by simpa using (half_pos hr).le)
    have hVc : IsClosed V := by
      rw [show V = {x | p x ≤ r / 2} from Set.ext fun _ => p.mem_closedBall_zero]
      exact isClosed_le hpc continuous_const
    have hVsub : V ⊆ U := fun x hx => hsub
      (p.mem_ball_zero.mpr ((p.mem_closedBall_zero.mp hx).trans_lt (half_lt_self hr)))
    let S := ev.flip.polar V
    have hSe : EquicontinuousAt (fun f : S => (f.val : X → ℂ)) 0 := by
      apply Metric.equicontinuousAt_iff_right.mpr
      intro ε hε
      let c : ℝ := ε / 2
      have hc : 0 < c := half_pos hε
      filter_upwards [p.ball_mem_nhds hpc (mul_pos hc (half_pos hr))] with x hx f
      let y : X := ((c : ℂ)⁻¹) • x
      have hy : y ∈ V := by
        apply p.mem_closedBall_zero.mpr
        have hpx : p x < c * (r / 2) := p.mem_ball_zero.mp hx
        simpa only [y, map_smul_eq_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hc.le,
          inv_mul_le_iff₀ hc] using hpx.le
      have hfy : ‖f.val y‖ ≤ 1 := f.property y hy
      have he : x = (c : ℂ) • y := by
        change x = (c : ℂ) • ((c : ℂ)⁻¹ • x)
        rw [smul_smul, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hc.ne'), one_smul]
      have hfx : ‖f.val x‖ ≤ c := by
        conv_lhs => rw [he]
        rw [map_smul, norm_smul, Complex.norm_real, Real.norm_of_nonneg hc.le]
        exact mul_le_of_le_one_right hc.le hfy
      rw [map_zero, dist_zero_left]
      exact hfx.trans_lt (half_lt_self hε)
    refine ⟨S, ⟨hSe, absolutePolar_convex ev V, absolutePolar_balanced ev V,
      absolutePolar_closed ev V⟩, ?_⟩
    have hdouble := closed_convex_balanced_eq_dual_bipolar hV0 hVc (p.convex_closedBall _ _)
      (p.balanced_closedBall_zero _)
    exact hdouble.symm ▸ hVsub
  · rintro ⟨S, ⟨hSe, _, _, _⟩, hSU⟩
    apply mem_of_superset _ hSU
    filter_upwards [Metric.equicontinuousAt_iff_right.mp hSe 1 zero_lt_one] with x hx f hf
    have hh := hx ⟨f, hf⟩
    rw [map_zero, dist_zero_left] at hh
    exact hh.le

end PolarNeighborhoods

end Masullo
