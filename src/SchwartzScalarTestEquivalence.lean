import SchwartzScalarTests
import WeakBoundedness

open Bornology Filter Function Set Topology
open scoped SchwartzMap ContDiff ENat

namespace Masullo

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

private theorem contDiffOn_of_localVectorContDiff_normed {d : ℕ} {U : Set (Fin d → ℝ)}
    (hU : IsOpen U) (m : ℕ) (f : (Fin d → ℝ) → V)
    (h : LocalVectorContDiff m f U) : ContDiffOn ℝ m f U := by
  induction m generalizing f with
  | zero => exact contDiffOn_zero.mpr h.1
  | succ m ih =>
    obtain ⟨g, hg, hweak⟩ := h
    have hgc (i : Fin d) := ih (g i) (hg i)
    let A (x : Fin d → ℝ) : (Fin d → ℝ) →L[ℝ] V := coordinateDifferential (fun i => g i x)
    have hAc : ContinuousOn (fun p : (Fin d → ℝ) × (Fin d → ℝ) => A p.1 p.2) (U ×ˢ univ) := by
      simp only [A, coordinateDifferential_apply]
      apply continuousOn_finsetSum
      intro i _
      exact ((continuous_apply i).comp continuous_snd).continuousOn.smul
        ((hgc i).continuousOn.comp continuous_fst.continuousOn (fun _ hx => hx.1))
    have hD (l : StrongDual ℂ V) (x : Fin d → ℝ) (hx : x ∈ U) :
        HasFDerivAt (fun y => l (f y)) ((l.restrictScalars ℝ).comp (A x)) x := by
      have hd := hasFDerivAt_of_continuous_coordinate_derivatives hU (fun y => l (f y))
        (fun i y => l (g i y)) (fun i y hy => hweak i y hy l)
        (fun i => l.continuous.comp_continuousOn (hgc i).continuousOn) hx
      have he : (l.restrictScalars ℝ).comp (A x) =
          coordinateDifferential (fun i => l (g i x)) := by
        apply ContinuousLinearMap.ext
        intro v
        change l (A x v) = _
        simp [A, coordinateDifferential_apply]
      rw [he]
      exact hd
    have hstrong (i : Fin d) (x : Fin d → ℝ) (hx : x ∈ U) :
        HasDerivAt (fun t : ℝ => f (x + t • Pi.single i 1)) (g i x) 0 := by
      have ht := strong_directional_of_continuous_weakDifferential hU f A hAc hD hx (Pi.single i 1)
      apply hasDerivAt_iff_tendsto_slope_zero.mpr
      simpa [A, coordinateDifferential_apply, slope_def_field, Pi.single_apply] using ht
    have hF (x : Fin d → ℝ) (hx : x ∈ U) : HasFDerivAt f (A x) x :=
      hasFDerivAt_of_continuous_coordinate_derivatives hU f g hstrong
        (fun i => (hgc i).continuousOn) hx
    rw [Nat.cast_succ, contDiffOn_succ_iff_fderiv_apply hU.uniqueDiffOn]
    refine ⟨fun x hx => (hF x hx).differentiableAt.differentiableWithinAt, by simp, fun v => ?_⟩
    have hsum : ContDiffOn ℝ (m : ℕ∞ω) (fun x => ∑ i, v i • g i x) U :=
      ContDiffOn.sum (fun i _ => contDiffOn_const.smul (hgc i))
    apply hsum.congr
    intro x hx
    rw [(hF x hx).hasFDerivWithinAt.fderivWithin (hU.uniqueDiffOn x hx)]
    exact coordinateDifferential_apply _ _

/-- Weak scalar smoothness on a finite-dimensional Euclidean space gives ordinary
Fréchet smoothness for a Banach target. -/
theorem contDiff_euclidean_of_scalar [CompleteSpace V] {d : ℕ}
    (f : EuclideanSpace ℝ (Fin d) → V)
    (hf : ∀ l : StrongDual ℂ V, ContDiff ℝ ∞ (fun x => l (f x))) :
    ContDiff ℝ ∞ f := by
  let e := EuclideanSpace.equiv (Fin d) ℝ
  let g := f ∘ e.symm
  have hs : ∀ l : StrongDual ℂ V, ContDiffOn ℝ ∞ (fun x => l (g x)) univ :=
    fun l => ((hf l).comp e.symm.contDiff).contDiffOn
  have hg : ContDiff ℝ ∞ g := by
    rw [← contDiffOn_univ, contDiffOn_infty]
    intro m
    exact contDiffOn_of_localVectorContDiff_normed isOpen_univ m g
      ((localVectorSmooth_iff_weak (𝕜 := ℝ) isOpen_univ g).mpr hs m)
  simpa [g, Function.comp_def] using hg.comp e.contDiff

/-- Scalar Schwartz bounds on a smooth map imply vector-valued Schwartz bounds. -/
theorem exists_schwartz_of_scalar_tests
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (f : X → V) (hs : ContDiff ℝ ∞ f)
    (h : ∀ l : StrongDual ℂ V, ∃ g : 𝓢(X, ℂ), ∀ x, g x = l (f x)) :
    ∃ g : 𝓢(X, V), ∀ x, g x = f x := by
  refine ⟨⟨f, hs, fun k n => ?_⟩, fun _ => rfl⟩
  let D (x : X) := ‖x‖ ^ k • iteratedFDeriv ℝ n f x
  let a (x : X) (v : Fin n → X) : V := (∏ i, ‖v i‖)⁻¹ • D x v
  let B : Set V := {y | ∃ x v, y = a x v}
  have hb : IsVonNBounded ℂ B := by
    apply (isVonNBounded_iff_dual_images B).mpr
    intro l
    obtain ⟨g, hg⟩ := h l
    have he : (g : X → ℂ) = (l.restrictScalars ℝ) ∘ f := funext hg
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨SchwartzMap.seminorm ℂ k n g, ?_⟩
    rintro _ ⟨_, ⟨x, v, rfl⟩, rfl⟩
    have hD := (l.restrictScalars ℝ).iteratedFDeriv_comp_left (x := x)
      hs.contDiffAt (i := n) (WithTop.coe_le_coe.mpr le_top)
    have hDj : iteratedFDeriv ℝ n g x v = l (iteratedFDeriv ℝ n f x v) := by
      rw [he, hD]
      rfl
    calc
      ‖l (a x v)‖ = ‖x‖ ^ k * (‖iteratedFDeriv ℝ n g x v‖ / ∏ i, ‖v i‖) := by
        change ‖(l.restrictScalars ℝ) ((∏ i, ‖v i‖)⁻¹ • (‖x‖ ^ k • iteratedFDeriv ℝ n f x) v)‖ = _
        simp only [smul_apply, map_smul, norm_smul]
        change ‖(∏ i, ‖v i‖)⁻¹‖ * (‖‖x‖ ^ k‖ * ‖l (iteratedFDeriv ℝ n f x v)‖) = _
        rw [← hDj]
        rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity), div_eq_mul_inv]
        ring
      _ ≤ ‖x‖ ^ k * ‖iteratedFDeriv ℝ n g x‖ :=
        mul_le_mul_of_nonneg_left ((iteratedFDeriv ℝ n g x).ratio_le_opNorm v) (by positivity)
      _ ≤ _ := SchwartzMap.le_seminorm ℂ k n g x
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp ((NormedSpace.isVonNBounded_iff ℂ).mp hb)
  refine ⟨max C 0, fun x => ?_⟩
  have hnorm : ‖D x‖ ≤ max C 0 := by
    apply ContinuousMultilinearMap.opNorm_le_bound (le_max_right _ _)
    intro v
    by_cases hv : ∏ i, ‖v i‖ = 0
    · obtain ⟨i, -, hi⟩ := Finset.prod_eq_zero_iff.mp hv
      rw [(D x).map_coord_zero i (norm_eq_zero.mp hi), norm_zero, hv, mul_zero]
    · have hpos : 0 < ∏ i, ‖v i‖ :=
        lt_of_le_of_ne (by positivity) (Ne.symm hv)
      have hm : ‖a x v‖ ≤ max C 0 := (hC (a x v) ⟨x, v, rfl⟩).trans (le_max_left _ _)
      rw [show ‖a x v‖ = ‖D x v‖ / ∏ i, ‖v i‖ by
        change ‖(∏ i, ‖v i‖)⁻¹ • D x v‖ = _
        rw [norm_smul, Real.norm_of_nonneg (by positivity), div_eq_inv_mul]] at hm
      exact (div_le_iff₀ hpos).mp hm
  simpa only [D, norm_smul, Real.norm_of_nonneg (pow_nonneg (norm_nonneg x) k)] using hnorm

section Coordinates

variable {I Y : Type*} [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]
  {p : SeminormFamily ℂ Y I} {d : ℕ}

/-- On finite-dimensional Euclidean domains, the scalar tests characterize
smoothness in every local Banach coordinate. -/
theorem localBanach_contDiff_iff_scalar (hp : WithSeminorms p)
    (f : EuclideanSpace ℝ (Fin d) → Y) :
    (∀ i, ContDiff ℝ ∞ (fun x => localBanachDenseMap (p i) (f x))) ↔
      ∀ l : StrongDual ℂ Y, ContDiff ℝ ∞ (fun x => l (f x)) := by
  refine ⟨fun h => localBanach_contDiff_scalar hp f h, fun h i => ?_⟩
  letI : IsTopologicalAddGroup Y := hp.topologicalAddGroup
  apply contDiff_euclidean_of_scalar
  intro l
  exact h (l.comp (localBanachMap (p i) (hp.continuous_seminorm i)))

/-- On finite-dimensional Euclidean domains, the scalar Schwartz tests
characterize membership in every local Banach Schwartz coordinate. -/
theorem localBanach_schwartz_iff_scalar (hp : WithSeminorms p)
    (f : EuclideanSpace ℝ (Fin d) → Y) :
    (∀ i, ∃ F : 𝓢(EuclideanSpace ℝ (Fin d), LocalBanach (p i)),
      ∀ x, F x = localBanachDenseMap (p i) (f x)) ↔
    ∀ l : StrongDual ℂ Y, ∃ F : 𝓢(EuclideanSpace ℝ (Fin d), ℂ), ∀ x, F x = l (f x) := by
  refine ⟨fun h => localBanach_schwartz_scalar hp f h, fun h i => ?_⟩
  letI : IsTopologicalAddGroup Y := hp.topologicalAddGroup
  have hSmooth := (localBanach_contDiff_iff_scalar hp f).mpr (fun l => by
    obtain ⟨F, hF⟩ := h l
    exact (funext hF) ▸ F.smooth')
  exact exists_schwartz_of_scalar_tests _ (hSmooth i)
    (fun l => h (l.comp (localBanachMap (p i) (hp.continuous_seminorm i))))

end Coordinates


end
end Masullo
