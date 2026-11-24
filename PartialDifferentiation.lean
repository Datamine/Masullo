import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Normed.Lp.PiLp

open Filter Function Set Topology Asymptotics
open scoped BigOperators Convex

namespace Masullo

section CoordinateMap

variable {𝕜 F : Type*} [CommSemiring 𝕜] [TopologicalSpace 𝕜]
  [AddCommMonoid F] [Module 𝕜 F] [TopologicalSpace F] [ContinuousAdd F]
  [ContinuousSMul 𝕜 F] {n : ℕ}

/-- A continuous linear map specified by its values on the coordinate basis. -/
noncomputable def coordinateDifferential (d : Fin n → F) : (Fin n → 𝕜) →L[𝕜] F :=
  ∑ i, (ContinuousLinearMap.proj i).smulRight (d i)

theorem coordinateDifferential_apply (d : Fin n → F) (y : Fin n → 𝕜) :
    coordinateDifferential d y = ∑ i, y i • d i := by
  simp [coordinateDifferential]

end CoordinateMap

section CoordinateDerivative

variable {𝕜 F : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {n : ℕ}

private def replacePrefix (x y : Fin n → 𝕜) (j : ℕ) (i : Fin n) : 𝕜 :=
  if i.1 < j then y i else x i

omit [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜] in
private theorem replacePrefix_zero (x y : Fin n → 𝕜) : replacePrefix x y 0 = x := by
  ext i
  simp [replacePrefix]

omit [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜] in
private theorem replacePrefix_full (x y : Fin n → 𝕜) : replacePrefix x y n = y := by
  ext i
  simp [replacePrefix, i.isLt]

omit [IsRCLikeNormedField 𝕜] in
private theorem replacePrefix_succ (x y : Fin n → 𝕜) (i : Fin n) :
    replacePrefix x y (i.1+1) = replacePrefix x y i.1 + (y i - x i) • Pi.single i 1 := by
  ext j
  by_cases hj : j = i
  · subst j
    simp [replacePrefix]
  · have hv : ¬ j.1 = i.1 := fun h => hj (Fin.ext h)
    have hb : j.1 < i.1 + 1 ↔ j.1 < i.1 := by omega
    simp [replacePrefix, hb, Pi.single_eq_of_ne hj]

omit [IsRCLikeNormedField 𝕜] in
private theorem continuous_replacePrefix (x : Fin n → 𝕜) (j : ℕ) :
    Continuous (fun y => replacePrefix x y j) := by
  apply continuous_pi_iff.mpr
  intro i
  by_cases hi : i.1 < j
  · simpa [replacePrefix, hi] using (continuous_apply i : Continuous fun y : Fin n → 𝕜 => y i)
  · simpa [replacePrefix, hi] using (continuous_const : Continuous fun _ : Fin n → 𝕜 => x i)

omit [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜] in
private theorem replacePrefix_self (x : Fin n → 𝕜) (j : ℕ) : replacePrefix x x j = x := by
  ext i
  simp [replacePrefix]

omit [IsRCLikeNormedField 𝕜] [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 F] in
private theorem sum_replacePrefix_sub (f : (Fin n → 𝕜) → F) (x y : Fin n → 𝕜) :
    (∑ i : Fin n, (f (replacePrefix x y (i.1 + 1)) - f (replacePrefix x y i.1))) = f y - f x := by
  let batch (i : ℕ) := f (replacePrefix x y (i + 1)) - f (replacePrefix x y i)
  change (∑ i : Fin n, batch (i : ℕ)) = _
  rw [Fin.sum_univ_eq_sum_range (f := batch)]
  have hh (k : ℕ) :
      (∑ i ∈ Finset.range k, (f (replacePrefix x y (i + 1)) - f (replacePrefix x y i))) =
        f (replacePrefix x y k) - f x := by
    induction k with
    | zero => simp [replacePrefix_zero]
    | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      abel
  change (∑ i ∈ Finset.range n, (f (replacePrefix x y (i + 1)) - f (replacePrefix x y i))) = _
  rw [hh, replacePrefix_full]

omit [IsRCLikeNormedField 𝕜] in
private theorem hasDerivAt_along_shifted_coordinate (f : (Fin n → 𝕜) → F)
    (z : Fin n → 𝕜) (t : 𝕜) (i : Fin n) (d : F)
    (h : HasDerivAt (fun w : 𝕜 => f ((z + t • Pi.single i 1) + w • Pi.single i 1)) d 0) :
    HasDerivAt (fun w : 𝕜 => f (z + w • Pi.single i 1)) d t := by
  have ht : -t + t = (0 : 𝕜) := neg_add_cancel _
  have hs := HasDerivAt.comp_const_add (-t) t (ht.symm ▸ h)
  convert hs using 1
  ext w
  congr 1
  rw [add_assoc, ← add_smul, ← add_assoc, add_neg_cancel, zero_add]

private theorem parameter_remainder_small {X : Type*} {l : Filter X} {u : 𝕜}
    {r : X → 𝕜} {f : X → 𝕜 → F} {d : X → 𝕜 → 𝕜 →L[𝕜] F}
    (hr : Tendsto r l (𝓝 u))
    (hd : ∀ᶠ p in l ×ˢ 𝓝 u, HasFDerivAt (f p.1) (d p.1 p.2) p.2)
    {D : 𝕜 →L[𝕜] F} (hc : Tendsto (fun p : X × 𝕜 => d p.1 p.2) (l ×ˢ 𝓝 u) (𝓝 D)) :
    (fun y => f y (r y) - f y u - D (r y - u)) =o[l] (fun y => r y - u) := by
  letI : RCLike 𝕜 := IsRCLikeNormedField.rclike 𝕜
  rw [isLittleO_iff]
  intro ε hε
  let bound (a : X) (b : 𝕜) : Prop := ‖d a b - D‖ < ε
  have hC : ∀ᶠ p in l ×ˢ 𝓝 u, bound p.1 p.2 := by
    have h := (Metric.tendsto_nhds.mp hc) ε hε
    simpa [dist_eq_norm, bound] using h
  have hu : Tendsto (fun _ : X => u) l (𝓝 u) := tendsto_const_nhds
  let deriv (a : X) (b : 𝕜) : Prop := HasFDerivAt (f a) (d a b) b
  have hD : ∀ᶠ p in l ×ˢ 𝓝 u, deriv p.1 p.2 := hd
  filter_upwards [Eventually.segment_of_prod_nhds (r := deriv) hu hr hD,
    Eventually.segment_of_prod_nhds (r := bound) hu hr hC] with y hy hεy
  exact Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le'
    (fun z hz => (show HasFDerivAt (f y) (d y z) z from hy z hz).hasFDerivWithinAt) (fun z hz => (show ‖d y z - D‖ < ε from hεy z hz).le)
    (convex_segment ..) (left_mem_segment ..) (right_mem_segment ..)

private theorem coordinate_remainder_small {U : Set (Fin n → 𝕜)} (hU : IsOpen U)
    (f : (Fin n → 𝕜) → F) (D : Fin n → (Fin n → 𝕜) → F)
    (hD : ∀ i z, z ∈ U → HasDerivAt (fun t : 𝕜 => f (z + t • Pi.single i 1)) (D i z) 0)
    (hc : ∀ i, ContinuousOn (D i) U) {x : Fin n → 𝕜} (hx : x ∈ U) (i : Fin n) :
    (fun y => f (replacePrefix x y (i.1 + 1)) - f (replacePrefix x y i.1) - (y i - x i) • D i x)
      =o[𝓝 x] (fun y => y - x) := by
  letI : RCLike 𝕜 := IsRCLikeNormedField.rclike 𝕜
  let z (y : Fin n → 𝕜) (t : 𝕜) := replacePrefix x y i.1 + t • Pi.single i 1
  have hz : ContinuousAt (fun p : (Fin n → 𝕜) × 𝕜 => z p.1 p.2) (x, 0) := by
    let g : (Fin n → 𝕜) × 𝕜 → Fin n → 𝕜 := fun p => replacePrefix x p.1 i.1
    let h : (Fin n → 𝕜) × 𝕜 → Fin n → 𝕜 := fun p => p.2 • Pi.single i 1
    have hg : Continuous g := (continuous_replacePrefix x i.1).comp continuous_fst
    have hh : Continuous h := continuous_snd.smul continuous_const
    change ContinuousAt (fun p => g p + h p) (x, 0)
    exact (hg.add hh).continuousAt
  have he : z x 0 = x := by simp [z, replacePrefix_self]
  have hzu : ∀ᶠ p in 𝓝 x ×ˢ 𝓝 (0 : 𝕜), z p.1 p.2 ∈ U := by
    rw [← nhds_prod_eq]
    have hm : U ∈ 𝓝 (z x 0) := by rw [he]; exact hU.mem_nhds hx
    exact hz.tendsto.eventually_mem hm
  let d (y : Fin n → 𝕜) (t : 𝕜) :=
    (ContinuousLinearMap.id 𝕜 𝕜).smulRight (D i (z y t))
  have hd : Tendsto (fun p : (Fin n → 𝕜) × 𝕜 => d p.1 p.2) (𝓝 x ×ˢ 𝓝 0)
      (𝓝 ((ContinuousLinearMap.id 𝕜 𝕜).smulRight (D i x))) := by
    rw [← nhds_prod_eq]
    have hc' : ContinuousAt (fun p : (Fin n → 𝕜) × 𝕜 => D i (z p.1 p.2)) (x, 0) :=
      ((hc i).continuousAt (hU.mem_nhds hx)).comp_of_eq hz he
    have hcd : Tendsto (fun p : (Fin n → 𝕜) × 𝕜 => D i (z p.1 p.2)) (𝓝 (x, 0)) (𝓝 (D i x)) := by
      simpa only [he] using hc'.tendsto
    exact (ContinuousLinearMap.smulRightL 𝕜 𝕜 F (ContinuousLinearMap.id 𝕜 𝕜)).continuous.continuousAt.tendsto.comp hcd
  have hp : Tendsto (fun y : Fin n → 𝕜 => y i - x i) (𝓝 x) (𝓝 (0 : 𝕜)) := by
    have hh : ContinuousAt (fun y : Fin n → 𝕜 => y i - x i) x :=
      (continuous_apply i).continuousAt.sub continuousAt_const
    simpa only [sub_self] using hh.tendsto
  have hder : ∀ᶠ p in 𝓝 x ×ˢ 𝓝 (0 : 𝕜),
      HasFDerivAt (fun t => f (z p.1 t)) (d p.1 p.2) p.2 := by
    filter_upwards [hzu] with p hp
    exact (hasDerivAt_along_shifted_coordinate f (replacePrefix x p.1 i.1) p.2 i _
      (hD i _ hp)).hasFDerivAt
  have h := parameter_remainder_small (f := fun y t => f (z y t)) (d := d) hp hder hd
  have hsmall :
      (fun y => f (replacePrefix x y (i.1 + 1)) - f (replacePrefix x y i.1) - (y i - x i) • D i x)
        =o[𝓝 x] (fun y => y i - x i) := by
    simpa [z, ← replacePrefix_succ, Function.comp_def] using h
  apply hsmall.trans_isBigO
  exact isBigO_of_le _ fun y => norm_le_pi_norm (y - x) i

/-- Continuous coordinate derivatives give the Fréchet derivative on a
finite-dimensional coordinate space, for real or complex scalars. -/
theorem hasFDerivAt_of_continuous_coordinate_derivatives
    {U : Set (Fin n → 𝕜)} (hU : IsOpen U) (f : (Fin n → 𝕜) → F)
    (D : Fin n → (Fin n → 𝕜) → F)
    (hD : ∀ i z, z ∈ U → HasDerivAt (fun t : 𝕜 => f (z + t • Pi.single i 1)) (D i z) 0)
    (hc : ∀ i, ContinuousOn (D i) U) {x : Fin n → 𝕜} (hx : x ∈ U) :
    HasFDerivAt f (coordinateDifferential fun i => D i x) x := by
  apply HasFDerivAt.of_isLittleO
  have hsmall := IsLittleO.sum (s := Finset.univ) fun i _ =>
    coordinate_remainder_small hU f D hD hc hx i
  refine hsmall.congr_left fun y => ?_
  rw [coordinateDifferential_apply, Finset.sum_sub_distrib, sum_replacePrefix_sub]
  rfl

end CoordinateDerivative

end Masullo
