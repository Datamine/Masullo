import IteratedDirectionalDerivatives
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

open Filter Function MeasureTheory Set
open scoped ContDiff SchwartzMap Topology

namespace Masullo

noncomputable section

variable {X Y T : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [MeasurableSpace T]

private abbrev Jet (Y : Type*) [NormedAddCommGroup Y] [NormedSpace ℝ Y] (n : ℕ) :=
  ContinuousMultilinearMap ℝ (fun _ : Fin n => Y) ℂ

/-- Differentiate in the retained variable only. -/
private def partialJet (f : 𝓢(X × Y, ℂ)) (n : ℕ) (p : X × Y) : Jet Y n :=
  (iteratedFDeriv ℝ n f p).compContinuousLinearMap (fun _ => ContinuousLinearMap.inr ℝ X Y)

private theorem partialJet_eq (f : 𝓢(X × Y, ℂ)) (n : ℕ) (x : X) (y : Y) :
    partialJet f n (x, y) = iteratedFDeriv ℝ n (fun t => f (x, t)) y := by
  let i := ContinuousLinearMap.inr ℝ X Y
  let g : X × Y → ℂ := fun p => f (p + (x, 0))
  have hg : ContDiff ℝ ∞ g := f.smooth'.comp (contDiff_id.add contDiff_const)
  have he : (fun t => f (x, t)) = g ∘ i := by
    funext t
    simp [g, i]
  rw [he, i.iteratedFDeriv_comp_right hg y (by exact_mod_cast le_top : (n : ℕ∞ω) ≤ ∞)]
  change _ = (iteratedFDeriv ℝ n (fun p => f (p + (x, 0))) (i y)).compContinuousLinearMap _
  rw [iteratedFDeriv_comp_add_right]
  simp [partialJet, i]

private theorem partialJet_continuous (f : 𝓢(X × Y, ℂ)) (n : ℕ) :
    Continuous (partialJet f n) :=
  (ContinuousMultilinearMap.compContinuousLinearMapL
    (fun _ : Fin n => ContinuousLinearMap.inr ℝ X Y)).continuous.comp
      (f.smooth n).continuous_iteratedFDeriv'

private theorem partialJet_norm_le (f : 𝓢(X × Y, ℂ)) (n : ℕ) (p : X × Y) :
    ‖partialJet f n p‖ ≤ ‖iteratedFDeriv ℝ n f p‖ := by
  have hi : ∏ _ : Fin n, ‖ContinuousLinearMap.inr ℝ X Y‖ ≤ 1 :=
    Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun _ _ =>
      ContinuousLinearMap.norm_inr_le_one ℝ X Y)
  exact (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
    ((mul_le_mul_of_nonneg_left hi (norm_nonneg _)).trans_eq (mul_one _))

private theorem partialJet_weighted (f : 𝓢(X × Y, ℂ)) (k m n : ℕ) (p : X × Y) :
    ‖p.2‖ ^ k * max 1 (‖p.1‖ ^ m) * ‖partialJet f n p‖ ≤
      ({(k, n), (k + m, n)} : Finset (ℕ × ℕ)).sup (schwartzSeminormFamily ℂ (X × Y) ℂ) f := by
  let J : Finset (ℕ × ℕ) := {(k, n), (k + m, n)}
  have hs (i : ℕ) (hi : (i, n) ∈ J) :
      SchwartzMap.seminorm ℂ i n f ≤ J.sup (schwartzSeminormFamily ℂ (X × Y) ℂ) f :=
    (Finset.le_sup (f := schwartzSeminormFamily ℂ (X × Y) ℂ) hi) f
  have h1 : ‖p.1‖ ≤ ‖p‖ := by rw [Prod.norm_def]; exact le_max_left _ _
  have h2 : ‖p.2‖ ≤ ‖p‖ := by rw [Prod.norm_def]; exact le_max_right _ _
  have hn := partialJet_norm_le f n p
  by_cases hp : ‖p.1‖ ^ m ≤ 1
  · rw [max_eq_left hp, mul_one]
    apply le_trans _ ((SchwartzMap.le_seminorm ℂ k n f p).trans (hs k (by simp [J])))
    gcongr
  · rw [max_eq_right (le_of_not_ge hp)]
    -- The two weights live on different factors, so compare both with the product norm.
    apply le_trans _ ((SchwartzMap.le_seminorm ℂ (k + m) n f p).trans
      (hs (k + m) (by simp [J])))
    rw [pow_add]
    gcongr

/-- Restriction to a fixed first coordinate is a continuous linear map on Schwartz spaces. -/
def schwartzSlice (x : X) : 𝓢(X × Y, ℂ) →L[ℂ] 𝓢(Y, ℂ) :=
  SchwartzMap.mkCLM (fun f y => f (x, y)) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
    (fun f => f.smooth'.comp (contDiff_const.prodMk contDiff_id)) (by
      rintro ⟨k, n⟩
      refine ⟨{(k, n)}, 1, zero_le_one, fun f y => ?_⟩
      simp only [one_mul, Finset.sup_singleton]
      rw [← partialJet_eq]
      calc
        _ ≤ ‖(x, y)‖ ^ k * ‖iteratedFDeriv ℝ n f (x, y)‖ := by
          have h : ‖y‖ ≤ ‖(x, y)‖ := le_max_right _ _
          exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) h k)
            (partialJet_norm_le f n (x, y)) (norm_nonneg _) (by positivity)
        _ ≤ _ := SchwartzMap.le_seminorm ℂ k n f (x, y))

@[simp] theorem schwartzSlice_apply (f : 𝓢(X × Y, ℂ)) (x : X) (y : Y) :
    schwartzSlice x f y = f (x, y) := rfl

/-- Every slice seminorm decays rapidly in the first variable. -/
theorem schwartzSlice_weighted_seminorm (f : 𝓢(X × Y, ℂ)) (k m n : ℕ) (x : X) :
    max 1 (‖x‖ ^ m) * SchwartzMap.seminorm ℂ k n (schwartzSlice x f) ≤
      ({(k, n), (k + m, n)} : Finset (ℕ × ℕ)).sup (schwartzSeminormFamily ℂ (X × Y) ℂ) f := by
  let M := ({(k, n), (k + m, n)} : Finset (ℕ × ℕ)).sup (schwartzSeminormFamily ℂ (X × Y) ℂ) f
  have h : 0 < max 1 (‖x‖ ^ m) := zero_lt_one.trans_le (le_max_left _ _)
  apply (le_div_iff₀' h).mp
  apply SchwartzMap.seminorm_le_bound ℂ k n _ (div_nonneg (apply_nonneg _ _) h.le)
  intro y
  apply (le_div_iff₀ h).mpr
  rw [show (schwartzSlice x f : Y → ℂ) = fun y => f (x, y) from rfl, ← partialJet_eq]
  simpa only [mul_right_comm] using partialJet_weighted f k m n (x, y)

private theorem weighted_iteratedFDeriv_horizontal_bound (f : 𝓢(X × Y, ℂ)) (k n : ℕ)
    (x x' : X) (y : Y) :
    ‖y‖ ^ k * ‖iteratedFDeriv ℝ n f (x', y) - iteratedFDeriv ℝ n f (x, y)‖ ≤
      SchwartzMap.seminorm ℂ k (n + 1) f * ‖x' - x‖ := by
  let D := iteratedFDeriv ℝ n f
  let J (z : X) := ‖y‖ ^ k • D (z, y)
  have hd : Differentiable ℝ D :=
    f.smooth'.differentiable_iteratedFDeriv (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top n))
  have hj (z : X) : HasFDerivAt J
      (‖y‖ ^ k • ((fderiv ℝ D (z, y)).comp (ContinuousLinearMap.inl ℝ X Y))) z := by
    have hD : HasFDerivAt D (fderiv ℝ D (z, y)) (z, y) := (hd (z, y)).hasFDerivAt
    have hcomp : HasFDerivAt (fun z : X => D (z, y))
        ((fderiv ℝ D (z, y)).comp (ContinuousLinearMap.inl ℝ X Y)) z :=
      hD.comp z (hasFDerivAt_prodMk_left z y)
    exact hcomp.const_smul (‖y‖ ^ k)
  have ht (z : X) : ‖fderiv ℝ J z‖ ≤ SchwartzMap.seminorm ℂ k (n + 1) f := by
    rw [(hj z).fderiv]
    refine (ContinuousLinearMap.opNorm_smul_le _ _).trans ?_
    rw [Real.norm_of_nonneg (by positivity)]
    have hcomp : ‖(fderiv ℝ D (z, y)).comp (ContinuousLinearMap.inl ℝ X Y)‖ ≤
        ‖fderiv ℝ D (z, y)‖ :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_of_le_one_right (norm_nonneg _) (ContinuousLinearMap.norm_inl_le_one ℝ X Y))
    have he : ‖fderiv ℝ D (z, y)‖ = ‖iteratedFDeriv ℝ (n + 1) f (z, y)‖ := by
      rw [show D = iteratedFDeriv ℝ n f from rfl, fderiv_iteratedFDeriv]
      exact (continuousMultilinearCurryLeftEquiv ℝ
        (fun _ : Fin (n + 1) => X × Y) ℂ).norm_map _
    rw [he] at hcomp
    calc
      _ ≤ ‖(z, y)‖ ^ k * ‖iteratedFDeriv ℝ (n + 1) f (z, y)‖ := by
        have h : ‖y‖ ≤ ‖(z, y)‖ := le_max_right _ _
        exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) h k) hcomp
          (ContinuousLinearMap.opNorm_nonneg _) (by positivity)
      _ ≤ _ := SchwartzMap.le_seminorm ℂ k (n + 1) f (z, y)
  have hmv := (convex_univ : Convex ℝ (univ : Set X)).norm_image_sub_le_of_norm_fderiv_le
    (fun z _ => (hj z).differentiableAt) (fun z _ => ht z) (mem_univ x) (mem_univ x')
  simpa only [J, D, ← smul_sub, norm_smul, Real.norm_of_nonneg (pow_nonneg (norm_nonneg y) k)]
    using hmv

private theorem weighted_partialJet_horizontal_bound (f : 𝓢(X × Y, ℂ)) (k n : ℕ)
    (x x' : X) (y : Y) :
    ‖y‖ ^ k * ‖partialJet f n (x', y) - partialJet f n (x, y)‖ ≤
      SchwartzMap.seminorm ℂ k (n + 1) f * ‖x' - x‖ := by
  let L : ContinuousMultilinearMap ℝ (fun _ : Fin n => X × Y) ℂ →L[ℝ] Jet Y n :=
    ContinuousMultilinearMap.compContinuousLinearMapL
      (fun _ : Fin n => ContinuousLinearMap.inr ℝ X Y)
  have hL (T : ContinuousMultilinearMap ℝ (fun _ : Fin n => X × Y) ℂ) : ‖L T‖ ≤ ‖T‖ := by
    have hi : ∏ _ : Fin n, ‖ContinuousLinearMap.inr ℝ X Y‖ ≤ 1 :=
      Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun _ _ =>
        ContinuousLinearMap.norm_inr_le_one ℝ X Y)
    exact (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
      (mul_le_of_le_one_right (norm_nonneg _) hi)
  change ‖y‖ ^ k * ‖L (iteratedFDeriv ℝ n f (x', y)) - L (iteratedFDeriv ℝ n f (x, y))‖ ≤ _
  rw [← map_sub]
  exact (mul_le_mul_of_nonneg_left (hL _) (by positivity)).trans
    (weighted_iteratedFDeriv_horizontal_bound f k n x x' y)

/-- Each Schwartz seminorm of a slice difference is controlled by the first-variable separation. -/
theorem schwartzSlice_sub_seminorm (f : 𝓢(X × Y, ℂ)) (k n : ℕ) (x x' : X) :
    SchwartzMap.seminorm ℂ k n (schwartzSlice x' f - schwartzSlice x f) ≤
      SchwartzMap.seminorm ℂ k (n + 1) f * ‖x' - x‖ := by
  apply SchwartzMap.seminorm_le_bound ℂ k n _ (by positivity)
  intro y
  change ‖y‖ ^ k * ‖iteratedFDeriv ℝ n (⇑(schwartzSlice x' f) - ⇑(schwartzSlice x f)) y‖ ≤ _
  rw [iteratedFDeriv_sub_apply ((schwartzSlice x' f).smooth n).contDiffAt
    ((schwartzSlice x f).smooth n).contDiffAt]
  change ‖y‖ ^ k * ‖iteratedFDeriv ℝ n (fun t => f (x', t)) y -
    iteratedFDeriv ℝ n (fun t => f (x, t)) y‖ ≤ _
  rw [← partialJet_eq, ← partialJet_eq]
  exact weighted_partialJet_horizontal_bound f k n x x' y

/-- Currying a joint Schwartz function is continuous for the full derivative topology. -/
theorem continuous_schwartzSlice (f : 𝓢(X × Y, ℂ)) :
    Continuous (fun x : X => schwartzSlice x f) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  apply ((schwartz_withSeminorms ℂ Y ℂ).tendsto_nhds _ _).mpr
  rintro ⟨k, n⟩ ε hε
  have hlim : Tendsto (fun z : X => SchwartzMap.seminorm ℂ k (n + 1) f * ‖z - x‖)
      (𝓝 x) (𝓝 0) := by
    have hc : Continuous (fun z : X => SchwartzMap.seminorm ℂ k (n + 1) f * ‖z - x‖) :=
      continuous_const.mul ((continuous_id.sub continuous_const).norm)
    simpa only [sub_self, norm_zero, mul_zero] using (hc.continuousAt (x := x)).tendsto
  filter_upwards [hlim.eventually (Iio_mem_nhds hε)] with z hz
  exact (schwartzSlice_sub_seminorm f k n x z).trans_lt hz

private theorem hasDerivAt_partialJet_horizontal (f : 𝓢(X × Y, ℂ)) (n : ℕ)
    (x v : X) (y : Y) (t : ℝ) :
    HasDerivAt (fun a : ℝ => partialJet f n (x + a • v, y))
      (partialJet (LineDeriv.lineDerivOp (v, (0 : Y)) f) n (x + t • v, y)) t := by
  let D := iteratedFDeriv ℝ n f
  let L : ContinuousMultilinearMap ℝ (fun _ : Fin n => X × Y) ℂ →L[ℝ] Jet Y n :=
    ContinuousMultilinearMap.compContinuousLinearMapL
      (fun _ : Fin n => ContinuousLinearMap.inr ℝ X Y)
  let p (a : ℝ) := (x + a • v, y)
  let w : X × Y := (v, 0)
  have hline : HasDerivAt p w t := by
    have h : HasDerivAt (fun a : ℝ => (x, y) + a • w) w t := by
      simpa using (((hasDerivAt_id t).smul_const w).const_add (x, y))
    exact h.congr_of_eventuallyEq (.of_forall fun a => by simp [p, w])
  have hD : HasFDerivAt D (fderiv ℝ D (p t)) (p t) :=
    (f.smooth'.differentiable_iteratedFDeriv
      (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top n)) _).hasFDerivAt
  have hcomp := (L.hasFDerivAt.comp (p t) hD).comp_hasDerivAt t hline
  change HasDerivAt (fun a => partialJet f n (x + a • v, y))
    (L ((fderiv ℝ D (p t)) w)) t at hcomp
  convert hcomp using 1
  ext m
  change iteratedFDeriv ℝ n (⇑(LineDeriv.lineDerivOp w f)) (p t)
      (fun i => ContinuousLinearMap.inr ℝ X Y (m i)) =
    (fderiv ℝ D (p t)) w (fun i => ContinuousLinearMap.inr ℝ X Y (m i))
  rw [show (⇑(LineDeriv.lineDerivOp w f) : X × Y → ℂ) =
      fun z => fderiv ℝ f z w from funext (SchwartzMap.lineDerivOp_apply_eq_fderiv w f)]
  exact iteratedFDeriv_directional_apply (f := (f : X × Y → ℂ)) f.smooth' w
    (fun i => ContinuousLinearMap.inr ℝ X Y (m i)) (p t)

/-- Subtracting the horizontal derivative leaves a quadratic remainder in every Schwartz seminorm. -/
theorem schwartzSlice_directional_remainder (f : 𝓢(X × Y, ℂ)) (k n : ℕ)
    (x v : X) (t : ℝ) :
    SchwartzMap.seminorm ℂ k n
        (schwartzSlice (x + t • v) f - schwartzSlice x f -
          t • schwartzSlice x (LineDeriv.lineDerivOp (v, (0 : Y)) f)) ≤
      SchwartzMap.seminorm ℂ k (n + 1) (LineDeriv.lineDerivOp (v, (0 : Y)) f) *
        ‖v‖ * ‖t‖ ^ 2 := by
  let df := LineDeriv.lineDerivOp (v, (0 : Y)) f
  let M := SchwartzMap.seminorm ℂ k (n + 1) df
  apply SchwartzMap.seminorm_le_bound ℂ k n _ (by positivity)
  intro y
  let F (r : ℝ) := partialJet f n (x + r • v, y)
  let G (r : ℝ) := partialJet df n (x + r • v, y)
  let R (r : ℝ) := ‖y‖ ^ k • (F r - F 0 - r • G 0)
  have hF (r : ℝ) : HasDerivAt F (G r) r := hasDerivAt_partialJet_horizontal f n x v y r
  have hR (r : ℝ) : HasDerivAt R (‖y‖ ^ k • (G r - G 0)) r := by
    have ht : HasDerivAt (fun r : ℝ => r • G 0) (G 0) r := by
      simpa using (hasDerivAt_id r).smul_const (G 0)
    exact (((hF r).sub_const (F 0)).sub ht).const_smul (‖y‖ ^ k)
  let B := Metric.closedBall (0 : ℝ) ‖t‖
  have hB (r : ℝ) (hr : r ∈ B) : ‖‖y‖ ^ k • (G r - G 0)‖ ≤ M * ‖v‖ * ‖t‖ := by
    have hr' : ‖r‖ ≤ ‖t‖ := mem_closedBall_zero_iff.mp hr
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    have h := weighted_partialJet_horizontal_bound df k n x (x + r • v) y
    simp only [G, zero_smul, add_zero, add_sub_cancel_left, norm_smul] at h ⊢
    exact h.trans (by
      change M * (‖r‖ * ‖v‖) ≤ M * ‖v‖ * ‖t‖
      rw [mul_comm ‖r‖ ‖v‖, ← mul_assoc]
      exact mul_le_mul_of_nonneg_left hr' (by positivity))
  have he := (convex_closedBall (0 : ℝ) ‖t‖).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun r _ => (hR r).hasDerivWithinAt) hB
    (mem_closedBall_zero_iff.mpr (by simp : ‖(0 : ℝ)‖ ≤ ‖t‖))
    (mem_closedBall_zero_iff.mpr le_rfl)
  have hR0 : R 0 = 0 := by
    change ‖y‖ ^ k • (F 0 - F 0 - (0 : ℝ) • G 0) = _
    ext m
    simp [smul_apply]
  have he' : ‖R t‖ ≤ M * ‖v‖ * ‖t‖ ^ 2 := by
    simpa only [hR0, sub_zero, pow_two, mul_assoc] using he
  let u := schwartzSlice (x + t • v) f
  let w := schwartzSlice x f
  let b := schwartzSlice x df
  have hjet : iteratedFDeriv ℝ n (⇑(u - w - t • b)) y =
      F t - F 0 - t • G 0 := by
    change iteratedFDeriv ℝ n (⇑u - ⇑w - t • ⇑b) y = _
    have huw : ContDiff ℝ n ((u : Y → ℂ) - (w : Y → ℂ)) :=
      (u.smooth n).sub (w.smooth n)
    have hb : ContDiff ℝ n (t • (b : Y → ℂ)) := (b.smooth n).const_smul t
    rw [iteratedFDeriv_sub_apply huw.contDiffAt hb.contDiffAt,
      iteratedFDeriv_sub_apply (u.smooth n).contDiffAt (w.smooth n).contDiffAt,
      iteratedFDeriv_const_smul_apply (b.smooth n).contDiffAt]
    change iteratedFDeriv ℝ n (fun z => f (x + t • v, z)) y -
      iteratedFDeriv ℝ n (fun z => f (x, z)) y -
      t • iteratedFDeriv ℝ n (fun z => df (x, z)) y = _
    rw [← partialJet_eq, ← partialJet_eq, ← partialJet_eq]
    simp [F, G]
  change ‖y‖ ^ k * ‖iteratedFDeriv ℝ n (⇑(u - w - t • b)) y‖ ≤ _
  rw [hjet]
  simpa only [R, norm_smul, Real.norm_of_nonneg (pow_nonneg (norm_nonneg y) k)] using he'

/-- Horizontal difference quotients of a slice converge in the Schwartz topology. -/
theorem schwartzSlice_directional_tendsto (f : 𝓢(X × Y, ℂ)) (x v : X) :
    Tendsto (fun t : ℝ => t⁻¹ • (schwartzSlice (x + t • v) f - schwartzSlice x f))
      (𝓝[≠] 0) (𝓝 (schwartzSlice x (LineDeriv.lineDerivOp (v, (0 : Y)) f))) := by
  let df := LineDeriv.lineDerivOp (v, (0 : Y)) f
  let b := schwartzSlice x df
  apply ((schwartz_withSeminorms ℂ Y ℂ).tendsto_nhds _ _).mpr
  rintro ⟨k, n⟩ ε hε
  let M := SchwartzMap.seminorm ℂ k (n + 1) df * ‖v‖
  have hc : Continuous (fun t : ℝ => M * ‖t‖) := continuous_const.mul continuous_norm
  have hlim : Tendsto (fun t : ℝ => M * ‖t‖) (𝓝[≠] 0) (𝓝 0) := by
    simpa only [norm_zero, mul_zero] using
      (hc.continuousAt (x := 0)).continuousWithinAt.tendsto
  filter_upwards [hlim.eventually (Iio_mem_nhds hε), self_mem_nhdsWithin] with t ht hne
  have hne' : t ≠ 0 := hne
  change SchwartzMap.seminorm ℂ k n
    (t⁻¹ • (schwartzSlice (x + t • v) f - schwartzSlice x f) - b) < ε
  rw [show t⁻¹ • (schwartzSlice (x + t • v) f - schwartzSlice x f) - b =
    t⁻¹ • (schwartzSlice (x + t • v) f - schwartzSlice x f - t • b) by
      simp only [smul_sub, inv_smul_smul₀ hne']]
  let P := schwartzSlice (x + t • v) f - schwartzSlice x f - t • b
  change SchwartzMap.seminorm ℂ k n (((t⁻¹ : ℝ) : ℂ) • P) < ε
  rw [map_smul_eq_mul, Complex.norm_real, norm_inv]
  have hb : SchwartzMap.seminorm ℂ k n P ≤ M * ‖t‖ ^ 2 :=
    schwartzSlice_directional_remainder f k n x v t
  apply (mul_le_mul_of_nonneg_left hb (by positivity)).trans_lt
  rwa [show ‖t‖⁻¹ * (M * ‖t‖ ^ 2) = M * ‖t‖ by
    field_simp [norm_ne_zero_iff.mpr hne']]

/-- Scalar tests differentiate a horizontal slice by differentiating the joint Schwartz function. -/
theorem schwartzSlice_hasDerivAt_scalar (f : 𝓢(X × Y, ℂ)) (x v : X)
    (l : 𝓢(Y, ℂ) →L[ℂ] ℂ) :
    HasDerivAt (fun t : ℝ => l (schwartzSlice (x + t • v) f))
      (l (schwartzSlice x (LineDeriv.lineDerivOp (v, (0 : Y)) f))) 0 := by
  apply hasDerivAt_iff_tendsto_slope_zero.mpr
  let L := l.restrictScalars ℝ
  let b := schwartzSlice x (LineDeriv.lineDerivOp (v, (0 : Y)) f)
  let u (t : ℝ) := schwartzSlice (x + t • v) f
  have hb : Tendsto (fun t : ℝ => t⁻¹ • (u t - u 0)) (𝓝[≠] 0) (𝓝 b) := by
    have hu0 : u 0 = schwartzSlice x f := by simp [u]
    rw [hu0]
    exact schwartzSlice_directional_tendsto f x v
  have hL : Tendsto L (𝓝 b) (𝓝 (L b)) := L.continuous.continuousAt
  have h := hL.comp hb
  simp only [zero_add]
  change Tendsto (fun t => t⁻¹ • (L (u t) - L (u 0))) (𝓝[≠] 0) (𝓝 (L b))
  refine h.congr' (.of_forall fun t => ?_)
  change L (t⁻¹ • (u t - u 0)) = _
  rw [map_smul, map_sub]

/-- Divide the kernel norm by the polynomial decay controlled by the input Schwartz test. -/
def schwartzKernelMajorant (γ : T → X) (w : T → ℂ) (m : ℕ) (t : T) : ℝ :=
  ‖w t‖ / max 1 (‖γ t‖ ^ m)

omit [NormedSpace ℝ X] [MeasurableSpace T] in
private theorem schwartzKernelMajorant_nonneg (γ : T → X) (w : T → ℂ) (m : ℕ) (t : T) :
    0 ≤ schwartzKernelMajorant γ w m t :=
  div_nonneg (norm_nonneg _) (le_trans zero_le_one (le_max_left _ _))

omit [MeasurableSpace T] in
private theorem partialWeightedJet_bound (γ : T → X) (w : T → ℂ) (m : ℕ)
    (f : 𝓢(X × Y, ℂ)) (k n : ℕ) (t : T) (y : Y) :
    ‖y‖ ^ k * ‖w t • partialJet f n (γ t, y)‖ ≤
      ({(k, n), (k + m, n)} : Finset (ℕ × ℕ)).sup (schwartzSeminormFamily ℂ (X × Y) ℂ) f *
        schwartzKernelMajorant γ w m t := by
  rw [norm_smul, schwartzKernelMajorant, ← mul_assoc, ← mul_div_assoc]
  apply (le_div_iff₀ (zero_lt_one.trans_le (le_max_left _ _))).mpr
  calc
    _ = ‖w t‖ * (‖y‖ ^ k * max 1 (‖γ t‖ ^ m) * ‖partialJet f n (γ t, y)‖) := by ring
    _ ≤ _ := (mul_le_mul_of_nonneg_left (partialJet_weighted f k m n (γ t, y))
      (norm_nonneg _)).trans_eq (mul_comm _ _)

variable [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]

variable {μ : Measure T} {γ : T → X} {w : T → ℂ} {m : ℕ}
  (hγ : Measurable γ) (hw : AEStronglyMeasurable w μ)
  (hM : Integrable (schwartzKernelMajorant γ w m) μ)

include hγ hw hM

private theorem partialWeightedJet_integrable (f : 𝓢(X × Y, ℂ)) (n : ℕ) (y : Y) :
    Integrable (fun t => w t • partialJet f n (γ t, y)) μ := by
  have hc : Continuous (fun x : X => partialJet f n (x, y)) :=
    (partialJet_continuous f n).comp (continuous_id.prodMk continuous_const)
  have hmeas := (hc.stronglyMeasurable.comp_measurable hγ).aestronglyMeasurable (μ := μ)
  have hm : AEStronglyMeasurable (fun t => w t • partialJet f n (γ t, y)) μ := hw.smul hmeas
  apply (hM.const_mul _).mono' hm
  exact Eventually.of_forall fun t => by
    simpa only [pow_zero, one_mul] using partialWeightedJet_bound γ w m f 0 n t y

private def partialIntegralJet (γ : T → X) (w : T → ℂ) (μ : Measure T)
    (f : 𝓢(X × Y, ℂ)) (n : ℕ) (y : Y) : Jet Y n :=
  ∫ t, w t • partialJet f n (γ t, y) ∂μ

set_option backward.isDefEq.respectTransparency false in
private theorem partialIntegralJet_hasFDerivAt (f : 𝓢(X × Y, ℂ)) (n : ℕ) (y : Y) :
    HasFDerivAt (partialIntegralJet γ w μ f n)
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => Y) ℂ
        (partialIntegralJet γ w μ f (n + 1) y)) y := by
  let C := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => Y) ℂ
  have hI (n : ℕ) (y : Y) := partialWeightedJet_integrable hγ hw hM f n y
  change HasFDerivAt _ (C (∫ t, w t • partialJet f (n + 1) (γ t, y) ∂μ)) y
  have hcomm : (∫ t, C (w t • partialJet f (n + 1) (γ t, y)) ∂μ) =
      C (∫ t, w t • partialJet f (n + 1) (γ t, y) ∂μ) := by
    simpa only [LinearIsometryEquiv.coe_toContinuousLinearEquiv] using
      (ContinuousLinearEquiv.integral_comp_comm (μ := μ) (𝕜 := ℝ) (E := Jet Y (n + 1))
        (F := Y →L[ℝ] Jet Y n) C.toContinuousLinearEquiv
        (fun t : T => w t • partialJet f (n + 1) (γ t, y)))
  rw [← hcomm]
  let P := ({(0, n + 1), (m, n + 1)} : Finset (ℕ × ℕ)).sup
    (schwartzSeminormFamily ℂ (X × Y) ℂ) f
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (s := univ)
    (bound := fun t => P * schwartzKernelMajorant γ w m t)
    (F := fun y t => w t • partialJet f n (γ t, y))
    (F' := fun y t => C (w t • partialJet f (n + 1) (γ t, y)))
    univ_mem (.of_forall fun y => (hI n y).aestronglyMeasurable) (hI n y)
    (C.continuous.comp_aestronglyMeasurable (hI (n + 1) y).aestronglyMeasurable) ?_
    (hM.const_mul P) ?_
  · exact Eventually.of_forall fun t y _ => by
      rw [C.norm_map]
      simpa only [P, pow_zero, one_mul, Nat.zero_add] using
        partialWeightedJet_bound γ w m f 0 (n + 1) t y
  · exact Eventually.of_forall fun t y _ => by
      let g : Y → ℂ := fun a => f (γ t, a)
      have hg : ContDiff ℝ ∞ g := f.smooth'.comp (contDiff_const.prodMk contDiff_id)
      have he (j : ℕ) : (fun a => partialJet f j (γ t, a)) = iteratedFDeriv ℝ j g :=
        funext fun a => partialJet_eq f j (γ t) a
      have hd : HasFDerivAt (iteratedFDeriv ℝ n g)
          (C (iteratedFDeriv ℝ (n + 1) g y)) y := by
        rw [← Function.comp_apply (f := C), ← fderiv_iteratedFDeriv]
        exact ((hg.differentiable_iteratedFDeriv (ENat.natCast_lt_of_coe_top_le_withTop le_rfl n)).differentiableAt).hasFDerivAt
      have he' : C (w t • partialJet f (n + 1) (γ t, y)) =
          w t • C (iteratedFDeriv ℝ (n + 1) g y) := by
        rw [partialJet_eq]
        rfl
      rw [he']
      have hfun : (fun a => w t • partialJet f n (γ t, a)) =
          (fun a => w t • iteratedFDeriv ℝ n g a) := by
        funext a
        rw [show partialJet f n (γ t, a) = iteratedFDeriv ℝ n g a from congrFun (he n) a]
      rw [hfun]
      exact hd.const_smul (w t)

/-- Each derivative in the remaining variable is obtained by differentiating
the original test in that variable under the integral. -/
private theorem partialIntegral_iteratedFDeriv (f : 𝓢(X × Y, ℂ)) (n : ℕ) :
    iteratedFDeriv ℝ n (fun y => ∫ t, w t * f (γ t, y) ∂μ) =
      partialIntegralJet γ w μ f n := by
  induction n with
  | zero =>
    funext y
    ext a
    rw [partialIntegralJet, ContinuousMultilinearMap.integral_apply
      (partialWeightedJet_integrable hγ hw hM f 0 y)]
    simp [partialJet, iteratedFDeriv_zero_apply]
  | succ n ih =>
    rw [iteratedFDeriv_succ_eq_comp_left, ih]
    funext y
    rw [Function.comp_apply, (partialIntegralJet_hasFDerivAt hγ hw hM f n y).fderiv]
    exact LinearIsometryEquiv.symm_apply_apply _ _

/-- Every pointwise integral in a Schwartz contraction is absolutely convergent. -/
theorem schwartzPartialIntegral_integrable (f : 𝓢(X × Y, ℂ)) (y : Y) :
    Integrable (fun t => w t * f (γ t, y)) μ := by
  have h := partialWeightedJet_integrable hγ hw hM f 0 y
  exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 0 => Y) ℂ (fun i => nomatch i)).integrable_comp
    h |>.congr (.of_forall fun t => by simp [partialJet, iteratedFDeriv_zero_apply])

private theorem partialIntegral_weighted_deriv_bound (f : 𝓢(X × Y, ℂ)) (k n : ℕ) (y : Y) :
    ‖y‖ ^ k * ‖iteratedFDeriv ℝ n (fun y => ∫ t, w t * f (γ t, y) ∂μ) y‖ ≤
      (∫ t, schwartzKernelMajorant γ w m t ∂μ) *
        ({(k, n), (k + m, n)} : Finset (ℕ × ℕ)).sup (schwartzSeminormFamily ℂ (X × Y) ℂ) f := by
  rw [partialIntegral_iteratedFDeriv hγ hw hM, partialIntegralJet]
  let P := ({(k, n), (k + m, n)} : Finset (ℕ × ℕ)).sup (schwartzSeminormFamily ℂ (X × Y) ℂ) f
  rw [← Real.norm_of_nonneg (pow_nonneg (norm_nonneg y) k), ← norm_smul, ← integral_smul]
  rw [mul_comm _ P, ← integral_const_mul]
  apply norm_integral_le_of_norm_le (hM.const_mul P)
  exact .of_forall fun t => by
    rw [norm_smul, Real.norm_of_nonneg (pow_nonneg (norm_nonneg y) k)]
    exact partialWeightedJet_bound γ w m f k n t y

/-- Integrate a Schwartz function in one coordinate against a kernel whose
growth is controlled by an integrable polynomially weighted majorant. The
output is a Schwartz function in the remaining variable, even when the
input couples the two coordinates. -/
def schwartzPartialIntegralCLM : 𝓢(X × Y, ℂ) →L[ℂ] 𝓢(Y, ℂ) :=
  SchwartzMap.mkCLM (fun f y => ∫ t, w t * f (γ t, y) ∂μ)
    (fun f g y => by
      simpa only [add_apply, mul_add] using
        integral_add (schwartzPartialIntegral_integrable hγ hw hM f y)
          (schwartzPartialIntegral_integrable hγ hw hM g y))
    (fun c f y => by
      simpa only [smul_apply, RingHom.id_apply, smul_eq_mul, mul_left_comm] using
        integral_const_mul c (fun t => w t * f (γ t, y)))
    (fun f => by
      apply contDiff_of_differentiable_iteratedFDeriv
      intro n _
      rw [partialIntegral_iteratedFDeriv hγ hw hM]
      exact fun y => (partialIntegralJet_hasFDerivAt hγ hw hM f n y).differentiableAt)
    (fun ⟨k, n⟩ => ⟨{(k, n), (k + m, n)}, ∫ t, schwartzKernelMajorant γ w m t ∂μ,
      integral_nonneg (schwartzKernelMajorant_nonneg γ w m),
      fun f y => partialIntegral_weighted_deriv_bound hγ hw hM f k n y⟩)

@[simp] theorem schwartzPartialIntegralCLM_apply (f : 𝓢(X × Y, ℂ)) (y : Y) :
    schwartzPartialIntegralCLM hγ hw hM f y = ∫ t, w t * f (γ t, y) ∂μ := rfl

/-- The contraction preserves vanishing of an entire derivative on the
fiber over a point of the retained space. -/
theorem schwartzPartialIntegralCLM_iteratedFDeriv_eq_zero
    (f : 𝓢(X × Y, ℂ)) (n : ℕ) (y : Y)
    (hf : ∀ x : X, iteratedFDeriv ℝ n f (x, y) = 0) :
    iteratedFDeriv ℝ n (schwartzPartialIntegralCLM hγ hw hM f) y = 0 := by
  change iteratedFDeriv ℝ n (fun y => ∫ t, w t * f (γ t, y) ∂μ) y = 0
  rw [partialIntegral_iteratedFDeriv hγ hw hM]
  change (∫ t, w t • partialJet f n (γ t, y) ∂μ) = 0
  have he (t : T) : partialJet f n (γ t, y) = 0 := by
    unfold partialJet
    rw [hf]
    ext a
    simp
  have hh : (fun t : T ↦ w t • partialJet f n (γ t, y)) = fun _ ↦ (0 : Jet Y n) := by
    funext t
    rw [he]
    ext a
    simp
  rw [hh, integral_zero]

/-- The norm of an integrable kernel majorant controls each resulting seminorm.
This estimate can be used uniformly in families of kernels. -/
theorem schwartzPartialIntegralCLM_seminorm_le (f : 𝓢(X × Y, ℂ)) (k n : ℕ) :
    SchwartzMap.seminorm ℂ k n (schwartzPartialIntegralCLM hγ hw hM f) ≤
      (∫ t, schwartzKernelMajorant γ w m t ∂μ) *
        ({(k, n), (k + m, n)} : Finset (ℕ × ℕ)).sup (schwartzSeminormFamily ℂ (X × Y) ℂ) f := by
  refine SchwartzMap.seminorm_le_bound ℂ k n _ (mul_nonneg
    (integral_nonneg (schwartzKernelMajorant_nonneg γ w m)) (apply_nonneg _ _)) ?_
  exact fun y => partialIntegral_weighted_deriv_bound hγ hw hM f k n y

end

end Masullo
