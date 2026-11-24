import ArchimedeanProductZeta
import ArchimedeanFundamentalDomain
import ArchimedeanLogFibreKernel

open NumberField NumberField.Units.dirichletUnitTheorem Set Topology
open scoped SchwartzMap NumberField Classical

namespace Masullo
noncomputable section

variable (F : Type*) [Field F] [NumberField F]

/-- Each multiplicity-weighted logarithm is continuous on the units. -/
theorem fullArchLog_coordinate_continuous (w : InfinitePlace F) :
    Continuous (fun a : InfiniteIdeles F => fullArchLog F a w) := by
  have hv : Continuous (fun a : InfiniteIdeles F => a.val w) :=
    (continuous_apply w).comp (Units.continuous_val : Continuous (Units.val : InfiniteIdeles F → InfiniteAdeleRing F))
  have hC := hv.norm
  apply continuous_iff_continuousAt.mpr
  intro a
  have h : ‖a.val w‖ ≠ 0 := norm_ne_zero_iff.mpr (infiniteCoord_nonzero F a w)
  have hl : ContinuousAt (fun b : InfiniteIdeles F => Real.log ‖b.val w‖) a :=
    (Real.continuousAt_log (x := ‖a.val w‖) h).comp
      (f := fun b : InfiniteIdeles F => ‖b.val w‖) hC.continuousAt
  exact continuous_const.continuousAt.mul hl

/-- A change by at most one in a logarithm costs at most a factor of `exp 1`
in the one-sided estimate. -/
theorem archLogFactor_le_of_shift {x y : ℝ} (h : |x - y| ≤ 1) :
    min 1 (Real.exp (-x)) ≤ Real.exp 1 * min 1 (Real.exp (-y)) := by
  rw [mul_min_of_nonneg _ _ (Real.exp_pos 1).le, mul_one, ← Real.exp_add]
  apply min_le_min (Real.one_le_exp zero_le_one)
  apply Real.exp_le_exp.mpr
  linarith only [(abs_le.mp h).1]

/-- Two Schwartz seminorms control the logarithmic majorant and its norm weight. -/
def archLogFibreSchwartzControl (k : ℕ) (f : 𝓢(mixedEmbedding.mixedSpace F, ℂ)) : ℝ :=
  max (SchwartzMap.seminorm ℂ 0 0 f)
    (SchwartzMap.seminorm ℂ (2 * (Fintype.card (InfinitePlace F) * (k + 1))) 0 f)

/-- A Schwartz test is bounded by the product of one-sided exponentials
in the actual multiplicity-weighted logarithms of the infinite places. -/
theorem archSchwartz_fullArchLog_weighted_le (k : ℕ) (f : 𝓢(mixedEmbedding.mixedSpace F, ℂ))
    (a : (InfiniteAdeleRing F)ˣ) :
    Real.exp ((k : ℝ) * max 0 (Real.log ‖a.val‖)) *
        ‖f (InfiniteAdeleRing.ringEquiv_mixedSpace F a.val)‖ ≤
      archLogFibreSchwartzControl F k f *
        ∏ w : InfinitePlace F, min 1 (Real.exp (-fullArchLog F a w)) := by
  let n := Fintype.card (InfinitePlace F)
  let p := SchwartzMap.seminorm ℂ 0 0 f
  let d := n * (k + 1)
  let q := SchwartzMap.seminorm ℂ (2 * d) 0 f
  let C := max p q
  have hC : 0 ≤ C := (apply_nonneg _ f).trans (le_max_left p q)
  let x := InfiniteAdeleRing.ringEquiv_mixedSpace F a.val
  have hv (w : InfinitePlace F) : 0 < ‖a.val w‖ :=
    norm_pos_iff.mpr (Units.map (Pi.evalRingHom InfinitePlace.Completion w).toMonoidHom a).ne_zero
  have hx (w : InfinitePlace F) : ‖a.val w‖ ≤ ‖x‖ := by
    have he : mixedEmbedding.normAtPlace w x = ‖a.val w‖ := by
      by_cases hw : w.IsReal
      · rw [mixedEmbedding.normAtPlace_apply_of_isReal hw]
        exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero
          (map_zero _) (a.val w)
      · let hw' := InfinitePlace.not_isReal_iff_isComplex.mp hw
        rw [mixedEmbedding.normAtPlace_apply_of_isComplex hw']
        exact (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero
          (map_zero _) (a.val w)
    rw [← he, mixedEmbedding.norm_eq_sup'_normAtPlace]
    exact Finset.le_sup' (fun w => mixedEmbedding.normAtPlace w x) (Finset.mem_univ w)
  let L := max 0 (Real.log ‖x‖)
  have hl (w : InfinitePlace F) : fullArchLog F a w ≤ 2 * L := by
    have hm : w.mult ≤ 2 := by unfold InfinitePlace.mult; split_ifs <;> norm_num
    have hm' : (w.mult : ℝ) ≤ 2 := by exact_mod_cast hm
    change (w.mult : ℝ) * Real.log ‖a.val w‖ ≤ _
    exact (mul_le_mul_of_nonneg_left ((Real.log_le_log (hv w) (hx w)).trans (le_max_right _ _))
      (Nat.cast_nonneg _)).trans (mul_le_mul_of_nonneg_right hm' (le_max_left _ _))
  have hprod : Real.exp (-2 * L) ^ n ≤ ∏ w : InfinitePlace F, min 1 (Real.exp (-fullArchLog F a w)) := by
    have he : (∏ _w : InfinitePlace F, Real.exp (-2 * L)) = Real.exp (-2 * L) ^ n := by simp [n]
    rw [← he]
    apply Finset.prod_le_prod (fun _ _ => (Real.exp_pos _).le)
    intro w _
    have hL : 0 ≤ L := le_max_left _ _
    exact le_min (Real.exp_le_one_iff.mpr (by linarith))
      (Real.exp_le_exp.mpr (by linarith only [hl w]))
  let P := max 0 (Real.log ‖a.val‖)
  have hP : P ≤ 2 * (n : ℝ) * L := by
    apply max_le (by positivity [show 0 ≤ L from le_max_left _ _])
    rw [← fullArchLog_sum]
    have hs := Finset.sum_le_sum (s := (Finset.univ : Finset (InfinitePlace F))) (fun w _ => hl w)
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, n, mul_assoc, mul_left_comm] using hs
  have hf : ‖f x‖ ≤ C * Real.exp (-2 * L) ^ d := by
    rcases le_or_gt ‖x‖ 1 with hn | hn
    · have hL : L = 0 := max_eq_left (Real.log_nonpos (norm_nonneg _) hn)
      rw [hL, mul_zero, Real.exp_zero, one_pow, mul_one]
      exact (SchwartzMap.norm_le_seminorm ℂ f x).trans (le_max_left _ _)
    · have hL : L = Real.log ‖x‖ := max_eq_right (Real.log_nonneg hn.le)
      have hpow : Real.exp (-2 * L) ^ d = (‖x‖ ^ (2 * d))⁻¹ := by
        rw [hL, show -2 * Real.log ‖x‖ = -Real.log (‖x‖ ^ 2) by rw [Real.log_pow]; push_cast; ring,
          Real.exp_neg, Real.exp_log (by positivity), inv_pow, ← pow_mul]
      rw [hpow, ← div_eq_mul_inv]
      exact (le_div_iff₀' (by positivity)).mpr
        ((SchwartzMap.norm_pow_mul_le_seminorm ℂ f (2 * d) x).trans (le_max_right _ _))
  have hE : Real.exp ((k : ℝ) * P) * Real.exp (-2 * L) ^ d ≤ Real.exp (-2 * L) ^ n := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hp := mul_le_mul_of_nonneg_left hP (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
    have he : (d : ℝ) = (n : ℝ) * ((k : ℝ) + 1) := by simp [d]
    rw [he]
    nlinarith only [hp]
  change Real.exp ((k : ℝ) * P) * ‖f x‖ ≤ _
  calc
    _ ≤ Real.exp ((k : ℝ) * P) * (C * Real.exp (-2 * L) ^ d) :=
      mul_le_mul_of_nonneg_left hf (Real.exp_pos _).le
    _ = C * (Real.exp ((k : ℝ) * P) * Real.exp (-2 * L) ^ d) := by ring
    _ ≤ C * Real.exp (-2 * L) ^ n := mul_le_mul_of_nonneg_left hE hC
    _ ≤ _ := mul_le_mul_of_nonneg_left hprod hC

/-- Existence form of the explicit weighted logarithmic estimate. -/
theorem archSchwartz_fullArchLog_weighted_bound (k : ℕ) (f : 𝓢(mixedEmbedding.mixedSpace F, ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : (InfiniteAdeleRing F)ˣ,
      Real.exp ((k : ℝ) * max 0 (Real.log ‖a.val‖)) *
        ‖f (InfiniteAdeleRing.ringEquiv_mixedSpace F a.val)‖ ≤
        C * ∏ w : InfinitePlace F, min 1 (Real.exp (-fullArchLog F a w)) :=
  ⟨archLogFibreSchwartzControl F k f, (apply_nonneg _ f).trans (le_max_left _ _),
    archSchwartz_fullArchLog_weighted_le F k f⟩

/-- The unweighted Schwartz bound on multiplicity-weighted logarithms. -/
theorem archSchwartz_fullArchLog_bound (f : 𝓢(mixedEmbedding.mixedSpace F, ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : (InfiniteAdeleRing F)ˣ,
      ‖f (InfiniteAdeleRing.ringEquiv_mixedSpace F a.val)‖ ≤
        C * ∏ w : InfinitePlace F, min 1 (Real.exp (-fullArchLog F a w)) := by
  simpa only [Nat.cast_zero, zero_mul, Real.exp_zero, one_mul] using
    archSchwartz_fullArchLog_weighted_bound F 0 f

/-- The product of the logarithmic factors restricts to the kernel after
one coordinate is eliminated by the prescribed modulus. -/
theorem archLogFibre_product_le_kernel (x : InfiniteIdeles F) (g : archNormOne F) :
    (∏ w : InfinitePlace F, min 1 (Real.exp (-fullArchLog F (g.val⁻¹ * x) w))) ≤
      archimedeanLogFibreKernel (max 0 (-Real.log ‖x.val‖))
        (fun w : {w : InfinitePlace F // w ≠ w₀} =>
          fullArchLog F x w - (archRegulatorLog F g).toAdd w) := by
  let l := fullArchLog F (g.val⁻¹ * x)
  let u (w : {w : InfinitePlace F // w ≠ w₀}) := fullArchLog F x w - (archRegulatorLog F g).toAdd w
  have hzero : fullArchLog F (1 : InfiniteIdeles F) = 0 := by
    funext w
    change (w.mult : ℝ) * Real.log ‖(1 : w.Completion)‖ = 0
    simp
  have hinv : fullArchLog F g.val⁻¹ + fullArchLog F g.val = 0 := by
    rw [← fullArchLog_mul, inv_mul_cancel, hzero]
  have hl (w : InfinitePlace F) : l w = fullArchLog F x w - fullArchLog F g.val w := by
    have hi := congrFun hinv w
    change fullArchLog F g.val⁻¹ w + fullArchLog F g.val w = 0 at hi
    change fullArchLog F (g.val⁻¹ * x) w = _
    rw [fullArchLog_mul]
    change fullArchLog F g.val⁻¹ w + fullArchLog F x w = _
    linarith
  have hu (w : {w : InfinitePlace F // w ≠ w₀}) : l w = u w := hl w
  have hsum : ∑ w, l w = Real.log ‖x.val‖ := by
    rw [show (∑ w, l w) = ∑ w, (fullArchLog F x w - fullArchLog F g.val w) from
      Finset.sum_congr rfl (fun w _ => hl w), Finset.sum_sub_distrib,
      fullArchLog_sum, fullArchLog_sum, (archNormOne_iff F g.val).mp g.property, Real.log_one, sub_zero]
  rw [Fintype.sum_eq_add_sum_subtype_ne _ (w₀ : InfinitePlace F)] at hsum
  have hlast : -l w₀ = -Real.log ‖x.val‖ + ∑ w, u w := by
    simp only [hu] at hsum
    linarith
  change (∏ w, min 1 (Real.exp (-l w))) ≤ archimedeanLogFibreKernel (max 0 (-Real.log ‖x.val‖)) u
  rw [Fintype.prod_eq_mul_prod_subtype_ne _ (w₀ : InfinitePlace F), hlast]
  simp only [hu, archimedeanLogFibreKernel]
  refine mul_le_mul_of_nonneg_right (min_le_min_left _ (Real.exp_le_exp.mpr
    (by linarith only [le_max_right (0 : ℝ) (-Real.log ‖x.val‖)]))) ?_
  exact Finset.prod_nonneg fun _ _ => le_min zero_le_one (Real.exp_pos _).le


/-- Restriction to a translated norm-one fibre eliminates the distinguished
logarithmic coordinate in the pointwise Schwartz bound. -/
theorem archSchwartz_logFibre_weighted_bound (k : ℕ) (f : 𝓢(mixedEmbedding.mixedSpace F, ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : InfiniteIdeles F) (g : archNormOne F),
      Real.exp ((k : ℝ) * max 0 (Real.log ‖x.val‖)) *
        ‖f (InfiniteAdeleRing.ringEquiv_mixedSpace F (g.val⁻¹ * x).val)‖ ≤
        C * archimedeanLogFibreKernel (max 0 (-Real.log ‖x.val‖))
          (fun w : {w : InfinitePlace F // w ≠ w₀} =>
            fullArchLog F x w - (archRegulatorLog F g).toAdd w) := by
  obtain ⟨C, hC, hSchwartz⟩ := archSchwartz_fullArchLog_weighted_bound F k f
  refine ⟨C, hC, fun x g => ?_⟩
  have hlog (z : InfiniteIdeles F) : fullArchLog F z⁻¹ + fullArchLog F z = 0 := by
    rw [← fullArchLog_mul, inv_mul_cancel]
    funext w
    change (w.mult : ℝ) * Real.log ‖(1 : w.Completion)‖ = 0
    simp
  have hnorm : Real.log ‖(g.val⁻¹ * x).val‖ = Real.log ‖x.val‖ := by
    rw [← fullArchLog_sum, fullArchLog_mul]
    have h : fullArchLog F g.val⁻¹ + fullArchLog F x = fullArchLog F x - fullArchLog F g.val := by
      rw [eq_neg_of_add_eq_zero_left (hlog g.val)]
      rw [sub_eq_add_neg, add_comm]
    rw [h, show (∑ w, (fullArchLog F x - fullArchLog F g.val) w) =
      ∑ w, (fullArchLog F x w - fullArchLog F g.val w) from rfl,
      Finset.sum_sub_distrib, fullArchLog_sum, fullArchLog_sum,
      (archNormOne_iff F g.val).mp g.property, Real.log_one, sub_zero]
  have hweight := hSchwartz (g.val⁻¹ * x)
  rw [hnorm] at hweight
  exact hweight.trans (mul_le_mul_of_nonneg_left (archLogFibre_product_le_kernel F x g) hC)

/-- The unweighted Schwartz estimate on a translated norm-one fibre. -/
theorem archSchwartz_logFibre_bound (f : 𝓢(mixedEmbedding.mixedSpace F, ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : InfiniteIdeles F) (g : archNormOne F),
      ‖f (InfiniteAdeleRing.ringEquiv_mixedSpace F (g.val⁻¹ * x).val)‖ ≤
        C * archimedeanLogFibreKernel (max 0 (-Real.log ‖x.val‖))
          (fun w : {w : InfinitePlace F // w ≠ w₀} =>
            fullArchLog F x w - (archRegulatorLog F g).toAdd w) := by
  simpa only [Nat.cast_zero, zero_mul, Real.exp_zero, one_mul] using
    archSchwartz_logFibre_weighted_bound F 0 f


end
end Masullo
