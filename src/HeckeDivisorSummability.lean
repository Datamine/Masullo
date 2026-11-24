import HeckeCompletedContour
import HeckeExplicitPrimeTerms
import Mathlib.Analysis.PSeries

open Complex Filter Function IsDedekindDomain MeasureTheory Metric NumberField Set
open scoped Classical NumberField Topology

namespace Masullo

noncomputable section

private theorem stripBin_mem_disk {z : ℂ} {n : ℤ}
    (hz : z.re ∈ Icc (0 : ℝ) 1) (hn : ⌊z.im⌋ = n) :
    z ∈ closedBall (⟨2,(n : ℝ)⟩ : ℂ) 4 := by
  have h := Int.floor_eq_iff.mp hn
  rw [mem_closedBall_iff_norm]
  let w := z - (⟨2,(n : ℝ)⟩ : ℂ)
  have hNorm : ‖w‖ ≤ |w.re| + |w.im| := by
    simpa only [Complex.re_add_im, norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs] using
      norm_add_le (w.re : ℂ) ((w.im : ℂ) * I)
  apply hNorm.trans
  have hr : |w.re| ≤ 2 := by
    change |z.re-2| ≤ 2
    exact abs_le.mpr ⟨by linarith [hz.1], by linarith [hz.2]⟩
  have hi : |w.im| ≤ 1 := by
    change |z.im-(n : ℝ)| ≤ 1
    exact abs_le.mpr ⟨by linarith [h.1], by linarith [h.2]⟩
  linarith

private theorem abs_ordinate_ge_half_of_floor {z : ℂ} {n : ℤ}
    (hn : ⌊z.im⌋ = n) (h : 2 ≤ |(n : ℝ)|) : |(n : ℝ)| / 2 ≤ |z.im| := by
  obtain ⟨hl, hu⟩ := Int.floor_eq_iff.mp hn
  have hab : |(n : ℝ) - z.im| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hdiff := (abs_abs_sub_abs_le_abs_sub (n : ℝ) z.im).trans hab
  linarith [(abs_le.mp hdiff).2]

variable (F : Type*) [Field F] [NumberField F]
private abbrev K := normOneIdeleClass F
private abbrev Place := HeightOneSpectrum (𝓞 F)

local instance divisorSumNormOneMeasurable : MeasurableSpace (K F) := borel _
local instance divisorSumNormOneBorel : BorelSpace (K F) := ⟨rfl⟩
local instance divisorSumIdeleMeasurable : MeasurableSpace (Idele F) := borel _
local instance divisorSumIdeleBorel : BorelSpace (Idele F) := ⟨rfl⟩

variable (χ : PontryaginDual (IdeleClass F)) (S : Finset (Place F))
  (hs : Surjective (sIdeleClassInclusion F S))
  (hu : globalNormOneCharacter F (heckeNormOneRestriction F χ) ∈
    (sUnramified F S : Set (QuasiCharacter (IdeleClass F))))
variable (ν : Measure (K F)) [ν.IsHaarMeasure]
variable (η : Measure (Idele F)) [η.IsHaarMeasure]
variable [∀ v : Place F, MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : Place F, BorelSpace (v.adicCompletion F)ˣ]
  (μ : ∀ v : Place F, Measure (v.adicCompletion F)ˣ)
  [∀ v : Place F, (μ v).IsHaarMeasure] [∀ v : Place F, SigmaFinite (μ v)]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]
variable (hν : IsWeilQuotientMeasure (principalIdeles F) η Measure.count (globalClassMeasure F ν))

set_option maxHeartbeats 650000 in
include μ hν in
/-- The actual completed Hecke divisor is absolutely summable against every
centered exponential-decay Mellin test. -/
theorem manuscriptCompletedHecke_divisor_summable
    {t : ℝ} (ht : HasHeckeHeight F χ t) (L : ℂ → ℂ) (hL : MeromorphicOn L univ)
    (he : EqOn L (manuscriptCompletedHeckeEuler F χ S hs hu t) {z | 1 < z.re})
    (g : PositiveRealExponentialDecay (univ : Set ℝ)) :
    Summable (fun z : ℂ => ‖(MeromorphicOn.divisor L univ z : ℂ) *
      mellin (g.val ∘ Real.log) (z - 1 / 2)‖) := by
  classical
  obtain ⟨W, _, _, _, _, _, hW, hWe, hOrder, _⟩ :=
    exists_manuscriptCompletedHecke_contour_edges F χ S hs hu ν η μ hν ht
  let d := MeromorphicOn.divisor L univ
  have hStrip (z : ℂ) (hz : d z ≠ 0) : z.re ∈ Icc (0 : ℝ) 1 := by
    have hz' : ¬ (z.re < 0 ∨ 1 < z.re) := by
      intro ho
      apply hz
      rw [hL.divisor_apply (mem_univ z), meromorphicOrderAt_congr
        (globalHeckeContinuation_unique_germ hL hW.meromorphicOn he hWe z), hOrder z ho]
      simp
    exact ⟨not_lt.mp (fun h => hz' (Or.inl h)), not_lt.mp (fun h => hz' (Or.inr h))⟩
  let D : Set ℂ := Function.support d
  let P (n : ℤ) : Set D := {p | ⌊p.val.im⌋ = n}
  have hUnique (p : D) : ∃! n, p ∈ P n := ⟨⌊p.val.im⌋, rfl, fun n h => h.symm⟩
  have hFinite (n : ℤ) : (P n).Finite := by
    let B := Icc (0 : ℝ) 1 ×ℂ Icc (n : ℝ) ((n : ℝ) + 1)
    have hc : IsCompact B := isCompact_Icc.reProdIm isCompact_Icc
    have hf : (MeromorphicOn.divisor L B).support.Finite :=
      (MeromorphicOn.divisor L B).finiteSupport hc
    apply Set.Finite.of_finite_image _ (f := (Subtype.val : D → ℂ)) Subtype.val_injective.injOn
    refine hf.subset ?_
    rintro z ⟨p, hp, rfl⟩
    have hp' := Int.floor_eq_iff.mp (show ⌊p.val.im⌋ = n from hp)
    have hpB : p.val ∈ B := Complex.mem_reProdIm.mpr
      ⟨hStrip p.val p.property, ⟨hp'.1, hp'.2.le⟩⟩
    rw [Function.mem_support, MeromorphicOn.divisor_apply
      (fun w _ => hL w (mem_univ w)) hpB, ← hL.divisor_apply (mem_univ p.val)]
    exact p.property
  letI (n : ℤ) : Fintype (P n) := (hFinite n).fintype
  let Φ (z : ℂ) := mellin (g.val ∘ Real.log) (z - 1 / 2)
  let J (z : ℂ) := ‖(d z : ℂ) * Φ z‖
  have hInd : D.indicator J = J := by
    funext z
    by_cases hz : z ∈ D
    · rw [Set.indicator_of_mem hz]
    · have hzero : d z = 0 := not_ne_iff.mp hz
      simp [Set.indicator_of_notMem hz, J, hzero]
  have hSub : Summable (fun z : D => J z.val) := by
    apply (summable_partition (f := fun z : D => J z.val) (fun _ => norm_nonneg _) hUnique).mpr
    refine ⟨fun n => (hasSum_fintype (fun z : P n => J z.val.val)).summable, ?_⟩
    obtain ⟨f, N, T, _, hT, hDisk⟩ :=
      manuscriptCompletedHecke_high_divisor_disk F χ S hs hu ν η μ hν t L hL he
    obtain ⟨hSch, _⟩ := exponentialLogProfile_mellinHypotheses g
    obtain ⟨A, hA, hDecay, _⟩ := (mellin_exponential_decay hSch).2.2.1
      (-1/2) (1/2) (by norm_num) 3
    let C := (8 * A * (N : ℝ)) / Real.log 2
    have hC : 0 ≤ C := by
      dsimp [C]
      exact div_nonneg (by positivity) (Real.log_nonneg (by norm_num))
    have hBound (n : ℤ) (hn : T ≤ |(n : ℝ)|) :
        (∑' z : P n, J z.val.val) ≤ C / (n : ℝ) ^ 2 := by
      let c : ℂ := ⟨2,(n : ℝ)⟩
      obtain ⟨hFin, hCount, hEq⟩ := hDisk (n : ℝ) hn
      let E := hFin.toFinset
      let m (z : ℂ) : ℝ := (analyticOrderNatAt f z : ℝ)
      have hE (z : ℂ) : z ∈ E ↔ z ∈ closedBall c 4 ∧ analyticOrderNatAt f z ≠ 0 :=
        Set.Finite.mem_toFinset _
      have hSum : (∑ z ∈ E, m z) ≤ ((N : ℝ) / Real.log 2) * |(n : ℝ)| := by
        have heq : (∑ᶠ z ∈ closedBall c 4, m z) = ∑ z ∈ E, m z := by
          rw [← finsum_mem_coe_finset]
          apply finsum_mem_inter_support_eq'
          intro z hz
          have hpos : analyticOrderNatAt f z ≠ 0 := fun h => hz (by simp [m, h])
          exact ⟨fun h => (hE z).mpr ⟨h,hpos⟩, fun h => ((hE z).mp h).1⟩
        rw [heq] at hCount
        have hlog : Real.log |(n : ℝ)| ≤ |(n : ℝ)| :=
          (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
        calc
          _ ≤ (N : ℝ) * Real.log |(n : ℝ)| / Real.log 2 := hCount
          _ = ((N : ℝ) / Real.log 2) * Real.log |(n : ℝ)| := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left hlog (div_nonneg (by positivity) (Real.log_nonneg (by norm_num)))
      let e : P n ↪ ℂ := ⟨fun z => z.val.val,
        fun _ _ h => Subtype.ext (Subtype.ext h)⟩
      have hp (z : P n) : z.val.val ∈ closedBall c 4 ∧ z.val.val.re ∈ Icc (0 : ℝ) 1 :=
        ⟨stripBin_mem_disk (hStrip z.val.val z.val.property) z.property,
          hStrip z.val.val z.val.property⟩
      have heq (z : P n) : d z.val.val = (analyticOrderNatAt f z.val.val : ℤ) :=
        hEq _ (hp z).1 (hp z).2
      have hIn : Finset.univ.map e ⊆ E := by
        intro z hz
        obtain ⟨p, _, rfl⟩ := Finset.mem_map.mp hz
        apply (hE _).mpr
        refine ⟨(hp p).1, fun h => p.val.property ?_⟩
        change analyticOrderNatAt f p.val.val = 0 at h
        rw [heq p, h]
        simp
      have hWeight (z : P n) : J z.val.val ≤ (8 * A / |(n : ℝ)| ^ 3) * m z.val.val := by
        have hNat : 0 < |(n : ℝ)| := by linarith
        have hLower := abs_ordinate_ge_half_of_floor (z := z.val.val) z.property (hT.trans hn)
        have hPow : (|(n : ℝ)| / 2) ^ 3 ≤ |z.val.val.im| ^ 3 :=
          pow_le_pow_left₀ (by positivity) hLower _
        have hΦ : ‖Φ z.val.val‖ ≤ 8*A / |(n : ℝ)| ^ 3 := by
          have hD := hDecay (z.val.val - (1/2 : ℂ))
            (by rw [Complex.sub_re]; norm_num; linarith [(hp z).2.1]) (by
              rw [Complex.sub_re]; norm_num; linarith [(hp z).2.2])
          have hid : (z.val.val - (1/2 : ℂ)).im = z.val.val.im := by simp [Complex.sub_im]
          rw [hid] at hD
          apply (le_div_iff₀ (by positivity)).mpr
          have h := (mul_le_mul_of_nonneg_right hPow (norm_nonneg (Φ z.val.val))).trans hD
          ring_nf at h ⊢
          linarith
        unfold J
        rw [norm_mul, heq z, Int.cast_natCast, Complex.norm_natCast, mul_comm]
        exact mul_le_mul_of_nonneg_right hΦ (Nat.cast_nonneg _)
      have hSum' : (∑ z : P n, m z.val.val) ≤ ((N : ℝ) / Real.log 2) * |(n : ℝ)| := by
        change (∑ z : P n, m (e z)) ≤ _
        rw [← Finset.sum_map (f := m) (e := e)]
        exact (Finset.sum_le_sum_of_subset_of_nonneg hIn (fun z _ _ => Nat.cast_nonneg _)).trans hSum
      rw [tsum_fintype]
      calc
        _ ≤ ∑ z : P n, (8 * A / |(n : ℝ)| ^ 3) * m z.val.val :=
          Finset.sum_le_sum fun z _ => hWeight z
        _ = (8 * A / |(n : ℝ)| ^ 3) * ∑ z : P n, m z.val.val := by rw [Finset.mul_sum]
        _ ≤ (8 * A / |(n : ℝ)| ^ 3) * (((N : ℝ) / Real.log 2) * |(n : ℝ)|) :=
          mul_le_mul_of_nonneg_left hSum' (by positivity)
        _ = _ := by
          have hn₀ : |(n : ℝ)| ≠ 0 := ne_of_gt (by linarith)
          rw [← sq_abs (n : ℝ)]
          dsimp [C]
          field_simp
    let Q (n : ℤ) := ∑' z : P n, J z.val.val
    have hbNorm (n : ℤ) (hn : T ≤ |(n : ℝ)|) : ‖Q n‖ ≤ C / (n : ℝ) ^ 2 :=
      (Real.norm_of_nonneg (tsum_nonneg fun _ => norm_nonneg _)).trans_le (hBound n hn)
    have hSummable : Summable (fun n : ℕ => C / (n : ℝ) ^ 2) := by
      simpa only [div_eq_mul_inv] using ((Real.summable_nat_pow_inv.mpr (by decide : 1 < 2)).mul_left C)
    obtain ⟨k, hk⟩ := exists_nat_ge T
    apply Summable.of_nat_of_neg
    · apply hSummable.of_norm_bounded_eventually
      rw [Nat.cofinite_eq_atTop]
      filter_upwards [eventually_ge_atTop k] with n hn
      exact hbNorm (n : ℤ) (by
        rw [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg _)]
        exact hk.trans (Nat.cast_le.mpr hn))
    · apply hSummable.of_norm_bounded_eventually
      rw [Nat.cofinite_eq_atTop]
      filter_upwards [eventually_ge_atTop k] with n hn
      simpa only [Int.cast_neg, Int.cast_natCast, neg_pow, Even.neg_pow (by decide : Even 2)] using
        hbNorm (-(n : ℤ)) (by
          rw [Int.cast_neg, abs_neg, Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg _)]
          exact hk.trans (Nat.cast_le.mpr hn))
  obtain ⟨a, ha⟩ := hSub
  have hIndSum : HasSum (D.indicator J) a := hasSum_subtype_iff_indicator.mp ha
  rw [hInd] at hIndSum
  exact hIndSum.summable

include μ hν in
/-- The centered contour comparison with absolute divisor convergence,
written on the right line for both characters. -/
theorem exists_manuscriptCompletedHecke_reflected_divisor_contour
    {t : ℝ} (ht : HasHeckeHeight F χ t)
    (g : PositiveRealExponentialDecay (univ : Set ℝ)) :
    ∃ (L : ℂ → ℂ) (U : Finset (Place F)) (hU : Surjective (sIdeleClassInclusion F U))
      (hUχ : globalNormOneCharacter F (heckeNormOneRestriction F χ⁻¹) ∈
        (sUnramified F U : Set (QuasiCharacter (IdeleClass F))))
      (V : ℂ → ℂ), MeromorphicNFOn L univ ∧ MeromorphicNFOn V univ ∧
      EqOn L (manuscriptCompletedHeckeEuler F χ S hs hu t) {z | 1 < z.re} ∧
      EqOn V (manuscriptCompletedHeckeEuler F χ⁻¹ U hU hUχ (-t)) {z | 1 < z.re} ∧
      let Φ := fun z => mellin (g.val ∘ Real.log) (z - 1 / 2)
      let R := fun y : ℝ => Φ ⟨2,y⟩ * logDeriv L ⟨2,y⟩
      let R' := fun y : ℝ => Φ (1 - ⟨2,y⟩) * logDeriv V ⟨2,y⟩
      Summable (fun z => ‖(MeromorphicOn.divisor L univ z : ℂ) * Φ z‖) ∧
      Integrable R ∧ Integrable R' ∧
      HasSum (fun z => (MeromorphicOn.divisor L univ z : ℂ) * Φ z)
        (((∫ y : ℝ, R y + R' y) / (2 * (Real.pi : ℂ))) +
          (Real.log (heckeDiscriminantConductor F χ) : ℂ) * g.val 0) := by
  obtain ⟨L, hL, hLe, hLeft, hRight, hCond, U, hU, hUχ, V, hV, hVe, hRef⟩ :=
    exists_manuscriptCompletedHecke_centered_residue_contour F χ S hs hu ν η μ hν ht g
  let Φ (z : ℂ) := mellin (g.val ∘ Real.log) (z - 1 / 2)
  let k := (Real.log (heckeDiscriminantConductor F χ) : ℂ)
  let P (y : ℝ) := Φ ⟨-1,y⟩ * logDeriv L ⟨-1,y⟩
  let R (y : ℝ) := Φ ⟨2,y⟩ * logDeriv L ⟨2,y⟩
  let R' (y : ℝ) := Φ (1 - ⟨2,y⟩) * logDeriv V ⟨2,y⟩
  let K₀ (y : ℝ) := k * Φ (1 - ⟨2,y⟩)
  have hAbs := manuscriptCompletedHecke_divisor_summable F χ S hs hu ν η μ hν ht L hL.meromorphicOn hLe g
  have hSum := hCond hAbs.of_norm
  obtain ⟨hKInt, hKValue⟩ := centeredMellin_reflected_constant_contour g 2 k
  have hKArg : (fun y : ℝ => k * mellin (g.val ∘ Real.log) (1 / 2 - (⟨2,y⟩ : ℂ))) = K₀ := by
    funext y
    change k * mellin _ (1 / 2 - (⟨2,y⟩ : ℂ)) =
      k * mellin _ (1 - (⟨2,y⟩ : ℂ) - 1 / 2)
    congr 2
    ring
  have hOrd (y : ℝ) : ((2 : ℂ) + (y : ℂ) * I) = ⟨2,y⟩ := by
    apply Complex.ext <;> simp [Complex.add_re, Complex.mul_re, Complex.add_im, Complex.mul_im]
  have hKi : Integrable K₀ := by
    change Integrable (fun y : ℝ => k * mellin _ (1 / 2 - ((2 : ℂ) + (y : ℂ) * I))) at hKInt
    simpa only [hOrd, hKArg] using hKInt
  have hKv : (∫ y, K₀ y) / (2 * (Real.pi : ℂ)) = k * g.val 0 := by
    change (∫ y : ℝ, k * mellin _ (1 / 2 - ((2 : ℂ) + (y : ℂ) * I))) / _ = _ at hKValue
    simpa only [hOrd, hKArg] using hKValue
  have hArg (y : ℝ) : (⟨-1,-y⟩ : ℂ) = 1 - (⟨2,y⟩ : ℂ) := by
    apply Complex.ext <;> norm_num [Complex.sub_re, Complex.sub_im]
  have hLeg (y : ℝ) : P (-y) = -(R' y + K₀ y) := by
    have hlog := hRef (-y)
    rw [neg_neg] at hlog
    dsimp only [P, R', K₀]
    rw [hlog, hArg]
    ring
  have hPi : Integrable P := hLeft
  have hRi : Integrable R := hRight
  have hPi' : Integrable (fun y => P (-y)) :=
    (Measure.measurePreserving_neg (volume : Measure ℝ)).integrable_comp_of_integrable hPi
  have hR'i : Integrable R' := by
    apply (hPi'.neg.sub hKi).congr
    refine .of_forall fun y => ?_
    change -P (-y) - K₀ y = R' y
    rw [hLeg, neg_neg, add_sub_cancel_right]
  have hLeftEq : (∫ y, P y) = -((∫ y, R' y) + ∫ y, K₀ y) := by
    rw [← integral_neg_eq_self P, ← integral_add hR'i hKi, ← integral_neg]
    exact integral_congr_ae (.of_forall hLeg)
  refine ⟨L, U, hU, hUχ, V, hL, hV, hLe, hVe, hAbs, hRi, hR'i, ?_⟩
  have hEq :
      ((∫ y, R y) - (∫ y, P y)) / (2 * (Real.pi : ℂ)) =
        ((∫ y, R y + R' y) / (2 * (Real.pi : ℂ))) + k * g.val 0 := by
    rw [hLeftEq, sub_neg_eq_add, ← add_assoc, add_div, hKv, integral_add hRi hR'i]
  exact hEq ▸ hSum

end

end Masullo
