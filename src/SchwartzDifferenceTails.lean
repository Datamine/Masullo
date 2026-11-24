import ExponentialDecayStructure
import SchwartzComplete
import Mathlib.Analysis.PSeries

open Filter Function Set Topology
open scoped ContDiff NNReal SchwartzMap

noncomputable section

namespace Masullo

private theorem le_tsum_of_orbit {A B : ℕ → ℝ} (hA : Tendsto A atTop (𝓝 0))
    (hB : ∀ n, 0 ≤ B n) (hS : Summable B) (hrec : ∀ n, A n ≤ B n + A (n + 1)) :
    A 0 ≤ ∑' n, B n := by
  have hfin (n : ℕ) : A 0 ≤ (∑ j ∈ Finset.range n, B j) + A n := by
    induction n with
    | zero => simp
    | succ n ih =>
      refine ih.trans ?_
      rw [Finset.sum_range_succ, add_assoc]
      exact add_le_add_right (hrec n) _
  simpa only [add_zero] using le_of_tendsto_of_tendsto tendsto_const_nhds
    (tendsto_const_nhds.add hA) (Eventually.of_forall fun n ↦
      (hfin n).trans (add_le_add_left (hS.sum_le_tsum _ (fun j _ ↦ hB j)) _))

/-- Forward telescoping with an exponentially decaying inhomogeneous term.
The polynomial factor is held fixed at the start of the orbit. -/
theorem norm_le_of_difference_tail {u v : ℝ → ℂ} {b d C : ℝ}
    (hb : 0 < b) (hd : 0 < d) (hC : 0 ≤ C) (k : ℕ)
    (hrec : ∀ x, ‖u x‖ ≤ ‖v x‖ + ‖u (x + d)‖)
    (hbound : ∀ x, 0 ≤ x → |x| ^ k * ‖v x‖ ≤ C * Real.exp (-b * x))
    (hzero : Tendsto u atTop (𝓝 0)) :
    ∀ x, 0 ≤ x → |x| ^ k * ‖u x‖ ≤ (C / (1 - Real.exp (-b * d))) * Real.exp (-b * x) := by
  intro x hx
  let r := Real.exp (-b * d)
  have hr : 0 ≤ r := Real.exp_nonneg _
  have hr' : r < 1 := Real.exp_lt_one_iff.mpr (by rw [neg_mul]; exact neg_lt_zero.mpr (mul_pos hb hd))
  let A := C * Real.exp (-b * x)
  have hA : 0 ≤ A := mul_nonneg hC (Real.exp_nonneg _)
  let w := |x| ^ k
  have hw : 0 ≤ w := by dsimp [w]; positivity
  have hv (n : ℕ) : w * ‖v (x + d * n)‖ ≤ A * r ^ n := by
    have hy : 0 ≤ x + d * n := by positivity
    have hxy : x ≤ x + d * n := le_add_of_nonneg_right (by positivity)
    have hpow : w ≤ |x + d * n| ^ k := by
      dsimp [w]
      rw [abs_of_nonneg hx, abs_of_nonneg hy]
      gcongr
    refine (mul_le_mul_of_nonneg_right hpow (norm_nonneg _)).trans ((hbound _ hy).trans_eq ?_)
    dsimp [A, r]
    rw [← Real.exp_nat_mul, mul_assoc, ← Real.exp_add]
    congr 2
    ring
  have ht : Tendsto (fun n : ℕ ↦ x + d * n) atTop atTop :=
    tendsto_atTop_add_const_left _ _ ((tendsto_const_mul_atTop_of_pos hd).mpr tendsto_natCast_atTop_atTop)
  have ht₀ : Tendsto (fun n : ℕ ↦ w * ‖u (x + d * n)‖) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, norm_zero, mul_zero] using tendsto_const_nhds.mul ((hzero.comp ht).norm)
  have hle := le_tsum_of_orbit ht₀ (fun n ↦ mul_nonneg hA (pow_nonneg hr n))
    ((summable_geometric_of_lt_one hr hr').mul_left A) (fun n ↦ by
      have he : x + d * (n + 1 : ℕ) = (x + d * n) + d := by push_cast; ring
      rw [he]
      have hstep := mul_le_mul_of_nonneg_left (hrec (x + d * n)) hw
      rw [mul_add] at hstep
      exact hstep.trans (add_le_add_left (hv n) _))
  rw [tsum_mul_left, tsum_geometric_of_lt_one hr hr'] at hle
  simpa only [Nat.cast_zero, mul_zero, add_zero, A, r, w, div_eq_mul_inv, mul_right_comm] using hle

/-- A cyclic difference between real Schwartz functions commutes with
ordinary logarithmic derivatives. -/
theorem iteratedDeriv_cyclicDifference (d : ℝ) (c : ℂ) (u : 𝓢(ℝ, ℂ)) (n : ℕ) (x : ℝ) :
    iteratedDeriv n (fun y : ℝ ↦ u y - c * u (y + d)) x =
      iteratedDeriv n u x - c * iteratedDeriv n u (x + d) := by
  have h₁ := (u.smooth n).contDiffAt (x := x)
  have h₂ : ContDiff ℝ n (fun y : ℝ ↦ u (y + d)) := (u.smooth n).comp (by fun_prop)
  change iteratedDeriv n (⇑u - fun y : ℝ ↦ c * u (y + d)) x = _
  rw [iteratedDeriv_sub h₁ (contDiffAt_const.mul h₂.contDiffAt),
    iteratedDeriv_const_mul_field, iteratedDeriv_comp_add_const]

private theorem iteratedDeriv_schwartz_tendsto_cocompact (u : 𝓢(ℝ, ℂ)) (n : ℕ) :
    Tendsto (iteratedDeriv n u) (cocompact ℝ) (𝓝 0) := by
  have h (n : ℕ) : ⇑((SchwartzMap.derivCLM ℂ ℂ ^ n) u) = iteratedDeriv n u := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ', iteratedDeriv_succ]
      change deriv (⇑((SchwartzMap.derivCLM ℂ ℂ ^ n) u)) = _
      rw [ih]
  rw [← h]
  exact ((SchwartzMap.derivCLM ℂ ℂ ^ n) u).tendsto_cocompact

/-- If the cyclic difference of a Schwartz profile satisfies a fixed
exponential Schwartz weight, then the profile satisfies that same weight. -/
theorem logExponentialWeight_of_schwartz_cyclicDifference {d : ℝ} (hd : 0 < d)
    (c : Circle) (u : 𝓢(ℝ, ℂ)) (a : ℝ)
    (hv : logExponentialWeight a (fun x : ℝ ↦ u x - (c : ℂ) * u (x + d)) ∈
      realSchwartzCoe.range) :
    logExponentialWeight a u ∈ realSchwartzCoe.range := by
  let v (x : ℝ) := u x - (c : ℂ) * u (x + d)
  have hvSmooth : ContDiff ℝ ∞ v :=
    (u.smooth ⊤).sub (contDiff_const.mul ((u.smooth ⊤).comp (by fun_prop)))
  have hvBounds := (logExponentialWeight_mem_range_iff a hvSmooth).mp hv
  have hdecay (k n : ℕ) (C : ℝ) (hC : 0 ≤ C)
      (hbound : ∀ x, |x| ^ k * ‖iteratedDeriv n v x‖ ≤ C * Real.exp (-(a * x))) :
      ∃ B : ℝ, 0 ≤ B ∧ ∀ x, 0 ≤ a * x →
        |x| ^ k * ‖iteratedDeriv n u x‖ ≤ B * Real.exp (-(a * x)) := by
    rcases lt_trichotomy 0 a with ha | rfl | ha
    · have hrec (x : ℝ) : ‖iteratedDeriv n u x‖ ≤
          ‖iteratedDeriv n v x‖ + ‖iteratedDeriv n u (x + d)‖ := by
        have he := iteratedDeriv_cyclicDifference d (c : ℂ) u n x
        have hsum := norm_add_le (iteratedDeriv n v x) ((c : ℂ) * iteratedDeriv n u (x + d))
        rw [norm_mul, Circle.norm_coe, one_mul] at hsum
        rw [show iteratedDeriv n v x = _ from he, sub_add_cancel] at hsum
        rw [show iteratedDeriv n v x = _ from he]
        exact hsum
      have hlim := (iteratedDeriv_schwartz_tendsto_cocompact u n).mono_left atTop_le_cocompact
      have hden : 0 ≤ 1 - Real.exp (-a * d) := sub_nonneg.mpr (Real.exp_le_one_iff.mpr
        (by rw [neg_mul]; exact neg_nonpos.mpr (mul_nonneg ha.le hd.le)))
      refine ⟨_, div_nonneg hC hden, fun x hx ↦ ?_⟩
      rw [← neg_mul]
      refine norm_le_of_difference_tail ha hd hC k hrec (fun y _ ↦ ?_) hlim
        x (nonneg_of_mul_nonneg_right hx ha)
      simpa only [neg_mul] using hbound y
    · refine ⟨SchwartzMap.seminorm ℂ k n u, apply_nonneg _ _, fun x _ ↦ ?_⟩
      simpa using u.le_seminorm' ℂ k n x
    · let U (x : ℝ) := iteratedDeriv n u (-x)
      let V (x : ℝ) := iteratedDeriv n v (-(x + d))
      have hrec (x : ℝ) : ‖U x‖ ≤ ‖V x‖ + ‖U (x + d)‖ := by
        have he : V x = U (x + d) - (c : ℂ) * U x := by
          dsimp only [V, U, v]
          rw [iteratedDeriv_cyclicDifference, show -(x + d) + d = -x by ring]
        have hs := norm_sub_le (U (x + d)) (V x)
        rwa [he, sub_sub_cancel, norm_mul, Circle.norm_coe, one_mul, ← he, add_comm] at hs
      have hV (x : ℝ) (hx : 0 ≤ x) : |x| ^ k * ‖V x‖ ≤ C * Real.exp (-(-a) * x) := by
        have hy : 0 ≤ x + d := by positivity
        have hp : |x| ^ k ≤ |-(x + d)| ^ k := by
          rw [abs_neg, abs_of_nonneg hx, abs_of_nonneg hy]
          gcongr
          exact le_add_of_nonneg_right hd.le
        refine (mul_le_mul_of_nonneg_right hp (norm_nonneg _)).trans
          ((hbound (-(x + d))).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC))
        have had := mul_nonpos_of_nonpos_of_nonneg ha.le hd.le
        linarith only [had]
      have hlim : Tendsto U atTop (𝓝 0) :=
        ((iteratedDeriv_schwartz_tendsto_cocompact u n).mono_left
          atBot_le_cocompact).comp tendsto_neg_atTop_atBot
      have hden : 0 ≤ 1 - Real.exp (-(-a) * d) := sub_nonneg.mpr (Real.exp_le_one_iff.mpr
        (by rw [neg_neg]; exact mul_nonpos_of_nonpos_of_nonneg ha.le hd.le))
      refine ⟨_, div_nonneg hC hden, fun x hx ↦ ?_⟩
      have hx' : 0 ≤ -x := neg_nonneg.mpr (nonpos_of_mul_nonneg_right hx ha)
      simpa only [U, abs_neg, neg_neg, mul_neg] using
        norm_le_of_difference_tail (neg_pos.mpr ha) hd hC k hrec hV hlim (-x) hx'
  apply (logExponentialWeight_mem_range_iff a (u.smooth ⊤)).mpr
  intro k n
  obtain ⟨C, hC, hbound⟩ := hvBounds k n
  obtain ⟨B, hB, htail⟩ := hdecay k n C hC hbound
  let P := SchwartzMap.seminorm ℂ k n u
  have hP : 0 ≤ P := apply_nonneg _ _
  refine ⟨B + P, add_nonneg hB hP, fun x ↦ ?_⟩
  by_cases hx : 0 ≤ a * x
  · exact (htail x hx).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hP) (Real.exp_nonneg _))
  · refine (u.le_seminorm' ℂ k n x).trans
      ((le_add_of_nonneg_left hB).trans ?_)
    exact le_mul_of_one_le_right (add_nonneg hB hP)
      (Real.one_le_exp_iff.mpr (neg_nonneg.mpr (le_of_not_ge hx)))

/-- Exponential weights are inherited individually by an ordinary Schwartz
preimage of a cyclic difference. This applies to any interval of exponents. -/
theorem logExponentialDecay_of_schwartz_cyclicDifference {I : Set ℝ} {d : ℝ}
    (hd : 0 < d) (c : Circle) (u : 𝓢(ℝ, ℂ))
    (hv : (fun x : ℝ ↦ u x - (c : ℂ) * u (x + d)) ∈ logExponentialDecaySubmodule I) :
    (⇑u : ℝ → ℂ) ∈ logExponentialDecaySubmodule I := by
  apply (Submodule.mem_iInf _).mpr
  intro a
  exact logExponentialWeight_of_schwartz_cyclicDifference hd c u a
    ((Submodule.mem_iInf _).mp hv a)

/-- Ordinary Schwartz cyclic differences for a logarithmic displacement and a phase. -/
def schwartzCyclicDifference (g : ℝ × Circle) : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) :=
  ContinuousLinearMap.id ℂ _ - (g.2 : ℂ) • SchwartzMap.compSubConstCLM ℂ (-g.1)

theorem schwartzCyclicDifference_apply (g : ℝ × Circle) (u : 𝓢(ℝ, ℂ)) (x : ℝ) :
    schwartzCyclicDifference g u x = u x - (g.2 : ℂ) * u (x + g.1) := by
  change u x - (g.2 : ℂ) * u (x - -g.1) = _
  rw [sub_neg_eq_add]

local instance (I : Set ℝ) : ContinuousSMul ℂ (PositiveRealExponentialDecay I) :=
  (PolynormableSpace.withSeminorms ℂ (PositiveRealExponentialDecay I)).continuousSMul

/-- The same cyclic differences on the weighted Schwartz space. -/
def logDecayCyclicDifference (I : Set ℝ) (hI : I.Nonempty) (g : ℝ × Circle) :
    PositiveRealExponentialDecay I →L[ℂ] PositiveRealExponentialDecay I :=
  ContinuousLinearMap.id ℂ _ - (g.2 : ℂ) • logExponentialDecayTranslation I hI g.1

theorem logDecayCyclicDifference_apply (I : Set ℝ) (hI : I.Nonempty) (g : ℝ × Circle)
    (u : PositiveRealExponentialDecay I) (x : ℝ) :
    (logDecayCyclicDifference I hI g u).val x = u.val x - (g.2 : ℂ) * u.val (x + g.1) := rfl

/-- A finite product of ordinary Schwartz differences, including repetitions. -/
def schwartzCyclicDifferenceProduct (gs : List (ℝ × Circle)) :
    𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) :=
  gs.foldr (fun g A ↦ (schwartzCyclicDifference g).comp A) (ContinuousLinearMap.id ℂ _)

/-- The weighted counterpart to the ordinary Schwartz product. -/
def logDecayCyclicDifferenceProduct (I : Set ℝ) (hI : I.Nonempty) (gs : List (ℝ × Circle)) :
    PositiveRealExponentialDecay I →L[ℂ] PositiveRealExponentialDecay I :=
  gs.foldr (fun g A ↦ (logDecayCyclicDifference I hI g).comp A) (ContinuousLinearMap.id ℂ _)

private theorem schwartzCyclicDifferenceProduct_preserves_weights {I : Set ℝ}
    (gs : List (ℝ × Circle)) (hgs : ∀ g ∈ gs, 0 < g.1) (u : 𝓢(ℝ, ℂ))
    (hu : ⇑(schwartzCyclicDifferenceProduct gs u) ∈ logExponentialDecaySubmodule I) :
    ⇑u ∈ logExponentialDecaySubmodule I := by
  induction gs with
  | nil => exact hu
  | cons g gs ih =>
    apply ih (fun a ha ↦ hgs a (List.mem_cons_of_mem _ ha))
    apply logExponentialDecay_of_schwartz_cyclicDifference (hgs g List.mem_cons_self) g.2
      (schwartzCyclicDifferenceProduct gs u)
    have he :
        ⇑(schwartzCyclicDifferenceProduct (g :: gs) u) =
          fun x ↦ schwartzCyclicDifferenceProduct gs u x -
            (g.2 : ℂ) * schwartzCyclicDifferenceProduct gs u (x + g.1) :=
      funext (schwartzCyclicDifference_apply g _)
    rwa [← he]

theorem zeroInclusion_intertwines_cyclicDifferenceProduct (I : Set ℝ)
    (h0 : (0 : ℝ) ∈ I) (gs : List (ℝ × Circle)) (u : PositiveRealExponentialDecay I) :
    positiveRealExponentialDecay_zeroInclusion I h0
        (logDecayCyclicDifferenceProduct I ⟨0, h0⟩ gs u) =
      schwartzCyclicDifferenceProduct gs (positiveRealExponentialDecay_zeroInclusion I h0 u) := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    change positiveRealExponentialDecay_zeroInclusion I h0
        (logDecayCyclicDifference I ⟨0, h0⟩ g (logDecayCyclicDifferenceProduct I ⟨0, h0⟩ gs u)) =
      schwartzCyclicDifference g
        (schwartzCyclicDifferenceProduct gs (positiveRealExponentialDecay_zeroInclusion I h0 u))
    rw [← ih]
    apply SchwartzMap.ext
    intro x
    simp only [positiveRealExponentialDecay_zeroInclusion_apply, schwartzCyclicDifference_apply]
    exact logDecayCyclicDifference_apply I ⟨0, h0⟩ g _ x

/-- In scalar logarithmic coordinates, the ordinary range of a finite
product meets a weighted space in exactly the weighted range. -/
theorem logDecayCyclicDifferenceProduct_range_eq_comap (I : Set ℝ) (h0 : (0 : ℝ) ∈ I)
    (gs : List (ℝ × Circle)) (hgs : ∀ g ∈ gs, 0 < g.1) :
    (logDecayCyclicDifferenceProduct I ⟨0, h0⟩ gs).range =
      (schwartzCyclicDifferenceProduct gs).range.comap
        (positiveRealExponentialDecay_zeroInclusion I h0).toLinearMap := by
  ext f
  change (∃ u, logDecayCyclicDifferenceProduct I ⟨0, h0⟩ gs u = f) ↔
    (∃ u, schwartzCyclicDifferenceProduct gs u = positiveRealExponentialDecay_zeroInclusion I h0 f)
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨_, (zeroInclusion_intertwines_cyclicDifferenceProduct I h0 gs u).symm⟩
  · rintro ⟨u, hu⟩
    have hprofile : ⇑(positiveRealExponentialDecay_zeroInclusion I h0 f) = f.val :=
      funext (positiveRealExponentialDecay_zeroInclusion_apply I h0 f)
    have hU : ⇑u ∈ logExponentialDecaySubmodule I :=
      schwartzCyclicDifferenceProduct_preserves_weights gs hgs u (by
        rw [hu, hprofile]
        exact f.property)
    let U : PositiveRealExponentialDecay I := ⟨u, hU⟩
    have hU₀ : positiveRealExponentialDecay_zeroInclusion I h0 U = u :=
      SchwartzMap.ext (positiveRealExponentialDecay_zeroInclusion_apply I h0 U)
    refine ⟨U, positiveRealExponentialDecay_zeroInclusion_injective I h0 ?_⟩
    rw [zeroInclusion_intertwines_cyclicDifferenceProduct, hU₀, hu]

/-- The canonical weighted-to-ordinary scalar quotient comparison is continuous. -/
def logDecayCyclicDifferenceProduct_quotientComparison (I : Set ℝ) (h0 : (0 : ℝ) ∈ I)
    (gs : List (ℝ × Circle)) (hgs : ∀ g ∈ gs, 0 < g.1) :
    (PositiveRealExponentialDecay I ⧸ (logDecayCyclicDifferenceProduct I ⟨0, h0⟩ gs).range)
      →L[ℂ] (𝓢(ℝ, ℂ) ⧸ (schwartzCyclicDifferenceProduct gs).range) :=
  (logDecayCyclicDifferenceProduct I ⟨0, h0⟩ gs).range.liftQL
    ((schwartzCyclicDifferenceProduct gs).range.mkQL.comp
      (positiveRealExponentialDecay_zeroInclusion I h0)) (fun f hf ↦ by
        rw [logDecayCyclicDifferenceProduct_range_eq_comap I h0 gs hgs] at hf
        exact (Submodule.Quotient.mk_eq_zero _).mpr hf)

/-- The canonical weighted-to-ordinary scalar quotient comparison is injective. -/
theorem logDecayCyclicDifferenceProduct_quotientComparison_injective (I : Set ℝ)
    (h0 : (0 : ℝ) ∈ I) (gs : List (ℝ × Circle)) (hgs : ∀ g ∈ gs, 0 < g.1) :
    Injective (logDecayCyclicDifferenceProduct_quotientComparison I h0 gs hgs) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro q hq
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  rw [logDecayCyclicDifferenceProduct_range_eq_comap I h0 gs hgs]
  change positiveRealExponentialDecay_zeroInclusion I h0 f ∈ (schwartzCyclicDifferenceProduct gs).range
  exact (Submodule.Quotient.mk_eq_zero (schwartzCyclicDifferenceProduct gs).range).mp hq

private def polynomialOrbitWeight (d : ℝ) (n : ℕ) : ℝ :=
  (if n = 0 then 1 else 0) + d⁻¹ ^ 2 * (n : ℝ)⁻¹ ^ 2

private theorem polynomialOrbitWeight_summable (d : ℝ) : Summable (polynomialOrbitWeight d) := by
  have h₁ : Summable (fun n : ℕ ↦ if n = 0 then (1 : ℝ) else 0) :=
    summable_of_ne_finset_zero (s := {0}) (by simp)
  have h₂ : Summable (fun n : ℕ ↦ (n : ℝ)⁻¹ ^ 2) := by
    simpa only [inv_pow] using (Real.summable_nat_pow_inv (p := 2)).mpr (by decide)
  exact h₁.add (h₂.mul_left _)

private theorem polynomialOrbitWeight_nonneg (d : ℝ) (n : ℕ) :
    0 ≤ polynomialOrbitWeight d n := by
  unfold polynomialOrbitWeight
  split <;> positivity

private theorem norm_le_of_polynomial_tail {u v : ℝ → ℂ} {d C : ℝ} (hd : 0 < d)
    (hC : 0 ≤ C) (k : ℕ) (hrec : ∀ x, ‖u x‖ ≤ ‖v x‖ + ‖u (x + d)‖)
    (hbound : ∀ x, 0 ≤ x → |x| ^ k * ‖v x‖ ≤ C ∧ |x| ^ (k + 2) * ‖v x‖ ≤ C)
    (hzero : Tendsto u atTop (𝓝 0)) (x : ℝ) (hx : 0 ≤ x) :
    |x| ^ k * ‖u x‖ ≤ C * ∑' n, polynomialOrbitWeight d n := by
  let w := |x| ^ k
  have hw : 0 ≤ w := by dsimp [w]; positivity
  have hv (n : ℕ) : w * ‖v (x + d * n)‖ ≤ C * polynomialOrbitWeight d n := by
    by_cases hn : n = 0
    · subst n
      simpa [polynomialOrbitWeight, w] using (hbound x hx).1
    let y := x + d * n
    have hy : 0 ≤ y := by dsimp [y]; positivity
    have hxy : x ≤ y := le_add_of_nonneg_right (by positivity)
    have hdy : d * (n : ℝ) ≤ y := le_add_of_nonneg_left hx
    have hp : w * ‖v y‖ * (d * (n : ℝ)) ^ 2 ≤ C := by
      calc
        _ ≤ |y| ^ k * ‖v y‖ * |y| ^ 2 := by
          rw [abs_of_nonneg hy]
          dsimp [w]
          rw [abs_of_nonneg hx]
          gcongr
        _ = |y| ^ (k + 2) * ‖v y‖ := by rw [pow_add]; ring
        _ ≤ _ := (hbound y hy).2
    have hd' : 0 < (d * (n : ℝ)) ^ 2 := by
      have : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
      positivity
    simp only [polynomialOrbitWeight, hn, ↓reduceIte, zero_add]
    rw [← mul_pow, ← mul_inv, inv_pow, ← div_eq_mul_inv]
    exact (le_div_iff₀ hd').mpr hp
  have ht : Tendsto (fun n : ℕ ↦ x + d * n) atTop atTop :=
    tendsto_atTop_add_const_left _ _ ((tendsto_const_mul_atTop_of_pos hd).mpr tendsto_natCast_atTop_atTop)
  have ht₀ : Tendsto (fun n : ℕ ↦ w * ‖u (x + d * n)‖) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, norm_zero, mul_zero] using tendsto_const_nhds.mul ((hzero.comp ht).norm)
  have hle := le_tsum_of_orbit ht₀ (fun n ↦ mul_nonneg hC (polynomialOrbitWeight_nonneg d n))
    ((polynomialOrbitWeight_summable d).mul_left C) (fun n ↦ by
      have he : x + d * (n + 1 : ℕ) = (x + d * n) + d := by push_cast; ring
      rw [he]
      have hstep := mul_le_mul_of_nonneg_left (hrec (x + d * n)) hw
      rw [mul_add] at hstep
      exact hstep.trans (add_le_add_left (hv n) _))
  rwa [tsum_mul_left, Nat.cast_zero, mul_zero, add_zero] at hle

private theorem schwartzCyclicDifference_seminorm (g : ℝ × Circle) (hg : 0 < g.1)
    (k n : ℕ) (u : 𝓢(ℝ, ℂ)) :
    SchwartzMap.seminorm ℂ k n u ≤ (∑' j, polynomialOrbitWeight g.1 j) *
      (SchwartzMap.seminorm ℂ k n (schwartzCyclicDifference g u) +
        SchwartzMap.seminorm ℂ (k + 2) n (schwartzCyclicDifference g u)) := by
  let v := schwartzCyclicDifference g u
  let C := SchwartzMap.seminorm ℂ k n v + SchwartzMap.seminorm ℂ (k + 2) n v
  have hC : 0 ≤ C := add_nonneg (apply_nonneg _ _) (apply_nonneg _ _)
  have hv (x : ℝ) :
      iteratedDeriv n v x = iteratedDeriv n u x - (g.2 : ℂ) * iteratedDeriv n u (x + g.1) := by
    have he : ⇑v = fun x ↦ u x - (g.2 : ℂ) * u (x + g.1) :=
      funext (schwartzCyclicDifference_apply g u)
    rw [he, iteratedDeriv_cyclicDifference]
  have hs (x : ℝ) : |x| ^ k * ‖iteratedDeriv n v x‖ ≤ C ∧
      |x| ^ (k + 2) * ‖iteratedDeriv n v x‖ ≤ C :=
    ⟨(v.le_seminorm' ℂ k n x).trans (le_add_of_nonneg_right (apply_nonneg _ _)),
      (v.le_seminorm' ℂ (k + 2) n x).trans (le_add_of_nonneg_left (apply_nonneg _ _))⟩
  have hsum : 0 ≤ ∑' j, polynomialOrbitWeight g.1 j :=
    tsum_nonneg (polynomialOrbitWeight_nonneg g.1)
  apply u.seminorm_le_bound' ℂ k n (mul_nonneg hsum hC)
  intro x
  rw [mul_comm (∑' j, polynomialOrbitWeight g.1 j)]
  by_cases hx : 0 ≤ x
  · have hrec (y : ℝ) : ‖iteratedDeriv n u y‖ ≤
        ‖iteratedDeriv n v y‖ + ‖iteratedDeriv n u (y + g.1)‖ := by
      have h := norm_add_le (iteratedDeriv n v y) ((g.2 : ℂ) * iteratedDeriv n u (y + g.1))
      conv_lhs at h => rw [hv, sub_add_cancel]
      rwa [norm_mul, Circle.norm_coe, one_mul] at h
    exact norm_le_of_polynomial_tail hg hC k hrec (fun y _ ↦ hs y)
      ((iteratedDeriv_schwartz_tendsto_cocompact u n).mono_left atTop_le_cocompact) x hx
  · let U (y : ℝ) := iteratedDeriv n u (-y)
    let V (y : ℝ) := iteratedDeriv n v (-(y + g.1))
    have hrec (y : ℝ) : ‖U y‖ ≤ ‖V y‖ + ‖U (y + g.1)‖ := by
      have he : V y = U (y + g.1) - (g.2 : ℂ) * U y := by
        dsimp only [V, U]
        rw [hv, show -(y + g.1) + g.1 = -y by ring]
      have h := norm_sub_le (U (y + g.1)) (V y)
      rwa [he, sub_sub_cancel, norm_mul, Circle.norm_coe, one_mul, ← he, add_comm] at h
    have hV (y : ℝ) (hy : 0 ≤ y) : |y| ^ k * ‖V y‖ ≤ C ∧ |y| ^ (k + 2) * ‖V y‖ ≤ C := by
      have habs : |y| ≤ |-(y + g.1)| := by
        rw [abs_neg, abs_of_nonneg hy, abs_of_nonneg (add_nonneg hy hg.le)]
        exact le_add_of_nonneg_right hg.le
      exact ⟨(mul_le_mul_of_nonneg_right (by gcongr) (norm_nonneg _)).trans (hs _).1,
        (mul_le_mul_of_nonneg_right (by gcongr) (norm_nonneg _)).trans (hs _).2⟩
    have h₀ : Tendsto U atTop (𝓝 0) :=
      ((iteratedDeriv_schwartz_tendsto_cocompact u n).mono_left
        atBot_le_cocompact).comp tendsto_neg_atTop_atBot
    simpa only [Real.norm_eq_abs, abs_neg, U, neg_neg] using
      norm_le_of_polynomial_tail hg hC k hrec hV h₀ (-x) (neg_nonneg.mpr (le_of_not_ge hx))

/-- An ordinary real Schwartz difference with positive shift has closed range
and a continuous inverse on its range. -/
theorem schwartzCyclicDifference_isClosedEmbedding (g : ℝ × Circle) (hg : 0 < g.1) :
    IsClosedEmbedding (schwartzCyclicDifference g) := by
  let D := schwartzCyclicDifference g
  let R := D.range
  let P := schwartzSeminormFamily ℂ ℝ ℂ
  have hP : WithSeminorms P := schwartz_withSeminorms ℂ ℝ ℂ
  let C : ℝ≥0 := ⟨∑' j, polynomialOrbitWeight g.1 j,
    tsum_nonneg (polynomialOrbitWeight_nonneg g.1)⟩
  have hbound (i : ℕ × ℕ) (f : 𝓢(ℝ, ℂ)) :
      P i f ≤ (C : ℝ) * ((P i + P (i.1 + 2, i.2)) (D f)) := by
    rcases i with ⟨k, n⟩
    exact schwartzCyclicDifference_seminorm g hg k n f
  have hi : Injective D := by
    apply (injective_iff_map_eq_zero _).mpr
    intro f hf
    by_contra hne
    obtain ⟨i, hi⟩ := hP.separating_of_T1 f hne
    have hh := hbound i f
    rw [hf, map_zero, mul_zero] at hh
    exact hi (hh.antisymm (apply_nonneg _ _))
  let e := LinearEquiv.ofInjective D.toLinearMap hi
  have he : Continuous e.symm := by
    apply hP.continuous_of_continuous_comp e.symm.toLinearMap
    intro i
    have hc : Continuous (P i + P (i.1 + 2, i.2)) := by
      simpa using (hP.continuous_seminorm i).add (hP.continuous_seminorm (i.1 + 2, i.2))
    apply Seminorm.continuous_of_le
      (q := C • (P i + P (i.1 + 2, i.2)).comp R.subtype)
      ((hc.comp continuous_subtype_val).const_smul C)
    intro x
    obtain ⟨f, rfl⟩ := e.surjective x
    change P i (e.symm (e f)) ≤ (C : ℝ) * ((P i + P (i.1 + 2, i.2)) (D f))
    rw [e.symm_apply_apply]
    exact hbound i f
  let E : 𝓢(ℝ, ℂ) ≃L[ℂ] R := ⟨e, D.continuous.subtype_mk _, he⟩
  have hD : IsEmbedding D := IsEmbedding.subtypeVal.comp E.toHomeomorph.isEmbedding
  letI : CompleteSpace 𝓢(ℝ, ℂ) := completeSpace_schwartzMap
  exact (AddMonoidHom.isUniformEmbedding_of_isEmbedding
    (f := D.toLinearMap.toAddMonoidHom) hD).isClosedEmbedding

/-- Composing ordinary Schwartz differences retains the closed embedding. -/
theorem schwartzCyclicDifferenceProduct_isClosedEmbedding (gs : List (ℝ × Circle))
    (hgs : ∀ g ∈ gs, 0 < g.1) : IsClosedEmbedding (schwartzCyclicDifferenceProduct gs) := by
  induction gs with
  | nil => exact IsClosedEmbedding.id
  | cons g gs ih =>
    exact (schwartzCyclicDifference_isClosedEmbedding g (hgs g List.mem_cons_self)).comp
      (ih fun a ha ↦ hgs a (List.mem_cons_of_mem _ ha))

/-- The range is closed in every weighted topology containing the zero test. -/
theorem logDecayCyclicDifferenceProduct_range_isClosed (I : Set ℝ) (h0 : (0 : ℝ) ∈ I)
    (gs : List (ℝ × Circle)) (hgs : ∀ g ∈ gs, 0 < g.1) :
    IsClosed ((logDecayCyclicDifferenceProduct I ⟨0, h0⟩ gs).range :
      Set (PositiveRealExponentialDecay I)) := by
  rw [logDecayCyclicDifferenceProduct_range_eq_comap I h0 gs hgs]
  exact (schwartzCyclicDifferenceProduct_isClosedEmbedding gs hgs).isClosed_range.preimage
    (positiveRealExponentialDecay_zeroInclusion I h0).continuous

end Masullo
