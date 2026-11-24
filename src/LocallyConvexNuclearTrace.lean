import LocallyConvexApproximation
import NuclearTrace
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.MetricSpace.Equicontinuity

open Filter Function Set Topology
open scoped CompactConvergenceCLM InnerProductSpace TensorProduct

namespace Masullo

noncomputable section

/-- A summable scalar sequence can absorb the inverse of a positive null
sequence while retaining absolute summability. -/
theorem summable_div_positive_null (a : ℕ → ℝ) (ha : Summable a)
    (ha0 : ∀ n, 0 ≤ a n) :
    ∃ s : ℕ → ℝ, (∀ n, 0 < s n) ∧ Tendsto s atTop (𝓝 0) ∧
      Summable (fun n => a n / s n) := by
  let b (n : ℕ) : ℝ := a n + (1/2 : ℝ)^n
  have hb : Summable b := ha.add (summable_geometric_of_lt_one (by norm_num) (by norm_num))
  have hb0 (n : ℕ) : 0 < b n := add_pos_of_nonneg_of_pos (ha0 n) (by positivity)
  let r (n : ℕ) := ∑' k, b (k+n)
  have htail (n : ℕ) : Summable (fun k => b (k+n)) := (summable_nat_add_iff n).mpr hb
  have hr0 (n : ℕ) : 0 < r n :=
    ((htail n).le_tsum 0 (fun k _ => (hb0 (k+n)).le)).trans_lt' (by simpa using hb0 n)
  have hr_eq (n : ℕ) : r n = b n + r (n+1) := by
    simpa [r, Nat.add_right_comm, Nat.add_assoc] using (htail n).tsum_eq_zero_add
  have hr_lim : Tendsto r atTop (𝓝 0) := by
    have eq (n : ℕ) : r n = (∑' k, b k) - ∑ k ∈ Finset.range n, b k := by
      have h := hb.sum_add_tsum_nat_add n
      dsimp [r]
      linarith
    have hc : Tendsto (fun _ : ℕ => ∑' k, b k) atTop (𝓝 (∑' k, b k)) := tendsto_const_nhds
    have h := hc.sub hb.hasSum.tendsto_sum_nat
    rw [sub_self] at h
    exact h.congr (fun n => (eq n).symm)
  let s (n : ℕ) := √(r n)
  have hs0 (n : ℕ) : 0 < s n := Real.sqrt_pos.mpr (hr0 n)
  have hs_lim : Tendsto s atTop (𝓝 0) := by
    simpa [s, Function.comp_def] using (Real.continuous_sqrt.continuousAt (x := 0)).tendsto.comp hr_lim
  refine ⟨s, hs0, hs_lim, summable_of_sum_range_le (c := 2 * s 0)
    (fun n => div_nonneg (ha0 n) (hs0 n).le) (fun N => ?_)⟩
  have hmono (n : ℕ) : s (n+1) ≤ s n := Real.sqrt_le_sqrt (by rw [hr_eq n]; linarith [hb0 n])
  have hbd (n : ℕ) : a n / s n ≤ 2 * (s n - s (n+1)) := by
    have hs_sq (k : ℕ) : (s k)^2 = r k := Real.sq_sqrt (hr0 k).le
    have hdiff : b n = (s n - s (n+1)) * (s n + s (n+1)) := by
      calc
        _ = r n - r (n+1) := by rw [hr_eq n]; ring
        _ = _ := by rw [← hs_sq, ← hs_sq]; ring
    have hab : a n ≤ b n := le_add_of_nonneg_right (by positivity)
    apply (div_le_iff₀ (hs0 n)).mpr
    calc
      _ ≤ b n := hab
      _ = (s n - s (n+1)) * (s n + s (n+1)) := hdiff
      _ ≤ (s n - s (n+1)) * (2 * s n) :=
        mul_le_mul_of_nonneg_left (by linarith [hmono n]) (sub_nonneg.mpr (hmono n))
      _ = _ := by ring
  calc
    _ ≤ ∑ n ∈ Finset.range N, 2 * (s n - s (n+1)) := Finset.sum_le_sum fun n _ => hbd n
    _ = 2 * (s 0 - s N) := by rw [← Finset.mul_sum, Finset.sum_range_sub']
    _ ≤ _ := by linarith [hs0 N]

section

variable {E F G B : Type*}
variable [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℂ E]
variable [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul ℂ F]
variable [AddCommGroup G] [Module ℂ G] [TopologicalSpace G] [IsTopologicalAddGroup G] [ContinuousSMul ℂ G]
variable [NormedAddCommGroup B] [NormedSpace ℂ B]

/-- A presentation through a Banach disk of the target. The disk is given by
the unit ball of the normed source of the inclusion J. -/
structure NuclearExpansion (J : B →L[ℂ] F) (A : E →L[ℂ] F) where
  coeff : ℕ → ℂ
  functional : ℕ → E →L[ℂ] ℂ
  vector : ℕ → B
  coeff_summable : Summable (fun n => ‖coeff n‖)
  equicont : EquicontinuousAt (fun n x => functional n x) 0
  vector_bound : ∀ n, ‖vector n‖ ≤ 1
  hasSum_apply : ∀ x, HasSum (fun n => (coeff n * functional n x) • J (vector n)) (A x)

namespace NuclearExpansion

omit [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] in
theorem eventually_norm_le {φ : ℕ → E →L[ℂ] ℂ}
    (hφ : EquicontinuousAt (fun n x => φ n x) 0) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x in 𝓝 (0 : E), ∀ n, ‖φ n x‖ ≤ ε := by
  have h := (Metric.equicontinuousAt_iff_right.mp hφ) ε hε
  filter_upwards [h] with x hx n
  simpa [dist_eq_norm, norm_sub_rev] using (hx n).le

omit [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] in
private theorem bounded_on_disk {φ : ℕ → E →L[ℂ] ℂ}
    (hφ : EquicontinuousAt (fun n x => φ n x) 0) (P : B →L[ℂ] E) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ n v, ‖v‖ ≤ 1 → ‖φ n (P v)‖ ≤ M := by
  have h := (P.continuous.tendsto (0 : B)).eventually
    (eventually_norm_le hφ (ε := 1) zero_lt_one |>.filter_mono (by simp))
  obtain ⟨r, hr, hr'⟩ := Metric.eventually_nhds_iff.mp h
  have hs : 0 < r/2 := by positivity
  refine ⟨(r/2)⁻¹, by positivity, fun n v hv => ?_⟩
  have hv' : dist (((r/2 : ℝ) : ℂ) • v) 0 < r := by
    rw [dist_zero_right, norm_smul]
    have he : ‖((r/2 : ℝ) : ℂ)‖ = r/2 := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
    rw [he]
    exact ((mul_le_mul_of_nonneg_left hv hs.le).trans_eq (mul_one _)).trans_lt (half_lt_self hr)
  have hh := hr' hv' n
  rw [map_smul, map_smul, smul_eq_mul, norm_mul] at hh
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs] at hh
  simpa only [mul_one] using (le_inv_mul_iff₀ hs).mpr hh

variable {J : B →L[ℂ] F} {A : E →L[ℂ] F} (R : NuclearExpansion J A)

omit [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] [IsTopologicalAddGroup F] [ContinuousSMul ℂ F] in
theorem pair_summable (T : F →L[ℂ] E) :
    Summable (fun n => ‖R.coeff n * R.functional n (T (J (R.vector n)))‖) := by
  obtain ⟨M, hM, hBd⟩ := bounded_on_disk R.equicont (T.comp J)
  exact (R.coeff_summable.mul_right M).of_nonneg_of_le (fun n => norm_nonneg _) fun n => by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hBd n _ (R.vector_bound n)) (norm_nonneg _)

def pair (T : F →L[ℂ] E) : ℂ :=
  ∑' n, R.coeff n * R.functional n (T (J (R.vector n)))

omit [ContinuousSMul ℂ E] [IsTopologicalAddGroup F] [ContinuousSMul ℂ F] in
theorem pair_add (T S : F →L[ℂ] E) : R.pair (T + S) = R.pair T + R.pair S := by
  simp only [pair, add_apply, map_add, mul_add]
  exact ((R.pair_summable T).of_norm.tsum_add (R.pair_summable S).of_norm)

omit [IsTopologicalAddGroup E] [IsTopologicalAddGroup F] [ContinuousSMul ℂ F] in
theorem pair_smul (c : ℂ) (T : F →L[ℂ] E) : R.pair (c • T) = c * R.pair T := by
  simp only [pair, smul_apply, map_smul, smul_eq_mul]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  ring

omit [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] [IsTopologicalAddGroup F] [ContinuousSMul ℂ F] in
theorem pair_zero : R.pair 0 = 0 := by
  simp [pair, zero_apply]

omit [IsTopologicalAddGroup F] [ContinuousSMul ℂ F] in
theorem pair_sub (T S : F →L[ℂ] E) : R.pair (T - S) = R.pair T - R.pair S := by
  rw [sub_eq_add_neg, pair_add, ← neg_one_smul ℂ S, pair_smul]
  ring


omit [IsTopologicalAddGroup E] [IsTopologicalAddGroup F] [ContinuousSMul ℂ F] in
theorem pair_rankOne (φ : F →L[ℂ] ℂ) (x : E) : R.pair (φ.smulRight x) = φ (A x) := by
  apply HasSum.tsum_eq
  convert φ.hasSum (R.hasSum_apply x) using 1
  funext n
  simp only [ContinuousLinearMap.smulRight_apply, map_smul, smul_eq_mul]
  ring

omit [IsTopologicalAddGroup F] [ContinuousSMul ℂ F] in
theorem pair_tensor_eq {K : Type*} [NormedAddCommGroup K] [NormedSpace ℂ K]
    {Q : K →L[ℂ] F} (S : NuclearExpansion Q A) (v : (F →L[ℂ] ℂ) ⊗[ℂ] E) :
    R.pair (tensorOperator F E v) = S.pair (tensorOperator F E v) := by
  induction v using TensorProduct.induction_on with
  | zero =>
    rw [map_zero]
    exact (R.pair_zero).trans S.pair_zero.symm
  | tmul φ x =>
    have eq : (tensorOperator F E (φ ⊗ₜ[ℂ] x) : F →L[ℂ] E) = φ.smulRight x := by
      ext y
      exact tensorOperator_tmul φ x y
    rw [eq, R.pair_rankOne, S.pair_rankOne]
  | add v w hv hw =>
    rw [map_add]
    let t : F →L[ℂ] E := tensorOperator F E v
    let s : F →L[ℂ] E := tensorOperator F E w
    change R.pair (t + s) = S.pair (t + s)
    exact (R.pair_add t s).trans ((congrArg₂ (· + ·) hv hw).trans (S.pair_add t s).symm)

omit [ContinuousSMul ℂ E] [IsTopologicalAddGroup F] [ContinuousSMul ℂ F] in
/-- The trace pairing of a nuclear expansion is continuous on the space
of operators endowed with compact convergence. -/
theorem pair_continuous : Continuous (fun T : F →L_c[ℂ] E => R.pair T) := by
  let L : (F →L_c[ℂ] E) →+ ℂ :=
    { toFun := fun T => R.pair T
      map_zero' := R.pair_zero
      map_add' := fun T S => R.pair_add T S }
  apply continuous_of_continuousAt_zero L
  rw [ContinuousAt, map_zero, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨s, hs, hsLim, hsum⟩ := summable_div_positive_null (fun n => ‖R.coeff n‖)
    R.coeff_summable (fun n => norm_nonneg _)
  let z (n : ℕ) := J (((s n : ℝ) : ℂ) • R.vector n)
  let K := insert 0 (range z)
  have hz : Tendsto z atTop (𝓝 0) := by
    have hu : Tendsto (fun n => ((s n : ℝ) : ℂ) • R.vector n) atTop (𝓝 (0 : B)) := by
      apply tendsto_zero_iff_norm_tendsto_zero.mpr
      apply squeeze_zero (fun _ => norm_nonneg _) _ hsLim
      intro n
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hs n)]
      exact (mul_le_mul_of_nonneg_left (R.vector_bound n) (hs n).le).trans_eq (mul_one _)
    simpa only [map_zero, Function.comp_def, z] using (J.continuous.tendsto 0).comp hu
  let a (n : ℕ) := ‖R.coeff n‖ / s n
  let M := ∑' n, a n
  have hM : 0 ≤ M := tsum_nonneg (fun n => div_nonneg (norm_nonneg _) (hs n).le)
  let δ := ε / (2 * (1 + M))
  have hδ : 0 < δ := by positivity
  let V := {x : E | ∀ n, ‖R.functional n x‖ ≤ δ}
  have hV : V ∈ 𝓝 (0 : E) := eventually_norm_le R.equicont hδ
  have hN : {T : F →L_c[ℂ] E | ∀ x ∈ K, T x ∈ V} ∈ 𝓝 (0 : F →L_c[ℂ] E) :=
    CompactConvergenceCLM.hasBasis_nhds_zero.mem_of_mem (i := (K, V))
      ⟨hz.isCompact_insert_range, hV⟩
  filter_upwards [hN] with T hT
  let d (n : ℕ) : ℂ := R.coeff n / ((s n : ℝ) : ℂ) * R.functional n (T (z n))
  have he (n : ℕ) : R.coeff n * R.functional n (T (J (R.vector n))) = d n := by
    dsimp only [d, z]
    rw [map_smul, map_smul, map_smul, smul_eq_mul]
    field_simp [Complex.ofReal_ne_zero.mpr (hs n).ne']
  have hbd (n : ℕ) : ‖d n‖ ≤ a n * δ := by
    have ht := hT (z n) (Or.inr (mem_range_self n))
    rw [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hs n)]
    exact mul_le_mul_of_nonneg_left (ht n) (div_nonneg (norm_nonneg _) (hs n).le)
  have hsum' : Summable (fun n => a n * δ) := hsum.mul_right δ
  have hd : Summable (fun n => ‖d n‖) := hsum'.of_nonneg_of_le (fun _ => norm_nonneg _) hbd
  change dist (R.pair T) 0 < ε
  rw [dist_zero_right]
  change ‖∑' n, R.coeff n * R.functional n (T (J (R.vector n)))‖ < ε
  simp only [he]
  calc
    ‖∑' n, d n‖ ≤ ∑' n, ‖d n‖ := norm_tsum_le_tsum_norm hd
    _ ≤ ∑' n, a n * δ := hd.tsum_le_tsum hbd hsum'
    _ = M * δ := tsum_mul_right
    _ < ε := by
      change M * (ε / (2 * (1 + M))) < ε
      have hh : 0 < 2 * (1 + M) := by positivity
      rw [← mul_div_assoc, div_lt_iff₀ hh]
      nlinarith


/-- Postcomposition applies the continuous map to the disk inclusion. -/
def postcomp (T : F →L[ℂ] G) : NuclearExpansion (T.comp J) (T.comp A) where
  coeff := R.coeff
  functional := R.functional
  vector := R.vector
  coeff_summable := R.coeff_summable
  equicont := R.equicont
  vector_bound := R.vector_bound
  hasSum_apply x := by
    simpa only [ContinuousLinearMap.comp_apply, map_smul] using (T.hasSum (R.hasSum_apply x))

/-- Precomposition pulls back the equicontinuous family of functionals. -/
def precomp (T : G →L[ℂ] E) : NuclearExpansion J (A.comp T) where
  coeff := R.coeff
  functional n := (R.functional n).comp T
  vector := R.vector
  coeff_summable := R.coeff_summable
  equicont := by
    apply Metric.equicontinuousAt_iff_right.mpr
    intro ε hε
    have ht : Tendsto T (𝓝 0) (𝓝 0) := by simpa only [map_zero] using T.continuous.tendsto 0
    filter_upwards [ht.eventually (Metric.equicontinuousAt_iff_right.mp R.equicont ε hε)] with x hx i
    simpa only [ContinuousLinearMap.comp_apply, map_zero] using hx i
  vector_bound := R.vector_bound
  hasSum_apply x := R.hasSum_apply (T x)

omit [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] [IsTopologicalAddGroup F] [ContinuousSMul ℂ F] in
include R in
/-- Both vectors and functionals of a nuclear representation may be chosen
to tend to zero, uniformly on a fixed neighborhood for the functionals. -/
theorem exists_null_rescaling :
    ∃ S : NuclearExpansion J A, Tendsto S.vector atTop (𝓝 0) ∧
      ∃ V ∈ 𝓝 (0 : E), ∀ ε > (0 : ℝ), ∀ᶠ n in atTop, ∀ x ∈ V, ‖S.functional n x‖ < ε := by
  obtain ⟨s, hs, hLim, hsum⟩ := summable_div_positive_null (fun n => ‖R.coeff n‖)
    R.coeff_summable (fun _ => norm_nonneg _)
  let b (n : ℕ) := min (s n) 1
  let d (n : ℕ) := √(b n)
  have hb0 (n : ℕ) : 0 < b n := lt_min (hs n) zero_lt_one
  have hd0 (n : ℕ) : 0 < d n := Real.sqrt_pos.mpr (hb0 n)
  have hd1 (n : ℕ) : d n ≤ 1 := Real.sqrt_le_one.mpr (min_le_right _ _)
  have hdsq (n : ℕ) : (d n)^2 = b n := Real.sq_sqrt (hb0 n).le
  have hbLim : Tendsto b atTop (𝓝 0) := by
    simpa only [min_eq_left zero_le_one] using
      hLim.min (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))
  have hdLim : Tendsto d atTop (𝓝 0) := by
    simpa [d, Function.comp_def] using (Real.continuous_sqrt.continuousAt (x := 0)).tendsto.comp hbLim
  have hcoef : Summable (fun n => ‖R.coeff n / ((b n : ℝ) : ℂ)‖) := by
    apply (hsum.add R.coeff_summable).of_nonneg_of_le (fun _ => norm_nonneg _)
    intro n
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hb0 n)]
    by_cases h : s n ≤ 1
    · rw [show b n = s n from min_eq_left h]
      exact le_add_of_nonneg_right (norm_nonneg _)
    · rw [show b n = 1 from min_eq_right (le_of_not_ge h), div_one]
      exact le_add_of_nonneg_left (div_nonneg (norm_nonneg _) (hs n).le)
  let c (n : ℕ) : ℂ := ↑(d n)
  have hcn (n : ℕ) : ‖c n‖ = d n := by
    dsimp [c]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hd0 n)]
  have hcsq (n : ℕ) : (c n)^2 = ↑(b n) := by
    dsimp [c]
    exact_mod_cast hdsq n
  let S : NuclearExpansion J A :=
    { coeff := fun n => R.coeff n / ((b n : ℝ) : ℂ)
      functional := fun n => c n • R.functional n
      vector := fun n => c n • R.vector n
      coeff_summable := hcoef
      equicont := by
        apply Metric.equicontinuousAt_iff_right.mpr
        intro ε hε
        filter_upwards [(Metric.equicontinuousAt_iff_right.mp R.equicont ε hε)] with x hx n
        simp only [smul_apply, map_zero, dist_zero_left] at hx ⊢
        rw [norm_smul, hcn]
        exact ((mul_le_mul_of_nonneg_right (hd1 n) (norm_nonneg _)).trans_eq (one_mul _)).trans_lt (hx n)
      vector_bound := fun n => by
        rw [norm_smul, hcn]
        exact ((mul_le_mul_of_nonneg_left (R.vector_bound n) (hd0 n).le).trans_eq (mul_one _)).trans (hd1 n)
      hasSum_apply := fun x => by
        have eq (n : ℕ) :
            ((R.coeff n / ((b n : ℝ) : ℂ)) * (c n • R.functional n) x) • J (c n • R.vector n) =
              (R.coeff n * R.functional n x) • J (R.vector n) := by
          rw [smul_apply, smul_eq_mul, map_smul, ← mul_smul]
          congr 1
          have hcb : (↑(b n) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hb0 n).ne'
          field_simp [hcb]
          calc
            _ = R.coeff n * R.functional n x * (c n)^2 := by ring
            _ = _ := by rw [hcsq]; ring
        simpa only [eq] using R.hasSum_apply x }
  refine ⟨S, ?_, {x | ∀ n, ‖R.functional n x‖ ≤ 1}, eventually_norm_le R.equicont zero_lt_one, ?_⟩
  · apply tendsto_zero_iff_norm_tendsto_zero.mpr
    refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) hdLim
    change ‖c n • R.vector n‖ ≤ d n
    rw [norm_smul, hcn]
    exact (mul_le_mul_of_nonneg_left (R.vector_bound n) (hd0 n).le).trans_eq (mul_one _)
  · intro ε hε
    filter_upwards [(Metric.tendsto_nhds.mp hdLim) ε hε] with n hn x hx
    change ‖(c n • R.functional n) x‖ < ε
    rw [smul_apply, norm_smul, hcn]
    rw [dist_zero_right, Real.norm_eq_abs, abs_of_pos (hd0 n)] at hn
    exact ((mul_le_mul_of_nonneg_left (hx n) (hd0 n).le).trans_eq (mul_one _)).trans_lt hn

end NuclearExpansion

namespace NuclearExpansion

variable {J : B →L[ℂ] E} {A : E →L[ℂ] E} (R : NuclearExpansion J A)

def trace : ℂ := R.pair (ContinuousLinearMap.id ℂ E)

omit [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] in
theorem trace_absolutely_summable :
    Summable (fun n => ‖R.coeff n * R.functional n (J (R.vector n))‖) :=
  R.pair_summable (ContinuousLinearMap.id ℂ E)

section HilbertDiagonal

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {JH : B →L[ℂ] H} {AH : H →L[ℂ] H}

/-- Definition C.3.4.2(1). The Hilbert diagonal has the same sum as the
locally convex nuclear trace. The argument bounding the rank-one costs by
the uniform functional and vector bounds follows original commit 60ac997. -/
theorem hilbertDiagonal_hasSum_trace (R : NuclearExpansion JH AH)
    {ι : Type*} (b : HilbertBasis ι ℂ H) :
    HasSum (fun i => ⟪b i, AH (b i)⟫_ℂ) R.trace := by
  let D := InnerProductSpace.toDual ℂ H
  have hdual (n : ℕ) (x : H) : ⟪D.symm (R.functional n), x⟫_ℂ = R.functional n x :=
    DFunLike.congr_fun (D.apply_symm_apply (R.functional n)) x
  obtain ⟨M, hM, hbound⟩ := bounded_on_disk R.equicont (ContinuousLinearMap.id ℂ H)
  have hnorm (n : ℕ) : ‖R.functional n‖ ≤ M := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm hM
    intro x hx
    exact hbound n x hx.le
  let T : RankOneSeries ℕ H :=
    { image := fun n => R.coeff n • JH (R.vector n)
      functional := fun n => D.symm (R.functional n)
      summableNorm := (R.coeff_summable.mul_right (‖JH‖ * M)).of_nonneg_of_le
        (fun _ => by positivity) fun n => by
          rw [norm_smul, D.symm.norm_map, mul_assoc]
          have hvec := (JH.le_opNorm (R.vector n)).trans
            (mul_le_of_le_one_right (norm_nonneg _) (R.vector_bound n))
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul hvec (hnorm n) (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _) }
  have hop : T.operator = AH := by
    ext x
    rw [T.operator_apply]
    simpa [T, hdual, smul_smul, mul_comm] using (R.hasSum_apply x).tsum_eq
  have htrace : T.trace = R.trace := by
    unfold RankOneSeries.trace trace pair
    exact tsum_congr fun n => by simp [T, hdual, smul_eq_mul]
  simpa only [hop, htrace] using T.hasSum_diagonal b

end HilbertDiagonal

/-- C.3.2.1. The approximation property makes the absolutely convergent
diagonal sum independent of the nuclear expansion. -/
theorem trace_eq_of_approximation (hE : HasCompactApproximation E)
    {K : Type*} [NormedAddCommGroup K] [NormedSpace ℂ K]
    {Q : K →L[ℂ] E} (S : NuclearExpansion Q A) : R.trace = S.trace := by
  have hEq : IsClosed {T : E →L_c[ℂ] E | R.pair T = S.pair T} :=
    isClosed_eq R.pair_continuous S.pair_continuous
  have hf : range (tensorOperator E E) ⊆ {T : E →L_c[ℂ] E | R.pair T = S.pair T} := by
    rintro _ ⟨v, rfl⟩
    exact R.pair_tensor_eq S v
  exact closure_minimal hf hEq hE

omit [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] in
/-- C.3.2.1. Conjugation transports the expansion and preserves its trace. -/
theorem trace_conjugation (T : E ≃L[ℂ] E) :
    ((R.precomp T.toContinuousLinearMap).postcomp T.symm.toContinuousLinearMap).trace = R.trace := by
  unfold trace pair
  apply tsum_congr
  intro n
  simp [precomp, postcomp]

end NuclearExpansion

/-- C.3.2.2. A nuclear factorization through a continuous injection has the
same trace on both spaces with the approximation property. -/
theorem nuclear_trace_injection
    {A₀ : F →L[ℂ] E} {J : B →L[ℂ] E} (R : NuclearExpansion J A₀)
    (T : E →L[ℂ] F) (hE : HasCompactApproximation E) (hF : HasCompactApproximation F)
    {K₁ K₂ : Type*} [NormedAddCommGroup K₁] [NormedSpace ℂ K₁]
    [NormedAddCommGroup K₂] [NormedSpace ℂ K₂]
    {J₁ : K₁ →L[ℂ] E} {J₂ : K₂ →L[ℂ] F}
    (S₁ : NuclearExpansion J₁ (A₀.comp T)) (S₂ : NuclearExpansion J₂ (T.comp A₀)) :
    S₁.trace = S₂.trace := by
  calc
    S₁.trace = (R.precomp T).trace := S₁.trace_eq_of_approximation hE _
    _ = (R.postcomp T).trace := rfl
    _ = S₂.trace := (R.postcomp T).trace_eq_of_approximation hF _


omit [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] [IsTopologicalAddGroup F] [ContinuousSMul ℂ F] in
/-- The two cyclic factorizations preserve the injective Banach disk model.
The expansions themselves exist whether or not the domain has the approximation property. -/
theorem nuclear_injection_preserves_disk
    [CompleteSpace B] {A₀ : F →L[ℂ] E} {J : B →L[ℂ] E} (R : NuclearExpansion J A₀)
    (hJ : Injective J) (T : E →L[ℂ] F) (hT : Injective T) :
    (Injective J ∧ Nonempty (NuclearExpansion J (A₀.comp T))) ∧
    (Injective (T.comp J) ∧ Nonempty (NuclearExpansion (T.comp J) (T.comp A₀))) :=
  ⟨⟨hJ, ⟨R.precomp T⟩⟩, ⟨hT.comp hJ, ⟨R.postcomp T⟩⟩⟩


end

end

end Masullo
