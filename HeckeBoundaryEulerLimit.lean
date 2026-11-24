import HeckeBoundaryTails
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

open Complex Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical NumberField Topology

namespace Masullo

noncomputable section

private abbrev dirichletAbelWeight (u : ℝ) (n : ℕ) : ℝ := ((n+2 : ℕ) : ℝ) ^ (-u)

/-- Abel's boundary theorem for ordinary Dirichlet partial sums indexed
by the integer norms starting at two. -/
theorem tendsto_dirichletAbel_right {a : ℕ → ℂ} {L : ℂ}
    (ha : Tendsto (fun n ↦ ∑ j ∈ Finset.range n, a j) atTop (𝓝 L))
    (hs : ∀ u > (0 : ℝ), Summable (fun n ↦ dirichletAbelWeight u n • a n)) :
    Tendsto (fun u : ℝ ↦ ∑' n, dirichletAbelWeight u n • a n) (𝓝[>] 0) (𝓝 L) := by
  let S (n : ℕ) := ∑ j ∈ Finset.range n, a j
  let b (n : ℕ) := a n - if n = 0 then L else 0
  let P (m : ℕ) (u : ℝ) := ∑ j ∈ Finset.range m, dirichletAbelWeight u j • a j
  have hB (n : ℕ) (hn : 0 < n) : (∑ j ∈ Finset.range n, b j) = S n - L := by
    simpa only [one_smul] using
      sum_range_adjust_first (fun j (_ : Unit) ↦ a j) (fun _ ↦ L) (fun _ ↦ 1) hn ()
  have htail (m : ℕ) (hm : 0 < m) (e : ℝ) (he : 0 ≤ e)
      (hS : ∀ n ≥ m, ‖S n - L‖ ≤ e) (u : ℝ) (hu : 0 < u) :
      ‖(∑' n, dirichletAbelWeight u n • a n) - P m u‖ ≤ 2 * e := by
    let w := dirichletAbelWeight u
    have hw : Antitone w := by
      intro i j hij
      exact Real.rpow_le_rpow_of_nonpos (by positivity) (by exact_mod_cast Nat.add_le_add_right hij 2)
        (neg_nonpos.mpr hu.le)
    have hw₀ (n : ℕ) : 0 ≤ w n := Real.rpow_nonneg (by positivity) _
    have hw₁ (n : ℕ) : w n ≤ 1 := by
      apply Real.rpow_le_one_of_one_le_of_nonpos _ (neg_nonpos.mpr hu.le)
      exact_mod_cast (show 1 ≤ n+2 by omega)
    have hf (n : ℕ) (hn : m < n) : ‖P n u - P m u‖ ≤ 2 * e := by
      rw [← Finset.sum_Ico_eq_sub (fun j ↦ w j • a j) hn.le]
      have heq : (∑ j ∈ Finset.Ico m n, w j • a j) = ∑ j ∈ Finset.Ico m n, w j • b j :=
        Finset.sum_congr rfl fun j hj ↦ by
          have hj₀ : j ≠ 0 := (hm.trans_le (Finset.mem_Ico.mp hj).1).ne'
          simp [b, hj₀]
      rw [heq]
      refine (norm_abelWeightedTail_le w b hw hw₀ hn (ε := e) (fun j hj ↦ ?_)).trans ?_
      · rw [hB j (hm.trans_le hj)]
        exact hS j hj
      · simpa only [mul_one] using mul_le_mul_of_nonneg_left (hw₁ m) (by positivity : 0 ≤ 2 * e)
    exact le_of_tendsto (((hs u hu).tendsto_sum_tsum_nat.sub_const (P m u)).norm)
      ((eventually_gt_atTop m).mono fun n hn ↦ hf n hn)
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  let e := ε / 4
  have he : 0 < e := div_pos hε (by norm_num)
  obtain ⟨m₀, hm₀⟩ := eventually_atTop.mp (((ha.sub_const L).norm).eventually_lt_const (by simpa using he))
  let m := max 1 m₀
  have hm : 0 < m := zero_lt_one.trans_le (le_max_left _ _)
  have hS (n : ℕ) (hn : m ≤ n) : ‖S n - L‖ ≤ e := (hm₀ n ((le_max_right 1 m₀).trans hn)).le
  have hPc : Continuous (P m) := by
    apply continuous_finsetSum
    intro j _
    exact ((Real.continuous_const_rpow (by positivity : (((j+2 : ℕ) : ℝ)) ≠ 0)).comp continuous_neg).smul
      continuous_const
  have hP₀ : P m 0 = S m := by simp [P, S, dirichletAbelWeight]
  obtain ⟨δ, hδ, hc⟩ := Metric.continuousAt_iff.mp (hPc.continuousAt (x := 0)) e he
  refine ⟨δ, hδ, fun u hu hdu ↦ ?_⟩
  have hclose := hc hdu
  rw [hP₀, dist_eq_norm] at hclose
  rw [dist_eq_norm]
  have h₁ := htail m hm e he.le hS u hu
  have h₂ := hS m le_rfl
  have hh := norm_sub_le_norm_sub_add_norm_sub (∑' n, dirichletAbelWeight u n • a n) (P m u) L
  have hh' := norm_sub_le_norm_sub_add_norm_sub (P m u) (S m) L
  linarith [show e = ε / 4 from rfl]

variable (F : Type*) [Field F] [NumberField F]

private abbrev K := normOneIdeleClass F
private abbrev Place := HeightOneSpectrum (𝓞 F)

/-- One logarithmic Euler coefficient indexed by a place and the
predecessor of the prime-power exponent. -/
def heckePrimePowerLogTerm (c : Place F → ℂ) (s : ℂ) (j : Place F × ℕ) : ℂ :=
  c j.1 ^ (j.2+1) / ((j.2+1 : ℕ) : ℂ) * ((heckePrimePowerIdeal F j).absNorm : ℂ) ^ (-s)

private theorem one_lt_boundaryPrimePowerNorm (j : Place F × ℕ) :
    1 < (heckePrimePowerIdeal F j).absNorm := by
  rw [heckePrimePowerIdeal, map_pow]
  exact Nat.one_lt_pow (Nat.succ_ne_zero _) (NumberField.HeightOneSpectrum.one_lt_absNorm j.1)

private theorem summable_norm_heckePrimePowerLogTerm (c : Place F → ℂ) (hc : ∀ v, ‖c v‖ ≤ 1)
    {s : ℂ} (hs : 1 < s.re) : Summable fun j ↦ ‖heckePrimePowerLogTerm F c s j‖ := by
  refine ((summable_norm_heckePrimePowerTerm F c hc hs).mul_left (Real.log 2)⁻¹).of_nonneg_of_le
    (fun _ ↦ norm_nonneg _) fun j ↦ ?_
  have hp : (2 : ℝ) ≤ (heckePrimePowerIdeal F j).absNorm := by
    exact_mod_cast Nat.succ_le_of_lt (one_lt_boundaryPrimePowerNorm F j)
  have hlog₂ : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hp
  rw [← show _ = heckePrimePowerLogTerm F c s j from heckePrimePowerLog_from_logDerivative F c s j,
    norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (hlog₂.le.trans hlog)]
  exact mul_le_mul_of_nonneg_right (inv_anti₀ hlog₂ hlog) (norm_nonneg _)

private theorem norm_boundaryEulerRatio_lt_one (c : Place F → ℂ) (hc : ∀ v, ‖c v‖ ≤ 1)
    (v : Place F) {s : ℂ} (hs : 0 < s.re) : ‖c v * (v.asIdeal.absNorm : ℂ) ^ (-s)‖ < 1 := by
  have hq : (1 : ℝ) < v.asIdeal.absNorm := by
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  rw [norm_mul, ← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans hq),
    Complex.neg_re]
  exact (mul_le_of_le_one_left (Real.rpow_nonneg (zero_lt_one.trans hq).le _) (hc v)).trans_lt
    (Real.rpow_lt_one_of_one_lt_of_neg hq (neg_neg_of_pos hs))

private theorem hasSum_heckePrimePowerLogTerm_local (c : Place F → ℂ) (hc : ∀ v, ‖c v‖ ≤ 1)
    (v : Place F) {s : ℂ} (hs : 0 < s.re) :
    HasSum (fun k : ℕ ↦ heckePrimePowerLogTerm F c s (v,k))
      (-Complex.log (1 - c v * (v.asIdeal.absNorm : ℂ) ^ (-s))) := by
  let z := c v * (v.asIdeal.absNorm : ℂ) ^ (-s)
  have he : (fun k : ℕ ↦ heckePrimePowerLogTerm F c s (v,k)) =
      fun k : ℕ ↦ z ^ (k+1) / (k+1) := by
    funext k
    dsimp only [heckePrimePowerLogTerm, z, heckePrimePowerIdeal]
    rw [map_pow, Nat.cast_pow, ← Complex.natCast_cpow_natCast_mul, Complex.cpow_nat_mul, mul_pow]
    push_cast
    ring
  rw [he]
  exact Complex.hasSum_taylorSeries_neg_log' (norm_boundaryEulerRatio_lt_one F c hc v hs)

private theorem exp_tsum_heckePrimePowerLogTerm_local (c : Place F → ℂ) (hc : ∀ v, ‖c v‖ ≤ 1)
    (v : Place F) {s : ℂ} (hs : 0 < s.re) :
    Complex.exp (∑' k : ℕ, heckePrimePowerLogTerm F c s (v,k)) = heckeEulerFactor F c v s := by
  let z := c v * (v.asIdeal.absNorm : ℂ) ^ (-s)
  have hsum := (hasSum_heckePrimePowerLogTerm_local F c hc v hs).tsum_eq
  rw [hsum, heckeEulerFactor, Complex.exp_neg]
  have h : 1 - z ≠ 0 := sub_ne_zero.mpr fun he ↦ by
    have hn : ‖z‖ < 1 := norm_boundaryEulerRatio_lt_one F c hc v hs
    simp [← he] at hn
  rw [Complex.exp_log h]

/-- In the open half-plane of absolute convergence, exponentiating the
logarithmic prime-power series gives the actual infinite Euler product. -/
theorem exp_tsum_heckePrimePowerLogTerm (c : Place F → ℂ) (hc : ∀ v, ‖c v‖ ≤ 1)
    {s : ℂ} (hs : 1 < s.re) :
    Complex.exp (∑' j, heckePrimePowerLogTerm F c s j) =
      ∏' v, heckeEulerFactor F c v s := by
  have h := (summable_norm_heckePrimePowerLogTerm F c hc hs).of_norm
  let A (v : Place F) := ∑' k : ℕ, heckePrimePowerLogTerm F c s (v,k)
  have hp : HasProd (fun v ↦ Complex.exp (A v)) (Complex.exp (∑' v, A v)) := by
    have ht : Tendsto (fun S : Finset (Place F) ↦ Complex.exp (∑ v ∈ S, A v)) atTop
        (𝓝 (Complex.exp (∑' v, A v))) := Complex.continuous_exp.continuousAt.tendsto.comp h.prod.hasSum
    change Tendsto (fun S : Finset (Place F) ↦ ∏ v ∈ S, Complex.exp (A v)) atTop _
    simpa only [Complex.exp_sum] using ht
  rw [h.tsum_prod, ← hp.tprod_eq]
  exact tprod_congr fun v ↦ exp_tsum_heckePrimePowerLogTerm_local F c hc v (zero_lt_one.trans hs)

private def groupedBoundaryLogTerm (c : Place F → ℂ) (s : ℂ) (n : ℕ) : ℂ :=
  heckeBoundaryLogWeight n • LSeries.term (heckeVonMangoldtCoefficient F c) s (n+2)

private theorem groupedBoundaryLogTerm_shift (c : Place F → ℂ) (s : ℂ) (u : ℝ) (n : ℕ) :
    groupedBoundaryLogTerm F c (s + (u : ℂ)) n =
      dirichletAbelWeight u n • groupedBoundaryLogTerm F c s n := by
  have hn : n + 2 ≠ 0 := by omega
  have hn' : ((n + 2 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hn
  have hc : ((dirichletAbelWeight u n : ℝ) : ℂ) = (((n+2 : ℕ) : ℂ) ^ (u : ℂ))⁻¹ := by
    rw [dirichletAbelWeight, Complex.ofReal_cpow (by positivity), Complex.ofReal_neg,
      Complex.ofReal_natCast, Complex.cpow_neg]
  simp only [groupedBoundaryLogTerm, LSeries.term_of_ne_zero hn, Complex.real_smul, hc,
    Complex.cpow_add _ _ hn', div_eq_mul_inv, mul_inv_rev]
  ring

private theorem summable_groupedBoundaryLogTerm (c : Place F → ℂ) (hc : ∀ v, ‖c v‖ ≤ 1)
    {s : ℂ} (hs : 1 < s.re) : Summable (groupedBoundaryLogTerm F c s) := by
  obtain ⟨hw, h₀, _⟩ := abelReciprocalLogWeight
  have e (n : ℕ) : heckeBoundaryLogWeight n ≤ heckeBoundaryLogWeight 0 := hw (Nat.zero_le n)
  exact ((summable_norm_term_heckeVonMangoldtCoefficient F c hc hs).comp_injective
    (show Injective (fun n : ℕ ↦ n+2) from fun _ _ h ↦ Nat.add_right_cancel h)
    ).mul_left (heckeBoundaryLogWeight 0) |>.of_norm_bounded fun n ↦ by
      rw [groupedBoundaryLogTerm, norm_smul,
        Real.norm_of_nonneg (show 0 ≤ heckeBoundaryLogWeight n from h₀ n)]
      exact mul_le_mul_of_nonneg_right (e n) (norm_nonneg _)

private theorem tsum_groupedBoundaryLogTerm_eq (c : Place F → ℂ) (hc : ∀ v, ‖c v‖ ≤ 1)
    {s : ℂ} (hs : 1 < s.re) :
    (∑' n, groupedBoundaryLogTerm F c s n) = ∑' j, heckePrimePowerLogTerm F c s j := by
  have hy : Tendsto (fun n : ℕ ↦ (((n+2 : ℕ) : ℝ))) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2)
  have hg (n : ℕ) : (∑ j ∈ Finset.range n, groupedBoundaryLogTerm F c s j) =
      ∑ j ∈ heckePrimePowerNormCutoff F (((n+2 : ℕ) : ℝ)), heckePrimePowerLogTerm F c s j :=
    sum_heckeBoundaryLogWeight F c s (Nat.ceil_natCast _)
  exact tendsto_nhds_unique (summable_groupedBoundaryLogTerm F c hc hs).tendsto_sum_tsum_nat
    ((((summable_norm_heckePrimePowerLogTerm F c hc hs).of_norm.hasSum).comp
      ((tendsto_heckePrimePowerNormCutoff F).comp hy)).congr fun n ↦ (hg n).symm)

/-- Abel's right limit for the grouped logarithms identifies their
exponential with any finite Euler continuation continuous at the boundary point. -/
theorem exp_heckeBoundaryLog_eq_continuation
    (c : Place F → ℂ) (hc : ∀ v, ‖c v‖ ≤ 1) {L : ℂ → ℂ} {s l : ℂ} (hs : s.re = 1)
    (hL : ContinuousAt L s)
    (he : EqOn L (fun w ↦ ∏' v, heckeEulerFactor F c v w) {w | 1 < w.re})
    (hl : Tendsto (fun x ↦ heckePrimePowerLogPartial F c x s) atTop (𝓝 l)) :
    Complex.exp l = L s := by
  have hseq : Tendsto (fun n ↦ ∑ j ∈ Finset.range n, groupedBoundaryLogTerm F c s j)
      atTop (𝓝 l) := by
    refine (hl.comp (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2))).congr fun n ↦ ?_
    exact (sum_heckeBoundaryLogWeight F c s (Nat.ceil_natCast (R := ℝ) (n+2))).symm
  have hright (u : ℝ) (hu : 0 < u) : 1 < (s + (u : ℂ)).re := by
    simpa [Complex.add_re, hs] using hu
  have ha := tendsto_dirichletAbel_right hseq (fun u hu ↦
    (summable_groupedBoundaryLogTerm F c hc (hright u hu)).congr fun n ↦
      groupedBoundaryLogTerm_shift F c s u n)
  have hA := Complex.continuous_exp.continuousAt.tendsto.comp ha
  have hsL : Tendsto (fun u : ℝ ↦ s + (u : ℂ)) (𝓝[>] 0) (𝓝 s) := by
    have hct : Continuous (fun u : ℝ ↦ s + (u : ℂ)) := continuous_const.add Complex.continuous_ofReal
    simpa using tendsto_nhdsWithin_of_tendsto_nhds (s := Ioi 0) (hct.continuousAt (x := 0))
  refine tendsto_nhds_unique (hA.congr' ?_) (hL.tendsto.comp hsL)
  filter_upwards [self_mem_nhdsWithin (s := Ioi (0 : ℝ))] with u hu
  change Complex.exp (∑' n, dirichletAbelWeight u n • groupedBoundaryLogTerm F c s n) = L (s + ↑u)
  calc
    _ = Complex.exp (∑' n, groupedBoundaryLogTerm F c (s + ↑u) n) :=
      congrArg Complex.exp (tsum_congr fun n ↦ (groupedBoundaryLogTerm_shift F c s u n).symm)
    _ = ∏' v, heckeEulerFactor F c v (s + ↑u) := by
      rw [tsum_groupedBoundaryLogTerm_eq F c hc (hright u hu)]
      exact exp_tsum_heckePrimePowerLogTerm F c hc (hright u hu)
    _ = _ := (he (hright u hu)).symm

/-- A prime cutoff exponentiates the grouped logarithmic sum together
with the positive contribution of the extra higher powers. -/
theorem heckeEulerPartial_eq_exp_grouped_add_crossover
    (c : Place F → ℂ) (hc : ∀ v, ‖c v‖ ≤ 1) (x : ℝ) {s : ℂ} (hs : 1/2 < s.re) :
    (∏ v ∈ heckePrimeNormCutoff F x, heckeEulerFactor F c v s) =
      Complex.exp (heckePrimePowerLogPartial F c x s + heckeHigherPrimePowerCrossover F c x s) := by
  let P := heckePrimeNormCutoff F x
  let Q := heckeHigherPrimePowerCutoff F x
  let h := heckeHigherPrimePowerLog F c s
  let a (j : Place F × ℕ) := if j.1 ∈ P then h j else 0
  let b (j : Place F × ℕ) := if j ∈ Q then h j else 0
  let d (j : Place F × ℕ) := if j.1 ∈ P ∧ j ∉ Q then h j else 0
  have hs₀ : 0 < s.re := (show (0 : ℝ) < 1/2 by norm_num).trans hs
  have hsH := summable_norm_heckeHigherPrimePowerLog F c hc hs
  have hmask (p : (Place F × ℕ) → Prop) [DecidablePred p] :
      Summable (fun j ↦ if p j then h j else 0) := by
    refine hsH.of_norm_bounded fun j ↦ ?_
    split_ifs
    · exact le_rfl
    · exact (norm_zero (E := ℂ)).le.trans (norm_nonneg _)
  have ha : Summable a := hmask _
  have hb : Summable b := hmask _
  have hd : Summable d := hmask _
  have hsplit : (∑' j, a j) = (∑ j ∈ Q, h j) + heckeHigherPrimePowerCrossover F c x s := by
    have hb' : ∑' j, b j = ∑ j ∈ Q, h j := by
      rw [tsum_eq_sum (s := Q) (fun j hj ↦ by simp [b, hj])]
      exact Finset.sum_congr rfl fun j hj ↦ by simp [b, hj]
    change (∑' j, a j) = (∑ j ∈ Q, h j) + ∑' j, d j
    rw [← hb', ← hb.tsum_add hd]
    apply tsum_congr
    intro j
    by_cases hj : j ∈ Q
    · have hp : j.1 ∈ P := prime_mem_of_higherPower_mem F hj
      simp [a, b, d, hp, hj]
    · simp [a, b, d, hj]
  have hbase : (∑ v ∈ P, ∑' k : ℕ, h (v,k)) = ∑' j, a j := by
    rw [ha.tsum_prod, tsum_eq_sum (s := P)]
    · apply Finset.sum_congr rfl
      intro v hv
      exact tsum_congr fun k ↦ by simp [a, hv]
    · intro v hv
      simp [a, hv]
  have hloc (v : Place F) : (∑' k : ℕ, heckePrimePowerLogTerm F c s (v,k)) =
      c v * (v.asIdeal.absNorm : ℂ) ^ (-s) + ∑' k : ℕ, h (v,k) := by
    rw [(hasSum_heckePrimePowerLogTerm_local F c hc v hs₀).summable.tsum_eq_zero_add]
    have hzero : heckePrimePowerLogTerm F c s (v,0) = c v * (v.asIdeal.absNorm : ℂ) ^ (-s) := by
      simp [heckePrimePowerLogTerm, heckePrimePowerIdeal]
    rw [hzero]
    rfl
  have hEq : (∑ v ∈ P, ∑' k : ℕ, heckePrimePowerLogTerm F c s (v,k)) =
      heckePrimePowerLogPartial F c x s + heckeHigherPrimePowerCrossover F c x s := by
    simp_rw [hloc, Finset.sum_add_distrib]
    rw [hbase, hsplit, heckePrimePowerLogPartial_split, ← add_assoc]
    rfl
  simp_rw [← exp_tsum_heckePrimePowerLogTerm_local F c hc _ hs₀]
  rw [← Complex.exp_sum, hEq]

theorem heckeReciprocalPartial_mul_exp_boundaryLog
    (c : Place F → ℂ) (hc : ∀ v, ‖c v‖ ≤ 1) (x : ℝ) {s l : ℂ} (hs : 1/2 < s.re) :
    heckeReciprocalPartial F c x s * Complex.exp l =
      Complex.exp (l - heckePrimePowerLogPartial F c x s - heckeHigherPrimePowerCrossover F c x s) := by
  rw [heckeReciprocalPartial, Finset.prod_inv_distrib,
    heckeEulerPartial_eq_exp_grouped_add_crossover F c hc x hs, ← Complex.exp_neg, ← Complex.exp_add]
  congr 1
  ring

/-- The oscillatory contribution in the norm-twist expansion has a
uniformly convergent difference series and is of order one over log x. -/
theorem perronBoundaryModel_uniform_bound {D : Set ℂ} (hD : IsCompact D)
    {q : ℂ} (hq : q.re = 1) (hDq : q ∉ D) (hline : D ⊆ {s | s.re = 1}) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ≥ (3 : ℝ),
      let p := ⌈x⌉₊ - 3
      let w := heckeBoundaryLogWeight
      let g (n : ℕ) (s : ℂ) := perronExponentialDifference (n : ℝ) (q - s)
      let d (k : ℕ) (s : ℂ) := (w (p+k) - w (p+k+1)) • g (p+k+2) s
      TendstoUniformlyOn (fun N s ↦ ∑ k ∈ Finset.range N, d k s)
        (fun s ↦ ∑' k, d k s) atTop D ∧
      ∀ s ∈ D, ‖-(w p • g (p+2) s) + (∑' k, d k s)‖ ≤ C / Real.log x := by
  obtain ⟨M, hM, hmodel⟩ := perronExponentialDifference_uniform_bound hD hq hDq hline
  obtain ⟨hw, hw₀, hwl⟩ := abelReciprocalLogWeight
  refine ⟨4 * M, by positivity, fun x hx ↦ ?_⟩
  intro p w g d
  let u (k : ℕ) := (w (p+k) - w (p+k+1)) * M
  have hu := (hasSum_antitone_weight_diff w hw hwl p).mul_right M
  have hmaj (k : ℕ) (s : ℂ) (hs : s ∈ D) : ‖d k s‖ ≤ u k := by
    have hn : 0 ≤ w (p+k) - w (p+k+1) := sub_nonneg.mpr (hw (Nat.le_succ _))
    change ‖(w (p+k) - w (p+k+1)) • g (p+k+2) s‖ ≤ _
    rw [norm_smul, Real.norm_of_nonneg hn]
    exact mul_le_mul_of_nonneg_left (hmodel _ s hs) hn
  refine ⟨tendstoUniformlyOn_tsum_nat hu.summable hmaj, ?_⟩
  intro s hs
  have had := hu.summable.of_nonneg_of_le (fun k ↦ norm_nonneg (d k s)) (fun k ↦ hmaj k s hs)
  have htail : ‖∑' k, d k s‖ ≤ w p * M :=
    (norm_tsum_le_tsum_norm had).trans ((had.tsum_le_tsum (fun k ↦ hmaj k s hs) hu.summable).trans_eq hu.tsum_eq)
  have hprev : ‖w p • g (p+2) s‖ ≤ w p * M := by
    rw [norm_smul, Real.norm_of_nonneg (show 0 ≤ w p from hw₀ p)]
    exact mul_le_mul_of_nonneg_left (hmodel _ s hs) (hw₀ p)
  let y : ℝ := ((p+2 : ℕ) : ℝ)
  have hM₀ : 3 ≤ ⌈x⌉₊ := by exact_mod_cast hx.trans (Nat.le_ceil x)
  have hy : 2 ≤ y := by dsimp [y]; exact_mod_cast (show 2 ≤ p+2 by omega)
  have hyM : y + 1 = (⌈x⌉₊ : ℝ) := by
    rw [show y + 1 = (((p+2+1 : ℕ) : ℝ)) by simp [y]]
    exact_mod_cast (show p+2+1 = ⌈x⌉₊ by dsimp [p]; omega)
  have hxy : x ≤ 2 * y := by linarith [Nat.le_ceil x, hyM]
  have hy₀ : 0 < y := by linarith
  have hl : 0 < Real.log x := Real.log_pos (by linarith)
  have hly : 0 < Real.log y := Real.log_pos (by linarith)
  have hlyx : Real.log x ≤ 2 * Real.log y := by
    have he := Real.log_le_log (by linarith : 0 < x) hxy
    rw [Real.log_mul (by norm_num) hy₀.ne'] at he
    linarith [Real.log_le_log (by norm_num : 0 < (2 : ℝ)) hy]
  have hwle : w p ≤ 2 / Real.log x := by
    change (Real.log y)⁻¹ ≤ _
    rw [inv_eq_one_div, div_le_div_iff₀ hly hl]
    linarith
  calc
    _ ≤ w p * M + w p * M := by
      exact (norm_add_le _ _).trans (add_le_add (by simpa only [norm_neg] using hprev) htail)
    _ ≤ (2 / Real.log x) * M + (2 / Real.log x) * M :=
      add_le_add (mul_le_mul_of_nonneg_right hwle hM) (mul_le_mul_of_nonneg_right hwle hM)
    _ = _ := by ring

local instance : MeasurableSpace (K F) := borel _
local instance : BorelSpace (K F) := ⟨rfl⟩
local instance : MeasurableSpace (Idele F) := borel _
local instance : BorelSpace (Idele F) := ⟨rfl⟩

variable (ν : Measure (K F)) [ν.IsHaarMeasure]
variable (η : Measure (Idele F)) [η.IsHaarMeasure]
variable [∀ v : Place F, MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : Place F, BorelSpace (v.adicCompletion F)ˣ]
  (μ : ∀ v : Place F, Measure (v.adicCompletion F)ˣ)
  [∀ v : Place F, (μ v).IsHaarMeasure] [∀ v : Place F, SigmaFinite (μ v)]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]
variable (hν : IsWeilQuotientMeasure (principalIdeles F) η Measure.count (globalClassMeasure F ν))

include μ hν in
/-- The grouped logarithm at the boundary exponentiates to the normal-form
Hecke continuation. The normalized reciprocal products tend locally
uniformly to one on the same domain. -/
theorem manuscriptFiniteHecke_boundary_normalized_limit (χ : PontryaginDual (IdeleClass F))
    {t : ℝ} (ht : HasHeckeHeight F χ t) :
    let D := heckeBoundaryDomain F χ t
    let c := heckeEulerCoefficient F χ (chosenFiniteUniformizer F)
    ∃ L l : ℂ → ℂ, MeromorphicNFOn L univ ∧
      EqOn L (manuscriptFiniteHeckeEuler F χ) {s | 1 < s.re} ∧
      (∀ s ∈ D, AnalyticAt ℂ L s ∧ L s ≠ 0) ∧
      TendstoLocallyUniformlyOn (heckePrimePowerLogPartial F c) l atTop D ∧
      (∀ s ∈ D, Complex.exp (l s) = L s) ∧
      TendstoLocallyUniformlyOn (fun x s ↦ heckeReciprocalPartial F c x s * L s)
        (fun _ ↦ 1) atTop D := by
  intro D c
  obtain ⟨L, hL, he, _⟩ := exists_manuscriptFiniteHecke_perron_model F ν η μ hν χ ht
  obtain ⟨l, hl⟩ := manuscriptFiniteHecke_boundary_log_locallyUniform F ν η μ hν χ ht
  obtain ⟨B, hB, _, hreg⟩ := manuscriptFiniteHecke_perron_band F ν η μ hν χ ht hL he
  have hc : ∀ v, ‖c v‖ ≤ 1 := norm_heckeEulerCoefficient_le_one F χ _
  have hLD (s : ℂ) (hs : s ∈ D) : AnalyticAt ℂ L s ∧ L s ≠ 0 := by
    have hsre : s.re = 1 := hs.1
    have hlog : 0 < Real.log (B * (|s.im| + 3)) := by
      apply Real.log_pos
      have hh := le_mul_of_one_le_left (show 0 ≤ |s.im| + 3 by positivity) hB
      linarith [abs_nonneg s.im]
    refine hreg s (by rw [hsre]; norm_num) ?_ hs.2
    rw [hsre]
    exact sub_le_self _ (div_nonneg finiteHeckeZeroFreeNumerator_pos.le (by positivity))
  have hEL (s : ℂ) (hs : s ∈ D) : Complex.exp (l s) = L s :=
    exp_heckeBoundaryLog_eq_continuation F c hc hs.1 (hLD s hs).1.continuousAt he (hl.tendsto_at hs)
  refine ⟨L, l, hL, he, hLD, hl, hEL, ?_⟩
  let E (x : ℝ) (s : ℂ) := l s - heckePrimePowerLogPartial F c x s - heckeHigherPrimePowerCrossover F c x s
  have hconst : TendstoLocallyUniformlyOn (fun _ : ℝ ↦ l) l atTop D := by
    apply TendstoUniformlyOn.tendstoLocallyUniformlyOn
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    exact Eventually.of_forall fun _ _ _ ↦ by rwa [dist_self]
  have hcross := ((heckeHigherPrimePowerCrossover_tendstoUniformlyOn F c hc (a := 1) (by norm_num)).mono
    (show D ⊆ {s | 1 ≤ s.re} from fun _ hs ↦ hs.1.ge)).tendstoLocallyUniformlyOn
  have hE : TendstoLocallyUniformlyOn E (fun _ ↦ 0) atTop D := by
    refine ((hconst.sub hl).sub hcross).congr_right ?_
    intro s _
    simp
  have hExp : TendstoLocallyUniformlyOn (fun x s ↦ Complex.exp (E x s)) (fun _ ↦ 1) atTop D := by
    rw [Metric.tendstoLocallyUniformlyOn_iff] at hE ⊢
    intro ε hε s hs
    obtain ⟨δ, hδ, hd⟩ := Metric.continuousAt_iff.mp (Complex.continuous_exp.continuousAt (x := 0)) ε hε
    obtain ⟨S, hS, hbound⟩ := hE δ hδ s hs
    refine ⟨S, hS, hbound.mono fun x hx z hz ↦ ?_⟩
    simpa [dist_comm, Complex.exp_zero] using hd (by simpa [dist_comm] using hx z hz)
  refine hExp.congr (fun x s hs ↦ ?_)
  rw [← hEL s hs]
  exact (heckeReciprocalPartial_mul_exp_boundaryLog F c hc x (by rw [hs.1]; norm_num)).symm

include μ hν in
/-- B.7.2.5. The partial finite Hecke Euler products converge locally
uniformly to the actual finite Hecke continuation on the stated boundary. -/
theorem manuscriptFiniteHecke_eulerPartial_locallyUniform (χ : PontryaginDual (IdeleClass F))
    {t : ℝ} (ht : HasHeckeHeight F χ t) :
    let c := heckeEulerCoefficient F χ (chosenFiniteUniformizer F)
    ∃ L : ℂ → ℂ, MeromorphicNFOn L univ ∧
      EqOn L (manuscriptFiniteHeckeEuler F χ) {s | 1 < s.re} ∧
      TendstoLocallyUniformlyOn (fun x s ↦ ∏ v ∈ heckePrimeNormCutoff F x, heckeEulerFactor F c v s)
        L atTop (heckeBoundaryDomain F χ t) := by
  intro c
  obtain ⟨L, l, hL, he, hreg, _, _, hN⟩ :=
    manuscriptFiniteHecke_boundary_normalized_limit F ν η μ hν χ ht
  have hC : ContinuousOn L (heckeBoundaryDomain F χ t) :=
    fun s hs ↦ (hreg s hs).1.continuousAt.continuousWithinAt
  exact ⟨L, hL, he, heckeEulerPartial_tendstoLocallyUniformlyOn F c hC
    (fun s hs ↦ (hreg s hs).2) hN⟩

include μ hν in
/-- The normalized reciprocal products have the explicit residual,
oscillatory term, and signed higher-power correction from the boundary
tail formula. The oscillatory term is zero in the nontrivial case. -/
theorem manuscriptFiniteHecke_boundary_normalization_formula (χ : PontryaginDual (IdeleClass F))
    {t : ℝ} (ht : HasHeckeHeight F χ t) (D : Set ℂ) (hD : IsCompact D)
    (hsub : D ⊆ heckeBoundaryDomain F χ t) :
    let q : ℂ := 1 + (t : ℂ) * I
    let c := heckeEulerCoefficient F χ (chosenFiniteUniformizer F)
    let g (n : ℕ) (s : ℂ) := if heckeNormOneRestriction F χ = 1 then
      perronExponentialDifference (n : ℝ) (q - s) else 0
    let w := heckeBoundaryLogWeight
    ∃ (L : ℂ → ℂ) (R : ℝ → ℂ → ℂ),
      MeromorphicNFOn L univ ∧ EqOn L (manuscriptFiniteHeckeEuler F χ) {s | 1 < s.re} ∧
      TendstoUniformlyOn (fun x s ↦ heckeReciprocalPartial F c x s * L s) (fun _ ↦ 1) atTop D ∧
      (∀ x ≥ (3 : ℝ), ContinuousOn (R x) D) ∧
      (∀ x ≥ (3 : ℝ), ∀ s ∈ D,
        let p := ⌈x⌉₊ - 3
        let d (k : ℕ) := (w (p+k) - w (p+k+1)) • g (p+k+2) s
        let O := -(w p • g (p+2) s) + ∑' k, d k
        Summable (fun k ↦ ‖d k‖) ∧
        heckeReciprocalPartial F c x s * L s =
          Complex.exp (R x s + O - heckeHigherPrimePowerCrossover F c x s)) ∧
      ∀ ε > (0 : ℝ), ∀ᶠ x : ℝ in atTop, ∀ s ∈ D, ‖R x s‖ < 2 * ε / Real.log x := by
  intro q c g w
  obtain ⟨L, l, hL, he, _, hl, hEL, hN⟩ := manuscriptFiniteHecke_boundary_normalized_limit F ν η μ hν χ ht
  have hline : D ⊆ {s | s.re = 1} := fun _ hs ↦ (hsub hs).1
  have hDq (hω : heckeNormOneRestriction F χ = 1) : q ∉ D := by
    intro hq
    exact ((hsub hq).2.resolve_left (not_not.mpr hω)) rfl
  obtain ⟨l', R, hl', hRc, htail, hRate⟩ :=
    manuscriptFiniteHecke_boundary_log_tails F ν η μ hν χ ht D hD hline hDq
  refine ⟨L, R, hL, he,
    (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hD).mp (hN.mono hsub), hRc, ?_, hRate⟩
  intro x hx s hs p d O
  have heq : l s = l' s := tendsto_nhds_unique (hl.tendsto_at (hsub hs)) (hl'.tendsto_at hs)
  obtain ⟨habs, hEq⟩ := htail x hx s hs
  refine ⟨habs, ?_⟩
  rw [← hEL s (hsub hs), heckeReciprocalPartial_mul_exp_boundaryLog F c
    (norm_heckeEulerCoefficient_le_one F χ _) x (by rw [hline hs]; norm_num), heq, hEq]
  congr 1
  dsimp only [O, d, g, w, p, q]
  abel

end

end Masullo
