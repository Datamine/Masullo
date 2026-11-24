import HeckePerronOneLine

open Complex Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical NumberField Topology

namespace Masullo

noncomputable section

theorem sum_range_adjust_first {Z : Type*} (a : ℕ → Z → ℂ) (A : Z → ℂ)
    (w : ℕ → ℝ) {n : ℕ} (hn : 0 < n) (z : Z) :
    (∑ j ∈ Finset.range n, w j • (a j z - if j = 0 then A z else 0)) =
      (∑ j ∈ Finset.range n, w j • a j z) - w 0 • A z := by
  rw [← Nat.sub_add_cancel hn, Finset.sum_range_succ', Finset.sum_range_succ']
  simp only [Nat.succ_ne_zero, ite_false, sub_zero, ite_true, smul_sub]
  abel

/-- A bounded model for the partial sums separates the weighted series
into the weighted model and a tail controlled by the uniform residual. -/
theorem abelWeighted_model_split {Z : Type*} (D : Set Z) (w : ℕ → ℝ) (a : ℕ → Z → ℂ)
    (A : Z → ℂ) (G : ℕ → Z → ℂ) (hw : Antitone w) (h₀ : ∀ j, 0 ≤ w j)
    (hlim : Tendsto w atTop (𝓝 0)) (hG₀ : ∀ z ∈ D, G 0 z = 0)
    (C : ℝ) (hG : ∀ n z, z ∈ D → ‖G n z‖ ≤ C)
    (hε : ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ z ∈ D,
      ‖(∑ j ∈ Finset.range n, a j z) - A z - G n z‖ ≤ ε) :
    let S (n : ℕ) (z : Z) := ∑ j ∈ Finset.range n, w j • a j z
    let V (n : ℕ) (z : Z) := ∑ j ∈ Finset.range n, w j • (G (j+1) z - G j z)
    ∃ L U : Z → ℂ, TendstoUniformlyOn S L atTop D ∧ TendstoUniformlyOn V U atTop D ∧
      ∀ ε > (0 : ℝ), ∀ᶠ m : ℕ in atTop, ∀ z ∈ D,
        ‖(L z - S m z) - (U z - V m z)‖ ≤ 2 * ε * w m := by
  intro S V
  let g (n : ℕ) (z : Z) := G (n+1) z - G n z
  let d (n : ℕ) (z : Z) := a n z - g n z - if n = 0 then A z else 0
  let R (n : ℕ) (z : Z) := ∑ j ∈ Finset.range n, w j • d j z
  let C₀ (z : Z) := w 0 • A z
  have hg (n : ℕ) (z : Z) (hz : z ∈ D) : (∑ j ∈ Finset.range n, g j z) = G n z := by
    simpa only [g, hG₀ z hz, sub_zero] using Finset.sum_range_sub (G · z) n
  have hd (n : ℕ) (hn : 0 < n) (z : Z) (hz : z ∈ D) :
      (∑ j ∈ Finset.range n, d j z) = (∑ j ∈ Finset.range n, a j z) - A z - G n z := by
    calc
      _ = (∑ j ∈ Finset.range n, (a j z - g j z)) - A z := by
        simpa only [one_smul] using
          sum_range_adjust_first (fun j z ↦ a j z - g j z) A (fun _ ↦ 1) hn z
      _ = _ := by rw [Finset.sum_sub_distrib, hg n z hz]; abel
  obtain ⟨U, hU, _⟩ := abelWeightedSums_uniform D w g hw h₀ hlim C (fun n z hz ↦ by rw [hg n z hz]; exact hG n z hz)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hε 1 zero_lt_one)
  obtain ⟨J, hJ, hbound⟩ := abelWeightedSums_uniform_eventually D w d hw h₀ hlim 1 (max N 1)
    (fun n hn z hz ↦ by
      rw [hd n (zero_lt_one.trans_le ((le_max_right N 1).trans hn)) z hz]
      exact hN n ((le_max_left N 1).trans hn) z hz)
  have hS (n : ℕ) (hn : 0 < n) (z : Z) : S n z = (R n z + V n z) + C₀ z := by
    have h : R n z = (∑ j ∈ Finset.range n, w j • (a j z - g j z)) - C₀ z :=
      sum_range_adjust_first (fun j z ↦ a j z - g j z) A w hn z
    rw [h, show (∑ j ∈ Finset.range n, w j • (a j z - g j z)) = S n z - V n z by
      simp only [smul_sub, Finset.sum_sub_distrib]; rfl]
    abel
  have hc : TendstoUniformlyOn (fun _ : ℕ ↦ C₀) C₀ atTop D := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    exact Eventually.of_forall fun _ _ _ ↦ by rwa [dist_self]
  have hu : TendstoUniformlyOn V U atTop D := hU
  have hl : TendstoUniformlyOn S (fun z ↦ (J z + U z) + C₀ z) atTop D := by
    exact ((hJ.add hu).add hc).congr (by
      filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn z _
      exact (hS n hn z).symm)
  refine ⟨_, U, hl, hu, fun ε hε₀ ↦ ?_⟩
  obtain ⟨m₀, hm₀⟩ := eventually_atTop.mp (hε ε hε₀)
  filter_upwards [eventually_ge_atTop m₀, eventually_gt_atTop (0 : ℕ)] with m hm hm₁ z hz
  have h := hbound m ε (fun n hn z hz ↦ by rw [hd n (hm₁.trans_le hn) z hz]; exact hm₀ n (hm.trans hn) z hz) z hz
  rw [hS m hm₁ z]
  exact (le_of_eq (congrArg norm (show J z + U z + C₀ z - (R m z + V m z + C₀ z) - (U z - V m z) =
    J z - R m z by abel))).trans h

/-- The nonnegative differences of a decreasing weight telescope. -/
theorem hasSum_antitone_weight_diff (w : ℕ → ℝ) (hw : Antitone w)
    (hlim : Tendsto w atTop (𝓝 0)) (p : ℕ) :
    HasSum (fun k ↦ w (p+k) - w (p+k+1)) (w p) := by
  let W (n : ℕ) := w (p+n)
  have hW : Tendsto W atTop (𝓝 0) := hlim.comp
    ((tendsto_add_atTop_nat p).congr fun n ↦ Nat.add_comm n p)
  have hdiff (k : ℕ) : 0 ≤ W k - W (k+1) :=
    sub_nonneg.mpr (hw (Nat.add_le_add_left (Nat.le_succ k) p))
  have hSum (n : ℕ) : (∑ k ∈ Finset.range n, (W k - W (k+1))) = W 0 - W n := by
    calc
      _ = -(∑ k ∈ Finset.range n, (W (k+1) - W k)) := by simp [neg_sub]
      _ = _ := by rw [Finset.sum_range_sub, neg_sub]
  have hd : HasSum (fun k ↦ W k - W (k+1)) (W 0) := by
    apply (hasSum_iff_tendsto_nat_of_nonneg hdiff _).mpr
    simp_rw [hSum]
    simpa using hW.const_sub (W 0)
  simpa only [W, Nat.add_assoc, Nat.add_zero] using hd

/-- The tail of a bounded model has the predecessor term and the
absolutely summable weight-difference series in the manuscript. -/
theorem abelWeighted_model_tail {w : ℕ → ℝ} {G : ℕ → ℂ} {U : ℂ}
    (hw : Antitone w) (h₀ : ∀ j, 0 ≤ w j) (hlim : Tendsto w atTop (𝓝 0))
    (C : ℝ) (hC : ∀ n, ‖G n‖ ≤ C)
    (hU : Tendsto (fun n ↦ ∑ j ∈ Finset.range n, w j • (G (j+1) - G j)) atTop (𝓝 U))
    (p : ℕ) :
    let a (k : ℕ) := (w (p+k) - w (p+k+1)) • G (p+k+1)
    Summable (fun k ↦ ‖a k‖) ∧
      U - (∑ j ∈ Finset.range (p+1), w j • (G (j+1) - G j)) =
        -(w p • G (p+1)) + ∑' k, a k := by
  intro a
  let W (n : ℕ) := w (p+n)
  let V (n : ℕ) := ∑ j ∈ Finset.range n, w j • (G (j+1) - G j)
  let Q (n : ℕ) := W n • G (p+n+1)
  have hW : Tendsto W atTop (𝓝 0) := hlim.comp
    ((tendsto_add_atTop_nat p).congr fun n ↦ Nat.add_comm n p)
  have hdiff (k : ℕ) : 0 ≤ W k - W (k+1) :=
    sub_nonneg.mpr (hw (Nat.add_le_add_left (Nat.le_succ k) p))
  have hd : HasSum (fun k ↦ W k - W (k+1)) (W 0) := by
    simpa only [W, Nat.add_assoc, Nat.add_zero] using hasSum_antitone_weight_diff w hw hlim p
  have ha : Summable (fun k ↦ ‖a k‖) := by
    refine (hd.summable.mul_right C).of_nonneg_of_le (fun _ ↦ norm_nonneg _) fun k ↦ ?_
    have he : a k = (W k - W (k+1)) • G (p+k+1) := by simp only [a, W, Nat.add_assoc]
    rw [he, norm_smul, Real.norm_of_nonneg (hdiff k)]
    exact mul_le_mul_of_nonneg_left (hC _) (hdiff k)
  refine ⟨ha, ?_⟩
  have hQ : Tendsto Q atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hW' : Tendsto (fun n ↦ W n * C) atTop (𝓝 0) := by simpa using hW.mul_const C
    apply squeeze_zero (fun _ ↦ norm_nonneg _) (fun n ↦ ?_) hW'
    change ‖W n • G (p+n+1)‖ ≤ _
    rw [norm_smul, Real.norm_of_nonneg (show 0 ≤ W n from h₀ (p+n))]
    exact mul_le_mul_of_nonneg_left (hC _) (h₀ (p+n))
  have hident (n : ℕ) : V (p+1+n) - V (p+1) =
      Q n - Q 0 + ∑ k ∈ Finset.range n, a k := by
    have hEq (k : ℕ) : w (p+1+k) • (G (p+1+k+1) - G (p+1+k)) =
        (Q (k+1) - Q k) + a k := by
      simp only [Q, a, W, smul_sub, sub_smul]
      have hp : p+1+k = p+k+1 := by omega
      have hq : p+1+k+1 = p+(k+1)+1 := by omega
      rw [hq, hp, show p + (k + 1) = p+k+1 by omega]
      abel
    simp only [V, Finset.sum_range_add _ (p+1) n, add_sub_cancel_left]
    simp_rw [hEq, Finset.sum_add_distrib, Finset.sum_range_sub]
  have h₁ : Tendsto (fun n ↦ V (p+1+n) - V (p+1)) atTop (𝓝 (U - V (p+1))) := by
    exact (hU.comp ((tendsto_add_atTop_nat (p+1)).congr fun n ↦ Nat.add_comm n (p+1))).sub_const _
  have h₂ : Tendsto (fun n ↦ Q n - Q 0 + ∑ k ∈ Finset.range n, a k) atTop
      (𝓝 (-(w p • G (p+1)) + ∑' k, a k)) := by
    simpa only [zero_sub, Q, W, Nat.add_zero] using
      (hQ.sub_const (Q 0)).add ha.of_norm.tendsto_sum_tsum_nat
  exact tendsto_nhds_unique h₁ (h₂.congr fun n ↦ (hident n).symm)

/-- The norm-twist divided differences are uniformly bounded on each
compact part of the one-line that avoids the pole. -/
theorem perronExponentialDifference_uniform_bound {D : Set ℂ} (hD : IsCompact D)
    {q : ℂ} (hqre : q.re = 1) (hDq : q ∉ D) (hline : D ⊆ {s | s.re = 1}) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : ℝ) s, s ∈ D → ‖perronExponentialDifference x (q-s)‖ ≤ C := by
  have hnot (s : ℂ) (hs : s ∈ D) : q ≠ s := by
    intro he
    exact hDq (he.symm ▸ hs)
  have hc : ContinuousOn (fun s : ℂ ↦ (q - s)⁻¹) D :=
    (continuous_const.sub continuous_id).continuousOn.inv₀ (fun s hs ↦ sub_ne_zero.mpr (hnot s hs))
  obtain ⟨C, hC⟩ := hD.exists_bound_of_continuousOn hc
  refine ⟨2 * max 0 C, by positivity, fun x s hs ↦ ?_⟩
  have he : ‖Complex.exp ((Real.log x : ℂ) * (q - s))‖ = 1 := by
    rw [Complex.norm_exp, Complex.mul_re, Complex.sub_re, hqre, hline hs]
    simp
  have hnum : ‖Complex.exp ((Real.log x : ℂ) * (q - s)) - 1‖ ≤ 2 :=
    (norm_sub_le _ _).trans (by rw [he, norm_one]; norm_num)
  rw [perronExponentialDifference, ite_eq_right (sub_ne_zero.mpr (hnot s hs)), div_eq_mul_inv, norm_mul]
  exact mul_le_mul hnum ((hC s hs).trans (le_max_right _ _)) (norm_nonneg _) (by norm_num)

variable (F : Type*) [Field F] [NumberField F]

private abbrev K := normOneIdeleClass F
private abbrev Place := HeightOneSpectrum (𝓞 F)

/-- The reciprocal logarithm at the norm indexed by n + 2. -/
def heckeBoundaryLogWeight (n : ℕ) : ℝ := (Real.log (((n + 2 : ℕ) : ℝ)))⁻¹

private abbrev coeff (c : Place F → ℂ) (n : ℕ) (s : ℂ) : ℂ :=
  LSeries.term (heckeVonMangoldtCoefficient F c) s (n + 2)

private theorem sum_heckeBoundaryCoeff (c : Place F → ℂ) (s : ℂ) (n : ℕ) :
    (∑ j ∈ Finset.range n, coeff F c j s) =
      heckePerronFullSum F c s (((n + 1 : ℕ) : ℝ)) := by
  have h := sum_term_heckeVonMangoldtCoefficient F c s (((n + 2 : ℕ) : ℝ)) (fun _ ↦ 1)
  rw [Nat.ceil_natCast, sum_heckeVonMangoldtCoefficient_from_two] at h
  simp only [one_mul] at h
  rw [h, heckePerronFullSum]
  refine Finset.sum_congr ?_ (fun _ _ ↦ rfl)
  ext j
  simp only [Finset.mem_filter, mem_heckePrimePowerNormCutoff]
  have ht : ((heckePrimePowerIdeal F j).absNorm : ℝ) < ((n + 2 : ℕ) : ℝ) ↔
      ((heckePrimePowerIdeal F j).absNorm : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
    norm_cast
    omega
  exact ⟨fun hj ↦ ⟨by push_cast at hj ⊢; linarith, ht.mp hj⟩, fun hj ↦ ht.mpr hj.2⟩

theorem sum_heckeBoundaryLogWeight (c : Place F → ℂ) (s : ℂ) {x : ℝ} {n : ℕ}
    (hn : ⌈x⌉₊ = n + 2) :
    (∑ j ∈ Finset.range n, heckeBoundaryLogWeight j • coeff F c j s) =
      heckePrimePowerLogPartial F c x s := by
  rw [← sum_reciprocalLog_heckeVonMangoldtCoefficient, hn, sum_heckeVonMangoldtCoefficient_from_two]
  simp only [heckeBoundaryLogWeight, Complex.real_smul, Complex.ofReal_inv]

private theorem analyticAt_boundaryCoeff (c : Place F → ℂ) (n : ℕ) (s : ℂ) :
    AnalyticAt ℂ (coeff F c n) s := by
  have hn : n + 2 ≠ 0 := by omega
  have hn' : ((n + 2 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hn
  have he (z : ℂ) : coeff F c n z =
      heckeVonMangoldtCoefficient F c (n + 2) * (((n + 2 : ℕ) : ℂ) ^ (-z)) := by
    rw [coeff, LSeries.term_of_ne_zero hn, Complex.cpow_neg, div_eq_mul_inv]
  rw [funext he]
  simp_rw [Complex.cpow_def_of_ne_zero hn']
  fun_prop

/-- The finite logarithmic sum over the manuscript's closed norm window
converges uniformly when the strict prefix sums do. -/
theorem heckePrimePowerLogWindow_tendstoUniformlyOn (c : Place F → ℂ) (x : ℝ)
    {D : Set ℂ} {L : ℂ → ℂ}
    (hL : TendstoUniformlyOn (heckePrimePowerLogPartial F c) L atTop D) :
    TendstoUniformlyOn (fun (y : ℝ) s ↦
      ∑ j ∈ (heckePrimePowerNormCutoff F ((⌊y⌋₊ : ℝ) + 1)).filter
          (fun j ↦ x ≤ ((heckePrimePowerIdeal F j).absNorm : ℝ)),
        c j.1 ^ (j.2+1) / ((j.2+1 : ℕ) : ℂ) *
          ((heckePrimePowerIdeal F j).absNorm : ℂ) ^ (-s))
      (fun s ↦ L s - heckePrimePowerLogPartial F c x s) atTop D := by
  let f (y : ℝ) := (⌊y⌋₊ : ℝ) + 1
  let A := heckePrimePowerNormCutoff F x
  let P := heckePrimePowerLogPartial F c
  have hfloor : Tendsto (fun y : ℝ ↦ (⌊y⌋₊ : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp tendsto_nat_floor_atTop
  have hf : Tendsto f atTop atTop := tendsto_atTop_add_const_right atTop (1 : ℝ) hfloor
  have hu : TendstoUniformlyOn (fun y : ℝ ↦ P (f y)) L atTop D :=
    fun u hu ↦ hf.eventually (hL u hu)
  have hc : TendstoUniformlyOn (fun _ : ℝ ↦ P x) (P x) atTop D := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    exact Eventually.of_forall fun _ _ _ ↦ by rwa [dist_self]
  refine (hu.sub hc).congr ?_
  filter_upwards [eventually_ge_atTop x] with y hy s _
  let B := heckePrimePowerNormCutoff F (f y)
  have hAB : A ⊆ B := by
    intro j hj
    apply (mem_heckePrimePowerNormCutoff F).mpr
    exact ((mem_heckePrimePowerNormCutoff F).mp hj).trans_le (hy.trans (Nat.lt_floor_add_one y).le)
  have hset : B.filter (fun j ↦ x ≤ ((heckePrimePowerIdeal F j).absNorm : ℝ)) = B \ A := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_sdiff, A, mem_heckePrimePowerNormCutoff, not_lt]
  change P (f y) s - P x s = _
  rw [show P (f y) s - P x s = _ from eq_sub_iff_add_eq.mpr (Finset.sum_sdiff hAB) |>.symm]
  exact Finset.sum_congr hset.symm fun _ _ ↦ rfl

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

set_option maxHeartbeats 650000 in
include μ hν in
/-- Corrected B.7.2.1 for the actual finite Hecke coefficients.
In the pure norm-twist case the displayed predecessor and series terms
are the oscillatory tail. They vanish in the nontrivial norm-one case. -/
theorem manuscriptFiniteHecke_boundary_log_tails (χ : PontryaginDual (IdeleClass F))
    {t : ℝ} (ht : HasHeckeHeight F χ t) (D : Set ℂ) (hD : IsCompact D)
    (hline : D ⊆ {s | s.re = 1})
    (hDq : heckeNormOneRestriction F χ = 1 → (1 + (t : ℂ) * I) ∉ D) :
    let q : ℂ := 1 + (t : ℂ) * I
    let c := heckeEulerCoefficient F χ (chosenFiniteUniformizer F)
    let g (n : ℕ) (s : ℂ) := if heckeNormOneRestriction F χ = 1 then
      perronExponentialDifference (n : ℝ) (q - s) else 0
    let w := heckeBoundaryLogWeight
    ∃ L : ℂ → ℂ, ∃ R : ℝ → ℂ → ℂ,
      TendstoUniformlyOn (heckePrimePowerLogPartial F c) L atTop D ∧
      (∀ x ≥ (3 : ℝ), ContinuousOn (R x) D) ∧
      (∀ x ≥ (3 : ℝ), ∀ s ∈ D,
        let p := ⌈x⌉₊ - 3
        let d (k : ℕ) := (w (p+k) - w (p+k+1)) • g (p+k+2) s
        Summable (fun k ↦ ‖d k‖) ∧
        L s - heckePrimePowerLogPartial F c x s =
          -(w p • g (p+2) s) + (∑' k, d k) + R x s) ∧
      ∀ ε > (0 : ℝ), ∀ᶠ x : ℝ in atTop, ∀ s ∈ D, ‖R x s‖ < 2 * ε / Real.log x := by
  intro q c g w
  let G (n : ℕ) (s : ℂ) := g (n+1) s
  let a := coeff F c
  let m (x : ℝ) := ⌈x⌉₊ - 2
  let S (n : ℕ) (s : ℂ) := ∑ j ∈ Finset.range n, w j • a j s
  let V (n : ℕ) (s : ℂ) := ∑ j ∈ Finset.range n, w j • (G (j+1) s - G j s)
  obtain ⟨hw, hw₀, hwlim⟩ := abelReciprocalLogWeight
  obtain ⟨L₀, _, _, A, _, _, _, hP⟩ := exists_manuscriptFiniteHecke_perron_model F ν η μ hν χ ht
  have hqre : q.re = 1 := by simp [q, Complex.add_re, Complex.mul_re]
  have hG₀ (s : ℂ) (_ : s ∈ D) : G 0 s = 0 := by
    simp [G, g, perronExponentialDifference]
  have hGB : ∃ C : ℝ, ∀ n s, s ∈ D → ‖G n s‖ ≤ C := by
    by_cases hω : heckeNormOneRestriction F χ = 1
    · obtain ⟨C, _, hC⟩ := perronExponentialDifference_uniform_bound hD hqre (hDq hω) hline
      exact ⟨C, fun n s hs ↦ by simpa only [G, g, hω, ite_true] using hC _ s hs⟩
    · exact ⟨0, fun _ _ _ ↦ by simp [G, g, hω]⟩
  obtain ⟨C, hC⟩ := hGB
  obtain ⟨B, hB⟩ := hD.exists_bound_of_continuousOn Complex.continuous_im.continuousOn
  have hN : Tendsto (fun n : ℕ ↦ (((n+1 : ℕ) : ℝ))) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hr (ε : ℝ) (hε : 0 < ε) : ∀ᶠ n : ℕ in atTop, ∀ s ∈ D,
      ‖(∑ j ∈ Finset.range n, a j s) - A s - G n s‖ ≤ ε := by
    filter_upwards [hN.eventually (hP B 1 ε zero_lt_one hε)] with n hn s hs
    have hAdm : heckePerronAdmissibleCutoff 1 (((n+1 : ℕ) : ℝ)) := by
      exact Or.inl ⟨((n+1 : ℕ) : ℤ), by simp⟩
    have habs : |s.im| ≤ B := by simpa only [Real.norm_eq_abs] using hB s hs
    have hh := (hn hAdm s (hline hs) habs).le
    rw [show (∑ j ∈ Finset.range n, a j s) = _ from sum_heckeBoundaryCoeff F c s n]
    change ‖heckePerronFullSum F c s (((n+1 : ℕ) : ℝ)) - (A s + G n s)‖ ≤ ε at hh
    simpa only [sub_add_eq_sub_sub] using hh
  obtain ⟨L, U, hL, hU, hbound⟩ := abelWeighted_model_split D w a A G hw hw₀ hwlim hG₀ C hC hr
  have hm : Tendsto m atTop atTop := by
    refine tendsto_atTop.mpr fun n ↦ ?_
    filter_upwards [(tendsto_nat_ceil_atTop (α := ℝ)).eventually (eventually_ge_atTop (n+2))] with x hx
    exact Nat.le_sub_of_add_le hx
  have hceil (x : ℝ) (hx : 3 ≤ x) : ⌈x⌉₊ = m x + 2 := by
    have h : 3 ≤ ⌈x⌉₊ := by exact_mod_cast hx.trans (Nat.le_ceil x)
    exact (Nat.sub_add_cancel (by omega : 2 ≤ ⌈x⌉₊)).symm
  have hLog (x : ℝ) (hx : 3 ≤ x) (s : ℂ) : S (m x) s = heckePrimePowerLogPartial F c x s :=
    sum_heckeBoundaryLogWeight F c s (hceil x hx)
  have hLreal : TendstoUniformlyOn (heckePrimePowerLogPartial F c) L atTop D := by
    have hcomp : TendstoUniformlyOn (fun x : ℝ ↦ S (m x)) L atTop D :=
      fun u hu ↦ hm.eventually (hL u hu)
    refine hcomp.congr ?_
    filter_upwards [eventually_ge_atTop (3 : ℝ)] with x hx s _
    exact hLog x hx s
  have hGC (n : ℕ) : ContinuousOn (G n) D := by
    by_cases hω : heckeNormOneRestriction F χ = 1
    · simp only [G, g, hω, ite_true]
      exact (show Continuous (perronExponentialDifference (((n+1 : ℕ) : ℝ))) from
        continuous_iff_continuousAt.mpr fun s ↦ (analyticAt_perronExponentialDifference _ s).continuousAt
        ).comp_continuousOn (continuous_const.sub continuous_id).continuousOn
    · simpa only [G, g, hω, ite_false] using
        (continuousOn_const : ContinuousOn (fun _ : ℂ ↦ (0 : ℂ)) D)
  have hSC (n : ℕ) : ContinuousOn (S n) D := by
    apply continuousOn_finsetSum
    intro j _
    have he : ContinuousOn (a j) D := fun s _ ↦
      (analyticAt_boundaryCoeff F c j s).continuousAt.continuousWithinAt
    exact (continuousOn_const (c := w j)).fun_smul he
  have hVC (n : ℕ) : ContinuousOn (V n) D := by
    apply continuousOn_finsetSum
    intro j _
    exact (continuousOn_const (c := w j)).fun_smul ((hGC (j+1)).fun_sub (hGC j))
  have hLC := hL.continuousOn (Frequently.of_forall hSC)
  have hUC := hU.continuousOn (Frequently.of_forall hVC)
  let R (x : ℝ) (s : ℂ) := (L s - heckePrimePowerLogPartial F c x s) - (U s - V (m x) s)
  refine ⟨L, R, hLreal, ?_, ?_, ?_⟩
  · intro x hx
    have he : heckePrimePowerLogPartial F c x = S (m x) := funext fun s ↦ (hLog x hx s).symm
    exact (show ContinuousOn (fun s ↦ L s - S (m x) s - (U s - V (m x) s)) D from
      (hLC.sub (hSC (m x))).sub (hUC.sub (hVC (m x)))) |>.congr
        (fun s _ ↦ by dsimp only [R]; rw [he])
  · intro x hx s hs p d
    have hp : m x = p + 1 := by
      have hh : 3 ≤ ⌈x⌉₊ := by exact_mod_cast hx.trans (Nat.le_ceil x)
      change ⌈x⌉₊ - 2 = ⌈x⌉₊ - 3 + 1
      omega
    obtain ⟨ha, hEq⟩ := abelWeighted_model_tail (w := w) (G := fun n ↦ G n s)
      hw hw₀ hwlim C (fun n ↦ hC n s hs) (hU.tendsto_at hs) p
    refine ⟨ha, ?_⟩
    have hTail : U s - V (m x) s = -(w p • g (p+2) s) + ∑' k, d k := by
      simpa only [hp, V, G, d, Nat.add_assoc, show (1+1 : ℕ) = 2 by rfl] using hEq
    dsimp only [R]
    rw [hTail]
    abel
  · intro ε hε
    filter_upwards [hm.eventually (hbound (ε / 2) (half_pos hε)), eventually_ge_atTop (3 : ℝ)] with x hx hx₃ s hs
    have hlog : 0 < Real.log x := Real.log_pos (by linarith)
    have hw' : w (m x) ≤ (Real.log x)⁻¹ := by
      dsimp only [w, heckeBoundaryLogWeight]
      rw [← hceil x hx₃]
      exact inv_anti₀ hlog (Real.log_le_log (by linarith) (Nat.le_ceil x))
    have h := hx s hs
    have h' : ‖R x s‖ ≤ 2 * (ε / 2) * w (m x) := by
      change ‖(L s - heckePrimePowerLogPartial F c x s) - (U s - V (m x) s)‖ ≤ _
      rw [← hLog x hx₃ s]
      exact h
    refine (h'.trans (mul_le_mul_of_nonneg_left hw' (by positivity))).trans_lt ?_
    rw [div_eq_mul_inv]
    exact mul_lt_mul_of_pos_right (by linarith) (inv_pos.mpr hlog)

/-- The common convergence domain on the one-line. -/
def heckeBoundaryDomain (χ : PontryaginDual (IdeleClass F)) (t : ℝ) : Set ℂ :=
  {s | s.re = 1 ∧ (heckeNormOneRestriction F χ ≠ 1 ∨ s ≠ 1 + (t : ℂ) * I)}

include μ hν in
/-- The grouped logarithms have a single locally uniform limit on the
full boundary domain. -/
theorem manuscriptFiniteHecke_boundary_log_locallyUniform (χ : PontryaginDual (IdeleClass F))
    {t : ℝ} (ht : HasHeckeHeight F χ t) :
    ∃ L : ℂ → ℂ, TendstoLocallyUniformlyOn
      (heckePrimePowerLogPartial F (heckeEulerCoefficient F χ (chosenFiniteUniformizer F)))
      L atTop (heckeBoundaryDomain F χ t) := by
  let D := heckeBoundaryDomain F χ t
  let q : ℂ := 1 + (t : ℂ) * I
  let P := heckePrimePowerLogPartial F (heckeEulerCoefficient F χ (chosenFiniteUniformizer F))
  have hCompact (S : Set ℂ) (hS : IsCompact S) (hSD : S ⊆ D) :
      ∃ L : ℂ → ℂ, TendstoUniformlyOn P L atTop S := by
    obtain ⟨L, _, hL, _⟩ := manuscriptFiniteHecke_boundary_log_tails F ν η μ hν χ ht S hS
      (fun s hs ↦ (hSD hs).1) (fun hω hq ↦ ((hSD hq).2.resolve_left (not_not.mpr hω)) rfl)
    exact ⟨L, hL⟩
  have hpt (s : ℂ) (hs : s ∈ D) : ∃ l : ℂ, Tendsto (fun x ↦ P x s) atTop (𝓝 l) := by
    obtain ⟨L, hL⟩ := hCompact {s} (isCompact_singleton) (singleton_subset_iff.mpr hs)
    exact ⟨L s, hL.tendsto_at (by simp)⟩
  let L (s : ℂ) := if hs : s ∈ D then (hpt s hs).choose else 0
  refine ⟨L, tendstoLocallyUniformlyOn_of_forall_exists_nhds fun s hs ↦ ?_⟩
  let r : ℝ := if heckeNormOneRestriction F χ = 1 then dist s q / 2 else 1
  have hr : 0 < r := by
    by_cases hω : heckeNormOneRestriction F χ = 1
    · simpa only [r, hω, ite_true] using half_pos (dist_pos.mpr (hs.2.resolve_left (not_not.mpr hω)))
    · simp [r, hω]
  let E := Metric.closedBall s r ∩ {z : ℂ | z.re = 1}
  have hE : IsCompact E := (isCompact_closedBall s r).inter_right
    (isClosed_eq Complex.continuous_re continuous_const)
  have hED : E ⊆ D := by
    intro z hz
    refine ⟨hz.2, ?_⟩
    by_cases hω : heckeNormOneRestriction F χ = 1
    · right
      change z ≠ q
      intro he
      have hd := Metric.mem_closedBall.mp hz.1
      rw [he, dist_comm, show r = dist s q / 2 by simp [r, hω]] at hd
      linarith [dist_pos.mpr (hs.2.resolve_left (not_not.mpr hω))]
    · exact .inl hω
  have hN : E ∈ 𝓝[D] s := by
    filter_upwards [nhdsWithin_le_nhds (Metric.closedBall_mem_nhds s hr), self_mem_nhdsWithin] with z hb hz
    exact ⟨hb, hz.1⟩
  obtain ⟨M, hM⟩ := hCompact E hE hED
  refine ⟨E, hN, hM.congr_right ?_⟩
  intro z hz
  have hzd := hED hz
  exact tendsto_nhds_unique (hM.tendsto_at hz) (by simpa only [L, dite_eq_left hzd] using (hpt z hzd).choose_spec)

include μ hν in
/-- B.7.2.3. The prime terms converge locally uniformly on the one-line
away from the norm-twist pole when that pole is present. -/
theorem manuscriptFiniteHecke_prime_log_locallyUniform (χ : PontryaginDual (IdeleClass F))
    {t : ℝ} (ht : HasHeckeHeight F χ t) :
    ∃ L : ℂ → ℂ, TendstoLocallyUniformlyOn
      (heckePrimeLogPartial F (heckeEulerCoefficient F χ (chosenFiniteUniformizer F)))
      L atTop (heckeBoundaryDomain F χ t) := by
  obtain ⟨L, hL⟩ := manuscriptFiniteHecke_boundary_log_locallyUniform F ν η μ hν χ ht
  exact ⟨_, heckePrimeLogPartial_tendstoLocallyUniformlyOn F _
    (norm_heckeEulerCoefficient_le_one F χ _) (fun _ hs ↦ hs.1.ge) hL⟩

end

end Masullo
