import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Real.Cardinality
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Tactic

open Filter Function MeasureTheory Set
open scoped ENNReal

namespace Masullo

private theorem phase_return_cover {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] (γ : ℝ → G) (hγ : ∀ a b, γ (a + b) = γ a * γ b)
    (U : Set G) (hU : IsOpen U) (h1 : (1 : G) ∈ U) :
    ∃ I : Finset ℝ, ∀ t : ℝ, ∃ i ∈ I, γ (t - i) ∈ U := by
  classical
  let V (i : ℝ) : Set G := {x | (γ i)⁻¹ * x ∈ U}
  have hv i : IsOpen (V i) := hU.preimage (continuous_const.mul continuous_id)
  have hcover : closure (range γ) ⊆ ⋃ i : ℝ, V i := by
    intro x hx
    let W : Set G := {v | v⁻¹ * x ∈ U}
    have hWo : IsOpen W := hU.preimage (continuous_inv.mul continuous_const)
    have hWx : x ∈ W := by simpa [W] using h1
    obtain ⟨y, hyW, ⟨i, rfl⟩⟩ := mem_closure_iff.mp hx W hWo hWx
    exact mem_iUnion.mpr ⟨i, hyW⟩
  obtain ⟨I, hI⟩ := (isClosed_closure.isCompact : IsCompact (closure (range γ))).elim_finite_subcover
    V hv hcover
  refine ⟨I, fun t => ?_⟩
  obtain ⟨i, hi, ht⟩ := mem_iUnion₂.mp (hI (subset_closure (mem_range_self t)))
  refine ⟨i, hi, ?_⟩
  have ht' : (γ i)⁻¹ * γ t ∈ U := ht
  have he : γ t = γ i * γ (t - i) := by rw [← hγ]; congr 1; ring
  simpa [he] using ht'

/-- Returns to an identity neighborhood along a one-parameter subgroup of a
compact group have a positive lower bound for their measure on both half-lines. -/
theorem compactPhase_positiveDensity {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] (γ : ℝ → G) (hγ : ∀ a b, γ (a + b) = γ a * γ b)
    (U : Set G) (hU : IsOpen U) (h1 : (1 : G) ∈ U) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ T in atTop,
      ENNReal.ofReal (c * T) ≤ volume (Icc 0 T ∩ γ ⁻¹' U) ∧
      ENNReal.ofReal (c * T) ≤ volume (Icc (-T) 0 ∩ γ ⁻¹' U) := by
  classical
  obtain ⟨I, hI⟩ := phase_return_cover γ hγ U hU h1
  have hI₀ : 0 < I.card := Finset.card_pos.mpr (by obtain ⟨i, hi, _⟩ := hI 0; exact ⟨i, hi⟩)
  let A : ℝ := 1 + ∑ i ∈ I, |i|
  have hA : 0 ≤ A := by positivity
  have hAi (i : ℝ) (hi : i ∈ I) : |i| ≤ A := by
    have h := Finset.single_le_sum (f := abs) (fun j _ => abs_nonneg j) hi
    dsimp [A]
    linarith
  have hbound (a b : ℝ) :
      ENNReal.ofReal ((b - a) - 2 * A) ≤ (I.card : ℝ≥0∞) * volume (Icc a b ∩ γ ⁻¹' U) := by
    let E := Icc a b ∩ γ ⁻¹' U
    let R (i : ℝ) := (fun x : ℝ => -i + x) ⁻¹' E
    have hsub : Icc (a + A) (b - A) ⊆ ⋃ i ∈ I, R i := by
      intro x hx
      obtain ⟨i, hi, ht⟩ := hI x
      have habs := abs_le.mp (hAi i hi)
      apply mem_iUnion₂.mpr
      refine ⟨i, hi, ?_⟩
      have hl := hx.1
      have hr := hx.2
      exact ⟨⟨by linarith, by linarith⟩, by simpa [sub_eq_add_neg, add_comm] using ht⟩
    calc
      ENNReal.ofReal ((b - a) - 2 * A) = volume (Icc (a + A) (b - A)) := by
        rw [Real.volume_Icc]
        congr 1
        ring
      _ ≤ volume (⋃ i ∈ I, R i) := measure_mono hsub
      _ ≤ ∑ i ∈ I, volume (R i) := measure_biUnion_finset_le I R
      _ = (I.card : ℝ≥0∞) * volume E := by
        simp only [R, MeasureTheory.measure_preimage_add, Finset.sum_const, nsmul_eq_mul]
  let c : ℝ := (2 * I.card)⁻¹
  have hc : 0 < c := by positivity
  refine ⟨c, hc, ?_⟩
  filter_upwards [eventually_ge_atTop (4 * A)] with T hT
  have hT₀ : 0 ≤ T := by linarith
  have hmul : (I.card : ℝ) * (c * T) = T / 2 := by
    dsimp [c]
    field_simp
  have hcast : (I.card : ℝ≥0∞) * ENNReal.ofReal (c * T) = ENNReal.ofReal (T / 2) := by
    rw [show (I.card : ℝ≥0∞) = ENNReal.ofReal (I.card : ℝ) by simp,
      ← ENNReal.ofReal_mul (by positivity), hmul]
  have hhalf : ENNReal.ofReal (T / 2) ≤ ENNReal.ofReal (T - 2 * A) :=
    ENNReal.ofReal_le_ofReal (by linarith)
  have finish {m : ℝ≥0∞} (hm : ENNReal.ofReal (T - 2 * A) ≤ (I.card : ℝ≥0∞) * m) :
      ENNReal.ofReal (c * T) ≤ m := by
    exact (ENNReal.mul_le_mul_iff_right (by exact_mod_cast hI₀.ne') (by simp)).mp
      (hcast.trans_le (hhalf.trans hm))
  exact ⟨finish (by simpa using hbound 0 T), finish (by simpa using hbound (-T) 0)⟩

section Euler

variable {ι : Type*} [Fintype ι]

/-- A finite product of reciprocal unramified Euler factors. The parameters
`a i` are the character values and `q i` are the residue field cardinalities. -/
noncomputable def reciprocalEuler (a : ι → ℂ) (q : ι → ℕ) (z : ℂ) : ℂ :=
  ∏ i, (1 - a i * Complex.exp (-(Real.log (q i) : ℂ) * z))

private noncomputable def phase (q : ι → ℕ) (t : ℝ) (i : ι) : Circle :=
  Circle.exp (-(Real.log (q i)) * t)

omit [Fintype ι] in
private theorem phase_add (q : ι → ℕ) (a b : ℝ) : phase q (a + b) = phase q a * phase q b := by
  funext i
  simp only [phase, mul_add, Circle.exp_add, Pi.mul_apply]

private noncomputable def phaseEuler (a : ι → ℂ) (q : ι → ℕ) (p : ι → Circle) (z : ℂ) : ℂ :=
  ∏ i, (1 - a i * Complex.exp (-(Real.log (q i) : ℂ) * z) * (p i : ℂ))

private theorem phaseEuler_one (a : ι → ℂ) (q : ι → ℕ) (z : ℂ) :
    phaseEuler a q 1 z = reciprocalEuler a q z := by simp [phaseEuler, reciprocalEuler]

private theorem phaseEuler_translate (a : ι → ℂ) (q : ι → ℕ) (z : ℂ) (t : ℝ) :
    phaseEuler a q (phase q t) z = reciprocalEuler a q (z + (t : ℂ) * Complex.I) := by
  apply Finset.prod_congr rfl
  intro i _
  have he : Complex.exp (-(Real.log (q i) : ℂ) * z) *
      Complex.exp ((↑(-(Real.log (q i)) * t) : ℂ) * Complex.I) =
      Complex.exp (-(Real.log (q i) : ℂ) * (z + (t : ℂ) * Complex.I)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp only [phase, Circle.coe_exp, mul_assoc, he]

/-- A strict uniform inequality, expressed without a choice of a value for
the supremum of an empty set. -/
def recurrenceReturns (f : ℂ → ℂ) (K : Set ℂ) (ε : ℝ) : Set ℝ :=
  {t | ∃ b < ε, ∀ z ∈ K, ‖f (z + (t : ℂ) * Complex.I) - f z‖ ≤ b}

theorem recurrenceReturns_iff_sup_lt {f : ℂ → ℂ} (hf : Continuous f) {K : Set ℂ}
    (hK : IsCompact K) (hK₀ : K.Nonempty) (ε t : ℝ) :
    t ∈ recurrenceReturns f K ε ↔
      sSup ((fun z => ‖f (z + (t : ℂ) * Complex.I) - f z‖) '' K) < ε := by
  let g (z : ℂ) := ‖f (z + (t : ℂ) * Complex.I) - f z‖
  have hg : Continuous g := ((hf.comp (continuous_id.add continuous_const)).sub hf).norm
  have hbounded := (hK.image hg).bddAbove
  have hnonempty := hK₀.image g
  constructor
  · rintro ⟨b, hb, h⟩
    exact (csSup_le hnonempty (by rintro _ ⟨z, hz, rfl⟩; exact h z hz)).trans_lt hb
  · intro h
    exact ⟨sSup (g '' K), h, fun z hz => le_csSup hbounded (mem_image_of_mem g hz)⟩

theorem reciprocalEuler_continuous (a : ι → ℂ) (q : ι → ℕ) : Continuous (reciprocalEuler a q) := by
  unfold reciprocalEuler
  fun_prop

theorem reciprocalEuler_inverse_norm (a : ι → ℂ) (q : ι → ℕ) (z : ℂ) :
    ‖(reciprocalEuler a q z)⁻¹‖ = ∏ i, ‖1 - a i * Complex.exp (-(Real.log (q i) : ℂ) * z)‖⁻¹ := by
  simp [reciprocalEuler, norm_inv, norm_prod, Finset.prod_inv_distrib]

private theorem phaseEuler_near_one (a : ι → ℂ) (q : ι → ℕ) {K : Set ℂ} (hK : IsCompact K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ U : Set (ι → Circle), IsOpen U ∧ (1 : ι → Circle) ∈ U ∧
      phase q ⁻¹' U ⊆ recurrenceReturns (reciprocalEuler a q) K ε := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have h : Continuous (fun p : (ι → Circle) × K => phaseEuler a q p.1 p.2.val) := by
    unfold phaseEuler
    fun_prop
  let P : C((ι → Circle), C(K, ℂ)) := ContinuousMap.curry ⟨_, h⟩
  let U := P ⁻¹' Metric.ball (P 1) (ε / 2)
  refine ⟨U, Metric.isOpen_ball.preimage P.continuous, Metric.mem_ball_self (by positivity), ?_⟩
  intro t ht
  refine ⟨ε / 2, by linarith, fun z hz => ?_⟩
  have hd := ContinuousMap.dist_apply_le_dist (f := P (phase q t)) (g := P 1) ⟨z, hz⟩
  have hub : dist (P (phase q t)) (P 1) < ε / 2 := ht
  have hh : dist (phaseEuler a q (phase q t) z) (phaseEuler a q 1 z) ≤ ε / 2 :=
    hd.trans hub.le
  rwa [phaseEuler_translate, phaseEuler_one, dist_eq_norm] at hh

/-- Proposition B.5.3.3. Finite reciprocal Euler products recur uniformly on
every compact set. Each half-line has an eventual linear lower bound for the
measure of return times, which gives positive upper density. -/
theorem reciprocalEuler_recurrence (a : ι → ℂ) (q : ι → ℕ) {K : Set ℂ} (hK : IsCompact K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ T in atTop,
      ENNReal.ofReal (c * T) ≤ volume (Icc 0 T ∩ recurrenceReturns (reciprocalEuler a q) K ε) ∧
      ENNReal.ofReal (c * T) ≤ volume (Icc (-T) 0 ∩ recurrenceReturns (reciprocalEuler a q) K ε) := by
  obtain ⟨U, hU, h1, hsub⟩ := phaseEuler_near_one a q hK hε
  obtain ⟨c, hc, h⟩ := compactPhase_positiveDensity (phase q) (phase_add q) U hU h1
  exact ⟨c, hc, h.mono fun _ ht => ⟨ht.1.trans (measure_mono (inter_subset_inter_right _ hsub)),
    ht.2.trans (measure_mono (inter_subset_inter_right _ hsub))⟩⟩

/-- The vertical translates lie in a compact family of holomorphic maps
on any strip. This verifies the hull hypothesis in the recurrence repair. -/
theorem reciprocalEuler_compact_holomorphic_hull (a : ι → ℂ) (q : ι → ℕ) (S : Set ℂ) :
    ∃ H : Set C(S, ℂ), IsCompact H ∧
      (∀ g ∈ H, ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F S ∧ ∀ z : S, F z = g z) ∧
      (∀ t : ℝ, ∃ g ∈ H, ∀ z : S, g z = reciprocalEuler a q (z + (t : ℂ) * Complex.I)) := by
  have hc : Continuous (fun p : (ι → Circle) × S => phaseEuler a q p.1 p.2.val) := by
    unfold phaseEuler
    fun_prop
  let P : C((ι → Circle), C(S, ℂ)) := ContinuousMap.curry ⟨_, hc⟩
  refine ⟨range P, isCompact_range P.continuous, ?_, ?_⟩
  · rintro _ ⟨p, rfl⟩
    have hd : Differentiable ℂ (phaseEuler a q p) := by
      unfold phaseEuler
      fun_prop
    exact ⟨phaseEuler a q p, (hd.differentiableOn.analyticOnNhd isOpen_univ).mono (subset_univ _),
      fun _ => rfl⟩
  · intro t
    exact ⟨P (phase q t), mem_range_self _, fun z => phaseEuler_translate a q z t⟩

private theorem reciprocalEuler_nonzero_at_some_imaginary (a : ι → ℂ) (q : ι → ℕ)
    (hq : ∀ i, 1 < q i) : ∃ t : ℝ, reciprocalEuler a q ((t : ℂ) * Complex.I) ≠ 0 := by
  classical
  let B (i : ι) : Set ℝ := {t | 1 - a i * Complex.exp
    (-(Real.log (q i) : ℂ) * ((t : ℂ) * Complex.I)) = 0}
  have hc (i : ι) : (B i).Countable := by
    by_cases ha : a i = 0
    · have he : B i = ∅ := by ext t; simp [B, ha]
      rw [he]
      exact countable_empty
    let L (t : ℝ) : ℂ := -(Real.log (q i) : ℂ) * ((t : ℂ) * Complex.I)
    have hlog : (Real.log (q i) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.log_pos (by exact_mod_cast hq i)).ne'
    have hi : Injective L := fun x y h => Complex.ofReal_injective
      (mul_right_cancel₀ Complex.I_ne_zero (mul_left_cancel₀ (neg_ne_zero.mpr hlog) h))
    have hd := (countable_singleton (1 / a i)).preimage_cexp.preimage hi
    apply hd.mono
    intro t ht
    change Complex.exp (L t) = 1 / a i
    apply (eq_div_iff ha).2
    change 1 - a i * Complex.exp (L t) = 0 at ht
    linear_combination -ht
  have hbad : (⋃ i, B i).Countable := countable_iUnion hc
  have ht : ∃ t, t ∉ ⋃ i, B i := by
    by_contra! h
    exact Cardinal.not_countable_real ((eq_univ_of_forall h) ▸ hbad)
  obtain ⟨t, ht⟩ := ht
  refine ⟨t, Finset.prod_ne_zero_iff.mpr fun i _ hi => ?_⟩
  exact ht (mem_iUnion.mpr ⟨i, hi⟩)

/-- A compact translated test set with a common lower bound inherits that
bound, up to a factor of two, on a sequence of recurrent translates. -/
private theorem reciprocalEuler_bounded_inverse_sequence_of_lowerBound
    (a : ι → ℂ) (q : ι → ℕ) {K : Set ℂ} (hK : IsCompact K) (t₀ r : ℝ) (hr : 0 < r)
    (hlower₀ : ∀ z ∈ K, r ≤ ‖reciprocalEuler a q (z + (t₀ : ℂ) * Complex.I)‖) :
    ∃ (N : ℝ) (T : ℤ → ℝ), 0 < N ∧ StrictMono T ∧
      (∀ k, 0 < k → 0 < T k) ∧ (∀ k, k < 0 → T k < 0) ∧
      Tendsto T atTop atTop ∧ Tendsto T atBot atBot ∧
      ∀ k z, z ∈ K →
        reciprocalEuler a q (z + (T k : ℂ) * Complex.I) ≠ 0 ∧
          ‖(reciprocalEuler a q (z + (T k : ℂ) * Complex.I))⁻¹‖ ≤ N := by
  classical
  let Z (z : ℂ) := z + (t₀ : ℂ) * Complex.I
  have hK' : IsCompact (Z '' K) := hK.image (continuous_id.add continuous_const)
  obtain ⟨U, hU, h1, hsub⟩ := phaseEuler_near_one a q
    hK' (ε := r / 2) (by linarith)
  obtain ⟨I, hI⟩ := phase_return_cover (phase q) (phase_add q) U hU h1
  choose i hi hreturn using hI
  let A : ℝ := ∑ j ∈ I, |j|
  have hA : 0 ≤ A := by positivity
  let D := |t₀| + A
  let L := 2 * D + 1
  have hD : 0 ≤ D := add_nonneg (abs_nonneg _) hA
  have hL : 0 < L := by dsimp [L]; linarith
  let T (k : ℤ) := t₀ + (L * (k : ℝ) - i (L * (k : ℝ)))
  have hdist (k : ℤ) : |T k - L * (k : ℝ)| ≤ D := by
    have hi' : |i (L * (k : ℝ))| ≤ A := Finset.single_le_sum (f := abs)
      (fun j _ => abs_nonneg j) (hi _)
    have he : T k - L * (k : ℝ) = t₀ - i (L * (k : ℝ)) := by dsimp [T]; ring
    rw [he]
    exact (abs_sub _ _).trans (add_le_add (le_refl _) hi')
  have hl (k : ℤ) : L * (k : ℝ) - D ≤ T k := by linarith [(abs_le.mp (hdist k)).1]
  have hu (k : ℤ) : T k ≤ L * (k : ℝ) + D := by linarith [(abs_le.mp (hdist k)).2]
  refine ⟨(r / 2)⁻¹, T, by positivity, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply strictMono_int_of_lt_succ
    intro k
    have h := hl (k + 1)
    push_cast at h
    linarith [hu k]
  · intro k hk
    have h : (1 : ℝ) ≤ k := by exact_mod_cast (show (1 : ℤ) ≤ k by omega)
    have hh := mul_le_mul_of_nonneg_left h hL.le
    linarith [hl k]
  · intro k hk
    have h : (k : ℝ) ≤ -1 := by exact_mod_cast (show k ≤ (-1 : ℤ) by omega)
    have hh := mul_le_mul_of_nonneg_left h hL.le
    linarith [hu k]
  · apply tendsto_atTop.mpr
    intro b
    filter_upwards [(tendsto_intCast_atTop_atTop (R := ℝ)).eventually
      (eventually_ge_atTop ((b + D) / L))] with k hk
    have h := (div_le_iff₀ hL).mp hk
    linarith [hl k]
  · apply tendsto_atBot.mpr
    intro b
    filter_upwards [(tendsto_intCast_atBot_iff (R := ℝ)).mpr tendsto_id |>.eventually
      (eventually_le_atBot ((b - D) / L))] with k hk
    have h := (le_div_iff₀ hL).mp hk
    change (k : ℝ) * L ≤ b - D at h
    linarith [hu k]
  · intro k z hzK
    let s := L * (k : ℝ) - i (L * (k : ℝ))
    obtain ⟨b, hb, hs⟩ := hsub (hreturn (L * (k : ℝ)))
    have hz : Z z + (s : ℂ) * Complex.I = z + (T k : ℂ) * Complex.I := by
      dsimp [Z, s, T]
      push_cast
      ring
    have hd := hs (Z z) (mem_image_of_mem Z hzK)
    change ‖reciprocalEuler a q (Z z + (s : ℂ) * Complex.I) - reciprocalEuler a q (Z z)‖ ≤ b at hd
    rw [hz] at hd
    have htri := norm_sub_norm_le (reciprocalEuler a q (Z z))
      (reciprocalEuler a q (z + (T k : ℂ) * Complex.I))
    rw [norm_sub_rev] at htri
    have hbase : r ≤ ‖reciprocalEuler a q (Z z)‖ := hlower₀ z hzK
    have hlower : r / 2 ≤ ‖reciprocalEuler a q (z + (T k : ℂ) * Complex.I)‖ := by linarith
    have hp : 0 < ‖reciprocalEuler a q (z + (T k : ℂ) * Complex.I)‖ :=
      lt_of_lt_of_le (half_pos hr) hlower
    exact ⟨norm_pos_iff.mp hp, by rw [norm_inv]; exact inv_anti₀ (half_pos hr) hlower⟩

/-- Corrected Proposition B.5.3.2. The signs are required for strictly
positive and strictly negative indices, so the central time can avoid a pole. -/
theorem reciprocalEuler_bounded_inverse_sequence (a : ι → ℂ) (q : ι → ℕ)
    (hq : ∀ i, 1 < q i) :
    ∃ (N : ℝ) (T : ℤ → ℝ), 0 < N ∧ StrictMono T ∧
      (∀ k, 0 < k → 0 < T k) ∧ (∀ k, k < 0 → T k < 0) ∧
      Tendsto T atTop atTop ∧ Tendsto T atBot atBot ∧
      ∀ k, reciprocalEuler a q ((T k : ℂ) * Complex.I) ≠ 0 ∧
        ‖(reciprocalEuler a q ((T k : ℂ) * Complex.I))⁻¹‖ ≤ N := by
  obtain ⟨t₀, ht₀⟩ := reciprocalEuler_nonzero_at_some_imaginary a q hq
  have hlower₀ : ∀ z ∈ ({0} : Set ℂ), ‖reciprocalEuler a q ((t₀ : ℂ) * Complex.I)‖ ≤
      ‖reciprocalEuler a q (z + (t₀ : ℂ) * Complex.I)‖ := by
    intro z hz
    rw [mem_singleton_iff.mp hz, zero_add]
  obtain ⟨N, T, hN, hT, hp, hn, hi, hj, hbound⟩ :=
    reciprocalEuler_bounded_inverse_sequence_of_lowerBound a q isCompact_singleton t₀ _
      (norm_pos_iff.mpr ht₀) hlower₀
  exact ⟨N, T, hN, hT, hp, hn, hi, hj, fun k => by
    simpa only [zero_add] using hbound k 0 (mem_singleton 0)⟩

/-- Normalizing each nonzero coefficient to a unit phase lets one choose a
height at which the original Euler product has no zeros at any real part. -/
private theorem reciprocalEuler_nonzero_on_some_horizontalLine (a : ι → ℂ) (q : ι → ℕ)
    (hq : ∀ i, 1 < q i) :
    ∃ t : ℝ, ∀ σ : ℝ, reciprocalEuler a q ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
  let b (i : ι) := a i / (‖a i‖ : ℂ)
  obtain ⟨t, ht⟩ := reciprocalEuler_nonzero_at_some_imaginary b q hq
  refine ⟨t, fun σ => Finset.prod_ne_zero_iff.mpr ?_⟩
  intro i hi hzero
  let L : ℝ := Real.log (q i)
  let p := Complex.exp (-(L : ℂ) * ((t : ℂ) * Complex.I))
  let R := Real.exp (-L * σ)
  have hp : ‖p‖ = 1 := by
    have he : (-(L : ℂ) * ((t : ℂ) * Complex.I)) = ((-L * t : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [show p = Complex.exp _ from rfl, he, Complex.norm_exp_ofReal_mul_I]
  have hR : 0 < R := Real.exp_pos _
  have he : Complex.exp (-(L : ℂ) * ((σ : ℂ) + (t : ℂ) * Complex.I)) = (R : ℂ) * p := by
    rw [mul_add, Complex.exp_add]
    simp only [R, p, Complex.ofReal_exp, Complex.ofReal_mul, Complex.ofReal_neg]
  change 1 - a i * Complex.exp (-(L : ℂ) * ((σ : ℂ) + (t : ℂ) * Complex.I)) = 0 at hzero
  rw [he, mul_left_comm] at hzero
  have hprod : (R : ℂ) * (a i * p) = 1 := (sub_eq_zero.mp hzero).symm
  have hnorm := congrArg norm hprod
  rw [norm_mul, norm_mul, hp, mul_one, Complex.norm_real, Real.norm_of_nonneg hR.le, norm_one] at hnorm
  have hR₀ : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  have hphase : a i * p = (‖a i‖ : ℂ) := by
    apply mul_left_cancel₀ hR₀
    rw [hprod]
    exact_mod_cast hnorm.symm
  apply ht
  apply Finset.prod_eq_zero hi
  have ha₀ : (‖a i‖ : ℂ) ≠ 0 := by
    exact_mod_cast (show ‖a i‖ ≠ 0 by intro h; rw [h, mul_zero] at hnorm; norm_num at hnorm)
  change 1 - a i / (‖a i‖ : ℂ) * p = 0
  rw [div_mul_eq_mul_div, hphase, div_self ha₀, sub_self]

/-- Corrected Lemma 7.1.1.1. A single sequence of ordinates avoids all poles
and bounds the inverse Euler product uniformly across a closed real segment. -/
theorem reciprocalEuler_bounded_inverse_strip_sequence (a : ι → ℂ) (q : ι → ℕ)
    (hq : ∀ i, 1 < q i) {α β : ℝ} (hαβ : α ≤ β) :
    ∃ (N : ℝ) (T : ℤ → ℝ), 0 < N ∧ StrictMono T ∧
      (∀ k, 0 < k → 0 < T k) ∧ (∀ k, k < 0 → T k < 0) ∧
      Tendsto T atTop atTop ∧ Tendsto T atBot atBot ∧
      ∀ k σ, σ ∈ Icc α β →
        reciprocalEuler a q ((σ : ℂ) + (T k : ℂ) * Complex.I) ≠ 0 ∧
          ‖(reciprocalEuler a q ((σ : ℂ) + (T k : ℂ) * Complex.I))⁻¹‖ ≤ N := by
  obtain ⟨t₀, ht₀⟩ := reciprocalEuler_nonzero_on_some_horizontalLine a q hq
  let K := Complex.ofReal '' Icc α β
  have hK : IsCompact K := isCompact_Icc.image Complex.continuous_ofReal
  have hK₀ : K.Nonempty := ⟨α, ⟨α, ⟨le_rfl, hαβ⟩, rfl⟩⟩
  let g (z : ℂ) := ‖reciprocalEuler a q (z + (t₀ : ℂ) * Complex.I)‖
  have hg : Continuous g := by unfold g reciprocalEuler; fun_prop
  obtain ⟨z, hz, hmin⟩ := hK.exists_isMinOn hK₀ hg.continuousOn
  obtain ⟨σ, hσ, rfl⟩ := hz
  obtain ⟨N, T, hN, hT, hp, hn, htop, hbot, hbound⟩ :=
    reciprocalEuler_bounded_inverse_sequence_of_lowerBound a q hK t₀ (g σ)
      (norm_pos_iff.mpr (ht₀ σ)) (fun z hz => hmin hz)
  exact ⟨N, T, hN, hT, hp, hn, htop, hbot,
    fun k σ hσ => hbound k σ (mem_image_of_mem Complex.ofReal hσ)⟩

/-- For the trivial coefficient and even one Euler factor the central time
forced by the printed signs is a pole of the inverse product. -/
theorem reciprocalEuler_printed_at_zero_obstruction (T : ℤ → ℝ)
    (hplus : ∀ k, 0 ≤ k → 0 ≤ T k) (hminus : ∀ k, k ≤ 0 → T k ≤ 0) :
    reciprocalEuler (fun _ : Unit => (1 : ℂ)) (fun _ => 2) ((T 0 : ℂ) * Complex.I) = 0 := by
  have h0 : T 0 = 0 := le_antisymm (hminus 0 le_rfl) (hplus 0 le_rfl)
  simp [h0, reciprocalEuler]

end Euler

end Masullo
