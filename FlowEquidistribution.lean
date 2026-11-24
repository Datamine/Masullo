import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.Localization.Module
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.ContinuousMap.Compact
import MeasureFoundations

open Filter Function Set MeasureTheory Topology
open scoped Interval NNReal ENNReal

namespace Masullo

noncomputable section

variable {G : Type*} [MetricSpace G] [CompactSpace G] [CommGroup G] [IsTopologicalGroup G]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

private def flowAverage (γ : Multiplicative ℝ →* G) (f : C(G, E)) (a b : ℝ) (x : G) : E :=
  (b - a)⁻¹ • ∫ t in a..b, f (x * γ (Multiplicative.ofAdd t))

omit [IsTopologicalGroup G] [CompleteSpace E] in
private theorem flowAverage_shift (γ : Multiplicative ℝ →* G) (hγ : Continuous γ)
    (f : C(G, E)) {a b : ℝ} (hab : a < b) (s : ℝ) :
    ‖flowAverage γ f a b (γ (Multiplicative.ofAdd s)) - flowAverage γ f a b 1‖ ≤
      (2 * ‖f‖ * |s|) / (b - a) := by
  let h : ℝ → E := fun t => f (γ (Multiplicative.ofAdd t))
  have hh : Continuous h := f.continuous.comp hγ
  have heq (t : ℝ) : f (γ (Multiplicative.ofAdd s) * γ (Multiplicative.ofAdd t)) = h (t + s) := by
    change f (γ (Multiplicative.ofAdd s) * γ (Multiplicative.ofAdd t)) =
      f (γ (Multiplicative.ofAdd (t + s)))
    rw [← map_mul, add_comm]
    rfl
  have hd : (∫ t in a + s..b + s, h t) - (∫ t in a..b, h t) =
      (∫ t in b..b + s, h t) - (∫ t in a..a + s, h t) := by
    have h₁ := intervalIntegral.integral_add_adjacent_intervals
      (hh.intervalIntegrable (μ := volume) a (a+s)) (hh.intervalIntegrable (μ := volume) (a+s) (b+s))
    have h₂ := intervalIntegral.integral_add_adjacent_intervals
      (hh.intervalIntegrable (μ := volume) a b) (hh.intervalIntegrable (μ := volume) b (b+s))
    rw [← h₂] at h₁
    apply sub_eq_sub_iff_add_eq_add.mpr
    simpa only [add_comm] using h₁
  have hb (r : ℝ) : ‖∫ t in r..r + s, h t‖ ≤ ‖f‖ * |s| := by
    convert intervalIntegral.norm_integral_le_of_norm_le_const
      (a := r) (b := r+s) (fun t _ => f.norm_coe_le_norm (γ (Multiplicative.ofAdd t))) using 1
    ring_nf
  unfold flowAverage
  simp only [one_mul, heq, intervalIntegral.integral_comp_add_right, ← smul_sub,
    norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos (sub_pos.mpr hab)]
  change (b-a)⁻¹ * ‖(∫ t in a+s..b+s, h t) - (∫ t in a..b, h t)‖ ≤ _
  rw [hd, div_eq_mul_inv, mul_comm (2 * ‖f‖ * |s|)]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (sub_nonneg.mpr hab.le))
  calc
    _ ≤ ‖∫ t in b..b+s, h t‖ + ‖∫ t in a..a+s, h t‖ := norm_sub_le _ _
    _ ≤ ‖f‖ * |s| + ‖f‖ * |s| := add_le_add (hb b) (hb a)
    _ = _ := by ring

omit [CompleteSpace E] in
private theorem flowAverage_oscillation (γ : Multiplicative ℝ →* G) (hγ : Continuous γ)
    (hd : DenseRange γ) (f : C(G, E)) {ε : ℝ} (hε : 0 < ε) :
    ∃ L : ℝ, 0 < L ∧ ∀ a b, L ≤ b - a → ∀ x,
      ‖flowAverage γ f a b x - flowAverage γ f a b 1‖ ≤ ε := by
  classical
  have hcont : Continuous (fun p : G × G => f (p.1 * p.2)) :=
    f.continuous.comp (continuous_fst.mul continuous_snd)
  obtain ⟨δ, hδ, hδ'⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous hcont) (ε/2) (by positivity)
  let U (s : ℝ) : Set G := Metric.ball (γ (Multiplicative.ofAdd s)) δ
  have hcover : (univ : Set G) ⊆ ⋃ s, U s := by
    intro x _
    obtain ⟨s, hs⟩ := hd.exists_dist_lt x hδ
    exact mem_iUnion.mpr ⟨s.toAdd, hs⟩
  obtain ⟨S, hS⟩ := isCompact_univ.elim_finite_subcover U (fun _ => Metric.isOpen_ball) hcover
  let C := ∑ s ∈ S, 2 * ‖f‖ * |s|
  have hC : 0 ≤ C := Finset.sum_nonneg fun _ _ => by positivity
  let L := 1 + C / (ε/2)
  have hL : 0 < L := by positivity
  refine ⟨L, hL, fun a b hab x => ?_⟩
  have hab' : a < b := sub_pos.mp (hL.trans_le hab)
  obtain ⟨s, hs⟩ := mem_iUnion.mp (hS (mem_univ x))
  obtain ⟨hsS, hs⟩ := mem_iUnion.mp hs
  have hnear (y : G) : ‖f (x * y) - f (γ (Multiplicative.ofAdd s) * y)‖ ≤ ε/2 := by
    rw [← dist_eq_norm]
    apply (hδ' (a := (x,y)) (b := (γ (Multiplicative.ofAdd s),y)) ?_).le
    rw [Prod.dist_eq, dist_self, max_eq_left dist_nonneg]
    exact hs
  have hleft (z : G) : Continuous (fun t : ℝ => f (z * γ (Multiplicative.ofAdd t))) :=
    f.continuous.comp (continuous_const.mul hγ)
  have hx : ‖flowAverage γ f a b x - flowAverage γ f a b (γ (Multiplicative.ofAdd s))‖ ≤ ε/2 := by
    unfold flowAverage
    rw [← smul_sub, ← intervalIntegral.integral_sub ((hleft x).intervalIntegrable (μ := volume) a b)
      ((hleft _).intervalIntegrable (μ := volume) a b), norm_smul, Real.norm_eq_abs,
      abs_inv, abs_of_pos (sub_pos.mpr hab')]
    have hI := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := a) (b := b) (fun t _ => hnear (γ (Multiplicative.ofAdd t)))
    rw [abs_of_pos (sub_pos.mpr hab')] at hI
    calc
      _ ≤ (b-a)⁻¹ * ((ε/2) * (b-a)) := mul_le_mul_of_nonneg_left hI (by positivity)
      _ = ε/2 := by field_simp [sub_ne_zero.mpr (ne_of_gt hab')]
  have hCs : 2 * ‖f‖ * |s| ≤ C :=
    Finset.single_le_sum (f := fun t => 2 * ‖f‖ * |t|) (fun _ _ => by positivity) hsS
  have hL' : C ≤ (ε/2) * (b-a) := by
    have hC' : C/(ε/2) ≤ b-a := by dsimp [L] at hab; linarith
    have := (div_le_iff₀ (show 0 < ε/2 by positivity)).mp hC'
    rwa [mul_comm] at this
  have hy : ‖flowAverage γ f a b (γ (Multiplicative.ofAdd s)) - flowAverage γ f a b 1‖ ≤ ε/2 :=
    (flowAverage_shift γ hγ f hab' s).trans ((div_le_iff₀ (sub_pos.mpr hab')).mpr (hCs.trans hL'))
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans ((add_le_add hx hy).trans_eq (by ring))

variable [MeasurableSpace G] [BorelSpace G]

private theorem flowAverage_integral (γ : Multiplicative ℝ →* G) (hγ : Continuous γ)
    (μ : Measure G) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant] (f : C(G, E))
    {a b : ℝ} (hab : a < b) :
    ∫ x, flowAverage γ f a b x ∂μ = ∫ x, f x ∂μ := by
  let k : ℝ → G → E := fun t x => f (γ (Multiplicative.ofAdd t) * x)
  have hk : Continuous (uncurry k) :=
    f.continuous.comp ((hγ.comp continuous_fst).mul continuous_snd)
  letI : IsFiniteMeasure (volume.restrict (uIoc a b)) :=
    ⟨by simp [uIoc_of_le hab.le]⟩
  have hki : Integrable (uncurry k) ((volume.restrict (uIoc a b)).prod μ) :=
    Integrable.of_bound hk.aestronglyMeasurable ‖f‖ (Eventually.of_forall fun x => f.norm_coe_le_norm _)
  have eq (x : G) : flowAverage γ f a b x = (b-a)⁻¹ • ∫ t in a..b, k t x := by
    simp only [flowAverage, k, mul_comm]
  have hK (t : ℝ) : ∫ x, k t x ∂μ = ∫ x, f x ∂μ :=
    integral_mul_left_eq_self _ _
  simp_rw [eq]
  rw [integral_smul, ← intervalIntegral_integral_swap hki]
  simp only [hK, intervalIntegral.integral_const, smul_smul]
  rw [inv_mul_cancel₀ (sub_ne_zero.mpr (ne_of_gt hab)), one_smul]

/-- On the closure of a real flow, averages of continuous functions converge
to their Haar integrals, for any intervals whose lengths tend to infinity. -/
theorem denseFlow_tendsto_average (γ : Multiplicative ℝ →* G) (hγ : Continuous γ)
    (hd : DenseRange γ) (μ : Measure G) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    (f : C(G, E)) {a b : ℝ → ℝ} (hlen : Tendsto (fun t => b t - a t) atTop atTop) :
    Tendsto (fun T => (b T - a T)⁻¹ • ∫ t in a T..b T, f (γ (Multiplicative.ofAdd t)))
      atTop (𝓝 (∫ x, f x ∂μ)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨L, hL, hosc⟩ := flowAverage_oscillation γ hγ hd f (show 0 < ε/2 by positivity)
  filter_upwards [hlen.eventually_ge_atTop L] with T hT
  let A := flowAverage γ f (a T) (b T)
  have hab : a T < b T := sub_pos.mp (hL.trans_le hT)
  have hAint : Integrable A μ := by
    let k : ℝ → G → E := fun t x => f (x * γ (Multiplicative.ofAdd t))
    have hk : Continuous (uncurry k) :=
      f.continuous.comp (continuous_snd.mul (hγ.comp continuous_fst))
    letI : IsFiniteMeasure (volume.restrict (Ioc (a T) (b T))) :=
      ⟨by simp⟩
    have hkInt : Integrable (uncurry k) ((volume.restrict (Ioc (a T) (b T))).prod μ) :=
      Integrable.of_bound hk.aestronglyMeasurable ‖f‖ (Eventually.of_forall fun x => f.norm_coe_le_norm _)
    change Integrable (fun x => (b T - a T)⁻¹ • ∫ t in a T..b T, k t x) μ
    simp_rw [intervalIntegral.integral_of_le hab.le]
    exact hkInt.integral_prod_right.smul ((b T - a T)⁻¹)
  have hmean : ∫ x, A x ∂μ = ∫ x, f x ∂μ :=
    flowAverage_integral γ hγ μ f hab
  have hbound := MeasureTheory.norm_integral_le_of_norm_le_const (μ := μ)
    (Eventually.of_forall (hosc _ _ hT))
  rw [integral_sub hAint (integrable_const (A 1)), hmean, integral_const] at hbound
  simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul, mul_one] at hbound
  simpa [dist_eq_norm, A, flowAverage, one_mul, norm_sub_rev] using hbound.trans_lt (half_lt_self hε)

/-- Continuous minorants of a bounded real function, converging at every continuity point. -/
private theorem exists_continuous_minorants {X : Type*} [MetricSpace X]
    (f : X → ℝ) (M : ℝ) (hf : ∀ x, |f x| ≤ M) :
    ∃ u : ℕ → C(X, ℝ), (∀ n x, -M ≤ u n x ∧ u n x ≤ f x) ∧
      ∀ x, ContinuousAt f x → Tendsto (fun n => u n x) atTop (𝓝 (f x)) := by
  let S (n : ℕ) (x : X) := range (fun y => f y + (n : ℝ) * dist x y)
  let v (n : ℕ) (x : X) := sInf (S n x)
  have hlow (n : ℕ) (x : X) : ∀ z ∈ S n x, -M ≤ z := by
    rintro _ ⟨y, rfl⟩
    have h := (abs_le.mp (hf y)).1
    exact h.trans (le_add_of_nonneg_right (by positivity))
  have hB (n : ℕ) (x : X) : BddBelow (S n x) := ⟨-M, hlow n x⟩
  have hne (n : ℕ) (x : X) : (S n x).Nonempty := ⟨_, mem_range_self x⟩
  have hv (n : ℕ) (x : X) : v n x ≤ f x := by
    simpa using csInf_le (hB n x) (mem_range_self x)
  have hdiff (n : ℕ) (x y : X) : v n x - v n y ≤ (n : ℝ) * dist x y := by
    apply sub_le_iff_le_add.mpr
    rw [add_comm, ← sub_le_iff_le_add]
    apply le_csInf (hne n y)
    rintro _ ⟨z, rfl⟩
    have h₁ : v n x ≤ f z + (n : ℝ) * dist x z :=
      csInf_le (hB n x) (mem_range_self z)
    have h₂ := mul_le_mul_of_nonneg_left (dist_triangle x y z) (Nat.cast_nonneg n)
    rw [mul_add] at h₂
    linarith
  have hcont (n : ℕ) : Continuous (v n) := by
    apply LipschitzWith.continuous (K := (n : ℝ≥0))
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [Real.dist_eq, abs_le]
    change -((n : ℝ) * dist x y) ≤ v n x - v n y ∧
      v n x - v n y ≤ (n : ℝ) * dist x y
    have hyx := hdiff n y x
    rw [dist_comm y x] at hyx
    exact ⟨by linarith, hdiff n x y⟩
  refine ⟨fun n => ⟨v n, hcont n⟩, fun n x => ⟨le_csInf (hne n x) (hlow n x), hv n x⟩, ?_⟩
  intro x hx
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hnear⟩ := Metric.continuousAt_iff.mp hx (ε / 2) (by positivity)
  filter_upwards [tendsto_natCast_atTop_atTop.eventually_ge_atTop (2 * M / δ)] with n hn
  have h₀ : f x - ε / 2 ≤ v n x := by
    apply le_csInf (hne n x)
    rintro _ ⟨y, rfl⟩
    by_cases hy : dist y x < δ
    · have h := (abs_lt.mp (show |f y - f x| < ε / 2 by simpa [Real.dist_eq] using hnear hy)).1
      have hpos : 0 ≤ (n : ℝ) * dist x y := by positivity
      linarith
    · have hδn : 2 * M ≤ (n : ℝ) * δ := (div_le_iff₀ hδ).mp hn
      have hdist := mul_le_mul_of_nonneg_left (le_of_not_gt hy) (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
      rw [dist_comm y x] at hdist
      linarith [(abs_le.mp (hf y)).1, (abs_le.mp (hf x)).2]
  change dist (v n x) (f x) < ε
  rw [Real.dist_eq, abs_lt]
  exact ⟨by linarith, by linarith [hv n x]⟩

omit [CompactSpace G] [CommGroup G] [IsTopologicalGroup G] in
private theorem aeStronglyMeasurable_of_ae_continuousAt
    (μ : Measure G) {f : G → ℂ} (hf : ∀ᵐ x ∂μ, ContinuousAt f x) :
    AEStronglyMeasurable f μ := by
  classical
  let S := {x | ContinuousAt f x}
  have hs : MeasurableSet S := measurableSet_of_continuousAt f
  have hc : ContinuousOn f S := fun _ hx => hx.continuousWithinAt
  have hm : Measurable (fun x : S => f x.val) :=
    (continuousOn_iff_continuous_domRestrict.mp hc).measurable
  obtain ⟨g, hg, heq⟩ := (MeasurableEmbedding.subtype_coe hs).exists_measurable_extend hm
    (fun _ => ⟨0⟩)
  apply hg.aestronglyMeasurable.congr
  filter_upwards [hf] with x hx
  exact congrFun heq (⟨x, hx⟩ : S)

private theorem intervalIntegrable_of_ae_bound {V : Type*} [NormedAddCommGroup V]
    {f : ℝ → V} (hf : AEStronglyMeasurable f volume) (M : ℝ) (hM : ∀ t, ‖f t‖ ≤ M)
    (a b : ℝ) : IntervalIntegrable f volume a b := by
  rw [intervalIntegrable_iff]
  haveI : IsFiniteMeasure (volume.restrict (Ι a b)) := ⟨by simp⟩
  exact Integrable.of_bound hf.restrict M (Eventually.of_forall hM)

private theorem denseFlow_eventually_average_gt (γ : Multiplicative ℝ →* G) (hγ : Continuous γ)
    (hd : DenseRange γ) (μ : Measure G) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    (f : G → ℝ) (M : ℝ) (hM : ∀ x, |f x| ≤ M) (hc : ∀ᵐ x ∂μ, ContinuousAt f x)
    (ht : ∀ a b : ℝ, IntervalIntegrable (fun t : ℝ => f (γ (Multiplicative.ofAdd t))) volume a b)
    {a b : ℝ → ℝ} (hlen : Tendsto (fun t => b t - a t) atTop atTop) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ T in atTop, (∫ x, f x ∂μ) - ε <
      (b T - a T)⁻¹ * ∫ t in a T..b T, f (γ (Multiplicative.ofAdd t)) := by
  obtain ⟨u, hu, huc⟩ := exists_continuous_minorants f M hM
  have hmeas (n : ℕ) : AEStronglyMeasurable (u n) μ := (u n).continuous.aestronglyMeasurable
  have hconv : Tendsto (fun n => ∫ x, u n x ∂μ) atTop (𝓝 (∫ x, f x ∂μ)) :=
    tendsto_integral_of_dominated_convergence (fun _ => M) hmeas (integrable_const _) (fun n =>
      Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_le]
        exact ⟨(hu n x).1, (hu n x).2.trans (abs_le.mp (hM x)).2⟩)
      (hc.mono fun x hx => huc x hx)
  obtain ⟨n, hn⟩ := ((Metric.tendsto_nhds.mp hconv) _ (show 0 < ε / 2 by positivity)).exists
  have hlim := Metric.tendsto_nhds.mp (denseFlow_tendsto_average γ hγ hd μ (u n) hlen)
    (ε / 2) (by positivity)
  filter_upwards [hlim, hlen.eventually_ge_atTop 1] with T hT hlength
  have hab : a T ≤ b T := by linarith
  have huInt : IntervalIntegrable (fun t : ℝ => u n (γ (Multiplicative.ofAdd t)))
      volume (a T) (b T) := ((u n).continuous.comp hγ).intervalIntegrable _ _
  have hlo := intervalIntegral.integral_mono_on hab huInt (ht (a T) (b T))
    (fun t _ => (hu n (γ (Multiplicative.ofAdd t))).2)
  have hb := mul_le_mul_of_nonneg_left hlo (inv_nonneg.mpr (sub_nonneg.mpr hab))
  rw [Real.dist_eq, abs_lt] at hn hT
  rw [smul_eq_mul] at hT
  linarith [hn.1, hT.1]

private theorem denseFlow_tendsto_real_average_ae_continuous (γ : Multiplicative ℝ →* G)
    (hγ : Continuous γ) (hd : DenseRange γ) (μ : Measure G) [IsProbabilityMeasure μ]
    [μ.IsMulLeftInvariant] (f : G → ℝ) (M : ℝ) (hM : ∀ x, |f x| ≤ M)
    (hc : ∀ᵐ x ∂μ, ContinuousAt f x)
    (ht : ∀ a b : ℝ, IntervalIntegrable (fun t : ℝ => f (γ (Multiplicative.ofAdd t))) volume a b)
    {a b : ℝ → ℝ} (hlen : Tendsto (fun t => b t - a t) atTop atTop) :
    Tendsto (fun T => (b T - a T)⁻¹ * ∫ t in a T..b T, f (γ (Multiplicative.ofAdd t)))
      atTop (𝓝 (∫ x, f x ∂μ)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hneg := denseFlow_eventually_average_gt γ hγ hd μ (fun x => -f x) M
    (fun x => by simpa only [abs_neg] using hM x) (hc.mono fun _ hx => hx.neg)
    (fun x y => (ht x y).neg) hlen hε
  filter_upwards [denseFlow_eventually_average_gt γ hγ hd μ f M hM hc ht hlen hε, hneg]
    with T h₁ h₂
  rw [integral_neg f, intervalIntegral.integral_neg, mul_neg] at h₂
  rw [Real.dist_eq, abs_lt]
  exact ⟨by linarith, by linarith⟩

/-- Corrected Kronecker–Weyl averaging for bounded tests continuous Haar-almost everywhere.
The time trace is required to be almost everywhere measurable for Lebesgue measure. -/
theorem denseFlow_tendsto_average_ae_continuous
    (γ : Multiplicative ℝ →* G) (hγ : Continuous γ) (hd : DenseRange γ)
    (μ : Measure G) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    (f : G → ℂ) (M : ℝ) (hM : ∀ x, ‖f x‖ ≤ M) (hc : ∀ᵐ x ∂μ, ContinuousAt f x)
    (ht : AEStronglyMeasurable (fun t : ℝ => f (γ (Multiplicative.ofAdd t))) volume)
    {a b : ℝ → ℝ} (hlen : Tendsto (fun t => b t - a t) atTop atTop) :
    Tendsto (fun T => (b T - a T)⁻¹ • ∫ t in a T..b T, f (γ (Multiplicative.ofAdd t)))
      atTop (𝓝 (∫ x, f x ∂μ)) := by
  have hf : Integrable f μ := Integrable.of_bound
    (aeStronglyMeasurable_of_ae_continuousAt μ hc) M (Eventually.of_forall hM)
  have hinterval (s t : ℝ) := intervalIntegrable_of_ae_bound ht M
      (fun t => hM (γ (Multiplicative.ofAdd t))) s t
  let A (T : ℝ) : ℂ := (b T - a T)⁻¹ • ∫ t in a T..b T, f (γ (Multiplicative.ofAdd t))
  let I : ℂ := ∫ x, f x ∂μ
  have hcoord (L : ℂ →L[ℝ] ℝ) (hL : ∀ z, |L z| ≤ ‖z‖) :
      Tendsto (fun T => L (A T)) atTop (𝓝 (L I)) := by
    have htime : ∀ s t : ℝ,
        IntervalIntegrable (fun t : ℝ => L (f (γ (Multiplicative.ofAdd t)))) volume s t :=
      intervalIntegrable_of_ae_bound (L.continuous.comp_aestronglyMeasurable ht) M
        (fun t => (hL _).trans (hM _))
    have h := denseFlow_tendsto_real_average_ae_continuous γ hγ hd μ (fun x => L (f x)) M
      (fun x => (hL _).trans (hM x))
      (hc.mono fun _ hx => L.continuous.continuousAt.comp hx) htime hlen
    simp_rw [L.integral_comp_comm hf, L.intervalIntegral_comp_comm (hinterval _ _),
      ← smul_eq_mul, ← L.map_smul] at h
    exact h
  have hr := hcoord Complex.reCLM Complex.abs_re_le_norm
  have hi := hcoord Complex.imCLM Complex.abs_im_le_norm
  exact (Complex.equivRealProdCLM.symm.continuous.tendsto (I.re, I.im)).comp
    (hr.prodMk_nhds hi) |>.congr (fun T => Complex.equivRealProdCLM.symm_apply_apply (A T))

/-- A rational-translation transversal in the unit interval is not Lebesgue measurable,
even after completion. -/
private theorem exists_nonNullMeasurable_subset_unit :
    ∃ E : Set ℝ, E ⊆ Icc (0 : ℝ) 1 ∧ ¬ NullMeasurableSet E volume := by
  classical
  let H : AddSubgroup ℝ := (Rat.castHom ℝ).toAddMonoidHom.range
  let π := QuotientAddGroup.mk' H
  let r (q : ℝ ⧸ H) := Int.fract q.out
  have hr (q : ℝ ⧸ H) : π (r q) = q := by
    have h : π (r q) = π q.out := by
      apply QuotientAddGroup.eq_iff_sub_mem.mpr
      change r q - q.out ∈ H
      refine ⟨-(⌊q.out⌋ : ℚ), ?_⟩
      change ((-(⌊q.out⌋ : ℚ) : ℚ) : ℝ) = Int.fract q.out - q.out
      push_cast
      unfold Int.fract
      ring
    exact h.trans (Quotient.out_eq q)
  let E := range r
  have hE : E ⊆ Icc (0 : ℝ) 1 := by
    rintro _ ⟨q, rfl⟩
    exact ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩
  refine ⟨E, hE, fun hm => ?_⟩
  let V (p : ℚ) : Set ℝ := (fun x : ℝ => (p : ℝ) + x) ⁻¹' E
  have hV (p : ℚ) : volume (V p) = volume E := measure_preimage_add _ _ _
  have hπ (p : ℚ) : π (p : ℝ) = 0 := by
    rw [← map_zero π]
    apply QuotientAddGroup.eq_iff_sub_mem.mpr
    rw [sub_zero]
    exact ⟨p, rfl⟩
  have hd : Pairwise fun p q : ℚ => Disjoint (V p) (V q) := by
    intro p q hpq
    apply Set.disjoint_left.mpr
    rintro x ⟨a, ha⟩ ⟨b, hb⟩
    have heq : a = b := by
      calc
        a = π (r a) := (hr a).symm
        _ = π x := by rw [ha, map_add, hπ, zero_add]
        _ = π (r b) := by rw [hb, map_add, hπ, zero_add]
        _ = b := hr b
    apply hpq
    subst b
    have : (p : ℝ) = (q : ℝ) := add_right_cancel (ha.symm.trans hb)
    exact_mod_cast this
  have hcover : (⋃ p, V p) = univ := by
    apply eq_univ_of_forall
    intro x
    have hs : r (π x) - x ∈ H := QuotientAddGroup.eq_iff_sub_mem.mp (hr (π x))
    obtain ⟨p, hp⟩ := hs
    refine mem_iUnion.mpr ⟨p, mem_range.mpr ⟨π x, ?_⟩⟩
    change (p : ℝ) = r (π x) - x at hp
    change r (π x) = (p : ℝ) + x
    rw [hp, sub_add_cancel]
  have hzero : volume E = 0 := by
    by_contra hpos
    let J := Icc (-1 : ℚ) 1
    haveI : Infinite J := (Icc_infinite (show (-1 : ℚ) < 1 by norm_num)).to_subtype
    have hsum : volume (⋃ j : J, V j.val) = ⊤ := by
      rw [measure_iUnion₀ (fun i j hij =>
        (hd (fun he => hij (Subtype.ext he))).aedisjoint) (fun j => hm.preimage
          (measurePreserving_add_left volume (j.val : ℝ)).quasiMeasurePreserving)]
      simp_rw [hV]
      exact ENNReal.tsum_const_eq_top_of_ne_zero hpos
    have hsubset : (⋃ j : J, V j.val) ⊆ Icc (-1 : ℝ) 2 := by
      intro x hx
      obtain ⟨j, hj⟩ := mem_iUnion.mp hx
      have he := hE hj
      have hmin : (-1 : ℝ) ≤ (j.val : ℝ) := by exact_mod_cast j.property.1
      have hmax : (j.val : ℝ) ≤ 1 := by exact_mod_cast j.property.2
      change 0 ≤ (j.val : ℝ) + x ∧ (j.val : ℝ) + x ≤ 1 at he
      exact ⟨by linarith [he.1], by linarith [he.2]⟩
    exact (isCompact_Icc.measure_lt_top (μ := volume)).ne
      (top_unique (hsum ▸ measure_mono hsubset))
  have hnull : volume (⋃ p, V p) = 0 := measure_iUnion_null_iff.mpr (fun p => (hV p).trans hzero)
  rw [hcover] at hnull
  exact (Measure.measure_univ_ne_zero.mpr (NeZero.ne (volume : Measure ℝ))) hnull

omit [CompactSpace G] in
private theorem injectiveFlow_arc_null (γ : Multiplicative ℝ →* G) (hγ : Continuous γ)
    (hi : Injective γ) (μ : Measure G) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant] :
    μ ((fun t : ℝ => γ (Multiplicative.ofAdd t)) '' Icc 0 1) = 0 := by
  let c : ℝ → G := fun t => γ (Multiplicative.ofAdd t)
  let K := c '' Icc 0 1
  have hK : IsCompact K := isCompact_Icc.image hγ
  have hadd (x y : ℝ) : c (x + y) = c x * c y := map_mul γ _ _
  let U (n : ℕ) := (fun x => c (2 * n) * x) ⁻¹' K
  have hU (n : ℕ) : μ (U n) = μ K := measure_preimage_mul μ _ _
  have hrep (n : ℕ) (x : G) (hx : x ∈ U n) :
      ∃ t ∈ Icc (0 : ℝ) 1, x = c (t - 2 * n) := by
    obtain ⟨t, ht, he⟩ := hx
    refine ⟨t, ht, mul_left_cancel (a := c (2 * n)) ?_⟩
    change c t = c (2 * n) * x at he
    rw [← he, ← hadd]
    congr 1
    ring
  have hd : Pairwise (fun m n => Disjoint (U m) (U n)) := by
    intro m n hmn
    apply Set.disjoint_left.mpr
    intro x hx hy
    obtain ⟨s, hs, hsx⟩ := hrep m x hx
    obtain ⟨t, ht, htx⟩ := hrep n x hy
    have he : s - 2 * (m : ℝ) = t - 2 * (n : ℝ) :=
      Multiplicative.ofAdd.injective (hi (hsx.symm.trans htx))
    cases lt_or_gt_of_ne hmn with
    | inl h =>
      have hle : (m : ℝ) + 1 ≤ n := by exact_mod_cast h
      linarith [hs.1, ht.2]
    | inr h =>
      have hle : (n : ℝ) + 1 ≤ m := by exact_mod_cast h
      linarith [hs.2, ht.1]
  by_contra hne
  have htop : μ (⋃ n, U n) = ⊤ := by
    rw [measure_iUnion hd (fun n => (continuous_const.mul continuous_id).measurable hK.isClosed.measurableSet)]
    simp_rw [hU]
    exact ENNReal.tsum_const_eq_top_of_ne_zero hne
  have hle := measure_mono (μ := μ) (subset_univ (⋃ n, U n))
  rw [htop, measure_univ] at hle
  exact ENNReal.one_ne_top (top_unique hle)

/-- The counting form of uniform distribution applies to every Borel set
whose boundary in the orbit closure has Haar measure zero. -/
theorem denseFlow_tendsto_indicator (γ : Multiplicative ℝ →* G) (hγ : Continuous γ)
    (hd : DenseRange γ) (μ : Measure G) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant] [μ.Regular]
    (U : Set G) (hU : MeasurableSet U) (hBd : μ (frontier U) = 0)
    {a b : ℝ → ℝ} (hlen : Tendsto (fun t => b t - a t) atTop atTop) :
    Tendsto (fun T => (b T - a T)⁻¹ *
        (∫ t in a T..b T, U.indicator (1 : G → ℝ) (γ (Multiplicative.ofAdd t))))
      atTop (𝓝 (μ.real U)) := by
  let v : G → ℝ := U.indicator 1
  have hv : Measurable v := measurable_const.indicator hU
  have hv0 (x) : 0 ≤ v x := indicator_nonneg (fun _ _ => zero_le_one) _
  have hv1 (x) : v x ≤ 1 := indicator_le_self' (fun _ _ => zero_le_one) _
  have hvi : Integrable v μ := Integrable.of_bound hv.aestronglyMeasurable 1
    (Eventually.of_forall fun x => by rw [Real.norm_eq_abs, abs_of_nonneg (hv0 x)]; exact hv1 x)
  have hvm : ∫ x, v x ∂μ = μ.real U := by
    simp [v, integral_indicator hU]
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hδ : 0 < ε/3 := by positivity
  obtain ⟨f, g, hf, hg, hfg, hgap⟩ :=
    continuous_nullFrontier_envelopes μ U hBd hδ
  have hfInt : Integrable f μ := f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hgInt : Integrable g μ := g.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hF : ∫ x, f x ∂μ ≤ μ.real U := by
    rw [← hvm]
    exact integral_mono hfInt hvi (fun x => (hfg x).1)
  have hG : μ.real U ≤ ∫ x, g x ∂μ := by
    rw [← hvm]
    exact integral_mono hvi hgInt (fun x => (hfg x).2)
  rw [integral_sub hgInt hfInt] at hgap
  let c : ℝ → G := fun t => γ (Multiplicative.ofAdd t)
  have hc : Continuous c := hγ
  have hfLim := (Metric.tendsto_nhds.mp (denseFlow_tendsto_average γ hγ hd μ f hlen)) _ hδ
  have hgLim := (Metric.tendsto_nhds.mp (denseFlow_tendsto_average γ hγ hd μ g hlen)) _ hδ
  filter_upwards [hfLim, hgLim, hlen.eventually_ge_atTop 1] with T hTf hTg hT
  have hab : a T < b T := sub_pos.mp (zero_lt_one.trans_le hT)
  have hvInt : IntervalIntegrable (v ∘ c) volume (a T) (b T) := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le).mpr
    letI : IsFiniteMeasure (volume.restrict (Ioc (a T) (b T))) := ⟨by simp⟩
    exact Integrable.of_bound (hv.comp hc.measurable).aestronglyMeasurable 1
      (Eventually.of_forall fun x => by
        change ‖v (c x)‖ ≤ 1
        rw [Real.norm_eq_abs, abs_of_nonneg (hv0 _)]
        exact hv1 _)
  have hlo := intervalIntegral.integral_mono_on hab.le
    ((f.continuous.comp hc).intervalIntegrable (μ := volume) _ _) hvInt (fun t _ => (hfg (c t)).1)
  have hhi := intervalIntegral.integral_mono_on hab.le hvInt
    ((g.continuous.comp hc).intervalIntegrable (μ := volume) _ _) (fun t _ => (hfg (c t)).2)
  have hl := mul_le_mul_of_nonneg_left hlo (inv_nonneg.mpr (sub_nonneg.mpr hab.le))
  have hr := mul_le_mul_of_nonneg_left hhi (inv_nonneg.mpr (sub_nonneg.mpr hab.le))
  rw [Real.dist_eq] at hTf hTg ⊢
  rw [abs_lt] at hTf hTg ⊢
  change -(ε/3) < (b T - a T)⁻¹ * (∫ t in a T..b T, f (c t)) - _ ∧ _ at hTf
  change -(ε/3) < (b T - a T)⁻¹ * (∫ t in a T..b T, g (c t)) - _ ∧ _ at hTg
  change -ε < (b T - a T)⁻¹ * (∫ t in a T..b T, (v ∘ c) t) - μ.real U ∧
    (b T - a T)⁻¹ * (∫ t in a T..b T, (v ∘ c) t) - μ.real U < ε
  simp only [Function.comp_apply, smul_eq_mul, c] at hl hr hTf hTg ⊢
  constructor <;> linarith [hTf.1, hTg.2]

end

section Torus

noncomputable section

abbrev FlowTorus (n : ℕ) := Multiplicative (Fin n → UnitAddCircle)

instance (n : ℕ) : MeasurableSpace (FlowTorus n) := borel _

instance (n : ℕ) : BorelSpace (FlowTorus n) := ⟨rfl⟩

noncomputable def torusFlow (τ : Fin n → ℝ) : Multiplicative ℝ →* FlowTorus n :=
  AddMonoidHom.toMultiplicative (AddMonoidHom.pi fun i =>
    (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))).comp
      (DistribSMul.toAddMonoidHom ℝ (τ i)))

theorem torusFlow_continuous (τ : Fin n → ℝ) : Continuous (torusFlow τ) := by
  change Continuous (fun t : ℝ => fun i : Fin n => ((τ i * t : ℝ) : UnitAddCircle))
  exact continuous_pi fun i => (AddCircle.continuous_mk' 1).comp (continuous_const.mul continuous_id)

/-- Rational independence of at least two frequencies rules out a nonzero period.
Adapted from mccorvie/riemann-masullo, commit d219ab2. -/
theorem torusFlow_injective_of_linearIndependent (hn : 2 ≤ n) {τ : Fin n → ℝ}
    (hτ : LinearIndependent ℚ τ) : Injective (torusFlow τ) := by
  rw [injective_iff_map_eq_one]
  intro t ht
  have hint (i : Fin n) : ∃ m : ℤ, (m : ℝ) = τ i * t.toAdd := by
    have hi : ((τ i * t.toAdd : ℝ) : UnitAddCircle) = 0 :=
      congrFun (congrArg Multiplicative.toAdd ht) i
    simpa using ((AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).mp hi)
  by_contra ht₁
  have ht₀ : t.toAdd ≠ 0 := ht₁
  let i : Fin n := ⟨0, by omega⟩
  let j : Fin n := ⟨1, by omega⟩
  have hij : i ≠ j := by
    intro h
    have hv := congrArg Fin.val h
    simp [i, j] at hv
  obtain ⟨a, ha⟩ := hint i
  obtain ⟨b, hb⟩ := hint j
  have hrel : (b : ℚ) • τ i + (-(a : ℚ)) • τ j = 0 := by
    rw [Rat.smul_def, Rat.smul_def]
    push_cast
    apply (mul_eq_zero.mp ?_).resolve_right ht₀
    calc
      ((b : ℝ) * τ i + -(a : ℝ) * τ j) * t.toAdd =
          (b : ℝ) * (τ i * t.toAdd) - (a : ℝ) * (τ j * t.toAdd) := by ring
      _ = 0 := by rw [← ha, ← hb]; ring
  have hb₀ : (b : ℚ) = 0 :=
    ((LinearIndepOn.pair_iff τ hij).mp (hτ.comp _ Subtype.val_injective) _ _ hrel).1
  have hbR : (b : ℝ) = 0 := by exact_mod_cast hb₀
  exact hτ.ne_zero j ((mul_eq_zero.mp (hb.symm.trans hbR)).resolve_right ht₀)

/-- The one-dimensional flow always has a nonzero period, including when its
single frequency is rationally independent. -/
theorem torusFlow_one_not_injective (τ : Fin 1 → ℝ) : ¬ Injective (torusFlow τ) := by
  intro hinj
  have hkernel (t : Multiplicative ℝ) (ht : torusFlow τ t = 1) : t = 1 :=
    hinj (ht.trans (map_one (torusFlow τ)).symm)
  by_cases hτ : τ 0 = 0
  · have h : torusFlow τ (Multiplicative.ofAdd (1 : ℝ)) = 1 := by
      apply congrArg Multiplicative.ofAdd
      funext i
      have hi : i = 0 := Subsingleton.elim _ _
      change ((τ i * 1 : ℝ) : UnitAddCircle) = 0
      simp [hi, hτ]
    exact one_ne_zero (show (1 : ℝ) = 0 from hkernel _ h)
  · have h : torusFlow τ (Multiplicative.ofAdd (τ 0)⁻¹) = 1 := by
      apply congrArg Multiplicative.ofAdd
      funext i
      have hi : i = 0 := Subsingleton.elim _ _
      change ((τ i * (τ 0)⁻¹ : ℝ) : UnitAddCircle) = 0
      rw [hi, mul_inv_cancel₀ hτ]
      exact (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).mpr ⟨1, one_zsmul _⟩
    exact (inv_ne_zero hτ) (show (τ 0)⁻¹ = (0 : ℝ) from hkernel _ h)

abbrev torusOrbit (τ : Fin n → ℝ) : Subgroup (FlowTorus n) :=
  (torusFlow τ).range.topologicalClosure

instance (τ : Fin n → ℝ) : CompactSpace (torusOrbit τ) :=
  isCompact_iff_compactSpace.mp ((torusFlow τ).range.isClosed_topologicalClosure.isCompact)

def torusOrbitFlow (τ : Fin n → ℝ) : Multiplicative ℝ →* torusOrbit τ :=
  (torusFlow τ).codRestrict _ (fun _ => subset_closure (mem_range_self _))

theorem torusOrbitFlow_continuous (τ : Fin n → ℝ) : Continuous (torusOrbitFlow τ) :=
  (torusFlow_continuous τ).subtype_mk _

theorem torusOrbitFlow_dense (τ : Fin n → ℝ) : DenseRange (torusOrbitFlow τ) := by
  intro x
  rw [closure_subtype, ← range_comp]
  exact x.property

noncomputable def torusOrbitHaar (τ : Fin n → ℝ) : Measure (torusOrbit τ) :=
  Measure.haarMeasure ⟨⟨univ, isCompact_univ⟩, by simp⟩

instance (τ : Fin n → ℝ) : IsProbabilityMeasure (torusOrbitHaar τ) :=
  ⟨Measure.haarMeasure_self⟩

instance (τ : Fin n → ℝ) : (torusOrbitHaar τ).IsMulLeftInvariant :=
  Measure.isMulLeftInvariant_haarMeasure _

instance (τ : Fin n → ℝ) : (torusOrbitHaar τ).Regular :=
  Measure.regular_haarMeasure

private theorem torusMonomial_mul (k : Fin n → ℤ) (x y : FlowTorus n) :
    UnitAddTorus.mFourier k (x * y).toAdd =
      UnitAddTorus.mFourier k x.toAdd * UnitAddTorus.mFourier k y.toAdd := by
  change UnitAddTorus.mFourier k (x.toAdd + y.toAdd) = _
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, Pi.add_apply, fourier_apply, smul_add,
    AddCircle.toCircle_add, Circle.coe_mul, Finset.prod_mul_distrib]

private theorem torusMonomial_flow (τ : Fin n → ℝ) (k : Fin n → ℤ) (t : ℝ) :
    UnitAddTorus.mFourier k (torusFlow τ (Multiplicative.ofAdd t)).toAdd =
      Complex.exp (2 * Real.pi * Complex.I * ((∑ i, (k i : ℝ) * τ i : ℝ) : ℂ) * t) := by
  have h (i : Fin n) : (torusFlow τ (Multiplicative.ofAdd t)).toAdd i =
      ((τ i * t : ℝ) : UnitAddCircle) := rfl
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, h, fourier_coe_apply, ← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- Rational independence makes the real flow dense in the ambient torus.
Uses the Fourier pairing from mccorvie/riemann-masullo, commit fbb923e, under
Apache-2.0, and Haar averaging on the actual orbit closure. -/
theorem torusFlow_denseRange_of_linearIndependent {τ : Fin n → ℝ}
    (hτ : LinearIndependent ℚ τ) : DenseRange (torusFlow τ) := by
  classical
  let H := torusOrbit τ
  let ν := torusOrbitHaar τ
  have hcont (x : FlowTorus n) : Continuous (fun y : H => (x * y.val).toAdd) :=
    (continuous_const.mul continuous_subtype_val :
      Continuous (fun y : H => (x * y.val : FlowTorus n)))
  have hInt (x : FlowTorus n) (f : C(UnitAddTorus (Fin n), ℂ)) :
      Integrable (fun y : H => f (x * y.val).toAdd) ν :=
    (f.continuous.comp (hcont x)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  let A (x : FlowTorus n) : C(UnitAddTorus (Fin n), ℂ) →L[ℂ] ℂ := LinearMap.mkContinuous
    { toFun := fun f => ∫ y : H, f (x * y.val).toAdd ∂ν
      map_add' := fun f g => integral_add (hInt x f) (hInt x g)
      map_smul' := fun c f => integral_smul c _ } 1 (by
        intro f
        rw [one_mul]
        simpa using norm_integral_le_of_norm_le_const (μ := ν)
          (Eventually.of_forall fun y : H => f.norm_coe_le_norm (x * y.val).toAdd))
  have hA (x : FlowTorus n) (f : C(UnitAddTorus (Fin n), ℂ)) :
      A x f = ∫ y : H, f (x * y.val).toAdd ∂ν := rfl
  have hzero (k : Fin n → ℤ) (hk : k ≠ 0) : A 1 (UnitAddTorus.mFourier k) = 0 := by
    let c : ℝ := ∑ i, (k i : ℝ) * τ i
    have hc : c ≠ 0 := by
      intro he
      apply hk
      have h := Fintype.linearIndependent_iff.mp hτ (fun i => (k i : ℚ))
        (by simpa [c, Rat.smul_def] using he)
      funext i
      exact_mod_cast h i
    let y := torusOrbitFlow τ (Multiplicative.ofAdd (1 / (2 * c)))
    have hy : UnitAddTorus.mFourier k y.val.toAdd = -1 := by
      change UnitAddTorus.mFourier k (torusFlow τ _).toAdd = _
      rw [torusMonomial_flow]
      have hphase : (2 * Real.pi * Complex.I * (c : ℂ) * ((1 / (2 * c) : ℝ) : ℂ)) =
          Real.pi * Complex.I := by
        push_cast
        field_simp [Complex.ofReal_ne_zero.mpr hc]
      rw [hphase, Complex.exp_pi_mul_I]
    have hinv := integral_mul_left_eq_self (μ := ν)
      (fun z : H => UnitAddTorus.mFourier k z.val.toAdd) y
    change (∫ z : H, UnitAddTorus.mFourier k (y.val * z.val).toAdd ∂ν) =
      ∫ z : H, UnitAddTorus.mFourier k z.val.toAdd ∂ν at hinv
    simp only [torusMonomial_mul, hy, neg_one_mul] at hinv
    rw [integral_neg (fun z : H => UnitAddTorus.mFourier k z.val.toAdd)] at hinv
    rw [hA]
    simp only [one_mul]
    linear_combination (-1 / 2 : ℂ) * hinv
  intro x
  by_contra hx
  let U := (fun y : H => x * y.val) '' (univ : Set H)
  have hU : IsClosed U := (isCompact_univ.image
      (continuous_const.mul continuous_subtype_val)).isClosed
  have hH : IsClosed (H : Set (FlowTorus n)) :=
    (torusFlow τ).range.isClosed_topologicalClosure
  have hd : Disjoint (H : Set (FlowTorus n)) U := by
    refine Set.disjoint_left.mpr ?_
    rintro _ hz ⟨y, -, rfl⟩
    apply hx
    change x ∈ H
    simpa using H.mul_mem hz (H.inv_mem y.property)
  obtain ⟨f, hf₀, hf₁, _⟩ := exists_continuous_zero_one_of_isClosed hH hU hd
  let φ : C(UnitAddTorus (Fin n), ℂ) := ⟨fun z => (f (Multiplicative.ofAdd z) : ℂ),
    Complex.continuous_ofReal.comp f.continuous⟩
  have hgen (k : Fin n → ℤ) : A x (UnitAddTorus.mFourier k) = A 1 (UnitAddTorus.mFourier k) := by
    by_cases hk : k = 0
    · subst k
      simp [UnitAddTorus.mFourier_zero, hA]
    have hrel : A x (UnitAddTorus.mFourier k) =
        UnitAddTorus.mFourier k x.toAdd * A 1 (UnitAddTorus.mFourier k) := by
      simp only [hA, one_mul, torusMonomial_mul]
      rw [integral_const_mul]
    rw [hrel, hzero k hk, mul_zero]
  have hspan : Submodule.span ℂ (range (UnitAddTorus.mFourier (d := Fin n))) ≤
      LinearMap.ker ((A x - A 1).toLinearMap) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨k, rfl⟩
    exact LinearMap.mem_ker.mpr (sub_eq_zero.mpr (hgen k))
  have heq : A x φ = A 1 φ := by
    have hmem : φ ∈ (Submodule.span ℂ (range (UnitAddTorus.mFourier (d := Fin n)))).topologicalClosure := by
      rw [UnitAddTorus.span_mFourier_closure_eq_top]
      trivial
    have hclosed : IsClosed (LinearMap.ker ((A x - A 1).toLinearMap) : Set C(UnitAddTorus (Fin n), ℂ)) :=
      (A x - A 1).isClosed_ker
    exact sub_eq_zero.mp (LinearMap.mem_ker.mp (closure_minimal hspan hclosed hmem))
  have hleft (y : H) : φ (x * y.val).toAdd = 1 := by
    change (f (x * y.val) : ℂ) = 1
    rw [hf₁ (show x * y.val ∈ U from ⟨y, mem_univ _, rfl⟩)]
    norm_num
  have hright (y : H) : φ (1 * y.val).toAdd = 0 := by
    rw [one_mul]
    change (f y.val : ℂ) = 0
    rw [hf₀ y.property]
    norm_num
  simp only [hA, hleft, hright] at heq
  haveI : IsProbabilityMeasure ν := inferInstanceAs (IsProbabilityMeasure (torusOrbitHaar τ))
  rw [integral_const (μ := ν) (1 : ℂ), integral_const (μ := ν) (0 : ℂ),
    probReal_univ, one_smul, smul_zero] at heq
  exact one_ne_zero heq

private def torusIntegerMap {d n : ℕ} (A : Fin n → Fin d → ℤ) : FlowTorus d →* FlowTorus n :=
  AddMonoidHom.toMultiplicative
    { toFun := fun x i => ∑ j, A i j • x j
      map_zero' := by ext i; simp
      map_add' := by intro x y; ext i; simp [Finset.sum_add_distrib] }

private theorem torusIntegerMap_continuous {d n : ℕ} (A : Fin n → Fin d → ℤ) :
    Continuous (torusIntegerMap A) := by
  change Continuous (fun x : Fin d → UnitAddCircle => fun i => ∑ j, A i j • x j)
  exact continuous_pi fun i => continuous_finsetSum _ fun j _ =>
    (continuous_zsmul (A i j)).comp (continuous_apply j)

private theorem torusIntegerMap_flow {d n : ℕ} (A : Fin n → Fin d → ℤ)
    {α : Fin d → ℝ} {β : Fin n → ℝ} (hA : ∀ i, ∑ j, A i j • α j = β i)
    (t : Multiplicative ℝ) :
    torusIntegerMap A (torusFlow α t) = torusFlow β t := by
  apply congrArg Multiplicative.ofAdd
  funext i
  let q : ℝ →+ UnitAddCircle := QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))
  change (∑ j, A i j • q (α j * t.toAdd)) = q (β i * t.toAdd)
  simp_rw [← map_zsmul, ← map_sum, zsmul_eq_mul]
  apply congrArg q
  rw [← hA i, Finset.sum_mul]
  simp_rw [zsmul_eq_mul, mul_assoc]

/-- The orbit closure is a torus of dimension equal to the rational rank of
the frequency vector, including the zero-frequency case of B.5.2.1(1). -/
theorem torusOrbit_equiv_rank (τ : Fin n → ℝ) :
    ∃ e : FlowTorus (Module.finrank ℚ (Submodule.span ℚ (range τ))) ≃* torusOrbit τ,
      Continuous e ∧ Continuous e.symm := by
  classical
  let M := Submodule.span ℤ (range τ)
  let v (i : Fin n) : M := ⟨τ i, Submodule.subset_span (mem_range_self i)⟩
  have hv : Submodule.span ℤ (range v) = ⊤ := by
    apply eq_top_iff.mpr
    intro x _
    have he : (Submodule.span ℤ (range v)).map M.subtype = M := by
      rw [Submodule.map_span, ← range_comp]
      rfl
    have hx : x.val ∈ (Submodule.span ℤ (range v)).map M.subtype := by
      rw [he]
      exact x.property
    obtain ⟨y, hy, heq⟩ := Submodule.mem_map.mp hx
    exact (Subtype.ext heq : y = x) ▸ hy
  obtain ⟨d, b⟩ := Module.basisOfFiniteTypeTorsionFree hv
  let σ (j : Fin d) : ℝ := (b j).val
  have hσ : LinearIndependent ℚ σ := (LinearIndependent.iff_fractionRing ℤ ℚ).mp
    (b.linearIndependent.map' M.subtype M.ker_subtype)
  let A (i : Fin n) (j : Fin d) : ℤ := b.repr (v i) j
  have hA (i : Fin n) : ∑ j, A i j • σ j = τ i := by
    simpa only [map_sum, map_zsmul, A, σ, Submodule.subtype_apply] using
      congrArg M.subtype (b.sum_repr (v i))
  have hrepr (j : Fin d) : ∃ c : Fin n → ℤ, ∑ i, c i • τ i = σ j := by
    exact (Submodule.mem_span_range_iff_exists_fun ℤ).mp (b j).property
  choose B hB using hrepr
  have hspan : Submodule.span ℚ (range σ) = Submodule.span ℚ (range τ) := by
    have hs (j : Fin d) : σ j ∈ Submodule.span ℚ (range τ) :=
      Submodule.span_le_restrictScalars ℤ ℚ _ (b j).property
    refine le_antisymm (Submodule.span_le.mpr (forall_mem_range.mpr hs)) ?_
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact Submodule.span_le_restrictScalars ℤ ℚ _
      ((Submodule.mem_span_range_iff_exists_fun ℤ).mpr ⟨A i, hA i⟩)
  have hrank : Module.finrank ℚ (Submodule.span ℚ (range τ)) = d := by
    rw [← hspan, finrank_span_eq_card hσ, Fintype.card_fin]
  let a := torusIntegerMap A
  let c := torusIntegerMap B
  have ha := torusIntegerMap_continuous A
  have hc := torusIntegerMap_continuous B
  have hd := torusFlow_denseRange_of_linearIndependent hσ
  have hca : LeftInverse c a := by
    have h : EqOn (c ∘ a) id (range (torusFlow σ)) := by
      rintro _ ⟨t, rfl⟩
      exact (congrArg c (torusIntegerMap_flow A hA t)).trans (torusIntegerMap_flow B hB t)
    intro z
    exact h.closure (hc.comp ha) continuous_id (hd z)
  have hr : range a = (torusOrbit τ : Set (FlowTorus n)) := by
    change range a = closure (range (torusFlow τ))
    have heq : a '' range (torusFlow σ) = range (torusFlow τ) := by
      rw [← range_comp]
      exact congrArg range (funext (torusIntegerMap_flow A hA))
    refine le_antisymm ?_ (closure_minimal ?_ ((isCompact_range ha).isClosed))
    · rw [← heq]
      exact ha.range_subset_closure_image_dense
        (show Dense (range (torusFlow σ)) from hd)
    · rw [← heq]
      exact image_subset_range _ _
  let incl : FlowTorus d →* torusOrbit τ := a.codRestrict _ (fun x => by
    change a x ∈ (torusOrbit τ : Set (FlowTorus n))
    rw [← hr]
    exact mem_range_self x)
  have hincl : Bijective incl := ⟨fun _ _ h => hca.injective (congrArg Subtype.val h), by
    intro y
    obtain ⟨x, hx⟩ : y.val ∈ range a := hr.symm ▸ y.property
    exact ⟨x, Subtype.ext hx⟩⟩
  let e := MulEquiv.ofBijective incl hincl
  have hsymm (y : torusOrbit τ) : e.symm y = c y.val := by
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [e.symm_apply_apply]
    exact (hca x).symm
  rw [hrank]
  exact ⟨e, ha.subtype_mk _, (hc.comp continuous_subtype_val).congr (fun y => (hsymm y).symm)⟩

/-- B.5.2.1 with the measurability required for the Lebesgue time integrals.
The orbit closure has the asserted rational rank, and both time averages
converge for every bounded, Haar-almost-everywhere continuous test with a
Lebesgue-measurable time trace, including measurability in the completion. -/
theorem kroneckerWeyl (τ : Fin n → ℝ) :
    (∃ e : FlowTorus (Module.finrank ℚ (Submodule.span ℚ (range τ))) ≃* torusOrbit τ,
      Continuous e ∧ Continuous e.symm) ∧
    ∀ (f : torusOrbit τ → ℂ) (M : ℝ), (∀ x, ‖f x‖ ≤ M) →
      (∀ᵐ x ∂torusOrbitHaar τ, ContinuousAt f x) →
      AEStronglyMeasurable (fun t : ℝ => f (torusOrbitFlow τ (Multiplicative.ofAdd t))) volume →
      (Tendsto (fun T : ℝ => (2 * T)⁻¹ •
          ∫ t in -T..T, f (torusOrbitFlow τ (Multiplicative.ofAdd t)))
        atTop (𝓝 (∫ x, f x ∂torusOrbitHaar τ))) ∧
      (Tendsto (fun T : ℝ => T⁻¹ •
          ∫ t in (0 : ℝ)..T, f (torusOrbitFlow τ (Multiplicative.ofAdd t)))
        atTop (𝓝 (∫ x, f x ∂torusOrbitHaar τ))) := by
  refine ⟨torusOrbit_equiv_rank τ, fun f M hM hc ht => ?_⟩
  have h (a b : ℝ → ℝ) := denseFlow_tendsto_average_ae_continuous (torusOrbitFlow τ)
    (torusOrbitFlow_continuous τ) (torusOrbitFlow_dense τ) (torusOrbitHaar τ) f M hM hc ht
      (a := a) (b := b)
  have hsym : Tendsto (fun T : ℝ => T - (-T)) atTop atTop :=
    (tendsto_id.const_mul_atTop (show 0 < (2 : ℝ) by norm_num)).congr (fun T => by dsimp; ring)
  have hforward : Tendsto (fun T : ℝ => T - 0) atTop atTop :=
    tendsto_atTop_atTop.mpr fun r => ⟨r, fun T hT => by simpa only [sub_zero] using hT⟩
  refine ⟨?_, by simpa using h (fun _ => 0) id hforward⟩
  simpa only [id_eq, sub_neg_eq_add, two_mul] using h (fun T => -T) id hsym

/-- The time-trace assumption in B.5.2.1(2) is necessary. Even on the
two-frequency flow with frequencies one and square root of two, a bounded
Haar-almost-everywhere continuous test can have a nonmeasurable time trace. -/
theorem kroneckerWeyl_nonmeasurable_time_trace :
    ∃ (τ : Fin 2 → ℝ) (f : torusOrbit τ → ℂ),
      (∀ x, ‖f x‖ ≤ 1) ∧ (∀ᵐ x ∂torusOrbitHaar τ, ContinuousAt f x) ∧
      ∀ T : ℝ, 1 ≤ T →
        (¬ IntervalIntegrable (fun t : ℝ => f (torusOrbitFlow τ (Multiplicative.ofAdd t))) volume 0 T) ∧
        (¬ IntervalIntegrable (fun t : ℝ => f (torusOrbitFlow τ (Multiplicative.ofAdd t))) volume (-T) T) := by
  classical
  let τ : Fin 2 → ℝ := ![1, Real.sqrt 2]
  have hinj : Injective (torusFlow τ) := by
    rw [injective_iff_map_eq_one]
    intro t ht
    have h (i : Fin 2) : ∃ k : ℤ, (k : ℝ) = τ i * t.toAdd := by
      have he : ((τ i * t.toAdd : ℝ) : UnitAddCircle) = 0 :=
        congrFun (congrArg Multiplicative.toAdd ht) i
      simpa using (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).mp he
    obtain ⟨k, hk⟩ := h 0
    obtain ⟨l, hl⟩ := h 1
    change (k : ℝ) = 1 * t.toAdd at hk
    change (l : ℝ) = Real.sqrt 2 * t.toAdd at hl
    rw [one_mul] at hk
    change t.toAdd = 0
    by_contra ht₀
    have hk₀ : (k : ℝ) ≠ 0 := hk.trans_ne ht₀
    apply irrational_sqrt_two
    refine ⟨(l : ℚ) / (k : ℚ), ?_⟩
    push_cast
    exact (div_eq_iff hk₀).mpr (by rw [hk, ← hl])
  have hji : Injective (torusOrbitFlow τ) := fun _ _ h => hinj (congrArg Subtype.val h)
  let c : ℝ → torusOrbit τ := fun t => torusOrbitFlow τ (Multiplicative.ofAdd t)
  have hci : Injective c := hji.comp Multiplicative.ofAdd.injective
  obtain ⟨E, hE, hnon⟩ := exists_nonNullMeasurable_subset_unit
  let f : torusOrbit τ → ℂ := (c '' E).indicator 1
  let K := c '' Icc 0 1
  have hc : Continuous c := torusOrbitFlow_continuous τ
  have hK : IsClosed K := (isCompact_Icc.image hc).isClosed
  have hzero : torusOrbitHaar τ K = 0 := injectiveFlow_arc_null (torusOrbitFlow τ)
    (torusOrbitFlow_continuous τ) hji (torusOrbitHaar τ)
  have hbound (x : torusOrbit τ) : ‖f x‖ ≤ 1 := by
    by_cases hx : x ∈ c '' E <;> simp [f, hx]
  have hcont : ∀ᵐ x ∂torusOrbitHaar τ, ContinuousAt f x := by
    have hne : ∀ᵐ x ∂torusOrbitHaar τ, x ∉ K := by
      rw [ae_iff]
      simpa using hzero
    filter_upwards [hne] with x hx
    have hconst : ContinuousAt (fun _ : torusOrbit τ => (0 : ℂ)) x := continuousAt_const
    apply hconst.congr
    filter_upwards [hK.isOpen_compl.mem_nhds hx] with y hy
    exact (indicator_of_notMem (fun h => hy (image_mono hE h)) _).symm
  have hpre : (f ∘ c) ⁻¹' ({1} : Set ℂ) = E := by
    ext t
    have he : c t ∈ c '' E ↔ t ∈ E := by
      exact ⟨fun ⟨u, hu, ht⟩ => (hci ht) ▸ hu, fun h => ⟨t, h, rfl⟩⟩
    by_cases ht : t ∈ E <;> simp [f, he, ht]
  have hbad : ¬ IntervalIntegrable (f ∘ c) volume 0 1 := by
    intro hm
    have hmeas := hm.1.aestronglyMeasurable.aemeasurable.nullMeasurableSet_preimage
      (measurableSet_singleton (1 : ℂ))
    rw [hpre] at hmeas
    have hnull := (nullMeasurableSet_restrict measurableSet_Ioc.nullMeasurableSet).mp hmeas
    apply hnon (hnull.congr ?_)
    filter_upwards [(volume : Measure ℝ).ae_ne 0] with t ht
    change (t ∈ E ∩ Ioc (0 : ℝ) 1) = (t ∈ E)
    apply propext
    exact ⟨And.left, fun he => ⟨he, lt_of_le_of_ne (hE he).1 ht.symm, (hE he).2⟩⟩
  refine ⟨τ, f, hbound, hcont, fun T hT => ⟨fun hf => hbad (hf.mono_set ?_),
    fun hf => hbad (hf.mono_set ?_)⟩⟩
  · rw [uIcc_of_le zero_le_one, uIcc_of_le (by linarith : 0 ≤ T)]
    exact Icc_subset_Icc le_rfl hT
  · rw [uIcc_of_le zero_le_one, uIcc_of_le (by linarith : -T ≤ T)]
    exact Icc_subset_Icc (by linarith) hT

/-- The quotient map of the fundamental cube, viewed on real coordinates. -/
def torusProjection (n : ℕ) (x : Fin n → ℝ) : FlowTorus n :=
  Multiplicative.ofAdd (fun i => (x i : UnitAddCircle))

def torusUnitCube (n : ℕ) : Set (Fin n → ℝ) :=
  {x | ∀ i, x i ∈ Ico (0 : ℝ) 1}

theorem torusUnitCube_measurable (n : ℕ) : MeasurableSet (torusUnitCube n) := by
  have eq : torusUnitCube n = ⋂ i : Fin n, (fun x : Fin n → ℝ => x i) ⁻¹' Ico (0 : ℝ) 1 := by
    ext x
    simp [torusUnitCube]
  rw [eq]
  exact MeasurableSet.iInter fun i => measurableSet_Ico.preimage (measurable_pi_apply i)

theorem torusUnitCube_open_image_measurable {n : ℕ} {U : Set (torusUnitCube n)} (hU : IsOpen U) :
    MeasurableSet (Subtype.val '' U) :=
  ((MeasurableEmbedding.subtype_coe (torusUnitCube_measurable n)).measurableSet_image).mpr
    hU.measurableSet

/-- On the half-open fundamental cube the torus projection has a Borel inverse. -/
theorem torusProjection_image_measurable {n : ℕ} (U : Set (Fin n → ℝ))
    (hU : MeasurableSet U) (hCube : ∀ x ∈ U, ∀ i, x i ∈ Ico (0 : ℝ) 1) :
    MeasurableSet (torusProjection n '' U) := by
  let e := AddCircle.measurableEquivIco (T := (1 : ℝ)) (0 : ℝ)
  let r : FlowTorus n → Fin n → ℝ := fun x i => (e (Multiplicative.toAdd x i)).val
  have hr : Measurable r := by
    apply measurable_pi_lambda
    intro i
    apply measurable_subtype_coe.comp (e.measurable.comp _)
    have hi : Continuous (fun x : FlowTorus n => Multiplicative.toAdd x i) := continuous_apply i
    exact Continuous.measurable (α := FlowTorus n) (γ := UnitAddCircle) hi
  have hr1 (x : FlowTorus n) : torusProjection n (r x) = x := by
    apply congrArg Multiplicative.ofAdd (funext _)
    intro i
    exact AddCircle.coe_equivIco (p := (1 : ℝ)) (a := 0)
  have hr2 (x : Fin n → ℝ) (hx : x ∈ U) : r (torusProjection n x) = x := by
    funext i
    change (AddCircle.equivIco (1 : ℝ) 0 (x i : UnitAddCircle)).val = x i
    rw [AddCircle.equivIco_coe_eq (by simpa using hCube x hx i)]
  have eq : torusProjection n '' U = r ⁻¹' U := by
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      change r (torusProjection n t) ∈ U
      rwa [hr2 t ht]
    · intro hx
      exact ⟨r x, hx, hr1 x⟩
  rw [eq]
  exact hr hU

/-- B.5.2.4, with both the one-sided and the symmetric time proportions. -/
theorem torusFlow_uniformDistribution (τ : Fin n → ℝ) (U : Set (Fin n → ℝ))
    (hU : MeasurableSet U) (hCube : ∀ x ∈ U, ∀ i, x i ∈ Ico (0 : ℝ) 1)
    (hBd : torusOrbitHaar τ
      (frontier ((Subtype.val : torusOrbit τ → FlowTorus n) ⁻¹' (torusProjection n '' U))) = 0) :
    let S := (Subtype.val : torusOrbit τ → FlowTorus n) ⁻¹' (torusProjection n '' U)
    let A := {t : ℝ | torusFlow τ (Multiplicative.ofAdd t) ∈ torusProjection n '' U}
    Tendsto (fun T : ℝ => (volume : Measure ℝ).real (Icc (-T) T ∩ A) / (2*T)) atTop
        (𝓝 ((torusOrbitHaar τ).real S)) ∧
    Tendsto (fun T : ℝ => (volume : Measure ℝ).real (Icc 0 T ∩ A) / T) atTop
        (𝓝 ((torusOrbitHaar τ).real S)) := by
  intro S A
  have hS : MeasurableSet S := (torusProjection_image_measurable U hU hCube).preimage
    measurable_subtype_coe
  have hc : Continuous (fun t : ℝ => torusFlow τ (Multiplicative.ofAdd t)) := torusFlow_continuous τ
  have hA : MeasurableSet A := (torusProjection_image_measurable U hU hCube).preimage hc.measurable
  have hAeq (t : ℝ) : S.indicator (1 : torusOrbit τ → ℝ)
      (torusOrbitFlow τ (Multiplicative.ofAdd t)) = A.indicator 1 t := by
    by_cases h : t ∈ A <;> simp [indicator_of_mem, indicator_of_notMem, h,
      show torusOrbitFlow τ (Multiplicative.ofAdd t) ∈ S ↔ t ∈ A from Iff.rfl]
  have hI (a b : ℝ) (hab : a ≤ b) :
      (∫ t in a..b, S.indicator (1 : torusOrbit τ → ℝ) (torusOrbitFlow τ (Multiplicative.ofAdd t))) =
        (volume : Measure ℝ).real (Icc a b ∩ A) := by
    simp_rw [hAeq]
    rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc, integral_indicator hA,
      Measure.restrict_restrict hA]
    simp only [Pi.one_apply, setIntegral_const, smul_eq_mul, mul_one, inter_comm]
  have hsym : Tendsto (fun T : ℝ => T - (-T)) atTop atTop := by
    refine (tendsto_id.const_mul_atTop (show 0 < (2 : ℝ) by norm_num)).congr (fun T => by dsimp only [id_eq]; ring)
  have hpos : Tendsto (fun T : ℝ => T - 0) atTop atTop := by
    simp only [sub_zero]
    exact tendsto_id
  constructor
  · apply (denseFlow_tendsto_indicator (torusOrbitFlow τ) (torusOrbitFlow_continuous τ)
      (torusOrbitFlow_dense τ) (torusOrbitHaar τ) S hS hBd hsym).congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
    rw [hI (-T) T (by linarith), show T - (-T) = 2*T by ring, div_eq_mul_inv, mul_comm]
  · apply (denseFlow_tendsto_indicator (torusOrbitFlow τ) (torusOrbitFlow_continuous τ)
      (torusOrbitFlow_dense τ) (torusOrbitHaar τ) S hS hBd hpos).congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
    rw [hI 0 T hT, sub_zero, div_eq_mul_inv, mul_comm]

end

end Torus

end Masullo
