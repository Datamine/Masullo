import HardySobolevHalfline
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

open Filter Function MeasureTheory Set Topology
open scoped ContDiff ENNReal

namespace Masullo

noncomputable section

local notation "realMeasure" => (volume : Measure ℝ)

private def tailDensity (s : ℝ) (k : ℕ) (δ x : ℝ) : ℝ :=
  Real.exp (-δ * x) * (x ^ (2 * k) * (1 + x ^ 2) ^ (-s / 2))

private theorem tailDensity_nonneg (s : ℝ) (k : ℕ) (δ x : ℝ) :
    0 ≤ tailDensity s k δ x := by
  unfold tailDensity
  rw [pow_mul]
  positivity

private theorem tailDensity_measurable (s : ℝ) (k : ℕ) (δ : ℝ) :
    Measurable (tailDensity s k δ) := by unfold tailDensity; fun_prop

/-- At a finite endpoint the polynomial tail is integrable exactly above the
strict Sobolev threshold. In the interior, the exponential gap absorbs every moment. -/
private theorem hardySobolev_tail_integrable_iff {s δ : ℝ} (hs : 0 ≤ s) (hδ : 0 ≤ δ) (k : ℕ) :
    IntegrableOn (tailDensity s k δ) (Ioi 0) ↔ 0 < δ ∨ 2 * (k : ℝ) + 1 < s := by
  rcases hδ.eq_or_lt with hzero | hpos
  · subst δ
    have htail (x : ℝ) : tailDensity s k 0 x = x ^ (2 * k) * (1 + x ^ 2) ^ (-s / 2) := by
      simp [tailDensity]
    simp only [lt_irrefl, false_or]
    constructor
    · intro h
      let c : ℝ := (2 : ℝ) ^ (-s / 2)
      have hc : 0 < c := Real.rpow_pos_of_pos (by norm_num) _
      have hl : IntegrableOn (fun x : ℝ => c * x ^ (2 * (k : ℝ) - s)) (Ioi 1) := by
        apply (h.mono_set (Ioi_subset_Ioi (by norm_num))).mono'
          (Measurable.aestronglyMeasurable (by fun_prop))
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
        have hx1 : 1 < x := hx
        have hx0 : 0 < x := zero_lt_one.trans hx1
        rw [Real.norm_of_nonneg (by positivity), htail]
        calc
          c * x ^ (2 * (k : ℝ) - s) = x ^ (2 * k) * (2 * x ^ 2) ^ (-s / 2) := by
            rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_natCast x 2,
              ← Real.rpow_mul hx0.le, ← Real.rpow_natCast x (2 * k),
              mul_left_comm, ← Real.rpow_add hx0]
            unfold c
            push_cast
            congr 2
            ring
          _ ≤ _ := mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_nonpos (by positivity) (by nlinarith) (by linarith)) (by positivity)
      have hi : IntegrableOn (fun x : ℝ => x ^ (2 * (k : ℝ) - s)) (Ioi 1) := by
        simpa only [IntegrableOn, ← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul] using hl.const_mul c⁻¹
      linarith [(integrableOn_Ioi_rpow_iff (show (0 : ℝ) < 1 by norm_num)).mp hi]
    · intro h
      have hd : (Module.finrank ℝ ℝ : ℝ) < s - 2 * (k : ℝ) := by simp; linarith
      apply ((integrable_rpow_neg_one_add_norm_sq (μ := (volume : Measure ℝ)) hd).integrableOn
        (s := Ioi 0)).mono' (tailDensity_measurable s k 0).aestronglyMeasurable
      refine .of_forall fun x => ?_
      rw [Real.norm_of_nonneg (tailDensity_nonneg s k 0 x), htail, Real.norm_eq_abs, sq_abs, pow_mul]
      have hq : 0 < 1 + x ^ 2 := by positivity
      have he : -(s - 2 * (k : ℝ)) / 2 = (k : ℝ) + -s / 2 := by ring
      rw [he, Real.rpow_add hq, Real.rpow_natCast]
      gcongr
      exact le_add_of_nonneg_left zero_le_one
  · refine ⟨fun _ => Or.inl hpos, fun _ => ?_⟩
    have hmain := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := 2 * (k : ℝ))
      (b := δ) (by have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg _; linarith) le_rfl hpos
    apply hmain.mono' (tailDensity_measurable s k δ).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 < x := hx
    have hp : x ^ (2 * (k : ℝ)) = x ^ (2 * k) := by
      exact_mod_cast Real.rpow_natCast x (2 * k)
    rw [Real.norm_of_nonneg (tailDensity_nonneg s k δ x), tailDensity, Real.rpow_one, hp]
    have hc : (1 + x ^ 2) ^ (-s / 2) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (le_add_of_nonneg_right (sq_nonneg x)) (by linarith)
    calc
      _ ≤ Real.exp (-δ * x) * (x ^ (2 * k) * 1) := by gcongr
      _ = _ := by rw [mul_one, mul_comm]

/-- The logarithmic kernel of a complex derivative evaluation. -/
def mellinEvaluationKernel (k : ℕ) (z : ℂ) (x : ℝ) : ℂ :=
  Complex.exp (z * (x : ℂ)) * (x : ℂ) ^ k

private theorem mellinEvaluationKernel_continuous (k : ℕ) (z : ℂ) :
    Continuous (mellinEvaluationKernel k z) := by unfold mellinEvaluationKernel; fun_prop

/-- The squared Mellin kernel in reciprocal-weight coordinates. -/
def evaluationDensity (a b s : ℝ) (k : ℕ) (z : ℂ) (x : ℝ) : ℝ :=
  ‖stripSobolevAmplitude (-a) (-b) (-s) x • mellinEvaluationKernel k z x‖ ^ 2

theorem evaluationDensity_eq (a b s : ℝ) (k : ℕ) (z : ℂ) (x : ℝ) :
    evaluationDensity a b s k z x =
      Real.exp (2 * (z.re - (if x ≤ 0 then a else b)) * x) *
        (x ^ (2 * k) * (1 + x ^ 2) ^ (-s / 2)) := by
  unfold evaluationDensity mellinEvaluationKernel stripSobolevAmplitude
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity), norm_mul, norm_pow,
    Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  have hp : (|x| ^ k) ^ 2 = x ^ (2 * k) := by
    rw [← pow_mul, Nat.mul_comm k 2, pow_mul, sq_abs, ← pow_mul]
  have hpol : ((1 + x ^ 2) ^ (-s / 4)) ^ 2 = (1 + x ^ 2) ^ (-s / 2) := by
    rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (by positivity : 0 ≤ 1 + x ^ 2)]
    congr 1
    push_cast
    ring
  simp only [mul_pow, hp, hpol, ← Real.exp_nat_mul]
  push_cast
  by_cases hx : x ≤ 0 <;> simp only [hx, ite_true, ite_false] <;>
    rw [mul_mul_mul_comm, ← Real.exp_add] <;> ring_nf


private theorem evaluationDensity_integrable_negative (a b s : ℝ) (k : ℕ) (z : ℂ) : IntegrableOn (evaluationDensity a b s k z) (Iio 0) ↔
      IntegrableOn (tailDensity s k (2 * (z.re - a))) (Ioi 0) := by
  rw [← (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
    (Homeomorph.neg ℝ).measurableEmbedding]
  simp only [neg_preimage, neg_Iio, neg_zero]
  apply integrableOn_congr_fun _ measurableSet_Ioi
  intro x hx
  have hx0 : 0 < x := hx
  simp only [Function.comp_apply, evaluationDensity_eq, tailDensity, ite_eq_left (neg_nonpos.mpr hx0.le),
    neg_sq, pow_mul]
  rw [show 2 * (z.re - a) * -x = -(2 * (z.re - a)) * x by ring]

private theorem evaluationDensity_integrable_positive (a b s : ℝ) (k : ℕ) (z : ℂ) : IntegrableOn (evaluationDensity a b s k z) (Ioi 0) ↔
      IntegrableOn (tailDensity s k (2 * (b - z.re))) (Ioi 0) := by
  apply integrableOn_congr_fun _ measurableSet_Ioi
  intro x hx
  have hx0 : 0 < x := hx
  simp only [evaluationDensity_eq, tailDensity, ite_eq_right hx0.not_ge]
  rw [show 2 * (z.re - b) = -(2 * (b - z.re)) by ring]

theorem evaluationDensity_integrable_iff {a b s : ℝ} {z : ℂ}
    (ha : a ≤ z.re) (hb : z.re ≤ b) (hs : 0 ≤ s) (k : ℕ) :
    Integrable (evaluationDensity a b s k z) ↔
      (a < z.re ∧ z.re < b) ∨ 2 * (k : ℝ) + 1 < s := by
  rw [← integrableOn_univ, ← Iio_union_Ici (a := (0 : ℝ)), integrableOn_union,
    integrableOn_Ici_iff_integrableOn_Ioi]
  rw [evaluationDensity_integrable_negative, evaluationDensity_integrable_positive, hardySobolev_tail_integrable_iff hs (by linarith),
    hardySobolev_tail_integrable_iff hs (by linarith)]
  have hl : 0 < 2 * (z.re - a) ↔ a < z.re := by constructor <;> intro h <;> linarith
  have hr : 0 < 2 * (b - z.re) ↔ z.re < b := by constructor <;> intro h <;> linarith
  rw [hl, hr]
  tauto

/-- The Mellin derivative kernel belongs to the reciprocal-weight Hilbert space
on every interior line, and on an endpoint exactly at the strict threshold. -/
theorem mellinEvaluationKernel_memLp_iff {a b s : ℝ} {z : ℂ}
    (ha : a ≤ z.re) (hb : z.re ≤ b) (hs : 0 ≤ s) (k : ℕ) :
    MemLp (mellinEvaluationKernel k z) 2 (stripMeasure (-a) (-b) (-s)) ↔
      (a < z.re ∧ z.re < b) ∨ 2 * (k : ℝ) + 1 < s := by
  let r := stripSobolevAmplitude (-a) (-b) (-s)
  let K := mellinEvaluationKernel k z
  have hr := stripSobolevAmplitude_continuous (-a) (-b) (-s)
  have hK := mellinEvaluationKernel_continuous k z
  rw [memLp_amplitudeMeasure_iff realMeasure r hr.measurable hK.aestronglyMeasurable,
    memLp_two_iff_integrable_sq_norm
      (show AEStronglyMeasurable (fun x => r x • K x) realMeasure from
        hr.aestronglyMeasurable.smul hK.aestronglyMeasurable)]
  exact evaluationDensity_integrable_iff ha hb hs k


/-- Testing the reciprocal-weight dual representative against smooth profiles
determines it almost everywhere on their open support domain. -/
theorem stripDual_rep_eq_on_support_of_compactTestPairing (a b s : ℝ) {K : ℝ → ℂ} (hK : Continuous K)
    {U : Set ℝ} (hU : IsOpen U) (L : StrongDual ℂ (StripSobolev a b s))
    (hL : ∀ f : PositiveRealExponentialDecay univ, HasCompactSupport f.val → tsupport f.val ⊆ U →
      L (stripSobolevTest univ ⟨a, mem_univ a⟩ ⟨b, mem_univ b⟩ s f) =
        ∫ x, f.val x * K x) :
    ∀ᵐ x ∂realMeasure, x ∈ U → (stripSobolevDuality a b s).symm L x = K x := by
  let q := stripSobolevAmplitude (-a) (-b) (-s)
  let j := stripSobolevTest univ ⟨a, mem_univ a⟩ ⟨b, mem_univ b⟩ s
  have hq := stripSobolevAmplitude_continuous (-a) (-b) (-s)
  have hqpos := stripSobolevAmplitude_pos (-a) (-b) (-s)
  have hposAC : realMeasure ≪ stripMeasure a b s :=
    absolutelyContinuous_amplitudeMeasure realMeasure _ (stripSobolevAmplitude_continuous a b s).measurable
      (stripSobolevAmplitude_pos a b s)
  have hnegAC : realMeasure ≪ stripMeasure (-a) (-b) (-s) :=
    absolutelyContinuous_amplitudeMeasure realMeasure q hq.measurable hqpos
  let g := (stripSobolevDuality a b s).symm L
  let G := amplitudeL2Iso realMeasure q hq.measurable hqpos g
  have hg : (g : ℝ → ℂ) =ᵐ[realMeasure] fun x => (q x)⁻¹ • G x := by
    have h := hnegAC.ae_le (amplitudeL2Iso_symm_ae realMeasure q hq.measurable hqpos G)
    rwa [(amplitudeL2Iso realMeasure q hq.measurable hqpos).symm_apply_apply] at h
  have hgI : LocallyIntegrable (g : ℝ → ℂ) realMeasure :=
    ((Lp.memLp G).locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)).continuous_smul
      (hq.inv₀ fun x => (hqpos x).ne') |>.congr hg.symm
  have hKI := hK.locallyIntegrable (μ := realMeasure)
  have hEq : ∀ᵐ x ∂realMeasure, x ∈ U → g x - K x = 0 := by
    apply hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      ((hgI.sub hKI).locallyIntegrableOn U)
    intro φ hφ hc hφU
    let p (x : ℝ) : ℂ := φ x
    let f : PositiveRealExponentialDecay univ :=
      ⟨p, mem_logExponentialDecaySubmodule_of_hasCompactSupport univ
        (hc.comp_left Complex.ofReal_zero) (Complex.ofRealCLM.contDiff.comp hφ)⟩
    have hpC : HasCompactSupport f.val := hc.comp_left Complex.ofReal_zero
    have hpU : tsupport f.val ⊆ U := by
      apply (closure_mono ?_).trans hφU
      intro x hx
      exact fun h => hx (by change (φ x : ℂ) = 0; rw [h, Complex.ofReal_zero])
    have hf := hposAC.ae_le (stripSobolevTest_ae univ ⟨a, mem_univ a⟩ ⟨b, mem_univ b⟩ s f)
    have hgf := stripSobolevDuality_apply a b s (j f) g
    rw [(stripSobolevDuality a b s).apply_symm_apply] at hgf
    have hpair : (∫ x, φ x • g x) = ∫ x, φ x • K x := by
      calc
        (∫ x, φ x • g x) = ∫ x, (j f) x * g x := by
          apply integral_congr_ae
          filter_upwards [hf] with x hx
          change (j f) x = (φ x : ℂ) at hx
          rw [hx, Complex.real_smul]
        _ = L (j f) := hgf.symm
        _ = ∫ x, φ x • K x := by
          rw [hL f hpC hpU]
          simp only [Complex.real_smul]
          rfl
    change (∫ x, φ x • (g x - K x)) = 0
    simp_rw [smul_sub]
    rw [integral_sub (hgI.integrable_smul_left_of_hasCompactSupport hφ.continuous hc)
      (hKI.integrable_smul_left_of_hasCompactSupport hφ.continuous hc), hpair, sub_self]
  exact hEq.mono fun x hx hxU => sub_eq_zero.mp (hx hxU)

/-- Testing against the supported exponential tests determines the dual
representative on the open support domain. -/
theorem stripDual_rep_eq_on_support_of_testPairing (a b s : ℝ) {K : ℝ → ℂ} (hK : Continuous K)
    {U : Set ℝ} (hU : IsOpen U) (L : StrongDual ℂ (StripSobolev a b s))
    (hL : ∀ f : PositiveRealExponentialDecay univ, (∀ x ∉ U, f.val x = 0) →
      L (stripSobolevTest univ ⟨a, mem_univ a⟩ ⟨b, mem_univ b⟩ s f) =
        ∫ x, f.val x * K x) :
    ∀ᵐ x ∂realMeasure, x ∈ U → (stripSobolevDuality a b s).symm L x = K x :=
  stripDual_rep_eq_on_support_of_compactTestPairing a b s hK hU L (fun f _ h => hL f
    (fun _ hx => image_eq_zero_of_notMem_tsupport (fun h' => hx (h h'))))

private theorem stripEvaluation_representable_iff (a b s : ℝ) {K : ℝ → ℂ} (hK : Continuous K)
    {U : Set ℝ} (hU : IsOpen U) :
    (∃ L : StrongDual ℂ (StripSobolev a b s), ∀ f : PositiveRealExponentialDecay univ,
        (∀ x ∉ U, f.val x = 0) →
        L (stripSobolevTest univ ⟨a, mem_univ a⟩ ⟨b, mem_univ b⟩ s f) =
          ∫ x, f.val x * K x) ↔ MemLp (U.indicator K) 2 (stripMeasure (-a) (-b) (-s)) := by
  let r := stripSobolevAmplitude a b s
  let q := stripSobolevAmplitude (-a) (-b) (-s)
  let j := stripSobolevTest univ ⟨a, mem_univ a⟩ ⟨b, mem_univ b⟩ s
  have hr := stripSobolevAmplitude_continuous a b s
  have hq := stripSobolevAmplitude_continuous (-a) (-b) (-s)
  have hrpos := stripSobolevAmplitude_pos a b s
  have hqpos := stripSobolevAmplitude_pos (-a) (-b) (-s)
  have hposAC : realMeasure ≪ stripMeasure a b s :=
    absolutelyContinuous_amplitudeMeasure realMeasure r hr.measurable hrpos
  have hnegAC : realMeasure ≪ stripMeasure (-a) (-b) (-s) :=
    absolutelyContinuous_amplitudeMeasure realMeasure q hq.measurable hqpos
  constructor
  · rintro ⟨L, hL⟩
    let g := (stripSobolevDuality a b s).symm L
    have hEq := stripDual_rep_eq_on_support_of_testPairing a b s hK hU L hL
    refine ((Lp.memLp g).indicator hU.measurableSet).ae_eq
      ((amplitudeMeasure_absolutelyContinuous realMeasure q).ae_le ?_)
    filter_upwards [hEq] with x hx
    by_cases hxU : x ∈ U
    · simp only [indicator_of_mem hxU]
      exact hx hxU
    · simp [hxU]
  · intro h
    let g := h.toLp (U.indicator K)
    refine ⟨stripSobolevDuality a b s g, fun f hf => ?_⟩
    rw [stripSobolevDuality_apply]
    apply integral_congr_ae
    filter_upwards [hposAC.ae_le (stripSobolevTest_ae univ ⟨a, mem_univ a⟩ ⟨b, mem_univ b⟩ s f),
      hnegAC.ae_le h.coeFn_toLp] with x hx hg
    change g x = U.indicator K x at hg
    rw [hx, hg]
    by_cases hxU : x ∈ U
    · rw [indicator_of_mem hxU]
    · simp [hf x hxU]

/-- A Mellin derivative on the scalar tests is its logarithmic moment integral. -/
theorem mellinEvaluation_test_integral (f : PositiveRealExponentialDecay univ) (k : ℕ) (z : ℂ) :
    iteratedDeriv k (mellin fun t => f.val (Real.log t)) z =
      ∫ x, f.val x * mellinEvaluationKernel k z x := by
  let T : logExponentialDecaySubmodule (univ : Set ℝ) := f
  change iteratedDeriv k (mellin fun t => T.val (Real.log t)) z =
    ∫ x, T.val x * mellinEvaluationKernel k z x
  rw [mellin_iteratedDeriv_log_moment, mellin_eq_log_integral]
  apply integral_congr_ae
  exact .of_forall fun x => by simp only [Real.log_exp, mellinEvaluationKernel]; ring

/-- The Mellin derivative evaluation extends continuously from the scalar tests
to the compact weighted completion exactly in the interior or above the strict
endpoint threshold. -/
theorem hardySobolev_mellinEvaluation_exists_iff {a b s : ℝ} {z : ℂ}
    (ha : a ≤ z.re) (hb : z.re ≤ b) (hs : 0 ≤ s) (k : ℕ) :
    (∃ L : StrongDual ℂ (StripSobolev a b s), ∀ f : PositiveRealExponentialDecay univ,
      L (stripSobolevTest univ ⟨a, mem_univ a⟩ ⟨b, mem_univ b⟩ s f) =
        iteratedDeriv k (mellin fun t => f.val (Real.log t)) z) ↔
      (a < z.re ∧ z.re < b) ∨ 2 * (k : ℝ) + 1 < s := by
  simp_rw [mellinEvaluation_test_integral]
  have hrep := stripEvaluation_representable_iff a b s (mellinEvaluationKernel_continuous k z)
    (isOpen_univ : IsOpen (univ : Set ℝ))
  rw [indicator_univ] at hrep
  simpa using hrep.trans (mellinEvaluationKernel_memLp_iff ha hb hs k)


private theorem mellinEvaluationKernel_indicator_memLp_iff
    {U : Set ℝ} (hU : MeasurableSet U) (a b s : ℝ) (k : ℕ) (z : ℂ) :
    MemLp (U.indicator (mellinEvaluationKernel k z)) 2 (stripMeasure (-a) (-b) (-s)) ↔
      IntegrableOn (evaluationDensity a b s k z) U := by
  let r := stripSobolevAmplitude (-a) (-b) (-s)
  let K := mellinEvaluationKernel k z
  have hr := stripSobolevAmplitude_continuous (-a) (-b) (-s)
  have hk := (mellinEvaluationKernel_continuous k z).measurable.indicator hU
  rw [memLp_amplitudeMeasure_iff realMeasure r hr.measurable hk.aestronglyMeasurable,
    memLp_two_iff_integrable_sq_norm
      (show AEStronglyMeasurable (fun x => r x • U.indicator K x) realMeasure from
        hr.aestronglyMeasurable.smul hk.aestronglyMeasurable)]
  have he : (fun x => ‖r x • U.indicator K x‖ ^ 2) = U.indicator (evaluationDensity a b s k z) := by
    funext x
    by_cases hx : x ∈ U <;> simp [hx, evaluationDensity, r, K]
  rw [he, integrable_indicator_iff hU]

/-- The closed completion of exponential tests that vanish off an open logarithmic set. -/
def supportedSobolevCompletion (a b s : ℝ) (U : Set ℝ) : Submodule ℂ (StripSobolev a b s) :=
  let S : Submodule ℂ (PositiveRealExponentialDecay univ) :=
    { carrier := {f | ∀ x ∉ U, f.val x = 0}
      zero_mem' := fun _ _ => rfl
      add_mem' := fun {f g} hf hg x hx => by
        change f.val x + g.val x = 0
        rw [hf x hx, hg x hx, add_zero]
      smul_mem' := fun c f hf x hx => by change c • f.val x = 0; rw [hf x hx, smul_zero] }
  (S.map (stripSobolevTest univ ⟨a, mem_univ a⟩ ⟨b, mem_univ b⟩ s).toLinearMap).topologicalClosure

/-- The dense inclusion of a supported exponential test into its completion. -/
def supportedSobolevTest (a b s : ℝ) (U : Set ℝ)
    (f : PositiveRealExponentialDecay univ) (hf : ∀ x ∉ U, f.val x = 0) :
    supportedSobolevCompletion a b s U :=
  ⟨stripSobolevTest univ ⟨a, mem_univ a⟩ ⟨b, mem_univ b⟩ s f,
    Submodule.le_topologicalClosure _ ⟨f, hf, rfl⟩⟩



instance (a b s : ℝ) (U : Set ℝ) : CompleteSpace (supportedSobolevCompletion a b s U) :=
  (Submodule.isClosed_topologicalClosure _).completeSpace_coe

theorem supportedSobolevTest_denseRange (a b s : ℝ) (U : Set ℝ) :
    DenseRange (fun f : {f : PositiveRealExponentialDecay univ // ∀ x ∉ U, f.val x = 0} =>
      supportedSobolevTest a b s U f.val f.property) := by
  let S := supportedSobolevCompletion a b s U
  let j (f : {f : PositiveRealExponentialDecay univ // ∀ x ∉ U, f.val x = 0}) : S :=
    supportedSobolevTest a b s U f.val f.property
  intro u
  change u ∈ closure (range j)
  rw [IsInducing.subtypeVal.closure_eq_preimage_closure_image, mem_preimage]
  rw [← range_comp]
  have h : (u : StripSobolev a b s) ∈ (S : Set (StripSobolev a b s)) := u.property
  apply (closure_mono ?_) h
  intro v hv
  obtain ⟨f, hf, rfl⟩ := hv
  exact ⟨⟨f, hf⟩, rfl⟩


private theorem supportedMellinEvaluation_iff (a b s : ℝ) {U : Set ℝ} (hU : IsOpen U) (k : ℕ) (z : ℂ) :
    (∃ L : StrongDual ℂ (supportedSobolevCompletion a b s U),
      ∀ (f : PositiveRealExponentialDecay univ) (hf : ∀ x ∉ U, f.val x = 0),
        L (supportedSobolevTest a b s U f hf) =
          iteratedDeriv k (mellin fun t => f.val (Real.log t)) z) ↔
      IntegrableOn (evaluationDensity a b s k z) U := by
  rw [← mellinEvaluationKernel_indicator_memLp_iff hU.measurableSet]
  have h := stripEvaluation_representable_iff a b s (mellinEvaluationKernel_continuous k z) hU
  rw [← h]
  simp_rw [mellinEvaluation_test_integral]
  constructor
  · rintro ⟨L, hL⟩
    obtain ⟨L', h', _⟩ := exists_extension_norm_eq (supportedSobolevCompletion a b s U) L
    exact ⟨L', fun f hf => (h' (supportedSobolevTest a b s U f hf)).trans (hL f hf)⟩
  · rintro ⟨L, hL⟩
    exact ⟨L.comp (supportedSobolevCompletion a b s U).subtypeL, fun f hf => hL f hf⟩


/-- Bounded Mellin evaluation on the supported tests is equivalent to
square integrability of the restricted kernel in the reciprocal weight. -/
theorem supportedMellinEvaluation_memLp_iff (a b s : ℝ) {U : Set ℝ}
    (hU : IsOpen U) (k : ℕ) (z : ℂ) :
    (∃ L : StrongDual ℂ (supportedSobolevCompletion a b s U),
      ∀ (f : PositiveRealExponentialDecay univ) (hf : ∀ x ∉ U, f.val x = 0),
        L (supportedSobolevTest a b s U f hf) =
          iteratedDeriv k (mellin fun t => f.val (Real.log t)) z) ↔
    MemLp (U.indicator (mellinEvaluationKernel k z)) 2 (stripMeasure (-a) (-b) (-s)) :=
  (supportedMellinEvaluation_iff a b s hU k z).trans
    (mellinEvaluationKernel_indicator_memLp_iff hU.measurableSet a b s k z).symm

/-- The open rays used by the completion and the two finite-norm support
conditions agree on the scalar exponential tests. -/
theorem scalarHardySobolev_openRay_support (f : PositiveRealExponentialDecay univ) :
    ((∀ x ∉ Iio (0 : ℝ), f.val x = 0) ↔ ∀ x : ℝ, 0 < x → f.val x = 0) ∧
    ((∀ x ∉ Ioi (0 : ℝ), f.val x = 0) ↔ ∀ x : ℝ, x < 0 → f.val x = 0) := by
  have hclosed : IsClosed {x : ℝ | f.val x = 0} :=
    isClosed_eq (smooth_exponentialProfile univ ⟨0, mem_univ 0⟩ f).continuous continuous_const
  constructor
  · refine ⟨fun h x hx => h x hx.not_gt, ?_⟩
    intro h x hx
    have hc : closure (Ioi (0 : ℝ)) ⊆ {x : ℝ | f.val x = 0} :=
      closure_minimal (fun x hx => h x hx) hclosed
    rw [closure_Ioi] at hc
    exact hc (show 0 ≤ x from le_of_not_gt (show ¬ x < 0 from hx))
  · refine ⟨fun h x hx => h x hx.not_gt, ?_⟩
    intro h x hx
    have hc : closure (Iio (0 : ℝ)) ⊆ {x : ℝ | f.val x = 0} :=
      closure_minimal (fun x hx => h x hx) hclosed
    rw [closure_Iio] at hc
    exact hc (show x ≤ 0 from le_of_not_gt (show ¬ 0 < x from hx))

/-- On the whole real base every finite-norm test is zero, so evaluations
extend as zero for every derivative order and every complex point. -/
theorem hardySobolev_univ_mellinEvaluation_zero (s : ℝ) (k : ℕ) (z : ℂ)
    (f : PositiveRealExponentialDecay univ)
    (hf : hardySobolevIntervalENorm volume id univ s f.val ≠ (∞ : ℝ≥0∞)) :
    iteratedDeriv k (mellin fun t => f.val (Real.log t)) z = 0 := by
  have h := (scalarHardySobolev_univ_finite_iff s univ ⟨0, mem_univ 0⟩ f).mp hf
  rw [mellinEvaluation_test_integral, h]
  change (∫ x, 0 * mellinEvaluationKernel k z x) = 0
  simp


/-- Point evaluation for the corrected right half-line completion. -/
theorem hardySobolev_right_mellinEvaluation_exists_iff {a s : ℝ} {z : ℂ}
    (hz : a ≤ z.re) (hs : 0 ≤ s) (k : ℕ) :
    (∃ L : StrongDual ℂ (supportedSobolevCompletion a a s (Iio 0)),
      ∀ (f : PositiveRealExponentialDecay univ) (hf : ∀ x ∉ Iio (0 : ℝ), f.val x = 0),
        L (supportedSobolevTest a a s (Iio 0) f hf) =
          iteratedDeriv k (mellin fun t => f.val (Real.log t)) z) ↔
      a < z.re ∨ 2 * (k : ℝ) + 1 < s := by
  rw [supportedMellinEvaluation_iff a a s isOpen_Iio, evaluationDensity_integrable_negative,
    hardySobolev_tail_integrable_iff hs (by linarith)]
  have h : 0 < 2 * (z.re - a) ↔ a < z.re := by constructor <;> intro h <;> linarith
  rw [h]

/-- Point evaluation for the corrected left half-line completion. -/
theorem hardySobolev_left_mellinEvaluation_exists_iff {b s : ℝ} {z : ℂ}
    (hz : z.re ≤ b) (hs : 0 ≤ s) (k : ℕ) :
    (∃ L : StrongDual ℂ (supportedSobolevCompletion b b s (Ioi 0)),
      ∀ (f : PositiveRealExponentialDecay univ) (hf : ∀ x ∉ Ioi (0 : ℝ), f.val x = 0),
        L (supportedSobolevTest b b s (Ioi 0) f hf) =
          iteratedDeriv k (mellin fun t => f.val (Real.log t)) z) ↔
      z.re < b ∨ 2 * (k : ℝ) + 1 < s := by
  rw [supportedMellinEvaluation_iff b b s isOpen_Ioi, evaluationDensity_integrable_positive,
    hardySobolev_tail_integrable_iff hs (by linarith)]
  have h : 0 < 2 * (b - z.re) ↔ z.re < b := by constructor <;> intro h <;> linarith
  rw [h]


private theorem evaluationDensity_continuous (a b s : ℝ) (k : ℕ) (z : ℂ) :
    Continuous (evaluationDensity a b s k z) := by
  unfold evaluationDensity
  exact ((stripSobolevAmplitude_continuous (-a) (-b) (-s)).smul
    (mellinEvaluationKernel_continuous k z)).norm.pow 2

/-- In the compact-base space with a lower cutoff, the finite upper endpoint
alone governs continuity. This holds even for evaluations left of the strip. -/
theorem hardySobolev_cutoff_mellinEvaluation_exists_iff
    {a b s cutoff : ℝ} {z : ℂ} (hcut : cutoff ≤ 0) (hz : z.re ≤ b) (hs : 0 ≤ s) (k : ℕ) :
    (∃ L : StrongDual ℂ (supportedSobolevCompletion a b s (Ioi cutoff)),
      ∀ (f : PositiveRealExponentialDecay univ) (hf : ∀ x ∉ Ioi cutoff, f.val x = 0),
        L (supportedSobolevTest a b s (Ioi cutoff) f hf) =
          iteratedDeriv k (mellin fun t => f.val (Real.log t)) z) ↔
      z.re < b ∨ 2 * (k : ℝ) + 1 < s := by
  rw [supportedMellinEvaluation_iff a b s isOpen_Ioi]
  have he : IntegrableOn (evaluationDensity a b s k z) (Ioi cutoff) ↔
      IntegrableOn (evaluationDensity a b s k z) (Ioi 0) := by
    refine ⟨fun h => h.mono_set (Ioi_subset_Ioi hcut), fun h => ?_⟩
    have hc : IntegrableOn (evaluationDensity a b s k z) (Icc cutoff 0) :=
      (evaluationDensity_continuous a b s k z).continuousOn.integrableOn_Icc
    apply (hc.union h).mono_set
    intro x hx
    rcases le_or_gt x 0 with h | h
    · exact Or.inl ⟨(show cutoff < x from hx).le, h⟩
    · exact Or.inr h
  rw [he, evaluationDensity_integrable_positive, hardySobolev_tail_integrable_iff hs (by linarith)]
  have h : 0 < 2 * (b - z.re) ↔ z.re < b := by constructor <;> intro h <;> linarith
  rw [h]

/-- The reciprocal-weight kernel is square integrable on a bounded
logarithmic interval at every complex argument. -/
theorem hardySobolev_bounded_mellinKernel (a b s c : ℝ) (k : ℕ) (z : ℂ) :
    MemLp ((Ioo c 0).indicator (mellinEvaluationKernel k z)) 2 (stripMeasure (-a) (-b) (-s)) := by
  rw [mellinEvaluationKernel_indicator_memLp_iff measurableSet_Ioo]
  exact ((evaluationDensity_continuous a b s k z).continuousOn.integrableOn_Icc).mono_set
    Ioo_subset_Icc_self

/-- With a lower cutoff in a right half-line base the remaining logarithmic
support is bounded, so every derivative evaluation extends on the whole plane. -/
theorem hardySobolev_right_cutoff_mellinEvaluation (a s cutoff : ℝ) (k : ℕ) (z : ℂ) :
    ∃ L : StrongDual ℂ (supportedSobolevCompletion a a s (Ioo cutoff 0)),
      ∀ (f : PositiveRealExponentialDecay univ) (hf : ∀ x ∉ Ioo cutoff (0 : ℝ), f.val x = 0),
        L (supportedSobolevTest a a s (Ioo cutoff 0) f hf) =
          iteratedDeriv k (mellin fun t => f.val (Real.log t)) z := by
  apply (supportedMellinEvaluation_iff a a s isOpen_Ioo k z).mpr
  exact ((evaluationDensity_continuous a a s k z).continuousOn.integrableOn_Icc).mono_set Ioo_subset_Icc_self

/-- The endpoint order permitted by the manuscript at equality has no bounded
extension, even on a singleton base. -/
theorem hardySobolev_critical_endpoint_counterexample (a : ℝ) (k : ℕ) :
    ¬ ∃ L : StrongDual ℂ (StripSobolev a a (2 * (k : ℝ) + 1)),
      ∀ f : PositiveRealExponentialDecay univ,
        L (stripSobolevTest univ ⟨a, mem_univ a⟩ ⟨a, mem_univ a⟩ (2 * (k : ℝ) + 1) f) =
          iteratedDeriv k (mellin fun t => f.val (Real.log t)) (a : ℂ) := by
  have h : a ≤ (a : ℂ).re := le_rfl
  have h' : (a : ℂ).re ≤ a := le_rfl
  rw [hardySobolev_mellinEvaluation_exists_iff h h' (by positivity)]
  simp


/-- The analytic test functions underlying the corrected Hardy–Sobolev model
are the whole-plane Schwartz–Bergman Mellin transforms. -/
def hardySobolevTestMellin :
    PositiveRealExponentialDecay univ ≃L[ℂ] SchwartzBergman (univ : Set ℝ) :=
  positiveRealFourierMellin univ isOpen_univ ordConnected_univ univ_nonempty

theorem hardySobolevTestMellin_apply (f : PositiveRealExponentialDecay univ) :
    (hardySobolevTestMellin f).val = mellin (fun t => f.val (Real.log t)) :=
  funext fun z => positiveRealFourierMellin_apply univ isOpen_univ ordConnected_univ
    univ_nonempty f z (mem_univ z.re)

/-- The completion of the analytic tests with the transported weighted norm. -/
def hardySobolevAnalyticTest (a b s : ℝ) :
    SchwartzBergman (univ : Set ℝ) →L[ℂ] StripSobolev a b s :=
  (stripSobolevTest univ ⟨a, mem_univ a⟩ ⟨b, mem_univ b⟩ s).comp
    hardySobolevTestMellin.symm.toContinuousLinearMap

theorem hardySobolevAnalyticTest_embedding (a b s : ℝ) :
    Injective (hardySobolevAnalyticTest a b s) ∧ DenseRange (hardySobolevAnalyticTest a b s) := by
  exact ⟨(stripSobolevTest_injective univ ⟨a, mem_univ a⟩ ⟨b, mem_univ b⟩ s).comp
    hardySobolevTestMellin.symm.injective,
    (stripSobolevTest_denseRange univ ⟨a, mem_univ a⟩ ⟨b, mem_univ b⟩ s).comp
      hardySobolevTestMellin.symm.surjective.denseRange
      (stripSobolevTest univ ⟨a, mem_univ a⟩ ⟨b, mem_univ b⟩ s).continuous⟩

/-- Scalar derivative evaluation on the compact analytic test completion. -/
theorem hardySobolev_analyticEvaluation_exists_iff {a b s : ℝ} {z : ℂ}
    (ha : a ≤ z.re) (hb : z.re ≤ b) (hs : 0 ≤ s) (k : ℕ) :
    (∃ L : StrongDual ℂ (StripSobolev a b s), ∀ F : SchwartzBergman (univ : Set ℝ),
      L (hardySobolevAnalyticTest a b s F) = iteratedDeriv k F.val z) ↔
      (a < z.re ∧ z.re < b) ∨ 2 * (k : ℝ) + 1 < s := by
  rw [← hardySobolev_mellinEvaluation_exists_iff ha hb hs k]
  constructor
  · rintro ⟨L, hL⟩
    refine ⟨L, fun f => ?_⟩
    specialize hL (hardySobolevTestMellin f)
    simpa only [hardySobolevAnalyticTest, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply,
      hardySobolevTestMellin_apply] using hL
  · rintro ⟨L, hL⟩
    refine ⟨L, fun F => ?_⟩
    obtain ⟨f, rfl⟩ := hardySobolevTestMellin.surjective F
    simpa only [hardySobolevAnalyticTest, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply,
      hardySobolevTestMellin_apply] using hL f


/-- Transport the supported test model to the analytic side of the Mellin map. -/
theorem hardySobolev_supportedAnalyticEvaluation_iff (a b s : ℝ) (U : Set ℝ)
    (k : ℕ) (z : ℂ) :
    (∃ L : StrongDual ℂ (supportedSobolevCompletion a b s U),
      ∀ (F : SchwartzBergman (univ : Set ℝ))
        (hF : ∀ x ∉ U, (hardySobolevTestMellin.symm F).val x = 0),
        L (supportedSobolevTest a b s U (hardySobolevTestMellin.symm F) hF) =
          iteratedDeriv k F.val z) ↔
    (∃ L : StrongDual ℂ (supportedSobolevCompletion a b s U),
      ∀ (f : PositiveRealExponentialDecay univ) (hf : ∀ x ∉ U, f.val x = 0),
        L (supportedSobolevTest a b s U f hf) =
          iteratedDeriv k (mellin fun t => f.val (Real.log t)) z) := by
  constructor
  · rintro ⟨L, hL⟩
    refine ⟨L, fun f hf => ?_⟩
    have hF : ∀ x ∉ U, (hardySobolevTestMellin.symm (hardySobolevTestMellin f)).val x = 0 := by
      rwa [ContinuousLinearEquiv.symm_apply_apply]
    have h := hL (hardySobolevTestMellin f) hF
    simpa only [ContinuousLinearEquiv.symm_apply_apply, hardySobolevTestMellin_apply] using h
  · rintro ⟨L, hL⟩
    refine ⟨L, fun F hF => ?_⟩
    obtain ⟨f, rfl⟩ := hardySobolevTestMellin.surjective F
    have hF' : ∀ x ∉ U, f.val x = 0 := by
      simpa only [ContinuousLinearEquiv.symm_apply_apply] using hF
    simpa only [ContinuousLinearEquiv.symm_apply_apply, hardySobolevTestMellin_apply] using hL f hF'

private theorem evenDegree_threshold (N k : ℕ) : 2 * (k : ℝ) + 1 < 2 * (N : ℝ) ↔ k < N := by
  have hNat : 2 * k + 1 < 2 * N ↔ k < N := by omega
  exact_mod_cast hNat

/-- Corollary 9.2.2.8 for compact bases. The lower multiplicative cutoff
is (1/A), and for even degree the endpoint orders are precisely (k<N). -/
theorem hardySobolev_cutoff_analyticEvaluation_iff {a b A : ℝ} (hA : 1 < A)
    {z : ℂ} (hz : z.re ≤ b) (N k : ℕ) :
    (∃ L : StrongDual ℂ (supportedSobolevCompletion a b (2 * (N : ℝ)) (Ioi (-Real.log A))),
      ∀ (F : SchwartzBergman (univ : Set ℝ))
        (hF : ∀ x ∉ Ioi (-Real.log A), (hardySobolevTestMellin.symm F).val x = 0),
        L (supportedSobolevTest a b (2 * (N : ℝ)) (Ioi (-Real.log A))
          (hardySobolevTestMellin.symm F) hF) = iteratedDeriv k F.val z) ↔
      z.re < b ∨ k < N := by
  rw [hardySobolev_supportedAnalyticEvaluation_iff, hardySobolev_cutoff_mellinEvaluation_exists_iff
    (neg_nonpos.mpr (Real.log_nonneg hA.le)) hz (by positivity)]
  rw [evenDegree_threshold]


/-- For a left half-line base, the corrected support already lies above the
lower cutoff (1/A) for (A>1). The endpoint condition is (k<N). -/
theorem hardySobolev_left_cutoff_analyticEvaluation_iff {b : ℝ} {z : ℂ}
    (hz : z.re ≤ b) (N k : ℕ) :
    (∃ L : StrongDual ℂ (supportedSobolevCompletion b b (2 * (N : ℝ)) (Ioi 0)),
      ∀ (F : SchwartzBergman (univ : Set ℝ))
        (hF : ∀ x ∉ Ioi (0 : ℝ), (hardySobolevTestMellin.symm F).val x = 0),
        L (supportedSobolevTest b b (2 * (N : ℝ)) (Ioi 0)
          (hardySobolevTestMellin.symm F) hF) = iteratedDeriv k F.val z) ↔
      z.re < b ∨ k < N := by
  rw [hardySobolev_supportedAnalyticEvaluation_iff,
    hardySobolev_left_mellinEvaluation_exists_iff hz (by positivity), evenDegree_threshold]

/-- For a right half-line base, the cutoff leaves bounded logarithmic
support. There is a derivative evaluation at every complex point. -/
theorem hardySobolev_right_cutoff_analyticEvaluation (a A : ℝ) (N k : ℕ) (z : ℂ) :
    ∃ L : StrongDual ℂ (supportedSobolevCompletion a a (2 * (N : ℝ)) (Ioo (-Real.log A) 0)),
      ∀ (F : SchwartzBergman (univ : Set ℝ))
        (hF : ∀ x ∉ Ioo (-Real.log A) (0 : ℝ), (hardySobolevTestMellin.symm F).val x = 0),
        L (supportedSobolevTest a a (2 * (N : ℝ)) (Ioo (-Real.log A) 0)
          (hardySobolevTestMellin.symm F) hF) = iteratedDeriv k F.val z := by
  rw [hardySobolev_supportedAnalyticEvaluation_iff]
  exact hardySobolev_right_cutoff_mellinEvaluation a (2 * (N : ℝ)) (-Real.log A) k z

end
end Masullo
