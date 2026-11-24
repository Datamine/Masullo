import HardySobolevHolomorphic
import RealFourierPlancherel

open Filter Function MeasureTheory Set Topology
open scoped ENNReal FourierTransform

namespace Masullo

noncomputable section

private abbrev Cutoff (a b c : ℝ) (N : ℕ) :=
  supportedSobolevCompletion a b (2 * (N : ℝ)) (Ioi c)

local notation "H" => (Lp ℂ 2 (volume : Measure ℝ))

private def mellinProfile {a b c : ℝ} {N : ℕ} (u : Cutoff a b c N)
    (k : ℕ) (r : ℝ) (x : ℝ) : ℂ :=
  u.val x * mellinEvaluationKernel k (r : ℂ) x

private def weightedCutoffProfile {a b c : ℝ} {N : ℕ} (u : Cutoff a b c N) (x : ℝ) : ℂ :=
  stripSobolevAmplitude a b (2 * (N : ℝ)) x • u.val x

private theorem weightedCutoffProfile_memLp {a b c : ℝ} {N : ℕ} (u : Cutoff a b c N) :
    MemLp (weightedCutoffProfile u) 2 volume := by
  let s := 2 * (N : ℝ)
  let A := stripSobolevAmplitude a b s
  have hA := (stripSobolevAmplitude_continuous a b s).measurable
  have hu : AEStronglyMeasurable (u.val : ℝ → ℂ) volume :=
    (Lp.aestronglyMeasurable u.val).mono_ac
      (absolutelyContinuous_amplitudeMeasure volume A hA (stripSobolevAmplitude_pos a b s))
  exact (memLp_amplitudeMeasure_iff volume A hA hu).mp (Lp.memLp u.val)

private theorem mellinProfile_aestronglyMeasurable {a b c : ℝ} {N : ℕ} (u : Cutoff a b c N)
    (k : ℕ) (r : ℝ) : AEStronglyMeasurable (mellinProfile u k r) volume := by
  have hu : AEStronglyMeasurable (u.val : ℝ → ℂ) volume :=
    (Lp.aestronglyMeasurable u.val).mono_ac (absolutelyContinuous_amplitudeMeasure volume _
      (stripSobolevAmplitude_continuous a b (2 * (N : ℝ))).measurable
      (stripSobolevAmplitude_pos a b (2 * (N : ℝ))))
  apply hu.mul
  apply Continuous.aestronglyMeasurable
  unfold mellinEvaluationKernel
  fun_prop

private theorem mellinProfile_norm_le {a b c r : ℝ} (hab : a ≤ b) (hr : r ≤ b)
    {N k : ℕ} (hk : k ≤ N) (u : Cutoff a b c N) :
    ∀ᵐ x : ℝ ∂volume, ‖mellinProfile u k r x‖ ≤
      Real.exp ((r - b) * c) * ‖weightedCutoffProfile u x‖ := by
  have hu := (mem_supportedSobolevCompletion_iff a b (2 * (N : ℝ)) isOpen_Ioi u.val).mp u.property
  filter_upwards [hu] with x hx
  by_cases hcut : x ∈ Ioi c
  · have hx' : c ≤ x := (show c < x from hcut).le
    have hex : Real.exp (r * x) ≤ Real.exp ((r - b) * c) * Real.exp (b * x) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have h := mul_le_mul_of_nonpos_left hx' (sub_nonpos.mpr hr)
      linarith
    have hpoly : ‖x‖ ^ k ≤ Real.sqrt ((1 + x ^ 2) ^ N) := by
      apply le_of_pow_le_pow_left₀ (n := 2) (by decide) (Real.sqrt_nonneg _)
      rw [Real.sq_sqrt (by positivity)]
      rw [show (‖x‖ ^ k) ^ 2 = (x ^ 2) ^ k by
        rw [← pow_mul, Nat.mul_comm, pow_mul, Real.norm_eq_abs, sq_abs]]
      exact (pow_le_pow_left₀ (sq_nonneg _) (le_add_of_nonneg_left zero_le_one) k).trans
        (pow_le_pow_right₀ (le_add_of_nonneg_right (sq_nonneg _)) hk)
    have hAmp : Real.exp (b * x) * Real.sqrt ((1 + x ^ 2) ^ N) ≤
        stripSobolevAmplitude a b (2 * (N : ℝ)) x := by
      apply le_of_pow_le_pow_left₀ (n := 2) (by decide) (stripSobolevAmplitude_pos a b _ x).le
      rw [mul_pow, Real.sq_sqrt (by positivity), ← Real.exp_nat_mul, stripSobolevAmplitude_sq hab]
      have hrN : 2 * (N : ℝ) / 2 = (N : ℝ) := by ring
      rw [hardySobolevWeight, hrN, Real.rpow_natCast]
      push_cast
      rw [show 2 * (b * x) = 2 * b * x by ring]
      exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
    simp only [mellinProfile, norm_mul, mellinEvaluationKernel_norm, Complex.ofReal_re,
      weightedCutoffProfile, norm_smul, Real.norm_of_nonneg (stripSobolevAmplitude_pos a b _ x).le]
    calc
      _ ≤ ‖u.val x‖ * ((Real.exp ((r - b) * c) * Real.exp (b * x)) *
          Real.sqrt ((1 + x ^ 2) ^ N)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hex hpoly (by positivity) (by positivity)) (norm_nonneg _)
      _ = Real.exp ((r - b) * c) * ((Real.exp (b * x) * Real.sqrt ((1 + x ^ 2) ^ N)) * ‖u.val x‖) := by ring
      _ ≤ _ := by gcongr
  · simp [mellinProfile, weightedCutoffProfile, hx hcut]

private theorem mellinProfile_memLp {a b c r : ℝ} (hab : a ≤ b) (hr : r ≤ b)
    {N k : ℕ} (hk : k ≤ N) (u : Cutoff a b c N) :
    MemLp (mellinProfile u k r) 2 volume := by
  apply ((weightedCutoffProfile_memLp u).norm.const_mul (Real.exp ((r - b) * c))).mono'
    (mellinProfile_aestronglyMeasurable u k r)
  filter_upwards [mellinProfile_norm_le hab hr hk u] with x hx
  simpa only [Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))] using hx

private def cutoffMellinProfileL2 {a b c : ℝ} (hab : a ≤ b) {N k : ℕ} (hk : k ≤ N)
    (u : Cutoff a b c N) (r : Iic b) : H :=
  (mellinProfile_memLp hab r.property hk u).toLp _

/-- The derivative trace in the Fourier frequency variable, completed at the
endpoint even when the Mellin moment has no absolutely convergent integral. -/
def cutoffMellinTraceL2 {a b c : ℝ} (hab : a ≤ b) {N k : ℕ} (hk : k ≤ N)
    (u : Cutoff a b c N) (r : Iic b) : H :=
  realFourierL2 (cutoffMellinProfileL2 hab hk u r)

/-- Exact Plancherel energy in the normalized frequency variable, including
the highest-order endpoint trace. -/
theorem cutoffMellinTraceL2_norm_sq {a b c : ℝ} (hab : a ≤ b) {N k : ℕ} (hk : k ≤ N)
    (u : Cutoff a b c N) (r : Iic b) :
    ‖cutoffMellinTraceL2 hab hk u r‖ ^ 2 =
      ∫ x : ℝ, ‖u.val x‖ ^ 2 * (Real.exp (2 * r.val * x) * (x ^ 2) ^ k) := by
  unfold cutoffMellinTraceL2 cutoffMellinProfileL2
  rw [realFourierL2.norm_map, norm_sq_toLp_two]
  apply integral_congr_ae
  refine .of_forall fun x => ?_
  change ‖mellinProfile u k r.val x‖ ^ 2 = _
  have hp : (‖x‖ ^ k) ^ 2 = (x ^ 2) ^ k := by
    rw [← pow_mul, Nat.mul_comm, pow_mul, Real.norm_eq_abs, sq_abs]
  simp only [mellinProfile, norm_mul, mellinEvaluationKernel_norm, Complex.ofReal_re,
    mul_pow, hp, ← Real.exp_nat_mul]
  push_cast
  ring_nf

private theorem continuousAt_cutoffMellinProfileL2_endpoint {a b c : ℝ} (hab : a ≤ b) (hc : c ≤ 0)
    {N k : ℕ} (hk : k ≤ N) (u : Cutoff a b c N) :
    ContinuousAt (cutoffMellinProfileL2 hab hk u) (⟨b, mem_Iic.mpr le_rfl⟩ : Iic b) := by
  let e : Iic b := ⟨b, mem_Iic.mpr le_rfl⟩
  let P := cutoffMellinProfileL2 hab hk u
  let M (r : Iic b) := mellinProfile u k r.val
  let w := weightedCutoffProfile u
  let C := Real.exp (-c)
  have hC : 1 ≤ C := by dsimp [C]; exact Real.one_le_exp (neg_nonneg.mpr hc)
  have hNear : ∀ᶠ r : Iic b in 𝓝 e, b - 1 < (r : ℝ) :=
    (continuous_subtype_val.tendsto e).eventually
      (Ioi_mem_nhds (show b - 1 < (e : ℝ) by dsimp [e]; linarith))
  have hDom : Integrable (fun x => ((2 * C) * ‖w x‖) ^ 2) := by
    have hw := weightedCutoffProfile_memLp u
    have hm := (memLp_two_iff_integrable_sq_norm hw.aestronglyMeasurable).mp hw
    refine (hm.const_mul ((2 * C) ^ 2)).congr (.of_forall fun x => ?_)
    change (2 * C) ^ 2 * ‖w x‖ ^ 2 = ((2 * C) * ‖w x‖) ^ 2
    ring
  have hMeas (r : Iic b) : AEStronglyMeasurable (fun x => ‖M r x - M e x‖ ^ 2) volume :=
    (((mellinProfile_aestronglyMeasurable u k r.val).sub
      (mellinProfile_aestronglyMeasurable u k e.val)).norm.pow 2)
  have hInt : Tendsto (fun r => ∫ x, ‖M r x - M e x‖ ^ 2) (𝓝 e) (𝓝 0) := by
    have he := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (l := 𝓝 e) (μ := (volume : Measure ℝ))
      (F := fun (r : Iic b) x => ‖M r x - M e x‖ ^ 2) (f := fun _ => (0 : ℝ))
      (fun x => ((2 * C) * ‖w x‖) ^ 2) (.of_forall hMeas) ?_ hDom ?_
    · simpa using he
    · filter_upwards [hNear] with r hr
      have hExp : Real.exp (((r : ℝ) - b) * c) ≤ C := by
        dsimp [C]
        apply Real.exp_le_exp.mpr
        have hn : -(1 : ℝ) ≤ (r : ℝ) - b := by linarith
        simpa using mul_le_mul_of_nonpos_right hn hc
      filter_upwards [mellinProfile_norm_le hab r.property hk u,
        mellinProfile_norm_le hab (r := b) le_rfl hk u] with x h₁ h₂
      have h₂' : ‖M e x‖ ≤ ‖w x‖ := by simpa [M, e, w] using h₂
      have h₁' : ‖M r x‖ ≤ C * ‖w x‖ :=
        h₁.trans (mul_le_mul_of_nonneg_right hExp (norm_nonneg _))
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      apply pow_le_pow_left₀ (norm_nonneg _)
      calc
        ‖M r x - M e x‖ ≤ ‖M r x‖ + ‖M e x‖ := norm_sub_le _ _
        _ ≤ C * ‖w x‖ + C * ‖w x‖ := add_le_add h₁'
          (h₂'.trans (le_mul_of_one_le_left (norm_nonneg _) hC))
        _ = _ := by ring
    · exact .of_forall fun x => by
        have hcM : Continuous (fun r : Iic b => M r x) := by
          dsimp [M, mellinProfile, mellinEvaluationKernel]
          fun_prop
        simpa using ((hcM.continuousAt (x := e).tendsto.sub (tendsto_const_nhds (x := M e x))).norm.pow 2)
  have hsq (r : Iic b) : ‖P r - P e‖ ^ 2 = ∫ x, ‖M r x - M e x‖ ^ 2 := by
    let hr := mellinProfile_memLp hab r.property hk u
    let he := mellinProfile_memLp hab e.property hk u
    have heq : P r - P e = (hr.sub he).toLp (M r - M e) := by
      apply Lp.ext
      filter_upwards [Lp.coeFn_sub (P r) (P e), hr.coeFn_toLp, he.coeFn_toLp,
        (hr.sub he).coeFn_toLp] with x hx h₁ h₂ hd
      have h₁' : P r x = M r x := h₁
      have h₂' : P e x = M e x := h₂
      rw [hx, hd, Pi.sub_apply, Pi.sub_apply, h₁', h₂']
    rw [heq, norm_sq_toLp_two (hr.sub he)]
    rfl
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have ht := Real.continuous_sqrt.continuousAt.tendsto.comp hInt
  simpa only [Function.comp_def, ← hsq, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _),
    Real.sqrt_zero] using ht

/-- Every derivative trace through order N has a strong L² limit at the endpoint. -/
theorem continuousAt_cutoffMellinTraceL2_endpoint {a b c : ℝ} (hab : a ≤ b) (hc : c ≤ 0)
    {N k : ℕ} (hk : k ≤ N) (u : Cutoff a b c N) :
    ContinuousAt (cutoffMellinTraceL2 hab hk u) (⟨b, mem_Iic.mpr le_rfl⟩ : Iic b) :=
  realFourierL2.continuous.continuousAt.comp (continuousAt_cutoffMellinProfileL2_endpoint hab hc hk u)

private theorem fourier_mellinProfile_eq {a b c : ℝ} {N : ℕ}
    (u : Cutoff a b c N) (k : ℕ) (r y : ℝ) :
    𝓕 (mellinProfile u k r) y =
      cutoffMellinIntegral u.val k ((r : ℂ) - ((2 * Real.pi * y : ℝ) : ℂ) * Complex.I) := by
  rw [Real.fourier_eq', cutoffMellinIntegral]
  apply integral_congr_ae
  refine .of_forall fun x => ?_
  simp only [mellinProfile, mellinEvaluationKernel, Real.inner_apply, smul_eq_mul]
  rw [sub_mul, Complex.exp_sub, div_eq_mul_inv, ← Complex.exp_neg]
  push_cast
  ring_nf

/-- The L² trace agrees with the actual Mellin integral on every interior line
and at the integrable endpoint orders, in the variable `y ↦ r - 2πiy`. -/
theorem cutoffMellinTraceL2_ae_eq_integral {a b c : ℝ} (hab : a ≤ b) (hc : c ≤ 0)
    {N k : ℕ} (hk : k ≤ N) (u : Cutoff a b c N) (r : Iic b)
    (hEval : (r : ℝ) < b ∨ 2 * (k : ℝ) + 1 < 2 * (N : ℝ)) :
    (cutoffMellinTraceL2 hab hk u r : ℝ → ℂ) =ᵐ[volume]
      fun y => cutoffMellinIntegral u.val k ((r.val : ℂ) - ((2 * Real.pi * y : ℝ) : ℂ) * Complex.I) := by
  have hP : (cutoffMellinProfileL2 hab hk u r : ℝ → ℂ) =ᵐ[volume] mellinProfile u k r.val :=
    (mellinProfile_memLp hab r.property hk u).coeFn_toLp
  have hI : Integrable (mellinProfile u k r.val) :=
    ((cutoffSobolev_mellinMoment_functional_of_le hc (by positivity) (z := (r.val : ℂ))
      r.property k hEval).choose_spec u).1
  exact (realFourierL2_ae_eq_fourier _ (hI.congr hP.symm)).trans
    (.of_forall fun y => (Real.fourier_congr_ae hP y).trans (fourier_mellinProfile_eq u k r.val y))

/-- On the open half-plane the actual holomorphic derivative is the
representative of the completed trace. -/
theorem cutoffMellinTraceL2_ae_eq_derivative {a b c : ℝ} (hab : a ≤ b) (hc : c ≤ 0)
    {N k : ℕ} (hk : k ≤ N) (u : Cutoff a b c N) (r : Iic b) (hr : (r : ℝ) < b) :
    (cutoffMellinTraceL2 hab hk u r : ℝ → ℂ) =ᵐ[volume]
      fun y => iteratedDeriv k (cutoffMellinIntegral u.val 0)
        ((r.val : ℂ) - ((2 * Real.pi * y : ℝ) : ℂ) * Complex.I) :=
  (cutoffMellinTraceL2_ae_eq_integral hab hc hk u r (Or.inl hr)).trans (.of_forall fun y =>
    (iteratedDeriv_cutoffMellinIntegral hc (by positivity) u k
      (by simpa [Complex.sub_re, Complex.mul_re] using hr)).symm)

/-- The completed endpoint energy with binomial weights is the squared
weighted Sobolev norm. -/
theorem cutoffMellinTraceL2_endpoint_norm_sum {b c : ℝ} {N : ℕ} (u : Cutoff b b c N) :
    (∑ k : Fin (N + 1), (N.choose (k : ℕ) : ℝ) *
      ‖cutoffMellinTraceL2 le_rfl (Nat.lt_succ_iff.mp k.isLt) u ⟨b, mem_Iic.mpr le_rfl⟩‖ ^ 2) =
        ‖u‖ ^ 2 := by
  let A := stripSobolevAmplitude b b (2 * (N : ℝ))
  let V := amplitudeL2Iso volume A (stripSobolevAmplitude_continuous b b _).measurable
    (stripSobolevAmplitude_pos b b _)
  have hV : ‖u‖ ^ 2 = ∫ x, ‖weightedCutoffProfile u x‖ ^ 2 := by
    have hv : ‖V u.val‖ ^ 2 = ∫ x, ‖V u.val x‖ ^ 2 := by
      simpa only [Lp.toLp_coeFn] using norm_sq_toLp_two (Lp.memLp (V u.val))
    rw [← show ‖V u.val‖ = ‖u‖ from V.norm_map u.val, hv]
    apply integral_congr_ae
    filter_upwards [amplitudeL2Iso_ae volume A (stripSobolevAmplitude_continuous b b _).measurable
      (stripSobolevAmplitude_pos b b _) u.val] with x hx
    rw [hx]
    rfl
  simp_rw [cutoffMellinTraceL2_norm_sq, ← integral_const_mul]
  rw [← integral_finsetSum, hV]
  · apply integral_congr_ae
    refine .of_forall fun x => ?_
    simp only [weightedCutoffProfile, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
      stripSobolevAmplitude_sq le_rfl, hardySobolevWeight, max_self]
    rw [show 2 * (N : ℝ) / 2 = (N : ℝ) by ring, Real.rpow_natCast]
    have he : ∀ j : Fin (N + 1),
        (N.choose (j : ℕ) : ℝ) * (‖u.val x‖ ^ 2 * (Real.exp (2 * b * x) * (x ^ 2) ^ (j : ℕ))) =
        (‖u.val x‖ ^ 2 * Real.exp (2 * b * x)) * ((x ^ 2) ^ (j : ℕ) * N.choose (j : ℕ)) :=
      fun j => by ring
    simp_rw [he, ← Finset.mul_sum]
    rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => (x ^ 2) ^ k * N.choose k)]
    have hbin := add_pow (x ^ 2) (1 : ℝ) N
    simp only [one_pow, mul_one] at hbin
    rw [← hbin, add_comm (x ^ 2) 1]
    ring
  · intro k _
    have hp := mellinProfile_memLp (a := b) (b := b) (r := b) le_rfl le_rfl
      (Nat.lt_succ_iff.mp k.isLt) u
    have hi := (memLp_two_iff_integrable_sq_norm hp.aestronglyMeasurable).mp hp
    refine (hi.const_mul (N.choose (k : ℕ) : ℝ)).congr (.of_forall fun x => ?_)
    change (N.choose (k : ℕ) : ℝ) * ‖mellinProfile u k b x‖ ^ 2 = _
    have hp' : (‖x‖ ^ (k : ℕ)) ^ 2 = (x ^ 2) ^ (k : ℕ) := by
      rw [← pow_mul, Nat.mul_comm, pow_mul, Real.norm_eq_abs, sq_abs]
    simp only [mellinProfile, norm_mul, mellinEvaluationKernel_norm, Complex.ofReal_re,
      mul_pow, hp', ← Real.exp_nat_mul]
    push_cast
    ring_nf

/-- Conversion from normalized Fourier frequency to the manuscript's
vertical height on every interior line. -/
theorem cutoffMellinTraceL2_physical_energy {a b c : ℝ} (hab : a ≤ b) (hc : c ≤ 0)
    {N k : ℕ} (hk : k ≤ N) (u : Cutoff a b c N) (r : Iic b) (hr : r.val < b) :
    ‖cutoffMellinTraceL2 hab hk u r‖ ^ 2 =
      (2 * Real.pi)⁻¹ * ∫ y : ℝ, ‖iteratedDeriv k (cutoffMellinIntegral u.val 0) (⟨r.val, y⟩ : ℂ)‖ ^ 2 := by
  let T := cutoffMellinTraceL2 hab hk u r
  have hn : ‖T‖ ^ 2 = ∫ x : ℝ, ‖T x‖ ^ 2 := by
    simpa only [Lp.toLp_coeFn] using norm_sq_toLp_two (Lp.memLp T)
  change ‖T‖ ^ 2 = _
  rw [hn]
  calc
    _ = ∫ y : ℝ, ‖iteratedDeriv k (cutoffMellinIntegral u.val 0)
        (⟨r.val, -(2 * Real.pi) * y⟩ : ℂ)‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [cutoffMellinTraceL2_ae_eq_derivative hab hc hk u r hr] with y hy
      have hz : (r.val : ℂ) - (↑(2 * Real.pi * y) : ℂ) * Complex.I =
          (⟨r.val, -(2 * Real.pi) * y⟩ : ℂ) := by
        apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
      change T y = _ at hy
      rw [hy, hz]
    _ = _ := (Measure.integral_comp_mul_left (fun y =>
        ‖iteratedDeriv k (cutoffMellinIntegral u.val 0) (⟨r.val, y⟩ : ℂ)‖ ^ 2)
        (-(2 * Real.pi))).trans (by
          rw [abs_inv, abs_neg, abs_of_pos (by positivity : 0 < 2 * Real.pi)]; rfl)

/-- On the positive logarithmic ray the boundary energy is the supremum
over the open left half-plane, in the manuscript's physical height. -/
theorem positiveCutoff_mellin_energy_isLUB {b : ℝ} {N k : ℕ} (hk : k ≤ N) (u : Cutoff b b 0 N) :
    IsLUB {E : ℝ | ∃ r < b,
      E = ∫ y : ℝ, ‖iteratedDeriv k (cutoffMellinIntegral u.val 0) (⟨r, y⟩ : ℂ)‖ ^ 2}
      ((2 * Real.pi) * ‖cutoffMellinTraceL2 le_rfl hk u ⟨b, mem_Iic.mpr le_rfl⟩‖ ^ 2) := by
  let e : Iic b := ⟨b, mem_Iic.mpr le_rfl⟩
  let P := cutoffMellinTraceL2 le_rfl hk u
  let f (r : ℝ) (x : ℝ) := ‖u.val x‖ ^ 2 * (Real.exp (2 * r * x) * (x ^ 2) ^ k)
  let E (r : ℝ) := ∫ y : ℝ, ‖iteratedDeriv k (cutoffMellinIntegral u.val 0) (⟨r, y⟩ : ℂ)‖ ^ 2
  have hE (r : Iic b) (hr : r.val < b) : E r.val = (2 * Real.pi) * ‖P r‖ ^ 2 := by
    rw [cutoffMellinTraceL2_physical_energy le_rfl le_rfl hk u r hr]
    change E r.val = (2 * Real.pi) * ((2 * Real.pi)⁻¹ * E r.val)
    rw [← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]
  have hi (r : Iic b) : Integrable (f r.val) := by
    have hp := mellinProfile_memLp le_rfl r.property hk u
    have hI := (memLp_two_iff_integrable_sq_norm hp.aestronglyMeasurable).mp hp
    refine hI.congr (.of_forall fun x => ?_)
    have hz : (‖x‖ ^ k) ^ 2 = (x ^ 2) ^ k := by
      rw [← pow_mul, Nat.mul_comm, pow_mul, Real.norm_eq_abs, sq_abs]
    simp only [mellinProfile, norm_mul, mellinEvaluationKernel_norm, Complex.ofReal_re,
      mul_pow, hz, ← Real.exp_nat_mul, f]
    push_cast
    ring_nf
  constructor
  · rintro A ⟨r, hr, rfl⟩
    let R : Iic b := ⟨r, mem_Iic.mpr hr.le⟩
    change E r ≤ (2 * Real.pi) * ‖P e‖ ^ 2
    rw [show E r = (2 * Real.pi) * ‖P R‖ ^ 2 from hE R hr]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [cutoffMellinTraceL2_norm_sq, cutoffMellinTraceL2_norm_sq]
    apply integral_mono_ae (hi R) (hi e)
    have hu := (mem_supportedSobolevCompletion_iff b b (2 * (N : ℝ)) isOpen_Ioi u.val).mp u.property
    filter_upwards [hu] with x hx
    show f r x ≤ f b x
    by_cases h : 0 < x
    · have hb : Real.exp (2 * r * x) ≤ Real.exp (2 * b * x) := by
        exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by linarith) h.le)
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hb (by positivity)) (sq_nonneg _)
    · simp [f, hx h]
  · intro A hA
    have hA' (r : ℝ) (hr : r < b) : E r ≤ A := hA ⟨r, hr, rfl⟩
    let t (n : ℕ) : Iic b := ⟨b - 1 / ((n : ℝ) + 1), mem_Iic.mpr (sub_le_self _ (by positivity))⟩
    have htb (n : ℕ) : (t n).val < b := sub_lt_self _ (by positivity)
    have ht : Tendsto t atTop (𝓝 e) := by
      apply tendsto_subtype_rng.mpr
      simpa only [t, e, sub_zero] using
        (tendsto_const_nhds (x := b)).sub (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    have hlim : Tendsto (fun n => (2 * Real.pi) * ‖P (t n)‖ ^ 2) atTop
        (𝓝 ((2 * Real.pi) * ‖P e‖ ^ 2)) :=
      (((continuousAt_cutoffMellinTraceL2_endpoint le_rfl le_rfl hk u).tendsto.comp ht).norm.pow 2).const_mul _
    exact le_of_tendsto' hlim fun n => (hE (t n) (htb n)) ▸ hA' (t n).val (htb n)

end
end Masullo
