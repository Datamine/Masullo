import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Complex.SummableUniformlyOn
import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn

open Filter MeasureTheory Set Topology
open scoped FourierTransform

namespace Masullo

/-- Counterexample to the disc-containment step in Lemma B.5.3.4(2).
The compact set consisting of the points at heights ±2 lies in the strip,
but no closed disc contained in the strip contains both points. -/
theorem tall_compact_not_in_strip_disc (c : ℂ) (r : ℝ)
    (hdisc : Metric.closedBall c r ⊆ {z : ℂ | -1 < z.re ∧ z.re < 1}) :
    ¬ ((2 : ℂ) * Complex.I ∈ Metric.closedBall c r ∧
      -(2 : ℂ) * Complex.I ∈ Metric.closedBall c r) := by
  rintro ⟨hpositive, hnegative⟩
  have hr : 0 ≤ r := (dist_nonneg (x := (2 : ℂ) * Complex.I)).trans hpositive
  have hrplus : c + (r : ℂ) ∈ Metric.closedBall c r := by
    rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hr]
  have hrminus : c - (r : ℂ) ∈ Metric.closedBall c r := by
    rw [Metric.mem_closedBall, dist_eq_norm, sub_sub_cancel_left, norm_neg, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hr]
  have hplus := (hdisc hrplus).2
  have hminus := (hdisc hrminus).1
  simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re] at hplus hminus
  have hd : dist ((2 : ℂ) * Complex.I) (-(2 : ℂ) * Complex.I) = 4 := by
    rw [dist_eq_norm, show (2 : ℂ) * Complex.I - -(2 : ℂ) * Complex.I = 4 * Complex.I by ring,
      norm_mul, Complex.norm_I, mul_one]
    norm_num
  have htri := dist_triangle ((2 : ℂ) * Complex.I) c (-(2 : ℂ) * Complex.I)
  rw [hd, dist_comm c] at htri
  have h₁ : dist ((2 : ℂ) * Complex.I) c ≤ r := hpositive
  have h₂ : dist (-(2 : ℂ) * Complex.I) c ≤ r := hnegative
  linarith

/-- One zero's contribution for the limiting test in §1.8.4.2, with
w = ρ - 1/2. The exponent includes the Haar density dt/t. -/
theorem integral_one_sided_mellin (z w : ℂ) (h : w.re < z.re) :
    (∫ t : ℝ in Ioi 1, (t : ℂ) ^ (w - z - 1)) = (z - w)⁻¹ := by
  rw [integral_Ioi_cpow_of_lt (by simp; linarith) zero_lt_one]
  simp only [Complex.ofReal_one, Complex.one_cpow, sub_add_cancel]
  rw [← neg_sub, div_neg, neg_div, neg_neg, one_div]

/-- Subtracting a fixed reference exponent makes the limiting test vanish
at the identity. Its spectral kernel is a difference of resolvents. -/
theorem integral_subtracted_mellin (z b w : ℂ) (hz : w.re < z.re) (hb : w.re < b.re) :
    (∫ t : ℝ in Ioi 1, ((t : ℂ) ^ (w - z - 1) - (t : ℂ) ^ (w - b - 1))) =
      (z - w)⁻¹ - (b - w)⁻¹ := by
  rw [integral_sub
    (integrableOn_Ioi_cpow_of_lt (by simp; linarith) zero_lt_one)
    (integrableOn_Ioi_cpow_of_lt (by simp; linarith) zero_lt_one),
    integral_one_sided_mellin z w hz, integral_one_sided_mellin b w hb]

/-- Smoothness is irrelevant to termwise removal of the logarithmic cutoffs.
It will enter when bounding the Fourier transforms simultaneously in the zero index. -/
theorem spectralLaplaceCutoff_tendsto (z b w : ℂ)
    (hz : w.re < z.re) (hb : w.re < b.re)
    (cutoff : ℕ → ℝ → ℝ) (hm : ∀ n, Measurable (cutoff n))
    (hcut : ∀ n x, cutoff n x ∈ Icc (0 : ℝ) 1)
    (hlim : ∀ x > 0, Tendsto (fun n => cutoff n x) atTop (𝓝 1)) :
    Tendsto (fun n => ∫ x in Ioi (0 : ℝ), (cutoff n x : ℂ) *
      (Complex.exp ((w - z) * (x : ℂ)) - Complex.exp ((w - b) * (x : ℂ))))
      atTop (𝓝 ((z - w)⁻¹ - (b - w)⁻¹)) := by
  let μ := volume.restrict (Ioi (0 : ℝ))
  let f (x : ℝ) := Complex.exp ((w - z) * (x : ℂ)) - Complex.exp ((w - b) * (x : ℂ))
  have hz' : (w - z).re < 0 := by simp; linarith
  have hb' : (w - b).re < 0 := by simp; linarith
  have hfz := integrableOn_exp_mul_complex_Ioi hz' 0
  have hfb := integrableOn_exp_mul_complex_Ioi hb' 0
  have hi : Integrable f μ := hfz.sub hfb
  have heval : (∫ x, f x ∂μ) = (z - w)⁻¹ - (b - w)⁻¹ := by
    change (∫ x in Ioi (0 : ℝ), Complex.exp ((w - z) * (x : ℂ)) -
      Complex.exp ((w - b) * (x : ℂ))) = _
    rw [integral_sub hfz hfb, integral_exp_mul_complex_Ioi hz', integral_exp_mul_complex_Ioi hb']
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
    simp only [neg_div, one_div, ← inv_neg, neg_sub]
  rw [← heval]
  apply tendsto_integral_of_dominated_convergence (‖f ·‖)
  · intro n
    exact ((Complex.continuous_ofReal.measurable.comp (hm n)).aestronglyMeasurable.mul hi.1)
  · exact hi.norm
  · intro n
    exact Eventually.of_forall fun x => by
      have h := hcut n x
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h.1]
      exact mul_le_of_le_one_left (norm_nonneg _) h.2
  · filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with x hx
    have h : Tendsto (fun n => (cutoff n x : ℂ)) atTop (𝓝 (1 : ℂ)) := by
      simpa only [Complex.ofReal_one] using (hlim x hx).ofReal
    simpa only [one_mul] using h.mul_const (f x)

/-- The subtracted kernel has inverse-square decay at large imaginary heights.
The bound is uniform if the test parameters range over a bounded set. -/
theorem norm_subtracted_resolvent_le (z b w : ℂ) (hw : 0 < |w.im|)
    (hz : 2 * |z.im| ≤ |w.im|) (hb : 2 * |b.im| ≤ |w.im|) :
    ‖(z - w)⁻¹ - (b - w)⁻¹‖ ≤ 4 * ‖b - z‖ / |w.im| ^ 2 := by
  have distance_lower (u : ℂ) (hu : 2 * |u.im| ≤ |w.im|) :
      |w.im| / 2 ≤ ‖u - w‖ := by
    have htriangle : |w.im| ≤ |u.im| + |u.im - w.im| := by
      calc
        |w.im| = |u.im - (u.im - w.im)| := by congr 1; ring
        _ ≤ |u.im| + |u.im - w.im| := abs_sub _ _
    have hn := Complex.abs_im_le_norm (u - w)
    rw [Complex.sub_im] at hn
    linarith
  have hzdist := distance_lower z hz
  have hbdist := distance_lower b hb
  have hzne : z - w ≠ 0 := norm_pos_iff.mp (by linarith)
  have hbne : b - w ≠ 0 := norm_pos_iff.mp (by linarith)
  have identity : (z - w)⁻¹ - (b - w)⁻¹ = (b - z) / ((z - w) * (b - w)) := by
    field_simp
    ring
  rw [identity, norm_div, norm_mul]
  have hden : (|w.im| / 2) ^ 2 ≤ ‖z - w‖ * ‖b - w‖ := by
    rw [pow_two]
    exact mul_le_mul hzdist hbdist (by positivity) (norm_nonneg _)
  calc
    _ ≤ ‖b - z‖ / (|w.im| / 2) ^ 2 :=
      div_le_div_of_nonneg_left (norm_nonneg _) (by positivity) hden
    _ = _ := by
      field_simp
      ring

/-- Normal convergence and holomorphy of the complete subtracted zero sum in a
right half-plane. Heights are counted with the supplied multiplicities. -/
theorem subtracted_zero_sum_holomorphic {ι : Type*} (w : ι → ℂ)
    (multiplicity : ι → ℕ) {edge : ℝ} (hwidth : ∀ i, (w i).re ≤ edge)
    (b : ℂ)
    (hfinite : ∀ H : ℝ, {i | |(w i).im| ≤ H}.Finite)
    (hcount : Summable (fun i => (multiplicity i : ℝ) / |(w i).im| ^ 2)) :
    SummableLocallyUniformlyOn
      (fun i z => (multiplicity i : ℂ) * ((z - w i)⁻¹ - (b - w i)⁻¹))
      {z | edge < z.re} ∧
    DifferentiableOn ℂ
      (fun z => ∑' i, (multiplicity i : ℂ) * ((z - w i)⁻¹ - (b - w i)⁻¹))
      {z | edge < z.re} := by
  have hopen : IsOpen {z : ℂ | edge < z.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hsum : SummableLocallyUniformlyOn
      (fun i z => (multiplicity i : ℂ) * ((z - w i)⁻¹ - (b - w i)⁻¹))
      {z | edge < z.re} := by
    apply SummableLocallyUniformlyOn.of_locally_bounded_eventually hopen
    intro K _ hK
    obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
    let M := max R ‖b‖
    have hM : 0 ≤ M := (norm_nonneg b).trans (le_max_right _ _)
    refine ⟨fun i => (8 * M) * ((multiplicity i : ℝ) / |(w i).im| ^ 2),
      hcount.mul_left _, ?_⟩
    have hlarge : ∀ᶠ i in cofinite, 2 * M < |(w i).im| := by
      rw [eventually_cofinite]
      simpa only [not_lt] using hfinite (2 * M)
    filter_upwards [hlarge] with i hi z hz
    have hzM : ‖z‖ ≤ M := (hR z hz).trans (le_max_left _ _)
    have hbM : ‖b‖ ≤ M := le_max_right _ _
    have hdiff : ‖b - z‖ ≤ 2 * M := (norm_sub_le b z).trans (by linarith)
    rw [norm_mul, Complex.norm_natCast]
    calc
      _ ≤ (multiplicity i : ℝ) * (4 * ‖b - z‖ / |(w i).im| ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        exact norm_subtracted_resolvent_le z b (w i) (by linarith)
          (by linarith [Complex.abs_im_le_norm z]) (by linarith [Complex.abs_im_le_norm b])
      _ = (4 * ‖b - z‖) * ((multiplicity i : ℝ) / |(w i).im| ^ 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  refine ⟨hsum, hsum.differentiableOn hopen ?_⟩
  intro i z hz
  have hz' : z - w i ≠ 0 := sub_ne_zero.mpr fun h => by
    change edge < z.re at hz
    exact (not_lt_of_ge (hwidth i)) (h ▸ hz)
  have hlinear : DifferentiableAt ℂ (fun v : ℂ => v - w i) z := by fun_prop
  have hinv : DifferentiableAt ℂ (fun v : ℂ => (v - w i)⁻¹) z := hlinear.inv hz'
  exact (hinv.sub_const ((b - w i)⁻¹)).const_mul (multiplicity i : ℂ)

theorem norm_fourier_le_integral {g : ℝ → ℂ} (hg : Integrable g) (y : ℝ) :
  ‖𝓕 g y‖ ≤ ∫ x, ‖g x‖ := by
  rw [Real.fourier_eq']
  apply norm_integral_le_of_norm_le hg.norm
  exact Eventually.of_forall fun x => by
    rw [norm_smul, Complex.norm_exp]
    simp

/-- Two integrations by parts give the frequency bound used for cutoff removal.
Integrability of both derivatives keeps the boundary terms under control. -/
theorem norm_fourier_le_of_second_deriv {f : ℝ → ℂ}
    (hf : Integrable f) (hd₁ : Differentiable ℝ f)
    (hf₁ : Integrable (deriv f)) (hd₂ : Differentiable ℝ (deriv f))
    (hf₂ : Integrable (deriv (deriv f))) (y : ℝ) :
    (2 * Real.pi * |y|) ^ 2 * ‖𝓕 f y‖ ≤ ∫ x, ‖deriv (deriv f) x‖ := by
  have h₁ := congrFun (Real.fourier_deriv hf hd₁ hf₁) y
  have h₂ := congrFun (Real.fourier_deriv hf₁ hd₂ hf₂) y
  calc
    _ = ‖𝓕 (deriv (deriv f)) y‖ := by
      rw [h₂, h₁, norm_smul, norm_smul]
      simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos, pow_two,
        mul_assoc, mul_left_comm, mul_comm]
    _ ≤ _ := norm_fourier_le_integral hf₂ y

/-- A dyadic shell count of order (n + 1) 2ⁿ gives the weighted summability
required by spectral cutoff removal. Shell zero may contain heights below one. -/
theorem dyadic_zero_count_summable {Shell : ℕ → Type*} [∀ n, Fintype (Shell n)]
    (height : (Σ n, Shell n) → ℝ) (multiplicity : (Σ n, Shell n) → ℕ)
    (hlower : ∀ n (i : Shell n), (2 : ℝ) ^ n ≤ max 1 |height ⟨n, i⟩|)
    {C : ℝ} (hcount : ∀ n, (∑ i : Shell n, (multiplicity ⟨n, i⟩ : ℝ)) ≤
      C * ((n : ℝ) + 1) * 2 ^ n) :
    Summable (fun i => (multiplicity i : ℝ) / (1 + height i ^ 2)) := by
  apply (summable_sigma_of_nonneg (fun _ => by positivity)).mpr
  refine ⟨fun _ => summable_of_hasFiniteSupport (Set.toFinite _), ?_⟩
  have hgeom : Summable (fun n : ℕ => C * ((n : ℝ) + 1) * (1 / 2 : ℝ) ^ n) := by
    have h₀ : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ n) :=
      summable_geometric_of_abs_lt_one (by norm_num)
    have h₁ : Summable (fun n : ℕ => (n : ℝ) * (1 / 2 : ℝ) ^ n) := by
      simpa only [pow_one] using
        summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1
          (r := 1 / 2) (by norm_num)
    simpa only [add_mul, one_mul, ← Pi.add_apply, mul_assoc] using (h₁.add h₀).mul_left C
  apply hgeom.of_nonneg_of_le
  · intro n
    exact tsum_nonneg fun _ => by positivity
  · intro n
    rw [tsum_fintype]
    have htwo : 0 < (2 : ℝ) ^ n := by positivity
    calc
      _ ≤ ∑ i : Shell n, (multiplicity ⟨n, i⟩ : ℝ) / ((2 : ℝ) ^ n) ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        have hi := hlower n i
        have hsq : ((2 : ℝ) ^ n) ^ 2 ≤ (max 1 |height ⟨n, i⟩|) ^ 2 := by gcongr
        exact hsq.trans (by
          rcases le_total |height ⟨n, i⟩| 1 with h | h
          · rw [max_eq_left h]
            nlinarith [sq_nonneg (height ⟨n, i⟩)]
          · rw [max_eq_right h, sq_abs]
            linarith)
      _ = (∑ i : Shell n, (multiplicity ⟨n, i⟩ : ℝ)) / ((2 : ℝ) ^ n) ^ 2 := by
        rw [Finset.sum_div]
      _ ≤ (C * ((n : ℝ) + 1) * 2 ^ n) / ((2 : ℝ) ^ n) ^ 2 :=
        div_le_div_of_nonneg_right (hcount n) (by positivity)
      _ = _ := by
        rw [div_pow, one_pow, div_eq_mul_inv, div_eq_mul_inv]
        field_simp

/-- Transfer termwise cutoff removal to the full spectral sum given a common
weighted inverse-square bound. -/
theorem spectralCutoff_tendsto {ι : Type*} (height : ι → ℝ)
    (multiplicity : ι → ℕ)
    (hcount : Summable (fun i => (multiplicity i : ℝ) / (1 + height i ^ 2)))
    (F : ℕ → ι → ℂ) (limit : ι → ℂ)
    (hlim : ∀ i, Tendsto (fun n => F n i) atTop (𝓝 (limit i)))
    (C : ℝ) (hbound : ∀ n i, ‖F n i‖ ≤ C / (1 + height i ^ 2)) :
    Tendsto (fun n => ∑' i, (multiplicity i : ℂ) * F n i) atTop
      (𝓝 (∑' i, (multiplicity i : ℂ) * limit i)) := by
  apply tendsto_tsum_of_dominated_convergence (hcount.mul_left C)
  · exact fun i => (hlim i).const_mul _
  · exact Eventually.of_forall fun n i => by
      rw [norm_mul, Complex.norm_natCast]
      calc
        _ ≤ (multiplicity i : ℝ) * (C / (1 + height i ^ 2)) :=
          mul_le_mul_of_nonneg_left (hbound n i) (Nat.cast_nonneg _)
        _ = _ := by ring

/-- A common bound on a profile and its second derivative gives uniform
reciprocal-square Fourier decay. -/
theorem norm_fourier_le_one_add_sq {f : ℝ → ℂ}
    (hint : Integrable f) (hint₁ : Integrable (deriv f))
    (hint₂ : Integrable (deriv (deriv f))) (hd₁ : Differentiable ℝ f)
    (hd₂ : Differentiable ℝ (deriv f))
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hA' : (∫ x, ‖f x‖) ≤ A) (hB' : (∫ x, ‖deriv (deriv f) x‖) ≤ B)
    (y : ℝ) :
    ‖𝓕 f y‖ ≤ (2 * A + 2 * B / (2 * Real.pi) ^ 2) / (1 + y ^ 2) := by
  let C := 2 * A + 2 * B / (2 * Real.pi) ^ 2
  let F := ‖𝓕 (f) y‖
  have hF : 0 ≤ F := norm_nonneg _
  have hFA : F ≤ A := (norm_fourier_le_integral hint y).trans hA'
  have hFB : (2 * Real.pi * |y|) ^ 2 * F ≤ B :=
    (norm_fourier_le_of_second_deriv hint hd₁ hint₁ hd₂ hint₂ y).trans
      hB'
  change F ≤ C / (1 + y ^ 2)
  apply (le_div_iff₀ (by positivity)).mpr
  by_cases hy : y ^ 2 ≤ 1
  · calc
      F * (1 + y ^ 2) ≤ A * 2 := mul_le_mul hFA (by linarith) (by positivity) hA
      _ ≤ C := by
        dsimp [C]
        have : 0 ≤ 2 * B / (2 * Real.pi) ^ 2 := by positivity
        linarith
  · have hmul : F * y ^ 2 ≤ B / (2 * Real.pi) ^ 2 := by
      apply (le_div_iff₀ (by positivity)).mpr
      rw [show F * y ^ 2 * (2 * Real.pi) ^ 2 = (2 * Real.pi * |y|) ^ 2 * F by
        simp only [mul_pow, sq_abs]
        ring]
      exact hFB
    calc
      F * (1 + y ^ 2) ≤ F * (2 * y ^ 2) :=
        mul_le_mul_of_nonneg_left (by linarith [lt_of_not_ge hy]) hF
      _ ≤ 2 * (B / (2 * Real.pi) ^ 2) := by linarith
      _ ≤ C := by
        have heq : 2 * (B / (2 * Real.pi) ^ 2) = 2 * B / (2 * Real.pi) ^ 2 := by ring
        rw [heq]
        exact le_add_of_nonneg_left (by positivity)

/-- The spectral cutoff limit follows from uniform L¹ bounds for the profiles
and their second derivatives, plus pointwise convergence of their Fourier transforms. -/
theorem spectralFourierCutoff_tendsto {ι : Type*} (height : ι → ℝ)
    (multiplicity : ι → ℕ)
    (hcount : Summable (fun i => (multiplicity i : ℝ) / (1 + height i ^ 2)))
    (profile : ℕ → ι → ℝ → ℂ) (limit : ι → ℂ)
    (hint : ∀ n i, Integrable (profile n i))
    (hint₁ : ∀ n i, Integrable (deriv (profile n i)))
    (hint₂ : ∀ n i, Integrable (deriv (deriv (profile n i))))
    (hd₁ : ∀ n i, Differentiable ℝ (profile n i))
    (hd₂ : ∀ n i, Differentiable ℝ (deriv (profile n i)))
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hA' : ∀ n i, (∫ x, ‖profile n i x‖) ≤ A)
    (hB' : ∀ n i, (∫ x, ‖deriv (deriv (profile n i)) x‖) ≤ B)
    (hlim : ∀ i, Tendsto (fun n => 𝓕 (profile n i) (height i)) atTop (𝓝 (limit i))) :
    Tendsto (fun n => ∑' i, (multiplicity i : ℂ) * 𝓕 (profile n i) (height i)) atTop
      (𝓝 (∑' i, (multiplicity i : ℂ) * limit i)) := by
  let C := 2 * A + 2 * B / (2 * Real.pi) ^ 2
  apply spectralCutoff_tendsto height multiplicity hcount _ limit hlim C
  intro n i
  exact norm_fourier_le_one_add_sq (hint n i) (hint₁ n i) (hint₂ n i) (hd₁ n i)
    (hd₂ n i) hA hB (hA' n i) (hB' n i) (height i)

end Masullo
