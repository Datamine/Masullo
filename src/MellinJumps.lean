import JumpCalculus
import MellinStrip

open Complex Filter Function MeasureTheory Set Topology

namespace Masullo

noncomputable section

/-- Bounded data whose tails decay at every exponential rate. -/
def SuperExponentialLogDecay (u : ℝ → ℂ) : Prop :=
  (∃ M : ℝ, ∀ x, ‖u x‖ ≤ M) ∧
    ∀ N : ℕ, ∃ C T : ℝ, 0 < C ∧ 0 < T ∧
      ∀ x, T < |x| → ‖u x‖ ≤ C * Real.exp (-(N : ℝ) * |x|)

theorem SuperExponentialLogDecay.global_bound {u : ℝ → ℂ}
    (hu : SuperExponentialLogDecay u) (R : ℝ) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 < C ∧ ∀ x, ‖u x‖ ≤ C * Real.exp (-R * |x|) := by
  obtain ⟨M, hM⟩ := hu.1
  obtain ⟨N, hN⟩ := exists_nat_ge R
  obtain ⟨C, T, hC, _, htail⟩ := hu.2 N
  refine ⟨max C (M * Real.exp (R * T)), hC.trans_le (le_max_left _ _), fun x => ?_⟩
  by_cases ht : T < |x|
  · exact (htail x ht).trans (mul_le_mul (le_max_left _ _)
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_neg hN) (abs_nonneg _)))
      (Real.exp_nonneg _) (hC.le.trans (le_max_left _ _)))
  · have hM₀ : 0 ≤ M := (norm_nonneg (u 0)).trans (hM 0)
    calc
      ‖u x‖ ≤ M := hM x
      _ = M * 1 := (mul_one _).symm
      _ ≤ M * Real.exp (R * T + -R * |x|) :=
        mul_le_mul_of_nonneg_left (Real.one_le_exp_iff.mpr (by
          have := mul_nonneg hR (sub_nonneg.mpr (le_of_not_gt ht))
          nlinarith)) hM₀
      _ ≤ _ := by
        rw [Real.exp_add, ← mul_assoc]
        exact mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_nonneg _)

private def logKernel (u : ℝ → ℂ) (s : ℂ) (x : ℝ) : ℂ :=
  Complex.exp (s * (x : ℂ)) * u x

private def expEnvelope (x : ℝ) : ℝ := Real.exp (-|x|)

private theorem integrable_expEnvelope : Integrable expEnvelope := by
  have h₁ : IntegrableOn expEnvelope (Iic 0) := by
    apply (integrableOn_exp_Iic (0 : ℝ)).congr_fun
    · intro x hx
      simp [expEnvelope, abs_of_nonpos (mem_Iic.mp hx)]
    · exact measurableSet_Iic
  have h₂ : IntegrableOn expEnvelope (Ioi 0) := by
    apply (integrableOn_exp_neg_Ioi (0 : ℝ)).congr_fun
    · intro x hx
      simp [expEnvelope, abs_of_pos (mem_Ioi.mp hx)]
    · exact measurableSet_Ioi
  simpa only [Iic_union_Ioi, integrableOn_univ] using h₁.union h₂

private theorem logKernel_bound {u : ℝ → ℂ} {R C : ℝ}
    (hu : ∀ x, ‖u x‖ ≤ C * Real.exp (-(R + 2) * |x|))
    {s : ℂ} (hs : |s.re| ≤ R) (x : ℝ) :
    ‖logKernel u s x‖ ≤ C * Real.exp (-2 * |x|) := by
  have ha : s.re * x ≤ R * |x| := calc
    s.re * x ≤ |s.re * x| := le_abs_self _
    _ = |s.re| * |x| := abs_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_right hs (abs_nonneg _)
  have he : ‖Complex.exp (s * (x : ℂ))‖ ≤ Real.exp (R * |x|) := by
    simpa only [Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero] using Real.exp_le_exp.mpr ha
  calc
    ‖logKernel u s x‖ ≤ Real.exp (R * |x|) * (C * Real.exp (-(R + 2) * |x|)) :=
      by
        rw [logKernel, norm_mul]
        exact mul_le_mul he (hu x) (norm_nonneg _) (Real.exp_nonneg _)
    _ = C * (Real.exp (R * |x|) * Real.exp (-(R + 2) * |x|)) := by ring
    _ = _ := by rw [← Real.exp_add]; congr 2; ring

private theorem logKernel_bound_envelope {u : ℝ → ℂ} {R C : ℝ} (hC : 0 ≤ C)
    (hu : ∀ x, ‖u x‖ ≤ C * Real.exp (-(R + 2) * |x|))
    {s : ℂ} (hs : |s.re| ≤ R) (x : ℝ) :
    ‖logKernel u s x‖ ≤ C * expEnvelope x :=
  (logKernel_bound hu hs x).trans (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (by linarith [abs_nonneg x])) hC)

private theorem logKernel_weighted_bound {u : ℝ → ℂ} {R C : ℝ}
    (hu : ∀ x, ‖u x‖ ≤ C * Real.exp (-(R + 2) * |x|))
    {s : ℂ} (hs : |s.re| ≤ R) (x : ℝ) :
    ‖(x : ℂ) * logKernel u s x‖ ≤ C * expEnvelope x := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hp : |x| ≤ Real.exp |x| := by linarith [Real.add_one_le_exp |x|]
  calc
    |x| * ‖logKernel u s x‖ ≤ Real.exp |x| * (C * Real.exp (-2 * |x|)) :=
      mul_le_mul hp (logKernel_bound hu hs x) (norm_nonneg _) (Real.exp_nonneg _)
    _ = C * (Real.exp |x| * Real.exp (-2 * |x|)) := by ring
    _ = _ := by rw [← Real.exp_add]; unfold expEnvelope; congr 2; ring

private theorem logKernel_measurable {u : ℝ → ℂ} (hu : Measurable u) (s : ℂ) :
    Measurable (logKernel u s) := (by
  have hc : Continuous (fun x : ℝ => Complex.exp (s * (x : ℂ))) := by fun_prop
  exact hc.measurable.mul hu)

private theorem logKernel_integrable {u : ℝ → ℂ} (hu : SuperExponentialLogDecay u)
    (hm : Measurable u) (s : ℂ) : Integrable (logKernel u s) := by
  obtain ⟨C, hC, hb⟩ := hu.global_bound (|s.re| + 2) (by positivity)
  exact (integrable_expEnvelope.const_mul C).mono' (logKernel_measurable hm s).aestronglyMeasurable
    (Eventually.of_forall (logKernel_bound_envelope hC.le hb le_rfl))

theorem SuperExponentialLogDecay.integrable {u : ℝ → ℂ}
    (hu : SuperExponentialLogDecay u) (hm : Measurable u) : Integrable u := by
  have he : logKernel u 0 = u := by
    funext x
    simp [logKernel]
  exact he ▸ logKernel_integrable hu hm 0

private theorem logKernel_deriv_parameter (u : ℝ → ℂ) (s : ℂ) (x : ℝ) :
    HasDerivAt (fun z => logKernel u z x) ((x : ℂ) * logKernel u s x) s := by
  simpa only [logKernel, one_mul, mul_assoc, mul_left_comm] using
    ((((hasDerivAt_id' s).mul_const (x : ℂ)).cexp).mul_const (u x))

private theorem logMellin_entire {u : ℝ → ℂ}
    (hu : SuperExponentialLogDecay u) (hm : Measurable u) :
    Differentiable ℂ (fun s => ∫ x, logKernel u s x) := by
  intro s
  let R := |s.re| + 1
  let S := {z : ℂ | |z.re| < R}
  have hS : S ∈ 𝓝 s := (isOpen_lt Complex.continuous_re.abs continuous_const).mem_nhds
    (show |s.re| < R by dsimp [R]; linarith)
  obtain ⟨C, hC, hb⟩ := hu.global_bound (R + 2) (by dsimp [R]; positivity)
  have hm' : Measurable (fun x : ℝ => (x : ℂ) * logKernel u s x) :=
    Complex.continuous_ofReal.measurable.mul (logKernel_measurable hm s)
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := logKernel u) (F' := fun z x => (x : ℂ) * logKernel u z x)
    (bound := fun x => C * expEnvelope x) hS
    (Eventually.of_forall fun z => (logKernel_measurable hm z).aestronglyMeasurable)
    (logKernel_integrable hu hm s) hm'.aestronglyMeasurable
    (Eventually.of_forall fun x z hz => logKernel_weighted_bound hb
      (show |z.re| < R from hz).le x)
    (integrable_expEnvelope.const_mul C)
    (Eventually.of_forall fun x z _ => logKernel_deriv_parameter u z x)
  exact hd.2.differentiableAt

private theorem logKernel_deriv_argument {u : ℝ → ℂ} {v : ℂ} {x : ℝ}
    (s : ℂ) (hu : HasDerivAt u v x) :
    HasDerivAt (logKernel u s) (logKernel (fun _ => v) s x + s * logKernel u s x) x := by
  have he : HasDerivAt (fun y : ℝ => Complex.exp (s * (y : ℂ)))
      (Complex.exp (s * (x : ℂ)) * s) x := by
    simpa only [one_mul, mul_one] using (((hasDerivAt_id' (x : ℂ)).const_mul s).cexp).comp_ofReal
  have h := he.mul hu
  have hval : Complex.exp (s * (x : ℂ)) * s * u x + Complex.exp (s * (x : ℂ)) * v =
      logKernel (fun _ => v) s x + s * logKernel u s x := by
    unfold logKernel
    ring
  rw [hval] at h
  exact h

private theorem logKernel_vanishes {u : ℝ → ℂ}
    (hu : SuperExponentialLogDecay u) (s : ℂ) {l : Filter ℝ}
    (hl : Tendsto (fun x : ℝ => |x|) l atTop) :
    Tendsto (logKernel u s) l (𝓝 0) := by
  obtain ⟨C, hC, hb⟩ := hu.global_bound (|s.re| + 2) (by positivity)
  have ht : Tendsto (fun x : ℝ => C * expEnvelope x) l (𝓝 0) := by
    have he := (Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hl)).const_mul C
    simpa only [Function.comp_def, expEnvelope, mul_zero] using he
  exact squeeze_zero_norm (logKernel_bound_envelope hC.le hb le_rfl) ht

private theorem logKernel_jump_identity {u v : ℝ → ℂ} {left right : ℝ → ℂ}
    (S : Finset ℝ) (hu : SuperExponentialLogDecay u)
    (humu : Measurable u) (hiv : Integrable (logKernel v s))
    (hderiv : ∀ x ∉ S, HasDerivAt u (v x) x)
    (hl : ∀ x ∈ S, Tendsto u (𝓝[<] x) (𝓝 (left x)))
    (hr : ∀ x ∈ S, Tendsto u (𝓝[>] x) (𝓝 (right x))) :
    (∫ x, logKernel v s x) + s * (∫ x, logKernel u s x) +
      (∑ x ∈ S, Complex.exp (s * (x : ℂ)) * (right x - left x)) = 0 := by
  classical
  let F := logKernel u s
  let D (x : ℝ) := logKernel v s x + s * F x
  let J := ∑ x ∈ S, Complex.exp (s * (x : ℂ)) * (right x - left x)
  have hD : Integrable D := hiv.add ((logKernel_integrable hu humu s).const_mul s)
  have hF (x : ℝ) (hx : x ∉ S) : HasDerivAt F (D x) x :=
    logKernel_deriv_argument s (hderiv x hx)
  have he : Continuous (fun x : ℝ => Complex.exp (s * (x : ℂ))) := by fun_prop
  have hleft (x : ℝ) (hx : x ∈ S) :
      Tendsto F (𝓝[<] x) (𝓝 (logKernel left s x)) :=
    ((he.tendsto x).mono_left nhdsWithin_le_nhds).mul (hl x hx)
  have hright (x : ℝ) (hx : x ∈ S) :
      Tendsto F (𝓝[>] x) (𝓝 (logKernel right s x)) :=
    ((he.tendsto x).mono_left nhdsWithin_le_nhds).mul (hr x hx)
  obtain ⟨M, hM⟩ := ((S.finite_toSet.image (fun x : ℝ => |x|)).bddAbove)
  have hftc : ∀ᶠ t : ℝ in atTop, (∫ x in (-t)..t, D x) + J = F t - F (-t) := by
    filter_upwards [eventually_gt_atTop (max M 0)] with t ht
    have ht₀ : 0 < t := (le_max_right M 0).trans_lt ht
    have hcover (x : ℝ) (hx : x ∈ S) : x ∈ Ioo (-t) t := by
      have hxM : |x| ≤ M := hM (mem_image_of_mem (fun x : ℝ => |x|) hx)
      exact abs_lt.mp (hxM.trans_lt ((le_max_left M 0).trans_lt ht))
    have hSm : t ∉ S := fun h => lt_irrefl t (hcover t h).2
    have hSn : -t ∉ S := fun h => lt_irrefl (-t) (hcover (-t) h).1
    have hFTC := integral_derivative_add_jumps S (neg_lt_self ht₀) hD
      (fun x _ => hF x)
      (((hF (-t) hSn).continuousAt.tendsto).mono_left nhdsWithin_le_nhds)
      (((hF t hSm).continuousAt.tendsto).mono_left nhdsWithin_le_nhds)
      (fun x hx _ => hleft x hx) (fun x hx _ => hright x hx)
    have hj : (∑ c ∈ S, (if c ∈ Ioo (-t) t then
        logKernel right s c - logKernel left s c else 0)) = J := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [ite_eq_left (hcover x hx)]
      simp only [logKernel, mul_sub]
    rwa [hj] at hFTC
  have ht : Tendsto (fun t : ℝ => (∫ x in (-t)..t, D x) + J) atTop
      (𝓝 ((∫ x, D x) + J)) :=
    (intervalIntegral_tendsto_integral hD tendsto_neg_atTop_atBot tendsto_id).add_const J
  have hu₁ := logKernel_vanishes hu s tendsto_abs_atTop_atTop
  have hu₂ := (logKernel_vanishes hu s tendsto_abs_atBot_atTop).comp tendsto_neg_atTop_atBot
  have ht₀ : Tendsto (fun t : ℝ => F t - F (-t)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, sub_zero] using hu₁.sub hu₂
  have h := tendsto_nhds_unique ht (ht₀.congr' (hftc.mono fun _ ht => ht.symm))
  dsimp only [D, F] at h
  rwa [integral_add hiv ((logKernel_integrable hu humu s).const_mul s), integral_const_mul] at h

/-- B.4.1.1. The Mellin transform of a piecewise smooth test with finitely
many jumps is entire and is uniformly of order `1 / ‖s‖` on bounded
vertical strips. The hypotheses are in the coordinate `x = log t`. -/
theorem mellin_finite_jumps_entire_strip
    (φ : ℝ → ℂ) (S : Finset ℝ) (v left right : ℝ → ℂ)
    (hu : SuperExponentialLogDecay (fun x => φ (Real.exp x)))
    (hv : SuperExponentialLogDecay v)
    (hderiv : ∀ x ∉ S, HasDerivAt (fun y => φ (Real.exp y)) (v x) x)
    (hcv : ContinuousOn v ((S : Set ℝ)ᶜ))
    (hl : ∀ x ∈ S, Tendsto (fun y => φ (Real.exp y)) (𝓝[<] x) (𝓝 (left x)))
    (hr : ∀ x ∈ S, Tendsto (fun y => φ (Real.exp y)) (𝓝[>] x) (𝓝 (right x))) :
    (∀ s : ℂ, MellinConvergent φ s) ∧ Differentiable ℂ (mellin φ) ∧
    ∀ R : ℝ, 0 ≤ R →
      ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, |s.re| ≤ R → ‖s‖ * ‖mellin φ s‖ ≤ C := by
  let u := fun x => φ (Real.exp x)
  have hmu : Measurable u := by
    apply ContinuousOn.measurable_of_countable_compl (s := (S : Set ℝ)ᶜ)
    · exact fun x hx => (hderiv x hx).continuousAt.continuousWithinAt
    · simpa only [compl_compl] using S.finite_toSet.countable
  have hmv : Measurable v := ContinuousOn.measurable_of_countable_compl hcv
    (by simpa only [compl_compl] using S.finite_toSet.countable)
  have heq (s : ℂ) : mellin φ s = ∫ x, logKernel u s x := mellin_eq_log_integral φ s
  refine ⟨?_, ?_, ?_⟩
  · intro s
    rw [MellinConvergent, ← Real.range_exp, ← image_univ,
      integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ
        (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
        Real.exp_injective.injOn, integrableOn_univ]
    refine (logKernel_integrable hu hmu s).congr (Eventually.of_forall fun x => ?_)
    change Complex.exp (s * (x : ℂ)) * φ (Real.exp x) =
      |Real.exp x| • ((↑(Real.exp x) : ℂ) ^ (s - 1) • φ (Real.exp x))
    rw [abs_of_pos (Real.exp_pos x), real_smul, smul_eq_mul,
      cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos x).ne'),
      ← Complex.ofReal_log (Real.exp_nonneg x), Real.log_exp,
      Complex.ofReal_exp, ← mul_assoc, ← Complex.exp_add]
    congr 2
    ring
  · rw [show mellin φ = fun s => ∫ x, logKernel u s x from funext heq]
    exact logMellin_entire hu hmu
  · intro R hR
    obtain ⟨K, hK, hKv⟩ := hv.global_bound (R + 2) (by positivity)
    let A := ∫ x, K * expEnvelope x
    let B := ∑ x ∈ S, Real.exp (R * |x|) * ‖right x - left x‖
    have hA : 0 ≤ A := integral_nonneg fun _ => by dsimp [expEnvelope]; positivity
    have hB : 0 ≤ B := Finset.sum_nonneg fun _ _ => by positivity
    refine ⟨1 + A + B, by linarith, fun s hs => ?_⟩
    have hI : ‖∫ x, logKernel v s x‖ ≤ A :=
      norm_integral_le_of_norm_le (integrable_expEnvelope.const_mul K)
        (Eventually.of_forall (logKernel_bound_envelope hK.le hKv hs))
    have hJ : ‖∑ x ∈ S, Complex.exp (s * (x : ℂ)) * (right x - left x)‖ ≤ B := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => ?_)
      rw [norm_mul]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      rw [Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      apply Real.exp_le_exp.mpr
      calc
        s.re * x ≤ |s.re * x| := le_abs_self _
        _ = |s.re| * |x| := abs_mul _ _
        _ ≤ R * |x| := mul_le_mul_of_nonneg_right hs (abs_nonneg _)
    have hid := logKernel_jump_identity S hu hmu (logKernel_integrable hv hmv s) hderiv hl hr
    have hex : s * (∫ x, logKernel u s x) = -(∫ x, logKernel v s x) -
        ∑ x ∈ S, Complex.exp (s * (x : ℂ)) * (right x - left x) := by
      linear_combination hid
    rw [heq, ← norm_mul, hex]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_neg]
    linarith

end
end Masullo
