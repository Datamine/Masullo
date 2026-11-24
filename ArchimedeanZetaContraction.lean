import SchwartzIsometricAverage
import SchwartzKernelTaylor
import AnalyticOperatorGerms
import RealArchimedeanZeta
import ComplexArchimedeanZeta
import Mathlib.Analysis.Calculus.TaylorIntegral

open Filter Function LineDeriv MeasureTheory Set
open scoped ContDiff SchwartzMap Topology NNReal

namespace Masullo

noncomputable section

private abbrev positiveHaar : Measure ℝ := volume.restrict (Ioi 0)

private theorem measurable_real_cpow (s : ℂ) : Measurable (fun t : ℝ => (t : ℂ) ^ s) := by
  apply measurable_of_measurable_on_compl_singleton 0
  apply Continuous.measurable
  apply continuous_iff_continuousAt.mpr
  intro t
  exact ContinuousAt.comp' (f := Subtype.val) (x := t)
    (Complex.continuousAt_ofReal_cpow_const t.val _ (Or.inr t.property))
    continuous_subtype_val.continuousAt

private theorem mellinMajorant_pos_eq (s : ℂ) (m : ℕ) {t : ℝ} (ht : 0 < t) :
    schwartzKernelMajorant (id : ℝ → ℝ) (fun t => (t : ℂ) ^ (s - 1)) m t =
      t ^ (s.re - 1) / max 1 (t ^ m) := by
  simp [schwartzKernelMajorant, Real.norm_of_nonneg ht.le,
    Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.sub_re]

private theorem mellinMajorant_tail_integrable (s : ℂ) (m : ℕ) (hm : s.re < m) :
    IntegrableOn (schwartzKernelMajorant (id : ℝ → ℝ) (fun t => (t : ℂ) ^ (s - 1)) m)
      (Ioi 1) := by
  apply (integrableOn_Ioi_rpow_of_lt
    (show s.re - 1 - (m : ℝ) < -1 by linarith) (zero_lt_one : (0 : ℝ) < 1)).congr_fun _
    measurableSet_Ioi
  intro t ht
  have h₁ : 1 < t := ht
  have hp := (zero_lt_one : (0 : ℝ) < 1).trans h₁
  rw [mellinMajorant_pos_eq s m hp, max_eq_right (one_le_pow₀ h₁.le)]
  exact (Real.rpow_sub hp (s.re - 1) (m : ℝ)).trans (by rw [Real.rpow_natCast])

private theorem positiveMellinMajorant_integrable (s : ℂ) (m : ℕ)
    (hs : 0 < s.re) (hm : s.re < m) :
    Integrable (schwartzKernelMajorant (id : ℝ → ℝ) (fun t => (t : ℂ) ^ (s - 1)) m)
      positiveHaar := by
  have h₀ : IntegrableOn
      (schwartzKernelMajorant (id : ℝ → ℝ) (fun t => (t : ℂ) ^ (s - 1)) m) (Ioc 0 1) := by
    apply (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1)
      (show -1 < s.re - 1 by linarith)).1.congr_fun _ measurableSet_Ioc
    intro t ht
    rw [mellinMajorant_pos_eq s m ht.1, max_eq_left (pow_le_one₀ ht.1.le ht.2), div_one]
  have h := h₀.union (mellinMajorant_tail_integrable s m hm)
  rwa [Ioc_union_Ioi_eq_Ioi zero_le_one] at h

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- Mellin contraction in a positive real coordinate of a coupled Schwartz test. -/
def schwartzPositiveMellin (s : ℂ) (hs : 0 < s.re) :
    𝓢(ℝ × Y, ℂ) →L[ℂ] 𝓢(Y, ℂ) :=
  schwartzPartialIntegralCLM measurable_id (measurable_real_cpow (s - 1)).aestronglyMeasurable
    (positiveMellinMajorant_integrable s (exists_nat_gt s.re).choose hs
      (exists_nat_gt s.re).choose_spec)

@[simp] theorem schwartzPositiveMellin_apply (s : ℂ) (hs : 0 < s.re)
    (f : 𝓢(ℝ × Y, ℂ)) (y : Y) :
    schwartzPositiveMellin s hs f y = ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) * f (t, y) :=
  rfl

attribute [local instance] complexZeta_circleMeasurable complexZeta_circleBorel

private theorem polarMellinMajorant_integrable (ν : Measure Circle) [IsFiniteMeasure ν]
    (s : ℂ) (j : ℤ) (m : ℕ) (hs : 0 < s.re) (hm : 2 * s.re < m) :
    Integrable (schwartzKernelMajorant (fun p : ℝ × Circle => p.1 • (p.2 : ℂ))
      (fun p => (p.1 : ℂ) ^ (2 * s - 1) * (p.2 : ℂ) ^ j) m) (positiveHaar.prod ν) := by
  have hr : (2 * s).re = 2 * s.re := by simp [Complex.mul_re]
  have h := (positiveMellinMajorant_integrable (2 * s) m
    (hr ▸ (show 0 < 2 * s.re by positivity)) (hr ▸ hm)).comp_fst ν
  apply h.congr
  exact .of_forall fun p => by
    simp [schwartzKernelMajorant, norm_zpow, Circle.norm_coe]

/-- Mellin contraction in a complex coordinate, written in polar variables
with any finite angular measure. For Tamagawa normalization the angular
measure is a constant multiple of the probability Haar measure. -/
def schwartzPolarMellin (ν : Measure Circle) [IsFiniteMeasure ν]
    (j : ℤ) (s : ℂ) (hs : 0 < s.re) : 𝓢(ℂ × Y, ℂ) →L[ℂ] 𝓢(Y, ℂ) :=
  schwartzPartialIntegralCLM
    (measurable_fst.smul ((continuous_subtype_val : Continuous (fun u : Circle => (u : ℂ))).measurable.comp
      measurable_snd))
    (((measurable_real_cpow (2 * s - 1)).comp measurable_fst).mul
      ((Continuous.zpow₀ (continuous_subtype_val.comp continuous_snd) j
        (fun p : ℝ × Circle => Or.inl (Circle.coe_ne_zero p.2)) : Continuous
          (fun p : ℝ × Circle => (p.2 : ℂ) ^ j)).measurable)).aestronglyMeasurable
    (polarMellinMajorant_integrable ν s j (exists_nat_gt (2 * s.re)).choose hs
      (exists_nat_gt (2 * s.re)).choose_spec)

@[simp] theorem schwartzPolarMellin_apply (ν : Measure Circle) [IsFiniteMeasure ν]
    (j : ℤ) (s : ℂ) (hs : 0 < s.re) (f : 𝓢(ℂ × Y, ℂ)) (y : Y) :
    schwartzPolarMellin ν j s hs f y = ∫ p : ℝ × Circle,
      ((p.1 : ℂ) ^ (2 * s - 1) * (p.2 : ℂ) ^ j) * f (p.1 • (p.2 : ℂ), y) ∂positiveHaar.prod ν :=
  rfl

private def realFirstDeriv : 𝓢(ℝ × Y, ℂ) →L[ℂ] 𝓢(ℝ × Y, ℂ) :=
  lineDerivOpCLM ℂ 𝓢(ℝ × Y, ℂ) ((1, 0) : ℝ × Y)

private def realFirstJet : ℕ → 𝓢(ℝ × Y, ℂ) →L[ℂ] 𝓢(ℝ × Y, ℂ)
  | 0 => ContinuousLinearMap.id ℂ _
  | n + 1 => (realFirstJet n).comp realFirstDeriv

private theorem realFirstDeriv_apply (f : 𝓢(ℝ × Y, ℂ)) (x : ℝ) (y : Y) :
    realFirstDeriv f (x, y) = deriv (fun t : ℝ => f (t, y)) x := by
  let l := ContinuousLinearMap.inl ℝ ℝ Y
  have h := (f.smooth 1).differentiable (by norm_num) (x, y)
  have hl : HasDerivAt (fun t : ℝ => (t, y)) ((1 : ℝ), (0 : Y)) x := by
    have h₁ := (l.hasFDerivAt (x := x)).hasDerivAt
    have h := h₁.add (hasDerivAt_const x ((0, y) : ℝ × Y))
    have he : (fun t : ℝ => (t, y)) = (l : ℝ → ℝ × Y) + fun _ => (0, y) := by
      funext t
      simp [l, Pi.add_apply, Prod.mk_add_mk]
    rw [he]
    simpa [l, Prod.mk_add_mk] using h
  have hd := h.hasFDerivAt.comp_hasDerivAt x hl
  rw [realFirstDeriv, SchwartzMap.lineDerivOpCLM_eq]
  change fderiv ℝ f (x, y) (1, 0) = _
  exact hd.deriv.symm

private theorem realFirstJet_apply (n : ℕ) (f : 𝓢(ℝ × Y, ℂ)) (x : ℝ) (y : Y) :
    realFirstJet n f (x, y) = iteratedDeriv n (fun t : ℝ => f (t, y)) x := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    change realFirstJet n (realFirstDeriv f) (x, y) = _
    rw [ih, iteratedDeriv_succ']
    congr 1
    funext t
    exact realFirstDeriv_apply f t y

private def realOriginSlice : 𝓢(ℝ × Y, ℂ) →L[ℂ] 𝓢(Y, ℂ) :=
  SchwartzMap.compCLMOfAntilipschitz ℂ (ContinuousLinearMap.inr ℝ ℝ Y).hasTemperateGrowth
    (K := 1) (by
      intro y z
      simp [edist_dist, Prod.dist_eq])

private def realMellinTail (s : ℂ) : 𝓢(ℝ × Y, ℂ) →L[ℂ] 𝓢(Y, ℂ) :=
  schwartzPartialIntegralCLM measurable_id (measurable_real_cpow (s - 1)).aestronglyMeasurable
    (mellinMajorant_tail_integrable s (exists_nat_gt s.re).choose
      (exists_nat_gt s.re).choose_spec)

private abbrev unitIntervalHaar : Measure ℝ := volume.restrict (Ioc 0 1)

private def lowerMellinKernel (n : ℕ) (s : ℂ) (p : ℝ × ℝ) : ℂ :=
  (p.1 : ℂ) ^ (s - 1 + (n + 1 : ℕ)) * ↑((1 - p.2) ^ n / (n.factorial : ℝ))

private theorem lowerMellinKernel_measurable (n : ℕ) (s : ℂ) :
    Measurable (lowerMellinKernel n s) :=
  ((measurable_real_cpow _).comp measurable_fst).mul (by fun_prop)

private theorem lowerMellinMajorant_integrable (n : ℕ) (s : ℂ)
    (hs : -((n + 1 : ℕ) : ℝ) < s.re) :
    Integrable (schwartzKernelMajorant (fun p : ℝ × ℝ => p.1 * p.2) (lowerMellinKernel n s) 0)
      (unitIntervalHaar.prod unitIntervalHaar) := by
  have h₁ : Integrable (fun t : ℝ => (t : ℂ) ^ (s - 1 + (n + 1 : ℕ))) unitIntervalHaar := by
    let b := s.re - 1 + ((n + 1 : ℕ) : ℝ)
    have hb : -1 < b := by dsimp [b]; linarith
    apply (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) hb).1.mono'
      (measurable_real_cpow _).aestronglyMeasurable
    filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioc (a := (0 : ℝ)) (b := 1))]
      with t ht
    rw [Complex.norm_cpow_eq_rpow_re_of_pos ht.1]
    simp [b]
  have h₂ : Integrable (fun r : ℝ => (↑((1 - r) ^ n / (n.factorial : ℝ)) : ℂ))
      unitIntervalHaar := by
    have hC : Continuous (fun r : ℝ => (↑((1 - r) ^ n / (n.factorial : ℝ)) : ℂ)) := by fun_prop
    exact (hC.integrableOn_Icc (a := (0 : ℝ)) (b := 1)).mono_set Ioc_subset_Icc_self
  apply (h₁.mul_prod h₂).norm.congr
  exact .of_forall fun p => by simp [schwartzKernelMajorant, lowerMellinKernel]

private def realMellinLower (n : ℕ) (s : ℂ) (hs : -((n + 1 : ℕ) : ℝ) < s.re) :
    𝓢(ℝ × Y, ℂ) →L[ℂ] 𝓢(Y, ℂ) :=
  (schwartzPartialIntegralCLM (measurable_fst.mul measurable_snd)
    (lowerMellinKernel_measurable n s).aestronglyMeasurable (lowerMellinMajorant_integrable n s hs)).comp
      (realFirstJet (n + 1))

private theorem realMellinTail_seminorm_le (b : ℝ) (m : ℕ) (hm : b < m)
    (s : ℂ) (hs : s.re ≤ b) (f : 𝓢(ℝ × Y, ℂ)) (k j : ℕ) :
    SchwartzMap.seminorm ℂ k j (realMellinTail s f) ≤
      (∫ t : ℝ in Ioi 1, schwartzKernelMajorant id (fun t : ℝ => (t : ℂ) ^ ((b : ℂ) - 1)) m t) *
      max (SchwartzMap.seminorm ℂ k j f) (SchwartzMap.seminorm ℂ (k + m) j f) := by
  let M (z : ℂ) := schwartzKernelMajorant (id : ℝ → ℝ) (fun t => (t : ℂ) ^ (z - 1)) m
  have hM := mellinMajorant_tail_integrable s m (hs.trans_lt hm)
  have hB : IntegrableOn (M (b : ℂ)) (Ioi 1) :=
    mellinMajorant_tail_integrable (b : ℂ) m (by simpa using hm)
  let T : 𝓢(ℝ × Y, ℂ) →L[ℂ] 𝓢(Y, ℂ) := schwartzPartialIntegralCLM measurable_id
    (measurable_real_cpow (s - 1)).aestronglyMeasurable hM
  have he : realMellinTail s f = T f := by
    ext y
    rfl
  rw [he]
  apply (schwartzPartialIntegralCLM_seminorm_le measurable_id
    (measurable_real_cpow (s - 1)).aestronglyMeasurable hM f k j).trans
  simp only [Finset.sup_insert, Finset.sup_singleton, Seminorm.coe_sup, Pi.sup_apply,
    schwartzSeminormFamily]
  apply mul_le_mul_of_nonneg_right _ (le_trans (apply_nonneg _ _) (le_max_left _ _))
  apply integral_mono_ae hM hB
  filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioi (a := (1 : ℝ)))] with t ht
  have hp : 0 < t := zero_lt_one.trans ht
  change M s t ≤ M (b : ℂ) t
  dsimp only [M]
  rw [mellinMajorant_pos_eq s m hp, mellinMajorant_pos_eq (b : ℂ) m hp, Complex.ofReal_re]
  exact div_le_div_of_nonneg_right
    (Real.rpow_le_rpow_of_exponent_le (le_of_lt ht) (sub_le_sub_right hs 1)) (by positivity)

private theorem realMellinLower_seminorm_le (n : ℕ) (a : ℝ)
    (ha : -((n + 1 : ℕ) : ℝ) < a) (s : ℂ) (hs : a ≤ s.re)
    (f : 𝓢(ℝ × Y, ℂ)) (k j : ℕ) :
    SchwartzMap.seminorm ℂ k j (realMellinLower n s (ha.trans_le hs) f) ≤
      (∫ p, schwartzKernelMajorant (fun p : ℝ × ℝ => p.1 * p.2)
        (lowerMellinKernel n (a : ℂ)) 0 p ∂(unitIntervalHaar.prod unitIntervalHaar)) *
      SchwartzMap.seminorm ℂ k j (realFirstJet (n + 1) f) := by
  let M (z : ℂ) := schwartzKernelMajorant (fun p : ℝ × ℝ => p.1 * p.2) (lowerMellinKernel n z) 0
  have hM := lowerMellinMajorant_integrable n s (ha.trans_le hs)
  have hA := lowerMellinMajorant_integrable n (a : ℂ) (by simpa using ha)
  change SchwartzMap.seminorm ℂ k j
    (schwartzPartialIntegralCLM (measurable_fst.mul measurable_snd)
      (lowerMellinKernel_measurable n s).aestronglyMeasurable hM (realFirstJet (n + 1) f)) ≤ _
  apply (schwartzPartialIntegralCLM_seminorm_le (measurable_fst.mul measurable_snd)
    (lowerMellinKernel_measurable n s).aestronglyMeasurable hM (realFirstJet (n + 1) f) k j).trans
  simp only [add_zero, Finset.sup_insert, Finset.sup_singleton, sup_idem, schwartzSeminormFamily]
  apply mul_le_mul_of_nonneg_right _ (apply_nonneg _ _)
  apply integral_mono_ae hM hA
  have ht : ∀ᵐ t ∂unitIntervalHaar, t ∈ Ioc (0 : ℝ) 1 :=
    ae_restrict_mem measurableSet_Ioc
  have hpt : ∀ᵐ p ∂(unitIntervalHaar.prod unitIntervalHaar),
      p ∈ Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1 :=
    (Measure.ae_prod_mem_iff_ae_ae_mem (measurableSet_Ioc.prod measurableSet_Ioc)).mpr
      (ht.mono fun _ hx ↦ ht.mono fun _ hy ↦ ⟨hx, hy⟩)
  filter_upwards [hpt] with p hp
  have hl : 0 < p.1 := hp.1.1
  have hu : p.1 ≤ 1 := hp.1.2
  change M s p ≤ M (a : ℂ) p
  simp only [M, schwartzKernelMajorant, pow_zero, max_self, div_one, lowerMellinKernel,
    norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hl, Complex.add_re, Complex.sub_re,
    Complex.one_re, Complex.ofReal_re]
  exact mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow_of_exponent_ge hl hu (by linarith)) (norm_nonneg _)

/-- A real Mellin chart acting on coupled tests. Taylor's integral remainder
is contracted in two auxiliary interval variables. The polar terms come from
the restrictions of the first-coordinate jets to the zero slice. -/
def schwartzMellinTaylorChart (n : ℕ) (s : ℂ) (hs : -((n + 1 : ℕ) : ℝ) < s.re) :
    𝓢(ℝ × Y, ℂ) →L[ℂ] 𝓢(Y, ℂ) :=
  realMellinTail s + realMellinLower n s hs +
    ∑ k ∈ Finset.range (n + 1),
      (((k.factorial : ℂ) * (s + k))⁻¹) • realOriginSlice.comp (realFirstJet k)


/-- A real Mellin chart is uniformly bounded by continuous seminorms of
the coupled input on every closed strip in the chart, at heights of modulus at least one. -/
theorem schwartzMellinTaylorChart_uniform_seminorm (n : ℕ) (a b : ℝ)
    (ha : -((n + 1 : ℕ) : ℝ) < a) (k j : ℕ) :
    ∃ p : Seminorm ℂ 𝓢(ℝ × Y, ℂ), Continuous p ∧
      ∀ (s : ℂ) (hs : s.re ∈ Icc a b) (_ : 1 ≤ |s.im|) (f : 𝓢(ℝ × Y, ℂ)),
        SchwartzMap.seminorm ℂ k j (schwartzMellinTaylorChart n s (ha.trans_le hs.1) f) ≤ p f := by
  obtain ⟨m, hm⟩ := exists_nat_gt b
  let A := ∫ p, schwartzKernelMajorant (fun p : ℝ × ℝ => p.1 * p.2)
    (lowerMellinKernel n (a : ℂ)) 0 p ∂(unitIntervalHaar.prod unitIntervalHaar)
  let B := ∫ t : ℝ in Ioi 1, schwartzKernelMajorant id (fun t : ℝ => (t : ℂ) ^ ((b : ℂ) - 1)) m t
  have hA : 0 ≤ A := integral_nonneg fun _ ↦ div_nonneg (norm_nonneg _) (by positivity)
  have hB : 0 ≤ B := integral_nonneg fun _ ↦ div_nonneg (norm_nonneg _) (by positivity)
  let r : Seminorm ℂ 𝓢(Y, ℂ) := SchwartzMap.seminorm ℂ k j
  let A' : ℝ≥0 := ⟨A, hA⟩
  let B' : ℝ≥0 := ⟨B, hB⟩
  let V := schwartz_withSeminorms ℂ (ℝ × Y) ℂ
  let p : Seminorm ℂ 𝓢(ℝ × Y, ℂ) :=
    B' • (SchwartzMap.seminorm ℂ k j ⊔ SchwartzMap.seminorm ℂ (k + m) j)
  let q : Seminorm ℂ 𝓢(ℝ × Y, ℂ) :=
    A' • (SchwartzMap.seminorm ℂ k j).comp (realFirstJet (n + 1)).toLinearMap
  let u (i : ℕ) := r.comp (realOriginSlice.comp (realFirstJet i)).toLinearMap
  have hr : Continuous (r : 𝓢(Y, ℂ) → ℝ) :=
    (schwartz_withSeminorms ℂ Y ℂ).continuous_seminorm (k, j)
  have hp : Continuous (p : 𝓢(ℝ × Y, ℂ) → ℝ) := by
    apply Continuous.const_smul _ B'
    exact (V.continuous_seminorm (k, j)).max (V.continuous_seminorm (k + m, j))
  have hq : Continuous (q : 𝓢(ℝ × Y, ℂ) → ℝ) := by
    exact ((V.continuous_seminorm (k, j)).comp
      (realFirstJet (Y := Y) (n + 1)).continuous).const_smul A'
  have hu (i : ℕ) : Continuous (u i : 𝓢(ℝ × Y, ℂ) → ℝ) :=
    hr.comp (realOriginSlice.comp (realFirstJet i)).continuous
  refine ⟨p + q + ∑ i ∈ Finset.range (n + 1), u i,
    (hp.add hq).add (Seminorm.continuous_finsetSum fun i _ ↦ hu i), ?_⟩
  · intro s hs hi f
    let c (i : ℕ) := (((i.factorial : ℂ) * (s + i))⁻¹)
    let v (i : ℕ) := c i • (realOriginSlice.comp (realFirstJet i)) f
    have hc (i : ℕ) : ‖c i‖ ≤ 1 := by
      have hsi : 1 ≤ ‖s + (i : ℂ)‖ := hi.trans (by simpa using Complex.abs_im_le_norm (s + i))
      have hf : 1 ≤ ‖(i.factorial : ℂ)‖ := by
        simp only [Complex.norm_natCast]
        exact_mod_cast Nat.factorial_pos i
      dsimp only [c]
      rw [norm_inv, norm_mul, inv_le_one_iff₀]
      exact Or.inr (one_le_mul_of_one_le_of_one_le hf hsi)
    have hv (i : ℕ) : r (v i) ≤ u i f := by
      dsimp only [v]
      rw [map_smul_eq_mul]
      exact mul_le_of_le_one_left (apply_nonneg _ _) (hc i)
    have ht : r (realMellinTail s f) ≤ p f := by
      simp only [p, smul_apply, NNReal.smul_def, smul_eq_mul, Seminorm.coe_sup, Pi.sup_apply]
      exact realMellinTail_seminorm_le b m hm s hs.2 f k j
    have hl : r (realMellinLower n s (ha.trans_le hs.1) f) ≤ q f := by
      simp only [q, smul_apply, NNReal.smul_def, smul_eq_mul, Seminorm.comp_apply]
      exact realMellinLower_seminorm_le n a ha s hs.1 f k j
    have hsum : r (∑ i ∈ Finset.range (n + 1), v i) ≤ ∑ i ∈ Finset.range (n + 1), u i f :=
      ((Finset.range (n + 1)).le_sum_of_subadditive r (map_zero r).le (map_add_le_add r) v).trans
        (Finset.sum_le_sum fun i _ ↦ hv i)
    simp only [add_apply, sum_apply]
    simp only [schwartzMellinTaylorChart, add_apply, sum_apply, smul_apply]
    exact (map_add_le_add r _ _).trans
      (add_le_add ((map_add_le_add r _ _).trans (add_le_add ht hl)) hsum)

/-- Restrict a coupled Schwartz test to a fixed value of the retained variable. -/
def archimedeanSlice {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (y : Y) : 𝓢(X × Y, ℂ) →L[ℂ] 𝓢(X, ℂ) :=
  SchwartzMap.compCLMOfAntilipschitz ℂ
    ((ContinuousLinearMap.inl ℝ X Y).hasTemperateGrowth.add (HasTemperateGrowth.const (0, y)))
    (K := 1) (by
      intro x z
      simp [edist_dist, Prod.dist_eq])

@[simp] theorem archimedeanSlice_apply {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (y : Y) (f : 𝓢(X × Y, ℂ)) (x : X) : archimedeanSlice y f x = f (x, y) := by
  change f ((x, 0) + (0, y)) = _
  simp

private theorem taylor_sub_eq_integral (g : 𝓢(ℝ, ℂ)) (n : ℕ) (t : ℝ) :
    g t - ∑ k ∈ Finset.range (n + 1), mellinTaylorCoeff g k * (t : ℂ) ^ k =
      (t : ℂ) ^ (n + 1) * ∫ r in Ioc (0 : ℝ) 1,
        (↑((1 - r) ^ n / (n.factorial : ℝ)) : ℂ) * iteratedDeriv (n + 1) g (t * r) := by
  have ht := map_add_eq_sum_add_integral_iteratedFDeriv
    (f := (g : ℝ → ℂ)) (x := 0) (y := t) (n := n)
    (fun _ _ => (g.smooth (n + 1)).contDiffAt)
  simp only [zero_add, smul_eq_mul, iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, Complex.real_smul,
    intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)] at ht
  have hsum : (∑ k ∈ Finset.range (n + 1), (↑((k.factorial : ℝ)⁻¹) : ℂ) *
      ((↑(t ^ k) : ℂ) * iteratedDeriv k g 0)) =
      ∑ k ∈ Finset.range (n + 1), mellinTaylorCoeff g k * (t : ℂ) ^ k := by
    apply Finset.sum_congr rfl
    intro k _
    simp only [mellinTaylorCoeff, Complex.ofReal_inv, Complex.ofReal_natCast, Complex.ofReal_pow]
    ring
  rw [hsum, add_comm] at ht
  apply (sub_eq_iff_eq_add).2
  calc
    g t = (↑((n.factorial : ℝ)⁻¹) : ℂ) *
        (∫ r in Ioc (0 : ℝ) 1,
          (↑((1 - r) ^ n) : ℂ) * ((↑(t ^ (n + 1)) : ℂ) * iteratedDeriv (n + 1) g (r * t))) +
        ∑ k ∈ Finset.range (n + 1), mellinTaylorCoeff g k * (t : ℂ) ^ k := ht
    _ = _ := by
      rw [← integral_const_mul, ← integral_const_mul]
      congr 1
      apply integral_congr_ae
      exact .of_forall fun r => by
        dsimp only
        rw [mul_comm r t]
        push_cast
        ring

private theorem realMellinLower_apply (n : ℕ) (s : ℂ) (hs : -((n + 1 : ℕ) : ℝ) < s.re)
    (f : 𝓢(ℝ × Y, ℂ)) (y : Y) :
    realMellinLower n s hs f y =
      ∫ t in Ioc (0 : ℝ) 1, (t : ℂ) ^ (s - 1) *
        (f (t, y) - ∑ k ∈ Finset.range (n + 1),
          mellinTaylorCoeff (archimedeanSlice y f) k * (t : ℂ) ^ k) := by
  have hi : Integrable (fun p : ℝ × ℝ =>
      lowerMellinKernel n s p * realFirstJet (n + 1) f (p.1 * p.2, y))
      (unitIntervalHaar.prod unitIntervalHaar) :=
    schwartzPartialIntegral_integrable (measurable_fst.mul measurable_snd)
    (lowerMellinKernel_measurable n s).aestronglyMeasurable
    (lowerMellinMajorant_integrable n s hs) (realFirstJet (n + 1) f) y
  change (∫ p : ℝ × ℝ, lowerMellinKernel n s p * realFirstJet (n + 1) f (p.1 * p.2, y)
    ∂unitIntervalHaar.prod unitIntervalHaar) = _
  rw [integral_prod _ hi]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro t ht
  dsimp only
  let g := archimedeanSlice y f
  have hne : (t : ℂ) ≠ 0 := by exact_mod_cast ht.1.ne'
  rw [show f (t, y) = g t from (archimedeanSlice_apply y f t).symm, taylor_sub_eq_integral g, ← mul_assoc,
    ← Complex.cpow_natCast, ← Complex.cpow_add _ _ hne, ← integral_const_mul]
  apply integral_congr_ae
  exact .of_forall fun r => by
    dsimp only
    rw [lowerMellinKernel, realFirstJet_apply]
    change _ = (t : ℂ) ^ (s - 1 + (n + 1 : ℕ)) *
      (↑((1 - r) ^ n / (n.factorial : ℝ)) * iteratedDeriv (n + 1) (fun t => g t) (t * r))
    simp only [g, archimedeanSlice_apply]
    ring

/-- The Schwartz-valued chart agrees at each slice with the scalar
continuation. This also gives compatibility of all overlapping charts. -/
theorem schwartzMellinTaylorChart_apply (n : ℕ) (s : ℂ)
    (hs : -((n + 1 : ℕ) : ℝ) < s.re) (f : 𝓢(ℝ × Y, ℂ)) (y : Y) :
    schwartzMellinTaylorChart n s hs f y = mellinTaylorContinued (archimedeanSlice y f) s := by
  let g := archimedeanSlice y f
  change _ = mellinTaylorContinued g.toFun s
  rw [mellinTaylorContinued_eq_split g.smooth' (schwartz_radial_rapid g) n hs]
  simp only [schwartzMellinTaylorChart, add_apply, sum_apply]
  rw [realMellinLower_apply]
  let G : ℝ → ℂ := fun t => f (t, y)
  have hg : (⇑(archimedeanSlice y f)) = G := funext (archimedeanSlice_apply y f)
  have hg' : g.toFun = G := hg
  have htail : realMellinTail s f y = ∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (s - 1) * G t := rfl
  change _ + (∑ k ∈ Finset.range (n + 1), (((k.factorial : ℂ) * (s + k))⁻¹) *
    realFirstJet k f (0, y)) = _
  rw [htail, hg]
  try rw [hg']
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [realFirstJet_apply, mellinTaylorCoeff, mul_inv, div_eq_mul_inv]
  ring


private theorem realMellinChart_exists (s : ℂ) : ∃ n : ℕ, -((n + 1 : ℕ) : ℝ) < s.re := by
  obtain ⟨n, hn⟩ := exists_nat_gt (-s.re)
  exact ⟨n, by push_cast; linarith⟩

/-- The Mellin continuation acts on one real coordinate of a Schwartz test
and leaves a Schwartz test in the remaining coordinates. -/
def schwartzMellinContinuedInFirst (s : ℂ) : 𝓢(ℝ × Y, ℂ) →L[ℂ] 𝓢(Y, ℂ) :=
  schwartzMellinTaylorChart (realMellinChart_exists s).choose s (realMellinChart_exists s).choose_spec

@[simp] theorem schwartzMellinContinuedInFirst_apply (s : ℂ)
    (f : 𝓢(ℝ × Y, ℂ)) (y : Y) :
    schwartzMellinContinuedInFirst s f y = mellinTaylorContinued (archimedeanSlice y f) s :=
  schwartzMellinTaylorChart_apply _ s _ f y

/-- A closed strip admits a single chart, giving uniform seminorm
control of the continued real Mellin contraction at large imaginary heights. -/
theorem schwartzMellinContinuedInFirst_uniform_seminorm (a b : ℝ) (k j : ℕ) :
    ∃ p : Seminorm ℂ 𝓢(ℝ × Y, ℂ), Continuous p ∧
      ∀ (s : ℂ), s.re ∈ Icc a b → 1 ≤ |s.im| → ∀ (f : 𝓢(ℝ × Y, ℂ)),
        SchwartzMap.seminorm ℂ k j (schwartzMellinContinuedInFirst s f) ≤ p f := by
  obtain ⟨n, hn⟩ := realMellinChart_exists (a : ℂ)
  obtain ⟨p, hp, h⟩ := schwartzMellinTaylorChart_uniform_seminorm (Y := Y) n a b
    (by simpa only [Complex.ofReal_re] using hn) k j
  refine ⟨p, hp, fun s hs hi f ↦ ?_⟩
  have hns : -((n + 1 : ℕ) : ℝ) < s.re := (by simpa only [Complex.ofReal_re] using hn :
    -((n + 1 : ℕ) : ℝ) < a).trans_le hs.1
  have he : schwartzMellinContinuedInFirst s f = schwartzMellinTaylorChart n s hns f := by
    ext y
    rw [schwartzMellinContinuedInFirst_apply, schwartzMellinTaylorChart_apply]
  rw [he]
  exact h s hs hi f

private def realReflectFirst : 𝓢(ℝ × Y, ℂ) →L[ℂ] 𝓢(ℝ × Y, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    ((LinearIsometryEquiv.neg ℝ).toContinuousLinearEquiv.prodCongr (ContinuousLinearEquiv.refl ℝ Y))

/-- Real-place zeta contraction with a sign character, continued in the
spectral parameter and acting on a possibly coupled Schwartz test. -/
def realArchimedeanZetaInFirst (a : ℕ) (s : ℂ) : 𝓢(ℝ × Y, ℂ) →L[ℂ] 𝓢(Y, ℂ) :=
  (schwartzMellinContinuedInFirst s).comp
    (ContinuousLinearMap.id ℂ _ + (-1 : ℂ) ^ a • realReflectFirst)

/-- Uniform strip bound for the continued real-place zeta contraction. -/
theorem realArchimedeanZetaInFirst_uniform_seminorm (ε : ℕ) (a b : ℝ) (k j : ℕ) :
    ∃ p : Seminorm ℂ 𝓢(ℝ × Y, ℂ), Continuous p ∧
      ∀ (s : ℂ), s.re ∈ Icc a b → 1 ≤ |s.im| → ∀ (f : 𝓢(ℝ × Y, ℂ)),
        SchwartzMap.seminorm ℂ k j (realArchimedeanZetaInFirst ε s f) ≤ p f := by
  obtain ⟨p, hp, hbound⟩ := schwartzMellinContinuedInFirst_uniform_seminorm (Y := Y) a b k j
  let T : 𝓢(ℝ × Y, ℂ) →L[ℂ] 𝓢(ℝ × Y, ℂ) :=
    ContinuousLinearMap.id ℂ _ + (-1 : ℂ) ^ ε • realReflectFirst
  exact ⟨p.comp T.toLinearMap, hp.comp T.continuous, fun s hs hi f ↦ hbound s hs hi (T f)⟩

@[simp] theorem realArchimedeanZetaInFirst_apply (a : ℕ) (s : ℂ)
    (f : 𝓢(ℝ × Y, ℂ)) (y : Y) :
    realArchimedeanZetaInFirst a s f y =
      realArchimedeanZetaContinued a (archimedeanSlice y f) s := by
  rw [realArchimedeanZetaInFirst, ContinuousLinearMap.comp_apply, schwartzMellinContinuedInFirst_apply,
    realArchimedeanZetaContinued]
  congr 1
  funext t
  simp only [archimedeanSlice_apply, realZetaProfile_apply, add_apply,
    ContinuousLinearMap.id_apply, smul_apply, smul_eq_mul]
  rfl

theorem realArchimedeanZetaInFirst_eq_integral (a : ℕ) (s : ℂ) (hs : 0 < s.re)
    (f : 𝓢(ℝ × Y, ℂ)) (y : Y) :
    realArchimedeanZetaInFirst a s f y = ∫ t : ℝ,
      ((|t| : ℝ) : ℂ) ^ (s - 1) * (if t < 0 then (-1 : ℂ) ^ a else 1) * f (t, y) := by
  rw [realArchimedeanZetaInFirst_apply,
    (realArchimedeanZetaContinued_eq_integral a (archimedeanSlice y f) hs).2]
  simp only [realArchimedeanZetaIntegral, realArchimedeanZetaIntegrand, archimedeanSlice_apply]

theorem realArchimedeanZetaInFirst_meromorphic (a : ℕ) (f : 𝓢(ℝ × Y, ℂ)) (y : Y) :
    Meromorphic (fun s => realArchimedeanZetaInFirst a s f y) := by
  simpa only [realArchimedeanZetaInFirst_apply] using
    realArchimedeanZetaContinued_meromorphic a (archimedeanSlice y f)

theorem schwartzPolarMellin_eq_continued (ν : Measure Circle) [IsFiniteMeasure ν]
    (j : ℤ) (s : ℂ) (hs : 0 < s.re) (f : 𝓢(ℂ × Y, ℂ)) (y : Y) :
    schwartzPolarMellin ν j s hs f y =
      complexArchimedeanZetaContinued ν j (archimedeanSlice y f) s := by
  rw [(complexArchimedeanZetaContinued_eq_polarIntegral ν j (archimedeanSlice y f) hs).2,
    schwartzPolarMellin_apply]
  simp only [complexArchimedeanZetaPolarIntegrand, archimedeanSlice_apply, mul_assoc]


private def radialPullback (u : Circle) : ℝ × Y →L[ℝ] ℂ × Y :=
  (ContinuousLinearMap.prodMapL ℝ ℝ ℂ Y Y)
    (ContinuousLinearMap.smulRightL ℝ ℝ ℂ (ContinuousLinearMap.id ℝ ℝ) (u : ℂ),
      ContinuousLinearMap.id ℝ Y)

private theorem radialPullback_continuous : Continuous (radialPullback (Y := Y)) :=
  (ContinuousLinearMap.prodMapL ℝ ℝ ℂ Y Y).continuous.comp
    (((ContinuousLinearMap.smulRightL ℝ ℝ ℂ (ContinuousLinearMap.id ℝ ℝ)).continuous.comp
      continuous_subtype_val).prodMk continuous_const)

private theorem radialPullback_isometric (u : Circle) (p : ℝ × Y) :
    ‖radialPullback u p‖ = ‖p‖ := by
  change ‖(p.1 • (u : ℂ), p.2)‖ = ‖p‖
  simp only [Prod.norm_def, norm_smul, Circle.norm_coe, mul_one]

/-- Angular projection of a coupled complex-coordinate test, with the
remaining coordinates retained in the Schwartz topology. -/
def schwartzRadialProjection (ν : Measure Circle) [IsFiniteMeasure ν] (j : ℤ) :
    𝓢(ℂ × Y, ℂ) →L[ℂ] 𝓢(ℝ × Y, ℂ) :=
  schwartzIsometricAverage (μ := ν) radialPullback_continuous radialPullback_isometric
    ((continuous_subtype_val : Continuous (fun u : Circle => (u : ℂ))).zpow₀ j
      (fun u => Or.inl (Circle.coe_ne_zero u)))
    (by intro u; rw [norm_zpow, Circle.norm_coe, one_zpow])

@[simp] theorem schwartzRadialProjection_apply (ν : Measure Circle) [IsFiniteMeasure ν] (j : ℤ)
    (f : 𝓢(ℂ × Y, ℂ)) (t : ℝ) (y : Y) :
    schwartzRadialProjection ν j f (t, y) =
      ∫ u : Circle, (u : ℂ) ^ j * f (t • (u : ℂ), y) ∂ν :=
  rfl

/-- Complex-place zeta contraction on the first coordinate of a coupled
Schwartz test, using the squared complex modulus. -/
def complexArchimedeanZetaInFirst (ν : Measure Circle) [IsFiniteMeasure ν] (j : ℤ) (s : ℂ) :
    𝓢(ℂ × Y, ℂ) →L[ℂ] 𝓢(Y, ℂ) :=
  (schwartzMellinContinuedInFirst (2 * s)).comp (schwartzRadialProjection ν j)

/-- Uniform strip bound for the continued complex-place zeta contraction. -/
theorem complexArchimedeanZetaInFirst_uniform_seminorm (ν : Measure Circle) [IsFiniteMeasure ν]
    (ε : ℤ) (a b : ℝ) (k j : ℕ) :
    ∃ p : Seminorm ℂ 𝓢(ℂ × Y, ℂ), Continuous p ∧
      ∀ (s : ℂ), s.re ∈ Icc a b → 1 ≤ |s.im| → ∀ (f : 𝓢(ℂ × Y, ℂ)),
        SchwartzMap.seminorm ℂ k j (complexArchimedeanZetaInFirst ν ε s f) ≤ p f := by
  obtain ⟨p, hp, hbound⟩ := schwartzMellinContinuedInFirst_uniform_seminorm (Y := Y) (2 * a) (2 * b) k j
  let T := schwartzRadialProjection (Y := Y) ν ε
  refine ⟨p.comp T.toLinearMap, hp.comp T.continuous, fun s hs hi f ↦ ?_⟩
  apply hbound (2 * s) _ _ (T f)
  · simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]
    exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  · simp only [Complex.mul_im, Complex.re_ofNat, Complex.im_ofNat, zero_mul, add_zero,
      abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    linarith

@[simp] theorem complexArchimedeanZetaInFirst_apply (ν : Measure Circle) [IsFiniteMeasure ν]
    (j : ℤ) (s : ℂ) (f : 𝓢(ℂ × Y, ℂ)) (y : Y) :
    complexArchimedeanZetaInFirst ν j s f y =
      complexArchimedeanZetaContinued ν j (archimedeanSlice y f) s := by
  rw [complexArchimedeanZetaInFirst, ContinuousLinearMap.comp_apply,
    schwartzMellinContinuedInFirst_apply, complexArchimedeanZetaContinued]
  congr 1
  funext t
  simp only [archimedeanSlice_apply, schwartzRadialProjection_apply, complexZetaProfile]

theorem complexArchimedeanZetaInFirst_meromorphic (ν : Measure Circle) [IsFiniteMeasure ν]
    (j : ℤ) (f : 𝓢(ℂ × Y, ℂ)) (y : Y) :
    Meromorphic (fun s => complexArchimedeanZetaInFirst ν j s f y) := by
  simpa only [complexArchimedeanZetaInFirst_apply] using
    complexArchimedeanZetaContinued_meromorphic ν j (archimedeanSlice y f)

theorem complexArchimedeanZetaInFirst_eq_polar (ν : Measure Circle) [IsFiniteMeasure ν]
    (j : ℤ) (s : ℂ) (hs : 0 < s.re) :
    complexArchimedeanZetaInFirst (Y := Y) ν j s = schwartzPolarMellin ν j s hs := by
  ext f y
  rw [complexArchimedeanZetaInFirst_apply, schwartzPolarMellin_eq_continued]


private theorem real_cpow_addParameter {t : ℝ} (ht : 0 < t) (z b h : ℂ) :
    (t : ℂ) ^ (z + h + b) = (t : ℂ) ^ (z + b) * Complex.exp (h * (Real.log t : ℂ)) := by
  have hne : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  have he : (t : ℂ) ^ h = Complex.exp (h * (Real.log t : ℂ)) := by
    rw [Complex.cpow_def_of_ne_zero hne, ← Complex.ofReal_log ht.le, mul_comm _ h]
  rw [show z + h + b = z + b + h by ring, Complex.cpow_add _ _ hne, he]

private theorem realMellinTail_hasOperatorTaylorEstimate (c : ℂ) :
    ∃ D, HasOperatorTaylorEstimate (realMellinTail (Y := Y)) c D := by
  let μ : Measure ℝ := volume.restrict (Ioi 1)
  let w (s : ℂ) (t : ℝ) := (t : ℂ) ^ (s - 1)
  obtain ⟨m, hm⟩ := exists_nat_gt (c.re + 2)
  have hI : ∀ᶠ h : ℂ in 𝓝 0,
      Integrable (schwartzKernelMajorant (id : ℝ → ℝ) (w (c + h)) m) μ := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) zero_lt_one] with h hh
    have hnorm : ‖h‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using hh
    apply mellinMajorant_tail_integrable
    rw [Complex.add_re]
    linarith [Complex.re_le_norm h]
  have hpow (h : ℂ) : ∀ᵐ t ∂μ, w (c + h) t = w c t * Complex.exp (h * (Real.log t : ℂ)) := by
    filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioi (a := (1 : ℝ)))] with t ht
    simpa only [w, sub_eq_add_neg] using
      real_cpow_addParameter (zero_lt_one.trans (mem_Ioi.mp ht)) c (-1) h
  have hM : Integrable (fun t =>
      schwartzKernelMajorant (id : ℝ → ℝ) (w c) m t * Real.exp ((2 * 1) * |Real.log t|)) μ := by
    have he := mellinMajorant_tail_integrable (c + 2) m (by simpa using hm)
    apply he.congr
    filter_upwards [hpow 2,
      ae_restrict_mem (μ := volume) (measurableSet_Ioi (a := (1 : ℝ)))] with t hw ht
    have hlog : 0 ≤ Real.log t := Real.log_nonneg (mem_Ioi.mp ht).le
    change schwartzKernelMajorant id (w (c + 2)) m t = _
    simp only [schwartzKernelMajorant, hw, norm_mul, Complex.norm_exp, abs_of_nonneg hlog,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.re_ofNat, mul_zero,
      sub_zero, mul_one]
    ring
  exact schwartzKernel_exp_hasOperatorTaylorEstimate (μ := μ) (γ := id) (w := w)
    measurable_id m (fun z => (measurable_real_cpow (z - 1)).aestronglyMeasurable)
    Real.measurable_log (mellinMajorant_tail_integrable c m (by linarith)) hI
    (.of_forall fun _ _ _ => rfl) (.of_forall hpow) zero_lt_one hM

private def realMellinLowerOn (n : ℕ) (s : ℂ) : 𝓢(ℝ × Y, ℂ) →L[ℂ] 𝓢(Y, ℂ) :=
  if hs : -((n + 1 : ℕ) : ℝ) < s.re then realMellinLower n s hs else 0

private theorem realMellinLowerOn_hasOperatorTaylorEstimate (n : ℕ) {c : ℂ}
    (hc : -((n + 1 : ℕ) : ℝ) < c.re) :
    ∃ D, HasOperatorTaylorEstimate (realMellinLowerOn (Y := Y) n) c D := by
  let μ := unitIntervalHaar.prod unitIntervalHaar
  let γ (p : ℝ × ℝ) := p.1 * p.2
  let w := lowerMellinKernel n
  let ell (p : ℝ × ℝ) := Real.log p.1
  let ρ := (c.re + ((n + 1 : ℕ) : ℝ)) / 4
  have hρ : 0 < ρ := by dsimp [ρ]; linarith
  have hγ : Measurable γ := measurable_fst.mul measurable_snd
  have hnear : ∀ᶠ h : ℂ in 𝓝 0, -((n + 1 : ℕ) : ℝ) < (c + h).re := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hρ] with h hh
    have hnorm : ‖h‖ < ρ := by simpa only [Metric.mem_ball, dist_zero_right] using hh
    rw [Complex.add_re]
    have hRe := (abs_le.mp (Complex.abs_re_le_norm h)).1
    dsimp [ρ] at hnorm
    linarith
  have hI : ∀ᶠ h : ℂ in 𝓝 0, Integrable (schwartzKernelMajorant γ (w (c + h)) 0) μ :=
    hnear.mono fun h hh => lowerMellinMajorant_integrable n (c + h) hh
  have hpos : ∀ᵐ p : ℝ × ℝ ∂μ, p.1 ∈ Ioc (0 : ℝ) 1 := by
    exact (Measure.ae_prod_iff_ae_ae (measurableSet_Ioc.preimage measurable_fst)).mpr
      ((ae_restrict_mem (μ := volume) measurableSet_Ioc).mono fun _ ht => .of_forall fun _ => ht)
  have hpow (h : ℂ) : ∀ᵐ p ∂μ, w (c + h) p = w c p * Complex.exp (h * (ell p : ℂ)) := by
    filter_upwards [hpos] with p hp
    have he := real_cpow_addParameter hp.1 c ((n + 1 : ℕ) - 1 : ℂ) h
    unfold w lowerMellinKernel ell
    rw [show c + h - 1 + ((n + 1 : ℕ) : ℂ) = c + h + (((n + 1 : ℕ) : ℂ) - 1) by ring,
      he, show c + ((↑(n + 1) : ℂ) - 1) = c - 1 + ↑(n + 1) by ring]
    ring
  have hM : Integrable (fun p => schwartzKernelMajorant γ (w c) 0 p *
      Real.exp ((2 * ρ) * |ell p|)) μ := by
    have hleft : -((n + 1 : ℕ) : ℝ) < (c + (-((2 * ρ : ℝ) : ℂ))).re := by
      rw [Complex.add_re, Complex.neg_re, Complex.ofReal_re]
      dsimp [ρ]
      linarith
    apply (lowerMellinMajorant_integrable n _ hleft).congr
    filter_upwards [hpow (-((2 * ρ : ℝ) : ℂ)), hpos] with p hp hmem
    have hlog : ell p ≤ 0 := Real.log_nonpos hmem.1.le hmem.2
    change schwartzKernelMajorant γ (w (c + (-((2 * ρ : ℝ) : ℂ)))) 0 p = _
    rw [schwartzKernelMajorant, hp, norm_mul, Complex.norm_exp, abs_of_nonpos hlog]
    simp only [neg_mul, Complex.neg_re, ← Complex.ofReal_mul, Complex.ofReal_re,
      schwartzKernelMajorant]
    rw [mul_neg]
    ring
  let A (s : ℂ) : 𝓢(ℝ × Y, ℂ) →L[ℂ] 𝓢(Y, ℂ) :=
    if hs : -((n + 1 : ℕ) : ℝ) < s.re then
      schwartzPartialIntegralCLM hγ (lowerMellinKernel_measurable n s).aestronglyMeasurable
        (lowerMellinMajorant_integrable n s hs)
    else 0
  have hA : ∀ᶠ h : ℂ in 𝓝 0, ∀ (f : 𝓢(ℝ × Y, ℂ)) y,
      A (c + h) f y = ∫ p, w (c + h) p * f (γ p, y) ∂μ := by
    filter_upwards [hnear] with h hh f y
    dsimp only [A]
    rw [dite_eq_left hh, schwartzPartialIntegralCLM_apply]
  obtain ⟨D, hD⟩ := schwartzKernel_exp_hasOperatorTaylorEstimate hγ 0
    (fun z => (lowerMellinKernel_measurable n z).aestronglyMeasurable)
    (Real.measurable_log.comp measurable_fst) (lowerMellinMajorant_integrable n c hc) hI hA
    (.of_forall hpow) hρ hM
  refine ⟨_, (hD.comp (HasOperatorTaylorEstimate.const (realFirstJet (n + 1)) c)).congr ?_⟩
  have hNhds : ∀ᶠ z : ℂ in 𝓝 c, -((n + 1 : ℕ) : ℝ) < z.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hc
  filter_upwards [hNhds] with z hz
  dsimp only [A]
  rw [dite_eq_left hz, realMellinLowerOn, dite_eq_left hz, realMellinLower]


/-- A common local denominator for the real Mellin chart. -/
def schwartzMellinDenominator (n : ℕ) (s : ℂ) : ℂ :=
  ∏ k ∈ Finset.range (n + 1), (s + k)

/-- The real Mellin chart with its denominators cleared. The upper and
lower kernels and the finitely many zero-slice jets are all retained. -/
def schwartzMellinNumerator (n : ℕ) (s : ℂ) :
    𝓢(ℝ × Y, ℂ) →L[ℂ] 𝓢(Y, ℂ) :=
  schwartzMellinDenominator n s • (realMellinTail s + realMellinLowerOn n s) +
    ∑ k ∈ Finset.range (n + 1),
      (∏ l ∈ (Finset.range (n + 1)).erase k, (s + (l : ℂ))) •
        ((k.factorial : ℂ)⁻¹ • realOriginSlice.comp (realFirstJet k))

theorem schwartzMellinNumerator_hasOperatorTaylorEstimate (n : ℕ) {c : ℂ}
    (hc : -((n + 1 : ℕ) : ℝ) < c.re) :
    ∃ D, HasOperatorTaylorEstimate (schwartzMellinNumerator (Y := Y) n) c D := by
  obtain ⟨_, hT⟩ := realMellinTail_hasOperatorTaylorEstimate (Y := Y) c
  obtain ⟨_, hL⟩ := realMellinLowerOn_hasOperatorTaylorEstimate (Y := Y) n hc
  obtain ⟨_, hProd⟩ := (hT.add hL).smul_linear_factors (Finset.range (n + 1)) (fun k => (k : ℂ))
  obtain ⟨_, hSum⟩ := HasOperatorTaylorEstimate.finset_sum (c := c) (Finset.range (n + 1))
    (fun k s => (∏ l ∈ (Finset.range (n + 1)).erase k, (s + (l : ℂ))) •
      ((k.factorial : ℂ)⁻¹ • (realOriginSlice (Y := Y)).comp (realFirstJet k))) (fun k _ =>
        (HasOperatorTaylorEstimate.const _ c).smul_linear_factors _ _)
  exact ⟨_, hProd.add hSum⟩

theorem schwartzMellinNumerator_eq (n : ℕ) {s : ℂ}
    (hs : -((n + 1 : ℕ) : ℝ) < s.re)
    (h : ∀ k ∈ Finset.range (n + 1), s + (k : ℂ) ≠ 0) :
    schwartzMellinNumerator (Y := Y) n s =
      schwartzMellinDenominator n s • schwartzMellinContinuedInFirst s := by
  have he : schwartzMellinContinuedInFirst (Y := Y) s = schwartzMellinTaylorChart n s hs := by
    ext f y
    rw [schwartzMellinContinuedInFirst_apply, schwartzMellinTaylorChart_apply]
  rw [he, schwartzMellinNumerator, schwartzMellinTaylorChart, realMellinLowerOn,
    dite_eq_left hs]
  simp only [smul_add, Finset.smul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [smul_smul, smul_smul, schwartzMellinDenominator,
    ← Finset.prod_erase_mul _ _ hk, mul_inv, mul_mul_mul_comm]
  rw [mul_inv_cancel₀ (h k hk), mul_one]


private theorem schwartzMellinScaled_meromorphicOperator (a : ℂ) (ha : a ≠ 0) :
    MeromorphicOperator (fun z => schwartzMellinContinuedInFirst (Y := Y) (a * z)) := by
  intro c
  obtain ⟨n, hn⟩ := realMellinChart_exists (a * c)
  let S := Finset.range (n + 1)
  have hU : ∀ᶠ z : ℂ in 𝓝 c, -((n + 1 : ℕ) : ℝ) < (a * z).re :=
    (isOpen_lt continuous_const (Complex.continuous_re.comp (continuous_const.mul continuous_id))).mem_nhds hn
  have hP : AnalyticAt ℂ (fun z => schwartzMellinDenominator n (a * z)) c := by
    unfold schwartzMellinDenominator
    apply S.analyticAt_fun_prod
    exact fun k _ => (analyticAt_const.mul analyticAt_id).add analyticAt_const
  have hne : ∀ᶠ z : ℂ in 𝓝[≠] c, ∀ k ∈ S, a * z + (k : ℂ) ≠ 0 := by
    apply S.eventually_all.mpr
    intro k _
    let r := -(k : ℂ) / a
    have hr : ∀ᶠ z : ℂ in 𝓝[≠] c, z ≠ r := by
      by_cases he : r = c
      · rw [he]
        exact self_mem_nhdsWithin
      · exact eventually_ne_nhdsWithin (Ne.symm he)
    filter_upwards [hr] with z hz hz'
    apply hz
    exact (eq_div_iff ha).2 (by linear_combination hz')
  refine ⟨fun z => schwartzMellinDenominator n (a * z), fun z => schwartzMellinNumerator n (a * z),
    hP, hne.mono (fun z h => Finset.prod_ne_zero_iff.mpr h), ?_, ?_⟩
  · filter_upwards [hne, hU.filter_mono nhdsWithin_le_nhds] with z hz hU
    exact schwartzMellinNumerator_eq n hU hz
  · filter_upwards [hU] with z hz
    obtain ⟨D, hD⟩ := schwartzMellinNumerator_hasOperatorTaylorEstimate (Y := Y) n hz
    have he : HasOperatorTaylorEstimate (schwartzMellinNumerator (Y := Y) n) (a * z + 0) D := by
      simpa only [add_zero] using hD
    exact ⟨a • D, by simpa only [add_zero] using he.reparametrize a 0⟩

/-- Real-place contractions compose as meromorphic operator families, with
seminorm control on their pole-cleared Taylor remainders. -/
theorem realArchimedeanZetaInFirst_meromorphicOperator (a : ℕ) :
    MeromorphicOperator (realArchimedeanZetaInFirst (Y := Y) a) := by
  have h := schwartzMellinScaled_meromorphicOperator (Y := Y) 1 one_ne_zero
  simp only [one_mul] at h
  exact h.comp (.const _)

/-- Complex-place contractions have the same operator meromorphy, with
the doubled Mellin coordinate and continuous angular projection. -/
theorem complexArchimedeanZetaInFirst_meromorphicOperator
    (ν : Measure Circle) [IsFiniteMeasure ν] (j : ℤ) :
    MeromorphicOperator (complexArchimedeanZetaInFirst (Y := Y) ν j) :=
  (schwartzMellinScaled_meromorphicOperator (Y := Y) 2 (by norm_num)).comp (.const _)


private theorem schwartzMellin_comp_hasOperatorTaylorEstimate
    {X : Type*} [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    (T : X →L[ℂ] 𝓢(ℝ × Y, ℂ)) (c : ℂ)
    (hz : ∀ k : ℕ, c + k = 0 → ∀ f : X, ∀ y : Y,
      mellinTaylorCoeff (archimedeanSlice y (T f)) k = 0) :
    ∃ D, HasOperatorTaylorEstimate (fun z => (schwartzMellinContinuedInFirst z).comp T) c D := by
  classical
  obtain ⟨n, hn⟩ := realMellinChart_exists c
  let K : Finset ℕ := Finset.range (n + 1)
  let J : Finset ℕ := K.filter (fun k : ℕ => c + (k : ℂ) ≠ 0)
  let L (k : ℕ) := ((realOriginSlice (Y := Y)).comp (realFirstJet k)).comp T
  let B (k : ℕ) (z : ℂ) := ((k.factorial : ℂ) * (z + k))⁻¹ • L k
  obtain ⟨_, hT⟩ := realMellinTail_hasOperatorTaylorEstimate (Y := Y) c
  obtain ⟨_, hR⟩ := realMellinLowerOn_hasOperatorTaylorEstimate (Y := Y) n hn
  obtain ⟨_, hJ⟩ := HasOperatorTaylorEstimate.finset_sum (c := c) J B (by
    intro k hk
    have hden : (k.factorial : ℂ) * (c + k) ≠ 0 :=
      mul_ne_zero (by exact_mod_cast Nat.factorial_ne_zero k) (Finset.mem_filter.mp hk).2
    exact HasOperatorTaylorEstimate.analytic_smul_fixed
      ((analyticAt_const.mul (analyticAt_id.add analyticAt_const)).inv hden) (L k))
  refine ⟨_, ((hT.add hR).comp (HasOperatorTaylorEstimate.const T c) |>.add hJ).congr ?_⟩
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hn] with z h
  have he : schwartzMellinContinuedInFirst (Y := Y) z = schwartzMellinTaylorChart n z h := by
    ext f y
    rw [schwartzMellinContinuedInFirst_apply, schwartzMellinTaylorChart_apply]
  rw [he]
  suffices hsum : ∑ k ∈ J, B k z = ∑ k ∈ K, B k z by
    rw [hsum]
    ext f y
    simp only [ContinuousLinearMap.comp_apply, schwartzMellinTaylorChart, add_apply, sum_apply,
      B, L, smul_apply, realMellinLowerOn, dite_eq_left h, K]
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro k _ hk
  have hzero : c + (k : ℂ) = 0 := by
    by_contra hc
    exact hk (Finset.mem_filter.mpr ⟨‹k ∈ K›, hc⟩)
  have hL : L k = 0 := by
    ext f y
    have H := hz k hzero f y
    rw [mellinTaylorCoeff] at H
    have hder := (mul_eq_zero.mp H).resolve_left (inv_ne_zero (by exact_mod_cast Nat.factorial_ne_zero k))
    change realFirstJet k (T f) (0, y) = 0
    rw [realFirstJet_apply]
    have hslice : ⇑(archimedeanSlice y (T f)) = fun t => T f (t, y) :=
      funext (archimedeanSlice_apply y (T f))
    rwa [hslice] at hder
  simp only [B, hL, smul_zero]

/-- Regular real parameters include the removable points of opposite parity. -/
theorem realArchimedeanZetaInFirst_hasOperatorTaylorEstimate (a : ℕ) (c : ℂ)
    (hc : ∀ k : ℕ, c + k = 0 → Odd (a + k)) :
    ∃ D, HasOperatorTaylorEstimate (realArchimedeanZetaInFirst (Y := Y) a) c D := by
  let T : 𝓢(ℝ × Y, ℂ) →L[ℂ] 𝓢(ℝ × Y, ℂ) :=
    ContinuousLinearMap.id ℂ _ + (-1 : ℂ) ^ a • realReflectFirst
  exact schwartzMellin_comp_hasOperatorTaylorEstimate T c (by
    intro k hk f y
    have he : archimedeanSlice y (T f) = realZetaProfile a (archimedeanSlice y f) := by
      ext t
      simp only [T, archimedeanSlice_apply, realZetaProfile_apply, add_apply,
        ContinuousLinearMap.id_apply, smul_apply, smul_eq_mul]
      rfl
    rw [he, realZetaProfile_taylorCoeff, (hc k hk).neg_one_pow, add_neg_cancel, zero_mul])

set_option maxHeartbeats 600000 in
/-- The compact angular projection removes every candidate complex pole whose
degree is absent from the character's angular lattice. -/
theorem complexArchimedeanZetaInFirst_hasOperatorTaylorEstimate (ν : Measure Circle)
    [IsFiniteMeasure ν] [ν.IsMulLeftInvariant] (j : ℤ) (c : ℂ)
    (hc : ∀ k : ℕ, 2 * c + k = 0 → ¬ ∃ n : ℕ, k = j.natAbs + 2 * n) :
    ∃ D, HasOperatorTaylorEstimate (complexArchimedeanZetaInFirst (Y := Y) ν j) c D := by
  obtain ⟨D, hD⟩ := schwartzMellin_comp_hasOperatorTaylorEstimate (schwartzRadialProjection (Y := Y) ν j)
    (2 * c) (by
      intro k hk f y
      have he : archimedeanSlice y (schwartzRadialProjection ν j f) =
          complexZetaProfile ν j (archimedeanSlice y f) := by
        ext t
        simp only [archimedeanSlice_apply, schwartzRadialProjection_apply, complexZetaProfile]
      rw [he, complexZetaProfile_taylorCoeff]
      suffices H : (∑ i ∈ Finset.range (k + 1), if j + 2 * (i : ℤ) = k then
          (ν.real univ : ℂ) * (complexAngularPolynomial k (iteratedFDeriv ℝ k (archimedeanSlice y f) 0)).coeff i
        else 0) = 0 by rw [H, mul_zero]
      apply Finset.sum_eq_zero
      intro i hi
      exact ite_eq_right (fun h => hc k hk ((complexZeta_angularIndex_iff j k).mp
        ⟨i, Nat.le_of_lt_succ (Finset.mem_range.mp hi), h⟩)))
  have he : HasOperatorTaylorEstimate
      (fun z => (schwartzMellinContinuedInFirst z).comp (schwartzRadialProjection (Y := Y) ν j))
      (2 * c + 0) D := by simpa only [add_zero] using hD
  refine ⟨(2 : ℂ) • D, (he.reparametrize 2 0).congr (.of_forall fun z => ?_)⟩
  change (schwartzMellinContinuedInFirst (2 * z + 0)).comp (schwartzRadialProjection ν j) =
    complexArchimedeanZetaInFirst ν j z
  rw [add_zero, complexArchimedeanZetaInFirst]

private theorem schwartzMellin_comp_analyticOperatorGerm
    {X : Type*} [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    (T : X →L[ℂ] 𝓢(ℝ × Y, ℂ)) {c : ℂ} {g : ℂ → ℂ} (hg : AnalyticAt ℂ g c)
    (hz : ∀ k : ℕ, c + k = 0 → g c = 0 ∨ ∀ f : X, ∀ y : Y,
      mellinTaylorCoeff (archimedeanSlice y (T f)) k = 0) :
    AnalyticOperatorGerm (fun z => g z • (schwartzMellinContinuedInFirst z).comp T) c := by
  obtain ⟨n, hn⟩ := realMellinChart_exists c
  have hU : ∀ᶠ z : ℂ in 𝓝 c, -((n + 1 : ℕ) : ℝ) < z.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hn
  let L (k : ℕ) := ((realOriginSlice (Y := Y)).comp (realFirstJet k)).comp T
  let B (k : ℕ) (z : ℂ) := (g z * ((k.factorial : ℂ) * (z + k))⁻¹) • L k
  have hTail : AnalyticOperatorGerm (realMellinTail (Y := Y)) c :=
    .of_taylor (.of_forall realMellinTail_hasOperatorTaylorEstimate)
  have hLower : AnalyticOperatorGerm (realMellinLowerOn (Y := Y) n) c :=
    .of_taylor (hU.mono fun _ h => realMellinLowerOn_hasOperatorTaylorEstimate n h)
  have hMain := ((hTail.add hLower).comp (.const T)).smul hg
  have hB (k : ℕ) : AnalyticOperatorGerm (B k) c := by
    have hfac : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
    by_cases hne : c + (k : ℂ) = 0
    · by_cases hg₀ : g c = 0
      · have horder : (1 : ℕ) ≤ analyticOrderAt g c := by
          simpa only [Nat.cast_one] using
            Order.one_le_iff_ne_zero.mpr (hg.analyticOrderAt_ne_zero.mpr hg₀)
        obtain ⟨q, hq, he⟩ := (natCast_le_analyticOrderAt hg (n := 1)).mp horder
        have hqg : AnalyticAt ℂ (fun z => q z * (k.factorial : ℂ)⁻¹) c := hq.mul analyticAt_const
        apply ((AnalyticOperatorGerm.const (c := c) (L k)).smul hqg).congr
        have hshift (z : ℂ) : z + (k : ℂ) = z - c := by linear_combination hne
        filter_upwards [he.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hgz hz'
        have hzc : z - c ≠ 0 := sub_ne_zero.mpr hz'
        have heq : g z * ((k.factorial : ℂ) * (z + k))⁻¹ = q z * (k.factorial : ℂ)⁻¹ := by
          rw [hgz, pow_one, smul_eq_mul, hshift]
          field_simp
        simp only [B, heq]
      · have hL : L k = 0 := by
          ext f y
          have H := (hz k hne).resolve_left hg₀ f y
          rw [mellinTaylorCoeff] at H
          have hder := (mul_eq_zero.mp H).resolve_left (inv_ne_zero hfac)
          change realFirstJet k (T f) (0, y) = 0
          rw [realFirstJet_apply]
          have hslice : ⇑(archimedeanSlice y (T f)) = fun t => T f (t, y) :=
            funext (archimedeanSlice_apply y (T f))
          rwa [hslice] at hder
        simpa only [B, hL, smul_zero] using
          AnalyticOperatorGerm.const (c := c) (0 : X →L[ℂ] 𝓢(Y, ℂ))
    · exact (AnalyticOperatorGerm.const (c := c) (L k)).smul
        (hg.mul ((analyticAt_const.mul (analyticAt_id.add analyticAt_const)).inv (mul_ne_zero hfac hne)))
  apply (hMain.add
    (AnalyticOperatorGerm.finset_sum (Finset.range (n + 1)) (fun k _ => hB k))).congr
  filter_upwards [hU.filter_mono nhdsWithin_le_nhds] with z h
  have he : schwartzMellinContinuedInFirst (Y := Y) z = schwartzMellinTaylorChart n z h := by
    ext f y
    rw [schwartzMellinContinuedInFirst_apply, schwartzMellinTaylorChart_apply]
  rw [he]
  ext f y
  simp only [ContinuousLinearMap.comp_apply, schwartzMellinTaylorChart, add_apply, sum_apply,
    B, L, smul_apply, realMellinLowerOn, dite_eq_left h, smul_add, Finset.smul_sum, smul_smul]

/-- Multiplying a real archimedean contraction by an analytic scalar that
vanishes at its sign-parity poles gives an analytic operator germ. -/
theorem realArchimedeanZetaInFirst_analyticOperatorGerm (a : ℕ) {c : ℂ} {g : ℂ → ℂ}
    (hg : AnalyticAt ℂ g c) (hc : ∀ k : ℕ, c + k = 0 → Even (a + k) → g c = 0) :
    AnalyticOperatorGerm (fun z => g z • realArchimedeanZetaInFirst (Y := Y) a z) c := by
  let T : 𝓢(ℝ × Y, ℂ) →L[ℂ] 𝓢(ℝ × Y, ℂ) :=
    ContinuousLinearMap.id ℂ _ + (-1 : ℂ) ^ a • realReflectFirst
  exact schwartzMellin_comp_analyticOperatorGerm T hg (by
    intro k hk
    by_cases hp : Even (a + k)
    · exact Or.inl (hc k hk hp)
    · right
      intro f y
      have he : archimedeanSlice y (T f) = realZetaProfile a (archimedeanSlice y f) := by
        ext t
        simp only [T, archimedeanSlice_apply, realZetaProfile_apply, add_apply,
          ContinuousLinearMap.id_apply, smul_apply, smul_eq_mul]
        rfl
      rw [he, realZetaProfile_taylorCoeff, (Nat.not_even_iff_odd.mp hp).neg_one_pow, add_neg_cancel,
        zero_mul])

set_option maxHeartbeats 700000 in
/-- Multiplying a complex archimedean contraction by an analytic scalar that
vanishes at its angular lattice gives an analytic operator germ. -/
theorem complexArchimedeanZetaInFirst_analyticOperatorGerm (ν : Measure Circle)
    [IsFiniteMeasure ν] [ν.IsMulLeftInvariant] (j : ℤ) {c : ℂ} {g : ℂ → ℂ}
    (hg : AnalyticAt ℂ g c)
    (hc : ∀ k : ℕ, 2 * c + k = 0 → (∃ n : ℕ, k = j.natAbs + 2 * n) → g c = 0) :
    AnalyticOperatorGerm (fun z => g z • complexArchimedeanZetaInFirst (Y := Y) ν j z) c := by
  have hcenter : (2 * c) / 2 = c := by ring
  have hg' : AnalyticAt ℂ (fun z => g (z / 2)) (2 * c) := by
    have hdiv : AnalyticAt ℂ (fun z : ℂ => z / 2) (2 * c) := analyticAt_id.div_const
    exact (show AnalyticAt ℂ g ((2 * c) / 2) by simpa only [hcenter] using hg).comp (f := fun z : ℂ => z / 2) (x := 2 * c) hdiv
  have H := schwartzMellin_comp_analyticOperatorGerm (schwartzRadialProjection (Y := Y) ν j) hg' (by
    intro k hk
    by_cases hp : ∃ n : ℕ, k = j.natAbs + 2 * n
    · exact Or.inl (by simpa only [hcenter] using hc k hk hp)
    · right
      intro f y
      have he : archimedeanSlice y (schwartzRadialProjection ν j f) =
          complexZetaProfile ν j (archimedeanSlice y f) := by
        ext t
        simp only [archimedeanSlice_apply, schwartzRadialProjection_apply, complexZetaProfile]
      rw [he, complexZetaProfile_taylorCoeff]
      suffices H : (∑ i ∈ Finset.range (k + 1), if j + 2 * (i : ℤ) = k then
          (ν.real univ : ℂ) * (complexAngularPolynomial k (iteratedFDeriv ℝ k (archimedeanSlice y f) 0)).coeff i
        else 0) = 0 by rw [H, mul_zero]
      apply Finset.sum_eq_zero
      intro i hi
      exact ite_eq_right (fun h => hp ((complexZeta_angularIndex_iff j k).mp
        ⟨i, Nat.le_of_lt_succ (Finset.mem_range.mp hi), h⟩)))
  have he : AnalyticOperatorGerm
      (fun z => g (z / 2) • (schwartzMellinContinuedInFirst z).comp
        (schwartzRadialProjection (Y := Y) ν j)) (2 * c + 0) := by
    simpa only [add_zero] using H
  apply (he.affine 2 0 two_ne_zero).congr (.of_forall fun z => ?_)
  change _ = g ((2 * z + 0) / 2) •
    (schwartzMellinContinuedInFirst (2 * z + 0)).comp (schwartzRadialProjection ν j)
  have hh : (2 * z + 0) / 2 = z := by ring
  rw [hh, add_zero, complexArchimedeanZetaInFirst]

private theorem realFirstJet_flat (k : ℕ) (f : 𝓢(ℝ × Y, ℂ)) (p : ℝ × Y)
    (hf : ∀ i : ℕ, iteratedFDeriv ℝ i f p = 0) :
    ∀ n : ℕ, iteratedFDeriv ℝ n (realFirstJet k f) p = 0 := by
  induction k generalizing f with
  | zero => exact hf
  | succ k ih =>
    apply ih (realFirstDeriv f)
    intro n
    have hD : iteratedFDeriv ℝ n (fderiv ℝ f) p = 0 := by
      apply norm_eq_zero.mp
      rw [norm_iteratedFDeriv_fderiv, hf (n+1), norm_zero]
    let L := ContinuousLinearMap.apply ℝ ℂ ((1, 0) : ℝ × Y)
    have he : ⇑(realFirstDeriv f) = L ∘ fderiv ℝ f := by
      funext x
      rw [realFirstDeriv, SchwartzMap.lineDerivOpCLM_eq]
      rfl
    rw [he]
    change iteratedFDeriv ℝ n (L ∘ fderiv ℝ f.toFun) p = 0
    have hD' : iteratedFDeriv ℝ n (fderiv ℝ f.toFun) p = 0 := hD
    rw [L.iteratedFDeriv_comp_left (f.smooth'.fderiv_right (by simp)).contDiffAt
      (by exact_mod_cast le_top : (n : ℕ∞ω) ≤ ∞), hD']
    ext a
    simp

private def realMellinRegularPart (n : ℕ) (s : ℂ) :
    𝓢(ℝ × Y, ℂ) →L[ℂ] 𝓢(Y, ℂ) := realMellinTail s + realMellinLowerOn n s

private theorem realMellinRegularPart_germ (n : ℕ) {c : ℂ}
    (hc : -((n+1 : ℕ) : ℝ) < c.re) :
    AnalyticOperatorGerm (realMellinRegularPart (Y := Y) n) c := by
  apply AnalyticOperatorGerm.add
  · exact .of_taylor (.of_forall realMellinTail_hasOperatorTaylorEstimate)
  · have hU : ∀ᶠ z in 𝓝 c, -((n+1 : ℕ) : ℝ) < z.re :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hc
    exact .of_taylor (hU.mono fun _ h ↦ realMellinLowerOn_hasOperatorTaylorEstimate n h)

private theorem realMellinRegularPart_flat (n : ℕ) (s : ℂ) (f : 𝓢(ℝ × Y, ℂ)) (y : Y)
    (hf : ∀ t : ℝ, ∀ k : ℕ, iteratedFDeriv ℝ k f (t,y) = 0) (k : ℕ) :
    iteratedFDeriv ℝ k (realMellinRegularPart n s f) y = 0 := by
  unfold realMellinRegularPart
  rw [add_apply]
  change iteratedFDeriv ℝ k ((realMellinTail s f : Y → ℂ) + (realMellinLowerOn n s f : Y → ℂ)) y = 0
  rw [iteratedFDeriv_add_apply
    ((realMellinTail s f).smooth k).contDiffAt ((realMellinLowerOn n s f).smooth k).contDiffAt]
  have hT : iteratedFDeriv ℝ k (realMellinTail s f) y = 0 := by
    unfold realMellinTail
    exact schwartzPartialIntegralCLM_iteratedFDeriv_eq_zero _ _ _ f k y (fun t ↦ hf t k)
  have hL : iteratedFDeriv ℝ k (realMellinLowerOn n s f) y = 0 := by
    unfold realMellinLowerOn
    split_ifs with hs
    · unfold realMellinLower
      exact schwartzPartialIntegralCLM_iteratedFDeriv_eq_zero (measurable_fst.mul measurable_snd)
        (lowerMellinKernel_measurable n s).aestronglyMeasurable (lowerMellinMajorant_integrable n s hs)
        (realFirstJet (n+1) f) k y
        (fun t ↦ realFirstJet_flat (n+1) f (t,y) (hf t) k)
    · simp
  rw [hT, hL, add_zero]

private theorem realMellinRegularPart_eq (n : ℕ) (s : ℂ) (hs : -((n+1 : ℕ) : ℝ) < s.re)
    (f : 𝓢(ℝ × Y, ℂ)) (hf : ∀ y : Y, ∀ k : ℕ, iteratedFDeriv ℝ k f (0,y) = 0) :
    schwartzMellinContinuedInFirst s f = realMellinRegularPart n s f := by
  have hchart : schwartzMellinContinuedInFirst (Y := Y) s = schwartzMellinTaylorChart n s hs := by
    ext g y
    rw [schwartzMellinContinuedInFirst_apply, schwartzMellinTaylorChart_apply]
  rw [hchart, schwartzMellinTaylorChart, realMellinRegularPart, realMellinLowerOn, dite_eq_left hs, add_apply]
  have hzero (k : ℕ) : ((realOriginSlice (Y := Y)).comp (realFirstJet k)) f = 0 := by
    ext y
    change realFirstJet k f (0,y) = 0
    have h := realFirstJet_flat k f (0,y) (hf y) 0
    simpa only [iteratedFDeriv_zero_apply, zero_apply] using
      congrArg (fun m : ContinuousMultilinearMap ℝ (fun _ : Fin 0 ↦ ℝ × Y) ℂ ↦
        m (fun _ ↦ 0)) h
  simp only [add_apply, sum_apply, smul_apply, hzero, smul_zero, Finset.sum_const_zero, add_zero]

/-- Flatness of a derivative passes to a linear pullback at the corresponding point. -/
theorem schwartzLinearPullback_jet_zero {X Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] (L : X →L[ℝ] Z) (f : 𝓢(Z, ℂ)) (n : ℕ) (x : X)
    (h : iteratedFDeriv ℝ n f (L x) = 0) :
    iteratedFDeriv ℝ n (f.toFun ∘ L) x = 0 := by
  rw [L.iteratedFDeriv_comp_right f.smooth' x (by exact_mod_cast le_top : (n : ℕ∞ω) ≤ ∞)]
  change (iteratedFDeriv ℝ n f.toFun (L x)).compContinuousLinearMap _ = 0
  have h' : iteratedFDeriv ℝ n f.toFun (L x) = 0 := h
  rw [h']
  ext m
  simp

private theorem realFold_jet_zero (a : ℕ) (f : 𝓢(ℝ × Y, ℂ)) (p : ℝ × Y) (n : ℕ)
    (hp : iteratedFDeriv ℝ n f p = 0) (hq : iteratedFDeriv ℝ n f (-p.1,p.2) = 0) :
    iteratedFDeriv ℝ n (f + (-1 : ℂ)^a • realReflectFirst f : 𝓢(ℝ × Y, ℂ)) p = 0 := by
  change iteratedFDeriv ℝ n ((f : ℝ × Y → ℂ) +
    (((-1 : ℂ)^a • realReflectFirst f : 𝓢(ℝ × Y, ℂ)) : ℝ × Y → ℂ)) p = 0
  rw [iteratedFDeriv_add_apply (f.smooth n).contDiffAt
    (((-1 : ℂ)^a • realReflectFirst f : 𝓢(ℝ × Y, ℂ)).smooth n).contDiffAt]
  have h : iteratedFDeriv ℝ n (realReflectFirst f) p = 0 := by
    exact schwartzLinearPullback_jet_zero _ f n p hq
  change _ + iteratedFDeriv ℝ n ((-1 : ℂ)^a • (realReflectFirst f : ℝ × Y → ℂ)) p = 0
  rw [hp, iteratedFDeriv_const_smul_apply ((realReflectFirst f).smooth n).contDiffAt, h, zero_add]
  ext v
  simp

/-- Near every parameter, a real Mellin contraction on tests flat on the
zero slice agrees with an analytic operator family. This family also
preserves flatness on fibers of the retained variables. -/
theorem exists_realArchimedeanZetaInFirst_flatGerm (a : ℕ) (c : ℂ) :
    ∃ A : ℂ → 𝓢(ℝ × Y, ℂ) →L[ℂ] 𝓢(Y, ℂ), AnalyticOperatorGerm A c ∧
      ∀ᶠ z in 𝓝 c,
        (∀ f : 𝓢(ℝ × Y, ℂ), (∀ y : Y, ∀ k : ℕ, iteratedFDeriv ℝ k f (0,y) = 0) →
          realArchimedeanZetaInFirst a z f = A z f) ∧
        ∀ (f : 𝓢(ℝ × Y, ℂ)) (y : Y), (∀ t : ℝ, ∀ k : ℕ, iteratedFDeriv ℝ k f (t,y) = 0) →
          ∀ k : ℕ, iteratedFDeriv ℝ k (A z f) y = 0 := by
  obtain ⟨n, hn⟩ := realMellinChart_exists c
  let B : 𝓢(ℝ × Y, ℂ) →L[ℂ] 𝓢(ℝ × Y, ℂ) :=
    ContinuousLinearMap.id ℂ _ + (-1 : ℂ)^a • realReflectFirst
  refine ⟨fun z ↦ (realMellinRegularPart n z).comp B,
    (realMellinRegularPart_germ n hn).comp (.const B), ?_⟩
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hn] with z hz
  constructor
  · intro f hf
    change schwartzMellinContinuedInFirst z (B f) = _
    apply realMellinRegularPart_eq n z hz
    exact fun y k ↦ realFold_jet_zero a f (0,y) k (hf y k) (by simpa only [neg_zero] using hf y k)
  · intro f y hf k
    apply realMellinRegularPart_flat n z (B f) y _ k
    exact fun t i ↦ realFold_jet_zero a f (t,y) i (hf t i) (hf (-t) i)

/-- The flat-test regularization of the complex contraction has the same
fiberwise preservation property, with the squared modulus parameter. -/
theorem exists_complexArchimedeanZetaInFirst_flatGerm (ν : Measure Circle) [IsFiniteMeasure ν]
    (j : ℤ) (c : ℂ) :
    ∃ A : ℂ → 𝓢(ℂ × Y, ℂ) →L[ℂ] 𝓢(Y, ℂ), AnalyticOperatorGerm A c ∧
      ∀ᶠ z in 𝓝 c,
        (∀ f : 𝓢(ℂ × Y, ℂ), (∀ y : Y, ∀ k : ℕ, iteratedFDeriv ℝ k f (0,y) = 0) →
          complexArchimedeanZetaInFirst ν j z f = A z f) ∧
        ∀ (f : 𝓢(ℂ × Y, ℂ)) (y : Y), (∀ t : ℂ, ∀ k : ℕ, iteratedFDeriv ℝ k f (t,y) = 0) →
          ∀ k : ℕ, iteratedFDeriv ℝ k (A z f) y = 0 := by
  obtain ⟨n, hn⟩ := realMellinChart_exists (2*c)
  let B := schwartzRadialProjection (Y := Y) ν j
  have hA : AnalyticOperatorGerm (realMellinRegularPart (Y := Y) n) (2*c+0) := by
    simpa only [add_zero] using realMellinRegularPart_germ (Y := Y) n hn
  have hscaled : AnalyticOperatorGerm (fun z ↦ realMellinRegularPart (Y := Y) n (2*z)) c :=
    (hA.affine 2 0 two_ne_zero).congr (.of_forall fun z ↦ by simp only [add_zero])
  refine ⟨fun z ↦ (realMellinRegularPart n (2*z)).comp B, hscaled.comp (.const B), ?_⟩
  have hnear : ∀ᶠ z : ℂ in 𝓝 c, -((n+1 : ℕ) : ℝ) < (2*z).re :=
    ((continuous_const.mul continuous_id : Continuous (fun z : ℂ ↦ 2*z)).tendsto c).eventually
      ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hn)
  filter_upwards [hnear] with z hz
  constructor
  · intro f hf
    change schwartzMellinContinuedInFirst (2*z) (B f) = _
    apply realMellinRegularPart_eq n (2*z) hz
    intro y k
    apply schwartzIsometricAverage_iteratedFDeriv_eq_zero
    intro u
    change iteratedFDeriv ℝ k f ((0 : ℝ) • (u : ℂ), y) = 0
    simpa only [zero_smul] using hf y k
  · intro f y hf k
    apply realMellinRegularPart_flat n (2*z) (B f) y _ k
    intro t i
    apply schwartzIsometricAverage_iteratedFDeriv_eq_zero
    exact fun u ↦ hf (t • (u : ℂ)) i

end

end Masullo
