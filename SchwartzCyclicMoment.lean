import ArchimedeanRadialMoments
import SchwartzCyclicPeriodization
import BergmanDifference

open Filter Function MeasureTheory Set Topology
open scoped ContDiff SchwartzMap

namespace Masullo

noncomputable section

private abbrev E := PositiveRealExponentialDecay (univ : Set ℝ)
private abbrev U : Set ℝ := univ
private theorem hU : U.Nonempty := univ_nonempty

private local instance : ContinuousSMul ℂ E :=
  (PolynormableSpace.withSeminorms ℂ E).continuousSMul

/-- The exponential moment is continuous in the weighted Schwartz topology. -/
def logProfileExponentialMomentCLM : E →L[ℂ] ℂ := by
  let one : U := ⟨1, mem_univ _⟩
  let A : E →L[ℂ] 𝓢(ℝ, ℂ) :=
    ⟨logExponentialDecayTwist U one,
      (continuous_apply one).comp (positiveRealExponentialDecay_isEmbedding U hU).continuous⟩
  exact (SchwartzMap.integralCLM ℂ volume).comp A

@[simp] theorem logProfileExponentialMomentCLM_apply (f : E) :
    logProfileExponentialMomentCLM f = logProfileExponentialMoment f.val := by
  change (∫ t, logExponentialDecayTwist U ⟨1, mem_univ _⟩ f t) = _
  unfold logProfileExponentialMoment
  apply integral_congr_ae (.of_forall fun x ↦ ?_)
  simpa only [Subtype.coe_mk, one_mul] using
    logExponentialDecayTwist_apply U ⟨1, mem_univ _⟩ f x

private theorem logProfileExponentialMoment_mellin_one (f : E) :
    (positiveRealFourierMellin U isOpen_univ ordConnected_univ hU f).val 1 =
      logProfileExponentialMoment f.val := by
  rw [positiveRealFourierMellin_apply _ _ _ _ _ _ (mem_univ _), mellin_eq_log_integral]
  simp only [logProfileExponentialMoment, Real.log_exp, one_mul, Complex.ofReal_exp]

/-- The full Mellin multiplier of a product of positive cyclic differences,
with multiplicities retained in the list of generators. -/
theorem logDecayCyclicDifferenceProduct_mellin (gs : List (ℝ × Circle)) (f : E) (z : ℂ) :
    (entireLogMellin (logDecayCyclicDifferenceProduct U hU gs f)).val z =
      (gs.map (fun g ↦ 1 - (g.2 : ℂ) * Complex.exp (-((g.1 : ℂ) * z)))).prod *
        (entireLogMellin f).val z := by
  induction gs with
  | nil => exact (one_mul _).symm
  | cons g gs ih =>
    let u := logDecayCyclicDifferenceProduct U hU gs f
    change (entireLogMellin (u - (g.2 : ℂ) • exponentialSchwartzTranslation g.1 u)).val z = _
    rw [map_sub, map_smul]
    change (entireLogMellin u).val z -
        (g.2 : ℂ) * (entireLogMellin (exponentialSchwartzTranslation g.1 u)).val z = _
    rw [entireMellin_translation]
    change (entireLogMellin u).val z -
      (g.2 : ℂ) * (Complex.exp (-((g.1 : ℂ) * z)) * (entireLogMellin u).val z) = _
    rw [show (entireLogMellin u).val z = _ from ih, List.map_cons, List.prod_cons]
    ring

/-- A continuous choice of compact representatives preserves the entire
Mellin transform modulo the cyclic multiplier. -/
theorem exists_logDecayCyclicDifferenceProduct_compactMellinRepresentative
    (gs : List (ℝ × Circle)) (hgs : ∀ g ∈ gs, 0 < g.1) :
    ∃ A : E →L[ℂ] E,
      (∀ f, support (A f).val ⊆ Icc (-(gs.map Prod.fst).sum) (gs.map Prod.fst).sum) ∧
      ∀ f, ∃ g : E, ∀ z : ℂ,
        (entireLogMellin f).val z - (entireLogMellin (A f)).val z =
          (gs.map (fun k ↦ 1 - (k.2 : ℂ) * Complex.exp (-((k.1 : ℂ) * z)))).prod *
            (entireLogMellin g).val z := by
  let J := positiveRealExponentialDecay_zeroInclusion U (mem_univ 0)
  obtain ⟨A, hA, hSupp⟩ :=
    schwartzCyclicDifferenceProduct_weighted_representatives U (mem_univ 0) gs hgs
  refine ⟨A.comp J, fun f ↦ hSupp (J f), fun f ↦ ?_⟩
  have hmem : f - A (J f) ∈ (logDecayCyclicDifferenceProduct U hU gs).range := by
    rw [logDecayCyclicDifferenceProduct_range_eq_comap U (mem_univ 0) gs hgs]
    change J (f - A (J f)) ∈ (schwartzCyclicDifferenceProduct gs).range
    rw [map_sub]
    exact hA (J f)
  obtain ⟨g, hg⟩ := hmem
  refine ⟨g, fun z ↦ ?_⟩
  have he := logDecayCyclicDifferenceProduct_mellin gs g z
  change logDecayCyclicDifferenceProduct U hU gs g = f - A (J f) at hg
  rw [hg, map_sub] at he
  exact he

private theorem logProfileExponentialMoment_difference (g : ℝ × Circle) (f : E) :
    logProfileExponentialMomentCLM (logDecayCyclicDifference U hU g f) =
      (1 - (g.2 : ℂ) * Real.exp (-g.1)) * logProfileExponentialMomentCLM f := by
  let M := logProfileExponentialMomentCLM
  change M (f - (g.2 : ℂ) • exponentialSchwartzTranslation g.1 f) = _
  have he := entireMellin_translation g.1 f 1
  change (positiveRealFourierMellin U isOpen_univ ordConnected_univ hU
    (exponentialSchwartzTranslation g.1 f)).val 1 =
      Complex.exp (-((g.1 : ℂ) * 1)) *
        (positiveRealFourierMellin U isOpen_univ ordConnected_univ hU f).val 1 at he
  simp only [logProfileExponentialMoment_mellin_one, mul_one, ← Complex.ofReal_neg,
    ← Complex.ofReal_exp] at he
  rw [map_sub, map_smul, smul_eq_mul]
  change M f - (g.2 : ℂ) * M (exponentialSchwartzTranslation g.1 f) = _
  rw [show M (exponentialSchwartzTranslation g.1 f) = (Real.exp (-g.1) : ℂ) * M f by
    simpa only [M, logProfileExponentialMomentCLM_apply] using he]
  ring

private theorem logProfileExponentialMoment_product_ne_zero (gs : List (ℝ × Circle))
    (hg : ∀ g ∈ gs, 0 < g.1) (f : E) (hf : logProfileExponentialMomentCLM f ≠ 0) :
    logProfileExponentialMomentCLM (logDecayCyclicDifferenceProduct U hU gs f) ≠ 0 := by
  induction gs with
  | nil => exact hf
  | cons g gs ih =>
    change logProfileExponentialMomentCLM (logDecayCyclicDifference U hU g
      (logDecayCyclicDifferenceProduct U hU gs f)) ≠ 0
    rw [logProfileExponentialMoment_difference]
    refine mul_ne_zero ?_ (ih (fun k hk ↦ hg k (List.mem_cons_of_mem _ hk)))
    intro h
    have hn := congrArg norm (sub_eq_zero.mp h)
    rw [norm_one, norm_mul, Circle.norm_coe, one_mul, Complex.norm_of_nonneg
      (Real.exp_pos _).le] at hn
    exact (Real.exp_lt_one_iff.mpr (neg_neg_of_pos (hg g List.mem_cons_self))).ne hn.symm

private theorem logDecayCyclicDifferenceProduct_compactSupport (gs : List (ℝ × Circle))
    (f : E) (hf : HasCompactSupport f.val) :
    HasCompactSupport (logDecayCyclicDifferenceProduct U hU gs f).val := by
  induction gs with
  | nil => exact hf
  | cons g gs ih =>
    let h := logDecayCyclicDifferenceProduct U hU gs f
    change HasCompactSupport (logDecayCyclicDifference U hU g h).val
    have hc : HasCompactSupport (fun x ↦ h.val (x + g.1)) :=
      ih.comp_homeomorph (Homeomorph.addRight g.1)
    change HasCompactSupport (fun x ↦ h.val x - (g.2 : ℂ) * h.val (x + g.1))
    exact ih.sub hc.mul_left

/-- A fixed compact-support section of the scalar cyclic quotient can be
chosen in the zero kernel of the Mellin value at one. -/
theorem schwartzCyclicDifferenceProduct_zeroMoment_representatives (gs : List (ℝ × Circle))
    (hg : ∀ g ∈ gs, 0 < g.1) :
    ∃ (a b : ℝ) (S : 𝓢(ℝ, ℂ) →L[ℂ] E),
      (∀ f, f - positiveRealExponentialDecay_zeroInclusion U (mem_univ 0) (S f) ∈
        (schwartzCyclicDifferenceProduct gs).range) ∧
      (∀ f, support (S f).val ⊆ Icc a b) ∧
      ∀ f, logProfileExponentialMoment (S f).val = 0 := by
  let M := logProfileExponentialMomentCLM
  let J := positiveRealExponentialDecay_zeroInclusion U (mem_univ 0)
  let D := logDecayCyclicDifferenceProduct U hU gs
  obtain ⟨S₀, hS₀, hSupp₀⟩ :=
    schwartzCyclicDifferenceProduct_weighted_representatives U (mem_univ 0) gs hg
  let bump : ContDiffBump (0 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩
  let u (t : ℝ) : ℂ := (bump t : ℝ)
  have hKu : HasCompactSupport u := bump.hasCompactSupport.comp_left Complex.ofReal_zero
  let f₀ : E := ⟨u, mem_logExponentialDecaySubmodule_of_hasCompactSupport U hKu
    (Complex.ofRealCLM.contDiff.comp bump.contDiff)⟩
  have hu : M f₀ ≠ 0 := by
    rw [show M = logProfileExponentialMomentCLM from rfl, logProfileExponentialMomentCLM_apply]
    change (∫ t : ℝ, (Real.exp t : ℂ) * (bump t : ℝ)) ≠ 0
    simp_rw [← Complex.ofReal_mul, integral_complex_ofReal, ne_eq, Complex.ofReal_eq_zero]
    apply ne_of_gt
    have hc : Continuous (fun t : ℝ ↦ Real.exp t * bump t) :=
      Real.continuous_exp.mul bump.continuous
    have hi : Integrable (fun t : ℝ ↦ Real.exp t * bump t) :=
      hc.integrable_of_hasCompactSupport bump.hasCompactSupport.mul_left
    refine (integral_pos_iff_support_of_nonneg (fun t ↦ mul_nonneg (Real.exp_pos t).le
      (bump.nonneg)) hi).mpr (hc.isOpen_support.measure_pos volume ⟨0, ?_⟩)
    change Real.exp 0 * bump 0 ≠ 0
    rw [bump.one_of_mem_closedBall (Metric.mem_closedBall_self bump.rIn_pos.le), Real.exp_zero]
    norm_num
  let v := (M (D f₀))⁻¹ • D f₀
  have hv : M v = 1 := by
    change M ((M (D f₀))⁻¹ • D f₀) = 1
    rw [map_smul, smul_eq_mul, inv_mul_cancel₀
      (logProfileExponentialMoment_product_ne_zero gs hg f₀ hu)]
  have hvK : HasCompactSupport v.val := by
    change HasCompactSupport ((fun _ : ℝ ↦ (M (D f₀))⁻¹) * (D f₀).val)
    exact (logDecayCyclicDifferenceProduct_compactSupport gs f₀ hKu).mul_left
  let K := Icc (-(gs.map Prod.fst).sum) (gs.map Prod.fst).sum ∪ tsupport v.val
  have hK : IsCompact K := isCompact_Icc.union hvK.isCompact
  obtain ⟨a, ha⟩ := hK.bddBelow
  obtain ⟨b, hb⟩ := hK.bddAbove
  let R : ℂ →L[ℂ] E := (ContinuousLinearMap.id ℂ ℂ).smulRight v
  let S := S₀ - R.comp (M.comp S₀)
  refine ⟨a, b, S, ?_, ?_, ?_⟩
  · intro f
    have hR : J v ∈ (schwartzCyclicDifferenceProduct gs).range := by
      change J ((M (D f₀))⁻¹ • D f₀) ∈ _
      rw [map_smul, zeroInclusion_intertwines_cyclicDifferenceProduct]
      exact Submodule.smul_mem _ _ ⟨J f₀, rfl⟩
    change f - J (S₀ f - M (S₀ f) • v) ∈ _
    rw [map_sub, map_smul, show f - (J (S₀ f) - M (S₀ f) • J v) =
      (f - J (S₀ f)) + M (S₀ f) • J v by abel]
    exact Submodule.add_mem _ (hS₀ f) (Submodule.smul_mem _ _ hR)
  · intro f x hx
    have hxK : x ∈ K := by
      by_contra hn
      have h₁ := notMem_support.mp fun h ↦ hn (Or.inl (hSupp₀ f h))
      have h₂ := notMem_support.mp fun h ↦ hn (Or.inr (subset_closure h))
      apply hx
      change (S₀ f).val x - M (S₀ f) * v.val x = 0
      rw [h₁, h₂, mul_zero, sub_zero]
    exact ⟨ha hxK, hb hxK⟩
  · intro f
    rw [← logProfileExponentialMomentCLM_apply]
    change M (S₀ f - M (S₀ f) • v) = 0
    rw [map_sub, map_smul, hv, smul_eq_mul, mul_one, sub_self]

end

end Masullo
