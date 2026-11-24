import SchwartzCyclicMoment
import HardySobolevMellin
import Mathlib.Analysis.Analytic.Order

open MeasureTheory Set

namespace Masullo

noncomputable section

/-- The Mellin symbol for one cyclic difference in logarithmic coordinates. -/
def cyclicMellinFactor (g : ℝ × Circle) (z : ℂ) : ℂ :=
  1 - (g.2 : ℂ) * Complex.exp (-((g.1 : ℂ) * z))

/-- The product retains one factor per generator, including repetitions. -/
def cyclicMellinSymbol (gs : List (ℝ × Circle)) (z : ℂ) : ℂ :=
  (gs.map (fun g ↦ cyclicMellinFactor g z)).prod

open Classical in
/-- The number of factors vanishing at a Mellin parameter. -/
def cyclicMellinMultiplicity (gs : List (ℝ × Circle)) (z : ℂ) : ℕ :=
  gs.countP (fun g ↦ decide (cyclicMellinFactor g z = 0))

private theorem cyclicMellinFactor_analytic (g : ℝ × Circle) (z : ℂ) :
    AnalyticAt ℂ (cyclicMellinFactor g) z := by
  unfold cyclicMellinFactor
  fun_prop

private theorem cyclicMellinFactor_hasDerivAt (g : ℝ × Circle) (z : ℂ) :
    HasDerivAt (cyclicMellinFactor g)
      ((g.1 : ℂ) * ((g.2 : ℂ) * Complex.exp (-((g.1 : ℂ) * z)))) z := by
  have h := ((((hasDerivAt_id z).const_mul (g.1 : ℂ)).neg.cexp).const_mul (g.2 : ℂ)).const_sub (1 : ℂ)
  exact h.congr_deriv (by
    change -((g.2 : ℂ) * (Complex.exp (-((g.1 : ℂ) * z)) * -((g.1 : ℂ) * 1))) = _
    ring)

/-- Each positive-log-period factor has simple zeros, and the product
order counts all vanishing factors at the center. -/
theorem cyclicMellinSymbol_analytic_order (gs : List (ℝ × Circle))
    (hgs : ∀ g ∈ gs, 0 < g.1) (z : ℂ) :
    AnalyticAt ℂ (cyclicMellinSymbol gs) z ∧
      analyticOrderAt (cyclicMellinSymbol gs) z = cyclicMellinMultiplicity gs z := by
  classical
  induction gs with
  | nil =>
    refine ⟨analyticAt_const, ?_⟩
    change analyticOrderAt (fun _ : ℂ ↦ (1 : ℂ)) z = 0
    exact analyticAt_const.analyticOrderAt_eq_zero.mpr one_ne_zero
  | cons g gs ih =>
    obtain ⟨ha, ho⟩ := ih (fun f hf ↦ hgs f (List.mem_cons_of_mem _ hf))
    have hg := cyclicMellinFactor_analytic g z
    have hProd : cyclicMellinSymbol (g :: gs) =
        cyclicMellinFactor g * cyclicMellinSymbol gs := rfl
    rw [hProd]
    refine ⟨hg.mul ha, ?_⟩
    rw [analyticOrderAt_mul hg ha, ho]
    by_cases hz : cyclicMellinFactor g z = 0
    · have hg' : analyticOrderAt (cyclicMellinFactor g) z = 1 := by
        apply hg.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hz
        have he : (g.2 : ℂ) * Complex.exp (-((g.1 : ℂ) * z)) = 1 :=
          (sub_eq_zero.mp hz).symm
        rw [(cyclicMellinFactor_hasDerivAt g z).deriv, he, mul_one]
        exact Complex.ofReal_ne_zero.mpr (hgs g List.mem_cons_self).ne'
      simp [cyclicMellinMultiplicity, hz, hg', Nat.cast_add, add_comm]
    · simp [cyclicMellinMultiplicity, hz, hg.analyticOrderAt_eq_zero.mpr hz]

/-- Positive logarithmic periods and unitary phases put every Mellin
symbol zero on the imaginary axis. -/
theorem cyclicMellinMultiplicity_re_eq_zero (gs : List (ℝ × Circle))
    (hgs : ∀ g ∈ gs, 0 < g.1) (z : ℂ) (hz : 0 < cyclicMellinMultiplicity gs z) :
    z.re = 0 := by
  classical
  have h := List.countP_pos_iff.mp hz
  rcases h with ⟨g, hg, hzero⟩
  have he : cyclicMellinFactor g z = 0 := of_decide_eq_true hzero
  have hnorm : ‖(g.2 : ℂ) * Complex.exp (-((g.1 : ℂ) * z))‖ = ‖(1 : ℂ)‖ :=
    congrArg norm (sub_eq_zero.mp he).symm
  rw [norm_mul, Circle.norm_coe, one_mul, Complex.norm_exp, norm_one] at hnorm
  have hre : (-((g.1 : ℂ) * z)).re = 0 :=
    Real.exp_injective (hnorm.trans Real.exp_zero.symm)
  have hprod : g.1 * z.re = 0 := by
    simpa [Complex.mul_re] using hre
  exact (mul_eq_zero.mp hprod).resolve_left (hgs g hg).ne'

private theorem entireLogMellin_analyticAt (f : PositiveRealExponentialDecay (univ : Set ℝ))
    (z : ℂ) : AnalyticAt ℂ (entireLogMellin f).val z := by
  apply Differentiable.analyticAt
  have h := (entireLogMellin f).property.2.1
  simpa only [preimage_univ, differentiableOn_univ] using h

/-- Every Mellin jet of order below the cyclic multiplicity vanishes on
the range of the entire-decay difference product. -/
theorem logDecayCyclicDifferenceProduct_mellinJet_eq_zero
    (gs : List (ℝ × Circle)) (hgs : ∀ g ∈ gs, 0 < g.1)
    (f : PositiveRealExponentialDecay (univ : Set ℝ)) (z : ℂ) (k : ℕ)
    (hk : k < cyclicMellinMultiplicity gs z) :
    iteratedDeriv k (entireLogMellin
      (logDecayCyclicDifferenceProduct univ univ_nonempty gs f)).val z = 0 := by
  obtain ⟨ha, horder⟩ := cyclicMellinSymbol_analytic_order gs hgs z
  have hM : (entireLogMellin (logDecayCyclicDifferenceProduct univ univ_nonempty gs f)).val =
      cyclicMellinSymbol gs * (entireLogMellin f).val :=
    funext (logDecayCyclicDifferenceProduct_mellin gs f)
  rw [hM]
  have hf := entireLogMellin_analyticAt f z
  have hbound : (cyclicMellinMultiplicity gs z : ℕ∞) ≤
      analyticOrderAt (cyclicMellinSymbol gs * (entireLogMellin f).val) z := by
    rw [analyticOrderAt_mul ha hf, horder]
    exact le_self_add
  exact (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (ha.mul hf)).mp hbound k hk

/-- The scalar Mellin derivative is the logarithmic moment integral on
the full entire-decay space. -/
theorem entireLogMellin_iteratedDeriv_eq_moment
    (f : PositiveRealExponentialDecay (univ : Set ℝ)) (z : ℂ) (k : ℕ) :
    iteratedDeriv k (entireLogMellin f).val z =
      ∫ t : ℝ, Complex.exp (z * (t : ℂ)) * ((t : ℂ) ^ k * f.val t) := by
  have hM : (entireLogMellin f).val = mellin (fun t ↦ f.val (Real.log t)) := by
    funext w
    exact positiveRealFourierMellin_apply _ _ _ _ _ _ (mem_univ _)
  rw [hM, mellin_iteratedDeriv_log_moment f k, mellin_eq_log_integral]
  simp only [Real.log_exp]

private theorem cyclicMellinFactor_sample_zero (g : ℝ × Circle) (hd : 0 < g.1) (n : ℤ) :
    cyclicMellinFactor g
      ((((Complex.arg (g.2 : ℂ) / g.1 - 2 * Real.pi * ((n : ℝ) / g.1) : ℝ) : ℂ) *
        Complex.I)) = 0 := by
  let a := Complex.arg (g.2 : ℂ)
  have hc : (g.2 : ℂ) = Complex.exp ((a : ℂ) * Complex.I) := by
    simpa only [Circle.norm_coe, Complex.ofReal_one, one_mul] using
      (Complex.norm_mul_exp_arg_mul_I (g.2 : ℂ)).symm
  have he : (a : ℂ) * Complex.I - (g.1 : ℂ) *
      (((a / g.1 - 2 * Real.pi * ((n : ℝ) / g.1) : ℝ) : ℂ) * Complex.I) =
        (n : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    have hd' : (g.1 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hd.ne'
    field_simp
    ring
  unfold cyclicMellinFactor
  change 1 - (g.2 : ℂ) * Complex.exp (-((g.1 : ℂ) *
    (((a / g.1 - 2 * Real.pi * ((n : ℝ) / g.1) : ℝ) : ℂ) * Complex.I))) = 0
  rw [hc, ← Complex.exp_add, ← sub_eq_add_neg, he, Complex.exp_int_mul_two_pi_mul_I, sub_self]

private theorem logDecayCyclicDifference_mem_range_of_mellinZeros
    (g : ℝ × Circle) (hd : 0 < g.1) (f : PositiveRealExponentialDecay (univ : Set ℝ))
    (hf : ∀ z, cyclicMellinFactor g z = 0 → (entireLogMellin f).val z = 0) :
    f ∈ (logDecayCyclicDifferenceProduct univ univ_nonempty [g]).range := by
  rw [logDecayCyclicDifferenceProduct_range_eq_comap univ (mem_univ 0) [g] (by
    intro x hx; rw [List.mem_singleton.mp hx]; exact hd)]
  letI : Fact (0 < g.1) := ⟨hd⟩
  change positiveRealExponentialDecay_zeroInclusion univ (mem_univ 0) f ∈
    (schwartzCyclicDifference g).range
  apply schwartzCyclicDifference_mem_range_of_samples_zero g.1 g.2
  intro n
  let z := (((Complex.arg (g.2 : ℂ) / g.1 - 2 * Real.pi * ((n : ℝ) / g.1) : ℝ) : ℂ) *
    Complex.I)
  have h := entireLogMellin_iteratedDeriv_eq_moment f z 0
  simp only [iteratedDeriv_zero, pow_zero, one_mul] at h
  rw [← hf z (cyclicMellinFactor_sample_zero g hd n)]
  simpa only [positiveRealExponentialDecay_zeroInclusion_apply, z] using h.symm

/-- The common Mellin jet kernel is exactly the finite cyclic difference
range on scalar entire-decay profiles. The proof divides one factor at
a time and retains the multiplicity of every remaining zero. -/
theorem logDecayCyclicDifferenceProduct_mem_range_iff_mellinJets
    (gs : List (ℝ × Circle)) (hgs : ∀ g ∈ gs, 0 < g.1)
    (f : PositiveRealExponentialDecay (univ : Set ℝ)) :
    f ∈ (logDecayCyclicDifferenceProduct univ univ_nonempty gs).range ↔
      ∀ z k, k < cyclicMellinMultiplicity gs z → iteratedDeriv k (entireLogMellin f).val z = 0 := by
  classical
  constructor
  · rintro ⟨u, rfl⟩ z k hk
    exact logDecayCyclicDifferenceProduct_mellinJet_eq_zero gs hgs u z k hk
  · intro hf
    induction gs generalizing f with
    | nil => exact ⟨f, rfl⟩
    | cons g gs ih =>
      have hd : 0 < g.1 := hgs g List.mem_cons_self
      have htail (x : ℝ × Circle) (hx : x ∈ gs) : 0 < x.1 :=
        hgs x (List.mem_cons_of_mem g hx)
      have hhead (x : ℝ × Circle) (hx : x ∈ [g]) : 0 < x.1 :=
        (List.mem_singleton.mp hx).symm ▸ hd
      have hcount (z : ℂ) : cyclicMellinMultiplicity (g :: gs) z =
          cyclicMellinMultiplicity [g] z + cyclicMellinMultiplicity gs z := by
        by_cases hz : cyclicMellinFactor g z = 0
        all_goals simp [cyclicMellinMultiplicity, hz, add_comm]
      have hzero (z : ℂ) (hz : cyclicMellinFactor g z = 0) : (entireLogMellin f).val z = 0 := by
        have hz' : 0 < cyclicMellinMultiplicity (g :: gs) z := by
          simp [cyclicMellinMultiplicity, hz]
        simpa only [iteratedDeriv_zero] using hf z 0 hz'
      obtain ⟨u, hu⟩ := logDecayCyclicDifference_mem_range_of_mellinZeros g hd f hzero
      have hsymbol : cyclicMellinSymbol [g] = cyclicMellinFactor g :=
        funext fun z ↦ by simp [cyclicMellinSymbol]
      have hF : (entireLogMellin f).val = cyclicMellinFactor g * (entireLogMellin u).val := by
        rw [← hu, ← hsymbol]
        exact funext (logDecayCyclicDifferenceProduct_mellin [g] u)
      have huJets (z : ℂ) (k : ℕ) (hk : k < cyclicMellinMultiplicity gs z) :
          iteratedDeriv k (entireLogMellin u).val z = 0 := by
        have hbound : (cyclicMellinMultiplicity (g :: gs) z : ℕ∞) ≤
            analyticOrderAt (entireLogMellin f).val z :=
          (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (entireLogMellin_analyticAt f z)).2 (hf z)
        have horder : analyticOrderAt (cyclicMellinFactor g) z =
            cyclicMellinMultiplicity [g] z :=
          hsymbol ▸ (cyclicMellinSymbol_analytic_order [g] hhead z).2
        rw [hcount, Nat.cast_add, hF, analyticOrderAt_mul
          (cyclicMellinFactor_analytic g z) (entireLogMellin_analyticAt u z), horder] at hbound
        have htailBound : (cyclicMellinMultiplicity gs z : ℕ∞) ≤
            analyticOrderAt (entireLogMellin u).val z :=
          (ENat.add_le_add_iff_left (ENat.natCast_ne_top (cyclicMellinMultiplicity [g] z))).1 hbound
        exact (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero
          (entireLogMellin_analyticAt u z)).1 htailBound k hk
      obtain ⟨v, hv⟩ := ih htail u huJets
      refine ⟨v, ?_⟩
      change logDecayCyclicDifferenceProduct univ univ_nonempty [g]
        (logDecayCyclicDifferenceProduct univ univ_nonempty gs v) = f
      exact (congrArg (logDecayCyclicDifferenceProduct univ univ_nonempty [g]) hv).trans hu

/-- The Mellin moment below the cyclic multiplicity is a continuous
functional on the actual entire-decay product quotient. -/
theorem exists_cyclicMellinMoment_quotient
    (gs : List (ℝ × Circle)) (hgs : ∀ g ∈ gs, 0 < g.1)
    (z : ℂ) (k : ℕ) (hk : k < cyclicMellinMultiplicity gs z) :
    let E := PositiveRealExponentialDecay (univ : Set ℝ)
    let P := (logDecayCyclicDifferenceProduct univ univ_nonempty gs).range
    ∃ L : (E ⧸ P) →L[ℂ] ℂ, ∀ f : E,
      L (P.mkQ f) = ∫ t : ℝ, Complex.exp (z * (t : ℂ)) * ((t : ℂ) ^ k * f.val t) := by
  dsimp only
  let E := PositiveRealExponentialDecay (univ : Set ℝ)
  let P := (logDecayCyclicDifferenceProduct univ univ_nonempty gs).range
  obtain ⟨J, hJ⟩ := exists_schwartzBergman_jetEvaluation isOpen_univ ordConnected_univ
    z (mem_univ z.re) k
  let M : E →L[ℂ] ℂ := J.comp entireLogMellin.toContinuousLinearMap
  have hP : P ≤ M.ker := by
    rintro _ ⟨f, rfl⟩
    change J (entireLogMellin (logDecayCyclicDifferenceProduct univ univ_nonempty gs f)) = 0
    exact (hJ _).trans (logDecayCyclicDifferenceProduct_mellinJet_eq_zero gs hgs f z k hk)
  refine ⟨P.liftQL M hP, fun f ↦ ?_⟩
  change J (entireLogMellin f) = _
  exact (hJ _).trans (entireLogMellin_iteratedDeriv_eq_moment f z k)

private theorem entireLogMellin_deriv_bound
    (f : PositiveRealExponentialDecay (univ : Set ℝ)) (k N : ℕ) :
    ∃ C : ℝ, ∀ y : ℝ, |y| ^ N *
      ‖iteratedDeriv k (entireLogMellin f).val ((y : ℂ) * Complex.I)‖ ≤ C := by
  let S := (entireLogMellin f).val
  have hdiff : DifferentiableOn ℂ S (Complex.re ⁻¹' Ioo (-2 : ℝ) 2) :=
    (entireLogMellin f).property.2.1.mono (by simp)
  have hB (a b : ℝ) (_ : -2 < a) (hab : a < b) (_ : b < 2) :
      BddAbove ((fun z : ℂ ↦ ‖z ^ N * S z‖) '' (Complex.re ⁻¹' Ioo a b)) :=
    ((entireLogMellin f).property.2.2 a b hab.le (subset_univ _) N).mono
      (image_mono (preimage_mono Ioo_subset_Icc_self))
  obtain ⟨C, hC⟩ := verticalStrip_weighted_iteratedDeriv_bounded (-2) 2 (by norm_num) S hdiff
    N hB k (-1) 1 (by norm_num) (by norm_num) (by norm_num)
  refine ⟨C, fun y ↦ ?_⟩
  let z := (y : ℂ) * Complex.I
  have hz : z ∈ Complex.re ⁻¹' Ioo (-1 : ℝ) 1 := by
    change (z.re ∈ Ioo (-1 : ℝ) 1)
    norm_num [z, Complex.mul_re]
  have he : ‖z‖ = |y| := by simp [z, Real.norm_eq_abs]
  have h : ‖z ^ N * iteratedDeriv k S z‖ ≤ C := hC ⟨z, hz, rfl⟩
  rw [norm_mul, norm_pow, he] at h
  exact h

/-- Mellin jets sampled on an affine lattice of nonzero spacing have
rapid decay in their integer index, at every fixed derivative order. -/
theorem entireLogMellin_sampledJets_rapid
    (f : PositiveRealExponentialDecay (univ : Set ℝ)) (a d : ℝ) (hd : d ≠ 0)
    (k N : ℕ) :
    ∃ C : ℝ, ∀ n : ℤ, |(n : ℝ)| ^ N *
      ‖iteratedDeriv k (entireLogMellin f).val
        (((a + d * (n : ℝ) : ℝ) : ℂ) * Complex.I)‖ ≤ C := by
  obtain ⟨B, hB⟩ := entireLogMellin_deriv_bound f k N
  obtain ⟨A, hA⟩ := entireLogMellin_deriv_bound f k 0
  let D := (1 + |a|) / |d|
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨D ^ N * max A B, fun n ↦ ?_⟩
  let y := a + d * (n : ℝ)
  have hdn : |d| * |(n : ℝ)| ≤ |y| + |a| := by
    rw [← abs_mul, show d * (n : ℝ) = y + -a by dsimp [y]; ring]
    simpa only [abs_neg] using abs_add_le y (-a)
  have hn : |(n : ℝ)| ≤ D * max 1 |y| := by
    rw [show D * max 1 |y| = ((1 + |a|) * max 1 |y|) / |d| by
      dsimp [D]
      ring]
    apply (le_div_iff₀ (abs_pos.mpr hd)).2
    calc
      |(n : ℝ)| * |d| ≤ |y| + |a| := by simpa only [mul_comm] using hdn
      _ ≤ (1 + |a|) * max 1 |y| := by
        rw [add_mul, one_mul]
        exact add_le_add (le_max_right _ _) (le_mul_of_one_le_right (abs_nonneg _) (le_max_left _ _))
  let v := ‖iteratedDeriv k (entireLogMellin f).val ((y : ℂ) * Complex.I)‖
  have hv : (max 1 |y|) ^ N * v ≤ max A B := by
    by_cases hy : 1 ≤ |y|
    · rw [max_eq_right hy]
      exact (hB y).trans (le_max_right _ _)
    · rw [max_eq_left (le_of_not_ge hy), one_pow, one_mul]
      exact ((by simpa only [pow_zero, one_mul] using hA y) : v ≤ A).trans (le_max_left _ _)
  change |(n : ℝ)| ^ N * v ≤ _
  calc
    _ ≤ (D * max 1 |y|) ^ N * v :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) hn _) (norm_nonneg _)
    _ = D ^ N * ((max 1 |y|) ^ N * v) := by rw [mul_pow, mul_assoc]
    _ ≤ _ := mul_le_mul_of_nonneg_left hv (pow_nonneg hD _)

end

end Masullo
