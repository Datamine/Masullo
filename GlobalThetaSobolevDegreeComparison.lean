import GlobalThetaSobolev
import WeightedTranslations

open Filter Function MeasureTheory NumberField Set Topology
open scoped ENNReal NumberField InnerProductSpace

namespace Masullo
noncomputable section

section Multipliers

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {r : X → ℝ}

/-- A bounded positive measurable multiplier on complex L² has dense range. -/
theorem denseRange_lpTwoPositiveMultiplier (hr : Measurable r) (hpos : ∀ x, 0 < r x)
    (hbound : ∀ x, |r x| ≤ 1) : DenseRange (lpTwoRealMultiplier (μ := μ) hr hbound) := by
  let M := lpTwoRealMultiplier (μ := μ) hr hbound
  let S := M.toLinearMap.range.topologicalClosure
  letI : CompleteSpace S := (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  have hSym : M.toLinearMap.IsSymmetric := by
    intro u v
    change inner ℂ (M u) v = inner ℂ u (M v)
    rw [L2.inner_def, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [lpTwoRealMultiplier_ae hr hbound u, lpTwoRealMultiplier_ae hr hbound v] with x hu hv
    rw [hu, hv, RCLike.inner_apply, RCLike.inner_apply, starRingEnd_apply, starRingEnd_apply]
    simp only [star_mul', Complex.star_def, Complex.conj_ofReal]
    ring
  have hS : S = ⊤ := by
    apply (Submodule.orthogonal_eq_bot_iff (K := S)).mp
    apply (Submodule.eq_bot_iff Sᗮ).mpr
    intro u hu
    have hz : inner ℂ (M (M u)) u = 0 :=
      (S.mem_orthogonal u).mp hu (M (M u)) (Submodule.le_topologicalClosure _ ⟨M u, rfl⟩)
    have hMu : M u = 0 :=
      inner_self_eq_zero.mp ((hSym (M u) u).symm.trans hz)
    apply Lp.ext
    filter_upwards [lpTwoRealMultiplier_ae hr hbound u, Lp.coeFn_zero ℂ 2 μ] with x hx hzero
    change M u x = (r x : ℂ) * u x at hx
    rw [hMu, hzero] at hx
    exact ((mul_eq_zero.mp hx.symm).resolve_left (Complex.ofReal_ne_zero.mpr (hpos x).ne')).trans hzero.symm
  intro u
  change u ∈ (S : Set (Lp ℂ 2 μ))
  rw [hS]
  exact Submodule.mem_top

end Multipliers

variable (F : Type*) [Field F] [NumberField F]
private abbrev Q := IdeleClass F
private abbrev t (q : Q F) := (ideleClassLogNorm F q).toAdd

local instance degreeComparisonMeasurable : MeasurableSpace (Q F) := borel _
local instance degreeComparisonBorel : BorelSpace (Q F) := ⟨rfl⟩

variable (μ : Measure (Q F)) [μ.IsHaarMeasure]

private abbrev amp (s x : ℝ) := hardySobolevAmplitude 0 0 s x

private theorem amp_squared (s x : ℝ) : amp s x ^ 2 = (1 + x^2) ^ (s/2) := by
  simp only [amp, hardySobolevAmplitude, hardySobolevWeight, mul_zero, zero_mul, Real.exp_zero,
    max_self, one_mul]
  exact Real.sq_sqrt (Real.rpow_nonneg (by positivity) _)

private theorem amp_positive (s x : ℝ) : 0 < amp s x := by
  change 0 < Real.sqrt (hardySobolevWeight 0 0 s x)
  apply Real.sqrt_pos.mpr
  simp only [hardySobolevWeight, mul_zero, zero_mul, Real.exp_zero, max_self, one_mul]
  exact Real.rpow_pos_of_pos (by positivity) _

private theorem amp_le_of_le (s u : ℝ) (h : s ≤ u) (x : ℝ) : amp s x ≤ amp u x := by
  have hpow : amp s x ^ 2 ≤ amp u x ^ 2 := by
    rw [amp_squared, amp_squared]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith [sq_nonneg x]) (by linarith)
  nlinarith [amp_positive s x, amp_positive u x]

private abbrev ratio (s u : ℝ) (q : Q F) := amp s (t F q) / amp u (t F q)

private theorem ratio_measurable (s u : ℝ) : Measurable (ratio F s u) := by
  have hl : Continuous (t F) := ideleClassLogNorm_continuous F
  have hA (v : ℝ) : Continuous (amp v) :=
    (continuous_hardySobolevWeight 0 0 v).sqrt
  exact ((hA s).measurable.comp hl.measurable).div ((hA u).measurable.comp hl.measurable)

private theorem ratio_pos (s u : ℝ) (q : Q F) : 0 < ratio F s u q :=
  div_pos (amp_positive _ _) (amp_positive _ _)

private theorem ratio_le_one (s u : ℝ) (h : s ≤ u) (q : Q F) : |ratio F s u q| ≤ 1 := by
  rw [abs_of_pos (ratio_pos F s u q)]
  exact (div_le_one (amp_positive _ _)).2 (amp_le_of_le s u h _)

/-- The change from the stronger zero-line Sobolev norm to the weaker one
is a contraction in amplitude coordinates, with dense ambient range. -/
def globalThetaSobolevDegreeComparison (s u : ℝ) (h : s ≤ u) :
    Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  lpTwoRealMultiplier (ratio_measurable F s u) (ratio_le_one F s u h)

omit [μ.IsHaarMeasure] in
theorem globalThetaSobolevDegreeComparison_norm_le (s u : ℝ) (h : s ≤ u) :
    ‖globalThetaSobolevDegreeComparison F μ s u h‖ ≤ 1 :=
  lpTwoRealMultiplier_norm_le _ _ zero_le_one

omit [μ.IsHaarMeasure] in
theorem globalThetaSobolevDegreeComparison_dense (s u : ℝ) (h : s ≤ u) :
    DenseRange (globalThetaSobolevDegreeComparison F μ s u h) :=
  denseRange_lpTwoPositiveMultiplier (ratio_measurable F s u) (ratio_pos F s u) (ratio_le_one F s u h)

theorem globalThetaSobolevDegreeComparison_map (s u : ℝ) (hs : 0 ≤ s) (hu : 0 ≤ u) (h : s ≤ u)
    (f : GlobalPolarTheta F) :
    globalThetaSobolevDegreeComparison F μ s u h (globalThetaSobolevMap F μ 0 0 0 u hu f) =
      globalThetaSobolevMap F μ 0 0 0 s hs f := by
  let fs := globalThetaSobolevMap F μ 0 0 0 s hs f
  let fu := globalThetaSobolevMap F μ 0 0 0 u hu f
  have hes := globalThetaSobolevMap_ae F μ 0 0 0 s hs f
  have heu := globalThetaSobolevMap_ae F μ 0 0 0 u hu f
  change (fs : Q F → ℂ) =ᵐ[μ] fun q =>
    (amp s (t F q) * Real.exp (0 * t F q)) • globalPolarThetaFunction F f q at hes
  change (fu : Q F → ℂ) =ᵐ[μ] fun q =>
    (amp u (t F q) * Real.exp (0 * t F q)) • globalPolarThetaFunction F f q at heu
  simp only [zero_mul, Real.exp_zero, mul_one] at hes heu
  apply Lp.ext
  filter_upwards [lpTwoRealMultiplier_ae (ratio_measurable F s u) (ratio_le_one F s u h) fu,
    hes, heu] with q hq hqs hqu
  change globalThetaSobolevDegreeComparison F μ s u h fu q = (ratio F s u q : ℂ) * fu q at hq
  change globalThetaSobolevDegreeComparison F μ s u h fu q = fs q
  rw [hq, hqs, hqu, Complex.real_smul, Complex.real_smul]
  change ((amp s (t F q) / amp u (t F q) : ℝ) : ℂ) *
    ((amp u (t F q) : ℂ) * globalPolarThetaFunction F f q) =
    (amp s (t F q) : ℂ) * globalPolarThetaFunction F f q
  rw [← mul_assoc, ← Complex.ofReal_mul, div_mul_cancel₀ _ (amp_positive _ _).ne']

/-- Ambient density at a Sobolev degree transfers to every weaker degree. -/
theorem globalThetaSobolevMap_dense_of_degree_ge (s u : ℝ) (hs : 0 ≤ s) (hu : 0 ≤ u) (h : s ≤ u)
    (hd : DenseRange (globalThetaSobolevMap F μ 0 0 0 u hu)) :
    DenseRange (globalThetaSobolevMap F μ 0 0 0 s hs) := by
  have hD := (globalThetaSobolevDegreeComparison_dense F μ s u h).comp hd
    (globalThetaSobolevDegreeComparison F μ s u h).continuous
  have he : (globalThetaSobolevDegreeComparison F μ s u h :
      Lp ℂ 2 μ → Lp ℂ 2 μ) ∘ (globalThetaSobolevMap F μ 0 0 0 u hu) =
      (globalThetaSobolevMap F μ 0 0 0 s hs : GlobalPolarTheta F → Lp ℂ 2 μ) :=
    funext (globalThetaSobolevDegreeComparison_map F μ s u hs hu h)
  exact he ▸ hD

/-- The density assertion at degrees above one would imply density at
every nonnegative degree, including the endpoints of the source claim. -/
theorem globalThetaSobolevMap_dense_of_all_high_degrees
    (h : ∀ (s : ℝ) (hs : 1 < s), DenseRange
      (globalThetaSobolevMap F μ 0 0 0 s (zero_lt_one.trans hs).le))
    (s : ℝ) (hs : 0 ≤ s) : DenseRange (globalThetaSobolevMap F μ 0 0 0 s hs) := by
  have ht : 1 < s + 2 := by linarith
  exact globalThetaSobolevMap_dense_of_degree_ge F μ s (s + 2) hs
    (zero_lt_one.trans ht).le (by linarith) (h (s + 2) ht)

end
end Masullo
