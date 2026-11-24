import FiniteLocalZeta
import Mathlib.NumberTheory.Padics.ProperSpace

open Function IsDedekindDomain NumberField Set Topology
open scoped Classical NumberField

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]
variable (v : HeightOneSpectrum (𝓞 F))

private abbrev K := v.adicCompletion F

private theorem residueNorm_gt_one : 1 < (v.asIdeal.absNorm : ℝ) := by
  exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v

theorem finitePlace_properSpace : ProperSpace (K F v) := by
  let π := (chosenFiniteUniformizer F v).val
  letI : LocallyCompactSpace (K F v) := finitePlace_locallyCompact F v
  letI : NontriviallyNormedField (K F v) := ⟨⟨π⁻¹, by
    rw [norm_inv, norm_finiteUniformizer F v _ (chosenFiniteUniformizer_spec F v), inv_inv]
    exact residueNorm_gt_one F v⟩⟩
  exact .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace _

/-- The indicator of the integer ring dilated by a uniformizer power. -/
def finiteValuationBallTest (n : ℤ) : locallyConstantTests (K F v) := by
  let r := (v.asIdeal.absNorm : ℝ) ^ (-n)
  have hr : 0 < r := zpow_pos (zero_lt_one.trans (residueNorm_gt_one F v)) _
  letI := finitePlace_properSpace F v
  exact compactOpenIndicator (K F v) ⟨Metric.closedBall 0 r, isCompact_closedBall _ _,
    IsUltrametricDist.isOpen_closedBall _ hr.ne'⟩

theorem finiteValuationBallTest_apply (n : ℤ) (x : K F v) :
    (finiteValuationBallTest F v n).val x =
      if ‖x‖ ≤ (v.asIdeal.absNorm : ℝ) ^ (-n) then 1 else 0 := by
  change (if x ∈ Metric.closedBall 0 ((v.asIdeal.absNorm : ℝ) ^ (-n)) then (1 : ℂ) else 0) = _
  simp only [Metric.mem_closedBall, dist_zero_right]

theorem finiteValuationBallTest_apply_uniformizer (n : ℤ) (x : K F v) :
    (finiteValuationBallTest F v n).val x =
      if ((chosenFiniteUniformizer F v ^ n : (K F v)ˣ)⁻¹).val * x ∈
        v.adicCompletionIntegers F then 1 else 0 := by
  rw [finiteValuationBallTest_apply]
  have hq : (1 : NNReal) < v.asIdeal.absNorm := by
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hpos : (0 : ℝ) < (v.asIdeal.absNorm : ℝ) ^ (-n) :=
    zpow_pos (zero_lt_one.trans (residueNorm_gt_one F v)) _
  have hunit (y : K F v) : y ∈ v.adicCompletionIntegers F ↔ ‖y‖ ≤ 1 := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, FinitePlace.norm_def]
    exact (WithZeroMulInt.toNNReal_le_one_iff hq).symm
  simp only [hunit, Units.val_zpow_eq_zpow_val, norm_mul,
    norm_zpow, norm_finiteUniformizer F v _ (chosenFiniteUniformizer_spec F v),
    inv_zpow, ← zpow_neg]
  rw [zpow_neg (v.asIdeal.absNorm : ℝ) (-n)]
  exact if_congr ((inv_mul_le_iff₀ hpos).trans (by rw [mul_one])).symm rfl rfl

theorem finiteValuationBallTest_apply_shell (i n : ℤ) (x : (K F v)ˣ)
    (hx : x ∈ finiteZetaShell F v n) :
    (finiteValuationBallTest F v i).val x.val = if i ≤ n then 1 else 0 := by
  rw [finiteValuationBallTest_apply]
  change ‖x.val‖ = (v.asIdeal.absNorm : ℝ) ^ (-n) at hx
  rw [hx]
  exact if_congr ((zpow_right_strictMono₀ (residueNorm_gt_one F v)).le_iff_le.trans neg_le_neg_iff)
    rfl rfl

private theorem finiteValuationBallTest_sub_apply_shell (i n : ℤ) (x : (K F v)ˣ)
    (hx : x ∈ finiteZetaShell F v n) :
    (finiteValuationBallTest F v i - finiteValuationBallTest F v (i + 1)).val x.val =
      if i = n then 1 else 0 := by
  change (finiteValuationBallTest F v i).val x.val -
    (finiteValuationBallTest F v (i + 1)).val x.val = _
  rw [finiteValuationBallTest_apply_shell F v i n x hx, finiteValuationBallTest_apply_shell F v (i+1) n x hx]
  by_cases h : i = n
  · subst n
    simp
  · by_cases hi : i < n
    · have hh : i + 1 ≤ n := by omega
      simp [hi.le, hh, h]
    · have hh : ¬ i + 1 ≤ n := by omega
      have hi' : ¬ i ≤ n := by omega
      simp [hi', hh, h]

/-- A compact, locally constant test invariant under integral units is a finite
linear combination of dilates of the integer-ring indicator. This includes
the entire ball on which the test is constant at zero. -/
theorem finiteValuationBallTest_expansion
    (f : locallyConstantTests (K F v))
    (hf : ∀ (x : K F v) (u : (K F v)ˣ), u ∈ finitePlaceIntegralUnits F v →
      f.val (x * u.val) = f.val x) :
    ∃ L : ℤ, ∃ N : ℕ,
      f = f.val 0 • finiteValuationBallTest F v (N : ℤ) +
        ∑ i ∈ Finset.Ico L (N : ℤ),
          f.val ((chosenFiniteUniformizer F v ^ i : (K F v)ˣ).val) •
            (finiteValuationBallTest F v i - finiteValuationBallTest F v (i + 1)) := by
  obtain ⟨L,N,_,h⟩ := finiteZetaShell_test_bounds F v f
  refine ⟨L,N,?_⟩
  apply Subtype.ext
  funext x
  simp only [Submodule.coe_add, Submodule.coe_smul, Submodule.coe_sum, Pi.add_apply, Pi.smul_apply,
    Finset.sum_apply, smul_eq_mul]
  by_cases hx : x = 0
  · subst x
    have hz (i : ℤ) : (finiteValuationBallTest F v i).val 0 = 1 := by
      rw [finiteValuationBallTest_apply, norm_zero, ite_eq_left (zpow_nonneg (le_of_lt
        (zero_lt_one.trans (residueNorm_gt_one F v))) _)]
    simp [hz]
  let y := Units.mk0 x hx
  change f.val y.val = f.val 0 * (finiteValuationBallTest F v (N : ℤ)).val y.val +
    ∑ i ∈ Finset.Ico L (N : ℤ),
      f.val ((chosenFiniteUniformizer F v ^ i : (K F v)ˣ).val) *
        (finiteValuationBallTest F v i - finiteValuationBallTest F v (i + 1)).val y.val
  obtain ⟨n,hn⟩ := iUnion_eq_univ_iff.mp (finiteZetaShell_iUnion F v) y
  rw [finiteValuationBallTest_apply_shell F v (N : ℤ) n y hn]
  simp_rw [finiteValuationBallTest_sub_apply_shell F v _ n y hn, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq']
  by_cases hN : (N : ℤ) ≤ n
  · have hI : n ∉ Finset.Ico L (N : ℤ) :=
      fun hI ↦ (not_lt_of_ge hN) (Finset.mem_Ico.mp hI).2
    simpa [hN, hI] using (h n y hn).2 hN
  by_cases hL : n < L
  · have hI : n ∉ Finset.Ico L (N : ℤ) :=
      fun hI ↦ (not_le_of_gt hL) (Finset.mem_Ico.mp hI).1
    simpa [hN, hI] using (h n y hn).1 hL
  have hI : n ∈ Finset.Ico L (N : ℤ) := Finset.mem_Ico.mpr ⟨le_of_not_gt hL, lt_of_not_ge hN⟩
  let π := chosenFiniteUniformizer F v
  let u := (π ^ n)⁻¹ * y
  have he : π ^ n * u = y := by simp [u]
  have hu : u ∈ finitePlaceIntegralUnits F v := by
    rw [← finiteZetaShell_preimage F v π (chosenFiniteUniformizer_spec F v) n]
    change π ^ n * u ∈ finiteZetaShell F v n
    rwa [he]
  have hh := hf (π ^ n).val u hu
  rw [← Units.val_mul, he] at hh
  simpa [hN, hI, π] using hh

end

end Masullo
