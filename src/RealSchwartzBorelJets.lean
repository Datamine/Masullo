import PointTemperedDistribution
import SchwartzComplete
import FrechetFactorization
import Mathlib.RingTheory.PowerSeries.PiTopology

open Filter Function Set TopologicalSpace Topology
open scoped ContDiff SchwartzMap PowerSeries.WithPiTopology

namespace Masullo

noncomputable section

private abbrev S := 𝓢(ℝ, ℂ)

/-- Pullback of a Schwartz function by positive real dilation. -/
def schwartzPositiveDilate {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (r : ℝ) (hr : 0 < r) : 𝓢(E, ℂ) →L[ℂ] 𝓢(E, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (LinearEquiv.smulOfNeZero ℝ E r hr.ne').toContinuousLinearEquiv

theorem schwartzPositiveDilate_seminorm_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (r : ℝ) (hr : 1 ≤ r) (f : 𝓢(E, ℂ)) (k j : ℕ) :
    SchwartzMap.seminorm ℂ k j (schwartzPositiveDilate r (zero_lt_one.trans_le hr) f) ≤
      r ^ j * SchwartzMap.seminorm ℂ k j f := by
  have hr0 := zero_lt_one.trans_le hr
  apply SchwartzMap.seminorm_le_bound ℂ _ _ _ (by positivity)
  intro x
  change ‖x‖ ^ k * ‖iteratedFDeriv ℝ j (fun y ↦ f.toFun (r • y)) x‖ ≤ _
  have htop : (j : ℕ∞ω) ≤ ∞ := by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤)
  rw [iteratedFDeriv_comp_const_smul r (f.smooth'.of_le htop), norm_smul,
    Real.norm_of_nonneg (pow_nonneg hr0.le _)]
  have hx : ‖x‖ ≤ ‖r • x‖ := by
    rw [norm_smul, Real.norm_of_nonneg hr0.le]
    exact le_mul_of_one_le_left (norm_nonneg _) hr
  calc
    _ = r ^ j * (‖x‖ ^ k * ‖iteratedFDeriv ℝ j f.toFun (r • x)‖) := by ring
    _ ≤ r ^ j * (‖r • x‖ ^ k * ‖iteratedFDeriv ℝ j f.toFun (r • x)‖) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (norm_nonneg _) hx _) (norm_nonneg _)) (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_left (SchwartzMap.le_seminorm ℂ k j f _) (by positivity)

private theorem realSchwartzJet_dilate (r : ℝ) (hr : 0 < r) (f : S) (j : ℕ) :
    realSchwartzJet j (schwartzPositiveDilate r hr f) = (r : ℂ) ^ j * realSchwartzJet j f := by
  change iteratedDeriv j (fun y ↦ f.toFun (r * y)) 0 = _
  have htop : (j : ℕ∞ω) ≤ ∞ := by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤)
  rw [iteratedDeriv_comp_const_smul (f.smooth'.of_le htop) r]
  change r ^ j • iteratedDeriv j f.toFun (r * 0) = _
  rw [mul_zero, Complex.real_smul, Complex.ofReal_pow]
  rfl

/-- Interpolate a sequence of Schwartz functionals with individually
normalized test functions and increasing homogeneity degrees. Positive
dilation controls every fixed seminorm in the tail of the series. -/
theorem exists_schwartz_interpolating_graded_jets
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (J : ℕ → 𝓢(E, ℂ) →L[ℂ] ℂ) (d : ℕ → ℕ)
    (hd : Tendsto d atTop atTop)
    (hSingle : ∀ n, ∃ f : 𝓢(E, ℂ), ∀ j, J j f = if j = n then 1 else 0)
    (hDilate : ∀ (r : ℝ) (hr : 0 < r) (f : 𝓢(E, ℂ)) (j : ℕ),
      J j (schwartzPositiveDilate r hr f) = (r : ℂ) ^ d j * J j f)
    (a : ℕ → ℂ) : ∃ f : 𝓢(E, ℂ), ∀ n, J n f = a n := by
  classical
  choose v hv using hSingle
  let ε (n : ℕ) := (1 / 2 : ℝ) ^ n
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  let B (n : ℕ) : ℝ := ∑ p ∈ Finset.Iic (n,n), SchwartzMap.seminorm ℂ p.1 p.2 (v n)
  have hB (n : ℕ) : 0 ≤ B n := Finset.sum_nonneg fun _ _ ↦ apply_nonneg _ _
  let r (n : ℕ) := 1 + ‖a n‖ * B n / ε n
  have hr (n : ℕ) : 1 ≤ r n := le_add_of_nonneg_right (by positivity)
  have hr0 (n : ℕ) := zero_lt_one.trans_le (hr n)
  let u (n : ℕ) := (a n / (r n : ℂ) ^ (d n)) • schwartzPositiveDilate (r n) (hr0 n) (v n)
  have hu (n j : ℕ) : J j (u n) = if j = n then a n else 0 := by
    have hne : (r n : ℂ) ^ (d n) ≠ 0 := pow_ne_zero _ (by exact_mod_cast (hr0 n).ne')
    rw [show u n = _ from rfl, map_smul, hDilate, hv]
    split_ifs with h
    · subst j
      rw [mul_one, smul_eq_mul, div_mul_cancel₀ _ hne]
    · simp
  have huB (n k j : ℕ) (hk : k ≤ n) (hj : j ≤ n) (hjd : j < d n) :
      SchwartzMap.seminorm ℂ k j (u n) ≤ ε n := by
    have hsem : SchwartzMap.seminorm ℂ k j (v n) ≤ B n :=
        Finset.single_le_sum (fun p : ℕ × ℕ ↦ fun _ ↦
          apply_nonneg (SchwartzMap.seminorm ℂ p.1 p.2) (v n))
          (show (k,j) ∈ Finset.Iic (n,n) from Finset.mem_Iic.mpr ⟨hk, hj⟩)
    have hpow : r n ^ (j + 1) ≤ r n ^ d n := pow_le_pow_right₀ (hr n) (by omega)
    have hdiv : r n ^ j / r n ^ d n ≤ (r n)⁻¹ := by
      apply (div_le_iff₀ (by positivity : 0 < r n ^ d n)).mpr
      rw [inv_mul_eq_div]
      apply (le_div_iff₀ (hr0 n)).mpr
      simpa only [pow_succ] using hpow
    calc
      _ ≤ (‖a n‖ / r n ^ d n) * (r n ^ j * B n) := by
        rw [show u n = _ from rfl, map_smul_eq_mul, norm_div, norm_pow,
          Complex.norm_real, Real.norm_of_nonneg (hr0 n).le]
        exact mul_le_mul_of_nonneg_left ((schwartzPositiveDilate_seminorm_le _ (hr n) _ _ _).trans
          (mul_le_mul_of_nonneg_left hsem (by positivity))) (by positivity)
      _ = (‖a n‖ * B n) * (r n ^ j / r n ^ d n) := by ring
      _ ≤ (‖a n‖ * B n) * (r n)⁻¹ := mul_le_mul_of_nonneg_left hdiv (by positivity)
      _ ≤ ε n := by
        rw [← div_eq_mul_inv]
        apply (div_le_iff₀ (hr0 n)).mpr
        change ‖a n‖ * B n ≤ ε n * (1 + ‖a n‖ * B n / ε n)
        rw [mul_add, mul_one, mul_div_cancel₀ _ (hε n).ne']
        linarith [hε n]
  have hs (k j : ℕ) : Summable (fun n ↦ SchwartzMap.seminorm ℂ k j (u n)) := by
    obtain ⟨m₀, hm₀⟩ := eventually_atTop.mp (Filter.tendsto_atTop.mp hd (j+1))
    let m := max m₀ (max k j)
    apply (summable_nat_add_iff m).mp
    refine Summable.of_nonneg_of_le (fun _ ↦ apply_nonneg _ _) (fun n ↦ ?_)
      ((summable_nat_add_iff m).mpr
        (summable_geometric_of_lt_one (r := (1/2 : ℝ)) (by norm_num) (by norm_num)))
    exact huB (n+m) k j (by dsimp [m]; omega) (by dsimp [m]; omega)
      (hm₀ _ (by dsimp [m]; omega))
  obtain ⟨f, hf⟩ := schwartz_tendsto_partialSums u hs
  refine ⟨f, fun j ↦ ?_⟩
  have hlim := (J j).continuous.continuousAt.tendsto.comp hf
  have hconst : (fun n ↦ J j (∑ i ∈ Finset.range n, u i)) =ᶠ[atTop] fun _ ↦ a j := by
    filter_upwards [eventually_gt_atTop j] with n hn
    simp only [map_sum, hu]
    simp [Finset.mem_range.mpr hn]
  exact tendsto_nhds_unique hlim (tendsto_const_nhds.congr' hconst.symm)

/-- Borel interpolation on the real Schwartz space. -/
theorem exists_realSchwartz_with_jets (a : ℕ → ℂ) :
    ∃ f : S, ∀ n, realSchwartzJet n f = a n :=
  exists_schwartz_interpolating_graded_jets realSchwartzJet id tendsto_id
    (fun n ↦ by
      obtain ⟨f, hf⟩ := exists_smoothTest_single_jet n
      exact ⟨smoothTestToSchwartz f, hf⟩)
    realSchwartzJet_dilate a

/-- The Taylor map with factorial-normalized coefficients, given the product
topology on the sequence of coefficients. -/
def realSchwartzTaylor : S →L[ℂ] (ℕ → ℂ) :=
  ContinuousLinearMap.pi fun j ↦ (j.factorial : ℂ)⁻¹ • realSchwartzJet j

/-- Flatness at zero is exactly the kernel of the Taylor map. -/
theorem mem_realSchwartzTaylor_ker (f : S) :
    f ∈ realSchwartzTaylor.ker ↔ ∀ j, realSchwartzJet j f = 0 := by
  change realSchwartzTaylor f = 0 ↔ _
  constructor
  · intro hf j
    have h := congrFun hf j
    change (j.factorial : ℂ)⁻¹ * realSchwartzJet j f = 0 at h
    exact (mul_eq_zero.mp h).resolve_left
      (inv_ne_zero (by exact_mod_cast Nat.factorial_ne_zero j))
  · intro hf
    funext j
    change (j.factorial : ℂ)⁻¹ * realSchwartzJet j f = 0
    rw [hf, mul_zero]

theorem realSchwartzTaylor_surjective : Surjective realSchwartzTaylor := by
  intro a
  obtain ⟨f, hf⟩ := exists_realSchwartz_with_jets (fun j ↦ (j.factorial : ℂ) * a j)
  refine ⟨f, funext fun j ↦ ?_⟩
  change (j.factorial : ℂ)⁻¹ * realSchwartzJet j f = a j
  rw [hf, ← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero j), one_mul]

/-- The quotient by the flat tests is topologically the product of all
Taylor coefficients. -/
def realSchwartzTaylorQuotient :
    (S ⧸ realSchwartzTaylor.ker) ≃L[ℂ] (ℕ → ℂ) := by
  let M := realSchwartzTaylor.ker
  let p := M.liftQL realSchwartzTaylor le_rfl
  have hp : Bijective p := by
    constructor
    · apply (LinearMap.ker_eq_bot.mp _ : Injective p.toLinearMap)
      exact Submodule.ker_liftQ_eq_bot _ _ _ le_rfl
    · intro a
      obtain ⟨x, rfl⟩ := realSchwartzTaylor_surjective a
      exact ⟨M.mkQ x, rfl⟩
  letI : @CompleteSpace S (IsTopologicalAddGroup.rightUniformSpace S) := by
    rw [IsUniformAddGroup.rightUniformSpace_eq]
    exact completeSpace_schwartzMap
  have hOpen := isOpenMap_of_surjective_complete_baire realSchwartzTaylor realSchwartzTaylor_surjective
  have hOpenQ : IsOpenMap p := by
    apply IsOpenMap.of_comp M.continuous_mkQ M.mkQ_surjective
    exact hOpen
  let e := LinearEquiv.ofBijective p.toLinearMap hp
  exact ⟨e, p.continuous, (e.toEquiv.toHomeomorphOfContinuousOpen p.continuous hOpenQ).continuous_invFun⟩

@[simp] theorem realSchwartzTaylorQuotient_mkQ (f : S) :
    realSchwartzTaylorQuotient (realSchwartzTaylor.ker.mkQ f) = realSchwartzTaylor f := rfl

private def sequencePowerSeriesEquiv : (ℕ → ℂ) ≃L[ℂ] PowerSeries ℂ where
  toFun := PowerSeries.mk
  invFun f n := PowerSeries.coeff n f
  left_inv _ := funext fun n ↦ PowerSeries.coeff_mk n _
  right_inv _ := PowerSeries.ext fun n ↦ PowerSeries.coeff_mk n _
  map_add' _ _ := PowerSeries.ext fun n ↦ by simp
  map_smul' _ _ := PowerSeries.ext fun n ↦ by simp
  continuous_toFun := by
    apply continuous_iff_continuousAt.mpr
    intro a
    apply (PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto ℂ _ _ _).mpr
    intro n
    simp only [PowerSeries.coeff_mk]
    exact (continuous_apply n).continuousAt.tendsto
  continuous_invFun := continuous_pi (PowerSeries.WithPiTopology.continuous_coeff ℂ)

/-- The flat-test quotient is the space of formal power series with the
coefficient product topology. -/
def realSchwartzTaylorPowerSeries :
    (S ⧸ realSchwartzTaylor.ker) ≃L[ℂ] PowerSeries ℂ :=
  realSchwartzTaylorQuotient.trans sequencePowerSeriesEquiv

@[simp] theorem realSchwartzTaylorPowerSeries_coeff (f : S) (n : ℕ) :
    PowerSeries.coeff n (realSchwartzTaylorPowerSeries (realSchwartzTaylor.ker.mkQ f)) =
      (n.factorial : ℂ)⁻¹ * realSchwartzJet n f := by
  change PowerSeries.coeff n (PowerSeries.mk
    (realSchwartzTaylorQuotient (realSchwartzTaylor.ker.mkQ f))) = _
  rw [PowerSeries.coeff_mk, realSchwartzTaylorQuotient_mkQ]
  rfl

end
end Masullo
