import ArchimedeanCharacters
import SchwartzFlatExtension
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

open Filter Set Topology
open scoped Classical ContDiff SchwartzMap

namespace Masullo

noncomputable section

/-- Read a character of the units as a function of the field coordinate.
The value assigned at zero is used for zero extension. -/
def unitCharacterZeroExtend {L : Type*} [Field L] [TopologicalSpace L]
    (χ : Lˣ →ₜ* ℂ) (x : L) : ℂ :=
  if hx : x ≠ 0 then χ (Units.mk0 x hx) else 0

@[simp] theorem unitCharacterZeroExtend_apply_units {L : Type*} [Field L] [TopologicalSpace L]
    (χ : Lˣ →ₜ* ℂ) (u : Lˣ) : unitCharacterZeroExtend χ u.val = χ u := by
  rw [unitCharacterZeroExtend, dite_eq_left u.ne_zero]
  exact congrArg χ (Units.ext rfl)

private theorem contDiffAt_ofReal_cpow {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a : E → ℝ} {x : E} (ha : ContDiffAt ℝ ∞ a x) (hax : 0 < a x) (z : ℂ) :
    ContDiffAt ℝ ∞ (fun y ↦ (a y : ℂ) ^ z) x := by
  have hlog : ContDiffAt ℝ ∞ (fun y ↦ (Real.log (a y) : ℂ)) x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x (ha.log hax.ne')
  have hz : ContDiffAt ℝ ∞ (fun _ : E ↦ z) x := contDiffAt_const
  apply (hlog.mul hz).cexp.congr_of_eventuallyEq
  filter_upwards [ha.continuousAt.eventually (lt_mem_nhds hax)] with y hy
  have hp : 0 < a y := hy
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hp.ne'), ← Complex.ofReal_log hp.le]

/-- A continuous real-place quasi-character is smooth off zero in its real coordinate. -/
theorem realUnitCharacterZeroExtend_contDiffOn (χ : ℝˣ →ₜ* ℂ) :
    ContDiffOn ℝ ∞ (unitCharacterZeroExtend χ) {x | x ≠ 0} := by
  obtain ⟨a, ha, _⟩ := existsUnique_realUnits_quasiCharacter_parameters χ
  intro x hx
  have hx0 : x ≠ 0 := hx
  have hn := contDiffAt_ofReal_cpow (contDiffAt_norm ℝ hx0) (norm_pos_iff.mpr hx0) a.1
  let b : ℂ := (if 0 < x then 1 else (-1 : ℂ)) ^ a.2.val
  have hB : ∀ᶠ y : ℝ in 𝓝 x, (if 0 < y then 1 else (-1 : ℂ)) ^ a.2.val = b := by
    rcases lt_or_gt_of_ne hx0 with h | h
    · filter_upwards [gt_mem_nhds h] with y hy
      simp [b, not_lt_of_ge h.le, not_lt_of_ge hy.le]
    · filter_upwards [lt_mem_nhds h] with y hy
      simp [b, h, hy]
  apply ContDiffAt.contDiffWithinAt
  have hb : ContDiffAt ℝ ∞ (fun _ : ℝ ↦ b) x := contDiffAt_const
  apply (hn.mul hb).congr_of_eventuallyEq
  filter_upwards [(isOpen_ne_fun continuous_id continuous_const).mem_nhds hx0, hB] with y hy hw
  have hne : y ≠ 0 := hy
  rw [unitCharacterZeroExtend, dite_eq_left hne, ha]
  change (‖y‖ : ℂ) ^ a.1 * (if 0 < y then 1 else (-1 : ℂ)) ^ a.2.val = _
  rw [hw]

private theorem contDiffAt_complex_zpow {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : E → ℂ} {x : E} (hg : ContDiffAt ℝ ∞ g x) (hx : g x ≠ 0) (m : ℤ) :
    ContDiffAt ℝ ∞ (fun y ↦ g y ^ m) x := by
  cases m with
  | ofNat m => simpa using hg.pow m
  | negSucc m =>
    have h : ContDiffAt ℝ ∞ (fun y ↦ g y ^ (m + 1))⁻¹ x :=
      (hg.pow (m + 1)).inv (pow_ne_zero (m + 1) hx)
    convert h using 1
    funext y
    exact zpow_negSucc _ _

/-- A continuous complex-place quasi-character is smooth off zero in its real
two-dimensional coordinate. -/
theorem complexUnitCharacterZeroExtend_contDiffOn (χ : ℂˣ →ₜ* ℂ) :
    ContDiffOn ℝ ∞ (unitCharacterZeroExtend χ) {x | x ≠ 0} := by
  obtain ⟨a, ha, _⟩ := existsUnique_complexUnits_quasiCharacter_parameters χ
  intro x hx
  have hx0 : x ≠ 0 := hx
  have hnorm := contDiffAt_norm ℝ (n := ∞) hx0
  have hnorm0 := norm_pos_iff.mpr hx0
  have hn := contDiffAt_ofReal_cpow (hnorm.pow 2) (pow_pos hnorm0 2) a.1
  have hid : ContDiffAt ℝ ∞ (fun y : ℂ ↦ y) x := contDiffAt_id
  have hc : ContDiffAt ℝ ∞ (fun y : ℂ ↦ (‖y‖ : ℂ)) x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x hnorm
  have hang : ContDiffAt ℝ ∞ (fun y : ℂ ↦ y / (‖y‖ : ℂ)) x := by
    simp only [div_eq_mul_inv]
    exact hid.mul (hc.inv (Complex.ofReal_ne_zero.mpr hnorm0.ne'))
  have hang' := contDiffAt_complex_zpow hang (div_ne_zero hx0 (Complex.ofReal_ne_zero.mpr hnorm0.ne')) a.2
  apply ContDiffAt.contDiffWithinAt
  apply (hn.mul hang').congr_of_eventuallyEq
  filter_upwards [(isOpen_ne_fun continuous_id continuous_const).mem_nhds hx0] with y hy
  have hne : y ≠ 0 := hy
  rw [unitCharacterZeroExtend, dite_eq_left hne, ha]
  rfl

private theorem norm_jet_dilation {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (b : E → ℂ) (hb : ContDiffOn ℝ ∞ b {x | x ≠ 0})
    (r : ℝ) (hr : 0 < r) (c : ℂ) (h : ∀ x : E, b (r • x) = c * b x)
    (x : E) (hx : x ≠ 0) (j : ℕ) :
    r ^ j * ‖iteratedFDeriv ℝ j b (r • x)‖ = ‖c‖ * ‖iteratedFDeriv ℝ j b x‖ := by
  let U := {x : E | x ≠ 0}
  have hU : IsOpen U := isOpen_ne_fun continuous_id continuous_const
  let A : E →L[ℝ] E := r • ContinuousLinearMap.id ℝ E
  have hA (y : E) : A y = r • y := rfl
  have hUA : A ⁻¹' U = U := by
    ext y
    change r • y ≠ 0 ↔ y ≠ 0
    simp [hr.ne']
  have he : b ∘ A = c • b := funext fun y ↦ h y
  have hxr : A x ∈ U := smul_ne_zero hr.ne' hx
  have hc := A.iteratedFDerivWithin_comp_right hb hU.uniqueDiffOn
    (hUA.symm ▸ hU.uniqueDiffOn) hxr (i := j) (by exact_mod_cast le_top : (j : ℕ∞ω) ≤ ∞)
  rw [he, hUA, iteratedFDerivWithin_of_isOpen j hU hx,
    iteratedFDerivWithin_of_isOpen j hU hxr,
    iteratedFDeriv_const_smul_apply (hb.contDiffAt (hU.mem_nhds hx) |>.of_le
      (by exact_mod_cast le_top : (j : ℕ∞ω) ≤ ∞))] at hc
  have hcomp : (iteratedFDeriv ℝ j b (A x)).compContinuousLinearMap (fun _ ↦ A) =
      (r ^ j) • iteratedFDeriv ℝ j b (A x) := by
    ext v
    change (iteratedFDeriv ℝ j b (A x)) (fun i ↦ r • v i) =
      r ^ j • (iteratedFDeriv ℝ j b (A x)) v
    rw [ContinuousMultilinearMap.map_smul_univ]
    simp
  rw [hcomp] at hc
  have hn := congrArg norm hc.symm
  simpa only [norm_smul, Real.norm_of_nonneg (pow_nonneg hr.le j), hA] using hn

/-- Smooth homogeneous functions have polynomially bounded jets at infinity
and singularities of finite order at the puncture. -/
private theorem homogeneous_jet_bounds {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [ProperSpace E] (b : E → ℂ) (hb : ContDiffOn ℝ ∞ b {x | x ≠ 0})
    (a : ℝ) (hscale : ∀ r : ℝ, 0 < r → ∃ c : ℂ, (∀ x : E, b (r • x) = c * b x) ∧ ‖c‖ = r ^ a)
    (n : ℕ) : ∃ (M : ℕ) (B : ℝ), 0 ≤ B ∧ ∀ j ≤ n, ∀ x : E, x ≠ 0 →
      ‖iteratedFDeriv ℝ j b x‖ ≤ B * max 1 ‖x‖ ^ M / min 1 ‖x‖ ^ M := by
  let U := {x : E | x ≠ 0}
  have hU : IsOpen U := isOpen_ne_fun continuous_id continuous_const
  have hSphere : Metric.sphere (0 : E) 1 ⊆ U := by
    intro y hy
    have hny : ‖y‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hy
    exact norm_ne_zero_iff.mp (hny.trans_ne one_ne_zero)
  have hc (j : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ y : E, ‖y‖ = 1 → ‖iteratedFDeriv ℝ j b y‖ ≤ C := by
    have hcont : ContinuousOn (fun y ↦ ‖iteratedFDeriv ℝ j b y‖) (Metric.sphere (0 : E) 1) := by
      apply ((hb.continuousOn_iteratedFDerivWithin
        (by exact_mod_cast le_top : (j : ℕ∞ω) ≤ ∞) hU.uniqueDiffOn).norm.mono hSphere).congr
      intro y hy
      change ‖iteratedFDeriv ℝ j b y‖ = ‖iteratedFDerivWithin ℝ j b U y‖
      exact congrArg norm ((iteratedFDerivWithin_of_isOpen j hU (hSphere hy)).symm)
    obtain ⟨C, hC⟩ := (isCompact_sphere (0 : E) 1).bddAbove_image hcont
    exact ⟨max C 0, le_max_right _ _, fun y hy ↦
      (hC ⟨y, by simpa only [Metric.mem_sphere, dist_zero_right] using hy, rfl⟩).trans (le_max_left _ _)⟩
  choose C hC hCb using hc
  obtain ⟨M, hM⟩ := exists_nat_gt (|a| + n)
  refine ⟨M, ∑ j ∈ Finset.range (n+1), C j, Finset.sum_nonneg (fun j _ ↦ hC j), ?_⟩
  intro j hj x hx
  let r := ‖x‖
  have hr : 0 < r := norm_pos_iff.mpr hx
  let y := r⁻¹ • x
  have hy : ‖y‖ = 1 := by
    simp [y, norm_smul, r, norm_ne_zero_iff.mpr hx]
  have hy0 : y ≠ 0 := norm_ne_zero_iff.mp (hy.trans_ne one_ne_zero)
  have hxy : r • y = x := by simp [y, smul_smul, hr.ne']
  obtain ⟨c, hs, hcn⟩ := hscale r hr
  have hJ := norm_jet_dilation b hb r hr c hs y hy0 j
  rw [hxy, hcn] at hJ
  have hB : C j ≤ ∑ l ∈ Finset.range (n+1), C l :=
    Finset.single_le_sum (fun l _ ↦ hC l) (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
  have hD : ‖iteratedFDeriv ℝ j b x‖ ≤ (∑ l ∈ Finset.range (n+1), C l) * r ^ (a - (j : ℝ)) := by
    rw [Real.rpow_sub_natCast hr.ne', ← mul_div_assoc]
    apply (le_div_iff₀ (pow_pos hr j)).mpr
    calc
      _ = r ^ a * ‖iteratedFDeriv ℝ j b y‖ := (mul_comm _ _).trans hJ
      _ ≤ r ^ a * (∑ l ∈ Finset.range (n+1), C l) :=
        mul_le_mul_of_nonneg_left ((hCb j y hy).trans hB) (Real.rpow_nonneg hr.le _)
      _ = _ := mul_comm _ _
  have hja : (j : ℝ) ≤ n := by exact_mod_cast hj
  have hplus : a - (j : ℝ) ≤ M := by linarith [le_abs_self a, Nat.cast_nonneg (α := ℝ) j]
  have hminus : -(M : ℝ) ≤ a - (j : ℝ) := by linarith [neg_abs_le a]
  refine hD.trans ?_
  change _ ≤ _ * max 1 r ^ M / min 1 r ^ M
  rcases le_total 1 r with h | h
  · rw [max_eq_right h, min_eq_left h, one_pow, div_one]
    exact mul_le_mul_of_nonneg_left (by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le h hplus) (Finset.sum_nonneg fun l _ ↦ hC l)
  · rw [max_eq_left h, min_eq_right h, one_pow, mul_one, div_eq_mul_inv]
    apply mul_le_mul_of_nonneg_left _ (Finset.sum_nonneg fun l _ ↦ hC l)
    rw [← Real.rpow_natCast, ← Real.rpow_neg hr.le]
    exact Real.rpow_le_rpow_of_exponent_ge hr h hminus

private def positiveScalarUnit (L : Type*) [NormedField L] [NormedAlgebra ℝ L]
    (r : ℝ) (hr : 0 < r) : Lˣ :=
  Units.mk0 (algebraMap ℝ L r) ((map_ne_zero (algebraMap ℝ L)).mpr hr.ne')

private theorem unitCharacterZeroExtend_smul {L : Type*} [NormedField L] [NormedAlgebra ℝ L]
    (χ : Lˣ →ₜ* ℂ) (r : ℝ) (hr : 0 < r) (x : L) :
    unitCharacterZeroExtend χ (r • x) =
      χ (positiveScalarUnit L r hr) * unitCharacterZeroExtend χ x := by
  by_cases hx : x = 0
  · simp [hx, unitCharacterZeroExtend]
  · have hm : (positiveScalarUnit L r hr * Units.mk0 x hx : Lˣ).val = r • x :=
      (Algebra.smul_def r x).symm
    rw [← hm, unitCharacterZeroExtend_apply_units, map_mul, unitCharacterZeroExtend, dite_eq_left hx]

/-- Every real-place quasi-character has polynomial jet bounds, with a
finite power of the inverse distance allowed at zero. -/
theorem realUnitCharacterZeroExtend_jet_bounds (χ : ℝˣ →ₜ* ℂ) (n : ℕ) :
    ∃ (M : ℕ) (B : ℝ), 0 ≤ B ∧ ∀ j ≤ n, ∀ x : ℝ, x ≠ 0 →
      ‖iteratedFDeriv ℝ j (unitCharacterZeroExtend χ) x‖ ≤
        B * max 1 ‖x‖ ^ M / min 1 ‖x‖ ^ M := by
  obtain ⟨a, ha, _⟩ := existsUnique_realUnits_quasiCharacter_parameters χ
  apply homogeneous_jet_bounds (unitCharacterZeroExtend χ)
    (realUnitCharacterZeroExtend_contDiffOn χ) a.1.re _ n
  intro r hr
  refine ⟨χ (positiveScalarUnit ℝ r hr), unitCharacterZeroExtend_smul χ r hr, ?_⟩
  rw [ha]
  change ‖(‖r‖ : ℂ) ^ a.1 * (if 0 < r then 1 else (-1 : ℂ)) ^ a.2.val‖ = _
  rw [ite_eq_left hr, one_pow, mul_one, Real.norm_of_nonneg hr.le, Complex.norm_cpow_eq_rpow_re_of_pos hr]

/-- The corresponding jet bounds for a complex-place quasi-character,
viewed as a function of its real two-dimensional coordinate. -/
theorem complexUnitCharacterZeroExtend_jet_bounds (χ : ℂˣ →ₜ* ℂ) (n : ℕ) :
    ∃ (M : ℕ) (B : ℝ), 0 ≤ B ∧ ∀ j ≤ n, ∀ x : ℂ, x ≠ 0 →
      ‖iteratedFDeriv ℝ j (unitCharacterZeroExtend χ) x‖ ≤
        B * max 1 ‖x‖ ^ M / min 1 ‖x‖ ^ M := by
  obtain ⟨a, ha, _⟩ := existsUnique_complexUnits_quasiCharacter_parameters χ
  apply homogeneous_jet_bounds (unitCharacterZeroExtend χ)
    (complexUnitCharacterZeroExtend_contDiffOn χ) (2 * a.1.re) _ n
  intro r hr
  refine ⟨χ (positiveScalarUnit ℂ r hr), unitCharacterZeroExtend_smul χ r hr, ?_⟩
  rw [ha]
  change ‖((‖(r : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ a.1 * ((r : ℂ) / (‖(r : ℂ)‖ : ℂ)) ^ a.2‖ = _
  rw [Complex.norm_of_nonneg hr.le, div_self (Complex.ofReal_ne_zero.mpr hr.ne'),
    one_zpow, mul_one, Complex.norm_cpow_eq_rpow_re_of_pos (pow_pos hr 2),
    ← Real.rpow_natCast, ← Real.rpow_mul hr.le]
  norm_num

private theorem coordinateMultiplier_bounds {E L : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup L] [NormedSpace ℝ L]
    (b : L → ℂ) (hb : ContDiffOn ℝ ∞ b {x | x ≠ 0})
    (h : ∀ n : ℕ, ∃ (M : ℕ) (B : ℝ), 0 ≤ B ∧ ∀ j ≤ n, ∀ x : L, x ≠ 0 →
      ‖iteratedFDeriv ℝ j b x‖ ≤ B * max 1 ‖x‖ ^ M / min 1 ‖x‖ ^ M)
    (p : E →L[ℝ] L) (hp : ∀ x : E, ‖p x‖ ≤ ‖x‖) (n : ℕ) :
    ∃ (M : ℕ) (B : ℝ), 0 ≤ B ∧ ∀ j ≤ n, ∀ x : E, p x ≠ 0 →
      ‖iteratedFDeriv ℝ j (b ∘ p) x‖ ≤ B * max 1 ‖x‖ ^ M / min 1 ‖p x‖ ^ M := by
  have hp' : ‖p‖ ≤ 1 := p.opNorm_le_bound zero_le_one (by simpa only [one_mul] using hp)
  obtain ⟨M, B, hB, hD⟩ := h n
  refine ⟨M, B, hB, fun j hj x hx ↦ ?_⟩
  have hU : IsOpen {x : L | x ≠ 0} := isOpen_ne_fun continuous_id continuous_const
  have hU' := hU.preimage p.continuous
  have hEq := p.iteratedFDerivWithin_comp_right hb hU.uniqueDiffOn hU'.uniqueDiffOn
    (x := x) hx (i := j) (by exact_mod_cast le_top : (j : ℕ∞ω) ≤ ∞)
  rw [iteratedFDerivWithin_of_isOpen j hU' hx, iteratedFDerivWithin_of_isOpen j hU hx] at hEq
  rw [hEq]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  refine (mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hp')).trans ((hD j hj _ hx).trans ?_)
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (le_max_of_le_left zero_le_one) (max_le_max_left 1 (hp x)) _) hB) (by positivity)

/-- A real- or complex-coordinate quasi-character acts continuously on
Schwartz tests flat on the coordinate hyperplane and any prescribed larger set. -/
theorem exists_coordinateQuasiCharacter_mulCLM {E L : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedField L] [NormedAlgebra ℝ L] (χ : Lˣ →ₜ* ℂ)
    (hb : ContDiffOn ℝ ∞ (unitCharacterZeroExtend χ) {x | x ≠ 0})
    (h : ∀ n : ℕ, ∃ (M : ℕ) (B : ℝ), 0 ≤ B ∧ ∀ j ≤ n, ∀ x : L, x ≠ 0 →
      ‖iteratedFDeriv ℝ j (unitCharacterZeroExtend χ) x‖ ≤ B * max 1 ‖x‖ ^ M / min 1 ‖x‖ ^ M)
    (p : E →L[ℝ] L) (i : L →L[ℝ] E) (hpi : Function.LeftInverse p i)
    (hp : ∀ x, ‖p x‖ ≤ ‖x‖) (hi : ∀ y, ‖i y‖ ≤ ‖y‖)
    (A : Set E) (hA : {x | p x = 0} ⊆ A) :
    ∃ M : schwartzFlatSubspace A →L[ℂ] schwartzFlatSubspace A,
      ∀ f : schwartzFlatSubspace A, ∀ x : E,
        (M f).val x = unitCharacterZeroExtend χ (p x) * f.val x := by
  let b := unitCharacterZeroExtend χ
  have hc : ContDiffOn ℝ ∞ (b ∘ p) {x | p x ≠ 0} :=
    hb.comp p.contDiff.contDiffOn (fun _ h ↦ h)
  obtain ⟨M, hM⟩ := exists_flatSchwartz_mulCLM_of_jet_bounds p i hpi hi (b ∘ p) hc
    (coordinateMultiplier_bounds b hb h p hp) A hA
  refine ⟨M, fun f x ↦ ?_⟩
  have hx := congrFun (hM f) x
  by_cases hpx : p x = 0 <;> simpa [indicator_apply, b, unitCharacterZeroExtend, hpx] using hx

end

end Masullo
