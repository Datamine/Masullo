import FiniteFlatQuasiCharacter
import FiniteTateFunctionalEquation

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped NumberField Pointwise

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

private abbrev K := v.adicCompletion F
private abbrev U := finitePlaceIntegralUnits F v
private abbrev Phase := (K F v)ˣ →ₜ* Circle

private def unitSphere : Set (K F v) :=
  Metric.closedBall 0 1 \ Metric.ball 0 1

private theorem mem_unitSphere (x : K F v) : x ∈ unitSphere F v ↔ ‖x‖ = 1 := by
  simp only [unitSphere, Set.mem_sdiff, Metric.mem_closedBall, Metric.mem_ball, dist_zero_right,
    not_lt]
  exact ⟨fun h ↦ le_antisymm h.1 h.2, fun h ↦ ⟨h.le, h.ge⟩⟩

private def unitSphereIndicator : finiteFlatTests F v := by
  have hK : IsCompact (Metric.closedBall (0 : K F v) 1) := by
    rw [finiteCompletion_closedBall]
    exact finitePlaceIntegral_compact F v
  have hCo : IsOpen (unitSphere F v) :=
    (IsUltrametricDist.isOpen_closedBall 0 (by norm_num)).sdiff
      (IsUltrametricDist.isClosed_ball _ _)
  let f := compactOpenIndicator (K F v) ⟨unitSphere F v, hK.diff Metric.isOpen_ball, hCo⟩
  refine ⟨f, ?_⟩
  change (unitSphere F v).indicator (fun _ ↦ (1 : ℂ)) 0 = 0
  exact indicator_of_notMem (by simp [mem_unitSphere]) _

private def gaussInversePhase (χ : Phase F v) : (K F v)ˣ →ₜ* ℂˣ := by
  let j : Circle →ₜ* ℂˣ := ⟨Circle.toUnits, Units.isEmbedding_val₀.continuous_iff.mpr
    continuous_subtype_val⟩
  exact j.comp χ⁻¹

/-- The conjugate unitary phase on the integral unit shell, extended by zero. -/
def finiteGaussTest (χ : Phase F v) : locallyConstantTests (K F v) :=
  (finiteFlatQuasiCharacterEquiv F v (gaussInversePhase F v χ) (unitSphereIndicator F v)).val

theorem finiteGaussTest_zero (χ : Phase F v) : (finiteGaussTest F v χ).val 0 = 0 :=
  (finiteFlatQuasiCharacterEquiv F v _ _).property

theorem finiteGaussTest_apply_units (χ : Phase F v) (u : (K F v)ˣ) :
    (finiteGaussTest F v χ).val u.val = if ‖u.val‖ = 1 then (((χ u)⁻¹ : Circle) : ℂ) else (0 : ℂ) := by
  unfold finiteGaussTest
  rw [finiteFlatQuasiCharacterEquiv_apply_units]
  change (((χ u)⁻¹ : Circle) : ℂ) *
    (unitSphere F v).indicator (fun _ ↦ (1 : ℂ)) u.val = _
  by_cases h : ‖u.val‖ = 1
  · rw [ite_eq_left h, indicator_of_mem ((mem_unitSphere F v _).mpr h), mul_one]
  · rw [ite_eq_right h, indicator_of_notMem (not_congr (mem_unitSphere F v _) |>.mpr h), mul_zero]

theorem finiteGaussTest_mellin
    [MeasurableSpace (K F v)ˣ] [BorelSpace (K F v)ˣ]
    (μ : Measure (K F v)ˣ) (χ : Phase F v) (z : ℂ) :
    finiteZetaIntegral F v μ χ (finiteGaussTest F v χ) z = (μ.real (U F v) : ℂ) := by
  have hU (u : (K F v)ˣ) : u ∈ U F v ↔ ‖u.val‖ = 1 := by
    change u ∈ finitePlaceIntegralUnits F v ↔ ‖u.val‖ = 1
    rw [← finiteZetaShell_zero, finiteZetaShell, mem_ofPred_eq, neg_zero, zpow_zero]
  have hUm : MeasurableSet (U F v) := by
    change MeasurableSet (finitePlaceIntegralUnits F v)
    rw [← finiteZetaShell_zero]
    exact (finiteZetaShell_closed F v 0).measurableSet
  unfold finiteZetaIntegral
  have he (u : (K F v)ˣ) :
      (finiteGaussTest F v χ).val u.val * ((χ u : Circle) : ℂ) * finiteZetaWeight F v z u =
        (U F v).indicator (fun _ ↦ (1 : ℂ)) u := by
    rw [finiteGaussTest_apply_units]
    by_cases h : ‖u.val‖ = 1
    · rw [ite_eq_left h, indicator_of_mem ((hU u).mpr h), ← Circle.coe_mul, inv_mul_cancel,
        Circle.coe_one]
      simp [finiteZetaWeight, h]
    · rw [ite_eq_right h, indicator_of_notMem (fun hu ↦ h ((hU u).mp hu)), zero_mul, zero_mul]
  simp_rw [he]
  rw [integral_indicator hUm, setIntegral_const]
  simp [Complex.real_smul]

theorem finiteGaussTest_dilate (χ : Phase F v) (u : (K F v)ˣ) (hu : ‖u.val‖ = 1) (x : K F v) :
    (finiteGaussTest F v χ).val (u.val⁻¹ * x) = (χ u : ℂ) * (finiteGaussTest F v χ).val x := by
  by_cases hx : x = 0
  · simp [hx, finiteGaussTest_zero]
  let a := Units.mk0 x hx
  rw [show u.val⁻¹ * x = (u⁻¹ * a).val by rw [Units.val_mul, Units.val_inv_eq_inv_val]; rfl]
  change (finiteGaussTest F v χ).val (u⁻¹ * a).val =
    (χ u : ℂ) * (finiteGaussTest F v χ).val a.val
  rw [finiteGaussTest_apply_units, finiteGaussTest_apply_units]
  have hn : ‖(u⁻¹ * a).val‖ = ‖a.val‖ := by simp [hu]
  rw [hn]
  split_ifs
  · rw [map_mul, map_inv, mul_inv_rev, inv_inv, ← Circle.coe_mul]
    exact congrArg (fun c : Circle ↦ (c : ℂ)) (mul_comm _ _)
  · simp

/-- A congruence level exists for every finite-place unitary phase. -/
theorem exists_finiteGaussTest_congruenceRadius (χ : Phase F v) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧
      ∀ u : (K F v)ˣ, ‖u.val - 1‖ ≤ ρ → χ u = 1 := by
  let ξ : (K F v)ˣ →ₜ* ℂ := ⟨Circle.coeHom.comp χ.toMonoidHom,
    continuous_subtype_val.comp χ.continuous⟩
  have hLC := finiteQuasiCharacter_isLocallyConstant F v ξ
  rw [IsLocallyConstant.iff_eventually_eq] at hLC
  let j : (K F v)ˣ → K F v := Units.val
  have hj : IsOpenEmbedding j := IsOpenUnits.isOpenEmbedding_unitsVal
  have hnh : j '' {u | ξ u = ξ 1} ∈ 𝓝 (j 1) := by
    rw [← hj.map_nhds_eq]
    exact Filter.image_mem_map (hLC 1)
  obtain ⟨r, hr, hB⟩ := Metric.mem_nhds_iff.mp hnh
  refine ⟨min (r / 2) (1 / 2), lt_min (by linarith) (by norm_num),
    (min_le_right _ _).trans_lt (by norm_num), ?_⟩
  intro u hu
  have hm : j u ∈ Metric.ball (j 1) r := by
    change dist u.val 1 < r
    rw [dist_eq_norm]
    exact (hu.trans (min_le_left _ _)).trans_lt (by linarith)
  obtain ⟨w, hw, he⟩ := hB hm
  have hw' : w = u := hj.injective he
  subst w
  exact Circle.coe_injective (hw.trans (map_one ξ) |>.trans Circle.coe_one.symm)

/-- A ramified phase has a positive least congruence exponent. The witness at
the preceding level detects the exact conductor, also at exponent one. -/
theorem exists_finiteGaussTest_conductor (χ : Phase F v) (hχ : ¬finiteZetaUnramified F v χ) :
    ∃ (n : ℕ), 0 < n ∧
      (∀ u : (K F v)ˣ, ‖u.val - 1‖ ≤ (v.asIdeal.absNorm : ℝ) ^ (-(n : ℤ)) → χ u = 1) ∧
      ∃ u : (K F v)ˣ, ‖u.val‖ = 1 ∧
        ‖u.val - 1‖ ≤ (v.asIdeal.absNorm : ℝ) ^ (1 - (n : ℤ)) ∧ χ u ≠ 1 := by
  classical
  let q := (v.asIdeal.absNorm : ℝ)
  have hq : 1 < q := by
    dsimp only [q]
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hq₀ := zero_lt_one.trans hq
  let P (n : ℕ) := ∀ u : (K F v)ˣ, ‖u.val - 1‖ ≤ q ^ (-(n : ℤ)) → χ u = 1
  have hP : ∃ n, P n := by
    obtain ⟨ρ, hρ, -, h⟩ := exists_finiteGaussTest_congruenceRadius F v χ
    have ht := tendsto_pow_atTop_nhds_zero_of_lt_one (inv_nonneg.mpr hq₀.le) (inv_lt_one_of_one_lt₀ hq)
    obtain ⟨n, hn⟩ := ((tendsto_order.mp ht).2 ρ hρ).exists
    refine ⟨n, fun u hu ↦ h u (hu.trans ?_)⟩
    rw [zpow_neg, zpow_natCast, ← inv_pow]
    exact hn.le
  have hfail : ∀ m : ℕ, ¬P m → ∃ u : (K F v)ˣ, ‖u.val - 1‖ ≤ q ^ (-(m : ℤ)) ∧ χ u ≠ 1 := by
    intro m hm
    dsimp [P] at hm
    push Not at hm
    exact hm
  have hP₀ : ¬P 0 := by
    intro h
    apply hχ
    intro u hu
    apply h u
    have hn : ‖u.val‖ = 1 := by simpa [finiteZetaShell] using
      (show u ∈ finiteZetaShell F v 0 from finiteZetaShell_zero F v ▸ hu)
    simpa only [Int.natCast_zero, neg_zero, zpow_zero, sub_eq_add_neg, norm_neg, norm_one, hn,
      max_self] using IsUltrametricDist.norm_add_le_max u.val (-1)
  let n := Nat.find hP
  have hn : n ≠ 0 := fun h ↦ hP₀ (h ▸ Nat.find_spec hP)
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hn
  refine ⟨n, Nat.pos_of_ne_zero hn, Nat.find_spec hP, ?_⟩
  by_cases hm₀ : m = 0
  · have hfailU : ∃ w : (K F v)ˣ, w ∈ U F v ∧ χ w ≠ 1 := by
      unfold finiteZetaUnramified at hχ
      push Not at hχ
      exact hχ
    obtain ⟨w, hw, hne⟩ := hfailU
    have hnorm : ‖w.val‖ = 1 := by simpa [finiteZetaShell] using
      (show w ∈ finiteZetaShell F v 0 from finiteZetaShell_zero F v ▸ hw)
    refine ⟨w, hnorm, ?_, hne⟩
    rw [hm, hm₀]
    simpa only [Nat.zero_add, Int.natCast_one, sub_self, zpow_zero, sub_eq_add_neg,
      norm_neg, norm_one, hnorm, max_self] using IsUltrametricDist.norm_add_le_max w.val (-1)
  · have hmn : m < n := by omega
    obtain ⟨u, hu, hne⟩ := hfail m (Nat.find_min hP hmn)
    have hsmall : ‖u.val - 1‖ < 1 := by
      apply hu.trans_lt
      rw [← zpow_zero q]
      exact zpow_lt_zpow_right₀ hq (by omega)
    refine ⟨u, le_antisymm ?_ ?_, ?_, hne⟩
    · have h := IsUltrametricDist.norm_add_le_max (u.val - 1) 1
      rwa [sub_add_cancel, norm_one, max_eq_right hsmall.le] at h
    · have h := IsUltrametricDist.norm_add_le_max u.val (-(u.val - 1))
      rw [show u.val + -(u.val - 1) = 1 by ring, norm_one, norm_neg, le_max_iff] at h
      exact h.resolve_right hsmall.not_ge
    · have he : (1 : ℤ) - n = -(m : ℤ) := by omega
      rwa [he]

/-- The inverse-phase test is invariant under the additive congruence ball. -/
theorem finiteGaussTest_add_period (χ : Phase F v) {ρ : ℝ} (hρ : ρ < 1)
    (hχ : ∀ u : (K F v)ˣ, ‖u.val - 1‖ ≤ ρ → χ u = 1)
    (t : K F v) (ht : ‖t‖ ≤ ρ) (x : K F v) :
    (finiteGaussTest F v χ).val (x + t) = (finiteGaussTest F v χ).val x := by
  have ht' := ht.trans_lt hρ
  have normShell (a b : K F v) (hb : ‖b‖ < 1) (ha : ‖a‖ = 1) : ‖a + b‖ = 1 := by
    refine le_antisymm ((IsUltrametricDist.norm_add_le_max a b).trans (by simp [ha, hb.le])) ?_
    have h := IsUltrametricDist.norm_add_le_max (a + b) (-b)
    rw [add_neg_cancel_right, ha, norm_neg, le_max_iff] at h
    exact h.resolve_right hb.not_ge
  have he : ‖x + t‖ = 1 ↔ ‖x‖ = 1 := by
    refine ⟨fun h ↦ ?_, normShell x t ht'⟩
    simpa only [add_neg_cancel_right] using normShell (x + t) (-t) (by simpa only [norm_neg] using ht') h
  have hz (a : K F v) (ha : ‖a‖ ≠ 1) : (finiteGaussTest F v χ).val a = 0 := by
    by_cases h : a = 0
    · simpa only [h] using finiteGaussTest_zero F v χ
    · have hz := finiteGaussTest_apply_units F v χ (Units.mk0 a h)
      change (finiteGaussTest F v χ).val a =
        (if ‖a‖ = 1 then (((χ (Units.mk0 a h))⁻¹ : Circle) : ℂ) else 0) at hz
      exact hz.trans (ite_eq_right ha)
  by_cases hx : ‖x‖ = 1
  · have hxt := he.mpr hx
    let a := Units.mk0 x (by intro h; simp [h] at hx)
    let b := Units.mk0 (x + t) (by intro h; simp [h] at hxt)
    have hab : ‖(a⁻¹ * b).val - 1‖ ≤ ρ := by
      have ha : x ≠ 0 := a.ne_zero
      change ‖(a⁻¹ * b).val - 1‖ ≤ _
      rw [Units.val_mul, Units.val_inv_eq_inv_val]
      change ‖x⁻¹ * (x + t) - 1‖ ≤ _
      rw [mul_add, inv_mul_cancel₀ ha, add_sub_cancel_left, norm_mul, norm_inv, hx, inv_one, one_mul]
      exact ht
    have h := hχ (a⁻¹ * b) hab
    rw [map_mul, map_inv, inv_mul_eq_iff_eq_mul, mul_one] at h
    change (finiteGaussTest F v χ).val b.val = (finiteGaussTest F v χ).val a.val
    rw [finiteGaussTest_apply_units, finiteGaussTest_apply_units, ite_eq_left (show ‖a.val‖ = 1 from hx),
      ite_eq_left (show ‖b.val‖ = 1 from hxt), h]
  · rw [hz (x + t) (fun h ↦ hx (he.mp h)), hz x hx]

section Fourier

variable [MeasurableSpace (K F v)] [BorelSpace (K F v)]
variable (ν : Measure (K F v)) [ν.IsAddHaarMeasure]

/-- Fourier transformation exchanges the inverse unit phase for the forward one. -/
theorem finiteGaussTest_fourier_dilate (χ : Phase F v) (u : (K F v)ˣ) (hu : ‖u.val‖ = 1)
    (y : K F v) :
    finitePlaceTraceFourier F v ν (finiteGaussTest F v χ).val (u.val * y) =
      (χ u : ℂ) * finitePlaceTraceFourier F v ν (finiteGaussTest F v χ).val y := by
  have h := finitePlaceTraceFourier_dilate F v ν u (finiteGaussTest F v χ).val y
  rw [funext (finiteGaussTest_dilate F v χ u hu), hu, one_smul] at h
  rw [← h]
  unfold finitePlaceTraceFourier
  simp_rw [mul_assoc]
  exact integral_const_mul _ _

/-- On a shell where the additive phase is unchanged by a ramified unit, the
Fourier transform of the Gauss test vanishes. -/
theorem finiteGaussTest_fourier_eq_zero_of_unit (χ : Phase F v) (u : (K F v)ˣ)
    (hu : ‖u.val‖ = 1) (hχ : χ u ≠ 1) (y : K F v)
    (hy : (u.val - 1) * y ∈ finitePlaceIntegerAnnihilator F v) :
    finitePlaceTraceFourier F v ν (finiteGaussTest F v χ).val y = 0 := by
  have h := finiteGaussTest_fourier_dilate F v ν χ u hu y
  have he : finitePlaceTraceFourier F v ν (finiteGaussTest F v χ).val (u.val * y) =
      finitePlaceTraceFourier F v ν (finiteGaussTest F v χ).val y := by
    unfold finitePlaceTraceFourier
    apply integral_congr_ae
    refine .of_forall fun x ↦ ?_
    by_cases hx : x = 0
    · simp [hx, finiteGaussTest_zero]
    let a := Units.mk0 x hx
    have ha : a.val = x := rfl
    by_cases hn : ‖x‖ = 1
    · have hi : x ∈ (v.adicCompletionIntegers F : Set (K F v)) := by
        rw [← finiteCompletion_closedBall]
        simp [Metric.mem_closedBall, hn]
      have hz := hy x hi
      apply congrArg (fun w : Additive Circle ↦ (finiteGaussTest F v χ).val x * (w.toMul : ℂ))
      rw [show x * (u.val * y) = x * y + x * ((u.val - 1) * y) by ring, map_add, hz, add_zero]
    · have hf : (finiteGaussTest F v χ).val x = 0 := by
        rw [← ha, finiteGaussTest_apply_units, ha, ite_eq_right hn]
      simp [hf]
  rw [he] at h
  have hh := (one_mul _).trans h
  exact (mul_eq_mul_right_iff.mp hh).resolve_left
    (fun heq ↦ hχ (Circle.coe_injective (heq.symm.trans Circle.coe_one.symm)))

/-- Above the dual congruence radius the exact Haar-normalized Fourier test
vanishes, by additive translation invariance. -/
theorem finiteGaussTest_fourier_eq_zero_of_outer (χ : Phase F v) (a : (K F v)ˣ)
    (ha : ‖a.val‖ < 1)
    (hχ : ∀ u : (K F v)ˣ, ‖u.val - 1‖ ≤ ‖a.val‖ → χ u = 1) (y : K F v)
    (hy : a.val * y ∉ finitePlaceIntegerAnnihilator F v) :
    finitePlaceTraceFourier F v ν (finiteGaussTest F v χ).val y = 0 := by
  change ¬ ∀ x ∈ (v.adicCompletionIntegers F : Set (K F v)),
    finitePlaceTraceCharacter F v (x * (a.val * y)) = 0 at hy
  push Not at hy
  obtain ⟨x, hx, hxy⟩ := hy
  have hx' : ‖x‖ ≤ 1 := by
    rw [← finiteCompletion_closedBall] at hx
    simpa using hx
  apply finitePlaceTraceFourier_eq_zero_of_period F v ν (a.val * x) y
  · apply finiteGaussTest_add_period F v χ ha hχ
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) hx'
  · simpa only [mul_assoc, mul_left_comm a.val x] using hxy

/-- The Fourier transform is supported on the single shell at the sum of
the different exponent and the positive multiplicative conductor exponent. -/
theorem finiteGaussTest_fourier_shell (χ : Phase F v) (hχ : ¬finiteZetaUnramified F v χ) :
    ∃ n : ℕ, 0 < n ∧ (∀ u : (K F v)ˣ,
      ‖u.val - 1‖ ≤ (v.asIdeal.absNorm : ℝ) ^ (-(n : ℤ)) → χ u = 1) ∧
      (∃ u : (K F v)ˣ, ‖u.val‖ = 1 ∧
        ‖u.val - 1‖ ≤ (v.asIdeal.absNorm : ℝ) ^ (1 - (n : ℤ)) ∧ χ u ≠ 1) ∧
      ∀ y : K F v, ‖y‖ ≠ (v.asIdeal.absNorm : ℝ) ^
          (multiplicity v.asIdeal (differentIdeal ℤ (𝓞 F)) + n) →
        finitePlaceTraceFourier F v ν (finiteGaussTest F v χ).val y = 0 := by
  let q := (v.asIdeal.absNorm : ℝ)
  let d := multiplicity v.asIdeal (differentIdeal ℤ (𝓞 F))
  have hq : 1 < q := by
    dsimp only [q]
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hq₀ := zero_lt_one.trans hq
  obtain ⟨n, hn, htriv, u, hu, hclose, hne⟩ := exists_finiteGaussTest_conductor F v χ hχ
  refine ⟨n, hn, htriv, ⟨u, hu, hclose, hne⟩, fun y hy ↦ ?_⟩
  have hadd : (u.val - 1) * y ∈ finitePlaceIntegerAnnihilator F v →
      finitePlaceTraceFourier F v ν (finiteGaussTest F v χ).val y = 0 :=
    finiteGaussTest_fourier_eq_zero_of_unit F v ν χ u hu hne y
  by_cases hy₀ : y = 0
  · apply hadd
    simp [hy₀, finitePlaceIntegerAnnihilator]
  let w := Units.mk0 y hy₀
  obtain ⟨m, hm⟩ := mem_iUnion.mp (show w ∈ ⋃ m : ℤ, finiteZetaShell F v m by
    rw [finiteZetaShell_iUnion]; exact mem_univ w)
  have hnorm : ‖y‖ = q ^ (-m) := hm
  have hy' : -m ≠ (d : ℤ) + (n : ℤ) := by
    intro he
    apply hy
    change ‖y‖ = q ^ (d + n)
    rw [hnorm, he, ← Int.natCast_add, zpow_natCast]
  rcases lt_or_gt_of_ne hy' with hlt | hgt
  · apply hadd
    rw [finitePlaceIntegerAnnihilator_eq_differentBall, mem_ofPred_eq, norm_mul, hnorm]
    change ‖u.val - 1‖ * q ^ (-m) ≤ q ^ d
    calc
      _ ≤ q ^ (1 - (n : ℤ)) * q ^ (-m) :=
        mul_le_mul_of_nonneg_right hclose (by positivity)
      _ ≤ q ^ d := by
        rw [← zpow_add₀ hq₀.ne', ← zpow_natCast]
        exact zpow_le_zpow_right₀ hq.le (by omega)
  · let a := chosenFiniteUniformizer F v ^ (n : ℤ)
    have ha : ‖a.val‖ = q ^ (-(n : ℤ)) := finitePlaceUniformizer_norm_zpow F v (n : ℤ)
    have ha₁ : ‖a.val‖ < 1 := by
      rw [ha, ← zpow_zero q]
      exact zpow_lt_zpow_right₀ hq (by omega)
    apply finiteGaussTest_fourier_eq_zero_of_outer F v ν χ a ha₁ (by simpa only [ha] using htriv)
    rw [finitePlaceIntegerAnnihilator_eq_differentBall, mem_ofPred_eq, norm_mul, ha, hnorm]
    change ¬ q ^ (-(n : ℤ)) * q ^ (-m) ≤ q ^ d
    rw [← zpow_add₀ hq₀.ne', ← zpow_natCast]
    exact (zpow_lt_zpow_right₀ hq (by omega)).not_ge

/-- Integrating the Fourier test against the inverse phase on a single shell
reduces to evaluation at the corresponding uniformizer power. -/
theorem finiteGaussTest_fourier_mellin_on_shell
    [MeasurableSpace (K F v)ˣ] [BorelSpace (K F v)ˣ]
    (μ : Measure (K F v)ˣ) [μ.IsHaarMeasure]
    (χ : Phase F v) (m : ℤ) (z : ℂ)
    (hs : ∀ g : (K F v)ˣ, g ∉ finiteZetaShell F v m →
      finitePlaceTraceFourier F v ν (finiteGaussTest F v χ).val g.val = 0) :
    finiteZetaIntegral F v μ χ⁻¹ (finitePlaceFourierTest F v ν (finiteGaussTest F v χ)) z =
      (μ.real (U F v) : ℂ) * (finiteZetaRatio F v χ⁻¹ z) ^ m *
        finitePlaceTraceFourier F v ν (finiteGaussTest F v χ).val
          ((chosenFiniteUniformizer F v ^ m : (K F v)ˣ) : K F v) := by
  let b := chosenFiniteUniformizer F v ^ m
  let T := finitePlaceTraceFourier F v ν (finiteGaussTest F v χ).val
  let C := (finiteZetaRatio F v χ⁻¹ z) ^ m * T b.val
  have he (g : (K F v)ˣ) : T g.val * (((χ⁻¹) g : Circle) : ℂ) * finiteZetaWeight F v z g =
      (finiteZetaShell F v m).indicator (fun _ ↦ C) g := by
    by_cases hg : g ∈ finiteZetaShell F v m
    · let u := b⁻¹ * g
      have hgu : b * u = g := mul_inv_cancel_left b g
      have hu : u ∈ U F v := by
        change u ∈ finitePlaceIntegralUnits F v
        rw [← finiteZetaShell_preimage F v _ (chosenFiniteUniformizer_spec F v) m]
        exact show b * u ∈ finiteZetaShell F v m from hgu ▸ hg
      have hun : ‖u.val‖ = 1 := by simpa [finiteZetaShell] using
        (show u ∈ finiteZetaShell F v 0 from finiteZetaShell_zero F v ▸ hu)
      have hT : T (b * u).val = (χ u : ℂ) * T b.val := by
        rw [Units.val_mul, mul_comm]
        exact finiteGaussTest_fourier_dilate F v ν χ u hun b.val
      rw [indicator_of_mem hg, ← hgu, hT]
      have htw := finiteZetaTwist_shell F v χ⁻¹ z m u hu
      change _ * _ * _ = C
      calc
        _ = ((χ u : ℂ) * T b.val) *
            ((((χ⁻¹) (b * u) : Circle) : ℂ) * finiteZetaWeight F v z (b * u)) := mul_assoc ..
        _ = ((χ u : ℂ) * (((χ u)⁻¹ : Circle) : ℂ)) * C := by
          rw [show (((χ⁻¹) (b * u) : Circle) : ℂ) * finiteZetaWeight F v z (b * u) =
            (finiteZetaRatio F v χ⁻¹ z) ^ m * (((χ u)⁻¹ : Circle) : ℂ) from htw]
          dsimp only [C]
          ring
        _ = C := by rw [← Circle.coe_mul, mul_inv_cancel, Circle.coe_one, one_mul]
    · rw [indicator_of_notMem hg, show T g.val = 0 from hs g hg, zero_mul, zero_mul]
  unfold finiteZetaIntegral
  change (∫ g, T g.val * (((χ⁻¹) g : Circle) : ℂ) * finiteZetaWeight F v z g ∂μ) = _
  simp_rw [he]
  rw [integral_indicator (finiteZetaShell_closed F v m).measurableSet, setIntegral_const,
    measureReal_def, finiteZetaShell_mass]
  simp [Complex.real_smul, C, T, b, mul_assoc, measureReal_def]

end Fourier

/-- In the unit shell, additive congruence balls represent cosets of the
multiplicative principal congruence subgroup. -/
theorem finiteGauss_mem_congruence_ball (x y : (K F v)ˣ) (hx : ‖x.val‖ = 1) (r : ℝ) :
    y.val ∈ Metric.closedBall x.val r ↔ ‖(x⁻¹ * y).val - 1‖ ≤ r := by
  rw [Metric.mem_closedBall, dist_eq_norm]
  have h : (x⁻¹ * y).val - 1 = x.val⁻¹ * (y.val - x.val) := by
    rw [Units.val_mul, Units.val_inv_eq_inv_val, mul_sub, inv_mul_cancel₀ x.ne_zero]
  rw [h, norm_mul, norm_inv, hx, inv_one, one_mul]

/-- The compact unit shell has a finite disjoint partition into closed balls
of a given positive congruence radius. -/
theorem exists_finiteGauss_representatives {ρ : ℝ} (hρ : 0 < ρ) (hρ₁ : ρ < 1) :
    ∃ R : Finset (K F v),
      (∀ c ∈ R, ‖c‖ = 1) ∧
      Set.Pairwise (R : Set (K F v)) (Disjoint on fun c ↦ Metric.closedBall c ρ) ∧
      {x : K F v | ‖x‖ = 1} = ⋃ c ∈ R, Metric.closedBall c ρ := by
  classical
  let S := unitSphere F v
  let B (c : K F v) := Metric.closedBall c ρ
  have hball (c : S) : B c.val ⊆ S := by
    intro x hx
    have hc := (mem_unitSphere F v c.val).mp c.property
    have ht : ‖x - c.val‖ < 1 := (Metric.mem_closedBall.mp hx).trans_lt hρ₁
    apply (mem_unitSphere F v x).mpr
    have ha := IsUltrametricDist.norm_add_le_max c.val (x - c.val)
    have hb := IsUltrametricDist.norm_add_le_max x (-(x - c.val))
    rw [show c.val + (x - c.val) = x by ring, hc, max_eq_left ht.le] at ha
    rw [show x + -(x - c.val) = c.val by ring, hc, norm_neg, le_max_iff] at hb
    exact le_antisymm ha (hb.resolve_right ht.not_ge)
  have hK : IsCompact S := by
    have hK : IsCompact (Metric.closedBall (0 : K F v) 1) := by
      rw [finiteCompletion_closedBall]
      exact finitePlaceIntegral_compact F v
    exact hK.diff Metric.isOpen_ball
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun c : S ↦ B c.val)
    (fun c ↦ IsUltrametricDist.isOpen_closedBall c.val hρ.ne')
    (fun x hx ↦ mem_iUnion.mpr ⟨⟨x, hx⟩, Metric.mem_closedBall_self hρ.le⟩)
  let cells := t.image (fun c : S ↦ B c.val)
  have hchoose (A : Set (K F v)) (hA : A ∈ cells) : ∃ c : S, B c.val = A := by
    obtain ⟨c, -, hc⟩ := Finset.mem_image.mp hA
    exact ⟨c, hc⟩
  let rep (A : {A // A ∈ cells}) : S := (hchoose A.val A.property).choose
  have hrep (A : {A // A ∈ cells}) : B (rep A).val = A.val := (hchoose A.val A.property).choose_spec
  let R := cells.attach.image (fun A ↦ (rep A).val)
  refine ⟨R, ?_, ?_, ?_⟩
  · intro c hc
    obtain ⟨A, -, rfl⟩ := Finset.mem_image.mp hc
    exact (mem_unitSphere F v _).mp (rep A).property
  · intro c hc e he hce
    rcases IsUltrametricDist.closedBall_eq_or_disjoint c e ρ with h | h
    · obtain ⟨A, -, rfl⟩ := Finset.mem_image.mp hc
      obtain ⟨D, -, rfl⟩ := Finset.mem_image.mp he
      exact (hce (congrArg (fun X ↦ (rep X).val) (Subtype.ext ((hrep A).symm.trans
        (h.trans (hrep D)))))).elim
    · exact h
  · have hS : {x : K F v | ‖x‖ = 1} = S := Set.ext fun x ↦ (mem_unitSphere F v x).symm
    rw [hS]
    refine Subset.antisymm ?_ ?_
    · intro x hx
      obtain ⟨c, hc, hxc⟩ := mem_iUnion₂.mp (ht hx)
      let A : {A // A ∈ cells} := ⟨B c.val, Finset.mem_image_of_mem _ hc⟩
      refine mem_iUnion₂.mpr ⟨(rep A).val, Finset.mem_image_of_mem _ (Finset.mem_attach _ _), ?_⟩
      change x ∈ B (rep A).val
      rw [hrep A]
      exact hxc
    · intro x hx
      obtain ⟨c, hc, hxc⟩ := mem_iUnion₂.mp hx
      obtain ⟨A, -, rfl⟩ := Finset.mem_image.mp hc
      exact hball (rep A) hxc

section Tamagawa

variable [∀ w : HeightOneSpectrum (𝓞 F), MeasurableSpace (w.adicCompletion F)]
  [∀ w : HeightOneSpectrum (𝓞 F), BorelSpace (w.adicCompletion F)]
  [MeasurableSpace (K F v)ˣ] [BorelSpace (K F v)ˣ]

local instance : (additiveHaarDifferent F v).IsAddHaarMeasure := additiveHaarDifferent_isHaar F v

/-- The additive Tamagawa Fourier coefficient of the canonical Gauss test. -/
def finiteGaussFourierCoefficient (χ : Phase F v) (n : ℕ) : ℂ :=
  let d := multiplicity v.asIdeal (differentIdeal ℤ (𝓞 F))
  finitePlaceTraceFourier F v (additiveHaarDifferent F v) (finiteGaussTest F v χ).val
    ((chosenFiniteUniformizer F v ^ (-((d : ℤ) + (n : ℤ))) : (K F v)ˣ) : K F v)

/-- On every ramified unitary component, the finite Tate multiplier equals the
reciprocal of the conductor-shell Fourier coefficient times the reflected
uniformizer power. The coefficient is nonzero. -/
theorem finiteGaussFourierCoefficient_tate_factor (μ : Measure (K F v)ˣ) [μ.IsHaarMeasure]
    (χ : Phase F v) (hχ : ¬finiteZetaUnramified F v χ)
    (ε : ℂ → ℂ) (hε : AnalyticOnNhd ℂ ε univ)
    (hFE : ∀ f : locallyConstantTests (K F v), finiteZetaContinuation F v μ χ f =
      fun z ↦ ε z * finiteZetaContinuation F v μ χ⁻¹
        (finitePlaceFourierTest F v (additiveHaarDifferent F v) f) (1 - z)) :
    ∃ n : ℕ, 0 < n ∧
      (∀ u : (K F v)ˣ, ‖u.val - 1‖ ≤ (v.asIdeal.absNorm : ℝ) ^ (-(n : ℤ)) → χ u = 1) ∧
      (∃ u : (K F v)ˣ, ‖u.val‖ = 1 ∧
        ‖u.val - 1‖ ≤ (v.asIdeal.absNorm : ℝ) ^ (1 - (n : ℤ)) ∧ χ u ≠ 1) ∧
      finiteGaussFourierCoefficient F v χ n ≠ 0 ∧
      ∀ z : ℂ, ε z = ((finiteZetaRatio F v χ⁻¹ (1 - z)) ^
        (-((multiplicity v.asIdeal (differentIdeal ℤ (𝓞 F)) : ℤ) + (n : ℤ))) *
        finiteGaussFourierCoefficient F v χ n)⁻¹ := by
  let ν := additiveHaarDifferent F v
  obtain ⟨n, hn, htriv, hprev, hsupport⟩ := finiteGaussTest_fourier_shell F v ν χ hχ
  let d := multiplicity v.asIdeal (differentIdeal ℤ (𝓞 F))
  let m : ℤ := -((d : ℤ) + (n : ℤ))
  let f := finiteGaussTest F v χ
  let M : ℂ := μ.real (U F v)
  let G := finiteGaussFourierCoefficient F v χ n
  let R (z : ℂ) := (finiteZetaRatio F v χ⁻¹ (1 - z)) ^ m
  have hM : M ≠ 0 := by
    dsimp only [M]
    exact_mod_cast (finiteZetaUnitMass_pos F v μ).ne'
  have hS (g : (K F v)ˣ) (hg : g ∉ finiteZetaShell F v m) :
      finitePlaceTraceFourier F v ν f.val g.val = 0 := by
    apply hsupport
    intro h
    apply hg
    change ‖g.val‖ = (v.asIdeal.absNorm : ℝ) ^ (-m)
    simpa only [m, neg_neg, ← Int.natCast_add, zpow_natCast] using h
  have hI (z : ℂ) (hz : z ∈ {z : ℂ | 0 < z.re ∧ z.re < 1}) : ε z * (R z * G) = 1 := by
    have h := congrFun (hFE f) z
    have hz' : 0 < (1 - z).re := by simpa using hz.2
    rw [← (finiteZetaContinuation_eq_integral F v μ χ f z hz.1).2,
      ← (finiteZetaContinuation_eq_integral F v μ χ⁻¹ _ (1 - z) hz').2,
      finiteGaussTest_mellin,
      finiteGaussTest_fourier_mellin_on_shell F v ν μ χ m (1 - z) hS] at h
    change M = ε z * (M * R z * G) at h
    apply mul_left_cancel₀ hM
    calc
      M * (ε z * (R z * G)) = ε z * (M * R z * G) := by ring
      _ = M * 1 := by rw [← h, mul_one]
  have hA : AnalyticOnNhd ℂ (fun z ↦ ε z * (R z * G)) univ := by
    intro z _
    have hz : AnalyticAt ℂ (fun w : ℂ ↦ 1 - w) z := analyticAt_const.sub analyticAt_id
    have hr := ((finiteZetaRatio_analytic F v χ⁻¹ (1 - z)).comp hz).zpow
      (finiteZetaRatio_ne_zero F v χ⁻¹ (1 - z)) (n := m)
    exact (hε z trivial).mul (hr.mul analyticAt_const)
  have hmid : (1 / 2 : ℂ) ∈ {z : ℂ | 0 < z.re ∧ z.re < 1} := by norm_num
  have hE : ∀ᶠ z in 𝓝 (1 / 2 : ℂ), ε z * (R z * G) = 1 := by
    have hopen : IsOpen {z : ℂ | 0 < z.re ∧ z.re < 1} :=
      (isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt Complex.continuous_re continuous_const)
    filter_upwards [hopen.mem_nhds hmid] with z hz using hI z hz
  have he := hA.eq_of_eventuallyEq (analyticOnNhd_const (v := (1 : ℂ))) hE
  have hG : G ≠ 0 := by
    intro h
    simpa only [h, mul_zero, zero_ne_one] using hI (1 / 2) hmid
  exact ⟨n, hn, htriv, hprev, hG, fun z ↦ eq_inv_of_mul_eq_one_left (congrFun he z)⟩

/-- The unit values in the sum are the conjugate multiplicative phase paired
with the positive trace character. -/
def finiteGaussSummand (χ : Phase F v) (n : ℕ) (x : K F v) : ℂ :=
  let d := multiplicity v.asIdeal (differentIdeal ℤ (𝓞 F))
  let b := chosenFiniteUniformizer F v ^ (-((d : ℤ) + (n : ℤ)))
  (finiteGaussTest F v χ).val x * ((finitePlaceTraceCharacter F v (x * b.val)).toMul : ℂ)

omit [∀ w : HeightOneSpectrum (𝓞 F), MeasurableSpace (w.adicCompletion F)]
  [∀ w : HeightOneSpectrum (𝓞 F), BorelSpace (w.adicCompletion F)]
  [MeasurableSpace (K F v)ˣ] [BorelSpace (K F v)ˣ] in
theorem finiteGaussSummand_apply_units (χ : Phase F v) (n : ℕ)
    (x : (K F v)ˣ) (hx : ‖x.val‖ = 1) :
    finiteGaussSummand F v χ n x.val =
      let d := multiplicity v.asIdeal (differentIdeal ℤ (𝓞 F))
      let b := chosenFiniteUniformizer F v ^ (-((d : ℤ) + (n : ℤ)))
      (((χ x)⁻¹ : Circle) : ℂ) * ((finitePlaceTraceCharacter F v (x.val * b.val)).toMul : ℂ) := by
  simp only [finiteGaussSummand, finiteGaussTest_apply_units, ite_eq_left hx]

omit [∀ w : HeightOneSpectrum (𝓞 F), MeasurableSpace (w.adicCompletion F)]
  [∀ w : HeightOneSpectrum (𝓞 F), BorelSpace (w.adicCompletion F)]
  [MeasurableSpace (K F v)ˣ] [BorelSpace (K F v)ˣ] in
private theorem finiteGaussSummand_off_shell (χ : Phase F v) (n : ℕ) {x : K F v}
    (hx : x ∉ unitSphere F v) : finiteGaussSummand F v χ n x = 0 := by
  unfold finiteGaussSummand
  by_cases h : x = 0
  · simp [h, finiteGaussTest_zero]
  · let u := Units.mk0 x h
    have hn : ‖u.val‖ ≠ 1 := fun he ↦ hx ((mem_unitSphere F v x).mpr he)
    change (finiteGaussTest F v χ).val u.val * _ = 0
    rw [finiteGaussTest_apply_units, ite_eq_right hn, zero_mul]

omit [MeasurableSpace (K F v)ˣ] [BorelSpace (K F v)ˣ] in
/-- The local Gauss coefficient is a finite sum with the correct additive
Tamagawa coset volume, for any choice of representatives. -/
theorem finiteGaussFourierCoefficient_eq_sum (χ : Phase F v) (n : ℕ) (hn : 0 < n)
    (hχ : ∀ u : (K F v)ˣ, ‖u.val - 1‖ ≤ (v.asIdeal.absNorm : ℝ) ^ (-(n : ℤ)) → χ u = 1)
    (R : Finset (K F v))
    (hdisj : Set.Pairwise (R : Set (K F v))
      (Disjoint on fun c ↦ Metric.closedBall c ((v.asIdeal.absNorm : ℝ) ^ (-(n : ℤ)))))
    (hcover : {x : K F v | ‖x‖ = 1} =
      ⋃ c ∈ R, Metric.closedBall c ((v.asIdeal.absNorm : ℝ) ^ (-(n : ℤ)))) :
    finiteGaussFourierCoefficient F v χ n =
      (((v.asIdeal.absNorm : ℝ) ^ (-(n : ℤ)) *
        (additiveHaarDifferent F v).real (v.adicCompletionIntegers F : Set (K F v)) : ℝ) : ℂ) *
        ∑ c ∈ R, finiteGaussSummand F v χ n c := by
  let q := (v.asIdeal.absNorm : ℝ)
  let ρ := q ^ (-(n : ℤ))
  let ν := additiveHaarDifferent F v
  let O := (v.adicCompletionIntegers F : Set (K F v))
  let d := multiplicity v.asIdeal (differentIdeal ℤ (𝓞 F))
  let b := chosenFiniteUniformizer F v ^ (-((d : ℤ) + (n : ℤ)))
  let a := chosenFiniteUniformizer F v ^ (n : ℤ)
  let B (c : K F v) := Metric.closedBall c ρ
  let g := finiteGaussSummand F v χ n
  have hq : 1 < q := by
    dsimp only [q]
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hq₀ := zero_lt_one.trans hq
  have hρ : ρ < 1 := by
    change q ^ (-(n : ℤ)) < 1
    rw [← zpow_zero q]
    exact zpow_lt_zpow_right₀ hq (by omega)
  have ha : ‖a.val‖ = ρ := finitePlaceUniformizer_norm_zpow F v (n : ℤ)
  have hb : ‖b.val‖ = q ^ ((d : ℤ) + (n : ℤ)) := by
    simpa only [neg_neg] using finitePlaceUniformizer_norm_zpow F v (-((d : ℤ) + (n : ℤ)))
  have hm (c : K F v) : ν.real (B c) = ρ * ν.real O := by
    have he : (fun x : K F v ↦ c + x) ⁻¹' B c = a • O := by
      rw [finitePlaceIntegral_dilate_eq_ball, ha]
      ext x
      change dist (c + x) c ≤ ρ ↔ ‖x‖ ≤ ρ
      rw [dist_eq_norm, add_sub_cancel_left]
    rw [measureReal_def, ← measure_preimage_add ν c (B c), he,
      show O = (v.adicCompletionIntegers F : Set (K F v)) from rfl,
      finitePlace_addHaar_smul, ENNReal.toReal_mul, ENNReal.coe_toReal, coe_nnnorm, ha, measureReal_def]
  have hconst (c x : K F v) (hx : x ∈ B c) : g x = g c := by
    have ht : ‖x - c‖ ≤ ρ := Metric.mem_closedBall.mp hx
    have hp := finiteGaussTest_add_period F v χ hρ hχ (x - c) ht c
    rw [show c + (x - c) = x by ring] at hp
    have hχ₀ : finitePlaceTraceCharacter F v ((x - c) * b.val) = 0 := by
      have hmem : (x - c) * b.val ∈ finitePlaceIntegerAnnihilator F v := by
        rw [finitePlaceIntegerAnnihilator_eq_differentBall, mem_ofPred_eq, norm_mul, hb]
        calc
          _ ≤ ρ * q ^ ((d : ℤ) + (n : ℤ)) :=
            mul_le_mul_of_nonneg_right ht (by positivity)
          _ = q ^ d := by
            change q ^ (-(n : ℤ)) * q ^ ((d : ℤ) + (n : ℤ)) = q ^ d
            rw [← zpow_add₀ hq₀.ne', ← zpow_natCast]
            congr 1
            omega
      simpa only [one_mul] using hmem 1 (Subring.one_mem _)
    change (finiteGaussTest F v χ).val x *
      ((finitePlaceTraceCharacter F v (x * b.val)).toMul : ℂ) =
      (finiteGaussTest F v χ).val c * ((finitePlaceTraceCharacter F v (c * b.val)).toMul : ℂ)
    rw [hp]
    apply congrArg (fun w : Additive Circle ↦ (finiteGaussTest F v χ).val c * (w.toMul : ℂ))
    rw [show x * b.val = c * b.val + (x - c) * b.val by ring, map_add, hχ₀, add_zero]
  have hg : Integrable g ν := finitePlace_integrable_mul_traceCharacter F v ν _ _
  have hS : unitSphere F v = ⋃ c ∈ R, B c := by
    rw [← hcover]
    exact Set.ext fun x ↦ mem_unitSphere F v x
  change (∫ x, g x ∂ν) = ((ρ * ν.real O : ℝ) : ℂ) * ∑ c ∈ R, g c
  calc
    _ = ∫ x in unitSphere F v, g x ∂ν :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero (fun _ hx ↦
        finiteGaussSummand_off_shell F v χ n hx)).symm
    _ = ∑ c ∈ R, ∫ x in B c, g x ∂ν := by
      rw [hS]
      exact integral_biUnion_finset R (fun _ _ ↦ Metric.isClosed_closedBall.measurableSet)
        hdisj (fun _ _ ↦ hg.integrableOn)
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c _
      rw [setIntegral_congr_fun Metric.isClosed_closedBall.measurableSet (hconst c),
        setIntegral_const, hm, Complex.real_smul]

omit [∀ w : HeightOneSpectrum (𝓞 F), MeasurableSpace (w.adicCompletion F)]
  [∀ w : HeightOneSpectrum (𝓞 F), BorelSpace (w.adicCompletion F)]
  [MeasurableSpace (K F v)ˣ] [BorelSpace (K F v)ˣ] in
/-- With a fixed finite phase, the ramified spectral power uses the sum of
the different and character conductor exponents. -/
theorem finiteGaussTateFactor_spectral_power
    (χ : Phase F v) (n : ℕ) (G : ℂ) (ε : ℂ → ℂ)
    (hε : ∀ z, ε z = ((finiteZetaRatio F v χ⁻¹ (1 - z)) ^
      (-((multiplicity v.asIdeal (differentIdeal ℤ (𝓞 F)) : ℤ) + (n : ℤ))) * G)⁻¹) (z : ℂ) :
    ε z = ε (1 / 2) * Complex.exp
      (((multiplicity v.asIdeal (differentIdeal ℤ (𝓞 F)) : ℂ) + (n : ℂ)) *
        (z - 1 / 2) * (Real.log (v.asIdeal.absNorm : ℝ) : ℂ)) := by
  let d := multiplicity v.asIdeal (differentIdeal ℤ (𝓞 F))
  let k : ℤ := (d : ℤ) + (n : ℤ)
  let L : ℂ := Real.log (v.asIdeal.absNorm : ℝ)
  let a : ℂ := ((χ⁻¹) (chosenFiniteUniformizer F v) : Circle)
  have h (w : ℂ) : ε w = G⁻¹ * (a ^ k * Complex.exp ((k : ℂ) * (-(1 - w) * L))) := by
    rw [hε w, mul_comm _ G, mul_inv, zpow_neg, inv_inv]
    change _ * (a * Complex.exp (-(1 - w) * L)) ^ k = _
    rw [mul_zpow, ← Complex.exp_int_mul]
  rw [h z, h (1 / 2)]
  change G⁻¹ * (a ^ k * Complex.exp ((k : ℂ) * (-(1 - z) * L))) =
    G⁻¹ * (a ^ k * Complex.exp ((k : ℂ) * (-(1 - (1 / 2 : ℂ)) * L))) *
      Complex.exp (((d : ℂ) + (n : ℂ)) * (z - 1 / 2) * L)
  have hk : (k : ℂ) = (d : ℂ) + (n : ℂ) := by simp [k]
  rw [← hk]
  have he : (k : ℂ) * (-(1 - z) * L) =
    (k : ℂ) * (-(1 - (1 / 2 : ℂ)) * L) + (k : ℂ) * (z - 1 / 2) * L := by ring
  rw [he, Complex.exp_add]
  ring

omit [∀ w : HeightOneSpectrum (𝓞 F), MeasurableSpace (w.adicCompletion F)]
  [∀ w : HeightOneSpectrum (𝓞 F), BorelSpace (w.adicCompletion F)]
  [MeasurableSpace (K F v)ˣ] [BorelSpace (K F v)ˣ] in
/-- A nonzero ramified Tate multiplier cannot have the spectral exponent of
(3.3.1.30), even allowing an arbitrary constant in front. -/
theorem finiteGaussTateFactor_not_different_only (n : ℕ) (hn : 0 < n) (ε : ℂ → ℂ)
    (hne : ε (1 / 2) ≠ 0)
    (hε : ∀ z, ε z = ε (1 / 2) * Complex.exp
      (((multiplicity v.asIdeal (differentIdeal ℤ (𝓞 F)) : ℂ) + (n : ℂ)) *
        (z - 1 / 2) * (Real.log (v.asIdeal.absNorm : ℝ) : ℂ))) :
    ¬ ∃ A : ℂ, ∀ z, ε z = A * Complex.exp
      ((multiplicity v.asIdeal (differentIdeal ℤ (𝓞 F)) : ℂ) *
        (z - 1 / 2) * (Real.log (v.asIdeal.absNorm : ℝ) : ℂ)) := by
  let d := multiplicity v.asIdeal (differentIdeal ℤ (𝓞 F))
  let L := Real.log (v.asIdeal.absNorm : ℝ)
  have hL : 0 < L := Real.log_pos (by exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v)
  rintro ⟨A, hA⟩
  have hmid : ε (1 / 2) = A := by simpa using hA (1 / 2)
  have h := (hA 1).symm.trans (hε 1)
  rw [← hmid] at h
  have he := mul_left_cancel₀ hne h
  have hnorm := congrArg norm he
  have he₁ : (d : ℂ) * ((1 : ℂ) - 1 / 2) * L = (((d : ℝ) * (1 / 2) * L : ℝ) : ℂ) := by
    push_cast
    ring
  have he₂ : ((d : ℂ) + (n : ℂ)) * ((1 : ℂ) - 1 / 2) * L =
      ((((d : ℝ) + (n : ℝ)) * (1 / 2) * L : ℝ) : ℂ) := by
    push_cast
    ring
  change ‖Complex.exp ((d : ℂ) * ((1 : ℂ) - 1 / 2) * L)‖ =
    ‖Complex.exp (((d : ℂ) + (n : ℂ)) * ((1 : ℂ) - 1 / 2) * L)‖ at hnorm
  rw [he₁, he₂, Complex.norm_exp, Complex.norm_exp, Complex.ofReal_re, Complex.ofReal_re] at hnorm
  have hh := Real.exp_injective hnorm
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hlt : (d : ℝ) * (1 / 2) * L < ((d : ℝ) + (n : ℝ)) * (1 / 2) * L := by
    gcongr
    linarith
  exact hlt.ne hh

/-- The ramified local multiplier in the S-local Tate product has the exact
finite Gauss-sum expression, with the Tamagawa volume of a conductor coset. -/
theorem IsFiniteTateMultiplier.ramified_gauss_sum
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    [∀ w : S, MeasurableSpace (w.val.adicCompletion F)ˣ]
    [∀ w : S, BorelSpace (w.val.adicCompletion F)ˣ]
    (μ : ∀ w : S, Measure (w.val.adicCompletion F)ˣ) [∀ w : S, (μ w).IsHaarMeasure]
    (χ : ∀ w : S, (w.val.adicCompletion F)ˣ →ₜ* Circle) (w : S) (ε : ℂ → ℂ)
    (hε : IsFiniteTateMultiplier F S μ χ w ε) (hχ : ¬finiteZetaUnramified F w.val (χ w)) :
    let q := (w.val.asIdeal.absNorm : ℝ)
    let d := multiplicity w.val.asIdeal (differentIdeal ℤ (𝓞 F))
    ∃ (n : ℕ) (R : Finset (K F w.val)), 0 < n ∧
      (∀ u : (K F w.val)ˣ, ‖u.val - 1‖ ≤ q ^ (-(n : ℤ)) → χ w u = 1) ∧
      (∃ u : (K F w.val)ˣ, ‖u.val‖ = 1 ∧
        ‖u.val - 1‖ ≤ q ^ (1 - (n : ℤ)) ∧ χ w u ≠ 1) ∧
      (∀ c ∈ R, ‖c‖ = 1) ∧
      Set.Pairwise (R : Set (K F w.val))
        (Disjoint on fun c ↦ Metric.closedBall c (q ^ (-(n : ℤ)))) ∧
      {x : K F w.val | ‖x‖ = 1} = ⋃ c ∈ R, Metric.closedBall c (q ^ (-(n : ℤ))) ∧
      (∀ z : ℂ, ε z = ((finiteZetaRatio F w.val (χ w)⁻¹ (1 - z)) ^ (-((d : ℤ) + (n : ℤ))) *
        (((q ^ (-(n : ℤ))) *
          (additiveHaarDifferent F w.val).real (w.val.adicCompletionIntegers F : Set (K F w.val)) : ℝ) : ℂ) *
        (∑ c ∈ R, finiteGaussSummand F w.val (χ w) n c))⁻¹) ∧
      (∀ z : ℂ, ε z = ε (1 / 2) * Complex.exp (((d : ℂ) + (n : ℂ)) *
        (z - 1 / 2) * (Real.log q : ℂ))) ∧
      ¬ (∃ A : ℂ, ∀ z, ε z = A * Complex.exp ((d : ℂ) * (z - 1 / 2) * (Real.log q : ℂ))) := by
  let q := (w.val.asIdeal.absNorm : ℝ)
  let d := multiplicity w.val.asIdeal (differentIdeal ℤ (𝓞 F))
  have hq : 1 < q := by
    dsimp only [q]
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm w.val
  have hχ' : ¬finiteZetaUnramified F w.val (χ w)⁻¹ := by
    intro h
    apply hχ
    intro u hu
    have he := h u hu
    change (χ w u)⁻¹ = 1 at he
    exact inv_eq_one.mp he
  have hFE (f : locallyConstantTests (K F w.val)) :
      finiteZetaContinuation F w.val (μ w) (χ w) f = fun z ↦ ε z *
        finiteZetaContinuation F w.val (μ w) (χ w)⁻¹
          (finitePlaceFourierTest F w.val (additiveHaarDifferent F w.val) f) (1 - z) := by
    funext z
    have he := hε.2.2.2.1 f z
    rw [finiteProductClearedLocal, ite_eq_right hχ, finiteProductClearedLocal,
      ite_eq_right hχ'] at he
    exact he
  obtain ⟨n, hn, htriv, hprev, -, hformula⟩ := finiteGaussFourierCoefficient_tate_factor
    F w.val (μ w) (χ w) hχ ε hε.1 hFE
  have hρ : 0 < q ^ (-(n : ℤ)) := zpow_pos (zero_lt_one.trans hq) _
  have hρ₁ : q ^ (-(n : ℤ)) < 1 := by
    rw [← zpow_zero q]
    exact zpow_lt_zpow_right₀ hq (by omega)
  obtain ⟨R, hR, hdisj, hcover⟩ := exists_finiteGauss_representatives F w.val hρ hρ₁
  have hpow := finiteGaussTateFactor_spectral_power F w.val (χ w) n _ ε hformula
  refine ⟨n, R, hn, htriv, hprev, hR, hdisj, hcover, fun z ↦ ?_, hpow,
    finiteGaussTateFactor_not_different_only F w.val n hn ε (hε.2.1 _) hpow⟩
  rw [hformula z, finiteGaussFourierCoefficient_eq_sum F w.val (χ w) n hn htriv R hdisj hcover]
  ring_nf

end Tamagawa

end

end Masullo
