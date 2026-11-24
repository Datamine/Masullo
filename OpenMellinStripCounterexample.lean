import ModulatedMellinStripBounds
import ModulatedExponentialRadial
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

open Filter Function MeasureTheory Set Topology
open scoped ContDiff SchwartzMap

namespace Masullo

noncomputable section

private abbrev I := Ioo (0 : ℝ) 1
private abbrev E := PositiveRealExponentialDecay I
private theorem strip_nonempty : Set.Nonempty I := ⟨1 / 2, by norm_num⟩

private def shiftedGaussian (n : ℕ) : E :=
  let r : ℝ := (n : ℝ) + 2
  let g : E := ⟨fun x ↦ (Real.exp (-(x ^ 2)) : ℂ),
    gaussianLogProfile_mem_logExponentialDecaySubmodule I⟩
  ((r * Real.exp (-r) : ℝ) : ℂ) • logExponentialDecayTranslation I strip_nonempty (-r) g

private theorem shiftedGaussian_apply (n : ℕ) (x : ℝ) :
    (shiftedGaussian n).val x =
      (((n : ℝ) + 2) * Real.exp (-((n : ℝ) + 2)) : ℝ) *
        (Real.exp (-((x - ((n : ℝ) + 2)) ^ 2)) : ℂ) := rfl

private theorem seminorm_translate_le (g : 𝓢(ℝ, ℂ)) (r : ℝ) (hr : 0 ≤ r) (k j : ℕ) :
    SchwartzMap.seminorm ℂ k j (SchwartzMap.compSubConstCLM ℂ r g) ≤
      2 ^ (k - 1) * (SchwartzMap.seminorm ℂ k j g + r ^ k * SchwartzMap.seminorm ℂ 0 j g) := by
  apply SchwartzMap.seminorm_le_bound' ℂ _ _ _ (by positivity)
  intro x
  have hEq : ⇑(SchwartzMap.compSubConstCLM ℂ r g) = fun x : ℝ ↦ g (x + -r) := by
    funext y
    rw [SchwartzMap.compSubConstCLM_apply, sub_eq_add_neg]
  rw [hEq, iteratedDeriv_comp_add_const]
  change |x| ^ k * ‖iteratedDeriv j g (x - r)‖ ≤ _
  have hxx : |x| ≤ |x - r| + r := by
    have h := abs_add_le (x - r) r
    rwa [sub_add_cancel, abs_of_nonneg hr] at h
  have H₀ := g.le_seminorm' ℂ 0 j (x - r)
  rw [pow_zero, one_mul] at H₀
  calc
    _ ≤ ((|x - r| + r) ^ k) * ‖iteratedDeriv j g (x - r)‖ :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) hxx _) (norm_nonneg _)
    _ ≤ (2 ^ (k - 1) * (|x - r| ^ k + r ^ k)) * ‖iteratedDeriv j g (x - r)‖ :=
      mul_le_mul_of_nonneg_right (add_pow_le (abs_nonneg _) hr _) (norm_nonneg _)
    _ = 2 ^ (k - 1) *
        (|x - r| ^ k * ‖iteratedDeriv j g (x - r)‖ + r ^ k * ‖iteratedDeriv j g (x - r)‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (add_le_add (g.le_seminorm' ℂ k j (x - r)) (mul_le_mul_of_nonneg_left H₀ (by positivity)))
      (by positivity)

private theorem scaled_power_exp_tendsto {δ : ℝ} (hδ : 0 < δ) (k : ℕ) :
    Tendsto (fun r : ℝ ↦ r ^ k * Real.exp (-δ * r)) atTop (𝓝 0) := by
  have ht : Tendsto (fun r : ℝ ↦ δ * r) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos hδ).mpr tendsto_id
  have h := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero k).comp ht).const_mul (δ⁻¹ ^ k)
  convert h using 1
  · funext r
    simp only [Function.comp_apply, neg_mul, ← mul_assoc, ← mul_pow,
      inv_mul_cancel₀ hδ.ne', one_mul]
  · rw [mul_zero]

private theorem shiftedGaussian_tendsto : Tendsto shiftedGaussian atTop (𝓝 (0 : E)) := by
  apply (positiveRealExponentialDecay_isEmbedding I strip_nonempty).isInducing.tendsto_nhds_iff.mpr
  apply tendsto_pi_nhds.mpr
  intro a
  let g := logExponentialDecayTwist I a
    ⟨fun x ↦ (Real.exp (-(x ^ 2)) : ℂ), gaussianLogProfile_mem_logExponentialDecaySubmodule I⟩
  let δ := 1 - a.val
  have hδ : 0 < δ := sub_pos.mpr a.property.2
  have he (n : ℕ) :
      logExponentialDecayTwist I a (shiftedGaussian n) =
        (( (n : ℝ) + 2) * Real.exp (-δ * ((n : ℝ) + 2)) : ℝ) •
          SchwartzMap.compSubConstCLM ℂ ((n : ℝ) + 2) g := by
    apply SchwartzMap.ext
    intro x
    erw [logExponentialDecayTwist_apply, shiftedGaussian_apply]
    let r := (n : ℝ) + 2
    change (Real.exp (a.val * x) : ℂ) * (((r * Real.exp (-r) : ℝ) : ℂ) *
      (Real.exp (-((x - r) ^ 2)) : ℂ)) = _
    have hg : g (x - r) = (Real.exp (a.val * (x - r)) : ℂ) *
        (Real.exp (-((x - r) ^ 2)) : ℂ) :=
      logExponentialDecayTwist_apply I a _ (x - r)
    change _ = ((r * Real.exp (-δ * r) : ℝ) : ℂ) * g (x - r)
    rw [hg]
    have hprod : (Real.exp (a.val * x) : ℂ) * (Real.exp (-r) : ℂ) =
        (Real.exp (-δ * r) : ℂ) * (Real.exp (a.val * (x - r)) : ℂ) := by
      rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Real.exp_add, ← Real.exp_add]
      congr 2
      dsimp [δ]
      ring
    simp only [Complex.ofReal_mul]
    linear_combination (r : ℂ) * (Real.exp (-((x - r) ^ 2)) : ℂ) * hprod
  change Tendsto (fun n ↦ logExponentialDecayTwist I a (shiftedGaussian n)) atTop
    (𝓝 (logExponentialDecayTwist I a 0))
  rw [map_zero]
  apply (schwartz_withSeminorms ℂ ℝ ℂ).tendsto_nhds _ _ |>.mpr
  rintro ⟨k, j⟩ ε hε
  let r (n : ℕ) : ℝ := (n : ℝ) + 2
  have hr : Tendsto r atTop atTop := tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun n : ℕ ↦
      2 ^ (k - 1) * (SchwartzMap.seminorm ℂ k j g * (r n ^ 1 * Real.exp (-δ * r n)) +
        SchwartzMap.seminorm ℂ 0 j g * (r n ^ (k + 1) * Real.exp (-δ * r n)))) atTop (𝓝 0) := by
    have h1 := ((scaled_power_exp_tendsto hδ 1).comp hr).const_mul (SchwartzMap.seminorm ℂ k j g)
    have hk := ((scaled_power_exp_tendsto hδ (k + 1)).comp hr).const_mul (SchwartzMap.seminorm ℂ 0 j g)
    simpa only [Function.comp_apply, mul_zero, add_zero] using (h1.add hk).const_mul (2 ^ (k - 1) : ℝ)
  filter_upwards [hlim.eventually (Iio_mem_nhds hε)] with n hn
  rw [sub_zero, SchwartzMap.schwartzSeminormFamily_apply, he]
  change SchwartzMap.seminorm ℂ k j (((r n * Real.exp (-δ * r n) : ℝ) : ℂ) • _) < _
  rw [map_smul_eq_mul, Complex.norm_real]
  have hn₀ : 0 ≤ r n := by dsimp [r]; positivity
  change ‖r n * Real.exp (-δ * r n)‖ * _ < _
  rw [Real.norm_of_nonneg (by positivity)]
  refine (mul_le_mul_of_nonneg_left (seminorm_translate_le g (r n) hn₀ k j) (by positivity)).trans_lt ?_
  convert hn using 1
  rw [pow_one, pow_succ]
  ring

/-- Fourier–Mellin integral in logarithmic coordinates on the positive-real group. -/
def logarithmicLaplace (u : ℝ → ℂ) (s : ℂ) : ℂ :=
  ∫ x : ℝ, u x * Complex.exp (s * (x : ℂ))

private theorem shiftedGaussian_integral (n : ℕ) (s : ℂ) :
    logarithmicLaplace (shiftedGaussian n).val s =
      (((n : ℝ) + 2 : ℝ) : ℂ) * Complex.exp ((s - 1) * (((n : ℝ) + 2 : ℝ) : ℂ)) *
        ((↑Real.pi : ℂ) ^ (1 / 2 : ℂ) * Complex.exp (s ^ 2 / 4)) := by
  let r : ℝ := (n : ℝ) + 2
  unfold logarithmicLaplace
  rw [← integral_add_right_eq_self (fun x : ℝ ↦
    (shiftedGaussian n).val x * Complex.exp (s * (x : ℂ))) r]
  have he (x : ℝ) : (shiftedGaussian n).val (x + r) * Complex.exp (s * ((x + r : ℝ) : ℂ)) =
      ((r : ℂ) * Complex.exp ((s - 1) * (r : ℂ))) *
        Complex.exp ((-1 : ℂ) * (x : ℂ) ^ 2 + s * (x : ℂ) + 0) := by
    rw [shiftedGaussian_apply, show x + r - ((n : ℝ) + 2) = x by dsimp [r]; ring]
    change ((r * Real.exp (-r) : ℝ) : ℂ) * ((Real.exp (-(x ^ 2)) : ℝ) : ℂ) * _ = _
    push_cast
    rw [mul_assoc, mul_assoc, ← Complex.exp_add, ← Complex.exp_add]
    rw [mul_assoc, ← Complex.exp_add]
    congr 2
    ring
  simp_rw [he, integral_const_mul]
  rw [integral_cexp_quadratic (b := (-1 : ℂ)) (by norm_num)]
  change _ = (r : ℂ) * Complex.exp ((s - 1) * (r : ℂ)) *
      ((↑Real.pi : ℂ) ^ (1 / 2 : ℂ) * Complex.exp (s ^ 2 / 4))
  ring_nf

/-- The printed whole-open-strip estimate fails already for the logarithmic
derivative on the positive-real group. The counterexample family tends to zero
in the decay topology even though the symbol-times-transform is unbounded. -/
theorem openLogMellinStrip_counterexample :
    ∃ B : Set E, Bornology.IsVonNBounded ℂ B ∧
      ∀ M C : ℝ, 0 < M → 0 < C → ∃ u ∈ B, ∃ s : ℂ,
        s.re ∈ I ∧ M ≤ ‖s‖ ∧ C < ‖s * logarithmicLaplace u.val s‖ := by
  letI : IsTopologicalAddGroup E := (PolynormableSpace.withSeminorms ℂ E).topologicalAddGroup
  letI : ContinuousSMul ℂ E := (PolynormableSpace.withSeminorms ℂ E).continuousSMul
  refine ⟨range shiftedGaussian, shiftedGaussian_tendsto.isVonNBounded_range ℂ, fun M C hM hC ↦ ?_⟩
  let y := M + 1
  let K := y * ‖((↑Real.pi : ℂ) ^ (1 / 2 : ℂ))‖ * Real.exp (-1 - y ^ 2 / 4)
  have hy : 0 < y := by dsimp [y]; linarith
  have hK : 0 < K := by
    have hn : (↑Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
    have hp : ((↑Real.pi : ℂ) ^ (1 / 2 : ℂ)) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hn)
    exact mul_pos (mul_pos hy (norm_pos_iff.mpr hp)) (Real.exp_pos _)
  obtain ⟨n, hn⟩ := exists_nat_gt (C / K)
  let r : ℝ := (n : ℝ) + 2
  let a := 1 - 1 / r
  let s : ℂ := (a : ℂ) + (y : ℂ) * Complex.I
  have hr : 1 < r := by dsimp [r]; linarith [Nat.cast_nonneg (α := ℝ) n]
  have ha : a ∈ I := by
    constructor
    · exact sub_pos.mpr ((div_lt_iff₀ (zero_lt_one.trans hr)).mpr (by simpa))
    · exact sub_lt_self _ (one_div_pos.mpr (zero_lt_one.trans hr))
  have hs₁ : s.re = a := by simp [s]
  have hs₂ : s.im = y := by simp [s]
  have hsN : y ≤ ‖s‖ := by
    simpa only [hs₂, abs_of_nonneg hy.le] using Complex.abs_im_le_norm s
  refine ⟨shiftedGaussian n, mem_range_self _, s, hs₁ ▸ ha,
    (show M ≤ y by dsimp [y]; linarith).trans hsN, ?_⟩
  have harg : ((s - 1) * (r : ℂ)).re = -1 := by
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
      Complex.sub_re, Complex.one_re, hs₁]
    dsimp [a]
    field_simp
    ring
  have hsq : -y ^ 2 / 4 ≤ (s ^ 2 / 4).re := by
    have h : (s ^ 2 / 4).re = (a ^ 2 - y ^ 2) / 4 := by
      rw [Complex.div_ofNat_re, pow_two, Complex.mul_re, hs₁, hs₂]
      ring
    rw [h]
    nlinarith [sq_nonneg a]
  have hscale : C < r * K :=
    (div_lt_iff₀ hK).mp (hn.trans (by dsimp [r]; linarith))
  rw [shiftedGaussian_integral]
  change C < ‖s * ((r : ℂ) * Complex.exp ((s - 1) * (r : ℂ)) *
    ((↑Real.pi : ℂ) ^ (1 / 2 : ℂ) * Complex.exp (s ^ 2 / 4)))‖
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp, harg]
  rw [abs_of_nonneg (zero_le_one.trans hr.le)]
  have he := Real.exp_le_exp.mpr hsq
  refine hscale.trans_le ?_
  dsimp [K]
  rw [sub_eq_add_neg, Real.exp_add]
  have h := mul_le_mul hsN he (Real.exp_nonneg _) (norm_nonneg s)
  calc
    _ = (r * ‖((↑Real.pi : ℂ) ^ (1 / 2 : ℂ))‖ * Real.exp (-1)) *
        (y * Real.exp (-y ^ 2 / 4)) := by ring
    _ ≤ (r * ‖((↑Real.pi : ℂ) ^ (1 / 2 : ℂ))‖ * Real.exp (-1)) *
        (‖s‖ * Real.exp ((s ^ 2 / 4).re)) := mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by ring

private abbrev RadialGroup := Multiplicative ℝ
private abbrev radialModulus : RadialGroup →ₜ* Multiplicative ℝ := ContinuousMonoidHom.id _
private def radialUnitary (y : ℝ) : PontryaginDual RadialGroup := modulusCharacter radialModulus y

local instance : MeasurableSpace RadialGroup := borel _
local instance : BorelSpace RadialGroup := ⟨rfl⟩

private theorem radialQuasiCharacter (a y : ℝ) (x : RadialGroup) :
    modulatedExponentialWeight radialModulus a
      (fun x ↦ (radialUnitary y x : ℂ)) x =
      Complex.exp (((a : ℂ) + (y : ℂ) * Complex.I) * (x.toAdd : ℂ)) := by
  change (Real.exp (a * x.toAdd) : ℂ) * (Circle.exp (y * x.toAdd) : ℂ) = _
  rw [Complex.ofReal_exp, Circle.coe_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem radialDerivativeSymbol (a y : ℝ) :
    modulatedMellinSymbol radialModulus [(1, [radialModulus])] a (radialUnitary y) =
      (a : ℂ) + (y : ℂ) * Complex.I := by
  rw [modulatedMellinSymbol_eq_operator]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.foldr_cons,
    List.foldr_nil, one_mul, add_zero]
  unfold bruhatOrbitDeriv
  have hEq : (fun t : ℝ ↦ modulatedExponentialWeight radialModulus a
      (fun x ↦ (radialUnitary y x : ℂ)) (1 * radialModulus (Multiplicative.ofAdd t))) =
      fun t : ℝ ↦ Complex.exp (((a : ℂ) + (y : ℂ) * Complex.I) * (t : ℂ)) := by
    funext t
    rw [one_mul]
    exact radialQuasiCharacter a y (Multiplicative.ofAdd t)
  rw [hEq]
  let z := (a : ℂ) + (y : ℂ) * Complex.I
  have h : HasDerivAt (fun w : ℂ ↦ Complex.exp (z * w)) z 0 := by
    simpa only [id_eq, mul_one, mul_zero, Complex.exp_zero, one_mul] using
      ((hasDerivAt_id' (0 : ℂ)).const_mul z).cexp
  exact h.comp_ofReal.deriv

/-- Failure of the printed open-strip bound for the actual weighted
Schwartz–Bruhat space of the positive-real group, for any Haar normalization. -/
theorem modulatedMellin_openStrip_counterexample (μ : Measure RadialGroup) [μ.IsHaarMeasure] :
    ∃ B : Set (ModulatedExponentialInductive radialModulus I), Bornology.IsVonNBounded ℂ B ∧
      ∀ M C : ℝ, 0 < M → 0 < C → ∃ f ∈ B, ∃ a ∈ I, ∃ y : ℝ,
        let p := modulatedMellinSymbol radialModulus [(1, [radialModulus])] a
          (radialUnitary y)
        M ≤ ‖p‖ ∧ C < ‖p * modulatedMellinIntegral μ radialModulus f.val a
          (radialUnitary y)‖ := by
  have hm : IsProperMap radialModulus := isProperMap_id
  have hs : Surjective radialModulus := surjective_id
  obtain ⟨c, hc, hμ⟩ := exists_modulatedLog_pushforward_eq_smul radialModulus μ hm hs
  have hc₀ : 0 < (c : ℝ) := by exact_mod_cast pos_iff_ne_zero.mpr hc
  obtain ⟨e, he, _⟩ := exists_modulatedDecayRadialIsotype radialModulus radialModulus
    (fun _ ↦ rfl) 1 I strip_nonempty hm
  let L := (modulatedDecayIsotype radialModulus 1 I).subtypeL.comp e.toContinuousLinearMap
  have hL (u : E) (x : RadialGroup) : (L u).val x = u.val x.toAdd := by
    change ((e u).val).val x = _
    rw [he]
    have hχ : extendModulatedCharacter radialModulus radialModulus (fun _ ↦ rfl) 1 x = 1 := rfl
    erw [hχ, inv_one, Circle.coe_one, mul_one]
    rfl
  have hMellin (u : E) (a y : ℝ) :
      modulatedMellinIntegral μ radialModulus (L u).val a (radialUnitary y) =
      (c : ℝ) • logarithmicLaplace u.val ((a : ℂ) + (y : ℂ) * Complex.I) := by
    let s := (a : ℂ) + (y : ℂ) * Complex.I
    let F (t : ℝ) := u.val t * Complex.exp (s * (t : ℂ))
    have hC : Continuous u.val := by
      obtain ⟨g, hg⟩ := (Submodule.mem_iInf _).mp u.property (⟨1 / 2, by norm_num⟩ : I)
      have heq : u.val = logExponentialWeight (-(1 / 2)) g := by
        change u.val = logExponentialWeight (-(1 / 2)) (realSchwartzCoe g)
        change realSchwartzCoe g = logExponentialWeight (1 / 2) u.val at hg
        rw [hg]
        funext x
        change u.val x = (Real.exp (-(1 / 2) * x) : ℂ) *
          ((Real.exp ((1 / 2) * x) : ℂ) * u.val x)
        rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add, neg_mul, neg_add_cancel,
          Real.exp_zero, Complex.ofReal_one, one_mul]
      rw [heq]
      change Continuous (fun x : ℝ ↦ (Real.exp (-(1 / 2) * x) : ℂ) * g x)
      exact ((Complex.continuous_ofReal.comp (by fun_prop : Continuous fun x : ℝ ↦
        Real.exp (-(1 / 2) * x))).mul g.continuous)
    have hF : Continuous F := hC.mul (by fun_prop)
    calc
      _ = ∫ x, F (modulatedLog radialModulus x) ∂μ := by
        unfold modulatedMellinIntegral
        congr 1
        funext x
        change ((Real.exp (a * x.toAdd) : ℂ) * (L u).val x) *
          (radialUnitary y x : ℂ) = F x.toAdd
        rw [hL]
        calc
          _ = u.val x.toAdd * (modulatedExponentialWeight radialModulus a
            (fun x ↦ (radialUnitary y x : ℂ)) x) := by
              change _ = u.val x.toAdd * ((Real.exp (a * x.toAdd) : ℂ) * _)
              ring
          _ = _ := by rw [radialQuasiCharacter]
      _ = ∫ t, F t ∂Measure.map (modulatedLog radialModulus) μ :=
        (integral_map continuous_toAdd.measurable.aemeasurable hF.aestronglyMeasurable).symm
      _ = _ := by rw [hμ, integral_smul_nnreal_measure]; rfl
  obtain ⟨B, hB, hbad⟩ := openLogMellinStrip_counterexample
  refine ⟨L '' B, hB.image L, fun M C hM hC ↦ ?_⟩
  obtain ⟨u, hu, s, hs, hp, hv⟩ := hbad M (C / c) hM (div_pos hC hc₀)
  have heq : (s.re : ℂ) + (s.im : ℂ) * Complex.I = s := Complex.re_add_im s
  refine ⟨L u, ⟨u, hu, rfl⟩, s.re, hs, s.im, ?_⟩
  dsimp only
  rw [radialDerivativeSymbol, heq, hMellin, heq, Complex.real_smul]
  refine ⟨hp, ?_⟩
  rw [mul_left_comm, norm_mul, Complex.norm_real, Real.norm_of_nonneg hc₀.le]
  have h := (div_lt_iff₀ hc₀).mp hv
  simpa only [mul_comm (c : ℝ)] using h

end

end Masullo
