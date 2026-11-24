import TranslationAverages
import NuclearTrace
import HilbertSchmidtKernels
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal Pointwise InnerProductSpace

namespace Masullo

noncomputable section

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
variable (μ : Measure G) [μ.IsMulLeftInvariant]
variable {U : ℕ → Set G}

omit [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [μ.IsMulLeftInvariant] in
private theorem translatedSquare_eq (x : G) (V : Set G) :
    (x, x) • (V ×ˢ V) = (x • V) ×ˢ (x • V) := by
  ext ⟨a, b⟩
  constructor
  · rintro ⟨⟨p, q⟩, ⟨hp, hq⟩, he⟩
    exact ⟨⟨p, hp, congrArg Prod.fst he⟩, ⟨q, hq, congrArg Prod.snd he⟩⟩
  · rintro ⟨⟨p, hp, rfl⟩, ⟨q, hq, rfl⟩⟩
    exact ⟨(p, q), ⟨hp, hq⟩, rfl⟩

omit [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [μ.IsMulLeftInvariant] in
private theorem enorm_translatedAverage_le_windowSup (hU : DoublingSequence μ U)
    (f : G → ℂ) (n : ℕ) (x : G) :
    ‖translatedAverage μ (U n) f x‖ₑ ≤ densityWindowSup μ U (fun y => ‖f y‖ₑ) x := by
  unfold translatedAverage densityWindowSup
  rw [enorm_smul, ← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (μ.real (U n))⁻¹),
    ENNReal.ofReal_inv_of_pos (by
      exact ENNReal.toReal_pos (hU.positive n).ne' (hU.finite n).ne), measureReal_def,
    ENNReal.ofReal_toReal (hU.finite n).ne]
  refine (mul_le_mul' le_rfl (enorm_integral_le_lintegral_enorm f)).trans ?_
  rw [mul_comm, ← div_eq_mul_inv, ← withDensity_apply _ ((hU.measurable n).const_smul x)]
  exact le_iSup (fun j => μ.withDensity (fun y => ‖f y‖ₑ) (x • U j) / μ (U j)) n

omit [Group G] [TopologicalSpace G] [T2Space G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [BorelSpace G] [μ.IsMulLeftInvariant] in
private theorem lintegral_enorm_sq_half (v : G → ℂ) :
    (∫⁻ x, ‖v x‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) = eLpNorm v 2 μ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)]
  norm_num

private theorem lintegral_windowSup_prod [IsFiniteMeasureOnCompacts μ]
    (hU : DoublingSequence μ U) (hU₀ : IsCompact (closure (U 0)))
    {C : ℝ≥0} (hC : 0 < C) (hDiff : ∀ k, μ (U k * (U k)⁻¹) < C * μ (U k))
    {f g : G → ℂ} (hf : Measurable f) (hg : Measurable g)
    (hfp : MemLp f 2 μ) (hgp : MemLp g 2 μ) :
    (∫⁻ x, densityWindowSup μ U (fun y => ‖f y‖ₑ) x *
      densityWindowSup μ U (fun y => ‖g y‖ₑ) x ∂μ) ≤
      8 * (C : ℝ≥0∞) * (eLpNorm f 2 μ * eLpNorm g 2 μ) := by
  let M (v : G → ℂ) := densityWindowSup μ U (fun y => ‖v y‖ₑ)
  have hM (v : G → ℂ) : Measurable (M v) := Measurable.iSup fun j =>
    measurable_translated_measure_div μ (μ.withDensity (fun y => ‖v y‖ₑ)) (hU.measurable j)
  have hroot {v : G → ℂ} (hv : Measurable v) (hvp : MemLp v 2 μ) :
      (∫⁻ x, M v x ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) ≤
        (8 * (C : ℝ≥0∞)) ^ (1 / 2 : ℝ) * eLpNorm v 2 μ := by
    have hfin : (∫⁻ x, ‖v x‖ₑ ^ (2 : ℝ) ∂μ) < ⊤ := by
      by_contra! h
      have ht : (∫⁻ x, ‖v x‖ₑ ^ (2 : ℝ) ∂μ) = ⊤ := top_le_iff.mp h
      have he := lintegral_enorm_sq_half μ v
      rw [ht, ENNReal.top_rpow_of_pos (by norm_num)] at he
      exact hvp.eLpNorm_lt_top.ne he.symm
    have hsq := densityWindowSup_sq μ hU hU₀ subset_closure hC hDiff hv.norm
      (fun _ => norm_nonneg _) (by
        simpa only [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, ENNReal.rpow_two] using hfin)
    simp only [ofReal_norm, ENNReal.ofReal_pow (norm_nonneg _)] at hsq
    rw [← lintegral_enorm_sq_half, ← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
    exact ENNReal.rpow_le_rpow (by simpa only [M, ENNReal.rpow_two] using hsq) (by norm_num)
  have hc : (2 : ℝ).HolderConjugate 2 := by
    rw [Real.holderConjugate_iff]
    norm_num
  calc
    _ ≤ (∫⁻ x, M f x ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) *
          (∫⁻ x, M g x ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) :=
      ENNReal.lintegral_mul_le_Lp_mul_Lq μ hc (hM f).aemeasurable (hM g).aemeasurable
    _ ≤ (((8 : ℝ≥0∞) * C) ^ (1 / 2 : ℝ) * eLpNorm f 2 μ) *
          (((8 : ℝ≥0∞) * C) ^ (1 / 2 : ℝ) * eLpNorm g 2 μ) :=
      mul_le_mul' (hroot hf hfp) (hroot hg hgp)
    _ = _ := by
      rw [mul_mul_mul_comm, ← ENNReal.rpow_add_of_nonneg (1 / 2) (1 / 2) (by norm_num) (by norm_num)]
      norm_num

private theorem ae_rankOneWindowMajorant_lt_top [IsFiniteMeasureOnCompacts μ]
    (hU : DoublingSequence μ U) (hU₀ : IsCompact (closure (U 0)))
    {C : ℝ≥0} (hC : 0 < C) (hDiff : ∀ k, μ (U k * (U k)⁻¹) < C * μ (U k))
    (u v : ℕ → G → ℂ) (hu : ∀ i, Measurable (u i)) (hv : ∀ i, Measurable (v i))
    (hu₂ : ∀ i, MemLp (u i) 2 μ) (hv₂ : ∀ i, MemLp (v i) 2 μ)
    (hmass : (∑' i, eLpNorm (u i) 2 μ * eLpNorm (v i) 2 μ) < ⊤) :
    ∀ᵐ x ∂μ, (∑' i, densityWindowSup μ U (fun y => ‖u i y‖ₑ) x *
      densityWindowSup μ U (fun y => ‖v i y‖ₑ) x) < ⊤ := by
  let M (f : G → ℂ) := densityWindowSup μ U (fun y => ‖f y‖ₑ)
  let majorant (i : ℕ) (x : G) := M (u i) x * M (v i) x
  have hM (f : G → ℂ) : Measurable (M f) := Measurable.iSup fun j =>
    measurable_translated_measure_div μ (μ.withDensity (fun y => ‖f y‖ₑ)) (hU.measurable j)
  have hmeas (i : ℕ) : Measurable (majorant i) := (hM _).mul (hM _)
  have hint : (∫⁻ x, ∑' i, majorant i x ∂μ) < ⊤ := by
    rw [lintegral_tsum (fun i => (hmeas i).aemeasurable)]
    refine (ENNReal.tsum_le_tsum fun i =>
      lintegral_windowSup_prod μ hU hU₀ hC hDiff (hu i) (hv i) (hu₂ i) (hv₂ i)).trans_lt ?_
    rw [ENNReal.tsum_mul_left]
    exact ENNReal.mul_lt_top (ENNReal.mul_lt_top (by norm_num) ENNReal.coe_lt_top) hmass
  exact ae_lt_top (Measurable.tsum hmeas) hint.ne

/-- The products of the averaged rank-one factors converge on the Haar diagonal. The
nuclear mass condition supplies a summable majorant uniform over all window sizes. -/
theorem translatedRankOneSeries_diagonal_ae [μ.Regular]
    (hU : DoublingSequence μ U) (hcof : CofinalAtOne U) (hU₀ : IsCompact (closure (U 0)))
    {C : ℝ≥0} (hC : 0 < C) (hDiff : ∀ k, μ (U k * (U k)⁻¹) < C * μ (U k))
    (u v : ℕ → G → ℂ) (hu : ∀ i, Measurable (u i)) (hv : ∀ i, Measurable (v i))
    (hu₂ : ∀ i, MemLp (u i) 2 μ) (hv₂ : ∀ i, MemLp (v i) 2 μ)
    (hmass : (∑' i, eLpNorm (u i) 2 μ * eLpNorm (v i) 2 μ) < ⊤) :
    ∀ᵐ x ∂μ, Tendsto
      (fun n => ∑' i, translatedAverage μ (U n) (u i) x *
        star (translatedAverage μ (U n) (v i) x)) atTop
      (𝓝 (∑' i, u i x * star (v i x))) := by
  let M (f : G → ℂ) := densityWindowSup μ U (fun y => ‖f y‖ₑ)
  let majorant (i : ℕ) (x : G) := M (u i) x * M (v i) x
  have hdiff (f : G → ℂ) (hf : MemLp f 2 μ) :
      ∀ᵐ x ∂μ, Tendsto (fun n => translatedAverage μ (U n) f x) atTop (𝓝 (f x)) :=
    (translatedAverage_ae_of_locallyIntegrable_of_isCompact_closure μ hU hcof hU₀ hC hDiff
      (hf.locallyIntegrable (by norm_num))).2
  filter_upwards [ae_rankOneWindowMajorant_lt_top μ hU hU₀ hC hDiff u v hu hv hu₂ hv₂ hmass,
    ae_all_iff.mpr (fun i => hdiff (u i) (hu₂ i)),
    ae_all_iff.mpr (fun i => hdiff (v i) (hv₂ i))] with x hsum hux hvx
  refine tendsto_tsum_of_dominated_convergence (ENNReal.summable_toReal hsum.ne)
    (fun i => (hux i).mul (hvx i).star) (Eventually.of_forall fun n i => ?_)
  have hi : majorant i x ≠ ⊤ :=
    ((ENNReal.le_tsum i).trans_lt hsum).ne
  have hb : ‖translatedAverage μ (U n) (u i) x *
      star (translatedAverage μ (U n) (v i) x)‖ₑ ≤ majorant i x := by
    rw [enorm_mul, ← ofReal_norm (star _), norm_star, ofReal_norm]
    exact mul_le_mul' (enorm_translatedAverage_le_windowSup μ hU (u i) n x)
      (enorm_translatedAverage_le_windowSup μ hU (v i) n x)
  exact (ENNReal.toReal_mono hi hb).trans_eq rfl

omit [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [BorelSpace G] in
private theorem translatedAverage_rankOneKernel (hU : DoublingSequence μ U)
    (u v : ℕ → G → ℂ) (hu : ∀ i, Measurable (u i)) (hv : ∀ i, Measurable (v i))
    (hmass : (∑' i, eLpNorm (u i) 2 μ * eLpNorm (v i) 2 μ) < ⊤)
    {k : G × G → ℂ} (hk : k =ᵐ[μ.prod μ] fun z => ∑' i, u i z.1 * star (v i z.2))
    [SFinite μ] (n : ℕ) (x : G) :
    translatedAverage (μ.prod μ) (U n ×ˢ U n) k (x, x) =
      ∑' i, translatedAverage μ (U n) (u i) x * star (translatedAverage μ (U n) (v i) x) := by
  let ν := μ.restrict (x • U n)
  let R (i : ℕ) (z : G × G) := u i z.1 * star (v i z.2)
  have hprod : (μ.prod μ).restrict ((x, x) • (U n ×ˢ U n)) = ν.prod ν := by
    rw [translatedSquare_eq, ← Measure.prod_restrict]
  have hmeas (i : ℕ) : Measurable (R i) :=
    ((hu i).comp measurable_fst).mul (continuous_star.measurable.comp ((hv i).comp measurable_snd))
  have hlocal (f : G → ℂ) (hf : Measurable f) :
      (∫⁻ y, ‖f y‖ₑ ∂ν) ≤ eLpNorm f 2 μ * μ (U n) ^ (1 / 2 : ℝ) := by
    rw [← eLpNorm_one_eq_lintegral_enorm]
    have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
      (μ := ν) (by norm_num : (1 : ℝ≥0∞) ≤ 2) hf.aestronglyMeasurable
    have hν : ν univ = μ (U n) := by
      rw [show ν = μ.restrict (x • U n) from rfl, Measure.restrict_apply_univ, measure_smul]
    refine h.trans ?_
    rw [hν, ENNReal.toReal_one, ENNReal.toReal_ofNat]
    have he : (1 / 1 - 1 / 2 : ℝ) = 1 / 2 := by norm_num
    rw [he]
    exact mul_le_mul' (eLpNorm_mono_measure f Measure.restrict_le_self) le_rfl
  have hsum : (∑' i, ∫⁻ z, ‖R i z‖ₑ ∂ν.prod ν) ≠ ⊤ := by
    have hind (i : ℕ) : (∫⁻ z, ‖R i z‖ₑ ∂ν.prod ν) ≤
        μ (U n) * (eLpNorm (u i) 2 μ * eLpNorm (v i) 2 μ) := by
      simp only [R, enorm_mul, ← ofReal_norm (star _), norm_star, ofReal_norm]
      rw [lintegral_prod_mul (hu i).enorm.aemeasurable (hv i).enorm.aemeasurable]
      refine (mul_le_mul' (hlocal (u i) (hu i)) (hlocal (v i) (hv i))).trans_eq ?_
      rw [mul_mul_mul_comm, ← ENNReal.rpow_add_of_nonneg (1 / 2) (1 / 2) (by norm_num) (by norm_num)]
      norm_num [mul_comm]
    apply ne_of_lt
    refine (ENNReal.tsum_le_tsum hind).trans_lt ?_
    rw [ENNReal.tsum_mul_left]
    exact ENNReal.mul_lt_top (hU.finite n) hmass
  have heq : ∫ z in (x, x) • (U n ×ˢ U n), k z ∂μ.prod μ =
      ∑' i, (∫ y, u i y ∂ν) * star (∫ y, v i y ∂ν) := by
    calc
      _ = ∫ z, ∑' i, R i z ∂ν.prod ν := by
        rw [← hprod]
        exact integral_congr_ae (ae_restrict_of_ae hk)
      _ = ∑' i, ∫ z, R i z ∂ν.prod ν :=
        integral_tsum (fun i => (hmeas i).aestronglyMeasurable) hsum
      _ = _ := by
        congr 1
        funext i
        change (∫ z, u i z.1 * (fun y => star (v i y)) z.2 ∂ν.prod ν) = _
        rw [integral_prod_mul (u i) (fun y => star (v i y))]
        exact congrArg ((∫ y, u i y ∂ν) * ·) integral_conj
  unfold translatedAverage
  rw [heq, measureReal_def, Measure.prod_prod, ENNReal.toReal_mul, mul_inv_rev]
  simp only [measureReal_def, RCLike.real_smul_eq_coe_mul, star_mul', Complex.star_def,
    map_mul, ← tsum_mul_left]
  congr 1
  funext i
  let c : ℝ := (μ (U n)).toReal⁻¹
  let a : ℂ := ∫ y, u i y ∂ν
  let b : ℂ := ∫ y, v i y ∂ν
  change (c : ℂ) * (c : ℂ) * (a * (starRingEnd ℂ) b) =
    ((c : ℂ) * a) * ((starRingEnd ℂ) (c : ℂ) * (starRingEnd ℂ) b)
  rw [Complex.conj_ofReal]
  ring

/-- The absolute means of a summable rank-one kernel over the double windows
are bounded uniformly in the window index at almost every center. -/
theorem rankOneKernel_enorm_windowBound [IsFiniteMeasureOnCompacts μ]
    (hU : DoublingSequence μ U) (hU₀ : IsCompact (closure (U 0)))
    {C : ℝ≥0} (hC : 0 < C) (hDiff : ∀ n, μ (U n * (U n)⁻¹) < C * μ (U n))
    (u v : ℕ → G → ℂ) (hu : ∀ i, Measurable (u i)) (hv : ∀ i, Measurable (v i))
    (hu₂ : ∀ i, MemLp (u i) 2 μ) (hv₂ : ∀ i, MemLp (v i) 2 μ)
    (hmass : (∑' i, eLpNorm (u i) 2 μ * eLpNorm (v i) 2 μ) < ⊤)
    {k : G × G → ℂ} (hk : k =ᵐ[μ.prod μ] fun z => ∑' i, u i z.1 * star (v i z.2)) :
    ∀ᵐ x ∂μ, ∃ B : ℝ≥0∞, B < ⊤ ∧ ∀ n,
      (∫⁻ z in (x, x) • (U n ×ˢ U n), ‖k z‖ₑ ∂μ.prod μ) / (μ (U n) * μ (U n)) ≤ B := by
  let M (f : G → ℂ) := densityWindowSup μ U (fun y => ‖f y‖ₑ)
  filter_upwards [ae_rankOneWindowMajorant_lt_top μ hU hU₀ hC hDiff u v hu hv hu₂ hv₂ hmass]
    with x hfinite
  refine ⟨∑' i, M (u i) x * M (v i) x, hfinite, fun n => ?_⟩
  let ν := μ.restrict (x • U n)
  let r (i : ℕ) (z : G × G) := u i z.1 * star (v i z.2)
  have hr (i : ℕ) : Measurable (r i) :=
    ((hu i).comp measurable_fst).mul (continuous_star.measurable.comp ((hv i).comp measurable_snd))
  have hprod : (μ.prod μ).restrict ((x, x) • (U n ×ˢ U n)) = ν.prod ν := by
    rw [translatedSquare_eq, ← Measure.prod_restrict]
  have hbound : (∫⁻ z in (x, x) • (U n ×ˢ U n), ‖k z‖ₑ ∂μ.prod μ) ≤
      ∑' i, ∫⁻ z, ‖r i z‖ₑ ∂ν.prod ν := by
    have hEq : k =ᵐ[ν.prod ν] fun z => ∑' i, r i z := hprod ▸ ae_restrict_of_ae hk
    have hEq' : (fun z => ‖k z‖ₑ) =ᵐ[ν.prod ν] fun z => ‖∑' i, r i z‖ₑ :=
      hEq.mono fun _ hz => congrArg enorm hz
    rw [hprod, lintegral_congr_ae hEq',
      ← lintegral_tsum (fun i => (hr i).enorm.aemeasurable)]
    exact lintegral_mono fun _ => enorm_tsum_le_tsum_enorm
  refine (ENNReal.div_le_div_right hbound _).trans ?_
  simp only [div_eq_mul_inv, ← ENNReal.tsum_mul_right]
  apply ENNReal.tsum_le_tsum
  intro i
  rw [← div_eq_mul_inv]
  simp only [r, enorm_mul, ← ofReal_norm (star _), norm_star, ofReal_norm]
  rw [lintegral_prod_mul (hu i).enorm.aemeasurable (hv i).enorm.aemeasurable,
    ENNReal.mul_div_mul_comm (.inl (hU.positive n).ne') (.inl (hU.finite n).ne)]
  have hi (f : G → ℂ) : (∫⁻ y, ‖f y‖ₑ ∂ν) / μ (U n) ≤ M f x := by
    rw [← withDensity_apply _ ((hU.measurable n).const_smul x)]
    exact le_iSup (fun j => μ.withDensity (fun y => ‖f y‖ₑ) (x • U j) / μ (U j)) n
  exact mul_le_mul' (hi (u i)) (hi (v i))

/-- Double-window smoothing of a Haar kernel represented by a nuclear rank-one series
recovers the diagonal series almost everywhere, for any product-a.e. representative. -/
theorem rankOneKernel_diagonal_ae [μ.Regular]
    (hU : DoublingSequence μ U) (hcof : CofinalAtOne U) (hU₀ : IsCompact (closure (U 0)))
    {C : ℝ≥0} (hC : 0 < C) (hDiff : ∀ k, μ (U k * (U k)⁻¹) < C * μ (U k))
    (u v : ℕ → G → ℂ) (hu : ∀ i, Measurable (u i)) (hv : ∀ i, Measurable (v i))
    (hu₂ : ∀ i, MemLp (u i) 2 μ) (hv₂ : ∀ i, MemLp (v i) 2 μ)
    (hmass : (∑' i, eLpNorm (u i) 2 μ * eLpNorm (v i) 2 μ) < ⊤)
    {k : G × G → ℂ} (hk : k =ᵐ[μ.prod μ] fun z => ∑' i, u i z.1 * star (v i z.2)) :
    ∀ᵐ x ∂μ, Tendsto (fun n =>
      translatedAverage (μ.prod μ) (U n ×ˢ U n) k (x, x)) atTop
      (𝓝 (∑' i, u i x * star (v i x))) := by
  filter_upwards [translatedRankOneSeries_diagonal_ae μ hU hcof hU₀ hC hDiff u v hu hv hu₂ hv₂ hmass]
    with x hx
  exact hx.congr fun n => (translatedAverage_rankOneKernel μ hU u v hu hv hmass hk n x).symm

/-- An absolutely summable family of rank-one factors in Haar L² defines a nuclear
operator. The integral of the smoothed diagonal equals its trace. -/
theorem rankOneKernel_diagonal_trace [μ.Regular]
    (hU : DoublingSequence μ U) (hcof : CofinalAtOne U) (hU₀ : IsCompact (closure (U 0)))
    {C : ℝ≥0} (hC : 0 < C) (hDiff : ∀ k, μ (U k * (U k)⁻¹) < C * μ (U k))
    (u v : ℕ → G → ℂ) (hu : ∀ i, Measurable (u i)) (hv : ∀ i, Measurable (v i))
    (hu₂ : ∀ i, MemLp (u i) 2 μ) (hv₂ : ∀ i, MemLp (v i) 2 μ)
    (hmass : (∑' i, eLpNorm (u i) 2 μ * eLpNorm (v i) 2 μ) < ⊤)
    {k : G × G → ℂ} (hk : k =ᵐ[μ.prod μ] fun z => ∑' i, u i z.1 * star (v i z.2)) :
    ∃ T : RankOneSeries ℕ (G →₂[μ] ℂ),
      T.image = (fun i => (hu₂ i).toLp (u i)) ∧
      T.functional = (fun i => (hv₂ i).toLp (v i)) ∧
      let d := regularizedLimit (fun n x =>
        translatedAverage (μ.prod μ) (U n ×ˢ U n) k (x, x))
      Integrable d μ ∧ (∫ x, d x ∂μ) = T.trace := by
  let w (i : ℕ) (x : G) := u i x * star (v i x)
  let d := regularizedLimit (fun n x =>
    translatedAverage (μ.prod μ) (U n ×ˢ U n) k (x, x))
  have hw (i : ℕ) : Measurable (w i) := (hu i).mul (continuous_star.measurable.comp (hv i))
  have hsum : (∑' i, ∫⁻ x, ‖w i x‖ₑ ∂μ) < ⊤ := by
    refine (ENNReal.tsum_le_tsum (fun i => ?_)).trans_lt hmass
    simp only [w, enorm_mul, ← ofReal_norm (star _), norm_star, ofReal_norm]
    rw [← lintegral_enorm_sq_half μ (u i), ← lintegral_enorm_sq_half μ (v i)]
    have hc : (2 : ℝ).HolderConjugate 2 := by
      rw [Real.holderConjugate_iff]
      norm_num
    exact ENNReal.lintegral_mul_le_Lp_mul_Lq μ hc
      (hu i).enorm.aemeasurable (hv i).enorm.aemeasurable
  have hd : d =ᵐ[μ] fun x => ∑' i, w i x := by
    filter_upwards [rankOneKernel_diagonal_ae μ hU hcof hU₀ hC hDiff u v hu hv hu₂ hv₂ hmass hk]
      with x hx
    exact regularizedLimit_tendsto hx
  let T : RankOneSeries ℕ (G →₂[μ] ℂ) :=
    { image := fun i => (hu₂ i).toLp (u i)
      functional := fun i => (hv₂ i).toLp (v i)
      summableNorm := by
        simpa only [ENNReal.toReal_mul, MeasureTheory.Lp.norm_toLp] using
          ENNReal.summable_toReal hmass.ne }
  refine ⟨T, rfl, rfl, (integrable_congr hd).mpr ⟨(Measurable.tsum hw).aestronglyMeasurable, ?_⟩, ?_⟩
  · apply hasFiniteIntegral_iff_enorm.mpr
    refine (lintegral_mono fun _ => enorm_tsum_le_tsum_enorm).trans_lt ?_
    rwa [lintegral_tsum fun i => (hw i).enorm.aemeasurable]
  · change (∫ x, d x ∂μ) = T.trace
    rw [integral_congr_ae hd, integral_tsum (fun i => (hw i).aestronglyMeasurable) hsum.ne,
      RankOneSeries.trace]
    apply tsum_congr
    intro i
    rw [MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(hu₂ i).coeFn_toLp, (hv₂ i).coeFn_toLp] with x hux hvx
    change w i x = ⟪(hv₂ i).toLp (v i) x, (hu₂ i).toLp (u i) x⟫_ℂ
    rw [hux, hvx, RCLike.inner_apply]
    rfl

omit [Group G] [TopologicalSpace G] [T2Space G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [BorelSpace G] [μ.IsMulLeftInvariant] in
/-- The actual L² kernel class of an absolutely summable rank-one presentation. -/
theorem RankOneSeries.exists_hilbertSchmidtKernel [SFinite μ]
    (T : RankOneSeries ℕ (G →₂[μ] ℂ)) :
    ∃ k : (G × G) →₂[μ.prod μ] ℂ,
      kernelIntegralOperator k = T.operator ∧
        k =ᵐ[μ.prod μ] fun z => ∑' i, T.image i z.1 * star (T.functional i z.2) := by
  let u (i : ℕ) : G → ℂ := T.image i
  let v (i : ℕ) : G → ℂ := T.functional i
  let h (i : ℕ) := memLp_rankOneKernel (Lp.memLp (T.image i)) (Lp.memLp (T.functional i))
  let K (i : ℕ) : (G × G) →₂[μ.prod μ] ℂ :=
    (h i).1.toLp (fun z => u i z.1 * star (v i z.2))
  have hterm (i : ℕ) : ‖K i‖ₑ = ‖T.image i‖ₑ * ‖T.functional i‖ₑ := by
    rw [Lp.enorm_def (T.image i), Lp.enorm_def (T.functional i)]
    exact (Lp.enorm_toLp (h i).1).trans (h i).2
  have hsum : (∑' i, ‖K i‖ₑ) ≠ ⊤ := by
    have hs := ENNReal.ofReal_tsum_of_nonneg
      (fun i => mul_nonneg (norm_nonneg (T.image i)) (norm_nonneg (T.functional i))) T.summableNorm
    simp only [ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm] at hs
    simp only [hterm, ← hs]
    exact ENNReal.ofReal_ne_top
  refine ⟨∑' i, K i, ?_, ?_⟩
  · change kernelIntegralOperatorCLM (∑' i, K i) = _
    rw [kernelIntegralOperatorCLM.map_tsum (Summable.of_enorm hsum), RankOneSeries.operator]
    apply tsum_congr
    intro i
    change kernelIntegralOperator (K i) = _
    rw [show kernelIntegralOperator (K i) =
      InnerProductSpace.rankOne ℂ ((Lp.memLp (T.image i)).toLp (u i))
        ((Lp.memLp (T.functional i)).toLp (v i)) from
      kernelIntegralOperator_rankOne (Lp.memLp (T.image i)) (Lp.memLp (T.functional i)),
      Lp.toLp_coeFn, Lp.toLp_coeFn]
  · filter_upwards [Lp.coeFn_tsum hsum, ae_all_iff.mpr (fun i => (h i).1.coeFn_toLp)] with z hz hz'
    exact hz.trans (tsum_congr fun i => hz' i)

omit [Group G] [TopologicalSpace G] [T2Space G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [BorelSpace G] [μ.IsMulLeftInvariant] in
theorem RankOneSeries.kernel_ae_eq [SFinite μ] [MeasureTheory.IsSeparable μ]
    (T : RankOneSeries ℕ (G →₂[μ] ℂ)) {k : G × G → ℂ} (hk : MemLp k 2 (μ.prod μ))
    (hoperator : kernelIntegralOperator (hk.toLp k) = T.operator) :
    k =ᵐ[μ.prod μ] fun z => ∑' i, T.image i z.1 * star (T.functional i z.2) := by
  obtain ⟨K, hK, hseries⟩ := T.exists_hilbertSchmidtKernel μ
  obtain ⟨s, hs, ⟨b⟩⟩ := exists_countable_hilbertBasis_L2 (ν := μ)
  letI : Countable s := hs.to_subtype
  have hEq : hk.toLp k = K := kernelIntegralOperator_injective b (hoperator.trans hK.symm)
  exact hk.coeFn_toLp.symm.trans (hEq ▸ hseries)

omit [Group G] [TopologicalSpace G] [T2Space G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [BorelSpace G] [μ.IsMulLeftInvariant] in
/-- The diagonal series of a nuclear presentation is integrable and computes the trace. -/
theorem RankOneSeries.diagonal_series_trace (T : RankOneSeries ℕ (G →₂[μ] ℂ)) :
    let d (x : G) := ∑' i, T.image i x * star (T.functional i x)
    Integrable d μ ∧ (∫ x, d x ∂μ) = T.trace := by
  let w (i : ℕ) (x : G) := T.image i x * star (T.functional i x)
  have hw (i : ℕ) : Measurable (w i) :=
    (Lp.stronglyMeasurable (T.image i)).measurable.mul
      (continuous_star.measurable.comp (Lp.stronglyMeasurable (T.functional i)).measurable)
  have hsum : (∑' i, ∫⁻ x, ‖w i x‖ₑ ∂μ) < ⊤ := by
    have hs := ENNReal.ofReal_tsum_of_nonneg
      (fun i => mul_nonneg (norm_nonneg (T.image i)) (norm_nonneg (T.functional i))) T.summableNorm
    simp only [ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm, Lp.enorm_def] at hs
    have hfinite : (∑' i, eLpNorm (T.image i) 2 μ * eLpNorm (T.functional i) 2 μ) < ⊤ := by
      rw [← hs]
      exact ENNReal.ofReal_lt_top
    refine (ENNReal.tsum_le_tsum fun i => ?_).trans_lt hfinite
    simp only [w, enorm_mul, ← ofReal_norm (star _), norm_star, ofReal_norm]
    rw [← lintegral_enorm_sq_half μ (T.image i), ← lintegral_enorm_sq_half μ (T.functional i)]
    exact ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two
      (Lp.aestronglyMeasurable (T.image i)).enorm (Lp.aestronglyMeasurable (T.functional i)).enorm
  refine ⟨?_, ?_⟩
  · refine ⟨(Measurable.tsum hw).aestronglyMeasurable, hasFiniteIntegral_iff_enorm.mpr ?_⟩
    refine (lintegral_mono fun _ => enorm_tsum_le_tsum_enorm).trans_lt ?_
    rwa [lintegral_tsum fun i => (hw i).enorm.aemeasurable]
  · rw [integral_tsum (fun i => (hw i).aestronglyMeasurable) hsum.ne, RankOneSeries.trace]
    apply tsum_congr
    intro i
    rw [MeasureTheory.L2.inner_def]
    exact integral_congr_ae (Eventually.of_forall fun x => by
      change w i x = ⟪T.functional i x, T.image i x⟫_ℂ
      rw [RCLike.inner_apply]
      rfl)

omit [Group G] [TopologicalSpace G] [T2Space G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [BorelSpace G] [μ.IsMulLeftInvariant] in
/-- On a separable L² space, the rank-one series gives a product-a.e. representative
whose diagonal is integrable and computes the trace. -/
theorem RankOneSeries.exists_diagonal_trace_representative [SFinite μ] [MeasureTheory.IsSeparable μ]
    (T : RankOneSeries ℕ (G →₂[μ] ℂ)) {k : G × G → ℂ} (hk : MemLp k 2 (μ.prod μ))
    (hoperator : kernelIntegralOperator (hk.toLp k) = T.operator) :
    ∃ smooth : G × G → ℂ, Measurable smooth ∧ smooth =ᵐ[μ.prod μ] k ∧
      Integrable (fun x => smooth (x, x)) μ ∧ (∫ x, smooth (x, x) ∂μ) = T.trace := by
  refine ⟨fun z => ∑' i, T.image i z.1 * star (T.functional i z.2), ?_,
    (T.kernel_ae_eq μ hk hoperator).symm, T.diagonal_series_trace μ⟩
  exact Measurable.tsum fun i =>
    ((Lp.stronglyMeasurable (T.image i)).measurable.comp measurable_fst).mul
      (continuous_star.measurable.comp
        ((Lp.stronglyMeasurable (T.functional i)).measurable.comp measurable_snd))

/-- The double-window averages of a nuclear kernel converge to its rank-one
diagonal series almost everywhere. -/
theorem RankOneSeries.kernel_diagonal_tendsto_series [μ.Regular]
    (T : RankOneSeries ℕ (G →₂[μ] ℂ))
    (hU : DoublingSequence μ U) (hcof : CofinalAtOne U) (hU₀ : IsCompact (closure (U 0)))
    {C : ℝ≥0} (hC : 0 < C) (hDiff : ∀ k, μ (U k * (U k)⁻¹) < C * μ (U k))
    {k : G × G → ℂ} (hk : MemLp k 2 (μ.prod μ))
    (hoperator : kernelIntegralOperator (hk.toLp k) = T.operator) :
    let a (n : ℕ) (x : G) := translatedAverage (μ.prod μ) (U n ×ˢ U n) k (x, x)
    ∀ᵐ x ∂μ, Tendsto (fun n => a n x) atTop
      (𝓝 (∑' i, T.image i x * star (T.functional i x))) := by
  have hk' : k =ᵐ[μ.prod μ] fun z => ∑' i, T.image i z.1 * star (T.functional i z.2) :=
    T.kernel_ae_eq μ hk hoperator
  have hmass : (∑' i, eLpNorm (T.image i) 2 μ * eLpNorm (T.functional i) 2 μ) < ⊤ := by
    have hs := ENNReal.ofReal_tsum_of_nonneg
      (fun i => mul_nonneg (norm_nonneg (T.image i)) (norm_nonneg (T.functional i))) T.summableNorm
    simp only [ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm, Lp.enorm_def] at hs
    rw [← hs]
    exact ENNReal.ofReal_lt_top
  have hmeas (f : G →₂[μ] ℂ) : Measurable f := (Lp.stronglyMeasurable f).measurable
  exact rankOneKernel_diagonal_ae μ hU hcof hU₀ hC hDiff
    (fun i => T.image i) (fun i => T.functional i)
    (fun i => hmeas _) (fun i => hmeas _) (fun i => Lp.memLp _) (fun i => Lp.memLp _) hmass hk'

/-- In the unweighted Haar setting the smoothed diagonal of any representative of the
actual nuclear integral operator is regular almost everywhere and integrates to its trace. -/
theorem RankOneSeries.kernel_diagonal_trace [μ.Regular]
    (T : RankOneSeries ℕ (G →₂[μ] ℂ))
    (hU : DoublingSequence μ U) (hcof : CofinalAtOne U) (hU₀ : IsCompact (closure (U 0)))
    {C : ℝ≥0} (hC : 0 < C) (hDiff : ∀ k, μ (U k * (U k)⁻¹) < C * μ (U k))
    {k : G × G → ℂ} (hk : MemLp k 2 (μ.prod μ))
    (hoperator : kernelIntegralOperator (hk.toLp k) = T.operator) :
    let a (n : ℕ) (x : G) := translatedAverage (μ.prod μ) (U n ×ˢ U n) k (x, x)
    (∀ᵐ x ∂μ, ∃ z, Tendsto (fun n => a n x) atTop (𝓝 z)) ∧
      Integrable (regularizedLimit a) μ ∧ (∫ x, regularizedLimit a x ∂μ) = T.trace := by
  let a (n : ℕ) (x : G) := translatedAverage (μ.prod μ) (U n ×ˢ U n) k (x, x)
  have ht := T.kernel_diagonal_tendsto_series μ hU hcof hU₀ hC hDiff hk hoperator
  have he : regularizedLimit a =ᵐ[μ] fun x => ∑' i, T.image i x * star (T.functional i x) :=
    ht.mono fun _ hx => regularizedLimit_tendsto hx
  exact ⟨ht.mono (fun _ hx => ⟨_, hx⟩), (T.diagonal_series_trace μ).1.congr he.symm,
    (integral_congr_ae he).trans (T.diagonal_series_trace μ).2⟩

end

end Masullo
