import ModulatedFrequencySobolev
import ModulatedBruhatStages
import ElementaryRadialSchwartz
import ModulatedSobolevConvolution
import PolynomialLpSeminorms

open Filter Function MeasureTheory Set Topology
open scoped ENNReal

namespace Masullo

noncomputable section

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
  (m : G →ₜ* Multiplicative ℝ)

private def logTailMajorant (t : ℝ) : ℝ := (1 + |t| ^ 2) ^ (-2 : ℝ)

private theorem logTailMajorant_continuous : Continuous logTailMajorant := by
  have h : Continuous (fun x : ℝ ↦ (1 : ℝ) + |x| ^ 2) := continuous_const.add (continuous_abs.pow 2)
  exact h.rpow_const (fun x => Or.inl (show 1 + |x| ^ 2 ≠ 0 by positivity))

private theorem logTailMajorant_nonneg (t : ℝ) : 0 ≤ logTailMajorant t :=
  Real.rpow_nonneg (by positivity) _

private theorem integrable_logTailMajorant (hm : IsProperMap m) (hms : Surjective m) :
    Integrable (fun g => logTailMajorant (modulatedLog m g)) μ := by
  obtain ⟨c, -, hc⟩ := exists_modulatedLog_pushforward_eq_smul m μ hm hms
  have hv : Integrable logTailMajorant (volume : Measure ℝ) := by
    have h := integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume) (r := 4) (by simp)
    apply h.congr
    refine .of_forall fun x => ?_
    norm_num [logTailMajorant, Real.norm_eq_abs]
  have hmap : Integrable logTailMajorant (Measure.map (modulatedLog m) μ) := by
    rw [hc]
    exact hv.smul_measure_nnreal
  exact hmap.comp_aemeasurable (continuous_toAdd.comp m.continuous).measurable.aemeasurable

private theorem exists_logTailMajorant_bound (s : ℝ) (hs : 0 ≤ s) :
    ∃ N : ℕ, ∀ t : ℝ, singletonSobolevKernelWeight 0 s t ≤
      (2 : ℝ) ^ (s / 2) * ((1 + t ^ 2) ^ N * logTailMajorant t) := by
  obtain ⟨N, hN⟩ := exists_nat_ge (s / 2 + 2)
  refine ⟨N, fun t => ?_⟩
  have hA : 1 ≤ 1 + t ^ 2 := le_add_of_nonneg_right (sq_nonneg t)
  have hAp : 0 < 1 + t ^ 2 := zero_lt_one.trans_le hA
  have ht : 1 + |t| ≤ 2 * (1 + t ^ 2) := by nlinarith [sq_nonneg (|t| - 1), sq_abs t, abs_nonneg t]
  have hpow := Real.rpow_le_rpow (show 0 ≤ 1 + |t| by positivity) ht
    (div_nonneg hs (by norm_num : (0 : ℝ) ≤ 2))
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hAp.le] at hpow
  simp only [singletonSobolevKernelWeight, zero_mul, Real.exp_zero, one_mul, logTailMajorant, sq_abs]
  rw [← Real.rpow_natCast, ← Real.rpow_add hAp]
  exact hpow.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hA (by linarith)) (by positivity))

/-- The realized stage inherits a continuous polynomially weighted
supremum bound in the logarithmic norm coordinate. -/
theorem exists_bruhatStage_logWeight_seminorm (P : BruhatSchwartzStage G) (N : ℕ) :
    ∃ q : Seminorm ℂ P.Space, Continuous q ∧ ∀ (f : P.Space) (g : G),
      (1 + (modulatedLog m g) ^ 2) ^ N * ‖P.realize f g‖ ≤ q f := by
  let A := ElementaryLCAModel P.2.realDim P.2.torusDim P.2.latticeRank P.2.finiteFactor
  let M := (P.1.descendHom m (P.1.modulation_eq_one_on_kernel m)).comp
    (P.2.equiv.symm : Multiplicative A →ₜ* P.1.StageQuotient)
  let l : A →+ ℝ := M.toMonoidHom.toAdditive
  have hl : Continuous l := continuous_toAdd.comp (M.continuous.comp continuous_ofAdd)
  have h := @exists_elementarySchwartz_logWeight_seminorm P.2.realDim P.2.torusDim P.2.latticeRank
    P.2.finiteFactor P.2.finiteGroup P.2.finiteTopology P.2.finiteDiscrete (Finite.of_fintype _) l hl N
  let p : Seminorm ℂ P.Space := h.choose
  have hp := h.choose_spec.1
  have hpv := h.choose_spec.2
  refine ⟨p, hp, fun f g => ?_⟩
  by_cases hg : g ∈ P.1.upper.val
  · let x : P.1.upper.val := ⟨g, hg⟩
    let y := (P.1.stageCoordinates P.2 x).toAdd
    have hy : l y = modulatedLog m g := by
      change ((P.1.descendHom m (P.1.modulation_eq_one_on_kernel m))
        (P.2.equiv.symm (P.2.equiv (QuotientGroup.mk x)))).toAdd = _
      rw [P.2.equiv.symm_apply_apply, LCAStructuralPair.descendHom_mk]
      rfl
    have hfy : P.realize f g = f y := P.1.realizeSchwartz_apply_of_mem P.2 f x
    exact (congrArg₂ (fun t z => (1 + t ^ 2) ^ N * ‖z‖) hy.symm hfy).trans_le (hpv f y)
  · have hz : P.realize f g = 0 := P.1.realizeSchwartz_apply_of_not_mem P.2 f g hg
    have he := congrArg (fun z : ℂ => (1 + (modulatedLog m g) ^ 2) ^ N * ‖z‖) hz
    have h0 : (1 + (modulatedLog m g) ^ 2) ^ N * ‖(0 : ℂ)‖ = 0 := by simp
    exact (he.trans h0).trans_le (apply_nonneg p f)

/-- A polynomial log weight of an actual Schwartz--Bruhat function belongs to Lᵖ. -/
theorem bruhatSchwartz_logPower_memLp (hm : IsProperMap m) (hms : Surjective m)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (n : ℕ) (f : BruhatSchwartz G) :
    MemLp (fun g ↦ ((|modulatedLog m g| : ℝ) : ℂ) ^ n * f.val g) p μ := by
  let w : G → ℝ := fun g ↦ logTailMajorant (modulatedLog m g)
  have hwi : Integrable w μ := integrable_logTailMajorant μ m hm hms
  have hw₀ g : 0 ≤ w g := logTailMajorant_nonneg _
  have hw₁ g : w g ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (le_add_of_nonneg_right (sq_nonneg _)) (by norm_num)
  have hw : MemLp w p μ := by
    by_cases hfin : p = ⊤
    · subst p
      exact memLp_top_of_bound hwi.aestronglyMeasurable 1
        (ae_of_all _ fun g => by simpa only [Real.norm_of_nonneg (hw₀ g)] using hw₁ g)
    apply (integrable_norm_rpow_iff hwi.aestronglyMeasurable (zero_lt_one.trans_le hp).ne'
      hfin).mp
    apply hwi.mono' (hwi.aestronglyMeasurable.norm.aemeasurable.pow_const _).aestronglyMeasurable
    refine ae_of_all _ fun g ↦ ?_
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _),
      Real.norm_of_nonneg (hw₀ g)]
    exact Real.rpow_le_self_of_le_one (hw₀ g) (hw₁ g)
      (by simpa using ENNReal.toReal_mono hfin hp)
  obtain ⟨P, u, hu⟩ := f.property
  obtain ⟨q, _, hq⟩ := exists_bruhatStage_logWeight_seminorm m P (n + 2)
  refine (hw.const_mul (q u)).mono' ?_ (ae_of_all _ fun g ↦ ?_)
  · have hlog : Continuous (modulatedLog m) := continuous_toAdd.comp m.continuous
    exact (((Complex.continuous_ofReal.comp hlog.abs).pow n).mul
      (bruhatSchwartz_continuous f)).aestronglyMeasurable
  let t := modulatedLog m g
  have hpos : 0 < 1 + t ^ 2 := by positivity
  have hbase : |t| ≤ 1 + t ^ 2 := by nlinarith [sq_nonneg (|t| - 1), sq_abs t]
  have he : (1 + t ^ 2) ^ (n + 2) * w g = (1 + t ^ 2) ^ n := by
    change (1 + t ^ 2) ^ (n + 2) * (1 + |t| ^ 2) ^ (-2 : ℝ) = _
    have hcast : ((n + 2 : ℕ) : ℝ) + (-2 : ℝ) = (n : ℝ) := by push_cast; ring
    rw [sq_abs, ← Real.rpow_natCast (1 + t ^ 2) (n + 2), ← Real.rpow_add hpos,
      hcast, Real.rpow_natCast]
  calc
    ‖((|t| : ℝ) : ℂ) ^ n * f.val g‖ = |t| ^ n * ‖f.val g‖ := by
      simp [norm_pow, Complex.norm_real, abs_abs, t]
    _ ≤ ((1 + t ^ 2) ^ n) * ‖f.val g‖ :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) hbase _) (norm_nonneg _)
    _ = ((1 + t ^ 2) ^ (n + 2) * ‖P.realize u g‖) * w g := by
      rw [← he, ← hu]
      ring
    _ ≤ q u * w g := mul_le_mul_of_nonneg_right (hq u g) (hw₀ g)

/-- The three weight families generate the same topology for Schwartz--Bruhat profiles,
including the derivative profiles on fixed stages of split idele classes. -/
theorem bruhatSchwartz_polynomialLpSeminorms {E I : Type*}
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (hm : IsProperMap m) (hms : Surjective m) {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (D : I → E →ₗ[ℂ] BruhatSchwartz G) :
    ∃ M U : SeminormFamily ℂ E (I × ℕ), ∃ P : SeminormFamily ℂ E (I × Polynomial ℂ),
      (∀ i n f, M (i, n) f = lpNorm
        (fun g ↦ ((|modulatedLog m g| : ℝ) : ℂ) ^ n * (D i f).val g) p μ) ∧
      (∀ i n f, U (i, n) f = lpNorm
        (fun g ↦ (1 + ((|modulatedLog m g| : ℝ) : ℂ) ^ n) * (D i f).val g) p μ) ∧
      (∀ i Q f, P (i, Q) f = lpNorm
        (fun g ↦ Q.eval ((|modulatedLog m g| : ℝ) : ℂ) * (D i f).val g) p μ) ∧
      (WithSeminorms M ↔ WithSeminorms U) ∧ (WithSeminorms M ↔ WithSeminorms P) :=
  polynomialLpSeminorms_same_topology (fun i ↦ bruhatSchwartzSubmodule.subtype.comp (D i))
    (fun g ↦ |modulatedLog m g|)
    (fun i n f ↦ bruhatSchwartz_logPower_memLp μ m hm hms Fact.out n (D i f))

set_option maxHeartbeats 1000000 in
/-- At each Bruhat stage a continuous Schwartz seminorm controls the
weighted L¹ norm required by the Sobolev convolution action. -/
theorem exists_bruhatStage_SobolevKernel_seminorm (hm : IsProperMap m) (hms : Surjective m)
    (s : ℝ) (hs : 0 ≤ s) (P : BruhatSchwartzStage G) :
    ∃ q : Seminorm ℂ P.Space, Continuous q ∧ ∀ f : P.Space,
      Integrable (fun g => ‖P.realize f g‖ * singletonSobolevKernelWeight 0 s (modulatedLog m g)) μ ∧
      (∫ g, ‖P.realize f g‖ * singletonSobolevKernelWeight 0 s (modulatedLog m g) ∂μ) ≤ q f := by
  let N := (exists_logTailMajorant_bound s hs).choose
  have hN := (exists_logTailMajorant_bound s hs).choose_spec
  have h := exists_bruhatStage_logWeight_seminorm m P N
  let p : Seminorm ℂ P.Space := h.choose
  have hp := h.choose_spec.1
  have hpv := h.choose_spec.2
  let W (g : G) := singletonSobolevKernelWeight 0 s (modulatedLog m g)
  let w (g : G) := ((2 : ℝ) ^ (s / 2)) * logTailMajorant (modulatedLog m g)
  have hw : Integrable w μ := (integrable_logTailMajorant μ m hm hms).const_mul _
  have hw₀ (g : G) : 0 ≤ w g := mul_nonneg (Real.rpow_nonneg (by norm_num) _) (logTailMajorant_nonneg _)
  let c : NNReal := ⟨∫ g, w g ∂μ, integral_nonneg hw₀⟩
  have hcp : Continuous (fun f : P.Space => (c : ℝ) * p f) := continuous_const.mul hp
  refine ⟨c • p, hcp, fun f => ?_⟩
  have hW (g : G) : 0 ≤ W g := by dsimp [W, singletonSobolevKernelWeight]; positivity
  have hWc : Continuous W := by
    have hL : Continuous (modulatedLog m) := continuous_toAdd.comp m.continuous
    have h := (continuous_const.add hL.abs : Continuous (fun g => (1 : ℝ) + |modulatedLog m g|))
    have hpow := h.rpow_const (p := s / 2) (fun g => Or.inl (show 1 + |modulatedLog m g| ≠ 0 by positivity))
    simpa [W, singletonSobolevKernelWeight] using hpow
  have hf : Continuous (P.realize f) := bruhatSchwartz_continuous (P.inclusion f)
  have hpt (g : G) : ‖P.realize f g‖ * W g ≤ p f * w g := by
    calc
      _ ≤ ‖P.realize f g‖ * ((2 : ℝ) ^ (s / 2) *
          ((1 + (modulatedLog m g) ^ 2) ^ N * logTailMajorant (modulatedLog m g))) :=
        mul_le_mul_of_nonneg_left (hN (modulatedLog m g)) (norm_nonneg _)
      _ = ((1 + (modulatedLog m g) ^ 2) ^ N * ‖P.realize f g‖) * w g := by dsimp [w]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (hpv f g) (hw₀ g)
  have hM : Integrable (fun g => ‖P.realize f g‖ * W g) μ :=
    (hw.const_mul (p f)).mono' (hf.norm.mul hWc).aestronglyMeasurable (.of_forall fun g => by
      change ‖‖P.realize f g‖ * W g‖ ≤ _
      rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (hW g))]
      exact hpt g)
  refine ⟨hM, (integral_mono hM (hw.const_mul (p f)) hpt).trans_eq ?_⟩
  rw [integral_const_mul]
  change p f * (∫ g, w g ∂μ) = (c : ℝ) * p f
  exact mul_comm _ _

/-- In the zero-line chart, every Schwartz–Bruhat kernel meets the exact
weighted integrability condition for integration of the translations. -/
theorem bruhatSchwartz_integrable_SobolevKernelWeight (hm : IsProperMap m) (hms : Surjective m)
    (s : ℝ) (hs : 0 ≤ s) (f : BruhatSchwartz G) :
    Integrable (fun g => ‖f.val g‖ * singletonSobolevKernelWeight 0 s (modulatedLog m g)) μ := by
  obtain ⟨P, z, hz⟩ := f.property
  rw [← hz]
  obtain ⟨q, _, hq⟩ := exists_bruhatStage_SobolevKernel_seminorm μ m hm hms s hs P
  exact (hq z).1

set_option maxHeartbeats 800000 in
/-- The zero-line convolution action is continuous from the final
Schwartz–Bruhat topology to the operator norm topology. -/
def bruhatSobolevZeroLineAction (hm : IsProperMap m) (hms : Surjective m)
    (s : ℝ) (hs : 0 ≤ s) : BruhatSchwartz G →L[ℂ] (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) := by
  let hB (f : BruhatSchwartz G) := bruhatSchwartz_integrable_SobolevKernelWeight μ m hm hms s hs f
  let T := hardySobolevMulTranslation μ m.toMonoidHom m.continuous 0 0 s hs
  let A (f : BruhatSchwartz G) := singletonSobolevConvolution μ m 0 s hs
    (bruhatSchwartz_continuous f).aestronglyMeasurable (hB f)
  let A₀ : BruhatSchwartz G →ₗ[ℂ] (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) :=
    { toFun := A
      map_add' := fun f g => by
        ext u : 1
        change (∫ x, (f.val x + g.val x) • T x u ∂μ) =
          (∫ x, f.val x • T x u ∂μ) + ∫ x, g.val x • T x u ∂μ
        simp_rw [add_smul]
        exact integral_add
          (integrable_singletonSobolev_kernel_eval μ m 0 s hs (bruhatSchwartz_continuous f).aestronglyMeasurable (hB f) u)
          (integrable_singletonSobolev_kernel_eval μ m 0 s hs (bruhatSchwartz_continuous g).aestronglyMeasurable (hB g) u)
      map_smul' := fun c f => by
        ext u : 1
        change (∫ x, (c • f.val x) • T x u ∂μ) = c • ∫ x, f.val x • T x u ∂μ
        simp_rw [smul_assoc, integral_smul] }
  refine ⟨A₀, (locallyConvexFinal_continuous_iff
    (fun P : BruhatSchwartzStage G => P.inclusion) A₀).mpr fun P => ?_⟩
  obtain ⟨q, hq, hqv⟩ := exists_bruhatStage_SobolevKernel_seminorm μ m hm hms s hs P
  let L := A₀.comp P.inclusion
  change Continuous L
  have hn : Continuous (fun f : P.Space => ‖L f‖) :=
    Seminorm.continuous_of_le (p := (normSeminorm ℂ _).comp L) hq
      (fun f => (singletonSobolevConvolution_opNorm_le μ m 0 s hs
        (bruhatSchwartz_continuous (P.inclusion f)).aestronglyMeasurable (hB (P.inclusion f))).trans (hqv f).2)
  refine continuous_of_tendsto_nhds_zero L.toAddMonoidHom ?_
  rw [Metric.tendsto_nhds]
  intro ε hε
  have ht := (hn.tendsto' 0 0 (by simp)).eventually (Iio_mem_nhds hε)
  filter_upwards [ht] with x hx
  change dist (L x) 0 < ε
  rw [dist_zero_right]
  exact hx

theorem bruhatSobolevZeroLineAction_apply (hm : IsProperMap m) (hms : Surjective m)
    (s : ℝ) (hs : 0 ≤ s) (f : BruhatSchwartz G) (u : Lp ℂ 2 μ) :
    bruhatSobolevZeroLineAction μ m hm hms s hs f u =
      ∫ g, f.val g • hardySobolevMulTranslation μ m.toMonoidHom m.continuous 0 0 s hs g u ∂μ := rfl

/-- In the topology obtained by twisting singleton-strip kernels to the
Schwartz–Bruhat space, the same continuous map integrates the translations
at the original abscissa. -/
theorem bruhatSobolevZeroLineAction_twisted_formula (hm : IsProperMap m) (hms : Surjective m)
    (b s : ℝ) (hs : 0 ≤ s) (f : BruhatSchwartz G) (u : Lp ℂ 2 μ) :
    bruhatSobolevZeroLineAction μ m hm hms s hs f u =
      ∫ g, (Real.exp (-(b * (m g).toAdd)) • f.val g) •
        hardySobolevMulTranslation μ m.toMonoidHom m.continuous b b s hs g u ∂μ := by
  rw [bruhatSobolevZeroLineAction_apply]
  apply integral_congr_ae
  refine .of_forall fun g => ?_
  change f.val g • hardySobolevMulTranslation μ m.toMonoidHom m.continuous 0 0 s hs g u =
    (Real.exp (-(b * (m g).toAdd)) • f.val g) •
      hardySobolevMulTranslation μ m.toMonoidHom m.continuous b b s hs g u
  rw [hardySobolevMulTranslation_singleton_eq_zeroLine μ m.toMonoidHom m.continuous b s hs g]
  let v := hardySobolevMulTranslation μ m.toMonoidHom m.continuous 0 0 s hs g u
  let a := b * (m g).toAdd
  change f.val g • v = (Real.exp (-a) • f.val g) • (Real.exp a • v)
  rw [smul_comm (Real.exp (-a) • f.val g) (Real.exp a), smul_assoc, smul_smul,
    ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_smul]

end

end Masullo
