import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
import Mathlib.Topology.DiscreteSubset

open Filter MeasureTheory Set
open scoped ENNReal InnerProductSpace Topology

namespace Masullo

noncomputable section

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y} [SFinite ν]

private theorem eLpNorm_two_eq (ρ : Measure X) (f : X → ℂ) :
    eLpNorm f 2 ρ = (∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂ρ) ^ (1 / 2 : ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)]
  norm_num

private theorem lintegral_enorm_sq (ρ : Measure X) (f : X → ℂ) :
    (∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂ρ) = eLpNorm f 2 ρ ^ (2 : ℝ) := by
  rw [eLpNorm_two_eq, ← ENNReal.rpow_mul]
  norm_num

/-- An L² kernel has square-integrable rows almost everywhere. -/
theorem memLp_kernelRows {k : X × Y → ℂ} (hk : MemLp k 2 (μ.prod ν)) :
    ∀ᵐ x ∂μ, MemLp (fun y => k (x, y)) 2 ν := by
  have hm := hk.aestronglyMeasurable.enorm.pow_const (2 : ℝ)
  have hfinite : (∫⁻ x, ∫⁻ y, ‖k (x, y)‖ₑ ^ (2 : ℝ) ∂ν ∂μ) < ⊤ := by
    rw [← lintegral_prod _ hm, lintegral_enorm_sq]
    exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hk.eLpNorm_lt_top.ne
  filter_upwards [hk.aestronglyMeasurable.prodMk_left, ae_lt_top' hm.lintegral_prod_right' hfinite.ne]
    with x hx hfin
  refine ⟨hx, ?_⟩
  rw [eLpNorm_two_eq]
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hfin.ne

private theorem integral_kernel_memLp {k : X × Y → ℂ} (hk : MemLp k 2 (μ.prod ν))
    {f : Y → ℂ} (hf : MemLp f 2 ν) :
    MemLp (fun x => ∫ y, k (x, y) * f y ∂ν) 2 μ ∧
      eLpNorm (fun x => ∫ y, k (x, y) * f y ∂ν) 2 μ ≤ eLpNorm k 2 (μ.prod ν) * eLpNorm f 2 ν := by
  have hmeas := (hk.aestronglyMeasurable.mul hf.aestronglyMeasurable.comp_snd).integral_prod_right'
  have hnorm (x : X) (hx : MemLp (fun y => k (x, y)) 2 ν) :
      ‖∫ y, k (x, y) * f y ∂ν‖ₑ ≤ eLpNorm (fun y => k (x, y)) 2 ν * eLpNorm f 2 ν := by
    refine (enorm_integral_le_lintegral_enorm _).trans ?_
    simp only [enorm_mul, eLpNorm_two_eq]
    exact ENNReal.lintegral_mul_le_Lp_mul_Lq ν Real.HolderConjugate.two_two
      hx.aestronglyMeasurable.enorm hf.aestronglyMeasurable.enorm
  have hbound : eLpNorm (fun x => ∫ y, k (x, y) * f y ∂ν) 2 μ ≤
      eLpNorm k 2 (μ.prod ν) * eLpNorm f 2 ν := by
    rw [← ENNReal.rpow_le_rpow_iff (by norm_num : (0 : ℝ) < 2),
      ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← lintegral_enorm_sq, ← lintegral_enorm_sq]
    rw [lintegral_prod _ (hk.aestronglyMeasurable.enorm.pow_const (2 : ℝ)),
      ← lintegral_mul_const'' _ (hk.aestronglyMeasurable.enorm.pow_const (2 : ℝ)).lintegral_prod_right']
    apply lintegral_mono_ae
    filter_upwards [memLp_kernelRows hk] with x hx
    rw [lintegral_enorm_sq, ← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
    exact ENNReal.rpow_le_rpow (hnorm x hx) (by norm_num)
  exact ⟨⟨hmeas, hbound.trans_lt (ENNReal.mul_lt_top hk.eLpNorm_lt_top hf.eLpNorm_lt_top)⟩, hbound⟩

private def kernelIntegralFun (k : (X × Y) →₂[μ.prod ν] ℂ) (f : Y →₂[ν] ℂ) : X →₂[μ] ℂ :=
  (integral_kernel_memLp (Lp.memLp k) (Lp.memLp f)).1.toLp _

private theorem kernelIntegralFun_ae (k : (X × Y) →₂[μ.prod ν] ℂ) (f : Y →₂[ν] ℂ) :
    ∀ᵐ x ∂μ, kernelIntegralFun k f x = ∫ y, k (x, y) * f y ∂ν :=
  MemLp.coeFn_toLp _

/-- A square-integrable kernel acts on L² by integrating over the source variable. -/
def kernelIntegralOperator (k : (X × Y) →₂[μ.prod ν] ℂ) : (Y →₂[ν] ℂ) →L[ℂ] (X →₂[μ] ℂ) :=
  LinearMap.mkContinuous
    { toFun := kernelIntegralFun k
      map_add' := fun f g => by
        apply Lp.ext
        filter_upwards [kernelIntegralFun_ae k (f + g), kernelIntegralFun_ae k f,
          kernelIntegralFun_ae k g, Lp.coeFn_add (kernelIntegralFun k f) (kernelIntegralFun k g),
          memLp_kernelRows (Lp.memLp k)] with x hfg hf hg hadd hx
        rw [hfg, hadd, Pi.add_apply, hf, hg]
        have hfint : Integrable (fun y => k (x, y) * f y) ν :=
          memLp_one_iff_integrable.mp ((Lp.memLp f).mul' hx)
        have hgint : Integrable (fun y => k (x, y) * g y) ν :=
          memLp_one_iff_integrable.mp ((Lp.memLp g).mul' hx)
        rw [← integral_add hfint hgint]
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_add f g] with y hy
        rw [hy, Pi.add_apply, mul_add]
      map_smul' := fun c f => by
        apply Lp.ext
        filter_upwards [kernelIntegralFun_ae k (c • f), kernelIntegralFun_ae k f,
          Lp.coeFn_smul c (kernelIntegralFun k f)] with x hcf hf hsmul
        change kernelIntegralFun k (c • f) x = (c • kernelIntegralFun k f) x
        rw [hcf, hsmul, Pi.smul_apply, hf, ← integral_smul]
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_smul c f] with y hy
        rw [hy, Pi.smul_apply, mul_smul_comm] }
    ‖k‖ (fun f => by
      change ‖kernelIntegralFun k f‖ ≤ ‖k‖ * ‖f‖
      rw [kernelIntegralFun, Lp.norm_toLp, Lp.norm_def, Lp.norm_def, ← ENNReal.toReal_mul]
      exact ENNReal.toReal_mono (ENNReal.mul_lt_top (Lp.memLp k).eLpNorm_lt_top
        (Lp.memLp f).eLpNorm_lt_top).ne (integral_kernel_memLp (Lp.memLp k) (Lp.memLp f)).2)

theorem kernelIntegralOperator_apply (k : (X × Y) →₂[μ.prod ν] ℂ) (f : Y →₂[ν] ℂ) :
    ∀ᵐ x ∂μ, Integrable (fun y => k (x, y) * f y) ν ∧
      kernelIntegralOperator k f x = ∫ y, k (x, y) * f y ∂ν := by
  filter_upwards [memLp_kernelRows (Lp.memLp k), kernelIntegralFun_ae k f] with x hx he
  refine ⟨memLp_one_iff_integrable.mp ((Lp.memLp f).mul' hx), ?_⟩
  change kernelIntegralFun k f x = _
  exact he

theorem kernelIntegralOperator_apply_of_memLp {k : X × Y → ℂ}
    (hk : MemLp k 2 (μ.prod ν)) (f : Y →₂[ν] ℂ) :
    ∀ᵐ x ∂μ, Integrable (fun y => k (x, y) * f y) ν ∧
      kernelIntegralOperator (hk.toLp k) f x = ∫ y, k (x, y) * f y ∂ν := by
  filter_upwards [kernelIntegralOperator_apply (hk.toLp k) f,
    Measure.ae_ae_of_ae_prod hk.coeFn_toLp] with x hx hrow
  have he : (fun y => hk.toLp k (x, y) * f y) =ᵐ[ν] (fun y => k (x, y) * f y) :=
    hrow.mono fun y hy => congrArg (· * f y) hy
  exact ⟨hx.1.congr he, hx.2.trans (integral_congr_ae he)⟩

/-- Integration against the kernel depends continuously and linearly on its L² class. -/
def kernelIntegralOperatorCLM :
    ((X × Y) →₂[μ.prod ν] ℂ) →L[ℂ] ((Y →₂[ν] ℂ) →L[ℂ] (X →₂[μ] ℂ)) :=
  LinearMap.mkContinuous
    { toFun := kernelIntegralOperator
      map_add' := fun k l => by
        ext f : 1
        apply Lp.ext
        filter_upwards [kernelIntegralOperator_apply (k + l) f,
          kernelIntegralOperator_apply k f, kernelIntegralOperator_apply l f,
          Lp.coeFn_add (kernelIntegralOperator k f) (kernelIntegralOperator l f),
          Measure.ae_ae_of_ae_prod (Lp.coeFn_add k l)] with x hkl hk hl hadd hrow
        change kernelIntegralOperator (k + l) f x =
          (kernelIntegralOperator k f + kernelIntegralOperator l f) x
        rw [hkl.2, hadd, Pi.add_apply, hk.2, hl.2, ← integral_add hk.1 hl.1]
        apply integral_congr_ae
        filter_upwards [hrow] with y hy
        rw [hy, Pi.add_apply, add_mul]
      map_smul' := fun c k => by
        ext f : 1
        apply Lp.ext
        filter_upwards [kernelIntegralOperator_apply (c • k) f, kernelIntegralOperator_apply k f,
          Lp.coeFn_smul c (kernelIntegralOperator k f),
          Measure.ae_ae_of_ae_prod (Lp.coeFn_smul c k)] with x hck hk hc hrow
        change kernelIntegralOperator (c • k) f x = (c • kernelIntegralOperator k f) x
        rw [hck.2, hc, Pi.smul_apply, hk.2, ← integral_smul]
        apply integral_congr_ae
        filter_upwards [hrow] with y hy
        rw [hy, Pi.smul_apply, smul_mul_assoc] }
    1 (fun k => by
      change ‖kernelIntegralOperator k‖ ≤ 1 * ‖k‖
      rw [one_mul]
      apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
      intro f
      change ‖kernelIntegralFun k f‖ ≤ ‖k‖ * ‖f‖
      rw [kernelIntegralFun, Lp.norm_toLp, Lp.norm_def, Lp.norm_def, ← ENNReal.toReal_mul]
      exact ENNReal.toReal_mono (ENNReal.mul_lt_top (Lp.memLp k).eLpNorm_lt_top
        (Lp.memLp f).eLpNorm_lt_top).ne (integral_kernel_memLp (Lp.memLp k) (Lp.memLp f)).2)

theorem tsum_enorm_basis_inner_sq {H ι : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (b : HilbertBasis ι ℂ H) (a : H) :
    (∑' i, ‖⟪a, b i⟫_ℂ‖ₑ ^ (2 : ℝ)) = ‖a‖ₑ ^ (2 : ℝ) := by
  have hs := lp.hasSum_norm (by norm_num : 0 < (2 : ℝ≥0∞).toReal) (b.repr a)
  have hs' : HasSum (fun i => ‖⟪b i, a⟫_ℂ‖ ^ 2) (‖a‖ ^ 2) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, b.repr_apply_apply, b.repr.norm_map] using hs
  simp only [ENNReal.rpow_two, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
  simp_rw [norm_inner_symm a (b _)]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) hs'.summable, hs'.tsum_eq]

private theorem opNorm_sq_le_basisEnergy {H K ι : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (b : HilbertBasis ι ℂ H) (A : H →L[ℂ] K) :
    ‖A‖ₑ ^ (2 : ℝ) ≤ ∑' i, ‖A (b i)‖ₑ ^ (2 : ℝ) := by
  let q : ℝ≥0∞ := ∑' i, ‖A (b i)‖ₑ ^ (2 : ℝ)
  change _ ≤ q
  by_cases hq : q = ⊤
  · simp [hq]
  have hpoint (y : K) : ‖A.adjoint y‖ₑ ^ (2 : ℝ) ≤
      q * ‖y‖ₑ ^ (2 : ℝ) := by
    rw [← tsum_enorm_basis_inner_sq b]
    unfold q
    rw [← ENNReal.tsum_mul_right]
    refine ENNReal.tsum_le_tsum fun i => ?_
    rw [ContinuousLinearMap.adjoint_inner_left, ← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
    apply ENNReal.rpow_le_rpow _ (by norm_num)
    rw [← ofReal_norm, ← ofReal_norm (A (b i)), ← ofReal_norm y,
      ← ENNReal.ofReal_mul (norm_nonneg _), mul_comm ‖A (b i)‖]
    exact ENNReal.ofReal_le_ofReal (norm_inner_le_norm y (A (b i)))
  let r := q ^ (1 / 2 : ℝ)
  have hr : r ≠ ⊤ := (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hq).ne
  have hrsq : r ^ (2 : ℝ) = q := by
    unfold r
    rw [← ENNReal.rpow_mul]
    norm_num
  have hA : ‖A.adjoint‖ ≤ r.toReal := by
    apply ContinuousLinearMap.opNorm_le_bound _ ENNReal.toReal_nonneg
    intro y
    have he : ‖A.adjoint y‖ₑ ≤ r * ‖y‖ₑ := by
      rw [← ENNReal.rpow_le_rpow_iff (by norm_num : (0 : ℝ) < 2),
        ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), hrsq]
      exact hpoint y
    simpa only [ENNReal.toReal_mul, toReal_enorm] using
      ENNReal.toReal_mono (ENNReal.mul_lt_top hr.lt_top enorm_lt_top).ne he
  rw [ContinuousLinearMap.adjoint.norm_map] at hA
  calc
    _ ≤ r ^ (2 : ℝ) := by
      apply ENNReal.rpow_le_rpow _ (by norm_num)
      rw [← ENNReal.ofReal_toReal hr, ← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal hA
    _ = _ := hrsq

/-- A finite Hilbert–Schmidt energy gives compactness via finite basis truncations. -/
theorem isCompactOperator_of_basisEnergy {H K ι : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (b : HilbertBasis ι ℂ H) (A : H →L[ℂ] K)
    (hA : (∑' i, ‖A (b i)‖ₑ ^ (2 : ℝ)) ≠ ⊤) : IsCompactOperator A := by
  classical
  let P (s : Finset ι) := ∑ i ∈ s, InnerProductSpace.rankOne ℂ (A (b i)) (b i)
  have hP (s : Finset ι) (i : ι) : P s (b i) = if i ∈ s then A (b i) else 0 := by
    simp only [P, sum_apply, InnerProductSpace.rankOne_apply,
      orthonormal_iff_ite.mp b.orthonormal]
    by_cases hi : i ∈ s
    · rw [ite_eq_left hi, Finset.sum_eq_single_of_mem i hi]
      · simp
      · intro j _ hji
        simp [hji]
    · rw [ite_eq_right hi]
      apply Finset.sum_eq_zero
      intro j hj
      have hji : j ≠ i := fun h => hi (h ▸ hj)
      simp [hji]
  have hnorm (s : Finset ι) : ‖A - P s‖ₑ ^ (2 : ℝ) ≤
      ∑' i : {i // i ∉ s}, ‖A (b i)‖ₑ ^ (2 : ℝ) := by
    refine (opNorm_sq_le_basisEnergy b (A - P s)).trans_eq ?_
    change _ = ∑' i : {i // i ∈ (↑s : Set ι)ᶜ}, ‖A (b i)‖ₑ ^ (2 : ℝ)
    rw [tsum_subtype (↑s : Set ι)ᶜ (fun i => ‖A (b i)‖ₑ ^ (2 : ℝ))]
    apply tsum_congr
    intro i
    by_cases hi : i ∈ s <;> simp [hP, hi]
  have ht : Tendsto P atTop (𝓝 A) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have ht := ENNReal.tendsto_tsum_compl_atTop_zero hA
    have hpos : 0 < ENNReal.ofReal ε ^ (2 : ℝ) :=
      ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr hε) ENNReal.ofReal_ne_top
    filter_upwards [(tendsto_order.mp ht).2 _ hpos] with s hs
    have hlt := (hnorm s).trans_lt hs
    have hn := (ENNReal.rpow_lt_rpow_iff (by norm_num : (0 : ℝ) < 2)).mp hlt
    rw [← ofReal_norm, ENNReal.ofReal_lt_ofReal_iff hε] at hn
    rwa [dist_comm, dist_eq_norm]
  apply isCompactOperator_of_tendsto ht
  refine Eventually.of_forall fun s => ?_
  let C := compactOperator (RingHom.id ℂ) H K
  change P s ∈ C
  apply Submodule.sum_mem C
  intro i _
  exact (isCompactOperator_of_locallyCompactSpace_rng
    (ContinuousLinearMap.toSpanSingleton ℂ (A (b i)))).comp_clm (innerSL ℂ (b i))

/-- The squared Hilbert–Schmidt norm of the integral operator equals the squared
L² norm of the kernel, computed on any countable orthonormal basis of the source. -/
theorem kernelIntegralOperator_hilbertSchmidt_sq {ι : Type*} [Countable ι]
    (b : HilbertBasis ι ℂ (Y →₂[ν] ℂ)) (k : (X × Y) →₂[μ.prod ν] ℂ) :
    (∑' i, ‖kernelIntegralOperator k (b i)‖ₑ ^ (2 : ℝ)) = ‖k‖ₑ ^ (2 : ℝ) := by
  simp only [Lp.enorm_def, ← lintegral_enorm_sq]
  rw [← lintegral_tsum (fun i =>
    (Lp.aestronglyMeasurable (kernelIntegralOperator k (b i))).enorm.pow_const (2 : ℝ))]
  rw [lintegral_prod _ ((Lp.aestronglyMeasurable k).enorm.pow_const (2 : ℝ))]
  apply lintegral_congr_ae
  filter_upwards [memLp_kernelRows (Lp.memLp k),
    ae_all_iff.mpr (fun i => kernelIntegralOperator_apply k (b i))] with x hx hbx
  let r : Y → ℂ := fun y => star (k (x, y))
  have hr : MemLp r 2 ν := hx.star
  let a : Y →₂[ν] ℂ := hr.toLp r
  have hinner (i : ι) : ⟪a, b i⟫_ℂ = ∫ y, k (x, y) * b i y ∂ν := by
    rw [MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hr.coeFn_toLp] with y hy
    change ⟪a y, b i y⟫_ℂ = _
    rw [hy, RCLike.inner_apply, show (starRingEnd ℂ) (r y) = k (x, y) from star_star _, mul_comm]
  calc
    _ = ∑' i, ‖⟪a, b i⟫_ℂ‖ₑ ^ (2 : ℝ) :=
      tsum_congr fun i => by rw [(hbx i).2, hinner i]
    _ = ‖a‖ₑ ^ (2 : ℝ) := tsum_enorm_basis_inner_sq b a
    _ = _ := by
      rw [Lp.enorm_toLp, ← lintegral_enorm_sq]
      simp only [r, ← ofReal_norm (star _), norm_star, ofReal_norm]

/-- The kernel is determined by its integral operator. -/
theorem kernelIntegralOperator_injective {ι : Type*} [Countable ι]
    (b : HilbertBasis ι ℂ (Y →₂[ν] ℂ)) :
    Function.Injective (kernelIntegralOperator (μ := μ) (ν := ν)) := by
  intro k l h
  have hz : kernelIntegralOperator (k - l) = 0 := by
    change kernelIntegralOperatorCLM (k - l) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr h
  have hsq := kernelIntegralOperator_hilbertSchmidt_sq b (k - l)
  rw [hz] at hsq
  have hpow : ‖k - l‖ₑ ^ (2 : ℕ) = 0 := by
    simpa only [zero_apply, enorm_zero, ENNReal.rpow_two, zero_pow (by decide : 2 ≠ 0),
      tsum_zero] using hsq.symm
  exact sub_eq_zero.mp (enorm_eq_zero.mp ((pow_eq_zero_iff (by decide : 2 ≠ 0)).mp hpow))

omit [SFinite ν] in
/-- A separable L² space admits a basis indexed by a countable subtype, including the
finite-dimensional and zero-dimensional cases. -/
theorem exists_countable_hilbertBasis_L2 [MeasureTheory.IsSeparable ν] :
    ∃ (s : Set (Y →₂[ν] ℂ)), s.Countable ∧ Nonempty (HilbertBasis s ℂ (Y →₂[ν] ℂ)) := by
  letI : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  obtain ⟨s, b, hb⟩ := exists_hilbertBasis (𝕜 := ℂ) (E := Y →₂[ν] ℂ)
  refine ⟨s, (HereditarilyLindelofSpace.isLindelof s).countable_of_isDiscrete ?_, ⟨b⟩⟩
  apply isDiscrete_iff_forall_mem_exists_isOpen.mpr
  intro x hx
  refine ⟨Metric.ball x 1, Metric.isOpen_ball, Set.ext fun y => ?_⟩
  constructor
  · rintro ⟨hyball, hys⟩
    have hdist : ‖y - x‖ < 1 := by simpa only [Metric.mem_ball, dist_eq_norm] using hyball
    change y = x
    by_contra hyx
    have hne : (⟨y, hys⟩ : s) ≠ ⟨x, hx⟩ := fun he => hyx (congrArg Subtype.val he)
    have horth := b.orthonormal.inner_eq_zero hne
    have hy1 := b.orthonormal.norm_eq_one ⟨y, hys⟩
    have hx1 := b.orthonormal.norm_eq_one ⟨x, hx⟩
    rw [hb] at horth hy1 hx1
    have hsq : ‖y - x‖ ^ 2 = 2 := by
      rw [norm_sub_sq (𝕜 := ℂ), horth, hy1, hx1]
      norm_num
    nlinarith [norm_nonneg (y - x)]
  · rintro (rfl : y = x)
    exact ⟨Metric.mem_ball_self zero_lt_one, hx⟩

/-- A separated rank-one kernel has L² norm equal to the product of its factors' norms. -/
theorem memLp_rankOneKernel {u : X → ℂ} {v : Y → ℂ}
    (hu : MemLp u 2 μ) (hv : MemLp v 2 ν) :
    let k := fun z : X × Y => u z.1 * star (v z.2)
    MemLp k 2 (μ.prod ν) ∧ eLpNorm k 2 (μ.prod ν) = eLpNorm u 2 μ * eLpNorm v 2 ν := by
  let k := fun z : X × Y => u z.1 * star (v z.2)
  have hn : eLpNorm k 2 (μ.prod ν) = eLpNorm u 2 μ * eLpNorm v 2 ν := by
    simp only [eLpNorm_two_eq, k, enorm_mul, ← ofReal_norm (star _), norm_star, ofReal_norm,
      ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
    rw [lintegral_prod_mul (hu.aestronglyMeasurable.enorm.pow_const _)
      (hv.aestronglyMeasurable.enorm.pow_const _)]
    exact ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)
  exact ⟨⟨hu.aestronglyMeasurable.comp_fst.mul hv.star.aestronglyMeasurable.comp_snd,
    hn ▸ ENNReal.mul_lt_top hu.eLpNorm_lt_top hv.eLpNorm_lt_top⟩, hn⟩

/-- The integral operator of the separated kernel is the Hilbert-space rank-one map. -/
theorem kernelIntegralOperator_rankOne [SFinite μ] {u : X → ℂ} {v : Y → ℂ}
    (hu : MemLp u 2 μ) (hv : MemLp v 2 ν) :
    let k := (memLp_rankOneKernel hu hv).1.toLp (fun z : X × Y => u z.1 * star (v z.2))
    kernelIntegralOperator k = InnerProductSpace.rankOne ℂ (hu.toLp u) (hv.toLp v) := by
  dsimp only
  let k := (memLp_rankOneKernel hu hv).1.toLp (fun z : X × Y => u z.1 * star (v z.2))
  ext f : 1
  apply Lp.ext
  rw [InnerProductSpace.rankOne_apply]
  filter_upwards [kernelIntegralOperator_apply k f,
    Measure.ae_ae_of_ae_prod (MemLp.coeFn_toLp (memLp_rankOneKernel hu hv).1),
    Lp.coeFn_smul (⟪hv.toLp v, f⟫_ℂ) (hu.toLp u), hu.coeFn_toLp] with x hx hrow hs hux
  rw [hx.2, hs, Pi.smul_apply, hux, smul_eq_mul, mul_comm _ (u x),
    MeasureTheory.L2.inner_def, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [hrow, hv.coeFn_toLp] with y hxy hvy
  rw [hxy, hvy, RCLike.inner_apply]
  change u x * star (v y) * f y = u x * (f y * star (v y))
  ring

end

end Masullo
