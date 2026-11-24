/-
Adapted from the Apache-2.0 RiemannMasullo project,
3b4b2cd6915a243a5299a26001ca6b1c1a2ed037, AppD_SchwartzBruhat/Sec1a.lean.
See External/PROVENANCE.md and External/RiemannMasullo.LICENSE.
-/
import PontryaginBidual
import LCAPlancherelExistence
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

noncomputable section

open Filter Function MeasureTheory Set Topology InnerProductSpace
open scoped ENNReal

namespace Masullo

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G]

section Fourier

variable [MeasurableSpace G] [BorelSpace G]
  [MeasurableSpace (PontryaginDual G)] [BorelSpace (PontryaginDual G)]

/-- Multiplying an L² function by a character translates its Plancherel transform. -/
private theorem lcaFourier_unitary_modulation (μ : Measure G)
    (ν : Measure (PontryaginDual G)) [ν.IsHaarMeasure]
    (U : Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 ν)
    (hU : ∀ (f : G → ℂ), Integrable f μ → ∀ (hf : MemLp f 2 μ),
      (U (hf.toLp f) : PontryaginDual G → ℂ) =ᵐ[ν] lcaFourier μ f)
    (ψ : PontryaginDual G) (f : Lp ℂ 2 μ) :
    ∃ g : Lp ℂ 2 μ, (g : G → ℂ) =ᵐ[μ] (fun x ↦ (ψ x : ℂ) * f x) ∧
      (U g : PontryaginDual G → ℂ) =ᵐ[ν] (fun χ ↦ U f (ψ⁻¹ * χ)) := by
  let m := measurePreserving_mul_left ν ψ⁻¹
  let c (x : G) : ℂ := ψ x
  have hc : MemLp c ∞ μ := memLp_top_of_bound
    (continuous_subtype_val.comp ψ.continuous).aestronglyMeasurable 1
      (.of_forall fun x ↦ (Circle.norm_coe (ψ x)).le)
  have hMem (v : Lp ℂ 2 μ) : MemLp (fun x ↦ c x * v x) 2 μ :=
    (Lp.memLp v).mul' hc
  let M (v : Lp ℂ 2 μ) := (hMem v).toLp (fun x ↦ c x * v x)
  have hM (v : Lp ℂ 2 μ) : (M v : G → ℂ) =ᵐ[μ] (fun x ↦ c x * v x) :=
    (hMem v).coeFn_toLp
  refine ⟨M f, hM f, ?_⟩
  let T := Lp.compMeasurePreservingₗᵢ ℂ (ψ⁻¹ * ·) m (p := 2) (E := ℂ)
  have hT (v : Lp ℂ 2 ν) : (T v : PontryaginDual G → ℂ) =ᵐ[ν] (fun χ ↦ v (ψ⁻¹ * χ)) :=
    Lp.coeFn_compMeasurePreserving v m
  suffices hEq : U (M f) = T (U f) by
    rw [hEq]
    exact hT (U f)
  have hMc : Continuous M := by
    apply Isometry.continuous
    apply Isometry.of_dist_eq
    intro v w
    simp only [dist_eq_norm]
    have hNorm : ∀ᵐ x ∂μ, ‖(M v - M w) x‖ = ‖(v - w) x‖ := by
      filter_upwards [hM v, hM w, Lp.coeFn_sub (M v) (M w), Lp.coeFn_sub v w]
        with x hv hw h₁ h₂
      simp only [Pi.sub_apply] at h₁ h₂
      rw [h₁, h₂, hv, hw, ← mul_sub, norm_mul, Circle.norm_coe (ψ x), one_mul]
    exact le_antisymm (Lp.norm_le_norm_of_ae_le (hNorm.mono fun _ h ↦ h.le))
      (Lp.norm_le_norm_of_ae_le (hNorm.mono fun _ h ↦ h.ge))
  refine (Lp.simpleFunc.denseRange (E := ℂ) (μ := μ) (p := 2) ENNReal.ofNat_ne_top).induction_on f
    (isClosed_eq (U.continuous.comp hMc) (T.continuous.comp U.continuous)) ?_
  intro s
  let v : Lp ℂ 2 μ := s
  have hv : Integrable (v : G → ℂ) μ :=
    ((SimpleFunc.memLp_iff_integrable two_ne_zero ENNReal.ofNat_ne_top).mp
      (Lp.simpleFunc.memLp s)).congr (Lp.simpleFunc.toSimpleFunc_eq_toFun s)
  have hMv : Integrable (fun x ↦ c x * v x) μ :=
    memLp_one_iff_integrable.mp ((memLp_one_iff_integrable.mpr hv).mul' hc)
  have hUv : (U v : PontryaginDual G → ℂ) =ᵐ[ν] lcaFourier μ v := by
    simpa only [Lp.toLp_coeFn] using hU _ hv (Lp.memLp v)
  change U (M v) = T (U v)
  apply Lp.ext
  filter_upwards [hU _ hMv (hMem v), hT (U v), m.quasiMeasurePreserving.ae_eq_comp hUv]
    with χ h₁ h₂ h₃
  rw [h₁, h₂, show U v (ψ⁻¹ * χ) = lcaFourier μ v (ψ⁻¹ * χ) from h₃]
  unfold lcaFourier
  apply integral_congr_ae
  exact .of_forall fun x ↦ by
    change c x * v x * star (χ x : ℂ) = v x * star (((ψ x)⁻¹ * χ x : Circle) : ℂ)
    rw [Circle.coe_mul, star_mul, Circle.coe_inv_eq_conj, ← Complex.star_def, star_star]
    change (ψ x : ℂ) * v x * _ = _
    ring

/-- A nonzero L² function with orthogonal modulations gives a normalized measure
whose Fourier–Stieltjes coefficients vanish at those modulations. -/
private theorem probability_of_l2_orthogonality (μ : Measure G) [μ.InnerRegularCompactLTTop]
    (f : Lp ℂ 2 μ) (hf : f ≠ 0) {V : Set (PontryaginDual G)}
    (hZero : ∀ ψ ∉ V, ∫ x, (ψ x : ℂ) * (‖f x‖ ^ 2 : ℝ) ∂μ = 0) :
    ∃ ν : Measure G, IsProbabilityMeasure ν ∧ ν.InnerRegular ∧
      ∀ ψ ∉ V, ∫ x, (ψ x : ℂ) ∂ν = 0 := by
  let w (x : G) := ‖f x‖ ^ 2
  have hw : ∀ x, 0 ≤ w x := fun x ↦ sq_nonneg _
  have hSq (x : G) : inner ℂ (f x) (f x) = (w x : ℂ) := by
    change _ = ((‖f x‖ ^ 2 : ℝ) : ℂ)
    rw [Complex.ofReal_pow]
    exact inner_self_eq_norm_sq_to_K (f x)
  have hInt : Integrable w μ := by
    simpa only [hSq, RCLike.re_to_complex, Complex.ofReal_re]
      using (L2.integrable_inner (𝕜 := ℂ) f f).re
  let ρ := μ.withDensity (fun x ↦ ENNReal.ofReal (w x))
  have hρ {s : Set G} (hs : MeasurableSet s) :
      ρ s = ENNReal.ofReal (∫ x in s, w x ∂μ) := by
    rw [withDensity_apply _ hs,
      ofReal_integral_eq_lintegral_ofReal hInt.integrableOn (.of_forall hw)]
  have hMass : ρ univ = ENNReal.ofReal (‖f‖ ^ 2) := by
    rw [hρ MeasurableSet.univ, Measure.restrict_univ]
    congr 1
    have hSelf : inner ℂ f f = ((‖f‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.ofReal_pow]
      exact inner_self_eq_norm_sq_to_K f
    rw [L2.inner_def] at hSelf
    simp_rw [hSq, integral_complex_ofReal] at hSelf
    exact Complex.ofReal_injective hSelf
  have hFinite : IsFiniteMeasure ρ := ⟨hMass ▸ ENNReal.ofReal_lt_top⟩
  have hPos : ρ univ ≠ 0 := by
    rw [hMass]
    exact (ENNReal.ofReal_pos.mpr (sq_pos_of_pos (norm_pos_iff.mpr hf))).ne'
  have hRegular : ρ.InnerRegular := by
    constructor
    intro s hs r hr
    have hrTop := hr.ne_top
    have hr' : r.toReal < ∫ x in s, w x ∂μ := by
      rw [hρ hs] at hr
      exact ENNReal.toReal_lt_of_lt_ofReal hr
    obtain ⟨K, hKs, hK, hTail⟩ := exists_isCompact_integral_norm_sdiff_lt hInt hs
      (sub_pos.mpr hr')
    simp only [Real.norm_of_nonneg (hw _)] at hTail
    refine ⟨K, hKs, hK, ?_⟩
    rw [hρ hK.isClosed.measurableSet, ← ENNReal.ofReal_toReal hrTop,
      ENNReal.ofReal_lt_ofReal_iff_of_nonneg ENNReal.toReal_nonneg]
    have hSplit := setIntegral_sdiff hK.isClosed.measurableSet hInt.integrableOn hKs
    linarith
  refine ⟨(ρ univ)⁻¹ • ρ, ⟨?_⟩, inferInstance, fun ψ hψ ↦ ?_⟩
  · rw [Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel hPos (measure_ne_top ρ _)]
  · rw [integral_smul_measure, integral_withDensity_eq_integral_toReal_smul₀
      hInt.aemeasurable.ennreal_ofReal (.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
    simp only [ENNReal.toReal_ofReal (hw _), Complex.real_smul, mul_comm (w _ : ℂ)]
    change _ * (∫ x, (ψ x : ℂ) * (‖f x‖ ^ 2 : ℝ) ∂μ) = 0
    rw [hZero ψ hψ, mul_zero]

end Fourier

open scoped Pointwise in
/-- For each identity neighborhood in the dual, there is an inner-regular probability
measure on the group whose Fourier–Stieltjes transform vanishes off that neighborhood.
One route is to take the autocorrelation of a bump on the dual and use Plancherel to
represent it by the squared modulus of the inverse transform of the bump. -/
theorem exists_pontryaginDual_localized_integral [MeasurableSpace G] [BorelSpace G]
    {V : Set (PontryaginDual G)} (hV : V ∈ 𝓝 (1 : PontryaginDual G)) :
    ∃ ν : Measure G, IsProbabilityMeasure ν ∧ ν.InnerRegular ∧
      ∀ ψ ∉ V, ∫ x, (ψ x : ℂ) ∂ν = 0 := by
  let : MeasurableSpace (PontryaginDual G) := borel _
  let : BorelSpace (PontryaginDual G) := ⟨rfl⟩
  let μ : Measure G := Measure.haar
  obtain ⟨ν, hν, -⟩ := lcaPlancherelMeasure_existsUnique μ
  let : ν.IsHaarMeasure := hν.1
  obtain ⟨U, hU, -⟩ := lcaFourier_unitary μ ν hν
  -- Choose a compact neighborhood whose pairwise quotients lie in V.
  obtain ⟨W, hW, -, hWinv, hWV⟩ := exists_closed_nhds_one_inv_eq_mul_subset hV
  obtain ⟨K, ⟨hK₁, hK⟩, hKW⟩ := (compact_basis_nhds (1 : PontryaginDual G)).mem_iff.mp hW
  have hKm := hK.isClosed.measurableSet
  have hKfin := (hK.measure_lt_top (μ := ν)).ne
  have hKpos := (ν.measure_pos_of_mem_nhds hK₁).ne'
  let a := indicatorConstLp (μ := ν) 2 hKm hKfin (1 : ℂ)
  have ha : (a : PontryaginDual G → ℂ) =ᵐ[ν] K.indicator (fun _ ↦ (1 : ℂ)) :=
    indicatorConstLp_coeFn
  have haNe : a ≠ 0 := by
    intro hz
    have hn := norm_indicatorConstLp (p := 2) (μ := ν) (hs := hKm) (hμs := hKfin) (c := (1 : ℂ))
      (by norm_num) ENNReal.ofNat_ne_top
    have hp := ENNReal.toReal_pos hKpos hKfin
    change ‖a‖ = _ at hn
    simp only [hz, norm_zero, norm_one, one_mul] at hn
    exact (Real.rpow_pos_of_pos hp _).ne' hn.symm
  let f := U.symm a
  have hUf : U f = a := U.apply_symm_apply a
  refine probability_of_l2_orthogonality μ f (U.symm.map_eq_zero_iff.not.mpr haNe) ?_
  intro ψ hψ
  obtain ⟨g, hg, hUg⟩ := lcaFourier_unitary_modulation μ ν U hU ψ f
  -- The transforms of f and g have disjoint supports up to null sets.
  have hUtf : inner ℂ (U f) (U g) = 0 := by
    let m := measurePreserving_mul_left ν ψ⁻¹
    rw [hUf] at hUg
    rw [L2.inner_def, hUf]
    rw [← integral_zero (α := PontryaginDual G) (μ := ν) (G := ℂ)]
    apply integral_congr_ae
    filter_upwards [ha, hUg, m.quasiMeasurePreserving.ae_eq_comp ha] with χ hχ hχ' hShift
    change a χ = _ at hχ
    change U g χ = _ at hχ'
    rw [hχ, hχ', show a (ψ⁻¹ * χ) = _ from hShift]
    by_cases hχK : χ ∈ K
    · have hOutside : ψ⁻¹ * χ ∉ K := by
        intro h
        apply hψ
        apply hWV
        refine ⟨χ, hKW hχK, (ψ⁻¹ * χ)⁻¹, ?_, by simp [mul_comm]⟩
        rw [← hWinv]
        exact Set.inv_mem_inv.mpr (hKW h)
      simp [indicator_of_notMem hOutside]
    · simp [indicator_of_notMem hχK]
  rw [U.inner_map_map, L2.inner_def] at hUtf
  refine (integral_congr_ae (hg.mono fun x hx ↦ ?_)).trans hUtf
  rw [RCLike.inner_apply, starRingEnd_apply, hx, mul_assoc, Complex.star_def, Complex.mul_conj,
    Complex.normSq_eq_norm_sq]

/-- Paper: Theorem D.1.1.1(2), p. 746. Evaluation gives the canonical topological
group isomorphism with the double dual. -/
theorem pontryaginDual_bidual :
    ∃ e : G ≃ₜ* PontryaginDual (PontryaginDual G),
      ∀ x χ, e x χ = χ x := by
  let e := pontryaginBidualEval (G := G)
  have hEmb := pontryaginBidualEval_isClosedEmbedding (G := G)
  have hSurj : Function.Surjective e := by
    intro η
    by_contra hη
    -- Choose a transform that vanishes on the translate of the evaluation image by η⁻¹.
    let V := ((η * ·) ⁻¹' Set.range e)ᶜ
    have hV : V ∈ 𝓝 (1 : PontryaginDual (PontryaginDual G)) :=
      (hEmb.isClosed_range.preimage (continuous_const.mul continuous_id)).isOpen_compl.mem_nhds
        (by simpa [V] using hη)
    let : MeasurableSpace (PontryaginDual G) := borel _
    let : BorelSpace (PontryaginDual G) := ⟨rfl⟩
    obtain ⟨ν, hν, hReg, hZero⟩ := exists_pontryaginDual_localized_integral hV
    let := hν
    let := hReg
    have hTest (x : G) : ∫ χ, (η⁻¹ χ : ℂ) * (χ x : ℂ) ∂ν = 0 := by
      have hx : η⁻¹ * e x ∉ V := by simp [V]
      exact hZero _ hx
    let : ν.Regular := inferInstance
    have hInt : Integrable (fun χ : PontryaginDual G ↦ (η⁻¹ χ : ℂ)) ν :=
      Integrable.of_bound (continuous_subtype_val.comp η⁻¹.continuous).aestronglyMeasurable 1
        (.of_forall fun χ ↦ (Circle.norm_coe _).le)
    have hZero' := ae_eq_zero_of_integral_mul_circle_eq_zero
      (fun χ : PontryaginDual G ↦ χ.toMonoidHom)
      (fun x ↦ (pontryaginBidualEval x).continuous)
      (fun χ ψ hEq ↦ PontryaginDual.ext fun x ↦ congrArg (fun k : G →* Circle ↦ k x) hEq)
      hInt hTest
    have hz : ∀ᵐ χ ∂ν, False := hZero'.mono fun χ hχ ↦ by
      have hn := Circle.norm_coe (η⁻¹ χ)
      change (η⁻¹ χ : ℂ) = 0 at hχ
      rw [hχ, norm_zero] at hn
      exact zero_ne_one hn
    have hνu : ν univ = 1 := measure_univ
    rw [ae_iff] at hz
    have hNull : ν univ = 0 := by simpa only [not_false_eq_true, Set.ofPred_true] using hz
    exact one_ne_zero (hνu.symm.trans hNull)
  let equiv := MulEquiv.ofBijective e.toMonoidHom ⟨hEmb.injective, hSurj⟩
  have hOpen := hEmb.isInducing.isOpenMap (by rw [hSurj.range_eq]; exact isOpen_univ)
  exact ⟨equiv.toContinuousMulEquiv (fun _ ↦
    (hOpen.isQuotientMap e.continuous hSurj).isCoinducing.isOpen_preimage),
    fun _ _ ↦ rfl⟩

/-- The canonical bidual evaluation is surjective on every locally compact Hausdorff
abelian group. -/
theorem pontryaginBidualEval_surjective : Surjective (pontryaginBidualEval (G := G)) := by
  obtain ⟨e, he⟩ := pontryaginDual_bidual (G := G)
  intro η
  refine ⟨e.symm η, ?_⟩
  have h : ∀ x, e x = pontryaginBidualEval x :=
    fun x ↦ PontryaginDual.ext (fun χ ↦ he x χ)
  rw [← h, e.apply_symm_apply]

/-- Corrected Lemma D.1.6.4. The two continuous homomorphism spaces are
isomorphic as Hausdorff topological groups with the compact-open topologies. -/
theorem oneParameterSubgroups_dual :
    ∃ e : OneParameterSubgroups G ≃ₜ*
        (PontryaginDual G →ₜ* PontryaginDual (Multiplicative ℝ)),
      ∀ a, e a = PontryaginDual.map a := by
  obtain ⟨eG, heG⟩ := pontryaginDual_bidual (G := G)
  exact oneParameterSubgroups_dual_of_bidual eG heG

end Masullo
