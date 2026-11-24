/-
The inverse pairing and inversion on L² adapt RiemannMasullo
Ch09_HardySobolev/Sec1.lean at db376192baf52253727c46e2b211619d4e6a3941 (Apache-2.0).
See External/PROVENANCE.md and External/RiemannMasullo.LICENSE.
-/
import LCAPlancherelExistence
import LCAConvolution
import PontryaginBidual

open Filter Function MeasureTheory Set Topology
open scoped ComplexConjugate ENNReal ZeroAtInfty
open InnerProductSpace

namespace Masullo

noncomputable section

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [MeasurableSpace (PontryaginDual G)] [BorelSpace (PontryaginDual G)]
  (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]
  (ν : Measure (PontryaginDual G))

omit [μ.IsHaarMeasure] in
/-- The inverse Fourier integral and the forward transform are adjoint on integrable
test functions. Compactly supported approximations provide a product-measurable kernel
even when the product topology and product σ-algebra have different Borel sets. -/
theorem lcaInverseFourier_integral_pairing
    {u : PontryaginDual G → ℂ} {q : G → ℂ} (hu : Integrable u ν) (hq : Integrable q μ)
    [ν.Regular] :
    (∫ x, (∫ χ, u χ * (χ x : ℂ) ∂ν) * star (q x) ∂μ) =
      ∫ χ, u χ * star (lcaFourier μ q χ) ∂ν := by
  obtain ⟨S, -, hqZero, hSσ⟩ := hq.aefinStronglyMeasurable.exists_set_sigmaFinite
  obtain ⟨T, -, huZero, hTσ⟩ := hu.aefinStronglyMeasurable.exists_set_sigmaFinite
  let := hSσ
  let := hTσ
  have hqZero := ae_imp_of_ae_restrict hqZero
  have huZero := ae_imp_of_ae_restrict huZero
  obtain ⟨Q, hQc, hQ, htQ⟩ := exists_tendsto_ae_compactSupport hq
  obtain ⟨U, hUc, hU, htU⟩ := exists_tendsto_ae_compactSupport hu
  let K (x : G) (χ : PontryaginDual G) := (u χ * (χ x : ℂ)) * star (q x)
  let A (n : ℕ) (p : G × PontryaginDual G) := (U n p.2 * (p.2 p.1 : ℂ)) * star (Q n p.1)
  have hEval : Continuous (fun p : G × PontryaginDual G ↦ (p.2 p.1 : ℂ)) :=
    continuous_subtype_val.comp ((continuous_eval (F := C(G, Circle))).comp
      (((ContinuousMonoidHom.isInducing_toContinuousMap G Circle).continuous.comp
        continuous_snd).prodMk continuous_fst))
  have hA (n : ℕ) : StronglyMeasurable (A n) := by
    apply HasCompactSupport.stronglyMeasurable_of_prod
      ((((hU n).comp continuous_snd).mul hEval).mul ((hQ n).comp continuous_fst).star)
    refine HasCompactSupport.intro ((hQc n).prod (hUc n)) ?_
    intro p hp
    by_cases hq : p.1 ∈ tsupport (Q n)
    · have hu : U n p.2 = 0 := image_eq_zero_of_notMem_tsupport (fun hu ↦ hp ⟨hq, hu⟩)
      simp [hu]
    · simp [image_eq_zero_of_notMem_tsupport hq]
  let k (p : G × PontryaginDual G) := limUnder atTop (fun n ↦ A n p)
  have hk : StronglyMeasurable k := StronglyMeasurable.limUnder hA
  have hLimit : ∀ᵐ x ∂μ, ∀ᵐ χ ∂ν, k (x, χ) = K x χ := by
    filter_upwards [htQ] with x hx
    filter_upwards [htU] with χ hχ
    exact ((hχ.mul tendsto_const_nhds).mul hx.star).limUnder_eq
  have hLimit' : ∀ᵐ χ ∂ν, ∀ᵐ x ∂μ, k (x, χ) = K x χ := by
    filter_upwards [htU] with χ hχ
    filter_upwards [htQ] with x hx
    exact ((hχ.mul tendsto_const_nhds).mul hx.star).limUnder_eq
  have hChar (x : G) : AEStronglyMeasurable (fun χ : PontryaginDual G ↦ (χ x : ℂ)) ν :=
    (hEval.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  have hRow (x : G) : Integrable (K x) ν :=
    (hu.mul_bdd (c := 1) (hChar x) (.of_forall fun χ ↦ (Circle.norm_coe (χ x)).le)).mul_const _
  have hInt : Integrable k ((μ.restrict S).prod (ν.restrict T)) := by
    apply (integrable_prod_iff hk.aestronglyMeasurable).2
    have hLim : ∀ᵐ x ∂μ.restrict S, (fun χ ↦ k (x, χ)) =ᵐ[ν.restrict T] K x :=
      ae_restrict_of_ae (hLimit.mono fun _ hx ↦ ae_restrict_of_ae hx)
    refine ⟨hLim.mono fun x hx ↦ (hRow x).restrict.congr hx.symm, ?_⟩
    refine (hq.norm.mul_const (∫ χ in T, ‖u χ‖ ∂ν)).restrict.congr ?_
    filter_upwards [hLim] with x hx
    symm
    calc
      _ = ∫ χ in T, ‖K x χ‖ ∂ν := integral_congr_ae (hx.mono fun χ hχ ↦ congrArg norm hχ)
      _ = _ := by simp [K, Circle.norm_coe, integral_mul_const, mul_comm]
  have hrowEq : ∀ᵐ x ∂μ, (∫ χ in T, k (x, χ) ∂ν) = ∫ χ, K x χ ∂ν := by
    filter_upwards [hLimit] with x hx
    rw [integral_congr_ae (ae_restrict_of_ae hx)]
    apply setIntegral_eq_integral_of_ae_compl_eq_zero
    exact huZero.mono fun χ hχ hmem ↦ by simp [K, hχ hmem]
  have hcolEq : ∀ᵐ χ ∂ν, (∫ x in S, k (x, χ) ∂μ) = ∫ x, K x χ ∂μ := by
    filter_upwards [hLimit'] with χ hχ
    rw [integral_congr_ae (ae_restrict_of_ae hχ)]
    apply setIntegral_eq_integral_of_ae_compl_eq_zero
    exact hqZero.mono fun x hx hmem ↦ by simp [K, hx hmem]
  calc
    _ = ∫ x, ∫ χ, K x χ ∂ν ∂μ := by simp_rw [K, integral_mul_const]
    _ = ∫ x in S, ∫ χ, K x χ ∂ν ∂μ := by
      symm
      exact setIntegral_eq_integral_of_ae_compl_eq_zero
        (hqZero.mono fun x hx hmem ↦ by simp [K, hx hmem])
    _ = ∫ x in S, ∫ χ in T, k (x, χ) ∂ν ∂μ :=
      integral_congr_ae (ae_restrict_of_ae (hrowEq.mono fun _ hx ↦ hx.symm))
    _ = ∫ χ in T, ∫ x in S, k (x, χ) ∂μ ∂ν := integral_integral_swap hInt
    _ = ∫ χ in T, ∫ x, K x χ ∂μ ∂ν := integral_congr_ae (ae_restrict_of_ae hcolEq)
    _ = ∫ χ, ∫ x, K x χ ∂μ ∂ν := setIntegral_eq_integral_of_ae_compl_eq_zero
      (huZero.mono fun χ hχ hmem ↦ by simp [K, hχ hmem])
    _ = _ := by
      congr with χ
      simp only [K, mul_assoc, integral_const_mul, lcaFourier, Complex.star_def,
        ← integral_conj, map_mul, starRingEnd_self_apply]
      congr 1
      apply integral_congr_ae
      exact .of_forall fun x ↦ mul_comm _ _

/-- Paper: Proposition 9.1.1.3(3), p. 397. For an L² element whose Plancherel transform is
integrable, the inverse Fourier integral represents that element and vanishes at infinity. -/
theorem lcaInverseFourier_zeroAtInfty [ν.IsHaarMeasure] [ν.Regular]
    (U : Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 ν) (hU : IsFourierPlancherel μ ν U)
    (v : Lp ℂ 2 μ) (u : PontryaginDual G → ℂ) (hu : Integrable u ν)
    (hv : (U v : PontryaginDual G → ℂ) =ᵐ[ν] u) :
    ∃ F : C₀(G, ℂ), (F : G → ℂ) =ᵐ[μ] (v : G → ℂ) ∧
      ∀ x, F x = ∫ χ, u χ * (χ x : ℂ) ∂ν := by
  obtain ⟨H, hH⟩ := lcaFourier_zeroAtInfty ν hu
  let e : CocompactMap G (PontryaginDual (PontryaginDual G)) :=
    ⟨⟨pontryaginBidualEval, pontryaginBidualEval.continuous⟩,
      pontryaginBidualEval_isClosedEmbedding.tendsto_cocompact⟩
  let F : C₀(G, ℂ) := (H.comp e).comp
    ⟨⟨Inv.inv, continuous_inv⟩, (Homeomorph.inv G).isClosedEmbedding.tendsto_cocompact⟩
  have hF (x : G) : F x = ∫ χ, u χ * (χ x : ℂ) ∂ν := by
    change H (pontryaginBidualEval x⁻¹) = _
    rw [hH]
    unfold lcaFourier
    apply integral_congr_ae
    exact .of_forall fun χ ↦ by
      change u χ * star (χ x⁻¹ : ℂ) = _
      rw [map_inv, Circle.coe_inv_eq_conj, ← Complex.star_def, star_star]
  refine ⟨F, ?_, hF⟩
  -- The nonzero set of a function in C₀ lies in a countable union of compact sets.
  let K (n : ℕ) : Set G := {x | 1 / ((n : ℝ) + 1) ≤ ‖F x‖}
  have hK (n : ℕ) : IsCompact (K n) := by
    have hc : IsClosed (K n) := isClosed_le continuous_const F.continuous.norm
    obtain ⟨L, hL, hsub⟩ := mem_cocompact.mp
      ((Metric.tendsto_nhds.mp F.zero_at_infty') _ (by positivity : 0 < 1 / ((n : ℝ) + 1)))
    exact hL.of_isClosed_subset hc fun x hx ↦ by
      by_contra hxL
      change 1 / ((n : ℝ) + 1) ≤ ‖F x‖ at hx
      have hlt : dist (F x) 0 < 1 / ((n : ℝ) + 1) := hsub hxL
      exact not_lt_of_ge hx (dist_zero_right (F x) ▸ hlt)
  let S := ⋃ n, K n
  have hS : MeasurableSet S := MeasurableSet.iUnion fun n ↦ (hK n).isClosed.measurableSet
  have hFS : ∀ x ∈ Sᶜ, F x = 0 := by
    intro x hx
    by_contra hne
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (norm_pos_iff.mpr hne)
    exact hx (mem_iUnion.mpr ⟨n, hn.le⟩)
  have hσ : SigmaFinite (μ.restrict S) := by
    refine ⟨⟨⟨fun n ↦ K n ∪ Sᶜ, fun _ ↦ trivial, fun n ↦ ?_, ?_⟩⟩⟩
    · rw [Measure.restrict_apply ((hK n).isClosed.measurableSet.union hS.compl),
        union_inter_distrib_right, compl_inter_self, union_empty]
      exact (measure_mono inter_subset_left).trans_lt (hK n).measure_lt_top
    · rw [← iUnion_union]
      exact union_compl_self S
  have hFin : AEFinStronglyMeasurable (F : G → ℂ) μ :=
    (F.continuous.stronglyMeasurable.finStronglyMeasurable_of_set_sigmaFinite
      hS hFS hσ).aefinStronglyMeasurable
  apply AEFinStronglyMeasurable.ae_eq_of_forall_setIntegral_eq _ _ _
    hFin ((Lp.memLp v).aefinStronglyMeasurable two_ne_zero ENNReal.ofNat_ne_top)
  · intro A _ hA
    let : IsFiniteMeasure (μ.restrict A) := isFiniteMeasure_restrict.mpr hA.ne
    exact Integrable.of_bound F.continuous.aestronglyMeasurable ‖F.toBCF‖
      (.of_forall F.toBCF.norm_coe_le_norm)
  · exact fun A _ hA ↦ integrableOn_Lp_of_measure_ne_top v (by norm_num) hA.ne
  · intro A hA hAμ
    let q : G → ℂ := A.indicator fun _ ↦ 1
    have hq : Integrable q μ := memLp_one_iff_integrable.mp
      (memLp_indicator_const (μ := μ) 1 hA (1 : ℂ) (.inr hAμ.ne))
    have hq₂ : MemLp q 2 μ := memLp_indicator_const (μ := μ) 2 hA (1 : ℂ) (.inr hAμ.ne)
    have hUq := hU q hq hq₂
    have hIndic (g : G → ℂ) : (∫ x, g x * star (q x) ∂μ) = ∫ x in A, g x ∂μ := by
      rw [← integral_indicator hA]
      congr with x
      by_cases hx : x ∈ A <;> simp [q, hx]
    calc
      _ = ∫ x, (∫ χ, u χ * (χ x : ℂ) ∂ν) * star (q x) ∂μ := by
        simp_rw [← hF]
        exact (hIndic F).symm
      _ = ∫ χ, u χ * star (lcaFourier μ q χ) ∂ν :=
        lcaInverseFourier_integral_pairing μ ν hu hq
      _ = inner ℂ (U (hq₂.toLp q)) (U v) := by
        rw [L2.inner_def]
        apply integral_congr_ae
        filter_upwards [hv, hUq] with χ hχ hχ'
        rw [RCLike.inner_apply, starRingEnd_apply, hχ, hχ']
      _ = inner ℂ (hq₂.toLp q) v := U.inner_map_map _ _
      _ = _ := by
        rw [← hIndic v, L2.inner_def]
        exact integral_congr_ae (hq₂.coeFn_toLp.mono fun x hx ↦ by
          change inner ℂ ((hq₂.toLp q) x) (v x) = v x * star (q x)
          rw [RCLike.inner_apply, starRingEnd_apply, hx])

set_option maxHeartbeats 1500000 in
/-- General L¹ inversion, with the source equality interpreted almost everywhere.
The prescribed Plancherel normalization is used to invert compact-test convolutions. -/
theorem lcaFourier_inversion_L1 [ν.IsHaarMeasure] [ν.Regular]
    (U : Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 ν) (hU : IsFourierPlancherel μ ν U)
    {f : G → ℂ} (hf : Integrable f μ) (hu : Integrable (lcaFourier μ f) ν) :
    ∃ F : C₀(G, ℂ), (F : G → ℂ) =ᵐ[μ] f ∧
      ∀ x, F x = ∫ χ, lcaFourier μ f χ * (χ x : ℂ) ∂ν := by
  let u := lcaFourier μ f
  let C := ∫ x, ‖f x‖ ∂μ
  have hu₂ : MemLp u 2 ν := by
    apply (memLp_two_iff_integrable_sq_norm hu.aestronglyMeasurable).2
    refine (hu.norm.const_mul C).mono' (hu.aestronglyMeasurable.norm.pow 2) ?_
    exact .of_forall fun χ ↦ by
      rw [Real.norm_of_nonneg (sq_nonneg _), sq]
      exact mul_le_mul_of_nonneg_right (norm_lcaFourier_le_integral_norm μ f χ) (norm_nonneg _)
  let v := U.symm (hu₂.toLp u)
  have hv : (U v : PontryaginDual G → ℂ) =ᵐ[ν] u := by
    simpa only [v, U.apply_symm_apply] using hu₂.coeFn_toLp
  obtain ⟨F, hFv, hFormula⟩ := lcaInverseFourier_zeroAtInfty μ ν U hU v u hu hv
  have hTest (η : G → ℂ) (hη : Continuous η) (hηK : HasCompactSupport η) :
      (∫ y, f y * η y⁻¹ ∂μ) = ∫ y, F y * η y⁻¹ ∂μ := by
    let a := lcaConvolution μ f η
    have hη₁ := hη.integrable_of_hasCompactSupport (μ := μ) hηK
    have ha := (lcaConvolution_integrable μ hf hη₁).2.1
    obtain ⟨haC, ha₂⟩ := lcaConvolution_L1_compact μ hf hη hηK
    have haF : lcaFourier μ a = u * lcaFourier μ η := lcaFourier_convolution μ hf hη₁
    have ha₁ : Integrable (lcaFourier μ a) ν := by
      rw [haF]
      exact hu.mul_bdd (continuous_lcaFourier μ hη₁).aestronglyMeasurable
        (.of_forall (norm_lcaFourier_le_integral_norm μ η))
    obtain ⟨A, hAa, hA⟩ := lcaInverseFourier_zeroAtInfty μ ν U hU
      (ha₂.toLp a) (lcaFourier μ a) ha₁ (hU a ha ha₂)
    have hEq : (A : G → ℂ) = a :=
      Measure.eq_of_ae_eq (hAa.trans ha₂.coeFn_toLp) A.continuous haC
    have hAtOne : (∫ y, f y * η y⁻¹ ∂μ) = ∫ χ, u χ * lcaFourier μ η χ ∂ν := by
      simpa only [haF, Pi.mul_apply, map_one, Circle.coe_one, mul_one, a, lcaConvolution]
        using (congrFun hEq 1).symm.trans (hA 1)
    let q (y : G) := star (η y⁻¹)
    have hq : Integrable q μ :=
      ((Measure.measurePreserving_inv μ).integrable_comp_of_integrable hη₁).norm.mono'
        ((hη.comp continuous_inv).star.aestronglyMeasurable)
        (.of_forall fun x ↦ by change ‖star (η x⁻¹)‖ ≤ ‖η x⁻¹‖; rw [norm_star])
    have hqF (χ : PontryaginDual G) : star (lcaFourier μ q χ) = lcaFourier μ η χ := by
      simp only [lcaFourier, Complex.star_def, ← integral_conj, map_mul, starRingEnd_self_apply]
      rw [← integral_inv_eq_self (fun y ↦ η y * conj (χ y : ℂ)) μ]
      apply integral_congr_ae
      exact .of_forall fun y ↦ by
        change conj (conj (η y⁻¹)) * (χ y : ℂ) = η y⁻¹ * conj (χ y⁻¹ : ℂ)
        rw [map_inv, Circle.coe_inv_eq_conj, starRingEnd_self_apply, starRingEnd_self_apply]
    refine hAtOne.trans ?_
    symm
    calc
      _ = ∫ y, (∫ χ, u χ * (χ y : ℂ) ∂ν) * star (q y) ∂μ := by
        apply integral_congr_ae
        exact .of_forall fun y ↦ by
          change F y * η y⁻¹ = (∫ χ, u χ * (χ y : ℂ) ∂ν) * star (star (η y⁻¹))
          rw [← hFormula, star_star]
      _ = ∫ χ, u χ * star (lcaFourier μ q χ) ∂ν :=
        lcaInverseFourier_integral_pairing μ ν hu hq
      _ = _ := integral_congr_ae (.of_forall fun χ ↦ congrArg (u χ * ·) (hqF χ))
  have hCompact (K : Set G) (hK : IsCompact K) : (F : G → ℂ) =ᵐ[μ.restrict K] f := by
    obtain ⟨b, hb₁, _, hbK, hb⟩ := exists_continuous_one_zero_of_isCompact hK
      isClosed_empty (disjoint_empty K)
    let d (x : G) : ℂ := (b x : ℂ)
    have hdC : Continuous d := Complex.continuous_ofReal.comp b.continuous
    have hdK : HasCompactSupport d := hbK.comp_left Complex.ofReal_zero
    have hdB (x : G) : ‖d x‖ ≤ 1 := by
      simp only [d, Complex.norm_real, Real.norm_of_nonneg (hb x).1]
      exact (hb x).2
    let j (x : G) : ℂ := (f x - F x) * d x
    have hj : Integrable j μ := by
      have hFd : Integrable (fun x ↦ F x * d x) μ :=
        (F.continuous.mul hdC).integrable_of_hasCompactSupport
          (show HasCompactSupport ((F : G → ℂ) * d) from hdK.mul_left)
      refine ((hf.mul_bdd hdC.aestronglyMeasurable (.of_forall hdB)).sub hFd).congr ?_
      exact .of_forall fun x ↦ by change f x * d x - F x * d x = (f x - F x) * d x; rw [sub_mul]
    have hz : ∀ χ, lcaFourier μ j χ = 0 := by
      intro χ
      let η (x : G) := d x⁻¹ * star (χ x⁻¹ : ℂ)
      have hη : Continuous η := (hdC.comp continuous_inv).mul
        ((continuous_subtype_val.comp χ.continuous).comp continuous_inv).star
      have hηK : HasCompactSupport η := by
        apply HasCompactSupport.intro (hdK.isCompact.image continuous_inv)
        intro x hx
        have hd : d x⁻¹ = 0 :=
          image_eq_zero_of_notMem_tsupport (fun hx' ↦ hx ⟨x⁻¹, hx', inv_inv x⟩)
        simp [η, hd]
      have hηInv (x : G) : η x⁻¹ = d x * star (χ x : ℂ) := by simp [η]
      have hbf (x : G) : ‖η x⁻¹‖ ≤ 1 := by
        rw [hηInv, norm_mul, norm_star, Circle.norm_coe, mul_one]
        exact hdB x
      have hFi : Integrable (fun x ↦ F x * η x⁻¹) μ :=
        ((F.continuous.mul (hη.comp continuous_inv))).integrable_of_hasCompactSupport
          (show HasCompactSupport (fun x ↦ F x * η x⁻¹) from
            (show HasCompactSupport (fun x ↦ η x⁻¹) from by
              rw [show (fun x ↦ η x⁻¹) = d * (fun x ↦ star (χ x : ℂ)) from funext hηInv]
              exact hdK.mul_right).mul_left)
      unfold lcaFourier
      calc
        _ = ∫ x, f x * η x⁻¹ - F x * η x⁻¹ ∂μ := by
          apply integral_congr_ae
          exact .of_forall fun x ↦ by
            change j x * star (χ x : ℂ) = f x * η x⁻¹ - F x * η x⁻¹
            rw [hηInv]; dsimp [j]; ring
        _ = _ := by
          have hfi : Integrable (fun x ↦ f x * η x⁻¹) μ :=
            hf.mul_bdd (show AEStronglyMeasurable (fun x ↦ η x⁻¹) μ from
              (hη.comp continuous_inv).aestronglyMeasurable) (.of_forall hbf)
          exact (integral_sub hfi hFi).trans (sub_eq_zero.mpr (hTest η hη hηK))
    have hZero := ae_eq_zero_of_lcaFourier_eq_zero μ hj hz
    filter_upwards [ae_restrict_of_ae hZero, ae_restrict_mem hK.isClosed.measurableSet] with x hx hxK
    have hdx : d x = 1 := by simpa [d] using congrArg (fun r : ℝ => (r : ℂ)) (hb₁ hxK)
    have hz' : f x - F x = 0 := by simpa [j, hdx] using hx
    exact (sub_eq_zero.mp hz').symm
  have hFint (s : Set G) (_ : MeasurableSet s) (hs : μ s < ∞) : IntegrableOn F s μ :=
    (integrableOn_Lp_of_measure_ne_top v (by norm_num) hs.ne).congr (ae_restrict_of_ae (s := s) hFv.symm)
  refine ⟨F, ?_, hFormula⟩
  obtain ⟨w, hw, hvw⟩ := (Lp.memLp v).aefinStronglyMeasurable two_ne_zero ENNReal.ofNat_ne_top
  refine AEFinStronglyMeasurable.ae_eq_of_forall_setIntegral_eq hFint
    (fun _ _ _ ↦ hf.integrableOn) ?_ ⟨w, hw, hFv.trans hvw⟩ hf.aefinStronglyMeasurable
  intro s hs hsfin
  let p (x : G) := F x - f x
  have hp : IntegrableOn p s μ := (hFint s hs hsfin).sub hf.integrableOn
  rw [← sub_eq_zero, ← integral_sub (hFint s hs hsfin) hf.integrableOn]
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  apply le_of_forall_pos_lt_add
  intro ε hε
  obtain ⟨K, hKs, hK, hTail⟩ := exists_isCompact_integral_norm_sdiff_lt
    (integrable_indicator_iff hs |>.2 hp) hs hε
  have hKzero : ∫ x in K, p x ∂μ = 0 :=
    (integral_congr_ae ((hCompact K hK).mono fun x hx ↦ sub_eq_zero.mpr hx)).trans
      (integral_zero _ _)
  change ‖∫ x in s, p x ∂μ‖ < 0 + ε
  rw [← sub_zero (∫ x in s, p x ∂μ), ← hKzero, ← setIntegral_sdiff hK.isClosed.measurableSet hp hKs,
    zero_add]
  refine (norm_integral_le_integral_norm _).trans_lt ?_
  exact (setIntegral_congr_fun (hs.diff hK.isClosed.measurableSet)
    (fun x hx ↦ by simp [indicator_of_mem hx.1])).symm.trans_lt hTail


/-- The unique Plancherel measure and unitary for the given regular Haar measure. -/
theorem lcaFourier_plancherel :
    ∃ ν : Measure (PontryaginDual G), IsLCAPlancherelMeasure μ ν ∧
      ∀ ν', IsLCAPlancherelMeasure μ ν' → ν' = ν ∧
        ∃! U : Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 ν', IsFourierPlancherel μ ν' U := by
  obtain ⟨ν, hν, hUnique⟩ := lcaPlancherelMeasure_existsUnique μ
  exact ⟨ν, hν, fun ν' hν' ↦ ⟨hUnique ν' hν', lcaFourier_unitary μ ν' hν'⟩⟩

/-- Corrected D.1.1.2(5). Inversion holds for the continuous representative
of the given integrable input whenever its Plancherel transform is integrable. -/
theorem lcaFourier_plancherel_inversion (hν : IsLCAPlancherelMeasure μ ν)
    {f : G → ℂ} (hf : Integrable f μ) (hu : Integrable (lcaFourier μ f) ν) :
    ∃ F : C₀(G, ℂ), (F : G → ℂ) =ᵐ[μ] f ∧
      ∀ x, F x = ∫ χ, lcaFourier μ f χ * (χ x : ℂ) ∂ν := by
  let : ν.IsHaarMeasure := hν.1
  let : ν.Regular := hν.2.1
  obtain ⟨U, hU, -⟩ := lcaFourier_unitary μ ν hν
  exact lcaFourier_inversion_L1 μ ν U hU hf hu

end
end Masullo
