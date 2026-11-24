/-
Adapted from the Apache-2.0 RiemannMasullo project, commit
db376192baf52253727c46e2b211619d4e6a3941, AppD_SchwartzBruhat/Sec1a.lean.
See External/PROVENANCE.md and External/RiemannMasullo.LICENSE.
-/
import LCAFourierIntegral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Continuous
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving

open Filter Function MeasureTheory Set Topology
open scoped ENNReal ZeroAtInfty

namespace Masullo

noncomputable section

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]

variable (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]

/-- Paper: (D.1.1.5), p. 746. Multiplicative convolution integrates the product with
the left translate of the second function. -/
def lcaConvolution (μ : Measure G) (f g : G → ℂ) (x : G) : ℂ :=
  ∫ y, f y * g (y⁻¹ * x) ∂μ

open scoped Pointwise in
/-- A product-measurable representative for the convolution kernel, carried on a
rectangle with σ-finite sides. The two sectionwise identities avoid any measurability
assumption on multiplication for the product σ-algebra. -/
private theorem lcaConvolution_kernel {f g : G → ℂ} (hf : Integrable f μ) (hg : Integrable g μ) :
    ∃ (S : Set G) (k : G × G → ℂ), SigmaFinite (μ.restrict S) ∧ StronglyMeasurable k ∧
      Function.support k ⊆ S ×ˢ S ∧
      (∀ x, ∀ᵐ y ∂μ, k (x, y) = f y * g (y⁻¹ * x)) ∧
      (∀ᵐ y ∂μ, ∀ᵐ x ∂μ, k (x, y) = f y * g (y⁻¹ * x)) := by
  obtain ⟨F, hF, cF, tF⟩ := exists_tendsto_ae_compactSupport hf
  obtain ⟨H, hH, cH, tH⟩ := exists_tendsto_ae_compactSupport hg
  let K n := tsupport (F n) ∪ tsupport (F n) * tsupport (H n)
  have hK (n) : IsCompact (K n) := (hF n).isCompact.union ((hF n).isCompact.mul (hH n).isCompact)
  let S := ⋃ n, K n
  have hS : MeasurableSet S := MeasurableSet.iUnion fun n ↦ (hK n).isClosed.measurableSet
  have hσ : SigmaFinite (μ.restrict S) := by
    refine ⟨⟨⟨fun n ↦ K n ∪ Sᶜ, fun _ ↦ trivial, fun n ↦ ?_, ?_⟩⟩⟩
    · rw [Measure.restrict_apply ((hK n).isClosed.measurableSet.union hS.compl),
        union_inter_distrib_right, compl_inter_self, union_empty]
      exact (measure_mono inter_subset_left).trans_lt (hK n).measure_lt_top
    · rw [← iUnion_union]
      exact union_compl_self S
  let P (n : ℕ) (p : G × G) := F n p.2 * H n (p.2⁻¹ * p.1)
  have hP (n) : Function.support (P n) ⊆ K n ×ˢ K n := by
    rintro ⟨x, y⟩ hp
    have hfy := subset_tsupport (F n) ((mul_ne_zero_iff.mp hp).1)
    have hgy := subset_tsupport (H n) ((mul_ne_zero_iff.mp hp).2)
    exact ⟨Or.inr ⟨y, hfy, y⁻¹ * x, hgy, mul_inv_cancel_left y x⟩, Or.inl hfy⟩
  have mP (n) : StronglyMeasurable (P n) := by
    have hcompact : HasCompactSupport (P n) := HasCompactSupport.intro ((hK n).prod (hK n))
      (fun p hp ↦ Function.notMem_support.mp (fun h ↦ hp (hP n h)))
    exact hcompact.stronglyMeasurable_of_prod ((cF n).comp continuous_snd |>.mul
      ((cH n).comp (continuous_snd.inv.mul continuous_fst)))
  let k (p : G × G) := limUnder atTop (fun n ↦ P n p)
  refine ⟨S, k, hσ, StronglyMeasurable.limUnder mP, ?_, ?_, ?_⟩
  · intro p hp
    by_contra h
    have hz (n) : P n p = 0 := Function.notMem_support.mp fun hn ↦
      h ⟨mem_iUnion.mpr ⟨n, (hP n hn).1⟩, mem_iUnion.mpr ⟨n, (hP n hn).2⟩⟩
    have ht : Tendsto (fun n ↦ P n p) atTop (𝓝 0) := by
      simp only [hz]
      exact tendsto_const_nhds
    exact hp ht.limUnder_eq
  · intro x
    have hmp := (measurePreserving_mul_right μ x).comp (Measure.measurePreserving_inv μ)
    filter_upwards [tF, hmp.quasiMeasurePreserving.tendsto_ae.eventually tH] with y hy hy'
    exact (hy.mul hy').limUnder_eq
  · filter_upwards [tF] with y hy
    have hmp := measurePreserving_mul_left μ y⁻¹
    filter_upwards [hmp.quasiMeasurePreserving.tendsto_ae.eventually tH] with x hx
    exact (hy.mul hx).limUnder_eq

/-- Paper: (D.1.1.5)–(D.1.1.6), p. 746. The fibre integrals of two L¹ functions
exist almost everywhere and their convolution is L¹ with the product norm bound. -/
theorem lcaConvolution_integrable {f g : G → ℂ} (hf : Integrable f μ) (hg : Integrable g μ) :
    (∀ᵐ x ∂μ, Integrable (fun y ↦ f y * g (y⁻¹ * x)) μ) ∧
      Integrable (lcaConvolution μ f g) μ ∧
      eLpNorm (lcaConvolution μ f g) 1 μ ≤ eLpNorm f 1 μ * eLpNorm g 1 μ := by
  obtain ⟨S, k, hσ, hk, hs, hrow, hcol⟩ := lcaConvolution_kernel μ hf hg
  have hzero (p : G × G) (hp : p ∉ S ×ˢ S) : k p = 0 :=
    Function.notMem_support.mp fun h ↦ hp (hs h)
  let N (x : G) := ∫⁻ y in S, ‖k (x, y)‖ₑ ∂μ
  have hN : Measurable N := hk.enorm.lintegral_prod_right'
  have hfull (x) : N x = ∫⁻ y, ‖k (x, y)‖ₑ ∂μ := by
    apply setLIntegral_eq_of_support_subset
    intro y hy
    by_contra h
    exact hy (by simp [hzero (x, y) (fun hp ↦ h hp.2)])
  have hconv (x) : (∫ y in S, k (x, y) ∂μ) = lcaConvolution μ f g x :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun y hy ↦ hzero (x, y) (fun hp ↦ hy hp.2))).trans (integral_congr_ae (hrow x))
  have hm : StronglyMeasurable (lcaConvolution μ f g) := (funext hconv) ▸ hk.integral_prod_right'
  -- Tonelli applies on the supporting rectangle, even when Haar measure on G is not σ-finite.
  have hbound : ∫⁻ x, N x ∂μ ≤ eLpNorm f 1 μ * eLpNorm g 1 μ := calc
    _ = ∫⁻ x in S, N x ∂μ := by
      symm
      apply setLIntegral_eq_of_support_subset
      intro x hx
      by_contra h
      exact hx (by simp [N, fun y ↦ hzero (x, y) (fun hp ↦ h hp.1)])
    _ = ∫⁻ y in S, ∫⁻ x in S, ‖k (x, y)‖ₑ ∂μ ∂μ := lintegral_lintegral_swap hk.enorm.aemeasurable
    _ ≤ ∫⁻ y, ∫⁻ x, ‖k (x, y)‖ₑ ∂μ ∂μ :=
      lintegral_mono' Measure.restrict_le_self fun y ↦ setLIntegral_le_lintegral _ _
    _ = ∫⁻ y, ‖f y‖ₑ * eLpNorm g 1 μ ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [hcol] with y hy
      calc
        _ = ∫⁻ x, ‖f y‖ₑ * ‖g (y⁻¹ * x)‖ₑ ∂μ := lintegral_congr_ae <|
          hy.mono fun x hx ↦ by rw [hx, enorm_mul]
        _ = _ := by
          rw [lintegral_const_mul' _ _ (by simp), lintegral_mul_left_eq_self (fun z ↦ ‖g z‖ₑ),
            eLpNorm_one_eq_lintegral_enorm]
    _ = _ := by
      rw [lintegral_mul_const'' _ hf.aestronglyMeasurable.enorm]
      simp only [eLpNorm_one_eq_lintegral_enorm]
  have hfin := hbound.trans_lt (ENNReal.mul_lt_top (memLp_one_iff_integrable.2 hf).eLpNorm_lt_top
    (memLp_one_iff_integrable.2 hg).eLpNorm_lt_top)
  have hle : ∫⁻ x, ‖lcaConvolution μ f g x‖ₑ ∂μ ≤ ∫⁻ x, N x ∂μ :=
    lintegral_mono fun x ↦ hconv x ▸ enorm_integral_le_lintegral_enorm _
  refine ⟨?_, ⟨hm.aestronglyMeasurable, hle.trans_lt hfin⟩, ?_⟩
  · filter_upwards [ae_lt_top hN hfin.ne] with x hx
    have hInt : Integrable (fun y ↦ k (x, y)) μ :=
      ⟨(hk.comp_measurable measurable_prodMk_left).aestronglyMeasurable, (hfull x).symm.trans_lt hx⟩
    exact hInt.congr (hrow x)
  · rw [eLpNorm_one_eq_lintegral_enorm]
    exact hle.trans hbound

omit [T2Space G] in
/-- Each fibre of an `L²` convolution is integrable, with the Cauchy–Schwarz bound. -/
lemma integrable_lcaConvolution_L2 {f g : G → ℂ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) (x : G) :
    Integrable (fun y ↦ f y * g (y⁻¹ * x)) μ ∧
      ‖lcaConvolution μ f g x‖ ≤ (eLpNorm f 2 μ).toReal * (eLpNorm g 2 μ).toReal := by
  have hpres : MeasurePreserving (fun y : G ↦ x / y) μ μ :=
    Measure.measurePreserving_div_left μ x
  have hfun : (fun y ↦ g (y⁻¹ * x)) = g ∘ fun y ↦ x / y := by
    ext y
    simp [div_eq_mul_inv, mul_comm]
  have hg' : MemLp (fun y ↦ g (y⁻¹ * x)) 2 μ := hfun ▸ hg.comp_measurePreserving hpres
  have hnorm : eLpNorm (fun y ↦ g (y⁻¹ * x)) 2 μ = eLpNorm g 2 μ := by
    rw [hfun]
    exact eLpNorm_comp_measurePreserving hg.aestronglyMeasurable hpres
  have hmul : MemLp (fun y ↦ f y * g (y⁻¹ * x)) 1 μ := MemLp.mul' (p := 2) (q := 2) (r := 1) hg' hf
  have hint : Integrable (fun y ↦ f y * g (y⁻¹ * x)) μ := memLp_one_iff_integrable.mp hmul
  have hprod : eLpNorm (fun y ↦ f y * g (y⁻¹ * x)) 1 μ ≤ eLpNorm f 2 μ * eLpNorm g 2 μ := by
    have hsmul := eLpNorm_smul_le_mul_eLpNorm (μ := μ) (p := 2) (q := 2) (r := 1)
      (φ := f) (f := fun y ↦ g (y⁻¹ * x)) hg'.aestronglyMeasurable hf.aestronglyMeasurable
    have hEq : (fun y ↦ f y * g (y⁻¹ * x)) = f • fun y ↦ g (y⁻¹ * x) := by
      ext y
      simp [smul_eq_mul]
    simpa [hEq, hnorm] using hsmul
  refine ⟨hint, ?_⟩
  have hfin : eLpNorm f 2 μ * eLpNorm g 2 μ ≠ ⊤ :=
    ENNReal.mul_ne_top hf.eLpNorm_ne_top hg.eLpNorm_ne_top
  have hI : ‖∫ y, f y * g (y⁻¹ * x) ∂μ‖ₑ ≤ eLpNorm f 2 μ * eLpNorm g 2 μ := by
    calc
      ‖∫ y, f y * g (y⁻¹ * x) ∂μ‖ₑ
          ≤ ∫⁻ y, ‖f y * g (y⁻¹ * x)‖ₑ ∂μ :=
            enorm_integral_le_lintegral_enorm (fun y ↦ f y * g (y⁻¹ * x))
      _ = eLpNorm (fun y ↦ f y * g (y⁻¹ * x)) 1 μ := eLpNorm_one_eq_lintegral_enorm.symm
      _ ≤ eLpNorm f 2 μ * eLpNorm g 2 μ := hprod
  simpa [lcaConvolution, toReal_enorm, ENNReal.toReal_mul] using ENNReal.toReal_mono hfin hI

omit [T2Space G] in
/-- Translation in `L²` makes the convolution of two `L²` functions continuous. -/
lemma continuous_lcaConvolution_L2 {f g : G → ℂ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Continuous (lcaConvolution μ f g) := by
  haveI : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨ENNReal.ofNat_ne_top⟩
  let gInv : G → ℂ := fun y ↦ g y⁻¹
  have hgInv : MemLp gInv 2 μ := hg.comp_measurePreserving (Measure.measurePreserving_inv μ)
  let F : Lp ℂ 2 μ := hf.toLp f
  let H : Lp ℂ 2 μ := hgInv.toLp gInv
  let pairing := (ContinuousLinearMap.mul ℂ ℂ).lpPairing μ 2 2
  have hshift : Continuous fun x : G ↦ DomMulAct.mk x⁻¹ • H :=
    (continuous_smul (M := Gᵈᵐᵃ) (X := Lp ℂ 2 μ)).comp
      ((DomMulAct.continuous_mk.comp continuous_inv).prodMk continuous_const)
  have hcont : Continuous (fun x : G ↦ pairing F (DomMulAct.mk x⁻¹ • H)) :=
    (pairing F).continuous.comp hshift
  refine hcont.congr fun x ↦ ?_
  rw [ContinuousLinearMap.lpPairing_eq_integral, lcaConvolution]
  simp only [ContinuousLinearMap.mul_apply']
  apply integral_congr_ae
  have hF : (F : G → ℂ) =ᵐ[μ] f := hf.coeFn_toLp
  have hH : (H : G → ℂ) =ᵐ[μ] gInv := hgInv.coeFn_toLp
  have hleft : (fun y ↦ (H : G → ℂ) (x⁻¹ * y)) =ᵐ[μ] fun y ↦ gInv (x⁻¹ * y) :=
    (measurePreserving_mul_left μ x⁻¹).quasiMeasurePreserving.ae_eq_comp hH
  have hAct := DomMulAct.smul_Lp_ae_eq (DomMulAct.mk x⁻¹) H
  simp only [Equiv.symm_apply_apply, smul_eq_mul] at hAct
  have htrans : (DomMulAct.mk x⁻¹ • H : Lp ℂ 2 μ) =ᵐ[μ] fun y ↦ g (y⁻¹ * x) := by
    refine hAct.trans (hleft.trans ?_)
    filter_upwards with y
    simp [gInv, mul_inv_rev, inv_inv]
  filter_upwards [hF, htrans] with y hyF hyT
  simp only [hyF, hyT]

/-- Paper: Lemma D.1.1.2(3), p. 747. The fibre integrals of two L² functions
exist everywhere and give a continuous function vanishing at infinity with the product norm bound. -/
theorem lcaConvolution_L2 {f g : G → ℂ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∀ x, Integrable (fun y ↦ f y * g (y⁻¹ * x)) μ) ∧
      ∃ F : C₀(G, ℂ), (∀ x, F x = lcaConvolution μ f g x) ∧
        ‖F‖ ≤ (eLpNorm f 2 μ).toReal * (eLpNorm g 2 μ).toReal := by
  have hint : ∀ x, Integrable (fun y ↦ f y * g (y⁻¹ * x)) μ :=
    fun x ↦ (integrable_lcaConvolution_L2 μ hf hg x).1
  have hpoint : ∀ x, ‖lcaConvolution μ f g x‖ ≤
      (eLpNorm f 2 μ).toReal * (eLpNorm g 2 μ).toReal :=
    fun x ↦ (integrable_lcaConvolution_L2 μ hf hg x).2
  have hcont : Continuous (lcaConvolution μ f g) := continuous_lcaConvolution_L2 μ hf hg
  let A := (eLpNorm f 2 μ).toReal
  let B := (eLpNorm g 2 μ).toReal
  have hzero : Tendsto (lcaConvolution μ f g) (cocompact G) (𝓝 (0 : ℂ)) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hCpos : 0 < A + B + 1 := by positivity
    let δr : ℝ := min 1 (ε / (2 * (A + B + 1)))
    have hδpos : 0 < δr := by
      have : 0 < ε / (2 * (A + B + 1)) := by positivity
      exact lt_min one_pos this
    have hδle : δr ≤ 1 := min_le_left _ _
    have hδmul : δr * (A + B + 1) ≤ ε / 2 := by
      have hle : δr ≤ ε / (2 * (A + B + 1)) := min_le_right _ _
      calc
        δr * (A + B + 1) ≤ ε / (2 * (A + B + 1)) * (A + B + 1) :=
          mul_le_mul_of_nonneg_right hle hCpos.le
        _ = ε / 2 := by field_simp [hCpos.ne']
    obtain ⟨f', hf'diff, hf'cont, hf'supp⟩ :=
      exists_compactTest_eLpNorm_sub_le (p := 2) ENNReal.ofNat_ne_top hf
        (ENNReal.ofReal_pos.mpr hδpos).ne'
    obtain ⟨g', hg'diff, hg'cont, hg'supp⟩ :=
      exists_compactTest_eLpNorm_sub_le (p := 2) ENNReal.ofNat_ne_top hg
        (ENNReal.ofReal_pos.mpr hδpos).ne'
    have hf' : MemLp f' 2 μ := hf'cont.memLp_of_hasCompactSupport (p := 2) hf'supp
    have hg' : MemLp g' 2 μ := hg'cont.memLp_of_hasCompactSupport (p := 2) hg'supp
    have hδf : (eLpNorm (f - f') 2 μ).toReal ≤ δr := by
      simpa [ENNReal.toReal_ofReal hδpos.le] using
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hf'diff
    have hδg : (eLpNorm (g - g') 2 μ).toReal ≤ δr := by
      simpa [ENNReal.toReal_ofReal hδpos.le] using
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hg'diff
    have hf'norm : (eLpNorm f' 2 μ).toReal ≤ A + δr := by
      have hle : eLpNorm f' 2 μ ≤ eLpNorm (f - f') 2 μ + eLpNorm f 2 μ := by
        calc
          eLpNorm f' 2 μ = eLpNorm (f + -(f - f')) 2 μ := by
            congr 1
            ext y
            simp [Pi.add_apply, Pi.sub_apply]
          _ ≤ eLpNorm f 2 μ + eLpNorm (-(f - f')) 2 μ :=
            eLpNorm_add_le hf.aestronglyMeasurable (hf.sub hf').aestronglyMeasurable.neg (by norm_num)
          _ = eLpNorm (f - f') 2 μ + eLpNorm f 2 μ := by rw [eLpNorm_neg, add_comm]
      have hfin1 : eLpNorm (f - f') 2 μ ≠ ⊤ :=
        ne_top_of_le_ne_top ENNReal.ofReal_ne_top hf'diff
      have hfin : eLpNorm (f - f') 2 μ + eLpNorm f 2 μ ≠ ⊤ :=
        ENNReal.add_ne_top.2 ⟨hfin1, hf.eLpNorm_ne_top⟩
      calc
        (eLpNorm f' 2 μ).toReal ≤ (eLpNorm (f - f') 2 μ + eLpNorm f 2 μ).toReal :=
          ENNReal.toReal_mono hfin hle
        _ = (eLpNorm (f - f') 2 μ).toReal + A := by
          rw [ENNReal.toReal_add hfin1 hf.eLpNorm_ne_top]
        _ ≤ δr + A := by gcongr
        _ = A + δr := add_comm _ _
    open scoped Pointwise in
    let K := tsupport f' * tsupport g'
    have hK : IsCompact K := hf'supp.isCompact.mul hg'supp.isCompact
    rw [eventually_iff, mem_cocompact']
    refine ⟨K, hK, ?_⟩
    intro x hx
    have hx' : ¬ dist (lcaConvolution μ f g x) 0 < ε := by
      simpa [mem_compl_iff, mem_ofPred] using hx
    by_contra hxK
    have htail : lcaConvolution μ f' g' x = 0 := by
      rw [lcaConvolution]
      rw [show (fun y ↦ f' y * g' (y⁻¹ * x)) = (0 : G → ℂ) by
        ext y
        by_contra hne
        have hy1 : y ∈ tsupport f' :=
          subset_tsupport f' (Function.mem_support.2 (left_ne_zero_of_mul hne))
        have hy2 : y⁻¹ * x ∈ tsupport g' :=
          subset_tsupport g' (Function.mem_support.2 (right_ne_zero_of_mul hne))
        exact hxK ⟨y, hy1, y⁻¹ * x, hy2, mul_inv_cancel_left y x⟩]
      exact integral_zero _ _
    have hsplit : lcaConvolution μ f g x - lcaConvolution μ f' g' x =
        lcaConvolution μ (f - f') g x + lcaConvolution μ f' (g - g') x := by
      have h1 := (integrable_lcaConvolution_L2 μ (hf.sub hf') hg x).1
      have h2 := (integrable_lcaConvolution_L2 μ hf' (hg.sub hg') x).1
      simp only [lcaConvolution]
      have hfg := hint x
      have hfg' := (integrable_lcaConvolution_L2 μ hf' hg' x).1
      rw [← integral_sub hfg hfg', ← integral_add h1 h2]
      refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
      simp only [Pi.sub_apply]
      ring
    have hdist : ‖lcaConvolution μ f g x‖ ≤
        (eLpNorm (f - f') 2 μ).toReal * B + (eLpNorm f' 2 μ).toReal * (eLpNorm (g - g') 2 μ).toReal := by
      calc
        ‖lcaConvolution μ f g x‖ =
            ‖lcaConvolution μ f g x - lcaConvolution μ f' g' x‖ := by rw [htail, sub_zero]
        _ = ‖lcaConvolution μ (f - f') g x + lcaConvolution μ f' (g - g') x‖ := by rw [hsplit]
        _ ≤ ‖lcaConvolution μ (f - f') g x‖ + ‖lcaConvolution μ f' (g - g') x‖ := norm_add_le _ _
        _ ≤ (eLpNorm (f - f') 2 μ).toReal * (eLpNorm g 2 μ).toReal +
              (eLpNorm f' 2 μ).toReal * (eLpNorm (g - g') 2 μ).toReal :=
            add_le_add (integrable_lcaConvolution_L2 μ (hf.sub hf') hg x).2
              (integrable_lcaConvolution_L2 μ hf' (hg.sub hg') x).2
    have hsmall : ‖lcaConvolution μ f g x‖ < ε := by
      calc
        ‖lcaConvolution μ f g x‖ ≤
            (eLpNorm (f - f') 2 μ).toReal * B +
              (eLpNorm f' 2 μ).toReal * (eLpNorm (g - g') 2 μ).toReal := hdist
        _ ≤ δr * B + (A + δr) * δr := by
            gcongr
        _ ≤ δr * B + (A + 1) * δr := by
            gcongr
        _ = δr * (A + B + 1) := by ring
        _ ≤ ε / 2 := hδmul
        _ < ε := by linarith
    exact hx' <| by simpa [dist_zero_right] using hsmall
  let F : C₀(G, ℂ) :=
    { toFun := lcaConvolution μ f g
      continuous_toFun := hcont
      zero_at_infty' := hzero }
  refine ⟨hint, F, fun _ ↦ rfl, ?_⟩
  rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
  exact (BoundedContinuousFunction.norm_le_of_nonempty (f := F.toBCF)).2 fun x ↦ by
    simpa [F, dist_eq_norm] using hpoint x

/-- Convolution of an integrable function with a continuous compactly supported
test is continuous and lies in L². -/
theorem lcaConvolution_L1_compact {f g : G → ℂ} (hf : Integrable f μ)
    (hg : Continuous g) (hgK : HasCompactSupport g) :
    Continuous (lcaConvolution μ f g) ∧ MemLp (lcaConvolution μ f g) 2 μ := by
  obtain ⟨C, hC⟩ := hgK.exists_bound_of_continuous hg
  let f₁ := (memLp_one_iff_integrable.mpr hf).toLp f
  let T (x : G) := Lp.compMeasurePreserving (x * ·) (measurePreserving_mul_left μ x) f₁
  have hT : Continuous T := by
    have hMul : Continuous fun x : G ↦ ContinuousMap.mulLeft (X := G) x :=
      (ContinuousMap.curry ⟨fun p : G × G ↦ p.1 * p.2, continuous_mul⟩).continuous
    exact continuous_const.compMeasurePreservingLp hMul _ ENNReal.one_ne_top
  have hgInf : MemLp (fun y ↦ g y⁻¹) ∞ μ :=
    memLp_top_of_bound (hg.comp continuous_inv).aestronglyMeasurable C
      (.of_forall fun y ↦ hC y⁻¹)
  let gInf := hgInf.toLp (fun y ↦ g y⁻¹)
  let B := (ContinuousLinearMap.mul ℂ ℂ).lpPairing μ 1 ∞
  have hrepr (x : G) : B (T x) gInf = lcaConvolution μ f g x := by
    rw [ContinuousLinearMap.lpPairing_eq_integral]
    have hTx : (T x : G → ℂ) =ᵐ[μ] fun y ↦ f (x * y) :=
      (Lp.coeFn_compMeasurePreserving f₁ _).trans
        ((measurePreserving_mul_left μ x).quasiMeasurePreserving.ae_eq_comp
          (MemLp.coeFn_toLp (memLp_one_iff_integrable.mpr hf)))
    calc
      _ = ∫ y, f (x * y) * g y⁻¹ ∂μ := by
        apply integral_congr_ae
        filter_upwards [hTx, hgInf.coeFn_toLp] with y hy hz
        change (T x : G → ℂ) y * (gInf : G → ℂ) y = _
        rw [hy, show (gInf : G → ℂ) y = g y⁻¹ from hz]
      _ = _ := by
        unfold lcaConvolution
        rw [← integral_mul_left_eq_self (μ := μ) (fun y ↦ f y * g (y⁻¹ * x)) x]
        simp only [mul_inv_rev, inv_mul_cancel_right]
  have hcont : Continuous (lcaConvolution μ f g) :=
    ((B.flip gInf).continuous.comp hT).congr hrepr
  let D := C * ∫ y, ‖f y‖ ∂μ
  have hb (x : G) : ‖lcaConvolution μ f g x‖ ≤ D := by
    rw [lcaConvolution, show D = C * ∫ y, ‖f y‖ ∂μ from rfl, ← integral_const_mul]
    apply norm_integral_le_of_norm_le (hf.norm.const_mul C)
    exact .of_forall fun y ↦ by
      rw [norm_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right (hC (y⁻¹ * x)) (norm_nonneg _)
  refine ⟨hcont, (memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable).2 ?_⟩
  have hi := (lcaConvolution_integrable μ hf (hg.integrable_of_hasCompactSupport hgK)).2.1
  refine (hi.norm.const_mul D).mono' (hcont.norm.pow 2).aestronglyMeasurable ?_
  exact .of_forall fun x ↦ by
    rw [Real.norm_of_nonneg (sq_nonneg _), sq]
    exact mul_le_mul_of_nonneg_right (hb x) (norm_nonneg _)

private theorem integral_lcaConvolution {f g : G → ℂ} (hf : Integrable f μ)
    (hg : Integrable g μ) :
    (∫ x, lcaConvolution μ f g x ∂μ) = (∫ y, f y ∂μ) * (∫ z, g z ∂μ) := by
  obtain ⟨S, k, hσ, hk, hs, hrow, hcol⟩ := lcaConvolution_kernel μ hf hg
  have hzeroRow (x : G) (hx : x ∉ S) (y : G) : k (x, y) = 0 :=
    Function.notMem_support.mp fun h ↦ hx (hs h).1
  have hzeroCol (y : G) (hy : y ∉ S) (x : G) : k (x, y) = 0 :=
    Function.notMem_support.mp fun h ↦ hy (hs h).2
  -- Fubini applies to the kernel on its σ-finite supporting rectangle.
  have hInt : Integrable k ((μ.restrict S).prod (μ.restrict S)) := by
    refine (integrable_prod_iff' hk.aestronglyMeasurable).2 ⟨?_, ?_⟩
    · apply ae_mono Measure.restrict_le_self
      filter_upwards [hcol] with y hy
      exact (((hg.comp_mul_left y⁻¹).const_mul (f y)).congr
        (hy.mono fun _ hx ↦ hx.symm)).restrict
    · refine (hf.norm.mul_const (∫ z, ‖g z‖ ∂μ)).restrict.congr ?_
      apply ae_mono Measure.restrict_le_self
      filter_upwards [hcol] with y hy
      symm
      calc
        _ = ∫ x, ‖k (x, y)‖ ∂μ := setIntegral_eq_integral_of_forall_compl_eq_zero
          (fun x hx ↦ by simp [hzeroRow x hx])
        _ = ∫ x, ‖f y * g (y⁻¹ * x)‖ ∂μ :=
          integral_congr_ae (hy.mono fun _ hx ↦ congrArg norm hx)
        _ = _ := by
          simp only [norm_mul, integral_const_mul, integral_mul_left_eq_self (fun z ↦ ‖g z‖)]
  have hrowIntegral (x : G) : (∫ y in S, k (x, y) ∂μ) = lcaConvolution μ f g x :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero (hzeroCol · · x)).trans
      (integral_congr_ae (hrow x))
  calc
    _ = ∫ x in S, ∫ y in S, k (x, y) ∂μ ∂μ := by
      simp_rw [← hrowIntegral]
      exact (setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun x hx ↦ by simp [hzeroRow x hx])).symm
    _ = ∫ y in S, ∫ x in S, k (x, y) ∂μ ∂μ := integral_integral_swap hInt
    _ = ∫ y, ∫ x, k (x, y) ∂μ ∂μ := by
      have hcolIntegral (y : G) : (∫ x in S, k (x, y) ∂μ) = ∫ x, k (x, y) ∂μ :=
        setIntegral_eq_integral_of_forall_compl_eq_zero (hzeroRow · · y)
      simp_rw [hcolIntegral]
      exact setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun y hy ↦ by simp [hzeroCol y hy])
    _ = _ := by
      rw [← integral_mul_const]
      apply integral_congr_ae
      filter_upwards [hcol] with y hy
      rw [integral_congr_ae hy, integral_const_mul, integral_mul_left_eq_self g]

/-- Paper: Lemma D.1.1.2(6), p. 747. The Fourier transform takes L¹ convolution
to pointwise multiplication on the dual. -/
theorem lcaFourier_convolution {f g : G → ℂ} (hf : Integrable f μ) (hg : Integrable g μ) :
    lcaFourier μ (lcaConvolution μ f g) = lcaFourier μ f * lcaFourier μ g := by
  funext χ
  change (∫ x, lcaConvolution μ f g x * star (χ x : ℂ) ∂μ) =
    (∫ x, f x * star (χ x : ℂ) ∂μ) * (∫ x, g x * star (χ x : ℂ) ∂μ)
  rw [← integral_lcaConvolution μ (integrable_fourierIntegrand μ hf χ)
    (integrable_fourierIntegrand μ hg χ)]
  apply integral_congr_ae
  exact .of_forall fun x ↦ by
    simp only [lcaConvolution, ← integral_mul_const]
    apply integral_congr_ae
    exact .of_forall fun y ↦ by
      have hχ : (χ x : ℂ) = (χ y : ℂ) * (χ (y⁻¹ * x) : ℂ) := by
        rw [← Circle.coe_mul, ← map_mul, mul_inv_cancel_left]
      rw [hχ, star_mul]
      ring

end
end Masullo
