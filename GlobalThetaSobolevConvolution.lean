import GlobalThetaSobolev
import IdelicCutoffKernel
import Mathlib.MeasureTheory.Integral.Prod

open Filter Function MeasureTheory NumberField Set Topology
open scoped ENNReal InnerProductSpace NumberField SchwartzMap

namespace Masullo

noncomputable section

private theorem integral_norm_pair_le {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (u v : Lp ℂ 2 μ) :
    (∫ x, ‖star (u x) * v x‖ ∂μ) ≤ ‖u‖ * ‖v‖ := by
  have hnorm (f : Lp ℂ 2 μ) : (∫ x, ‖f x‖ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) = ‖f‖ := by
    rw [Lp.norm_def, (Lp.memLp f).eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
    norm_num
    exact (ENNReal.toReal_ofReal (by positivity)).symm
  have h := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
    (by simpa using Lp.memLp u) (by simpa using Lp.memLp v)
  rw [hnorm u, hnorm v] at h
  simpa only [norm_mul, starRingEnd_apply, norm_star] using h

/-- Fubini identifies a Bochner integral in complex L² with a specified
L² representative of the pointwise integral. -/
theorem lpTwo_integral_eq_of_representatives
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν]
    (u : Y → Lp ℂ 2 μ) (v : Y → X → ℂ) (w : Lp ℂ 2 μ)
    (hu : Integrable u ν) (hv : Measurable (Function.uncurry v))
    (hrep : ∀ y, (u y : X → ℂ) =ᵐ[μ] v y)
    (hw : (w : X → ℂ) =ᵐ[μ] fun x ↦ ∫ y, v y x ∂ν) :
    (∫ y, u y ∂ν) = w := by
  refine (ext_iff_inner_left (𝕜 := ℂ)).mpr fun h ↦ ?_
  let K (p : Y × X) : ℂ := star (h p.2) * v p.1 p.2
  have hKm : AEStronglyMeasurable K (ν.prod μ) :=
    (((Complex.continuous_conj.measurable.comp
      ((Lp.stronglyMeasurable h).measurable.comp measurable_snd))).mul hv).aestronglyMeasurable
  have hpair (y : Y) :
      (fun x ↦ K (y, x)) =ᵐ[μ] fun x ↦ star (h x) * u y x :=
    (hrep y).mono fun x hx ↦ congrArg (star (h x) * ·) hx.symm
  have hK : Integrable K (ν.prod μ) := by
    apply (integrable_prod_iff hKm).mpr
    refine ⟨Eventually.of_forall fun y ↦ ?_, ?_⟩
    · apply Integrable.congr (L2.integrable_inner (𝕜 := ℂ) h (u y)) _
      filter_upwards [(hpair y).symm] with x hx
      exact (mul_comm _ _).trans hx
    · refine (hu.norm.const_mul ‖h‖).mono' hKm.norm.integral_prod_right'
        (Eventually.of_forall fun y ↦ ?_)
      rw [Real.norm_of_nonneg (integral_nonneg fun _ ↦ norm_nonneg _)]
      calc
        _ = ∫ x, ‖star (h x) * u y x‖ ∂μ :=
          integral_congr_ae ((hpair y).mono fun _ hx ↦ congrArg norm hx)
        _ ≤ ‖h‖ * ‖u y‖ := integral_norm_pair_le h (u y)
  change innerSL ℂ h (∫ y, u y ∂ν) = ⟪h, w⟫_ℂ
  rw [← (innerSL ℂ h).integral_comp_comm hu]
  calc
    _ = ∫ y, ∫ x, K (y, x) ∂μ ∂ν := by
      apply integral_congr_ae
      refine Eventually.of_forall fun y ↦ ?_
      change ⟪h, u y⟫_ℂ = _
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [(hpair y).symm] with x hx
      exact (mul_comm _ _).trans hx
    _ = ∫ x, ∫ y, K (y, x) ∂ν ∂μ :=
      (integral_prod K hK).symm.trans (integral_prod_symm K hK)
    _ = ⟪h, w⟫_ℂ := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hw] with x hx
      change (∫ y, star (h x) * v y x ∂ν) = w x * star (h x)
      rw [integral_const_mul, hx, mul_comm]

variable (F : Type*) [Field F] [NumberField F]

private abbrev Q := IdeleClass F

local instance thetaConvolutionMeasurable : MeasurableSpace (Q F) := borel _
local instance thetaConvolutionBorel : BorelSpace (Q F) := ⟨rfl⟩

variable (μ : Measure (Q F)) [μ.IsHaarMeasure]

/-- A Bochner integral of weighted translates of a vector in the
polar-free theta closure still belongs to that closure. The parameter
measure may be supported on a subgroup or on the logarithmic section. -/
theorem globalThetaSobolevCompletion_integral_translate_mem
    {Y : Type*} [MeasurableSpace Y] (ν : Measure Y)
    (a l r s : ℝ) (hs : 0 ≤ s) (g : Y → Q F) (φ : Y → ℂ)
    (u : Lp ℂ 2 μ) (hu : u ∈ globalThetaSobolevCompletion F μ a l r s hs)
    (hI : Integrable (fun y ↦ φ y • hardySobolevMulTranslation μ
      (ideleClassLogNorm F) (ideleClassLogNorm_continuous F) l r s hs (g y) u) ν) :
    (∫ y, φ y • hardySobolevMulTranslation μ
      (ideleClassLogNorm F) (ideleClassLogNorm_continuous F) l r s hs (g y) u ∂ν) ∈
      globalThetaSobolevCompletion F μ a l r s hs := by
  let N := globalThetaSobolevCompletion F μ a l r s hs
  letI : IsClosed (N : Set (Lp ℂ 2 μ)) := globalThetaSobolevCompletion_isClosed F μ a l r s hs
  let T (y : Y) := hardySobolevMulTranslation μ
    (ideleClassLogNorm F) (ideleClassLogNorm_continuous F) l r s hs (g y) u
  apply (Submodule.Quotient.mk_eq_zero N).mp
  change N.mkQL (∫ y, φ y • T y ∂ν) = 0
  rw [← N.mkQL.integral_comp_comm hI]
  have hz (y : Y) : N.mkQL (φ y • T y) = 0 :=
    (Submodule.Quotient.mk_eq_zero N).mpr
      (N.smul_mem _ (globalThetaSobolevCompletion_mapsTo F μ a l r s hs (g y) hu))
  exact (integral_congr_ae (Eventually.of_forall hz)).trans (by simp)

private abbrev amp (s : ℝ) (x : Q F) :=
  hardySobolevAmplitude 0 0 s (ideleClassLogNorm F x).toAdd

private theorem amp_pos (s : ℝ) (x : Q F) : 0 < amp F s x := by
  apply Real.sqrt_pos.mpr
  unfold hardySobolevWeight
  positivity

/-- In the zero-line chart, the Bochner integral of translations has
the ordinary pointwise convolution formula after dividing out the amplitude.
The kernel may be integrated on either factor of the idele class splitting. -/
theorem globalZeroLine_integral_translate_eq
    {Y : Type*} [MeasurableSpace Y] (ν : Measure Y) [SFinite ν]
    (s : ℝ) (hs : 0 ≤ s) (g : Y → Q F) (hg : Measurable g)
    (φ : Y → ℂ) (hφ : Measurable φ)
    (u w : Lp ℂ 2 μ) (v : Q F → ℂ) (hv : Measurable v)
    (huRep : (u : Q F → ℂ) =ᵐ[μ] fun x ↦ (amp F s x : ℂ) * v x)
    (hwRep : (w : Q F → ℂ) =ᵐ[μ] fun x ↦
      (amp F s x : ℂ) * ∫ y, φ y * v ((g y)⁻¹ * x) ∂ν)
    (hI : Integrable (fun y ↦ φ y • hardySobolevMulTranslation μ
      (ideleClassLogNorm F) (ideleClassLogNorm_continuous F) 0 0 s hs (g y) u) ν) :
    (∫ y, φ y • hardySobolevMulTranslation μ
      (ideleClassLogNorm F) (ideleClassLogNorm_continuous F) 0 0 s hs (g y) u ∂ν) = w := by
  letI : LocallyCompactSpace (Q F) := ideleClasses_locallyCompact
  letI : T2Space (Q F) := ideleClasses_hausdorff
  letI : SecondCountableTopology (Q F) := ideleClass_secondCountable F
  let T (y : Y) := hardySobolevMulTranslation μ
    (ideleClassLogNorm F) (ideleClassLogNorm_continuous F) 0 0 s hs (g y) u
  let k (y : Y) (x : Q F) := (amp F s x : ℂ) * (φ y * v ((g y)⁻¹ * x))
  have hm : Measurable (uncurry k) := by
    have ha : Continuous (amp F s) := (continuous_hardySobolevWeight 0 0 s).sqrt.comp
      (continuous_toAdd.comp (ideleClassLogNorm_continuous F))
    exact ((Complex.continuous_ofReal.measurable.comp ha.measurable).comp measurable_snd).mul
      ((hφ.comp measurable_fst).mul
        (hv.comp (((hg.comp measurable_fst).inv).mul measurable_snd)))
  have hrep (y : Y) : ((φ y • T y : Lp ℂ 2 μ) : Q F → ℂ) =ᵐ[μ] k y := by
    filter_upwards [Lp.coeFn_smul (φ y) (T y), hardySobolevMulTranslation_ae μ
      (ideleClassLogNorm F) (ideleClassLogNorm_continuous F) 0 0 s hs (g y) u,
      (measurePreserving_mul_left μ (g y)⁻¹).quasiMeasurePreserving.ae huRep] with x h₁ h₂ h₃
    change T y x = _ at h₂
    rw [h₁]
    change φ y * T y x = k y x
    rw [h₂, h₃, Complex.ofReal_div]
    let z := (g y)⁻¹ * x
    change φ y * ((amp F s x : ℂ) / (amp F s z : ℂ) * ((amp F s z : ℂ) * v z)) =
      (amp F s x : ℂ) * (φ y * v z)
    rw [← mul_assoc ((amp F s x : ℂ) / (amp F s z : ℂ)),
      div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr (amp_pos F s z).ne')]
    ring
  have hw : (w : Q F → ℂ) =ᵐ[μ] fun x ↦ ∫ y, k y x ∂ν := by
    simpa only [k, integral_const_mul] using hwRep
  exact lpTwo_integral_eq_of_representatives (fun y ↦ φ y • T y) k w hI hm hrep hw

/-- A represented convolution of a vector in the zero-line theta closure remains in it. -/
theorem globalThetaSobolevCompletion_mem_of_convolution
    {Y : Type*} [MeasurableSpace Y] (ν : Measure Y) [SFinite ν]
    (s : ℝ) (hs : 0 ≤ s) (g : Y → Q F) (hg : Measurable g)
    (φ : Y → ℂ) (hφ : Measurable φ)
    (u w : Lp ℂ 2 μ) (v : Q F → ℂ) (hv : Measurable v)
    (hu : u ∈ globalThetaSobolevCompletion F μ 0 0 0 s hs)
    (huRep : (u : Q F → ℂ) =ᵐ[μ] fun x ↦ (amp F s x : ℂ) * v x)
    (hwRep : (w : Q F → ℂ) =ᵐ[μ] fun x ↦
      (amp F s x : ℂ) * ∫ y, φ y * v ((g y)⁻¹ * x) ∂ν)
    (hI : Integrable (fun y ↦ φ y • hardySobolevMulTranslation μ
      (ideleClassLogNorm F) (ideleClassLogNorm_continuous F) 0 0 s hs (g y) u) ν) :
    w ∈ globalThetaSobolevCompletion F μ 0 0 0 s hs := by
  rw [← globalZeroLine_integral_translate_eq F μ ν s hs g hg φ hφ u w v hv huRep hwRep hI]
  exact globalThetaSobolevCompletion_integral_translate_mem F μ ν 0 0 0 s hs g φ u hu hI

set_option maxHeartbeats 1600000 in
theorem integrable_globalZeroLine_translate {Y : Type*} [TopologicalSpace Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y] (ν : Measure Y)
    (s : ℝ) (hs : 0 ≤ s) (g : Y → Q F) (hg : Continuous g) (φ : Y → ℂ)
    (hφ : AEStronglyMeasurable φ ν) (u : Lp ℂ 2 μ)
    (hu : u ∈ globalThetaSobolevCompletion F μ 0 0 0 s hs)
    (hI : Integrable (fun y ↦ ‖φ y‖ * (1 + |(ideleClassLogNorm F (g y)).toAdd|) ^ (s / 2)) ν) :
    Integrable (fun y ↦ φ y • hardySobolevMulTranslation μ
      (ideleClassLogNorm F) (ideleClassLogNorm_continuous F) 0 0 s hs (g y) u) ν := by
  letI : LocallyCompactSpace (Q F) := ideleClasses_locallyCompact
  letI : T2Space (Q F) := ideleClasses_hausdorff
  letI : SecondCountableTopology (Q F) := ideleClass_secondCountable F
  letI : μ.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure μ
  let T := hardySobolevMulTranslation μ
    (ideleClassLogNorm F) (ideleClassLogNorm_continuous F) 0 0 s hs
  let N := globalThetaSobolevCompletion F μ 0 0 0 s hs
  let v : N := ⟨u, hu⟩
  have ht : Continuous (fun y : Y ↦ T (g y) u) :=
    continuous_subtype_val.comp ((continuous_globalThetaSobolevCompletion_translate F μ 0 0 0 s hs).comp
      (hg.prodMk (continuous_const (y := v))))
  refine (hI.mul_const ‖u‖).mono' (hφ.smul ht.aestronglyMeasurable) (.of_forall fun y ↦ ?_)
  rw [norm_smul, mul_assoc]
  apply mul_le_mul_of_nonneg_left ((T (g y)).le_opNorm u |>.trans ?_) (norm_nonneg _)
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  simpa only [zero_mul, Real.exp_zero, one_mul] using
    hardySobolevMulTranslation_singleton_opNorm_le μ (ideleClassLogNorm F)
      (ideleClassLogNorm_continuous F) 0 s hs (g y)

private theorem integrable_schwartz_polynomial (s : ℝ) (c : 𝓢(ℝ, ℂ)) :
    Integrable (fun t : ℝ ↦ ‖c t‖ * (1 + |t|) ^ (s / 2)) := by
  obtain ⟨n, hn⟩ := exists_nat_ge (s / 2)
  have hpow (t : ℝ) : (1 + |t|) ^ (s / 2) ≤ (1 + |t|) ^ n := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (le_add_of_nonneg_right (abs_nonneg t)) hn
  have hmajor : Integrable (fun t : ℝ ↦ (1 + |t|) ^ n * ‖c t‖) := by
    induction n with
    | zero => simpa using c.integrable.norm
    | succ n _ =>
      rw [show (fun t : ℝ ↦ (1 + |t|) ^ (n+1) * ‖c t‖) =
          fun t : ℝ ↦ ∑ j ∈ Finset.range (n + 2),
            ((n+1).choose j : ℝ) * (‖t‖ ^ j * ‖c t‖) by
        funext t
        rw [add_comm 1, add_pow, Finset.sum_mul]
        simp only [one_pow, mul_one, Real.norm_eq_abs]
        exact Finset.sum_congr rfl (fun _ _ ↦ by ring)]
      exact integrable_finsetSum _ (fun j _ ↦ (c.integrable_pow_mul volume j).const_mul _)
  apply hmajor.mono' ((c.continuous.norm.mul
    ((continuous_const.add continuous_abs).rpow_const (fun t ↦ Or.inl (ne_of_gt (add_pos_of_pos_of_nonneg zero_lt_one (abs_nonneg t)))))).aestronglyMeasurable) _
  filter_upwards with t
  change ‖‖c t‖ * (1 + |t|) ^ (s / 2)‖ ≤ _
  rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg
    (add_nonneg zero_le_one (abs_nonneg t)) _)), mul_comm ((1 + |t|) ^ n)]
  exact mul_le_mul_of_nonneg_left (hpow t) (norm_nonneg _)

/-- Radial convolution by a Schwartz kernel preserves the zero-line theta
closure whenever the pointwise output is represented in weighted L². -/
theorem globalThetaSobolevCompletion_radial_convolution_mem
    (s : ℝ) (hs : 0 ≤ s) (c : 𝓢(ℝ, ℂ))
    (u w : Lp ℂ 2 μ) (v : Q F → ℂ) (hv : Measurable v)
    (hu : u ∈ globalThetaSobolevCompletion F μ 0 0 0 s hs)
    (huRep : (u : Q F → ℂ) =ᵐ[μ] fun x ↦ (amp F s x : ℂ) * v x)
    (hwRep : (w : Q F → ℂ) =ᵐ[μ] fun x ↦ (amp F s x : ℂ) *
      ∫ t : ℝ, c t * v ((ideleClassExpSection F (Multiplicative.ofAdd t))⁻¹ * x)) :
    w ∈ globalThetaSobolevCompletion F μ 0 0 0 s hs := by
  let g (t : ℝ) := ideleClassExpSection F (Multiplicative.ofAdd t)
  have hg : Continuous g := (ideleClassExpSection_continuous F).comp continuous_ofAdd
  apply globalThetaSobolevCompletion_mem_of_convolution F μ volume s hs g hg.measurable
    c c.continuous.measurable u w v hv hu huRep hwRep
  apply integrable_globalZeroLine_translate F μ volume s hs g hg c c.continuous.aestronglyMeasurable u hu
  simp only [g, ideleClassLogNorm_expSection]
  exact integrable_schwartz_polynomial s c

private abbrev K := normOneIdeleClass F

local instance thetaConvolutionNormOneMeasurable : MeasurableSpace (K F) := borel _
local instance thetaConvolutionNormOneBorel : BorelSpace (K F) := ⟨rfl⟩

/-- The actual homogeneous theta profile is obtained inside the zero-line
Sobolev closure by averaging translations over the compact norm-one group. -/
theorem globalThetaSobolevCompletion_homogeneous_mem
    (ν : Measure (K F)) [IsFiniteMeasure ν] (ω : PontryaginDual (K F))
    (s : ℝ) (hs : 0 ≤ s) (f : GlobalBruhat F) (hf : GlobalBruhat.polarEvaluation F f = 0)
    (w : Lp ℂ 2 μ)
    (hw : (w : Q F → ℂ) =ᵐ[μ] fun q ↦ (amp F s q : ℂ) *
      adelicHomogeneousTheta F ν ω (GlobalBruhat.algebraicEquiv F f).val q) :
    w ∈ globalThetaSobolevCompletion F μ 0 0 0 s hs := by
  let x : GlobalPolarTheta F := ⟨(globalThetaOperator F).ker.mkQL f, hf⟩
  let v := globalThetaOperator F f
  let u := globalThetaSobolevMap F μ 0 0 0 s hs x
  have hu : u ∈ globalThetaSobolevCompletion F μ 0 0 0 s hs := subset_closure ⟨x, rfl⟩
  have hv : Continuous v := adelicTheta_continuous F
    (bruhat_theta_continuous_and_invariant (GlobalBruhat.algebraicEquiv F f).property).1
  have huRep : (u : Q F → ℂ) =ᵐ[μ] fun q ↦ (amp F s q : ℂ) * v q := by
    have h := globalThetaSobolevMap_ae F μ 0 0 0 s hs x
    change (u : Q F → ℂ) =ᵐ[μ] fun q ↦
      (amp F s q * Real.exp (0 * (ideleClassLogNorm F q).toAdd)) • v q at h
    simpa only [zero_mul, Real.exp_zero, mul_one, Complex.real_smul] using h
  let g (k : K F) : Q F := k.val⁻¹
  let φ (k : K F) : ℂ := (ω k : ℂ)
  have hg : Continuous g := (continuous_subtype_val : Continuous (fun k : K F ↦ k.val)).inv
  have hφ : Continuous φ := continuous_subtype_val.comp ω.continuous
  apply globalThetaSobolevCompletion_mem_of_convolution F μ ν s hs g hg.measurable
    φ hφ.measurable u w v hv.measurable hu huRep
  · filter_upwards [hw] with q hq
    rw [hq]
    congr 1
    apply integral_congr_ae
    exact .of_forall fun k ↦ by
      change (ω k : ℂ) * adelicTheta F (GlobalBruhat.algebraicEquiv F f).val (k.val * q) =
        (ω k : ℂ) * adelicTheta F (GlobalBruhat.algebraicEquiv F f).val ((k.val⁻¹)⁻¹ * q)
      exact congrArg (fun z : Q F ↦ (ω k : ℂ) * adelicTheta F
        (GlobalBruhat.algebraicEquiv F f).val (z * q)) (inv_inv (k.val : Q F)).symm
  · letI : SecondCountableTopology (Q F) := ideleClass_secondCountable F
    letI : SecondCountableTopology (K F) := IsEmbedding.subtypeVal.secondCountableTopology
    apply integrable_globalZeroLine_translate F μ ν s hs g hg φ hφ.aestronglyMeasurable u hu
    have h (k : K F) : (ideleClassLogNorm F (g k)).toAdd = 0 := by
      have hk : ideleClassNorm F k.val = 1 := k.property
      change Real.log (ideleClassNorm F k.val⁻¹) = 0
      rw [map_inv, hk, inv_one, Real.log_one]
    simp only [h, abs_zero, add_zero, Real.one_rpow, mul_one, φ, Circle.norm_coe]
    exact integrable_const _

end
end Masullo
